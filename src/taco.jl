mutable struct TacoLowerContext
    tensor_variable_names
    index_variable_names
    input_transposes
    output_transposes
    usage
    index_headers
    tensor_file_headers
    tensor_file_options
    tensor_file_handlers
    tensor_file_readers
    tensor_output_constructors
    tensor_writers
    tensor_option_number
    names
    inputs
    output
    dims
    maybevar
    operands
end

function TacoLowerContext()
    tensor_variable_names = Dict()
    index_variable_names = Dict()
    input_transposes = ""
    output_transposes = ""
    usage = ""
    index_headers = ""
    tensor_file_headers = ""
    tensor_file_options = ""
    tensor_file_handlers = ""
    tensor_file_readers = ""
    tensor_output_constructors = ""
    tensor_writers = ""
    tensor_option_number = 3
    names = Set()
    inputs = Set()
    output = ""
    dims = Dimensions()
    maybevar = true
    operands = []

    TacoLowerContext(
        tensor_variable_names,
        index_variable_names,
        input_transposes,
        output_transposes,
        usage,
        index_headers,
        tensor_file_headers,
        tensor_file_options,
        tensor_file_handlers,
        tensor_file_readers,
        tensor_output_constructors,
        tensor_writers,
        tensor_option_number,
        names,
        inputs,
        output,
        dims,
        maybevar,
        operands,
    )
end
getdims(ctx::TacoLowerContext) = ctx.dims

function script_transpose!(node, ctx::TacoLowerContext)
    if (@ex@capture node @i ~cons where (@loop ~~idxs (~a)[~~idxs1] = (~b)[~~idxs2])) &&
        a isa SymbolicHollowDirector &&
        all(p -> p isa ConvertProtocol, a.protocol) && 
        b isa SymbolicHollowDirector &&
        all(p -> p isa ConvertProtocol, b.protocol)
        ctx.input_transposes = """
        $(ctx.input_transposes)
        Tensor<double> tensor_$(getname(a)) = tensor_$(getname(b)).transpose({$(join(map(string, getsites(b) .- 1), ", "))}, Format({$(join(map(taco_format, getformat(a)), ", "))}));
        TensorVar tensorvar_$(getname(a)) = tensor_$(getname(a)).getTensorVar();
        """
        ctx.tensor_variable_names[getname(a)] = "tensor_$(getname(a))"
        script!((@i b[$idxs2]), ctx, true)
        res = script_transpose!(cons, ctx)
        return res
    elseif (@ex@capture node @i (@loop ~~idxs (~a)[~~idxs1] = (~b)[~~idxs2]) where ~prod) &&
        a isa SymbolicHollowDirector &&
        all(p -> p isa ConvertProtocol, a.protocol) && 
        b isa SymbolicHollowDirector &&
        all(p -> p isa ConvertProtocol, b.protocol)
        ctx.output_transposes = """
        $(ctx.output_transposes)
        tensor_$(getname(a)) = tensor_$(getname(b)).transpose("$(getname(a))", {$(join(map(string, getsites(b) .- 1), ", "))}, Format({$(join(map(taco_format, getformat(a)), ", "))}));
        """
        #ctx.tensor_variable_names[getname(a)] = "tensor_$(getname(a))"
        script!(access(a, Write(), idxs1), ctx, true)
        res = script_transpose!(prod, ctx)
        return res
    end
    return script!(node, ctx)
end

function script!(node::With, ctx::TacoLowerContext)
    push!(ctx.names, getname(getresult(node.prod)))
    prod = script!(node.prod, ctx)
    cons = script!(node.cons, ctx)
    delete!(ctx.names, getname(getresult(node.prod)))
    return "where($cons, $prod)"
end

function script!(node::Loop, ctx::TacoLowerContext)
    isempty(node.idxs) && return script!(node.body, ctx)
    body = script!(Loop(node.idxs[2:end], node.body), ctx)
    return "forall($(script_index!(node.idxs[1], ctx)), $body)"
end

function script!(node::Assign, ctx::TacoLowerContext)
    lhs = script!(node.lhs, ctx)
    rhs = script!(node.rhs, ctx)
    if node.op === nothing
        return "$lhs = $rhs"
    elseif node.op === + 
        return "$lhs += $rhs"
    end
end

function script!(node::Call, ctx::TacoLowerContext)
    "($(join(map(arg->script!(arg, ctx), node.args), " $(node.op) ")))" #TODO very brittle, only works for infix ops
end

function script_index!(n::Name, ctx::TacoLowerContext)
    n = getname(n)
    if !haskey(ctx.index_variable_names, n)
        ctx.index_variable_names[n] = "index_$n"
        ctx.index_headers = """
            $(ctx.index_headers)
            IndexVar index_$n;
        """
    end
    return "index_$n"
end

#TODO does this belong in this hacky file or should it join the main repo
getformat(tns::SymbolicSolidTensor) = [ArrayFormat() for _ in tns.dims]

taco_format(::ArrayFormat) = "Dense"
taco_format(::HashFormat) = "Dense" #TODO need a taco compat check
taco_format(::ListFormat) = "Sparse"
taco_format(::NoFormat) = "Sparse"

function script!(node::Access, ctx::TacoLowerContext, ignoreoperand=false)
    idxs = map(idx->script_index!(idx, ctx), node.idxs)
    tns = node.tns

    if !(getname(node.tns) in map(node->getname(node.tns), ctx.operands)) && !(getname(node.tns) in ctx.names) && node.mode == Read() && !ignoreoperand
        push!(ctx.operands, node)
    end

    if !haskey(ctx.tensor_variable_names, getname(node.tns))
        ctx.tensor_variable_names[getname(node.tns)] = "tensor_$(getname(node.tns))"

        if getname(node.tns) in ctx.names
            ctx.tensor_output_constructors = """
            $(ctx.tensor_output_constructors)
            Tensor<double> tensor_$(getname(tns))({$(join(map(idx->ctx.dims[getname(idx)], node.idxs), ", "))}, Format({$(join(map(taco_format, getformat(tns)), ", "))}));
            TensorVar tensorvar_$(getname(tns)) = tensor_$(getname(tns)).getTensorVar();
            """
        else
            ctx.tensor_file_headers = """
            $(ctx.tensor_file_headers)
            std::string file_$(getname(tns)) = "";
            """

            ctx.tensor_file_options = """
            $(ctx.tensor_file_options)
            {"tensor_$(getname(tns))", required_argument, NULL, 1},
            """

            ctx.usage = """ $(ctx.usage)
            "--tensor_$(getname(tns)) <arg> file\\n"
            """

            ctx.tensor_file_handlers = """
            $(ctx.tensor_file_handlers)
            case $(ctx.tensor_option_number):

            if (stat(optarg, &statthing) < 0 || !S_ISREG(statthing.st_mode))
            {
                printf("argument to --tensor_$(getname(tns)) must be a file\\n");
                usage();
                return 1;
            }
            file_$(getname(tns)) = optarg;
            break;
            """
            ctx.tensor_option_number += 1

            if node.mode === Read()
                ctx.tensor_file_readers = """
                $(ctx.tensor_file_readers)
                if(file_$(getname(tns)) == ""){
                    std::cout << "oh no! There's no tensor file for $(getname(tns))" << std::endl;
                    return -1;
                }
                Tensor<double> tensor_$(getname(tns)) = read(file_$(getname(tns)), Format({$(join(map(taco_format, getformat(tns)), ", "))}), true);
                TensorVar tensorvar_$(getname(tns)) = tensor_$(getname(tns)).getTensorVar();
                """
            else
                ctx.output = tns
            
                ctx.tensor_output_constructors = """
                $(ctx.tensor_output_constructors)
                Tensor<double> tensor_$(getname(tns))({$(join(map(idx->ctx.dims[getname(idx)], node.idxs), ", "))}, Format({$(join(map(taco_format, getformat(tns)), ", "))}));
                TensorVar tensorvar_$(getname(tns)) = tensor_$(getname(tns)).getTensorVar();
                """

                ctx.tensor_writers = """
                $(ctx.tensor_writers)
                if(file_$(getname(tns)) != ""){
                    write(file_$(getname(tns)), tensor_$(getname(tns)));
                }
                """
            end
        end
    end
    if ctx.maybevar
        return "tensorvar_$(getname(tns))($(join(idxs, ", ")))"
    else
        return "tensor_$(getname(tns))($(join(idxs, ", ")))"
    end
end

lower_axes(tns::Union{SymbolicHollowTensor, SymbolicSolidTensor}, ctx::TacoLowerContext) = map(1:length(tns.dims)) do i
    if getname(tns) in ctx.inputs
        "tensor_$(getname(tns)).getDimensions()[$(i - 1)]"
    else
        nothing
    end
end

lower_axis_merge(::TacoLowerContext, a, b) = a === nothing ? b : a

function lower_taco(prgm)
    prgm = transform_ssa(prgm)
    ctx = TacoLowerContext()
    ctx.inputs = setdiff(getglobals(prgm), [getname(getresult(prgm))])
    Postwalk(node -> (dimensionalize!(node, ctx); node))(prgm)
    cin = script_transpose!(prgm, ctx)
    ctx.maybevar = false

    point = assign(access(ctx.output, Update(), [Name(freshen(:foo)) for _ in getformat(ctx.output)]), +, foldl((a, b) -> call(*, a, b), ctx.operands))
    point = script!(point, ctx)

    script = """
    #include "taco/tensor.h"
    //#include "taco/format.h"
    //#include "taco/lower/lower.h"
    //#include "taco/ir/ir.h"
    #include <iostream>
    #include <getopt.h>
    #include <sys/stat.h>
    #include <string>
    #include <chrono>

    template <typename Setup, typename Test>
    double benchmark(double time_max, int trial_max, Setup setup, Test test){
        auto time_total = std::chrono::high_resolution_clock::duration(0);
        auto time_min = std::chrono::high_resolution_clock::duration(0);
        int trial = 0;
        while(trial < trial_max){
            setup();
            auto tic = std::chrono::high_resolution_clock::now();
            test();
            auto toc = std::chrono::high_resolution_clock::now();
            auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(toc-tic);
            trial++;
            if(trial == 1 || time < time_min){
                time_min = time;
            }
            time_total += time;
            if(time_total.count() * 1e-9 > time_max){
                break;
            }
        }
        return time_min.count() * 1e-9;
    }

    using namespace taco;

    static void usage()
    {
        fprintf(stderr,
            "usage: foo [options]\\n"
            "  --ntrials <arg>        Maximum number of trials to run\\n"
            "  --ttrials <arg>        Maximum time to run trials\\n"
            "  --help                 Display help message\\n"
            $(ctx.usage)
        );
    }

    int main(int argc, char **argv)
    {
        int help = 0;


        int n_trials = 10000;
        double t_trials = 5.0;

        $(ctx.tensor_file_headers)

        /* Beware. Option parsing below. */
        long longarg;
        double doublearg;
        struct stat statthing;
        while (1)
        {
            const char *options = "";
            const struct option long_options[] = {
                {"ntrials", required_argument, NULL, 1},
                {"ttrials", required_argument, NULL, 1},
                {"help", no_argument, &help, 1},
                $(ctx.tensor_file_options)
                {0, 0, 0, 0}};

            /* getopt_long stores the option index here. */
            int option_index = 0;

            int c = getopt_long(argc, argv, options, long_options, &option_index);

            if (c == 0){
                continue;
            }

            /* Detect the end of the options. */
            if (c == -1)
                break;

            switch (option_index) {
                case 0:
                    errno = 0;
                    longarg = strtol(optarg, 0, 10);
                    if (errno != 0 || longarg < 1)
                    {
                        printf("option --ntrials takes an integer maximum number of trials >= 1\\n");
                        usage();
                        return 1;
                    }
                    n_trials = longarg;
                    break;

                case 1:
                    errno = 0;
                    doublearg = strtod(optarg, 0);
                    if (errno != 0 || doublearg < 0.0)
                    {
                        printf("option --ttrials takes a maximum measurement time in seconds >= 0.0\\n");
                        usage();
                        return 1;
                    }
                    t_trials = doublearg;
                    break;

                case 2:
                    help = 1;
                    break;

                $(ctx.tensor_file_handlers)

                default:
                    printf("unrecognized argument\\n");
                    usage();
                    abort();
            }
        }

        if (help)
        {
            printf("Try a tensor kernel!\\n");
            usage();
            return 0;
        }

        taco::setEvaluateAtAssign(false);

        // Create tensors
        $(ctx.tensor_file_readers)

        $(ctx.input_transposes)

        $(ctx.tensor_output_constructors)

        // Form a tensor-vector multiplication expression
        $(ctx.index_headers)

        $(point);

        // Compile the expression
        tensor_$(getname(ctx.output)).compile($cin);

        // Assemble output indices and numerically compute the result
        auto time = benchmark(
            10, 10000, [&tensor_$(getname(ctx.output))]()
            { tensor_$(getname(ctx.output)).assemble(); 
            //tensor_$(getname(ctx.output)).setNeedsCompute(true);
            },
            [&tensor_$(getname(ctx.output))]()
            { tensor_$(getname(ctx.output)).compute();
             });

        std::cout << time << std::endl;

        $(ctx.output_transposes)

        $(ctx.tensor_writers)

        return 0;
    }
    """

    script = read(open(`clang-format`, "r", IOBuffer(script)), String)
    #println(script)
    return script
end

function writetns(fname, data::Dict)
    open(fname, "w") do io
        for (coord, val) in pairs(data)
            write(io, join(coord, " "))
            write(io, " ")
            write(io, string(val))
            write(io, "\n")
        end
    end
end

function readtns(fname)
    data = Dict()
    for line in readlines(fname)
        if length(line) > 1
            line = split(line, "#")[1]
            entries = split(line)
            if length(entries) >= 1
                data[map(s->parse(Int, s), entries[1:end-1])] = parse(Float64, entries[1])
            end
        end
    end
    return (vals, coords...)
end

function build_taco(prgm, name = "kernel_$(hash(prgm, UInt(0)))")
    TACO_LIB = "/Users/Peter/Projects/taco/build/lib"
    TACO_INC = "/Users/Peter/Projects/taco/include"
    TACO_SRC = "/Users/Peter/Projects/taco/src"

    exe = joinpath(@get_scratch!("kernels"), name)
    if !isfile(exe) || true
        src = joinpath(@get_scratch!("kernels"), "$name.cpp")
        obj = joinpath(@get_scratch!("kernels"), "$name.o")
        open(src, "w") do io
            write(io, lower_taco(prgm))
        end
        run(`gcc -c -o $obj $src --std=c++11 -I$(TACO_INC) -I$(TACO_SRC) -g -ggdb -O0`)
        run(`gcc -o $exe $obj --std=c++11 -L$(TACO_LIB) -g -ggdb -O0 -lm -ltaco -lstdc++`)
    end

    exe
end

function run_taco(prgm, inputs)
    exe = build_taco(prgm)
    args = []
    for (name, val) in pairs(inputs)
        if val isa String
            push!(args, "--tensor_$(name)")
            push!(args, val)
        else
            f = joinpath(@get_scratch!("tensors"), "tensor_$(name).tns")
            writetns(f, val...)
            push!(args, "--tensor_$(name)")
            push!(args, f)
        end
    end
    io = IOBuffer()
    run(pipeline(`$exe $args`, stdout=io))
    return parse(Float64, String(take!(io)))
end

function generate_uniform_taco_inputs(tnss, n, ρ)
    NamedTuple(map(tns->Symbol(getname(tns)) => generate_uniform_taco_input(tns, n, ρ), tnss))
end

function generate_uniform_taco_input(tns, n, ρ)
    f = joinpath(@get_scratch!("tensors"), "tensor_$(getname(tns))_$(rand(UInt128)).tns")
    r = length(getsites(tns))
    N = ρ * n^r
    data = Dict()
    for _ = 1:ρ * n^r
        while true
            coord = rand(1:n, r)
            if !haskey(data, coord)
                data[coord] = rand()
                break
            end
        end
    end

    data[[n for _ in 1:r]] = rand() #TODO tns is a bad file format

    writetns(f, data)
    return f
end

mutable struct IsTacoFormattableContext
    res
end
function istacoformattable(prgm)
    #println()
    #println()
    ctx = IsTacoFormattableContext(true)
    istacoformattable!(prgm, ctx)
    #println(ctx.res)
    #display(prgm)
    #println()
    return ctx.res
end
function istacoformattable!(node, ctx::IsTacoFormattableContext)
    if istree(node)
        map(arg->istacoformattable!(arg, ctx::IsTacoFormattableContext), arguments(node))
    end
end
function istacoformattable!(node::Access{SymbolicHollowDirector, <:Union{Write, Update}}, ctx::IsTacoFormattableContext)
    if length(getformat(node.tns)) > 1
        ctx.res &= !any(isequal(HashFormat()), getformat(node.tns))
    end
end
function istacoformattable!(node::Access{SymbolicHollowDirector, Read}, ctx::IsTacoFormattableContext)
    if length(getformat(node.tns)) > 1
        ctx.res &= !any(isequal(HashFormat()), getformat(node.tns))
    elseif length(getformat(node.tns)) == 1
        ctx.res &= getprotocol(node.tns)[1] in [StepProtocol(), ConvertProtocol()]
    end
end

struct ReformatReadTacoContext <: AbstractReformatContext
    qnt
    nest
end
ReformatReadTacoContext() = ReformatReadTacoContext([], Dict())
mutable struct ReformatReadTacoTensorContext <: AbstractReformatContext
    qnt
    nest
    tnss
end
mutable struct ReformatReadTacoCollectContext <: AbstractReformatContext
    qnt
    nest
    reqs
end
mutable struct ReformatReadTacoSubstituteContext <: AbstractReformatContext
    qnt
    nest
    tns
    keep
    tns′
    mode
end
function transform_reformat(root, ctx::ReformatReadTacoContext, style::ReformatSymbolicStyle)
    reqs = Dict()
    transform_reformat(root, ReformatReadTacoCollectContext(ctx.qnt, ctx.nest, reqs))
    prods = []
    conss = []
    for ((name, mode), req) in pairs(reqs)
        if issubset(req.idxs[1:req.keep - 1], ctx.qnt) && (mode == Read() || getname(getresult(root)) == getname(req.tns))# && haskey(ctx.nest, name) || req.global
            format′ = req.format[req.keep : end]
            name′ = freshen(getname(req.tns))
            dims′ = req.tns.dims[req.keep : end]
            tns′ = SymbolicHollowTensor(name′, format′, dims′, req.tns.default)
            idxs′ = map(i->Name(freshen(getname(i))), req.idxs[req.keep:end])
            #for now, assume that a different pass will add "default" read/write protocols
            root = transform_reformat(root, ReformatReadTacoSubstituteContext(ctx.qnt, ctx.nest, req.tns, req.keep, tns′, mode))
            conv_protocol = Any[ConvertProtocol() for _ = 1:length(tns′.perm)]
            dir′ = SymbolicHollowDirector(tns′, conv_protocol)
            dir = SymbolicHollowDirector(req.tns, vcat(req.protocol, conv_protocol))
            if mode == Read()
                push!(prods, @i (@loop $idxs′ $dir′[$idxs′] = $(dir)[$(req.idxs[1:req.keep-1]), $idxs′]))
            else
                push!(conss, @i (@loop $idxs′ $(dir)[$(req.idxs[1:req.keep-1]), $idxs′] = $dir′[$idxs′]))
            end
        end
    end
    return foldr(with, conss, init = foldl(with, prods, init = transform_reformat(root, ctx, style.style)))
end
make_style(node, ::ReformatReadTacoContext, ::Access{SymbolicHollowDirector}) = ReformatSymbolicStyle(DefaultStyle())
mutable struct ReformatReadTacoRequest
    tns
    keep
    idxs
    protocol
    format
end
function transform_reformat(node::Access{SymbolicHollowDirector}, ctx::ReformatReadTacoCollectContext, ::DefaultStyle)
    name = getname(node.tns)
    protocol = getprotocol(node.tns)
    format = getformat(node.tns)
    top = get(ctx.nest, name, 0)
    if length(protocol) > 1 && protocol[end] == InsertProtocol() && format[end] in [ListFormat(), NoFormat()]
        req = ctx.reqs[(name, node.mode)] = ReformatReadTacoRequest(node.tns.tns, length(protocol), node.idxs, protocol[1:end-1], Any[HashFormat() for _ in format])
    end
    return node
end
function transform_reformat(node::Access{SymbolicHollowDirector}, ctx::ReformatReadTacoSubstituteContext, ::DefaultStyle)
    if getname(node.tns.tns) == getname(ctx.tns) && node.mode == ctx.mode
        return Access(SymbolicHollowDirector(ctx.tns′, getprotocol(node.tns)[ctx.keep:end]), node.mode, node.idxs[ctx.keep:end])
    end
    return node
end