mutable struct TacoLowerContext
    tensor_variable_names
    index_variable_names
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
end

function TacoLowerContext()
    tensor_variable_names = Dict()
    index_variable_names = Dict()
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

    TacoLowerContext(
        tensor_variable_names,
        index_variable_names,
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
        output
    )
end

function script!(node::With, ctx::TacoLowerContext)
    push!(ctx.names, getname(getresult(prod)))
    prod = script!(node.prod, ctx)
    cons = script!(node.cons, ctx)
    delete!(ctx.names, getname(getresult(prod)))
    return "where($prod, $cons)"
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
    "$(node.op)($(join(map(arg->script!(arg, ctx), node.args), ", ")))"
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

taco_format(::ArrayFormat) = "Dense()"
taco_format(::ListFormat) = "Sparse()"

function script!(node::Access, ctx::TacoLowerContext)
    idxs = map(idx->script_index!(idx, ctx), node.idxs)
    tns = node.tns
    if !haskey(ctx.tensor_variable_names, getname(node.tns))
        ctx.tensor_variable_names[getname(node.tns)] = "tensor_$(getname(node.tns))"

        if getname(node.tns) in ctx.names
            ctx.tensor_file_readers = """
            $(ctx.tensor_file_readers)
            Tensor<double> tensor_$(getname(tns)) = read(file_$(getname(tns)), Format({$(join(map(taco_format, getformat(tns)), ", "))}));
            """
        elseif !(getname(node.tns) in ctx.inputs)

            ctx.tensor_file_headers = """
            $(ctx.tensor_file_headers)
            std::string file_$(getname(tns)) = "";
            """

            ctx.tensor_file_options = """
            $(ctx.tensor_file_options)
            {"tensor_$(getname(tns))", required_argument, 0, 0},
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
                Tensor<double> tensor_$(getname(tns)) = read(file_$(getname(tns)), Format({$(join(map(taco_format, getformat(tns)), ", "))}), pack=true);
                """
            else
                ctx.output = "tensor_$(getname(tns))"
            
                ctx.tensor_output_constructors = """
                $(ctx.tensor_output_constructors)
                tensor_$(getname(tns)) Tensor<double>(Format({$(join(map(taco_format, getformat(tns)), ", "))}));
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
    return "tensor_$(getname(tns))[$(join(idxs, ", "))]"
end

#=
lower_axes(tns::SymbolicHollowDirector, ctx) = lower_axes(tns.tns, ctx)[getsites(tns)]
function lower_axes(tns::SymbolicHollowTensor, ctx) = map(1:length(tns.dims)) do i
    if ctx.tns[getname(tns)].isinput
        "$(ctx.tns).getDimensions()[mode]"
    else
        nothing
    end
end

lower_axis_merge(::AsymptoticContext, a, b) = a === nothing ? b : a
=#

function lower_taco(prgm)
    ctx = TacoLowerContext()
    cin = script!(prgm, ctx)

    script = """
    #include "taco/tensor.h"
    //#include "taco/format.h"
    //#include "taco/lower/lower.h"
    //#include "taco/ir/ir.h"
    #include "sparrow.hpp"
    #include <iostream>
    #include <getopt.h>
    #include <sys/stat.h>
    #include <string>

    using namespace taco;

    static void usage()
    {
        fprintf(stderr,
            "usage: foo [options]\\n"
            "  -n, --ntrials <arg>        Maximum number of trials to run\\n"
            "  -t, --ttrials <arg>        Maximum time to run trials\\n"
            "  -h, --help                 Display help message\\n");
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
            const char *options = "n:t:h";
            const struct option long_options[] = {
                {"ntrials", required_argument, 0, 'n'},
                {"ttrials", required_argument, 0, 't'},
                {"help", no_argument, &help, 1},
                $(ctx.tensor_file_options)
                {0, 0, 0, 0}};

            /* getopt_long stores the option index here. */
            int option_index = 0;

            int c = getopt_long(argc, argv, options, long_options, &option_index);

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

        // Create tensors
        $(ctx.tensor_file_readers)

        // Pack inserted data as described by the formats
        $(ctx.tensor_output_constructors)

        // Form a tensor-vector multiplication expression
        $(ctx.index_headers)

        // Compile the expression
        $(ctx.output).compile($cin);

        // Assemble output indices and numerically compute the result
        auto time = benchmark(
            10, 10000, [&$(ctx.output)]()
            { $(ctx.output).assemble(); },
            [&$(ctx.output)]()
            { $(ctx.output).compute(); });

        std::cout << time << std::endl;

        $(ctx.tensor_writers)

        return 0;
    }
    """

    script = read(open(`clang-format`, "r", IOBuffer(script)), String)
    return script
end
