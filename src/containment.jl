#A few notes:
#Cup() is equivalent to Empty()
#Wedge() is equivalent to true
normalize_time = 0
normalize_calls = 0

#Cup > Such > Times > Vee > Exists > Wedge > Rename

#cap->Wedge
#Vee->Cup

#Can only swap two nodes in one pass!

#We are given an expression such that (cup, such, times) > (vee, exists, wedge)

#thus, we do an inital pass to turn bring Vee to the top, Vee into Cup, and Cup to the top, then we have
# cup > (such, times) > (exists, wedge)
#At this point, we can bring such up, and collapse such, and push wedge down and collapse wedge

#Postwalks can bring things up, prewalks push down
# vee needs to be postwalked


function normalize_asymptote_2(ex)
    ex = Postwalk(Chain([
        (@rule $(Empty()) => Cup()),
        (@rule true => Wedge()),
        (@rule false => Vee()),

        (@rule Such(Cup(), ~p) => Cup()),

        (@rule Times(~~s, Cup(), ~~t) => Cup()),

        (@rule Exists(~~i, Vee()) => Vee()),

        (@rule Wedge(~~p, Vee(), ~~q) => Vee()),

        (@rule Such(~s, Vee()) => Cup()),

        Fixpoint(@rule Wedge(~~p, Wedge(~~q), ~~r) => Wedge(~~p..., ~~q..., ~~r...)), 
        #(@rule Wedge(~~p) => Wedge(unique(~~p)...)),

        Fixpoint(@rule Cup(~~s, Cup(~~t), ~~u) => Cup(~~s..., ~~t..., ~~u...)),
        #(@rule Cup(~~p) => Cup(unique(~~p)...)),

        Fixpoint(@rule Vee(~~p, Vee(~~q), ~~r) => Vee(~~p..., ~~q..., ~~r...)),
        #(@rule Vee(~~p) => Vee(unique(~~p)...)),
        #(@rule Vee(~p) => ~p),
    ]))(ex)

    ex = transform_ssa(ex)
    ex = Postwalk(Chain([
        Prestep(Link([
            (@rule Such(Cup(), ~p) => Cup()),
            (@rule Such(Cup(~s, ~~t), ~p) => Cup(Such(~s, ~p), Such(Cup(~~t...), ~p))),
        ])),

        Prestep(Link([
            (@rule Times(~~s, Cup(), ~~t) => Cup()),
            (@rule Times(~~s, Cup(~t, ~~u), ~~v) => Cup(Times(~~s..., ~t, ~~v...), Times(~~s..., Cup(~~u...), ~~v...))),
        ])),

        Prestep(Link([
            (@rule Exists(~~i, Vee()) => Vee()),
            (@rule Exists(~~i, Vee(~p, ~~q)) => Vee(Exists(~~i..., ~p), Exists(~~i..., Vee(~~q...)))),
        ])),

        Prestep(Link([
            (@rule Wedge(~~p, Vee(), ~~q) => Vee()),
            (@rule Wedge(~~p, Vee(~q, ~~r), ~~s) => Vee(Wedge(~~p..., ~q, ~~s...), Wedge(~~p..., Vee(~~r...), ~~s...))),
        ])),

        Prestep(Link([
            (@rule Such(~s, Vee()) => Cup()),
            (@rule Such(~s, Vee(~p, ~~q)) => Cup(Such(~s, ~p), Such(~s, Vee(~~q...)))),
        ])),

        Fixpoint(@rule Vee(~~p, Vee(~~q), ~~r) => Vee(~~p..., ~~q..., ~~r...)),

        Fixpoint(@rule Cup(~~s, Cup(~~t), ~~u) => Cup(~~s..., ~~t..., ~~u...)),
    ]))(ex)

    ex = Postwalk(Chain([
        Prestep(@rule Times(~~s, Such(~t, ~p), ~~u) => Such(Times(~~s..., ~t, ~~u...), ~p)), #Requires ssa #not really
        Fixpoint(@rule Such(Such(~s, ~p), ~q) => Such(~s, Wedge(~p, ~q))),
    ]))(ex)

    ex = Postwalk(Chain([
        Fixpoint(@rule Times(~~s, Times(~~t), ~~u) => Times(~~s..., ~~t..., ~~u...)),

        Prestep(@rule Wedge(~~p, Exists(~~i, ~q), ~~r) => Exists(~~i..., Wedge(~~p..., ~q, ~~r...))), #Requires ssa
        Fixpoint(@rule Exists(~~i, Exists(~~j, ~p)) => Exists(~~i..., ~~j..., ~p)),
    ]))(ex)

    ex = Postwalk(Chain([
        Fixpoint(@rule Wedge(~~p, Wedge(~~q), ~~r) => Wedge(~~p..., ~~q..., ~~r...)), 
        (@rule Wedge(~~p) => Wedge(unique(~~p)...)),
        (@rule Cup(~~p) => Cup(unique(~~p)...)),
    ]))(ex)

    return ex
end

function normalize_asymptote(x)
    global normalize_time += @elapsed y = normalize_asymptote_2(Such(x, Exists(Wedge())))
    global normalize_calls
    normalize_calls += 1
    return y
end

function normalize_proposition(x)
    global normalize_time += @elapsed y = normalize_asymptote_2(Exists(Wedge(x)))
    global normalize_calls
    normalize_calls += 1
    return y
end

"""
    isdominated(a, b)
    Given abstract set expressions a and b, return true when b dominates a.
    ArgumentError if the answer cannot be determined.
"""
function isdominated(a, b; sunk_costs = [], assumptions = [], normal=false)
    global dominate_calls
    dominate_calls += 1
    normal &= isempty(sunk_costs) && isempty(assumptions)
    function canonicalize(q)
        if !normal
            q = normalize_asymptote(Such(Cup(q, sunk_costs...), Wedge(assumptions...)))
        end
        err = ArgumentError("unrecognized query form: $q")
        (@capture q Cup(~~q_queries)) || throw(err)
        return q_queries
    end
    a_queries = canonicalize(a)
    b_queries = canonicalize(b)
    for a_query in a_queries
        covered = false
        for b_query in b_queries

            if _isdominated(a_query, b_query)
                covered = true
                continue
            end
        end
        if !covered
            return false
        end
    end
    return true
end

function _isdominated(a, b)
    head_op = gensym(:head)

    function canonicalize(q)
        err = ArgumentError("unrecognized query form: $q")
        (@capture q Such(Times(~~q_heads), Exists(~~q_frees, Wedge(~~q_preds)))) || throw(err)
        all(q_head -> q_head isa Domain, q_heads) || throw(err)
        return (q_heads, q_frees, q_preds)
    end
    (a_heads, a_frees, a_preds) = canonicalize(a)
    (b_heads, b_frees, b_preds) = canonicalize(b)

    #at some point we should check that predicate arity is consistent

    #there is very likely a smarter way to do this inside the homomorphism
    #finder that would be much smarter because it would use the existing
    #bindings. I'm just not ready to write that code today. AFAICT, what we want
    #to do is not equivalent to implication testing, and we would need the homomorphism
    #to go "backwards" for the head variables. Something to consider in the future.

    a_frees = vcat(a_frees, map(a_head->a_head.var, a_heads))
    b_frees = vcat(b_frees, map(b_head->b_head.var, b_heads))

    for σ in sympermutations(map(b_head->b_head.rng, b_heads), map(a_head->a_head.rng, a_heads))
        a_head_preds = []
        b_head_preds = []
        for (a_head, b_head) in zip(a_heads, b_heads[σ])
            op = gensym(:op)
            push!(a_head_preds, Predicate(op, a_head.var))
            push!(b_head_preds, Predicate(op, b_head.var))
        end
        if isimplied(Exists(a_frees..., Wedge(vcat(a_head_preds, a_preds)...)), Exists(b_frees..., Wedge(vcat(b_head_preds, b_preds)...)), normal=true)
            return true
        end
    end
    return false
end

"""
    isimplied(a, b)
    Given abstract predicate expressions a and b, return true when b implies a.
    ArgumentError if the answer cannot be determined.
"""
function isimplied(a, b; assumptions = [], normal=false)
    normal &= isempty(assumptions)
    function canonicalize(p)
        err = ArgumentError("unrecognized proposition: $p")
        if !normal
            p = normalize_proposition(Exists(Wedge(p, assumptions...)))
        end
        (@capture p Exists(~~p_frees, Wedge(~~p_preds))) || throw(err)
        p_op_args = Dict()
        for p_pred in p_preds
            p_pred isa Predicate || throw(err)
            push!(get!(p_op_args, p_pred.op, []), p_pred.args)
        end
        return (p_frees, p_op_args, p_preds)
    end

    (a_frees, a_op_args, a_preds) = canonicalize(a)
    (b_frees, b_op_args, b_preds) = canonicalize(b)

    keys(b_op_args) ⊆ keys(a_op_args) || return false

    #is this a good heuristic?
    b_preds = sort(b_preds, by=b_pred->length(a_op_args[b_pred.op]))

    morph = Dict() #mighty morphin' power rangers...
    depth = 1
    width = ones(Int, length(b_preds))
    bindings = [[] for _ = 1:length(b_preds)]
    while true
        if depth > length(b_preds)
            return true
        end
        b_pred = b_preds[depth]

        if width[depth] > length(a_op_args[b_pred.op])
            width[depth] = 1
            depth -= 1
            if depth > 0
                width[depth] += 1
            else
                break
            end
            continue
        end
        a_args = a_op_args[b_pred.op][width[depth]]

        conflict = false
        for b_idx in bindings[depth]
            delete!(morph, b_idx)
        end
        empty!(bindings[depth])
        for (a_idx, b_idx) in zip(a_args, b_pred.args)
                if haskey(morph, b_idx)
                    if morph[b_idx] != a_idx
                        conflict = true
                        break
                    end
            elseif b_idx in b_frees
                    push!(bindings[depth], b_idx)
                    morph[b_idx] = a_idx
            elseif b_idx != a_idx
                conflict = true
                break
            end
        end

        if !conflict
            depth += 1
        else
            for b_idx in bindings[depth]
                delete!(morph, b_idx)
            end
            empty!(bindings[depth])
            width[depth] += 1
        end
    end

    return false
end

#=
supersimplify_asymptote = Fixpoint(Chain([simplify_asymptote,#This should be normalize_asymptote 
    #(@rule ~p => display(~p)),
Postwalk(Chain([
    (@rule Such(~t, Wedge(~~p, ~q, ~~r)) => begin
        if isdominated(Such(~t, Wedge(~~p..., ~~r...)), Such(~t, Wedge(~~p..., ~q, ~~r...)))
            Such(~t, Wedge(~~p..., ~~r...))
        end
    end),

    (@rule Such(~t, Exists(~~i, Wedge(~~p, ~q, ~~r))) => begin
        #println("does")
        #display(Such(~t, Exists(~~i..., Wedge(~~p..., ~~r..., true)))) 
        #println("dominate")
        #display(Such(~t, Exists(~~i..., ~q)))
        #println("??")
        if isdominated(Such(~t, Exists(~~i..., Wedge(~~p..., ~~r...))), Such(~t, Exists(~~i..., Wedge(~~p..., ~q, ~~r...))))
            Such(~t, Exists(~~i..., Wedge(~~p..., ~~r...)))
        end
    end),

    (@rule Cup(~~s, ~t, ~~u) => begin
        if isdominated(~t, Cup(~~s..., ~~u...))
            Cup(~~s..., ~~u...)
        end
    end),
]))]))
=#

function supersimplify_asymptote(a; normal = false)
    if !normal
        a = normalize_asymptote(a)
    end
    err = ArgumentError("unrecognized asymptote form: $a")
    (@capture a Cup(~~a_queries)) || throw(err)

    a_queries = map(a_queries) do q
        (@capture q Such(Times(~~q_heads), ~q_that)) || throw(err)
        all(q_head -> q_head isa Domain, q_heads) || throw(err)
        Such(Times(q_heads...), supersimplify_proposition(q_that, normal = true))
    end

    b_queries = []
    for a_query in a_queries[randperm(end)]
        b_queries′ = Any[a_query]
        keep = true
        for b_query in b_queries
            dom_a = _isdominated(a_query, b_query)
            dom_b = _isdominated(b_query, a_query)
            if dom_a
                keep = false
                break
            elseif !dom_b
                push!(b_queries′, b_query)
            end
        end
        if keep
            b_queries = b_queries′
        end
    end

    return Cup(b_queries...)
end

function supersimplify_proposition(p; normal = false)
    err = ArgumentError("unrecognized proposition: $p")
    if !normal
        p = normalize_proposition(p)
    end
    (@capture p Exists(~~p_frees, Wedge(~~p_preds))) || throw(err)
    i = 1
    while i <= length(p_preds)
        q_preds = collect(p_preds)
        popat!(q_preds, i)
        if isimplied(Exists(p_frees..., Wedge(q_preds...)), Exists(p_frees..., Wedge(p_preds...)), normal=true)
            p_preds = q_preds
        else
            i += 1
        end
    end
    return Exists(p_frees..., Wedge(p_preds...))
end

function asymptote_equal(a, b, assumptions=[], sunk_costs=[])
    a = simplify_asymptote(Cup(a, sunk_costs...))
    b = simplify_asymptote(Cup(b, sunk_costs...))
    return isdominated(a, b, assumptions=assumptions) && isdominated(b, a, assumptions=assumptions)
end