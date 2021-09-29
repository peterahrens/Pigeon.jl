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

        (@rule Times(~~s, Cup(), ~~u) => Cup()),

        (@rule Exists(~~i, Vee()) => Vee()),

        (@rule Wedge(~~p, Vee(), ~~s) => Vee()),

        (@rule Such(~s, Vee()) => Cup()),

        #=
        Fixpoint(@rule Wedge(~~p, Wedge(~~q), ~~r) => Wedge(~~p..., ~~q..., ~~r...)), 
        (@rule Wedge(~~p) => Wedge(unique(~~p)...)),

        Fixpoint(@rule Cup(~~s, Cup(~~t), ~~u) => Cup(~~s..., ~~t..., ~~u...)),
        (@rule Cup(~~p) => Cup(unique(~~p)...)),

        Fixpoint(@rule Vee(~~p, Vee(~~q), ~~r) => Vee(~~p..., ~~q..., ~~r...)),
        (@rule Vee(~~p) => Vee(unique(~~p)...)),
        (@rule Vee(~p) => ~p),
        =#
    ]))(ex)

    ex = transform_ssa(ex)

    ex = Postwalk(Chain([
        Prestep(Link([
            (@rule Such(Cup(), ~p) => Cup()),
            (@rule Such(Cup(~s, ~~t), ~p) => Cup(Such(~s, ~p), Such(Cup(~~t...), ~p))),
        ])),

        Prestep(Link([
            (@rule Times(~~s, Cup(), ~~u) => Cup()),
            (@rule Times(~~s, Cup(~t, ~~u), ~~v) => Cup(Times(~~s..., ~t, ~~v...), Times(~~s..., Cup(~~u...), ~~v...))),
        ])),

        Prestep(Link([
            (@rule Exists(~~i, Vee()) => Vee()),
            (@rule Exists(~~i, Vee(~p, ~~q)) => Vee(Exists(~~i..., ~p), Exists(~~i..., ~~q...))),
        ])),

        Prestep(Link([
            (@rule Wedge(~~p, Vee(), ~~s) => Vee()),
            (@rule Wedge(~~p, Vee(~q, ~~r), ~~s) => Vee(Wedge(~~p..., ~q, ~~r...), Wedge(~~p..., Vee(~~r...), ~~s...))),
        ])),

        Prestep(Link([
            (@rule Such(~s, Vee()) => Cup()),
            (@rule Such(~s, Vee(~p, ~~q)) => Cup(Such(~s, ~p), Such(~s, Vee(~~q...)))),
        ])),

        Fixpoint(@rule Vee(~~p, Vee(~~q), ~~r) => Vee(~~p..., ~~q..., ~~r...)),

        Fixpoint(@rule Cup(~~s, Cup(~~t), ~~u) => Cup(~~s..., ~~t..., ~~u...)),
    ]))(ex)

    ex = Postwalk(Chain([
        Prestep(@rule Times(~~s, Such(~t, ~p), ~~u) => Such(Times(~~s..., ~t, ~~u...), ~p)), #Requires ssa
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
#=
    global normalize_time += @elapsed y = begin
    Fixpoint(Postwalk(Chain([
    (@rule $(Empty()) => Cup()),
    (@rule true => Wedge()),
    (@rule false => Vee()),

    (@rule Such(Such(~s, ~p), ~q) => Such(~s, Wedge(~p, ~q))),

    (@rule Such(~s, false) => Cup()),
    (@rule Such(Cup(), ~p) => Cup()),

    (@rule Wedge(~~p, true, ~~q) => Wedge(~~p..., ~~q...)),
    (@rule Wedge(~~p, Wedge(~~q), ~~r) => Wedge(~~p..., ~~q..., ~~r...)),
    (@rule Wedge(~~p, false, ~~q) => false),
    (@rule Wedge(~~p, ~q, ~~r, ~q, ~~s) => Wedge(~~p..., ~q, ~~r..., ~~s...)),

    (@rule Vee(~p) => ~p),

    (@rule Wedge(~~p, Vee(~q, ~r, ~~s), ~~t) => 
        Vee(Wedge(~~p..., ~q, ~~t...), Wedge(~~p..., Vee(~r, ~~s...), ~~t...))),

    (@rule Cup(~~s, Cup(), ~~t) => Cup(~~s..., ~~t...)),
    (@rule Cup(~~s, Cup(~~t), ~~u) => Cup(~~s..., ~~t..., ~~u...)),
    (@rule Cup(~~s, ~t, ~~u, ~t, ~~v) => Cup(~~s..., ~t, ~~u..., ~~v...)),

    (@rule Cap(~~s, $(Cup()), ~~u) => Cup()),
    (@rule Cap(~s) => ~s),

    (@rule Times(~~s, $(Cup()), ~~u) => Cup()),
    (@rule Times(~~s, Times(~~t), ~~u) => Times(~~s..., ~~t..., ~~u...)),
    (@rule Times(Such(~s, ~p), ~~t) => Such(Times(~s, ~~t...), ~p)),
    (@rule Times(Cup(~s, ~t, ~~u), ~~v) => Cup(Times(~s, ~~v...), Times(Cup(~t, ~~u...), ~~v...))),
    (@rule Times(Cup(~s), ~~t) => Cup(Times(~s), ~~t...)),

    (@rule Such(~t, Vee(~p, ~q)) => 
        Cup(Such(~t, ~p), Such(~t, ~q))),
    (@rule Such(Cup(~s, ~t, ~~u), ~p) => 
        Cup(Such(~s, ~p), Such(Cup(~t, ~~u...), ~p))),
    (@rule Such(Cup(~s), ~p) => Cup(Such(~s, ~p))),
    (@rule Cap(~~s, Such(~t, ~p), ~~u, Such(~t, ~q), ~~v) =>
        Cap(~~s..., Such(~t, Wedge(~p, ~q)), ~~u..., ~~v...)),

    (@rule Exists(~~i, false) => false),
    (@rule Exists(~~i, Exists(~~j, ~p)) => Exists(~~i..., ~~j..., ~p)),
    (@rule Wedge(~~p, Exists(~~i, ~q), ~~r) => begin
        i′ = freshen.(~~i)
        subs = Dict(Pair.(~~i, i′)...)
        q′ = Postwalk(subex->get(subs, subex, subex))(~q)
        Exists(i′..., Wedge(~~p..., q′, ~~r...))
    end),

    (@rule Exists(~~i, Vee(~p, ~q, ~~r)) =>
        Vee(Exists(~~i..., ~p), Exists(~~i..., Vee(~q, ~~r...)))),
])))(x)
end
=#
    global normalize_time += @elapsed y = normalize_asymptote_2(x)
    global normalize_calls
    normalize_calls += 1
    return y
end

"""
    isdominated(a, b)
    Given abstract set expressions a and b, return true when b dominates a.
    ArgumentError if the answer cannot be determined.
"""
function isdominated(a, b; sunk_costs = [], assumptions = [])
    global dominate_calls
    dominate_calls += 1
    function canonicalize(q)
        q = normalize_asymptote(Cup(q))
        err = ArgumentError("unrecognized query form: $q")
        (@capture q Cup(~~q_queries)) || throw(err)
        return q_queries
    end
    a_queries = canonicalize(Cup(a, sunk_costs...))
    b_queries = canonicalize(Cup(b, sunk_costs...))
    for a_query in a_queries
        covered = false
        for b_query in b_queries

            if _isdominated(a_query, b_query, assumptions)
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

function _isdominated(a, b, assumptions)
    head_op = gensym(:head)

    function canonicalize(q)
        err = ArgumentError("unrecognized query form: $q")
        q = normalize_asymptote(Such(Times(q), Exists(Wedge(true))))
        (@capture q Such(Times(~~q_heads), ~q_that)) || throw(err)
        all(q_head -> q_head isa Domain, q_heads) || throw(err)
        return(q_heads, q_that)
    end
    a_heads, a_that = canonicalize(a)
    b_heads, b_that = canonicalize(b)

    #at some point we should check that predicate arity is consistent

    #there is very likely a smarter way to do this inside the homomorphism
    #finder that would be much smarter because it would use the existing
    #bindings. I'm just not ready to write that code today. AFAICT, what we want
    #to do is not equivalent to implication testing, and we would need the homomorphism
    #to go "backwards" for the head variables. Something to consider in the future.

    a_prop = Wedge(map(a_head->Predicate(a_head.rng, a_head.var), a_heads)..., a_that)
    a_prop = Exists(map(a_head->a_head.var, a_heads)..., a_prop)
    a_prop = Wedge(a_prop, assumptions...) #This feels wrong TODO are these variables right?

    for σ in sympermutations(map(b_head->b_head.rng, b_heads), map(a_head->a_head.rng, a_heads))
        b_prop = b_that
        for (a_head, b_head) in zip(a_heads, b_heads[σ])
            b_prop = Wedge(b_prop, Predicate(b_head.rng, b_head.var))
        end
        b_prop = Exists(map(b_head->b_head.var, b_heads)..., b_prop)
        if isimplied(a_prop, b_prop)
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
function isimplied(a, b)
    function canonicalize(p)
        err = ArgumentError("unrecognized proposition: $p")
        p = normalize_asymptote(Exists(Wedge(p)))
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

supersimplify_asymptote = Fixpoint(Chain([simplify_asymptote, 
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

function asymptote_equal(a, b, assumptions=[], sunk_costs=[])
    a = simplify_asymptote(Cup(a, sunk_costs...))
    b = simplify_asymptote(Cup(b, sunk_costs...))
    return isdominated(a, b, assumptions=assumptions) && isdominated(b, a, assumptions=assumptions)
end