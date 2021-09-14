#A few notes:
#Cup() is equivalent to Empty()
#Wedge() is equivalent to true

normalize_asymptote = Fixpoint(Postwalk(Chain([
    (@rule $(Empty()) => Cup()),

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

    (@rule Exists(~~i, Exists(~~j, ~p)) => Exists(~~i..., ~~j..., ~p)),
    (@rule Wedge(~~p, Exists(~~i, ~q), ~~r) => begin
        i′ = freshen.(~~i)
        q′ = Postwalk(subex->get(Dict(Pair.(~~i, i′)...), subex, subex))(~q)
        Exists(i′..., Wedge(~~p..., q′, ~~r...))
    end),

    (@rule Exists(~~i, Vee(~p, ~q, ~~r)) =>
        Vee(Exists(~~i, ~p), Exists(~~i, Vee(~q, ~~r)))),
])))


struct _isdominated_Head end

"""
    isdominated(a, b)
    Given abstract set expressions a and b, return true when b dominates a.
    ArgumentError if the answer cannot be determined.
"""
function isdominated(a, b)
    vars = Dict()
    preds = Dict()

    function canonicalize_set(q)
        q = normalize_asymptote(Cup(q))
        err = ArgumentError("unrecognized query form: $q")
        q isa Cup || throw(err)
        (@capture q Cup(~~q_terms)) || throw(err)
        return map(q_terms) do q_term
            q_term = normalize_asymptote(Such(Times(q_term), Exists(Wedge(true))))
            (@capture q_term Such(Times(~~q_heads), ~q_that)) || throw(err)
            return (q_heads, q_that)
        end
    end

    function canonicalize_pred(q, r_heads, q_that)
        err = ArgumentError("unrecognized query form: $q")
        q_term = normalize_asymptote(Wedge(map(r_head->Predicate(_isdominated_Head(), r_head), r_heads)..., q_that))
        (@capture q_term Exists(~~q_frees, Wedge(~~q_preds))) || throw(err)
        q_op_args = Dict()
        for q_pred in q_preds
            q_pred isa Predicate || throw(err)
            push!(get!(q_op_args, q_pred.op, []), q_pred.args)
        end
        return (q_op_args, q_preds)
    end

    a_terms = canonicalize_set(a)
    b_terms = canonicalize_set(b)

    #at some point we should check that predicate arity is consistent

    for (a_heads, a_that) in a_terms
        covered = false
        for (b_heads, b_that) in b_terms
            (a_op_args, a_preds) = canonicalize_pred(a, b_heads, a_that)
            (b_op_args, b_preds) = canonicalize_pred(b, a_heads, b_that)
            keys(b_op_args) ⊆ keys(a_op_args) || continue
            #is this a good heuristic?
            b_preds = sort(b_preds, by=b_pred->length(a_op_args[b_pred.op]))

            morph = Dict() #mighty morphin' power rangers...
            depth = 1
            width = ones(Int, length(b_preds))
            bindings = [[] for _ = 1:length(b_preds)]
            while true
                if depth > length(b_preds)
                    covered = true
                    break
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
                    else
                        push!(bindings[depth], b_idx)
                        morph[b_idx] = a_idx
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

            if covered
                break
            end
        end
        if !covered
            return false
        end
    end
    return true
end

supersimplify_asymptote = Fixpoint(Chain([simplify_asymptote, 
    #(@rule ~p => display(~p)),
Postwalk(Chain([
    (@rule Such(~t, Wedge(~~p, ~q, ~~r)) => begin
        if isdominated(Such(~t, Wedge(~~p..., ~~r..., true)), Such(~t, ~q))
            if isempty(~~p) && isempty(~~r)
                Such(~t, true)
            else
                Such(~t, Wedge(~~p..., ~~r..., true))
            end
        end
    end),

    (@rule Such(~t, Exists(~~i, Wedge(~~p, ~q, ~~r))) => begin
        #println("does")
        #display(Such(~t, Exists(~~i..., Wedge(~~p..., ~~r..., true)))) 
        #println("dominate")
        #display(Such(~t, Exists(~~i..., ~q)))
        #println("??")
        if isdominated(Such(~t, Exists(~~i..., Wedge(~~p..., ~~r..., true))), Such(~t, Exists(~~i..., ~q)))
            if isempty(~~p) && isempty(~~r)
                Such(~t, Exists(~~i..., true))
            else
                Such(~t, Exists(~~i..., Wedge(~~p..., ~~r..., true)))
            end
        end
    end),

    (@rule Cup(~~s, ~t, ~~u) => begin
        if isdominated(~t, Cup(~~s..., Empty(), ~~u...))
            if isempty(~~s) && isempty(~~u)
                return Empty()
            else
                Cup(~~s..., ~~u...)
            end
        end
    end),
]))]))

function asymptote_equal(a, b)
    a = simplify_asymptote(a)
    b = simplify_asymptote(b)
    return isdominated(a, b) && isdominated(b, a)
end