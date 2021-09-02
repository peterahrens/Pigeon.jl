normalize_asymptote = Fixpoint(Postwalk(Chain([
    (@rule Such(Such(~s, ~p), ~q) => Such(~s, Wedge(~p, ~q))),

    (@rule Such(~s, false) => Empty()),
    (@rule Such($(Empty()), ~p) => Empty()),

    (@rule Wedge(~~p, Wedge(~~q), ~~r) => Wedge(~~p..., ~~q..., ~~r...)),
    (@rule Wedge(~~p, true, ~q, ~~r) => Wedge(~~p..., ~q, ~r...)),
    (@rule Wedge(~~p, ~q, true, ~~r) => Wedge(~~p..., ~q, ~r...)),
    (@rule Wedge(~~p, false, ~q, ~~r) => false),
    (@rule Wedge(~~p, ~q, false, ~~r) => false),
    (@rule Wedge(~~p, ~q, ~~r, ~q, ~~s) => Wedge(~~p..., ~q, ~~r..., ~~s...)),

    (@rule Vee(~p) => ~p),

    (@rule Wedge(~~p, Vee(~q, ~r, ~~s), ~~t) => 
        Vee(Wedge(~~p..., ~q, ~~t...), Wedge(~~p..., Vee(~r, ~~s...), ~~t...))),

    (@rule Cup(~~s, $(Empty()), ~t, ~~u) => Cup(~~s..., ~t, ~~u...)),
    (@rule Cup(~~s, ~t, $(Empty()), ~~u) => Cup(~~s..., ~t, ~~u...)),
    (@rule Cup($(Empty())) => Empty()),
    (@rule Cup(~~s, Cup(~~t), ~~u) => Cup(~~s..., ~~t..., ~~u...)),
    (@rule Cup(~~s, ~t, ~~u, ~t, ~~v) => Cup(~~s..., ~t, ~~u..., ~~v...)),

    (@rule Cap(~~s, $(Empty()), ~~u) => Empty()),
    (@rule Cap(~s) => ~s),

    (@rule Times(~~s, $(Empty()), ~~u) => Empty()),
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
    
"""
    isdominated(a, b)
    Given abstract set expressions a and b, return true when b dominates a.
    ArgumentError if the answer cannot be determined.
"""
function isdominated(a, b)
    a = normalize_asymptote(Cup(a))
    b = normalize_asymptote(Cup(b))
    #display(a)
    #display(b)
    #println("begin domination analysis")
    err_a = ArgumentError("unrecognized form of a: $a")
    err_b = ArgumentError("unrecognized form of b: $b")
    if a == Empty()
        return true
    elseif b == Empty()
        return false
    end
    (@capture a Cup(~~terms_a)) || throw(err_a)
    (@capture b Cup(~~terms_b)) || throw(err_b)

    #at some point we should check that predicate arity is consistent

    for term_a in terms_a
        term_a = normalize_asymptote(Such(Times(term_a), Exists(Wedge(true))))
        (@capture term_a Such(Times(~~head_a), Exists(~~free_a, Wedge(~~preds_a)))) || throw(err_a)

        preds_a == [true] || all(isa.(preds_a, (Predicate,))) || throw(err_a)

        if preds_a != [true]
            op_preds_a = Dict()
            for pred_a in preds_a
                op_preds_a[pred_a.op] = push!(get(op_preds_a, pred_a.op, []), pred_a)
            end

            #related to comment on line 120
            for op in keys(op_preds_a)
                op_preds_a[op] = push!(op_preds_a[op], Predicate(op, (gensym() for _ in first(op_preds_a[op]).args)...))
            end
        end


        covered = false
        for term_b = terms_b
            term_b = normalize_asymptote(Such(Times(term_b), Exists(Wedge(true))))

            (@capture term_b Such(Times(~~head_b), Exists(~~free_b, Wedge(~~preds_b)))) || throw(err_b)

            if !(head_a ⊆ head_b)
                continue
            end

            #THIS IS A WEIRD LINE OF CODE
            morefree_b = setdiff(head_b, head_a)

            if preds_b == [true]
                covered = true
                continue
            end
            if preds_a == [true]
                continue
            end

            all(isa.(preds_b, (Predicate,))) || throw(err_b)

            #if !(map(pred_b->pred_b.op, preds_b) ⊆ keys(op_preds_a))
            #    continue
            #end

            # a really silly block of code that makes everything really awful.
            # This line of code assumes that every predicate has at least one setting
            # which makes it true
            for pred_b in preds_b
                if !haskey(op_preds_a, pred_b.op)
                    op_preds_a[pred_b.op] = push!(get(op_preds_a, pred_b.op, []), Predicate(pred_b.op, (gensym() for _ in pred_b.args)...))
                end
            end

            #look for a homomorphism from b to a, i.e. a mapping h from indices
            #of b to indices of a such that for each pred p(i...) in b, theres a
            #pred p(h.(i)...) in a

            morph = Dict() #mighty morphin' power rangers...
            depth = 1
            width = ones(Int, length(preds_b))
            bindings = [[] for _ = 1:length(preds_b)]
            while true
                if depth > length(preds_b)
                    covered = true
                    break
                end
                b_pred = preds_b[depth]

                if width[depth] > length(op_preds_a[b_pred.op])
                    width[depth] = 1
                    depth -= 1
                    if depth > 0
                        width[depth] += 1
                    else
                        break
                    end
                    continue
                end
                a_pred = op_preds_a[b_pred.op][width[depth]]

                conflict = false
                for b_idx in bindings[depth]
                    delete!(morph, b_idx)
                end
                empty!(bindings[depth])
                for (a_idx, b_idx) in zip(a_pred.args, b_pred.args)
                    if (b_idx in free_b) || (b_idx in morefree_b)
                        if haskey(morph, b_idx)
                            if morph[b_idx] != a_idx
                                conflict = true
                                break
                            end
                        else
                            push!(bindings[depth], b_idx)
                            morph[b_idx] = a_idx
                        end
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