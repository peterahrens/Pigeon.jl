normalize_index = Fixpoint(Postwalk(Chain([
	(@ex@rule i"+(~~a, +(~~b), ~~c)"p => i"+(~~a, ~~b, ~~c)"c),
	(@ex@rule i"+(~a)"p => ~a),
	(@ex@rule i"~a - ~b"p => i"~a + (- ~b)"c),
	(@ex@rule i"- (- ~a)"p => ~a),
	(@ex@rule i"- +(~a, ~~b)"p => i"+(- ~a, - +(~~b))"c),
	(@ex@rule i"*(~~a, *(~~b), ~~c)"p => i"*(~~a, ~~b, ~~c)"c),
	(@ex@rule i"*(~a)"p => ~a),
	(@ex@rule i"*(~~a, - ~b, ~~c)"p => i"-(*(~~a, ~b, ~~c))"c),
	(@ex@rule i"+(~~a)"p => if !issorted(~~a) i"+($(sort(~~a)))"c end),
	(@ex@rule i"*(~~a)"p => if !issorted(~~a) i"*($(sort(~~a)))"c end),
	(@ex@rule i"∀ (~~i) ∀ (~~j) ~s"p => i"∀ (~~i), (~~j) ~s"c),
])))