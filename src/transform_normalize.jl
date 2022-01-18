normalize_index = Rewrite(Fixpoint(Postwalk(Chain([
	(@rule @i(+(~~a, +(~~b), ~~c)) => @i +(~~a, ~~b, ~~c)),
	(@rule @i(+(~a)) => ~a),
	(@rule @i(~a - ~b) => @i ~a + (- ~b)),
	(@rule @i(- (- ~a)) => ~a),
	(@rule @i(- +(~a, ~~b)) => @i +(- ~a, - +(~~b))),
	(@rule @i(*(~~a, *(~~b), ~~c)) => @i *(~~a, ~~b, ~~c)),
	(@rule @i(*(~a)) => ~a),
	(@rule @i(*(~~a, - ~b, ~~c)) => @i -(*(~~a, ~b, ~~c))),
	#(@rule @i(+(~~a)) => if !issorted(~~a) @i +($(sort(~~a))) end),
	#(@rule @i(*(~~a)) => if !issorted(~~a) @i *($(sort(~~a))) end),
	(@rule @i(@loop ~~i @loop ~~j ~s) => @i @loop ~~i ~~j ~s),
]))))