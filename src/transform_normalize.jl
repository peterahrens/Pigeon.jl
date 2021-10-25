normalize_index = Fixpoint(Postwalk(Chain([
	(@ex@rule @i(+(~~a, +(~~b), ~~c)) => @i +(~~a, ~~b, ~~c)),
	(@ex@rule @i(+(~a)) => ~a),
	(@ex@rule @i(~a - ~b) => @i ~a + (- ~b)),
	(@ex@rule @i(- (- ~a)) => ~a),
	(@ex@rule @i(- +(~a, ~~b)) => @i +(- ~a, - +(~~b))),
	(@ex@rule @i(*(~~a, *(~~b), ~~c)) => @i *(~~a, ~~b, ~~c)),
	(@ex@rule @i(*(~a)) => ~a),
	(@ex@rule @i(*(~~a, - ~b, ~~c)) => @i -(*(~~a, ~b, ~~c))),
	#(@ex@rule @i(+(~~a)) => if !issorted(~~a) @i +($(sort(~~a))) end),
	#(@ex@rule @i(*(~~a)) => if !issorted(~~a) @i *($(sort(~~a))) end),
	(@ex@rule @i(@loop ~~i @loop ~~j ~s) => @i @loop ~~i ~~j ~s),
])))