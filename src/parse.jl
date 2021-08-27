const index_notation_grammar = """
?start: _statement

_statement: where | _producer
where: _statement _WHERE _producer
_producer: loop | assign | _expression
loop: _LOOP _arguments _statement
assign: _expression [_argument] _EQUALS _expression
_expressions: _expression (_COMMA _expression)*
_expression: add | subtract | negate | _term
add: _expression PLUS _term
subtract: _expression MINUS _term
negate: MINUS _term
_term: multiply | divide | _factor
multiply: _term TIMES _factor
divide: _term SLASH _factor
_factor: exponentiate | _base
exponentiate: _base CARET _factor
_base: call | access | _argument
call: _argument _OPEN_PAREN [_expressions] _CLOSE_PAREN
access: _argument _OPEN_BRACKET [_expressions] _CLOSE_BRACKET
_arguments: _argument (_COMMA _argument)*
splat: _argument _ELLIPSIS
_argument: splat | _leaf
slot: _APPROX NAME
segment: _APPROX _APPROX NAME
_leaf: INTERPOLATE | slot | segment | LITERAL | NAME | PLUS | MINUS | TIMES | SLASH | CARET | _OPEN_PAREN _statement _CLOSE_PAREN

PLUS: /\\+\\s*/
MINUS: /\\-\\s*/
TIMES: /\\*\\s*/
SLASH: /\\/\\s*/
CARET: /\\^\\s*/

_WHERE: /##where#\\s*/
_EQUALS: /\\=\\s*/
_COMMA: /,\\s*/
_APPROX: /~/
_ELLIPSIS: /\\.\\.\\.\\s*/
_OPEN_PAREN: /\\(\\s*/
_CLOSE_PAREN: /\\)\\s*/
_OPEN_BRACKET: /\\[\\s*/
_CLOSE_BRACKET: /\\]\\s*/
_LOOP: /##loop#\\s*/

LITERAL: /\\-?[0-9]+\\.?[0-9]*\\s*/
NAME: /[_A-Za-z][_A-Za-z0-9]*\\s*/
INTERPOLATE: /##interpolate#[0-9_]*\\s*/

%import common.SIGNED_NUMBER
%import common.CNAME
"""

const index_notation_parser = Lerche.Lark(index_notation_grammar, parser="lalr",lexer="contextual")

struct TreeToIndex <: Lerche.Transformer
    bindings
end

Lerche.@inline_rule where(t::TreeToIndex, cons, prod) = :(_where($cons, $prod))
Lerche.@rule loop(t::TreeToIndex, args) = :(loop($(args[1:end-1]...), $(args[end])))
Lerche.@terminal PLUS(t::TreeToIndex, _) = Literal(+)
Lerche.@terminal MINUS(t::TreeToIndex, _) = Literal(-)
Lerche.@terminal TIMES(t::TreeToIndex, _) = Literal(*)
Lerche.@terminal SLASH(t::TreeToIndex, _) = Literal(/)
Lerche.@terminal CARET(t::TreeToIndex, _) = Literal(^)
Lerche.@terminal NAME(t::TreeToIndex, name) = Name(Symbol(strip(String(name), [' ',])))
Lerche.@terminal INTERPOLATE(t::TreeToIndex, name) = t.bindings[Symbol(strip(String(name), [' ',]))]
Lerche.@terminal LITERAL(t::TreeToIndex, num) = Literal(parse(Int, strip(String(num), [' ',])))
Lerche.@inline_rule slot(t::TreeToIndex, name) = esc(:(~$(name.name)))
Lerche.@inline_rule segment(t::TreeToIndex, name) = esc(:(~~$(name.name)))
Lerche.@inline_rule splat(t::TreeToIndex, arg) = :($arg...)
Lerche.@rule assign(t::TreeToIndex, lhs_op_rhs) = :(assign($(lhs_op_rhs...)))
Lerche.@inline_rule access(t::TreeToIndex, tns, idxs...) = :(access($tns, $(idxs...)))
Lerche.@inline_rule call(t::TreeToIndex, f, args...) = :(call($f, $(args...)))
Lerche.@inline_rule add(t::TreeToIndex, arg1, f, arg2) = :(call($(Literal(+)), $arg1, $arg2))
Lerche.@inline_rule subtract(t::TreeToIndex, arg1, f, arg2) = :(call($(Literal(-)), $arg1, $arg2))
Lerche.@inline_rule negate(t::TreeToIndex, f, arg) = :(call($(Literal(-)), $arg))
Lerche.@inline_rule multiply(t::TreeToIndex, arg1, f, arg2) = :(call($(Literal(*)), $arg1, $arg2))
Lerche.@inline_rule divide(t::TreeToIndex, arg1, f, arg2) = :(call($(Literal(/)), $arg1, $arg2))
Lerche.@inline_rule exponentiate(t::TreeToIndex, arg1, f, arg2) = :(call($(Literal(^)), $arg1, $arg2))

function preparse_index_notation(s)
	s′ = []
	pos = 1
    bindings = Dict()
	while (m = findnext("\$", s, pos)) !== nothing
        push!(s′, s[pos:first(m) - 1])
        pos = first(m) + 1
        (ex, pos′) = Meta.parse(s, pos, greedy=false)
        sym = gensym(:interpolate)
        bindings[sym] = esc(ex)
        push!(s′, "$(string(sym))")
        pos = pos′
	end
    if pos <= lastindex(s)
        push!(s′, s[pos:end])
    end
    s = join(s′, " ")
    s = replace(s, r"\n"=>" ")
    s = replace(s, r"∀|(\bfor\b)|(\bloop\b)"=>"##loop#")
    s = replace(s, r"(\bwhere\b)"=>"##where#")
    s = String(strip(s, [' ',]))
    (s, bindings)
end

function parse_index_notation(s)
    (s, bindings) = preparse_index_notation(s)
    t = Lerche.parse(index_notation_parser,s) 
    return Lerche.transform(TreeToIndex(bindings),t)
end

macro i_str(s)
    return parse_index_notation(s)
end