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

struct TreeToConcrete <: Lerche.Transformer
    bindings
end

Lerche.@inline_rule where(t::TreeToConcrete, cons, prod) = :(Where($cons, $prod))
Lerche.@rule loop(t::TreeToConcrete, args) = :(Loop($(args[1:end-1]...), $(args[end])))
Lerche.@terminal PLUS(t::TreeToConcrete, _) = Literal(+)
Lerche.@terminal MINUS(t::TreeToConcrete, _) = Literal(-)
Lerche.@terminal TIMES(t::TreeToConcrete, _) = Literal(*)
Lerche.@terminal SLASH(t::TreeToConcrete, _) = Literal(/)
Lerche.@terminal CARET(t::TreeToConcrete, _) = Literal(^)
Lerche.@terminal NAME(t::TreeToConcrete, name) = Name(Symbol(strip(String(name), [' ',])))
Lerche.@terminal INTERPOLATE(t::TreeToConcrete, name) = t.bindings[Symbol(strip(String(name), [' ',]))]
Lerche.@terminal LITERAL(t::TreeToConcrete, num) = Literal(parse(Int, strip(String(num), [' ',])))
Lerche.@inline_rule slot(t::TreeToConcrete, name) = esc(:(~$(name.name)))
Lerche.@inline_rule segment(t::TreeToConcrete, name) = esc(:(~~$(name.name)))
Lerche.@inline_rule splat(t::TreeToConcrete, arg) = :($arg...)
Lerche.@rule assign(t::TreeToConcrete, lhs_op_rhs) = :(Assign($(lhs_op_rhs...)))
Lerche.@inline_rule access(t::TreeToConcrete, tns, idxs...) = :(Access($tns, $(idxs...)))
Lerche.@inline_rule call(t::TreeToConcrete, f, args...) = :(Call($f, $(args...)))
Lerche.@inline_rule add(t::TreeToConcrete, arg1, f, arg2) = :(Call($(Literal(+)), $arg1, $arg2))
Lerche.@inline_rule subtract(t::TreeToConcrete, arg1, f, arg2) = :(Call($(Literal(-)), $arg1, $arg2))
Lerche.@inline_rule negate(t::TreeToConcrete, f, arg) = :(Call($(Literal(-)), $arg))
Lerche.@inline_rule multiply(t::TreeToConcrete, arg1, f, arg2) = :(Call($(Literal(*)), $arg1, $arg2))
Lerche.@inline_rule divide(t::TreeToConcrete, arg1, f, arg2) = :(Call($(Literal(/)), $arg1, $arg2))
Lerche.@inline_rule exponentiate(t::TreeToConcrete, arg1, f, arg2) = :(Call($(Literal(^)), $arg1, $arg2))

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
    return Lerche.transform(TreeToConcrete(bindings),t)
end

macro i_str(s)
    return parse_index_notation(s)
end

macro capture(ex, lhs)
    keys = Symbol[]
    lhs_term = SymbolicUtils.makepattern(lhs, keys)
    unique!(keys)
    bind = Expr(:block, map(key-> :($(esc(key)) = getindex(__MATCHES__, $(QuoteNode(key)))), keys)...)
    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        __MATCHES__ = SymbolicUtils.Rule($(QuoteNode(lhs)),
             lhs_pattern,
             SymbolicUtils.matcher(lhs_pattern),
             identity,
             SymbolicUtils.rule_depth($lhs_term))($(esc(ex)))
        if __MATCHES__ !== nothing
            $bind
            true
        else
            false
        end
    end
end