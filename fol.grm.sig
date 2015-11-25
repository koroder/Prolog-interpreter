signature Fol_TOKENS =
sig
type ('a,'b) token
type svalue
val PARSEQUERY:  'a * 'a -> (svalue,'a) token
val PARSEPROG:  'a * 'a -> (svalue,'a) token
val IF:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
val DOT:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val VARIABLE: (string) *  'a * 'a -> (svalue,'a) token
val NAME: (string) *  'a * 'a -> (svalue,'a) token
end
signature Fol_LRVALS=
sig
structure Tokens : Fol_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
