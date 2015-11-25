structure Tokens = Tokens
structure Interface = Interface
open Interface

type pos = Interface.pos
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val eof = fn () => Tokens.EOF(!line,!line)
fun makeInt (s : string) = s

%%
%header (functor FolLexFun(structure Tokens: Fol_TOKENS
			   structure Interface: INTERFACE) : LEXER);
alpha=[A-Za-z];
alphaCap=[A-Z];
alphaSmall=[a-z];
alphaNum=[A-Za-z0-9];
undersc=[_];
prime=['];
digit=[0-9];
nonZeroDigit=[1-9];
ws=[\t\ ]*;

%%
<INITIAL>{ws}	=> (lex());
<INITIAL>\n	=> (next_line(); lex());
<INITIAL>":-"	=> (Tokens.IF(!line,!line));
<INITIAL>","	=> (Tokens.COMMA(!line,!line));
<INITIAL>"."    => (Tokens.DOT(!line,!line));
<INITIAL>"("	=> (Tokens.LPAREN(!line,!line));
<INITIAL>")"	=> (Tokens.RPAREN(!line,!line));
<INITIAL>{alphaSmall}{alphaNum}*{undersc}{alphaNum}+{prime}*    => (Tokens.NAME (yytext,!line,!line));
<INITIAL>{alphaSmall}({alphaNum}*{undersc}{alphaNum}+)+{prime}* => (Tokens.NAME (yytext,!line,!line));
<INITIAL>{alphaSmall}{alphaNum}*{prime}*		        => (Tokens.NAME (yytext,!line,!line));
<INITIAL>{alphaCap}{alphaNum}*{undersc}{alphaNum}+{prime}*    => (Tokens.VARIABLE (yytext,!line,!line));
<INITIAL>{alphaCap}({alphaNum}*{undersc}{alphaNum}+)+{prime}* => (Tokens.VARIABLE (yytext,!line,!line));
<INITIAL>{alphaCap}{alphaNum}*{prime}* 		              => (Tokens.VARIABLE (yytext,!line,!line));
<INITIAL>.	=> (error ("ignoring illegal character" ^ yytext,
			   !line,!line); lex());
