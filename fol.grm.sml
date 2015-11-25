
functor FolLrValsFun (structure Token : TOKEN
			       structure Absyn : ABSYN ) : Fol_LRVALS = 
struct
structure ParserData=
struct
structure Header = 
struct
open Absyn


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\011\000\000\000\
\\001\000\001\000\024\000\002\000\023\000\000\000\
\\001\000\004\000\027\000\000\000\
\\001\000\005\000\040\000\008\000\042\000\000\000\
\\001\000\005\000\014\000\000\000\
\\001\000\005\000\015\000\000\000\
\\001\000\006\000\000\000\000\000\
\\001\000\008\000\013\000\000\000\
\\001\000\009\000\004\000\010\000\003\000\000\000\
\\032\000\001\000\011\000\000\000\
\\033\000\000\000\
\\034\000\001\000\011\000\000\000\
\\035\000\000\000\
\\036\000\001\000\011\000\000\000\
\\037\000\000\000\
\\038\000\000\000\
\\039\000\000\000\
\\041\000\000\000\
\\043\000\007\000\025\000\000\000\
\\044\000\000\000\
\\045\000\003\000\018\000\000\000\
\\046\000\000\000\
\\047\000\000\000\
\\048\000\007\000\026\000\000\000\
\\049\000\000\000\
\\050\000\003\000\018\000\000\000\
\\051\000\000\000\
\\052\000\000\000\
\"
val actionRowNumbers =
"\008\000\011\000\009\000\007\000\
\\003\000\004\000\005\000\013\000\
\\012\000\020\000\010\000\000\000\
\\016\000\015\000\014\000\021\000\
\\001\000\017\000\018\000\023\000\
\\002\000\026\000\025\000\000\000\
\\001\000\022\000\027\000\019\000\
\\024\000\006\000"
val gotoT =
"\
\\001\000\029\000\000\000\
\\002\000\008\000\003\000\007\000\004\000\006\000\005\000\005\000\
\\006\000\004\000\010\000\003\000\000\000\
\\002\000\010\000\003\000\007\000\004\000\006\000\005\000\005\000\
\\006\000\004\000\010\000\003\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\014\000\003\000\007\000\004\000\006\000\005\000\005\000\
\\006\000\004\000\010\000\003\000\000\000\
\\000\000\
\\007\000\015\000\000\000\
\\000\000\
\\006\000\018\000\011\000\017\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\020\000\009\000\019\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\026\000\000\000\
\\006\000\018\000\011\000\027\000\000\000\
\\008\000\028\000\009\000\019\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 30
val numrules = 21
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | VARIABLE of  (string)
 | NAME of  (string) | BODY of  (tree) | HEAD of  (tree)
 | TERM of  (tree) | NTERM of  (tree) | TUPLE of  (tree)
 | LITERAL of  (tree) | RULE of  (tree) | FACT of  (tree)
 | STATEMENT of  (tree) | PROGRAM of  (tree) | BEGIN of  (tree)
end
type svalue = MlyValue.svalue
type result = tree
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn _ => false
val showTerminal =
fn (T 0) => "NAME"
  | (T 1) => "VARIABLE"
  | (T 2) => "LPAREN"
  | (T 3) => "RPAREN"
  | (T 4) => "DOT"
  | (T 5) => "EOF"
  | (T 6) => "COMMA"
  | (T 7) => "IF"
  | (T 8) => "PARSEPROG"
  | (T 9) => "PARSEQUERY"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 
2)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( _, PARSEPROG1left, PARSEPROG1right)) :: rest671)) =>
 let val  result = MlyValue.BEGIN (Null)
 in ( LrTable.NT 0, ( result, PARSEPROG1left, PARSEPROG1right), 
rest671)
end
|  ( 1, ( ( _, ( MlyValue.PROGRAM PROGRAM, _, PROGRAM1right)) :: ( _, 
( _, PARSEPROG1left, _)) :: rest671)) => let val  result = 
MlyValue.BEGIN (Node("BEGIN",[PROGRAM]))
 in ( LrTable.NT 0, ( result, PARSEPROG1left, PROGRAM1right), rest671)

end
|  ( 2, ( ( _, ( _, PARSEQUERY1left, PARSEQUERY1right)) :: rest671))
 => let val  result = MlyValue.BEGIN (Null)
 in ( LrTable.NT 0, ( result, PARSEQUERY1left, PARSEQUERY1right), 
rest671)
end
|  ( 3, ( ( _, ( MlyValue.PROGRAM PROGRAM, _, PROGRAM1right)) :: ( _, 
( _, PARSEQUERY1left, _)) :: rest671)) => let val  result = 
MlyValue.BEGIN (Node("BEGIN",[PROGRAM]))
 in ( LrTable.NT 0, ( result, PARSEQUERY1left, PROGRAM1right), rest671
)
end
|  ( 4, ( ( _, ( MlyValue.STATEMENT STATEMENT, STATEMENT1left, 
STATEMENT1right)) :: rest671)) => let val  result = MlyValue.PROGRAM (
Node("PROGRAM",[STATEMENT]))
 in ( LrTable.NT 1, ( result, STATEMENT1left, STATEMENT1right), 
rest671)
end
|  ( 5, ( ( _, ( MlyValue.PROGRAM PROGRAM, _, PROGRAM1right)) :: ( _, 
( MlyValue.STATEMENT STATEMENT, STATEMENT1left, _)) :: rest671)) =>
 let val  result = MlyValue.PROGRAM (
Node("PROGRAM",[STATEMENT,PROGRAM]))
 in ( LrTable.NT 1, ( result, STATEMENT1left, PROGRAM1right), rest671)

end
|  ( 6, ( ( _, ( _, _, DOT1right)) :: ( _, ( MlyValue.FACT FACT, 
FACT1left, _)) :: rest671)) => let val  result = MlyValue.STATEMENT (
Node("STATEMENT",[FACT]))
 in ( LrTable.NT 2, ( result, FACT1left, DOT1right), rest671)
end
|  ( 7, ( ( _, ( _, _, DOT1right)) :: ( _, ( MlyValue.RULE RULE, 
RULE1left, _)) :: rest671)) => let val  result = MlyValue.STATEMENT (
Node("STATEMENT",[RULE]))
 in ( LrTable.NT 2, ( result, RULE1left, DOT1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.LITERAL LITERAL, LITERAL1left, LITERAL1right
)) :: rest671)) => let val  result = MlyValue.FACT (
Node("FACT",[LITERAL]))
 in ( LrTable.NT 3, ( result, LITERAL1left, LITERAL1right), rest671)

end
|  ( 9, ( ( _, ( MlyValue.BODY BODY, _, BODY1right)) :: _ :: ( _, ( 
MlyValue.HEAD HEAD, HEAD1left, _)) :: rest671)) => let val  result = 
MlyValue.RULE (Node("RULE",[HEAD,BODY]))
 in ( LrTable.NT 4, ( result, HEAD1left, BODY1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.LITERAL LITERAL, LITERAL1left, 
LITERAL1right)) :: rest671)) => let val  result = MlyValue.HEAD (
Node("HEAD",[LITERAL]))
 in ( LrTable.NT 9, ( result, LITERAL1left, LITERAL1right), rest671)

end
|  ( 11, ( ( _, ( MlyValue.LITERAL LITERAL, LITERAL1left, 
LITERAL1right)) :: rest671)) => let val  result = MlyValue.BODY (
Node("BODY",[LITERAL]))
 in ( LrTable.NT 10, ( result, LITERAL1left, LITERAL1right), rest671)

end
|  ( 12, ( ( _, ( MlyValue.BODY BODY, _, BODY1right)) :: _ :: ( _, ( 
MlyValue.LITERAL LITERAL, LITERAL1left, _)) :: rest671)) => let val  
result = MlyValue.BODY (Node("BODY",[LITERAL,BODY]))
 in ( LrTable.NT 10, ( result, LITERAL1left, BODY1right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.NAME NAME, NAME1left, NAME1right)) :: 
rest671)) => let val  result = MlyValue.LITERAL (
Node("LITERAL",[Node("NAME",[Leaf(NAME)])]))
 in ( LrTable.NT 5, ( result, NAME1left, NAME1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.TUPLE TUPLE, _, TUPLE1right)) :: ( _, ( 
MlyValue.NAME NAME, NAME1left, _)) :: rest671)) => let val  result = 
MlyValue.LITERAL (Node("LITERAL",[Node("NAME",[Leaf(NAME)]),TUPLE]))
 in ( LrTable.NT 5, ( result, NAME1left, TUPLE1right), rest671)
end
|  ( 15, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.NTERM NTERM,
 _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.TUPLE (Node("TUPLE",[NTERM]))
 in ( LrTable.NT 6, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.TERM TERM, TERM1left, TERM1right)) :: 
rest671)) => let val  result = MlyValue.NTERM (Node("NTERM",[TERM]))
 in ( LrTable.NT 7, ( result, TERM1left, TERM1right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.NTERM NTERM, _, NTERM1right)) :: _ :: ( _, 
( MlyValue.TERM TERM, TERM1left, _)) :: rest671)) => let val  result =
 MlyValue.NTERM (Node("NTERM",[TERM,NTERM]))
 in ( LrTable.NT 7, ( result, TERM1left, NTERM1right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.NAME NAME, NAME1left, NAME1right)) :: 
rest671)) => let val  result = MlyValue.TERM (
Node("TERM",[Node("NAME",[Leaf(NAME)])]))
 in ( LrTable.NT 8, ( result, NAME1left, NAME1right), rest671)
end
|  ( 19, ( ( _, ( MlyValue.VARIABLE VARIABLE, VARIABLE1left, 
VARIABLE1right)) :: rest671)) => let val  result = MlyValue.TERM (
Node("TERM",[Node("VARIABLE",[Leaf(VARIABLE)])]))
 in ( LrTable.NT 8, ( result, VARIABLE1left, VARIABLE1right), rest671)

end
|  ( 20, ( ( _, ( MlyValue.TUPLE TUPLE, _, TUPLE1right)) :: ( _, ( 
MlyValue.NAME NAME, NAME1left, _)) :: rest671)) => let val  result = 
MlyValue.TERM (Node("TERM",[Node("NAME",[Leaf(NAME)]),TUPLE]))
 in ( LrTable.NT 8, ( result, NAME1left, TUPLE1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.BEGIN x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : Fol_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun NAME (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.NAME i,p1,p2))
fun VARIABLE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VARIABLE i,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun DOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun PARSEPROG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun PARSEQUERY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
end
end
