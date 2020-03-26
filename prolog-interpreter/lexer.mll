let digit = ['0'-'9']
let number = ['1'-'9'] (digit)*
let space = ' ' | '\t' | '\r' | '\n'
let lower_alpha = ['a'-'z']
let capital_alpha = ['A'-'Z'] 
let symb = lower_alpha (lower_alpha | capital_alpha | '_' | digit)* 
let varname = capital_alpha (lower_alpha | capital_alpha | '_' | digit)*

rule main = parse
| space+        { main lexbuf }
| "rule"        { Parser.RULE }
| "query"       { Parser.QUERY }
| ":-"          { Parser.IMPLY }
| "[]"          { Parser.NIL }
| "["           { Parser.LBRACKET }
| "]"           { Parser.RBRACKET }
| "|"           { Parser.BAR }
| "("           { Parser.LPAR }
| ")"           { Parser.RPAR }
| ","           { Parser.COMMA}
| "."           { Parser.DOT }
| ";"           { Parser.SEMI }
| "\+"          { Parser.NEG }
| symb  as id   { Parser.SYMBID id }
| number as num { Parser.NUMBER num }
| varname as vn { Parser.VARID vn }
| _             { failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}
