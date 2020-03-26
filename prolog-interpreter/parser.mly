%{
  open Syntax
  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)
%}

%token <string> SYMBID 
%token <string> VARID 
%token <string> NUMBER
%token IMPLY COMMA
%token RULE QUERY
%token LPAR RPAR 
%token DOT SEMI
%token LBRACKET RBRACKET BAR NIL
%token NEG

%start toplevel 
%type <Syntax.command> toplevel
%% 

toplevel:
  | RULE rule { CRule ($2) }
  | RULE fact { CRule ($2) }
  | QUERY query { CQuery ($2) }
  | DOT { CExit }
  | SEMI { CCont }
;

query:
  | predicates { $1 }

fact:
  | predicate DOT { ($1,[]) }
;

rule:
  | predicate IMPLY predicates DOT { ($1,$3) }
;

predicates:
  | predicate { [$1] }
  | predicate COMMA predicates { $1::$3 }
;

predicate:
  | SYMBID LPAR terms RPAR { EPdSymb($1,$3) }
  | SYMBID { EPdSymb($1,[]) }
;

terms:
  | term { [$1] }
  | term COMMA terms { $1::$3 }
;

term:
  | atomic { $1 }
  | SYMBID LPAR symbs RPAR { EFnSymb($1,$3) }
;
 
symbs:
  | atomic { [$1] }
  | atomic COMMA symbs { $1::$3 } 
;

atomic:
  | SYMBID { EConst($1) }
  | NUMBER { EConst($1) }
  | VARID  { EVar($1) }
  | list   { $1 }
;

atomics:
  | list_last { $1 }
  | atomic COMMA atomics { ECons($1,$3) } 
;

list_last:
  | atomic { ECons($1,ENil) }
  | atomic BAR atomic { ECons($1,$3) }
;

list:
  | NIL { ENil }
  | LBRACKET atomics RBRACKET { $2 }
;

