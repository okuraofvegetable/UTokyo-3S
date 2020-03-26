open Syntax
open Eval

let empty_env = []
let empty_tyenv = []
       
let rec read_eval_print env tyenv =
  print_string "# ";
  flush stdout;
  let cmd = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
  let (id, newenv, newtyenv, v) = eval_command env tyenv cmd in
  (Printf.printf "%s = " id;
   print_value v;
   print_newline ();
   read_eval_print newenv newtyenv)

let initial_env = empty_env

let initial_tyenv = empty_tyenv
    
let _ = read_eval_print initial_env initial_tyenv
