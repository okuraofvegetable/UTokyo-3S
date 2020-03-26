open Syntax
open Eval

let rec print_sigma table sigma =
  match table with
  | [] -> ()
  | (num,id)::rest -> (if List.mem_assoc num sigma then (Printf.printf "%s = " id;print_term (List.assoc num sigma);print_string "\n"));
                      print_sigma rest sigma

let print_result result sigma table =
  if result = false 
    then print_string "\x1b[1;31mfalse.\x1b[0;39m\n"
  else if table = [] 
    then print_string "true.\n"
  else  print_sigma table sigma

let rec read_eval_print oldrules oldqueue oldtable in_progress =
  (if (in_progress = false) then (print_string "?- "));
  flush stdout;
  try(
    let cmd = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
    let (result,sigma,rules,queue,table,progress,no_result) = eval_command cmd oldrules oldqueue oldtable in
    (
     (if no_result = false 
      then print_result result sigma table
      else ());
     read_eval_print rules queue table progress)
  )
  with | UndefinedProcedure -> 
            (print_string "\x1b[31mUndefined procedure.\x1b[39m\n";
             read_eval_print oldrules oldqueue oldtable in_progress)
       | Parsing.Parse_error -> 
            (print_string "\x1b[31mParse Error.\x1b[39m\n";
             read_eval_print oldrules oldqueue oldtable in_progress)
       | Failure msg -> 
            (print_string ("\x1b[31mFailure "^msg^"\x1b[39m\n");
             read_eval_print oldrules oldqueue oldtable in_progress)
    
let _ = read_eval_print [] [] [] false
