{
open Parser
}

rule read = parse
  | [' ' '\t' '\n'] { read lexbuf }
  | ['0'-'9']+ as n { INT (int_of_string n) }
  | eof { EOF }
  | _ { failwith "unexpected character" }