%{
open Ast
%}

%token <int> INT
%token UNIT
%token EOF

%start <Ast.expr> main

%%

main:
  | e = expr EOF { e }

expr:
  | i = INT { Int i }
  | u = UNIT
  // | a = expr PLUS b = expr { Add (a, b) }