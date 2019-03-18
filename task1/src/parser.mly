%{
  open Tree;;
%}
%token <string> VAR
%token OPEN CLOSE
%token EOF
%token DOT
%token SLASH
%token APPLICATION
%left  APPLICATION
%start main
%type <Tree.expr> main
%%
main:
        expr EOF           { $1 }
expr:
        | VAR { Var($1) }
        | OPEN expr CLOSE { $2 }
        | expr APPLICATION expr { Appl($1, $3) }
        | SLASH VAR DOT expr { Abst($2, $4) }
