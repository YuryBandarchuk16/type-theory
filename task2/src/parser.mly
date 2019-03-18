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
        | expr APPLICATION expr { Application($1, $3) }
        | SLASH VAR DOT expr { Abstraction($2, $4) }
