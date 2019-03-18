type token =
  | VAR of (string)
  | OPEN
  | CLOSE
  | EOF
  | DOT
  | SLASH
  | APPLICATION

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.expr
