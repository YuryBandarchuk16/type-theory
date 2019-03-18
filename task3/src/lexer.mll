{
open Parser
}

let variable = ['a' - 'z']+ ['a' - 'z' '0' - '9' '\'']*
let w = [' ' '\t' '\n' '\r']

rule main = parse
        | variable as v     { VAR(v) }
        | w+                { APPLICATION }
        | w*'.'w*           { DOT }
        | "\\"w*            { SLASH }
        | "("w*             { OPEN }
        | w*")"             { CLOSE }
        | eof               { EOF }
