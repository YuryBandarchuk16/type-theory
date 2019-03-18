type expr =
	| Var of string
	| Application of expr * expr
	| Abstraction of string * expr;;
