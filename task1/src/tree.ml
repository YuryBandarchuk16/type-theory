type expr =
	| Var of string
	| Appl of expr * expr
	| Abst of string * expr;;
