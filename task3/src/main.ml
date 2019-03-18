open Tree;;
open Buffer;;
open Printf;;

module Ht = Hashtbl;;
module M = Map.Make(String);;
module S = Set.Make(String);;

type e_type = Type of string | Impl of e_type * e_type;;
type either_e = Just of e_type | Nothing;;
type algebraic_term_application = AT of e_type * e_type;;

let (>>) x f = f x;;

let string_of_tree tree =
  let buf = create (2048 * 1024) in
  let rec helper t = match t with
  | Var(v) -> add_string buf v; ()
  | Application(left, right) -> add_char buf '('; helper left; add_char buf ' '; helper right; add_char buf ')'; ()
  | Abstraction(v, rest) -> add_string buf ("(\\" ^ v ^ "."); helper rest; add_char buf ')'; ()
  in helper tree;
  contents buf;;

let ic = stdin;;
let oc = stdout;;

let read_all_input () = begin
  let lines = ref [] in
  let match1 = (Str.regexp "(") in
  let replace1 = " ( " in
  let match2 = (Str.regexp ")") in
  let replace2 = " ) " in
  let match3 = (Str.regexp "\\\\") in
  let replace3 = " \\\\" in
  let helper () =
    try
      while true; do
        let line = (ic >> input_line) in
        let line1 = Str.global_replace match1 replace1 line in
        let line2 = Str.global_replace match2 replace2 line1 in
        let line3 = Str.global_replace match3 replace3 line2 in
        let line4 = String.trim line3 in
        lines := line4 :: !lines
        done; List.rev !lines
      with End_of_file -> List.rev !lines in
  let buf = create 2048 in
  let rec concatenate items = match items with
  | x::xs -> add_string buf x; add_string buf "\n"; concatenate xs
  | [] -> contents buf in
  concatenate (helper());
end;;

let all_input = String.trim (read_all_input());;
let inputExpression = all_input >> Lexing.from_string >> Parser.main Lexer.main;;

let rec extractFreeVariables expression setOfVariables = begin
  match expression with 
  | Var v -> (S.add v setOfVariables)
  | Application(p, q) -> begin
    let freeVariablesInPAndBefore = extractFreeVariables p setOfVariables in
    let freeVariablesInPAndQAndBefore = extractFreeVariables q freeVariablesInPAndBefore in
    freeVariablesInPAndQAndBefore
  end
  | Abstraction(varName, restOfExpression) -> begin
    let allFreeVariables = extractFreeVariables restOfExpression setOfVariables in
    (S.remove varName allFreeVariables)
  end
end;;

let allTypes = Ht.create 1024;;
let defaultContext = Ht.create 1024;;
let takenTypeNamesGeneral = Ht.create 1024;;
let takenTypeNamesForExpressions = Ht.create 1024;;

let getFreeTypeNameForExpression storage expression = begin
  let newTypeIndex = Ht.length allTypes in
  let x = try Ht.find storage expression with _ -> begin
    let newType = Type("t" ^ (string_of_int newTypeIndex)) in
    Ht.add storage expression newType;
    Ht.add allTypes newType 1;
    newType
  end in x
end;;

let getOrNotCreateTypeNameForExpression storage expression = begin
  let newTypeIndex = Ht.length allTypes in
  let x = try Ht.find storage expression with _ -> begin
    let newType = Type("t" ^ (string_of_int newTypeIndex)) in
    Ht.add allTypes newType 1;
    newType
  end in x
end;;

let getAndRecreateTypeNameForExpression storage expression = begin
  let newStorage = Ht.copy storage in
  (newStorage, getFreeTypeNameForExpression newStorage expression)
end

let getFreeTypeNameForGeneralPurpose() = begin
  let newTypeIndex = Ht.length allTypes in
  let newTypeName = Type("t" ^ (string_of_int newTypeIndex)) in
  Ht.add takenTypeNamesGeneral newTypeName 1;
  Ht.add allTypes newTypeName 1;
  newTypeName
end

let mergeContexts a b = begin
  Ht.iter (fun k v -> Ht.add a k v) b;
  a
end;;

let rec string_of_type t = begin
  match t with 
  | Type name -> name
  | Impl (a, b) -> "(" ^ (string_of_type a) ^ "->" ^ (string_of_type b) ^ ")"
end;;

let buildDefaultContext v = begin
    let typeName = getFreeTypeNameForExpression takenTypeNamesForExpressions (Var v) in
    Ht.add defaultContext (Var v) typeName;
end;;

S.iter buildDefaultContext (extractFreeVariables inputExpression S.empty);;

let rec mergeTwoLists a b = begin
  match a with
  | [] -> b
  | x::xs -> x::(mergeTwoLists xs b)
end;;

let rec getEquationsAndType expression currentContext = begin
  match expression with
  | Var v -> ([], [getFreeTypeNameForExpression currentContext expression])
  | Application(p, q) -> begin
    let currentType = getFreeTypeNameForExpression currentContext expression in
    let (contextInP, typeOfP) = getAndRecreateTypeNameForExpression currentContext p in
    let (contextInQ, typeOfQ) = getAndRecreateTypeNameForExpression currentContext q in
    let (equationsInP, typesInP) = getEquationsAndType p contextInP in
    let (equationsInQ, typesInQ) = getEquationsAndType q contextInQ in
    let totalEquations = mergeTwoLists equationsInP equationsInQ in
    let totalTypes = mergeTwoLists typesInP typesInQ in
    let newEquation = AT(typeOfP, Impl(typeOfQ, currentType)) in
    (newEquation::totalEquations, currentType::totalTypes)
  end
  | Abstraction(varName, restOfExpression) -> begin
    let currentType = getFreeTypeNameForExpression currentContext expression in
    let (contextInRest, typeOfVar)  = getAndRecreateTypeNameForExpression currentContext (Var varName) in
    let typeOfRest = getFreeTypeNameForExpression contextInRest restOfExpression in
    let (equations, types) = getEquationsAndType restOfExpression contextInRest in
    let newEquation = AT(currentType, Impl(typeOfVar, typeOfRest)) in
    (newEquation::equations, (currentType::(typeOfVar::types)))
  end
end;;

let reduceEquations typeNameBefore newType equations = begin
  let rec simplifyOne currentType = begin
    match currentType with
    | Impl(a, b) -> begin
      let newA = simplifyOne a in
      let newB = simplifyOne b in
      Impl(newA, newB)
    end
    | Type(typeName) -> begin
      if (typeName = typeNameBefore) then newType else Type(typeName)
    end
  end in
  let rec simplifyMany equations = begin
    match equations with 
    | [] -> []
    | x::xs -> begin
      match x with 
      | AT(from, too) -> begin
        let newAT = AT((simplifyOne from), (simplifyOne too)) in
        let rest = (simplifyMany xs) in
        newAT::rest
      end
    end
  end in simplifyMany equations
end;;

let rec needsReplacement target equation = begin
  match equation with
  | Type typeName -> begin
    if (typeName = target) then true else false
  end
  | Impl (from, too) -> begin
    if (needsReplacement target from) then true 
    else needsReplacement target too
  end
end;;

let clearEquations ll = begin
  let rec helper l = begin
    match l with
    | [] -> []
    | x::[] -> [x]
    | x::xs -> begin
      let rest = helper xs in
      match rest with
      | [] -> [x]
      | y::ys -> begin
        if (x <> y) then x::rest else rest
      end
    end
  end in
  helper (List.sort compare ll)
end;;

let rec simplify equations result = begin
  match equations with
  | [] -> result
  | x::tail -> begin
    let defaultPredicate = ((<>) x) in
    let withoutX = (List.filter defaultPredicate result) in
    match x with 
    | AT(Type t1, Type t2) when (t1 = t2) -> begin
      simplify tail withoutX
    end
    | AT(Type typeName, rest) -> begin
      if (needsReplacement typeName rest) then begin
        match rest with
        | Type otherTypeName -> begin
          simplify tail result
        end
        | Impl(a, b) -> begin 
          print_endline "Expression has no type";
          exit 0; []
        end
      end else begin
        let simplified = reduceEquations typeName (rest) withoutX in
        let cleared = clearEquations (x::simplified) in  
        clearEquations (simplify (reduceEquations typeName rest tail) cleared)
      end
    end
    | AT(rest, Type typeName) -> begin
      if (needsReplacement typeName rest) then begin
        print_endline "Expression has no type";
        exit 0; []
      end else begin
        let simplified = reduceEquations typeName rest withoutX in
        let cleared = clearEquations (AT(Type typeName, rest)::simplified) in
        clearEquations (simplify (reduceEquations typeName rest tail) cleared)
      end
    end
    | AT(Impl (s1, s2), Impl(t1, t2)) -> begin
      clearEquations (simplify tail (AT(s1, t1)::(AT(s2, t2)::withoutX)))
    end
  end
end;;

let rec makeUnification equations = begin
  let newEquations = simplify equations equations in
  if ((List.length newEquations) = (List.length equations)) then simplify (simplify newEquations newEquations) (simplify newEquations newEquations)
  else makeUnification newEquations
end;;

let rec buildTypeSubstitution unifiedEquations = begin
  match unifiedEquations with
  | [] -> Ht.create 1024
  | x::xs -> begin
    let substitution = buildTypeSubstitution xs in
    match x with
    | AT(from, actualType) -> begin
      match from with
      | Impl(a, b) -> begin
        print_endline "Expression has no type";
        exit 0; substitution
      end
      | Type typeName -> begin
        Ht.add substitution from actualType;
        substitution
      end
    end
  end
end;;

let (equations, types) = getEquationsAndType inputExpression (Ht.copy defaultContext);;
let substitution = buildTypeSubstitution (makeUnification equations);;

let getType varName = begin
  let resultType = try begin
    let initialType = Ht.find defaultContext varName in
    let afterSubstitution = try Ht.find substitution initialType with _ -> initialType in
    afterSubstitution
  end with _ -> begin
    let name = match varName with
    | Var v -> v
    | _ -> "" in
    let afterSubstitution = try Ht.find substitution (Type name) with _ -> begin
      print_endline "Expression has no type";
      exit 0; (Type name)
    end in
    afterSubstitution
  end in
  resultType
end;;

let string_of_typed_expression expression = begin
  ((string_of_tree expression) ^ " : " ^ (string_of_type (getType expression)))
end;;

let string_of_context context = begin
  let buf = create (2 * 1024) in
  let flag = Ht.create 1 in
  List.iter (fun typedExpression -> begin
    if (Ht.length flag = 0) then begin
      Ht.add flag 1 1;
    end else begin
      add_string buf ", ";
      if (Ht.length flag = 0) then begin
        Ht.add flag 2 2;
      end else begin () end;
    end;
    add_string buf (string_of_typed_expression typedExpression);
  end) context;
  if (Ht.length flag = 1) then begin (add_char buf ' '); end else begin () end;
  contents buf;
end;;

let defaultContextVars = Ht.fold (fun k v acc ->  k::acc) defaultContext [];;

let rec buildProof expression defaultContextVars zvs types = begin
 match types with
 | [] -> ([], [])
 | currentType::xs -> begin
    Ht.add defaultContext expression currentType;
    let contextDescription = (string_of_context defaultContextVars) in
    let expressionDescription = (string_of_tree expression) in
    let expressionTypeDescription = (string_of_type (getType expression))  in
    let prefix = 
      (zvs ^ contextDescription ^ "|- " ^ expressionDescription ^ " : " ^ expressionTypeDescription) in
    match expression with
    | Var varName -> begin
      Ht.remove defaultContext expression;
      ([prefix ^ " [rule #1]"], xs)
    end
    | Application(p, q) -> begin
      let currentProof = (prefix ^ " [rule #2]") in
      let (proofOfP, typesInQ) = buildProof p defaultContextVars (zvs ^ "*   ") xs in
      let (proofOfQ, typesInRest) = buildProof q defaultContextVars (zvs ^ "*   ") typesInQ in
      let totalProofs = mergeTwoLists proofOfP proofOfQ in
      (currentProof::totalProofs, typesInRest)
    end
    | Abstraction(varName, restOfExpression) -> begin
      let currentProof = (prefix ^ " [rule #3]") in
      let currentAbstractionVar = (Var varName) in
      let (currentVarType, newXS) = match xs with
      | [] -> begin
        print_endline "Expression has no type";
        exit 0; ((Type varName), [])
      end
      | y::ys -> begin
        (y, ys)
      end in
      Ht.add defaultContext currentAbstractionVar currentVarType;
      let (proofOfRest, typesInRest) = buildProof restOfExpression (currentAbstractionVar::defaultContextVars) (zvs ^ "*   ") newXS in
      Ht.remove defaultContext expression;
      (currentProof::proofOfRest, typesInRest)
    end
 end
end;;

let (proofLines, _) = (buildProof inputExpression defaultContextVars "" types);;

List.iter (fun proofLine -> begin
  print_endline proofLine;
end) proofLines;;
