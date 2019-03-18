open Tree;;
open Buffer;;
open Printf;;

module M = Map.Make(String);;

type either = Just of expr | Nothing of expr;;

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

let buildDBIndex expression = begin
  let getCurrentIndex variableName visitedMap currentDepth = begin
    let index = M.find variableName visitedMap in
    let currentIndex = currentDepth - index - 1 in
    string_of_int currentIndex 
  end in
  let rec build expression visitedMap depth = begin
    match expression with
    | Var v -> begin
      if (M.mem v visitedMap) then begin
        let newName = getCurrentIndex v visitedMap depth in
        Var newName
      end else Var v
    end
    | Application(p, q) -> begin
      let newP = build p visitedMap depth in
      let newQ = build q visitedMap depth in
      Application (newP, newQ)
    end
    | Abstraction (varName, restOfExpression) -> begin
      let indexedExpression = build restOfExpression (M.add varName depth visitedMap) (depth + 1) in
      Abstraction (varName, indexedExpression)
    end
  end in
  build expression M.empty 0
end;;

 
let explode s = begin
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []
end;;

let is_integer s = begin
  let rec validator chars = begin
    match chars with 
    | c::cs -> begin
      let code = Char.code c in
      if (code >= 48 + 0 && code <= 48 + 9) then validator cs
      else false
    end
    | [] -> true
  end in validator (explode s)
end;;

let rec updateIndices expression targetDepth depth = begin
  match expression with 
  | Application(p, q) -> begin
    let newP = updateIndices p targetDepth depth in
    let newQ = updateIndices q targetDepth depth in
    Application(newP, newQ)
  end
  | Abstraction(varName, restOfExpression) -> begin
    let newExpression = updateIndices restOfExpression targetDepth (depth + 1) in
    Abstraction(varName, newExpression)
  end
  | Var v -> begin
    if (is_integer v) then begin
      let currentDepth = int_of_string v in
      if (depth - 1 >= currentDepth) then expression 
      else begin
        Var(string_of_int (targetDepth + currentDepth))
      end
    end else expression
  end
end;;

let rec confirmReduction p q = begin
  let rec visitor expression depth = begin
    match expression with
    | Var v -> begin
      if (v = (string_of_int depth)) then begin
        updateIndices q depth 0
      end else begin
        if (is_integer v) then begin
          let intValue = int_of_string v in
          if (intValue > depth) then Var(string_of_int(intValue - 1)) else expression
        end else expression
      end
    end
    | Application(pp, qq) -> Application(visitor pp depth, visitor qq depth)
    | Abstraction(varName, restOfExpression) -> Abstraction(varName, visitor restOfExpression (depth + 1))
  end in
  match p with 
  | Abstraction(varName, restOfExpression) -> begin
    (*print_endline "Hi!";
    print_endline (string_of_tree restOfExpression);*)
    Just(visitor restOfExpression 0)
  end
  | _ -> Just(Application(p, q))
end;;

let rec findBetaRedex expression = begin
  match expression with 
  | Var v -> Nothing(expression)
  | Abstraction (varName, restOfExpression) -> begin
    let maybeBetaRedex = findBetaRedex restOfExpression in
      match maybeBetaRedex with
      | Just e -> Just(Abstraction(varName, e))
      | Nothing e -> Nothing(Abstraction(varName, e))
  end
  | Application (p, q) -> begin
    match p with
    | Abstraction (varName, restOfExpression) -> confirmReduction p q
    | _ -> begin
      let maybeBetaRedex = findBetaRedex p in
        match maybeBetaRedex with
        | Just e -> Just(Application(e, q))
        | Nothing e -> begin
          let anotherMaybeBetaRedex = findBetaRedex q in
            match anotherMaybeBetaRedex with
            | Just e -> Just(Application(p, e))
            | Nothing e -> Nothing(Application(p, e))
        end
    end
  end
end;;

let makeCanonicalForm expression = begin
  let rec visitor expression storage depth = begin
    match expression with 
    | Var v -> begin
      (*print_endline "Weclome!";
      print_endline v;*)
      if (is_integer v) then begin
        (*print_endline "it's int";*)
        let actualId = depth - (int_of_string v) - 1 in
        let actualVarName = M.find (string_of_int actualId) storage in
        (*print_endline "Hi!";
        print_endline "Number id";
        print_endline v;
        print_endline "New name: ";
        print_endline actualVarName;*)
        Var actualVarName
      end else expression
    end
    | Application(p, q) -> begin
      let newP = visitor p storage depth in
      let newQ = visitor q storage depth in
      Application(newP, newQ)
    end
    | Abstraction(varName, restOfExpression) -> begin
      let indexedExpression = visitor restOfExpression (M.add (string_of_int depth) varName storage) (depth + 1) in
      Abstraction (varName, indexedExpression)
    end
  end in visitor expression M.empty 0
end;;

let unifyVariable varName storage = begin
  if (M.mem varName storage) then begin
    let times = M.find varName storage in
    ((varName ^ (String.make (times + 1) '\'')), (M.add varName (times + 1) storage))
  end else 
    (*(M.add varName 0 storage)*)
    (varName, (M.add varName 0 storage))
end;;

let printMap m = M.iter (fun key value -> Printf.printf "%s -> %d\n" key value) m;;

let unifyVariables expression = begin
  let rec unifier expression depth = begin
    match expression with 
      | Var v -> begin
        if (is_integer v) then begin
          let intValue = int_of_string v in
          if (intValue = depth) then (expression, M.empty) else 
            begin
              let unified = unifyVariable v M.empty in
              (expression, snd unified)
            end
        end else begin
          let unified = unifyVariable v M.empty in
          (*print_endline "hi";
          print_endline v;
          printMap (snd unified);*)
          (expression, snd unified)
        end
      end
      | Application(p, q) -> begin
        let unifiedP = unifier p depth in
        let unifiedQ = unifier q depth in
        (*printMap (snd unifiedP);
        printMap (snd unifiedQ);*)
        let unifiedStorage = M.merge (fun k xo yo -> match xo, yo with
                                                  | Some x, Some y -> Some (max x y)
                                                  | None, Some y -> Some y
                                                  | Some x, None -> Some x
                                                  | _ -> None) (snd unifiedP) (snd unifiedQ) in
        (*print_endline "Anything interesting?";
        printMap unifiedStorage;*)
        (Application(fst unifiedP, fst unifiedQ), unifiedStorage)
      end
      | Abstraction(varName, restOfExpression) -> begin
        let (newExpression, storage) = unifier restOfExpression (depth + 1) in
          (*print_endline "Critical section!";
          printMap storage;*)
          let (newVarName, newStorage) = unifyVariable varName storage in
            (Abstraction(newVarName, newExpression), newStorage)
      end
  end in fst (unifier expression (-1))
end;;

let makeNormalization expression = begin
  let rec makeManyBetaReductions maybeExpression = begin
    match maybeExpression with
    | Just e -> makeManyBetaReductions (findBetaRedex e)
    | Nothing e -> Just e
  end in
  match makeManyBetaReductions (Just expression) with
  | Just e -> e
  | Nothing e -> e
end;;


(*let s = string_of_tree (buildDBIndex inputExpression);;
fprintf oc "%s\n" s;;*)

(*all_input >> Lexing.from_string >> Parser.main Lexer.main >> string_of_tree >> fprintf oc "%s\n";;*)

let dbIndex = buildDBIndex inputExpression;;
let normalized = makeNormalization dbIndex;;
let unifiedVariables = unifyVariables normalized;;
let answer = string_of_tree (makeCanonicalForm unifiedVariables);;

(*fprintf oc "%s\n" (string_of_tree dbIndex);;
fprintf oc "%s\n" (string_of_tree normalized);;
fprintf oc "%s\n" (string_of_tree unifiedVariables);;
fprintf oc "Answer: %s\n" answer;;*)
fprintf oc "%s\n" answer;;
