module TypeCheck

open AST

// Symbol table is a mapping from 'Identifier' (string) to 'CType'. Note that
// 'Identifier' and 'Ctype' are defined in AST.fs file.
type SymbolTable = Map<Identifier,CType>

// For semantic analysis, you will need the following type definition. Note the
// difference between 'Ctype' and 'Typ': 'Ctype' represents the type annoted in
// the C code, whereas 'Typ' represents the type obtained during type checking.
type Typ = Int | Bool | NullPtr | IntPtr | BoolPtr | Error

// Convert 'CType' into 'Typ'.
let ctypeToTyp (ctype: CType) : Typ =
  match ctype with
  | CInt -> Int
  | CBool -> Bool
  | CIntPtr -> IntPtr
  | CBoolPtr -> BoolPtr

// Check expression 'e' and return its type. If the type of expression cannot be
// decided due to some semantic error, return 'Error' as its type.
let rec checkExp (symTab: SymbolTable) (e: Exp) : Typ =
  match e with
  | Null -> NullPtr
  | Num _ -> Int
  | Boolean _ -> Bool
  | Var x ->
      match Map.tryFind x symTab with
      | Some value -> ctypeToTyp value
      | None -> Error
  | Deref x -> 
      match Map.tryFind x symTab with
      | Some CIntPtr -> Int
      | Some CBoolPtr -> Bool
      | _ -> Error
  | AddrOf x ->
      match Map.tryFind x symTab with
      | Some CInt -> IntPtr
      | Some CBool -> BoolPtr
      | _ -> Error
  | Neg exp -> 
      let type_exp = checkExp symTab exp
      match type_exp with 
      | Int -> Int
      | _ -> Error
  | Add (exp1,exp2) | Sub (exp1,exp2) | Mul (exp1,exp2) | Div (exp1,exp2) ->
      let t1 = checkExp symTab exp1
      let t2 = checkExp symTab exp2
      match t1, t2 with
      | (Int,Int) -> Int
      | _ -> Error 
  | GreaterEq (exp1,exp2) | GreaterThan (exp1,exp2) | LessEq (exp1,exp2) | LessThan (exp1,exp2) ->
      let t1 = checkExp symTab exp1
      let t2 = checkExp symTab exp2
      match t1, t2 with
      | (Int,Int) -> Bool
      | _ -> Error 
  | Equal (exp1,exp2) | NotEq (exp1,exp2) -> // E == E
      let t1 = checkExp symTab exp1
      let t2 = checkExp symTab exp2
      if (t1 = t2) then Bool 
      else
          match t1,t2 with
          | (IntPtr, NullPtr) | (NullPtr,IntPtr) | (NullPtr,NullPtr)
          | (BoolPtr, NullPtr) | (NullPtr,BoolPtr) -> Bool
          | _ -> Error
  | And (exp1,exp2) | Or (exp1,exp2) -> // E && E
      let t1 = checkExp symTab exp1
      let t2 = checkExp symTab exp2
      match t1, t2 with
      | (Bool,Bool) -> Bool
      | _ -> Error
  | Not exp -> 
      let t1 = checkExp symTab exp
      match t1 with
      | Bool -> Bool
      | _ -> Error

// Check statement 'stmt' and return a pair of (1) list of line numbers that
// contain semantic errors, and (2) symbol table updated by 'stmt'.
let rec checkStmt (symTab: SymbolTable) (retTyp: CType) (stmt: Stmt) =
  match stmt with
  | Declare (line, ctyp, x) -> 
      ([], Map.add x ctyp symTab) // error - free 인듯
  | Define (line, ctyp, x, exp) ->
      let t1 = checkExp symTab exp
      let added_Map = Map.add x ctyp symTab
      if (t1 = (ctypeToTyp ctyp)) then ([],added_Map) 
      else 
        match (ctypeToTyp ctyp), t1 with
        | (IntPtr,IntPtr) | (IntPtr,NullPtr) | (BoolPtr,BoolPtr) | (BoolPtr,NullPtr) -> ([],added_Map)
        | _ -> ([line],added_Map)
  | Assign (line, Id, exp) ->
      let t1 = checkExp symTab (Var Id)
      let t2 = checkExp symTab exp
      if (t1 = t2) && t1 <> Error then ([],symTab) 
      else
        match (t1,t2) with
        | (IntPtr,IntPtr) | (IntPtr,NullPtr) | (BoolPtr,BoolPtr) | (BoolPtr,NullPtr) -> ([],symTab)
        | _ -> ([line],symTab)
  | PtrUpdate (line, Id, exp) ->
      let exp_type = checkExp symTab exp
      let id_type = checkExp symTab (Var Id)
      match id_type, exp_type with
      | (IntPtr,Int) | (BoolPtr,Bool) -> ([],symTab)
      | _ -> ([line],symTab)    
  | Return (line, exp) ->
      let t1 = checkExp symTab exp
      if (t1 = (ctypeToTyp retTyp)) then ([],symTab) 
      else
        match (ctypeToTyp retTyp), t1 with
        | (IntPtr,NullPtr) | (BoolPtr,NullPtr) -> ([],symTab)
        | _ -> ([line],symTab)
  | If (line, exp, stmt_list1, stmt_list2) ->
      let cond_type = checkExp symTab exp
      let list1 = checkStmts symTab retTyp stmt_list1
      let list2 = checkStmts symTab retTyp stmt_list2
      match cond_type with
      | Bool | Int | IntPtr | BoolPtr | NullPtr  -> (list1 @ list2,symTab) 
      | _ -> (list1 @ list2 @ [line],symTab)
  | While (line, exp, stmt_list) -> 
      let cond_type = checkExp symTab exp
      let list1 = checkStmts symTab retTyp stmt_list
      match cond_type with
      | Bool | Int | IntPtr | BoolPtr  -> (list1,symTab) 
      | _ -> (list1 @ [line],symTab)

// Check the statement list and return the line numbers of semantic errors. Note
// that 'checkStmt' and 'checkStmts' are mutually-recursive (they can call each
// other). This function design will make your code more concise.
and checkStmts symTab (retTyp: CType) (stmts: Stmt list): LineNo list =
  match stmts with
  | [] -> []
  | stmt :: tail ->
      let new_symTab: SymbolTable = Map.empty
      let (error_list,new_symTab) = checkStmt symTab retTyp stmt
      error_list @ checkStmts new_symTab retTyp tail

// Record the type of arguments to the symbol table.
let rec collectArgTypes argDecls symTab =
  match argDecls with
  | [] -> symTab
  | (ctyp,id) :: tail -> collectArgTypes tail (Map.add id ctyp symTab)

// Check the program and return the line numbers of semantic errors.
let run (prog: Program) : LineNo list =
  let (retTyp, _, args, stmts) = prog
  let symTab = collectArgTypes args Map.empty
  let errorLines = checkStmts symTab retTyp stmts
  // Remove duplicate entries and sort in ascending order.
  List.sort (List.distinct errorLines)
