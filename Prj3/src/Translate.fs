module Translate

open AST
open IR
open Helper


// Copy your "Translate.fs" file from Phase #2 (and fix it if needed).
// Symbol table is a mapping from identifier to a pair of register and type.
// Register is recorded here will be containg the address of that variable.
type SymbolTable = Map<Identifier,Register * CType>
let regNum_Arr = ref 0
let createArrRegName() = 
  let reg = sprintf"%%a%d" !regNum_Arr
  let _ = regNum_Arr := !regNum_Arr + 1
  reg

let regNum_Addr = ref 0

let createAddrRegName() = 
  let reg = sprintf"%%x%d" !regNum_Addr
  let _ = regNum_Addr := !regNum_Addr + 1
  reg

// Let's assume the following size for each data type.
let sizeof (ctyp: CType) =
  match ctyp with
  | CInt -> 4
  | CBool -> 1
  | CIntPtr -> 8
  | CBoolPtr -> 8
  | CIntArr n -> 4 * n
  | CBoolArr n -> n

// Find the register that contains "pointer" to variable 'vname'
let lookupVar (symtab: SymbolTable) (vname: Identifier) : Register =
  let _ = if not (Map.containsKey vname symtab) then failwith "Unbound variable"
  fst (Map.find vname symtab)

let checkType (symtab: SymbolTable) (vname: Identifier) : CType =
  let _ = if not (Map.containsKey vname symtab) then failwith "Unbound variable"
  snd  (Map.find vname symtab) 
//   (regName,ctyp)

let rec transExp (symtab: SymbolTable) (e: Exp) : Register * Instr list =
  match e with
  | Null ->
      let r = createRegName ()
      (r, [Set (r, Imm 0)])
  | Num i ->
      let r = createRegName ()
      (r, [Set (r, Imm i)])
  | Boolean true ->
      let r = createRegName()
      (r,[Set (r, Imm 1)])
  | Boolean false ->
      let r = createRegName()
      (r,[Set (r, Imm 0)])
  | Var vname ->
      let varReg = lookupVar symtab vname // Contains the address of 'vname'
      let r = createRegName()
      (r, [Load (r, varReg)])
  | Deref vname ->                      // *a
      let varReg = lookupVar symtab vname
      let r1 = createRegName()
      let r2 = createRegName()
      (r2, [Load (r1,varReg)] @ [Load (r2,r1)])
  | AddrOf vname ->                     // &a
      let varReg = lookupVar symtab vname
      let newReg = createAddrRegName()
      (newReg,[Set(newReg,Reg varReg)])
  | Arr (vname,exp) -> // r1 = size * idx_reg , r2 = varReg + r1 
      let varReg = lookupVar symtab vname
      let (idx_reg,idx_inst) = transExp symtab exp
      let size = 
        match checkType symtab vname with
        | CIntArr _ -> 4
        | CBoolArr _ -> 1
        | _ -> 0
      let r1 = createRegName()
      let r2 = createRegName()
      let r3 = createRegName()
      (r3,idx_inst @ [BinOp(r1,MulOp,Imm size,Reg idx_reg)] @ [BinOp(r2,AddOp,Reg varReg,Reg r1)] @ [Load(r3,r2)] )
  | Neg exp ->
      let (r1,inst1) = transExp symtab exp
      let r = createRegName()
      (r,inst1 @ [UnOp (r,NegOp,Reg r1)])
  | Add (exp1,exp2) -> 
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,AddOp,Reg r1,Reg r2)])
  | Sub (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,SubOp,Reg r1,Reg r2)])
  | Mul (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,MulOp,Reg r1,Reg r2)])
  | Div (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,DivOp,Reg r1,Reg r2)])
  | Equal (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,EqOp,Reg r1,Reg r2)])
  | NotEq (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,NeqOp,Reg r1,Reg r2)])
  | LessEq (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,LeqOp,Reg r1,Reg r2)])
  | LessThan (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,LtOp,Reg r1,Reg r2)])
  | GreaterEq (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,GeqOp,Reg r1,Reg r2)])
  | GreaterThan (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2
      let r = createRegName()
      (r,inst1 @ inst2 @ [BinOp (r,GtOp,Reg r1,Reg r2)])
  | And (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2      
      let L1 = createLabel()
      let r3 = createRegName()
      (r3, inst1 @ [Set(r2,Imm 0)] @ [GotoIfNot(Reg r1,L1)] @ inst2 @ [Label L1] @ [Set(r3,Reg r2)])
  | Or (exp1,exp2) ->
      let (r1,inst1) = transExp symtab exp1
      let (r2,inst2) = transExp symtab exp2      
      let L1 = createLabel()
      let r3 = createRegName()
      (r3,inst1 @ [Set(r2,Imm 1)] @ [GotoIf(Reg r1,L1)] @ inst2 @ [Label L1] @ [Set(r3,Reg r2)] )
  | Not exp ->
      let (r1,inst1) = transExp symtab exp
      let r = createRegName()
      (r,inst1 @ [UnOp (r,NotOp,Reg r1)])
//   | _ -> ("", []) // TODO: Fill in the remaining cases to complete the code.

let rec transStmt (symtab: SymbolTable) stmt : SymbolTable * Instr list =
  match stmt with
  | Declare (_, typ, vname) ->
      let r =
        match typ with
        | CIntArr(_) | CBoolArr(_) -> createArrRegName()
        | _ -> createRegName()
      let size = sizeof typ
      let symtab = Map.add vname (r, typ) symtab
      (symtab, [LocalAlloc (r, size)])
  | Define (_,typ,vname,exp) ->
      let r =
        match typ with
        | CIntArr(_) | CBoolArr(_) -> createArrRegName()        
        | _ -> createRegName()
      let size = sizeof typ
      let symtab = Map.add vname (r,typ) symtab
      let (val_Reg,val_inst) = transExp symtab exp
      (symtab, [LocalAlloc (r,size)] @ val_inst @ [Store (Reg val_Reg, r)])
  | Assign (_,vname,exp) ->
      let var_Reg = lookupVar symtab vname
      let (val_Reg, val_inst) = transExp symtab exp
      (symtab, val_inst @ [Store (Reg val_Reg,var_Reg)])
  | PtrUpdate (_,vname,exp) ->
      let varReg = lookupVar symtab vname
      let r1 = createRegName()
      let r2 = createRegName()
      let (val_Reg,val_inst) = transExp symtab exp
      (symtab,[Load (r1,varReg)] @ val_inst @ [Store (Reg val_Reg,r1)])
  | ArrUpdate (_,vname,idx_exp,val_exp) ->
      let varReg = lookupVar symtab vname
      let (idx_reg,idx_inst) = transExp symtab idx_exp
      let (val_Reg, val_inst ) = transExp symtab val_exp
      let size = 
        match checkType symtab vname with
        | CIntArr _ -> 4
        | CBoolArr _ -> 1
        | _ -> 0
      let r1 = createRegName()
      let r2 = createRegName()
      (symtab,idx_inst @ val_inst @ [BinOp(r1,MulOp,Imm size,Reg idx_reg)] 
      @ [BinOp(r2,AddOp,Reg varReg,Reg r1)] @ [Store (Reg val_Reg,r2)])
  | Return (_,exp) -> 
      let r = createRegName()
      let (val_Reg,val_inst) = transExp symtab exp
      (symtab,val_inst @ [Ret (Reg val_Reg)])
  | If (_,exp,stmts1, stmts2) ->
      let (cond_Reg,cond_inst) = transExp symtab exp
      let inst1 = transStmts symtab stmts1
      let inst2 = transStmts symtab stmts2
      let L1 = createLabel()
      let L_fin = createLabel()
      (symtab,cond_inst @ [GotoIf (Reg cond_Reg,L1)] @ inst2 @ [Goto (L_fin)] @ [Label L1] @ inst1 @ [Label L_fin])              
  | While (_,exp,stmts) ->
      let (cond_Reg, cond_inst) = transExp symtab exp
      let inst_list = transStmts symtab stmts
      let L_st = createLabel()
      let L1 = createLabel()
      let L_fin = createLabel()
      (symtab,  [Label L_st] @ cond_inst @ [GotoIfNot(Reg cond_Reg,L_fin)] @ inst_list @ [Goto L_st] @ [Label L_fin])

and transStmts symtab stmts: Instr list =
  match stmts with
  | [] -> []
  | headStmt :: tailStmts ->
      let symtab, instrs = transStmt symtab headStmt
      instrs @ transStmts symtab tailStmts

// This code allocates memory for each argument and records information to the
// symbol table. Note that argument can be handled similarly to local variable.
let rec transArgs accSymTab accInstrs args =
  match args with
  | [] -> accSymTab, accInstrs
  | headArg :: tailArgs ->
      // In our IR model, register 'argName' is already defined at the entry.
      let (argTyp, argName) = headArg
      let r =
        match argTyp with
        | CIntArr(_) | CBoolArr(_) -> createArrRegName()
        | _ -> createRegName()
      let size = sizeof argTyp
      // From now on, we can use 'r' as a pointer to access 'argName'.
      let accSymTab = Map.add argName (r, argTyp) accSymTab
      let accInstrs = [LocalAlloc (r, size); Store (Reg argName, r)] @ accInstrs
      transArgs accSymTab accInstrs tailArgs


// Translate input program into IR code.
// let run (prog: Program) : IRCode =
//   let (_, fname, args, stmts) = prog
//   let argRegs = List.map snd args
//   (fname, argRegs, [])
// Translate input program into IR code.
let run (prog: Program) : IRCode =
  let (_, fname, args, stmts) = prog
  let argRegs = List.map snd args
  let symtab, argInstrs = transArgs Map.empty [] args
  let bodyInstrs = transStmts symtab stmts
  (fname, argRegs, argInstrs @ bodyInstrs)
