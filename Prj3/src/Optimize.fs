module Optimize

open IR
open CFG
open DFA
open Translate
// type VarMap = Map<string,Register>

module MemToReg =
  let isCandidateReg (reg: Register) : bool =
    if reg.StartsWith("%x") || reg.StartsWith("%r") then true else false

  let findCandidateRegs (instr: Instr) (regSet: Set<Register>) : Set<Register> =
    match instr with
    | LocalAlloc (r, _) ->
        if isCandidateReg r then Set.add r regSet else regSet
    | _ -> regSet

  /// LocalAlloc에서 Register를 모아2
  let collectCandidateRegs (instrMap: InstrMap) (nodeID: int) (regSet: Set<Register>) : Set<Register> =
    let instr = Map.find nodeID instrMap
    findCandidateRegs instr regSet

  let collectAllCandidates (instrMap: InstrMap) (allNodes: int list) (regSet: Set<Register>) : Set<Register> =
    List.fold (fun acc nodeID -> collectCandidateRegs instrMap nodeID acc) regSet allNodes

  let findNotCandidate (instr: Instr) (regSet: Set<Register>) : Set<Register> =
    match instr with
    | Store(Reg r,_) | UnOp(_,_,Reg r) | Set(_,Reg r) -> if Set.contains r regSet then Set.remove r regSet else regSet
    | BinOp(_,_,Imm n,Reg r) | BinOp(_,_,Reg r,Imm n) -> if Set.contains r regSet then Set.remove r regSet else regSet
    | BinOp(_,_,Reg r1,Reg r2) ->
        let newRegSet = if Set.contains r1 regSet then Set.remove r1 regSet else regSet
        let newRegSet = if Set.contains r2 newRegSet then Set.remove r2 newRegSet else newRegSet
        newRegSet
    | _ -> regSet

  /// Store에서 사용된 Register를 제거2
  let removeNotCandidates (instrMap: InstrMap) (nodeID: int) (regSet: Set<Register>) : Set<Register> =
    let instr = Map.find nodeID instrMap
    findNotCandidate instr regSet

  let removeRegs (instrMap: InstrMap) (allNodes: int list) (candidateRegs: Set<Register>) : Set<Register> =
    List.fold (fun acc nodeID -> removeNotCandidates instrMap nodeID acc) candidateRegs allNodes
  
  /// (LocalAlloc 제거, Store/Load 변환)
  let changeInstr (instr: Instr) (regSet: Set<Register>) : Instr list =
    match instr with
    | LocalAlloc (r, _) ->
        if Set.contains r regSet then [] else [instr] // LocalAlloc 제거
    | Store (oprnd, r) ->
        if Set.contains r regSet then [Set (r, oprnd)] else [instr] // Store -> Set
    | Load (dest, src) ->
        if Set.contains src regSet then [Set (dest, Reg src)] else [instr] // Load -> Set
    | _ -> [instr] // 나머지는 그대로 유지

  let findInstr (instrMap: InstrMap) (nodeID: int) (finalRegs: Set<Register>) (instrs: Instr list) : Instr list =
    let instr = Map.find nodeID instrMap
    instrs @ changeInstr instr finalRegs

  let collectOptimizedInstrs (instrMap: InstrMap) (allNodes: int list) (finalRegs: Set<Register>) : Instr list =
    List.fold (fun acc nodeID -> findInstr instrMap nodeID finalRegs acc) [] allNodes

  let MemToReg (cfg: CFG) : Instr list =
    let instrMap, _, _ = cfg
    let allNodes = CFG.getAllNodes cfg
    let candidateRegs = collectAllCandidates instrMap allNodes Set.empty
    let finalRegs = removeRegs instrMap allNodes candidateRegs
    collectOptimizedInstrs instrMap allNodes finalRegs

  let run (instrs: Instr list) : Instr list =
    let cfg = CFG.make instrs
    MemToReg cfg



module ConstantFolding =
  let foldConstant instr =
    let temp : Register = "temp"
    match instr with
    | UnOp (r, NegOp, Imm x) -> (true, Set (r, Imm (-x)))
    | UnOp (r, NotOp, Imm x) -> (true, Set (r, Imm (if x = 0 then 1 else 0)))
    // BinOp - Arith
    | BinOp (r, AddOp, Imm x, Imm y) -> (true, Set (r, Imm (x + y)))
    | BinOp (r, SubOp, Imm x, Imm y) -> (true, Set (r, Imm (x - y)))
    | BinOp (r, MulOp, Imm x, Imm y) -> (true, Set (r, Imm (x * y)))
    | BinOp (r, DivOp, Imm x, Imm y) -> (true, Set (r, Imm (x / y)))
    // BinOp - Comparison
    | BinOp (r, EqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x = y then 1 else 0)))
    | BinOp (r, NeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <> y then 1 else 0)))
    | BinOp (r, LeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <= y then 1 else 0)))
    | BinOp (r, LtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x < y then 1 else 0)))
    | BinOp (r, GeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x >= y then 1 else 0)))
    | BinOp (r, GtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x > y then 1 else 0)))
    // if false -> 지우고 , if true -> goto
    | GotoIf (Imm num,L1) -> if num = 0 then (true,Set(temp,Imm 0)) else (true,Goto(L1))
    | GotoIfNot (Imm num,L1) -> if num <> 0 then (true,Set(temp,Imm 0)) else (true,Goto(L1))
    | _ -> (false,instr)

  let run instrs =
    let results = List.map foldConstant instrs
    let flags, instrs = List.unzip results
    let isOptimized = List.contains true flags
    (isOptimized, instrs)


module ConstantPropagation =
  
  // instr의 reg t에 해당하는 Set(t,Imm num)꼴이 있으면 num을 return
  let findRegValue (rdSet: DFA.RDSet) (t: Register) : int option =
    let rec findValueInSet setList =
      match setList with
      | [] -> None
      | instr :: tail ->
        match instr with
        | Set (reg, Imm num) when reg = t -> Some num
        | _ -> findValueInSet tail
    findValueInSet (Set.toList rdSet)

  // instr에서 정의되는 reg 반환
  let getDefReg (instr: Instr) : Register option =
    match instr with
    | Set (r, _) | LocalAlloc (r, _) | UnOp (r, _, _) | BinOp (r, _, _, _) | Load (r, _) -> Some r
    | _ -> None
  
  // reg를 정의하는 Set(t, Imm num) 형태의 instr 개수 return
  let countDef_Instrs (rdSet: DFA.RDSet) (t: Register) : int =
    let rec countDef list acc =
        match list with
        | [] -> acc
        | instr :: tail ->
            match instr with
            | Set (reg, _) | LocalAlloc (reg, _) | UnOp (reg, _, _) | BinOp (reg, _, _, _) | Load (reg, _) when reg = t -> countDef tail (acc + 1)
            | _ -> countDef tail acc
    countDef (Set.toList rdSet) 0

  let countSet_Instr (rdSet: DFA.RDSet) (t: Register) : int =
    let rec countSet list acc =
        match list with
        | [] -> acc
        | instr :: tail ->
            match instr with
            | Set (reg, Imm _) when reg = t -> countSet tail (acc + 1)
            | _ -> countSet tail acc
    countSet (Set.toList rdSet) 0 

  /// 각 instruction 중 우변의 operand로 쓰인 register 가 있다면 이를 교체해줘
  let changeInstr (rdSet: DFA.RDSet) (instr: Instr) : Instr =
      match instr with
      | Set (r, Reg t) ->
        if (countDef_Instrs rdSet t = 1) && (countSet_Instr rdSet t = 1)then 
          match findRegValue rdSet t with
          | Some num -> Set (r, Imm num)
          | None -> instr
        else instr
      | UnOp (r, op, Reg t) ->
        if (countDef_Instrs rdSet t = 1) && (countSet_Instr rdSet t = 1)then
          match findRegValue rdSet t with
          | Some num -> UnOp (r, op, Imm num)
          | None -> instr
        else instr
      | BinOp (r, op, Reg t1, Reg t2) ->
        let newOp1 =
          if (countDef_Instrs rdSet t1 = 1) && (countSet_Instr rdSet t1 = 1)then
            match findRegValue rdSet t1 with
            | Some num -> Imm num
            | None -> Reg t1
          else Reg t1
        let newOp2 =
            if (countDef_Instrs rdSet t2 = 1) && (countSet_Instr rdSet t2 = 1)then
              match findRegValue rdSet t2 with
              | Some num -> Imm num
              | None -> Reg t2
            else Reg t2
        BinOp (r, op, newOp1, newOp2)
      | BinOp (r, op, Imm v, Reg t) ->
        if (countDef_Instrs rdSet t = 1) && (countSet_Instr rdSet t = 1)then
          match findRegValue rdSet t with
          | Some num -> BinOp (r,op,Imm v, Imm num)
          | None -> instr
        else instr
      | BinOp (r, op, Reg t, Imm v) ->
        if (countDef_Instrs rdSet t = 1) && (countSet_Instr rdSet t = 1)then
          match findRegValue rdSet t with
          | Some num -> BinOp (r,op, Imm num, Imm v)
          | None -> instr
        else instr
      | Load (r1, r2) ->
        if (countDef_Instrs rdSet r2 = 1) && (countSet_Instr rdSet r2 = 1)then
          match findRegValue rdSet r2 with
          | Some num -> Set (r1,Imm num)
          | None -> instr
        else instr
      | Store (Reg r,v) ->
         if (countDef_Instrs rdSet r = 1) && (countSet_Instr rdSet r = 1)then
          match findRegValue rdSet r with
          | Some num -> Store (Imm num,v)
          | None -> instr
         else instr
      | GotoIf(Reg r, l1) -> 
        if (countDef_Instrs rdSet r = 1) && (countSet_Instr rdSet r = 1)then
          match findRegValue rdSet r with
          | Some num -> GotoIf (Imm num,l1)
          | None -> instr
         else instr  
      | GotoIfNot(Reg r, l1) -> 
        if (countDef_Instrs rdSet r = 1) && (countSet_Instr rdSet r = 1)then
          match findRegValue rdSet r with
          | Some num -> GotoIfNot (Imm num,l1)
          | None -> instr
         else instr  
      | Ret(Reg r) ->
        if (countDef_Instrs rdSet r = 1) && (countSet_Instr rdSet r = 1)then
          match findRegValue rdSet r with
          | Some num -> Ret(Imm num)
          | None -> instr
         else instr 
      | _ -> instr

  // Write your logic to run constant propagation with RD analysis result.
  let run instrs =
    let cfg = CFG.make instrs
    let rdMap = RDAnalysis.run cfg
    let allNodes = CFG.getAllNodes cfg
    let rec applyChange nodes acc =
      match nodes with
      | [] -> List.rev acc 
      | nodeID :: tail ->
          let instr = CFG.getInstr nodeID cfg
          let rdSet =
              match Map.tryFind nodeID rdMap with
              | Some set -> set
              | None -> Set.empty
          let newInstr = changeInstr rdSet instr
          applyChange tail (newInstr :: acc)

    let optimizedInstrs = applyChange allNodes []
    let hasChanged = (instrs <> optimizedInstrs)
    (hasChanged, optimizedInstrs)

module CopyPropagation =
  
  // aeSet에서 t가 Set(t,reg r1)에 해당하는 instr을 찾아. 
  let checkSet instr reg : bool =
    match instr with 
    | Set(r ,_) -> r = reg
    | _ -> false 

  // instr을 보고 해당 우변의 reg인 t를 확인해 
  // 만약 있다면 -> 해당 reg 반환
  // 없다면 -> None
  let findSubReg (aeSet: DFA.AESet) (t: Register) : Register =
    let s = Set.filter (fun x -> (checkSet x t)) aeSet
    let s = Set.toList s
    // printfn "instr %A" s
    match s with
    | Set(reg,Reg r1) :: _ -> if t = reg then r1 else t
    | _ -> t


  let changeInstr (aeSet: DFA.AESet) (instr: Instr) : Instr =
    // printfn "Instrction %A, ae_in %A" instr aeSet
    match instr with
    | Set (r, Reg t) -> Set (r, Reg (findSubReg aeSet t))
    | UnOp (r, op, Reg t) -> UnOp(r,op,Reg (findSubReg aeSet t))
    | BinOp(r,op,Reg t1,Reg t2) -> BinOp(r,op,Reg (findSubReg aeSet t1),Reg (findSubReg aeSet t2))
    | BinOp(r,op,Imm n1,Reg t1) -> BinOp(r,op,Imm n1,Reg (findSubReg aeSet t1))
    | BinOp(r,op,Reg t1,Imm n1) -> BinOp(r,op,Reg (findSubReg aeSet t1),Imm n1)
    | Load (r1, r) -> Load(r1,(findSubReg aeSet r)) 
    | Store (Reg r1,r2) -> Store(Reg (findSubReg aeSet r1),(findSubReg aeSet r2))
    | Store (Imm n,r2) -> Store(Imm n,(findSubReg aeSet r2))
    | GotoIf(Reg r1, l1) -> GotoIf(Reg (findSubReg aeSet r1),l1)
    | GotoIfNot(Reg r1, l1) -> GotoIfNot(Reg (findSubReg aeSet r1),l1)
    | Ret(Reg r) -> Ret(Reg (findSubReg aeSet r))
    | _ -> instr

  let run (instrs: Instr list) : bool * Instr list =
    let cfg = CFG.make instrs
    let aeOutMap = AEAnalysis.run cfg
    let allNodes = CFG.getAllNodes cfg
    let rec mapNodes nodes acc =
      match nodes with
      | [] -> acc
      | nodeID :: rest ->
          let instr = CFG.getInstr nodeID cfg
          let aeIn = AEAnalysis.propagation nodeID cfg aeOutMap
          let newInstr = changeInstr aeIn instr
          mapNodes rest (newInstr :: acc)

    let optimizedInstrs = List.rev (mapNodes allNodes [])
    let hasChanged = (instrs <> optimizedInstrs)
    (hasChanged, optimizedInstrs)


module CSE = 
  // copy에선 set만 봤는데 
  // 여기서 set무시하고 bin Un load 만 확인해서.
  // 내가 대체하고 싶은 cse

  // %t2 = 4 * %t1
  // %t3 = 4 * %t1 -> %t3 = %t2

  // 있는지 부터 확인해. 
  
  let checkTwoExp instr1 instr2 : bool =
    match instr1,instr2 with
    | UnOp(r1,op1,a1),UnOp(r2,op2,a2) -> (op1 = op2) && (a1 = a2) 
    | BinOp(r1,op1,a1,b1),BinOp(r2,op2,a2,b2) -> (op1 = op2) && (a1 = a2) && (b1 = b2)
    | Load(r1,a1),Load(r2,a2) -> (a1 = a2)
    | _ -> false

  let findSubExp aeSet instr : Register option =
    let aeList = Set.toList aeSet
    let rec findCandidateExp instrlist =
      match instrlist with
      | [] -> None
      | head :: tail ->
        if checkTwoExp head instr
        then 
          match head with
          | UnOp(r,_,_) | BinOp(r,_,_,_) | Load(r,_)-> Some r
          | _ -> findCandidateExp tail
        else findCandidateExp tail
    findCandidateExp aeList
    
  let changeInstr (aeSet: DFA.AESet) (instr: Instr) : Instr =
    // printfn "Instrction %A, ae_in %A" instr aeSet
    match findSubExp aeSet instr with
    | Some replaceReg -> 
      match instr with
      | UnOp(r,_,_) | BinOp(r,_,_,_) | Load(r,_) -> Set(r,Reg replaceReg)
      | _ -> instr
    | None -> instr

  let run (instrs: Instr list) : bool * Instr list =
    let cfg = CFG.make instrs
    let aeOutMap = AEAnalysis.run cfg
    let allNodes = CFG.getAllNodes cfg
    let rec mapNodes nodes acc =
      match nodes with
      | [] -> acc
      | nodeID :: tail ->
          let instr = CFG.getInstr nodeID cfg
          let aeIn = AEAnalysis.propagation nodeID cfg aeOutMap
          let newInstr = changeInstr aeIn instr
          mapNodes tail (newInstr :: acc)

    let optimizedInstrs = List.rev (mapNodes allNodes [])
    let hasChanged = (instrs <> optimizedInstrs)
    (hasChanged, optimizedInstrs)

module DCE =

  /// 현재 instr에서 정의된 reg return
  let getDefReg (instr: Instr) =
    match instr with
    | Set (r, _) | LocalAlloc (r, _) | UnOp (r, _, _) | BinOp (r, _, _, _) | Load (r, _) -> Some r
    | _ -> None

  let applyDCE (cfg: CFG) (nodeID: int) (lvMap: Map<int, LVSet>) : Instr list =
    let instr = CFG.getInstr nodeID cfg
    let lvSet =
      match Map.tryFind nodeID lvMap with
      | Some set -> set
      | None -> Set.empty

    match getDefReg instr with
    | Some reg -> if Set.contains reg lvSet then [instr] else []
    | None -> [instr]

  let run (instrs: Instr list) : bool * Instr list =
    let cfg = CFG.make instrs
    let lvMap = LVAnalysis.run cfg // nodeID -> LVSet
    let allNodes = CFG.getAllNodes cfg

    let rec processNodes acc nodes =
      match nodes with
      | [] -> acc
      | nodeID :: tail ->
          let filteredInstrs = applyDCE cfg nodeID lvMap
          processNodes (acc @ filteredInstrs) tail

    let optimizedInstrs = processNodes [] allNodes
    let hasChanged = (instrs <> optimizedInstrs)
    (hasChanged, optimizedInstrs)



// You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =
  let cf, instrs1 = ConstantFolding.run instrs
  let cp, instrs2 = ConstantPropagation.run instrs1
  let copy,instrs3 = CopyPropagation.run instrs2
  // printfn
  //     "After COPY diff : %A \n -> \n\n %A"
  //     (Set.difference (Set.ofList instrs2) (Set.ofList instrs3))
  //     (Set.difference (Set.ofList instrs3) (Set.ofList instrs2))
  let cse, instrs4 = CSE.run instrs3
  let dce , instrs5 = DCE.run instrs4

  if cp || cf || copy || cse || dce then optimizeLoop instrs5 else instrs5

let run (ir: IRCode) : IRCode =
  let (fname, args, instrs) = ir
  let instrs = MemToReg.run instrs
  // let optimizedInstrs = optimizeLoop instrs
  // (fname, args, optimizedInstrs)
  (fname,args,instrs)

