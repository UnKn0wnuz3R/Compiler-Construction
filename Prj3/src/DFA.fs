module DFA

open IR
open CFG

// You can represent a 'reaching definition' element with an instruction.
type RDSet = Set<Instr>
type AESet = Set<Instr>
type LVSet = Set<Register>

module RDAnalysis =

  let checkReg (t: Register) (instr: Instr) : bool = 
    match instr with
    | Set (t1,_) | LocalAlloc (t1, _) | UnOp (t1, _, _) | BinOp (t1, _, _, _) | Load (t1, _) -> t1 = t
    | _ -> false

  let transFunc (rd_in: RDSet) (instr: Instr) : RDSet =
    match instr with
    // 알 로 유 바 셋 -> 빼고 추가해 
    | Set (t, _) | LocalAlloc (t, _) | UnOp (t, _, _) | BinOp (t, _, _, _) | Load (t, _) ->
      let newSet = Set.filter (fun x -> not (checkReg t x)) rd_in
      Set.add instr newSet
    | _ -> rd_in

  let propagation (nodeID: int) (cfg: CFG) (rdOutMap: Map<int, RDSet>) : RDSet = 
    let preds_list = CFG.getPreds nodeID cfg
    let union_pred rdset predID : RDSet = 
      let predRD_out = Map.find predID rdOutMap
      Set.union rdset predRD_out
    List.fold union_pred Set.empty preds_list

  let rec fixpoint (cfg: CFG) (allNodes: int list) (rdInMap: Map<int, RDSet>) (rdOutMap: Map<int, RDSet>) : Map<int, RDSet> = 
    let calcNode (rd_in, rd_out, flag)  nodeID = 
      let newIn = propagation nodeID cfg rd_out
      let curr_inst = CFG.getInstr nodeID cfg
      let newOut = transFunc newIn curr_inst

      let prevOut = Map.find nodeID rd_out
      let isChanged = (newOut <> prevOut)

      let updateIn = Map.add nodeID newIn rd_in
      let updateOut = Map.add nodeID newOut rd_out
      (updateIn, updateOut, flag || isChanged)
    
    let (newRDInMap, newRDOutMap, changed) = List.fold calcNode (rdInMap, rdOutMap, false) allNodes
    if not changed then newRDInMap else fixpoint cfg allNodes newRDInMap newRDOutMap

  let run (cfg: CFG) : Map<int, RDSet> =
    let allNodes = CFG.getAllNodes cfg
    let rdInMap = List.fold (fun acc id -> Map.add id Set.empty acc) Map.empty allNodes
    let rdOutMap = List.fold (fun acc id -> Map.add id Set.empty acc) Map.empty allNodes
    fixpoint cfg allNodes rdInMap rdOutMap    

module AEAnalysis =  
  
  /// 모든 표현식의 Universal Set을 계산(알 로 유 바 셋)
  let calc_UniversalSet (cfg: CFG) : AESet =
    let allNodes = CFG.getAllNodes cfg
    let allInstrs = List.fold (fun acc nodeID -> Set.add (CFG.getInstr nodeID cfg) acc) Set.empty allNodes
    allInstrs

  // let univ_Set = calc_UniversalSet cfg 
  let removeLoad ae_in instr : bool =
    match instr with 
    | Load(_,_) -> true
    | _ -> false  

  // 현재 정의되는 reg가 들어있는 instr 다 빼기
  let removeInstr instr reg : bool =
    match instr with
    | Set(r,Imm n) | UnOp(r,_,Imm n) -> (reg = r)
    | Set(r,Reg r1) | UnOp(r,_,Reg r1) -> (reg = r) || (reg = r1) 
    | LocalAlloc(r,_) -> (reg = r)
    | BinOp(r,_,Reg r1,Imm n) | BinOp(r,_,Imm n,Reg r1) -> (reg = r) || (reg = r1)
    | BinOp(r,_,Reg r1,Reg r2) -> (reg = r) || (reg = r1) || (reg = r2)
    | BinOp(r,_,Imm n1,Imm n2) -> (reg = r)
    | Load(r,r1) -> (reg = r) || (reg = r1)
    | _ -> false

  let transFunc (ae_in: AESet) (instr: Instr) : AESet =
    match instr with
    // 빼기 : 알 로 유 바 셋
    // 추가 : 유 바 셋 (우변에 현재 정의되는 reg 있는지 확인)
    // store -> 나오면 모든 load를 다 빼
    | Set (r, Reg r1) | UnOp (r, _, Reg r1) ->
      if r1 <> r 
      then 
        let newSet = Set.filter (fun x -> not (removeInstr x r)) ae_in
        Set.add instr newSet
      else 
        Set.filter (fun x -> not (removeInstr x r)) ae_in
    | BinOp (r, _, Imm n1, Imm n2) -> 
      let newSet = Set.filter (fun x -> not (removeInstr x r)) ae_in
      Set.add instr newSet
    | BinOp (r,_,Reg r1, Imm n) | BinOp (r,_, Imm n,Reg r1) ->
      if r <> r1 
      then   
        let newSet =Set.filter (fun x -> not (removeInstr x r)) ae_in
        Set.add instr newSet
      else 
       Set.filter (fun x -> not (removeInstr x r)) ae_in
    | BinOp (r,_,Reg r1, Reg r2) ->
      if (r <> r1) && (r <> r2)
      then  
        let newSet = Set.filter (fun x -> not (removeInstr x r)) ae_in
        Set.add instr newSet
      else 
       Set.filter (fun x -> not (removeInstr x r)) ae_in
    | Load (r, _)| LocalAlloc (r, _) | Set(r,_) | UnOp(r,_,_)  -> Set.filter (fun x -> not (removeInstr x r)) ae_in
    | Store(_,_) -> Set.filter (fun x -> not (removeLoad ae_in x)) ae_in
    | _ -> ae_in

  let propagation (nodeID: int) (cfg: CFG) (aeOutMap: Map<int, AESet>) : AESet = 
    let preds_list = CFG.getPreds nodeID cfg
    match preds_list with
    | [] -> Set.empty
    | _ -> 
      let intersect_pred aeSet predID : AESet = 
        let predAE_out = Map.find predID aeOutMap
        Set.intersect aeSet predAE_out
      List.fold intersect_pred (calc_UniversalSet cfg) preds_list

  let rec fixpoint (cfg: CFG) (allNodes: int list) (aeOutMap: Map<int, AESet>) : Map<int,AESet> = 
    let rec calcNode (ae_out, flag) nodes =
      match nodes with
      | [] -> (ae_out,flag)
      | nodeID :: rest ->
        let newIn = propagation nodeID cfg ae_out
        let curr_inst = CFG.getInstr nodeID cfg
        let newOut = transFunc newIn curr_inst

        let prevOut = Map.find nodeID ae_out
        let isChanged = (newOut <> prevOut)

        let updateOut = Map.add nodeID newOut ae_out
        calcNode (updateOut, flag || isChanged) rest 
    
    let (newAEOutMap, flag) = calcNode (aeOutMap, false) allNodes
    if not flag then newAEOutMap else fixpoint cfg allNodes newAEOutMap

  let run (cfg: CFG) : Map<int, AESet> =
    let allNodes = CFG.getAllNodes cfg
    let univ_Set = calc_UniversalSet cfg
    let aeOutMap = List.fold (fun acc id -> Map.add id univ_Set acc) Map.empty allNodes
    let finalAEOut = fixpoint cfg allNodes aeOutMap
    
    // List.iter (fun nodeID ->
    //   let instr = CFG.getInstr nodeID cfg
    //   let rdSet = Map.find nodeID finalRDIn
    //   printfn "Node %d: Instruction: %A, rd_in: %A" nodeID instr rdSet
    // ) allNodes
    
    finalAEOut


module LVAnalysis =

  let useRegs instr =
    match instr with
    | BinOp (_, _, Reg r1, Reg r2) -> Set.ofList [r1; r2]
    | Store(Reg r1,r2) -> Set.ofList [r1;r2]
    | Set (_, Reg r) | UnOp (_, _, Reg r) | Load (_, r) | Store (_, r) 
    | GotoIf (Reg r, _) | GotoIfNot (Reg r, _) 
    | Ret (Reg r) | BinOp (_, _, Reg r, _) | BinOp (_, _, _, Reg r) -> Set.add r Set.empty
    | _ -> Set.empty

  let defReg instr =
    match instr with
    | Set (r, _) | LocalAlloc (r, _) | UnOp (r, _, _) | BinOp (r, _, _, _) | Load (r, _) -> Some r
    | _ -> None

  let calc_LVOut nodeID cfg (lv_in: Map<int, LVSet>) : LVSet =
    let succNodes = CFG.getSuccs nodeID cfg
    let rec union_succ_LVin acc succ_list =
      match succ_list with
      | [] -> acc
      | head :: tail ->
          let succ_LVin = 
            match Map.tryFind head lv_in with
            | Some set -> set
            | None -> Set.empty
          union_succ_LVin (Set.union acc succ_LVin) tail
    union_succ_LVin Set.empty succNodes

  /// Transfer function: LV_out -> LV_in
  let transfer nodeID cfg (lv_out: LVSet) : LVSet =
    let instr = CFG.getInstr nodeID cfg
    let DefReg = defReg instr
    let UseRegs = useRegs instr
    match DefReg with
    | Some r -> Set.union (Set.remove r lv_out) UseRegs
    | None -> Set.union lv_out UseRegs

  let rec fixpoint (cfg: CFG) (lvInMap: Map<int, LVSet>) (lvOutMap: Map<int, LVSet>) : Map<int, LVSet> =
    let allNodes = List.rev (CFG.getAllNodes cfg) 
    let rec processNodes (updatedInMap, updatedOutMap, hasChanged) nodes =
      match nodes with
      | [] -> (updatedInMap, updatedOutMap, hasChanged)
      | nodeID :: rest ->
          let newLVOut = calc_LVOut nodeID cfg updatedInMap
          let newLVIn = transfer nodeID cfg newLVOut

          let oldLVIn = Map.find nodeID updatedInMap
          let changed = (newLVIn <> oldLVIn) 

          let newInMap = Map.add nodeID newLVIn updatedInMap
          let newOutMap = Map.add nodeID newLVOut updatedOutMap
          processNodes (newInMap, newOutMap, hasChanged || changed) rest

    let (newLVInMap, newLVOutMap, hasChanged) = processNodes (lvInMap, lvOutMap, false) allNodes
    if hasChanged then fixpoint cfg newLVInMap newLVOutMap else newLVOutMap

  let run (cfg: CFG) : Map<int, LVSet> =
    let allNodes = CFG.getAllNodes cfg
    let lvInMap = List.fold (fun acc nodeID -> Map.add nodeID Set.empty acc) Map.empty allNodes
    let lvOutMap = List.fold (fun acc nodeID -> Map.add nodeID Set.empty acc) Map.empty allNodes
    fixpoint cfg lvInMap lvOutMap





