module

public import MinCostFlow.HierPaths.BuildProgConnRow
public import MinCostFlow.HierPaths.BuildProgFinishBatch

/-!
# Shortcutting a sibling matching

A one-pair routing reply has one endpoint row. Keep its endpoint
address and the shortcut directory in a two-word context for the CSR
writer. The shared walk row procedure erases repeated vertices.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Arguments are reply base and end, parent endpoint base and vertex
count, raw walk length bound, and the matching size. -/
def buildConnEraseProc (fWalk : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 0) (.const 4)) ;;
  .assign 7 (.bin .add (.reg 6) (.load (.bin .add (.reg 0) (.const 1)))) ;;
  .assign 8 (.bin .add (.reg 6) (.load (.bin .add (.reg 0) (.const 2)))) ;;
  .assign 9 (.bin .add (.reg 7) (.const 2)) ;;
  .assign 10 (.bin .add (.reg 1) (.const 2)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 5)) ;;
  .assign 12 (.bin .add (.bin .add (.reg 11) (.reg 4)) (.const 1)) ;;
  .store (.reg 1) (.reg 9) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 10) ;;
  .call 13 fWalk [.reg 8,.reg 5,.const 0,.reg 9,.reg 2,.reg 11,.reg 12,.reg 10,
    .bin .add (.reg 12) (.reg 3),.reg 5] ;;
  .ret (.reg 13)

theorem buildConnEraseProc_noRand (fWalk : ℕ) : (buildConnEraseProc fWalk).NoRand := by
  simp [buildConnEraseProc,Stmt.NoRand]

/-- Model of the routed row for a single pair. -/
def connectorWalkRow (M : List (ℕ × ℕ)) (emb : ℕ → List ℕ) : BuildWalkRow :=
  ⟨M.length,M.length,0,fun i => (edgeAt M i).1,fun i => (edgeAt M i).2,emb⟩

/-- The argument array to the shared walk writer for a single matching. -/
def connEraseWalkArgs (mem : ℕ → ℕ) (rep top ends n d s : ℕ) : List ℕ :=
  let mt := (matchedTableBases mem rep).1
  let tb := (matchedTableBases mem rep).2
  let dir := top+2
  let vs := dir+s
  let P := vs+d+1
  [tb,s,0,mt+2,ends,vs,P,dir,P+n,s]

/-- On return the context identifies the shortened connector rows. -/
def buildConnEraseContract (w : ℕ) (G : Graph) (M : List (ℕ × ℕ))
    (emb : ℕ → List ℕ) (d : ℕ) : Contract where
  pre args mem := ∃ rep top ends,
    args = [rep,top,ends,G.n,d,M.length] ∧
    ListAt mem rep (routeResultWords (.matched [M] emb)) ∧
    rep+(routeResultWords (.matched [M] emb)).length ≤ top ∧ ZeroFrom mem top ∧
    top+2+M.length+d+1+G.n < 2^w ∧ 4 < 2^w ∧
    (∀ i < M.length, IsEdgeWalk G.edges (edgeAt M i).1 (edgeAt M i).2 (emb i)) ∧
    ∀ mid, (∀ a < top, mid a = mem a) → ZeroFrom mid (top+2) →
      (buildWalkRowContract w G (connectorWalkRow M emb)).pre
        (connEraseWalkArgs mem rep top ends G.n d M.length) mid
  post args mem v after := ∃ rep top ends,
    args = [rep,top,ends,G.n,d,M.length] ∧
    v = (connectorWalkRow M emb).cursor (top+2+M.length+d+1+G.n) M.length ∧
    ConnectorRowsAt top M.length (edgeAt M) (fun i => erase G.edges (edgeAt M i).1 (emb i)) v after ∧
    (∀ a < top, after a = mem a) ∧
    (∀ i < G.n, after (top+2+M.length+d+1+i) = 0) ∧ ZeroFrom after v
  cost args mem := (buildWalkRowContract w G (connectorWalkRow M emb)).cost args mem+130

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

private theorem endpoints_get {M : List (ℕ × ℕ)} {i : ℕ} (hi : i < M.length) :
    let es := M.flatMap (fun e => [e.1,e.2])
    have hf : 2*i+1 < es.length := by simp [es,List.length_flatMap,Nat.mul_comm]; omega
    es[2*i]'(Nat.lt_succ_self _ |>.trans hf) = (edgeAt M i).1 ∧
      es[2*i+1]'hf = (edgeAt M i).2 := by
  induction M generalizing i with
  | nil => simp at hi
  | cons e M ih =>
    cases i with
    | zero => simp [edgeAt]
    | succ i =>
      have h : i < M.length := by simp at hi; omega
      have hh : 2*(i+1) = 2*i+1+1 := by omega
      simpa only [hh,List.flatMap_cons,List.cons_append,List.nil_append,List.getElem_cons_succ,
        edgeAt,List.getD_cons_succ] using ih h

/-- The connector writer preserves the router reply and records the actual
shortcut list for every matching edge. -/
theorem buildConnEraseProc_meetsContract {w d f fWalk : ℕ} {p : Program} {G : Graph}
    {M : List (ℕ × ℕ)} {emb : ℕ → List ℕ}
    (hf : p.procs[f]? = some (buildConnEraseProc fWalk))
    (hwk : MeetsContract w p fWalk (buildWalkRowContract w G (connectorWalkRow M emb))) :
    MeetsContract w p f (buildConnEraseContract w G M emb d) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨rep,top,ends,rfl,hReply,hRe,hZero,hRoom,hw,hRaw,hFits⟩ := hPre
  let R := connectorWalkRow M emb
  let s := M.length
  let mt := (matchedTableBases mem rep).1
  let tb := (matchedTableBases mem rep).2
  let src := mt+2
  let dir := top+2
  let vs := dir+s
  let P := vs+d+1
  let out := P+G.n
  have hSh : ([M] : List (List (ℕ × ℕ))).flatten.length = s := by simp [s]
  obtain ⟨hMT,hTB⟩ := routeMatched_view hReply
  obtain ⟨hMend,hTend⟩ := matchedTables_end_le hReply hRe
  have hSrc : ListAt mem src (matchingRowWords [M] 0) := by
    have hv := (matchingRow_view (by simp : 0 < ([M] : List (List (ℕ × ℕ))).length) hMT).2.2.2
    simpa [src,mt,matchedTableBases,flatIndex] using hv
  have hSrcEnd : src+2*s ≤ top := by
    change mt+(csrList 1 (matchingRowWords [M])).length ≤ top at hMend
    have hLen : (csrList 1 (matchingRowWords [M])).length = 2+2*s := by
      simp [csrList,csrData,List.range_succ,length_matchingRowWords,s]
    rw [hLen] at hMend
    dsimp [src]
    omega
  change tb + _ ≤ top at hTend
  have hRep4 : rep+4 ≤ mt := Nat.le_add_right .. 
  have hR4 : rep+4 < 2^w := by dsimp [src] at hSrcEnd; omega
  have hMt : mt < 2^w := by dsimp [src] at hSrcEnd; omega
  have hTb : tb < 2^w := by omega
  change rep+4+mem (rep+1) < 2^w at hMt
  change rep+4+mem (rep+2) < 2^w at hTb
  have hR1 : rep+1 < 2^w := by omega
  have hR2 : rep+2 < 2^w := by omega
  have hOne : 1 < 2^w := by omega
  have hTwo : 2 < 2^w := by omega
  have hSrcW : src < 2^w := by omega
  have hDir : dir < 2^w := by dsimp [dir]; omega
  have hVs : vs < 2^w := by dsimp [vs,dir,s]; omega
  have hPd : vs+d < 2^w := by dsimp [vs,dir,s]; omega
  have hP : P < 2^w := by dsimp [P,vs,dir,s]; omega
  have hOut : out < 2^w := hRoom
  have hTop1 : top+1 < 2^w := by omega
  let mid := Function.update (Function.update mem top src) (top+1) dir
  have hFrame (a : ℕ) (ha : a < top ∨ top+2 ≤ a) : mid a = mem a := by
    simp only [mid,Function.update_of_ne (show a ≠ top+1 by omega),
      Function.update_of_ne (show a ≠ top by omega)]
  have hPreWalk := hFits mid (fun a ha => hFrame a (Or.inl ha))
    (fun a ha => (hFrame a (Or.inr ha)).trans (hZero a (by omega)))
  refine runs_start_le ?_
  unfold buildConnEraseProc
  refine runs_seq_assign_le (v := rep+4) ?_ ?_
  · simp [Expr.eval,startState,hw,hR4]
  refine runs_seq_assign_le (v := mt) ?_ ?_
  · simp [Expr.eval,startState,Function.update,hOne,hR1,hMt,mt,matchedTableBases]
  refine runs_seq_assign_le (v := tb) ?_ ?_
  · simp [Expr.eval,startState,Function.update,hTwo,hR2,hTb,tb,matchedTableBases]
  refine runs_seq_assign_le (v := src) ?_ ?_
  · simp [Expr.eval,Function.update,hTwo,hSrcW,src]
  refine runs_seq_assign_le (v := dir) ?_ ?_
  · simp [Expr.eval,startState,Function.update,hTwo,hDir,dir]
  refine runs_seq_assign_le (v := vs) ?_ ?_
  · simp [Expr.eval,startState,Function.update,hVs,vs,s]
  refine runs_seq_assign_le (v := P) ?_ ?_
  · simp [Expr.eval,startState,Function.update,hOne,hPd,hP,P]
  refine runs_seq_store_le (x := top) (v := src)
    (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := top+1) (v := dir) ?_ (Expr.eval_reg_of_eq (by simp)) ?_
  · simp [Expr.eval,startState,Function.update,hOne,hTop1]
  refine runs_seq_call_le hwk (vs := [tb,s,0,src,ends,vs,P,dir,out,s]) ?_ ?_ hPreWalk ?_
  · simp [Expr.eval,evalArgs,startState,Function.update,hOut,out,s]
  · have hE := hWords ends (by simp)
    wram_words
  intro v after pos₂ hPost
  obtain ⟨tb₀,src₀,ends₀,vs₀,P₀,dir₀,out₀,he,hv,hZ,hKeep,hPositions,hAt⟩ := hPost
  simp only [connectorWalkRow,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,_,_,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := he
  have hOutV : out ≤ v := by
    rw [hv]
    exact R.cursor_mono _ (Nat.zero_le _)
  have hDirOut : dir+s ≤ out := by dsimp [out,P,vs]; omega
  have hBelow (a : ℕ) (ha : a < dir) : after a = mid a := hKeep a (Or.inl ha)
  have hCtxLo : after top = src := (hBelow _ (by dsimp [dir]; omega)).trans (by simp [mid])
  have hCtxHi : after (top+1) = dir := (hBelow _ (by dsimp [dir]; omega)).trans (by simp [mid])
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨rep,top,ends,rfl,hv,?_,
      fun a ha => (hBelow a (by dsimp [dir]; omega)).trans (hFrame a (Or.inl ha)),hPositions,hZ⟩
    change ConnectorRowsAt top M.length (edgeAt M)
      (fun i => erase G.edges (edgeAt M i).1 (emb i)) v after
    refine ⟨(Nat.le_add_right dir s).trans (hDirOut.trans hOutV),?_⟩
    change after top + 2*s ≤ v ∧ after (top+1)+s ≤ v ∧ _
    rw [hCtxLo,hCtxHi]
    refine ⟨hSrcEnd.trans ((Nat.le_add_right top 2).trans ((Nat.le_add_right dir s).trans (hDirOut.trans hOutV))),
      hDirOut.trans hOutV,?_⟩
    intro i hi
    have hEven : 2*i+1 < (matchingRowWords [M] 0).length := by
      rw [length_matchingRowWords]
      simpa using (show 2*i+1 < 2*M.length by omega)
    have hEven0 : 2*i < (matchingRowWords [M] 0).length := (Nat.lt_succ_self _).trans hEven
    have hWord₀ := hSrc (2*i) hEven0
    have hWord₁ := hSrc (2*i+1) hEven
    have he₀ : (matchingRowWords [M] 0)[2*i] = (edgeAt M i).1 := by
      exact (endpoints_get hi).1
    have he₁ : (matchingRowWords [M] 0)[2*i+1] = (edgeAt M i).2 := by
      exact (endpoints_get hi).2
    have hKeepSrc (a : ℕ) (ha : a < top) : after a = mem a :=
      (hBelow a (by dsimp [dir]; omega)).trans (hFrame a (Or.inl ha))
    have hC0 : src+2*i < top := by omega
    have hC1 : src+2*i+1 < top := by omega
    obtain ⟨hPtr,hWalk⟩ := hAt i hi
    refine ⟨(hKeepSrc _ hC0).trans (hWord₀.trans he₀),
      (hKeepSrc _ hC1).trans (by simpa [Nat.add_assoc] using hWord₁.trans he₁),?_⟩
    rw [hPtr]
    have hLen : (erase G.edges (edgeAt M i).1 (emb i)).length ≤ (emb i).length :=
      (erase_spec (emb i).length _ _ _ le_rfl (hRaw i hi)).2.1.length_le
    have hNext : R.cursor out i+1+(emb i).length = R.cursor out (i+1) := by
      simp [R,BuildWalkRow.cursor,BuildWalkRow.raw,connectorWalkRow]
    refine ⟨?_,by simpa [connectorWalkRow,BuildWalkRow.raw] using hWalk⟩
    rw [hv]
    exact (Nat.add_le_add_left hLen _).trans (hNext.le.trans (R.cursor_mono _ (Nat.succ_le_of_lt hi)))
  · simp [buildConnEraseContract,buildWalkRowContract,Expr.size,argsSize]
    omega

/-- A one-row reply with its declared walk bounds supplies the shortcut
writer's input and scratch conditions. -/
theorem buildConnErase_pre_of_matched {w Δ b L z d rep top ends : ℕ} {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {M : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {mem : ℕ → ℕ}
    (hValid : G.IsValid) (hX : X ⊆ Finset.range G.n) (hPairs : ValidTerminalPairs X pairs)
    (hMatch : RouteMatchedSpec G X pairs Δ L b z [M] emb)
    (hLength : routePathLen Δ b L ≤ d)
    (hReply : ListAt mem rep (routeResultWords (.matched [M] emb)))
    (hBelow : rep+(routeResultWords (.matched [M] emb)).length ≤ top)
    (hEndPts : ListAt mem ends (G.edges.flatMap fun e => [e.1,e.2])) (hEndPtsLe : ends+2*G.m ≤ top)
    (hZero : ZeroFrom mem top) (hBits : 4 < 2^w)
    (hWord : (connectorWalkRow M emb).cursor (top+2+M.length+d+1+G.n) M.length < 2^w) :
    (buildConnEraseContract w G M emb d).pre [rep,top,ends,G.n,d,M.length] mem := by
  let R := connectorWalkRow M emb
  let mt := (matchedTableBases mem rep).1
  let tb := (matchedTableBases mem rep).2
  let src := mt+2
  let dir := top+2
  let vs := dir+M.length
  let P := vs+d+1
  let out := P+G.n
  have hOut : out < 2^w := (R.cursor_mono out (Nat.zero_le _)).trans_lt hWord
  have hCanon (i : ℕ) (hi : i < M.length) :
      R.u i < G.n ∧ IsEdgeWalk G.edges (R.u i) (R.v i) (emb i) := by
    have hh := matchingWalkRow_correct (i := 0) hMatch hX hPairs (by simp)
      (show i < (([M] : List (List (ℕ × ℕ))).getD 0 []).length by simpa using hi)
    simpa [R,matchingWalkRow,connectorWalkRow,BuildWalkRow.raw,flatIndex] using hh
  refine ⟨rep,top,ends,rfl,hReply,hBelow,hZero,hOut,hBits,fun i hi => (hCanon i hi).2,?_⟩
  intro mid hFrame hZ
  obtain ⟨hMT,hTB⟩ := routeMatched_view hReply
  obtain ⟨hME,hTE⟩ := matchedTables_end_le hReply hBelow
  have hTab : ListAt mem tb (csrList R.total R.emb) := by
    simpa [R,connectorWalkRow,tb,matchedTableBases] using hTB
  have hSize : (csrList 1 (matchingRowWords [M])).length = 2+2*M.length := by
    simp [csrList,csrData,List.range_succ,length_matchingRowWords]
  have hSrcEnd : src+2*M.length ≤ top := by
    change mt+(csrList 1 (matchingRowWords [M])).length ≤ top at hME
    rw [hSize] at hME
    dsimp [src]
    omega
  have hTabEnd : tb+(csrList R.total R.emb).length ≤ top := by
    simpa [R,connectorWalkRow] using hTE
  have hSrc : ListAt mem src (matchingRowWords [M] 0) := by
    have hv := (matchingRow_view (by simp : 0 < ([M] : List (List (ℕ × ℕ))).length) hMT).2.2.2
    simpa [src,mt,matchedTableBases,flatIndex] using hv
  have hRaw (i : ℕ) (hi : i < R.count) : (R.raw i).length ≤ d := by
    have hh : i < ([M] : List (List (ℕ × ℕ))).flatten.length := by simpa [R,connectorWalkRow] using hi
    simpa [R,connectorWalkRow,BuildWalkRow.raw] using (hMatch.2.2.2.2.1 i hh).trans hLength
  have hFit : WalkRowFit w R G tb src ends vs P dir out := by
    refine ⟨by change 0+M.length ≤ M.length; simp,
      hTabEnd.trans (Nat.le_add_right ..),hSrcEnd.trans (Nat.le_add_right ..),
      hEndPtsLe.trans (Nat.le_add_right ..),le_rfl,?_,le_rfl,hWord,by omega⟩
    intro i hi
    have hh := hRaw i hi
    dsimp [P]
    omega
  refine ⟨tb,src,ends,vs,P,dir,out,rfl,hFit,hValid,
    WordRAM.ListAt.congr hTab (fun a _ ha => hFrame a (ha.trans_le hTabEnd)),
    WordRAM.ListAt.congr hEndPts (fun a _ ha => ?_),?_,
    fun a ha => hZ a (by dsimp [out,P,vs,dir] at ha; omega),
    fun a _ => hZ _ (by dsimp [P,vs,dir]; omega)⟩
  · have hLen : (G.edges.flatMap fun e => [e.1,e.2]).length = 2*G.m := by
      simp [Graph.m,List.length_flatMap,Nat.mul_comm]
    rw [hLen] at ha
    exact hFrame a (ha.trans_le hEndPtsLe)
  · intro i hi
    have hi' : i < M.length := hi
    have hIdx : 2*i < (matchingRowWords [M] 0).length := by
      rw [length_matchingRowWords]
      simpa using (show 2*i < 2*M.length by omega)
    have hCell := hSrc (2*i) hIdx
    have hVal : (matchingRowWords [M] 0)[2*i] = (edgeAt M i).1 := (endpoints_get hi').1
    exact ⟨(hFrame _ (by omega)).trans (hCell.trans hVal),
      by simpa [R,connectorWalkRow,BuildWalkRow.raw] using hCanon i hi'⟩

end MinCostFlow.HierPaths
