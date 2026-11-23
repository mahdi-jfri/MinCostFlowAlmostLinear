module

public import MinCostFlow.SparseCore.Program.ReadRecord
public import MinCostFlow.DynSpanner.Program.DynGraphDelete

import WordRAM.Tactic

/-!
# Two list loops of the update: removed forest edges and new roots

An update gets from P4 a change record (`LSFChangeAt`): the new roots and the forest edges that
leave the forest. The update applies the record with two loops:

* `delEdgesStmt` (`[gPtr, listPtr, n]`) deletes the `n` edges listed at `listPtr` from the graph
  at `gPtr`, skipping the edges that are not there (`delEdges_meetsContract`). The graph becomes
  `{ G with E := G.E \ l.toFinset }`.
* `setRootsStmt` (`[rootsPtr, listPtr, n]`) sets the root bit of each of the `n` vertices listed at
  `listPtr` (`setRoots_meetsContract`). The root set becomes `R ∪ l.toFinset`.

Each costs a constant per list entry.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## The procedures -/

/-- Delete the `n` edges listed at `listPtr` from the graph at `gPtr`: `[gPtr, listPtr, n]`. -/
def delEdgesStmt (bEdge : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
     .call 5 (bEdge + dgIdxDeleteEdge) [.reg 0, .reg 4]) ;;
  .ret (.const 0)

/-- Set the root bits of the `n` vertices listed at `listPtr`: `[rootsPtr, listPtr, n]`. -/
def setRootsStmt : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
     .store (.bin .add (.reg 0) (.reg 4)) (.const 1)) ;;
  .ret (.const 0)

/-- Index of `delEdgesStmt` in `readLoopProcs`. -/
def readIdxDelEdges : ℕ := 0
/-- Index of `setRootsStmt` in `readLoopProcs`. -/
def readIdxSetRoots : ℕ := 1

/-- The two loops, with the edge procedures of the graph library at `bEdge`. -/
def readLoopProcs (bEdge : ℕ) : List Stmt := [delEdgesStmt bEdge, setRootsStmt]

/-- The loops use no random bits. -/
theorem readLoopProcs_noRand (bEdge : ℕ) : ∀ s ∈ readLoopProcs bEdge, s.NoRand := by
  intro s hs
  simp only [readLoopProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> simp [delEdgesStmt, setRootsStmt, forRange, forUp, Stmt.NoRand]

/-! ## The model of the loops -/

/-- One deletion of `dgDeleteEdge`: the edge leaves the edge set if it is there. -/
def delEdgeStep (G : MGraph) (e : ℕ) : MGraph :=
  if e ∈ G.E then G.applyUpdate (.delete e) else G

/-- A deletion step erases the edge from the edge set, whether or not it is there. -/
theorem delEdgeStep_eq (G : MGraph) (e : ℕ) : delEdgeStep G e = { G with E := G.E.erase e } := by
  unfold delEdgeStep
  split_ifs with h
  · rfl
  · rw [Finset.erase_eq_of_notMem h]

/-- Deleting the edges of a list one by one removes the listed edges. -/
theorem foldl_delEdgeStep (l : List ℕ) (G : MGraph) :
    l.foldl delEdgeStep G = { G with E := G.E \ l.toFinset } := by
  induction l generalizing G with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih, delEdgeStep_eq]
    congr 1
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
    tauto

/-- Setting the bit of a vertex below `vCap` adds it to the root set. -/
theorem RootsAt.set {mem : ℕ → ℕ} {a vCap u : ℕ} {R : Finset ℕ} (hR : RootsAt mem a vCap R)
    (hu : u < vCap) : RootsAt (Function.update mem (a + u) 1) a vCap (insert u R) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · exact hR.1 x hx
  · by_cases hxu : x = u
    · subst hxu
      exact Or.inl ⟨Finset.mem_insert_self _ _, by simp⟩
    · rw [Function.update_of_ne (by omega)]
      rcases hR.2 x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Finset.mem_insert_of_mem h1, h2⟩
      · exact Or.inr ⟨by simp [hxu, h1], h2⟩

/-! ## Contracts -/

/-- Contract of `delEdgesStmt` for the graph `G` and the list `l`: the list is outside the graph
block, and its entries are words. -/
def delEdgesContract (w vCap eCap : ℕ) (G : MGraph) (l : List ℕ) : Contract where
  pre args mem := ∃ gPtr listPtr, args = [gPtr, listPtr, l.length] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ listPtr + l.length < 2 ^ w ∧
    ListAt mem listPtr l ∧ (∀ e ∈ l, e < 2 ^ w) ∧
    (∀ i < l.length, listPtr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ listPtr + i) ∧
    DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr listPtr, args = [gPtr, listPtr, l.length] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap { G with E := G.E \ l.toFinset } ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost _ _ := 490 * l.length + 20

/-- Contract of `setRootsStmt` for the root set `R` and the list `l` of vertices below `vCap`: the
list is outside the bit table. -/
def setRootsContract (w vCap : ℕ) (R : Finset ℕ) (l : List ℕ) : Contract where
  pre args mem := ∃ rootsPtr listPtr, args = [rootsPtr, listPtr, l.length] ∧
    16 ≤ 2 ^ w ∧ rootsPtr + vCap < 2 ^ w ∧ listPtr + l.length < 2 ^ w ∧
    ListAt mem listPtr l ∧ (∀ u ∈ l, u < vCap) ∧
    (∀ i < l.length, listPtr + i < rootsPtr ∨ rootsPtr + vCap ≤ listPtr + i) ∧
    RootsAt mem rootsPtr vCap R
  post args mem ret mem' := ∃ rootsPtr listPtr, args = [rootsPtr, listPtr, l.length] ∧ ret = 0 ∧
    RootsAt mem' rootsPtr vCap (R ∪ l.toFinset) ∧
    ∀ addr, addr < rootsPtr ∨ rootsPtr + vCap ≤ addr → mem' addr = mem addr
  cost _ _ := 30 * l.length + 20

/-! ## Proofs -/

/-- `delEdgesStmt` meets `delEdgesContract`. -/
theorem delEdges_meetsContract {w : ℕ} {p : Program} {b bEdge bOps vCap eCap : ℕ} {G : MGraph}
    {l : List ℕ} (hp : p.HasAt b (readLoopProcs bEdge)) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + readIdxDelEdges) (delEdgesContract w vCap eCap G l) := by
  refine meetsContract_of_runs
    (hp.get (i := readIdxDelEdges) (by simp [readLoopProcs, readIdxDelEdges])) ?_
  rintro args mem pos ω hargs ⟨gPtr, listPtr, rfl, hw16, hbound, hlistB, hlist, hlw, hdisj, hG⟩
  simp only [readLoopProcs, readIdxDelEdges, List.getElem_cons_zero]
  have hn : l.length < 2 ^ w := hargs _ (by simp)
  have hg : gPtr < 2 ^ w := hargs _ (by simp)
  have hlp : listPtr < 2 ^ w := hargs _ (by simp)
  let frame : (ℕ → ℕ) → Prop := fun m =>
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → m addr = mem addr
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = gPtr ∧ st.regs 1 = listPtr ∧ st.regs 2 = l.length ∧ st.regs 3 = k ∧
    DynGraphAt st.mem gPtr vCap eCap ((l.take k).foldl delEdgeStep G) ∧ frame st.mem
  let body : Stmt :=
    .assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
    .call 5 (bEdge + dgIdxDeleteEdge) [.reg 0, .reg 4]
  have hLoop : Triple w p (fun st => st = startState [gPtr, listPtr, l.length] mem pos)
      (forRange 3 (.const 0) (.reg 2) body) (normalPost (Inv l.length))
      (fun _ => (l.length - 0) * (480 + Expr.size (.reg 2) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 2) + 5)) := by
    refine Triple.forRange_const 480 0 l.length (Nat.zero_le _) (by omega) (fun _ => hn)
      (fun st hst => by
        subst hst
        refine ⟨Expr.eval_const (by omega), ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
        · simp [startState]
        · simp [startState]
        · simp [startState]
        · simp
        · simpa [startState] using hG)
      (fun k st _ _ hk => hk.2.2.2.1)
      (fun k st _ _ hk => by simp [Expr.eval, hk.2.2.1])
      (fun k _ hk st ω' hInv => by
        obtain ⟨hr0, hr1, hr2, hr3, hGk, hfr⟩ := hInv
        have hval : st.mem (listPtr + k) = l[k] := by
          rw [hfr _ (hdisj k hk)]; exact hlist k hk
        have hlk : l[k] < 2 ^ w := hlw _ (List.getElem_mem hk)
        apply runs_start_le
        refine runs_seq_assign_le (v := l[k]) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr3) (by omega)) hval) ?_
        refine runs_call_le (dgDeleteEdge_meetsContract (G := (l.take k).foldl delEdgeStep G)
          (vCap := vCap) (eCap := eCap) hpEdge hpOps)
          (vs := [gPtr, l[k]]) (by simp [evalArgs, Expr.eval, hr0])
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl | rfl) <;> omega)
          ⟨gPtr, l[k], rfl, hw16, hbound, hGk⟩ ?_
        rintro v mem' pos' ⟨_, _, hEq, _, hG', hfr'⟩
        simp only [List.cons.injEq, and_true] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · simp [Function.update_of_ne, hr0]
        · simp [Function.update_of_ne, hr1]
        · simp [Function.update_of_ne, hr2]
        · simp
        · rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
          exact hG'
        · exact fun addr ha => (hfr' addr ha).trans (hfr addr ha)
        · simp [Function.update_of_ne, hr3]
        · simp only [dgDeleteEdgeContract, argsSize, Expr.size] at *
          omega)
  apply runs_start_le
  refine runs_seq_triple_le hLoop rfl ?_
  rintro st ⟨hr0, hr1, hr2, hr3, hGn, hfr⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨gPtr, listPtr, rfl, rfl, ?_, hfr⟩ ?_
  · rw [List.take_of_length_le (le_refl _), foldl_delEdgeStep] at hGn
    exact hGn
  · simp only [delEdgesContract, Expr.size]
    omega

/-- `setRootsStmt` meets `setRootsContract`. -/
theorem setRoots_meetsContract {w : ℕ} {p : Program} {b bEdge vCap : ℕ} {R : Finset ℕ}
    {l : List ℕ} (hp : p.HasAt b (readLoopProcs bEdge)) :
    MeetsContract w p (b + readIdxSetRoots) (setRootsContract w vCap R l) := by
  refine meetsContract_of_runs
    (hp.get (i := readIdxSetRoots) (by simp [readLoopProcs, readIdxSetRoots])) ?_
  rintro args mem pos ω hargs ⟨rootsPtr, listPtr, rfl, hw16, hbound, hlistB, hlist, hlv, hdisj, hR⟩
  simp only [readLoopProcs, readIdxSetRoots, List.getElem_cons_succ, List.getElem_cons_zero]
  have hn : l.length < 2 ^ w := hargs _ (by simp)
  have hlp : listPtr < 2 ^ w := hargs _ (by simp)
  let frame : (ℕ → ℕ) → Prop := fun m =>
    ∀ addr, addr < rootsPtr ∨ rootsPtr + vCap ≤ addr → m addr = mem addr
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = rootsPtr ∧ st.regs 1 = listPtr ∧ st.regs 2 = l.length ∧ st.regs 3 = k ∧
    RootsAt st.mem rootsPtr vCap (R ∪ (l.take k).toFinset) ∧ frame st.mem
  let body : Stmt :=
    .assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
    .store (.bin .add (.reg 0) (.reg 4)) (.const 1)
  have hLoop : Triple w p (fun st => st = startState [rootsPtr, listPtr, l.length] mem pos)
      (forRange 3 (.const 0) (.reg 2) body) (normalPost (Inv l.length))
      (fun _ => (l.length - 0) * (20 + Expr.size (.reg 2) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 2) + 5)) := by
    refine Triple.forRange_const 20 0 l.length (Nat.zero_le _) (by omega) (fun _ => hn)
      (fun st hst => by
        subst hst
        refine ⟨Expr.eval_const (by omega), ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
        · simp [startState]
        · simp [startState]
        · simp [startState]
        · simp
        · simpa [startState] using hR)
      (fun k st _ _ hk => hk.2.2.2.1)
      (fun k st _ _ hk => by simp [Expr.eval, hk.2.2.1])
      (fun k _ hk st ω' hInv => by
        obtain ⟨hr0, hr1, hr2, hr3, hRk, hfr⟩ := hInv
        have hval : st.mem (listPtr + k) = l[k] := by
          rw [hfr _ (hdisj k hk)]; exact hlist k hk
        have hlk : l[k] < vCap := hlv _ (List.getElem_mem hk)
        apply runs_start_le
        refine runs_seq_assign_le (v := l[k]) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr3) (by omega)) hval) ?_
        refine runs_store_le (x := rootsPtr + l[k]) (v := 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
            (Expr.eval_reg_of_eq (by simp)) (by omega)) (Expr.eval_const (by omega)) ?_ ?_
        · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simp [Function.update_of_ne, hr0]
          · simp [Function.update_of_ne, hr1]
          · simp [Function.update_of_ne, hr2]
          · simp
          · have := RootsAt.set hRk hlk
            rw [List.take_succ_eq_append_getElem hk, List.toFinset_append]
            convert this using 1
            ext x
            simp only [Finset.mem_union, List.mem_toFinset, List.mem_singleton, Finset.mem_insert]
            tauto
          · intro addr ha
            have hne : addr ≠ rootsPtr + l[k] := by rcases ha with ha | ha <;> omega
            show Function.update st.mem (rootsPtr + l[k]) 1 addr = mem addr
            rw [Function.update_of_ne hne]
            exact hfr addr ha
          · simp [Function.update_of_ne, hr3]
        · simp only [Expr.size]
          omega)
  apply runs_start_le
  refine runs_seq_triple_le hLoop rfl ?_
  rintro st ⟨hr0, hr1, hr2, hr3, hRn, hfr⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨rootsPtr, listPtr, rfl, rfl, ?_, hfr⟩ ?_
  · rw [List.take_of_length_le (le_refl _)] at hRn
    exact hRn
  · simp only [setRootsContract, Expr.size]
    omega

end MinCostFlow.SparseCore.Program.Read
