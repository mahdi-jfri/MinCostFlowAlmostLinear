module

public import MinCostFlow.LSF.Program.InitTreeLSSTOpsBase
import Mathlib.Tactic.Linarith

/-!
# The tracker graph of the `T` block

The `T` block (`TBlockAt`) keeps, for the `i`-th edge `f` of `T₀`, two self-loops in a dynamic
graph `dgT`: edge `2 i` sits at the current tail of `f` and edge `2 i + 1` at its current head.
When a vertex is split, the dynamic graph moves these loops with the edges of `G` at that end,
so the loops follow the ends of the tree edges. A bridge edge of `T₀` is not an edge of `G`, so
it gets no loops (its ends are kept in the frozen arrays instead).

At the start the first `nOrig` edges of `T₀` are edges of `G₀` and the others are bridges
(`t0EdgesProc` writes them in this order). `tTrackProc` builds `dgT`: an empty graph, the
vertices of `vList`, and for each `i < nOrig` the loops `2 i` and `2 i + 1` at the vertices
`vList[tTail[i]]` and `vList[tHead[i]]`. The result is `tTrackGraph` (`tTrack_meetsContract`),
at cost `O(n0 + nOrig)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## The procedure -/

/-- Args: `[dgTPtr, vCap, eCapT, n0, vListPtr, nOrig, tTailPtr, tHeadPtr]`. -/
def tTrackProc (bDg : ℕ) : Stmt :=
  .call 8 (bDg + dgIdxInitEmpty) [.reg 0, .reg 1, .reg 2] ;;
  forRange 8 (.const 0) (.reg 3)
    (.assign 9 (.load (.bin .add (.reg 4) (.reg 8))) ;;
     .call 10 (bDg + dgIdxAddVertex) [.reg 0, .reg 9]) ;;
  forRange 8 (.const 0) (.reg 5)
    (.assign 9 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 8))))) ;;
     .assign 11 (.bin .add (.reg 8) (.reg 8)) ;;
     .call 10 (bDg + 7 + dgIdxInsertEdge) [.reg 0, .reg 11, .reg 9, .reg 9] ;;
     .assign 9 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 8))))) ;;
     .call 10 (bDg + 7 + dgIdxInsertEdge)
       [.reg 0, .bin .add (.reg 11) (.const 1), .reg 9, .reg 9]) ;;
  .ret (.const 0)

lemma tTrackProc_noRand (bDg : ℕ) : (tTrackProc bDg).NoRand := by
  simp [tTrackProc, forRange, forUp, Stmt.NoRand]

/-- The vertex of the loop `k`: the tail of tree edge `k / 2` for even `k`, the head for odd
`k`, read through the index arrays. -/
def trackEnd (mem : ℕ → ℕ) (vListPtr tTailPtr tHeadPtr k : ℕ) : ℕ :=
  if k % 2 = 0 then mem (vListPtr + mem (tTailPtr + k / 2))
  else mem (vListPtr + mem (tHeadPtr + k / 2))

/-- The graph with vertex set `V` and the loops `0, …, k - 1`, loop `e` at `f e`. -/
def tTrackGraph (V : Finset ℕ) (f : ℕ → ℕ) (k : ℕ) : MGraph where
  V := V
  E := Finset.range k
  tail e := if e < k then f e else 0
  head e := if e < k then f e else 0

lemma tTrackGraph_succ (V : Finset ℕ) (f : ℕ → ℕ) (k : ℕ) :
    (tTrackGraph V f k).applyUpdate (.insert k (f k) (f k)) = tTrackGraph V f (k + 1) := by
  have hfun : Function.update (fun e => if e < k then f e else 0) k (f k) =
      fun e => if e < k + 1 then f e else 0 := by
    funext e
    by_cases hek : e = k
    · subst hek; simp
    · rw [Function.update_of_ne hek]
      by_cases hlt : e < k
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
  simp only [MGraph.applyUpdate, tTrackGraph, hfun, Finset.range_add_one]

/-- The graph with the first `i` vertices of `vList` and no edges. -/
def tVGraph (vList : List ℕ) (i : ℕ) : MGraph where
  V := (vList.take i).toFinset
  E := ∅
  tail _ := 0
  head _ := 0

lemma tVGraph_succ {vList : List ℕ} {i : ℕ} (hi : i < vList.length) :
    ({ tVGraph vList i with V := insert vList[i] (tVGraph vList i).V } : MGraph) =
      tVGraph vList (i + 1) := by
  simp only [tVGraph]
  congr 1
  rw [List.take_succ_eq_append_getElem hi, List.toFinset_append, List.toFinset_cons,
    List.toFinset_nil, insert_empty_eq, Finset.union_comm]
  rfl

/-- The contract of `tTrackProc`. The arrays it reads lie outside the graph block. -/
def tTrackContract (w : ℕ) : Contract where
  pre args mem := ∃ (dgTPtr vCap eCapT n0 vListPtr nOrig tTailPtr tHeadPtr : ℕ),
    args = [dgTPtr, vCap, eCapT, n0, vListPtr, nOrig, tTailPtr, tHeadPtr] ∧
    16 ≤ 2 ^ w ∧ dgTPtr + dynGraphSize vCap eCapT < 2 ^ w ∧ 2 * nOrig ≤ eCapT ∧
    (∀ i < dynGraphSize vCap eCapT, mem (dgTPtr + i) = 0) ∧
    (vListPtr + n0 ≤ dgTPtr ∨ dgTPtr + dynGraphSize vCap eCapT ≤ vListPtr) ∧
    vListPtr + n0 < 2 ^ w ∧
    (tTailPtr + nOrig ≤ dgTPtr ∨ dgTPtr + dynGraphSize vCap eCapT ≤ tTailPtr) ∧
    tTailPtr + nOrig < 2 ^ w ∧
    (tHeadPtr + nOrig ≤ dgTPtr ∨ dgTPtr + dynGraphSize vCap eCapT ≤ tHeadPtr) ∧
    tHeadPtr + nOrig < 2 ^ w ∧
    (∀ i < n0, mem (vListPtr + i) < vCap) ∧
    (∀ i < nOrig, mem (tTailPtr + i) < n0 ∧ mem (tHeadPtr + i) < n0)
  post args mem ret mem' := ∃ (dgTPtr vCap eCapT n0 vListPtr nOrig tTailPtr tHeadPtr : ℕ),
    args = [dgTPtr, vCap, eCapT, n0, vListPtr, nOrig, tTailPtr, tHeadPtr] ∧ ret = 0 ∧
    DynGraphAt mem' dgTPtr vCap eCapT
      (tTrackGraph ((memSlice mem vListPtr n0).toFinset)
        (trackEnd mem vListPtr tTailPtr tHeadPtr) (2 * nOrig)) ∧
    ∀ a, a < dgTPtr ∨ dgTPtr + dynGraphSize vCap eCapT ≤ a → mem' a = mem a
  cost args _ := 150 * args.getD 3 0 + 1000 * args.getD 5 0 + 100

lemma tVGraph_full {vList : List ℕ} (f : ℕ → ℕ) :
    tVGraph vList vList.length = tTrackGraph vList.toFinset f 0 := by
  simp only [tVGraph, tTrackGraph, List.take_length, Finset.range_zero, Nat.not_lt_zero,
    if_false]

/-! ## Proof -/

set_option maxHeartbeats 800000 in
theorem tTrack_meetsContract {w : ℕ} {p : Program} {b bDg : ℕ}
    (hp : p.procs[b]? = some (tTrackProc bDg)) (hpDg : p.HasAt bDg (dgRelocProcs bDg)) :
    MeetsContract w p b (tTrackContract w) := by
  have hpOps : p.HasAt bDg dgOpsProcs := dgReloc_hasAt_ops hpDg
  have hpEdge : p.HasAt (bDg + 7) (dgEdgeProcs bDg) := dgReloc_hasAt_edge hpDg
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨dgTPtr, vCap, eCapT, n0, vListPtr, nOrig, tTailPtr, tHeadPtr, rfl, h16, hbd, h2n,
    hzero, hvD, hvW, htD, htW, hhD, hhW, hvC, hidx⟩ := hpre
  set args := [dgTPtr, vCap, eCapT, n0, vListPtr, nOrig, tTailPtr, tHeadPtr] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hdw : dgTPtr < 2 ^ w := hwords _ (by simp [hargs])
  have hvCw : vCap < 2 ^ w := hwords _ (by simp [hargs])
  have heCw : eCapT < 2 ^ w := hwords _ (by simp [hargs])
  have hn0w : n0 < 2 ^ w := hwords _ (by simp [hargs])
  have hnOw : nOrig < 2 ^ w := hwords _ (by simp [hargs])
  set vs := memSlice mem vListPtr n0 with hvs
  set f := trackEnd mem vListPtr tTailPtr tHeadPtr with hf
  have hvslen : vs.length = n0 := memSlice_length _ _ _
  have hvsget : ∀ i (hi : i < vs.length), vs[i] = mem (vListPtr + i) := fun i hi =>
    memSlice_getElem _ _ _ _ hi
  have hvsmem : ∀ i < n0, mem (vListPtr + i) ∈ vs.toFinset := fun i hi => by
    rw [List.mem_toFinset, ← hvsget i (by omega)]; exact List.getElem_mem _
  let Fr : (ℕ → ℕ) → Prop := fun m =>
    ∀ a, a < dgTPtr ∨ dgTPtr + dynGraphSize vCap eCapT ≤ a → m a = mem a
  let Rg : State → Prop := fun st => ∀ i < 8, st.regs i = args.getD i 0
  -- reading the input arrays, which lie outside the graph block
  have hvR : ∀ m, Fr m → ∀ i < n0, m (vListPtr + i) = mem (vListPtr + i) := fun m hm i hi =>
    hm _ (by rcases hvD with h | h <;> [left; right] <;> omega)
  have htR : ∀ m, Fr m → ∀ i < nOrig, m (tTailPtr + i) = mem (tTailPtr + i) := fun m hm i hi =>
    hm _ (by rcases htD with h | h <;> [left; right] <;> omega)
  have hhR : ∀ m, Fr m → ∀ i < nOrig, m (tHeadPtr + i) = mem (tHeadPtr + i) := fun m hm i hi =>
    hm _ (by rcases hhD with h | h <;> [left; right] <;> omega)
  -- the vertex loop
  let InvV : ℕ → State → Prop := fun i st =>
    Rg st ∧ st.regs 8 = i ∧ DynGraphAt st.mem dgTPtr vCap eCapT (tVGraph vs i) ∧ Fr st.mem
  have hloopV : Triple w p
      (fun st => Rg st ∧ DynGraphAt st.mem dgTPtr vCap eCapT (tVGraph vs 0) ∧ Fr st.mem)
      (forRange 8 (.const 0) (.reg 3)
        (.assign 9 (.load (.bin .add (.reg 4) (.reg 8))) ;;
         .call 10 (bDg + dgIdxAddVertex) [.reg 0, .reg 9]))
      (normalPost (InvV n0))
      (fun _ => (n0 - 0) * (130 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.forRange_const 130 0 n0 (Nat.zero_le _) hw1 (fun _ => hn0w) ?_ ?_ ?_ ?_
    · rintro st ⟨hR, hdg, hfr⟩
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hdg, hfr⟩
      simp only [Function.update_of_ne (show i ≠ 8 by omega)]; exact hR i hi
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have r3 : st.regs 3 = n0 := h.1 3 (by omega)
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨hR, h8, hdg, hfr⟩ := hI
      have r0 : st.regs 0 = dgTPtr := hR 0 (by omega)
      have r4 : st.regs 4 = vListPtr := hR 4 (by omega)
      have hvi : st.mem (vListPtr + i) = mem (vListPtr + i) := hvR _ hfr i hi
      have hlen : i < vs.length := by omega
      have hxw : mem (vListPtr + i) < 2 ^ w := lt_trans (hvC i hi) hvCw
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := mem (vListPtr + i)) (by rw [← hvi]; eval_expr) ?_
      refine runs_call_le (vs := [dgTPtr, mem (vListPtr + i)])
        (dgAddVertex_meetsContract (G := tVGraph vs i) hpOps)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> assumption)
        ⟨dgTPtr, _, rfl, h16, hbd, hvC i hi, hdg⟩ ?_
      rintro v₂ mem₂ pos₂ ⟨g₂, x₂, heq₂, -, hdg₂, hfr₂⟩
      simp only [List.cons.injEq, and_true] at heq₂
      obtain ⟨rfl, rfl⟩ := heq₂
      refine ⟨⟨⟨fun k hk => ?_, by simp, ?_, fun a ha => ?_⟩, by simpa using h8⟩, ?_⟩
      · simp only [Function.update_of_ne (show k ≠ 8 by omega),
          Function.update_of_ne (show k ≠ 10 by omega), Function.update_of_ne (show k ≠ 9 by omega)]
        exact hR k hk
      · rw [← tVGraph_succ hlen, hvsget i hlen]; exact hdg₂
      · show mem₂ a = mem a
        rw [hfr₂ a ha]; exact hfr a ha
      · simp [argsSize, Expr.size, dgAddVertexContract]
  -- the loop over the tree edges of `G₀`
  let InvE : ℕ → State → Prop := fun i st =>
    Rg st ∧ st.regs 8 = i ∧
      DynGraphAt st.mem dgTPtr vCap eCapT (tTrackGraph vs.toFinset f (2 * i)) ∧ Fr st.mem
  have hloopE : Triple w p
      (fun st => Rg st ∧ DynGraphAt st.mem dgTPtr vCap eCapT (tTrackGraph vs.toFinset f (2 * 0)) ∧
        Fr st.mem)
      (forRange 8 (.const 0) (.reg 5)
        (.assign 9 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 8))))) ;;
         .assign 11 (.bin .add (.reg 8) (.reg 8)) ;;
         .call 10 (bDg + 7 + dgIdxInsertEdge) [.reg 0, .reg 11, .reg 9, .reg 9] ;;
         .assign 9 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 8))))) ;;
         .call 10 (bDg + 7 + dgIdxInsertEdge)
           [.reg 0, .bin .add (.reg 11) (.const 1), .reg 9, .reg 9]))
      (normalPost (InvE nOrig))
      (fun _ => (nOrig - 0) * (950 + (Expr.reg 5).size + 8) +
        ((Expr.const 0).size + (Expr.reg 5).size + 5)) := by
    refine Triple.forRange_const 950 0 nOrig (Nat.zero_le _) hw1 (fun _ => hnOw) ?_ ?_ ?_ ?_
    · rintro st ⟨hR, hdg, hfr⟩
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hdg, hfr⟩
      simp only [Function.update_of_ne (show i ≠ 8 by omega)]; exact hR i hi
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have r5 : st.regs 5 = nOrig := h.1 5 (by omega)
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨hR, h8, hdg, hfr⟩ := hI
      have r0 : st.regs 0 = dgTPtr := hR 0 (by omega)
      have r4 : st.regs 4 = vListPtr := hR 4 (by omega)
      have r6 : st.regs 6 = tTailPtr := hR 6 (by omega)
      have r7 : st.regs 7 = tHeadPtr := hR 7 (by omega)
      obtain ⟨hti, hhi⟩ := hidx i hi
      have hT1 : st.mem (tTailPtr + i) = mem (tTailPtr + i) := htR _ hfr i hi
      have hx : st.mem (vListPtr + st.mem (tTailPtr + i)) = f (2 * i) := by
        rw [hT1, hvR _ hfr _ hti, hf]
        simp only [trackEnd, Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left _ two_pos]
      have hxV : f (2 * i) ∈ vs.toFinset := by
        rw [← hx, hT1, hvR _ hfr _ hti]; exact hvsmem _ hti
      have hxw : f (2 * i) < 2 ^ w := by
        rw [← hx, hT1, hvR _ hfr _ hti]; exact lt_trans (hvC _ hti) hvCw
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := f (2 * i)) (by rw [← hx]; eval_expr) ?_
      refine runs_seq_assign_le (v := 2 * i) (by rw [show 2 * i = i + i by omega]; eval_expr) ?_
      refine runs_seq_call_le (vs := [dgTPtr, 2 * i, f (2 * i), f (2 * i)])
        (dgInsertEdge_meetsContract (G := tTrackGraph vs.toFinset f (2 * i)) hpEdge hpOps)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> omega)
        ⟨dgTPtr, _, _, _, rfl, h16, hbd, hxV, hxV, hdg⟩ ?_
      rintro v₃ mem₃ pos₃ ⟨g₃, e₃, u₃, x₃, heq₃, -, hdg₃, hfr₃⟩
      simp only [List.cons.injEq, and_true] at heq₃
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₃
      rw [if_pos ⟨by omega, by simp [tTrackGraph]⟩, tTrackGraph_succ] at hdg₃
      have hfr₃' : Fr mem₃ := fun a ha => by rw [hfr₃ a ha]; exact hfr a ha
      have hH1 : mem₃ (tHeadPtr + i) = mem (tHeadPtr + i) := hhR _ hfr₃' i hi
      have hy : mem₃ (vListPtr + mem₃ (tHeadPtr + i)) = f (2 * i + 1) := by
        rw [hH1, hvR _ hfr₃' _ hhi, hf]
        have h1 : (2 * i + 1) % 2 = 1 := by omega
        have h2 : (2 * i + 1) / 2 = i := by omega
        simp only [trackEnd, h1, h2, one_ne_zero, if_false]
      have hyV : f (2 * i + 1) ∈ vs.toFinset := by
        rw [← hy, hH1, hvR _ hfr₃' _ hhi]; exact hvsmem _ hhi
      have hyw : f (2 * i + 1) < 2 ^ w := by
        rw [← hy, hH1, hvR _ hfr₃' _ hhi]; exact lt_trans (hvC _ hhi) hvCw
      refine runs_seq_assign_le (v := f (2 * i + 1)) (by rw [← hy]; eval_expr) ?_
      refine runs_call_le (vs := [dgTPtr, 2 * i + 1, f (2 * i + 1), f (2 * i + 1)])
        (dgInsertEdge_meetsContract (G := tTrackGraph vs.toFinset f (2 * i + 1)) hpEdge hpOps)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> omega)
        ⟨dgTPtr, _, _, _, rfl, h16, hbd, hyV, hyV, hdg₃⟩ ?_
      rintro v₄ mem₄ pos₄ ⟨g₄, e₄, u₄, x₄, heq₄, -, hdg₄, hfr₄⟩
      simp only [List.cons.injEq, and_true] at heq₄
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₄
      rw [if_pos ⟨by omega, by simp [tTrackGraph]⟩, tTrackGraph_succ,
        show 2 * i + 1 + 1 = 2 * (i + 1) by ring] at hdg₄
      refine ⟨⟨⟨fun k hk => ?_, by simp, hdg₄, fun a ha => ?_⟩, by simpa using h8⟩, ?_⟩
      · simp only [Function.update_of_ne (show k ≠ 8 by omega),
          Function.update_of_ne (show k ≠ 10 by omega), Function.update_of_ne (show k ≠ 9 by omega),
          Function.update_of_ne (show k ≠ 11 by omega)]
        exact hR k hk
      · show mem₄ a = mem a
        rw [hfr₄ a ha]; exact hfr₃' a ha
      · simp [argsSize, Expr.size, dgInsertEdgeContract]
  -- the run
  refine runs_start_le ?_
  unfold tTrackProc
  refine runs_seq_call_le (vs := [dgTPtr, vCap, eCapT]) (dgInitEmptyLocal_meetsContract hpOps)
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    ⟨dgTPtr, vCap, eCapT, rfl, h16, hbd, hzero⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨g₁, vc₁, ec₁, heq₁, -, hdg₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  refine runs_seq_triple_le hloopV ⟨fun i hi => ?_, ?_, fun a ha => ?_⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 8 by omega)]
    interval_cases i <;> simp [startState, hargs]
  · have h0 : tVGraph vs 0 = { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 } := by
      simp [tVGraph]
    rw [h0]; exact hdg₁
  · refine hfr₁ a ?_
    rcases ha with ha | ha
    · left; exact ha
    · right; simp only [dynGraphSize] at ha; omega
  rintro st₂ ⟨hR₂, -, hdg₂, hfr₂⟩
  have hP2 : Rg st₂ ∧ DynGraphAt st₂.mem dgTPtr vCap eCapT (tTrackGraph vs.toFinset f (2 * 0)) ∧
      Fr st₂.mem := by
    refine ⟨hR₂, ?_, hfr₂⟩
    rw [Nat.mul_zero, ← tVGraph_full, hvslen]; exact hdg₂
  refine runs_seq_triple_le hloopE hP2 ?_
  rintro st₃ ⟨-, -, hdg₃, hfr₃⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨dgTPtr, vCap, eCapT, n0, vListPtr, nOrig, tTailPtr,
    tHeadPtr, rfl, rfl, hdg₃, hfr₃⟩ ?_
  simp only [tTrackContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg, Nat.sub_zero, dgInitEmptyLocalContract, argsSize]
  omega

end

end MinCostFlow.LSF.Program
