module

public import MinCostFlow.SparseCore.Program.CompContract
import MinCostFlow.SparseCore.CompLSFBridge
import WordRAM.Tactic

/-!
# Readout Procedures (`op 1`..`op 5`) for Per-Component Dynamic LSF (`CompReadout`)

Implements and verifies the five `O(1)`-time deterministic (`NoRand`) readout operations of
`compLSFDS`:

* `op 1` (`compVertCompProc`): vertex component index, edgeful flag, and initial `(n_C, m_C)`.
* `op 2` (`compWindowHandleProc`): handle `hWin` of the LSF window for edgeful component `c` and
  branch `j`.
* `op 3` (`compRootProc`): forest root `RF.root v` in branch `j` (`v` directly for isolated
  components, `compRoot[compId[v]]` inside the window for edgeful components).
* `op 4` (`compEdgeInfoProc`): `isCross`, `isIns`, and exact rational `wstrGlobal e` pointers
  (`oneLimb` for inserted/cross/isolated edges, window `(wstrNum, wstrDen)` for surviving edges).
* `op 5` (`compInfoProc`): global header readout `(numComps, numEdgeful, k, vCap, eCap, L_w)`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Procedure bodies -/

def compReadoutIdxVert : ℕ := 0
def compReadoutIdxWinHandle : ℕ := 1
def compReadoutIdxRoot : ℕ := 2
def compReadoutIdxEdge : ℕ := 3
def compReadoutIdxInfo : ℕ := 4

/-- `op 1`: `args = [b, v, heap]`. Writes `(c, isEdgeful, n0_c, m0_c)` at `[heap, heap + 4)`. -/
def compVertCompProc : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const compOffVCompPtr))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffN0Ptr))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffM0Ptr))) ;;
  .assign 7 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .store (.reg 2) (.reg 7) ;;
  .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 8) ;;
  .assign 8 (.load (.bin .add (.reg 5) (.reg 7))) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.reg 8) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.reg 7))) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 8) ;;
  .ret (.bin .add (.reg 2) (.const 4))

/-- `op 2`: `args = [b, c, j, heap]`. Writes window handle `hWin` at `heap`, returns `heap + 1`. -/
def compWindowHandleProc : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 5) (.reg 1))) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 7) (.reg 4)) (.reg 2)))) ;;
  .store (.reg 3) (.reg 8) ;;
  .ret (.bin .add (.reg 3) (.const 1))

/-- `op 3`: `args = [b, j, v, heap]`. Writes `(S j).RF.root v` at `heap`, returns `heap + 1`. -/
def compRootProc : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffVCompPtr))) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.reg 2))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 6) (.reg 5))) ;;
  .cond (.reg 7)
    (.assign 8 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
     .assign 9 (.load (.bin .add (.reg 8) (.reg 5))) ;;
     .assign 10 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
     .assign 11 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
     .assign 12 (.load (.bin .add (.reg 11) (.bin .add (.bin .mul (.reg 9) (.reg 10)) (.reg 1)))) ;;
     .assign 13 (.load (.bin .add (.reg 12) (.const lsfOffFAncPtr))) ;;
     .assign 14 (.load (.bin .add (.reg 13) (.const fOffCompIdPtr))) ;;
     .assign 15 (.load (.bin .add (.reg 13) (.const fOffCompRootPtr))) ;;
     .assign 16 (.load (.bin .add (.reg 14) (.reg 2))) ;;
     .assign 17 (.load (.bin .add (.reg 15) (.reg 16))) ;;
     .store (.reg 3) (.reg 17) ;;
     .ret (.bin .add (.reg 3) (.const 1)))
    (.store (.reg 3) (.reg 2) ;;
     .ret (.bin .add (.reg 3) (.const 1)))

/-- `op 4`: `args = [b, j, e, heap]`. Writes `(isCross, isIns, numPtr, denPtr)` at
`[heap, heap + 4)`, returns `heap + 4`. -/
def compEdgeInfoProc : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr))) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.reg 2))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 6) (.reg 2))) ;;
  .store (.reg 3) (.reg 5) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 7) ;;
  .cond (.reg 7)
    (.assign 8 (.load (.bin .add (.reg 0) (.const compOffOneLimbPtr))) ;;
     .store (.bin .add (.reg 3) (.const 2)) (.reg 8) ;;
     .store (.bin .add (.reg 3) (.const 3)) (.reg 8) ;;
     .ret (.bin .add (.reg 3) (.const 4)))
    (.assign 8 (.load (.bin .add (.reg 0) (.const compOffEdgeC1Ptr))) ;;
     .assign 9 (.load (.bin .add (.reg 8) (.reg 2))) ;;
     .assign 10 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
     .assign 11 (.load (.bin .add (.reg 10) (.reg 9))) ;;
     .assign 12 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
     .assign 13 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
     .assign 14 (.load (.bin .add (.reg 13) (.bin .add (.bin .mul (.reg 11) (.reg 12)) (.reg 1)))) ;;
     .assign 15 (.load (.bin .add (.reg 0) (.const compOffLW))) ;;
     .assign 16 (.load (.bin .add (.reg 14) (.const lsfOffWstrNumPtr))) ;;
     .assign 17 (.load (.bin .add (.reg 14) (.const lsfOffWstrDenPtr))) ;;
     .store (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 16) (.bin .mul (.reg 2) (.reg 15))) ;;
     .store (.bin .add (.reg 3) (.const 3)) (.bin .add (.reg 17) (.bin .mul (.reg 2) (.reg 15))) ;;
     .ret (.bin .add (.reg 3) (.const 4)))

/-- `op 5`: `args = [b, heap]`. Writes `(numComps, numEdgeful, k, vCap, eCap, L_w)` at
`[heap, heap + 6)`, returns `heap + 6`. -/
def compInfoProc : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const compOffNumComps))) ;;
  .store (.reg 1) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const compOffNumEdgeful))) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .store (.bin .add (.reg 1) (.const 2)) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .store (.bin .add (.reg 1) (.const 3)) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const compOffECap))) ;;
  .store (.bin .add (.reg 1) (.const 4)) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const compOffLW))) ;;
  .store (.bin .add (.reg 1) (.const 5)) (.reg 2) ;;
  .ret (.bin .add (.reg 1) (.const 6))

/-- Bundled readout procedures (`5` deterministic procedures). -/
def compReadoutProcs : List Stmt :=
  [compVertCompProc, compWindowHandleProc, compRootProc, compEdgeInfoProc, compInfoProc]

lemma compReadoutProcs_length : compReadoutProcs.length = 5 := rfl

lemma compReadoutProcs_noRand : ∀ s ∈ compReadoutProcs, s.NoRand := by
  intro s hs
  simp only [compReadoutProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    simp [compVertCompProc, compWindowHandleProc, compRootProc, compEdgeInfoProc, compInfoProc,
      Stmt.NoRand]

end

/-! ## 2. Shared helpers for readout proofs -/

public section

lemma compEndAddr_le_heap {W : LSFWindowImpl} {k b heap : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {mem : ℕ → ℕ}
    (hrep : CompLSFRepAt W k b S x mem)
    (hdisj : ∀ a, compFoot b x a → a < heap) :
    x.endAddr ≤ heap := by
  have hTE := hrep.2.2.2.2.2.2.2.2.2.1
  have hpos : b < x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hTE; omega
  have hlt := hdisj (x.endAddr - 1) ⟨by omega, by omega⟩
  omega

private lemma unsignedVal_zero_of_all_zero {mem : ℕ → ℕ} {a h L : ℕ}
    (hz : ∀ i < L, mem (a + i) = 0) :
    unsignedVal mem a h L = 0 := by
  induction L generalizing a with
  | zero => rfl
  | succ L ih =>
    rw [unsignedVal, show mem a = 0 from by simpa using hz 0 (Nat.zero_lt_succ L),
      ih (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1] using hz (i + 1) (by omega))]
    simp

lemma compOneLimb_valid_and_intVal {mem : ℕ → ℕ} {a h L : ℕ}
    (hh : 1 ≤ h) (hL : 1 ≤ L) (hhL : 2 ≤ h * L)
    (h0 : mem a = 1) (hz : ∀ i, 1 ≤ i → i < L → mem (a + i) = 0) :
    Valid mem a h L ∧ intVal mem a h L = 1 := by
  have hbase2 : 2 ≤ base h := by
    dsimp only [base]; exact le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hh)
  have hVal : Valid mem a h L := by
    intro i hi
    cases i with
    | zero => simpa [h0] using (by omega : 1 < base h)
    | succ i => rw [hz (i + 1) (by omega) hi]; omega
  have hU : unsignedVal mem a h L = 1 := by
    cases L with
    | zero => omega
    | succ L' =>
      rw [unsignedVal, h0, unsignedVal_zero_of_all_zero
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1] using hz (i + 1) (by omega) (by omega))]
      simp
  have hCap : 4 ≤ capacity h L := by
    dsimp only [capacity, base]
    rw [← pow_mul]
    exact le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) hhL)
  refine ⟨hVal, ?_⟩
  simp only [intVal, signedVal, hU, show ¬(capacity h L ≤ 2 * 1) by omega, ↓reduceIte, sub_zero]
  rfl

lemma compRespects_of_readout {W : LSFWindowImpl} {k b heap d : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {mem mem' : ℕ → ℕ}
    (hrep : CompLSFRepAt W k b S x mem)
    (hdisj : ∀ a, compFoot b x a → a < heap)
    (hz : ZeroFrom mem heap)
    (hfr : ∀ a, a < heap ∨ heap + d ≤ a → mem' a = mem a) :
    CompLSFRepAt W k b S x mem' ∧
    compPhi b x mem' = compPhi b x mem ∧
    (compLSFRep W k).Respects (compFoot b x) heap d mem (heap + d) b x mem' := by
  have hloc := compLSFRep_local W k b S x mem mem' fun a ha =>
    (hfr a (Or.inl (hdisj a ha))).symm
  refine ⟨hloc.1 hrep, hloc.2.symm, Nat.le_add_right _ _, le_rfl,
    fun a ha => (hfr a (Or.inr ha)).trans (hz a (by omega)),
    fun a ha _ => hfr a (Or.inl ha), fun a ha => Or.inl ha⟩

/-! ## 3. Verification of `op 1`..`op 3` -/

/-- Verification of `op 1` (`compVertCompProc`). -/
theorem compLSFDS_op1 {W : LSFWindowImpl} {w k b : ℕ} {G₀ : MGraph}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {p : Program}
    (hrep : CompLSFRepAt W k b S x mem)
    (hpre : (compLSFDS W w k G₀).pre 1 S args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hdisj : ∀ a, compFoot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).space 1 S args mem < 2 ^ w) :
    ∃ o st' c, Runs w p ω compVertCompProc (startState args mem pos) o st' c ∧
      ∃ S' x', CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDS W w k G₀).post 1 S args mem S' st'.mem ∧
        (compLSFRep W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDS W w k G₀).space 1 S args mem) mem o.value b x' st'.mem ∧
        c + compPhi b x' st'.mem ≤ (compLSFDS W w k G₀).cost 1 S args mem + compPhi b x mem := by
  rcases hpre with ⟨hk, b', v, heap, rfl, hw16, hvG⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
  simp only [compLSFDS, List.getD_cons_zero, List.getD_cons_succ] at hsp ⊢
  have hheap_eq : heapArg [b, v, heap] = heap := rfl
  rw [hheap_eq] at hdisj hz hsp ⊢
  have hend : x.endAddr ≤ heap := compEndAddr_le_heap hrep hdisj
  have hrep_all := hrep
  rcases hrep with ⟨hk', _, _, _, _, _, _, hnc, hne, hTE, hhdr, hBr, hm0, hTrack,
    hCompInfo, _, hVComp, _, _, _, _, _, _, _⟩
  rcases hhdr with ⟨_, _, _, _, _, _, _, hh_nC, _, hh_vComp, hh_ef, _, hh_n0, hh_m0,
    _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨ℓ₀, hBr'⟩ := hBr
  have hvC_ex : ∃ c : Fin x.numComps, v ∈ ((S ⟨0, hk⟩).compSt (x.compOf c)).G.V := by
    have hvU := (hBr' ⟨0, hk⟩).1.hV_eq ▸ hvG
    rw [Finset.mem_biUnion] at hvU
    obtain ⟨C, hC, hvC⟩ := hvU
    obtain ⟨c, rfl⟩ := (hTrack.hBij.2 C).mp hC
    exact ⟨c, hvC⟩
  obtain ⟨c, hvC⟩ := hvC_ex
  have hvlt : v < x.vCap := hTrack.hVlt v hvG
  have hclt : c.1 < x.vCap := lt_of_lt_of_le c.2 hnc
  have hvc_m : mem (compVCompBase b + v) = c.1 := hVComp c v hvC
  obtain ⟨hef_m, hn0_m, hm0_m, _⟩ := hCompInfo c
  set Gc0 := compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hGc0_n : Gc0.n ≤ x.vCap := by
    have hV0_sub : Gc0.V ⊆ Finset.range x.vCap := fun u hu => by
      have hCI := (hBr' ⟨0, hk⟩).1.hCompLSF (x.compOf c) (hTrack.compOf_mem c)
      have hSInv := LSFInvWith.toStructInv hCI.1
      have huT : u ∈ ((S ⟨0, hk⟩).compSt (x.compOf c)).T₀.V := by
        rw [hSInv.hTV, hCI.2.1]; exact hu
      have huC : u ∈ ((S ⟨0, hk⟩).compSt (x.compOf c)).G.V := by
        rw [hSInv.hGV_eq]; exact Finset.mem_union_left _ huT
      have huG : u ∈ (S ⟨0, hk⟩).G.V := by
        rw [← (hBr' ⟨0, hk⟩).1.hV_eq]; exact Finset.mem_biUnion.mpr ⟨x.compOf c, hTrack.compOf_mem c, huC⟩
      exact Finset.mem_range.mpr (hTrack.hVlt u huG)
    calc Gc0.n = Gc0.V.card := rfl
      _ ≤ (Finset.range x.vCap).card := Finset.card_le_card hV0_sub
      _ = x.vCap := Finset.card_range _
  have hGc0_m : Gc0.m < 2 ^ w := by
    have hsub : Gc0.E ⊆ (S ⟨0, hk⟩).G₀.E := Finset.filter_subset _ _
    have hle : Gc0.m ≤ x.m0Total := hm0 ▸ Finset.card_le_card hsub
    have hmk : x.m0Total ≤ x.m0Total * k := Nat.le_mul_of_pos_right _ (by omega)
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compGhostSize, compHdrSize] at hTE; omega
  have hb_w : b + compHdrSize < 2 ^ w := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hvC_w : compVCompBase b + v < 2 ^ w := by
    dsimp [compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hef_w : compEdgefulBase b x.vCap + c.1 < 2 ^ w := by
    dsimp [compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hn0_w : compN0Base b x.vCap + c.1 < 2 ^ w := by
    dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
      compGhostSize, compHdrSize] at hStat ⊢; omega
  have hm0_w : compM0Base b x.vCap + c.1 < 2 ^ w := by
    dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase,
      compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hhdr_w : compVCompBase b < 2 ^ w ∧ compEdgefulBase b x.vCap < 2 ^ w ∧
      compN0Base b x.vCap < 2 ^ w ∧ compM0Base b x.vCap < 2 ^ w := by
    dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase,
      compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have h_ef_lt : (if 1 ≤ Gc0.m then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  have h_n0_lt : Gc0.n < 2 ^ w := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat; omega
  have h_c_lt : c.1 < 2 ^ w := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat; omega
  have hst0 : ∃ o st' c_run,
      Runs w p ω compVertCompProc (startState [b, v, heap] mem pos) o st' c_run ∧
      (o = .returned (heap + 4) ∧
        st'.mem heap = c.1 ∧
        st'.mem (heap + 1) = (if 1 ≤ Gc0.m then 1 else 0) ∧
        st'.mem (heap + 2) = Gc0.n ∧
        st'.mem (heap + 3) = Gc0.m ∧
        ∀ a, a < heap ∨ heap + 4 ≤ a → st'.mem a = mem a) ∧
      0 + c_run ≤ 120 := by
    unfold compVertCompProc
    have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
      dsimp [compHdrSize] at hb_w hoff; omega
    refine runs_seq_assign_le (v := compVCompBase b)
      (Expr.eval_load_of_eq (by have := hb_off compOffVCompPtr (by decide); eval_expr) hh_vComp) ?_
    refine runs_seq_assign_le (v := compEdgefulBase b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulPtr (by decide); eval_expr) hh_ef) ?_
    refine runs_seq_assign_le (v := compN0Base b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffN0Ptr (by decide); eval_expr) hh_n0) ?_
    refine runs_seq_assign_le (v := compM0Base b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffM0Ptr (by decide); eval_expr) hh_m0) ?_
    refine runs_seq_assign_le (v := c.1) (Expr.eval_load_of_eq (by eval_expr) hvc_m) ?_
    refine runs_seq_store_le (x := heap) (v := c.1) (by eval_expr) (by eval_expr) ?_
    have hef_m1 : Function.update mem heap c.1 (compEdgefulBase b x.vCap + c.1) =
        if 1 ≤ Gc0.m then 1 else 0 := by
      rw [Function.update_of_ne (by
        dsimp [compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega), hef_m]
    refine runs_seq_assign_le (v := if 1 ≤ Gc0.m then 1 else 0)
      (Expr.eval_load_of_eq (by eval_expr) hef_m1) ?_
    refine runs_seq_store_le (x := heap + 1) (v := if 1 ≤ Gc0.m then 1 else 0)
      (by eval_expr) (by eval_expr) ?_
    have hn0_m2 : Function.update (Function.update mem heap c.1) (heap + 1)
        (if 1 ≤ Gc0.m then 1 else 0) (compN0Base b x.vCap + c.1) = Gc0.n := by
      have hlt2 : compN0Base b x.vCap + c.1 < heap := by
        dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
          compGhostSize, compHdrSize] at hStat ⊢; omega
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hn0_m]
    refine runs_seq_assign_le (v := Gc0.n) (Expr.eval_load_of_eq (by eval_expr) hn0_m2) ?_
    refine runs_seq_store_le (x := heap + 2) (v := Gc0.n) (by eval_expr) (by eval_expr) ?_
    have hm0_m3 : Function.update (Function.update (Function.update mem heap c.1) (heap + 1)
        (if 1 ≤ Gc0.m then 1 else 0)) (heap + 2) Gc0.n (compM0Base b x.vCap + c.1) = Gc0.m := by
      have hlt3 : compM0Base b x.vCap + c.1 < heap := by
        dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase,
          compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hm0_m]
    refine runs_seq_assign_le (v := Gc0.m) (Expr.eval_load_of_eq (by eval_expr) hm0_m3) ?_
    refine runs_seq_store_le (x := heap + 3) (v := Gc0.m) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := heap + 4) (by eval_expr) ?_ (by simp [Expr.size])
    refine ⟨rfl,
      by simp [startState],
      by simp [startState],
      by simp [startState],
      by simp [startState],
      fun a ha => by simp [startState, Function.update_of_ne (by omega : a ≠ heap + 3),
        Function.update_of_ne (by omega : a ≠ heap + 2),
        Function.update_of_ne (by omega : a ≠ heap + 1),
        Function.update_of_ne (by omega : a ≠ heap)]⟩
  rcases hst0 with ⟨o, st', c_run, hrun, ⟨rfl, h0, h1, h2, h3, hfr⟩, hc⟩
  obtain ⟨hrep', hphi', hresp⟩ := compRespects_of_readout hrep_all hdisj hz hfr
  refine ⟨.returned (heap + 4), st', c_run, hrun, S, x, hrep', ?_, hresp, by omega⟩
  refine ⟨rfl, hk, x.compOf c, hTrack.compOf_mem c, hvC, ?_, h1, h2, h3⟩
  rw [h0, hh_nC]; exact c.2

/-- Verification of `op 2` (`compWindowHandleProc`). -/
theorem compLSFDS_op2 {W : LSFWindowImpl} {w k b : ℕ} {G₀ : MGraph}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {p : Program}
    (hrep : CompLSFRepAt W k b S x mem)
    (hpre : (compLSFDS W w k G₀).pre 2 S args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hdisj : ∀ a, compFoot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).space 2 S args mem < 2 ^ w) :
    ∃ o st' c, Runs w p ω compWindowHandleProc (startState args mem pos) o st' c ∧
      ∃ S' x', CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDS W w k G₀).post 2 S args mem S' st'.mem ∧
        (compLSFRep W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDS W w k G₀).space 2 S args mem) mem o.value b x' st'.mem ∧
        c + compPhi b x' st'.mem ≤ (compLSFDS W w k G₀).cost 2 S args mem + compPhi b x mem := by
  rcases hpre with ⟨b', c_idx, j_idx, heap, rfl, hw16, hc_lt, hef1, hj_lt⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
  simp only [compLSFDS, List.getD_cons_zero, List.getD_cons_succ] at hsp ⊢
  have hheap_eq : heapArg [b, c_idx, j_idx, heap] = heap := rfl
  rw [hheap_eq] at hdisj hz hsp ⊢
  have hend : x.endAddr ≤ heap := compEndAddr_le_heap hrep hdisj
  have hrep_all := hrep
  rcases hrep with ⟨hk, _, _, _, _, _, _, hnc, hne, hTE, hhdr, hBr, _, hTrack,
    hCompInfo, _, _, _, _, _, _, _, hWins, _⟩
  rcases hhdr with ⟨_, _, hh_k, _, _, _, _, hh_nC, _, _, hh_ef, hh_efIdx, _, _, _, _, _, _, _, _, _, hh_hdl, _, _⟩
  rw [hh_nC] at hc_lt
  rw [hh_ef] at hef1
  let cF : Fin x.numComps := ⟨c_idx, hc_lt⟩
  obtain ⟨hef_m, _, _, hEfEx⟩ := hCompInfo cF
  have hm_ge1 : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf cF)).m := by
    by_contra h0
    have h0' : mem (compEdgefulBase b x.vCap + c_idx) = 0 := by simpa [cF, h0] using hef_m
    omega
  obtain ⟨ec, _, hec_m, hec_eq⟩ := hEfEx hm_ge1
  let jF : Fin k := ⟨j_idx, hj_lt⟩
  obtain ⟨hWin_m, hWin_rep, _, _, _, hWin_ge, hWin_le⟩ := hWins ec jF
  set hWin := x.winHandle ec jF
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hidx_lt : ec.1 * k + jF.1 < x.m0Total * k := by
    calc ec.1 * k + jF.1 < ec.1 * k + k := Nat.add_lt_add_left jF.2 _
      _ = (ec.1 + 1) * k := by ring
      _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
  have hk_w : k < 2 ^ w := by
    have : 1 ≤ x.m0Total := by omega
    have : k ≤ x.m0Total * k := Nat.le_mul_of_pos_left k this
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_w : b + compHdrSize < 2 ^ w := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hH_w : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + jF.1) < 2 ^ w := by
    dsimp only [compTablesEnd] at hTE; omega
  have hWin_w : hWin < 2 ^ w := by
    have : hWin < (x.winConc ec jF).endAddr hWin := by
      have := lsfHdr_lt_end hWin (x.winConc ec jF).vCap (x.winConc ec jF).eCap
        (x.winConc ec jF).n0 (x.winConc ec jF).tM (x.winConc ec jF).L_w
      dsimp only [LSFConcrete.endAddr, lsfHdrSize] at this ⊢; omega
    omega
  have hefi_w : compEdgefulIdxBase b x.vCap + c_idx < 2 ^ w := by
    dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
      compGhostSize, compHdrSize] at hStat ⊢; omega
  have hst0 : ∃ o st' c_run,
      Runs w p ω compWindowHandleProc (startState [b, c_idx, j_idx, heap] mem pos) o st' c_run ∧
      (o = .returned (heap + 1) ∧ st'.mem heap = hWin ∧
        ∀ a, a < heap ∨ heap + 1 ≤ a → st'.mem a = mem a) ∧
      0 + c_run ≤ 80 := by
    unfold compWindowHandleProc
    have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
      dsimp [compHdrSize] at hb_w hoff; omega
    refine runs_seq_assign_le (v := k)
      (Expr.eval_load_of_eq (by have := hb_off compOffK (by decide); eval_expr) hh_k) ?_
    refine runs_seq_assign_le (v := compEdgefulIdxBase b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulIdxPtr (by decide); eval_expr) hh_efIdx) ?_
    refine runs_seq_assign_le (v := compHandlesBase b x.vCap x.eCap x.L_w)
      (Expr.eval_load_of_eq (by have := hb_off compOffHandlesPtr (by decide); eval_expr) hh_hdl) ?_
    refine runs_seq_assign_le (v := ec.1) (Expr.eval_load_of_eq (by eval_expr) hec_m) ?_
    refine runs_seq_assign_le (v := hWin)
      (Expr.eval_load_of_eq (by
        have hmul : ec.1 * k < 2 ^ w := by dsimp [jF] at hH_w; omega
        have hadd : ec.1 * k + j_idx < 2 ^ w := by dsimp [jF] at hH_w; omega
        eval_expr) hWin_m) ?_
    refine runs_seq_store_le (x := heap) (v := hWin) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := heap + 1) (by eval_expr)
      ⟨rfl, by simp [startState], fun a ha => by simp [startState, Function.update_of_ne (by omega : a ≠ heap)]⟩
      (by simp [Expr.size])
  rcases hst0 with ⟨o, st', c_run, hrun, ⟨rfl, h0, hfr⟩, hc⟩
  obtain ⟨hrep', hphi', hresp⟩ := compRespects_of_readout hrep_all hdisj hz hfr
  refine ⟨.returned (heap + 1), st', c_run, hrun, S, x, hrep', ?_, hresp, by omega⟩
  obtain ⟨ℓ₀, hBr'⟩ := hBr
  have hWin_rep' : (LSFRep W.h).rep hWin ((S jF).compSt (x.compOf cF)) (x.winConc ec jF) st'.mem := by
    have hrep_m := (lsfRep_local W.h hWin ((S jF).compSt (x.compOf (x.edgefulComp ec)))
      (x.winConc ec jF) mem st'.mem fun a ha =>
        (hfr a (Or.inl (lt_of_lt_of_le (lt_of_lt_of_le ha.2 hWin_le) hend))).symm).1 hWin_rep
    rwa [hec_eq] at hrep_m
  refine ⟨rfl, hj_lt, x.compOf cF, ?_, x.winConc ec jF, by simpa [h0] using hWin_rep'⟩
  rw [(hBr' jF).2.1]
  exact Finset.mem_filter.mpr ⟨hTrack.compOf_mem cF, hm_ge1⟩

/-- Verification of `op 3` (`compRootProc`). -/
theorem compLSFDS_op3 {W : LSFWindowImpl} {w k b : ℕ} {G₀ : MGraph}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {p : Program}
    (hrep : CompLSFRepAt W k b S x mem)
    (hpre : (compLSFDS W w k G₀).pre 3 S args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hdisj : ∀ a, compFoot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).space 3 S args mem < 2 ^ w) :
    ∃ o st' c, Runs w p ω compRootProc (startState args mem pos) o st' c ∧
      ∃ S' x', CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDS W w k G₀).post 3 S args mem S' st'.mem ∧
        (compLSFRep W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDS W w k G₀).space 3 S args mem) mem o.value b x' st'.mem ∧
        c + compPhi b x' st'.mem ≤ (compLSFDS W w k G₀).cost 3 S args mem + compPhi b x mem ∧
        x' = x := by
  rcases hpre with ⟨hk, b', j_idx, v, heap, rfl, hw16, hj_lt, hvG⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
  simp only [compLSFDS, List.getD_cons_zero, List.getD_cons_succ] at hsp ⊢
  have hheap_eq : heapArg [b, j_idx, v, heap] = heap := rfl
  rw [hheap_eq] at hdisj hz hsp ⊢
  have hend : x.endAddr ≤ heap := compEndAddr_le_heap hrep hdisj
  have hrep_all := hrep
  rcases hrep with ⟨hk', _, _, _, _, _, _, hnc, hne, hTE, hhdr, hBr, _, hTrack,
    hCompInfo, _, hVComp, _, _, _, _, _, hWins, _⟩
  rcases hhdr with ⟨_, _, hh_k, _, _, _, _, _, _, hh_vComp, hh_ef, hh_efIdx, _, _, _, _, _, _, _, _, _, hh_hdl, _, _⟩
  obtain ⟨ℓ₀, hBr'⟩ := hBr
  let jF : Fin k := ⟨j_idx, hj_lt⟩
  have ⟨hInv_j, hG0_j, hG_j, _, _, _, hCG_j⟩ := hBr' jF
  have hvC_ex : ∃ c : Fin x.numComps, v ∈ ((S ⟨0, hk⟩).compSt (x.compOf c)).G.V := by
    have hvU := (hBr' ⟨0, hk⟩).1.hV_eq ▸ hvG
    rw [Finset.mem_biUnion] at hvU
    obtain ⟨C, hC, hvC⟩ := hvU
    obtain ⟨c, rfl⟩ := (hTrack.hBij.2 C).mp hC
    exact ⟨c, hvC⟩
  obtain ⟨c, hvC⟩ := hvC_ex
  have hvCj : v ∈ ((S jF).compSt (x.compOf c)).G.V := (hCG_j c).symm ▸ hvC
  have hC_mem_j : x.compOf c ∈ components (S jF).G₀ := hG0_j.symm ▸ hTrack.compOf_mem c
  have hRoot_eq : (S jF).RF.root v = ((S jF).compSt (x.compOf c)).RF.root v :=
    compLSF_RF_root_eq hInv_j hC_mem_j hvCj
  have hvlt : v < x.vCap := hTrack.hVlt v hvG
  have hclt : c.1 < x.vCap := lt_of_lt_of_le c.2 hnc
  have hvc_m : mem (compVCompBase b + v) = c.1 := hVComp c v hvC
  obtain ⟨hef_m, _, _, hEfEx⟩ := hCompInfo c
  set Gc0 := compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_w : b + compHdrSize < 2 ^ w := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hvC_w : compVCompBase b + v < 2 ^ w := by
    dsimp [compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hef_w : compEdgefulBase b x.vCap + c.1 < 2 ^ w := by
    dsimp [compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have h_ef_lt : (if 1 ≤ Gc0.m then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  have h_c_lt : c.1 < 2 ^ w := by
    dsimp [compStaticSize, compGhostSize, compHdrSize] at hStat; omega
  have hst0 : ∃ o st' c_run,
      Runs w p ω compRootProc (startState [b, j_idx, v, heap] mem pos) o st' c_run ∧
      (o = .returned (heap + 1) ∧ st'.mem heap = (S jF).RF.root v ∧
        ∀ a, a < heap ∨ heap + 1 ≤ a → st'.mem a = mem a) ∧
      0 + c_run ≤ 150 := by
    unfold compRootProc
    have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
      dsimp [compHdrSize] at hb_w hoff; omega
    refine runs_seq_assign_le (v := compVCompBase b)
      (Expr.eval_load_of_eq (by have := hb_off compOffVCompPtr (by decide); eval_expr) hh_vComp) ?_
    refine runs_seq_assign_le (v := c.1) (Expr.eval_load_of_eq (by eval_expr) hvc_m) ?_
    refine runs_seq_assign_le (v := compEdgefulBase b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulPtr (by decide); eval_expr) hh_ef) ?_
    refine runs_seq_assign_le (v := if 1 ≤ Gc0.m then 1 else 0)
      (Expr.eval_load_of_eq (by eval_expr) hef_m) ?_
    refine WordRAM.runs_cond_le (v := if 1 ≤ Gc0.m then 1 else 0) (by eval_expr) ?_ ?_
    · intro hef_ne
      have hm_ge1 : 1 ≤ Gc0.m := by
        by_contra h0; exact hef_ne (by simp [h0])
      obtain ⟨ec, _, hec_m, hec_eq⟩ := hEfEx hm_ge1
      obtain ⟨hWin_m, hWin_rep, hvWin, _, _, hWin_ge, hWin_le⟩ := hWins ec jF
      set hWin := x.winHandle ec jF
      set xWin := x.winConc ec jF
      rw [hec_eq] at hWin_rep
      have hWin_hdr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hWin_fAnc := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hWin_inv := hWin_rep.2.2.2.2.2.2.1
      set fAncPtr := lsfFAncPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM
      have hfAnc_sub := lsfFAnc_sub_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
      have hWin_hdr_le := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
      dsimp only [LSFConcrete.endAddr] at hWin_le
      have hcid_mem := hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v (hWin_inv.RF_V_eq ▸ hvCj)
      set cid := mem (fCompIdBase fAncPtr xWin.vCap + v)
      have hcid_act := hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cid hcid_mem.2.1
      have hcid_lt : cid < xWin.vCap := hcid_act.1
      have hrt_val : mem (fCompRootBase fAncPtr xWin.vCap + cid) = (S jF).RF.root v :=
        compRoot_eq_of_fAncAt hInv_j hC_mem_j hWin_fAnc hvCj
      have hrt_lt : (S jF).RF.root v < xWin.vCap := by
        rw [hRoot_eq]
        have hRS := lsfInv_to_RS (hInv_j.hCompLSF (x.compOf c) hC_mem_j).1
        have hrm := (rootedForest_root_spec hRS hvCj).1
        exact hWin_fAnc.2.2.2.2.2.2.1 _ (hWin_inv.RF_V_eq.symm ▸
          lsfInv_R_sub_V (hInv_j.hCompLSF (x.compOf c) hC_mem_j).1 hrm)
      have hidx_lt : ec.1 * k + j_idx < x.m0Total * k := by
        calc ec.1 * k + j_idx < ec.1 * k + k := Nat.add_lt_add_left hj_lt _
          _ = (ec.1 + 1) * k := by ring
          _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
      have hk_w : k < 2 ^ w := by
        have : k ≤ x.m0Total * k := Nat.le_mul_of_pos_left k (by omega)
        dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
      have hWin_ltw : hWin + lsfHdrSize < 2 ^ w := by omega
      have hfAnc_ltw : fAncPtr + fAncSize xWin.vCap < 2 ^ w := by omega
      have hcid_ltw : fCompIdBase fAncPtr xWin.vCap + v < 2 ^ w := by
        dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
      have hcr_ltw : fCompRootBase fAncPtr xWin.vCap + cid < 2 ^ w := by
        dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
      have hH_w : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j_idx) < 2 ^ w := by
        dsimp only [compTablesEnd] at hTE; omega
      have hefi_w : compEdgefulIdxBase b x.vCap + c.1 < 2 ^ w := by
        dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
          compGhostSize, compHdrSize] at hStat ⊢; omega
      have hv_ltw : xWin.vCap < 2 ^ w := by dsimp [fAncSize] at hfAnc_ltw; omega
      refine runs_seq_assign_le (v := compEdgefulIdxBase b x.vCap)
        (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulIdxPtr (by decide); eval_expr) hh_efIdx) ?_
      refine runs_seq_assign_le (v := ec.1) (Expr.eval_load_of_eq (by eval_expr) hec_m) ?_
      refine runs_seq_assign_le (v := k)
        (Expr.eval_load_of_eq (by have := hb_off compOffK (by decide); eval_expr) hh_k) ?_
      refine runs_seq_assign_le (v := compHandlesBase b x.vCap x.eCap x.L_w)
        (Expr.eval_load_of_eq (by have := hb_off compOffHandlesPtr (by decide); eval_expr) hh_hdl) ?_
      refine runs_seq_assign_le (v := hWin)
        (Expr.eval_load_of_eq (by
          have : ec.1 * k < 2 ^ w := by omega
          have : ec.1 * k + j_idx < 2 ^ w := by omega
          eval_expr) hWin_m) ?_
      refine runs_seq_assign_le (v := fAncPtr)
        (Expr.eval_load_of_eq (by
          have : lsfOffFAncPtr < 2 ^ w ∧ hWin + lsfOffFAncPtr < 2 ^ w := by
            dsimp [lsfOffFAncPtr, lsfHdrSize] at hWin_ltw ⊢; omega
          eval_expr) hWin_hdr.2.2.2.2.2.2.2.1) ?_
      refine runs_seq_assign_le (v := fCompIdBase fAncPtr xWin.vCap)
        (Expr.eval_load_of_eq (by
          have : fOffCompIdPtr < 2 ^ w ∧ fAncPtr + fOffCompIdPtr < 2 ^ w := by
            dsimp [fOffCompIdPtr, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
          eval_expr) hWin_fAnc.2.2.2.1) ?_
      refine runs_seq_assign_le (v := fCompRootBase fAncPtr xWin.vCap)
        (Expr.eval_load_of_eq (by
          have : fOffCompRootPtr < 2 ^ w ∧ fAncPtr + fOffCompRootPtr < 2 ^ w := by
            dsimp [fOffCompRootPtr, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
          eval_expr) hWin_fAnc.2.2.2.2.1) ?_
      refine runs_seq_assign_le (v := cid) (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
      refine runs_seq_assign_le (v := (S jF).RF.root v)
        (Expr.eval_load_of_eq (by eval_expr) hrt_val) ?_
      refine runs_seq_store_le (x := heap) (v := (S jF).RF.root v)
        (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := heap + 1) (by eval_expr)
        ⟨rfl, by simp [startState],
          fun a ha => by simp [startState, Function.update_of_ne (by omega : a ≠ heap)]⟩
        (by simp [Expr.size])
    · intro hef_0
      have hm0_c : (compGraph (S jF).G₀ (x.compOf c)).m = 0 := by
        rw [hG0_j]
        by_contra hne0
        have hpos : 1 ≤ Gc0.m := Nat.pos_of_ne_zero hne0
        simp [hpos] at hef_0
      have hiso := (isoComp_props hInv_j hC_mem_j hm0_c).2.2 v hvCj
      refine runs_seq_store_le (x := heap) (v := v) (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := heap + 1) (by eval_expr)
        ⟨rfl, by simp [startState, hiso],
          fun a ha => by simp [startState, Function.update_of_ne (by omega : a ≠ heap)]⟩
        (by simp [Expr.size])
  rcases hst0 with ⟨o, st', c_run, hrun, ⟨rfl, h0, hfr⟩, hc⟩
  obtain ⟨hrep', hphi', hresp⟩ := compRespects_of_readout hrep_all hdisj hz hfr
  exact ⟨.returned (heap + 1), st', c_run, hrun, S, x, hrep', ⟨rfl, hj_lt, h0⟩, hresp, by omega, rfl⟩


end

end MinCostFlow.SparseCore.Program
