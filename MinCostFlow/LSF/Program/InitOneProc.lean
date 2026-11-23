module

public import MinCostFlow.LSF.Program.BlockRep
public import MinCostFlow.LSF.Program.Utils
import Mathlib.Tactic.Linarith

/-!
# Helper procedures for one-vertex LSF initialization (`n₀ = 1`)

This file defines and verifies two small deterministic procedures used when `G₀` has a single
vertex `r₀`:
* `initOneBlocksProc`: writes the trivial `T` block (`tM = 0`), one-vertex `F` graph, one-root
  `FAnc` block, and empty `W` block onto zeroed static memory.
* `initOneWstrProc h`: writes the exact rational stretch `6 / 1` (in `L_w` signed base-`2^h` limbs)
  for every edge in `G₀`'s edge list.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## One-vertex, zero-edge dynamic graph writer -/

/-- Straight-line stores writing a one-vertex (`rR0`), zero-edge `DynGraphAt` at `rBase` with
capacities `(rVc, rEc)` onto zeroed memory. Does not modify any registers. -/
def storeOneVertDg (rBase rVc rEc rR0 : ℕ) : Stmt :=
  .store (.reg rBase) (.reg rVc) ;;
  .store (.bin .add (.reg rBase) (.const 1)) (.reg rEc) ;;
  .store (.bin .add (.reg rBase) (.const 2)) (.const 1) ;;
  .store (.bin .add (.bin .add (.reg rBase) (.const 4)) (.reg rR0)) (.const 1) ;;
  .store (.bin .add (.bin .add (.reg rBase) (.const 4)) (.reg rVc)) (.reg rR0) ;;
  .store (.bin .add (.bin .add (.bin .add (.reg rBase) (.const 4))
    (.bin .mul (.const 3) (.reg rVc))) (.reg rR0)) (.reg rR0) ;;
  .store (.bin .add (.bin .add (.bin .add (.reg rBase) (.const 4))
    (.bin .mul (.const 4) (.reg rVc))) (.reg rR0)) (.reg rR0)

lemma storeOneVertDg_noRand (rBase rVc rEc rR0 : ℕ) :
    (storeOneVertDg rBase rVc rEc rR0).NoRand := by
  simp [storeOneVertDg, Stmt.NoRand]

private lemma dynGraphAt_of_oneVert_writes {mem : ℕ → ℕ} {a vCap eCap r0 : ℕ}
    (hr0 : r0 < vCap)
    (h0 : mem (a + dgVCapOff) = vCap)
    (h1 : mem (a + dgECapOff) = eCap)
    (h2 : mem (a + dgNOff) = 1)
    (h3 : mem (a + dgMOff) = 0)
    (hvp : ∀ v < vCap, mem (dgVPresBase a + v) = if v = r0 then 1 else 0)
    (hvl : mem (dgVListBase a vCap) = r0)
    (hpos : mem (dgVPosBase a vCap + r0) = 0)
    (he2i : mem (dgExtToIntBase a vCap + r0) = r0)
    (hi2e : mem (dgIntToExtBase a vCap + r0) = r0)
    (hdeg : ∀ s < vCap, mem (dgSlotDegBase a vCap + s) = 0)
    (hhead : ∀ s < vCap, mem (dgIncHeadBase a vCap + s) = 0)
    (hep : ∀ e < eCap, mem (dgEPresBase a vCap + e) = 0)
    {G : MGraph} (hV : G.V = {r0}) (hE : G.E = ∅) :
    DynGraphAt mem a vCap eCap G := by
  have hn : G.n = 1 := by unfold MGraph.n; rw [hV]; simp
  have hm : G.m = 0 := by unfold MGraph.m; rw [hE]; simp
  refine ⟨fun _ he => absurd (hE ▸ he) (Finset.notMem_empty _),
    fun v hv => by rw [hV, Finset.mem_singleton] at hv; subst hv; exact hr0,
    fun _ he => absurd (hE ▸ he) (Finset.notMem_empty _),
    h0, h1, by rw [hn]; exact h2, by rw [hm]; exact h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hvp v hv, hV]; simp
  · refine ⟨[r0], by simp [hn], List.nodup_singleton r0, by simp [hV], ?_, ?_⟩
    · intro i hi
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi; simpa using hvl
    · intro i hi
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi; simpa using hpos
  · intro v hv
    rw [hV, Finset.mem_singleton] at hv; subst hv
    rw [he2i, hi2e, hV]
    exact ⟨Finset.mem_singleton_self _, rfl⟩
  · intro s hs
    rw [hV, Finset.mem_singleton] at hs; subst hs
    rw [hi2e, he2i, hV]
    exact ⟨Finset.mem_singleton_self _, rfl⟩
  · intro e he
    rw [hep e he, hE]; simp
  · refine ⟨[], by simp [hm], List.nodup_nil, by simp [hE],
      fun _ hi => by simp at hi, fun _ hi => by simp at hi⟩
  · intro _ he; exact absurd (hE ▸ he) (Finset.notMem_empty _)
  · refine ⟨fun _ => [], fun s hs => ⟨?_, by simpa using hdeg s hs, ?_⟩⟩
    · refine ⟨List.nodup_nil, fun _ h => by simp at h, by simpa using hhead s hs,
        fun _ hi => by simp at hi⟩
    · intro h; simp [hE]

lemma storeOneVertDg_triple {w rBase rVc rEc rR0 : ℕ} {p : Program}
    (a vCap eCap r0 : ℕ) (regs₀ mem₀ : ℕ → ℕ)
    (hw16 : 16 ≤ 2 ^ w) (hr0 : r0 < vCap)
    (hbd : a + dynGraphSize vCap eCap < 2 ^ w)
    (hzero : ∀ i < dynGraphSize vCap eCap, mem₀ (a + i) = 0) :
    Triple w p
      (fun st => st.regs = regs₀ ∧ regs₀ rBase = a ∧ regs₀ rVc = vCap ∧ regs₀ rEc = eCap ∧
        regs₀ rR0 = r0 ∧ st.mem = mem₀)
      (storeOneVertDg rBase rVc rEc rR0)
      (normalPost fun st => st.regs = regs₀ ∧
        (∀ G : MGraph, G.V = {r0} → G.E = ∅ → DynGraphAt st.mem a vCap eCap G) ∧
        (∀ z, z < a ∨ a + dynGraphSize vCap eCap ≤ z → st.mem z = mem₀ z))
      (fun _ => 120) := by
  intro st ω ⟨hregs, hB, hVc, hEc, hR0, hmem⟩
  subst hmem
  have hB' : st.regs rBase = a := hregs ▸ hB
  have hVc' : st.regs rVc = vCap := hregs ▸ hVc
  have hEc' : st.regs rEc = eCap := hregs ▸ hEc
  have hR0' : st.regs rR0 = r0 := hregs ▸ hR0
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  refine runs_start_le ?_
  unfold storeOneVertDg
  refine runs_seq_store_le (x := a) (v := vCap) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := a + 1) (v := eCap) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := a + 2) (v := 1) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := a + 4 + r0) (v := 1) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := a + 4 + vCap) (v := r0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := a + 4 + 3 * vCap + r0) (v := r0) (by eval_expr) (by eval_expr) ?_
  refine runs_store_le (x := a + 4 + 4 * vCap + r0) (v := r0) (by eval_expr) (by eval_expr) ?_
    (by wram_cost)
  dsimp only
  refine ⟨hregs, fun G hV hE => ?_, ?_⟩
  · refine dynGraphAt_of_oneVert_writes hr0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hV hE
    · simp only [dgVCapOff, Nat.add_zero]
      simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · simp only [dgECapOff]
      simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · simp only [dgNOff]
      simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · simp only [dgMOff]
      simp (disch := omega) only [Function.update_of_ne]
      exact hzero 3 (by omega)
    · intro v hv
      simp only [dgVPresBase]
      by_cases hvr : v = r0
      · subst hvr
        rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hvr)]
        simp (disch := omega) only [Function.update_of_ne]
        rw [Nat.add_assoc]; exact hzero (4 + v) (by omega)
    · simp only [dgVListBase]
      simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · simp only [dgVPosBase]
      simp (disch := omega) only [Function.update_of_ne]
      rw [Nat.add_assoc, Nat.add_assoc]; exact hzero (4 + (2 * vCap + r0)) (by omega)
    · simp only [dgExtToIntBase]
      simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · simp only [dgIntToExtBase]
      exact Function.update_self _ _ _
    · intro s hs
      simp only [dgSlotDegBase]
      simp (disch := omega) only [Function.update_of_ne]
      rw [Nat.add_assoc, Nat.add_assoc]; exact hzero (4 + (5 * vCap + s)) (by omega)
    · intro s hs
      simp only [dgIncHeadBase]
      simp (disch := omega) only [Function.update_of_ne]
      rw [Nat.add_assoc, Nat.add_assoc]; exact hzero (4 + (6 * vCap + s)) (by omega)
    · intro e he
      simp only [dgEPresBase]
      simp (disch := omega) only [Function.update_of_ne]
      rw [Nat.add_assoc, Nat.add_assoc]; exact hzero (4 + (7 * vCap + e)) (by omega)
  · intro z hz
    simp (disch := omega) only [Function.update_of_ne]

/-! ## Sub-block writers for `n₀ = 1` -/

private lemma tBlockAt_oneVert {mem : ℕ → ℕ} {tPtr vCap eCap r0 : ℕ}
    (h0 : mem (tPtr + 0) = 0)
    (h1 : mem (tPtr + 1) = tDgTPtr tPtr)
    (h2 : mem (tPtr + 2) = tOrigIdBase tPtr vCap 0)
    (h3 : mem (tPtr + 3) = tPiBase tPtr vCap 0)
    (h4 : mem (tPtr + 4) = tFrozenTailBase tPtr vCap 0)
    (h5 : mem (tPtr + 5) = tFrozenHeadBase tPtr vCap 0)
    (h6 : mem (tPtr + 6) = tIdxOfEdgeBase tPtr vCap 0)
    (h7 : mem (tPtr + 7) = tSplitScratchBase tPtr vCap eCap 0)
    (hidx0 : ∀ e < eCap, mem (tIdxOfEdgeBase tPtr vCap 0 + e) = 0)
    (hdgT : ∀ G : MGraph, G.V = {r0} → G.E = ∅ → DynGraphAt mem (tDgTPtr tPtr) vCap 1 G)
    {G T : MGraph} (hGV : G.V = {r0}) (hTE : T.E = ∅) :
    TBlockAt mem tPtr vCap eCap 0 G T T (fun _ => 0) [] := by
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, rfl, List.nodup_nil,
    by simp [hTE], fun _ hi => by simp at hi, fun _ hi => by simp at hi,
    fun _ hi => by simp at hi, fun e he hne => absurd (hidx0 e he) hne,
    ⟨{r0}, ∅, fun _ => 0, fun _ => 0⟩, hdgT _ rfl rfl, hGV.symm,
    fun _ he => absurd he (Finset.notMem_empty _), fun _ hi => by simp at hi⟩

/-- Writes the `T` block header (`tM = 0`) at `reg 0` using scratch regs `7, 8, 9, 10`,
then fills `dgT` via `storeOneVertDg`. Expects regs `0=tPtr, 4=vCap, 5=eCap, 6=r0`. -/
def storeOneTBlock : Stmt :=
  .assign 7 (.bin .add (.reg 0) (.const 8)) ;;
  .assign 8 (.bin .add (.reg 7) (.bin .add (.const 13) (.bin .mul (.const 7) (.reg 4)))) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 5)) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.reg 7) ;;
  .store (.bin .add (.reg 0) (.const 2)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 4)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 5)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 6)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 7)) (.reg 9) ;;
  .assign 10 (.const 1) ;;
  storeOneVertDg 7 4 10 6

lemma storeOneTBlock_noRand : storeOneTBlock.NoRand := by
  simp [storeOneTBlock, storeOneVertDg_noRand, Stmt.NoRand]

private lemma storeOneTBlock_triple {w : ℕ} {p : Program}
    (tPtr vCap eCap r0 : ℕ) (regs₀ mem₀ : ℕ → ℕ)
    (hw16 : 16 ≤ 2 ^ w) (hr0 : r0 < vCap)
    (hbd : tPtr + tBlockSize vCap eCap 0 < 2 ^ w)
    (hzero : ∀ a, tPtr ≤ a → a < tPtr + tBlockSize vCap eCap 0 → mem₀ a = 0) :
    Triple w p
      (fun st => st.regs = regs₀ ∧ regs₀ 0 = tPtr ∧ regs₀ 4 = vCap ∧ regs₀ 5 = eCap ∧
        regs₀ 6 = r0 ∧ st.mem = mem₀)
      storeOneTBlock
      (normalPost fun st =>
        (∀ r ≤ 6, st.regs r = regs₀ r) ∧
        (∀ G T : MGraph, G.V = {r0} → T.V = {r0} → T.E = ∅ →
          TBlockAt st.mem tPtr vCap eCap 0 G T T (fun _ => 0) []) ∧
        (∀ z, z < tPtr ∨ tPtr + tBlockSize vCap eCap 0 ≤ z → st.mem z = mem₀ z))
      (fun _ => 210) := by
  intro st ω ⟨hregs, h0, h4, h5, h6, hmem⟩
  subst hmem
  have h0' : st.regs 0 = tPtr := hregs ▸ h0
  have h4' : st.regs 4 = vCap := hregs ▸ h4
  have h5' : st.regs 5 = eCap := hregs ▸ h5
  have h6' : st.regs 6 = r0 := hregs ▸ h6
  have hTsz : tBlockSize vCap eCap 0 = 8 + (4 + 7 * vCap + 9) + eCap + 4 := by
    simp [tBlockSize, tHdrSize, dynGraphSize]
  have htOrig : tOrigIdBase tPtr vCap 0 = tPtr + 8 + (13 + 7 * vCap) := by
    simp [tOrigIdBase, tDgTPtr, tHdrSize, dynGraphSize]; omega
  have htPi : tPiBase tPtr vCap 0 = tPtr + 8 + (13 + 7 * vCap) := by simp [tPiBase, htOrig]
  have htFT : tFrozenTailBase tPtr vCap 0 = tPtr + 8 + (13 + 7 * vCap) := by simp [tFrozenTailBase, htPi]
  have htFH : tFrozenHeadBase tPtr vCap 0 = tPtr + 8 + (13 + 7 * vCap) := by simp [tFrozenHeadBase, htFT]
  have htIdx : tIdxOfEdgeBase tPtr vCap 0 = tPtr + 8 + (13 + 7 * vCap) := by simp [tIdxOfEdgeBase, htFH]
  have htSplit : tSplitScratchBase tPtr vCap eCap 0 = tPtr + 8 + (13 + 7 * vCap) + eCap := by
    simp [tSplitScratchBase, htIdx]
  refine runs_start_le ?_
  unfold storeOneTBlock
  refine runs_seq_assign_le (v := tPtr + 8) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := tPtr + 8 + (13 + 7 * vCap)) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := tPtr + 8 + (13 + 7 * vCap) + eCap) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := tPtr + 1) (v := tPtr + 8) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := tPtr + 2) (v := tPtr + 8 + (13 + 7 * vCap)) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := tPtr + 3) (v := tPtr + 8 + (13 + 7 * vCap)) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := tPtr + 4) (v := tPtr + 8 + (13 + 7 * vCap)) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := tPtr + 5) (v := tPtr + 8 + (13 + 7 * vCap)) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := tPtr + 6) (v := tPtr + 8 + (13 + 7 * vCap)) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := tPtr + 7) (v := tPtr + 8 + (13 + 7 * vCap) + eCap) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_; dsimp only
  refine runs_triple_le (storeOneVertDg_triple (tPtr + 8) vCap 1 r0 _ _ hw16 hr0
    (by dsimp [dynGraphSize]; omega) (fun i hi => by
      dsimp only
      simp (disch := omega) only [Function.update_of_ne]
      exact hzero (tPtr + 8 + i) (by omega) (by dsimp [dynGraphSize] at hi; omega)))
    ⟨rfl, by dsimp only; simp (disch := omega) only [Function.update_of_ne, Function.update_self],
      by dsimp only; simp (disch := omega) only [Function.update_of_ne]; exact h4',
      by dsimp only; exact Function.update_self _ _ _,
      by dsimp only; simp (disch := omega) only [Function.update_of_ne]; exact h6', rfl⟩
    (fun o st2 h2 => ?_) (by wram_cost)
  cases o with
  | returned _ => exact False.elim h2
  | normal =>
    rcases h2 with ⟨h2_regs, hdgT, hfr2⟩
    refine ⟨fun r hr => by
        rw [h2_regs]; dsimp only
        simp (disch := omega) only [Function.update_of_ne]
        exact congrFun hregs r,
      ?_, ?_⟩
    · intro G T hGV _ hTE
      refine tBlockAt_oneVert ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hdgT hGV hTE
      · rw [hfr2 _ (Or.inl (by omega))]; dsimp only
        simp (disch := omega) only [Function.update_of_ne]
        exact hzero _ (by omega) (by omega)
      · rw [hfr2 _ (Or.inl (by omega))]; dsimp only [tDgTPtr, tHdrSize]
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [hfr2 _ (Or.inl (by omega)), htOrig]; dsimp only
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [hfr2 _ (Or.inl (by omega)), htPi]; dsimp only
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [hfr2 _ (Or.inl (by omega)), htFT]; dsimp only
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [hfr2 _ (Or.inl (by omega)), htFH]; dsimp only
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [hfr2 _ (Or.inl (by omega)), htIdx]; dsimp only
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [hfr2 _ (Or.inl (by omega)), htSplit]; dsimp only
        exact Function.update_self _ _ _
      · intro e he
        rw [htIdx, hfr2 _ (Or.inr (by dsimp [dynGraphSize]; omega))]; dsimp only
        clear hdgT hfr2 h2_regs hGV hTE
        simp (disch := omega) only [Function.update_of_ne]
        exact hzero _ (by omega) (by omega)
    · intro z hz
      rw [hfr2 z (by dsimp [dynGraphSize]; omega)]; dsimp only
      clear hdgT hfr2 h2_regs
      simp (disch := omega) only [Function.update_of_ne]

private lemma fAncAt_oneVert {mem : ℕ → ℕ} {fAncPtr vCap r0 : ℕ} (hr0 : r0 < vCap)
    (h0 : mem (fAncPtr + 0) = 1)
    (h1 : mem (fAncPtr + 1) = fIsRootBase fAncPtr)
    (h2 : mem (fAncPtr + 2) = fRListBase fAncPtr vCap)
    (h3 : mem (fAncPtr + 3) = fCompIdBase fAncPtr vCap)
    (h4 : mem (fAncPtr + 4) = fCompRootBase fAncPtr vCap)
    (h5 : mem (fAncPtr + 5) = fCompSizeBase fAncPtr vCap)
    (hisR : ∀ v < vCap, mem (fIsRootBase fAncPtr + v) = if v = r0 then 1 else 0)
    (hrL : mem (fRListBase fAncPtr vCap) = r0)
    (hcid : mem (fCompIdBase fAncPtr vCap + r0) = r0)
    (hcr : mem (fCompRootBase fAncPtr vCap + r0) = r0)
    (hcs : mem (fCompSizeBase fAncPtr vCap + r0) = 1)
    {RF : RootedForest} (hFV : RF.F.V = {r0}) (hR : RF.R = {r0}) :
    FAncAt mem fAncPtr vCap RF [r0] (fun _ => r0) (fun _ => r0) (fun _ => 1) {r0} := by
  classical
  have hRc : RF.R.card = 1 := by rw [hR]; simp
  refine ⟨by rw [hRc]; exact h0, h1, h2, h3, h4, h5,
    fun v hv => by rw [hFV, Finset.mem_singleton] at hv; subst hv; exact hr0,
    by simp [hRc], List.nodup_singleton r0, by simp [hR], by simp; omega,
    fun i hi => by
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi; simpa using hrL,
    fun v hv => by rw [hisR v hv, hR]; simp,
    by rw [hR], ?_, ?_⟩
  · intro c hc
    rw [Finset.mem_singleton] at hc
    rcases hc with rfl
    refine ⟨hr0, hcr, by rw [hR]; exact Finset.mem_singleton_self _, rfl, hcs, le_rfl, ?_⟩
    have hfilt : RF.F.V.filter (fun u => RF.F.Connected u c) = {c} := by
      ext u
      simp only [Finset.mem_filter, hFV, Finset.mem_singleton, and_iff_left_iff_imp]
      intro hu; rcases hu with rfl
      exact ⟨[], MGraph.IsWalk.nil _⟩
    rw [hfilt]; simp
  · intro v hv
    rw [hFV, Finset.mem_singleton] at hv
    rcases hv with rfl
    dsimp only
    rw [hcid]
    exact ⟨rfl, Finset.mem_singleton_self _, ⟨[], MGraph.IsWalk.nil _⟩⟩

/-- Writes the one-root `FAnc` block at `reg 2` using scratch regs `12..16`.
Expects regs `2=fAncPtr, 4=vCap, 6=r0`. -/
def storeOneFAnc : Stmt :=
  .assign 12 (.bin .add (.reg 2) (.const 6)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 4)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 4)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 4)) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 4)) ;;
  .store (.reg 2) (.const 1) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 12) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.reg 13) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 14) ;;
  .store (.bin .add (.reg 2) (.const 4)) (.reg 15) ;;
  .store (.bin .add (.reg 2) (.const 5)) (.reg 16) ;;
  .store (.bin .add (.reg 12) (.reg 6)) (.const 1) ;;
  .store (.reg 13) (.reg 6) ;;
  .store (.bin .add (.reg 14) (.reg 6)) (.reg 6) ;;
  .store (.bin .add (.reg 15) (.reg 6)) (.reg 6) ;;
  .store (.bin .add (.reg 16) (.reg 6)) (.const 1)

lemma storeOneFAnc_noRand : storeOneFAnc.NoRand := by
  simp [storeOneFAnc, Stmt.NoRand]

private lemma storeOneFAnc_triple {w : ℕ} {p : Program}
    (fAncPtr vCap r0 : ℕ) (regs₀ mem₀ : ℕ → ℕ)
    (hw16 : 16 ≤ 2 ^ w) (hr0 : r0 < vCap)
    (hbd : fAncPtr + fAncSize vCap < 2 ^ w)
    (hzero : ∀ a, fAncPtr ≤ a → a < fAncPtr + fAncSize vCap → mem₀ a = 0) :
    Triple w p
      (fun st => st.regs = regs₀ ∧ regs₀ 2 = fAncPtr ∧ regs₀ 4 = vCap ∧ regs₀ 6 = r0 ∧
        st.mem = mem₀)
      storeOneFAnc
      (normalPost fun st =>
        (∀ r ≤ 6, st.regs r = regs₀ r) ∧
        (∀ RF : RootedForest, RF.F.V = {r0} → RF.F.E = ∅ → RF.R = {r0} →
          FAncAt st.mem fAncPtr vCap RF [r0] (fun _ => r0) (fun _ => r0) (fun _ => 1) {r0}) ∧
        (∀ z, z < fAncPtr ∨ fAncPtr + fAncSize vCap ≤ z → st.mem z = mem₀ z))
      (fun _ => 140) := by
  intro st ω ⟨hregs, h2, h4, h6, hmem⟩
  subst hmem
  have h2' : st.regs 2 = fAncPtr := hregs ▸ h2
  have h4' : st.regs 4 = vCap := hregs ▸ h4
  have h6' : st.regs 6 = r0 := hregs ▸ h6
  have hFAsz : fAncSize vCap = 6 + 5 * vCap := rfl
  have hfa1 : fIsRootBase fAncPtr = fAncPtr + 6 := rfl
  have hfa2 : fRListBase fAncPtr vCap = fAncPtr + 6 + vCap := rfl
  have hfa3 : fCompIdBase fAncPtr vCap = fAncPtr + 6 + vCap + vCap := by
    simp [fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]
  have hfa4 : fCompRootBase fAncPtr vCap = fAncPtr + 6 + vCap + vCap + vCap := by
    simp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]
  have hfa5 : fCompSizeBase fAncPtr vCap = fAncPtr + 6 + vCap + vCap + vCap + vCap := by
    simp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]
  refine runs_start_le ?_
  unfold storeOneFAnc
  refine runs_seq_assign_le (v := fAncPtr + 6) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := fAncPtr + 6 + vCap) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := fAncPtr + 6 + vCap + vCap) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := fAncPtr + 6 + vCap + vCap + vCap) (by eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := fAncPtr + 6 + vCap + vCap + vCap + vCap) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr) (v := 1) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 1) (v := fAncPtr + 6) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 2) (v := fAncPtr + 6 + vCap) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 3) (v := fAncPtr + 6 + vCap + vCap) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 4) (v := fAncPtr + 6 + vCap + vCap + vCap) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 5) (v := fAncPtr + 6 + vCap + vCap + vCap + vCap) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 6 + r0) (v := 1) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 6 + vCap) (v := r0) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 6 + vCap + vCap + r0) (v := r0) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + 6 + vCap + vCap + vCap + r0) (v := r0) (by eval_expr) (by eval_expr) ?_; dsimp only
  refine runs_store_le (x := fAncPtr + 6 + vCap + vCap + vCap + vCap + r0) (v := 1)
    (by eval_expr) (by eval_expr) ?_ (by wram_cost)
  dsimp only
  refine ⟨fun r hr => by simp (disch := omega) only [Function.update_of_ne]; exact congrFun hregs r,
    fun RF hFV _ hR => ?_, ?_⟩
  · refine fAncAt_oneVert hr0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hFV hR
    · simp (disch := omega) only [Nat.add_zero, Function.update_of_ne, Function.update_self]
    · rw [hfa1]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · rw [hfa2]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · rw [hfa3]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · rw [hfa4]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · rw [hfa5]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · intro v hv
      rw [hfa1]
      by_cases hvr : v = r0
      · subst hvr
        rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hvr)]
        simp (disch := omega) only [Function.update_of_ne]
        exact hzero _ (by omega) (by omega)
    · rw [hfa2]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · rw [hfa3]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · rw [hfa4]; simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · rw [hfa5]; exact Function.update_self _ _ _
  · intro z hz
    simp (disch := omega) only [Function.update_of_ne]

private lemma wBlockAt_oneVert {mem : ℕ → ℕ} {wPtr : ℕ}
    (h0 : mem (wPtr + 0) = 0)
    (h1 : mem (wPtr + 1) = wVertOffBase wPtr)
    (h2 : mem (wPtr + 2) = wVertsBase wPtr 1)
    (h3 : mem (wPtr + 3) = wEdgeOffBase wPtr 1)
    (h4 : mem (wPtr + 4) = wEdgesBase wPtr 1)
    (h5 : mem (wPtr + 5) = 0)
    (h6 : mem (wPtr + 6) = 0)
    (hvo0 : mem (wVertOffBase wPtr + 0) = 0)
    (heo0 : mem (wEdgeOffBase wPtr 1 + 0) = 0)
    (F : MGraph) :
    WBlockAt mem wPtr 1 ∅ F := by
  dsimp only [WBlockAt, wOffNumPieces, wOffTotalVerts, wOffTotalEdges,
    wOffVertOffPtr, wOffVertsPtr, wOffEdgeOffPtr, wOffEdgesPtr]
  rw [h0, h5, h6]
  exact ⟨h1, h2, h3, h4, by omega, by omega, by omega, hvo0, hvo0, heo0, heo0,
    [], rfl, List.nodup_nil, by simp, fun _ hi => by simp at hi⟩

/-- Writes the empty `W` block at `reg 3` (`n₀ = 1`). Does not modify any registers. -/
def storeOneWBlock : Stmt :=
  .store (.bin .add (.reg 3) (.const 1)) (.bin .add (.reg 3) (.const 7)) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 3) (.const 9)) ;;
  .store (.bin .add (.reg 3) (.const 3)) (.bin .add (.reg 3) (.const 11)) ;;
  .store (.bin .add (.reg 3) (.const 4)) (.bin .add (.reg 3) (.const 13))

lemma storeOneWBlock_noRand : storeOneWBlock.NoRand := by
  simp [storeOneWBlock, Stmt.NoRand]

private lemma storeOneWBlock_triple {w : ℕ} {p : Program}
    (wPtr : ℕ) (mem₀ : ℕ → ℕ)
    (hw16 : 16 ≤ 2 ^ w) (hbd : wPtr + wBlockSize 1 < 2 ^ w)
    (hzero : ∀ a, wPtr ≤ a → a < wPtr + wBlockSize 1 → mem₀ a = 0) :
    Triple w p
      (fun st => st.regs 3 = wPtr ∧ st.mem = mem₀)
      storeOneWBlock
      (normalPost fun st =>
        (∀ F : MGraph, WBlockAt st.mem wPtr 1 ∅ F) ∧
        (∀ z, z < wPtr ∨ wPtr + wBlockSize 1 ≤ z → st.mem z = mem₀ z))
      (fun _ => 50) := by
  intro st ω ⟨h3, hmem⟩
  subst hmem
  have hWsz : wBlockSize 1 = 14 := by decide
  refine runs_start_le ?_
  unfold storeOneWBlock
  refine runs_seq_store_le (x := wPtr + 1) (v := wPtr + 7) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 2) (v := wPtr + 9) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 3) (v := wPtr + 11) (by eval_expr) (by eval_expr) ?_
  refine runs_store_le (x := wPtr + 4) (v := wPtr + 13) (by eval_expr) (by eval_expr) ?_
    (by wram_cost)
  dsimp only
  refine ⟨fun F => wBlockAt_oneVert ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ F, ?_⟩
  · simp (disch := omega) only [Function.update_of_ne]
    exact hzero _ (by omega) (by omega)
  · simp (disch := omega) only [Function.update_of_ne, Function.update_self]; rfl
  · simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    simp [wVertsBase, wVertOffBase, wHdrSize]
  · simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    simp [wEdgeOffBase, wVertsBase, wVertOffBase, wHdrSize]
  · simp only [Function.update_self, wEdgesBase, wEdgeOffBase, wVertsBase, wVertOffBase, wHdrSize]
  · simp (disch := omega) only [Function.update_of_ne]
    exact hzero _ (by omega) (by omega)
  · simp (disch := omega) only [Function.update_of_ne]
    exact hzero _ (by omega) (by omega)
  · simp only [wVertOffBase, wHdrSize]
    simp (disch := omega) only [Function.update_of_ne]
    exact hzero _ (by omega) (by omega)
  · simp only [wEdgeOffBase, wVertsBase, wVertOffBase, wHdrSize]
    simp (disch := omega) only [Function.update_of_ne]
    exact hzero _ (by omega) (by omega)
  · intro z hz
    simp (disch := omega) only [Function.update_of_ne]

/-! ## `initOneBlocksProc`: static T, F, FAnc, and W blocks for `n₀ = 1` -/

/-- Args (regs `0..6`): `[tPtr, fPtr, fAncPtr, wPtr, vCap, eCap, r0]`.
Writes the `T` block (`tM = 0`), one-vertex `F` graph, one-root `FAnc` block, and empty `W` block
onto zeroed static memory. -/
def initOneBlocksProc : Stmt :=
  storeOneTBlock ;;
  .assign 11 (.bin .add (.bin .mul (.const 3) (.reg 5)) (.const 1)) ;;
  storeOneVertDg 1 4 11 6 ;;
  storeOneFAnc ;;
  storeOneWBlock ;;
  .ret (.const 0)

lemma initOneBlocksProc_noRand : initOneBlocksProc.NoRand := by
  simp [initOneBlocksProc, storeOneTBlock_noRand, storeOneVertDg_noRand,
    storeOneFAnc_noRand, storeOneWBlock_noRand, Stmt.NoRand]

def initOneBlocksContract (w : ℕ) : Contract where
  pre args mem := ∃ tPtr fPtr fAncPtr wPtr vCap eCap r0,
    args = [tPtr, fPtr, fAncPtr, wPtr, vCap, eCap, r0] ∧
    16 ≤ 2 ^ w ∧ r0 < vCap ∧ 1 ≤ eCap ∧
    tPtr + tBlockSize vCap eCap 0 ≤ fPtr ∧
    fPtr + dynGraphSize vCap (fECap eCap 1) ≤ fAncPtr ∧
    fAncPtr + fAncSize vCap ≤ wPtr ∧
    wPtr + wBlockSize 1 < 2 ^ w ∧
    (∀ a, tPtr ≤ a → a < wPtr + wBlockSize 1 → mem a = 0)
  post args mem ret mem' := ∃ tPtr fPtr fAncPtr wPtr vCap eCap r0,
    args = [tPtr, fPtr, fAncPtr, wPtr, vCap, eCap, r0] ∧
    ret = 0 ∧
    (∀ G T : MGraph, G.V = {r0} → T.V = {r0} → T.E = ∅ →
      TBlockAt mem' tPtr vCap eCap 0 G T T (fun _ => 0) []) ∧
    (∀ F : MGraph, F.V = {r0} → F.E = ∅ →
      DynGraphAt mem' fPtr vCap (fECap eCap 1) F) ∧
    (∀ RF : RootedForest, RF.F.V = {r0} → RF.F.E = ∅ → RF.R = {r0} →
      FAncAt mem' fAncPtr vCap RF [r0] (fun _ => r0) (fun _ => r0) (fun _ => 1) {r0}) ∧
    (∀ F : MGraph, WBlockAt mem' wPtr 1 ∅ F) ∧
    (∀ a, a < tPtr ∨ wPtr + wBlockSize 1 ≤ a → mem' a = mem a)
  cost _ _ := 600

theorem initOneBlocks_meetsContract {w f : ℕ} {p : Program}
    (hp : p.procs[f]? = some initOneBlocksProc) :
    MeetsContract w p f (initOneBlocksContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨tPtr, fPtr, fAncPtr, wPtr, vCap, eCap, r0, rfl, hw16, hr0, hec1,
    hl1, hl2, hl3, hl4, hzero⟩ := hpre
  have hFsz : dynGraphSize vCap (fECap eCap 1) = 4 + 7 * vCap + 9 * (3 * eCap + 1) := rfl
  refine runs_start_le ?_
  unfold initOneBlocksProc
  refine runs_seq_triple_le (storeOneTBlock_triple tPtr vCap eCap r0 _ mem hw16 hr0 (by omega)
    (fun a ha1 ha2 => hzero a ha1 (by omega)))
    ⟨rfl, by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], rfl⟩ fun st1 h1 => ?_
  rcases h1 with ⟨hr1, hT1, hfr1⟩
  have h1_1 : st1.regs 1 = fPtr := (hr1 1 (by omega)).trans (by simp [startState])
  have h1_2 : st1.regs 2 = fAncPtr := (hr1 2 (by omega)).trans (by simp [startState])
  have h1_3 : st1.regs 3 = wPtr := (hr1 3 (by omega)).trans (by simp [startState])
  have h1_4 : st1.regs 4 = vCap := (hr1 4 (by omega)).trans (by simp [startState])
  have h1_5 : st1.regs 5 = eCap := (hr1 5 (by omega)).trans (by simp [startState])
  have h1_6 : st1.regs 6 = r0 := (hr1 6 (by omega)).trans (by simp [startState])
  refine runs_seq_assign_le (v := 3 * eCap + 1) (by eval_expr) ?_
  refine runs_seq_triple_le (storeOneVertDg_triple fPtr vCap (fECap eCap 1) r0 _ st1.mem
    hw16 hr0 (by omega) (fun i hi => (hfr1 _ (Or.inr (by omega))).trans
      (hzero _ (by omega) (by omega))))
    ⟨rfl, by simp [h1_1], by simp [h1_4], by simp [fECap], by simp [h1_6], rfl⟩ fun st2 h2 => ?_
  rcases h2 with ⟨hr2, hdgF2, hfr2⟩
  have h2_2 : st2.regs 2 = fAncPtr := by rw [hr2]; simp [h1_2]
  have h2_3 : st2.regs 3 = wPtr := by rw [hr2]; simp [h1_3]
  have h2_4 : st2.regs 4 = vCap := by rw [hr2]; simp [h1_4]
  have h2_6 : st2.regs 6 = r0 := by rw [hr2]; simp [h1_6]
  refine runs_seq_triple_le (storeOneFAnc_triple fAncPtr vCap r0 st2.regs st2.mem
    hw16 hr0 (by omega) (fun a ha1 ha2 => (hfr2 a (Or.inr (by omega))).trans
      ((hfr1 a (Or.inr (by omega))).trans (hzero a (by omega) (by omega)))))
    ⟨rfl, h2_2, h2_4, h2_6, rfl⟩ fun st3 h3 => ?_
  rcases h3 with ⟨hr3, hFA3, hfr3⟩
  have h3_3 : st3.regs 3 = wPtr := (hr3 3 (by omega)).trans h2_3
  refine runs_seq_triple_le (storeOneWBlock_triple wPtr st3.mem hw16 hl4
    (fun a ha1 ha2 => (hfr3 a (Or.inr (by omega))).trans
      ((hfr2 a (Or.inr (by omega))).trans ((hfr1 a (Or.inr (by omega))).trans
        (hzero a (by omega) ha2)))))
    ⟨h3_3, rfl⟩ fun st4 h4 => ?_
  rcases h4 with ⟨hW4, hfr4⟩
  refine runs_ret_le (v := 0) (by eval_expr) ?_
    (by simp only [initOneBlocksContract]; wram_cost)
  refine ⟨tPtr, fPtr, fAncPtr, wPtr, vCap, eCap, r0, rfl, rfl, ?_, ?_, ?_, hW4, ?_⟩
  · intro G T hGV hTV hTE
    exact (hT1 G T hGV hTV hTE).of_agree fun a ha1 ha2 =>
      (hfr4 a (Or.inl (by omega))).trans ((hfr3 a (Or.inl (by omega))).trans
        (hfr2 a (Or.inl (by omega))))
  · intro F hFV hFE
    exact (hdgF2 F hFV hFE).of_agree fun a ha1 ha2 =>
      (hfr4 a (Or.inl (by omega))).trans (hfr3 a (Or.inl (by omega)))
  · intro RF hFV hFE hR
    exact (hFA3 RF hFV hFE hR).of_agree fun a ha1 ha2 =>
      hfr4 a (Or.inl (by omega))
  · intro a ha
    rcases ha with ha | ha
    · rw [hfr4 a (Or.inl (by omega)), hfr3 a (Or.inl (by omega)),
        hfr2 a (Or.inl (by omega)), hfr1 a (Or.inl ha)]
    · rw [hfr4 a (Or.inr ha), hfr3 a (Or.inr (by omega)),
        hfr2 a (Or.inr (by omega)), hfr1 a (Or.inr (by omega))]

/-! ## `initOneWstrProc`: writing `6 / 1` stretch arrays for `n₀ = 1` -/

/-- Straight-line stores writing `ds` at `regs[rDst] + idx, regs[rDst] + idx + 1, ...`. -/
def emitLimbsAt (rDst : ℕ) : List ℕ → ℕ → Stmt
  | [], _ => .nop
  | d :: ds, idx =>
    .store (.bin .add (.reg rDst) (.const idx)) (.const d) ;;
    emitLimbsAt rDst ds (idx + 1)

lemma emitLimbsAt_noRand (rDst : ℕ) : ∀ ds idx, (emitLimbsAt rDst ds idx).NoRand
  | [], _ => by simp [emitLimbsAt, Stmt.NoRand]
  | _ :: ds, idx => by simp [emitLimbsAt, Stmt.NoRand, emitLimbsAt_noRand rDst ds (idx + 1)]

private lemma emitLimbsAt_triple {w rDst dst idx : ℕ} {p : Program}
    (ds : List ℕ) (regs₀ mem₀ : ℕ → ℕ)
    (hd : ∀ d ∈ ds, d < 2 ^ w) (hbd : dst + idx + ds.length < 2 ^ w) :
    Triple w p
      (fun st => st.regs = regs₀ ∧ regs₀ rDst = dst ∧ st.mem = mem₀)
      (emitLimbsAt rDst ds idx)
      (normalPost fun st => st.regs = regs₀ ∧
        (∀ j (hj : j < ds.length), st.mem (dst + idx + j) = ds[j]'hj) ∧
        (∀ z, z < dst + idx ∨ dst + idx + ds.length ≤ z → st.mem z = mem₀ z))
      (fun _ => 10 * ds.length + 2) := by
  induction ds generalizing idx mem₀ with
  | nil =>
    intro st ω ⟨hregs, _, hmem⟩
    subst hmem
    exact runs_start_le (runs_nop_le ⟨hregs, fun _ hj => by simp at hj, fun _ _ => rfl⟩
      (by simp only [List.length_nil]; omega))
  | cons d ds ih =>
    intro st ω ⟨hregs, hdst, hmem⟩
    subst hmem
    simp only [List.length_cons] at hbd
    have hdw : d < 2 ^ w := hd d List.mem_cons_self
    have hdst' : st.regs rDst = dst := hregs ▸ hdst
    let mem₁ := Function.update st.mem (dst + idx) d
    refine runs_start_le ?_
    unfold emitLimbsAt
    refine runs_seq_store_le (x := dst + idx) (v := d) (by eval_expr) (by eval_expr) ?_
    refine runs_triple_le (ih (idx := idx + 1) (mem₀ := mem₁)
      (fun x hx => hd x (List.mem_cons_of_mem d hx)) (by omega))
      ⟨hregs, hdst, rfl⟩ (fun o st' h => ?_) (by simp only [List.length_cons]; wram_cost)
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨hregs', hset, hfr⟩
      refine ⟨hregs', fun j hj => ?_, fun z hz => ?_⟩
      · cases j with
        | zero =>
          simpa using (hfr (dst + idx) (Or.inl (by omega))).trans (by simp [mem₁])
        | succ j =>
          have hj' : j < ds.length := by simp only [List.length_cons] at hj; omega
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hset j hj'
      · have hz' : z < dst + (idx + 1) ∨ dst + (idx + 1) + ds.length ≤ z := by
          simp only [List.length_cons] at hz; omega
        rw [hfr z hz']
        exact Function.update_of_ne (show z ≠ dst + idx by simp only [List.length_cons] at hz; omega)
          d st.mem

private lemma listVal_append_zeros' (h : ℕ) :
    ∀ (ds : List ℕ) (k : ℕ), listVal h (ds ++ List.replicate k 0) = listVal h ds
  | [], k => by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.nil_append] at ih
      simp [List.replicate_succ, listVal, ih]
  | d :: ds, k => by
    simp [listVal, listVal_append_zeros' h ds k]

private lemma valid_intVal_of_natLimbs {mem : ℕ → ℕ} {dst h L val : ℕ}
    (hh : 1 ≤ h) (hlen : (natLimbs h val).length ≤ L) (hcap : 2 * val < capacity h L)
    (hhead : ∀ j (hj : j < (natLimbs h val).length), mem (dst + j) = (natLimbs h val)[j]'hj)
    (htail : ∀ j, (natLimbs h val).length ≤ j → j < L → mem (dst + j) = 0) :
    Num.Valid mem dst h L ∧ Num.intVal mem dst h L = (val : ℤ) := by
  have hval : Num.Valid mem dst h L := by
    intro j hj
    by_cases hlt : j < (natLimbs h val).length
    · rw [hhead j hlt]
      exact natLimbs_lt _ (List.getElem_mem hlt)
    · rw [htail j (by omega) hj]
      exact base_pos h
  have hlat : ListAt mem dst (natLimbs h val ++ List.replicate (L - (natLimbs h val).length) 0) := by
    intro i hi
    simp only [List.length_append, List.length_replicate] at hi
    by_cases hlt : i < (natLimbs h val).length
    · rw [List.getElem_append_left hlt]; exact hhead i hlt
    · rw [List.getElem_append_right (by omega)]
      simp [htail i (by omega) (by omega)]
  have hlen_app : (natLimbs h val ++ List.replicate (L - (natLimbs h val).length) 0).length = L := by
    simp; omega
  have huv : unsignedVal mem dst h L = val := by
    rw [← hlen_app, unsignedVal_listAt hlat, listVal_append_zeros', natLimbs_listVal (by omega)]
  refine ⟨hval, ?_⟩
  unfold Num.intVal Num.signedVal
  rw [huv, ite_eq_right_iff.mpr (fun hc => by omega), sub_zero]

private lemma unsignedVal_zero {mem : ℕ → ℕ} {dst h : ℕ} :
    ∀ L, (∀ j < L, mem (dst + j) = 0) → unsignedVal mem dst h L = 0
  | 0, _ => rfl
  | L + 1, hz => by
    unfold unsignedVal
    rw [show mem dst = 0 by simpa using hz 0 (Nat.succ_pos L),
      unsignedVal_zero L (fun j hj => by
        rw [show dst + 1 + j = dst + (j + 1) by omega]; exact hz (j + 1) (by omega))]
    simp

private lemma valid_intVal_one {mem : ℕ → ℕ} {dst h L : ℕ} (hh : 1 ≤ h) (hL : 1 ≤ L)
    (hcap : 2 < capacity h L) (h0 : mem dst = 1) (htail : ∀ j, 1 ≤ j → j < L → mem (dst + j) = 0) :
    Num.Valid mem dst h L ∧ Num.intVal mem dst h L = 1 := by
  have h1b : 1 < base h := by
    unfold base
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
    omega
  have hval : Num.Valid mem dst h L := by
    intro j hj
    cases j with
    | zero => simpa [h0] using h1b
    | succ j => rw [htail (j + 1) (by omega) hj]; exact base_pos h
  have huv : unsignedVal mem dst h L = 1 := by
    cases L with
    | zero => omega
    | succ L' =>
      unfold unsignedVal
      rw [h0, unsignedVal_zero L' (fun j hj => by
        rw [show dst + 1 + j = dst + (j + 1) by omega]; exact htail (j + 1) (by omega) (by omega))]
      simp
  refine ⟨hval, ?_⟩
  unfold Num.intVal Num.signedVal
  rw [huv, ite_eq_right_iff.mpr (fun hc => by omega), sub_zero]
  rfl

lemma natLimbs_six_len_le {h : ℕ} (hh : 1 ≤ h) : (natLimbs h 6).length ≤ 3 := by
  rw [natLimbs_length_le_iff (by omega)]
  have h2 : 2 ≤ base h := by
    unfold base
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
    simpa using this
  calc 6 < 2 ^ 3 := by decide
    _ ≤ (base h) ^ 3 := Nat.pow_le_pow_left h2 3

/-- Args (regs `0..4`): `[eListPtr, m0, numSt, denSt, L_w]`.
For each edge `e` in `eList` at `eListPtr`, writes `6` at `numSt + e * L_w` and `1` at
`denSt + e * L_w` onto zeroed arrays. -/
def initOneWstrProc (h : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 1) (
    .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
    .assign 7 (.bin .mul (.reg 6) (.reg 4)) ;;
    .assign 8 (.bin .add (.reg 2) (.reg 7)) ;;
    emitLimbsAt 8 (natLimbs h 6) 0 ;;
    .store (.bin .add (.reg 3) (.reg 7)) (.const 1)
  ) ;;
  .ret (.const 0)

lemma initOneWstrProc_noRand (h : ℕ) : (initOneWstrProc h).NoRand := by
  simp [initOneWstrProc, forRange, forUp, emitLimbsAt_noRand, Stmt.NoRand]

def initOneWstrContract (w h : ℕ) : Contract where
  pre args mem := ∃ (eListPtr m0 numSt denSt L_w eCap : ℕ) (eList : List ℕ),
    args = [eListPtr, m0, numSt, denSt, L_w] ∧
    1 ≤ h ∧ 3 * h + 2 ≤ w ∧ 1 ≤ L_w ∧ 1 ≤ eCap ∧
    (natLimbs h 6).length ≤ L_w ∧ 12 < capacity h L_w ∧
    eList.length = m0 ∧ eList.Nodup ∧ (∀ e ∈ eList, e < eCap) ∧
    ListAt mem eListPtr eList ∧
    eListPtr + m0 ≤ numSt ∧ numSt + eCap * L_w = denSt ∧ denSt + eCap * L_w < 2 ^ w ∧
    (∀ i < eCap * L_w, mem (numSt + i) = 0) ∧
    (∀ i < eCap * L_w, mem (denSt + i) = 0)
  post args mem ret mem' := ∃ (eListPtr m0 numSt denSt L_w : ℕ),
    args = [eListPtr, m0, numSt, denSt, L_w] ∧
    ret = 0 ∧
    (∀ i < m0,
      let e := mem (eListPtr + i)
      Num.Valid mem' (numSt + e * L_w) h L_w ∧ Num.intVal mem' (numSt + e * L_w) h L_w = 6 ∧
      Num.Valid mem' (denSt + e * L_w) h L_w ∧ Num.intVal mem' (denSt + e * L_w) h L_w = 1) ∧
    (∀ a, a < numSt ∨ denSt + (denSt - numSt) ≤ a → mem' a = mem a)
  cost args _ := 80 * args.getD 1 0 + 50

set_option maxHeartbeats 1600000 in
theorem initOneWstr_meetsContract {w h f : ℕ} {p : Program}
    (hp : p.procs[f]? = some (initOneWstrProc h)) :
    MeetsContract w p f (initOneWstrContract w h) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨eListPtr, m0, numSt, denSt, L_w, eCap, eList, rfl, hh, hhw, hLw, hec1,
    h6len, h12cap, helen, hend, helt, hlat, hl1, hl2, hl3, hzn, hzd⟩ := hpre
  have h2w : 2 ^ h < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hw1 : 1 < 2 ^ w := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hlen3 : (natLimbs h 6).length ≤ 3 := natLimbs_six_len_le hh
  have hd_lt : ∀ d ∈ natLimbs h 6, d < 2 ^ w := fun d hd =>
    lt_trans (natLimbs_lt d hd) h2w
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = eListPtr ∧ st.regs 1 = m0 ∧ st.regs 2 = numSt ∧ st.regs 3 = denSt ∧
    st.regs 4 = L_w ∧ st.regs 5 = i ∧
    (∀ k (hk : k < i), ∀ (hkm : k < eList.length),
      let e := eList[k]'hkm
      Num.Valid st.mem (numSt + e * L_w) h L_w ∧ Num.intVal st.mem (numSt + e * L_w) h L_w = 6 ∧
      Num.Valid st.mem (denSt + e * L_w) h L_w ∧ Num.intVal st.mem (denSt + e * L_w) h L_w = 1) ∧
    (∀ e < eCap, (∀ k (hk : k < i), ∀ (hkm : k < eList.length), eList[k]'hkm ≠ e) →
      (∀ j < L_w, st.mem (numSt + e * L_w + j) = 0 ∧ st.mem (denSt + e * L_w + j) = 0)) ∧
    (∀ a, (a < numSt ∨ numSt + eCap * L_w ≤ a) → (a < denSt ∨ denSt + eCap * L_w ≤ a) →
      st.mem a = mem a)
  refine runs_start_le ?_
  unfold initOneWstrProc
  have hloop : Triple w p (fun st => st = startState [eListPtr, m0, numSt, denSt, L_w] mem pos)
      (forRange 5 (.const 0) (.reg 1) (
        .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
        .assign 7 (.bin .mul (.reg 6) (.reg 4)) ;;
        .assign 8 (.bin .add (.reg 2) (.reg 7)) ;;
        emitLimbsAt 8 (natLimbs h 6) 0 ;;
        .store (.bin .add (.reg 3) (.reg 7)) (.const 1)))
      (normalPost (Inv m0)) (fun _ => 75 * m0 + 20) := by
    refine (Triple.forRange_const 65 0 m0 (Nat.zero_le m0) hw1 (fun _ => by omega)
      (fun st hst => by
        subst hst
        refine ⟨by eval_expr, by simp [startState], by simp [startState], by simp [startState],
          by simp [startState], by simp [startState], by simp, fun _ hk => by omega, ?_,
          fun _ _ _ => rfl⟩
        intro e he _ j hj
        have hmul : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w he
        rw [Nat.add_mul, Nat.one_mul] at hmul
        rw [Nat.add_assoc, Nat.add_assoc]
        exact ⟨hzn _ (by omega), hzd _ (by omega)⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
      (fun i _ hi st ω' hinv => by
        rcases hinv with ⟨h0, h1, h2, h3, h4, hr5, hdone, hrem, hfr⟩
        have him : i < eList.length := by omega
        set e := eList[i]'him with he_def
        have he_lt : e < eCap := helt e (List.getElem_mem him)
        have he_mem : st.mem (eListPtr + i) = e :=
          (hfr (eListPtr + i) (Or.inl (by omega)) (Or.inl (by omega))).trans (hlat i him)
        have hmul_lt : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w he_lt
        have heLw : e * L_w + L_w ≤ eCap * L_w := by rw [Nat.add_mul, Nat.one_mul] at hmul_lt; exact hmul_lt
        have he_fresh : ∀ k (hk : k < i), ∀ (hkm : k < eList.length), eList[k]'hkm ≠ e := by
          intro k hk hkm hEq
          have hfin : (⟨k, hkm⟩ : Fin eList.length) = ⟨i, him⟩ :=
            (List.nodup_iff_injective_getElem.mp hend) hEq
          have : k = i := congrArg Fin.val hfin
          omega
        have he_zero := hrem e he_lt he_fresh
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := e) (by eval_expr) ?_
        refine runs_seq_assign_le (v := e * L_w) (by eval_expr) ?_
        refine runs_seq_assign_le (v := numSt + e * L_w) (by eval_expr) ?_
        refine runs_seq_triple_le (emitLimbsAt_triple (dst := numSt + e * L_w) (natLimbs h 6) _ st.mem hd_lt
          (by omega)) ⟨rfl, by simp, rfl⟩ fun st2 h2' => ?_
        rcases h2' with ⟨h2_regs, hset6, hfr6⟩
        have h2_0 : st2.regs 0 = eListPtr := by rw [h2_regs]; simp [h0]
        have h2_1 : st2.regs 1 = m0 := by rw [h2_regs]; simp [h1]
        have h2_2 : st2.regs 2 = numSt := by rw [h2_regs]; simp [h2]
        have h2_3 : st2.regs 3 = denSt := by rw [h2_regs]; simp [h3]
        have h2_4 : st2.regs 4 = L_w := by rw [h2_regs]; simp [h4]
        have h2_5 : st2.regs 5 = i := by rw [h2_regs]; simp [hr5]
        have h2_7 : st2.regs 7 = e * L_w := by rw [h2_regs]; simp
        refine runs_store_le (x := denSt + e * L_w) (v := 1) (by eval_expr) (by eval_expr) ?_
          (by wram_cost)
        set mem3 := Function.update st2.mem (denSt + e * L_w) 1 with hmem3_def
        have hnum_e : Num.Valid mem3 (numSt + e * L_w) h L_w ∧
            Num.intVal mem3 (numSt + e * L_w) h L_w = 6 := by
          refine valid_intVal_of_natLimbs (val := 6) hh h6len h12cap
            (fun j hj => ?_) (fun j hj1 hj2 => ?_)
          · rw [hmem3_def, Function.update_of_ne (show numSt + e * L_w + j ≠ denSt + e * L_w by omega)]
            simpa using hset6 j hj
          · rw [hmem3_def, Function.update_of_ne (show numSt + e * L_w + j ≠ denSt + e * L_w by omega),
              hfr6 _ (Or.inr (by omega))]
            exact (he_zero j hj2).1
        have hden_e : Num.Valid mem3 (denSt + e * L_w) h L_w ∧
            Num.intVal mem3 (denSt + e * L_w) h L_w = 1 := by
          refine valid_intVal_one hh hLw (by omega)
            (by rw [hmem3_def, Function.update_self])
            (fun j hj1 hj2 => by
              rw [hmem3_def, Function.update_of_ne (show denSt + e * L_w + j ≠ denSt + e * L_w by omega),
                hfr6 _ (Or.inr (by omega))]
              exact (he_zero j hj2).2)
        have hmem3_other : ∀ e' < eCap, e' ≠ e → ∀ j < L_w,
            mem3 (numSt + e' * L_w + j) = st.mem (numSt + e' * L_w + j) ∧
            mem3 (denSt + e' * L_w + j) = st.mem (denSt + e' * L_w + j) := by
          intro e' he' hne j hj
          have he'Lw : e' * L_w + L_w ≤ eCap * L_w := by
            have := Nat.mul_le_mul_right L_w he'
            rwa [Nat.succ_mul] at this
          have hdisj : e' * L_w + j < e * L_w ∨ e * L_w + L_w ≤ e' * L_w + j := by
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · left
              have : (e' + 1) * L_w ≤ e * L_w := Nat.mul_le_mul_right L_w hlt
              rw [Nat.add_mul, Nat.one_mul] at this; omega
            · right
              have : (e + 1) * L_w ≤ e' * L_w := Nat.mul_le_mul_right L_w hgt
              rw [Nat.add_mul, Nat.one_mul] at this; omega
          constructor
          · rw [hmem3_def, Function.update_of_ne (show numSt + e' * L_w + j ≠ denSt + e * L_w by omega),
              hfr6 _ (by omega)]
          · rw [hmem3_def, Function.update_of_ne (show denSt + e' * L_w + j ≠ denSt + e * L_w by omega),
              hfr6 _ (Or.inr (by omega))]
        refine ⟨⟨by simp [h2_0], by simp [h2_1], by simp [h2_2], by simp [h2_3], by simp [h2_4],
          by simp, ?_, ?_, ?_⟩, h2_5⟩
        · intro k hk hkm
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | rfl
          · have hne : eList[k]'hkm ≠ e := he_fresh k hk' hkm
            have hprev := hdone k hk' hkm
            have hlt' : eList[k]'hkm < eCap := helt _ (List.getElem_mem hkm)
            have hconN : ∀ j < L_w, mem3 (numSt + (eList[k]'hkm) * L_w + j) =
                st.mem (numSt + (eList[k]'hkm) * L_w + j) :=
              fun j hj => (hmem3_other _ hlt' hne j hj).1
            have hconD : ∀ j < L_w, mem3 (denSt + (eList[k]'hkm) * L_w + j) =
                st.mem (denSt + (eList[k]'hkm) * L_w + j) :=
              fun j hj => (hmem3_other _ hlt' hne j hj).2
            dsimp only
            refine ⟨fun j hj => by rw [hconN j hj]; exact hprev.1 j hj,
              by rw [Num.intVal_congr hconN]; exact hprev.2.1,
              fun j hj => by rw [hconD j hj]; exact hprev.2.2.1 j hj,
              by rw [Num.intVal_congr hconD]; exact hprev.2.2.2⟩
          · dsimp only
            exact ⟨hnum_e.1, hnum_e.2, hden_e.1, hden_e.2⟩
        · intro e' he' hfresh' j hj
          have hne : e' ≠ e := (hfresh' i (Nat.lt_succ_self i) him).symm
          have hprev := hrem e' he' (fun k hk hkm => hfresh' k (Nat.lt_succ_of_lt hk) hkm) j hj
          have hc := hmem3_other e' he' hne j hj
          dsimp only
          rw [hc.1, hc.2]
          exact hprev
        · intro a ha1 ha2
          dsimp only
          rw [hmem3_def, Function.update_of_ne (show a ≠ denSt + e * L_w by omega),
            hfr6 a (by omega)]
          exact hfr a ha1 ha2)).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop rfl fun st' hpost => ?_
  rcases hpost with ⟨-, -, -, -, -, -, hdone, -, hfr⟩
  refine runs_ret_le (v := 0) (by eval_expr) ?_
    (by simp only [initOneWstrContract, List.getD_cons_succ, List.getD_cons_zero]; wram_cost)
  refine ⟨eListPtr, m0, numSt, denSt, L_w, rfl, rfl, ?_, fun a ha => hfr a (by omega) (by omega)⟩
  intro i hi
  have him : i < eList.length := by omega
  dsimp only
  rw [hlat i him]
  exact hdone i hi him

end

end MinCostFlow.LSF.Program
