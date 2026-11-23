module

public import MinCostFlow.ExpanderDecomp.OuterProgRecLabels
public import MinCostFlow.ExpanderDecomp.OuterProgRecCombine
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Helper Triples and Tree-Space Budget for `outerDecompRecProc` (`OuterProgRecBase`)

Proves the `RemoveFake` workspace bound, `Triple` specifications of `writeCompLabelsStmt`,
`writeConstLabelStmt`, and `computeRfWorkBoundStmt`, and the explicit recursion-depth / tree-space
budget (`recDepthBound`, `recTreeSpace`), re-exporting `OuterProgRecLabels` and
`OuterProgRecCombine`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 8. `RemoveFake` Workspace and `Triple` Proofs for Helper Statements -/

/-- Whenever `e ≤ M`, `mF ≤ e`, `1 ≤ Λ`, and `2 * M < 2 ^ LParam M`, the exact `RemoveFake`
workspace `removeFakeWorkSpace k e mF (rfHParam e mF 1 Λ)` is at most
`rfWorkBound k e mF Λ (LParam M)`. -/
lemma removeFakeWorkSpace_le_rfWorkBound {M k e mF Λ : ℕ}
    (heM : e ≤ M) (hmF : mF ≤ e) (hΛ : 1 ≤ Λ) (h2ML : 2 * M < 2 ^ LParam M) :
    removeFakeWorkSpace k e mF (rfHParam e mF 1 Λ) ≤ rfWorkBound k e mF Λ (LParam M) := by
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have h2m_lt : 2 * (e + 2 * mF) + 1 < 2 ^ (LParam M + 2) := by
    have hpow : 2 ^ (LParam M + 2) = 4 * 2 ^ LParam M := by ring
    rw [hpow]; omega
  have hlog : Nat.log 2 (2 * (e + 2 * mF) + 1) < LParam M + 2 :=
    Nat.log_lt_of_lt_pow (by omega) h2m_lt
  have hlog1 : Nat.log 2 (2 * (e + 2 * mF) + 1) + 1 ≤ 2 * LParam M := by omega
  have hH : rfHParam e mF 1 Λ ≤ 112 * Λ * LParam M + 2 := by
    have h1 : 4 * rfCcap 1 Λ ≤ 56 * Λ := by unfold rfCcap; simp only [Nat.div_one]; omega
    unfold rfHParam
    have h2 : 4 * rfCcap 1 Λ * (Nat.log 2 (2 * (e + 2 * mF) + 1) + 1) ≤
        (56 * Λ) * (2 * LParam M) := Nat.mul_le_mul h1 hlog1
    have h3 : (56 * Λ) * (2 * LParam M) = 112 * Λ * LParam M := by ring
    rw [h3] at h2
    omega
  have h2H : 2 * (112 * Λ * LParam M) = 224 * Λ * LParam M := by ring
  unfold removeFakeWorkSpace pruneWorkSpace rfWorkBound
  omega

/-- `Triple` for `writeCompLabelsStmt`: shifts `k` local labels from `tmpLblAddr` by `nl` into
`labelsAddr[verts[i]]` and stores `nl + k` at `nextLblAddr`. -/
lemma writeCompLabels_triple {w n k vertsAddr labelsAddr nextLblAddr tmpLblAddr nl : ℕ}
    (p : Program) (st₀ : State) (verts : List ℕ)
    (hr0 : st₀.regs 0 = k) (hr1 : st₀.regs 1 = vertsAddr)
    (hr6 : st₀.regs 6 = labelsAddr) (hr7 : st₀.regs 7 = nextLblAddr)
    (hr10 : st₀.regs 10 = tmpLblAddr)
    (hlen : verts.length = k) (hnd : verts.Nodup) (hsub : ∀ u ∈ verts, u < n)
    (hV : ListAt st₀.mem vertsAddr verts)
    (hnl : st₀.mem nextLblAddr = nl)
    (hlbl_lt : ∀ i < k, st₀.mem (tmpLblAddr + i) < k)
    (hdLV : DisjointRange labelsAddr n vertsAddr k)
    (hdLT : DisjointRange labelsAddr n tmpLblAddr k)
    (hdLN : DisjointRange labelsAddr n nextLblAddr 1)
    (hV_w : vertsAddr + k < 2 ^ w) (hT_w : tmpLblAddr + k < 2 ^ w)
    (hL_w : labelsAddr + n < 2 ^ w)
    (hk_w : k + 1 < 2 ^ w) (hnl_w : nl + k < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    Triple w p (fun s => s = st₀) writeCompLabelsStmt
      (normalPost fun s' =>
        s'.mem nextLblAddr = nl + k ∧
        (∀ i (hi : i < k), s'.mem (labelsAddr + verts[i]'(hlen ▸ hi)) = nl + st₀.mem (tmpLblAddr + i)) ∧
        (∀ a, (∀ u ∈ verts, a ≠ labelsAddr + u) → a ≠ nextLblAddr → s'.mem a = st₀.mem a) ∧
        (∀ r' ≤ 11, s'.regs r' = st₀.regs r'))
      (fun _ => 40 * k + 30) := by
  intro s ω hs; subst s
  let st1 : State := { st₀ with regs := Function.update st₀.regs 12 nl }
  have h1 : Runs w p ω (.assign 12 (.load (.reg 7))) st₀ .normal st1 3 :=
    runs_assign_iff.mpr ⟨nl, by simp [Expr.eval, hr7, hnl], rfl, rfl, by simp [Expr.size]⟩
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 13 = j ∧ st.regs 12 = nl ∧
    (∀ r' ≤ 11, st.regs r' = st₀.regs r') ∧
    (∀ i (hi : i < j) (hik : i < k), st.mem (labelsAddr + verts[i]'(by omega)) = nl + st₀.mem (tmpLblAddr + i)) ∧
    (∀ a, (∀ i (hi : i < j) (hik : i < k), a ≠ labelsAddr + verts[i]'(by omega)) → st.mem a = st₀.mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 13) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 14 (.load (.bin .add (.reg 1) (.reg 13))) ;;
      .assign 15 (.load (.bin .add (.reg 10) (.reg 13))) ;;
      .store (.bin .add (.reg 6) (.reg 14)) (.bin .add (.reg 12) (.reg 15)))
    (P := fun s => s = st1) (Inv := Inv) 26 0 k (Nat.zero_le k) (by omega) (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp, by simp [st1],
        fun r' hr' => by simp [st1, Function.update_of_ne (by omega : r' ≠ 13),
          Function.update_of_ne (by omega : r' ≠ 12)],
        fun _ hi _ => by omega, fun _ _ => rfl⟩)
    (fun _ s _ _ hI => hI.1)
    (fun _ s _ _ ⟨_, _, hkr, _, _⟩ => Expr.eval_reg_of_eq (by rw [hkr 0 (by decide), hr0]))
    (fun j _ hj => by
      intro s ω ⟨h13, h12, hkr, hdone, hfr⟩
      set v := verts[j]'(by omega)
      set lv := st₀.mem (tmpLblAddr + j)
      have hv_lt : v < n := hsub v (List.getElem_mem _)
      have hlv_lt : lv < k := hlbl_lt j hj
      have hmemV : s.mem (vertsAddr + j) = v := by
        rw [hfr (vertsAddr + j) (fun i hi hik => by
          have := hsub verts[i] (List.getElem_mem _)
          rcases hdLV with hL | hL <;> omega)]
        exact hV j (by omega)
      have hmemT : s.mem (tmpLblAddr + j) = lv := by
        rw [hfr (tmpLblAddr + j) (fun i hi hik => by
          have := hsub verts[i] (List.getElem_mem _)
          rcases hdLT with hL | hL <;> omega)]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := v)
        (by simp [Expr.eval, BinOp.eval, hkr 1 (by decide), hr1, h13,
              (by omega : vertsAddr + j < 2 ^ w), hmemV]) ?_
      refine runs_seq_assign_le (v := lv)
        (by simp [Expr.eval, BinOp.eval, hkr 10 (by decide), hr10, h13,
              (by omega : tmpLblAddr + j < 2 ^ w), hmemT]) ?_
      refine runs_store_le (x := labelsAddr + v) (v := nl + lv)
        (by simp [Expr.eval, BinOp.eval, hkr 6 (by decide), hr6, (by omega : labelsAddr + v < 2 ^ w)])
        (by simp [Expr.eval, BinOp.eval, h12, (by omega : nl + lv < 2 ^ w)])
        ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, by simp [h12],
        fun r' hr' => by
          dsimp only
          rw [Function.update_of_ne (by omega : r' ≠ 13),
              Function.update_of_ne (by omega : r' ≠ 15),
              Function.update_of_ne (by omega : r' ≠ 14), hkr r' hr'],
        fun i hi hik => by
          dsimp only
          by_cases hij : i = j
          · subst hij; simp [v, lv]
          · have hne : verts[i]'(by omega) ≠ v := fun heq =>
              hij ((List.Nodup.getElem_inj_iff hnd).mp heq)
            rw [Function.update_of_ne (by omega)]
            exact hdone i (by omega) hik,
        fun a ha => by
          dsimp only
          rw [Function.update_of_ne (show a ≠ labelsAddr + v from ha j (by omega) hj)]
          exact hfr a (fun i hi hik => ha i (by omega) hik)⟩,
        by simp [h13]⟩)
  rcases hloop st1 ω rfl with ⟨o2, st2, c2, hrun2, hq2, hc2⟩
  cases o2 with
  | returned _ => exact False.elim hq2
  | normal =>
    rcases hq2 with ⟨_, h2_12, h2_r, h2_done, h2_fr⟩
    let st3 : State := { st2 with mem := Function.update st2.mem nextLblAddr (nl + k) }
    have h3 : Runs w p ω (.store (.reg 7) (.bin .add (.reg 12) (.reg 0))) st2 .normal st3 5 :=
      runs_store_iff.mpr ⟨nextLblAddr, nl + k,
        by simp [Expr.eval, h2_r 7 (by decide), hr7],
        by simp [Expr.eval, BinOp.eval, h2_12, h2_r 0 (by decide), hr0, hnl_w],
        rfl, rfl, by simp [Expr.size]⟩
    have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, 3, c2 + 5 + 1, h1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, 5, hrun2, h3, rfl⟩), rfl⟩)
    refine ⟨.normal, st3, _, hrun, ?_, by dsimp [Expr.size] at hc2 ⊢; omega⟩
    refine ⟨by simp [st3], fun i hi => ?_, fun a ha haN => ?_, h2_r⟩
    · have hv_lt : verts[i]'(hlen ▸ hi) < n := hsub _ (List.getElem_mem _)
      dsimp only [st3]
      rw [Function.update_of_ne (by rcases hdLN with hL | hL <;> omega)]
      exact h2_done i hi hi
    · dsimp only [st3]
      rw [Function.update_of_ne haN]
      exact h2_fr a (fun i hi _ => ha _ (List.getElem_mem _))

/-- `Triple` for `writeConstLabelStmt`: paints `rList[0..kR-1]` with `nl` in `labelsAddr` and
updates `mem[nextLblAddr] := nl + 1`. -/
lemma writeConstLabel_triple {w n kR rAddr labelsAddr nextLblAddr nl : ℕ}
    (p : Program) (st₀ : State) (rList : List ℕ)
    (hr6 : st₀.regs 6 = labelsAddr) (hr7 : st₀.regs 7 = nextLblAddr)
    (hr24 : st₀.regs 24 = rAddr) (hr28 : st₀.regs 28 = kR)
    (hlen : rList.length = kR) (hsub : ∀ u ∈ rList, u < n)
    (hR : ListAt st₀.mem rAddr rList) (hnl : st₀.mem nextLblAddr = nl)
    (hdLR : DisjointRange labelsAddr n rAddr kR)
    (hdLN : DisjointRange labelsAddr n nextLblAddr 1)
    (hR_w : rAddr + kR < 2 ^ w) (hL_w : labelsAddr + n < 2 ^ w)
    (hk_w : kR + 1 < 2 ^ w)
    (hnl_w : nl + 1 < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    Triple w p (fun s => s = st₀) writeConstLabelStmt
      (normalPost fun s' =>
        s'.mem nextLblAddr = nl + 1 ∧
        (∀ u ∈ rList, s'.mem (labelsAddr + u) = nl) ∧
        (∀ a, (∀ u ∈ rList, a ≠ labelsAddr + u) → a ≠ nextLblAddr → s'.mem a = st₀.mem a) ∧
        (∀ r', r' ≤ 29 ∨ 33 ≤ r' → s'.regs r' = st₀.regs r'))
      (fun _ => 30 * kR + 30) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  let st1 : State := { st₀ with regs := Function.update st₀.regs 30 nl }
  have h1 : Runs w p ω (.assign 30 (.load (.reg 7))) st₀ .normal st1 3 :=
    runs_assign_iff.mpr ⟨nl, by simp [Expr.eval, hr7, hnl], rfl, rfl, by simp [Expr.size]⟩
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 31 = j ∧ st.regs 30 = nl ∧
    (∀ r', r' ≤ 29 ∨ 33 ≤ r' → st.regs r' = st₀.regs r') ∧
    (∀ i (hi : i < j) (hik : i < kR), st.mem (labelsAddr + rList[i]'(by omega)) = nl) ∧
    (∀ a, (∀ i (hi : i < j) (hik : i < kR), a ≠ labelsAddr + rList[i]'(by omega)) → st.mem a = st₀.mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 31) (lo := .const 0) (hi := .reg 28)
    (body :=
      .assign 32 (.load (.bin .add (.reg 24) (.reg 31))) ;;
      .store (.bin .add (.reg 6) (.reg 32)) (.reg 30))
    (P := fun s => s = st1) (Inv := Inv) 18 0 kR (Nat.zero_le kR) (by omega) (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp, by simp [st1],
        fun r' hr' => by simp [st1, Function.update_of_ne (by omega : r' ≠ 31),
          Function.update_of_ne (by omega : r' ≠ 30)],
        fun _ hi _ => by omega, fun _ _ => rfl⟩)
    (fun _ s _ _ hI => hI.1)
    (fun _ s _ _ ⟨_, _, hkr, _, _⟩ => Expr.eval_reg_of_eq (by rw [hkr 28 (Or.inl (by decide)), hr28]))
    (fun j _ hj => by
      intro s ω ⟨h31, h30, hkr, hdone, hfr⟩
      set v := rList[j]'(by omega)
      have hv_lt : v < n := hsub v (List.getElem_mem _)
      have hmemR : s.mem (rAddr + j) = v := by
        rw [hfr (rAddr + j) (fun i hi hik => by
          have := hsub rList[i] (List.getElem_mem _)
          rcases hdLR with hL | hL <;> omega)]
        exact hR j (by omega)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := v)
        (by simp [Expr.eval, BinOp.eval, hkr 24 (Or.inl (by decide)), hr24, h31,
              (by omega : rAddr + j < 2 ^ w), hmemR]) ?_
      refine runs_store_le (x := labelsAddr + v) (v := nl)
        (by simp [Expr.eval, BinOp.eval, hkr 6 (Or.inl (by decide)), hr6, (by omega : labelsAddr + v < 2 ^ w)])
        (by simp [Expr.eval, h30]) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, by simp [h30],
        fun r' hr' => by
          dsimp only
          rw [Function.update_of_ne (by omega : r' ≠ 31),
              Function.update_of_ne (by omega : r' ≠ 32), hkr r' hr'],
        fun i hi hik => by
          dsimp only
          by_cases heq : labelsAddr + rList[i]'(by omega) = labelsAddr + v
          · rw [heq, Function.update_self]
          · rw [Function.update_of_ne heq]
            have hi_lt : i < j := by
              by_contra hge
              have : i = j := by omega
              subst this; exact heq rfl
            exact hdone i hi_lt hik,
        fun a ha => by
          dsimp only
          rw [Function.update_of_ne (show a ≠ labelsAddr + v from ha j (by omega) hj)]
          exact hfr a (fun i hi hik => ha i (by omega) hik)⟩,
        by simp [h31]⟩)
  rcases hloop st1 ω rfl with ⟨o2, st2, c2, hrun2, hq2, hc2⟩
  cases o2 with
  | returned _ => exact False.elim hq2
  | normal =>
    rcases hq2 with ⟨_, h2_30, h2_r, h2_done, h2_fr⟩
    let st3 : State := { st2 with mem := Function.update st2.mem nextLblAddr (nl + 1) }
    have h3 : Runs w p ω (.store (.reg 7) (.bin .add (.reg 30) (.const 1))) st2 .normal st3 5 :=
      runs_store_iff.mpr ⟨nextLblAddr, nl + 1,
        by simp [Expr.eval, h2_r 7 (Or.inl (by decide)), hr7],
        by simp [Expr.eval, BinOp.eval, h2_30, hw1, hnl_w],
        rfl, rfl, by simp [Expr.size]⟩
    have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, 3, c2 + 5 + 1, h1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, 5, hrun2, h3, rfl⟩), rfl⟩)
    refine ⟨.normal, st3, _, hrun, ?_, by dsimp [Expr.size] at hc2 ⊢; omega⟩
    refine ⟨by simp [st3], fun u hu => ?_, fun a ha haN => ?_, h2_r⟩
    · rcases List.getElem_of_mem hu with ⟨i, hi, rfl⟩
      have hv_lt : rList[i] < n := hsub _ (List.getElem_mem _)
      dsimp only [st3]
      rw [Function.update_of_ne (by rcases hdLN with hL | hL <;> omega)]
      exact h2_done i (by omega) (by omega)
    · dsimp only [st3]
      rw [Function.update_of_ne haN]
      exact h2_fr a (fun i hi _ => ha _ (List.getElem_mem _))

/-- `Triple` for `computeRfWorkBoundStmt`: computes `rfWorkBound k e mF Λ L` into `r31`. -/
lemma computeRfWorkBound_triple {w k e mF Λ L : ℕ}
    (p : Program) (st₀ : State)
    (hr0 : st₀.regs 0 = k) (hr2 : st₀.regs 2 = e)
    (hr27 : st₀.regs 27 = mF) (hr22 : st₀.regs 22 = Λ) (hr23 : st₀.regs 23 = L)
    (hL1 : 1 ≤ L) (hwb : rfWorkBound k e mF Λ L < 2 ^ w) (h250 : 250 < 2 ^ w) :
    Triple w p (fun s => s = st₀) computeRfWorkBoundStmt
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧
        s'.regs 31 = rfWorkBound k e mF Λ L ∧
        (∀ r', r' ≤ 30 ∨ 33 ≤ r' → s'.regs r' = st₀.regs r'))
      (fun _ => 50) := by
  intro s ω hs; subst s
  have hwb' : 16 * k + 7 * e + 30 * mF + 224 * Λ * L + 20 < 2 ^ w := hwb
  have h16k : 16 * k < 2 ^ w := by omega
  have h7e : 7 * e < 2 ^ w := by omega
  have h30m : 30 * mF < 2 ^ w := by omega
  have h224L : 224 * Λ * L < 2 ^ w := by omega
  have h224 : 224 * Λ < 2 ^ w := by
    have : 224 * Λ ≤ 224 * Λ * L := Nat.le_mul_of_pos_right _ hL1
    omega
  refine runs_start_le ?_
  dsimp only [computeRfWorkBoundStmt]
  refine runs_seq_assign_le (v := 16 * k)
    (by simp [Expr.eval, BinOp.eval, hr0, (by omega : 16 < 2 ^ w), h16k]) ?_
  refine runs_seq_assign_le (v := 16 * k + 7 * e)
    (by simp [Expr.eval, BinOp.eval, hr2, (by omega : 7 < 2 ^ w), h7e,
          (by omega : 16 * k + 7 * e < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 16 * k + 7 * e + 30 * mF)
    (by simp [Expr.eval, BinOp.eval, hr27, (by omega : 30 < 2 ^ w), h30m,
          (by omega : 16 * k + 7 * e + 30 * mF < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 224 * Λ)
    (by simp [Expr.eval, BinOp.eval, hr22, (by omega : 224 < 2 ^ w), h224]) ?_
  refine runs_seq_assign_le (v := 224 * Λ * L)
    (by simp [Expr.eval, BinOp.eval, hr23, h224L]) ?_
  refine runs_assign_le (v := rfWorkBound k e mF Λ L)
    (by simp [Expr.eval, BinOp.eval, (by omega : 20 < 2 ^ w),
          (by omega : 224 * Λ * L + 20 < 2 ^ w), rfWorkBound, Nat.add_assoc]; omega)
    ⟨rfl, by simp, fun r' hr' => by
      dsimp only
      rw [Function.update_of_ne (by omega : r' ≠ 31),
          Function.update_of_ne (by omega : r' ≠ 32),
          Function.update_of_ne (by omega : r' ≠ 32),
          Function.update_of_ne (by omega : r' ≠ 31),
          Function.update_of_ne (by omega : r' ≠ 31),
          Function.update_of_ne (by omega : r' ≠ 31)]⟩
    (by simp [Expr.size])

end MinCostFlow.ExpanderDecomp

/-! ## 9. Explicit Recursion-Depth and Tree-Space Budget -/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

/-- Explicit upper bound on the recursion tree depth from an edge count `e` when every recursive
child shrinks by at least the factor `(16 * D - 1) / (16 * D)`. -/
def recDepthBound (D : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
    if _hD : 1 ≤ D then
      1 + recDepthBound D ((16 * D - 1) * (e + 1) / (16 * D))
    else 1
termination_by e => e
decreasing_by
  exact Nat.div_lt_of_lt_mul (by
    have hlt : (16 * D - 1) * (e + 1) < (16 * D) * (e + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.succ_pos e)
    linarith)

/-- Total zero-heap space budget for a subtree rooted at edge count `e` with per-edge budget
`perE` and per-witness-edge budget `perW`. -/
def recTreeSpace (D perE perW e : ℕ) : ℕ :=
  recDepthBound D e * e * perE + 2 * e * perW + 3

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

lemma recDepthBound_mono {D : ℕ} (hD : 1 ≤ D) :
    ∀ e₂ e₁, e₁ ≤ e₂ → recDepthBound D e₁ ≤ recDepthBound D e₂ := by
  intro e₂
  induction e₂ using Nat.strong_induction_on with
  | h e₂ ih =>
    intro e₁ hle
    cases e₁ with
    | zero => simp [recDepthBound]
    | succ a =>
      cases e₂ with
      | zero => omega
      | succ b =>
        rw [recDepthBound, recDepthBound]
        simp only [hD, ↓reduceDIte]
        have hlt : (16 * D - 1) * (b + 1) / (16 * D) < b + 1 :=
          Nat.div_lt_of_lt_mul (by
            have := Nat.mul_lt_mul_of_pos_right (show 16 * D - 1 < 16 * D by omega) (Nat.succ_pos b)
            linarith)
        have hdiv : (16 * D - 1) * (a + 1) / (16 * D) ≤ (16 * D - 1) * (b + 1) / (16 * D) :=
          Nat.div_le_div_right (Nat.mul_le_mul_left _ hle)
        exact Nat.add_le_add_left (ih _ hlt _ hdiv) 1

lemma recDepthBound_step {D e e' : ℕ} (hD : 1 ≤ D) (he : 1 ≤ e)
    (hsh : 16 * D * e' ≤ (16 * D - 1) * e) :
    1 + recDepthBound D e' ≤ recDepthBound D e := by
  cases e with
  | zero => omega
  | succ b =>
    rw [recDepthBound]
    simp only [hD, ↓reduceDIte]
    have hdiv : e' ≤ (16 * D - 1) * (b + 1) / (16 * D) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hsh)
    exact Nat.add_le_add_left (recDepthBound_mono hD _ _ hdiv) 1

lemma recDepthBound_pow_le {D : ℕ} (hD : 1 ≤ D) :
    ∀ e, 1 ≤ recDepthBound D e →
      (16 * D) ^ (recDepthBound D e - 1) ≤ (16 * D - 1) ^ (recDepthBound D e - 1) * e := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    cases e with
    | zero => simp [recDepthBound]
    | succ b =>
      intro _
      rw [recDepthBound]
      simp only [hD, ↓reduceDIte, Nat.add_sub_cancel_left]
      set e' := (16 * D - 1) * (b + 1) / (16 * D)
      have hlt : e' < b + 1 :=
        Nat.div_lt_of_lt_mul (by
          have := Nat.mul_lt_mul_of_pos_right (show 16 * D - 1 < 16 * D by omega) (Nat.succ_pos b)
          linarith)
      have hsh : 16 * D * e' ≤ (16 * D - 1) * (b + 1) := Nat.mul_div_le _ _
      exact pow_le_of_step hsh (Nat.succ_pos b) (ih e' hlt)

lemma recDepthBound_le_HDepth (cfg : ParamConfig) {M r e : ℕ} (heM : e ≤ M) :
    recDepthBound (DOut cfg M r) e ≤ HDepth cfg M r := by
  have hD : 1 ≤ DOut cfg M r := one_le_DOut cfg M r
  have h1 := depth_le_of_pow (K := 16 * DOut cfg M r) (by omega) heM (recDepthBound_pow_le hD e)
  unfold HDepth; omega

lemma recTreeSpace_cut_step {D perE perW e e₁ e₂ : ℕ}
    (hD : 1 ≤ D) (he : 1 ≤ e) (hsum : e₁ + e₂ ≤ e)
    (hsh1 : 16 * D * e₁ ≤ (16 * D - 1) * e) (hsh2 : 16 * D * e₂ ≤ (16 * D - 1) * e) :
    e * perE + recTreeSpace D perE perW e₁ + recTreeSpace D perE perW e₂ ≤
      recTreeSpace D perE perW e + 3 := by
  have hd1 := recDepthBound_step hD he hsh1
  have hd2 := recDepthBound_step hD he hsh2
  set d := recDepthBound D e
  have hd_pos : 1 ≤ d := by omega
  have hm1 : recDepthBound D e₁ * e₁ ≤ (d - 1) * e₁ := Nat.mul_le_mul_right e₁ (by omega)
  have hm2 : recDepthBound D e₂ * e₂ ≤ (d - 1) * e₂ := Nat.mul_le_mul_right e₂ (by omega)
  have hcomb : (recDepthBound D e₁ * e₁ + recDepthBound D e₂ * e₂) * perE ≤
      ((d - 1) * e) * perE := by
    apply Nat.mul_le_mul_right perE
    calc recDepthBound D e₁ * e₁ + recDepthBound D e₂ * e₂
        ≤ (d - 1) * e₁ + (d - 1) * e₂ := Nat.add_le_add hm1 hm2
      _ = (d - 1) * (e₁ + e₂) := by ring
      _ ≤ (d - 1) * e := Nat.mul_le_mul_left _ hsum
  have hw : (2 * e₁ + 2 * e₂) * perW ≤ (2 * e) * perW :=
    Nat.mul_le_mul_right perW (by omega)
  have hde : e * perE + (d - 1) * e * perE = d * e * perE := by
    have : d = (d - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  unfold recTreeSpace
  have hdist1 : recDepthBound D e₁ * e₁ * perE + recDepthBound D e₂ * e₂ * perE =
      (recDepthBound D e₁ * e₁ + recDepthBound D e₂ * e₂) * perE := by ring
  have hdist2 : 2 * e₁ * perW + 2 * e₂ * perW = (2 * e₁ + 2 * e₂) * perW := by ring
  linarith

lemma recTreeSpace_witness_step {D perE perW e eRest : ℕ}
    (hD : 1 ≤ D) (he : 1 ≤ e) (h16 : 16 * eRest ≤ e)
    (hsh : 16 * D * eRest ≤ (16 * D - 1) * e) :
    e * perE + e * perW + recTreeSpace D perE perW eRest ≤
      recTreeSpace D perE perW e := by
  have hdR := recDepthBound_step hD he hsh
  set d := recDepthBound D e
  have hd_pos : 1 ≤ d := by omega
  have hmR : recDepthBound D eRest * eRest * perE ≤ (d - 1) * e * perE :=
    Nat.mul_le_mul_right perE (Nat.mul_le_mul (by omega) (by omega))
  have hw : (e + 2 * eRest) * perW ≤ (2 * e) * perW :=
    Nat.mul_le_mul_right perW (by omega)
  have hde : e * perE + (d - 1) * e * perE = d * e * perE := by
    have : d = (d - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  unfold recTreeSpace
  have hdistW : e * perW + 2 * eRest * perW = (e + 2 * eRest) * perW := by ring
  linarith

end MinCostFlow.ExpanderDecomp
