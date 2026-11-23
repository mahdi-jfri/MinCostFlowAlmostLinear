module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedCandA

import Mathlib.Tactic.Linarith

/-!
# Dynamic Spanner Candidate Collection: Phase B Helpers & Inner Loop (`DynSpannerAffectedCandB`)

Verifies pure fold/rangeCost helpers, Phase B statement splits (`dsCandInnerBody`,
`dsCandMidBody`, `dsCandOuterBody`, `dsCandPhaseBStmt`), `CandCtx` / `CandMemInv`, and
`dsCollectCand_innerLoop_triple` for `dsCollectCandStmt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Sequence append reassociation helper -/

/-- Append `b` to the right spine of a `;`-sequence `a`. -/
def seqAppend (a b : Stmt) : Stmt :=
  match a with
  | .seq x y => x ;; seqAppend y b
  | _ => a ;; b

lemma runs_seq_reassoc_rev {w : ℕ} {p : Program} {ω : ℕ → Bool} {x y z : Stmt}
    {st : State} {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω ((x ;; y) ;; z) st o st' c) :
    ∃ c' ≤ c, Runs w p ω (x ;; y ;; z) st o st' c' := by
  rcases runs_seq_iff.mp h with ⟨u, c1, hxy, rfl, rfl⟩ | ⟨st1, c1, c2, hxy, hz, rfl⟩
  · rcases runs_seq_iff.mp hxy with ⟨u', cx, hx, hu, rfl⟩ | ⟨st0, cx, cy, hx, hy, rfl⟩
    · cases hu
      exact ⟨cx + 1, by omega, runs_seq_iff.mpr (Or.inl ⟨u, cx, hx, rfl, rfl⟩)⟩
    · exact ⟨cx + cy + 2, by omega,
        runs_seq_iff.mpr (Or.inr ⟨st0, cx, cy + 1, hx,
          runs_seq_iff.mpr (Or.inl ⟨u, cy, hy, rfl, rfl⟩), by omega⟩)⟩
  · rcases runs_seq_iff.mp hxy with ⟨u, cx, hx, hu, rfl⟩ | ⟨st0, cx, cy, hx, hy, rfl⟩
    · cases hu
    · exact ⟨cx + (cy + c2 + 1) + 1, by omega,
        runs_seq_iff.mpr (Or.inr ⟨st0, cx, cy + c2 + 1, hx,
          runs_seq_iff.mpr (Or.inr ⟨st1, cy, c2, hy, hz, rfl⟩), rfl⟩)⟩

lemma runs_seqAppend {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ {a b : Stmt} {st : State} {o : Outcome} {st' : State} {c : ℕ},
      Runs w p ω (a ;; b) st o st' c →
      ∃ c' ≤ c, Runs w p ω (seqAppend a b) st o st' c'
  | .seq x y, b, _, _, _, c, h => by
    rcases runs_seq_reassoc_rev h with ⟨c₁, hc₁, h₁⟩
    rcases runs_seq_iff.mp h₁ with ⟨u, cx, hx, rfl, rfl⟩ | ⟨st0, cx, cyz, hx, hyz, rfl⟩
    · exact ⟨cx + 1, by omega, runs_seq_iff.mpr (Or.inl ⟨u, cx, hx, rfl, rfl⟩)⟩
    · rcases runs_seqAppend hyz with ⟨c', hc', hyb⟩
      exact ⟨cx + c' + 1, by omega, runs_seq_iff.mpr (Or.inr ⟨st0, cx, c', hx, hyb, rfl⟩)⟩
  | .nop, _, _, _, _, c, h => ⟨c, le_rfl, h⟩
  | .assign _ _, _, _, _, _, c, h => ⟨c, le_rfl, h⟩
  | .store _ _, _, _, _, _, c, h => ⟨c, le_rfl, h⟩
  | .rand _, _, _, _, _, c, h => ⟨c, le_rfl, h⟩
  | .cond _ _ _, _, _, _, _, c, h => ⟨c, le_rfl, h⟩
  | .loop _ _, _, _, _, _, c, h => ⟨c, le_rfl, h⟩
  | .call _ _ _, _, _, _, _, c, h => ⟨c, le_rfl, h⟩
  | .ret _, _, _, _, _, c, h => ⟨c, le_rfl, h⟩

lemma runs_seqAppend_triple_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {P : State → Prop} {a b : Stmt} {Q₁ : State → Prop} {T₁ : State → ℕ}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (ht : Triple w p P a (normalPost Q₁) T₁) (hP : P st)
    (hrest : ∀ st₁, Q₁ st₁ →
      ∃ o st' c₂, Runs w p ω b st₁ o st' c₂ ∧ Q o st' ∧ (k + T₁ st + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (seqAppend a b) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases runs_seq_triple_le ht hP hrest with ⟨o, st', c, hruns, hq, hc⟩
  rcases runs_seqAppend hruns with ⟨c', hc', hruns'⟩
  exact ⟨o, st', c', hruns', hq, by omega⟩

/-! ## Pure fold & range-cost helpers -/

def midCandFold (G' : MGraph) (revLists_i : ℕ → List ℕ) (cand0 : List ℕ)
    (sPrevList : List ℕ) (k : ℕ) : List ℕ :=
  (sPrevList.take k).foldl (fun c v => filterCandFold G' c (revLists_i v)) cand0

def outerCandFold (L : ℕ) (G' : MGraph) (revLists : Fin (L + 1) → ℕ → List ℕ)
    (sPrevList : List ℕ) (i : ℕ) : List ℕ :=
  (List.range i).foldl (fun c r =>
    if hr : r < L + 1 then midCandFold G' (revLists ⟨r, hr⟩) c sPrevList sPrevList.length
    else c) []

lemma midCandFold_zero (G' : MGraph) (revLists_i : ℕ → List ℕ) (cand0 : List ℕ)
    (sPrevList : List ℕ) : midCandFold G' revLists_i cand0 sPrevList 0 = cand0 := rfl

lemma midCandFold_succ {G' : MGraph} {revLists_i : ℕ → List ℕ} {cand0 : List ℕ}
    {sPrevList : List ℕ} {k : ℕ} (hk : k < sPrevList.length) :
    midCandFold G' revLists_i cand0 sPrevList (k + 1) =
      filterCandFold G' (midCandFold G' revLists_i cand0 sPrevList k) (revLists_i sPrevList[k]) := by
  simp only [midCandFold, List.take_succ_eq_append_getElem hk, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

lemma midCandFold_props {G' : MGraph} {eCap : ℕ} {revLists_i : ℕ → List ℕ}
    {cand0 sPrevList : List ℕ}
    (hnd0 : cand0.Nodup) (hsub0 : ∀ x ∈ cand0, x ∈ G'.E ∧ x < eCap)
    (hrl : ∀ v ∈ sPrevList, ∀ e ∈ revLists_i v, e < eCap) :
    ∀ k ≤ sPrevList.length,
      (midCandFold G' revLists_i cand0 sPrevList k).Nodup ∧
      (∀ x ∈ midCandFold G' revLists_i cand0 sPrevList k, x ∈ G'.E ∧ x < eCap) ∧
      (∀ x, x ∈ midCandFold G' revLists_i cand0 sPrevList k ↔
        x ∈ cand0 ∨ (x ∈ G'.E ∧ ∃ v ∈ sPrevList.take k, x ∈ revLists_i v)) := by
  intro k hk
  induction k with
  | zero => exact ⟨hnd0, hsub0, fun x => by simp [midCandFold_zero]⟩
  | succ k ih =>
    have hlt : k < sPrevList.length := by omega
    have h1 := ih (Nat.le_of_lt hlt)
    have h2 := filterCandFold_props h1.1 h1.2.1 (hrl sPrevList[k] (List.getElem_mem hlt))
    rw [midCandFold_succ hlt]
    refine ⟨h2.1, h2.2.1, fun x => ?_⟩
    rw [h2.2.2 x, h1.2.2 x, List.take_succ_eq_append_getElem hlt]
    constructor
    · rintro ((hc | ⟨hxE, v, hv, hxv⟩) | ⟨hxE, hxk⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨hxE, v, List.mem_append.mpr (Or.inl hv), hxv⟩
      · exact Or.inr ⟨hxE, sPrevList[k], List.mem_append.mpr (Or.inr (List.mem_singleton_self _)), hxk⟩
    · rintro (hc | ⟨hxE, v, hv, hxv⟩)
      · exact Or.inl (Or.inl hc)
      · rcases List.mem_append.mp hv with hv | hv
        · exact Or.inl (Or.inr ⟨hxE, v, hv, hxv⟩)
        · rw [List.mem_singleton] at hv; subst hv; exact Or.inr ⟨hxE, hxv⟩

lemma midCandFold_of_empty {G' : MGraph} {revLists_i : ℕ → List ℕ}
    {cand0 sPrevList : List ℕ} (hem : ∀ v ∈ sPrevList, revLists_i v = []) :
    ∀ k ≤ sPrevList.length, midCandFold G' revLists_i cand0 sPrevList k = cand0 := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : k < sPrevList.length := by omega
    rw [midCandFold_succ hlt, ih (Nat.le_of_lt hlt), hem _ (List.getElem_mem hlt),
      filterCandFold, List.foldl_nil]

lemma outerCandFold_zero (L : ℕ) (G' : MGraph) (revLists : Fin (L + 1) → ℕ → List ℕ)
    (sPrevList : List ℕ) : outerCandFold L G' revLists sPrevList 0 = [] := rfl

lemma outerCandFold_succ {L : ℕ} {G' : MGraph} {revLists : Fin (L + 1) → ℕ → List ℕ}
    {sPrevList : List ℕ} {i : ℕ} (hi : i < L + 1) :
    outerCandFold L G' revLists sPrevList (i + 1) =
      midCandFold G' (revLists ⟨i, hi⟩) (outerCandFold L G' revLists sPrevList i)
        sPrevList sPrevList.length := by
  simp only [outerCandFold, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [dite_eq_left_of_eq_true (eq_true hi)]

lemma outerCandFold_props {L j eCap : ℕ} {G' : MGraph}
    {S_prev : Finset ℕ} {sPrevList : List ℕ} {revLists : Fin (L + 1) → ℕ → List ℕ}
    (hj : j ≤ L) (hs_mem : ∀ v, v ∈ sPrevList ↔ v ∈ S_prev)
    (hrl : ∀ i : Fin (L + 1), i.1 < j → ∀ v ∈ S_prev, ∀ e ∈ revLists i v, e < eCap) :
    ∀ k ≤ j,
      (outerCandFold L G' revLists sPrevList k).Nodup ∧
      (∀ x ∈ outerCandFold L G' revLists sPrevList k, x ∈ G'.E ∧ x < eCap) ∧
      (∀ x, x ∈ outerCandFold L G' revLists sPrevList k ↔
        x ∈ G'.E ∧ ∃ i : Fin (L + 1), ∃ v ∈ S_prev, i.1 < k ∧ x ∈ revLists i v) := by
  intro k hk
  induction k with
  | zero =>
    rw [outerCandFold_zero]
    exact ⟨List.nodup_nil, (fun _ hx => by cases hx), (fun x => by simp)⟩
  | succ k ih =>
    have hk_lt : k < j := by omega
    have hk_L1 : k < L + 1 := by omega
    have h1 := ih (Nat.le_of_lt hk_lt)
    have h2 := midCandFold_props (revLists_i := revLists ⟨k, hk_L1⟩) (sPrevList := sPrevList)
      h1.1 h1.2.1 (fun v hv => hrl ⟨k, hk_L1⟩ hk_lt v ((hs_mem v).mp hv))
      sPrevList.length (le_refl _)
    rw [outerCandFold_succ hk_L1]
    refine ⟨h2.1, h2.2.1, fun x => ?_⟩
    rw [h2.2.2 x, h1.2.2 x, List.take_length]
    constructor
    · rintro (⟨hxE, i, v, hv, hik, hxi⟩ | ⟨hxE, v, hv, hxv⟩)
      · exact ⟨hxE, i, v, hv, by omega, hxi⟩
      · exact ⟨hxE, ⟨k, hk_L1⟩, v, (hs_mem v).mp hv, Nat.lt_succ_self k, hxv⟩
    · rintro ⟨hxE, i, v, hv, hik, hxi⟩
      by_cases hik' : i.1 < k
      · exact Or.inl ⟨hxE, i, v, hv, hik', hxi⟩
      · have hieq : i = ⟨k, hk_L1⟩ := Fin.ext (by dsimp only; omega)
        subst hieq; exact Or.inr ⟨hxE, v, (hs_mem v).mpr hv, hxi⟩

lemma rangeCost_scale (c : ℕ) (f : ℕ → ℕ) (hi : ℕ) :
    rangeCost (fun i => c * f i) 0 hi = c * rangeCost f 0 hi := by
  induction hi with
  | zero => simp
  | succ hi ih =>
    simp only [rangeCost, Nat.sub_zero, List.range'_eq_map_range, List.map_map,
      List.range_succ, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton] at ih ⊢
    simp only [Function.comp_def, Nat.zero_add] at ih ⊢
    rw [ih]; ring

lemma rangeCost_zero_map_sum {α : Type*} (xs : List α) (f : α → ℕ) :
    rangeCost (fun k => if hk : k < xs.length then f xs[k] else 0) 0 xs.length = (xs.map f).sum := by
  suffices ∀ n ≤ xs.length,
      rangeCost (fun k => if hk : k < xs.length then f xs[k] else 0) 0 n = ((xs.take n).map f).sum by
    simpa [List.take_length] using this xs.length (le_refl _)
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n < xs.length := by omega
    simp only [rangeCost, Nat.sub_zero, List.range'_eq_map_range, List.map_map,
      List.range_succ, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton] at ih ⊢
    simp only [Function.comp_def, Nat.zero_add] at ih ⊢
    rw [ih (Nat.le_of_lt hlt), dite_eq_left_of_eq_true (eq_true hlt), List.take_succ_eq_append_getElem hlt,
      List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]

lemma rangeCost_zero_finset_sum (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = (Finset.range n).sum f := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [rangeCost, Nat.sub_zero, List.range'_eq_map_range, List.map_map,
      List.range_succ, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton] at ih ⊢
    simp only [Function.comp_def, Nat.zero_add] at ih ⊢
    rw [ih, Finset.sum_range_succ]

/-! ## Phase B statement splits and invariants -/

def dsCandInnerBody : Stmt :=
  .assign 25 (.load (.reg 24)) ;;
  .cond (.load (.bin .add (.reg 17) (.reg 25)))
    (.cond (.bin .eq (.load (.bin .add (.reg 13) (.reg 25))) (.reg 6))
       .nop
       (.store (.bin .add (.reg 13) (.reg 25)) (.reg 6) ;;
        .store (.reg 14) (.reg 25) ;;
        .assign 14 (.bin .add (.reg 14) (.const 1))))
    .nop ;;
  .assign 24 (.load (.bin .add (.reg 24) (.const 1)))

def dsCandMidBody : Stmt :=
  .assign 23 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 22))) ;;
  .cond (.bin .eq (.load (.bin .add (.reg 20) (.reg 23))) (.reg 19))
    (.assign 24 (.load (.bin .add (.reg 21) (.reg 23))) ;;
     .loop (.reg 24) dsCandInnerBody)
    .nop

def dsCandOuterBody : Stmt :=
  .assign 19 (.load (.bin .add (.reg 7) (.reg 18))) ;;
  .cond (.reg 19)
    (.assign 20 (.bin .add (.reg 8) (.bin .mul (.reg 18) (.reg 3))) ;;
     .assign 21 (.bin .add (.reg 9) (.bin .mul (.reg 18) (.reg 3))) ;;
     forRange 22 (.const 0) (.reg 15) dsCandMidBody)
    .nop

def dsCandPhaseBStmt : Stmt :=
  .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 6) ;;
  .assign 16 (.reg 14) ;;
  .assign 17 (.bin .add (.bin .add (.reg 0) (.const (dsHdrSize + 4))) (.bin .mul (.const 7) (.reg 3))) ;;
  forRange 18 (.const 0) (.reg 1) dsCandOuterBody ;;
  .store (.bin .add (.reg 2) (.const 1)) (.bin .sub (.reg 14) (.reg 16)) ;;
  .ret (.reg 14)

def dsCandBasesStmt : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dsGenOff))) ;;
  .assign 14 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4)))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 14))) ;;
  .assign 7 (.bin .add (.reg 7)
    (.bin .add (.bin .mul (.const 3) (.reg 4)) (.bin .mul (.const 2) (.bin .add (.reg 5) (.const 1))))) ;;
  .assign 8 (.bin .add (.reg 7)
    (.bin .add (.bin .add (.reg 5) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 4))))) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 10) (.bin .add (.reg 5) (.const 1)))
    (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
  .assign 12 (.bin .add (.reg 11) (.bin .add (.reg 5) (.const 1))) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 3)))

def dsCandPhaseAStmt : Stmt :=
  .assign 14 (.bin .add (.reg 2) (.const 2)) ;;
  .assign 15 (.bin .sub (.reg 1) (.const 1)) ;;
  .cond (.load (.bin .add (.reg 10) (.reg 15)))
    (.assign 15 (.load (.bin .add (.reg 11) (.reg 15))) ;;
     .loop (.reg 15)
       (.assign 16 (.load (.reg 15)) ;;
        .store (.reg 14) (.reg 16) ;;
        .assign 14 (.bin .add (.reg 14) (.const 1)) ;;
        .store (.bin .add (.reg 12) (.reg 16)) (.const 1) ;;
        .assign 15 (.load (.bin .add (.reg 15) (.const 1)))))
    .nop ;;
  .assign 15 (.bin .sub (.reg 14) (.bin .add (.reg 2) (.const 2))) ;;
  .store (.reg 2) (.reg 15)

lemma dsCollectCandStmt_eq :
    dsCollectCandStmt = seqAppend dsCandBasesStmt (seqAppend dsCandPhaseAStmt dsCandPhaseBStmt) :=
  rfl

structure CandCtx where
  w : ℕ
  L : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  j : ℕ
  heapPtr : ℕ
  G' : MGraph
  S_prev : Finset ℕ
  sPrevList : List ℕ
  revLists : Fin (L + 1) → ℕ → List ℕ
  footRev : ℕ → Prop
  mem0 : ℕ → ℕ
  memB0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  h1j : 1 ≤ j
  hjL : j ≤ L
  hfix : b + dsFixedSize L vCap eCap ≤ heapPtr
  hh_lt : heapPtr + 2 + vCap + eCap < 2 ^ w
  hG_E : ∀ e ∈ G'.E, e < eCap
  hepres : ∀ e < eCap, mem0 (dgEPresBase (dsGPtr b) vCap + e) = if e ∈ G'.E then 1 else 0
  hfootRev : ∀ a, footRev a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr
  hS_cap : ∀ v ∈ S_prev, v < vCap
  hs_nd : sPrevList.Nodup
  hs_mem : ∀ v, v ∈ sPrevList ↔ v ∈ S_prev
  hgen_pos : 1 ≤ mem0 (b + dsGenOff)
  hgen1_lt : mem0 (b + dsGenOff) + 1 < 2 ^ w
  hm_sPrev_len : memB0 heapPtr = sPrevList.length
  hm_sPrev_at : ListAt memB0 (heapPtr + 2) sPrevList
  hm_sBit : ∀ v < vCap, memB0 (dsSBitBase b L vCap eCap + v) = if v ∈ S_prev then 1 else 0
  hm_gen : memB0 (b + dsGenOff) = mem0 (b + dsGenOff) + 1
  hm_eStamp0 : ∀ e < eCap, memB0 (dsEStampBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff)
  hm_domGen0 : ∀ i : Fin (L + 1), i.1 < j → mem0 (dsDomGenBase b L vCap eCap + i.1) ≤ mem0 (b + dsGenOff)
  hm_rev : ∀ i : Fin (L + 1), i.1 < j → ∀ v ∈ S_prev,
    mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem0 (b + dsGenOff) ∧
    (if 0 < mem0 (dsDomGenBase b L vCap eCap + i.1) ∧
        mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) = mem0 (dsDomGenBase b L vCap eCap + i.1)
     then LinkedListIn footRev mem0 (mem0 (dsRevHeadBase b L vCap eCap + i.1 * vCap + v)) (revLists i v)
     else revLists i v = []) ∧
    (∀ e ∈ revLists i v, e < eCap)
  hm_agree : ∀ addr, addr ≠ b + dsGenOff →
    (∀ v < vCap, addr ≠ dsSBitBase b L vCap eCap + v) →
    (addr < heapPtr ∨ heapPtr + 2 + sPrevList.length ≤ addr) →
    memB0 addr = mem0 addr

theorem CandCtx.lay (c : CandCtx) : DsCandLayout c.b c.L c.vCap c.eCap c.heapPtr c.w :=
  dsCandLayout_mk c.hfix c.hh_lt

def CandCtx.gen0 (c : CandCtx) : ℕ := c.mem0 (c.b + dsGenOff)
def CandCtx.gen1 (c : CandCtx) : ℕ := c.mem0 (c.b + dsGenOff) + 1
def CandCtx.candBase (c : CandCtx) : ℕ := c.heapPtr + 2 + c.sPrevList.length

lemma CandCtx.sPrev_len_le (c : CandCtx) : c.sPrevList.length ≤ c.vCap :=
  list_length_le_of_nodup_lt c.hs_nd fun v hv => c.hS_cap v ((c.hs_mem v).mp hv)

lemma CandCtx.memB0_lt_fix_eq (c : CandCtx) {addr : ℕ}
    (h1 : addr ≠ c.b + dsGenOff)
    (h2 : ∀ v < c.vCap, addr ≠ dsSBitBase c.b c.L c.vCap c.eCap + v)
    (h3 : addr < c.heapPtr) : c.memB0 addr = c.mem0 addr :=
  c.hm_agree addr h1 h2 (Or.inl h3)

lemma CandCtx.mul_vCap_lt {c : CandCtx} {i : ℕ} (hi : i < c.j) (hvp : 0 < c.vCap) :
    i * c.vCap < (c.L + 1) * c.vCap := by
  have : i < c.L + 1 := by have := c.hjL; omega
  exact Nat.mul_lt_mul_of_pos_right this hvp

lemma CandCtx.mul_vCap_add_lt {c : CandCtx} {i v : ℕ} (hi : i < c.j) (hv : v < c.vCap) :
    i * c.vCap + v < (c.L + 1) * c.vCap := by
  calc i * c.vCap + v < i * c.vCap + c.vCap := by omega
    _ = (i + 1) * c.vCap := (Nat.succ_mul i c.vCap).symm
    _ ≤ (c.L + 1) * c.vCap := Nat.mul_le_mul_right _ (by have := c.hjL; omega)

def CandFixedRegs (L vCap eCap b j heapPtr sPrevLen gen1 : ℕ) (st : State) : Prop :=
  st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 2 = heapPtr ∧
  st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 5 = L ∧
  st.regs 6 = gen1 ∧
  st.regs 7 = dsDomGenBase b L vCap eCap ∧
  st.regs 8 = dsRevGenBase b L vCap eCap ∧
  st.regs 9 = dsRevHeadBase b L vCap eCap ∧
  st.regs 10 = dsSGenBase b L vCap eCap ∧
  st.regs 11 = dsSHeadBase b L vCap eCap ∧
  st.regs 12 = dsSBitBase b L vCap eCap ∧
  st.regs 13 = dsEStampBase b L vCap eCap ∧
  st.regs 15 = sPrevLen ∧
  st.regs 16 = heapPtr + 2 + sPrevLen ∧
  st.regs 17 = dgEPresBase (dsGPtr b) vCap

lemma CandFixedRegs.agree {L vCap eCap b j heapPtr sPrevLen gen1 : ℕ}
    {st st' : State} (hf : CandFixedRegs L vCap eCap b j heapPtr sPrevLen gen1 st)
    (h : ∀ r ≤ 17, r ≠ 14 → st'.regs r = st.regs r) :
    CandFixedRegs L vCap eCap b j heapPtr sPrevLen gen1 st' := by
  rcases hf with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r15, r16, r17⟩
  exact ⟨(h 0 (by omega) (by omega)).trans r0, (h 1 (by omega) (by omega)).trans r1,
    (h 2 (by omega) (by omega)).trans r2, (h 3 (by omega) (by omega)).trans r3,
    (h 4 (by omega) (by omega)).trans r4, (h 5 (by omega) (by omega)).trans r5,
    (h 6 (by omega) (by omega)).trans r6, (h 7 (by omega) (by omega)).trans r7,
    (h 8 (by omega) (by omega)).trans r8, (h 9 (by omega) (by omega)).trans r9,
    (h 10 (by omega) (by omega)).trans r10, (h 11 (by omega) (by omega)).trans r11,
    (h 12 (by omega) (by omega)).trans r12, (h 13 (by omega) (by omega)).trans r13,
    (h 15 (by omega) (by omega)).trans r15, (h 16 (by omega) (by omega)).trans r16,
    (h 17 (by omega) (by omega)).trans r17⟩

structure CandMemInv (c : CandCtx) (cand : List ℕ) (st : State) : Prop where
  regs : CandFixedRegs c.L c.vCap c.eCap c.b c.j c.heapPtr c.sPrevList.length c.gen1 st
  cand_nd : cand.Nodup
  cand_sub : ∀ e ∈ cand, e ∈ c.G'.E ∧ e < c.eCap
  r14_eq : st.regs 14 = c.candBase + cand.length
  cand_at : ListAt st.mem c.candBase cand
  eStamp_spec : ∀ e < c.eCap,
    (e ∈ cand → st.mem (dsEStampBase c.b c.L c.vCap c.eCap + e) = c.gen1) ∧
    (e ∉ cand → st.mem (dsEStampBase c.b c.L c.vCap c.eCap + e) ≤ c.gen0)
  frame : ∀ addr, (∀ e < c.eCap, addr ≠ dsEStampBase c.b c.L c.vCap c.eCap + e) →
    (addr < c.candBase ∨ c.candBase + cand.length ≤ addr) → st.mem addr = c.memB0 addr

lemma CandMemInv.candBase_add_le {c : CandCtx} {cand : List ℕ} {st : State}
    (h : CandMemInv c cand st) : c.candBase + cand.length ≤ c.heapPtr + 2 + c.vCap + c.eCap := by
  have hc := list_length_le_of_nodup_lt h.cand_nd (fun e he => (h.cand_sub e he).2)
  have hs := c.sPrev_len_le
  dsimp only [CandCtx.candBase]; omega

lemma CandMemInv.read_lt_fix {c : CandCtx} {cand : List ℕ} {st : State}
    (h : CandMemInv c cand st) {addr : ℕ} (hfix_lt : addr < c.b + dsFixedSize c.L c.vCap c.eCap)
    (hgen : addr ≠ c.b + dsGenOff)
    (hsb : ∀ v < c.vCap, addr ≠ dsSBitBase c.b c.L c.vCap c.eCap + v)
    (hes : ∀ e < c.eCap, addr ≠ dsEStampBase c.b c.L c.vCap c.eCap + e) :
    st.mem addr = c.mem0 addr := by
  have hhp : addr < c.heapPtr := lt_of_lt_of_le hfix_lt c.hfix
  have hcb : addr < c.candBase := by dsimp only [CandCtx.candBase]; omega
  rw [h.frame addr hes (Or.inl hcb), c.memB0_lt_fix_eq hgen hsb hhp]

lemma CandMemInv.read_footRev {c : CandCtx} {cand : List ℕ} {st : State}
    (h : CandMemInv c cand st) {a : ℕ} (ha : c.footRev a) : st.mem a = c.mem0 a := by
  have hfa := c.hfootRev a ha
  have hlay := c.lay
  have hcb : a < c.candBase := by dsimp only [CandCtx.candBase]; omega
  have hgen : a ≠ c.b + dsGenOff := by
    have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh
    have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
    have := hlay.sb_lt_es; have := hlay.es_lt_fix; omega
  have hsb : ∀ v < c.vCap, a ≠ dsSBitBase c.b c.L c.vCap c.eCap + v := fun v hv => by
    have := hlay.es_lt_fix; have := hlay.sb_lt_es; omega
  have hes : ∀ e < c.eCap, a ≠ dsEStampBase c.b c.L c.vCap c.eCap + e := fun e he => by
    have := hlay.es_lt_fix; omega
  rw [h.frame a hes (Or.inl hcb), c.memB0_lt_fix_eq hgen hsb hfa.2]

lemma CandMemInv.read_epres {c : CandCtx} {cand : List ℕ} {st : State}
    (h : CandMemInv c cand st) {e : ℕ} (he : e < c.eCap) :
    st.mem (dgEPresBase (dsGPtr c.b) c.vCap + e) = if e ∈ c.G'.E then 1 else 0 := by
  have hlay := c.lay
  have := hlay.ep_lt_fix
  have h1 : dgEPresBase (dsGPtr c.b) c.vCap + e ≠ c.b + dsGenOff := by
    have := hlay.b_lt_dom; have := hlay.epres_eq; have := hlay.min_eq; have := hlay.dom_eq
    have := hlay.dgs_eq
    have : dsGenOff < dsHdrSize := by decide
    omega
  have h2 : ∀ v < c.vCap, dgEPresBase (dsGPtr c.b) c.vCap + e ≠ dsSBitBase c.b c.L c.vCap c.eCap + v := by
    intro v hv
    have := hlay.epres_eq; have := hlay.min_eq; have := hlay.dom_eq; have := hlay.dgs_eq
    have := hlay.dom_lt_revg; have := hlay.revg_lt_revh; have := hlay.revh_lt_sg
    have := hlay.sg_lt_sh; have := hlay.sh_lt_sb; omega
  have h3 : ∀ z < c.eCap, dgEPresBase (dsGPtr c.b) c.vCap + e ≠ dsEStampBase c.b c.L c.vCap c.eCap + z := by
    intro z hz
    have := hlay.epres_eq; have := hlay.min_eq; have := hlay.dom_eq; have := hlay.dgs_eq
    have := hlay.dom_lt_revg; have := hlay.revg_lt_revh; have := hlay.revh_lt_sg
    have := hlay.sg_lt_sh; have := hlay.sh_lt_sb; have := hlay.sb_lt_es; omega
  rw [h.read_lt_fix (by omega) h1 h2 h3, c.hepres e he]

lemma CandMemInv.read_sPrev {c : CandCtx} {cand : List ℕ} {st : State}
    (h : CandMemInv c cand st) {k : ℕ} (hk : k < c.sPrevList.length) :
    st.mem (c.heapPtr + 2 + k) = c.sPrevList[k] := by
  have hlay := c.lay
  have hes : ∀ z < c.eCap, c.heapPtr + 2 + k ≠ dsEStampBase c.b c.L c.vCap c.eCap + z := fun z hz => by
    have := hlay.es_lt_fix; have := c.hfix; omega
  have hcb : c.heapPtr + 2 + k < c.candBase := by dsimp only [CandCtx.candBase]; omega
  rw [h.frame _ hes (Or.inl hcb)]
  exact listAt_get hk c.hm_sPrev_at

lemma CandMemInv.step_add {c : CandCtx} {cand : List ℕ} {st st' : State} {e : ℕ}
    (h : CandMemInv c cand st) (heE : e ∈ c.G'.E) (heCap : e < c.eCap) (heC : e ∉ cand)
    (hregs : CandFixedRegs c.L c.vCap c.eCap c.b c.j c.heapPtr c.sPrevList.length c.gen1 st')
    (hr14 : st'.regs 14 = c.candBase + cand.length + 1)
    (hmem : st'.mem = Function.update
      (Function.update st.mem (dsEStampBase c.b c.L c.vCap c.eCap + e) c.gen1)
      (c.candBase + cand.length) e) :
    CandMemInv c (cand ++ [e]) st' := by
  have hlay := c.lay
  have hes_lt_cb : ∀ z < c.eCap, dsEStampBase c.b c.L c.vCap c.eCap + z < c.candBase := fun z hz => by
    have := hlay.es_lt_fix; have := c.hfix; dsimp only [CandCtx.candBase]; omega
  refine {
    regs := hregs
    cand_nd := List.nodup_append.mpr ⟨h.cand_nd, List.nodup_singleton e, fun x hx y hy hxy => by
      subst hxy; rw [List.mem_singleton] at hy; subst hy; exact heC hx⟩
    cand_sub := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl; exact h.cand_sub x hx; exact ⟨heE, heCap⟩
    r14_eq := by simpa [Nat.add_assoc] using hr14
    cand_at := listAt_snoc (listAt_of_agree (fun t ht => by
      rw [hmem, Function.update_of_ne (by omega), Function.update_of_ne (by
        have := hes_lt_cb e heCap; omega)]) h.cand_at) (by
      rw [hmem, Function.update_self])
    eStamp_spec := fun z hz => by
      rw [hmem, Function.update_of_ne (by have := hes_lt_cb z hz; omega)]
      by_cases hze : z = e
      · subst hze; rw [Function.update_self]
        exact ⟨fun _ => rfl, fun hn => absurd (by simp) hn⟩
      · rw [Function.update_of_ne (by omega)]
        simpa [List.mem_append, List.mem_singleton, hze] using h.eStamp_spec z hz
    frame := fun addr hns hrange => by
      simp only [List.length_append, List.length_singleton] at hrange
      rw [hmem, Function.update_of_ne (by omega), Function.update_of_ne (hns e heCap)]
      exact h.frame addr hns (by omega)
  }

/-! ## Innermost linked-list loop -/

lemma innerLoop_next24 {c : CandCtx} {p : Program} {ω : ℕ → Bool}
    {cand : List ℕ} {rl : List ℕ} {head0 : ℕ} {k : ℕ} (hlt : k < rl.length)
    {st : State} {k0 T : ℕ}
    (hinv : CandMemInv c cand st)
    (hr24 : st.regs 24 = llPtr c.mem0 head0 k)
    (hll : LinkedListIn c.footRev c.mem0 head0 rl)
    (hr_eq : ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st.regs r = st.regs r)
    (rInit : ℕ → ℕ)
    (hinit : ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st.regs r = rInit r)
    (hcost : k0 + 5 ≤ T) :
    ∃ (o : Outcome) (st' : State) (c' : ℕ),
      Runs c.w p ω (.assign 24 (.load (.bin .add (.reg 24) (.const 1)))) st o st' c' ∧
      (o = .normal ∧
        CandMemInv c cand st' ∧
        st'.regs 24 = llPtr c.mem0 head0 (k + 1) ∧
        ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st'.regs r = rInit r) ∧
      k0 + c' ≤ T := by
  have _ := hr_eq
  have hsp := llPtr_step_spec hll k hlt
  have hlay := c.lay
  have hp1_lt : llPtr c.mem0 head0 k + 1 < 2 ^ c.w :=
    lt_trans (c.hfootRev _ hsp.2.2.1).2 hlay.hp_lt_w
  have hm_next : st.mem (llPtr c.mem0 head0 k + 1) = llPtr c.mem0 head0 (k + 1) := by
    rw [hinv.read_footRev hsp.2.2.1, hsp.2.2.2.2]
  have hev : (Expr.load (.bin .add (.reg 24) (.const 1))).eval c.w st =
      some (llPtr c.mem0 head0 (k + 1)) :=
    Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr24) (Expr.eval_const (by omega)) hp1_lt) hm_next
  refine runs_assign_le hev ?_ (by simp [Expr.size]; omega)
  dsimp only
  refine ⟨rfl, ⟨hinv.regs.agree (fun r hr h14 => by
      dsimp only
      exact Function.update_of_ne (f := st.regs) (v := llPtr c.mem0 head0 (k + 1))
        (by omega : r ≠ 24)), hinv.cand_nd, hinv.cand_sub,
    by dsimp only; rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 24), hinv.r14_eq],
    hinv.cand_at, hinv.eStamp_spec, hinv.frame⟩,
    by rw [Function.update_self],
    fun r h14 h24 h25 => by rw [Function.update_of_ne h24, hinit r h14 h24 h25]⟩

lemma dsCollectCand_innerLoop_triple (c : CandCtx) {p : Program}
    {cand0 : List ℕ} (hnd0 : cand0.Nodup)
    (hsub0 : ∀ x ∈ cand0, x ∈ c.G'.E ∧ x < c.eCap)
    (head0 : ℕ) (rl : List ℕ)
    (hll : LinkedListIn c.footRev c.mem0 head0 rl)
    (hrl_lt : ∀ e ∈ rl, e < c.eCap)
    (rInit : ℕ → ℕ) :
    Triple c.w p
      (fun st => CandMemInv c cand0 st ∧ st.regs 24 = head0 ∧
        ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st.regs r = rInit r)
      (.loop (.reg 24) dsCandInnerBody)
      (normalPost fun st => CandMemInv c (filterCandFold c.G' cand0 rl) st ∧
        ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st.regs r = rInit r)
      (fun _ => 60 * rl.length + 10) := by
  have hlay := c.lay
  have hw16 := c.hw16
  let InvI : State → Prop := fun st =>
    ∃ k ≤ rl.length,
      CandMemInv c (filterCandFold c.G' cand0 (rl.take k)) st ∧
      st.regs 24 = llPtr c.mem0 head0 k ∧
      ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st.regs r = rInit r
  let mFn : State → ℕ := fun st =>
    if h : ∃ k ≤ rl.length, st.regs 24 = llPtr c.mem0 head0 k then
      rl.length - Nat.find h
    else 0
  let remFn : State → ℕ := fun st => 60 * mFn st + 10
  have hm_eq : ∀ {st} {k} (hk : k ≤ rl.length),
      st.regs 24 = llPtr c.mem0 head0 k → mFn st = rl.length - k := by
    intro st k hk hr24
    have hex : ∃ k' ≤ rl.length, st.regs 24 = llPtr c.mem0 head0 k' := ⟨k, hk, hr24⟩
    have hm1 : mFn st = rl.length - Nat.find hex := by dsimp only [mFn]; split_ifs; rfl
    have hsp := Nat.find_spec hex
    rw [hm1, llPtr_inj hll hsp.1 hk (hsp.2.symm.trans hr24)]
  exact (Triple.loop_measure
    (Inv := InvI)
    (Q := normalPost fun st => CandMemInv c (filterCandFold c.G' cand0 rl) st ∧
      ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st.regs r = rInit r)
    (condVal := fun st => st.regs 24) (m := mFn) (rem := remFn)
    (fun st ⟨k, hk, _, hr24, _⟩ => by simp [Expr.eval, hr24])
    (fun st ⟨k, hk, hinv, hr24, hfr⟩ hzero => by
      have hkeq : k = rl.length := by
        by_contra hne
        have hpos := (llPtr_step_spec hll k (lt_of_le_of_ne hk hne)).1
        rw [hr24] at hzero; omega
      subst hkeq; rw [List.take_length] at hinv
      exact ⟨⟨hinv, hfr⟩, by dsimp only [remFn, Expr.size]; omega⟩)
    (fun st ⟨k, hk, hinv, hr24, hfr⟩ hnz => by
      have hlt : k < rl.length := by
        by_contra hge; apply hnz
        rw [hr24, show k = rl.length by omega, llPtr_zero hll]
      have hsp := llPtr_step_spec hll k hlt
      set e := rl[k]
      set candK := filterCandFold c.G' cand0 (rl.take k)
      have he_cap : e < c.eCap := hrl_lt e (List.getElem_mem hlt)
      have hm_e : st.mem (llPtr c.mem0 head0 k) = e := by
        rw [hinv.read_footRev hsp.2.1, hsp.2.2.2.1]
      have hev25 : (Expr.load (.reg 24)).eval c.w st = some e :=
        Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr24) hm_e
      have hfold_props := filterCandFold_props (es := rl.take k) hnd0 hsub0
        (fun x hx => hrl_lt x (List.mem_of_mem_take hx))
      have hk1_take : rl.take (k + 1) = rl.take k ++ [e] :=
        List.take_succ_eq_append_getElem hlt
      have hfold_succ : filterCandFold c.G' cand0 (rl.take (k + 1)) =
          filterCandStep c.G' candK e := by
        simp only [filterCandFold, hk1_take, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
      refine ⟨52, fun s ω hs => ?_⟩
      · subst s
        suffices hres : ∃ o st' c_1,
            Runs c.w p ω dsCandInnerBody st o st' c_1 ∧
              (match o with
                | .returned u =>
                  normalPost
                      (fun st =>
                        CandMemInv c (filterCandFold c.G' cand0 rl) st ∧
                          ∀ (r : ℕ), r ≠ 14 → r ≠ 24 → r ≠ 25 → st.regs r = rInit r)
                      (.returned u) st' ∧
                    (Expr.reg 24).size + 52 + 1 ≤ remFn st
                | .normal => InvI st' ∧ mFn st' < mFn st ∧
                    (Expr.reg 24).size + 52 + remFn st' + 1 ≤ remFn st) ∧
              0 + c_1 ≤ 52 by
          rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
          dsimp only
          exact ⟨o, st', c_1, hr, hq, by omega⟩
        dsimp only [dsCandInnerBody]
        refine runs_seq_assign_le hev25 ?_
        have h17_e : dgEPresBase (dsGPtr c.b) c.vCap + e < 2 ^ c.w := by
          have := hlay.ep_lt_fix; have := c.hfix; have := hlay.hp_lt_w; omega
        have hm_ep : st.mem (dgEPresBase (dsGPtr c.b) c.vCap + e) = if e ∈ c.G'.E then 1 else 0 :=
          hinv.read_epres he_cap
        refine runs_seq_cond_le (v := if e ∈ c.G'.E then 1 else 0) ?_ ?_ ?_
        · exact Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide : (17 : ℕ) ≠ 25), hinv.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]))
            (Expr.eval_reg_of_eq (by simp)) h17_e) hm_ep
        · intro hE_nz
          have heE : e ∈ c.G'.E := by
            by_contra hnE; simp [hnE] at hE_nz
          have hinv1 : CandMemInv c candK { st with regs := Function.update st.regs 25 e } :=
            { regs := hinv.regs.agree (fun r hr h14 => by
                dsimp only; exact Function.update_of_ne (f := st.regs) (v := e) (by omega : r ≠ 25))
              cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
              r14_eq := by dsimp only; rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 25), hinv.r14_eq]
              cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame }
          have hr24_1 : (Function.update st.regs 25 e) 24 = llPtr c.mem0 head0 k := by
            rw [Function.update_of_ne (by decide : (24 : ℕ) ≠ 25), hr24]
          have hinit1 : ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → (Function.update st.regs 25 e) r = rInit r :=
            fun r h14 h24 h25 => by rw [Function.update_of_ne h25, hfr r h14 h24 h25]
          have h13_e : dsEStampBase c.b c.L c.vCap c.eCap + e < 2 ^ c.w := by
            have := hlay.es_lt_fix; have := c.hfix; have := hlay.hp_lt_w; omega
          refine runs_seq_cond_le (v := if e ∈ candK then 1 else 0) ?_ ?_ ?_
          · have hcmp : (if st.mem (dsEStampBase c.b c.L c.vCap c.eCap + e) = c.gen1 then 1 else 0) =
                if e ∈ candK then 1 else 0 := by
              by_cases heC : e ∈ candK
              · simp [(hinv.eStamp_spec e he_cap).1 heC, heC]
              · have hlt_g := (hinv.eStamp_spec e he_cap).2 heC
                have hne_g : st.mem (dsEStampBase c.b c.L c.vCap c.eCap + e) ≠ c.gen1 := by
                  dsimp only [CandCtx.gen0, CandCtx.gen1] at *; omega
                simp [heC, hne_g]
            rw [← hcmp]
            exact Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq hinv1.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
              (Expr.eval_reg_of_eq (r := 25) (v := e) (by simp)) h13_e) rfl)
              (Expr.eval_reg_of_eq hinv1.regs.2.2.2.2.2.2.1) (by omega)
          · intro hC_nz
            have heC : e ∈ candK := by by_contra hnc; simp [hnc] at hC_nz
            have hstep_eq : filterCandFold c.G' cand0 (rl.take (k + 1)) = candK := by
              rw [hfold_succ]; dsimp only [filterCandStep]; simp [heE, heC]
            refine runs_seq_nop_le ?_
            rcases innerLoop_next24 (p := p) (ω := ω) (k0 := 0) (T := 5)
                hlt hinv1 hr24_1 hll (fun r _ _ _ => rfl) rInit hinit1 (by omega) with
              ⟨_, st', c', hr, ⟨rfl, hi', hr24', hfr'⟩, hc⟩
            refine ⟨.normal, st', c', hr, ⟨?_, ?_⟩, by dsimp only [Expr.size]; omega⟩
            · refine ⟨k + 1, Nat.succ_le_of_lt hlt, by rwa [hstep_eq], hr24', hfr'⟩
            · have hm1 := hm_eq (Nat.succ_le_of_lt hlt) hr24'
              have hm0 := hm_eq hk hr24
              dsimp only [remFn, Expr.size]; omega
          · intro hC_z
            have heC : e ∉ candK := by
              intro hc; simp [hc] at hC_z
            have hstep_eq : filterCandFold c.G' cand0 (rl.take (k + 1)) = candK ++ [e] := by
              rw [hfold_succ]; dsimp only [filterCandStep]; simp [heE, heC]
            have he_lt_w : e < 2 ^ c.w := lt_trans he_cap hlay.eCap_w
            have hg_lt_w : c.gen1 < 2 ^ c.w := c.hgen1_lt
            have hcnd_add_le : c.candBase + (candK ++ [e]).length ≤ c.heapPtr + 2 + c.vCap + c.eCap := by
              have hnd' : (candK ++ [e]).Nodup := List.nodup_append.mpr
                ⟨hinv.cand_nd, List.nodup_singleton e, fun x hx y hy hxy => by
                  subst hxy; rw [List.mem_singleton] at hy; subst hy; exact heC hx⟩
              have hsub' : ∀ x ∈ candK ++ [e], x < c.eCap := fun x hx => by
                simp only [List.mem_append, List.mem_singleton] at hx
                rcases hx with hx | rfl; exact (hinv.cand_sub x hx).2; exact he_cap
              have := list_length_le_of_nodup_lt hnd' hsub'
              have := c.sPrev_len_le
              dsimp only [CandCtx.candBase]; omega
            have hr14_next_lt : c.candBase + candK.length + 1 < 2 ^ c.w := by
              have := c.hh_lt; simp only [List.length_append, List.length_singleton] at hcnd_add_le; omega
            refine runs_seq_assoc_le ?_
            refine runs_seq_store_le
              (Expr.eval_add (Expr.eval_reg_of_eq hinv1.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
                (Expr.eval_reg_of_eq (v := e) (by simp)) h13_e)
              (Expr.eval_reg_of_eq hinv1.regs.2.2.2.2.2.2.1) ?_
            refine runs_seq_assoc_le ?_
            refine runs_seq_store_le (Expr.eval_reg_of_eq hinv1.r14_eq)
              (Expr.eval_reg_of_eq (v := e) (by simp)) ?_
            refine runs_seq_assign_le
              (Expr.eval_add (Expr.eval_reg_of_eq hinv1.r14_eq) (Expr.eval_const (by omega)) hr14_next_lt) ?_
            let st3 : State :=
              { mem := Function.update (Function.update st.mem
                  (dsEStampBase c.b c.L c.vCap c.eCap + e) c.gen1) (c.candBase + candK.length) e
                regs := Function.update (Function.update st.regs 25 e) 14 (c.candBase + candK.length + 1)
                pos := st.pos }
            have hinv3 : CandMemInv c (candK ++ [e]) st3 :=
              hinv.step_add heE he_cap heC
                (hinv1.regs.agree (fun r hr h14 => by
                  dsimp only [st3]; rw [Function.update_of_ne h14]))
                (by dsimp only [st3]; simp) rfl
            have hr24_3 : st3.regs 24 = llPtr c.mem0 head0 k := by
              dsimp only [st3]
              rw [Function.update_of_ne (by decide : (24 : ℕ) ≠ 14), hr24_1]
            have hinit3 : ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → st3.regs r = rInit r :=
              fun r h14 h24 h25 => by dsimp only [st3]; rw [Function.update_of_ne h14, hinit1 r h14 h24 h25]
            rcases innerLoop_next24 (p := p) (ω := ω) (k0 := 0) (T := 5)
                (st := st3) hlt hinv3 hr24_3 hll (fun r _ _ _ => rfl) rInit hinit3 (by omega) with
              ⟨_, st', c', hr, ⟨rfl, hi', hr24', hfr'⟩, hc⟩
            refine ⟨.normal, st', c', hr, ⟨?_, ?_⟩, by dsimp only [Expr.size]; omega⟩
            · refine ⟨k + 1, Nat.succ_le_of_lt hlt, by rwa [hstep_eq], hr24', hfr'⟩
            · have hm1 := hm_eq (Nat.succ_le_of_lt hlt) hr24'
              have hm0 := hm_eq hk hr24
              dsimp only [remFn, Expr.size]; omega
        · intro hE_z
          have hnE : e ∉ c.G'.E := by intro hE; simp [hE] at hE_z
          have hstep_eq : filterCandFold c.G' cand0 (rl.take (k + 1)) = candK := by
            rw [hfold_succ]; dsimp only [filterCandStep]; simp [hnE]
          have hinv1 : CandMemInv c candK { st with regs := Function.update st.regs 25 e } :=
            { regs := hinv.regs.agree (fun r hr h14 => by
                dsimp only; exact Function.update_of_ne (f := st.regs) (v := e) (by omega : r ≠ 25))
              cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
              r14_eq := by dsimp only; rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 25), hinv.r14_eq]
              cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame }
          have hr24_1 : (Function.update st.regs 25 e) 24 = llPtr c.mem0 head0 k := by
            rw [Function.update_of_ne (by decide : (24 : ℕ) ≠ 25), hr24]
          have hinit1 : ∀ r, r ≠ 14 → r ≠ 24 → r ≠ 25 → (Function.update st.regs 25 e) r = rInit r :=
            fun r h14 h24 h25 => by rw [Function.update_of_ne h25, hfr r h14 h24 h25]
          refine runs_seq_nop_le ?_
          rcases innerLoop_next24 (p := p) (ω := ω) (k0 := 0) (T := 5)
              hlt hinv1 hr24_1 hll (fun r _ _ _ => rfl) rInit hinit1 (by omega) with
            ⟨_, st', c', hr, ⟨rfl, hi', hr24', hfr'⟩, hc⟩
          refine ⟨.normal, st', c', hr, ⟨?_, ?_⟩, by dsimp only [Expr.size]; omega⟩
          · refine ⟨k + 1, Nat.succ_le_of_lt hlt, by rwa [hstep_eq], hr24', hfr'⟩
          · have hm1 := hm_eq (Nat.succ_le_of_lt hlt) hr24'
            have hm0 := hm_eq hk hr24
            dsimp only [remFn, Expr.size]; omega)
    ).conseq
      (fun st ⟨hinv, hr24, hfr⟩ =>
        ⟨0, Nat.zero_le _, by simpa [filterCandFold] using hinv, by simpa [llPtr] using hr24, hfr⟩)
      (fun _ _ h => h)
      (fun st ⟨_, hr24, _⟩ => by
        have hm0 := hm_eq (Nat.zero_le _) (by simpa [llPtr] using hr24)
        dsimp only [remFn]; omega)

end

end MinCostFlow.DynSpanner.Program
