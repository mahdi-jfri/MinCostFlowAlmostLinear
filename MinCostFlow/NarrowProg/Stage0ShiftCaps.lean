module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.NarrowProg.Stage0ShiftHelpers
public import MinCostFlow.NarrowProg.Stage0Check
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 3: shifted capacities and shifted demands on active vertices

Given the checked input from `stage0Check`:
- `stage0ShiftCaps` computes `(shiftedGraph I hv).capacity e = ((I.edge e).upper - (I.edge e).lower).toNat`
  for every `e < m` into `pShCapBuf` (`m * L_dem` limbs) and records canonical lengths in `pShCapLen`.
- `stage0ShiftDemInit`, `stage0ShiftDemEdges`, `stage0ShiftDemFin` compute `shiftedDemand I (act[c])`
  ONLY for the `cnt ≤ 2 * m` active vertices (`0` space and `0` work per isolated vertex) using two
  lazy base-`2 ^ k` accumulators per active vertex, normalized once via `accNormalize`.
- `stage0Shift` allocates all shift arrays from `Assn.free h (2 ^ w - h)` and writes the 5 output
  pointers `[pShCapBuf, pShCapLen, pShDemBuf, pShDemSign, pShDemLen]` into `pShiftOut`.
- `stage0ShiftMod` packages the polymorphic `Module ι` in `O(m * (narrowMaxCapLimbs I + 1) + 1)` time.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg

/-! ### Array-of-blocks update helper & deterministic demand accumulator rows -/

theorem prod_func_update {n idx : ℕ} (hidx : idx < n) (p L : ℕ)
    (f : ℕ → List ℕ) (v : List ℕ) :
    (∏ c ∈ Finset.range n, Assn.list (p + c * L) (Function.update f idx v c)) =
      Assn.list (p + idx * L) v *
        ∏ c ∈ (Finset.range n).erase idx, Assn.list (p + c * L) (f c) := by
  rw [Assn.prod_eq_mul_erase (Finset.mem_range.mpr hidx), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro c hc
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]

theorem accAddList_replicate_zero {xs : List ℕ} {L : ℕ} (h : xs.length ≤ L) :
    accAddList (List.replicate L 0) xs = padLimbs xs L := by
  apply List.ext_getElem
  · simp [accAddList, length_padLimbs h]
  · intro j hj1 hj2
    have hjL : j < L := by simpa [accAddList] using hj1
    simp only [accAddList, List.getElem_ofFn, Fin.getElem_fin, List.getElem_replicate, zero_add,
      padLimbs]
    by_cases hjs : j < xs.length
    · rw [List.getD_eq_getElem _ _ hjs, List.getElem_append_left hjs]
    · rw [List.getD_eq_default _ _ (by omega), List.getElem_append_right (by omega),
        List.getElem_replicate]

/-- Initial positive accumulator row for active index `c` after processing the first `i` active
vertices. -/
def initPosRow (I : Instance) (act : List ℕ) (L i c : ℕ) : List ℕ :=
  if h : c < i ∧ c < act.length then
    if ¬ (I.d (act[c]'h.2) < 0) then
      padLimbs (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[c]'h.2)).natAbs) L
    else List.replicate L 0
  else List.replicate L 0

/-- Initial negative accumulator row for active index `c` after processing the first `i` active
vertices. -/
def initNegRow (I : Instance) (act : List ℕ) (L i c : ℕ) : List ℕ :=
  if h : c < i ∧ c < act.length then
    if I.d (act[c]'h.2) < 0 then
      padLimbs (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[c]'h.2)).natAbs) L
    else List.replicate L 0
  else List.replicate L 0

/-- Positive lazy accumulator row for active index `c` after scanning `i` edges. -/
def edgePosRow (I : Instance) (hv : I.IsValid) (act : List ℕ) (L : ℕ) : ℕ → ℕ → List ℕ
  | 0, c => initPosRow I act L act.length c
  | i + 1, c =>
    if h : i < I.m then
      let e : Fin I.m := ⟨i, h⟩
      let el := (FlowReduction.shiftedGraph I hv).endpointLabels
      let lt := el.table ((FlowReduction.shiftedGraph I hv).tail e) - 1
      let lh := el.table ((FlowReduction.shiftedGraph I hv).head e) - 1
      let loDig := Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs
      if (I.edge e).lower < 0 then
        Function.update (edgePosRow I hv act L i) lt
          (accAddList (edgePosRow I hv act L i lt) loDig) c
      else
        Function.update (edgePosRow I hv act L i) lh
          (accAddList (edgePosRow I hv act L i lh) loDig) c
    else edgePosRow I hv act L i c

/-- Negative lazy accumulator row for active index `c` after scanning `i` edges. -/
def edgeNegRow (I : Instance) (hv : I.IsValid) (act : List ℕ) (L : ℕ) : ℕ → ℕ → List ℕ
  | 0, c => initNegRow I act L act.length c
  | i + 1, c =>
    if h : i < I.m then
      let e : Fin I.m := ⟨i, h⟩
      let el := (FlowReduction.shiftedGraph I hv).endpointLabels
      let lt := el.table ((FlowReduction.shiftedGraph I hv).tail e) - 1
      let lh := el.table ((FlowReduction.shiftedGraph I hv).head e) - 1
      let loDig := Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs
      if (I.edge e).lower < 0 then
        Function.update (edgeNegRow I hv act L i) lh
          (accAddList (edgeNegRow I hv act L i lh) loDig) c
      else
        Function.update (edgeNegRow I hv act L i) lt
          (accAddList (edgeNegRow I hv act L i lt) loDig) c
    else edgeNegRow I hv act L i c

theorem edgeRow_props (I : Instance) (hv : I.IsValid) {act : List ℕ}
    (hact : ActiveInv (FlowReduction.shiftedGraph I hv).endpointLabels act)
    {L : ℕ} (hL1 : 1 ≤ L)
    (hedge : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length < L)
    (hdem : ∀ (c : ℕ) (hc : c < act.length),
      (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[c]'hc)).natAbs).length < L) :
    ∀ i ≤ I.m, ∀ c,
      (edgePosRow I hv act L i c).length = L ∧
      (edgeNegRow I hv act L i c).length = L ∧
      (∀ x ∈ edgePosRow I hv act L i c, x ≤ (i + 1) * (2 ^ narrowLimbWidth I - 1)) ∧
      (∀ x ∈ edgeNegRow I hv act L i c, x ≤ (i + 1) * (2 ^ narrowLimbWidth I - 1)) ∧
      Nat.ofDigits (2 ^ narrowLimbWidth I) (edgePosRow I hv act L i c) <
        (i + 1) * (2 ^ narrowLimbWidth I) ^ (L - 1) ∧
      Nat.ofDigits (2 ^ narrowLimbWidth I) (edgeNegRow I hv act L i c) <
        (i + 1) * (2 ^ narrowLimbWidth I) ^ (L - 1) ∧
      (∀ (hc : c < act.length),
        ((Nat.ofDigits (2 ^ narrowLimbWidth I) (edgePosRow I hv act L i c) : ℕ) : ℤ) -
        ((Nat.ofDigits (2 ^ narrowLimbWidth I) (edgeNegRow I hv act L i c) : ℕ) : ℤ) =
          I.d (act[c]'hc) -
            ∑ e : Fin I.m, if e.val < i then
              FlowReduction.coefficient I e ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e).lower
            else 0) := by
  set k := narrowLimbWidth I with hk_def
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth I
  have hB2 : 2 ≤ 2 ^ k := two_le_pow hk1
  have hpow_pos : 0 < (2 ^ k) ^ (L - 1) := Nat.pow_pos (by omega)
  intro i
  induction i with
  | zero =>
    intro _ c
    simp only [edgePosRow, edgeNegRow, Nat.zero_add, one_mul]
    have hsum0 : ∀ hc : c < act.length,
        (∑ e : Fin I.m, if e.val < 0 then
          FlowReduction.coefficient I e ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e).lower else 0) = 0 := by
      intro _; simp
    by_cases hc : c < act.length
    · have hdl := hdem c hc
      have hdlL : Limbs k (Nat.digits (2 ^ k) (I.d (act[c]'hc)).natAbs) := digits_limbs hk1 _
      have hpadL : Limbs k (padLimbs (Nat.digits (2 ^ k) (I.d (act[c]'hc)).natAbs) L) :=
        limbs_padLimbs hdlL L
      have hd_lt : (I.d (act[c]'hc)).natAbs < (2 ^ k) ^ (L - 1) := by
        have h1 := ofDigits_lt_pow_length hk1 hdlL
        rw [Nat.ofDigits_digits] at h1
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
      have hplen : (padLimbs (Nat.digits (2 ^ k) (I.d (act[c]'hc)).natAbs) L).length = L :=
        length_padLimbs (by omega)
      by_cases hneg : I.d (act[c]'hc) < 0
      · simp only [initPosRow, initNegRow, ← hk_def, hc, and_self, ↓reduceDIte, hneg,
          not_true_eq_false, ↓reduceIte, List.length_replicate, hplen,
          ofDigits_replicate_zero, ofDigits_padLimbs, Nat.ofDigits_digits, hsum0 hc, sub_zero]
        exact ⟨trivial, trivial, fun x hx => by rw [List.eq_of_mem_replicate hx]; omega,
          fun x hx => by have := hpadL x hx; omega, hpow_pos, hd_lt, fun _ => by omega⟩
      · simp only [initPosRow, initNegRow, ← hk_def, hc, and_self, ↓reduceDIte, hneg,
          not_false_eq_true, ↓reduceIte, List.length_replicate, hplen,
          ofDigits_replicate_zero, ofDigits_padLimbs, Nat.ofDigits_digits, hsum0 hc, sub_zero]
        exact ⟨trivial, trivial, fun x hx => by have := hpadL x hx; omega,
          fun x hx => by rw [List.eq_of_mem_replicate hx]; omega, hd_lt, hpow_pos, fun _ => by omega⟩
    · simp only [initPosRow, initNegRow, hc, and_false, ↓reduceDIte, List.length_replicate,
        ofDigits_replicate_zero]
      exact ⟨trivial, trivial, fun x hx => by rw [List.eq_of_mem_replicate hx]; omega,
        fun x hx => by rw [List.eq_of_mem_replicate hx]; omega, hpow_pos, hpow_pos,
        fun h => False.elim h⟩
  | succ i ih =>
    intro hi c
    have hlt : i < I.m := by omega
    have hprev := ih (by omega)
    set e : Fin I.m := ⟨i, hlt⟩
    set el := (FlowReduction.shiftedGraph I hv).endpointLabels
    set lt := el.table ((FlowReduction.shiftedGraph I hv).tail e) - 1
    set lh := el.table ((FlowReduction.shiftedGraph I hv).head e) - 1
    set loDig := Nat.digits (2 ^ k) (I.edge e).lower.natAbs
    have hloLen : loDig.length < L := hedge e
    have hloL : Limbs k loDig := digits_limbs hk1 _
    have hlo_lt : (I.edge e).lower.natAbs < (2 ^ k) ^ (L - 1) := by
      have h1 := ofDigits_lt_pow_length hk1 hloL
      rw [Nat.ofDigits_digits] at h1
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
    have hupd_elem : ∀ (xs : List ℕ), xs.length = L →
        (∀ x ∈ xs, x ≤ (i + 1) * (2 ^ k - 1)) →
        ∀ x ∈ accAddList xs loDig, x ≤ (i + 2) * (2 ^ k - 1) := by
      intro xs hxsL hxsB x hx
      rw [accAddList, List.mem_ofFn] at hx
      rcases hx with ⟨j, rfl⟩
      have h1 := hxsB xs[j] (List.getElem_mem j.isLt)
      have h2 := hloL.getD_lt j.val
      have : (i + 2) * (2 ^ k - 1) = (i + 1) * (2 ^ k - 1) + (2 ^ k - 1) := by ring
      omega
    have hupd_val : ∀ (xs : List ℕ), xs.length = L →
        Nat.ofDigits (2 ^ k) xs < (i + 1) * (2 ^ k) ^ (L - 1) →
        Nat.ofDigits (2 ^ k) (accAddList xs loDig) < (i + 2) * (2 ^ k) ^ (L - 1) := by
      intro xs hxsL hxsV
      rw [ofDigits_accAddList (2 ^ k) (by omega), Nat.ofDigits_digits]
      have : (i + 2) * (2 ^ k) ^ (L - 1) = (i + 1) * (2 ^ k) ^ (L - 1) + (2 ^ k) ^ (L - 1) := by
        ring
      omega
    have htab_tail : 0 < el.table ((FlowReduction.shiftedGraph I hv).tail e) :=
      Circulation.tail_label_pos (FlowReduction.shiftedGraph I hv) e
    have htab_head : 0 < el.table ((FlowReduction.shiftedGraph I hv).head e) :=
      Circulation.head_label_pos (FlowReduction.shiftedGraph I hv) e
    have hsum_step : ∀ (hc : c < act.length),
        (∑ e' : Fin I.m, if e'.val < i + 1 then
          FlowReduction.coefficient I e' ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e').lower else 0) =
        (∑ e' : Fin I.m, if e'.val < i then
          FlowReduction.coefficient I e' ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e').lower else 0) +
          FlowReduction.coefficient I e ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e).lower := by
      intro hc
      have hsplit : ∀ e' : Fin I.m,
          (if e'.val < i + 1 then
            FlowReduction.coefficient I e' ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e').lower else 0) =
          (if e'.val < i then
            FlowReduction.coefficient I e' ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e').lower else 0) +
          (if e' = e then
            FlowReduction.coefficient I e ⟨act[c]'hc, (hact.2 c hc).1⟩ * (I.edge e).lower else 0) := by
        intro e'
        by_cases he' : e' = e
        · subst he'; simp [e]
        · have hne : e'.val ≠ i := fun h => he' (Fin.ext h)
          have hiff : (e'.val < i + 1) ↔ (e'.val < i) := by omega
          simp [he', hiff]
      simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
      simp
    have hclt_iff : ∀ (hc : c < act.length), (c = lt) ↔ act[c]'hc = (I.edge e).tail := by
      intro hc
      obtain ⟨hvn, htabc⟩ := hact.2 c hc
      constructor
      · intro rfl
        have heq : el.table ⟨act[lt]'hc, hvn⟩ = el.table ((FlowReduction.shiftedGraph I hv).tail e) := by
          omega
        have hne : el.table ⟨act[lt]'hc, hvn⟩ ≠ 0 := by omega
        have hfin := (Circulation.endpointLabels_valid (FlowReduction.shiftedGraph I hv)).2 _ _ hne heq
        exact congrArg Fin.val hfin
      · intro hval
        have hfin : (⟨act[c]'hc, hvn⟩ : Fin I.n) = (FlowReduction.shiftedGraph I hv).tail e :=
          Fin.ext hval
        rw [hfin] at htabc; omega
    have hclh_iff : ∀ (hc : c < act.length), (c = lh) ↔ act[c]'hc = (I.edge e).head := by
      intro hc
      obtain ⟨hvn, htabc⟩ := hact.2 c hc
      constructor
      · intro rfl
        have heq : el.table ⟨act[lh]'hc, hvn⟩ = el.table ((FlowReduction.shiftedGraph I hv).head e) := by
          omega
        have hne : el.table ⟨act[lh]'hc, hvn⟩ ≠ 0 := by omega
        have hfin := (Circulation.endpointLabels_valid (FlowReduction.shiftedGraph I hv)).2 _ _ hne heq
        exact congrArg Fin.val hfin
      · intro hval
        have hfin : (⟨act[c]'hc, hvn⟩ : Fin I.n) = (FlowReduction.shiftedGraph I hv).head e :=
          Fin.ext hval
        rw [hfin] at htabc; omega
    obtain ⟨hpL, hnL, hpB, hnB, hpV, hnV, hdiff⟩ := hprev c
    have hmon_elem : ∀ x, x ≤ (i + 1) * (2 ^ k - 1) → x ≤ (i + 2) * (2 ^ k - 1) := by
      intro x hx
      have h1 : (i + 1) * (2 ^ k - 1) ≤ (i + 2) * (2 ^ k - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hmon_val : ∀ x, x < (i + 1) * (2 ^ k) ^ (L - 1) → x < (i + 2) * (2 ^ k) ^ (L - 1) := by
      intro x hx
      have h1 : (i + 1) * (2 ^ k) ^ (L - 1) ≤ (i + 2) * (2 ^ k) ^ (L - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hpos_step : edgePosRow I hv act L (i + 1) c =
        if (I.edge e).lower < 0 then
          Function.update (edgePosRow I hv act L i) lt (accAddList (edgePosRow I hv act L i lt) loDig) c
        else
          Function.update (edgePosRow I hv act L i) lh (accAddList (edgePosRow I hv act L i lh) loDig) c := by
      simp only [edgePosRow.eq_2, hlt, ↓reduceDIte]; rfl
    have hneg_step : edgeNegRow I hv act L (i + 1) c =
        if (I.edge e).lower < 0 then
          Function.update (edgeNegRow I hv act L i) lh (accAddList (edgeNegRow I hv act L i lh) loDig) c
        else
          Function.update (edgeNegRow I hv act L i) lt (accAddList (edgeNegRow I hv act L i lt) loDig) c := by
      simp only [edgeNegRow.eq_2, hlt, ↓reduceDIte]; rfl
    rw [hpos_step, hneg_step]
    by_cases hneg : (I.edge e).lower < 0
    · simp only [hneg, ↓reduceIte]
      have hp_upd : (Function.update (edgePosRow I hv act L i) lt
          (accAddList (edgePosRow I hv act L i lt) loDig) c).length = L ∧
          (∀ x ∈ Function.update (edgePosRow I hv act L i) lt
            (accAddList (edgePosRow I hv act L i lt) loDig) c, x ≤ (i + 2) * (2 ^ k - 1)) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgePosRow I hv act L i) lt
            (accAddList (edgePosRow I hv act L i lt) loDig) c) < (i + 2) * (2 ^ k) ^ (L - 1) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgePosRow I hv act L i) lt
            (accAddList (edgePosRow I hv act L i lt) loDig) c) =
            Nat.ofDigits (2 ^ k) (edgePosRow I hv act L i c) +
              if c = lt then (I.edge e).lower.natAbs else 0 := by
        by_cases hct : c = lt
        · subst hct; simp only [Function.update_self, ↓reduceIte, length_accAddList]
          exact ⟨hpL, hupd_elem _ hpL hpB, hupd_val _ hpL hpV,
            by rw [ofDigits_accAddList (2 ^ k) (by omega), Nat.ofDigits_digits]⟩
        · simp only [Function.update_of_ne hct, hct, ↓reduceIte, add_zero]
          exact ⟨hpL, fun x hx => hmon_elem x (hpB x hx), hmon_val _ hpV, trivial⟩
      have hn_upd : (Function.update (edgeNegRow I hv act L i) lh
          (accAddList (edgeNegRow I hv act L i lh) loDig) c).length = L ∧
          (∀ x ∈ Function.update (edgeNegRow I hv act L i) lh
            (accAddList (edgeNegRow I hv act L i lh) loDig) c, x ≤ (i + 2) * (2 ^ k - 1)) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgeNegRow I hv act L i) lh
            (accAddList (edgeNegRow I hv act L i lh) loDig) c) < (i + 2) * (2 ^ k) ^ (L - 1) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgeNegRow I hv act L i) lh
            (accAddList (edgeNegRow I hv act L i lh) loDig) c) =
            Nat.ofDigits (2 ^ k) (edgeNegRow I hv act L i c) +
              if c = lh then (I.edge e).lower.natAbs else 0 := by
        by_cases hch : c = lh
        · subst hch; simp only [Function.update_self, ↓reduceIte, length_accAddList]
          exact ⟨hnL, hupd_elem _ hnL hnB, hupd_val _ hnL hnV,
            by rw [ofDigits_accAddList (2 ^ k) (by omega), Nat.ofDigits_digits]⟩
        · simp only [Function.update_of_ne hch, hch, ↓reduceIte, add_zero]
          exact ⟨hnL, fun x hx => hmon_elem x (hnB x hx), hmon_val _ hnV, trivial⟩
      refine ⟨hp_upd.1, hn_upd.1, hp_upd.2.1, hn_upd.2.1, hp_upd.2.2.1, hn_upd.2.2.1, fun hc => ?_⟩
      rw [hp_upd.2.2.2, hn_upd.2.2.2, hsum_step hc, FlowReduction.coefficient]
      have hlo_eq : ((I.edge e).lower.natAbs : ℤ) = -(I.edge e).lower := by omega
      have hd := hdiff hc
      have h1 := hclt_iff hc
      have h2 := hclh_iff hc
      simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_zero]
      by_cases hct : c = lt
      · have ht := h1.mp hct
        by_cases hch : c = lh
        · have hh := h2.mp hch
          rw [ite_eq_left hct, ite_eq_left hch, ite_eq_left ht, ite_eq_left hh, hlo_eq]; linarith
        · have hh := mt h2.mpr hch
          rw [ite_eq_left hct, ite_eq_right hch, ite_eq_left ht, ite_eq_right hh, hlo_eq]; linarith
      · have ht := mt h1.mpr hct
        by_cases hch : c = lh
        · have hh := h2.mp hch
          rw [ite_eq_right hct, ite_eq_left hch, ite_eq_right ht, ite_eq_left hh, hlo_eq]; linarith
        · have hh := mt h2.mpr hch
          rw [ite_eq_right hct, ite_eq_right hch, ite_eq_right ht, ite_eq_right hh]; linarith
    · simp only [hneg, ↓reduceIte]
      have hp_upd : (Function.update (edgePosRow I hv act L i) lh
          (accAddList (edgePosRow I hv act L i lh) loDig) c).length = L ∧
          (∀ x ∈ Function.update (edgePosRow I hv act L i) lh
            (accAddList (edgePosRow I hv act L i lh) loDig) c, x ≤ (i + 2) * (2 ^ k - 1)) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgePosRow I hv act L i) lh
            (accAddList (edgePosRow I hv act L i lh) loDig) c) < (i + 2) * (2 ^ k) ^ (L - 1) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgePosRow I hv act L i) lh
            (accAddList (edgePosRow I hv act L i lh) loDig) c) =
            Nat.ofDigits (2 ^ k) (edgePosRow I hv act L i c) +
              if c = lh then (I.edge e).lower.natAbs else 0 := by
        by_cases hch : c = lh
        · subst hch; simp only [Function.update_self, ↓reduceIte, length_accAddList]
          exact ⟨hpL, hupd_elem _ hpL hpB, hupd_val _ hpL hpV,
            by rw [ofDigits_accAddList (2 ^ k) (by omega), Nat.ofDigits_digits]⟩
        · simp only [Function.update_of_ne hch, hch, ↓reduceIte, add_zero]
          exact ⟨hpL, fun x hx => hmon_elem x (hpB x hx), hmon_val _ hpV, trivial⟩
      have hn_upd : (Function.update (edgeNegRow I hv act L i) lt
          (accAddList (edgeNegRow I hv act L i lt) loDig) c).length = L ∧
          (∀ x ∈ Function.update (edgeNegRow I hv act L i) lt
            (accAddList (edgeNegRow I hv act L i lt) loDig) c, x ≤ (i + 2) * (2 ^ k - 1)) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgeNegRow I hv act L i) lt
            (accAddList (edgeNegRow I hv act L i lt) loDig) c) < (i + 2) * (2 ^ k) ^ (L - 1) ∧
          Nat.ofDigits (2 ^ k) (Function.update (edgeNegRow I hv act L i) lt
            (accAddList (edgeNegRow I hv act L i lt) loDig) c) =
            Nat.ofDigits (2 ^ k) (edgeNegRow I hv act L i c) +
              if c = lt then (I.edge e).lower.natAbs else 0 := by
        by_cases hct : c = lt
        · subst hct; simp only [Function.update_self, ↓reduceIte, length_accAddList]
          exact ⟨hnL, hupd_elem _ hnL hnB, hupd_val _ hnL hnV,
            by rw [ofDigits_accAddList (2 ^ k) (by omega), Nat.ofDigits_digits]⟩
        · simp only [Function.update_of_ne hct, hct, ↓reduceIte, add_zero]
          exact ⟨hnL, fun x hx => hmon_elem x (hnB x hx), hmon_val _ hnV, trivial⟩
      refine ⟨hp_upd.1, hn_upd.1, hp_upd.2.1, hn_upd.2.1, hp_upd.2.2.1, hn_upd.2.2.1, fun hc => ?_⟩
      rw [hp_upd.2.2.2, hn_upd.2.2.2, hsum_step hc, FlowReduction.coefficient]
      have hlo_eq : ((I.edge e).lower.natAbs : ℤ) = (I.edge e).lower := by omega
      have hd := hdiff hc
      have h1 := hclt_iff hc
      have h2 := hclh_iff hc
      simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_zero]
      by_cases hct : c = lt
      · have ht := h1.mp hct
        by_cases hch : c = lh
        · have hh := h2.mp hch
          rw [ite_eq_left hct, ite_eq_left hch, ite_eq_left ht, ite_eq_left hh, hlo_eq]; linarith
        · have hh := mt h2.mpr hch
          rw [ite_eq_left hct, ite_eq_right hch, ite_eq_left ht, ite_eq_right hh, hlo_eq]; linarith
      · have ht := mt h1.mpr hct
        by_cases hch : c = lh
        · have hh := h2.mp hch
          rw [ite_eq_right hct, ite_eq_left hch, ite_eq_right ht, ite_eq_left hh, hlo_eq]; linarith
        · have hh := mt h2.mpr hch
          rw [ite_eq_right hct, ite_eq_right hch, ite_eq_right ht, ite_eq_right hh]; linarith

/-! ### `stage0ShiftCaps`: shifted capacities for all `m` edges -/

wram_def stage0ShiftCaps (shiftOneCap : ℕ)
    (pEdges, m, pShCapBuf, pShCapLen, pTmpA, pTmpB, L, k) {
  off := 0
  dstOff := 0
  for i in 0 .. m {
    loSign := mem[pEdges + off + 2]
    loLen := mem[pEdges + off + 3]
    loPtr := mem[pEdges + off + 4]
    hiSign := mem[pEdges + off + 5]
    hiLen := mem[pEdges + off + 6]
    hiPtr := mem[pEdges + off + 7]
    len := shiftOneCap(loPtr, loSign, loLen, hiPtr, hiSign, hiLen,
      pShCapBuf + dstOff, pTmpA, pTmpB, L, k)
    mem[pShCapLen + i] := len
    off := off + 11
    dstOff := dstOff + L
  }
  return 0
}

structure Stage0ShiftCapsData where
  I : Instance
  hv : I.IsValid
  L : ℕ
  lenBuf : List ℕ
  tmpA0 : List ℕ
  tmpB0 : List ℕ

def stage0ShiftCapsSpec (w : ℕ) : Spec Stage0ShiftCapsData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ) (pTmpA : ℕ) (pTmpB : ℕ),
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, d.I.m, pShCapBuf, pShCapLen, pTmpA, pTmpB, d.L, k] ∧
      2 * k ≤ w ∧ 1 ≤ d.L ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L ∧
        (Nat.digits (2 ^ k) (d.I.edge e).upper.natAbs).length < d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      d.lenBuf.length = d.I.m ∧ d.tmpA0.length = d.L ∧ d.tmpB0.length = d.L⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m, Assn.list (pShCapBuf + i * d.L) (List.replicate d.L 0)) *
    Assn.list pShCapLen d.lenBuf * Assn.list pTmpA d.tmpA0 * Assn.list pTmpB d.tmpB0
  post := fun d args v => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pTmpA : ℕ) (pTmpB : ℕ) (tmpA1 : List ℕ) (tmpB1 : List ℕ),
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, d.I.m, pShCapBuf, pShCapLen, pTmpA, pTmpB, d.L, k] ∧ v = 0 ∧
      tmpA1.length = d.L ∧ tmpB1.length = d.L⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if h : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, h⟩)) d.L
        else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    Assn.list pTmpA tmpA1 * Assn.list pTmpB tmpB1

theorem stage0ShiftCaps_meets {w : ℕ} {p : Program} {f shiftOneCap : ℕ} {T1 : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ShiftCaps shiftOneCap))
    (h1 : Meets w p shiftOneCap ((stage0ShiftOneCapSpec w).withCost fun d _ => T1 d.L)) :
    Meets w p f ((stage0ShiftCapsSpec w).withCost fun d _ => (T1 d.L + 110) * d.I.m + 40) := by
  sep_enter d with h2k hL1 hcaps hltL hpE h11m hpB hmL hlenB htmpAL htmpBL
  have hk3 : 3 ≤ narrowLimbWidth d.I := three_le_narrowLimbWidth d.I
  sep_step; sep_step
  sep_for (fun i (t : List ℕ × List ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
      ⟨[pEdges, d.I.m, pShCapBuf, pShCapLen, pTmpA, pTmpB, d.L, narrowLimbWidth d.I,
        i * 11, i * d.L, i, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
        t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2],
      i ≤ d.I.m ∧ t.1.length = d.L ∧ t.2.1.length = d.L,
      (T1 d.L + 95) * (d.I.m - i) + 15,
      [Assn.list 0 (narrowEncode d.I),
       ∏ j ∈ Finset.range d.I.m,
         Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []),
       ∏ j ∈ Finset.range d.I.m,
         Assn.list (pShCapBuf + j * d.L)
           (if h : j < i ∧ j < d.I.m then
             padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
               ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j, h.2⟩)) d.L
           else List.replicate d.L 0),
       Assn.list pShCapLen
         ((List.ofFn fun j : Fin i =>
           if h : j.val < d.I.m then
             (Nat.digits (2 ^ narrowLimbWidth d.I)
               ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j.val, h⟩)).length
           else 0) ++
          d.lenBuf.drop i),
       Assn.list pTmpA t.1, Assn.list pTmpB t.2.1]⟩)
    with ⟨tmpA, tmpB, loS, loL, loP, hiS, hiL, hiP, len⟩
  · let e : Fin d.I.m := ⟨i, hhi⟩
    have hmem : i ∈ Finset.range d.I.m := Finset.mem_range.mpr hhi
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []))
    have hcurE : Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else []) =
        Assn.list (pEdges + i * 11) (edgeRec d.I e) := by simp [e, hhi]
    sep_apply hcurE
    have hedgeRec_len : (edgeRec d.I e).length = 11 := rfl
    sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
    simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ] at hloSign hloLen hloPtr hhiSign hhiLen hhiPtr
    subst loSign loLen loPtr hiSign hiLen hiPtr
    sep_apply hcurE.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []))).symm
    -- Pull dst block i and input edge i's lower/upper limbs
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pShCapBuf + j * d.L)
        (if h : j < i ∧ j < d.I.m then
          padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
            ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j, h.2⟩)) d.L
        else List.replicate d.L 0))
    have hcurB : Assn.list (pShCapBuf + i * d.L)
        (if h : i < i ∧ i < d.I.m then
          padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
            ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, h.2⟩)) d.L
        else List.replicate d.L 0) = Assn.list (pShCapBuf + i * d.L) (List.replicate d.L 0) := by
      simp
    sep_apply hcurB
    sep_apply list_narrowEncode_split d.I d.hv
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (edgeStartPos d.I j)
        (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else []))
    have hcurW : Assn.list (edgeStartPos d.I i)
        (if h : i < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨i, h⟩) else []) =
        Assn.list (edgeStartPos d.I i) (narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge e)) := by
      simp [e, hhi]
    sep_apply hcurW
    sep_apply list_narrowEdgeWords d.I e
    sep_apply list_intWords (edgeStartPos d.I e.val + 2) (narrowLimbWidth d.I) (d.I.edge e).lower
    sep_apply list_intWords (edgeHiPos d.I e) (narrowLimbWidth d.I) (d.I.edge e).upper
    have hloAtom :
        Assn.list (edgeStartPos d.I e.val + 2 + 2)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs) =
        Assn.list (edgeLoPtr d.I e)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs) := rfl
    have hhiAtom :
        Assn.list (edgeHiPos d.I e + 2)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).upper.natAbs) =
        Assn.list (edgeHiPtr d.I e)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).upper.natAbs) := rfl
    sep_apply hloAtom; sep_apply hhiAtom
    generalize hF :
      ((0 ↦ narrowLimbWidth d.I) * (1 ↦ d.I.n) * (2 ↦ d.I.m) *
       (edgeStartPos d.I e.val ↦ (d.I.edge e).tail) *
       (edgeStartPos d.I e.val + 1 ↦ (d.I.edge e).head) *
       (edgeStartPos d.I e.val + 2 ↦ if (d.I.edge e).lower < 0 then 1 else 0) *
       (edgeStartPos d.I e.val + 2 + 1 ↦
         (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length) *
       (edgeHiPos d.I e ↦ if (d.I.edge e).upper < 0 then 1 else 0) *
       (edgeHiPos d.I e + 1 ↦
         (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).upper.natAbs).length) *
       Assn.list (edgeCostPos d.I e) (intWords (narrowLimbWidth d.I) (d.I.edge e).cost) *
       (∏ j ∈ (Finset.range d.I.m).erase i,
         Assn.list (edgeStartPos d.I j)
           (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else [])) *
       (∏ v ∈ Finset.range d.I.n,
         Assn.list (demStartPos d.I v)
           (if h : v < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d v) else [])) *
       (∏ j ∈ Finset.range d.I.m,
         Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else [])) *
       (∏ j ∈ (Finset.range d.I.m).erase i,
         Assn.list (pShCapBuf + j * d.L)
           (if h : j < i ∧ j < d.I.m then
             padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
               ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j, h.2⟩)) d.L
           else List.replicate d.L 0)) *
       Assn.list pShCapLen
         ((List.ofFn fun j : Fin i =>
           if h : j.val < d.I.m then
             (Nat.digits (2 ^ narrowLimbWidth d.I)
               ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j.val, h⟩)).length
           else 0) ++
          d.lenBuf.drop i)) = F
    have hcap_e := hcaps e
    have hlo_e := (hltL e).1
    have hhi_e := (hltL e).2
    sep_apply hF
    sep_step from (⟨narrowLimbWidth d.I, d.L, (d.I.edge e).lower, (d.I.edge e).upper,
      List.replicate d.L 0, tmpA, tmpB⟩ : ShiftOneCapData) with htmpA1 htmpB1
    subst F; sep_norm
    -- Reassemble narrowEncode I
    sep_apply hloAtom.symm; sep_apply hhiAtom.symm
    sep_apply (list_intWords (edgeStartPos d.I e.val + 2) (narrowLimbWidth d.I) (d.I.edge e).lower).symm
    sep_apply (list_intWords (edgeHiPos d.I e) (narrowLimbWidth d.I) (d.I.edge e).upper).symm
    sep_apply (list_narrowEdgeWords d.I e).symm
    sep_apply hcurW.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (edgeStartPos d.I j)
        (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else []))).symm
    sep_apply (list_narrowEncode_split d.I d.hv).symm
    -- Reassemble pShCapBuf product for i + 1
    have hbuf_next :
        Assn.list (pShCapBuf + i * d.L)
          (padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) ((d.I.edge e).upper - (d.I.edge e).lower).toNat) d.L) *
        (∏ j ∈ (Finset.range d.I.m).erase i,
          Assn.list (pShCapBuf + j * d.L)
            (if h : j < i ∧ j < d.I.m then
              padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
                ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j, h.2⟩)) d.L
            else List.replicate d.L 0)) =
        ∏ j ∈ Finset.range d.I.m,
          Assn.list (pShCapBuf + j * d.L)
            (if h : j < i + 1 ∧ j < d.I.m then
              padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
                ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j, h.2⟩)) d.L
            else List.replicate d.L 0) := by
      rw [Assn.prod_eq_mul_erase hmem]
      congr 1
      · simp [e, hhi, FlowReduction.shiftedGraph]
      · apply Finset.prod_congr rfl
        intro j hj
        have hne : j ≠ i := Finset.ne_of_mem_erase hj
        by_cases hji : j < i ∧ j < d.I.m
        · have hji2 : j < i + 1 ∧ j < d.I.m := ⟨by omega, hji.2⟩
          simp only [hji, hji2]
        · have hji2 : ¬ (j < i + 1 ∧ j < d.I.m) := by omega
          simp only [hji, hji2]
    sep_apply hbuf_next
    have hlen_l : ((List.ofFn fun j : Fin i =>
        if h : j.val < d.I.m then
          (Nat.digits (2 ^ narrowLimbWidth d.I)
            ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j.val, h⟩)).length
        else 0) ++
        d.lenBuf.drop i).length = d.I.m := by simp; omega
    have hnext_mul : i * d.L + d.L = (i + 1) * d.L := by ring
    have hnext_lt : (i + 1) * d.L ≤ d.I.m * d.L := Nat.mul_le_mul_right d.L (by omega)
    sep_step
    have hset_len :
        ((List.ofFn fun j : Fin i =>
            if h : j.val < d.I.m then
              (Nat.digits (2 ^ narrowLimbWidth d.I)
                ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j.val, h⟩)).length
            else 0) ++
          d.lenBuf.drop i).set i len_1 =
        (List.ofFn fun j : Fin (i + 1) =>
            if h : j.val < d.I.m then
              (Nat.digits (2 ^ narrowLimbWidth d.I)
                ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j.val, h⟩)).length
            else 0) ++
          d.lenBuf.drop (i + 1) := by
      rw [set_append_drop (by simp) (by omega), List.ofFn_succ']
      simp [hlen_1, e, hhi, FlowReduction.shiftedGraph]
    sep_apply (show Assn.list pShCapLen _ = Assn.list pShCapLen _ from congrArg (Assn.list pShCapLen) hset_len)
    sep_step; sep_step
  · have hbuf_fin :
        (∏ j ∈ Finset.range d.I.m,
          Assn.list (pShCapBuf + j * d.L)
            (if h : j < d.I.m ∧ j < d.I.m then
              padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
                ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j, h.2⟩)) d.L
            else List.replicate d.L 0)) =
        ∏ j ∈ Finset.range d.I.m,
          Assn.list (pShCapBuf + j * d.L)
            (if h : j < d.I.m then
              padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
                ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j, h⟩)) d.L
            else []) := by
      apply Finset.prod_congr rfl; intro j hj; simp [Finset.mem_range.mp hj]
    have hlen_fin :
        ((List.ofFn fun j : Fin d.I.m =>
            if h : j.val < d.I.m then
              (Nat.digits (2 ^ narrowLimbWidth d.I)
                ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨j.val, h⟩)).length
            else 0) ++ d.lenBuf.drop d.I.m) =
        List.ofFn fun e : Fin d.I.m =>
          (Nat.digits (2 ^ narrowLimbWidth d.I)
            ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length := by
      rw [List.drop_of_length_le (by omega), List.append_nil]
      apply List.ext_getElem <;> simp
    sep_apply hbuf_fin
    sep_apply (show Assn.list pShCapLen _ = Assn.list pShCapLen _ from congrArg (Assn.list pShCapLen) hlen_fin)
    sep_step

/-! ### `stage0ShiftDemInit`: initialize lazy demand accumulators from `I.d (act[c])` -/

end MinCostFlow.NarrowProg
