module

public import MinCostFlow.LastLevelProgram.CanonicalOracle
public import MinCostFlow.LastLevelProgram.FixedPoint
import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.PadicValNat

/-!
# Caller-independent fixed-point query format

The tree query in Definition 5.8 (pages 19–20) uses a common scale for
lengths and weights. Use the least exact length precision, enlarged by
the fixed weight-grid precision, and choose the signed block width
from the resulting numerators.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

/-- A vector is on the binary grid if each value has an integer numerator. -/
def OnQueryGrid (P : ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ e, ∃ a : ℤ, x e = (a : ℝ) / (2 : ℝ)^P

/-- Increasing the precision preserves exact encodability. -/
theorem OnQueryGrid.mono {P Q : ℕ} {x : ℕ → ℝ}
    (hx : OnQueryGrid P x) (h : P ≤ Q) : OnQueryGrid Q x := by
  intro e
  obtain ⟨a,ha⟩ := hx e
  refine ⟨a * (2 : ℤ)^(Q-P), ?_⟩
  rw [ha, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    ← Nat.add_sub_of_le h, pow_add]
  field_simp
  congr 2
  omega

/-- Use the minimum exact length precision, with zero as a fallback for
inputs outside the dyadic domain. -/
noncomputable def lengthQueryPrecision (x : ℕ → ℝ) : ℕ :=
  open Classical in
  if h : ∃ P, OnQueryGrid P x then Nat.find h else 0

/-- The least precision represents every value of a dyadic length vector. -/
theorem lengthQueryPrecision_exact {x : ℕ → ℝ} (h : ∃ P, OnQueryGrid P x) :
    OnQueryGrid (lengthQueryPrecision x) x := by
  classical
  rw [lengthQueryPrecision, dite_eq_left h]
  exact Nat.find_spec h

/-- The query precision is never larger than the maximum of the input
length precision and the model's weight precision. -/
theorem lengthQueryPrecision_le {x : ℕ → ℝ} {P : ℕ} (h : OnQueryGrid P x) :
    lengthQueryPrecision x ≤ P := by
  classical
  rw [lengthQueryPrecision, dite_eq_left (show ∃ Q, OnQueryGrid Q x from ⟨P,h⟩)]
  exact Nat.find_min' _ h

/-- Reducing the fractional precision is exact precisely when the dropped
power of two divides each integer numerator. -/
theorem onQueryGrid_div_iff {P Q : ℕ} (hQP : Q ≤ P) (a : ℕ → ℤ) :
    OnQueryGrid Q (fun e => (a e : ℝ) / (2 : ℝ)^P) ↔
      ∀ e, (2 : ℤ)^(P-Q) ∣ a e := by
  have hp : (2 : ℝ)^P = (2 : ℝ)^Q * (2 : ℝ)^(P-Q) := by
    rw [← pow_add,Nat.add_sub_of_le hQP]
  constructor
  · intro hg e
    obtain ⟨b,hb⟩ := hg e
    refine ⟨b,?_⟩
    have hb' : (a e : ℝ) = (2 : ℝ)^(P-Q) * (b : ℝ) := by
      rw [hp] at hb
      field_simp at hb
      linarith only [hb]
    exact_mod_cast hb'
  · intro hd e
    obtain ⟨b,hb⟩ := hd e
    refine ⟨b,?_⟩
    change (a e : ℝ) / (2 : ℝ)^P = _
    rw [hb, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hp]
    field_simp

/-- The least exact precision is obtained by removing the greatest
common power of two, capped at the original precision. -/
theorem lengthQueryPrecision_of_commonShift {P d : ℕ} (a : ℕ → ℤ)
    (hd : d ≤ P) (hdiv : ∀ e, (2 : ℤ)^d ∣ a e)
    (hmax : ∀ k ≤ P, (∀ e, (2 : ℤ)^k ∣ a e) → k ≤ d) :
    lengthQueryPrecision (fun e => (a e : ℝ) / (2 : ℝ)^P) = P-d := by
  let x := fun e => (a e : ℝ) / (2 : ℝ)^P
  have hg : OnQueryGrid (P-d) x := (onQueryGrid_div_iff (by omega) a).2
    (by simpa only [show P-(P-d) = d by omega] using hdiv)
  have hle := lengthQueryPrecision_le hg
  have hgrid := lengthQueryPrecision_exact ⟨P-d,hg⟩
  have hdiv' := (onQueryGrid_div_iff (show lengthQueryPrecision x ≤ P by omega) a).1 hgrid
  have hk := hmax (P-lengthQueryPrecision x) (Nat.sub_le ..) hdiv'
  change lengthQueryPrecision x = P-d
  omega

/-- Scan nonzero integer magnitudes for the smallest binary valuation.
Zero entries impose no restriction. The initial value caps the shift. -/
def commonLengthShift (P : ℕ) (xs : List ℕ) : ℕ :=
  xs.foldr (fun n d => if n = 0 then d else min (padicValNat 2 n) d) P

/-- The scan returns the greatest admissible common shift. -/
theorem le_commonLengthShift_iff (P k : ℕ) (xs : List ℕ) :
    k ≤ commonLengthShift P xs ↔ k ≤ P ∧ ∀ n ∈ xs, 2^k ∣ n := by
  induction xs with
  | nil => simp [commonLengthShift]
  | cons n xs ih =>
    by_cases hn : n = 0
    · subst n
      simpa [commonLengthShift, List.forall_mem_cons] using ih
    · simpa only [commonLengthShift,List.foldr_cons,ite_eq_right hn,le_min_iff,
        List.forall_mem_cons, ← Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hn,
        and_left_comm] using
        (and_congr_right (a := 2^k ∣ n) fun _ => ih)

/-- A finite list covering the nonzero numerators suffices to recover
the least precision of the entire length vector. -/
theorem lengthQueryPrecision_of_scan (P : ℕ) (a : ℕ → ℤ) (xs : List ℕ)
    (hx : ∀ n, n ≠ 0 → (n ∈ xs ↔ ∃ e, (a e).natAbs = n)) :
    lengthQueryPrecision (fun e => (a e : ℝ) / (2 : ℝ)^P) =
      P-commonLengthShift P xs := by
  let d := commonLengthShift P xs
  have hd := (le_commonLengthShift_iff P d xs).1 (le_refl d)
  apply lengthQueryPrecision_of_commonShift a hd.1
  · intro e
    by_cases he : (a e).natAbs = 0
    · have ha : a e = 0 := Int.natAbs_eq_zero.mp he
      simp [ha]
    · have hm := hd.2 _ ((hx _ he).2 ⟨e,rfl⟩)
      exact_mod_cast (Int.natAbs_dvd_natAbs.1 (by simpa using hm) :
        (Int.ofNat (2^d)) ∣ a e)
  · intro k hk ha
    apply (le_commonLengthShift_iff P k xs).2
    refine ⟨hk, fun n hn => ?_⟩
    by_cases hz : n = 0
    · simp [hz]
    · obtain ⟨e,he⟩ := (hx n hz).1 hn
      rw [← he]
      simpa using Int.natAbs_dvd_natAbs.2 (ha e)

/-- The graph's integer query format uses one bit per limb. -/
noncomputable def graphQueryPrecision (weightGrid : ℕ) (lengths : ℕ → ℝ) : ℕ :=
  max weightGrid (lengthQueryPrecision lengths)

/-- Both vectors can be represented exactly at the selected common precision. -/
theorem graphQueryPrecision_exact {weightGrid : ℕ} {lengths weights : ℕ → ℝ}
    (hl : ∃ P, OnQueryGrid P lengths) (hw : OnQueryGrid weightGrid weights) :
    OnQueryGrid (graphQueryPrecision weightGrid lengths) lengths ∧
      OnQueryGrid (graphQueryPrecision weightGrid lengths) weights :=
  ⟨(lengthQueryPrecision_exact hl).mono (le_max_right ..), hw.mono (le_max_left ..)⟩

/-- Reserve a sign bit above the largest length or weight numerator.
The width depends only on the maximum, so the program can scan bit
counts without adding multiword numerators. -/
noncomputable def graphQueryLimbs (G : MGraph) (P weightBound : ℕ) (lengths : ℕ → ℝ) : ℕ :=
  (max weightBound (G.E.sup fun e => (queryNumerator P (lengths e)).natAbs)).size + 1

private theorem fits_queryLimbs_of_bound {n B : ℕ} (h : n ≤ B) :
    Num.Fits 1 (B.size+1) (n : ℤ) := by
  have hn := h.trans_lt (Nat.lt_size_self B)
  have hp : (2 * n : ℕ) < Num.capacity 1 (B.size+1) := by
    change 2 * n < (2 : ℕ)^(B.size+1)
    rw [pow_succ]
    omega
  unfold Num.Fits
  constructor
  · have hcap : (0 : ℤ) ≤ (Num.capacity 1 (B.size+1) : ℤ) := by positivity
    omega
  · exact_mod_cast hp

/-- Every nonnegative length numerator fits the graph-derived width. -/
theorem graphQueryLimbs_length {G : MGraph} {P B e : ℕ} {lengths : ℕ → ℝ}
    (he : e ∈ G.E) (h : 0 ≤ queryNumerator P (lengths e)) :
    Num.Fits 1 (graphQueryLimbs G P B lengths) (queryNumerator P (lengths e)) := by
  rw [← Int.natAbs_of_nonneg h]
  apply fits_queryLimbs_of_bound
  exact (Finset.le_sup (f := fun f => (queryNumerator P (lengths f)).natAbs) he).trans
    (le_max_right ..)

/-- The same width fits any nonnegative weight numerator bounded by the
round-independent weight bound. -/
theorem graphQueryLimbs_weight {G : MGraph} {P B : ℕ} {lengths : ℕ → ℝ} {a : ℤ}
    (ha : 0 ≤ a) (hB : a.natAbs ≤ B) :
    Num.Fits 1 (graphQueryLimbs G P B lengths) a := by
  rw [← Int.natAbs_of_nonneg ha]
  apply fits_queryLimbs_of_bound
  exact hB.trans (le_max_left ..)

/-- The widest numerator can be found by taking the maximum of the
individual bit counts. -/
theorem graphQueryLimbs_eq_maxSize (G : MGraph) (P B : ℕ) (len : ℕ → ℝ) :
    graphQueryLimbs G P B len =
      max B.size (G.E.sup fun e => (queryNumerator P (len e)).natAbs.size) + 1 := by
  let n := fun e => (queryNumerator P (len e)).natAbs
  change (max B (G.E.sup n)).size+1 = max B.size (G.E.sup fun e => (n e).size)+1
  congr 1
  apply le_antisymm
  · apply Nat.size_le.mpr
    apply max_lt
    · exact (Nat.size_le).mp (le_max_left ..)
    · let k := max B.size (G.E.sup fun f => (n f).size)
      have hs : G.E.sup n ≤ 2^k-1 := by
        apply (Finset.sup_le_iff).2
        intro e he
        have hsz : (n e).size ≤ k :=
          (Finset.le_sup (f := fun f => (n f).size) he).trans (le_max_right ..)
        have hp := (Nat.size_le).mp hsz
        omega
      change G.E.sup n < 2^k
      have hp := Nat.two_pow_pos k
      omega
  · apply max_le (Nat.size_le_size (le_max_left ..))
    apply (Finset.sup_le_iff).2
    intro e he
    exact Nat.size_le_size ((Finset.le_sup (f := n) he).trans (le_max_right ..))

/-- The last-level query grid refines the exact lengths and the model's
weight grid on the representative graph. -/
noncomputable def roundQueryPrecision (C : ℝ) (G : MGraph) (len : ℕ → ℝ) : ℕ :=
  graphQueryPrecision (weightPrecision C G) len

/-- The last-level width includes the bound of twice the edge count on
each live weight during multiplicative weights. -/
noncomputable def roundQueryLimbs (C : ℝ) (G : MGraph) (len : ℕ → ℝ) : ℕ :=
  let P := roundQueryPrecision C G len
  graphQueryLimbs G P (2 * G.m * 2^P) len

/-- The round-derived width provides the strict capacity inequality
needed by the weight fit argument. -/
theorem roundQueryLimbs_weightCapacity (C : ℝ) (G : MGraph) (len : ℕ → ℝ) :
    2 * (2 : ℝ)^roundQueryPrecision C G len * (2 * (G.m : ℝ)) <
      Num.capacity 1 (roundQueryLimbs C G len) := by
  let P := roundQueryPrecision C G len
  let B := 2 * G.m * 2^P
  have hf : Num.Fits 1 (roundQueryLimbs C G len) (B : ℤ) :=
    graphQueryLimbs_weight (G := G) (P := P) (B := B) (lengths := len)
      (a := (B : ℤ)) (Int.natCast_nonneg _) (by simp)
  have hn : 2 * B < Num.capacity 1 (roundQueryLimbs C G len) := by
    exact_mod_cast hf.2
  have hr : (2 * B : ℕ) < Num.capacity 1 (roundQueryLimbs C G len) := hn
  have hc : ((2 * B : ℕ) : ℝ) < (Num.capacity 1 (roundQueryLimbs C G len) : ℝ) := by
    exact_mod_cast hr
  calc
    _ = ((2 * B : ℕ) : ℝ) := by dsimp [B,P]; push_cast; ring
    _ < _ := hc

/-- A vector containing one unit of its caller grid needs the full
caller precision in the exact guest format. -/
theorem lengthQueryPrecision_eq_of_unit {P : ℕ} {a : ℕ → ℤ} {e : ℕ}
    (he : a e = 1) :
    lengthQueryPrecision (fun f => (a f : ℝ) / (2 : ℝ)^P) = P := by
  let len := fun f => (a f : ℝ) / (2 : ℝ)^P
  have hgrid : OnQueryGrid P len := fun f => ⟨a f,rfl⟩
  have hle := lengthQueryPrecision_le hgrid
  have hd := (onQueryGrid_div_iff hle a).mp (lengthQueryPrecision_exact ⟨P,hgrid⟩) e
  rw [he] at hd
  have hn := Int.natAbs_dvd_natAbs.mpr hd
  have hone : (2 : ℕ)^(P-lengthQueryPrecision len) = 1 := by
    change (2 : ℤ).natAbs^(P-lengthQueryPrecision len) ∣ (1 : ℤ).natAbs at hn
    exact Nat.dvd_one.mp hn
  have hzero : P-lengthQueryPrecision len = 0 := by
    by_contra hp
    have htwo : 2 ≤ (2 : ℕ)^(P-lengthQueryPrecision len) :=
      Nat.le_self_pow hp 2
    omega
  change lengthQueryPrecision len = P
  exact Nat.le_antisymm hle (by omega)

/-- The exact guest width is at least the caller precision plus one
when a length is one unit of the caller grid and the graph has an edge. -/
theorem roundQueryLimbs_ge_of_unit (C : ℝ) (G : MGraph) (P : ℕ) (a : ℕ → ℤ)
    (hm : 0 < G.m) {e : ℕ} (he : a e = 1) :
    P+1 ≤ roundQueryLimbs C G (fun f => (a f : ℝ) / (2 : ℝ)^P) := by
  let len := fun f => (a f : ℝ) / (2 : ℝ)^P
  let Q := roundQueryPrecision C G len
  have hQ : P ≤ Q := by
    change P ≤ max (weightPrecision C G) (lengthQueryPrecision len)
    rw [lengthQueryPrecision_eq_of_unit he]
    exact le_max_right ..
  change P+1 ≤ graphQueryLimbs G Q (2*G.m*2^Q) len
  rw [graphQueryLimbs_eq_maxSize]
  have hsize : (2*G.m*2^Q).size = (2*G.m).size+Q := by
    rw [← Nat.shiftLeft_eq,Nat.size_shiftLeft (by omega : 2*G.m ≠ 0)]
  rw [hsize]
  exact Nat.succ_le_succ (le_max_of_le_left (by omega))

end MinCostFlow.LastLevelProgram
