module

public import MinCostFlow.Statement.Problem
public import MinCostFlow.NarrowProg.ReadInt
public import MinCostFlow.NarrowProg.TopBitLength
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.GeneralScalingModel
public import MinCostFlow.Scaling.ReductionCapacityBounds
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

/-!
# Narrow-word encoding definitions, bit-width bounds, and Stage 0/3 space budgets

Defines the base-`2 ^ k` instance and answer encoding (`narrowEncode`, `narrowIsCorrectAnswer`,
matching `track/narrow-statement:MinCostFlow/Statement/Problem.lean` by unfolding), proves the
automatic bit-width bounds implied by `k = narrowLimbWidth I` (`6 * I.m + 1 < 2 ^ k`,
`narrowAnswer_length_le_encode`, digit-length monotonicity and `clog` bounds), and fixes the
explicit space budget `narrowMainSpace` and word-size predicate `NarrowMainFits`.
-/

@[expose] public section

open WordRAM WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Narrow-word instance and answer encoding -/

/-- Number of bits of an integer `x`: one sign bit plus `Nat.log 2 |x| + 1` binary digits. -/
def narrowIntBits (x : ℤ) : ℕ :=
  Nat.log 2 x.natAbs + 2

/-- Number of bits of an edge (tail, head, lower, upper, cost). -/
def narrowEdgeBits (e : Edge) : ℕ :=
  narrowIntBits e.tail + narrowIntBits e.head + narrowIntBits e.lower +
    narrowIntBits e.upper + narrowIntBits e.cost

/-- Total bit length `z` of an instance (Section 2, page 7). -/
def narrowBitLength (I : Instance) : ℕ :=
  narrowIntBits I.n + narrowIntBits I.m +
    (I.edges.map narrowEdgeBits).sum + (I.demand.map narrowIntBits).sum

/-- Limb width `k = ⌊log₂ z⌋ + 1`, satisfying `z < 2 ^ k ≤ 2 * z`. -/
def narrowLimbWidth (I : Instance) : ℕ :=
  Nat.log 2 (narrowBitLength I) + 1

/-- An edge written in base `2 ^ k`: `tail`, `head`, then `lower`, `upper`, `cost` via `intWords`. -/
def narrowEdgeWords (k : ℕ) (e : Edge) : List ℕ :=
  e.tail :: e.head :: (intWords k e.lower ++ intWords k e.upper ++ intWords k e.cost)

/-- The instance written as a list of words in base `2 ^ k` (`k = narrowLimbWidth I`). -/
def narrowEncode (I : Instance) : List ℕ :=
  let k := narrowLimbWidth I
  k :: I.n :: I.m :: (I.edges.flatMap (narrowEdgeWords k) ++ I.demand.flatMap (intWords k))

/-- Correct answer in base `2 ^ (narrowLimbWidth I)`: `[0]` if infeasible, or `1` followed by
the `intWords`-encoded values of an integral minimum-cost flow. -/
def narrowIsCorrectAnswer (I : Instance) (out : List ℕ) : Prop :=
  (out = [0] ∧ ∀ f, ¬ I.IsFeasible f) ∨
  ∃ f : Fin I.m → ℤ, I.IsMinCostFlow (fun j => (f j : ℝ)) ∧
    out = 1 :: (List.finRange I.m).flatMap fun j => intWords (narrowLimbWidth I) (f j)

/-- Number of base-`2 ^ k` limbs of `U = I.maxCapacity`. -/
def narrowMaxCapLimbs (I : Instance) : ℕ :=
  (Nat.digits (2 ^ narrowLimbWidth I) I.maxCapacity).length

/-- Number of base-`2 ^ k` limbs of `C = I.maxCost`. -/
def narrowMaxCostLimbs (I : Instance) : ℕ :=
  (Nat.digits (2 ^ narrowLimbWidth I) I.maxCost).length

/-! ### Bit-length and limb-width inequalities -/

private theorem sum_map_ge_const {α : Type} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, c ≤ f x) : c * l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have : c * (l.length + 1) = c + c * l.length := by ring
    omega

theorem narrowIntBits_ge_two (x : ℤ) : 2 ≤ narrowIntBits x := by
  unfold narrowIntBits; omega

theorem narrowEdgeBits_ge_ten (e : Edge) : 10 ≤ narrowEdgeBits e := by
  unfold narrowEdgeBits
  have h1 := narrowIntBits_ge_two e.tail
  have h2 := narrowIntBits_ge_two e.head
  have h3 := narrowIntBits_ge_two e.lower
  have h4 := narrowIntBits_ge_two e.upper
  have h5 := narrowIntBits_ge_two e.cost
  omega

theorem narrowBitLength_ge (I : Instance) (hv : I.IsValid) :
    10 * I.m + 2 * I.n + 4 ≤ narrowBitLength I := by
  unfold narrowBitLength
  have hn := narrowIntBits_ge_two I.n
  have hm := narrowIntBits_ge_two I.m
  have he := sum_map_ge_const I.edges narrowEdgeBits 10 (fun e _ => narrowEdgeBits_ge_ten e)
  have hd := sum_map_ge_const I.demand narrowIntBits 2 (fun x _ => narrowIntBits_ge_two x)
  rw [hv.2] at hd
  change 10 * I.m ≤ (I.edges.map narrowEdgeBits).sum at he
  omega

theorem four_le_narrowBitLength (I : Instance) : 4 ≤ narrowBitLength I := by
  unfold narrowBitLength
  have hn := narrowIntBits_ge_two I.n
  have hm := narrowIntBits_ge_two I.m
  omega

theorem narrowBitLength_lt_pow_limbWidth (I : Instance) :
    narrowBitLength I < 2 ^ narrowLimbWidth I := by
  unfold narrowLimbWidth
  exact Nat.lt_pow_succ_log_self (by decide) (narrowBitLength I)

theorem three_le_narrowLimbWidth (I : Instance) : 3 ≤ narrowLimbWidth I := by
  unfold narrowLimbWidth
  have h4 : 4 ≤ narrowBitLength I := four_le_narrowBitLength I
  have hlog : 2 ≤ Nat.log 2 (narrowBitLength I) := by
    have : Nat.log 2 4 ≤ Nat.log 2 (narrowBitLength I) := Nat.log_mono_right h4
    have h2 : Nat.log 2 4 = 2 := by decide
    omega
  omega

theorem one_le_narrowLimbWidth (I : Instance) : 1 ≤ narrowLimbWidth I :=
  le_trans (by decide) (three_le_narrowLimbWidth I)

theorem six_mul_m_add_one_lt_pow_limbWidth (I : Instance) (hv : I.IsValid) :
    6 * I.m + 1 < 2 ^ narrowLimbWidth I := by
  have h1 := narrowBitLength_ge I hv
  have h2 := narrowBitLength_lt_pow_limbWidth I
  omega

theorem two_mul_m_add_one_lt_pow_limbWidth (I : Instance) (hv : I.IsValid) :
    2 * I.m + 1 < 2 ^ narrowLimbWidth I := by
  have := six_mul_m_add_one_lt_pow_limbWidth I hv; omega

theorem m_add_one_lt_pow_limbWidth (I : Instance) (hv : I.IsValid) :
    I.m + 1 < 2 ^ narrowLimbWidth I := by
  have := six_mul_m_add_one_lt_pow_limbWidth I hv; omega

theorem n_add_one_lt_pow_limbWidth (I : Instance) (hv : I.IsValid) :
    I.n + 1 < 2 ^ narrowLimbWidth I := by
  have h1 := narrowBitLength_ge I hv
  have h2 := narrowBitLength_lt_pow_limbWidth I
  omega

theorem two_mul_lt_pow_of_three_le {k : ℕ} (hk : 3 ≤ k) : 2 * k < 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h3 : k < 3
    · have hk2 : k = 2 := by omega
      subst hk2; decide
    · have hih := ih (by omega)
      rw [Nat.pow_succ]
      omega

theorem limbWidth_log_bound {k w : ℕ} (hk : 3 ≤ k) (h2k : 2 * k + 1 ≤ w) :
    k + Nat.log 2 (2 * k) + 2 ≤ w := by
  have hlt : 2 * k < 2 ^ k := two_mul_lt_pow_of_three_le hk
  have hlog : Nat.log 2 (2 * k) < k := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
  omega

/-! ### Digit-length and input magnitude bounds -/

theorem digits_length_mono {b x y : ℕ} (hb : 1 < b) (h : x ≤ y) :
    (Nat.digits b x).length ≤ (Nat.digits b y).length := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hy : y ≠ 0 := by omega
    rw [Nat.length_digits b x hb hx, Nat.length_digits b y hb hy]
    exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem digits_length_le_clog {k x : ℕ} (hk : 1 ≤ k) :
    (Nat.digits (2 ^ k) x).length ≤ Nat.clog 2 (x + 1) := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hb : 1 < 2 ^ k := by have := two_le_pow hk; omega
    have hlen : (Nat.digits (2 ^ k) x).length = Nat.log (2 ^ k) x + 1 :=
      Nat.length_digits (2 ^ k) x hb hx
    rw [hlen]
    have hlt : (2 ^ k) ^ (Nat.log (2 ^ k) x) ≤ x := Nat.pow_log_le_self (2 ^ k) hx
    have hpow2 : 2 ^ (Nat.log (2 ^ k) x) ≤ (2 ^ k) ^ (Nat.log (2 ^ k) x) :=
      Nat.pow_le_pow_left (two_le_pow hk) _
    have hclog := Nat.le_pow_clog (by decide : 1 < 2) (x + 1)
    have hlt2 : 2 ^ (Nat.log (2 ^ k) x) < 2 ^ Nat.clog 2 (x + 1) := by omega
    have hlt_exp : Nat.log (2 ^ k) x < Nat.clog 2 (x + 1) :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt2
    omega

theorem digits_canonical {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    CanonicalLimbs k (Nat.digits (2 ^ k) n) :=
  ⟨digits_limbs hk n, fun h => digits_getLast_ne_zero n h⟩

private theorem mem_le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem lower_natAbs_le_maxCapacity' (I : Instance) (e : Fin I.m) :
    (I.edge e).lower.natAbs ≤ I.maxCapacity := by
  unfold Instance.maxCapacity
  have hmem : max (I.edge e).lower.natAbs (I.edge e).upper.natAbs ∈
      (I.edges.map fun e => max e.lower.natAbs e.upper.natAbs) ++ I.demand.map Int.natAbs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)
  exact le_trans (le_max_left _ _) (mem_le_foldr_max hmem)

theorem upper_natAbs_le_maxCapacity' (I : Instance) (e : Fin I.m) :
    (I.edge e).upper.natAbs ≤ I.maxCapacity := by
  unfold Instance.maxCapacity
  have hmem : max (I.edge e).lower.natAbs (I.edge e).upper.natAbs ∈
      (I.edges.map fun e => max e.lower.natAbs e.upper.natAbs) ++ I.demand.map Int.natAbs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)
  exact le_trans (le_max_right _ _) (mem_le_foldr_max hmem)

theorem demand_natAbs_le_maxCapacity' (I : Instance) (hv : I.IsValid) (v : Fin I.n) :
    (I.d v).natAbs ≤ I.maxCapacity := by
  unfold Instance.maxCapacity
  have hv' : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
  have hdv : I.d v = I.demand[v.val]'hv' := by
    unfold Instance.d; exact List.getD_eq_getElem _ _ hv'
  have hmem : (I.d v).natAbs ∈
      (I.edges.map fun e => max e.lower.natAbs e.upper.natAbs) ++ I.demand.map Int.natAbs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨I.d v, hdv ▸ List.getElem_mem hv', rfl⟩)
  exact mem_le_foldr_max hmem

theorem cost_natAbs_le_maxCost' (I : Instance) (e : Fin I.m) :
    (I.edge e).cost.natAbs ≤ I.maxCost := by
  unfold Instance.maxCost
  exact mem_le_foldr_max (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)

theorem narrowEncode_length_ge_three (I : Instance) : 3 ≤ (narrowEncode I).length := by
  simp [narrowEncode]

/-- For any feasible integral flow `f`, the encoded answer `1 :: flatMap (intWords k) f` is no
longer than `narrowEncode I`. -/
theorem narrowAnswer_length_le_encode (I : Instance) (f : Fin I.m → ℤ)
    (hf : ∀ e, (I.edge e).lower ≤ f e ∧ f e ≤ (I.edge e).upper) :
    (1 :: (List.finRange I.m).flatMap fun j => intWords (narrowLimbWidth I) (f j)).length ≤
      (narrowEncode I).length := by
  set k := narrowLimbWidth I
  have hk : 1 ≤ k := one_le_narrowLimbWidth I
  have hb : 1 < 2 ^ k := by have := two_le_pow hk; omega
  have hflat : ∀ (n : ℕ) (g₁ g₂ : Fin n → List ℕ),
      (∀ i, (g₁ i).length ≤ (g₂ i).length) →
      ((List.finRange n).flatMap g₁).length ≤ ((List.finRange n).flatMap g₂).length := by
    intro n g₁ g₂ hle
    simp only [List.length_flatMap]
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      have h0 := hle 0
      have hrest := ih (fun i => g₁ i.succ) (fun i => g₂ i.succ) (fun i => hle i.succ)
      omega
  have hedges : (I.edges.flatMap (narrowEdgeWords k)).length =
      ((List.finRange I.m).flatMap (fun j => narrowEdgeWords k (I.edge j))).length := by
    have hmap : I.edges = (List.finRange I.m).map I.edge := by
      refine List.ext_getElem (by simp only [List.length_map, List.length_finRange]; rfl) fun i hi _ => ?_
      simp [Instance.edge]
    conv_lhs => rw [hmap, List.flatMap_map]
  have hle_edge : ∀ j : Fin I.m,
      (intWords k (f j)).length ≤ (narrowEdgeWords k (I.edge j)).length := by
    intro j
    have hbounds := hf j
    have habs : (f j).natAbs ≤ max (I.edge j).lower.natAbs (I.edge j).upper.natAbs := by omega
    have hdig : (Nat.digits (2 ^ k) (f j).natAbs).length ≤
        max (Nat.digits (2 ^ k) (I.edge j).lower.natAbs).length
          (Nat.digits (2 ^ k) (I.edge j).upper.natAbs).length := by
      rcases le_total (I.edge j).lower.natAbs (I.edge j).upper.natAbs with hlu | hul
      · rw [max_eq_right hlu] at habs
        exact le_trans (digits_length_mono hb habs) (le_max_right _ _)
      · rw [max_eq_left hul] at habs
        exact le_trans (digits_length_mono hb habs) (le_max_left _ _)
    simp only [intWords_length, narrowEdgeWords, List.length_cons, List.length_append]
    omega
  have hsum := hflat I.m (fun j => intWords k (f j)) (fun j => narrowEdgeWords k (I.edge j)) hle_edge
  simp only [narrowEncode, List.length_cons, List.length_append]
  rw [hedges]
  omega

/-! ### Explicit Stage 0/3 space budgets and word-size predicate -/

/-- Monotone upper bound on `stage1CircSpace K (narrowLimbWidth I) S` for both pruned calls
(`K.n ≤ I.n + 1`, `K.m ≤ 3 * I.m`, `maxCap K ≤ scalingCapacityBudget I U`, `maxCost K ≤ max C 1`). -/
def narrowStage1SpaceBound (I : Instance) (S : ℕ → ℕ → ℕ) : ℕ :=
  let k := narrowLimbWidth I
  let U := I.maxCapacity
  let C := I.maxCost
  let T_U := Nat.size (FlowReduction.scalingCapacityBudget I U)
  let L_c := Nat.size (max C 1)
  let K_cap := T_U / k + 2
  let L_limbs := L_c / k + 2
  let R := 28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (I.m + 1) + 1)
  let startSp := (I.n + 1) + 30 + 48 * I.m + 15 * I.m * K_cap + 3 * I.m * L_limbs
  let bsSp := 5 + 12 * I.m + 18 * I.m * K_cap +
    T_U * (2 + 72 * I.m + S (6 * I.m + 1) (12 * I.m))
  let dualSp := 50 + 180 * I.m + 150 * I.m + S (6 * I.m + 2) (36 * I.m)
  startSp + R * (bsSp + dualSp)

/-- Total heap space beyond `(narrowEncode I).length` used by `narrowMain`. -/
def narrowMainSpace (I : Instance) (S : ℕ → ℕ → ℕ) : ℕ :=
  let L_U := narrowMaxCapLimbs I
  let L_C := narrowMaxCostLimbs I
  let L_dem := L_U + 1
  4 * I.n + 65 * I.m + 13 * I.m * L_dem + 2 * I.m * L_C + 7 * L_dem + 60 +
    2 * narrowStage1SpaceBound I S

/-- Plain word-size and memory-fit hypotheses on `w` for `narrowMain`. Every conjunct follows
from `w ≥ c * log₂ z` for a fixed constant `c` whenever `S` is polynomial. -/
def NarrowMainFits (w : ℕ) (S : ℕ → ℕ → ℕ) (I : Instance) (_hv : I.IsValid) : Prop :=
  let k := narrowLimbWidth I
  2 * k + 1 ≤ w ∧
  (18 * I.m + 21) * upperClip (3 * I.m) < 2 ^ w ∧
  (narrowEncode I).length + narrowMainSpace I S < 2 ^ w

end MinCostFlow.NarrowProg
