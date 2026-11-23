module

public import MinCostFlow.Machine.WideWord.LSSTModelBase
public import MinCostFlow.Machine.WideWord.LSSTModel
public import MinCostFlow.Machine.WideWord.Limbs
public import MinCostFlow.Num.LoadSmall
public import MinCostFlow.Num.PackWord
public import MinCostFlow.Num.Less
public import MinCostFlow.Num.SignExtend
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.Multiply
public import MinCostFlow.Num.IntegerDivide
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Multiword fixed-point weight base definitions and module layout

This file provides the representation bridges, numerical scaling inequalities, relocatable
`weightsModule`, and state-stepping combinators used by the weight-computation modules
for Theorem 2.2.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM MinCostFlow

/-! ### Representation bridges and numerical inequalities -/

/-- Closed range `[a, a + la)` is disjoint from `[b, b + lb)`. -/
def DisjointRanges (a la b lb : ℕ) : Prop :=
  a + la ≤ b ∨ b + lb ≤ a

/-- Working limb width used for intermediate weight calculations. -/
def kWidthOf (nlCnt L : ℕ) : ℕ :=
  L + (Nat.log 2 (4 * nlCnt + 2) + 1) + 2

/-- Bump-pointer workspace consumed per edge by `weightStepProc`. -/
def weightStepSpace (K : ℕ) : ℕ :=
  16 * K + 2 * Num.integerDivideSpace (2 * K)

/-- Total bump-pointer workspace consumed by `weightsProc`. -/
def weightsSpace (nlCnt K : ℕ) : ℕ :=
  13 * K + nlCnt * (18 * K + 2 * Num.integerDivideSpace (2 * K))

/-- Time cost bound of `weightStepProc`. -/
def weightStepCost (K : ℕ) : ℕ :=
  2800 * K * K + 4200 * K + 1800

/-- Time cost bound of `weightsProc`. -/
def weightsCost (nlCnt L : ℕ) : ℕ :=
  (nlCnt + 1) * (weightStepCost (kWidthOf nlCnt L) + 140 * kWidthOf nlCnt L + 600) +
    nlCnt * (42 * L + 200) + 300

theorem bitWidth_two_pow_bound (n : ℕ) : 4 * n + 2 < 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : 4 ≤ 2 ^ (n + 2) :=
      le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega))
    have hpow : 2 ^ ((n + 1) + 2) = 2 ^ (n + 2) + 2 ^ (n + 2) := by rw [pow_succ]; ring
    omega

theorem activeVertsList_length_bounds {G : IndexedGraph} (hG : G.Valid)
    (hne : 1 ≤ (nonloopEdges G).length) :
    2 ≤ (activeVertsList G).length ∧ (activeVertsList G).length ≤ 2 * (nonloopEdges G).length := by
  have hnd : (activeVertsList G).Nodup := activeVertsList_nodup G
  rw [← List.toFinset_card_of_nodup hnd]
  have he0 : (nonloopEdges G)[0]'(by omega) ∈ nonloopEdges G := List.getElem_mem (by omega)
  obtain ⟨hm0, hne_ep⟩ := mem_nonloopEdges_iff.mp he0
  have hu0 : G.tail ((nonloopEdges G)[0]'(by omega)) ∈ (activeVertsList G).toFinset :=
    List.mem_toFinset.mpr (mem_activeVertsList_iff.mpr ⟨(hG.2 _ hm0).1, _, he0, Or.inl rfl⟩)
  have hv0 : G.head ((nonloopEdges G)[0]'(by omega)) ∈ (activeVertsList G).toFinset :=
    List.mem_toFinset.mpr (mem_activeVertsList_iff.mpr ⟨(hG.2 _ hm0).2, _, he0, Or.inr rfl⟩)
  have hsub2 : ({G.tail ((nonloopEdges G)[0]'(by omega)),
      G.head ((nonloopEdges G)[0]'(by omega))} : Finset ℕ) ⊆ (activeVertsList G).toFinset := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hge : 2 ≤ (activeVertsList G).toFinset.card := by
    have hc := Finset.card_le_card hsub2
    rwa [Finset.card_pair hne_ep] at hc
  have hsub_ub : (activeVertsList G).toFinset ⊆
      (nonloopEdges G).toFinset.image G.tail ∪ (nonloopEdges G).toFinset.image G.head := by
    intro u hu
    obtain ⟨_, e, he_nl, rfl | rfl⟩ := mem_activeVertsList_iff.mp (List.mem_toFinset.mp hu)
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr he_nl))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr he_nl))
  have hle : (activeVertsList G).toFinset.card ≤ 2 * (nonloopEdges G).length := by
    calc (activeVertsList G).toFinset.card
        ≤ ((nonloopEdges G).toFinset.image G.tail ∪
            (nonloopEdges G).toFinset.image G.head).card := Finset.card_le_card hsub_ub
      _ ≤ ((nonloopEdges G).toFinset.image G.tail).card +
            ((nonloopEdges G).toFinset.image G.head).card := Finset.card_union_le _ _
      _ ≤ (nonloopEdges G).toFinset.card + (nonloopEdges G).toFinset.card :=
          Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ (nonloopEdges G).length + (nonloopEdges G).length :=
          Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ = 2 * (nonloopEdges G).length := by ring
  exact ⟨hge, hle⟩

theorem numValid_congr {mem₁ mem₂ : ℕ → ℕ} {a h L : ℕ}
    (heq : ∀ i < L, mem₁ (a + i) = mem₂ (a + i)) (hv : Num.Valid mem₁ a h L) :
    Num.Valid mem₂ a h L :=
  fun i hi => by rw [← heq i hi]; exact hv i hi

theorem unsignedVal_congr_range {mem₁ mem₂ : ℕ → ℕ} {a h L : ℕ}
    (heq : ∀ i < L, mem₁ (a + i) = mem₂ (a + i)) :
    Num.unsignedVal mem₁ a h L = Num.unsignedVal mem₂ a h L := by
  induction L generalizing a with
  | zero => simp [Num.unsignedVal]
  | succ L ih =>
    simp only [Num.unsignedVal]
    have h0 : mem₁ a = mem₂ a := by simpa using heq 0 (by omega)
    rw [h0, ih (fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using heq (i + 1) (by omega))]

theorem intVal_congr_range {mem₁ mem₂ : ℕ → ℕ} {a h L : ℕ}
    (heq : ∀ i < L, mem₁ (a + i) = mem₂ (a + i)) :
    Num.intVal mem₁ a h L = Num.intVal mem₂ a h L := by
  simp only [Num.intVal, unsignedVal_congr_range heq]

theorem unsignedVal_add_split (mem : ℕ → ℕ) (a h K M : ℕ) :
    Num.unsignedVal mem a h (K + M) =
      Num.unsignedVal mem a h K + Num.capacity h K * Num.unsignedVal mem (a + K) h M := by
  induction K generalizing a with
  | zero => simp [Num.unsignedVal, Num.capacity]
  | succ K ih =>
    simp only [Nat.succ_add, Num.unsignedVal, Num.capacity, pow_succ'] at *
    rw [ih (a + 1), show a + 1 + K = a + (K + 1) by omega]
    ring

theorem numValid_add_split {mem : ℕ → ℕ} {a h K M : ℕ} (hv : Num.Valid mem a h (K + M)) :
    Num.Valid mem a h K ∧ Num.Valid mem (a + K) h M :=
  ⟨fun i hi => hv i (by omega), fun i hi => by
    simpa [Nat.add_assoc] using hv (K + i) (by omega)⟩

theorem unsignedVal_prefix_eq {mem : ℕ → ℕ} {a h K M : ℕ}
    (hv : Num.Valid mem a h (K + M))
    (hlt : Num.unsignedVal mem a h (K + M) < Num.capacity h K) :
    Num.Valid mem a h K ∧ Num.unsignedVal mem a h K = Num.unsignedVal mem a h (K + M) := by
  refine ⟨(numValid_add_split hv).1, ?_⟩
  rw [unsignedVal_add_split] at hlt ⊢
  have hz : Num.unsignedVal mem (a + K) h M = 0 := by
    by_contra hne
    have hpos : 1 ≤ Num.unsignedVal mem (a + K) h M := Nat.pos_of_ne_zero hne
    have hmul := Nat.mul_le_mul_left (Num.capacity h K) hpos
    omega
  rw [hz, mul_zero, Nat.add_zero]

theorem limbsAt_of_numValid {mem : ℕ → ℕ} {a h L : ℕ} (hv : Num.Valid mem a h L) :
    LimbsAt mem a L h (Num.unsignedVal mem a h L) := by
  refine limbsAt_iff_pointwise.mpr ⟨?_, fun i hi => ?_⟩
  · simpa [Num.capacity, Num.base, ← pow_mul, Nat.mul_comm h L] using Num.unsignedVal_lt hv
  · induction L generalizing a i with
    | zero => omega
    | succ L ih =>
      simp only [Num.unsignedVal]
      have h0 : mem a < 2 ^ h := by simpa [Num.base] using hv 0 (by omega)
      have hv_tail : Num.Valid mem (a + 1) h L := fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using hv (j + 1) (by omega)
      cases i with
      | zero =>
        simp only [Nat.zero_mul, pow_zero, Nat.div_one, Nat.add_zero]
        rw [show Num.base h = 2 ^ h from rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
      | succ i =>
        rw [show (i + 1) * h = h + i * h by ring, pow_add, ← Nat.div_div_eq_div_mul]
        rw [show Num.base h = 2 ^ h from rfl, Nat.add_mul_div_left _ _ (Nat.two_pow_pos h),
          Nat.div_eq_of_lt h0, Nat.zero_add]
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using ih hv_tail i (by omega)

theorem intVal_eq_nat_of_pos {mem : ℕ → ℕ} {a h L : ℕ}
    (hv : Num.Valid mem a h L) (hpos : 0 < Num.intVal mem a h L) :
    Num.intVal mem a h L = (Num.unsignedVal mem a h L : ℤ) ∧
      2 * Num.unsignedVal mem a h L < Num.capacity h L ∧
      1 ≤ Num.unsignedVal mem a h L := by
  have hu_lt := Num.unsignedVal_lt hv
  dsimp only [Num.intVal, Num.signedVal] at hpos ⊢
  split_ifs at * <;> omega

theorem signedVal_eq_of_lt {h L u : ℕ} (hlt : 2 * u < Num.capacity h L) :
    Num.signedVal h L u = (u : ℤ) := by
  dsimp only [Num.signedVal]
  split_ifs <;> omega

theorem fits_of_lt_half_cap {h L n : ℕ} (h2 : 2 * n < Num.capacity h L) :
    Num.Fits h L (n : ℤ) :=
  ⟨by omega, by exact_mod_cast h2⟩

theorem nat_ceil_div_eq {a b : ℕ} (hb : 1 ≤ b) :
    Nat.ceil ((a : ℝ) / (b : ℝ)) = (a + b - 1) / b := by
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb
  rcases eq_or_lt_of_le (Nat.zero_le a) with rfl | ha
  · have hdiv : (0 + b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
    simp only [Nat.cast_zero, zero_div, Nat.ceil_zero, hdiv]
  · have hpos : (a + b - 1) / b ≠ 0 := Nat.ne_of_gt (Nat.div_pos (by omega) hb)
    rw [Nat.ceil_eq_iff hpos]
    have h1 : (a + b - 1) / b * b ≤ a + b - 1 := Nat.div_mul_le_self _ b
    have hdv := Nat.div_add_mod (a + b - 1) b
    have hmod := Nat.mod_lt (a + b - 1) (by omega : 0 < b)
    have h2 : a + b - 1 < ((a + b - 1) / b + 1) * b := by nlinarith
    have hq1 : 1 ≤ (a + b - 1) / b := Nat.pos_of_ne_zero hpos
    have hsub : ((a + b - 1) / b - 1) * b < a := by
      have hm : ((a + b - 1) / b - 1) * b + b = (a + b - 1) / b * b := by
        calc ((a + b - 1) / b - 1) * b + b
            = ((a + b - 1) / b - 1 + 1) * b := by ring
          _ = (a + b - 1) / b * b := by rw [Nat.sub_add_cancel hq1]
      omega
    have hle : a ≤ (a + b - 1) / b * b := by
      have hm : ((a + b - 1) / b + 1) * b = (a + b - 1) / b * b + b := by ring
      omega
    exact ⟨(lt_div_iff₀ hb_r).mpr (by exact_mod_cast hsub),
      (div_le_iff₀ hb_r).mpr (by exact_mod_cast hle)⟩

private theorem list_map_div_sum (xs : List ℕ) (f : ℕ → ℕ) (c : ℝ) :
    (xs.map fun i => (f i : ℝ) / c).sum = ((xs.map f).sum : ℝ) / c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

theorem edgeMult_eq_nat {G : IndexedGraph} {v : ℕ → ℝ} {vNat : ℕ → ℕ} {P : ℕ}
    (hv_pos : ∀ e ∈ nonloopEdges G, 1 ≤ vNat e)
    (hv_eq : ∀ e ∈ nonloopEdges G, v e = (vNat e : ℝ) / (2 : ℝ) ^ P)
    {e : ℕ} (he : e ∈ nonloopEdges G) :
    let nl := nonloopEdges G
    let S := (nl.map vNat).sum
    1 ≤ S ∧
    LSF.edgeMult { G.toMGraph with E := nl.toFinset } v e =
      (nl.length * vNat e + S - 1) / S ∧
    1 ≤ (nl.length * vNat e + S - 1) / S ∧
    (nl.length * vNat e + S - 1) / S ≤ nl.length := by
  intro nl S
  have he_le_S : vNat e ≤ S :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem he)
  have hS_pos : 1 ≤ S := le_trans (hv_pos e he) he_le_S
  have hnl_pos : 1 ≤ nl.length := List.length_pos_of_mem he
  have h2P : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hnorm : ({ G.toMGraph with E := nl.toFinset } : MGraph).norm1 v = (S : ℝ) / (2 : ℝ) ^ P := by
    have hnd : nl.Nodup := nonloopEdges_nodup G
    have hsum_eq : ∑ f ∈ nl.toFinset, |v f| = (nl.map fun f => v f).sum := by
      rw [← List.sum_toFinset _ hnd]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hfn := List.mem_toFinset.mp hf
      rw [hv_eq f hfn, abs_of_pos (div_pos (by exact_mod_cast (hv_pos f hfn)) h2P)]
    dsimp only [MGraph.norm1]
    rw [hsum_eq, List.map_congr_left fun f hf => hv_eq f hf, list_map_div_sum]
  have hcard : ({ G.toMGraph with E := nl.toFinset } : MGraph).E.card = nl.length :=
    List.toFinset_card_of_nodup (nonloopEdges_nodup G)
  have hfrac : ((({ G.toMGraph with E := nl.toFinset } : MGraph).E.card : ℝ) * v e) /
      ({ G.toMGraph with E := nl.toFinset } : MGraph).norm1 v =
      ((nl.length * vNat e : ℕ) : ℝ) / (S : ℝ) := by
    rw [hcard, hv_eq e he, hnorm]
    push_cast
    field_simp [h2P.ne']
  refine ⟨hS_pos, ?_, ?_, ?_⟩
  · dsimp only [LSF.edgeMult]
    rw [hfrac, nat_ceil_div_eq hS_pos]
  · have h1 : 1 ≤ nl.length * vNat e := Nat.mul_pos hnl_pos (hv_pos e he)
    exact Nat.div_pos (by omega) hS_pos
  · have hlt : nl.length * vNat e + S - 1 < (nl.length + 1) * S := by
      have hmul : nl.length * vNat e ≤ nl.length * S := Nat.mul_le_mul_left _ he_le_S
      have : (nl.length + 1) * S = nl.length * S + S := by ring
      omega
    have hlt_q : (nl.length * vNat e + S - 1) / S < nl.length + 1 :=
      (Nat.div_lt_iff_lt_mul hS_pos).mpr hlt
    omega

theorem stretch_ineq_from_nat {G : IndexedGraph} {ℓ : ℕ → ℝ} {lNat : ℕ → ℕ} {P minIdx : ℕ}
    (hG : G.Valid) (hne : 1 ≤ (nonloopEdges G).length)
    (hmin_lt : minIdx < (nonloopEdges G).length)
    (hl_pos : ∀ e ∈ nonloopEdges G, 1 ≤ lNat e)
    (hl_eq : ∀ e ∈ nonloopEdges G, ℓ e = (lNat e : ℝ) / (2 : ℝ) ^ P)
    (hl_min : ∀ e ∈ nonloopEdges G, lNat ((nonloopEdges G)[minIdx]'hmin_lt) ≤ lNat e) :
    let Vcnt := (activeVertsList G).length
    let lmin := lNat ((nonloopEdges G)[minIdx]'hmin_lt)
    let δ : ℝ := (lmin : ℝ) / ((2 : ℝ) ^ P * (2 * (Vcnt : ℝ)))
    let w_orig (e : ℕ) : ℕ := (2 * Vcnt * lNat e) / lmin
    0 < δ ∧
    (∀ e ∈ nonloopEdges G, 4 ≤ w_orig e) ∧
    (∀ e ∈ nonloopEdges G, ℓ e ≤ δ * ((w_orig e : ℝ) + 1)) ∧
    (∀ e ∈ nonloopEdges G, δ * (w_orig e : ℝ) ≤ ℓ e) ∧
    (∀ e ∈ nonloopEdges G, δ * (Vcnt : ℝ) ≤ ℓ e / 2) := by
  intro Vcnt lmin δ w_orig
  have h2V_ge : 2 ≤ Vcnt := (activeVertsList_length_bounds hG hne).1
  have hlmin_pos : 1 ≤ lmin := hl_pos _ (List.getElem_mem hmin_lt)
  have h2P : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hV_r : (0 : ℝ) < Vcnt := by exact_mod_cast (by omega : 0 < Vcnt)
  have hlmin_r : (0 : ℝ) < lmin := by exact_mod_cast hlmin_pos
  have hδ_pos : 0 < δ := by positivity
  refine ⟨hδ_pos, fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_⟩
  · have hm : 4 * lmin ≤ 2 * Vcnt * lNat e := by
      calc 4 * lmin ≤ 4 * lNat e := Nat.mul_le_mul_left 4 (hl_min e he)
        _ ≤ (2 * Vcnt) * lNat e := Nat.mul_le_mul_right _ (by omega)
    exact (Nat.le_div_iff_mul_le hlmin_pos).mpr hm
  · have hlt : 2 * Vcnt * lNat e ≤ (w_orig e + 1) * lmin := by
      have hdv := Nat.div_add_mod (2 * Vcnt * lNat e) lmin
      have hmod := Nat.mod_lt (2 * Vcnt * lNat e) (by omega : 0 < lmin)
      dsimp only [w_orig]
      nlinarith
    have hlt_r : (2 * (Vcnt : ℝ) * (lNat e : ℝ)) ≤ ((w_orig e : ℝ) + 1) * (lmin : ℝ) := by
      exact_mod_cast hlt
    rw [hl_eq e he]
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ h2P (by positivity)]
    nlinarith
  · have hle := Nat.div_mul_le_self (2 * Vcnt * lNat e) lmin
    have hle_r : (w_orig e : ℝ) * (lmin : ℝ) ≤ 2 * (Vcnt : ℝ) * (lNat e : ℝ) := by
      exact_mod_cast hle
    rw [hl_eq e he]
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) h2P]
    nlinarith
  · have hmin_r : (lmin : ℝ) ≤ (lNat e : ℝ) := by exact_mod_cast hl_min e he
    rw [hl_eq e he]
    dsimp only [δ]
    calc (lmin : ℝ) / ((2 : ℝ) ^ P * (2 * (Vcnt : ℝ))) * (Vcnt : ℝ)
        = (lmin : ℝ) / ((2 : ℝ) ^ P * 2) := by field_simp
      _ ≤ (lNat e : ℝ) / ((2 : ℝ) ^ P * 2) :=
          div_le_div_of_nonneg_right hmin_r (by positivity)
      _ = (lNat e : ℝ) / (2 : ℝ) ^ P / 2 := by ring

theorem kWidth_capacity_bounds {h L nlCnt : ℕ} (hh : 0 < h) (_hL : 1 ≤ L) (hne : 1 ≤ nlCnt) :
    let Lcnt := Nat.log 2 (4 * nlCnt + 2) + 1
    let K := L + Lcnt + 2
    L ≤ K ∧ 2 ≤ Lcnt ∧
    4 * nlCnt + 2 < 2 ^ Lcnt ∧
    4 * nlCnt < 2 ^ Lcnt ∧
    nlCnt < 2 ^ (Lcnt - 2) ∧
    2 * nlCnt * Num.capacity h L < Num.capacity h K ∧
    8 * nlCnt < Num.capacity h K := by
  intro Lcnt K
  have hlog : 4 * nlCnt + 2 < 2 ^ Lcnt := Nat.lt_pow_succ_log_self (by norm_num) _
  have hLcnt2 : 2 ≤ Lcnt := by
    have h4 : 2 ^ 2 ≤ 4 * nlCnt + 2 := by omega
    have hpow := Nat.log_mono_right (b := 2) h4
    have hlog2 : Nat.log 2 (2 ^ 2) = 2 := Nat.log_pow (by norm_num) 2
    omega
  have hnl_lt : nlCnt < 2 ^ (Lcnt - 2) := by
    have hpow : 2 ^ Lcnt = 4 * 2 ^ (Lcnt - 2) := by
      have : Lcnt = 2 + (Lcnt - 2) := by omega
      rw [this, pow_add]; norm_num
    omega
  have hcap_sum : 2 * nlCnt * Num.capacity h L < Num.capacity h K := by
    have hmul : 2 * nlCnt * Num.capacity h L < 2 ^ (Lcnt - 2 + 1) * Num.capacity h L := by
      have h2n : 2 * nlCnt < 2 ^ (Lcnt - 2 + 1) := by rw [pow_succ]; omega
      exact Nat.mul_lt_mul_of_pos_right h2n (by
        rw [Num.capacity, Num.base, ← pow_mul]; exact Nat.two_pow_pos _)
    have hcapL : Num.capacity h L = 2 ^ (L * h) := by
      rw [Num.capacity, Num.base, ← pow_mul, Nat.mul_comm h L]
    have hexp2 : Lcnt - 2 + 1 + L * h < K * h := by
      have h1 : (Lcnt - 2) * 1 ≤ (Lcnt - 2) * h := Nat.mul_le_mul_left _ hh
      have h2 : K * h = L * h + (Lcnt - 2) * h + 4 * h := by
        dsimp only [K]; rw [show L + Lcnt + 2 = L + (Lcnt - 2) + 4 by omega]; ring
      nlinarith
    have hle2 : 2 ^ (Lcnt - 2 + 1) * Num.capacity h L < Num.capacity h K := by
      rw [hcapL, ← pow_add]
      simpa [Num.capacity, Num.base, ← pow_mul, Nat.mul_comm h K] using
        Nat.pow_lt_pow_right (by norm_num : 1 < 2) hexp2
    omega
  have h8 : 8 * nlCnt < Num.capacity h K := by
    have hle8 : 8 * nlCnt < 2 ^ (Lcnt + 1) := by rw [pow_succ]; omega
    have hexp8 : Lcnt + 1 ≤ K * h := by
      have h1 : Lcnt * 1 ≤ Lcnt * h := Nat.mul_le_mul_left _ hh
      have h2 : K * h = L * h + Lcnt * h + 2 * h := by dsimp only [K]; ring
      nlinarith
    have hpow8 : 2 ^ (Lcnt + 1) ≤ Num.capacity h K := by
      simpa [Num.capacity, Num.base, ← pow_mul, Nat.mul_comm h K] using
        Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hexp8
    omega
  exact ⟨by dsimp only [K]; omega, hLcnt2, hlog, by omega, hnl_lt, hcap_sum, h8⟩

/-! ### Procedures and module layout -/

def idxWeightsEntry : ℕ := 0
def idxBitWidth : ℕ := 1
def idxFindMinLen : ℕ := 2
def idxSumWeights : ℕ := 3
def idxWeightStep : ℕ := 4
def idxCopyLimbs : ℕ := 5
def idxWLoadSmall : ℕ := 6
def idxWPackWord : ℕ := 7
def idxWLess : ℕ := 8
def idxWSignExtend : ℕ := 11
def idxWAdd : ℕ := 14
def idxWSubtract : ℕ := 16
def idxWMultiply : ℕ := 21
def idxWIntegerDivide : ℕ := 26

/-- Arguments `[nlCnt]`. Computes `Nat.log 2 (4 * nlCnt + 2) + 1`. -/
def bitWidthProc : Stmt :=
  .assign 1 (.bin .add (.bin .mul (.const 4) (.reg 0)) (.const 2)) ;;
  .assign 2 (.const 0) ;;
  .assign 3 (.bin .add (.reg 0) (.const 2)) ;;
  forRange 4 (.const 0) (.reg 3)
    (.cond (.bin .lt (.const 0) (.reg 1))
      (.assign 1 (.bin .div (.reg 1) (.const 2)) ;; .assign 2 (.bin .add (.reg 2) (.const 1)))
      .nop) ;;
  .ret (.reg 2)

/-- Arguments `[nlCnt, nlPtr, lenPtr, L]`. Returns index `minIdx < nlCnt` minimizing `ℓ`. -/
def findMinLenProc (lessIdx : ℕ) : Stmt :=
  .assign 4 (.const 0) ;;
  .assign 5 (.bin .add (.reg 2) (.bin .mul (.load (.reg 1)) (.reg 3))) ;;
  forRange 6 (.const 1) (.reg 0)
    (.assign 7 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 6))) (.reg 3))) ;;
     .call 8 lessIdx [.reg 7, .reg 5, .reg 3] ;;
     .cond (.bin .eq (.reg 8) (.const 1))
       (.assign 4 (.reg 6) ;; .assign 5 (.reg 7))
       .nop) ;;
  .ret (.reg 4)

/-- Arguments `[nlCnt, nlPtr, wtPtr, L, K, heap]`. Accumulates `S = ∑_{nl} v` at `ret - K`. -/
def sumWeightsProc (loadIdx seIdx addIdx : ℕ) : Stmt :=
  .assign 6 (.reg 5) ;;
  .call 5 loadIdx [.const 0, .reg 4, .reg 5] ;;
  forRange 8 (.const 0) (.reg 0)
    (.assign 9 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 8))) (.reg 3))) ;;
     .call 7 seIdx [.reg 9, .reg 3, .reg 4, .reg 5] ;;
     .call 9 addIdx [.reg 6, .reg 5, .reg 4, .reg 7] ;;
     .assign 6 (.reg 7) ;;
     .assign 5 (.reg 9)) ;;
  .ret (.reg 5)

/-- Arguments `[src, K, dst]`. Copies `K` words in place into `dst`. -/
def copyLimbsProc : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))) ;;
  .ret (.const 0)

/-- Arguments `[e, lenPtr, wtPtr, L, K, nlCnt_K, twoV_K, S_2K, S_m1_2K, lmin_2K,
outMultAddr, outWAddr, heap]`. Writes `mult[e]` and `K`-limb `w_orig[e]`; returns new heap. -/
def weightStepProc (copyIdx packIdx seIdx addIdx mulIdx divIdx : ℕ) : Stmt :=
  .assign 13 (.bin .mul (.const 2) (.reg 4)) ;;
  .assign 14 (.bin .add (.reg 2) (.bin .mul (.reg 0) (.reg 3))) ;;
  .call 15 seIdx [.reg 14, .reg 3, .reg 4, .reg 12] ;;
  .call 16 mulIdx [.reg 5, .reg 12, .reg 4, .reg 15] ;;
  .assign 17 (.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 4))) ;;
  .call 18 addIdx [.reg 17, .reg 8, .reg 13, .reg 16] ;;
  .call 15 divIdx [.reg 16, .reg 7, .reg 13, .reg 18] ;;
  .assign 17 (.bin .sub (.reg 15) (.reg 13)) ;;
  .call 16 packIdx [.reg 17, .reg 4] ;;
  .store (.reg 10) (.reg 16) ;;
  .assign 14 (.bin .add (.reg 1) (.bin .mul (.reg 0) (.reg 3))) ;;
  .call 16 seIdx [.reg 14, .reg 3, .reg 4, .reg 15] ;;
  .call 17 mulIdx [.reg 6, .reg 15, .reg 4, .reg 16] ;;
  .assign 18 (.bin .add (.reg 16) (.bin .mul (.const 4) (.reg 4))) ;;
  .call 15 divIdx [.reg 18, .reg 9, .reg 13, .reg 17] ;;
  .assign 17 (.bin .sub (.reg 15) (.reg 13)) ;;
  .call 16 copyIdx [.reg 17, .reg 4, .reg 11] ;;
  .ret (.reg 15)

/-- Arguments `[nlCnt, nlPtr, lenPtr, wtPtr, Vcnt, L, outMultPtr, outWPtr, outKPtr, heap]`. -/
def weightsProc (b : ℕ) : Stmt :=
  .call 10 (b + idxBitWidth) [.reg 0] ;;
  .assign 11 (.bin .add (.reg 5) (.bin .add (.reg 10) (.const 2))) ;;
  .store (.reg 8) (.reg 11) ;;
  .call 12 (b + idxFindMinLen) [.reg 0, .reg 1, .reg 2, .reg 5] ;;
  .assign 13 (.bin .mul (.const 2) (.reg 11)) ;;
  .assign 19 (.reg 9) ;;
  .assign 14 (.reg 19) ;;
  .call 19 (b + idxWLoadSmall) [.bin .mul (.const 2) (.reg 4), .reg 11, .reg 19] ;;
  .assign 15 (.reg 19) ;;
  .call 19 (b + idxWLoadSmall) [.reg 0, .reg 11, .reg 19] ;;
  .assign 16 (.reg 19) ;;
  .call 19 (b + idxWLoadSmall) [.const 1, .reg 11, .reg 19] ;;
  .assign 20 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 12))) (.reg 5))) ;;
  .call 21 (b + idxWSignExtend) [.reg 20, .reg 5, .reg 11, .reg 19] ;;
  .assign 20 (.reg 19) ;;
  .assign 19 (.reg 21) ;;
  .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
  .assign 17 (.reg 19) ;;
  .assign 19 (.reg 21) ;;
  .call 19 (b + idxSumWeights) [.reg 0, .reg 1, .reg 3, .reg 5, .reg 11, .reg 19] ;;
  .assign 20 (.bin .sub (.reg 19) (.reg 11)) ;;
  .call 21 (b + idxWSubtract) [.reg 20, .reg 16, .reg 11, .reg 19] ;;
  .assign 22 (.bin .add (.reg 19) (.reg 11)) ;;
  .assign 19 (.reg 21) ;;
  .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
  .assign 18 (.reg 19) ;;
  .assign 19 (.reg 21) ;;
  .call 21 (b + idxWSignExtend) [.reg 22, .reg 11, .reg 13, .reg 19] ;;
  .assign 23 (.reg 19) ;;
  .assign 19 (.reg 21) ;;
  forRange 24 (.const 0) (.reg 0)
    (.assign 20 (.load (.bin .add (.reg 1) (.reg 24))) ;;
     .assign 21 (.bin .add (.reg 6) (.reg 24)) ;;
     .assign 22 (.bin .add (.reg 7) (.bin .mul (.reg 24) (.reg 11))) ;;
     .call 19 (b + idxWeightStep)
       [.reg 20, .reg 2, .reg 3, .reg 5, .reg 11, .reg 15, .reg 14, .reg 18, .reg 23, .reg 17,
        .reg 21, .reg 22, .reg 19]) ;;
  .ret (.reg 19)

/-- Relocatable weights module placed at procedure base `b` (51 procedures). -/
def weightsModule (b h : ℕ) : List Stmt :=
  [ weightsProc b,
    bitWidthProc,
    findMinLenProc (b + idxWLess),
    sumWeightsProc (b + idxWLoadSmall) (b + idxWSignExtend) (b + idxWAdd),
    weightStepProc (b + idxCopyLimbs) (b + idxWPackWord) (b + idxWSignExtend)
      (b + idxWAdd) (b + idxWMultiply) (b + idxWIntegerDivide),
    copyLimbsProc ] ++
    (Num.loadSmallModule (b + idxWLoadSmall) h ++
    (Num.packWordModule (b + idxWPackWord) h ++
    (Num.lessModule (b + idxWLess) h ++
    (Num.signExtendModule (b + idxWSignExtend) h ++
    (Num.addModule (b + idxWAdd) h ++
    (Num.subtractModule (b + idxWSubtract) h ++
    (Num.multiplyModule (b + idxWMultiply) h ++
     Num.integerDivideModule (b + idxWIntegerDivide) h)))))))

theorem integerDivideModule_length (b h : ℕ) : (Num.integerDivideModule b h).length = 25 := by
  simp only [Num.integerDivideModule, Num.absoluteModule, Num.unsignedDivideModule,
    Num.restoreQuotientModule, Num.effectiveLengthModule, Num.extendCopyModule,
    Num.divisionLoopModule, Num.divisionStepModule, Num.negateModule, Num.isNegativeModule,
    Num.unsignedLessModule, Num.copyModule, Num.estimateDigitModule, Num.scaleCarryModule,
    Num.isZeroModule, Num.negateCarryModule, Num.subtractModule, Num.addModule,
    List.length_append, List.length_cons, List.length_nil]

private theorem weights_tail_length (b h : ℕ) :
    (Num.loadSmallModule (b + idxWLoadSmall) h ++
    (Num.packWordModule (b + idxWPackWord) h ++
    (Num.lessModule (b + idxWLess) h ++
    (Num.signExtendModule (b + idxWSignExtend) h ++
    (Num.addModule (b + idxWAdd) h ++
    (Num.subtractModule (b + idxWSubtract) h ++
    (Num.multiplyModule (b + idxWMultiply) h ++
     Num.integerDivideModule (b + idxWIntegerDivide) h))))))).length = 45 := by
  simp only [Num.loadSmallModule, Num.packWordModule, Num.lessModule, Num.signExtendModule,
    Num.addModule, Num.subtractModule, Num.multiplyModule, Num.negateModule,
    integerDivideModule_length, Num.isNegativeModule, Num.extendCopyModule,
    List.length_append, List.length_cons, List.length_nil]

theorem weightsModule_length (b h : ℕ) : (weightsModule b h).length = 51 := by
  have ht := weights_tail_length b h
  change 6 + (Num.loadSmallModule (b + idxWLoadSmall) h ++
    (Num.packWordModule (b + idxWPackWord) h ++
    (Num.lessModule (b + idxWLess) h ++
    (Num.signExtendModule (b + idxWSignExtend) h ++
    (Num.addModule (b + idxWAdd) h ++
    (Num.subtractModule (b + idxWSubtract) h ++
    (Num.multiplyModule (b + idxWMultiply) h ++
     Num.integerDivideModule (b + idxWIntegerDivide) h))))))).length = 51
  omega

theorem weightsModule_noRand (b h : ℕ) : ∀ s ∈ weightsModule b h, s.NoRand := by
  intro s hs
  simp only [weightsModule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h1 | hmod
  · rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [weightsProc, forRange, WordRAM.forUp, Stmt.NoRand]
    · simp [bitWidthProc, forRange, WordRAM.forUp, Stmt.NoRand]
    · simp [findMinLenProc, forRange, WordRAM.forUp, Stmt.NoRand]
    · simp [sumWeightsProc, forRange, WordRAM.forUp, Stmt.NoRand]
    · simp [weightStepProc, Stmt.NoRand]
    · simp [copyLimbsProc, forRange, WordRAM.forUp, Stmt.NoRand]
  · rcases hmod with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · have : s = Num.loadSmallBody (b + idxWLoadSmall) h := by
        simpa [Num.loadSmallModule] using h1
      subst s; exact Num.loadSmallBody_noRand _ _
    · have : s = Num.packWordBody (b + idxWPackWord) h := by
        simpa [Num.packWordModule] using h1
      subst s; exact Num.packWordBody_noRand _ _
    · exact Num.lessModule_noRand _ _ _ h1
    · exact Num.signExtendModule_noRand _ _ _ h1
    · exact Num.addModule_noRand _ _ _ h1
    · exact Num.subtractModule_noRand _ _ _ h1
    · exact Num.multiplyModule_noRand _ _ _ h1
    · exact Num.integerDivideModule_noRand _ _ _ h1

theorem weights_hasAt_sub {b h : ℕ} {p : Program} (hp : p.HasAt b (weightsModule b h)) :
    p.HasAt (b + idxWLoadSmall) (Num.loadSmallModule (b + idxWLoadSmall) h) ∧
    p.HasAt (b + idxWPackWord) (Num.packWordModule (b + idxWPackWord) h) ∧
    p.HasAt (b + idxWLess) (Num.lessModule (b + idxWLess) h) ∧
    p.HasAt (b + idxWSignExtend) (Num.signExtendModule (b + idxWSignExtend) h) ∧
    p.HasAt (b + idxWAdd) (Num.addModule (b + idxWAdd) h) ∧
    p.HasAt (b + idxWSubtract) (Num.subtractModule (b + idxWSubtract) h) ∧
    p.HasAt (b + idxWMultiply) (Num.multiplyModule (b + idxWMultiply) h) ∧
    p.HasAt (b + idxWIntegerDivide) (Num.integerDivideModule (b + idxWIntegerDivide) h) := by
  have htail : p.HasAt (b + 6)
      (Num.loadSmallModule (b + idxWLoadSmall) h ++
      (Num.packWordModule (b + idxWPackWord) h ++
      (Num.lessModule (b + idxWLess) h ++
      (Num.signExtendModule (b + idxWSignExtend) h ++
      (Num.addModule (b + idxWAdd) h ++
      (Num.subtractModule (b + idxWSubtract) h ++
      (Num.multiplyModule (b + idxWMultiply) h ++
       Num.integerDivideModule (b + idxWIntegerDivide) h))))))) := by
    simpa only [weightsModule, List.length_cons, List.length_nil] using Num.hasAt_append_right hp
  have hl := Num.hasAt_append_left htail
  have t1 := Num.hasAt_append_right htail
  change p.HasAt (b + 7) _ at t1
  have hpk := Num.hasAt_append_left t1
  have t2 := Num.hasAt_append_right t1
  change p.HasAt (b + 8) _ at t2
  have hls := Num.hasAt_append_left t2
  have t3 := Num.hasAt_append_right t2
  change p.HasAt (b + 11) _ at t3
  have hse := Num.hasAt_append_left t3
  have t4 := Num.hasAt_append_right t3
  change p.HasAt (b + 14) _ at t4
  have had := Num.hasAt_append_left t4
  have t5 := Num.hasAt_append_right t4
  change p.HasAt (b + 16) _ at t5
  have hsb := Num.hasAt_append_left t5
  have t6 := Num.hasAt_append_right t5
  change p.HasAt (b + 21) _ at t6
  have hml := Num.hasAt_append_left t6
  have hdv := Num.hasAt_append_right t6
  change p.HasAt (b + 26) _ at hdv
  exact ⟨hl, hpk, hls, hse, had, hsb, hml, hdv⟩

/-! ### Abstract state-stepping combinators -/

theorem runs_seq_assign_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {r aCost : ℕ} {e : Expr}
    {s₂ : Stmt} {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (ha : e.size + 2 = aCost)
    (hnext : ∀ (st' : State), st'.mem = st.mem → st'.pos = st.pos →
      st'.regs = Function.update st.regs r v →
      ∃ o st'' c, Runs w p ω s₂ st' o st'' c ∧ Q o st'' ∧ (k + aCost) + c ≤ T) :
    ∃ o st'' c, Runs w p ω (.assign r e ;; s₂) st o st'' c ∧ Q o st'' ∧ k + c ≤ T :=
  runs_seq_assign_le he (by
    obtain ⟨o, st'', c, hr, hq, hc⟩ := hnext { st with regs := Function.update st.regs r v } rfl rfl rfl
    exact ⟨o, st'', c, hr, hq, by omega⟩)

theorem runs_seq_store_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {aCost : ℕ} {ea ev : Expr}
    {s₂ : Stmt} {st : State} {x v k T : ℕ} {Q : Outcome → State → Prop}
    (hea : ea.eval w st = some x) (hev : ev.eval w st = some v)
    (ha : ea.size + ev.size + 2 = aCost)
    (hnext : ∀ (st' : State), st'.mem = Function.update st.mem x v → st'.regs = st.regs →
      st'.pos = st.pos →
      ∃ o st'' c, Runs w p ω s₂ st' o st'' c ∧ Q o st'' ∧ (k + aCost) + c ≤ T) :
    ∃ o st'' c, Runs w p ω (.store ea ev ;; s₂) st o st'' c ∧ Q o st'' ∧ k + c ≤ T :=
  runs_seq_store_le hea hev (by
    obtain ⟨o, st'', c, hr, hq, hc⟩ :=
      hnext { st with mem := Function.update st.mem x v } rfl rfl rfl
    exact ⟨o, st'', c, hr, hq, by omega⟩)

theorem runs_seq_call_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f aCost cCost : ℕ}
    {argsE : List Expr} {C : Contract} {s₂ : Stmt} {st : State} {vs : List ℕ} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hmc : MeetsContract w p f C)
    (heval : evalArgs w st argsE = some vs)
    (hvs : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs st.mem)
    (ha : argsSize argsE + 2 = aCost)
    (hc : C.cost vs st.mem = cCost)
    (hnext : ∀ v mem' (st' : State), C.post vs st.mem v mem' →
      st'.mem = mem' → st'.regs = Function.update st.regs r v →
      ∃ o st'' c, Runs w p ω s₂ st' o st'' c ∧ Q o st'' ∧ (k + (aCost + cCost)) + c ≤ T) :
    ∃ o st'' c, Runs w p ω (.call r f argsE ;; s₂) st o st'' c ∧ Q o st'' ∧ k + c ≤ T :=
  runs_seq_call_le hmc heval hvs hpre fun v mem' pos' hpost => by
    obtain ⟨o, st'', c, hr, hq, hle⟩ :=
      hnext v mem' { mem := mem', regs := Function.update st.regs r v, pos := pos' } hpost rfl rfl
    exact ⟨o, st'', c, hr, hq, by omega⟩

end MinCostFlow.WideWord
