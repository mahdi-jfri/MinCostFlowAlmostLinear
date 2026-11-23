module

public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Expander.Components
public import MinCostFlow.Expander.ExpanderDecomp
public import MinCostFlow.Expander.TwinDecompose

import MinCostFlow.Expander.GraphHelpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algorithm 5 (`Decompose`) and Theorem 8.5

Formalizes Algorithm 5 (`Decompose`), Claim B.2 (`|E(G_i)| ≤ 2^i n`), and Theorem 8.5 of
van den Brand et al. (arXiv:2309.16629v1, page 41 and Appendix B, page 49) from
`Cited.ExpanderDecomposition`, using the loopless twin-graph reduction and expander pruning of
`TwinDecompose.lean`.

## Departures from the paper
1. As the README says ("Where the proof departs from the paper"), `Cited.ExpanderDecomposition`
   yields `φ_B1 = Ω(1 / exp(O(log^{2/3}(m + 2) log log(m + 2))))` rather than `exp(log^{1/3} m)`.
2. For multigraphs (`G` with parallel edges), `Δ_max(G)` and `m / n` can exceed `poly(n)`, so
   `ℓ = ⌈log₂ Δ_max(G)⌉ + 1` in Algorithm 5 can be `Θ(log m)` rather than `O(log n)`. We take
   `ℓ = if m ≤ n then 0 else ⌊log₂(m / n)⌋ + 1 ≤ Nat.log 2 (m + 2) + 1`, and additionally prove
   `ℓ ≤ Nat.log 2 (n + 2) + 1 ≤ 2 * Nat.log 2 (n + 2) + 2` whenever `G.IsSimple`.
3. `decomposeLevel` replaces `G_i^↻` self-loops with `twinGraph (2 ^ i) curG` and deterministic
   expander pruning.
-/

namespace MinCostFlow.Expander

@[expose] public section

/-- Recursive chain of levels `i, i - 1, …, 1, 0` of Algorithm 5, returning `[G_0, G_1, …, G_i]`
together with the accumulated deterministic pruning step count. -/
noncomputable def decomposeChain (decomp : ℕ → ℕ → Cited.Graph → List ℕ)
    (φ_level : ℕ → ℝ) (curG : Cited.Graph) : ℕ → List Cited.Graph × ℕ
  | 0 => ([curG], 0)
  | i + 1 =>
      let G_twin := twinGraph (2 ^ (i + 1)) curG
      let (Gi, remG, st) := decomposeLevel decomp (φ_level G_twin.m) curG (i + 1)
      let (rest, stRest) := decomposeChain decomp φ_level remG i
      (rest ++ [Gi], st + stRest)

/-- Full Algorithm 5 (`Decompose`): sets `ℓ := 0` if `G.m ≤ G.n`, else `Nat.log 2 (G.m / G.n) + 1`,
and runs `decomposeChain`. -/
noncomputable def decomposeModel (decomp : ℕ → ℕ → Cited.Graph → List ℕ)
    (φ_level : ℕ → ℝ) (G : Cited.Graph) : List Cited.Graph :=
  let ℓ := if G.m ≤ G.n then 0 else Nat.log 2 (G.m / G.n) + 1
  (decomposeChain decomp φ_level G ℓ).1

/-- Level count `ℓ(G)` of Algorithm 5. -/
def decomposeEll (G : Cited.Graph) : ℕ :=
  if G.m ≤ G.n then 0 else Nat.log 2 (G.m / G.n) + 1

/-- Component lists `comps k` (`1 ≤ k ≤ i`) and edge-endpoint level assignment `lvl : ℕ × ℕ → ℕ`
produced along `decomposeChain`. -/
noncomputable def decomposeChainMeta (decomp : ℕ → ℕ → Cited.Graph → List ℕ)
    (φ_level : ℕ → ℝ) (curG : Cited.Graph) : ℕ → (ℕ → List (Finset ℕ)) × (ℕ × ℕ → ℕ)
  | 0 => (fun _ => [], fun _ => 0)
  | i + 1 =>
      let G_twin := twinGraph (2 ^ (i + 1)) curG
      let (_, remG, _) := decomposeLevel decomp (φ_level G_twin.m) curG (i + 1)
      let compsI := decomposeLevelComps decomp (φ_level G_twin.m) curG (i + 1)
      let predI := decomposeLevelPred decomp (φ_level G_twin.m) curG (i + 1)
      let (compsRest, lvlRest) := decomposeChainMeta decomp φ_level remG i
      (fun k => if k = i + 1 then compsI else compsRest k,
       fun e => if predI e then i + 1 else lvlRest e)

/-- Explicit operation count of `decomposeChain`: sums building `twinGraph`, invoking
`decompCost 1 200 G_twin`, exact pruning steps `st`, splitting `curG` edges, and recursive calls,
with base cost `curG.m` at level `0`. -/
noncomputable def decomposeChainCost (decomp : ℕ → ℕ → Cited.Graph → List ℕ)
    (decompCost : ℕ → ℕ → Cited.Graph → ℕ) (φ_level : ℕ → ℝ) (curG : Cited.Graph) : ℕ → ℕ
  | 0 => curG.m
  | i + 1 =>
      let G_twin := twinGraph (2 ^ (i + 1)) curG
      let (_, remG, st) := decomposeLevel decomp (φ_level G_twin.m) curG (i + 1)
      (G_twin.n + G_twin.m) + decompCost 1 200 G_twin + st + (curG.n + curG.m) +
        decomposeChainCost decomp decompCost φ_level remG i

/-- Explicit operation count of `decomposeModel`. -/
noncomputable def decomposeModelCost (decomp : ℕ → ℕ → Cited.Graph → List ℕ)
    (decompCost : ℕ → ℕ → Cited.Graph → ℕ) (φ_level : ℕ → ℝ) (G : Cited.Graph) : ℕ :=
  decomposeChainCost decomp decompCost φ_level G (decomposeEll G)

/-- Subpolynomial `exp(C * log(m+2)^{2/3} * log(log(m+2)+2))` factor of Theorem B.1 / 8.5. -/
noncomputable def subpolyB1 (C : ℝ) (m : ℕ) : ℝ :=
  Real.exp (C * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2))

lemma subpolyB1_mono_m {C : ℝ} (hC : 0 ≤ C) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    subpolyB1 C m₁ ≤ subpolyB1 C m₂ := by
  unfold subpolyB1
  rw [Real.exp_le_exp]
  have hL1 : 0 < Real.log ((m₁ : ℝ) + 2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) m₁])
  have hlog_le : Real.log ((m₁ : ℝ) + 2) ≤ Real.log ((m₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : m₁ + 2 ≤ m₂ + 2))
  have hrp : Real.log ((m₁ : ℝ) + 2) ^ (2 / 3 : ℝ) ≤ Real.log ((m₂ : ℝ) + 2) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hL1.le hlog_le (by norm_num)
  have hll1 : 0 ≤ Real.log (Real.log ((m₁ : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
  have hll : Real.log (Real.log ((m₁ : ℝ) + 2) + 2) ≤ Real.log (Real.log ((m₂ : ℝ) + 2) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL2 : 0 ≤ Real.log ((m₂ : ℝ) + 2) :=
    (Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) m₂])).le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hrp hC) hll hll1
    (mul_nonneg hC (Real.rpow_nonneg hL2 (2 / 3 : ℝ)))

end

section

private noncomputable def sb (C : ℝ) (m : ℕ) : ℝ :=
  Real.exp (C * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2))

private lemma sb_pos (C : ℝ) (m : ℕ) : 0 < sb C m := Real.exp_pos _

private lemma log_add_two_pos (m : ℕ) : 0 < Real.log ((m : ℝ) + 2) := by
  apply Real.log_pos
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private lemma log_log_add_two_pos (m : ℕ) : 0 < Real.log (Real.log ((m : ℝ) + 2) + 2) := by
  apply Real.log_pos
  have h := log_add_two_pos m
  linarith

private lemma one_le_sb {C : ℝ} (hC : 0 ≤ C) (m : ℕ) : 1 ≤ sb C m := by
  rw [sb, Real.one_le_exp_iff]
  have h1 : 0 ≤ Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (log_add_two_pos m).le _
  have h2 : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := (log_log_add_two_pos m).le
  exact mul_nonneg (mul_nonneg hC h1) h2

private lemma sb_mono_C {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) (m : ℕ) : sb C₁ m ≤ sb C₂ m := by
  rw [sb, sb, Real.exp_le_exp]
  have h1 : 0 ≤ Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (log_add_two_pos m).le _
  have h2 : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := (log_log_add_two_pos m).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC h1) h2

private lemma sb_mul_sb (C₁ C₂ : ℝ) (m : ℕ) : sb C₁ m * sb C₂ m = sb (C₁ + C₂) m := by
  rw [sb, sb, sb, ← Real.exp_add]
  congr 1
  ring

private lemma sb_sq (C : ℝ) (m : ℕ) : sb C m ^ 2 = sb (2 * C) m := by
  rw [sq, sb_mul_sb, two_mul]

private lemma log_add_two_le_three_mul_sb_one (m : ℕ) :
    Real.log ((m : ℝ) + 2) + 2 ≤ 3 * sb 1 m := by
  set L := Real.log ((m : ℝ) + 2)
  have hL_pos : 0 < L := log_add_two_pos m
  by_cases hL1 : 1 ≤ L
  · have hrp : 1 ≤ L ^ (2 / 3 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hll : 0 ≤ Real.log (L + 2) := (log_log_add_two_pos m).le
    have hexp_le : Real.log (L + 2) ≤ 1 * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by
      have : Real.log (L + 2) ≤ L ^ (2 / 3 : ℝ) * Real.log (L + 2) :=
        le_mul_of_one_le_left hll hrp
      linarith
    have h1 : L + 2 ≤ sb 1 m := by
      calc L + 2 = Real.exp (Real.log (L + 2)) := (Real.exp_log (by linarith)).symm
        _ ≤ sb 1 m := Real.exp_le_exp.mpr hexp_le
    linarith [sb_pos 1 m]
  · have h1 : 1 ≤ sb 1 m := one_le_sb zero_le_one m
    linarith

private lemma sb_four_mul {C : ℝ} (hC : 0 ≤ C) {m' m : ℕ} (hm : m' ≤ 4 * m) :
    sb C m' ≤ sb (9 * C) m := by
  rw [sb, sb, Real.exp_le_exp]
  set L' := Real.log ((m' : ℝ) + 2)
  set L := Real.log ((m : ℝ) + 2)
  have hL_pos : 0 < L := log_add_two_pos m
  have hL'_pos : 0 < L' := log_add_two_pos m'
  have hm'_le : (m' : ℝ) + 2 ≤ ((m : ℝ) + 2) ^ 3 := by
    have h4 : (m' : ℝ) + 2 ≤ 4 * (m : ℝ) + 2 := by
      exact_mod_cast (show m' + 2 ≤ 4 * m + 2 by omega)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm2 : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
    have hm3 : 0 ≤ (m : ℝ) ^ 3 := pow_nonneg hm0 3
    have hexp : ((m : ℝ) + 2) ^ 3 = (m : ℝ) ^ 3 + 6 * (m : ℝ) ^ 2 + 12 * (m : ℝ) + 8 := by ring
    linarith
  have hL'_le : L' ≤ 3 * L := by
    calc L' ≤ Real.log (((m : ℝ) + 2) ^ (3 : ℕ)) :=
          Real.log_le_log (by positivity) hm'_le
      _ = (3 : ℝ) * L := by rw [Real.log_pow]; norm_num; rfl
  have hrp_le : L' ^ (2 / 3 : ℝ) ≤ 3 * L ^ (2 / 3 : ℝ) := by
    calc L' ^ (2 / 3 : ℝ) ≤ (3 * L) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow hL'_pos.le hL'_le (by norm_num)
      _ = (3 : ℝ) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) :=
          Real.mul_rpow (by norm_num) hL_pos.le
      _ ≤ (3 : ℝ) ^ (1 : ℝ) * L ^ (2 / 3 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL_pos.le _)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 * L ^ (2 / 3 : ℝ) := by norm_num
  have hlog3 : Real.log 3 ≤ 2 * Real.log (L + 2) := by
    have h3 : (3 : ℝ) ≤ (L + 2) ^ (2 : ℕ) := by nlinarith
    calc Real.log 3 ≤ Real.log ((L + 2) ^ (2 : ℕ)) := Real.log_le_log (by norm_num) h3
      _ = 2 * Real.log (L + 2) := by rw [Real.log_pow]; norm_num
  have hll_le : Real.log (L' + 2) ≤ 3 * Real.log (L + 2) := by
    calc Real.log (L' + 2) ≤ Real.log (3 * (L + 2)) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 3 + Real.log (L + 2) :=
          Real.log_mul (by norm_num) (by linarith)
      _ ≤ 3 * Real.log (L + 2) := by linarith
  have h1 : 0 ≤ L' ^ (2 / 3 : ℝ) := Real.rpow_nonneg hL'_pos.le _
  have h2 : 0 ≤ Real.log (L' + 2) := (log_log_add_two_pos m').le
  have h3 : 0 ≤ L ^ (2 / 3 : ℝ) := Real.rpow_nonneg hL_pos.le _
  have h4 : 0 ≤ Real.log (L + 2) := (log_log_add_two_pos m).le
  calc C * L' ^ (2 / 3 : ℝ) * Real.log (L' + 2)
      ≤ (C * (3 * L ^ (2 / 3 : ℝ))) * (3 * Real.log (L + 2)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hrp_le hC) hll_le h2
        exact mul_nonneg hC (by positivity)
    _ = 9 * C * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by ring

private lemma natLog2_eight_mul_add_one_le {c m : ℕ} (hc : c ≤ 4 * m) :
    (Nat.log 2 (2 * c + 1) + 1 : ℝ) ≤ 12 * sb 1 m := by
  set k := Nat.log 2 (2 * c + 1)
  have hpow : 2 ^ k ≤ 2 * c + 1 := Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2 : ℝ) ^ k ≤ 8 * ((m : ℝ) + 2) := by
    exact_mod_cast (show 2 ^ k ≤ 8 * (m + 2) by omega)
  have hlog_pow : (k : ℝ) * Real.log 2 ≤ Real.log ((2 : ℝ) ^ 3) + Real.log ((m : ℝ) + 2) := by
    calc (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) := by rw [Real.log_pow]
      _ ≤ Real.log (8 * ((m : ℝ) + 2)) := Real.log_le_log (by positivity) hpowR
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log ((m : ℝ) + 2) := by
          rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num]
          exact Real.log_mul (by norm_num) (by positivity)
  have hlog8 : Real.log ((2 : ℝ) ^ 3) = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hl2 : (0.5 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hk_le : (k : ℝ) ≤ 6 + 2 * Real.log ((m : ℝ) + 2) := by
    have hmul : (k : ℝ) * (0.5 : ℝ) ≤ (k : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg k)
    have h1 : (k : ℝ) * (0.5 : ℝ) ≤ 3 * Real.log 2 + Real.log ((m : ℝ) + 2) := by
      linarith [hlog_pow, hlog8]
    have hl2_le_one : Real.log 2 ≤ 1 := by
      have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
    nlinarith
  have hLpos : 0 < Real.log ((m : ℝ) + 2) := log_add_two_pos m
  have hsb := log_add_two_le_three_mul_sb_one m
  nlinarith

private lemma natLog2_add_one_le_self {k : ℕ} (hk : 1 ≤ k) : Nat.log 2 k + 1 ≤ k := by
  have hlt : Nat.log 2 k < k := by
    rw [Nat.log_lt_iff_lt_pow (by norm_num) (by omega)]
    exact Nat.lt_two_pow_self
  omega

private lemma isSimple_m_le_n_sq {G : Cited.Graph} (hV : G.IsValid) (hS : G.IsSimple) :
    G.m ≤ G.n * G.n := by
  let canon : ℕ × ℕ → ℕ × ℕ := fun e => (min e.1 e.2, max e.1 e.2)
  have hnodup : (G.edges.map canon).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    refine List.Pairwise.imp (fun {e f} hne hceq => ?_) hS.2
    apply hne
    have hmin : min e.1 e.2 = min f.1 f.2 := congrArg Prod.fst hceq
    have hmax : max e.1 e.2 = max f.1 f.2 := congrArg Prod.snd hceq
    rcases le_total e.1 e.2 with he | he <;> rcases le_total f.1 f.2 with hf | hf
    · simp only [min_eq_left he, min_eq_left hf] at hmin
      simp only [max_eq_right he, max_eq_right hf] at hmax
      rw [hmin, hmax]
    · simp only [min_eq_left he, min_eq_right hf] at hmin
      simp only [max_eq_right he, max_eq_left hf] at hmax
      rw [hmin, hmax, Sym2.eq_swap]
    · simp only [min_eq_right he, min_eq_left hf] at hmin
      simp only [max_eq_left he, max_eq_right hf] at hmax
      rw [hmin, hmax, Sym2.eq_swap]
    · simp only [min_eq_right he, min_eq_right hf] at hmin
      simp only [max_eq_left he, max_eq_left hf] at hmax
      rw [hmin, hmax]
  have hsub : (G.edges.map canon).toFinset ⊆ Finset.range G.n ×ˢ Finset.range G.n := by
    intro p hp
    rw [List.mem_toFinset, List.mem_map] at hp
    rcases hp with ⟨e, he, rfl⟩
    have hv := hV e he
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    dsimp only [canon]
    exact ⟨by omega, by omega⟩
  have hcard : (G.edges.map canon).length ≤ (Finset.range G.n ×ˢ Finset.range G.n).card := by
    rw [← List.toFinset_card_of_nodup hnodup]
    exact Finset.card_le_card hsub
  simp only [List.length_map, Finset.card_product, Finset.card_range] at hcard
  exact hcard

private lemma geom_sum_two_step (i : ℕ) :
    (2 ^ (i + 1) - 2) + 2 ^ (i + 1) = 2 ^ (i + 2) - 2 := by
  have h1 : 2 ≤ 2 ^ (i + 1) := by
    have : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by norm_num)
    rw [pow_succ']
    omega
  rw [pow_succ' 2 (i + 1)]
  omega

/-- Specification of `decomposeChain` for `i` levels (`i, …, 1, 0`) starting from `curG` with
`curG.m ≤ 2 ^ i * curG.n`: preserves `n`, `IsValid`, and `IsLoopless`; edge-partitions `curG`;
satisfies Claim B.2 (`|E(G_j)| ≤ 2^j n` for all `j ≤ i`); guarantees that every nontrivial
connected component of `G_j` (`1 ≤ j ≤ i`) is a `φ_min`-expander with min degree `≥ φ_min * 2^j`;
matches `decomposeChainMeta` (`comps`, `lvl`); and bounds `decomposeChainCost`. -/
private theorem decomposeChain_spec
    {decomp : ℕ → ℕ → Cited.Graph → List ℕ} {decompCost : ℕ → ℕ → Cited.Graph → ℕ}
    {K cr C₀_dec K_cost φ_min C_step : ℝ}
    (hK : 0 < K) (hcr : 0 < cr) (hC0 : 0 < C₀_dec) (hKc : 0 < K_cost)
    (hdecAll : ∀ (G' : Cited.Graph), G'.IsValid → G'.IsLoopless →
      let label := decomp 1 200 G'
      Cited.IsExpanderDecomposition G' (1 / 200 : ℝ) (phiB1 K cr 1 200 G'.m) label ∧
        ((G'.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
          (1 / 200 : ℝ) * (G'.m : ℝ) ∧
        (decompCost 1 200 G' : ℝ) ≤
          K_cost * (G'.n + (200 : ℝ) ^ 2 * (G'.m + 2) * sb C₀_dec G'.m))
    {m_max : ℕ}
    (_hφ_min_pos : 0 < φ_min)
    (hstep_mono : ∀ {cG : Cited.Graph} {m_t : ℕ}, cG.m ≤ m_max → m_t ≤ m_max →
      let φ_b := phiB1 K cr 1 200 m_t
      let C_max := max 7 (Nat.ceil (4 / φ_b) + 2)
      let H_max := 4 * C_max * (Nat.log 2 (2 * cG.m + 1) + 1) + 2
      ((4 * H_max + 14) * (4 * H_max + 4) : ℝ) ≤ C_step) :
    ∀ (i : ℕ) (curG : Cited.Graph),
      curG.IsValid → curG.IsLoopless →
      curG.m ≤ 2 ^ i * curG.n → curG.m ≤ m_max →
      2 * 2 ^ i * curG.n ≤ m_max →
      (∀ m' ≤ m_max, φ_min ≤ phiB1 K cr 1 200 m' / 3) →
      let (gs, pruneSteps) := decomposeChain decomp (phiB1 K cr 1 200) curG i
      let (compsFn, lvlFn) := decomposeChainMeta decomp (phiB1 K cr 1 200) curG i
      let totalCost := decomposeChainCost decomp decompCost (phiB1 K cr 1 200) curG i
      gs.length = i + 1 ∧
      (∀ Gi ∈ gs, Gi.n = curG.n ∧ Gi.IsValid ∧ Gi.IsLoopless) ∧
      (gs.map Cited.Graph.edges).flatten.Perm curG.edges ∧
      (∀ j : ℕ, (hj : j < gs.length) → (gs[j]).m ≤ 2 ^ j * curG.n) ∧
      (∀ j : ℕ, (hj : j < gs.length) → 1 ≤ j →
        ∀ X ∈ Cited.partsOf (gs[j]) (compLabels (gs[j])), 2 ≤ X.card →
          (gs[j]).IsConductanceExpanderOn X φ_min ∧
          ∀ x ∈ X, φ_min * (2 : ℝ) ^ j ≤ ((gs[j]).deg x : ℝ)) ∧
      (pruneSteps : ℝ) ≤ C_step * ((2 * (2 ^ (i + 1) - 2) * curG.n + i * curG.n : ℕ) : ℝ) ∧
      (∀ e, lvlFn e ≤ i) ∧
      (∀ j : ℕ, (hj : j < gs.length) →
        (gs[j]).edges = curG.edges.filter fun e => decide (lvlFn e = j)) ∧
      (∀ j : ℕ, (hj : j < gs.length) → 1 ≤ j →
        (compsFn j).Pairwise Disjoint ∧
        (∀ R ∈ compsFn j, R ⊆ curG.verts ∧ 2 ≤ R.card ∧
          (gs[j]).IsConductanceExpanderOn R φ_min ∧
          (∀ x ∈ R, φ_min * (2 : ℝ) ^ j ≤ ((gs[j]).degIn R x : ℝ)) ∧
          (∀ e ∈ (gs[j]).edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
        (∀ e ∈ (gs[j]).edges, ∃ R ∈ compsFn j, e.1 ∈ R ∧ e.2 ∈ R)) ∧
      (totalCost : ℝ) ≤
        ((3 * (2 ^ (i + 1) - 2) * curG.n + 3 * i * curG.n + curG.n : ℕ) : ℝ) +
        (pruneSteps : ℝ) +
        K_cost * (((2 * i * curG.n : ℕ) : ℝ) +
          (40000 : ℝ) * ((2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i : ℕ) : ℝ) * sb C₀_dec m_max) := by
  intro i
  induction i with
  | zero =>
    intro curG hV hL hm _ _ _
    dsimp only [decomposeChain, decomposeChainMeta, decomposeChainCost]
    refine ⟨rfl, ?_, by simp, ?_, ?_, ?_, fun _ => le_rfl, ?_, ?_, ?_⟩
    · intro Gi hGi
      simp only [List.mem_singleton] at hGi
      subst hGi
      exact ⟨rfl, hV, hL⟩
    · intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      simpa using hm
    · intro j hj hj1
      simp only [List.length_singleton] at hj
      omega
    · simp
    · intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      simp
    · intro j hj hj1
      simp only [List.length_singleton] at hj
      omega
    · have h0 : 2 * (2 ^ (0 + 1) - 2) * curG.n + 2 * 0 = 0 := by norm_num
      have h1 : 3 * (2 ^ (0 + 1) - 2) * curG.n + 3 * 0 * curG.n + curG.n = curG.n := by norm_num
      rw [h0, h1]
      have hm_le : (curG.m : ℝ) ≤ (curG.n : ℝ) := by exact_mod_cast (by simpa using hm : curG.m ≤ curG.n)
      have hnonneg : 0 ≤ K_cost * (((2 * 0 * curG.n : ℕ) : ℝ) + (40000 : ℝ) * ((0 : ℕ) : ℝ) * sb C₀_dec m_max) := by
        simp
      linarith
  | succ i ih =>
    intro curG hV hL hm hm_max htwin_max hφ_min
    dsimp only [decomposeChain, decomposeChainMeta, decomposeChainCost]
    set G_twin := twinGraph (2 ^ (i + 1)) curG
    set φ_b := phiB1 K cr 1 200 G_twin.m
    have hTV : G_twin.IsValid := twinGraph_isValid hV
    have hTL : G_twin.IsLoopless := twinGraph_isLoopless hL
    have hdecFull := hdecAll G_twin hTV hTL
    have hφ_pos : 0 < φ_b := phiB1_pos hK hcr (by omega) (by omega) G_twin.m
    have hφ_le : φ_b ≤ 1 := phiB1_le_one K cr 1 200 G_twin.m
    have hGtwin_le : G_twin.m ≤ m_max := by
      have hm_tw : G_twin.m ≤ 2 * 2 ^ (i + 1) * curG.n := by
        change (twinGraph (2 ^ (i + 1)) curG).m ≤ 2 * 2 ^ (i + 1) * curG.n
        rw [twinGraph_m, Nat.mul_assoc]
        omega
      exact le_trans hm_tw htwin_max
    have hdecPair :
        Cited.IsExpanderDecomposition G_twin (1 / 200 : ℝ) φ_b (decomp 1 200 G_twin) ∧
          ((G_twin.edges.filter fun e =>
            decide ((decomp 1 200 G_twin).getD e.1 0 ≠ (decomp 1 200 G_twin).getD e.2 0)).length : ℝ) ≤
              (1 / 200 : ℝ) * (G_twin.m : ℝ) :=
      ⟨hdecFull.1, hdecFull.2.1⟩
    have hdl := decomposeLevel_spec (i := i + 1) hV hL (by omega) hφ_pos hφ_le hm hdecPair
    set lvl := decomposeLevel decomp φ_b curG (i + 1)
    set Gi := lvl.1
    set remG := lvl.2.1
    set st := lvl.2.2
    rw [show lvl = (Gi, remG, st) from rfl] at hdl
    dsimp only at hdl
    simp only [Nat.add_sub_cancel] at hdl
    rcases hdl with ⟨hnGi, hnrem, hGiV, hGiL, hremV, hremL, hpermLvl, hGi_m, hrem_m, hcompsGi, hst,
      hGi_edges, hrem_edges, hvalidRs_disj, hvalidRs_spec, hGi_memR⟩
    have hrem_max : remG.m ≤ m_max := by
      have hsub_le : remG.m ≤ curG.m := by
        have := hpermLvl.length_eq
        simp only [List.length_append] at this
        change remG.edges.length ≤ curG.edges.length
        omega
      exact le_trans hsub_le hm_max
    have htwin_prev : 2 * 2 ^ i * remG.n ≤ m_max := by
      rw [hnrem]
      have hpow_le : 2 ^ i ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 * 2 ^ i * curG.n ≤ 2 * 2 ^ (i + 1) * curG.n := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hpow_le)
      exact le_trans this htwin_max
    have hih := ih remG hremV hremL hrem_m hrem_max htwin_prev hφ_min
    set chainRest := decomposeChain decomp (phiB1 K cr 1 200) remG i
    set rest := chainRest.1
    set stRest := chainRest.2
    set metaRest := decomposeChainMeta decomp (phiB1 K cr 1 200) remG i
    set compsRest := metaRest.1
    set lvlRest := metaRest.2
    set costRest := decomposeChainCost decomp decompCost (phiB1 K cr 1 200) remG i
    rw [show chainRest = (rest, stRest) from rfl,
        show metaRest = (compsRest, lvlRest) from rfl] at hih
    dsimp only at hih
    rcases hih with ⟨hlen_rest, hvalid_rest, hperm_rest, hm_rest, hcomps_rest, hst_rest,
      hlvl_le, hrest_edges, hcomps_meta_rest, hcost_rest⟩
    set predI := decomposeLevelPred decomp φ_b curG (i + 1)
    set compsI := decomposeLevelComps decomp φ_b curG (i + 1)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton, hlen_rest]
    · intro Gx hGx
      simp only [List.mem_append, List.mem_singleton] at hGx
      rcases hGx with hGx | rfl
      · rcases hvalid_rest Gx hGx with ⟨hnx, hVx, hLx⟩
        exact ⟨hnx.trans hnrem, hVx, hLx⟩
      · exact ⟨hnGi, hGiV, hGiL⟩
    · simp only [List.map_append, List.map_singleton, List.flatten_append, List.flatten_singleton]
      have hp1 : ((rest.map Cited.Graph.edges).flatten ++ Gi.edges).Perm (remG.edges ++ Gi.edges) :=
        List.Perm.append_right Gi.edges hperm_rest
      have hp2 : (remG.edges ++ Gi.edges).Perm (Gi.edges ++ remG.edges) := List.perm_append_comm
      exact hp1.trans (hp2.trans hpermLvl)
    · intro j hj
      simp only [List.length_append, List.length_singleton, hlen_rest] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · have hlt' : j < rest.length := by omega
        rw [List.getElem_append_left hlt']
        have := hm_rest j hlt'
        rwa [hnrem] at this
      · have hge : rest.length ≤ i + 1 := by omega
        rw [List.getElem_append_right hge]
        have hzero : i + 1 - rest.length = 0 := by omega
        simp [hzero, hGi_m]
    · intro j hj hj1 X hX hXcard
      simp only [List.length_append, List.length_singleton, hlen_rest] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · have hlt' : j < rest.length := by omega
        rw [List.getElem_append_left hlt'] at hX ⊢
        exact hcomps_rest j hlt' hj1 X hX hXcard
      · have hge : rest.length ≤ i + 1 := by omega
        rw [List.getElem_append_right hge] at hX ⊢
        have hzero : i + 1 - rest.length = 0 := by omega
        simp only [hzero, List.getElem_cons_zero] at hX ⊢
        have hcomp := hcompsGi X hX hXcard
        have hφ_le_div : φ_min ≤ φ_b / 3 := hφ_min G_twin.m hGtwin_le
        refine ⟨isConductanceExpanderOn_mono hφ_le_div hcomp.1, fun x hx => ?_⟩
        exact le_trans (mul_le_mul_of_nonneg_right hφ_le_div (by positivity)) (hcomp.2 x hx)
    · have hstR : (st : ℝ) ≤ C_step * ((2 * curG.m + curG.n : ℕ) : ℝ) := by
        have hm_mono := hstep_mono hm_max hGtwin_le
        dsimp only at hm_mono
        have h1 : (st : ℝ) ≤
            ((4 * ((4 * max 7 (Nat.ceil (4 / φ_b) + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2 : ℕ) : ℝ) + 14) *
             (4 * ((4 * max 7 (Nat.ceil (4 / φ_b) + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2 : ℕ) : ℝ) + 4)) *
              ((2 * curG.m + curG.n : ℕ) : ℝ) := by
          exact_mod_cast hst
        exact le_trans h1 (mul_le_mul_of_nonneg_right hm_mono (Nat.cast_nonneg _))
      have hcur_le : (2 * curG.m + curG.n : ℕ) ≤ 2 * 2 ^ (i + 1) * curG.n + curG.n := by
        rw [Nat.mul_assoc]; omega
      have hcur_R : ((2 * curG.m + curG.n : ℕ) : ℝ) ≤
          ((2 * 2 ^ (i + 1) * curG.n + curG.n : ℕ) : ℝ) := by exact_mod_cast hcur_le
      have hC_nn : 0 ≤ C_step := by
        by_contra hlt
        push Not at hlt
        nlinarith [hstep_mono hm_max hGtwin_le, show (0 : ℝ) ≤ ((4 * _ + 14) * (4 * _ + 4) : ℝ) from by positivity]
      have hcomb_eq : (2 * (2 ^ (i + 1) - 2) * curG.n + i * curG.n) +
          (2 * 2 ^ (i + 1) * curG.n + curG.n) =
          2 * (2 ^ (i + 2) - 2) * curG.n + (i + 1) * curG.n := by
        have hstep := geom_sum_two_step i
        calc (2 * (2 ^ (i + 1) - 2) * curG.n + i * curG.n) + (2 * 2 ^ (i + 1) * curG.n + curG.n)
            = 2 * ((2 ^ (i + 1) - 2) + 2 ^ (i + 1)) * curG.n + (i + 1) * curG.n := by ring
          _ = 2 * (2 ^ (i + 2) - 2) * curG.n + (i + 1) * curG.n := by rw [hstep]
      have hst_R : (st : ℝ) ≤ C_step * ((2 * 2 ^ (i + 1) * curG.n + curG.n : ℕ) : ℝ) :=
        le_trans hstR (mul_le_mul_of_nonneg_left hcur_R hC_nn)
      rw [Nat.cast_add, show i + 1 + 1 = i + 2 from rfl]
      have hcomb_R : ((2 * (2 ^ (i + 1) - 2) * curG.n + i * curG.n : ℕ) : ℝ) +
          ((2 * 2 ^ (i + 1) * curG.n + curG.n : ℕ) : ℝ) =
          ((2 * (2 ^ (i + 2) - 2) * curG.n + (i + 1) * curG.n : ℕ) : ℝ) := by
        exact_mod_cast hcomb_eq
      rw [← hcomb_R, mul_add]
      rw [hnrem] at hst_rest
      linarith
    · intro e
      split_ifs
      · exact le_rfl
      · exact Nat.le_succ_of_le (hlvl_le e)
    · intro j hj
      simp only [List.length_append, List.length_singleton, hlen_rest] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · have hlt' : j < rest.length := by omega
        rw [List.getElem_append_left hlt', hrest_edges j hlt', hrem_edges, List.filter_filter]
        congr 1
        ext e
        have hjne : j ≠ i + 1 := by omega
        by_cases hp : predI e
        · simp [hp, hjne.symm]
        · simp [hp]
      · have hge : rest.length ≤ i + 1 := by omega
        rw [List.getElem_append_right hge]
        have hzero : i + 1 - rest.length = 0 := by omega
        simp only [hzero, List.getElem_cons_zero, hGi_edges]
        congr 1
        ext e
        have hle := hlvl_le e
        by_cases hp : predI e
        · simp [hp]
        · simp [hp, show lvlRest e ≠ i + 1 by omega]
    · intro j hj hj1
      simp only [List.length_append, List.length_singleton, hlen_rest] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · have hlt' : j < rest.length := by omega
        rw [List.getElem_append_left hlt']
        have hjne : j ≠ i + 1 := by omega
        simp only [hjne, ↓reduceIte]
        have hcm := hcomps_meta_rest j hlt' hj1
        refine ⟨hcm.1, fun R hR => ?_, hcm.2.2⟩
        rcases hcm.2.1 R hR with ⟨hRv, hRc, hRexp, hRdeg, hRcl⟩
        have hverts_eq : remG.verts = curG.verts := by simp [Cited.Graph.verts, hnrem]
        exact ⟨hverts_eq ▸ hRv, hRc, hRexp, hRdeg, hRcl⟩
      · have hge : rest.length ≤ i + 1 := by omega
        rw [List.getElem_append_right hge]
        have hzero : i + 1 - rest.length = 0 := by omega
        simp only [hzero, List.getElem_cons_zero, ↓reduceIte]
        have hφ_le_div : φ_min ≤ φ_b / 3 := hφ_min G_twin.m hGtwin_le
        refine ⟨hvalidRs_disj, fun R hR => ?_, hGi_memR⟩
        rcases hvalidRs_spec R hR with ⟨hRv, hRc, hRexp, hRdeg, hRcl⟩
        refine ⟨hRv, hRc, isConductanceExpanderOn_mono hφ_le_div hRexp, fun x hx => ?_, hRcl⟩
        exact le_trans (mul_le_mul_of_nonneg_right hφ_le_div (by positivity)) (hRdeg x hx)
    · have hcost_i := hdecFull.2.2
      have hGtwin_mR : (G_twin.m : ℝ) ≤ ((2 * 2 ^ (i + 1) * curG.n : ℕ) : ℝ) := by
        exact_mod_cast (show G_twin.m ≤ 2 * 2 ^ (i + 1) * curG.n by
          change (twinGraph (2 ^ (i + 1)) curG).m ≤ 2 * 2 ^ (i + 1) * curG.n
          rw [twinGraph_m, Nat.mul_assoc]; omega)
      have hsb_le : sb C₀_dec G_twin.m ≤ sb C₀_dec m_max := by
        rw [sb, sb, Real.exp_le_exp]
        have hL1 := log_add_two_pos G_twin.m
        have hll1 := (log_log_add_two_pos G_twin.m).le
        have hlogm : Real.log ((G_twin.m : ℝ) + 2) ≤ Real.log ((m_max : ℝ) + 2) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast (by omega : G_twin.m + 2 ≤ m_max + 2)
        have hrp : Real.log ((G_twin.m : ℝ) + 2) ^ (2 / 3 : ℝ) ≤
            Real.log ((m_max : ℝ) + 2) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow hL1.le hlogm (by norm_num)
        have hll : Real.log (Real.log ((G_twin.m : ℝ) + 2) + 2) ≤
            Real.log (Real.log ((m_max : ℝ) + 2) + 2) :=
          Real.log_le_log (by linarith) (by linarith)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hrp hC0.le) hll hll1
          (mul_nonneg hC0.le (Real.rpow_nonneg (log_add_two_pos m_max).le (2 / 3 : ℝ)))
      have hGtwin_n : G_twin.n = 2 * curG.n := rfl
      have hcost_i' : (decompCost 1 200 G_twin : ℝ) ≤
          K_cost * (((2 * curG.n : ℕ) : ℝ) +
            (40000 : ℝ) * ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ) * sb C₀_dec m_max) := by
        refine le_trans hcost_i ?_
        apply mul_le_mul_of_nonneg_left _ hKc.le
        rw [hGtwin_n]
        have hm_plus : (G_twin.m : ℝ) + 2 ≤ ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ) := by
          rw [Nat.cast_add, Nat.cast_ofNat]
          linarith
        have hsb_nn : 0 ≤ sb C₀_dec G_twin.m := (sb_pos _ _).le
        have hprod : (200 : ℝ) ^ 2 * ((G_twin.m : ℝ) + 2) * sb C₀_dec G_twin.m ≤
            (40000 : ℝ) * ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ) * sb C₀_dec m_max := by
          calc (200 : ℝ) ^ 2 * ((G_twin.m : ℝ) + 2) * sb C₀_dec G_twin.m
              ≤ (40000 : ℝ) * ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ) * sb C₀_dec G_twin.m := by
                apply mul_le_mul_of_nonneg_right _ hsb_nn
                linarith
            _ ≤ (40000 : ℝ) * ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ) * sb C₀_dec m_max := by
                apply mul_le_mul_of_nonneg_left hsb_le
                positivity
        linarith
      have hover_i : (G_twin.n + G_twin.m + (curG.n + curG.m) : ℕ) ≤
          3 * 2 ^ (i + 1) * curG.n + 3 * curG.n := by
        have hm_tw : G_twin.m ≤ 2 * 2 ^ (i + 1) * curG.n := by
          change (twinGraph (2 ^ (i + 1)) curG).m ≤ 2 * 2 ^ (i + 1) * curG.n
          rw [twinGraph_m, Nat.mul_assoc]
          omega
        have hthree : 3 * 2 ^ (i + 1) * curG.n = 2 * 2 ^ (i + 1) * curG.n + 2 ^ (i + 1) * curG.n := by
          ring
        rw [hGtwin_n, hthree]
        omega
      have hover_comb : (3 * (2 ^ (i + 1) - 2) * curG.n + 3 * i * curG.n + curG.n) +
          (3 * 2 ^ (i + 1) * curG.n + 3 * curG.n) =
          3 * (2 ^ (i + 2) - 2) * curG.n + 3 * (i + 1) * curG.n + curG.n := by
        have hstep := geom_sum_two_step i
        calc (3 * (2 ^ (i + 1) - 2) * curG.n + 3 * i * curG.n + curG.n) +
              (3 * 2 ^ (i + 1) * curG.n + 3 * curG.n)
            = 3 * ((2 ^ (i + 1) - 2) + 2 ^ (i + 1)) * curG.n + 3 * (i + 1) * curG.n + curG.n := by ring
          _ = 3 * (2 ^ (i + 2) - 2) * curG.n + 3 * (i + 1) * curG.n + curG.n := by rw [hstep]
      have hcomb1 : 2 * i * curG.n + 2 * curG.n = 2 * (i + 1) * curG.n := by ring
      have hcomb2 : (2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i) + (2 * 2 ^ (i + 1) * curG.n + 2) =
          2 * (2 ^ (i + 2) - 2) * curG.n + 2 * (i + 1) := by
        have hstep := geom_sum_two_step i
        calc (2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i) + (2 * 2 ^ (i + 1) * curG.n + 2)
            = 2 * ((2 ^ (i + 1) - 2) + 2 ^ (i + 1)) * curG.n + 2 * (i + 1) := by ring
          _ = 2 * (2 ^ (i + 2) - 2) * curG.n + 2 * (i + 1) := by rw [hstep]
      have hcomb1R : ((2 * i * curG.n : ℕ) : ℝ) + ((2 * curG.n : ℕ) : ℝ) =
          ((2 * (i + 1) * curG.n : ℕ) : ℝ) := by exact_mod_cast hcomb1
      have hcomb2R : ((2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i : ℕ) : ℝ) +
          ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ) =
          ((2 * (2 ^ (i + 2) - 2) * curG.n + 2 * (i + 1) : ℕ) : ℝ) := by exact_mod_cast hcomb2
      rw [hnrem] at hcost_rest
      have hover_iR : ((G_twin.n + G_twin.m + (curG.n + curG.m) : ℕ) : ℝ) ≤
          ((3 * 2 ^ (i + 1) * curG.n + 3 * curG.n : ℕ) : ℝ) := by exact_mod_cast hover_i
      have hover_combR : ((3 * (2 ^ (i + 1) - 2) * curG.n + 3 * i * curG.n + curG.n : ℕ) : ℝ) +
          ((3 * 2 ^ (i + 1) * curG.n + 3 * curG.n : ℕ) : ℝ) =
          ((3 * (2 ^ (i + 2) - 2) * curG.n + 3 * (i + 1) * curG.n + curG.n : ℕ) : ℝ) := by
        exact_mod_cast hover_comb
      have hsum_cast : ((G_twin.n + G_twin.m + decompCost 1 200 G_twin + st +
          (curG.n + curG.m) + costRest : ℕ) : ℝ) =
          ((G_twin.n + G_twin.m + (curG.n + curG.m) : ℕ) : ℝ) +
            (st : ℝ) + (decompCost 1 200 G_twin : ℝ) + (costRest : ℝ) := by
        push_cast; ring
      rw [hsum_cast, show i + 1 + 1 = i + 2 from rfl]
      have hK_part : (decompCost 1 200 G_twin : ℝ) + (costRest : ℝ) ≤
          ((3 * (2 ^ (i + 1) - 2) * curG.n + 3 * i * curG.n + curG.n : ℕ) : ℝ) +
            (stRest : ℝ) +
            K_cost * (((2 * (i + 1) * curG.n : ℕ) : ℝ) +
              (40000 : ℝ) * ((2 * (2 ^ (i + 2) - 2) * curG.n + 2 * (i + 1) : ℕ) : ℝ) * sb C₀_dec m_max) := by
        have hstepK : (decompCost 1 200 G_twin : ℝ) +
            K_cost * (((2 * i * curG.n : ℕ) : ℝ) +
              (40000 : ℝ) * ((2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i : ℕ) : ℝ) * sb C₀_dec m_max) ≤
            K_cost * (((2 * (i + 1) * curG.n : ℕ) : ℝ) +
              (40000 : ℝ) * ((2 * (2 ^ (i + 2) - 2) * curG.n + 2 * (i + 1) : ℕ) : ℝ) * sb C₀_dec m_max) := by
          calc (decompCost 1 200 G_twin : ℝ) +
                K_cost * (((2 * i * curG.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i : ℕ) : ℝ) * sb C₀_dec m_max)
              ≤ K_cost * (((2 * curG.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ) * sb C₀_dec m_max) +
                K_cost * (((2 * i * curG.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i : ℕ) : ℝ) * sb C₀_dec m_max) := by
                  linarith
            _ = K_cost * ((((2 * i * curG.n : ℕ) : ℝ) + ((2 * curG.n : ℕ) : ℝ)) +
                  (40000 : ℝ) * (((2 * (2 ^ (i + 1) - 2) * curG.n + 2 * i : ℕ) : ℝ) +
                    ((2 * 2 ^ (i + 1) * curG.n + 2 : ℕ) : ℝ)) * sb C₀_dec m_max) := by ring
            _ = K_cost * (((2 * (i + 1) * curG.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * (2 ^ (i + 2) - 2) * curG.n + 2 * (i + 1) : ℕ) : ℝ) * sb C₀_dec m_max) := by
                  rw [hcomb1R, hcomb2R]
        linarith
      have hst_sum_cast : ((st + stRest : ℕ) : ℝ) = (st : ℝ) + (stRest : ℝ) :=
        Nat.cast_add st stRest
      rw [hst_sum_cast]
      linarith [hover_iR, hover_combR, hK_part]

end

public section

/-- **Theorem 8.5** (van den Brand et al., arXiv:2309.16629v1, page 41; Appendix B, page 49):
given `Cited.ExpanderDecomposition`, there is a deterministic decomposition algorithm
`alg := decomposeModel (decompModel citedOut thr) (phiB1 K_dec cr_dec 1 200)` with component/level
metadata `decomposeChainMeta` and defined operation count `decomposeModelCost`, partitioning any
valid loopless graph `G` into edge-disjoint subgraphs `G_0, G_1, …, G_ℓ` with
`ℓ ≤ Nat.log 2 (G.m + 2) + 1` (and `ℓ ≤ 2 * Nat.log 2 (G.n + 2) + 2` for simple `G`),
`|E(G_i)| ≤ 2^i * G.n` for all `0 ≤ i ≤ ℓ`, every nontrivial connected component of `G_i`
(`1 ≤ i ≤ ℓ`) a `φ(G.m)`-expander with minimum degree `≥ φ(G.m) * 2^i`, `φ` antitone in `m`,
and total cost `O(m · exp(O(log(m + 2)^{2/3} log log(m + 2))))`. -/
theorem theorem_8_5 (hDec : Cited.ExpanderDecomposition) :
    ∃ (φ : ℕ → ℝ) (C₀ C₁ C_cost : ℝ)
      (P : WordRAM.Program) (c_w thr : ℕ) (K_dec cr_dec : ℝ)
      (citedOut : ℕ → ℕ → Cited.Graph → List ℕ)
      (citedCost : ℕ → ℕ → Cited.Graph → ℕ),
      0 < C₀ ∧ 0 < C₁ ∧ 0 < C_cost ∧ 0 < K_dec ∧ 0 < cr_dec ∧
      (∀ m : ℕ, 0 < φ m ∧ φ m ≤ 1 ∧
        1 / φ m ≤ C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2))) ∧
      (∀ m₁ m₂ : ℕ, m₁ ≤ m₂ → φ m₂ ≤ φ m₁) ∧
      (∀ (a b : ℕ) (G : Cited.Graph), G.IsValid → G.IsLoopless → 1 ≤ a → a ≤ b →
        thr ≤ G.m →
        WordRAM.RunsTo (WordRAM.wordSize c_w (G.encode ++ [a, b, rOf G.m])) P
          (G.encode ++ [a, b, rOf G.m]) (fun _ => false) (citedOut a b G) (citedCost a b G)) ∧
      let decomp := decompModel citedOut thr
      let decompC := decompModelCost citedCost thr
      let φ_level := phiB1 K_dec cr_dec 1 200
      ∀ (G : Cited.Graph), G.IsValid → G.IsLoopless →
        let gs := decomposeModel decomp φ_level G
        let (compsFn, lvlFn) := decomposeChainMeta decomp φ_level G (decomposeEll G)
        let cost := decomposeModelCost decomp decompC φ_level G
        let ℓ := gs.length - 1
        1 ≤ gs.length ∧
        ℓ = decomposeEll G ∧
        ℓ ≤ Nat.log 2 (G.m + 2) + 1 ∧
        (G.IsSimple → ℓ ≤ 2 * Nat.log 2 (G.n + 2) + 2) ∧
        (∀ Gi ∈ gs, Gi.n = G.n ∧ Gi.IsValid ∧ Gi.IsLoopless) ∧
        (gs.map Cited.Graph.edges).flatten.Perm G.edges ∧
        (∀ i : ℕ, (hi : i < gs.length) → (gs[i]).m ≤ 2 ^ i * G.n) ∧
        (∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          ∀ X ∈ Cited.partsOf (gs[i]) (compLabels (gs[i])), 2 ≤ X.card →
            (gs[i]).IsConductanceExpanderOn X (φ G.m) ∧
            ∀ x ∈ X, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).deg x : ℝ)) ∧
        (∀ e, lvlFn e ≤ ℓ) ∧
        (∀ i : ℕ, (hi : i < gs.length) →
          (gs[i]).edges = G.edges.filter fun e => decide (lvlFn e = i)) ∧
        (∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          (compsFn i).Pairwise Disjoint ∧
          (∀ R ∈ compsFn i, R ⊆ G.verts ∧ 2 ≤ R.card ∧
            (gs[i]).IsConductanceExpanderOn R (φ G.m) ∧
            (∀ x ∈ R, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).degIn R x : ℝ)) ∧
            (∀ e ∈ (gs[i]).edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
          (∀ e ∈ (gs[i]).edges, ∃ R ∈ compsFn i, e.1 ∈ R ∧ e.2 ∈ R)) ∧
        (cost : ℝ) ≤
          C_cost * (G.m : ℝ) * Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
  rcases expanderDecomp_of_cited hDec with
    ⟨K, cr, C₀_dec, K_cost, P, c_w, citedOut, citedCost, hK, hcr, hC₀_dec, hKc, hcitedRuns, hdecAll⟩
  rcases subpoly_exp_bounds hK hcr with ⟨C_sub, hC_sub, hsub_phi, _⟩
  set C_base := max C₀_dec C_sub
  have hC_base : 0 < C_base := lt_of_lt_of_le hC₀_dec (le_max_left _ _)
  set C₀ := 18 * C_base + 2
  have hC₀ : 0 < C₀ := by positivity
  set M_phi : ℝ := max 1 (max ((thresholdB1 cr : ℝ) + 1) (K * 200))
  have hM_phi : 1 ≤ M_phi := le_max_left _ _
  set C₁ : ℝ := 3 * M_phi
  have hC₁ : 0 < C₁ := by linarith
  set B_const : ℝ := (1366 * M_phi) ^ 2
  set C_cost : ℝ := 16 + 9 * B_const + K_cost * (2 + 400000)
  have hC_cost : 0 < C_cost := by
    have hB : 1 ≤ B_const := by
      have : 1 ≤ 1366 * M_phi := by linarith
      nlinarith
    positivity
  let φ : ℕ → ℝ := fun m => 1 / (C₁ * sb (9 * C_base) m)
  refine ⟨φ, C₀, C₁, C_cost, P, c_w, thresholdB1 cr, K, cr, citedOut, citedCost,
    hC₀, hC₁, hC_cost, hK, hcr, ?_, ?_, ?_, ?_⟩
  · intro m
    have hsb1 : 1 ≤ sb (9 * C_base) m := one_le_sb (by positivity) m
    have hden_ge_three : 3 ≤ C₁ * sb (9 * C_base) m := by nlinarith
    have hden_pos : 0 < C₁ * sb (9 * C_base) m := by linarith
    refine ⟨div_pos one_pos hden_pos, div_le_one_of_le₀ (by linarith) hden_pos.le, ?_⟩
    rw [one_div_one_div]
    change C₁ * sb (9 * C_base) m ≤ C₁ * sb C₀ m
    exact mul_le_mul_of_nonneg_left (sb_mono_C (by dsimp [C₀]; linarith) m) hC₁.le
  · intro m₁ m₂ hm
    have hsb_pos : 0 < sb (9 * C_base) m₁ := sb_pos _ _
    have hsb_le : sb (9 * C_base) m₁ ≤ sb (9 * C_base) m₂ := by
      change subpolyB1 (9 * C_base) m₁ ≤ subpolyB1 (9 * C_base) m₂
      exact subpolyB1_mono_m (by positivity) hm
    dsimp only [φ]
    exact one_div_le_one_div_of_le (mul_pos hC₁ hsb_pos) (mul_le_mul_of_nonneg_left hsb_le hC₁.le)
  · intro a b G hGv hGl ha hab hm
    exact (hcitedRuns a b G hGv hGl ha hab hm).1
  · dsimp only
    intro G hV hL
    dsimp only [decomposeModel, decomposeModelCost]
    set ℓ := decomposeEll G
    have hℓ_def : ℓ = if G.m ≤ G.n then 0 else Nat.log 2 (G.m / G.n) + 1 := rfl
    by_cases hm_le_n : G.m ≤ G.n
    · have hℓ0 : ℓ = 0 := by simp only [ℓ, decomposeEll, hm_le_n, ↓reduceIte]
      simp only [hm_le_n, ↓reduceIte]
      rw [hℓ0]
      dsimp only [decomposeChain, decomposeChainMeta, decomposeChainCost]
      refine ⟨le_refl 1, ?_, ?_, ?_, ?_, by simp, ?_, ?_, fun _ => le_rfl, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro _; simp
      · intro Gi hGi
        simp only [List.mem_singleton] at hGi
        subst hGi
        exact ⟨rfl, hV, hL⟩
      · intro j hj
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        change G.m ≤ 2 ^ 0 * G.n
        simp only [pow_zero, one_mul]
        exact hm_le_n
      · intro j hj hj1
        simp only [List.length_singleton] at hj
        omega
      · intro j hj
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        change G.edges = G.edges.filter fun _ => decide (0 = 0)
        exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
      · intro j hj hj1
        simp only [List.length_singleton] at hj
        omega
      · have hsb_ge1 : 1 ≤ Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := one_le_sb hC₀.le G.m
        have hC_ge1 : 1 ≤ C_cost := by
          have : 0 ≤ 9 * B_const + K_cost * (2 + 400000) := by positivity
          dsimp only [C_cost]
          linarith
        calc (G.m : ℝ) = 1 * (G.m : ℝ) * 1 := by ring
          _ ≤ C_cost * (G.m : ℝ) * Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hC_ge1 (Nat.cast_nonneg _))
                hsb_ge1 (by norm_num) (by positivity)
    · have hm_gt_n : G.n < G.m := Nat.lt_of_not_le hm_le_n
      have hℓ_eq : ℓ = Nat.log 2 (G.m / G.n) + 1 := by simp only [ℓ, decomposeEll, hm_le_n, ↓reduceIte]
      have hn_pos : 1 ≤ G.n := by
        have hm_pos : 1 ≤ G.m := by omega
        rcases List.length_pos_iff_exists_mem.mp hm_pos with ⟨e, he⟩
        have := (hV e he).1
        omega
      have hq_pos : 1 ≤ G.m / G.n := (Nat.le_div_iff_mul_le hn_pos).mpr (by omega)
      have hm_le_powℓ : G.m ≤ 2 ^ ℓ * G.n := by
        have hlt : G.m / G.n < 2 ^ ℓ := by
          rw [hℓ_eq]
          exact Nat.lt_pow_succ_log_self (by norm_num) (G.m / G.n)
        have hmul_lt : G.m / G.n * G.n < 2 ^ ℓ * G.n := Nat.mul_lt_mul_of_pos_right hlt hn_pos
        have hdiv : G.m < (G.m / G.n + 1) * G.n := by
          have := Nat.div_add_mod G.m G.n
          have := Nat.mod_lt G.m hn_pos
          nlinarith
        nlinarith
      have hpowℓ_le_2m : 2 ^ ℓ * G.n ≤ 2 * G.m := by
        have h1 : 2 ^ Nat.log 2 (G.m / G.n) ≤ G.m / G.n :=
          Nat.pow_log_le_self 2 (by omega)
        have h2 : 2 ^ ℓ = 2 * 2 ^ Nat.log 2 (G.m / G.n) := by
          rw [hℓ_eq, pow_succ']
        have h3 : (G.m / G.n) * G.n ≤ G.m := Nat.div_mul_le_self G.m G.n
        calc 2 ^ ℓ * G.n = 2 * ((2 ^ Nat.log 2 (G.m / G.n)) * G.n) := by rw [h2]; ring
          _ ≤ 2 * ((G.m / G.n) * G.n) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right G.n h1)
          _ ≤ 2 * G.m := Nat.mul_le_mul_left 2 h3
      have hmmax_le : 2 * 2 ^ ℓ * G.n ≤ 4 * G.m := by rw [Nat.mul_assoc]; omega
      have hℓ_logm : ℓ ≤ Nat.log 2 (G.m + 2) + 1 := by
        rw [hℓ_eq]
        exact Nat.add_le_add_right (Nat.log_mono_right (le_trans (Nat.div_le_self G.m G.n) (by omega))) 1
      have hℓ_logn : G.IsSimple → ℓ ≤ 2 * Nat.log 2 (G.n + 2) + 2 := by
        intro hS
        have hm_sq : G.m ≤ G.n * G.n := isSimple_m_le_n_sq hV hS
        have hdiv_n : G.m / G.n ≤ G.n := Nat.div_le_of_le_mul hm_sq
        rw [hℓ_eq]
        have hlogn : Nat.log 2 (G.m / G.n) ≤ Nat.log 2 (G.n + 2) :=
          Nat.log_mono_right (le_trans hdiv_n (by omega : G.n ≤ G.n + 2))
        omega
      have hℓ_mul_n : ℓ * G.n ≤ G.m := by
        have h1 : ℓ ≤ G.m / G.n := by
          rw [hℓ_eq]
          exact natLog2_add_one_le_self hq_pos
        exact le_trans (Nat.mul_le_mul_right G.n h1) (Nat.div_mul_le_self G.m G.n)
      have hφ_min_spec : ∀ m' ≤ 4 * G.m, φ G.m ≤ phiB1 K cr 1 200 m' / 3 := by
        intro m' hm'
        have hφ_b_pos : 0 < phiB1 K cr 1 200 m' := phiB1_pos hK hcr (by omega) (by omega) m'
        have hsub := hsub_phi 1 200 m' (by omega) (by omega)
        have hmax_le : max ((thresholdB1 cr : ℝ) + 1) (K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ≤ M_phi := by
          have heq : K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = K * 200 := by norm_num
          rw [heq]
          exact le_max_right _ _
        have hsb1 : sb C_sub m' ≤ sb C_base m' := sb_mono_C (le_max_right _ _) m'
        have hsb2 : sb C_base m' ≤ sb (9 * C_base) G.m := sb_four_mul hC_base.le hm'
        have hinv : 1 / (phiB1 K cr 1 200 m' / 3) ≤ C₁ * sb (9 * C_base) G.m := by
          calc 1 / (phiB1 K cr 1 200 m' / 3) = 3 * (1 / phiB1 K cr 1 200 m') := by ring
            _ ≤ 3 * (M_phi * sb C_sub m') := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                refine le_trans hsub (mul_le_mul_of_nonneg_right hmax_le (sb_pos _ _).le)
            _ ≤ 3 * (M_phi * sb (9 * C_base) G.m) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact mul_le_mul_of_nonneg_left (le_trans hsb1 hsb2) (by linarith)
            _ = C₁ * sb (9 * C_base) G.m := by ring
        rw [show φ G.m = 1 / (C₁ * sb (9 * C_base) G.m) from rfl]
        have hdiv := one_div_le_one_div_of_le (one_div_pos.mpr (by linarith)) hinv
        rwa [one_div_one_div] at hdiv
      have hC_step_bound : ∀ {cG : Cited.Graph} {m_t : ℕ}, cG.m ≤ 4 * G.m → m_t ≤ 4 * G.m →
          let φ_b := phiB1 K cr 1 200 m_t
          let C_max := max 7 (Nat.ceil (4 / φ_b) + 2)
          let H_max := 4 * C_max * (Nat.log 2 (2 * cG.m + 1) + 1) + 2
          ((4 * H_max + 14) * (4 * H_max + 4) : ℝ) ≤
            B_const * sb (18 * C_base + 2) G.m := by
        intro cG m_t hcG hm_t
        dsimp only
        have hφ_pos : 0 < phiB1 K cr 1 200 m_t := phiB1_pos hK hcr (by omega) (by omega) m_t
        have hsub := hsub_phi 1 200 m_t (by omega) (by omega)
        have hmax_le : max ((thresholdB1 cr : ℝ) + 1) (K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ≤ M_phi := by
          have heq : K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = K * 200 := by norm_num
          rw [heq]
          exact le_max_right _ _
        have hsb_mt : sb C_sub m_t ≤ sb (9 * C_base) G.m :=
          le_trans (sb_mono_C (le_max_right _ _) m_t) (sb_four_mul hC_base.le hm_t)
        have hinv_le : 1 / phiB1 K cr 1 200 m_t ≤ M_phi * sb (9 * C_base) G.m :=
          le_trans hsub (mul_le_mul hmax_le hsb_mt (sb_pos _ _).le (by linarith))
        set S := M_phi * sb (9 * C_base) G.m
        have hS1 : 1 ≤ S := by
          have hsb1 := one_le_sb (by positivity : 0 ≤ 9 * C_base) G.m
          nlinarith
        have h4φ_le : 4 / phiB1 K cr 1 200 m_t ≤ 4 * S := by
          calc 4 / phiB1 K cr 1 200 m_t = 4 * (1 / phiB1 K cr 1 200 m_t) := by ring
            _ ≤ 4 * S := mul_le_mul_of_nonneg_left hinv_le (by norm_num)
        have hceil_lt : (Nat.ceil (4 / phiB1 K cr 1 200 m_t) : ℝ) < 4 / phiB1 K cr 1 200 m_t + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have hCmax_le : ((max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) : ℕ) : ℝ) ≤ 7 * S := by
          push_cast
          apply max_le (by linarith)
          linarith
        have hlog_le : ((Nat.log 2 (2 * cG.m + 1) + 1 : ℕ) : ℝ) ≤ 12 * sb 1 G.m := by
          push_cast
          exact natLog2_eight_mul_add_one_le hcG
        have hsb1_ge : 1 ≤ sb 1 G.m := one_le_sb zero_le_one G.m
        have hSsb_ge : 1 ≤ S * sb 1 G.m := by nlinarith
        have hHmax_le : ((4 * max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) *
            (Nat.log 2 (2 * cG.m + 1) + 1) + 2 : ℕ) : ℝ) ≤ 338 * (S * sb 1 G.m) := by
          push_cast
          have hprod : 4 * ((max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) : ℕ) : ℝ) *
              ((Nat.log 2 (2 * cG.m + 1) + 1 : ℕ) : ℝ) ≤ 4 * (7 * S) * (12 * sb 1 G.m) := by
            push_cast at hCmax_le hlog_le ⊢
            apply mul_le_mul (mul_le_mul_of_nonneg_left hCmax_le (by norm_num)) hlog_le
              (by positivity) (by positivity)
          push_cast at hprod
          linarith
        set H := ((4 * max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) *
            (Nat.log 2 (2 * cG.m + 1) + 1) + 2 : ℕ) : ℝ)
        have h4H14 : 4 * H + 14 ≤ 1366 * (S * sb 1 G.m) := by linarith
        have h4H4 : 4 * H + 4 ≤ 1366 * (S * sb 1 G.m) := by linarith
        have hH0 : 0 ≤ 4 * H + 4 := by positivity
        have hprodH : (4 * H + 14) * (4 * H + 4) ≤ (1366 * (S * sb 1 G.m)) ^ 2 := by
          calc (4 * H + 14) * (4 * H + 4) ≤ (1366 * (S * sb 1 G.m)) * (1366 * (S * sb 1 G.m)) :=
                mul_le_mul h4H14 h4H4 hH0 (by positivity)
            _ = (1366 * (S * sb 1 G.m)) ^ 2 := by ring
        have hsq_eq : (1366 * (S * sb 1 G.m)) ^ 2 = B_const * sb (18 * C_base + 2) G.m := by
          have h1 : (sb (9 * C_base) G.m * sb 1 G.m) ^ 2 = sb (18 * C_base + 2) G.m := by
            rw [sb_mul_sb, sb_sq]
            congr 1; ring
          calc (1366 * (S * sb 1 G.m)) ^ 2 = (1366 * M_phi) ^ 2 * (sb (9 * C_base) G.m * sb 1 G.m) ^ 2 := by
                dsimp only [S]; ring
            _ = B_const * sb (18 * C_base + 2) G.m := by rw [h1]
        exact le_trans hprodH (le_of_eq hsq_eq)
      have hφ_pos : 0 < φ G.m := div_pos one_pos (mul_pos hC₁ (sb_pos _ _))
      have hdec1200 : ∀ (G' : Cited.Graph), G'.IsValid → G'.IsLoopless →
          let label := decompModel citedOut (thresholdB1 cr) 1 200 G'
          Cited.IsExpanderDecomposition G' (1 / 200 : ℝ) (phiB1 K cr 1 200 G'.m) label ∧
            ((G'.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
              (1 / 200 : ℝ) * (G'.m : ℝ) ∧
            (decompModelCost citedCost (thresholdB1 cr) 1 200 G' : ℝ) ≤
              K_cost * (G'.n + (200 : ℝ) ^ 2 * (G'.m + 2) * sb C₀_dec G'.m) := by
        intro G' hG'V hG'L
        simpa [sb] using hdecAll 1 200 G' hG'V hG'L (by omega) (by omega)
      have hchain := decomposeChain_spec hK hcr hC₀_dec hKc hdec1200 (m_max := 4 * G.m)
        hφ_pos hC_step_bound ℓ G hV hL hm_le_powℓ (by omega) hmmax_le hφ_min_spec
      set chain := decomposeChain (decompModel citedOut (thresholdB1 cr)) (phiB1 K cr 1 200) G ℓ
      set gs := chain.1
      set pruneSteps := chain.2
      set metaOut := decomposeChainMeta (decompModel citedOut (thresholdB1 cr)) (phiB1 K cr 1 200) G ℓ
      set compsFn := metaOut.1
      set lvlFn := metaOut.2
      rw [show chain = (gs, pruneSteps) from rfl, show metaOut = (compsFn, lvlFn) from rfl] at hchain
      dsimp only at hchain
      rcases hchain with ⟨hlen, hvalid, hperm, hm_gs, hcomps, hprune, hlvl_le, hgs_edges,
        hcomps_meta, htotalCost⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change 1 ≤ gs.length; omega
      · change gs.length - 1 = ℓ; rw [hlen, Nat.add_sub_cancel]
      · change gs.length - 1 ≤ Nat.log 2 (G.m + 2) + 1
        rw [hlen, Nat.add_sub_cancel]; exact hℓ_logm
      · intro hS
        change gs.length - 1 ≤ 2 * Nat.log 2 (G.n + 2) + 2
        rw [hlen, Nat.add_sub_cancel]
        exact hℓ_logn hS
      · change ∀ Gi ∈ gs, Gi.n = G.n ∧ Gi.IsValid ∧ Gi.IsLoopless; exact hvalid
      · change (gs.map Cited.Graph.edges).flatten.Perm G.edges; exact hperm
      · change ∀ i : ℕ, (hi : i < gs.length) → (gs[i]).m ≤ 2 ^ i * G.n; exact hm_gs
      · change ∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          ∀ X ∈ Cited.partsOf (gs[i]) (compLabels (gs[i])), 2 ≤ X.card →
            (gs[i]).IsConductanceExpanderOn X (φ G.m) ∧
            ∀ x ∈ X, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).deg x : ℝ)
        exact hcomps
      · intro e
        change lvlFn e ≤ gs.length - 1
        rw [hlen, Nat.add_sub_cancel]
        exact hlvl_le e
      · change ∀ i : ℕ, (hi : i < gs.length) →
          (gs[i]).edges = G.edges.filter fun e => decide (lvlFn e = i)
        exact hgs_edges
      · change ∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          (compsFn i).Pairwise Disjoint ∧
          (∀ R ∈ compsFn i, R ⊆ G.verts ∧ 2 ≤ R.card ∧
            (gs[i]).IsConductanceExpanderOn R (φ G.m) ∧
            (∀ x ∈ R, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).degIn R x : ℝ)) ∧
            (∀ e ∈ (gs[i]).edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
          (∀ e ∈ (gs[i]).edges, ∃ R ∈ compsFn i, e.1 ∈ R ∧ e.2 ∈ R)
        exact hcomps_meta
      · have htw1 : (2 ^ (ℓ + 1) - 2) * G.n ≤ 4 * G.m := by
          have h1 : 2 ^ (ℓ + 1) - 2 ≤ 2 * 2 ^ ℓ := by rw [pow_succ']; omega
          calc (2 ^ (ℓ + 1) - 2) * G.n ≤ (2 * 2 ^ ℓ) * G.n := Nat.mul_le_mul_right G.n h1
            _ = 2 * (2 ^ ℓ * G.n) := by ring
            _ ≤ 2 * (2 * G.m) := Nat.mul_le_mul_left 2 hpowℓ_le_2m
            _ = 4 * G.m := by ring
        have htw_le : 2 * (2 ^ (ℓ + 1) - 2) * G.n ≤ 8 * G.m := by
          calc 2 * (2 ^ (ℓ + 1) - 2) * G.n = 2 * ((2 ^ (ℓ + 1) - 2) * G.n) := by ring
            _ ≤ 2 * (4 * G.m) := Nat.mul_le_mul_left 2 htw1
            _ = 8 * G.m := by ring
        have htw3_le : 3 * (2 ^ (ℓ + 1) - 2) * G.n ≤ 12 * G.m := by
          calc 3 * (2 ^ (ℓ + 1) - 2) * G.n = 3 * ((2 ^ (ℓ + 1) - 2) * G.n) := by ring
            _ ≤ 3 * (4 * G.m) := Nat.mul_le_mul_left 3 htw1
            _ = 12 * G.m := by ring
        have h9m : 2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n ≤ 9 * G.m := by omega
        have h16m : 3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n ≤ 16 * G.m := by
          have h3ℓ : 3 * ℓ * G.n = 3 * (ℓ * G.n) := by ring
          omega
        have h2ℓ : 2 * ℓ ≤ 2 * G.m := by
          calc 2 * ℓ = 2 * (ℓ * 1) := by ring
            _ ≤ 2 * (ℓ * G.n) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left ℓ hn_pos)
            _ ≤ 2 * G.m := Nat.mul_le_mul_left 2 hℓ_mul_n
        have h10m : 2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ ≤ 10 * G.m := by omega
        have h9mR : ((2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n : ℕ) : ℝ) ≤ 9 * (G.m : ℝ) := by
          exact_mod_cast h9m
        have h16mR : ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ) ≤ 16 * (G.m : ℝ) := by
          exact_mod_cast h16m
        have h2ℓn : 2 * ℓ * G.n ≤ 2 * G.m := by rw [Nat.mul_assoc]; omega
        have h2ℓnR : ((2 * ℓ * G.n : ℕ) : ℝ) ≤ 2 * (G.m : ℝ) := by exact_mod_cast h2ℓn
        have h10mR : ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) ≤ 10 * (G.m : ℝ) := by
          exact_mod_cast h10m
        have hsb_dec : sb C₀_dec (4 * G.m) ≤ sb C₀ G.m := by
          refine le_trans (sb_mono_C (le_max_left C₀_dec C_sub) (4 * G.m)) ?_
          refine le_trans (sb_four_mul hC_base.le (le_refl (4 * G.m))) ?_
          exact sb_mono_C (by dsimp [C₀]; linarith) G.m
        have hsb0_ge : 1 ≤ sb C₀ G.m := one_le_sb hC₀.le G.m
        have hover' : ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ) ≤
            16 * (G.m : ℝ) * sb C₀ G.m := by
          calc ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ)
              ≤ 16 * (G.m : ℝ) := h16mR
            _ = (16 * (G.m : ℝ)) * 1 := by ring
            _ ≤ (16 * (G.m : ℝ)) * sb C₀ G.m := mul_le_mul_of_nonneg_left hsb0_ge (by positivity)
            _ = 16 * (G.m : ℝ) * sb C₀ G.m := by ring
        have hB0 : 0 ≤ B_const := by positivity
        change (pruneSteps : ℝ) ≤ (B_const * sb C₀ G.m) *
          ((2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n : ℕ) : ℝ) at hprune
        have hprune' : (pruneSteps : ℝ) ≤ 9 * B_const * (G.m : ℝ) * sb C₀ G.m := by
          calc (pruneSteps : ℝ)
              ≤ (B_const * sb C₀ G.m) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n : ℕ) : ℝ) := hprune
            _ ≤ (B_const * sb C₀ G.m) * (9 * (G.m : ℝ)) :=
                mul_le_mul_of_nonneg_left h9mR (mul_nonneg hB0 (sb_pos _ _).le)
            _ = 9 * B_const * (G.m : ℝ) * sb C₀ G.m := by ring
        have hdecomp' : K_cost * (((2 * ℓ * G.n : ℕ) : ℝ) +
              (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) * sb C₀_dec (4 * G.m)) ≤
            K_cost * (2 + 400000) * (G.m : ℝ) * sb C₀ G.m := by
          have h1 : (2 : ℝ) * (G.m : ℝ) ≤ 2 * (G.m : ℝ) * sb C₀ G.m := by
            calc (2 : ℝ) * (G.m : ℝ) = (2 * (G.m : ℝ)) * 1 := by ring
              _ ≤ (2 * (G.m : ℝ)) * sb C₀ G.m := mul_le_mul_of_nonneg_left hsb0_ge (by positivity)
          have h2 : (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) * sb C₀_dec (4 * G.m) ≤
              400000 * (G.m : ℝ) * sb C₀ G.m := by
            calc (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) * sb C₀_dec (4 * G.m)
                ≤ (40000 : ℝ) * (10 * (G.m : ℝ)) * sb C₀_dec (4 * G.m) := by
                  apply mul_le_mul_of_nonneg_right _ (sb_pos _ _).le
                  linarith
              _ ≤ (40000 : ℝ) * (10 * (G.m : ℝ)) * sb C₀ G.m := by
                  apply mul_le_mul_of_nonneg_left hsb_dec (by positivity)
              _ = 400000 * (G.m : ℝ) * sb C₀ G.m := by ring
          calc K_cost * (((2 * ℓ * G.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) * sb C₀_dec (4 * G.m))
              ≤ K_cost * (2 * (G.m : ℝ) + 400000 * (G.m : ℝ) * sb C₀ G.m) := by
                apply mul_le_mul_of_nonneg_left _ hKc.le
                linarith
            _ ≤ K_cost * (2 * (G.m : ℝ) * sb C₀ G.m + 400000 * (G.m : ℝ) * sb C₀ G.m) := by
                apply mul_le_mul_of_nonneg_left (by linarith) hKc.le
            _ = K_cost * (2 + 400000) * (G.m : ℝ) * sb C₀ G.m := by ring
        calc (decomposeChainCost (decompModel citedOut (thresholdB1 cr))
                (decompModelCost citedCost (thresholdB1 cr)) (phiB1 K cr 1 200) G ℓ : ℝ)
            ≤ ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ) +
                (pruneSteps : ℝ) +
                K_cost * (((2 * ℓ * G.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) * sb C₀_dec (4 * G.m)) :=
              htotalCost
          _ ≤ 16 * (G.m : ℝ) * sb C₀ G.m + 9 * B_const * (G.m : ℝ) * sb C₀ G.m +
                K_cost * (2 + 400000) * (G.m : ℝ) * sb C₀ G.m := by linarith
          _ = C_cost * (G.m : ℝ) * sb C₀ G.m := by dsimp only [C_cost]; ring

end

end MinCostFlow.Expander
