module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortPos
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortAppend

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The potential of the data structure of Theorem 8.2

The amortized cost of a batch in Theorem 8.2 (page 39) is the time bound
`90 L n^{1/L} K₁ E_L Δ₁ Λ` per unit of encoding size (`dsBatchRate`), times the constant `C`
of `updateLoop_amortized` (`dsAmortConst`). The program does not pay this much in each batch: a
restart or a rebuild of a high level costs much more than one batch can pay for. So the data
structure keeps a bank.
* Each batch puts `⌈C · rate · Enc(U)⌉` into the bank (`dsBatchCharge`), and the initialization
  puts `1440 Φ₀`, where `Φ₀ = Σ_i |E(H_i)|` is the potential `levelPot` of the first state
  (`dsBankTotal`).
* The steps run so far take `Σ_k dsStepAmortCost k` out of it (`dsSpent`).
The potential of the data structure is what is left (`dsBank`). It never goes below zero: this is
the sum of Lemma 5.9 for the update loop (`updateLoop_amortized`), with the encoding size of all
updates split into the batches (`batchEnc_flatten`). This is `dsSpent_le_bankTotal`.

When a batch is added, the bank grows by the charge of the batch (`dsBankTotal_append`) and the
spent part grows by the costs of the new steps only, since the costs of the old steps do not
change (`dsSpent_append`, from `dsStepAmortCost_append`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The constant of the amortized cost: the constant of `updateLoop_amortized`. It depends only on
the constants of the sparsifier. -/
def dsAmortConst (impl : SparsifyImpl) : ℕ :=
  dsInitCostFactor impl + 3000 + dsStepPosFactor impl

/-- The time bound of Theorem 8.2 per unit of encoding size,
`90 L n^{1/L} K₁ E_L Δ₁ Λ`, with `n = max nMax 1`. -/
noncomputable def dsBatchRate (impl : SparsifyImpl) (mMax L nMax : ℕ) (G₀ : MGraph) : ℝ :=
  let P := (canonicalSparsifyParams impl mMax).absorbTime
  90 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) * (P.K_t + P.K_s + 1) *
    (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
    (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)

/-- What a batch `U` on the graph `G` puts into the bank: `⌈C · rate · Enc(U)⌉`. -/
noncomputable def dsBatchCharge (impl : SparsifyImpl) (mMax L nMax : ℕ) (G₀ G : MGraph)
    (U : List Update) : ℕ :=
  ⌈(dsAmortConst impl : ℝ) * dsBatchRate impl mMax L nMax G₀ * (G.batchEnc U : ℝ)⌉₊

/-- Everything put into the bank: `1440 Φ₀` and the charges of the batches `Us`, each on the graph
it is applied to. -/
noncomputable def dsBankTotal (impl : SparsifyImpl) (mMax L q nMax : ℕ) (G₀ : MGraph)
    (Us : List (List Update)) : ℕ :=
  1440 * levelPot (runState (L := L) G₀ q (canonicalSparsify impl) [] 0) +
    ∑ t ∈ Finset.range Us.length,
      dsBatchCharge impl mMax L nMax G₀ (G₀.applyBatch (Us.take t).flatten) (Us.getD t [])

/-- What the steps on the updates `us` take out of the bank. -/
noncomputable def dsSpent (impl : SparsifyImpl) (mMax L q vCap eCap : ℕ) (G₀ : MGraph)
    (us : List Update) : ℕ :=
  ∑ k ∈ Finset.range us.length, dsStepAmortCost G₀ impl mMax L q vCap eCap us k

/-- The potential of the data structure: what is left in the bank. -/
noncomputable def dsBank (impl : SparsifyImpl) (mMax L q vCap eCap nMax : ℕ) (G₀ : MGraph)
    (Us : List (List Update)) : ℕ :=
  dsBankTotal impl mMax L q nMax G₀ Us - dsSpent impl mMax L q vCap eCap G₀ Us.flatten

/-- The encoding size of all updates is the sum over the batches, each on the graph it is applied
to. -/
theorem batchEnc_flatten : ∀ (Us : List (List Update)) (G : MGraph),
    G.batchEnc Us.flatten =
      ∑ t ∈ Finset.range Us.length, (G.applyBatch (Us.take t).flatten).batchEnc (Us.getD t [])
  | [], G => by simp [MGraph.batchEnc]
  | U :: Us, G => by
    rw [List.flatten_cons, batchEnc_append, batchEnc_flatten Us (G.applyBatch U),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.flatten_cons, applyBatch_append, List.getD_cons_succ,
      List.take_zero, List.flatten_nil, List.getD_cons_zero]
    simp [MGraph.applyBatch, Nat.add_comm]

/-- The bank grows by the charge of a new batch. -/
theorem dsBankTotal_append (impl : SparsifyImpl) (mMax L q nMax : ℕ) (G₀ : MGraph)
    (Us : List (List Update)) (U : List Update) :
    dsBankTotal impl mMax L q nMax G₀ (Us ++ [U]) =
      dsBankTotal impl mMax L q nMax G₀ Us +
        dsBatchCharge impl mMax L nMax G₀ (G₀.applyBatch Us.flatten) U := by
  unfold dsBankTotal
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  have hsame : ∀ t ∈ Finset.range Us.length,
      dsBatchCharge impl mMax L nMax G₀ (G₀.applyBatch ((Us ++ [U]).take t).flatten)
          ((Us ++ [U]).getD t []) =
        dsBatchCharge impl mMax L nMax G₀ (G₀.applyBatch (Us.take t).flatten) (Us.getD t []) :=
    fun t ht => by
      have ht' : t < Us.length := Finset.mem_range.mp ht
      rw [List.take_append_of_le_length ht'.le, List.getD_append _ _ _ _ ht']
  rw [Finset.sum_congr rfl hsame, List.take_append_of_le_length le_rfl, List.take_length,
    List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
  ring

/-- The spent part grows by the costs of the new steps: the costs of the old steps do not change
when updates are appended (`dsStepAmortCost_append`). -/
theorem dsSpent_append (impl : SparsifyImpl) (mMax L q vCap eCap : ℕ) (G₀ : MGraph)
    (us U : List Update) :
    dsSpent impl mMax L q vCap eCap G₀ (us ++ U) =
      dsSpent impl mMax L q vCap eCap G₀ us +
        ∑ r ∈ Finset.range U.length,
          dsStepAmortCost G₀ impl mMax L q vCap eCap (us ++ U) (us.length + r) := by
  unfold dsSpent
  rw [List.length_append, Finset.sum_range_add]
  congr 1
  exact Finset.sum_congr rfl fun k hk =>
    dsStepAmortCost_append G₀ impl mMax L q vCap eCap us U (Finset.mem_range.mp hk)

/-- **The bank never goes below zero.** For a history of valid deletions and splits with at most
`nMax - n₀` splits, `q = phaseBase nMax L` and `1 ≤ max p_s p_t`, the steps take out at most what
was put in. This is the sum of Lemma 5.9 (`updateLoop_amortized`), with `45 q ≤ 90 n^{1/L}`
(`phaseBase_le`) and the encoding size split into the batches (`batchEnc_flatten`). -/
theorem dsSpent_le_bankTotal (impl : SparsifyImpl) {mMax L vCap eCap nMax : ℕ} {G₀ : MGraph}
    {Us : List (List Update)} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid Us.flatten) (hds : ∀ u ∈ Us.flatten, isDelOrSplit u)
    (hnMax : G₀.n + batchSplitCount Us.flatten ≤ nMax) (hp : 1 ≤ max impl.p_s impl.p_t) :
    dsSpent impl mMax L (phaseBase nMax L) vCap eCap G₀ Us.flatten ≤
      dsBankTotal impl mMax L (phaseBase nMax L) nMax G₀ Us := by
  set q := phaseBase nMax L with hq
  set us := Us.flatten with hus
  have hsum := updateLoop_amortized (vCap := vCap) (eCap := eCap) impl hVG₀ hL
    (two_le_phaseBase nMax L) hGm₀ hBV hds (T := us.length) le_rfl
    (by rw [List.take_length]; exact hnMax) (nCap_le_phaseBase_pow nMax L hL) hp
  simp only [List.take_length] at hsum
  set P := (canonicalSparsifyParams impl mMax).absorbTime with hP
  set C : ℝ := (dsInitCostFactor impl : ℝ) + 3000 + (dsStepPosFactor impl : ℝ) with hC
  set K : ℝ := (P.K_t + P.K_s + 1) * (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
    (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) with hK
  -- The factors are nonnegative.
  obtain ⟨hEL1, -⟩ := expFactor_bounds P.hγ_c P.hγ_ℓ L G₀.maxDeg
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ P.K_t + P.K_s + 1 := by linarith [P.hK_t, P.hK_s]
    have h2 : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
    have h3 : 0 ≤ 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
      linarith [Real.log_nonneg h2]
    have h4 : (0 : ℝ) ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
        P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := by linarith
    positivity
  have hC0 : 0 ≤ C := by positivity
  have hEnc0 : (0 : ℝ) ≤ (G₀.batchEnc us : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  -- `45 q ≤ 90 n^{1/L}`.
  have hqle := phaseBase_le nMax L hL
  have hrate : 45 * (L : ℝ) * (q : ℝ) * K ≤ dsBatchRate impl mMax L nMax G₀ := by
    have h1 : 45 * (L : ℝ) * (q : ℝ) ≤
        90 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hqle (show (0 : ℝ) ≤ 45 * L by positivity)
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hK0
    simp only [dsBatchRate]
    rw [hK] at h2
    linarith
  -- The real form of the bank.
  have hcharge : ∀ t ∈ Finset.range Us.length,
      (dsAmortConst impl : ℝ) * dsBatchRate impl mMax L nMax G₀ *
          ((G₀.applyBatch (Us.take t).flatten).batchEnc (Us.getD t []) : ℝ) ≤
        (dsBatchCharge impl mMax L nMax G₀ (G₀.applyBatch (Us.take t).flatten)
          (Us.getD t []) : ℝ) := fun t _ => Nat.le_ceil _
  have hCeq : (dsAmortConst impl : ℝ) = C := by simp only [dsAmortConst, hC]; push_cast; ring
  have henc := batchEnc_flatten Us G₀
  have hsplit : C * dsBatchRate impl mMax L nMax G₀ * (G₀.batchEnc us : ℝ) =
      ∑ t ∈ Finset.range Us.length, (dsAmortConst impl : ℝ) * dsBatchRate impl mMax L nMax G₀ *
        ((G₀.applyBatch (Us.take t).flatten).batchEnc (Us.getD t []) : ℝ) := by
    rw [hus, henc, hCeq]
    push_cast
    rw [Finset.mul_sum]
  have hmain : C * (45 * (L : ℝ) * (q : ℝ) * K * (G₀.batchEnc us : ℝ)) ≤
      C * dsBatchRate impl mMax L nMax G₀ * (G₀.batchEnc us : ℝ) := by
    have := mul_le_mul_of_nonneg_right hrate hEnc0
    have := mul_le_mul_of_nonneg_left this hC0
    linarith
  have hsum' : (dsSpent impl mMax L q vCap eCap G₀ us : ℝ) ≤
      (dsBankTotal impl mMax L q nMax G₀ Us : ℝ) := by
    have hS : (dsSpent impl mMax L q vCap eCap G₀ us : ℝ) =
        ∑ k ∈ Finset.range us.length, (dsStepAmortCost G₀ impl mMax L q vCap eCap us k : ℝ) := by
      simp only [dsSpent]; push_cast; rfl
    have hB : (dsBankTotal impl mMax L q nMax G₀ Us : ℝ) =
        1440 * (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us 0) : ℝ) +
          ∑ t ∈ Finset.range Us.length,
            (dsBatchCharge impl mMax L nMax G₀ (G₀.applyBatch (Us.take t).flatten)
              (Us.getD t []) : ℝ) := by
      simp only [dsBankTotal]; push_cast; rfl
    have h45 : C * (45 * (L : ℝ) * (q : ℝ) * K * (G₀.batchEnc us : ℝ)) =
        C * (45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) *
          (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) *
          (G₀.batchEnc us : ℝ)) := by rw [hK]; ring
    have hcs := Finset.sum_le_sum hcharge
    rw [hS, hB]
    linarith
  exact_mod_cast hsum'

end

end MinCostFlow.DynSpanner.Program
