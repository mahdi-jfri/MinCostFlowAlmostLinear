module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortPosFacts
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortPosCost
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortTrans
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortMono
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortSum
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortPosArith

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The amortized cost of a step with `0 < j`

A step with `0 < j` (Algorithm 6, lines 67 to 90) rebuilds level `j` from the affected edges
`E_aff` of the levels below. The cost bound of the program for it (`dsStepPosCostModel`, with the
loop overhead of `dsStepAmortCost`) has these parts:
* the search for `E_aff` among the candidates of `RevHistoryInv` (`dsStepPosAffCostModel`);
* the call of the sparsifier on `J` (its time bound `cQ` times `R + 6`, and the translation);
* the composition and the re-embedding of the walks, and the new level `j`;
* clearing the old levels `≥ j` (`1440 · oldBucketsSum`);
* the epilogue and linear terms.

We bound each part by the sizes of `stepPos_facts` and compare with the budget of Lemma 5.9,
`(L + 1) Enc(u) + |U_H| + |D| + sLen · 22 K₁ E_L Δ₁ Λ`. Every size is at most a constant times
`W = sLen · E_L Δ₁`:
* `|S_{j-1}| ≤ 2 sLen`, `j ≤ ℓ` (`le_lenBound_pred`), `|E_aff| ≤ |S_{j-1}| V`, the candidates are at
  most `|S_{j-1}| j V`, and the old walks have length at most `ℓ`;
* the sparsifier, the composed walks and the new walks cost at most a constant times
  `|E_aff| γ_ℓ² (ℓ + 1)² Λ`, and `|E(J̃)| ≤ 2 K_s |E_aff| γ_ℓ Λ`;
* `V (ℓ + 1)² γ_ℓ² ≤ E_L Δ₁` (`vcong_len_sq_le`), the slack of `E_L` that pays for the log of the
  walk lengths in the translation.
The old levels are paid by the potential: `oldSum + Φ_{k+1} ≤ Φ_k + |E(J̃)|`.

The bound is first shown for general graphs, sets and walks (`stepPos_budget_of`), with the facts
of `stepPos_facts` as hypotheses, and then for the step itself (`stepPos_budget`), for every
constant `C ≥ dsStepPosFactor impl`. With `stepZero_budget` it gives `updateLoop_amortized`, the
sum of Lemma 5.9 with no extra hypothesis.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The constant of the budget of a step with `0 < j`. It depends only on the guest's register
bound `R` and word-size constant `cw`. -/
def dsStepPosFactor (impl : SparsifyImpl) : ℕ :=
  2 * transConst impl + 8 * impl.program.regBound + 400000

/-- A sum over a set is at most its size times a bound on its terms. -/
lemma sum_le_card_mul_of_le {s : Finset ℕ} {f : ℕ → ℝ} {c : ℝ} (h : ∀ e ∈ s, f e ≤ c) :
    ∑ e ∈ s, f e ≤ (s.card : ℝ) * c := by
  have := Finset.sum_le_card_nsmul s f c h
  simpa [nsmul_eq_mul] using this

/-- `1 ≤ E_L Δ₁` and `ℓ_i ≤ E_L Δ₁` for `i ≤ L`. -/
lemma one_le_EL_mul {γ_c γ_ℓ : ℝ} (hc : 1 ≤ γ_c) (hl : 1 ≤ γ_ℓ) (L Δ i : ℕ) (hi : i ≤ L) :
    1 ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) *
      γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) * ((Δ : ℝ) + 1) ∧
    lenBound γ_ℓ i ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) *
      γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) * ((Δ : ℝ) + 1) := by
  obtain ⟨hEL1, -, -, hℓL, -, -, -, -, -, -⟩ := expFactor_bounds hc hl L Δ
  have h2 : (1 : ℝ) ≤ (Δ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) Δ]
  have h1 : lenBound γ_ℓ i ≤ lenBound γ_ℓ L := lenBound_mono hl hi
  set E := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) *
      γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
  have hE : E ≤ E * ((Δ : ℝ) + 1) := le_mul_of_one_le_right (by linarith) h2
  exact ⟨by linarith, by linarith⟩

/-- **The budget of a step with `0 < j`, for general data.** Here `G'` is the graph after the
update, `S = S_{j-1}`, `Ea = E_aff`, `Cs` the candidates with `crs` their count with repetitions,
`J` the graph on `E_aff` with its walks `embJH`, `oS` the old levels, `Φ0`, `Φ1` the potential
before and after, and `UH`, `D` the sizes of the output. The hypotheses are the facts of
`stepPos_facts`. The copies `implc = impl` and `Lc = L` are the forms in which the cost of the
program names the implementation and the number of levels. -/
theorem stepPos_budget_of (impl : SparsifyImpl) {mMax nMax L vCap eCap j sLen Δ m0 crs oS UH D : ℕ}
    {implc : SparsifyImpl} {Lc : ℕ} (himpl : implc = impl) (hLc : Lc = L)
    {G' J : MGraph} {S Ea Cs : Finset ℕ} {piLt embJH : MinCostFlow.Embedding} {Φ0 Φ1 enc C : ℝ}
    (hL : 1 ≤ L) (hj1 : 1 ≤ j) (hjL : j ≤ L) (henc : 1 ≤ enc)
    (hp : 1 ≤ max impl.p_s impl.p_t) (hC : (dsStepPosFactor impl : ℝ) ≤ C)
    (hS2 : (S.card : ℝ) ≤ 2 * (sLen : ℝ))
    (hAff : (Ea.card : ℝ) ≤ (S.card : ℝ) *
      vcongBound (canonicalSparsifyParams impl mMax).absorbTime.γ_c
        (canonicalSparsifyParams impl mMax).absorbTime.γ_ℓ Δ (j - 1))
    (hpiL : ∀ e ∈ G'.E, ((piLt e).length : ℝ) ≤
      lenBound (canonicalSparsifyParams impl mMax).absorbTime.γ_ℓ (j - 1))
    (hJn : J.n ≤ 2 * Ea.card) (hJnG : J.n ≤ G'.n) (hG'n : G'.n ≤ nMax) (hAm : Ea.card ≤ m0)
    (hEsub : Ea ⊆ G'.E) (hCsub : Cs ⊆ G'.E) (hJm : J.m = Ea.card) (hJE : J.E = Ea)
    (hcandle : Cs.card ≤ crs)
    (hcand : (crs : ℝ) ≤ (S.card : ℝ) * ((j : ℝ) *
      vcongBound (canonicalSparsifyParams impl mMax).absorbTime.γ_c
        (canonicalSparsifyParams impl mMax).absorbTime.γ_ℓ Δ (j - 1)))
    (hpot : (oS : ℝ) + Φ1 ≤ Φ0 +
      (if Ea.Nonempty then ((canonicalSparsify impl G' J embJH).Jtilde.m : ℝ) else 0))
    (hNE : Ea.Nonempty →
      let P := (canonicalSparsifyParams impl mMax).absorbTime
      let ℓ := lenBound P.γ_ℓ (j - 1)
      let out := canonicalSparsify impl G' J embJH
      let embMid := MinCostFlow.Embedding.comp embJH
        (fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e))
      (embJH.length J : ℝ) ≤ ℓ + 1 ∧
      (out.Jtilde.m : ℝ) ≤ P.K_s * (J.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s ∧
      (∀ e ∈ J.E, ((embMid e).length : ℝ) ≤ P.γ_ℓ * (ℓ + 1)) ∧
      (∀ e ∈ Ea, ((reembedWalk G' G' piLt embMid S e).length : ℝ) ≤ lenBound P.γ_ℓ j) ∧
      (∀ e ∈ J.E, (out.emb e).length ≤ ⌈impl.γ_ℓ mMax⌉₊)) :
    (((500 * (Lc + 1) + 1320 * 0 + 1100) + (20 * (Lc + 1 - j) + 20) +
        (100 * crs + 100 * (j * S.card) + 100 * S.card + 100 * j +
          100 * (∑ e ∈ Cs, (piLt e).length) + 40 * (Cs.card * j) + 160 * Cs.card +
          Ea.card * (35 * j + 60) + 800 * (∑ e ∈ Ea, (piLt e).length) + 2000 * Ea.card + 1200) +
        ((if 0 < Ea.card then
            dsStepPosNonEmptyCost implc mMax Lc vCap eCap j G' J piLt embJH S Ea.toList oS
          else dsStepPosEmptyCost Lc j oS) +
          dsStepPosEpilogueCost S.card J.m J.n 0 UH + 40) + 330 +
        35 * Lc + 520 + 90 * D + 90 * Ea.card + 240 * UH + 240 : ℕ) : ℝ) ≤
      C * (((L : ℝ) + 1) * enc + (UH : ℝ) + (D : ℝ) +
          (sLen : ℝ) * (22 * ((canonicalSparsifyParams impl mMax).absorbTime.K_t +
              (canonicalSparsifyParams impl mMax).absorbTime.K_s + 1) *
            (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) *
              (canonicalSparsifyParams impl mMax).absorbTime.γ_c ^ (L + 1) *
              (canonicalSparsifyParams impl mMax).absorbTime.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) *
            ((Δ : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + (m0 : ℝ) + 2)) ^
              (max (canonicalSparsifyParams impl mMax).absorbTime.p_s
                (canonicalSparsifyParams impl mMax).absorbTime.p_t))) +
        1440 * (Φ0 - Φ1) := by
  subst implc Lc
  set P := (canonicalSparsifyParams impl mMax).absorbTime with hPdef
  -- The factors.
  have hγ1 : 1 ≤ P.γ_ℓ := P.hγ_ℓ
  have hV0 : 0 ≤ vcongBound P.γ_c P.γ_ℓ Δ (j - 1) :=
    vcongBound_nonneg (by linarith [P.hγ_c]) (by linarith) _ _
  have hℓ1 : 1 ≤ lenBound P.γ_ℓ (j - 1) := one_le_lenBound hγ1 _
  obtain ⟨hY1, hℓY⟩ := one_le_EL_mul P.hγ_c P.hγ_ℓ L Δ (j - 1) (le_trans (Nat.sub_le j 1) hjL)
  have hQY := vcong_len_sq_le P.hγ_c P.hγ_ℓ L Δ j hj1 hjL
  have hjℓ : (j : ℝ) ≤ lenBound P.γ_ℓ (j - 1) := le_lenBound_pred hγ1 hj1
  have hbig1 : (1 : ℝ) ≤ (nMax : ℝ) + (m0 : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) m0]
  have hlog0 : 0 ≤ Real.log ((nMax : ℝ) + (m0 : ℝ) + 2) := Real.log_nonneg hbig1
  have hΛ1 : 1 ≤ (1 + Real.log ((nMax : ℝ) + (m0 : ℝ) + 2)) ^ (max P.p_s P.p_t) :=
    one_le_pow₀ (by linarith)
  have hΛ₁ : 1 + Real.log ((nMax : ℝ) + (m0 : ℝ) + 2) ≤
      (1 + Real.log ((nMax : ℝ) + (m0 : ℝ) + 2)) ^ (max P.p_s P.p_t) := by
    have h := logPow_mono (p := 1) (p' := max P.p_s P.p_t) hbig1 le_rfl hp
    rwa [pow_one] at h
  have hKs0 : 0 ≤ P.K_s := P.hK_s
  have hKt0 : 0 ≤ P.K_t := P.hK_t
  have hK₁ : 1 ≤ P.K_t + P.K_s + 1 := by linarith
  -- The constant.
  have hF : (dsStepPosFactor impl : ℝ) =
      2 * (transConst impl : ℝ) + 8 * (impl.program.regBound : ℝ) + 400000 := by
    simp only [dsStepPosFactor]; push_cast; ring
  rw [hF] at hC
  have hT0 : (0 : ℝ) ≤ (transConst impl : ℝ) := Nat.cast_nonneg _
  have hR0 : (0 : ℝ) ≤ (impl.program.regBound : ℝ) := Nat.cast_nonneg _
  -- The sizes.
  have ht : ((L + 1 - j : ℕ) : ℝ) ≤ (L : ℝ) + 1 := by
    have : L + 1 - j ≤ L + 1 := Nat.sub_le _ _
    exact_mod_cast this
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjLR : (j : ℝ) ≤ L := by exact_mod_cast hjL
  have hJnR : (J.n : ℝ) ≤ 2 * (Ea.card : ℝ) := by exact_mod_cast hJn
  have hcandleR : (Cs.card : ℝ) ≤ (crs : ℝ) := by exact_mod_cast hcandle
  have hSc : ∑ e ∈ Cs, ((piLt e).length : ℝ) ≤ (Cs.card : ℝ) * lenBound P.γ_ℓ (j - 1) :=
    sum_le_card_mul_of_le fun e he => hpiL e (hCsub he)
  have hSE : ∑ e ∈ Ea, ((piLt e).length : ℝ) ≤ (Ea.card : ℝ) * lenBound P.γ_ℓ (j - 1) :=
    sum_le_card_mul_of_le fun e he => hpiL e (hEsub he)
  have hbud : (sLen : ℝ) * (22 * (P.K_t + P.K_s + 1) *
        (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
          P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((Δ : ℝ) + 1) *
        (1 + Real.log ((nMax : ℝ) + (m0 : ℝ) + 2)) ^ (max P.p_s P.p_t)) =
      (sLen : ℝ) * (22 * (P.K_t + P.K_s + 1) *
        (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
          P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) * ((Δ : ℝ) + 1)) *
        (1 + Real.log ((nMax : ℝ) + (m0 : ℝ) + 2)) ^ (max P.p_s P.p_t)) := by ring
  rw [hbud]
  by_cases hne : 0 < Ea.card
  · -- The nonempty branch.
    have hne' : Ea.Nonempty := Finset.card_pos.mp hne
    obtain ⟨hlen, hJt, hmid, hrw, hout⟩ := hNE hne'
    rw [ite_eq_left hne'] at hpot
    rw [ite_eq_left hne, dsStepPosNonEmptyCost_toList, sparsifyDynCost_eq]
    simp only [dsStepPosEpilogueCost]
    push_cast
    have ha1 : (1 : ℝ) ≤ Ea.card := by exact_mod_cast hne
    have hJmR : (J.m : ℝ) = (Ea.card : ℝ) := by exact_mod_cast hJm
    have hJlog1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) J.n, Nat.cast_nonneg (α := ℝ) J.m]
    have hJlog0 : (0 : ℝ) ≤ Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := Real.log_nonneg hJlog1
    have hJnm : (J.n : ℝ) + (J.m : ℝ) + 2 ≤ (nMax : ℝ) + (m0 : ℝ) + 2 := by
      have h1 : (J.n : ℝ) ≤ nMax := by exact_mod_cast le_trans hJnG hG'n
      have h2 : (J.m : ℝ) ≤ m0 := by rw [hJmR]; exact_mod_cast hAm
      linarith
    have hΛJs := logPow_mono (p := P.p_s) (p' := max P.p_s P.p_t) hJlog1 hJnm (le_max_left _ _)
    have hΛJt := logPow_mono (p := impl.p_t) (p' := max P.p_s P.p_t) hJlog1 hJnm
      (le_max_right _ _)
    have hΛJs0 : (0 : ℝ) ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s := by positivity
    have hΛJt0 : (0 : ℝ) ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t := by positivity
    -- The guest's time bound.
    have hγt : 1 ≤ impl.γ_t mMax := impl.hγ_t mMax
    have hKtI0 : 0 ≤ impl.K_t * impl.γ_t mMax := mul_nonneg impl.hK_t (by linarith)
    have hKtI : impl.K_t * impl.γ_t mMax ≤ P.K_t + P.K_s + 1 := by
      have : impl.K_t * impl.γ_t mMax ≤ (2 * impl.K_t + 1) * impl.γ_t mMax :=
        mul_le_mul_of_nonneg_right (by linarith [impl.hK_t]) (by linarith)
      have h2 : P.K_t = (2 * impl.K_t + 1) * impl.γ_t mMax := rfl
      linarith
    have hγ' : impl.γ_ℓ mMax = P.γ_ℓ := rfl
    have hQ : (sparsifyGuestBound impl mMax J embJH : ℝ) ≤ impl.K_t * impl.γ_t mMax *
        (1 + (J.n : ℝ) + (Ea.card : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t + 1 := by
      have hlen0 : (0 : ℝ) ≤ (embJH.length J : ℝ) := Nat.cast_nonneg _
      have h0 : 0 ≤ impl.K_t * impl.γ_t mMax *
          (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t := by positivity
      have h := Nat.ceil_lt_add_one h0
      rw [sparsifyGuestBound_def]
      rw [hJmR, hγ'] at h ⊢
      linarith
    -- The translation.
    have hTr := sparsifyTransCost_le_budget impl mMax G' J embJH (nm := nMax + m0)
      (by rw [hJm]; exact hJn) (by rw [hJm]; exact hne)
      (by have := le_trans hJnG hG'n; omega) hlen hℓ1
    have hnm : (((nMax + m0 : ℕ) : ℝ) + 2) = (nMax : ℝ) + (m0 : ℝ) + 2 := by push_cast; ring
    rw [hnm, hJmR, hγ'] at hTr
    -- The walks.
    have hceil : ((⌈impl.γ_ℓ mMax⌉₊ : ℕ) : ℝ) ≤ 2 * P.γ_ℓ := by
      have h2 : 1 ≤ impl.γ_ℓ mMax := impl.hγ_ℓ mMax
      have h1 := Nat.ceil_lt_add_one (show 0 ≤ impl.γ_ℓ mMax by linarith)
      rw [← hγ']
      linarith
    have hSout : ∑ e ∈ Ea, (((canonicalSparsify impl G' J embJH).emb e).length : ℝ) ≤
        (Ea.card : ℝ) * (2 * P.γ_ℓ) :=
      sum_le_card_mul_of_le fun e he =>
        le_trans (by exact_mod_cast hout e (hJE ▸ he)) hceil
    have hSoutEmb : ∑ e ∈ Ea, ((shortcutWalk (canonicalSparsify impl G' J embJH).Jtilde
        (J.tail e) ((canonicalSparsify impl G' J embJH).emb e)).length : ℝ) ≤
        ∑ e ∈ Ea, (((canonicalSparsify impl G' J embJH).emb e).length : ℝ) :=
      Finset.sum_le_sum fun e _ => by exact_mod_cast shortcutWalk_length_le _ _ _
    have hSmid := sum_le_card_mul_of_le (s := Ea) fun e he => hmid e (hJE ▸ he)
    have hSrw := sum_le_card_mul_of_le (s := Ea) fun e he => hrw e he
    rw [lenBound_succ_pred P.γ_ℓ hj1] at hSrw
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hUH0 : (0 : ℝ) ≤ UH := Nat.cast_nonneg _
    have key := stepPos_arith_nonempty (Lr := (L : ℝ)) (j := (j : ℝ)) (t := ((L + 1 - j : ℕ) : ℝ))
      (UH := (UH : ℝ)) (D := (D : ℝ)) (Φ0 := Φ0) (Φ1 := Φ1) (oS := (oS : ℝ)) (cr := (crs : ℝ))
      hLr henc hj1R hjℓ ht hjLR (Nat.cast_nonneg _) (Nat.cast_nonneg _) hS2 ha1 hAff hcand
      (Nat.cast_nonneg _) hcandleR hSc hSE (Nat.cast_nonneg _) hJnR hV0 hℓ1 hγ1 hQY hℓY hY1
      hΛ1 hK₁ hKs0 (by linarith) hKtI0 hKtI hJt hΛJs0 hΛJs (Nat.cast_nonneg _) hlen hQ hΛJt0
      hΛJt hTr hΛ₁ (by linarith) hSout hSoutEmb hSmid (by linarith [hSrw]) hpot hT0 hR0 hUH0
      hD0 hC
    refine le_trans (le_of_eq ?_) key
    rw [hJmR]
    ring
  · -- The empty branch.
    have hne' : ¬ Ea.Nonempty := fun h => hne (Finset.card_pos.mpr h)
    rw [ite_eq_right hne'] at hpot
    rw [ite_eq_right hne]
    simp only [dsStepPosEmptyCost, dsStepPosEpilogueCost]
    push_cast
    have hJmR : (J.m : ℝ) = (Ea.card : ℝ) := by exact_mod_cast hJm
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hUH0 : (0 : ℝ) ≤ UH := Nat.cast_nonneg _
    obtain ⟨hVY, hVℓ, hVℓ2⟩ : vcongBound P.γ_c P.γ_ℓ Δ (j - 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) * ((Δ : ℝ) + 1) ∧
        vcongBound P.γ_c P.γ_ℓ Δ (j - 1) * lenBound P.γ_ℓ (j - 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) * ((Δ : ℝ) + 1) ∧
        vcongBound P.γ_c P.γ_ℓ Δ (j - 1) * lenBound P.γ_ℓ (j - 1) ^ 2 ≤
          3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) * ((Δ : ℝ) + 1) := by
      obtain ⟨k1, kℓ, kℓ2, -⟩ := slack_le hℓ1 hγ1
      have key : ∀ Z : ℝ, Z ≤ (lenBound P.γ_ℓ (j - 1) + 1) ^ 2 * P.γ_ℓ ^ 2 →
          vcongBound P.γ_c P.γ_ℓ Δ (j - 1) * Z ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) *
            P.γ_c ^ (L + 1) * P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) * ((Δ : ℝ) + 1) :=
        fun Z hZ => by
          have := mul_le_mul_of_nonneg_left hZ hV0
          linarith
      exact ⟨by simpa using key 1 k1, key _ kℓ, key _ kℓ2⟩
    have key := stepPos_arith_empty (Lr := (L : ℝ)) (j := (j : ℝ)) (t := ((L + 1 - j : ℕ) : ℝ))
      (UH := (UH : ℝ)) (D := (D : ℝ)) (Φ0 := Φ0) (Φ1 := Φ1) (oS := (oS : ℝ)) (cr := (crs : ℝ))
      (T := (transConst impl : ℝ))
      hLr henc hj1R hjℓ ht hjLR (Nat.cast_nonneg _) (Nat.cast_nonneg _) hS2 (Nat.cast_nonneg _)
      hAff hcand (Nat.cast_nonneg _) hcandleR hSc hSE hJnR hV0 hℓ1 hVℓ2 hVY hVℓ hℓY hY1
      hΛ1 hK₁ (by simpa using hpot) hT0 hR0 hUH0 hD0 hC
    refine le_trans (le_of_eq ?_) key
    rw [hJmR]
    ring

/-- **The amortized cost of a step with `0 < j`.** The program's bound for the step, with the
overhead of the batch loop, is at most `C` times the budget of the step in the sum of Lemma 5.9,
plus `1440` times the drop of the potential `levelPot`. It assumes `1 ≤ max p_s p_t` (`hp`) and a
bound `nMax` on the number of vertices after the step. This is the hypothesis `hpos` of
`updateLoop_amortized_sum`. -/
theorem stepPos_budget (impl : SparsifyImpl) {G₀ : MGraph} {mMax L q vCap eCap nMax : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj : 0 < chooseLevel L q (k + 1))
    (hn : (G₀.applyBatch (us.take (k + 1))).n ≤ nMax)
    (hp : 1 ≤ max impl.p_s impl.p_t) (C : ℝ) (hC : (dsStepPosFactor impl : ℝ) ≤ C) :
    let P := (canonicalSparsifyParams impl mMax).absorbTime
    let res := runStepOut (L := L) G₀ q (canonicalSparsify impl) us k
    (dsStepAmortCost G₀ impl mMax L q vCap eCap us k : ℝ) ≤
      C * (((L : ℝ) + 1) * ((G₀.applyBatch (us.take k)).updateEnc (us[k]'hk) : ℝ) +
          (res.UH.length : ℝ) + (res.D.card : ℝ) +
          ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
            (22 * (P.K_t + P.K_s + 1) *
              (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
                P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
              (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t))) +
        1440 * ((levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us k) : ℝ) -
          (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) : ℝ)) := by
  intro P res
  have hF := stepPos_facts (mMax := mMax) impl hVG₀ hL hq hGm₀ hBV hds hk hj
  dsimp only at hF
  set u := us[k]'hk with hu_def
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  set m : StepPosModel := ⟨G₀, impl, L, q, k, us, u⟩ with hm
  obtain ⟨hres, hS2, hAff, hpiL, hJn, hJnG, hAm, hEsub, hCsub, hcand, hpot, hNE⟩ := hF
  have hjL : m.j ≤ L := chooseLevel_le L q (k + 1)
  have hresR : res = m.res := hres
  -- The graph after the update.
  have hq1 : 1 ≤ q := by omega
  have hSpec : SparsifySpec mMax P (canonicalSparsify impl) :=
    canonicalSparsify_spec_absorb impl mMax
  obtain ⟨hInvk, -⟩ := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds k hk.le
  have hreemb_eq : runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k = m.E_aff := by
    simp only [runStepReembSet, hu]
    have hq_eq : m.st.q = q := hInvk.q_eq
    have ht_eq : m.st.t = k := hInvk.t_eq
    have hcl : chooseLevel L m.st.q (m.st.t + 1) ≠ 0 := by
      rw [hq_eq, ht_eq]; exact Nat.ne_of_gt hj
    have hsr := stepReembSet_eq_pos m.st u hcl
    dsimp only at hsr
    change stepReembSet m.st u = m.E_aff
    rw [hsr]
    simp only [hq_eq, ht_eq]
    rfl
  -- The program's cost, in pieces.
  have hstep : dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 =
      dsStepPosCostModel m mMax vCap eCap 0 := by
    unfold dsStepCostAt
    rw [hu]
    exact if_neg (Nat.ne_of_gt hj)
  have hAffN : dsStepPosAffCostModel m =
      100 * modelCandRevSum m + 100 * (m.j * m.S_prev.card) + 100 * m.S_prev.card + 100 * m.j +
        100 * (∑ e ∈ modelCandSet m, (m.piLt_mid e).length) +
        40 * ((modelCandSet m).card * m.j) + 160 * (modelCandSet m).card +
        m.E_aff.card * (35 * m.j + 60) + 800 * (∑ e ∈ m.E_aff, (m.piLt_mid e).length) +
        2000 * m.E_aff.card + 1200 := by
    simp only [dsStepPosAffCostModel, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      smul_eq_mul]
    ring
  have hcost : dsStepAmortCost G₀ impl mMax L q vCap eCap us k =
      (500 * (m.L + 1) + 1320 * 0 + 1100) + (20 * (m.L + 1 - m.j) + 20) +
        (100 * modelCandRevSum m + 100 * (m.j * m.S_prev.card) + 100 * m.S_prev.card +
          100 * m.j + 100 * (∑ e ∈ modelCandSet m, (m.piLt_mid e).length) +
          40 * ((modelCandSet m).card * m.j) + 160 * (modelCandSet m).card +
          m.E_aff.card * (35 * m.j + 60) + 800 * (∑ e ∈ m.E_aff, (m.piLt_mid e).length) +
          2000 * m.E_aff.card + 1200) +
        ((if 0 < m.E_aff.card then
            dsStepPosNonEmptyCost m.impl mMax m.L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH
              m.S_prev m.E_aff.toList (modelOldSum m)
          else dsStepPosEmptyCost m.L m.j (modelOldSum m)) +
          dsStepPosEpilogueCost m.S_prev.card m.J.m m.J.n 0 m.res.UH.length + 40) + 330 +
        35 * L + 520 + 90 * m.res.D.card + 90 * m.E_aff.card + 240 * m.res.UH.length + 240 := by
    rw [dsStepAmortCost_eq, hstep, hres, hreemb_eq]
    unfold dsStepPosCostModel dsStepPosCost
    rw [hAffN, Finset.length_toList]
  have hG'eq : m.G' = G₀.applyBatch (us.take (k + 1)) := by
    show (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u = _
    rw [hInvk.G_eq, take_succ_of_getElem? hu, applyBatch_append]
    rfl
  have hG'n : m.G'.n ≤ nMax := hG'eq ▸ hn
  have henc : (1 : ℝ) ≤ ((G₀.applyBatch (us.take k)).updateEnc u : ℝ) := by
    exact_mod_cast one_le_updateEnc _ u
  have key := stepPos_budget_of (L := L) (j := m.j) (Δ := G₀.maxDeg) (m0 := G₀.m)
    (crs := modelCandRevSum m) (oS := modelOldSum m) (UH := m.res.UH.length)
    (D := m.res.D.card) (G' := m.G') (J := m.J) (S := m.S_prev) (Ea := m.E_aff)
    (Cs := modelCandSet m) (piLt := m.piLt_mid) (embJH := m.embJH) (vCap := vCap)
    (eCap := eCap) (mMax := mMax) (nMax := nMax)
    (sLen := k + 1 - lastRebuild q L (m.j - 1) (k + 1))
    (Φ0 := (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us k) : ℝ))
    (Φ1 := (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) : ℝ))
    (implc := m.impl) (Lc := m.L) impl rfl rfl hL hj hjL henc hp hC hS2 hAff hpiL hJn hJnG hG'n
    hAm hEsub hCsub rfl rfl (card_modelCandSet_le m) hcand hpot hNE
  rw [hcost, hresR]
  exact key

/-- **The sum of Lemma 5.9 for the update loop, with no extra hypothesis.** Under deletions and
splits, with `T` updates, at most `nMax ≤ q^L` vertices, and `1 ≤ max p_s p_t`, the program's
cost of the first `T` steps is at most `C · 45 L q K₁ E_L Δ₁ Λ · Enc(U)` plus `1440 Φ_0`, for the
constant `C = dsInitCostFactor impl + 3000 + dsStepPosFactor impl`. It depends only on the
constants of the sparsifier. -/
theorem updateLoop_amortized (impl : SparsifyImpl) {G₀ : MGraph} {mMax L q vCap eCap : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {T nMax : ℕ} (hT : T ≤ us.length) (hnMax : G₀.n + batchSplitCount (us.take T) ≤ nMax)
    (hn_pow : max nMax 1 ≤ q ^ L) (hp : 1 ≤ max impl.p_s impl.p_t) :
    let P := (canonicalSparsifyParams impl mMax).absorbTime
    ∑ k ∈ Finset.range T, (dsStepAmortCost G₀ impl mMax L q vCap eCap us k : ℝ) ≤
      ((dsInitCostFactor impl : ℝ) + 3000 + (dsStepPosFactor impl : ℝ)) *
        (45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) *
          (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) *
          (G₀.batchEnc (us.take T) : ℝ)) +
      1440 * (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us 0) : ℝ) := by
  have h0 : (0 : ℝ) ≤ (dsStepPosFactor impl : ℝ) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (dsInitCostFactor impl : ℝ) := Nat.cast_nonneg _
  refine updateLoop_amortized_sum impl hVG₀ hL hq hGm₀ hBV hds hT hnMax hn_pow hp _
    (by linarith) fun k hk hj => ?_
  exact stepPos_budget impl hVG₀ hL hq hGm₀ hBV hds (lt_of_lt_of_le hk hT) hj
    (le_trans (n_take_le hBV hds (Nat.succ_le_of_lt hk)) hnMax) hp _ (by linarith)

end

end MinCostFlow.DynSpanner.Program
