module

public import MinCostFlow.DynSpanner.Correctness

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The summation step of Lemma 5.9

The cost bound of [chen2022maximum] Lemma 5.9 (arXiv:2203.00671v2, Section 5.1), as used in
Theorem 8.2 (page 39), sums per-step bounds over a prefix `[0, T)` of the updates. A step at level
`j = 0` (a restart) costs at most `N₁ · 12 L q K₁ E_L Δ₁ Λ` more than `(L + 1) Enc(u) + |U_H| + |D|`,
and it happens once every `q ^ L ≥ N₁` steps. A step at level `0 < j` costs at most
`sLen · 22 K₁ E_L Δ₁ Λ` more, where `sLen` is the number of steps since the last rebuild of level
`j - 1`, and these lengths sum to at most `L q T`. So the total is
`45 L q K₁ E_L Δ₁ Λ · Enc(us[0, T))`.

This file proves that sum for any function with these per-step bounds
(`lemma_5_9_sum_of_step_bounds`), so that it applies both to the model's cost `res.cost` and to the
cost bound of a program. It also holds the counting lemmas the sum uses: `sum_sLen_le` (the lengths
`sLen`) and `sum_range_restart_factor` (the restarts), and `expFactor_bounds`, which compares the
length and congestion bounds with `E_L`.
-/

namespace MinCostFlow.DynSpanner

public section

/-- A prefix of a batch has at most as many splits as the batch. -/
theorem batchSplitCount_take_le (us : List Update) (k : ℕ) :
    batchSplitCount (us.take k) ≤ batchSplitCount us := by
  have h : us = us.take k ++ us.drop k := (List.take_append_drop k us).symm
  conv_rhs => rw [h, batchSplitCount_append]
  exact Nat.le_add_right _ _

/-- Under deletions and splits, each split adds one vertex. -/
theorem n_applyBatch_of_delOrSplit :
    ∀ (xs : List Update) (G : MGraph),
      G.BatchIsValid xs → (∀ u ∈ xs, isDelOrSplit u) →
      (G.applyBatch xs).n = G.n + batchSplitCount xs
  | [], _, _, _ => by simp [MGraph.applyBatch, batchSplitCount]
  | u :: xs, G, hBV, hds => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hdu := hds u List.mem_cons_self
    have hds' : ∀ x ∈ xs, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    have ih := n_applyBatch_of_delOrSplit xs (G.applyUpdate u) hBV' hds'
    have hn1 := n_applyUpdate_of_delOrSplit hu hdu
    simp only [MGraph.applyBatch, List.foldl_cons] at ih ⊢
    rw [ih, hn1]
    have hsp : batchSplitCount (u :: xs) = (if isSplit u then 1 else 0) + batchSplitCount xs := by
      cases u with
      | delete _ => simp [batchSplitCount, isSplit]
      | insert _ _ _ => simp [batchSplitCount, isSplit]
      | split _ _ _ _ => simp [batchSplitCount, List.countP_cons, isSplit, Nat.add_comm]
    omega

/-- The encoding size of a concatenation of batches is the sum of the encoding sizes, each on the
graph it is applied to. -/
theorem batchEnc_append :
    ∀ (U₁ U₂ : List Update) (G : MGraph),
      G.batchEnc (U₁ ++ U₂) = G.batchEnc U₁ + (G.applyBatch U₁).batchEnc U₂
  | [], _, _ => by simp [MGraph.batchEnc, MGraph.applyBatch]
  | u :: U₁, U₂, G => by
    have ih := batchEnc_append U₁ U₂ (G.applyUpdate u)
    have hstep : G.applyBatch (u :: U₁) = (G.applyUpdate u).applyBatch U₁ := rfl
    simp only [List.cons_append, MGraph.batchEnc]
    rw [ih, hstep, Nat.add_assoc]

/-- Applying the batches `f 0, f 1, …` of a run in order, and the sum of their encoding sizes. -/
theorem applyBatch_and_batchEnc_flatMap :
    ∀ (f : ℕ → List Update) (H : ℕ → MGraph) (T : ℕ),
      (∀ k < T, (H k).applyBatch (f k) = H (k + 1)) →
      (H 0).applyBatch ((List.range T).flatMap f) = H T ∧
      (H 0).batchEnc ((List.range T).flatMap f) = ∑ k ∈ Finset.range T, (H k).batchEnc (f k)
  | _, _, 0, _ => ⟨rfl, by simp [MGraph.batchEnc]⟩
  | f, H, T + 1, hstep => by
    obtain ⟨hA, hE⟩ := applyBatch_and_batchEnc_flatMap f H T (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hsplit : (List.range (T + 1)).flatMap f = (List.range T).flatMap f ++ f T := by
      rw [List.range_succ, List.flatMap_append]; simp
    refine ⟨?_, ?_⟩
    · rw [hsplit, applyBatch_append, hA, hstep T (Nat.lt_succ_self T)]
    · rw [hsplit, batchEnc_append, hA, hE, Finset.sum_range_succ]

/-- The encoding sizes of the first `T` updates, each on the graph before it, sum to
`Enc(us[0, T))`. -/
theorem sum_range_updateEnc_opt (G₀ : MGraph) (us : List Update) :
    ∀ T ≤ us.length,
      (∑ k ∈ Finset.range T,
        match us[k]? with
        | some u => (G₀.applyBatch (us.take k)).updateEnc u
        | none => 0) =
      G₀.batchEnc (us.take T)
  | 0, _ => by simp [MGraph.batchEnc]
  | T + 1, hT => by
    have hT_le : T ≤ us.length := Nat.le_of_succ_le hT
    have hu : us[T]? = some (us[T]'hT) := List.getElem?_eq_getElem hT
    have htake : us.take (T + 1) = us.take T ++ [us[T]'hT] := take_succ_of_getElem? hu
    rw [Finset.sum_range_succ, sum_range_updateEnc_opt G₀ us T hT_le, htake, batchEnc_append, hu]
    simp [MGraph.batchEnc]

/-- Among the first `T` steps, at most `T / B_j` choose level `j` (`B_j = phasePeriod q L j`). -/
theorem card_level_eq_filter_le {q L : ℕ} (hq : 1 ≤ q) {j : ℕ} (hj : j ≤ L) (T : ℕ) :
    (((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
      (fun k => chooseLevel L q (k + 1) = j)).card ≤ T / phasePeriod q L j := by
  have him : (((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
      (fun k => chooseLevel L q (k + 1) = j)).image (fun k => k + 1) ⊆
      (Finset.Icc 1 T).filter (fun s => phasePeriod q L j ∣ s) := by
    intro s hs
    rw [Finset.mem_image] at hs
    rcases hs with ⟨k, hk, rfl⟩
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.succ_pos k, hk.1.1⟩, ?_⟩
    exact (chooseLevel_le_iff_dvd hq hj).mp (hk.2 ▸ le_rfl)
  calc (((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
          (fun k => chooseLevel L q (k + 1) = j)).card
      = ((((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
          (fun k => chooseLevel L q (k + 1) = j)).image (fun k => k + 1)).card :=
        (Finset.card_image_of_injective _ Nat.succ_injective).symm
    _ ≤ ((Finset.Icc 1 T).filter (fun s => phasePeriod q L j ∣ s)).card := Finset.card_le_card him
    _ ≤ T / phasePeriod q L j := card_multiples_le (phasePeriod q L j) T (phasePeriod_pos hq L j)

/-- Among the first `T` steps, at most `T / B_0` are restarts. -/
theorem card_level_zero_filter_le {q L : ℕ} (hq : 1 ≤ q) (T : ℕ) :
    ((Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)).card ≤
      T / phasePeriod q L 0 := by
  have him : ((Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)).image (fun k => k + 1) ⊆
      (Finset.Icc 1 T).filter (fun s => phasePeriod q L 0 ∣ s) := by
    intro s hs
    rw [Finset.mem_image] at hs
    rcases hs with ⟨k, hk, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.succ_pos k, hk.1⟩, ?_⟩
    exact (chooseLevel_le_iff_dvd hq (Nat.zero_le L)).mp (hk.2 ▸ le_rfl)
  calc ((Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)).card
      = (((Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)).image
          (fun k => k + 1)).card :=
        (Finset.card_image_of_injective _ Nat.succ_injective).symm
    _ ≤ ((Finset.Icc 1 T).filter (fun s => phasePeriod q L 0 ∣ s)).card := Finset.card_le_card him
    _ ≤ T / phasePeriod q L 0 := card_multiples_le (phasePeriod q L 0) T (phasePeriod_pos hq L 0)

/-- The number of steps since the last rebuild of level `j - 1` is at most `q · B_j`. -/
theorem sLen_lt_phasePeriod {q L : ℕ} (hq : 1 ≤ q) {j : ℕ}
    (hj_pos : 0 < j) (hj_le : j ≤ L) (k : ℕ) :
    k + 1 - lastRebuild q L (j - 1) (k + 1) ≤ q * phasePeriod q L j := by
  have hB_pos : 0 < phasePeriod q L (j - 1) := phasePeriod_pos hq L (j - 1)
  have hdiv := Nat.div_add_mod (k + 1) (phasePeriod q L (j - 1))
  have hmod := Nat.mod_lt (k + 1) hB_pos
  have hsLen : k + 1 - lastRebuild q L (j - 1) (k + 1) ≤ phasePeriod q L (j - 1) := by
    unfold lastRebuild
    rw [mul_comm (phasePeriod q L (j - 1)) _] at hdiv
    omega
  have hB_eq : phasePeriod q L (j - 1) = q * phasePeriod q L j := by
    simp only [phasePeriod]
    have hexp : L - (j - 1) = (L - j) + 1 := by omega
    rw [hexp, pow_succ']
  exact le_trans hsLen (by rw [hB_eq])

/-- Over the steps at levels `0 < j` among the first `T`, the lengths `sLen` sum to at most
`L q T`. -/
theorem sum_sLen_le {L q : ℕ} (hq : 1 ≤ q) (T : ℕ) :
    (∑ k ∈ (Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1)),
      ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) ≤
      (L : ℝ) * (q : ℝ) * (T : ℝ) := by
  have hmaps : ∀ k ∈ (Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1)),
      chooseLevel L q (k + 1) ∈ Finset.Icc 1 L := fun k hk => by
    rw [Finset.mem_filter] at hk
    exact Finset.mem_Icc.mpr ⟨hk.2, chooseLevel_le L q (k + 1)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hj_bnd : ∀ j ∈ Finset.Icc 1 L,
      (∑ k ∈ ((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
        (fun k => chooseLevel L q (k + 1) = j),
          ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) ≤
      (q : ℝ) * (T : ℝ) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hcard := card_level_eq_filter_le hq hj.2 T
    have hterm : ∀ k ∈ ((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
        (fun k => chooseLevel L q (k + 1) = j),
        ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) ≤
        (q : ℝ) * (phasePeriod q L j : ℝ) := fun k hk => by
      rw [Finset.mem_filter] at hk
      rw [hk.2]
      exact_mod_cast sLen_lt_phasePeriod hq hj.1 hj.2 k
    calc (∑ k ∈ ((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
            (fun k => chooseLevel L q (k + 1) = j),
              ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ))
        ≤ ∑ _ ∈ ((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
            (fun k => chooseLevel L q (k + 1) = j),
            (q : ℝ) * (phasePeriod q L j : ℝ) := Finset.sum_le_sum hterm
      _ = (((((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
            (fun k => chooseLevel L q (k + 1) = j)).card : ℕ) : ℝ) *
            ((q : ℝ) * (phasePeriod q L j : ℝ)) := by simp
      _ ≤ ((T / phasePeriod q L j : ℕ) : ℝ) * ((q : ℝ) * (phasePeriod q L j : ℝ)) := by
            gcongr
      _ = (q : ℝ) * (((T / phasePeriod q L j * phasePeriod q L j : ℕ) : ℝ)) := by
            push_cast; ring
      _ ≤ (q : ℝ) * (T : ℝ) := by
            gcongr
            exact_mod_cast Nat.div_mul_le_self T (phasePeriod q L j)
  calc ∑ j ∈ Finset.Icc 1 L,
          ∑ k ∈ ((Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))).filter
            (fun k => chooseLevel L q (k + 1) = j),
              ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)
      ≤ ∑ _ ∈ Finset.Icc 1 L, (q : ℝ) * (T : ℝ) := Finset.sum_le_sum hj_bnd
    _ = (L : ℝ) * (q : ℝ) * (T : ℝ) := by simp [mul_assoc]

/-- The restarts among the first `T` steps, each charged `A`, cost at most `T · A / q ^ L`. -/
theorem sum_range_restart_factor {q L T : ℕ} (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A) :
    (((Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)).card : ℝ) * A ≤
      (T : ℝ) * (A / (q ^ L : ℝ)) := by
  have hcard := card_level_zero_filter_le (L := L) hq T
  have hBpos : (0 : ℝ) < (q ^ L : ℝ) := by
    exact_mod_cast Nat.pow_pos (by omega : 0 < q)
  have hB_eq : phasePeriod q L 0 = q ^ L := by simp [phasePeriod]
  rw [hB_eq] at hcard
  calc (((Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)).card : ℝ) * A
      ≤ ((T / q ^ L : ℕ) : ℝ) * A := by gcongr
    _ = (((T / q ^ L * q ^ L : ℕ) : ℝ)) * (A / (q ^ L : ℝ)) := by
          push_cast; field_simp [ne_of_gt hBpos]
    _ ≤ (T : ℝ) * (A / (q ^ L : ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_mul_le_self T (q ^ L))
            (div_nonneg hA (le_of_lt hBpos))

/-- The length and congestion bounds of level `L`, and their products used in Lemma 5.9, are at
most `E_L` (times `Δ₀ + 1` for the congestion). -/
theorem expFactor_bounds {γ_c γ_ℓ : ℝ} (hc : 1 ≤ γ_c) (hl : 1 ≤ γ_ℓ) (L maxDeg₀ : ℕ) :
    let ℓ_L := lenBound γ_ℓ L
    let V_L := vcongBound γ_c γ_ℓ maxDeg₀ L
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) *
      γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let deg1 := (maxDeg₀ : ℝ) + 1
    1 ≤ E_L ∧ γ_ℓ ≤ E_L ∧ γ_ℓ ^ 2 ≤ E_L ∧
    ℓ_L ≤ E_L ∧ ℓ_L + 1 ≤ E_L ∧
    V_L ≤ E_L * deg1 ∧ V_L * ℓ_L ≤ E_L * deg1 ∧
    V_L * γ_ℓ ^ 2 * (ℓ_L + 1) ≤ E_L * deg1 ∧
    V_L * γ_ℓ * (ℓ_L + 1) ≤ E_L * deg1 ∧
    γ_ℓ * (ℓ_L + 1) ≤ E_L := by
  intro ℓ_L V_L E_L deg1
  have hc0 : 0 ≤ γ_c := by linarith
  have hl0 : 0 ≤ γ_ℓ := by linarith
  have hE1 : 1 ≤ E_L := by
    have h1 : (1 : ℝ) ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ γ_c ^ (L + 1) := one_le_pow₀ hc
    have h3 : (1 : ℝ) ≤ γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := one_le_pow₀ hl
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
  have hexp_tri : L * (L + 1) / 2 + (L + 1) = (L + 1) * (L + 2) / 2 := by
    have h2 : (L + 1) * (L + 2) = L * (L + 1) + 2 * (L + 1) := by ring
    rw [h2]; omega
  have hℓ : ℓ_L ≤ E_L := by
    unfold ℓ_L lenBound E_L
    have h3 : (3 : ℝ) ^ L ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h1c : (1 : ℝ) ≤ γ_c ^ (L + 1) := one_le_pow₀ hc
    have hl_le : γ_ℓ ^ (L + 1) ≤ γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) :=
      pow_le_pow_right₀ hl (by rw [← hexp_tri]; omega)
    have h1r : (3 : ℝ) ^ L * γ_ℓ ^ (L + 1) = (3 : ℝ) ^ L * 1 * γ_ℓ ^ (L + 1) := by ring
    rw [h1r]
    exact mul_le_mul (mul_le_mul h3 h1c (by norm_num) (by positivity)) hl_le
      (pow_nonneg hl0 _) (by positivity)
  have hℓ1 : ℓ_L + 1 ≤ E_L := by
    unfold ℓ_L lenBound E_L
    have h3 : (3 : ℝ) ^ L * 2 ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) := by
      have : (3 : ℝ) ^ L * 2 ≤ 3 ^ L * 3 := by gcongr; norm_num
      have hpow : (3 : ℝ) ^ (L + 1) ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [show (3 : ℝ) ^ (L + 1) = 3 ^ L * 3 from pow_succ _ _]
    have h1c : (1 : ℝ) ≤ γ_c ^ (L + 1) := one_le_pow₀ hc
    have h1l : (1 : ℝ) ≤ ℓ_L := one_le_lenBound hl L
    have hl_le : γ_ℓ ^ (L + 1) ≤ γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) :=
      pow_le_pow_right₀ hl (by rw [← hexp_tri]; omega)
    calc ℓ_L + 1 ≤ 2 * ℓ_L := by linarith
      _ = ((3 : ℝ) ^ L * 2) * 1 * γ_ℓ ^ (L + 1) := by dsimp only [ℓ_L, lenBound]; ring
      _ ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) * γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) :=
          mul_le_mul (mul_le_mul h3 h1c (by norm_num) (by positivity)) hl_le
            (pow_nonneg hl0 _) (by positivity)
  have hγl_le : γ_ℓ ≤ E_L := by
    have : γ_ℓ ≤ γ_ℓ ^ (L + 1) := by simpa using pow_le_pow_right₀ hl (by omega : 1 ≤ L + 1)
    have h1 : 1 ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
    have hℓ_ge : γ_ℓ ^ (L + 1) ≤ ℓ_L := by
      dsimp only [ℓ_L, lenBound]; exact le_mul_of_one_le_left (pow_nonneg hl0 _) h1
    exact le_trans (le_trans this hℓ_ge) hℓ
  have hγl2_le : γ_ℓ ^ 2 ≤ E_L := by
    have : γ_ℓ ^ 2 ≤ γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) :=
      pow_le_pow_right₀ hl (by omega)
    have h3 : (1 : ℝ) ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) := one_le_pow₀ (by norm_num)
    have h1c : (1 : ℝ) ≤ γ_c ^ (L + 1) := one_le_pow₀ hc
    calc γ_ℓ ^ 2 = 1 * 1 * γ_ℓ ^ 2 := by ring
      _ ≤ E_L := by dsimp only [E_L]; gcongr
  have hdeg : (maxDeg₀ : ℝ) ≤ deg1 := by dsimp only [deg1]; linarith
  have hdeg0 : 0 ≤ deg1 := by dsimp only [deg1]; positivity
  have hV_mul : ∀ (k3 kl : ℕ),
      (3 : ℝ) ^ k3 ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) →
      kl ≤ (L + 1) * (L + 2) / 2 + 2 →
      (3 : ℝ) ^ k3 * γ_ℓ ^ kl * γ_c ^ (L + 1) * (maxDeg₀ : ℝ) ≤ E_L * deg1 := by
    intro k3 kl hk3 hkl
    have hle_l : γ_ℓ ^ kl ≤ γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := pow_le_pow_right₀ hl hkl
    calc (3 : ℝ) ^ k3 * γ_ℓ ^ kl * γ_c ^ (L + 1) * (maxDeg₀ : ℝ)
        ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) *
          γ_c ^ (L + 1) * deg1 := by gcongr
      _ = E_L * deg1 := by dsimp only [E_L]; ring
  have hV : V_L ≤ E_L * deg1 := by
    unfold V_L vcongBound
    exact hV_mul _ _ (pow_le_pow_right₀ (by norm_num) (by omega)) (by rw [← hexp_tri]; omega)
  have hVℓ : V_L * ℓ_L ≤ E_L * deg1 := by
    have heq : V_L * ℓ_L = 3 ^ ((L + 1) * (L + 2) / 2 + L) * γ_ℓ ^ ((L + 1) * (L + 2) / 2) *
        γ_c ^ (L + 1) * (maxDeg₀ : ℝ) := by
      unfold V_L vcongBound ℓ_L lenBound
      rw [← hexp_tri, pow_add, pow_add]; ring
    rw [heq]
    exact hV_mul _ _ (pow_le_pow_right₀ (by norm_num) (by omega)) (by omega)
  have hVℓ2 : V_L * γ_ℓ ^ 2 * (ℓ_L + 1) ≤ E_L * deg1 := by
    have h1l : (1 : ℝ) ≤ ℓ_L := one_le_lenBound hl L
    have h2 : V_L * γ_ℓ ^ 2 * (ℓ_L + 1) ≤
        (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 1) * γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) *
          γ_c ^ (L + 1) * (maxDeg₀ : ℝ) := by
      have heq : 2 * (V_L * γ_ℓ ^ 2 * ℓ_L) =
          (3 ^ ((L + 1) * (L + 2) / 2 + L) * 2) * γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) *
            γ_c ^ (L + 1) * (maxDeg₀ : ℝ) := by
        unfold V_L vcongBound ℓ_L lenBound
        rw [← hexp_tri, pow_add, pow_add, pow_add]; ring
      have hVnn : 0 ≤ V_L := vcongBound_nonneg hc0 hl0 maxDeg₀ L
      have hbd : V_L * γ_ℓ ^ 2 * (ℓ_L + 1) ≤ 2 * (V_L * γ_ℓ ^ 2 * ℓ_L) := by
        have : ℓ_L + 1 ≤ 2 * ℓ_L := by linarith
        nlinarith [mul_nonneg hVnn (sq_nonneg γ_ℓ)]
      have h32 : (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L) * 2 ≤
          3 ^ ((L + 1) * (L + 2) / 2 + L + 1) := by
        rw [pow_succ]; linarith [pow_pos (by norm_num : (0 : ℝ) < 3) ((L + 1) * (L + 2) / 2 + L)]
      refine le_trans hbd (le_trans (le_of_eq heq) ?_)
      gcongr
    exact le_trans h2 (hV_mul _ _ (pow_le_pow_right₀ (by norm_num) (by omega)) (by omega))
  have hVℓ1 : V_L * γ_ℓ * (ℓ_L + 1) ≤ E_L * deg1 := by
    have hVnn : 0 ≤ V_L := vcongBound_nonneg hc0 hl0 maxDeg₀ L
    have hlnn : 0 ≤ ℓ_L + 1 := by linarith [one_le_lenBound hl L]
    have h1 : V_L * γ_ℓ * (ℓ_L + 1) ≤ V_L * γ_ℓ ^ 2 * (ℓ_L + 1) := by
      have : γ_ℓ ≤ γ_ℓ ^ 2 := by nlinarith
      nlinarith [mul_nonneg hVnn hlnn]
    exact le_trans h1 hVℓ2
  have hγℓ1 : γ_ℓ * (ℓ_L + 1) ≤ E_L := by
    have h1l : 1 ≤ ℓ_L := one_le_lenBound hl L
    have h3 : (3 : ℝ) ^ L * 2 ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) := by
      have : (3 : ℝ) ^ L * 2 ≤ 3 ^ L * 3 := by gcongr; norm_num
      have hpow : (3 : ℝ) ^ (L + 1) ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [show (3 : ℝ) ^ (L + 1) = 3 ^ L * 3 from pow_succ _ _]
    have h1c : 1 ≤ γ_c ^ (L + 1) := one_le_pow₀ hc
    have hl_exp : L + 2 ≤ (L + 1) * (L + 2) / 2 + 2 := by
      rw [← hexp_tri]
      have h2 : L + 1 ≤ L * (L + 1) / 2 + (L + 1) := by omega
      omega
    have hl_le : γ_ℓ ^ (L + 2) ≤ γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) :=
      pow_le_pow_right₀ hl hl_exp
    have hmul : γ_ℓ * (ℓ_L + 1) ≤ γ_ℓ * (2 * ℓ_L) :=
      mul_le_mul_of_nonneg_left (by linarith) hl0
    have h2l : γ_ℓ * (2 * ℓ_L) = ((3 : ℝ) ^ L * 2) * 1 * γ_ℓ ^ (L + 2) := by
      dsimp only [ℓ_L, lenBound]
      have hpw : γ_ℓ ^ (L + 2) = γ_ℓ ^ (L + 1) * γ_ℓ := pow_succ _ _
      rw [hpw]; ring
    exact le_trans hmul (le_trans (le_of_eq h2l)
      (mul_le_mul (mul_le_mul h3 h1c (by norm_num) (by positivity)) hl_le
        (pow_nonneg hl0 _) (by positivity)))
  exact ⟨hE1, hγl_le, hγl2_le, hℓ, hℓ1, hV, hVℓ, hVℓ2, hVℓ1, hγℓ1⟩

/-- **The sum of Lemma 5.9** ([chen2022maximum] Lemma 5.9, arXiv:2203.00671v2, Section 5.1, as
used for Theorem 8.2, page 39). Let `f k` be a cost of step `k` that exceeds
`(L + 1) Enc(u_k) + |U_H| + |D|` by at most `N₁ · 12 L q K₁ E_L Δ₁ Λ` at a restart (`j = 0`), and by
at most `sLen · 22 K₁ E_L Δ₁ Λ` at a rebuild of level `0 < j`. Then the sum of `f` over the first
`T` steps is at most `45 L q K₁ E_L Δ₁ Λ · Enc(us[0, T))`. The hypotheses on `∑ |U_H|` and `∑ |D|`
are the bounds of `lemma_5_9`. -/
theorem lemma_5_9_sum_of_step_bounds {G₀ : MGraph} {L q : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hL : 1 ≤ L) (hq : 2 ≤ q) {us : List Update} {T nMax : ℕ} (hT : T ≤ us.length)
    (hn_pow : max nMax 1 ≤ q ^ L)
    (hTotal_UH : ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) ≤
      (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ *
        (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) * (T : ℝ))
    (hTotal_D : ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
      3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) *
        (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s * (T : ℝ))
    (f : ℕ → ℝ)
    (hf0 : ∀ k (hk : k < T), chooseLevel L q (k + 1) = 0 →
      f k ≤ ((L : ℝ) + 1) *
          ((G₀.applyBatch (us.take k)).updateEnc (us[k]'(lt_of_lt_of_le hk hT)) : ℝ) +
        ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) +
        ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) +
        ((max nMax 1 : ℕ) : ℝ) * (12 * ((L : ℝ) * (q : ℝ)) * (P.K_t + P.K_s + 1) *
          (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)))
    (hfpos : ∀ k (hk : k < T), 0 < chooseLevel L q (k + 1) →
      f k ≤ ((L : ℝ) + 1) *
          ((G₀.applyBatch (us.take k)).updateEnc (us[k]'(lt_of_lt_of_le hk hT)) : ℝ) +
        ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) +
        ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) +
        ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
          (22 * (P.K_t + P.K_s + 1) *
            (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
              P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
            (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t))) :
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    ∑ k ∈ Finset.range T, f k ≤
      45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
        (G₀.batchEnc (us.take T) : ℝ) := by
  intro Λ E_L
  have hq1 : 1 ≤ q := le_trans (by omega) hq
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hL_r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hq_r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hLq_ge2 : (2 : ℝ) ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have hL1 : (L : ℝ) + 1 ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have h1nm : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hlog_nm_nn : 0 ≤ Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := Real.log_nonneg h1nm
  set Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
  have hΛs_ge1 : 1 ≤ Λ_s := one_le_pow₀ (by linarith)
  have hΛ_ge1 : 1 ≤ Λ := one_le_pow₀ (by linarith)
  have hΛs_le : Λ_s ≤ Λ := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  set N_1 : ℝ := ((max nMax 1 : ℕ) : ℝ)
  have hN1_pow : N_1 ≤ (q ^ L : ℝ) := by dsimp only [N_1]; exact_mod_cast hn_pow
  set F0 := (Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)
  set Fpos := (Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))
  have hsplit_sum : ∀ f : ℕ → ℝ,
      ∑ k ∈ Finset.range T, f k = (∑ k ∈ F0, f k) + (∑ k ∈ Fpos, f k) := fun f => by
    have h := (Finset.sum_filter_add_sum_filter_not (Finset.range T)
      (fun k => chooseLevel L q (k + 1) = 0) f).symm
    have hFpos : (Finset.range T).filter (fun k => ¬ chooseLevel L q (k + 1) = 0) = Fpos := by
      ext k; simp only [Fpos, Finset.mem_filter, Nat.pos_iff_ne_zero]
    rwa [hFpos] at h
  obtain ⟨hEL1, hEL_l, _, _, _, _, _, _, _, hEL_γℓ1⟩ := expFactor_bounds P.hγ_c P.hγ_ℓ L G₀.maxDeg
  set deg1 : ℝ := (G₀.maxDeg : ℝ) + 1
  set K1 : ℝ := P.K_t + P.K_s + 1
  have hK1_nn : 0 ≤ K1 := by linarith [P.hK_t, P.hK_s]
  have hEL_nn : 0 ≤ E_L := by linarith
  have hdeg1_nn : 0 ≤ deg1 := by positivity
  have h1_d : (1 : ℝ) ≤ deg1 := by
    dsimp only [deg1]; linarith [Nat.cast_nonneg (α := ℝ) G₀.maxDeg]
  have h1_le : (1 : ℝ) ≤ K1 := by dsimp only [K1]; linarith [P.hK_t, P.hK_s]
  have hKs_le : P.K_s ≤ K1 := by dsimp only [K1]; linarith [P.hK_t]
  have hM : 0 ≤ K1 * E_L * deg1 * Λ := by positivity
  set enc_k : ℕ → ℝ := fun k => match us[k]? with
    | some u => ((G₀.applyBatch (us.take k)).updateEnc u : ℝ)
    | none => 0
  set extra_k : ℕ → ℝ := fun k =>
    f k - ((L : ℝ) + 1) * enc_k k -
      ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) -
      ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ)
  have hsum_enc : ∑ k ∈ Finset.range T, enc_k k = (G₀.batchEnc (us.take T) : ℝ) := by
    have hmatch_cast : ∀ k, (match us[k]? with
        | some u => ((G₀.applyBatch (us.take k)).updateEnc u : ℝ)
        | none => 0) =
        ((match us[k]? with
          | some u => (G₀.applyBatch (us.take k)).updateEnc u
          | none => 0 : ℕ) : ℝ) := fun k => by
      cases us[k]? <;> simp
    dsimp only [enc_k]
    simp_rw [hmatch_cast]
    exact_mod_cast sum_range_updateEnc_opt G₀ us T hT
  have hT_enc : (T : ℝ) ≤ (G₀.batchEnc (us.take T) : ℝ) := by
    have := length_le_batchEnc G₀ (us.take T)
    rw [List.length_take, min_eq_left hT] at this
    exact_mod_cast this
  have hsum_decomp :
      ∑ k ∈ Finset.range T, f k =
      ((L : ℝ) + 1) * (G₀.batchEnc (us.take T) : ℝ) +
        ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) +
        ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) +
        (∑ k ∈ F0, extra_k k) + (∑ k ∈ Fpos, extra_k k) := by
    have h1 : ∀ k, f k =
        ((L : ℝ) + 1) * enc_k k +
        ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) +
        ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) + extra_k k := fun k => by
      dsimp only [extra_k]; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_enc]
    rw [hsplit_sum extra_k]
    ring
  have hExtra_F0 : ∀ k ∈ F0, extra_k k ≤ N_1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hk_lt : k < us.length := lt_of_lt_of_le hk.1 hT
    have hu_some : us[k]? = some (us[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
    have h0 := hf0 k hk.1 hk.2
    have henc_match : enc_k k = ((G₀.applyBatch (us.take k)).updateEnc (us[k]'hk_lt) : ℝ) := by
      simp [enc_k, hu_some]
    dsimp only [extra_k]
    rw [henc_match]
    dsimp only [N_1, K1, E_L, deg1, Λ]
    linarith
  have hExtra_Fpos : ∀ k ∈ Fpos,
      extra_k k ≤ ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
        (22 * K1 * E_L * deg1 * Λ) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hk_lt : k < us.length := lt_of_lt_of_le hk.1 hT
    have hu_some : us[k]? = some (us[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
    have h0 := hfpos k hk.1 hk.2
    have henc_match : enc_k k = ((G₀.applyBatch (us.take k)).updateEnc (us[k]'hk_lt) : ℝ) := by
      simp [enc_k, hu_some]
    dsimp only [extra_k]
    rw [henc_match]
    dsimp only [K1, E_L, deg1, Λ]
    linarith
  have hSum_F0_extra : ∑ k ∈ F0, extra_k k ≤
      12 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ * (T : ℝ) := by
    have hAnn : 0 ≤ N_1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ) := by positivity
    calc ∑ k ∈ F0, extra_k k
        ≤ ∑ _ ∈ F0, N_1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ) :=
          Finset.sum_le_sum hExtra_F0
      _ = (F0.card : ℝ) * (N_1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ)) := by simp
      _ ≤ (T : ℝ) * ((N_1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ)) / (q ^ L : ℝ)) :=
          sum_range_restart_factor hq1 hAnn
      _ ≤ (T : ℝ) * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ) := by
          gcongr
          have hBpos : (0 : ℝ) < (q ^ L : ℝ) := by exact_mod_cast Nat.pow_pos (by omega : 0 < q)
          have : 0 ≤ 12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ := by positivity
          calc (N_1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ)) / (q ^ L : ℝ)
              = (N_1 / (q ^ L : ℝ)) * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ) := by ring
            _ ≤ 1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ) := by
                gcongr; exact (div_le_one hBpos).mpr hN1_pow
            _ = 12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ := one_mul _
      _ = _ := by ring
  have hSum_Fpos_extra : ∑ k ∈ Fpos, extra_k k ≤
      22 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ * (T : ℝ) := by
    have hnn : 0 ≤ 22 * K1 * E_L * deg1 * Λ := by positivity
    calc ∑ k ∈ Fpos, extra_k k
        ≤ ∑ k ∈ Fpos, ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
            (22 * K1 * E_L * deg1 * Λ) := Finset.sum_le_sum hExtra_Fpos
      _ = (∑ k ∈ Fpos, ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
            (22 * K1 * E_L * deg1 * Λ) := by rw [← Finset.sum_mul]
      _ ≤ ((L : ℝ) * (q : ℝ) * (T : ℝ)) * (22 * K1 * E_L * deg1 * Λ) :=
          mul_le_mul_of_nonneg_right (sum_sLen_le hq1 T) hnn
      _ = _ := by ring
  have h1prod : 1 ≤ K1 * E_L * deg1 * Λ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1_le hEL1) h1_d) hΛ_ge1
  have hL1_Enc : ((L : ℝ) + 1) * (G₀.batchEnc (us.take T) : ℝ) ≤
      1 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ * (G₀.batchEnc (us.take T) : ℝ) := by
    have henc_nn : 0 ≤ (G₀.batchEnc (us.take T) : ℝ) := Nat.cast_nonneg _
    have : (L : ℝ) + 1 ≤ 1 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ := by
      calc (L : ℝ) + 1 ≤ (L : ℝ) * (q : ℝ) := hL1
        _ ≤ ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) := le_mul_of_one_le_right (by linarith) h1prod
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right this henc_nn
  have hKE_deg : K1 * E_L * Λ ≤ K1 * E_L * deg1 * Λ := by
    have h0 := mul_le_mul_of_nonneg_left h1_d (mul_nonneg hK1_nn hEL_nn)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right h0 (by linarith)
  have hUH_T : ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) ≤
      7 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ * (T : ℝ) := by
    have h2_le : (2 : ℝ) ≤ (L : ℝ) * (q : ℝ) * (K1 * E_L * deg1 * Λ) :=
      le_trans hLq_ge2 (le_mul_of_one_le_right (by linarith) h1prod)
    have hA : P.K_s * P.γ_ℓ ≤ K1 * E_L := mul_le_mul hKs_le hEL_l hγl hK1_nn
    have hB : P.K_s * P.γ_ℓ * Λ_s ≤ K1 * E_L * deg1 * Λ :=
      le_trans (mul_le_mul hA hΛs_le (by linarith) (mul_nonneg hK1_nn hEL_nn)) hKE_deg
    have h6_le : 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s ≤
        6 * (L : ℝ) * (q : ℝ) * (K1 * E_L * deg1 * Λ) := by
      have h0 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 6 * (L : ℝ) * (q : ℝ))
      exact le_trans (le_of_eq (by ring)) (le_trans h0 (le_of_eq (by ring)))
    calc ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ)
        ≤ (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ) := hTotal_UH
      _ ≤ (7 * (L : ℝ) * (q : ℝ) * (K1 * E_L * deg1 * Λ)) * (T : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [h2_le, h6_le]) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hD_T : ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
      3 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ * (T : ℝ) := by
    have hA : P.K_s * (P.γ_ℓ * (lenBound P.γ_ℓ L + 1)) ≤ K1 * E_L :=
      mul_le_mul hKs_le hEL_γℓ1 (mul_nonneg hγl (by linarith [lenBound_nonneg hγl L])) hK1_nn
    have hB : P.K_s * (P.γ_ℓ * (lenBound P.γ_ℓ L + 1)) * Λ_s ≤ K1 * E_L * deg1 * Λ :=
      le_trans (mul_le_mul hA hΛs_le (by linarith) (mul_nonneg hK1_nn hEL_nn)) hKE_deg
    have h3_le : 3 * (L : ℝ) * (q : ℝ) * P.K_s * (P.γ_ℓ * (lenBound P.γ_ℓ L + 1)) * Λ_s ≤
        3 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ := by
      have h0 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 3 * (L : ℝ) * (q : ℝ))
      exact le_trans (le_of_eq (by ring)) (le_trans h0 (le_of_eq (by ring)))
    calc ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ)
        ≤ (3 * (L : ℝ) * (q : ℝ) * P.K_s * (P.γ_ℓ * (lenBound P.γ_ℓ L + 1)) * Λ_s) * (T : ℝ) :=
          le_trans hTotal_D (le_of_eq (by ring))
      _ ≤ (3 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ) * (T : ℝ) :=
          mul_le_mul_of_nonneg_right h3_le (Nat.cast_nonneg _)
      _ = _ := by ring
  have hsum_T_bnd : ∑ k ∈ Finset.range T, f k ≤
      1 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ * (G₀.batchEnc (us.take T) : ℝ) +
        44 * (((L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ) * (T : ℝ)) := by
    have hsub := add_le_add (add_le_add (add_le_add (add_le_add hL1_Enc hUH_T) hD_T) hSum_F0_extra) hSum_Fpos_extra
    rw [← hsum_decomp] at hsub
    exact le_trans hsub (le_of_eq (by ring))
  have hEnc_T_bnd : 44 * (((L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ) * (T : ℝ)) ≤
      44 * (((L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ) * (G₀.batchEnc (us.take T) : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT_enc (by positivity)) (by norm_num)
  calc ∑ k ∈ Finset.range T, f k
      ≤ 1 * (L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ * (G₀.batchEnc (us.take T) : ℝ) +
          44 * (((L : ℝ) * (q : ℝ) * K1 * E_L * deg1 * Λ) * (G₀.batchEnc (us.take T) : ℝ)) :=
        add_le_add le_rfl hEnc_T_bnd |>.trans' (by linarith only [hsum_T_bnd])
    _ = 45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
          (G₀.batchEnc (us.take T) : ℝ) := by
        dsimp only [K1, deg1]; ring

end

end MinCostFlow.DynSpanner
