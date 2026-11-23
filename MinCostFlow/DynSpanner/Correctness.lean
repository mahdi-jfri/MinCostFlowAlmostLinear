module

public import MinCostFlow.DynSpanner.StepTransition

import Mathlib.Tactic.Linarith

/-!
# Correctness and re-embedding guarantees of the dynamic spanner algorithm

This file proves the main structural, approximation, and re-embedding guarantees for Algorithm 6
(adapted to Theorem 8.1):

* `lemma_5_6` ([chen2022maximum] arXiv:2203.00671v2, Section 5.1, Lemma 5.6):
  valid embeddings `Π_{≤ j} : G^{(k)} → H_{≤ j}^{(k)}` at all phases divisible by `B_j = q^{L-j}`,
  and valid total embedding `Π_{G → H} : G^{(k)} → H^{(k)}` at all steps `k`.
* `claim_5_8` ([chen2022maximum] Section 5.1, Claim 5.8, tightened to `3^i · γ_ℓ^{i+1}`):
  `length(Π_{≤ i}) ≤ 3^i · γ_ℓ^{i + 1}` at all steps `k` and levels `i`.
* `claim_5_7` ([chen2022maximum] Section 5.1, Claim 5.7, tightened uniformly for `γ_ℓ, γ_c ≥ 1`):
  `vcong(Π_{≤ i}) ≤ 3^{(i+1)(i+2)/2} · γ_ℓ^{i(i+1)/2} · γ_c^{i+1} · Δ_max(G^{(0)})`.
* `reembed_step_spec` and `reembed_batch_spec` (Theorem 8.2, Item 3):
  for any single step or batch `U` with re-embedding set `D`, every surviving edge `e ∉ D`
  satisfies `(Π')⁻¹(e) ⊆ Π⁻¹(e)`.
* `update_batch_spec` and `batchTrace_spec`: exact correspondence between the batch driver `update`
  on a sequence of valid batches and the flat single-update trace.
-/

namespace MinCostFlow.DynSpanner

section CorrectnessMain

@[expose] public section

private theorem piLe_eq_at_lastRebuild {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k ≤ us.length) (i : Fin (L + 1)) :
    let r := lastRebuild q L i.1 k
    ∀ e ∈ (G₀.applyBatch (us.take k)).E,
      piLe (runState (L := L) G₀ q sparsify us k) i.1 e =
      piLe (runState (L := L) G₀ q sparsify us r) i.1 e := by
  intro r e heGk
  have hr_le : r ≤ k := lastRebuild_le q L i.1 k
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk).1
  have hr_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r (le_trans hr_le hk)).1
  have htake_k : us.take k = us.take r ++ (us.take k).drop r := by
    have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le]
    rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
  obtain ⟨hBV_k, hds_k, _⟩ := batchIsValid_take us G₀ k hBV hds
  rw [htake_k, batchIsValid_append] at hBV_k
  obtain ⟨hBV_r, hBV_d⟩ := hBV_k
  have hds_r : ∀ u ∈ us.take r, isDelOrSplit u := fun u hu =>
    hds_k u (by rw [htake_k]; exact List.mem_append_left _ hu)
  have hds_d : ∀ u ∈ (us.take k).drop r, isDelOrSplit u := fun u hu =>
    hds_k u (by rw [htake_k]; exact List.mem_append_right _ hu)
  have hVGr : (G₀.applyBatch (us.take r)).IsValid :=
    (batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_r hds_r).1
  have heGr : e ∈ (G₀.applyBatch (us.take r)).E := by
    have hsub := (batch_delOrSplit_invariants ((us.take k).drop r) (G₀.applyBatch (us.take r))
      hVGr hBV_d hds_d).2.1
    rw [← applyBatch_append, ← htake_k] at hsub
    exact hsub heGk
  have hm_eq : ∀ m : Fin (L + 1), m.1 ≤ i.1 →
      lastRebuild q L m.1 r = lastRebuild q L m.1 k := fun m hm => by
    have hm_le : lastRebuild q L m.1 k ≤ r := lastRebuild_mono_level hq hm (Nat.le_of_lt_succ i.2)
    exact lastRebuild_idempotent_le hq hm_le hr_le
  have h0k : e ∈ (runState (L := L) G₀ q sparsify us k).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
    rw [hk_inv.inDom0]; exact heGk
  have h0r : e ∈ (runState (L := L) G₀ q sparsify us r).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
    rw [hr_inv.inDom0]; exact heGr
  obtain ⟨m₁, hm₁_lt, hm₁_dom, hm₁_none, heq₁⟩ := piLtFrom_eq
    (runState (L := L) G₀ q sparsify us k).Pi_level
    (runState (L := L) G₀ q sparsify us k).inDom (Nat.succ_pos i.1) h0k
  obtain ⟨m₂, hm₂_lt, hm₂_dom, hm₂_none, heq₂⟩ := piLtFrom_eq
    (runState (L := L) G₀ q sparsify us r).Pi_level
    (runState (L := L) G₀ q sparsify us r).inDom (Nat.succ_pos i.1) h0r
  have hcongr : ∀ m : Fin (L + 1), m.1 < i.1 + 1 →
      (e ∈ (runState (L := L) G₀ q sparsify us k).inDom m ↔
       e ∈ (runState (L := L) G₀ q sparsify us r).inDom m) := fun m hm => by
    rw [hk_inv.inDom_eq m, hr_inv.inDom_eq m, hm_eq m (Nat.lt_succ_iff.mp hm)]
    simp only [Finset.mem_inter]
    tauto
  have hm_eq_idx : m₁ = m₂ := by
    by_contra hne
    rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · exact hm₁_none m₂ hlt hm₂_lt ((hcongr m₂ hm₂_lt).mpr hm₂_dom)
    · exact hm₂_none m₁ hlt hm₁_lt ((hcongr m₁ hm₁_lt).mp hm₁_dom)
  change piLtFrom _ _ (i.1 + 1) e = piLtFrom _ _ (i.1 + 1) e
  rw [heq₁, heq₂, hm_eq_idx, hk_inv.Pi_level_eq m₂, hr_inv.Pi_level_eq m₂,
    hm_eq m₂ (Nat.lt_succ_iff.mp hm₂_lt)]

/-- **Lemma 5.6** ([chen2022maximum] arXiv:2203.00671v2, Section 5.1):
At every step `k` divisible by `phasePeriod q L i = q^{L - i}`, `Π_{≤ i}` is a valid embedding
from `G^{(k)}` into `H_{≤ i}^{(k)}`. In particular, for all `k`, `Π_{G → H} = Π_{≤ L}` embeds
`G^{(k)}` into the union spanner `H^{(k)}`. -/
theorem lemma_5_6 {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k ≤ us.length) :
    (∀ i : Fin (L + 1), phasePeriod q L i.1 ∣ k →
      Embedding.IsEmbedding (piLe (runState (L := L) G₀ q sparsify us k) i.1)
        (G₀.applyBatch (us.take k))
        (unionGraphLt (G₀.applyBatch (us.take k))
          (runState (L := L) G₀ q sparsify us k).H_level (i.1 + 1))) ∧
    Embedding.IsEmbedding (piTotal (runState (L := L) G₀ q sparsify us k))
      (G₀.applyBatch (us.take k))
      (runState (L := L) G₀ q sparsify us k).H := by
  have hinv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk).1
  refine ⟨fun i hdvd => hinv.emb_at i ((chooseLevel_le_iff_dvd hq (Nat.le_of_lt_succ i.2)).mpr hdvd), ?_⟩
  have hL_emb := hinv.emb_at ⟨L, Nat.lt_succ_self L⟩ (chooseLevel_le L q k)
  dsimp only at hL_emb
  exact isEmbedding_graph_congr
    (H₁ := unionGraphLt (G₀.applyBatch (us.take k)) (runState (L := L) G₀ q sparsify us k).H_level (L + 1))
    (H₂ := (runState (L := L) G₀ q sparsify us k).H)
    hinv.H_V.symm hinv.H_E.symm
    (fun e he => (hinv.H_sub.2.2 e (hinv.H_E ▸ he)).1.symm)
    (fun e he => (hinv.H_sub.2.2 e (hinv.H_E ▸ he)).2.symm)
    hL_emb

/-- **Claim 5.8** ([chen2022maximum] Section 5.1, tightened to `3^i · γ_ℓ^{i + 1}` uniformly
for all `γ_ℓ ≥ 1`): at every step `k` and every level `i`, `length(Π_{≤ i}) ≤ 3^i · γ_ℓ^{i + 1}`. -/
theorem claim_5_8 {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k ≤ us.length) (i : Fin (L + 1)) :
    (Embedding.length (piLe (runState (L := L) G₀ q sparsify us k) i.1)
      (G₀.applyBatch (us.take k)) : ℝ) ≤ lenBound P.γ_ℓ i.1 := by
  set r := lastRebuild q L i.1 k
  have hr_le : r ≤ k := lastRebuild_le q L i.1 k
  have hr_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r (le_trans hr_le hk)).1
  have hr_ch : chooseLevel L q r ≤ i.1 := lastRebuild_chooseLevel_le hq (Nat.le_of_lt_succ i.2)
  have hpi_eq := piLe_eq_at_lastRebuild hVG₀ hL hq hGm₀ hSpec hBV hds hk i
  rw [length_congr_eq hpi_eq]
  have htake_k : us.take k = us.take r ++ (us.take k).drop r := by
    have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le]
    rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
  obtain ⟨hBV_k, hds_k, _⟩ := batchIsValid_take us G₀ k hBV hds
  rw [htake_k, batchIsValid_append] at hBV_k
  have hds_r : ∀ u ∈ us.take r, isDelOrSplit u := fun u hu =>
    hds_k u (by rw [htake_k]; exact List.mem_append_left _ hu)
  have hds_d : ∀ u ∈ (us.take k).drop r, isDelOrSplit u := fun u hu =>
    hds_k u (by rw [htake_k]; exact List.mem_append_right _ hu)
  have hVGr := (batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_k.1 hds_r).1
  have hSub := (batch_delOrSplit_invariants ((us.take k).drop r) (G₀.applyBatch (us.take r))
    hVGr hBV_k.2 hds_d).2.1
  rw [← applyBatch_append, ← htake_k] at hSub
  have hsup : Embedding.length (piLe (runState (L := L) G₀ q sparsify us r) i.1)
      (G₀.applyBatch (us.take k)) ≤
      Embedding.length (piLe (runState (L := L) G₀ q sparsify us r) i.1)
      (G₀.applyBatch (us.take r)) := by
    unfold Embedding.length
    rw [Finset.sup_le_iff]
    intro e he
    exact Finset.le_sup (f := fun e => (piLe (runState (L := L) G₀ q sparsify us r) i.1 e).length)
      (hSub he)
  exact le_trans (Nat.cast_le.mpr hsup) (hr_inv.len_at i hr_ch)

/-- **Claim 5.7** ([chen2022maximum] Section 5.1, tightened uniformly for all `γ_ℓ, γ_c ≥ 1`):
At every step `k` divisible by `q^{L - i}`, `vcong(Π_{≤ i}) ≤ 3^{(i+1)(i+2)/2} γ_ℓ^{i(i+1)/2} γ_c^{i+1} Δ_max(G₀)`.
In particular, at all steps `k`, `vcong(Π_{G → H}) ≤ 3^{(L+1)(L+2)/2} γ_ℓ^{L(L+1)/2} γ_c^{L+1} Δ_max(G₀)`. -/
theorem claim_5_7 {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k ≤ us.length) :
    (∀ i : Fin (L + 1), phasePeriod q L i.1 ∣ k →
      Embedding.vcong (piLe (runState (L := L) G₀ q sparsify us k) i.1)
        (G₀.applyBatch (us.take k))
        (unionGraphLt (G₀.applyBatch (us.take k))
          (runState (L := L) G₀ q sparsify us k).H_level (i.1 + 1)) (fun _ => 1) ≤
        vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1) ∧
    Embedding.vcong (piTotal (runState (L := L) G₀ q sparsify us k))
      (G₀.applyBatch (us.take k))
      (runState (L := L) G₀ q sparsify us k).H (fun _ => 1) ≤
      vcongBound P.γ_c P.γ_ℓ G₀.maxDeg L := by
  have hinv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk).1
  refine ⟨fun i hdvd => hinv.vcong_at i ((chooseLevel_le_iff_dvd hq (Nat.le_of_lt_succ i.2)).mpr hdvd), ?_⟩
  obtain ⟨hBV_k, hds_k, _⟩ := batchIsValid_take us G₀ k hBV hds
  have hVGk := (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k).1
  have hUg_valid : (unionGraphLt (G₀.applyBatch (us.take k))
      (runState (L := L) G₀ q sparsify us k).H_level (L + 1)).IsValid := fun e he =>
    hVGk e (hinv.H_sub.2.1 (hinv.H_E ▸ he))
  have hL_emb := hinv.emb_at ⟨L, Nat.lt_succ_self L⟩ (chooseLevel_le L q k)
  dsimp only at hL_emb
  have hvc_eq := vcong_graph_congr hVGk hUg_valid hinv.H_V.symm hinv.H_E.symm
    (fun e he => (hinv.H_sub.2.2 e (hinv.H_E ▸ he)).1.symm)
    (fun e he => (hinv.H_sub.2.2 e (hinv.H_E ▸ he)).2.symm) hL_emb
  change Embedding.vcong (piLe (runState (L := L) G₀ q sparsify us k) L)
    (G₀.applyBatch (us.take k)) (runState (L := L) G₀ q sparsify us k).H (fun _ => 1) ≤
    vcongBound P.γ_c P.γ_ℓ G₀.maxDeg L
  rw [← hvc_eq]
  exact hinv.vcong_at ⟨L, Nat.lt_succ_self L⟩ (chooseLevel_le L q k)

end

end CorrectnessMain

section Reembedding

@[expose] public section

private theorem dropLast_walkVertices_eq_of_not_mem_allTouched :
    ∀ (p : List (ℕ × Bool)) {G_s G' : MGraph} {delta : List Update} {a_s a_k b_k : ℕ},
      G_s.IsValid → G_s.BatchIsValid delta → (∀ u ∈ delta, isDelOrSplit u) →
      G' = G_s.applyBatch delta → G'.IsWalk a_k b_k p →
      a_k ∈ G'.V → batchAnc delta a_k = a_s →
      (∀ z ∈ (G'.walkVertices a_k p).dropLast, z ∉ allTouched G_s delta) →
      (G_s.walkVertices a_s p).dropLast = (G'.walkVertices a_k p).dropLast
  | [], _, _, _, a_s, a_k, _, _, _, _, _, _, _, _, _ => by
    simp [MGraph.walkVertices]
  | x :: xs, G_s, G', delta, a_s, a_k, b_k, hV_s, hBV_d, hds_d, hG', hw, ha_k, hanc, hdrop => by
    cases hw with
    | cons hxG' hsrc hrest =>
      have ha_not : a_k ∉ allTouched G_s delta := by
        apply hdrop a_k
        simp [MGraph.walkVertices, List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
      have hnt := not_mem_allTouched_invariants delta G_s hV_s hBV_d hds_d a_k ha_not
      have ha_eq : a_k = a_s := by
        have hV1 : a_k ∈ (G_s.applyBatch delta).V := hG' ▸ ha_k
        rw [← hanc, hnt.2.1 (hnt.1 hV1)]
      cases xs with
      | nil =>
        simp [MGraph.walkVertices, ha_eq]
      | cons y ys =>
        have hinv := batch_delOrSplit_invariants delta G_s hV_s hBV_d hds_d
        have hVG' : G'.IsValid := hG' ▸ hinv.1
        have hxGs : x.1 ∈ G_s.E := hinv.2.1 (hG' ▸ hxG')
        have hdst_V : G'.dst x ∈ G'.V := by
          cases xb : x.2
          · simp [MGraph.dst, xb]; exact (hVG' x.1 hxG').1
          · simp [MGraph.dst, xb]; exact (hVG' x.1 hxG').2
        have hdst_anc : batchAnc delta (G'.dst x) = G_s.dst x := by
          have hends := hinv.2.2.2.2.2.2 x.1 hxGs
          cases xb : x.2
          · simp only [MGraph.dst, xb, Bool.false_eq_true, ↓reduceIte, hG', hends.1]
          · simp only [MGraph.dst, xb, ↓reduceIte, hG', hends.2]
        have hdrop_rest : ∀ z ∈ (G'.walkVertices (G'.dst x) (y :: ys)).dropLast,
            z ∉ allTouched G_s delta := fun z hz => by
          apply hdrop z
          simp only [MGraph.walkVertices, List.map_cons,
            List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.mem_cons] at hz ⊢
          right; exact hz
        have ih := dropLast_walkVertices_eq_of_not_mem_allTouched (y :: ys)
          hV_s hBV_d hds_d hG' hrest hdst_V hdst_anc hdrop_rest
        simp only [MGraph.walkVertices, List.map_cons,
          List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)] at ih ⊢
        rw [ha_eq]
        congr 1

theorem prefix_suffix_preserve_backward {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (j : ℕ) (hj_pos : 0 < j) (hj_le : j ≤ L)
    (hj_eq : chooseLevel L q (k + 1) = j)
    {eG : ℕ} (heG' : eG ∈ (G₀.applyBatch (us.take (k + 1))).E)
    {p₁ q₂ : List (ℕ × Bool)}
    (hp₁_pref : p₁ <+: piLe (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) (k + 1))) (j - 1) eG)
    (hq₂_pref : q₂ <+: walkRev (piLe (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) (k + 1))) (j - 1) eG))
    (hp₁_walk : (G₀.applyBatch (us.take (k + 1))).IsWalk ((G₀.applyBatch (us.take (k + 1))).tail eG)
      (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
        (fun i => ((runState (L := L) G₀ q sparsify us k).H_level i).applyBatch
          (restrictUpdate (us[k]'hk) ((runState (L := L) G₀ q sparsify us k).H_level i))) j)
        ((G₀.applyBatch (us.take (k + 1))).tail eG)
        (piLe (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) (k + 1))) (j - 1) eG)
        (allTouched (G₀.applyBatch (us.take (lastRebuild q L (j - 1) (k + 1))))
          ((us.take (k + 1)).drop (lastRebuild q L (j - 1) (k + 1))))).1 p₁)
    (hq₂_walk : (G₀.applyBatch (us.take (k + 1))).IsWalk ((G₀.applyBatch (us.take (k + 1))).head eG)
      (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
        (fun i => ((runState (L := L) G₀ q sparsify us k).H_level i).applyBatch
          (restrictUpdate (us[k]'hk) ((runState (L := L) G₀ q sparsify us k).H_level i))) j)
        ((G₀.applyBatch (us.take (k + 1))).head eG)
        (walkRev (piLe (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) (k + 1))) (j - 1) eG))
        (allTouched (G₀.applyBatch (us.take (lastRebuild q L (j - 1) (k + 1))))
          ((us.take (k + 1)).drop (lastRebuild q L (j - 1) (k + 1))))).1 q₂)
    (hp₁_drop : ∀ z ∈ ((G₀.applyBatch (us.take (k + 1))).walkVertices
      ((G₀.applyBatch (us.take (k + 1))).tail eG) p₁).dropLast,
      z ∉ allTouched (G₀.applyBatch (us.take (lastRebuild q L (j - 1) (k + 1))))
        ((us.take (k + 1)).drop (lastRebuild q L (j - 1) (k + 1))))
    (hq₂_drop : ∀ z ∈ ((G₀.applyBatch (us.take (k + 1))).walkVertices
      ((G₀.applyBatch (us.take (k + 1))).head eG) q₂).dropLast,
      z ∉ allTouched (G₀.applyBatch (us.take (lastRebuild q L (j - 1) (k + 1))))
        ((us.take (k + 1)).drop (lastRebuild q L (j - 1) (k + 1)))) :
    let r := lastRebuild q L (j - 1) (k + 1)
    ∀ s, r ≤ s → s ≤ k →
      ∀ i : Fin (L + 1), j - 1 ≤ i.1 →
        p₁ <+: piLe (runState (L := L) G₀ q sparsify us s) i.1 eG ∧
        q₂ <+: walkRev (piLe (runState (L := L) G₀ q sparsify us s) i.1 eG) := by
  intro r s hrs hsk
  have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ (k + 1) := by
    rw [← hj_eq]; exact not_dvd_of_lt_chooseLevel (Nat.sub_lt (hj_eq ▸ hj_pos) Nat.one_pos)
  have hr_eq_k : r = lastRebuild q L (j - 1) k := lastRebuild_eq_of_not_dvd hr_not_dvd
  have hr_le_k : r ≤ k := hr_eq_k ▸ lastRebuild_le q L (j - 1) k
  -- Prove by induction on `d = s - r`!
  obtain ⟨d, hd⟩ : ∃ d, s = r + d := ⟨s - r, (Nat.add_sub_cancel' hrs).symm⟩
  subst hd
  clear hrs
  revert hsk
  induction d with
  | zero =>
    intro _ i hi
    have hr_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r (Nat.le_of_lt (Nat.lt_of_le_of_lt hr_le_k hk))).1
    have hr_ch : chooseLevel L q r ≤ j - 1 :=
      lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
    have hsub1 : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
    have hGr_E : eG ∈ (G₀.applyBatch (us.take r)).E := by
      obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
      have htk : us.take (k + 1) = us.take r ++ (us.take (k + 1)).drop r := by
        have h1 : (us.take (k + 1)).take r = us.take r := by
          rw [List.take_take, min_eq_left (Nat.le_succ_of_le hr_le_k)]
        rw [← h1]; exact (List.take_append_drop r (us.take (k + 1))).symm
      rw [htk, batchIsValid_append] at hBV_k1
      have hds_d : ∀ u ∈ (us.take (k + 1)).drop r, isDelOrSplit u := fun u hu =>
        hds_k1 u (by rw [htk]; exact List.mem_append_right _ hu)
      have hds_r : ∀ u ∈ us.take r, isDelOrSplit u := fun u hu =>
        hds_k1 u (by rw [htk]; exact List.mem_append_left _ hu)
      have hVr := (batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_k1.1 hds_r).1
      have hSub := (batch_delOrSplit_invariants ((us.take (k + 1)).drop r)
        (G₀.applyBatch (us.take r)) hVr hBV_k1.2 hds_d).2.1
      rw [← applyBatch_append, ← htk] at hSub
      exact hSub heG'
    have he0 : eG ∈ (runState (L := L) G₀ q sparsify us (r + 0)).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
      simpa [Nat.add_zero] using (hr_inv.inDom0 ▸ hGr_E)
    have hpi_eq : piLe (runState (L := L) G₀ q sparsify us (r + 0)) i.1 eG =
        piLe (runState (L := L) G₀ q sparsify us r) (j - 1) eG := by
      refine piLtFrom_eq_of_lt _ _ (Nat.succ_pos (j - 1)) (Nat.succ_le_succ hi) he0 ?_
      intro m hm1 _
      have hm_not : chooseLevel L q (lastRebuild q L m.1 r) < m.1 := by
        have hlr : lastRebuild q L m.1 r = r := by
          have hdvd_B : phasePeriod q L m.1 ∣ phasePeriod q L (j - 1) :=
            phasePeriod_dvd_of_le (Nat.le_trans (Nat.le_succ _) hm1) (Nat.le_of_lt_succ m.2)
          have hdvd_r : phasePeriod q L m.1 ∣ r :=
            dvd_trans hdvd_B (lastRebuild_dvd q L (j - 1) (k + 1))
          exact lastRebuild_eq_self_of_dvd hdvd_r
        rw [hlr]
        exact lt_of_le_of_lt hr_ch (Nat.lt_of_succ_le hm1)
      simp only [Nat.add_zero]
      rw [(hr_inv.inactive m hm_not).1]
      exact Finset.notMem_empty eG
    rw [hpi_eq]
    exact ⟨hp₁_pref, hq₂_pref⟩
  | succ d ih =>
    intro hle_k i hi
    have hd_le_k : r + d ≤ k := Nat.le_of_succ_le hle_k
    have ih_d := ih hd_le_k
    have hstep_pos : r < r + d + 1 := by omega
    have hch_m : j ≤ chooseLevel L q (r + d + 1) := by
      have h1 := lt_chooseLevel_between_lastRebuild hq (le_trans (Nat.sub_le j 1) hj_le)
        hstep_pos (Nat.succ_le_succ hd_le_k)
      omega
    set m := chooseLevel L q (r + d + 1)
    have hm_ne : ¬ m = 0 := Nat.ne_of_gt (lt_of_lt_of_le hj_pos hch_m)
    have hm_le : m ≤ L := chooseLevel_le L q (r + d + 1)
    have hlt_len : r + d < us.length := lt_of_le_of_lt hd_le_k hk
    have hu_some : us[r + d]? = some (us[r + d]'hlt_len) := List.getElem?_eq_getElem hlt_len
    set u_s := us[r + d]'hlt_len
    have hprev_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (r + d) (Nat.le_of_lt hlt_len)).1
    have hnext_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (r + d + 1) (Nat.succ_le_of_lt hlt_len)).1
    have hGrd1_E : eG ∈ (G₀.applyBatch (us.take (r + d + 1))).E := by
      obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
      have htk : us.take (k + 1) = us.take (r + d + 1) ++ (us.take (k + 1)).drop (r + d + 1) := by
        have h1 : (us.take (k + 1)).take (r + d + 1) = us.take (r + d + 1) := by
          rw [List.take_take, min_eq_left (Nat.succ_le_succ hd_le_k)]
        rw [← h1]; exact (List.take_append_drop (r + d + 1) (us.take (k + 1))).symm
      rw [htk, batchIsValid_append] at hBV_k1
      have hds_1 : ∀ u ∈ us.take (r + d + 1), isDelOrSplit u := fun u hu =>
        hds_k1 u (by rw [htk]; exact List.mem_append_left _ hu)
      have hds_2 : ∀ u ∈ (us.take (k + 1)).drop (r + d + 1), isDelOrSplit u := fun u hu =>
        hds_k1 u (by rw [htk]; exact List.mem_append_right _ hu)
      have hVs := (batch_delOrSplit_invariants (us.take (r + d + 1)) G₀ hVG₀ hBV_k1.1 hds_1).1
      have hSub := (batch_delOrSplit_invariants ((us.take (k + 1)).drop (r + d + 1))
        (G₀.applyBatch (us.take (r + d + 1))) hVs hBV_k1.2 hds_2).2.1
      rw [← applyBatch_append, ← htk] at hSub
      exact hSub heG'
    have hstep_ch : chooseLevel L (runState (L := L) G₀ q sparsify us (r + d)).q
        ((runState (L := L) G₀ q sparsify us (r + d)).t + 1) = m := by
      rw [hprev_inv.q_eq, hprev_inv.t_eq]
    -- Notice: if `i.1 < m`, `piLe (st (r + d + 1)) i.1 eG = piLe (st (r + d)) i.1 eG`!
    by_cases him : i.1 < m
    · have hpi_same : piLe (runState (L := L) G₀ q sparsify us (r + d + 1)) i.1 eG =
          piLe (runState (L := L) G₀ q sparsify us (r + d)) i.1 eG := by
        have hst1 : runState (L := L) G₀ q sparsify us (r + d + 1) =
            (step (runState (L := L) G₀ q sparsify us (r + d)) u_s sparsify).state := by
          simp [runState, hu_some, u_s]
        have h0_1 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom ⟨0, Nat.zero_lt_succ L⟩ :=
          hnext_inv.inDom0 ▸ hGrd1_E
        have h0_0 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d)).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
          rw [hprev_inv.inDom0]
          have htk' : us.take (r + d + 1) = us.take (r + d) ++ [u_s] := take_succ_of_getElem? hu_some
          obtain ⟨_, _, hu_v⟩ := batchIsValid_take us G₀ (r + d) hBV hds
          exact (E_applyUpdate_subset (hu_v u_s hu_some).2) (by
            simpa [htk', applyBatch_append, MGraph.applyBatch] using hGrd1_E)
        have hcongr_in : ∀ l : Fin (L + 1), l.1 < i.1 + 1 →
            (eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom l ↔
             eG ∈ (runState (L := L) G₀ q sparsify us (r + d)).inDom l) := fun l hl => by
          have hlm : l.1 < m := Nat.lt_of_lt_of_le hl him
          have hst1' : (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom l =
              (runState (L := L) G₀ q sparsify us (r + d)).inDom l ∩
              (G₀.applyBatch (us.take (r + d + 1))).E := by
            rw [hst1]; dsimp only [step]
            simp only [hstep_ch, hm_ne, ↓reduceDIte]
            simp only [hlm, ↓reduceIte]
            have htk' : us.take (r + d + 1) = us.take (r + d) ++ [u_s] := take_succ_of_getElem? hu_some
            rw [hprev_inv.G_eq, htk', applyBatch_append, MGraph.applyBatch]
            rfl
          rw [hst1']
          simp [hGrd1_E]
        obtain ⟨l₁, hl₁, hl₁d, hl₁n, heq₁⟩ := piLtFrom_eq _ _ (Nat.succ_pos i.1) h0_1
        obtain ⟨l₂, hl₂, hl₂d, hl₂n, heq₂⟩ := piLtFrom_eq _ _ (Nat.succ_pos i.1) h0_0
        have hl_eq : l₁ = l₂ := by
          by_contra hne
          rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
          · exact hl₁n l₂ hlt hl₂ ((hcongr_in l₂ hl₂).mpr hl₂d)
          · exact hl₂n l₁ hlt hl₁ ((hcongr_in l₁ hl₁).mp hl₁d)
        have hPi_same : (runState (L := L) G₀ q sparsify us (r + d + 1)).Pi_level l₂ =
            (runState (L := L) G₀ q sparsify us (r + d)).Pi_level l₂ := by
          rw [hst1]; dsimp only [step]
          simp only [hstep_ch, hm_ne, ↓reduceDIte]
          simp [Nat.lt_of_lt_of_le hl₂ him]
        change piLtFrom _ _ (i.1 + 1) eG = piLtFrom _ _ (i.1 + 1) eG
        rw [heq₁, heq₂, hl_eq, hPi_same]
      rw [← Nat.add_assoc, hpi_same]
      exact ih_d i hi
    · -- Now `m ≤ i.1`! Let `pi_mid := piLe (st (r + d)) (m - 1)` which has `p₁ <+: pi_mid eG` and `q₂ <+: walkRev (pi_mid eG)` by `ih_d`!
      have hm_ge_i : j - 1 ≤ m - 1 := by omega
      have ih_mid := ih_d ⟨m - 1, by omega⟩ hm_ge_i
      have hst1 : runState (L := L) G₀ q sparsify us (r + d + 1) =
          (step (runState (L := L) G₀ q sparsify us (r + d)) u_s sparsify).state := by
        simp [runState, hu_some, u_s]
      -- Show `piLe (st (r + d + 1)) i.1 eG` is either `pi_mid eG` or `Pi_m eG`:
      have h_pi_mid_eq : ∀ e' ∈ (G₀.applyBatch (us.take (r + d + 1))).E,
          piLtFrom (runState (L := L) G₀ q sparsify us (r + d)).Pi_level
            (fun l => (runState (L := L) G₀ q sparsify us (r + d)).inDom l ∩
              (G₀.applyBatch (us.take (r + d + 1))).E) m e' =
          piLe (runState (L := L) G₀ q sparsify us (r + d)) (m - 1) e' := fun e' he' => by
        have hm_pos : 0 < m := lt_of_lt_of_le hj_pos hch_m
        have hsub1 : (m - 1) + 1 = m := Nat.sub_add_cancel hm_pos
        change _ = piLtFrom _ _ ((m - 1) + 1) e'
        rw [hsub1]
        have h0_0 : e' ∈ (runState (L := L) G₀ q sparsify us (r + d)).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
          rw [hprev_inv.inDom0]
          have htk' : us.take (r + d + 1) = us.take (r + d) ++ [u_s] := take_succ_of_getElem? hu_some
          obtain ⟨_, _, hu_v⟩ := batchIsValid_take us G₀ (r + d) hBV hds
          exact (E_applyUpdate_subset (hu_v u_s hu_some).2) (by
            simpa [htk', applyBatch_append, MGraph.applyBatch] using he')
        exact piLtFrom_congr_inDom _ fun l hl => by
          simp only [Finset.mem_inter, and_iff_left_iff_imp]
          intro _; exact he'
      have h_pi_1 : piLe (runState (L := L) G₀ q sparsify us (r + d + 1)) i.1 eG =
          piLe (runState (L := L) G₀ q sparsify us (r + d + 1)) m eG := by
        have he0 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom ⟨0, Nat.zero_lt_succ L⟩ :=
          hnext_inv.inDom0 ▸ hGrd1_E
        refine piLtFrom_eq_of_lt _ _ (Nat.succ_pos m) (Nat.succ_le_succ (Nat.le_of_not_lt him)) he0 ?_
        intro l hl1 _
        rw [hst1]; dsimp only [step]
        simp only [hstep_ch, hm_ne, ↓reduceDIte]
        have hlt_m : ¬ l.1 < m := Nat.not_lt.mpr (Nat.le_of_succ_le hl1)
        have hne_m : l.1 ≠ m := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hl1)
        simp [hlt_m, hne_m]
      rw [← Nat.add_assoc, h_pi_1]
      set G_s := G₀.applyBatch (us.take (r + d + 1))
      set G_k1 := G₀.applyBatch (us.take (k + 1))
      have htk' : us.take (r + d + 1) = us.take (r + d) ++ [u_s] := take_succ_of_getElem? hu_some
      have hGs_eq : G_s = (runState (L := L) G₀ q sparsify us (r + d)).G.applyUpdate u_s := by
        simp [G_s, hprev_inv.G_eq, htk', MGraph.applyBatch]
      set H_mid_s : Fin (L + 1) → MGraph := fun l =>
        ((runState (L := L) G₀ q sparsify us (r + d)).H_level l).applyBatch
          (restrictUpdate u_s ((runState (L := L) G₀ q sparsify us (r + d)).H_level l))
      set H_lt_s := unionGraphLt G_s H_mid_s m
      set inDom_mid_s : Fin (L + 1) → Finset ℕ := fun l =>
        (runState (L := L) G₀ q sparsify us (r + d)).inDom l ∩ G_s.E
      set piLt_mid_s := piLtFrom (runState (L := L) G₀ q sparsify us (r + d)).Pi_level inDom_mid_s m
      set S_prev_s := (runState (L := L) G₀ q sparsify us (r + d)).S_level ⟨m - 1, by omega⟩ ∪
        touchedVertices (runState (L := L) G₀ q sparsify us (r + d)).G u_s
      set E_aff_s := affectedEdges G_s H_lt_s piLt_mid_s S_prev_s
      by_cases heAff_s : eG ∈ E_aff_s
      · -- Case A: `eG ∈ E_aff_s`, so `piLe (st (r + d + 1)) m eG = p₁_s ++ embMid_s eG ++ walkRev q₂_s`:
        let out_s := if E_aff_s.Nonempty then
          sparsify (buildAuxHost G_s H_lt_s E_aff_s)
            (buildProjGraph G_s H_lt_s piLt_mid_s S_prev_s E_aff_s)
            (projWalk G_s H_lt_s piLt_mid_s S_prev_s)
          else ⟨buildProjGraph G_s H_lt_s piLt_mid_s S_prev_s E_aff_s, idEmb, 0⟩
        have hval_m : piLe (runState (L := L) G₀ q sparsify us (r + d + 1)) m eG =
            reembedWalk G_s H_lt_s piLt_mid_s
              (Embedding.comp (projWalk G_s H_lt_s piLt_mid_s S_prev_s)
                (fun e => shortcutWalk out_s.Jtilde
                  ((buildProjGraph G_s H_lt_s piLt_mid_s S_prev_s E_aff_s).tail e)
                  (out_s.emb e))) S_prev_s eG := by
          have he0 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom
              ⟨0, Nat.zero_lt_succ L⟩ := hnext_inv.inDom0 ▸ hGrd1_E
          have hm_dom : eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom
              ⟨m, Nat.lt_succ_of_le hm_le⟩ := by
            rw [hst1]; dsimp only [step]
            simp only [hstep_ch, hm_ne, ↓reduceDIte]
            simpa [← hGs_eq, E_aff_s, H_lt_s, H_mid_s, piLt_mid_s, inDom_mid_s, S_prev_s] using heAff_s
          obtain ⟨l, hlm, _hld, hln, heql⟩ := piLtFrom_eq _ _ (Nat.succ_pos m) he0
          have hl_eq : l.1 = m := by
            apply le_antisymm (Nat.lt_succ_iff.mp hlm)
            by_contra hlt
            exact hln ⟨m, Nat.lt_succ_of_le hm_le⟩ (Nat.lt_of_not_le hlt) (Nat.lt_succ_self m) hm_dom
          change piLtFrom _ _ (m + 1) eG = _
          rw [heql, show l = ⟨m, Nat.lt_succ_of_le hm_le⟩ from Fin.ext hl_eq]
          rw [hst1]; dsimp only [step]
          simp only [hstep_ch, hm_ne, ↓reduceDIte]
          simp only [lt_irrefl, ↓reduceIte, ← hGs_eq, out_s, E_aff_s, S_prev_s, piLt_mid_s,
            inDom_mid_s, H_lt_s, H_mid_s]
        rw [hval_m]
        -- Show `S_prev_s ⊆ S_prev_{k+1}`!
        have hS_sub : S_prev_s ⊆ allTouched (G₀.applyBatch (us.take r)) ((us.take (k + 1)).drop r) := by
          set rm := lastRebuild q L (m - 1) (r + d)
          have hrm_ge_r : r ≤ rm := by
            have hdvd_B : phasePeriod q L (m - 1) ∣ phasePeriod q L (j - 1) :=
              phasePeriod_dvd_of_le (by omega) (by omega)
            have hdvd_r : phasePeriod q L (m - 1) ∣ r :=
              dvd_trans hdvd_B (lastRebuild_dvd q L (j - 1) (k + 1))
            obtain ⟨q1, hq1⟩ := hdvd_r
            have hBpos : 0 < phasePeriod q L (m - 1) := phasePeriod_pos hq L (m - 1)
            have hq1_le : q1 ≤ (r + d) / phasePeriod q L (m - 1) := by
              rw [Nat.le_div_iff_mul_le hBpos]; linarith [hq1, show r ≤ r + d by omega]
            calc r = q1 * phasePeriod q L (m - 1) := by linarith [hq1]
              _ ≤ ((r + d) / phasePeriod q L (m - 1)) * phasePeriod q L (m - 1) :=
                Nat.mul_le_mul_right _ hq1_le
          have hrm_le : rm ≤ r + d := lastRebuild_le q L (m - 1) (r + d)
          have hSprev_eq : S_prev_s =
              allTouched (G₀.applyBatch (us.take rm)) ((us.take (r + d + 1)).drop rm) := by
            dsimp only [S_prev_s]
            rw [hprev_inv.S_level_eq ⟨m - 1, by omega⟩]
            have hdrop_app : (us.take (r + d + 1)).drop rm =
                (us.take (r + d)).drop rm ++ [u_s] := by
              rw [htk', List.drop_append_of_le_length]
              simp [List.length_take]; omega
            have hGapp : (G₀.applyBatch (us.take rm)).applyBatch ((us.take (r + d)).drop rm) =
                (runState (L := L) G₀ q sparsify us (r + d)).G := by
              have htk_rm : us.take (r + d) = us.take rm ++ (us.take (r + d)).drop rm := by
                have h1 : (us.take (r + d)).take rm = us.take rm := by
                  rw [List.take_take, min_eq_left hrm_le]
                rw [← h1]; exact (List.take_append_drop rm (us.take (r + d))).symm
              rw [hprev_inv.G_eq]; conv_rhs => rw [htk_rm]
              exact (applyBatch_append G₀ (us.take rm) ((us.take (r + d)).drop rm)).symm
            rw [hdrop_app, allTouched_append, hGapp]
            simp [allTouched, rm]
          have h_rm_rd1 : rm ≤ r + d + 1 := Nat.le_succ_of_le hrm_le
          have h_rd1_k1 : r + d + 1 ≤ k + 1 := Nat.succ_le_succ hd_le_k
          have htk_rm1 : us.take (r + d + 1) = us.take rm ++ (us.take (r + d + 1)).drop rm := by
            have h1 : (us.take (r + d + 1)).take rm = us.take rm := by
              rw [List.take_take, min_eq_left h_rm_rd1]
            rw [← h1]; exact (List.take_append_drop rm (us.take (r + d + 1))).symm
          have hdrop_rm1 : (us.take (r + d + 1)).drop r =
              (us.take rm).drop r ++ (us.take (r + d + 1)).drop rm := by
            conv_lhs => rw [htk_rm1]
            rw [List.drop_append_of_le_length]
            rw [List.length_take]
            exact le_trans hrm_ge_r (Nat.le_min.mpr ⟨le_rfl, by omega⟩)
          have htk_rm_r : us.take rm = us.take r ++ (us.take rm).drop r := by
            have h1 : (us.take rm).take r = us.take r := by rw [List.take_take, min_eq_left hrm_ge_r]
            rw [← h1]; exact (List.take_append_drop r (us.take rm)).symm
          have hG_rm : (G₀.applyBatch (us.take r)).applyBatch ((us.take rm).drop r) =
              G₀.applyBatch (us.take rm) := by
            conv_rhs => rw [htk_rm_r]
            exact (applyBatch_append G₀ (us.take r) ((us.take rm).drop r)).symm
          have hsub1 : allTouched (G₀.applyBatch (us.take rm)) ((us.take (r + d + 1)).drop rm) ⊆
              allTouched (G₀.applyBatch (us.take r)) ((us.take (r + d + 1)).drop r) := by
            rw [hdrop_rm1, allTouched_append, hG_rm]
            exact Finset.subset_union_right
          have htk_rd1_k1 : us.take (k + 1) =
              us.take (r + d + 1) ++ (us.take (k + 1)).drop (r + d + 1) := by
            have h1 : (us.take (k + 1)).take (r + d + 1) = us.take (r + d + 1) := by
              rw [List.take_take, min_eq_left h_rd1_k1]
            rw [← h1]; exact (List.take_append_drop (r + d + 1) (us.take (k + 1))).symm
          have hdrop_k1_r : (us.take (k + 1)).drop r =
              (us.take (r + d + 1)).drop r ++ (us.take (k + 1)).drop (r + d + 1) := by
            conv_lhs => rw [htk_rd1_k1]
            rw [List.drop_append_of_le_length]
            rw [List.length_take]
            exact le_trans (Nat.le_succ_of_le (Nat.le_trans hrm_ge_r hrm_le))
              (Nat.le_min.mpr ⟨le_rfl, by omega⟩)
          have hsub2 : allTouched (G₀.applyBatch (us.take r)) ((us.take (r + d + 1)).drop r) ⊆
              allTouched (G₀.applyBatch (us.take r)) ((us.take (k + 1)).drop r) := by
            rw [hdrop_k1_r, allTouched_append]
            exact Finset.subset_union_left
          rw [hSprev_eq]
          exact Finset.Subset.trans hsub1 hsub2
        set delta_sk := (us.take (k + 1)).drop (r + d + 1)
        have h_rd1_k1 : r + d + 1 ≤ k + 1 := Nat.succ_le_succ hd_le_k
        have htk_rd1_k1 : us.take (k + 1) = us.take (r + d + 1) ++ delta_sk := by
          have h1 : (us.take (k + 1)).take (r + d + 1) = us.take (r + d + 1) := by
            rw [List.take_take, min_eq_left h_rd1_k1]
          rw [← h1]; exact (List.take_append_drop (r + d + 1) (us.take (k + 1))).symm
        obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
        have hBV_split := (batchIsValid_append G₀ (us.take (r + d + 1)) delta_sk).mp
          (htk_rd1_k1 ▸ hBV_k1)
        have hBV_rd1 : G₀.BatchIsValid (us.take (r + d + 1)) := hBV_split.1
        have hBV_sk : G_s.BatchIsValid delta_sk := hBV_split.2
        have hds_rd1 : ∀ x ∈ us.take (r + d + 1), isDelOrSplit x := fun x hx =>
          hds_k1 x (by rw [htk_rd1_k1]; exact List.mem_append_left _ hx)
        have hds_sk : ∀ x ∈ delta_sk, isDelOrSplit x := fun x hx =>
          hds_k1 x (by rw [htk_rd1_k1]; exact List.mem_append_right _ hx)
        have hVGs : G_s.IsValid := (batch_delOrSplit_invariants _ G₀ hVG₀ hBV_rd1 hds_rd1).1
        have hGk1_eq : G_k1 = G_s.applyBatch delta_sk := by
          dsimp only [G_k1, G_s]
          rw [htk_rd1_k1, applyBatch_append]
        have hinv_sk := batch_delOrSplit_invariants delta_sk G_s hVGs hBV_sk hds_sk
        have hVG_k1 : G_k1.IsValid := hGk1_eq ▸ hinv_sk.1
        have heG_s : eG ∈ G_s.E := hinv_sk.2.1 (hGk1_eq ▸ heG')
        have hS_sk_sub : allTouched G_s delta_sk ⊆
            allTouched (G₀.applyBatch (us.take r)) ((us.take (k + 1)).drop r) := by
          have hr_rd1 : r ≤ r + d + 1 := by omega
          have htk_rs : us.take (r + d + 1) = us.take r ++ (us.take (r + d + 1)).drop r := by
            have h1 : (us.take (r + d + 1)).take r = us.take r := by
              rw [List.take_take, min_eq_left hr_rd1]
            rw [← h1]; exact (List.take_append_drop r (us.take (r + d + 1))).symm
          have hGrs : (G₀.applyBatch (us.take r)).applyBatch ((us.take (r + d + 1)).drop r) = G_s := by
            dsimp only [G_s]; conv_rhs => rw [htk_rs]
            exact (applyBatch_append G₀ (us.take r) ((us.take (r + d + 1)).drop r)).symm
          have hdrop_k1_r : (us.take (k + 1)).drop r = (us.take (r + d + 1)).drop r ++ delta_sk := by
            conv_lhs => rw [htk_rd1_k1]
            rw [List.drop_append_of_le_length]
            rw [List.length_take]
            exact le_trans hr_rd1 (Nat.le_min.mpr ⟨le_rfl, by omega⟩)
          rw [hdrop_k1_r, allTouched_append, hGrs]
          exact Finset.subset_union_right
        have hanc_ends := hinv_sk.2.2.2.2.2.2 eG heG_s
        have hdrop_p : (G_s.walkVertices (G_s.tail eG) p₁).dropLast =
            (G_k1.walkVertices (G_k1.tail eG) p₁).dropLast :=
          dropLast_walkVertices_eq_of_not_mem_allTouched p₁ hVGs hBV_sk hds_sk hGk1_eq
            hp₁_walk (hVG_k1 eG heG').1 (hGk1_eq ▸ hanc_ends.1)
            fun z hz hmem => hp₁_drop z hz (hS_sk_sub hmem)
        have hdrop_q : (G_s.walkVertices (G_s.head eG) q₂).dropLast =
            (G_k1.walkVertices (G_k1.head eG) q₂).dropLast :=
          dropLast_walkVertices_eq_of_not_mem_allTouched q₂ hVGs hBV_sk hds_sk hGk1_eq
            hq₂_walk (hVG_k1 eG heG').2 (hGk1_eq ▸ hanc_ends.2)
            fun z hz hmem => hq₂_drop z hz (hS_sk_sub hmem)
        have hp_not_Ss : ∀ z ∈ (H_lt_s.walkVertices (G_s.tail eG) p₁).dropLast, z ∉ S_prev_s := by
          intro z hz hzS
          have hz' : z ∈ (G_k1.walkVertices (G_k1.tail eG) p₁).dropLast := by
            rw [← hdrop_p]; exact hz
          exact hp₁_drop z hz' (hS_sub hzS)
        have hq_not_Ss : ∀ z ∈ (H_lt_s.walkVertices (G_s.head eG) q₂).dropLast, z ∉ S_prev_s := by
          intro z hz hzS
          have hz' : z ∈ (G_k1.walkVertices (G_k1.head eG) q₂).dropLast := by
            rw [← hdrop_q]; exact hz
          exact hq₂_drop z hz' (hS_sub hzS)
        obtain ⟨rest₁, hrest₁⟩ := ih_mid.1
        obtain ⟨rest₂, hrest₂⟩ := ih_mid.2
        rw [← h_pi_mid_eq eG hGrd1_E] at hrest₁ hrest₂
        have hp_res : p₁ <+: (prefixWalk H_lt_s (G_s.tail eG) (piLt_mid_s eG) S_prev_s).2 := by
          rw [← hrest₁]
          exact prefixWalk_append_of_not_mem H_lt_s S_prev_s p₁ rest₁ (G_s.tail eG) hp_not_Ss
        have hq_res :
            q₂ <+: (prefixWalk H_lt_s (G_s.head eG) (walkRev (piLt_mid_s eG)) S_prev_s).2 := by
          rw [← hrest₂]
          exact prefixWalk_append_of_not_mem H_lt_s S_prev_s q₂ rest₂ (G_s.head eG) hq_not_Ss
        constructor
        · dsimp only [reembedWalk]
          rw [List.append_assoc]
          exact hp_res.trans (List.prefix_append _ _)
        · dsimp only [reembedWalk]
          rw [walkRev_append, walkRev_append, walkRev_walkRev]
          exact hq_res.trans (List.prefix_append _ _)
      · -- Case B: `eG ∉ E_aff_s`, so `piLe (st (r + d + 1)) m eG = piLt_mid_s eG = pi_mid eG`.
        have he0 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom
            ⟨0, Nat.zero_lt_succ L⟩ := hnext_inv.inDom0 ▸ hGrd1_E
        have hm_pos : 0 < m := lt_of_lt_of_le hj_pos hch_m
        have hm_not : eG ∉ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom
            ⟨m, Nat.lt_succ_of_le hm_le⟩ := by
          rw [hst1]; dsimp only [step]
          simp only [hstep_ch, hm_ne, ↓reduceDIte]
          simpa [← hGs_eq, E_aff_s, H_lt_s, H_mid_s, piLt_mid_s, inDom_mid_s, S_prev_s] using heAff_s
        have hprev := piLtFrom_eq_prev_of_not_mem
          (runState (L := L) G₀ q sparsify us (r + d + 1)).Pi_level
          (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom
          (j := ⟨m, Nat.lt_succ_of_le hm_le⟩) hm_pos he0 hm_not
        have hcongr_in : ∀ l : Fin (L + 1), l.1 < m →
            (eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom l ↔
             eG ∈ inDom_mid_s l) := fun l hl => by
          rw [hst1]; dsimp only [step]
          simp only [hstep_ch, hm_ne, ↓reduceDIte]
          simp [hl, ← hGs_eq, inDom_mid_s]
        have h0_mid : eG ∈ inDom_mid_s ⟨0, Nat.zero_lt_succ L⟩ :=
          (hcongr_in ⟨0, Nat.zero_lt_succ L⟩ hm_pos).mp he0
        have hcongr_mid : piLtFrom (runState (L := L) G₀ q sparsify us (r + d + 1)).Pi_level
            (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom m eG = piLt_mid_s eG := by
          obtain ⟨l₁, hl₁, hl₁d, hl₁n, heq₁⟩ := piLtFrom_eq _ _ hm_pos he0
          obtain ⟨l₂, hl₂, hl₂d, hl₂n, heq₂⟩ := piLtFrom_eq _ _ hm_pos h0_mid
          have hl_eq : l₁ = l₂ := by
            by_contra hne
            rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
            · exact hl₁n l₂ hlt hl₂ ((hcongr_in l₂ hl₂).mpr hl₂d)
            · exact hl₂n l₁ hlt hl₁ ((hcongr_in l₁ hl₁).mp hl₁d)
          have hPi_same : (runState (L := L) G₀ q sparsify us (r + d + 1)).Pi_level l₂ =
              (runState (L := L) G₀ q sparsify us (r + d)).Pi_level l₂ := by
            rw [hst1]; dsimp only [step]
            simp only [hstep_ch, hm_ne, ↓reduceDIte]
            simp [hl₂]
          change piLtFrom _ _ m eG = piLtFrom _ _ m eG
          rw [heq₁, heq₂, hl_eq, hPi_same]
        change _ <+: piLtFrom _ _ (m + 1) eG ∧ _ <+: walkRev (piLtFrom _ _ (m + 1) eG)
        rw [hprev, hcongr_mid, h_pi_mid_eq eG hGrd1_E]
        exact ih_mid

private theorem prefixWalk_eq_of_disjoint (H : MGraph) (S : Finset ℕ) :
    ∀ (w : List (ℕ × Bool)) (a b : ℕ),
      H.IsWalk a b w → Disjoint (H.walkVertices a w).toFinset S →
      prefixWalk H a w S = (b, w)
  | [], a, _, h, hdis => by
    cases h with
    | nil _ =>
      have ha : a ∉ S := Finset.disjoint_left.mp hdis (by simp [MGraph.walkVertices])
      simp [prefixWalk, ha]
  | x :: w', a, b, h, hdis => by
    cases h with
    | cons _ _ hrest =>
      have ha : a ∉ S := Finset.disjoint_left.mp hdis (by simp [MGraph.walkVertices])
      have hdis' : Disjoint (H.walkVertices (H.dst x) w').toFinset S := by
        refine Finset.disjoint_left.mpr fun z hz => Finset.disjoint_left.mp hdis ?_
        simpa [MGraph.walkVertices] using Or.inr hz
      have ih := prefixWalk_eq_of_disjoint H S w' (H.dst x) b hrest hdis'
      simp [prefixWalk, ha, ih]

/-- **Theorem 8.2, Item 3 (single-step re-embedding guarantee)**:
For any edge `eG` surviving at step `k + 1` and any spanner edge `eH ∈ Π'(eG)` not in the
re-embedded edge set `D^{(k+1)}`, `eH` was already on `Π(eG)` before step `k + 1`. -/
theorem reembed_step_spec {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    let st := runState (L := L) G₀ q sparsify us k
    let res := runStepOut (L := L) G₀ q sparsify us k
    let st' := runState (L := L) G₀ q sparsify us (k + 1)
    ∀ eG ∈ (G₀.applyBatch (us.take (k + 1))).E, ∀ eH,
      eH ∈ walkEdges (piTotal st' eG) → eH ∉ res.D → eH ∈ walkEdges (piTotal st eG) := by
  intro st res st' eG heG' eH heH_walk heH_notD
  have hu_some : us[k]? = some (us[k]'hk) := List.getElem?_eq_getElem hk
  set u := us[k]'hk
  have hres_eq : res = step st u sparsify := by simp [res, runStepOut, hu_some, st, u]
  have hst'_eq : st' = res.state := by simp [st', runState, hu_some, res, hres_eq, st]
  have hInv := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk)
  have hk1_inv := hInv.1
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (Nat.le_of_lt hk)).1
  have hRec := hInv.2 k (Nat.lt_succ_self k) u hu_some
  by_cases hj0 : chooseLevel L q (k + 1) = 0
  · obtain ⟨_, _, hD_card, _⟩ := hRec.restart_bounds hj0
    have hD_card_nat : res.D.card = res.state.H.E.card := by exact_mod_cast hD_card
    have hD_eq : res.D = st'.H.E :=
      Finset.eq_of_subset_of_card_le hRec.D_sub (by rw [hst'_eq, hD_card_nat])
    have hemb' := (lemma_5_6 hVG₀ hL hq hGm₀ hSpec hBV hds (k := k + 1) (Nat.succ_le_of_lt hk)).2
    have hw' := hemb'.2 eG (hk1_inv.G_eq ▸ heG')
    rw [mem_walkEdges_iff] at heH_walk
    rcases heH_walk with ⟨x, hx, rfl⟩
    have hxH : x.1 ∈ st'.H.E := IsWalk.mem_edge hw' x hx
    exact absurd (hD_eq ▸ hxH) heH_notD
  · set j := chooseLevel L q (k + 1)
    have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
    have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
    have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
    have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
    obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
    obtain ⟨hBV_k, hds_k, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
    obtain ⟨hu_valid, hdu⟩ := hU_valid u hu_some
    have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
    have hinv_k := batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k
    have hVGk : (G₀.applyBatch (us.take k)).IsValid := hinv_k.1
    set Gk := G₀.applyBatch (us.take k)
    set G' := G₀.applyBatch (us.take (k + 1))
    have hG'_eq : G' = Gk.applyUpdate u := by
      simp [G', Gk, htake_succ, MGraph.applyBatch]
    have hinv_k1 := batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀ hBV_k1 hds_k1
    have hVG' : G'.IsValid := hinv_k1.1
    have hG'E_sub : G'.E ⊆ Gk.E := by
      have h1 := (batch_delOrSplit_invariants [u] Gk hVGk
        ⟨hu_valid, True.intro⟩ (fun x hx => by simp at hx; rwa [hx])).2.1
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil] at h1
      rwa [← hG'_eq] at h1
    set r := lastRebuild q L (j - 1) (k + 1)
    have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ k + 1 := by
      intro hdvd
      have := (chooseLevel_le_iff_dvd hq (le_trans (Nat.sub_le j 1) hj_le)).mpr hdvd
      omega
    have hr_eq_k : r = lastRebuild q L (j - 1) k :=
      lastRebuild_eq_of_not_dvd (q := q) (L := L) (i := j - 1) hr_not_dvd
    have hr_le_k : r ≤ k := by rw [hr_eq_k]; exact lastRebuild_le q L (j - 1) k
    have hInv_r := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r (le_trans hr_le_k (Nat.le_of_lt hk))).1
    have hr_ch : chooseLevel L q r ≤ j - 1 :=
      lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
    set st_r := runState (L := L) G₀ q sparsify us r
    set G_r := G₀.applyBatch (us.take r)
    set delta := (us.take (k + 1)).drop r
    have htake_k1 : us.take (k + 1) = us.take r ++ delta := by
      have h1 : (us.take (k + 1)).take r = us.take r := by
        rw [List.take_take, min_eq_left (le_trans hr_le_k (Nat.le_succ k))]
      rw [← h1]; exact (List.take_append_drop r (us.take (k + 1))).symm
    have hBV_split := (batchIsValid_append G₀ (us.take r) delta).mp (htake_k1 ▸ hBV_k1)
    have hBV_r : G₀.BatchIsValid (us.take r) := hBV_split.1
    have hBV_d : G_r.BatchIsValid delta := hBV_split.2
    have hds_d : ∀ x ∈ delta, isDelOrSplit x := fun x hx =>
      hds_k1 x (by rw [htake_k1]; exact List.mem_append_right _ hx)
    have hds_r : ∀ x ∈ us.take r, isDelOrSplit x := fun x hx =>
      hds_k1 x (by rw [htake_k1]; exact List.mem_append_left _ hx)
    have hinv_r_d := batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_r hds_r
    have hVG_r : G_r.IsValid := hinv_r_d.1
    have hG_r_m : G_r.m ≤ mMax := le_trans (Finset.card_le_card hinv_r_d.2.1) hGm₀
    have hG'_delta : G' = G_r.applyBatch delta := by
      dsimp only [G', G_r]; rw [htake_k1, applyBatch_append]
    have hinv_d := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
    have hrk_eq_lt : ∀ {m : ℕ}, m < j →
        lastRebuild q L m (k + 1) = lastRebuild q L m k ∧
        lastRebuild q L m r = lastRebuild q L m k := fun {m} hm => by
      have hm_le : m ≤ j - 1 := Nat.le_pred_of_lt hm
      have h1 : lastRebuild q L m (k + 1) = lastRebuild q L m k := by
        refine lastRebuild_eq_of_not_dvd fun hdvd => hr_not_dvd ?_
        exact dvd_trans (phasePeriod_dvd_of_le hm_le (le_trans (Nat.sub_le j 1) hj_le)) hdvd
      have hmr_le : lastRebuild q L m k ≤ r := by
        rw [hr_eq_k]
        exact lastRebuild_mono_level hq hm_le (le_trans (Nat.sub_le j 1) hj_le)
      exact ⟨h1, lastRebuild_idempotent_le hq hmr_le hr_le_k⟩
    set H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    have hH_mid_props : ∀ i : Fin (L + 1),
        G'.IsSubgraph (H_mid i) ∧ (H_mid i).V = G'.V ∧ (H_mid i).E = (st.H_level i).E ∩ G'.E :=
      fun i => by
        obtain ⟨_, h1, h2, h3, _, _⟩ :=
          isSubgraph_restrictUpdate (hk_inv.H_level_sub i) (hk_inv.H_level_V i) hu_valid hdu
        exact ⟨hG'_eq ▸ h1, hG'_eq ▸ h2, hG'_eq ▸ h3⟩
    set H_lt := unionGraphLt G' H_mid j
    set H_lt_r := unionGraphLt G_r st_r.H_level j
    have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
      refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
      intro e he
      simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and] at he
      rcases he with ⟨i, _, hei⟩
      exact (hInv_r.H_level_sub i).2.1 hei
    have hHLt_E : H_lt.E = H_lt_r.E ∩ G'.E := by
      ext e
      simp only [H_lt, H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_inter, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hij, hei⟩
        rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2] at hei
        have hei' := Finset.mem_inter.mp hei
        have hei1 := Finset.mem_inter.mp hei'.1
        have hei_r : e ∈ (st_r.H_level i).E := by
          rw [hInv_r.H_level_E i]
          exact Finset.mem_inter.mpr ⟨hei1.1, hinv_d.2.1 (hG'_delta ▸ hei'.2)⟩
        exact ⟨⟨i, hij, hei_r⟩, hei'.2⟩
      · rintro ⟨⟨i, hij, hei_r⟩, heG'⟩
        refine ⟨i, hij, ?_⟩
        rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2]
        rw [hInv_r.H_level_E i, Finset.mem_inter] at hei_r
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hei_r.1, hG'E_sub heG'⟩, heG'⟩
    have hSub_lt : G'.IsSubgraph H_lt := ⟨Finset.Subset.rfl, hHLt_E ▸ Finset.inter_subset_right,
      fun _ _ => ⟨rfl, rfl⟩⟩
    set inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    set piLt_mid : Embedding := piLtFrom st.Pi_level inDom_mid j
    set S_prev : Finset ℕ := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u
    have hS_prev_eq : S_prev = allTouched G_r delta := by
      dsimp only [S_prev]
      rw [hk_inv.S_level_eq ⟨j - 1, by omega⟩, ← hr_eq_k]
      have hdrop_app : (us.take (k + 1)).drop r = (us.take k).drop r ++ [u] := by
        rw [htake_succ, List.drop_append_of_le_length]
        rw [List.length_take]; exact le_trans hr_le_k (Nat.le_min.mpr ⟨le_rfl, Nat.le_of_lt hk⟩)
      have hGapp : G_r.applyBatch ((us.take k).drop r) = Gk := by
        have htk : us.take k = us.take r ++ (us.take k).drop r := by
          have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le_k]
          rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
        dsimp only [Gk, G_r]; conv_rhs => rw [htk]
        exact (applyBatch_append _ _ _).symm
      dsimp only [delta]
      rw [hdrop_app, allTouched_append, hGapp]
      dsimp only [Gk, G_r]
      rw [hk_inv.G_eq]
      simp [allTouched]
    have hpi_eq : ∀ e ∈ G'.E, piLt_mid e = piLe st_r (j - 1) e := fun e heG'' => by
      change piLtFrom st.Pi_level inDom_mid j e = piLtFrom st_r.Pi_level st_r.inDom ((j - 1) + 1) e
      have hsub1 : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
      rw [hsub1]
      have h0_mid : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
        dsimp only [inDom_mid]; rw [Finset.mem_inter, hk_inv.inDom0]; exact ⟨hG'E_sub heG'', heG''⟩
      have h0_r : e ∈ st_r.inDom ⟨0, Nat.zero_lt_succ L⟩ := by
        rw [hInv_r.inDom0]; exact hinv_d.2.1 (hG'_delta ▸ heG'')
      have hcongr_in : ∀ m : Fin (L + 1), m.1 < j → (e ∈ inDom_mid m ↔ e ∈ st_r.inDom m) := by
        intro m hm
        have h1 := hk_inv.inDom_eq m
        have h2 := hInv_r.inDom_eq m
        rw [← (hrk_eq_lt hm).2] at h1
        have heGk : e ∈ Gk.E := hG'E_sub heG''
        have heGr : e ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ heG'')
        constructor
        · intro h; rw [Finset.mem_inter] at h; have h' := h.1; rw [h1, Finset.mem_inter] at h'
          rw [h2]; exact Finset.mem_inter.mpr ⟨h'.1, heGr⟩
        · intro h; rw [h2, Finset.mem_inter] at h
          refine Finset.mem_inter.mpr ⟨?_, heG''⟩
          rw [h1]; exact Finset.mem_inter.mpr ⟨h.1, heGk⟩
      obtain ⟨m₁, hm₁j, hm₁d, hm₁none, heq₁⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
      obtain ⟨m₂, hm₂j, hm₂d, hm₂none, heq₂⟩ := piLtFrom_eq st_r.Pi_level st_r.inDom hj_pos h0_r
      have hm_eq : m₁ = m₂ := by
        by_contra hne
        rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
        · exact hm₁none m₂ hlt hm₂j ((hcongr_in m₂ hm₂j).mpr hm₂d)
        · exact hm₂none m₁ hlt hm₁j ((hcongr_in m₁ hm₁j).mp hm₁d)
      rw [heq₁, heq₂, hm_eq, hk_inv.Pi_level_eq m₂, ← (hrk_eq_lt hm₂j).2, hInv_r.Pi_level_eq m₂]
    have hj1_succ : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
    have hEmbr := hInv_r.emb_at ⟨j - 1, by omega⟩ hr_ch
    have hLenr := hInv_r.len_at ⟨j - 1, by omega⟩ hr_ch
    have hVcr := hInv_r.vcong_at ⟨j - 1, by omega⟩ hr_ch
    dsimp only at hEmbr hLenr hVcr
    rw [hj1_succ] at hEmbr hVcr
    have hPW := projWalk_spec hSpec hVG_r hBV_d hds_d hG_r_m hSub_lt_r hEmbr hLenr hVcr
      (vcongBound_nonneg hγc hγl G₀.maxDeg (j - 1))
      (vcongBound_step P.hγ_c P.hγ_ℓ G₀.maxDeg (j - 1))
      (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E)
      (by simp [H_lt, unionGraphLt, hG'_delta]) (by simp [H_lt, unionGraphLt, hG'_delta])
      (hG'_delta ▸ hSub_lt) hS_prev_eq.symm.subset (fun e he => hpi_eq e (hG'_delta ▸ he))
    dsimp only at hPW
    rw [← hG'_delta] at hPW
    rcases hPW with ⟨_, _, _, hOut_aff, _, _, _, _, _, _, _, _, _, _, _, hOut_emb, -⟩
    set E_aff := affectedEdges G' H_lt piLt_mid S_prev
    set J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    set H_aux := buildAuxHost G' H_lt E_aff
    set embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
    set out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
    set outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
    set embMid : Embedding := Embedding.comp embJH outEmb
    set Pi_j : Embedding := reembedWalk G' H_lt piLt_mid embMid S_prev
    have hD_eq : res.D = out.Jtilde.E.biUnion fun e => walkEdges (embJH e) := by
      rw [hres_eq]; dsimp only [step]
      have hst_eq : st.q = q ∧ st.t = k ∧ st.G = Gk := ⟨hk_inv.q_eq, hk_inv.t_eq, hk_inv.G_eq⟩
      simp only [show ¬ chooseLevel L st.q (st.t + 1) = 0 by rw [hst_eq.1, hst_eq.2.1]; exact hj0,
        ↓reduceDIte]
      have hch_j : chooseLevel L st.q (st.t + 1) = j := by rw [hst_eq.1, hst_eq.2.1]
      have hstG' : st.G.applyUpdate u = G' := by rw [hst_eq.2.2, ← hG'_eq]
      simp only [hch_j, hstG', H_mid, H_lt, inDom_mid, piLt_mid, E_aff, J, H_aux, embJH, out,
        S_prev, st]
    have hres_st_Pi : ∀ l : Fin (L + 1), st'.Pi_level l =
        if l.1 < j then st.Pi_level l else if l.1 = j then Pi_j else fun _ => [] := fun l => by
      rw [hst'_eq, hres_eq]; dsimp only [step]
      have hch_j : chooseLevel L st.q (st.t + 1) = j := by rw [hk_inv.q_eq, hk_inv.t_eq]
      have hch_ne : ¬ chooseLevel L st.q (st.t + 1) = 0 := by rw [hch_j]; exact hj0
      simp only [hch_ne, ↓reduceDIte]
      have hstG' : st.G.applyUpdate u = G' := by rw [hk_inv.G_eq, ← hG'_eq]
      simp only [hch_j, hstG', Pi_j, embMid, outEmb, embJH, out, J, H_aux, E_aff, S_prev, piLt_mid,
        inDom_mid, H_lt, H_mid, st]
    have hres_st_inDom : ∀ l : Fin (L + 1), st'.inDom l =
        if l.1 < j then inDom_mid l else if l.1 = j then E_aff else ∅ := fun l => by
      rw [hst'_eq, hres_eq]; dsimp only [step]
      have hch_j : chooseLevel L st.q (st.t + 1) = j := by rw [hk_inv.q_eq, hk_inv.t_eq]
      have hch_ne : ¬ chooseLevel L st.q (st.t + 1) = 0 := by rw [hch_j]; exact hj0
      simp only [hch_ne, ↓reduceDIte]
      have hstG' : st.G.applyUpdate u = G' := by rw [hk_inv.G_eq, ← hG'_eq]
      simp only [hch_j, hstG', E_aff, S_prev, piLt_mid, inDom_mid, H_lt, H_mid, st]
    have hpiTot' : piTotal st' eG = if eG ∈ E_aff then Pi_j eG else piLt_mid eG := by
      have he0' : eG ∈ st'.inDom ⟨0, Nat.zero_lt_succ L⟩ := hk1_inv.inDom0 ▸ heG'
      have hlt_L := piLtFrom_eq_of_lt st'.Pi_level st'.inDom (Nat.succ_pos j) (Nat.succ_le_succ hj_le)
        he0' fun l hl1 _ => by
          rw [hres_st_inDom l]
          simp [Nat.not_lt.mpr (Nat.le_of_succ_le hl1),
            Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hl1)]
      change piLtFrom st'.Pi_level st'.inDom (L + 1) eG = _
      rw [hlt_L]
      by_cases heAff : eG ∈ E_aff
      · have hj_dom : eG ∈ st'.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
          rw [hres_st_inDom]; simp [heAff]
        obtain ⟨m, hmj, _, hm_none, heqm⟩ := piLtFrom_eq st'.Pi_level st'.inDom (Nat.succ_pos j) he0'
        have hm_eq : m.1 = j := by
          apply le_antisymm (Nat.lt_succ_iff.mp hmj)
          by_contra hlt
          exact hm_none ⟨j, Nat.lt_succ_of_le hj_le⟩ (Nat.lt_of_not_le hlt) (Nat.lt_succ_self j) hj_dom
        rw [heqm, show m = ⟨j, Nat.lt_succ_of_le hj_le⟩ from Fin.ext hm_eq, hres_st_Pi]
        simp [heAff]
      · have hj_not : eG ∉ st'.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
          rw [hres_st_inDom]; simp [heAff]
        have hprev := piLtFrom_eq_prev_of_not_mem st'.Pi_level st'.inDom
          (j := ⟨j, Nat.lt_succ_of_le hj_le⟩) hj_pos he0' hj_not
        rw [hprev]
        have hcongr_mid : piLtFrom st'.Pi_level st'.inDom j eG = piLt_mid eG := by
          have h0_mid : eG ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
            dsimp only [inDom_mid]; rw [Finset.mem_inter, hk_inv.inDom0]; exact ⟨hG'E_sub heG', heG'⟩
          obtain ⟨m, hmj, hmd, hm_none, heqm⟩ := piLtFrom_eq st'.Pi_level st'.inDom hj_pos he0'
          obtain ⟨m', hm'j, hm'd, hm'_none, heqm'⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
          have hmm' : m = m' := by
            by_contra hne
            rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
            · exact hm_none m' hlt hm'j (by rw [hres_st_inDom]; simp [hm'j, hm'd])
            · exact hm'_none m hlt hmj (by rw [hres_st_inDom] at hmd; simpa [hmj] using hmd)
          dsimp only [piLt_mid]
          rw [heqm, heqm', hmm', hres_st_Pi]
          simp [hm'j]
        rw [hcongr_mid]; simp [heAff]
    -- Apply prefix/suffix preservation backwards from `r` to `k`!
    set S_r := allTouched G_r delta
    set p_r := piLe st_r (j - 1) eG
    set p₁ := (prefixWalk H_lt (G'.tail eG) p_r S_r).2
    set q₂ := (prefixWalk H_lt (G'.head eG) (walkRev p_r) S_r).2
    have hpi_r : piLt_mid eG = p_r := hpi_eq eG heG'
    have hSub_lt_delta : (G_r.applyBatch delta).IsSubgraph H_lt := hG'_delta ▸ hSub_lt
    have hHLt_V_delta : H_lt.V = (G_r.applyBatch delta).V := by
      simp [H_lt, unionGraphLt, hG'_delta]
    have hHLt_E_delta : H_lt.E = H_lt_r.E ∩ (G_r.applyBatch delta).E := hG'_delta ▸ hHLt_E
    have hEnds_lt : ∀ e ∈ H_lt_r.E, H_lt.tail e = (G_r.applyBatch delta).tail e ∧
        H_lt.head e = (G_r.applyBatch delta).head e := fun _ _ => by
      simp [H_lt, unionGraphLt, hG'_delta]
    have hw_r : H_lt_r.IsWalk (G_r.tail eG) (G_r.head eG) p_r :=
      hEmbr.2 eG (hinv_d.2.1 (hG'_delta ▸ heG'))
    have hanc_ends := hinv_d.2.2.2.2.2.2 eG (hinv_d.2.1 (hG'_delta ▸ heG'))
    have hV_tail : G'.tail eG ∈ (G_r.applyBatch delta).V := by
      rw [← hG'_delta]; exact (hVG' eG heG').1
    have hV_head : G'.head eG ∈ (G_r.applyBatch delta).V := by
      rw [← hG'_delta]; exact (hVG' eG heG').2
    have hanc_t : batchAnc delta (G'.tail eG) = G_r.tail eG := by
      rw [hG'_delta]; exact hanc_ends.1
    have hanc_h : batchAnc delta (G'.head eG) = G_r.head eG := by
      rw [hG'_delta]; exact hanc_ends.2
    have hTouch_r : allTouched G_r delta ⊆ S_r := Finset.Subset.rfl
    have hp₁_prop := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta hHLt_V_delta
      hHLt_E_delta hEnds_lt hTouch_r p_r (G_r.tail eG) (G_r.head eG) (G'.tail eG)
      (hVG_r eG (hinv_d.2.1 (hG'_delta ▸ heG'))).1
      (hVG_r eG (hinv_d.2.1 (hG'_delta ▸ heG'))).2
      hw_r hV_tail hanc_t
    have hq₂_prop := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta hHLt_V_delta
      hHLt_E_delta hEnds_lt hTouch_r (walkRev p_r) (G_r.head eG) (G_r.tail eG) (G'.head eG)
      (hVG_r eG (hinv_d.2.1 (hG'_delta ▸ heG'))).2
      (hVG_r eG (hinv_d.2.1 (hG'_delta ▸ heG'))).1
      (isWalk_walkRev hw_r) hV_head hanc_h
    have hVw1 := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge hw_r) hV_tail
    have hVw2 := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge (isWalk_walkRev hw_r)) hV_head
    have hdisj_of_not_aff : ¬ eG ∈ E_aff →
        Disjoint (H_lt.walkVertices (G'.tail eG) p_r).toFinset S_r ∧
        Disjoint (H_lt.walkVertices (G'.head eG) (walkRev p_r)).toFinset S_r := fun hnot => by
      have hdis1 : Disjoint (H_lt.walkVertices (G'.tail eG) p_r).toFinset S_r := by
        rw [Finset.disjoint_left]
        intro z hz hzS
        rw [List.mem_toFinset, ← hpi_r] at hz
        rw [show S_r = S_prev from hS_prev_eq.symm] at hzS
        exact hnot (Finset.mem_filter.mpr ⟨heG', decide_eq_true ⟨z, hz, hzS⟩⟩)
      refine ⟨hdis1, ?_⟩
      rw [Finset.disjoint_left]
      intro z hz hzS
      have h1 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
        hTouch_r (IsWalk.mem_edge (isWalk_walkRev hw_r)) hV_head hanc_h hVw2).mp
        ⟨z, List.mem_toFinset.mp hz, hzS⟩
      obtain ⟨z₀, hz₀, hz₀S⟩ := h1
      have hz₀' : z₀ ∈ H_lt_r.walkVertices (G_r.tail eG) p_r :=
        (mem_walkVertices_walkRev hw_r z₀).mp hz₀
      have h2 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
        hTouch_r (IsWalk.mem_edge hw_r) hV_tail hanc_t hVw1).mpr
        ⟨z₀, hz₀', hz₀S⟩
      obtain ⟨w, hw, hwS⟩ := h2
      rw [← hpi_r] at hw
      rw [show S_r = S_prev from hS_prev_eq.symm] at hwS
      exact hnot (Finset.mem_filter.mpr ⟨heG', decide_eq_true ⟨w, hw, hwS⟩⟩)
    have hp_all :
        p₁ <+: p_r ∧ q₂ <+: walkRev p_r ∧
        G'.IsWalk (G'.tail eG) (prefixWalk H_lt (G'.tail eG) p_r S_r).1 p₁ ∧
        G'.IsWalk (G'.head eG) (prefixWalk H_lt (G'.head eG) (walkRev p_r) S_r).1 q₂ ∧
        (∀ z ∈ (G'.walkVertices (G'.tail eG) p₁).dropLast, z ∉ S_r) ∧
        (∀ z ∈ (G'.walkVertices (G'.head eG) q₂).dropLast, z ∉ S_r) := by
      by_cases heAff : eG ∈ E_aff
      · have hhit1 : ∃ z ∈ H_lt.walkVertices (G'.tail eG) p_r, z ∈ S_r := by
          have h0 : ∃ z ∈ H_lt.walkVertices (G'.tail eG) (piLt_mid eG), z ∈ S_prev := by
            simpa [E_aff, affectedEdges, decide_eq_true_eq] using (Finset.mem_filter.mp heAff).2
          simpa [hpi_r, hS_prev_eq] using h0
        have h1 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
          hTouch_r (IsWalk.mem_edge hw_r) hV_tail hanc_t hVw1).mp hhit1
        have h2 : ∃ z₀ ∈ H_lt_r.walkVertices (G_r.head eG) (walkRev p_r), z₀ ∈ S_r := by
          obtain ⟨z₀, hz₀, hz₀S⟩ := h1
          exact ⟨z₀, (mem_walkVertices_walkRev hw_r z₀).mpr hz₀, hz₀S⟩
        have hhit2 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
          hTouch_r (IsWalk.mem_edge (isWalk_walkRev hw_r)) hV_head hanc_h hVw2).mpr h2
        have hp1_s := hp₁_prop.2 hhit1
        have hq2_s := hq₂_prop.2 hhit2
        refine ⟨hp1_s.2.2.2.1, hq2_s.2.2.2.1,
          IsWalk.of_isSubgraph hSub_lt hp1_s.2.2.1,
          IsWalk.of_isSubgraph hSub_lt hq2_s.2.2.1,
          fun z hz hmem => (hp1_s.2.2.2.2.2 z hz).1 hmem,
          fun z hz hmem => (hq2_s.2.2.2.2.2 z hz).1 hmem⟩
      · obtain ⟨hdis1, hdis2⟩ := hdisj_of_not_aff heAff
        obtain ⟨_, hw1, _⟩ := hp₁_prop.1 hdis1
        obtain ⟨_, hw2, _⟩ := hq₂_prop.1 hdis2
        have heq1 := prefixWalk_eq_of_disjoint H_lt S_r p_r (G'.tail eG) (G_r.head eG) hw1 hdis1
        have heq2 := prefixWalk_eq_of_disjoint H_lt S_r (walkRev p_r)
          (G'.head eG) (G_r.tail eG) hw2 hdis2
        have hp1_val : p₁ = p_r := by dsimp only [p₁]; rw [heq1]
        have hq2_val : q₂ = walkRev p_r := by dsimp only [q₂]; rw [heq2]
        refine ⟨hp1_val ▸ List.prefix_rfl, hq2_val ▸ List.prefix_rfl, ?_, ?_, ?_, ?_⟩
        · dsimp only [p₁]; rw [heq1]; exact IsWalk.of_isSubgraph hSub_lt hw1
        · dsimp only [q₂]; rw [heq2]; exact IsWalk.of_isSubgraph hSub_lt hw2
        · intro z hz hmem
          have hz' : z ∈ (H_lt.walkVertices (G'.tail eG) p_r).toFinset :=
            List.mem_toFinset.mpr (List.dropLast_subset _ (by rwa [← hp1_val]))
          exact Finset.disjoint_left.mp hdis1 hz' hmem
        · intro z hz hmem
          have hz' : z ∈ (H_lt.walkVertices (G'.head eG) (walkRev p_r)).toFinset :=
            List.mem_toFinset.mpr (List.dropLast_subset _ (by rwa [← hq2_val]))
          exact Finset.disjoint_left.mp hdis2 hz' hmem
    have hPres := prefix_suffix_preserve_backward hVG₀ hL hq hGm₀ hSpec hBV hds hk j hj_pos hj_le rfl
      heG' hp_all.1 hp_all.2.1 hp_all.2.2.1 hp_all.2.2.2.1 hp_all.2.2.2.2.1 hp_all.2.2.2.2.2
      k hr_le_k le_rfl ⟨L, Nat.lt_succ_self L⟩ (Nat.le_trans (Nat.sub_le j 1) hj_le)
    rw [hpiTot'] at heH_walk
    by_cases heAff : eG ∈ E_aff
    · simp only [heAff, ↓reduceIte, Pi_j, reembedWalk] at heH_walk
      rw [walkEdges_append, walkEdges_append, walkEdges_walkRev] at heH_walk
      simp only [Finset.mem_union] at heH_walk
      rcases heH_walk with (h1 | hmid) | h2
      · exact walkEdges_subset_of_prefix hPres.1 (by rwa [hpi_r, hS_prev_eq] at h1)
      · exfalso
        rw [mem_walkEdges_iff] at hmid
        rcases hmid with ⟨y, hy, rfl⟩
        simp only [embMid, Embedding.comp, List.mem_flatMap] at hy
        rcases hy with ⟨x, hx, hyx⟩
        have hxJ : x.1 ∈ out.Jtilde.E := IsWalk.mem_edge (hOut_emb.2 eG heAff) x hx
        have hy_edge : y.1 ∈ walkEdges (embJH x.1) := by
          cases xb : x.2
          · simp only [xb, Bool.false_eq_true, ↓reduceIte] at hyx
            rw [← walkEdges_walkRev]
            exact mem_walkEdges_iff.mpr ⟨y, hyx, rfl⟩
          · simp only [xb, ↓reduceIte] at hyx
            exact mem_walkEdges_iff.mpr ⟨y, hyx, rfl⟩
        exact heH_notD (by rw [hD_eq, Finset.mem_biUnion]; exact ⟨x.1, hxJ, hy_edge⟩)
      · rw [← walkEdges_walkRev]
        exact walkEdges_subset_of_prefix hPres.2 (by rwa [hpi_r, hS_prev_eq] at h2)
    · simp only [heAff, ↓reduceIte] at heH_walk
      obtain ⟨hdis1, _⟩ := hdisj_of_not_aff heAff
      have heq1 := prefixWalk_eq_of_disjoint H_lt S_r p_r (G'.tail eG) (G_r.head eG)
        (hp₁_prop.1 hdis1).2.1 hdis1
      have hp1_val : p₁ = p_r := by dsimp only [p₁]; rw [heq1]
      rw [hpi_r] at heH_walk
      exact walkEdges_subset_of_prefix (hp1_val ▸ hPres.1) heH_walk

/-- Equivalence between iterating single updates along a flat trace `[k₀, k₀ + U.length)` and
calling the batch driver `updateGo` on `U`. -/
theorem updateGo_run_eq {L q : ℕ} {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (G₀ : MGraph) (us : List Update) :
    ∀ (U : List Update) (k₀ : ℕ) (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ),
      k₀ + U.length ≤ us.length →
      (∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) →
      updateGo sparsify (runState (L := L) G₀ q sparsify us k₀) U uhAcc dAcc cAcc =
        { state := runState (L := L) G₀ q sparsify us (k₀ + U.length)
          UH := uhAcc ++ (List.range U.length).flatMap fun i =>
            (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH
          D := (dAcc ∪ (Finset.range U.length).biUnion fun i =>
            (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D) ∩
              (runState (L := L) G₀ q sparsify us (k₀ + U.length)).H.E
          cost := cAcc + ∑ i ∈ Finset.range U.length,
            (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).cost }
  | [], k₀, uhAcc, dAcc, cAcc, _, _ => by
    simp [updateGo]
  | u :: rest, k₀, uhAcc, dAcc, cAcc, hlen, hmatch => by
    have hu_some : us[k₀]? = some u := by simpa using hmatch 0 (Nat.zero_lt_succ rest.length)
    have hst1 : runState (L := L) G₀ q sparsify us (k₀ + 1) =
        (step (runState (L := L) G₀ q sparsify us k₀) u sparsify).state := by
      simp [runState, hu_some]
    have hres0 : runStepOut (L := L) G₀ q sparsify us k₀ =
        step (runState (L := L) G₀ q sparsify us k₀) u sparsify := by
      simp [runStepOut, hu_some]
    have ih := updateGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us rest (k₀ + 1)
      (uhAcc ++ (step (runState (L := L) G₀ q sparsify us k₀) u sparsify).UH)
      (dAcc ∪ (step (runState (L := L) G₀ q sparsify us k₀) u sparsify).D)
      (cAcc + (step (runState (L := L) G₀ q sparsify us k₀) u sparsify).cost)
      (by simp only [List.length_cons] at hlen; omega)
      fun i hi => by
        have h1 := hmatch (i + 1) (Nat.succ_lt_succ hi)
        rw [show k₀ + 1 + i = k₀ + (i + 1) from by omega]
        exact h1
    dsimp only [updateGo]
    rw [← hst1, ih, ← hres0]
    have hidx : k₀ + 1 + rest.length = k₀ + (u :: rest).length := by
      simp only [List.length_cons]; omega
    rw [hidx]
    have hflat : uhAcc ++ (runStepOut (L := L) G₀ q sparsify us k₀).UH ++
        (List.range rest.length).flatMap (fun i =>
          (runStepOut (L := L) G₀ q sparsify us (k₀ + 1 + i)).UH) =
        uhAcc ++ (List.range (u :: rest).length).flatMap fun i =>
          (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH := by
      rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        List.append_assoc]
      simp only [Nat.add_zero]
      congr 2
      exact congrArg (fun g => List.flatMap g (List.range rest.length))
        (funext fun i => by rw [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 i])
    have hD : dAcc ∪ (runStepOut (L := L) G₀ q sparsify us k₀).D ∪
        (Finset.range rest.length).biUnion (fun i =>
          (runStepOut (L := L) G₀ q sparsify us (k₀ + 1 + i)).D) =
        dAcc ∪ (Finset.range (u :: rest).length).biUnion fun i =>
          (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D := by
      ext x
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, List.length_cons]
      constructor
      · rintro ((hx | hx) | ⟨i, hi, hxi⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨0, Nat.zero_lt_succ _, by simpa using hx⟩
        · exact Or.inr ⟨i + 1, Nat.succ_lt_succ hi, by
            rwa [show k₀ + (i + 1) = k₀ + 1 + i from by omega]⟩
      · rintro (hx | ⟨i, hi, hxi⟩)
        · exact Or.inl (Or.inl hx)
        · cases i with
          | zero => exact Or.inl (Or.inr (by simpa using hxi))
          | succ i' =>
            exact Or.inr ⟨i', Nat.lt_of_succ_lt_succ hi, by
              rwa [show k₀ + 1 + i' = k₀ + (i' + 1) from by omega]⟩
    have hCost : cAcc + (runStepOut (L := L) G₀ q sparsify us k₀).cost +
        ∑ i ∈ Finset.range rest.length,
          (runStepOut (L := L) G₀ q sparsify us (k₀ + 1 + i)).cost =
        cAcc + ∑ i ∈ Finset.range (u :: rest).length,
          (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).cost := by
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have hsum : ∑ x ∈ Finset.range rest.length,
            (runStepOut (L := L) G₀ q sparsify us (k₀ + 1 + x)).cost =
          ∑ x ∈ Finset.range rest.length,
            (runStepOut (L := L) G₀ q sparsify us (k₀ + (x + 1))).cost :=
        Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i]
      rw [hsum]; omega
    rw [hflat, hD, hCost]

private theorem batchIsValid_range_stepOut {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (k₀ : ℕ) :
    ∀ m : ℕ, k₀ + m ≤ us.length →
      let uh := (List.range m).flatMap fun i =>
        (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH
      (runState (L := L) G₀ q sparsify us k₀).H.BatchIsValid uh ∧
      (runState (L := L) G₀ q sparsify us k₀).H.applyBatch uh =
        (runState (L := L) G₀ q sparsify us (k₀ + m)).H
  | 0, _ => ⟨True.intro, by simp [MGraph.applyBatch]⟩
  | m + 1, hm => by
    have ih := batchIsValid_range_stepOut hVG₀ hL hq hGm₀ hSpec hBV hds k₀ m (by omega)
    have hlt : k₀ + m < us.length := by omega
    have hu_some : us[k₀ + m]? = some (us[k₀ + m]'hlt) := List.getElem?_eq_getElem hlt
    have hRec := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + m + 1) (by omega)).2
      (k₀ + m) (Nat.lt_succ_self _) (us[k₀ + m]'hlt) hu_some
    have hsplit : (List.range (m + 1)).flatMap (fun i =>
          (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH) =
        (List.range m).flatMap (fun i => (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH) ++
          (runStepOut (L := L) G₀ q sparsify us (k₀ + m)).UH := by
      rw [List.range_succ, List.flatMap_append]; simp
    dsimp only
    rw [hsplit, batchIsValid_append, applyBatch_append, ih.2, ← Nat.add_assoc]
    exact ⟨⟨ih.1, hRec.uh_valid⟩, hRec.uh_apply⟩

private theorem sum_range_count_flatMap (n : ℕ) (f : ℕ → List Update)
    (w : List Update → ℕ) (hw_app : ∀ a b, w (a ++ b) = w a + w b) (hw_nil : w [] = 0) :
    w ((List.range n).flatMap f) = ∑ i ∈ Finset.range n, w (f i) := by
  induction n with
  | zero => simp [hw_nil]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hw_app, ih, Finset.sum_range_succ]

private theorem batchSplitCount_updateGo {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ (U : List Update) (k₀ : ℕ),
      k₀ + U.length ≤ us.length →
      (∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) →
      ∑ i ∈ Finset.range U.length,
        batchSplitCount (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH ≤ batchSplitCount U
  | [], _, _, _ => by simp [batchSplitCount]
  | u :: U', k₀, hlen, hmatch => by
    have hu_some : us[k₀]? = some u := by simpa using hmatch 0 (Nat.zero_lt_succ U'.length)
    have hRec := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + 1)
      (by simp only [List.length_cons] at hlen; omega)).2
      k₀ (Nat.lt_succ_self k₀) u hu_some
    have ih := batchSplitCount_updateGo hVG₀ hL hq hGm₀ hSpec hBV hds U' (k₀ + 1)
      (by simp only [List.length_cons] at hlen; omega) fun i hi => by
        have h1 := hmatch (i + 1) (Nat.succ_lt_succ hi)
        rw [show k₀ + 1 + i = k₀ + (i + 1) from by omega]
        exact h1
    rw [List.length_cons, Finset.sum_range_succ']
    have hsp_u : batchSplitCount (u :: U') = (if isSplit u then 1 else 0) + batchSplitCount U' := by
      cases u with
      | delete _ => simp [batchSplitCount, isSplit]
      | insert _ _ _ => simp [batchSplitCount, isSplit]
      | split _ _ _ _ => simp [batchSplitCount, List.countP_cons, isSplit, Nat.add_comm]
    have h0 := hRec.uh_splits
    simp only [Nat.add_zero]
    have hsum : ∑ x ∈ Finset.range U'.length,
          batchSplitCount (runStepOut (L := L) G₀ q sparsify us (k₀ + (x + 1))).UH =
        ∑ i ∈ Finset.range U'.length,
          batchSplitCount (runStepOut (L := L) G₀ q sparsify us (k₀ + 1 + i)).UH :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm i 1, ← Nat.add_assoc]
    omega

/-- Batch update correctness, recourse bounds, and operation count decomposition over any valid
contiguous slice `U` of `us`. -/
theorem update_batch_spec {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k₀ : ℕ} {U : List Update}
    (hlen : k₀ + U.length ≤ us.length)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    let st := runState (L := L) G₀ q sparsify us k₀
    let res := update st U sparsify
    res.state = runState (L := L) G₀ q sparsify us (k₀ + U.length) ∧
    st.H.BatchIsValid res.UH ∧
    st.H.applyBatch res.UH = res.state.H ∧
    res.D ⊆ res.state.H.E ∧
    res.UH.length = ∑ i ∈ Finset.range U.length, (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH.length ∧
    batchInsertCount res.UH = ∑ i ∈ Finset.range U.length,
      batchInsertCount (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH ∧
    batchDeleteCount res.UH = ∑ i ∈ Finset.range U.length,
      batchDeleteCount (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH ∧
    batchSplitCount res.UH ≤ batchSplitCount U ∧
    res.D.card ≤ ∑ i ∈ Finset.range U.length, (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D.card ∧
    res.cost = ∑ i ∈ Finset.range U.length, (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).cost := by
  intro st res
  have hrun := updateGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us U k₀ [] ∅ 0 hlen hmatch
  have hbv := batchIsValid_range_stepOut hVG₀ hL hq hGm₀ hSpec hBV hds k₀ U.length hlen
  have hst' : res.state = runState (L := L) G₀ q sparsify us (k₀ + U.length) := by
    dsimp only [res, update]; rw [hrun]
  have hUH_eq : res.UH = (List.range U.length).flatMap fun i =>
      (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH := by
    dsimp only [res, update]; rw [hrun]; simp
  have hD_eq : res.D = ((Finset.range U.length).biUnion fun i =>
      (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D) ∩ res.state.H.E := by
    dsimp only [res, update]; rw [hrun]; simp
  have hCost_eq : res.cost = ∑ i ∈ Finset.range U.length,
      (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).cost := by
    dsimp only [res, update]; rw [hrun]; simp
  refine ⟨hst', hUH_eq ▸ hbv.1, ?_, hD_eq ▸ Finset.inter_subset_right, ?_, ?_, ?_, ?_, ?_, hCost_eq⟩
  · rw [hUH_eq, hbv.2, ← hst']
  · rw [hUH_eq]
    exact sum_range_count_flatMap U.length _ List.length (fun _ _ => List.length_append) rfl
  · rw [hUH_eq]
    exact sum_range_count_flatMap U.length _ batchInsertCount batchInsertCount_append rfl
  · rw [hUH_eq]
    exact sum_range_count_flatMap U.length _ batchDeleteCount batchDeleteCount_append rfl
  · have hsp : batchSplitCount res.UH = ∑ i ∈ Finset.range U.length,
        batchSplitCount (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).UH := by
      rw [hUH_eq]
      exact sum_range_count_flatMap U.length _ batchSplitCount batchSplitCount_append rfl
    rw [hsp]
    exact batchSplitCount_updateGo hVG₀ hL hq hGm₀ hSpec hBV hds U k₀ hlen hmatch
  · calc res.D.card
        ≤ ((Finset.range U.length).biUnion fun i =>
            (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D).card :=
          Finset.card_le_card (hD_eq ▸ Finset.inter_subset_left)
      _ ≤ ∑ i ∈ Finset.range U.length, (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D.card :=
          Finset.card_biUnion_le

/-- **Theorem 8.2, Item 3 (batch re-embedding guarantee)**:
For any batch `U` processed at step `k₀` and any edge `eG ∈ res.state.G.E`, if a spanner edge
`eH ∈ Π'(eG)` does not belong to `res.D`, then `eH` already belonged to `Π(eG)` before the batch. -/
theorem reembed_batch_spec {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k₀ : ℕ} {U : List Update}
    (hlen : k₀ + U.length ≤ us.length)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    let st := runState (L := L) G₀ q sparsify us k₀
    let res := update st U sparsify
    ∀ eG ∈ res.state.G.E, ∀ eH,
      eH ∈ walkEdges (piTotal res.state eG) → eH ∉ res.D → eH ∈ walkEdges (piTotal st eG) := by
  intro st res eG heG_res eH heH_walk heH_notD
  have hrun := updateGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us U k₀ [] ∅ 0 hlen hmatch
  have hst' : res.state = runState (L := L) G₀ q sparsify us (k₀ + U.length) := by
    dsimp only [res, update]; rw [hrun]
  have hinv_end := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + U.length) hlen).1
  have heG_end : eG ∈ (G₀.applyBatch (us.take (k₀ + U.length))).E := by
    rw [← hinv_end.G_eq, ← hst']; exact heG_res
  have hemb_end := (lemma_5_6 hVG₀ hL hq hGm₀ hSpec hBV hds (k := k₀ + U.length) hlen).2
  have hw_end := hemb_end.2 eG heG_end
  rw [← hst'] at hw_end
  have heH_H : eH ∈ res.state.H.E := by
    rw [mem_walkEdges_iff] at heH_walk
    rcases heH_walk with ⟨x, hx, rfl⟩
    exact IsWalk.mem_edge hw_end x hx
  have hD_eq : res.D = ((Finset.range U.length).biUnion fun i =>
      (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D) ∩ res.state.H.E := by
    dsimp only [res, update]; rw [hrun]; simp
  have heH_not_step : ∀ i < U.length,
      eH ∉ (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D := by
    intro i hi hmem
    apply heH_notD
    rw [hD_eq, Finset.mem_inter]
    exact ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hmem⟩, heH_H⟩
  have hback : ∀ r ≤ U.length,
      eH ∈ walkEdges (piTotal (runState (L := L) G₀ q sparsify us (k₀ + (U.length - r))) eG) := by
    intro r
    induction r with
    | zero =>
      intro _
      simpa [hst'] using heH_walk
    | succ r ih =>
      intro hr
      set p := U.length - (r + 1)
      have hp_lt : p < U.length := by omega
      have hsucc : U.length - r = p + 1 := by omega
      have ih' := ih (by omega)
      rw [hsucc, ← Nat.add_assoc] at ih'
      have heG_p1 : eG ∈ (G₀.applyBatch (us.take (k₀ + p + 1))).E := by
        obtain ⟨hBV_end, hds_end, _⟩ := batchIsValid_take us G₀ (k₀ + U.length) hBV hds
        have htake_eq : us.take (k₀ + U.length) =
            us.take (k₀ + p + 1) ++ (us.take (k₀ + U.length)).drop (k₀ + p + 1) := by
          have h1 : (us.take (k₀ + U.length)).take (k₀ + p + 1) = us.take (k₀ + p + 1) := by
            rw [List.take_take, min_eq_left (by omega)]
          rw [← h1]; exact (List.take_append_drop _ _).symm
        have hBV_split := (batchIsValid_append G₀ (us.take (k₀ + p + 1)) _).mp
          (htake_eq ▸ hBV_end)
        have hds1 : ∀ x ∈ us.take (k₀ + p + 1), isDelOrSplit x := fun x hx =>
          hds_end x (by rw [htake_eq]; exact List.mem_append_left _ hx)
        have hds2 : ∀ x ∈ (us.take (k₀ + U.length)).drop (k₀ + p + 1), isDelOrSplit x := fun x hx =>
          hds_end x (by rw [htake_eq]; exact List.mem_append_right _ hx)
        have hV1 := (batch_delOrSplit_invariants _ G₀ hVG₀ hBV_split.1 hds1).1
        have hSub := (batch_delOrSplit_invariants _ _ hV1 hBV_split.2 hds2).2.1
        rw [← applyBatch_append, ← htake_eq] at hSub
        exact hSub heG_end
      have hstep := reembed_step_spec hVG₀ hL hq hGm₀ hSpec hBV hds (k := k₀ + p) (by omega)
        eG heG_p1 eH ih' (heH_not_step p hp_lt)
      simpa [Nat.add_assoc] using hstep
  simpa using hback U.length le_rfl

/-- State after processing the first `t` batches of `Us`. -/
def runBatchState {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) : ℕ → DynSpannerState L
  | 0 => (init G₀ L q sparsify).state
  | t + 1 =>
    match Us[t]? with
    | some U => (update (runBatchState G₀ q sparsify Us t) U sparsify).state
    | none => runBatchState G₀ q sparsify Us t

/-- Batch output emitted on batch `t` (`Us[t]`) starting from `runBatchState ... t`. -/
def runBatchStepOut {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) (t : ℕ) : StepOut L :=
  match Us[t]? with
  | some U => update (runBatchState G₀ q sparsify Us t) U sparsify
  | none => ⟨runBatchState G₀ q sparsify Us t, [], ∅, 0⟩

/-- Number of single updates across the first `t` batches of `Us`. -/
def batchPrefixLen (Us : List (List Update)) (t : ℕ) : ℕ :=
  (Us.take t).flatten.length

private theorem batchPrefixLen_succ {Us : List (List Update)} {t : ℕ} {U : List Update}
    (ht : Us[t]? = some U) :
    batchPrefixLen Us (t + 1) = batchPrefixLen Us t + U.length := by
  simp [batchPrefixLen, take_succ_of_getElem? ht, List.flatten_append]

private theorem batchPrefixLen_le (Us : List (List Update)) (t : ℕ) :
    batchPrefixLen Us t ≤ Us.flatten.length := by
  have h1 : Us = Us.take t ++ Us.drop t := (List.take_append_drop t Us).symm
  conv_rhs => rw [h1, List.flatten_append, List.length_append]
  exact Nat.le_add_right _ _

private theorem getElem?_flatten_of_take_succ {Us : List (List Update)} {t : ℕ} {U : List Update}
    (ht : Us[t]? = some U) :
    ∀ (i : ℕ) (hi : i < U.length), Us.flatten[batchPrefixLen Us t + i]? = some (U[i]'hi) := by
  intro i hi
  have hsplit : Us = Us.take (t + 1) ++ Us.drop (t + 1) := (List.take_append_drop (t + 1) Us).symm
  have hflat : Us.flatten =
      (Us.take t).flatten ++ U ++ (Us.drop (t + 1)).flatten := by
    conv_lhs => rw [hsplit, take_succ_of_getElem? ht, List.flatten_append, List.flatten_append]
    simp [List.append_assoc]
  rw [hflat, List.append_assoc]
  have hlt_pref : (Us.take t).flatten.length ≤ batchPrefixLen Us t + i := by
    simp [batchPrefixLen]
  rw [List.getElem?_append_right hlt_pref]
  have hidx : batchPrefixLen Us t + i - (Us.take t).flatten.length = i := by
    simp [batchPrefixLen]
  rw [hidx, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

/-- Correspondence between the iterated batch driver `runBatchState` / `runBatchStepOut` over `Us`
and the flat single-update trace `Us.flatten`, together with all correctness and Item 3 guarantees. -/
theorem batchTrace_spec {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {Us : List (List Update)}
    (hBV : G₀.BatchIsValid Us.flatten) (hds : ∀ u ∈ Us.flatten, isDelOrSplit u) :
    (∀ t ≤ Us.length,
      runBatchState (L := L) G₀ q sparsify Us t =
        runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t) ∧
      (runBatchState (L := L) G₀ q sparsify Us t).G =
        G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t)) ∧
      Embedding.IsEmbedding (piTotal (runBatchState (L := L) G₀ q sparsify Us t))
        (runBatchState (L := L) G₀ q sparsify Us t).G
        (runBatchState (L := L) G₀ q sparsify Us t).H ∧
      (Embedding.length (piTotal (runBatchState (L := L) G₀ q sparsify Us t))
        (runBatchState (L := L) G₀ q sparsify Us t).G : ℝ) ≤ lenBound P.γ_ℓ L ∧
      Embedding.vcong (piTotal (runBatchState (L := L) G₀ q sparsify Us t))
        (runBatchState (L := L) G₀ q sparsify Us t).G
        (runBatchState (L := L) G₀ q sparsify Us t).H (fun _ => 1) ≤
        vcongBound P.γ_c P.γ_ℓ G₀.maxDeg L) ∧
    (∀ t < Us.length, ∀ U, Us[t]? = some U →
      let st := runBatchState (L := L) G₀ q sparsify Us t
      let res := runBatchStepOut (L := L) G₀ q sparsify Us t
      let k₀ := batchPrefixLen Us t
      res = update (runState (L := L) G₀ q sparsify Us.flatten k₀) U sparsify ∧
      res.state = runBatchState (L := L) G₀ q sparsify Us (t + 1) ∧
      st.H.BatchIsValid res.UH ∧
      st.H.applyBatch res.UH = res.state.H ∧
      res.D ⊆ res.state.H.E ∧
      (∀ eG ∈ res.state.G.E, ∀ eH,
        eH ∈ walkEdges (piTotal res.state eG) → eH ∉ res.D →
        eH ∈ walkEdges (piTotal st eG))) := by
  have hState_eq : ∀ t ≤ Us.length,
      runBatchState (L := L) G₀ q sparsify Us t =
        runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t) := by
    intro t
    induction t with
    | zero => intro _; simp [runBatchState, runState, batchPrefixLen]
    | succ t ih =>
      intro ht
      have hlt : t < Us.length := Nat.lt_of_succ_le ht
      have ht_some : Us[t]? = some (Us[t]'hlt) := List.getElem?_eq_getElem hlt
      have hlen_le : batchPrefixLen Us t + (Us[t]'hlt).length ≤ Us.flatten.length := by
        rw [← batchPrefixLen_succ ht_some]
        exact batchPrefixLen_le Us (t + 1)
      have hub := update_batch_spec hVG₀ hL hq hGm₀ hSpec hBV hds hlen_le
        (getElem?_flatten_of_take_succ ht_some)
      simp only [runBatchState, ht_some, ih (Nat.le_of_lt hlt)]
      rw [hub.1, ← batchPrefixLen_succ ht_some]
  constructor
  · intro t ht
    have hst := hState_eq t ht
    have hlen_le := batchPrefixLen_le Us t
    have hinv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (batchPrefixLen Us t) hlen_le).1
    have hemb := (lemma_5_6 hVG₀ hL hq hGm₀ hSpec hBV hds (k := batchPrefixLen Us t) hlen_le).2
    have hvc := (claim_5_7 hVG₀ hL hq hGm₀ hSpec hBV hds (k := batchPrefixLen Us t) hlen_le).2
    have hlen := claim_5_8 hVG₀ hL hq hGm₀ hSpec hBV hds hlen_le ⟨L, Nat.lt_succ_self L⟩
    rw [hst, hinv.G_eq]
    exact ⟨rfl, rfl, hemb, hlen, hvc⟩
  · intro t ht U ht_some
    have hst := hState_eq t (Nat.le_of_lt ht)
    have hlen_le : batchPrefixLen Us t + U.length ≤ Us.flatten.length := by
      rw [← batchPrefixLen_succ ht_some]
      exact batchPrefixLen_le Us (t + 1)
    have hmatch := getElem?_flatten_of_take_succ ht_some
    have hub := update_batch_spec hVG₀ hL hq hGm₀ hSpec hBV hds hlen_le hmatch
    have hre := reembed_batch_spec hVG₀ hL hq hGm₀ hSpec hBV hds hlen_le hmatch
    have hres_eq : runBatchStepOut (L := L) G₀ q sparsify Us t =
        update (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t)) U sparsify := by
      simp [runBatchStepOut, ht_some, hst]
    have hres_st : (runBatchStepOut (L := L) G₀ q sparsify Us t).state =
        runBatchState (L := L) G₀ q sparsify Us (t + 1) := by
      simp [runBatchStepOut, runBatchState, ht_some]
    refine ⟨hres_eq, hres_st, ?_, ?_, ?_, ?_⟩
    · rw [hst, hres_eq]; exact hub.2.1
    · rw [hst, hres_eq]; exact hub.2.2.1
    · rw [hres_eq]; exact hub.2.2.2.1
    · intro eG heG eH heH hnotD
      rw [hres_eq] at heG heH hnotD
      rw [hst]
      exact hre eG heG eH heH hnotD

private theorem prefixWalk_fst_eq_of_snd_nil (H : MGraph) (a : ℕ) (w : List (ℕ × Bool))
    (S : Finset ℕ) (h : (prefixWalk H a w S).2 = []) :
    (prefixWalk H a w S).1 = a := by
  cases w with
  | nil =>
    unfold prefixWalk
    split_ifs <;> rfl
  | cons x xs =>
    unfold prefixWalk at h ⊢
    by_cases ha : a ∈ S
    · simp [ha]
    · simp [ha] at h

private theorem dropLast_map {α β : Type*} (f : α → β) :
    ∀ xs : List α, xs.dropLast.map f = (xs.map f).dropLast
  | [] => rfl
  | [_] => rfl
  | _ :: y :: xs => by
    simp [List.dropLast, dropLast_map f (y :: xs)]

private theorem walkVertices_dropLast_append_end {G : MGraph} :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)},
      G.IsWalk a b P → (G.walkVertices a P).dropLast ++ [b] = G.walkVertices a P
  | _, _, [], h => by cases h; rfl
  | a, b, x :: xs, .cons _ _ hw => by
    have ih := walkVertices_dropLast_append_end hw
    simp only [MGraph.walkVertices, List.map_cons] at ih ⊢
    rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
    simpa [List.cons_append] using congrArg (a :: ·) ih

private theorem take_append_dropLast_drop {α : Type*} {xs : List α} {a b : ℕ}
    (hnd : xs.Nodup) (hle : a ≤ b) :
    List.Disjoint (xs.take a) (xs.drop b) := by
  have h1 : xs = xs.take a ++ xs.drop a := (List.take_append_drop a xs).symm
  have hdisj : List.Disjoint (xs.take a) (xs.drop a) := by
    rw [h1] at hnd
    exact List.disjoint_of_nodup_append hnd
  intro z hza hzb
  refine hdisj hza ?_
  have hsub : xs.drop b = (xs.drop a).drop (b - a) := by
    rw [List.drop_drop, Nat.add_sub_cancel' hle]
  rw [hsub] at hzb
  exact List.mem_of_mem_drop hzb

private theorem walkVertices_append_eq {G : MGraph} {a b : ℕ} {P Q : List (ℕ × Bool)}
    (hP : G.IsWalk a b P) :
    G.walkVertices a (P ++ Q) = (G.walkVertices a P).dropLast ++ G.walkVertices b Q := by
  induction hP with
  | nil u => simp [MGraph.walkVertices]
  | @cons u' _ x P' _ _ _ ih =>
    simp only [MGraph.walkVertices, List.map_cons, List.cons_append, List.map_append] at ih ⊢
    rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
    exact congrArg (u' :: ·) ih

private theorem walkVertices_walkRev_tail {G : MGraph} {d c : ℕ} {q : List (ℕ × Bool)}
    (hq : G.IsWalk d c q) :
    (walkRev q).map G.dst = (G.walkVertices d q).dropLast.reverse := by
  have hrev := walkVertices_walkRev hq
  have hdl : G.walkVertices d q = (G.walkVertices d q).dropLast ++
      [(G.walkVertices d q).getLast (by simp [MGraph.walkVertices])] :=
    (List.dropLast_append_getLast (by simp [MGraph.walkVertices])).symm
  have htail := congrArg List.tail hrev
  conv_rhs at htail => rw [hdl, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.tail_cons]
  simpa [MGraph.walkVertices] using htail

private theorem isWalk_congr_ends {H₁ H₂ : MGraph} {a b : ℕ} {P : List (ℕ × Bool)}
    (hP : H₁.IsWalk a b P) (hE : ∀ x ∈ P, x.1 ∈ H₂.E)
    (hT : ∀ x ∈ P, H₂.tail x.1 = H₁.tail x.1) (hH : ∀ x ∈ P, H₂.head x.1 = H₁.head x.1) :
    H₂.IsWalk a b P := by
  induction hP with
  | nil u => exact .nil u
  | @cons u' _ x P' hx hsrc hrest ih =>
    have hmem : ∀ y ∈ P', y ∈ x :: P' := fun y hy => List.mem_cons_of_mem _ hy
    have hTx := hT x List.mem_cons_self
    have hHx := hH x List.mem_cons_self
    refine .cons (hE x List.mem_cons_self) ?_ (by
      rw [show H₂.dst x = H₁.dst x by cases xb : x.2 <;> simp [MGraph.dst, xb, hTx, hHx]]
      exact ih (fun y hy => hE y (hmem y hy)) (fun y hy => hT y (hmem y hy))
        (fun y hy => hH y (hmem y hy)))
    cases xb : x.2 <;> simpa [MGraph.src, xb, hTx, hHx] using hsrc

private theorem step_isPath_eAff {G_r H_lt_r H_lt G' stH : MGraph} {delta : List Update}
    {S_prev E_aff : Finset ℕ} {pi_r piLt_mid : Embedding}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {mMax i G₀_maxDeg : ℕ} {P : SparsifyParams}
    (hSpec : SparsifySpec mMax P sparsify)
    (hVG_r : G_r.IsValid) (hBV_d : G_r.BatchIsValid delta) (hds_d : ∀ u ∈ delta, isDelOrSplit u)
    (hVG' : G'.IsValid) (hG_r_m : G_r.m ≤ mMax) (hG'_delta : G' = G_r.applyBatch delta)
    (hSub_lt_r : G_r.IsSubgraph H_lt_r) (hSub_lt : G'.IsSubgraph H_lt)
    (hHLt_V : H_lt.V = G'.V) (hHLt_E : H_lt.E = H_lt_r.E ∩ G'.E)
    (hHLt_tail : H_lt.tail = G'.tail) (hHLt_head : H_lt.head = G'.head)
    (hEmbr : Embedding.IsEmbedding pi_r G_r H_lt_r)
    (hLenr : (Embedding.length pi_r G_r : ℝ) ≤ lenBound P.γ_ℓ i)
    (hVcr : Embedding.vcong pi_r G_r H_lt_r (fun _ => 1) ≤ vcongBound P.γ_c P.γ_ℓ G₀_maxDeg i)
    (hTouch_r : allTouched G_r delta ⊆ S_prev)
    (hpi_eq : ∀ e' ∈ G'.E, piLt_mid e' = pi_r e')
    (hE_aff : E_aff = affectedEdges G' H_lt piLt_mid S_prev)
    (hHlt_sub_stH : H_lt.E ⊆ stH.E)
    {e : ℕ} (heAff : e ∈ E_aff)
    (hNodup_r : (H_lt_r.walkVertices (G_r.tail e) (pi_r e)).Nodup)
    (hDisj : Disjoint
      ((if E_aff.Nonempty then sparsify (buildAuxHost G' H_lt E_aff)
          (buildProjGraph G' H_lt piLt_mid S_prev E_aff) (projWalk G' H_lt piLt_mid S_prev)
        else ⟨buildProjGraph G' H_lt piLt_mid S_prev E_aff, idEmb, 0⟩).Jtilde.E.biUnion
        fun e' => walkEdges (projWalk G' H_lt piLt_mid S_prev e'))
      stH.E) :
    let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    let H_aux := buildAuxHost G' H_lt E_aff
    let embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
    let out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
    let outEmb : Embedding := fun e' => shortcutWalk out.Jtilde (J.tail e') (out.emb e')
    let embMid : Embedding := Embedding.comp embJH outEmb
    (G'.walkVertices (G'.tail e) (reembedWalk G' H_lt piLt_mid embMid S_prev e)).Nodup := by
  intro J H_aux embJH out outEmb embMid
  have hinv_d := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
  have hEnds_lt : ∀ e' ∈ H_lt_r.E,
      H_lt.tail e' = (G_r.applyBatch delta).tail e' ∧
      H_lt.head e' = (G_r.applyBatch delta).head e' := fun _ _ => by
    rw [hHLt_tail, hHLt_head, hG'_delta]; exact ⟨rfl, rfl⟩
  have hHLt_V_delta : H_lt.V = (G_r.applyBatch delta).V := hG'_delta ▸ hHLt_V
  have hHLt_E_delta : H_lt.E = H_lt_r.E ∩ (G_r.applyBatch delta).E := hG'_delta ▸ hHLt_E
  have hSub_lt_delta : (G_r.applyBatch delta).IsSubgraph H_lt := hG'_delta ▸ hSub_lt
  have hPW := projWalk_spec (i := i) hSpec hVG_r hBV_d hds_d hG_r_m hSub_lt_r hEmbr hLenr hVcr
    (vcongBound_nonneg (by linarith [P.hγ_c]) (by linarith [P.hγ_ℓ]) G₀_maxDeg i)
    (vcongBound_step P.hγ_c P.hγ_ℓ G₀_maxDeg i)
    hHLt_V_delta hHLt_E_delta (hG'_delta ▸ hHLt_tail) (hG'_delta ▸ hHLt_head)
    hSub_lt_delta hTouch_r (fun e' he' => hpi_eq e' (hG'_delta ▸ he'))
  dsimp only at hPW
  rw [← hG'_delta, ← hE_aff] at hPW
  rcases hPW with ⟨_, _, _, hOut_aff, _, _, _, _, _, _, _, _, _, _, _, hOut_emb, -⟩
  have hEne : E_aff.Nonempty := ⟨e, heAff⟩
  have hAux_valid : H_aux.IsValid := fun e' he' => by
    simp only [H_aux, buildAuxHost, Finset.mem_union] at he'
    rcases he' with he' | he'
    · exact hVG' e' (hSub_lt.2.1 he')
    · exact hVG' e' (by rw [hE_aff] at he'; exact (Finset.mem_filter.mp he').1)
  have hJ_valid : J.IsValid := fun e' he' => by
    refine ⟨?_, ?_⟩ <;>
    · simp only [J, buildProjGraph, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨e', he', by simp⟩
  have hJ_m_le : J.m ≤ mMax := by
    change E_aff.card ≤ mMax
    exact le_trans (Finset.card_le_card (Finset.Subset.trans
      (by rw [hE_aff]; exact Finset.filter_subset _ _) (hG'_delta ▸ hinv_d.2.1))) hG_r_m
  have hPref_any : ∀ e' ∈ E_aff,
      let res1 := prefixWalk H_lt (G'.tail e') (piLt_mid e') S_prev
      let res2 := prefixWalk H_lt (G'.head e') (walkRev (piLt_mid e')) S_prev
      res1.1 ∈ S_prev ∧ res1.1 ∈ G'.V ∧ H_lt.IsWalk (G'.tail e') res1.1 res1.2 ∧
      res1.2 <+: piLt_mid e' ∧
      (∀ z ∈ (H_lt.walkVertices (G'.tail e') res1.2).dropLast, z ∉ S_prev ∧ z ∈ G_r.V ∧ batchAnc delta z = z) ∧
      res2.1 ∈ S_prev ∧ res2.1 ∈ G'.V ∧ H_lt.IsWalk (G'.head e') res2.1 res2.2 ∧
      res2.2 <+: walkRev (piLt_mid e') ∧
      (∀ z ∈ (H_lt.walkVertices (G'.head e') res2.2).dropLast, z ∉ S_prev ∧ z ∈ G_r.V ∧ batchAnc delta z = z) ∧
      res1.2.length + res2.2.length ≤ (piLt_mid e').length := by
    intro e' he'Aff
    have he'Aff0 := hE_aff ▸ he'Aff
    have he'G' : e' ∈ G'.E := (Finset.mem_filter.mp he'Aff0).1
    have he'Gr : e' ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ he'G')
    have hEmbr' := hEmbr.2 e' he'Gr
    have hanc' := hinv_d.2.2.2.2.2.2 e' he'Gr
    have hHit' : ∃ z ∈ H_lt.walkVertices (G'.tail e') (pi_r e'), z ∈ S_prev := by
      have hf := Finset.mem_filter.mp he'Aff0
      rw [hpi_eq e' he'G'] at hf
      exact decide_eq_true_eq.mp hf.2
    have hVw1' := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge hEmbr') (by rw [← hG'_delta]; exact (hVG' e' he'G').1)
    have hVw2' := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge (isWalk_walkRev hEmbr')) (by rw [← hG'_delta]; exact (hVG' e' he'G').2)
    have hHitRev' : ∃ z ∈ H_lt.walkVertices (G'.head e') (walkRev (pi_r e')), z ∈ S_prev := by
      obtain ⟨z, hz, hzS⟩ := hHit'
      have hz_ex := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
        hTouch_r (IsWalk.mem_edge hEmbr')
        (by rw [← hG'_delta]; exact (hVG' e' he'G').1)
        (a₀ := G_r.tail e') (by rw [hG'_delta]; exact hanc'.1) hVw1').mp ⟨z, hz, hzS⟩
      obtain ⟨z₀, hz₀, hz₀S⟩ := hz_ex
      exact (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
        hTouch_r (IsWalk.mem_edge (isWalk_walkRev hEmbr'))
        (by rw [← hG'_delta]; exact (hVG' e' he'G').2)
        (a₀ := G_r.head e') (by rw [hG'_delta]; exact hanc'.2) hVw2').mpr
        ⟨z₀, (mem_walkVertices_walkRev hEmbr' z₀).mpr hz₀, hz₀S⟩
    have hp1' := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta hHLt_V_delta
      hHLt_E_delta hEnds_lt hTouch_r (pi_r e') (G_r.tail e') (G_r.head e')
      (G'.tail e') (hVG_r e' he'Gr).1 (hVG_r e' he'Gr).2 hEmbr'
      (by rw [← hG'_delta]; exact (hVG' e' he'G').1)
      (by rw [hG'_delta]; exact hanc'.1)).2 hHit'
    have hq2' := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta hHLt_V_delta
      hHLt_E_delta hEnds_lt hTouch_r (walkRev (pi_r e')) (G_r.head e') (G_r.tail e')
      (G'.head e') (hVG_r e' he'Gr).2 (hVG_r e' he'Gr).1 (isWalk_walkRev hEmbr')
      (by rw [← hG'_delta]; exact (hVG' e' he'G').2)
      (by rw [hG'_delta]; exact hanc'.2)).2 hHitRev'
    have hpq' := prefixWalk_length_add_le hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta
      hHLt_V_delta hHLt_E_delta hEnds_lt hTouch_r
      (hVG_r e' he'Gr).1 (hVG_r e' he'Gr).2 hEmbr'
      (by rw [← hG'_delta]; exact (hVG' e' he'G').1)
      (by rw [← hG'_delta]; exact (hVG' e' he'G').2)
      (a₀ := G_r.tail e') (b₀ := G_r.head e')
      (by rw [hG'_delta]; exact hanc'.1) (by rw [hG'_delta]; exact hanc'.2) hHit' hHitRev'
    rw [← hpi_eq e' he'G'] at hp1' hq2' hpq'
    rw [← hG'_delta] at hp1' hq2'
    exact ⟨hp1'.1, hp1'.2.1, hp1'.2.2.1, hp1'.2.2.2.1, hp1'.2.2.2.2.2,
      hq2'.1, hq2'.2.1, hq2'.2.2.1, hq2'.2.2.2.1, hq2'.2.2.2.2.2, hpq'⟩
  have hEmbJH_valid : Embedding.IsEmbedding embJH J H_aux := by
    have hsub_aux : H_aux.IsSubgraph H_lt :=
      ⟨hHLt_V ▸ Finset.Subset.rfl, Finset.subset_union_left,
        fun _ _ => ⟨congrFun hHLt_tail _, congrFun hHLt_head _⟩⟩
    refine ⟨?_, fun e' he'Aff => ?_⟩
    · intro v hv
      simp only [J, buildProjGraph, Finset.mem_biUnion, Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with ⟨e', he'Aff, rfl | rfl⟩
      · exact (hPref_any e' he'Aff).2.1
      · exact (hPref_any e' he'Aff).2.2.2.2.2.2.1
    · have hp := hPref_any e' he'Aff
      have hw1 : H_aux.IsWalk (J.tail e') (G'.tail e')
          (walkRev (prefixWalk H_lt (G'.tail e') (piLt_mid e') S_prev).2) :=
        IsWalk.of_isSubgraph hsub_aux (isWalk_walkRev hp.2.2.1)
      have hw_e : H_aux.IsWalk (G'.tail e') (G'.head e') [(e', true)] :=
        .cons (Finset.mem_union_right _ he'Aff) rfl (.nil _)
      have hw2 : H_aux.IsWalk (G'.head e') (J.head e')
          (prefixWalk H_lt (G'.head e') (walkRev (piLt_mid e')) S_prev).2 :=
        IsWalk.of_isSubgraph hsub_aux hp.2.2.2.2.2.2.2.1
      simpa [embJH, projWalk, List.append_assoc] using IsWalk.append (IsWalk.append hw1 hw_e) hw2
  have hLen1_J : J.E.Nonempty → 1 ≤ Embedding.length embJH J := fun _ => by
    have hge : 1 ≤ (embJH e).length := by
      simp only [embJH, projWalk, List.length_append, List.length_cons, List.length_nil]
      omega
    exact le_trans hge (Finset.le_sup (f := fun e' => (embJH e').length) heAff)
  have hSpOut := hSpec H_aux J embJH hAux_valid hJ_valid hJ_m_le hLen1_J hEmbJH_valid
  have hJsub : J.IsSubgraph out.Jtilde := by
    simpa [out, hEne] using hSpOut.1
  have he'_prop : ∀ e' ∈ out.Jtilde.E,
      (prefixWalk H_lt (G'.tail e') (piLt_mid e') S_prev).2 = [] ∧
      (prefixWalk H_lt (G'.head e') (walkRev (piLt_mid e')) S_prev).2 = [] ∧
      embJH e' = [(e', true)] ∧
      G'.tail e' ∈ S_prev ∧ G'.head e' ∈ S_prev ∧
      J.tail e' = G'.tail e' ∧ J.head e' = G'.head e' := by
    intro e' he'
    have he'Aff : e' ∈ E_aff := hOut_aff he'
    have hp := hPref_any e' he'Aff
    have hp_nil : (prefixWalk H_lt (G'.tail e') (piLt_mid e') S_prev).2 = [] := by
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      have hxH : x.1 ∈ H_lt.E := IsWalk.mem_edge hp.2.2.1 x hx
      have hxD : x.1 ∈ out.Jtilde.E.biUnion fun e'' => walkEdges (embJH e'') := by
        refine Finset.mem_biUnion.mpr ⟨e', he', mem_walkEdges_iff.mpr ⟨(x.1, !x.2), ?_, rfl⟩⟩
        simp only [embJH, projWalk, List.mem_append]
        left; left
        exact List.mem_reverse.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Finset.disjoint_left.mp hDisj hxD (hHlt_sub_stH hxH)
    have hq_nil : (prefixWalk H_lt (G'.head e') (walkRev (piLt_mid e')) S_prev).2 = [] := by
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      have hxH : x.1 ∈ H_lt.E := IsWalk.mem_edge hp.2.2.2.2.2.2.2.1 x hx
      have hxD : x.1 ∈ out.Jtilde.E.biUnion fun e'' => walkEdges (embJH e'') := by
        refine Finset.mem_biUnion.mpr ⟨e', he', mem_walkEdges_iff.mpr ⟨x, ?_, rfl⟩⟩
        simp [embJH, projWalk, List.mem_append, hx]
      exact Finset.disjoint_left.mp hDisj hxD (hHlt_sub_stH hxH)
    have hemb' : embJH e' = [(e', true)] := by
      dsimp only [embJH, projWalk]
      rw [hp_nil, hq_nil]
      simp [walkRev]
    have hft : (prefixWalk H_lt (G'.tail e') (piLt_mid e') S_prev).1 = G'.tail e' :=
      prefixWalk_fst_eq_of_snd_nil _ _ _ _ hp_nil
    have hfh : (prefixWalk H_lt (G'.head e') (walkRev (piLt_mid e')) S_prev).1 = G'.head e' :=
      prefixWalk_fst_eq_of_snd_nil _ _ _ _ hq_nil
    exact ⟨hp_nil, hq_nil, hemb', hft ▸ hp.1, hfh ▸ hp.2.2.2.2.2.1, hft, hfh⟩
  have hp_e := hPref_any e heAff
  set p₁ := (prefixWalk H_lt (G'.tail e) (piLt_mid e) S_prev).2
  set q₂ := (prefixWalk H_lt (G'.head e) (walkRev (piLt_mid e)) S_prev).2
  set v₁ := (prefixWalk H_lt (G'.tail e) (piLt_mid e) S_prev).1
  set v₂ := (prefixWalk H_lt (G'.head e) (walkRev (piLt_mid e)) S_prev).1
  have hOut_walk_e : out.Jtilde.IsWalk v₁ v₂ (outEmb e) := hOut_emb.2 e heAff
  have hOut_nodup_e : (out.Jtilde.walkVertices v₁ (outEmb e)).Nodup := by
    change (out.Jtilde.walkVertices (J.tail e) (shortcutWalk out.Jtilde (J.tail e) (out.emb e))).Nodup
    exact shortcutWalk_nodup out.Jtilde (out.emb e) (J.tail e)
  have hOut_ends_e : ∀ x ∈ outEmb e,
      out.Jtilde.tail x.1 = G'.tail x.1 ∧ out.Jtilde.head x.1 = G'.head x.1 ∧
      G'.tail x.1 ∈ S_prev ∧ G'.head x.1 ∈ S_prev ∧ embJH x.1 = [(x.1, true)] := by
    intro x hx
    have hxE : x.1 ∈ out.Jtilde.E := IsWalk.mem_edge hOut_walk_e x hx
    obtain ⟨_, _, hembx, htxS, hhxS, hJtx, hJhx⟩ := he'_prop x.1 hxE
    obtain ⟨htJ, hhJ⟩ := hJsub.2.2 x.1 hxE
    exact ⟨htJ.trans hJtx, hhJ.trans hJhx, htxS, hhxS, hembx⟩
  have hOut_inS : ∀ z ∈ out.Jtilde.walkVertices v₁ (outEmb e), z ∈ S_prev := by
    intro z hz
    simp only [MGraph.walkVertices, List.mem_cons, List.mem_map] at hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · exact hp_e.1
    · obtain ⟨ht, hh, hts, hhs, _⟩ := hOut_ends_e x hx
      cases xb : x.2 <;> simp [MGraph.dst, xb, ht, hh, hts, hhs]
  have hEmbMid_eq : embMid e = outEmb e := by
    dsimp only [embMid, Embedding.comp]
    calc (outEmb e).flatMap (fun x => if x.2 then embJH x.1 else walkRev (embJH x.1))
        = (outEmb e).flatMap (fun x => [x]) := by
            refine List.flatMap_congr fun x hx => ?_
            rw [(hOut_ends_e x hx).2.2.2.2]
            rcases x with ⟨eid, true | false⟩ <;> simp [walkRev]
      _ = outEmb e := by induction outEmb e <;> simp [*]
  have hWV_decomp :
      G'.walkVertices (G'.tail e) (reembedWalk G' H_lt piLt_mid embMid S_prev e) =
        (H_lt.walkVertices (G'.tail e) p₁).dropLast ++
        out.Jtilde.walkVertices v₁ (outEmb e) ++
        (H_lt.walkVertices (G'.head e) q₂).dropLast.reverse := by
    dsimp only [reembedWalk]
    rw [hEmbMid_eq]
    have hp1_G' : G'.IsWalk (G'.tail e) v₁ p₁ :=
      isWalk_congr_ends hp_e.2.2.1 (fun x hx =>
        hSub_lt.2.1 (IsWalk.mem_edge hp_e.2.2.1 x hx))
        (fun _ _ => congrFun hHLt_tail.symm _) (fun _ _ => congrFun hHLt_head.symm _)
    have hOut_G' : G'.IsWalk v₁ v₂ (outEmb e) :=
      isWalk_congr_ends hOut_walk_e
        (fun x hx => (Finset.mem_filter.mp (hE_aff ▸ hOut_aff (IsWalk.mem_edge hOut_walk_e x hx))).1)
        (fun x hx => (hOut_ends_e x hx).1.symm)
        (fun x hx => (hOut_ends_e x hx).2.1.symm)
    have hq2_G' : G'.IsWalk (G'.head e) v₂ q₂ :=
      isWalk_congr_ends hp_e.2.2.2.2.2.2.2.1 (fun x hx =>
        hSub_lt.2.1 (IsWalk.mem_edge hp_e.2.2.2.2.2.2.2.1 x hx))
        (fun _ _ => congrFun hHLt_tail.symm _) (fun _ _ => congrFun hHLt_head.symm _)
    have hwalk12 : G'.IsWalk (G'.tail e) v₂ (p₁ ++ outEmb e) := IsWalk.append hp1_G' hOut_G'
    rw [walkVertices_append_eq hwalk12, walkVertices_append_eq hp1_G']
    have hdrop1 : G'.walkVertices (G'.tail e) p₁ = H_lt.walkVertices (G'.tail e) p₁ := by
      simp [MGraph.walkVertices, MGraph.dst, hHLt_tail, hHLt_head]
    have hmid_wv : G'.walkVertices v₁ (outEmb e) = out.Jtilde.walkVertices v₁ (outEmb e) := by
      simp only [MGraph.walkVertices, List.cons.injEq, true_and]
      refine List.map_congr_left fun x hx => ?_
      obtain ⟨ht, hh, _⟩ := hOut_ends_e x hx
      cases x.2 <;> simp [MGraph.dst, ht, hh]
    have hrev_tail :
        G'.walkVertices v₂ (walkRev q₂) =
          v₂ :: (H_lt.walkVertices (G'.head e) q₂).dropLast.reverse := by
      have htail := walkVertices_walkRev_tail hq2_G'
      have hq_wv : G'.walkVertices (G'.head e) q₂ = H_lt.walkVertices (G'.head e) q₂ := by
        simp [MGraph.walkVertices, MGraph.dst, hHLt_tail, hHLt_head]
      rw [hq_wv] at htail
      simp [MGraph.walkVertices, htail]
    have hdrop12 :
        ((G'.walkVertices (G'.tail e) p₁).dropLast ++ G'.walkVertices v₁ (outEmb e)).dropLast =
          (G'.walkVertices (G'.tail e) p₁).dropLast ++
          (G'.walkVertices v₁ (outEmb e)).dropLast :=
      List.dropLast_append_of_ne_nil (by simp [MGraph.walkVertices])
    have hmid_all :
        (G'.walkVertices v₁ (outEmb e)).dropLast ++ [v₂] = G'.walkVertices v₁ (outEmb e) :=
      walkVertices_dropLast_append_end hOut_G'
    rw [hdrop12]
    rw [show (G'.walkVertices (G'.tail e) p₁).dropLast ++ (G'.walkVertices v₁ (outEmb e)).dropLast ++
          G'.walkVertices v₂ (walkRev q₂) =
        (G'.walkVertices (G'.tail e) p₁).dropLast ++
          ((G'.walkVertices v₁ (outEmb e)).dropLast ++ [v₂]) ++
          (H_lt.walkVertices (G'.head e) q₂).dropLast.reverse by
      rw [hrev_tail]; simp [List.append_assoc]]
    rw [hmid_all, hdrop1, hmid_wv]
  have heAff0 := hE_aff ▸ heAff
  have heG' : e ∈ G'.E := (Finset.mem_filter.mp heAff0).1
  have heGr : e ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ heG')
  have hEmbr_e := hEmbr.2 e heGr
  have hanc_e := hinv_d.2.2.2.2.2.2 e heGr
  have hpi_r_eq := hpi_eq e heG'
  set xs := H_lt_r.walkVertices (G_r.tail e) (pi_r e)
  have hpref_take : ∀ (a : ℕ) (P w : List (ℕ × Bool)), P <+: w →
      (H_lt_r.walkVertices a P).dropLast = (H_lt_r.walkVertices a w).take P.length := by
    intro a P w ⟨rest, hrest⟩
    subst hrest
    induction P generalizing a with
    | nil => simp [MGraph.walkVertices]
    | cons x xs' ih =>
      simp only [MGraph.walkVertices, List.cons_append, List.map_cons, List.map_append,
        List.length_cons] at ih ⊢
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
      simpa [MGraph.walkVertices] using congrArg (a :: ·) (ih (H_lt_r.dst x))
  have hp_sub : p₁ <+: pi_r e := by rw [← hpi_r_eq]; exact hp_e.2.2.2.1
  have hq_sub : q₂ <+: walkRev (pi_r e) := by rw [← hpi_r_eq]; exact hp_e.2.2.2.2.2.2.2.2.1
  have hp1_eq_take :
      (H_lt.walkVertices (G'.tail e) p₁).dropLast = xs.take p₁.length := by
    have hpEdges : ∀ x ∈ p₁, x.1 ∈ H_lt_r.E := fun x hx =>
      IsWalk.mem_edge hEmbr_e x (hp_sub.mem hx)
    have hpMap := walkVertices_batchAnc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hpEdges
      (a := G'.tail e) (a₀ := G_r.tail e) (by rw [hG'_delta]; exact hanc_e.1)
    have hmap_drop := dropLast_map (batchAnc delta) (H_lt.walkVertices (G'.tail e) p₁)
    have hid : ((H_lt.walkVertices (G'.tail e) p₁).dropLast).map (batchAnc delta) =
        (H_lt.walkVertices (G'.tail e) p₁).dropLast := by
      calc ((H_lt.walkVertices (G'.tail e) p₁).dropLast).map (batchAnc delta)
          = ((H_lt.walkVertices (G'.tail e) p₁).dropLast).map id :=
            List.map_congr_left fun z hz => (hp_e.2.2.2.2.1 z hz).2.2
        _ = (H_lt.walkVertices (G'.tail e) p₁).dropLast := List.map_id _
    rw [← hid, hmap_drop, hpMap]
    exact hpref_take (G_r.tail e) p₁ (pi_r e) hp_sub
  have hq2_eq_drop :
      (H_lt.walkVertices (G'.head e) q₂).dropLast.reverse =
        xs.drop ((pi_r e).length + 1 - q₂.length) := by
    have hqEdges : ∀ x ∈ q₂, x.1 ∈ H_lt_r.E := fun x hx =>
      IsWalk.mem_edge (isWalk_walkRev hEmbr_e) x (hq_sub.mem hx)
    have hqMap := walkVertices_batchAnc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hqEdges
      (a := G'.head e) (a₀ := G_r.head e) (by rw [hG'_delta]; exact hanc_e.2)
    have hmap_drop := dropLast_map (batchAnc delta) (H_lt.walkVertices (G'.head e) q₂)
    have hid : ((H_lt.walkVertices (G'.head e) q₂).dropLast).map (batchAnc delta) =
        (H_lt.walkVertices (G'.head e) q₂).dropLast := by
      calc ((H_lt.walkVertices (G'.head e) q₂).dropLast).map (batchAnc delta)
          = ((H_lt.walkVertices (G'.head e) q₂).dropLast).map id :=
            List.map_congr_left fun z hz => (hp_e.2.2.2.2.2.2.2.2.2.1 z hz).2.2
        _ = (H_lt.walkVertices (G'.head e) q₂).dropLast := List.map_id _
    have hdl_eq : (H_lt.walkVertices (G'.head e) q₂).dropLast =
        (H_lt_r.walkVertices (G_r.head e) q₂).dropLast := by
      rw [← hid, hmap_drop, hqMap]
    have htk_rev : (H_lt_r.walkVertices (G_r.head e) q₂).dropLast =
        xs.reverse.take q₂.length := by
      have h1 := hpref_take (G_r.head e) q₂ (walkRev (pi_r e)) hq_sub
      rwa [walkVertices_walkRev hEmbr_e] at h1
    rw [hdl_eq, htk_rev, List.take_reverse, List.reverse_reverse]
    simp [xs, MGraph.walkVertices]
  rw [hWV_decomp, hp1_eq_take, hq2_eq_drop]
  have hnd1 : (xs.take p₁.length).Nodup := hNodup_r.take
  have hnd3 : (xs.drop ((pi_r e).length + 1 - q₂.length)).Nodup := hNodup_r.drop
  have hpq_strict : p₁.length ≤ (pi_r e).length + 1 - q₂.length := by
    have hsum : p₁.length + q₂.length ≤ (piLt_mid e).length := hp_e.2.2.2.2.2.2.2.2.2.2
    have hlen : (piLt_mid e).length = (pi_r e).length := congrArg List.length hpi_r_eq
    omega
  have hdisj13 : List.Disjoint (xs.take p₁.length) (xs.drop ((pi_r e).length + 1 - q₂.length)) :=
    take_append_dropLast_drop hNodup_r hpq_strict
  have hdisj12 : List.Disjoint (xs.take p₁.length) (out.Jtilde.walkVertices v₁ (outEmb e)) := by
    intro z hz1 hz2
    rw [← hp1_eq_take] at hz1
    exact (hp_e.2.2.2.2.1 z hz1).1 (hOut_inS z hz2)
  have hdisj23 : List.Disjoint (out.Jtilde.walkVertices v₁ (outEmb e))
      (xs.drop ((pi_r e).length + 1 - q₂.length)) := by
    intro z hz2 hz3
    rw [← hq2_eq_drop, List.mem_reverse] at hz3
    exact (hp_e.2.2.2.2.2.2.2.2.2.1 z hz3).1 (hOut_inS z hz2)
  rw [List.append_assoc, List.nodup_append, List.nodup_append]
  refine ⟨hnd1, ⟨hOut_nodup_e, hnd3, fun _ ha _ hb hab => hdisj23 ha (hab ▸ hb)⟩, ?_⟩
  intro z hz1 z' hz23 hab
  subst hab
  rcases List.mem_append.mp hz23 with hz2 | hz3
  · exact hdisj12 hz1 hz2
  · exact hdisj13 hz1 hz3

theorem step_isPath_of_disjoint {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ k ≤ us.length,
      (∀ m < k, 0 < chooseLevel L q (m + 1) →
        Disjoint (runStepOut (L := L) G₀ q sparsify us m).D
          (runState (L := L) G₀ q sparsify us m).H.E) →
      (∀ i : Fin (L + 1), chooseLevel L q k ≤ i.1 →
        ∀ e ∈ (G₀.applyBatch (us.take k)).E,
          ((unionGraphLt (runState (L := L) G₀ q sparsify us k).G
            (runState (L := L) G₀ q sparsify us k).H_level (i.1 + 1)).walkVertices
              ((runState (L := L) G₀ q sparsify us k).G.tail e)
              (piLe (runState (L := L) G₀ q sparsify us k) i.1 e)).Nodup) ∧
      ∀ e ∈ (runState (L := L) G₀ q sparsify us k).G.E,
        (runState (L := L) G₀ q sparsify us k).H.IsPath
          ((runState (L := L) G₀ q sparsify us k).G.tail e)
          ((runState (L := L) G₀ q sparsify us k).G.head e)
          (piTotal (runState (L := L) G₀ q sparsify us k) e) := by
  intro k hk hDisj
  have hInd : ∀ n ≤ us.length,
      (∀ m < n, 0 < chooseLevel L q (m + 1) →
        Disjoint (runStepOut (L := L) G₀ q sparsify us m).D
          (runState (L := L) G₀ q sparsify us m).H.E) →
      ∀ i : Fin (L + 1), chooseLevel L q n ≤ i.1 →
        ∀ e ∈ (G₀.applyBatch (us.take n)).E,
          ((unionGraphLt (runState (L := L) G₀ q sparsify us n).G
            (runState (L := L) G₀ q sparsify us n).H_level (i.1 + 1)).walkVertices
              ((runState (L := L) G₀ q sparsify us n).G.tail e)
              (piLe (runState (L := L) G₀ q sparsify us n) i.1 e)).Nodup := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hDisj_n i hi_ch e heGn
      cases n with
      | zero =>
        simp only [List.take_zero, MGraph.applyBatch] at heGn
        change ((unionGraphLt (init (L := L) G₀ q sparsify).state.G
          (init (L := L) G₀ q sparsify).state.H_level (i.1 + 1)).walkVertices _ _).Nodup
        exact initAt_nodup G₀ sparsify i e heGn
      | succ m =>
        have hm_lt : m < us.length := Nat.lt_of_succ_le hn
        have hu_some : us[m]? = some (us[m]'hm_lt) := List.getElem?_eq_getElem hm_lt
        set u := us[m]'hm_lt
        set st := runState (L := L) G₀ q sparsify us m
        set res := runStepOut (L := L) G₀ q sparsify us m
        set st' := runState (L := L) G₀ q sparsify us (m + 1)
        have hres_eq : res = step st u sparsify := by simp [res, runStepOut, hu_some, st, u]
        have hst'_eq : st' = res.state := by simp [st', runState, hu_some, res, hres_eq, st]
        set j := chooseLevel L q (m + 1)
        have hm1_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (m + 1) hn).1
        have hm_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds m (Nat.le_of_lt hm_lt)).1
        rw [hm1_inv.G_eq]
        by_cases hj0 : j = 0
        · have hj_st : chooseLevel L st.q (st.t + 1) = 0 := by
            rw [hm_inv.q_eq, hm_inv.t_eq]; exact hj0
          have heG' : e ∈ (st.G.applyUpdate u).E := by
            have hGs : st.G.applyUpdate u = G₀.applyBatch (us.take (m + 1)) := by
              rw [hm_inv.G_eq, take_succ_of_getElem? hu_some, applyBatch_append]
              rfl
            exact hGs ▸ heGn
          set resI := initAt (st.G.applyUpdate u) L st.q (st.t + 1) sparsify
          have hst'_G : st'.G = resI.state.G := by
            rw [hst'_eq, hres_eq]; dsimp only [step]; simp [hj_st, resI]
          have hst'_Hl : st'.H_level = resI.state.H_level := by
            rw [hst'_eq, hres_eq]; dsimp only [step]; simp [hj_st, resI]
          have hst'_Pi : st'.Pi_level = resI.state.Pi_level := by
            rw [hst'_eq, hres_eq]; dsimp only [step]; simp [hj_st, resI]
          have hst'_inDom : st'.inDom = resI.state.inDom := by
            rw [hst'_eq, hres_eq]; dsimp only [step]; simp [hj_st, resI]
          have hGs : st.G.applyUpdate u = G₀.applyBatch (us.take (m + 1)) := by
            rw [hm_inv.G_eq, take_succ_of_getElem? hu_some, applyBatch_append]
            rfl
          rw [← hGs, hst'_Hl]
          have hpi_eq_init : piLe st' i.1 e = piLe resI.state i.1 e := by
            change piLtFrom st'.Pi_level st'.inDom (i.1 + 1) e =
              piLtFrom resI.state.Pi_level resI.state.inDom (i.1 + 1) e
            rw [hst'_Pi, hst'_inDom]
          rw [hpi_eq_init]
          exact initAt_nodup (st.G.applyUpdate u) sparsify i e heG'
        · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
          have hj_le : j ≤ L := chooseLevel_le L q (m + 1)
          have hDisj_m : Disjoint res.D st.H.E := hDisj_n m (Nat.lt_succ_self m) hj_pos
          have htake_succ : us.take (m + 1) = us.take m ++ [u] := take_succ_of_getElem? hu_some
          obtain ⟨hBV_m, hds_m, hu_valid_all⟩ := batchIsValid_take us G₀ m hBV hds
          have hu_valid : (G₀.applyBatch (us.take m)).UpdateIsValid u := (hu_valid_all u hu_some).1
          have hdu : isDelOrSplit u := hds u (List.getElem_mem hm_lt)
          obtain ⟨hBV_m1, hds_m1, _⟩ := batchIsValid_take us G₀ (m + 1) hBV hds
          have hVGk : (G₀.applyBatch (us.take m)).IsValid :=
            (batch_delOrSplit_invariants (us.take m) G₀ hVG₀ hBV_m hds_m).1
          set Gk := G₀.applyBatch (us.take m)
          set G' := G₀.applyBatch (us.take (m + 1))
          have hG'_eq : G' = Gk.applyUpdate u := by simp [G', Gk, htake_succ, MGraph.applyBatch]
          have hVG' : G'.IsValid :=
            (batch_delOrSplit_invariants (us.take (m + 1)) G₀ hVG₀ hBV_m1 hds_m1).1
          have hG'E_sub : G'.E ⊆ Gk.E := by
            have h1 := (batch_delOrSplit_invariants [u] Gk hVGk
              ⟨hu_valid, True.intro⟩ (fun x hx => by simp at hx; rwa [hx])).2.1
            simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil] at h1
            rwa [← hG'_eq] at h1
          have hpi_collapse : piLe st' i.1 e = piLe st' j e := by
            have h0 : e ∈ st'.inDom ⟨0, Nat.zero_lt_succ L⟩ := hm1_inv.inDom0 ▸ heGn
            have hj_le_i : j ≤ i.1 := hi_ch
            have hl1 : ∀ l : Fin (L + 1), j < l.1 → l.1 < i.1 + 1 → e ∉ st'.inDom l := fun l hjl _ => by
              rw [hst'_eq, hres_eq]; dsimp only [step]
              have hch : chooseLevel L st.q (st.t + 1) = j := by rw [hm_inv.q_eq, hm_inv.t_eq]
              have hj_st_ne : chooseLevel L st.q (st.t + 1) ≠ 0 := by rw [hch]; exact hj0
              simp only [hj_st_ne, ↓reduceDIte]
              simp only [hch, Nat.not_lt.mpr (Nat.le_of_lt hjl), Nat.ne_of_gt hjl, ↓reduceIte,
                Finset.notMem_empty, not_false_eq_true]
            change piLtFrom st'.Pi_level st'.inDom (i.1 + 1) e =
              piLtFrom st'.Pi_level st'.inDom (j + 1) e
            exact piLtFrom_eq_of_lt st'.Pi_level st'.inDom (Nat.succ_pos j) (Nat.succ_le_succ hj_le_i) h0 hl1
          have hG'tail : (unionGraphLt G' st'.H_level (i.1 + 1)).tail = G'.tail := rfl
          have hG'head : (unionGraphLt G' st'.H_level (i.1 + 1)).head = G'.head := rfl
          rw [hpi_collapse, walkVertices_congr_ends hG'tail hG'head]
          -- Relate to last rebuild `r` of level `j - 1`
          set r := lastRebuild q L (j - 1) (m + 1)
          have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ m + 1 := by
            intro hdvd
            have := (chooseLevel_le_iff_dvd hq (le_trans (Nat.sub_le j 1) hj_le)).mpr hdvd
            omega
          have hr_eq_m : r = lastRebuild q L (j - 1) m :=
            lastRebuild_eq_of_not_dvd (q := q) (L := L) (i := j - 1) hr_not_dvd
          have hr_le_m : r ≤ m := by rw [hr_eq_m]; exact lastRebuild_le q L (j - 1) m
          have hr_lt_m1 : r < m + 1 := Nat.lt_succ_of_le hr_le_m
          have hr_ch : chooseLevel L q r ≤ j - 1 :=
            lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
          have hInv_r := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r (le_trans hr_le_m (Nat.le_of_lt hm_lt))).1
          set st_r := runState (L := L) G₀ q sparsify us r
          set G_r := G₀.applyBatch (us.take r)
          set delta := (us.take (m + 1)).drop r
          have htake_m1 : us.take (m + 1) = us.take r ++ delta := by
            have h1 : (us.take (m + 1)).take r = us.take r := by
              rw [List.take_take, min_eq_left (le_trans hr_le_m (Nat.le_succ m))]
            rw [← h1]; exact (List.take_append_drop r (us.take (m + 1))).symm
          have hBV_split := (batchIsValid_append G₀ (us.take r) delta).mp (htake_m1 ▸ hBV_m1)
          have hBV_r : G₀.BatchIsValid (us.take r) := hBV_split.1
          have hBV_d : G_r.BatchIsValid delta := hBV_split.2
          have hds_d : ∀ x ∈ delta, isDelOrSplit x := fun x hx =>
            hds_m1 x (by rw [htake_m1]; exact List.mem_append_right _ hx)
          have hds_r : ∀ x ∈ us.take r, isDelOrSplit x := fun x hx =>
            hds_m1 x (by rw [htake_m1]; exact List.mem_append_left _ hx)
          have hinv_r_d := batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_r hds_r
          have hVG_r : G_r.IsValid := hinv_r_d.1
          have hG_r_m : G_r.m ≤ mMax := le_trans (Finset.card_le_card hinv_r_d.2.1) hGm₀
          have hG'_delta : G' = G_r.applyBatch delta := by
            dsimp only [G', G_r]; rw [htake_m1, applyBatch_append]
          have hinv_d := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
          have heGr : e ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ heGn)
          have hNodup_r :
              ((unionGraphLt G_r st_r.H_level ((j - 1) + 1)).walkVertices
                (G_r.tail e) (piLe st_r (j - 1) e)).Nodup := by
            have hih := ih r hr_lt_m1 (le_trans hr_le_m (Nat.le_of_lt hm_lt))
              (fun k' hk' hkp => hDisj_n k' (lt_trans hk' hr_lt_m1) hkp)
              ⟨j - 1, by omega⟩ hr_ch e heGr
            simpa [st_r, hInv_r.G_eq] using hih
          have hrk_eq_lt : ∀ {l : ℕ}, l < j →
              lastRebuild q L l (m + 1) = lastRebuild q L l m ∧
              lastRebuild q L l r = lastRebuild q L l m := fun {l} hl => by
            have hl_le : l ≤ j - 1 := Nat.le_pred_of_lt hl
            have h1 : lastRebuild q L l (m + 1) = lastRebuild q L l m := by
              refine lastRebuild_eq_of_not_dvd fun hdvd => hr_not_dvd ?_
              exact dvd_trans (phasePeriod_dvd_of_le hl_le (le_trans (Nat.sub_le j 1) hj_le)) hdvd
            have hmr_le : lastRebuild q L l m ≤ r := by
              rw [hr_eq_m]
              exact lastRebuild_mono_level hq hl_le (le_trans (Nat.sub_le j 1) hj_le)
            exact ⟨h1, lastRebuild_idempotent_le hq hmr_le hr_le_m⟩
          set H_mid : Fin (L + 1) → MGraph :=
            fun l => (st.H_level l).applyBatch (restrictUpdate u (st.H_level l))
          have hH_mid_props : ∀ l : Fin (L + 1),
              G'.IsSubgraph (H_mid l) ∧ (H_mid l).V = G'.V ∧ (H_mid l).E = (st.H_level l).E ∩ G'.E :=
            fun l => by
              obtain ⟨_, h1, h2, h3, _, _⟩ :=
                isSubgraph_restrictUpdate (hm_inv.H_level_sub l) (hm_inv.H_level_V l) hu_valid hdu
              exact ⟨hG'_eq ▸ h1, hG'_eq ▸ h2, hG'_eq ▸ h3⟩
          set H_lt := unionGraphLt G' H_mid j
          set H_lt_r := unionGraphLt G_r st_r.H_level j
          have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
            refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
            intro e' he'
            simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_univ, true_and] at he'
            rcases he' with ⟨l, _, hel⟩
            exact (hInv_r.H_level_sub l).2.1 hel
          have hHLt_E : H_lt.E = H_lt_r.E ∩ G'.E := by
            ext e'
            simp only [H_lt, H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_inter, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨l, hlj, hel⟩
              rw [(hH_mid_props l).2.2, hm_inv.H_level_E l, ← (hrk_eq_lt hlj).2] at hel
              have hel' := Finset.mem_inter.mp hel
              have hel1 := Finset.mem_inter.mp hel'.1
              have hel_r : e' ∈ (st_r.H_level l).E := by
                rw [hInv_r.H_level_E l]
                exact Finset.mem_inter.mpr ⟨hel1.1, hinv_d.2.1 (hG'_delta ▸ hel'.2)⟩
              exact ⟨⟨l, hlj, hel_r⟩, hel'.2⟩
            · rintro ⟨⟨l, hlj, hel_r⟩, he'G'⟩
              refine ⟨l, hlj, ?_⟩
              rw [(hH_mid_props l).2.2, hm_inv.H_level_E l, ← (hrk_eq_lt hlj).2]
              rw [hInv_r.H_level_E l, Finset.mem_inter] at hel_r
              exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hel_r.1, hG'E_sub he'G'⟩, he'G'⟩
          have hSub_lt : G'.IsSubgraph H_lt := ⟨Finset.Subset.rfl, hHLt_E ▸ Finset.inter_subset_right,
            fun _ _ => ⟨rfl, rfl⟩⟩
          set inDom_mid : Fin (L + 1) → Finset ℕ := fun l => st.inDom l ∩ G'.E
          set piLt_mid := piLtFrom st.Pi_level inDom_mid j
          have hpi_eq : ∀ e' ∈ G'.E, piLt_mid e' = piLe st_r (j - 1) e' := fun e' he' => by
            have he'Gr : e' ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ he')
            have h0_st : e' ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
              dsimp only [inDom_mid]; rw [Finset.mem_inter, hm_inv.inDom0]; exact ⟨hG'E_sub he', he'⟩
            have h0_r : e' ∈ st_r.inDom ⟨0, Nat.zero_lt_succ L⟩ := hInv_r.inDom0 ▸ he'Gr
            obtain ⟨l₁, hl₁, hl₁d, hl₁n, heq₁⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_st
            have hsub1 : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
            obtain ⟨l₂, hl₂, hl₂d, hl₂n, heq₂⟩ := piLtFrom_eq st_r.Pi_level st_r.inDom hj_pos h0_r
            have hcongr : ∀ l : Fin (L + 1), l.1 < j →
                (e' ∈ inDom_mid l ↔ e' ∈ st_r.inDom l) := fun l hl => by
              dsimp only [inDom_mid]
              rw [hm_inv.inDom_eq l, hInv_r.inDom_eq l, (hrk_eq_lt hl).2]
              simp only [Finset.mem_inter]
              exact ⟨fun h => ⟨h.1.1, he'Gr⟩, fun h => ⟨⟨h.1, hG'E_sub he'⟩, he'⟩⟩
            have hl_eq : l₁ = l₂ := by
              by_contra hne
              rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
              · exact hl₁n l₂ hlt hl₂ ((hcongr l₂ hl₂).mpr hl₂d)
              · exact hl₂n l₁ hlt hl₁ ((hcongr l₁ hl₁).mp hl₁d)
            change piLtFrom st.Pi_level inDom_mid j e' =
              piLtFrom st_r.Pi_level st_r.inDom ((j - 1) + 1) e'
            rw [hsub1, heq₁, heq₂, hl_eq, hm_inv.Pi_level_eq l₂, hInv_r.Pi_level_eq l₂,
              (hrk_eq_lt hl₂).2]
          set S_prev := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u
          have hS_prev_eq : S_prev = allTouched G_r delta := by
            have hS_r : st.S_level ⟨j - 1, by omega⟩ =
                allTouched G_r ((us.take m).drop r) := by
              rw [hm_inv.S_level_eq ⟨j - 1, by omega⟩, ← hr_eq_m]
            have hdrop : delta = (us.take m).drop r ++ [u] := by
              dsimp only [delta]
              rw [htake_succ, List.drop_append_of_le_length (by rw [List.length_take]; omega)]
            have hGrd : G_r.applyBatch ((us.take m).drop r) = st.G := by
              have htake_m : us.take m = us.take r ++ (us.take m).drop r := by
                have h1 : (us.take m).take r = us.take r := by rw [List.take_take, min_eq_left hr_le_m]
                rw [← h1]; exact (List.take_append_drop r (us.take m)).symm
              dsimp only [G_r]
              rw [← applyBatch_append, ← htake_m, ← hm_inv.G_eq]
            dsimp only [S_prev]
            rw [hS_r, hdrop, allTouched_append, hGrd]
            simp [allTouched]
          set E_aff := affectedEdges G' H_lt piLt_mid S_prev
          set J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
          set H_aux := buildAuxHost G' H_lt E_aff
          set embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
          set out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
          set outEmb : Embedding := fun e' => shortcutWalk out.Jtilde (J.tail e') (out.emb e')
          set embMid : Embedding := Embedding.comp embJH outEmb
          set Pi_j : Embedding := reembedWalk G' H_lt piLt_mid embMid S_prev
          have hstep_ch : chooseLevel L st.q (st.t + 1) = j := by rw [hm_inv.q_eq, hm_inv.t_eq]
          have hstG' : st.G.applyUpdate u = G' := by rw [hm_inv.G_eq, ← hG'_eq]
          have hst'_inDom : ∀ l : Fin (L + 1), st'.inDom l =
              if l.1 < j then inDom_mid l else if l.1 = j then E_aff else ∅ := fun l => by
            rw [hst'_eq, hres_eq]; dsimp only [step]
            have hj_st_ne : chooseLevel L st.q (st.t + 1) ≠ 0 := by rw [hstep_ch]; exact hj0
            simp only [hj_st_ne, ↓reduceDIte]
            simp only [hstep_ch, hstG', E_aff, S_prev, piLt_mid, inDom_mid, H_lt, H_mid, st]
          have hst'_Pi : ∀ l : Fin (L + 1), st'.Pi_level l =
              if l.1 < j then st.Pi_level l else if l.1 = j then Pi_j else fun _ => [] := fun l => by
            rw [hst'_eq, hres_eq]; dsimp only [step]
            simp only [show chooseLevel L st.q (st.t + 1) ≠ 0 by rw [hstep_ch]; exact hj0, ↓reduceDIte]
            simp only [hstep_ch, hstG', Pi_j, embMid, outEmb, embJH, out, J, H_aux, E_aff, S_prev,
              piLt_mid, inDom_mid, H_lt, H_mid, st]
          have hres_D_eq : res.D = out.Jtilde.E.biUnion fun e' => walkEdges (embJH e') := by
            rw [hres_eq]; dsimp only [step]
            simp only [show chooseLevel L st.q (st.t + 1) ≠ 0 by rw [hstep_ch]; exact hj0, ↓reduceDIte]
            simp only [hstep_ch, hstG', H_mid, H_lt, inDom_mid, piLt_mid, E_aff, J, H_aux, embJH, out,
              S_prev, st]
          -- Show `piLe st' j e` is `Pi_j e` if `e ∈ E_aff`, else `piLt_mid e`
          have hpi_j : piLe st' j e = if e ∈ E_aff then Pi_j e else piLt_mid e := by
            have he0' : e ∈ st'.inDom ⟨0, Nat.zero_lt_succ L⟩ := hm1_inv.inDom0 ▸ heGn
            by_cases heAff : e ∈ E_aff
            · have hj_dom : e ∈ st'.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
                rw [hst'_inDom]; simp [heAff]
              obtain ⟨l, hlj, _, hl_none, heql⟩ := piLtFrom_eq st'.Pi_level st'.inDom (Nat.succ_pos j) he0'
              have hl_eq : l.1 = j := by
                apply le_antisymm (Nat.lt_succ_iff.mp hlj)
                by_contra hlt
                exact hl_none ⟨j, Nat.lt_succ_of_le hj_le⟩ (Nat.lt_of_not_le hlt) (Nat.lt_succ_self j) hj_dom
              change piLtFrom _ _ (j + 1) e = _
              rw [heql, show l = ⟨j, Nat.lt_succ_of_le hj_le⟩ from Fin.ext hl_eq, hst'_Pi]
              simp [heAff]
            · have hj_not : e ∉ st'.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
                rw [hst'_inDom]; simp [heAff]
              have hprev := piLtFrom_eq_prev_of_not_mem st'.Pi_level st'.inDom
                (j := ⟨j, Nat.lt_succ_of_le hj_le⟩) hj_pos he0' hj_not
              change piLtFrom _ _ (j + 1) e = _
              rw [hprev]
              have h0_mid : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
                dsimp only [inDom_mid]; rw [Finset.mem_inter, hm_inv.inDom0]; exact ⟨hG'E_sub heGn, heGn⟩
              obtain ⟨l, hlj, hld, hl_none, heql⟩ := piLtFrom_eq st'.Pi_level st'.inDom hj_pos he0'
              obtain ⟨l', hl'j, hl'd, hl'_none, heql'⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
              have hll' : l = l' := by
                by_contra hne
                rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
                · exact hl_none l' hlt hl'j (by rw [hst'_inDom]; simp [hl'j, hl'd])
                · exact hl'_none l hlt hlj (by rw [hst'_inDom] at hld; simpa [hlj] using hld)
              dsimp only [piLt_mid]
              rw [heql, heql', hll', hst'_Pi]
              simp [hl'j, heAff]
          have hEmbr := hInv_r.emb_at ⟨j - 1, by omega⟩ hr_ch
          have hLenr := hInv_r.len_at ⟨j - 1, by omega⟩ hr_ch
          have hVcr := hInv_r.vcong_at ⟨j - 1, by omega⟩ hr_ch
          have hsub_add : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
          dsimp only at hEmbr hLenr hVcr
          rw [hsub_add] at hEmbr hVcr
          have hEmbr_e : H_lt_r.IsWalk (G_r.tail e) (G_r.head e) (piLe st_r (j - 1) e) :=
            hEmbr.2 e heGr
          have hEnds_lt : ∀ e' ∈ H_lt_r.E,
              H_lt.tail e' = (G_r.applyBatch delta).tail e' ∧
              H_lt.head e' = (G_r.applyBatch delta).head e' := fun _ _ => by
            simp [H_lt, unionGraphLt, hG'_delta]
          have hHLt_V_delta : H_lt.V = (G_r.applyBatch delta).V := by
            simp [H_lt, unionGraphLt, hG'_delta]
          have hHLt_E_delta : H_lt.E = H_lt_r.E ∩ (G_r.applyBatch delta).E := hG'_delta ▸ hHLt_E
          have hSub_lt_delta : (G_r.applyBatch delta).IsSubgraph H_lt := hG'_delta ▸ hSub_lt
          have hTouch_r : allTouched G_r delta ⊆ S_prev := hS_prev_eq ▸ Finset.Subset.rfl
          have hanc_ends := hinv_d.2.2.2.2.2.2 e heGr
          have hV_tail : G'.tail e ∈ (G_r.applyBatch delta).V := by
            rw [← hG'_delta]; exact (hVG' e heGn).1
          have hV_head : G'.head e ∈ (G_r.applyBatch delta).V := by
            rw [← hG'_delta]; exact (hVG' e heGn).2
          have hanc_t : batchAnc delta (G'.tail e) = G_r.tail e := by
            rw [hG'_delta]; exact hanc_ends.1
          have hanc_h : batchAnc delta (G'.head e) = G_r.head e := by
            rw [hG'_delta]; exact hanc_ends.2
          have hpi_r_eq : piLt_mid e = piLe st_r (j - 1) e := hpi_eq e heGn
          have hNodup_r' : (H_lt_r.walkVertices (G_r.tail e) (piLe st_r (j - 1) e)).Nodup := by
            change ((unionGraphLt G_r st_r.H_level ((j - 1) + 1)).walkVertices
              (G_r.tail e) (piLe st_r (j - 1) e)).Nodup
            rw [Nat.sub_add_cancel hj_pos]
            exact hNodup_r
          rw [hpi_j]
          split_ifs with heAff
          · -- Case `e ∈ E_aff`: use `Disjoint res.D st.H.E` + `shortcutWalk` via `step_isPath_eAff`
            have hHlt_sub_stH : H_lt.E ⊆ st.H.E := by
              intro x hx
              simp only [H_lt, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_univ, true_and] at hx
              rcases hx with ⟨l, _, hxl⟩
              have hxl' : x ∈ (st.H_level l).E := ((hH_mid_props l).2.2 ▸ hxl |> Finset.mem_inter.mp).1
              rw [hm_inv.H_E]
              exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l,
                Nat.lt_succ_of_le (Nat.le_of_lt_succ l.2)⟩, hxl'⟩
            exact step_isPath_eAff hSpec hVG_r hBV_d hds_d hVG' hG_r_m hG'_delta
              hSub_lt_r hSub_lt rfl hHLt_E rfl rfl hEmbr hLenr hVcr hTouch_r hpi_eq rfl
              hHlt_sub_stH heAff hNodup_r' (hres_D_eq ▸ hDisj_m)
          · -- Case `e ∉ E_aff`
            have hdisj_e : Disjoint (H_lt.walkVertices (G'.tail e) (piLe st_r (j - 1) e)).toFinset
                S_prev := by
              rw [Finset.disjoint_left]
              intro z hz hzS
              apply heAff
              refine Finset.mem_filter.mpr ⟨heGn, decide_eq_true ?_⟩
              rw [hpi_r_eq]
              exact ⟨z, List.mem_toFinset.mp hz, hzS⟩
            have hp_unaff := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta hHLt_V_delta
              hHLt_E_delta hEnds_lt hTouch_r (piLe st_r (j - 1) e) (G_r.tail e) (G_r.head e)
              (G'.tail e) (hVG_r e heGr).1 (hVG_r e heGr).2 hEmbr_e hV_tail hanc_t).1 hdisj_e
            have hwv_eq : G'.walkVertices (G'.tail e) (piLt_mid e) =
                H_lt_r.walkVertices (G_r.tail e) (piLe st_r (j - 1) e) := by
              rw [hpi_r_eq]
              have h1 : G'.walkVertices (G'.tail e) (piLe st_r (j - 1) e) =
                  H_lt.walkVertices (G'.tail e) (piLe st_r (j - 1) e) :=
                walkVertices_congr_ends (H := G') (G := H_lt) rfl rfl (G'.tail e) _
              rw [h1, hp_unaff.2.2]
            rw [hwv_eq]
            exact hNodup_r'
  refine ⟨hInd k hk hDisj, fun e heGk => ?_⟩
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk).1
  have heGn : e ∈ (G₀.applyBatch (us.take k)).E := hk_inv.G_eq ▸ heGk
  have hnd := hInd k hk hDisj ⟨L, Nat.lt_succ_self L⟩ (chooseLevel_le L q k) e heGn
  have hemb := (lemma_5_6 hVG₀ hL hq hGm₀ hSpec hBV hds (k := k) hk).2.2 e heGn
  have h1 := walkVertices_of_isSubgraph hk_inv.H_sub hemb
  refine ⟨hk_inv.G_eq ▸ hemb, ?_⟩
  rw [hk_inv.G_eq, ← h1]
  rw [walkVertices_congr_ends (H := G₀.applyBatch (us.take k))
    (G := unionGraphLt (G₀.applyBatch (us.take k))
      (runState (L := L) G₀ q sparsify us k).H_level (L + 1)) rfl rfl]
  rw [← hk_inv.G_eq]
  exact hnd

private theorem abs_walkFlow_eq_one_of_nodup :
    ∀ {P : List (ℕ × Bool)} {e : ℕ},
      (P.map Prod.fst).Nodup → e ∈ walkEdges P → |walkFlow P e| = 1
  | [], e, _, he => by simp [walkEdges] at he
  | x :: P', e, hnd, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have he' : e = x.1 ∨ e ∈ walkEdges P' := by
      simpa [walkEdges, List.mem_map, eq_comm] using he
    rcases he' with rfl | heP'
    · have hzero : walkFlow P' x.1 = 0 := by
        unfold walkFlow
        refine List.sum_eq_zero ?_
        intro v hv
        rw [List.mem_map] at hv
        rcases hv with ⟨y, hy, rfl⟩
        have hne : y.1 ≠ x.1 := fun h => hnd.1 (List.mem_map.mpr ⟨y, hy, h⟩)
        simp [hne]
      unfold walkFlow at hzero ⊢
      simp only [List.map_cons, List.sum_cons, ↓reduceIte, hzero, add_zero]
      cases x.2 <;> norm_num
    · have hne : x.1 ≠ e := fun h => by
        rw [← h, mem_walkEdges_iff] at heP'
        rcases heP' with ⟨y, hy, hyfst⟩
        exact hnd.1 (List.mem_map.mpr ⟨y, hy, hyfst⟩)
      have ih := abs_walkFlow_eq_one_of_nodup hnd.2 heP'
      unfold walkFlow at ih ⊢
      simp [List.map_cons, hne, ih]

theorem piTotal_walkFlow_abs_eq_one_of_stepDisjoint {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ k ≤ us.length,
      (∀ m < k, 0 < chooseLevel L q (m + 1) →
        Disjoint (runStepOut (L := L) G₀ q sparsify us m).D
          (runState (L := L) G₀ q sparsify us m).H.E) →
      ∀ e ∈ (runState (L := L) G₀ q sparsify us k).G.E,
      ∀ e' ∈ walkEdges (piTotal (runState (L := L) G₀ q sparsify us k) e),
        |walkFlow (piTotal (runState (L := L) G₀ q sparsify us k) e) e'| = 1 := by
  intro k hk hDisj e he e' he'
  have hP := (step_isPath_of_disjoint hVG₀ hL hq hGm₀ hSpec hBV hds k hk hDisj).2 e he
  exact abs_walkFlow_eq_one_of_nodup (isPath_edges_nodup hP) he'

end

end Reembedding

end MinCostFlow.DynSpanner
