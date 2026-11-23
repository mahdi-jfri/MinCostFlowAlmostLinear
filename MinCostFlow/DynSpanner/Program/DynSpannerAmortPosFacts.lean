module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortCand
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortPot
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortWalks
public import MinCostFlow.DynSpanner.Program.DynSpannerStepHelpers
public import MinCostFlow.DynSpanner.StepTransition

/-!
# The sizes behind the cost of a step with `0 < j`

The cost of the program for a step with `0 < j` (`dsStepPosCostModel`) is written with the sets
and walks of the model step: `S_{j-1}`, `E_aff`, the graph `J` with its walks `Π_{J → G'}`, the
candidates of `RevHistoryInv`, the output `J̃` of the sparsifier, and the new walks. This file
gathers the bounds on their sizes that the proof of Lemma 5.9 uses (`stepPos_facts`), from the
record `StepCostRecord.rebuild_sizes` of the model, the candidate bounds of
`DynSpannerAmortCand.lean` (Claim 5.7), and the potential bound of `DynSpannerAmortPot.lean`.

One point needs care. The program calls the sparsifier with host `G'`, the model with host
`H_aux = H_{<j} ∪ E_aff`. Both have the same endpoints, and `embJH` is an embedding into both
(`H_aux` is a subgraph of `G'`), so the canonical sparsifier returns the same output
(`canonicalSparsify_congr_ends`). The same holds for the walks `reembedWalk`, whose host enters
only through its endpoints (`prefixWalk_congr_ends`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The new level `j` after a step with `0 < j` is the output `J̃` of the sparsifier, or empty
when `E_aff` is empty. -/
lemma StepPosModel.res_H_level_j (m : StepPosModel) (hq : m.st.q = m.q) (ht : m.st.t = m.k)
    (hj : 0 < m.j) (hjL : m.j < m.L + 1) :
    (m.res.state.H_level ⟨m.j, hjL⟩).E =
      (if m.E_aff.Nonempty then
        canonicalSparsify m.impl (buildAuxHost m.G' m.H_lt m.E_aff) m.J m.embJH
       else ⟨m.J, idEmb, 0⟩).Jtilde.E := by
  have hj0 : chooseLevel m.L m.st.q (m.st.t + 1) ≠ 0 := by rw [hq, ht]; exact Nat.ne_of_gt hj
  simp only [StepPosModel.res, step]
  rw [dif_neg hj0]
  have hjj : chooseLevel m.L m.st.q (m.st.t + 1) = m.j := by rw [hq, ht]
  simp only [hjj, lt_irrefl, ↓reduceIte]

/-- **The sizes of a step with `0 < j`** (proof of Lemma 5.9, page 39), for the model step `m` at
update `k`. With `sLen` the number of updates since the last rebuild of level `j - 1`,
`V = vcongBound(j - 1)` and `ℓ = lenBound(j - 1)`:
`|S_{j-1}| ≤ 2 sLen`, `|E_aff| ≤ |S_{j-1}| V`, the old walks have length at most `ℓ`,
`|V(J)| ≤ 2 |E_aff|`, the candidates are at most `|S_{j-1}| j V`, the old levels `≥ j` are paid by
the potential up to `|E(J̃)|`, and, when `E_aff` is nonempty, the bounds on the walks of `J`, on
`J̃`, and on the new walks. -/
theorem stepPos_facts (impl : SparsifyImpl) {G₀ : MGraph} {mMax L q : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj : 0 < chooseLevel L q (k + 1)) :
    let m : StepPosModel := ⟨G₀, impl, L, q, k, us, us[k]'hk⟩
    let P := (canonicalSparsifyParams impl mMax).absorbTime
    let sLen := k + 1 - lastRebuild q L (m.j - 1) (k + 1)
    let V := vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (m.j - 1)
    let ℓ := lenBound P.γ_ℓ (m.j - 1)
    let out := canonicalSparsify impl m.G' m.J m.embJH
    let outEmb : MinCostFlow.Embedding := fun e => shortcutWalk out.Jtilde (m.J.tail e) (out.emb e)
    let embMid := MinCostFlow.Embedding.comp m.embJH outEmb
    runStepOut (L := L) G₀ q (canonicalSparsify impl) us k = m.res ∧
    (m.S_prev.card : ℝ) ≤ 2 * (sLen : ℝ) ∧
    (m.E_aff.card : ℝ) ≤ (m.S_prev.card : ℝ) * V ∧
    (∀ e ∈ m.G'.E, ((m.piLt_mid e).length : ℝ) ≤ ℓ) ∧
    m.J.n ≤ 2 * m.E_aff.card ∧ m.J.n ≤ m.G'.n ∧ m.E_aff.card ≤ G₀.m ∧
    m.E_aff ⊆ m.G'.E ∧ modelCandSet m ⊆ m.G'.E ∧
    (modelCandRevSum m : ℝ) ≤ (m.S_prev.card : ℝ) * ((m.j : ℝ) * V) ∧
    (modelOldSum m : ℝ) +
        (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) : ℝ) ≤
      (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us k) : ℝ) +
        (if m.E_aff.Nonempty then (out.Jtilde.m : ℝ) else 0) ∧
    (m.E_aff.Nonempty →
      (m.embJH.length m.J : ℝ) ≤ ℓ + 1 ∧
      (out.Jtilde.m : ℝ) ≤ P.K_s * (m.J.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((m.J.n : ℝ) + (m.J.m : ℝ) + 2)) ^ P.p_s ∧
      (∀ e ∈ m.J.E, ((embMid e).length : ℝ) ≤ P.γ_ℓ * (ℓ + 1)) ∧
      (∀ e ∈ m.E_aff, ((reembedWalk m.G' m.G' m.piLt_mid embMid m.S_prev e).length : ℝ) ≤
        lenBound P.γ_ℓ m.j) ∧
      (∀ e ∈ m.J.E, (out.emb e).length ≤ ⌈impl.γ_ℓ mMax⌉₊)) := by
  intro m P sLen V ℓ out outEmb embMid
  set sp := canonicalSparsify impl
  set u := us[k]'hk with hu_def
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  have hq1 : 1 ≤ q := by omega
  have hSpec : SparsifySpec mMax P sp := canonicalSparsify_spec_absorb impl mMax
  obtain ⟨hInvk, -⟩ := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds k hk.le
  obtain ⟨-, hRecs⟩ := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) hk
  have hRec := hRecs k (Nat.lt_succ_self k) u hu
  have hres : runStepOut (L := L) G₀ q sp us k = m.res := by
    simp only [runStepOut, hu]; rfl
  have hst1 : runState (L := L) G₀ q sp us (k + 1) = m.res.state := by
    simp only [runState, hu]; rfl
  have hjL : m.j ≤ L := chooseLevel_le L q (k + 1)
  obtain ⟨hS2, hAff, hpiL, hJn, hJnG, hG'm, hVG', hAuxV, hJV, hEmbAux, hSub, hNE⟩ :=
    hRec.rebuild_sizes hj
  -- The candidates.
  have hcand : (modelCandRevSum m : ℝ) ≤ (m.S_prev.card : ℝ) * ((m.j : ℝ) * V) := by
    have hSn : ∀ i : Fin (m.L + 1), i.1 < m.j →
        SnapInv m.G₀ m.L m.q mMax P (canonicalSparsify m.impl) m.us
          (lastRebuild m.q m.L i.1 m.k) := fun i _ =>
      (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds _
        (le_trans (lastRebuild_le q L i.1 k) hk.le)).1
    have hVr : ∀ i : Fin (m.L + 1), i.1 < m.j →
        (m.G₀.applyBatch (m.us.take (lastRebuild m.q m.L i.1 m.k))).IsValid := fun i _ => by
      obtain ⟨h1, h2, -⟩ := batchIsValid_take us G₀ (lastRebuild q L i.1 k) hBV hds
      exact (batch_delOrSplit_invariants _ G₀ hVG₀ h1 h2).1
    have h := modelCandRevSum_le (mMax := mMax) (P := P) m hq1 hSn hVr
    have hsum : ∑ i ∈ Finset.range m.j, vcongBound P.γ_c P.γ_ℓ m.G₀.maxDeg i ≤ (m.j : ℝ) * V := by
      have := Finset.sum_le_card_nsmul (Finset.range m.j)
        (fun i => vcongBound P.γ_c P.γ_ℓ m.G₀.maxDeg i) V fun i hi =>
          vcongBound_mono P.hγ_c P.hγ_ℓ _ (by have := Finset.mem_range.mp hi; omega)
      simpa [nsmul_eq_mul] using this
    exact le_trans h (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  -- The potential.
  have hjL1 : m.j < m.L + 1 := Nat.lt_succ_of_le hjL
  have hpot := oldSum_add_levelPot_le m hInvk.q_eq hInvk.t_eq hj hjL1
  have hHj := m.res_H_level_j hInvk.q_eq hInvk.t_eq hj hjL1
  -- The two hosts give the same sparsifier output.
  have hEmbG' : m.embJH.IsEmbedding m.J m.G' :=
    ⟨hEmbAux.1, fun e he => IsWalk.of_isSubgraph hSub (hEmbAux.2 e he)⟩
  have hLen1 : m.J.E.Nonempty → 1 ≤ m.embJH.length m.J := by
    rintro ⟨e, he⟩
    have hle : (m.embJH e).length ≤ m.embJH.length m.J :=
      Finset.le_sup (f := fun x => (m.embJH x).length) he
    have hpos : 1 ≤ (m.embJH e).length := by
      simp only [StepPosModel.embJH, projWalk, List.length_append, List.length_cons,
        List.length_nil]
      omega
    omega
  have hcongr : canonicalSparsify impl (buildAuxHost m.G' m.H_lt m.E_aff) m.J m.embJH = out :=
    canonicalSparsify_congr_ends impl rfl rfl hAuxV hVG' hJV hLen1 hEmbAux hEmbG'
  have hEsub : m.E_aff ⊆ m.G'.E := Finset.filter_subset _ _
  have hJm : m.J.m ≤ mMax := le_trans (Finset.card_le_card hEsub) (le_trans hG'm hGm₀)
  refine ⟨hres, by exact_mod_cast hS2, hAff, hpiL, hJn, hJnG,
    le_trans (Finset.card_le_card hEsub) hG'm, hEsub,
    (by intro e he; simp only [modelCandSet, Finset.mem_filter] at he; exact he.1), hcand, ?_, ?_⟩
  · rw [hst1]
    have h := (Nat.cast_le (α := ℝ)).mpr hpot
    push_cast at h
    have hm : (m.res.state.H_level ⟨m.j, hjL1⟩).m =
        if m.E_aff.Nonempty then out.Jtilde.m else 0 := by
      rw [MGraph.m, hHj]
      split_ifs with hne
      · rw [hcongr]; rfl
      · simp only [Finset.not_nonempty_iff_eq_empty] at hne
        show m.E_aff.card = 0
        rw [hne, Finset.card_empty]
    rw [hm] at h
    split_ifs at h ⊢ <;> push_cast at h <;> linarith
  · intro hne
    obtain ⟨hL1, hJt, hLenMid, hRe⟩ := hNE hne
    set outA := canonicalSparsify impl (buildAuxHost m.G' m.H_lt m.E_aff) m.J m.embJH with houtA
    have hJt' : (outA.Jtilde.m : ℝ) ≤ P.K_s * (m.J.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((m.J.n : ℝ) + (m.J.m : ℝ) + 2)) ^ P.p_s := hJt
    have hLenMid' : ((MinCostFlow.Embedding.comp m.embJH
        (fun e => shortcutWalk outA.Jtilde (m.J.tail e) (outA.emb e))).length m.J : ℝ) ≤
        P.γ_ℓ * (m.embJH.length m.J : ℝ) := hLenMid
    have hRe' : ∀ e ∈ m.E_aff, ((reembedWalk m.G' m.H_lt m.piLt_mid
        (MinCostFlow.Embedding.comp m.embJH
          (fun e => shortcutWalk outA.Jtilde (m.J.tail e) (outA.emb e))) m.S_prev e).length : ℝ) ≤
        lenBound P.γ_ℓ m.j := hRe
    clear_value outA
    subst hcongr
    clear hJt hLenMid hRe
    have hJt := hJt'
    have hLenMid := hLenMid'
    have hRe := hRe'
    refine ⟨hL1, hJt, fun e he => ?_, fun e he => ?_, ?_⟩
    · have h1 : ((embMid e).length : ℝ) ≤ (embMid.length m.J : ℝ) := by
        exact_mod_cast Finset.le_sup (f := fun x => (embMid x).length) he
      have h2 : P.γ_ℓ * (m.embJH.length m.J : ℝ) ≤ P.γ_ℓ * (ℓ + 1) :=
        mul_le_mul_of_nonneg_left hL1 (by linarith [P.hγ_ℓ])
      exact le_trans h1 (le_trans hLenMid h2)
    · have h := hRe e he
      have heq : reembedWalk m.G' m.G' m.piLt_mid embMid m.S_prev e =
          reembedWalk m.G' m.H_lt m.piLt_mid embMid m.S_prev e := by
        simp only [reembedWalk, prefixWalk_congr_ends (H₁ := m.G') (H₂ := m.H_lt) rfl rfl]
      rw [heq]
      exact h
    · exact canonicalSparsify_emb_length_le impl mMax hVG' hJV hJm hLen1 hEmbG'

end

end MinCostFlow.DynSpanner.Program
