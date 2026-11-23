module

public import MinCostFlow.DynSpanner.ReembDefs

import Mathlib.Tactic.Linarith

/-!
# Auxiliary lemmas for re-embedded edge coverage (`DynSpanner.ReembAux`)

Helper lemmas showing that when a surviving edge `eG` is not in `E_aff` at a positive-level
rebuild `j`, its level-`< j` walk avoids every touched vertex since the last rebuild of level
`j - 1`, and therefore its `piLe` embedding stays identically equal across all intermediate steps
at levels `≥ j`.
-/

namespace MinCostFlow.DynSpanner

public section

/-! ## Coverage: every surviving edge whose embedding changes is in `stepReembSet` / `updateReembSet` -/

/-- Any vertex `z ∈ (G₀.applyBatch us).V` outside `allTouched G₀ us` has `batchAnc us z = z`. -/
theorem batchAnc_eq_self_of_not_mem_allTouched :
    ∀ (us : List Update) (G₀ : MGraph),
      G₀.IsValid → G₀.BatchIsValid us → (∀ u ∈ us, isDelOrSplit u) →
      ∀ z ∈ (G₀.applyBatch us).V, z ∉ allTouched G₀ us → batchAnc us z = z
  | [], _, _, _, _, _, _, _ => rfl
  | u :: us, G₀, hV, hBV, hds, z, hz, hnot => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hdu := hds u List.mem_cons_self
    have hds' : ∀ x ∈ us, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    have hV1 := isValid_applyUpdate_of_delOrSplit hV hu hdu
    simp only [MGraph.applyBatch, List.foldl_cons] at hz
    simp only [allTouched, Finset.mem_union, not_or] at hnot
    have ih := batchAnc_eq_self_of_not_mem_allTouched us (G₀.applyUpdate u) hV1 hBV' hds' z hz hnot.2
    rw [batchAnc_cons, ih]
    cases u with
    | insert _ _ _ => exact hdu.elim
    | delete _ => rfl
    | split v v' _ _ =>
      have hne : z ≠ v' := fun h => hnot.1 (by simp [touchedVertices, h])
      simp [stepAnc, hne]

/-- The endpoint `b` of any walk `G.IsWalk a b p` appears in `G.walkVertices a p`. -/
theorem mem_walkVertices_end {G : MGraph} :
    ∀ {a b : ℕ} {p : List (ℕ × Bool)}, G.IsWalk a b p → b ∈ G.walkVertices a p
  | _, _, [], .nil _ => by simp [MGraph.walkVertices]
  | _, _, _ :: _, .cons _ _ hrest => by
    simp only [MGraph.walkVertices, List.mem_cons]
    exact Or.inr (mem_walkVertices_end hrest)

/-- If a walk in `G_k1 = G_s.applyBatch delta` avoids `allTouched G_s delta`, then its vertex list
in `G_s` equals its vertex list in `G_k1`. -/
theorem walkVertices_eq_of_not_mem_allTouched :
    ∀ (p : List (ℕ × Bool)) {G_s G_k1 : MGraph} {delta : List Update} {a_s a_k1 b_k1 : ℕ},
      G_s.IsValid → G_s.BatchIsValid delta → (∀ u ∈ delta, isDelOrSplit u) →
      G_k1 = G_s.applyBatch delta →
      G_k1.IsWalk a_k1 b_k1 p →
      a_k1 ∈ G_k1.V →
      batchAnc delta a_k1 = a_s →
      (∀ z ∈ G_k1.walkVertices a_k1 p, z ∉ allTouched G_s delta) →
      G_s.walkVertices a_s p = G_k1.walkVertices a_k1 p
  | [], G_s, G_k1, delta, a_s, a_k1, _, hVs, hBV, hds, hGk1, _, ha_V, hanc, hnot => by
    have ha_not : a_k1 ∉ allTouched G_s delta := hnot a_k1 (by simp [MGraph.walkVertices])
    have ha_eq : a_s = a_k1 :=
      hanc.symm.trans (batchAnc_eq_self_of_not_mem_allTouched delta G_s hVs hBV hds a_k1
        (hGk1 ▸ ha_V) ha_not)
    simp [MGraph.walkVertices, ha_eq]
  | x :: rest, G_s, G_k1, delta, a_s, a_k1, b_k1, hVs, hBV, hds, hGk1, hwalk, ha_V, hanc, hnot => by
    have ha_not : a_k1 ∉ allTouched G_s delta := hnot a_k1 (by simp [MGraph.walkVertices])
    have ha_eq : a_s = a_k1 :=
      hanc.symm.trans (batchAnc_eq_self_of_not_mem_allTouched delta G_s hVs hBV hds a_k1
        (hGk1 ▸ ha_V) ha_not)
    cases hwalk with
    | cons hx hsrc hrest =>
      have hinv := batch_delOrSplit_invariants delta G_s hVs hBV hds
      have hx_s : x.1 ∈ G_s.E := hinv.2.1 (hGk1 ▸ hx)
      have hdst_V : G_k1.dst x ∈ G_k1.V := by
        have hVk1 : G_k1.IsValid := hGk1 ▸ hinv.1
        cases xb : x.2 <;> simp [MGraph.dst, xb]
        · exact (hVk1 x.1 hx).1
        · exact (hVk1 x.1 hx).2
      have hdst_anc : batchAnc delta (G_k1.dst x) = G_s.dst x := by
        have hend := hinv.2.2.2.2.2.2 x.1 hx_s
        cases xb : x.2 <;> simp only [MGraph.dst, xb, Bool.false_eq_true, ↓reduceIte, hGk1]
        · exact hend.1
        · exact hend.2
      have hnot_rest : ∀ z ∈ G_k1.walkVertices (G_k1.dst x) rest, z ∉ allTouched G_s delta :=
        fun z hz => hnot z (by
          simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz ⊢
          exact Or.inr hz)
      have ih := walkVertices_eq_of_not_mem_allTouched rest hVs hBV hds hGk1 hrest hdst_V hdst_anc
        hnot_rest
      simp only [MGraph.walkVertices, ha_eq]
      congr 1

/-- If `eG ∉ E_aff` at step `k + 1` (with `j = chooseLevel L q (k + 1) > 0`), then for every
intermediate step `s` with `r ≤ s ≤ k` and every level `i ≥ j - 1`, `piLe (st s) i eG` stays
identically equal to `p_r = piLe (st r) (j - 1) eG`. -/
theorem piLe_eq_of_not_affected {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (j : ℕ) (hj_pos : 0 < j) (hj_le : j ≤ L)
    (hj_eq : chooseLevel L q (k + 1) = j)
    {eG : ℕ} (heG' : eG ∈ (G₀.applyBatch (us.take (k + 1))).E)
    (hp_walk : (G₀.applyBatch (us.take (k + 1))).IsWalk
      ((G₀.applyBatch (us.take (k + 1))).tail eG)
      ((G₀.applyBatch (us.take (k + 1))).head eG)
      (piLe (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) (k + 1))) (j - 1) eG))
    (hp_disj : ∀ z ∈ (G₀.applyBatch (us.take (k + 1))).walkVertices
      ((G₀.applyBatch (us.take (k + 1))).tail eG)
      (piLe (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) (k + 1))) (j - 1) eG),
      z ∉ allTouched (G₀.applyBatch (us.take (lastRebuild q L (j - 1) (k + 1))))
        ((us.take (k + 1)).drop (lastRebuild q L (j - 1) (k + 1)))) :
    let r := lastRebuild q L (j - 1) (k + 1)
    ∀ s, r ≤ s → s ≤ k →
      ∀ i : Fin (L + 1), j - 1 ≤ i.1 →
        piLe (runState (L := L) G₀ q sparsify us s) i.1 eG =
          piLe (runState (L := L) G₀ q sparsify us r) (j - 1) eG := by
  intro r s hrs hsk
  set p_r := piLe (runState (L := L) G₀ q sparsify us r) (j - 1) eG
  have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ (k + 1) := by
    rw [← hj_eq]; exact not_dvd_of_lt_chooseLevel (Nat.sub_lt (hj_eq ▸ hj_pos) Nat.one_pos)
  have hr_eq_k : r = lastRebuild q L (j - 1) k := lastRebuild_eq_of_not_dvd hr_not_dvd
  have hr_le_k : r ≤ k := hr_eq_k ▸ lastRebuild_le q L (j - 1) k
  obtain ⟨d, hd⟩ : ∃ d, s = r + d := ⟨s - r, (Nat.add_sub_cancel' hrs).symm⟩
  subst hd
  clear hrs
  revert hsk
  induction d with
  | zero =>
    intro _ i hi
    have hr_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r
      (Nat.le_of_lt (Nat.lt_of_le_of_lt hr_le_k hk))).1
    have hr_ch : chooseLevel L q r ≤ j - 1 :=
      lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
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
    have hm_pos : 0 < m := lt_of_lt_of_le hj_pos hch_m
    have hm_ne : ¬ m = 0 := Nat.ne_of_gt hm_pos
    have hm_le : m ≤ L := chooseLevel_le L q (r + d + 1)
    have hlt_len : r + d < us.length := lt_of_le_of_lt hd_le_k hk
    have hu_some : us[r + d]? = some (us[r + d]'hlt_len) := List.getElem?_eq_getElem hlt_len
    set u_s := us[r + d]'hlt_len
    have hprev_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (r + d) (Nat.le_of_lt hlt_len)).1
    have hnext_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (r + d + 1)
      (Nat.succ_le_of_lt hlt_len)).1
    have hst1 : runState (L := L) G₀ q sparsify us (r + d + 1) =
        (step (runState (L := L) G₀ q sparsify us (r + d)) u_s sparsify).state := by
      simp [runState, hu_some, u_s]
    have hstep_ch : chooseLevel L (runState (L := L) G₀ q sparsify us (r + d)).q
        ((runState (L := L) G₀ q sparsify us (r + d)).t + 1) = m := by
      rw [hprev_inv.q_eq, hprev_inv.t_eq]
    set G_s := G₀.applyBatch (us.take (r + d + 1))
    set G_k1 := G₀.applyBatch (us.take (k + 1))
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
      dsimp only [G_k1, G_s]; rw [htk_rd1_k1, applyBatch_append]
    have hinv_sk := batch_delOrSplit_invariants delta_sk G_s hVGs hBV_sk hds_sk
    have hVG_k1 : G_k1.IsValid := hGk1_eq ▸ hinv_sk.1
    have hGrd1_E : eG ∈ G_s.E := hinv_sk.2.1 (hGk1_eq ▸ heG')
    have htk' : us.take (r + d + 1) = us.take (r + d) ++ [u_s] := take_succ_of_getElem? hu_some
    have hGs_eq : G_s = (runState (L := L) G₀ q sparsify us (r + d)).G.applyUpdate u_s := by
      simp [G_s, hprev_inv.G_eq, htk', MGraph.applyBatch]
    by_cases him : i.1 < m
    · -- `i < m`: `inDom` and `Pi_level` at levels `≤ i` are unchanged on surviving `eG`.
      have h0_1 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom ⟨0, Nat.zero_lt_succ L⟩ :=
        hnext_inv.inDom0 ▸ hGrd1_E
      have h0_0 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d)).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
        rw [hprev_inv.inDom0]
        obtain ⟨_, _, hu_v⟩ := batchIsValid_take us G₀ (r + d) hBV hds
        have hmem : eG ∈ ((G₀.applyBatch (us.take (r + d))).applyUpdate u_s).E := by
          have : G_s = (G₀.applyBatch (us.take (r + d))).applyUpdate u_s := by
            dsimp only [G_s]; rw [htk', applyBatch_append]; rfl
          rwa [← this]
        exact E_applyUpdate_subset (hu_v u_s hu_some).2 hmem
      have hcongr_in : ∀ l : Fin (L + 1), l.1 < i.1 + 1 →
          (eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom l ↔
           eG ∈ (runState (L := L) G₀ q sparsify us (r + d)).inDom l) := fun l hl => by
        have hlm : l.1 < m := Nat.lt_of_lt_of_le hl him
        have hst1' : (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom l =
            (runState (L := L) G₀ q sparsify us (r + d)).inDom l ∩ G_s.E := by
          rw [hst1]; dsimp only [step]
          simp only [hstep_ch, hm_ne, ↓reduceDIte, hlm, ↓reduceIte, ← hGs_eq]
        rw [hst1']; simp [hGrd1_E]
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
      have hpi_same : piLe (runState (L := L) G₀ q sparsify us (r + d + 1)) i.1 eG =
          piLe (runState (L := L) G₀ q sparsify us (r + d)) i.1 eG := by
        change piLtFrom _ _ (i.1 + 1) eG = piLtFrom _ _ (i.1 + 1) eG
        rw [heq₁, heq₂, hl_eq, hPi_same]
      rw [← Nat.add_assoc, hpi_same]
      exact ih_d i hi
    · -- `m ≤ i`: show `eG ∉ E_aff_s`, so `piLe (st (r + d + 1)) i eG = piLt_mid_s eG = p_r`.
      have hm_ge_i : j - 1 ≤ m - 1 := by omega
      have ih_mid : piLe (runState (L := L) G₀ q sparsify us (r + d)) (m - 1) eG = p_r :=
        ih_d ⟨m - 1, by omega⟩ hm_ge_i
      have h_pi_mid_eq :
          piLtFrom (runState (L := L) G₀ q sparsify us (r + d)).Pi_level
            (fun l => (runState (L := L) G₀ q sparsify us (r + d)).inDom l ∩ G_s.E) m eG =
          piLe (runState (L := L) G₀ q sparsify us (r + d)) (m - 1) eG := by
        have hsub1 : (m - 1) + 1 = m := Nat.sub_add_cancel hm_pos
        change _ = piLtFrom _ _ ((m - 1) + 1) eG
        rw [hsub1]
        exact piLtFrom_congr_inDom _ fun l _ => by
          simp only [Finset.mem_inter, and_iff_left_iff_imp]
          intro _; exact hGrd1_E
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
      -- Show `S_prev_s ⊆ S_r` and `allTouched G_s delta_sk ⊆ S_r`.
      have hS_sub : S_prev_s ⊆
          allTouched (G₀.applyBatch (us.take r)) ((us.take (k + 1)).drop r) := by
        set rm := lastRebuild q L (m - 1) (r + d)
        have hrm_le : rm ≤ r + d := lastRebuild_le q L (m - 1) (r + d)
        have hrm_ge_r : r ≤ rm := by
          have h1 : lastRebuild q L (j - 1) (r + d) = r := by
            rw [hr_eq_k]
            exact lastRebuild_idempotent_le hq (by rw [← hr_eq_k]; omega)
              (by rw [← hr_eq_k]; exact hd_le_k)
          rw [← h1]
          exact lastRebuild_mono_level hq (by omega) (le_trans (Nat.sub_le m 1) hm_le)
        have hSprev_eq : S_prev_s =
            allTouched (G₀.applyBatch (us.take rm)) ((us.take (r + d + 1)).drop rm) := by
          dsimp only [S_prev_s]
          rw [hprev_inv.S_level_eq ⟨m - 1, by omega⟩]
          have hdrop_app : (us.take (r + d + 1)).drop rm = (us.take (r + d)).drop rm ++ [u_s] := by
            rw [htk', List.drop_append_of_le_length]
            rw [List.length_take]; exact le_trans hrm_le (Nat.le_min.mpr ⟨le_rfl, Nat.le_of_lt hlt_len⟩)
          have hGapp : (G₀.applyBatch (us.take rm)).applyBatch ((us.take (r + d)).drop rm) =
              G₀.applyBatch (us.take (r + d)) := by
            have htk_rm : us.take (r + d) = us.take rm ++ (us.take (r + d)).drop rm := by
              have h1 : (us.take (r + d)).take rm = us.take rm := by
                rw [List.take_take, min_eq_left hrm_le]
              rw [← h1]; exact (List.take_append_drop rm (us.take (r + d))).symm
            conv_rhs => rw [htk_rm]
            exact (applyBatch_append G₀ (us.take rm) ((us.take (r + d)).drop rm)).symm
          rw [hdrop_app, allTouched_append, hGapp, hprev_inv.G_eq]
          simp [allTouched]
          rfl
        have htk_rm1 : us.take (r + d + 1) = us.take rm ++ (us.take (r + d + 1)).drop rm := by
          have h1 : (us.take (r + d + 1)).take rm = us.take rm := by
            rw [List.take_take, min_eq_left (Nat.le_succ_of_le hrm_le)]
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
        have hdrop_k1_r : (us.take (k + 1)).drop r =
            (us.take (r + d + 1)).drop r ++ delta_sk := by
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
      -- Hence `eG ∉ E_aff_s`.
      have heAff_s : eG ∉ E_aff_s := by
        intro hmem
        have hhit : ∃ z ∈ H_lt_s.walkVertices (G_s.tail eG) (piLt_mid_s eG), z ∈ S_prev_s := by
          simpa [E_aff_s, affectedEdges, decide_eq_true_eq] using (Finset.mem_filter.mp hmem).2
        obtain ⟨z, hz, hzS⟩ := hhit
        have hpi_s : piLt_mid_s eG = p_r := h_pi_mid_eq.trans ih_mid
        rw [hpi_s] at hz
        have hwv_eq : H_lt_s.walkVertices (G_s.tail eG) p_r = G_s.walkVertices (G_s.tail eG) p_r :=
          rfl
        rw [hwv_eq] at hz
        have hanc_t : batchAnc delta_sk (G_k1.tail eG) = G_s.tail eG := by
          have hend := hinv_sk.2.2.2.2.2.2 eG hGrd1_E
          rw [hGk1_eq]; exact hend.1
        have hwv_k1 : G_s.walkVertices (G_s.tail eG) p_r = G_k1.walkVertices (G_k1.tail eG) p_r :=
          walkVertices_eq_of_not_mem_allTouched p_r hVGs hBV_sk hds_sk hGk1_eq hp_walk
            (hVG_k1 eG heG').1 hanc_t fun w hw hmemT => hp_disj w hw (hS_sk_sub hmemT)
        rw [hwv_k1] at hz
        exact hp_disj z hz (hS_sub hzS)
      -- Now evaluate `piLe (st (r + d + 1)) m eG = piLt_mid_s eG = p_r`.
      have he0 : eG ∈ (runState (L := L) G₀ q sparsify us (r + d + 1)).inDom
          ⟨0, Nat.zero_lt_succ L⟩ := hnext_inv.inDom0 ▸ hGrd1_E
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
      rw [← Nat.add_assoc, h_pi_1]
      change piLtFrom _ _ (m + 1) eG = p_r
      rw [hprev, hcongr_mid, h_pi_mid_eq, ih_mid]

end

end MinCostFlow.DynSpanner
