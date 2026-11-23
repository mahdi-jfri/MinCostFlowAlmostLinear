module

public import MinCostFlow.DynSpanner.ReembAux

import Mathlib.Tactic

/-!
# Dynamic-spanner domain invariants for leaving-edge coverage (`AssemblyFsCostSpanDom`)

* `runState_H_level_sub_inDom`: at every step `t` and level `l`, `(H_level l).E ⊆ inDom l`.
* `not_mem_inDom_of_not_affected`: if `e ∉ E_aff` at step `k + 1` (level `j > 0`), then
  `e ∉ (runState s).inDom l` for all `r ≤ s ≤ k` and `l ≥ j`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner

public section

/-- At every step `t` of a valid run and every level `l`, every edge in `H_level l` lies in
`inDom l`. -/
theorem runState_H_level_sub_inDom {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ (t : ℕ), t ≤ us.length → ∀ l : Fin (L + 1),
      ((runState (L := L) G₀ q sparsify us t).H_level l).E ⊆
        (runState (L := L) G₀ q sparsify us t).inDom l
  | 0, _, l => by
    have hInv0 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds 0 (Nat.zero_le _)).1
    rcases Nat.eq_zero_or_pos l.1 with hl0 | hlpos
    · have hl : l = ⟨0, Nat.zero_lt_succ L⟩ := Fin.ext hl0
      subst hl
      rw [hInv0.inDom0]
      exact (hInv0.H_level_sub ⟨0, Nat.zero_lt_succ L⟩).2.1
    · intro e he
      have hne : l ≠ 0 := fun h => by subst h; simp at hlpos
      have : ((runState (L := L) G₀ q sparsify us 0).H_level l).E = ∅ := by
        simp [runState, DynSpanner.init, initAt, hne, emptyGraphOn]
      rw [this] at he
      exact absurd he (Finset.notMem_empty e)
  | k + 1, hk1, l => by
    have hk : k < us.length := Nat.lt_of_succ_le hk1
    have ih := runState_H_level_sub_inDom hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le
    set u := us[k]'hk
    have hu : us[k]? = some u := List.getElem?_eq_getElem hk
    obtain ⟨hInvk, -⟩ := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le
    obtain ⟨hInvk1, hRecs⟩ := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hk1
    set st := runState (L := L) G₀ q sparsify us k
    set st' := runState (L := L) G₀ q sparsify us (k + 1)
    have hst' : st' = (step st u sparsify).state := by simp [st', runState, hu]; rfl
    have hch : chooseLevel L st.q (st.t + 1) = chooseLevel L q (k + 1) := by
      rw [hInvk.q_eq, hInvk.t_eq]
    rcases Nat.eq_zero_or_pos (chooseLevel L q (k + 1)) with hj0 | hjpos
    · rcases Nat.eq_zero_or_pos l.1 with hl0 | hlpos
      · have hl : l = ⟨0, Nat.zero_lt_succ L⟩ := Fin.ext hl0
        subst hl
        rw [hInvk1.inDom0]
        exact (hInvk1.H_level_sub ⟨0, Nat.zero_lt_succ L⟩).2.1
      · intro e he
        have hne : l ≠ 0 := fun h => by subst h; simp at hlpos
        have h0 : (st'.H_level l).E = ∅ := by
          rw [hst']; dsimp only [step]
          rw [dite_eq_left_of_eq_true (eq_true (hch.trans hj0))]
          simp [initAt, hne, emptyGraphOn]
        rw [h0] at he
        exact absurd he (Finset.notMem_empty e)
    · have hjne : chooseLevel L st.q (st.t + 1) ≠ 0 := by
        rw [hch]; exact Nat.pos_iff_ne_zero.mp hjpos
      set j := chooseLevel L q (k + 1)
      have hHlev : st'.H_level l =
          if l.1 < j then (st.H_level l).applyBatch (restrictUpdate u (st.H_level l))
          else if l.1 = j then
            let G' := st.G.applyUpdate u
            let H_mid := fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
            let H_lt := unionGraphLt G' H_mid j
            let inDom_mid := fun i => st.inDom i ∩ G'.E
            let piLt_mid := piLtFrom st.Pi_level inDom_mid j
            let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
              touchedVertices st.G u
            let E_aff := affectedEdges G' H_lt piLt_mid S_prev
            let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
            let H_aux := buildAuxHost G' H_lt E_aff
            let embJH := projWalk G' H_lt piLt_mid S_prev
            let out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
            { V := G'.V, E := out.Jtilde.E, tail := G'.tail, head := G'.head }
          else emptyGraphOn (st.G.applyUpdate u) := by
        rw [hst']; dsimp only [step]
        rw [dite_eq_right_of_eq_false (eq_false hjne)]
        simp only [hch]
      have hDom : st'.inDom l =
          if l.1 < j then st.inDom l ∩ (st.G.applyUpdate u).E
          else if l.1 = j then
            let G' := st.G.applyUpdate u
            let H_mid := fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
            let H_lt := unionGraphLt G' H_mid j
            let inDom_mid := fun i => st.inDom i ∩ G'.E
            let piLt_mid := piLtFrom st.Pi_level inDom_mid j
            let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
              touchedVertices st.G u
            affectedEdges G' H_lt piLt_mid S_prev
          else ∅ := by
        rw [hst']; dsimp only [step]
        rw [dite_eq_right_of_eq_false (eq_false hjne)]
        simp only [hch]
      intro e he
      rw [hHlev] at he
      rw [hDom]
      split_ifs at he ⊢ with hlt heq
      · obtain ⟨-, -, hU_val⟩ := batchIsValid_take us G₀ k hBV hds
        obtain ⟨hu_val, hdu⟩ := hU_val u hu
        have hsub := (isSubgraph_restrictUpdate (hInvk.H_level_sub l) (hInvk.H_level_V l)
          hu_val hdu).2.2.2.1
        rw [hsub] at he
        obtain ⟨he1, he2⟩ := Finset.mem_inter.mp he
        rw [← hInvk.G_eq] at he2
        exact Finset.mem_inter.mpr ⟨ih l he1, he2⟩
      · dsimp only at he ⊢
        set G' := st.G.applyUpdate u
        set H_mid := fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
        set H_lt := unionGraphLt G' H_mid j
        set inDom_mid := fun i => st.inDom i ∩ G'.E
        set piLt_mid := piLtFrom st.Pi_level inDom_mid j
        set S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
          touchedVertices st.G u
        set E_aff := affectedEdges G' H_lt piLt_mid S_prev
        set J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
        set H_aux := buildAuxHost G' H_lt E_aff
        set embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
        by_cases hne : E_aff.Nonempty
        · simp only [hne, ↓reduceIte] at he
          have hRec := hRecs k (Nat.lt_succ_self k) u hu
          obtain ⟨-, -, -, -, -, -, -, hAuxV, hJV, hEmbAux, -, -⟩ := hRec.rebuild_sizes hjpos
          have hJm : J.m ≤ mMax := by
            have hsub1 : J.E ⊆ G'.E := Finset.filter_subset _ _
            have hG'_eq : G' = st'.G := by
              rw [hst']; dsimp only [step]; rw [dite_eq_right_of_eq_false (eq_false hjne)]
            have hsub2 : G'.E ⊆ G₀.E := by
              rw [hG'_eq, hInvk1.G_eq]
              exact (batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀
                (batchIsValid_take us G₀ (k + 1) hBV hds).1
                (batchIsValid_take us G₀ (k + 1) hBV hds).2.1).2.1
            exact le_trans (Finset.card_le_card (hsub1.trans hsub2)) hGm₀
          have hLen1 : J.E.Nonempty → 1 ≤ Embedding.length embJH J := by
            rintro ⟨x, hx⟩
            have hle : (embJH x).length ≤ Embedding.length embJH J :=
              Finset.le_sup (f := fun y => (embJH y).length) hx
            have hpos : 1 ≤ (embJH x).length := by
              simp only [embJH, projWalk, List.length_append, List.length_cons, List.length_nil]
              omega
            omega
          exact (hSpec H_aux J embJH hAuxV hJV hJm hLen1 hEmbAux).1.2.1 he
        · simp only [hne, ↓reduceIte] at he
          exact he
      · simp [emptyGraphOn] at he

/-- Companion to `piLe_eq_of_not_affected`: under the same hypotheses, `eG` never enters
`inDom l` for any level `l ≥ j` at any step `r ≤ s ≤ k`. -/
theorem not_mem_inDom_of_not_affected {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
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
      ∀ l : Fin (L + 1), j ≤ l.1 →
        eG ∉ (runState (L := L) G₀ q sparsify us s).inDom l := by
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
    intro _ l hl
    have hr_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r
      (Nat.le_of_lt (Nat.lt_of_le_of_lt hr_le_k hk))).1
    have hr_ch : chooseLevel L q r ≤ j - 1 :=
      lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
    have hl_not : chooseLevel L q (lastRebuild q L l.1 r) < l.1 := by
      have hlr : lastRebuild q L l.1 r = r := by
        have hdvd_B : phasePeriod q L l.1 ∣ phasePeriod q L (j - 1) :=
          phasePeriod_dvd_of_le (by omega) (Nat.le_of_lt_succ l.2)
        have hdvd_r : phasePeriod q L l.1 ∣ r :=
          dvd_trans hdvd_B (lastRebuild_dvd q L (j - 1) (k + 1))
        exact lastRebuild_eq_self_of_dvd hdvd_r
      rw [hlr]
      omega
    simp only [Nat.add_zero]
    rw [(hr_inv.inactive l hl_not).1]
    exact Finset.notMem_empty eG
  | succ d ih =>
    intro hle_k l hl
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
    have hst1 : runState (L := L) G₀ q sparsify us (r + d + 1) =
        (step (runState (L := L) G₀ q sparsify us (r + d)) u_s sparsify).state := by
      simp [runState, hu_some, u_s]
    have hstep_ch : chooseLevel L (runState (L := L) G₀ q sparsify us (r + d)).q
        ((runState (L := L) G₀ q sparsify us (r + d)).t + 1) = m := by
      rw [hprev_inv.q_eq, hprev_inv.t_eq]
    rw [← Nat.add_assoc, hst1]
    dsimp only [step]
    simp only [hstep_ch, hm_ne, ↓reduceDIte]
    split_ifs with hlm heq
    · intro hmem
      exact ih_d l hl (Finset.mem_inter.mp hmem).1
    · -- `l.1 = m`: show `eG ∉ E_aff_s` using `piLe_eq_of_not_affected`.
      set G_s := G₀.applyBatch (us.take (r + d + 1))
      set G_k1 := G₀.applyBatch (us.take (k + 1))
      set delta_sk := (us.take (k + 1)).drop (r + d + 1)
      have h_rd1_k1 : r + d + 1 ≤ k + 1 := Nat.succ_le_succ hd_le_k
      have htk_rd1_k1 : us.take (k + 1) = us.take (r + d + 1) ++ delta_sk := by
        have h1 : (us.take (k + 1)).take (r + d + 1) = us.take (r + d + 1) := by
          rw [List.take_take, min_eq_left h_rd1_k1]
        rw [← h1]; exact (List.take_append_drop (r + d + 1) (us.take (k + 1))).symm
      obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
      have hBV_split := (MinCostFlow.DynSpanner.batchIsValid_append G₀ (us.take (r + d + 1)) delta_sk).mp
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
      have ih_mid : piLe (runState (L := L) G₀ q sparsify us (r + d)) (m - 1) eG = p_r :=
        piLe_eq_of_not_affected hVG₀ hL hq hGm₀ hSpec hBV hds hk j hj_pos hj_le hj_eq
          heG' hp_walk hp_disj (r + d) (Nat.le_add_right r d) hd_le_k ⟨m - 1, by omega⟩
          (by change j - 1 ≤ m - 1; omega)
      have h_pi_mid_eq :
          piLtFrom (runState (L := L) G₀ q sparsify us (r + d)).Pi_level
            (fun i => (runState (L := L) G₀ q sparsify us (r + d)).inDom i ∩ G_s.E) m eG =
          piLe (runState (L := L) G₀ q sparsify us (r + d)) (m - 1) eG := by
        have hsub1 : (m - 1) + 1 = m := Nat.sub_add_cancel hm_pos
        change _ = piLtFrom _ _ ((m - 1) + 1) eG
        rw [hsub1]
        exact piLtFrom_congr_inDom _ fun i _ => by
          simp only [Finset.mem_inter, and_iff_left_iff_imp]
          intro _; exact hGrd1_E
      set S_prev_s := (runState (L := L) G₀ q sparsify us (r + d)).S_level ⟨m - 1, by omega⟩ ∪
        touchedVertices (runState (L := L) G₀ q sparsify us (r + d)).G u_s
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
      intro hmem
      rw [← hGs_eq] at hmem
      have hhit : ∃ z ∈ G_s.walkVertices (G_s.tail eG)
          (piLtFrom (runState (L := L) G₀ q sparsify us (r + d)).Pi_level
            (fun i => (runState (L := L) G₀ q sparsify us (r + d)).inDom i ∩ G_s.E) m eG),
          z ∈ S_prev_s := by
        exact of_decide_eq_true (Finset.mem_filter.mp hmem).2
      obtain ⟨z, hz, hzS⟩ := hhit
      rw [h_pi_mid_eq, ih_mid] at hz
      have hanc_t : batchAnc delta_sk (G_k1.tail eG) = G_s.tail eG := by
        have hend := hinv_sk.2.2.2.2.2.2 eG hGrd1_E
        rw [hGk1_eq]; exact hend.1
      have hwv_k1 : G_s.walkVertices (G_s.tail eG) p_r = G_k1.walkVertices (G_k1.tail eG) p_r :=
        walkVertices_eq_of_not_mem_allTouched p_r hVGs hBV_sk hds_sk hGk1_eq hp_walk
          (hVG_k1 eG heG').1 hanc_t fun w hw hmemT => hp_disj w hw (hS_sk_sub hmemT)
      rw [hwv_k1] at hz
      exact hp_disj z hz (hS_sub hzS)
    · exact Finset.notMem_empty eG


end

end MinCostFlow.SparseCore.Program
