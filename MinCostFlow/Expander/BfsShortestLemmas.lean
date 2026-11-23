module

public import MinCostFlow.Expander.CsrBfsProg

/-!
# Shortest-Path BFS Distance Lower Bound and Loop Invariant Helpers

This file defines the auxiliary BFS shortest-path invariant `BfsShortestInv`, proves it is
preserved by initialization, skip, push, and pop transitions of `bfsPathProc`, extracts the edge
relaxation property at termination, and proves `dist_le_walk_edges_length_add_one`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited
open MinCostFlow.Spanner

/-- Auxiliary shortest-path invariant maintained during the BFS main loop (`bfs_main_loop`):
1. Queue distances are non-decreasing along `queue[0 .. qTail - 1]`.
2. Every vertex at distance `≥ 2` has its parent `parV[x]` already popped (`< qHead`).
3. Every kept incident neighbor of every fully scanned vertex (`i + 1 < qHead`) has distance at
   most `dist(queue[i]) + 1`.
4. Every kept already-scanned incident neighbor of `cur` (`csrOff G cur + t < k`) has distance at
   most `dist(cur) + 1`. -/
def BfsShortestInv (n workAddr parVBase queueBase vMaskAddr eMaskAddr : ℕ)
    (G : Cited.Graph) (memInit : ℕ → ℕ) (st : State) : Prop :=
  (∀ i j, i ≤ j → j < st.regs 15 →
    st.mem (workAddr + st.mem (queueBase + i)) ≤ st.mem (workAddr + st.mem (queueBase + j))) ∧
  (∀ x < n, 2 ≤ st.mem (workAddr + x) →
    ∃ ip < st.regs 14, st.mem (queueBase + ip) = st.mem (parVBase + x)) ∧
  (∀ i, i + 1 < st.regs 14 →
    ∀ t (ht : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length),
      let q_entry := (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht
      memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
      st.mem (workAddr + q_entry.2.2) ≤ st.mem (workAddr + st.mem (queueBase + i)) + 1) ∧
  (0 < st.regs 14 →
    ∀ t (ht : t < (csrIncAux (st.regs 18) 0 G.edges).length),
      csrOff G (st.regs 18) + t < st.regs 16 →
      let q_entry := (csrIncAux (st.regs 18) 0 G.edges)[t]'ht
      memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
      st.mem (workAddr + q_entry.2.2) ≤ st.mem (workAddr + st.regs 18) + 1)

lemma bfsShortestInv_init
    {n workAddr parVBase queueBase vMaskAddr eMaskAddr u : ℕ}
    {G : Cited.Graph} {memInit : ℕ → ℕ} {st : State}
    (hr14 : st.regs 14 = 0) (hr15 : st.regs 15 = 1)
    (hdist : ∀ x < n, st.mem (workAddr + x) = if x = u then 1 else 0) :
    BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    rw [hr15] at hj
    have hi : i = j := by omega
    subst hi; exact le_refl _
  · intro x hx hge
    rw [hdist x hx] at hge
    split_ifs at hge <;> omega
  · intro i hi
    rw [hr14] at hi; omega
  · intro hpos
    rw [hr14] at hpos; omega

/-- `BfsShortestInv` reads only the memory and registers 14, 15, 16 and 18, so it transfers
to any state that agrees with the old one there. -/
lemma bfsShortestInv_congr
    {n workAddr parVBase queueBase vMaskAddr eMaskAddr : ℕ}
    {G : Cited.Graph} {memInit : ℕ → ℕ} {st st' : State}
    (hmem : st'.mem = st.mem) (hr14 : st'.regs 14 = st.regs 14)
    (hr15 : st'.regs 15 = st.regs 15) (hr16 : st'.regs 16 = st.regs 16)
    (hr18 : st'.regs 18 = st.regs 18)
    (hshort : BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st) :
    BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st' := by
  unfold BfsShortestInv
  rw [hmem, hr14, hr15, hr16, hr18]
  exact hshort

lemma bfsShortestInv_skip
    {n workAddr parVBase queueBase vMaskAddr eMaskAddr : ℕ}
    {G : Cited.Graph} {memInit : ℕ → ℕ} {st st' : State}
    (hn : G.n = n) (hval : G.IsValid)
    (hq_lt : ∀ i < st.regs 15, st.mem (queueBase + i) < n ∧ st.mem (workAddr + st.mem (queueBase + i)) ≠ 0)
    (hpar_dist : ∀ x < n, 2 ≤ st.mem (workAddr + x) →
      st.mem (workAddr + st.mem (parVBase + x)) + 1 = st.mem (workAddr + x))
    (h14_15 : st.regs 14 ≤ st.regs 15)
    (hcur_pos : 0 < st.regs 14)
    (hcur_eq : st.regs 18 = st.mem (queueBase + (st.regs 14 - 1)))
    (hcur_le : csrOff G (st.regs 18) ≤ st.regs 16)
    (hk_lt : st.regs 16 < st.regs 17)
    (hkEnd_eq : st.regs 17 = csrOff G (st.regs 18 + 1))
    (hmem : st'.mem = st.mem)
    (hr14 : st'.regs 14 = st.regs 14) (hr15 : st'.regs 15 = st.regs 15)
    (hr16 : st'.regs 16 = st.regs 16 + 1) (hr18 : st'.regs 18 = st.regs 18)
    (hstep_ok :
      let q_entry := (csrIncAux (st.regs 18) 0 G.edges)[st.regs 16 - csrOff G (st.regs 18)]'(by rw [hkEnd_eq, csrOff_succ] at hk_lt; omega)
      memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
      st.mem (workAddr + q_entry.2.2) ≠ 0)
    (hshort : BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st) :
    BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st' := by
  rcases hshort with ⟨hq_mono, hpar_pop, hsp_d, hsc_d⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    rw [hmem]; rw [hr15] at hj; exact hq_mono i j hij hj
  · intro x hx hge
    rw [hmem, hr14]; exact hpar_pop x hx (by rw [← hmem]; exact hge)
  · dsimp only
    intro i hi t ht hvm hem
    rw [hr14] at hi
    have ht' : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by rwa [← hmem]
    have hget_eq : (csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t]'ht =
        (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht' := by simp only [hmem]
    rw [hget_eq] at hvm hem ⊢
    rw [hmem]
    exact hsp_d i hi t ht' hvm hem
  · dsimp only
    intro _ t ht hlt hvm hem
    have ht' : t < (csrIncAux (st.regs 18) 0 G.edges).length := by rwa [← hr18]
    have hget_eq : (csrIncAux (st'.regs 18) 0 G.edges)[t]'ht =
        (csrIncAux (st.regs 18) 0 G.edges)[t]'ht' := by simp only [hr18]
    rw [hget_eq] at hvm hem ⊢
    rw [hmem, hr18]
    rw [hr16] at hlt
    by_cases hlt_old : csrOff G (st.regs 18) + t < st.regs 16
    · exact hsc_d hcur_pos t ht' hlt_old hvm hem
    · have ht_eq : t = st.regs 16 - csrOff G (st.regs 18) := by rw [hr18] at hlt; omega
      subst ht_eq
      set nbr := (csrIncAux (st.regs 18) 0 G.edges)[st.regs 16 - csrOff G (st.regs 18)].2.2
      have hnbr_nz : st.mem (workAddr + nbr) ≠ 0 := hstep_ok hvm hem
      have hcur_nz : st.mem (workAddr + st.regs 18) ≠ 0 := by
        rw [hcur_eq]; exact (hq_lt (st.regs 14 - 1) (by omega)).2
      have hnbr_lt : nbr < n := by
        rw [← hn]; exact (csrIncAux_getElem_lt hval ht').2.1
      by_cases hd2 : 2 ≤ st.mem (workAddr + nbr)
      · have hpi := hpar_dist nbr hnbr_lt hd2
        obtain ⟨ip, hip, hip_eq⟩ := hpar_pop nbr hnbr_lt hd2
        have hmono := hq_mono ip (st.regs 14 - 1) (by omega) (by omega)
        rw [hip_eq, ← hcur_eq] at hmono
        omega
      · omega

lemma bfsShortestInv_push
    {n workAddr parVBase queueBase vMaskAddr eMaskAddr nbr dcur : ℕ}
    {G : Cited.Graph} {memInit : ℕ → ℕ} {st st' : State}
    (hn : G.n = n) (hval : G.IsValid)
    (hq_lt : ∀ i < st.regs 15, st.mem (queueBase + i) < n ∧ st.mem (workAddr + st.mem (queueBase + i)) ≠ 0)
    (hpar_dist : ∀ x < n, 2 ≤ st.mem (workAddr + x) →
      st.mem (workAddr + st.mem (parVBase + x)) + 1 = st.mem (workAddr + x))
    (hscan_prev : ∀ i, i + 1 < st.regs 14 →
      ∀ t (ht : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length),
        let q_entry := (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht
        memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
        st.mem (workAddr + q_entry.2.2) ≠ 0)
    (hscan_cur : 0 < st.regs 14 →
      ∀ t (ht : t < (csrIncAux (st.regs 18) 0 G.edges).length),
        csrOff G (st.regs 18) + t < st.regs 16 →
        let q_entry := (csrIncAux (st.regs 18) 0 G.edges)[t]'ht
        memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
        st.mem (workAddr + q_entry.2.2) ≠ 0)
    (h14_15 : st.regs 14 ≤ st.regs 15)
    (hcur_pos : 0 < st.regs 14)
    (hcur_eq : st.regs 18 = st.mem (queueBase + (st.regs 14 - 1)))
    (hcur_n : st.regs 18 < n) (hnbr_lt : nbr < n)
    (hcur_le : csrOff G (st.regs 18) ≤ st.regs 16)
    (hk_lt : st.regs 16 < st.regs 17) (hkEnd_eq : st.regs 17 = csrOff G (st.regs 18 + 1))
    (hd_cur : st.mem (workAddr + st.regs 18) = dcur)
    (hd_nbr0 : st.mem (workAddr + nbr) = 0)
    (hdcur_pos : 1 ≤ dcur)
    (hcur_ne_nbr : st.regs 18 ≠ nbr)
    (hq_entry_nbr :
      let t := st.regs 16 - csrOff G (st.regs 18)
      let q_entry := (csrIncAux (st.regs 18) 0 G.edges)[t]'(by rw [hkEnd_eq, csrOff_succ] at hk_lt; omega)
      q_entry.2.2 = nbr)
    (hmem_dist : ∀ x < n, st'.mem (workAddr + x) = if x = nbr then dcur + 1 else st.mem (workAddr + x))
    (hmem_parV : st'.mem (parVBase + nbr) = st.regs 18)
    (hmem_parV_ne : ∀ x < n, x ≠ nbr → st'.mem (parVBase + x) = st.mem (parVBase + x))
    (hmem_q : ∀ i < st.regs 15 + 1, st'.mem (queueBase + i) = if i = st.regs 15 then nbr else st.mem (queueBase + i))
    (hr14 : st'.regs 14 = st.regs 14) (hr15 : st'.regs 15 = st.regs 15 + 1)
    (hr16 : st'.regs 16 = st.regs 16 + 1) (hr18 : st'.regs 18 = st.regs 18)
    (hshort : BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st) :
    BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st' := by
  rcases hshort with ⟨hq_mono, hpar_pop, hsp_d, hsc_d⟩
  have hq_dist_eq : ∀ i < st.regs 15, st'.mem (workAddr + st'.mem (queueBase + i)) =
      st.mem (workAddr + st.mem (queueBase + i)) := by
    intro i hi
    have hqi := hq_lt i hi
    have hne : st.mem (queueBase + i) ≠ nbr := fun h => hqi.2 (by rw [h]; exact hd_nbr0)
    rw [hmem_q i (by omega)]
    split_ifs with h1
    · omega
    · rw [hmem_dist _ hqi.1]
      split_ifs with h2
      · exact absurd h2 hne
      · rfl
  have hd_nbr' : st'.mem (workAddr + nbr) = dcur + 1 := by
    rw [hmem_dist nbr hnbr_lt]
    split_ifs <;> [rfl; contradiction]
  have hd_cur' : st'.mem (workAddr + st'.regs 18) = dcur := by
    rw [hr18, hmem_dist _ hcur_n]
    split_ifs with h1
    · exact absurd h1 hcur_ne_nbr
    · exact hd_cur
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    rw [hr15] at hj
    by_cases hjq : j = st.regs 15
    · subst hjq
      rw [hmem_q (st.regs 15) (by omega)]
      split_ifs with h1
      swap
      · exact absurd rfl h1
      rw [hd_nbr']
      by_cases hiq : i = st.regs 15
      · subst hiq
        rw [hmem_q (st.regs 15) (by omega)]
        simp only [↓reduceIte, hd_nbr', le_refl]
      · have hi' : i < st.regs 15 := by omega
        rw [hq_dist_eq i hi']
        have hqi := hq_lt i hi'
        by_cases hd2 : 2 ≤ st.mem (workAddr + st.mem (queueBase + i))
        · have hpi := hpar_dist _ hqi.1 hd2
          obtain ⟨ip, hip, hip_eq⟩ := hpar_pop _ hqi.1 hd2
          have hmono := hq_mono ip (st.regs 14 - 1) (by omega) (by omega)
          rw [hip_eq, ← hcur_eq, hd_cur] at hmono
          omega
        · omega
    · have hj' : j < st.regs 15 := by omega
      have hi' : i < st.regs 15 := by omega
      rw [hq_dist_eq i hi', hq_dist_eq j hj']
      exact hq_mono i j hij hj'
  · intro x hx hge
    rw [hr14]
    rw [hmem_dist x hx] at hge
    by_cases hxn : x = nbr
    · subst hxn
      refine ⟨st.regs 14 - 1, by omega, ?_⟩
      rw [hmem_q _ (by omega)]
      split_ifs with h1
      · omega
      · rw [← hcur_eq, hmem_parV]
    · simp only [hxn, ↓reduceIte] at hge
      obtain ⟨ip, hip, hip_eq⟩ := hpar_pop x hx hge
      refine ⟨ip, hip, ?_⟩
      rw [hmem_q ip (by omega)]
      split_ifs with h1
      · omega
      · rw [hmem_parV_ne x hx hxn, hip_eq]
  · dsimp only
    intro i hi t ht hvm hem
    rw [hr14] at hi
    have hi_ne : i ≠ st.regs 15 := by omega
    have hqi := hq_lt i (by omega)
    have hq_eq : st'.mem (queueBase + i) = st.mem (queueBase + i) := by
      rw [hmem_q i (by omega)]; simp [hi_ne]
    have ht' : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by
      simpa [hq_eq] using ht
    have hget_eq : (csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t]'ht =
        (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht' := by
      simp only [hq_eq]
    rw [hget_eq] at hvm hem ⊢
    have hnz_nbr := hscan_prev i hi t ht' hvm hem
    have hprev := hsp_d i hi t ht' hvm hem
    have hqn : (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t].2.2 < n := by
      rw [← hn]; exact (csrIncAux_getElem_lt hval ht').2.1
    have hq_ne : (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t].2.2 ≠ nbr := by
      intro heq; rw [heq] at hnz_nbr; exact hnz_nbr hd_nbr0
    rw [hmem_dist _ hqn, hq_dist_eq i (by omega)]
    simp [hq_ne, hprev]
  · dsimp only
    intro _ t ht hlt hvm hem
    rw [hr16] at hlt
    have ht' : t < (csrIncAux (st.regs 18) 0 G.edges).length := by rwa [← hr18]
    have hget_eq : (csrIncAux (st'.regs 18) 0 G.edges)[t]'ht =
        (csrIncAux (st.regs 18) 0 G.edges)[t]'ht' := by simp only [hr18]
    rw [hget_eq] at hvm hem ⊢
    rw [hd_cur']
    rw [hr18] at hlt
    by_cases hlt_old : csrOff G (st.regs 18) + t < st.regs 16
    · have hprev := hsc_d hcur_pos t ht' hlt_old hvm hem
      have hnz_nbr := hscan_cur hcur_pos t ht' hlt_old hvm hem
      have hqn : (csrIncAux (st.regs 18) 0 G.edges)[t].2.2 < n := by
        rw [← hn]; exact (csrIncAux_getElem_lt hval ht').2.1
      have hq_ne : (csrIncAux (st.regs 18) 0 G.edges)[t].2.2 ≠ nbr := by
        intro heq; rw [heq] at hnz_nbr; exact hnz_nbr hd_nbr0
      rw [hmem_dist _ hqn]
      simp only [hq_ne, ↓reduceIte]
      omega
    · have ht_eq : t = st.regs 16 - csrOff G (st.regs 18) := by omega
      subst ht_eq
      rw [hq_entry_nbr, hmem_dist nbr hnbr_lt]
      split_ifs <;> [omega; contradiction]

lemma bfsShortestInv_pop
    {n workAddr parVBase queueBase vMaskAddr eMaskAddr : ℕ}
    {G : Cited.Graph} {memInit : ℕ → ℕ} {st st' : State}
    (hcur_of_pos : 0 < st.regs 14 →
      st.regs 18 = st.mem (queueBase + (st.regs 14 - 1)) ∧
      st.regs 17 = csrOff G (st.regs 18 + 1))
    (hk_ge : st.regs 17 ≤ st.regs 16)
    (hmem : st'.mem = st.mem)
    (hr14 : st'.regs 14 = st.regs 14 + 1)
    (hr15 : st'.regs 15 = st.regs 15)
    (hr16 : st'.regs 16 = csrOff G (st'.regs 18))
    (hshort : BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st) :
    BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st' := by
  rcases hshort with ⟨hq_mono, hpar_pop, hsp_d, hsc_d⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    rw [hmem]; rw [hr15] at hj; exact hq_mono i j hij hj
  · intro x hx hge
    rw [hmem, hr14]
    obtain ⟨ip, hip, hip_eq⟩ := hpar_pop x hx (by rwa [← hmem])
    exact ⟨ip, by omega, hip_eq⟩
  · dsimp only
    intro i hi t ht hvm hem
    rw [hr14] at hi
    have ht' : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by rwa [← hmem]
    have hget_eq : (csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t]'ht =
        (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht' := by simp only [hmem]
    rw [hget_eq] at hvm hem ⊢
    rw [hmem]
    by_cases hi_last : i + 1 = st.regs 14
    · have h14_pos : 0 < st.regs 14 := by omega
      obtain ⟨h18_eq, hkEnd_eq⟩ := hcur_of_pos h14_pos
      have hi_idx : i = st.regs 14 - 1 := by omega
      subst hi_idx
      have ht'' : t < (csrIncAux (st.regs 18) 0 G.edges).length := by rwa [← h18_eq] at ht'
      have hget_eq2 : (csrIncAux (st.mem (queueBase + (st.regs 14 - 1))) 0 G.edges)[t]'ht' =
          (csrIncAux (st.regs 18) 0 G.edges)[t]'ht'' := by simp only [h18_eq]
      rw [hget_eq2] at hvm hem ⊢
      have hk_in : csrOff G (st.regs 18) + t < st.regs 16 := by
        have hOff : csrOff G (st.regs 18) + t < csrOff G (st.regs 18 + 1) := by
          rw [csrOff_succ]; omega
        omega
      rw [← h18_eq]
      exact hsc_d h14_pos t ht'' hk_in hvm hem
    · exact hsp_d i (by omega) t ht' hvm hem
  · intro _ t _ hlt
    rw [hr16] at hlt
    omega

lemma bfsShortestInv_step_relax
    {n workAddr parVBase queueBase vMaskAddr eMaskAddr : ℕ}
    {G : Cited.Graph} {memInit : ℕ → ℕ} {st : State}
    (hn : G.n = n)
    (hdist_q : ∀ x < n, st.mem (workAddr + x) ≠ 0 → ∃ i < st.regs 15, st.mem (queueBase + i) = x)
    (hscan_prev : ∀ i, i + 1 < st.regs 14 →
      ∀ t (ht : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length),
        let q_entry := (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht
        memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
        st.mem (workAddr + q_entry.2.2) ≠ 0)
    (hscan_cur : 0 < st.regs 14 →
      ∀ t (ht : t < (csrIncAux (st.regs 18) 0 G.edges).length),
        csrOff G (st.regs 18) + t < st.regs 16 →
        let q_entry := (csrIncAux (st.regs 18) 0 G.edges)[t]'ht
        memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
        st.mem (workAddr + q_entry.2.2) ≠ 0)
    (hcur_of_pos : 0 < st.regs 14 →
      st.regs 18 = st.mem (queueBase + (st.regs 14 - 1)) ∧
      st.regs 17 = csrOff G (st.regs 18 + 1))
    (hterm : st.regs 14 = st.regs 15 ∧ st.regs 17 ≤ st.regs 16)
    (hshort : BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st) :
    ∀ x < G.n, st.mem (workAddr + x) ≠ 0 →
      ∀ j < G.m, memInit (eMaskAddr + j) ≠ 0 →
        ∀ y < G.n, memInit (vMaskAddr + y) ≠ 0 →
          Walk.EdgeMatches (G.edges.getD j (0, 0)) x y →
          st.mem (workAddr + y) ≠ 0 ∧
            st.mem (workAddr + y) ≤ st.mem (workAddr + x) + 1 := by
  rcases hshort with ⟨_, _, hsp_d, hsc_d⟩
  intro x hx hdx_nz j hj hem y hy hvm hmatch
  by_cases hxy : x = y
  · subst hxy
    exact ⟨hdx_nz, Nat.le_succ _⟩
  · obtain ⟨i, hi, hi_eq⟩ := hdist_q x (by omega) hdx_nz
    have hj' : j < G.edges.length := by simpa [Cited.Graph.m] using hj
    have hmem_inc := edge_mem_csrIncAux_of_ne (r := 0) hj' hxy hmatch
    have hex_t : ∃ t, ∃ ht : t < (csrIncAux x 0 G.edges).length,
        (csrIncAux x 0 G.edges)[t].1 = j ∧ (csrIncAux x 0 G.edges)[t].2.2 = y := by
      rcases hmem_inc with hmem_inc | hmem_inc <;>
        obtain ⟨t, ht, hget⟩ := List.mem_iff_getElem.mp hmem_inc <;>
        exact ⟨t, ht, by simp [hget], by simp [hget]⟩
    obtain ⟨t, ht, ht1, ht2⟩ := hex_t
    by_cases hi_last : i + 1 = st.regs 14
    · have h14_pos : 0 < st.regs 14 := by omega
      obtain ⟨h18_eq, hkEnd_eq⟩ := hcur_of_pos h14_pos
      have hi_idx : i = st.regs 14 - 1 := by omega
      have hx_cur : st.regs 18 = x := by rw [h18_eq, ← hi_idx, hi_eq]
      have ht_cur : t < (csrIncAux (st.regs 18) 0 G.edges).length := by simpa [hx_cur] using ht
      have hget_eq : (csrIncAux (st.regs 18) 0 G.edges)[t]'ht_cur =
          (csrIncAux x 0 G.edges)[t]'ht := by simp only [hx_cur]
      have hlt_k : csrOff G (st.regs 18) + t < st.regs 16 := by
        have hOff : csrOff G (st.regs 18) + t < csrOff G (st.regs 18 + 1) := by
          rw [csrOff_succ]; omega
        omega
      have hle := hsc_d h14_pos t ht_cur hlt_k
        (by rw [hget_eq, ht2]; exact hvm) (by rw [hget_eq, ht1]; exact hem)
      have hnz' := hscan_cur h14_pos t ht_cur hlt_k
        (by rw [hget_eq, ht2]; exact hvm) (by rw [hget_eq, ht1]; exact hem)
      exact ⟨by rwa [hget_eq, ht2] at hnz', by rwa [hget_eq, ht2, hx_cur] at hle⟩
    · have hi_lt : i + 1 < st.regs 14 := by omega
      have ht_q : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by
        simpa [hi_eq] using ht
      have hget_eq : (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht_q =
          (csrIncAux x 0 G.edges)[t]'ht := by simp only [hi_eq]
      have hnz' := hscan_prev i hi_lt t ht_q
        (by rw [hget_eq, ht2]; exact hvm) (by rw [hget_eq, ht1]; exact hem)
      have hle := hsp_d i hi_lt t ht_q
        (by rw [hget_eq, ht2]; exact hvm) (by rw [hget_eq, ht1]; exact hem)
      exact ⟨by rwa [hget_eq, ht2] at hnz', by rwa [hget_eq, ht2, hi_eq] at hle⟩

private lemma list_getD_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

private lemma list_getD_zero_of_head {l : List ℕ} {u : ℕ}
    (hlen : 0 < l.length) (hhead : l.head? = some u) :
    l.getD 0 0 = u := by
  rw [List.getD_eq_getElem _ _ hlen]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem hlen, ← List.head?_eq_getElem?]
  exact hhead

private lemma list_getD_last_of_getLast {l : List ℕ} {k v : ℕ}
    (hlen : l.length = k + 1) (hlast : l.getLast? = some v) :
    l.getD k 0 = v := by
  have hk : k < l.length := by omega
  rw [List.getD_eq_getElem _ _ hk]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem hk]
  rw [List.getLast?_eq_getElem?] at hlast
  simpa [hlen] using hlast

/-- Any walk `W` from `u` to `v` in the unmasked subgraph (`eMask ≠ 0` on edges, `vMask ≠ 0` on
vertices) reaches `v` with label `dist v ≠ 0` and `dist v ≤ W.edges.length + 1`, assuming `dist`
starts at `dist u = 1` and relaxes every unmasked edge out of labeled vertices. -/
theorem dist_le_walk_edges_length_add_one
    {G : Cited.Graph} (hV : G.IsValid) {dist vMask eMask : ℕ → ℕ} {u v : ℕ}
    (hdu : dist u = 1)
    (hstep : ∀ x < G.n, dist x ≠ 0 →
      ∀ j < G.m, eMask j ≠ 0 →
        ∀ y < G.n, vMask y ≠ 0 →
          Walk.EdgeMatches (G.edges.getD j (0, 0)) x y →
          dist y ≠ 0 ∧ dist y ≤ dist x + 1)
    {W : Walk} (hW : W.IsWalk G u v)
    (heW : ∀ e ∈ W.edges, eMask e ≠ 0)
    (hvW : ∀ x ∈ W.verts, vMask x ≠ 0) :
    dist v ≠ 0 ∧ dist v ≤ W.edges.length + 1 := by
  have hverts_lt := Walk.isWalk_verts_lt hV hW
  rcases hW with ⟨_, _, ⟨_, hWe, huv⟩ | ⟨_, hlen, hhead, hlast, hedges, hwalk_step⟩⟩
  · subst huv
    simp [hWe, hdu]
  · have hprefix : ∀ k ≤ W.edges.length,
        dist (W.verts.getD k 0) ≠ 0 ∧ dist (W.verts.getD k 0) ≤ k + 1 := by
      intro k
      induction k with
      | zero =>
        intro _
        rw [list_getD_zero_of_head (by omega) hhead, hdu]
        decide
      | succ k ih =>
        intro hk
        have ihk := ih (Nat.le_of_succ_le hk)
        have hkn : k < W.edges.length := by omega
        have hx_mem : W.verts.getD k 0 ∈ W.verts := list_getD_mem (by omega)
        have hy_mem : W.verts.getD (k + 1) 0 ∈ W.verts := list_getD_mem (by omega)
        have he_mem : W.edges.getD k 0 ∈ W.edges := list_getD_mem hkn
        have hstep_k := hstep
          (W.verts.getD k 0) (hverts_lt _ hx_mem) ihk.1
          (W.edges.getD k 0) (hedges _ he_mem) (heW _ he_mem)
          (W.verts.getD (k + 1) 0) (hverts_lt _ hy_mem) (hvW _ hy_mem)
          (hwalk_step k hkn)
        exact ⟨hstep_k.1, by omega⟩
    have hfinal := hprefix W.edges.length (le_refl _)
    rw [list_getD_last_of_getLast hlen hlast] at hfinal
    exact hfinal

end MinCostFlow.Expander
