module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBQuery

import Mathlib.Tactic.Linarith

/-!
# Step B Single-Round Post-Query Matched Handler (`ProgStepBRoundPost`)

Defines `sbOneRoundAfterQueryStmt`, list/filterMap helpers (`filterMap_range_nodup`,
`sb_rpairs_fst_snd`), and verifies the `.matched` post-router branch (`sbOneRound_afterQuery_matched`)
that scatters matched edges, completes all `t` cut blocks into witness graphs and `fA`,
and re-establishes `SbLoopInv ... (m + 1)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Post-Query Statement and FilterMap Helpers -/

/-- Post-query router call and cut/matched dispatch inside `sbOneRoundStmt`. -/
def sbOneRoundAfterQueryStmt (bRoute : ℕ) : Stmt :=
  seqStmts [
    .store (.reg 23) (.reg 25),
    .cond (.bin .eq (.reg 25) (.const 0))
      .nop
      (seqStmts [
        .assign 27 (.reg 12),
        .assign 28 (.load (.reg 1)),
        .assign 29 (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 28))),
        .assign 30 (.load (.bin .add (.reg 7) (.const 2))),
        .assign 31 (.load (.bin .add (.reg 7) (.const 1))),
        .call 12 bRoute [.reg 1, .reg 11, .reg 23, .reg 30, .reg 31, .const 100, .reg 6, .reg 27, .reg 29],
        .cond (.bin .eq (.load (.reg 27)) (.const 1))
          (seqStmts [
            sbCopyCutZeroStmt 27 10 30 31 32,
            .assign 13 (.const 1)
          ])
          sbMatchedPostStmt
      ])
  ]

theorem sbOneRoundAfterQueryStmt_noRand (bRoute : ℕ) :
    (sbOneRoundAfterQueryStmt bRoute).NoRand := by
  simp [sbOneRoundAfterQueryStmt, sbCopyCutZeroStmt, sbMatchedPostStmt, sbScatterStmt,
    sbCompleteCutLoopStmt, sbMarkListStmt, sbZipDualStmt, scSetMatchedStmt, scCollectUnmatchedStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

lemma filterMap_range_nodup {n : ℕ} {P : ℕ → Bool} :
    ((List.range n).filterMap fun i => if P i then some i else none).Nodup := by
  have hgen : ∀ l : List ℕ, l.Nodup →
      (l.filterMap fun i => if P i then some i else none).Nodup := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a rest ih =>
      intro hnd
      rcases List.nodup_cons.mp hnd with ⟨hnot, hrest⟩
      simp only [List.filterMap_cons]
      split_ifs
      · rw [List.nodup_cons]
        refine ⟨fun hmem => ?_, ih hrest⟩
        rcases List.mem_filterMap.mp hmem with ⟨b, hb, hfb⟩
        split_ifs at hfb
        cases hfb; exact hnot hb
      · exact ih hrest
  exact hgen (List.range n) List.nodup_range

lemma sb_rpairs_fst_snd {nBlocks b : ℕ} {vs : List ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} :
    let rpairs : List (ℕ × (Finset ℕ × Finset ℕ)) := (List.range nBlocks).filterMap fun i =>
      if bst.active i then
        match res i with
        | .expander _ => none
        | .cut U =>
            let B := blockSet vs b i
            let C' := padToHalf B (smallerSide B U)
            some (i, (C', B \ C'))
      else none
    rpairs.map Prod.fst = ((List.range nBlocks).filterMap fun i =>
      if bst.active i then match res i with | .cut _ => some i | .expander _ => none else none) ∧
    rpairs.map Prod.snd = ((List.range nBlocks).filterMap fun i =>
      if bst.active i then match res i with
        | .cut U =>
            let B := blockSet vs b i
            let C' := padToHalf B (smallerSide B U)
            some (C', B \ C')
        | .expander _ => none
      else none) := by
  dsimp only
  rw [List.map_filterMap, List.map_filterMap]
  constructor
  · congr 1; funext i
    by_cases h : bst.active i
    · simp only [h, ite_true]; cases res i <;> rfl
    · simp [h]
  · congr 1; funext i
    by_cases h : bst.active i
    · simp only [h, ite_true]; cases res i <;> rfl
    · simp [h]

/-! ## 2. Matched Post-Router Handler (`sbOneRound_afterQuery_matched`) -/

/-- Total length of `callsFakeEdges calls` is at most `k` whenever `calls.length ≤ 49 * cp.L + 2`,
each call has `fake.length ≤ z`, and `z = k / cp.D q`. -/
lemma sb_callsFakeEdges_length_le_k {cp : CoreParams} {r q k z R : ℕ} {G : Graph} {X : Finset ℕ}
    {calls : List RoutedCall}
    (hcfg : CoreParamsValid cp r) (hq1 : 1 ≤ q) (hqr : q ≤ r) (hz_eq : z = k / cp.D q)
    (hlen : calls.length ≤ 49 * cp.L + 2) (hval : ∀ c ∈ calls, c.Valid G X R z) :
    (callsFakeEdges calls).length ≤ k := by
  have h1 : ∀ l : List RoutedCall, (∀ c ∈ l, c.fake.length ≤ z) →
      (callsFakeEdges l).length ≤ l.length * z := by
    intro l
    induction l with
    | nil => intro _; simp [callsFakeEdges]
    | cons c rest ih =>
      intro hv
      simp only [callsFakeEdges, List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      have hhd := hv c List.mem_cons_self
      have htl := ih (fun x hx => hv x (List.mem_cons_of_mem c hx))
      dsimp only [callsFakeEdges] at htl
      omega
  have h2 := h1 calls (fun c hc => (hval c hc).2.2.2.2.2)
  have h3 : calls.length * z ≤ (49 * cp.L + 2) * (k / cp.D q) := by
    rw [hz_eq]; exact Nat.mul_le_mul_right _ hlen
  exact le_trans (le_trans h2 h3) (stepB_fake_len_le_k hcfg hq1 hqr)

/-- Runs the matched branch of `sbOneRoundAfterQueryStmt` via `sbMatchedPost_triple`. -/
private lemma sbOneRound_matched_run {cfg : ParamConfig} {M r q w Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 m : ℕ}
    {p : Program} {memStart memR : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    {matchings : List (List (ℕ × ℕ))} {stQ stR : State} {ω : ℕ → Bool}
    (hX_sub : X ⊆ Finset.range G.n) (hb_even : Even b) (hnb_b : nBlocks * b ≤ k)
    (ht_le_nb : cutIds.length ≤ nBlocks) (hm_le : m ≤ 49 * LParam M)
    (hmod : SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z m bst)
    (hInvQ : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 memStart G X bst nBlocks res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists stQ)
    (hr14Q : stQ.regs 14 = (callsFakeEdges bst.calls).length)
    (hcut_nd : cutIds.Nodup) (hcut_lt : ∀ i ∈ cutIds, i < nBlocks)
    (hvtp : ValidTerminalPairs X pairs)
    (hmlen_t : matchings.length = cutIds.length)
    (hpm_p : ∀ i (hi : i < pairs.length),
      let M_i := matchings.getD i []
      let p_i := pairs[i]'hi
      (∀ e ∈ M_i, e.1 ∈ p_i.1 ∧ e.2 ∈ p_i.2) ∧ (M_i.map Prod.fst).Nodup ∧ (M_i.map Prod.snd).Nodup)
    (hflat_le_k : matchings.flatten.length ≤ k) (hflat_le_n : matchings.flatten.length ≤ G.n)
    (hF_atR : EdgesAt memR fA (callsFakeEdges bst.calls))
    (hF_cap : (callsFakeEdges bst.calls).length + (completeBatchFake pairs matchings).length ≤ k)
    (hprev_W : ∀ i < nBlocks,
      let ps := sbPersist h0 k b nBlocks (LParam M)
      GraphAt memR (ps.wBaseA + i * ps.wStride)
        (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i))))
    (htag0 : memR (stQ.regs 12) = 0)
    (hmLenR : memR (stQ.regs 12 + 1) = matchings.flatten.length)
    (hmAtR : EdgesAt memR (stQ.regs 12 + 2) matchings.flatten)
    (hlocR : ∀ u < G.n, memR (locA + u) = 0)
    (hmemR_eq : stR.mem = memR) (hr27R : stR.regs 27 = stQ.regs 12)
    (hlt27R : ∀ r < 27, r ≠ 12 → stR.regs r = stQ.regs r)
    (hfrR_below : ∀ a < stQ.regs 12, memR a = Function.update stQ.mem pairsA cutIds.length a)
    (hbounds : let ps := sbPersist h0 k b nBlocks (LParam M)
      locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ DisjointRange locA G.n fA (2 * k) ∧
      ps.hPersist ≤ cutRecsA ∧ pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧ hSub0 = tmpA + 4 * b + 2 + b ∧
      stQ.regs 12 + 2 + 2 * G.n < 2 ^ w ∧ 16 < 2 ^ w) :
    let ps := sbPersist h0 k b nBlocks (LParam M)
    let t := cutIds.length
    ∃ st' cPost,
      Runs w p ω (.cond (.bin .eq (.load (.reg 27)) (.const 1))
          (seqStmts [sbCopyCutZeroStmt 27 10 30 31 32, .assign 13 (.const 1)])
          sbMatchedPostStmt) stR .normal st' cPost ∧
      st'.regs 14 = (callsFakeEdges bst.calls).length + (completeBatchFake pairs matchings).length ∧
      (∀ r < 27, r ≠ 14 → st'.regs r = stR.regs r) ∧
      (∀ u < G.n, st'.mem (locA + u) = 0) ∧
      (∀ a, (a < locA ∨ locA + G.n ≤ a) → (a < tmpA ∨ tmpA + 2 * b ≤ a) →
        (a < fA ∨ fA + 2 * k ≤ a) → (a < ps.wBaseA ∨ ps.wBaseA + nBlocks * ps.wStride ≤ a) →
        st'.mem a = memR a) ∧
      EdgesAt st'.mem fA (callsFakeEdges bst.calls ++ completeBatchFake pairs matchings) ∧
      (∀ idx (hidx : idx < t),
        let i := cutIds[idx]'hidx
        let p_i := pairs[idx]'(hInvQ.lens_eq.2.2.2.2.symm ▸ hidx)
        GraphAt st'.mem (ps.wBaseA + i * ps.wStride)
          (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i) ++
            (matchings.getD idx [] ++ completeMatchingFake p_i.1 p_i.2 (matchings.getD idx []))))) ∧
      (∀ i < nBlocks, i ∉ cutIds →
        GraphAt st'.mem (ps.wBaseA + i * ps.wStride)
          (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i)))) ∧
      cPost ≤ 340 * k + 350 * nBlocks + 280 := by
  intro ps t
  have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
  rcases hbounds with ⟨hloc_h, hf_h, hd_lf, hP_le, hpairs_eq, htmp_eq, hhSub_eq, hrt_w, hw16⟩
  rw [hps_id] at hP_le
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨u, hu⟩; omega
  have hgeQ := hInvQ.h_ge
  have hmem_lt_rt : ∀ a, cutRecsA ≤ a → a < tmpA → a ≠ pairsA → memR a = stQ.mem a := fun a h1 h2 hne => by
    rw [hfrR_below a (by omega), Function.update_of_ne hne]
  have hloc_p : locA + G.n ≤ pairsA := by omega
  have hf_p : fA + 2 * k ≤ pairsA := by omega
  have hw_p : ps.wBaseA + nBlocks * ps.wStride ≤ pairsA := by omega
  have htmp_w : tmpA < 2 ^ w := by omega
  have hcut_p : cutRecsA ≤ pairsA := by omega
  have hrec_lists : ∀ idx (hidx : idx < t),
      let cL := cPrimeLists[idx]'(hInvQ.lens_eq.2.2.1.symm ▸ hidx)
      let oL := compLists[idx]'(hInvQ.lens_eq.2.2.2.1.symm ▸ hidx)
      let cA := cPrimeAddrs[idx]'(hInvQ.lens_eq.1.symm ▸ hidx)
      let oA := compAddrs[idx]'(hInvQ.lens_eq.2.1.symm ▸ hidx)
      let p_i := pairs[idx]'(hInvQ.lens_eq.2.2.2.2.symm ▸ hidx)
      cL.length = b / 2 ∧ cL.Pairwise (· < ·) ∧ cL.toFinset = p_i.1 ∧ ListAt memR cA cL ∧
      DisjointRange locA G.n cA (b / 2) ∧ DisjointRange tmpA (2 * b) cA (b / 2) ∧
      DisjointRange fA (2 * k) cA (b / 2) ∧ DisjointRange ps.wBaseA (nBlocks * ps.wStride) cA (b / 2) ∧
      cA + b / 2 < 2 ^ w ∧
      oL.length = b / 2 ∧ oL.Pairwise (· < ·) ∧ oL.toFinset = p_i.2 ∧ ListAt memR oA oL ∧
      DisjointRange locA G.n oA (b / 2) ∧ DisjointRange tmpA (2 * b) oA (b / 2) ∧
      DisjointRange fA (2 * k) oA (b / 2) ∧ DisjointRange ps.wBaseA (nBlocks * ps.wStride) oA (b / 2) ∧
      oA + b / 2 < 2 ^ w := by
    intro idx hidx
    rcases hInvQ.recs_at idx hidx with ⟨hcA, hoA, _, _, _, _, _, hcL, hoL, hcLen, hoLen, hLatC, hLatO⟩
    have hidx_mul : idx * (2 + b) + (2 + b) ≤ nBlocks * (2 + b) := by
      have := Nat.mul_le_mul_right (2 + b) (show idx + 1 ≤ nBlocks from Nat.lt_of_lt_of_le hidx ht_le_nb)
      rwa [Nat.succ_mul] at this
    dsimp only
    rw [hcA] at hLatC ⊢
    rw [hoA] at hLatO ⊢
    have hc_lo : pairsA < pairsA + 1 + idx * (2 + b) + 1 :=
      lt_of_lt_of_le (Nat.lt_succ_self pairsA) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    have hc_hi : pairsA + 1 + idx * (2 + b) + 1 + b / 2 ≤ tmpA := by
      rw [htmp_eq]; have : b / 2 ≤ b := Nat.div_le_self b 2; linarith
    have ho_lo : pairsA < pairsA + 1 + idx * (2 + b) + 2 + b / 2 :=
      lt_of_lt_of_le (Nat.lt_succ_self pairsA) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    have ho_hi : pairsA + 1 + idx * (2 + b) + 2 + b / 2 + b / 2 ≤ tmpA := by
      rw [htmp_eq]; linarith
    refine ⟨hcLen, hcL ▸ pairwise_lt_sort _, by rw [hcL]; ext u; simp,
      fun u hu => (hmem_lt_rt _ (le_trans hcut_p (le_of_lt (lt_of_lt_of_le hc_lo (Nat.le_add_right _ _))))
        (lt_of_lt_of_le (Nat.add_lt_add_left (hcLen ▸ hu) _) hc_hi)
        (Nat.ne_of_gt (lt_of_lt_of_le hc_lo (Nat.le_add_right _ _)))).trans (hLatC u hu),
      Or.inl (le_trans hloc_p (le_of_lt hc_lo)), Or.inr hc_hi,
      Or.inl (le_trans hf_p (le_of_lt hc_lo)), Or.inl (le_trans hw_p (le_of_lt hc_lo)),
      lt_of_le_of_lt hc_hi htmp_w,
      hoLen, hoL ▸ pairwise_lt_sort _, by rw [hoL]; ext u; simp,
      fun u hu => (hmem_lt_rt _ (le_trans hcut_p (le_of_lt (lt_of_lt_of_le ho_lo (Nat.le_add_right _ _))))
        (lt_of_lt_of_le (Nat.add_lt_add_left (hoLen ▸ hu) _) ho_hi)
        (Nat.ne_of_gt (lt_of_lt_of_le ho_lo (Nat.le_add_right _ _)))).trans (hLatO u hu),
      Or.inl (le_trans hloc_p (le_of_lt ho_lo)), Or.inr ho_hi,
      Or.inl (le_trans hf_p (le_of_lt ho_lo)), Or.inl (le_trans hw_p (le_of_lt ho_lo)),
      lt_of_le_of_lt ho_hi htmp_w⟩
  have hrun : ∃ o st' cPost,
      Runs w p ω (.cond (.bin .eq (.load (.reg 27)) (.const 1))
          (seqStmts [sbCopyCutZeroStmt 27 10 30 31 32, .assign 13 (.const 1)])
          sbMatchedPostStmt) stR o st' cPost ∧
      (normalPost fun st' =>
        st'.regs 14 = (callsFakeEdges bst.calls).length + (completeBatchFake pairs matchings).length ∧
        (∀ r < 27, r ≠ 14 → st'.regs r = stR.regs r) ∧
        (∀ u < G.n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + G.n ≤ a) → (a < tmpA ∨ tmpA + 2 * b ≤ a) →
          (a < fA ∨ fA + 2 * k ≤ a) → (a < ps.wBaseA ∨ ps.wBaseA + nBlocks * ps.wStride ≤ a) →
          st'.mem a = memR a) ∧
        EdgesAt st'.mem fA (callsFakeEdges bst.calls ++ completeBatchFake pairs matchings) ∧
        (∀ idx (hidx : idx < t),
          let i := cutIds[idx]'hidx
          let p_i := pairs[idx]'(hInvQ.lens_eq.2.2.2.2.symm ▸ hidx)
          GraphAt st'.mem (ps.wBaseA + i * ps.wStride)
            (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i) ++
              (matchings.getD idx [] ++ completeMatchingFake p_i.1 p_i.2 (matchings.getD idx []))))) ∧
        (∀ i < nBlocks, i ∉ cutIds →
          GraphAt st'.mem (ps.wBaseA + i * ps.wStride)
            (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i))))) o st' ∧
      cPost ≤ 340 * k + 350 * nBlocks + 280 := by
    refine runs_start_le ?_
    refine runs_cond_le (v := 0)
      (Expr.eval_eq_false (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr27R) (hmemR_eq ▸ htag0))
        (Expr.eval_const (by omega)) (by decide) (by omega))
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_triple_le
      (sbMatchedPost_triple (w := w) (n := G.n) (b := b) (k := k) (nBlocks := nBlocks)
        (t := t) (maxR := ps.maxR) (wStride := ps.wStride) (locA := locA) (fA := fA)
        (cutRecsA := cutRecsA) (tmpA := tmpA) (rtOutA := stQ.regs 12) (wBaseA := ps.wBaseA)
        (prevF := (callsFakeEdges bst.calls).length) (p := p) (mem := memR) (X := X)
        (pairs := pairs) (cutIds := cutIds) (cPrimeAddrs := cPrimeAddrs) (compAddrs := compAddrs)
        (cPrimeLists := cPrimeLists) (compLists := compLists) (matchings := matchings)
        (prevFEs := callsFakeEdges bst.calls)
        (prevEdges := fun i => witnessEdges (bst.rounds i) (bst.numRounds i)) (st₀ := stR)
        hInvQ.lens_eq.2.2.2.2 rfl hInvQ.lens_eq.1 hInvQ.lens_eq.2.1 hInvQ.lens_eq.2.2.1 hInvQ.lens_eq.2.2.2.1
        hcut_nd hcut_lt hX_sub hvtp hmlen_t (fun idx hidx => hpm_p idx (hInvQ.lens_eq.2.2.2.2.symm ▸ hidx))
        (fun idx hidx => (hmem_lt_rt _ (by omega) (by omega) (by omega)).trans (hInvQ.recs_at idx hidx).2.2.1)
        (fun idx hidx => (hmem_lt_rt _ (by omega) (by omega) (by omega)).trans (hInvQ.recs_at idx hidx).2.2.2.1)
        (fun idx hidx => (hmem_lt_rt _ (by omega) (by omega) (by omega)).trans (hInvQ.recs_at idx hidx).2.2.2.2.1)
        hrec_lists rfl hF_atR hF_cap rfl hprev_W
        (fun i hi => by
          rw [witnessEdges_length (hmod.rounds_len i hi)]
          exact Nat.mul_le_mul_right _ ((hmod.numRounds_le i hi).trans (by dsimp only [ps, sbPersist]; omega)))
        (fun idx hidx => by
          dsimp only
          have hi_lt : cutIds[idx]'hidx < nBlocks := hcut_lt _ (List.getElem_mem hidx)
          rw [witnessEdges_length (hmod.rounds_len _ hi_lt)]
          have hpmi := hpm_p idx (hInvQ.lens_eq.2.2.2.2.symm ▸ hidx)
          have hrec := hInvQ.recs_at idx hidx
          have hc1 : (pairs[idx]'(hInvQ.lens_eq.2.2.2.2.symm ▸ hidx)).1.card = b / 2 := by
            have := hrec.2.2.2.2.2.2.2.2.2.1; rw [hrec.2.2.2.2.2.2.2.1, Finset.length_sort] at this; exact this
          have hc2 : (pairs[idx]'(hInvQ.lens_eq.2.2.2.2.symm ▸ hidx)).2.card = b / 2 := by
            have := hrec.2.2.2.2.2.2.2.2.2.2.1; rw [hrec.2.2.2.2.2.2.2.2.1, Finset.length_sort] at this; exact this
          have hcm := (completeMatchingFake_spec (le_of_eq (hc1.trans hc2.symm)) hpmi.1 hpmi.2.1 hpmi.2.2).2.2.2.2.2.2.1
          rw [List.length_append, hc1] at hcm
          have hnr : bst.numRounds (cutIds[idx]'hidx) + 1 ≤ ps.maxR := by
            have := hmod.numRounds_le _ hi_lt; dsimp only [ps, sbPersist]; omega
          have hmul := Nat.mul_le_mul_right (b / 2) hnr
          rw [Nat.succ_mul] at hmul; omega)
        hmLenR hmAtR hlocR
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hd_lf
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inl (by omega)) (Or.inl (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hw16
        ((hlt27R 4 (by decide) (by decide)).trans hInvQ.args.r4)
        ((hlt27R 8 (by decide) (by decide)).trans hInvQ.args.r8)
        ((hlt27R 9 (by decide) (by decide)).trans hInvQ.args.r9)
        ((hlt27R 14 (by decide) (by decide)).trans hr14Q)
        ((hlt27R 22 (by decide) (by decide)).trans hInvQ.r22)
        ((hlt27R 24 (by decide) (by decide)).trans hInvQ.r24)
        ((hlt27R 25 (by decide) (by decide)).trans hInvQ.r25)
        hr27R hmemR_eq) rfl ?_ (by
          have htb : t * (b / 2) ≤ k / 2 := by
            have h1 : t * (b / 2) ≤ nBlocks * (b / 2) := Nat.mul_le_mul_right _ ht_le_nb
            have h2 : 2 * (nBlocks * (b / 2)) = nBlocks * (2 * (b / 2)) := by ring
            rw [h2half] at h2; omega
          have h220 : 220 * t * (b / 2) = 220 * (t * (b / 2)) := by ring
          simp only [Expr.size]; omega)
    rintro (_ | _) st' h'
    · rcases h' with ⟨h14', hoth', _, hloc', hfr', hF', hWcut', hWnon'⟩
      exact ⟨h14', fun r hr h14 => hoth' r (by omega) h14, hloc', hfr', hF', hWcut', hWnon'⟩
    · exact h'
  rcases hrun with ⟨o, st', cPost, hr, hp, hc⟩
  cases o with
  | returned _ => exact False.elim hp
  | normal =>
    rcases hp with ⟨h14', hreg', hloc', hfr', hF', hWcut', hWnon'⟩
    exact ⟨st', cPost, hr, h14', hreg', hloc', hfr', hF', hWcut', hWnon', hc⟩

/-- Handles the `.matched matchings emb` outcome after `bRoute` returns in a round. -/
theorem sbOneRound_afterQuery_matched {cfg : ParamConfig} {M r q w C_sp Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 hRound cutRecsA pairsA tmpA hSub0 m : ℕ}
    {p : Program} {mem0 memStart memR : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    {matchings : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    {stQ stR : State} {ω : ℕ → Bool}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (_hG_val : G.IsValid) (hX_at : VertsAt mem0 xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2) (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k) (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hm_le : m ≤ 49 * LParam M)
    (hmod : SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z m bst)
    (hpers : SbPersistAt memStart G X b nBlocks (LParam M) h0 bst)
    (hF_at0 : EdgesAt memStart fA (callsFakeEdges bst.calls))
    (hfr0 : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) →
      (a < fA ∨ fA + 2 * k ≤ a) → (a < outA ∨ outA + 2 + k ≤ a) → memStart a = mem0 a)
    (hgeom : locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ DisjointRange locA G.n fA (2 * k))
    (hlay : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ hRound ∧
      hRound ≤ (sbPersist h0 k b nBlocks (LParam M)).hPersist +
        m * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks ∧
      cutRecsA = hRound ∧ pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧ hSub0 = tmpA + 4 * b + 2 + b ∧
      hRound + sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks < 2 ^ w ∧
      128 < 2 ^ w)
    (hInvQ : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 memStart G X bst nBlocks res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists stQ)
    (hr14Q : stQ.regs 14 = (callsFakeEdges bst.calls).length)
    (hr15Q : stQ.regs 15 = m)
    (ht0 : cutIds.length ≠ 0)
    (hvtp : ValidTerminalPairs X pairs)
    (hrc_eq : routeOrCut G X pairs (coreParamsOf cfg M r).Δ (coreParamsOf cfg M r).L 100 z =
      .matched matchings emb)
    (hmemR_eq : stR.mem = memR) (hr27R : stR.regs 27 = stQ.regs 12)
    (hlt27R : ∀ r < 27, r ≠ 12 → stR.regs r = stQ.regs r)
    (hRoutR : RouteOutAt memR (stQ.regs 12) (.matched matchings emb))
    (hRt_le : stQ.regs 12 + 2 + 2 * G.n ≤ stR.regs 12)
    (hRt_ub : stR.regs 12 ≤ stQ.regs 12 + 2 + 2 * G.n +
      outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q))
    (hzfR : ZeroFrom memR (stR.regs 12))
    (hfrR_below : ∀ a < stQ.regs 12, memR a = Function.update stQ.mem pairsA cutIds.length a) :
    ∃ st' cPost,
      Runs w p ω (.cond (.bin .eq (.load (.reg 27)) (.const 1))
          (seqStmts [sbCopyCutZeroStmt 27 10 30 31 32, .assign 13 (.const 1)])
          sbMatchedPostStmt) stR .normal st' cPost ∧
      SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X (m + 1)
        { mem := st'.mem, regs := Function.update st'.regs 15 (m + 1), pos := st'.pos } ∧
      st'.regs 15 = m ∧
      cPost ≤ 340 * k + 350 * nBlocks + 280 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  set t := cutIds.length
  set rtOutA := stQ.regs 12
  set hAfterRt := stR.regs 12
  set memP := Function.update stQ.mem pairsA t
  rcases hgeom with ⟨hloc_h, hf_h, hd_lf⟩
  rcases hlay with ⟨hhP_le, hhR_le, hcut_eq, hpairs_eq, htmp_eq, hhSub_eq, hStep_w, hw128⟩
  have hw16 : 16 < 2 ^ w := by omega
  have hr12R : stR.regs 12 = hAfterRt := rfl
  have hcfg : CoreParamsValid cp r := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnb_div : nBlocks = k / b := by rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX_at.1]
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hb_pos : 0 < b := by have := harith.2.2.1; omega
  have hb_even : Even b := harith.2.2.2.1
  have hXL : X.card < 2 ^ cp.L := by rw [← hX_at.1]; exact harith.2.2.2.2.2.2.2.2
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le vs b
    rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  have hb_le_k : b ≤ k := by rw [hb_eq]; exact hklo
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by
    dsimp only [ps, sbPersist]; omega
  have hsub0_bound : hSub0 ≤ hRound + 6 * k + 5 * nBlocks + 3 := by
    have hmul : nBlocks * (2 + b) = 2 * nBlocks + nBlocks * b := by ring
    omega
  have hstep_def : sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks =
      nBlocks * Sprev + outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
      6 * k + 6 * nBlocks + 2 * G.n + 10 := rfl
  have hQ12_step : rtOutA + 2 + 2 * G.n +
      outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) ≤
      hRound + sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks := by
    have := hInvQ.h_le; omega
  have ht_le_nb : t ≤ nBlocks := by
    dsimp only [t]; rw [hInvQ.cutIds_eq]
    exact (List.length_filterMap_le _ _).trans (by rw [List.length_range])
  have hfrP_below : ∀ a < ps.wRelA, (a < locA ∨ locA + G.n ≤ a) →
      (a < ps.actA ∨ ps.wBaseA ≤ a) → memP a = memStart a := fun a ha h1 h2 => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.frame_persist a ha h1 h2
  have hfrP_w : ∀ a, ps.wBaseA ≤ a → a < ps.wRelA → memP a = memStart a := fun a h1 h2 => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.frame_w a h1 h2
  have hlocP : ∀ u < G.n, memP (locA + u) = 0 := fun u hu => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.loc0 u hu
  have hstep_mod := sbModelInv_round_step hcfg hX_sub hGloop hdegG hXL
    (Finset.sort_nodup X (· ≤ ·)) (by ext u; simp) hb_pos hb_even
    (hnb_eq ▸ hmod) res (fun i hi hact => hInvQ.res_spec i (hnb_eq.symm ▸ hi) hact)
  set rpairs : List (ℕ × (Finset ℕ × Finset ℕ)) := (List.range nBlocks).filterMap fun i =>
    if bst.active i then match res i with
      | .expander _ => none
      | .cut U => let B := blockSet vs b i; let C' := padToHalf B (smallerSide B U); some (i, (C', B \ C'))
    else none
  have hfs := sb_rpairs_fst_snd (nBlocks := nBlocks) (b := b) (vs := vs) (bst := bst) (res := res)
  have hcut_rp : cutIds = rpairs.map Prod.fst := hInvQ.cutIds_eq.trans hfs.1.symm
  have hpairs_rp : pairs = rpairs.map Prod.snd := hInvQ.pairs_eq.trans hfs.2.symm
  have hrp_len : rpairs.length = t := by dsimp only [t]; rw [hcut_rp, List.length_map]
  have hstep_rc := hstep_mod.2.2
  split at hstep_rc
  · next U hrt =>
      have : RouteResult.cut U = RouteResult.matched matchings emb := by
        rw [← hrt, ← hrc_eq]; congr 1; rw [← hnb_eq, hpairs_rp]; rfl
      cases this
  next matchings' emb' hrt =>
  have hmeq : RouteResult.matched matchings' emb' = RouteResult.matched matchings emb := by
    rw [← hrt, ← hrc_eq]; congr 1; rw [← hnb_eq, hpairs_rp]; rfl
  cases hmeq
  rcases hstep_rc with ⟨hmod', hnewM_eq⟩
  rcases hRoutR with ⟨htag0, hmLenR, hmAtR⟩
  have hmspec := routeOrCut_isMatchingPlayer.spec G X pairs cp.Δ cp.L 100 z hX_sub hGloop
    hcfg.hΔ_pos hdegG hcfg.hL hXL (by decide) hvtp
  rw [hrc_eq] at hmspec
  have hrc_val : (RoutedCall.mk matchings.flatten emb (completeBatchFake pairs matchings)).Valid
      G X (routeCong cp.Δ 100 cp.L) z :=
    routedCall_valid_of_matched hvtp hmspec
  rcases hmspec with ⟨hmlen_p, hpm_p, _, _, _⟩
  have hmlen_t : matchings.length = t := hmlen_p.trans hInvQ.lens_eq.2.2.2.2
  have hflat_le_k : matchings.flatten.length ≤ k := by
    have h1 : matchings.flatten.length ≤ t * (b / 2) := by
      have hsum : matchings.flatten.length = (matchings.map List.length).sum := List.length_flatten
      rw [hsum]
      have hle_all : ∀ idx (hidx : idx < matchings.length), (matchings[idx]'hidx).length ≤ b / 2 := by
        intro idx hidx
        have hpmi := hpm_p idx (hmlen_p ▸ hidx)
        have hidx_c : idx < cutIds.length := by omega
        have hlen_p1 : (pairs[idx]'(hmlen_p ▸ hidx)).1.card = b / 2 := by
          have hrec := hInvQ.recs_at idx hidx_c
          have hcL := hrec.2.2.2.2.2.2.2.1
          have hcl := hrec.2.2.2.2.2.2.2.2.2.1
          rw [hcL, Finset.length_sort] at hcl; exact hcl
        have hnd1 : ((matchings.getD idx []).map Prod.fst).Nodup := hpmi.2.1
        have hsub1 : ((matchings.getD idx []).map Prod.fst).toFinset ⊆ (pairs[idx]'(hmlen_p ▸ hidx)).1 := by
          intro v hv
          rcases List.mem_map.mp (List.mem_toFinset.mp hv) with ⟨e, he, rfl⟩
          exact (hpmi.1 e he).1
        have hle1 : (matchings.getD idx []).length ≤ (pairs[idx]'(hmlen_p ▸ hidx)).1.card := by
          rw [← List.length_map Prod.fst, ← List.toFinset_card_of_nodup hnd1]
          exact Finset.card_le_card hsub1
        simpa [List.getD_eq_getElem?_getD, hidx, hlen_p1] using hle1
      have hgen : ∀ (L : List (List (ℕ × ℕ))), (∀ x ∈ L, x.length ≤ b / 2) →
          (L.map List.length).sum ≤ L.length * (b / 2) := by
        intro L
        induction L with
        | nil => intro _; simp
        | cons a rest ih =>
          intro hall
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
          have h1 := hall a List.mem_cons_self
          have h2 := ih fun x hx => hall x (List.mem_cons_of_mem _ hx)
          omega
      have h2 := hgen matchings fun x hx => by
        rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩; exact hle_all idx hidx
      rw [hmlen_t] at h2; exact h2
    have h2 : t * (b / 2) ≤ nBlocks * b := Nat.mul_le_mul ht_le_nb (Nat.div_le_self b 2)
    omega
  have hflat_le_n : matchings.flatten.length ≤ G.n := by
    have hk_le_n : k ≤ G.n := by rw [hX_at.1]; exact (Finset.card_le_card hX_sub).trans (by simp)
    omega
  have hcut_nd : cutIds.Nodup := by
    rw [hInvQ.cutIds_eq]
    have h := filterMap_range_nodup (n := nBlocks) (P := fun i =>
      if bst.active i then match res i with | .cut _ => true | .expander _ => false else false)
    convert h using 1
    congr 1; funext i
    by_cases h1 : bst.active i = true
    · simp only [h1, ↓reduceIte]; cases res i <;> rfl
    · simp [h1]
  have hcut_lt : ∀ i ∈ cutIds, i < nBlocks := fun i hi => by
    rw [hInvQ.cutIds_eq, List.mem_filterMap] at hi
    rcases hi with ⟨j, hj, hfj⟩
    split_ifs at hfj
    cases h : res j with
    | expander _ => rw [h] at hfj; cases hfj
    | cut _ => rw [h] at hfj; cases hfj; exact List.mem_range.mp hj
  have hpmap_eq : (List.map Prod.snd ((List.range nBlocks).filterMap fun i =>
      if bst.active i = true then match res i with
        | .expander _ => none
        | .cut U =>
          have B := blockSet (X.sort (· ≤ ·)) b i
          have C' := padToHalf B (smallerSide B U)
          some (i, (C', B \ C'))
      else none)) = pairs := by
    rw [hpairs_rp]
  have hpairs_ne : pairs.isEmpty = false := by
    have hplen : pairs.length = t := hInvQ.lens_eq.2.2.2.2
    cases hp : pairs with
    | nil => exfalso; rw [hp] at hplen; exact ht0 hplen.symm
    | cons _ _ => rfl
  have hF_cap : (callsFakeEdges bst.calls).length + (completeBatchFake pairs matchings).length ≤ k := by
    let rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩
    have hlen : (bst.calls ++ [rc]).length ≤ 49 * cp.L + 2 := by
      rw [List.length_append, List.length_singleton]; have := hmod.calls_len; show bst.calls.length + 1 ≤ 49 * LParam M + 2; omega
    have hval : ∀ c ∈ bst.calls ++ [rc], c.Valid G X (routeCong cp.Δ 100 cp.L) z := by
      intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact hmod.calls_valid c h1
      · rw [List.mem_singleton.mp h2]; exact hrc_val
    have h := sb_callsFakeEdges_length_le_k hcfg (by omega) hqr hz_eq hlen hval
    simpa [callsFakeEdges, rc] using h
  have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
  have hprev_W : ∀ i < nBlocks,
      GraphAt memR (ps.wBaseA + i * ps.wStride)
        (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i))) := fun i hi => by
    have hWlen : 2 + 2 * (witnessEdges (bst.rounds i) (bst.numRounds i)).length ≤ ps.wStride := by
      rw [witnessEdges_length (hmod.rounds_len i hi)]
      have h1 : bst.numRounds i * (b / 2) ≤ (49 * LParam M + 1) * (b / 2) :=
        Nat.mul_le_mul_right _ ((hmod.numRounds_le i hi).trans (by omega))
      have h2 : ps.wStride = 2 + 2 * ((49 * LParam M + 1) * (b / 2)) := by dsimp only [ps, sbPersist]; ring
      omega
    have hiw : i * ps.wStride + ps.wStride ≤ nBlocks * ps.wStride := by
      have : (i + 1) * ps.wStride ≤ nBlocks * ps.wStride := Nat.mul_le_mul_right _ (by omega); linarith
    have hW0 := hpers.w_at i hi; dsimp only at hW0; rw [← hX_at.1, hps_id] at hW0
    have hagree : ∀ a, ps.wBaseA + i * ps.wStride ≤ a → a < ps.wBaseA + i * ps.wStride + ps.wStride →
        memR a = memStart a := fun a h1 h2 =>
      (hfrR_below a (by have := hInvQ.h_ge; omega)).trans (hfrP_w a (by omega) (by omega))
    rw [graphAt_mk_iff] at hW0 ⊢
    exact ⟨(hagree _ (le_refl _) (by omega)).trans hW0.1,
      (hagree _ (by omega) (by omega)).trans hW0.2.1,
      fun idx hidx => ⟨(hagree _ (by omega) (by omega)).trans (hW0.2.2 idx hidx).1,
        (hagree _ (by omega) (by omega)).trans (hW0.2.2 idx hidx).2⟩⟩
  have hF_atR : EdgesAt memR fA (callsFakeEdges bst.calls) := fun idx hidx => by
    have hlen_lt : (callsFakeEdges bst.calls).length ≤ k :=
      sb_callsFakeEdges_length_le_k hcfg (by omega) hqr hz_eq
        (hmod.calls_len.trans (by show m ≤ 49 * LParam M + 2; omega)) hmod.calls_valid
    have h1 : fA + 2 * idx < locA ∨ locA + G.n ≤ fA + 2 * idx := by rcases hd_lf with h | h <;> [right; left] <;> omega
    have h2 : fA + 2 * idx + 1 < locA ∨ locA + G.n ≤ fA + 2 * idx + 1 := by rcases hd_lf with h | h <;> [right; left] <;> omega
    rw [hfrR_below _ (by have := hInvQ.h_ge; omega), hfrR_below _ (by have := hInvQ.h_ge; omega),
      hfrP_below _ (by omega) h1 (Or.inl (by omega)), hfrP_below _ (by omega) h2 (Or.inl (by omega))]
    exact hF_at0 idx hidx
  have hlocR : ∀ u < G.n, memR (locA + u) = 0 := fun u hu => by
    rw [hfrR_below _ (by have := hInvQ.h_ge; omega)]; exact hlocP u hu
  have hrun_ok := sbOneRound_matched_run (p := p) (ω := ω) hX_sub hb_even hnb_b ht_le_nb hm_le hmod hInvQ hr14Q
    hcut_nd hcut_lt hvtp hmlen_t hpm_p hflat_le_k hflat_le_n hF_atR hF_cap hprev_W
    htag0 hmLenR hmAtR hlocR hmemR_eq hr27R hlt27R hfrR_below
    ⟨hloc_h, hf_h, hd_lf, hcut_eq ▸ hhP_le, hpairs_eq, htmp_eq, hhSub_eq, by omega, hw16⟩
  rcases hrun_ok with ⟨st', cPost, hPost, hr14', hreg', hloc', hfr', hF', hWcut', hWnon', hcPost⟩
  dsimp only at hfr' hWcut' hWnon'
  rw [hps_id] at hfr' hWcut' hWnon'
  have hcallsF_eq : ∀ (ps1 ps2 : List (Finset ℕ × Finset ℕ)), ps1 = pairs → ps2 = pairs →
      callsFakeEdges (if ps1.isEmpty then bst.calls
        else bst.calls ++ [⟨matchings.flatten, emb, completeBatchFake ps2 matchings⟩]) =
      callsFakeEdges bst.calls ++ completeBatchFake pairs matchings := by
    rintro _ _ rfl rfl; simp [hpairs_ne, callsFakeEdges]
  have hpmap_mod : ∀ (f : ℕ → Option (ℕ × (Finset ℕ × Finset ℕ))),
      (∀ i, f i = if bst.active i = true then match res i with
        | .expander _ => none
        | .cut U => have B := blockSet (X.sort (· ≤ ·)) b i; have C' := padToHalf B (smallerSide B U); some (i, (C', B \ C'))
        else none) →
      List.map Prod.snd ((List.range nBlocks).filterMap f) = pairs := by
    intro f hf
    rw [← hpmap_eq]; congr 2; funext i; exact hf i
  refine ⟨st', cPost, hPost, ?_, (hreg' 15 (by decide) (by decide)).trans ((hlt27R 15 (by decide) (by decide)).trans hr15Q), hcPost⟩
  refine ⟨sbArgs_of_eq hInvQ.args (fun r hr => by
      dsimp only; rw [Function.update_of_ne (by omega)]
      exact (hreg' r (by omega) (by omega)).trans (hlt27R r (by omega) (by omega))),
    by simp, hloc',
    by dsimp only; rw [Function.update_of_ne (by decide), hreg' 12 (by decide) (by decide), hr12R, hps_id]; have := hInvQ.h_ge; omega,
    by dsimp only; rw [Function.update_of_ne (by decide), hreg' 12 (by decide) (by decide), hr12R, hps_id]; rw [Nat.succ_mul]; omega,
    fun a ha => by
      dsimp only at ha ⊢; rw [Function.update_of_ne (by decide), hreg' 12 (by decide) (by decide), hr12R] at ha
      rw [hfr' a (Or.inr (by have := hInvQ.h_ge; omega)) (Or.inr (by have := hInvQ.h_ge; omega))
        (Or.inr (by have := hInvQ.h_ge; omega)) (Or.inr (by have := hInvQ.h_ge; omega))]
      exact hzfR a ha,
    fun a ha h1 h2 h3 => by
      rw [hfr' a h1 (Or.inl (by omega)) h2 (Or.inl (by omega)),
        hfrR_below a (by have := hInvQ.h_ge; omega),
        hfrP_below a (by omega) h1 (Or.inl (by omega))]
      exact hfr0 a ha h1 h2 h3,
    Or.inr ⟨by dsimp only; rw [Function.update_of_ne (by decide), hreg' 13 (by decide) (by decide), hlt27R 13 (by decide) (by decide), hInvQ.r13],
      _, hnb_eq.symm ▸ hmod', ?_,
      by dsimp only; rw [Function.update_of_ne (by decide), hr14', ← List.length_append]
         congr 1; apply Eq.symm; apply hcallsF_eq
         · apply hpmap_mod; intro i; by_cases h1 : bst.active i = true <;> simp [h1]; cases res i <;> rfl
         · apply hpmap_mod; intro i; by_cases h1 : bst.active i = true <;> simp [h1]; cases res i <;> rfl,
      by dsimp only; convert hF' using 1
         apply hcallsF_eq
         · apply hpmap_mod; intro i; by_cases h1 : bst.active i = true <;> simp [h1]; cases res i <;> rfl
         · apply hpmap_mod; intro i; by_cases h1 : bst.active i = true <;> simp [h1]; cases res i <;> rfl⟩⟩
  -- Prove `SbPersistAt st'.mem G X b nBlocks (LParam M) h0 bst'`
  have hmem_pres : ∀ a, h0 ≤ a → a < ps.wBaseA → st'.mem a = stQ.mem a := fun a h1 h2 => by
    rw [hfr' a (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl h2),
      hfrR_below a (by have := hInvQ.h_ge; omega)]
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]
  have hfpQ := hInvQ.frame_persist; dsimp only at hfpQ; rw [hps_id] at hfpQ
  refine ⟨⟨(hmem_pres h0 (le_refl _) (by omega)).trans ((hfpQ h0 (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans hpers.xLen_at.1),
      fun idx hidx => by
        have hidx' : idx < k := by rw [Finset.length_sort, ← hX_at.1] at hidx; exact hidx
        exact (hmem_pres (h0 + 1 + idx) (by omega) (by omega)).trans
          ((hfpQ _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (hpers.xLen_at.2 idx hidx))⟩,
    fun i hi => by
      dsimp only; rw [← hX_at.1, hps_id, hmem_pres _ (by omega) (by omega)]
      have haQ := hInvQ.act_mem i hi; dsimp only at haQ; rw [hps_id] at haQ
      rw [haQ]; simp only [hi, true_and]
      cases bst.active i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      cases res i <;> rfl,
    fun i hi hnf => by
      dsimp only at hnf ⊢; rw [← hX_at.1, hps_id]
      have hsaved := hInvQ.saved_mem i hi; dsimp only at hsaved; rw [hps_id] at hsaved
      have hib : i * b + b ≤ nBlocks * b := by
        have : (i + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega); linarith
      have hBi_card : (blockSet (X.sort (· ≤ ·)) b i).card = b :=
        card_blockSet (Finset.sort_nodup X (· ≤ ·)) (by rw [← hnb_eq]; exact hi)
      cases hact : bst.active i with
      | false =>
        have h1 := hsaved.1 hact
        have hSL : ((bst.savedS i).sort (· ≤ ·)).length ≤ b := by
          rw [Finset.length_sort]; exact (Finset.card_le_card (hmod.inactive_exp i hi hact).1).trans (le_of_eq hBi_card)
        have hCL : ((blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i).sort (· ≤ ·)).length ≤ b := by
          rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)
        simp only [Bool.false_eq_true, and_false, ite_false]
        exact ⟨(hmem_pres _ (by omega) (by omega)).trans h1.1,
          (hmem_pres _ (by omega) (by omega)).trans h1.2.1,
          fun idx hidx => (hmem_pres _ (by omega) (by omega)).trans (h1.2.2.1 idx hidx),
          fun idx hidx => (hmem_pres _ (by omega) (by omega)).trans (h1.2.2.2 idx hidx)⟩
      | true =>
        cases hri : res i with
        | cut U => simp only [hi, hact, and_self, ite_true, hri] at hnf; cases hnf
        | expander S =>
          have h1 := hsaved.2 hi hact S hri
          have hSp := hInvQ.res_spec i hi hact; rw [hri] at hSp
          have hSL : (S.sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact (Finset.card_le_card hSp.1).trans (le_of_eq hBi_card)
          have hCL : ((blockSet (X.sort (· ≤ ·)) b i \ S).sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)
          simp only [hi, and_self, ite_true]
          exact ⟨(hmem_pres _ (by omega) (by omega)).trans h1.1,
            (hmem_pres _ (by omega) (by omega)).trans h1.2.1,
            fun idx hidx => (hmem_pres _ (by omega) (by omega)).trans (h1.2.2.1 idx hidx),
            fun idx hidx => (hmem_pres _ (by omega) (by omega)).trans (h1.2.2.2 idx hidx)⟩,
    fun i hi => by
      dsimp only; rw [← hX_at.1]
      by_cases hin : i ∈ cutIds
      · rcases List.mem_iff_getElem.mp hin with ⟨idx, hidx, hci_eq⟩
        have hact_i : bst.active i = true ∧ ∃ U, res i = .cut U := by
          rw [hInvQ.cutIds_eq, List.mem_filterMap] at hin
          rcases hin with ⟨j, _, hfj⟩
          split_ifs at hfj with ha_j
          cases hrj : res j with
          | expander _ => rw [hrj] at hfj; cases hfj
          | cut U => rw [hrj] at hfj; cases hfj; exact ⟨ha_j, U, hrj⟩
        rcases hact_i with ⟨hact_i, U, hri⟩
        have hidx_rp : idx < rpairs.length := by omega
        have hnew_idx := hnewM_eq idx (by rw [← hnb_eq]; exact hidx_rp)
        have hrfst : (rpairs[idx]'hidx_rp).1 = i := by
          have h := congrArg (fun l => l[idx]?) hcut_rp
          simp only [List.getElem?_eq_getElem hidx, List.getElem?_map,
            List.getElem?_eq_getElem hidx_rp] at h
          exact (Option.some.inj h).symm.trans hci_eq
        have hw := hWcut' idx hidx
        rw [hci_eq] at hw
        convert hw using 2
        simp only [hi, hact_i, and_self, ite_true, hri, witnessEdges]
        rw [witnessEdges_congr_lt (M₂ := bst.rounds i) (fun j hj => by simp [Nat.ne_of_lt hj])]
        congr 1
        have htrans : ∀ (lhs1 lhs2 : List (ℕ × ℕ)) (p1 p2 : Finset ℕ × Finset ℕ),
            lhs1 = lhs2 → p1 = p2 →
            lhs2 = matchings.getD idx [] ++ completeMatchingFake p2.1 p2.2 (matchings.getD idx []) →
            lhs1 = matchings.getD idx [] ++ completeMatchingFake p1.1 p1.2 (matchings.getD idx []) := by
          rintro _ _ _ _ rfl rfl h; exact h
        have hrp_fn_eq : ∀ (f1 f2 : ℕ → Option (ℕ × (Finset ℕ × Finset ℕ))),
            (∀ j, f1 j = f2 j) →
            List.filterMap f1 (List.range nBlocks) = List.filterMap f2 (List.range (numFullBlocks vs b)) := by
          intro f1 f2 hf; rw [← hnb_eq]; congr 1; funext j; exact hf j
        refine htrans _ _ _ _ ?_ ?_ hnew_idx
        · have hfm_eq : ∀ (L1 L2 : List (ℕ × (Finset ℕ × Finset ℕ))) (x1 x2 : ℕ), L1 = L2 → x1 = x2 →
              (match L1.findIdx? (fun ip => decide (ip.1 = x1)) with
                | none => []
                | some k' => have p := (L1.map Prod.snd).getD k' (∅, ∅); have m := matchings.getD k' []; m ++ completeMatchingFake p.1 p.2 m) =
              (match L2.findIdx? (fun ip => decide (ip.1 = x2)) with
                | none => []
                | some k' => have p := (L2.map Prod.snd).getD k' (∅, ∅); have m := matchings.getD k' []; m ++ completeMatchingFake p.1 p.2 m) := by
            rintro _ _ _ _ rfl rfl; rfl
          apply hfm_eq
          · apply hrp_fn_eq; intro j
            by_cases h1 : bst.active j = true <;> simp [h1]
          · rw [← hrfst]; congr 1
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem hidx_rp, ← List.getElem?_eq_getElem]
            congr 1; apply hrp_fn_eq; intro j
            by_cases h1 : bst.active j = true
            · simp only [h1, ↓reduceIte]; cases res j <;> rfl
            · simp [h1]
        · apply Option.some.inj
          rw [← List.getElem?_eq_getElem (hInvQ.lens_eq.2.2.2.2.symm ▸ hidx), ← List.getElem?_eq_getElem]
          congr 1; rw [hpairs_rp]; congr 1; apply hrp_fn_eq; intro j
          by_cases h1 : bst.active j = true
          · simp only [h1, ↓reduceIte]; cases res j <;> rfl
          · simp [h1]
      · have hnot_cut : bst.active i = false ∨ ∃ S, res i = .expander S := by
          cases hact_i : bst.active i with
          | false => exact Or.inl rfl
          | true =>
            cases hri : res i with
            | expander S => exact Or.inr ⟨S, rfl⟩
            | cut U =>
              exfalso; apply hin; rw [hInvQ.cutIds_eq, List.mem_filterMap]
              exact ⟨i, List.mem_range.mpr hi, by simp [hact_i, hri]⟩
        convert hWnon' i hi hin using 2
        rcases hnot_cut with hf | ⟨S, hS⟩
        · simp [hf]
        · simp only [hi, hS]; split_ifs <;> rfl,
    fun idx hidx => by
      have hidx' : idx < b := by simpa using hidx
      dsimp only; rw [← hX_at.1, hps_id,
        hfr' _ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
        hfrR_below _ (by have := hInvQ.h_ge; omega),
        hfrP_w _ (by omega) (by omega)]
      have := hpers.rangeB_at; rw [← hX_at.1, hps_id] at this; exact this idx hidx⟩


end MinCostFlow.ExpanderDecomp
