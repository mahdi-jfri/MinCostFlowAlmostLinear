module

public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkBank
public import MinCostFlow.SparseCore.Program.AssemblyFirstNewPairs
public import MinCostFlow.SparseCore.Program.AssemblyBranchEmbLink
public import MinCostFlow.SparseCore.Program.AssemblyBranchSide
public import MinCostFlow.SparseCore.Program.AssemblyBranchFull

import MinCostFlow.DynSpanner.StepTransition

/-!
# The walk potential `Ψ` and its single-pair step lemmas (`AssemblyFirstWalkPot`)

An edge `e` that leaves `S_cur` during a branch step while staying in the graph of an active bucket
spanner `p = (C, b)` switches from its self-walk `[(e, true)]` to the table walk `piTotal (dyn' p)
e`. The spanner need not re-embed `e` in that step, so the spanner's bank does not pay for copying
that walk. To pay it, the branch holds the walk potential `Ψ` (`walkPot`):
```
walkPot tr = ∑ C ∈ tr.activeComps, ∑ b ∈ tr.activeBuckets C,
  ∑ e ∈ tr.S_cur.E ∩ (tr.dyn (C, b)).G.E, (piTotal (tr.dyn (C, b)) e).length.
```

Under `RestartScurModelInv`, `BunDisjointInv`, `CompLSFInv`, and `(tr.dyn p).G.E = (tr.bun p).edges`,
an edge of `(tr.dyn p).G` lies in `tr.S_cur` iff it lies in `(tr.dyn p).H` (`scur_inter_dynG_eq_dynH`),
so `walkPot tr` equals `slotsWalkPot P S6 slots` (`walkPot_eq_slotsWalkPot`), which depends only on
the bucket spanner table and can be placed directly in `asmBrSideRep.phi` without changing
`AsmBrSide`.

This file defines `walkPot`, `slotWalkPot`, `slotsWalkPot`, and `stepNewWalks`, proves the spanner
entering-`H` coverage (`runStepH_sdiff_sub_reemb`, `updateH_sdiff_sub_updateReembSet`), proves the
per-pair potential inequalities (`walkPot_old_pair_step`, `walkPot_old_pair_leaving`,
`walkPot_new_pair_step`), and bounds `walkPot` after a restart (`walkPot_restart_le`). The
branch-level step change and total bound against `branchStepCharge` are in
`AssemblyFirstWalkBound.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Definitions -/

@[expose] public section

/-- **The walk potential `Ψ` of a branch state**: the total length of the table walks `piTotal`
of the edges of `S_cur` that lie in the graph of an active bucket spanner. -/
noncomputable def walkPot {L : ℕ} (tr : BundleTreeState L) : ℕ :=
  tr.activeComps.sum fun C =>
    (tr.activeBuckets C).sum fun b =>
      (tr.S_cur.E ∩ (tr.dyn (C, b)).G.E).sum fun e =>
        (piTotal (tr.dyn (C, b)) e).length

/-- The walk potential of one bucket spanner slot: the total length of `piTotal` over the spanner
edges `H.E` of that slot, or `0` if the slot is empty. -/
noncomputable def slotWalkPot (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ) : ℕ :=
  if hs : s < cap then
    match S6 ⟨s, hs⟩ with
    | some d => (d.state P).H.E.sum fun e => (piTotal (d.state P) e).length
    | none => 0
  else 0

/-- The sum of `slotWalkPot` over the active slot list `slots`. Equal to `walkPot tr` whenever
`S6` represents `tr`'s active bucket spanners (`walkPot_eq_slotsWalkPot`). -/
noncomputable def slotsWalkPot (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) : ℕ :=
  (slots.map (slotWalkPot P S6)).sum

/-- Total length of all new off-spanner table walks needed by a branch step:
* for each already-active pair `p = (C, b)`, every edge in `(R_p \ S_cur'.E) ∪ ((S_cur.E \
  S_cur'.E) ∩ (dyn' p).G.E)` (re-embedded off-spanner edges and edges that left `S_cur` while
  staying in `p`'s graph);
* for each newly active pair `p = (C, b)`, every off-spanner edge in `(dyn' p).G.E \ S_cur'.E`. -/
noncomputable def stepNewWalks {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : ℕ :=
  let info := stepBundleTree sparsify tr U ord ord'
  let tr' := info.state
  (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
    let p := (C, b)
    let R := updateReembSet (tr.dyn p) (info.U_B p) (sparsify tr.m₀)
    let L_p := (tr.S_cur.E \ tr'.S_cur.E) ∩ (tr'.dyn p).G.E
    ((R \ tr'.S_cur.E) ∪ L_p).sum fun e => (piTotal (tr'.dyn p) e).length) +
  (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
    let p := (C, b)
    ((tr'.dyn p).G.E \ tr'.S_cur.E).sum fun e => (piTotal (tr'.dyn p) e).length)

end

public section

/-! ## Identifying `S_cur ∩ dyn.G` with `dyn.H`, and `walkPot` with `slotsWalkPot` -/

/-- Under `RestartScurModelInv`, `BunDisjointInv`, `CompLSFInv`, and `(tr.dyn (C, b)).G.E =
(tr.bun (C, b)).edges`, an edge of an active bucket spanner graph `(tr.dyn (C, b)).G` belongs to
`tr.S_cur` iff it belongs to `(tr.dyn (C, b)).H`. -/
theorem scur_inter_dynG_eq_dynH {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState L}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    {C : Finset ℕ} (hC : C ∈ tr.activeComps) {b : ℤ} (hb : b ∈ tr.activeBuckets C)
    (hDynG : (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges) :
    tr.S_cur.E ∩ (tr.dyn (C, b)).G.E = (tr.dyn (C, b)).H.E := by
  have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
  have hbun_q := hMod.2.2.2.2 C hC b hb
  have hSE := hMod.2.2.1
  have huniq : ∀ e, ∀ p ∈ activePairs tr, e ∈ (tr.bun p).edges → e ∈ (tr.bun (C, b)).edges →
      p = (C, b) := by
    intro e p hp hep heq
    by_contra hne
    exact Finset.disjoint_left.mp (hBD.1 p hp (C, b) hq hne) hep heq
  ext e
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨heS, heG⟩
    have heq : e ∈ (tr.bun (C, b)).edges := hDynG ▸ heG
    rw [hSE] at heS
    simp only [Finset.mem_union, Finset.mem_biUnion] at heS
    rcases heS with (⟨C', hC', b', hb', heH'⟩ | ⟨C', hC', heX⟩) | hcr
    · have hp : (C', b') ∈ activePairs tr := mem_activePairs.mpr ⟨hC', hb'⟩
      have heBun' : e ∈ (tr.bun (C', b')).edges := (hMod.2.2.2.2 C' hC' b' hb').2.2.2 heH'
      have hpeq : (C', b') = (C, b) := huniq e (C', b') hp heBun' heq
      rw [hpeq] at heH'
      exact heH'
    · exfalso
      unfold BundleTreeState.extraEdges at heX
      obtain ⟨heC', hnb⟩ := Finset.mem_sdiff.mp heX
      by_cases hCC : C' = C
      · subst hCC
        exact hnb (Finset.mem_biUnion.mpr ⟨b, hb, heq⟩)
      · exact comp_edge_disjoint hI (hMod.1 hC') (hMod.1 hC) hCC
          (Finset.mem_sdiff.mp heC').1 (hbun_q.2.1 heq)
          (Finset.disjoint_left.mp (hBD.2 (C, b) hq) heq)
    · exact absurd hcr (Finset.disjoint_left.mp (hBD.2 (C, b) hq) heq)
  · intro heH
    refine ⟨?_, ?_⟩
    · rw [hSE]
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_biUnion.mpr ⟨b, hb, heH⟩⟩))
    · rw [hDynG]
      exact hbun_q.2.2.2 heH

/-- Under `RestartScurModelInv`, `BunDisjointInv`, `CompLSFInv`, and `(tr.dyn p).G.E =
(tr.bun p).edges` on active pairs, `walkPot tr` equals the sum of `(piTotal (tr.dyn (C, b))
e).length` over `e ∈ (tr.dyn (C, b)).H.E` for all active pairs. -/
theorem walkPot_eq_H_sum {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState L}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hDynG : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges) :
    walkPot tr = tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
      (tr.dyn (C, b)).H.E.sum fun e => (piTotal (tr.dyn (C, b)) e).length := by
  unfold walkPot
  refine Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun b hb => ?_
  rw [scur_inter_dynG_eq_dynH hI hMod hBD hC hb (hDynG C hC b hb)]

/-- Under `SlotMapOK` and matching bucket spanners `S6`, `walkPot tr` equals `slotsWalkPot P S6
slots`, which depends only on the bucket spanner state and slot list (not on `S_cur`). -/
theorem walkPot_eq_slotsWalkPot {slotCap cap : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S6 : BucketSpannerState cap}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hDynG : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges)
    (hMap : SlotMapOK tr slotCap cap slots slotOf)
    (hSpan : ∀ q ∈ activePairs tr, ∃ (hs : slotOf q < cap) (d : DSHist),
      S6 ⟨slotOf q, hs⟩ = some d ∧ d.state P = tr.dyn q) :
    walkPot tr = slotsWalkPot P S6 slots := by
  rw [walkPot_eq_H_sum hI hMod hBD hDynG, slotsWalkPot, hMap.sum_map_eq]
  refine Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨hs, d, hd, hst⟩ := hSpan (C, b) (mem_activePairs.mpr ⟨hC, hb⟩)
  unfold slotWalkPot
  simp only [hs, ↓reduceDIte, hd, hst]

/-! ## Edges newly entering `H` belong to `updateReembSet` -/

/-- **Single-step entering-`H` coverage.** Every edge in `(runState (k + 1)).H.E \ (runState k).H.E`
belongs to `runStepReembSet k`. -/
theorem runStepH_sdiff_sub_reemb {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    (runState (L := L) G₀ q sparsify us (k + 1)).H.E \
        (runState (L := L) G₀ q sparsify us k).H.E ⊆
      runStepReembSet (L := L) G₀ q sparsify us k := by
  intro e he
  obtain ⟨heH', heNotH⟩ := Finset.mem_sdiff.mp he
  set u := us[k]'hk
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  obtain ⟨hInvk, -⟩ := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le
  obtain ⟨hInvk1, hRecs⟩ := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hk
  set st := runState (L := L) G₀ q sparsify us k
  set st' := runState (L := L) G₀ q sparsify us (k + 1)
  have hst' : st' = (step st u sparsify).state := by simp [st', runState, hu]; rfl
  have hch : chooseLevel L st.q (st.t + 1) = chooseLevel L q (k + 1) := by
    rw [hInvk.q_eq, hInvk.t_eq]
  rcases Nat.eq_zero_or_pos (chooseLevel L q (k + 1)) with hj0 | hjpos
  · have hR : runStepReembSet (L := L) G₀ q sparsify us k = (st.G.applyUpdate u).E := by
      simp only [runStepReembSet, hu]
      exact stepReembSet_eq_zero st u (hch.trans hj0)
    rw [hR]
    have heG' : e ∈ st'.G.E := by
      rw [hInvk1.G_eq]
      exact hInvk1.H_sub.2.1 heH'
    have hG' : st'.G = st.G.applyUpdate u := by
      rw [hst']; dsimp only [step]; rw [dite_eq_left_of_eq_true (eq_true (hch.trans hj0))]; rfl
    rwa [← hG']
  · have hjne : chooseLevel L st.q (st.t + 1) ≠ 0 := by
      rw [hch]; exact Nat.pos_iff_ne_zero.mp hjpos
    set j := chooseLevel L q (k + 1)
    have hR : runStepReembSet (L := L) G₀ q sparsify us k =
        affectedEdges (st.G.applyUpdate u)
          (unionGraphLt (st.G.applyUpdate u)
            (fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))) j)
          (piLtFrom st.Pi_level (fun i => st.inDom i ∩ (st.G.applyUpdate u).E) j)
          (st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
            touchedVertices st.G u) := by
      simp only [runStepReembSet, hu]
      have hsr := stepReembSet_eq_pos st u hjne
      simpa only [hch] using hsr
    rw [hInvk1.H_E] at heH'
    simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and] at heH'
    obtain ⟨i, -, hei⟩ := heH'
    have hHlev : st'.H_level i =
        if i.1 < j then (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
        else if i.1 = j then
          let G' := st.G.applyUpdate u
          let H_mid := fun l => (st.H_level l).applyBatch (restrictUpdate u (st.H_level l))
          let H_lt := unionGraphLt G' H_mid j
          let inDom_mid := fun l => st.inDom l ∩ G'.E
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
    rw [hHlev] at hei
    split_ifs at hei with hlt heq
    · exfalso
      apply heNotH
      obtain ⟨-, -, hU_val⟩ := batchIsValid_take us G₀ k hBV hds
      obtain ⟨hu_val, hdu⟩ := hU_val u hu
      have hsub := (isSubgraph_restrictUpdate (hInvk.H_level_sub i) (hInvk.H_level_V i)
        hu_val hdu).2.2.2.1
      rw [hsub] at hei
      rw [hInvk.H_E]
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, i.2, (Finset.mem_inter.mp hei).1⟩
    · rw [hR]
      dsimp only at hei
      set G' := st.G.applyUpdate u
      set H_mid := fun l => (st.H_level l).applyBatch (restrictUpdate u (st.H_level l))
      set H_lt := unionGraphLt G' H_mid j
      set inDom_mid := fun l => st.inDom l ∩ G'.E
      set piLt_mid := piLtFrom st.Pi_level inDom_mid j
      set S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
        touchedVertices st.G u
      set E_aff := affectedEdges G' H_lt piLt_mid S_prev
      set J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
      set H_aux := buildAuxHost G' H_lt E_aff
      set embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
      by_cases hne : E_aff.Nonempty
      · simp only [hne, ↓reduceIte] at hei
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
        exact (hSpec H_aux J embJH hAuxV hJV hJm hLen1 hEmbAux).1.2.1 hei
      · simp only [hne, ↓reduceIte] at hei
        exact hei
    · simp [emptyGraphOn] at hei

/-- **Batch entering-`H` coverage.** Every edge in `out.state.H.E \ st₀.H.E` belongs to
`updateReembSet st₀ U sparsify`. -/
theorem updateH_sdiff_sub_updateReembSet {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us U : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k₀ : ℕ} (hlen : k₀ + U.length ≤ us.length)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    (runState (L := L) G₀ q sparsify us (k₀ + U.length)).H.E \
        (runState (L := L) G₀ q sparsify us k₀).H.E ⊆
      updateReembSet (runState (L := L) G₀ q sparsify us k₀) U sparsify := by
  rw [updateReembSet_run_eq G₀ us U k₀ hmatch]
  intro e he
  obtain ⟨heH', heNotH⟩ := Finset.mem_sdiff.mp he
  have hInvEnd := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + U.length) hlen).1
  have heG' : e ∈ (runState (L := L) G₀ q sparsify us (k₀ + U.length)).G.E := by
    rw [hInvEnd.G_eq]
    exact hInvEnd.H_sub.2.1 heH'
  refine Finset.mem_inter.mpr ⟨?_, heG'⟩
  suffices h : ∀ n, k₀ + n ≤ us.length →
      e ∈ (runState (L := L) G₀ q sparsify us (k₀ + n)).H.E →
      e ∉ (runState (L := L) G₀ q sparsify us k₀).H.E →
      ∃ i < n, e ∈ runStepReembSet (L := L) G₀ q sparsify us (k₀ + i) by
    obtain ⟨i, hi, hmem⟩ := h U.length hlen heH' heNotH
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hmem⟩
  intro n
  induction n with
  | zero => intro _ h1 h2; exact absurd h1 h2
  | succ m ih =>
    intro hm h1 h2
    by_cases hmid : e ∈ (runState (L := L) G₀ q sparsify us (k₀ + m)).H.E
    · obtain ⟨i, hi, hmem⟩ := ih (by omega) hmid h2
      exact ⟨i, Nat.lt_succ_of_lt hi, hmem⟩
    · refine ⟨m, Nat.lt_succ_self m, ?_⟩
      exact runStepH_sdiff_sub_reemb hVG₀ hL hq hGm₀ hSpec hBV hds (k := k₀ + m) (by omega)
        (Finset.mem_sdiff.mpr ⟨h1, hmid⟩)

/-- `DSHist` form of `updateH_sdiff_sub_updateReembSet`. -/
theorem dsHist_H_sdiff_sub_updateReembSet (P : DSParams) (s : DSHist) (U : List Update)
    (hVG₀ : s.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : s.G₀.m ≤ P.mMax)
    (hBV : s.G₀.BatchIsValid (s.flat ++ U)) (hds : ∀ u ∈ s.flat ++ U, isDelOrSplit u) :
    ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P).H.E \ (s.state P).H.E ⊆
      updateReembSet (s.state P) U (canonicalSparsify P.impl) := by
  have hq : 1 ≤ s.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hst : s.state P = runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
      s.flat.length := by
    rw [runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U s.flat.length le_rfl]; rfl
  have hst' : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P =
      runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
        (s.flat.length + U.length) := by
    simp only [DSHist.state, dsHist_flat_append, List.length_append]; rfl
  have hmatch : ∀ (i : ℕ) (hi : i < U.length),
      (s.flat ++ U)[s.flat.length + i]? = some (U[i]'hi) := by
    intro i hi
    simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hi
  rw [hst, hst']
  exact updateH_sdiff_sub_updateReembSet hVG₀ hL hq hGm₀
    (canonicalSparsify_spec_absorb P.impl P.mMax) hBV hds (by simp) hmatch

/-- For a `DSHist` `s` and batch `U`, advancing `s` by `U` matches `DynSpanner.update`. -/
theorem dsHist_append_state_eq_update (P : DSParams) (s : DSHist) (U : List Update) :
    (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P =
      (DynSpanner.update (s.state P) U (canonicalSparsify P.impl)).state := by
  have hst : s.state P = runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
      s.flat.length := by
    rw [runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U s.flat.length le_rfl]; rfl
  have hout := updateGo_run_eq (L := P.L) (q := s.q P) (sparsify := canonicalSparsify P.impl)
    s.G₀ (s.flat ++ U) U s.flat.length [] ∅ 0 (by simp) (fun i hi => by
      simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact List.getElem?_eq_getElem hi)
  rw [hst]
  change runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.Us ++ [U]).flatten
      (s.Us ++ [U]).flatten.length = _
  have hfl : (s.Us ++ [U]).flatten = s.flat ++ U := dsHist_flat_append s U
  rw [hfl, List.length_append]
  exact congrArg StepOut.state hout.symm

/-- `DSHist` form of `piTotal_eq_of_not_mem_updateReembSet`. -/
theorem dsHist_piTotal_eq_of_not_mem_updateReembSet (P : DSParams) (s : DSHist) (U : List Update)
    (hVG₀ : s.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : s.G₀.m ≤ P.mMax)
    (hBV : s.G₀.BatchIsValid (s.flat ++ U)) (hds : ∀ u ∈ s.flat ++ U, isDelOrSplit u) :
    ∀ e ∈ ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P).G.E,
      e ∉ updateReembSet (s.state P) U (canonicalSparsify P.impl) →
      piTotal ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P) e = piTotal (s.state P) e := by
  have hq : 1 ≤ s.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hst : s.state P = runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
      s.flat.length := by
    rw [runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U s.flat.length le_rfl]; rfl
  rw [dsHist_append_state_eq_update P s U, hst]
  exact piTotal_eq_of_not_mem_updateReembSet hVG₀ hL hq hGm₀
    (canonicalSparsify_spec_absorb P.impl P.mMax) hBV hds (by simp) (fun i hi => by
      simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact List.getElem?_eq_getElem hi)

/-! ## Per-pair change of `walkPot` -/

/-- **Single already-active pair step.** The new off-spanner walks of re-embedded edges and edges
leaving `H` (staying in `G'`), plus the new potential `∑ e ∈ H', w' e`, are at most the old
potential `∑ e ∈ H, w e` plus the re-embedded walks `∑ e ∈ R, w' e`. -/
theorem walkPot_old_pair_step {H H' G' R : Finset ℕ} {w w' : ℕ → ℕ}
    (hH'_sub : H' ⊆ G') (hEnter : H' \ H ⊆ R) (hSame : ∀ e ∈ G', e ∉ R → w' e = w e) :
    (((R \ H') ∪ ((H \ H') ∩ G')).sum w') + H'.sum w' ≤ H.sum w + R.sum w' := by
  classical
  set A := (R \ H') ∪ ((H \ H') ∩ G')
  have hdisj : Disjoint A H' := by
    rw [Finset.disjoint_left]
    intro e heA heH'
    rcases Finset.mem_union.mp heA with h1 | h2
    · exact (Finset.mem_sdiff.mp h1).2 heH'
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).1).2 heH'
  rw [← Finset.sum_union hdisj]
  have hsplit := Finset.sum_filter_add_sum_filter_not (A ∪ H') (· ∈ R) w'
  have h1 : ((A ∪ H').filter (· ∈ R)).sum w' ≤ R.sum w' :=
    Finset.sum_le_sum_of_subset fun e he => (Finset.mem_filter.mp he).2
  have h2 : ((A ∪ H').filter (· ∉ R)).sum w' ≤ H.sum w := by
    calc ((A ∪ H').filter (· ∉ R)).sum w'
        = ((A ∪ H').filter (· ∉ R)).sum w := by
          refine Finset.sum_congr rfl fun e he => ?_
          obtain ⟨heU, heNotR⟩ := Finset.mem_filter.mp he
          refine hSame e ?_ heNotR
          rcases Finset.mem_union.mp heU with heA | heH'
          · rcases Finset.mem_union.mp heA with hR | hL
            · exact absurd (Finset.mem_sdiff.mp hR).1 heNotR
            · exact (Finset.mem_inter.mp hL).2
          · exact hH'_sub heH'
      _ ≤ H.sum w := by
          refine Finset.sum_le_sum_of_subset fun e he => ?_
          obtain ⟨heU, heNotR⟩ := Finset.mem_filter.mp he
          rcases Finset.mem_union.mp heU with heA | heH'
          · rcases Finset.mem_union.mp heA with hR | hL
            · exact absurd (Finset.mem_sdiff.mp hR).1 heNotR
            · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hL).1).1
          · by_contra heNotH
            exact heNotR (hEnter (Finset.mem_sdiff.mpr ⟨heH', heNotH⟩))
  rw [← hsplit, Nat.add_comm (H.sum w)]
  exact Nat.add_le_add h1 h2

/-- Corollary of `walkPot_old_pair_step` for leaving edges outside `R` alone: an edge that leaves
`H` without being re-embedded pays its walk directly from `Ψ`. -/
theorem walkPot_old_pair_leaving {H H' G' R : Finset ℕ} {w w' : ℕ → ℕ}
    (hH'_sub : H' ⊆ G') (hEnter : H' \ H ⊆ R) (hSame : ∀ e ∈ G', e ∉ R → w' e = w e) :
    (((H \ H') ∩ G') \ R).sum w' + H'.sum w' ≤ H.sum w + R.sum w' := by
  have hsub : ((H \ H') ∩ G') \ R ⊆ (R \ H') ∪ ((H \ H') ∩ G') :=
    Finset.sdiff_subset.trans Finset.subset_union_right
  have hle : (((H \ H') ∩ G') \ R).sum w' ≤ ((R \ H') ∪ ((H \ H') ∩ G')).sum w' :=
    Finset.sum_le_sum_of_subset hsub
  have hmain := walkPot_old_pair_step hH'_sub hEnter hSame
  omega

/-- **Single newly active pair step.** The off-spanner walks `G' \ H'` plus the new potential `H'`
are at most the re-embedded walks `R` plus the initial walks `G`. -/
theorem walkPot_new_pair_step {G G' H' R : Finset ℕ} {w w' : ℕ → ℕ}
    (hG'_sub : G' ⊆ G) (hH'_sub : H' ⊆ G') (hSame : ∀ e ∈ G', e ∉ R → w' e = w e) :
    (G' \ H').sum w' + H'.sum w' ≤ R.sum w' + G.sum w := by
  classical
  have hun : (G' \ H') ∪ H' = G' := Finset.sdiff_union_of_subset hH'_sub
  rw [← Finset.sum_union Finset.sdiff_disjoint, hun]
  have hsplit := Finset.sum_filter_add_sum_filter_not G' (· ∈ R) w'
  have h1 : (G'.filter (· ∈ R)).sum w' ≤ R.sum w' :=
    Finset.sum_le_sum_of_subset fun e he => (Finset.mem_filter.mp he).2
  have h2 : (G'.filter (· ∉ R)).sum w' ≤ G.sum w := by
    calc (G'.filter (· ∉ R)).sum w'
        = (G'.filter (· ∉ R)).sum w :=
          Finset.sum_congr rfl fun e he =>
            hSame e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
      _ ≤ G.sum w :=
          Finset.sum_le_sum_of_subset fun e he => hG'_sub (Finset.mem_filter.mp he).1
  rw [← hsplit]
  exact Nat.add_le_add h1 h2

/-! ## `walkPot` after a restart -/

/-- After a branch restart, `walkPot` of the restarted state is at most `singleRestartInner`
(and hence at most `singleBundleRestartMachCost`). -/
theorem walkPot_restart_le (P : DSParams) (tr : BundleTreeState P.L) (ord : ℕ → List End)
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : 1 ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound)
    (hG : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      let Hb := SparseCore.normGraph (restartBucketBundle tr ord C b).graph
      Hb.IsValid ∧ Hb.m ≤ P.mMax) :
    walkPot (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord) ≤
      singleRestartInner tr ord := by
  unfold walkPot singleRestartInner
  refine le_trans ?_ (Nat.le_add_left _ _)
  refine Finset.sum_le_sum fun C hCmem => Finset.sum_le_sum fun b hb => ?_
  set Hb := SparseCore.normGraph (restartBucketBundle tr ord C b).graph
  have hCmem' : C ∈ tr.activeComps := hCmem
  have hdyn : (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).dyn (C, b) =
      DSHist.state P ⟨Hb, []⟩ := by
    simp only [restartBundleTree, hCmem', ↓reduceIte, dsHist_state_nil, hSB]; rfl
  rw [hdyn]
  have hsub : (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).S_cur.E ∩
      (DSHist.state P ⟨Hb, []⟩).G.E ⊆ Hb.E := by
    intro e he
    have heG := (Finset.mem_inter.mp he).2
    simpa [dsHist_state_nil, DynSpanner.init, initAt] using heG
  have h1 : ((restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).S_cur.E ∩
      (DSHist.state P ⟨Hb, []⟩).G.E).sum (fun e => (piTotal (DSHist.state P ⟨Hb, []⟩) e).length) ≤
      Hb.E.sum (fun e => (piTotal (DSHist.state P ⟨Hb, []⟩) e).length) :=
    Finset.sum_le_sum_of_subset hsub
  have h2 := init_walks_le_spanInitBound P (hG C hCmem b hb).1 (hG C hCmem b hb).2
  have h3 := spanInitBound_mono (L := P.L) hP (le_of_eq hSB) Hb
  have h4 := Nat.le_mul_of_pos_left (spanInitBound tr.spanParams P.L tr.splitBound Hb) hC
  exact le_trans h1 (le_trans h2 (le_trans h3 h4))

/-- After a branch restart, `walkPot` is at most `singleBundleRestartMachCost`. -/
theorem walkPot_restart_le_machCost (P : DSParams) (tr : BundleTreeState P.L) (ord : ℕ → List End)
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : 1 ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound)
    (hG : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      let Hb := SparseCore.normGraph (restartBucketBundle tr ord C b).graph
      Hb.IsValid ∧ Hb.m ≤ P.mMax) :
    walkPot (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord) ≤
      singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  rw [singleBundleRestartMachCost_eq_inner]
  exact le_trans (walkPot_restart_le P tr ord hP hC hSB hG)
    (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _)))

/-- Under `AsmBrSideModel`, `walkPot` after a restart is at most `singleBundleRestartMachCost`.
This supplies the restart bound of `AsmWalkPotRestartOK` directly from the facts already kept in
`AsmBrSideModel`. -/
theorem walkPot_restart_le_of_sideModel
    {B5 : (kB slotCap vCap eCap : ℕ) → WordRAM.DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {a : AsmBranchAbs depth} {y : AsmBrSide B5 depth}
    (hmod : AsmBrSideModel impl w depth L capExp limbMul Ψ a y) :
    walkPot (restartBundleTree depth (fun _ => canonicalSparsify impl) a.tr a.ord) ≤
      singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) a.tr a.ord := by
  obtain ⟨hMap, hMatch, _, _, hSG, _, _, hP, hC, hSB, _, _, _, _, _, _, _, _⟩ := hmod
  set P := asmBrSP impl w depth y
  refine walkPot_restart_le_machCost P a.tr a.ord hP
    (le_trans (one_le_dsAmortConst impl) hC) hSB fun C hCmem b hb => ?_
  have hq : (C, b) ∈ activePairs a.tr := mem_activePairs.mpr ⟨hCmem, hb⟩
  have hsl : y.slotOf (C, b) ∈ y.slots := hMap.2.1 (C, b) hq
  have hok := hSG (y.slotOf (C, b)) hsl
  have hrg : restartSlotGraph y.bunS a.tr.cs a.ord a.tr.k (y.slotOf (C, b)) =
      SparseCore.normGraph (restartBucketBundle a.tr a.ord C b).graph := by
    obtain ⟨hslot, B, hB, hAg⟩ := hMatch (C, b) hq
    simp only [restartSlotGraph, restartSlotBundle, hslot, ↓reduceDIte, hB,
      restartBucketBundle, hAg.2.1]; rfl
  rw [hrg] at hok
  exact ⟨hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1⟩

/-- **`walkPot` satisfies `AsmWalkPotRestartOK`** for every sparsifier implementation `impl` and
balancing depth `depth`. -/
theorem walkPot_restartOK (impl : SparsifyImpl) (depth : ℕ) :
    AsmWalkPotRestartOK impl depth walkPot := by
  intro tr ord mMax _ _ hP hC hG
  exact walkPot_restart_le_machCost ⟨impl, mMax, 0, depth, 0, 0, tr.splitBound⟩ tr ord
    hP (le_trans (one_le_dsAmortConst impl) hC) rfl hG

end

end MinCostFlow.SparseCore.Program
