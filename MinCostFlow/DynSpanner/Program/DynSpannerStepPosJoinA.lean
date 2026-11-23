module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepHead
public import MinCostFlow.DynSpanner.Program.DynSpannerAffStage
public import MinCostFlow.DynSpanner.Program.DynSpannerSparsifyStage
public import MinCostFlow.DynSpanner.Program.DynSpannerReembStage
public import MinCostFlow.DynSpanner.Program.DynSpannerStepBridge
public import MinCostFlow.DynSpanner.Program.DynSpannerStepMid
public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedCover
public import MinCostFlow.DynSpanner.StepTransition

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stage Joins for a `0 < j` Step (Part A: Prefix Walks, `AffCtx`, `Sparsify`, and `RSCtx`)

Pure mathematical join lemmas linking the abstract model (`SnapInv`, `RevHistoryInv`,
`prefixWalk_spec`) to the Word-RAM contracts of the first four stages of a `0 < j` step:

* `prefixWalksValid_of_snapInv`: establishes `PrefixWalksValid` and the `hpi_walk` prefix edge
  membership for every edge `e ∈ G'.E` after any sequence of deletions and splits.
* `buildAffCtx`: constructs `AffCtx` from `DynSpannerStateAt` and `dsStepHeadContract.post`,
  and proves `a.affSet = affectedEdges G' H_lt piLt_mid S_prev`.
* `projGraph_sparsify_facts`: verifies `1 ≤ J.n`, `J.IsValid`, `J.m ≤ mMax`,
  `embJH.IsEmbedding J G'`, `1 ≤ embJH.length J`, `canonicalSparsify impl H_aux J embJH =
  canonicalSparsify impl G' J embJH`, and `J.IsWalk` for all `out.emb e`.
* `buildRSCtx` and O(1) space inequalities `reembStageNeed_le_from_ret` and
  `setLevelWalks_space_le_from_ret`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Prefix-walk validity from `SnapInv` -/

private lemma prefixWalk_len_gt_of_no_hit {G : MGraph} {S : Finset ℕ} :
    ∀ (P : List (ℕ × Bool)) (cur : ℕ) (k : ℕ) (hk : k < P.length),
      ¬ (cur ∈ S ∨ ∃ i < k, ∃ hi : i < P.length, G.dst (P[i]'hi) ∈ S) →
      ∃ hlt : k < (prefixWalk G cur P S).2.length, (prefixWalk G cur P S).2[k]'hlt = P[k]'hk
  | [], _, _, hk, _ => (Nat.not_lt_zero _ hk).elim
  | x :: xs, cur, k, hk, hnh => by
    have hcur : cur ∉ S := fun h => hnh (Or.inl h)
    simp only [prefixWalk, hcur, ↓reduceIte]
    cases k with
    | zero => exact ⟨Nat.zero_lt_succ _, rfl⟩
    | succ k' =>
      have hk' : k' < xs.length := Nat.lt_of_succ_lt_succ hk
      have hnh' : ¬ (G.dst x ∈ S ∨ ∃ i < k', ∃ hi : i < xs.length, G.dst (xs[i]'hi) ∈ S) := by
        rintro (h | ⟨i, hi, hil, hS⟩)
        · exact hnh (Or.inr ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, h⟩)
        · exact hnh (Or.inr ⟨i + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hil, hS⟩)
      obtain ⟨hlt, heq⟩ := prefixWalk_len_gt_of_no_hit xs (G.dst x) k' hk' hnh'
      exact ⟨Nat.succ_lt_succ hlt, by simpa using heq⟩

private lemma prefixWalk_eq_of_disjoint {G : MGraph} {S : Finset ℕ} :
    ∀ (P : List (ℕ × Bool)) (a b : ℕ),
      G.IsWalk a b P → Disjoint (G.walkVertices a P).toFinset S →
      prefixWalk G a P S = (b, P)
  | [], a, _, .nil _, hdisj => by
    have ha : a ∉ S := fun h => (Finset.disjoint_left.mp hdisj) (by simp [MGraph.walkVertices]) h
    simp [prefixWalk, ha]
  | x :: xs, a, b, .cons _ _ hrest, hdisj => by
    have ha : a ∉ S := fun h => (Finset.disjoint_left.mp hdisj) (by simp [MGraph.walkVertices]) h
    have hdisj' : Disjoint (G.walkVertices (G.dst x) xs).toFinset S := by
      rw [Finset.disjoint_left]
      intro z hz
      apply Finset.disjoint_left.mp hdisj
      simp only [List.mem_toFinset, MGraph.walkVertices, List.map_cons, List.mem_cons] at hz ⊢
      exact Or.inr hz
    simp only [prefixWalk, ha, ↓reduceIte, prefixWalk_eq_of_disjoint xs (G.dst x) b hrest hdisj']

private lemma isWalk_of_ends_sub {H G : MGraph} (hsub : H.E ⊆ G.E)
    (ht : H.tail = G.tail) (hh : H.head = G.head) :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)}, H.IsWalk a b P → G.IsWalk a b P
  | a, _, [], .nil _ => .nil a
  | _, _, x :: xs, .cons he hsrc hrest =>
    .cons (hsub he) (by cases x.2 <;> simpa [MGraph.src, ht, hh] using hsrc)
      (by
        have hd : H.dst x = G.dst x := by cases x.2 <;> simp [MGraph.dst, ht, hh]
        rw [← hd]
        exact isWalk_of_ends_sub hsub ht hh hrest)

/-- Extract the rebuild-phase snapshot `r = lastRebuild q L (j - 1) k`, `delta`, and `prefixWalk_spec`
hypotheses for a `0 < j` step at timestamp `k + 1`. -/
theorem stepPos_phase_snapshot {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hq : 1 ≤ q)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} {u : Update} (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    (hj_pos : 0 < chooseLevel L q (k + 1)) :
    let st := runState (L := L) G₀ q sparsify us k
    let j := chooseLevel L q (k + 1)
    let r := lastRebuild q L (j - 1) k
    let G_r := G₀.applyBatch (us.take r)
    let delta := (us.take (k + 1)).drop r
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
      touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid j
    let H_lt_r := unionGraphLt G_r (runState (L := L) G₀ q sparsify us r).H_level j
    let pi_r := piLt (runState (L := L) G₀ q sparsify us r) j
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    r ≤ k ∧ G_r.IsValid ∧ G_r.BatchIsValid delta ∧ (∀ u' ∈ delta, isDelOrSplit u') ∧
    G' = G_r.applyBatch delta ∧ G_r.IsSubgraph H_lt_r ∧
    Embedding.IsEmbedding pi_r G_r H_lt_r ∧
    H_lt.V = G'.V ∧ H_lt.E = H_lt_r.E ∩ G'.E ∧ H_lt.tail = G'.tail ∧ H_lt.head = G'.head ∧
    G'.IsSubgraph H_lt ∧ allTouched G_r delta ⊆ S_prev ∧
    (∀ e ∈ G'.E, piLt_mid e = pi_r e) ∧
    (∀ e ∈ G'.E, ∀ x ∈ piLt_mid e, x.1 ∈ G₀.E) := by
  intro st j r G_r delta G' H_mid inDom_mid S_prev H_lt H_lt_r pi_r piLt_mid
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hr_le : r ≤ k := lastRebuild_le q L (j - 1) k
  have hk_inv := hPref k le_rfl
  have hr_inv := hPref r hr_le
  obtain ⟨hBV_k, hds_k, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
  have hG'_eq_batch : G' = G₀.applyBatch (us.take (k + 1)) := by
    simp [G', st, hk_inv.G_eq, htake_succ, MGraph.applyBatch]
  have hsplit : us.take (k + 1) = us.take r ++ delta := by
    have h1 : (us.take (k + 1)).take r = us.take r := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    simpa [h1, delta] using (List.take_append_drop r (us.take (k + 1))).symm
  have hBV_succ : G₀.BatchIsValid (us.take (k + 1)) := by
    rw [htake_succ, batchIsValid_append]
    refine ⟨hBV_k, ?_⟩
    simpa [MGraph.BatchIsValid, ← hk_inv.G_eq] using hu_val
  have hds_succ : ∀ u' ∈ us.take (k + 1), isDelOrSplit u' := by
    intro u' hu'
    rw [htake_succ, List.mem_append, List.mem_singleton] at hu'
    rcases hu' with h | rfl
    · exact hds_k u' h
    · exact hdu
  have hBV_split := (batchIsValid_append G₀ (us.take r) delta).mp (hsplit ▸ hBV_succ)
  have hInv_r := batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_split.1
    (fun u' hu' => hds_succ u' (hsplit ▸ List.mem_append_left _ hu'))
  have hVG_r : G_r.IsValid := hInv_r.1
  have hBV_d : G_r.BatchIsValid delta := hBV_split.2
  have hds_d : ∀ u' ∈ delta, isDelOrSplit u' :=
    fun u' hu' => hds_succ u' (hsplit ▸ List.mem_append_right _ hu')
  have hG'_eq : G' = G_r.applyBatch delta := by
    rw [hG'_eq_batch, hsplit, applyBatch_append]
  have hLast : ∀ i : Fin (L + 1), i.1 < j → lastRebuild q L i.1 k = lastRebuild q L i.1 r := by
    intro i hi
    exact (lastRebuild_idempotent_le hq (lastRebuild_mono_level hq (by omega) (by omega)) hr_le).symm
  have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
    refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    intro e he
    simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at he
    rcases he with ⟨i, _, hei⟩
    exact (hr_inv.H_level_sub i).2.1 hei
  have hEmb_lt_r : Embedding.IsEmbedding pi_r G_r H_lt_r := by
    have hcl_r : chooseLevel L q r ≤ j - 1 := lastRebuild_chooseLevel_le hq (by omega)
    have hle_eq : piLe (runState (L := L) G₀ q sparsify us r) (j - 1) = pi_r := by
      simp [piLe, pi_r, show j - 1 + 1 = j by omega]
    have hU_eq : unionGraphLt G_r (runState (L := L) G₀ q sparsify us r).H_level (j - 1 + 1) =
        H_lt_r := by
      simp [H_lt_r, show j - 1 + 1 = j by omega]
    have hemb := hr_inv.emb_at ⟨j - 1, by omega⟩ hcl_r
    rwa [hle_eq, hU_eq] at hemb
  have hG'E_sub_k : G'.E ⊆ st.G.E := E_applyUpdate_subset hdu
  have hHLtE : H_lt.E = H_lt_r.E ∩ G'.E := by
    ext e
    simp only [H_lt, H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨i, hij, hei⟩
      have hei' : e ∈ (st.H_level i).E ∩ G'.E := by
        have hsub_i : (st.H_level i).E ⊆ st.G.E := by
          rw [hk_inv.G_eq]; exact (hk_inv.H_level_sub i).2.1
        rw [← applyBatch_restrict_E_inter hdu hsub_i]
        exact hei
      have hli := hk_inv.H_level_E i
      have hlr := hr_inv.H_level_E i
      rw [hLast i hij] at hli
      have hei_r : e ∈ ((runState (L := L) G₀ q sparsify us r).H_level i).E := by
        rw [hlr]
        have h1 : e ∈ ((runState (L := L) G₀ q sparsify us (lastRebuild q L i.1 r)).H_level i).E :=
          (Finset.mem_inter.mp (hli ▸ (Finset.mem_inter.mp hei').1)).1
        have h2 : e ∈ G_r.E :=
          (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_eq ▸ (Finset.mem_inter.mp hei').2)
        exact Finset.mem_inter.mpr ⟨h1, h2⟩
      exact ⟨⟨i, hij, hei_r⟩, (Finset.mem_inter.mp hei').2⟩
    · rintro ⟨⟨i, hij, hei_r⟩, heG'⟩
      refine ⟨i, hij, ?_⟩
      have hsub_i : (st.H_level i).E ⊆ st.G.E := by
        rw [hk_inv.G_eq]; exact (hk_inv.H_level_sub i).2.1
      rw [show (H_mid i).E = (st.H_level i).E ∩ G'.E from applyBatch_restrict_E_inter hdu hsub_i]
      refine Finset.mem_inter.mpr ⟨?_, heG'⟩
      have hli := hk_inv.H_level_E i
      have hlr := hr_inv.H_level_E i
      rw [hLast i hij] at hli
      rw [hli]
      refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hlr ▸ hei_r)).1, ?_⟩
      rw [← hk_inv.G_eq]; exact hG'E_sub_k heG'
  have hSub_lt : G'.IsSubgraph H_lt := by
    refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    intro e he
    rw [hHLtE] at he
    exact (Finset.mem_inter.mp he).2
  have hTouch : allTouched G_r delta ⊆ S_prev := by
    have hdelta_eq : delta = (us.take k).drop r ++ [u] := by
      dsimp only [delta]
      rw [htake_succ, List.drop_append_of_le_length (by
        have hkl : k < us.length := by
          by_contra h; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hu_some
        rw [List.length_take]; omega)]
    rw [hdelta_eq, allTouched_append]
    have h1 : allTouched G_r ((us.take k).drop r) = st.S_level ⟨j - 1, by omega⟩ :=
      (hk_inv.S_level_eq ⟨j - 1, by omega⟩).symm
    have h2 : G_r.applyBatch ((us.take k).drop r) = st.G := by
      have hs : us.take k = us.take r ++ (us.take k).drop r := by
        have : (us.take k).take r = us.take r := by
          rw [List.take_take, Nat.min_eq_left hr_le]
        simpa [this] using (List.take_append_drop r (us.take k)).symm
      rw [hk_inv.G_eq]
      conv_rhs => rw [hs, applyBatch_append]
    rw [h1, h2]
    simp [allTouched, S_prev]
  have hpi_eq : ∀ e ∈ G'.E, piLt_mid e = pi_r e := by
    intro e heG'
    have heGr : e ∈ G_r.E := (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_eq ▸ heG')
    have hdom_iff : ∀ i : Fin (L + 1), i.1 < j →
        (e ∈ inDom_mid i ↔ e ∈ (runState (L := L) G₀ q sparsify us r).inDom i) := by
      intro i hij
      have hdk : st.inDom i = (runState (L := L) G₀ q sparsify us (lastRebuild q L i.1 k)).inDom i ∩
          (G₀.applyBatch (us.take k)).E := hk_inv.inDom_eq i
      have hdr := hr_inv.inDom_eq i
      rw [hLast i hij] at hdk
      simp only [inDom_mid, hdk, hdr, Finset.mem_inter]
      constructor
      · rintro ⟨⟨h1, _⟩, _⟩; exact ⟨h1, heGr⟩
      · rintro ⟨h1, _⟩; exact ⟨⟨h1, hk_inv.G_eq ▸ hG'E_sub_k heG'⟩, heG'⟩
    have hfind : findEmbLevel inDom_mid j e =
        findEmbLevel (runState (L := L) G₀ q sparsify us r).inDom j e := by
      unfold findEmbLevel
      congr 1
      refine List.find?_congr fun i hi => ?_
      have hilt : i < min j (L + 1) := List.mem_range.mp (List.mem_reverse.mp hi)
      have hij : i < j := (Nat.lt_min.mp hilt).1
      have hiL : i < L + 1 := (Nat.lt_min.mp hilt).2
      simp only [hiL, ↓reduceDIte, decide_eq_decide]
      exact hdom_iff ⟨i, hiL⟩ hij
    dsimp only [piLt_mid, pi_r, piLt, piLtFrom]
    rw [hfind]
    split_ifs with h
    · have hlt_j : findEmbLevel (runState (L := L) G₀ q sparsify us r).inDom j e < j :=
        (findEmbLevel_lt _ hj_pos hj_le e).1
      have hpk := hk_inv.Pi_level_eq ⟨_, h⟩
      have hpr := hr_inv.Pi_level_eq ⟨_, h⟩
      rw [hLast ⟨_, h⟩ hlt_j] at hpk
      exact congrFun (hpk.trans hpr.symm) e
    · rfl
  have hpi_E0 : ∀ e ∈ G'.E, ∀ x ∈ piLt_mid e, x.1 ∈ G₀.E := by
    intro e heG' x hx
    rw [hpi_eq e heG'] at hx
    have heGr : e ∈ G_r.E := (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_eq ▸ heG')
    have hxHr : x.1 ∈ H_lt_r.E := IsWalk.mem_edge (hEmb_lt_r.2 e heGr) x hx
    exact hInv_r.2.1 (hSub_lt_r.2.1 hxHr)
  exact ⟨hr_le, hVG_r, hBV_d, hds_d, hG'_eq, hSub_lt_r, hEmb_lt_r, rfl, hHLtE, rfl, rfl,
    hSub_lt, hTouch, hpi_eq, hpi_E0⟩

/-- Under `SnapInv` at all `s ≤ k`, every edge `e ∈ G'.E` satisfies `PrefixWalksValid` and the
`hpi_walk` prefix edge membership condition needed by `AffCtx` and `RSCtx`. -/
theorem prefixWalksValid_of_snapInv {G₀ : MGraph} {L q mMax eCap : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hq : 1 ≤ q) (hE₀_cap : ∀ e ∈ G₀.E, e < eCap)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} {u : Update} (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    (hj_pos : 0 < chooseLevel L q (k + 1)) :
    let st := runState (L := L) G₀ q sparsify us k
    let j := chooseLevel L q (k + 1)
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
      touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid j
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    (∀ e ∈ G'.E,
      PrefixWalksValid G' S_prev eCap (G'.tail e) (G'.head e) (piLt_mid e) ∧
      (∀ idx (hidx : idx < (piLt_mid e).length),
        ¬ (G'.tail e ∈ S_prev ∨
          ∃ i < idx, ∃ hi : i < (piLt_mid e).length, G'.dst ((piLt_mid e)[i]'hi) ∈ S_prev) →
        ((piLt_mid e)[idx]'hidx).1 ∈ H_lt.E)) := by
  intro st j G' H_mid inDom_mid S_prev H_lt piLt_mid e heG'
  obtain ⟨_, hVG_r, hBV_d, hds_d, hG'_eq, hSub_lt_r, hEmb_lt_r, hHLtV, hHLtE, hHLt_t, hHLt_h,
    hSub_lt, hTouch, hpi_eq, hpi_E0⟩ :=
    stepPos_phase_snapshot hVG₀ hq hBV hds hu_some hPref hj_pos
  have hInvG := batch_delOrSplit_invariants _ _ hVG_r hBV_d hds_d
  rcases hInvG with ⟨hVG', hEG'_sub, _, _, _, _, hAncEnds⟩
  have hInvG := batch_delOrSplit_invariants _ _ hVG_r hBV_d hds_d
  rcases hInvG with ⟨hVG_batch, hEG'_sub, _, _, _, _, hAncEnds⟩
  have hG'_eq' : G' = (G₀.applyBatch (us.take (lastRebuild q L (j - 1) k))).applyBatch
      ((us.take (k + 1)).drop (lastRebuild q L (j - 1) k)) := hG'_eq
  have hpi_eq' : piLt_mid e = piLt (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) k)) j e :=
    hpi_eq e heG'
  have hVG' : G'.IsValid := by rw [hG'_eq']; exact hVG_batch
  have heGr : e ∈ (G₀.applyBatch (us.take (lastRebuild q L (j - 1) k))).E :=
    hEG'_sub (by rw [← hG'_eq']; exact heG')
  have hw_r := hEmb_lt_r.2 e heGr
  have hEnds_lt : ∀ f ∈ (unionGraphLt (G₀.applyBatch (us.take (lastRebuild q L (j - 1) k)))
      (runState (L := L) G₀ q sparsify us (lastRebuild q L (j - 1) k)).H_level j).E,
      H_lt.tail f = G'.tail f ∧ H_lt.head f = G'.head f :=
    fun _ _ => ⟨congrFun hHLt_t _, congrFun hHLt_h _⟩
  have hpf1 := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (by rw [← hG'_eq']; exact hSub_lt)
    (by rw [← hG'_eq']; exact hHLtV) (by rw [← hG'_eq']; exact hHLtE)
    (by intro f hf; rw [← hG'_eq']; exact hEnds_lt f hf) hTouch
    (piLt_mid e) _ _ (G'.tail e)
    (hVG_r e heGr).1 (hVG_r e heGr).2 (by rw [hpi_eq']; exact hw_r)
    (by rw [← hG'_eq']; exact (hVG' e heG').1)
    (by rw [hG'_eq']; exact (hAncEnds e heGr).1)
  have hpf2 := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (by rw [← hG'_eq']; exact hSub_lt)
    (by rw [← hG'_eq']; exact hHLtV) (by rw [← hG'_eq']; exact hHLtE)
    (by intro f hf; rw [← hG'_eq']; exact hEnds_lt f hf) hTouch
    (walkRev (piLt_mid e)) _ _ (G'.head e)
    (hVG_r e heGr).2 (hVG_r e heGr).1 (by rw [hpi_eq']; exact isWalk_walkRev hw_r)
    (by rw [← hG'_eq']; exact (hVG' e heG').2)
    (by rw [hG'_eq']; exact (hAncEnds e heGr).2)
  have hW1_Hlt : H_lt.IsWalk (G'.tail e) (prefixWalk H_lt (G'.tail e) (piLt_mid e) S_prev).1
      (prefixWalk H_lt (G'.tail e) (piLt_mid e) S_prev).2 := by
    by_cases hhit : ∃ z ∈ H_lt.walkVertices (G'.tail e) (piLt_mid e), z ∈ S_prev
    · exact (hpf1.2 hhit).2.2.1
    · have hdisj : Disjoint (H_lt.walkVertices (G'.tail e) (piLt_mid e)).toFinset S_prev := by
        rw [Finset.disjoint_left]
        intro z hz hzS
        exact hhit ⟨z, List.mem_toFinset.mp hz, hzS⟩
      have hfull := (hpf1.1 hdisj).2.1
      rw [prefixWalk_eq_of_disjoint (piLt_mid e) (G'.tail e) _ hfull hdisj]
      exact hfull
  have hW2_Hlt : H_lt.IsWalk (G'.head e) (prefixWalk H_lt (G'.head e) (walkRev (piLt_mid e)) S_prev).1
      (prefixWalk H_lt (G'.head e) (walkRev (piLt_mid e)) S_prev).2 := by
    by_cases hhit : ∃ z ∈ H_lt.walkVertices (G'.head e) (walkRev (piLt_mid e)), z ∈ S_prev
    · exact (hpf2.2 hhit).2.2.1
    · have hdisj : Disjoint (H_lt.walkVertices (G'.head e) (walkRev (piLt_mid e))).toFinset S_prev := by
        rw [Finset.disjoint_left]
        intro z hz hzS
        exact hhit ⟨z, List.mem_toFinset.mp hz, hzS⟩
      have hfull := (hpf2.1 hdisj).2.1
      rw [prefixWalk_eq_of_disjoint (walkRev (piLt_mid e)) (G'.head e) _ hfull hdisj]
      exact hfull
  have hpw1_eq : prefixWalk G' (G'.tail e) (piLt_mid e) S_prev =
      prefixWalk H_lt (G'.tail e) (piLt_mid e) S_prev :=
    prefixWalk_congr_ends hHLt_t.symm hHLt_h.symm _ _ _
  have hpw2_eq : prefixWalk G' (G'.head e) (walkRev (piLt_mid e)) S_prev =
      prefixWalk H_lt (G'.head e) (walkRev (piLt_mid e)) S_prev :=
    prefixWalk_congr_ends hHLt_t.symm hHLt_h.symm _ _ _
  refine ⟨⟨?_, ?_, fun x hx => hE₀_cap x.1 (hpi_E0 e heG' x hx)⟩, fun idx hidx hnh => ?_⟩
  · rw [hpw1_eq]; exact isWalk_of_ends_sub hSub_lt.2.1 hHLt_t hHLt_h hW1_Hlt
  · rw [hpw2_eq]; exact isWalk_of_ends_sub hSub_lt.2.1 hHLt_t hHLt_h hW2_Hlt
  · obtain ⟨hlt, heq⟩ := prefixWalk_len_gt_of_no_hit (piLt_mid e) (G'.tail e) idx hidx hnh
    have hmem : (piLt_mid e)[idx]'hidx ∈ (prefixWalk G' (G'.tail e) (piLt_mid e) S_prev).2 := by
      rw [← heq]; exact List.getElem_mem hlt
    rw [hpw1_eq] at hmem
    exact IsWalk.mem_edge hW1_Hlt _ hmem

/-! ## Building `AffCtx` after `dsStepHeadStmt` -/

lemma touchedVertices_nonempty {G : MGraph} {u : Update} (hds : isDelOrSplit u) :
    (touchedVertices G u).Nonempty := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e => exact ⟨G.tail e, by simp [touchedVertices]⟩
  | split v v' _ _ => exact ⟨v, by simp [touchedVertices]⟩

/-- Construct `AffCtx` from `DynSpannerStateAt`, `dsStepHeadContract.post`, `SnapInv`, and
`RevHistoryInv`, and show `a.affSet = affectedEdges G' H_lt piLt_mid S_prev`. -/
theorem buildAffCtx_of_stepHead {G₀ : MGraph} {w L q mMax vCap eCap b k uLen : ℕ}
    {P : SparsifyParams} {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {us : List Update} {u : Update} {mem0 mid mem2 : ℕ → ℕ} {x : DynSpannerMeta L}
    {updPtr headHeap outPref r₁ prefRet heapAff : ℕ}
    (hVG₀ : G₀.IsValid) (hL1 : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    (hE₀_cap : ∀ e ∈ G₀.E, e < eCap)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    (hRev : RevHistoryInv G₀ q sparsify us k x)
    (hj_pos : 0 < chooseLevel L q (k + 1))
    (hw16 : 16 ≤ 2 ^ w)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x (runState (L := L) G₀ q sparsify us k))
    (hGV'_cap : ∀ v ∈ ((runState (L := L) G₀ q sparsify us k).G.applyUpdate u).V, v < vCap)
    (hfoot_lt : ∀ a, heapFoot x a → a < outPref)
    (hfix_out : b + dsFixedSize L vCap eCap ≤ outPref)
    (hout_head : outPref + uLen ≤ headHeap)
    (hhead_le : headHeap + 4 * chooseLevel L q (k + 1) ≤ heapAff)
    (hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hout_w : outPref < 2 ^ w)
    (hgen_w : mem2 (b + dsGenOff) + 1 < 2 ^ w)
    (hHeadPost :
      let st := runState (L := L) G₀ q sparsify us k
      let j := chooseLevel L q (k + 1)
      (dsUpdateSLevelsContract w L vCap eCap b j st.G u uLen st.S_level x.sLists (heapFoot x)).post
        [b, j, updPtr, headHeap] mem0 r₁ mid ∧
      (dsStepPrefixContract w L vCap eCap b st.G st.H u uLen
        (fun i => if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else []) outPref).post
        [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr,
          dgEPresBase (dsHPtr b vCap eCap) vCap, outPref] mid prefRet mem2) :
    let st := runState (L := L) G₀ q sparsify us k
    let j := chooseLevel L q (k + 1)
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
      touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid j
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    ∃ (sLists' : Fin (L + 1) → List ℕ) (a : AffCtx),
      a.w = w ∧ a.L = L ∧ a.vCap = vCap ∧ a.eCap = eCap ∧ a.b = b ∧ a.j = j ∧
      a.heapPtr = heapAff ∧ a.G' = G' ∧ a.H_lt = H_lt ∧
      a.piLt_mid = piLt_mid ∧ a.S_prev = S_prev ∧
      a.sPrevList = sLists' ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∧
      a.mem0 = mem2 ∧ a.footPi = heapFoot x ∧
      a.affSet = affectedEdges G' H_lt piLt_mid S_prev ∧
      a.candSet = revCandSet L j x.revLists S_prev G' ∧
      candRevSum a.L a.j a.revLists a.sPrevList =
        candRevSum L j x.revLists (sLists' ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩) ∧
      (∀ i : Fin (L + 1),
        let S' : Finset ℕ := if i.1 < j then st.S_level i ∪ touchedVertices st.G u else ∅
        mem2 (dsSGenBase b L vCap eCap + i.1) ≤ mem2 (b + dsGenOff) ∧
        (j ≤ i.1 → mem2 (dsSGenBase b L vCap eCap + i.1) = 0) ∧
        (∀ v ∈ S', v < vCap) ∧
        (∀ v < vCap,
          mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff) ∧
          ((0 < mem2 (dsSGenBase b L vCap eCap + i.1) ∧
            mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
              mem2 (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ S')) ∧
        (sLists' i).Nodup ∧ (∀ v, v ∈ sLists' i ↔ v ∈ S') ∧
        (if 0 < mem2 (dsSGenBase b L vCap eCap + i.1)
         then LinkedListIn (fun p => heapFoot x p ∨ (headHeap ≤ p ∧ p < r₁)) mem2
                (mem2 (dsSHeadBase b L vCap eCap + i.1)) (sLists' i)
         else sLists' i = [])) := by
  intro st j G' H_mid inDom_mid S_prev H_lt piLt_mid
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  rcases hHeadPost with ⟨hUpdS, hPrefP⟩
  rcases hUpdS with ⟨_, _, hargs_s, hr1_ge, hr1_le, hgen_le1, _, hgen_pos1, ⟨sLists', hSL'⟩, hfrS⟩
  simp only [List.cons.injEq, and_true] at hargs_s
  obtain ⟨_, _, rfl, rfl⟩ := hargs_s
  rcases hPrefP with ⟨_, _, hDG', _, _, _, hfrP⟩
  rcases hState with ⟨hxV, hxE, hxiv, hb1, hGval, _, _, _, _, hGV_cap, hGE_cap,
    _, _, hmL, hmV, hmE, _, _, _, hAux0, _, _, hDom0, _, hSBitVSt0, hESt0⟩
  have hG'val : G'.IsValid := isValid_applyUpdate_of_delOrSplit hGval (hk_inv.G_eq ▸ hu_val) hdu
  have hG'E_sub : G'.E ⊆ st.G.E := E_applyUpdate_subset hdu
  have hGE'_cap : ∀ e ∈ G'.E, e < eCap := fun e he => hGE_cap e (hG'E_sub he)
  have hlay := dsFilterLayout_mk (b := b) (L := L) (vCap := vCap) (eCap := eCap) (w := w) hfix_w
  have hfa := dsFixedSize_add b L vCap eCap
  have hdom_le_s : dsDomGenBase b L vCap eCap ≤ dsSGenBase b L vCap eCap := by
    simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega
  have hs_le_sb : dsSGenBase b L vCap eCap ≤ dsSBitBase b L vCap eCap := by
    simp only [dsSBitBase, dsSHeadBase, dsVSGenBase]; omega
  have hdom_le_sb : dsDomGenBase b L vCap eCap ≤ dsSBitBase b L vCap eCap := le_trans hdom_le_s hs_le_sb
  have hsh_le_sb : dsSHeadBase b L vCap eCap + (L + 1) = dsSBitBase b L vCap eCap := rfl
  have hsb_le_es : dsSBitBase b L vCap eCap + vCap ≤ dsEStampBase b L vCap eCap := by
    simp only [dsEStampBase, dsVStampBase]; omega
  have hes_le_fix : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by
    rw [← hfa]; simp only [dsMEmbTempBase, dsKeptStampBase]; omega
  have hhdr_le_fix : dsGPtr b ≤ b + dsFixedSize L vCap eCap := by
    have := hlay.dom_ge_b; have := hlay.sb_le_fix; simp only [dsGPtr]; omega
  -- Helper: agreement between `mem2` and `mid`, and between `mid` and `mem0`.
  have hmem2_hdr : ∀ addr, addr < dsGPtr b → mem2 addr = mid addr := fun addr ha =>
    hfrP addr (Or.inl (by omega)) (Or.inl ha)
  have hmem2_ge_dom : ∀ addr, dsDomGenBase b L vCap eCap ≤ addr →
      (addr < outPref ∨ outPref + uLen ≤ addr) → mem2 addr = mid addr := fun addr h1 h2 =>
    hfrP addr h2 (Or.inr (Or.inr h1))
  have hmem2_gen : mem2 (b + dsGenOff) = mid (b + dsGenOff) :=
    hmem2_hdr _ (by simp [dsGPtr, dsHdrSize, dsGenOff])
  have hmid_mem0_hdr : ∀ addr, addr < dsGPtr b → addr ≠ b + dsGenOff → mid addr = mem0 addr := by
    intro addr ha hne
    refine hfrS addr ⟨hne, ?_, ?_, ?_, Or.inl (by omega)⟩
    · intro k' _; have := hlay.dom_ge_b; simp only [dsGPtr] at ha; omega
    · intro k' _ v _; have := hlay.dom_ge_b; simp only [dsGPtr, dsVSGenBase] at ha ⊢; omega
    · intro k' _; have := hlay.dom_ge_b; simp only [dsGPtr, dsSHeadBase, dsVSGenBase] at ha ⊢; omega
  have hmid_mem0_dom : ∀ addr, dsDomGenBase b L vCap eCap ≤ addr →
      addr < dsSGenBase b L vCap eCap → mid addr = mem0 addr := by
    intro addr h1 h2
    refine hfrS addr ⟨by have := hlay.dom_ge_b; simp only [dsGenOff, dsHdrSize] at *; omega,
      fun _ _ => by omega, fun _ _ _ _ => by simp only [dsVSGenBase]; omega,
      fun _ _ => by simp only [dsSHeadBase, dsVSGenBase]; omega,
      Or.inl (by have := hlay.sb_le_fix; omega)⟩
  have hmid_mem0_ge_sb : ∀ addr, dsSBitBase b L vCap eCap ≤ addr →
      addr < b + dsFixedSize L vCap eCap → mid addr = mem0 addr := by
    intro addr h1 h2
    refine hfrS addr ⟨by have := hlay.dom_ge_b; simp only [dsGenOff, dsHdrSize] at *; omega,
      fun k' hk' => by simp only [dsSBitBase, dsSHeadBase, dsVSGenBase] at h1; omega,
      fun k' hk' v hv => by
        have hmul : k' * vCap + v < (L + 1) * vCap := by
          calc k' * vCap + v < k' * vCap + vCap := by omega
            _ = (k' + 1) * vCap := by ring
            _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right _ (by omega)
        simp only [dsSBitBase, dsSHeadBase] at h1; omega,
      fun k' hk' => by simp only [dsSBitBase] at h1; omega,
      Or.inl (by omega)⟩
  have hmid_mem0_foot : ∀ a, heapFoot x a → mid a = mem0 a := by
    intro a ⟨iv, hiv, h1, h2⟩
    have hlo : b + dsFixedSize L vCap eCap ≤ a := le_trans (hxiv iv hiv) h1
    have hhi : a < outPref := hfoot_lt a ⟨iv, hiv, h1, h2⟩
    refine hfrS a ⟨by simp only [dsGenOff]; have := dsFixedSize_pos L vCap eCap; omega,
      fun k' hk' => by simp only [dsSBitBase, dsSHeadBase, dsVSGenBase] at hsb_le_es; omega,
      fun k' hk' v hv => by
        have hmul : k' * vCap + v < (L + 1) * vCap := by
          calc k' * vCap + v < k' * vCap + vCap := by omega
            _ = (k' + 1) * vCap := by ring
            _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right _ (by omega)
        simp only [dsSBitBase, dsSHeadBase] at hsb_le_es; omega,
      fun k' hk' => by simp only [dsSBitBase] at hsb_le_es; omega,
      Or.inl (by omega)⟩
  have hmem2_foot : ∀ a, heapFoot x a → mem2 a = mem0 a := fun a ha => by
    have hhi := hfoot_lt a ha
    have ⟨iv, hiv, h1, _⟩ := ha
    have hlo : b + dsFixedSize L vCap eCap ≤ a := le_trans (hxiv iv hiv) h1
    exact (hmem2_ge_dom a (by have := hlay.sb_le_fix; omega) (Or.inl hhi)).trans (hmid_mem0_foot a ha)
  have hmem2_sfoot : ∀ a, (heapFoot x a ∨ (headHeap ≤ a ∧ a < r₁)) → mem2 a = mid a := by
    intro a ha
    rcases ha with ha | ⟨h1, h2⟩
    · have ⟨iv, hiv, h1, _⟩ := ha
      have hlo : b + dsFixedSize L vCap eCap ≤ a := le_trans (hxiv iv hiv) h1
      exact hmem2_ge_dom a (by have := hlay.sb_le_fix; omega) (Or.inl (hfoot_lt a ha))
    · exact hmem2_ge_dom a (by have := hlay.sb_le_fix; omega) (Or.inr (by omega))
  -- Transfer `S_level` postcondition from `mid` to `mem2`.
  have hSL2 : ∀ i : Fin (L + 1),
      let S' : Finset ℕ := if i.1 < j then st.S_level i ∪ touchedVertices st.G u else ∅
      mem2 (dsSGenBase b L vCap eCap + i.1) ≤ mem2 (b + dsGenOff) ∧
      (j ≤ i.1 → mem2 (dsSGenBase b L vCap eCap + i.1) = 0) ∧
      (∀ v ∈ S', v < vCap) ∧
      (∀ v < vCap,
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff) ∧
        ((0 < mem2 (dsSGenBase b L vCap eCap + i.1) ∧
          mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
            mem2 (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ S')) ∧
      (sLists' i).Nodup ∧ (∀ v, v ∈ sLists' i ↔ v ∈ S') ∧
      (if 0 < mem2 (dsSGenBase b L vCap eCap + i.1)
       then LinkedListIn (fun p => heapFoot x p ∨ (headHeap ≤ p ∧ p < r₁)) mem2
              (mem2 (dsSHeadBase b L vCap eCap + i.1)) (sLists' i)
       else sLists' i = []) := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hSL' i
    have hsg_eq : mem2 (dsSGenBase b L vCap eCap + i.1) = mid (dsSGenBase b L vCap eCap + i.1) :=
      hmem2_ge_dom _ (by omega) (Or.inl (by
        have := i.2; simp only [dsSBitBase, dsSHeadBase, dsVSGenBase] at hsb_le_es; omega))
    have hsh_eq : mem2 (dsSHeadBase b L vCap eCap + i.1) = mid (dsSHeadBase b L vCap eCap + i.1) :=
      hmem2_ge_dom _ (by simp only [dsSHeadBase, dsVSGenBase]; omega) (Or.inl (by
        have := i.2; simp only [dsSBitBase] at hsb_le_es; omega))
    rw [hmem2_gen, hsg_eq, hsh_eq]
    refine ⟨h1, h2, h3, fun v hv => ?_, h5, h6, ?_⟩
    · have hmul : i.1 * vCap + v < (L + 1) * vCap := by
        calc i.1 * vCap + v < i.1 * vCap + vCap := by omega
          _ = (i.1 + 1) * vCap := by ring
          _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right _ (by omega)
      have hvs_eq : mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
          mid (dsVSGenBase b L vCap eCap + i.1 * vCap + v) :=
        hmem2_ge_dom _ (by simp only [dsVSGenBase]; omega) (Or.inl (by
          simp only [dsSBitBase, dsSHeadBase] at hsb_le_es; omega))
      rw [hvs_eq]; exact h4 v hv
    · split_ifs at h7 ⊢
      · exact h7.of_agree hmem2_sfoot
      · exact h7
  -- Now construct `AffCtx` on `mem2`.
  have hprev_lt : j - 1 < L + 1 := by omega
  have hprev_lt_j : (⟨j - 1, hprev_lt⟩ : Fin (L + 1)).1 < j := by dsimp; omega
  obtain ⟨hsg_le_p, _, hS_cap_p, hvs_p, hsnd_p, hsiff_p, hsll_p⟩ := hSL2 ⟨j - 1, hprev_lt⟩
  simp only [hprev_lt_j, ↓reduceIte] at hS_cap_p hvs_p hsiff_p
  have hsg_pos_p : 0 < mem2 (dsSGenBase b L vCap eCap + (j - 1)) := by
    obtain ⟨v0, hv0⟩ := touchedVertices_nonempty hdu
    have hv0S : v0 ∈ S_prev := Finset.mem_union_right _ hv0
    exact ((hvs_p v0 (hS_cap_p v0 hv0S)).2.mpr hv0S).1
  have hsll_p' : LinkedListIn (fun p => heapFoot x p ∨ (headHeap ≤ p ∧ p < r₁)) mem2
      (mem2 (dsSHeadBase b L vCap eCap + (j - 1))) (sLists' ⟨j - 1, hprev_lt⟩) := by
    simpa [hsg_pos_p] using hsll_p
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hSub_lt, _, _, _⟩ :=
    stepPos_phase_snapshot hVG₀ hq hBV hds hu_some hPref hj_pos
  have hpw_all := prefixWalksValid_of_snapInv hVG₀ hq hE₀_cap hBV hds hu_some hPref hj_pos
  have hdom_mem2 : ∀ addr, dsDomGenBase b L vCap eCap ≤ addr →
      addr < dsSGenBase b L vCap eCap → mem2 addr = mem0 addr := fun addr h1 h2 =>
    (hmem2_ge_dom addr h1 (Or.inl (by
      simp only [dsSBitBase, dsSHeadBase, dsVSGenBase] at hsb_le_es; omega))).trans
      (hmid_mem0_dom addr h1 h2)
  have hAux2 : DynGraphAt mem2 (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph := by
    refine dynGraphAt_of_agree hAux0 fun addr h1 h2 => ?_
    have haux_end : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl
    have haux_ge : dsGPtr b ≤ dsAuxPtr b vCap eCap := by
      simp only [dsAuxPtr, dsHPtr]; omega
    have haux_lt_dom : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsDomGenBase b L vCap eCap := by
      rw [haux_end]; exact dsDomGenBase_eq b L vCap eCap ▸ Nat.le_add_right _ _
    have haux_le_fix := dsFixedSize_ge_aux b L vCap eCap
    have hp := hfrP addr (Or.inl (by omega)) (Or.inr (Or.inl ⟨h1, by omega⟩))
    have hs := hfrS addr ⟨by simp only [dsGenOff, dsHdrSize, dsGPtr] at haux_ge ⊢; omega,
      fun _ _ => by omega, fun _ _ _ _ => by simp only [dsVSGenBase]; omega,
      fun _ _ => by simp only [dsSHeadBase, dsVSGenBase]; omega, Or.inl (by omega)⟩
    exact hp.trans hs
  let a : AffCtx :=
    { w := w, L := L, vCap := vCap, eCap := eCap, b := b, j := j, heapPtr := heapAff
      G' := G', H_lt := H_lt, inDom_mid := inDom_mid, Pi_level := st.Pi_level
      piLt_mid := piLt_mid, S_prev := S_prev, sPrevList := sLists' ⟨j - 1, hprev_lt⟩
      revLists := x.revLists, memInDom := x.memInDom
      footPi := heapFoot x
      footS := fun p => heapFoot x p ∨ (headHeap ≤ p ∧ p < r₁)
      footRev := heapFoot x
      mem0 := mem2
      hw16 := hw16, h1j := hj_pos, hjL := hj_le, hfix_w := hfix_w
      hfixH := by omega
      hmL := ((hmem2_hdr _ (by simp [dsGPtr, dsHdrSize, dsLOff])).trans
        (hmid_mem0_hdr _ (by simp [dsGPtr, dsHdrSize, dsLOff]) (by simp [dsLOff, dsGenOff]))).trans hmL
      hmV := ((hmem2_hdr _ (by simp [dsGPtr, dsHdrSize, dsVCapOff])).trans
        (hmid_mem0_hdr _ (by simp [dsGPtr, dsHdrSize, dsVCapOff]) (by simp [dsVCapOff, dsGenOff]))).trans hmV
      hmE := ((hmem2_hdr _ (by simp [dsGPtr, dsHdrSize, dsECapOff])).trans
        (hmid_mem0_hdr _ (by simp [dsGPtr, dsHdrSize, dsECapOff]) (by simp [dsECapOff, dsGenOff]))).trans hmE
      hgen1 := by rw [hmem2_gen]; exact hgen_pos1
      hgenB := hgen_w
      hDG := hDG', hG_val := hG'val, hGV_cap := hGV'_cap, hGE_cap := hGE'_cap
      hH_sub := hSub_lt.2.1, hH_ends := ⟨rfl, rfl⟩
      hdom := fun i _ e he => by
        have hmul := idx_lt_mul i.2 he
        rw [hdom_mem2 (dsDomGenBase b L vCap eCap + i.1) (by omega)
          (by have := i.2; simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega)]
        rw [hdom_mem2 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e)
          (by simp only [dsEdgeDomGenBase]; omega)
          (by simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase]; omega)]
        exact ((hDom0 i).2.1 e he).2
      hinDom_eq := fun i _ => by
        have h0 := (hDom0 i).2.2.2.1
        change st.inDom i ∩ G'.E = x.memInDom i ∩ G'.E
        rw [h0, Finset.inter_assoc, Finset.inter_eq_right.mpr hG'E_sub]
      hinDom0 := fun e he => by
        change e ∈ st.inDom ⟨0, Nat.zero_lt_succ L⟩ ∩ G'.E
        rw [Finset.mem_inter, hk_inv.inDom0, ← hk_inv.G_eq]
        exact ⟨hG'E_sub he, he⟩
      hpi_at := fun i _ e he => by
        have he_old : e ∈ st.inDom i := (Finset.mem_inter.mp he).1
        have heC : e < eCap := hGE'_cap e (Finset.mem_inter.mp he).2
        have hmul := idx_lt_mul i.2 heC
        have hpi_eq := hdom_mem2 (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)
          (by simp only [dsPiPtrBase, dsEdgeDomGenBase]; omega)
          (by simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase]; omega)
        obtain ⟨hmw, hrf⟩ := (hDom0 i).2.2.2.2.1 e he_old
        simp only at hmw hrf ⊢
        rw [hpi_eq]
        refine ⟨hmw.of_agree fun addr h1 h2 => hmem2_foot addr (hrf addr h1 (by rw [mWalkEncode_length]; omega)),
          hrf, ?_⟩
        set ptr := mem0 (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)
        set len := (mWalkEncode (st.Pi_level i e)).length
        have hlen_pos : 1 ≤ len := by simp only [len, mWalkEncode_length]; omega
        have hlast : ptr + len - 1 < outPref :=
          hfoot_lt (ptr + len - 1) (hrf (ptr + len - 1) (by omega) (by omega))
        change ptr + len < 2 ^ w
        omega
      hpi_walk := fun e he => (hpw_all e he).2
      hpiLt_eq := rfl
      hfootPi := fun p hp => ⟨let ⟨iv, hiv, h1, _⟩ := hp; le_trans (hxiv iv hiv) h1,
        lt_of_lt_of_le (hfoot_lt p hp) (by omega)⟩
      hfootS := fun p hp => by
        rcases hp with ⟨iv, hiv, h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_trans (hxiv iv hiv) h1, lt_of_lt_of_le (hfoot_lt p ⟨iv, hiv, h1, h2⟩) (by omega)⟩
        · exact ⟨by omega, by omega⟩
      hfootRev := fun p hp => ⟨let ⟨iv, hiv, h1, _⟩ := hp; le_trans (hxiv iv hiv) h1,
        lt_of_lt_of_le (hfoot_lt p hp) (by omega)⟩
      hS_cap := hS_cap_p, hs_nd := hsnd_p, hs_iff := hsiff_p
      hsg0 := hsg_pos_p, hsgle := hsg_le_p, hsll := hsll_p'
      hsbit0 := fun v hv => by
        have h1 := hmem2_ge_dom (dsSBitBase b L vCap eCap + v) (by omega)
          (Or.inl (by have := hlay.sb_le_fix; omega))
        have h2 := hmid_mem0_ge_sb (dsSBitBase b L vCap eCap + v) (by omega)
          (by have := hlay.sb_le_fix; omega)
        exact (h1.trans h2).trans (hSBitVSt0 v hv).1
      hestamp := fun e he => by
        have h1 := hmem2_ge_dom (dsEStampBase b L vCap eCap + e) (by omega)
          (Or.inl (by omega))
        have h2 := hmid_mem0_ge_sb (dsEStampBase b L vCap eCap + e) (by omega)
          (by omega)
        rw [h1, h2, hmem2_gen]
        exact le_trans (hESt0 e he).1 hgen_le1
      hdomle := fun i _ => by
        rw [hdom_mem2 (dsDomGenBase b L vCap eCap + i.1) (by omega)
          (by have := i.2; simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega),
          hmem2_gen]
        exact le_trans (hDom0 i).1 hgen_le1
      hrev := fun i _ v hvS => by
        have hv : v < vCap := hS_cap_p v hvS
        have hmul := idx_lt_mul i.2 hv
        have hdg := hdom_mem2 (dsDomGenBase b L vCap eCap + i.1) (by omega)
          (by have := i.2; simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega)
        have hrg := hdom_mem2 (dsRevGenBase b L vCap eCap + i.1 * vCap + v)
          (by simp only [dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega)
          (by simp only [dsSGenBase, dsRevHeadBase]; omega)
        have hrh := hdom_mem2 (dsRevHeadBase b L vCap eCap + i.1 * vCap + v)
          (by simp only [dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega)
          (by simp only [dsSGenBase]; omega)
        obtain ⟨hrg0, _, hre0, hll0⟩ := (hDom0 i).2.2.2.2.2 v hv
        rw [hdg, hrg, hrh, hmem2_gen]
        refine ⟨le_trans hrg0 hgen_le1, ?_, fun e he => (hre0 e he).1⟩
        split_ifs at hll0 ⊢
        · exact hll0.of_agree hmem2_foot
        · exact hll0
      aux0 := hAux2
      walks := fun e he => (hpw_all e he).1 }
  have haff_eq : a.affSet = affectedEdges G' H_lt piLt_mid S_prev := by
    ext e
    simp only [AffCtx.affSet, AffCtx.candSet, Finset.mem_filter, a]
    constructor
    · rintro ⟨_, heA⟩; exact heA
    · intro heA
      have heG' : e ∈ G'.E := (Finset.mem_filter.mp heA).1
      have hcov := revLists_covers_affectedEdges hVG₀ hL1 hq hGm₀ hSpec hBV hds hu_some hPref hRev
        (fun v hv => by rw [hxV]; exact hGV_cap v hv) hj_pos e heA
      obtain ⟨i, hij, _, _, v, hvS, hev⟩ := hcov
      exact ⟨⟨heG', i, v, hvS, hij, hev⟩, heA⟩
  exact ⟨sLists', a, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, haff_eq, rfl,
    rfl, hSL2⟩

/-! ## `Sparsify` and `RSCtx` joins -/

/-- Properties of `J` and `embJH` needed for `dsSparsifyStageContract.pre` when `E_aff.Nonempty`,
connecting the host graph `G'` in memory to the abstract model's `H_aux`. -/
theorem projGraph_sparsify_facts {G₀ : MGraph} {L q mMax vCap eCap : ℕ} {impl : SparsifyImpl}
    {us : List Update} {k : ℕ} {u : Update}
    (hVG₀ : G₀.IsValid) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax) (hE₀_cap : ∀ e ∈ G₀.E, e < eCap)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hj_pos : 0 < chooseLevel L q (k + 1))
    (hGV'_cap : ∀ v ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).V, v < vCap)
    (hGE'_cap : ∀ e ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).E, e < eCap) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let j := chooseLevel L q (k + 1)
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
      touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid j
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    let E_aff := affectedEdges G' H_lt piLt_mid S_prev
    let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    let H_aux := buildAuxHost G' H_lt E_aff
    let embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
    E_aff.Nonempty →
      1 ≤ J.n ∧ J.IsValid ∧ J.m ≤ mMax ∧
      (∀ v ∈ J.V, v < vCap) ∧ (∀ e ∈ J.E, e < eCap) ∧
      embJH.IsEmbedding J G' ∧ (1 ≤ embJH.length J) ∧
      canonicalSparsify impl H_aux J embJH = canonicalSparsify impl G' J embJH ∧
      (∀ e ∈ J.E, J.IsWalk (J.tail e) (J.head e) ((canonicalSparsify impl G' J embJH).emb e)) ∧
      (∀ e ∈ J.E, ∀ x ∈ embJH e, x.1 < eCap) := by
  intro st j G' H_mid inDom_mid S_prev H_lt piLt_mid E_aff J H_aux embJH hne
  obtain ⟨hr_le, hVG_r, hBV_d, hds_d, hG'_eq, hSub_lt_r, hEmb_lt_r, hHLtV, hHLtE, hHLt_t, hHLt_h,
    hSub_lt, hTouch, hpi_eq, _⟩ :=
    stepPos_phase_snapshot hVG₀ hq hBV hds hu_some hPref hj_pos
  have hInvG := batch_delOrSplit_invariants _ _ hVG_r hBV_d hds_d
  have hG'_eq' : G' = (G₀.applyBatch (us.take (lastRebuild q L (j - 1) k))).applyBatch
      ((us.take (k + 1)).drop (lastRebuild q L (j - 1) k)) := hG'_eq
  have hVG' : G'.IsValid := by rw [hG'_eq']; exact hInvG.1
  have hG'm : G'.m ≤ mMax := by
    have hsub : G'.E ⊆ G₀.E := by
      have h1 : G'.E ⊆ (G₀.applyBatch (us.take (lastRebuild q L (j - 1) k))).E := by
        rw [hG'_eq']; exact hInvG.2.1
      have h2 := (batch_delOrSplit_invariants (us.take (lastRebuild q L (j - 1) k)) G₀ hVG₀
        (batchIsValid_take us G₀ _ hBV hds).1 (batchIsValid_take us G₀ _ hBV hds).2.1).2.1
      exact Finset.Subset.trans h1 h2
    exact le_trans (Finset.card_le_card hsub) hGm₀
  have hJm : J.m ≤ mMax :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hG'm
  have hJn_pos : 1 ≤ J.n := by
    obtain ⟨e, he⟩ := hne
    have hv : (proj G' H_lt piLt_mid S_prev e).1 ∈ J.V := by
      simp only [J, buildProjGraph, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨e, he, Or.inl rfl⟩
    exact Finset.card_pos.mpr ⟨_, hv⟩
  have hJval : J.IsValid := fun e he => by
    simp only [J, buildProjGraph, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨⟨e, he, Or.inl rfl⟩, ⟨e, he, Or.inr rfl⟩⟩
  have hpw := prefixWalksValid_of_snapInv hVG₀ hq hE₀_cap hBV hds hu_some hPref hj_pos
  have hEmbJH : embJH.IsEmbedding J G' := by
    have hVsub : J.V ⊆ G'.V := by
      intro v hv
      simp only [J, buildProjGraph, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with ⟨e, heA, rfl | rfl⟩
      · have heG' := (Finset.mem_filter.mp heA).1
        have hW1 := (hpw e heG').1.1
        rw [prefixWalk_congr_ends hHLt_t.symm hHLt_h.symm] at hW1
        exact isWalk_end_mem_V hVG' (hVG' e heG').1 hW1
      · have heG' := (Finset.mem_filter.mp heA).1
        have hW2 := (hpw e heG').1.2.1
        rw [prefixWalk_congr_ends hHLt_t.symm hHLt_h.symm] at hW2
        exact isWalk_end_mem_V hVG' (hVG' e heG').2 hW2
    refine ⟨hVsub, fun e heJ => ?_⟩
    have heG' : e ∈ G'.E := (Finset.mem_filter.mp heJ).1
    have hW1 := (hpw e heG').1.1
    have hW2 := (hpw e heG').1.2.1
    rw [prefixWalk_congr_ends hHLt_t.symm hHLt_h.symm] at hW1 hW2
    have hmid : G'.IsWalk (G'.tail e) (G'.head e) [(e, true)] :=
      .cons heG' (by simp [MGraph.src]) (.nil (G'.head e))
    have h12 := MGraph.isWalk_append (isWalk_walkRev hW1) hmid
    have hfull := MGraph.isWalk_append h12 hW2
    simpa [embJH, projWalk, J, buildProjGraph, proj, List.append_assoc] using hfull
  have hLen1 : 1 ≤ embJH.length J := by
    obtain ⟨e, he⟩ := hne
    have hle : (embJH e).length ≤ embJH.length J :=
      Finset.le_sup (f := fun x => (embJH x).length) he
    have hpos : 1 ≤ (embJH e).length := by
      simp only [embJH, projWalk, List.length_append, List.length_cons, List.length_nil]
      omega
    omega
  have hcongr : canonicalSparsify impl H_aux J embJH = canonicalSparsify impl G' J embJH := by
    have hHaux_val : H_aux.IsValid := fun e he => by
      simp only [H_aux, buildAuxHost, Finset.mem_union] at he ⊢
      rcases he with he | he
      · exact hVG' e (hSub_lt.2.1 he)
      · exact hVG' e (Finset.mem_filter.mp he).1
    have hEmb_aux : embJH.IsEmbedding J H_aux := by
      refine ⟨hEmbJH.1, fun e heJ => ?_⟩
      have heG' : e ∈ G'.E := (Finset.mem_filter.mp heJ).1
      have hpi_e : piLt_mid e = piLt (runState (L := L) G₀ q (canonicalSparsify impl) us
          (lastRebuild q L (j - 1) k)) j e := hpi_eq e heG'
      have hW1_sub : ∀ x ∈ (prefixWalk H_lt (G'.tail e) (piLt_mid e) S_prev).2, x.1 ∈ H_aux.E := by
        intro x hx
        have heGr := hInvG.2.1 (by rw [← hG'_eq']; exact heG')
        have hEnds_lt : ∀ f ∈ (unionGraphLt (G₀.applyBatch (us.take (lastRebuild q L (j - 1) k)))
            (runState (L := L) G₀ q (canonicalSparsify impl) us (lastRebuild q L (j - 1) k)).H_level j).E,
            H_lt.tail f = G'.tail f ∧ H_lt.head f = G'.head f :=
          fun _ _ => ⟨congrFun hHLt_t _, congrFun hHLt_h _⟩
        have hpf1 := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (by rw [← hG'_eq']; exact hSub_lt)
          (by rw [← hG'_eq']; exact hHLtV) (by rw [← hG'_eq']; exact hHLtE)
          (by intro f hf; rw [← hG'_eq']; exact hEnds_lt f hf) hTouch
          (piLt_mid e) _ _ (G'.tail e)
          (hVG_r e heGr).1 (hVG_r e heGr).2 (by rw [hpi_e]; exact hEmb_lt_r.2 e heGr)
          (by rw [← hG'_eq']; exact (hVG' e heG').1)
          (by rw [hG'_eq']; exact (hInvG.2.2.2.2.2.2 e heGr).1)
        have hhit : ∃ z ∈ H_lt.walkVertices (G'.tail e) (piLt_mid e), z ∈ S_prev := by
          simpa [E_aff, affectedEdges, decide_eq_true_eq] using (Finset.mem_filter.mp heJ).2
        exact Finset.mem_union_left _ (IsWalk.mem_edge (hpf1.2 hhit).2.2.1 x hx)
      have hW2_sub : ∀ x ∈ (prefixWalk H_lt (G'.head e) (walkRev (piLt_mid e)) S_prev).2, x.1 ∈ H_aux.E := by
        intro x hx
        have heGr := hInvG.2.1 (by rw [← hG'_eq']; exact heG')
        have hEnds_lt : ∀ f ∈ (unionGraphLt (G₀.applyBatch (us.take (lastRebuild q L (j - 1) k)))
            (runState (L := L) G₀ q (canonicalSparsify impl) us (lastRebuild q L (j - 1) k)).H_level j).E,
            H_lt.tail f = G'.tail f ∧ H_lt.head f = G'.head f :=
          fun _ _ => ⟨congrFun hHLt_t _, congrFun hHLt_h _⟩
        have hpf2 := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (by rw [← hG'_eq']; exact hSub_lt)
          (by rw [← hG'_eq']; exact hHLtV) (by rw [← hG'_eq']; exact hHLtE)
          (by intro f hf; rw [← hG'_eq']; exact hEnds_lt f hf) hTouch
          (walkRev (piLt_mid e)) _ _ (G'.head e)
          (hVG_r e heGr).2 (hVG_r e heGr).1 (by rw [hpi_e]; exact isWalk_walkRev (hEmb_lt_r.2 e heGr))
          (by rw [← hG'_eq']; exact (hVG' e heG').2)
          (by rw [hG'_eq']; exact (hInvG.2.2.2.2.2.2 e heGr).2)
        by_cases hhit : ∃ z ∈ H_lt.walkVertices (G'.head e) (walkRev (piLt_mid e)), z ∈ S_prev
        · exact Finset.mem_union_left _ (IsWalk.mem_edge (hpf2.2 hhit).2.2.1 x hx)
        · have hdisj : Disjoint (H_lt.walkVertices (G'.head e) (walkRev (piLt_mid e))).toFinset S_prev := by
            rw [Finset.disjoint_left]; intro z hz hzS; exact hhit ⟨z, List.mem_toFinset.mp hz, hzS⟩
          have hfull := (hpf2.1 hdisj).2.1
          rw [prefixWalk_eq_of_disjoint _ _ _ hfull hdisj] at hx
          exact Finset.mem_union_left _ (IsWalk.mem_edge hfull x hx)
      have hwalk_aux : ∀ {a b : ℕ} {W : List (ℕ × Bool)},
          G'.IsWalk a b W → (∀ x ∈ W, x.1 ∈ H_aux.E) → H_aux.IsWalk a b W := by
        intro a b W hW hsubW
        induction hW with
        | nil u₀ => exact .nil u₀
        | cons _ hsrc _ ih =>
          refine .cons (hsubW _ List.mem_cons_self) hsrc
            (ih fun x hx => hsubW x (List.mem_cons_of_mem _ hx))
      refine hwalk_aux (hEmbJH.2 e heJ) fun x hx => ?_
      simp only [embJH, projWalk, List.mem_append, List.mem_singleton] at hx
      rcases hx with (hx | rfl) | hx
      · obtain ⟨y, hy, hxy⟩ := mem_walkRev_fst hx
        rw [← hxy]; exact hW1_sub y hy
      · exact Finset.mem_union_right _ heJ
      · exact hW2_sub x hx
    exact canonicalSparsify_congr_ends impl rfl rfl hHaux_val hVG' hJval (fun _ => hLen1) hEmb_aux hEmbJH
  have hJwalk := canonicalSparsify_walk_in_J impl mMax hVG' hJval hJm (fun _ => hLen1) hEmbJH
  refine ⟨hJn_pos, hJval, hJm, fun v hv => hGV'_cap v (hEmbJH.1 hv),
    fun e he => hGE'_cap e (Finset.mem_filter.mp he).1, hEmbJH, hLen1, hcongr, hJwalk,
    fun e he x hx => hGE'_cap x.1 (IsWalk.mem_edge (hEmbJH.2 e he) x hx)⟩

/-! ## O(1) Space Inequalities for `dsReembStage` and `dsSetLevelWalks` -/

private lemma compHeapNeed_eq (embJH outEmb : Embedding) (es : List ℕ) :
    compHeapNeed embJH outEmb es =
      2 * (es.map fun e => (Embedding.comp embJH outEmb e).length).sum + es.length := by
  unfold compHeapNeed compOutLen
  induction es with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, comp_eq_flatMap] at ih ⊢
    omega

private lemma reembHeapNeed_eq (embLt embMid : Embedding) (es : List ℕ) :
    reembHeapNeed embLt embMid es =
      14 * (es.map fun e => (embLt e).length).sum +
        4 * (es.map fun e => (embMid e).length).sum + 15 * es.length := by
  unfold reembHeapNeed
  induction es with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- `reembStageNeed` is bounded in `O(1)` arithmetic by the return pointer `ret_reemb` of
`dsReembStageStmt` and `lenSum = ∑_{e ∈ es} |embLt e|`. -/
theorem reembStageNeed_le_from_ret (G : MGraph) (embLt embJH outEmb : Embedding)
    (S : Finset ℕ) (es : List ℕ) (heapReemb : ℕ) :
    let ret := reembHeapAt G embLt (Embedding.comp embJH outEmb) S es
      (heapReemb + es.length + compHeapNeed embJH outEmb es) es.length
    let lenSum := (es.map fun e => (embLt e).length).sum
    heapReemb ≤ ret ∧
    ret ≤ heapReemb + 16 * es.length + 14 * lenSum + 3 * (ret - heapReemb) ∧
    heapReemb + reembStageNeed embLt embJH outEmb es ≤
      heapReemb + 16 * es.length + 14 * lenSum + 3 * (ret - heapReemb) := by
  intro ret lenSum
  have hge : heapReemb + es.length + compHeapNeed embJH outEmb es ≤ ret := by
    simp only [ret, reembHeapAt]; omega
  have hcomp_eq := compHeapNeed_eq embJH outEmb es
  have hreemb_eq := reembHeapNeed_eq embLt (Embedding.comp embJH outEmb) es
  unfold reembStageNeed
  omega

/-- The heap words written by `dsSetLevelWalksStmt` for `Pi_j` are bounded by
`2 * (ret_reemb - heapReemb)`. -/
theorem setLevelWalks_space_le_from_ret (G : MGraph) (embLt embJH outEmb : Embedding)
    (S : Finset ℕ) (es : List ℕ) (heapReemb : ℕ) :
    let embMid := Embedding.comp embJH outEmb
    let Pi_j := reembedWalk G G embLt embMid S
    let ret := reembHeapAt G embLt embMid S es
      (heapReemb + es.length + compHeapNeed embJH outEmb es) es.length
    2 * (es.map fun e => (Pi_j e).length + 1).sum ≤ 2 * (ret - heapReemb) := by
  intro embMid Pi_j ret
  have hsum_le : (es.map fun e => (Pi_j e).length + 1).sum ≤
      (es.map (reembOutLen G embLt embMid S)).sum := by
    unfold reembOutLen
    dsimp only [Pi_j]
    induction es with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      omega
  have hret_ge : (es.map (reembOutLen G embLt embMid S)).sum ≤ ret - heapReemb := by
    simp only [ret, reembHeapAt, List.take_length]; omega
  omega

end

end MinCostFlow.DynSpanner.Program

