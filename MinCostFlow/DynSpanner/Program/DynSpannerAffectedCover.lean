module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepHelpers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reverse-Bucket Coverage & Candidate Count Bound (`DynSpannerAffectedCover`)

Proves:
* `revLists_covers_affectedEdges`: for every `e ∈ affectedEdges G' H_lt piLt_mid S_prev`,
  its source level `m = findEmbLevel inDom_mid j e < j` satisfies `∃ v ∈ S_prev, e ∈ x.revLists m v`.
* `revLists_cand_sum_le`: bounds `∑ i < j, ∑ v ∈ S_prev, (x.revLists i v).length ≤ 2 * eaBound`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

private lemma lastRebuild_mono_right {q L i a b : ℕ} (hle : a ≤ b) :
    lastRebuild q L i a ≤ lastRebuild q L i b := by
  unfold lastRebuild
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right hle)

private lemma lastRebuild_eq_of_forall_not_dvd {q L m a : ℕ} :
    ∀ b, a ≤ b → (∀ s, a < s → s ≤ b → ¬ phasePeriod q L m ∣ s) →
      lastRebuild q L m b = lastRebuild q L m a := by
  intro b hab hnd
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
    have hnd1 : ¬ phasePeriod q L m ∣ (a + d + 1) :=
      hnd (a + d + 1) (by omega) (by omega)
    rw [← Nat.add_assoc, lastRebuild_eq_of_not_dvd hnd1]
    exact ih (by omega) fun s h1 h2 => hnd s h1 (by omega)

private lemma take_split_drop {α : Type*} {xs : List α} {a b : ℕ} (hab : a ≤ b) :
    xs.take b = xs.take a ++ (xs.take b).drop a := by
  have h1 : (xs.take b).take a = xs.take a := by rw [List.take_take, min_eq_left hab]
  conv_lhs => rw [← List.take_append_drop a (xs.take b), h1]

private lemma drop_take_prefix {α : Type*} (xs : List α) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (xs.take b).drop a = ((xs.take c).drop a).take (b - a) := by
  rw [List.take_drop, show a + (b - a) = b from Nat.add_sub_cancel' hab,
    List.take_take, min_eq_left hbc]

private lemma applyBatch_drop_props {G₀ : MGraph} {us : List Update}
    (hVG₀ : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {a b : ℕ} (hab : a ≤ b) :
    let Ga := G₀.applyBatch (us.take a)
    let Gb := G₀.applyBatch (us.take b)
    let d := (us.take b).drop a
    Ga.IsValid ∧ Gb.IsValid ∧ Ga.BatchIsValid d ∧ (∀ u ∈ d, isDelOrSplit u) ∧
    Gb = Ga.applyBatch d ∧ Gb.E ⊆ Ga.E ∧ Ga.V ⊆ Gb.V ∧
    (∀ e ∈ Ga.E, batchAnc d (Gb.tail e) = Ga.tail e ∧ batchAnc d (Gb.head e) = Ga.head e) := by
  intro Ga Gb d
  have ht : us.take b = us.take a ++ d := take_split_drop hab
  obtain ⟨hBVa, hdsa, _⟩ := batchIsValid_take us G₀ a hBV hds
  obtain ⟨hBVb, hdsb, _⟩ := batchIsValid_take us G₀ b hBV hds
  have hBVd : Ga.BatchIsValid d := (batchIsValid_append G₀ (us.take a) d).mp (ht ▸ hBVb) |>.2
  have hdsd : ∀ u ∈ d, isDelOrSplit u := fun u hu =>
    hdsb u (ht ▸ List.mem_append_right _ hu)
  have hInvA := batch_delOrSplit_invariants (us.take a) G₀ hVG₀ hBVa hdsa
  have hInvD := batch_delOrSplit_invariants d Ga hInvA.1 hBVd hdsd
  have hGb_eq : Gb = Ga.applyBatch d := by dsimp [Gb, Ga]; rw [ht, applyBatch_append]
  exact ⟨hInvA.1, hGb_eq ▸ hInvD.1, hBVd, hdsd, hGb_eq, hGb_eq ▸ hInvD.2.1,
    hGb_eq ▸ hInvD.2.2.1, fun e he => by rw [hGb_eq]; exact hInvD.2.2.2.2.2.2 e he⟩

private lemma walkVertices_mem_pair {H : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P →
      ∀ x ∈ P, H.src x ∈ H.walkVertices u P ∧ H.dst x ∈ H.walkVertices u P
  | _, _, [], .nil _, _, hx => by simp at hx
  | _, _, y :: _, .cons _ hsrc hrest, x, hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxs
    · refine ⟨by rw [hsrc]; exact mem_walkVertices_start H _ _, ?_⟩
      simp [MGraph.walkVertices]
    · obtain ⟨h1, h2⟩ := walkVertices_mem_pair hrest x hxs
      simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at h1 h2 ⊢
      exact ⟨by tauto, by tauto⟩

private lemma walkVertices_unchanged_of_not_touched {G₁ H₁ H₂ : MGraph} {delta : List Update}
    (hG₁ : G₁.IsValid) (hBV : G₁.BatchIsValid delta) (hds : ∀ u ∈ delta, isDelOrSplit u)
    (hSub₁ : G₁.IsSubgraph H₁)
    (hEnds : ∀ e ∈ H₁.E, H₂.tail e = (G₁.applyBatch delta).tail e ∧
      H₂.head e = (G₁.applyBatch delta).head e)
    {u₀ u₁ v₀ : ℕ} {P : List (ℕ × Bool)} (hW : H₁.IsWalk u₀ v₀ P) (hu_start : u₁ = u₀)
    (hDisj : ∀ z ∈ H₁.walkVertices u₀ P, z ∉ allTouched G₁ delta) :
    H₂.walkVertices u₁ P = H₁.walkVertices u₀ P := by
  subst hu_start
  induction hW with
  | nil _ => rfl
  | @cons a b x xs hxE hsrc hrest ih =>
    have hxG : x.1 ∈ G₁.E := hSub₁.2.1 hxE
    have hmem := walkVertices_mem_pair (.cons hxE hsrc hrest) x List.mem_cons_self
    have hs_nt : H₁.src x ∉ allTouched G₁ delta := hDisj _ hmem.1
    have hd_nt : H₁.dst x ∉ allTouched G₁ delta := hDisj _ hmem.2
    have hte_eq : H₁.tail x.1 = G₁.tail x.1 := (hSub₁.2.2 x.1 hxE).1
    have hhe_eq : H₁.head x.1 = G₁.head x.1 := (hSub₁.2.2 x.1 hxE).2
    have hEnds_x := hEnds x.1 hxE
    have hinv_s := (not_mem_allTouched_invariants delta G₁ hG₁ hBV hds _ hs_nt).2.2 x.1 hxG
    have hinv_d := (not_mem_allTouched_invariants delta G₁ hG₁ hBV hds _ hd_nt).2.2 x.1 hxG
    have ht_eq : H₂.tail x.1 = H₁.tail x.1 := by
      cases xb : x.2
      · have hdef : H₁.dst x = H₁.tail x.1 := by simp [MGraph.dst, xb]
        rw [hEnds_x.1]
        exact (hinv_d.1 (hdef.trans hte_eq).symm).2.trans hdef
      · have hdef : H₁.src x = H₁.tail x.1 := by simp [MGraph.src, xb]
        rw [hEnds_x.1]
        exact (hinv_s.1 (hdef.trans hte_eq).symm).2.trans hdef
    have hh_eq : H₂.head x.1 = H₁.head x.1 := by
      cases xb : x.2
      · have hdef : H₁.src x = H₁.head x.1 := by simp [MGraph.src, xb]
        rw [hEnds_x.2]
        exact (hinv_s.2 (hdef.trans hhe_eq).symm).2.trans hdef
      · have hdef : H₁.dst x = H₁.head x.1 := by simp [MGraph.dst, xb]
        rw [hEnds_x.2]
        exact (hinv_d.2 (hdef.trans hhe_eq).symm).2.trans hdef
    have hdst_eq : H₂.dst x = H₁.dst x := by
      cases xb : x.2 <;> simp [MGraph.dst, xb, ht_eq, hh_eq]
    have hDisj' : ∀ z ∈ H₁.walkVertices (H₁.dst x) xs, z ∉ allTouched G₁ delta := fun z hz => by
      refine hDisj z ?_
      simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz ⊢
      rcases hz with rfl | hz'
      · right; left; rfl
      · right; right; exact hz'
    simp only [MGraph.walkVertices, List.map_cons]
    congr 1
    rw [hdst_eq]
    exact ih hDisj'

private lemma exists_min_touched_prefix {G₀ : MGraph} {S : Finset ℕ} :
    ∀ (xs : List Update), G₀.IsValid → G₀.BatchIsValid xs → (∀ u ∈ xs, isDelOrSplit u) →
      (∃ z ∈ S, z ∈ allTouched G₀ xs) →
      ∃ (idx : ℕ) (hidx : idx < xs.length), ∃ w₀ ∈ S,
        w₀ ∈ touchedVertices (G₀.applyBatch (xs.take idx)) (xs[idx]'hidx) ∧
        ∀ z ∈ S, z ∉ allTouched G₀ (xs.take idx)
  | [], _, _, _, ⟨_, _, hz⟩ => by simp [allTouched] at hz
  | u :: xs, hG, hBV, hds, ⟨z, hzS, hzT⟩ => by
    by_cases hhit0 : ∃ w₀ ∈ S, w₀ ∈ touchedVertices G₀ u
    · obtain ⟨w₀, hw₀S, hw₀T⟩ := hhit0
      exact ⟨0, by simp, w₀, hw₀S, hw₀T, fun _ _ => by simp [allTouched]⟩
    · simp only [allTouched, Finset.mem_union] at hzT
      have hz_tail : z ∈ allTouched (G₀.applyUpdate u) xs :=
        hzT.resolve_left fun h => hhit0 ⟨z, hzS, h⟩
      have hV1 := isValid_applyUpdate_of_delOrSplit hG hBV.1 (hds u List.mem_cons_self)
      have hds1 : ∀ x ∈ xs, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
      obtain ⟨idx, hidx, w₀, hw₀S, hw₀T, hprev⟩ :=
        exists_min_touched_prefix xs hV1 hBV.2 hds1 ⟨z, hzS, hz_tail⟩
      refine ⟨idx + 1, by simp [hidx], w₀, hw₀S, ?_, fun w hwS => ?_⟩
      · simpa [MGraph.applyBatch, List.take_succ_cons] using hw₀T
      · simp only [List.take_succ_cons, allTouched, Finset.mem_union, not_or]
        exact ⟨fun h => hhit0 ⟨w, hwS, h⟩, hprev w hwS⟩

private lemma allTouched_take_mono {G₀ : MGraph} (xs : List Update) {a : ℕ} :
    allTouched G₀ (xs.take a) ⊆ allTouched G₀ xs := by
  have ht := List.take_append_drop a xs
  conv_rhs => rw [← ht, allTouched_append]
  exact Finset.subset_union_left

private lemma touchedVertices_mem_allTouched_middle {G₀ : MGraph}
    (xs ys : List Update) (idx : ℕ) (hidx : idx < ys.length) :
    touchedVertices (G₀.applyBatch (xs ++ ys.take idx)) ys[idx] ⊆ allTouched G₀ (xs ++ ys) := by
  have hy : ys = ys.take idx ++ ys[idx] :: ys.drop (idx + 1) := by
    have htd := List.take_append_drop idx ys
    rw [← List.getElem_cons_drop hidx] at htd
    exact htd.symm
  rw [allTouched_append]
  intro v hv
  refine Finset.mem_union_right _ ?_
  rw [hy, allTouched_append]
  rw [applyBatch_append] at hv
  exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simp [hv]))

private lemma step_inDom_pos {L : ℕ} (st : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    {j : ℕ} (hj : chooseLevel L st.q (st.t + 1) = j) (hj0 : 0 < j) (hjL : j ≤ L) :
    (step st u sparsify).state.inDom ⟨j, Nat.lt_succ_of_le hjL⟩ =
      affectedEdges (st.G.applyUpdate u)
        (unionGraphLt (st.G.applyUpdate u)
          (fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))) j)
        (piLtFrom st.Pi_level (fun i => st.inDom i ∩ (st.G.applyUpdate u).E) j)
        (st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u) := by
  dsimp only [step]
  split_ifs with h0
  · exfalso; omega
  · simp only [hj, lt_irrefl, ↓reduceIte]
  · simp only [hj, lt_irrefl, ↓reduceIte]

private lemma S_prev_eq_allTouched {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {us : List Update} {s : ℕ} {u_s : Update} (_hq : 1 ≤ q)
    (hu_s : us[s]? = some u_s) (hInv_s : SnapInv G₀ L q mMax P sparsify us s)
    {c : ℕ} (hc_pos : 0 < c) (hc_le : c ≤ L) (hc_cho : chooseLevel L q (s + 1) = c) :
    let st_s := runState (L := L) G₀ q sparsify us s
    let r_c := lastRebuild q L (c - 1) (s + 1)
    r_c ≤ s ∧
    st_s.S_level ⟨c - 1, by omega⟩ ∪ touchedVertices st_s.G u_s =
      allTouched (G₀.applyBatch (us.take r_c)) ((us.take (s + 1)).drop r_c) := by
  intro st_s r_c
  have hr_nd : ¬ phasePeriod q L (c - 1) ∣ (s + 1) :=
    not_dvd_of_lt_chooseLevel (by rw [hc_cho]; omega)
  have hr_eq : r_c = lastRebuild q L (c - 1) s := lastRebuild_eq_of_not_dvd hr_nd
  have hr_le : r_c ≤ s := hr_eq ▸ lastRebuild_le q L (c - 1) s
  refine ⟨hr_le, ?_⟩
  have hdrop : (us.take (s + 1)).drop r_c = (us.take s).drop r_c ++ [u_s] := by
    rw [take_succ_of_getElem? hu_s, List.drop_append_of_le_length]
    have hs_lt : s < us.length := by
      by_contra hle; simp [List.getElem?_eq_none (Nat.le_of_not_lt hle)] at hu_s
    rw [List.length_take]; omega
  have hGapp : (G₀.applyBatch (us.take r_c)).applyBatch ((us.take s).drop r_c) =
      G₀.applyBatch (us.take s) := by
    rw [← applyBatch_append, ← take_split_drop hr_le]
  rw [hdrop, allTouched_append, hGapp, hInv_s.S_level_eq ⟨c - 1, by omega⟩, ← hr_eq, hInv_s.G_eq]
  simp [allTouched]

private lemma unionGraphLt_sub_and_ends {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {us : List Update} (hVG₀ : G₀.IsValid) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u ∈ us, isDelOrSplit u) (_hq : 1 ≤ q)
    {a b c : ℕ} (hab : a ≤ b) (hc_pos : 0 < c) (_hc_le : c ≤ L)
    (hInv_a : SnapInv G₀ L q mMax P sparsify us a)
    (hInv_b : SnapInv G₀ L q mMax P sparsify us b)
    (hLast : ∀ i : Fin (L + 1), i.1 < c → lastRebuild q L i.1 a = lastRebuild q L i.1 b) :
    let Ga := G₀.applyBatch (us.take a)
    let Gb := G₀.applyBatch (us.take b)
    let H_lt_a := unionGraphLt Ga (runState (L := L) G₀ q sparsify us a).H_level c
    let H_lt_b := unionGraphLt Gb (runState (L := L) G₀ q sparsify us b).H_level c
    Ga.IsSubgraph H_lt_a ∧
    H_lt_b.E = H_lt_a.E ∩ Gb.E ∧
    (∀ f ∈ H_lt_a.E, H_lt_b.tail f = Gb.tail f ∧ H_lt_b.head f = Gb.head f) ∧
    (∀ e ∈ Gb.E,
      piLtFrom (runState (L := L) G₀ q sparsify us b).Pi_level
        (runState (L := L) G₀ q sparsify us b).inDom c e =
      piLtFrom (runState (L := L) G₀ q sparsify us a).Pi_level
        (runState (L := L) G₀ q sparsify us a).inDom c e) := by
  intro Ga Gb H_lt_a H_lt_b
  obtain ⟨_, _, _, _, _, heGb_sub, _, _⟩ := applyBatch_drop_props hVG₀ hBV hds hab
  have hSub_a : Ga.IsSubgraph H_lt_a := by
    refine ⟨Finset.Subset.rfl, fun f hf => ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    simp only [H_lt_a, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hf
    rcases hf with ⟨i, _, hi⟩
    exact (hInv_a.H_level_sub i).2.1 hi
  have hE_eq : H_lt_b.E = H_lt_a.E ∩ Gb.E := by
    ext f
    simp only [H_lt_b, H_lt_a, unionGraphLt, unionEdgesLt, Finset.mem_inter, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hic, hfb⟩
      rw [hInv_b.H_level_E i, ← hLast i hic, Finset.mem_inter] at hfb
      refine ⟨⟨i, hic, ?_⟩, hfb.2⟩
      rw [hInv_a.H_level_E i]
      exact Finset.mem_inter.mpr ⟨hfb.1, heGb_sub hfb.2⟩
    · rintro ⟨⟨i, hic, hfa⟩, hfb⟩
      refine ⟨i, hic, ?_⟩
      rw [hInv_b.H_level_E i, ← hLast i hic]
      rw [hInv_a.H_level_E i, Finset.mem_inter] at hfa
      exact Finset.mem_inter.mpr ⟨hfa.1, hfb⟩
  have hpi : ∀ e ∈ Gb.E,
      piLtFrom (runState (L := L) G₀ q sparsify us b).Pi_level
        (runState (L := L) G₀ q sparsify us b).inDom c e =
      piLtFrom (runState (L := L) G₀ q sparsify us a).Pi_level
        (runState (L := L) G₀ q sparsify us a).inDom c e := fun e heGb => by
    have h0b : e ∈ (runState (L := L) G₀ q sparsify us b).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
      rw [hInv_b.inDom0]; exact heGb
    have h0a : e ∈ (runState (L := L) G₀ q sparsify us a).inDom ⟨0, Nat.zero_lt_succ L⟩ := by
      rw [hInv_a.inDom0]; exact heGb_sub heGb
    obtain ⟨m₁, hm₁, hm₁_dom, hm₁_none, heq₁⟩ :=
      piLtFrom_eq _ _ hc_pos h0b
    obtain ⟨m₂, hm₂, hm₂_dom, hm₂_none, heq₂⟩ :=
      piLtFrom_eq _ _ hc_pos h0a
    have hcongr : ∀ m : Fin (L + 1), m.1 < c →
        (e ∈ (runState (L := L) G₀ q sparsify us b).inDom m ↔
         e ∈ (runState (L := L) G₀ q sparsify us a).inDom m) := fun m hm => by
      rw [hInv_b.inDom_eq m, hInv_a.inDom_eq m, hLast m hm]
      have := heGb_sub heGb
      simp only [Finset.mem_inter]; tauto
    have hm_eq : m₁ = m₂ := by
      by_contra hne
      rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
      · exact hm₁_none m₂ hlt hm₂ ((hcongr m₂ hm₂).mpr hm₂_dom)
      · exact hm₂_none m₁ hlt hm₁ ((hcongr m₁ hm₁).mp hm₁_dom)
    rw [heq₁, heq₂, hm_eq, hInv_b.Pi_level_eq m₂, hInv_a.Pi_level_eq m₂, hLast m₂ hm₂]
  exact ⟨hSub_a, hE_eq, fun _ _ => ⟨rfl, rfl⟩, hpi⟩

/-- **Completeness of `revLists` coverage** (`i < j`, `v ∈ S_prev`):
under `SnapInv` (all `≤ k`) and `RevHistoryInv k x`, every edge `e ∈ affectedEdges G' H_lt piLt_mid S_prev`
at level `m = findEmbLevel inDom_mid j e < j` appears in `x.revLists ⟨m, _⟩ v` for some `v ∈ S_prev`. -/
theorem revLists_covers_affectedEdges {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (_hL : 1 ≤ L) (hq : 1 ≤ q) (_hGm₀ : G₀.m ≤ mMax)
    (_hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} {u : Update} (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    {x : DynSpannerMeta L} (hRev : RevHistoryInv G₀ q sparsify us k x)
    (hV_cap : ∀ v ∈ (runState (L := L) G₀ q sparsify us k).G.V, v < x.vCap)
    (hj_pos : 0 < chooseLevel L q (k + 1)) :
    let st := runState (L := L) G₀ q sparsify us k
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨chooseLevel L q (k + 1) - 1,
      by have := chooseLevel_le L q (k + 1); omega⟩ ∪ touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid (chooseLevel L q (k + 1))
    let piLt_mid := piLtFrom st.Pi_level inDom_mid (chooseLevel L q (k + 1))
    ∀ e ∈ affectedEdges G' H_lt piLt_mid S_prev,
      ∃ i : Fin (L + 1),
        i.1 < chooseLevel L q (k + 1) ∧
        e ∈ inDom_mid i ∧
        (∀ m' : Fin (L + 1), i.1 < m'.1 → m'.1 < chooseLevel L q (k + 1) → e ∉ inDom_mid m') ∧
        ∃ v ∈ S_prev, e ∈ x.revLists i v := by
  intro st G' H_mid inDom_mid S_prev H_lt piLt_mid e heAff
  set j := chooseLevel L q (k + 1)
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hk_lt_len : k < us.length := by
    by_contra hle; simp [List.getElem?_eq_none (Nat.le_of_not_lt hle)] at hu_some
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_valid, hdu⟩ := hU_valid u hu_some
  have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
  have hG'_eq : G' = G₀.applyBatch (us.take (k + 1)) := by
    simp [G', st, hk_inv.G_eq, htake_succ, MGraph.applyBatch]
  have hG'E_sub_k : G'.E ⊆ st.G.E := by
    change (st.G.applyUpdate u).E ⊆ st.G.E
    exact E_applyUpdate_subset hdu
  have heG' : e ∈ G'.E := (Finset.mem_filter.mp heAff).1
  have he_dom0 : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ :=
    Finset.mem_inter.mpr ⟨by rw [hk_inv.inDom0, ← hk_inv.G_eq]; exact hG'E_sub_k heG', heG'⟩
  obtain ⟨m, hmj, hm_dom, hm_none, hm_pi⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos he_dom0
  refine ⟨m, hmj, hm_dom, hm_none, ?_⟩
  obtain ⟨tm, htm_def⟩ : ∃ x, x = lastRebuild q L m.1 k := ⟨_, rfl⟩
  have htm_le_k : tm ≤ k := htm_def ▸ lastRebuild_le q L m.1 k
  have hr_info := S_prev_eq_allTouched hq hu_some hk_inv hj_pos hj_le rfl
  obtain ⟨r, hr_def⟩ : ∃ x, x = lastRebuild q L (j - 1) (k + 1) := ⟨_, rfl⟩
  have hr_le_k : r ≤ k := hr_def ▸ hr_info.1
  have hS_prev_eq : S_prev = allTouched (G₀.applyBatch (us.take r)) ((us.take (k + 1)).drop r) :=
    hr_def ▸ hr_info.2
  have hr_nd : ¬ phasePeriod q L (j - 1) ∣ (k + 1) :=
    not_dvd_of_lt_chooseLevel (Nat.sub_lt hj_pos Nat.one_pos)
  have hr_eq_k : r = lastRebuild q L (j - 1) k := hr_def.trans (lastRebuild_eq_of_not_dvd hr_nd)
  have htm_le_r : tm ≤ r := by
    rw [htm_def, hr_eq_k]
    exact lastRebuild_mono_level hq (Nat.le_pred_of_lt hmj) (le_trans (Nat.sub_le j 1) hj_le)
  have hInv_tm := hPref tm htm_le_k
  have hInv_r := hPref r hr_le_k
  obtain ⟨hVG_tm, hVG_r, hBV_tm_r, hds_tm_r, hGr_eq_tm, heGr_sub_tm, _, hAnc_tm_r⟩ :=
    applyBatch_drop_props hVG₀ hBV hds htm_le_r
  obtain ⟨_, hVG', hBV_r_d, hds_r_d, hG'_delta_r, hG'E_sub_r, _, hAnc_r_k1⟩ :=
    applyBatch_drop_props hVG₀ hBV hds (Nat.le_succ_of_le hr_le_k)
  obtain ⟨_, _, _, _, _, hG'E_sub_tm, _, _⟩ :=
    applyBatch_drop_props hVG₀ hBV hds (Nat.le_succ_of_le htm_le_k)
  rw [← hG'_eq] at hVG' hG'_delta_r hG'E_sub_r hG'E_sub_tm hAnc_r_k1
  set G_tm := G₀.applyBatch (us.take tm)
  set G_r := G₀.applyBatch (us.take r)
  set delta_tm_r := (us.take r).drop tm
  set delta_r := (us.take (k + 1)).drop r
  set st_tm := runState (L := L) G₀ q sparsify us tm
  set st_r := runState (L := L) G₀ q sparsify us r
  set w := st_tm.Pi_level m e
  have hw_mid_eq : piLt_mid e = w := by
    change piLtFrom st.Pi_level inDom_mid j e = w
    rw [hm_pi, hk_inv.Pi_level_eq m, ← htm_def]
  have htm_cho : chooseLevel L q tm ≤ m.1 := htm_def ▸ lastRebuild_chooseLevel_le hq (Nat.le_of_lt_succ m.2)
  have he_Gtm : e ∈ G_tm.E := hG'E_sub_tm heG'
  have he_Gr : e ∈ G_r.E := hG'E_sub_r heG'
  have hm_dom_tm : e ∈ st_tm.inDom m := by
    have h1 := (Finset.mem_inter.mp hm_dom).1
    rw [hk_inv.inDom_eq m, Finset.mem_inter, ← htm_def] at h1
    exact h1.1
  have hpi_tm_eq : piLe st_tm m.1 e = w := by
    have h0' : e ∈ st_tm.inDom ⟨0, Nat.zero_lt_succ L⟩ := by rw [hInv_tm.inDom0]; exact he_Gtm
    simpa [piLe, piLt, w] using (piLtFrom_eq_self_of_mem st_tm.Pi_level st_tm.inDom h0' hm_dom_tm)
  have hw_walk_tm : (unionGraphLt G_tm st_tm.H_level (m.1 + 1)).IsWalk (G_tm.tail e) (G_tm.head e) w := by
    rw [← hpi_tm_eq]; exact (hInv_tm.emb_at m htm_cho).2 e he_Gtm
  have hHtm_sub_G : G_tm.IsSubgraph st_tm.H := hInv_tm.H_sub
  have hw_walk_sttm : st_tm.H.IsWalk (G_tm.tail e) (G_tm.head e) w := by
    refine IsWalk.of_isSubgraph (G := st_tm.H) (H := unionGraphLt G_tm st_tm.H_level (m.1 + 1))
      ?_ hw_walk_tm
    refine ⟨hInv_tm.H_V ▸ Finset.Subset.rfl, fun f hf => ?_, fun f hf => ?_⟩
    · rw [hInv_tm.H_E]; exact unionEdgesLt_mono _ (Nat.succ_le_of_lt m.2) hf
    · have hfH : f ∈ st_tm.H.E := by rw [hInv_tm.H_E]; exact unionEdgesLt_mono _ (Nat.succ_le_of_lt m.2) hf
      exact ⟨(hHtm_sub_G.2.2 f hfH).1.symm, (hHtm_sub_G.2.2 f hfH).2.symm⟩
  have hrk_lt_tm : lastRebuild q L m.1 r = tm := htm_def ▸ lastRebuild_idempotent_le hq (htm_def ▸ htm_le_r) hr_le_k
  have hNoTouch_tm_r : ∀ z ∈ st_tm.H.walkVertices (G_tm.tail e) w, z ∉ allTouched G_tm delta_tm_r := by
    intro z0 hz0 hzT
    obtain ⟨idx, hidx_lt, w₀, hw₀W, hw₀T, hprev_nt⟩ :=
      exists_min_touched_prefix (S := (st_tm.H.walkVertices (G_tm.tail e) w).toFinset)
        delta_tm_r hVG_tm hBV_tm_r hds_tm_r ⟨z0, List.mem_toFinset.mpr hz0, hzT⟩
    replace hw₀W : w₀ ∈ st_tm.H.walkVertices (G_tm.tail e) w := List.mem_toFinset.mp hw₀W
    replace hprev_nt : ∀ z ∈ st_tm.H.walkVertices (G_tm.tail e) w,
        z ∉ allTouched G_tm (delta_tm_r.take idx) := fun z hz => hprev_nt z (List.mem_toFinset.mpr hz)
    set a := tm + idx
    have hr_lt_len : r ≤ us.length := le_trans hr_le_k (Nat.le_of_lt hk_lt_len)
    have ha_lt_r : a < r := by
      simp only [delta_tm_r, List.length_drop, List.length_take, min_eq_left hr_lt_len] at hidx_lt
      omega
    obtain ⟨c_star, s₂, hc_le, ha1_le_s₂, hs₂_le_r, hs₂_c, hm_lt_c, hSc_gt, hc_min⟩ :
        ∃ c_star s₂ : ℕ,
          c_star ≤ j - 1 ∧ a + 1 ≤ s₂ ∧ s₂ ≤ r ∧ chooseLevel L q s₂ = c_star ∧
          m.1 < c_star ∧ (∀ s, s₂ < s → s ≤ r → c_star < chooseLevel L q s) ∧
          (∀ s, a + 1 ≤ s → s ≤ r → c_star ≤ chooseLevel L q s) := by
      set S_rng := Finset.Icc (a + 1) r
      have hS_ne : S_rng.Nonempty := ⟨r, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
      set c_star := S_rng.inf' hS_ne (fun s => chooseLevel L q s)
      set S_c := S_rng.filter (fun s => chooseLevel L q s = c_star)
      have hSc_ne : S_c.Nonempty := by
        obtain ⟨s, hs, hseq⟩ := Finset.exists_mem_eq_inf' hS_ne (fun s => chooseLevel L q s)
        exact ⟨s, Finset.mem_filter.mpr ⟨hs, hseq.symm⟩⟩
      set s₂ := S_c.max' hSc_ne
      have hs₂_mem : s₂ ∈ S_rng := (Finset.mem_filter.mp (Finset.max'_mem S_c hSc_ne)).1
      have hs₂_c : chooseLevel L q s₂ = c_star :=
        (Finset.mem_filter.mp (Finset.max'_mem S_c hSc_ne)).2
      have ha1_le_s₂ : a + 1 ≤ s₂ := (Finset.mem_Icc.mp hs₂_mem).1
      have hs₂_le_r : s₂ ≤ r := (Finset.mem_Icc.mp hs₂_mem).2
      have hr_cho : chooseLevel L q r ≤ j - 1 :=
        hr_def ▸ lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
      have hc_le : c_star ≤ j - 1 := le_trans
        (Finset.inf'_le (f := fun s => chooseLevel L q s) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
        hr_cho
      have hm_lt_c : m.1 < c_star := by
        by_contra hle
        have hdiv_s₂ : phasePeriod q L c_star ∣ s₂ := hs₂_c ▸ chooseLevel_dvd L q s₂
        have hdiv_m : phasePeriod q L m.1 ∣ phasePeriod q L c_star := by
          unfold phasePeriod; exact pow_dvd_pow q (by omega)
        have hlast_ge : s₂ ≤ lastRebuild q L m.1 r :=
          (lastRebuild_eq_self_of_dvd (dvd_trans hdiv_m hdiv_s₂)).symm ▸ lastRebuild_mono_right hs₂_le_r
        rw [hrk_lt_tm] at hlast_ge; omega
      have hSc_gt : ∀ s, s₂ < s → s ≤ r → c_star < chooseLevel L q s := by
        intro s hs1 hs2
        have hsmem : s ∈ S_rng := Finset.mem_Icc.mpr ⟨by omega, hs2⟩
        rcases lt_or_eq_of_le (Finset.inf'_le (f := fun s => chooseLevel L q s) hsmem) with hlt | heq
        · exact hlt
        · exfalso
          have hle_max := Finset.le_max' S_c s (Finset.mem_filter.mpr ⟨hsmem, heq.symm⟩)
          omega
      exact ⟨c_star, s₂, hc_le, ha1_le_s₂, hs₂_le_r, hs₂_c, hm_lt_c, hSc_gt, fun s h1 h2 =>
        Finset.inf'_le (f := fun s => chooseLevel L q s) (Finset.mem_Icc.mpr ⟨h1, h2⟩)⟩
    have hc_le_L : c_star ≤ L := by omega
    obtain ⟨s₂', hs₂_succ⟩ : ∃ s₂', s₂ = s₂' + 1 := ⟨s₂ - 1, by omega⟩
    have hs₂'_lt_us : s₂' < us.length := by omega
    set u₂ := us[s₂']'hs₂'_lt_us
    have hu₂_some : us[s₂']? = some u₂ := List.getElem?_eq_getElem hs₂'_lt_us
    have hInv_s₂' := hPref s₂' (by omega)
    obtain ⟨s'', hs''_eq⟩ : ∃ s'', s'' = lastRebuild q L (c_star - 1) s₂ := ⟨_, rfl⟩
    have hs''_eq_s₂' : s'' = lastRebuild q L (c_star - 1) s₂' := by
      have hnd : ¬ phasePeriod q L (c_star - 1) ∣ s₂ := by
        rw [hs₂_succ]; exact not_dvd_of_lt_chooseLevel (by rw [← hs₂_succ, hs₂_c]; omega)
      rw [hs₂_succ] at hnd
      rw [hs''_eq, hs₂_succ]
      exact lastRebuild_eq_of_not_dvd hnd
    have hs''_le_a : s'' ≤ a := by
      by_contra hgt
      have h1 : c_star ≤ chooseLevel L q s'' :=
        hc_min s'' (by omega) (hs''_eq ▸ le_trans (lastRebuild_le q L (c_star - 1) s₂) hs₂_le_r)
      have h2 : chooseLevel L q s'' ≤ c_star - 1 :=
        hs''_eq ▸ lastRebuild_chooseLevel_le hq (by omega)
      omega
    have htm_le_s'' : tm ≤ s'' := by
      have h1 : lastRebuild q L m.1 s₂ ≤ s'' :=
        hs''_eq ▸ lastRebuild_mono_level hq (Nat.le_pred_of_lt hm_lt_c) (by omega)
      have h2' : lastRebuild q L m.1 r ≤ s₂ := hrk_lt_tm.symm ▸ (by omega : tm ≤ s₂)
      rw [lastRebuild_idempotent_le hq h2' hs₂_le_r, hrk_lt_tm] at h1
      exact h1
    have hInv_s'' := hPref s'' (by omega)
    set st_s₂' := runState (L := L) G₀ q sparsify us s₂'
    set st_s'' := runState (L := L) G₀ q sparsify us s''
    set G_s'' := G₀.applyBatch (us.take s'')
    set G_s₂ := st_s₂'.G.applyUpdate u₂
    have hGs₂_eq : G_s₂ = G₀.applyBatch (us.take s₂) := by
      rw [hs₂_succ, take_succ_of_getElem? hu₂_some]
      simp [G_s₂, st_s₂', hInv_s₂'.G_eq, MGraph.applyBatch]
    obtain ⟨hVG_s'', hVG_s₂, hBV_d2, hds_d2, hGs₂_eq_d2, he_sub_s''_s₂, _, hAnc_s''_s₂⟩ :=
      applyBatch_drop_props hVG₀ hBV hds (show s'' ≤ s₂ by omega)
    rw [← hGs₂_eq] at hVG_s₂ hGs₂_eq_d2 he_sub_s''_s₂ hAnc_s''_s₂
    obtain ⟨_, _, _, _, _, hGs₂'_sub_s₂, _, _⟩ :=
      applyBatch_drop_props hVG₀ hBV hds (show s₂' ≤ s₂ by omega)
    rw [← hGs₂_eq] at hGs₂'_sub_s₂
    have he_Gs₂ : e ∈ G_s₂.E := by
      obtain ⟨_, _, _, _, _, he_s₂_k1, _, _⟩ :=
        applyBatch_drop_props hVG₀ hBV hds (show s₂ ≤ k + 1 by omega)
      rw [← hGs₂_eq, ← hG'_eq] at he_s₂_k1; exact he_s₂_k1 heG'
    have he_Gs'' : e ∈ G_s''.E := he_sub_s''_s₂ he_Gs₂
    have htm_s₂' : lastRebuild q L m.1 s₂' = tm := by
      have h1 : lastRebuild q L m.1 r ≤ s₂' := by rw [hrk_lt_tm]; omega
      rw [lastRebuild_idempotent_le hq h1 (by omega), hrk_lt_tm]
    have htm_s'' : lastRebuild q L m.1 s'' = tm := by
      have h1 : lastRebuild q L m.1 r ≤ s'' := by rw [hrk_lt_tm]; exact htm_le_s''
      rw [lastRebuild_idempotent_le hq h1 (by omega), hrk_lt_tm]
    have hlast_c_eq : lastRebuild q L c_star k = s₂ := by
      have hmr_le : lastRebuild q L c_star k ≤ r := by
        rw [hr_eq_k]
        exact lastRebuild_mono_level hq hc_le (le_trans (Nat.sub_le j 1) hj_le)
      rw [(lastRebuild_idempotent_le hq hmr_le hr_le_k).symm]
      have h2 : lastRebuild q L c_star r = lastRebuild q L c_star s₂ := by
        refine lastRebuild_eq_of_forall_not_dvd r hs₂_le_r fun s hs1 hs2 hdvd => ?_
        have hlt := hSc_gt s hs1 hs2
        have hle_cho : chooseLevel L q s ≤ c_star := by
          have : s = lastRebuild q L c_star s := (lastRebuild_eq_self_of_dvd hdvd).symm
          calc chooseLevel L q s = chooseLevel L q (lastRebuild q L c_star s) := by rw [← this]
            _ ≤ c_star := lastRebuild_chooseLevel_le hq hc_le_L
        omega
      rw [h2]
      exact lastRebuild_eq_self_of_dvd (hs₂_c ▸ chooseLevel_dvd L q s₂)
    -- Step s₂ (= s₂' + 1) places e ∈ inDom c_star
    have hst_s₂_inDom :
        e ∈ (runState (L := L) G₀ q sparsify us s₂).inDom ⟨c_star, Nat.lt_succ_of_le hc_le_L⟩ := by
      set inDom_mid2 : Fin (L + 1) → Finset ℕ := fun i => st_s₂'.inDom i ∩ G_s₂.E
      set H_mid2 : Fin (L + 1) → MGraph :=
        fun i => (st_s₂'.H_level i).applyBatch (restrictUpdate u₂ (st_s₂'.H_level i))
      set H_lt2 := unionGraphLt G_s₂ H_mid2 c_star
      set S_prev2 := st_s₂'.S_level ⟨c_star - 1, by omega⟩ ∪ touchedVertices st_s₂'.G u₂
      set piLt_mid2 := piLtFrom st_s₂'.Pi_level inDom_mid2 c_star
      have hres2_eq : runState (L := L) G₀ q sparsify us s₂ = (step st_s₂' u₂ sparsify).state := by
        rw [hs₂_succ]; dsimp [runState]; rw [hu₂_some]
      have hj_s₂' : chooseLevel L st_s₂'.q (st_s₂'.t + 1) = c_star := by
        rw [hInv_s₂'.q_eq, hInv_s₂'.t_eq, ← hs₂_succ, hs₂_c]
      have hin2 : (runState (L := L) G₀ q sparsify us s₂).inDom ⟨c_star, Nat.lt_succ_of_le hc_le_L⟩ =
          affectedEdges G_s₂ H_lt2 piLt_mid2 S_prev2 := by
        rw [hres2_eq]
        exact step_inDom_pos st_s₂' u₂ sparsify hj_s₂' (by omega) hc_le_L
      rw [hin2]
      refine Finset.mem_filter.mpr ⟨he_Gs₂, decide_eq_true ?_⟩
      have hm'_s''_s₂' : ∀ m' : Fin (L + 1), m'.1 < c_star →
          lastRebuild q L m'.1 s'' = lastRebuild q L m'.1 s₂' := fun m' hm' => by
        have h1 : lastRebuild q L m'.1 s₂' ≤ s'' := by
          rw [hs''_eq_s₂']
          exact lastRebuild_mono_level hq (Nat.le_pred_of_lt hm') (by omega)
        exact lastRebuild_idempotent_le hq h1 (by omega)
      have hm2_dom_m : e ∈ inDom_mid2 m := by
        refine Finset.mem_inter.mpr ⟨?_, he_Gs₂⟩
        rw [hInv_s₂'.inDom_eq m, htm_s₂']
        exact Finset.mem_inter.mpr ⟨hm_dom_tm, hGs₂'_sub_s₂ he_Gs₂⟩
      have hnot_above : ∀ q' : Fin (L + 1), m.1 < q'.1 → q'.1 < c_star → e ∉ inDom_mid2 q' := by
        intro q' hmq hqc hdom_q'
        have hq'_last_r : lastRebuild q L q'.1 r = lastRebuild q L q'.1 s₂' := by
          have h1 : lastRebuild q L q'.1 r = lastRebuild q L q'.1 s₂ := by
            refine lastRebuild_eq_of_forall_not_dvd r hs₂_le_r fun s hs1 hs2 hdvd => ?_
            have hgt := hSc_gt s hs1 hs2
            have hcho_s : chooseLevel L q s ≤ q'.1 := by
              have := lastRebuild_eq_self_of_dvd hdvd
              calc chooseLevel L q s = chooseLevel L q (lastRebuild q L q'.1 s) := by rw [this]
                _ ≤ q'.1 := lastRebuild_chooseLevel_le hq (Nat.le_of_lt_succ q'.2)
            omega
          have hnd2 : ¬ phasePeriod q L q'.1 ∣ s₂ := by
            intro hdvd
            have hcho2 : chooseLevel L q s₂ ≤ q'.1 := by
              have := lastRebuild_eq_self_of_dvd hdvd
              calc chooseLevel L q s₂ = chooseLevel L q (lastRebuild q L q'.1 s₂) := by rw [this]
                _ ≤ q'.1 := lastRebuild_chooseLevel_le hq (Nat.le_of_lt_succ q'.2)
            omega
          rw [hs₂_succ] at hnd2
          rw [h1, hs₂_succ]
          exact lastRebuild_eq_of_not_dvd hnd2
        have hq'_last_k : lastRebuild q L q'.1 k = lastRebuild q L q'.1 r := by
          have hmr_le : lastRebuild q L q'.1 k ≤ r := by
            rw [hr_eq_k]
            exact lastRebuild_mono_level hq (by omega : q'.1 ≤ j - 1) (le_trans (Nat.sub_le j 1) hj_le)
          exact (lastRebuild_idempotent_le hq hmr_le hr_le_k).symm
        have he_in_q' : e ∈ inDom_mid q' := by
          refine Finset.mem_inter.mpr ⟨?_, heG'⟩
          rw [hk_inv.inDom_eq q', hq'_last_k, hq'_last_r]
          have h1 := (Finset.mem_inter.mp hdom_q').1
          rw [hInv_s₂'.inDom_eq q', Finset.mem_inter] at h1
          exact Finset.mem_inter.mpr ⟨h1.1, hk_inv.G_eq ▸ hG'E_sub_k heG'⟩
        exact hm_none q' hmq (lt_of_lt_of_le hqc (by omega)) he_in_q'
      have hpi2_w : piLt_mid2 e = w := by
        change piLtFrom st_s₂'.Pi_level inDom_mid2 c_star e = w
        have h0_2 : e ∈ inDom_mid2 ⟨0, Nat.zero_lt_succ L⟩ :=
          Finset.mem_inter.mpr ⟨by rw [hInv_s₂'.inDom0]; exact hGs₂'_sub_s₂ he_Gs₂, he_Gs₂⟩
        obtain ⟨m₂, hm₂_lt, hm₂_dom, hm₂_none, heq₂⟩ :=
          piLtFrom_eq st_s₂'.Pi_level inDom_mid2 (by omega : 0 < c_star) h0_2
        have hm₂_eq : m₂ = m := by
          by_contra hne
          rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
          · exact hm₂_none m hlt hm_lt_c hm2_dom_m
          · exact hnot_above m₂ hlt hm₂_lt hm₂_dom
        rw [heq₂, hm₂_eq, hInv_s₂'.Pi_level_eq m, htm_s₂']
      rw [hpi2_w]
      have hS_prev2_eq : S_prev2 = allTouched G_s'' ((us.take s₂).drop s'') := by
        have h1 := (S_prev_eq_allTouched hq hu₂_some hInv_s₂' (by omega : 0 < c_star) hc_le_L
          (by rw [← hs₂_succ, hs₂_c])).2
        have htake2 : us.take (s₂' + 1) = us.take s₂ := by rw [← hs₂_succ]
        have hrc2 : lastRebuild q L (c_star - 1) (s₂' + 1) = s'' := by rw [← hs₂_succ, ← hs''_eq]
        simpa only [htake2, hrc2] using h1
      have hw_s'' : piLe st_s'' (c_star - 1) e = w := by
        change piLtFrom st_s''.Pi_level st_s''.inDom ((c_star - 1) + 1) e = w
        rw [show (c_star - 1) + 1 = c_star from Nat.sub_add_cancel (by omega)]
        have h0_s'' : e ∈ st_s''.inDom ⟨0, Nat.zero_lt_succ L⟩ := by
          rw [hInv_s''.inDom0]; exact he_Gs''
        have hcongr_in : ∀ q' : Fin (L + 1), q'.1 < c_star →
            (e ∈ st_s''.inDom q' ↔ e ∈ inDom_mid2 q') := fun q' hq' => by
          simp only [inDom_mid2, Finset.mem_inter]
          rw [hInv_s''.inDom_eq q', hm'_s''_s₂' q' hq', hInv_s₂'.inDom_eq q',
            Finset.mem_inter, Finset.mem_inter]
          have := he_Gs₂; have := hGs₂'_sub_s₂ he_Gs₂; tauto
        obtain ⟨m₃, hm₃_lt, hm₃_dom, hm₃_none, heq₃⟩ :=
          piLtFrom_eq st_s''.Pi_level st_s''.inDom (by omega : 0 < c_star) h0_s''
        have hm₃_eq : m₃ = m := by
          by_contra hne
          rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
          · exact hm₃_none m hlt hm_lt_c ((hcongr_in m hm_lt_c).mpr hm2_dom_m)
          · exact hnot_above m₃ hlt hm₃_lt ((hcongr_in m₃ hm₃_lt).mp hm₃_dom)
        rw [heq₃, hm₃_eq, hInv_s''.Pi_level_eq m, htm_s'']
      set H_lt_s'' := unionGraphLt G_s'' st_s''.H_level c_star
      have hSub_lt_s'' : G_s''.IsSubgraph H_lt_s'' := by
        refine ⟨Finset.Subset.rfl, fun f hf => ?_, fun _ _ => ⟨rfl, rfl⟩⟩
        simp only [H_lt_s'', unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_univ, true_and] at hf
        rcases hf with ⟨i, _, hi⟩
        exact (hInv_s''.H_level_sub i).2.1 hi
      have hcho_s'' : chooseLevel L q s'' ≤ (⟨c_star - 1, by omega⟩ : Fin (L + 1)).1 := by
        rw [hs''_eq]; exact lastRebuild_chooseLevel_le hq (by omega)
      have hEmb_s'' := hInv_s''.emb_at ⟨c_star - 1, by omega⟩ hcho_s''
      have hw_walk_s'' : H_lt_s''.IsWalk (G_s''.tail e) (G_s''.head e) w := by
        have he_w := hEmb_s''.2 e he_Gs''
        change (unionGraphLt G_s'' st_s''.H_level ((c_star - 1) + 1)).IsWalk _ _ _ at he_w
        rwa [show (c_star - 1) + 1 = c_star from Nat.sub_add_cancel (by omega), hw_s''] at he_w
      have hw_edge_s'' : ∀ x ∈ w, x.1 ∈ H_lt_s''.E := IsWalk.mem_edge hw_walk_s''
      have hEnds_lt2 : ∀ f ∈ H_lt_s''.E, H_lt2.tail f = G_s₂.tail f ∧ H_lt2.head f = G_s₂.head f :=
        fun _ _ => ⟨rfl, rfl⟩
      have hV_tail_s₂ : G_s₂.tail e ∈ G_s₂.V := (hVG_s₂ e he_Gs₂).1
      have hVw2 := walkVertices_subset_V_of_batch hVG_s'' hBV_d2 hds_d2 hSub_lt_s''
        (Hk := H_lt2) (by rw [← hGs₂_eq_d2]; exact hEnds_lt2) hw_edge_s''
        (by rw [← hGs₂_eq_d2]; exact hV_tail_s₂)
      have hw_disj_s'' : ∀ z ∈ st_tm.H.walkVertices (G_tm.tail e) w,
          z ∉ allTouched G_tm ((us.take s'').drop tm) := by
        intro z hz hzT
        have hsub : allTouched G_tm ((us.take s'').drop tm) ⊆
            allTouched G_tm (delta_tm_r.take idx) := by
          have h1 : (us.take s'').drop tm = (delta_tm_r.take idx).take (s'' - tm) := by
            have hpa : idx = a - tm := by omega
            have hda : delta_tm_r.take idx = (us.take a).drop tm := by
              rw [hpa]
              exact (drop_take_prefix us (by omega : tm ≤ a) (by omega : a ≤ r)).symm
            rw [hda]
            exact drop_take_prefix us htm_le_s'' hs''_le_a
          rw [h1]
          exact allTouched_take_mono _
        exact hprev_nt z hz (hsub hzT)
      have hGs''_tail : G_s''.tail e = G_tm.tail e := by
        have hz0 := mem_walkVertices_start st_tm.H (G_tm.tail e) w
        have hnt0 : G_tm.tail e ∉ allTouched G_tm ((us.take s'').drop tm) := hw_disj_s'' _ hz0
        obtain ⟨_, _, hBV_tm_s'', hds_tm_s'', hGs''_eq_tm, _, _, _⟩ :=
          applyBatch_drop_props hVG₀ hBV hds htm_le_s''
        change (G₀.applyBatch (us.take s'')).tail e = G_tm.tail e
        rw [hGs''_eq_tm]
        exact ((not_mem_allTouched_invariants _ G_tm hVG_tm hBV_tm_s'' hds_tm_s'' _ hnt0).2.2 e
          he_Gtm).1 rfl |>.2
      have hwv_s''_eq : H_lt_s''.walkVertices (G_s''.tail e) w =
          st_tm.H.walkVertices (G_tm.tail e) w := by
        obtain ⟨_, _, hBV_tm_s'', hds_tm_s'', hGs''_eq_tm, _, _, _⟩ :=
          applyBatch_drop_props hVG₀ hBV hds htm_le_s''
        refine walkVertices_unchanged_of_not_touched hVG_tm hBV_tm_s'' hds_tm_s'' hHtm_sub_G ?_
          hw_walk_sttm hGs''_tail hw_disj_s''
        intro f _; rw [← hGs''_eq_tm]; exact ⟨rfl, rfl⟩
      have hw₀_Sprev2 : w₀ ∈ S_prev2 := by
        rw [hS_prev2_eq]
        have hs₂_len : s₂ ≤ us.length := by omega
        have hidx2 : a - s'' < ((us.take s₂).drop s'').length := by
          rw [List.length_drop, List.length_take, min_eq_left hs₂_len]; omega
        have hsub2 := touchedVertices_mem_allTouched_middle (G₀ := G_s'') []
          ((us.take s₂).drop s'') (a - s'') hidx2
        simp only [List.nil_append] at hsub2
        refine hsub2 ?_
        have hpa : idx = a - tm := by omega
        have hda : delta_tm_r.take idx = (us.take a).drop tm := by
          rw [hpa]
          exact (drop_take_prefix us (by omega : tm ≤ a) (by omega : a ≤ r)).symm
        have hda2 : ((us.take s₂).drop s'').take (a - s'') = (us.take a).drop s'' :=
          (drop_take_prefix us hs''_le_a (by omega : a ≤ s₂)).symm
        have hsplit : (us.take a).drop tm = (us.take s'').drop tm ++ (us.take a).drop s'' := by
          have hs''_len : s'' ≤ us.length := by omega
          have hlen : (us.take s'').length = s'' := by rw [List.length_take, min_eq_left hs''_len]
          conv_lhs => rw [take_split_drop hs''_le_a, List.drop_append, hlen,
            Nat.sub_eq_zero_of_le htm_le_s'']
          rfl
        have hGa_eq : G_s''.applyBatch (((us.take s₂).drop s'').take (a - s'')) =
            G_tm.applyBatch (delta_tm_r.take idx) := by
          obtain ⟨_, _, _, _, hGs''_eq_tm, _, _, _⟩ :=
            applyBatch_drop_props hVG₀ hBV hds htm_le_s''
          rw [hda, hda2, hsplit, applyBatch_append, ← hGs''_eq_tm]
        have helem : ((us.take s₂).drop s'')[a - s'']'hidx2 = delta_tm_r[idx]'hidx_lt := by
          simp only [delta_tm_r, List.getElem_drop, List.getElem_take]
          congr 1; omega
        rwa [hGa_eq, helem]
      have hhit_s'' : ∃ z₀ ∈ H_lt_s''.walkVertices (G_s''.tail e) w, z₀ ∈ S_prev2 :=
        ⟨w₀, hwv_s''_eq ▸ hw₀W, hw₀_Sprev2⟩
      exact (exists_mem_walkVertices_iff_anc hVG_s'' hBV_d2 hds_d2 hSub_lt_s''
        (Hk := H_lt2) (by rw [← hGs₂_eq_d2]; exact hEnds_lt2) (by rw [hS_prev2_eq])
        hw_edge_s'' (by rw [← hGs₂_eq_d2]; exact hV_tail_s₂)
        (by exact (hAnc_s''_s₂ e he_Gs'').1) hVw2).mpr hhit_s''
    have he_mid_c : e ∈ inDom_mid ⟨c_star, Nat.lt_succ_of_le hc_le_L⟩ := by
      refine Finset.mem_inter.mpr ⟨?_, heG'⟩
      rw [hk_inv.inDom_eq ⟨c_star, Nat.lt_succ_of_le hc_le_L⟩, hlast_c_eq]
      exact Finset.mem_inter.mpr ⟨hst_s₂_inDom, hk_inv.G_eq ▸ hG'E_sub_k heG'⟩
    exact hm_none ⟨c_star, Nat.lt_succ_of_le hc_le_L⟩ hm_lt_c (Nat.lt_of_le_pred hj_pos hc_le) he_mid_c
  -- Finish: H_lt_r.walkVertices (G_r.tail e) w = st_tm.H.walkVertices (G_tm.tail e) w
  have hGr_tail : G_r.tail e = G_tm.tail e := by
    have hz0 := mem_walkVertices_start st_tm.H (G_tm.tail e) w
    have hnt0 : G_tm.tail e ∉ allTouched G_tm delta_tm_r := hNoTouch_tm_r _ hz0
    rw [hGr_eq_tm]
    exact ((not_mem_allTouched_invariants delta_tm_r G_tm hVG_tm hBV_tm_r hds_tm_r _ hnt0).2.2 e
      he_Gtm).1 rfl |>.2
  set H_lt_r := unionGraphLt G_r st_r.H_level j
  have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
    refine ⟨Finset.Subset.rfl, fun f hf => ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hf
    rcases hf with ⟨i, _, hi⟩
    exact (hInv_r.H_level_sub i).2.1 hi
  have hwv_r_eq : H_lt_r.walkVertices (G_r.tail e) w = st_tm.H.walkVertices (G_tm.tail e) w :=
    walkVertices_unchanged_of_not_touched hVG_tm hBV_tm_r hds_tm_r hHtm_sub_G
      (fun f _ => by rw [← hGr_eq_tm]; exact ⟨rfl, rfl⟩) hw_walk_sttm hGr_tail hNoTouch_tm_r
  have hw_r_eq : piLe st_r (j - 1) e = w := by
    change piLtFrom st_r.Pi_level st_r.inDom ((j - 1) + 1) e = w
    rw [show (j - 1) + 1 = j from Nat.sub_add_cancel hj_pos]
    have h0_r : e ∈ st_r.inDom ⟨0, Nat.zero_lt_succ L⟩ := by rw [hInv_r.inDom0]; exact he_Gr
    have hm_r_eq : ∀ q' : Fin (L + 1), q'.1 < j →
        lastRebuild q L q'.1 r = lastRebuild q L q'.1 k := fun q' hq' => by
      have h1 : lastRebuild q L q'.1 k ≤ r := by
        rw [hr_eq_k]
        exact lastRebuild_mono_level hq (Nat.le_pred_of_lt hq') (le_trans (Nat.sub_le j 1) hj_le)
      exact lastRebuild_idempotent_le hq h1 hr_le_k
    have hcongr_in : ∀ q' : Fin (L + 1), q'.1 < j →
        (e ∈ st_r.inDom q' ↔ e ∈ inDom_mid q') := fun q' hq' => by
      simp only [inDom_mid, Finset.mem_inter]
      rw [hInv_r.inDom_eq q', hm_r_eq q' hq', hk_inv.inDom_eq q', Finset.mem_inter,
        Finset.mem_inter, ← hk_inv.G_eq]
      have h1 := heG'; have h2 := hG'E_sub_k heG'
      tauto
    obtain ⟨m_r, hm_r_lt, hm_r_dom, hm_r_none, heq_r⟩ :=
      piLtFrom_eq st_r.Pi_level st_r.inDom hj_pos h0_r
    have hm_r_is_m : m_r = m := by
      by_contra hne
      rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
      · exact hm_r_none m hlt hmj ((hcongr_in m hmj).mpr hm_dom)
      · exact hm_none m_r hlt hm_r_lt ((hcongr_in m_r hm_r_lt).mp hm_r_dom)
    rw [heq_r, hm_r_is_m, hInv_r.Pi_level_eq m, hm_r_eq m hmj, ← htm_def]
  have hcho_r : chooseLevel L q r ≤ (⟨j - 1, by omega⟩ : Fin (L + 1)).1 := by
    rw [hr_def]; exact lastRebuild_chooseLevel_le hq (by omega)
  have hEmb_r := hInv_r.emb_at ⟨j - 1, by omega⟩ hcho_r
  have hw_walk_r : H_lt_r.IsWalk (G_r.tail e) (G_r.head e) w := by
    have he_w := hEmb_r.2 e he_Gr
    change (unionGraphLt G_r st_r.H_level ((j - 1) + 1)).IsWalk _ _ _ at he_w
    rwa [show (j - 1) + 1 = j from Nat.sub_add_cancel hj_pos, hw_r_eq] at he_w
  have hw_edge_r : ∀ x ∈ w, x.1 ∈ H_lt_r.E := IsWalk.mem_edge hw_walk_r
  have hEnds_lt : ∀ f ∈ H_lt_r.E, H_lt.tail f = G'.tail f ∧ H_lt.head f = G'.head f :=
    fun _ _ => ⟨rfl, rfl⟩
  have hV_tail' : G'.tail e ∈ G'.V := (hVG' e heG').1
  have hVw_r := walkVertices_subset_V_of_batch hVG_r hBV_r_d hds_r_d hSub_lt_r
    (Hk := H_lt) (by rw [← hG'_delta_r]; exact hEnds_lt) hw_edge_r (by rw [← hG'_delta_r]; exact hV_tail')
  have hhit_G' : ∃ z ∈ H_lt.walkVertices (G'.tail e) w, z ∈ S_prev := by
    have h1 := (Finset.mem_filter.mp heAff).2
    rw [decide_eq_true_eq, hw_mid_eq] at h1
    exact h1
  obtain ⟨v, hv_w, hv_S⟩ := (exists_mem_walkVertices_iff_anc hVG_r hBV_r_d hds_r_d hSub_lt_r
    (Hk := H_lt) (by rw [← hG'_delta_r]; exact hEnds_lt) (by rw [hS_prev_eq])
    hw_edge_r (by rw [← hG'_delta_r]; exact hV_tail')
    (hAnc_r_k1 e he_Gr).1 hVw_r).mp hhit_G'
  rw [hwv_r_eq] at hv_w
  have hv_Vtm : v ∈ st_tm.H.V := by
    have hVH_tm : st_tm.H.IsValid := hInv_tm.H_valid
    have htail_tm : G_tm.tail e ∈ st_tm.H.V := by
      rw [hInv_tm.H_V]; exact (hVG_tm e he_Gtm).1
    exact IsWalk.walkVertices_mem_V hVH_tm hw_walk_sttm htail_tm v hv_w
  have hv_cap : v < x.vCap := by
    apply hV_cap
    rw [hk_inv.G_eq]
    obtain ⟨_, _, _, _, _, _, hV_tm_k, _⟩ := applyBatch_drop_props hVG₀ hBV hds htm_le_k
    exact hV_tm_k (hInv_tm.H_V ▸ hv_Vtm)
  have hRev_m := (hRev m).2 v hv_cap e
  rw [← htm_def] at hRev_m
  refine ⟨v, hv_S, hRev_m.mpr ⟨hm_dom_tm, ?_⟩⟩
  simpa [st_tm, hInv_tm.G_eq] using hv_w

private lemma sum_vcongBound_le {γ_c γ_ℓ : ℝ} (hc : 1 ≤ γ_c) (hl : 1 ≤ γ_ℓ) (maxDeg₀ : ℕ) :
    ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), vcongBound γ_c γ_ℓ maxDeg₀ i) ≤
      2 * vcongBound γ_c γ_ℓ maxDeg₀ n
  | 0 => by
    have h0_nn := vcongBound_nonneg (γ_c := γ_c) (γ_ℓ := γ_ℓ) (by linarith) (by linarith) maxDeg₀ 0
    rw [Finset.range_one, Finset.sum_singleton]
    linarith
  | n + 1 => by
    have ih := sum_vcongBound_le hc hl maxDeg₀ n
    have hstep := vcongBound_step hc hl maxDeg₀ n
    have hnn := vcongBound_nonneg (γ_c := γ_c) (γ_ℓ := γ_ℓ) (by linarith) (by linarith) maxDeg₀ n
    have hlen_nn : 0 ≤ lenBound γ_ℓ n := lenBound_nonneg (by linarith) n
    have hprod_ge1 : 1 ≤ γ_c * (lenBound γ_ℓ n + 1) := by nlinarith
    have h4 : 4 * vcongBound γ_c γ_ℓ maxDeg₀ n ≤ vcongBound γ_c γ_ℓ maxDeg₀ (n + 1) := by
      have hmul : 3 * vcongBound γ_c γ_ℓ maxDeg₀ n ≤
          γ_c * (lenBound γ_ℓ n + 1) * (3 * vcongBound γ_c γ_ℓ maxDeg₀ n) := by nlinarith
      linarith
    rw [Finset.sum_range_succ]
    linarith

/-- Total reverse-list candidate edges scanned across levels `i < j` and vertices `v ∈ S_prev` is
at most `2 * S_prev.card * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)`. -/
theorem revLists_cand_sum_le {L q mMax : ℕ} {P : SparsifyParams}
    {G₀ : MGraph} {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {us : List Update} {k : ℕ} {x : DynSpannerMeta L}
    (hVG₀ : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hq1 : 1 ≤ q) (hAll : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    (hRev : RevHistoryInv G₀ q sparsify us k x)
    {j : ℕ} (hj_pos : 0 < j) (hj_le : j ≤ L)
    (S_prev : Finset ℕ) (hS_cap : ∀ v ∈ S_prev, v < x.vCap)
    (hnd : ∀ i : Fin (L + 1), ∀ v < x.vCap, (x.revLists i v).Nodup) :
    (∑ i ∈ (Finset.univ : Finset (Fin (L + 1))).filter (fun i => i.1 < j),
      ∑ v ∈ S_prev, ((x.revLists i v).length : ℝ)) ≤
      2 * (S_prev.card : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1) := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (L + 1))).filter (fun i => i.1 < j),
      ∑ v ∈ S_prev, ((x.revLists i v).length : ℝ) ≤
        (S_prev.card : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 := fun i _ => by
    have h1 : ∀ v ∈ S_prev, ((x.revLists i v).length : ℝ) ≤
        vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 := fun v hv =>
      revLists_card_le_vcongBound hVG₀ hBV hds hq1 hAll hRev (hS_cap v hv) (hnd i v (hS_cap v hv))
    calc ∑ v ∈ S_prev, ((x.revLists i v).length : ℝ)
        ≤ ∑ _v ∈ S_prev, vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 := Finset.sum_le_sum h1
      _ = (S_prev.card : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsum1 := Finset.sum_le_sum hterm
  have hsum2 : (∑ i ∈ (Finset.univ : Finset (Fin (L + 1))).filter (fun i => i.1 < j),
      (S_prev.card : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1) =
      (S_prev.card : ℝ) * ∑ idx ∈ Finset.range j, vcongBound P.γ_c P.γ_ℓ G₀.maxDeg idx := by
    rw [← Finset.mul_sum]
    congr 1
    refine Finset.sum_bij (fun i _ => i.1) (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hi ⊢; exact hi)
      (fun a₁ _ a₂ _ h => Fin.ext h)
      (fun b hb => ⟨⟨b, by simp only [Finset.mem_range] at hb; omega⟩,
        by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hb ⊢; exact hb, rfl⟩)
      (fun _ _ => rfl)
  have hgeo := sum_vcongBound_le P.hγ_c P.hγ_ℓ G₀.maxDeg (j - 1)
  rw [show (j - 1) + 1 = j from Nat.sub_add_cancel hj_pos] at hgeo
  have hS_nn : (0 : ℝ) ≤ (S_prev.card : ℝ) := Nat.cast_nonneg _
  calc (∑ i ∈ (Finset.univ : Finset (Fin (L + 1))).filter (fun i => i.1 < j),
        ∑ v ∈ S_prev, ((x.revLists i v).length : ℝ))
      ≤ (S_prev.card : ℝ) * ∑ idx ∈ Finset.range j, vcongBound P.γ_c P.γ_ℓ G₀.maxDeg idx :=
          hsum1.trans_eq hsum2
    _ ≤ (S_prev.card : ℝ) * (2 * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)) :=
          mul_le_mul_of_nonneg_left hgeo hS_nn
    _ = 2 * (S_prev.card : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1) := by ring

end

end MinCostFlow.DynSpanner.Program
