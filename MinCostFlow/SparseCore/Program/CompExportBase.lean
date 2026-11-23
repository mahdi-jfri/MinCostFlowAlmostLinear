module

public import MinCostFlow.SparseCore.Program.CompBatchBase
public import MinCostFlow.SparseCore.Program.ReadSpec
import MinCostFlow.SparseCore.CoreModel
import WordRAM.Tactic

/-!
# Branch Export Helpers (`CompExportBase`)

Pure graph-theoretic lemmas and the first two export sub-loops for `op 6` (`compExportBranchProc`,
providing the `Restart.ExportAt` and `Read.ReadInitAt` data for branch `j`):
1. `compLSF_T_cur_E_sub_compEdgeSet`: every tree edge of every component belongs to
   `compEdgeSet cs.G₀ C`, so `encTEdge cs.G₀ C f = f` and isolated components have `T_cur.E = ∅`.
2. `exportAt_of_lists`: builds `Restart.ExportAt` from `ListAt` vertex lists and contiguous edge
   triples.
3. `compExpRootsStmt` / `compExpRoots_runs`: scans `vL` of `gPtr` in `O(G.n + 1)` time to emit the
   exact `Nodup` root list of `(S j).RF.R`.
4. `compExpPairsStmt` / `compExpPairs_runs`: scans `eL` of `gPtr` in `O((G.m + 1) * L_w)` time to
   populate the `(numPtr, denPtr)` stretch-pair tables of branch `j`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Pure graph-theoretic export lemmas -/

/-- Every edge of `(cs.compSt C).T_cur` lies in `compEdgeSet cs.G₀ C` (no non-component bridge
edges can appear when `compGraph cs.G₀ C` is connected). -/
lemma compLSF_T_cur_E_sub_compEdgeSet {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    (cs.compSt C).T_cur.E ⊆ compEdgeSet cs.G₀ C := by
  classical
  have hCI := (hI.hCompLSF C hC).1
  have hG0C : (cs.compSt C).G₀ = compGraph cs.G₀ C := (hI.hCompLSF C hC).2.1
  intro f hf
  have hfT0 : f ∈ (cs.compSt C).T₀.E := hCI.hT_cur_E ▸ hf
  have hT0 := hCI.hT₀
  have hF0 : (cs.compSt C).T₀.IsForest := hT0.isForest
  set T0 := (cs.compSt C).T₀
  set G0 := (cs.compSt C).G₀
  have hG0_conn : ∀ u ∈ G0.V, ∀ v ∈ G0.V, G0.Connected u v := by
    rw [hG0C]; exact compGraph_connected hI.hG₀_val hC
  have hsubE : ∀ e ∈ G0.E, walkEdges (T0.forestPath (G0.tail e) (G0.head e)) ⊆ G0.E := hCI.hTp₀
  have hf_ends := hF0.1 f hfT0
  have hno_loop : T0.tail f ≠ T0.head f := isForest_no_selfLoop hF0 hfT0
  set F' : MGraph := { T0 with E := T0.E.erase f }
  set A : Finset ℕ := T0.V.filter fun u => F'.Connected (T0.tail f) u
  have htA : T0.tail f ∈ A := Finset.mem_filter.mpr ⟨hf_ends.1, connected_refl _ _⟩
  have hhNotA : T0.head f ∉ A := by
    intro hmem
    have hconn := (Finset.mem_filter.mp hmem).2
    obtain ⟨P, hP⟩ := connected_isPath hconn
    have hP_T0 : T0.IsPath (T0.tail f) (T0.head f) P := by
      refine ⟨?_, hP.2⟩
      have hlift : ∀ {x y : ℕ} {Q : List (ℕ × Bool)}, F'.IsWalk x y Q → T0.IsWalk x y Q := by
        intro x y Q hQ
        induction hQ with
        | nil z => exact .nil z
        | cons he hs _ ih => exact .cons (Finset.mem_of_mem_erase he) hs ih
      exact hlift hP.1
    have h1_path : T0.IsPath (T0.tail f) (T0.head f) [(f, true)] := by
      refine ⟨.cons hfT0 rfl (.nil _), ?_⟩
      simp [MGraph.walkVertices, MGraph.dst, hno_loop]
    have hP_eq : P = [(f, true)] := isPath_unique hF0 hP_T0 h1_path
    have hcontra : ∀ x y Q, F'.IsWalk x y Q → Q = [(f, true)] → False := by
      intro x y Q hQ hEq
      cases hQ with
      | nil _ => cases hEq
      | cons he _ _ => cases hEq; exact (Finset.mem_erase.mp he).1 rfl
    exact hcontra _ _ P hP.1 hP_eq
  have hwalk_exit : ∀ {x y : ℕ} {Q : List (ℕ × Bool)}, G0.IsWalk x y Q → x ∈ A → y ∉ A →
      ∃ e ∈ G0.E, (G0.tail e ∈ A ∧ G0.head e ∉ A) ∨ (G0.head e ∈ A ∧ G0.tail e ∉ A) := by
    intro x y Q hQ
    induction hQ with
    | nil _ => intro h1 h2; exact absurd h1 h2
    | @cons x y z rest heE hsrc _ ih =>
      intro hxA hyNotA
      by_cases hdstA : G0.dst z ∈ A
      · exact ih hdstA hyNotA
      · rcases z with ⟨e, _ | _⟩
        · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
          simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hdstA
          exact ⟨e, heE, Or.inr ⟨hsrc ▸ hxA, hdstA⟩⟩
        · simp only [MGraph.src, ↓reduceIte] at hsrc
          simp only [MGraph.dst, ↓reduceIte] at hdstA
          exact ⟨e, heE, Or.inl ⟨hsrc ▸ hxA, hdstA⟩⟩
  obtain ⟨Q, hQ⟩ := hG0_conn (T0.tail f) (hCI.hTV ▸ hf_ends.1) (T0.head f) (hCI.hTV ▸ hf_ends.2)
  obtain ⟨e, heE, hcross⟩ := hwalk_exit hQ htA hhNotA
  have heEnds := hCI.hG₀_val e heE
  have hPe : T0.IsPath (G0.tail e) (G0.head e) (T0.forestPath (G0.tail e) (G0.head e)) :=
    forestPath_isPath hF0 (hT0.connected (hCI.hTV.symm ▸ heEnds.1) (hCI.hTV.symm ▸ heEnds.2))
  have hf_on_Pe : f ∈ walkEdges (T0.forestPath (G0.tail e) (G0.head e)) := by
    by_contra hnot
    have hwalkF' : ∀ {x y : ℕ} {R : List (ℕ × Bool)}, T0.IsWalk x y R → f ∉ walkEdges R → F'.IsWalk x y R := by
      intro x y R hR
      induction hR with
      | nil z => intro _; exact .nil z
      | @cons x y z rest hzE hs _ ih =>
        intro hnf
        have hne : z.1 ≠ f := fun h => hnf (by simp [walkEdges, h])
        exact .cons (Finset.mem_erase.mpr ⟨hne, hzE⟩) hs
          (ih fun h => hnf (by simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert]; exact Or.inr h))
    have hconn_e : F'.Connected (G0.tail e) (G0.head e) := ⟨_, hwalkF' hPe.1 hnot⟩
    rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (Finset.mem_filter.mpr ⟨hCI.hTV.symm ▸ heEnds.2, connected_trans (Finset.mem_filter.mp h1).2 hconn_e⟩)
    · exact h2 (Finset.mem_filter.mpr ⟨hCI.hTV.symm ▸ heEnds.1, connected_trans (Finset.mem_filter.mp h1).2 (connected_symm hconn_e)⟩)
  have hfG0 : f ∈ G0.E := hsubE e heE hf_on_Pe
  simpa [G0, hG0C, compGraph] using hfG0

/-- Every edge of `cs.T` comes from a unique edgeful component without relabeling (`encTEdge = id`),
is active in that component's `G` and not in `cs.insertedGlobal`, has endpoints matching `(cs.compSt C).G`,
and the total number of initial tree edges across edgeful components is at most `cs.G.n`. -/
lemma compLSF_T_eq_edgeful {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) :
    (∀ C ∈ components cs.G₀, (compGraph cs.G₀ C).m = 0 → (cs.compSt C).T_cur.E = ∅) ∧
    cs.T.E = (edgefulComps cs.G₀).biUnion (fun C =>
      (cs.compSt C).T_cur.E.filter fun f => f ∈ (cs.compSt C).G.E ∧ f ∉ cs.insertedGlobal) ∧
    (∀ C ∈ edgefulComps cs.G₀, ∀ f ∈ (cs.compSt C).T_cur.E,
      f ∈ (cs.compSt C).G.E → f ∉ cs.insertedGlobal →
      cs.T.tail f = (cs.compSt C).G.tail f ∧ cs.T.head f = (cs.compSt C).G.head f) ∧
    (∀ C₁ ∈ edgefulComps cs.G₀, ∀ C₂ ∈ edgefulComps cs.G₀, C₁ ≠ C₂ →
      Disjoint (cs.compSt C₁).T_cur.E (cs.compSt C₂).T_cur.E) ∧
    cs.T.m ≤ cs.G₀.m ∧
    (edgefulComps cs.G₀).sum (fun C => (cs.compSt C).T_cur.m) ≤ cs.G.n := by
  classical
  have hsub : ∀ C ∈ components cs.G₀, (cs.compSt C).T_cur.E ⊆ compEdgeSet cs.G₀ C :=
    fun C hC => compLSF_T_cur_E_sub_compEdgeSet hI hC
  have hiso : ∀ C ∈ components cs.G₀, (compGraph cs.G₀ C).m = 0 → (cs.compSt C).T_cur.E = ∅ := by
    intro C hC hm
    rw [Finset.eq_empty_iff_forall_notMem]
    intro f hf
    have hfE := hsub C hC hf
    have hpos : 0 < (compGraph cs.G₀ C).m := Finset.card_pos.mpr ⟨f, hfE⟩
    omega
  have hEeq : cs.T.E = (edgefulComps cs.G₀).biUnion (fun C =>
      (cs.compSt C).T_cur.E.filter fun f => f ∈ (cs.compSt C).G.E ∧ f ∉ cs.insertedGlobal) := by
    ext e
    simp only [CompLSFState.T, edgefulComps, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨C, hC, f, hf, rfl⟩, heG, heNI⟩
      have hfE := hsub C hC hf
      rw [encTEdge_eq_self hfE] at heG heNI ⊢
      have heNC : f ∉ cs.crossEdges := fun hc => heNI (hI.hCross_sub hc)
      obtain ⟨C', hC', hfC'⟩ := hI.hEdge_cover f heG heNC
      have hfNI' : f ∉ (cs.compSt C').insertedEdges := fun hi => heNI (hI.hCompIns_sub C' hC' hi)
      have hCI' := (hI.hCompLSF C' hC').1
      have hfE' : f ∈ compEdgeSet cs.G₀ C' := by
        have h1 := (hCI'.hsurv_edge f hfC' hfNI').1
        rwa [(hI.hCompLSF C' hC').2.1, compGraph] at h1
      have hCC' : C' = C := by
        by_contra hne
        exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint cs.G₀ hC' hC hne) hfE' hfE
      exact ⟨C, ⟨hC, Finset.card_pos.mpr ⟨f, hfE⟩⟩, hf, hCC' ▸ hfC', heNI⟩
    · rintro ⟨C, ⟨hC, _⟩, hf, hfCG, hfNI⟩
      exact ⟨⟨C, hC, e, hf, encTEdge_eq_self (hsub C hC hf)⟩, hI.hCE_sub C hC hfCG, hfNI⟩
  have hends : ∀ C ∈ edgefulComps cs.G₀, ∀ f ∈ (cs.compSt C).T_cur.E,
      f ∈ (cs.compSt C).G.E → f ∉ cs.insertedGlobal →
      cs.T.tail f = (cs.compSt C).G.tail f ∧ cs.T.head f = (cs.compSt C).G.head f := by
    intro C hC f _ hfCG hfNI
    have hCm : C ∈ components cs.G₀ := (Finset.mem_filter.mp hC).1
    have hfNC : f ∉ cs.crossEdges := fun hc => hfNI (hI.hCross_sub hc)
    have he := hI.hNonCross_ends C hCm f hfCG hfNC
    exact ⟨he.1.symm, he.2.symm⟩
  have hdisj : ∀ C₁ ∈ edgefulComps cs.G₀, ∀ C₂ ∈ edgefulComps cs.G₀, C₁ ≠ C₂ →
      Disjoint (cs.compSt C₁).T_cur.E (cs.compSt C₂).T_cur.E := by
    intro C₁ hC₁ C₂ hC₂ hne
    have h1 := compEdgeSet_pairwiseDisjoint cs.G₀ (Finset.mem_filter.mp hC₁).1 (Finset.mem_filter.mp hC₂).1 hne
    exact h1.mono (hsub C₁ (Finset.mem_filter.mp hC₁).1) (hsub C₂ (Finset.mem_filter.mp hC₂).1)
  have hm_le : cs.T.m ≤ cs.G₀.m := by
    refine Finset.card_le_card fun f hf => ?_
    rw [hEeq, Finset.mem_biUnion] at hf
    obtain ⟨C, hC, hfC⟩ := hf
    exact (Finset.mem_filter.mp (hsub C (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hfC).1)).1
  have hsum_le : (edgefulComps cs.G₀).sum (fun C => (cs.compSt C).T_cur.m) ≤ cs.G.n := by
    have hterm : ∀ C ∈ edgefulComps cs.G₀, (cs.compSt C).T_cur.m ≤ ((cs.compSt C).G.V).card := by
      intro C hC
      have hCm := (Finset.mem_filter.mp hC).1
      have hCI := LSFInvWith.toStructInv (hI.hCompLSF C hCm).1
      have hT_E : (cs.compSt C).T_cur.E = (cs.compSt C).T₀.E := hCI.hT_cur_E
      have hT_le : (cs.compSt C).T₀.E.card ≤ (cs.compSt C).T₀.V.card := by
        have h1 := spanningTree_edge_card hCI.hT₀.1 ⟨_, hCI.hT₀.2⟩
        omega
      have hV_le : (cs.compSt C).T₀.V.card ≤ (cs.compSt C).G.V.card := by
        rw [hCI.hGV_eq]
        exact Finset.card_le_card Finset.subset_union_left
      change (cs.compSt C).T_cur.E.card ≤ (cs.compSt C).G.V.card
      rw [hT_E]; exact le_trans hT_le hV_le
    calc (edgefulComps cs.G₀).sum (fun C => (cs.compSt C).T_cur.m)
        ≤ (edgefulComps cs.G₀).sum (fun C => ((cs.compSt C).G.V).card) := Finset.sum_le_sum hterm
      _ ≤ (components cs.G₀).sum (fun C => ((cs.compSt C).G.V).card) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ((components cs.G₀).biUnion (fun C => (cs.compSt C).G.V)).card :=
          (Finset.card_biUnion fun C₁ hC₁ C₂ hC₂ hne => hI.hV_disj C₁ hC₁ C₂ hC₂ hne).symm
      _ = cs.G.n := by rw [hI.hV_eq]; rfl
  exact ⟨hiso, hEeq, hends, hdisj, hm_le, hsum_le⟩

/-- `cs.RF.F` edge decomposition across edgeful components and `cs.RF.F.m ≤ cs.G₀.m`. -/
lemma compLSF_F_eq_edgeful {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) :
    cs.RF.F.E = (edgefulComps cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) ∧
    (∀ C ∈ edgefulComps cs.G₀, ∀ f ∈ (cs.compSt C).RF.F.E,
      cs.RF.F.tail f = (cs.compSt C).RF.F.tail f ∧ cs.RF.F.head f = (cs.compSt C).RF.F.head f) ∧
    (∀ C₁ ∈ edgefulComps cs.G₀, ∀ C₂ ∈ edgefulComps cs.G₀, C₁ ≠ C₂ →
      Disjoint (cs.compSt C₁).RF.F.E (cs.compSt C₂).RF.F.E) ∧
    cs.RF.F.m ≤ cs.G₀.m := by
  classical
  have hEeq : cs.RF.F.E = (edgefulComps cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) := by
    ext e
    simp only [CompLSFState.RF, edgefulComps, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨C, hC, he⟩
      have heC := hI.hF_sub_compE C hC he
      exact ⟨C, ⟨hC, Finset.card_pos.mpr ⟨e, heC⟩⟩, he⟩
    · rintro ⟨C, ⟨hC, _⟩, he⟩
      exact ⟨C, hC, he⟩
  have hends : ∀ C ∈ edgefulComps cs.G₀, ∀ f ∈ (cs.compSt C).RF.F.E,
      cs.RF.F.tail f = (cs.compSt C).RF.F.tail f ∧ cs.RF.F.head f = (cs.compSt C).RF.F.head f := by
    intro C hC f hf
    have hsub := compLSF_RF_sub_comp hI (Finset.mem_filter.mp hC).1
    exact ⟨(hsub.2.2 f hf).1.symm, (hsub.2.2 f hf).2.symm⟩
  have hdisj : ∀ C₁ ∈ edgefulComps cs.G₀, ∀ C₂ ∈ edgefulComps cs.G₀, C₁ ≠ C₂ →
      Disjoint (cs.compSt C₁).RF.F.E (cs.compSt C₂).RF.F.E := by
    intro C₁ hC₁ C₂ hC₂ hne
    have h1 := compEdgeSet_pairwiseDisjoint cs.G₀ (Finset.mem_filter.mp hC₁).1 (Finset.mem_filter.mp hC₂).1 hne
    exact h1.mono (hI.hF_sub_compE C₁ (Finset.mem_filter.mp hC₁).1)
      (hI.hF_sub_compE C₂ (Finset.mem_filter.mp hC₂).1)
  have hm_le : cs.RF.F.m ≤ cs.G₀.m := by
    refine Finset.card_le_card fun f hf => ?_
    rw [hEeq, Finset.mem_biUnion] at hf
    obtain ⟨C, hC, hfC⟩ := hf
    exact (Finset.mem_filter.mp (hI.hF_sub_compE C (Finset.mem_filter.mp hC).1 hfC)).1
  exact ⟨hEeq, hends, hdisj, hm_le⟩

/-- Number of edgeful components never exceeds `cs.G.n`. -/
lemma compLSF_numEdgeful_le_n {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {numComps vCap eCap numEdgeful : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ}
    {edgefulComp : Fin numEdgeful → Fin numComps}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    (hef_inj : Function.Injective edgefulComp) :
    numEdgeful ≤ cs.G.n := by
  classical
  have hne : ∀ c : Fin numComps, ((cs.compSt (compOf c)).G.V).Nonempty := fun c => by
    have hCI := (hI.hCompLSF _ (hT.compOf_mem c)).1
    obtain ⟨v, hv⟩ := compGraph_nonempty (hT.compOf_mem c)
    exact ⟨v, hCI.hGV_eq ▸ Finset.mem_union_left _ (hCI.hTV ▸ (hI.hCompLSF _ (hT.compOf_mem c)).2.1.symm ▸ hv)⟩
  let f : Fin numEdgeful → ℕ := fun ec => (hne (edgefulComp ec)).choose
  have hf_mem : ∀ ec : Fin numEdgeful, f ec ∈ cs.G.V := fun ec =>
    hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨compOf (edgefulComp ec), hT.compOf_mem _, (hne (edgefulComp ec)).choose_spec⟩
  have hf_inj : Function.Injective f := fun ec₁ ec₂ heq => by
    by_contra hne_ec
    have h1 : f ec₁ ∈ (cs.compSt (compOf (edgefulComp ec₁))).G.V := (hne (edgefulComp ec₁)).choose_spec
    have h2 : f ec₂ ∈ (cs.compSt (compOf (edgefulComp ec₂))).G.V := (hne (edgefulComp ec₂)).choose_spec
    have hc_ne : compOf (edgefulComp ec₁) ≠ compOf (edgefulComp ec₂) :=
      fun h => hne_ec (hef_inj (hT.hBij.1 h))
    rw [heq] at h1
    exact Finset.disjoint_left.mp (hI.hV_disj _ (hT.compOf_mem _) _ (hT.compOf_mem _) hc_ne) h1 h2
  calc numEdgeful = (Finset.univ : Finset (Fin numEdgeful)).card := by simp
    _ = ((Finset.univ : Finset (Fin numEdgeful)).image f).card := (Finset.card_image_of_injective _ hf_inj).symm
    _ ≤ cs.G.V.card := Finset.card_le_card fun v hv => by
        obtain ⟨ec, _, rfl⟩ := Finset.mem_image.mp hv; exact hf_mem ec

/-- Build `Restart.ExportAt` from explicit vertex list `vL` and edge-triple list `eT`. -/
lemma exportAt_of_lists {mem : ℕ → ℕ} {d hEnd vPtr ePtr : ℕ} {G : MGraph}
    {vL : List ℕ} {eT : List (ℕ × ℕ × ℕ)}
    (hd0 : mem d = G.n) (hd1 : mem (d + 1) = vPtr) (hd2 : mem (d + 2) = G.m) (hd3 : mem (d + 3) = ePtr)
    (hvLen : vL.length = G.n) (hvNd : vL.Nodup) (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (hvAt : ListAt mem vPtr vL)
    (heLen : eT.length = G.m) (heNd : (eT.map Prod.fst).Nodup)
    (heSub : ∀ t ∈ eT, t.1 ∈ G.E ∧ t.2.1 = G.tail t.1 ∧ t.2.2 = G.head t.1)
    (heCov : ∀ e ∈ G.E, ∃ t ∈ eT, t.1 = e)
    (heAt : ∀ i (hi : i < eT.length),
      mem (ePtr + 3 * i) = eT[i].1 ∧ mem (ePtr + 3 * i + 1) = eT[i].2.1 ∧ mem (ePtr + 3 * i + 2) = eT[i].2.2)
    (hb1 : d + 4 ≤ hEnd) (hb2 : d ≤ vPtr) (hb3 : d ≤ ePtr)
    (hb4 : vPtr + G.n ≤ hEnd) (hb5 : ePtr + 3 * G.m ≤ hEnd) :
    Restart.ExportAt mem d hEnd G := by
  have hv_eq : readList mem (mem (d + 1)) (mem d) = vL := by
    rw [hd1, hd0, ← hvLen]
    refine List.ext_getElem (by simp [readList]) fun i h1 h2 => by
      simp only [readList, List.getElem_map, List.getElem_range]; exact hvAt i h2
  have he_eq : readTriples mem (mem (d + 3)) (mem (d + 2)) = eT := by
    rw [hd3, hd2, ← heLen]
    refine List.ext_getElem (by simp [readTriples]) fun i h1 h2 => by
      simp only [readTriples, List.getElem_map, List.getElem_range]
      obtain ⟨a1, a2, a3⟩ := heAt i h2
      exact Prod.ext a1 (Prod.ext a2 a3)
  dsimp only [Restart.ExportAt]
  rw [hv_eq, he_eq, hd0, hd1, hd2, hd3]
  exact ⟨rfl, rfl, hvNd, hvMem, heNd, heSub, heCov, hb1, hb2, hb3, hb4, hb5⟩

/-! ## 2. Sub-loop 1: Export roots of `(S j).RF.R` -/

/-- Scan `r4 = n` vertices at `r3 = vPtr` (holding `vL` of `G.V`) and append every vertex belonging
to `(S j).RF.R` starting at `r5 = rootsPtr`, accumulating `r6 = nR`.
Registers preserved `< 6`: `r0 = b`, `r1 = j`, `r2 = k`, `r3 = vPtr`, `r4 = n`, `r5 = rootsPtr`.
Uses scratch registers `7..15`. -/
def compExpRootsStmt : Stmt :=
  .assign 6 (.const 0) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const compOffVCompPtr))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
  .assign 11 (.const 0) ;;
  .loop (.bin .lt (.reg 11) (.reg 4))
    (.assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
     .assign 13 (.load (.bin .add (.reg 7) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
     .cond (.reg 14)
       (.assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;
        .assign 14 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 14) (.reg 2)) (.reg 1)))) ;;
        .assign 14 (.load (.bin .add (.reg 14) (.const lsfOffFAncPtr))) ;;
        .assign 14 (.load (.bin .add (.reg 14) (.const fOffIsRootPtr))) ;;
        .assign 14 (.load (.bin .add (.reg 14) (.reg 12))))
       (.assign 14 (.const 1)) ;;
     .cond (.reg 14)
       (.store (.bin .add (.reg 5) (.reg 6)) (.reg 12) ;;
        .assign 6 (.bin .add (.reg 6) (.const 1)))
       .nop ;;
     .assign 11 (.bin .add (.reg 11) (.const 1)))

lemma compExpRootsStmt_noRand : compExpRootsStmt.NoRand := by
  simp [compExpRootsStmt, Stmt.NoRand]

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compExpRootsStmt`: writes `vL.filter (· ∈ (S j).RF.R)` at `rootsPtr`,
sets `reg 6 = roots.length = (S j).RF.R.card`, preserves memory outside `[rootsPtr, rootsPtr + nR)`,
and runs in `≤ 80 * n + 40` steps. -/
theorem compExpRoots_runs {W : LSFWindowImpl} {w k b vPtr rootsPtr : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k} {vL : List ℕ}
    {st : State} {ω : ℕ → Bool} (j : Fin k)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepAt W k b S x st.mem)
    (hvL_nd : vL.Nodup) (hvL_mem : ∀ v, v ∈ vL ↔ v ∈ (S j).G.V)
    (hvL_at : ListAt st.mem vPtr vL)
    (hend_le : x.endAddr ≤ rootsPtr)
    (hv_disj : vPtr + vL.length ≤ rootsPtr)
    (hr_w : rootsPtr + vL.length < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = j.1) (hr2 : st.regs 2 = k)
    (hr3 : st.regs 3 = vPtr) (hr4 : st.regs 4 = vL.length) (hr5 : st.regs 5 = rootsPtr) :
    let roots := vL.filter fun v => decide (v ∈ (S j).RF.R)
    ∃ st' c,
      Runs w p ω compExpRootsStmt st .normal st' c ∧
      (∀ r < 6, st'.regs r = st.regs r) ∧
      st'.regs 6 = roots.length ∧
      roots.Nodup ∧ roots.toFinset = (S j).RF.R ∧ roots.length = (S j).RF.R.card ∧
      roots.length ≤ vL.length ∧
      ListAt st'.mem rootsPtr roots ∧
      (∀ a, a < rootsPtr ∨ rootsPtr + roots.length ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 80 * vL.length + 40 := by
  intro roots
  obtain ⟨hk, _, _, _, _, _, _, hnumC, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩, hm0Tot, hT,
    hCompMeta, _, hVComp, _, _, _, _, _, hWins, _⟩ := hrep
  have hS_G := (hBr j).2.2.1
  have hS_G0 := (hBr j).2.1
  have hIj := (hBr j).1
  have hI0 := (hBr ⟨0, hk⟩).1
  have hb_hdr_lt : b + compHdrSize ≤ x.endAddr := by
    have : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := by omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_lt hoff; omega
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  -- Prefix (6 assigns)
  let s1 : State := { st with regs := Function.update st.regs 6 0 }
  let s2 : State := { s1 with regs := Function.update s1.regs 7 (compVCompBase b) }
  let s3 : State := { s2 with regs := Function.update s2.regs 8 (compEdgefulBase b x.vCap) }
  let s4 : State := { s3 with regs := Function.update s3.regs 9 (compEdgefulIdxBase b x.vCap) }
  let s5 : State := { s4 with regs := Function.update s4.regs 10 (compHandlesBase b x.vCap x.eCap x.L_w) }
  let s6 : State := { s5 with regs := Function.update s5.regs 11 0 }
  have hp1 : Runs w p ω (.assign 6 (.const 0)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const compOffVCompPtr)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨compVCompBase b, Expr.eval_load_of_eq (by
      have := hb_off compOffVCompPtr (by decide); simp [s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨compEdgefulBase b x.vCap, Expr.eval_load_of_eq (by
      have := hb_off compOffEdgefulPtr (by decide); simp [s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨compEdgefulIdxBase b x.vCap, Expr.eval_load_of_eq (by
      have := hb_off compOffEdgefulIdxPtr (by decide); simp [s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨compHandlesBase b x.vCap x.eCap x.L_w, Expr.eval_load_of_eq (by
      have := hb_off compOffHandlesPtr (by decide); simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 11 (.const 0)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Loop over `rem = vL.length - i`
  have hloop : ∀ rem i (s : State), i ≤ vL.length → vL.length - i = rem →
      let pref := (vL.take i).filter fun v => decide (v ∈ (S j).RF.R)
      (∀ r < 6, s.regs r = st.regs r) →
      s.regs 6 = pref.length →
      s.regs 7 = compVCompBase b → s.regs 8 = compEdgefulBase b x.vCap →
      s.regs 9 = compEdgefulIdxBase b x.vCap → s.regs 10 = compHandlesBase b x.vCap x.eCap x.L_w →
      s.regs 11 = i →
      ListAt s.mem rootsPtr pref →
      (∀ a, a < rootsPtr ∨ rootsPtr + pref.length ≤ a → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 11) (.reg 4))
            (.assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
             .assign 13 (.load (.bin .add (.reg 7) (.reg 12))) ;;
             .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
             .cond (.reg 14)
               (.assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;
                .assign 14 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 14) (.reg 2)) (.reg 1)))) ;;
                .assign 14 (.load (.bin .add (.reg 14) (.const lsfOffFAncPtr))) ;;
                .assign 14 (.load (.bin .add (.reg 14) (.const fOffIsRootPtr))) ;;
                .assign 14 (.load (.bin .add (.reg 14) (.reg 12))))
               (.assign 14 (.const 1)) ;;
             .cond (.reg 14)
               (.store (.bin .add (.reg 5) (.reg 6)) (.reg 12) ;;
                .assign 6 (.bin .add (.reg 6) (.const 1)))
               .nop ;;
             .assign 11 (.bin .add (.reg 11) (.const 1))))
          s .normal st' c ∧
        (∀ r < 6, st'.regs r = st.regs r) ∧
        st'.regs 6 = roots.length ∧
        ListAt st'.mem rootsPtr roots ∧
        (∀ a, a < rootsPtr ∨ rootsPtr + roots.length ≤ a → st'.mem a = st.mem a) ∧
        c ≤ 80 * rem + 5 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem pref hr_lt hr6 _ _ _ _ hr11 hLA hfr
      have hi_eq : i = vL.length := by omega
      subst hi_eq
      have hpref_eq : pref = roots := by simp [pref, roots]
      rw [hpref_eq] at hr6 hLA hfr
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr11, hr_lt 4 (by omega), hr4],
        rfl, rfl, by simp [Expr.size]⟩), hr_lt, hr6, hLA, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem pref hr_lt hr6 hr7 hr8 hr9 hr10 hr11 hLA hfr
      have hi_lt : i < vL.length := by omega
      set v := vL[i]
      have hv_mem0 : v ∈ (S ⟨0, hk⟩).G.V := hS_G ▸ (hvL_mem v).mp (List.getElem_mem hi_lt)
      obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp (hI0.hV_eq ▸ hv_mem0)
      obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
      have hv_lt : v < x.vCap := hT.hVlt v hv_mem0
      have hc_lt : c.1 < x.vCap := lt_of_lt_of_le c.2 hnumC
      have hpref_le : pref.length ≤ i := le_trans (List.length_filter_le _ _) (by simp)
      have hs_v : s.mem (vPtr + i) = v := (hfr _ (Or.inl (by omega))).trans (hvL_at i hi_lt)
      have hs_vc : s.mem (compVCompBase b + v) = c.1 :=
        (hfr _ (Or.inl (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize] at hTE ⊢; omega))).trans (hVComp c v hvC)
      set efFlag := if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then 1 else 0
      have hs_ef : s.mem (compEdgefulBase b x.vCap + c.1) = efFlag :=
        (hfr _ (Or.inl (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase, compHdrSize] at hTE ⊢; omega))).trans (hCompMeta c).1
      let t1 : State := { s with regs := Function.update s.regs 12 v }
      let t2 : State := { t1 with regs := Function.update t1.regs 13 c.1 }
      let t3 : State := { t2 with regs := Function.update t2.regs 14 efFlag }
      have ht1 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 3) (.reg 11)))) s .normal t1 5 :=
        runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr_lt 3 (by omega), hr3, hr11,
          show vPtr + i < 2 ^ w by omega]) hs_v, rfl, rfl, by simp [Expr.size]⟩
      have ht2 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 7) (.reg 12)))) t1 .normal t2 5 :=
        runs_assign_iff.mpr ⟨c.1, Expr.eval_load_of_eq (by
          have : compVCompBase b + v < 2 ^ w := by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize] at hte_w ⊢; omega
          simp [t1, Expr.eval, BinOp.eval, hr7, this]) hs_vc, rfl, rfl, by simp [Expr.size]⟩
      have ht3 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 8) (.reg 13)))) t2 .normal t3 5 :=
        runs_assign_iff.mpr ⟨efFlag, Expr.eval_load_of_eq (by
          have : compEdgefulBase b x.vCap + c.1 < 2 ^ w := by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase, compHdrSize] at hte_w ⊢; omega
          simp [t2, t1, Expr.eval, BinOp.eval, hr8, this]) hs_ef, rfl, rfl, by simp [Expr.size]⟩
      -- Determine `isRootFlag = if v ∈ (S j).RF.R then 1 else 0`
      set isR := if v ∈ (S j).RF.R then 1 else 0
      have hv_in_R_iff : v ∈ (S j).RF.R ↔ v ∈ ((S j).compSt (x.compOf c)).RF.R := by
        simp only [CompLSFState.RF, LSFState.RF, Finset.mem_biUnion, hS_G0]
        constructor
        · rintro ⟨D, hD, hvD⟩
          have hInvD := LSFInvWith.toStructInv (hIj.hCompLSF D (hS_G0.symm ▸ hD)).1
          have hvVD : v ∈ ((S j).compSt D).G.V := by
            rcases Finset.mem_union.mp hvD with h1 | h2
            · exact hInvD.hGV_eq ▸ Finset.mem_union_left _
                (upClosure_subset (hldAuxTree_isRootedTree hInvD.hT₀) hInvD.hR₀_sub h1)
            · exact hInvD.hGV_eq ▸ Finset.mem_union_right _ h2
          have hvVC : v ∈ ((S j).compSt (x.compOf c)).G.V := ((hBr j).2.2.2.2.2.2 c).symm ▸ hvC
          have hDC : D = x.compOf c := by
            by_contra hne
            exact Finset.disjoint_left.mp (hIj.hV_disj D (hS_G0.symm ▸ hD) _ (hS_G0.symm ▸ hC) hne) hvVD hvVC
          exact hDC ▸ hvD
        · intro h; exact ⟨x.compOf c, hC, h⟩
      let t4 : State := { t3 with regs := Function.update t3.regs 14 isR }
      have ht4_ex : ∃ c4, Runs w p ω
          (.cond (.reg 14)
            (.assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;
             .assign 14 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 14) (.reg 2)) (.reg 1)))) ;;
             .assign 14 (.load (.bin .add (.reg 14) (.const lsfOffFAncPtr))) ;;
             .assign 14 (.load (.bin .add (.reg 14) (.const fOffIsRootPtr))) ;;
             .assign 14 (.load (.bin .add (.reg 14) (.reg 12))))
            (.assign 14 (.const 1))) t3 .normal t4 c4 ∧ c4 ≤ 36 := by
        by_cases hpos : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m
        · have hef1 : efFlag = 1 := ite_eq_left hpos
          obtain ⟨ec, _, hmi, hcomp⟩ := (hCompMeta c).2.2.2 hpos
          obtain ⟨hslot, hWrep, hvW, _, _, hWge, hWle⟩ := hWins ec j
          set hWin := x.winHandle ec j
          set xWin := x.winConc ec j
          set fAncPtr := lsfFAncPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM
          have hfAnc_hdr := hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
          have hfAnc := hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hisR_ptr : st.mem (fAncPtr + fOffIsRootPtr) = fIsRootBase fAncPtr := hfAnc.2.1
          have hisR_val : st.mem (fIsRootBase fAncPtr + v) = isR := by
            have h1 := hfAnc.2.2.2.2.2.2.2.2.2.2.2.2.1 v (hvW.symm ▸ hv_lt)
            rw [hcomp] at h1; simpa [isR, hv_in_R_iff] using h1
          have hWin_lt : hWin + lsfHdrSize < 2 ^ w := by
            have := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
            dsimp only [LSFConcrete.endAddr] at hWle; omega
          have hfAnc_end : fAncPtr + fAncSize xWin.vCap ≤ x.endAddr := by
            have : fAncPtr + fAncSize xWin.vCap ≤ xWin.endAddr hWin := by
              dsimp only [fAncPtr, LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfFAncPtr,
                lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
            omega
          have h1_lt : compEdgefulIdxBase b x.vCap + c.1 < x.endAddr := by
            have : compEdgefulIdxBase b x.vCap + c.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
              dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase,
                compEdgefulBase, compVCompBase, compHdrSize]; omega
            omega
          have h2_lt : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) < x.endAddr := by
            have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (Nat.succ_le_of_lt (lt_of_lt_of_le ec.2 hnumEf))
            have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
            dsimp only [compTablesEnd] at hTE; omega
          let a1 : State := { t3 with regs := Function.update t3.regs 14 ec.1 }
          let a2 : State := { a1 with regs := Function.update a1.regs 14 hWin }
          let a3 : State := { a2 with regs := Function.update a2.regs 14 fAncPtr }
          let a4 : State := { a3 with regs := Function.update a3.regs 14 (fIsRootBase fAncPtr) }
          have ha1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 9) (.reg 13)))) t3 .normal a1 5 :=
            runs_assign_iff.mpr ⟨ec.1, Expr.eval_load_of_eq (by simp [t3, t2, t1, Expr.eval, BinOp.eval, hr9,
              show compEdgefulIdxBase b x.vCap + c.1 < 2 ^ w by omega]) ((hfr _ (Or.inl (by omega))).trans hmi),
              rfl, rfl, by simp [Expr.size]⟩
          have ha2 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 14) (.reg 2)) (.reg 1))))) a1 .normal a2 9 :=
            runs_assign_iff.mpr ⟨hWin, Expr.eval_load_of_eq (by
              have h1 : ec.1 * k < 2 ^ w := by omega
              have h2 : ec.1 * k + j.1 < 2 ^ w := by omega
              have h3 : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) < 2 ^ w := by omega
              simp [a1, t3, t2, t1, Expr.eval, BinOp.eval, hr10, hr_lt 2 (by omega), hr2, hr_lt 1 (by omega), hr1, h1, h2, h3])
              ((hfr _ (Or.inl (by omega))).trans hslot), rfl, rfl, by simp [Expr.size]⟩
          have ha3 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 14) (.const lsfOffFAncPtr)))) a2 .normal a3 5 :=
            runs_assign_iff.mpr ⟨fAncPtr, Expr.eval_load_of_eq (by
              have : lsfOffFAncPtr < 2 ^ w ∧ hWin + lsfOffFAncPtr < 2 ^ w := by dsimp only [lsfOffFAncPtr, lsfHdrSize] at hWin_lt ⊢; omega
              simp [a2, Expr.eval, BinOp.eval, this.1, this.2])
              ((hfr _ (Or.inl (by
                have := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
                dsimp only [lsfOffFAncPtr, lsfHdrSize, LSFConcrete.endAddr] at this hWle ⊢; omega))).trans hfAnc_hdr),
              rfl, rfl, by simp [Expr.size]⟩
          have ha4 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 14) (.const fOffIsRootPtr)))) a3 .normal a4 5 :=
            runs_assign_iff.mpr ⟨fIsRootBase fAncPtr, Expr.eval_load_of_eq (by
              have : fOffIsRootPtr < 2 ^ w ∧ fAncPtr + fOffIsRootPtr < 2 ^ w := by
                dsimp only [fOffIsRootPtr, fAncSize, fAncHdrSize] at hfAnc_end ⊢; omega
              simp [a3, Expr.eval, BinOp.eval, this.1, this.2])
              ((hfr _ (Or.inl (by dsimp only [fOffIsRootPtr, fAncSize, fAncHdrSize] at hfAnc_end ⊢; omega))).trans hisR_ptr),
              rfl, rfl, by simp [Expr.size]⟩
          have ha5 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 14) (.reg 12)))) a4 .normal t4 5 :=
            runs_assign_iff.mpr ⟨isR, Expr.eval_load_of_eq (by
              have : fIsRootBase fAncPtr + v < 2 ^ w := by
                dsimp only [fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_end ⊢; omega
              simp [a4, a3, a2, a1, t3, t2, t1, Expr.eval, BinOp.eval, this])
              ((hfr _ (Or.inl (by dsimp only [fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_end ⊢; omega))).trans hisR_val),
              rfl, by simp [t4, a4, a3, a2, a1], by simp [Expr.size]⟩
          have hth : Runs w p ω _ t3 .normal t4 33 :=
            runs_seq_iff.mpr (Or.inr ⟨a1, 5, _, ha1, runs_seq_iff.mpr (Or.inr ⟨a2, 9, _, ha2,
              runs_seq_iff.mpr (Or.inr ⟨a3, 5, _, ha3, runs_seq_iff.mpr (Or.inr ⟨a4, 5, 5, ha4, ha5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
          exact ⟨35, runs_cond_iff.mpr ⟨1, 33, by simp [t3, Expr.eval, hef1], by simpa using hth, by simp [Expr.size]⟩, by omega⟩
        · have hef0 : efFlag = 0 := ite_eq_right hpos
          have hm0 : (compGraph (S j).G₀ (x.compOf c)).m = 0 := by rw [hS_G0]; omega
          have hiso := isoComp_props hIj (hS_G0.symm ▸ hC) hm0
          have hvR : v ∈ (S j).RF.R := hv_in_R_iff.mpr (by
            change v ∈ ((S j).compSt (x.compOf c)).R; rw [hiso.2.1]; exact ((hBr j).2.2.2.2.2.2 c).symm ▸ hvC)
          have hisR1 : isR = 1 := ite_eq_left hvR
          have hel : Runs w p ω (.assign 14 (.const 1)) t3 .normal t4 2 :=
            runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, by simp [t4, hisR1], by simp [Expr.size]⟩
          exact ⟨4, runs_cond_iff.mpr ⟨0, 2, by simp [t3, Expr.eval, hef0], by simpa using hel, by simp [Expr.size]⟩, by omega⟩
      obtain ⟨c4, ht4, hc4⟩ := ht4_ex
      -- Conditional append of `v` into `rootsPtr + pref.length`
      set pref' := (vL.take (i + 1)).filter fun u => decide (u ∈ (S j).RF.R)
      have hpref'_eq : pref' = if v ∈ (S j).RF.R then pref ++ [v] else pref := by
        dsimp only [pref', pref]; rw [List.take_add_one, List.getElem?_eq_getElem hi_lt, Option.toList_some,
          List.filter_append, List.filter_cons, List.filter_nil]
        by_cases hvR : v ∈ (S j).RF.R <;> simp [hvR, v]
      have ht5_ex : ∃ t5 c5,
          Runs w p ω
            (.cond (.reg 14) (.store (.bin .add (.reg 5) (.reg 6)) (.reg 12) ;; .assign 6 (.bin .add (.reg 6) (.const 1))) .nop)
            t4 .normal t5 c5 ∧
          (∀ r < 6, t5.regs r = st.regs r) ∧
          t5.regs 6 = pref'.length ∧ t5.regs 7 = compVCompBase b ∧
          t5.regs 8 = compEdgefulBase b x.vCap ∧ t5.regs 9 = compEdgefulIdxBase b x.vCap ∧
          t5.regs 10 = compHandlesBase b x.vCap x.eCap x.L_w ∧ t5.regs 11 = i ∧
          ListAt t5.mem rootsPtr pref' ∧
          (∀ a, a < rootsPtr ∨ rootsPtr + pref'.length ≤ a → t5.mem a = st.mem a) ∧ c5 ≤ 15 := by
        by_cases hvR : v ∈ (S j).RF.R
        · have hisR1 : isR = 1 := ite_eq_left hvR
          have hp'_eq : pref' = pref ++ [v] := by rw [hpref'_eq, ite_eq_left hvR]
          let u1 : State := { t4 with mem := Function.update t4.mem (rootsPtr + pref.length) v }
          let u2 : State := { u1 with regs := Function.update u1.regs 6 (pref.length + 1) }
          have hu1 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 6)) (.reg 12)) t4 .normal u1 5 :=
            runs_store_iff.mpr ⟨rootsPtr + pref.length, v,
              by simp [t4, t3, t2, t1, Expr.eval, BinOp.eval, hr_lt 5 (by omega), hr5, hr6, show rootsPtr + pref.length < 2 ^ w by omega],
              by simp [t4, t3, t2, t1, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
          have hu2 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1))) u1 .normal u2 4 :=
            runs_assign_iff.mpr ⟨pref.length + 1, by simp [u1, t4, t3, t2, t1, Expr.eval, BinOp.eval, hr6, hw1,
              show pref.length + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
          have hth : Runs w p ω _ t4 .normal u2 10 := runs_seq_iff.mpr (Or.inr ⟨u1, 5, 4, hu1, hu2, rfl⟩)
          refine ⟨u2, 12, runs_cond_iff.mpr ⟨1, 10, by simp [t4, Expr.eval, hisR1], by simpa using hth, by simp [Expr.size]⟩,
            fun r hr => by simp [u2, u1, t4, t3, t2, t1, show r ≠ 6 by omega, show r ≠ 12 by omega, show r ≠ 13 by omega, show r ≠ 14 by omega, hr_lt r hr],
            by simp [u2, hp'_eq], by simp [u2, u1, t4, t3, t2, t1, hr7], by simp [u2, u1, t4, t3, t2, t1, hr8],
            by simp [u2, u1, t4, t3, t2, t1, hr9], by simp [u2, u1, t4, t3, t2, t1, hr10],
            by simp [u2, u1, t4, t3, t2, t1, hr11], ?_, ?_, by omega⟩
          · have hLA_app : ListAt u2.mem rootsPtr (pref ++ [v]) := fun q hq => by
              by_cases hql : q < pref.length
              · rw [List.getElem_append_left hql]; dsimp only [u2, u1, t4, t3, t2, t1]
                rw [Function.update_of_ne (by omega)]; exact hLA q hql
              · have hq_eq : q = pref.length := by simp at hq; omega
                subst hq_eq; simp [u2, u1]
            exact hp'_eq.symm ▸ hLA_app
          · intro a ha; rw [hp'_eq, List.length_append] at ha; dsimp only [u2, u1, t4, t3, t2, t1]
            rw [Function.update_of_ne (by simp at ha; omega)]; exact hfr a (by simp at ha; omega)
        · have hisR0 : isR = 0 := ite_eq_right hvR
          have hp'_eq : pref' = pref := by rw [hpref'_eq, ite_eq_right hvR]
          refine ⟨t4, 3, runs_cond_iff.mpr ⟨0, 1, by simp [t4, Expr.eval, hisR0],
            by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
            fun r hr => by simp [t4, t3, t2, t1, show r ≠ 12 by omega, show r ≠ 13 by omega, show r ≠ 14 by omega, hr_lt r hr],
            by simp [t4, t3, t2, t1, hr6, hp'_eq], by simp [t4, t3, t2, t1, hr7],
            by simp [t4, t3, t2, t1, hr8], by simp [t4, t3, t2, t1, hr9],
            by simp [t4, t3, t2, t1, hr10], by simp [t4, t3, t2, t1, hr11],
            hp'_eq ▸ hLA, hp'_eq ▸ hfr, by omega⟩
      obtain ⟨t5, c5, ht5, hr5_lt, hr5_6, hr5_7, hr5_8, hr5_9, hr5_10, hr5_11, hLA5, hfr5, hc5⟩ := ht5_ex
      let t6 : State := { t5 with regs := Function.update t5.regs 11 (i + 1) }
      have ht6 : Runs w p ω (.assign 11 (.bin .add (.reg 11) (.const 1))) t5 .normal t6 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, BinOp.eval, hr5_11, hw1, show i + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal t6 (24 + c4 + c5) :=
        runs_seq_iff.mpr (Or.inr ⟨t1, 5, _, ht1, runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, ht2,
          runs_seq_iff.mpr (Or.inr ⟨t3, 5, _, ht3, runs_seq_iff.mpr (Or.inr ⟨t4, c4, _, ht4,
          runs_seq_iff.mpr (Or.inr ⟨t5, c5, 4, ht5, ht6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
      obtain ⟨st', cRest, hrest, hr'_lt, hr'_6, hLA', hfr', hcRest⟩ :=
        ih (i + 1) t6 (by omega) (by omega) (fun r hr => by simp [t6, show r ≠ 11 by omega, hr5_lt r hr])
          (by simpa [t6, pref'] using hr5_6) (by simp [t6, hr5_7]) (by simp [t6, hr5_8]) (by simp [t6, hr5_9])
          (by simp [t6, hr5_10]) (by simp [t6]) hLA5 hfr5
      have hfull : Runs w p ω
          (.loop (.bin .lt (.reg 11) (.reg 4))
            (.assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
             .assign 13 (.load (.bin .add (.reg 7) (.reg 12))) ;;
             .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
             .cond (.reg 14)
               (.assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;
                .assign 14 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 14) (.reg 2)) (.reg 1)))) ;;
                .assign 14 (.load (.bin .add (.reg 14) (.const lsfOffFAncPtr))) ;;
                .assign 14 (.load (.bin .add (.reg 14) (.const fOffIsRootPtr))) ;;
                .assign 14 (.load (.bin .add (.reg 14) (.reg 12))))
               (.assign 14 (.const 1)) ;;
             .cond (.reg 14)
               (.store (.bin .add (.reg 5) (.reg 6)) (.reg 12) ;;
                .assign 6 (.bin .add (.reg 6) (.const 1)))
               .nop ;;
             .assign 11 (.bin .add (.reg 11) (.const 1)))) s .normal st' (24 + c4 + c5 + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, t6, 24 + c4 + c5, cRest,
          by simp [Expr.eval, BinOp.eval, hr11, hr_lt 4 (by omega), hr4, hi_lt, hw0], by decide,
          hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 24 + c4 + c5 + cRest + 4, hfull, hr'_lt, hr'_6, hLA', hfr', by omega⟩
  obtain ⟨st', cL, hrunL, hr'_lt, hr'_6, hLA', hfr', hcL⟩ :=
    hloop vL.length 0 s6 (Nat.zero_le _) (Nat.sub_zero _)
      (fun r hr => by simp [s6, s5, s4, s3, s2, s1, show r ≠ 6 by omega, show r ≠ 7 by omega, show r ≠ 8 by omega, show r ≠ 9 by omega, show r ≠ 10 by omega, show r ≠ 11 by omega])
      (by simp [s6, s5, s4, s3, s2, s1]) (by simp [s6, s5, s4, s3, s2]) (by simp [s6, s5, s4, s3])
      (by simp [s6, s5, s4]) (by simp [s6, s5]) (by simp [s6]) (fun _ hi => by simp at hi) (fun _ _ => rfl)
  have hrun_all : Runs w p ω compExpRootsStmt st .normal st' (30 + cL) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, hp1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hp2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, hp3, runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, hp4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, hp5, runs_seq_iff.mpr (Or.inr ⟨s6, 2, cL, hp6, hrunL, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  have hnd : roots.Nodup := hvL_nd.filter _
  have hfin : roots.toFinset = (S j).RF.R := by
    ext v; simp only [roots, List.mem_toFinset, List.mem_filter, hvL_mem, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨(compLSF_RF_isRSF hIj).2.2.1 h, h⟩⟩
  have hcard : roots.length = (S j).RF.R.card := by
    rw [← hfin, List.toFinset_card_of_nodup hnd]
  exact ⟨st', 30 + cL, hrun_all, hr'_lt, hr'_6, hnd, hfin, hcard, List.length_filter_le _ _, hLA', hfr', by omega⟩

end

end MinCostFlow.SparseCore.Program
