module

public import MinCostFlow.LSF.Program.DecompClosureMath
public import MinCostFlow.LSF.Program.DecompMark
public import MinCostFlow.LSF.Program.DecompLabel
public import MinCostFlow.LSF.Program.DecompDegSpec
public import MinCostFlow.LSF.Program.DecompGenBoundary
public import MinCostFlow.LSF.Program.DecompGenRec

/-!
# The decomposition `W_T` from the five passes

The decomposition of `T₀` is computed by five passes over the vertex indices: the degree pass
(`decompDegProc`), the greedy pass (`decompGreedyProc`), the label pass (`decompLabelProc`), the
mark pass (`decompMarkProc`) and the closure pass (`decompClosureProc`). `wT_spec` collects what
their contracts give into three facts about one decomposition `W` of `T₀`:
* `W` satisfies `IsTreeDecompSpec` (Lemma B.7);
* the closure pass marks exactly the boundary of `W`;
* two tree edges have the same label exactly when one piece of `W` holds both.

The decomposition is `finalDecomp` of the bottom-up decomposition `progDecomp` for the child
lists of the greedy pass (`greedyChildLists`).
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program.DecompGen

/-- The label of a vertex, from the label arrays on indices. -/
def labV (vList : List ℕ) (labY labB : ℕ → ℕ) (v : ℕ) : ℕ × ℕ :=
  (vList.getD (labY (vList.idxOf v)) 0, labB (vList.idxOf v))

/-- The labels point to indices: `labY x < n`. -/
lemma labY_lt {n tM r : ℕ} {tl hd par pe dep nb bidx labY labB : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep)
    (hlab : ∀ x < n, x ≠ r → LabelRule par nb bidx labY labB r x) :
    ∀ d x, x < n → x ≠ r → dep x ≤ d → labY x < n := by
  intro d
  induction d with
  | zero =>
    intro x hx hxr hd
    have := (hR.step x hx hxr).2.2
    omega
  | succ d ih =>
    intro x hx hxr hd
    have hpx := hR.par_lt x hx
    have hstep := hR.step x hx hxr
    have h := hlab x hx hxr
    unfold LabelRule at h
    split_ifs at h with hc
    · rw [Prod.mk.injEq] at h; rw [h.1]; exact hpx
    · rw [Prod.mk.injEq] at h
      rw [h.1]
      push_neg at hc
      exact ih (par x) hpx hc.2 (by omega)

/-- The labels on vertices satisfy `IsLabeling`. -/
theorem labV_isLabeling {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep nb bidx labY labB : ℕ → ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hlab : ∀ x < vList.length, x ≠ r → LabelRule par nb bidx labY labB r x) :
    IsLabeling T₀ (vList.getD r 0) (vtxFun vList bidx) (vtxFun vList nb) (labV vList labY labB) := by
  intro v hv hvr
  have hvL := (hV v).mp hv
  set x := vList.idxOf v with hx
  have hxn : x < vList.length := List.idxOf_lt_length_of_mem hvL
  have hgx : vList.getD x 0 = v := getD_idxOf hvL
  have hxr : x ≠ r := fun h => hvr (by rw [← hgx, h])
  have hpar : parent T₀ (vList.getD r 0) v = vList.getD (par x) 0 := by
    rw [← hgx]; exact ((t0Rooted_spec hT.isForest hA hnd hR hr hxn).2 hxr).1
  have hpn := hR.par_lt x hxn
  have hip : vList.idxOf (parent T₀ (vList.getD r 0) v) = par x := by
    rw [hpar, idxOf_getD hnd hpn]
  have hpr : parent T₀ (vList.getD r 0) v = vList.getD r 0 ↔ par x = r := by
    rw [hpar]
    exact ⟨getD_inj hnd hpn hr, fun h => by rw [h]⟩
  have h := hlab x hxn hxr
  unfold LabelRule at h
  simp only [labV, vtxFun, hip, ← hx]
  by_cases hc : bidx x < nb (par x) ∨ par x = r
  · rw [ite_eq_left (hc.imp_right hpr.mpr)]
    rw [ite_eq_left hc, Prod.mk.injEq] at h
    rw [Prod.mk.injEq]
    exact ⟨by rw [h.1, hpar], h.2⟩
  · rw [ite_eq_right (fun h' => hc (h'.imp_right hpr.mp))]
    rw [ite_eq_right hc, Prod.mk.injEq] at h
    rw [Prod.mk.injEq]
    exact ⟨by rw [h.1], h.2⟩

/-- What the five passes give: one decomposition `W` of `T₀` with Lemma B.7, its boundary (the
closure pass), and its pieces (the labels). -/
theorem wT_spec {G₀ T₀ : MGraph} {vList : List ℕ} {tM r k : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ} {Q : List ℕ}
    {deg ν cur nb bidx s labY labB S cnt has inR : ℕ → ℕ}
    (hG₀ : G₀.IsValid) (hTV : T₀.V = G₀.V) (hV2 : 2 ≤ G₀.V.card) (hE : G₀.E.Nonempty)
    (hk : 0 < k)
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hQ : TopDownOrder vList.length r par Q)
    (hdeg : ∀ x < vList.length, (deg x : ℝ) = vWeight G₀ (fun _ => 1) (vList.getD x 0))
    (hν : ∀ x < vList.length, ν x = degNu (decompThetaNat G₀ k) (deg x))
    (hG : GreedyState Q par vList.length (decompThetaNat G₀ k) ν cur nb bidx s 1)
    (hlab : ∀ x < vList.length, x ≠ r → LabelRule par nb bidx labY labB r x)
    (hS : ∀ x < vList.length, x ≠ r → S x = markVal (decompThetaNat G₀ k) (nb x) (deg x))
    (hSr : S r = rootMarkVal (decompThetaNat G₀ k) (nb r) (deg r)
      (rootFlag par bidx nb r vList.length))
    (hC : ClosureState Q par vList.length S cnt has inR 1)
    (hCr : inR r = closureIn (S r) (cnt r)) :
    let νR := decompNu G₀ (fun _ => 1) (decompParam G₀ (k : ℝ))
    let θR := decompTheta G₀ (fun _ => 1) (decompParam G₀ (k : ℝ))
    let L := greedyChildLists vList Q par
    let W := finalDecomp G₀ (fun _ => 1) (decompParam G₀ (k : ℝ)) T₀ (vList.getD r 0)
      (progDecomp νR θR L T₀.V.card (vList.getD r 0)).1
      (progDecomp νR θR L T₀.V.card (vList.getD r 0)).2
    IsTreeDecompSpec G₀ T₀ k W ∧
    (∀ v ∈ T₀.V, vtxFun vList inR v = 1 ↔ v ∈ boundary W) ∧
    (∀ x < vList.length, x ≠ r → ∀ x' < vList.length, x' ≠ r →
      ((labY x = labY x' ∧ labB x = labB x') ↔ ∃ P ∈ W,
        parentEdge T₀ (vList.getD r 0) (vList.getD x 0) ∈ inducedEdges T₀ P ∧
        parentEdge T₀ (vList.getD r 0) (vList.getD x' 0) ∈ inducedEdges T₀ P)) := by
  classical
  intro νR θR L W
  set n := vList.length with hn_def
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  set r₀ := vList.getD r 0 with hr₀
  set θ := decompThetaNat G₀ k with hθdef
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hθ : θR = (θ : ℝ) := decompTheta_eq hE k
  have hgV : ∀ x < n, g x ∈ T₀.V := fun x hx =>
    (hV _).mpr (by simp only [hg]; rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _)
  have hidx : ∀ v ∈ T₀.V, vList.idxOf v < n ∧ g (vList.idxOf v) = v := fun v hv =>
    ⟨List.idxOf_lt_length_of_mem ((hV v).mp hv), getD_idxOf ((hV v).mp hv)⟩
  have hνR : ∀ x < n, νR (g x) = (ν x : ℝ) := by
    intro x hx
    rw [hν x hx]
    exact (degNu_eq_decompNu hE k (hTV ▸ hgV x hx) (hdeg x hx)).symm
  obtain ⟨hL, hrun0⟩ := greedy_bridge hT hA hnd hV hR hr hQ hG νR hνR
  set sV : ℕ → ℝ := fun v => νR v + (vtxFun vList cur v : ℝ) with hsV
  have hrun : ∀ u ∈ T₀.V, OnlineRun θR sV (vtxFun vList bidx) 0 0 (L u) (vtxFun vList nb u)
      (sV u - νR u) := by
    rw [hθ]; exact hrun0
  have hspec : IsTreeDecompSpec G₀ T₀ k W :=
    progDecomp_isTreeDecompSpec hG₀ hT hTV hV2 hE hkR hL
  have hlabV := labV_isLabeling hT hA hnd hV hR hr hlab
  refine ⟨hspec, ?_, ?_⟩
  swap
  · -- the labels
    intro x hx hxr x' hx' hx'r
    have hl := (label_spec hT νR θR hL sV hrun hlabV G₀ (fun _ => 1) (decompParam G₀ (k : ℝ))
      hspec.2.1).2
    have hgxr : ∀ y < n, y ≠ r → g y ≠ r₀ := fun y hy hyr h => hyr (getD_inj hnd hy hr h)
    have h1 := hl (g x) (hgV x hx) (hgxr x hx hxr) (g x') (hgV x' hx') (hgxr x' hx' hx'r)
    rw [← h1]
    simp only [labV, hg, idxOf_getD hnd hx, idxOf_getD hnd hx', Prod.mk.injEq]
    have hy1 := labY_lt hR hlab (dep x) x hx hxr le_rfl
    have hy2 := labY_lt hR hlab (dep x') x' hx' hx'r le_rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rw [h1], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨getD_inj hnd hy1 hy2 h1, h2⟩
  · -- the boundary
    have hw : ∀ e ∈ G₀.E, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) e := fun _ _ => zero_le_one
    have hθpos : 0 < θR := by
      have hm : (0 : ℝ) < (G₀.E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE)
      have hp := decompParam_pos (G₀ := G₀) hkR
      simp only [θR, decompTheta, Finset.sum_const, nsmul_eq_mul, mul_one]
      positivity
    have hνnn : ∀ v ∈ T₀.V, 0 ≤ νR v := by
      intro v _
      simp only [νR, decompNu]
      split_ifs
      · exact le_rfl
      · exact vWeight_nonneg hw v
    have hνle : ∀ v ∈ T₀.V, νR v ≤ θR := by
      intro v hv
      show (if v ∈ decompHeavy G₀ (fun _ => 1) (decompParam G₀ (k : ℝ)) then 0
        else vWeight G₀ (fun _ => 1) v) ≤ decompTheta G₀ (fun _ => 1) (decompParam G₀ (k : ℝ))
      split_ifs with hvH
      · exact le_of_lt hθpos
      · rw [decompHeavy, Finset.mem_filter] at hvH
        by_contra hlt
        exact hvH ⟨hTV ▸ hv, lt_of_not_ge hlt⟩
    have hroot : (subtree T₀ r₀ r₀).card ≤ T₀.V.card :=
      Finset.card_le_card (fun _ hx => (mem_subtree_iff.mp hx).1)
    have hgood := progDecomp_good hT νR hνnn θR hθpos hνle hL _ r₀ hT.2 hroot
    have hpos : (0 : ℝ) < ∑ e ∈ G₀.E, (fun _ => (1 : ℝ)) e := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr hE)
    have hb := (b7Props_of_good hG₀ hT hTV hV2 (fun _ => 1) hw (decompParam G₀ (k : ℝ))
      (decompParam_pos hkR) hpos hgood).2
    set D := progDecomp νR θR L T₀.V.card r₀ with hD
    have hWb : boundary W = lcaClosure T₀ r₀ (boundary (rootPieces r₀ D.1 D.2) ∪
        decompHeavy G₀ (fun _ => 1) (decompParam G₀ (k : ℝ))) := hb
    -- the children of the root, on indices
    have hrootchild : (∃ c ∈ childSet T₀ r₀ r₀, vtxFun vList bidx c = vtxFun vList nb r₀) ↔
        0 < rootFlag par bidx nb r n := by
      have hir : vList.idxOf r₀ = r := idxOf_getD hnd hr
      unfold rootFlag
      constructor
      · rintro ⟨c, hc, hbc⟩
        obtain ⟨hcV, hcr, hpc⟩ := (mem_childSet_iff hT).mp hc
        obtain ⟨hyn, hgy⟩ := hidx c hcV
        have hyr : vList.idxOf c ≠ r := fun h => hcr (by rw [← hgy, h])
        have hpy : par (vList.idxOf c) = r := by
          have h1 := ((t0Rooted_spec hT.isForest hA hnd hR hr hyn).2 hyr).1
          have hgy' : vList.getD (vList.idxOf c) 0 = c := hgy
          rw [hgy', hpc] at h1
          exact getD_inj hnd (hR.par_lt _ hyn) hr h1.symm
        rw [ite_eq_left ⟨vList.idxOf c, hyn, hyr, hpy, by
          simp only [vtxFun, hir] at hbc; exact hbc⟩]
        omega
      · intro hf
        by_contra hno
        rw [ite_eq_right ?_] at hf
        · omega
        rintro ⟨y, hyn, hyr, hpy, hby⟩
        apply hno
        refine ⟨g y, (mem_childSet_iff hT).mpr ⟨hgV y hyn, fun h => hyr (getD_inj hnd hyn hr h),
          ?_⟩, ?_⟩
        · rw [((t0Rooted_spec hT.isForest hA hnd hR hr hyn).2 hyr).1, hpy]
        · simp only [vtxFun, hg, idxOf_getD hnd hyn, hir]; exact hby
    have hset : boundary (rootPieces r₀ D.1 D.2) ∪
        decompHeavy G₀ (fun _ => 1) (decompParam G₀ (k : ℝ)) =
        T₀.V.filter (fun v => 0 < vtxFun vList S v) := by
      have hchar : ∀ v ∈ T₀.V, (v ∈ boundary (rootPieces r₀ D.1 D.2) ∨
          v ∈ decompHeavy G₀ (fun _ => 1) (decompParam G₀ (k : ℝ))) ↔ 0 < vtxFun vList S v := by
        intro v hv
        obtain ⟨hxn, hgx⟩ := hidx v hv
        have hdv := hdeg _ hxn
        rw [show vList.getD (vList.idxOf v) 0 = v from hgx] at hdv
        have hheavy : v ∈ decompHeavy G₀ (fun _ => 1) (decompParam G₀ (k : ℝ)) ↔
            θ < deg (vList.idxOf v) := by
          rw [decompHeavy, Finset.mem_filter, ← hdv]
          change _ ∧ θR < _ ↔ _
          rw [hθ, Nat.cast_lt]
          exact ⟨fun h => h.2, fun h => ⟨hTV ▸ hv, h⟩⟩
        rw [boundary_rootPieces hT hL hrun hlabV hv, hheavy, hrootchild]
        by_cases hvr : v = r₀
        · subst hvr
          have hir : vList.idxOf r₀ = r := idxOf_getD hnd hr
          simp only [vtxFun, hir, hSr, rootMarkVal]
          split_ifs with hc <;> simp_all <;> omega
        · have hxr : vList.idxOf v ≠ r := fun h => hvr (by rw [← hgx, h])
          simp only [vtxFun]
          rw [hS _ hxn hxr, markVal]
          simp only [hvr, false_and, or_false, ne_eq, not_false_eq_true, true_and]
          split_ifs with hc <;> omega
      ext v
      rw [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hvB
        have hvV : v ∈ T₀.V := by
          rcases hvB with hvB | hvB
          · have hvU := (Finset.mem_filter.mp hvB).1
            obtain ⟨P, hP, hvP⟩ := Finset.mem_biUnion.mp hvU
            have hPsub : P ⊆ subtree T₀ r₀ r₀ := by
              unfold rootPieces at hP
              split_ifs at hP
              · exact (hgood.2.2.2.2.1 P hP).2.1
              · rcases Finset.mem_insert.mp hP with rfl | hP
                · exact hgood.2.2.1
                · exact (hgood.2.2.2.2.1 P hP).2.1
            exact (mem_subtree_iff.mp (hPsub hvP)).1
          · rw [hTV]; exact (Finset.mem_filter.mp hvB).1
        exact ⟨hvV, (hchar v hvV).mp hvB⟩
      · rintro ⟨hvV, hvS⟩
        exact (hchar v hvV).mpr hvS
    intro v hv
    rw [hWb, hset]
    exact closure_bridge hT hA hnd hV hR hr hQ hC hCr v hv

end MinCostFlow.LSF.Program

end
