module

public import MinCostFlow.SparseCore.BundleOutBatch
public import MinCostFlow.SparseCore.CanonCoreRelease
import MinCostFlow.LSF.Lemma54Split
import MinCostFlow.SparseCore.CoreModel

/-!
# The canonical core batch is ordered

A batch of the component-wise LSF changes the global core graph by an ordered core batch with
split bound two. This file proves that the canonical core batch
`canonCoreBatch cs U` is such a batch, with one split per new root, at most one deletion per
update, and only deletions of the input (`canonCoreBatch_spec`). So it meets `CoreBatchSpec`.

The proof follows the existence proof, update by update. The input edit of an update gives the
core edit `inputCoreBatch` (`orderedCore_inputCoreBatch`), with the intermediate forest named by
the canonical roots. The released forest edges, taken in increasing order, give `releasesBatch`
(`orderedCore_releasesBatch`). The two concatenate (`orderedCore_canonStepCore`), and the steps
concatenate along the batch.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

private theorem cast_order_eq {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h
  rfl

private theorem batchDeletes_eq_empty_of_countP_eq_zero {U : List Update}
    (h : U.countP deleteTag = 0) : batchDeletes U = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  obtain ⟨u, hu, rfl⟩ := (mem_batchDeletes_iff U e).mp he
  have hpos : 0 < U.countP deleteTag := List.countP_pos_iff.mpr ⟨.delete e, hu, rfl⟩
  omega

private theorem batchDeletes_append (U₁ U₂ : List Update) :
    batchDeletes (U₁ ++ U₂) = batchDeletes U₁ ∪ batchDeletes U₂ := by
  ext e
  simp only [Finset.mem_union, mem_batchDeletes_iff, List.mem_append]
  constructor
  · rintro ⟨u, hu | hu, heq⟩
    · exact Or.inl ⟨u, hu, heq⟩
    · exact Or.inr ⟨u, hu, heq⟩
  · rintro (⟨u, hu, heq⟩ | ⟨u, hu, heq⟩)
    · exact ⟨u, Or.inl hu, heq⟩
    · exact ⟨u, Or.inr hu, heq⟩

/-- A vertex split of the input is the core split `refineSplit` of the root of the split vertex. -/
private theorem orderedCore_split_canon {G : MGraph} {L L' : LSF}
    {v v' fresh β : ℕ} {At Ah : Finset ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.split v v' At Ah)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.split v v' At Ah)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.split v v' At Ah)))
    (hForest : L'.F.F = L.F.F.applyUpdate (.split v v' At Ah))
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R)
    (hu : G.UpdateIsValid (.split v v' At Ah)) (hs : RotationStep β (.split v v' At Ah) ρ σ) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hF')
      [refineSplit (coreGraph G L) (coreGraph (G.applyUpdate (.split v v' At Ah)) L')
        (L.F.root v) fresh] := by
  let H := G.applyUpdate (.split v v' At Ah)
  let P : ℕ → ℕ := fun w => if w = v' then v else w
  let r := L.F.root v
  have hvf : v' ∉ L.F.F.V := fun h => hu.2.1 (hF.2.1 ▸ h)
  have hvG : v ∈ H.V := Finset.mem_insert_of_mem hu.1
  have hvG' : v' ∈ H.V := Finset.mem_insert_self _ _
  have hn : L'.F.root v ≠ L'.F.root v' := by
    intro he
    have hc := connected_of_root_eq hF' hvG hvG' he
    rw [hForest] at hc
    exact applySplit_separates hF.1 (hF.2.1.symm ▸ hu.1) hvf At Ah hc
  have hr (w : ℕ) (hw : w ∈ H.V) (he : P w = v) :
      L'.F.root w = r ∨ L'.F.root w = fresh := by
    obtain ⟨hwR, hc⟩ := root_mem_R hF' hw
    rw [hRoots] at hwR
    rcases Finset.mem_insert.mp hwR with hFresh | hOld
    · exact Or.inr hFresh
    · have htG := hF.2.2.1 hOld
      have hp : P (L'.F.root w) = L'.F.root w := by
        have hne : L'.F.root w ≠ v' := fun h => hu.2.1 (h ▸ htG)
        simp [P, hne]
      rw [hForest] at hc
      have hproj := connected_applySplit_proj hF.1.1 hvf At Ah hc
      change L.F.F.Connected (P w) (P (L'.F.root w)) at hproj
      rw [he, hp] at hproj
      exact Or.inl ((root_eq_of_mem_R hF hOld).symm.trans
        (root_eq_of_connected hF hu.1 htG hproj).symm)
  obtain ⟨side, hk, hm⟩ : ∃ side : Bool,
      L'.F.F.Connected (if side then v else v') r ∧
      L'.F.F.Connected (if side then v' else v) fresh := by
    rcases hr v hvG (by simp [P]) with h₁ | h₁ <;>
      rcases hr v' hvG' (by simp [P]) with h₂ | h₂
    · exact (hn (h₁.trans h₂.symm)).elim
    · exact ⟨true, h₁ ▸ (root_mem_R hF' hvG).2, h₂ ▸ (root_mem_R hF' hvG').2⟩
    · exact ⟨false, h₂ ▸ (root_mem_R hF' hvG').2, h₁ ▸ (root_mem_R hF' hvG).2⟩
    · exact (hn (h₁.trans h₂.symm)).elim
  obtain ⟨hv, he, ho⟩ := coreRotation_vertexSplit side ρ σ hG hH hF hF' hForest
    hRoots hf hk hm hu hs
  exact OrderedCoreBatch.singleton hv he ho

private theorem forestAfterInput_root_sep {G : MGraph} {RF : RootedForest} {u : Update}
    (hF : RF.IsRootedSpanningForestOf G) (hu : G.UpdateIsValid u)
    {a b : ℕ} (ha : a ∈ RF.R) (hb : b ∈ RF.R)
    (hc : (forestAfterInput RF.F u).Connected a b) : a = b := by
  have hconn : RF.F.Connected a b := by
    cases u with
    | insert => exact hc
    | delete e => exact connected_of_subgraph (eraseForestEdge_subgraph _ e) hc
    | split v v' St Sh =>
      have hvf : v' ∉ RF.F.V := fun he => hu.2.1 (hF.2.1 ▸ he)
      have ha' : a ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 ha)
      have hb' : b ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 hb)
      exact by simpa [ha', hb'] using connected_applySplit_proj hF.1.1 hvf St Sh hc
  have hEq := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb) hconn
  rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hEq

/-- The core edit of one input update is ordered, and the LSF after it (`inputMid`) roots the
forest after the input edit with roots between the old and the final ones. This is the
canonical form of the input step of `orderedCore_input`. -/
theorem orderedCore_inputCoreBatch {cs : CompLSFState} {u : Update} {last : LSF} {β : ℕ}
    (ρ : Rotation cs.G) (σ : Rotation (cs.G.applyUpdate u))
    (hG : cs.G.IsValid) (hH : (cs.G.applyUpdate u).IsValid)
    (hF : cs.lsf.F.IsRootedSpanningForestOf cs.G)
    (hlast : last.F.IsRootedSpanningForestOf (cs.G.applyUpdate u))
    (hlastR : last.F.R = (compLSFStepSingle cs u).RF.R)
    (hu : cs.G.UpdateIsValid u) (hs : RotationStep β u ρ σ) (hβ : 2 ≤ β)
    (hR : cs.lsf.F.R ⊆ last.F.R)
    (hK : (forestAfterInput cs.lsf.F.F u).IsForest)
    (hKG : (cs.G.applyUpdate u).IsSubgraph (forestAfterInput cs.lsf.F.F u))
    (hsub : (forestAfterInput cs.lsf.F.F u).IsSubgraph last.F.F) :
    ∃ hm : (inputMid cs u).F.IsRootedSpanningForestOf (cs.G.applyUpdate u),
      (inputMid cs u).F.F = forestAfterInput cs.lsf.F.F u ∧ cs.lsf.F.R ⊆ (inputMid cs u).F.R ∧
      (inputMid cs u).F.R ⊆ last.F.R ∧
      OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hm) (inputCoreBatch cs u) ∧
      (inputCoreBatch cs u).countP deleteTag ≤ 1 ∧
      batchDeletes (inputCoreBatch cs u) ⊆ batchDeletes [u] := by
  have hKV : (forestAfterInput cs.lsf.F.F u).V = (cs.G.applyUpdate u).V := by
    cases u with
    | insert => exact hF.2.1
    | delete => exact hF.2.1
    | split v v' St Sh =>
      change insert v' cs.lsf.F.F.V = insert v' cs.G.V
      rw [hF.2.1]
  have hIntermediate := canonRoots_spec hK hKV hKG hlast hsub hR
    (fun _ ha _ hb hc => forestAfterInput_root_sep hF hu ha hb hc)
  rw [hlastR] at hIntermediate
  cases u with
  | insert e a b =>
    have hm : cs.lsf.F.IsRootedSpanningForestOf (cs.G.applyUpdate (.insert e a b)) :=
      ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hKG⟩
    obtain ⟨he, ho⟩ := coreRotation_insert ρ σ hG hH hF hm hu hs
    let op := Update.insert e (cs.lsf.F.root a) (cs.lsf.F.root b)
    have hv : (coreGraph cs.G cs.lsf).UpdateIsValid op :=
      ⟨fun h => hu.1 (Finset.mem_sdiff.mp h).1, (root_mem_R hF hu.2.1).1,
        (root_mem_R hF hu.2.2).1⟩
    have hdel0 : ([op] : List Update).countP deleteTag = 0 := by simp [op, deleteTag]
    refine ⟨hm, rfl, Finset.Subset.rfl, hR, OrderedCoreBatch.singleton hv he ho,
      by simp [inputCoreBatch, deleteTag], ?_⟩
    change batchDeletes [op] ⊆ _
    rw [batchDeletes_eq_empty_of_countP_eq_zero hdel0]
    exact Finset.empty_subset _
  | delete e =>
    by_cases he : e ∈ cs.lsf.F.F.E
    · obtain ⟨hRo, hRf, hm⟩ := hIntermediate
      let K := forestAfterInput cs.lsf.F.F (.delete e)
      let R := canonRoots K cs.lsf.F.R (compLSFStepSingle cs (.delete e)).RF.R
      let mid : LSF := ⟨cs.lsf.T, ⟨K, R⟩, cs.lsf.wstr⟩
      have hM : inputMid cs (.delete e) = mid := by
        simp only [inputMid, show e ∈ cs.RF.F.E from he, ↓reduceIte]; rfl
      have hB : inputCoreBatch cs (.delete e) =
          [refineSplit (coreGraph cs.G cs.lsf) (coreGraph (cs.G.applyUpdate (.delete e)) mid)
            (cs.lsf.F.root (cs.lsf.F.F.tail e)) (newRoot R cs.lsf.F.R)] := by
        simp only [inputCoreBatch, show e ∈ cs.RF.F.E from he, ↓reduceIte, hM]; rfl
      rw [hB, hM]
      have hm' : mid.F.IsRootedSpanningForestOf (cs.G.applyUpdate (.delete e)) := hm
      have hcount : R.card = cs.lsf.F.R.card + 1 := by
        rw [← rootedForest_components_card hm', ← rootedForest_components_card hF]
        exact forest_eraseEdge_components_card hF.1 he
      obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
      have ho := orderedCore_delete_forest_canon (L' := mid) ρ σ hG hH hF hm' he rfl hR' hnew
        hs hβ
      have hd : ([refineSplit (coreGraph cs.G cs.lsf)
          (coreGraph (cs.G.applyUpdate (.delete e)) mid) (cs.lsf.F.root (cs.lsf.F.F.tail e))
          (newRoot R cs.lsf.F.R)] : List Update).countP deleteTag = 0 := by
        simp [refineSplit, deleteTag]
      refine ⟨hm', rfl, hRo, hlastR ▸ hRf, ?_, by simp [refineSplit, deleteTag], ?_⟩
      · rw [newRoot_eq hR' hnew]
        exact ho
      · rw [batchDeletes_eq_empty_of_countP_eq_zero hd]
        exact Finset.empty_subset _
    · have hK_eq : forestAfterInput cs.lsf.F.F (.delete e) = cs.lsf.F.F := by
        change { cs.lsf.F.F with E := cs.lsf.F.F.E.erase e } = cs.lsf.F.F
        rw [Finset.erase_eq_of_notMem he]
      have hM : inputMid cs (.delete e) = cs.lsf := by
        simp only [inputMid, show e ∉ cs.RF.F.E from he, ↓reduceIte]
      have hB : inputCoreBatch cs (.delete e) = [.delete e] := by
        simp only [inputCoreBatch, show e ∉ cs.RF.F.E from he, ↓reduceIte]
      have hHG : (cs.G.applyUpdate (.delete e)).IsSubgraph cs.lsf.F.F := hK_eq ▸ hKG
      have hm : cs.lsf.F.IsRootedSpanningForestOf (cs.G.applyUpdate (.delete e)) :=
        ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hHG⟩
      obtain ⟨hEq, ho⟩ := coreRotation_delete ρ σ hG hH hF hm he hs
      have hv : (coreGraph cs.G cs.lsf).UpdateIsValid (.delete e) := Finset.mem_sdiff.mpr ⟨hu, he⟩
      rw [hB]
      rw [hM]
      exact ⟨hm, hK_eq.symm, Finset.Subset.rfl, hR, OrderedCoreBatch.singleton hv hEq ho,
        by simp [deleteTag], Finset.Subset.rfl⟩
  | split v v' St Sh =>
    obtain ⟨hRo, hRf, hm⟩ := hIntermediate
    let K := forestAfterInput cs.lsf.F.F (.split v v' St Sh)
    let R := canonRoots K cs.lsf.F.R (compLSFStepSingle cs (.split v v' St Sh)).RF.R
    let mid : LSF := ⟨cs.lsf.T, ⟨K, R⟩, cs.lsf.wstr⟩
    have hM : inputMid cs (.split v v' St Sh) = mid := rfl
    have hB : inputCoreBatch cs (.split v v' St Sh) =
        [refineSplit (coreGraph cs.G cs.lsf) (coreGraph (cs.G.applyUpdate (.split v v' St Sh)) mid)
          (cs.lsf.F.root v) (newRoot R cs.lsf.F.R)] := rfl
    rw [hB, hM]
    have hcount : R.card = cs.lsf.F.R.card + 1 := by
      have ho := rootedForest_R_add_edges hF
      have hn := rootedForest_R_add_edges hm
      have hv : (cs.G.applyUpdate (.split v v' St Sh)).V.card = cs.G.V.card + 1 :=
        Finset.card_insert_of_notMem hu.2.1
      change R.card + cs.lsf.F.F.E.card = (cs.G.applyUpdate (.split v v' St Sh)).V.card at hn
      omega
    obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
    have ho := orderedCore_split_canon (L' := mid) ρ σ hG hH hF hm rfl hR' hnew hu hs
    refine ⟨hm, rfl, hRo, hlastR ▸ hRf, ?_, by simp [refineSplit, deleteTag], ?_⟩
    · rw [newRoot_eq hR' hnew]
      exact ho
    · have hd : ([refineSplit (coreGraph cs.G cs.lsf)
          (coreGraph (cs.G.applyUpdate (.split v v' St Sh)) mid) (cs.lsf.F.root v)
          (newRoot R cs.lsf.F.R)] : List Update).countP deleteTag = 0 := by
        simp [refineSplit, deleteTag]
      rw [batchDeletes_eq_empty_of_countP_eq_zero hd]
      exact Finset.empty_subset _

private theorem card_applyBatch_splits {G : MGraph} {U : List Update} (h : G.BatchIsValid U) :
    (G.applyBatch U).V.card = G.V.card + batchSplitCount U := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch, batchSplitCount]
  | cons u U ih =>
    change ((G.applyUpdate u).applyBatch U).V.card = G.V.card + batchSplitCount (u :: U)
    rw [ih h.2]
    cases u with
    | insert => simp [MGraph.applyUpdate, batchSplitCount, isSplit]
    | delete => simp [MGraph.applyUpdate, batchSplitCount, isSplit]
    | split v v' St Sh =>
      have hV : (G.applyUpdate (.split v v' St Sh)).V.card = G.V.card + 1 :=
        Finset.card_insert_of_notMem h.1.2.1
      simp [hV, batchSplitCount, List.countP_cons, isSplit, Nat.add_right_comm G.V.card,
        Nat.add_assoc]

private theorem compLSF_forestAfterInput {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    let K := forestAfterInput cs.RF.F u
    let cs' := compLSFStepSingle cs u
    K.IsForest ∧ (cs.G.applyUpdate u).IsSubgraph K ∧ K.IsSubgraph cs'.RF.F ∧
      K.V = cs'.RF.F.V := by
  intro K cs'
  have hF := compLSF_RF_isRSF hI
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF' := compLSF_RF_isRSF hI'
  have hdec := compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩
  have hFE : cs'.RF.F.E ⊆ cs.RF.F.E := hdec.1
  have hFG : cs.RF.F.E ⊆ cs.G.E := hF.2.2.2.2.2.1
  have hFG' : cs'.RF.F.E ⊆ cs'.G.E := hF'.2.2.2.2.2.1
  have hFV : cs.RF.F.V = cs.G.V := hF.2.1
  have hFV' : cs'.RF.F.V = cs'.G.V := hF'.2.1
  have hKG : (cs.G.applyUpdate u).IsSubgraph K := by
    cases u with
    | insert e a b =>
      refine ⟨hFV.le, hFG.trans (Finset.subset_insert _ _), fun f hf => ?_⟩
      have hfe : f ≠ e := fun h => hu.1 (h ▸ hFG hf)
      change cs.G.tail f = Function.update cs.G.tail e a f ∧
        cs.G.head f = Function.update cs.G.head e b f
      simp [Function.update_of_ne hfe]
    | delete e =>
      exact ⟨hFV.le, Finset.erase_subset_erase e hFG, fun _ _ => ⟨rfl, rfl⟩⟩
    | split v v' St Sh =>
      refine ⟨?_, hFG, fun _ _ => ⟨rfl, rfl⟩⟩
      change insert v' cs.RF.F.V ⊆ insert v' cs.G.V
      rw [hFV]
  have hKV : K.V = cs'.G.V := by
    cases u with
    | insert => exact hFV
    | delete => exact hFV
    | split v v' St Sh =>
      change insert v' cs.RF.F.V = insert v' cs.G.V
      rw [hFV]
  refine ⟨?_, hKG, ?_, hKV.trans hFV'.symm⟩
  · cases u with
    | insert => exact hF.1
    | delete e => exact isForest_eraseEdge hF.1 e
    | split v v' St Sh =>
      exact applyUpdate_split_isForest hF.1 (hFV ▸ hu.1) (hFV ▸ hu.2.1) St Sh
  · have hKE : cs'.RF.F.E ⊆ K.E := by
      cases u with
      | insert => exact hFE
      | split => exact hFE
      | delete e =>
        intro f hf
        refine Finset.mem_erase.mpr ⟨?_, hFE hf⟩
        rintro rfl
        have := hFG' hf
        change f ∈ cs.G.E.erase f at this
        simp at this
    refine ⟨hFV'.trans hKV.symm |>.le, hKE, fun f hf => ?_⟩
    have hfK := hKE hf
    obtain ⟨h1, h2⟩ := hKG.2.2 f hfK
    exact ⟨h1.symm, h2.symm⟩

private theorem card_sdiff_trans {A B C : Finset ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    (C \ A).card = (C \ B).card + (B \ A).card := by
  rw [Finset.card_sdiff_of_subset h₁, Finset.card_sdiff_of_subset h₂,
    Finset.card_sdiff_of_subset (h₁.trans h₂)]
  have := Finset.card_le_card h₁
  have := Finset.card_le_card h₂
  omega

/-- The canonical core batch of one update of the component-wise LSF is ordered, has one split
per new root and at most one deletion, and deletes only the edge that the update deletes. -/
theorem orderedCore_canonStepCore {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    {β : ℕ} {ρ : Rotation cs.G} {σ : Rotation (cs.G.applyUpdate u)}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) (hr : RotationStep β u ρ σ)
    (hβ : 2 ≤ β) :
    let cs' := compLSFStepSingle cs u
    ∃ hI' : CompLSFInv C_lsst ℓ₀ cs',
      OrderedCoreBatch β (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI))
        (coreRotation (L := cs'.lsf) σ hI'.hG_val (compLSF_RF_isRSF hI')) (canonStepCore cs u) ∧
      batchSplitCount (canonStepCore cs u) = (cs'.RF.R \ cs.RF.R).card ∧
      (canonStepCore cs u).countP deleteTag ≤ 1 ∧
      batchDeletes (canonStepCore cs u) ⊆ batchDeletes [u] := by
  intro cs'
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF := compLSF_RF_isRSF hI
  have hF' : cs'.RF.IsRootedSpanningForestOf (cs.G.applyUpdate u) := compLSF_RF_isRSF hI'
  have hH : (cs.G.applyUpdate u).IsValid := hI'.hG_val
  have hR : cs.RF.R ⊆ cs'.RF.R := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).2
  obtain ⟨hK, hKG, hsub, hKV⟩ := compLSF_forestAfterInput hI hu
  let K := forestAfterInput cs.RF.F u
  let cuts := (K.E \ cs'.RF.F.E).sort (· ≤ ·)
  let Fc := cuts.foldl eraseForestEdge K
  have hFcE : Fc.E = cs'.RF.F.E := by
    simp only [Fc, cuts, foldl_eraseForestEdge, Finset.sort_toFinset]
    exact Finset.sdiff_sdiff_eq_self hsub.2.1
  have hFcK : K.IsSubgraph Fc := by
    refine ⟨?_, ?_, fun _ _ => by simp [Fc, foldl_eraseForestEdge]⟩
    · simp only [Fc, foldl_eraseForestEdge]; exact Finset.Subset.rfl
    · simp only [Fc, foldl_eraseForestEdge]; exact Finset.sdiff_subset
  have hEqF : GraphEq Fc cs'.RF.F := by
    refine ⟨?_, hFcE, fun f hf => ?_⟩
    · simp only [Fc, foldl_eraseForestEdge]; exact hKV
    · have hf' : f ∈ cs'.RF.F.E := hFcE ▸ hf
      obtain ⟨h1, h2⟩ := hsub.2.2 f hf'
      simp only [Fc, foldl_eraseForestEdge]
      exact ⟨h1.symm, h2.symm⟩
  let L'' : LSF := ⟨cs'.lsf.T, ⟨Fc, cs'.RF.R⟩, cs'.lsf.wstr⟩
  have hL'' : L''.F.IsRootedSpanningForestOf (cs.G.applyUpdate u) :=
    isRootedSpanningForestOf_congr hF' rfl (graphEq_symm hEqF)
  obtain ⟨hm, hmidF, _, hmR, h₀, hd₀, hdel₀⟩ :=
    orderedCore_inputCoreBatch (last := L'') ρ σ hI.hG_val hH hF hL'' rfl hu hr hβ hR hK
      hKG hFcK
  have hCut : cuts.foldl eraseForestEdge (inputMid cs u).F.F = L''.F.F := by rw [hmidF]; rfl
  have hMem : ∀ e ∈ cuts, e ∈ (inputMid cs u).F.F.E := by
    intro e he
    rw [hmidF]
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1
  have h₁ := orderedCore_releasesBatch σ hH cuts hm hL'' hmR hCut hMem
    (Finset.sort_nodup _ _) hβ
  have hb := h₀.append h₁
  have hdef : canonStepCore cs u = inputCoreBatch cs u ++
      releasesBatch (cs.G.applyUpdate u) L''.F.R (inputMid cs u) cuts := rfl
  rw [hdef]
  refine ⟨hI', hb.congr_lsf σ hH hL'' hF' rfl hEqF, ?_, ?_, ?_⟩
  · obtain ⟨hv, hEq, _⟩ := hb
    have hc := card_applyBatch_splits hv
    have hV := congrArg Finset.card hEq.1
    change cs'.RF.R.card = _ at hV
    change _ = cs.RF.R.card + batchSplitCount _ at hc
    rw [Finset.card_sdiff_of_subset hR, hV.trans hc, Nat.add_sub_cancel_left]
  · simpa only [List.countP_append, releasesBatch_countP_delete, Nat.add_zero] using hd₀
  · rw [batchDeletes_append, batchDeletes_eq_empty_of_countP_eq_zero
      (releasesBatch_countP_delete _ _ _ _), Finset.union_empty]
    exact hdel₀

/-- The canonical core batch of a batch is an ordered core batch from the core rotation before
the batch to the core rotation after it, with one split per new root, at most one deletion per
update, and only deletions of the input. -/
theorem orderedCore_canonCoreBatch {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {G : MGraph} {U : List Update}
    {β : ℕ} {ρ : Rotation G} {σ : Rotation (G.applyBatch U)} (hrot : RotationBatch β U ρ σ)
    (hβ : 2 ≤ β) (hU : G.BatchIsValid U) (cs : CompLSFState) (hS : cs.G = G)
    (hI : CompLSFInv C_lsst ℓ₀ cs) :
    let cs' := compLSFBatch cs U
    ∃ he : cs'.G = G.applyBatch U, ∃ hI' : CompLSFInv C_lsst ℓ₀ cs',
      OrderedCoreBatch β
        (coreRotation (L := cs.lsf) (hS.symm ▸ ρ) hI.hG_val (compLSF_RF_isRSF hI))
        (coreRotation (L := cs'.lsf) (he.symm ▸ σ) hI'.hG_val (compLSF_RF_isRSF hI'))
        (canonCoreBatch cs U) ∧
      batchSplitCount (canonCoreBatch cs U) = (cs'.RF.R \ cs.RF.R).card ∧
      (canonCoreBatch cs U).countP deleteTag ≤ U.length ∧
      batchDeletes (canonCoreBatch cs U) ⊆ batchDeletes U := by
  induction hrot generalizing cs with
  | @nil G ρ σ hr =>
    subst G
    exact ⟨rfl, hI, OrderedCoreBatch.of_isRotated _ _ hr,
      by simp [canonCoreBatch, batchSplitCount, compLSFBatch], by simp [canonCoreBatch],
      by simp [canonCoreBatch, batchDeletes]⟩
  | @cons G u rest ρ ρ' σ hs _ ih =>
    subst G
    obtain ⟨hI₀, h₀, hc₀, hd₀, hdel₀⟩ := orderedCore_canonStepCore hI hU.1 hs hβ
    obtain ⟨he₁, hI₁, h₁, hc₁, hd₁, hdel₁⟩ := ih hU.2 (compLSFStepSingle cs u) rfl hI₀
    have hR₀ : cs.RF.R ⊆ (compLSFStepSingle cs u).RF.R :=
      (compLSFBatch_decremental (U := [u]) hI ⟨hU.1, trivial⟩).2
    have hR₁ := (compLSFBatch_decremental (U := rest) hI₀ hU.2).2
    have hdef : canonCoreBatch cs (u :: rest) =
        canonStepCore cs u ++ canonCoreBatch (compLSFStepSingle cs u) rest := rfl
    rw [hdef]
    refine ⟨he₁, hI₁, h₀.append h₁, ?_, ?_, ?_⟩
    · change batchSplitCount _ =
        ((compLSFBatch (compLSFStepSingle cs u) rest).RF.R \ cs.RF.R).card
      rw [batchSplitCount_append, card_sdiff_trans hR₀ hR₁, hc₀, hc₁, Nat.add_comm]
    · rw [List.countP_append, List.length_cons]
      omega
    · rw [batchDeletes_append]
      have hcons : batchDeletes (u :: rest) = batchDeletes [u] ∪ batchDeletes rest := by
        simpa using batchDeletes_append [u] rest
      rw [hcons]
      exact Finset.union_subset_union hdel₀ hdel₁

/-- The canonical core batch meets `CoreBatchSpec` whenever `cs` meets the component-wise LSF
invariant and `U` is a valid ordered batch with split bound two between rotations with the
given orders (paper Lemma 5.14, page 22). -/
theorem canonCoreBatch_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    {ord ord' : ℕ → List End} (hI : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G)
    (σ : Rotation (cs.G.applyBatch U)) (hρ : ρ.order = ord) (hσ : σ.order = ord')
    (hrot : RotationBatch 2 U ρ σ) (hU : cs.G.BatchIsValid U) :
    CoreBatchSpec cs ord ord' U (canonCoreBatch cs U) := by
  obtain ⟨he, hI', hOCB, hsp, hdel, hdelSub⟩ :=
    orderedCore_canonCoreBatch (C_lsst := C_lsst) (ℓ₀ := ℓ₀) hrot (Nat.le_refl 2) hU cs rfl hI
  refine ⟨?_, hsp, hdel, hdelSub⟩
  intro ρ' σ' hG hF hG' hF' hρ' hσ'
  have hρEq : ρ' = ρ := Rotation.ext_order (hρ'.trans hρ.symm)
  have hσEq : σ' = he.symm ▸ σ :=
    Rotation.ext_order (by rw [cast_order_eq, hσ, hσ'])
  subst hρEq
  subst hσEq
  exact hOCB

end MinCostFlow.SparseCore
