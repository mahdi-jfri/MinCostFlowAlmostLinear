module

public import MinCostFlow.SparseCore.Program.ReadTree
public import MinCostFlow.SparseCore.LSFInsertNonTree
public import MinCostFlow.Chain.BundleRestart

/-!
# Model bridges for piece P10 (`ReadBridge`)

Links the abstract operations of `ReadView` (`ReadSpec.lean`) to the model of the sparse-core
bundle tool (`CompLSF.lean`, `LSFInsertNonTree.lean`, `BundleRestart.lean`, `RestartIface.lean`):

1. **Same graphs and same LSF views** (`SameLSF`): two LSF views with `SameGraph` on `T` and `F.F`,
   equal root sets `F.R`, and equal stretch tables `wstr` satisfy the same memory readout predicates
   (`LSFAt.of_same`, `ReadLSFOut.of_same`, `ReadSOut.of_same`).
2. **Updates and `LSFChange.Exact`** (`lsfViewStep_sameLSF`): for a `CompLSFState` meeting
   `CompLSFInv`, any valid batch `U` and exact change record `c : LSFChange` yield
   `SameLSF (lsfViewStep cs.lsf U c) (compLSFBatch cs U).lsf` (combining `compLSFBatch_T_sameGraph`
   from `LSFInsertNonTree.lean` with `lsfViewStep_F_same`, `lsfViewStep_R_eq`, and
   `compLSFBatch_wstr_eq`).
3. **Restarts and `scurViewRebuild` / `restartBundleTree`** (`readView_rebuild_same_scurViewRebuild`,
   `readView_rebuild_eq_scurViewRebuild`, `readView_rebuild_same_restartBundleTree`): when the old
   bundle edges `slotsGE` contain the new spanner edges `slotsHE` and lie in `G.E`, the core ends
   lie in `S.V`, and `S.E \ slotsGE = X`, `ReadView.rebuild` produces the same sparsified core `S`
   as `scurViewRebuild` (and `restartBundleTree`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.Bundle
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Same LSF views and readout transfer -/

/-- Two LSF views agree on everything a graph/LSF readout sees: `T` and `F.F` up to `SameGraph`,
the same root set `F.R`, and the same stretch table `wstr`. -/
def SameLSF (lsf₁ lsf₂ : LSF) : Prop :=
  SameGraph lsf₁.T lsf₂.T ∧ SameGraph lsf₁.F.F lsf₂.F.F ∧
    lsf₁.F.R = lsf₂.F.R ∧ lsf₁.wstr = lsf₂.wstr

theorem SameLSF.refl (lsf : LSF) : SameLSF lsf lsf :=
  ⟨SameGraph.refl _, SameGraph.refl _, rfl, rfl⟩

theorem SameLSF.symm {lsf₁ lsf₂ : LSF} (h : SameLSF lsf₁ lsf₂) : SameLSF lsf₂ lsf₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem SameLSF.trans {lsf₁ lsf₂ lsf₃ : LSF} (h₁ : SameLSF lsf₁ lsf₂) (h₂ : SameLSF lsf₂ lsf₃) :
    SameLSF lsf₁ lsf₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

/-- `LSFAt` is invariant under `SameLSF`. -/
theorem LSFAt.of_same {mem : ℕ → ℕ} {a vCap eCap h L P : ℕ} {E : Finset ℕ} {lsf₁ lsf₂ : LSF}
    (hAt : LSFAt mem a vCap eCap h L P E lsf₁) (hs : SameLSF lsf₁ lsf₂) :
    LSFAt mem a vCap eCap h L P E lsf₂ :=
  ⟨DynGraphAt.of_same hAt.1 hs.1, DynGraphAt.of_same hAt.2.1 hs.2.1,
    hs.2.2.1 ▸ hAt.2.2.1, hs.2.2.2 ▸ hAt.2.2.2⟩

/-- `ReadLSFOut` is invariant under `SameLSF`. -/
theorem ReadLSFOut.of_same {mem : ℕ → ℕ} {h L_w P : ℕ} {v : ReadView} {lsf' : LSF}
    (hout : ReadLSFOut mem h L_w P v) (hs : SameLSF v.lsf lsf') :
    ReadLSFOut mem h L_w P { v with lsf := lsf' } := by
  obtain ⟨hLw, ⟨fV, fE, hLSF⟩, hPr⟩ := hout
  exact ⟨hLw, ⟨fV, fE, LSFAt.of_same hLSF hs⟩, hPr⟩

/-- `ReadSOut` is invariant under `SameGraph`. -/
theorem ReadSOut.of_same {mem : ℕ → ℕ} {h : ℕ} {v : ReadView} {S' : MGraph}
    (hout : ReadSOut mem h v) (hs : SameGraph v.S S') :
    ReadSOut mem h { v with S := S' } := by
  obtain ⟨gV, gE, hS⟩ := hout
  exact ⟨gV, gE, DynGraphAt.of_same hS hs⟩

/-- `SameGraph` preserves `IsWalk`. -/
theorem SameGraph.isWalk_iff {H K : MGraph} (hs : SameGraph H K) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P ↔ K.IsWalk u v P
  | _, _, [] => by
    constructor <;> (intro h; cases h; exact .nil _)
  | u, v, x :: rest => by
    constructor
    · intro h
      cases h with
      | cons hxE hxSrc hrest =>
        have hxK : x.1 ∈ K.E := hs.2.1 ▸ hxE
        have he := hs.2.2 x.1 hxE
        have hsrc : K.src x = u := by unfold MGraph.src at *; rw [← he.1, ← he.2]; exact hxSrc
        have hdst : K.dst x = H.dst x := by unfold MGraph.dst; rw [← he.1, ← he.2]
        exact .cons hxK hsrc (hdst ▸ (hs.isWalk_iff.mp hrest))
    · intro h
      cases h with
      | cons hxE hxSrc hrest =>
        have hxH : x.1 ∈ H.E := hs.2.1.symm ▸ hxE
        have he := hs.2.2 x.1 hxH
        have hsrc : H.src x = u := by unfold MGraph.src at *; rw [he.1, he.2]; exact hxSrc
        have hdst : H.dst x = K.dst x := by unfold MGraph.dst; rw [he.1, he.2]
        exact .cons hxH hsrc (hdst ▸ (hs.isWalk_iff.mpr hrest))

/-- `SameGraph` preserves `Connected`. -/
theorem SameGraph.connected_iff {H K : MGraph} (hs : SameGraph H K) (u v : ℕ) :
    H.Connected u v ↔ K.Connected u v :=
  ⟨fun ⟨P, hP⟩ => ⟨P, hs.isWalk_iff.mp hP⟩, fun ⟨P, hP⟩ => ⟨P, hs.isWalk_iff.mpr hP⟩⟩

/-- `SameLSF` preserves the root function of a rooted spanning forest. -/
theorem SameLSF.root_eq {G : MGraph} {lsf₁ lsf₂ : LSF} (hs : SameLSF lsf₁ lsf₂)
    (hRS : lsf₁.F.IsRootedSpanningForestOf G) {u : ℕ} (hu : u ∈ G.V) :
    lsf₁.F.root u = lsf₂.F.root u := by
  have hspec := rootedForest_root_spec hRS hu
  have hRS₂ : lsf₂.F.IsRootedSpanningForestOf G := by
    refine ⟨⟨?_, ?_⟩, hs.2.1.1.symm.trans hRS.2.1, hs.2.2.1 ▸ hRS.2.2.1, ?_, ?_⟩
    · intro e he
      have he₁ : e ∈ lsf₁.F.F.E := hs.2.1.2.1.symm ▸ he
      have hend := hRS.1.1 e he₁
      have heq := hs.2.1.2.2 e he₁
      rw [← hs.2.1.1, ← heq.1, ← heq.2]
      exact hend
    · rintro P ⟨hne, hnd, v, hW⟩
      exact hRS.1.2 P ⟨hne, hnd, v, hs.2.1.isWalk_iff.mpr hW⟩
    · intro v hv
      obtain ⟨r, ⟨hr, hc⟩, huniq⟩ := hRS.2.2.2.1 v hv
      exact ⟨r, ⟨hs.2.2.1 ▸ hr, (hs.2.1.connected_iff v r).mp hc⟩,
        fun r' ⟨hr', hc'⟩ => huniq r' ⟨hs.2.2.1.symm ▸ hr', (hs.2.1.connected_iff v r').mpr hc'⟩⟩
    · refine ⟨hs.2.1.1 ▸ hRS.2.2.2.2.1, hs.2.1.2.1 ▸ hRS.2.2.2.2.2.1, fun e he => ?_⟩
      have he₁ : e ∈ lsf₁.F.F.E := hs.2.1.2.1.symm ▸ he
      have h1 := hs.2.1.2.2 e he₁
      have h2 := hRS.2.2.2.2.2.2 e he₁
      exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
  exact (rootedForest_root_eq_of_mem hRS₂ hu (hs.2.2.1 ▸ hspec.1)
    ((hs.2.1.connected_iff _ _).mp hspec.2)).symm

/-! ## Bridge 1: `LSFChange.Exact` and `lsfViewStep` against `compLSFBatch` -/

/-- `wstr` after `compLSFBatch` is the fold of `wstrViewUpdate`. -/
theorem compLSFBatch_wstr_eq (cs : CompLSFState) (U : List Update) :
    (compLSFBatch cs U).lsf.wstr = U.foldl wstrViewUpdate cs.lsf.wstr := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih =>
    change (compLSFBatch (compLSFStepSingle cs u) rest).lsf.wstr =
      rest.foldl wstrViewUpdate (wstrViewUpdate cs.lsf.wstr u)
    have h1 : (compLSFStepSingle cs u).lsf.wstr = wstrViewUpdate cs.lsf.wstr u := by
      cases u <;> rfl
    rw [← h1]
    exact ih (compLSFStepSingle cs u)

/-- Under `LSFChange.Exact`, the root set of `lsfViewStep` is the root set of `compLSFBatch`. -/
theorem lsfViewStep_R_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    {c : LSFChange} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    (hc : c.Exact cs.lsf (compLSFBatch cs U).lsf) :
    (lsfViewStep cs.lsf U c).F.R = (compLSFBatch cs U).lsf.F.R := by
  have hsub : cs.RF.R ⊆ (compLSFBatch cs U).RF.R := (compLSFBatch_decremental hI hU).2
  change cs.RF.R ∪ c.roots.toFinset = (compLSFBatch cs U).RF.R
  rw [hc.2.1]
  exact Finset.union_sdiff_of_subset hsub

/-- One step of `dgBatchTarget 0` preserves subgraph agreement with `G`, vertex equality, and
containment of the component forest edges. -/
private theorem dgBatchTarget_zero_step {G H : MGraph} {u : Update} (hu : G.UpdateIsValid u)
    (hV : H.V = G.V) (hE : H.E ⊆ G.E)
    (hends : ∀ e ∈ H.E, H.tail e = G.tail e ∧ H.head e = G.head e) :
    let H' := dgBatchTarget 0 H u
    let G' := G.applyUpdate u
    H'.V = G'.V ∧ H'.E ⊆ G'.E ∧ H'.E ⊆ H.E ∧
      (∀ e ∈ H'.E, H'.tail e = G'.tail e ∧ H'.head e = G'.head e) ∧
      ∀ Fsub : Finset ℕ, Fsub ⊆ H.E → Fsub ⊆ G'.E → Fsub ⊆ H'.E := by
  cases u with
  | insert e a b =>
    obtain ⟨heG, _, _⟩ := hu
    refine ⟨by simpa [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate] using hV,
      by simpa [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate] using
        hE.trans (Finset.subset_insert e G.E),
      by simp [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch], fun f hf => ?_, fun Fsub hFH _ => by
        simpa [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch] using hFH⟩
    simp only [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, List.foldl_nil] at hf ⊢
    have hne : f ≠ e := fun h => heG (h ▸ hE hf)
    simp only [MGraph.applyUpdate, Function.update_of_ne hne]
    exact hends f hf
  | delete e =>
    have hV' : (dgBatchTarget 0 H (.delete e)).V = H.V := by
      simp only [dgBatchTarget_zero, restrictUpdate]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate]
    have hE' : (dgBatchTarget 0 H (.delete e)).E = H.E.erase e := by
      simp only [dgBatchTarget_zero, restrictUpdate]
      split_ifs with he
      · simp [MGraph.applyBatch, MGraph.applyUpdate]
      · simp [MGraph.applyBatch, Finset.erase_eq_of_notMem he]
    have hO : ∀ f, (dgBatchTarget 0 H (.delete e)).tail f = H.tail f ∧
        (dgBatchTarget 0 H (.delete e)).head f = H.head f := fun f => by
      simp only [dgBatchTarget_zero, restrictUpdate]
      split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate]
    refine ⟨hV'.trans hV, hE' ▸ Finset.erase_subset_erase e hE, hE' ▸ Finset.erase_subset e H.E,
      fun f hf => ?_, fun Fsub hFH hFG' => ?_⟩
    · rw [hE'] at hf
      have hfH := Finset.mem_of_mem_erase hf
      exact ⟨(hO f).1.trans (hends f hfH).1, (hO f).2.trans (hends f hfH).2⟩
    · rw [hE']
      intro f hf
      have hne : f ≠ e := (Finset.mem_erase.mp (hFG' hf)).1
      exact Finset.mem_erase.mpr ⟨hne, hFH hf⟩
  | split v v' St Sh =>
    refine ⟨by simp [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate, hV],
      by simpa [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate] using hE,
      by simp [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate],
      fun f hf => ?_, fun Fsub hFH _ => by
        simpa [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate] using hFH⟩
    simp only [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, List.foldl_cons,
      List.foldl_nil, MGraph.applyUpdate] at hf ⊢
    obtain ⟨ht, hh⟩ := hends f hf
    simp [hf, ht, hh]

/-- Folding `dgBatchTarget 0` along `U` keeps the forest vertices, endpoints on surviving edges, and
sandwiches `F'.E` between `(compLSFBatch cs U).RF.F.E` and `cs.RF.F.E`. -/
private theorem dgBatchTarget_zero_foldl_compLSF {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {cs : CompLSFState} {H : MGraph},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      H.V = cs.G.V → H.E ⊆ cs.G.E → cs.RF.F.E ⊆ H.E →
      (∀ e ∈ H.E, H.tail e = cs.G.tail e ∧ H.head e = cs.G.head e) →
      let H' := U.foldl (dgBatchTarget 0) H
      let cs' := compLSFBatch cs U
      H'.V = cs'.G.V ∧ H'.E ⊆ H.E ∧ cs'.RF.F.E ⊆ H'.E ∧
        ∀ e ∈ H'.E, H'.tail e = cs'.G.tail e ∧ H'.head e = cs'.G.head e
  | [], cs, H, _, _, hV, _, hFH, hends => ⟨hV, Finset.Subset.rfl, hFH, hends⟩
  | u :: rest, cs, H, hI, ⟨hu, hrest⟩, hV, hE, hFH, hends => by
    have hstep := dgBatchTarget_zero_step hu hV hE hends
    set cs₁ := compLSFStepSingle cs u
    have hI₁ : CompLSFInv C_lsst ℓ₀ cs₁ := compLSFInv_step hI hu
    have hF₁_sub_F : cs₁.RF.F.E ⊆ cs.RF.F.E :=
      (compLSFBatch_decremental hI (U := [u]) ⟨hu, trivial⟩).1
    have hF₁_sub_G₁ : cs₁.RF.F.E ⊆ cs₁.G.E := (compLSF_RF_isRSF hI₁).2.2.2.2.2.1
    have hF₁_sub_H₁ : cs₁.RF.F.E ⊆ (dgBatchTarget 0 H u).E :=
      hstep.2.2.2.2 cs₁.RF.F.E (hF₁_sub_F.trans hFH) hF₁_sub_G₁
    have ih := dgBatchTarget_zero_foldl_compLSF rest hI₁ hrest
      hstep.1 hstep.2.1 hF₁_sub_H₁ hstep.2.2.2.1
    exact ⟨ih.1, ih.2.1.trans hstep.2.2.1, ih.2.2.1, ih.2.2.2⟩

/-- Under `LSFChange.Exact`, the forest graph of `lsfViewStep` has `SameGraph` with the forest graph
of `compLSFBatch`. -/
theorem lsfViewStep_F_same {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    {c : LSFChange} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    (hc : c.Exact cs.lsf (compLSFBatch cs U).lsf) :
    SameGraph (lsfViewStep cs.lsf U c).F.F (compLSFBatch cs U).lsf.F.F := by
  have hRS := compLSF_RF_isRSF hI
  have hfold := dgBatchTarget_zero_foldl_compLSF (H := cs.RF.F) U hI hU rfl
    hRS.2.2.2.2.2.1 Finset.Subset.rfl (fun _ _ => ⟨rfl, rfl⟩)
  obtain ⟨hV, hE_le, hF'_le, hends⟩ := hfold
  have hE_eq : (U.foldl (dgBatchTarget 0) cs.RF.F).E \ c.fDel.toFinset = (compLSFBatch cs U).RF.F.E := by
    rw [hc.2.2.2]
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨he1, he2⟩
      by_contra hnot
      exact he2 ⟨hE_le he1, hnot⟩
    · intro he
      exact ⟨hF'_le he, fun h => h.2 he⟩
  refine ⟨hV, hE_eq, fun e he => ?_⟩
  exact hends e (Finset.mem_sdiff.mp he).1

/-- `TreeAgree cs.G cs.T` holds for every `CompLSFInv` state. -/
theorem compLSF_treeAgree {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : TreeAgree cs.G cs.T :=
  ⟨hI.hG_val, (compLSF_T_isForest hI).1, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-- **Bridge 1: `LSFChange.Exact` gives the model's next LSF view.**
For any `CompLSFState` satisfying `CompLSFInv`, any valid batch `U`, and an exact change record
`c : LSFChange`, `lsfViewStep cs.lsf U c` has `SameLSF` with `(compLSFBatch cs U).lsf`. -/
theorem lsfViewStep_sameLSF {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    {c : LSFChange} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    (hc : c.Exact cs.lsf (compLSFBatch cs U).lsf) :
    SameLSF (lsfViewStep cs.lsf U c) (compLSFBatch cs U).lsf :=
  ⟨(compLSFBatch_T_sameGraph hU).symm, lsfViewStep_F_same hI hU hc,
    lsfViewStep_R_eq hI hU hc, (compLSFBatch_wstr_eq cs U).symm⟩

/-- A `ReadView` built from a `CompLSFState` meeting `CompLSFInv` meets `ReadView.Inv` as soon as
the names fit in the capacities, `S` is valid, and the stretch pairs match `cs.wstrGlobal`. -/
theorem readView_inv_of_compLSF {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {vCap eCap tCap : ℕ}
    {cs : CompLSFState} {S : MGraph} {num den : ℕ → ℤ}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hGV : ∀ x ∈ cs.G.V, x < vCap) (hGE : ∀ e ∈ cs.G.E, e < eCap) (het : eCap ≤ tCap)
    (hTE : ∀ e ∈ cs.T.E, e < tCap)
    (hSval : S.IsValid) (hSV : ∀ x ∈ S.V, x < vCap) (hSE : ∀ e ∈ S.E, e < eCap)
    (hpairs : ∀ e ∈ cs.G.E, 0 < den e ∧ (num e : ℝ) / den e = cs.wstrGlobal e) :
    ReadView.Inv vCap eCap tCap ⟨cs.G, cs.lsf, S, num, den⟩ := by
  have hRS := compLSF_RF_isRSF hI
  have hta := compLSF_treeAgree hI
  exact ⟨hI.hG_val, hGV, hGE, het, hta.2.1, hta.2.2.1, hTE, hta.2.2.2,
    hRS.2.1, hRS.2.2.2.2, hRS.2.2.1, hRS.2.2.2.1, hSval, hSV, hSE, hpairs⟩

/-! ## Bridge 2: `ReadView.rebuild` against `scurViewRebuild` and `restartBundleTree` -/

/-- The core endpoints of an edge of `G` lie in `lsf.F.R` whenever `lsf.F` is a rooted spanning
forest of `G` and `G` is valid. -/
theorem coreGraph_ends_mem_R {G : MGraph} {lsf : LSF} (hG : G.IsValid)
    (hRS : lsf.F.IsRootedSpanningForestOf G) {e : ℕ} (he : e ∈ G.E) :
    (coreGraph G lsf).tail e ∈ lsf.F.R ∧ (coreGraph G lsf).head e ∈ lsf.F.R := by
  obtain ⟨ht, hh⟩ := hG e he
  exact ⟨(rootedForest_root_spec hRS ht).1, (rootedForest_root_spec hRS hh).1⟩

/-- **Generic rebuild bridge (`SameGraph`).** Under the model invariants (`new ⊆ old ⊆ G.E`, core
ends of `new` in `S.V`, `S` a subgraph of `coreGraph G lsf`, and `S.E \ old = X`),
`ReadView.rebuildS` produces a sparsified core with `SameGraph` to `ScurView.rebuild`. -/
theorem readView_rebuildS_same_scurView {v : ReadView} {sv : ScurView} {old new : Finset ℕ}
    (hV : sv.V = v.S.V)
    (htail : sv.tail = (coreGraph v.G v.lsf).tail)
    (hhead : sv.head = (coreGraph v.G v.lsf).head)
    (hsub : (coreGraph v.G v.lsf).IsSubgraph v.S)
    (hnew_old : new ⊆ old) (hold_G : old ⊆ v.G.E)
    (hcoreV : ∀ e ∈ new, (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧
      (coreGraph v.G v.lsf).head e ∈ v.S.V)
    (hX : v.S.E \ old = sv.X) :
    SameGraph (v.rebuildS old new).S (sv.rebuild new).S := by
  classical
  have hadd : (new ∩ v.G.E).filter (fun e =>
      (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V) = new := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun h => h.1.1, fun he => ⟨⟨he, hold_G (hnew_old he)⟩, hcoreV e he⟩⟩
  have hE : (v.rebuildS old new).S.E = (sv.rebuild new).S.E := by
    change (v.S.E \ (old ∪ new)) ∪ _ = new ∪ sv.X
    rw [hadd, Finset.union_eq_left.mpr hnew_old, hX, Finset.union_comm]
  refine ⟨hV.symm, hE, fun e he => ?_⟩
  change (if e ∈ _ then (coreGraph v.G v.lsf).tail e else v.S.tail e) = sv.tail e ∧
    (if e ∈ _ then (coreGraph v.G v.lsf).head e else v.S.head e) = sv.head e
  rw [hadd, htail, hhead]
  by_cases hne : e ∈ new
  · simp [hne]
  · simp only [hne, ↓reduceIte]
    have heS : e ∈ v.S.E := by
      have he' : e ∈ new ∪ sv.X := by change e ∈ (sv.rebuild new).S.E; rw [← hE]; exact he
      rcases Finset.mem_union.mp he' with h | h
      · exact absurd h hne
      · exact (Finset.mem_sdiff.mp (hX.symm ▸ h)).1
    exact hsub.2.2 e heS

/-- **Exact rebuild bridge (`=`).** When `v.S` also has `tail` and `head` equal to `coreGraph`
everywhere (as for `BundleTreeState.S_cur` after initialization or restart), `ReadView.rebuildS`
gives exact `MGraph` equality with `ScurView.rebuild`. -/
theorem readView_rebuildS_eq_scurView {v : ReadView} {sv : ScurView} {old new : Finset ℕ}
    (hV : sv.V = v.S.V)
    (htail : sv.tail = (coreGraph v.G v.lsf).tail)
    (hhead : sv.head = (coreGraph v.G v.lsf).head)
    (hStail : v.S.tail = (coreGraph v.G v.lsf).tail)
    (hShead : v.S.head = (coreGraph v.G v.lsf).head)
    (hnew_old : new ⊆ old) (hold_G : old ⊆ v.G.E)
    (hcoreV : ∀ e ∈ new, (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧
      (coreGraph v.G v.lsf).head e ∈ v.S.V)
    (hX : v.S.E \ old = sv.X) :
    (v.rebuildS old new).S = (sv.rebuild new).S := by
  classical
  have hadd : (new ∩ v.G.E).filter (fun e =>
      (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V) = new := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun h => h.1.1, fun he => ⟨⟨he, hold_G (hnew_old he)⟩, hcoreV e he⟩⟩
  unfold ReadView.rebuildS ScurView.rebuild
  dsimp only
  rw [hadd, Finset.union_eq_left.mpr hnew_old, hX, Finset.union_comm]
  congr 1
  · exact hV.symm
  · funext e; rw [htail, hStail]; split_ifs <;> rfl
  · funext e; rw [hhead, hShead]; split_ifs <;> rfl

/-- **Bridge 2 (`SameGraph`): `ReadView.rebuild` equals `scurViewRebuild`.** -/
theorem readView_rebuild_same_scurViewRebuild {P : DSParams} {cap : ℕ}
    {v : ReadView} {sv : ScurView} {S6 : BucketSpannerState cap} {slots : List ℕ}
    (hG : v.G.IsValid) (hRS : v.lsf.F.IsRootedSpanningForestOf v.G)
    (hSV : v.S.V = v.lsf.F.R) (hV : sv.V = v.S.V)
    (htail : sv.tail = (coreGraph v.G v.lsf).tail)
    (hhead : sv.head = (coreGraph v.G v.lsf).head)
    (hsub : (coreGraph v.G v.lsf).IsSubgraph v.S)
    (hH_sub_G : ∀ s ∈ slots, slotHE P S6 s ⊆ slotGE P S6 s)
    (hG_sub_vG : slotsGE P S6 slots ⊆ v.G.E)
    (hX : v.S.E \ slotsGE P S6 slots = sv.X) :
    SameGraph (v.rebuild P S6 slots).S (scurViewRebuild P sv S6 slots).S := by
  have hnew_old : slotsHE P S6 slots ⊆ slotsGE P S6 slots := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨s, hs, hes⟩
    exact Finset.mem_biUnion.mpr ⟨s, hs, hH_sub_G s (List.mem_toFinset.mp hs) hes⟩
  exact readView_rebuildS_same_scurView hV htail hhead hsub hnew_old hG_sub_vG
    (fun e he => hSV ▸ coreGraph_ends_mem_R hG hRS (hG_sub_vG (hnew_old he))) hX

/-- **Bridge 2 (`=`): `ReadView.rebuild` equals `scurViewRebuild` on the nose** when `v.S` has
the endpoints of `coreGraph v.G v.lsf`. -/
theorem readView_rebuild_eq_scurViewRebuild {P : DSParams} {cap : ℕ}
    {v : ReadView} {sv : ScurView} {S6 : BucketSpannerState cap} {slots : List ℕ}
    (hG : v.G.IsValid) (hRS : v.lsf.F.IsRootedSpanningForestOf v.G)
    (hSV : v.S.V = v.lsf.F.R) (hV : sv.V = v.S.V)
    (htail : sv.tail = (coreGraph v.G v.lsf).tail)
    (hhead : sv.head = (coreGraph v.G v.lsf).head)
    (hStail : v.S.tail = (coreGraph v.G v.lsf).tail)
    (hShead : v.S.head = (coreGraph v.G v.lsf).head)
    (hH_sub_G : ∀ s ∈ slots, slotHE P S6 s ⊆ slotGE P S6 s)
    (hG_sub_vG : slotsGE P S6 slots ⊆ v.G.E)
    (hX : v.S.E \ slotsGE P S6 slots = sv.X) :
    (v.rebuild P S6 slots).S = (scurViewRebuild P sv S6 slots).S := by
  have hnew_old : slotsHE P S6 slots ⊆ slotsGE P S6 slots := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨s, hs, hes⟩
    exact Finset.mem_biUnion.mpr ⟨s, hs, hH_sub_G s (List.mem_toFinset.mp hs) hes⟩
  exact readView_rebuildS_eq_scurView hV htail hhead hStail hShead hnew_old hG_sub_vG
    (fun e he => hSV ▸ coreGraph_ends_mem_R hG hRS (hG_sub_vG (hnew_old he))) hX

/-- **Bridge 2 specialized to `restartBundleTree`:** when `v` holds the branch data of `tr`, the
old `S_cur` has the model form `dynUnionE ∪ X` with `dynUnionE ⊆ bunUnionE` and `Disjoint X
bunUnionE`, and the bucket spanner table `S6` holds the fresh spanners of `restartBundleTree` on
the listed `slots` (whose bundle graphs have union `bunUnionE` and spanners have union
`dynUnionE'`), `(v.rebuild P S6 slots).S` has `SameGraph` with
`(restartBundleTree L sparsify tr ord).S_cur`. -/
theorem readView_rebuild_same_restartBundleTree {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {P : DSParams} {cap : ℕ} {tr : BundleTreeState L} {ord : ℕ → List End}
    {v : ReadView} {S6 : BucketSpannerState cap} {slots : List ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hGeq : v.G = tr.cs.G) (hlsf : v.lsf = tr.cs.lsf)
    (hSV : v.S.V = tr.cs.RF.R)
    (hSsub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph v.S)
    (hH_sub_G : ∀ s ∈ slots, slotHE P S6 s ⊆ slotGE P S6 s)
    (hG_sub_vG : slotsGE P S6 slots ⊆ tr.cs.G.E)
    (hHE_eq : slotsHE P S6 slots =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        (DynSpanner.init (normGraph (restartBucketBundle tr ord C b).graph) L
          (phaseBase ((normGraph (restartBucketBundle tr ord C b).graph).n + tr.splitBound) L)
          (sparsify tr.m₀)).state.H.E)
    (hSE_form : v.S.E =
      (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b => (tr.dyn (C, b)).H.E) ∪
      ((tr.activeComps.biUnion fun C =>
          ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \
            (tr.activeBuckets C).biUnion fun b =>
              (if C ∈ tr.activeComps then restartBucketBundle tr ord C b else tr.bun (C, b)).edges) ∪
        tr.cs.crossEdges))
    (hdyn_sub : (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        (tr.dyn (C, b)).H.E) ⊆ slotsGE P S6 slots)
    (hX_disj : Disjoint
      ((tr.activeComps.biUnion fun C =>
          ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \
            (tr.activeBuckets C).biUnion fun b =>
              (if C ∈ tr.activeComps then restartBucketBundle tr ord C b else tr.bun (C, b)).edges) ∪
        tr.cs.crossEdges)
      (slotsGE P S6 slots)) :
    SameGraph (v.rebuild P S6 slots).S (restartBundleTree L sparsify tr ord).S_cur := by
  classical
  set X : Finset ℕ :=
    (tr.activeComps.biUnion fun C =>
        ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \
          (tr.activeBuckets C).biUnion fun b =>
            (if C ∈ tr.activeComps then restartBucketBundle tr ord C b else tr.bun (C, b)).edges) ∪
      tr.cs.crossEdges
  let sv : ScurView :=
    { V := tr.cs.RF.R
      tail := (coreGraph tr.cs.G tr.cs.lsf).tail
      head := (coreGraph tr.cs.G tr.cs.lsf).head
      X := X
      S := v.S }
  have hX : v.S.E \ slotsGE P S6 slots = X := by
    rw [hSE_form, Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hdyn_sub,
      Finset.empty_union, Finset.sdiff_eq_self_of_disjoint hX_disj]
  have hmain := readView_rebuild_same_scurViewRebuild (sv := sv) (S6 := S6) (slots := slots)
    (hGeq ▸ hI.hG_val) (hGeq ▸ hlsf ▸ compLSF_RF_isRSF hI)
    (hlsf ▸ hSV) hSV.symm (by simp [sv, hGeq, hlsf]) (by simp [sv, hGeq, hlsf])
    (hGeq ▸ hlsf ▸ hSsub) hH_sub_G (hGeq ▸ hG_sub_vG) hX
  have hEq : (scurViewRebuild P sv S6 slots).S = (restartBundleTree L sparsify tr ord).S_cur := by
    unfold scurViewRebuild ScurView.rebuild restartBundleTree
    dsimp only [sv, X]
    rw [hHE_eq, Finset.union_assoc]
  exact hEq ▸ hmain

end MinCostFlow.SparseCore.Program.Read
