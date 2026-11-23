module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepRel
public import MinCostFlow.SparseCore.CanonCoreSpec

import Mathlib.Tactic

/-!
# Pure model bridge for the block-by-block tour step (`AssemblyFirstTourStepChain`)

Connects `CompLSFInv`, `OrderedBatch`, `OrdEditsForBatch`, `canonSplitList`, and
`restrictSplits keep (canonCoreBatch cs U)` to `TourRelChain` and the four per-update cases of
`asmFirstTourBlockStepStmt`:

1. **`GraphEq` transport for rooted forests** (`graphEq_connected_iff`, `graphEq_eraseForestEdge`,
   `graphEq_root_eq`) and `TourRelChain` concatenation (`tourRelChain_append`).
2. **Release-chain construction (`tourRelChain_of_releasesBatch`)**:
   proves that `releasesSplitEntries final.R L cuts` and
   `restrictSplits keep (releasesBatch G final.R L cuts)` form a valid `TourRelChain`.
3. **Quiet-prefix splitting (`isQuietUpdate`, `splitQuietPrefix`, `splitLeadingReleases_canonSplitList`,
   `tourRelChain_of_quietPrefix`)**: splits any remaining batch `U` into a prefix `U_quiet` of
   `.insert` and non-forest `.delete` updates (whose leading releases are all consumed up front by
   `asmFirstTourConsumeRelStmt`) followed by `U_rest` starting at a forest `.delete` or `.split` wall.
4. **Per-update synchronization**:
   - quiet `.insert` (`tourStep_quiet_insert_sync`),
   - quiet non-forest `.delete` (`tourStep_quiet_delete_sync`),
   - wall forest `.delete` (`tourStep_wall_forestDelete_sync`),
   - wall `.split` (`tourStep_wall_split_sync`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. `GraphEq` transport and `TourRelChain` concatenation -/

public section

theorem graphEq_connected_iff {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) {u v : ℕ} :
    G₁.Connected u v ↔ G₂.Connected u v :=
  ⟨connected_of_subgraph ⟨h.1.le, h.2.1.le, h.2.2⟩,
   connected_of_subgraph ⟨h.1.symm.le, h.2.1.symm.le, fun e he =>
     let ⟨h1, h2⟩ := h.2.2 e (h.2.1.symm ▸ he); ⟨h1.symm, h2.symm⟩⟩⟩

theorem graphEq_eraseForestEdge {F₁ F₂ : MGraph} (h : GraphEq F₁ F₂) (e : ℕ) :
    GraphEq (eraseForestEdge F₁ e) (eraseForestEdge F₂ e) := by
  refine ⟨h.1, ?_, fun f hf => h.2.2 f (Finset.mem_of_mem_erase hf)⟩
  change F₁.E.erase e = F₂.E.erase e
  rw [h.2.1]

theorem graphEq_root_eq {rf₁ rf₂ : RootedForest} (hF : GraphEq rf₁.F rf₂.F) (hR : rf₁.R = rf₂.R)
    {v : ℕ} : rf₁.root v = rf₂.root v := by
  classical
  unfold RootedForest.root
  have hfun : (fun r => r ∈ rf₁.R ∧ rf₁.F.Connected v r) =
      (fun r => r ∈ rf₂.R ∧ rf₂.F.Connected v r) :=
    funext fun r => propext (by rw [hR, graphEq_connected_iff hF])
  simp only [hfun]

theorem tourRelChain_append {vCap eCap : ℕ} {keep M : Finset ℕ}
    {s₀ s₁ s₂ : TourAbs} {S₀ S₁ S₂ : MGraph}
    {rels₁ rels₂ : List CompSplitEntry} {Ps₁ Ps₂ : List Update}
    (h₁ : TourRelChain vCap eCap keep M s₀ S₀ rels₁ Ps₁ s₁ S₁)
    (h₂ : TourRelChain vCap eCap keep M s₁ S₁ rels₂ Ps₂ s₂ S₂) :
    TourRelChain vCap eCap keep M s₀ S₀ (rels₁ ++ rels₂) (Ps₁ ++ Ps₂) s₂ S₂ := by
  induction h₁ with
  | nil _ _ => simpa using h₂
  | cons he heM hkept hfrLt hfrV hfrNotR huniq hSt hSh _ ih =>
    exact TourRelChain.cons he heM hkept hfrLt hfrV hfrNotR huniq hSt hSh (ih h₂)

/-! ## 2. Release-chain construction for `releasesBatch` -/

theorem restrictSplits_append (keep : Finset ℕ) (U₁ U₂ : List Update) :
    restrictSplits keep (U₁ ++ U₂) = restrictSplits keep U₁ ++ restrictSplits keep U₂ := by
  induction U₁ with
  | nil => rfl
  | cons u U₁ ih => cases u <;> simp [restrictSplits, ih]

/-- Releasing the forest edges `cuts` from `L` to `final` builds a `TourRelChain` matching
`releasesSplitEntries final.R L cuts` and `restrictSplits keep (releasesBatch G final.R L cuts)`. -/
theorem tourRelChain_of_releasesBatch {vCap eCap : ℕ} {keep M : Finset ℕ}
    {G : MGraph} {final : RootedForest}
    (hFinal : final.IsRootedSpanningForestOf G)
    (hR_lt : ∀ r ∈ final.R, r < vCap) :
    ∀ (cuts : List ℕ) (L : LSF) (s : TourAbs) (S : MGraph),
      L.F.IsRootedSpanningForestOf G →
      L.F.R ⊆ final.R →
      cuts.foldl eraseForestEdge L.F.F = final.F →
      (∀ e ∈ cuts, e ∈ L.F.F.E) →
      cuts.Nodup →
      TourValid vCap eCap s →
      GraphEq s.rf.F L.F.F →
      s.rf.R = L.F.R →
      TourMarksAt s M →
      (∀ e ∈ cuts, e ∉ M) →
      TourKeepMatch keep s S →
      (∀ f ∈ keep, f ∈ G.E ∧ ordSrc s.ord (f, true) = G.tail f ∧ ordSrc s.ord (f, false) = G.head f) →
      ∃ s_f S_f,
        TourRelChain vCap eCap keep M s S
          (releasesSplitEntries final.R L cuts)
          (restrictSplits keep (releasesBatch G final.R L cuts)) s_f S_f ∧
        s_f.ord = s.ord ∧ s_f.marked = s.marked ∧
        GraphEq s_f.rf.F final.F ∧ s_f.rf.R = final.R ∧
        TourValid vCap eCap s_f ∧ TourMarksAt s_f M ∧ TourKeepMatch keep s_f S_f := by
  intro cuts
  induction cuts with
  | nil =>
    intro L s S hF hR hCut _ _ hv hFeq hReq hM _ hK _
    have hFE : L.F.F = final.F := hCut
    have hRC : L.F.R.card = final.R.card := by
      rw [← rootedForest_components_card hF, ← rootedForest_components_card hFinal, hFE]
    have hRE : L.F.R = final.R := Finset.eq_of_subset_of_card_le hR hRC.ge
    exact ⟨s, S, .nil s S, rfl, rfl, hFE ▸ hFeq, hReq.trans hRE, hv, hM, hK⟩
  | cons e cuts ih =>
    intro L s S hF hR hCut hMem hNd hv hFeq hReq hM hMdisj hK hkeepG
    have heL : e ∈ L.F.F.E := hMem e List.mem_cons_self
    have heS : e ∈ s.rf.F.E := hFeq.2.1.symm ▸ heL
    have heM : e ∉ M := hMdisj e List.mem_cons_self
    let K := eraseForestEdge L.F.F e
    have hKn : K.IsForest := isForest_eraseEdge hF.1 e
    have hKV : K.V = G.V := hF.2.1
    have hKsub : L.F.F.IsSubgraph K := eraseForestEdge_subgraph _ _
    have hKG : G.IsSubgraph K :=
      ⟨hF.2.2.2.2.1, fun _ hf => hF.2.2.2.2.2.1 (Finset.mem_of_mem_erase hf),
        fun f hf => hF.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    have hrest : cuts.foldl eraseForestEdge K = final.F := hCut
    have hFinalK : K.IsSubgraph final.F := by
      rw [← hrest, foldl_eraseForestEdge]
      exact ⟨Finset.Subset.rfl, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hsep : ∀ a ∈ L.F.R, ∀ b ∈ L.F.R, K.Connected a b → a = b := by
      intro a ha b hb hConn
      have hr := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb)
        (connected_of_subgraph hKsub hConn)
      rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hr
    obtain ⟨hIncl, hSub, hMid⟩ := canonRoots_spec hKn hKV hKG hFinal hFinalK hR hsep
    let Lmid : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R final.R⟩, L.wstr⟩
    have hRc : (canonRoots K L.F.R final.R).card = L.F.R.card + 1 := by
      rw [← rootedForest_components_card hMid, ← rootedForest_components_card hF]
      exact forest_eraseEdge_components_card hF.1 heL
    obtain ⟨fresh, hfrNotL, hReqMid⟩ := roots_insert_of_card hIncl hRc
    have hnew : newRoot Lmid.F.R L.F.R = fresh := newRoot_eq hReqMid hfrNotL
    have hfrLt : fresh < vCap := hR_lt fresh (hSub (hReqMid ▸ Finset.mem_insert_self _ _))
    have hfrV : fresh ∈ s.rf.F.V := by
      rw [hFeq.1, hF.2.1]
      exact hFinal.2.2.1 (hSub (hReqMid ▸ Finset.mem_insert_self _ _))
    have hfrNotR : fresh ∉ s.rf.R := hReq ▸ hfrNotL
    have hKeq : GraphEq (eraseForestEdge s.rf.F e) K := graphEq_eraseForestEdge hFeq e
    have huniq' : ∀ v ∈ s.rf.F.V,
        ∃! r, r ∈ insert fresh s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r := by
      intro v hvV
      have hvG : v ∈ G.V := hF.2.1 ▸ hFeq.1 ▸ hvV
      obtain ⟨r, ⟨hrR, hvr⟩, hru⟩ := hMid.2.2.2.1 v hvG
      refine ⟨r, ⟨by rwa [hReq, ← hReqMid], (graphEq_connected_iff hKeq).mpr hvr⟩, ?_⟩
      intro r' ⟨hr'R, hvr'⟩
      exact hru r' ⟨by rwa [hReqMid, ← hReq], (graphEq_connected_iff hKeq).mp hvr'⟩
    have hkept_eq : L.F.root (L.F.F.tail e) = s.rf.root (s.rf.F.tail e) := by
      rw [(hFeq.2.2 e heS).1]
      exact (graphEq_root_eq hFeq hReq).symm
    set s₁ := tourCut s e fresh
    have hF1_eq : GraphEq s₁.rf.F Lmid.F.F := hKeq
    have hR1_eq : s₁.rf.R = Lmid.F.R := by
      change insert fresh s.rf.R = canonRoots K L.F.R final.R
      rw [hReq, hReqMid]
    have hSt : ∀ f ∈ keep,
        f ∈ ((coreGraph G L).E.filter fun x => (coreGraph (G.applyUpdate (.delete e)) Lmid).tail x = fresh) ↔
        s₁.rf.root (ordSrc s.ord (f, true)) = fresh := by
      intro f hf
      have hfG := (hkeepG f hf).1
      have hfOpen : f ∉ L.F.F.E := hFeq.2.1 ▸ (hK.2 (f, true) hf).2.1
      have hfCore : f ∈ (coreGraph G L).E := Finset.mem_sdiff.mpr ⟨hfG, hfOpen⟩
      simp only [Finset.mem_filter, hfCore, true_and]
      change Lmid.F.root (G.tail f) = fresh ↔ s₁.rf.root (ordSrc s.ord (f, true)) = fresh
      rw [(hkeepG f hf).2.1, graphEq_root_eq hF1_eq hR1_eq]
    have hSh : ∀ f ∈ keep,
        f ∈ ((coreGraph G L).E.filter fun x => (coreGraph (G.applyUpdate (.delete e)) Lmid).head x = fresh) ↔
        s₁.rf.root (ordSrc s.ord (f, false)) = fresh := by
      intro f hf
      have hfG := (hkeepG f hf).1
      have hfOpen : f ∉ L.F.F.E := hFeq.2.1 ▸ (hK.2 (f, false) hf).2.1
      have hfCore : f ∈ (coreGraph G L).E := Finset.mem_sdiff.mpr ⟨hfG, hfOpen⟩
      simp only [Finset.mem_filter, hfCore, true_and]
      change Lmid.F.root (G.head f) = fresh ↔ s₁.rf.root (ordSrc s.ord (f, false)) = fresh
      rw [(hkeepG f hf).2.2, graphEq_root_eq hF1_eq hR1_eq]
    obtain ⟨hv1, hM1, hK1, _, _, _⟩ :=
      tourCut_split_sync hv hM hK heS heM hkept_eq hfrV hfrNotR huniq' hSt hSh
    have hMemRest : ∀ f ∈ cuts, f ∈ K.E := fun f hf =>
      Finset.mem_erase.mpr ⟨fun h => (List.nodup_cons.mp hNd).1 (h ▸ hf),
        hMem f (List.mem_cons_of_mem _ hf)⟩
    have hMdisjRest : ∀ f ∈ cuts, f ∉ M := fun f hf => hMdisj f (List.mem_cons_of_mem _ hf)
    set St := (coreGraph G L).E.filter fun x => (coreGraph (G.applyUpdate (.delete e)) Lmid).tail x = fresh
    set Sh := (coreGraph G L).E.filter fun x => (coreGraph (G.applyUpdate (.delete e)) Lmid).head x = fresh
    set S₁ := S.applyUpdate (.split (L.F.root (L.F.F.tail e)) fresh (St ∩ keep) (Sh ∩ keep))
    obtain ⟨s_f, S_f, hchRest, hord_f, hmk_f, hFf, hRf, hvf, hMf, hKf⟩ :=
      ih Lmid s₁ S₁ hMid hSub hrest hMemRest (List.nodup_cons.mp hNd).2 hv1 hF1_eq hR1_eq
        hM1 hMdisjRest hK1 hkeepG
    refine ⟨s_f, S_f, ?_, hord_f, hmk_f, hFf, hRf, hvf, hMf, hKf⟩
    simp only [releasesSplitEntries, releasesBatch, refineSplit, restrictSplits]
    rw [hnew]
    exact TourRelChain.cons heS heM hkept_eq hfrLt hfrV hfrNotR huniq' hSt hSh hchRest

/-! ## 3. Quiet-prefix splitting and leading releases -/

/-- Whether input update `u` on `cs` has no input split (`inputSplitEntries cs u = []`):
either `.insert` or a non-forest `.delete`. -/
@[expose] noncomputable def isQuietUpdate (cs : CompLSFState) : Update → Bool
  | .insert _ _ _ => true
  | .delete e => by classical exact decide (e ∉ cs.RF.F.E)
  | .split _ _ _ _ => false

/-- Split `U` into its maximal leading prefix of quiet updates (`isQuietUpdate = true`) and the
remaining suffix (either `[]` or starting with a forest `.delete` or `.split` wall). -/
@[expose] noncomputable def splitQuietPrefix (cs : CompLSFState) :
    List Update → List Update × List Update
  | [] => ([], [])
  | u :: U =>
    if isQuietUpdate cs u then
      let p := splitQuietPrefix (compLSFStepSingle cs u) U
      (u :: p.1, p.2)
    else
      ([], u :: U)

theorem splitQuietPrefix_append (cs : CompLSFState) (U : List Update) :
    (splitQuietPrefix cs U).1 ++ (splitQuietPrefix cs U).2 = U := by
  induction U generalizing cs with
  | nil => rfl
  | cons u U ih =>
    unfold splitQuietPrefix
    split_ifs
    · simp only [List.cons_append, List.cons.injEq, true_and]; exact ih _
    · rfl

theorem asmFirstCanonSplitList_append (cs : CompLSFState) (U₁ U₂ : List Update) :
    canonSplitList cs (U₁ ++ U₂) =
      canonSplitList cs U₁ ++ canonSplitList (compLSFBatch cs U₁) U₂ := by
  induction U₁ generalizing cs with
  | nil => rfl
  | cons u U₁ ih =>
    simp only [List.cons_append, canonSplitList, compLSFBatch, List.foldl_cons,
      List.append_assoc]
    exact congrArg (canonStepSplits cs u ++ ·) (ih (compLSFStepSingle cs u))

theorem canonCoreBatch_append (cs : CompLSFState) (U₁ U₂ : List Update) :
    canonCoreBatch cs (U₁ ++ U₂) =
      canonCoreBatch cs U₁ ++ canonCoreBatch (compLSFBatch cs U₁) U₂ := by
  induction U₁ generalizing cs with
  | nil => rfl
  | cons u U₁ ih =>
    simp only [List.cons_append, canonCoreBatch, compLSFBatch, List.foldl_cons, List.append_assoc]
    exact congrArg (canonStepCore cs u ++ ·) (ih (compLSFStepSingle cs u))

theorem asmFirstInputSplitEntries_eq_nil_of_quiet {cs : CompLSFState} {u : Update}
    (hq : isQuietUpdate cs u = true) : inputSplitEntries cs u = [] := by
  cases u with
  | insert _ _ _ => rfl
  | delete e =>
    simp only [isQuietUpdate, decide_eq_true_eq] at hq
    simp [inputSplitEntries, hq]
  | split _ _ _ _ => simp [isQuietUpdate] at hq

theorem asmFirstInputSplitEntries_head_false_of_not_quiet {cs : CompLSFState} {u : Update}
    (hnq : isQuietUpdate cs u = false) :
    ∃ kept fresh, inputSplitEntries cs u = [⟨false, 0, kept, fresh⟩] := by
  cases u with
  | insert _ _ _ => simp [isQuietUpdate] at hnq
  | delete e =>
    simp only [isQuietUpdate, decide_eq_false_iff_not, not_not] at hnq
    refine ⟨cs.RF.root (cs.RF.F.tail e), newRoot (inputMid cs (.delete e)).F.R cs.RF.R, ?_⟩
    simp [inputSplitEntries, hnq]
  | split v _ _ _ =>
    exact ⟨_, _, rfl⟩

private lemma splitLeadingReleases_nil_eq : splitLeadingReleases [] = ([], []) := by
  have h := splitLeadingReleases_append []
  rcases List.append_eq_nil_iff.mp h with ⟨h1, h2⟩
  exact Prod.ext h1 h2

private lemma splitLeadingReleases_cons_false {e : CompSplitEntry}
    (he : e.isRelease = false) (rest : List CompSplitEntry) :
    splitLeadingReleases (e :: rest) = ([], e :: rest) := by
  have h := splitLeadingReleases_append (e :: rest)
  cases h1 : (splitLeadingReleases (e :: rest)).1 with
  | nil => rw [h1, List.nil_append] at h; exact Prod.ext h1 h
  | cons a as =>
    rw [h1, List.cons_append] at h
    have ha : a = e := (List.cons.inj h).1
    have ht := splitLeadingReleases_fst_true (e :: rest) a (by rw [h1]; exact List.mem_cons_self)
    rw [ha, he] at ht; cases ht

/-- `splitLeadingReleases` on `canonSplitList cs U` matches `splitQuietPrefix cs U`. -/
theorem splitLeadingReleases_canonSplitList (cs : CompLSFState) (U : List Update) :
    splitLeadingReleases (canonSplitList cs U) =
      (canonSplitList cs (splitQuietPrefix cs U).1,
       canonSplitList (compLSFBatch cs (splitQuietPrefix cs U).1)
         (splitQuietPrefix cs U).2) := by
  induction U generalizing cs with
  | nil => simpa [canonSplitList, splitQuietPrefix] using splitLeadingReleases_nil_eq
  | cons u U ih =>
    unfold splitQuietPrefix
    by_cases hq : isQuietUpdate cs u = true
    · simp only [hq, ↓reduceIte]
      have hnil := asmFirstInputSplitEntries_eq_nil_of_quiet hq
      have hstep : canonStepSplits cs u =
          releasesSplitEntries (compLSFStepSingle cs u).RF.R (inputMid cs u)
            (((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·)) := by
        simp [canonStepSplits, hnil]
      have hall := asmFirstReleasesSplitEntries_all_true (compLSFStepSingle cs u).RF.R (inputMid cs u)
        (((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·))
      simp only [canonSplitList, compLSFBatch, List.foldl_cons]
      rw [hstep, splitLeadingReleases_of_all_true hall, ih (compLSFStepSingle cs u)]; rfl
    · have hnq : isQuietUpdate cs u = false := by cases h : isQuietUpdate cs u <;> simp_all
      simp only [hnq, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨kept, fresh, hhead⟩ := asmFirstInputSplitEntries_head_false_of_not_quiet hnq
      simp only [canonSplitList, canonStepSplits, hhead, List.cons_append,
        List.nil_append, compLSFBatch, List.foldl_nil]
      exact splitLeadingReleases_cons_false (e := ⟨false, 0, kept, fresh⟩) rfl _

/-- Single-step forest and release properties of `compLSFStepSingle cs u`. -/
theorem compLSFStepSingle_forest_props {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    let cs' := compLSFStepSingle cs u
    let K := forestAfterInput cs.RF.F u
    let cuts := (K.E \ cs'.RF.F.E).sort (· ≤ ·)
    let Fc := cuts.foldl eraseForestEdge K
    CompLSFInv C_lsst ℓ₀ cs' ∧
    cs'.G = cs.G.applyUpdate u ∧
    cs.RF.R ⊆ cs'.RF.R ∧
    K.IsForest ∧ cs'.G.IsSubgraph K ∧ K.IsSubgraph cs'.RF.F ∧
    GraphEq Fc cs'.RF.F ∧
    (RootedForest.mk Fc cs'.RF.R).IsRootedSpanningForestOf cs'.G ∧
    (∀ e ∈ cuts, e ∈ K.E) ∧
    cuts.Nodup := by
  intro cs' K cuts Fc
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hG' : cs'.G = cs.G.applyUpdate u := by
    have := (compLSFBatch_step_props [u] hI ⟨hu, trivial⟩).2.1
    simpa [compLSFBatch, MGraph.applyBatch] using this
  have hdec := compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩
  have hF0 := compLSF_RF_isRSF hI
  have hF' := compLSF_RF_isRSF hI'
  have hKV : K.V = cs'.G.V := by
    rw [hG']
    cases u with
    | insert => exact hF0.2.1
    | delete => exact hF0.2.1
    | split v v' St Sh => change insert v' cs.RF.F.V = insert v' cs.G.V; rw [hF0.2.1]
  have hEsub : cs'.RF.F.E ⊆ K.E := by
    intro e he
    have he0 : e ∈ cs.RF.F.E := hdec.1 he
    cases u with
    | insert _ _ _ => exact he0
    | delete d =>
      have heG' : e ∈ cs'.G.E := hF'.2.2.2.2.2.1 he
      rw [hG'] at heG'
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp heG').1, he0⟩
    | split _ _ _ _ => exact he0
  have hKends : ∀ e ∈ K.E, K.tail e = cs'.G.tail e ∧ K.head e = cs'.G.head e := by
    intro e he
    rw [hG']
    cases u with
    | insert f a b =>
      have hne : e ≠ f := fun h => hu.1 (h ▸ hF0.2.2.2.2.2.1 he)
      have he0 := hF0.2.2.2.2.2.2 e he
      simp [K, forestAfterInput, MGraph.applyUpdate, Function.update_of_ne hne, he0.1, he0.2]
    | delete d => exact hF0.2.2.2.2.2.2 e (Finset.mem_of_mem_erase he)
    | split v v' St Sh =>
      have he0 := hF0.2.2.2.2.2.2 e he
      simp [K, forestAfterInput, MGraph.applyUpdate, he0.1, he0.2]
  have hKG : cs'.G.IsSubgraph K := by
    refine ⟨hKV.symm ▸ Finset.Subset.rfl, ?_, hKends⟩
    intro e he
    rw [hG']
    cases u with
    | insert f a b => exact Finset.mem_insert_of_mem (hF0.2.2.2.2.2.1 he)
    | delete d =>
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he).1,
        hF0.2.2.2.2.2.1 (Finset.mem_of_mem_erase he)⟩
    | split v v' St Sh => exact hF0.2.2.2.2.2.1 he
  have hKsub' : K.IsSubgraph cs'.RF.F := by
    refine ⟨by rw [hF'.2.1, hKV], hEsub, fun e he => ?_⟩
    have h1 := hF'.2.2.2.2.2.2 e he
    have h2 := hKends e (hEsub he)
    exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩
  have hKF : K.IsForest := by
    cases u with
    | insert _ _ _ => exact hF0.1
    | delete d => exact isForest_eraseEdge hF0.1 d
    | split v v' St Sh =>
      exact applyUpdate_split_isForest hF0.1 (hF0.2.1.symm ▸ hu.1) (fun h => hu.2.1 (hF0.2.1 ▸ h)) St Sh
  have hEqF : GraphEq Fc cs'.RF.F := by
    refine ⟨by simp [Fc, foldl_eraseForestEdge, hKV, hF'.2.1], ?_, fun f hf => ?_⟩
    · simp only [Fc, cuts, foldl_eraseForestEdge, Finset.sort_toFinset]
      exact Finset.sdiff_sdiff_eq_self hEsub
    · have hf' : f ∈ cs'.RF.F.E := by
        simp only [Fc, cuts, foldl_eraseForestEdge, Finset.sort_toFinset] at hf
        rwa [Finset.sdiff_sdiff_eq_self hEsub] at hf
      have h2 := hKsub'.2.2 f hf'
      simp only [Fc, foldl_eraseForestEdge]
      exact ⟨h2.1.symm, h2.2.symm⟩
  have hFcRSF : (RootedForest.mk Fc cs'.RF.R).IsRootedSpanningForestOf cs'.G :=
    isRootedSpanningForestOf_congr hF' rfl (graphEq_symm hEqF)
  exact ⟨hI', hG', hdec.2, hKF, hKG, hKsub', hEqF, hFcRSF,
    fun e he => (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1, Finset.sort_nodup _ _⟩

/-- Every quiet prefix `U_quiet` (all updates have `isQuietUpdate = true`) yields a single
`TourRelChain` matching `canonSplitList cs U_quiet` and
`restrictSplits keep (canonCoreBatch cs U_quiet)`, advancing `s.rf` to `(compLSFBatch cs U_quiet).RF`
while leaving `s.ord` and `s.marked` unchanged. -/
theorem tourRelChain_of_quietPrefix {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {vCap eCap : ℕ}
    {keep M : Finset ℕ} :
    ∀ (Uq : List Update) (cs : CompLSFState) (s : TourAbs) (S : MGraph),
      CompLSFInv C_lsst ℓ₀ cs →
      cs.G.BatchIsValid Uq →
      (∀ i (hi : i < Uq.length), isQuietUpdate (compLSFBatch cs (Uq.take i)) Uq[i] = true) →
      (∀ r ∈ (compLSFBatch cs Uq).RF.R, r < vCap) →
      TourValid vCap eCap s →
      GraphEq s.rf.F cs.RF.F →
      s.rf.R = cs.RF.R →
      TourMarksAt s M →
      Disjoint M cs.RF.F.E →
      TourKeepMatch keep s S →
      Disjoint keep (batchDeletes Uq) →
      (∀ f ∈ keep, f ∈ cs.G.E ∧ ordSrc s.ord (f, true) = cs.G.tail f ∧ ordSrc s.ord (f, false) = cs.G.head f) →
      ∃ s_f S_f,
        TourRelChain vCap eCap keep M s S
          (canonSplitList cs Uq)
          (restrictSplits keep (canonCoreBatch cs Uq)) s_f S_f ∧
        s_f.ord = s.ord ∧ s_f.marked = s.marked ∧
        GraphEq s_f.rf.F (compLSFBatch cs Uq).RF.F ∧ s_f.rf.R = (compLSFBatch cs Uq).RF.R ∧
        TourValid vCap eCap s_f ∧ TourMarksAt s_f M ∧ TourKeepMatch keep s_f S_f := by
  intro Uq
  induction Uq with
  | nil =>
    intro cs s S _ _ _ _ hv hFeq hReq hM _ hK _ _
    exact ⟨s, S, .nil s S, rfl, rfl, hFeq, hReq, hv, hM, hK⟩
  | cons u Uq ih =>
    intro cs s S hI hBU hQuiet hR_lt hv hFeq hReq hM hMdisj hK hKdisj hkeepG
    have hq0 : isQuietUpdate cs u = true := by
      simpa [compLSFBatch] using hQuiet 0 (Nat.zero_lt_succ _)
    have hBU1 : cs.G.UpdateIsValid u := hBU.1
    obtain ⟨hI1, hG1, hR01, hKF, hKG, _, hEqF1, hFcRSF1, hcutsMem, hcutsNd⟩ :=
      compLSFStepSingle_forest_props hI hBU1
    set cs1 := compLSFStepSingle cs u
    have hBUrest : cs1.G.BatchIsValid Uq := hG1.symm ▸ hBU.2
    have hR1_lt : ∀ r ∈ cs1.RF.R, r < vCap := fun r hr =>
      hR_lt r ((compLSFBatch_decremental hI1 hBUrest).2 hr)
    have hmid_eq : inputMid cs u = cs.lsf := by
      cases u with
      | insert _ _ _ => rfl
      | delete e =>
        simp only [isQuietUpdate, decide_eq_true_eq] at hq0
        simp [inputMid, hq0]
      | split _ _ _ _ => simp [isQuietUpdate] at hq0
    have hK_eq : forestAfterInput cs.RF.F u = cs.RF.F := by
      cases u with
      | insert _ _ _ => rfl
      | delete e =>
        simp only [isQuietUpdate, decide_eq_true_eq] at hq0
        change { cs.RF.F with E := cs.RF.F.E.erase e } = cs.RF.F
        rw [Finset.erase_eq_of_notMem hq0]
      | split _ _ _ _ => simp [isQuietUpdate] at hq0
    have hF0 := compLSF_RF_isRSF hI
    have hF0_G1 : cs.lsf.F.IsRootedSpanningForestOf cs1.G := by
      have hKG' : cs1.G.IsSubgraph cs.RF.F := hK_eq ▸ hKG
      have hV' : cs.RF.F.V = cs1.G.V := by
        rw [hG1]
        cases u with
        | insert => exact hF0.2.1
        | delete => exact hF0.2.1
        | split => simp [isQuietUpdate] at hq0
      exact ⟨hF0.1, hV', fun _ hr => hV' ▸ hF0.2.2.1 hr, fun v hv => hF0.2.2.2.1 v (hV' ▸ hv), hKG'⟩
    have hkeepG1 : ∀ f ∈ keep, f ∈ cs1.G.E ∧ ordSrc s.ord (f, true) = cs1.G.tail f ∧
        ordSrc s.ord (f, false) = cs1.G.head f := by
      intro f hf
      obtain ⟨hfG, hft, hfh⟩ := hkeepG f hf
      rw [hG1]
      cases u with
      | insert e a b =>
        have hne : f ≠ e := fun h => hBU1.1 (h ▸ hfG)
        exact ⟨Finset.mem_insert_of_mem hfG,
          by simpa [MGraph.applyUpdate, Function.update_of_ne hne] using hft,
          by simpa [MGraph.applyUpdate, Function.update_of_ne hne] using hfh⟩
      | delete e =>
        have hne : f ≠ e := fun h =>
          Finset.disjoint_left.mp hKdisj hf (by rw [h]; exact (mem_batchDeletes_iff _ _).mpr ⟨.delete e, List.mem_cons_self, rfl⟩)
        exact ⟨Finset.mem_erase.mpr ⟨hne, hfG⟩, hft, hfh⟩
      | split _ _ _ _ => simp [isQuietUpdate] at hq0
    set cuts := ((forestAfterInput cs.RF.F u).E \ cs1.RF.F.E).sort (· ≤ ·)
    have hMcuts : ∀ e ∈ cuts, e ∉ M := fun e he => by
      have he0 : e ∈ cs.RF.F.E := hK_eq ▸ hcutsMem e he
      exact Finset.disjoint_right.mp hMdisj he0
    obtain ⟨s1, S1, hch1, hord1, hmk1, hF1, hR1, hv1, hM1, hK1⟩ :=
      tourRelChain_of_releasesBatch (G := cs1.G) (final := ⟨cuts.foldl eraseForestEdge cs.RF.F, cs1.RF.R⟩)
        (hK_eq ▸ hFcRSF1) hR1_lt cuts cs.lsf s S hF0_G1 hR01 rfl (hK_eq ▸ hcutsMem) hcutsNd
        hv hFeq hReq hM hMcuts hK hkeepG1
    have hF1_cs1 : GraphEq s1.rf.F cs1.RF.F := graphEq_trans hF1 (hK_eq ▸ hEqF1)
    have hMdisj1 : Disjoint M cs1.RF.F.E :=
      Disjoint.mono_right (compLSFBatch_decremental (U := [u]) hI ⟨hBU1, trivial⟩).1 hMdisj
    have hKdisj1 : Disjoint keep (batchDeletes Uq) :=
      Disjoint.mono_right (fun e he => by
        obtain ⟨u', hu', h⟩ := (mem_batchDeletes_iff _ _).mp he
        exact (mem_batchDeletes_iff _ _).mpr ⟨u', List.mem_cons_of_mem _ hu', h⟩) hKdisj
    have hQuiet1 : ∀ i (hi : i < Uq.length), isQuietUpdate (compLSFBatch cs1 (Uq.take i)) Uq[i] = true :=
      fun i hi => by
        have := hQuiet (i + 1) (Nat.succ_lt_succ hi)
        simpa [compLSFBatch, List.take_succ_cons, cs1] using this
    obtain ⟨s_f, S_f, hch2, hord2, hmk2, hFf, hRf, hvf, hMf, hKf⟩ :=
      ih cs1 s1 S1 hI1 hBUrest hQuiet1 hR_lt hv1 hF1_cs1 hR1 hM1 hMdisj1 hK1 hKdisj1
        (by rw [hord1]; exact hkeepG1)
    have hstep_sp : canonStepSplits cs u =
        releasesSplitEntries cs1.RF.R cs.lsf cuts := by
      simp [canonStepSplits, asmFirstInputSplitEntries_eq_nil_of_quiet hq0, hmid_eq, cs1, cuts]
    have hstep_rs : restrictSplits keep (canonStepCore cs u) =
        restrictSplits keep (releasesBatch cs1.G cs1.RF.R cs.lsf cuts) := by
      rw [canonStepCore, restrictSplits_append, hmid_eq, ← hG1]
      have hin : restrictSplits keep (inputCoreBatch cs u) = [] := by
        cases u with
        | insert _ _ _ => rfl
        | delete e =>
          simp only [isQuietUpdate, decide_eq_true_eq] at hq0
          simp [inputCoreBatch, hq0, restrictSplits]
        | split _ _ _ _ => simp [isQuietUpdate] at hq0
      rw [hin, List.nil_append]
    refine ⟨s_f, S_f, ?_, hord2.trans hord1, hmk2.trans hmk1, hFf, hRf, hvf, hMf, hKf⟩
    simp only [canonSplitList, canonCoreBatch, restrictSplits_append, hstep_sp, hstep_rs]
    exact tourRelChain_append hch1 hch2

/-! ## 4. Per-update synchronization for the four cases of `asmFirstTourBlockStepStmt` -/

/-- Case 1: quiet `.insert e a b` on top of an already-cut release forest `s.rf`
(same vertices `s.rf.F.V = G.V`, forest edges `s.rf.F.E ⊆ G.E`). -/
theorem tourStep_quiet_insert_sync {vCap eCap e a b : ℕ} {y₁ y₂ : Option End}
    {s : TourAbs} {keep M : Finset ℕ} {S G : MGraph}
    (hv : TourValid vCap eCap s)
    (he_lt : e < eCap) (ha_lt : a < vCap) (hb_lt : b < vCap)
    (heG : e ∉ G.E) (heF : e ∉ s.rf.F.E) (haV : a ∈ s.rf.F.V) (hbV : b ∈ s.rf.F.V)
    (hordG : ∀ v x, x ∈ s.ord v ↔ x.1 ∈ G.E ∧ G.src x = v)
    (hy1 : ∀ y, y₁ = some y → y.1 < eCap)
    (hy2 : ∀ y, y₂ = some y → y.1 < eCap)
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S) (heM : e ∉ M) (hek : e ∉ keep) :
    let eds := [.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]
    let s' := tourApplyEdits s eds
    TourEditsValid vCap eCap s eds ∧
    TourValid vCap eCap s' ∧
    TourMarksAt s' M ∧
    TourKeepMatch keep s' S ∧
    tourMarkPot keep s' = tourMarkPot keep s := by
  intro eds s'
  have hnot_mem : ∀ x : End, x.1 = e → ∀ u, x ∉ s.ord u := fun x hx u hu =>
    heG (hx ▸ ((hordG u x).mp hu).1)
  have hev1 : TourEditValid vCap eCap s (.insertBefore a (e, true) y₁) :=
    ⟨ha_lt, haV, he_lt, heF, hnot_mem (e, true) rfl, fun y hy => hy1 y (Option.mem_def.mp hy)⟩
  have hv1 : TourValid vCap eCap (tourApplyEdit s (.insertBefore a (e, true) y₁)) :=
    tourValid_applyEdit_insertBefore hv hev1
  have hnot2 : ∀ u, (e, false) ∉ applyOrdEdit s.ord (.insertBefore a (e, true) y₁) u := by
    intro u hu
    simp only [applyOrdEdit] at hu
    by_cases hua : u = a
    · subst hua; simp only [Function.update_self] at hu
      have : (e, false) ∈ s.ord u := by
        cases y₁ with
        | none =>
          simp only [insertBeforeList, List.mem_append, List.mem_singleton] at hu
          exact hu.resolve_right (fun h => by cases h)
        | some y0 =>
          simp only [insertBeforeList, List.mem_append, List.mem_cons] at hu
          rcases hu with h1 | h2 | h3
          · exact List.mem_of_mem_take h1
          · cases h2
          · exact List.mem_of_mem_drop h3
      exact hnot_mem (e, false) rfl u this
    · simp only [Function.update_of_ne hua] at hu
      exact hnot_mem (e, false) rfl u hu
  have hev2 : TourEditValid vCap eCap (tourApplyEdit s (.insertBefore a (e, true) y₁))
      (.insertBefore b (e, false) y₂) :=
    ⟨hb_lt, hbV, he_lt, heF, hnot2, fun y hy => hy2 y (Option.mem_def.mp hy)⟩
  have hv' : TourValid vCap eCap s' := tourValid_applyEdit_insertBefore hv1 hev2
  have hmp := tourMarkPot_insert hv hv' hM hK heM hek
  exact ⟨⟨hev1, hev2, trivial⟩, hv', hmp.1, hmp.2.1, hmp.2.2⟩

/-- Case 2: quiet non-forest `.delete e` (`e ∉ s.rf.F.E`) on top of an already-cut release forest. -/
theorem tourStep_quiet_delete_sync {vCap eCap e : ℕ}
    {s : TourAbs} {keep M : Finset ℕ} {S : MGraph}
    (hv : TourValid vCap eCap s) (he_lt : e < eCap) (heOpen : e ∉ s.rf.F.E)
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S) (hek : e ∉ keep) :
    let s' := tourApplyEdit s (.dropEdge e)
    TourEditsValid vCap eCap s [.dropEdge e] ∧
    TourValid vCap eCap s' ∧
    TourMarksAt s' (M.erase e) ∧
    TourKeepMatch keep s' S ∧
    tourMarkPot keep s' ≤ tourMarkPot keep s := by
  intro s'
  have hev : TourEditValid vCap eCap s (.dropEdge e) := ⟨he_lt, heOpen⟩
  have hv' : TourValid vCap eCap s' := tourValid_applyEdit_dropEdge hv heOpen
  have hmp := tourMarkPot_dropEdge hv hv' hM hK hek
  exact ⟨⟨hev, trivial⟩, hv', hmp.1, hmp.2.1, hmp.2.2⟩

/-- Case 3: wall forest `.delete e` (`e ∈ s.rf.F.E`, `e ∉ M`): `tourCut` followed by `dropEdge e`
preserves `tourMarkedList` identically at every root, so `outSmallSide` after `dropEdge e`
satisfies `tourMarkPot_split_step` with the exact same `Y` and potential bound. -/
theorem tourStep_wall_forestDelete_sync {vCap eCap e kept fresh : ℕ}
    {s : TourAbs} {keep M : Finset ℕ} {S : MGraph} {St Sh : Finset ℕ}
    (hv : TourValid vCap eCap s) (he_lt : e < eCap)
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S)
    (he : e ∈ s.rf.F.E) (heM : e ∉ M) (hek : e ∉ keep)
    (hkept_eq : kept = s.rf.root (s.rf.F.tail e))
    (hfreshV : fresh ∈ s.rf.F.V) (hfreshNotR : fresh ∉ s.rf.R)
    (huniq' : ∀ v ∈ s.rf.F.V,
      ∃! r, r ∈ insert fresh s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r)
    (hSt : ∀ f ∈ keep, f ∈ St ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, true)) = fresh)
    (hSh : ∀ f ∈ keep, f ∈ Sh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, false)) = fresh) :
    let s₁ := tourCut s e fresh
    let s₂ := tourApplyEdit s₁ (.dropEdge e)
    let S' := S.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))
    TourEditsValid vCap eCap s₁ [.dropEdge e] ∧
    TourValid vCap eCap s₂ ∧
    TourMarksAt s₂ M ∧
    TourKeepMatch keep s₂ S' ∧
    kept ∈ s.rf.R ∧
    (∀ r ∈ s.rf.R, r ≠ kept →
      (tourMarkedList s₂ r).toFinset = (tourMarkedList s r).toFinset) ∧
    (tourMarkedList s₂ kept).toFinset ∪ (tourMarkedList s₂ fresh).toFinset =
      (tourMarkedList s kept).toFinset := by
  intro s₁ s₂ S'
  obtain ⟨hv1, hM1, hK1, hkeptR, hother1, hunion1⟩ :=
    tourCut_split_sync hv hM hK he heM hkept_eq hfreshV hfreshNotR huniq' hSt hSh
  have heOpen1 : e ∉ s₁.rf.F.E := Finset.notMem_erase _ _
  have hev2 : TourEditValid vCap eCap s₁ (.dropEdge e) := ⟨he_lt, heOpen1⟩
  have hv2 : TourValid vCap eCap s₂ := tourValid_applyEdit_dropEdge hv1 heOpen1
  have hMe : M.erase e = M := Finset.erase_eq_of_notMem heM
  obtain ⟨hM2', hK2, _⟩ := tourMarkPot_dropEdge hv1 hv2 hM1 hK1 hek
  have hM2 : TourMarksAt s₂ M := hMe ▸ hM2'
  have hml_eq : ∀ r, (tourMarkedList s₂ r).toFinset = (tourMarkedList s₁ r).toFinset := by
    intro r
    ext z
    rw [List.mem_toFinset, List.mem_toFinset, mem_tourMarkedList_iff hv2 hM2,
      mem_tourMarkedList_iff hv1 hM1]
    have hrf2 : s₂.rf = s₁.rf := rfl
    rw [hrf2]
    constructor
    · rintro ⟨hrR, ⟨u, hzu⟩, hopen, hzM, hrt⟩
      have hne : z.1 ≠ e := fun h => heM (h ▸ hzM)
      have hzu1 : z ∈ s₁.ord u := (List.mem_filter.mp hzu).1
      have hsrc : ordSrc s₂.ord z = ordSrc s₁.ord z := by
        rw [hv2.compat.ordSrc_eq hzu, hv1.compat.ordSrc_eq hzu1]
      exact ⟨hrR, ⟨u, hzu1⟩, hopen, hzM, hsrc ▸ hrt⟩
    · rintro ⟨hrR, ⟨u, hzu1⟩, hopen, hzM, hrt⟩
      have hne : z.1 ≠ e := fun h => heM (h ▸ hzM)
      have hzu : z ∈ s₂.ord u := List.mem_filter.mpr ⟨hzu1, by simpa using hne⟩
      have hsrc : ordSrc s₂.ord z = ordSrc s₁.ord z := by
        rw [hv2.compat.ordSrc_eq hzu, hv1.compat.ordSrc_eq hzu1]
      exact ⟨hrR, ⟨u, hzu⟩, hopen, hzM, hsrc.symm ▸ hrt⟩
  refine ⟨⟨hev2, trivial⟩, hv2, hM2, hK2, hkeptR, fun r hr hne => ?_, ?_⟩
  · rw [hml_eq r]; exact hother1 r hr hne
  · rw [hml_eq kept, hml_eq fresh]; exact hunion1

end

end MinCostFlow.SparseCore.Program
