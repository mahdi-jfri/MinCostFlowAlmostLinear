module

public import MinCostFlow.SparseCore.Program.BundleUnified
public import MinCostFlow.SparseCore.Program.RestartModelState
public import MinCostFlow.SparseCore.Program.OutSpec

/-!
# Model-level bridge lemmas for `bundleStep` on `bunTableRep` (`BundleModelBridgeStep`)

Proves the pure model-and-representation lemmas connecting `tableAfterStep` to `bundleRunsStep`,
`bundleCompStep`, `outCoreOrder`, `BunAgree`, and `bunRestartInv`:

1. `outCoreOrder_eq_coreRotation`, `outCoreOrder_coreCordOf`, `outCoreOrder_disj`, and
   `outCoreOrder_mem_iff_src`: links `outCoreOrder st ord` to `coreRotation` and `CoreCordOf`.
2. `BunAgree.ends_eq`, `BunAgree.isPartition_iff`, `BunAgree.bundleStepReady_iff`,
   `BunAgree.bundleRunsStep_eq`, and `BunAgree.bundleCompStep_eq`: `BunAgree` bundle states have
   identical `BundleStepReady`, identical update batches, and `BunAgree` post-states under
   `bundleCompStep` (including exact equality of `parent`).
3. `tableAfterStepRuns`, `tableAfterStep_congr_runs`, and `bunRestartInv_tableAfterStepRuns`:
   under `BundleStepReady` and exact candidate detection, `BundleTableRepAt` transfers from
   `tableAfterStep` to `tableAfterStepRuns` with zero memory changes, and `bunRestartInv` is
   preserved when advancing from `cord` to `outCoreOrder info.state ord'`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

@[expose] public section

/-- Model-level post-step bundle table: applies `(bundleRunsStep cs B₀ k ord' U).2` to every
active slot of `S₀`. Under `BundleStepReady`, this has the same `vertices`, `edges`, `bundleOf`,
and empty-bundle parents as `tableAfterStep`, so it shares the exact same memory representation
(`tableAfterStep_congr_runs`) while also carrying the exact `bundleRunsStep` parents needed for
`BunAgree` and `bunRestartInv`. -/
noncomputable def tableAfterStepRuns {slotCap : ℕ} (cs : CompLSFState) (k : ℕ)
    (ord' : ℕ → List End) (U : List Update) (S₀ : BundleTableState slotCap) :
    BundleTableState slotCap :=
  fun j => (S₀ j).map fun B₀ => (bundleRunsStep cs B₀ k ord' U).2

end

public section

/-! ## 1. `outCoreOrder` bridge lemmas -/

theorem outCoreOrder_eq_coreRotation {L : ℕ} {st : BundleTreeState L} {ord : ℕ → List End}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ st.cs)
    (ρ : Rotation st.cs.G) (hρ : ρ.order = ord) :
    outCoreOrder st ord = (coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).order := by
  have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ st.cs) (ρ' : Rotation st.cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  unfold outCoreOrder
  rw [dite_eq_left hex]
  have hρ' := Rotation.ext_order (hex.choose_spec.choose_spec.choose_spec.choose_spec.trans hρ.symm)
  exact congrArg Rotation.order (by
    cases hρ'
    rfl)

theorem outCoreOrder_coreCordOf {L : ℕ} {st : BundleTreeState L} {ord : ℕ → List End}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ st.cs)
    (ρ : Rotation st.cs.G) (hρ : ρ.order = ord) :
    CoreCordOf st.cs ord (outCoreOrder st ord) :=
  ⟨C_lsst, ℓ₀, hI, ρ, hρ, outCoreOrder_eq_coreRotation hI ρ hρ⟩

theorem outCoreOrder_disj {L : ℕ} (st : BundleTreeState L) (ord : ℕ → List End) :
    ∀ v₁ v₂ x, x ∈ outCoreOrder st ord v₁ → x ∈ outCoreOrder st ord v₂ → v₁ = v₂ := by
  unfold outCoreOrder
  split_ifs with hex
  · intro v₁ v₂ x hx₁ hx₂
    set ρc := coreRotation (L := st.cs.lsf)
      hex.choose_spec.choose_spec.choose_spec.choose
      hex.choose_spec.choose_spec.choose.hG_val
      (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)
    exact ((ρc.mem_order v₁ x).mp hx₁).2.symm.trans ((ρc.mem_order v₂ x).mp hx₂).2
  · intro _ _ _ hx; simp at hx

theorem outCoreOrder_mem_iff_src {L : ℕ} {st : BundleTreeState L} {ord : ℕ → List End}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ st.cs)
    (ρ : Rotation st.cs.G) (hρ : ρ.order = ord)
    {x : End} (hxE : x.1 ∈ (coreGraph st.cs.G st.cs.lsf).E) (v : ℕ) :
    x ∈ outCoreOrder st ord v ↔ (coreGraph st.cs.G st.cs.lsf).src x = v := by
  rw [outCoreOrder_eq_coreRotation hI ρ hρ]
  set ρc := coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)
  rw [ρc.mem_order]
  exact ⟨fun h => h.2, fun h => ⟨hxE, h⟩⟩

/-! ## 2. `BunAgree` invariance for `BundleStepReady`, `bundleRunsStep`, and `bundleCompStep` -/

theorem bunAgree_ends_eq {B₁ B₂ : BundleState} (h : BunAgree B₁ B₂) (b : ℕ) :
    B₁.ends b = B₂.ends b := by
  ext x; simp only [BundleState.mem_ends, h.2.1]
  exact ⟨fun ⟨hx, hxb⟩ => ⟨hx, (h.2.2.2 x (h.2.1.symm ▸ hx)).symm.trans hxb⟩,
    fun ⟨hx, hxb⟩ => ⟨hx, (h.2.2.2 x (h.2.1.symm ▸ hx)).trans hxb⟩⟩

theorem bunAgree_isPartition_iff {G : MGraph} {ρ : Rotation G} {k : ℕ}
    {B₁ B₂ : BundleState} (h : BunAgree B₁ B₂) :
    B₁.IsPartition ρ k ↔ B₂.IsPartition ρ k := by
  have himp : ∀ {A B : BundleState}, BunAgree A B → A.IsPartition ρ k → B.IsPartition ρ k := by
    intro A B hag hA
    have hA_ends := bunAgree_ends_eq hag
    refine ⟨hag.2.1 ▸ hA.1, fun b hb => hag.2.2.1 ▸ hA.2.1 b (hag.1.symm ▸ hb), fun x hx => ?_, fun b hb => ?_⟩
    · have hxA : x ∈ edgeEnds A.edges := hag.2.1 ▸ hx
      have hbo : B.bundleOf x = A.bundleOf x := (hag.2.2.2 x ((mem_edgeEnds _ _).mp hxA)).symm
      rw [hbo, ← hag.1, ← hag.2.2.1]
      exact hA.2.2.1 x hxA
    · have hbA : b ∈ A.vertices := hag.1.symm ▸ hb
      obtain ⟨hsz, harc⟩ := hA.2.2.2 b hbA
      refine ⟨by rw [← hA_ends b]; exact hsz, ?_⟩
      rw [← hag.2.2.1, ← hag.2.1]
      obtain ⟨u, v, hrot, hu, hv⟩ := harc
      refine ⟨u, v, hrot, fun x hx => ?_, fun x hx => ?_⟩
      · simpa [← hA_ends b] using hu x hx
      · simpa [← hA_ends b] using hv x hx
  exact ⟨himp h, himp ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun x hx => (h.2.2.2 x (h.2.1 ▸ hx)).symm⟩⟩

theorem bunAgree_bundleStepReady_iff {cs : CompLSFState} {B₁ B₂ : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BunAgree B₁ B₂) :
    BundleStepReady cs B₁ k ord ord' U ↔ BundleStepReady cs B₂ k ord ord' U := by
  unfold BundleStepReady
  constructor <;> rintro ⟨C, ℓ, hI, ρ, σ, h1, h2, h3, h4, h5⟩
  · exact ⟨C, ℓ, hI, ρ, σ, h1, h2, h3, h4, (bunAgree_isPartition_iff h).mp h5⟩
  · exact ⟨C, ℓ, hI, ρ, σ, h1, h2, h3, h4, (bunAgree_isPartition_iff h).mpr h5⟩

/-- Under `BundleStepReady`, `BunAgree` bundle states produce identical update batches and
`BunAgree` post-states under `bundleRunsStep` (and `bundleCompStep`). -/
theorem bunAgree_bundleRunsStep_eq {cs : CompLSFState} {B₁ B₂ : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update}
    (hag : BunAgree B₁ B₂) (h1 : BundleStepReady cs B₁ k ord ord' U) :
    let r₁ := bundleRunsStep cs B₁ k ord' U
    let r₂ := bundleRunsStep cs B₂ k ord' U
    r₁.1 = r₂.1 ∧ BunAgree r₁.2 r₂.2 := by
  intro r₁ r₂
  have h2 : BundleStepReady cs B₂ k ord ord' U := (bunAgree_bundleStepReady_iff hag).mp h1
  set cs' := compLSFBatch cs U
  set E := B₁.edges \ batchDeletes U
  set src' := (coreGraph cs'.G cs'.lsf).src
  have hE2 : B₂.edges \ batchDeletes U = E := by rw [← hag.2.1]
  have hsurv : ∀ b, survivingEnds B₁ E b = survivingEnds B₂ E b := fun b => by
    ext x; simp only [survivingEnds, Finset.mem_filter, bunAgree_ends_eq hag b]
  have hfr : ∀ b, finalRootsOf B₁ E src' b = finalRootsOf B₂ E src' b := fun b => by
    simp only [finalRootsOf, hsurv b]
  have hvr : ∀ b, byRootVRuns B₁ E src' b = byRootVRuns B₂ E src' b := fun b => by
    simp only [byRootVRuns, rawByRootVRuns, hfr b, hsurv b]
  have hcands : exactSplitCands B₁ E src' = exactSplitCands B₂ E src' := by
    simp only [exactSplitCands, hag.1, hfr]
  have heq1 := bundleRunsStep_eq_byRoot h1
  have heq2 := bundleRunsStep_eq_byRoot h2
  have hfold : ∀ (csL : List ℕ) (s₁ s₂ : List Update × BundleState),
      s₁.1 = s₂.1 → s₁.2.vertices = s₂.2.vertices → s₁.2.edges = E → s₂.2.edges = E →
      (∀ x ∈ edgeEnds E, s₁.2.bundleOf x = s₂.2.bundleOf x) →
      let f₁ := (csL.map fun b => (b, byRootVRuns B₁ E src' b)).foldl runsFoldStep s₁
      let f₂ := (csL.map fun b => (b, byRootVRuns B₂ E src' b)).foldl runsFoldStep s₂
      f₁.1 = f₂.1 ∧ f₁.2.vertices = f₂.2.vertices ∧ f₁.2.edges = E ∧ f₂.2.edges = E ∧
        ∀ x ∈ edgeEnds E, f₁.2.bundleOf x = f₂.2.bundleOf x := by
    intro csL
    induction csL with
    | nil => intro s₁ s₂ hU hV hE1 hE2 hbo; exact ⟨hU, hV, hE1, hE2, hbo⟩
    | cons b rest ih =>
      intro s₁ s₂ hU hV hE1 hE2 hbo
      simp only [List.map_cons, List.foldl_cons, hvr b]
      set vr := byRootVRuns B₂ E src' b
      have hupd : bundleRunUpdates b (s₁.2.vertices.sup id + 1) (vr.map Prod.snd) =
          bundleRunUpdates b (s₂.2.vertices.sup id + 1) (vr.map Prod.snd) := by rw [hV]
      have hU' : (runsFoldStep s₁ (b, vr)).1 = (runsFoldStep s₂ (b, vr)).1 := by
        simp [runsFoldStep, bundleSplitFoldStep, hU, hupd]
      have hV' : (runsFoldStep s₁ (b, vr)).2.vertices = (runsFoldStep s₂ (b, vr)).2.vertices := by
        ext c; rw [runsFoldStep_vertices, runsFoldStep_vertices, hV]
      have happly : ∀ (ops : List Update) (G₁ G₂ : MGraph),
          G₁.E = E → G₂.E = E →
          (∀ e ∈ E, G₁.tail e = G₂.tail e ∧ G₁.head e = G₂.head e) →
          (∀ op ∈ ops, ∀ e, op ≠ .delete e ∧ ∀ a c, op ≠ .insert e a c) →
          (G₁.applyBatch ops).E = E ∧ (G₂.applyBatch ops).E = E ∧
          ∀ e ∈ E, (G₁.applyBatch ops).tail e = (G₂.applyBatch ops).tail e ∧
            (G₁.applyBatch ops).head e = (G₂.applyBatch ops).head e := by
        intro ops
        induction ops with
        | nil => intro G₁ G₂ h1 h2 hth _; exact ⟨h1, h2, hth⟩
        | cons op ops' ihO =>
          intro G₁ G₂ h1 h2 hth hall
          have hop := hall op List.mem_cons_self
          cases op with
          | insert e a c => exact False.elim ((hop e).2 a c rfl)
          | delete e => exact False.elim ((hop e).1 rfl)
          | split v v' St Sh =>
            refine ihO _ _ h1 h2 (fun e he => ?_) (fun o ho => hall o (List.mem_cons_of_mem _ ho))
            obtain ⟨ht, hh⟩ := hth e he
            simp [MGraph.applyUpdate, ht, hh]
      have hsp : ∀ op ∈ bundleRunUpdates b (s₁.2.vertices.sup id + 1) (vr.map Prod.snd),
          ∀ e, op ≠ .delete e ∧ ∀ a c, op ≠ .insert e a c := by
        intro op hop e
        unfold bundleRunUpdates at hop
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp hop
        exact ⟨by simp, fun _ _ => by simp⟩
      have hth0 : ∀ e ∈ E, s₁.2.graph.tail e = s₂.2.graph.tail e ∧
          s₁.2.graph.head e = s₂.2.graph.head e := fun e he =>
        ⟨hbo (e, true) ((mem_edgeEnds E (e, true)).mpr he),
         hbo (e, false) ((mem_edgeEnds E (e, false)).mpr he)⟩
      have hres := happly _ s₁.2.graph s₂.2.graph hE1 hE2 hth0 hsp
      have hE1' : (runsFoldStep s₁ (b, vr)).2.edges = E := hres.1
      have hE2' : (runsFoldStep s₂ (b, vr)).2.edges = E := by
        simpa [runsFoldStep, bundleSplitFoldStep, hupd] using hres.2.1
      have hbo' : ∀ x ∈ edgeEnds E, (runsFoldStep s₁ (b, vr)).2.bundleOf x =
          (runsFoldStep s₂ (b, vr)).2.bundleOf x := by
        intro x hx
        obtain ⟨ht, hh⟩ := hres.2.2 x.1 ((mem_edgeEnds E x).mp hx)
        rcases x with ⟨e, side⟩
        cases side with
        | true => simpa [runsFoldStep, bundleSplitFoldStep, MGraph.src, hupd] using ht
        | false => simpa [runsFoldStep, bundleSplitFoldStep, MGraph.src, hupd] using hh
      exact ih _ _ hU' hV' hE1' hE2' hbo'
  have hbase := hfold (exactSplitCands B₁ E src')
    (((B₁.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete, { B₁ with edges := E })
    (((B₂.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete, { B₂ with edges := E })
    (by rw [hag.2.1]) hag.1 rfl rfl (fun x hx => hag.2.2.2 x (Finset.sdiff_subset ((mem_edgeEnds E x).mp hx)))
  dsimp only at hbase
  have hU_eq : r₁.1 = r₂.1 := by
    rw [heq1.1, heq2.1]
    change (byRootSplitFold B₁ E src' _ (exactSplitCands B₁ E src')).1 =
      (byRootSplitFold B₂ (B₂.edges \ batchDeletes U) src' _ (exactSplitCands B₂ (B₂.edges \ batchDeletes U) src')).1
    rw [hE2, ← hcands]; exact hbase.1
  have hV_eq : r₁.2.vertices = r₂.2.vertices := by
    rw [heq1.2.1, heq2.2.1]
    change (byRootSplitFold B₁ E src' _ (exactSplitCands B₁ E src')).2.vertices =
      (byRootSplitFold B₂ (B₂.edges \ batchDeletes U) src' _ (exactSplitCands B₂ (B₂.edges \ batchDeletes U) src')).2.vertices
    rw [hE2, ← hcands]; exact hbase.2.1
  have hE_eq : r₁.2.edges = r₂.2.edges := by
    rw [heq1.2.2.1, heq2.2.2.1]
    change (byRootSplitFold B₁ E src' _ (exactSplitCands B₁ E src')).2.edges =
      (byRootSplitFold B₂ (B₂.edges \ batchDeletes U) src' _ (exactSplitCands B₂ (B₂.edges \ batchDeletes U) src')).2.edges
    rw [hE2, ← hcands]; exact hbase.2.2.1.trans hbase.2.2.2.1.symm
  have hbo_eq : ∀ x : End, x.1 ∈ r₁.2.edges → r₁.2.bundleOf x = r₂.2.bundleOf x := by
    intro x hx
    have hxE : x ∈ edgeEnds E := by
      rw [heq1.2.2.1] at hx
      change x.1 ∈ (byRootSplitFold B₁ E src' _ (exactSplitCands B₁ E src')).2.edges at hx
      rw [byRootSplitFold, hbase.2.2.1] at hx
      exact (mem_edgeEnds E x).mpr hx
    rw [heq1.2.2.2, heq2.2.2.2]
    change (byRootSplitFold B₁ E src' _ (exactSplitCands B₁ E src')).2.bundleOf x =
      (byRootSplitFold B₂ (B₂.edges \ batchDeletes U) src' _ (exactSplitCands B₂ (B₂.edges \ batchDeletes U) src')).2.bundleOf x
    rw [hE2, ← hcands]; exact hbase.2.2.2.2 x hxE
  have hp1 := bundleRunsStep_parent_eq h1
  have hp2 := bundleRunsStep_parent_eq h2
  have hpar_eq : r₁.2.parent = r₂.2.parent := by
    funext c
    by_cases hc : c ∈ r₁.2.vertices
    · have hc2 : c ∈ r₂.2.vertices := hV_eq ▸ hc
      have hends_c : r₁.2.ends c = r₂.2.ends c := by
        ext x; simp only [BundleState.mem_ends, hE_eq]
        exact ⟨fun ⟨hx, hxb⟩ => ⟨hx, (hbo_eq x (hE_eq.symm ▸ hx)).symm.trans hxb⟩,
          fun ⟨hx, hxb⟩ => ⟨hx, (hbo_eq x (hE_eq.symm ▸ hx)).trans hxb⟩⟩
      by_cases hem : r₁.2.ends c = ∅
      · have hem2 : r₂.2.ends c = ∅ := hends_c ▸ hem
        rw [(hp1.2.1 c hc hem).2, (hp2.2.1 c hc2 hem2).2, hag.2.2.1]
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hem
        rw [hp1.1 c hc x hx, hp2.1 c hc2 x (by rwa [← hends_c])]
    · have hc2 : c ∉ r₂.2.vertices := fun h => hc (hV_eq.symm ▸ h)
      rw [hp1.2.2 c hc, hp2.2.2 c hc2, hag.2.2.1]
  exact ⟨hU_eq, hV_eq, hE_eq, hpar_eq, hbo_eq⟩

theorem bunAgree_bundleCompStep_eq {cs : CompLSFState} {B₁ B₂ : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update}
    (hag : BunAgree B₁ B₂) (h1 : BundleStepReady cs B₁ k ord ord' U) :
    let r₁ := bundleCompStep cs B₁ k ord ord' U
    let r₂ := bundleCompStep cs B₂ k ord ord' U
    r₁.1 = r₂.1 ∧ BunAgree r₁.2 r₂.2 := by
  have h2 := (bunAgree_bundleStepReady_iff hag).mp h1
  simpa only [bundleCompStep_eq h1, bundleCompStep_eq h2] using bunAgree_bundleRunsStep_eq hag h1

/-! ## 3. Lifting `tableAfterStep` to `tableAfterStepRuns` and `bunRestartInv` -/

/-- Under `BundleStepReady` and exact candidate detection, `tableAfterStep` and
`tableAfterStepRuns` satisfy `BundleTableRepAt` on the exact same memory (`st'.mem`). -/
theorem tableAfterStep_congr_runs {slotCap vCap eCap tbl : ℕ} {cs : CompLSFState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {mem₀ mem : ℕ → ℕ}
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m mem₀)
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady cs B₀ k ord ord' U)
    (hcand : ∀ j B₀, S₀ j = some B₀ →
      candSet j = (exactSplitCands B₀ (B₀.edges \ batchDeletes U)
        (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src).toFinset)
    (hrep : BundleTableRepAt slotCap vCap eCap tbl
      (tableAfterStep S₀ (batchDeletes U)
        (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src candSet) m mem) :
    BundleTableRepAt slotCap vCap eCap tbl (tableAfterStepRuns cs k ord' U S₀) m mem := by
  set D := batchDeletes U
  set src' := (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src
  refine hrep.congr_parent fun j => ?_
  unfold tableAfterStep tableAfterStepRuns
  cases hS : S₀ j with
  | none => trivial
  | some B₀ =>
    simp only [Option.map_some]
    have hr := hready j B₀ hS
    have hc := hcand j B₀ hS
    have heq := bundleStepEmitSlot_eq_bundleRunsStep hr hc
    have hp := bundleRunsStep_parent_eq hr
    have hslot0 := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
    rw [hS] at hslot0
    cases hm0 : m.slotBlocks j with
    | none => rw [hm0] at hslot0; exact False.elim hslot0
    | some pb =>
      rw [hm0] at hslot0
      obtain ⟨nB₀, hV₀, -, -, -, hp0_out, -⟩ := hslot0.2.1
      have hVruns := bundleRunsStep_vertices_range hr hV₀
      set fast := byRootSplitFold B₀ (B₀.edges \ D) src'
        (((B₀.edges ∩ D).sort (· ≤ ·)).map Update.delete) ((candSet j).sort (· ≤ ·))
      set res := bundleRunsStep cs B₀ k ord' U
      have hfast_card : fast.2.vertices.card = nB₀ + batchSplitCount res.1 := by
        rw [← heq.2.1, hVruns, Finset.card_range]
      refine ⟨heq.2.1, heq.2.2.1, fun x _ => congrFun heq.2.2.2 x, fun b hb => ?_, fun b hb hem => ?_⟩
      · have hb_not : b ∉ res.2.vertices := by
          rw [hVruns, Finset.mem_range]; omega
        rw [hp.2.2 b hb_not]
        exact hp0_out b (by omega)
      · have hb_res : b ∈ res.2.vertices := heq.2.1.symm ▸ hb
        have hem_res : res.2.ends b = ∅ := by
          ext x; simp only [BundleState.mem_ends, heq.2.2.1, heq.2.2.2]
          exact by simpa [BundleState.mem_ends] using (Finset.ext_iff.mp hem x)
        have hpar_res : res.2.parent b = B₀.parent b := (hp.2.1 b hb_res hem_res).2
        have hb_old : b ∈ B₀.vertices := (hp.2.1 b hb_res hem_res).1
        have hpar_fast : fast.2.parent b = B₀.parent b := by
          have hnot_cand : b ∉ (candSet j).sort (· ≤ ·) := by
            intro hmem
            rw [Finset.mem_sort, hc, List.mem_toFinset] at hmem
            unfold exactSplitCands at hmem
            have h2 : 2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card := by
              simpa using (List.mem_filter.mp hmem).2
            have hvr0 : (byRootVRuns B₀ (B₀.edges \ D) src' b).length ≥ 2 := by
              simp [byRootVRuns, rawByRootVRuns, promoteLargestRun_length, Finset.length_sort]; omega
            have hvr_mem_raw : ∀ vr ∈ byRootVRuns B₀ (B₀.edges \ D) src' b,
                vr ∈ rawByRootVRuns B₀ (B₀.edges \ D) src' b := fun vr hvr =>
              (promoteLargestRun_perm _).subset hvr
            have hvr0_mem := hvr_mem_raw _ (List.getElem_mem (show 0 < (byRootVRuns B₀ (B₀.edges \ D) src' b).length by omega))
            obtain ⟨v0, hv0_s, hv0_eq⟩ := List.mem_map.mp hvr0_mem
            have hrun0_ne : ((byRootVRuns B₀ (B₀.edges \ D) src' b)[0]'(by omega)).2 ≠ [] := by
              rw [← hv0_eq]
              have hv0m : v0 ∈ finalRootsOf B₀ (B₀.edges \ D) src' b := (Finset.mem_sort _).mp hv0_s
              unfold finalRootsOf at hv0m
              obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hv0m
              intro hnil
              have hm_in : x ∈ ((((survivingEnds B₀ (B₀.edges \ D) b).filter fun y => src' y = v0).image endKey).sort (· ≤ ·)).map endOfKey :=
                List.mem_map.mpr ⟨endKey x, (Finset.mem_sort _).mpr (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxv⟩, rfl⟩), bundle_endOfKey_endKey x⟩
              dsimp only at hnil; rw [hnil] at hm_in; cases hm_in
            obtain ⟨x1, hx1⟩ := List.exists_mem_of_ne_nil _ hrun0_ne
            have hx1_raw : x1 ∈ ((((survivingEnds B₀ (B₀.edges \ D) b).filter fun y => src' y = v0).image endKey).sort (· ≤ ·)).map endOfKey := by
              simpa [← hv0_eq] using hx1
            have hx1_surv_src : x1 ∈ survivingEnds B₀ (B₀.edges \ D) b ∧ src' x1 = v0 := by
              obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp hx1_raw
              rw [Finset.mem_sort, Finset.mem_image] at hk1
              obtain ⟨y, hy, rfl⟩ := hk1
              rw [bundle_endOfKey_endKey]
              exact Finset.mem_filter.mp hy
            have hx1_surv : x1 ∈ survivingEnds B₀ (B₀.edges \ D) b := hx1_surv_src.1
            have hbo_keep : fast.2.bundleOf x1 = b := by
              have hfold_keep : ∀ (csL : List ℕ) (s : List Update × BundleState),
                  s.2.bundleOf x1 = b →
                  (∀ c ∈ csL, ∀ vr ∈ (byRootVRuns B₀ (B₀.edges \ D) src' c).drop 1, x1 ∉ vr.2) →
                  ((csL.map fun c => (c, byRootVRuns B₀ (B₀.edges \ D) src' c)).foldl runsFoldStep s).2.bundleOf x1 = b := by
                intro csL
                induction csL with
                | nil => intro s hbo _; exact hbo
                | cons c rest ih =>
                  intro s hbo hnot
                  simp only [List.map_cons, List.foldl_cons]
                  refine ih _ ?_ (fun d hd => hnot d (List.mem_cons_of_mem _ hd))
                  have hnot_c := hnot c List.mem_cons_self
                  have hstep_keep : ∀ (ops : List Update) (G : MGraph),
                      (∀ op ∈ ops, ∀ v v' St Sh, op = .split v v' St Sh →
                        (x1.2 = true → x1.1 ∉ St) ∧ (x1.2 = false → x1.1 ∉ Sh)) →
                      (∀ op ∈ ops, ∀ e, op ≠ .delete e ∧ ∀ a d, op ≠ .insert e a d) →
                      (if x1.2 then (G.applyBatch ops).tail x1.1 else (G.applyBatch ops).head x1.1) =
                        (if x1.2 then G.tail x1.1 else G.head x1.1) := by
                    intro ops
                    induction ops with
                    | nil => intro G _ _; rfl
                    | cons op ops' ihO =>
                      intro G hsp' hno
                      have h1' := hno op List.mem_cons_self
                      cases op with
                      | insert e a d => exact False.elim ((h1' e).2 a d rfl)
                      | delete e => exact False.elim ((h1' e).1 rfl)
                      | split v v' St Sh =>
                        have h2' := hsp' _ List.mem_cons_self v v' St Sh rfl
                        have hcons : G.applyBatch (.split v v' St Sh :: ops') =
                            (G.applyUpdate (.split v v' St Sh)).applyBatch ops' := rfl
                        rw [hcons, ihO _ (fun o ho => hsp' o (List.mem_cons_of_mem _ ho))
                          (fun o ho => hno o (List.mem_cons_of_mem _ ho))]
                        rcases x1 with ⟨e1, side1⟩
                        cases side1 with
                        | true => simp [MGraph.applyUpdate, h2'.1 rfl]
                        | false => simp [MGraph.applyUpdate, h2'.2 rfl]
                  have hsp_c : ∀ op ∈ bundleRunUpdates c (s.2.vertices.sup id + 1)
                      ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.snd),
                      ∀ v v' St Sh, op = .split v v' St Sh →
                        (x1.2 = true → x1.1 ∉ St) ∧ (x1.2 = false → x1.1 ∉ Sh) := by
                    intro op hop v v' St Sh heqOp
                    unfold bundleRunUpdates at hop
                    obtain ⟨⟨r, idx⟩, hmem_z, heq_u⟩ := List.mem_map.mp hop
                    rw [heqOp] at heq_u
                    injection heq_u with _ _ hSt hSh
                    have hr_mem : r ∈ ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.snd).drop 1 := by
                      obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hmem_z
                      rw [List.getElem_zipIdx] at hkeq
                      have hreq := (Prod.mk.inj hkeq).1
                      rw [← hreq]
                      exact List.getElem_mem (by simpa using hk)
                    rw [← List.map_drop] at hr_mem
                    obtain ⟨vr, hvr_m, rfl⟩ := List.mem_map.mp hr_mem
                    have hx1_not : x1 ∉ vr.2 := hnot_c vr hvr_m
                    refine ⟨fun ht hStm => hx1_not ?_, fun hf hShm => hx1_not ?_⟩
                    · rw [← hSt, List.mem_toFinset, List.mem_map] at hStm
                      obtain ⟨⟨e', s'⟩, hfm, he'⟩ := hStm
                      obtain ⟨hrm, hs'⟩ := List.mem_filter.mp hfm
                      rcases x1 with ⟨e1, side1⟩; dsimp only at ht he'; subst ht; subst he'
                      have : s' = true := by simpa using hs'
                      subst this; exact hrm
                    · rw [← hSh, List.mem_toFinset, List.mem_map] at hShm
                      obtain ⟨⟨e', s'⟩, hfm, he'⟩ := hShm
                      obtain ⟨hrm, hs'⟩ := List.mem_filter.mp hfm
                      rcases x1 with ⟨e1, side1⟩; dsimp only at hf he'; subst hf; subst he'
                      have : s' = false := by simpa using hs'
                      subst this; exact hrm
                  have hno_c : ∀ op ∈ bundleRunUpdates c (s.2.vertices.sup id + 1)
                      ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.snd),
                      ∀ e, op ≠ .delete e ∧ ∀ a d, op ≠ .insert e a d := by
                    intro op hop e
                    unfold bundleRunUpdates at hop
                    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hop
                    exact ⟨by simp, fun _ _ => by simp⟩
                  have hres_bo := hstep_keep _ s.2.graph hsp_c hno_c
                  rcases x1 with ⟨e1, side1⟩
                  cases side1 with
                  | true => simpa [runsFoldStep, bundleSplitFoldStep, BundleState.graph, MGraph.src, hbo] using hres_bo
                  | false => simpa [runsFoldStep, bundleSplitFoldStep, BundleState.graph, MGraph.src, hbo] using hres_bo
              refine hfold_keep _ _ ((BundleState.mem_ends _ _ _).mp (Finset.mem_filter.mp hx1_surv).1).2 ?_
              intro c _ vr hvr_m hx1_in
              obtain ⟨idx, hidx, hvr_eq⟩ := List.getElem_of_mem hvr_m
              rw [List.getElem_drop] at hvr_eq
              have hvr_in_all : vr ∈ byRootVRuns B₀ (B₀.edges \ D) src' c := by
                rw [← hvr_eq]; exact List.getElem_mem (by simp at hidx; omega)
              obtain ⟨vc, _, hvc_eq⟩ := List.mem_map.mp ((promoteLargestRun_perm _).subset hvr_in_all)
              rw [← hvc_eq] at hx1_in
              obtain ⟨k1, hk1, heq1'⟩ := List.mem_map.mp hx1_in
              rw [Finset.mem_sort, Finset.mem_image] at hk1
              obtain ⟨y, hy, rfl⟩ := hk1
              rw [bundle_endOfKey_endKey] at heq1'
              subst heq1'
              have hy_f := Finset.mem_filter.mp hy
              by_cases hcb : c = b
              · subst hcb
                have hnd_fst : ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.fst).Nodup := by
                  unfold byRootVRuns
                  rw [((promoteLargestRun_perm _).map Prod.fst).nodup_iff]
                  simp [rawByRootVRuns, List.map_map, Function.comp_def, Finset.sort_nodup]
                have hfst0 : ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.fst)[0]'(by simp; omega) = v0 := by
                  simp [← hv0_eq]
                have hfst1 : ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.fst)[1 + idx]'(by simp at hidx ⊢; omega) = vc := by
                  simp [hvr_eq, ← hvc_eq]
                have hsrc_eq : ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.fst)[0]'(by simp; omega) =
                    ((byRootVRuns B₀ (B₀.edges \ D) src' c).map Prod.fst)[1 + idx]'(by simp at hidx ⊢; omega) := by
                  rw [hfst0, hfst1, ← hx1_surv_src.2, hy_f.2]
                have h0_eq := (List.Nodup.getElem_inj_iff hnd_fst).mp hsrc_eq
                omega
              · have h1b := ((BundleState.mem_ends _ _ _).mp (Finset.mem_filter.mp hx1_surv).1).2
                have h2c := ((BundleState.mem_ends _ _ _).mp (Finset.mem_filter.mp hy_f.1).1).2
                exact hcb (h2c.symm.trans h1b)
            have hresE : res.2.edges = B₀.edges \ D := (bundleRunsStep_spec hr).2.2.2.2.1
            have hx1_in_fast : x1 ∈ fast.2.ends b :=
              (BundleState.mem_ends _ _ _).mpr ⟨by rw [← heq.2.2.1, hresE]; exact (Finset.mem_filter.mp hx1_surv).2, hbo_keep⟩
            rw [hem] at hx1_in_fast; exact Finset.notMem_empty x1 hx1_in_fast
          have hfold_par : ∀ (csL : List ℕ) (s : List Update × BundleState),
              b ∈ s.2.vertices → b ∉ csL → s.2.parent b = B₀.parent b →
              ((csL.map fun c => (c, byRootVRuns B₀ (B₀.edges \ D) src' c)).foldl runsFoldStep s).2.parent b =
                B₀.parent b := by
            intro csL
            induction csL with
            | nil => intro s _ _ hp'; exact hp'
            | cons c rest ih =>
              intro s hbv hnot hp'
              simp only [List.map_cons, List.foldl_cons]
              have hbc : b ≠ c := fun h => hnot (h ▸ List.mem_cons_self)
              have hble : b ≤ s.2.vertices.sup id := Finset.le_sup (f := id) hbv
              refine ih _ (by rw [runsFoldStep_vertices]; exact Or.inl hbv)
                (fun h => hnot (List.mem_cons_of_mem _ h)) ?_
              simp [runsFoldStep, runParent, hbc, show ¬ (s.2.vertices.sup id + 1 ≤ b) by omega, hp']
          exact hfold_par _ _ hb_old hnot_cand rfl
        rw [hpar_res, hpar_fast]

/-- `bunRestartInv` is preserved across `tableAfterStepRuns` when moving from `cord` to
`cord' = outCoreOrder info.state ord'`. -/
theorem bunRestartInv_tableAfterStepRuns {L slotCap vCap eCap : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    {S₀ : BundleTableState slotCap} {cord : ℕ → List End}
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U)
    (hcord'_bounds : ∀ v x, x ∈ outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v →
      v < vCap ∧ x.1 < eCap) :
    bunRestartInv vCap eCap (tableAfterStepRuns tr.cs tr.k ord' U S₀)
      (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord') := by
  set info := stepBundleTree sparsify tr U ord ord'
  set cord' := outCoreOrder info.state ord'
  refine ⟨⟨outCoreOrder_disj info.state ord', fun j B' hS' b hb => ?_⟩, hcord'_bounds⟩
  unfold tableAfterStepRuns at hS'
  cases hS0 : S₀ j with
  | none => rw [hS0] at hS'; cases hS'
  | some B₀ =>
    rw [hS0] at hS'; simp only [Option.map_some, Option.some.injEq] at hS'; subst hS'
    have hr := hready j B₀ hS0
    have hp := bundleRunsStep_parent_eq hr
    by_cases hem : (bundleRunsStep tr.cs B₀ tr.k ord' U).2.ends b = ∅
    · obtain ⟨hb0, hp0⟩ := hp.2.1 b hb hem
      exact ⟨hp0 ▸ (hinv0.1.2 j B₀ hS0 b hb0).1, fun x hx => by rw [hem] at hx; cases hx⟩
    · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hem
      obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, _, hσ, _, hU, _⟩ := hready j B₀ hS0
      have hI' := compLSFBatch_inv hI hU
      let σ' : Rotation info.state.cs.G := (compLSFBatch_G tr.cs U).symm ▸ σ
      have hσ' : σ'.order = ord' := by
        dsimp only [σ']
        have hcast : ∀ {G H : MGraph} (he : G = H) (τ : Rotation G), (he ▸ τ : Rotation H).order = τ.order := by
          intro G H he τ; cases he; rfl
        exact (hcast _ σ).trans hσ
      have hpart := (bundleRunsStep_spec hr).1.1 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
      have hx_in_cord' : ∀ x ∈ (bundleRunsStep tr.cs B₀ tr.k ord' U).2.ends b,
          x ∈ cord' ((bundleRunsStep tr.cs B₀ tr.k ord' U).2.parent b) := fun x hx => by
        have hxE : x.1 ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E :=
          hpart.1 ((BundleState.mem_ends _ _ _).mp hx).1
        rw [outCoreOrder_mem_iff_src hI' σ' hσ' hxE]
        exact (hp.1 b hb x hx).symm
      exact ⟨(hcord'_bounds _ x₀ (hx_in_cord' x₀ hx₀)).1, hx_in_cord'⟩

end

end MinCostFlow.SparseCore.Program
