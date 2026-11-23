module

public import MinCostFlow.SparseCore.Program.RestartMain
public import MinCostFlow.SparseCore.Program.ReadSpec
import MinCostFlow.SparseCore.BundleRunInvBase

/-!
# Link from the machine restart to the model state `restartBundleTree` (`RestartModelState`)

Connects the post-restart machine state produced by `restartBranch_runs` (`RestartMain.lean`) to
`restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord` (`Chain/BundleRestart.lean`):

* `restartBranchStmt_noRand`: `restartBranchStmt` is deterministic (no `rand`).
* `scurRebuildAt_of_readBranchAt`: P10's `ReadBranchAt.restart` (`ReadSpec.lean`) directly
  instantiates `ScurRebuildAt` (`RestartIface.lean`).
* `activePairs`, `SlotMapOK`, `BunTableMatches`: bijective slot assignment between the active
  `(component, bucket)` pairs of `tr` and the distinct slot list `slots`.
* `restart_bun_agree` and `restart_bun_graphEq`: every active slot holds a new bundle state that
  agrees with `(restartBundleTree …).bun (C, b)` up to `BunAgree` (and `GraphEq` on graphs).
* `restartSpanState_slot_eq` and `restartSpanState_state_eq_dyn`: every active slot of
  `restartSpanState` holds `some ⟨tr'.initBunG (C, b), []⟩`, whose `DSHist.state P` equals
  `tr'.dyn (C, b)` literally.
* `scurViewRebuild_eq_restart_S_cur` and `readViewRebuild_graphEq_restart_S_cur`: rebuilding
  `S_cur` via `scurViewRebuild` gives `tr'.S_cur` literally, and rebuilding P10's `ReadView` via
  `ReadView.rebuild` gives `tr'.S_cur` up to `GraphEq` (and exact `G`, `lsf`).
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program
open MinCostFlow.SparseCore.Program.Read

public section

/-! ## Determinism of `restartBranchStmt` and instantiation of `ScurRebuildAt` from P10 -/

/-- `restartBranchStmt` uses no randomness. -/
theorem restartBranchStmt_noRand (fBun fAct fScur : ℕ) :
    (restartBranchStmt fBun fAct fScur).NoRand := by
  simp [restartBranchStmt, forRange, forUp, restartLoopBody, Stmt.NoRand]

/-- P10's `ReadBranchAt` (`ReadSpec.lean`) directly yields an instance of `ScurRebuildAt` for its
restart procedure at `b + readIdx 3`. -/
@[expose] noncomputable def scurRebuildAt_of_readBranchAt
    {R : DSRep ReadView} {vCap eCap tCap L_w P_fp : ℕ} {P : DSParams} {cap : ℕ} {p : Program}
    {b : ℕ} {readIdx : ℕ → ℕ} {fRoot : ℕ} {Q : RootQueryAt P.w p fRoot} {mul : ℕ}
    (hLoc : R.Local) (hB : ReadBranchAt R P.w vCap eCap tCap L_w P_fp P cap p b readIdx fRoot Q mul) :
    ScurRebuildAt P cap p (b + readIdx 3) where
  α := ReadView
  rebuild := ReadView.rebuild P
  size := fun _ S6 slots => rebuildSize P S6 slots
  rep := R
  mul := mul
  space := readSpace mul vCap tCap L_w
  rep_local := hLoc
  σ4 := Q.σ
  rep4 := Q.R
  rep4_local := Q.R_local
  rootCost := Q.cost
  rootsOK := fun v s4 j => ∀ u ∈ v.G.V, Q.ok s4 j u ∧ Q.root s4 j u = v.lsf.F.root u
  runs := by
    intro scurH spanTbl slotsPtr h b4 j slots v y S6 x6 s4 x4 mem pos ω
      hscurW hspanW hnW hslotsPtrW hb4W hjW hhW hlist hlist_h hact hrep hrep6 hrep4 hroots
      hfy hf6 hf4 hd76 hd74 hd64 hslotfree hz hsp
    obtain ⟨body, hb, o, st', c, y', x4', hrun, hrep', hrep4', hlo, hhi, hz', hfr, hfy', hf4',
        hd74', hcost⟩ :=
      hB.restart scurH spanTbl slotsPtr h b4 j slots v y S6 x6 s4 x4 mem pos ω
        hscurW hspanW hnW hslotsPtrW hb4W hjW hhW hlist hlist_h hact hrep hrep6 hrep4 hroots
        hfy hf6 hf4 hd76 hd74 hd64 hslotfree hz hsp
    refine ⟨body, hb, o, st', c, y', x4', hrun, hrep', hrep4', hlo, hhi, hz', hfr, hfy', hf4',
      hd74', ?_⟩
    have hlog1 : 1 ≤ ordStoreLog P.eCap := Nat.succ_pos _
    have hmul : (mul + 2 * Q.cost) * (rebuildSize P S6 slots + slots.length + 1) ≤
        (mul + 2 * Q.cost) * (rebuildSize P S6 slots + slots.length + 1) * ordStoreLog P.eCap :=
      Nat.le_mul_of_pos_right _ hlog1
    omega

/-! ## Active pairs and slot assignment -/

/-- The finite set of active `(component, bucket)` pairs of a branch state `tr`. -/
@[expose] noncomputable def activePairs {L : ℕ} (tr : BundleTreeState L) :
    Finset (Finset ℕ × ℤ) :=
  open Classical in
  tr.activeComps.biUnion fun C => (tr.activeBuckets C).image fun b => (C, b)

theorem mem_activePairs {L : ℕ} {tr : BundleTreeState L} {p : Finset ℕ × ℤ} :
    p ∈ activePairs tr ↔ p.1 ∈ tr.activeComps ∧ p.2 ∈ tr.activeBuckets p.1 := by
  classical
  unfold activePairs
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨C, hC, b, hb, rfl⟩
    exact ⟨hC, hb⟩
  · rintro ⟨hC, hb⟩
    exact ⟨p.1, hC, p.2, hb, rfl⟩

theorem activePairs_sum {L : ℕ} (tr : BundleTreeState L) (f : Finset ℕ × ℤ → ℕ) :
    (activePairs tr).sum f =
      tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b => f (C, b) := by
  classical
  unfold activePairs
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_image]
    intro b₁ _ b₂ _ h
    exact (Prod.mk.inj h).2
  · intro C₁ _ C₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_image] at hp₁ hp₂
    obtain ⟨_, _, rfl⟩ := hp₁
    obtain ⟨_, _, h2⟩ := hp₂
    exact hne (Prod.mk.inj h2).1.symm

theorem activePairs_card {L : ℕ} (tr : BundleTreeState L) :
    (activePairs tr).card = tr.activeComps.sum fun C => (tr.activeBuckets C).card := by
  have h := activePairs_sum tr (fun _ => 1)
  simpa using h

theorem activePairs_biUnion {L : ℕ} (tr : BundleTreeState L) (f : Finset ℕ × ℤ → Finset ℕ) :
    (activePairs tr).biUnion f =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b => f (C, b) := by
  classical
  ext e
  simp only [Finset.mem_biUnion, mem_activePairs]
  constructor
  · rintro ⟨⟨C, b⟩, ⟨hC, hb⟩, he⟩
    exact ⟨C, hC, b, hb, he⟩
  · rintro ⟨C, hC, b, hb, he⟩
    exact ⟨(C, b), ⟨hC, hb⟩, he⟩

/-- `slotOf` assigns a distinct slot in `slots` to every active `(component, bucket)` pair of `tr`,
bijectively onto `slots`, with every slot within both `slotCap` and `cap`. -/
@[expose] def SlotMapOK {L : ℕ} (tr : BundleTreeState L) (slotCap cap : ℕ) (slots : List ℕ)
    (slotOf : Finset ℕ × ℤ → ℕ) : Prop :=
  slots.Nodup ∧
  (∀ p ∈ activePairs tr, slotOf p ∈ slots) ∧
  (∀ s ∈ slots, ∃ p ∈ activePairs tr, slotOf p = s) ∧
  (∀ p₁ ∈ activePairs tr, ∀ p₂ ∈ activePairs tr, slotOf p₁ = slotOf p₂ → p₁ = p₂) ∧
  (∀ s ∈ slots, s < slotCap ∧ s < cap)

theorem SlotMapOK.image_eq {L slotCap cap : ℕ} {tr : BundleTreeState L} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} (h : SlotMapOK tr slotCap cap slots slotOf) :
    (activePairs tr).image slotOf = slots.toFinset := by
  ext s
  simp only [Finset.mem_image, List.mem_toFinset]
  exact ⟨fun ⟨p, hp, heq⟩ => heq ▸ h.2.1 p hp, fun hs => h.2.2.1 s hs⟩

theorem SlotMapOK.length_eq {L slotCap cap : ℕ} {tr : BundleTreeState L} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} (h : SlotMapOK tr slotCap cap slots slotOf) :
    slots.length = tr.activeComps.sum fun C => (tr.activeBuckets C).card := by
  rw [← List.toFinset_card_of_nodup h.1, ← h.image_eq,
    Finset.card_image_of_injOn (fun p₁ hp₁ p₂ hp₂ heq => h.2.2.2.1 p₁ hp₁ p₂ hp₂ heq),
    activePairs_card]

theorem SlotMapOK.sum_map_eq {L slotCap cap : ℕ} {tr : BundleTreeState L} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} (h : SlotMapOK tr slotCap cap slots slotOf) (f : ℕ → ℕ) :
    (slots.map f).sum =
      tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b => f (slotOf (C, b)) := by
  rw [← activePairs_sum tr (fun p => f (slotOf p)), ← Finset.sum_image (f := f)
    (fun p₁ hp₁ p₂ hp₂ heq => h.2.2.2.1 p₁ hp₁ p₂ hp₂ heq), h.image_eq]
  exact (List.sum_toFinset f h.1).symm

theorem SlotMapOK.biUnion_eq {L slotCap cap : ℕ} {tr : BundleTreeState L} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} (h : SlotMapOK tr slotCap cap slots slotOf) (f : ℕ → Finset ℕ) :
    slots.toFinset.biUnion f =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b => f (slotOf (C, b)) := by
  ext e
  simp only [Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro ⟨s, hs, he⟩
    obtain ⟨⟨C, b⟩, hp, rfl⟩ := h.2.2.1 s hs
    have ⟨hC, hb⟩ := mem_activePairs.mp hp
    exact ⟨C, hC, b, hb, he⟩
  · rintro ⟨C, hC, b, hb, he⟩
    exact ⟨slotOf (C, b), h.2.1 (C, b) (mem_activePairs.mpr ⟨hC, hb⟩), he⟩

/-! ## Agreement of bundles and dynamic spanners with `restartBundleTree` -/

/-- The bundle table `S` matches the active `(component, bucket)` pairs of `tr` up to `BunAgree`. -/
@[expose] def BunTableMatches {L slotCap : ℕ} (tr : BundleTreeState L)
    (slotOf : Finset ℕ × ℤ → ℕ) (S : Fin slotCap → Option BundleState) : Prop :=
  ∀ p ∈ activePairs tr, ∃ (hs : slotOf p < slotCap) (B : BundleState),
    S ⟨slotOf p, hs⟩ = some B ∧ BunAgree B (tr.bun p)

theorem restartSlotBundle_eq_restartBucketBundle {L slotCap : ℕ} {tr : BundleTreeState L}
    {slotOf : Finset ℕ × ℤ → ℕ} {S : Fin slotCap → Option BundleState}
    (hMatch : BunTableMatches tr slotOf S) (ord : ℕ → List End) {C : Finset ℕ} {b : ℤ}
    (hC : C ∈ tr.activeComps) (hb : b ∈ tr.activeBuckets C) :
    restartSlotBundle S tr.cs ord tr.k (slotOf (C, b)) = restartBucketBundle tr ord C b := by
  obtain ⟨hs, B, hSB, hag⟩ := hMatch (C, b) (mem_activePairs.mpr ⟨hC, hb⟩)
  unfold restartSlotBundle restartBucketBundle
  simp only [hs, ↓reduceDIte, hSB, hag.2.1]

theorem restartSlotGraph_eq_initBunG {L slotCap : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) {tr : BundleTreeState L}
    {slotOf : Finset ℕ × ℤ → ℕ} {S : Fin slotCap → Option BundleState}
    (hMatch : BunTableMatches tr slotOf S) (ord : ℕ → List End) {C : Finset ℕ} {b : ℤ}
    (hC : C ∈ tr.activeComps) (hb : b ∈ tr.activeBuckets C) :
    restartSlotGraph S tr.cs ord tr.k (slotOf (C, b)) =
      (restartBundleTree L sparsify tr ord).initBunG (C, b) := by
  unfold restartSlotGraph
  rw [restartSlotBundle_eq_restartBucketBundle hMatch ord hC hb]
  simp only [restartBundleTree, hC, ↓reduceIte]
  rfl

/-- **Bundle state link.** After the restart, every active slot `(C, b)` holds a bundle state `B'`
that agrees with `(restartBundleTree …).bun (C, b)` up to `BunAgree` (and `GraphEq` on graphs). -/
theorem restart_bun_agree {L slotCap cap : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) {tr : BundleTreeState L}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S S' : Fin slotCap → Option BundleState}
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (ord : ℕ → List End)
    (hPost : ∀ s ∈ slots, ∃ (hs : s < slotCap) (B' : BundleState), S' ⟨s, hs⟩ = some B' ∧
      BunAgree B' (restartSlotBundle S tr.cs ord tr.k s)) :
    BunTableMatches (restartBundleTree L sparsify tr ord) slotOf S' ∧
      ∀ p ∈ activePairs tr, ∃ (hs : slotOf p < slotCap) (B' : BundleState),
        S' ⟨slotOf p, hs⟩ = some B' ∧
          GraphEq B'.graph ((restartBundleTree L sparsify tr ord).bun p).graph := by
  have hact : activePairs (restartBundleTree L sparsify tr ord) = activePairs tr := rfl
  have hEach : ∀ p ∈ activePairs tr, ∃ (hs : slotOf p < slotCap) (B' : BundleState),
      S' ⟨slotOf p, hs⟩ = some B' ∧
        BunAgree B' ((restartBundleTree L sparsify tr ord).bun p) := by
    intro ⟨C, b⟩ hp
    have ⟨hC, hb⟩ := mem_activePairs.mp hp
    obtain ⟨hs, B', hSB', hag⟩ := hPost (slotOf (C, b)) (hMap.2.1 (C, b) hp)
    refine ⟨hs, B', hSB', ?_⟩
    rw [restartSlotBundle_eq_restartBucketBundle hMatch ord hC hb] at hag
    simpa only [restartBundleTree, hC, ↓reduceIte] using hag
  refine ⟨fun p hp => hEach p (hact ▸ hp), fun p hp => ?_⟩
  obtain ⟨hs, B', hSB', hag⟩ := hEach p hp
  exact ⟨hs, B', hSB', graphEq_of_bunAgree hag⟩

/-- **Dynamic spanner link.** After the restart, every active slot `(C, b)` of `restartSpanState`
holds the empty history on `(restartBundleTree …).initBunG (C, b)`, whose `DSHist.state P` is
literally `(restartBundleTree …).dyn (C, b)`. -/
theorem restartSpanState_state_eq_dyn {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) {C : Finset ℕ} {b : ℤ}
    (hC : C ∈ tr.activeComps) (hb : b ∈ tr.activeBuckets C) :
    let tr' := restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord
    let S6' := restartSpanState S6 S tr.cs ord tr.k slots
    ∃ (hs : slotOf (C, b) < cap) (d : DSHist),
      S6' ⟨slotOf (C, b), hs⟩ = some d ∧ d = ⟨tr'.initBunG (C, b), []⟩ ∧
      d.state P = tr'.dyn (C, b) := by
  intro tr' S6'
  have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) (mem_activePairs.mpr ⟨hC, hb⟩)
  have hs : slotOf (C, b) < cap := (hMap.2.2.2.2 _ hmem).2
  refine ⟨hs, ⟨tr'.initBunG (C, b), []⟩, ?_, rfl, ?_⟩
  · unfold S6' restartSpanState
    simp only [hmem, ↓reduceIte]
    rw [restartSlotGraph_eq_initBunG (fun _ => canonicalSparsify P.impl) hMatch ord hC hb]
  · rw [dsHist_state_nil]
    simp only [tr', restartBundleTree, hC, ↓reduceIte, hSB]

/-! ## `DSHist` base graph and initial spanner subgraph -/

/-- The current graph of an empty `DSHist` is its initial graph `Hb`. -/
theorem dsHist_init_G_eq (P : DSParams) (Hb : MGraph) :
    (DSHist.state P ⟨Hb, []⟩).G = Hb := by
  rw [dsHist_state_nil]
  rfl

/-- The initial spanner of an empty `DSHist` on a valid graph `Hb` with `Hb.m ≤ P.mMax` has its
edges inside `Hb.E`. -/
theorem dsHist_init_H_sub_E (P : DSParams) {Hb : MGraph} (hVal : Hb.IsValid) (hm : Hb.m ≤ P.mMax) :
    (DSHist.state P ⟨Hb, []⟩).H.E ⊆ Hb.E := by
  rw [dsHist_state_nil]
  unfold DynSpanner.init initAt initCore
  by_cases hE : Hb.E.Nonempty
  · simp only [hE, ↓reduceDIte]
    have hspec := canonicalSparsify_spec_absorb P.impl P.mMax (activeSubgraph Hb)
      (activeSubgraph Hb) idEmb (activeSubgraph_isValid hVal) (activeSubgraph_isValid hVal)
      hm (fun h => by rw [idEmb_length_eq_one h]) (idEmb_isEmbedding _)
    exact hspec.1.2.1
  · simp only [hE, ↓reduceDIte, emptyGraphOn]
    exact Finset.empty_subset _

theorem slotGE_restartSpanState {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) {C : Finset ℕ} {b : ℤ}
    (hC : C ∈ tr.activeComps) (hb : b ∈ tr.activeBuckets C) :
    slotGE P (restartSpanState S6 S tr.cs ord tr.k slots) (slotOf (C, b)) =
      ((restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).initBunG (C, b)).E := by
  obtain ⟨hs, d, hd, rfl, _⟩ := restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB hC hb
  unfold slotGE
  simp only [hs, ↓reduceDIte, hd, dsHist_init_G_eq]

theorem slotHE_restartSpanState {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) {C : Finset ℕ} {b : ℤ}
    (hC : C ∈ tr.activeComps) (hb : b ∈ tr.activeBuckets C) :
    slotHE P (restartSpanState S6 S tr.cs ord tr.k slots) (slotOf (C, b)) =
      ((restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).dyn (C, b)).H.E := by
  obtain ⟨hs, d, hd, _, hst⟩ := restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB hC hb
  unfold slotHE
  simp only [hs, ↓reduceDIte, hd, hst]

theorem slotsGE_restartSpanState {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) :
    slotsGE P (restartSpanState S6 S tr.cs ord tr.k slots) slots =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        ((restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).bun (C, b)).edges := by
  unfold slotsGE
  rw [hMap.biUnion_eq]
  refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b hb => ?_
  rw [slotGE_restartSpanState P S6 ord hMap hMatch hSB hC hb]
  simp only [restartBundleTree, hC, ↓reduceIte]
  rfl

theorem slotsHE_restartSpanState {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) :
    slotsHE P (restartSpanState S6 S tr.cs ord tr.k slots) slots =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        ((restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).dyn (C, b)).H.E := by
  unfold slotsHE
  rw [hMap.biUnion_eq]
  refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b hb => ?_
  exact slotHE_restartSpanState P S6 ord hMap hMatch hSB hC hb

/-! ## `S_cur` link for `scurViewRebuild` and `ReadView.rebuild` -/

theorem restartBucketBundle_edges_of_coreCord {L : ℕ} {tr : BundleTreeState L}
    {ord cord : ℕ → List End} (hcord : CoreCordOf tr.cs ord cord) (C : Finset ℕ) (b : ℤ) :
    (restartBucketBundle tr ord C b).edges = (tr.bun (C, b)).edges := by
  obtain ⟨_, _, hI, ρ, hρ, _⟩ := hcord
  exact initBundleFor_edges hI hρ (tr.bun (C, b)).edges tr.k

/-- **`S_cur` link for `scurViewRebuild`.** When `v` holds the core vertices, core ends, and
non-spanner edges `extraComps ∪ crossEdges`, `scurViewRebuild` on `restartSpanState` gives
`(restartBundleTree …).S_cur` literally. -/
theorem scurViewRebuild_eq_restart_S_cur {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap)
    {ord cord : ℕ → List End} {v : ScurView}
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) (hcord : CoreCordOf tr.cs ord cord)
    (hV : v.V = tr.cs.RF.R)
    (htail : v.tail = (coreGraph tr.cs.G tr.cs.lsf).tail)
    (hhead : v.head = (coreGraph tr.cs.G tr.cs.lsf).head)
    (hX : v.X = (tr.activeComps.biUnion fun C => tr.extraEdges C) ∪ tr.cs.crossEdges) :
    (scurViewRebuild P v (restartSpanState S6 S tr.cs ord tr.k slots) slots).S =
      (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).S_cur := by
  set tr' := restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord
  have hHE := slotsHE_restartSpanState P S6 ord hMap hMatch hSB
  have hEx : (tr.activeComps.biUnion fun C => tr.extraEdges C) =
      tr.activeComps.biUnion fun C =>
        ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \
          (tr.activeBuckets C).biUnion fun b => (tr'.bun (C, b)).edges := by
    refine Finset.biUnion_congr rfl fun C hC => ?_
    unfold BundleTreeState.extraEdges
    congr 1
    refine Finset.biUnion_congr rfl fun b _ => ?_
    simp only [tr', restartBundleTree, hC, ↓reduceIte]
    exact (restartBucketBundle_edges_of_coreCord hcord C b).symm
  unfold scurViewRebuild ScurView.rebuild
  simp only [hV, htail, hhead, hHE, hX, hEx, ← Finset.union_assoc]
  have hDynEq : (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        (tr'.dyn (C, b)).H.E) =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        (DynSpanner.init (SparseCore.normGraph (restartBucketBundle tr ord C b).graph) P.L
          (phaseBase ((SparseCore.normGraph (restartBucketBundle tr ord C b).graph).n +
            tr.splitBound) P.L) (canonicalSparsify P.impl)).state.H.E := by
    refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b _ => ?_
    simp only [tr', restartBundleTree, hC, ↓reduceIte]
  rw [hDynEq]
  rfl

/-- Pre-restart model invariants of a branch state `tr` needed to identify `ReadView.rebuild` with
`(restartBundleTree …).S_cur` up to `GraphEq`. All of these hold along every valid run
(`runOrdAfterRestarts_bun_inv`, `runOrdAfterRestarts_S_cur_inv`). -/
@[expose] def RestartScurModelInv {L : ℕ} (tr : BundleTreeState L) : Prop :=
  tr.activeComps ⊆ components tr.cs.G₀ ∧
  tr.S_cur.V = tr.cs.RF.R ∧
  tr.S_cur.E =
    (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b => (tr.dyn (C, b)).H.E) ∪
      (tr.activeComps.biUnion fun C => tr.extraEdges C) ∪ tr.cs.crossEdges ∧
  (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur ∧
  (∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
    (tr.bun (C, b)).edges ⊆ (coreGraph tr.cs.G tr.cs.lsf).E ∧
    (tr.bun (C, b)).edges ⊆ (tr.cs.compSt C).G.E ∧
    Disjoint (tr.bun (C, b)).edges tr.cs.insertedGlobal ∧
    (tr.dyn (C, b)).H.E ⊆ (tr.bun (C, b)).edges)

private lemma comp_edge_disj_nonCross {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C₁ C₂ : Finset ℕ}
    (hC₁ : C₁ ∈ components cs.G₀) (hC₂ : C₂ ∈ components cs.G₀) (hne : C₁ ≠ C₂)
    {e : ℕ} (he₁ : e ∈ (cs.compSt C₁).G.E) (he₂ : e ∈ (cs.compSt C₂).G.E)
    (hnc : e ∉ cs.crossEdges) : False := by
  have ht₁ : cs.G.tail e ∈ (cs.compSt C₁).G.V := by
    rw [← (hI.hNonCross_ends C₁ hC₁ e he₁ hnc).1]
    exact ((hI.hCompLSF C₁ hC₁).1.hG_val e he₁).1
  have ht₂ : cs.G.tail e ∈ (cs.compSt C₂).G.V := by
    rw [← (hI.hNonCross_ends C₂ hC₂ e he₂ hnc).1]
    exact ((hI.hCompLSF C₂ hC₂).1.hG_val e he₂).1
  exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁ C₂ hC₂ hne) ht₁ ht₂

/-- **`S_cur` link for P10 (`ReadView.rebuild`).** Under `RestartScurModelInv` and `CoreCordOf`,
rebuilding P10's `ReadView` from `restartSpanState` leaves the same `G` and `lsf` and a graph `S`
satisfying `GraphEq v'.S (restartBundleTree …).S_cur`. -/
theorem readViewRebuild_graphEq_restart_S_cur {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap)
    {ord cord : ℕ → List End} {v : ReadView}
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) (hcord : CoreCordOf tr.cs ord cord)
    (hMod : RestartScurModelInv tr)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hvG : v.G = tr.cs.G) (hvLSF : v.lsf = tr.cs.lsf) (hvS : GraphEq v.S tr.S_cur) :
    let tr' := restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord
    let v' := v.rebuild P (restartSpanState S6 S tr.cs ord tr.k slots) slots
    v'.G = tr'.cs.G ∧ v'.lsf = tr'.cs.lsf ∧ GraphEq v'.S tr'.S_cur := by
  classical
  intro tr' v'
  have ⟨_, _, hI, ρ, hρ, _⟩ := hcord
  obtain ⟨hAct, hSV, hSE, hSubCore, hBunInv⟩ := hMod
  set S6' := restartSpanState S6 S tr.cs ord tr.k slots
  set bunE := tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
    (tr.bun (C, b)).edges
  set dynE' := tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
    (tr'.dyn (C, b)).H.E
  set extraE := tr.activeComps.biUnion fun C => tr.extraEdges C
  have hGE : slotsGE P S6' slots = bunE := by
    rw [slotsGE_restartSpanState P S6 ord hMap hMatch hSB]
    refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b _ => ?_
    simp only [restartBundleTree, hC, ↓reduceIte]
    exact restartBucketBundle_edges_of_coreCord hcord C b
  have hHE : slotsHE P S6' slots = dynE' := slotsHE_restartSpanState P S6 ord hMap hMatch hSB
  have hDyn'Sub : dynE' ⊆ bunE := by
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨C, hC, heB⟩ := he
    rw [Finset.mem_biUnion] at heB
    obtain ⟨b, hb, heb⟩ := heB
    have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) (mem_activePairs.mpr ⟨hC, hb⟩)
    obtain ⟨hs, d, hd, rfl, hst⟩ := restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB hC hb
    have hokCB : SpanGraphOK P (tr'.initBunG (C, b)) := by
      have h1 := hok _ hmem
      rwa [restartSlotGraph_eq_initBunG (fun _ => canonicalSparsify P.impl) hMatch ord hC hb] at h1
    have hsubH := dsHist_init_H_sub_E P hokCB.2.2.2.2.2.2.1 hokCB.2.2.2.2.2.2.2.1
    rw [hst] at hsubH
    have heInit : e ∈ (tr'.initBunG (C, b)).E := hsubH heb
    have heBun : e ∈ (tr.bun (C, b)).edges := by
      simp only [tr', restartBundleTree, hC, ↓reduceIte, SparseCore.normGraph_E] at heInit
      rwa [← restartBucketBundle_edges_of_coreCord hcord C b]
    exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_biUnion.mpr ⟨b, hb, heBun⟩⟩
  have hBunSubCore : bunE ⊆ (coreGraph tr.cs.G tr.cs.lsf).E := by
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨C, hC, heB⟩ := he
    rw [Finset.mem_biUnion] at heB
    obtain ⟨b, hb, heb⟩ := heB
    exact (hBunInv C hC b hb).1 heb
  have hRF := compLSF_RF_isRSF hI
  have hAddEq : (dynE' ∩ v.G.E).filter (fun e =>
      (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V) = dynE' := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter, hvG, hvLSF, hvS.1, hSV]
    constructor
    · intro h; exact h.1.1
    · intro he
      have heCore := hBunSubCore (hDyn'Sub he)
      have heG : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp heCore).1
      have hth := hI.hG_val e heG
      exact ⟨⟨he, heG⟩, (root_mem_R hRF hth.1).1, (root_mem_R hRF hth.2).1⟩
  have hDynOldSub :
      (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        (tr.dyn (C, b)).H.E) ⊆ bunE := by
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨C, hC, heB⟩ := he
    rw [Finset.mem_biUnion] at heB
    obtain ⟨b, hb, heb⟩ := heB
    exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_biUnion.mpr ⟨b, hb, (hBunInv C hC b hb).2.2.2 heb⟩⟩
  have hDisjCross : Disjoint tr.cs.crossEdges bunE := by
    rw [Finset.disjoint_left]
    intro e heX heB
    rw [Finset.mem_biUnion] at heB
    obtain ⟨C, hC, heB⟩ := heB
    rw [Finset.mem_biUnion] at heB
    obtain ⟨b, hb, heb⟩ := heB
    exact Finset.disjoint_left.mp (hBunInv C hC b hb).2.2.1 heb (hI.hCross_sub heX)
  have hDisjExtra : Disjoint extraE bunE := by
    rw [Finset.disjoint_left]
    intro e heEx heB
    rw [Finset.mem_biUnion] at heEx heB
    obtain ⟨C₁, hC₁, he₁⟩ := heEx
    obtain ⟨C₂, hC₂, he₂⟩ := heB
    rw [Finset.mem_biUnion] at he₂
    obtain ⟨b₂, hb₂, heb₂⟩ := he₂
    by_cases hEq : C₁ = C₂
    · subst hEq
      have hnot := (Finset.mem_sdiff.mp he₁).2
      exact hnot (Finset.mem_biUnion.mpr ⟨b₂, hb₂, heb₂⟩)
    · have heG₁ : e ∈ (tr.cs.compSt C₁).G.E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he₁).1).1
      have heG₂ : e ∈ (tr.cs.compSt C₂).G.E := (hBunInv C₂ hC₂ b₂ hb₂).2.1 heb₂
      have hnc : e ∉ tr.cs.crossEdges := fun hc =>
        Finset.disjoint_left.mp (hBunInv C₂ hC₂ b₂ hb₂).2.2.1 heb₂ (hI.hCross_sub hc)
      exact comp_edge_disj_nonCross hI (hAct hC₁) (hAct hC₂) hEq heG₁ heG₂ hnc
  have hUnion : bunE ∪ dynE' = bunE := Finset.union_eq_left.mpr hDyn'Sub
  have hEx' : extraE = tr.activeComps.biUnion fun C =>
      ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \
        (tr.activeBuckets C).biUnion fun b => (tr'.bun (C, b)).edges := by
    refine Finset.biUnion_congr rfl fun C hC => ?_
    unfold BundleTreeState.extraEdges
    congr 1
    refine Finset.biUnion_congr rfl fun b _ => ?_
    simp only [tr', restartBundleTree, hC, ↓reduceIte]
    exact (restartBucketBundle_edges_of_coreCord hcord C b).symm
  have hDynEq' : dynE' = tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
      (DynSpanner.init (SparseCore.normGraph (restartBucketBundle tr ord C b).graph) P.L
        (phaseBase ((SparseCore.normGraph (restartBucketBundle tr ord C b).graph).n +
          tr.splitBound) P.L) (canonicalSparsify P.impl)).state.H.E := by
    refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b _ => ?_
    simp only [tr', restartBundleTree, hC, ↓reduceIte]
  have hTr'E : tr'.S_cur.E = dynE' ∪ extraE ∪ tr.cs.crossEdges := by
    rw [hDynEq', hEx']
    rfl
  have hEeq : (v.S.E \ (bunE ∪ dynE')) ∪ dynE' = tr'.S_cur.E := by
    rw [hUnion, hvS.2.1, hSE, hTr'E]
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨(⟨hd | hex⟩ | hcr), hnb⟩ | hd')
      · exact absurd (hDynOldSub hd) hnb
      · exact Or.inl (Or.inr hex)
      · exact Or.inr hcr
      · exact Or.inl (Or.inl hd')
    · rintro ((hd' | hex) | hcr)
      · exact Or.inr hd'
      · exact Or.inl ⟨Or.inl (Or.inr hex), Finset.disjoint_left.mp hDisjExtra hex⟩
      · exact Or.inl ⟨Or.inr hcr, Finset.disjoint_left.mp hDisjCross hcr⟩
  refine ⟨hvG, hvLSF, ?_, ?_, ?_⟩
  · show v.S.V = tr'.S_cur.V
    exact hvS.1.trans hSV
  · show (v.S.E \ (slotsGE P S6' slots ∪ slotsHE P S6' slots)) ∪ _ = tr'.S_cur.E
    rw [hGE, hHE, hAddEq, hEeq]
  · intro e he
    show (if e ∈ _ then (coreGraph v.G v.lsf).tail e else v.S.tail e) = tr'.S_cur.tail e ∧
      (if e ∈ _ then (coreGraph v.G v.lsf).head e else v.S.head e) = tr'.S_cur.head e
    have he' : e ∈ (v.S.E \ (bunE ∪ dynE')) ∪ dynE' := by
      change e ∈ (v.S.E \ (slotsGE P S6' slots ∪ slotsHE P S6' slots)) ∪ _ at he
      rwa [hGE, hHE, hAddEq] at he
    rw [hHE, hAddEq]
    by_cases hd : e ∈ dynE'
    · simp only [hd, ↓reduceIte, hvG, hvLSF]
      exact ⟨rfl, rfl⟩
    · simp only [hd, ↓reduceIte]
      have heOld : e ∈ v.S.E := (Finset.mem_sdiff.mp ((Finset.mem_union.mp he').resolve_right hd)).1
      have heOld' : e ∈ tr.S_cur.E := hvS.2.1 ▸ heOld
      have h1 := hvS.2.2 e heOld
      have h2 := hSubCore.2.2 e heOld'
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

end

end MinCostFlow.SparseCore.Program.Restart
