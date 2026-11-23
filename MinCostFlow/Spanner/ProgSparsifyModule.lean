module

public import MinCostFlow.Spanner.ProgSparsify
public import MinCostFlow.Spanner.ProgTask1Proof
public import MinCostFlow.Spanner.ProgTask2Proof
public import MinCostFlow.Spanner.ProgTask3Proof

@[expose] public section

/-!
# Self-Contained Word-RAM Module for `Sparsify`

Assembles the single fixed procedure list `sparsifyModule impl base`, linking `sparsifyBody`
(entry at `base`), Tasks 1–3, the output stage `sparsifyOutBody` and its helpers, and the four
tool sub-modules (`decompose`, `constructExpander`, `pathDS.boundsProcs`, `pathDS.procs`).

No input-dependent constants (`mMax`, `m`, `k`, `φ`) appear in any procedure body. The main
results are `sparsifyModule_noRand` and `sparsifyModule_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- Base address of `impl.decompose.procs` inside `sparsifyModule impl base`. -/
def sparsifyDecBase (base : ℕ) : ℕ := base + 29

/-- Base address of `impl.constructExpander.procs` inside `sparsifyModule impl base`. -/
def sparsifyCeBase (impl : SpannerToolImpl) (base : ℕ) : ℕ :=
  sparsifyDecBase base + (impl.decompose.procs (sparsifyDecBase base)).length

/-- Base address of `impl.pathDS.boundsProcs` inside `sparsifyModule impl base`. -/
def sparsifyBoundsBase (impl : SpannerToolImpl) (base : ℕ) : ℕ :=
  sparsifyCeBase impl base + (impl.constructExpander.procs (sparsifyCeBase impl base)).length

/-- Base address of `impl.pathDS.procs` inside `sparsifyModule impl base`. -/
def sparsifyDsBase (impl : SpannerToolImpl) (base : ℕ) : ℕ :=
  sparsifyBoundsBase impl base + (impl.pathDS.boundsProcs (sparsifyBoundsBase impl base)).length

/-- The 29 fixed procedures of `Sparsify` before the four tool sub-modules. -/
def sparsifyPrefixProcs (impl : SpannerToolImpl) (base : ℕ) : List Stmt :=
  let decBase := sparsifyDecBase base
  let ceBase := sparsifyCeBase impl base
  let boundsBase := sparsifyBoundsBase impl base
  let dsBase := sparsifyDsBase impl base
  let ce := impl.constructExpander
  [ sparsifyBody (base + 1) (base + 6) (base + 11) (base + 16) ] ++
  task1Module (base + 2) (base + 3) decBase (base + 4) (base + 5) ++
  stripLoopsModule ++
  embJHStatsModule ++
  witnessPrepModule ++
  buildWitnessCoreModule ce.phiNum ce.phiDen ce.c_deg_int ceBase boundsBase ++
  task2Module (base + 6) dsBase ++
  task3Module ce.phiNum ce.phiDen (base + 11) dsBase ++
  [ sparsifyOutBody (base + 18) (base + 19) (base + 20) (base + 21) (base + 23) (base + 28)
  , memCopyStmt
  , flatEdgesBody (base + 17)
  , dedupListBody
  , subgraphBody
  , posTableBody
  , mapListBody
  , mapEmbBody (base + 17) (base + 22)
  , revCopyBody
  , revWalkBody (base + 24)
  , composeStepBody (base + 17) (base + 25)
  , composeWalkBody (base + 26) (base + 17)
  , composeEmbBody (base + 27) ]

/-- Complete self-contained Word-RAM module for `Sparsify`, with entry procedure at `base`. -/
def sparsifyModule (impl : SpannerToolImpl) (base : ℕ) : List Stmt :=
  let decBase := sparsifyDecBase base
  let ceBase := sparsifyCeBase impl base
  let boundsBase := sparsifyBoundsBase impl base
  let dsBase := sparsifyDsBase impl base
  sparsifyPrefixProcs impl base ++
    impl.decompose.procs decBase ++
    impl.constructExpander.procs ceBase ++
    impl.pathDS.boundsProcs boundsBase ++
    impl.pathDS.procs dsBase

/-- Standalone Word-RAM program for `Sparsify` with entry at procedure `0`. -/
def sparsifyProgram (impl : SpannerToolImpl) : Program :=
  { procs := sparsifyModule impl 0 }

lemma sparsifyPrefixProcs_length (impl : SpannerToolImpl) (base : ℕ) :
    (sparsifyPrefixProcs impl base).length = 29 := by
  simp [sparsifyPrefixProcs, task1Module, stripLoopsModule, embJHStatsModule, witnessPrepModule,
    buildWitnessCoreModule, task2Module, task3Module]

lemma sparsifyModule_nonempty (impl : SpannerToolImpl) (base : ℕ) :
    0 < (sparsifyModule impl base).length := by
  simp [sparsifyModule, sparsifyPrefixProcs_length]

/-- Every fixed procedure in `sparsifyPrefixProcs` is deterministic (`Stmt.NoRand`). -/
theorem sparsifyPrefixProcs_noRand (impl : SpannerToolImpl) (base : ℕ) :
    ∀ s ∈ sparsifyPrefixProcs impl base, s.NoRand := by
  intro s hs
  simp only [sparsifyPrefixProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((((((rfl | h) | h) | h) | h) | h) | h) | h) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact sparsifyBody_noRand _ _ _ _
  · exact task1Module_noRand _ _ _ _ _ _ h
  · exact stripLoopsModule_noRand _ h
  · exact embJHStatsModule_noRand _ h
  · exact witnessPrepModule_noRand _ h
  · exact buildWitnessCoreModule_noRand _ _ _ _ _ _ h
  · exact task2Module_noRand _ _ _ h
  · simp only [task3Module, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      simp [task3Body, t3InitEmbBody, t3DrainQueueBody, t3MiddleEdgeBody, t3RoundBody,
        t3ForRange, t3St, Stmt.NoRand]
  · exact sparsifyOutBody_noRand _ _ _ _ _ _
  · exact memCopyStmt_noRand
  · simp [flatEdgesBody, forRange, forUp, Stmt.NoRand]
  · simp [dedupListBody, forRange, forUp, Stmt.NoRand]
  · simp [subgraphBody, forRange, forUp, Stmt.NoRand]
  · simp [posTableBody, forRange, forUp, Stmt.NoRand]
  · simp [mapListBody, forRange, forUp, Stmt.NoRand]
  · simp [mapEmbBody, forRange, forUp, Stmt.NoRand]
  · simp [revCopyBody, forRange, forUp, Stmt.NoRand]
  · simp [revWalkBody, Stmt.NoRand]
  · simp [composeStepBody, Stmt.NoRand]
  · simp [composeWalkBody, composeWalkLoop, forRange, forUp, Stmt.NoRand]
  · simp [composeEmbBody, forRange, forUp, Stmt.NoRand]

/-- `sparsifyModule impl base` is deterministic (`Stmt.NoRand`) whenever the three tool
implementations are deterministic. -/
theorem sparsifyModule_noRand (impl : SpannerToolImpl) (base : ℕ)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase base), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl base), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl base), s.NoRand) :
    ∀ s ∈ sparsifyModule impl base, s.NoRand := by
  intro s hs
  simp only [sparsifyModule, List.mem_append] at hs
  rcases hs with (((h | h) | h) | h) | h
  · exact sparsifyPrefixProcs_noRand impl base s h
  · exact hdec s h
  · exact hce s h
  · exact impl.pathDS.hbounds_noRand _ s h
  · exact hds s h

private lemma hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := fun i hi => by
  have h1 := h i (by simp; omega); rwa [List.getElem_append_left hi] at h1

private lemma hasAt_append_right {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt (b + xs.length) ys := fun i hi => by
  have h1 := h (xs.length + i) (by simp; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at h1
  simpa [Nat.add_assoc, Nat.add_sub_cancel_left] using h1

private lemma hasAt_singleton_of {p : Program} {base i : ℕ} {ms : List Stmt} {s : Stmt}
    (hhas : p.HasAt base ms) (hi : i < ms.length) (hs : ms[i]'hi = s) :
    p.procs[base + i]? = some s := by
  have h1 := hhas i hi
  rwa [hs] at h1

/-- `sparsifyModule impl base` meets `sparsifyContract impl w` at entry procedure `base`. -/
theorem sparsifyModule_meetsContract {w : ℕ} {p : Program} {impl : SpannerToolImpl} {base : ℕ}
    (hhas : p.HasAt base (sparsifyModule impl base)) :
    MeetsContract w p base (sparsifyContract impl w) := by
  intro args mem pos ω hwords hpre
  have hw1 : 1 < 2 ^ w := by
    obtain ⟨inp, _, _, _, hmax⟩ := hpre
    have h1 : 3 ≤ sparsifyOutSpace (Task1Input.mwCap impl inp.J) inp.J.m
        (Task2Input.gammaExpCap impl inp.J) := by unfold sparsifyOutSpace; dsimp only; omega
    have h2 : sparsifyOutSpace (Task1Input.mwCap impl inp.J) inp.J.m
        (Task2Input.gammaExpCap impl inp.J) ≤ sparsifyMaxHeapEnd impl inp := by
      unfold sparsifyMaxHeapEnd; omega
    omega
  set decBase := sparsifyDecBase base
  set ceBase := sparsifyCeBase impl base
  set boundsBase := sparsifyBoundsBase impl base
  set dsBase := sparsifyDsBase impl base
  set ce := impl.constructExpander
  have hprefLen : (sparsifyPrefixProcs impl base).length = 29 := sparsifyPrefixProcs_length impl base
  have hhasR : p.HasAt base (sparsifyPrefixProcs impl base ++
      (impl.decompose.procs decBase ++
        (ce.procs ceBase ++ (impl.pathDS.boundsProcs boundsBase ++ impl.pathDS.procs dsBase)))) := by
    simpa [sparsifyModule, decBase, ceBase, boundsBase, dsBase, ce, List.append_assoc] using hhas
  have hpreHas : p.HasAt base (sparsifyPrefixProcs impl base) := hasAt_append_left hhasR
  have htail1 := hasAt_append_right hhasR
  rw [hprefLen] at htail1
  have hdecHas : p.HasAt decBase (impl.decompose.procs decBase) := hasAt_append_left htail1
  have htail2 := hasAt_append_right htail1
  have hceHas : p.HasAt ceBase (ce.procs ceBase) := hasAt_append_left htail2
  have htail3 := hasAt_append_right htail2
  have hbdHas : p.HasAt boundsBase (impl.pathDS.boundsProcs boundsBase) := hasAt_append_left htail3
  have hdsHas : p.HasAt dsBase (impl.pathDS.procs dsBase) := hasAt_append_right htail3
  -- Extract each fixed procedure from `hpreHas`.
  have hslot : ∀ (k : ℕ) (hk : k < 29),
      p.procs[base + k]? = some ((sparsifyPrefixProcs impl base)[k]'(by omega)) :=
    fun k hk => hasAt_singleton_of hpreHas (by omega) rfl
  have h0 : p.procs[base]? = some (sparsifyBody (base + 1) (base + 6) (base + 11) (base + 16)) := by
    simpa [sparsifyPrefixProcs] using hslot 0 (by decide)
  have ht1Has : p.HasAt (base + 1) (task1Module (base + 2) (base + 3) decBase (base + 4) (base + 5)) := by
    intro i hi; have hi0 : i = 0 := by simp [task1Module] at hi; omega
    subst hi0; simpa [sparsifyPrefixProcs, task1Module] using hslot 1 (by decide)
  have hstripHas : p.HasAt (base + 2) stripLoopsModule := by
    intro i hi; have hi0 : i = 0 := by simp [stripLoopsModule] at hi; omega
    subst hi0; simpa [sparsifyPrefixProcs, stripLoopsModule, task1Module] using hslot 2 (by decide)
  have hstatsHas : p.HasAt (base + 3) embJHStatsModule := by
    intro i hi; have hi0 : i = 0 := by simp [embJHStatsModule] at hi; omega
    subst hi0
    simpa [sparsifyPrefixProcs, embJHStatsModule, stripLoopsModule, task1Module] using hslot 3 (by decide)
  have hprepHas : p.HasAt (base + 4) witnessPrepModule := by
    intro i hi; have hi0 : i = 0 := by simp [witnessPrepModule] at hi; omega
    subst hi0
    simpa [sparsifyPrefixProcs, witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module]
      using hslot 4 (by decide)
  have hcoreHas : p.HasAt (base + 5)
      (buildWitnessCoreModule ce.phiNum ce.phiDen ce.c_deg_int ceBase boundsBase) := by
    intro i hi; have hi0 : i = 0 := by simp [buildWitnessCoreModule] at hi; omega
    subst hi0
    simpa [sparsifyPrefixProcs, buildWitnessCoreModule, witnessPrepModule, embJHStatsModule,
      stripLoopsModule, task1Module] using hslot 5 (by decide)
  have ht2Has : p.HasAt (base + 6) (task2Module (base + 6) dsBase) := by
    intro i hi
    have hi5 : i < 5 := by simpa [task2Module] using hi
    have h1 := hslot (6 + i) (by omega)
    rw [← Nat.add_assoc] at h1
    rw [h1]; congr 1
    interval_cases i <;>
      simp [sparsifyPrefixProcs, task2Module, buildWitnessCoreModule, witnessPrepModule,
        embJHStatsModule, stripLoopsModule, task1Module, dsBase]
  have ht3Has : p.HasAt (base + 11) (task3Module ce.phiNum ce.phiDen (base + 11) dsBase) := by
    intro i hi
    have hi5 : i < 5 := by simpa [task3Module] using hi
    have h1 := hslot (11 + i) (by omega)
    rw [← Nat.add_assoc] at h1
    rw [h1]; congr 1
    interval_cases i <;>
      simp [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule, witnessPrepModule,
        embJHStatsModule, stripLoopsModule, task1Module, dsBase, ce]
  have hdsSpec := impl.pathDS.spec w p dsBase hdsHas
  have ht1 : MeetsContract w p (base + 1) (task1Contract impl w) :=
    task1_meetsContract ht1Has hstripHas hstatsHas hdecHas hprepHas hcoreHas hceHas hbdHas
  have ht2 : MeetsContract w p (base + 6) (task2Contract impl w) := task2_meetsContract ht2Has hdsSpec
  have ht3 : MeetsContract w p (base + 11) (task3Contract impl w) := task3_meetsContract ht3Has hdsSpec
  have hmc : MeetsContract w p (base + 17) (memCopyContract w) :=
    memCopy_meetsContract hw1 (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 17 (by decide))
  have hff : MeetsContract w p (base + 18) (flatEdgesContract w) :=
    flatEdges_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 18 (by decide)) hmc
  have hfd : MeetsContract w p (base + 19) (dedupListContract w) := by
    refine dedupList_meetsContract fun i hi => ?_
    have hi0 : i = 0 := by simp [dedupListModule] at hi; omega
    subst hi0
    simpa [sparsifyPrefixProcs, dedupListModule, task3Module, task2Module, buildWitnessCoreModule,
      witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 19 (by decide)
  have hfsub : MeetsContract w p (base + 20) (subgraphContract w) :=
    subgraph_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 20 (by decide))
  have hfpos : MeetsContract w p (base + 21) (posTableContract w) :=
    posTable_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 21 (by decide))
  have hfml : MeetsContract w p (base + 22) (mapListContract w) :=
    mapList_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 22 (by decide))
  have hfmap : MeetsContract w p (base + 23) (mapEmbContract w) :=
    mapEmb_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 23 (by decide))
      hmc hfml
  have hfrc : MeetsContract w p (base + 24) (revCopyContract w) :=
    revCopy_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 24 (by decide))
  have hfrw : MeetsContract w p (base + 25) (revWalkContract w) :=
    revWalk_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 25 (by decide))
      hfrc
  have hfcs : MeetsContract w p (base + 26) (composeStepContract w) :=
    composeStep_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 26 (by decide))
      hmc hfrw
  have hfcw : MeetsContract w p (base + 27) (composeWalkContract w) :=
    composeWalk_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 27 (by decide))
      hfcs hmc
  have hfcomp : MeetsContract w p (base + 28) (composeEmbContract w) :=
    composeEmb_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 28 (by decide))
      hfcw
  have hfout : MeetsContract w p (base + 16) (sparsifyOutContract w) :=
    sparsifyOut_meetsContract (by
      simpa [sparsifyPrefixProcs, task3Module, task2Module, buildWitnessCoreModule,
        witnessPrepModule, embJHStatsModule, stripLoopsModule, task1Module] using hslot 16 (by decide))
      hff hfd hfsub hfpos hfmap hfcomp
  exact sparsify_meetsContract h0 ht1 ht2 ht3 hfout args mem pos ω hwords hpre

/-- Standalone `sparsifyProgram impl` meets `sparsifyContract impl w` at entry procedure `0`. -/
theorem sparsifyProgram_meetsContract {w : ℕ} (impl : SpannerToolImpl) :
    MeetsContract w (sparsifyProgram impl) 0 (sparsifyContract impl w) :=
  sparsifyModule_meetsContract fun i hi => by simp [sparsifyProgram, hi]

end MinCostFlow.Spanner
