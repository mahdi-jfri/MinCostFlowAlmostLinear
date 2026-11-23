module

public import MinCostFlow.SparseCore.Program.ReadStep
public import MinCostFlow.SparseCore.Program.ReadRestart
public import MinCostFlow.SparseCore.Program.ReadRestartInit

/-!
# Full assembly of piece P10 (`ReadMain`)

Assembles all five operations of one branch (`readLSF`, `readS`, `step`, `restart`, `init`) for the
local representation `readRep` (`ReadRep.lean`) with cost factor `readBranchMul := 5300`.

* `readRep_sExtract`, `readRep_scurRebuildAt`: instantiate `ReadRestart.lean`
  for `readRep`, discharging both `ReadBranchAt.restart` and the `ScurRebuildAt` interface of
  `RestartIface.lean`.
* `readRep_init13`: wraps `readInit_runs` (uniform 13-argument `init` receiving
  `[vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h]`) into `readRep`.
* `readBranchProcs` (18 `NoRand` procedures, uniform across all capacities and limb counts),
  `HasReadProcs`, and `hasReadProcs_inhabited` (non-vacuity witness).
* `readBranchAt_readRep`: proves `ReadBranchAt` (`ReadSpec.lean`) for `readRep` under the uniform
  predicate `HasReadProcs p b fRoot`.
* `sig_readBranch_proved` (and `sig_readBranch13_proved`): proves the main statement
  `sig_readBranch HasReadProcs readBranchIdx13` of `ReadSpec.lean`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Word-size arithmetic and `Program.HasAt` slicing -/

/-- `1 ≤ L_w` and `(vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w` imply `16 ≤ 2 ^ w`. -/
theorem hw16_of_wordBound {w vCap tCap L_w : ℕ}
    (hLw : 1 ≤ L_w) (hw : (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w) : 16 ≤ 2 ^ w := by
  have h2 : 2 ≤ vCap + tCap + 2 := by omega
  have h4 : 4 ≤ (vCap + tCap + 2) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul h2 h2
  have h2L : 2 ≤ L_w + 1 := by omega
  have h8 : 8 ≤ (vCap + tCap + 2) ^ 2 * (L_w + 1) :=
    Nat.mul_le_mul h4 h2L
  by_cases hw4 : w < 4
  · interval_cases w <;> omega
  · exact le_trans (by decide : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by omega) (by omega))

/-- `(vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w` implies `L_w < 2 ^ w`. -/
theorem hLw_of_wordBound {w vCap tCap L_w : ℕ}
    (hw : (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w) : L_w < 2 ^ w := by
  have h1a : 1 ≤ vCap + tCap + 2 := by omega
  have h1 : 1 ≤ (vCap + tCap + 2) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul h1a h1a
  have h2 : L_w + 1 ≤ (vCap + tCap + 2) ^ 2 * (L_w + 1) := by
    simpa using Nat.mul_le_mul_right (L_w + 1) h1
  omega

private theorem hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := fun i hi => by
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

private theorem hasAt_append_right {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt (b + xs.length) ys := fun i hi => by
  have := h (xs.length + i) (by simp; omega)
  simpa [← Nat.add_assoc, List.getElem_append_right (Nat.le_add_right xs.length i)] using this

/-! ## Restart instantiation for `readRep` -/

/-- `readRep` supports in-place replacement of `S` (`ReadSExtract`). -/
theorem readRep_sExtract (vCap eCap tCap L_w P : ℕ) :
    ReadSExtract vCap eCap (readRep vCap eCap tCap L_w P) := by
  intro r v y mem hrep
  obtain ⟨hyv, hlay, hkeep, hrec, h9, h10, hlive, hfrz⟩ := hrep
  have hlay' := hlay
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := hlay'
  simp only [readFullWords] at l1
  refine ⟨y.q.s, y.q.g, hrec.2.2.2.2.2.1, hrec.2.2.2.2.2.2.1,
    Or.inl ⟨by omega, by simp [readFullWords]⟩,
    Or.inl ⟨by omega, by simp [readFullWords]⟩,
    hrec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrec.gGraph,
    fun a h1 h2 => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))),
    fun a h1 h2 => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))),
    fun a _ h2 => Or.inl (by omega), ?_⟩
  intro S' mem' hS' hag
  refine ⟨{ y with view := { v with S := S' } }, ?_, fun a ha => ha, ?_⟩
  · have hw : ∀ i < readFullWords, mem' (r + i) = mem (r + i) := fun i hi =>
      hag (r + i) (Or.inl ⟨by omega, by omega⟩)
        (Or.inl (by simp only [readFullWords] at hi; omega))
    have hdom : ∀ e ∈ v.G.E, e < eCap := hrec.gGraph.2.2.1
    have hdisj :
        (∀ i < readRecWords, r + i < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ r + i) ∧
        (∀ a, y.q.t ≤ a → a < y.q.t + dynGraphSize vCap tCap →
          a < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ a) ∧
        (∀ a, y.q.f ≤ a → a < y.q.f + dynGraphSize vCap tCap →
          a < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ a) ∧
        (∀ a, y.q.roots ≤ a → a < y.q.roots + vCap →
          a < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ a) ∧
        (∀ a, y.q.g ≤ a → a < y.q.g + dynGraphSize vCap eCap →
          a < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ a) ∧
        (∀ a, y.q.num ≤ a → a < y.q.num + eCap * L_w →
          a < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ a) ∧
        (∀ a, y.q.den ≤ a → a < y.q.den + eCap * L_w →
          a < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ a) :=
      ⟨fun i hi => Or.inl (by simp only [readRecWords] at hi; omega),
       fun a _ h2 => Or.inl (by omega),
       fun a _ h2 => Or.inl (by omega),
       fun a _ h2 => Or.inl (by omega),
       fun a h1 _ => Or.inr (by omega),
       fun a h1 _ => Or.inr (by omega),
       fun a h1 _ => Or.inr (by omega)⟩
    have hrecS : ReadRecAt mem' r vCap eCap tCap L_w P { v with S := S' } y.q :=
      hrec.with_S hS' hdom hdisj (fun a ha hSout => hag a (Or.inr (Or.inl ha)) hSout)
    refine ⟨rfl, hlay, hkeep.with_S S', hrecS,
      (hw 9 (by decide)).trans h9, (hw 10 (by decide)).trans h10,
      hlive.of_agree (fun a h1 h2 =>
        hag a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))) (Or.inr (by omega))),
      hfrz.of_agree (fun a h1 h2 =>
        hag a (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))) (Or.inr (by omega)))⟩
  · change readPotMul * treePot v.G v.lsf.T ≤ readPotMul * treePot y.view.G y.view.lsf.T
    rw [hyv]

/-- `ScurRebuildAt` (`RestartIface.lean`) instantiated for `readRep`. -/
noncomputable def readRep_scurRebuildAt {vCap eCap tCap L_w P cap mul : ℕ}
    {SP : DSParams} {p : Program} {bOps bEdge bLoop fRoot bSelf : ℕ}
    (Q : RootQueryAt SP.w p fRoot)
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpSelf : p.HasAt bSelf (readRestartProcs bOps bEdge bLoop fRoot bSelf))
    (hw16 : 16 ≤ 2 ^ SP.w) (hSPe : SP.eCap ≤ eCap) (hmul : 800 ≤ mul) (hL : 1 ≤ L_w) :
    ScurRebuildAt SP cap p (bSelf + readRestartIdxMain) :=
  readRestart_scurRebuildAt (tCap := tCap) Q hpOps hpEdge hpLoop hpSelf
    (readRep_local vCap eCap tCap L_w P) hw16 hSPe hmul hL (readRep_sExtract vCap eCap tCap L_w P)

/-! ## Initialization instantiation for `readRep` -/

/-- Uniform 13-argument initialization clause for `readRep`. -/
theorem readRep_init13 {w vCap eCap tCap L_w P mul : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bLoop bInitOps bSelf : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpInitOps : p.HasAt bInitOps (readInitOpsProcs bEdge))
    (hpSelf : p.HasAt bSelf (readInitProcs bBatch bLoop bInitOps bSelf))
    (heT : eCap ≤ tCap) (hLw : 1 ≤ L_w) (hw16 : 16 ≤ 2 ^ w) (hLwW : L_w < 2 ^ w)
    (hmul : 3100 ≤ mul)
    (gD tD fD rootsPtr nR numPtr denPtr sD h : ℕ) (v : ReadView) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool)
    (hargs : ∀ a ∈ [gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h], a < 2 ^ w)
    (hInit : ReadInitAt mem h L_w gD tD fD rootsPtr nR numPtr denPtr sD v)
    (hInv : v.Inv vCap eCap tCap) (hz : ZeroFrom mem h)
    (hroom : h + readSpace mul vCap tCap L_w (readInitSize v) < 2 ^ w) :
    ∃ body, p.procs[bSelf + readInitIdxMain]? = some body ∧ ∃ o st' c y,
      Runs w p ω body
        (startState [vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h]
          mem pos) o st' c ∧
      (readRep vCap eCap tCap L_w P).rep h v y st'.mem ∧
      h ≤ o.value ∧ o.value ≤ h + readSpace mul vCap tCap L_w (readInitSize v) ∧
      ZeroFrom st'.mem o.value ∧ (∀ a < h, st'.mem a = mem a) ∧
      (∀ a, (readRep vCap eCap tCap L_w P).foot h y a → h ≤ a ∧ a < o.value) ∧
      c + (readRep vCap eCap tCap L_w P).phi h y st'.mem ≤
        mul * (readInitSize v + 1) * (L_w + 1) := by
  have hsp := readInit_space_le (vCap := vCap) (eCap := eCap) (tCap := tCap) (L_w := L_w)
    (x := readInitSize v) (mul := mul) heT hLw (by omega)
  have hproc : p.procs[bSelf + readInitIdxMain]? = some (readInitStmt bLoop bInitOps bSelf) :=
    hpSelf.get (i := readInitIdxMain) (by simp [readInitProcs, readInitIdxMain])
  obtain ⟨o, st', c, hr, ho, hRec, h9, h10, hLive, hFrz, hz', hfr', hc⟩ :=
    readInit_runs (P := P) hpOps hpEdge hpBatch hpLoop hpInitOps hpSelf hw16 hLwW hargs
      hInit hInv hz (by omega) (pos := pos) (ω := ω)
  let ptrs := readInitPtrs h vCap eCap tCap L_w
  let y : ReadConc := ⟨ptrs.1, ptrs.2.1, ptrs.2.2.1, v⟩
  have ho' : o.value = ptrs.2.2.2 := ho
  have hlay : ReadLayout h vCap eCap tCap L_w y := by
    dsimp only [ReadLayout, readFullWords, y, ptrs, readInitPtrs]; omega
  have hhEnd : ptrs.2.2.2 = h + (readInitPtrs 0 vCap eCap tCap L_w).2.2.2 := by
    dsimp only [ptrs, readInitPtrs]; omega
  have hfrzEnd : y.frz + dynGraphSize vCap tCap = ptrs.2.2.2 := rfl
  have hcost : 3100 * (readInitSize v + 1) * (L_w + 1) ≤
      mul * (readInitSize v + 1) * (L_w + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmul)
  refine ⟨_, hproc, o, st', c, y, hr, ⟨rfl, hlay, hInv.keep, hRec, h9, h10, hLive, hFrz⟩,
    by omega, by omega, by rwa [ho], hfr',
    fun a ha => by have := readFoot_bounds hlay ha; omega, ?_⟩
  simp only [readRep_phi, readPotMul, y]
  omega

/-! ## Unified procedure block and indices -/

/-- The cost factor of piece P10 (`5300`, matching `readStepMul`). -/
def readBranchMul : ℕ := readStepMul

/-- All 18 uniform procedures of piece P10, placed contiguously starting at `b`:
* `b + 0`: `readLSFStmt`
* `b + 1`: `readSStmt`
* `b + 2 .. b + 8`: `readStepProcs L (b + 2)` (7 procedures, main at `b + 2`)
* `b + 9 .. b + 12`: `readRestartProcs L.ops L.edge L.loops fRoot (b + 9)` (4 procedures, main at `b + 12`)
* `b + 13 .. b + 14`: `readInitOpsProcs L.edge` (2 procedures)
* `b + 15 .. b + 17`: `readInitProcs L.batch L.loops (b + 13) (b + 15)` (3 procedures, main at `b + 17`). -/
def readBranchProcs (L : ReadLib) (fRoot b : ℕ) : List Stmt :=
  [readLSFStmt, readSStmt] ++
  readStepProcs L (b + 2) ++
  readRestartProcs L.ops L.edge L.loops fRoot (b + 9) ++
  readInitOpsProcs L.edge ++
  readInitProcs L.batch L.loops (b + 13) (b + 15)

theorem readStepProcs_noRand (L : ReadLib) (b : ℕ) :
    ∀ s ∈ readStepProcs L b, s.NoRand := by
  intro s hs
  simp only [readStepProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact readStepStmt_noRand L (b + 1)
  · exact walkStmt_noRand (b + 2)
  · exact updOneStmt_noRand L (b + 3) (b + 6)
  · exact splitTStmt_noRand L (b + 4) (b + 5)
  · exact splitMoveStmt_noRand L
  · exact splitKeepStmt_noRand L
  · exact delFrzStmt_noRand L

theorem readBranchProcs_noRand (L : ReadLib) (fRoot b : ℕ) :
    ∀ s ∈ readBranchProcs L fRoot b, s.NoRand := by
  intro s hs
  simp only [readBranchProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((((rfl | rfl) | hStep) | hRest) | hOps) | hInit
  · exact readLSFStmt_noRand
  · exact readSStmt_noRand
  · exact readStepProcs_noRand L (b + 2) s hStep
  · exact readRestartProcs_noRand L.ops L.edge L.loops fRoot (b + 9) s hRest
  · exact readInitOpsProcs_noRand L.edge s hOps
  · exact readInitProcs_noRand L.batch L.loops (b + 13) (b + 15) s hInit

/-- Operation indices inside `readBranchProcs` (uniform 13-argument `init` at `b + 17`). -/
def readBranchIdx13 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 12
  | _ => 17

/-- Alias for the operation indices inside `readBranchProcs`. -/
abbrev readBranchIdx : ℕ → ℕ := readBranchIdx13

/-- Uniform program predicate: `p` has a `ReadLib` and `readBranchProcs` at `b`. -/
def HasReadProcs (p : Program) (b fRoot : ℕ) : Prop :=
  ∃ L : ReadLib, L.Has p ∧ p.HasAt b (readBranchProcs L fRoot b)

private theorem readBranchProcs_parts {p : Program} {L : ReadLib} {fRoot b : ℕ}
    (hp : p.HasAt b (readBranchProcs L fRoot b)) :
    p.procs[b + 0]? = some readLSFStmt ∧
    p.procs[b + 1]? = some readSStmt ∧
    p.HasAt (b + 2) (readStepProcs L (b + 2)) ∧
    p.HasAt (b + 9) (readRestartProcs L.ops L.edge L.loops fRoot (b + 9)) ∧
    p.HasAt (b + 13) (readInitOpsProcs L.edge) ∧
    p.HasAt (b + 15) (readInitProcs L.batch L.loops (b + 13) (b + 15)) := by
  dsimp only [readBranchProcs] at hp
  have h1 := hasAt_append_left hp
  have hInit := hasAt_append_right hp
  have h2 := hasAt_append_left h1
  have hOps := hasAt_append_right h1
  have h3 := hasAt_append_left h2
  have hRest := hasAt_append_right h2
  have hRead := hasAt_append_left h3
  have hStep := hasAt_append_right h3
  simp only [List.length_append, List.length_cons, List.length_nil,
    readStepProcs, readRestartProcs, readInitOpsProcs] at hStep hRest hOps hInit
  refine ⟨hRead.get (i := 0) (by decide), hRead.get (i := 1) (by decide),
    hStep, hRest, hOps, hInit⟩

/-- Non-vacuity witness: for every `fRoot`, there is a program `p` and base `b` satisfying
`HasReadProcs p b fRoot`. -/
theorem hasReadProcs_inhabited (fRoot : ℕ) : ∃ p b, HasReadProcs p b fRoot := by
  let bOps := 0
  let bEdge := dgOpsProcs.length
  let bSplit := bEdge + (dgEdgeProcs bOps).length
  let bBatch := bSplit + (dgSplitProcs bOps bSplit).length
  let bCollect := bBatch + (dgBatchProcs bOps bEdge bSplit bBatch).length
  let bCopy := bCollect + 1
  let bSetOne := bCopy + 1
  let bLoops := bSetOne + 1
  let bMain := bLoops + (readLoopProcs bEdge).length
  let L : ReadLib := ⟨bOps, bEdge, bSplit, bBatch, bCollect, bCopy, bSetOne, bLoops⟩
  let p : Program := ⟨dgOpsProcs ++ dgEdgeProcs bOps ++ dgSplitProcs bOps bSplit ++
    dgBatchProcs bOps bEdge bSplit bBatch ++ [collectStmt] ++ [copyWords] ++
    [LSF.Program.lsfSetWstrOneProc] ++ readLoopProcs bEdge ++ readBranchProcs L fRoot bMain⟩
  have hAll : p.HasAt 0 p.procs := fun i hi => by
    simp [List.getElem?_eq_getElem hi]
  have h1 := hasAt_append_left hAll; have hMain := hasAt_append_right hAll
  have h2 := hasAt_append_left h1; have hLoops := hasAt_append_right h1
  have h3 := hasAt_append_left h2; have hSetOne := hasAt_append_right h2
  have h4 := hasAt_append_left h3; have hCopy := hasAt_append_right h3
  have h5 := hasAt_append_left h4; have hCollect := hasAt_append_right h4
  have h6 := hasAt_append_left h5; have hBatch := hasAt_append_right h5
  have h7 := hasAt_append_left h6; have hSplit := hasAt_append_right h6
  have hOps := hasAt_append_left h7; have hEdge := hasAt_append_right h7
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    at hEdge hSplit hBatch hCollect hCopy hSetOne hLoops hMain
  exact ⟨p, bMain, L,
    ⟨hOps, hEdge, hSplit, hBatch, hCollect.head, hCopy, hSetOne.head, hLoops⟩, hMain⟩

/-! ## Main assembly theorems -/

/-- **Exact `ReadBranchAt` (`ReadSpec.lean`) for `readRep`** under the uniform predicate
`HasReadProcs p b fRoot`, with `mul = readBranchMul = 5300`. -/
theorem readBranchAt_readRep {w vCap eCap tCap L_w P : ℕ} {SP : DSParams}
    {cap : ℕ} {p : Program} {b fRoot : ℕ} {Q : RootQueryAt w p fRoot}
    (hp : HasReadProcs p b fRoot)
    (_hSPw : SP.w = w) (hSPe : SP.eCap ≤ eCap) (heT : eCap ≤ tCap)
    (hLw : 1 ≤ L_w) (hw : (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w) :
    ReadBranchAt (readRep vCap eCap tCap L_w P) w vCap eCap tCap L_w P SP cap p b
      readBranchIdx13 fRoot Q readBranchMul := by
  obtain ⟨L, hL, hMain⟩ := hp
  obtain ⟨hLSF, hS, hStep, hRest, hOps, hInit⟩ := readBranchProcs_parts hMain
  have hw16 := hw16_of_wordBound hLw hw
  have hLwW := hLw_of_wordBound hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r h v y mem pos ω _ _ hrep hfoot hz hroom
    exact readRep_readLSF hLSF (by decide) r h v y mem pos ω hrep hfoot hz hroom
  · intro r h v y mem pos ω _ _ hrep hfoot hz hroom
    exact readRep_readS hS (by decide) r h v y mem pos ω hrep hfoot hz hroom
  · intro r batch words chg us usWords h v y U U_S c mem pos ω hargs hrep hfoot hz
      hB hval hcaps hBin hC hCin hBS hvalS hcapsS hBSin hins hInv hroom
    exact readRep_step hL (readStepProcs_step hStep) (readStepProcs_walk hL hStep)
      le_rfl hLw hw16 r batch words chg us usWords h v y U U_S c mem pos ω
      hargs hrep hfoot hz hB hval hcaps hBin hC hCin hBS hvalS hcapsS hBSin hins hInv hroom
  · intro r spanTbl slotsPtr h b4 j slots v y S6 x6 s4 x4 mem pos ω
      hrW hspanW hnW hslotsW hb4W hjW hhW hlist hlist_h hact hR hrep6 hrep4 hQok
      hfootR hfoot6 hfoot4 hdisj_R6 hdisj_R4 hdisj_64 _hdisj_slots hz hroom
    simpa [readBranchIdx13, readRestartIdxMain, Nat.add_assoc] using
      readRestart_branch_clause hL.1 hL.2.1 hL.2.2.2.2.2.2.2 hRest hw16 hSPe (by decide) hLw
        (readRep_sExtract vCap eCap tCap L_w P) r spanTbl slotsPtr h b4 j slots v y S6 x6 s4 x4
        mem pos ω hrW hspanW hnW hslotsW hb4W hjW hhW hlist hlist_h hact hR hrep6 hrep4 hQok
        hfootR hfoot6 hfoot4 hdisj_R6 hdisj_R4 hdisj_64 hz hroom
  · intro gD tD fD rootsPtr nR numPtr denPtr sD h v mem pos ω hargs hInitAt hInv hz hroom
    simpa [readBranchIdx13, readInitIdxMain, Nat.add_assoc] using
      readRep_init13 hL.1 hL.2.1 hL.2.2.2.1 hL.2.2.2.2.2.2.2 hOps hInit heT hLw hw16 hLwW
        (by decide) gD tD fD rootsPtr nR numPtr denPtr sD h v mem pos ω
        hargs hInitAt hInv hz hroom

/-- Compatibility alias for `ReadBranchAt` (`ReadSpec.lean`). -/
abbrev ReadBranchAt13 := ReadBranchAt

/-- Compatibility alias for `sig_readBranch` (`ReadSpec.lean`). -/
abbrev sig_readBranch13 := sig_readBranch

/-- **Main uniform assembly theorem of piece P10** (`sig_readBranch`, `ReadSpec.lean`, with
`mul = readBranchMul = 5300`). -/
theorem sig_readBranch_proved : sig_readBranch HasReadProcs readBranchIdx13 :=
  ⟨readBranchMul, fun _ vCap eCap tCap L_w P _ _ _ _ _ _ hp hSPw hSPe heT hLw hw =>
    ⟨readRep vCap eCap tCap L_w P, readRep_local vCap eCap tCap L_w P,
      readBranchAt_readRep hp hSPw hSPe heT hLw hw⟩⟩

/-- Compatibility alias for `sig_readBranch_proved`. -/
theorem sig_readBranch13_proved : sig_readBranch13 HasReadProcs readBranchIdx13 :=
  sig_readBranch_proved

end MinCostFlow.SparseCore.Program.Read
