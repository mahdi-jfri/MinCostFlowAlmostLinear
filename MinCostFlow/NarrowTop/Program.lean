module

public import WordRAM.Module
public import WordRAM.Std.Bits
public import WordRAM.Std.Array
public import WordRAM.Std.Limbs
public import MinCostFlow.NarrowProg.BitScale
public import MinCostFlow.NarrowProg.Stage1Mod
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.NarrowProg.Stage0Entry
public import MinCostFlow.NarrowTop.Statement
public import MinCostFlow.NarrowTop.HostSolver
public import MinCostFlow.Scaling.PropagateLabelsProgram
import Mathlib.Tactic.Ring

/-!
# Linked narrow-word program and its `RunsTo` theorem (`narrowProgram`)

Links all narrow-word procedures into a single deterministic `WordRAM.Program` using
`WordRAM.link` and `Module.Placed`:
1. `pkg.mainMod` (entry procedure `0`: `narrowMain`, calling `stage1Circ` at `NarrowTopName.stage1 0`);
2. `stage1Mod topStage1Names` (39 procedures of Stage 1 cost scaling);
3. `bitScaleMod topBitScaleNames` (17 procedures of Stage 2 bit scaling and shared primitives);
4. `topStdMod` (`clog2`, `copy`, `limbsAdd`);
5. `propLabelsMod propBase` (`propagateLabelsModule propBase`);
6. `narrowSolverAdapterMod NarrowTopName.solverAux P.solver 0 solBase P.scratchDegree`
   (the host-width compressed-relocated solver adapter from `HostSolver.lean`).

Proves:
- `narrowProgram_isDeterministic`: no `rand` instruction anywhere in the linked program;
- `narrowProgram_stage1_meets_uniform`: `stage1Circ` meets `stage1CircSpec` with an explicit
  `w`-independent constant `narrowStage1Const` (derived directly from `bitScale_meets_direct`
  and `stage1Circ_meets`, avoiding any `w`-dependent existential inside `MeetsO`);
- `narrowProgram_runsTo`: `RunsTo` on `narrowEncode I` via `runsTo_of_meets_narrowEntry`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std
open MinCostFlow.Scaling MinCostFlow.Scaling.Machine MinCostFlow.Final
open MinCostFlow.Narrow MinCostFlow.NarrowProg MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowTop

/-! ### Procedure names and static module layout -/

/-- Disjoint procedure-name type for the linked narrow-word program. Using disjoint constructors
for each component allows a structural `Nodup` proof without sorting `P.solver.procs.length`
names in the kernel. -/
inductive NarrowTopName
  | mainAux (i : ℕ)
  | stage1 (k : ℕ)
  | bitScale (k : ℕ)
  | std (k : ℕ)
  | propAux (i : ℕ)
  | solverAux (i : ℕ)
  deriving DecidableEq

/-- Procedure names for `bitScaleMod` inside `narrowProgram`. -/
def topBitScaleNames : BitScaleNames NarrowTopName where
  bitScale := .bitScale 0
  bitLength := .bitScale 1
  topBitLength := .bitScale 2
  limbBit := .bitScale 3
  accAdd := .bitScale 4
  accNormalize := .bitScale 5
  limbsSub := .bitScale 6
  phaseWriteFwd := .bitScale 7
  phaseWriteRev := .bitScale 8
  phaseWrite := .bitScale 9
  nzLoad := .bitScale 10
  clamp := .bitScale 11
  phaseUpdateEdge := .bitScale 12
  phaseUpdate := .bitScale 13
  max2 := .bitScale 14
  bitScaleLoop := .bitScale 15
  bitScaleFinalize := .bitScale 16
  solver := .solverAux 0

/-- Procedure names for `stage1Mod` inside `narrowProgram`. Entry `stage1Circ` is `.stage1 0`. -/
def topStage1Names : Stage1Names NarrowTopName where
  stage1Circ := .stage1 0
  stage1Compress := .stage1 1
  stage1DecLimbs := .stage1 2
  stage1PrepNegCosts := .stage1 3
  stage1PadCaps := .stage1 4
  stage1FillPtrs := .stage1 5
  stage1Write8 := .stage1 6
  stage1Write9 := .stage1 7
  stage1StartMeta := .stage1 8
  stage1WriteLayout := .stage1 9
  stage1StartHdr := .stage1 10
  stage1InitHalfCosts := .stage1 11
  stage1InitResEndpoints := .stage1 12
  stage1InitCapTables := .stage1 13
  stage1InitAdjCosts := .stage1 14
  stage1Start := .stage1 15
  stage1Min := .stage1 16
  stage1RoundEdge := .stage1 17
  stage1RoundedCosts := .stage1 18
  stage1CanonLen := .stage1 19
  stage1ResCaps := .stage1 20
  stage1WriteS := .stage1 21
  stage1WriteQEdges := .stage1 22
  stage1WriteQ := .stage1 23
  stage1BuildRouting := .stage1 24
  stage1DualExtract := .stage1 25
  stage1CopyPad := .stage1 26
  stage1FlowUpdate := .stage1 27
  stage1CostBit := .stage1 28
  stage1StepActive := .stage1 29
  stage1LoadAndStep := .stage1 30
  stage1StateUpdate := .stage1 31
  stage1RoundCostsCall := .stage1 32
  stage1RoundResCapsCall := .stage1 33
  stage1RoundBitScaleCall := .stage1 34
  stage1RoundDualCall := .stage1 35
  stage1RoundFlowCall := .stage1 36
  stage1RoundStateCall := .stage1 37
  stage1Round := .stage1 38
  bitScale := topBitScaleNames.bitScale
  solver := .solverAux 0
  propLabels := .propAux 0
  bitLength := topBitScaleNames.bitLength
  clog2 := .std 0
  topBitLength := topBitScaleNames.topBitLength
  limbBit := topBitScaleNames.limbBit
  copy := .std 1
  limbsAdd := .std 2
  limbsSub := topBitScaleNames.limbsSub

/-- Shared WordRAM stdlib procedures (`clog2`, `copy`, `limbsAdd`) needed by `stage1Mod` beyond
those already placed by `bitScaleMod`. -/
def topStdMod : Module NarrowTopName :=
  ⟨[(.std 0, fun idx => clog2 (idx topBitScaleNames.bitLength)),
    (.std 1, fun _ => copy),
    (.std 2, fun _ => limbsAdd)]⟩

theorem topStdMod_noRand : topStdMod.NoRand := by
  wram_no_rand

/-- Polymorphic `WordRAM.Module` wrapper for `propagateLabelsModule b`. -/
def propLabelsMod (b : ℕ) : Module NarrowTopName :=
  ⟨(propagateLabelsModule b).zipIdx.map fun p => (.propAux p.2, fun _ => p.1)⟩

theorem propLabelsMod_bodies (b : ℕ) (idx : NarrowTopName → ℕ) :
    (propLabelsMod b).bodies idx = propagateLabelsModule b := by
  unfold propLabelsMod Module.bodies
  rw [List.map_map]
  simp only [Function.comp_def]
  have h : ∀ (l : List Stmt) (k : ℕ), (l.zipIdx k).map Prod.fst = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x xs ih => intro k; simp [List.zipIdx_cons, ih]
  exact h _ 0

theorem propLabelsMod_names (b : ℕ) :
    (propLabelsMod b).names = (List.range (propagateLabelsModule b).length).map .propAux := by
  unfold propLabelsMod Module.names
  rw [List.map_map]
  simp only [Function.comp_def]
  have h : ∀ (l : List Stmt) (k : ℕ),
      (l.zipIdx k).map (fun p => NarrowTopName.propAux p.2) =
        (List.range' k l.length).map .propAux := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x xs ih => intro k; simp [List.zipIdx_cons, List.range'_succ, ih]
  rw [h _ 0, List.range_eq_range']

theorem propLabelsMod_noRand (b : ℕ) : (propLabelsMod b).NoRand := by
  intro q hq idx
  unfold propLabelsMod at hq
  obtain ⟨⟨body, i⟩, hmem, rfl⟩ := List.mem_map.mp hq
  have ⟨_, _, hget⟩ := List.mem_zipIdx hmem
  exact propagateLabelsModule_noRand b body (List.mem_of_getElem hget.symm)

/-! ### Outer `narrowMain` module interface -/

/-- Interface package for the outer `narrowMain` module (Stages 0 and 3). -/
structure NarrowMainPkg where
  /-- Outer module whose head procedure is procedure `0` (`narrowMain`) and which calls
  `stage1Circ` at `NarrowTopName.stage1 0`. -/
  mainMod : Module NarrowTopName
  /-- `mainMod` is nonempty (its head procedure is placed at index `0`). -/
  mainMod_nonempty : mainMod.procs ≠ []
  /-- Every procedure defined in `mainMod` uses the `mainAux` name constructor. -/
  mainMod_names_main : ∀ n ∈ mainMod.names, ∃ i, n = .mainAux i
  /-- Procedure names in `mainMod` are distinct. -/
  mainMod_names_nodup : mainMod.names.Nodup
  /-- `mainMod` contains no `rand` instructions. -/
  mainMod_noRand : mainMod.NoRand
  /-- Uniform (`w`-independent) non-`stage1Circ` cost constant `a0` of `narrowMain`. -/
  a0 : ℕ
  /-- Entry correctness and cost of `narrowMain` at procedure `0`, given any monotone workspace `S`
  and monotone 4-argument cost envelope `B` for `stage1Circ`. -/
  mainMod_meets :
    ∀ (w : ℕ) (p : Program) (idx : NarrowTopName → ℕ)
      (S : ℕ → ℕ → ℕ) (B : ℕ → ℕ → ℕ → ℕ → ℕ),
      (∀ n n' m m', n ≤ n' → m ≤ m' → S n m ≤ S n' m') →
      (∀ n n' m m' u u' c c', n ≤ n' → m ≤ m' → u ≤ u' → c ≤ c' →
        B n m u c ≤ B n' m' u' c') →
      mainMod.Placed p idx →
      idx (mainMod.procs.head mainMod_nonempty).1 = 0 →
      Meets w p (idx (.stage1 0)) ((stage1CircSpec w S).withCost fun x _ =>
        B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) →
      Meets w p 0
        (narrowEntrySpec w (NarrowMainFits w S)
          (fun I _ =>
            a0 * (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) +
            B (I.n + 1) (3 * I.m) (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
            B I.n (2 * I.m) (2 * I.maxCapacity) I.maxCost)
          (fun I _ out => narrowIsCorrectAnswer I out))

/-! ### The linked whole program -/

/-- Base procedure index of `propagateLabelsModule` inside `narrowProgram`. -/
def narrowPropBase (pkg : NarrowMainPkg) : ℕ :=
  (linkProcs [pkg.mainMod, stage1Mod topStage1Names, bitScaleMod topBitScaleNames, topStdMod]).length

/-- Base procedure index of `narrowSolverAdapterModule` inside `narrowProgram`. -/
def narrowSolverBase (pkg : NarrowMainPkg) : ℕ :=
  narrowPropBase pkg + (propagateLabelsModule (narrowPropBase pkg)).length

/-- Solver adapter module placed at `narrowSolverBase pkg`. -/
noncomputable def narrowSolverMod (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg) :
    Module NarrowTopName :=
  narrowSolverAdapterMod NarrowTopName.solverAux P.solver 0 (narrowSolverBase pkg) P.scratchDegree

/-- List of modules forming the complete narrow-word minimum-cost flow program. -/
noncomputable def narrowModules (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg) :
    List (Module NarrowTopName) :=
  [pkg.mainMod,
   stage1Mod topStage1Names,
   bitScaleMod topBitScaleNames,
   topStdMod,
   propLabelsMod (narrowPropBase pkg),
   narrowSolverMod P pkg]

/-- The complete linked deterministic Word-RAM program for narrow-word minimum-cost flow.
Procedure `0` is the entry of `pkg.mainMod`. -/
noncomputable def narrowProgram (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg) : Program :=
  link (narrowModules P pkg)

theorem narrowProgram_isDeterministic (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg) :
    (narrowProgram P pkg).IsDeterministic := by
  apply link_isDeterministic
  intro m hm
  simp only [narrowModules, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pkg.mainMod_noRand
  · exact stage1Mod_noRand topStage1Names
  · exact bitScaleMod_noRand topBitScaleNames
  · exact topStdMod_noRand
  · exact propLabelsMod_noRand _
  · exact narrowSolverAdapterMod_noRand NarrowTopName.solverAux P.solver 0 _ P.scratchDegree
      P.solver_deterministic

/-! ### Structural `Nodup` and placement lemmas -/

private def NarrowTopName.tag : NarrowTopName → Fin 6
  | .mainAux _ => 0
  | .stage1 _ => 1
  | .bitScale _ => 2
  | .std _ => 3
  | .propAux _ => 4
  | .solverAux _ => 5

private theorem nodup_append_of_tags {l1 l2 : List NarrowTopName} {t1 : Fin 6}
    (h1 : l1.Nodup) (h2 : l2.Nodup)
    (ht1 : ∀ x ∈ l1, x.tag = t1) (ht2 : ∀ y ∈ l2, y.tag ≠ t1) :
    (l1 ++ l2).Nodup :=
  List.nodup_append.mpr ⟨h1, h2, fun x hx y hy hxy => ht2 y hy (hxy ▸ ht1 x hx)⟩

private theorem stage1Names_nodup : (stage1Mod topStage1Names).names.Nodup := by decide
private theorem bitScaleNames_nodup : (bitScaleMod topBitScaleNames).names.Nodup := by decide
private theorem stdNames_nodup : topStdMod.names.Nodup := by decide

private theorem stage1Names_tag :
    ∀ n ∈ (stage1Mod topStage1Names).names, n.tag = 1 := by decide
private theorem bitScaleNames_tag :
    ∀ n ∈ (bitScaleMod topBitScaleNames).names, n.tag = 2 := by decide
private theorem stdNames_tag :
    ∀ n ∈ topStdMod.names, n.tag = 3 := by decide

private theorem propNames_tag (b : ℕ) :
    ∀ n ∈ (propLabelsMod b).names, n.tag = 4 := by
  intro n hn; rw [propLabelsMod_names] at hn
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hn; rfl

private theorem solverNames_tag (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg) :
    ∀ n ∈ (narrowSolverMod P pkg).names, n.tag = 5 := by
  intro n hn; unfold narrowSolverMod at hn; rw [narrowSolverAdapterMod_names] at hn
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hn; rfl

theorem narrowModules_names_nodup (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg) :
    (linkNames (narrowModules P pkg)).Nodup := by
  unfold linkNames narrowModules
  simp only [linkProcs_cons, linkProcs_nil, List.append_nil, List.map_append]
  have h5 : (propLabelsMod (narrowPropBase pkg)).names.Nodup := by
    rw [propLabelsMod_names]
    exact List.nodup_range.map fun _ _ h => NarrowTopName.propAux.inj h
  have h6 : (narrowSolverMod P pkg).names.Nodup := by
    unfold narrowSolverMod; rw [narrowSolverAdapterMod_names]
    exact List.nodup_range.map fun _ _ h => NarrowTopName.solverAux.inj h
  have ht0 : ∀ n ∈ pkg.mainMod.names, n.tag = 0 := fun n hn => by
    obtain ⟨_, rfl⟩ := pkg.mainMod_names_main n hn; rfl
  have h45 : ((propLabelsMod (narrowPropBase pkg)).names ++ (narrowSolverMod P pkg).names).Nodup :=
    nodup_append_of_tags h5 h6 (propNames_tag _) fun y hy => by
      rw [solverNames_tag P pkg y hy]; decide
  have h35 : (topStdMod.names ++ ((propLabelsMod (narrowPropBase pkg)).names ++
      (narrowSolverMod P pkg).names)).Nodup :=
    nodup_append_of_tags stdNames_nodup h45 stdNames_tag fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · rw [propNames_tag _ y hy]; decide
      · rw [solverNames_tag P pkg y hy]; decide
  have h25 : ((bitScaleMod topBitScaleNames).names ++ (topStdMod.names ++
      ((propLabelsMod (narrowPropBase pkg)).names ++ (narrowSolverMod P pkg).names))).Nodup :=
    nodup_append_of_tags bitScaleNames_nodup h35 bitScaleNames_tag fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · rw [stdNames_tag y hy]; decide
      · rcases List.mem_append.mp hy with hy | hy
        · rw [propNames_tag _ y hy]; decide
        · rw [solverNames_tag P pkg y hy]; decide
  have h15 : ((stage1Mod topStage1Names).names ++ ((bitScaleMod topBitScaleNames).names ++
      (topStdMod.names ++ ((propLabelsMod (narrowPropBase pkg)).names ++
        (narrowSolverMod P pkg).names)))).Nodup :=
    nodup_append_of_tags stage1Names_nodup h25 stage1Names_tag fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · rw [bitScaleNames_tag y hy]; decide
      · rcases List.mem_append.mp hy with hy | hy
        · rw [stdNames_tag y hy]; decide
        · rcases List.mem_append.mp hy with hy | hy
          · rw [propNames_tag _ y hy]; decide
          · rw [solverNames_tag P pkg y hy]; decide
  exact nodup_append_of_tags pkg.mainMod_names_nodup h15 ht0 fun y hy => by
    rcases List.mem_append.mp hy with hy | hy
    · rw [stage1Names_tag y hy]; decide
    · rcases List.mem_append.mp hy with hy | hy
      · rw [bitScaleNames_tag y hy]; decide
      · rcases List.mem_append.mp hy with hy | hy
        · rw [stdNames_tag y hy]; decide
        · rcases List.mem_append.mp hy with hy | hy
          · rw [propNames_tag _ y hy]; decide
          · rw [solverNames_tag P pkg y hy]; decide

/-! ### Explicit `w`-independent Stage 1 cost constant and verification -/

/-- Explicit `w`-independent multiplicative constant for `stage1Circ` wired with `bitScaleMod`
and `narrowSolverAdapterMod`. -/
def narrowStage1Const : ℕ := 16075 * 1441

/-- Cost shape of `stage1Circ` matching `stage1Mod_meets`. -/
def narrowStage1CostShape (T_sol : ℕ → ℕ → ℕ) (I : Circulation) (k : ℕ) : ℕ :=
  let C := I.compress
  let R := narrowCostRounds C
  let T_U := bitScalingPhases I
  let L := costScaleBits I
  R * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
        T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) +
    I.m * (T_U / k + L / k + 1) + T_U + L + 1

private theorem stage1_uniform_cost_bound (T_sol : ℕ → ℕ → ℕ) (I : Circulation) (k : ℕ) :
    let T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ := fun T_U n m k' =>
      720 * (T_U * T_sol (n + 1) (4 * m) + T_U * (2 * m) + (2 * m) * (T_U / k' + 1) + T_U + 1)
    stage1CircCost T_bs_max T_sol 75 I k ≤
      narrowStage1Const * narrowStage1CostShape T_sol I k := by
  intro T_bs_max
  unfold stage1CircCost narrowStage1Const narrowStage1CostShape
  dsimp only
  split_ifs with hm0
  · have h1 : 1 ≤ narrowCostRounds I.compress *
        (bitScalingPhases I * T_sol (I.compress.n + 1) (4 * I.m) +
          T_sol (I.compress.n + 2) (8 * I.m + 2 * I.compress.n) +
          bitScalingPhases I * I.m + I.m * (bitScalingPhases I / k + 1) +
          bitScalingPhases I + I.compress.n + 1) +
        I.m * (bitScalingPhases I / k + costScaleBits I / k + 1) +
        bitScalingPhases I + costScaleBits I + 1 := by omega
    have h2 := Nat.mul_le_mul_left (16075 * 1441) h1
    omega
  · set C := I.compress
    set R := narrowCostRounds C
    set T_U := bitScalingPhases I
    set L := costScaleBits I
    have hstart_le : stage1StartCost I k ≤
        1500 * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) := by
      unfold stage1StartCost stage1StartHdrCost
      dsimp only [T_U, L]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
      omega
    have hround_le : stage1RoundCost T_bs_max T_sol 75 I k + 25 ≤
        15775 * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          I.m * (T_U / k + 1) + C.n + 1) := by
      unfold stage1RoundCost
      dsimp only
      have hm_term : (510 * (T_U / k + 2) + 75 + 14500) * I.m ≤
          15775 * (I.m * (T_U / k + 1)) := by
        have heq : (510 * (T_U / k + 2) + 75 + 14500) * I.m =
            I.m * (510 * (T_U / k) + 15595) := by ring
        rw [heq, ← Nat.mul_assoc, Nat.mul_comm 15775 I.m, Nat.mul_assoc]
        apply Nat.mul_le_mul_left
        have h1 : 15775 * (T_U / k + 1) = 15775 * (T_U / k) + 15775 := by ring
        rw [h1]
        have h2 := Nat.mul_le_mul_right (T_U / k) (by decide : 510 ≤ 15775)
        omega
      have h1 := Nat.le_mul_of_pos_left (T_bs_max T_U C.n I.m k) (by decide : 0 < 15775)
      have h2 := Nat.le_mul_of_pos_left (T_sol (C.n + 2) (8 * I.m + 2 * C.n)) (by decide : 0 < 15775)
      have h3 := Nat.mul_le_mul_right C.n (by decide : 3400 ≤ 15775)
      dsimp only [C, T_U, Circulation.compress] at hm_term h1 h2 h3 ⊢
      simp only [Nat.mul_add, Nat.mul_one] at hm_term ⊢
      omega
    have hG_round_inner :
        T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          I.m * (T_U / k + 1) + C.n + 1 ≤
        1441 * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) := by
      dsimp only [T_bs_max]
      have hmul1 : T_U * (2 * I.m) = 2 * (T_U * I.m) := by ring
      have hmul2 : 2 * I.m * (T_U / k + 1) = 2 * (I.m * (T_U / k + 1)) := by ring
      rw [hmul1, hmul2]
      have h720 : 720 * (T_U * T_sol (C.n + 1) (4 * I.m) + 2 * (T_U * I.m) +
          2 * (I.m * (T_U / k + 1)) + T_U + 1) ≤
          1440 * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) := by
        have heq : 1440 * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) =
            720 * (2 * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
              T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1)) := by ring
        rw [heq]
        apply Nat.mul_le_mul_left 720
        omega
      have heq2 : 1441 * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) =
          1440 * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) +
          (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) := by ring
      omega
    set A := R * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
      T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1)
    set B := I.m * (T_U / k + L / k + 1) + T_U + L + 1
    have hR_le : R * (stage1RoundCost T_bs_max T_sol 75 I k + 25) ≤ (16075 * 1441) * A := by
      calc R * (stage1RoundCost T_bs_max T_sol 75 I k + 25)
          ≤ R * (15775 * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
              I.m * (T_U / k + 1) + C.n + 1)) := Nat.mul_le_mul_left R hround_le
        _ ≤ R * (15775 * (1441 * (T_U * T_sol (C.n + 1) (4 * I.m) +
              T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
              T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1))) :=
            Nat.mul_le_mul_left R (Nat.mul_le_mul_left 15775 hG_round_inner)
        _ = (15775 * 1441) * A := by dsimp only [A]; ring
        _ ≤ (16075 * 1441) * A := Nat.mul_le_mul_right A (by decide)
    have hB_le : stage1StartCost I k + 250 ≤ (16075 * 1441) * B := by
      have hB1 : 1 ≤ B := by dsimp only [B]; omega
      have h250 : 250 ≤ 250 * B := Nat.le_mul_of_pos_right 250 hB1
      have hmul : (1500 + 250) * B = 1500 * B + 250 * B := by ring
      have h1750 : (1500 + 250) * B ≤ (16075 * 1441) * B :=
        Nat.mul_le_mul_right B (by decide)
      omega
    have htot := Nat.add_le_add hR_le hB_le
    have hcomb : (16075 * 1441) * A + (16075 * 1441) * B = (16075 * 1441) * (A + B) := by ring
    have hcomm : stage1StartCost I k + R * (stage1RoundCost T_bs_max T_sol 75 I k + 25) + 250 =
        R * (stage1RoundCost T_bs_max T_sol 75 I k + 25) + (stage1StartCost I k + 250) := by ring
    have hrhs : (16075 * 1441) * (A + B) =
        (16075 * 1441) * (R * (T_U * T_sol (C.n + 1) (4 * I.m) +
            T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) +
          I.m * (T_U / k + L / k + 1) + T_U + L + 1) := by
      dsimp only [A, B]; ring
    rw [hcomm, ← hrhs, ← hcomb]
    exact htot

/-- Uniform (`w`-independent constant) Stage 1 correctness inside `narrowProgram P pkg`,
wiring `stage1Mod`, `bitScaleMod`, `topStdMod`, `propLabelsMod`, and `narrowSolverAdapterMod`. -/
theorem narrowProgram_stage1_meets_uniform (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg)
    (w : ℕ) :
    Meets w (narrowProgram P pkg) (linkIndex (narrowModules P pkg) (.stage1 0))
      ((stage1CircSpec w (narrowSolverSpace P.scratchDegree)).withCost fun x _ =>
        narrowStage1Const * narrowStage1CostShape (narrowSolverTime P) x.1 x.2.1) := by
  set ms := narrowModules P pkg
  set p := narrowProgram P pkg
  set idx := linkIndex ms
  have hnd : (linkNames ms).Nodup := narrowModules_names_nodup P pkg
  have hp_s1 : (stage1Mod topStage1Names).Placed p idx :=
    link_placed hnd (by simp [ms, narrowModules])
  have hp_bs : (bitScaleMod topBitScaleNames).Placed p idx :=
    link_placed hnd (by simp [ms, narrowModules])
  have hp_std : topStdMod.Placed p idx :=
    link_placed hnd (by simp [ms, narrowModules])
  -- `propagateLabelsModule` placement
  have hprop_idx : idx (.propAux 0) = narrowPropBase pkg := by
    have hpre : ms = [pkg.mainMod, stage1Mod topStage1Names, bitScaleMod topBitScaleNames, topStdMod] ++
        propLabelsMod (narrowPropBase pkg) :: [narrowSolverMod P pkg] := rfl
    have hlen_pos : 0 < (propLabelsMod (narrowPropBase pkg)).procs.length := by
      simp [propLabelsMod, propagateLabelsModule]
    have h0 := linkIndex_eq (pre := [pkg.mainMod, stage1Mod topStage1Names,
        bitScaleMod topBitScaleNames, topStdMod])
      (post := [narrowSolverMod P pkg])
      (m := propLabelsMod (narrowPropBase pkg)) (by simpa [hpre] using hnd) 0 hlen_pos
    have hhead : ((propLabelsMod (narrowPropBase pkg)).procs[0]'hlen_pos).1 = .propAux 0 := by
      simp [propLabelsMod, propagateLabelsModule]
    rw [hhead] at h0
    simpa [hpre, narrowPropBase, idx] using h0
  have hprop_hasAt : p.HasAt (idx (.propAux 0)) (propagateLabelsModule (idx (.propAux 0))) := by
    rw [hprop_idx]
    have h := link_hasAt
      [pkg.mainMod, stage1Mod topStage1Names, bitScaleMod topBitScaleNames, topStdMod]
      [narrowSolverMod P pkg] (propLabelsMod (narrowPropBase pkg))
    rw [propLabelsMod_bodies] at h
    exact h
  -- `narrowSolverAdapterModule` placement
  have hsol_len_pre : (linkProcs [pkg.mainMod, stage1Mod topStage1Names,
      bitScaleMod topBitScaleNames, topStdMod, propLabelsMod (narrowPropBase pkg)]).length =
      narrowSolverBase pkg := by
    unfold narrowSolverBase narrowPropBase
    simp only [linkProcs_cons, linkProcs_nil, List.append_nil, List.length_append,
      propLabelsMod, List.length_map, List.length_zipIdx]
    omega
  have hsol_idx : idx (.solverAux 0) = narrowSolverBase pkg := by
    have hpre : ms = [pkg.mainMod, stage1Mod topStage1Names, bitScaleMod topBitScaleNames, topStdMod,
        propLabelsMod (narrowPropBase pkg)] ++ narrowSolverMod P pkg :: [] := rfl
    have hlen_pos : 0 < (narrowSolverMod P pkg).procs.length := by
      simp [narrowSolverMod, narrowSolverAdapterMod, narrowSolverAdapterModule]
    have h0 := linkIndex_eq
      (pre := [pkg.mainMod, stage1Mod topStage1Names, bitScaleMod topBitScaleNames, topStdMod,
        propLabelsMod (narrowPropBase pkg)])
      (post := []) (m := narrowSolverMod P pkg) (by simpa [hpre] using hnd) 0 hlen_pos
    have hhead : ((narrowSolverMod P pkg).procs[0]'hlen_pos).1 = .solverAux 0 := by
      simp [narrowSolverMod, narrowSolverAdapterMod, narrowSolverAdapterModule]
    rw [hhead, hsol_len_pre] at h0
    simpa [hpre, idx] using h0
  have hsol_hasAt : p.HasAt (idx (.solverAux 0))
      (narrowSolverAdapterModule P.solver 0 (idx (.solverAux 0)) P.scratchDegree) := by
    rw [hsol_idx]
    have h := link_hasAt
      [pkg.mainMod, stage1Mod topStage1Names, bitScaleMod topBitScaleNames, topStdMod,
        propLabelsMod (narrowPropBase pkg)]
      [] (narrowSolverMod P pkg)
    rw [narrowSolverMod, narrowSolverAdapterMod_bodies, hsol_len_pre] at h
    exact h
  have hsolC : MeetsContract w p (idx (.solverAux 0))
      (solverContract w (narrowSolverTime P) (narrowSolverSpace P.scratchDegree)) :=
    narrowSolverAdapter_meetsContract P hsol_hasAt
  have hsolP : p.procs[idx (.solverAux 0)]? =
      some (narrowSolverAdapterBody (idx (.solverAux 0) + 1) (idx (.solverAux 0) + 7)
        (idx (.solverAux 0) + 5)) :=
    hsol_hasAt.head
  -- Stage 2 (`bitScale`) with explicit constant `720`
  have hbit720 : Meets w p (idx topBitScaleNames.bitScale)
      ((bitScaleSpec w (narrowSolverSpace P.scratchDegree)).withCost fun d _ =>
        720 * (bitScalingPhases d.I * narrowSolverTime P (d.I.n + 1) (2 * d.I.m) +
          bitScalingPhases d.I * d.I.m + d.I.m * (bitScalingPhases d.I / d.k + 1) +
          bitScalingPhases d.I + 1)) := by
    have hdir := bitScale_meets_direct (w := w)
      (hp_bs.get (n := topBitScaleNames.bitScale)
        (b := fun i => bitScale (i topBitScaleNames.topBitLength)
          (i topBitScaleNames.bitScaleLoop) (i topBitScaleNames.bitScaleFinalize))
        (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.bitLength) (b := fun _ => bitLength) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.topBitLength)
        (b := fun i => topBitLength (i topBitScaleNames.bitLength)) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.limbBit) (b := fun _ => limbBit) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.accAdd) (b := fun _ => accAdd) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.accNormalize) (b := fun _ => accNormalize) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.limbsSub) (b := fun _ => limbsSub) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.phaseWriteFwd)
        (b := fun i => phaseWriteFwd (i topBitScaleNames.limbBit)) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.phaseWriteRev) (b := fun _ => phaseWriteRev) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.phaseWrite)
        (b := fun i => phaseWrite (i topBitScaleNames.phaseWriteFwd) (i topBitScaleNames.phaseWriteRev))
        (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.nzLoad) (b := fun _ => nzLoad) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.clamp) (b := fun _ => clamp) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.phaseUpdateEdge)
        (b := fun i => phaseUpdateEdge (i topBitScaleNames.limbBit) (i topBitScaleNames.accAdd)
          (i topBitScaleNames.nzLoad) (i topBitScaleNames.clamp))
        (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.phaseUpdate)
        (b := fun i => phaseUpdate (i topBitScaleNames.phaseUpdateEdge)) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.max2) (b := fun _ => max2) (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.bitScaleLoop)
        (b := fun i => bitScaleLoop (i topBitScaleNames.phaseWrite) (i topBitScaleNames.solver)
          (i topBitScaleNames.phaseUpdate) (i topBitScaleNames.max2))
        (by simp [bitScaleMod]))
      (hp_bs.get (n := topBitScaleNames.bitScaleFinalize)
        (b := fun i => bitScaleFinalize (i topBitScaleNames.accNormalize) (i topBitScaleNames.limbsSub))
        (by simp [bitScaleMod]))
      hsolC hsolP
    refine hdir.withCost_mono fun d _ => ?_
    dsimp only
    have hm_le : d.I.m ≤ d.I.m * (bitScalingPhases d.I / d.k + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hmul : 720 * (bitScalingPhases d.I * narrowSolverTime P (d.I.n + 1) (2 * d.I.m) +
        bitScalingPhases d.I * d.I.m + d.I.m * (bitScalingPhases d.I / d.k + 1) +
        bitScalingPhases d.I + 1) =
        720 * (bitScalingPhases d.I * narrowSolverTime P (d.I.n + 1) (2 * d.I.m)) +
        720 * (bitScalingPhases d.I * d.I.m) + 720 * (d.I.m * (bitScalingPhases d.I / d.k + 1)) +
        720 * bitScalingPhases d.I + 720 := by ring
    have h150 : 150 * d.I.m * (bitScalingPhases d.I / d.k + 2) =
        150 * (d.I.m * (bitScalingPhases d.I / d.k + 1)) + 150 * d.I.m := by ring
    have h720m : 720 * bitScalingPhases d.I * d.I.m = 720 * (bitScalingPhases d.I * d.I.m) := by ring
    have h1 := Nat.le_mul_of_pos_left
      (bitScalingPhases d.I * narrowSolverTime P (d.I.n + 1) (2 * d.I.m)) (by decide : 0 < 720)
    omega
  -- Wire Stage 1 procedures with explicit constant `narrowStage1Const`
  let N := topStage1Names
  let B := topBitScaleNames
  have hm_bl := bitLength_meets (w := w) (hp_bs.get (n := B.bitLength) (b := fun _ => bitLength) (by simp [bitScaleMod, B]))
  have hm_clog := clog2_meets (w := w) (hp_std.get (n := .std 0) (b := fun i => clog2 (i B.bitLength)) (by simp [topStdMod, B])) hm_bl
  have hm_top := topBitLength_meets (w := w) (hp_bs.get (n := B.topBitLength) (b := fun i => topBitLength (i B.bitLength)) (by simp [bitScaleMod, B])) hm_bl
  have hm_lb := limbBit_meets (w := w) (hp_bs.get (n := B.limbBit) (b := fun _ => limbBit) (by simp [bitScaleMod, B]))
  have hm_copy := copy_meets (w := w) (hp_std.get (n := .std 1) (b := fun _ => copy) (by simp [topStdMod]))
  have hm_add := limbsAdd_meets (w := w) (hp_std.get (n := .std 2) (b := fun _ => limbsAdd) (by simp [topStdMod]))
  have hm_sub := limbsSub_meets (w := w) (hp_bs.get (n := B.limbsSub) (b := fun _ => limbsSub) (by simp [bitScaleMod, B]))
  have hm_sol := solverContract_meets_stage1SolverSpec hsolC hsolP
  have hm_prop := propagateLabels_meets_stage1PropSpec (w := w) hprop_hasAt
  have hm_comp := stage1Compress_meets (w := w) (hp_s1.get (n := N.stage1Compress) (b := fun _ => stage1Compress) (by simp [stage1Mod, N]))
  have hm_dec := stage1DecLimbs_meets (w := w) (hp_s1.get (n := N.stage1DecLimbs) (b := fun _ => stage1DecLimbs) (by simp [stage1Mod, N]))
  have hm_prep := stage1PrepNegCosts_meets (w := w) (hp_s1.get (n := N.stage1PrepNegCosts) (b := fun i => stage1PrepNegCosts (i N.stage1DecLimbs) (i N.copy)) (by simp [stage1Mod, N])) hm_dec hm_copy
  have hm_pad := stage1PadCaps_meets (w := w) (hp_s1.get (n := N.stage1PadCaps) (b := fun i => stage1PadCaps (i N.copy)) (by simp [stage1Mod, N])) hm_copy
  have hm_fill := stage1FillPtrs_meets (w := w) (hp_s1.get (n := N.stage1FillPtrs) (b := fun _ => stage1FillPtrs) (by simp [stage1Mod, N]))
  have hm_w8 := stage1Write8_meets (w := w) (hp_s1.get (n := N.stage1Write8) (b := fun _ => stage1Write8) (by simp [stage1Mod, N]))
  have hm_w9 := stage1Write9_meets (w := w) (hp_s1.get (n := N.stage1Write9) (b := fun _ => stage1Write9) (by simp [stage1Mod, N]))
  have hm_meta := stage1StartMeta_meets (w := w) (hp_s1.get (n := N.stage1StartMeta) (b := fun i => stage1StartMeta (i N.topBitLength) (i N.clog2) (i N.bitLength)) (by simp [stage1Mod, N])) hm_top hm_clog hm_bl
  have hm_lay := stage1WriteLayout_meets (w := w) (hp_s1.get (n := N.stage1WriteLayout) (b := fun i => stage1WriteLayout (i N.stage1Write8) (i N.stage1Write9)) (by simp [stage1Mod, N])) hm_w8 hm_w9
  have hm_hdr := stage1StartHdr_meets (w := w) (hp_s1.get (n := N.stage1StartHdr) (b := fun i => stage1StartHdr (i N.stage1Compress) (i N.stage1StartMeta) (i N.stage1WriteLayout)) (by simp [stage1Mod, N])) hm_comp hm_meta hm_lay
  have hm_half := stage1InitHalfCosts_meets (w := w) (hp_s1.get (n := N.stage1InitHalfCosts) (b := fun i => stage1InitHalfCosts (i N.copy)) (by simp [stage1Mod, N])) hm_copy
  have hm_rep := stage1InitResEndpoints_meets (w := w) (hp_s1.get (n := N.stage1InitResEndpoints) (b := fun i => stage1InitResEndpoints (i N.copy)) (by simp [stage1Mod, N])) hm_copy
  have hm_ct := stage1InitCapTables_meets (w := w) (hp_s1.get (n := N.stage1InitCapTables) (b := fun i => stage1InitCapTables (i N.stage1PadCaps) (i N.stage1FillPtrs)) (by simp [stage1Mod, N])) hm_pad hm_fill
  have hm_adj := stage1InitAdjCosts_meets (w := w) (hp_s1.get (n := N.stage1InitAdjCosts) (b := fun i => stage1InitAdjCosts (i N.stage1PrepNegCosts)) (by simp [stage1Mod, N])) hm_prep
  have hm_start := stage1Start_meets (w := w) (hp_s1.get (n := N.stage1Start) (b := fun i => stage1Start (i N.stage1StartHdr) (i N.stage1InitHalfCosts) (i N.stage1InitResEndpoints) (i N.stage1InitCapTables) (i N.stage1InitAdjCosts)) (by simp [stage1Mod, N])) hm_hdr hm_half hm_rep hm_ct hm_adj
  have hm_min := stage1Min_meets (w := w) (hp_s1.get (n := N.stage1Min) (b := fun _ => stage1Min) (by simp [stage1Mod, N]))
  have hm_re := stage1RoundEdge_meets (w := w) (hp_s1.get (n := N.stage1RoundEdge) (b := fun i => stage1RoundEdge (i N.stage1Min)) (by simp [stage1Mod, N])) hm_min
  have hm_rc := stage1RoundedCosts_meets (w := w) (hp_s1.get (n := N.stage1RoundedCosts) (b := fun i => stage1RoundedCosts (i N.stage1RoundEdge)) (by simp [stage1Mod, N])) hm_re
  have hm_can := stage1CanonLen_meets (w := w) (hp_s1.get (n := N.stage1CanonLen) (b := fun _ => stage1CanonLen) (by simp [stage1Mod, N]))
  have hm_resCaps := stage1ResCaps_meets (w := w) (Tsub := fun n => 60 * n + 30) (hp_s1.get (n := N.stage1ResCaps) (b := fun i => stage1ResCaps (i N.limbsSub) (i N.stage1CanonLen)) (by simp [stage1Mod, N])) hm_sub (fun n => by omega) hm_can
  have hm_ws := stage1WriteS_meets (w := w) (hp_s1.get (n := N.stage1WriteS) (b := fun _ => stage1WriteS) (by simp [stage1Mod, N]))
  have hm_wqe := stage1WriteQEdges_meets (w := w) (hp_s1.get (n := N.stage1WriteQEdges) (b := fun _ => stage1WriteQEdges) (by simp [stage1Mod, N]))
  have hm_wq := stage1WriteQ_meets (w := w) (hp_s1.get (n := N.stage1WriteQ) (b := fun i => stage1WriteQ (i N.stage1WriteQEdges)) (by simp [stage1Mod, N])) hm_wqe
  have hm_br := stage1BuildRouting_meets (w := w) (hp_s1.get (n := N.stage1BuildRouting) (b := fun _ => stage1BuildRouting) (by simp [stage1Mod, N]))
  have hm_dual := stage1DualExtract_meets (w := w) (hp_s1.get (n := N.stage1DualExtract) (b := fun i => stage1DualExtract (i N.stage1WriteS) (i N.stage1WriteQ) (i N.solver) (i N.stage1BuildRouting) (i N.propLabels)) (by simp [stage1Mod, N])) hm_ws hm_wq hm_sol hm_br hm_prop
  have hm_cp := stage1CopyPad_meets (w := w) (hp_s1.get (n := N.stage1CopyPad) (b := fun i => stage1CopyPad (i N.copy)) (by simp [stage1Mod, N])) hm_copy
  have hm_flow := stage1FlowUpdate_meets (w := w) (hp_s1.get (n := N.stage1FlowUpdate) (b := fun i => stage1FlowUpdate (i N.stage1CopyPad) (i N.limbsAdd) (i N.limbsSub)) (by simp [stage1Mod, N])) hm_cp hm_add hm_sub
  have hm_cb := stage1CostBit_meets (w := w) (hp_s1.get (n := N.stage1CostBit) (b := fun i => stage1CostBit (i N.limbBit)) (by simp [stage1Mod, N])) hm_lb
  have hm_sa := stage1StepActive_meets (w := w) (hp_s1.get (n := N.stage1StepActive) (b := fun _ => stage1StepActive) (by simp [stage1Mod, N]))
  have hm_ls := stage1LoadAndStep_meets (w := w) (hp_s1.get (n := N.stage1LoadAndStep) (b := fun i => stage1LoadAndStep (i N.stage1StepActive)) (by simp [stage1Mod, N])) hm_sa
  have hm_state := stage1StateUpdate_meets (w := w) (hp_s1.get (n := N.stage1StateUpdate) (b := fun i => stage1StateUpdate (i N.stage1CostBit) (i N.stage1LoadAndStep)) (by simp [stage1Mod, N])) hm_cb hm_ls
  have hm_rcCall := stage1RoundCostsCall_meets (w := w) (hp_s1.get (n := N.stage1RoundCostsCall) (b := fun i => stage1RoundCostsCall (i N.stage1RoundedCosts)) (by simp [stage1Mod, N])) hm_rc
  have hm_resCall := stage1RoundResCapsCall_meets (w := w) (hp_s1.get (n := N.stage1RoundResCapsCall) (b := fun i => stage1RoundResCapsCall (i N.stage1ResCaps)) (by simp [stage1Mod, N])) hm_resCaps
  have hm_dualCall := stage1RoundDualCall_meets (w := w) (hp_s1.get (n := N.stage1RoundDualCall) (b := fun i => stage1RoundDualCall (i N.stage1DualExtract)) (by simp [stage1Mod, N])) hm_dual
  have hm_flowCall := stage1RoundFlowCall_meets (w := w) (hp_s1.get (n := N.stage1RoundFlowCall) (b := fun i => stage1RoundFlowCall (i N.stage1FlowUpdate)) (by simp [stage1Mod, N])) hm_flow
  have hm_stateCall := stage1RoundStateCall_meets (w := w) (hp_s1.get (n := N.stage1RoundStateCall) (b := fun i => stage1RoundStateCall (i N.stage1StateUpdate)) (by simp [stage1Mod, N])) hm_state
  let T_bs : Circulation → ℕ → ℕ := fun J k =>
    720 * (bitScalingPhases J * narrowSolverTime P (J.n + 1) (2 * J.m) +
      bitScalingPhases J * J.m + J.m * (bitScalingPhases J / k + 1) +
      bitScalingPhases J + 1)
  let T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ := fun T_U n m k =>
    720 * (T_U * narrowSolverTime P (n + 1) (4 * m) + T_U * (2 * m) +
      (2 * m) * (T_U / k + 1) + T_U + 1)
  have hm_bsCall := stage1RoundBitScaleCall_meets (w := w) (T_bs := T_bs)
    (hp_s1.get (n := N.stage1RoundBitScaleCall) (b := fun i => stage1RoundBitScaleCall (i N.bitScale)) (by simp [stage1Mod, N])) hbit720
  have hbs_mono : ∀ (I : Circulation) (s : NarrowCostState I.compress) (k : ℕ),
      (∀ e, 0 ≤ s.flow e ∧ s.flow e ≤ (I.compress.capacity e : ℤ)) →
      T_bs (narrowRoundInstance I.compress s) k ≤ T_bs_max (bitScalingPhases I) I.compress.n I.m k := by
    intro I s k hfeas
    have hT : bitScalingPhases (narrowRoundInstance I.compress s) ≤ bitScalingPhases I :=
      bitScalingPhases_narrowRound_le I.compress s hfeas
    have hdiv : bitScalingPhases (narrowRoundInstance I.compress s) / k ≤ bitScalingPhases I / k :=
      Nat.div_le_div_right hT
    set J := narrowRoundInstance I.compress s
    have hJn : J.n = I.compress.n := rfl
    have hJm : J.m = 2 * I.m := by change I.m + I.m = 2 * I.m; omega
    dsimp only [T_bs, T_bs_max]
    rw [hJn, hJm, show 2 * (2 * I.m) = 4 * I.m by omega]
    apply Nat.mul_le_mul_left 720
    have h1 := Nat.mul_le_mul_right (narrowSolverTime P (I.compress.n + 1) (4 * I.m)) hT
    have h2 := Nat.mul_le_mul_right (2 * I.m) hT
    have h3 := Nat.mul_le_mul_left (2 * I.m) (Nat.add_le_add_right hdiv 1)
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) hT) (le_refl 1)
  have hm_round := stage1Round_meets (w := w) (T_bs := T_bs) (T_bs_max := T_bs_max)
    (hp_s1.get (n := topStage1Names.stage1Round)
      (b := fun i => stage1Round (i topStage1Names.stage1RoundCostsCall)
        (i topStage1Names.stage1RoundResCapsCall) (i topStage1Names.stage1RoundBitScaleCall)
        (i topStage1Names.stage1RoundDualCall) (i topStage1Names.stage1RoundFlowCall)
        (i topStage1Names.stage1RoundStateCall))
      (by simp [stage1Mod]))
    hm_rcCall hm_resCall hm_bsCall hbs_mono hm_dualCall hm_flowCall hm_stateCall
  have hm_circ := stage1Circ_meets (w := w)
    (hp_s1.get (n := topStage1Names.stage1Circ)
      (b := fun i => stage1Circ (i topStage1Names.stage1Start) (i topStage1Names.stage1Round))
      (by simp [stage1Mod])) hm_start hm_round
  exact hm_circ.withCost_mono fun x _ => stage1_uniform_cost_bound (narrowSolverTime P) x.1 x.2.1

/-! ### Whole-program `RunsTo` theorem -/

/-- **Whole-program run theorem.** On any valid instance `(I, hv)` and host word size `w`
satisfying `NarrowMainFits` and the input word/length bounds, and for any monotone envelope `B`
dominating `narrowStage1Const * narrowStage1CostShape (narrowSolverTime P)`, `narrowProgram P pkg`
halts with a correct narrow-word answer within the counted cost bound. -/
theorem narrowProgram_runsTo (P : DyadicWithVConcretePrograms) (pkg : NarrowMainPkg)
    (B : ℕ → ℕ → ℕ → ℕ → ℕ)
    (hB_mono : ∀ n n' m m' u u' c c', n ≤ n' → m ≤ m' → u ≤ u' → c ≤ c' →
      B n m u c ≤ B n' m' u' c')
    (hB_ge : ∀ (K : Circulation) (k : ℕ),
      narrowStage1Const * narrowStage1CostShape (narrowSolverTime P) K k ≤
        B K.n K.m (circMaxCapacity K) (circMaxCost K))
    {w : ℕ} {I : Instance} (hv : I.IsValid)
    (hfits : NarrowMainFits w (narrowSolverSpace P.scratchDegree) I hv)
    (hlen : (narrowEncode I).length < 2 ^ w)
    (hwords : ∀ x ∈ narrowEncode I, x < 2 ^ w) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo w (narrowProgram P pkg) (narrowEncode I) ω out cost ∧
      narrowIsCorrectAnswer I out ∧
      cost ≤ pkg.a0 * (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) +
        B (I.n + 1) (3 * I.m) (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
        B I.n (2 * I.m) (2 * I.maxCapacity) I.maxCost + 2 := by
  set ms := narrowModules P pkg
  have hnd : (linkNames ms).Nodup := narrowModules_names_nodup P pkg
  have hp_main : pkg.mainMod.Placed (narrowProgram P pkg) (linkIndex ms) :=
    link_placed hnd (by simp [ms, narrowModules])
  have hhead_idx : linkIndex ms (pkg.mainMod.procs.head pkg.mainMod_nonempty).1 = 0 := by
    have hpos : 0 < pkg.mainMod.procs.length := List.length_pos_of_ne_nil pkg.mainMod_nonempty
    have h0 := linkIndex_eq (pre := [])
      (post := [stage1Mod topStage1Names, bitScaleMod topBitScaleNames, topStdMod,
        propLabelsMod (narrowPropBase pkg), narrowSolverMod P pkg])
      (m := pkg.mainMod) hnd 0 hpos
    have hget : pkg.mainMod.procs[0]'hpos = pkg.mainMod.procs.head pkg.mainMod_nonempty :=
      (List.head_eq_getElem_zero pkg.mainMod_nonempty).symm
    simpa [hget, ms, narrowModules] using h0
  have hstage1 : Meets w (narrowProgram P pkg) (linkIndex ms (.stage1 0))
      ((stage1CircSpec w (narrowSolverSpace P.scratchDegree)).withCost fun x _ =>
        B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) :=
    (narrowProgram_stage1_meets_uniform P pkg w).withCost_mono fun x _ => hB_ge x.1 x.2.1
  have hentry := pkg.mainMod_meets w (narrowProgram P pkg) (linkIndex ms)
    (narrowSolverSpace P.scratchDegree) B
    (fun _ _ _ _ hn hm => narrowSolverSpace_mono P.scratchDegree hn hm)
    hB_mono hp_main hhead_idx hstage1
  exact runsTo_of_meets_narrowEntry hentry hv hfits hlen hwords ω

end MinCostFlow.NarrowTop
