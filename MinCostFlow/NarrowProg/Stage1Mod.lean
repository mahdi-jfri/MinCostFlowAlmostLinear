module

public import WordRAM.Module
public import WordRAM.Std.Bits
public import WordRAM.Std.Array
public import WordRAM.Std.Limbs
public import MinCostFlow.NarrowProg.LimbBit
public import MinCostFlow.NarrowProg.TopBitLength
public import MinCostFlow.NarrowProg.BitScale
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
public import MinCostFlow.NarrowProg.Stage1Layout
public import MinCostFlow.NarrowProg.Stage1StartHdr
public import MinCostFlow.NarrowProg.Stage1StartInit
public import MinCostFlow.NarrowProg.Stage1Start
public import MinCostFlow.NarrowProg.Stage1CostBit
public import MinCostFlow.NarrowProg.Stage1RoundedCosts
public import MinCostFlow.NarrowProg.Stage1DualWrite
public import MinCostFlow.NarrowProg.Stage1DualQ
public import MinCostFlow.NarrowProg.Stage1DualRouting
public import MinCostFlow.NarrowProg.Stage1Dual
public import MinCostFlow.NarrowProg.Stage1FlowUpdate
public import MinCostFlow.NarrowProg.Stage1StateUpdate
public import MinCostFlow.NarrowProg.Stage1ResCaps
public import MinCostFlow.NarrowProg.Stage1RoundPrep
public import MinCostFlow.NarrowProg.Stage1RoundApply
public import MinCostFlow.NarrowProg.Stage1Round
public import MinCostFlow.NarrowProg.Stage1Loop

/-!
# Complete polymorphic Stage 1 module (`stage1Mod`, Part 6)

Bundles all 39 Stage 1 WordRAM procedures into a single polymorphic `Module ι`
(`stage1Mod`, parameterized by `Stage1Names ι` with no `String` procedure names),
proves `(stage1Mod names).NoRand`, and wires all internal `*_meets` theorems with:
- `bitScaleSpec w S` (`MeetsO`, matching `bitScaleMod_meets` from `BitScale.lean`),
- the first-layer bounded solver (`MeetsContract w p solver (solverContract w T_sol S)`),
- the first-layer `propagateLabelsModule`, and
- the WordRAM stdlib / Round 1 primitives (`bitLength`, `clog2`, `topBitLength`,
  `limbBit`, `copy`, `limbsAdd`, `limbsSub`),

into the end-to-end big-O theorem `stage1Mod_meets` for `stage1Circ`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

/-- Procedure names for `stage1Mod`, polymorphic over any name type `ι`.
Includes the 39 Stage 1 internal procedures placed by `stage1Mod` and the 10 external
callee names (`bitScale`, `solver`, `propLabels`, `bitLength`, `clog2`, `topBitLength`,
`limbBit`, `copy`, `limbsAdd`, `limbsSub`). -/
structure Stage1Names (ι : Type) where
  -- Top-level entry
  stage1Circ : ι
  -- Startup procedures (`Stage1Start*`)
  stage1Compress : ι
  stage1DecLimbs : ι
  stage1PrepNegCosts : ι
  stage1PadCaps : ι
  stage1FillPtrs : ι
  stage1Write8 : ι
  stage1Write9 : ι
  stage1StartMeta : ι
  stage1WriteLayout : ι
  stage1StartHdr : ι
  stage1InitHalfCosts : ι
  stage1InitResEndpoints : ι
  stage1InitCapTables : ι
  stage1InitAdjCosts : ι
  stage1Start : ι
  -- Rounded costs (`Stage1RoundedCosts`)
  stage1Min : ι
  stage1RoundEdge : ι
  stage1RoundedCosts : ι
  -- Residual capacities (`Stage1ResCaps`)
  stage1CanonLen : ι
  stage1ResCaps : ι
  -- Dual extraction (`Stage1Dual*`)
  stage1WriteS : ι
  stage1WriteQEdges : ι
  stage1WriteQ : ι
  stage1BuildRouting : ι
  stage1DualExtract : ι
  -- Flow update (`Stage1FlowUpdate`)
  stage1CopyPad : ι
  stage1FlowUpdate : ι
  -- State update (`Stage1CostBit`, `Stage1StateUpdate`)
  stage1CostBit : ι
  stage1StepActive : ι
  stage1LoadAndStep : ι
  stage1StateUpdate : ι
  -- Round dispatchers & round (`Stage1Round*`)
  stage1RoundCostsCall : ι
  stage1RoundResCapsCall : ι
  stage1RoundBitScaleCall : ι
  stage1RoundDualCall : ι
  stage1RoundFlowCall : ι
  stage1RoundStateCall : ι
  stage1Round : ι
  -- External callees (placed by `bitScaleMod`, stdlib, `propagateLabelsModule`, solver)
  bitScale : ι
  solver : ι
  propLabels : ι
  bitLength : ι
  clog2 : ι
  topBitLength : ι
  limbBit : ι
  copy : ι
  limbsAdd : ι
  limbsSub : ι

/-- Complete polymorphic module containing all 39 Stage 1 procedures. -/
def stage1Mod {ι : Type} (names : Stage1Names ι) : Module ι :=
  ⟨[(names.stage1Compress, fun _ => stage1Compress),
    (names.stage1DecLimbs, fun _ => stage1DecLimbs),
    (names.stage1PrepNegCosts, fun idx =>
      stage1PrepNegCosts (idx names.stage1DecLimbs) (idx names.copy)),
    (names.stage1PadCaps, fun idx => stage1PadCaps (idx names.copy)),
    (names.stage1FillPtrs, fun _ => stage1FillPtrs),
    (names.stage1Write8, fun _ => stage1Write8),
    (names.stage1Write9, fun _ => stage1Write9),
    (names.stage1StartMeta, fun idx =>
      stage1StartMeta (idx names.topBitLength) (idx names.clog2) (idx names.bitLength)),
    (names.stage1WriteLayout, fun idx =>
      stage1WriteLayout (idx names.stage1Write8) (idx names.stage1Write9)),
    (names.stage1StartHdr, fun idx =>
      stage1StartHdr (idx names.stage1Compress) (idx names.stage1StartMeta)
        (idx names.stage1WriteLayout)),
    (names.stage1InitHalfCosts, fun idx => stage1InitHalfCosts (idx names.copy)),
    (names.stage1InitResEndpoints, fun idx => stage1InitResEndpoints (idx names.copy)),
    (names.stage1InitCapTables, fun idx =>
      stage1InitCapTables (idx names.stage1PadCaps) (idx names.stage1FillPtrs)),
    (names.stage1InitAdjCosts, fun idx => stage1InitAdjCosts (idx names.stage1PrepNegCosts)),
    (names.stage1Start, fun idx =>
      stage1Start (idx names.stage1StartHdr) (idx names.stage1InitHalfCosts)
        (idx names.stage1InitResEndpoints) (idx names.stage1InitCapTables)
        (idx names.stage1InitAdjCosts)),
    (names.stage1Min, fun _ => stage1Min),
    (names.stage1RoundEdge, fun idx => stage1RoundEdge (idx names.stage1Min)),
    (names.stage1RoundedCosts, fun idx => stage1RoundedCosts (idx names.stage1RoundEdge)),
    (names.stage1CanonLen, fun _ => stage1CanonLen),
    (names.stage1ResCaps, fun idx =>
      stage1ResCaps (idx names.limbsSub) (idx names.stage1CanonLen)),
    (names.stage1WriteS, fun _ => stage1WriteS),
    (names.stage1WriteQEdges, fun _ => stage1WriteQEdges),
    (names.stage1WriteQ, fun idx => stage1WriteQ (idx names.stage1WriteQEdges)),
    (names.stage1BuildRouting, fun _ => stage1BuildRouting),
    (names.stage1DualExtract, fun idx =>
      stage1DualExtract (idx names.stage1WriteS) (idx names.stage1WriteQ)
        (idx names.solver) (idx names.stage1BuildRouting) (idx names.propLabels)),
    (names.stage1CopyPad, fun idx => stage1CopyPad (idx names.copy)),
    (names.stage1FlowUpdate, fun idx =>
      stage1FlowUpdate (idx names.stage1CopyPad) (idx names.limbsAdd) (idx names.limbsSub)),
    (names.stage1CostBit, fun idx => stage1CostBit (idx names.limbBit)),
    (names.stage1StepActive, fun _ => stage1StepActive),
    (names.stage1LoadAndStep, fun idx => stage1LoadAndStep (idx names.stage1StepActive)),
    (names.stage1StateUpdate, fun idx =>
      stage1StateUpdate (idx names.stage1CostBit) (idx names.stage1LoadAndStep)),
    (names.stage1RoundCostsCall, fun idx =>
      stage1RoundCostsCall (idx names.stage1RoundedCosts)),
    (names.stage1RoundResCapsCall, fun idx =>
      stage1RoundResCapsCall (idx names.stage1ResCaps)),
    (names.stage1RoundBitScaleCall, fun idx =>
      stage1RoundBitScaleCall (idx names.bitScale)),
    (names.stage1RoundDualCall, fun idx =>
      stage1RoundDualCall (idx names.stage1DualExtract)),
    (names.stage1RoundFlowCall, fun idx =>
      stage1RoundFlowCall (idx names.stage1FlowUpdate)),
    (names.stage1RoundStateCall, fun idx =>
      stage1RoundStateCall (idx names.stage1StateUpdate)),
    (names.stage1Round, fun idx =>
      stage1Round (idx names.stage1RoundCostsCall) (idx names.stage1RoundResCapsCall)
        (idx names.stage1RoundBitScaleCall) (idx names.stage1RoundDualCall)
        (idx names.stage1RoundFlowCall) (idx names.stage1RoundStateCall)),
    (names.stage1Circ, fun idx =>
      stage1Circ (idx names.stage1Start) (idx names.stage1Round))]⟩

theorem stage1Mod_noRand {ι : Type} (names : Stage1Names ι) :
    (stage1Mod names).NoRand := by
  wram_no_rand

/-- End-to-end big-O specification of `stage1Mod`: in any program placing `stage1Mod names`
alongside Stage 2 (`bitScale` meeting `bitScaleMod_meets`), the bounded circulation solver,
`propagateLabelsModule`, and the stdlib/Round 1 primitives, `stage1Circ` meets
`stage1CircSpec w S` in time matching `outer_work_compressed_bound`. -/
theorem stage1Mod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {names : Stage1Names ι} {T_sol S : ℕ → ℕ → ℕ} {solBody : Stmt}
    (hp : (stage1Mod names).Placed p idx)
    (hbit : MeetsO w p (idx names.bitScale) (bitScaleSpec w S) fun d _ =>
      let T := bitScalingPhases d.I
      T * T_sol (d.I.n + 1) (2 * d.I.m) + T * d.I.m + d.I.m * (T / d.k + 1) + T + 1)
    (hsolC : MeetsContract w p (idx names.solver) (solverContract w T_sol S))
    (hsolP : p.procs[idx names.solver]? = some solBody)
    (hprop : p.HasAt (idx names.propLabels) (propagateLabelsModule (idx names.propLabels)))
    (hbl : p.procs[idx names.bitLength]? = some bitLength)
    (hclog : p.procs[idx names.clog2]? = some (clog2 (idx names.bitLength)))
    (htop : p.procs[idx names.topBitLength]? = some (topBitLength (idx names.bitLength)))
    (hlb : p.procs[idx names.limbBit]? = some limbBit)
    (hcopy : p.procs[idx names.copy]? = some copy)
    (hadd : p.procs[idx names.limbsAdd]? = some limbsAdd)
    (hsub : p.procs[idx names.limbsSub]? = some limbsSub) :
    MeetsO w p (idx names.stage1Circ) (stage1CircSpec w S) fun x _ =>
      let I := x.1
      let k := x.2.1
      let C := I.compress
      let R := narrowCostRounds C
      let T_U := bitScalingPhases I
      let L := costScaleBits I
      R * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) +
        I.m * (T_U / k + L / k + 1) + T_U + L + 1 := by
  -- External primitives
  have hm_bl := bitLength_meets (w := w) hbl
  have hm_clog := clog2_meets (w := w) hclog hm_bl
  have hm_top := topBitLength_meets (w := w) htop hm_bl
  have hm_lb := limbBit_meets (w := w) hlb
  have hm_copy := copy_meets (w := w) hcopy
  have hm_add := limbsAdd_meets (w := w) hadd
  have hm_sub := limbsSub_meets (w := w) hsub
  have hm_sol := solverContract_meets_stage1SolverSpec hsolC hsolP
  have hm_prop := propagateLabels_meets_stage1PropSpec (w := w) hprop
  -- Startup phase
  have hm_comp := stage1Compress_meets (w := w)
    (hp.get (n := names.stage1Compress) (b := fun _ => stage1Compress) (by simp [stage1Mod]))
  have hm_dec := stage1DecLimbs_meets (w := w)
    (hp.get (n := names.stage1DecLimbs) (b := fun _ => stage1DecLimbs) (by simp [stage1Mod]))
  have hm_prep := stage1PrepNegCosts_meets (w := w)
    (hp.get (n := names.stage1PrepNegCosts)
      (b := fun i => stage1PrepNegCosts (i names.stage1DecLimbs) (i names.copy))
      (by simp [stage1Mod])) hm_dec hm_copy
  have hm_pad := stage1PadCaps_meets (w := w)
    (hp.get (n := names.stage1PadCaps)
      (b := fun i => stage1PadCaps (i names.copy)) (by simp [stage1Mod])) hm_copy
  have hm_fill := stage1FillPtrs_meets (w := w)
    (hp.get (n := names.stage1FillPtrs) (b := fun _ => stage1FillPtrs) (by simp [stage1Mod]))
  have hm_w8 := stage1Write8_meets (w := w)
    (hp.get (n := names.stage1Write8) (b := fun _ => stage1Write8) (by simp [stage1Mod]))
  have hm_w9 := stage1Write9_meets (w := w)
    (hp.get (n := names.stage1Write9) (b := fun _ => stage1Write9) (by simp [stage1Mod]))
  have hm_meta := stage1StartMeta_meets (w := w)
    (hp.get (n := names.stage1StartMeta)
      (b := fun i => stage1StartMeta (i names.topBitLength) (i names.clog2) (i names.bitLength))
      (by simp [stage1Mod])) hm_top hm_clog hm_bl
  have hm_lay := stage1WriteLayout_meets (w := w)
    (hp.get (n := names.stage1WriteLayout)
      (b := fun i => stage1WriteLayout (i names.stage1Write8) (i names.stage1Write9))
      (by simp [stage1Mod])) hm_w8 hm_w9
  have hm_hdr := stage1StartHdr_meets (w := w)
    (hp.get (n := names.stage1StartHdr)
      (b := fun i => stage1StartHdr (i names.stage1Compress) (i names.stage1StartMeta)
        (i names.stage1WriteLayout)) (by simp [stage1Mod])) hm_comp hm_meta hm_lay
  have hm_half := stage1InitHalfCosts_meets (w := w)
    (hp.get (n := names.stage1InitHalfCosts)
      (b := fun i => stage1InitHalfCosts (i names.copy)) (by simp [stage1Mod])) hm_copy
  have hm_rep := stage1InitResEndpoints_meets (w := w)
    (hp.get (n := names.stage1InitResEndpoints)
      (b := fun i => stage1InitResEndpoints (i names.copy)) (by simp [stage1Mod])) hm_copy
  have hm_ct := stage1InitCapTables_meets (w := w)
    (hp.get (n := names.stage1InitCapTables)
      (b := fun i => stage1InitCapTables (i names.stage1PadCaps) (i names.stage1FillPtrs))
      (by simp [stage1Mod])) hm_pad hm_fill
  have hm_adj := stage1InitAdjCosts_meets (w := w)
    (hp.get (n := names.stage1InitAdjCosts)
      (b := fun i => stage1InitAdjCosts (i names.stage1PrepNegCosts))
      (by simp [stage1Mod])) hm_prep
  have hm_start := stage1Start_meets (w := w)
    (hp.get (n := names.stage1Start)
      (b := fun i => stage1Start (i names.stage1StartHdr) (i names.stage1InitHalfCosts)
        (i names.stage1InitResEndpoints) (i names.stage1InitCapTables)
        (i names.stage1InitAdjCosts)) (by simp [stage1Mod]))
    hm_hdr hm_half hm_rep hm_ct hm_adj
  -- Round step primitives
  have hm_min := stage1Min_meets (w := w)
    (hp.get (n := names.stage1Min) (b := fun _ => stage1Min) (by simp [stage1Mod]))
  have hm_re := stage1RoundEdge_meets (w := w)
    (hp.get (n := names.stage1RoundEdge)
      (b := fun i => stage1RoundEdge (i names.stage1Min)) (by simp [stage1Mod])) hm_min
  have hm_rc := stage1RoundedCosts_meets (w := w)
    (hp.get (n := names.stage1RoundedCosts)
      (b := fun i => stage1RoundedCosts (i names.stage1RoundEdge)) (by simp [stage1Mod])) hm_re
  have hm_can := stage1CanonLen_meets (w := w)
    (hp.get (n := names.stage1CanonLen) (b := fun _ => stage1CanonLen) (by simp [stage1Mod]))
  have hm_resCaps := stage1ResCaps_meets (w := w) (Tsub := fun n => 60 * n + 30)
    (hp.get (n := names.stage1ResCaps)
      (b := fun i => stage1ResCaps (i names.limbsSub) (i names.stage1CanonLen))
      (by simp [stage1Mod])) hm_sub (fun n => by omega) hm_can
  have hm_ws := stage1WriteS_meets (w := w)
    (hp.get (n := names.stage1WriteS) (b := fun _ => stage1WriteS) (by simp [stage1Mod]))
  have hm_wqe := stage1WriteQEdges_meets (w := w)
    (hp.get (n := names.stage1WriteQEdges) (b := fun _ => stage1WriteQEdges) (by simp [stage1Mod]))
  have hm_wq := stage1WriteQ_meets (w := w)
    (hp.get (n := names.stage1WriteQ)
      (b := fun i => stage1WriteQ (i names.stage1WriteQEdges)) (by simp [stage1Mod])) hm_wqe
  have hm_br := stage1BuildRouting_meets (w := w)
    (hp.get (n := names.stage1BuildRouting) (b := fun _ => stage1BuildRouting)
      (by simp [stage1Mod]))
  have hm_dual := stage1DualExtract_meets (w := w)
    (hp.get (n := names.stage1DualExtract)
      (b := fun i => stage1DualExtract (i names.stage1WriteS) (i names.stage1WriteQ)
        (i names.solver) (i names.stage1BuildRouting) (i names.propLabels))
      (by simp [stage1Mod])) hm_ws hm_wq hm_sol hm_br hm_prop
  have hm_cp := stage1CopyPad_meets (w := w)
    (hp.get (n := names.stage1CopyPad)
      (b := fun i => stage1CopyPad (i names.copy)) (by simp [stage1Mod])) hm_copy
  have hm_flow := stage1FlowUpdate_meets (w := w)
    (hp.get (n := names.stage1FlowUpdate)
      (b := fun i => stage1FlowUpdate (i names.stage1CopyPad) (i names.limbsAdd)
        (i names.limbsSub)) (by simp [stage1Mod])) hm_cp hm_add hm_sub
  have hm_cb := stage1CostBit_meets (w := w)
    (hp.get (n := names.stage1CostBit)
      (b := fun i => stage1CostBit (i names.limbBit)) (by simp [stage1Mod])) hm_lb
  have hm_sa := stage1StepActive_meets (w := w)
    (hp.get (n := names.stage1StepActive) (b := fun _ => stage1StepActive) (by simp [stage1Mod]))
  have hm_ls := stage1LoadAndStep_meets (w := w)
    (hp.get (n := names.stage1LoadAndStep)
      (b := fun i => stage1LoadAndStep (i names.stage1StepActive)) (by simp [stage1Mod])) hm_sa
  have hm_state := stage1StateUpdate_meets (w := w)
    (hp.get (n := names.stage1StateUpdate)
      (b := fun i => stage1StateUpdate (i names.stage1CostBit) (i names.stage1LoadAndStep))
      (by simp [stage1Mod])) hm_cb hm_ls
  -- Round dispatchers
  have hm_rcCall := stage1RoundCostsCall_meets (w := w)
    (hp.get (n := names.stage1RoundCostsCall)
      (b := fun i => stage1RoundCostsCall (i names.stage1RoundedCosts))
      (by simp [stage1Mod])) hm_rc
  have hm_resCall := stage1RoundResCapsCall_meets (w := w)
    (hp.get (n := names.stage1RoundResCapsCall)
      (b := fun i => stage1RoundResCapsCall (i names.stage1ResCaps))
      (by simp [stage1Mod])) hm_resCaps
  have hm_dualCall := stage1RoundDualCall_meets (w := w)
    (hp.get (n := names.stage1RoundDualCall)
      (b := fun i => stage1RoundDualCall (i names.stage1DualExtract))
      (by simp [stage1Mod])) hm_dual
  have hm_flowCall := stage1RoundFlowCall_meets (w := w)
    (hp.get (n := names.stage1RoundFlowCall)
      (b := fun i => stage1RoundFlowCall (i names.stage1FlowUpdate))
      (by simp [stage1Mod])) hm_flow
  have hm_stateCall := stage1RoundStateCall_meets (w := w)
    (hp.get (n := names.stage1RoundStateCall)
      (b := fun i => stage1RoundStateCall (i names.stage1StateUpdate))
      (by simp [stage1Mod])) hm_state
  -- Unpack Stage 2 (`bitScale`) big-O constant `K`
  obtain ⟨K, hbitK⟩ := hbit
  let T_bs : Circulation → ℕ → ℕ := fun J k =>
    K * (bitScalingPhases J * T_sol (J.n + 1) (2 * J.m) + bitScalingPhases J * J.m +
      J.m * (bitScalingPhases J / k + 1) + bitScalingPhases J + 1)
  let T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ := fun T_U n m k =>
    K * (T_U * T_sol (n + 1) (4 * m) + T_U * (2 * m) + (2 * m) * (T_U / k + 1) + T_U + 1)
  have hm_bsCall := stage1RoundBitScaleCall_meets (w := w) (T_bs := T_bs)
    (hp.get (n := names.stage1RoundBitScaleCall)
      (b := fun i => stage1RoundBitScaleCall (i names.bitScale))
      (by simp [stage1Mod])) hbitK
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
    change K * (bitScalingPhases J * T_sol (J.n + 1) (2 * J.m) + bitScalingPhases J * J.m +
        J.m * (bitScalingPhases J / k + 1) + bitScalingPhases J + 1) ≤
      K * (bitScalingPhases I * T_sol (I.compress.n + 1) (4 * I.m) +
        bitScalingPhases I * (2 * I.m) + (2 * I.m) * (bitScalingPhases I / k + 1) +
        bitScalingPhases I + 1)
    rw [hJn, hJm, show 2 * (2 * I.m) = 4 * I.m by omega]
    apply Nat.mul_le_mul_left K
    have h1 := Nat.mul_le_mul_right (T_sol (I.compress.n + 1) (4 * I.m)) hT
    have h2 := Nat.mul_le_mul_right (2 * I.m) hT
    have h3 := Nat.mul_le_mul_left (2 * I.m) (Nat.add_le_add_right hdiv 1)
    omega
  have hm_round := stage1Round_meets (w := w) (T_bs := T_bs) (T_bs_max := T_bs_max)
    (hp.get (n := names.stage1Round)
      (b := fun i => stage1Round (i names.stage1RoundCostsCall) (i names.stage1RoundResCapsCall)
        (i names.stage1RoundBitScaleCall) (i names.stage1RoundDualCall)
        (i names.stage1RoundFlowCall) (i names.stage1RoundStateCall))
      (by simp [stage1Mod]))
    hm_rcCall hm_resCall hm_bsCall hbs_mono hm_dualCall hm_flowCall hm_stateCall
  have hm_circ := stage1Circ_meetsO (w := w)
    (hp.get (n := names.stage1Circ)
      (b := fun i => stage1Circ (i names.stage1Start) (i names.stage1Round))
      (by simp [stage1Mod])) hm_start hm_round
  refine hm_circ.trans ⟨2 * K + 1, fun x => ?_⟩
  set I := x.1.1
  set k := x.1.2.1
  set C := I.compress
  set R := narrowCostRounds C
  set T_U := bitScalingPhases I
  set L := costScaleBits I
  set G_round := T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
    T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1
  set G_init := I.m * (T_U / k + L / k + 1) + T_U + L + 1
  have hinner : T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
      I.m * (T_U / k + 1) + C.n + 1 ≤ (2 * K + 1) * G_round := by
    dsimp only [T_bs_max, G_round]
    have hmul : T_U * (2 * I.m) = 2 * (T_U * I.m) := by ring
    have hmul2 : 2 * I.m * (T_U / k + 1) = 2 * (I.m * (T_U / k + 1)) := by ring
    rw [hmul, hmul2]
    have hK2 : K * (T_U * T_sol (C.n + 1) (4 * I.m) + 2 * (T_U * I.m) +
        2 * (I.m * (T_U / k + 1)) + T_U + 1) ≤
        2 * K * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) := by
      have heq : 2 * K * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) =
          K * (2 * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1)) := by ring
      rw [heq]
      apply Nat.mul_le_mul_left K
      omega
    have heq2 : (2 * K + 1) * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
        T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) =
        2 * K * (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) +
        (T_U * T_sol (C.n + 1) (4 * I.m) + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
          T_U * I.m + I.m * (T_U / k + 1) + T_U + C.n + 1) := by ring
    omega
  have hR_le : R * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
      I.m * (T_U / k + 1) + C.n + 1) ≤ (2 * K + 1) * (R * G_round) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 * K + 1) R, Nat.mul_assoc]
    exact Nat.mul_le_mul_left R hinner
  have hGinit : G_init ≤ (2 * K + 1) * G_init := Nat.le_mul_of_pos_left _ (by omega)
  have hsum : R * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
        I.m * (T_U / k + 1) + C.n + 1) + G_init ≤
      (2 * K + 1) * (R * G_round + G_init) := by
    rw [Nat.mul_add (2 * K + 1)]
    exact Nat.add_le_add hR_le hGinit
  dsimp only [I, k, C, R, T_U, L, G_round, G_init] at hsum ⊢
  simpa only [Nat.add_assoc] using hsum

end MinCostFlow.NarrowProg.Stage1
