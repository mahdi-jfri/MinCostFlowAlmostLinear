module

public import MinCostFlow.ExpanderDecomp.CoreProgOn
public import MinCostFlow.ExpanderDecomp.CorePlayer
public import MinCostFlow.ExpanderDecomp.ProgCloud
public import MinCostFlow.ExpanderDecomp.ProgEdgeColor
public import MinCostFlow.ExpanderDecomp.ProgRemoveFake
public import MinCostFlow.ExpanderDecomp.ProgStepBSpec
public import MinCostFlow.ExpanderDecomp.ProgStepC
public import MinCostFlow.ExpanderDecomp.ProgStepCLeftover
public import MinCostFlow.ExpanderDecomp.OneShotProgFilterEdges
public import MinCostFlow.ExpanderDecomp.OneShotProgCompleteFake
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Standalone `Core` Word-RAM Entry Point and Module (`CoreProg`)

Provides the whole-graph entry procedure `coreEntryProc`, its core-theorem contract
`coreEntryContract` (delivering `CoreOutcomeSpec cfg M q G res` and the closed-form and size-sensitive time
bounds), the concrete procedure bundle `coreModuleProcs` (linking `ProgCloud.cloudExpanderProcs`,
`ProgEdgeColor.edgeColor17Proc`, `ProgRemoveFake.removeFakeProcs`, `ProgStepC.stepCProc`,
`ProgStepCLeftover.stepCLeftoverProc`, and all internal `OneShot`/`Core` procedures so that only
the multi-pair router and Step B remain as external contracts), determinism (`coreModuleProcs_noRand`),
full module verification (`coreModule_meetsContract_B`), and a concrete non-vacuity witness
(`coreEntryContract_pre_example`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Whole-Graph Space/Time Envelopes, `coreEntryProc`, and `coreEntryContract` -/

/-- Heap advance and word-size headroom bound for `coreEntryProc` at level `q`. -/
def coreEntrySpace (S_B S_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) : ℕ :=
  coreProgSpace S_B S_C cfg M r q + 2 * (NOf M r) ^ q

/-- Step-count bound for `coreEntryProc` at level `q`. -/
def coreEntryTime (K_B K_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) : ℕ :=
  coreProgTime K_B K_C cfg M r q + 25 * (NOf M r) ^ q + 100

/-- Standalone deterministic Word-RAM entry procedure for whole-graph `Core(q, G)`
(the core theorem `core_spec`). `args = [q, gAddr, pAddr, outAddr, h]`: allocates a zeroed marker buffer
`locAddr = h` and vertex array `xAddr = h + G.n` via `idx.initRange`, then calls `idx.coreOn`. -/
def coreEntryProc (idx : CoreIdx) : Stmt :=
  seqStmts
    [ .assign 5 (.load (.reg 1))
    , .assign 6 (.reg 4)
    , .assign 7 (.bin .add (.reg 4) (.reg 5))
    , .assign 8 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5)))
    , .call 9 idx.initRange [.reg 5, .reg 7]
    , .call 8 idx.coreOn
        [.reg 0, .reg 1, .reg 5, .reg 7, .reg 2, .reg 6, .reg 3, .reg 8]
    , .ret (.reg 8) ]

/-- Core-theorem whole-graph Word-RAM contract for `coreEntryProc`:
`args = [q, gAddr, pAddr, outAddr, h]`. Delivers `CoreOutcomeSpec cfg M q G res` at `outAddr`
(`CoreOutAt`), heap advance `v ∈ [h, h + coreEntrySpace]` with `ZeroFrom mem' v`, frame below `h`
outside `[outAddr, outAddr + 2 + G.n)`, and step count `≤ coreEntryTime`. -/
noncomputable def coreEntryContract (cfg : ParamConfig) (M r w K_B C_stepC C_left S_B C_sp : ℕ) :
    Contract where
  pre args mem :=
    let cp := coreParamsOf cfg M r
    let S_C := stepCSpaceConst C_sp
    ∃ (q gAddr pAddr outAddr h : ℕ) (G : Graph),
      args = [q, gAddr, pAddr, outAddr, h] ∧
      12 ≤ cfg.a₀ ∧ 4 ≤ cfg.a ∧ r ≤ ell M ∧ q ≤ r ∧
      CoreParamsAt mem pAddr cp r ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      G.IsLoopless ∧
      G.n ≤ cp.N ^ q ∧
      (∀ v < G.n, G.deg v ≤ cp.Δ) ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      pAddr + coreParamsSize r ≤ h ∧
      outAddr + 2 + G.n ≤ h ∧
      DisjointRange outAddr (2 + G.n) gAddr (2 + 2 * G.m) ∧
      DisjointRange outAddr (2 + G.n) pAddr (coreParamsSize r) ∧
      ZeroFrom mem h ∧
      h + coreEntrySpace S_B S_C cfg M r q < 2 ^ w
  post args mem v mem' :=
    let cp := coreParamsOf cfg M r
    let S_C := stepCSpaceConst C_sp
    ∀ (q gAddr pAddr outAddr h : ℕ) (G : Graph),
      args = [q, gAddr, pAddr, outAddr, h] →
      12 ≤ cfg.a₀ → 4 ≤ cfg.a → r ≤ ell M → q ≤ r →
      CoreParamsAt mem pAddr cp r →
      GraphAt mem gAddr G →
      G.IsValid →
      G.IsLoopless →
      G.n ≤ cp.N ^ q →
      (∀ v < G.n, G.deg v ≤ cp.Δ) →
      gAddr + 2 + 2 * G.m ≤ h →
      pAddr + coreParamsSize r ≤ h →
      outAddr + 2 + G.n ≤ h →
      DisjointRange outAddr (2 + G.n) gAddr (2 + 2 * G.m) →
      DisjointRange outAddr (2 + G.n) pAddr (coreParamsSize r) →
      ZeroFrom mem h →
      h + coreEntrySpace S_B S_C cfg M r q < 2 ^ w →
      (∃ res : CoreResult, CoreOutAt mem' outAddr res ∧ CoreOutcomeSpec cfg M q G res) ∧
      h ≤ v ∧ v ≤ h + coreEntrySpace S_B S_C cfg M r q ∧
      ZeroFrom mem' v ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + G.n ≤ a) → mem' a = mem a)
  cost args _ :=
    coreEntryTime K_B (stepCTimeConst C_stepC C_left) cfg M r (args.getD 0 0)

/-! ## 2. Concrete Procedure Table (`coreModuleIdx`, `coreModuleProcs`) -/

/-- Procedure index layout for `coreModuleProcs` placed at `base`, with external procedure indices
`stepBIdx` (Step B) and `routeIdx` (multi-pair router `multiPairRouterContract`). -/
def coreModuleIdx (base stepBIdx routeIdx : ℕ) : CoreIdx :=
  let cloudBase := base + 13
  let rfBase := cloudBase + (cloudExpanderProcs 0).length
  { copyWords     := base
    initRange     := base + 1
    filterDiff    := base + 2
    filterInter   := base + 3
    filterEdgesIn := base + 4
    completeFake  := base + 5
    edgeColor17   := base + 6
    stepD         := base + 7
    stepCMacro    := base + 8
    stepCLeftover := base + 9
    oneShot       := base + 10
    coreOn        := base + 11
    core          := base + 12
    cloudExpander := cloudBase
    removeFake    := rfBase
    stepB         := stepBIdx
    stepBRound    := 0
    routeOrCut    := routeIdx }

/-- Complete deterministic Word-RAM procedure bundle for `Core` and `OneShot` placed at `base`,
concretely installing all internal helpers together with `ProgCloud.cloudExpanderProcs`,
`ProgEdgeColor.edgeColor17Proc`, `ProgRemoveFake.removeFakeProcs`, `ProgStepC.stepCProc routeIdx`,
and `ProgStepCLeftover.stepCLeftoverProc routeIdx`. -/
def coreModuleProcs (base stepBIdx routeIdx : ℕ) : List Stmt :=
  let idx := coreModuleIdx base stepBIdx routeIdx
  [ copyWordsProc
  , initRangeProc
  , filterDiffProc
  , filterInterProc
  , filterEdgesInProc
  , completeFakeProc
  , edgeColor17Proc
  , stepDProc idx
  , stepCProc routeIdx
  , stepCLeftoverProc routeIdx
  , oneShotProc idx
  , coreOnProc idx
  , coreEntryProc idx ] ++
    cloudExpanderProcs idx.cloudExpander ++
    removeFakeProcs idx.removeFake

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. Determinism (`NoRand`) and the Closed-Form and Size-Sensitive Time Bounds -/

lemma coreEntryProc_noRand (idx : CoreIdx) : (coreEntryProc idx).NoRand := by
  simp [coreEntryProc, seqStmts, Stmt.NoRand]

/-- Every procedure in `coreModuleProcs` is deterministic (`NoRand`). -/
theorem coreModuleProcs_noRand (base stepBIdx routeIdx : ℕ) :
    ∀ s ∈ coreModuleProcs base stepBIdx routeIdx, s.NoRand := by
  intro s hs
  unfold coreModuleProcs at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with
    ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hcloud) | hrf
  · exact copyWordsProc_noRand
  · exact initRangeProc_noRand
  · exact filterSetProc_noRand false
  · exact filterSetProc_noRand true
  · exact filterEdgesInProc_noRand
  · exact completeFakeProc_noRand
  · exact edgeColor17Proc_noRand
  · exact stepDProc_noRand _
  · exact stepCProc_noRand _
  · exact stepCLeftoverProc_noRand _
  · exact oneShotProc_noRand _
  · exact coreOnProc_noRand _
  · exact coreEntryProc_noRand _
  · exact cloudExpanderProcs_noRand _ s hcloud
  · exact removeFakeProcs_noRand _ s hrf

/-- **Closed-form time bound** for `coreEntryProc`: `coreEntryTime` is bounded by a fixed constant multiple
of `coreTimeBound cfg M r q`. -/
theorem coreEntryTime_le_coreTimeBound (K_B K_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) :
    coreEntryTime K_B K_C cfg M r q ≤
      (coreTimeConst K_B K_C + 25) * coreTimeBound cfg M r q + 100 := by
  unfold coreEntryTime coreProgTime
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hW1 : 1 ≤ WParam cfg M := by unfold WParam; omega
  have hNq : (NOf M r) ^ q ≤ coreTimeBound cfg M r q := by
    unfold coreTimeBound
    have hpow : (NOf M r) ^ q ≤ (NOf M r) ^ (q + 1) := Nat.pow_le_pow_right hN1 (by omega)
    have hWp : 1 ≤ (WParam cfg M) ^ (10 * q ^ 2 + 10) := Nat.one_le_pow _ _ hW1
    calc (NOf M r) ^ q = (NOf M r) ^ q * 1 := (Nat.mul_one _).symm
      _ ≤ (NOf M r) ^ (q + 1) * (WParam cfg M) ^ (10 * q ^ 2 + 10) := Nat.mul_le_mul hpow hWp
  have hmul : 25 * (NOf M r) ^ q ≤ 25 * coreTimeBound cfg M r q :=
    Nat.mul_le_mul_left 25 hNq
  rw [Nat.add_mul]
  linarith only [hmul]

/-- **Size-sensitive time bound** (at `q = coreLevel M r n`): for `2 ≤ n ≤ N ^ r`,
`coreEntryTime` at `coreLevel M r n` is `O(n * N ^ 2 * W ^ (10 * r ^ 2 + 10))`. -/
theorem coreEntryTime_coreLevel_le (K_B K_C : ℕ) (cfg : ParamConfig) {M r n : ℕ}
    (hn2 : 2 ≤ n) (hnr : n ≤ (NOf M r) ^ r) :
    coreEntryTime K_B K_C cfg M r (coreLevel M r n) ≤
      (coreTimeConst K_B K_C + 25) *
        (n * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) + 100 := by
  have h1 := coreEntryTime_le_coreTimeBound K_B K_C cfg M r (coreLevel M r n)
  have h2 := coreTimeBound_size_sensitive cfg M r (one_le_coreLevel hn2) (coreLevel_le hnr)
    (pow_pred_coreLevel_lt hn2)
  have h3 := Nat.mul_le_mul_left (coreTimeConst K_B K_C + 25) h2
  linarith only [h1, h3]

/-! ## 4. Verification of `coreEntryProc` and `coreModuleProcs` -/

private lemma graph_m_le_delta_mul_n {G : Graph} {Δ : ℕ}
    (hGvalid : G.IsValid) (hdeg : ∀ v < G.n, G.deg v ≤ Δ) :
    G.m ≤ Δ * G.n := by
  have hvol : G.volIn G.verts G.verts = 2 * G.m := by
    rw [volIn_self, inside_verts_of_isValid hGvalid]; rfl
  have hsum : G.volIn G.verts G.verts ≤ ∑ _v ∈ G.verts, Δ := by
    unfold Graph.volIn
    refine Finset.sum_le_sum fun v hv => ?_
    have hlt : v < G.n := Finset.mem_range.mp hv
    have hle : G.degIn G.verts v ≤ G.deg v := by
      simp [Graph.degIn, Graph.deg, inside_verts_of_isValid hGvalid]
    exact le_trans hle (hdeg v hlt)
  rw [hvol, Finset.sum_const, Graph.verts, Finset.card_range, smul_eq_mul] at hsum
  have hcomm : G.n * Δ = Δ * G.n := Nat.mul_comm _ _
  omega

/-- **Core-theorem whole-graph verification**: `coreEntryProc idx` meets
`coreEntryContract` given verified `idx.initRange` and `idx.coreOn`. -/
theorem coreEntryProc_meetsContract {w : ℕ} {p : Program} {idx : CoreIdx}
    {cfg : ParamConfig} {M r K_B C_stepC C_left S_B C_sp : ℕ}
    (hself : p.procs[idx.core]? = some (coreEntryProc idx))
    (hInit : MeetsContract w p idx.initRange (initRangeContract w))
    (hCoreOn : MeetsContract w p idx.coreOn
      (coreOnContract cfg M r w K_B (stepCTimeConst C_stepC C_left)
        S_B (stepCSpaceConst C_sp))) :
    MeetsContract w p idx.core (coreEntryContract cfg M r w K_B C_stepC C_left S_B C_sp) := by
  set K_C := stepCTimeConst C_stepC C_left
  set S_C := stepCSpaceConst C_sp
  refine meetsContract_of_runs hself fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨q, gAddr, pAddr, outAddr, h, G,
    rfl, ha0, ha, hrl, hqr, hP, hG, hGvalid, hGloop, hGnNq, hdeg,
    hg_h, hp_h, hout_h, hd_og, hd_op, hZero, hw⟩
  set cp := coreParamsOf cfg M r
  have hsp4000 : 4000 ≤ coreProgSpace S_B S_C cfg M r q :=
    coreProgSpace_base_ge S_B S_C cfg M r q
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hGn_bound : G.n ≤ 2048 * LParam M * (NOf M r) ^ r := by
    have hpow : (NOf M r) ^ q ≤ (NOf M r) ^ r := Nat.pow_le_pow_right hN1 hqr
    have h1 : 1 ≤ 2048 * LParam M := by omega
    calc G.n ≤ (NOf M r) ^ q := hGnNq
      _ ≤ (NOf M r) ^ r := hpow
      _ = 1 * (NOf M r) ^ r := (Nat.one_mul _).symm
      _ ≤ (2048 * LParam M) * (NOf M r) ^ r := Nat.mul_le_mul_right _ h1
  have hmG : G.m ≤ cp.Δ * G.n := graph_m_le_delta_mul_n hGvalid hdeg
  have hdegIn : ∀ v ∈ G.verts, G.degIn G.verts v ≤ cp.Δ := fun v hv => by
    have hle : G.degIn G.verts v ≤ G.deg v := by
      simp [Graph.degIn, Graph.deg, inside_verts_of_isValid hGvalid]
    exact le_trans hle (hdeg v (Finset.mem_range.mp hv))
  have hcs : coreParamsSize r = 7 + 3 * r := rfl
  have hw2 : 2 < 2 ^ w := by unfold coreEntrySpace at hw; omega
  have h2n_w : 2 * G.n < 2 ^ w := by
    have : G.n ≤ (NOf M r) ^ q := hGnNq
    unfold coreEntrySpace at hw; omega
  have hh2n_w : h + 2 * G.n < 2 ^ w := by
    have : G.n ≤ (NOf M r) ^ q := hGnNq
    unfold coreEntrySpace at hw; omega
  refine runs_start_le ?_
  dsimp only [coreEntryProc, seqStmts]
  -- 1. `r5 := mem[gAddr] = G.n`
  refine runs_seq_assign_le (v := G.n)
    (graphAt_n hG ▸ Expr.eval_load (Expr.eval_reg_of_eq (by simp [startState]))) ?_
  -- 2. `r6 := h` (`locAddr`)
  refine runs_seq_assign_le (v := h) (Expr.eval_reg_of_eq (by simp [startState])) ?_
  -- 3. `r7 := h + G.n` (`xAddr`)
  refine runs_seq_assign_le (v := h + G.n)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
  -- 4. `r8 := h + 2 * G.n` (`h1`)
  refine runs_seq_assign_le (v := h + 2 * G.n)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_mul (Expr.eval_const hw2) (Expr.eval_reg_of_eq (by simp)) h2n_w) hh2n_w) ?_
  -- 5. `call idx.initRange [G.n, h + G.n]`
  have hInit_pre : (initRangeContract w).pre [G.n, h + G.n] mem :=
    ⟨G.n, h + G.n, rfl, by omega, by omega, by unfold coreEntrySpace at hw; omega⟩
  refine runs_seq_call_le (vs := [G.n, h + G.n]) hInit
    (by simp [evalArgs, Expr.eval])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> omega)
    hInit_pre ?_
  intro _v1 mem1 _pos1 hpostInit
  simp only [initRangeContract, List.getD_cons_zero, List.getD_cons_succ] at hpostInit
  rcases hpostInit with ⟨_, hX1, hfr1⟩
  -- Preserve `CoreParamsAt`, `GraphAt`, `locAddr = h` zeroed, and `ZeroFrom mem1 (h + 2 * G.n)`
  have hP1 : CoreParamsAt mem1 pAddr cp r := by
    have hag : ∀ a, pAddr ≤ a → a < pAddr + coreParamsSize r → mem1 a = mem a :=
      fun a h1 h2 => hfr1 a (Or.inl (by omega))
    refine ⟨by rw [hag pAddr le_rfl (by omega)]; exact hP.1,
      by rw [hag (pAddr + 1) (by omega) (by omega)]; exact hP.2.1,
      by rw [hag (pAddr + 2) (by omega) (by omega)]; exact hP.2.2.1,
      by rw [hag (pAddr + 3) (by omega) (by omega)]; exact hP.2.2.2.1,
      fun j hj => by rw [hag (pAddr + 4 + j) (by omega) (by omega)]; exact hP.2.2.2.2.1 j hj,
      fun j hj => by rw [hag (pAddr + 5 + r + j) (by omega) (by omega)]; exact hP.2.2.2.2.2.1 j hj,
      fun j hj => by rw [hag (pAddr + 6 + 2 * r + j) (by omega) (by omega)]; exact hP.2.2.2.2.2.2 j hj⟩
  have hG1 : GraphAt mem1 gAddr G :=
    hG.congr fun a h1 h2 => by
      have hlenG : G.encode.length = 2 + 2 * G.m := graph_encode_length G
      exact hfr1 a (Or.inl (by omega))
  have hloc1 : ∀ u < G.n, mem1 (h + u) = 0 := fun u hu => by
    rw [hfr1 (h + u) (Or.inl (by omega))]
    exact hZero (h + u) (by omega)
  have hZero1 : ZeroFrom mem1 (h + 2 * G.n) := fun a ha => by
    rw [hfr1 a (Or.inr (by omega))]
    exact hZero a (by omega)
  have hw_core : h + 2 * G.n + coreProgSpace S_B S_C cfg M r q < 2 ^ w := by
    have hGn' : G.n ≤ (NOf M r) ^ q := hGnNq
    have hw' : h + (coreProgSpace S_B S_C cfg M r q + 2 * (NOf M r) ^ q) < 2 ^ w := hw
    omega
  -- 6. `call idx.coreOn [q, gAddr, G.n, h + G.n, pAddr, h, outAddr, h + 2 * G.n]`
  have hCO_pre : (coreOnContract cfg M r w K_B K_C S_B S_C).pre
      [q, gAddr, G.n, h + G.n, pAddr, h, outAddr, h + 2 * G.n] mem1 :=
    ⟨q, gAddr, G.n, h + G.n, pAddr, h, outAddr, h + 2 * G.n, G, G.verts,
      rfl, ha0, ha, hrl, hqr, hP1, hG1, hGvalid, hGn_bound, hX1, Finset.Subset.refl _,
      fun e he => hGloop e (mem_inside_iff.mp he).1, hGnNq, hdegIn, hmG, hloc1,
      by omega, by omega, by omega, by omega, by omega,
      Or.inr (by omega), Or.inl le_rfl, Or.inr hp_h, Or.inr (by omega), hd_og, Or.inl (by omega),
      hd_op, hZero1, hw_core⟩
  refine runs_seq_call_le
    (vs := [q, gAddr, G.n, h + G.n, pAddr, h, outAddr, h + 2 * G.n]) hCoreOn
    (by simp [evalArgs, Expr.eval, startState])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hCO_pre ?_
  intro hFin memFin _posFin hpostCO
  have hCO_res := hpostCO q gAddr G.n (h + G.n) pAddr h outAddr (h + 2 * G.n) G G.verts
    rfl ha0 ha hrl hqr hP1 hG1 hGvalid hGn_bound hX1 (Finset.Subset.refl _)
    (fun e he => hGloop e (mem_inside_iff.mp he).1) hGnNq hdegIn hmG hloc1
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inl le_rfl) (Or.inr hp_h) (Or.inr (by omega)) hd_og
    (Or.inl (by omega)) hd_op hZero1 hw_core
  rcases hCO_res with ⟨⟨res, hResOut, hResSpec⟩, hhFin_lo, hhFin_hi, hZeroFin, _, hfrFin⟩
  -- 7. `ret r8` (= hFin)
  refine runs_ret_le (v := hFin) (by simp [Expr.eval]) ?_ ?_
  · intro q' gAddr' pAddr' outAddr' h' G' hargs'
      _ _ _ _ _ hG' _ _ _ _ _ _ _ _ _ _ _
    simp only [List.cons.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
    have hG_eq : G = G' := by
      rw [← readGraph_eq_of_graphAt hG, readGraph_eq_of_graphAt hG']
    rcases hG_eq with rfl
    simp only [Outcome.value]
    refine ⟨⟨res, hResOut, coreOutcomeSpec_of_coreSpec hResSpec⟩, by omega, ?_,
      hZeroFin, ?_⟩
    · have hGn' : G.n ≤ (NOf M r) ^ q := hGnNq
      change hFin ≤ h + (coreProgSpace S_B S_C cfg M r q + 2 * (NOf M r) ^ q)
      change hFin ≤ h + 2 * G.n + coreProgSpace S_B S_C cfg M r q at hhFin_hi
      omega
    · intro a ha hno
      rw [hfrFin a (by omega) hno]
      exact hfr1 a (Or.inl (by omega))
  · have hargI : argsSize [.reg 5, .reg 7] = 2 := by decide
    have hargC : argsSize [.reg 0, .reg 1, .reg 5, .reg 7, .reg 2, .reg 6, .reg 3,
      .reg 8] = 8 := by decide
    simp only [coreEntryContract, initRangeContract, coreOnContract, Expr.size, hargI, hargC,
      initRangeCost, List.getD_cons_zero]
    unfold coreEntryTime
    have hGn' : G.n ≤ (NOf M r) ^ q := hGnNq
    linarith only [hGn']

private lemma cloudExpanderProcs_length_eq (b : ℕ) :
    (cloudExpanderProcs b).length = (cloudExpanderProcs 0).length := by
  simp [cloudExpanderProcs, runner]

/-- Whenever `n ≤ 2048 * LParam M * (NOf M r) ^ r`, `ProgStepBSpec.stepBSpace` fits inside
`OneShotProgStepContracts.oneShotStepBSpace` with the same constant `S_B`. -/
theorem stepBSpace_le_oneShotStepBSpace {S_B M r q n Sprev : ℕ}
    (hn : n ≤ 2048 * LParam M * (NOf M r) ^ r) :
    stepBSpace S_B n (NOf M r) (LParam M) q Sprev ≤
      oneShotStepBSpace S_B M r q Sprev := by
  unfold stepBSpace oneShotStepBSpace coreSpaceBase
  set B := 2048 * LParam M * (NOf M r) ^ r + 3
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hL1 : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have hB2 : 2 ≤ B := by omega
  have h1 : (n + 3) ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 : 2 * B ^ 4 ≤ B ^ 5 := by
    calc 2 * B ^ 4 ≤ B * B ^ 4 := Nat.mul_le_mul_right _ hB2
      _ = B ^ 5 := by ring
  have h3 : LParam M ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have hNp : 1 ≤ (NOf M r) ^ (q + 1) := Nat.one_le_pow _ _ hN1
    have hL7 : 1 ≤ (LParam M) ^ 7 := Nat.one_le_pow _ _ hL1
    have hL8 : (LParam M) ^ 8 = LParam M * (LParam M) ^ 7 := by ring
    rw [hL8]
    calc LParam M = 1 * (LParam M * 1) := by ring
      _ ≤ (NOf M r) ^ (q + 1) * (LParam M * (LParam M) ^ 7) :=
          Nat.mul_le_mul hNp (Nat.mul_le_mul_left _ hL7)
  have hB4_ge1 : 1 ≤ B ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h4 : (n + 3) ^ 4 * LParam M + (NOf M r) ^ (q + 1) * (LParam M) ^ 8 ≤
      B ^ 5 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have ha : (n + 3) ^ 4 * LParam M ≤ B ^ 4 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) :=
      Nat.mul_le_mul h1 h3
    have hb : (NOf M r) ^ (q + 1) * (LParam M) ^ 8 ≤
        B ^ 4 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) :=
      Nat.le_mul_of_pos_left _ hB4_ge1
    calc (n + 3) ^ 4 * LParam M + (NOf M r) ^ (q + 1) * (LParam M) ^ 8
        ≤ 2 * B ^ 4 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) := by
          have : 2 * B ^ 4 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) =
              B ^ 4 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) +
              B ^ 4 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) := by ring
          omega
      _ ≤ B ^ 5 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) := Nat.mul_le_mul_right _ h2
      _ = B ^ 5 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
  have h5 := Nat.mul_le_mul_left S_B h4
  have hr : S_B * (B ^ 5 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8) =
      S_B * B ^ 5 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
  omega

/-- Any Step B procedure meeting `ProgStepBSpec.stepBContract` immediately meets
`OneShotProgStepContracts.oneShotStepBContract` with the same constants `(K_B, S_B)`. -/
theorem oneShotStepBContract_of_stepBContract {w f : ℕ} {p : Program}
    {cfg : ParamConfig} {M r q K_B S_B Tprev Sprev : ℕ}
    (hB : MeetsContract w p f (stepBContract cfg M r q w K_B S_B Tprev Sprev)) :
    MeetsContract w p f (oneShotStepBContract cfg M r q w K_B S_B Tprev Sprev) := by
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h, G, X,
    rfl, ha, hrl, hq2, hqr, hP, hG, hGvalid, hGn, hX, hXrange, hGloop, hdegG, hmG,
    hklo, hkhi, hb_eq, hnb_eq, hz_eq, hloc0,
    hg_h, hx_h, hp_h, hloc_h, hf_h, hout_h,
    hd_lg, hd_lx, hd_lp, hd_lf, hd_lo, hd_og, hd_ox, hd_op, hd_of, hd_fg, hd_fx, hd_fp,
    hZero, hw⟩
  have hsp : stepBSpace S_B G.n (NOf M r) (LParam M) q Sprev ≤
      oneShotStepBSpace S_B M r q Sprev := stepBSpace_le_oneShotStepBSpace hGn
  have hpre' : (stepBContract cfg M r q w K_B S_B Tprev Sprev).pre
      [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h] mem :=
    ⟨gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h, G, X,
      rfl, ha, hrl, hq2, hqr, hP, hG, hGvalid, hX, hXrange, hGloop, hdegG, hmG,
      hklo, hkhi, hb_eq, hnb_eq, hz_eq, hloc0,
      hg_h, hx_h, hp_h, hloc_h, hf_h, hout_h,
      hd_lg, hd_lx, hd_lp, hd_lf, hd_lo, hd_og, hd_ox, hd_op, hd_of, hd_fg, hd_fx, hd_fp,
      hZero, by omega⟩
  obtain ⟨body, hbody, o, st', c, hrun, hpost, hcost⟩ := hB _ mem pos ω hwords hpre'
  refine ⟨body, hbody, o, st', c, hrun, ?_, hcost⟩
  intro gAddr' k' xAddr' b' nBlocks' z' pAddr' locAddr' fAddr' outAddr' h' G' X' hargs'
    ha' hrl' hq2' hqr' hP' hG' hGvalid' hGn' hX' hXrange' hGloop' hdegG' hmG'
    hklo' hkhi' hb_eq' hnb_eq' hz_eq' hloc0'
    hg_h' hx_h' hp_h' hloc_h' hf_h' hout_h'
    hd_lg' hd_lx' hd_lp' hd_lf' hd_lo' hd_og' hd_ox' hd_op' hd_of' hd_fg' hd_fx' hd_fp'
    hZero' hw'
  have hsp' : stepBSpace S_B G'.n (NOf M r) (LParam M) q Sprev ≤
      oneShotStepBSpace S_B M r q Sprev := stepBSpace_le_oneShotStepBSpace hGn'
  obtain ⟨hout, hv1, hv2, hZ, hloc, hfr⟩ :=
    hpost gAddr' k' xAddr' b' nBlocks' z' pAddr' locAddr' fAddr' outAddr' h' G' X' hargs'
      ha' hrl' hq2' hqr' hP' hG' hGvalid' hX' hXrange' hGloop' hdegG' hmG'
      hklo' hkhi' hb_eq' hnb_eq' hz_eq' hloc0'
      hg_h' hx_h' hp_h' hloc_h' hf_h' hout_h'
      hd_lg' hd_lx' hd_lp' hd_lf' hd_lo' hd_og' hd_ox' hd_op' hd_of' hd_fg' hd_fx' hd_fp'
      hZero' (by omega)
  exact ⟨hout, hv1, le_trans hv2 (by omega), hZ, hloc, hfr⟩

/-- Full `coreModuleProcs` verification for `coreOnProc` with Step C (`stepCProc`,
`stepCLeftoverProc`) concretely installed inside `coreModuleProcs`: takes only the multi-pair
router contract (`multiPairRouterContract`) and Step B (`ProgStepBSpec.stepBContract`) as
hypotheses. -/
theorem coreModule_coreOn_meetsContract_B {w : ℕ} {p : Program}
    {base stepBIdx routeIdx : ℕ}
    {cfg : ParamConfig} {M r K_B C_rt S_B C_sp : ℕ}
    (hp : p.HasAt base (coreModuleProcs base stepBIdx routeIdx))
    (hRoute : MeetsContract w p routeIdx (multiPairRouterContract C_rt C_sp w))
    (hStepB_rec : ∀ q, 2 ≤ q → q ≤ r →
      MeetsContract w p (coreModuleIdx base stepBIdx routeIdx).coreOn
        ((coreOnContract cfg M r w K_B (stepCTimeConst (C_rt + 2000) (C_rt + 1000))
            S_B (stepCSpaceConst C_sp)).below (fun args _ => args.getD 0 0) q) →
      MeetsContract w p stepBIdx
        (stepBContract cfg M r q w K_B S_B
          (coreProgTime K_B (stepCTimeConst (C_rt + 2000) (C_rt + 1000)) cfg M r (q - 1))
          (coreProgSpace S_B (stepCSpaceConst C_sp) cfg M r (q - 1)))) :
    MeetsContract w p (coreModuleIdx base stepBIdx routeIdx).coreOn
      (coreOnContract cfg M r w K_B (stepCTimeConst (C_rt + 2000) (C_rt + 1000))
        S_B (stepCSpaceConst C_sp)) := by
  set idx := coreModuleIdx base stepBIdx routeIdx
  set head : List Stmt :=
    [ copyWordsProc, initRangeProc, filterDiffProc, filterInterProc,
      filterEdgesInProc, completeFakeProc, edgeColor17Proc,
      stepDProc idx, stepCProc routeIdx, stepCLeftoverProc routeIdx,
      oneShotProc idx, coreOnProc idx, coreEntryProc idx ]
  have hp' : p.HasAt base
      (head ++ cloudExpanderProcs idx.cloudExpander ++ removeFakeProcs idx.removeFake) := hp
  have hAt : ∀ j (hj : j < 13), p.procs[base + j]? = some (head[j]'hj) := by
    intro j hj
    have hlt : j < (head ++ cloudExpanderProcs idx.cloudExpander ++
        removeFakeProcs idx.removeFake).length := by
      simp [head]; omega
    have hget := hp'.get hlt
    rw [List.getElem_append_left (by simp [head]; omega),
      List.getElem_append_left (by simp [head]; omega)] at hget
    exact hget
  have hCopy : MeetsContract w p idx.copyWords (copyWordsContract w) :=
    copyWordsProc_meetsContract (by simpa [idx, coreModuleIdx, head] using hAt 0 (by decide))
  have hDiff : MeetsContract w p idx.filterDiff (filterSetContract w false) :=
    filterSetProc_meetsContract false
      (by simpa [idx, coreModuleIdx, head, filterDiffProc] using hAt 2 (by decide))
  have hFE : MeetsContract w p idx.filterEdgesIn (filterEdgesInContract w) :=
    filterEdgesInProc_meetsContract (by simpa [idx, coreModuleIdx, head] using hAt 4 (by decide))
  have hCol : MeetsContract w p idx.edgeColor17 (edgeColor17Contract w) := by
    refine edgeColor17Proc_spec fun i hi => ?_
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa [idx, coreModuleIdx, head] using hAt 6 (by decide)
  have hCloud : MeetsContract w p idx.cloudExpander (cloudExpanderContract w) := by
    refine cloudExpander_spec fun i hi => ?_
    have hlt : 13 + i < (head ++ cloudExpanderProcs idx.cloudExpander ++
        removeFakeProcs idx.removeFake).length := by
      simp [head]; omega
    have hget := hp'.get hlt
    rw [List.getElem_append_left (by simp [head]; omega),
      List.getElem_append_right (by simp [head])] at hget
    simpa [idx, coreModuleIdx, head, Nat.add_assoc] using hget
  have hRF : MeetsContract w p idx.removeFake (removeFakeContract w) := by
    refine removeFake_spec_prog fun i hi => ?_
    have hlenC : (cloudExpanderProcs idx.cloudExpander).length = (cloudExpanderProcs 0).length :=
      cloudExpanderProcs_length_eq _
    have hlt : 13 + (cloudExpanderProcs 0).length + i <
        (head ++ cloudExpanderProcs idx.cloudExpander ++
          removeFakeProcs idx.removeFake).length := by
      simp [head, hlenC]; omega
    have hget := hp'.get hlt
    rw [List.getElem_append_right (by simp [head, hlenC]; omega)] at hget
    have hsub : 13 + (cloudExpanderProcs 0).length + i -
        (head ++ cloudExpanderProcs idx.cloudExpander).length = i := by
      simp [head, hlenC]; omega
    simp only [hsub] at hget
    simpa [idx, coreModuleIdx, Nat.add_assoc] using hget
  have hStepD : MeetsContract w p idx.stepD (stepDContract w) :=
    stepDProc_meetsContract w p idx
      (by simpa [idx, coreModuleIdx, head] using hAt 7 (by decide)) hFE hRF
  have hStepC : MeetsContract w p idx.stepCMacro
      (stepCContract (coreParamsOf cfg M r) cloud (C_rt + 2000) C_sp w) :=
    stepCProc_spec (by simpa [idx, coreModuleIdx, head] using hAt 8 (by decide)) hRoute
  have hLeft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) (C_rt + 1000) C_sp w) :=
    stepCLeftoverProc_spec (by simpa [idx, coreModuleIdx, head] using hAt 9 (by decide))
      (multiPairRouterContract_implies_routeOrCutContract hRoute)
  exact coreOnProc_meetsContract
    (by simpa [idx, coreModuleIdx, head] using hAt 11 (by decide))
    (by simpa [idx, coreModuleIdx, head] using hAt 10 (by decide))
    hCopy hDiff hCloud hCol hStepC hLeft hStepD
    (fun q hq2 hqr ih => oneShotStepBContract_of_stepBContract (hStepB_rec q hq2 hqr ih))

/-- Full `coreModuleProcs` verification for the whole-graph core-theorem entry point
`coreEntryProc` with Step C (`stepCProc`, `stepCLeftoverProc`) concretely installed inside
`coreModuleProcs`: given `p.HasAt base (coreModuleProcs base stepBIdx routeIdx)`, the multi-pair
router contract at `routeIdx`, and the Step B contract at `stepBIdx`, the entry procedure at
`base + 12` meets `coreEntryContract`. -/
theorem coreModule_meetsContract_B {w : ℕ} {p : Program}
    {base stepBIdx routeIdx : ℕ}
    {cfg : ParamConfig} {M r K_B C_rt S_B C_sp : ℕ}
    (hp : p.HasAt base (coreModuleProcs base stepBIdx routeIdx))
    (hRoute : MeetsContract w p routeIdx (multiPairRouterContract C_rt C_sp w))
    (hStepB_rec : ∀ q, 2 ≤ q → q ≤ r →
      MeetsContract w p (coreModuleIdx base stepBIdx routeIdx).coreOn
        ((coreOnContract cfg M r w K_B (stepCTimeConst (C_rt + 2000) (C_rt + 1000))
            S_B (stepCSpaceConst C_sp)).below (fun args _ => args.getD 0 0) q) →
      MeetsContract w p stepBIdx
        (stepBContract cfg M r q w K_B S_B
          (coreProgTime K_B (stepCTimeConst (C_rt + 2000) (C_rt + 1000)) cfg M r (q - 1))
          (coreProgSpace S_B (stepCSpaceConst C_sp) cfg M r (q - 1)))) :
    MeetsContract w p (coreModuleIdx base stepBIdx routeIdx).core
      (coreEntryContract cfg M r w K_B (C_rt + 2000) (C_rt + 1000) S_B C_sp) := by
  have hCoreOn := coreModule_coreOn_meetsContract_B hp hRoute hStepB_rec
  set idx := coreModuleIdx base stepBIdx routeIdx
  set head : List Stmt :=
    [ copyWordsProc, initRangeProc, filterDiffProc, filterInterProc,
      filterEdgesInProc, completeFakeProc, edgeColor17Proc,
      stepDProc idx, stepCProc routeIdx, stepCLeftoverProc routeIdx,
      oneShotProc idx, coreOnProc idx, coreEntryProc idx ]
  have hp' : p.HasAt base
      (head ++ cloudExpanderProcs idx.cloudExpander ++ removeFakeProcs idx.removeFake) := hp
  have hAt : ∀ j (hj : j < 13), p.procs[base + j]? = some (head[j]'hj) := by
    intro j hj
    have hlt : j < (head ++ cloudExpanderProcs idx.cloudExpander ++
        removeFakeProcs idx.removeFake).length := by
      simp [head]; omega
    have hget := hp'.get hlt
    rw [List.getElem_append_left (by simp [head]; omega),
      List.getElem_append_left (by simp [head]; omega)] at hget
    exact hget
  have hInit : MeetsContract w p idx.initRange (initRangeContract w) :=
    initRangeProc_meetsContract (by simpa [idx, coreModuleIdx, head] using hAt 1 (by decide))
  exact coreEntryProc_meetsContract
    (by simpa [idx, coreModuleIdx, head] using hAt 12 (by decide)) hInit hCoreOn

/-! ## 5. Non-Vacuity Witness (`coreEntryContract_pre_example`) -/

/-- Non-vacuity witness for `coreEntryContract`: at `cfg = ParamConfig.default`, `M = 0`, `r = 1`,
`q = 1`, on the valid loopless empty 2-vertex graph `G = ⟨2, []⟩`, the precondition of
`coreEntryContract` is satisfiable for a concrete memory layout and word size `w`. -/
theorem coreEntryContract_pre_example :
    ∃ w mem gAddr pAddr outAddr h,
      (coreEntryContract ParamConfig.default 0 1 w 1 1 1 1 1).pre
        [1, gAddr, pAddr, outAddr, h] mem := by
  let cp := coreParamsOf ParamConfig.default 0 1
  let G : Graph := ⟨2, []⟩
  let gAddr : ℕ := 0
  let pAddr : ℕ := 4
  let outAddr : ℕ := 20
  let h : ℕ := 30
  let B : ℕ := h + coreEntrySpace 1 (stepCSpaceConst 1) ParamConfig.default 0 1 1
  let w : ℕ := Nat.log 2 B + 1
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 2
    else if a = 1 then 0
    else if a = 4 then cp.N
    else if a = 5 then cp.L
    else if a = 6 then cp.Δ
    else if a = 7 then 1
    else if a = 8 then cp.P 0
    else if a = 9 then cp.P 1
    else if a = 10 then cp.D 0
    else if a = 11 then cp.D 1
    else if a = 12 then cp.N ^ 0
    else if a = 13 then cp.N ^ 1
    else 0
  refine ⟨w, mem, gAddr, pAddr, outAddr, h, 1, gAddr, pAddr, outAddr, h, G,
    rfl, by decide, by decide, by decide, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, Or.inr (by decide), Or.inr (by decide), ?_, ?_⟩
  · refine ⟨by simp [mem, pAddr, cp], by simp [mem, pAddr, cp], by simp [mem, pAddr, cp],
      by simp [mem, pAddr], ?_, ?_, ?_⟩
    · intro j hj; interval_cases j <;> simp [mem, pAddr, cp]
    · intro j hj; interval_cases j <;> simp [mem, pAddr, cp]
    · intro j hj; interval_cases j <;> simp [mem, pAddr, cp]
  · intro i hi
    simp only [G, Graph.encode, List.flatMap_nil, List.length_cons, List.length_nil] at hi
    interval_cases i <;> simp [mem, G, gAddr, Graph.encode, Graph.m]
  · intro e he; simp [G] at he
  · intro e he; simp [G] at he
  · change 2 ≤ (NOf 0 1) ^ 1
    have h4 := four_le_NOf 0 1
    simpa using le_trans (by decide : 2 ≤ 4) h4
  · intro v _; simp [G, Graph.deg, Graph.degIn, Graph.inside]
  · intro a ha
    have : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 4 ∧ a ≠ 5 ∧ a ≠ 6 ∧ a ≠ 7 ∧ a ≠ 8 ∧ a ≠ 9 ∧
      a ≠ 10 ∧ a ≠ 11 ∧ a ≠ 12 ∧ a ≠ 13 := by omega
    simp [mem, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1,
      this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1,
      this.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2]
  · exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) B

end MinCostFlow.ExpanderDecomp
