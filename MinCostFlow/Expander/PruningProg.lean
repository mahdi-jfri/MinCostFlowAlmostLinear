module

public import WordRAM.Logic
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.ExpanderPruning
public import MinCostFlow.Expander.PruningInitProg
public import MinCostFlow.Expander.PruningStepsProg

import Mathlib.Tactic.Linarith

/-!
# Top-Level Word-RAM Expander Pruning (`PruningProg`)

Compiles and verifies the full deterministic expander-pruning loop (`pruneExpanderStmt`),
combining `initPruneStmt` (`PruningInitProg`) and `pruneStepStmt` (`PruningStepsProg`):
- `pruneLoopStmt` / `pruneLoop_triple`: repeats `pruneStepStmt` while `0 < peelTop + actTop`
  using `Triple.loop_inv` with potential measure `pot cfg s`, proving termination with empty
  queues (`sFin.peelQ = []`, `sFin.active = []`) in `≤ 360 * pot cfg s₀ + 10` cycles.
- `pruneExpanderStmt` / `pruneExpander_triple`: chains `initPruneStmt` and `pruneLoopStmt`,
  bounding total runtime by `pruneTimeBound cfg.G.n cfg.G.m cfg.H` (`O(n + m H²)`).
- `pruneExpander_wordram_spec`: extracts the pruned set `R` from `outRAddr[0 .. n - 1]`,
  proving `R ⊆ cfg.X \ cfg.B`, `(φ₀ / 3)`-conductance (`conductance_of_pruned`), minimum
  internal degree `≥ cfg.θ_out_nat`, and the volume/cut bounds needed by `Decompose`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Statements and `NoRand` -/

/-- Main pruning loop: executes `pruneStepStmt` while `prPeelTop + prActTop > 0`. -/
def pruneLoopStmt : Stmt :=
  .loop (.bin .lt (.const 0) (.bin .add (.reg prPeelTop) (.reg prActTop))) pruneStepStmt

lemma pruneLoopStmt_noRand : pruneLoopStmt.NoRand := by
  simp [pruneLoopStmt, Stmt.NoRand, pruneStepStmt_noRand]

/-- Full deterministic expander pruning program (`initPruneStmt ;; pruneLoopStmt`). -/
def pruneExpanderStmt : Stmt :=
  initPruneStmt ;; pruneLoopStmt

lemma pruneExpanderStmt_noRand : pruneExpanderStmt.NoRand :=
  ⟨initPruneStmt_noRand, pruneLoopStmt_noRand⟩

/-- Explicit worst-case Word-RAM cycle bound `O(n + m · H²)` for `pruneExpanderStmt`. -/
def pruneTimeBound (n m H : ℕ) : ℕ :=
  170 * n + 140 * m + 30 * (H + 1) +
    360 * ((4 * H + 14) * (4 * H + 4) * (2 * m + 1)) + 221

/-! ## 2. Frame & Combinatorial Helpers -/

private lemma peelQ_length_le_n {cfg : PruneCfg} {s : PruneState}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hpq : PeelQInv cfg s) :
    s.peelQ.length ≤ cfg.G.n := by
  have hsub : ∀ x ∈ s.peelQ, x ∈ Finset.range cfg.G.n := fun x hx => by
    rw [← hcfgX]; exact hpq.2.1 x hx
  calc
    s.peelQ.length = s.peelQ.toFinset.card := (List.toFinset_card_of_nodup hpq.1).symm
    _ ≤ (Finset.range cfg.G.n).card :=
      Finset.card_le_card (fun x hx => hsub x (List.mem_toFinset.mp hx))
    _ = cfg.G.n := Finset.card_range cfg.G.n

private lemma cfg_edges_length_eq_m {cfg : PruneCfg}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hGv : cfg.G.IsValid) :
    cfg.edges.length = cfg.G.m := by
  unfold PruneCfg.edges
  rw [hcfgX]
  change (cfg.G.inside cfg.G.verts).length = cfg.G.m
  rw [inside_verts_of_isValid hGv]
  rfl

private lemma cutPR_eq_cutIn_of_sub (cfg : PruneCfg) (s : PruneState) :
    cutPR cfg s = cfg.G.cutIn cfg.X (s.Rset cfg) := by
  unfold cutPR Cited.Graph.cutIn PruneCfg.edges
  congr 1
  apply List.filter_congr
  intro e he
  have he' := List.mem_filter.mp he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he'
  have h1 : e.1 ∈ s.Rset cfg ↔ s.inR e.1 = true := by
    simp [PruneState.Rset, he'.2.1]
  have h2 : e.2 ∈ s.Rset cfg ↔ s.inR e.2 = true := by
    simp [PruneState.Rset, he'.2.2]
  by_cases b1 : s.inR e.1 = true <;> by_cases b2 : s.inR e.2 = true <;>
    simp [h1, h2, b1, b2]

private lemma volPminusB_eq {cfg : PruneCfg} {s : PruneState} :
    volPminusB cfg s = cfg.G.volIn cfg.X ((cfg.X \ cfg.B) \ s.Rset cfg) := by
  unfold volPminusB Cited.Graph.volIn
  have hfilt :
      (cfg.X \ cfg.B) \ s.Rset cfg = cfg.X.filter fun u => !s.inR u && decide (u ∉ cfg.B) := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, PruneState.Rset, Bool.eq_false_iff]
    tauto
  rw [hfilt, Finset.sum_filter]
  rfl

/-! ## 3. Loop & Full Program Verification -/

/-- Correctness and runtime bound for the pruning loop `pruneLoopStmt`. -/
theorem pruneLoop_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s₀ : PruneState} {buckets₀ : ℕ → List ℕ} (st₁ : State)
    (hinv₀ : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s₀ buckets₀ st₁)
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w) :
    Triple w p (fun st => st = st₁) pruneLoopStmt
      (normalPost fun st' =>
        ∃ sFin bucketsFin,
          (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₁.regs r) ∧
          st'.pos = st₁.pos ∧
          PreservedOutside2 st₁.mem st'.mem outRAddr (outRAddr + cfg.G.n)
            workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
          PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr sFin bucketsFin st' ∧
          sFin.peelQ = [] ∧
          sFin.active = [] ∧
          sFin.steps + pot cfg sFin ≤ s₀.steps + pot cfg s₀ ∧
          volPminusB cfg sFin + 2 * cfg.C_cap * cutPR cfg sFin ≤
            volPminusB cfg s₀ + 2 * cfg.C_cap * cutPR cfg s₀)
      (fun _ => 360 * pot cfg s₀ + 10) := by
  let loopCond := Expr.bin .lt (.const 0) (.bin .add (.reg prPeelTop) (.reg prActTop))
  let Inv : PruneState → State → Prop := fun s st =>
    ∃ buckets,
      (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st.regs r = st₁.regs r) ∧
      st.pos = st₁.pos ∧
      PreservedOutside2 st₁.mem st.mem outRAddr (outRAddr + cfg.G.n)
        workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
      PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st ∧
      s.steps + pot cfg s ≤ s₀.steps + pot cfg s₀ ∧
      volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s ≤
        volPminusB cfg s₀ + 2 * cfg.C_cap * cutPR cfg s₀
  have hwb := pruneWordBound_pos hw
  have hinit : ∀ st, st = st₁ → Inv s₀ st := fun st hst => by
    subst hst
    exact ⟨buckets₀, fun _ _ _ _ => rfl, rfl, fun _ _ _ => rfl, hinv₀, le_rfl, le_rfl⟩
  refine (Triple.loop_inv (Inv := Inv)
    (condVal := fun st => if 0 < st.regs prPeelTop + st.regs prActTop then 1 else 0)
    (fun s => pot cfg s)
    (fun s => 360 * pot cfg s + 10)
    ?_ ?_ ?_ s₀).weaken_pre hinit
  · intro s st ⟨buckets, _, _, _, hinv, _, _⟩
    have hpeel_le := peelQ_length_le_n hinv.cfg_X hinv.peelQ_inv
    have hact_le := hinv.active_len_le
    have hsum_lt : s.peelQ.length + s.active.length < 2 ^ w := by
      unfold PruneWordBound pruneWorkSpace at hw
      omega
    have hr1 : Expr.eval w st (.reg prPeelTop) = some s.peelQ.length := by
      simp [Expr.eval, hinv.reg_peelTop]
    have hr2 : Expr.eval w st (.reg prActTop) = some s.active.length := by
      simp [Expr.eval, hinv.reg_actTop]
    rw [hinv.reg_peelTop, hinv.reg_actTop]
    exact Expr.eval_bin (op := .lt) (Expr.eval_const (by omega))
      (Expr.eval_bin (op := .add) hr1 hr2 (by dsimp only [BinOp.eval]; exact hsum_lt))
      (by dsimp only [BinOp.eval]; split_ifs <;> omega)
  · intro s st ⟨buckets, hreg, hpos, hpr, hinv, hst_le, hvc_le⟩ h0
    have hsum0 : st.regs prPeelTop + st.regs prActTop = 0 := by
      by_contra hne
      have hpos_sum : 0 < st.regs prPeelTop + st.regs prActTop := Nat.pos_of_ne_zero hne
      simp [hpos_sum] at h0
    rw [hinv.reg_peelTop, hinv.reg_actTop] at hsum0
    have hpq0 : s.peelQ = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hact0 : s.active = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨⟨s, buckets, hreg, hpos, hpr, hinv, hpq0, hact0, hst_le, hvc_le⟩, ?_⟩
    simp [Expr.size]
  · intro s st ⟨buckets, hreg, hpos, hpr, hinv, hst_le, hvc_le⟩ hne
    have hsum_pos : 0 < st.regs prPeelTop + st.regs prActTop := by
      by_contra h0
      have h0' : ¬ 0 < st.regs prPeelTop + st.regs prActTop := h0
      simp [h0'] at hne
    rw [hinv.reg_peelTop, hinv.reg_actTop] at hsum_pos
    have hq_ne : s.peelQ ≠ [] ∨ s.active ≠ [] := by
      by_cases hp : s.peelQ = []
      · right; intro ha; rw [hp, ha] at hsum_pos; simp at hsum_pos
      · exact Or.inl hp
    obtain ⟨T_step, hstep⟩ :=
      pruneStep_triple (p := p) st hinv hq_ne hθ hw hdisj hcsr_w houtR_w
    refine ⟨T_step, ?_⟩
    intro st_in ω hsi
    subst st_in
    rcases hstep st ω rfl with ⟨o', st', c', hr', hq', hc'⟩
    cases o' with
    | returned => exact False.elim hq'
    | normal =>
      rcases hq' with ⟨s', buckets', hreg', hpos', hpr', hinv', hs'_st, hs'_lt, hs'_vc, hT⟩
      have hpr'_ws : PreservedOutside2 st.mem st'.mem outRAddr (outRAddr + cfg.G.n)
          workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) := fun q hq1 hq2 =>
        hpr' q hq1 (by
          rcases hq2 with h | h
          · exact Or.inl (by dsimp [wHArr]; omega)
          · exact Or.inr h)
      refine ⟨.normal, st', c', hr',
        ⟨s', ⟨buckets', fun r hr h1 h2 => (hreg' r hr h1 h2).trans (hreg r hr h1 h2),
          hpos'.trans hpos, preservedOutside2_trans hpr hpr'_ws, hinv',
          hs'_st.trans hst_le, hs'_vc.trans hvc_le⟩, hs'_lt, ?_⟩, hc'⟩
      dsimp only [loopCond, Expr.size]
      omega

/-- End-to-end Word-RAM simulation and runtime bound for `pruneExpanderStmt`. -/
theorem pruneExpander_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} (st₀ : State)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hinB_w : inBAddr + cfg.G.n < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hG : GraphAt st₀.mem gAddr cfg.G)
    (hCsr : HasCsrAt st₀.mem csrAddr cfg.G)
    (hinB : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ st₀.mem (inBAddr + b) ≠ 0) :
    Triple w p
      (fun st => st = st₀ ∧ InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      pruneExpanderStmt
      (normalPost fun st' =>
        ∃ sFin bucketsFin,
          st'.pos = st₀.pos ∧
          PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
            workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
          PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr sFin bucketsFin st' ∧
          sFin.peelQ = [] ∧
          sFin.active = [] ∧
          sFin.steps ≤ (4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * cfg.G.m + 1) ∧
          volPminusB cfg sFin + 2 * cfg.C_cap * cutPR cfg sFin ≤
            2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B)
      (fun _ => pruneTimeBound cfg.G.n cfg.G.m cfg.H) := by
  intro st ω hpre
  set sInit := initStateList cfg (List.range cfg.G.n).reverse
  have hXList : (List.range cfg.G.n).reverse.Nodup ∧
      ∀ x, x ∈ (List.range cfg.G.n).reverse ↔ x ∈ cfg.X :=
    ⟨List.nodup_reverse.mpr List.nodup_range, fun x => by simp [hcfgX]⟩
  have hpot_init : pot cfg sInit ≤
      (4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * cfg.G.m + 1) := by
    have h1 := pot_initStateList_le hval hXList
    rwa [cfg_edges_length_eq_m hcfgX hval.1] at h1
  have hsteps_init : sInit.steps = 0 := rfl
  have hR_init : sInit.Rset cfg = cfg.X \ cfg.B := by
    ext u
    simp [PruneState.Rset, sInit, initStateList, Finset.mem_sdiff]
  have hvolP_init : volPminusB cfg sInit = 0 := by
    unfold volPminusB
    apply Finset.sum_eq_zero
    intro u hu
    by_cases huB : u ∈ cfg.B <;> simp [sInit, initStateList, hu, huB]
  have hcut_init : cutPR cfg sInit = cfg.G.cutIn cfg.X cfg.B := by
    rw [cutPR_eq_cutIn_of_sub cfg sInit, hR_init]
    exact cutIn_sdiff cfg.G cfg.X cfg.B hval.2.1
  dsimp only [pruneExpanderStmt]
  rcases initPrune_triple (p := p) st₀ hcfgX hval hw hdisj hg_w hcsr_w hinB_w houtR_w hG hCsr hinB
      st ω hpre with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
  cases o₁ with
  | returned => exact False.elim hq₁
  | normal =>
    rcases hq₁ with ⟨hp₁, hpr₁, hinv₁⟩
    rcases pruneLoop_triple (p := p) st₁ hinv₁ hθ hw hdisj hcsr_w houtR_w st₁ ω rfl with
      ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
    cases o₂ with
    | returned => exact False.elim hq₂
    | normal =>
      rcases hq₂ with ⟨sFin, bucketsFin, _, hp₂, hpr₂, hinv₂, hpq₂, hact₂, hsFin_st, hsFin_vc⟩
      have hvc₂ : volPminusB cfg sFin + 2 * cfg.C_cap * cutPR cfg sFin ≤
          2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B := by
        rw [hvolP_init, hcut_init, zero_add] at hsFin_vc
        exact hsFin_vc
      dsimp only at hc₁ hc₂
      dsimp only [sInit] at hsFin_st hpot_init hsteps_init hc₂
      have h360 : 360 * pot cfg (initStateList cfg (List.range cfg.G.n).reverse) ≤
          360 * ((4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * cfg.G.m + 1)) :=
        Nat.mul_le_mul_left 360 hpot_init
      refine ⟨.normal, st₂, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩),
        ⟨sFin, bucketsFin, hp₂.trans hp₁, preservedOutside2_trans hpr₁ hpr₂, hinv₂, hpq₂, hact₂,
          by omega, hvc₂⟩, ?_⟩
      dsimp only [pruneTimeBound]
      omega

/-- `pruneExpander_wordram_spec`, together with the fact that the cells of `outRAddr` hold `1` on
`R` and `0` elsewhere. -/
theorem pruneExpander_wordram_spec_bits {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} {φ₀ : ℝ}
    (st₀ : State) (ω : ℕ → Bool)
    (hreg0 : InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st₀)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hexp : cfg.G.IsConductanceExpanderOn cfg.X φ₀) (hφ₀ : 0 < φ₀)
    (hC5 : 5 ≤ cfg.C_cap) (hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1))
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hinB_w : inBAddr + cfg.G.n < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hG : GraphAt st₀.mem gAddr cfg.G)
    (hCsr : HasCsrAt st₀.mem csrAddr cfg.G)
    (hinB : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ st₀.mem (inBAddr + b) ≠ 0) :
    ∃ st' c,
      Runs w p ω pruneExpanderStmt st₀ .normal st' c ∧
      st'.pos = st₀.pos ∧
      PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
        workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
      c ≤ pruneTimeBound cfg.G.n cfg.G.m cfg.H ∧
      let R : Finset ℕ := (Finset.range cfg.G.n).filter fun x => decide (st'.mem (outRAddr + x) ≠ 0)
      R ⊆ cfg.X \ cfg.B ∧
      cfg.G.IsConductanceExpanderOn R (φ₀ / 3) ∧
      (∀ v ∈ R, cfg.θ_out_nat ≤ cfg.G.degIn R v) ∧
      cfg.G.volIn cfg.X ((cfg.X \ cfg.B) \ R) + 2 * cfg.C_cap * cfg.G.cutIn cfg.X R ≤
        2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B ∧
      cfg.G.volIn cfg.X (cfg.X \ R) ≤
        cfg.G.volIn cfg.X cfg.B + 2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B ∧
      (∀ u < cfg.G.n, st'.mem (outRAddr + u) = if u ∈ R then 1 else 0) := by
  rcases pruneExpander_triple st₀ hcfgX hval hθ hw hdisj hg_w hcsr_w hinB_w houtR_w hG hCsr hinB
      st₀ ω ⟨rfl, hreg0⟩ with ⟨o, st', c, hrun, hpost, hc⟩
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨sFin, bucketsFin, hpos, hpres, hinv, hpq0, hact0, _, hvc⟩
    let R : Finset ℕ := (Finset.range cfg.G.n).filter fun x => decide (st'.mem (outRAddr + x) ≠ 0)
    have hR_eq : R = sFin.Rset cfg := by
      ext u
      simp only [R, PruneState.Rset, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨huN, hmem⟩
        rw [hinv.outR_eq u huN] at hmem
        have huR : sFin.inR u = true := by by_contra hf; simp [hf] at hmem
        exact ⟨hcfgX ▸ Finset.mem_range.mpr huN, huR⟩
      · rintro ⟨huX, huR⟩
        have huN : u < cfg.G.n := Finset.mem_range.mp (hcfgX ▸ huX)
        refine ⟨huN, ?_⟩
        rw [hinv.outR_eq u huN]
        simp [huR]
    have hRsub : R ⊆ cfg.X \ cfg.B := by
      rw [hR_eq]
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      refine Finset.mem_sdiff.mpr ⟨hu'.1, fun huB => ?_⟩
      have hfalse := hinv.prune_inv.not_inR_B u huB
      simp [hu'.2] at hfalse
    have hexpR : cfg.G.IsConductanceExpanderOn R (φ₀ / 3) := by
      rw [hR_eq]
      exact conductance_of_pruned hexp hφ₀ hC5 hCphi hinv.prune_inv hact0
    have hdegR : ∀ v ∈ R, cfg.θ_out_nat ≤ cfg.G.degIn R v := by
      intro v hv
      rw [hR_eq] at hv ⊢
      have hv' := Finset.mem_filter.mp hv
      have hge : cfg.θ_out_nat ≤ sFin.degR v := by
        by_contra hlt
        push Not at hlt
        have hmem := hinv.prune_inv.degR_peel v hv'.2 hlt
        rw [hpq0] at hmem
        simp at hmem
      rwa [← hinv.prune_inv.degR_eq v hv'.2]
    have hvc' : cfg.G.volIn cfg.X ((cfg.X \ cfg.B) \ R) + 2 * cfg.C_cap * cfg.G.cutIn cfg.X R ≤
        2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B := by
      rw [hR_eq]
      rw [← volPminusB_eq, ← cutPR_eq_cutIn_of_sub cfg sFin]
      exact hvc
    have hvolXR : cfg.G.volIn cfg.X (cfg.X \ R) ≤
        cfg.G.volIn cfg.X cfg.B + 2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B := by
      have hunion : cfg.X \ R = cfg.B ∪ ((cfg.X \ cfg.B) \ R) := by
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨huX, huR⟩
          by_cases huB : u ∈ cfg.B
          · exact Or.inl huB
          · exact Or.inr ⟨⟨huX, huB⟩, huR⟩
        · rintro (huB | ⟨⟨huX, _⟩, huR⟩)
          · exact ⟨hval.2.1 huB, fun huR => (Finset.mem_sdiff.mp (hRsub huR)).2 huB⟩
          · exact ⟨huX, huR⟩
      have hdisj_BR : Disjoint cfg.B ((cfg.X \ cfg.B) \ R) :=
        Finset.disjoint_left.mpr fun _ hxB hx => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 hxB
      rw [hunion, volIn_disjoint_union cfg.G cfg.X cfg.B ((cfg.X \ cfg.B) \ R) hdisj_BR]
      omega
    refine ⟨st', c, hrun, hpos, hpres, hc, hRsub, hexpR, hdegR, hvc', hvolXR, fun u hu => ?_⟩
    rw [hinv.outR_eq u hu]
    by_cases huR : sFin.inR u = true
    · have : u ∈ R := by
        simp only [R, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
        exact ⟨hu, by rw [hinv.outR_eq u hu]; simp [huR]⟩
      rw [if_pos this]; simp [huR]
    · have : u ∉ R := by
        simp only [R, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq, not_and]
        intro _; rw [hinv.outR_eq u hu]; simp [huR]
      rw [if_neg this]; simp [huR]

/-- Top-level Word-RAM specification recovering `(φ₀ / 3)`-conductance, minimum internal degree
`≥ cfg.θ_out_nat`, and the volume/cut bounds on the pruned set `R` stored in `[outRAddr .. outRAddr + n)`. -/
theorem pruneExpander_wordram_spec {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} {φ₀ : ℝ}
    (st₀ : State) (ω : ℕ → Bool)
    (hreg0 : InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st₀)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hexp : cfg.G.IsConductanceExpanderOn cfg.X φ₀) (hφ₀ : 0 < φ₀)
    (hC5 : 5 ≤ cfg.C_cap) (hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1))
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hinB_w : inBAddr + cfg.G.n < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hG : GraphAt st₀.mem gAddr cfg.G)
    (hCsr : HasCsrAt st₀.mem csrAddr cfg.G)
    (hinB : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ st₀.mem (inBAddr + b) ≠ 0) :
    ∃ st' c,
      Runs w p ω pruneExpanderStmt st₀ .normal st' c ∧
      st'.pos = st₀.pos ∧
      PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
        workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
      c ≤ pruneTimeBound cfg.G.n cfg.G.m cfg.H ∧
      let R : Finset ℕ := (Finset.range cfg.G.n).filter fun x => decide (st'.mem (outRAddr + x) ≠ 0)
      R ⊆ cfg.X \ cfg.B ∧
      cfg.G.IsConductanceExpanderOn R (φ₀ / 3) ∧
      (∀ v ∈ R, cfg.θ_out_nat ≤ cfg.G.degIn R v) ∧
      cfg.G.volIn cfg.X ((cfg.X \ cfg.B) \ R) + 2 * cfg.C_cap * cfg.G.cutIn cfg.X R ≤
        2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B ∧
      cfg.G.volIn cfg.X (cfg.X \ R) ≤
        cfg.G.volIn cfg.X cfg.B + 2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B := by
  obtain ⟨st', c, hrun, hpos, hpres, hc, hRsub, hexpR, hdegR, hvc', hvolXR, _⟩ :=
    pruneExpander_wordram_spec_bits (p := p) st₀ ω hreg0 hcfgX hval hexp hφ₀ hC5 hCphi hθ hw hdisj
      hg_w hcsr_w hinB_w houtR_w hG hCsr hinB
  exact ⟨st', c, hrun, hpos, hpres, hc, hRsub, hexpR, hdegR, hvc', hvolXR⟩

end MinCostFlow.Expander
