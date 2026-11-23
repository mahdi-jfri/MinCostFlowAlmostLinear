module

public import MinCostFlow.ExpanderDecomp.RouteProgBFSLoop

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Multi-Source Layered BFS Word-RAM Procedure (`bfsLayers_meetsContract`)

Verifies `bfsLayersProc` against `bfsLayers`, establishing
exactness (`BfsOutAt`), untouched-stamp preservation, frame outside `BfsWriteSet`,
and linear time `≤ 140 * (bfsLayers ...).cost + 180` (`bfsLayers_triple`,
`bfsLayers_meetsContract`).
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Fast Config Load Helper (`bfsLoadCfg_triple`) -/

private lemma loadCfg_step_inv {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {i cfgAddr : ℕ} {f mem0 : ℕ → ℕ} {st : State} {rest : Stmt} {P : Outcome → State → Prop} {c1 : ℕ}
    (hw : cfgAddr + 26 ≤ 2 ^ w) (hi : i ≤ 15)
    (hm : st.mem = mem0) (hregs : ∀ r ≤ i, st.regs r = f r) (hf0 : f 0 = cfgAddr)
    (hmem : mem0 (cfgAddr + i) = f (i + 1))
    (hrest : ∀ st1 : State, st1.mem = mem0 → (∀ r ≤ i + 1, st1.regs r = f r) →
      ∃ o st' c, Runs w p ω rest st1 o st' c ∧ P o st' ∧ c ≤ c1) :
    ∃ o st' c,
      Runs w p ω (.seq (.assign (i + 1) (.load (.bin .add (.reg 0) (.const i)))) rest) st o st' c ∧
      P o st' ∧ c ≤ c1 + 7 := by
  have hr0 : st.regs 0 = cfgAddr := (hregs 0 (Nat.zero_le _)).trans hf0
  have hev : (Expr.load (.bin .add (.reg 0) (.const i))).eval w st = some (f (i + 1)) := by
    simp [Expr.eval, BinOp.eval, hr0, show i < 2 ^ w by omega, show cfgAddr + i < 2 ^ w by omega, hm, hmem]
  have ha : Runs w p ω (.assign (i + 1) (.load (.bin .add (.reg 0) (.const i)))) st .normal
      { st with regs := Function.update st.regs (i + 1) (f (i + 1)) }
      ((Expr.load (.bin .add (.reg 0) (.const i))).size + 1) :=
    runs_assign_iff.mpr ⟨f (i + 1), hev, rfl, rfl, rfl⟩
  have hregs1 : ∀ r ≤ i + 1, (Function.update st.regs (i + 1) (f (i + 1))) r = f r := by
    intro r hr
    by_cases h : r = i + 1
    · subst h; exact Function.update_self _ _ _
    · rw [Function.update_of_ne h]; exact hregs r (by omega)
  obtain ⟨o, st', c, hrun, hp, hle⟩ :=
    hrest { st with regs := Function.update st.regs (i + 1) (f (i + 1)) } hm hregs1
  refine ⟨o, st', _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha, hrun, rfl⟩), hp, ?_⟩
  simp only [Expr.size]; omega

private lemma bfsLoadCfg_triple {w : ℕ} {p : Program}
    {cfg : BfsCfg} {cfgAddr : ℕ} {st0 : State}
    (hcfg : BfsCfgAt st0.mem cfgAddr cfg)
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 26 ≤ 2 ^ w) :
    Triple w p (fun st => st = st0) bfsLoadCfgStmt
      (normalPost fun st1 =>
        st1.mem = st0.mem ∧
        ∀ r ≤ 16, st1.regs r =
          match r with
          | 0 => cfgAddr | 1 => cfg.offAddr | 2 => cfg.nbAddr
          | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
          | 5 => cfg.hasStop | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
          | 8 => cfg.visStampAddr | 9 => cfg.distAddr
          | 10 => cfg.layerOffAddr | 11 => cfg.layerDataAddr | 12 => cfg.tmpNxtAddr
          | 13 => cfg.bfsGen | 14 => cfg.maxDist | 15 => cfg.initPtr | _ => cfg.initLen)
      (fun _ => 115) := by
  let f : ℕ → ℕ := fun r =>
    match r with
    | 0 => cfgAddr | 1 => cfg.offAddr | 2 => cfg.nbAddr
    | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
    | 5 => cfg.hasStop | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
    | 8 => cfg.visStampAddr | 9 => cfg.distAddr
    | 10 => cfg.layerOffAddr | 11 => cfg.layerDataAddr | 12 => cfg.tmpNxtAddr
    | 13 => cfg.bfsGen | 14 => cfg.maxDist | 15 => cfg.initPtr | _ => cfg.initLen
  rcases hcfg with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15⟩
  wram_enter; subst st; dsimp only; simp only [Nat.zero_add]; unfold bfsLoadCfgStmt; dsimp only [seqStmts]
  have hr0' : ∀ r ≤ 0, st0.regs r = f r := fun r hr => by
    have : r = 0 := by omega
    subst this; exact hr0
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) rfl hr0' rfl hc0 (c1 := 108) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc1 (c1 := 101) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc2 (c1 := 94) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc3 (c1 := 87) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc4 (c1 := 80) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc5 (c1 := 73) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc6 (c1 := 66) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc7 (c1 := 59) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc8 (c1 := 52) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc9 (c1 := 45) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc10 (c1 := 38) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc11 (c1 := 31) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc12 (c1 := 24) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc13 (c1 := 17) (fun s hm hr => ?_)
  refine loadCfg_step_inv (f := f) hw_cfg (by decide) hm hr rfl hc14 (c1 := 10) (fun s hm hr => ?_)
  have hs0 : s.regs 0 = cfgAddr := hr 0 (by decide)
  have hev16 : (Expr.load (.bin .add (.reg 0) (.const 15))).eval w s = some (f 16) := by
    simp [Expr.eval, BinOp.eval, hs0, show 15 < 2 ^ w by omega, show cfgAddr + 15 < 2 ^ w by omega,
      hm, hc15, f]
  refine ⟨.normal, { s with regs := Function.update s.regs 16 (f 16) }, _,
    runs_assign_iff.mpr ⟨f 16, hev16, rfl, rfl, rfl⟩, ⟨hm, fun r hr' => ?_⟩, ?_⟩
  · dsimp only
    by_cases h : r = 16
    · subst h; exact Function.update_self _ _ _
    · rw [Function.update_of_ne h]; exact hr r (by omega)
  · simp only [Expr.size]; omega

/-! ## 2. Full Procedure Triple (`bfsLayers_triple`) -/

theorem bfsLayers_triple {w : ℕ} {p : Program}
    {X V S0 stopSet : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {cfg : BfsCfg} {cfgAddr m2 : ℕ} {st0 : State}
    (hVX : V ⊆ X)
    (hS0_V : S0 ⊆ V)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcfg : BfsCfgAt st0.mem cfgAddr cfg)
    (hcsr : NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : BfsDisj w X.card m2 cfg cfgAddr)
    (hmask : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hstop : cfg.hasStop = 0 → stopSet = ∅)
    (hstop_mem : cfg.hasStop ≠ 0 →
      ∀ v < X.card, st0.mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ stopSet)
    (hinit_list : ListAt st0.mem cfg.initPtr ((S0.sort (· ≤ ·)).map (locOf X)))
    (hinit_len : cfg.initLen = S0.card)
    (hvis0 : ∀ v < X.card, st0.mem (cfg.visStampAddr + v) ≠ cfg.bfsGen)
    (hr0 : st0.regs 0 = cfgAddr) :
    let res := bfsLayers adj V S0 cfg.maxDist stopSet
    Triple w p (fun st => st = st0) bfsLayersProc
      (retPost fun v st' =>
        v = res.visited.card ∧
        BfsOutAt st'.mem X cfg cfgAddr res ∧
        (∀ u < X.card, origOf X u ∉ res.visited →
          st'.mem (cfg.visStampAddr + u) = st0.mem (cfg.visStampAddr + u)) ∧
        (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st'.mem a = st0.mem a))
      (fun _ => bfsProgCost (bfsLayers adj V S0 cfg.maxDist stopSet).cost) := by
  have hS0_X : S0 ⊆ X := Finset.Subset.trans hS0_V hVX
  have hS0_inter : S0 ∩ V = S0 := Finset.inter_eq_left.mpr hS0_V
  have hS0_le : S0.card ≤ X.card := Finset.card_le_card hS0_X
  rcases hdisj with ⟨hd_vd, hd_vlo, hd_vld, hd_vt, hd_vc, hd_dlo, hd_dld, hd_dt, hd_dc,
    hd_lold, hd_lot, hd_loc, hd_ldt, hd_ldc, hd_tc,
    hr_cfg, hr_off, hr_nb, hr_mask, hr_stop, hr_init,
    hw_cfg, hw_off, hw_nb, hw_mask, hw_stop, hw_vis, hw_dist, hw_lo, hw_ld, hw_tmp, hw_init,
    hw_mb, hw_hs, hw_sv, hw_gen, hw_md, hw_m2, hw_nX, hw4⟩
  have hdisj' : BfsDisj w X.card m2 cfg cfgAddr :=
    ⟨hd_vd, hd_vlo, hd_vld, hd_vt, hd_vc, hd_dlo, hd_dld, hd_dt, hd_dc,
      hd_lold, hd_lot, hd_loc, hd_ldt, hd_ldc, hd_tc,
      hr_cfg, hr_off, hr_nb, hr_mask, hr_stop, hr_init,
      hw_cfg, hw_off, hw_nb, hw_mask, hw_stop, hw_vis, hw_dist, hw_lo, hw_ld, hw_tmp, hw_init,
      hw_mb, hw_hs, hw_sv, hw_gen, hw_md, hw_m2, hw_nX, hw4⟩
  dsimp only
  wram_enter
  subst st
  unfold bfsLayersProc
  dsimp only [seqStmts]
  refine runs_seq_triple_le (bfsLoadCfg_triple (p := p) hcfg hr0 hw_cfg) rfl (fun st1 hst1 => ?_)
  rcases hst1 with ⟨hmem1, hregs1⟩
  have hr1_0 : st1.regs 0 = cfgAddr := hregs1 0 (by decide)
  have hr1_10 : st1.regs 10 = cfg.layerOffAddr := hregs1 10 (by decide)
  have hr1_16 : st1.regs 16 = S0.card := (hregs1 16 (by decide)).trans hinit_len
  refine runs_seq_store_le (x := cfg.layerOffAddr) (v := 0) (by eval_expr) (by eval_expr) ?_
  set st2 : State := { st1 with mem := Function.update st1.mem cfg.layerOffAddr 0 }
  have hst2_fr : ∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st2.mem a = st0.mem a := by
    intro a ha
    have hne : a ≠ cfg.layerOffAddr := fun h => ha (Or.inr (Or.inr (Or.inl (by omega))))
    simp only [st2, Function.update_of_ne hne, hmem1]
  by_cases hS0_empty : S0.card = 0
  · -- Empty S0: return immediately
    have hS0_eq : S0 = ∅ := Finset.card_eq_zero.mp hS0_empty
    have hcond0 : (Expr.reg 16).eval w st2 = some 0 := by simp [Expr.eval, st2, hr1_16, hS0_empty]
    have hwr := bfsWriteRet_triple (p := p) (st0 := st2) hr1_0 hw_cfg
      (vNumL := 0) (vTotV := 0) (vMaxR := 0) (vHit := 0) (vExh := 1)
      (eNumL := .const 0) (eTotV := .const 0) (eMaxR := .const 0)
      (eHit := .const 0) (eExh := .const 1)
      (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr)
      (by intro e he m; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl)
      st2 ω rfl
    rcases hwr with ⟨o3, st3, c3, hrun3, hpost3, hc3⟩
    cases o3 with
    | normal => exact hpost3.elim
    | returned v =>
      rcases hpost3 with ⟨hv_eq, h16, h17, h18, h19, h20, hfr3⟩
      refine ⟨.returned v, st3, (Expr.reg 16).size + c3 + 1,
        runs_cond_iff.mpr ⟨0, c3, hcond0, by simpa using hrun3, rfl⟩, ?_, ?_⟩
      · dsimp only [retPost]
        simp only [bfsLayers, hS0_eq, Finset.empty_inter, Finset.sort_empty, List.isEmpty_nil, ↓reduceIte]
        refine ⟨by simp [hv_eq], ⟨?_, ?_, ?_, ?_, h16, h17, h18, h19, h20⟩, ?_, ?_⟩
        · intro r hr; have hr0' : r = 0 := by simp at hr; omega
          subst hr0'
          have hne : cfg.layerOffAddr + 0 < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.layerOffAddr + 0 := by
            rcases hd_loc with h | h <;> omega
          rw [hfr3 _ hne]; simp [st2]
        · intro r hr; cases hr
        · intro u hu
          have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
            rcases hd_vc with h | h <;> omega
          have hne_lo : cfg.visStampAddr + u ≠ cfg.layerOffAddr := by
            have := disjRange_ne hd_vlo hu (by omega : 0 < X.card + 1); omega
          rw [hfr3 _ hne]
          simp only [st2, Function.update_of_ne hne_lo, hmem1]
          exact iff_of_false (hvis0 u hu) (Finset.notMem_empty _)
        · intro u _ hm; cases hm
        · intro u hu _
          have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
            rcases hd_vc with h | h <;> omega
          have hne_lo : cfg.visStampAddr + u ≠ cfg.layerOffAddr := by
            have := disjRange_ne hd_vlo hu (by omega : 0 < X.card + 1); omega
          rw [hfr3 _ hne]
          simp only [st2, Function.update_of_ne hne_lo, hmem1]
        · intro a ha
          have hne : a < cfgAddr + 16 ∨ cfgAddr + 21 ≤ a := by
            by_contra hc; push Not at hc
            exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc)))))
          rw [hfr3 a hne]; exact hst2_fr a ha
      · simp only [bfsLayers, hS0_eq, Finset.empty_inter, Finset.sort_empty, List.isEmpty_nil, ↓reduceIte,
          bfsProgCost, Expr.size] at hc3 ⊢
        omega
  · -- Non-empty S0: run bfsInitStmt
    have hS0_pos : 0 < S0.card := Nat.pos_of_ne_zero hS0_empty
    have hL0_nonempty : (S0.sort (· ≤ ·)).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hS0_pos
      exact ⟨x, (Finset.mem_sort (· ≤ ·)).mpr hx⟩
    have hst2_init_list : ListAt st2.mem cfg.initPtr ((S0.sort (· ≤ ·)).map (locOf X)) := by
      intro j hj
      simp only [List.length_map, Finset.length_sort] at hj
      rw [hst2_fr _ (hr_init _ ⟨by omega, by omega⟩)]
      exact hinit_list j (by simp [hj])
    have hst2_stop : cfg.hasStop ≠ 0 →
        ∀ v < X.card, st2.mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ stopSet := by
      intro hhs v hv'
      rw [hst2_fr _ (hr_stop hhs _ ⟨by omega, by omega⟩)]
      exact hstop_mem hhs v hv'
    have hst2_vis0 : ∀ v < X.card, st2.mem (cfg.visStampAddr + v) ≠ cfg.bfsGen := by
      intro v hv'
      have hne_lo : cfg.visStampAddr + v ≠ cfg.layerOffAddr := by
        have := disjRange_ne hd_vlo hv' (by omega : 0 < X.card + 1); omega
      simp only [st2, Function.update_of_ne hne_lo, hmem1]; exact hvis0 v hv'
    have hinit_run := bfsInit_triple (p := p) (st0 := st2) hS0_X hdisj' hst2_init_list hinit_len hS0_pos
      hstop hst2_stop hst2_vis0 hregs1 st2 ω rfl
    rcases hinit_run with ⟨o3, st3, c3, hrun3, hpost3, hc3⟩
    cases o3 with
    | returned _ => exact hpost3.elim
    | normal =>
      rcases hpost3 with ⟨hr3, hr3_21, hlo3_1, hld3, hvis3, hdist3, hvis3_eq, hfr3, hlo3_0⟩
      have hst3_lo0 : st3.mem cfg.layerOffAddr = 0 := by rw [hlo3_0]; simp [st2]
      have hst3_fr : ∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st3.mem a = st0.mem a := by
        intro a ha; rw [hfr3 a ha, hst2_fr a ha]
      have hst3_vis_out : ∀ v < X.card, origOf X v ∉ S0 →
          st3.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v) := by
        intro v hv' hnot
        have hne_lo : cfg.visStampAddr + v ≠ cfg.layerOffAddr := by
          have := disjRange_ne hd_vlo hv' (by omega : 0 < X.card + 1); omega
        simp only [hvis3_eq v hv', hnot, ↓reduceIte, st2, Function.update_of_ne hne_lo, hmem1]
      have hr3_0 : st3.regs 0 = cfgAddr := (hr3 0 (by decide)).trans hr1_0
      have hr3_16 : st3.regs 16 = S0.card := (hr3 16 (by decide)).trans hr1_16
      by_cases hhit0 : (S0.sort (· ≤ ·)).any (fun v => decide (v ∈ stopSet))
      · -- Layer 0 hits stopSet: write outputs and return
        have hwr := bfsWriteRet_triple (p := p) (st0 := st3) hr3_0 hw_cfg
          (vNumL := 1) (vTotV := S0.card) (vMaxR := 0) (vHit := 1) (vExh := 0)
          (eNumL := .const 1) (eTotV := .reg 16) (eMaxR := .const 0)
          (eHit := .const 1) (eExh := .const 0)
          (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr)
          (by intro e he m; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl)
          st3 ω rfl
        rcases hwr with ⟨o4, st4, c4, hrun4, hpost4, hc4⟩
        cases o4 with
        | normal => exact hpost4.elim
        | returned v =>
          rcases hpost4 with ⟨hv_eq, h16, h17, h18, h19, h20, hfr4⟩
          have hcond_true : Runs w p ω
              (seqStmts
                [ bfsInitStmt
                , .cond (.reg 21)
                    (bfsWriteRetStmt (.const 1) (.reg 16) (.const 0) (.const 1) (.const 0))
                    (seqStmts
                      [ .assign 17 (.const 0)
                      , .assign 18 (.const 0)
                      , .assign 19 (.reg 16)
                      , bfsMainLoopStmt
                      , bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                          (.const 0) (.const 0) ]) ])
              st2 (.returned v) st4 (c3 + ((Expr.reg 21).size + c4 + 1) + 1) := by
            dsimp only [seqStmts]
            refine runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hrun3, ?_, rfl⟩)
            refine runs_cond_iff.mpr ⟨1, c4, by simp [Expr.eval, hr3_21, hhit0], by simpa using hrun4, rfl⟩
          refine ⟨.returned v, st4, (Expr.reg 16).size + (c3 + ((Expr.reg 21).size + c4 + 1) + 1) + 1,
            runs_cond_iff.mpr ⟨S0.card, _, by simp [Expr.eval, st2, hr1_16],
              by simpa [hS0_empty] using hcond_true, rfl⟩, ?_, ?_⟩
          · dsimp only [retPost]
            simp only [bfsLayers, hS0_inter, hL0_nonempty, Bool.false_eq_true, ↓reduceIte, hhit0]
            refine ⟨hv_eq, ⟨?_, ?_, ?_, ?_, h16, h17, h18, h19, h20⟩, ?_, ?_⟩
            · intro r hr
              have hr_cases : r = 0 ∨ r = 1 := by simp at hr; omega
              rcases hr_cases with rfl | rfl
              · have hne : cfg.layerOffAddr + 0 < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.layerOffAddr + 0 := by
                  rcases hd_loc with h | h <;> omega
                rw [hfr4 _ hne]; simp [hst3_lo0]
              · have hne : cfg.layerOffAddr + 1 < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.layerOffAddr + 1 := by
                  rcases hd_loc with h | h <;> omega
                rw [hfr4 _ hne]; simp [hlo3_1, Finset.length_sort]
            · intro r hr j hj
              have hr0' : r = 0 := by simp at hr; omega
              subst hr0'
              simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero,
                List.getElem_cons_zero] at hj ⊢
              simp only [List.length_map, Finset.length_sort] at hj
              have hne : cfg.layerDataAddr + j < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.layerDataAddr + j := by
                rcases hd_ldc with h | h <;> omega
              rw [hfr4 _ hne]; exact hld3 j (by simp [hj])
            · intro u hu
              have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                rcases hd_vc with h | h <;> omega
              rw [hfr4 _ hne]; exact hvis3 u hu
            · intro u hu hm
              have hne : cfg.distAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.distAddr + u := by
                rcases hd_dc with h | h <;> omega
              rw [hfr4 _ hne, hdist3 u hu hm]; simp [hm]
            · intro u hu hnot
              have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                rcases hd_vc with h | h <;> omega
              rw [hfr4 _ hne]; exact hst3_vis_out u hu hnot
            · intro a ha
              have hne : a < cfgAddr + 16 ∨ cfgAddr + 21 ≤ a := by
                by_contra hc; push Not at hc
                exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc)))))
              rw [hfr4 a hne]; exact hst3_fr a ha
          · simp only [bfsLayers, hS0_inter, hL0_nonempty, Bool.false_eq_true, ↓reduceIte, hhit0,
              bfsProgCost, Finset.length_sort, Expr.size] at hc3 hc4 ⊢
            omega
      · -- Enter main BFS loop!
        set st4 : State :=
          { st3 with regs := Function.update (Function.update (Function.update st3.regs 17 0) 18 0) 19 S0.card }
        have hsetup_run : ∃ c4,
            Runs w p ω
              (seqStmts [ .assign 17 (.const 0), .assign 18 (.const 0), .assign 19 (.reg 16) ])
              st3 .normal st4 c4 ∧ c4 ≤ 15 := by
          have htr : Triple w p (fun st => st = st3)
              (seqStmts [ .assign 17 (.const 0), .assign 18 (.const 0), .assign 19 (.reg 16) ])
              (normalPost fun st' => st' = st4) (fun _ => 15) := by
            wram_enter; subst st; dsimp only [seqStmts]
            refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
            refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
            refine runs_assign_le (v := S0.card) (by eval_expr) rfl (by wram_cost)
          obtain ⟨o4, st4', c4, hr4, hp4, hc4⟩ := htr st3 ω rfl
          cases o4 with
          | returned _ => exact hp4.elim
          | normal => subst hp4; exact ⟨c4, hr4, hc4⟩
        rcases hsetup_run with ⟨c4, hrun4, hc4⟩
        set initDist : ℕ → Option ℕ := fun v => if v ∈ S0 then some 0 else none
        have hmain := bfsMainLoop_triple (p := p) hVX hadj_X hcsr hm2 hdisj' hmask hstop hstop_mem
          cfg.maxDist 0 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)] S0 initDist st4
          hw_md hS0_V
          (fun L hL => by
            simp only [List.mem_singleton] at hL; subst hL
            exact ⟨by simp [Finset.length_sort, hS0_pos], fun x hx => (Finset.mem_sort (· ≤ ·)).mp hx⟩)
          rfl
          (fun x hx => (Finset.mem_sort (· ≤ ·)).mp hx)
          (by simp [Finset.length_sort, hS0_pos])
          (by simp [Finset.length_sort])
          (by simp [Finset.length_sort])
          (fun r hr => by
            have hr_cases : r = 0 ∨ r = 1 := by omega
            rcases hr_cases with rfl | rfl
            · simp [st4, hst3_lo0]
            · simp [st4, hlo3_1, Finset.length_sort])
          (fun r hr => by
            have hr0' : r = 0 := by omega
            subst hr0'
            simpa [st4] using hld3)
          (by simpa [st4] using hld3)
          hvis3 hst3_vis_out
          (fun v hv' hm => by simp [initDist, hm, st4, hdist3 v hv' hm])
          hst3_fr
          (fun r hr => by
            interval_cases r <;> first
              | rfl
              | (simp [st4]
                 try exact (hr3 _ (by decide)).trans (hregs1 _ (by decide))))
          ω
        rcases hmain with ⟨o5, st5, c5, hrun5, hpost5, hc5⟩
        have htail : ∃ v st6 c6,
            Runs w p ω
              (.seq bfsMainLoopStmt
                (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                  (.const 0) (.const 0)))
              st4 (.returned v) st6 c6 ∧
            let res0 := bfsLoop adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)] S0 initDist 0
            v = res0.visited.card ∧
            BfsOutAt st6.mem X cfg cfgAddr res0 ∧
            (∀ u < X.card, origOf X u ∉ res0.visited →
              st6.mem (cfg.visStampAddr + u) = st0.mem (cfg.visStampAddr + u)) ∧
            (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st6.mem a = st0.mem a) ∧
            c6 ≤ 140 * res0.cost + 55 := by
          cases o5 with
          | returned v =>
            exact ⟨v, st5, c5 + 1, runs_seq_iff.mpr (Or.inl ⟨v, c5, hrun5, rfl, rfl⟩),
              hpost5.1, hpost5.2.1, hpost5.2.2.1, hpost5.2.2.2, by omega⟩
          | normal =>
            rcases hpost5 with ⟨hhs_f, hexh_f, hr5_0, hr5_17, hr5_19, hlen_eq, hvis_le5, hmax_le5,
              hsum5, hlo5, hld5, hvis5, hvis5_out, hdist5, hfr5⟩
            set res0 := bfsLoop adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)] S0 initDist 0
            have hwr := bfsWriteRet_triple (p := p) (st0 := st5) hr5_0 hw_cfg
              (vNumL := res0.maxReached + 1) (vTotV := res0.visited.card) (vMaxR := res0.maxReached)
              (vHit := 0) (vExh := 0)
              (eNumL := .bin .add (.reg 17) (.const 1)) (eTotV := .reg 19) (eMaxR := .reg 17)
              (eHit := .const 0) (eExh := .const 0)
              (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr)
              (by intro e he m; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                  rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl)
              st5 ω rfl
            rcases hwr with ⟨o6, st6, c6, hrun6, hpost6, hc6⟩
            cases o6 with
            | normal => exact hpost6.elim
            | returned v =>
              rcases hpost6 with ⟨hv_eq, h16, h17, h18, h19, h20, hfr6⟩
              refine ⟨v, st6, c5 + c6 + 1,
                runs_seq_iff.mpr (Or.inr ⟨st5, c5, c6, hrun5, hrun6, rfl⟩),
                hv_eq, ⟨?_, ?_, ?_, ?_, by rw [h16, hlen_eq], h17, h18, by simp [h19, hhs_f], by simp [h20, hexh_f]⟩,
                ?_, ?_, ?_⟩
              · intro idx hidx
                have hne : cfg.layerOffAddr + idx < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.layerOffAddr + idx := by
                  rcases hd_loc with h | h <;> omega
                rw [hfr6 _ hne]; exact hlo5 idx hidx
              · intro idx hidx j hj
                have hj_lt : ((res0.layers.take idx).map List.length).sum + j < X.card := by
                  have hle_sum : ((res0.layers.take idx).map List.length).sum +
                      (res0.layers[idx]'hidx).length ≤ (res0.layers.map List.length).sum := by
                    have h1 : ((res0.layers.take (idx + 1)).map List.length).sum =
                        ((res0.layers.take idx).map List.length).sum + (res0.layers[idx]'hidx).length := by
                      rw [List.take_succ_eq_append_getElem hidx, List.map_append, List.sum_append,
                        List.map_singleton, List.sum_singleton]
                    rw [← h1]
                    have h2 := List.take_append_drop (idx + 1) res0.layers
                    have h3 := congr_arg (fun ls => (ls.map List.length).sum) h2
                    simp only [List.map_append, List.sum_append] at h3
                    omega
                  simp only [List.length_map] at hj
                  omega
                have hne : cfg.layerDataAddr + ((res0.layers.take idx).map List.length).sum + j < cfgAddr + 16 ∨
                    cfgAddr + 21 ≤ cfg.layerDataAddr + ((res0.layers.take idx).map List.length).sum + j := by
                  rcases hd_ldc with h | h <;> omega
                rw [hfr6 _ hne]; exact hld5 idx hidx j hj
              · intro u hu
                have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                  rcases hd_vc with h | h <;> omega
                rw [hfr6 _ hne]; exact hvis5 u hu
              · intro u hu hm
                have hne : cfg.distAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.distAddr + u := by
                  rcases hd_dc with h | h <;> omega
                rw [hfr6 _ hne]; exact hdist5 u hu hm
              · intro u hu hnot
                have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                  rcases hd_vc with h | h <;> omega
                rw [hfr6 _ hne]; exact hvis5_out u hu hnot
              · intro a ha
                have hne : a < cfgAddr + 16 ∨ cfgAddr + 21 ≤ a := by
                  by_contra hc; push Not at hc
                  exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc)))))
                rw [hfr6 a hne]; exact hfr5 a ha
              · simp only [Expr.size] at hc6; omega
        rcases htail with ⟨v, st6, c6, hrun6, hv_eq, hout6, hvis6_out, hfr6, hc6⟩
        have hfalse_run : ∃ cF,
            Runs w p ω
              (seqStmts
                [ .assign 17 (.const 0)
                , .assign 18 (.const 0)
                , .assign 19 (.reg 16)
                , bfsMainLoopStmt
                , bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                    (.const 0) (.const 0) ])
              st3 (.returned v) st6 cF ∧ cF ≤ c4 + c6 + 10 := by
          rcases runs_seq_iff.mp hrun4 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
          · cases h
          rcases runs_seq_iff.mp hrb with ⟨_, _, _, h, _⟩ | ⟨sb, cb1, cb2, hrb1, hrb2, rfl⟩
          · cases h
          refine ⟨ca + (cb1 + (cb2 + c6 + 1) + 1) + 1, ?_, by omega⟩
          dsimp only [seqStmts]
          exact runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, hra,
            runs_seq_iff.mpr (Or.inr ⟨sb, cb1, _, hrb1,
              runs_seq_iff.mpr (Or.inr ⟨st4, cb2, _, hrb2, hrun6, rfl⟩), rfl⟩), rfl⟩)
        rcases hfalse_run with ⟨cF, hrunF, hcF⟩
        have hcond_true : Runs w p ω
            (seqStmts
              [ bfsInitStmt
              , .cond (.reg 21)
                  (bfsWriteRetStmt (.const 1) (.reg 16) (.const 0) (.const 1) (.const 0))
                  (seqStmts
                    [ .assign 17 (.const 0)
                    , .assign 18 (.const 0)
                    , .assign 19 (.reg 16)
                    , bfsMainLoopStmt
                    , bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                        (.const 0) (.const 0) ]) ])
            st2 (.returned v) st6 (c3 + ((Expr.reg 21).size + cF + 1) + 1) := by
          dsimp only [seqStmts]
          refine runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hrun3, ?_, rfl⟩)
          refine runs_cond_iff.mpr ⟨0, cF, by simp [Expr.eval, hr3_21, hhit0], by simpa using hrunF, rfl⟩
        have hres_eq :
            bfsLayers adj V S0 cfg.maxDist stopSet =
              { bfsLoop adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)] S0 initDist 0 with
                cost := (bfsLoop adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)] S0 initDist 0).cost +
                  (S0.card + S0.card + 1) } := by
          have hcost_add := bfsLoop_cost_add adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)]
            S0 initDist 0 (S0.card + S0.card + 1)
          have hf := bfsLoop_fields_add adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)]
            S0 initDist 0 (S0.card + S0.card + 1)
          simp only [bfsLayers, hS0_inter, hL0_nonempty, Bool.false_eq_true, ↓reduceIte, hhit0,
            Finset.length_sort]
          cases hA : bfsLoop adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)] S0 initDist
            (S0.card + S0.card + 1) with
          | mk lA vA dA mA hA' eA cA =>
          cases hB : bfsLoop adj V stopSet cfg.maxDist 0 (S0.sort (· ≤ ·)) [S0.sort (· ≤ ·)] S0 initDist 0 with
          | mk lB vB dB mB hB' eB cB =>
          simp only [Nat.zero_add] at hcost_add hf
          rw [hA, hB] at hf hcost_add
          dsimp only at hf hcost_add
          rcases hf with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only [hcost_add]
        refine ⟨.returned v, st6, _,
          runs_cond_iff.mpr ⟨S0.card, _, by simp [Expr.eval, st2, hr1_16],
            by simpa [hS0_empty] using hcond_true, rfl⟩, ?_, ?_⟩
        · dsimp only [retPost]
          rw [hres_eq]
          exact ⟨hv_eq, hout6, hvis6_out, hfr6⟩
        · rw [hres_eq]
          simp only [bfsProgCost, Expr.size] at hc3 hc4 hc6 hcF ⊢
          omega

/-! ## 3. Procedure Contract (`bfsLayersContract` and `bfsLayers_meetsContract`) -/

/-- Contract for `bfsLayersProc` on argument `[cfgAddr]`. -/
@[expose] def bfsLayersContract (w : ℕ) (X V S0 stopSet : Finset ℕ) (adj : ℕ → List (ℕ × ℕ))
    (cfg : BfsCfg) (m2 : ℕ) : Contract where
  pre args mem :=
    args.length = 1 ∧
    let cfgAddr := args.getD 0 0
    V ⊆ X ∧
    S0 ⊆ V ∧
    (∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X) ∧
    BfsCfgAt mem cfgAddr cfg ∧
    NbCsrAt mem cfg.offAddr cfg.nbAddr X adj ∧
    adjCsrOff X adj X.card ≤ m2 ∧
    BfsDisj w X.card m2 cfg cfgAddr ∧
    (∀ v < X.card, mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V) ∧
    (cfg.hasStop = 0 → stopSet = ∅) ∧
    (cfg.hasStop ≠ 0 →
      ∀ v < X.card, mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ stopSet) ∧
    ListAt mem cfg.initPtr ((S0.sort (· ≤ ·)).map (locOf X)) ∧
    cfg.initLen = S0.card ∧
    (∀ v < X.card, mem (cfg.visStampAddr + v) ≠ cfg.bfsGen)
  post args mem v mem' :=
    let cfgAddr := args.getD 0 0
    let res := bfsLayers adj V S0 cfg.maxDist stopSet
    v = res.visited.card ∧
    BfsOutAt mem' X cfg cfgAddr res ∧
    (∀ u < X.card, origOf X u ∉ res.visited →
      mem' (cfg.visStampAddr + u) = mem (cfg.visStampAddr + u)) ∧
    (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → mem' a = mem a)
  cost _ _ := bfsProgCost (bfsLayers adj V S0 cfg.maxDist stopSet).cost

/-- `bfsLayersProc` meets `bfsLayersContract` deterministically. -/
theorem bfsLayers_meetsContract {w : ℕ} {p : Program} {idx : ℕ}
    (hproc : p.procs[idx]? = some bfsLayersProc)
    (X V S0 stopSet : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) (cfg : BfsCfg) (m2 : ℕ) :
    MeetsContract w p idx (bfsLayersContract w X V S0 stopSet adj cfg m2) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨hlen, hVX, hS0_V, hadj_X, hcfg, hcsr, hm2, hdisj, hmask, hstop, hstop_mem,
    hinit_list, hinit_len, hvis0⟩
  have htr := bfsLayers_triple (w := w) (p := p) (st0 := startState args mem pos)
    hVX hS0_V hadj_X hcfg hcsr hm2 hdisj hmask hstop hstop_mem hinit_list hinit_len hvis0 rfl
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := htr (startState args mem pos) ω rfl
  cases o with
  | normal => exact hpost.elim
  | returned v =>
    exact ⟨bfsLayersProc, hproc, .returned v, st', c, hrun, hpost, hc⟩

end MinCostFlow.ExpanderDecomp
