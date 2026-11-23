module

public import MinCostFlow.ExpanderDecomp.RouteProgDFSStep

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Blocking DFS Word-RAM Procedure (`dfsBlock_triple`, `dfsBlock_meetsContract`)

Verifies `dfsBlockProc` against `dfsBlock`: loads the 24-word config
block, runs `dfsSourcesLoopStmt` across all sources in `S ∩ V`, prepends accepted
paths directly onto the incoming `PathChainAt` chain `acc`, writes outputs to
`cfgAddr + 24 .. cfgAddr + 28`, and runs in `≤ 150 * (dfsBlock ...).cost + 260`
deterministic Word-RAM steps.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Fast Config Load Helper (`dfsLoadCfg_triple`) -/

private lemma dfsLoadCfg_step {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {i cfgAddr : ℕ} {f mem0 : ℕ → ℕ} {st : State} {rest : Stmt} {P : Outcome → State → Prop} {c1 : ℕ}
    (hw : cfgAddr + 32 < 2 ^ w) (hi : i ≤ 23)
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

private lemma dfsLoadCfg_triple {w : ℕ} {p : Program}
    {cfg : DfsCfg} {cfgAddr : ℕ} {st0 : State}
    (hcfg : DfsCfgAt st0.mem cfgAddr cfg)
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 32 < 2 ^ w) :
    Triple w p (fun st => st = st0) dfsLoadCfgStmt
      (normalPost fun st1 =>
        st1.mem = st0.mem ∧
        ∀ r ≤ 24, st1.regs r =
          match r with
          | 0 => cfgAddr
          | 1 => cfg.offAddr | 2 => cfg.nbAddr | 3 => cfg.edgeAddr
          | 4 => cfg.maskArrAddr | 5 => cfg.maskBadVal
          | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
          | 8 => cfg.visStampAddr | 9 => cfg.bfsGen | 10 => cfg.distAddr
          | 11 => cfg.curStampAddr | 12 => cfg.curAddr
          | 13 => cfg.usedStampAddr | 14 => cfg.deadStampAddr
          | 15 => cfg.stkVertAddr | 16 => cfg.stkEdgeAddr | 17 => cfg.usedListAddr
          | 18 => cfg.dfsGen | 19 => cfg.targetDepth | 20 => cfg.srcPtr | 21 => cfg.srcLen
          | 22 => cfg.heapIn | 23 => cfg.inHead | _ => cfg.inTail)
      (fun _ => 175) := by
  let f : ℕ → ℕ := fun r =>
    match r with
    | 0 => cfgAddr
    | 1 => cfg.offAddr | 2 => cfg.nbAddr | 3 => cfg.edgeAddr
    | 4 => cfg.maskArrAddr | 5 => cfg.maskBadVal
    | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
    | 8 => cfg.visStampAddr | 9 => cfg.bfsGen | 10 => cfg.distAddr
    | 11 => cfg.curStampAddr | 12 => cfg.curAddr
    | 13 => cfg.usedStampAddr | 14 => cfg.deadStampAddr
    | 15 => cfg.stkVertAddr | 16 => cfg.stkEdgeAddr | 17 => cfg.usedListAddr
    | 18 => cfg.dfsGen | 19 => cfg.targetDepth | 20 => cfg.srcPtr | 21 => cfg.srcLen
    | 22 => cfg.heapIn | 23 => cfg.inHead | _ => cfg.inTail
  rcases hcfg with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23⟩
  wram_enter; subst st; dsimp only; simp only [Nat.zero_add]; unfold dfsLoadCfgStmt; dsimp only [seqStmts]
  have hr0' : ∀ r ≤ 0, st0.regs r = f r := fun r hr => by
    have : r = 0 := by omega
    subst this; exact hr0
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) rfl hr0' rfl hc0 (c1 := 168) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc1 (c1 := 161) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc2 (c1 := 154) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc3 (c1 := 147) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc4 (c1 := 140) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc5 (c1 := 133) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc6 (c1 := 126) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc7 (c1 := 119) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc8 (c1 := 112) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc9 (c1 := 105) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc10 (c1 := 98) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc11 (c1 := 91) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc12 (c1 := 84) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc13 (c1 := 77) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc14 (c1 := 70) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc15 (c1 := 63) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc16 (c1 := 56) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc17 (c1 := 49) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc18 (c1 := 42) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc19 (c1 := 35) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc20 (c1 := 28) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc21 (c1 := 21) (fun s hm hr => ?_)
  refine dfsLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl hc22 (c1 := 14) (fun s hm hr => ?_)
  have hs0 : s.regs 0 = cfgAddr := hr 0 (by decide)
  have hev24 : (Expr.load (.bin .add (.reg 0) (.const 23))).eval w s = some (f 24) := by
    simp [Expr.eval, BinOp.eval, hs0, show 23 < 2 ^ w by omega, show cfgAddr + 23 < 2 ^ w by omega,
      hm, hc23, f]
  refine ⟨.normal, { s with regs := Function.update s.regs 24 (f 24) }, _,
    runs_assign_iff.mpr ⟨f 24, hev24, rfl, rfl, rfl⟩, ⟨hm, fun r hr' => ?_⟩, ?_⟩
  · dsimp only
    by_cases h : r = 24
    · subst h; exact Function.update_self _ _ _
    · rw [Function.update_of_ne h]; exact hr r (by omega)
  · simp only [Expr.size]; omega

/-! ## 2. Outer Sources Loop (`dfsSourcesLoop_triple`) -/

private lemma dfsStateAt_cost_irrel' {mem mem0 : ℕ → ℕ} {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {cfg : DfsCfg} {cfgAddr heapLo heapPtr pathsHead pathsTail : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {ds1 ds2 : DFSState} {ul : List ℕ}
    (h : DfsStateAt mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul)
    (hu : ds1.used = ds2.used) (hd : ds1.dead = ds2.dead)
    (hc : ds1.cursor = ds2.cursor) (hp : ds1.paths = ds2.paths) :
    DfsStateAt mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds2 ul := by
  cases ds1; cases ds2; simp only at hu hd hc hp; subst hu; subst hd; subst hc; subst hp
  rcases h with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩

private lemma dfsSourcesLoop_triple {w : ℕ} {p : Program}
    {X V T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    {cfg : DfsCfg} {cfgAddr m2 heapLo fuel : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {srcs : List ℕ} {mem0 : ℕ → ℕ}
    (hVX : V ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcsr : AdjCsrAt mem0 cfg.offAddr cfg.nbAddr cfg.edgeAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : DfsDisj w X.card m2 cfg cfgAddr)
    (hheap_lo : heapLo ≤ cfg.heapIn)
    (hacc_disj : ∀ a, heapLo ≤ a ∧ a < cfg.heapIn → ¬ DfsWriteSet X.card cfg cfgAddr a)
    (hmask : ∀ v < X.card, mem0 (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hstop : ∀ v < X.card, mem0 (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ T)
    (hdist_mem : ∀ v < X.card,
      (mem0 (cfg.visStampAddr + v) = cfg.bfsGen ∧ dist (origOf X v) = some (mem0 (cfg.distAddr + v))) ∨
      (mem0 (cfg.visStampAddr + v) ≠ cfg.bfsGen ∧ dist (origOf X v) = none))
    (hsrc_list : ListAt mem0 cfg.srcPtr (srcs.map (locOf X)))
    (hsrc_len : cfg.srcLen = srcs.length)
    (hsrc_ok : ∀ s ∈ srcs, s ∈ V ∧ dist s = some 0)
    (rem : ℕ) :
    ∀ (srcIdx : ℕ) (ds : DFSState) (ul : List ℕ)
      (heapPtr pathsHead pathsTail : ℕ) (st0 : State),
      srcIdx + rem = srcs.length →
      dfsPot V ds < fuel →
      DfsStateAt st0.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds ul →
      DfsRegsAt st0.regs cfg cfgAddr heapPtr pathsHead pathsTail ds.used.card ds.paths.length →
      st0.regs 27 = srcIdx →
      ∀ ω,
        let dsF := dfsSources V T dist cfg.targetDepth fuel (srcs.drop srcIdx) { ds with cost := 0 }
        ∃ st' c,
          Runs w p ω dfsSourcesLoopStmt st0 .normal st' c ∧
          (∃ heapPtr' pathsHead' pathsTail' ul',
            DfsStateAt st'.mem mem0 X V adj cfg cfgAddr heapLo heapPtr' pathsHead' pathsTail' acc dsF ul' ∧
            DfsRegsAt st'.regs cfg cfgAddr heapPtr' pathsHead' pathsTail' dsF.used.card dsF.paths.length) ∧
          c ≤ 150 * dsF.cost + 5 := by
  have hw_src := hdisj.w_src; have hw_us := hdisj.w_us; have hw_ds := hdisj.w_ds
  have hw_sv := hdisj.w_sv; have hw_dg := hdisj.w_dgen; have hw4 := hdisj.w4
  induction rem with
  | zero =>
    intro srcIdx ds ul heapPtr pathsHead pathsTail st0 hrem _ hinv hregs hr27 ω
    have hidx_eq : srcIdx = srcs.length := by omega
    have hr21 : st0.regs 21 = srcs.length := (hregs 21 (by decide)).trans hsrc_len
    have hdrop : srcs.drop srcIdx = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hev0 : (Expr.bin .lt (.reg 27) (.reg 21)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr27, hr21, hidx_eq, show 0 < 2 ^ w by omega]
    refine ⟨st0, (Expr.bin .lt (.reg 27) (.reg 21)).size + 1,
      runs_loop_iff.mpr (Or.inl ⟨hev0, rfl, rfl, rfl⟩), ?_, ?_⟩
    · simp only [hdrop, dfsSources]
      exact ⟨heapPtr, pathsHead, pathsTail, ul, dfsStateAt_cost_irrel' hinv rfl rfl rfl rfl, hregs⟩
    · simp only [hdrop, dfsSources, Expr.size]; omega
  | succ rem' ih =>
    intro srcIdx ds ul heapPtr pathsHead pathsTail st0 hrem hfuel hinv hregs hr27 ω
    have hidx_lt : srcIdx < srcs.length := by omega
    have hr20 : st0.regs 20 = cfg.srcPtr := hregs 20 (by decide)
    have hr21 : st0.regs 21 = srcs.length := (hregs 21 (by decide)).trans hsrc_len
    have hguard : (Expr.bin .lt (.reg 27) (.reg 21)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr27, hr21, hidx_lt, show 1 < 2 ^ w by omega]
    set s := srcs[srcIdx]'hidx_lt
    have hs_mem : s ∈ srcs := List.getElem_mem hidx_lt
    have hsV : s ∈ V := (hsrc_ok s hs_mem).1
    have hsDist : dist s = some 0 := (hsrc_ok s hs_mem).2
    have hsX : s ∈ X := hVX hsV
    have hs_loc_lt : locOf X s < X.card := locOf_lt hsX
    have hdrop_cons : srcs.drop srcIdx = s :: srcs.drop (srcIdx + 1) :=
      List.drop_eq_getElem_cons hidx_lt
    have hsrc_mem : st0.mem (cfg.srcPtr + srcIdx) = locOf X s := by
      rw [hinv.frame_out _ (hdisj.ro_src _ ⟨by omega, by omega⟩)]
      have := hsrc_list srcIdx (by simp [hidx_lt])
      simpa [s] using this
    -- Step 1: r28 := mem[srcPtr + srcIdx]
    set st1 : State := { st0 with regs := Function.update st0.regs 28 (locOf X s) }
    have hload_s : Runs w p ω (.assign 28 (.load (.bin .add (.reg 20) (.reg 27)))) st0 .normal st1
        ((Expr.load (.bin .add (.reg 20) (.reg 27))).size + 1) := by
      refine runs_assign_iff.mpr ⟨locOf X s, ?_, rfl, rfl, rfl⟩
      simp [Expr.eval, BinOp.eval, hr20, hr27, hsrc_mem, show cfg.srcPtr + srcIdx < 2 ^ w by omega]
    have hst1_r13 : st1.regs 13 = cfg.usedStampAddr := by simp [st1, hregs 13 (by decide)]
    have hst1_r14 : st1.regs 14 = cfg.deadStampAddr := by simp [st1, hregs 14 (by decide)]
    have hst1_r15 : st1.regs 15 = cfg.stkVertAddr := by simp [st1, hregs 15 (by decide)]
    have hst1_r18 : st1.regs 18 = cfg.dfsGen := by simp [st1, hregs 18 (by decide)]
    have hst1_r27 : st1.regs 27 = srcIdx := by simp [st1, hr27]
    have hst1_r28 : st1.regs 28 = locOf X s := by simp [st1]
    have hs_used_iff : st1.mem (cfg.usedStampAddr + locOf X s) = cfg.dfsGen ↔ s ∈ ds.used := by
      simpa [st1, origOf_locOf hsX] using hinv.used_stamp (locOf X s) hs_loc_lt
    have hs_dead_iff : st1.mem (cfg.deadStampAddr + locOf X s) = cfg.dfsGen ↔ s ∈ ds.dead := by
      simpa [st1, origOf_locOf hsX] using hinv.dead_stamp (locOf X s) hs_loc_lt
    by_cases hsd : s ∈ ds.used ∨ s ∈ ds.dead
    · -- Skip source s
      have hcond_skip : ∃ c2,
          Runs w p ω
            (.cond (.bin .eq (.load (.bin .add (.reg 13) (.reg 28))) (.reg 18))
              .nop
              (.cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 28))) (.reg 18))
                .nop
                (seqStmts
                  [ .store (.reg 15) (.reg 28)
                  , .assign 30 (.const 0)
                  , .assign 31 (.reg 28)
                  , .assign 29 (.const 1)
                  , dfsStepLoopStmt ])))
            st1 .normal st1 c2 ∧ c2 ≤ 20 := by
        by_cases hsu : s ∈ ds.used
        · have h1 : st1.mem (cfg.usedStampAddr + locOf X s) = cfg.dfsGen := hs_used_iff.mpr hsu
          have hev : (Expr.bin .eq (.load (.bin .add (.reg 13) (.reg 28))) (.reg 18)).eval w st1 = some 1 := by
            simp [Expr.eval, BinOp.eval, hst1_r13, hst1_r18, hst1_r28, h1,
              show cfg.usedStampAddr + locOf X s < 2 ^ w by omega, show 1 < 2 ^ w by omega]
          exact ⟨_, runs_cond_iff.mpr ⟨1, 1, hev, by simp [runs_nop_iff], rfl⟩, by simp [Expr.size]⟩
        · have hsD : s ∈ ds.dead := hsd.resolve_left hsu
          have h1 : st1.mem (cfg.usedStampAddr + locOf X s) ≠ cfg.dfsGen := mt hs_used_iff.mp hsu
          have h2 : st1.mem (cfg.deadStampAddr + locOf X s) = cfg.dfsGen := hs_dead_iff.mpr hsD
          have hev1 : (Expr.bin .eq (.load (.bin .add (.reg 13) (.reg 28))) (.reg 18)).eval w st1 = some 0 := by
            simp [Expr.eval, BinOp.eval, hst1_r13, hst1_r18, hst1_r28, h1,
              show cfg.usedStampAddr + locOf X s < 2 ^ w by omega, show 0 < 2 ^ w by omega]
          have hev2 : (Expr.bin .eq (.load (.bin .add (.reg 14) (.reg 28))) (.reg 18)).eval w st1 = some 1 := by
            simp [Expr.eval, BinOp.eval, hst1_r14, hst1_r18, hst1_r28, h2,
              show cfg.deadStampAddr + locOf X s < 2 ^ w by omega, show 1 < 2 ^ w by omega]
          refine ⟨(Expr.bin .eq (.load (.bin .add (.reg 13) (.reg 28))) (.reg 18)).size +
              ((Expr.bin .eq (.load (.bin .add (.reg 14) (.reg 28))) (.reg 18)).size + 1 + 1) + 1,
            runs_cond_iff.mpr ⟨0, _, hev1, ?_, rfl⟩, by simp [Expr.size]⟩
          simp only [↓reduceIte]
          exact runs_cond_iff.mpr ⟨1, 1, hev2, by simp [runs_nop_iff], rfl⟩
      rcases hcond_skip with ⟨c2, hrun2, hc2⟩
      set st2 : State := { st1 with regs := Function.update st1.regs 27 (srcIdx + 1) }
      have hinc : Runs w p ω (.assign 27 (.bin .add (.reg 27) (.const 1))) st1 .normal st2
          ((Expr.bin .add (.reg 27) (.const 1)).size + 1) := by
        refine runs_assign_iff.mpr ⟨srcIdx + 1, ?_, rfl, rfl, rfl⟩
        simp [Expr.eval, BinOp.eval, hst1_r27, show 1 < 2 ^ w by omega, show srcIdx + 1 < 2 ^ w by omega]
      have hbody : Runs w p ω _ st0 .normal st2 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload_s,
          runs_seq_iff.mpr (Or.inr ⟨st1, c2, _, hrun2, hinc, rfl⟩), rfl⟩)
      have hst2_regs : DfsRegsAt st2.regs cfg cfgAddr heapPtr pathsHead pathsTail ds.used.card ds.paths.length :=
        fun k hk => by
          simp only [st2, st1, Function.update_of_ne (by omega : k ≠ 27), Function.update_of_ne (by omega : k ≠ 28)]
          exact hregs k hk
      obtain ⟨st3, c3, hrun3, hpost3, hc3⟩ :=
        ih (srcIdx + 1) ds ul heapPtr pathsHead pathsTail st2 (by omega) hfuel hinv hst2_regs (by simp [st2]) ω
      have hadd := dfsSources_cost_add V T dist cfg.targetDepth fuel (srcs.drop (srcIdx + 1)) { ds with cost := 0 } 1
      set dsA := dfsSources V T dist cfg.targetDepth fuel (srcs.drop (srcIdx + 1)) { ds with cost := 1 }
      set dsB := dfsSources V T dist cfg.targetDepth fuel (srcs.drop (srcIdx + 1)) { ds with cost := 0 }
      have hAB : dsA = { dsB with cost := dsB.cost + 1 } := by
        rcases hadd with ⟨h1, h2, h3, h4, h5⟩
        cases hA : dsA; cases hB : dsB
        simp only [dsA, dsB, hA, hB] at h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5]
      have hstep_eq :
          dfsSources V T dist cfg.targetDepth fuel (srcs.drop srcIdx) { ds with cost := 0 } =
            { dsB with cost := dsB.cost + 1 } := by
        rw [← hAB, hdrop_cons]; simp only [dfsSources, hsd, ↓reduceIte, dsA]
      refine ⟨st3, _,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, _, c3, hguard, by omega, hbody, hrun3, rfl⟩)),
        ?_, ?_⟩
      · rw [hstep_eq]
        rcases hpost3 with ⟨hp3, ph3, pt3, ul3, hinv3, hregs3⟩
        exact ⟨hp3, ph3, pt3, ul3, dfsStateAt_cost_irrel' hinv3 rfl rfl rfl rfl, hregs3⟩
      · rw [hstep_eq]
        simp only [Expr.size] at hc2 hc3 ⊢; omega
    · -- Run dfsStepLoopStmt from source s
      push Not at hsd
      rcases hsd with ⟨hsu, hsD⟩
      have h1 : st1.mem (cfg.usedStampAddr + locOf X s) ≠ cfg.dfsGen := mt hs_used_iff.mp hsu
      have h2 : st1.mem (cfg.deadStampAddr + locOf X s) ≠ cfg.dfsGen := mt hs_dead_iff.mp hsD
      have hev1 : (Expr.bin .eq (.load (.bin .add (.reg 13) (.reg 28))) (.reg 18)).eval w st1 = some 0 := by
        simp [Expr.eval, BinOp.eval, hst1_r13, hst1_r18, hst1_r28, h1,
          show cfg.usedStampAddr + locOf X s < 2 ^ w by omega, show 0 < 2 ^ w by omega]
      have hev2 : (Expr.bin .eq (.load (.bin .add (.reg 14) (.reg 28))) (.reg 18)).eval w st1 = some 0 := by
        simp [Expr.eval, BinOp.eval, hst1_r14, hst1_r18, hst1_r28, h2,
          show cfg.deadStampAddr + locOf X s < 2 ^ w by omega, show 0 < 2 ^ w by omega]
      set mem2 := Function.update st1.mem cfg.stkVertAddr (locOf X s)
      set st2 : State :=
        { mem := mem2
          regs := Function.update (Function.update (Function.update st1.regs 30 0) 31 (locOf X s)) 29 1
          pos := st1.pos }
      have hsetup : ∃ c2,
          Runs w p ω
            (seqStmts
              [ .store (.reg 15) (.reg 28)
              , .assign 30 (.const 0)
              , .assign 31 (.reg 28)
              , .assign 29 (.const 1) ])
            st1 .normal st2 c2 ∧ c2 ≤ 20 := by
        have htr : Triple w p (fun st => st = st1)
            (seqStmts
              [ .store (.reg 15) (.reg 28)
              , .assign 30 (.const 0)
              , .assign 31 (.reg 28)
              , .assign 29 (.const 1) ])
            (normalPost fun st => st = st2) (fun _ => 20) := by
          wram_enter; subst st; dsimp only [seqStmts]
          refine runs_seq_store_le (x := cfg.stkVertAddr) (v := locOf X s) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
          refine runs_seq_assign_le (v := locOf X s) (by eval_expr) ?_
          refine runs_assign_le (v := 1) (by eval_expr) rfl (by wram_cost)
        obtain ⟨o2, st2', c2, hr2', hp2, hc2⟩ := htr st1 ω rfl
        cases o2 with | returned _ => exact hp2.elim | normal => subst hp2; exact ⟨c2, hr2', hc2⟩
      rcases hsetup with ⟨c2, hrun2, hc2⟩
      have h0_lt_X : 0 < X.card := by omega
      have hfr_m2 : ∀ a, a ≠ cfg.stkVertAddr → mem2 a = st0.mem a :=
        fun a h => Function.update_of_ne h _ _
      have hinv2 : DfsStateAt mem2 mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds ul := by
        refine ⟨hinv.used_sub, hinv.dead_sub, hinv.paths_le, ?_, ?_, ?_,
          hinv.ul_len, hinv.ul_nd, hinv.ul_sub, hinv.ul_cov, ?_, hinv.heap_lo, hinv.heap_hi,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro v hv
          rw [hfr_m2 _ (by have := disjRange_ne hdisj.us_sv hv h0_lt_X; omega)]
          exact hinv.used_stamp v hv
        · intro v hv
          rw [hfr_m2 _ (by have := disjRange_ne hdisj.ds_sv hv h0_lt_X; omega)]
          exact hinv.dead_stamp v hv
        · intro v hv
          rw [hfr_m2 _ (by have := disjRange_ne hdisj.cs_sv hv h0_lt_X; omega),
              hfr_m2 _ (by have := disjRange_ne hdisj.cur_sv hv h0_lt_X; omega)]
          exact hinv.cur_inv v hv
        · intro j hj
          have hle : ul.length ≤ X.card := by
            rw [hinv.ul_len]; exact Finset.card_le_card (Finset.Subset.trans hinv.used_sub hVX)
          rw [hfr_m2 _ (by have := disjRange_ne hdisj.sv_ul h0_lt_X (by omega : j < X.card); omega)]
          exact hinv.ul_at j hj
        · exact hinv.chain.congr (fun k hk1 hk2 => hfr_m2 k (by
            by_cases hlt : k < cfg.heapIn
            · intro h; subst h; exact hacc_disj _ ⟨hk1, hlt⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
            · have hhi : heapPtr ≤ cfg.heapIn + 5 * X.card := by
                have := hinv.heap_hi; have := Finset.card_le_card (Finset.Subset.trans hinv.used_sub hVX); omega
              have := disjRange_ne hdisj.sv_hp h0_lt_X (by omega : k - cfg.heapIn < 5 * X.card); omega))
        · intro a ha
          rw [hfr_m2 a (fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))]
          exact hinv.frame_out a ha
        · intro a ha
          rw [hfr_m2 a (by rcases hdisj.sv_co with h | h <;> omega)]
          exact hinv.frame_cfgOut a ha
        · intro v hv
          rw [hfr_m2 _ (by have := disjRange_ne hdisj.cs_sv hv h0_lt_X; omega)]
          exact hinv.stamp_cur v hv
        · intro v hv
          rw [hfr_m2 _ (by have := disjRange_ne hdisj.us_sv hv h0_lt_X; omega)]
          exact hinv.stamp_used v hv
        · intro v hv
          rw [hfr_m2 _ (by have := disjRange_ne hdisj.ds_sv hv h0_lt_X; omega)]
          exact hinv.stamp_dead v hv
      have hstk2 : DfsStackAt mem2 X V dist cfg ds s s 0 [] := by
        refine ⟨Nat.zero_le _, rfl, rfl, ?_, fun k hk => by simp at hk, ?_⟩
        · intro k hk
          have hk0 : k = 0 := by simp [stackVerts] at hk; omega
          subst hk0; simp [mem2, stackVerts]
        · intro k hk
          have hk0 : k = 0 := by simp [stackVerts] at hk; omega
          subst hk0; exact ⟨hsV, hsu, hsD, hsDist⟩
      have hregs2 : DfsRegsAt st2.regs cfg cfgAddr heapPtr pathsHead pathsTail ds.used.card ds.paths.length :=
        fun k hk => by
          simp only [st2, st1, Function.update_of_ne (by omega : k ≠ 29),
            Function.update_of_ne (by omega : k ≠ 31), Function.update_of_ne (by omega : k ≠ 30),
            Function.update_of_ne (by omega : k ≠ 28)]
          exact hregs k hk
      obtain ⟨st3, c3, hrun3, hpost3, hc3⟩ :=
        dfsStepLoop_triple (p := p) hVX hadj_X hcsr hm2 hdisj hheap_lo hacc_disj hmask hstop hdist_mem
          (dfsPot V ds) fuel s s 0 [] ds ul heapPtr pathsHead pathsTail st2
          rfl hfuel hinv2 hstk2 hregs2 (by simp [st2, hst1_r28]) (by simp [st2]) (by simp [st2]) (by simp [st2]) ω
      rcases hpost3 with ⟨hp3, ph3, pt3, ul3, hinv3, hregs3, hr3_27, _⟩
      have hst3_r27 : st3.regs 27 = srcIdx := by rw [hr3_27]; simp [st2, hst1_r27]
      set ds1 := dfsStep V T dist cfg.targetDepth s fuel s 0 [] { ds with cost := 0 }
      have hpot1 : dfsPot V ds1 < fuel := by
        have := dfsPot_dfsStep_le V T dist cfg.targetDepth s fuel s 0 [] { ds with cost := 0 }
        have heq : dfsPot V { ds with cost := 0 } = dfsPot V ds := rfl
        dsimp only [ds1]; omega
      set st4 : State := { st3 with regs := Function.update st3.regs 27 (srcIdx + 1) }
      have hinc : Runs w p ω (.assign 27 (.bin .add (.reg 27) (.const 1))) st3 .normal st4
          ((Expr.bin .add (.reg 27) (.const 1)).size + 1) := by
        refine runs_assign_iff.mpr ⟨srcIdx + 1, ?_, rfl, rfl, rfl⟩
        simp [Expr.eval, BinOp.eval, hst3_r27, show 1 < 2 ^ w by omega, show srcIdx + 1 < 2 ^ w by omega]
      have hregs4 : DfsRegsAt st4.regs cfg cfgAddr hp3 ph3 pt3 ds1.used.card ds1.paths.length :=
        fun k hk => by
          simp only [st4, Function.update_of_ne (by omega : k ≠ 27)]
          exact hregs3 k hk
      obtain ⟨st5, c5, hrun5, hpost5, hc5⟩ :=
        ih (srcIdx + 1) ds1 ul3 hp3 ph3 pt3 st4 (by omega) hpot1 hinv3 hregs4 (by simp [st4]) ω
      -- Stitch hrun2 + hrun3 + hinc into body
      rcases runs_seq_iff.mp hrun2 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
      · cases h
      rcases runs_seq_iff.mp hrb with ⟨_, _, _, h, _⟩ | ⟨sb, cb1, cb2, hrb1, hrb2, rfl⟩
      · cases h
      rcases runs_seq_iff.mp hrb2 with ⟨_, _, _, h, _⟩ | ⟨sc, cc1, cc2, hrc1, hrc2, rfl⟩
      · cases h
      have hbranch : Runs w p ω
          (seqStmts
            [ .store (.reg 15) (.reg 28)
            , .assign 30 (.const 0)
            , .assign 31 (.reg 28)
            , .assign 29 (.const 1)
            , dfsStepLoopStmt ])
          st1 .normal st3 (ca + (cb1 + (cc1 + (cc2 + c3 + 1) + 1) + 1) + 1) := by
        dsimp only [seqStmts]
        exact runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, hra,
          runs_seq_iff.mpr (Or.inr ⟨sb, cb1, _, hrb1,
            runs_seq_iff.mpr (Or.inr ⟨sc, cc1, _, hrc1,
              runs_seq_iff.mpr (Or.inr ⟨st2, cc2, _, hrc2, hrun3, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have hcond2 : Runs w p ω
          (.cond (.bin .eq (.load (.bin .add (.reg 13) (.reg 28))) (.reg 18))
            .nop
            (.cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 28))) (.reg 18))
              .nop
              (seqStmts
                [ .store (.reg 15) (.reg 28)
                , .assign 30 (.const 0)
                , .assign 31 (.reg 28)
                , .assign 29 (.const 1)
                , dfsStepLoopStmt ])))
          st1 .normal st3 _ :=
        runs_cond_iff.mpr ⟨0, _, hev1, by simpa using runs_cond_iff.mpr ⟨0, _, hev2, by simpa using hbranch, rfl⟩, rfl⟩
      have hbody : Runs w p ω _ st0 .normal st4 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload_s,
          runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hcond2, hinc, rfl⟩), rfl⟩)
      -- Relate model costs
      have hstep1 := dfsStep_cost_add V T dist cfg.targetDepth s fuel s 0 [] { ds with cost := 0 } 1
      have hds1_eq : dfsStep V T dist cfg.targetDepth s fuel s 0 [] { ds with cost := 1 } =
          { ds1 with cost := ds1.cost + 1 } := by
        rcases hstep1 with ⟨ha, hb, hc, hd, he⟩
        cases hA : dfsStep V T dist cfg.targetDepth s fuel s 0 [] { ds with cost := 1 }
        cases hB : ds1
        simp only [ds1, hA, hB] at ha hb hc hd he
        simp only [ha, hb, hc, hd, he]
      have hsrc_add := dfsSources_cost_add V T dist cfg.targetDepth fuel (srcs.drop (srcIdx + 1))
        { ds1 with cost := 0 } (ds1.cost + 1)
      set dsF1 := dfsSources V T dist cfg.targetDepth fuel (srcs.drop (srcIdx + 1)) { ds1 with cost := 0 }
      have hfinal_eq :
          dfsSources V T dist cfg.targetDepth fuel (srcs.drop srcIdx) { ds with cost := 0 } =
            { dsF1 with cost := dsF1.cost + (ds1.cost + 1) } := by
        rw [hdrop_cons]
        simp only [dfsSources, hsu, hsD, or_self, ↓reduceIte, Nat.zero_add, hds1_eq]
        rcases hsrc_add with ⟨ha, hb, hc, hd, he⟩
        cases hA : dfsSources V T dist cfg.targetDepth fuel (srcs.drop (srcIdx + 1)) { ds1 with cost := ds1.cost + 1 }
        cases hB : dsF1
        simp only [dsF1, hA, hB, Nat.zero_add] at ha hb hc hd he
        simp only [ha, hb, hc, hd, he]
      refine ⟨st5, _,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st4, _, c5, hguard, by omega, hbody, hrun5, rfl⟩)),
        ?_, ?_⟩
      · rw [hfinal_eq]
        rcases hpost5 with ⟨hp5, ph5, pt5, ul5, hinv5, hregs5⟩
        exact ⟨hp5, ph5, pt5, ul5, dfsStateAt_cost_irrel' hinv5 rfl rfl rfl rfl, hregs5⟩
      · rw [hfinal_eq]
        simp only [Expr.size] at hc2 hc3 hc5 ⊢; omega

/-! ## 3. Full Procedure Triple (`dfsBlock_triple`) and Contract (`dfsBlock_meetsContract`) -/

theorem dfsBlock_triple {w : ℕ} {p : Program}
    {X V S T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    {cfg : DfsCfg} {cfgAddr m2 heapLo : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {st0 : State}
    (hVX : V ⊆ X)
    (hSV : S ⊆ V)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcfg : DfsCfgAt st0.mem cfgAddr cfg)
    (hcsr : AdjCsrAt st0.mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : DfsDisj w X.card m2 cfg cfgAddr)
    (hheap_lo : heapLo ≤ cfg.heapIn)
    (hacc_disj : ∀ a, heapLo ≤ a ∧ a < cfg.heapIn → ¬ DfsWriteSet X.card cfg cfgAddr a)
    (hacc_chain : PathChainAt st0.mem X heapLo cfg.heapIn cfg.inHead cfg.inTail acc)
    (hmask : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hstop : ∀ v < X.card, st0.mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ T)
    (hdist_mem : ∀ v < X.card,
      (st0.mem (cfg.visStampAddr + v) = cfg.bfsGen ∧ dist (origOf X v) = some (st0.mem (cfg.distAddr + v))) ∨
      (st0.mem (cfg.visStampAddr + v) ≠ cfg.bfsGen ∧ dist (origOf X v) = none))
    (hdist_zero : ∀ s ∈ S, dist s = some 0)
    (hsrc_list : ListAt st0.mem cfg.srcPtr ((S.sort (· ≤ ·)).map (locOf X)))
    (hsrc_len : cfg.srcLen = S.card)
    (hcs0 : ∀ v < X.card, st0.mem (cfg.curStampAddr + v) ≠ cfg.dfsGen)
    (hus0 : ∀ v < X.card, st0.mem (cfg.usedStampAddr + v) ≠ cfg.dfsGen)
    (hds0 : ∀ v < X.card, st0.mem (cfg.deadStampAddr + v) ≠ cfg.dfsGen)
    (hr0 : st0.regs 0 = cfgAddr) :
    let res := dfsBlock adj V S T dist cfg.targetDepth
    Triple w p (fun st => st = st0) dfsBlockProc
      (retPost fun v st' =>
        v = res.used.card ∧
        DfsOutAt st'.mem X cfg cfgAddr heapLo acc res ∧
        (∀ v < X.card, st'.mem (cfg.curStampAddr + v) = st0.mem (cfg.curStampAddr + v) ∨
          st'.mem (cfg.curStampAddr + v) = cfg.dfsGen) ∧
        (∀ v < X.card, st'.mem (cfg.usedStampAddr + v) = st0.mem (cfg.usedStampAddr + v) ∨
          st'.mem (cfg.usedStampAddr + v) = cfg.dfsGen) ∧
        (∀ v < X.card, st'.mem (cfg.deadStampAddr + v) = st0.mem (cfg.deadStampAddr + v) ∨
          st'.mem (cfg.deadStampAddr + v) = cfg.dfsGen) ∧
        (∀ a, ¬ DfsWriteSet X.card cfg cfgAddr a → st'.mem a = st0.mem a))
      (fun _ => dfsProgCost (dfsBlock adj V S T dist cfg.targetDepth).cost) := by
  have hS_inter : S ∩ V = S := Finset.inter_eq_left.mpr hSV
  have hsrcs_len : cfg.srcLen = (S.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hsrc_len
  have hsrc_ok : ∀ s ∈ S.sort (· ≤ ·), s ∈ V ∧ dist s = some 0 := by
    intro s hs; have hsS : s ∈ S := (Finset.mem_sort (· ≤ ·)).mp hs
    exact ⟨hSV hsS, hdist_zero s hsS⟩
  have hw4 := hdisj.w4
  dsimp only
  wram_enter; subst st
  unfold dfsBlockProc; dsimp only [seqStmts]
  refine runs_seq_triple_le (dfsLoadCfg_triple (p := p) hcfg hr0 hdisj.w_cfg) rfl (fun st1 hst1 => ?_)
  rcases hst1 with ⟨hmem1, hregs1⟩
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st2 : State :=
    { mem := st1.mem
      regs := Function.update (Function.update (Function.update st1.regs 25 0) 26 0) 27 0
      pos := st1.pos }
  set init : DFSState := { used := ∅, dead := ∅, cursor := adj, paths := [], cost := 0 }
  have hinv2 : DfsStateAt st2.mem st0.mem X V adj cfg cfgAddr heapLo cfg.heapIn cfg.inHead cfg.inTail acc init [] := by
    refine ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.zero_le _, ?_, ?_, ?_,
      rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h (Finset.notMem_empty _),
      fun _ h => absurd h (by simp), le_rfl, by simp, ?_, fun _ _ => hmem1 ▸ rfl, fun _ _ => hmem1 ▸ rfl,
      fun _ _ => Or.inl (hmem1 ▸ rfl), fun _ _ => Or.inl (hmem1 ▸ rfl), fun _ _ => Or.inl (hmem1 ▸ rfl)⟩
    · intro v hv; simp [st2, hmem1, init, hus0 v hv]
    · intro v hv; simp [st2, hmem1, init, hds0 v hv]
    · intro v hv; exact ⟨fun _ => rfl, fun h => absurd (by simpa [st2, hmem1] using h) (hcs0 v hv)⟩
    · simpa [st2, hmem1, init] using hacc_chain
  have hregs2 : DfsRegsAt st2.regs cfg cfgAddr cfg.heapIn cfg.inHead cfg.inTail init.used.card init.paths.length := by
    intro r hr
    by_cases h25 : r = 25
    · subst h25; simp [st2, init]
    · by_cases h26 : r = 26
      · subst h26; simp [st2, init]
      · have hne27 : r ≠ 27 := by omega
        simp only [st2, Function.update_of_ne hne27, Function.update_of_ne h26, Function.update_of_ne h25]
        have := hregs1 r (by omega)
        interval_cases r <;> omega
  obtain ⟨st3, c3, hrun3, hpost3, hc3⟩ :=
    dfsSourcesLoop_triple (p := p) (fuel := dfsPot V init + 1) (srcs := S.sort (· ≤ ·))
      hVX hadj_X hcsr hm2 hdisj hheap_lo hacc_disj hmask hstop hdist_mem hsrc_list hsrcs_len hsrc_ok
      (S.sort (· ≤ ·)).length 0 init [] cfg.heapIn cfg.inHead cfg.inTail st2
      (Nat.zero_add _) (Nat.lt_succ_self _) hinv2 hregs2 (by simp [st2]) ω
  rcases hpost3 with ⟨hp3, ph3, pt3, ul3, hinv3, hregs3⟩
  have hres_eq : dfsBlock adj V S T dist cfg.targetDepth =
      dfsSources V T dist cfg.targetDepth (dfsPot V init + 1) ((S.sort (· ≤ ·)).drop 0) { init with cost := 0 } := by
    simp [dfsBlock, hS_inter, init]
  have hr3_0 : st3.regs 0 = cfgAddr := hregs3 0 (by decide)
  have hwr := dfsWriteRet_triple (p := p) (st0 := st3) hr3_0 hdisj.w_cfg st3 ω rfl
  obtain ⟨o4, st4, c4, hrun4, hpost4, hc4⟩ := hwr
  cases o4 with
  | normal => exact hpost4.elim
  | returned v =>
    rcases hpost4 with ⟨hv, h24, h25, h26, h27, h28, hfr4⟩
    refine ⟨.returned v, st4, c3 + c4 + 1, runs_seq_iff.mpr (Or.inr ⟨st3, c3, c4, hrun3, hrun4, rfl⟩), ?_, ?_⟩
    · dsimp only [retPost]
      rw [hres_eq]
      set res := dfsSources V T dist cfg.targetDepth (dfsPot V init + 1) ((S.sort (· ≤ ·)).drop 0) { init with cost := 0 }
      have hr3_22 : st3.regs 22 = hp3 := hregs3 22 (by decide)
      have hr3_23 : st3.regs 23 = ph3 := hregs3 23 (by decide)
      have hr3_24 : st3.regs 24 = pt3 := hregs3 24 (by decide)
      have hr3_25 : st3.regs 25 = res.used.card := hregs3 25 (by decide)
      have hr3_26 : st3.regs 26 = res.paths.length := hregs3 26 (by decide)
      refine ⟨hv.trans hr3_25, ⟨h24.trans hr3_25, h25.trans hr3_26, by rw [h28, hr3_22]; exact hinv3.heap_lo,
        by rw [h28, hr3_22]; exact hinv3.heap_hi, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · refine ⟨ul3, hinv3.ul_len, hinv3.ul_nd, hinv3.ul_sub, hinv3.ul_cov, ?_⟩
        intro j hj
        have hle : ul3.length ≤ X.card := by
          rw [hinv3.ul_len]; exact Finset.card_le_card (Finset.Subset.trans hinv3.used_sub hVX)
        rw [hfr4 _ (by rcases hdisj.ul_co with h | h <;> omega)]
        exact hinv3.ul_at j hj
      · intro u hu
        rw [hfr4 _ (by rcases hdisj.us_co with h | h <;> omega)]
        exact hinv3.used_stamp u hu
      · rw [h26, h27, h28, hr3_22, hr3_23, hr3_24]
        exact hinv3.chain.congr (fun k hk1 hk2 => hfr4 k (by
          by_cases hlt : k < cfg.heapIn
          · by_contra hc; push Not at hc
            exact hacc_disj k ⟨hk1, hlt⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))))
          · have hhi : hp3 ≤ cfg.heapIn + 5 * X.card := by
              have := hinv3.heap_hi; have := Finset.card_le_card (Finset.Subset.trans hinv3.used_sub hVX); omega
            rcases hdisj.co_hp with h | h <;> omega))
      · intro u hu
        rw [hfr4 _ (by rcases hdisj.cs_co with h | h <;> omega)]
        exact hinv3.stamp_cur u hu
      · intro u hu
        rw [hfr4 _ (by rcases hdisj.us_co with h | h <;> omega)]
        exact hinv3.stamp_used u hu
      · intro u hu
        rw [hfr4 _ (by rcases hdisj.ds_co with h | h <;> omega)]
        exact hinv3.stamp_dead u hu
      · intro a ha
        have hne : a < cfgAddr + 24 ∨ cfgAddr + 29 ≤ a := by
          by_contra hc; push Not at hc
          exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))))
        rw [hfr4 a hne]; exact hinv3.frame_out a ha
    · rw [hres_eq]
      simp only [dfsProgCost, Expr.size] at hc3 hc4 ⊢; omega

/-- Contract for `dfsBlockProc` on argument `[cfgAddr]`. -/
@[expose] def dfsBlockContract (w : ℕ) (X V S T : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) (dist : ℕ → Option ℕ)
    (cfg : DfsCfg) (m2 heapLo : ℕ) (acc : List ((ℕ × ℕ) × List ℕ)) : Contract where
  pre args mem :=
    args.length = 1 ∧
    let cfgAddr := args.getD 0 0
    V ⊆ X ∧
    S ⊆ V ∧
    (∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X) ∧
    DfsCfgAt mem cfgAddr cfg ∧
    AdjCsrAt mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X adj ∧
    adjCsrOff X adj X.card ≤ m2 ∧
    DfsDisj w X.card m2 cfg cfgAddr ∧
    heapLo ≤ cfg.heapIn ∧
    (∀ a, heapLo ≤ a ∧ a < cfg.heapIn → ¬ DfsWriteSet X.card cfg cfgAddr a) ∧
    PathChainAt mem X heapLo cfg.heapIn cfg.inHead cfg.inTail acc ∧
    (∀ v < X.card, mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V) ∧
    (∀ v < X.card, mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ T) ∧
    (∀ v < X.card,
      (mem (cfg.visStampAddr + v) = cfg.bfsGen ∧ dist (origOf X v) = some (mem (cfg.distAddr + v))) ∨
      (mem (cfg.visStampAddr + v) ≠ cfg.bfsGen ∧ dist (origOf X v) = none)) ∧
    (∀ s ∈ S, dist s = some 0) ∧
    ListAt mem cfg.srcPtr ((S.sort (· ≤ ·)).map (locOf X)) ∧
    cfg.srcLen = S.card ∧
    (∀ v < X.card, mem (cfg.curStampAddr + v) ≠ cfg.dfsGen) ∧
    (∀ v < X.card, mem (cfg.usedStampAddr + v) ≠ cfg.dfsGen) ∧
    (∀ v < X.card, mem (cfg.deadStampAddr + v) ≠ cfg.dfsGen)
  post args mem v mem' :=
    let cfgAddr := args.getD 0 0
    let res := dfsBlock adj V S T dist cfg.targetDepth
    v = res.used.card ∧
    DfsOutAt mem' X cfg cfgAddr heapLo acc res ∧
    (∀ u < X.card, mem' (cfg.curStampAddr + u) = mem (cfg.curStampAddr + u) ∨
      mem' (cfg.curStampAddr + u) = cfg.dfsGen) ∧
    (∀ u < X.card, mem' (cfg.usedStampAddr + u) = mem (cfg.usedStampAddr + u) ∨
      mem' (cfg.usedStampAddr + u) = cfg.dfsGen) ∧
    (∀ u < X.card, mem' (cfg.deadStampAddr + u) = mem (cfg.deadStampAddr + u) ∨
      mem' (cfg.deadStampAddr + u) = cfg.dfsGen) ∧
    (∀ a, ¬ DfsWriteSet X.card cfg cfgAddr a → mem' a = mem a)
  cost _ _ := dfsProgCost (dfsBlock adj V S T dist cfg.targetDepth).cost

/-- `dfsBlockProc` meets `dfsBlockContract` deterministically. -/
theorem dfsBlock_meetsContract {w : ℕ} {p : Program} {idx : ℕ}
    (hproc : p.procs[idx]? = some dfsBlockProc)
    (X V S T : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) (dist : ℕ → Option ℕ)
    (cfg : DfsCfg) (m2 heapLo : ℕ) (acc : List ((ℕ × ℕ) × List ℕ)) :
    MeetsContract w p idx (dfsBlockContract w X V S T adj dist cfg m2 heapLo acc) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨hlen, hVX, hSV, hadj_X, hcfg, hcsr, hm2, hdisj, hheap_lo, hacc_disj, hacc_chain,
    hmask, hstop, hdist_mem, hdist_zero, hsrc_list, hsrc_len, hcs0, hus0, hds0⟩
  have htr := dfsBlock_triple (w := w) (p := p) (st0 := startState args mem pos)
    hVX hSV hadj_X hcfg hcsr hm2 hdisj hheap_lo hacc_disj hacc_chain hmask hstop hdist_mem
    hdist_zero hsrc_list hsrc_len hcs0 hus0 hds0 rfl
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := htr (startState args mem pos) ω rfl
  cases o with
  | normal => exact hpost.elim
  | returned v =>
    exact ⟨dfsBlockProc, hproc, .returned v, st', c, hrun, hpost, hc⟩

end MinCostFlow.ExpanderDecomp
