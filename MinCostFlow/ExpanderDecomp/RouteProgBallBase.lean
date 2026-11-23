module

public import MinCostFlow.ExpanderDecomp.RouteProgBallSpec

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer Ball Growing Sub-Triples (`RouteProgBallBase`)

Verifies the helper sub-statements of `growBallProc`: `ballLoadCfg_triple`, `ballCountInc_triple`,
`ballAddLayer_triple`, and `ballWriteRet_triple`. Pure lemmas, configuration layout, and
statements live in `RouteProgBallSpec.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 4. Helper Sub-Triples -/

private lemma ballLoadCfg_step {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {i cfgAddr : ℕ} {f mem0 : ℕ → ℕ} {st : State} {rest : Stmt} {P : Outcome → State → Prop} {c1 : ℕ}
    (hw : cfgAddr + 24 < 2 ^ w) (hi : i ≤ 17)
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

theorem ballLoadCfg_triple {w : ℕ} {p : Program}
    {cfg : BallCfg} {cfgAddr : ℕ} {st0 : State}
    (hcfg : BallCfgAt st0.mem cfgAddr cfg)
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 24 < 2 ^ w) :
    Triple w p (fun st => st = st0) ballLoadCfgStmt
      (normalPost fun st1 =>
        st1.mem = st0.mem ∧
        ∀ r ≤ 18, st1.regs r =
          match r with
          | 0 => cfgAddr | 1 => cfg.bfsCfgAddr | 2 => cfg.offAddr | 3 => cfg.nbAddr
          | 4 => cfg.maskArrAddr | 5 => cfg.maskBadVal
          | 6 => cfg.layerOffS | 7 => cfg.layerDataS | 8 => cfg.layerOffT | 9 => cfg.layerDataT
          | 10 => cfg.sPtr | 11 => cfg.sLen | 12 => cfg.tPtr | 13 => cfg.tLen
          | 14 => cfg.ballStampAddr | 15 => cfg.ballListAddr
          | 16 => cfg.bfsGenIn | 17 => cfg.ballGenIn | _ => cfg.b)
      (fun _ => 135) := by
  let f : ℕ → ℕ := fun r =>
    match r with
    | 0 => cfgAddr | 1 => cfg.bfsCfgAddr | 2 => cfg.offAddr | 3 => cfg.nbAddr
    | 4 => cfg.maskArrAddr | 5 => cfg.maskBadVal
    | 6 => cfg.layerOffS | 7 => cfg.layerDataS | 8 => cfg.layerOffT | 9 => cfg.layerDataT
    | 10 => cfg.sPtr | 11 => cfg.sLen | 12 => cfg.tPtr | 13 => cfg.tLen
    | 14 => cfg.ballStampAddr | 15 => cfg.ballListAddr
    | 16 => cfg.bfsGenIn | 17 => cfg.ballGenIn | _ => cfg.b
  rcases hcfg with ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩
  wram_enter; subst st; dsimp only; simp only [Nat.zero_add]; unfold ballLoadCfgStmt; dsimp only [seqStmts]
  have hr0' : ∀ r ≤ 0, st0.regs r = f r := fun r hr => by
    have : r = 0 := by omega
    subst this; exact hr0
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) rfl hr0' rfl c0 (c1 := 128) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c1 (c1 := 121) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c2 (c1 := 114) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c3 (c1 := 107) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c4 (c1 := 100) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c5 (c1 := 93) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c6 (c1 := 86) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c7 (c1 := 79) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c8 (c1 := 72) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c9 (c1 := 65) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c10 (c1 := 58) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c11 (c1 := 51) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c12 (c1 := 44) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c13 (c1 := 37) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c14 (c1 := 30) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c15 (c1 := 23) (fun s hm hr => ?_)
  refine ballLoadCfg_step (f := f) hw_cfg (by decide) hm hr rfl c16 (c1 := 16) (fun s hm hr => ?_)
  have hs0 : s.regs 0 = cfgAddr := hr 0 (by decide)
  have hev18 : (Expr.load (.bin .add (.reg 0) (.const 17))).eval w s = some (f 18) := by
    simp [Expr.eval, BinOp.eval, hs0, show 17 < 2 ^ w by omega, show cfgAddr + 17 < 2 ^ w by omega,
      hm, c17, f]
  refine ⟨.normal, { s with regs := Function.update s.regs 18 (f 18) }, _,
    runs_assign_iff.mpr ⟨f 18, hev18, rfl, rfl, rfl⟩, ⟨hm, fun r hr' => ?_⟩, ?_⟩
  · dsimp only
    by_cases h : r = 18
    · subst h; exact Function.update_self _ _ _
    · rw [Function.update_of_ne h]; exact hr r (by omega)
  · simp only [Expr.size]; omega

theorem ballCountInc_triple {w : ℕ} {p : Program}
    {X V cur : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {u : ℕ}
    {cfg : BallCfg} {m2 ballGen : ℕ} {st0 : State}
    (huX : u ∈ X)
    (hadj_X : ∀ x ∈ X, ∀ e ∈ adj x, e.1 ∈ X)
    (hcsr : NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hmask : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hbs : ∀ v < X.card, st0.mem (cfg.ballStampAddr + v) = ballGen ↔ origOf X v ∈ cur)
    (hw_nb : cfg.nbAddr + m2 + 5 < 2 ^ w)
    (hw_mask : cfg.maskArrAddr + X.card + 5 < 2 ^ w)
    (hw_bs : cfg.ballStampAddr + X.card + 5 < 2 ^ w)
    (hw_m2 : m2 + 5 < 2 ^ w)
    (hw_nX : X.card + 5 < 2 ^ w)
    (hw_mb : cfg.maskBadVal < 2 ^ w)
    (hw_bg : ballGen < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hr3 : st0.regs 3 = cfg.nbAddr)
    (hr4 : st0.regs 4 = cfg.maskArrAddr)
    (hr5 : st0.regs 5 = cfg.maskBadVal)
    (hr14 : st0.regs 14 = cfg.ballStampAddr)
    (hr27 : st0.regs 27 = ballGen)
    (hr33 : st0.regs 33 = locOf X u)
    (hr34 : st0.regs 34 = adjCsrOff X adj (locOf X u))
    (hr35 : st0.regs 35 = adjCsrOff X adj (locOf X u + 1)) :
    let r := countIncidence V cur u (adj u)
    Triple w p (fun st => st = st0) ballCountIncStmt
      (normalPost fun st' =>
        st'.mem = st0.mem ∧
        (∀ k ≤ 33, st'.regs k = st0.regs k) ∧
        st'.regs 35 = st0.regs 35 ∧
        st'.regs 36 = r.1 ∧
        st'.regs 37 = r.2.1)
      (fun _ => 50 * (adj u).length + 20) := by
  have hu_loc_lt : locOf X u < X.card := locOf_lt huX
  have hbase_succ : adjCsrOff X adj (locOf X u + 1) =
      adjCsrOff X adj (locOf X u) + (adj u).length := by
    rw [adjCsrOff_succ, origOf_locOf huX]
  have hend_le_m2 : adjCsrOff X adj (locOf X u + 1) ≤ m2 :=
    le_trans (adjCsrOff_mono X adj (by omega)) hm2
  have hci := countIncidence_spec_pub V cur u (adj u)
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  dsimp only
  wram_enter; subst st
  unfold ballCountIncStmt; dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set base := adjCsrOff X adj (locOf X u)
  set eEnd := adjCsrOff X adj (locOf X u + 1)
  set st1 : State :=
    { mem := st0.mem
      regs := Function.update (Function.update st0.regs 36 0) 37 0
      pos := st0.pos }
  have hloop :
      Triple w p
        (fun st =>
          st.mem = st0.mem ∧
          (∀ k ≤ 33, st.regs k = st0.regs k) ∧
          st.regs 35 = eEnd ∧
          base ≤ st.regs 34 ∧ st.regs 34 ≤ eEnd ∧
          st.regs 36 = (((adj u).take (st.regs 34 - base)).filter fun q => decide (q.1 ∈ cur)).length ∧
          st.regs 37 = (((adj u).take (st.regs 34 - base)).filter fun q =>
            decide (q.1 ∈ V) && decide (q.1 ∉ insert u cur)).length)
        (.loop (.bin .lt (.reg 34) (.reg 35))
          (seqStmts
            [ .assign 38 (.load (.bin .add (.reg 3) (.reg 34)))
            , .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 38))) (.reg 27))
                (.assign 36 (.bin .add (.reg 36) (.const 1)))
                (.cond (.bin .eq (.reg 38) (.reg 33))
                  .nop
                  (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                    .nop
                    (.assign 37 (.bin .add (.reg 37) (.const 1)))))
            , .assign 34 (.bin .add (.reg 34) (.const 1)) ]))
        (normalPost fun st =>
          st.mem = st0.mem ∧
          (∀ k ≤ 33, st.regs k = st0.regs k) ∧
          st.regs 35 = st0.regs 35 ∧
          st.regs 36 = (countIncidence V cur u (adj u)).1 ∧
          st.regs 37 = (countIncidence V cur u (adj u)).2.1)
        (fun st => ((Expr.bin .lt (.reg 34) (.reg 35)).size + 44 + 1) * (eEnd - st.regs 34) +
          (Expr.bin .lt (.reg 34) (.reg 35)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => eEnd - st.regs 34)
      (condVal := fun st => if st.regs 34 < eEnd then 1 else 0)
      (bodyBound := 44) ?_ ?_ ?_
    · intro st ⟨_, _, h35, _, _, _, _⟩
      eval_expr
    · intro st ⟨hm, hrr, h35, hge, hle, h36, h37⟩ hv
      have heq : st.regs 34 = eEnd := by split_ifs at hv; omega
      have hdiff : st.regs 34 - base = (adj u).length := by omega
      rw [hdiff, List.take_length] at h36 h37
      exact ⟨hm, hrr, h35.trans hr35.symm, h36.trans hci.1.symm, h37.trans hci.2.1.symm⟩
    · intro stL ⟨hm, hrr, h35, hge, hle, h36, h37⟩ hv
      have h34_lt : stL.regs 34 < eEnd := by split_ifs at hv <;> omega
      set j := stL.regs 34 - base
      have hj_lt : j < (adj u).length := by omega
      have hj_lt_orig : j < (adj (origOf X (locOf X u))).length := by rwa [origOf_locOf huX]
      set pe := (adj u)[j]'hj_lt
      have hpe_mem : pe ∈ adj u := List.getElem_mem hj_lt
      have hwX : pe.1 ∈ X := hadj_X u huX pe hpe_mem
      have hw_loc_lt : locOf X pe.1 < X.card := locOf_lt hwX
      have hnb_mem : stL.mem (cfg.nbAddr + stL.regs 34) = locOf X pe.1 := by
        rw [hm, show cfg.nbAddr + stL.regs 34 = cfg.nbAddr + adjCsrOff X adj (locOf X u) + j by omega]
        have h2 := hcsr.2 (locOf X u) hu_loc_lt j hj_lt_orig
        have heq_pe : ((adj (origOf X (locOf X u)))[j]'hj_lt_orig).1 = pe.1 := by
          congr 1; simp only [pe, origOf_locOf huX]
        rwa [heq_pe] at h2
      have h3 : stL.regs 3 = cfg.nbAddr := (hrr 3 (by decide)).trans hr3
      have h4 : stL.regs 4 = cfg.maskArrAddr := (hrr 4 (by decide)).trans hr4
      have h5 : stL.regs 5 = cfg.maskBadVal := (hrr 5 (by decide)).trans hr5
      have h14 : stL.regs 14 = cfg.ballStampAddr := (hrr 14 (by decide)).trans hr14
      have h27 : stL.regs 27 = ballGen := (hrr 27 (by decide)).trans hr27
      have h33 : stL.regs 33 = locOf X u := (hrr 33 (by decide)).trans hr33
      have h36_le : stL.regs 36 ≤ j := by rw [h36]; exact (List.length_filter_le _ _).trans (by simp)
      have h37_le : stL.regs 37 ≤ j := by rw [h37]; exact (List.length_filter_le _ _).trans (by simp)
      have htake_succ : (adj u).take (j + 1) = (adj u).take j ++ [pe] :=
        List.take_succ_eq_append_getElem hj_lt
      wram_enter; subst st; dsimp only [seqStmts]
      refine runs_seq_assign_le (v := locOf X pe.1) (by rw [← hnb_mem]; eval_expr) ?_
      set stA : State := { stL with regs := Function.update stL.regs 38 (locOf X pe.1) }
      -- Evaluate the outer cond + inner conds into stB (regs updated at 36 or 37, mem unchanged)
      set inInc : ℕ := if pe.1 ∈ cur then 1 else 0
      set outInc : ℕ := if pe.1 ∈ V ∧ pe.1 ∉ insert u cur then 1 else 0
      have hcond_step : ∃ stB cB,
          Runs w p ω
            (.cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 38))) (.reg 27))
              (.assign 36 (.bin .add (.reg 36) (.const 1)))
              (.cond (.bin .eq (.reg 38) (.reg 33))
                .nop
                (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                  .nop
                  (.assign 37 (.bin .add (.reg 37) (.const 1))))))
            stA .normal stB cB ∧
          stB.mem = st0.mem ∧
          (∀ k ≤ 35, stB.regs k = stL.regs k) ∧
          stB.regs 36 = stL.regs 36 + inInc ∧
          stB.regs 37 = stL.regs 37 + outInc ∧
          cB ≤ 30 := by
        by_cases hcur : pe.1 ∈ cur
        · have hst_eq : st0.mem (cfg.ballStampAddr + locOf X pe.1) = ballGen :=
            (hbs (locOf X pe.1) hw_loc_lt).mpr (by rwa [origOf_locOf hwX])
          have hev1 : (Expr.bin .eq (.load (.bin .add (.reg 14) (.reg 38))) (.reg 27)).eval w stA = some 1 := by
            simp [Expr.eval, BinOp.eval, stA, h14, h27, hm, hst_eq, hw_ne,
              show cfg.ballStampAddr + locOf X pe.1 < 2 ^ w by omega]
          have ha : Runs w p ω (.assign 36 (.bin .add (.reg 36) (.const 1))) stA .normal
              { stA with regs := Function.update stA.regs 36 (stL.regs 36 + 1) } 4 :=
            runs_assign_iff.mpr ⟨stL.regs 36 + 1,
              by simp [Expr.eval, BinOp.eval, stA, show 1 < 2 ^ w by omega, show stL.regs 36 + 1 < 2 ^ w by omega],
              rfl, rfl, rfl⟩
          refine ⟨{ stA with regs := Function.update stA.regs 36 (stL.regs 36 + 1) }, _,
            runs_cond_iff.mpr ⟨1, 4, hev1, by simpa using ha, rfl⟩,
            hm, fun k hk => by simp [stA, Function.update_of_ne (by omega : k ≠ 36),
              Function.update_of_ne (by omega : k ≠ 38)],
            by simp [stA, inInc, hcur],
            by simp [stA, outInc, Finset.mem_insert, hcur],
            by simp [Expr.size]⟩
        · have hst_ne : st0.mem (cfg.ballStampAddr + locOf X pe.1) ≠ ballGen := by
            intro h; exact hcur (by simpa [origOf_locOf hwX] using (hbs (locOf X pe.1) hw_loc_lt).mp h)
          have hev1 : (Expr.bin .eq (.load (.bin .add (.reg 14) (.reg 38))) (.reg 27)).eval w stA = some 0 := by
            simp [Expr.eval, BinOp.eval, stA, h14, h27, hm, hst_ne,
              show cfg.ballStampAddr + locOf X pe.1 < 2 ^ w by omega]
          by_cases hwu : pe.1 = u
          · have hev2 : (Expr.bin .eq (.reg 38) (.reg 33)).eval w stA = some 1 := by
              simp [Expr.eval, BinOp.eval, stA, h33, hwu, hw_ne]
            have hr2 : Runs w p ω
                (.cond (.bin .eq (.reg 38) (.reg 33))
                  .nop
                  (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                    .nop
                    (.assign 37 (.bin .add (.reg 37) (.const 1)))))
                stA .normal stA ((Expr.bin .eq (.reg 38) (.reg 33)).size + 1 + 1) :=
              runs_cond_iff.mpr ⟨1, 1, hev2, by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), rfl⟩
            refine ⟨stA, _, runs_cond_iff.mpr ⟨0, _, hev1, by simpa using hr2, rfl⟩,
              hm, fun k hk => by simp [stA, Function.update_of_ne (by omega : k ≠ 38)],
              by simp [stA, inInc, hcur],
              by simp [stA, outInc, Finset.mem_insert, hwu],
              by simp [Expr.size]⟩
          · have hloc_ne : locOf X pe.1 ≠ locOf X u := fun h => hwu (by rw [← origOf_locOf hwX, h, origOf_locOf huX])
            have hev2 : (Expr.bin .eq (.reg 38) (.reg 33)).eval w stA = some 0 := by
              simp [Expr.eval, BinOp.eval, stA, h33, hloc_ne]
            by_cases hwV : pe.1 ∈ V
            · have hm_ne : st0.mem (cfg.maskArrAddr + locOf X pe.1) ≠ cfg.maskBadVal :=
                (hmask (locOf X pe.1) hw_loc_lt).mpr (by rwa [origOf_locOf hwX])
              have hev3 : (Expr.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5)).eval w stA = some 0 := by
                simp [Expr.eval, BinOp.eval, stA, h4, h5, hm, hm_ne,
                  show cfg.maskArrAddr + locOf X pe.1 < 2 ^ w by omega]
              have ha : Runs w p ω (.assign 37 (.bin .add (.reg 37) (.const 1))) stA .normal
                  { stA with regs := Function.update stA.regs 37 (stL.regs 37 + 1) } 4 :=
                runs_assign_iff.mpr ⟨stL.regs 37 + 1,
                  by simp [Expr.eval, BinOp.eval, stA, show 1 < 2 ^ w by omega, show stL.regs 37 + 1 < 2 ^ w by omega],
                  rfl, rfl, rfl⟩
              have hr3 : Runs w p ω
                  (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                    .nop (.assign 37 (.bin .add (.reg 37) (.const 1))))
                  stA .normal { stA with regs := Function.update stA.regs 37 (stL.regs 37 + 1) } _ :=
                runs_cond_iff.mpr ⟨0, 4, hev3, by simpa using ha, rfl⟩
              have hr2 : Runs w p ω
                  (.cond (.bin .eq (.reg 38) (.reg 33))
                    .nop
                    (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                      .nop (.assign 37 (.bin .add (.reg 37) (.const 1)))))
                  stA .normal { stA with regs := Function.update stA.regs 37 (stL.regs 37 + 1) } _ :=
                runs_cond_iff.mpr ⟨0, _, hev2, by simpa using hr3, rfl⟩
              refine ⟨{ stA with regs := Function.update stA.regs 37 (stL.regs 37 + 1) }, _,
                runs_cond_iff.mpr ⟨0, _, hev1, by simpa using hr2, rfl⟩,
                hm, fun k hk => by simp [stA, Function.update_of_ne (by omega : k ≠ 37),
                  Function.update_of_ne (by omega : k ≠ 38)],
                by simp [stA, inInc, hcur],
                by simp [stA, outInc, Finset.mem_insert, hwV, hwu, hcur],
                by simp [Expr.size]⟩
            · have hm_eq : st0.mem (cfg.maskArrAddr + locOf X pe.1) = cfg.maskBadVal := by
                by_contra h; exact hwV (by simpa [origOf_locOf hwX] using (hmask (locOf X pe.1) hw_loc_lt).mp h)
              have hev3 : (Expr.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5)).eval w stA = some 1 := by
                simp [Expr.eval, BinOp.eval, stA, h4, h5, hm, hm_eq, hw_ne,
                  show cfg.maskArrAddr + locOf X pe.1 < 2 ^ w by omega]
              have hr3 : Runs w p ω
                  (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                    .nop (.assign 37 (.bin .add (.reg 37) (.const 1))))
                  stA .normal stA _ :=
                runs_cond_iff.mpr ⟨1, 1, hev3, by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), rfl⟩
              have hr2 : Runs w p ω
                  (.cond (.bin .eq (.reg 38) (.reg 33))
                    .nop
                    (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                      .nop (.assign 37 (.bin .add (.reg 37) (.const 1)))))
                  stA .normal stA _ :=
                runs_cond_iff.mpr ⟨0, _, hev2, by simpa using hr3, rfl⟩
              refine ⟨stA, _, runs_cond_iff.mpr ⟨0, _, hev1, by simpa using hr2, rfl⟩,
                hm, fun k hk => by simp [stA, Function.update_of_ne (by omega : k ≠ 38)],
                by simp [stA, inInc, hcur],
                by simp [stA, outInc, hwV],
                by simp [Expr.size]⟩
      rcases hcond_step with ⟨stB, cB, hrunB, hmB, hregsB, h36B, h37B, hcB⟩
      have h34B : stB.regs 34 = stL.regs 34 := hregsB 34 (by decide)
      have ha_inc : Runs w p ω (.assign 34 (.bin .add (.reg 34) (.const 1))) stB .normal
          { stB with regs := Function.update stB.regs 34 (stL.regs 34 + 1) } 4 :=
        runs_assign_iff.mpr ⟨stL.regs 34 + 1,
          by simp [Expr.eval, BinOp.eval, h34B, show 1 < 2 ^ w by omega, show stL.regs 34 + 1 < 2 ^ w by omega],
          rfl, rfl, rfl⟩
      refine ⟨.normal, { stB with regs := Function.update stB.regs 34 (stL.regs 34 + 1) },
        cB + 4 + 1, runs_seq_iff.mpr (Or.inr ⟨stB, cB, 4, hrunB, ha_inc, rfl⟩), ?_,
        by simp only [Expr.size]; omega⟩
      refine ⟨⟨hmB, fun k hk => by simp [Function.update_of_ne (by omega : k ≠ 34), hregsB k (by omega), hrr k hk],
        by simp [hregsB 35 (by decide), h35], by simp; omega, by simp; omega, ?_, ?_⟩, by simp; omega⟩
      · dsimp only
        rw [Function.update_self, Function.update_of_ne (by decide : (36 : ℕ) ≠ 34), h36B, h36]
        rw [show stL.regs 34 + 1 - base = j + 1 by omega, htake_succ, List.filter_append]
        by_cases hc : pe.1 ∈ cur <;> simp [inInc, hc]
      · dsimp only
        rw [Function.update_self, Function.update_of_ne (by decide : (37 : ℕ) ≠ 34), h37B, h37]
        rw [show stL.regs 34 + 1 - base = j + 1 by omega, htake_succ, List.filter_append]
        dsimp only [outInc]
        by_cases hv' : pe.1 ∈ V <;> by_cases hu' : pe.1 = u <;> by_cases hc' : pe.1 ∈ cur <;>
          simp [hv', hu', hc']
  obtain ⟨o, st', c, hrun, hpost, hc⟩ :=
    hloop st1 ω ⟨rfl, fun k hk => by simp [st1, Function.update_of_ne (by omega : k ≠ 37),
      Function.update_of_ne (by omega : k ≠ 36)],
      by simp [st1, hr35, eEnd], by simp [st1, hr34, base], by simp [st1, hr34, base, eEnd]; omega,
      by simp [st1, hr34, base], by simp [st1, hr34, base]⟩
  cases o with
  | returned _ => exact hpost.elim
  | normal =>
    refine ⟨.normal, st', c, hrun, hpost, ?_⟩
    simp only [Expr.size, st1, Function.update_of_ne (by decide : (34 : ℕ) ≠ 37),
      Function.update_of_ne (by decide : (34 : ℕ) ≠ 36), hr34] at hc ⊢
    omega

theorem ballAddLayer_triple {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {cfg : BallCfg} {m2 ballGen selData lo : ℕ} {L : List ℕ}
    (hVX : V ⊆ X)
    (hadj_X : ∀ x ∈ X, ∀ e ∈ adj x, e.1 ∈ X)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj_bs_bl : DisjRange cfg.ballStampAddr X.card cfg.ballListAddr X.card)
    (hdisj_bs_off : DisjRange cfg.ballStampAddr X.card cfg.offAddr (X.card + 1))
    (hdisj_bs_nb : DisjRange cfg.ballStampAddr X.card cfg.nbAddr m2)
    (hdisj_bs_mask : DisjRange cfg.ballStampAddr X.card cfg.maskArrAddr X.card)
    (hdisj_bs_data : DisjRange cfg.ballStampAddr X.card selData X.card)
    (hdisj_bl_off : DisjRange cfg.ballListAddr X.card cfg.offAddr (X.card + 1))
    (hdisj_bl_nb : DisjRange cfg.ballListAddr X.card cfg.nbAddr m2)
    (hdisj_bl_mask : DisjRange cfg.ballListAddr X.card cfg.maskArrAddr X.card)
    (hdisj_bl_data : DisjRange cfg.ballListAddr X.card selData X.card)
    (hw_off : cfg.offAddr + X.card + 5 < 2 ^ w)
    (hw_nb : cfg.nbAddr + m2 + 5 < 2 ^ w)
    (hw_mask : cfg.maskArrAddr + X.card + 5 < 2 ^ w)
    (hw_bs : cfg.ballStampAddr + X.card + 5 < 2 ^ w)
    (hw_bl : cfg.ballListAddr + X.card + 5 < 2 ^ w)
    (hw_data : selData + X.card + 5 < 2 ^ w)
    (hw_m2 : m2 + 5 < 2 ^ w)
    (hw_nX : X.card + 5 < 2 ^ w)
    (hw_mb : cfg.maskBadVal < 2 ^ w)
    (hw_bg : ballGen < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hL_len : lo + L.length ≤ X.card) :
    ∀ (remL : List ℕ) (idx : ℕ) (cur : Finset ℕ) (bd : ℕ) (bl : List ℕ) (st0 : State),
      idx + remL.length = lo + L.length →
      remL.Nodup →
      (∀ u ∈ remL, u ∈ V) →
      cur ⊆ V →
      Disjoint cur remL.toFinset →
      bd + ∑ v ∈ V \ cur, (adj v).length ≤ m2 →
      NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj →
      (∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V) →
      (∀ v < X.card, st0.mem (cfg.ballStampAddr + v) = ballGen ↔ origOf X v ∈ cur) →
      (∀ v < X.card, st0.mem (cfg.ballStampAddr + v) ≤ ballGen) →
      bl.length = cur.card →
      bl.Nodup →
      (∀ x ∈ bl, x < X.card ∧ origOf X x ∈ cur) →
      (∀ v ∈ cur, v ∈ X ∧ locOf X v ∈ bl) →
      ListAt st0.mem cfg.ballListAddr bl →
      ListAt st0.mem (selData + idx) (remL.map (locOf X)) →
      st0.regs 2 = cfg.offAddr →
      st0.regs 3 = cfg.nbAddr →
      st0.regs 4 = cfg.maskArrAddr →
      st0.regs 5 = cfg.maskBadVal →
      st0.regs 14 = cfg.ballStampAddr →
      st0.regs 15 = cfg.ballListAddr →
      st0.regs 25 = selData →
      st0.regs 27 = ballGen →
      st0.regs 28 = cur.card →
      st0.regs 29 = bd →
      st0.regs 31 = idx →
      st0.regs 32 = lo + L.length →
      ∀ ω, ∃ st' c,
        Runs w p ω ballAddLayerStmt st0 .normal st' c ∧
        (let a := addLayerToBall adj V remL cur bd 0
         (∀ k ≤ 30, k ≠ 28 → k ≠ 29 → st'.regs k = st0.regs k) ∧
         st'.regs 28 = a.1.card ∧
         st'.regs 29 = a.2.1 ∧
         a.1 = cur ∪ remL.toFinset ∧
         a.1 ⊆ V ∧
         a.2.1 + ∑ v ∈ V \ a.1, (adj v).length ≤ m2 ∧
         (∀ v < X.card, st'.mem (cfg.ballStampAddr + v) = ballGen ↔ origOf X v ∈ a.1) ∧
         (∀ v < X.card, st'.mem (cfg.ballStampAddr + v) ≤ ballGen) ∧
         (∃ bl' : List ℕ, bl'.length = a.1.card ∧ bl'.Nodup ∧
           (∀ x ∈ bl', x < X.card ∧ origOf X x ∈ a.1) ∧
           (∀ v ∈ a.1, v ∈ X ∧ locOf X v ∈ bl') ∧
           ListAt st'.mem cfg.ballListAddr bl') ∧
         (∀ addr,
           (addr < cfg.ballStampAddr ∨ cfg.ballStampAddr + X.card ≤ addr) →
           (addr < cfg.ballListAddr ∨ cfg.ballListAddr + X.card ≤ addr) →
           st'.mem addr = st0.mem addr)) ∧
        c ≤ 105 * (addLayerToBall adj V remL cur bd 0).2.2 + 5 := by
  intro remL
  induction remL with
  | nil =>
    intro idx cur bd bl st0 hidx _ _ hcurV _ hpot _ _ hbs hbs_le hbl_len hbl_nd hbl_sub hbl_cov
      hbl_at _ _ _ _ _ _ _ _ _ hr28 hr29 hr31 hr32 ω
    have hidx_eq : idx = lo + L.length := by simp at hidx; exact hidx
    have hev : (Expr.bin .lt (.reg 31) (.reg 32)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr31, hr32, hidx_eq]
    refine ⟨st0, (Expr.bin .lt (.reg 31) (.reg 32)).size + 1,
      runs_loop_iff.mpr (Or.inl ⟨hev, rfl, rfl, rfl⟩), ?_, by simp [addLayerToBall, Expr.size]⟩
    exact ⟨fun _ _ _ _ => rfl, hr28, hr29, by simp [addLayerToBall], hcurV, hpot, hbs, hbs_le,
      ⟨bl, hbl_len, hbl_nd, hbl_sub, hbl_cov, hbl_at⟩, fun _ _ _ => rfl⟩
  | cons u rest ih =>
    intro idx cur bd bl st0 hidx hnd hsubV hcurV hdisj_cur hpot hcsr hmask hbs hbs_le hbl_len
      hbl_nd hbl_sub hbl_cov hbl_at hdata hr2 hr3 hr4 hr5 hr14 hr15 hr25 hr27 hr28 hr29 hr31 hr32 ω
    have huV : u ∈ V := hsubV u List.mem_cons_self
    have huX : u ∈ X := hVX huV
    have hu_loc_lt : locOf X u < X.card := locOf_lt huX
    have hu_not_cur : u ∉ cur := Finset.disjoint_right.mp hdisj_cur (by simp)
    have hnd_cons := List.nodup_cons.mp hnd
    have hcur_le_X : cur.card ≤ X.card := Finset.card_le_card (Finset.Subset.trans hcurV hVX)
    have hcur_lt_X : cur.card < X.card := by
      have h1 : insert u cur ⊆ X := Finset.insert_subset huX (Finset.Subset.trans hcurV hVX)
      have h2 := Finset.card_le_card h1
      rw [Finset.card_insert_of_notMem hu_not_cur] at h2; omega
    have hidx_lt : idx < lo + L.length := by simp at hidx; omega
    have hev_guard : (Expr.bin .lt (.reg 31) (.reg 32)).eval w st0 = some 1 := by
      have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
      simp [Expr.eval, BinOp.eval, hr31, hr32, hidx_lt, hw_ne]
    -- Step 1: r33 := selData[idx], r34 := off[u], r35 := off[u+1]
    have hdata_u : st0.mem (selData + idx) = locOf X u := by
      have h0 := hdata 0 (by simp)
      simp only [Nat.add_zero, List.map_cons, List.getElem_cons_zero] at h0; exact h0
    have hoff_u : st0.mem (cfg.offAddr + locOf X u) = adjCsrOff X adj (locOf X u) :=
      hcsr.1 (locOf X u) (by omega)
    have hoff_u1 : st0.mem (cfg.offAddr + (locOf X u + 1)) = adjCsrOff X adj (locOf X u + 1) :=
      hcsr.1 (locOf X u + 1) (by omega)
    set st1 : State :=
      { mem := st0.mem
        regs := Function.update (Function.update (Function.update st0.regs 33 (locOf X u))
          34 (adjCsrOff X adj (locOf X u))) 35 (adjCsrOff X adj (locOf X u + 1))
        pos := st0.pos }
    have hpre1 : ∃ c1,
        Runs w p ω
          (seqStmts
            [ .assign 33 (.load (.bin .add (.reg 25) (.reg 31)))
            , .assign 34 (.load (.bin .add (.reg 2) (.reg 33)))
            , .assign 35 (.load (.bin .add (.reg 2) (.bin .add (.reg 33) (.const 1)))) ])
          st0 .normal st1 c1 ∧ c1 ≤ 20 := by
      have h0 : ∃ o s c,
          Runs w p ω
            (seqStmts
              [ .assign 33 (.load (.bin .add (.reg 25) (.reg 31)))
              , .assign 34 (.load (.bin .add (.reg 2) (.reg 33)))
              , .assign 35 (.load (.bin .add (.reg 2) (.bin .add (.reg 33) (.const 1)))) ])
            st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 20 := by
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := locOf X u) (by rw [← hdata_u]; eval_expr) ?_
        refine runs_seq_assign_le (v := adjCsrOff X adj (locOf X u)) (by rw [← hoff_u]; eval_expr) ?_
        refine runs_assign_le (v := adjCsrOff X adj (locOf X u + 1)) (by rw [← hoff_u1]; eval_expr)
          ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
      exact ⟨c1, hrun1, by omega⟩
    rcases hpre1 with ⟨c1, hrun1, hc1⟩
    -- Step 2: ballCountInc_triple
    obtain ⟨o2, st2, c2, hrun2, hpost2, hc2⟩ :=
      ballCountInc_triple (p := p) (st0 := st1) huX hadj_X hcsr hm2 hmask hbs
        hw_nb hw_mask hw_bs hw_m2 hw_nX hw_mb hw_bg hw4
        (by simp [st1, hr3]) (by simp [st1, hr4]) (by simp [st1, hr5]) (by simp [st1, hr14])
        (by simp [st1, hr27]) (by simp [st1]) (by simp [st1]) (by simp [st1]) st1 ω rfl
    cases o2 with
    | returned _ => exact hpost2.elim
    | normal =>
    rcases hpost2 with ⟨hmem2, hregs2, _, h2_36, h2_37⟩
    set rci := countIncidence V cur u (adj u)
    have hci_spec := countIncidence_spec_pub V cur u (adj u)
    have hpot_next := bd_pot_step (inCnt := rci.1) huV hu_not_cur hpot hci_spec.2.2.2.2
    set bd1 := bd + rci.2.1 - rci.1
    set cur1 := insert u cur
    set mem3 : ℕ → ℕ :=
      Function.update (Function.update st0.mem (cfg.ballStampAddr + locOf X u) ballGen)
        (cfg.ballListAddr + cur.card) (locOf X u)
    set st3 : State :=
      { mem := mem3
        regs := Function.update (Function.update (Function.update st2.regs 29 bd1)
          28 (cur.card + 1)) 31 (idx + 1)
        pos := st2.pos }
    have hpost3 : ∃ c3,
        Runs w p ω
          (seqStmts
            [ .assign 29 (.bin .sub (.bin .add (.reg 29) (.reg 37)) (.reg 36))
            , .store (.bin .add (.reg 14) (.reg 33)) (.reg 27)
            , .store (.bin .add (.reg 15) (.reg 28)) (.reg 33)
            , .assign 28 (.bin .add (.reg 28) (.const 1))
            , .assign 31 (.bin .add (.reg 31) (.const 1)) ])
          st2 .normal st3 c3 ∧ c3 ≤ 45 := by
      have h0 : ∃ o s c,
          Runs w p ω
            (seqStmts
              [ .assign 29 (.bin .sub (.bin .add (.reg 29) (.reg 37)) (.reg 36))
              , .store (.bin .add (.reg 14) (.reg 33)) (.reg 27)
              , .store (.bin .add (.reg 15) (.reg 28)) (.reg 33)
              , .assign 28 (.bin .add (.reg 28) (.const 1))
              , .assign 31 (.bin .add (.reg 31) (.const 1)) ])
            st2 o s c ∧ (o = .normal ∧ s = st3) ∧ 0 + c ≤ 45 := by
        dsimp only [seqStmts]
        have h2_14 : st2.regs 14 = cfg.ballStampAddr := by rw [hregs2 14 (by decide)]; simp [st1, hr14]
        have h2_15 : st2.regs 15 = cfg.ballListAddr := by rw [hregs2 15 (by decide)]; simp [st1, hr15]
        have h2_27 : st2.regs 27 = ballGen := by rw [hregs2 27 (by decide)]; simp [st1, hr27]
        have h2_28 : st2.regs 28 = cur.card := by rw [hregs2 28 (by decide)]; simp [st1, hr28]
        have h2_29 : st2.regs 29 = bd := by rw [hregs2 29 (by decide)]; simp [st1, hr29]
        have h2_31 : st2.regs 31 = idx := by rw [hregs2 31 (by decide)]; simp [st1, hr31]
        have h2_33 : st2.regs 33 = locOf X u := by rw [hregs2 33 (by decide)]; simp [st1]
        have hbd1_lt : bd + rci.2.1 < 2 ^ w := by
          have h1 : bd + rci.2.1 ≤ m2 := hpot_next.1
          omega
        have hrci1_lt : rci.1 < 2 ^ w := by
          have h1 := adjCsrOff_succ X adj (locOf X u)
          have h2 := adjCsrOff_mono X adj (show locOf X u + 1 ≤ X.card by omega)
          rw [origOf_locOf huX] at h1
          have h3 : rci.1 ≤ (adj u).length := hci_spec.2.2.2.1
          omega
        refine runs_seq_assign_le (v := bd1)
          (by simp [Expr.eval, BinOp.eval, h2_29, h2_37, h2_36, hbd1_lt, bd1,
            show bd + rci.2.1 - rci.1 < 2 ^ w by omega]) ?_
        refine runs_seq_store_le (x := cfg.ballStampAddr + locOf X u) (v := ballGen)
          (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := cfg.ballListAddr + cur.card) (v := locOf X u)
          (by eval_expr) (by eval_expr) ?_
        refine runs_seq_assign_le (v := cur.card + 1) (by eval_expr) ?_
        refine runs_assign_le (v := idx + 1) (by eval_expr) ?_ (by wram_cost)
        exact ⟨rfl, by simp only [st3, mem3, hmem2, st1]⟩
      rcases h0 with ⟨_, _, c3, hrun3, ⟨rfl, rfl⟩, hc3⟩
      exact ⟨c3, hrun3, by omega⟩
    rcases hpost3 with ⟨c3, hrun3, hc3⟩
    -- Frame helper for mem3
    have hfr3 : ∀ addr,
        (addr < cfg.ballStampAddr ∨ cfg.ballStampAddr + X.card ≤ addr) →
        (addr < cfg.ballListAddr ∨ cfg.ballListAddr + X.card ≤ addr) →
        mem3 addr = st0.mem addr := by
      intro addr h1 h2
      simp only [mem3, Function.update_of_ne (by omega : addr ≠ cfg.ballListAddr + cur.card),
        Function.update_of_ne (by omega : addr ≠ cfg.ballStampAddr + locOf X u)]
    have hcsr3 : NbCsrAt mem3 cfg.offAddr cfg.nbAddr X adj := by
      refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
      · rw [hfr3 _ (by rcases hdisj_bs_off with x | x <;> omega)
                   (by rcases hdisj_bl_off with x | x <;> omega)]
        exact hcsr.1 i hi
      · have hlt : adjCsrOff X adj i + j < m2 := by
          have := adjCsrOff_mono X adj (show i + 1 ≤ X.card by omega)
          have := adjCsrOff_succ X adj i; omega
        rw [Nat.add_assoc, hfr3 _ (by rcases hdisj_bs_nb with x | x <;> omega)
                                   (by rcases hdisj_bl_nb with x | x <;> omega), ← Nat.add_assoc]
        exact hcsr.2 i hi j hj
    have hmask3 : ∀ v < X.card, mem3 (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V := by
      intro v hv
      rw [hfr3 _ (by rcases hdisj_bs_mask with x | x <;> omega)
                 (by rcases hdisj_bl_mask with x | x <;> omega)]
      exact hmask v hv
    have hbs3 : ∀ v < X.card, mem3 (cfg.ballStampAddr + v) = ballGen ↔ origOf X v ∈ cur1 := by
      intro v hv
      have hne_bl : cfg.ballStampAddr + v ≠ cfg.ballListAddr + cur.card := by
        rcases hdisj_bs_bl with x | x <;> omega
      simp only [mem3, Function.update_of_ne hne_bl, cur1, Finset.mem_insert]
      by_cases hveq : v = locOf X u
      · subst hveq; simp [origOf_locOf huX]
      · rw [Function.update_of_ne (by omega), hbs v hv]
        have hne_u : origOf X v ≠ u := fun h => hveq (by rw [← h, locOf_origOf hv])
        tauto
    have hbs3_le : ∀ v < X.card, mem3 (cfg.ballStampAddr + v) ≤ ballGen := by
      intro v hv
      have hne_bl : cfg.ballStampAddr + v ≠ cfg.ballListAddr + cur.card := by
        rcases hdisj_bs_bl with x | x <;> omega
      simp only [mem3, Function.update_of_ne hne_bl]
      by_cases hveq : v = locOf X u
      · subst hveq; simp
      · rw [Function.update_of_ne (by omega)]; exact hbs_le v hv
    have hbl3 : ListAt mem3 cfg.ballListAddr (bl ++ [locOf X u]) := by
      intro j hj
      simp only [List.length_append, List.length_singleton, hbl_len] at hj
      by_cases hje : j = cur.card
      · subst hje
        simp only [mem3, Function.update_self]
        rw [List.getElem_append_right (by omega)]; simp [hbl_len]
      · have hjlt : j < cur.card := by omega
        have hne_bs : cfg.ballListAddr + j ≠ cfg.ballStampAddr + locOf X u := by
          rcases hdisj_bs_bl with x | x <;> omega
        simp only [mem3, Function.update_of_ne (by omega : cfg.ballListAddr + j ≠ cfg.ballListAddr + cur.card),
          Function.update_of_ne hne_bs]
        rw [List.getElem_append_left (by omega)]
        exact hbl_at j (by omega)
    have hdata3 : ListAt mem3 (selData + (idx + 1)) (rest.map (locOf X)) := by
      intro j hj
      have hj_lt : idx + 1 + j < X.card := by simp at hj hidx; omega
      rw [Nat.add_assoc, hfr3 _ (by rcases hdisj_bs_data with x | x <;> omega)
                                 (by rcases hdisj_bl_data with x | x <;> omega)]
      have hd := hdata (j + 1) (by simp at hj ⊢; omega)
      rw [show selData + idx + (j + 1) = selData + (idx + 1 + j) by omega] at hd
      simpa using hd
    have hcur1_card : cur1.card = cur.card + 1 := Finset.card_insert_of_notMem hu_not_cur
    -- Invoke IH on rest
    obtain ⟨stF, cIH, hrunIH, hpostIH, hcIH⟩ :=
      ih (idx + 1) cur1 bd1 (bl ++ [locOf X u]) st3
        (by simp at hidx; omega) hnd_cons.2 (fun x hx => hsubV x (List.mem_cons_of_mem _ hx))
        (Finset.insert_subset huV hcurV)
        (by rw [Finset.disjoint_left]; intro x hx hxR
            rcases Finset.mem_insert.mp hx with rfl | hxC
            · exact hnd_cons.1 (List.mem_toFinset.mp hxR)
            · exact Finset.disjoint_left.mp hdisj_cur hxC (by simp [List.mem_toFinset.mp hxR]))
        hpot_next.2 hcsr3 hmask3 hbs3 hbs3_le
        (by simp [hbl_len, hcur1_card])
        (by rw [List.nodup_append]; refine ⟨hbl_nd, List.nodup_singleton _, fun a ha b hb hab => ?_⟩
            simp at hb; subst hb; subst hab
            have := (hbl_sub (locOf X u) ha).2; rw [origOf_locOf huX] at this; exact hu_not_cur this)
        (fun x hx => by
          rcases List.mem_append.mp hx with hx1 | hx2
          · exact ⟨(hbl_sub x hx1).1, Finset.mem_insert_of_mem (hbl_sub x hx1).2⟩
          · simp at hx2; subst hx2; exact ⟨hu_loc_lt, by simp [cur1, origOf_locOf huX]⟩)
        (fun v hv => by
          rcases Finset.mem_insert.mp hv with rfl | hvC
          · exact ⟨huX, by simp⟩
          · exact ⟨(hbl_cov v hvC).1, List.mem_append_left _ (hbl_cov v hvC).2⟩)
        hbl3 hdata3
        (by simp [st3, hregs2 2 (by decide), st1, hr2])
        (by simp [st3, hregs2 3 (by decide), st1, hr3])
        (by simp [st3, hregs2 4 (by decide), st1, hr4])
        (by simp [st3, hregs2 5 (by decide), st1, hr5])
        (by simp [st3, hregs2 14 (by decide), st1, hr14])
        (by simp [st3, hregs2 15 (by decide), st1, hr15])
        (by simp [st3, hregs2 25 (by decide), st1, hr25])
        (by simp [st3, hregs2 27 (by decide), st1, hr27])
        (by simp [st3, hcur1_card])
        (by simp [st3]) (by simp [st3])
        (by simp [st3, hregs2 32 (by decide), st1, hr32]) ω
    -- Compose body st0 → st1 → st2 → st3
    have hbody : ∃ cB,
        Runs w p ω
          (seqStmts
            [ .assign 33 (.load (.bin .add (.reg 25) (.reg 31)))
            , .assign 34 (.load (.bin .add (.reg 2) (.reg 33)))
            , .assign 35 (.load (.bin .add (.reg 2) (.bin .add (.reg 33) (.const 1))))
            , ballCountIncStmt
            , .assign 29 (.bin .sub (.bin .add (.reg 29) (.reg 37)) (.reg 36))
            , .store (.bin .add (.reg 14) (.reg 33)) (.reg 27)
            , .store (.bin .add (.reg 15) (.reg 28)) (.reg 33)
            , .assign 28 (.bin .add (.reg 28) (.const 1))
            , .assign 31 (.bin .add (.reg 31) (.const 1)) ])
          st0 .normal st3 cB ∧ cB ≤ c1 + c2 + c3 + 10 := by
      dsimp only [seqStmts] at hrun1 ⊢
      rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩; · cases h
      rcases runs_seq_iff.mp hrb with ⟨_, _, _, h, _⟩ | ⟨sb, cb1, cb2, hrb1, hrb2, rfl⟩; · cases h
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, hra,
        runs_seq_iff.mpr (Or.inr ⟨sb, cb1, _, hrb1,
          runs_seq_iff.mpr (Or.inr ⟨st1, cb2, _, hrb2,
            runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3, hrun2, hrun3, rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩
    rcases hbody with ⟨cB, hrunB, hcB⟩
    have hrun_tot : Runs w p ω ballAddLayerStmt st0 .normal stF
        ((Expr.bin .lt (.reg 31) (.reg 32)).size + cB + cIH + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st3, cB, cIH, hev_guard, by decide, hrunB, hrunIH, rfl⟩))
    have hadd := addLayerToBall_cost_add adj V rest cur1 bd1 0 (0 + rci.2.2 + 1)
    simp only [Nat.zero_add] at hadd
    rcases hpostIH with ⟨hrF, h28F, h29F, ha1, ha1V, hpotF, hbsF, hbsF_le, hblF, hfrF⟩
    refine ⟨stF, _, hrun_tot, ?_, ?_⟩
    · dsimp only [addLayerToBall]
      simp only [Nat.zero_add]
      change (∀ k ≤ 30, k ≠ 28 → k ≠ 29 → stF.regs k = st0.regs k) ∧
        stF.regs 28 = (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1.card ∧
        stF.regs 29 = (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).2.1 ∧
        (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1 = cur ∪ (u :: rest).toFinset ∧
        (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1 ⊆ V ∧
        (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).2.1 +
          ∑ v ∈ V \ (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1, (adj v).length ≤ m2 ∧
        (∀ v < X.card, stF.mem (cfg.ballStampAddr + v) = ballGen ↔
          origOf X v ∈ (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1) ∧
        (∀ v < X.card, stF.mem (cfg.ballStampAddr + v) ≤ ballGen) ∧
        (∃ bl' : List ℕ, bl'.length = (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1.card ∧
          bl'.Nodup ∧
          (∀ x ∈ bl', x < X.card ∧ origOf X x ∈ (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1) ∧
          (∀ v ∈ (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).1, v ∈ X ∧ locOf X v ∈ bl') ∧
          ListAt stF.mem cfg.ballListAddr bl') ∧
        (∀ addr,
          (addr < cfg.ballStampAddr ∨ cfg.ballStampAddr + X.card ≤ addr) →
          (addr < cfg.ballListAddr ∨ cfg.ballListAddr + X.card ≤ addr) →
          stF.mem addr = st0.mem addr)
      rw [hadd.1, hadd.2.1]
      refine ⟨?_, h28F, h29F, ?_, ha1V, hpotF, hbsF, hbsF_le, hblF, ?_⟩
      · intro k hk h28 h29
        rw [hrF k hk h28 h29]
        simp [st3, Function.update_of_ne (by omega : k ≠ 31), Function.update_of_ne h28,
          Function.update_of_ne h29, hregs2 k (by omega), st1,
          Function.update_of_ne (by omega : k ≠ 35), Function.update_of_ne (by omega : k ≠ 34),
          Function.update_of_ne (by omega : k ≠ 33)]
      · rw [ha1]; ext x; simp [cur1, Finset.mem_union, Finset.mem_insert]
      · intro addr h1 h2
        rw [hfrF addr h1 h2]; exact hfr3 addr h1 h2
    · dsimp only [addLayerToBall]
      simp only [Nat.zero_add]
      change (Expr.bin .lt (.reg 31) (.reg 32)).size + cB + cIH + 1 ≤
        105 * (addLayerToBall adj V rest cur1 bd1 (rci.2.2 + 1)).2.2 + 5
      rw [hadd.2.2]
      have hlen_eq : rci.2.2 = (adj u).length := hci_spec.2.2.1
      simp only [Expr.size] at hc1 hc2 hc3 hcB hcIH ⊢
      omega

theorem ballWriteRet_triple {w : ℕ} {p : Program}
    {cfgAddr : ℕ} {st0 : State}
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 24 < 2 ^ w) :
    Triple w p (fun st => st = st0) ballWriteRetStmt
      (retPost fun v st' =>
        v = st0.regs 28 ∧
        st'.mem (cfgAddr + 18) = st0.regs 28 ∧
        st'.mem (cfgAddr + 19) = st0.regs 19 ∧
        st'.mem (cfgAddr + 20) = st0.regs 27 ∧
        (∀ a, a < cfgAddr + 18 ∨ cfgAddr + 21 ≤ a → st'.mem a = st0.mem a))
      (fun _ => 35) := by
  wram_enter; subst st
  unfold ballWriteRetStmt; dsimp only [seqStmts]
  refine runs_seq_store_le (x := cfgAddr + 18) (v := st0.regs 28) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 19) (v := st0.regs 19) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 20) (v := st0.regs 27) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := st0.regs 28) (by eval_expr) ?_ (by wram_cost)
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp
  · intro a ha
    simp only [Function.update_of_ne (by omega : a ≠ cfgAddr + 20),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 19),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 18)]

end MinCostFlow.ExpanderDecomp
