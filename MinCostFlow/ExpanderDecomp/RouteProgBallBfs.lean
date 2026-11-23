module

public import MinCostFlow.ExpanderDecomp.RouteProgBallScan

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer Ball Growing Dual-BFS Stage (`RouteProgBallBfs`)

Verifies the prefix of `growBallProc` that loads `BallCfg` and runs the two radius-`h * L` BFS
traversals from `S` and `T` via `bfsLayersProc`, returning the post-BFS state and preserved
layer/CSR/mask/stamp invariants for the ball-selection and layer-scan stage in `RouteProgBall.lean`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Prefix statements of `growBallProc`: load `BallCfg` and execute BFS from `S` and `T`. -/
@[expose] def ballBfsSTStmts (bBfs : ℕ) : List Stmt :=
  [ ballLoadCfgStmt
  , .assign 19 (.bin .add (.reg 16) (.const 1))
  , .store (.bin .add (.reg 1) (.const 9)) (.reg 6)
  , .store (.bin .add (.reg 1) (.const 10)) (.reg 7)
  , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
  , .store (.bin .add (.reg 1) (.const 14)) (.reg 10)
  , .store (.bin .add (.reg 1) (.const 15)) (.reg 11)
  , .call 20 bBfs [.reg 1]
  , .assign 21 (.load (.bin .add (.reg 1) (.const 16)))
  , .assign 19 (.bin .add (.reg 19) (.const 1))
  , .store (.bin .add (.reg 1) (.const 9)) (.reg 8)
  , .store (.bin .add (.reg 1) (.const 10)) (.reg 9)
  , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
  , .store (.bin .add (.reg 1) (.const 14)) (.reg 12)
  , .store (.bin .add (.reg 1) (.const 15)) (.reg 13)
  , .call 22 bBfs [.reg 1]
  , .assign 23 (.load (.bin .add (.reg 1) (.const 16))) ]

lemma growBallBfsST_triple {w : ℕ} {p : Program} {bBfs : ℕ}
    {X V S T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {h L : ℕ}
    {cfg : BallCfg} {bfsCfg : BfsCfg} {cfgAddr m2 : ℕ} {st0 : State}
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hVX : V ⊆ X) (hSV : S ⊆ V) (hTV : T ⊆ V)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcfg : BallCfgAt st0.mem cfgAddr cfg)
    (hbfs_cfg : BfsCfgAt st0.mem cfg.bfsCfgAddr bfsCfg)
    (hmaxDist : bfsCfg.maxDist = h * L)
    (hcsr : NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : BallDisj w X.card m2 cfg bfsCfg cfgAddr)
    (hmask : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hs_list : ListAt st0.mem cfg.sPtr ((S.sort (· ≤ ·)).map (locOf X)))
    (hs_len : cfg.sLen = S.card)
    (ht_list : ListAt st0.mem cfg.tPtr ((T.sort (· ≤ ·)).map (locOf X)))
    (ht_len : cfg.tLen = T.card)
    (hvis0 : ∀ v < X.card, st0.mem (bfsCfg.visStampAddr + v) ≤ cfg.bfsGenIn)
    (hbs0 : ∀ v < X.card, st0.mem (cfg.ballStampAddr + v) ≤ cfg.ballGenIn)
    (hr0 : st0.regs 0 = cfgAddr) (ω : ℕ → Bool) :
    let bfsS := bfsLayers adj V S (h * L) ∅
    let bfsT := bfsLayers adj V T (h * L) ∅
    let selBfs := if bfsS.visited.card ≤ bfsT.visited.card then bfsS else bfsT
    let selOff := if bfsS.visited.card ≤ bfsT.visited.card then cfg.layerOffS else cfg.layerOffT
    let selData := if bfsS.visited.card ≤ bfsT.visited.card then cfg.layerDataS else cfg.layerDataT
    ∃ stT cST,
      Runs w p ω (seqStmts (ballBfsSTStmts bBfs)) st0 .normal stT cST ∧
      (∀ r ≤ 18, stT.regs r =
        match r with
        | 0 => cfgAddr | 1 => cfg.bfsCfgAddr | 2 => cfg.offAddr | 3 => cfg.nbAddr
        | 4 => cfg.maskArrAddr | 5 => cfg.maskBadVal | 6 => cfg.layerOffS
        | 7 => cfg.layerDataS | 8 => cfg.layerOffT | 9 => cfg.layerDataT
        | 10 => cfg.sPtr | 11 => cfg.sLen | 12 => cfg.tPtr | 13 => cfg.tLen
        | 14 => cfg.ballStampAddr | 15 => cfg.ballListAddr
        | 16 => cfg.bfsGenIn | 17 => cfg.ballGenIn | _ => cfg.b) ∧
      stT.regs 19 = cfg.bfsGenIn + 2 ∧
      stT.regs 20 = bfsS.visited.card ∧
      stT.regs 21 = bfsS.layers.length ∧
      stT.regs 22 = bfsT.visited.card ∧
      stT.regs 23 = bfsT.layers.length ∧
      NbCsrAt stT.mem cfg.offAddr cfg.nbAddr X adj ∧
      (∀ v < X.card, stT.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V) ∧
      (∀ r ≤ selBfs.layers.length, stT.mem (selOff + r) = ((selBfs.layers.take r).map List.length).sum) ∧
      (∀ r (hr : r < selBfs.layers.length),
        ListAt stT.mem (selData + ((selBfs.layers.take r).map List.length).sum) ((selBfs.layers[r]'hr).map (locOf X))) ∧
      (∀ v < X.card, stT.mem (cfg.ballStampAddr + v) ≤ cfg.ballGenIn) ∧
      (∀ v < X.card, stT.mem (bfsCfg.visStampAddr + v) ≤ cfg.bfsGenIn + 2) ∧
      (∀ a, ¬ BallWriteSet X.card cfg bfsCfg cfgAddr a → stT.mem a = st0.mem a) ∧
      cST ≤ bfsProgCost bfsS.cost + bfsProgCost bfsT.cost + 350 := by
  have hbS := hdisj.bfs_disj_S
  have hbT := hdisj.bfs_disj_T
  have hw_cfg := hdisj.w_cfg
  have hw_bcfg : cfg.bfsCfgAddr + 25 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_off : cfg.offAddr + X.card + 5 < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_off] at this; exact this
  have hw_nb : cfg.nbAddr + m2 + 5 < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_nb] at this; exact this
  have hw_mask : cfg.maskArrAddr + X.card + 5 < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_mask] at this; exact this
  have hw_lOffS : cfg.layerOffS + X.card + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_lDataS : cfg.layerDataS + X.card + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_lOffT : cfg.layerOffT + X.card + 5 < 2 ^ w := hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_lDataT : cfg.layerDataT + X.card + 5 < 2 ^ w := hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_sPtr : cfg.sPtr + cfg.sLen + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_tPtr : cfg.tPtr + cfg.tLen + 5 < 2 ^ w := hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_mb : cfg.maskBadVal < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_bad] at this; exact this
  have hw_m2 : m2 + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_nX : X.card + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw4 : 4 ≤ 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw_bs := hdisj.w_bs
  have hw_bl := hdisj.w_bl
  have hw_bgen := hdisj.w_bgen
  have hw_ballgen := hdisj.w_ballgen
  have hw_mul := hdisj.w_mul
  have hw_b16 := hdisj.w_b16
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  dsimp only
  -- Step 1: Load 18 config words
  obtain ⟨o1, st1, c1, hrun1, hst1, hc1⟩ :=
    ballLoadCfg_triple (p := p) hcfg hr0 hw_cfg st0 ω rfl
  cases o1 with
  | returned _ => exact hst1.elim
  | normal =>
  rcases hst1 with ⟨hmem1, hregs1⟩
  have h1_1 : st1.regs 1 = cfg.bfsCfgAddr := hregs1 1 (by decide)
  have h1_6 : st1.regs 6 = cfg.layerOffS := hregs1 6 (by decide)
  have h1_7 : st1.regs 7 = cfg.layerDataS := hregs1 7 (by decide)
  have h1_8 : st1.regs 8 = cfg.layerOffT := hregs1 8 (by decide)
  have h1_9 : st1.regs 9 = cfg.layerDataT := hregs1 9 (by decide)
  have h1_10 : st1.regs 10 = cfg.sPtr := hregs1 10 (by decide)
  have h1_11 : st1.regs 11 = cfg.sLen := hregs1 11 (by decide)
  have h1_12 : st1.regs 12 = cfg.tPtr := hregs1 12 (by decide)
  have h1_13 : st1.regs 13 = cfg.tLen := hregs1 13 (by decide)
  have h1_16 : st1.regs 16 = cfg.bfsGenIn := hregs1 16 (by decide)
  have h1_17 : st1.regs 17 = cfg.ballGenIn := hregs1 17 (by decide)
  -- Step 2: Setup and call BFS from S
  set memS0 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update st1.mem
      (cfg.bfsCfgAddr + 9) cfg.layerOffS)
      (cfg.bfsCfgAddr + 10) cfg.layerDataS)
      (cfg.bfsCfgAddr + 12) (cfg.bfsGenIn + 1))
      (cfg.bfsCfgAddr + 14) cfg.sPtr)
      (cfg.bfsCfgAddr + 15) cfg.sLen
  set stS0 : State :=
    { mem := memS0, regs := Function.update st1.regs 19 (cfg.bfsGenIn + 1), pos := st1.pos }
  have hsetupS : ∃ cSetupS,
      Runs w p ω
        (seqStmts
          [ .assign 19 (.bin .add (.reg 16) (.const 1))
          , .store (.bin .add (.reg 1) (.const 9)) (.reg 6)
          , .store (.bin .add (.reg 1) (.const 10)) (.reg 7)
          , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
          , .store (.bin .add (.reg 1) (.const 14)) (.reg 10)
          , .store (.bin .add (.reg 1) (.const 15)) (.reg 11) ])
        st1 .normal stS0 cSetupS ∧ cSetupS ≤ 45 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 19 (.bin .add (.reg 16) (.const 1))
            , .store (.bin .add (.reg 1) (.const 9)) (.reg 6)
            , .store (.bin .add (.reg 1) (.const 10)) (.reg 7)
            , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
            , .store (.bin .add (.reg 1) (.const 14)) (.reg 10)
            , .store (.bin .add (.reg 1) (.const 15)) (.reg 11) ])
          st1 o s c ∧ (o = .normal ∧ s = stS0) ∧ 0 + c ≤ 45 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := cfg.bfsGenIn + 1) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 9) (v := cfg.layerOffS) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 10) (v := cfg.layerDataS) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 12) (v := cfg.bfsGenIn + 1) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 14) (v := cfg.sPtr) (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := cfg.bfsCfgAddr + 15) (v := cfg.sLen) (by eval_expr) (by eval_expr)
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cSetupS, hrun, ⟨rfl, rfl⟩, hc⟩
    exact ⟨cSetupS, hrun, by omega⟩
  rcases hsetupS with ⟨cSetupS, hrunSetupS, hcSetupS⟩
  have hmemS0_fr : ∀ a, a < cfg.bfsCfgAddr + 9 ∨ cfg.bfsCfgAddr + 16 ≤ a → memS0 a = st0.mem a := by
    intro a ha
    simp only [memS0, hmem1,
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 15),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 14),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 12),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 10),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 9)]
  set bfsCfgS : BfsCfg :=
    { bfsCfg with
      layerOffAddr := cfg.layerOffS, layerDataAddr := cfg.layerDataS,
      bfsGen := cfg.bfsGenIn + 1, initPtr := cfg.sPtr, initLen := cfg.sLen }
  have hbfsS_pre : (bfsLayersContract w X V S ∅ adj bfsCfgS m2).pre [cfg.bfsCfgAddr] memS0 := by
    dsimp only [bfsLayersContract, List.getD, List.getElem?_cons_zero, Option.getD_some]
    rcases hbfs_cfg with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, _, _, b11, _, b13, _, _⟩
    refine ⟨rfl, hVX, hSV, hadj_X, ?_, ?_, hm2, hbS, ?_, fun _ => rfl,
      fun h0 => by dsimp only [bfsCfgS] at h0; rw [hdisj.bfs_hasStop] at h0; omega, ?_, hs_len, ?_⟩
    · refine ⟨(hmemS0_fr _ (Or.inl (by omega))).trans b0,
        (hmemS0_fr _ (Or.inl (by omega))).trans b1, (hmemS0_fr _ (Or.inl (by omega))).trans b2,
        (hmemS0_fr _ (Or.inl (by omega))).trans b3, (hmemS0_fr _ (Or.inl (by omega))).trans b4,
        (hmemS0_fr _ (Or.inl (by omega))).trans b5, (hmemS0_fr _ (Or.inl (by omega))).trans b6,
        (hmemS0_fr _ (Or.inl (by omega))).trans b7, (hmemS0_fr _ (Or.inl (by omega))).trans b8,
        by simp [memS0, bfsCfgS], by simp [memS0, bfsCfgS],
        by simp only [memS0, hmem1, Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 15),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 14),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 12),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 10),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 9)]; exact b11,
        by simp [memS0, bfsCfgS],
        by simp only [memS0, hmem1, Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 15),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 14),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 12),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 10),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 9)]; exact b13,
        by simp [memS0, bfsCfgS], by simp [memS0, bfsCfgS]⟩
    · dsimp only [bfsCfgS]; rw [hdisj.bfs_off, hdisj.bfs_nb]
      refine ⟨fun i hi => (hmemS0_fr _ (by rcases hdisj.bcfg_off with x | x <;> omega)).trans (hcsr.1 i hi),
        fun i hi j hj => ?_⟩
      have hlt' : adjCsrOff X adj i + j < m2 := by
        have := adjCsrOff_mono X adj (show i + 1 ≤ X.card by omega)
        have := adjCsrOff_succ X adj i; omega
      rw [Nat.add_assoc, hmemS0_fr _ (by rcases hdisj.bcfg_nb with x | x <;> omega), ← Nat.add_assoc]
      exact hcsr.2 i hi j hj
    · intro v hv; dsimp only [bfsCfgS]; rw [hdisj.bfs_mask, hdisj.bfs_bad]
      rw [hmemS0_fr _ (by rcases hdisj.bcfg_mask with x | x <;> omega)]; exact hmask v hv
    · intro j hj; dsimp only [bfsCfgS]
      have hj_lt : j < cfg.sLen := by simp only [List.length_map, Finset.length_sort] at hj; omega
      rw [hmemS0_fr _ (by rcases hdisj.bcfg_s with x | x <;> omega)]; exact hs_list j hj
    · intro v hv; dsimp only [bfsCfgS]
      rw [hmemS0_fr _ (by rcases hdisj.bcfg_vis with x | x <;> omega)]
      have := hvis0 v hv; omega
  have hbfsS_mc := bfsLayers_meetsContract (w := w) hbfs_proc X V S ∅ adj bfsCfgS m2
  obtain ⟨bodyS, hbodyS, oS, stBfsS, cBfsS, hrunBfsS_raw, hpostS, hcBfsS⟩ :=
    hbfsS_mc [cfg.bfsCfgAddr] memS0 stS0.pos ω (by intro v hv; simp at hv; subst hv; omega) hbfsS_pre
  set vS := oS.value
  set memS1 := stBfsS.mem
  set posS1 := stBfsS.pos
  have hrunBfsS : Runs w p ω (.call 20 bBfs [.reg 1]) stS0 .normal
      { mem := memS1, regs := Function.update stS0.regs 20 vS, pos := posS1 }
      (argsSize [.reg 1] + cBfsS + 1) :=
    runs_call_iff.mpr ⟨[cfg.bfsCfgAddr], bodyS, oS, stBfsS, cBfsS,
      by simp [evalArgs, Expr.eval, stS0, h1_1], hbodyS, hrunBfsS_raw, rfl, rfl, rfl⟩
  simp only [bfsLayersContract, List.getD, List.getElem?_cons_zero, Option.getD_some] at hpostS hcBfsS
  have hbfsS_eq : bfsLayers adj V S bfsCfgS.maxDist ∅ = bfsLayers adj V S (h * L) ∅ := by
    dsimp only [bfsCfgS]; rw [hmaxDist]
  rw [hbfsS_eq] at hpostS hcBfsS
  set bfsS := bfsLayers adj V S (h * L) ∅
  rcases hpostS with ⟨hvS, hbfsS_out, hvisS_untouch, hbfsS_fr⟩
  dsimp only [bfsCfgS] at hvisS_untouch
  have hbfsS_linv : bfsS.visited ⊆ V ∧ bfsS.layers.flatten.Nodup ∧
      (∀ x, x ∈ bfsS.layers.flatten ↔ x ∈ bfsS.visited) ∧
      bfsS.layers.flatten.length = bfsS.visited.card ∧ bfsS.layers.length ≤ V.card :=
    bfsLayers_layers_inv adj V S (h * L) ∅
  have hvisS_le : ∀ v < X.card, memS1 (bfsCfg.visStampAddr + v) ≤ cfg.bfsGenIn + 1 := by
    intro v hv
    by_cases hm : origOf X v ∈ bfsS.visited
    · have := (hbfsS_out.2.2.1 v hv).mpr hm; dsimp only [bfsCfgS] at this; omega
    · rw [hvisS_untouch v hv hm, hmemS0_fr _ (by rcases hdisj.bcfg_vis with x | x <;> omega)]
      have := hvis0 v hv; omega
  have hnumLS_mem : memS1 (cfg.bfsCfgAddr + 16) = bfsS.layers.length := hbfsS_out.2.2.2.2.1
  have hnumLS_lt_w : bfsS.layers.length < 2 ^ w := by
    have : bfsS.layers.length ≤ V.card := hbfsS_linv.2.2.2.2
    have : V.card ≤ X.card := Finset.card_le_card hVX; omega
  have hvisS_card_lt_w : bfsS.visited.card < 2 ^ w := by
    have : bfsS.visited.card ≤ V.card := Finset.card_le_card hbfsS_linv.1
    have : V.card ≤ X.card := Finset.card_le_card hVX; omega
  -- Load numLayersS into r21 and Setup BFS from T
  set stS1 : State :=
    { mem := memS1
      regs := Function.update (Function.update stS0.regs 20 vS) 21 bfsS.layers.length
      pos := posS1 }
  have hrunLoadS : Runs w p ω (.assign 21 (.load (.bin .add (.reg 1) (.const 16))))
      { mem := memS1, regs := Function.update stS0.regs 20 vS, pos := posS1 } .normal stS1
      ((Expr.load (.bin .add (.reg 1) (.const 16))).size + 1) :=
    runs_assign_iff.mpr ⟨bfsS.layers.length,
      by simp [Expr.eval, BinOp.eval, stS0, h1_1, show 16 < 2 ^ w by omega,
           show cfg.bfsCfgAddr + 16 < 2 ^ w by omega, hnumLS_mem],
      rfl, rfl, rfl⟩
  set memT0 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update memS1
      (cfg.bfsCfgAddr + 9) cfg.layerOffT)
      (cfg.bfsCfgAddr + 10) cfg.layerDataT)
      (cfg.bfsCfgAddr + 12) (cfg.bfsGenIn + 2))
      (cfg.bfsCfgAddr + 14) cfg.tPtr)
      (cfg.bfsCfgAddr + 15) cfg.tLen
  set stT0 : State :=
    { mem := memT0, regs := Function.update stS1.regs 19 (cfg.bfsGenIn + 2), pos := posS1 }
  have hsetupT : ∃ cSetupT,
      Runs w p ω
        (seqStmts
          [ .assign 19 (.bin .add (.reg 19) (.const 1))
          , .store (.bin .add (.reg 1) (.const 9)) (.reg 8)
          , .store (.bin .add (.reg 1) (.const 10)) (.reg 9)
          , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
          , .store (.bin .add (.reg 1) (.const 14)) (.reg 12)
          , .store (.bin .add (.reg 1) (.const 15)) (.reg 13) ])
        stS1 .normal stT0 cSetupT ∧ cSetupT ≤ 45 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 19 (.bin .add (.reg 19) (.const 1))
            , .store (.bin .add (.reg 1) (.const 9)) (.reg 8)
            , .store (.bin .add (.reg 1) (.const 10)) (.reg 9)
            , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
            , .store (.bin .add (.reg 1) (.const 14)) (.reg 12)
            , .store (.bin .add (.reg 1) (.const 15)) (.reg 13) ])
          stS1 o s c ∧ (o = .normal ∧ s = stT0) ∧ 0 + c ≤ 45 := by
      dsimp only [seqStmts]
      have hS1_1 : stS1.regs 1 = cfg.bfsCfgAddr := by simp [stS1, stS0, h1_1]
      have hS1_8 : stS1.regs 8 = cfg.layerOffT := by simp [stS1, stS0, h1_8]
      have hS1_9 : stS1.regs 9 = cfg.layerDataT := by simp [stS1, stS0, h1_9]
      have hS1_12 : stS1.regs 12 = cfg.tPtr := by simp [stS1, stS0, h1_12]
      have hS1_13 : stS1.regs 13 = cfg.tLen := by simp [stS1, stS0, h1_13]
      have hS1_19 : stS1.regs 19 = cfg.bfsGenIn + 1 := by simp [stS1, stS0]
      refine runs_seq_assign_le (v := cfg.bfsGenIn + 2)
        (by simp [Expr.eval, BinOp.eval, hS1_19, show 1 < 2 ^ w by omega,
             show cfg.bfsGenIn + 1 + 1 < 2 ^ w by omega]) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 9) (v := cfg.layerOffT) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 10) (v := cfg.layerDataT) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 12) (v := cfg.bfsGenIn + 2) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.bfsCfgAddr + 14) (v := cfg.tPtr) (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := cfg.bfsCfgAddr + 15) (v := cfg.tLen) (by eval_expr) (by eval_expr)
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cSetupT, hrun, ⟨rfl, rfl⟩, hc⟩
    exact ⟨cSetupT, hrun, by omega⟩
  rcases hsetupT with ⟨cSetupT, hrunSetupT, hcSetupT⟩
  have hmemT0_fr : ∀ a, a < cfg.bfsCfgAddr + 9 ∨ cfg.bfsCfgAddr + 16 ≤ a → memT0 a = memS1 a := by
    intro a ha
    simp only [memT0,
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 15),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 14),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 12),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 10),
      Function.update_of_ne (by omega : a ≠ cfg.bfsCfgAddr + 9)]
  have hS_fr_all : ∀ a, ¬ BallWriteSet X.card cfg bfsCfg cfgAddr a → memT0 a = st0.mem a := by
    intro a ha
    have hnot5 : a ≠ cfg.bfsCfgAddr + 15 ∧ a ≠ cfg.bfsCfgAddr + 14 ∧ a ≠ cfg.bfsCfgAddr + 12 ∧
        a ≠ cfg.bfsCfgAddr + 10 ∧ a ≠ cfg.bfsCfgAddr + 9 := by
      refine ⟨fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))))))⟩
    have hT0 : memT0 a = memS1 a := by
      simp only [memT0, Function.update_of_ne hnot5.1, Function.update_of_ne hnot5.2.1,
        Function.update_of_ne hnot5.2.2.1, Function.update_of_ne hnot5.2.2.2.1,
        Function.update_of_ne hnot5.2.2.2.2]
    have hS0 : memS0 a = st0.mem a := by
      simp only [memS0, hmem1, Function.update_of_ne hnot5.1, Function.update_of_ne hnot5.2.1,
        Function.update_of_ne hnot5.2.2.1, Function.update_of_ne hnot5.2.2.2.1,
        Function.update_of_ne hnot5.2.2.2.2]
    rw [hT0, hbfsS_fr a (fun hbw => ha (bfsWriteSet_S_sub_ballWriteSet hbw)), hS0]
  set bfsCfgT : BfsCfg :=
    { bfsCfg with
      layerOffAddr := cfg.layerOffT, layerDataAddr := cfg.layerDataT,
      bfsGen := cfg.bfsGenIn + 2, initPtr := cfg.tPtr, initLen := cfg.tLen }
  have hbfsT_pre : (bfsLayersContract w X V T ∅ adj bfsCfgT m2).pre [cfg.bfsCfgAddr] memT0 := by
    dsimp only [bfsLayersContract, List.getD, List.getElem?_cons_zero, Option.getD_some]
    rcases hbfs_cfg with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, _, _, b11, _, b13, _, _⟩
    have hroS_cfg : ∀ i < 16, memS1 (cfg.bfsCfgAddr + i) = memS0 (cfg.bfsCfgAddr + i) := fun i hi =>
      hbfsS_fr _ (hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ ⟨by omega, by omega⟩)
    refine ⟨rfl, hVX, hTV, hadj_X, ?_, ?_, hm2, hbT, ?_, fun _ => rfl,
      fun h0 => by dsimp only [bfsCfgT] at h0; rw [hdisj.bfs_hasStop] at h0; omega, ?_, ht_len, ?_⟩
    · refine ⟨(hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 0 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b0)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 1 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b1)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 2 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b2)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 3 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b3)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 4 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b4)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 5 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b5)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 6 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b6)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 7 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b7)),
        (hmemT0_fr _ (Or.inl (by omega))).trans ((hroS_cfg 8 (by decide)).trans ((hmemS0_fr _ (Or.inl (by omega))).trans b8)),
        by simp [memT0, bfsCfgT], by simp [memT0, bfsCfgT],
        by rw [show memT0 (cfg.bfsCfgAddr + 11) = memS1 (cfg.bfsCfgAddr + 11) by
             simp only [memT0, Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 15),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 14),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 12),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 10),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 9)],
             hroS_cfg 11 (by decide)]
           simp only [memS0, hmem1, Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 15),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 14),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 12),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 10),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 11 ≠ cfg.bfsCfgAddr + 9)]; exact b11,
        by simp [memT0, bfsCfgT],
        by rw [show memT0 (cfg.bfsCfgAddr + 13) = memS1 (cfg.bfsCfgAddr + 13) by
             simp only [memT0, Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 15),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 14),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 12),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 10),
               Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 9)],
             hroS_cfg 13 (by decide)]
           simp only [memS0, hmem1, Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 15),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 14),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 12),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 10),
             Function.update_of_ne (by omega : cfg.bfsCfgAddr + 13 ≠ cfg.bfsCfgAddr + 9)]; exact b13,
        by simp [memT0, bfsCfgT], by simp [memT0, bfsCfgT]⟩
    · dsimp only [bfsCfgT]; rw [hdisj.bfs_off, hdisj.bfs_nb]
      refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
      · rw [hmemT0_fr _ (by rcases hdisj.bcfg_off with x | x <;> omega),
            hbfsS_fr _ (hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
              ⟨by rw [hdisj.bfs_off]; omega, by rw [hdisj.bfs_off]; omega⟩),
            hmemS0_fr _ (by rcases hdisj.bcfg_off with x | x <;> omega)]
        exact hcsr.1 i hi
      · have hlt' : adjCsrOff X adj i + j < m2 := by
          have := adjCsrOff_mono X adj (show i + 1 ≤ X.card by omega)
          have := adjCsrOff_succ X adj i; omega
        rw [Nat.add_assoc,
            hmemT0_fr _ (by rcases hdisj.bcfg_nb with x | x <;> omega),
            hbfsS_fr _ (hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
              ⟨by rw [hdisj.bfs_nb]; omega, by rw [hdisj.bfs_nb]; omega⟩),
            hmemS0_fr _ (by rcases hdisj.bcfg_nb with x | x <;> omega), ← Nat.add_assoc]
        exact hcsr.2 i hi j hj
    · intro v hv; dsimp only [bfsCfgT]; rw [hdisj.bfs_mask, hdisj.bfs_bad]
      rw [hmemT0_fr _ (by rcases hdisj.bcfg_mask with x | x <;> omega),
          hbfsS_fr _ (hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
            ⟨by rw [hdisj.bfs_mask]; omega, by rw [hdisj.bfs_mask]; omega⟩),
          hmemS0_fr _ (by rcases hdisj.bcfg_mask with x | x <;> omega)]
      exact hmask v hv
    · intro j hj; dsimp only [bfsCfgT]
      have hj_lt : j < cfg.tLen := by simp only [List.length_map, Finset.length_sort] at hj; omega
      rw [hmemT0_fr _ (by rcases hdisj.bcfg_t with x | x <;> omega),
          hbfsS_fr _ (hdisj.t_bfsS _ ⟨by omega, by omega⟩),
          hmemS0_fr _ (by rcases hdisj.bcfg_t with x | x <;> omega)]
      exact ht_list j hj
    · intro v hv; dsimp only [bfsCfgT]
      rw [hmemT0_fr _ (by rcases hdisj.bcfg_vis with x | x <;> omega)]
      have := hvisS_le v hv; omega
  have hbfsT_mc := bfsLayers_meetsContract (w := w) hbfs_proc X V T ∅ adj bfsCfgT m2
  obtain ⟨bodyT, hbodyT, oT, stBfsT, cBfsT, hrunBfsT_raw, hpostT, hcBfsT⟩ :=
    hbfsT_mc [cfg.bfsCfgAddr] memT0 stT0.pos ω (by intro v hv; simp at hv; subst hv; omega) hbfsT_pre
  set vT := oT.value
  set memT1 := stBfsT.mem
  set posT1 := stBfsT.pos
  have hrunBfsT : Runs w p ω (.call 22 bBfs [.reg 1]) stT0 .normal
      { mem := memT1, regs := Function.update stT0.regs 22 vT, pos := posT1 }
      (argsSize [.reg 1] + cBfsT + 1) :=
    runs_call_iff.mpr ⟨[cfg.bfsCfgAddr], bodyT, oT, stBfsT, cBfsT,
      by simp [evalArgs, Expr.eval, stT0, stS1, stS0, h1_1], hbodyT, hrunBfsT_raw, rfl, rfl, rfl⟩
  simp only [bfsLayersContract, List.getD, List.getElem?_cons_zero, Option.getD_some] at hpostT hcBfsT
  have hbfsT_eq : bfsLayers adj V T bfsCfgT.maxDist ∅ = bfsLayers adj V T (h * L) ∅ := by
    dsimp only [bfsCfgT]; rw [hmaxDist]
  rw [hbfsT_eq] at hpostT hcBfsT
  set bfsT := bfsLayers adj V T (h * L) ∅
  rcases hpostT with ⟨hvT, hbfsT_out, hvisT_untouch, hbfsT_fr⟩
  dsimp only [bfsCfgT] at hvisT_untouch
  have hbfsT_linv : bfsT.visited ⊆ V ∧ bfsT.layers.flatten.Nodup ∧
      (∀ x, x ∈ bfsT.layers.flatten ↔ x ∈ bfsT.visited) ∧
      bfsT.layers.flatten.length = bfsT.visited.card ∧ bfsT.layers.length ≤ V.card :=
    bfsLayers_layers_inv adj V T (h * L) ∅
  have hvisT_le : ∀ v < X.card, memT1 (bfsCfg.visStampAddr + v) ≤ cfg.bfsGenIn + 2 := by
    intro v hv
    by_cases hm : origOf X v ∈ bfsT.visited
    · have := (hbfsT_out.2.2.1 v hv).mpr hm; dsimp only [bfsCfgT] at this; omega
    · rw [hvisT_untouch v hv hm, hmemT0_fr _ (by rcases hdisj.bcfg_vis with x | x <;> omega)]
      have := hvisS_le v hv; omega
  have hnumLT_mem : memT1 (cfg.bfsCfgAddr + 16) = bfsT.layers.length := hbfsT_out.2.2.2.2.1
  have hnumLT_lt_w : bfsT.layers.length < 2 ^ w := by
    have : bfsT.layers.length ≤ V.card := hbfsT_linv.2.2.2.2
    have : V.card ≤ X.card := Finset.card_le_card hVX; omega
  have hvisT_card_lt_w : bfsT.visited.card < 2 ^ w := by
    have : bfsT.visited.card ≤ V.card := Finset.card_le_card hbfsT_linv.1
    have : V.card ≤ X.card := Finset.card_le_card hVX; omega
  -- Load numLayersT into r23
  set regsBeforeCond : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update st1.regs 19 (cfg.bfsGenIn + 1)) 20 vS) 21 bfsS.layers.length)
      19 (cfg.bfsGenIn + 2)) 22 vT) 23 bfsT.layers.length
  have hrunLoadT : Runs w p ω (.assign 23 (.load (.bin .add (.reg 1) (.const 16))))
      { mem := memT1, regs := Function.update stT0.regs 22 vT, pos := posT1 } .normal
      { mem := memT1, regs := regsBeforeCond, pos := posT1 }
      ((Expr.load (.bin .add (.reg 1) (.const 16))).size + 1) :=
    runs_assign_iff.mpr ⟨bfsT.layers.length,
      by simp [Expr.eval, BinOp.eval, stT0, stS1, stS0, h1_1, show 16 < 2 ^ w by omega,
           show cfg.bfsCfgAddr + 16 < 2 ^ w by omega, hnumLT_mem],
      rfl, rfl, rfl⟩
  -- Step 4: Select smaller ball via .cond (r22 < r20)
  set selBfs := if bfsS.visited.card ≤ bfsT.visited.card then bfsS else bfsT
  set selOff := if bfsS.visited.card ≤ bfsT.visited.card then cfg.layerOffS else cfg.layerOffT
  set selData := if bfsS.visited.card ≤ bfsT.visited.card then cfg.layerDataS else cfg.layerDataT
  have hT_fr_all : ∀ a, ¬ BallWriteSet X.card cfg bfsCfg cfgAddr a → memT1 a = st0.mem a := by
    intro a ha
    rw [hbfsT_fr a (fun hbw => ha (bfsWriteSet_T_sub_ballWriteSet hbw))]
    exact hS_fr_all a ha
  have hsel_loff : ∀ r ≤ selBfs.layers.length,
      memT1 (selOff + r) = ((selBfs.layers.take r).map List.length).sum := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card
    · simp only [selBfs, selOff, hle, ↓reduceIte]
      intro r hr
      have hr_le_X : r ≤ X.card := by have := hbfsS_linv.2.2.2.2; have := Finset.card_le_card hVX; omega
      rw [hbfsT_fr _ (hdisj.lOffS_bfsT _ ⟨by omega, by omega⟩),
          hmemT0_fr _ (by rcases hdisj.lOffS_bcfg with x | x <;> omega)]
      exact hbfsS_out.1 r hr
    · simp only [selBfs, selOff, hle, ↓reduceIte]
      exact hbfsT_out.1
  have hsel_ldata : ∀ r (hr : r < selBfs.layers.length),
      ListAt memT1 (selData + ((selBfs.layers.take r).map List.length).sum)
        ((selBfs.layers[r]'hr).map (locOf X)) := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card
    · simp only [selBfs, selData, hle, ↓reduceIte]
      intro r hr j hj
      have hlt_X : ((bfsS.layers.take r).map List.length).sum + j < X.card := by
        have h1 : ((bfsS.layers.take (r + 1)).map List.length).sum ≤ (bfsS.layers.map List.length).sum := by
          have hsp := List.take_append_drop (r + 1) bfsS.layers
          have hlen_sp : (bfsS.layers.map List.length).sum =
              ((bfsS.layers.take (r + 1)).map List.length).sum +
              ((bfsS.layers.drop (r + 1)).map List.length).sum := by
            conv_lhs => rw [← hsp, List.map_append, List.sum_append]
          omega
        rw [List.take_succ_eq_append_getElem hr, List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton] at h1
        have hlen_fl : (bfsS.layers.map List.length).sum = bfsS.layers.flatten.length := by
          rw [List.length_flatten]
        have h2 := hbfsS_linv.2.2.2.1
        have h3 : bfsS.visited.card ≤ X.card := Finset.card_le_card (Finset.Subset.trans hbfsS_linv.1 hVX)
        simp only [List.length_map] at hj; omega
      rw [Nat.add_assoc,
          hbfsT_fr _ (hdisj.lDataS_bfsT _ ⟨by omega, by omega⟩),
          hmemT0_fr _ (by rcases hdisj.lDataS_bcfg with x | x <;> omega), ← Nat.add_assoc]
      exact hbfsS_out.2.1 r hr j hj
    · simp only [selBfs, selData, hle, ↓reduceIte]
      exact hbfsT_out.2.1
  have hcsrT1 : NbCsrAt memT1 cfg.offAddr cfg.nbAddr X adj := by
    refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
    · rw [hbfsT_fr _ (hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
            ⟨by rw [hdisj.bfs_off]; omega, by rw [hdisj.bfs_off]; omega⟩),
          hmemT0_fr _ (by rcases hdisj.bcfg_off with x | x <;> omega),
          hbfsS_fr _ (hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
            ⟨by rw [hdisj.bfs_off]; omega, by rw [hdisj.bfs_off]; omega⟩),
          hmemS0_fr _ (by rcases hdisj.bcfg_off with x | x <;> omega)]
      exact hcsr.1 i hi
    · have hlt' : adjCsrOff X adj i + j < m2 := by
        have := adjCsrOff_mono X adj (show i + 1 ≤ X.card by omega)
        have := adjCsrOff_succ X adj i; omega
      rw [Nat.add_assoc,
          hbfsT_fr _ (hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
            ⟨by rw [hdisj.bfs_nb]; omega, by rw [hdisj.bfs_nb]; omega⟩),
          hmemT0_fr _ (by rcases hdisj.bcfg_nb with x | x <;> omega),
          hbfsS_fr _ (hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
            ⟨by rw [hdisj.bfs_nb]; omega, by rw [hdisj.bfs_nb]; omega⟩),
          hmemS0_fr _ (by rcases hdisj.bcfg_nb with x | x <;> omega), ← Nat.add_assoc]
      exact hcsr.2 i hi j hj
  have hmaskT1 : ∀ v < X.card, memT1 (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V := by
    intro v hv
    rw [hbfsT_fr _ (hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
          ⟨by rw [hdisj.bfs_mask]; omega, by rw [hdisj.bfs_mask]; omega⟩),
        hmemT0_fr _ (by rcases hdisj.bcfg_mask with x | x <;> omega),
        hbfsS_fr _ (hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
          ⟨by rw [hdisj.bfs_mask]; omega, by rw [hdisj.bfs_mask]; omega⟩),
        hmemS0_fr _ (by rcases hdisj.bcfg_mask with x | x <;> omega)]
    exact hmask v hv
  have hbsT1_le : ∀ v < X.card, memT1 (cfg.ballStampAddr + v) ≤ cfg.ballGenIn := by
    intro v hv
    rw [hbfsT_fr _ (hdisj.bs_bfsT _ ⟨by omega, by omega⟩),
        hmemT0_fr _ (by rcases hdisj.bs_bcfg with x | x <;> omega),
        hbfsS_fr _ (hdisj.bs_bfsS _ ⟨by omega, by omega⟩),
        hmemS0_fr _ (by rcases hdisj.bs_bcfg with x | x <;> omega)]
    exact hbs0 v hv
  -- Chain ballLoadCfgStmt ++ setupS ++ callS ++ loadS ++ setupT ++ callT ++ loadT
  have hrun_T_seg : ∃ cTSeg, Runs w p ω
      (seqStmts
        [ .assign 19 (.bin .add (.reg 19) (.const 1))
        , .store (.bin .add (.reg 1) (.const 9)) (.reg 8)
        , .store (.bin .add (.reg 1) (.const 10)) (.reg 9)
        , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
        , .store (.bin .add (.reg 1) (.const 14)) (.reg 12)
        , .store (.bin .add (.reg 1) (.const 15)) (.reg 13)
        , .call 22 bBfs [.reg 1]
        , .assign 23 (.load (.bin .add (.reg 1) (.const 16))) ])
      stS1 .normal { mem := memT1, regs := regsBeforeCond, pos := posT1 } cTSeg ∧
      cTSeg ≤ cSetupT + cBfsT + 18 := by
    have h1 : Runs w p ω
        (seqStmts [ .call 22 bBfs [.reg 1], .assign 23 (.load (.bin .add (.reg 1) (.const 16))) ])
        stT0 .normal { mem := memT1, regs := regsBeforeCond, pos := posT1 }
        ((argsSize [.reg 1] + cBfsT + 1) + ((Expr.load (.bin .add (.reg 1) (.const 16))).size + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrunBfsT, hrunLoadT, rfl⟩)
    obtain ⟨cTSeg, hTSeg, hcTSeg⟩ := ball_runs_seqStmts_append (by simp) (by simp) hrunSetupT h1
    refine ⟨cTSeg, hTSeg, ?_⟩
    simp only [Expr.size, argsSize, List.length_cons, List.length_nil] at hcTSeg; omega
  rcases hrun_T_seg with ⟨cTSeg, hrunTSeg, hcTSeg⟩
  have hrun_S_seg : ∃ cSSeg, Runs w p ω
      (seqStmts
        [ .assign 19 (.bin .add (.reg 16) (.const 1))
        , .store (.bin .add (.reg 1) (.const 9)) (.reg 6)
        , .store (.bin .add (.reg 1) (.const 10)) (.reg 7)
        , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
        , .store (.bin .add (.reg 1) (.const 14)) (.reg 10)
        , .store (.bin .add (.reg 1) (.const 15)) (.reg 11)
        , .call 20 bBfs [.reg 1]
        , .assign 21 (.load (.bin .add (.reg 1) (.const 16)))
        , .assign 19 (.bin .add (.reg 19) (.const 1))
        , .store (.bin .add (.reg 1) (.const 9)) (.reg 8)
        , .store (.bin .add (.reg 1) (.const 10)) (.reg 9)
        , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
        , .store (.bin .add (.reg 1) (.const 14)) (.reg 12)
        , .store (.bin .add (.reg 1) (.const 15)) (.reg 13)
        , .call 22 bBfs [.reg 1]
        , .assign 23 (.load (.bin .add (.reg 1) (.const 16))) ])
      st1 .normal { mem := memT1, regs := regsBeforeCond, pos := posT1 } cSSeg ∧
      cSSeg ≤ cSetupS + cBfsS + cTSeg + 18 := by
    have h1 : Runs w p ω
        (seqStmts
          [ .call 20 bBfs [.reg 1]
          , .assign 21 (.load (.bin .add (.reg 1) (.const 16)))
          , .assign 19 (.bin .add (.reg 19) (.const 1))
          , .store (.bin .add (.reg 1) (.const 9)) (.reg 8)
          , .store (.bin .add (.reg 1) (.const 10)) (.reg 9)
          , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
          , .store (.bin .add (.reg 1) (.const 14)) (.reg 12)
          , .store (.bin .add (.reg 1) (.const 15)) (.reg 13)
          , .call 22 bBfs [.reg 1]
          , .assign 23 (.load (.bin .add (.reg 1) (.const 16))) ])
        stS0 .normal { mem := memT1, regs := regsBeforeCond, pos := posT1 }
        ((argsSize [.reg 1] + cBfsS + 1) + (((Expr.load (.bin .add (.reg 1) (.const 16))).size + 1) + cTSeg + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrunBfsS,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrunLoadS, hrunTSeg, rfl⟩), rfl⟩)
    obtain ⟨cSSeg, hSSeg, hcSSeg⟩ := ball_runs_seqStmts_append (by simp) (by simp) hrunSetupS h1
    refine ⟨cSSeg, hSSeg, ?_⟩
    simp only [Expr.size, argsSize, List.length_cons, List.length_nil] at hcSSeg; omega
  rcases hrun_S_seg with ⟨cSSeg, hrunSSeg, hcSSeg⟩
  refine ⟨{ mem := memT1, regs := regsBeforeCond, pos := posT1 }, c1 + cSSeg + 1,
    runs_seq_iff.mpr (Or.inr ⟨st1, c1, cSSeg, hrun1, hrunSSeg, rfl⟩),
    fun r hr => by
      simp only [regsBeforeCond, Function.update_of_ne (by omega : r ≠ 23),
        Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 19),
        Function.update_of_ne (by omega : r ≠ 21), Function.update_of_ne (by omega : r ≠ 20)]
      exact hregs1 r hr,
    by simp [regsBeforeCond], by simp [regsBeforeCond, hvS], by simp [regsBeforeCond],
    by simp [regsBeforeCond, hvT], by simp [regsBeforeCond],
    hcsrT1, hmaskT1, hsel_loff, hsel_ldata, hbsT1_le, hvisT_le, hT_fr_all, ?_⟩
  dsimp only at hc1
  omega

end MinCostFlow.ExpanderDecomp
