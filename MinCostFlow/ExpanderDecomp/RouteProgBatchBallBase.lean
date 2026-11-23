module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchRoute

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Cut-Finding Ball-Growing Loop Verification (`RouteProgBatchBall`)

Verifies `batchBallLoopStmt` against `batchBallLoop` (failed-batch branch):
- `growBall_ball_sub`: unconditionally `(growBall adj V S T b h L).ball ⊆ V`.
- `BatchBallInv`, `BatchBallRegs`: loop invariants across remaining terminal pairs.
- `batchBallFilterAB_triple`, `batchBallCallSetup_triple`: straight-line step helpers.
- `batchBallStep_grow`: verifies the `S ≠ ∅ ∧ T ≠ ∅` branch calling `growBallProc` and
  `batchCopyBallStmt`.
- `batchBallLoop_triple`: full inductive verification of `batchBallLoopStmt`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Helpers for `growBall` and `LocalBSlicesAt` -/

lemma scanBallLayers_ball_sub (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (b : ℕ) :
    ∀ (layers : List (List ℕ)) (cur : Finset ℕ) (bd cost : ℕ),
      (∀ L ∈ layers, ∀ u ∈ L, u ∈ V) →
      cur ⊆ V →
      (scanBallLayers adj V b layers cur bd cost).1 ⊆ V := by
  intro layers
  induction layers with
  | nil => intro cur _ _ _ hcur; exact hcur
  | cons L rest ih =>
    intro cur bd cost hL hcur
    have hadd_sub : ∀ (l : List ℕ) (c : Finset ℕ) (b0 c0 : ℕ),
        (∀ u ∈ l, u ∈ V) → c ⊆ V → (addLayerToBall adj V l c b0 c0).1 ⊆ V := by
      intro l
      induction l with
      | nil => intro c _ _ _ hc; exact hc
      | cons u us ihu =>
        intro c b0 c0 hu hc
        dsimp only [addLayerToBall]
        exact ihu _ _ _ (fun x hx => hu x (List.mem_cons_of_mem _ hx))
          (Finset.insert_subset (hu u List.mem_cons_self) hc)
    dsimp only [scanBallLayers]
    have hcur1 : (addLayerToBall adj V L cur bd cost).1 ⊆ V :=
      hadd_sub L cur bd cost (hL L List.mem_cons_self) hcur
    split_ifs
    · exact hcur1
    · exact ih _ _ _ (fun L' hL' => hL L' (List.mem_cons_of_mem _ hL')) hcur1

lemma growBall_ball_sub (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (b h L : ℕ) :
    (growBall adj V S T b h L).ball ⊆ V := by
  dsimp only [growBall]
  set bfsS := bfsLayers adj V S (h * L) ∅
  set bfsT := bfsLayers adj V T (h * L) ∅
  have hS := bfsLayers_layers_inv adj V S (h * L) ∅
  have hT := bfsLayers_layers_inv adj V T (h * L) ∅
  split_ifs
  · exact scanBallLayers_ball_sub adj V b bfsS.layers ∅ 0 _
      (fun l hl u hu => hS.1 ((hS.2.2.1 u).mp (List.mem_flatten.mpr ⟨l, hl, hu⟩)))
      (Finset.empty_subset _)
  · exact scanBallLayers_ball_sub adj V b bfsT.layers ∅ 0 _
      (fun l hl u hu => hT.1 ((hT.2.2.1 u).mp (List.mem_flatten.mpr ⟨l, hl, hu⟩)))
      (Finset.empty_subset _)

lemma localBSlicesAt_slot_bound {mem : ℕ → ℕ} {bOffAddr bLenAddr bDataAddr : ℕ}
    {X : Finset ℕ} {ps : List (Finset ℕ × Finset ℕ)} {cap : ℕ}
    (hbs : LocalBSlicesAt mem bOffAddr bLenAddr bDataAddr X ps cap) :
    ∀ u v, u ≤ v → v ≤ ps.length → mem (bOffAddr + u) ≤ mem (bOffAddr + v) := by
  intro u v huv hv
  have hstep : ∀ d, u + d ≤ ps.length → mem (bOffAddr + u) ≤ mem (bOffAddr + (u + d)) := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ihd =>
      intro hd
      have hlt : u + d < ps.length := by omega
      have h1 := (hbs.2 (u + d) hlt).1
      rw [show bOffAddr + (u + (d + 1)) = bOffAddr + (u + d) + 1 by omega]
      exact le_trans (ihd (by omega)) (by omega)
  have := hstep (v - u) (by omega)
  rwa [show u + (v - u) = v by omega] at this

/-! ## 2. Ball-Loop Invariants and Straight-Line Helpers -/

structure BatchBallInv (mem mem0 : ℕ → ℕ) (G : Graph) (X V_res : Finset ℕ)
    (cfg : BatchCfg) (hL : ℕ) (remPairs : List (Finset ℕ × Finset ℕ))
    (i : ℕ) (U : Finset ℕ) (ul : List ℕ) (bfsGen ballGen : ℕ) : Prop where
  U_sub : U ⊆ X
  bfs_lo : cfg.bfsGenIn ≤ bfsGen
  bfs_hi : bfsGen + 2 * (remPairs.length - i) ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 3)
  ball_lo : cfg.ballGenIn ≤ ballGen
  ball_hi : ballGen + (remPairs.length - i) ≤ cfg.ballGenIn + cfg.k
  res_csr : NbCsrAt mem (wsResOff cfg.ws cfg.nX) (wsResNb cfg.ws cfg.nX) X
    (adjOf ⟨G.n, G.inside V_res⟩ X)
  la : LocalAPairsAt mem cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X remPairs X.card
  bs : LocalBSlicesAt mem (wsBOff cfg.ws cfg.nX cfg.m2)
    (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k) (wsBData cfg.ws cfg.nX cfg.m2 cfg.k) X remPairs X.card
  live_ok : ∀ v < X.card,
    mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≠ cfg.liveGenIn + 1 ↔ origOf X v ∈ X \ U
  live_le : ∀ v < X.card,
    mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.liveGenIn + 1
  vis_le : ∀ v < X.card, mem (wsVisStamp cfg.ws cfg.nX + v) ≤ bfsGen
  ball_le : ∀ v < X.card, mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ ballGen
  ul_len : ul.length = U.card
  ul_nd : ul.Nodup
  ul_sub : ∀ x ∈ ul, x < X.card ∧ origOf X x ∈ U
  ul_cov : ∀ v ∈ U, v ∈ X ∧ locOf X v ∈ ul
  ul_at : ListAt mem (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k) ul
  sub_init : BatchSubCfgsInit mem cfg hL
  frame_ws : ∀ a, ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) → mem a = mem0 a
  ro_stamps : ∀ a,
    (wsIsoStamp cfg.ws ≤ a ∧ a < wsIsoStamp cfg.ws + 2 * cfg.nX) ∨
    (wsCurStamp cfg.ws cfg.nX ≤ a ∧ a < wsCurStamp cfg.ws cfg.nX + 4 * cfg.nX) →
    mem a = mem0 a

@[expose] def BatchBallRegs (regs : ℕ → ℕ) (cfg : BatchCfg) (cfgAddr : ℕ)
    (bfsGen ballGen i cutSize : ℕ) : Prop :=
  regs 0 = cfgAddr ∧ regs 1 = cfg.nX ∧ regs 2 = cfg.k ∧
  regs 9 = cfg.aOffAddr ∧ regs 10 = cfg.aLenAddr ∧ regs 11 = cfg.aDataAddr ∧
  regs 14 = cfg.ws ∧ regs 15 = wsBallCfg cfg.ws ∧ regs 16 = wsBfsBallCfg cfg.ws ∧
  regs 17 = wsBOff cfg.ws cfg.nX cfg.m2 ∧ regs 18 = bfsGen ∧ regs 19 = ballGen ∧
  regs 20 = wsBLen cfg.ws cfg.nX cfg.m2 cfg.k ∧ regs 21 = wsBData cfg.ws cfg.nX cfg.m2 cfg.k ∧
  regs 22 = wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k ∧ regs 23 = cfg.liveGenIn + 1 ∧
  regs 31 = i ∧ regs 32 = cutSize ∧
  regs 33 = wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ∧
  regs 34 = wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ∧
  regs 35 = wsBallList cfg.ws cfg.nX cfg.m2 cfg.k ∧
  regs 36 = wsCutList cfg.ws cfg.nX cfg.m2 cfg.k

lemma batchBallCallSetup_triple {w : ℕ} {p : Program}
    {cfg : BatchCfg} {sLen tLen bfsGen ballGen : ℕ}
    (hw_ws : cfg.ws + 124 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (hr15 : st0.regs 15 = wsBallCfg cfg.ws) (hr16 : st0.regs 16 = wsBfsBallCfg cfg.ws)
    (hr18 : st0.regs 18 = bfsGen) (hr19 : st0.regs 19 = ballGen)
    (hr23 : st0.regs 23 = cfg.liveGenIn + 1)
    (hr37 : st0.regs 37 = sLen) (hr38 : st0.regs 38 = tLen) :
    ∀ ω,
      ∃ st1 c1,
        Runs w p ω
          (seqStmts
            [ .store (.bin .add (.reg 15) (.const 4)) (.reg 23)
            , .store (.bin .add (.reg 15) (.const 10)) (.reg 37)
            , .store (.bin .add (.reg 15) (.const 12)) (.reg 38)
            , .store (.bin .add (.reg 15) (.const 15)) (.reg 18)
            , .store (.bin .add (.reg 15) (.const 16)) (.reg 19)
            , .store (.bin .add (.reg 16) (.const 3)) (.reg 23) ])
          st0 .normal st1 c1 ∧
        st1.regs = st0.regs ∧
        st1.mem (wsBallCfg cfg.ws + 4) = cfg.liveGenIn + 1 ∧
        st1.mem (wsBallCfg cfg.ws + 10) = sLen ∧
        st1.mem (wsBallCfg cfg.ws + 12) = tLen ∧
        st1.mem (wsBallCfg cfg.ws + 15) = bfsGen ∧
        st1.mem (wsBallCfg cfg.ws + 16) = ballGen ∧
        st1.mem (wsBfsBallCfg cfg.ws + 3) = cfg.liveGenIn + 1 ∧
        (∀ a, a ≠ wsBallCfg cfg.ws + 4 → a ≠ wsBallCfg cfg.ws + 10 →
          a ≠ wsBallCfg cfg.ws + 12 → a ≠ wsBallCfg cfg.ws + 15 →
          a ≠ wsBallCfg cfg.ws + 16 → a ≠ wsBfsBallCfg cfg.ws + 3 → st1.mem a = st0.mem a) ∧
        c1 ≤ 50 := by
  intro ω
  have hb_w : wsBallCfg cfg.ws + 20 < 2 ^ w := by unfold wsBallCfg; omega
  have hbb_w : wsBfsBallCfg cfg.ws + 20 < 2 ^ w := by unfold wsBfsBallCfg; omega
  set mem1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update st0.mem (wsBallCfg cfg.ws + 4) (cfg.liveGenIn + 1))
    (wsBallCfg cfg.ws + 10) sLen)
    (wsBallCfg cfg.ws + 12) tLen)
    (wsBallCfg cfg.ws + 15) bfsGen)
    (wsBallCfg cfg.ws + 16) ballGen)
    (wsBfsBallCfg cfg.ws + 3) (cfg.liveGenIn + 1)
  set st1 : State := { st0 with mem := mem1 }
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .store (.bin .add (.reg 15) (.const 4)) (.reg 23)
          , .store (.bin .add (.reg 15) (.const 10)) (.reg 37)
          , .store (.bin .add (.reg 15) (.const 12)) (.reg 38)
          , .store (.bin .add (.reg 15) (.const 15)) (.reg 18)
          , .store (.bin .add (.reg 15) (.const 16)) (.reg 19)
          , .store (.bin .add (.reg 16) (.const 3)) (.reg 23) ])
        st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 50 := by
    dsimp only [seqStmts]
    refine runs_seq_store_le (x := wsBallCfg cfg.ws + 4) (v := cfg.liveGenIn + 1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := wsBallCfg cfg.ws + 10) (v := sLen) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := wsBallCfg cfg.ws + 12) (v := tLen) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := wsBallCfg cfg.ws + 15) (v := bfsGen) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := wsBallCfg cfg.ws + 16) (v := ballGen) (by eval_expr) (by eval_expr) ?_
    refine runs_store_le (x := wsBfsBallCfg cfg.ws + 3) (v := cfg.liveGenIn + 1) (by eval_expr) (by eval_expr)
      ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
  refine ⟨st1, c1, hrun1, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · simp only [st1, mem1, wsBallCfg, wsBfsBallCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  · simp only [st1, mem1, wsBallCfg, wsBfsBallCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · simp only [st1, mem1, wsBallCfg, wsBfsBallCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  · simp only [st1, mem1, wsBallCfg, wsBfsBallCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · simp only [st1, mem1, wsBallCfg, wsBfsBallCfg]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · simp only [st1, mem1, wsBallCfg, wsBfsBallCfg]
    rw [Function.update_self]
  · intro a h1 h2 h3 h4 h5 h6
    simp only [st1, mem1, Function.update_of_ne h6, Function.update_of_ne h5,
      Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h1]

lemma batchBallPostLoad_triple {w : ℕ} {p : Program}
    {ballCfgAddr bfsGen1 ballGen1 ballListAddr cutListAddr cutSize : ℕ}
    (hw_bc : ballCfgAddr + 24 < 2 ^ w) (hw20 : 20 < 2 ^ w)
    {st0 : State}
    (hr15 : st0.regs 15 = ballCfgAddr) (hr32 : st0.regs 32 = cutSize)
    (hr35 : st0.regs 35 = ballListAddr) (hr36 : st0.regs 36 = cutListAddr)
    (hm19 : st0.mem (ballCfgAddr + 19) = bfsGen1)
    (hm20 : st0.mem (ballCfgAddr + 20) = ballGen1) :
    ∀ ω,
      let st1 : State :=
        { st0 with
          regs := Function.update (Function.update (Function.update (Function.update
            (Function.update st0.regs 18 bfsGen1) 19 ballGen1) 24 ballListAddr) 25 cutListAddr)
            27 cutSize }
      ∃ c1,
        Runs w p ω
          (seqStmts
            [ .assign 18 (.load (.bin .add (.reg 15) (.const 19)))
            , .assign 19 (.load (.bin .add (.reg 15) (.const 20)))
            , .assign 24 (.reg 35)
            , .assign 25 (.reg 36)
            , .assign 27 (.reg 32) ])
          st0 .normal st1 c1 ∧ c1 ≤ 35 := by
  intro ω
  set st1 : State :=
    { st0 with
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update st0.regs 18 bfsGen1) 19 ballGen1) 24 ballListAddr) 25 cutListAddr)
        27 cutSize }
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .assign 18 (.load (.bin .add (.reg 15) (.const 19)))
          , .assign 19 (.load (.bin .add (.reg 15) (.const 20)))
          , .assign 24 (.reg 35)
          , .assign 25 (.reg 36)
          , .assign 27 (.reg 32) ])
        st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 35 := by
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := bfsGen1) (by rw [← hm19]; eval_expr) ?_
    refine runs_seq_assign_le (v := ballGen1) (by rw [← hm20]; eval_expr) ?_
    refine runs_seq_assign_le (v := ballListAddr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := cutListAddr) (by eval_expr) ?_
    refine runs_assign_le (v := cutSize) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
  exact ⟨c1, hrun1, by omega⟩

lemma batchBallFilterOne_triple {w : ℕ} {p : Program}
    {X Vlive A : Finset ℕ}
    {offAddr lenAddr dataAddr liveStampAddr liveGen outBuf i off_i dstReg : ℕ}
    (hAX : A ⊆ X) (hVX : Vlive ⊆ X)
    (hdisj_out_in : DisjRange outBuf X.card (dataAddr + off_i) A.card)
    (hdisj_out_ls : DisjRange outBuf X.card liveStampAddr X.card)
    (hw_off : offAddr + i < 2 ^ w) (hw_len : lenAddr + i < 2 ^ w)
    (hw_in : dataAddr + off_i + A.card + 5 < 2 ^ w)
    (hw_out : outBuf + X.card + 5 < 2 ^ w)
    (hw_ls : liveStampAddr + X.card + 5 < 2 ^ w)
    (hw_lg : liveGen < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    {rOff rLen rData rOut : ℕ}
    (_hrOff_ne : rOff ≠ 24 ∧ rOff ≠ 25 ∧ rOff ≠ 26 ∧ rOff ≠ 27 ∧ rOff ≠ 28 ∧ rOff ≠ 29 ∧ rOff ≠ 30)
    (hrLen_ne : rLen ≠ 24 ∧ rLen ≠ 25 ∧ rLen ≠ 26 ∧ rLen ≠ 27 ∧ rLen ≠ 28 ∧ rLen ≠ 29 ∧ rLen ≠ 30)
    (_hrData_ne : rData ≠ 24 ∧ rData ≠ 25 ∧ rData ≠ 26 ∧ rData ≠ 27 ∧ rData ≠ 28 ∧ rData ≠ 29 ∧ rData ≠ 30)
    (hrOut_ne : rOut ≠ 24 ∧ rOut ≠ 25 ∧ rOut ≠ 26 ∧ rOut ≠ 27 ∧ rOut ≠ 28 ∧ rOut ≠ 29 ∧ rOut ≠ 30)
    (_hr31_ne : (31 : ℕ) ≠ 24)
    {st0 : State}
    (hoff_m : st0.mem (offAddr + i) = off_i)
    (hlen_m : st0.mem (lenAddr + i) = A.card)
    (hlist : ListAt st0.mem (dataAddr + off_i) ((A.sort (· ≤ ·)).map (locOf X)))
    (hls : ∀ v < X.card, st0.mem (liveStampAddr + v) ≠ liveGen ↔ origOf X v ∈ Vlive)
    (hrOff : st0.regs rOff = offAddr) (hrLen : st0.regs rLen = lenAddr)
    (hrData : st0.regs rData = dataAddr) (hrOut : st0.regs rOut = outBuf)
    (hr22 : st0.regs 22 = liveStampAddr) (hr23 : st0.regs 23 = liveGen) (hr31 : st0.regs 31 = i) :
    ∀ ω,
      ∃ stF cF,
        Runs w p ω
          (seqStmts
            [ .assign 24 (.bin .add (.reg rData) (.load (.bin .add (.reg rOff) (.reg 31))))
            , .assign 26 (.load (.bin .add (.reg rLen) (.reg 31)))
            , .assign 27 (.reg rOut)
            , batchFilterLiveStmt
            , .assign dstReg (.reg 25) ])
          st0 .normal stF cF ∧
        (∀ r, r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ dstReg →
          stF.regs r = st0.regs r) ∧
        stF.regs dstReg = (A ∩ Vlive).card ∧
        ListAt stF.mem outBuf (((A ∩ Vlive).sort (· ≤ ·)).map (locOf X)) ∧
        (∀ a, ¬ (outBuf ≤ a ∧ a < outBuf + X.card) → stF.mem a = st0.mem a) ∧
        cF ≤ 45 * A.card + 55 := by
  intro ω
  set l := (A.sort (· ≤ ·)).map (locOf X)
  have hl_len : l.length = A.card := by simp [l, Finset.length_sort]
  have hl_le : l.length ≤ X.card := by rw [hl_len]; exact Finset.card_le_card hAX
  have hl_lt : ∀ v ∈ l, v < X.card := by
    intro v hv; rw [List.mem_map] at hv
    rcases hv with ⟨u, hu, rfl⟩
    exact locOf_lt (hAX ((Finset.mem_sort (· ≤ ·)).mp hu))
  have hl_filt : l.filter (fun v => decide (origOf X v ∈ Vlive)) =
      ((A ∩ Vlive).sort (· ≤ ·)).map (locOf X) := sort_inter_map_locOf hAX hVX
  set st1 : State :=
    { st0 with regs := Function.update (Function.update (Function.update st0.regs 24 (dataAddr + off_i))
        26 A.card) 27 outBuf }
  have hpre : ∃ c1,
      Runs w p ω
        (seqStmts
          [ .assign 24 (.bin .add (.reg rData) (.load (.bin .add (.reg rOff) (.reg 31))))
          , .assign 26 (.load (.bin .add (.reg rLen) (.reg 31)))
          , .assign 27 (.reg rOut) ])
        st0 .normal st1 c1 ∧ c1 ≤ 25 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 24 (.bin .add (.reg rData) (.load (.bin .add (.reg rOff) (.reg 31))))
            , .assign 26 (.load (.bin .add (.reg rLen) (.reg 31)))
            , .assign 27 (.reg rOut) ])
          st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 25 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := dataAddr + off_i)
        (by simp [Expr.eval, BinOp.eval, hrData, hrOff, hr31, show offAddr + i < 2 ^ w by omega,
             hoff_m, show dataAddr + off_i < 2 ^ w by omega]) ?_
      refine runs_seq_assign_le (v := A.card)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne hrLen_ne.1, hrLen,
             hr31, show lenAddr + i < 2 ^ w by omega, hlen_m]) ?_
      refine runs_assign_le (v := outBuf)
        (by simp [Expr.eval, Function.update_of_ne hrOut_ne.2.2.1, Function.update_of_ne hrOut_ne.1, hrOut])
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c1, h, ⟨rfl, rfl⟩, hc1⟩; exact ⟨c1, h, by omega⟩
  rcases hpre with ⟨c1, hrun1, hc1⟩
  obtain ⟨st2, c2, hrun2, hregs2, hr25_2, hlist2, hfr2, hc2⟩ :=
    batchFilterLive_triple (w := w) (p := p) (X := X) (Vlive := Vlive) (l := l) (st0 := st1)
      hl_lt hl_le (by rwa [hl_len]) hdisj_out_ls (by rwa [hl_len]) hw_out hw_ls hw_lg hw4
      hlist hls (by simp [st1, hr22]) (by simp [st1, hr23])
      (by simp [st1]) (by simp [st1, hl_len]) (by simp [st1]) ω
  set stF : State := { st2 with regs := Function.update st2.regs dstReg (A ∩ Vlive).card }
  have h25_eq : st2.regs 25 = (A ∩ Vlive).card := by
    rw [hr25_2, hl_filt]; simp [Finset.length_sort]
  have hrun3 : Runs w p ω (.assign dstReg (.reg 25)) st2 .normal stF ((Expr.reg 25).size + 1) :=
    runs_assign_iff.mpr ⟨(A ∩ Vlive).card, by simp [Expr.eval, h25_eq], rfl, rfl, rfl⟩
  have hrun23 : Runs w p ω (seqStmts [batchFilterLiveStmt, .assign dstReg (.reg 25)])
      st1 .normal stF (c2 + ((Expr.reg 25).size + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2, hrun3, rfl⟩)
  obtain ⟨cF, hrunF, hcF⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun1 hrun23
  refine ⟨stF, cF, hrunF,
    fun r h24 h25 h26 h27 h28 h29 h30 hdst => by
      simp only [stF, Function.update_of_ne hdst, hregs2 r h25 h28 h29 h30, st1,
        Function.update_of_ne h27, Function.update_of_ne h26, Function.update_of_ne h24],
    by simp [stF], by rwa [hl_filt] at hlist2, hfr2, ?_⟩
  simp only [Expr.size, List.length_cons, List.length_nil] at hc2 hcF
  rw [hl_len] at hc2; omega

/-! ## 3. Non-Empty Ball-Growing Step (`batchBallStep_grow`) -/

lemma batch_not_ballWriteSet_ws_ro {cfg : BatchCfg}
    {liveGen sLen tLen bfsGen ballGen hL a : ℕ}
    (ha :
      (wsResOff cfg.ws cfg.nX ≤ a ∧ a < wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k) ∨
      (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + cfg.nX) ∨
      (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsCutList cfg.ws cfg.nX cfg.m2 cfg.k + cfg.nX) ∨
      (wsIsoStamp cfg.ws ≤ a ∧ a < wsIsoStamp cfg.ws + 2 * cfg.nX) ∨
      (wsCurStamp cfg.ws cfg.nX ≤ a ∧ a < wsCurStamp cfg.ws cfg.nX + 4 * cfg.nX)) :
    ¬ BallWriteSet cfg.nX
      (mkBatchBallCfg cfg liveGen sLen tLen bfsGen ballGen)
      (mkBatchBallBfsCfg cfg liveGen hL) (wsBallCfg cfg.ws) a := by
  intro hw
  simp only [BallWriteSet, mkBatchBallCfg, mkBatchBallBfsCfg,
    wsBallCfg, wsBfsBallCfg, wsVisStamp, wsDist, wsTmpNxt, wsLayerOffS, wsLayerDataS,
    wsLayerOffT, wsLayerDataT, wsBallStamp, wsBallList] at hw
  simp only [wsResOff, wsLayerOffS, wsLiveStamp, wsCutList, wsIsoStamp, wsCurStamp] at ha
  rcases ha with ha | ha | ha | ha | ha <;>
    (rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw <;> omega)

lemma batch_ws_ro_outside_124_and_bufs {cfg : BatchCfg} {a : ℕ}
    (ha :
      (wsResOff cfg.ws cfg.nX ≤ a ∧ a < wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k) ∨
      (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + cfg.nX) ∨
      (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsCutList cfg.ws cfg.nX cfg.m2 cfg.k + cfg.nX) ∨
      (wsIsoStamp cfg.ws ≤ a ∧ a < wsIsoStamp cfg.ws + 2 * cfg.nX) ∨
      (wsCurStamp cfg.ws cfg.nX ≤ a ∧ a < wsCurStamp cfg.ws cfg.nX + 4 * cfg.nX)) :
    (a < cfg.ws ∨ cfg.ws + 124 ≤ a) ∧
    ¬ ((wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + cfg.nX) ∨
       (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + cfg.nX)) := by
  simp only [wsResOff, wsLayerOffS, wsLiveStamp, wsCutList, wsIsoStamp, wsCurStamp,
    wsSBallBuf, wsTBallBuf] at ha ⊢
  rcases ha with ha | ha | ha | ha | ha <;> constructor <;> omega

lemma batch_ball_r_ne {r : ℕ} (hr : r ≤ 17 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23) :
    r ≠ 31 ∧ r ≠ 18 ∧ r ≠ 19 ∧ r ≠ 24 ∧ r ≠ 25 ∧ r ≠ 26 ∧ r ≠ 27 ∧ r ≠ 28 ∧
    r ≠ 29 ∧ r ≠ 30 ∧ r ≠ 32 ∧ r ≠ 37 ∧ r ≠ 38 := by omega


lemma ballDisj_of_dyn {w nX m2 a : ℕ} {c : BallCfg} {b : BfsCfg}
    {lo1 ld1 bg1 ip1 il1 : ℕ}
    (h : BallDisj w nX m2 c b a) :
    BallDisj w nX m2 c
      ({ b with
          layerOffAddr := lo1, layerDataAddr := ld1, bfsGen := bg1,
          initPtr := ip1, initLen := il1 }) a := by
  cases h; constructor <;> assumption

end MinCostFlow.ExpanderDecomp
