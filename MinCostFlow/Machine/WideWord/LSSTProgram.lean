module

public import MinCostFlow.Machine.WideWord.LSSTProgramSim
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Top-Level Theorem 2.2 WordRAM Program Verification and Parameter Selection

This file proves the top-level theorems for `lsstModule`:
- `lsst_runs`: explicit non-existential deterministic execution theorem on `(G, v, ℓ)`.
- `lsst_meetsContract`: `lsstModule Q_AN b h` meets `lsstContract Q_AN c_AN K_AN w h`.
- `lsst_param_selection`: explicit host parameter selection (`h = 1`, `L_sim = lsstLSimMin`, `w`).
- `theorem_2_2_program`: deterministic WordRAM realization of **Theorem 2.2** (page 7 of
  arXiv:2309.16629v1) from `Cited.LowStretchSpanningTree`.
- `theorem_2_2_program_linear`: corollary giving the explicit linear-in-`(m + n + 1)` cost bound
  `16000 * (G.m + G.n + 1) * lsstOverheadFactor Q_AN c_AN K_AN G.n G.m L`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Top-level runs & contract theorems (`lsst_runs`, `lsst_meetsContract`) -/

theorem lsst_runs {w h b c_AN : ℕ} {p Q_AN : Program} {K_AN : ℝ} {ω : ℕ → Bool}
    (hp : p.HasAt b (lsstModule Q_AN b h))
    (hAN : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        WordRAM.RunsTo (WordRAM.wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) * (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ)
    (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (mem_orig : ℕ → ℕ) (pos : ℕ)
    (hwords : ∀ a ∈ [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
      outOrigPtr, outBridgePtr, outHdrPtr, heap], a < 2 ^ w)
    (hc_pos : 1 ≤ c_AN) (hG : G.Valid) (h1 : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L)
    (hLsim : lsstLSimMin c_AN G.n G.m L h ≤ L_sim)
    (ht_lt : tailArr + G.m ≤ heap) (hh_lt : headArr + G.m ≤ heap)
    (hlen_lt : lenArr + G.m * L ≤ heap) (hwt_lt : wtArr + G.m * L ≤ heap)
    (hoo_lt : outOrigPtr + G.n ≤ heap) (hob_lt : outBridgePtr + 2 * G.n ≤ heap)
    (hoh_lt : outHdrPtr + 2 ≤ heap)
    (hd_ob : DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n))
    (hd_oh : DisjointRanges outOrigPtr G.n outHdrPtr 2)
    (hd_bh : DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2)
    (htail_at : ListAt mem_orig tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhead_at : ListAt mem_orig headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hlen_orig : ∀ e < G.m, Num.Valid mem_orig (lenArr + e * L) h L ∧
      Num.fixVal mem_orig (lenArr + e * L) h L P_fp = ℓ e ∧ 0 < ℓ e)
    (hwt_orig : ∀ e < G.m, Num.Valid mem_orig (wtArr + e * L) h L ∧
      Num.fixVal mem_orig (wtArr + e * L) h L P_fp = v e ∧ 0 < v e)
    (hz_orig : ZeroFrom mem_orig heap)
    (hheap_space : heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w) :
    ∃ st' c,
      Runs w p ω (lsstEntryProc b h)
        (startState [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
          outOrigPtr, outBridgePtr, outHdrPtr, heap] mem_orig pos)
        (.returned 0) st' c ∧
      LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) st'.mem ∧
      ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h) ∧
      c ≤ lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h := by
  suffices hmain : ∃ o st' c,
      Runs w p ω (lsstEntryProc b h)
        (startState [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
          outOrigPtr, outBridgePtr, outHdrPtr, heap] mem_orig pos)
        o st' c ∧
      (LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig o st'.mem ∧
        ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h)) ∧
      0 + c ≤ lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h by
    obtain ⟨o, st', c, hrun, ⟨hpost, hz_end⟩, hc⟩ := hmain
    rcases hpost with ⟨origEdges, bridgePairs, rfl, h1, h2, h3, h4, hlt, hsum, h5, h6, h7, h8⟩
    exact ⟨st', c, hrun, ⟨origEdges, bridgePairs, rfl, h1, h2, h3, h4, hlt, hsum, h5, h6, h7, h8⟩, hz_end,
      by rwa [Nat.zero_add] at hc⟩
  have hGraph := lsst_hasAt_graph hp
  have hscan_mc : MeetsContract w p (lsstGraphBase b + idxScanNonloops) (scanNonloopsContract G w) :=
    scanNonloops_meetsContract (hasAt_csrAuxModule hGraph)
  have hw5 : 5 ≤ w := by omega
  have h16_w : 16 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 4 ≤ w))
  have hm_le_sp : G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    dsimp only [lsstSpace]; omega
  have hheap_m_w : heap + G.m < 2 ^ w := lt_of_le_of_lt (Nat.add_le_add_left hm_le_sp heap) hheap_space
  have ht_m_w : tailArr + G.m < 2 ^ w := lt_of_le_of_lt (by omega) hheap_m_w
  have hh_m_w : headArr + G.m < 2 ^ w := lt_of_le_of_lt (by omega) hheap_m_w
  have hm_w : G.m < 2 ^ w := hwords G.m (by simp)
  have htA_w : tailArr < 2 ^ w := hwords tailArr (by simp)
  have hhA_w : headArr < 2 ^ w := hwords headArr (by simp)
  have hheap_w : heap < 2 ^ w := hwords heap (by simp)
  let st0 := startState [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
    outOrigPtr, outBridgePtr, outHdrPtr, heap] mem_orig pos
  have hrg0 : LSSTInRegs st0 G.n G.m tailArr headArr lenArr wtArr L L_sim
      outOrigPtr outBridgePtr outHdrPtr heap :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpre_scan : (scanNonloopsContract G w).pre [G.m, tailArr, headArr, heap] st0.mem :=
    ⟨tailArr, headArr, heap, rfl, h16_w, ht_m_w, hh_m_w, hheap_m_w,
      Or.inr ht_lt, Or.inr hh_lt, htail_at, hhead_at⟩
  dsimp only [lsstEntryProc]
  refine runs_seq_call_step (ω := ω) (k := 0) (T := lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h)
    (Q := fun o st' =>
      LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig o st'.mem ∧
      ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h))
    hscan_mc
    (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r1)
      (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r2)
        (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r3)
          (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r11) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    hpre_scan rfl (rfl : _ = scanNonloopsCost G.m) fun nl_ret mem1 s1 hp1 hm1 hr1 => ?_
  rcases hp1 with ⟨t1, h1', o1, heq1, hret1, hnl_at1, hfr1⟩
  simp only [List.cons.injEq, and_true] at heq1
  rcases heq1 with ⟨_, _, _, eo1⟩
  rw [← eo1] at hnl_at1 hfr1
  have hrg1 := lsstInRegs_upd hrg0 hr1 (by decide)
  have hs1_20 : s1.regs 20 = (nonloopEdges G).length := by rw [hr1, Function.update_self, hret1]
  have hs1_nl : ListAt s1.mem heap (nonloopEdges G) := by rw [hm1]; exact hnl_at1
  have hs1_pres : ∀ a < heap, s1.mem a = mem_orig a := fun a ha => by
    rw [hm1, hfr1 a (Or.inl ha)]
    rfl
  have hs1_zero : ZeroFrom s1.mem (heap + G.m) := fun a ha => by
    rw [hm1, hfr1 a (Or.inr ha)]
    exact hz_orig a (by omega)
  have hs1_tail : ListAt s1.mem tailArr (List.ofFn fun i : Fin G.m => G.tail i) :=
    htail_at.congr fun q hq1 hq2 => by
      rw [List.length_ofFn] at hq2
      exact hs1_pres q (lt_of_lt_of_le hq2 ht_lt)
  have hs1_head : ListAt s1.mem headArr (List.ofFn fun i : Fin G.m => G.head i) :=
    hhead_at.congr fun q hq1 hq2 => by
      rw [List.length_ofFn] at hq2
      exact hs1_pres q (lt_of_lt_of_le hq2 hh_lt)
  have hv_pos : ∀ e < G.m, 0 < v e := fun e he => (hwt_orig e he).2.2
  have he20 : (.reg 20 : Expr).eval w s1 = some (nonloopEdges G).length := Expr.eval_reg_of_eq hs1_20
  by_cases hnl0 : (nonloopEdges G).length = 0
  · have hstar_bd : ((Expr.reg 1).size + (Expr.reg 2).size + (Expr.reg 3).size + (Expr.reg 11).size + 2 +
        scanNonloopsCost G.m) + (starPairsCost G.n + 30) + 2 ≤ lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h := by
      dsimp only [lsstCost, Expr.size]
      omega
    obtain ⟨o, st', c1, hrun1, ⟨hpost1, hge1⟩, hc1⟩ :=
      lsst_star_runs K_AN hGraph G v ℓ tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr
        outHdrPtr heap hG hw5 hoo_lt hob_lt hoh_lt hd_ob hd_oh hd_bh hv_pos hheap_m_w hrg1 hs1_pres hnl0
        (k := (Expr.reg 1).size + (Expr.reg 2).size + (Expr.reg 3).size + (Expr.reg 11).size + 2 +
          scanNonloopsCost G.m + 2)
        (T := lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h) (by dsimp only [Expr.size] at hstar_bd ⊢; omega)
    have hz_star : ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h) := by
      intro a ha
      have hm_le_sp : G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
        dsimp only [lsstSpace]; omega
      rw [hge1 a (by omega)]
      exact hs1_zero a (by omega)
    refine ⟨o, st', 1 + c1 + 1, runs_cond_iff.mpr ⟨0, c1, hnl0 ▸ he20, by simpa using hrun1, rfl⟩,
      ⟨hpost1, hz_star⟩, ?_⟩
    dsimp only [argsSize, Expr.size] at hc1 ⊢
    omega
  · have hnl_m : (nonloopEdges G).length ≤ G.m := nonloopEdges_length_le G
    have hcsr_mono : buildCSRCost G.n (nonloopEdges G).length ≤ buildCSRCost G.n G.m := by
      dsimp only [buildCSRCost]; exact Nat.mul_le_mul_right _ (by omega)
    have hbfs_mono : bfsBridgesCost G.n (nonloopEdges G).length ≤ bfsBridgesCost G.n G.m := by
      dsimp only [bfsBridgesCost]; omega
    have hgen_bd : ((Expr.reg 1).size + (Expr.reg 2).size + (Expr.reg 3).size + (Expr.reg 11).size + 2 +
          scanNonloopsCost G.m) + 2 +
        (buildCSRCost G.n (nonloopEdges G).length + buildVertIdxCost G.n +
          bfsBridgesCost G.n (nonloopEdges G).length + 80) +
        (weightsCost G.m L + (110 * G.m + (4 * G.m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
          simDecodeCost Q_AN (w'Max c_AN G.n G.m L h) (2 * G.m) (4 * G.m) G.n L_sim
            (anCostBound K_AN G.n G.m L_sim h) + 200) ≤ lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h := by
      dsimp only [lsstCost, Expr.size]
      linarith only [hcsr_mono, hbfs_mono]
    obtain ⟨o, st', c1, hrun1, hpost1, hc1⟩ :=
      lsst_graph_stage_runs (Q_post := fun o st' =>
          LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig o st'.mem ∧
          ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h))
        K_AN hGraph G tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap
        hG h1 hw hnl0 ht_lt hh_lt hheap_space hs1_tail hs1_head hs1_nl hs1_zero hs1_pres hrg1 hs1_20
        (tail := .ret (.const 0))
        fun s_bfs B newHeap vListPtr inactPtr bPtr bfsHeap hnew hvL hinP hbP hbfsP hB_le
            hrgB hrB20 hrB22 hrB23 hrB24 hrB26 hrB29 hrB30 hrB31 hrB32 hnlB hinB hBB hvidxB hBr hzB hpresB =>
          lsst_weights_sim_runs K_AN hp hAN G v ℓ P_fp tailArr headArr lenArr wtArr L L_sim
            outOrigPtr outBridgePtr outHdrPtr heap B newHeap vListPtr inactPtr bPtr bfsHeap
            hc_pos hG h1 hw hL1 hLsim hnl0 ht_lt hh_lt hlen_lt hwt_lt hoo_lt hob_lt hoh_lt hd_ob hd_oh hd_bh
            htail_at hhead_at hlen_orig hwt_orig hheap_space hnew hvL hinP hbP hbfsP hB_le
            hrgB hrB20 hrB22 hrB23 hrB24 hrB26 hrB29 hrB30 hrB31 hrB32 hnlB hinB hBB hvidxB hBr hzB hpresB
            hgen_bd
    refine ⟨o, st', 1 + c1 + 1, runs_cond_iff.mpr ⟨(nonloopEdges G).length, c1, he20, by
      simp [hnl0]; exact hrun1, rfl⟩, hpost1, ?_⟩
    dsimp only [argsSize, Expr.size] at hc1 ⊢
    omega

/-- Variant of `lsstEntryProc` that returns the actual trie allocation frontier `hp_end`
with `heap ≤ hp_end ≤ heap + lsstSpace Q_AN K_AN G.n G.m L_sim h` and `ZeroFrom st'.mem hp_end`. -/
def lsstFrontierProc (b h : ℕ) : Stmt :=
  .call 20 (lsstGraphBase b + idxScanNonloops) [.reg 1, .reg 2, .reg 3, .reg 11] ;;
  .cond (.reg 20)
    (.assign 21 (.bin .add (.reg 11) (.reg 1)) ;;
     .call 22 (lsstGraphBase b + idxBuildCSR) [.reg 0, .reg 20, .reg 11, .reg 2, .reg 3, .reg 21] ;;
     .assign 23 (.load (.reg 21)) ;;
     .assign 24 (.load (.bin .add (.reg 21) (.const 1))) ;;
     .assign 25 (.bin .add (.reg 21) (.const 2)) ;;
     .assign 26 (.bin .add (.reg 25) (.reg 0)) ;;
     .assign 27 (.bin .add (.reg 26) (.reg 0)) ;;
     .assign 28 (.bin .add (.reg 27) (.bin .add (.reg 0) (.const 1))) ;;
     .assign 29 (.load (.reg 25)) ;;
     .call 45 (lsstGraphBase b + idxBuildVertIdx) [.reg 23, .reg 25, .reg 22] ;;
     .assign 30 (.bin .add (.reg 22) (.reg 0)) ;;
     .assign 31 (.bin .add (.reg 30) (.reg 0)) ;;
     .call 32 (lsstGraphBase b + idxBfsBridges)
       [.reg 0, .reg 27, .reg 28, .reg 23, .reg 25, .reg 30, .reg 31] ;;
     .assign 33 (.bin .add (.reg 31) (.bin .mul (.const 2) (.reg 0))) ;;
     .assign 34 (.bin .add (.reg 33) (.reg 20)) ;;
     .assign 35 (.bin .add (.reg 34) (.const 1)) ;;
     .assign 36 (.bin .add (.reg 35) (.bin .mul (.reg 20) (.reg 7))) ;;
     .call 37 (lsstWeightsBase b + idxWeightsEntry)
       [.reg 20, .reg 11, .reg 4, .reg 5, .reg 23, .reg 6, .reg 33, .reg 35, .reg 34, .reg 36] ;;
     .assign 38 (.load (.reg 34)) ;;
     .assign 39 (.bin .add (.reg 37) (.bin .mul (.const 2) (.reg 20))) ;;
     .call 40 (lsstEncodeBase b + idxEncodeGAug)
       [.reg 20, .reg 11, .reg 2, .reg 3, .reg 22, .reg 33, .reg 35, .reg 38, .reg 23,
         .reg 32, .reg 30, .reg 7, .const (2 ^ h), .reg 37, .reg 39] ;;
     .assign 41 (.bin .add (.reg 40) (.reg 32)) ;;
     .assign 42 (.bin .add (.const 2) (.bin .mul (.const 3) (.reg 41))) ;;
     .assign 43 (.bin .add (.reg 39) (.bin .mul (.reg 42) (.reg 7))) ;;
     .call 45 (lsstEncodeBase b + idxSimDecode)
       [.reg 23, .reg 41, .reg 40, .reg 32, .reg 30, .reg 24, .reg 26, .reg 29, .reg 39,
         .reg 7, .const h, .const (2 ^ h), .reg 37, .reg 8, .reg 9, .reg 10, .reg 43] ;;
     .assign 44 (.load (.bin .add (.reg 43) (.const 1))) ;;
     .ret (.reg 44))
    (.store (.reg 10) (.const 0) ;;
     .call 21 (lsstGraphBase b + idxStarPairs) [.reg 0, .reg 9] ;;
     .store (.bin .add (.reg 10) (.const 1)) (.reg 21) ;;
     .ret (.bin .add (.reg 11) (.reg 1)))

lemma lsstFrontierProc_noRand (b h : ℕ) : (lsstFrontierProc b h).NoRand := by
  dsimp only [lsstFrontierProc, Stmt.NoRand]
  decide

theorem lsst_frontier_runs {w h b c_AN : ℕ} {p Q_AN : Program} {K_AN : ℝ} {ω : ℕ → Bool}
    (hp : p.HasAt b (lsstModule Q_AN b h))
    (hAN : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        WordRAM.RunsTo (WordRAM.wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) * (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ)
    (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (mem_orig : ℕ → ℕ) (pos : ℕ)
    (hwords : ∀ a ∈ [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
      outOrigPtr, outBridgePtr, outHdrPtr, heap], a < 2 ^ w)
    (hc_pos : 1 ≤ c_AN) (hG : G.Valid) (h1 : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L)
    (hLsim : lsstLSimMin c_AN G.n G.m L h ≤ L_sim)
    (ht_lt : tailArr + G.m ≤ heap) (hh_lt : headArr + G.m ≤ heap)
    (hlen_lt : lenArr + G.m * L ≤ heap) (hwt_lt : wtArr + G.m * L ≤ heap)
    (hoo_lt : outOrigPtr + G.n ≤ heap) (hob_lt : outBridgePtr + 2 * G.n ≤ heap)
    (hoh_lt : outHdrPtr + 2 ≤ heap)
    (hd_ob : DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n))
    (hd_oh : DisjointRanges outOrigPtr G.n outHdrPtr 2)
    (hd_bh : DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2)
    (htail_at : ListAt mem_orig tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhead_at : ListAt mem_orig headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hlen_orig : ∀ e < G.m, Num.Valid mem_orig (lenArr + e * L) h L ∧
      Num.fixVal mem_orig (lenArr + e * L) h L P_fp = ℓ e ∧ 0 < ℓ e)
    (hwt_orig : ∀ e < G.m, Num.Valid mem_orig (wtArr + e * L) h L ∧
      Num.fixVal mem_orig (wtArr + e * L) h L P_fp = v e ∧ 0 < v e)
    (hz_orig : ZeroFrom mem_orig heap)
    (hheap_space : heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w) :
    ∃ hp_end st' c,
      Runs w p ω (lsstFrontierProc b h)
        (startState [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
          outOrigPtr, outBridgePtr, outHdrPtr, heap] mem_orig pos)
        (.returned hp_end) st' c ∧
      heap ≤ hp_end ∧
      hp_end ≤ heap + lsstSpace Q_AN K_AN G.n G.m L_sim h ∧
      LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) st'.mem ∧
      ZeroFrom st'.mem hp_end ∧
      c ≤ lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h + 10 := by
  have hw5 : 5 ≤ w := by omega
  have h16_w : 16 ≤ 2 ^ w :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 4 ≤ w))
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hsp_ge : 4 + 9 * G.n + 4 * G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    dsimp only [lsstSpace]; omega
  have hheap_m_w : heap + G.m < 2 ^ w :=
    lt_of_le_of_lt (by omega) hheap_space
  have hm_w : G.m < 2 ^ w := hwords G.m (by simp)
  have ht_m_w : tailArr + G.m < 2 ^ w := lt_of_le_of_lt (by omega) hheap_space
  have hh_m_w : headArr + G.m < 2 ^ w := lt_of_le_of_lt (by omega) hheap_space
  have htA_w : tailArr < 2 ^ w := hwords tailArr (by simp)
  have hhA_w : headArr < 2 ^ w := hwords headArr (by simp)
  have hheap_w : heap < 2 ^ w := hwords heap (by simp)
  have hGraph := lsst_hasAt_graph hp
  have hscan_mc : MeetsContract w p (lsstGraphBase b + idxScanNonloops) (scanNonloopsContract G w) :=
    scanNonloops_meetsContract (hasAt_csrAuxModule hGraph)
  let st0 := startState [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
    outOrigPtr, outBridgePtr, outHdrPtr, heap] mem_orig pos
  have hrg0 : LSSTInRegs st0 G.n G.m tailArr headArr lenArr wtArr L L_sim
      outOrigPtr outBridgePtr outHdrPtr heap :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpre_scan : (scanNonloopsContract G w).pre [G.m, tailArr, headArr, heap] st0.mem :=
    ⟨tailArr, headArr, heap, rfl, h16_w, ht_m_w, hh_m_w, hheap_m_w,
      Or.inr ht_lt, Or.inr hh_lt, htail_at, hhead_at⟩
  dsimp only [lsstFrontierProc]
  suffices hmain : ∃ o st' c,
      Runs w p ω
        (.call 20 (lsstGraphBase b + idxScanNonloops) [.reg 1, .reg 2, .reg 3, .reg 11] ;;
         .cond (.reg 20)
           (.assign 21 (.bin .add (.reg 11) (.reg 1)) ;;
            .call 22 (lsstGraphBase b + idxBuildCSR) [.reg 0, .reg 20, .reg 11, .reg 2, .reg 3, .reg 21] ;;
            .assign 23 (.load (.reg 21)) ;;
            .assign 24 (.load (.bin .add (.reg 21) (.const 1))) ;;
            .assign 25 (.bin .add (.reg 21) (.const 2)) ;;
            .assign 26 (.bin .add (.reg 25) (.reg 0)) ;;
            .assign 27 (.bin .add (.reg 26) (.reg 0)) ;;
            .assign 28 (.bin .add (.reg 27) (.bin .add (.reg 0) (.const 1))) ;;
            .assign 29 (.load (.reg 25)) ;;
            .call 45 (lsstGraphBase b + idxBuildVertIdx) [.reg 23, .reg 25, .reg 22] ;;
            .assign 30 (.bin .add (.reg 22) (.reg 0)) ;;
            .assign 31 (.bin .add (.reg 30) (.reg 0)) ;;
            .call 32 (lsstGraphBase b + idxBfsBridges)
              [.reg 0, .reg 27, .reg 28, .reg 23, .reg 25, .reg 30, .reg 31] ;;
            .assign 33 (.bin .add (.reg 31) (.bin .mul (.const 2) (.reg 0))) ;;
            .assign 34 (.bin .add (.reg 33) (.reg 20)) ;;
            .assign 35 (.bin .add (.reg 34) (.const 1)) ;;
            .assign 36 (.bin .add (.reg 35) (.bin .mul (.reg 20) (.reg 7))) ;;
            .call 37 (lsstWeightsBase b + idxWeightsEntry)
              [.reg 20, .reg 11, .reg 4, .reg 5, .reg 23, .reg 6, .reg 33, .reg 35, .reg 34, .reg 36] ;;
            .assign 38 (.load (.reg 34)) ;;
            .assign 39 (.bin .add (.reg 37) (.bin .mul (.const 2) (.reg 20))) ;;
            .call 40 (lsstEncodeBase b + idxEncodeGAug)
              [.reg 20, .reg 11, .reg 2, .reg 3, .reg 22, .reg 33, .reg 35, .reg 38, .reg 23,
                .reg 32, .reg 30, .reg 7, .const (2 ^ h), .reg 37, .reg 39] ;;
            .assign 41 (.bin .add (.reg 40) (.reg 32)) ;;
            .assign 42 (.bin .add (.const 2) (.bin .mul (.const 3) (.reg 41))) ;;
            .assign 43 (.bin .add (.reg 39) (.bin .mul (.reg 42) (.reg 7))) ;;
            .call 45 (lsstEncodeBase b + idxSimDecode)
              [.reg 23, .reg 41, .reg 40, .reg 32, .reg 30, .reg 24, .reg 26, .reg 29, .reg 39,
                .reg 7, .const h, .const (2 ^ h), .reg 37, .reg 8, .reg 9, .reg 10, .reg 43] ;;
            .assign 44 (.load (.bin .add (.reg 43) (.const 1))) ;;
            .ret (.reg 44))
           (.store (.reg 10) (.const 0) ;;
            .call 21 (lsstGraphBase b + idxStarPairs) [.reg 0, .reg 9] ;;
            .store (.bin .add (.reg 10) (.const 1)) (.reg 21) ;;
            .ret (.bin .add (.reg 11) (.reg 1))))
        st0 o st' c ∧
      (∃ hp_end, o = .returned hp_end ∧ heap ≤ hp_end ∧
        hp_end ≤ heap + lsstSpace Q_AN K_AN G.n G.m L_sim h ∧
        LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) st'.mem ∧
        ZeroFrom st'.mem hp_end) ∧
      0 + c ≤ lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h + 10 by
    obtain ⟨o, st', c, hrun, ⟨hp_end, rfl, h1', h2', hpost', hz'⟩, hc⟩ := hmain
    exact ⟨hp_end, st', c, hrun, h1', h2', hpost', hz', by rwa [Nat.zero_add] at hc⟩
  refine runs_seq_call_step (ω := ω) (k := 0) (T := lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h + 10)
    hscan_mc
    (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r1)
      (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r2)
        (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r3)
          (evalArgs_cons (Expr.eval_reg_of_eq hrg0.r11) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    hpre_scan rfl (rfl : _ = scanNonloopsCost G.m) fun nl_ret mem1 s1 hp1 hm1 hr1 => ?_
  rcases hp1 with ⟨t1, h1', o1, heq1, hret1, hnl_at1, hfr1⟩
  simp only [List.cons.injEq, and_true] at heq1
  rcases heq1 with ⟨_, _, _, eo1⟩
  rw [← eo1] at hnl_at1 hfr1
  have hrg1 := lsstInRegs_upd hrg0 hr1 (by decide)
  have hs1_20 : s1.regs 20 = (nonloopEdges G).length := by rw [hr1, Function.update_self, hret1]
  have hs1_nl : ListAt s1.mem heap (nonloopEdges G) := by rw [hm1]; exact hnl_at1
  have hs1_pres : ∀ a < heap, s1.mem a = mem_orig a := fun a ha => by
    rw [hm1, hfr1 a (Or.inl ha)]
    rfl
  have hs1_zero : ZeroFrom s1.mem (heap + G.m) := fun a ha => by
    rw [hm1, hfr1 a (Or.inr ha)]
    exact hz_orig a (by omega)
  have hs1_tail : ListAt s1.mem tailArr (List.ofFn fun i : Fin G.m => G.tail i) :=
    htail_at.congr fun q hq1 hq2 => by
      rw [List.length_ofFn] at hq2
      exact hs1_pres q (lt_of_lt_of_le hq2 ht_lt)
  have hs1_head : ListAt s1.mem headArr (List.ofFn fun i : Fin G.m => G.head i) :=
    hhead_at.congr fun q hq1 hq2 => by
      rw [List.length_ofFn] at hq2
      exact hs1_pres q (lt_of_lt_of_le hq2 hh_lt)
  have hv_pos : ∀ e < G.m, 0 < v e := fun e he => (hwt_orig e he).2.2
  have he20 : (.reg 20 : Expr).eval w s1 = some (nonloopEdges G).length := Expr.eval_reg_of_eq hs1_20
  by_cases hnl0 : (nonloopEdges G).length = 0
  · have hstar_bd : ((Expr.reg 1).size + (Expr.reg 2).size + (Expr.reg 3).size + (Expr.reg 11).size + 2 +
        scanNonloopsCost G.m) + (starPairsCost G.n + 30) + 2 ≤
        lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h + 10 := by
      dsimp only [lsstCost, Expr.size]; omega
    obtain ⟨o, st', c1, hrun1, ⟨rfl, hpost1, hge1⟩, hc1⟩ :=
      lsst_star_runs_ret K_AN hGraph G v ℓ tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr
        outHdrPtr heap hG hw5 hoo_lt hob_lt hoh_lt hd_ob hd_oh hd_bh hv_pos hheap_m_w hrg1 hs1_pres hnl0
        (.bin .add (.reg 11) (.reg 1)) (heap + G.m)
        (fun s h11 h1s => Expr.eval_add (Expr.eval_reg_of_eq h11) (Expr.eval_reg_of_eq h1s) hheap_m_w)
        (by decide)
        (k := (Expr.reg 1).size + (Expr.reg 2).size + (Expr.reg 3).size + (Expr.reg 11).size + 2 +
          scanNonloopsCost G.m + 2)
        (T := lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h + 10)
        (by dsimp only [Expr.size] at hstar_bd ⊢; omega)
    have hm_le_sp : G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
      dsimp only [lsstSpace]; omega
    have hz_star : ZeroFrom st'.mem (heap + G.m) := fun a ha => by
      rw [hge1 a (by omega)]
      exact hs1_zero a ha
    refine ⟨.returned (heap + G.m), st', 1 + c1 + 1,
      runs_cond_iff.mpr ⟨0, c1, hnl0 ▸ he20, by simpa using hrun1, rfl⟩,
      ⟨heap + G.m, rfl, Nat.le_add_right _ _, Nat.add_le_add_left hm_le_sp _, hpost1, hz_star⟩, ?_⟩
    dsimp only [argsSize, Expr.size] at hc1 ⊢; omega
  · have hnl_m : (nonloopEdges G).length ≤ G.m := nonloopEdges_length_le G
    have hcsr_mono : buildCSRCost G.n (nonloopEdges G).length ≤ buildCSRCost G.n G.m := by
      dsimp only [buildCSRCost]; exact Nat.mul_le_mul_right _ (by omega)
    have hbfs_mono : bfsBridgesCost G.n (nonloopEdges G).length ≤ bfsBridgesCost G.n G.m := by
      dsimp only [bfsBridgesCost]; omega
    have hgen_bd : ((Expr.reg 1).size + (Expr.reg 2).size + (Expr.reg 3).size + (Expr.reg 11).size + 2 +
          scanNonloopsCost G.m) + 2 +
        (buildCSRCost G.n (nonloopEdges G).length + buildVertIdxCost G.n +
          bfsBridgesCost G.n (nonloopEdges G).length + 80) +
        (weightsCost G.m L + (110 * G.m + (4 * G.m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
          simDecodeCost Q_AN (w'Max c_AN G.n G.m L h) (2 * G.m) (4 * G.m) G.n L_sim
            (anCostBound K_AN G.n G.m L_sim h) + (12 + 198)) ≤
        lsstCost Q_AN K_AN c_AN G.n G.m L L_sim h + 10 := by
      dsimp only [lsstCost, Expr.size]
      linarith only [hcsr_mono, hbfs_mono]
    obtain ⟨o, st', c1, hrun1, hpost1, hc1⟩ :=
      lsst_graph_stage_runs (ω := ω) (Q_post := fun o st' =>
          ∃ hp_end, o = .returned hp_end ∧ heap ≤ hp_end ∧
            hp_end ≤ heap + lsstSpace Q_AN K_AN G.n G.m L_sim h ∧
            LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) st'.mem ∧
            ZeroFrom st'.mem hp_end)
        K_AN hGraph G tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap
        hG h1 hw hnl0 ht_lt hh_lt hheap_space hs1_tail hs1_head hs1_nl hs1_zero hs1_pres hrg1 hs1_20
        (tail := .assign 44 (.load (.bin .add (.reg 43) (.const 1))) ;; .ret (.reg 44))
        fun s_bfs B newHeap vListPtr inactPtr bPtr bfsHeap hnew hvL hinP hbP hbfsP hB_le
            hrgB hrB20 hrB22 hrB23 hrB24 hrB26 hrB29 hrB30 hrB31 hrB32 hnlB hinB hBB hvidxB hBr hzB hpresB =>
          lsst_weights_sim_runs_tail K_AN hp hAN G v ℓ P_fp tailArr headArr lenArr wtArr L L_sim
            outOrigPtr outBridgePtr outHdrPtr heap B newHeap vListPtr inactPtr bPtr bfsHeap
            hc_pos hG h1 hw hL1 hLsim hnl0 ht_lt hh_lt hlen_lt hwt_lt hoo_lt hob_lt hoh_lt hd_ob hd_oh hd_bh
            htail_at hhead_at hlen_orig hwt_orig hheap_space hnew hvL hinP hbP hbfsP hB_le
            hrgB hrB20 hrB22 hrB23 hrB24 hrB26 hrB29 hrB30 hrB31 hrB32 hnlB hinB hBB hvidxB hBr hzB hpresB
            (.assign 44 (.load (.bin .add (.reg 43) (.const 1))) ;; .ret (.reg 44)) 12
            (fun o st' => ∃ hp_end, o = .returned hp_end ∧ heap ≤ hp_end ∧
              hp_end ≤ heap + lsstSpace Q_AN K_AN G.n G.m L_sim h ∧
              LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) st'.mem ∧
              ZeroFrom st'.mem hp_end)
            (fun s12 simHeap hp_end k12 h43 hlo hc1 hheap_le hc1_le hz_hp hpost12 _ hk12 => by
              have hc1_w : simHeap + 1 < 2 ^ w := by omega
              have hhp_w : hp_end < 2 ^ w := by omega
              refine runs_seq_assign_step
                (Expr.eval_load_of_eq
                  (Expr.eval_add (Expr.eval_reg_of_eq h43) (Expr.eval_const hw1) hc1_w) hc1)
                rfl fun s13 hm13 _ hr13 => ?_
              have h44 : s13.regs 44 = hp_end := by rw [hr13, Function.update_self]
              refine runs_ret_le (Expr.eval_reg_of_eq h44)
                ⟨hp_end, rfl, hheap_le, hc1_le, hm13 ▸ hpost12, hm13 ▸ hz_hp⟩ ?_
              simp only [Expr.size] at hk12 ⊢
              omega)
            hgen_bd
    refine ⟨o, st', 1 + c1 + 1, runs_cond_iff.mpr ⟨(nonloopEdges G).length, c1, he20, by
      simp [hnl0]; exact hrun1, rfl⟩, hpost1, ?_⟩
    dsimp only [argsSize, Expr.size] at hc1 ⊢
    omega

theorem lsst_meetsContract {w h b c_AN : ℕ} {p Q_AN : Program} {K_AN : ℝ}
    (hp : p.HasAt b (lsstModule Q_AN b h))
    (hAN : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        WordRAM.RunsTo (WordRAM.wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) * (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight)) :
    MeetsContract w p (b + idxLSSTEntry) (lsstContract Q_AN c_AN K_AN w h) := by
  have hentry : p.procs[b + idxLSSTEntry]? = some (lsstEntryProc b h) := lsst_hasAt_entry hp
  refine meetsContract_of_runs hentry ?_
  rintro args mem_orig pos ω hwords ⟨G, v, ℓ, P_fp, tailArr, headArr, lenArr, wtArr, L, L_sim,
    outOrigPtr, outBridgePtr, outHdrPtr, heap, rfl, hc_pos, hG, h1, hw, hL1, hLsim,
    ht_lt, hh_lt, hlen_lt, hwt_lt, hoo_lt, hob_lt, hoh_lt, hd_ob, hd_oh, hd_bh,
    htail_at, hhead_at, hlen_orig, hwt_orig, hz_orig, hheap_space⟩
  obtain ⟨st', c, hrun, ⟨origEdges, bridgePairs, _, hhdr0, hhdr1, hlen1, hlen2, _, _, hlo, hbr, hlsst, hframe⟩,
    hz_end, hc⟩ :=
    lsst_runs (ω := ω) (pos := pos) hp hAN G v ℓ P_fp tailArr headArr lenArr wtArr L L_sim
      outOrigPtr outBridgePtr outHdrPtr heap mem_orig hwords hc_pos hG h1 hw hL1 hLsim ht_lt hh_lt hlen_lt hwt_lt
      hoo_lt hob_lt hoh_lt hd_ob hd_oh hd_bh htail_at hhead_at hlen_orig hwt_orig hz_orig hheap_space
  exact ⟨.returned 0, st', c, hrun, ⟨G, v, ℓ, P_fp, tailArr, headArr, lenArr, wtArr, L, L_sim,
    outOrigPtr, outBridgePtr, outHdrPtr, heap, origEdges, bridgePairs, rfl, rfl,
    hhdr0, hhdr1, hlen1, hlen2, hlo, hbr, hlsst, hframe, hz_end⟩, hc⟩

/-! ### Parameter selection and Main Theorem 2.2 WordRAM assembly -/

/-- Explicit host parameters `(h = 1, L_sim = lsstLSimMin c_AN G.n G.m L 1, w)` sufficient for
any instance `(G, v, ℓ)` with `L`-limb inputs above `heap`. -/
theorem lsst_param_selection (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (hc : 1 ≤ c_AN)
    (G : IndexedGraph) (L heap : ℕ) (_hL1 : 1 ≤ L) :
    let h := 1
    let L_sim := lsstLSimMin c_AN G.n G.m L h
    let w := max 5 (Nat.log 2 (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h) + 1)
    1 ≤ h ∧ 3 * h + 2 ≤ w ∧ lsstLSimMin c_AN G.n G.m L h ≤ L_sim ∧
      kWidthOf G.m L ≤ L_sim ∧ w'Max c_AN G.n G.m L h ≤ L_sim * h ∧
      heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w := by
  intro h L_sim w
  have hw5 : 5 ≤ w := le_max_left 5 _
  have hw_log : Nat.log 2 (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h) + 1 ≤ w := le_max_right 5 _
  have hlt_pow : heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _) (Nat.pow_le_pow_right (by norm_num) hw_log)
  obtain ⟨hk, hw', _⟩ := lsstLSimMin_bounds hc (le_refl 1) (le_refl L_sim)
  exact ⟨le_refl 1, by dsimp only [h]; omega, le_refl L_sim, hk, hw', hlt_pow⟩

/-- **Theorem 2.2** (page 7 of arXiv:2309.16629v1) on the WordRAM: from
`Cited.LowStretchSpanningTree` (`[AN19]`), there exist a deterministic host module family
`lsstModule Q_AN`, constants `c_AN ≥ 1`, `K_AN : ℝ`, and `C = 4 * max K_AN 1 + 5` such that:
1. For any host program `p` containing `lsstModule Q_AN b 1` at offset `b`, `b + idxLSSTEntry`
   deterministically meets `lsstContract Q_AN c_AN K_AN w 1` for all host word sizes `w`.
2. For any valid `IndexedGraph` `G` with positive `P_fp`-fixed-point `L`-limb weights `v, ℓ`,
   setting `L_sim = lsstLSimMin c_AN G.n G.m L 1` and `w ≥ max 5 (log₂(heap + lsstSpace) + 1)`,
   executing `p` at `b + idxLSSTEntry` deterministically returns `0`, writes a tree `(origEdges,
   bridgePairs)` whose `decodedTree` satisfies `IsLSST G.toMGraph ℓ v (C * log²(G.n + 2))`,
   preserves the caller memory frame, and runs within `lsstCost` steps (carrying
   `Cited.logLogFactor` and `Cited.weightFactor` via `anCostBound`). -/
theorem theorem_2_2_program :
    ∃ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      1 ≤ c_AN ∧
      (∀ (b : ℕ), ∀ s ∈ lsstModule Q_AN b 1, s.NoRand) ∧
      (∀ (w b : ℕ) (p : Program), p.HasAt b (lsstModule Q_AN b 1) →
        MeetsContract w p (b + idxLSSTEntry) (lsstContract Q_AN c_AN K_AN w 1)) ∧
      (∀ (b : ℕ) (p : Program) (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ)
          (tailArr headArr lenArr wtArr L outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
          (mem_orig : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
        let L_sim := lsstLSimMin c_AN G.n G.m L 1
        let w := max 5 (Nat.log 2 (heap + lsstSpace Q_AN K_AN G.n G.m L_sim 1) + 1)
        p.HasAt b (lsstModule Q_AN b 1) →
        G.Valid → 1 ≤ L →
        tailArr + G.m ≤ heap → headArr + G.m ≤ heap →
        lenArr + G.m * L ≤ heap → wtArr + G.m * L ≤ heap →
        outOrigPtr + G.n ≤ heap → outBridgePtr + 2 * G.n ≤ heap → outHdrPtr + 2 ≤ heap →
        DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n) →
        DisjointRanges outOrigPtr G.n outHdrPtr 2 →
        DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2 →
        ListAt mem_orig tailArr (List.ofFn fun i : Fin G.m => G.tail i) →
        ListAt mem_orig headArr (List.ofFn fun i : Fin G.m => G.head i) →
        (∀ e < G.m, Num.Valid mem_orig (lenArr + e * L) 1 L ∧
          Num.fixVal mem_orig (lenArr + e * L) 1 L P_fp = ℓ e ∧ 0 < ℓ e) →
        (∀ e < G.m, Num.Valid mem_orig (wtArr + e * L) 1 L ∧
          Num.fixVal mem_orig (wtArr + e * L) 1 L P_fp = v e ∧ 0 < v e) →
        ZeroFrom mem_orig heap →
        ∃ st' c origEdges bridgePairs,
          Runs w p ω (lsstEntryProc b 1)
            (startState [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
              outOrigPtr, outBridgePtr, outHdrPtr, heap] mem_orig pos)
            (.returned 0) st' c ∧
          st'.mem outHdrPtr = origEdges.length ∧
          st'.mem (outHdrPtr + 1) = bridgePairs.length ∧
          origEdges.length ≤ G.n ∧
          bridgePairs.length ≤ G.n ∧
          ListAt st'.mem outOrigPtr origEdges ∧
          ListAt st'.mem outBridgePtr (bridgePairs.flatMap fun q => [q.1, q.2]) ∧
          MinCostFlow.LSF.IsLSST G.toMGraph ℓ v
            ((4 * max K_AN 1 + 5) * Real.log (↑G.n + 2) ^ 2)
            (decodedTree G.n G.m G.tail G.head origEdges bridgePairs) ∧
          (∀ a < heap,
            (a < outOrigPtr ∨ outOrigPtr + G.n ≤ a) →
            (a < outBridgePtr ∨ outBridgePtr + 2 * G.n ≤ a) →
            (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → st'.mem a = mem_orig a) ∧
          ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim 1) ∧
          c ≤ lsstCost Q_AN K_AN c_AN G.n G.m L L_sim 1) := by
  obtain ⟨Q_AN, c_AN, K_AN, hc_pos, hAN⟩ := cited_c_pos_of_lsst
  refine ⟨Q_AN, c_AN, K_AN, hc_pos, (fun b => lsstModule_noRand Q_AN b 1),
    (fun w b p hp => lsst_meetsContract hp hAN), ?_⟩
  intro b p G v ℓ P_fp tailArr headArr lenArr wtArr L outOrigPtr outBridgePtr outHdrPtr heap
    mem_orig pos ω L_sim w hp hG hL1 ht_lt hh_lt hlen_lt hwt_lt hoo_lt hob_lt hoh_lt
    hd_ob hd_oh hd_bh htail_at hhead_at hlen_orig hwt_orig hz_orig
  obtain ⟨h1, hw, hLsim, _, _, hheap_space⟩ :=
    lsst_param_selection Q_AN c_AN K_AN hc_pos G L heap hL1
  have hLsim_le_sp : L_sim ≤ lsstSpace Q_AN K_AN G.n G.m L_sim 1 := by
    have h1' : L_sim ≤ (2 + 3 * (4 * G.m)) * L_sim :=
      Nat.le_mul_of_pos_left L_sim (Nat.add_pos_left (by decide) _)
    have h2' : (2 + 3 * (4 * G.m)) * L_sim ≤ lsstSpace Q_AN K_AN G.n G.m L_sim 1 := by
      dsimp only [lsstSpace]
      exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
    exact le_trans h1' h2'
  have hheap_lt_w : heap < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hheap_space
  have hm_le_sp : G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim 1 := by
    dsimp only [lsstSpace]; omega
  have h4n_w : 4 + 9 * G.n + 4 * G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim 1 := by
    dsimp only [lsstSpace]; omega
  have hwords : ∀ a ∈ [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
      outOrigPtr, outBridgePtr, outHdrPtr, heap], a < 2 ^ w := by
    intro a ha
    have hn_w : G.n < 2 ^ w :=
      lt_of_le_of_lt (le_trans (by omega) (le_trans h4n_w (Nat.le_add_left _ heap))) hheap_space
    have hm_w : G.m < 2 ^ w :=
      lt_of_le_of_lt (le_trans hm_le_sp (Nat.le_add_left _ heap)) hheap_space
    have hLsim_w : L_sim < 2 ^ w :=
      lt_of_le_of_lt (le_trans hLsim_le_sp (Nat.le_add_left _ heap)) hheap_space
    have hL_w : L < 2 ^ w := by
      have : L ≤ kWidthOf G.m L := by dsimp only [kWidthOf]; omega
      exact lt_of_le_of_lt (le_trans this (le_trans (le_max_left _ _) hLsim)) hLsim_w
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hn_w
    · exact hm_w
    · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) ht_lt) hheap_lt_w
    · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hh_lt) hheap_lt_w
    · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hlen_lt) hheap_lt_w
    · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hwt_lt) hheap_lt_w
    · exact hL_w
    · exact hLsim_w
    · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hoo_lt) hheap_lt_w
    · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hob_lt) hheap_lt_w
    · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hoh_lt) hheap_lt_w
    · exact hheap_lt_w
  obtain ⟨st', c, hrun, ⟨origEdges, bridgePairs, _, hhdr0, hhdr1, hlen1, hlen2, _, _, hlo, hbr, hlsst, hframe⟩,
    hz_end, hc⟩ :=
    lsst_runs (ω := ω) (pos := pos) hp hAN G v ℓ P_fp tailArr headArr lenArr wtArr L L_sim
      outOrigPtr outBridgePtr outHdrPtr heap mem_orig hwords hc_pos hG h1 hw hL1 hLsim ht_lt hh_lt hlen_lt hwt_lt
      hoo_lt hob_lt hoh_lt hd_ob hd_oh hd_bh htail_at hhead_at hlen_orig hwt_orig hz_orig hheap_space
  exact ⟨st', c, origEdges, bridgePairs, hrun, hhdr0, hhdr1, hlen1, hlen2, hlo, hbr, hlsst, hframe,
    hz_end, hc⟩

/-- Linear-factor corollary of `theorem_2_2_program`: every deterministic WordRAM run on a
valid instance `(G, v, ℓ)` with `L`-limb fixed-point weights completes in at most
`16000 * (G.m + G.n + 1) * lsstOverheadFactor Q_AN c_AN K_AN G.n G.m L` steps. -/
theorem theorem_2_2_program_linear :
    ∃ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      1 ≤ c_AN ∧
      (∀ (b : ℕ), ∀ s ∈ lsstModule Q_AN b 1, s.NoRand) ∧
      (∀ (w b : ℕ) (p : Program), p.HasAt b (lsstModule Q_AN b 1) →
        MeetsContract w p (b + idxLSSTEntry) (lsstContract Q_AN c_AN K_AN w 1)) ∧
      (∀ (b : ℕ) (p : Program) (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ)
          (tailArr headArr lenArr wtArr L outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
          (mem_orig : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
        let L_sim := lsstLSimMin c_AN G.n G.m L 1
        let w := max 5 (Nat.log 2 (heap + lsstSpace Q_AN K_AN G.n G.m L_sim 1) + 1)
        p.HasAt b (lsstModule Q_AN b 1) →
        G.Valid → 1 ≤ L →
        tailArr + G.m ≤ heap → headArr + G.m ≤ heap →
        lenArr + G.m * L ≤ heap → wtArr + G.m * L ≤ heap →
        outOrigPtr + G.n ≤ heap → outBridgePtr + 2 * G.n ≤ heap → outHdrPtr + 2 ≤ heap →
        DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n) →
        DisjointRanges outOrigPtr G.n outHdrPtr 2 →
        DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2 →
        ListAt mem_orig tailArr (List.ofFn fun i : Fin G.m => G.tail i) →
        ListAt mem_orig headArr (List.ofFn fun i : Fin G.m => G.head i) →
        (∀ e < G.m, Num.Valid mem_orig (lenArr + e * L) 1 L ∧
          Num.fixVal mem_orig (lenArr + e * L) 1 L P_fp = ℓ e ∧ 0 < ℓ e) →
        (∀ e < G.m, Num.Valid mem_orig (wtArr + e * L) 1 L ∧
          Num.fixVal mem_orig (wtArr + e * L) 1 L P_fp = v e ∧ 0 < v e) →
        ZeroFrom mem_orig heap →
        ∃ st' c origEdges bridgePairs,
          Runs w p ω (lsstEntryProc b 1)
            (startState [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
              outOrigPtr, outBridgePtr, outHdrPtr, heap] mem_orig pos)
            (.returned 0) st' c ∧
          st'.mem outHdrPtr = origEdges.length ∧
          st'.mem (outHdrPtr + 1) = bridgePairs.length ∧
          origEdges.length ≤ G.n ∧
          bridgePairs.length ≤ G.n ∧
          ListAt st'.mem outOrigPtr origEdges ∧
          ListAt st'.mem outBridgePtr (bridgePairs.flatMap fun q => [q.1, q.2]) ∧
          MinCostFlow.LSF.IsLSST G.toMGraph ℓ v
            ((4 * max K_AN 1 + 5) * Real.log (↑G.n + 2) ^ 2)
            (decodedTree G.n G.m G.tail G.head origEdges bridgePairs) ∧
          (∀ a < heap,
            (a < outOrigPtr ∨ outOrigPtr + G.n ≤ a) →
            (a < outBridgePtr ∨ outBridgePtr + 2 * G.n ≤ a) →
            (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → st'.mem a = mem_orig a) ∧
          ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim 1) ∧
          (c : ℝ) ≤ 16000 * ((G.m + G.n + 1 : ℕ) : ℝ) *
            lsstOverheadFactor Q_AN c_AN K_AN G.n G.m L) := by
  obtain ⟨Q_AN, c_AN, K_AN, hc_pos, hnorand, hmc, hmain⟩ := theorem_2_2_program
  refine ⟨Q_AN, c_AN, K_AN, hc_pos, hnorand, hmc, ?_⟩
  intro b p G v ℓ P_fp tailArr headArr lenArr wtArr L outOrigPtr outBridgePtr outHdrPtr heap
    mem_orig pos ω L_sim w hp hG hL1 ht_lt hh_lt hlen_lt hwt_lt hoo_lt hob_lt hoh_lt
    hd_ob hd_oh hd_bh htail_at hhead_at hlen_orig hwt_orig hz_orig
  obtain ⟨st', c, origEdges, bridgePairs, hrun, h0, h1, hlen1, hlen2, hlo, hbr, hlsst, hframe,
    hz_end, hc⟩ :=
    hmain b p G v ℓ P_fp tailArr headArr lenArr wtArr L outOrigPtr outBridgePtr outHdrPtr heap
      mem_orig pos ω hp hG hL1 ht_lt hh_lt hlen_lt hwt_lt hoo_lt hob_lt hoh_lt
      hd_ob hd_oh hd_bh htail_at hhead_at hlen_orig hwt_orig hz_orig
  exact ⟨st', c, origEdges, bridgePairs, hrun, h0, h1, hlen1, hlen2, hlo, hbr, hlsst, hframe, hz_end,
    le_trans (Nat.cast_le.mpr hc) (lsstCost_le_linear_factor Q_AN c_AN K_AN hG.1)⟩

end MinCostFlow.WideWord
