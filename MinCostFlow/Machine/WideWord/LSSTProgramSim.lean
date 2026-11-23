module

public import MinCostFlow.Machine.WideWord.LSSTProgramSimBase
public import MinCostFlow.Machine.WideWord.LSSTProgramStages
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Verification of the Theorem 2.2 WordRAM Program and Main Assembly

This file completes the verification of `lsstModule`:
- `lsst_weights_sim_runs`: general branch stage 2 chaining weight rounding/scaling
  (`weights_runs`), `buildGAug` limb encoding (`encodeGAug_runs`), `[AN19]` invocation,
  multi-word simulation + output decoding (`simDecode_runs`), and `concreteLSST_isLSST`.
- `lsst_meetsContract`: `lsstModule Q_AN b h` meets `lsstContract Q_AN c_AN K_AN w h`.
- `lsst_param_selection` and `theorem_2_2_program`: deterministic Theorem 2.2 WordRAM program
  and explicit parameter selection from `Cited.LowStretchSpanningTree`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

lemma lsst_weights_sim_runs {w h b c_AN : ℕ} {P Q_AN : Program} {ω : ℕ → Bool}
    {mem_orig : ℕ → ℕ} {st : State} {k T : ℕ}
    (K_AN : ℝ)
    (hp : P.HasAt b (lsstModule Q_AN b h))
    (hAN : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        WordRAM.RunsTo (WordRAM.wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) * (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ)
    (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (B : List ℕ) (newHeap vListPtr inactPtr bPtr bfsHeap : ℕ)
    (hc_pos : 1 ≤ c_AN) (hG : G.Valid) (h1 : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L)
    (hLsim : lsstLSimMin c_AN G.n G.m L h ≤ L_sim)
    (hnl_ne : (nonloopEdges G).length ≠ 0)
    (ht_lt : tailArr + G.m ≤ heap) (hh_lt : headArr + G.m ≤ heap)
    (hlen_lt : lenArr + G.m * L ≤ heap) (hwt_lt : wtArr + G.m * L ≤ heap)
    (hoo_lt : outOrigPtr + G.n ≤ heap) (hob_lt : outBridgePtr + 2 * G.n ≤ heap)
    (hoh_lt : outHdrPtr + 2 ≤ heap)
    (hd_ob : DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n))
    (hd_oh : DisjointRanges outOrigPtr G.n outHdrPtr 2)
    (hd_bh : DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2)
    (htail_orig : ListAt mem_orig tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhead_orig : ListAt mem_orig headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hlen_orig : ∀ e < G.m, Num.Valid mem_orig (lenArr + e * L) h L ∧
      Num.fixVal mem_orig (lenArr + e * L) h L P_fp = ℓ e ∧ 0 < ℓ e)
    (hwt_orig : ∀ e < G.m, Num.Valid mem_orig (wtArr + e * L) h L ∧
      Num.fixVal mem_orig (wtArr + e * L) h L P_fp = v e ∧ 0 < v e)
    (hheap_space : heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w)
    (hnew : newHeap = heap + G.m + 3 + 5 * G.n + 2 * (nonloopEdges G).length)
    (hvL : vListPtr = heap + G.m + 2)
    (hinP : inactPtr = vListPtr + G.n)
    (hbP : bPtr = newHeap + G.n)
    (hbfsP : bfsHeap = bPtr + G.n)
    (hB_le : B.length ≤ (activeVertsList G).length)
    (hrg : LSSTInRegs st G.n G.m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap)
    (hr20 : st.regs 20 = (nonloopEdges G).length)
    (hr22 : st.regs 22 = newHeap)
    (hr23 : st.regs 23 = (activeVertsList G).length)
    (hr24 : st.regs 24 = (inactiveVertsList G.n (activeVertsList G)).length)
    (hr26 : st.regs 26 = inactPtr)
    (hr29 : st.regs 29 = (activeVertsList G).headD 0)
    (hr30 : st.regs 30 = bPtr)
    (hr31 : st.regs 31 = bfsHeap)
    (hr32 : st.regs 32 = B.length)
    (hnl_at : ListAt st.mem heap (nonloopEdges G))
    (hinact_at : ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)))
    (hB_at : ListAt st.mem bPtr B)
    (hvidx_at : ∀ u ∈ activeVertsList G, st.mem (newHeap + u) = (activeVertsList G).idxOf u)
    (hBr : ∀ v' : ℕ → ℝ, (∀ e < G.m, 0 < v' e) →
      IsBridgeVerts
        (MinCostFlow.LSF.weightedCopyGraph
          { G.toMGraph with E := (nonloopEdges G).toFinset } v')
        (activeVertsList G).toFinset ((activeVertsList G).headD 0) B)
    (hz_h3 : ZeroFrom st.mem (bfsHeap + 2 * G.n))
    (hpres : ∀ a < heap, st.mem a = mem_orig a)
    (hk : k + (weightsCost G.m L + (110 * G.m + (4 * G.m) * (70 * L_sim + 110) +
        50 * L_sim + 120) +
      simDecodeCost Q_AN (w'Max c_AN G.n G.m L h) (2 * G.m) (4 * G.m) G.n L_sim
        (anCostBound K_AN G.n G.m L_sim h) + 200) ≤ T) :
    ∃ o st' c,
      Runs w P ω
        (.assign 33 (.bin .add (.reg 31) (.bin .mul (.const 2) (.reg 0))) ;;
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
         .ret (.const 0))
        st o st' c ∧
      (LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig o st'.mem ∧
        ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h)) ∧
      k + c ≤ T :=
  lsst_weights_sim_runs_tail K_AN hp hAN G v ℓ P_fp tailArr headArr lenArr wtArr L L_sim
    outOrigPtr outBridgePtr outHdrPtr heap B newHeap vListPtr inactPtr bPtr bfsHeap
    hc_pos hG h1 hw hL1 hLsim hnl_ne ht_lt hh_lt hlen_lt hwt_lt hoo_lt hob_lt hoh_lt
    hd_ob hd_oh hd_bh htail_orig hhead_orig hlen_orig hwt_orig hheap_space hnew hvL hinP hbP
    hbfsP hB_le hrg hr20 hr22 hr23 hr24 hr26 hr29 hr30 hr31 hr32 hnl_at hinact_at hB_at
    hvidx_at hBr hz_h3 hpres (.ret (.const 0)) 2
    (fun o st' => LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig o st'.mem ∧
      ZeroFrom st'.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h))
    (fun s12 _ _ _ _ _ _ _ _ _ hpost12 hz12 hk12 =>
      runs_ret_le (Expr.eval_const (Nat.two_pow_pos w)) ⟨hpost12, hz12⟩
        (by simp only [Expr.size] at hk12 ⊢; omega))
    hk

end MinCostFlow.WideWord
