module

public import MinCostFlow.LSF.Program.BatchTBlockOpsBase
import Mathlib.Tactic.Linarith

/-!
# `T`-Block Delete Procedure Verification (`BatchTBlockOps`)

Verifies `lsfTBlockDeleteProc` (`lsfTBlockDelete_meetsContract`), freezing active endpoint-match
trackers of a deleted tree edge into `tFrozenTail`/`tFrozenHead` while preserving `TBlockAt` in
`O(1)` time (`Lemma 5.4`, `arXiv:2309.16629v1` page 17 and Appendix A.1 page 48).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Verification of `lsfTBlockDeleteProc` -/

private lemma tBlock_delete_step_notMem {mem : ℕ → ℕ} {tPtr vCap eCap tM e : ℕ}
    {G T_cur T₀ : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hT : TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList)
    (he_lt : e < eCap) (hzero : mem (tIdxOfEdgeBase tPtr vCap tM + e) = 0) :
    TBlockAt mem tPtr vCap eCap tM (G.applyUpdate (.delete e)) T_cur T₀ π tOrigList := by
  rcases hT with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, htrack⟩
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, fun i hi => ?_⟩
  have hne : tOrigList[i] ≠ e := by
    intro hEq
    have h1' := hidx1 i hi (hEq ▸ he_lt)
    rw [hEq, hzero] at h1'; omega
  have htr := htrack i hi
  simp only [MGraph.applyUpdate, Finset.mem_erase, hne, ne_eq, not_false_eq_true, true_and]
  exact htr

private lemma tBlock_delete_post {mem mem' : ℕ → ℕ} {tPtr vCap eCap tM i e u v : ℕ}
    {G T_cur T₀ dgT : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hT : TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList)
    (hdgT_eq : DynGraphAt mem (tDgTPtr tPtr) vCap (2 * tM + 1) dgT ∧
      dgT.V = G.V ∧ (∀ k ∈ dgT.E, k < 2 * tM) ∧
      ∀ j (hj : j < tOrigList.length),
        let f := tOrigList[j]
        (2 * j ∈ dgT.E ↔ f ∈ G.E ∧ G.tail f = T_cur.tail f) ∧
        (2 * j ∈ dgT.E → dgT.tail (2 * j) = T_cur.tail f ∧ dgT.head (2 * j) = T_cur.tail f) ∧
        (2 * j ∉ dgT.E → mem (tFrozenTailBase tPtr vCap tM + j) = T_cur.tail f) ∧
        (2 * j + 1 ∈ dgT.E ↔ f ∈ G.E ∧ G.head f = T_cur.head f) ∧
        (2 * j + 1 ∈ dgT.E →
          dgT.tail (2 * j + 1) = T_cur.head f ∧ dgT.head (2 * j + 1) = T_cur.head f) ∧
        (2 * j + 1 ∉ dgT.E → mem (tFrozenHeadBase tPtr vCap tM + j) = T_cur.head f))
    (hi_len : i < tOrigList.length) (hi_eq : tOrigList[i] = e)
    (hu_eq : u = G.tail e) (hv_eq : v = G.head e)
    (hfr : ∀ a, ¬ (tDgTPtr tPtr ≤ a ∧ a < tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1)) →
      a ≠ tFrozenTailBase tPtr vCap tM + i → a ≠ tFrozenHeadBase tPtr vCap tM + i →
      mem' a = mem a)
    (hft_i : mem' (tFrozenTailBase tPtr vCap tM + i) = if 2 * i ∈ dgT.E then u else mem (tFrozenTailBase tPtr vCap tM + i))
    (hfh_i : mem' (tFrozenHeadBase tPtr vCap tM + i) = if 2 * i + 1 ∈ dgT.E then v else mem (tFrozenHeadBase tPtr vCap tM + i))
    (dgT2 : MGraph)
    (hdgT2_def : dgT2 =
      (let dgT1 := if 2 * i ∈ dgT.E then dgT.applyUpdate (.delete (2 * i)) else dgT
       if 2 * i + 1 ∈ dgT1.E then dgT1.applyUpdate (.delete (2 * i + 1)) else dgT1))
    (hdgT2_at : DynGraphAt mem' (tDgTPtr tPtr) vCap (2 * tM + 1) dgT2) :
    TBlockAt mem' tPtr vCap eCap tM (G.applyUpdate (.delete e)) T_cur T₀ π tOrigList := by
  rcases hT with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2, _⟩
  rcases hdgT_eq with ⟨_, hdgTV, hdgTE, htrack⟩
  have hi_lt : i < tM := by omega
  have hhd : ∀ off < tHdrSize, mem' (tPtr + off) = mem (tPtr + off) := fun off hoff =>
    hfr _ (by dsimp [tDgTPtr]; omega)
      (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr]; omega)
      (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr]; omega)
  have horig_eq : ∀ j < tM, mem' (tOrigIdBase tPtr vCap tM + j) = mem (tOrigIdBase tPtr vCap tM + j) :=
    fun j hj => hfr _ (by dsimp [tOrigIdBase]; omega)
      (by dsimp [tFrozenTailBase, tPiBase]; omega)
      (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega)
  have hpi_eq : ∀ j < tM, mem' (tPiBase tPtr vCap tM + j) = mem (tPiBase tPtr vCap tM + j) :=
    fun j hj => hfr _ (by dsimp [tPiBase, tOrigIdBase]; omega)
      (by dsimp [tFrozenTailBase]; omega)
      (by dsimp [tFrozenHeadBase, tFrozenTailBase]; omega)
  have hidx_eq : ∀ f < eCap, mem' (tIdxOfEdgeBase tPtr vCap tM + f) = mem (tIdxOfEdgeBase tPtr vCap tM + f) :=
    fun f _ => hfr _ (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase]; omega)
      (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase]; omega)
      (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase]; omega)
  have hdgT2_V : dgT2.V = (G.applyUpdate (.delete e)).V := by
    rw [hdgT2_def]; dsimp only
    by_cases h1' : 2 * i ∈ dgT.E <;> simp only [h1', ↓reduceIte] <;>
      (split_ifs <;> simp [MGraph.applyUpdate, hdgTV])
  have hdgT2_E : ∀ k ∈ dgT2.E, k < 2 * tM := by
    intro k hk; rw [hdgT2_def] at hk; dsimp only at hk
    by_cases h1' : 2 * i ∈ dgT.E
    · simp only [h1', ↓reduceIte] at hk
      split_ifs at hk
      · simp only [MGraph.applyUpdate, Finset.mem_erase] at hk; exact hdgTE k hk.2.2
      · simp only [MGraph.applyUpdate, Finset.mem_erase] at hk; exact hdgTE k hk.2
    · simp only [h1', ↓reduceIte] at hk
      split_ifs at hk
      · simp only [MGraph.applyUpdate, Finset.mem_erase] at hk; exact hdgTE k hk.2
      · exact hdgTE k hk
  refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1,
    (hhd _ (by decide)).trans h2, (hhd _ (by decide)).trans h3,
    (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
    (hhd _ (by decide)).trans h6, (hhd _ (by decide)).trans h7,
    hlen, hnd, hmemT,
    fun j hj => (horig_eq j (by omega)).trans (hLO j hj),
    fun j hj => (hpi_eq j (by simp at hj; omega)).trans (hLPi j hj),
    fun j hj hlt => (hidx_eq _ hlt).trans (hidx1 j hj hlt),
    fun f hf hne => by
      have hm := hidx_eq f hf; rw [hm] at hne ⊢; exact hidx2 f hf hne,
    dgT2, hdgT2_at, hdgT2_V, hdgT2_E, fun j hj => ?_⟩
  have htrj := htrack j hj
  by_cases hji : j = i
  · subst hji
    rw [hi_eq] at htrj ⊢
    have h2i_not2 : 2 * j ∉ dgT2.E := by
      rw [hdgT2_def]
      by_cases h1' : 2 * j ∈ dgT.E
      · simp only [h1', ↓reduceIte]
        split_ifs <;> simp [MGraph.applyUpdate]
      · simp only [h1', ↓reduceIte]
        split_ifs <;> simp [MGraph.applyUpdate, h1']
    have h2i1_not2 : 2 * j + 1 ∉ dgT2.E := by
      rw [hdgT2_def]; dsimp only
      by_cases h1' : 2 * j ∈ dgT.E
      · simp only [h1', ↓reduceIte]; split_ifs with h2'
        · simp [MGraph.applyUpdate]
        · exact h2'
      · simp only [h1', ↓reduceIte]; split_ifs with h2'
        · simp [MGraph.applyUpdate]
        · exact h2'
    refine ⟨by simp [h2i_not2, MGraph.applyUpdate], fun h => absurd h h2i_not2, fun _ => ?_,
      by simp [h2i1_not2, MGraph.applyUpdate], fun h => absurd h h2i1_not2, fun _ => ?_⟩
    · rw [hft_i]
      split_ifs with hm
      · rw [hu_eq]; exact (htrj.1.mp hm).2
      · exact htrj.2.2.1 hm
    · rw [hfh_i]
      split_ifs with hm
      · rw [hv_eq]; exact (htrj.2.2.2.1.mp hm).2
      · exact htrj.2.2.2.2.2 hm
  · have hf_ne : tOrigList[j] ≠ e := fun h => hji (hnd.getElem_inj_iff.mp (h.trans hi_eq.symm))
    have h2j_ne1 : 2 * j ≠ 2 * i := by omega
    have h2j_ne2 : 2 * j ≠ 2 * i + 1 := by omega
    have h2j1_ne1 : 2 * j + 1 ≠ 2 * i := by omega
    have h2j1_ne2 : 2 * j + 1 ≠ 2 * i + 1 := by omega
    have hft_j : mem' (tFrozenTailBase tPtr vCap tM + j) = mem (tFrozenTailBase tPtr vCap tM + j) :=
      hfr _ (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase]; omega) (by omega)
        (by dsimp [tFrozenHeadBase, tFrozenTailBase]; omega)
    have hfh_j : mem' (tFrozenHeadBase tPtr vCap tM + j) = mem (tFrozenHeadBase tPtr vCap tM + j) :=
      hfr _ (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase]; omega)
        (by dsimp [tFrozenHeadBase, tFrozenTailBase]; omega) (by omega)
    have hm2j : 2 * j ∈ dgT2.E ↔ 2 * j ∈ dgT.E := by
      rw [hdgT2_def]
      by_cases h1' : 2 * i ∈ dgT.E <;> simp only [h1', ↓reduceIte]
      · split_ifs <;> simp [MGraph.applyUpdate, h2j_ne1, h2j_ne2]
      · split_ifs
        · simp [MGraph.applyUpdate, h2j_ne2]
        · simp
    have hm2j1 : 2 * j + 1 ∈ dgT2.E ↔ 2 * j + 1 ∈ dgT.E := by
      rw [hdgT2_def]
      by_cases h1' : 2 * i ∈ dgT.E <;> simp only [h1', ↓reduceIte]
      · split_ifs
        · simp [MGraph.applyUpdate, h2j1_ne1, hji]
        · simp [MGraph.applyUpdate, h2j1_ne1]
      · split_ifs
        · simp [MGraph.applyUpdate, hji]
        · simp
    have htl : ∀ k, dgT2.tail k = dgT.tail k := fun k => by
      rw [hdgT2_def]; by_cases h1' : 2 * i ∈ dgT.E <;> simp only [h1', ↓reduceIte] <;>
        (split_ifs <;> rfl)
    have hhd_g : ∀ k, dgT2.head k = dgT.head k := fun k => by
      rw [hdgT2_def]; by_cases h1' : 2 * i ∈ dgT.E <;> simp only [h1', ↓reduceIte] <;>
        (split_ifs <;> rfl)
    simp only [hm2j, hm2j1, htl, hhd_g, hft_j, hfh_j, MGraph.applyUpdate, Finset.mem_erase,
      hf_ne, ne_eq, not_false_eq_true, true_and]
    exact htrj

/-- `lsfTBlockDeleteProc` meets `lsfTBlockDeleteContract`. -/
theorem lsfTBlockDelete_meetsContract {w idx idxDgDel vCap eCap tM : ℕ} {p : Program}
    {G T_cur T₀ : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (hp : p.procs[idx]? = some (lsfTBlockDeleteProc idxDgDel))
    (hDgDel : ∀ H, MeetsContract w p idxDgDel (dgDeleteEdgeContract w vCap (2 * tM + 1) H)) :
    MeetsContract w p idx (lsfTBlockDeleteContract w vCap eCap tM G T_cur T₀ π tOrigList) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨tPtr, e, u, v, rfl, hw16, hbound, hGval, heG, hu_eq, hv_eq, he_lt, hT⟩
  have hT_copy := hT
  rcases hT with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, htrack⟩
  have hdgT_lt : tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) < 2 ^ w := by
    dsimp [tDgTPtr, tBlockSize] at hbound ⊢; omega
  have hdgT_sub : tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tDgTPtr, tBlockSize]; omega
  have hidx_base_lt : tIdxOfEdgeBase tPtr vCap tM + eCap ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hft_base_lt : tFrozenTailBase tPtr vCap tM + tM ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hfh_base_lt : tFrozenHeadBase tPtr vCap tM + tM ≤ tPtr + tBlockSize vCap eCap tM := by
    dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hu_lt : u < vCap := hdgT.2.1 u (hdgTV.symm ▸ hu_eq ▸ (hGval e heG).1)
  have hv_lt : v < vCap := hdgT.2.1 v (hdgTV.symm ▸ hv_eq ▸ (hGval e heG).2)
  have hvCap_ltw : vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgT_lt; omega
  have heCap_ltw : eCap < 2 ^ w := by dsimp [tBlockSize] at hbound; omega
  have htM_ltw : tM < 2 ^ w := by dsimp [tBlockSize, dynGraphSize] at hbound; omega
  have h2tM1_ltw : 2 * tM + 1 < 2 ^ w := by dsimp [tBlockSize, dynGraphSize] at hbound; omega
  have htPtr_ltw : tPtr + tHdrSize < 2 ^ w := by dsimp [tBlockSize] at hbound; omega
  have hepBase_lt : dgEPresBase (tDgTPtr tPtr) vCap + (2 * tM + 1) < 2 ^ w := by
    dsimp [dgEPresBase, dynGraphSize] at hdgT_lt ⊢; omega
  have h7v_lt : 7 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgT_lt; omega
  have hdg4_lt : tDgTPtr tPtr + 4 < 2 ^ w := by dsimp [dynGraphSize] at hdgT_lt; omega
  have hst0 : (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 0 = tPtr ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 1 = vCap ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 2 = eCap ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 4 = e ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 5 = u ∧
      (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 6 = v := by
    simp [startState]
  rcases hst0 with ⟨hr0, hr1, hr2, hr4, hr5, hr6⟩
  have hgoal : ∃ o st' c,
      Runs w p ω (lsfTBlockDeleteProc idxDgDel)
        (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (lsfTBlockDeleteContract w vCap eCap tM G T_cur T₀ π tOrigList).post
          [tPtr, vCap, eCap, tM, e, u, v] mem 0 st'.mem) ∧
      0 + c ≤ 1100 := by
    dsimp only [lsfTBlockDeleteProc]
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tIdxOfEdgeBase tPtr vCap tM)
      (by dsimp [tOffIdxOfEdgePtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h6) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tDgTPtr tPtr)
      (by dsimp [tOffDgTPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h1) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tFrozenTailBase tPtr vCap tM)
      (by dsimp [tOffFrozenTailPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h4) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tFrozenHeadBase tPtr vCap tM)
      (by dsimp [tOffFrozenHeadPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h5) ?_
    have hepBase_lt0 : tDgTPtr tPtr + 4 + 7 * vCap < 2 ^ w := by
      dsimp [dgEPresBase] at hepBase_lt; omega
    refine runs_seq_assign_le (v := dgEPresBase (tDgTPtr tPtr) vCap) (by
      dsimp [dgEPresBase]; eval_expr) ?_
    refine runs_seq_cond_le (v := 1) (by
      rw [show (1 : ℕ) = BinOp.lt.eval e eCap by dsimp [BinOp.eval]; simp [he_lt]]
      exact Expr.eval_bin (by eval_expr) (by eval_expr)
        (by dsimp [BinOp.eval]; rw [ite_eq_left he_lt]; omega))
      ?_ (fun h0' => by omega)
    intro _
    refine runs_seq_assoc_le ?_
    have hidx0_ltw : tIdxOfEdgeBase tPtr vCap tM < 2 ^ w := by omega
    have hidx_e_ltw : tIdxOfEdgeBase tPtr vCap tM + e < 2 ^ w := by omega
    set idx1 := mem (tIdxOfEdgeBase tPtr vCap tM + e)
    by_cases hidx0 : idx1 = 0
    · refine runs_seq_assign_le (v := 0) ?_ ?_
      · exact Expr.eval_load_of_eq (by eval_expr) hidx0
      refine runs_seq_cond_le (v := 0) (by eval_expr) (fun h => absurd rfl h) ?_
      intro _
      refine runs_seq_nop_le ?_
      refine runs_ret_le (v := 0) (by eval_expr)
        ⟨rfl, tPtr, e, u, v, rfl, rfl, tBlock_delete_step_notMem hT_copy he_lt hidx0,
          fun _ _ => rfl⟩ ?_
      dsimp only [Expr.size]; omega
    · obtain ⟨i, hi_len, hi_eq, hidx_eq⟩ := hidx2 e he_lt hidx0
      have hi_lt : i < tM := by omega
      have hidx1_ltw : i + 1 < 2 ^ w := by omega
      refine runs_seq_assign_le (v := i + 1) ?_ ?_
      · exact Expr.eval_load_of_eq (by eval_expr) hidx_eq
      refine runs_seq_cond_le (v := i + 1) (by eval_expr) ?_ (fun h => by omega)
      intro _
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := i) (by
        rw [show some i = some (BinOp.sub.eval (i + 1) 1) from rfl]
        exact Expr.eval_bin (by eval_expr) (by eval_expr) (by dsimp [BinOp.eval]; omega)) ?_
      refine runs_seq_assoc_le ?_
      let dgT1 : MGraph := if 2 * i ∈ dgT.E then dgT.applyUpdate (.delete (2 * i)) else dgT
      let dgT2 : MGraph := if 2 * i + 1 ∈ dgT1.E then dgT1.applyUpdate (.delete (2 * i + 1)) else dgT1
      have h2i1_iff : 2 * i + 1 ∈ dgT1.E ↔ 2 * i + 1 ∈ dgT.E := by
        dsimp [dgT1]; split_ifs <;> simp [MGraph.applyUpdate]
      have hstep2 : ∀ (mem1 : ℕ → ℕ) (r14 : ℕ) (pos1 : ℕ) (k1 : ℕ),
          DynGraphAt mem1 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT1 →
          (∀ a, ¬ (tDgTPtr tPtr ≤ a ∧ a < tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1)) →
            a ≠ tFrozenTailBase tPtr vCap tM + i → mem1 a = mem a) →
          mem1 (tFrozenTailBase tPtr vCap tM + i) =
            (if 2 * i ∈ dgT.E then u else mem (tFrozenTailBase tPtr vCap tM + i)) →
          k1 ≤ 550 →
          ∃ o st' c,
            Runs w p ω
              (.cond (.load (.bin .add (.reg 11) (.bin .add (.bin .mul (.const 2) (.reg 13)) (.const 1))))
                (.store (.bin .add (.reg 10) (.reg 13)) (.reg 6) ;;
                 .call 14 idxDgDel
                   [.reg 8, .bin .add (.bin .mul (.const 2) (.reg 13)) (.const 1)])
                .nop ;; .ret (.const 0))
              { mem := mem1,
                regs := Function.update (Function.update (Function.update (Function.update
                  (Function.update (Function.update (Function.update (Function.update
                    (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs
                    7 (tIdxOfEdgeBase tPtr vCap tM)) 8 (tDgTPtr tPtr))
                    9 (tFrozenTailBase tPtr vCap tM)) 10 (tFrozenHeadBase tPtr vCap tM))
                    11 (dgEPresBase (tDgTPtr tPtr) vCap))
                    12 (i + 1)) 13 i) 14 r14,
                pos := pos1 } o st' c ∧
            (o = .returned 0 ∧
              (lsfTBlockDeleteContract w vCap eCap tM G T_cur T₀ π tOrigList).post
                [tPtr, vCap, eCap, tM, e, u, v] mem 0 st'.mem) ∧
            k1 + c ≤ 1100 := by
        intro mem1 r14 pos1 k1 hdgT1 hfr1 hft1 hk1
        have hep2 : mem1 (dgEPresBase (tDgTPtr tPtr) vCap + (2 * i + 1)) =
            if 2 * i + 1 ∈ dgT1.E then 1 else 0 :=
          hdgT1.2.2.2.2.2.2.2.2.2.2.2.1 (2 * i + 1) (by omega)
        refine runs_seq_cond_le (v := if 2 * i + 1 ∈ dgT1.E then 1 else 0) ?_ ?_ ?_
        · exact Expr.eval_load_of_eq (by eval_expr) hep2
        · intro hne
          refine runs_seq_assoc_le ?_
          have h2i1_in1 : 2 * i + 1 ∈ dgT1.E := by by_contra hc; simp [hc] at hne
          have h2i1_in : 2 * i + 1 ∈ dgT.E := h2i1_iff.mp h2i1_in1
          refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
          let mem1b := Function.update mem1 (tFrozenHeadBase tPtr vCap tM + i) v
          have hdgT1b : DynGraphAt mem1b (tDgTPtr tPtr) vCap (2 * tM + 1) dgT1 :=
            hdgT1.of_agree fun a _ ha2 =>
              Function.update_of_ne (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase] at *; omega) _ _
          have hpre_d2 : (dgDeleteEdgeContract w vCap (2 * tM + 1) dgT1).pre
              [tDgTPtr tPtr, 2 * i + 1] mem1b :=
            ⟨tDgTPtr tPtr, 2 * i + 1, rfl, hw16, hdgT_lt, hdgT1b⟩
          refine runs_seq_call_le (hDgDel dgT1) (by eval_expr)
            (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl <;> omega)
            hpre_d2 ?_
          intro _ mem2 _ hpost2
          rcases hpost2 with ⟨_, _, hargs2, _, hdgT2_raw, hfr2⟩
          simp only [List.cons.injEq, and_true] at hargs2
          rcases hargs2 with ⟨rfl, rfl⟩
          have hdgT2_at : DynGraphAt mem2 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT2 := by
            simpa only [dgT2, h2i1_in1, ↓reduceIte] using hdgT2_raw
          have hfr12 : ∀ a, ¬ (tDgTPtr tPtr ≤ a ∧ a < tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1)) →
              a ≠ tFrozenTailBase tPtr vCap tM + i → a ≠ tFrozenHeadBase tPtr vCap tM + i →
              mem2 a = mem a := fun a hnot hne1 hne2 =>
            (hfr2 a (by omega)).trans ((Function.update_of_ne hne2 _ _).trans (hfr1 a hnot hne1))
          have hft2 : mem2 (tFrozenTailBase tPtr vCap tM + i) =
              if 2 * i ∈ dgT.E then u else mem (tFrozenTailBase tPtr vCap tM + i) := by
            refine (hfr2 _ (Or.inr (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase]; omega))).trans ?_
            dsimp only [mem1b]
            rw [Function.update_of_ne (by dsimp [tFrozenHeadBase, tFrozenTailBase]; omega), hft1]
          have hfh2 : mem2 (tFrozenHeadBase tPtr vCap tM + i) =
              if 2 * i + 1 ∈ dgT.E then v else mem (tFrozenHeadBase tPtr vCap tM + i) := by
            simp only [h2i1_in, ↓reduceIte]
            refine (hfr2 _ (Or.inr (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase]; omega))).trans ?_
            exact Function.update_self _ _ _
          refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, tPtr, e, u, v, rfl, rfl,
            tBlock_delete_post hT_copy ⟨hdgT, hdgTV, hdgTE, htrack⟩ hi_len hi_eq hu_eq hv_eq
              hfr12 hft2 hfh2 dgT2 rfl hdgT2_at,
            fun a ha => hfr12 a (by dsimp [tDgTPtr, tBlockSize] at ha ⊢; omega)
              (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize] at ha ⊢; omega)
              (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize] at ha ⊢; omega)⟩ ?_
          dsimp only [dgDeleteEdgeContract, argsSize, Expr.size]; omega
        · intro heq0
          have h2i1_not1 : 2 * i + 1 ∉ dgT1.E := fun hc => by simp [hc] at heq0
          have h2i1_not : 2 * i + 1 ∉ dgT.E := fun hc => h2i1_not1 (h2i1_iff.mpr hc)
          have hdgT2_at : DynGraphAt mem1 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT2 := by
            simpa only [dgT2, h2i1_not1, ↓reduceIte] using hdgT1
          have hfh2 : mem1 (tFrozenHeadBase tPtr vCap tM + i) =
              if 2 * i + 1 ∈ dgT.E then v else mem (tFrozenHeadBase tPtr vCap tM + i) := by
            simp only [h2i1_not, ↓reduceIte]
            exact hfr1 _ (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase]; omega)
              (by dsimp [tFrozenHeadBase, tFrozenTailBase]; omega)
          refine runs_seq_nop_le ?_
          refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, tPtr, e, u, v, rfl, rfl,
            tBlock_delete_post hT_copy ⟨hdgT, hdgTV, hdgTE, htrack⟩ hi_len hi_eq hu_eq hv_eq
              (fun a hnot hne1 _ => hfr1 a hnot hne1) hft1 hfh2 dgT2 rfl hdgT2_at,
            fun a ha => hfr1 a (by dsimp [tDgTPtr, tBlockSize] at ha ⊢; omega)
              (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize] at ha ⊢; omega)⟩ ?_
          dsimp only [Expr.size]; omega
      have hep1 : mem (dgEPresBase (tDgTPtr tPtr) vCap + 2 * i) = if 2 * i ∈ dgT.E then 1 else 0 :=
        hdgT.2.2.2.2.2.2.2.2.2.2.2.1 (2 * i) (by omega)
      refine runs_seq_cond_le (v := if 2 * i ∈ dgT.E then 1 else 0) ?_ ?_ ?_
      · exact Expr.eval_load_of_eq (by eval_expr) hep1
      · intro hne
        refine runs_seq_assoc_le ?_
        have h2i_in : 2 * i ∈ dgT.E := by by_contra hc; simp [hc] at hne
        refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
        let mem0b := Function.update mem (tFrozenTailBase tPtr vCap tM + i) u
        have hdgTb : DynGraphAt mem0b (tDgTPtr tPtr) vCap (2 * tM + 1) dgT :=
          hdgT.of_agree fun a _ ha2 =>
            Function.update_of_ne (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase] at *; omega) _ _
        have hpre_d1 : (dgDeleteEdgeContract w vCap (2 * tM + 1) dgT).pre
            [tDgTPtr tPtr, 2 * i] mem0b :=
          ⟨tDgTPtr tPtr, 2 * i, rfl, hw16, hdgT_lt, hdgTb⟩
        refine runs_seq_call_le (hDgDel dgT) (by eval_expr)
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl <;> omega)
          hpre_d1 ?_
        intro r14 mem1 pos1 hpost1
        rcases hpost1 with ⟨_, _, hargs1, _, hdgT1_raw, hfr1⟩
        simp only [List.cons.injEq, and_true] at hargs1
        rcases hargs1 with ⟨rfl, rfl⟩
        have hdgT1_at : DynGraphAt mem1 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT1 := by
          simpa only [dgT1, h2i_in, ↓reduceIte] using hdgT1_raw
        have hfr1' : ∀ a, ¬ (tDgTPtr tPtr ≤ a ∧ a < tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1)) →
            a ≠ tFrozenTailBase tPtr vCap tM + i → mem1 a = mem a := fun a hnot hne1 =>
          (hfr1 a (by omega)).trans (Function.update_of_ne hne1 _ _)
        have hft1 : mem1 (tFrozenTailBase tPtr vCap tM + i) =
            if 2 * i ∈ dgT.E then u else mem (tFrozenTailBase tPtr vCap tM + i) := by
          simp only [h2i_in, ↓reduceIte]
          exact (hfr1 _ (Or.inr (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase]; omega))).trans
            (Function.update_self _ _ _)
        exact hstep2 mem1 r14 pos1 _ hdgT1_at hfr1' hft1
          (by dsimp only [dgDeleteEdgeContract, argsSize, Expr.size]; omega)
      · intro heq0
        have h2i_not : 2 * i ∉ dgT.E := fun hc => by simp [hc] at heq0
        have hdgT1_at : DynGraphAt mem (tDgTPtr tPtr) vCap (2 * tM + 1) dgT1 := by
          simpa only [dgT1, h2i_not, ↓reduceIte] using hdgT
        refine runs_seq_nop_le ?_
        have hreg_eq : (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update
              (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs
              7 (tIdxOfEdgeBase tPtr vCap tM)) 8 (tDgTPtr tPtr))
              9 (tFrozenTailBase tPtr vCap tM)) 10 (tFrozenHeadBase tPtr vCap tM))
              11 (dgEPresBase (tDgTPtr tPtr) vCap))
              12 (i + 1)) 13 i) =
            Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
              (startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs
              7 (tIdxOfEdgeBase tPtr vCap tM)) 8 (tDgTPtr tPtr))
              9 (tFrozenTailBase tPtr vCap tM)) 10 (tFrozenHeadBase tPtr vCap tM))
              11 (dgEPresBase (tDgTPtr tPtr) vCap))
              12 (i + 1)) 13 i) 14
              ((startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 14) := by
          funext r; by_cases hr : r = 14
          · subst hr; simp
          · simp [Function.update_of_ne hr]
        rw [hreg_eq]
        exact hstep2 mem ((startState [tPtr, vCap, eCap, tM, e, u, v] mem pos).regs 14) pos _
          hdgT1_at (fun _ _ _ => rfl) (by simp [h2i_not]) (by dsimp only [Expr.size]; omega)
  obtain ⟨o, st', c, hrun, ⟨rfl, hpost⟩, hc⟩ := hgoal
  exact ⟨lsfTBlockDeleteProc idxDgDel, hp, .returned 0, st', c, hrun, hpost, by simpa [lsfTBlockDeleteContract] using hc⟩

end

end MinCostFlow.LSF.Program
