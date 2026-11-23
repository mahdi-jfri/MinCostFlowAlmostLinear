module

public import MinCostFlow.SparseCore.Program.LSFWindowRepackDefs
import WordRAM.Tactic

/-!
# Sparse Repack Verification for `WBlockAt` and `WstrAt`

Proves `repackWBlockProc_runs` and `repackWstrProc_runs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## Verification of `repackWBlockProc` -/

lemma repackWBlockProc_runs {w : ℕ} {p : Program} {bCopy : ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {guestBase wPtr_g dstW n0 : ℕ} {W_init : Finset (Finset ℕ)} {F₀ : MGraph}
    (hw : 20 < 2 ^ w)
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hMemW : ∀ a, guestBase + wPtr_g ≤ a → a < guestBase + wPtr_g + wBlockSize n0 → mem a < 2 ^ w)
    (hW : WBlockAt (fun x => mem (guestBase + x)) wPtr_g n0 W_init F₀)
    (hsrc_w : guestBase + wPtr_g + wBlockSize n0 < 2 ^ w)
    (hdst_w : dstW + wBlockSize n0 < 2 ^ w)
    (hdisj : guestBase + wPtr_g + wBlockSize n0 ≤ dstW ∨ dstW + wBlockSize n0 ≤ guestBase + wPtr_g) :
    ∃ st' c,
      Runs w p ω (repackWBlockProc bCopy) (startState [guestBase + wPtr_g, dstW, n0] mem pos)
        (.returned 0) st' c ∧
      WBlockAt st'.mem dstW n0 W_init F₀ ∧
      (∀ a, a < dstW ∨ dstW + wBlockSize n0 ≤ a → st'.mem a = mem a) ∧
      c ≤ 105 * n0 + 220 := by
  set srcW := guestBase + wPtr_g
  suffices hmain : ∃ o st' c,
      Runs w p ω (repackWBlockProc bCopy) (startState [srcW, dstW, n0] mem pos) o st' c ∧
      (o = .returned 0 ∧ WBlockAt st'.mem dstW n0 W_init F₀ ∧
        (∀ a, a < dstW ∨ dstW + wBlockSize n0 ≤ a → st'.mem a = mem a)) ∧
      c ≤ 105 * n0 + 220 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, hc⟩
  have hoffs : wOffNumPieces = 0 ∧ wOffVertOffPtr = 1 ∧ wOffVertsPtr = 2 ∧
      wOffEdgeOffPtr = 3 ∧ wOffEdgesPtr = 4 ∧ wOffTotalVerts = 5 ∧ wOffTotalEdges = 6 ∧
      wHdrSize = 7 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsz : wBlockSize n0 = 7 + (n0 + 1) + 2 * n0 + (n0 + 1) + n0 := rfl
  have hnpW : mem (srcW + wOffNumPieces) < 2 ^ w := hMemW _ (by omega) (by omega)
  have htvW : mem (srcW + wOffTotalVerts) < 2 ^ w := hMemW _ (by omega) (by omega)
  have hteW : mem (srcW + wOffTotalEdges) < 2 ^ w := hMemW _ (by omega) (by omega)
  refine runs_start_le ?_
  unfold repackWBlockProc
  refine runs_seq_assign_le (v := wVertOffBase dstW) (by dsimp [wVertOffBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := wVertsBase dstW n0) (by dsimp [wVertsBase, wVertOffBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := wEdgeOffBase dstW n0) (by dsimp [wEdgeOffBase, wVertsBase, wVertOffBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := wEdgesBase dstW n0) (by dsimp [wEdgesBase, wEdgeOffBase, wVertsBase, wVertOffBase]; eval_expr) ?_
  refine runs_seq_store_le (x := dstW + wOffNumPieces) (v := mem (srcW + wOffNumPieces)) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := dstW + wOffVertOffPtr) (v := wVertOffBase dstW) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := dstW + wOffVertsPtr) (v := wVertsBase dstW n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := dstW + wOffEdgeOffPtr) (v := wEdgeOffBase dstW n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := dstW + wOffEdgesPtr) (v := wEdgesBase dstW n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := dstW + wOffTotalVerts) (v := mem (srcW + wOffTotalVerts))
    (by eval_expr)
    (by have hrd : Function.update (Function.update (Function.update (Function.update (Function.update mem
            (dstW + wOffNumPieces) (mem (srcW + wOffNumPieces)))
            (dstW + wOffVertOffPtr) (wVertOffBase dstW)) (dstW + wOffVertsPtr) (wVertsBase dstW n0))
            (dstW + wOffEdgeOffPtr) (wEdgeOffBase dstW n0)) (dstW + wOffEdgesPtr) (wEdgesBase dstW n0)
            (srcW + wOffTotalVerts) = mem (srcW + wOffTotalVerts) := by
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        eval_expr) ?_
  refine runs_seq_store_le (x := dstW + wOffTotalEdges) (v := mem (srcW + wOffTotalEdges))
    (by eval_expr)
    (by have hrd : Function.update (Function.update (Function.update (Function.update (Function.update (Function.update mem
            (dstW + wOffNumPieces) (mem (srcW + wOffNumPieces)))
            (dstW + wOffVertOffPtr) (wVertOffBase dstW)) (dstW + wOffVertsPtr) (wVertsBase dstW n0))
            (dstW + wOffEdgeOffPtr) (wEdgeOffBase dstW n0)) (dstW + wOffEdgesPtr) (wEdgesBase dstW n0))
            (dstW + wOffTotalVerts) (mem (srcW + wOffTotalVerts)) (srcW + wOffTotalEdges) = mem (srcW + wOffTotalEdges) := by
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        eval_expr) ?_
  set mem0 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update mem (dstW + wOffNumPieces) (mem (srcW + wOffNumPieces)))
      (dstW + wOffVertOffPtr) (wVertOffBase dstW)) (dstW + wOffVertsPtr) (wVertsBase dstW n0))
      (dstW + wOffEdgeOffPtr) (wEdgeOffBase dstW n0)) (dstW + wOffEdgesPtr) (wEdgesBase dstW n0))
      (dstW + wOffTotalVerts) (mem (srcW + wOffTotalVerts)))
      (dstW + wOffTotalEdges) (mem (srcW + wOffTotalEdges))
  have hmem0_out : ∀ a, a < dstW ∨ dstW + wHdrSize ≤ a → mem0 a = mem a := fun a ha => by
    dsimp only [mem0]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine runs_seq_call_le hCopy
    (by eval_expr)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl
        · dsimp [wVertOffBase]; omega
        · omega
        · omega)
    ⟨wVertOffBase dstW, srcW + wHdrSize, 5 * n0 + 2, rfl,
      by dsimp [wVertOffBase]; omega, by omega, by dsimp [wVertOffBase]; omega⟩
    (fun _ mem1 pos1 hpost1 => ?_)
  rcases hpost1 with ⟨_, _, _, harg1, _, hcp1, hfr1⟩
  cases harg1
  refine runs_ret_le (by eval_expr) ⟨rfl, ?_, fun a ha =>
    (hfr1 a (by dsimp [wVertOffBase]; omega)).trans (hmem0_out a (by omega))⟩
    (by simp [memCopyContract, argsSize, Expr.size]; omega)
  have hpay : ∀ off < 5 * n0 + 2, mem1 (dstW + wHdrSize + off) = mem (srcW + wHdrSize + off) := by
    intro off hoff
    have h1 := hcp1 off hoff
    dsimp [wVertOffBase] at h1
    exact h1.trans (hmem0_out (srcW + wHdrSize + off) (by omega))
  have hhdr_eq : ∀ off < wHdrSize, mem1 (dstW + off) = mem0 (dstW + off) := fun off hoff =>
    hfr1 (dstW + off) (Or.inl (by dsimp [wVertOffBase]; omega))
  have hnp : mem1 (dstW + wOffNumPieces) = mem (guestBase + (wPtr_g + wOffNumPieces)) := by
    rw [hhdr_eq _ (by omega)]; dsimp only [mem0, srcW]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self, Nat.add_assoc]
  have htv : mem1 (dstW + wOffTotalVerts) = mem (guestBase + (wPtr_g + wOffTotalVerts)) := by
    rw [hhdr_eq _ (by omega)]; dsimp only [mem0, srcW]
    rw [Function.update_of_ne (by omega), Function.update_self, Nat.add_assoc]
  have hte : mem1 (dstW + wOffTotalEdges) = mem (guestBase + (wPtr_g + wOffTotalEdges)) := by
    rw [hhdr_eq _ (by omega)]; dsimp only [mem0, srcW]
    rw [Function.update_self, Nat.add_assoc]
  dsimp only [WBlockAt] at hW ⊢
  rw [hnp, htv, hte]
  rcases hW with ⟨_, _, _, _, hnp_le, htv_le, hte_le, hvo0, hvoN, heo0, heoN,
    wList, hwlen, hwnd, hwmem, hpieces⟩
  have hvo : ∀ j ≤ n0, mem1 (wVertOffBase dstW + j) = mem (guestBase + (wVertOffBase wPtr_g + j)) := fun j hj => by
    have := hpay j (by omega)
    simpa [srcW, wVertOffBase, Nat.add_assoc] using this
  have heo : ∀ j ≤ n0, mem1 (wEdgeOffBase dstW n0 + j) = mem (guestBase + (wEdgeOffBase wPtr_g n0 + j)) := fun j hj => by
    have := hpay (3 * n0 + 1 + j) (by omega)
    simpa [srcW, wEdgeOffBase, wVertsBase, wVertOffBase, Nat.add_assoc, show n0 + 1 + 2 * n0 = 3 * n0 + 1 by omega] using this
  refine ⟨?_, ?_, ?_, ?_, hnp_le, htv_le, hte_le,
    (hvo 0 (Nat.zero_le _)).trans hvo0, (hvo _ hnp_le).trans hvoN,
    (heo 0 (Nat.zero_le _)).trans heo0, (heo _ hnp_le).trans heoN,
    wList, hwlen, hwnd, hwmem, ?_⟩
  · rw [hhdr_eq _ (by omega)]; dsimp only [mem0]
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])
  · rw [hhdr_eq _ (by omega)]; dsimp only [mem0]
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])
  · rw [hhdr_eq _ (by omega)]; dsimp only [mem0]
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])
  · rw [hhdr_eq _ (by omega)]; dsimp only [mem0]
    repeat (first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)])
  · intro i hi
    have hi_n0 : i + 1 ≤ n0 := by omega
    rw [hvo i (by omega), hvo (i + 1) hi_n0, heo i (by omega), heo (i + 1) hi_n0]
    rcases hpieces i hi with ⟨h1, h2, h3, h4, vL, hvlen, hvnd, hvmem, hvLA, eL, helen, hend, hemem, heLA⟩
    refine ⟨h1, h2, h3, h4, vL, hvlen, hvnd, hvmem, fun j hj => ?_, eL, helen, hend, hemem, fun j hj => ?_⟩
    · have hjlt : mem (guestBase + (wVertOffBase wPtr_g + i)) + j < 2 * n0 := by omega
      have hp := hpay (n0 + 1 + (mem (guestBase + (wVertOffBase wPtr_g + i)) + j)) (by omega)
      have heq1 : dstW + wHdrSize + (n0 + 1 + (mem (guestBase + (wVertOffBase wPtr_g + i)) + j)) =
          wVertsBase dstW n0 + mem (guestBase + (wVertOffBase wPtr_g + i)) + j := by dsimp [wVertsBase, wVertOffBase]; omega
      have heq2 : srcW + wHdrSize + (n0 + 1 + (mem (guestBase + (wVertOffBase wPtr_g + i)) + j)) =
          guestBase + (wVertsBase wPtr_g n0 + mem (guestBase + (wVertOffBase wPtr_g + i)) + j) := by dsimp [srcW, wVertsBase, wVertOffBase]; omega
      rw [heq1, heq2] at hp; exact hp.trans (hvLA j hj)
    · have hjlt : mem (guestBase + (wEdgeOffBase wPtr_g n0 + i)) + j < n0 := by omega
      have hp := hpay (4 * n0 + 2 + (mem (guestBase + (wEdgeOffBase wPtr_g n0 + i)) + j)) (by omega)
      have heq1 : dstW + wHdrSize + (4 * n0 + 2 + (mem (guestBase + (wEdgeOffBase wPtr_g n0 + i)) + j)) =
          wEdgesBase dstW n0 + mem (guestBase + (wEdgeOffBase wPtr_g n0 + i)) + j := by dsimp [wEdgesBase, wEdgeOffBase, wVertsBase, wVertOffBase]; omega
      have heq2 : srcW + wHdrSize + (4 * n0 + 2 + (mem (guestBase + (wEdgeOffBase wPtr_g n0 + i)) + j)) =
          guestBase + (wEdgesBase wPtr_g n0 + mem (guestBase + (wEdgeOffBase wPtr_g n0 + i)) + j) := by dsimp [srcW, wEdgesBase, wEdgeOffBase, wVertsBase, wVertOffBase]; omega
      rw [heq1, heq2] at hp; exact hp.trans (heLA j hj)

/-! ## Verification of `repackWstrProc` -/

lemma repackWstrProc_runs {w : ℕ} {p : Program} {bCopy : ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} {srcDgG srcNum srcDen dstNum dstDen vCap_g eCap_g eCap_h h L_w_g L_w_h : ℕ}
    {G : MGraph} {wstr : ℕ → ℝ}
    (hw : 20 < 2 ^ w)
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hh1 : 1 ≤ h) (hLw_le : L_w_g ≤ L_w_h) (heCap : eCap_g ≤ eCap_h)
    (hdgG : DynGraphAt mem srcDgG vCap_g eCap_g G)
    (hWstr : WstrAt mem srcNum srcDen eCap_g h L_w_g G wstr)
    (hdg_w : srcDgG + dynGraphSize vCap_g eCap_g < 2 ^ w)
    (hsrcN_w : srcNum + eCap_g * L_w_g < 2 ^ w)
    (hsrcD_w : srcDen + eCap_g * L_w_g < 2 ^ w)
    (hdstN_w : dstNum + eCap_h * L_w_h < 2 ^ w)
    (hdstD_w : dstDen + eCap_h * L_w_h < 2 ^ w)
    (hLwh_w : L_w_h < 2 ^ w)
    (hdst_disj : dstNum + eCap_h * L_w_h ≤ dstDen)
    (hsrc_lt_dst : srcDgG + dynGraphSize vCap_g eCap_g ≤ dstNum ∧
                   srcNum + eCap_g * L_w_g ≤ dstNum ∧
                   srcDen + eCap_g * L_w_g ≤ dstNum)
    (hzeroN : ∀ a, dstNum ≤ a → a < dstNum + eCap_h * L_w_h → mem a = 0)
    (hzeroD : ∀ a, dstDen ≤ a → a < dstDen + eCap_h * L_w_h → mem a = 0) :
    ∃ st' c,
      Runs w p ω (repackWstrProc bCopy)
        (startState [srcDgG, srcNum, srcDen, L_w_g, dstNum, dstDen, L_w_h] mem pos)
        (.returned 0) st' c ∧
      WstrAt st'.mem dstNum dstDen eCap_h h L_w_h G wstr ∧
      (∀ a, a < dstNum ∨ (dstNum + eCap_h * L_w_h ≤ a ∧ a < dstDen) ∨
        dstDen + eCap_h * L_w_h ≤ a → st'.mem a = mem a) ∧
      c ≤ G.m * (40 * L_w_g + 70) + 80 := by
  suffices hmain : ∃ o st' c,
      Runs w p ω (repackWstrProc bCopy)
        (startState [srcDgG, srcNum, srcDen, L_w_g, dstNum, dstDen, L_w_h] mem pos) o st' c ∧
      (o = .returned 0 ∧ WstrAt st'.mem dstNum dstDen eCap_h h L_w_h G wstr ∧
        (∀ a, a < dstNum ∨ (dstNum + eCap_h * L_w_h ≤ a ∧ a < dstDen) ∨
          dstDen + eCap_h * L_w_h ≤ a → st'.mem a = mem a)) ∧
      c ≤ G.m * (40 * L_w_g + 70) + 80 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, hc⟩
  rcases hdgG with ⟨_, _, helt, hdgV, hdgE, _, hdgM, _, _, _, _, _,
    ⟨eL, heL_len, heL_nd, heL_mem, heL_LA, _⟩, _, _⟩
  rcases hWstr with ⟨hhLg, hLg1, hWstrE⟩
  have hoffs : dgVCapOff = 0 ∧ dgECapOff = 1 ∧ dgMOff = 3 := ⟨rfl, rfl, rfl⟩
  have hdg_sz : dynGraphSize vCap_g eCap_g = 4 + 7 * vCap_g + 9 * eCap_g := rfl
  have hGm_le : G.m ≤ eCap_g := by
    have hsub : G.E ⊆ Finset.range eCap_g := fun e he => Finset.mem_range.mpr (helt e he)
    calc G.m = G.E.card := rfl
      _ ≤ (Finset.range eCap_g).card := Finset.card_le_card hsub
      _ = eCap_g := Finset.card_range eCap_g
  refine runs_start_le ?_
  unfold repackWstrProc
  refine runs_seq_assign_le (v := vCap_g) (by eval_expr) ?_
  refine runs_seq_assign_le (v := eCap_g) (by eval_expr) ?_
  refine runs_seq_assign_le (v := G.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := dgEListBase srcDgG vCap_g eCap_g) (by dsimp [dgEListBase]; eval_expr) ?_
  let WInv : ℕ → State → Prop := fun i st =>
    st.regs 1 = srcNum ∧ st.regs 2 = srcDen ∧ st.regs 3 = L_w_g ∧
    st.regs 4 = dstNum ∧ st.regs 5 = dstDen ∧ st.regs 6 = L_w_h ∧
    st.regs 9 = G.m ∧ st.regs 10 = dgEListBase srcDgG vCap_g eCap_g ∧ st.regs 11 = i ∧
    (∀ a, a < dstNum ∨ (dstNum + eCap_h * L_w_h ≤ a ∧ a < dstDen) ∨
      dstDen + eCap_h * L_w_h ≤ a → st.mem a = mem a) ∧
    (∀ j (hj : j < i), ∀ (hj' : j < eL.length),
      let e := eL[j]
      (∀ t < L_w_g, st.mem (dstNum + e * L_w_h + t) = mem (srcNum + e * L_w_g + t) ∧
                    st.mem (dstDen + e * L_w_h + t) = mem (srcDen + e * L_w_g + t)) ∧
      (∀ t, L_w_g ≤ t → t < L_w_h → st.mem (dstNum + e * L_w_h + t) = 0 ∧
                                     st.mem (dstDen + e * L_w_h + t) = 0)) ∧
    (∀ e < eCap_h, (∀ j (hj : j < i), ∀ (hj' : j < eL.length), eL[j] ≠ e) →
      ∀ t < L_w_h, st.mem (dstNum + e * L_w_h + t) = 0 ∧ st.mem (dstDen + e * L_w_h + t) = 0)
  have hwLoop : Triple w p
      (fun st => st.regs 1 = srcNum ∧ st.regs 2 = srcDen ∧ st.regs 3 = L_w_g ∧
        st.regs 4 = dstNum ∧ st.regs 5 = dstDen ∧ st.regs 6 = L_w_h ∧
        st.regs 9 = G.m ∧ st.regs 10 = dgEListBase srcDgG vCap_g eCap_g ∧ st.mem = mem)
      (forRange 11 (.const 0) (.reg 9)
        (.assign 12 (.load (.bin .add (.reg 10) (.reg 11))) ;;
         .call 13 bCopy
           [.bin .add (.reg 4) (.bin .mul (.reg 12) (.reg 6)),
            .bin .add (.reg 1) (.bin .mul (.reg 12) (.reg 3)),
            .reg 3] ;;
         .call 13 bCopy
           [.bin .add (.reg 5) (.bin .mul (.reg 12) (.reg 6)),
            .bin .add (.reg 2) (.bin .mul (.reg 12) (.reg 3)),
            .reg 3]))
      (normalPost (WInv G.m)) (fun _ => G.m * (40 * L_w_g + 70) + 7) := by
    refine (Triple.forRange_const (40 * L_w_g + 60) 0 G.m (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨r1, r2, r3, r4, r5, r6, r9, r10, hmeq⟩
        refine ⟨by eval_expr, r1, r2, r3, r4, r5, r6, r9, r10, by simp,
          fun _ _ => by rw [hmeq], fun j hj _ => by omega, fun e he _ t ht => ?_⟩
        rw [hmeq]
        have heL : e * L_w_h + t < eCap_h * L_w_h := by
          calc e * L_w_h + t < (e + 1) * L_w_h := by rw [Nat.add_mul, Nat.one_mul]; omega
            _ ≤ eCap_h * L_w_h := Nat.mul_le_mul_right _ he
        exact ⟨hzeroN _ (by omega) (by omega), hzeroD _ (by omega) (by omega)⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h9 := hi.2.2.2.2.2.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨r1, r2, r3, r4, r5, r6, r9, r10, r11, hfrW, hWdone, hW0⟩
        have hiL : i < eL.length := by omega
        set e := eL[i]
        have he_G : e ∈ G.E := (heL_mem e).mp (List.getElem_mem hiL)
        have he_lt : e < eCap_g := helt e he_G
        have he_rd : st.mem (dgEListBase srcDgG vCap_g eCap_g + i) = e := by
          rw [hfrW _ (Or.inl (by dsimp [dgEListBase]; omega))]; exact heL_LA i hiL
        have he_mul_g : e * L_w_g + L_w_g ≤ eCap_g * L_w_g := by
          calc e * L_w_g + L_w_g = (e + 1) * L_w_g := by ring
            _ ≤ eCap_g * L_w_g := Nat.mul_le_mul_right _ he_lt
        have he_mul_h : e * L_w_h + L_w_h ≤ eCap_h * L_w_h := by
          calc e * L_w_h + L_w_h = (e + 1) * L_w_h := by ring
            _ ≤ eCap_h * L_w_h := Nat.mul_le_mul_right _ (by omega)
        have he_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < eL.length), eL[j] ≠ e := by
          intro j hj hj' hEq
          have := (List.nodup_iff_injective_getElem.mp heL_nd) (a₁ := ⟨j, hj'⟩) (a₂ := ⟨i, hiL⟩) hEq
          simp only [Fin.mk.injEq] at this; omega
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := e) (by
          have hlt : dgEListBase srcDgG vCap_g eCap_g + i < 2 ^ w := by dsimp [dgEListBase]; omega
          eval_expr) ?_
        refine runs_seq_call_le hCopy
          (by eval_expr)
          (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
          ⟨dstNum + e * L_w_h, srcNum + e * L_w_g, L_w_g, rfl, by omega, by omega, by omega⟩
          (fun _ mem1 pos1 hpost1 => ?_)
        rcases hpost1 with ⟨_, _, _, harg1, _, hcp1, hfr1⟩
        cases harg1
        refine runs_call_le hCopy
          (by eval_expr)
          (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
          ⟨dstDen + e * L_w_h, srcDen + e * L_w_g, L_w_g, rfl, by omega, by omega, by omega⟩
          (fun _ mem2 pos2 hpost2 => ?_)
        rcases hpost2 with ⟨_, _, _, harg2, _, hcp2, hfr2⟩
        cases harg2
        dsimp only at hcp1 hfr1 hcp2 hfr2
        have hdisj_e : ∀ e' : ℕ, e' ≠ e → ∀ t < L_w_h,
            (dstNum + e' * L_w_h + t < dstNum + e * L_w_h ∨
             dstNum + e * L_w_h + L_w_g ≤ dstNum + e' * L_w_h + t) ∧
            (dstDen + e' * L_w_h + t < dstDen + e * L_w_h ∨
             dstDen + e * L_w_h + L_w_g ≤ dstDen + e' * L_w_h + t) := by
          intro e' hne t ht
          rcases lt_or_gt_of_ne hne with hlt' | hgt'
          · have : e' * L_w_h + t < e * L_w_h := by
              calc e' * L_w_h + t < (e' + 1) * L_w_h := by rw [Nat.add_mul, Nat.one_mul]; omega
                _ ≤ e * L_w_h := Nat.mul_le_mul_right _ hlt'
            exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
          · have : e * L_w_h + L_w_h ≤ e' * L_w_h := by
              calc e * L_w_h + L_w_h = (e + 1) * L_w_h := by ring
                _ ≤ e' * L_w_h := Nat.mul_le_mul_right _ hgt'
            exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
        refine ⟨⟨⟨by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5], by simp [r6],
          by simp [r9], by simp [r10], by simp,
          fun a ha => (hfr2 a (by omega)).trans ((hfr1 a (by omega)).trans (hfrW a ha)),
          fun j hj hj' => ?_, fun e' he' hne t ht => ?_⟩, by simp [r11]⟩,
          by simp [memCopyContract, argsSize, Expr.size]; omega⟩
        · by_cases hji : j = i
          · subst hji
            change (∀ t < L_w_g, mem2 (dstNum + e * L_w_h + t) = mem (srcNum + e * L_w_g + t) ∧
                mem2 (dstDen + e * L_w_h + t) = mem (srcDen + e * L_w_g + t)) ∧
              (∀ t, L_w_g ≤ t → t < L_w_h → mem2 (dstNum + e * L_w_h + t) = 0 ∧
                mem2 (dstDen + e * L_w_h + t) = 0)
            refine ⟨fun t ht => ⟨?_, ?_⟩, fun t ht1 ht2 => ⟨?_, ?_⟩⟩
            · rw [hfr2 (dstNum + e * L_w_h + t) (Or.inl (by omega)), hcp1 t ht,
                  hfrW (srcNum + e * L_w_g + t) (Or.inl (by omega))]
            · rw [hcp2 t ht, hfr1 (srcDen + e * L_w_g + t) (Or.inl (by omega)),
                  hfrW (srcDen + e * L_w_g + t) (Or.inl (by omega))]
            · rw [hfr2 (dstNum + e * L_w_h + t) (Or.inl (by omega)),
                  hfr1 (dstNum + e * L_w_h + t) (Or.inr (by omega))]
              exact (hW0 e (by omega) he_ne_prev t ht2).1
            · rw [hfr2 (dstDen + e * L_w_h + t) (Or.inr (by omega)),
                  hfr1 (dstDen + e * L_w_h + t) (Or.inr (by omega))]
              exact (hW0 e (by omega) he_ne_prev t ht2).2
          · have hd := hWdone j (by omega) hj'
            have hne := he_ne_prev j (by omega) hj'
            have hej_lt : eL[j] < eCap_g := helt _ ((heL_mem _).mp (List.getElem_mem hj'))
            have hej_mul : eL[j] * L_w_h + L_w_h ≤ eCap_h * L_w_h := by
              calc eL[j] * L_w_h + L_w_h = (eL[j] + 1) * L_w_h := by ring
                _ ≤ eCap_h * L_w_h := Nat.mul_le_mul_right _ (by omega)
            refine ⟨fun t ht => ⟨?_, ?_⟩, fun t ht1 ht2 => ⟨?_, ?_⟩⟩
            · dsimp only
              rw [hfr2 (dstNum + eL[j] * L_w_h + t) (Or.inl (by omega)),
                  hfr1 (dstNum + eL[j] * L_w_h + t) (hdisj_e _ hne t (by omega)).1]
              exact (hd.1 t ht).1
            · dsimp only
              rw [hfr2 (dstDen + eL[j] * L_w_h + t) (hdisj_e _ hne t (by omega)).2,
                  hfr1 (dstDen + eL[j] * L_w_h + t) (Or.inr (by omega))]
              exact (hd.1 t ht).2
            · dsimp only
              rw [hfr2 (dstNum + eL[j] * L_w_h + t) (Or.inl (by omega)),
                  hfr1 (dstNum + eL[j] * L_w_h + t) (hdisj_e _ hne t ht2).1]
              exact (hd.2 t ht1 ht2).1
            · dsimp only
              rw [hfr2 (dstDen + eL[j] * L_w_h + t) (hdisj_e _ hne t ht2).2,
                  hfr1 (dstDen + eL[j] * L_w_h + t) (Or.inr (by omega))]
              exact (hd.2 t ht1 ht2).2
        · have hne_e : e' ≠ e := (hne i (by omega) hiL).symm
          have he'_mul : e' * L_w_h + L_w_h ≤ eCap_h * L_w_h := by
            calc e' * L_w_h + L_w_h = (e' + 1) * L_w_h := by ring
              _ ≤ eCap_h * L_w_h := Nat.mul_le_mul_right _ he'
          have h0 := hW0 e' he' (fun j hj hj' => hne j (by omega) hj') t ht
          dsimp only
          refine ⟨(hfr2 (dstNum + e' * L_w_h + t) (Or.inl (by omega))).trans
              ((hfr1 (dstNum + e' * L_w_h + t) (hdisj_e e' hne_e t ht).1).trans h0.1),
            (hfr2 (dstDen + e' * L_w_h + t) (hdisj_e e' hne_e t ht).2).trans
              ((hfr1 (dstDen + e' * L_w_h + t) (Or.inr (by omega))).trans h0.2)⟩)).mono_cost
      (fun _ _ => by dsimp [Expr.size]; ring_nf; omega)
  refine runs_seq_triple_le hwLoop ⟨by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp, by simp, rfl⟩ (fun st1 hW1 => ?_)
  rcases hW1 with ⟨_, _, _, _, _, _, _, _, _, hfr1, hWdone, _⟩
  refine runs_ret_le (by eval_expr) ⟨rfl, ?_, hfr1⟩ (by dsimp [Expr.size]; omega)
  refine ⟨le_trans hhLg (Nat.mul_le_mul_left h hLw_le), le_trans hLg1 hLw_le, fun e he => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((heL_mem e).mpr he)
  obtain ⟨helt_g, hvN_g, hvD_g, hiN_g, hiD_g, hval⟩ := hWstrE _ he
  obtain ⟨hcp_e, hze_e⟩ := hWdone j (by omega) hj
  have hvN_lo : Valid st1.mem (dstNum + eL[j] * L_w_h) h L_w_g := fun t ht => by
    rw [(hcp_e t ht).1]; exact hvN_g t ht
  have hvD_lo : Valid st1.mem (dstDen + eL[j] * L_w_h) h L_w_g := fun t ht => by
    rw [(hcp_e t ht).2]; exact hvD_g t ht
  have hiN_lo : intVal st1.mem (dstNum + eL[j] * L_w_h) h L_w_g =
      intVal mem (srcNum + eL[j] * L_w_g) h L_w_g := intVal_congr fun t ht => (hcp_e t ht).1
  have hiD_lo : intVal st1.mem (dstDen + eL[j] * L_w_h) h L_w_g =
      intVal mem (srcDen + eL[j] * L_w_g) h L_w_g := intVal_congr fun t ht => (hcp_e t ht).2
  obtain ⟨hvN_h, hiN_h⟩ := intVal_zero_extend_pos hh1 hLw_le hvN_lo (hiN_lo.symm ▸ hiN_g)
    (fun t ht1 ht2 => (hze_e t ht1 ht2).1)
  obtain ⟨hvD_h, hiD_h⟩ := intVal_zero_extend_pos hh1 hLw_le hvD_lo (hiD_lo.symm ▸ hiD_g)
    (fun t ht1 ht2 => (hze_e t ht1 ht2).2)
  refine ⟨lt_of_lt_of_le helt_g heCap, hvN_h, hvD_h, ?_, ?_, ?_⟩
  · rw [hiN_h, hiN_lo]; exact hiN_g
  · rw [hiD_h, hiD_lo]; exact hiD_g
  · rw [hiN_h, hiN_lo, hiD_h, hiD_lo]; exact hval

end MinCostFlow.SparseCore.Program
