module

public import MinCostFlow.ExpanderDecomp.OuterProgRecChild
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cut-Branch Verification for `outerDecompRecProc` (`OuterProgRecCut`)

Proves `recCut_runs` for the sparse port-cut branch of `outerDecompRecProc` using `recChild_runs`
from `OuterProgRecChild.lean`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 2. Cut Branch (`recCut_runs`) -/

/-- Plain-arithmetic helper bundling `OuterRoundPortCutWordBound` and `OuterRoundPortCutDisjoint`. -/
private lemma round_wordBound_aux {w n k e kU vertsAddr h h3 uAddr locAddr hRoot : ℕ}
    (hRoot_le : hRoot ≤ h) (h3_ge : h + 2 * e ≤ h3)
    (hVA : vertsAddr + k ≤ h) (hU_ge : h ≤ uAddr) (hU : uAddr + kU ≤ h3)
    (hlocH : locAddr + n ≤ hRoot) (hdLV : DisjointRange locAddr n vertsAddr k)
    (h4e16 : 4 * e + 16 < 2 ^ w) (hk16 : k + 16 < 2 ^ w)
    (hh5_lt : h3 + 4 * k + 4 * e + 2 + roundPortCutSpace k e < 2 ^ w) :
    let sAddr := h3
    let tAddr := sAddr + k
    let lenAddr := tAddr + k
    let e1Addr := lenAddr + 2
    let e2Addr := e1Addr + 2 * e
    let act1Addr := e2Addr + 2 * e
    let act2Addr := act1Addr + k
    let h4 := act2Addr + k
    OuterRoundPortCutWordBound w n k e kU vertsAddr h uAddr locAddr sAddr tAddr lenAddr h4 ∧
    OuterRoundPortCutDisjoint n k e kU vertsAddr h uAddr locAddr sAddr tAddr lenAddr := by
  intro sAddr tAddr lenAddr e1Addr e2Addr act1Addr act2Addr h4
  have hh4_eq : h4 = h3 + 4 * k + 4 * e + 2 := by
    dsimp only [h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr, tAddr, sAddr]; omega
  unfold roundPortCutSpace at hh5_lt
  refine ⟨?_, ?_⟩
  · unfold OuterRoundPortCutWordBound roundPortCutSpace
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, h4e16, hk16⟩
  · unfold OuterRoundPortCutDisjoint DisjointRange
    refine ⟨hdLV, Or.inl (by omega), Or.inl (by omega),
      Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega),
      Or.inl (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩

/-- Executes the rounding prefix of `recCutStmt idx` (`A1 ;; A2 ;; A3 ;; bRound ;; L12`) on `st3`,
returning `stL` with the rounded cut lists `(H.restrict S).verts` and `(H.restrict (H.vertSet \ S)).verts`,
their lengths in `r27` and `r28`, and a continuation chainer into the remaining child calls. -/
private lemma recCut_round_runs {M r w : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv ParamConfig.default M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hRound : MeetsContract w pProg idx.bRound (outerRoundPortCutContract w))
    {ω : ℕ → Bool} {H : CompactSubgraph} {vertsAddr h h3 : ℕ} {st st3 : State}
    {U : Finset ℕ} {uList : List ℕ}
    (hRep : H.Represents G H.vertSet) (hXV : H.vertSet ⊆ G.verts)
    (heM : H.edges.length ≤ M)
    (hRoot_le : hRoot ≤ h) (hVA_h : vertsAddr + H.verts.length ≤ h)
    (hdLV : DisjointRange locAddr G.n vertsAddr H.verts.length)
    (hV : ListAt st.mem vertsAddr H.verts)
    (hloc0 : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hr0 : st.regs 0 = H.verts.length) (hr1 : st.regs 1 = vertsAddr)
    (hr2 : st.regs 2 = H.edges.length) (hr5 : st.regs 5 = locAddr)
    (h3_r10 : st3.regs 10 = h) (h3_r15 : st3.regs 15 = h3)
    (h3_r14_le : st3.regs 14 + 4 ≤ h3) (h3_ge : h + 2 * H.edges.length ≤ h3)
    (hZero3 : ZeroFrom st3.mem h3)
    (hOwn3 : ListAt st3.mem h (portOwnersList H.edges))
    (hU_nd : uList.Nodup) (hU_fin : uList.toFinset = U)
    (hU_kU : st3.mem (st3.regs 14 + 1) = uList.length)
    (hU_list : ListAt st3.mem (st3.mem (st3.regs 14 + 2)) uList)
    (hU_ge : h ≤ st3.mem (st3.regs 14 + 2))
    (hU_le : st3.mem (st3.regs 14 + 2) + uList.length ≤ h3)
    (hU_lt : ∀ p ∈ uList, p < 2 * H.edges.length)
    (h3_regs : ∀ r' ≤ 9, st3.regs r' = st.regs r')
    (h3_belowH : ∀ a < h, st3.mem a = st.mem a)
    (hh5_lt : h3 + 4 * H.verts.length + 4 * H.edges.length + 2 +
      roundPortCutSpace H.verts.length H.edges.length < 2 ^ w) :
    let k := H.verts.length
    let e := H.edges.length
    let S := roundPortCut G H.vertSet U
    let sAddr := h3
    let tAddr := sAddr + k
    let lenAddr := tAddr + k
    let e1Addr := lenAddr + 2
    let e2Addr := e1Addr + 2 * e
    let act1Addr := e2Addr + 2 * e
    let act2Addr := act1Addr + k
    let h4 := act2Addr + k
    let h5 := h4 + roundPortCutSpace k e
    ∃ (stL : State),
      stL.regs 19 = sAddr ∧ stL.regs 20 = tAddr ∧ stL.regs 22 = e1Addr ∧
      stL.regs 23 = e2Addr ∧ stL.regs 24 = act1Addr ∧ stL.regs 25 = act2Addr ∧
      stL.regs 26 = h5 ∧
      stL.regs 27 = (H.restrict S).verts.length ∧
      stL.regs 28 = (H.restrict (H.vertSet \ S)).verts.length ∧
      (∀ r' ≤ 9, stL.regs r' = st.regs r') ∧
      ListAt stL.mem sAddr (H.restrict S).verts ∧
      ListAt stL.mem tAddr (H.restrict (H.vertSet \ S)).verts ∧
      ZeroFrom stL.mem h5 ∧
      (∀ u < G.n, stL.mem (locAddr + u) = 0) ∧
      (∀ a < h, stL.mem a = st.mem a) ∧
      ∀ (rest : Stmt) (oEnd : Outcome) (stEnd : State) (cRest : ℕ),
        Runs w pProg ω rest stL oEnd stEnd cRest →
        ∃ cTot,
          Runs w pProg ω
            ((.assign 17 (.load (.bin .add (.reg 14) (.const 1))) ;;
              .assign 18 (.load (.bin .add (.reg 14) (.const 2))) ;;
              .assign 19 (.reg 15) ;;
              .assign 20 (.bin .add (.reg 19) (.reg 0))) ;;
             (.assign 21 (.bin .add (.reg 20) (.reg 0)) ;;
              .assign 22 (.bin .add (.reg 21) (.const 2)) ;;
              .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 2))) ;;
              .assign 24 (.bin .add (.reg 23) (.bin .mul (.const 2) (.reg 2)))) ;;
             (.assign 25 (.bin .add (.reg 24) (.reg 0)) ;;
              .assign 26 (.bin .add (.reg 25) (.reg 0))) ;;
             .call 26 idx.bRound
               [.reg 0, .reg 1, .reg 2, .reg 10, .reg 17, .reg 18, .reg 5,
                .reg 19, .reg 20, .reg 21, .reg 26] ;;
             (.assign 27 (.load (.reg 21)) ;;
              .assign 28 (.load (.bin .add (.reg 21) (.const 1)))) ;;
             rest) st3 oEnd stEnd cTot ∧
          cTot ≤ outerRoundPortCutCost k e uList.length + cRest + 110 := by
  set k := H.verts.length
  set e := H.edges.length
  set S := roundPortCut G H.vertSet U
  set uAddr := st3.mem (st3.regs 14 + 2)
  set kU := uList.length
  set sAddr := h3
  set tAddr := sAddr + k
  set lenAddr := tAddr + k
  set e1Addr := lenAddr + 2
  set e2Addr := e1Addr + 2 * e
  set act1Addr := e2Addr + 2 * e
  set act2Addr := act1Addr + k
  set h4 := act2Addr + k
  set h5 := h4 + roundPortCutSpace k e
  have hh4_eq : h4 = h3 + 4 * k + 4 * e + 2 := by
    dsimp only [h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr, tAddr, sAddr]; omega
  have hh5_lt' : h5 < 2 ^ w := by dsimp only [h5]; omega
  have hw16 : 16 < 2 ^ w := by have := env.hw250; omega
  have hsubV : ∀ u ∈ H.verts, u < G.n := fun u hu =>
    Finset.mem_range.mp (hXV (List.mem_toFinset.mpr hu))
  have hk_le_n : k ≤ G.n := by
    have h1 : H.verts.toFinset.card ≤ (Finset.range G.n).card := Finset.card_le_card hXV
    rw [List.toFinset_card_of_nodup hRep.1, Finset.card_range] at h1; exact h1
  have hk16 : k + 16 < 2 ^ w := by have := env.hwN; omega
  have h4e16 : 4 * e + 16 < 2 ^ w := by
    have h1 := env.hN2M_w
    have h2 : 4 * M ≤ NOf M r * (2 * M) := by
      have := env.hN2
      calc 4 * M = 2 * (2 * M) := by ring
        _ ≤ NOf M r * (2 * M) := Nat.mul_le_mul_right (2 * M) this
    omega
  have hA1 : Triple w pProg (fun s => s = st3)
      (.assign 17 (.load (.bin .add (.reg 14) (.const 1))) ;;
       .assign 18 (.load (.bin .add (.reg 14) (.const 2))) ;;
       .assign 19 (.reg 15) ;;
       .assign 20 (.bin .add (.reg 19) (.reg 0)))
      (normalPost fun s' => s'.mem = st3.mem ∧
        s'.regs 17 = kU ∧ s'.regs 18 = uAddr ∧ s'.regs 19 = sAddr ∧ s'.regs 20 = tAddr ∧
        (∀ r' ≤ 16, s'.regs r' = st3.regs r'))
      (fun _ => 25) := by
    intro s ω hs; subst s
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := kU)
      (by simp [Expr.eval, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : st3.regs 14 + 1 < 2 ^ w), hU_kU]) ?_
    refine runs_seq_assign_le (v := uAddr)
      (by simp [Expr.eval, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : st3.regs 14 + 2 < 2 ^ w), uAddr]) ?_
    refine runs_seq_assign_le (v := sAddr) (by simp [Expr.eval, h3_r15, sAddr]) ?_
    refine runs_assign_le (v := tAddr)
      (by simp [Expr.eval, BinOp.eval, h3_regs 0 (by decide), hr0, (by omega : sAddr + k < 2 ^ w), tAddr])
      ⟨rfl, by simp, by simp, by simp, by simp, fun r' hr' => by
        dsimp only
        rw [Function.update_of_ne (by omega : r' ≠ 20), Function.update_of_ne (by omega : r' ≠ 19),
            Function.update_of_ne (by omega : r' ≠ 18), Function.update_of_ne (by omega : r' ≠ 17)]⟩
      (by simp [Expr.size])
  rcases hA1 st3 ω rfl with ⟨oA1, stA1, cA1, hrunA1, hqA1, hcA1⟩
  cases oA1 with
  | returned _ => exact False.elim hqA1
  | normal =>
    rcases hqA1 with ⟨hA1_mem, hA1_17, hA1_18, hA1_19, hA1_20, hA1_r⟩
    have hA2 : Triple w pProg (fun s => s = stA1)
        (.assign 21 (.bin .add (.reg 20) (.reg 0)) ;;
         .assign 22 (.bin .add (.reg 21) (.const 2)) ;;
         .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 2))) ;;
         .assign 24 (.bin .add (.reg 23) (.bin .mul (.const 2) (.reg 2))))
        (normalPost fun s' => s'.mem = st3.mem ∧
          s'.regs 21 = lenAddr ∧ s'.regs 22 = e1Addr ∧ s'.regs 23 = e2Addr ∧ s'.regs 24 = act1Addr ∧
          (∀ r' ≤ 20, s'.regs r' = stA1.regs r'))
        (fun _ => 30) := by
      intro s ω hs; subst s
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := lenAddr)
        (by simp [Expr.eval, BinOp.eval, hA1_20, hA1_r 0 (by decide), h3_regs 0 (by decide), hr0,
              (by omega : tAddr + k < 2 ^ w), lenAddr]) ?_
      refine runs_seq_assign_le (v := e1Addr)
        (by simp [Expr.eval, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : lenAddr + 2 < 2 ^ w), e1Addr]) ?_
      refine runs_seq_assign_le (v := e2Addr)
        (by simp [Expr.eval, BinOp.eval, hA1_r 2 (by decide), h3_regs 2 (by decide), hr2,
              (by omega : 2 < 2 ^ w), (by omega : 2 * e < 2 ^ w),
              (by omega : e1Addr + 2 * e < 2 ^ w), e2Addr]) ?_
      refine runs_assign_le (v := act1Addr)
        (by simp [Expr.eval, BinOp.eval, hA1_r 2 (by decide), h3_regs 2 (by decide), hr2,
              (by omega : 2 < 2 ^ w), (by omega : 2 * e < 2 ^ w),
              (by omega : e2Addr + 2 * e < 2 ^ w), act1Addr])
        ⟨hA1_mem, by simp, by simp, by simp, by simp, fun r' hr' => by
          dsimp only
          rw [Function.update_of_ne (by omega : r' ≠ 24), Function.update_of_ne (by omega : r' ≠ 23),
              Function.update_of_ne (by omega : r' ≠ 22), Function.update_of_ne (by omega : r' ≠ 21)]⟩
        (by simp [Expr.size])
    rcases hA2 stA1 ω rfl with ⟨oA2, stA2, cA2, hrunA2, hqA2, hcA2⟩
    cases oA2 with
    | returned _ => exact False.elim hqA2
    | normal =>
      rcases hqA2 with ⟨hA2_mem, hA2_21, hA2_22, hA2_23, hA2_24, hA2_r⟩
      have hA3 : Triple w pProg (fun s => s = stA2)
          (.assign 25 (.bin .add (.reg 24) (.reg 0)) ;;
           .assign 26 (.bin .add (.reg 25) (.reg 0)))
          (normalPost fun s' => s'.mem = st3.mem ∧
            s'.regs 25 = act2Addr ∧ s'.regs 26 = h4 ∧
            (∀ r' ≤ 24, s'.regs r' = stA2.regs r'))
          (fun _ => 14) := by
        intro s ω hs; subst s
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := act2Addr)
          (by simp [Expr.eval, BinOp.eval, hA2_24, hA2_r 0 (by decide), hA1_r 0 (by decide),
                h3_regs 0 (by decide), hr0, (by omega : act1Addr + k < 2 ^ w), act2Addr]) ?_
        refine runs_assign_le (v := h4)
          (by simp [Expr.eval, BinOp.eval, hA2_r 0 (by decide), hA1_r 0 (by decide),
                h3_regs 0 (by decide), hr0, (by omega : act2Addr + k < 2 ^ w), h4])
          ⟨hA2_mem, by simp, by simp, fun r' hr' => by
            dsimp only
            rw [Function.update_of_ne (by omega : r' ≠ 26), Function.update_of_ne (by omega : r' ≠ 25)]⟩
          (by simp [Expr.size])
      rcases hA3 stA2 ω rfl with ⟨oA3, stA3, cA3, hrunA3, hqA3, hcA3⟩
      cases oA3 with
      | returned _ => exact False.elim hqA3
      | normal =>
        rcases hqA3 with ⟨hA3_mem, hA3_25, hA3_26, hA3_r⟩
        have h3_V : ListAt st3.mem vertsAddr H.verts := fun i hi => by
          rw [h3_belowH (vertsAddr + i) (by omega)]; exact hV i hi
        have h3_loc0 : ∀ u < G.n, st3.mem (locAddr + u) = 0 := fun u hu => by
          rw [h3_belowH (locAddr + u) (by have := env.hlocH; omega)]; exact hloc0 u hu
        have hWB := round_wordBound_aux hRoot_le h3_ge hVA_h hU_ge hU_le env.hlocH hdLV h4e16 hk16 hh5_lt
        have hRoundCall := runs_call_of_meetsContract (r := 26) (p := pProg) (w := w) (st := stA3)
          (args := [.reg 0, .reg 1, .reg 2, .reg 10, .reg 17, .reg 18, .reg 5,
            .reg 19, .reg 20, .reg 21, .reg 26])
          (vs := [k, vertsAddr, e, h, kU, uAddr, locAddr, sAddr, tAddr, lenAddr, h4]) hRound
          (by simp [evalArgs, Expr.eval, hA3_r 0 (by decide), hA2_r 0 (by decide), hA1_r 0 (by decide),
                h3_regs 0 (by decide), hr0, hA3_r 1 (by decide), hA2_r 1 (by decide), hA1_r 1 (by decide),
                h3_regs 1 (by decide), hr1, hA3_r 2 (by decide), hA2_r 2 (by decide), hA1_r 2 (by decide),
                h3_regs 2 (by decide), hr2, hA3_r 10 (by decide), hA2_r 10 (by decide), hA1_r 10 (by decide),
                h3_r10, hA3_r 17 (by decide), hA2_r 17 (by decide), hA1_17,
                hA3_r 18 (by decide), hA2_r 18 (by decide), hA1_18,
                hA3_r 5 (by decide), hA2_r 5 (by decide), hA1_r 5 (by decide), h3_regs 5 (by decide), hr5,
                hA3_r 19 (by decide), hA2_r 19 (by decide), hA1_19,
                hA3_r 20 (by decide), hA2_r 20 (by decide), hA1_20,
                hA3_r 21 (by decide), hA2_21, hA3_26])
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              have := env.hlocH
              rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                (dsimp only [h5, roundPortCutSpace, h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr, tAddr, sAddr] at *; omega))
          ⟨G.n, k, vertsAddr, e, h, kU, uAddr, locAddr, sAddr, tAddr, lenAddr, h4,
            H.verts, portOwnersList H.edges, uList, rfl,
            rfl, hRep.1, hsubV, portOwnersList_length H.edges,
            fun v hv => mem_portOwnersList_inside (hRep.2.2 ▸ hv),
            rfl, hU_nd, hU_lt,
            hA3_mem ▸ h3_V, hA3_mem ▸ hOwn3, hA3_mem ▸ hU_list,
            fun u hu => by rw [hA3_mem]; exact h3_loc0 u hu,
            fun a ha => by rw [hA3_mem]; exact hZero3 a (by omega),
            hWB.1, hWB.2⟩ ω
        rcases hRoundCall with ⟨stR, cR, vR, hrunR, hpostR, hR_26, hR_other, hcR⟩
        dsimp only [outerRoundPortCutContract, List.getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] at hpostR hcR
        have hOwn_rd : readList st3.mem h (2 * e) = portOwnersList H.edges := by
          rw [← portOwnersList_length H.edges]; exact readList_eq_of_listAt hOwn3
        simp only [hA3_mem] at hpostR
        rw [hOwn_rd, readList_eq_of_listAt h3_V, readList_eq_of_listAt hU_list, hU_fin] at hpostR
        rcases hpostR with ⟨hvR_eq, hZeroR, hR_S, hR_T, hR_kS, hR_kT, hR_fr⟩
        have hsList_eq : (H.verts.filter fun x =>
            decide (portCountPrefix (portOwnersList H.edges) (2 * e) x ≤
              2 * portInUCountPrefix (portOwnersList H.edges) U (2 * e) x)) =
            (H.restrict S).verts := by
          unfold CompactSubgraph.restrict
          apply List.filter_congr; intro x hx
          have hxX : x ∈ H.vertSet := List.mem_toFinset.mpr hx
          simp only [decide_eq_decide]
          exact portCountPrefix_iff_mem_roundPortCut hRep.2.2.symm hxX
        have htList_eq : (H.verts.filter fun x =>
            !decide (portCountPrefix (portOwnersList H.edges) (2 * e) x ≤
              2 * portInUCountPrefix (portOwnersList H.edges) U (2 * e) x)) =
            (H.restrict (H.vertSet \ S)).verts := by
          unfold CompactSubgraph.restrict
          apply List.filter_congr; intro x hx
          have hxX : x ∈ H.vertSet := List.mem_toFinset.mpr hx
          have hiff := portCountPrefix_iff_mem_roundPortCut (U := U) hRep.2.2.symm hxX
          change portCountPrefix (portOwnersList H.edges) (2 * e) x ≤
            2 * portInUCountPrefix (portOwnersList H.edges) U (2 * e) x ↔ x ∈ S at hiff
          by_cases hmem : x ∈ S
          · simp [hiff.mpr hmem, hmem]
          · simp [mt hiff.mp hmem, hxX, hmem]
        rw [hsList_eq] at hR_S hR_kS
        rw [htList_eq] at hR_T hR_kT
        set kS := (H.restrict S).verts.length
        set kT := (H.restrict (H.vertSet \ S)).verts.length
        have hlen1_lt : lenAddr + 1 < 2 ^ w := by
          dsimp only [h5, roundPortCutSpace, h4, act2Addr, act1Addr, e2Addr, e1Addr] at hh5_lt'; omega
        have hL12 : Triple w pProg (fun s => s = stR)
            (.assign 27 (.load (.reg 21)) ;;
             .assign 28 (.load (.bin .add (.reg 21) (.const 1))))
            (normalPost fun s' => s'.mem = stR.mem ∧
              s'.regs 27 = kS ∧ s'.regs 28 = kT ∧
              (∀ r' ≤ 26, s'.regs r' = stR.regs r'))
            (fun _ => 12) := by
          intro s ω hs; subst s
          have hr21 : stR.regs 21 = lenAddr := by
            rw [hR_other 21 (by decide), hA3_r 21 (by decide), hA2_21]
          refine runs_start_le ?_
          refine runs_seq_assign_le (v := kS) (by simp [Expr.eval, hr21, hR_kS]) ?_
          refine runs_assign_le (v := kT)
            (by simp [Expr.eval, BinOp.eval, hr21, (by omega : 1 < 2 ^ w), hlen1_lt, hR_kT])
            ⟨rfl, by simp, by simp, fun r' hr' => by
              dsimp only
              rw [Function.update_of_ne (by omega : r' ≠ 28), Function.update_of_ne (by omega : r' ≠ 27)]⟩
            (by simp [Expr.size])
        rcases hL12 stR ω rfl with ⟨oL, stL, cL, hrunL, hqL, hcL⟩
        cases oL with
        | returned _ => exact False.elim hqL
        | normal =>
          rcases hqL with ⟨hL_mem, hL_27, hL_28, hL_r⟩
          have hh_s : h ≤ sAddr := le_trans (Nat.le_add_right _ _) h3_ge
          have hh_t : h ≤ tAddr := le_trans hh_s (Nat.le_add_right _ _)
          have hh_len : h ≤ lenAddr := le_trans hh_t (Nat.le_add_right _ _)
          have hh_h4 : h ≤ h4 := by dsimp only [h4, act2Addr, act1Addr, e2Addr, e1Addr]; linarith
          have hR_belowH : ∀ a < h, stR.mem a = st.mem a := fun a ha => by
            rw [hR_fr a (lt_of_lt_of_le ha hh_h4) (Or.inl (lt_of_lt_of_le ha hh_s))
                  (Or.inl (lt_of_lt_of_le ha hh_t)) (Or.inl (lt_of_lt_of_le ha hh_len)),
                h3_belowH a ha]
          refine ⟨stL,
            by rw [hL_r 19 (by decide), hR_other 19 (by decide), hA3_r 19 (by decide), hA2_r 19 (by decide), hA1_19],
            by rw [hL_r 20 (by decide), hR_other 20 (by decide), hA3_r 20 (by decide), hA2_r 20 (by decide), hA1_20],
            by rw [hL_r 22 (by decide), hR_other 22 (by decide), hA3_r 22 (by decide), hA2_22],
            by rw [hL_r 23 (by decide), hR_other 23 (by decide), hA3_r 23 (by decide), hA2_23],
            by rw [hL_r 24 (by decide), hR_other 24 (by decide), hA3_r 24 (by decide), hA2_24],
            by rw [hL_r 25 (by decide), hR_other 25 (by decide), hA3_25],
            by rw [hL_r 26 (by decide), hR_26, hvR_eq],
            hL_27, hL_28,
            fun r' hr' => by
              rw [hL_r r' (by omega), hR_other r' (by omega), hA3_r r' (by omega),
                  hA2_r r' (by omega), hA1_r r' (by omega), h3_regs r' hr'],
            hL_mem ▸ hR_S, hL_mem ▸ hR_T,
            by rw [hL_mem, ← hvR_eq]; exact hZeroR,
            fun u hu => by rw [hL_mem, hR_belowH (locAddr + u) (by have := env.hlocH; omega)]; exact hloc0 u hu,
            fun a ha => by rw [hL_mem]; exact hR_belowH a ha,
            fun rest oEnd stEnd cRest hRest => ?_⟩
          refine ⟨cA1 + (cA2 + (cA3 + (cR + (cL + cRest + 1) + 1) + 1) + 1) + 1,
            runs_seq_iff.mpr (Or.inr ⟨stA1, cA1, _, hrunA1,
              runs_seq_iff.mpr (Or.inr ⟨stA2, cA2, _, hrunA2,
                runs_seq_iff.mpr (Or.inr ⟨stA3, cA3, _, hrunA3,
                  runs_seq_iff.mpr (Or.inr ⟨stR, cR, _, hrunR,
                    runs_seq_iff.mpr (Or.inr ⟨stL, cL, cRest, hrunL, hRest, rfl⟩),
                    rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
          dsimp at hcA1 hcA2 hcA3 hcL
          simp only [argsSize, Expr.size, Nat.add_zero] at hcR
          omega

lemma recCut_runs {M r w C_core C_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv ParamConfig.default M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hSub : RecSubprocs M r w pProg idx C_core C_rt C_sp routeC)
    {ω : ℕ → Bool} {eBound : ℕ}
    (hIH : RecIH ParamConfig.default M r w C_core C_rt C_sp routeC pProg idx G
      paramAddr locAddr labelsAddr nextLblAddr hRoot ω eBound)
    {H : CompactSubgraph} {vertsAddr edgesAddr h h3 nl₀ c3 : ℕ} {st st3 : State}
    {U : Finset ℕ}
    (heBound : H.edges.length ≤ eBound + 1)
    (hRep : H.Represents G H.vertSet) (hXV : H.vertSet ⊆ G.verts)
    (hSorted : H.verts.Pairwise (· < ·)) (hXdeg : ∀ v ∈ H.vertSet, 1 ≤ G.degIn H.vertSet v)
    (heM : H.edges.length ≤ M) (hQlt : QOut ParamConfig.default M r < H.edges.length)
    (hGameSpec : OuterGameOutcomeSpec ParamConfig.default M r H.edges.length
      (portGraph cloud G H.vertSet) (.cut U))
    (hRoot_le : hRoot ≤ h)
    (hVA_h : vertsAddr + H.verts.length ≤ h) (hEA_h : edgesAddr + 2 * H.edges.length ≤ h)
    (hdLV : DisjointRange locAddr G.n vertsAddr H.verts.length)
    (hdLE : DisjointRange locAddr G.n edgesAddr (2 * H.edges.length))
    (hdLbE : DisjointRange labelsAddr G.n edgesAddr (2 * H.edges.length))
    (hdNE : DisjointRange nextLblAddr 1 edgesAddr (2 * H.edges.length))
    (hPB : OuterParamBlockAt st.mem paramAddr ParamConfig.default G.n M r)
    (hV : ListAt st.mem vertsAddr H.verts) (hE : EdgesAt st.mem edgesAddr H.edges)
    (hloc0 : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hnl : st.mem nextLblAddr = nl₀) (hnl_le : nl₀ + H.verts.length ≤ G.n)
    (hSpace : h + recTreeSpace (DOut ParamConfig.default M r)
      (recPerEdgeSpace ParamConfig.default C_sp M r routeC)
      (recPerWitSpace ParamConfig.default M r) H.edges.length < 2 ^ w)
    (hr0 : st.regs 0 = H.verts.length) (hr1 : st.regs 1 = vertsAddr)
    (hr2 : st.regs 2 = H.edges.length) (hr3 : st.regs 3 = edgesAddr)
    (hr4 : st.regs 4 = paramAddr) (hr5 : st.regs 5 = locAddr)
    (hr6 : st.regs 6 = labelsAddr) (hr7 : st.regs 7 = nextLblAddr)
    (h3_r10 : st3.regs 10 = h) (h3_r15 : st3.regs 15 = h3)
    (h3_r14_le : st3.regs 14 + 4 ≤ h3) (h3_ge : h + 2 * H.edges.length ≤ h3)
    (h3_le : h3 ≤ h + 2 * H.edges.length + (2 + 20 * H.edges.length) +
      portGraphWorkSpace H.verts.length H.edges.length + portGraphHeapSpace H.edges.length + 4 +
      outerGameSpace C_sp M r H.edges.length
        (outerGameMaxCost ParamConfig.default M r routeC H.edges.length))
    (hZero3 : ZeroFrom st3.mem h3)
    (hOwn3 : ListAt st3.mem h (portOwnersList H.edges))
    (hOut3 : OuterGameOutAt st3.mem (st3.regs 14) h h3 H.edges.length (.cut U))
    (h3_regs : ∀ r' ≤ 9, st3.regs r' = st.regs r')
    (h3_belowH : ∀ a < h, st3.mem a = st.mem a)
    (hc3 : c3 ≤ outerGameStepBound C_core C_rt r H.edges.length
        (outerGameMaxCost ParamConfig.default M r routeC H.edges.length) +
      portGraphCost H.verts.length H.edges.length + 70) :
    ∃ h' st' c,
      Runs w pProg ω (recCutStmt idx) st3 (.returned h') st' c ∧
      RecNodePost ParamConfig.default M r C_core C_rt C_sp routeC G locAddr labelsAddr nextLblAddr
        h H st.mem nl₀ h' st'.mem (c3 + c + 20) := by
  let cfg := ParamConfig.default
  set k := H.verts.length
  set e := H.edges.length
  set lc := outerGameMaxCost cfg M r routeC e
  have he_eq : (G.inside H.vertSet).length = e := congrArg List.length hRep.2.2.symm
  have hQlt' : QOut cfg M r < e := hQlt
  have he1 : 1 ≤ e := by unfold QOut at hQlt'; omega
  have h2D_lt : 2 * DOut cfg M r < (G.inside H.vertSet).length := by unfold QOut at hQlt'; omega
  have hk_le_2e : k ≤ 2 * e := by
    have := verts_length_le_two_mul_edges hRep hXdeg; omega
  have hlc_le : lc ≤ e * modelPerEdge cfg M r routeC := outerGameMaxCost_le_modelPerEdge he1
  have hnode_sp := recNode_space_le (cfg := cfg) (C_sp := C_sp) he1 heM hk_le_2e hlc_le
  -- Mathematical cut guarantees from `hGameSpec` + `lemma_8` + `edge_shrink_cut`
  rcases hGameSpec with ⟨hUV, hUsparse, hUz1, hUz2⟩
  change e / DOut cfg M r + 1 ≤ 2 * U.card at hUz1
  change e / DOut cfg M r + 1 ≤ 2 * ((portGraph cloud G H.vertSet).verts \ U).card at hUz2
  set S := roundPortCut G H.vertSet U
  have hD1 : 1 ≤ DOut cfg M r := one_le_DOut cfg M r
  have hb_a0 : 2 * cfg.a₀ ≤ bOut cfg M := two_mul_a0_le_bOut cfg M
  obtain ⟨hSX, _, _, hUret1, hUret2, _, h32⟩ :=
    lemma_8 cloud_isCloudExpander cfg.ha₀ env.hα hb_a0 hUV hUsparse
  change S ⊆ H.vertSet at hSX
  change U.card ≤ 2 * G.volIn H.vertSet S at hUret1
  change ((portGraph cloud G H.vertSet).verts \ U).card ≤
    2 * G.volIn H.vertSet (H.vertSet \ S) at hUret2
  change bOut cfg M * G.cutIn H.vertSet S ≤
    cfg.kappa * min (G.volIn H.vertSet S) (G.volIn H.vertSet (H.vertSet \ S)) at h32
  obtain ⟨hsh1_in, hsh2_in, hlt1_in, hlt2_in⟩ :=
    edge_shrink_cut G hSX hD1 h2D_lt (by rw [he_eq]; omega) (by rw [he_eq]; omega) hUret1 hUret2
  have hrep1 := CompactSubgraph.restrict_represents hRep hSX
  have hrep2 := CompactSubgraph.restrict_represents hRep (Finset.sdiff_subset (s := H.vertSet) (t := S))
  have hst1 := CompactSubgraph.stripIsolated_spec hrep1
  have hst2 := CompactSubgraph.stripIsolated_spec hrep2
  set iso₁ := (H.restrict S).stripIsolated.1
  set act₁ := (H.restrict S).stripIsolated.2
  set iso₂ := (H.restrict (H.vertSet \ S)).stripIsolated.1
  set act₂ := (H.restrict (H.vertSet \ S)).stripIsolated.2
  have he1_in : act₁.edges = G.inside S := hst1.2.2.2.2.2.1.trans hrep1.2.2
  have he2_in : act₂.edges = G.inside (H.vertSet \ S) := hst2.2.2.2.2.2.1.trans hrep2.2.2
  have he1_eq : (H.restrict S).edges.length = (G.inside S).length := congrArg List.length hrep1.2.2
  have he2_eq : (H.restrict (H.vertSet \ S)).edges.length = (G.inside (H.vertSet \ S)).length :=
    congrArg List.length hrep2.2.2
  have he1_act : act₁.edges.length = (H.restrict S).edges.length := congrArg List.length hst1.2.2.2.2.2.1
  have he2_act : act₂.edges.length = (H.restrict (H.vertSet \ S)).edges.length := congrArg List.length hst2.2.2.2.2.2.1
  have hsum_e12 : (H.restrict S).edges.length + (H.restrict (H.vertSet \ S)).edges.length ≤ e := by
    have := inside_length_split G hSX; omega
  have hsh1 : 16 * DOut cfg M r * (H.restrict S).edges.length ≤ (16 * DOut cfg M r - 1) * e := by
    rw [he1_eq, ← he_eq]; exact hsh1_in
  have hsh2 : 16 * DOut cfg M r * (H.restrict (H.vertSet \ S)).edges.length ≤ (16 * DOut cfg M r - 1) * e := by
    rw [he2_eq, ← he_eq]; exact hsh2_in
  have htree_step := recTreeSpace_cut_step (D := DOut cfg M r)
    (perE := recPerEdgeSpace cfg C_sp M r routeC) (perW := recPerWitSpace cfg M r)
    hD1 he1 hsum_e12 hsh1 hsh2
  -- Extract `uList` from `OuterGameOutAt`
  rcases hOut3 with ⟨_, uList, hU_nd, hU_fin, hU_kU, hU_list, hU_ge, hU_le⟩
  have hU_lt : ∀ p ∈ uList, p < 2 * e := fun p hp => by
    have h1 : p ∈ (portGraph cloud G H.vertSet).verts := hUV (hU_fin ▸ List.mem_toFinset.mpr hp)
    rw [Graph.verts, portGraph_n, he_eq, Finset.mem_range] at h1; exact h1
  set kU := uList.length
  have hkU_le : kU ≤ 2 * e := by
    have h1 : uList.length = U.card := by rw [← hU_fin, List.toFinset_card_of_nodup hU_nd]
    have h2 : U.card ≤ (Finset.range (2 * e)).card :=
      Finset.card_le_card (fun p hp => Finset.mem_range.mpr (hU_lt p (List.mem_toFinset.mp (hU_fin ▸ hp))))
    rw [Finset.card_range] at h2; omega
  -- Buffer addresses above `h3`
  set sAddr := h3
  set tAddr := sAddr + k
  set lenAddr := tAddr + k
  set e1Addr := lenAddr + 2
  set e2Addr := e1Addr + 2 * e
  set act1Addr := e2Addr + 2 * e
  set act2Addr := act1Addr + k
  set h4 := act2Addr + k
  set h5 := h4 + roundPortCutSpace k e
  have hh5_node : h5 + 3 ≤ h + e * recPerEdgeSpace cfg C_sp M r routeC := by
    dsimp only [h5, roundPortCutSpace, h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr, tAddr, sAddr]
    linarith only [h3_le, hnode_sp]
  have hh5_sp : h5 + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
        (recPerWitSpace cfg M r) (H.restrict S).edges.length +
      recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
        (recPerWitSpace cfg M r) (H.restrict (H.vertSet \ S)).edges.length ≤
      h + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
        (recPerWitSpace cfg M r) e := by linarith only [hh5_node, htree_step]
  have hSpace' : h + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
      (recPerWitSpace cfg M r) e < 2 ^ w := hSpace
  have hh5_lt : h5 < 2 ^ w := by linarith only [hh5_sp, hSpace']
  have hPre := recCut_round_runs env hSub.hRound hRep hXV heM hRoot_le hVA_h hdLV hV hloc0
    hr0 hr1 hr2 hr5 h3_r10 h3_r15 h3_r14_le h3_ge hZero3 hOwn3
    hU_nd hU_fin hU_kU hU_list hU_ge hU_le hU_lt h3_regs h3_belowH
    (by have : h3 + 4 * k + 4 * e + 2 + roundPortCutSpace k e = h5 := by
          dsimp only [h5, h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr, tAddr, sAddr]; ring
        linarith only [this, hh5_node, htree_step, hSpace']) (ω := ω)
  rcases hPre with ⟨stL, hL_19, hL_20, hL_22, hL_23, hL_24, hL_25, hL_26, hL_27, hL_28,
    hL_r0_9, hL_S, hL_T, hZeroL, hL_loc0, hL_belowH, hCutPreChain⟩
  change stL.regs 19 = sAddr at hL_19
  change stL.regs 20 = tAddr at hL_20
  change stL.regs 22 = e1Addr at hL_22
  change stL.regs 23 = e2Addr at hL_23
  change stL.regs 24 = act1Addr at hL_24
  change stL.regs 25 = act2Addr at hL_25
  change stL.regs 26 = h5 at hL_26
  change ListAt stL.mem sAddr (H.restrict S).verts at hL_S
  change ListAt stL.mem tAddr (H.restrict (H.vertSet \ S)).verts at hL_T
  change ZeroFrom stL.mem h5 at hZeroL
  set kS := (H.restrict S).verts.length
  set kT := (H.restrict (H.vertSet \ S)).verts.length
  have hkSkT : kS + kT = k := by
    have h1 : (H.restrict (H.vertSet \ S)).verts.toFinset.card +
        (H.restrict S).verts.toFinset.card = H.verts.toFinset.card := by
      rw [hrep1.2.1, hrep2.2.1]
      exact Finset.card_sdiff_add_card_eq_card hSX
    rw [List.toFinset_card_of_nodup hrep1.1, List.toFinset_card_of_nodup hrep2.1,
        List.toFinset_card_of_nodup hRep.1] at h1
    omega
  have hh_s : h ≤ sAddr := le_trans (Nat.le_add_right _ _) h3_ge
  have hh_t : h ≤ tAddr := le_trans hh_s (Nat.le_add_right _ _)
  have hh_e1 : h ≤ e1Addr := le_trans hh_t (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hh_e2 : h ≤ e2Addr := le_trans hh_e1 (Nat.le_add_right _ _)
  have hh_a1 : h ≤ act1Addr := le_trans hh_e2 (Nat.le_add_right _ _)
  have hh_a2 : h ≤ act2Addr := le_trans hh_a1 (Nat.le_add_right _ _)
  have hh_h5 : h ≤ h5 := le_trans hh_a2 (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hkS_le : kS ≤ k := by linarith only [hkSkT]
  have hkT_le : kT ≤ k := by linarith only [hkSkT]
  have hL_PB : OuterParamBlockAt stL.mem paramAddr cfg G.n M r := by
    have hp : ∀ j < 12, stL.mem (paramAddr + j) = st.mem (paramAddr + j) := fun j hj =>
      hL_belowH _ (lt_of_lt_of_le (Nat.add_lt_add_left hj paramAddr) (le_trans env.hparH hRoot_le))
    exact ⟨by rw [hp 0 (by decide)]; exact hPB.1, by rw [hp 1 (by decide)]; exact hPB.2.1,
      by rw [hp 2 (by decide)]; exact hPB.2.2.1, by rw [hp 3 (by decide)]; exact hPB.2.2.2.1,
      by rw [hp 4 (by decide)]; exact hPB.2.2.2.2.1, by rw [hp 5 (by decide)]; exact hPB.2.2.2.2.2.1,
      by rw [hp 6 (by decide)]; exact hPB.2.2.2.2.2.2.1, by rw [hp 7 (by decide)]; exact hPB.2.2.2.2.2.2.2.1,
      by rw [hp 8 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.1, by rw [hp 9 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.1,
      by rw [hp 10 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.1, by rw [hp 11 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.2⟩
  have hL_E : EdgesAt stL.mem edgesAddr H.edges := fun i hi =>
    ⟨by rw [hL_belowH (edgesAddr + 2 * i) (lt_of_lt_of_le (Nat.add_lt_add_left (by linarith only [hi]) edgesAddr) hEA_h)]; exact (hE i hi).1,
     by rw [hL_belowH (edgesAddr + 2 * i + 1) (lt_of_lt_of_le (by linarith only [hi] : edgesAddr + 2 * i + 1 < edgesAddr + 2 * e) hEA_h)]; exact (hE i hi).2⟩
  have hL_nl : stL.mem nextLblAddr = nl₀ := by
    rw [hL_belowH nextLblAddr (lt_of_lt_of_le (Nat.lt_succ_self nextLblAddr) (le_trans env.hnextH hRoot_le)), hnl]
  -- Child 1 (`S`)
  have hlt1 : (H.restrict S).edges.length < e := by rw [he1_eq, ← he_eq]; exact hlt1_in
  have hlt2 : (H.restrict (H.vertSet \ S)).edges.length < e := by rw [he2_eq, ← he_eq]; exact hlt2_in
  have hCh1 := recChild_runs env hSub hIH hRep hXV hSorted hSX
    (Nat.le_of_lt_succ (lt_of_lt_of_le hlt1 heBound)) (le_trans (le_of_lt hlt1) heM)
    (rK := 27) (rV := 19) (rE := 22) (rAct := 24) (rRest := 29) (rStrip := 30) (rH := 26)
    (by decide) (by decide) (by decide)
    (edgesAddr := edgesAddr) (vSAddr := sAddr) (eSAddr := e1Addr)
    (actSAddr := act1Addr) (hCur := h5) (nl₀ := nl₀) (st := stL)
    (le_trans hRoot_le hh_h5)
    (le_trans hEA_h hh_h5)
    (by dsimp only [h5, h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr, tAddr]; linarith only [hkS_le])
    (by dsimp only [h5, h4, act2Addr, act1Addr, e2Addr]; linarith only [])
    (by dsimp only [h5, h4, act2Addr]; linarith only [hkS_le])
    hdLE
    (Or.inr (le_trans hEA_h hh_e1))
    (Or.inr (by dsimp only [e1Addr, lenAddr, tAddr]; linarith only [hkS_le]))
    (Or.inr (by dsimp only [act1Addr, e2Addr, e1Addr, lenAddr, tAddr]; linarith only [hkS_le]))
    (Or.inr (by dsimp only [act1Addr, e2Addr]; linarith only []))
    (le_trans hRoot_le hh_s)
    (le_trans hRoot_le hh_e1)
    (le_trans hRoot_le hh_a1)
    hL_PB hL_S hL_E hL_loc0 hL_nl
    (by linarith only [hkS_le, hnl_le]) hZeroL (by linarith only [hh5_sp, hSpace'])
    (by rw [hL_r0_9 2 (by decide), hr2]) (by rw [hL_r0_9 3 (by decide), hr3])
    (by rw [hL_r0_9 4 (by decide), hr4]) (by rw [hL_r0_9 5 (by decide), hr5])
    (by rw [hL_r0_9 6 (by decide), hr6]) (by rw [hL_r0_9 7 (by decide), hr7])
    hL_27 hL_19 hL_22 hL_24 hL_26
  rcases hCh1 with ⟨stC1, h6, cC1, o₁, hrunC1, ho1Spec, ho1Lbl, ho1Nl, hh6_ge, hh6_le,
    hZero6, hloc6, hC1_fr, hC1_26, hC1_other, hcC1⟩
  -- Child 2 (`H.vertSet \ S`)
  set nl₂ := stC1.mem nextLblAddr
  have hC1_PB : OuterParamBlockAt stC1.mem paramAddr cfg G.n M r := by
    have hp : ∀ j < 12, stC1.mem (paramAddr + j) = stL.mem (paramAddr + j) := fun j hj => by
      have hj_h : paramAddr + j < h := lt_of_lt_of_le (Nat.add_lt_add_left hj paramAddr) (le_trans env.hparH hRoot_le)
      exact hC1_fr _ (lt_of_lt_of_le hj_h hh_h5) (Or.inl (lt_of_lt_of_le hj_h hh_e1))
        (Or.inl (lt_of_lt_of_le hj_h hh_a1))
        (fun u hu => by have huN := Finset.mem_range.mp (hXV (hSX hu)); rcases env.hdPLb with h1 | h1 <;> linarith only [hj, huN, h1])
        (by rcases env.hdPN with h1 | h1 <;> linarith only [hj, h1])
    exact ⟨by rw [hp 0 (by decide)]; exact hL_PB.1, by rw [hp 1 (by decide)]; exact hL_PB.2.1,
      by rw [hp 2 (by decide)]; exact hL_PB.2.2.1, by rw [hp 3 (by decide)]; exact hL_PB.2.2.2.1,
      by rw [hp 4 (by decide)]; exact hL_PB.2.2.2.2.1, by rw [hp 5 (by decide)]; exact hL_PB.2.2.2.2.2.1,
      by rw [hp 6 (by decide)]; exact hL_PB.2.2.2.2.2.2.1, by rw [hp 7 (by decide)]; exact hL_PB.2.2.2.2.2.2.2.1,
      by rw [hp 8 (by decide)]; exact hL_PB.2.2.2.2.2.2.2.2.1, by rw [hp 9 (by decide)]; exact hL_PB.2.2.2.2.2.2.2.2.2.1,
      by rw [hp 10 (by decide)]; exact hL_PB.2.2.2.2.2.2.2.2.2.2.1, by rw [hp 11 (by decide)]; exact hL_PB.2.2.2.2.2.2.2.2.2.2.2⟩
  have hC1_T : ListAt stC1.mem tAddr (H.restrict (H.vertSet \ S)).verts := fun i hi => by
    have hi_k : i < k := lt_of_lt_of_le hi hkT_le
    rw [hC1_fr (tAddr + i)
          (by dsimp only [h5, h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr]; linarith only [hi_k])
          (Or.inl (by dsimp only [e1Addr, lenAddr]; linarith only [hi_k]))
          (Or.inl (by dsimp only [act1Addr, e2Addr, e1Addr, lenAddr]; linarith only [hi_k]))
          (fun u hu => by
            have huH := lt_of_lt_of_le (Nat.add_lt_add_left (Finset.mem_range.mp (hXV (hSX hu))) labelsAddr) (le_trans env.hlblH hRoot_le)
            linarith only [huH, hh_t])
          (by have hnH := lt_of_lt_of_le (Nat.lt_succ_self nextLblAddr) (le_trans env.hnextH hRoot_le); linarith only [hnH, hh_t])]
    exact hL_T i hi
  have hC1_E : EdgesAt stC1.mem edgesAddr H.edges := fun i hi => by
    have hm : ∀ j < 2 * e, stC1.mem (edgesAddr + j) = stL.mem (edgesAddr + j) := fun j hj =>
      hC1_fr (edgesAddr + j) (lt_of_lt_of_le (Nat.add_lt_add_left hj edgesAddr) (le_trans hEA_h hh_h5))
        (Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hj edgesAddr) (le_trans hEA_h hh_e1)))
        (Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hj edgesAddr) (le_trans hEA_h hh_a1)))
        (fun u hu => by have huN := Finset.mem_range.mp (hXV (hSX hu)); rcases hdLbE with h1 | h1 <;> linarith only [hj, huN, h1])
        (by rcases hdNE with h1 | h1 <;> linarith only [hj, h1])
    exact ⟨by rw [hm (2 * i) (by linarith only [hi])]; exact (hL_E i hi).1,
           by rw [Nat.add_assoc, hm (2 * i + 1) (by linarith only [hi]), ← Nat.add_assoc]; exact (hL_E i hi).2⟩
  have hCh2 := recChild_runs env hSub hIH hRep hXV hSorted Finset.sdiff_subset
    (Nat.le_of_lt_succ (lt_of_lt_of_le hlt2 heBound)) (le_trans (le_of_lt hlt2) heM)
    (rK := 28) (rV := 20) (rE := 23) (rAct := 25) (rRest := 29) (rStrip := 30) (rH := 26)
    (by decide) (by decide) (by decide)
    (edgesAddr := edgesAddr) (vSAddr := tAddr) (eSAddr := e2Addr)
    (actSAddr := act2Addr) (hCur := h6) (nl₀ := nl₂) (st := stC1)
    (le_trans (le_trans hRoot_le hh_h5) hh6_ge)
    (le_trans (le_trans hEA_h hh_h5) hh6_ge)
    (by have ht_le : tAddr + k ≤ h5 := by dsimp only [h5, h4, act2Addr, act1Addr, e2Addr, e1Addr, lenAddr]; linarith only []
        linarith only [hkT_le, ht_le, hh6_ge])
    (by have he2_le : e2Addr + 2 * e ≤ h5 := by dsimp only [h5, h4, act2Addr, act1Addr]; linarith only []
        linarith only [he2_le, hh6_ge])
    (by have ha2_le : act2Addr + k ≤ h5 := by dsimp only [h5, h4]; linarith only []
        linarith only [hkT_le, ha2_le, hh6_ge])
    hdLE
    (Or.inr (le_trans hEA_h hh_e2))
    (Or.inr (by dsimp only [e2Addr, e1Addr, lenAddr]; linarith only [hkT_le]))
    (Or.inr (by dsimp only [act2Addr, act1Addr, e2Addr, e1Addr, lenAddr]; linarith only [hkT_le]))
    (Or.inr (by dsimp only [act2Addr, act1Addr]; linarith only []))
    (le_trans hRoot_le hh_t)
    (le_trans hRoot_le hh_e2)
    (le_trans hRoot_le hh_a2)
    hC1_PB hC1_T hC1_E hloc6 rfl (by linarith only [ho1Nl, hkSkT, hnl_le]) hZero6
    (by rw [he1_act] at hh6_le; linarith only [hh6_le, hh5_sp, hSpace'])
    (by rw [hC1_other 2 (by decide) (by decide) (by decide), hL_r0_9 2 (by decide), hr2])
    (by rw [hC1_other 3 (by decide) (by decide) (by decide), hL_r0_9 3 (by decide), hr3])
    (by rw [hC1_other 4 (by decide) (by decide) (by decide), hL_r0_9 4 (by decide), hr4])
    (by rw [hC1_other 5 (by decide) (by decide) (by decide), hL_r0_9 5 (by decide), hr5])
    (by rw [hC1_other 6 (by decide) (by decide) (by decide), hL_r0_9 6 (by decide), hr6])
    (by rw [hC1_other 7 (by decide) (by decide) (by decide), hL_r0_9 7 (by decide), hr7])
    (by rw [hC1_other 28 (by decide) (by decide) (by decide), hL_28])
    (by rw [hC1_other 20 (by decide) (by decide) (by decide), hL_20])
    (by rw [hC1_other 23 (by decide) (by decide) (by decide), hL_23])
    (by rw [hC1_other 25 (by decide) (by decide) (by decide), hL_25])
    hC1_26
  rcases hCh2 with ⟨stC2, h7, cC2, o₂, hrunC2, ho2Spec, ho2Lbl, ho2Nl, hh7_ge, hh7_le,
    hZero7, hloc7, hC2_fr, hC2_26, _, hcC2⟩
  have hRet : Runs w pProg ω (.ret (.reg 26)) stC2 (.returned h7) stC2 2 :=
    runs_ret_iff.mpr ⟨h7, by simp [Expr.eval, hC2_26], rfl, rfl, by simp [Expr.size]⟩
  rcases runs_seq_iff.mp hrunC1 with ⟨_, _, _, hno, _⟩ | ⟨stC1a, cC1a, cC1bc, hC1a, hC1bc, rfl⟩
  · cases hno
  rcases runs_seq_iff.mp hC1bc with ⟨_, _, _, hno, _⟩ | ⟨stC1b, cC1b, cC1c, hC1b, hC1c, rfl⟩
  · cases hno
  rcases runs_seq_iff.mp hrunC2 with ⟨_, _, _, hno, _⟩ | ⟨stC2a, cC2a, cC2bc, hC2a, hC2bc, rfl⟩
  · cases hno
  rcases runs_seq_iff.mp hC2bc with ⟨_, _, _, hno, _⟩ | ⟨stC2b, cC2b, cC2c, hC2b, hC2c, rfl⟩
  · cases hno
  have hTailRun :=
    runs_seq_iff.mpr (Or.inr ⟨stC1a, cC1a, _, hC1a,
      runs_seq_iff.mpr (Or.inr ⟨stC1b, cC1b, _, hC1b,
        runs_seq_iff.mpr (Or.inr ⟨stC1, cC1c, _, hC1c,
          runs_seq_iff.mpr (Or.inr ⟨stC2a, cC2a, _, hC2a,
            runs_seq_iff.mpr (Or.inr ⟨stC2b, cC2b, _, hC2b,
              runs_seq_iff.mpr (Or.inr ⟨stC2, cC2c, 2, hC2c, hRet, rfl⟩),
              rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  rcases hCutPreChain _ _ _ _ hTailRun with ⟨cTot, hrunAll, hcTot⟩
  have ho1Lbl_end : LabelsMatchParts stC2.mem labelsAddr S
      ((iso₁.map fun v => ({v} : Finset ℕ)) ++ o₁.parts) nl₀ nl₂ :=
    labelsMatchParts_congr ho1Lbl fun v hv => by
      have hv_h : labelsAddr + v < h :=
        lt_of_lt_of_le (Nat.add_lt_add_left (Finset.mem_range.mp (hXV (hSX hv))) labelsAddr)
          (le_trans env.hlblH hRoot_le)
      exact hC2_fr (labelsAddr + v) (lt_of_lt_of_le hv_h (le_trans hh_h5 hh6_ge))
        (Or.inl (lt_of_lt_of_le hv_h hh_e2)) (Or.inl (lt_of_lt_of_le hv_h hh_a2))
        (fun u hu => by
          have huv : v ≠ u := fun h => (Finset.mem_sdiff.mp hu).2 (h ▸ hv)
          intro heq; exact huv (Nat.add_left_cancel heq))
        (by have hvN := Finset.mem_range.mp (hXV (hSX hv)); rcases env.hdLbN with h1 | h1 <;> linarith only [hvN, h1])
  have hAllLbl : LabelsMatchParts stC2.mem labelsAddr H.vertSet
      (((iso₁.map fun v => ({v} : Finset ℕ)) ++ o₁.parts) ++
        ((iso₂.map fun v => ({v} : Finset ℕ)) ++ o₂.parts)) nl₀ (stC2.mem nextLblAddr) := by
    rw [← Finset.union_sdiff_of_subset hSX]
    exact labelsMatchParts_union disjoint_sdiff_self_right ho1Lbl_end ho2Lbl
  have hSpec := progRecSpec_cut_combine (act₁ := act₁) (act₂ := act₂) (S := S)
    hRep hSX he1 hst1.1 hst1.2.1 hst1.2.2.1 hst1.2.2.2.2.1 he1_in
    hst2.1 hst2.2.1 hst2.2.2.1 hst2.2.2.2.2.1 he2_in h32
    (by rw [he1_act]; exact hsh1) (by rw [he2_act]; exact hsh2) ho1Spec ho2Spec
  refine ⟨h7, stC2, cTot, hrunAll, _, hSpec, hAllLbl, by linarith only [ho1Nl, ho2Nl, hkSkT],
    le_trans hh_h5 (le_trans hh6_ge hh7_ge),
    by rw [he1_act] at hh6_le; rw [he2_act] at hh7_le; linarith only [hh5_sp, hh6_le, hh7_le], hZero7, hloc7, ?_, ?_⟩
  · intro a ha haLb haN
    rw [hC2_fr a (lt_of_lt_of_le ha (le_trans hh_h5 hh6_ge)) (Or.inl (lt_of_lt_of_le ha hh_e2))
          (Or.inl (lt_of_lt_of_le ha hh_a2)) (fun u hu => haLb u (Finset.sdiff_subset hu)) haN,
        hC1_fr a (lt_of_lt_of_le ha hh_h5) (Or.inl (lt_of_lt_of_le ha hh_e1))
          (Or.inl (lt_of_lt_of_le ha hh_a1)) (fun u hu => haLb u (hSX hu)) haN,
        hL_belowH a ha]
  · dsimp only
    simp only [outerRoundPortCutCost, portGraphCost, outerGameStepBound] at hcTot hc3
    set rs := runnerScale explicitProgram
    set F := outerGameCostFactor C_core C_rt
    set pe := recPerEdgeCost cfg C_core C_rt M r routeC
    set pw := recPerWitCost cfg M r
    have hgame_mul : F * (lc + 2 * e) + 40 * e * r ≤
        e * (F * (modelPerEdge cfg M r routeC + 2) + 40 * r) := by
      have h1 : lc + 2 * e ≤ e * (modelPerEdge cfg M r routeC + 2) := by
        have : e * (modelPerEdge cfg M r routeC + 2) = e * modelPerEdge cfg M r routeC + 2 * e := by ring
        linarith only [hlc_le, this]
      calc F * (lc + 2 * e) + 40 * e * r
          ≤ F * (e * (modelPerEdge cfg M r routeC + 2)) + 40 * e * r :=
            Nat.add_le_add_right (Nat.mul_le_mul_left F h1) _
        _ = e * (F * (modelPerEdge cfg M r routeC + 2) + 40 * r) := by ring
    have hF_le : F * (lc + e + 1) ≤ F * (lc + 2 * e) := Nat.mul_le_mul_left F (by linarith only [he1])
    have h40r_le : 40 * r ≤ 40 * e * r := by
      calc 40 * r = 40 * 1 * r := by ring
        _ ≤ 40 * e * r := Nat.mul_le_mul_right r (Nat.mul_le_mul_left 40 he1)
    have hpe_exp : e * pe =
        e * (F * (modelPerEdge cfg M r routeC + 2) + 40 * r) + (rs * 760) * e + 8000 * e := by
      unfold pe recPerEdgeCost; ring
    have hdistE : (e + o₁.edgeSum + o₂.edgeSum) * pe = e * pe + o₁.edgeSum * pe + o₂.edgeSum * pe := by ring
    have hdistW : (o₁.witnessEdgeSum + o₂.witnessEdgeSum) * pw =
        o₁.witnessEdgeSum * pw + o₂.witnessEdgeSum * pw := by ring
    have hpg_exp : (rs * 760 + 1900) * e = (rs * 760) * e + 1900 * e := by ring
    linarith only [hcTot, hc3, hcC1, hcC2, hgame_mul, hF_le, h40r_le, hpe_exp, hdistE, hdistW, hpg_exp,
      hk_le_2e, hkSkT, hkU_le, hsum_e12, he1_act, he2_act, he1]


end MinCostFlow.ExpanderDecomp
