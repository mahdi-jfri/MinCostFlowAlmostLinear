module

public import MinCostFlow.SparseCore.Program.OrdStoreMovePrep
import Mathlib.Tactic

/-!
# Order Store `moveEnds` Passes 3–4: Splay Position Scan and Heapsort

This file implements and verifies Passes 3 and 4 of `ordMoveEndsBody`:
* Pass 3 (`ordMovePosLoop`): for each deduplicated live candidate `u` in `scratch[0 .. 2*cnt - 1]`,
  calls `ordSplayRoot [b, u]`. If `u` belongs to vertex `v`, records `(u.left.sz, u)` at
  `scratch[2 * out .. 2 * out + 1]`.
* Pass 4: calls `ordHeapSort [scratch, out]` to sort the `out` selected nodes of vertex `v` by
  their exact in-order index in `(S.trees v).toList`, recovering the exact filtered sublist.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState MinCostFlow.DynSpanner.Program

/-- Pass 3 of `moveEnds`: splays each candidate in `scratch[0 .. 2*cnt - 1]` and collects
`(pos, u)` pairs for candidates belonging to vertex `v`. -/
def ordMovePosLoop (splayRootProc : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 11))
    (.assign 13 (.load (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1))) ;;
     .call 14 splayRootProc [.reg 0, .reg 13] ;;
     .cond (.bin .eq (.reg 14) (.bin .add (.reg 1) (.const 1)))
       (.assign 15 (.load (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13)))) ;;
        .assign 16 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 15))) (.const 4))) ;;
        .store (.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))) (.reg 16) ;;
        .store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))) (.const 1)) (.reg 13) ;;
        .assign 12 (.bin .add (.reg 12) (.const 1)))
       .nop ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

theorem ordMovePosLoop_noRand (srP : ℕ) : (ordMovePosLoop srP).NoRand := by
  simp [ordMovePosLoop, Stmt.NoRand]

theorem ordMovePosLoop_runs
    {w b v scratch rotProc stepProc splayProc splayRootProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hsplayRoot : p.procs[splayRootProc]? = some (ordSplayRootBody splayProc)) (ω : ℕ → Bool)
    {st0 : State} {ord : ℕ → List End} {S : OrdStoreState} {cand : List ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S st0.mem) (hv : v < S.vCap)
    (hnd : cand.Nodup) (hlive : ∀ u ∈ cand, ∃ w0 < S.vCap, u ∈ (S.trees w0).toList)
    (hscr0 : ∀ i < cand.length, st0.mem (scratch + 2 * i + 1) = cand.getD i 0)
    (hz0 : ZeroFrom st0.mem (scratch + 2 * cand.length))
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hscr_w : scratch + 2 * cand.length < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr0 : st0.regs 0 = b) (hr1 : st0.regs 1 = v) (hr6 : st0.regs 6 = scratch)
    (hr9 : st0.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr10 : st0.regs 10 = 0) (hr11 : st0.regs 11 = cand.length) (hr12 : st0.regs 12 = 0) :
    ∃ st' c, ∃ S' : OrdStoreState, ∃ pairs : List (ℕ × ℕ),
      Runs w p ω (ordMovePosLoop splayRootProc) st0 .normal st' c ∧
      (∀ r, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → st'.regs r = st0.regs r) ∧
      st'.regs 12 = pairs.length ∧ pairs.length ≤ cand.length ∧
      OrdInv ord S' ∧ OrdArenaAt b S' st'.mem ∧
      S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
      (∀ u, (S'.trees u).toList = (S.trees u).toList) ∧
      sumCountNodes S' = sumCountNodes S ∧
      readPairs st'.mem scratch pairs.length = pairs ∧
      (pairs.map Prod.snd).Nodup ∧
      (∀ q ∈ pairs, q.2 ∈ (S.trees v).toList ∧ q.1 = (S.trees v).toList.idxOf q.2) ∧
      (∀ u ∈ (S.trees v).toList, u ∈ pairs.map Prod.snd ↔ u ∈ cand) ∧
      ZeroFrom st'.mem (scratch + 2 * cand.length) ∧
      (∀ a < scratch, ¬ ordFoot b S.vCap S.eCap a → st'.mem a = st0.mem a) ∧
      c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
        ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 4200 * ((cand.length + 1) * ordStoreLog S.eCap) := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  have hheap_foot : b + ordArenaSize S.vCap S.eCap ≤ scratch + 2 * cand.length := by omega
  have hloop : ∀ rem (i : ℕ) (st : State) (Si : OrdStoreState) (pairs : List (ℕ × ℕ)),
      i + rem = cand.length →
      OrdInv ord Si → OrdArenaAt b Si st.mem →
      Si.vCap = S.vCap → Si.eCap = S.eCap →
      (∀ u, (Si.trees u).toList = (S.trees u).toList) →
      sumCountNodes Si = sumCountNodes S →
      st.regs 0 = b → st.regs 1 = v → st.regs 6 = scratch → st.regs 9 = nb →
      st.regs 10 = i → st.regs 11 = cand.length → st.regs 12 = pairs.length →
      pairs.length ≤ i →
      (∀ t, i ≤ t → t < cand.length → st.mem (scratch + 2 * t + 1) = cand.getD t 0) →
      readPairs st.mem scratch pairs.length = pairs →
      (pairs.map Prod.snd).Nodup →
      (∀ q ∈ pairs, q.2 ∈ (S.trees v).toList ∧ q.1 = (S.trees v).toList.idxOf q.2) →
      (∀ u ∈ (S.trees v).toList, u ∈ pairs.map Prod.snd ↔ u ∈ cand.take i) →
      ZeroFrom st.mem (scratch + 2 * cand.length) →
      (∀ a < scratch, ¬ ordFoot b S.vCap S.eCap a → st.mem a = st0.mem a) →
      ∃ st' c, ∃ S' : OrdStoreState, ∃ pairs' : List (ℕ × ℕ),
        Runs w p ω (ordMovePosLoop splayRootProc) st .normal st' c ∧
        (∀ r, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → st'.regs r = st.regs r) ∧
        st'.regs 12 = pairs'.length ∧ pairs'.length ≤ cand.length ∧
        OrdInv ord S' ∧ OrdArenaAt b S' st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        (∀ u, (S'.trees u).toList = (S.trees u).toList) ∧
        sumCountNodes S' = sumCountNodes S ∧
        readPairs st'.mem scratch pairs'.length = pairs' ∧
        (pairs'.map Prod.snd).Nodup ∧
        (∀ q ∈ pairs', q.2 ∈ (S.trees v).toList ∧ q.1 = (S.trees v).toList.idxOf q.2) ∧
        (∀ u ∈ (S.trees v).toList, u ∈ pairs'.map Prod.snd ↔ u ∈ cand) ∧
        ZeroFrom st'.mem (scratch + 2 * cand.length) ∧
        (∀ a < scratch, ¬ ordFoot b S.vCap S.eCap a → st'.mem a = st0.mem a) ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT Si + 4200 * rem * ordStoreLog S.eCap + 50 := by
    intro rem
    induction rem with
    | zero =>
      intro i st Si pairs hi hinvi harenai hvi hei hlisti hcnti r0 r1 r6 r9 r10 r11 r12 hple
        hrem_scr hrp hpnd hppos hpmem hzi hfri
      have hi_eq : i = cand.length := by omega
      subst hi_eq
      have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r11) (by omega) (by omega)
      refine ⟨st, _, Si, pairs, ord_runs_loop_false hcond, fun _ _ _ _ _ _ _ => rfl, r12, hple,
        hinvi, harenai, hvi, hei, hlisti, hcnti, hrp, hpnd, hppos,
        fun u hu => by simpa [List.take_length] using hpmem u hu, hzi, hfri,
        by simp [Expr.size_bin, Expr.size_reg]; omega⟩
    | succ rem ih =>
      intro i st Si pairs hi hinvi harenai hvi hei hlisti hcnti r0 r1 r6 r9 r10 r11 r12 hple
        hrem_scr hrp hpnd hppos hpmem hzi hfri
      have hi_lt : i < cand.length := by omega
      have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r11) hi_lt (by omega)
      set u := cand.getD i 0 with hu_def
      have hu_eq : cand[i]'hi_lt = u := by simp [hu_def, List.getD_eq_getElem?_getD, hi_lt]
      have hu_mem_cand : u ∈ cand := hu_eq ▸ List.getElem_mem hi_lt
      have hu_ntake : u ∉ cand.take i := by
        intro hm
        have hsp := List.take_append_drop i cand
        rw [List.drop_eq_getElem_cons hi_lt, hu_eq] at hsp
        have hnd' := hnd; rw [← hsp, List.nodup_append] at hnd'
        exact hnd'.2.2 u hm u List.mem_cons_self rfl
      have htake_succ : cand.take (i + 1) = cand.take i ++ [u] := by
        rw [List.take_succ_eq_append_getElem hi_lt, hu_eq]
      obtain ⟨w0, hw0, hu_mem0⟩ := hlive u hu_mem_cand
      have hu_memi : u ∈ (Si.trees w0).toList := by rw [hlisti w0]; exact hu_mem0
      have ha13 : Runs w p ω
          (.assign 13 (.load (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)))) st .normal
          { st with regs := Function.update st.regs 13 u } _ :=
        runs_assign_iff.mpr ⟨u, Expr.eval_load_of_eq (by
          have he : (Expr.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)).eval w st =
              some (scratch + (i + i) + 1) :=
            Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r6)
              (Expr.eval_add (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r10) (by omega)) (by omega))
              (Expr.eval_const (by omega)) (by omega)
          rwa [show scratch + (i + i) + 1 = scratch + 2 * i + 1 by omega] at he) (hrem_scr i (le_refl i) hi_lt),
          rfl, rfl, rfl⟩
      set st1 : State := { st with regs := Function.update st.regs 13 u }
      obtain ⟨oSR, stSR, cSR, hrunSR, ⟨S1, hoSR, hinv1, harena1, hfr1, hv1, he1, hrt1, _, hlist1, hcnt1, hphi1⟩, hcSR⟩ :=
        ordSplayRootBody_runs hrot hstep hsplay ω hinvi harenai (by rw [hvi]; exact hw0) hu_memi
          (by rw [hvi, hei]; exact hheap_foot) hzi hscr_w hwide (pos := st1.pos)
      have hcallSR : Runs w p ω (.call 14 splayRootProc [.reg 0, .reg 13]) st1 .normal
          { stSR with regs := Function.update st1.regs 14 (w0 + 1) } (argsSize [.reg 0, .reg 13] + cSR + 1) :=
        runs_call_iff.mpr ⟨[b, u], ordSplayRootBody splayProc, oSR, stSR, cSR,
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [st1, r0]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st1])) (evalArgs_nil _ _)),
          hsplayRoot, hrunSR, rfl, by simp [hoSR], rfl⟩
      set st2 : State := { stSR with regs := Function.update st1.regs 14 (w0 + 1) }
      have hphi1_mul : cSR + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT Si + 4000 * ordStoreLog S.eCap := by
        unfold ordPhi; rw [hcnt1]
        have h1 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi1
        have h2 : ORD_PHI_WEIGHT * (sumTreePhi S1 + (Si.trees w0).depthOf u / 2) =
            ORD_PHI_WEIGHT * sumTreePhi S1 + ORD_PHI_WEIGHT * ((Si.trees w0).depthOf u / 2) := by ring
        have h3 : ORD_PHI_WEIGHT * (sumTreePhi Si + 3 * ordStoreLog Si.eCap) =
            ORD_PHI_WEIGHT * sumTreePhi Si + 3 * ORD_PHI_WEIGHT * ordStoreLog Si.eCap := by ring
        rw [hei] at h1 h3
        unfold ORD_PHI_WEIGHT at h1 h2 h3 ⊢; unfold ORD_SPLAY_RATE at hcSR
        have h650 : ((Si.trees w0).depthOf u / 2) * 650 ≤ 1000 * ((Si.trees w0).depthOf u / 2) := by omega
        omega
      have hstSR_scr : ∀ a, scratch ≤ a → a < scratch + 2 * cand.length → stSR.mem a = st.mem a := fun a ha1 ha2 =>
        hfr1.2 a ha2 (fun hf => by rw [hvi, hei] at hf; unfold ordFoot at hf; omega)
      have hstSR_lt : ∀ a < scratch, ¬ ordFoot b S.vCap S.eCap a → stSR.mem a = st0.mem a := fun a ha hnf =>
        (hfr1.2 a (by omega) (by rw [hvi, hei]; exact hnf)).trans (hfri a ha hnf)
      have hrp1 : readPairs stSR.mem scratch pairs.length = pairs :=
        (readPairs_congr fun a ha1 ha2 => hstSR_scr a ha1 (by omega)).trans hrp
      -- Branch on w0 = v
      have hbranch : ∃ st3 c3, ∃ pairs1 : List (ℕ × ℕ),
          Runs w p ω
            (.cond (.bin .eq (.reg 14) (.bin .add (.reg 1) (.const 1)))
              (.assign 15 (.load (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13)))) ;;
               .assign 16 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 15))) (.const 4))) ;;
               .store (.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))) (.reg 16) ;;
               .store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))) (.const 1)) (.reg 13) ;;
               .assign 12 (.bin .add (.reg 12) (.const 1)))
              .nop) st2 .normal st3 c3 ∧
          (∀ r, r ≠ 12 → r ≠ 15 → r ≠ 16 → st3.regs r = st2.regs r) ∧
          st3.regs 12 = pairs1.length ∧ pairs1.length ≤ i + 1 ∧
          OrdArenaAt b S1 st3.mem ∧
          (∀ t, i + 1 ≤ t → t < cand.length → st3.mem (scratch + 2 * t + 1) = cand.getD t 0) ∧
          readPairs st3.mem scratch pairs1.length = pairs1 ∧
          (pairs1.map Prod.snd).Nodup ∧
          (∀ q ∈ pairs1, q.2 ∈ (S.trees v).toList ∧ q.1 = (S.trees v).toList.idxOf q.2) ∧
          (∀ z ∈ (S.trees v).toList, z ∈ pairs1.map Prod.snd ↔ z ∈ cand.take (i + 1)) ∧
          ZeroFrom st3.mem (scratch + 2 * cand.length) ∧
          (∀ a < scratch, ¬ ordFoot b S.vCap S.eCap a → st3.mem a = st0.mem a) ∧
          c3 ≤ 60 := by
        by_cases hwv : v = w0
        · subst hwv
          have hc1 : (Expr.bin .eq (.reg 14) (.bin .add (.reg 1) (.const 1))).eval w st2 = some 1 :=
            Expr.eval_eq_true (Expr.eval_reg_of_eq (v := v + 1) (by simp [st2]))
              (Expr.eval_add (Expr.eval_reg_of_eq (v := v) (by simp [st2, st1, r1]))
                (Expr.eval_const (by omega)) (by omega)) rfl (by omega)
          obtain ⟨L, R, htv1⟩ : ∃ L R, S1.trees v = .node u L R := by
            cases htv : S1.trees v with
            | leaf => exfalso; have h1 := hlist1 v; rw [htv, hlisti v] at h1; exact List.not_mem_nil (h1 ▸ hu_mem0)
            | node id l r => simp only [htv, AuxTree.rootId] at hrt1; exact ⟨l, r, by rw [hrt1]⟩
          have htv1_inv : TreeInv ordPayload S1.splay (.node u L R) := htv1 ▸ hinv1.tree_inv v (by rw [hv1, hvi]; exact hv)
          rcases htv1_inv.sub with ⟨-, huL, -, -, -, -, -, hsubL, -⟩
          rcases AuxTree.nodup_node_unfold htv1_inv.nodup with ⟨-, hu_nL, -, -, -⟩
          have hu_c1 : u ≤ S1.nextNode := (hinv1.live_le_nextNode (by rw [hv1, hvi]; exact hv) (by rw [hlist1 v, hlisti v]; exact hu_mem0)).2
          have hL_c1 : L.rootId ≤ S1.nextNode := by
            cases L with
            | leaf => simp [AuxTree.rootId]
            | node lid ll lr =>
              have hmem : lid ∈ (S1.trees v).toList := by
                rw [htv1]; exact List.mem_append_left _ (List.mem_append_left _ (AuxTree.rootId_mem (t := .node lid ll lr) (by simp)))
              exact (hinv1.live_le_nextNode (by rw [hv1, hvi]; exact hv) hmem).2
          have hnb_w : nb + 8 * (S1.nextNode + 1) < 2 ^ w := by
            have := ordNodesBase_end b S.vCap S.eCap; have := hinv1.next_le; rw [he1, hei] at this; rw [hnb]; omega
          have hm_uL : stSR.mem (nb + 8 * u) = L.rootId := by
            have h := (harena1.nodes_at u hu_c1).1; rw [hv1, he1, hvi, hei, ← hnb] at h; simpa [ordNodeAddr, huL] using h
          have hm_Lsz : stSR.mem (nb + 8 * L.rootId + 4) = L.countNodes := by
            have h := (harena1.nodes_at L.rootId hL_c1).2.2.2.2.1; rw [hv1, he1, hvi, hei, ← hnb] at h
            have hlsz : (S1.splay.nodes L.rootId).sz = L.countNodes := by
              cases L with
              | leaf => simp [AuxTree.rootId, AuxTree.countNodes, hinv1.null_node, ordNullNode]
              | node lid ll lr => exact hsubL.2.2.2.2.2.1
            simpa [ordNodeAddr, hlsz] using h
          have hidx_u : (S.trees v).toList.idxOf u = L.countNodes := by
            have h1 : (S.trees v).toList = L.toList ++ u :: R.toList := by
              rw [← hlisti v, ← hlist1 v, htv1]; simp [AuxTree.toList]
            rw [h1, idxOf_append_cons_of_not_mem hu_nL, AuxTree.length_toList]
          have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))))) st2 .normal
              { st2 with regs := Function.update st2.regs 15 L.rootId } _ :=
            runs_assign_iff.mpr ⟨L.rootId, Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [st2, st1, r9]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st2, st1])) (by omega)) (by omega))
              hm_uL, rfl, rfl, rfl⟩
          set st3 : State := { st2 with regs := Function.update st2.regs 15 L.rootId }
          have ha16 : Runs w p ω
              (.assign 16 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 15))) (.const 4)))) st3 .normal
              { st3 with regs := Function.update st3.regs 16 L.countNodes } _ :=
            runs_assign_iff.mpr ⟨L.countNodes, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [st3, st2, st1, r9]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st3])) (by omega)) (by omega))
              (Expr.eval_const (by omega)) (by omega)) hm_Lsz, rfl, rfl, rfl⟩
          set st4 : State := { st3 with regs := Function.update st3.regs 16 L.countNodes }
          have hs1 : Runs w p ω (.store (.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))) (.reg 16)) st4 .normal
              { st4 with mem := Function.update stSR.mem (scratch + 2 * pairs.length) L.countNodes } _ :=
            runs_store_iff.mpr ⟨scratch + 2 * pairs.length, L.countNodes,
              by
                have he : (Expr.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))).eval w st4 =
                    some (scratch + (pairs.length + pairs.length)) :=
                  Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, r6]))
                    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, r12]))
                      (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, r12])) (by omega)) (by omega)
                rwa [show scratch + (pairs.length + pairs.length) = scratch + 2 * pairs.length by omega] at he,
              Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
          set m1 := Function.update stSR.mem (scratch + 2 * pairs.length) L.countNodes
          set st5 : State := { st4 with mem := m1 }
          have hs2 : Runs w p ω
              (.store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))) (.const 1)) (.reg 13)) st5 .normal
              { st5 with mem := Function.update m1 (scratch + 2 * pairs.length + 1) u } _ :=
            runs_store_iff.mpr ⟨scratch + 2 * pairs.length + 1, u,
              by
                have he : (Expr.bin .add (.bin .add (.reg 6) (.bin .add (.reg 12) (.reg 12))) (.const 1)).eval w st5 =
                    some (scratch + (pairs.length + pairs.length) + 1) :=
                  Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r6]))
                    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r12]))
                      (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r12])) (by omega)) (by omega))
                    (Expr.eval_const (by omega)) (by omega)
                rwa [show scratch + (pairs.length + pairs.length) + 1 = scratch + 2 * pairs.length + 1 by omega] at he,
              Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1]), rfl, rfl, rfl⟩
          set m2 := Function.update m1 (scratch + 2 * pairs.length + 1) u
          set st6 : State := { st5 with mem := m2 }
          have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1))) st6 .normal
              { st6 with regs := Function.update st6.regs 12 (pairs.length + 1) } _ :=
            runs_assign_iff.mpr ⟨pairs.length + 1, Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, r12]))
              (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
          have hm2_out : ∀ a, a ≠ scratch + 2 * pairs.length → a ≠ scratch + 2 * pairs.length + 1 → m2 a = stSR.mem a :=
            fun a h1 h2 => by dsimp only [m2, m1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]
          have hrp2 : readPairs m2 scratch (pairs.length + 1) = pairs ++ [(L.countNodes, u)] := by
            have hstep : readPairs m2 scratch (pairs.length + 1) =
                readPairs m2 scratch pairs.length ++ [(m2 (scratch + 2 * pairs.length), m2 (scratch + 2 * pairs.length + 1))] := by
              unfold readPairs; rw [List.range_succ, List.map_append, List.map_singleton]
            rw [hstep]
            have hpre : readPairs m2 scratch pairs.length = pairs :=
              (readPairs_congr fun a ha1 ha2 => hm2_out a (by omega) (by omega)).trans hrp1
            rw [hpre]; dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
          refine ⟨{ st6 with regs := Function.update st6.regs 12 (pairs.length + 1) }, _,
            pairs ++ [(L.countNodes, u)],
            ord_runs_cond_true hc1 Nat.one_ne_zero (ord_runs_seq_normal ha15 (ord_runs_seq_normal ha16
              (ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2 ha12)))),
            fun r h12 h15 h16 => by simp [st6, st5, st4, st3, h12, h15, h16],
            by simp, by simp; omega,
            harena1.congr hinv1.next_le (fun a ha => by
              rw [hv1, he1, hvi, hei] at ha; exact hm2_out a (by unfold ordFoot at ha; omega) (by unfold ordFoot at ha; omega)),
            fun t ht1 ht2 => by
              dsimp only [st6]
              rw [hm2_out _ (by omega) (by omega), hstSR_scr _ (by omega) (by omega)]
              exact hrem_scr t (by omega) ht2,
            by simpa using hrp2,
            by
              rw [List.map_append, List.map_singleton, List.nodup_append]
              refine ⟨hpnd, List.nodup_singleton u, fun a ha b hb h => ?_⟩
              rw [List.mem_singleton.mp hb] at h; subst h
              exact hu_ntake ((hpmem u hu_mem0).mp ha),
            fun q hq => by
              rw [List.mem_append, List.mem_singleton] at hq
              rcases hq with hqp | rfl
              · exact hppos q hqp
              · exact ⟨hu_mem0, hidx_u.symm⟩,
            fun z hz => by
              rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton,
                htake_succ, List.mem_append, List.mem_singleton, hpmem z hz],
            fun a ha => (hm2_out a (by omega) (by omega)).trans (hfr1.1 a ha),
            fun a ha hnf => (hm2_out a (by omega) (by omega)).trans (hstSR_lt a ha hnf),
            by simp [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
        · have hc1 : (Expr.bin .eq (.reg 14) (.bin .add (.reg 1) (.const 1))).eval w st2 = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := w0 + 1) (by simp [st2]))
              (Expr.eval_add (Expr.eval_reg_of_eq (v := v) (by simp [st2, st1, r1]))
                (Expr.eval_const (by omega)) (by omega)) (by omega) (by omega)
          refine ⟨st2, _, pairs, ord_runs_cond_false hc1 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
            fun _ _ _ _ => rfl, by simp [st2, st1, r12], by omega, harena1,
            fun t ht1 ht2 => (hstSR_scr _ (by omega) (by omega)).trans (hrem_scr t (by omega) ht2),
            hrp1, hpnd, hppos,
            fun z hz => by
              rw [htake_succ, List.mem_append, List.mem_singleton, hpmem z hz]
              constructor
              · exact Or.inl
              · rintro (h | rfl)
                · exact h
                · exfalso; exact hinv.disj_trees v w0 hwv u hz hu_mem0,
            hfr1.1, hstSR_lt, by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
      obtain ⟨st3, c3, pairs1, hrun3, hreg3, r12_3, hple3, harena3, hrem3, hrp3, hpnd3, hppos3, hpmem3, hz3, hfr3, hc3⟩ := hbranch
      have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) st3 .normal
          { st3 with regs := Function.update st3.regs 10 (i + 1) } _ :=
        runs_assign_iff.mpr ⟨i + 1, Expr.eval_add
          (Expr.eval_reg_of_eq (by rw [hreg3 10 (by decide) (by decide) (by decide)]; simp [st2, st1, r10]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st4 : State := { st3 with regs := Function.update st3.regs 10 (i + 1) }
      obtain ⟨stF, cF, SF, pairsF, hrunF, hregF, r12F, hpleF, hinvF, harenaF, hvF, heF, hlistF, hcntF,
        hrpF, hpndF, hpposF, hpmemF, hzF, hfrF, hphiF⟩ :=
        ih (i + 1) st4 S1 pairs1 (by omega) hinv1 harena3 (hv1.trans hvi) (he1.trans hei)
          (fun u0 => (hlist1 u0).trans (hlisti u0)) (hcnt1.trans hcnti)
          (by simp [st4, hreg3 0 (by decide) (by decide) (by decide), st2, st1, r0])
          (by simp [st4, hreg3 1 (by decide) (by decide) (by decide), st2, st1, r1])
          (by simp [st4, hreg3 6 (by decide) (by decide) (by decide), st2, st1, r6])
          (by simp [st4, hreg3 9 (by decide) (by decide) (by decide), st2, st1, r9])
          (by simp [st4]) (by simp [st4, hreg3 11 (by decide) (by decide) (by decide), st2, st1, r11])
          (by simp [st4, r12_3]) hple3 hrem3 hrp3 hpnd3 hppos3 hpmem3 hz3 hfr3
      refine ⟨stF, _, SF, pairsF,
        ord_runs_loop_true hcond Nat.one_ne_zero
          (ord_runs_seq_normal ha13 (ord_runs_seq_normal hcallSR (ord_runs_seq_normal hrun3 ha10))) hrunF,
        fun r h10 h12 h13 h14 h15 h16 => by
          rw [hregF r h10 h12 h13 h14 h15 h16]; simp only [st4, Function.update_of_ne h10]
          rw [hreg3 r h12 h15 h16]; simp [st2, st1, h13, h14],
        r12F, hpleF, hinvF, harenaF, hvF, heF, hlistF, hcntF, hrpF, hpndF, hpposF, hpmemF, hzF, hfrF, ?_⟩
      have hmul_step : 4200 * (rem + 1) * ordStoreLog S.eCap =
          4200 * rem * ordStoreLog S.eCap + 4200 * ordStoreLog S.eCap := by ring
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
        argsSize_cons, argsSize_nil] at *
      omega
  obtain ⟨stF, cF, SF, pairsF, hrunF, hregF, r12F, hpleF, hinvF, harenaF, hvF, heF, hlistF, hcntF,
    hrpF, hpndF, hpposF, hpmemF, hzF, hfrF, hphiF⟩ :=
    hloop cand.length 0 st0 S [] (by omega) hinv harena rfl rfl (fun _ => rfl) rfl
      hr0 hr1 hr6 hr9 hr10 hr11 (by simpa using hr12) (by simp)
      (fun t _ ht => hscr0 t ht) (by simp [readPairs]) List.nodup_nil
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => by simp) hz0 (fun _ _ _ => rfl)
  refine ⟨stF, cF, SF, pairsF, hrunF, hregF, r12F, hpleF, hinvF, harenaF, hvF, heF, hlistF, hcntF,
    hrpF, hpndF, hpposF, hpmemF, hzF, hfrF, ?_⟩
  have hmul : 4200 * ((cand.length + 1) * ordStoreLog S.eCap) =
      4200 * cand.length * ordStoreLog S.eCap + 4200 * ordStoreLog S.eCap := by ring
  omega

/-- Combined Passes 3 and 4: splay scan followed by heapsort, yielding the exact sorted
sublist `selNodes` of `(S.trees v).toList` in `scratch[0 .. 2*out - 1]`. -/
theorem ordMovePosSort_runs
    {w b v len arrPtr scratch rotProc stepProc splayProc splayRootProc siftProc sortProc : ℕ}
    {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hsplayRoot : p.procs[splayRootProc]? = some (ordSplayRootBody splayProc))
    (hsift : p.procs[siftProc]? = some (ordSiftDownBody siftProc))
    (hsort : p.procs[sortProc]? = some (ordHeapSortBody siftProc)) (ω : ℕ → Bool)
    {st0 : State} {ord : ℕ → List End} {S : OrdStoreState} {cand : List ℕ} {mem0 : ℕ → ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S st0.mem) (hv : v < S.vCap)
    (hnd : cand.Nodup) (hcle : cand.length ≤ len)
    (hlive : ∀ u ∈ cand, ∃ w0 < S.vCap, u ∈ (S.trees w0).toList)
    (hiff : ∀ u, u ∈ cand ↔ ∃ t < len, mem0 (arrPtr + t) < 2 * S.eCap ∧ S.eNode (mem0 (arrPtr + t)) = u ∧ u ≠ 0)
    (hscr0 : ∀ i < cand.length, st0.mem (scratch + 2 * i + 1) = cand.getD i 0)
    (hz0 : ZeroFrom st0.mem (scratch + 2 * cand.length))
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hscr_w : scratch + 2 * len + 2 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr0 : st0.regs 0 = b) (hr1 : st0.regs 1 = v) (hr6 : st0.regs 6 = scratch)
    (hr9 : st0.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr10 : st0.regs 10 = 0) (hr11 : st0.regs 11 = cand.length) (hr12 : st0.regs 12 = 0) :
    let sel : Finset End := ((readList mem0 arrPtr len).map endOfKey).toFinset
    let selNodes : List ℕ := (S.trees v).toList.filter (fun u => decide (endOfKey (S.splay.nodes u).val ∈ sel))
    ∃ st' c, ∃ S' : OrdStoreState,
      Runs w p ω (ordMovePosLoop splayRootProc ;; .call 17 sortProc [.reg 6, .reg 12]) st0 .normal st' c ∧
      (∀ r, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → st'.regs r = st0.regs r) ∧
      st'.regs 12 = selNodes.length ∧ selNodes.length ≤ cand.length ∧
      OrdInv ord S' ∧ OrdArenaAt b S' st'.mem ∧
      S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
      (∀ u, (S'.trees u).toList = (S.trees u).toList) ∧
      (∀ u < S.vCap, ∀ x ∈ (S.trees u).toList, (S'.splay.nodes x).val = (S.splay.nodes x).val) ∧
      sumCountNodes S' = sumCountNodes S ∧
      (∀ i < selNodes.length, st'.mem (scratch + 2 * i + 1) = selNodes.getD i 0) ∧
      ZeroFrom st'.mem (scratch + 2 * cand.length) ∧
      (∀ a < scratch, ¬ ordFoot b S.vCap S.eCap a → st'.mem a = st0.mem a) ∧
      c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
        ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 5500 * ((len + 1) * ordStoreLog S.eCap) := by
  dsimp only
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  set sel : Finset End := ((readList mem0 arrPtr len).map endOfKey).toFinset
  set selNodes : List ℕ := (S.trees v).toList.filter (fun u => decide (endOfKey (S.splay.nodes u).val ∈ sel))
  obtain ⟨st1, c1, S1, pairs, hrun1, hreg1, r12_1, hple1, hinv1, harena1, hv1, he1, hlist1, hcnt1,
    hrp1, hpnd1, hppos1, hpmem1, hz1, hfr1, hphi1⟩ :=
    ordMovePosLoop_runs hrot hstep hsplay hsplayRoot ω hinv harena hv hnd hlive hscr0 hz0 hfoot
      (by omega) hwide hr0 hr1 hr6 hr9 hr10 hr11 hr12
  obtain ⟨oS, stS, cS, hrunS, ⟨hsortS, hpermS, houtS⟩, hcS⟩ :=
    ordHeapSortBody_runs hsift ω (by omega : scratch + 2 * pairs.length + 2 < 2 ^ w)
      (mem := st1.mem) (pos := st1.pos)
  have hcallS : Runs w p ω (.call 17 sortProc [.reg 6, .reg 12]) st1 .normal
      { stS with regs := Function.update st1.regs 17 oS.value } (argsSize [.reg 6, .reg 12] + cS + 1) :=
    runs_call_iff.mpr ⟨[scratch, pairs.length], ordHeapSortBody siftProc, oS, stS, cS,
      evalArgs_cons (Expr.eval_reg_of_eq (by rw [hreg1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr6))
        (evalArgs_cons (Expr.eval_reg_of_eq r12_1) (evalArgs_nil _ _)),
      hsort, hrunS, rfl, rfl, rfl⟩
  set pairs' := readPairs stS.mem scratch pairs.length
  have hrpS : pairs' = readPairs stS.mem scratch pairs.length := rfl
  rw [hrp1] at hpermS
  have hsel_eq : pairs'.map Prod.snd = selNodes := by
    apply sorted_pairs_eq_filter (hinv.tree_inv v hv).nodup hsortS ((hpermS.map Prod.snd).nodup_iff.mpr hpnd1)
      (fun q hq => hppos1 q (hpermS.mem_iff.mp hq))
    intro u hu
    rw [(hpermS.map Prod.snd).mem_iff, hpmem1 u hu, hiff u]
    have hu_nz : u ≠ 0 := SplayState.SubtreeInv_nonZero (hinv.tree_inv v hv).sub hu
    have hu_klt : (S.splay.nodes u).val < 2 * S.eCap := hinv.key_lt v hv u hu
    have hu_en : S.eNode (S.splay.nodes u).val = u := hinv.eNode_eq_of_mem hv hu
    simp only [decide_eq_true_eq, sel, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨k, hk_rl, hk_eq⟩
      have hkeq : k = (S.splay.nodes u).val := endOfKey_injective hk_eq
      subst hkeq
      obtain ⟨t, ht, hgt⟩ := List.getElem_of_mem hk_rl
      have hlen_rl : (readList mem0 arrPtr len).length = len := readList_length mem0 arrPtr len
      have ht' : t < len := hlen_rl ▸ ht
      have hm_t : mem0 (arrPtr + t) = (S.splay.nodes u).val := by
        have h1 := readList_getElem mem0 arrPtr len t ht; omega
      exact ⟨t, ht', by rw [hm_t]; exact hu_klt, by rw [hm_t]; exact hu_en, hu_nz⟩
    · rintro ⟨t, ht, hklt, hen, _⟩
      refine ⟨mem0 (arrPtr + t), ?_, ?_⟩
      · have hlen_rl : (readList mem0 arrPtr len).length = len := readList_length mem0 arrPtr len
        have hgt := readList_getElem mem0 arrPtr len t (by rw [hlen_rl]; exact ht)
        rw [← hgt]; exact List.getElem_mem (by omega)
      · rcases hinv.eNode_spec (mem0 (arrPtr + t)) hklt with ⟨h0, _⟩ | ⟨_, _, _, hval⟩
        · exfalso; exact hu_nz (hen.symm.trans h0)
        · rw [hen] at hval; rw [hval]
  have hlen_sel : selNodes.length = pairs.length := by
    rw [← hsel_eq, List.length_map, readPairs_length]
  have hout_le_ecap : pairs.length ≤ 2 * S.eCap := by
    have hsub : selNodes.toFinset ⊆ (S.trees v).toList.toFinset := by
      intro x hx; rw [List.mem_toFinset] at hx ⊢; exact (List.mem_filter.mp hx).1
    have hcard := Finset.card_le_card hsub
    have hnd_sel : selNodes.Nodup := (hinv.tree_inv v hv).nodup.filter _
    rw [List.toFinset_card_of_nodup hnd_sel, List.toFinset_card_of_nodup (hinv.tree_inv v hv).nodup,
      AuxTree.length_toList] at hcard
    have hv_le : (S.trees v).countNodes ≤ sumCountNodes S :=
      Finset.single_le_sum (f := fun u => (S.trees u).countNodes) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hv)
    have := hinv.sumCountNodes_le; omega
  have hlog_out : Nat.log 2 (pairs.length + 2) + 1 ≤ 2 * ordStoreLog S.eCap := by
    unfold ordStoreLog
    have h1 : Nat.log 2 (pairs.length + 2) ≤ Nat.log 2 (2 * (S.eCap + 2)) :=
      Nat.log_mono_right (by omega)
    have h2 : Nat.log 2 (2 * (S.eCap + 2)) = Nat.log 2 (S.eCap + 2) + 1 := by
      rw [Nat.mul_comm, Nat.log_mul_base (by decide) (by omega)]
    omega
  have hval_eq : ∀ u < S.vCap, ∀ x ∈ (S.trees u).toList, (S1.splay.nodes x).val = (S.splay.nodes x).val := by
    intro u hu x hx
    have h1 := hinv1.list_eq u (by rw [hv1]; exact hu)
    have h2 := hinv.list_eq u hu
    rw [hlist1 u] at h1; rw [← h1] at h2
    rcases List.getElem_of_mem hx with ⟨i, hi, hgi⟩
    have hm := congrArg (fun l => l[i]?) h2
    simp [hi, hgi] at hm
    exact (endOfKey_injective hm).symm
  refine ⟨{ stS with regs := Function.update st1.regs 17 oS.value }, _, S1,
    ord_runs_seq_normal hrun1 hcallS,
    fun r h10 h12 h13 h14 h15 h16 h17 => by
      simp only [Function.update_of_ne h17]; exact hreg1 r h10 h12 h13 h14 h15 h16,
    by simp [r12_1, hlen_sel], by omega, hinv1,
    harena1.congr hinv1.next_le (fun a ha => by
      rw [hv1, he1] at ha; exact houtS a (Or.inl (by unfold ordFoot at ha; omega))),
    hv1, he1, hlist1, hval_eq, hcnt1,
    fun i hi => by
      have hi' : i < pairs.length := by omega
      have hget : pairs'[i]'(by rw [readPairs_length]; exact hi') = (stS.mem (scratch + 2 * i), stS.mem (scratch + 2 * i + 1)) :=
        readPairs_getElem stS.mem scratch pairs.length i (by rw [readPairs_length]; exact hi')
      have hsel_i : selNodes.getD i 0 = (pairs'[i]'(by rw [readPairs_length]; exact hi')).2 := by
        rw [← hsel_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by rw [readPairs_length]; exact hi'), Option.map_some, Option.getD_some]
      rw [hsel_i, hget],
    fun a ha => (houtS a (Or.inr (by omega))).trans (hz1 a ha),
    fun a ha hnf => (houtS a (Or.inl ha)).trans (hfr1 a ha hnf), ?_⟩
  have hcS_le : cS ≤ 1000 * ((len + 1) * ordStoreLog S.eCap) := by
    unfold ORD_SORT_COST_MUL at hcS
    have h1 : pairs.length * (Nat.log 2 (pairs.length + 2) + 1) ≤ len * (2 * ordStoreLog S.eCap) :=
      Nat.mul_le_mul (by omega) hlog_out
    have h2 : len * (2 * ordStoreLog S.eCap) = 2 * (len * ordStoreLog S.eCap) := by ring
    have h3 : (len + 1) * ordStoreLog S.eCap = len * ordStoreLog S.eCap + ordStoreLog S.eCap := by ring
    nlinarith
  have h1_le : (cand.length + 1) * ordStoreLog S.eCap ≤ (len + 1) * ordStoreLog S.eCap :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *
  nlinarith

end MinCostFlow.SparseCore.Program
