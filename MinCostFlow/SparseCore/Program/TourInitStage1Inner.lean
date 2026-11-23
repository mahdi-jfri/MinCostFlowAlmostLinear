module

public import MinCostFlow.SparseCore.Program.TourInitStage1Prep
import Mathlib.Tactic

/-!
# Stage 1 Inner Loop (`tourInitInner_runs`)

Verifies `tourInitInnerLoop`, allocating nodes and joining them into a single splay tree for one
nonempty vertex record during Stage 1 initialization.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

theorem tourInitInner_runs {w vCap eCap b v keysPtr hOut nn0 : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool)
    {xs : List End} {st0 : State}
    {s0 : SplayState TourVal TourSum Unit} {trees0 : List AuxTree}
    {nodeOf0 keyOf0 : ℕ → ℕ}
    (hvLt : v < vCap) (hxs_ne : xs ≠ []) (hxs_nd : xs.Nodup)
    (hxs_lt : ∀ z ∈ xs, z.1 < eCap)
    (hxs_fresh : ∀ z ∈ xs, nodeOf0 (endKey z) = 0)
    (hxs_mem : ∀ j (hj : j < xs.length), st0.mem (keysPtr + j) = endKey (xs[j]'hj))
    (hkeys_lt : keysPtr + xs.length ≤ b)
    (hnn_end : nn0 + xs.length ≤ 2 * eCap)
    (hno0 : ∀ k < 2 * eCap, st0.mem (nodeOfEndBase b vCap + k) = nodeOf0 k ∧ nodeOf0 k ≤ nn0)
    (hko0 : ∀ u, 1 ≤ u → u ≤ nn0 → st0.mem (keyOfNodeBase b vCap eCap + u) = keyOf0 u ∧ keyOf0 u < 2 * eCap ∧ nodeOf0 (keyOf0 u) = u)
    (hno_ko0 : ∀ k < 2 * eCap, nodeOf0 k ≠ 0 → keyOf0 (nodeOf0 k) = k)
    (hn0 : tourLayout.NodesAt st0.mem (nodesBase b vCap eCap) nn0 s0)
    (hinv0 : TourForestInv nn0 s0 trees0)
    (hvals0 : TourValsOk w nn0 s0)
    (hord_le : ordHandleOf b vCap eCap ≤ hOut) (hroom : hOut + 2 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) (hzero0 : ZeroFrom st0.mem hOut)
    (hr5 : st0.regs 5 = firstEndBase b) (hr7 : st0.regs 7 = nodeOfEndBase b vCap)
    (hr8 : st0.regs 8 = endOwnerBase b vCap eCap) (hr9 : st0.regs 9 = keyOfNodeBase b vCap eCap)
    (hr10 : st0.regs 10 = nodesBase b vCap eCap) (hr12 : st0.regs 12 = 2 * eCap + 2)
    (hr13 : st0.regs 13 = hOut) (hr15 : st0.regs 15 = keysPtr)
    (hr16 : st0.regs 16 = nn0) (hr18 : st0.regs 18 = v) (hr19 : st0.regs 19 = xs.length)
    (hr20 : st0.regs 20 = 0) (hr21 : st0.regs 21 = 0) :
    ∃ (tV : AuxTree) (s1 : SplayState TourVal TourSum Unit) (nodeOf1 keyOf1 : ℕ → ℕ)
      (st1 : State) (c1 : ℕ),
      Runs w p ω (tourInitInnerLoop C.initNode C.join) st0 .normal st1 c1 ∧
      (∀ k < 20, k ≠ 16 → st1.regs k = st0.regs k) ∧
      st1.regs 16 = nn0 + xs.length ∧
      tourLayout.NodesAt st1.mem (nodesBase b vCap eCap) (nn0 + xs.length) s1 ∧
      TourForestInv (nn0 + xs.length) s1 (tV :: trees0) ∧
      TourValsOk w (nn0 + xs.length) s1 ∧
      ZeroFrom st1.mem hOut ∧
      (∀ u, u ∈ tV.toList ↔ nn0 < u ∧ u ≤ nn0 + xs.length) ∧
      tV.toList.map (fun u => endOfKey (keyOf1 u)) = xs ∧
      (∀ k, (∀ z ∈ xs, k ≠ endKey z) → nodeOf1 k = nodeOf0 k) ∧
      (∀ z ∈ xs, nodeOf1 (endKey z) = nn0 + 1 + xs.idxOf z) ∧
      (∀ u, 1 ≤ u → u ≤ nn0 → keyOf1 u = keyOf0 u) ∧
      (∀ k < 2 * eCap, st1.mem (nodeOfEndBase b vCap + k) = nodeOf1 k ∧ nodeOf1 k ≤ nn0 + xs.length) ∧
      (∀ u, 1 ≤ u → u ≤ nn0 + xs.length →
        st1.mem (keyOfNodeBase b vCap eCap + u) = keyOf1 u ∧ keyOf1 u < 2 * eCap ∧ nodeOf1 (keyOf1 u) = u) ∧
      (∀ k < 2 * eCap, nodeOf1 k ≠ 0 → keyOf1 (nodeOf1 k) = k) ∧
      st1.mem (firstEndBase b + v) = nn0 + 1 ∧
      (∀ z ∈ xs, st1.mem (endOwnerBase b vCap eCap + endKey z) = v + 1) ∧
      (∀ u ≤ nn0, (s1.nodes u).val = (s0.nodes u).val) ∧
      (∀ u, nn0 < u → u ≤ nn0 + xs.length →
        (s1.nodes u).val = ⟨true, false, if u = nn0 + 1 then v + 1 else 0⟩) ∧
      (∀ a < hOut, a ≠ firstEndBase b + v →
        (∀ z ∈ xs, a ≠ nodeOfEndBase b vCap + endKey z) →
        (∀ z ∈ xs, a ≠ endOwnerBase b vCap eCap + endKey z) →
        (∀ u, nn0 < u → u ≤ nn0 + xs.length → a ≠ keyOfNodeBase b vCap eCap + u) →
        ¬tourLayout.InRecords (nodesBase b vCap eCap) (nn0 + xs.length) a →
        st1.mem a = st0.mem a) ∧
      c1 + TOUR_PHI_MULT * forestPhi (tV :: trees0) ≤
        TOUR_PHI_MULT * forestPhi trees0 + xs.length * (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) + 20 := by
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hloop : ∀ (rem j : ℕ) (tCur? : Option AuxTree)
      (sC : SplayState TourVal TourSum Unit) (noC koC : ℕ → ℕ) (stC : State),
      (hj_sum : j + rem = xs.length) →
      (j = 0 → tCur? = none) →
      (0 < j → ∃ tC, tCur? = some tC ∧ (∀ u, u ∈ tC.toList ↔ nn0 < u ∧ u ≤ nn0 + j) ∧
        tC.toList.map (fun u => endOfKey (koC u)) = xs.take j) →
      (∀ k < 20, k ≠ 16 → stC.regs k = st0.regs k) →
      stC.regs 16 = nn0 + j → stC.regs 20 = optRoot tCur? → stC.regs 21 = j →
      tourLayout.NodesAt stC.mem (nodesBase b vCap eCap) (nn0 + j) sC →
      TourForestInv (nn0 + j) sC (optTrees tCur? ++ trees0) →
      TourValsOk w (nn0 + j) sC →
      ZeroFrom stC.mem hOut →
      (∀ k, (∀ z ∈ xs.take j, k ≠ endKey z) → noC k = nodeOf0 k) →
      (∀ i (hi : i < j), noC (endKey (xs[i]'(by omega))) = nn0 + 1 + i) →
      (∀ u, 1 ≤ u → u ≤ nn0 → koC u = keyOf0 u) →
      (∀ k < 2 * eCap, stC.mem (nodeOfEndBase b vCap + k) = noC k ∧ noC k ≤ nn0 + j) →
      (∀ u, 1 ≤ u → u ≤ nn0 + j →
        stC.mem (keyOfNodeBase b vCap eCap + u) = koC u ∧ koC u < 2 * eCap ∧ noC (koC u) = u) →
      (∀ k < 2 * eCap, noC k ≠ 0 → koC (noC k) = k) →
      (0 < j → stC.mem (firstEndBase b + v) = nn0 + 1) →
      (∀ i (hi : i < j), stC.mem (endOwnerBase b vCap eCap + endKey (xs[i]'(by omega))) = v + 1) →
      (∀ u ≤ nn0, (sC.nodes u).val = (s0.nodes u).val) →
      (∀ u, nn0 < u → u ≤ nn0 + j →
        (sC.nodes u).val = ⟨true, false, if u = nn0 + 1 then v + 1 else 0⟩) →
      (∀ a < hOut, a ≠ firstEndBase b + v →
        (∀ z ∈ xs, a ≠ nodeOfEndBase b vCap + endKey z) →
        (∀ z ∈ xs, a ≠ endOwnerBase b vCap eCap + endKey z) →
        (∀ u, nn0 < u → u ≤ nn0 + xs.length → a ≠ keyOfNodeBase b vCap eCap + u) →
        ¬tourLayout.InRecords (nodesBase b vCap eCap) (nn0 + xs.length) a →
        stC.mem a = st0.mem a) →
      ∃ (tV : AuxTree) (s1 : SplayState TourVal TourSum Unit) (no1 ko1 : ℕ → ℕ)
        (st1 : State) (c : ℕ),
        Runs w p ω (tourInitInnerLoop C.initNode C.join) stC .normal st1 c ∧
        (∀ k < 20, k ≠ 16 → st1.regs k = st0.regs k) ∧
        st1.regs 16 = nn0 + xs.length ∧
        tourLayout.NodesAt st1.mem (nodesBase b vCap eCap) (nn0 + xs.length) s1 ∧
        TourForestInv (nn0 + xs.length) s1 (tV :: trees0) ∧
        TourValsOk w (nn0 + xs.length) s1 ∧
        ZeroFrom st1.mem hOut ∧
        (∀ u, u ∈ tV.toList ↔ nn0 < u ∧ u ≤ nn0 + xs.length) ∧
        tV.toList.map (fun u => endOfKey (ko1 u)) = xs ∧
        (∀ k, (∀ z ∈ xs, k ≠ endKey z) → no1 k = nodeOf0 k) ∧
        (∀ z ∈ xs, no1 (endKey z) = nn0 + 1 + xs.idxOf z) ∧
        (∀ u, 1 ≤ u → u ≤ nn0 → ko1 u = keyOf0 u) ∧
        (∀ k < 2 * eCap, st1.mem (nodeOfEndBase b vCap + k) = no1 k ∧ no1 k ≤ nn0 + xs.length) ∧
        (∀ u, 1 ≤ u → u ≤ nn0 + xs.length →
          st1.mem (keyOfNodeBase b vCap eCap + u) = ko1 u ∧ ko1 u < 2 * eCap ∧ no1 (ko1 u) = u) ∧
        (∀ k < 2 * eCap, no1 k ≠ 0 → ko1 (no1 k) = k) ∧
        st1.mem (firstEndBase b + v) = nn0 + 1 ∧
        (∀ z ∈ xs, st1.mem (endOwnerBase b vCap eCap + endKey z) = v + 1) ∧
        (∀ u ≤ nn0, (s1.nodes u).val = (s0.nodes u).val) ∧
        (∀ u, nn0 < u → u ≤ nn0 + xs.length →
          (s1.nodes u).val = ⟨true, false, if u = nn0 + 1 then v + 1 else 0⟩) ∧
        (∀ a < hOut, a ≠ firstEndBase b + v →
          (∀ z ∈ xs, a ≠ nodeOfEndBase b vCap + endKey z) →
          (∀ z ∈ xs, a ≠ endOwnerBase b vCap eCap + endKey z) →
          (∀ u, nn0 < u → u ≤ nn0 + xs.length → a ≠ keyOfNodeBase b vCap eCap + u) →
          ¬tourLayout.InRecords (nodesBase b vCap eCap) (nn0 + xs.length) a →
          st1.mem a = st0.mem a) ∧
        c + TOUR_PHI_MULT * forestPhi (tV :: trees0) ≤
          TOUR_PHI_MULT * forestPhi (optTrees tCur? ++ trees0) +
            rem * (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) + 20 := by
    intro rem
    induction rem with
    | zero =>
      intro j tCur? sC noC koC stC hj _ htPos hreg hr16 hr20C hr21C hnC hinvC hvalsC hzC
        hno_fr hno_i hko_old hnoC hkoC hnkC hfeC heoC hval_old hval_new hfrC
      have hj_eq : j = xs.length := by omega
      subst hj_eq
      have hpos : 0 < xs.length := List.length_pos_of_ne_nil hxs_ne
      obtain ⟨tC, rfl, htC_mem, htC_map⟩ := htPos hpos
      have hcond : (Expr.bin .lt (.reg 21) (.reg 19)).eval w stC = some 0 := by
        simp [Expr.eval, hr21C, hreg 19 (by omega) (by omega), hr19, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨tC, sC, noC, koC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hreg, hr16, hnC, by simpa [optTrees] using hinvC, hvalsC, hzC, htC_mem,
        by simpa [List.take_length] using htC_map,
        fun k hk => hno_fr k (by simpa [List.take_length] using hk),
        fun z hz => by
          have hi : xs.idxOf z < xs.length := List.idxOf_lt_length_iff.mpr hz
          simpa [List.getElem_idxOf hi] using hno_i (xs.idxOf z) hi,
        hko_old, hnoC, hkoC, hnkC, hfeC hpos,
        fun z hz => by
          have hi : xs.idxOf z < xs.length := List.idxOf_lt_length_iff.mpr hz
          simpa [List.getElem_idxOf hi] using heoC (xs.idxOf z) hi,
        hval_old, hval_new, hfrC, by simp [optTrees, Expr.size]; omega⟩
    | succ rem ih =>
      intro j tCur? sC noC koC stC hj htZero htPos hreg hr16 hr20C hr21C hnC hinvC hvalsC hzC
        hno_fr hno_i hko_old hnoC hkoC hnkC hfeC heoC hval_old hval_new hfrC
      have hj_lt : j < xs.length := by omega
      set z := xs[j]'hj_lt
      set k := endKey z
      set u := nn0 + j + 1
      have hz_mem : z ∈ xs := List.getElem_mem hj_lt
      have hk_lt : k < 2 * eCap := endKey_lt_two_mul (hxs_lt z hz_mem)
      have hcond : (Expr.bin .lt (.reg 21) (.reg 19)).eval w stC = some 1 := by
        simp [Expr.eval, hr21C, hreg 19 (by omega) (by omega), hr19, hj_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hmem_k : stC.mem (keysPtr + j) = k := by
        have hlt_b : keysPtr + j < b := by omega
        rw [hfrC (keysPtr + j) (by simp [ordHandleOf, tourFixedSize] at hord_le; omega)
          (by simp [firstEndBase]; omega) (fun z' _ => by simp [nodeOfEndBase]; omega)
          (fun z' _ => by simp [endOwnerBase]; omega) (fun u' _ _ => by simp [keyOfNodeBase]; omega)
          (not_inRecords_of_lt_nodesBase (by simp [nodesBase]; omega))]
        exact hxs_mem j hj_lt
      have hk_not_prev : ∀ z' ∈ xs.take j, k ≠ endKey z' := by
        intro z' hz' heq
        have hzeq : z = z' := by simpa [k, endOfKey_endKey] using congrArg endOfKey heq
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz'
        simp only [List.length_take, lt_min_iff] at hi
        rw [List.getElem_take] at hzeq
        have := (List.Nodup.getElem_inj_iff hxs_nd).mp hzeq; omega
      have hnoC_k0 : noC k = 0 := (hno_fr k hk_not_prev).trans (hxs_fresh z hz_mem)
      -- Execute preamble: load k, u := u + 1, store nodeOfEnd[k], keyOfNode[u], endOwner[k], r24 := 1, r25 := 0
      set r1 := Function.update stC.regs 22 k
      set r2 := Function.update r1 16 u
      set m1 := Function.update stC.mem (nodeOfEndBase b vCap + k) u
      set m2 := Function.update m1 (keyOfNodeBase b vCap eCap + u) k
      set m3 := Function.update m2 (endOwnerBase b vCap eCap + k) (v + 1)
      set r3 := Function.update r2 24 1
      set r4 := Function.update r3 25 0
      have ha_k := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 22) (rBase := 15) (rIdx := 21)
        (base := keysPtr) (idx := j) (val := k) (st := stC) (by rw [hreg 15 (by omega) (by omega), hr15]) hr21C
        (by simp [ordHandleOf, tourFixedSize] at hord_le; omega) hmem_k
      have ha_u : Runs w p ω (.assign 16 (.bin .add (.reg 16) (.const 1))) ⟨stC.mem, r1, stC.pos⟩ .normal ⟨stC.mem, r2, stC.pos⟩ 4 :=
        runs_assign_iff.mpr ⟨u, by simp [Expr.eval, r1, hr16, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : nn0 + j + 1 < 2 ^ w), u], rfl, rfl, rfl⟩
      have hst_no : Runs w p ω (.store (.bin .add (.reg 7) (.reg 22)) (.reg 16)) ⟨stC.mem, r2, stC.pos⟩ .normal ⟨m1, r2, stC.pos⟩ 5 :=
        runs_store_iff.mpr ⟨nodeOfEndBase b vCap + k, u,
          by simp [Expr.eval, r2, r1, hreg 7 (by omega) (by omega), hr7, BinOp.eval,
            (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : nodeOfEndBase b vCap + k < 2 ^ w)],
          by simp [Expr.eval, r2], rfl, rfl, rfl⟩
      have hst_ko : Runs w p ω (.store (.bin .add (.reg 9) (.reg 16)) (.reg 22)) ⟨m1, r2, stC.pos⟩ .normal ⟨m2, r2, stC.pos⟩ 5 :=
        runs_store_iff.mpr ⟨keyOfNodeBase b vCap eCap + u, k,
          by simp [Expr.eval, r2, r1, hreg 9 (by omega) (by omega), hr9, BinOp.eval,
            (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : keyOfNodeBase b vCap eCap + u < 2 ^ w)],
          by simp [Expr.eval, r2, r1], rfl, rfl, rfl⟩
      have hst_eo : Runs w p ω (.store (.bin .add (.reg 8) (.reg 22)) (.bin .add (.reg 18) (.const 1))) ⟨m2, r2, stC.pos⟩ .normal ⟨m3, r2, stC.pos⟩ 7 :=
        runs_store_iff.mpr ⟨endOwnerBase b vCap eCap + k, v + 1,
          by simp [Expr.eval, r2, r1, hreg 8 (by omega) (by omega), hr8, BinOp.eval,
            (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : endOwnerBase b vCap eCap + k < 2 ^ w)],
          by simp [Expr.eval, r2, r1, hreg 18 (by omega) (by omega), hr18, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : v + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have ha24 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 24) (val := 1) (st := ⟨m3, r2, stC.pos⟩) (by omega)
      have ha25 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 25) (val := 0) (st := ⟨m3, r3, stC.pos⟩) (by omega)
      have hm3_ne : ∀ a, a ≠ nodeOfEndBase b vCap + k → a ≠ keyOfNodeBase b vCap eCap + u →
          a ≠ endOwnerBase b vCap eCap + k → m3 a = stC.mem a := fun a h1 h2 h3 => by
        simp only [m3, m2, m1]; rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
      have hn3 : tourLayout.NodesAt m3 (nodesBase b vCap eCap) (nn0 + j) sC :=
        NodesAt.congr tourLayout hnC fun a ha => by
          have hge := (inRecords_lt_ordHandle_of_le (by omega : nn0 + j ≤ 2 * eCap) ha).1
          exact hm3_ne a (by simp [nodeOfEndBase, nodesBase] at hge ⊢; omega)
            (by simp [keyOfNodeBase, nodesBase] at hge ⊢; omega)
            (by simp [endOwnerBase, nodesBase] at hge ⊢; omega)
      have hAu_lt : nodesBase b vCap eCap + 17 * u + 17 < 2 ^ w := by
        simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
      -- Branch on `j = 0` vs `j > 0`, producing `(tNext, sNext, stB, cB)`
      have hbranch : ∃ (tNext : AuxTree) (sNext : SplayState TourVal TourSum Unit) (stB : State) (cB : ℕ),
          Runs w p ω (.cond (.bin .eq (.reg 21) (.const 0))
            (.store (.bin .add (.reg 5) (.reg 18)) (.reg 16) ;;
             .assign 23 (.bin .add (.reg 18) (.const 1)) ;;
             .call 26 C.initNode [.reg 10, .reg 16, .reg 24, .reg 25, .reg 23] ;;
             .assign 20 (.reg 16))
            (.call 26 C.initNode [.reg 10, .reg 16, .reg 24, .reg 25, .reg 25] ;;
             .call 20 C.join [.reg 10, .reg 20, .reg 16, .reg 12, .reg 13]))
            ⟨m3, r4, stC.pos⟩ .normal stB cB ∧
          (∀ q < 20, q ≠ 16 → stB.regs q = st0.regs q) ∧
          stB.regs 16 = u ∧ stB.regs 20 = tNext.rootId ∧ stB.regs 21 = j ∧
          tourLayout.NodesAt stB.mem (nodesBase b vCap eCap) u sNext ∧
          TourForestInv u sNext (tNext :: trees0) ∧
          TourValsOk w u sNext ∧
          ZeroFrom stB.mem hOut ∧
          tNext.toList = optList tCur? ++ [u] ∧
          stB.mem (firstEndBase b + v) = nn0 + 1 ∧
          (∀ id ≤ nn0 + j, (sNext.nodes id).val = (sC.nodes id).val) ∧
          (sNext.nodes u).val = ⟨true, false, if j = 0 then v + 1 else 0⟩ ∧
          (∀ a < hOut, a ≠ firstEndBase b + v →
            ¬tourLayout.InRecords (nodesBase b vCap eCap) u a → stB.mem a = m3 a) ∧
          cB + TOUR_PHI_MULT * forestPhi (tNext :: trees0) ≤
            TOUR_PHI_MULT * forestPhi (optTrees tCur? ++ trees0) +
              TOUR_JOIN_AMORT * (2 * tourLog eCap) + 700 := by
        by_cases hj0 : j = 0
        · subst hj0
          have htNone : tCur? = none := htZero rfl
          subst htNone
          have hc0 : (Expr.bin .eq (.reg 21) (.const 0)).eval w ⟨m3, r4, stC.pos⟩ = some 1 := by
            simp [Expr.eval, r4, r3, r2, r1, hr21C, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
          set m4 := Function.update m3 (firstEndBase b + v) u
          set r5 := Function.update r4 23 (v + 1)
          have hst_fe : Runs w p ω (.store (.bin .add (.reg 5) (.reg 18)) (.reg 16))
              ⟨m3, r4, stC.pos⟩ .normal ⟨m4, r4, stC.pos⟩ 5 :=
            runs_store_iff.mpr ⟨firstEndBase b + v, u,
              by simp [Expr.eval, r4, r3, r2, r1, hreg 5 (by omega) (by omega), hr5, hreg 18 (by omega) (by omega), hr18,
                BinOp.eval, (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : firstEndBase b + v < 2 ^ w)],
              by simp [Expr.eval, r4, r3, r2], rfl, rfl, rfl⟩
          have ha23 : Runs w p ω (.assign 23 (.bin .add (.reg 18) (.const 1)))
              ⟨m4, r4, stC.pos⟩ .normal ⟨m4, r5, stC.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨v + 1, by simp [Expr.eval, r4, r3, r2, r1, hreg 18 (by omega) (by omega), hr18, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : v + 1 < 2 ^ w)], rfl, rfl, rfl⟩
          obtain ⟨oI, stI, cI, hrunI, ⟨hnuI, hfrI⟩, hcI⟩ :=
            tourInitNodeBody_runs (w := w) (nb := nodesBase b vCap eCap) (x := u) (isOpen := 1)
              (isMarked := 0) (rootTag := v + 1) (pos := stC.pos) (p := p) ω (mem := m4) hAu_lt hwide
          have hcallI := runs_call_regs5 26 10 16 24 25 23 (st := ⟨m4, r5, stC.pos⟩) C.initNode_body
            (by simp [r5, r4, r3, r2, r1, hreg 10 (by omega) (by omega), hr10])
            (by simp [r5, r4, r3, r2]) (by simp [r5, r4, r3]) (by simp [r5, r4]) (by simp [r5]) hrunI
          set r6 := Function.update r5 26 oI.value
          set r7 := Function.update r6 20 u
          have ha20 : Runs w p ω (.assign 20 (.reg 16)) { stI with regs := r6 } .normal { stI with regs := r7 } 2 :=
            runs_assign_iff.mpr ⟨u, by simp [Expr.eval, r6, r5, r4, r3, r2], rfl, rfl, rfl⟩
          have hn4 : tourLayout.NodesAt m4 (nodesBase b vCap eCap) nn0 sC :=
            NodesAt.congr tourLayout hn3 fun a ha => by
              have hge := (inRecords_lt_ordHandle_of_le (by omega : nn0 ≤ 2 * eCap) ha).1
              dsimp only [m4]; exact Function.update_of_ne (by simp [firstEndBase, nodesBase] at hge ⊢; omega) _ _
          have hnuI' : tourLayout.NodeAt stI.mem (nodesBase b vCap eCap) u (tourSingletonNode u ⟨true, false, v + 1⟩) := by
            simpa [tourSingletonNode] using hnuI
          have ⟨hnI, hinvI, hphiI⟩ := tourInitNode_fresh_succ_preserves (trees := trees0) hn4 (by simpa [optTrees] using hinvC) hnuI' hfrI
          refine ⟨AuxTree.node u .leaf .leaf, { nodes := Function.update sC.nodes u (tourSingletonNode u ⟨true, false, v + 1⟩) },
            { stI with regs := r7 }, _,
            tour_runs_cond_true hc0 (by omega) (tour_runs_seq_normal hst_fe (tour_runs_seq_normal ha23 (tour_runs_seq_normal hcallI ha20))),
            fun q hq hq16 => by
              simp [r7, r6, r5, r4, r3, r2, r1, Function.update_of_ne (by omega : q ≠ 20), Function.update_of_ne (by omega : q ≠ 26),
                Function.update_of_ne (by omega : q ≠ 23), Function.update_of_ne (by omega : q ≠ 25),
                Function.update_of_ne (by omega : q ≠ 24), Function.update_of_ne hq16, Function.update_of_ne (by omega : q ≠ 22), hreg q hq hq16],
            by simp [r7, r6, r5, r4, r3, r2], by simp [r7, AuxTree.rootId],
            by simp [r7, r6, r5, r4, r3, r2, r1, hr21C],
            hnI, hinvI,
            ⟨by omega, fun id hid => by
              by_cases hiu : id = u
              · subst hiu; simp [tourSingletonNode]; omega
              · simp [Function.update_of_ne hiu]; exact hvalsC.2 id (by omega)⟩,
            fun a ha => by
              rw [hfrI a (fun i hi => by simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
              dsimp only [m4]; rw [Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
              rw [hm3_ne a (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
              exact hzC a ha,
            by simp [AuxTree.toList, optList],
            by rw [hfrI _ (fun i hi => by simp [firstEndBase, nodesBase]; omega)]; simp [m4, u],
            fun id hid => by simp [Function.update_of_ne (by omega : id ≠ u)],
            by simp [tourSingletonNode],
            fun a _ hfe hnr => by
              rw [hfrI a (fun i hi heq => hnr (by simp only [NodeLayout.InRecords, NodeLayout.nodeAddr, tourLayout_stride]; omega))]
              dsimp only [m4]; exact Function.update_of_ne hfe _ _,
            by simp only [optTrees, Option.toList_none, List.nil_append] at hphiI ⊢; rw [hphiI]; clear * - hcI htl; simp only [Expr.size, TOUR_SPLICE_COST, TOUR_JOIN_AMORT] at *; omega⟩
        · have hj_pos : 0 < j := by omega
          obtain ⟨tC, rfl, _, _⟩ := htPos hj_pos
          have hc0 : (Expr.bin .eq (.reg 21) (.const 0)).eval w ⟨m3, r4, stC.pos⟩ = some 0 := by
            simp [Expr.eval, r4, r3, r2, r1, hr21C, hj0, BinOp.eval, (by omega : 0 < 2 ^ w)]
          obtain ⟨oI, stI, cI, hrunI, ⟨hnuI, hfrI⟩, hcI⟩ :=
            tourInitNodeBody_runs (w := w) (nb := nodesBase b vCap eCap) (x := u) (isOpen := 1)
              (isMarked := 0) (rootTag := 0) (pos := stC.pos) (p := p) ω (mem := m3) hAu_lt hwide
          have hcallI := runs_call_regs5 26 10 16 24 25 25 (st := ⟨m3, r4, stC.pos⟩) C.initNode_body
            (by simp [r4, r3, r2, r1, hreg 10 (by omega) (by omega), hr10])
            (by simp [r4, r3, r2]) (by simp [r4, r3]) (by simp [r4]) (by simp [r4]) hrunI
          set r5 := Function.update r4 26 oI.value
          set sI : SplayState TourVal TourSum Unit :=
            { nodes := Function.update sC.nodes u (tourSingletonNode u ⟨true, false, 0⟩) }
          have hnuI' : tourLayout.NodeAt stI.mem (nodesBase b vCap eCap) u (tourSingletonNode u ⟨true, false, 0⟩) := by
            simpa [tourSingletonNode] using hnuI
          have ⟨hnI, hinvI, hphiI⟩ := tourInitNode_fresh_succ_preserves hn3 hinvC hnuI' hfrI
          have hperm_sw : (AuxTree.node u .leaf .leaf :: (optTrees (some tC) ++ trees0)).Perm
              (optTrees (some tC) ++ optTrees (some (AuxTree.node u .leaf .leaf)) ++ trees0) := by
            simpa [optTrees] using List.Perm.swap tC (AuxTree.node u .leaf .leaf) trees0
          have hvalsI : TourValsOk w u sI :=
            ⟨by omega, fun id hid => by
              by_cases hiu : id = u
              · subst hiu; simp [sI, tourSingletonNode]
              · simp [sI, Function.update_of_ne hiu]; exact hvalsC.2 id (by omega)⟩
          have hzI : ZeroFrom stI.mem hOut := fun a ha => by
            rw [hfrI a (fun i hi => by simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
            rw [hm3_ne a (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
            exact hzC a ha
          have hheapI : HeapOk tourLayout w (nodesBase b vCap eCap) u hOut 2 stI.mem :=
            ⟨by simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega,
             hroom, hzI, by omega⟩
          obtain ⟨tJ?, sJ, oJ, stJ, cJ, hrunJ, hoJ, hnJ, hfrJ, hinvJ, hvalsJ, hlistJ, hvalJ, _, hcostJ⟩ :=
            tourJoinBody_runs (fuel := 2 * eCap + 2) (pos := stI.pos) C ω hnI (hinvI.perm hperm_sw).1 hvalsI
              (by omega) (by omega) hheapI
          cases tJ? with
          | none => simp [optList, AuxTree.toList] at hlistJ
          | some tJ =>
            have hcallJ := runs_call_regs5 20 10 20 16 12 13 (st := { stI with regs := r5 }) C.join_body
              (by simp [r5, r4, r3, r2, r1, hreg 10 (by omega) (by omega), hr10])
              (by simp [r5, r4, r3, r2, r1, hr20C]) (by simp [r5, r4, r3, r2, optRoot, AuxTree.rootId])
              (by simp [r5, r4, r3, r2, r1, hreg 12 (by omega) (by omega), hr12])
              (by simp [r5, r4, r3, r2, r1, hreg 13 (by omega) (by omega), hr13]) hrunJ
            set r6 := Function.update r5 20 oJ.value
            have hlog_u : Nat.log 2 (u + 2) + 1 ≤ 2 * tourLog eCap := tourLog_of_le (by omega)
            have hmul_j : TOUR_JOIN_AMORT * (Nat.log 2 (u + 2) + 1) ≤ TOUR_JOIN_AMORT * (2 * tourLog eCap) :=
              Nat.mul_le_mul_left _ hlog_u
            refine ⟨tJ, sJ, { stJ with regs := r6 }, _,
              tour_runs_cond_false hc0 (tour_runs_seq_normal hcallI hcallJ),
              fun q hq hq16 => by
                simp [r6, r5, r4, r3, r2, r1, Function.update_of_ne (by omega : q ≠ 20), Function.update_of_ne (by omega : q ≠ 26),
                  Function.update_of_ne (by omega : q ≠ 25), Function.update_of_ne (by omega : q ≠ 24),
                  Function.update_of_ne hq16, Function.update_of_ne (by omega : q ≠ 22), hreg q hq hq16],
              by simp [r6, r5, r4, r3, r2], by simpa [r6, optRoot] using hoJ,
              by simp [r6, r5, r4, r3, r2, r1, hr21C],
              hnJ, by simpa [optTrees] using hinvJ, hvalsJ, hfrJ.1,
              by simpa [optList, AuxTree.toList] using hlistJ,
              by
                rw [hfrJ.2 _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                  (not_inRecords_of_lt_nodesBase (by simp [firstEndBase, nodesBase]; omega)),
                  hfrI _ (fun i hi => by simp [firstEndBase, nodesBase]; omega),
                  hm3_ne _ (by simp [firstEndBase, nodeOfEndBase]; omega)
                    (by simp [firstEndBase, keyOfNodeBase]; omega) (by simp [firstEndBase, endOwnerBase]; omega)]
                exact hfeC hj_pos,
              fun id hid => by rw [hvalJ id (by omega)]; dsimp only; rw [Function.update_of_ne (by omega : id ≠ nn0 + j + 1)],
              by rw [hvalJ u (le_refl _)]; simp [tourSingletonNode, hj0, u],
              fun a ha _ hnr => by
                rw [hfrJ.2 a ha hnr, hfrI a (fun i hi heq => hnr (by simp only [NodeLayout.InRecords, NodeLayout.nodeAddr, tourLayout_stride]; omega))],
              by
                rw [forestPhi_perm hperm_sw] at hphiI
                simp only [optTrees, Option.toList_some, List.cons_append, List.nil_append] at hphiI hcostJ ⊢
                rw [hphiI] at hcostJ
                dsimp only [u] at hmul_j
                clear * - hcI hcostJ hmul_j; simp only [Expr.size, TOUR_SPLICE_COST] at *; omega⟩
      obtain ⟨tNext, sNext, stB, cB, hrunB, hrB_lt, hrB16, hrB20, hrB21, hnB, hinvB, hvalsB, hzB,
        htN_list, hfeB, hvalB_old, hvalB_u, hfrB, hcB⟩ := hbranch
      set rFin := Function.update stB.regs 21 (j + 1)
      have ha_inc : Runs w p ω (.assign 21 (.bin .add (.reg 21) (.const 1))) stB .normal { stB with regs := rFin } 4 :=
        runs_assign_iff.mpr ⟨j + 1, by simp [Expr.eval, hrB21, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : j + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hbody := tour_runs_seq_normal ha_k (tour_runs_seq_normal ha_u (tour_runs_seq_normal hst_no (tour_runs_seq_normal hst_ko
        (tour_runs_seq_normal hst_eo (tour_runs_seq_normal ha24 (tour_runs_seq_normal ha25 (tour_runs_seq_normal hrunB ha_inc)))))))
      set noNext := Function.update noC k u
      set koNext := Function.update koC u k
      have hfrB_pre : ∀ a < nodesBase b vCap eCap, a ≠ firstEndBase b + v → stB.mem a = m3 a := fun a ha hfe =>
        hfrB a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega) hfe (not_inRecords_of_lt_nodesBase ha)
      have htN_mem : ∀ id, id ∈ tNext.toList ↔ nn0 < id ∧ id ≤ u := fun id => by
        rw [htN_list, List.mem_append, List.mem_singleton]
        by_cases hj0 : j = 0
        · subst hj0; rw [htZero rfl]; simp [optList, u]; omega
        · obtain ⟨tC, rfl, htC_mem, _⟩ := htPos (by omega)
          simp only [optList, Option.elim, htC_mem]; omega
      have htN_map : tNext.toList.map (fun id => endOfKey (koNext id)) = xs.take (j + 1) := by
        rw [htN_list, List.map_append, List.map_singleton, List.take_succ_eq_append_getElem hj_lt]
        congr 1
        · by_cases hj0 : j = 0
          · subst hj0; rw [htZero rfl]; rfl
          · obtain ⟨tC, rfl, htC_mem, htC_map⟩ := htPos (by omega)
            rw [← htC_map]; refine List.map_congr_left fun id hid => ?_
            have := (htC_mem id).mp hid; simp [koNext, Function.update_of_ne (by omega : id ≠ u)]
        · simp [koNext, k, z, endOfKey_endKey]
      obtain ⟨tV, s1, no1, ko1, st1, cRest, hrunR, hr1_lt, hr1_16, hn1, hinv1, hvals1, hz1,
        htV_mem, htV_map, hno1_fr, hno1_z, hko1_old, hno1_mem, hko1_mem, hnk1, hfe1, heo1,
        hval1_old, hval1_new, hfr1, hcRest⟩ :=
        ih (j + 1) (some tNext) sNext noNext koNext { stB with regs := rFin } (by omega) (by omega)
          (fun _ => ⟨tNext, rfl, htN_mem, htN_map⟩)
          (fun q hq hq16 => by simp [rFin, Function.update_of_ne (by omega : q ≠ 21), hrB_lt q hq hq16])
          (by simp [rFin, hrB16, u]; omega) (by simp [rFin, hrB20, optRoot]) (by simp [rFin])
          (by simpa [u, Nat.add_assoc] using hnB) (by simpa [optTrees, u, Nat.add_assoc] using hinvB)
          (by simpa [u, Nat.add_assoc] using hvalsB) hzB
          (fun k' hk' => by
            have hk'ne : k' ≠ k := hk' z (by rw [List.take_succ_eq_append_getElem hj_lt]; exact List.mem_append_right _ (List.mem_singleton_self _))
            simp only [noNext, Function.update_of_ne hk'ne]
            exact hno_fr k' fun z' hz' => hk' z' (by rw [List.take_succ_eq_append_getElem hj_lt]; exact List.mem_append_left _ hz'))
          (fun i hi => by
            by_cases hij : i = j
            · subst hij; simp [noNext, k, z, u]; omega
            · have hi' : i < j := by omega
              have hne : endKey (xs[i]'(by omega)) ≠ k := fun heq =>
                hk_not_prev (xs[i]'(by omega)) (by rw [List.mem_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩) heq.symm
              simp only [noNext, Function.update_of_ne hne]; exact hno_i i hi')
          (fun id h1 h2 => by simp only [koNext, Function.update_of_ne (by omega : id ≠ u)]; exact hko_old id h1 h2)
          (fun k' hk' => by
            rw [hfrB_pre _ (by simp [nodeOfEndBase, nodesBase]; omega) (by simp [nodeOfEndBase, firstEndBase]; omega)]
            by_cases hkk : k' = k
            · subst hkk
              have hne1 : nodeOfEndBase b vCap + k ≠ endOwnerBase b vCap eCap + k := by
                simp [nodeOfEndBase, endOwnerBase]; omega
              have hne2 : nodeOfEndBase b vCap + k ≠ keyOfNodeBase b vCap eCap + u := by
                simp [nodeOfEndBase, keyOfNodeBase]; omega
              simp only [noNext, m3, m2, m1, Function.update_self, Function.update_of_ne hne1,
                Function.update_of_ne hne2]
              exact ⟨trivial, by omega⟩
            · rw [hm3_ne _ (by omega) (by simp [nodeOfEndBase, keyOfNodeBase]; omega) (by simp [nodeOfEndBase, endOwnerBase]; omega)]
              simp only [noNext, Function.update_of_ne hkk]
              have := hnoC k' hk'; exact ⟨this.1, by omega⟩)
          (fun id h1 h2 => by
            rw [hfrB_pre _ (by simp [keyOfNodeBase, nodesBase]; omega) (by simp [keyOfNodeBase, firstEndBase]; omega)]
            by_cases hiu : id = u
            · subst hiu
              have hne : keyOfNodeBase b vCap eCap + u ≠ endOwnerBase b vCap eCap + k := by
                simp [keyOfNodeBase, endOwnerBase]; omega
              exact ⟨by simp [koNext, m3, m2, hne], by simpa [koNext] using hk_lt, by simp [noNext, koNext]⟩
            · have hle : id ≤ nn0 + j := by omega
              have hkm := hkoC id h1 hle
              have hkne : koC id ≠ k := fun heq => by rw [heq, hnoC_k0] at hkm; omega
              rw [hm3_ne _ (by simp [keyOfNodeBase, nodeOfEndBase]; omega) (by omega) (by simp [keyOfNodeBase, endOwnerBase]; omega)]
              simp only [noNext, koNext, Function.update_of_ne hiu, Function.update_of_ne hkne]
              exact hkm)
          (fun k' hk' hnz => by
            by_cases hkk : k' = k
            · subst hkk; simp [noNext, koNext]
            · simp only [noNext, koNext, Function.update_of_ne hkk] at hnz ⊢
              have hle := (hnoC k' hk').2
              rw [Function.update_of_ne (by omega)]; exact hnkC k' hk' hnz)
          (fun _ => hfeB)
          (fun i hi => by
            have hki_lt : endKey (xs[i]'(by omega)) < 2 * eCap :=
              endKey_lt_two_mul (hxs_lt _ (List.getElem_mem (by omega)))
            rw [hfrB_pre _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, firstEndBase]; omega)]
            by_cases hij : i = j
            · subst hij; simp [m3, k, z]
            · have hi' : i < j := by omega
              have hne : endKey (xs[i]'(by omega)) ≠ k := fun heq =>
                hk_not_prev (xs[i]'(by omega)) (by rw [List.mem_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩) heq.symm
              rw [hm3_ne _ (by simp [endOwnerBase, nodeOfEndBase]; omega) (by simp [endOwnerBase, keyOfNodeBase]; omega) (by omega)]
              exact heoC i hi')
          (fun id hid => (hvalB_old id (by omega)).trans (hval_old id hid))
          (fun id h1 h2 => by
            by_cases hiu : id = u
            · subst hiu; rw [hvalB_u]; by_cases hj0 : j = 0 <;> simp [hj0, u]
            · rw [hvalB_old id (by omega)]; exact hval_new id h1 (by omega))
          (fun a ha hfe hno_a heo_a hko_a hnr => by
            have hnr_u : ¬tourLayout.InRecords (nodesBase b vCap eCap) u a := fun hr => by
              apply hnr
              simp only [NodeLayout.InRecords, NodeLayout.nodeAddr, tourLayout_stride] at hr ⊢
              exact ⟨hr.1, by omega⟩
            rw [hfrB a ha hfe hnr_u, hm3_ne a (hno_a z hz_mem) (hko_a u (by omega) (by omega)) (heo_a z hz_mem)]
            exact hfrC a ha hfe hno_a heo_a hko_a hnr)
      refine ⟨tV, s1, no1, ko1, st1, _,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrunR, rfl⟩)),
        hr1_lt, hr1_16, hn1, hinv1, hvals1, hz1, htV_mem, htV_map, hno1_fr, hno1_z, hko1_old,
        hno1_mem, hko1_mem, hnk1, hfe1, heo1, hval1_old, hval1_new, hfr1, ?_⟩
      simp only [optTrees, Option.toList_some, List.singleton_append] at hcRest
      have hmul : (rem + 1) * (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) =
          rem * (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) + (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) := by ring
      have hstep : TOUR_JOIN_AMORT * (2 * tourLog eCap) + 750 ≤ (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) := by
        clear * - htl; simp only [TOUR_JOIN_AMORT]; omega
      clear * - hcB hcRest hmul hstep; simp only [Expr.size] at *; omega
  exact hloop xs.length 0 none s0 nodeOf0 keyOf0 st0 (by omega) (fun _ => rfl) (fun h => by omega)
    (fun _ _ _ => rfl) hr16 (by simp [optRoot, hr20]) hr21 hn0 (by simpa [optTrees] using hinv0) hvals0 hzero0
    (fun _ _ => rfl) (fun _ h => by omega) (fun _ _ _ => rfl) hno0 hko0 hno_ko0 (fun h => by omega)
    (fun _ h => by omega) (fun _ _ => rfl) (fun _ h1 h2 => by omega) (fun _ _ _ _ _ _ _ => rfl)


end MinCostFlow.SparseCore.Program
