module

public import MinCostFlow.HierPaths.BuildRouterBridgeIn
public import MinCostFlow.HierPaths.BuildRouterBridgeOutB
public import MinCostFlow.ExpanderDecomp.RouteProgWrap
import Mathlib.Tactic.Linarith

/-!
# Static Router Bridge (`BuildRouterBridge`)

Bridges `routeOrCutPairsProc` (`MinCostFlow.ExpanderDecomp.RouteProgWrap`, entry `base + 12` of
`routerProcs base`, satisfying `routeOrCutPairsWithWalksContract`) into the walk-producing static
router interface `ProvidesRouter` (`BuildProgContracts.lean`).

Main exports:
* `routerBridgeProc` / `routerBridgeProcs`: relocatable 16-procedure deterministic module
  (`[routerBridgeProc ...] ++ routerProcs (base + 1) ++ [buildCopyProc]`, entry at `base + 0`).
* `routerBridgeProcs_noRand`: determinism (`Stmt.NoRand`) of every procedure in the module.
* `routerBridgeProcs_providesRouter`: `ProvidesRouter w routerBridgeK routeOrCut routeOrCutCost
  routerBridgeSpace p base` for every placement `p.HasAt base (routerBridgeProcs base)` and word
  size `w`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Cut output packing branch: reads `U.card` from `outAddr + 1`, writes the 5-word header
`[0, 1, 1 + U.card, 1 + U.card, 1]` at `h .. h + 4`, copies `finsetWords U` from `outAddr + 2`
down to `h + 5`, and returns `vInner`. -/
def bridgePackCutStmt (fCopy : ℕ) : Stmt :=
  .assign 16 (.load (.bin .add (.reg 12) (.const 1))) ;;
  .assign 17 (.bin .add (.const 1) (.reg 16)) ;;
  .store (.reg 9) (.const 0) ;;
  .store (.bin .add (.reg 9) (.const 1)) (.const 1) ;;
  .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
  .store (.bin .add (.reg 9) (.const 3)) (.reg 17) ;;
  .store (.bin .add (.reg 9) (.const 4)) (.const 1) ;;
  .call 18 fCopy [.bin .add (.reg 12) (.const 2), .reg 16, .bin .add (.reg 9) (.const 5)] ;;
  .ret (.reg 14)

theorem bridgePackCutStmt_noRand (fCopy : ℕ) : (bridgePackCutStmt fCopy).NoRand := by
  simp [bridgePackCutStmt, Stmt.NoRand]

/-- Top-level static router bridge procedure matching `RouterProcContract`.
Calls `bridgePrepInputsStmt`, delegates to `routeOrCutPairsProc` at `fPairs`, and packs either
the cut or matched+walks output into `routeResultWords` at `h`. -/
def routerBridgeProc (fPairs fCopy : ℕ) : Stmt :=
  bridgePrepInputsStmt fCopy ;;
  (.call 14 fPairs [.reg 0, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6, .reg 12, .reg 13] ;;
   .cond (.load (.reg 12)) (bridgePackCutStmt fCopy) (bridgePackMatchedStmt fCopy))

theorem routerBridgeProc_noRand (fPairs fCopy : ℕ) :
    (routerBridgeProc fPairs fCopy).NoRand := by
  simp [routerBridgeProc, bridgePrepInputsStmt_noRand, bridgePackCutStmt_noRand,
    bridgePackMatchedStmt_noRand, Stmt.NoRand]

/-- Relocatable 16-procedure deterministic module implementing `ProvidesRouter` at offset `0`:
* `base + 0`: `routerBridgeProc (base + 1 + routerPairsEntryOff) (base + 15)`
* `base + 1 .. base + 14`: `routerProcs (base + 1)` (14 procedures, `routeOrCutPairsProc` at `base + 13`)
* `base + 15`: `buildCopyProc` -/
def routerBridgeProcs (base : ℕ) : List Stmt :=
  [routerBridgeProc (base + 1 + routerPairsEntryOff) (base + 15)] ++
    routerProcs (base + 1) ++ [buildCopyProc]

theorem routerBridgeProcs_noRand (base : ℕ) :
    ∀ s ∈ routerBridgeProcs base, s.NoRand := by
  intro s hs
  simp only [routerBridgeProcs, List.mem_append, List.mem_singleton] at hs
  rcases hs with (rfl | hmem) | rfl
  · exact routerBridgeProc_noRand _ _
  · exact routerProcs_noRand (base + 1) s hmem
  · unfold buildCopyProc forRange
    simp [Stmt.NoRand]
    repeat (first | constructor | trivial)

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Verification of `bridgePackCutStmt`: writes `routeResultWords (.cut U)` at `h`, preserves
memory `< h` and `ZeroFrom vInner`, and returns `vInner`. -/
private theorem bridgePackCut_runs {w fCopy h outAddr vInner : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {U : Finset ℕ}
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hr9 : st.regs 9 = h) (hr12 : st.regs 12 = outAddr) (hr14 : st.regs 14 = vInner)
    (hOut : RouteOutSortedAt st.mem outAddr (.cut U))
    (hh5 : h + 5 ≤ outAddr)
    (hUv : outAddr + 2 + U.card ≤ vInner)
    (hvW : vInner < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hZ : ZeroFrom st.mem vInner) :
    ∃ st' c,
      Runs w p ω (bridgePackCutStmt fCopy) st (.returned vInner) st' c ∧
      ListAt st'.mem h (routeResultWords (.cut U)) ∧
      h + (routeResultWords (.cut U)).length ≤ vInner ∧
      ZeroFrom st'.mem vInner ∧
      (∀ a < h, st'.mem a = st.mem a) ∧
      c ≤ 17 * U.card + 80 := by
  have hCopyDown := buildCopyProc_meetsDownContract (w := w) hCopy
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have h1U : 1 + U.card < 2 ^ w := by omega
  have hCutLen : (finsetWords U).length = U.card := Finset.length_sort _
  suffices hS : ∃ o st' c,
      Runs w p ω (bridgePackCutStmt fCopy) st o st' c ∧
      (o = .returned vInner ∧
       ListAt st'.mem h (routeResultWords (.cut U)) ∧
       h + (routeResultWords (.cut U)).length ≤ vInner ∧
       ZeroFrom st'.mem vInner ∧
       (∀ a < h, st'.mem a = st.mem a)) ∧
      0 + c ≤ 17 * U.card + 80 by
    obtain ⟨_, st', c, hr, ⟨rfl, h1, h2, h3, h4⟩, hc⟩ := hS
    exact ⟨st', c, hr, h1, h2, h3, h4, by omega⟩
  unfold bridgePackCutStmt
  refine runs_seq_assign_le (v := U.card)
    (by simp [Expr.eval, BinOp.eval, hr12, hw1, show outAddr + 1 < 2 ^ w by omega, hOut.2.1]) ?_
  refine runs_seq_assign_le (v := 1 + U.card)
    (by simp [Expr.eval, BinOp.eval, hw1, h1U]) ?_
  refine runs_seq_store_le (x := h) (v := 0) (by simp [Expr.eval, hr9]) (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := h + 1) (v := 1)
    (by simp [Expr.eval, BinOp.eval, hr9, hw1, show h + 1 < 2 ^ w by omega])
    (by simp [Expr.eval, hw1]) ?_
  refine runs_seq_store_le (x := h + 2) (v := 1 + U.card)
    (by simp [Expr.eval, BinOp.eval, hr9, hw2, show h + 2 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := h + 3) (v := 1 + U.card)
    (by simp [Expr.eval, BinOp.eval, hr9, hw3, show h + 3 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := h + 4) (v := 1)
    (by simp [Expr.eval, BinOp.eval, hr9, hw4, show h + 4 < 2 ^ w by omega])
    (by simp [Expr.eval, hw1]) ?_
  refine runs_seq_call_le hCopyDown (vs := [outAddr + 2, U.card, h + 5])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr12, hr9, hw2, hw5,
      show outAddr + 2 < 2 ^ w by omega, show h + 5 < 2 ^ w by omega])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
    ⟨outAddr + 2, U.card, h + 5, rfl, by omega, by omega, hw1⟩ ?_
  intro _ mem' pos' hPost
  obtain ⟨_, _, _, hEq, hCop, hFr⟩ := hPost
  simp only [List.cons.injEq, and_true] at hEq
  obtain ⟨rfl, rfl, rfl⟩ := hEq
  dsimp only at hCop hFr
  refine runs_ret_le (v := vInner) (by simp [Expr.eval, hr14]) ?_ ?_
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [routeResultWords_cut_eq]
      refine listAt_append.mpr ⟨?_, ?_⟩
      · refine listAt_cons.mpr ⟨?_, listAt_cons.mpr ⟨?_, listAt_cons.mpr ⟨?_,
          listAt_cons.mpr ⟨?_, listAt_cons.mpr ⟨?_, by simp [ListAt]⟩⟩⟩⟩⟩
        · dsimp only
          rw [hFr h (Or.inl (by omega)), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        · dsimp only
          rw [hFr (h + 1) (Or.inl (by omega)), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        · dsimp only
          rw [show h + 1 + 1 = h + 2 by omega, hFr (h + 2) (Or.inl (by omega)),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        · dsimp only
          rw [show h + 1 + 1 + 1 = h + 3 by omega, hFr (h + 3) (Or.inl (by omega)),
            Function.update_of_ne (by omega), Function.update_self]
        · dsimp only
          rw [show h + 1 + 1 + 1 + 1 = h + 4 by omega, hFr (h + 4) (Or.inl (by omega)),
            Function.update_self]
      · simp only [List.length_cons, List.length_nil]
        intro j hj
        rw [hCutLen] at hj
        rw [hCop j hj, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hOut.2.2 j (by rw [Finset.length_sort]; exact hj)
    · rw [routeResultWords_cut_eq, List.length_append, hCutLen]
      simp only [List.length_cons, List.length_nil]; omega
    · intro a ha
      dsimp only
      rw [hFr a (Or.inr (by omega)), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hZ a ha
    · intro a ha
      dsimp only
      rw [hFr a (Or.inl (by omega)), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · simp only [buildCopyDownContract, buildCopyContract, List.getD_cons_zero, List.getD_cons_succ,
      argsSize, Expr.size]
    omega

private lemma readLenPrefixedList_of_vertSetAt_br {mem : ℕ → ℕ} {a : ℕ} {S : Finset ℕ}
    (h : VertSetAt mem a S) :
    (readLenPrefixedList mem a).toFinset = S ∧ mem a = S.card := by
  rcases h with ⟨xs, hnd, hfin, hseq⟩
  have hread : readLenPrefixedList mem a = xs := by
    unfold readLenPrefixedList
    rw [hseq.1, readList_eq_of_listAt hseq.2]
  exact ⟨hread ▸ hfin, by rw [hseq.1, ← hfin, List.toFinset_card_of_nodup hnd]⟩

private lemma readPairs_of_pairsAt_br {mem : ℕ → ℕ} {pAddr : ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} (hp : PairsAt mem pAddr pairs) :
    (List.ofFn fun i : Fin (mem pAddr) =>
      ((readLenPrefixedList mem (mem (pAddr + 1 + 2 * i.1))).toFinset,
       (readLenPrefixedList mem (mem (pAddr + 2 + 2 * i.1))).toFinset)) = pairs := by
  apply List.ext_getElem (by simp [hp.1])
  intro i hi _
  have hi' : i < pairs.length := by simpa [hp.1] using hi
  simp only [List.getElem_ofFn]
  have hpi := hp.2 i hi'
  exact Prod.ext (readLenPrefixedList_of_vertSetAt_br hpi.1).1
    (readLenPrefixedList_of_vertSetAt_br hpi.2).1

private lemma pairsAt_congr {mem₁ mem₂ : ℕ → ℕ} {pTable outAddr : ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)}
    (hP : PairsAt mem₁ pTable pairs)
    (hB : PairsBounded mem₁ pTable pairs outAddr)
    (hEq : ∀ a < outAddr, mem₂ a = mem₁ a) :
    PairsAt mem₂ pTable pairs ∧ PairsBounded mem₂ pTable pairs outAddr := by
  have h1 : PairsAt mem₂ pTable pairs := by
    refine ⟨by rw [hEq pTable (by have := hB.1; omega)]; exact hP.1, fun i hi => ?_⟩
    have hpi := hP.2 i hi
    have hbi := hB.2 i hi
    have heA : mem₂ (pTable + 1 + 2 * i) = mem₁ (pTable + 1 + 2 * i) :=
      hEq _ (by have := hB.1; omega)
    have heB : mem₂ (pTable + 2 + 2 * i) = mem₁ (pTable + 2 + 2 * i) :=
      hEq _ (by have := hB.1; omega)
    rw [heA, heB]
    refine ⟨?_, ?_⟩
    · rcases hpi.1 with ⟨xs, hnd, hfin, hseq⟩
      have hlen : xs.length = (pairs[i]'hi).1.card := by
        rw [← hfin, List.toFinset_card_of_nodup hnd]
      exact ⟨xs, hnd, hfin, by rw [hEq _ (by omega)]; exact hseq.1, fun j hj => by
        rw [hEq _ (by omega)]; exact hseq.2 j hj⟩
    · rcases hpi.2 with ⟨xs, hnd, hfin, hseq⟩
      have hlen : xs.length = (pairs[i]'hi).2.card := by
        rw [← hfin, List.toFinset_card_of_nodup hnd]
      exact ⟨xs, hnd, hfin, by rw [hEq _ (by omega)]; exact hseq.1, fun j hj => by
        rw [hEq _ (by omega)]; exact hseq.2 j hj⟩
  have h2 : PairsBounded mem₂ pTable pairs outAddr := by
    refine ⟨hB.1, fun i hi => ?_⟩
    have hbi := hB.2 i hi
    rw [hEq _ (by have := hB.1; omega), hEq _ (by have := hB.1; omega)]
    exact hbi
  exact ⟨h1, h2⟩

/-- **`routerBridgeProcs` implements `ProvidesRouter` at offset `0`.** -/
theorem routerBridgeProcs_providesRouter {w base : ℕ} {p : Program}
    (hAt : p.HasAt base (routerBridgeProcs base)) :
    ProvidesRouter w routerBridgeK routeOrCut routeOrCutCost routerBridgeSpace p base := by
  have hProc : p.procs[base]? = some (routerBridgeProc (base + 1 + routerPairsEntryOff) (base + 15)) := by
    have h0 := hAt 0 (by simp [routerBridgeProcs])
    simpa [routerBridgeProcs] using h0
  have hRouterAt : p.HasAt (base + 1) (routerProcs (base + 1)) := by
    intro j hj
    have hlen : (routerProcs (base + 1)).length = 14 := rfl
    have h' := hAt (j + 1) (by simp [routerBridgeProcs, hlen]; omega)
    have hidx : base + 1 + j = base + (j + 1) := by omega
    rw [hidx, h']
    simp [routerBridgeProcs, List.getElem_append_left, hj]
  have hCopy : p.procs[base + 15]? = some buildCopyProc := by
    have hlen : (routerProcs (base + 1)).length = 14 := rfl
    have h' := hAt 15 (by simp [routerBridgeProcs, hlen])
    rw [h']
    simp [routerBridgeProcs, hlen]
  have hPairsMC := routeOrCutPairs_meetsContract (w := w) hRouterAt
  intro G X pairs
  refine meetsContract_of_runs hProc fun args mem pos ω hwords hPre => ?_
  rcases hPre with ⟨⟨gAddr, xAddr, pAddr, Δ, L, b, z, h, rfl,
    hG, hGValid, hX, hP, hg, hx, hp, hRPre, hb⟩, hZ, hRoomS⟩
  simp only [heapArg, List.getLastD_cons, List.getLastD_nil, List.getD_cons_zero,
    List.getD_cons_succ] at hRoomS hZ
  have hSpBnd := routerBridgeSpace_bounds (z := z) hRPre hb
  have hXlen : (finsetWords X).length = X.card := Finset.length_sort _
  have hGlen : G.encode.length = 2 + 2 * G.m := by
    simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]; omega
  have hw16 : 16 < 2 ^ w := by
    have : 16 < routerBridgeSpace G.n G.encode.length (pairsWords pairs).length (Δ + L + b + z) := by
      unfold routerBridgeSpace
      have h1 : 1 ≤ (G.n + G.encode.length + (pairsWords pairs).length + (Δ + L + b + z) + 2) ^ 11 :=
        Nat.one_le_pow 11 _ (by omega)
      omega
    omega
  -- Stage 1: prepare `VertSetAt` and `PairsAt` inputs
  obtain ⟨st1, c1, hrun1, hr1lo, hr1_10, hr1_11, hr1_12, hr1_13, hr1_15, hVert1, hPairs1,
    hPairsB1, hCurEndLe, hFr1, hZ1, hc1⟩ :=
    bridgePrepInputs_runs (w := w) (ω := ω) (pos := pos) hCopy hG hX hP hg hx hp hZ (by omega)
  set xBuf := h
  set pTable := h + 1 + X.card
  set curEnd := bridgePairCur pTable pairs.length pairs (2 * pairs.length)
  set outAddr := curEnd + 5
  set hInner := outAddr + 2 + 2 * G.n
  have hh_lt_out : h < outAddr := by dsimp only [outAddr, curEnd, bridgePairCur, pTable]; omega
  have hG1 : GraphAt st1.mem gAddr G := fun j hj => by
    rw [hFr1 _ (by omega)]; exact hG j hj
  have hZInner : ZeroFrom st1.mem hInner := fun a ha => hZ1 a (by omega)
  have hPairsBInner : PairsBounded st1.mem pTable pairs hInner :=
    ⟨by have := hPairsB1.1; omega, fun i hi => by have := hPairsB1.2 i hi; omega⟩
  have hEvalInner : evalArgs w st1
      [.reg 0, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6, .reg 12, .reg 13] =
      some [gAddr, xBuf, pTable, Δ, L, b, z, outAddr, hInner] := by
    have h0 : st1.regs 0 = gAddr := by rw [hr1lo 0 (by decide)]; rfl
    have h3 : st1.regs 3 = Δ := by rw [hr1lo 3 (by decide)]; rfl
    have h4 : st1.regs 4 = L := by rw [hr1lo 4 (by decide)]; rfl
    have h5 : st1.regs 5 = b := by rw [hr1lo 5 (by decide)]; rfl
    have h6 : st1.regs 6 = z := by rw [hr1lo 6 (by decide)]; rfl
    simp [evalArgs, Expr.eval, h0, hr1_10, hr1_11, h3, h4, h5, h6, hr1_12, hr1_13]
  have hArgsInnerW : ∀ v ∈ [gAddr, xBuf, pTable, Δ, L, b, z, outAddr, hInner], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hwords v (by simp)
    · omega
    · omega
    · exact hwords v (by simp)
    · exact hwords v (by simp)
    · exact hwords v (by simp)
    · exact hwords v (by simp)
    · omega
    · omega
  have hPreInner : (routeOrCutPairsWithWalksContract w).pre
      [gAddr, xBuf, pTable, Δ, L, b, z, outAddr, hInner] st1.mem := by
    have hHInnerW : hInner + routeOrCutPairsHeapSpace G.n G.m X.card pairs.length
        (routeOrCutCost G X pairs Δ L b z) + 16 < 2 ^ w := by
      dsimp only [hInner, outAddr, pTable, xBuf] at hCurEndLe ⊢; omega
    refine ⟨gAddr, xBuf, pTable, Δ, L, b, z, outAddr, hInner, G, X, pairs, rfl,
      hG1, hGValid, hVert1, hRPre.1, hRPre.2.1, hRPre.2.2.1, hRPre.2.2.2.1,
      hRPre.2.2.2.2.1, hRPre.2.2.2.2.2.1, hb, hPairs1, hPairsBInner, hRPre.2.2.2.2.2.2,
      hZInner, by dsimp only [hInner, outAddr, curEnd, bridgePairCur, pTable, xBuf]; omega,
      by dsimp only [hInner, outAddr, curEnd, bridgePairCur, pTable, xBuf]; omega,
      le_rfl, hHInnerW, by omega, hw16⟩
  -- Stage 2: call `routeOrCutPairsProc`
  obtain ⟨bodyInner, hBodyInner, oInner, stInner, c2, hCallRun, hPostInner, hc2⟩ :=
    hPairsMC [gAddr, xBuf, pTable, Δ, L, b, z, outAddr, hInner] st1.mem st1.pos ω
      hArgsInnerW hPreInner
  have hInnerCostEq : (routeOrCutPairsWithWalksContract w).cost
      [gAddr, xBuf, pTable, Δ, L, b, z, outAddr, hInner] st1.mem =
      routeOrCutPairsTotalCost G.m X.card pairs.length (routeOrCutCost G X pairs Δ L b z) := by
    simp only [routeOrCutPairsWithWalksContract, List.getD_cons_zero, List.getD_cons_succ]
    have hRG : ExpanderDecomp.readGraph st1.mem gAddr = G := readGraph_eq_of_graphAt hG1
    have hGm : st1.mem (gAddr + 1) = G.m := by
      have h1 := hG1 1 (by simp [Graph.encode])
      simpa [Graph.encode] using h1
    have hRX := readLenPrefixedList_of_vertSetAt_br hVert1
    have hRP := readPairs_of_pairsAt_br hPairs1
    have hPk : st1.mem pTable = pairs.length := hPairs1.1
    rw [hRG, hGm, hRX.1, hRX.2]
    simp only [Fin.val_cast]
    rw [hRP, hPk]
  rw [hInnerCostEq] at hc2
  set vInner := oInner.value
  have hInnerPost := hPostInner G X pairs hG1 hGValid hVert1 hRPre.1 hPairs1
  rcases hInnerPost with ⟨hOut2, hWalks2, hvInnerLo, hvInnerHi, hZ2, hFr2⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hOut2 hWalks2 hvInnerLo hvInnerHi hFr2
  set st2 : State := { regs := Function.update st1.regs 14 vInner, mem := stInner.mem, pos := stInner.pos }
  have hCallStmt : Runs w p ω
      (.call 14 (base + 1 + routerPairsEntryOff)
        [.reg 0, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6, .reg 12, .reg 13])
      st1 .normal st2 (c2 + argsSize [.reg 0, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6,
        .reg 12, .reg 13] + 1) :=
    runs_call_iff.mpr ⟨[gAddr, xBuf, pTable, Δ, L, b, z, outAddr, hInner], bodyInner,
      oInner, stInner, c2, hEvalInner, hBodyInner, hCallRun, rfl, rfl, by omega⟩
  have hSpec := routeOrCut_isMatchingPlayer.spec G X pairs Δ L b z hRPre.1 hRPre.2.1
    hRPre.2.2.1 hRPre.2.2.2.1 hRPre.2.2.2.2.1 hRPre.2.2.2.2.2.1 hb hRPre.2.2.2.2.2.2
  have hTotalCostBnd := routeOrCutPairsTotalCost_le_bridge (G := G) (X := X) (pairs := pairs)
    (L := L) (rcost := routeOrCutCost G X pairs Δ L b z) hRPre.2.2.2.2.1 hRPre.2.2.2.2.2.1
  -- Stage 3: branch on cut vs matched
  cases hRes : routeOrCut G X pairs Δ L b z with
  | cut U =>
    rw [hRes] at hOut2 hSpec
    have hCond1 : (Expr.load (.reg 12)).eval w st2 = some 1 := by
      simp [Expr.eval, st2, hr1_12, hOut2.1]
    have hUleX : U.card ≤ X.card := Finset.card_le_card hSpec.1
    have hXleN : X.card ≤ G.n := by simpa using Finset.card_le_card hRPre.1
    obtain ⟨st3, c3, hrun3, hList3, hEnd3, hZ3, hFr3, hc3⟩ :=
      bridgePackCut_runs (w := w) (h := h) (p := p) (ω := ω) (st := st2) hCopy
        (by simp [st2, hr1lo 9 (by decide), startState, xBuf]) (by simp [st2, hr1_12]) (by simp [st2])
        hOut2 (by dsimp only [outAddr, curEnd, bridgePairCur, pTable]; omega)
        (by omega) (by omega) hw16 hZ2
    have hCondRun : Runs w p ω
        (.cond (.load (.reg 12)) (bridgePackCutStmt (base + 15)) (bridgePackMatchedStmt (base + 15)))
        st2 (.returned vInner) st3 (c3 + (Expr.load (.reg 12)).size + 1) :=
      runs_cond_iff.mpr ⟨1, c3, hCond1, by simpa using hrun3, by omega⟩
    have hFull : Runs w p ω
        (routerBridgeProc (base + 1 + routerPairsEntryOff) (base + 15))
        (startState [gAddr, xAddr, pAddr, Δ, L, b, z, X.card, pairs.length, h] mem pos)
        (.returned vInner) st3
        (c1 + ((c2 + argsSize [.reg 0, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6,
          .reg 12, .reg 13] + 1) + (c3 + (Expr.load (.reg 12)).size + 1) + 1) + 1) := by
      unfold routerBridgeProc
      exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
        runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hCallStmt, hCondRun, rfl⟩), rfl⟩)
    refine ⟨.returned vInner, st3, _, hFull, ?_, ?_⟩
    · refine ⟨⟨?_, ?_, ?_, ?_, trivial⟩, gAddr, xAddr, pAddr, Δ, L, b, z, h, rfl, ?_, ?_⟩
      · simp only [Outcome.value, heapArg, List.getLastD_cons, List.getLastD_nil]; omega
      · simp only [Outcome.value, heapArg, List.getLastD_cons, List.getLastD_nil,
          List.getD_cons_zero, List.getD_cons_succ]; omega
      · intro a ha
        have ha' : a < h := by
          simpa [heapArg] using ha
        rw [hFr3 a ha']
        dsimp only [st2]
        rw [hFr2 a (by omega) (Or.inl (by omega)), hFr1 a ha']
      · exact hZ3
      · rwa [hRes]
      · simp only [Outcome.value]; rwa [hRes]
    · simp only [RouterProcContract, heapContract, List.getD_cons_zero, List.getD_cons_succ,
        argsSize, Expr.size, routerBridgeK]
      have hMulA : 1700 * (finsetWords X).length * (L + 1) =
          1700 * ((finsetWords X).length * (L + 1)) := Nat.mul_assoc _ _ _
      have hXleXL : X.card ≤ (finsetWords X).length * (L + 1) := by
        rw [hXlen]; exact Nat.le_mul_of_pos_right _ (by omega)
      omega
  | matched Ms emb =>
    rw [hRes] at hOut2 hWalks2 hSpec
    have hCond0 : (Expr.load (.reg 12)).eval w st2 = some 0 := by
      simp [Expr.eval, st2, hr1_12, hOut2.1]
    have ⟨hPairs2, hPairsB2⟩ := pairsAt_congr hPairs1 hPairsB1 fun a ha =>
      hFr2 a (by omega) (Or.inl ha)
    have hResLenLe := routeResultWords_matched_len_le hRes
    have hTotLe := routeOrCut_matched_total_le_cost hRes
    have hWalksLenLe := routeOrCut_matched_walks_len_le_cost hRes
    have hMsLen : Ms.length = pairs.length := hSpec.1
    obtain ⟨st3, c3, hrun3, hList3, hEnd3, hZ3, hFr3, hc3⟩ :=
      bridgePackMatched_runs (w := w) (h := h) (p := p) (ω := ω) (st := st2) hCopy
        (by simp [st2, hr1lo 8 (by decide), startState])
        (by simp [st2, hr1lo 9 (by decide), startState, xBuf])
        (by simp [st2, hr1_11]) (by simp [st2, hr1_12]) (by simp [st2, hr1_13])
        (by simp [st2]) (by simp [st2, hr1_15])
        hRPre.1 hRPre.2.2.2.2.2.2 hSpec hPairs2 hPairsB2 hOut2 hWalks2.1 hWalks2.2
        (by omega) rfl hvInnerLo hZ2 (by omega)
    set resEnd := vInner + G.n + pairs.length + (routeResultWords (.matched Ms emb)).length
    have hCondRun : Runs w p ω
        (.cond (.load (.reg 12)) (bridgePackCutStmt (base + 15)) (bridgePackMatchedStmt (base + 15)))
        st2 (.returned resEnd) st3 (c3 + (Expr.load (.reg 12)).size + 1) :=
      runs_cond_iff.mpr ⟨0, c3, hCond0, by simpa using hrun3, by omega⟩
    have hFull : Runs w p ω
        (routerBridgeProc (base + 1 + routerPairsEntryOff) (base + 15))
        (startState [gAddr, xAddr, pAddr, Δ, L, b, z, X.card, pairs.length, h] mem pos)
        (.returned resEnd) st3
        (c1 + ((c2 + argsSize [.reg 0, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6,
          .reg 12, .reg 13] + 1) + (c3 + (Expr.load (.reg 12)).size + 1) + 1) + 1) := by
      unfold routerBridgeProc
      exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
        runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hCallStmt, hCondRun, rfl⟩), rfl⟩)
    refine ⟨.returned resEnd, st3, _, hFull, ?_, ?_⟩
    · refine ⟨⟨?_, ?_, ?_, ?_, trivial⟩, gAddr, xAddr, pAddr, Δ, L, b, z, h, rfl, ?_, ?_⟩
      · simp only [Outcome.value, heapArg, List.getLastD_cons, List.getLastD_nil]; omega
      · simp only [Outcome.value, heapArg, List.getLastD_cons, List.getLastD_nil,
          List.getD_cons_zero, List.getD_cons_succ]; omega
      · intro a ha
        have ha' : a < h := by
          simpa [heapArg] using ha
        rw [hFr3 a ha']
        dsimp only [st2]
        rw [hFr2 a (by omega) (Or.inl (by omega)), hFr1 a ha']
      · exact hZ3
      · rwa [hRes]
      · simp only [Outcome.value]; rwa [hRes]
    · simp only [RouterProcContract, heapContract, List.getD_cons_zero, List.getD_cons_succ,
        argsSize, Expr.size, routerBridgeK]
      have hMulA : 1700 * (finsetWords X).length * (L + 1) =
          1700 * ((finsetWords X).length * (L + 1)) := Nat.mul_assoc _ _ _
      have hXleXL : X.card ≤ (finsetWords X).length * (L + 1) := by
        rw [hXlen]; exact Nat.le_mul_of_pos_right _ (by omega)
      omega

end MinCostFlow.HierPaths
