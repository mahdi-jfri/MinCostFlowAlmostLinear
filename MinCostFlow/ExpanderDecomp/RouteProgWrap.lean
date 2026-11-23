module

public import MinCostFlow.ExpanderDecomp.RouteProgWrapBase

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Verification of `routeOrCutPairsProc` (`RouteProgWrap`)

Verifies the `RouteProgLayout` entry procedure `routeOrCutPairsProc` (`base + 12` in
`routerProcs base`), which implements `routeOrCut` on `GraphAt`, `VertSetAt`, and `PairsAt`
inputs `[gAddr, xAddr, pAddr, Δ, L, b, z, outAddr, h]`:
- `RouteOutSortedAt`: strengthens `RouteOutAt` by guaranteeing that a cut `U` is written in
  strictly increasing vertex order (`U.sort (· ≤ ·)`).
- `routeOrCutPairsWithWalksContract`: top-level `PairsAt` contract writing `RouteOutSortedAt`
  at `outAddr` and (when matched) `WalksAt` at `h` with every walk inside `[h, h')`, returning
  `h'` with `h + (1 + X.card) ≤ h' ≤ h + routeOrCutPairsHeapSpace ...` and `ZeroFrom mem' h'`.
- `routeOrCutPairs_meetsContract`: proves `MeetsContract` for every relocatable placement
  `p.HasAt base (routerProcs base)` and word size `w`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Sorted Cut Output Layout and Sorting Helper -/

/-- Output layout at `outAddr` strengthening `RouteOutAt`: when `res = .cut U`, the cut vertices
at `outAddr + 2 .. outAddr + 1 + |U|` are stored in strictly increasing order `U.sort (· ≤ ·)`. -/
def RouteOutSortedAt (mem : ℕ → ℕ) (outAddr : ℕ) : RouteResult → Prop
  | .matched matchings _ =>
      mem outAddr = 0 ∧
      mem (outAddr + 1) = matchings.flatten.length ∧
      EdgesAt mem (outAddr + 2) matchings.flatten
  | .cut U =>
      mem outAddr = 1 ∧
      mem (outAddr + 1) = U.card ∧
      ListAt mem (outAddr + 2) (U.sort (· ≤ ·))

lemma RouteOutSortedAt.toRouteOutAt {mem : ℕ → ℕ} {outAddr : ℕ} {res : RouteResult}
    (h : RouteOutSortedAt mem outAddr res) :
    RouteOutAt mem outAddr res := by
  cases res with
  | matched matchings emb => exact h
  | cut U =>
    refine ⟨h.1, U.sort (· ≤ ·), Finset.sort_nodup U (· ≤ ·), Finset.sort_toFinset U (· ≤ ·),
      by rw [Finset.length_sort]; exact h.2.1, h.2.2⟩

private lemma list_eq_finset_sort {xs U_list : List ℕ} {U : Finset ℕ}
    (hperm : xs.Perm U_list) (hnd : U_list.Nodup) (hfin : U_list.toFinset = U)
    (hpw : xs.Pairwise (· ≤ ·)) :
    xs = U.sort (· ≤ ·) := by
  have hxs_nd : xs.Nodup := hperm.nodup_iff.mpr hnd
  have hsort_nd : (U.sort (· ≤ ·)).Nodup := Finset.sort_nodup U (· ≤ ·)
  have hperm_sort : xs.Perm (U.sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup hxs_nd hsort_nd]
    intro x
    rw [Finset.mem_sort, ← hfin, List.mem_toFinset]
    exact hperm.mem_iff
  exact hperm_sort.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hpw
    (Finset.pairwise_sort U (· ≤ ·))

private lemma listAt_tab {mem : ℕ → ℕ} {base n : ℕ} :
    ListAt mem base (tab n fun i => mem (base + i)) := by
  intro i hi
  simp [tab]

private lemma tab_eq_of_listAt {mem : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : ListAt mem base xs) :
    (tab xs.length fun i => mem (base + i)) = xs := by
  apply List.ext_getElem (by simp [tab])
  intro i hi _
  simp only [tab, List.getElem_map, List.getElem_range]
  exact h i (by simpa [tab] using hi)

/-! ## 2. Top-Level `PairsAt` Contract with Walks -/

/-- Top-level contract for `routeOrCutPairsProc` (`base + 12` of `routerProcs base`) on
`RouteProgLayout` inputs `[gAddr, xAddr, pAddr, Δ, L, b, z, outAddr, h]`.
Writes `RouteOutSortedAt` at `outAddr` (with cut `U` in increasing vertex order) and, when
matched, `WalksAt` at `h` with every walk stored inside `[h, v)`, returns bump-heap cursor `v`
with `h + (1 + X.card) ≤ v ≤ h + routeOrCutPairsHeapSpace ...` and `ZeroFrom mem' v`, and
preserves all memory below `h` outside `[outAddr, outAddr + 2 + 2 * G.n)`. -/
noncomputable def routeOrCutPairsWithWalksContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr xAddr pAddr Δ L b z outAddr h : ℕ)
      (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)),
      args = [gAddr, xAddr, pAddr, Δ, L, b, z, outAddr, h] ∧
      GraphAt mem gAddr G ∧ G.IsValid ∧
      VertSetAt mem xAddr X ∧ X ⊆ Finset.range G.n ∧
      (∀ ed ∈ G.inside X, ed.1 ≠ ed.2) ∧
      1 ≤ Δ ∧ (∀ v ∈ X, G.degIn X v ≤ Δ) ∧
      1 ≤ L ∧ X.card < 2 ^ L ∧ 2 ≤ b ∧
      PairsAt mem pAddr pairs ∧ PairsBounded mem pAddr pairs h ∧
      ValidTerminalPairs X pairs ∧
      ZeroFrom mem h ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + 1 + X.card ≤ h ∧
      outAddr + 2 + 2 * G.n ≤ h ∧
      h + routeOrCutPairsHeapSpace G.n G.m X.card pairs.length
        (routeOrCutCost G X pairs Δ L b z) + 16 < 2 ^ w ∧
      routeOrCutParamBound G.m X.card pairs.length Δ L b z < 2 ^ w ∧
      16 < 2 ^ w
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let pAddr := args.getD 2 0
    let Δ := args.getD 3 0
    let L := args.getD 4 0
    let b := args.getD 5 0
    let z := args.getD 6 0
    let outAddr := args.getD 7 0
    let h := args.getD 8 0
    ∀ (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)),
      GraphAt mem gAddr G → G.IsValid →
      VertSetAt mem xAddr X → X ⊆ Finset.range G.n →
      PairsAt mem pAddr pairs →
      let res := routeOrCut G X pairs Δ L b z
      let rcost := routeOrCutCost G X pairs Δ L b z
      RouteOutSortedAt mem' outAddr res ∧
      (match res with
       | .matched matchings emb =>
           WalksAt mem' h matchings.flatten.length emb ∧
           ∀ idx < matchings.flatten.length,
             h ≤ mem' (h + 1 + idx) ∧
             mem' (h + 1 + idx) + 1 + (emb idx).length ≤ v
       | .cut _ => True) ∧
      h + (1 + X.card) ≤ v ∧
      v ≤ h + routeOrCutPairsHeapSpace G.n G.m X.card pairs.length rcost ∧
      ZeroFrom mem' v ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + 2 * G.n ≤ a) → mem' a = mem a)
  cost args mem :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let pAddr := args.getD 2 0
    let Δ := args.getD 3 0
    let L := args.getD 4 0
    let b := args.getD 5 0
    let z := args.getD 6 0
    let G := readGraph mem gAddr
    let X := (readLenPrefixedList mem xAddr).toFinset
    let m := mem (gAddr + 1)
    let nX := mem xAddr
    let k := mem pAddr
    -- Model cost indexed by the unique decoded `pairs`
    let pairs := List.ofFn fun i : Fin k =>
      ((readLenPrefixedList mem (mem (pAddr + 1 + 2 * i.1))).toFinset,
       (readLenPrefixedList mem (mem (pAddr + 2 + 2 * i.1))).toFinset)
    routeOrCutPairsTotalCost m nX k (routeOrCutCost G X pairs Δ L b z)

/-! ## 3. Helper Lemmas for Decoding and Parameter Computation -/

private lemma readLenPrefixedList_of_vertSetAt {mem : ℕ → ℕ} {a : ℕ} {S : Finset ℕ}
    (h : VertSetAt mem a S) :
    (readLenPrefixedList mem a).toFinset = S ∧ mem a = S.card := by
  rcases h with ⟨xs, hnd, hfin, hseq⟩
  have hread : readLenPrefixedList mem a = xs := by
    unfold readLenPrefixedList
    rw [hseq.1, readList_eq_of_listAt hseq.2]
  exact ⟨hread ▸ hfin, by rw [hseq.1, ← hfin, List.toFinset_card_of_nodup hnd]⟩

private lemma readPairs_of_pairsAt {mem : ℕ → ℕ} {pAddr : ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} (hp : PairsAt mem pAddr pairs) :
    (List.ofFn fun i : Fin (mem pAddr) =>
      ((readLenPrefixedList mem (mem (pAddr + 1 + 2 * i.1))).toFinset,
       (readLenPrefixedList mem (mem (pAddr + 2 + 2 * i.1))).toFinset)) = pairs := by
  apply List.ext_getElem (by simp [hp.1])
  intro i hi _
  have hi' : i < pairs.length := by simpa [hp.1] using hi
  simp only [List.getElem_ofFn]
  have hpi := hp.2 i hi'
  exact Prod.ext (readLenPrefixedList_of_vertSetAt hpi.1).1
    (readLenPrefixedList_of_vertSetAt hpi.2).1

private lemma pairsAt_unique {mem : ℕ → ℕ} {pAddr : ℕ}
    {pairs₁ pairs₂ : List (Finset ℕ × Finset ℕ)}
    (h1 : PairsAt mem pAddr pairs₁) (h2 : PairsAt mem pAddr pairs₂) :
    pairs₁ = pairs₂ := by
  rw [← readPairs_of_pairsAt h1, readPairs_of_pairsAt h2]

private lemma vertSetAt_unique {mem : ℕ → ℕ} {a : ℕ} {X₁ X₂ : Finset ℕ}
    (h1 : VertSetAt mem a X₁) (h2 : VertSetAt mem a X₂) :
    X₁ = X₂ := by
  rw [← (readLenPrefixedList_of_vertSetAt h1).1, (readLenPrefixedList_of_vertSetAt h2).1]

private lemma graphAt_unique {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : Graph}
    (h1 : GraphAt mem a G₁) (h2 : GraphAt mem a G₂) :
    G₁ = G₂ := by
  rw [← readGraph_eq_of_graphAt h1, readGraph_eq_of_graphAt h2]

private lemma wrapComputeParams_triple {w : ℕ} {p : Program}
    {h n m nX m2 k Δ L b z outAddr initDem rcost : ℕ} {st0 : State}
    (hm2_le : m2 ≤ 2 * m) (hnX_le : nX ≤ n) (hdem_le : initDem ≤ nX)
    (hout_h : outAddr + 2 + 2 * n ≤ h) (hΔ : 1 ≤ Δ) (hL : 1 ≤ L) (hb : 2 ≤ b)
    (hw_sp : h + routeOrCutPairsHeapSpace n m nX k rcost + 16 < 2 ^ w)
    (hw_par : routeOrCutParamBound m nX k Δ L b z < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hr3 : st0.regs 3 = Δ) (hr4 : st0.regs 4 = L) (hr5 : st0.regs 5 = b)
    (hr11 : st0.regs 11 = nX) (hr12 : st0.regs 12 = k)
    (hr15 : st0.regs 15 = m2) (hr17 : st0.regs 17 = wrapPairsWorkAddr h n m nX) :
    Triple w p (fun st => st = st0)
      (seqStmts
        [ .assign 19 (.bin .add (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 3) (.reg 11)))
            (.bin .mul (.const 3) (.reg 12))) (.const 1))
        , .assign 20 (.bin .add (.reg 19) (.reg 12))
        , .assign 21 (.bin .add (.reg 20) (.reg 12))
        , .assign 22 (.bin .add (.reg 21) (.const 32))
        , .assign 23 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.reg 22) (.const 129))
            (.bin .mul (.const 27) (.reg 11))) (.reg 15)) (.bin .mul (.const 3) (.reg 12))) (.const 1))
        , .assign 24 (.bin .add (.bin .add (.reg 23) (.bin .mul (.const 2) (.reg 11))) (.const 2))
        , .assign 25 (.bin .mul (.bin .mul (.const 16) (.reg 3)) (.reg 5))
        , .assign 26 (.bin .mul (.reg 25) (.reg 4))
        , .assign 27 (.bin .mul (.const 2) (.reg 26))
        , .assign 28 (.bin .mul (.reg 25) (.bin .add (.reg 27) (.const 1)))
        , .assign 29 (.bin .mul (.reg 28) (.reg 4)) ])
      (normalPost fun st' =>
        st'.mem = st0.mem ∧
        (∀ r ≤ 18, st'.regs r = st0.regs r) ∧
        st'.regs 19 = wrapAccHeadAddr h n m nX k ∧ st'.regs 20 = wrapAccTailAddr h n m nX k ∧
        st'.regs 21 = wrapCfgAddr h n m nX k ∧ st'.regs 22 = wrapWsAddr h n m nX k ∧
        st'.regs 23 = wrapCLo h n m nX m2 k ∧ st'.regs 24 = wrapPLo h n m nX m2 k ∧
        st'.regs 26 = routeH Δ b * L ∧ st'.regs 27 = routeD Δ b L ∧
        st'.regs 28 = routeHBatch Δ b L ∧ st'.regs 29 = routeR Δ b L)
      (fun _ => 110) := by
  have hdisj := mkWrapLoopDisj (w := w) (rcost := rcost) hm2_le hnX_le hdem_le hout_h hw_sp hw_par hw16
  have hw_ah := hdisj.w_ah; have hw_at := hdisj.w_at; have hw_cfg := hdisj.w_cfg
  have hw_ws := hdisj.w_ws; have hw_hp := hdisj.w_hp; have hw_ch := hdisj.w_ch
  have hw_d := hdisj.w_d; have hw_hL := hdisj.w_hL; have hw_Hbatch_s := hdisj.w_Hbatch_s
  have hw_R := hdisj.w_R; have hw_b16 := hdisj.w_b16; have hw_nX4 := hdisj.w_nX4
  have hw_m2 := hdisj.w_m2; have hw_k := hdisj.w_k
  dsimp only [mkWrapLoopCfg] at hw_ah hw_at hw_cfg hw_ws hw_d hw_hL hw_Hbatch_s hw_R hw_b16 hw_nX4 hw_m2 hw_k
  have h16Δ : 16 * Δ < 2 ^ w := by
    have hpar : routeR Δ b L * (k * (routeD Δ b L + 3) + 1) + (nX + 1) * routeHBatch Δ b L +
        routeD Δ b L + 16 * b * (2 * m + Δ + 1) + z + 32 < 2 ^ w := hw_par
    have : 16 * Δ ≤ 16 * b * (2 * m + Δ + 1) := by nlinarith
    omega
  have hhP_le : routeH Δ b ≤ routeH Δ b * L := Nat.le_mul_of_pos_right _ hL
  have haccH : wrapPairsWorkAddr h n m nX + 3 * nX + 3 * k + 1 = wrapAccHeadAddr h n m nX k := by
    unfold wrapAccHeadAddr localPairsSpace; omega
  have hwsCLo : wrapWsAddr h n m nX k + 129 + 27 * nX + m2 + 3 * k + 1 =
      wrapCLo h n m nX m2 k := by
    unfold wrapCLo batchScratchSize; omega
  have hcLoPLo : wrapCLo h n m nX m2 k + 2 * nX + 2 = wrapPLo h n m nX m2 k := by
    unfold wrapPLo wrapCHi; omega
  have hD_eq : 2 * (routeH Δ b * L) = routeD Δ b L := by unfold routeD routePathLen routeH; ring
  have hHb_eq : routeH Δ b * (routeD Δ b L + 1) = routeHBatch Δ b L := by
    unfold routeHBatch routeBatchH routeH; ring
  have hR_eq : routeHBatch Δ b L * L = routeR Δ b L := rfl
  have hpLo_lt : wrapPLo h n m nX m2 k < 2 ^ w := by unfold wrapPHi at hw_hp; omega
  have hcLo_lt : wrapCLo h n m nX m2 k < 2 ^ w := by unfold wrapCHi at hw_ch; omega
  have hws_lt : wrapWsAddr h n m nX k + batchScratchSize nX m2 k + 1 < 2 ^ w := by
    unfold wrapCLo at hcLo_lt; omega
  have hws_sz : wrapWsAddr h n m nX k + 129 + 27 * nX + m2 + 3 * k + 1 < 2 ^ w := by
    rw [hwsCLo]; exact hcLo_lt
  have haccH_lt : wrapPairsWorkAddr h n m nX + 3 * nX + 3 * k + 1 < 2 ^ w := by
    rw [haccH]; omega
  have h16Δ_b : 16 * Δ * b < 2 ^ w := by
    change routeH Δ b < 2 ^ w; omega
  have hL_lt : L < 2 ^ w := by
    have hpos : 0 < 16 * Δ * b := Nat.mul_pos (Nat.mul_pos (by omega) hΔ) (by omega)
    have hle : L ≤ 16 * Δ * b * L := Nat.le_mul_of_pos_left L hpos
    have h1 : 16 * Δ * b * L = routeH Δ b * L := rfl
    omega
  wram_enter
  · subst st
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := wrapAccHeadAddr h n m nX k) (by rw [← haccH]; eval_expr) ?_
    refine runs_seq_assign_le (v := wrapAccTailAddr h n m nX k) (by unfold wrapAccTailAddr; eval_expr) ?_
    refine runs_seq_assign_le (v := wrapCfgAddr h n m nX k) (by unfold wrapCfgAddr; eval_expr) ?_
    refine runs_seq_assign_le (v := wrapWsAddr h n m nX k) (by unfold wrapWsAddr; eval_expr) ?_
    refine runs_seq_assign_le (v := wrapCLo h n m nX m2 k) (by rw [← hwsCLo]; eval_expr) ?_
    refine runs_seq_assign_le (v := wrapPLo h n m nX m2 k) (by rw [← hcLoPLo]; eval_expr) ?_
    refine runs_seq_assign_le (v := routeH Δ b) (by unfold routeH; eval_expr) ?_
    refine runs_seq_assign_le (v := routeH Δ b * L) (by eval_expr) ?_
    refine runs_seq_assign_le (v := routeD Δ b L) (by rw [← hD_eq]; eval_expr) ?_
    refine runs_seq_assign_le (v := routeHBatch Δ b L) (by rw [← hHb_eq]; eval_expr) ?_
    refine runs_assign_le (v := routeR Δ b L) (by rw [← hR_eq]; eval_expr) ?_ (by wram_cost)
    refine ⟨rfl, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Function.update_of_ne (by omega : r ≠ 29), Function.update_of_ne (by omega : r ≠ 28), Function.update_of_ne (by omega : r ≠ 27), Function.update_of_ne (by omega : r ≠ 26), Function.update_of_ne (by omega : r ≠ 25), Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 23), Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 21), Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 19)]
    all_goals simp

private lemma runs_cons_seqStmts {w c1 c2 : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : Stmt} {rest : List Stmt} {st0 st1 st2 : State} {o : Outcome}
    (hrest : rest ≠ []) (h1 : Runs w p ω s st0 .normal st1 c1)
    (h2 : Runs w p ω (seqStmts rest) st1 o st2 c2) :
    Runs w p ω (seqStmts (s :: rest)) st0 o st2 (c1 + c2 + 1) := by
  cases rest with
  | nil => exact absurd rfl hrest
  | cons _ _ => exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, h1, h2, rfl⟩)

/-! ## 4. Main Contract Proof for `routeOrCutPairsProc` -/

/-- Relocatable contract satisfaction for `routeOrCutPairsProc` (`base + 12` in
`routerProcs base`), for every placement `base` and word size `w`. -/
theorem routeOrCutPairs_meetsContract {w base : ℕ} {p : Program}
    (hp : p.HasAt base (routerProcs base)) :
    MeetsContract w p (base + routerPairsEntryOff) (routeOrCutPairsWithWalksContract w) := by
  -- Extract individual procedure placements from `p.HasAt base (routerProcs base)`
  have hp0 : p.HasAt base [siftDownProc] := fun i hi => by
    simp only [List.length_singleton] at hi; interval_cases i; simpa [routerProcs] using hp 0 (by simp [routerProcs])
  have hp1 : p.HasAt (base + 1) [heapSortProc base] := fun i hi => by
    simp only [List.length_singleton] at hi; interval_cases i; simpa [routerProcs] using hp 1 (by simp [routerProcs])
  have hp2 : p.HasAt (base + 2) [buildLocalCsrProc (base + 1)] := fun i hi => by
    simp only [List.length_singleton] at hi; interval_cases i; simpa [routerProcs] using hp 2 (by simp [routerProcs])
  have hp3 : p.HasAt (base + 3) [buildLocalPairsProc] := fun i hi => by
    simp only [List.length_singleton] at hi; interval_cases i; simpa [routerProcs] using hp 3 (by simp [routerProcs])
  have hp4 : p.procs[base + 4]? = some bfsLayersProc := by simpa [routerProcs] using hp 4 (by simp [routerProcs])
  have hp5 : p.procs[base + 5]? = some dfsBlockProc := by simpa [routerProcs] using hp 5 (by simp [routerProcs])
  have hp6 : p.procs[base + 6]? = some (shortPathBlockProc (base + 4) (base + 5)) := by simpa [routerProcs] using hp 6 (by simp [routerProcs])
  have hp7 : p.procs[base + 7]? = some buildResCsrProc := by simpa [routerProcs] using hp 7 (by simp [routerProcs])
  have hp8 : p.procs[base + 8]? = some buildCurBProc := by simpa [routerProcs] using hp 8 (by simp [routerProcs])
  have hp9 : p.procs[base + 9]? = some (growBallProc (base + 4)) := by simpa [routerProcs] using hp 9 (by simp [routerProcs])
  have hp10 : p.procs[base + 10]? = some (runBatchProc (base + 6) (base + 7) (base + 8) (base + 9)) := by simpa [routerProcs] using hp 10 (by simp [routerProcs])
  have hp11 : p.procs[base + 11]? = some (routeOrCutCsrProc (base + 10)) := by simpa [routerProcs] using hp 11 (by simp [routerProcs])
  have hp12 : p.procs[base + routerPairsEntryOff]? =
      some (routeOrCutPairsProc (base + 1) (base + 2) (base + 3) (base + 11)) := by
    simpa [routerProcs, routerPairsEntryOff] using hp 12 (by simp [routerProcs])
  have hsortMC : MeetsContract w p (base + 1) (heapSortContract w) := heapSort_spec hp0 hp1
  have hcsrMC : MeetsContract w p (base + 2) (buildLocalCsrContract w) :=
    buildLocalCsr_meetsContract hp2 hsortMC
  have hpairsMC : MeetsContract w p (base + 3) (buildLocalPairsContract w) :=
    buildLocalPairs_meetsContract hp3
  -- Unpack precondition
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨gAddr, xAddr, pAddr, Δ, L, b, z, outAddr, h, G, X, pairs,
    rfl, hGA, hGval, hX, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hP, hPbnd, hvtp,
    hzf, hg_h, hx_h, hout_h, hw_sp, hw_par, hw16⟩
  set n := G.n
  set m := G.m
  set nX := X.card
  set k := pairs.length
  set m2 := 2 * (G.inside X).length
  set initDem := totalDemand pairs
  set rcost := routeOrCutCost G X pairs Δ L b z
  have hnX_le : nX ≤ n := by
    have := Finset.card_le_card hX_sub; simpa [nX, n] using this
  have hm2_le : m2 ≤ 2 * m := by
    have : (G.inside X).length ≤ G.m := List.length_filter_le _ _
    dsimp only [m2, m]; omega
  have htp : RouteTerminalPairs X pairs := routeTerminalPairs_of_validTerminalPairs hvtp
  have hdem_le : initDem ≤ nX := routeTerminalPairs_totalDemand_le htp
  have hX_mem : mem xAddr = nX := (readLenPrefixedList_of_vertSetAt hX).2
  have hGn_mem : mem gAddr = n := graphAt_n hGA
  have hGm_mem : mem (gAddr + 1) = m := graphAt_m hGA
  have hPk_mem : mem pAddr = k := hP.1
  have hGenc_len : G.encode.length = 2 + 2 * m := by
    unfold Graph.encode; simp [Graph.m, m]; omega
  -- Stage 0: load n, m, nX, k and compute csrW = h + 1 + nX
  set st0 := startState [gAddr, xAddr, pAddr, Δ, L, b, z, outAddr, h] mem pos
  set csrW := wrapCsrWorkAddr h nX
  set st1 : State :=
    { mem := mem
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update st0.regs 9 n) 10 m) 11 nX) 12 k) 14 csrW
      pos := pos }
  have hst0_lt : gAddr < 2 ^ w ∧ xAddr < 2 ^ w ∧ pAddr < 2 ^ w ∧ Δ < 2 ^ w ∧ L < 2 ^ w ∧
      b < 2 ^ w ∧ z < 2 ^ w ∧ outAddr < 2 ^ w ∧ h < 2 ^ w :=
    ⟨hwords gAddr (by simp), hwords xAddr (by simp), hwords pAddr (by simp),
     hwords Δ (by simp), hwords L (by simp), hwords b (by simp),
     hwords z (by simp), hwords outAddr (by simp), hwords h (by simp)⟩
  have hcsrW_lt : csrW + localCsrSpace n m nX + 4 < 2 ^ w := by
    dsimp only [csrW, wrapCsrWorkAddr]; unfold routeOrCutPairsHeapSpace at hw_sp; omega
  have hstage0 : ∃ c0,
      Runs w p ω
        (seqStmts
          [ .assign 9 (.load (.reg 0)), .assign 10 (.load (.bin .add (.reg 0) (.const 1)))
          , .assign 11 (.load (.reg 1)), .assign 12 (.load (.reg 2))
          , .assign 14 (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 11)) ])
        st0 .normal st1 c0 ∧ c0 ≤ 35 := by
    have hg1_lt : gAddr + 1 < 2 ^ w := by omega
    have hcsr_lt0 : h + 1 + nX < 2 ^ w := by dsimp only [csrW, wrapCsrWorkAddr] at hcsrW_lt; omega
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .assign 9 (.load (.reg 0)), .assign 10 (.load (.bin .add (.reg 0) (.const 1)))
            , .assign 11 (.load (.reg 1)), .assign 12 (.load (.reg 2))
            , .assign 14 (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 11)) ])
          st0 o s c0 ∧ (o = .normal ∧ s = st1) ∧ 0 + c0 ≤ 35 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := n) (by simp [st0, startState, Expr.eval, hGn_mem]) ?_
      refine runs_seq_assign_le (v := m) (by rw [← hGm_mem]; eval_expr) ?_
      refine runs_seq_assign_le (v := nX) (by rw [← hX_mem]; eval_expr) ?_
      refine runs_seq_assign_le (v := k) (by rw [← hPk_mem]; eval_expr) ?_
      refine runs_assign_le (v := csrW) (by unfold csrW wrapCsrWorkAddr; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c0, hrun, ⟨rfl, rfl⟩, hc0⟩; exact ⟨c0, hrun, by omega⟩
  rcases hstage0 with ⟨c0, hrun0, hc0⟩
  -- Stage 1: call buildLocalCsrProc
  have hcsrArgs : evalArgs w st1 [.reg 0, .reg 1, .reg 14] = some [gAddr, xAddr, csrW] := by
    simp [evalArgs, Expr.eval, st1, st0, startState]
  have hcsrW_args : ∀ v ∈ [gAddr, xAddr, csrW], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  have hcsrPre : (buildLocalCsrContract w).pre [gAddr, xAddr, csrW] mem :=
    ⟨gAddr, xAddr, csrW, G, X, rfl, hGA, hGval, hX, hX_sub,
      by dsimp only [csrW, wrapCsrWorkAddr]; omega, by dsimp only [csrW, wrapCsrWorkAddr]; omega,
      fun a ha => hzf a (by dsimp only [csrW, wrapCsrWorkAddr] at ha; omega), hcsrW_lt, by omega⟩
  obtain ⟨st2, c1, ret1, hrun1, hpost1, hr2_15, hr2_oth, hc1⟩ :=
    runs_call_of_meetsContract (r := 15) hcsrMC hcsrArgs hcsrW_args hcsrPre ω
  have hpost1' := hpost1 G X hGA hGval hX hX_sub
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hpost1'
  rcases hpost1' with ⟨hm2_ret, horig2, hloc2, hcsr2, hfr2_lo, hzf2⟩
  subst hm2_ret
  simp only [buildLocalCsrContract, List.getD_cons_zero, List.getD_cons_succ, st1] at hc1
  rw [hGm_mem, hX_mem] at hc1
  -- Stage 2: compute locIdAddr and pairsW, call buildLocalPairsProc
  set locIdAddr := csrLocIdAddr csrW nX m
  set pairsW := wrapPairsWorkAddr h n m nX
  have hloc_eq : csrW + 3 * nX + 1 + 4 * m = locIdAddr := rfl
  have hpairsW_eq : locIdAddr + n = pairsW := by
    dsimp only [locIdAddr, pairsW, csrLocIdAddr, wrapPairsWorkAddr, localCsrSpace, csrW]; omega
  have hpairsW_lt : pairsW + localPairsSpace nX k + 4 < 2 ^ w := by
    dsimp only [pairsW, wrapPairsWorkAddr, wrapCsrWorkAddr]; unfold routeOrCutPairsHeapSpace at hw_sp; omega
  set st3 : State :=
    { st2 with regs := Function.update (Function.update st2.regs 16 locIdAddr) 17 pairsW }
  have hst2_regs : ∀ r ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14], st2.regs r = st1.regs r :=
    fun r hr => hr2_oth r (by intro h15; subst h15; simp at hr)
  have hstage2a : ∃ c2a,
      Runs w p ω
        (seqStmts
          [ .assign 16 (.bin .add (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 11)))
              (.const 1)) (.bin .mul (.const 4) (.reg 10)))
          , .assign 17 (.bin .add (.reg 16) (.reg 9)) ])
        st2 .normal st3 c2a ∧ c2a ≤ 25 := by
    have hr2_9 : st2.regs 9 = n := by rw [hr2_oth 9 (by decide)]; simp [st1]
    have hr2_10 : st2.regs 10 = m := by rw [hr2_oth 10 (by decide)]; simp [st1]
    have hr2_11 : st2.regs 11 = nX := by rw [hr2_oth 11 (by decide)]; simp [st1]
    have hr2_14 : st2.regs 14 = csrW := by rw [hr2_oth 14 (by decide)]; simp [st1]
    have h0 : ∃ o s c2a,
        Runs w p ω
          (seqStmts
            [ .assign 16 (.bin .add (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 11)))
                (.const 1)) (.bin .mul (.const 4) (.reg 10)))
            , .assign 17 (.bin .add (.reg 16) (.reg 9)) ])
          st2 o s c2a ∧ (o = .normal ∧ s = st3) ∧ 0 + c2a ≤ 25 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := locIdAddr) (by rw [← hloc_eq]; eval_expr) ?_
      refine runs_assign_le (v := pairsW) (by rw [← hpairsW_eq]; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c2a, hrun, ⟨rfl, rfl⟩, hc2a⟩; exact ⟨c2a, hrun, by omega⟩
  rcases hstage2a with ⟨c2a, hrun2a, hc2a⟩
  have hP2 : PairsAt st3.mem pAddr pairs := by
    refine ⟨(hfr2_lo pAddr (by have := hPbnd.1; dsimp only [csrW, wrapCsrWorkAddr]; omega)).trans hP.1,
      fun i hi => ?_⟩
    have hpi := hP.2 i hi
    have hbi := hPbnd.2 i hi
    have hpa : st2.mem (pAddr + 1 + 2 * i) = mem (pAddr + 1 + 2 * i) :=
      hfr2_lo _ (by have := hPbnd.1; dsimp only [csrW, wrapCsrWorkAddr]; omega)
    have hpb : st2.mem (pAddr + 2 + 2 * i) = mem (pAddr + 2 + 2 * i) :=
      hfr2_lo _ (by have := hPbnd.1; dsimp only [csrW, wrapCsrWorkAddr]; omega)
    dsimp only [st3]
    rw [hpa, hpb]
    exact ⟨VertSetAt.of_agree_below hpi.1 (by dsimp only [csrW, wrapCsrWorkAddr]; omega) (fun a ha => hfr2_lo a ha),
      VertSetAt.of_agree_below hpi.2 (by dsimp only [csrW, wrapCsrWorkAddr]; omega) (fun a ha => hfr2_lo a ha)⟩
  have hPbnd2 : PairsBounded st3.mem pAddr pairs pairsW := by
    refine ⟨by have := hPbnd.1; dsimp only [pairsW, wrapPairsWorkAddr, wrapCsrWorkAddr]; omega, fun i hi => ?_⟩
    have hbi := hPbnd.2 i hi
    have hpa : st2.mem (pAddr + 1 + 2 * i) = mem (pAddr + 1 + 2 * i) :=
      hfr2_lo _ (by have := hPbnd.1; dsimp only [csrW, wrapCsrWorkAddr]; omega)
    have hpb : st2.mem (pAddr + 2 + 2 * i) = mem (pAddr + 2 + 2 * i) :=
      hfr2_lo _ (by have := hPbnd.1; dsimp only [csrW, wrapCsrWorkAddr]; omega)
    dsimp only [st3]
    rw [hpa, hpb]
    dsimp only [pairsW, wrapPairsWorkAddr, wrapCsrWorkAddr]; omega
  have hpairsArgs : evalArgs w st3 [.reg 2, .reg 11, .reg 16, .reg 17, .reg 9] =
      some [pAddr, nX, locIdAddr, pairsW, n] := by
    have h2 : st3.regs 2 = pAddr := by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_oth 2 (by decide)]; simp [st1, st0, startState]
    have h11 : st3.regs 11 = nX := by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_oth 11 (by decide)]; simp [st1]
    have h9 : st3.regs 9 = n := by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_oth 9 (by decide)]; simp [st1]
    have h16 : st3.regs 16 = locIdAddr := by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_self]
    have h17 : st3.regs 17 = pairsW := by dsimp only [st3]; rw [Function.update_self]
    simp [evalArgs, Expr.eval, h2, h11, h16, h17, h9]
  have hpairsW_args : ∀ v ∈ [pAddr, nX, locIdAddr, pairsW, n], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
  have hpairsPre : (buildLocalPairsContract w).pre [pAddr, nX, locIdAddr, pairsW, n] st3.mem :=
    ⟨rfl, X, pairs, rfl, hX_sub, hP2, hPbnd2, htp, le_of_eq hpairsW_eq, hloc2, hzf2, hpairsW_lt, by omega⟩
  obtain ⟨st4, c2b, ret2, hrun2b, hpost2, hr4_18, hr4_oth, hc2b⟩ :=
    runs_call_of_meetsContract (r := 18) hpairsMC hpairsArgs hpairsW_args hpairsPre ω
  have hpost2' := hpost2 X pairs rfl hX_sub hP2 hPbnd2 htp (le_of_eq hpairsW_eq) hloc2
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hpost2'
  rcases hpost2' with ⟨hdem_ret, hlp4, hfr4_lo, hzf4⟩
  subst hdem_ret
  simp only [buildLocalPairsContract, List.getD_cons_zero, List.getD_cons_succ, hP2.1] at hc2b
  -- Stage 3: compute remaining addresses/params + writeRouteLoopCfgStmt
  have hr4_base : st4.regs 3 = Δ ∧ st4.regs 4 = L ∧ st4.regs 5 = b ∧ st4.regs 6 = z ∧
      st4.regs 7 = outAddr ∧ st4.regs 8 = h ∧ st4.regs 10 = m ∧ st4.regs 11 = nX ∧
      st4.regs 12 = k ∧ st4.regs 14 = csrW ∧ st4.regs 15 = m2 ∧ st4.regs 17 = pairsW := by
    have hlo : ∀ r, r ≤ 14 → st4.regs r = st1.regs r := fun r hr => by
      rw [hr4_oth r (by omega)]; dsimp only [st3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hr2_oth r (by omega)]
    exact ⟨by rw [hlo 3 (by decide)]; simp [st1, st0, startState],
      by rw [hlo 4 (by decide)]; simp [st1, st0, startState],
      by rw [hlo 5 (by decide)]; simp [st1, st0, startState],
      by rw [hlo 6 (by decide)]; simp [st1, st0, startState],
      by rw [hlo 7 (by decide)]; simp [st1, st0, startState],
      by rw [hlo 8 (by decide)]; simp [st1, st0, startState],
      by rw [hlo 10 (by decide)]; simp [st1], by rw [hlo 11 (by decide)]; simp [st1],
      by rw [hlo 12 (by decide)]; simp [st1], by rw [hlo 14 (by decide)]; simp [st1],
      by rw [hr4_oth 15 (by decide)]; dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr2_15,
      by rw [hr4_oth 17 (by decide)]; dsimp only [st3]; rw [Function.update_self]⟩
  obtain ⟨o5, st5, c3a, hrun3a, hpost3a, hc3a⟩ :=
    wrapComputeParams_triple (w := w) (p := p) (rcost := rcost) hm2_le hnX_le hdem_le hout_h hΔ hL hb
      hw_sp hw_par hw16 hr4_base.1 hr4_base.2.1 hr4_base.2.2.1 hr4_base.2.2.2.2.2.2.2.1
      hr4_base.2.2.2.2.2.2.2.2.1 hr4_base.2.2.2.2.2.2.2.2.2.2.1 hr4_base.2.2.2.2.2.2.2.2.2.2.2
      st4 ω rfl
  cases o5 with
  | returned _ => exact hpost3a.elim
  | normal =>
    rcases hpost3a with ⟨hmem5, hr5_lo, hr5_19, hr5_20, hr5_21, hr5_22, hr5_23, hr5_24,
      hr5_26, hr5_27, hr5_28, hr5_29⟩
    obtain ⟨o6, st6, c3b, hrun3b, hpost3b, hc3b⟩ :=
      writeRouteLoopCfg_triple (w := w) (p := p) (rcost := rcost) hm2_le hnX_le hout_h
        hw_sp hw_par hw16
        ((hr5_lo 5 (by decide)).trans hr4_base.2.2.1)
        ((hr5_lo 6 (by decide)).trans hr4_base.2.2.2.1)
        ((hr5_lo 7 (by decide)).trans hr4_base.2.2.2.2.1)
        ((hr5_lo 8 (by decide)).trans hr4_base.2.2.2.2.2.1)
        ((hr5_lo 10 (by decide)).trans hr4_base.2.2.2.2.2.2.1)
        ((hr5_lo 11 (by decide)).trans hr4_base.2.2.2.2.2.2.2.1)
        ((hr5_lo 12 (by decide)).trans hr4_base.2.2.2.2.2.2.2.2.1)
        ((hr5_lo 14 (by decide)).trans hr4_base.2.2.2.2.2.2.2.2.2.1)
        ((hr5_lo 15 (by decide)).trans hr4_base.2.2.2.2.2.2.2.2.2.2.1)
        ((hr5_lo 17 (by decide)).trans hr4_base.2.2.2.2.2.2.2.2.2.2.2)
        ((hr5_lo 18 (by decide)).trans hr4_18) hdem_le
        hr5_19 hr5_20 hr5_21 hr5_22 hr5_23 hr5_24 hr5_26 hr5_27 hr5_28 hr5_29
        st5 ω rfl
    cases o6 with
    | returned _ => exact hpost3b.elim
    | normal =>
      rcases hpost3b with ⟨hr6_eq, hcfg6, hfr6⟩
      -- Stage 4: call routeOrCutCsrProc
      set cfgAddr := wrapCfgAddr h n m nX k
      set pLo := wrapPLo h n m nX m2 k
      set pHi := wrapPHi h n m nX m2 k rcost
      set cLo := wrapCLo h n m nX m2 k
      set cHi := wrapCHi h n m nX m2 k
      set rcfg := mkWrapLoopCfg h n m nX m2 k Δ L b z outAddr initDem
      have hdisj := mkWrapLoopDisj (w := w) (rcost := rcost) hm2_le hnX_le hdem_le hout_h hw_sp hw_par hw16
      have hloopMC := routeOrCutCsr_meetsContract (w := w) hp11 hp10 hp6 hp4 hp5 hp7 hp8 hp9
        G X Δ b L pairs rcfg pLo pHi cLo cHi
      have hmem_pre6 : ∀ a < cfgAddr, st6.mem a = st4.mem a := fun a ha =>
        (hfr6 a (by omega)).trans (congrFun hmem5 a)
      have hcsr6 : AdjCsrAt st6.mem rcfg.batch.offAddr rcfg.batch.nbAddr rcfg.batch.edgeAddr X (adjOf G X) := by
        have hcsr_m2 : adjCsrOff X (adjOf G X) X.card ≤ m2 := by rw [adjCsrOff_adjOf_card]
        have h1 : csrOffAddr csrW X.card + X.card < pairsW := by
          dsimp only [csrOffAddr, pairsW, wrapPairsWorkAddr, localCsrSpace, csrW, nX]; omega
        have h2 : csrNbAddr csrW X.card + m2 ≤ pairsW := by
          dsimp only [csrNbAddr, pairsW, wrapPairsWorkAddr, localCsrSpace, csrW, nX]; omega
        have h3 : csrEdgeAddr csrW X.card G.m + m2 ≤ pairsW := by
          dsimp only [csrEdgeAddr, pairsW, wrapPairsWorkAddr, localCsrSpace, csrW, nX, m]; omega
        have h4 : pairsW ≤ cfgAddr := by
          dsimp only [pairsW, cfgAddr, wrapCfgAddr, wrapAccTailAddr, wrapAccHeadAddr]; omega
        exact hcsr2.congr
          (fun j hj => (hmem_pre6 _ (by omega)).trans (hfr4_lo _ (by omega)))
          (fun j hj => (hmem_pre6 _ (by omega)).trans (hfr4_lo _ (by omega)))
          (fun j hj => (hmem_pre6 _ (by omega)).trans (hfr4_lo _ (by omega)))
      have hlp6 : LocalPairsAt st6.mem rcfg.batch.pairBAddr rcfg.batch.aOffAddr
          rcfg.batch.aLenAddr rcfg.batch.aDataAddr X pairs X.card := by
        have hlt_cfg : pairsW + localPairsSpace nX k ≤ cfgAddr := by
          dsimp only [cfgAddr, wrapCfgAddr, wrapAccTailAddr, wrapAccHeadAddr]; omega
        refine ⟨fun v hv => by
            rw [hmem_pre6 _ (by dsimp only [rcfg, mkWrapLoopCfg, pairsBAddr, localPairsSpace] at hlt_cfg ⊢; omega)]
            exact hlp4.1 v hv,
          ⟨by rw [hmem_pre6 _ (by dsimp only [rcfg, mkWrapLoopCfg, pairsAOffAddr, localPairsSpace] at hlt_cfg ⊢; omega)]
              exact hlp4.2.1,
           fun j hj => ?_⟩⟩
        have hj4 := hlp4.2.2 j hj
        have ho1 := hmem_pre6 (pairsAOffAddr pairsW nX + j) (by dsimp only [pairsAOffAddr, localPairsSpace] at hlt_cfg ⊢; omega)
        have ho2 := hmem_pre6 (pairsAOffAddr pairsW nX + j + 1) (by dsimp only [pairsAOffAddr, localPairsSpace] at hlt_cfg ⊢; omega)
        have hl := hmem_pre6 (pairsALenAddr pairsW nX k + j) (by dsimp only [pairsALenAddr, localPairsSpace] at hlt_cfg ⊢; omega)
        refine ⟨by dsimp only [rcfg, mkWrapLoopCfg]; rw [ho1, ho2, hl]; exact hj4.1,
          by dsimp only [rcfg, mkWrapLoopCfg]; rw [hl]; exact hj4.2.1, fun t ht => ?_⟩
        have ht_lt : st4.mem (pairsAOffAddr pairsW nX + j) + t < X.card := by
          have hmo := localAPairsAt_slot_bound hlp4.2 (j + 1) pairs.length (by omega) le_rfl
          have h1 := hlp4.2.1; have h2 := hj4.1; have h3 := hj4.2.1
          rw [show pairsAOffAddr pairsW X.card + (j + 1) = pairsAOffAddr pairsW X.card + j + 1 by omega] at hmo
          simp only [List.length_map, Finset.length_sort] at ht
          dsimp only [nX, k] at h1 h2 h3 ⊢; omega
        dsimp only [rcfg, mkWrapLoopCfg]
        rw [ho1, Nat.add_assoc, hmem_pre6 _ (by dsimp only [pairsADataAddr, localPairsSpace] at hlt_cfg ⊢; omega),
          ← Nat.add_assoc]
        exact hj4.2.2 t ht
      have horig6 : ListAt st6.mem rcfg.origVertAddr (sortedX X) := fun j hj => by
        simp only [sortedX, Finset.length_sort] at hj
        have h1 : csrOrigAddr (wrapCsrWorkAddr h nX) + j < pairsW := by
          dsimp only [csrOrigAddr, pairsW, wrapPairsWorkAddr, localCsrSpace]; omega
        have h2 : pairsW ≤ cfgAddr := by
          dsimp only [pairsW, cfgAddr, wrapCfgAddr, wrapAccTailAddr, wrapAccHeadAddr]; omega
        exact ((hmem_pre6 _ (by dsimp only [rcfg, mkWrapLoopCfg]; omega)).trans
          (hfr4_lo _ (by dsimp only [rcfg, mkWrapLoopCfg]; omega))).trans (horig2 j (by simp [sortedX, hj]))
      have hzero_ws6 : ∀ a, (wrapAccHeadAddr h n m nX k ≤ a ∧ a < cfgAddr) ∨ cfgAddr + 32 ≤ a →
          st6.mem a = 0 := fun a ha => by
        rw [hfr6 a (by rcases ha with ⟨_, h1⟩ | h1 <;> omega), congrFun hmem5 a]
        exact hzf4 a (by dsimp only [wrapAccHeadAddr, cfgAddr, wrapCfgAddr, wrapAccTailAddr, pairsW, nX, k] at ha ⊢; omega)
      have hloopPre : (routeOrCutCsrContract w G X Δ b L pairs rcfg pLo pHi cLo cHi).pre [cfgAddr] st6.mem :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          hvtp, fun v hv => by have := Finset.mem_range.mp (hX_sub hv); omega,
          hcfg6, hdisj, le_rfl, hcsr6, hlp6, horig6,
          fun j hj => ⟨hzero_ws6 _ (Or.inl ⟨by dsimp only [rcfg, mkWrapLoopCfg]; omega,
              by dsimp only [rcfg, mkWrapLoopCfg, cfgAddr, wrapCfgAddr, wrapAccTailAddr]; omega⟩),
            hzero_ws6 _ (Or.inl ⟨by dsimp only [rcfg, mkWrapLoopCfg, wrapAccTailAddr]; omega,
              by dsimp only [rcfg, mkWrapLoopCfg, cfgAddr, wrapCfgAddr]; omega⟩)⟩,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsIsoStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsMatchAStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsVisStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsCurStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsUsedStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsDeadStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsBallStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _,
          fun v hv => by rw [hzero_ws6 _ (Or.inr (by dsimp only [rcfg, mkWrapLoopCfg, wsLiveStamp, wrapWsAddr]; omega))]; exact Nat.zero_le _⟩
      have hloopArgs : evalArgs w st6 [.reg 21] = some [cfgAddr] := by
        simp [evalArgs, Expr.eval, hr6_eq, hr5_21]
      have hloopW : ∀ v ∈ [cfgAddr], v < 2 ^ w := fun v hv => by
        simp only [List.mem_singleton] at hv; subst hv; have := hdisj.w_cfg; omega
      obtain ⟨st7, c4, tag7, hrun4, hpost4, hr7_30, hr7_oth, hc4⟩ :=
        runs_call_of_meetsContract (r := 30) hloopMC hloopArgs hloopW hloopPre ω
      rcases hpost4 with ⟨htag7, hout7, hwalks7, hp_lo7, hp_hi7, hfr7⟩
      simp only [List.getD_cons_zero] at hwalks7 hp_lo7 hp_hi7 hfr7
      simp only [routeOrCutCsrContract, argsSize, Expr.size] at hc4
      -- Combine frames below `h` and `ZeroFrom` at `hOut := st7.mem (cfgAddr + 22) + 15 * nX`
      set hOut := st7.mem (cfgAddr + 22) + 15 * nX
      have hp_lo7' : pLo ≤ st7.mem (cfgAddr + 22) := hp_lo7
      have hp_hi7' : st7.mem (cfgAddr + 22) ≤ pLo + 5 * rcost := hp_hi7
      have hOut_le : hOut ≤ h + routeOrCutPairsHeapSpace n m nX k rcost := by
        dsimp only [hOut, pLo, wrapPLo, wrapCHi, wrapCLo, wrapWsAddr, wrapCfgAddr,
          wrapAccTailAddr, wrapAccHeadAddr, wrapPairsWorkAddr, wrapCsrWorkAddr,
          routeOrCutPairsHeapSpace, batchScratchSize] at hp_hi7' ⊢
        omega
      have hOut_ge : h + (1 + nX) ≤ hOut := by
        dsimp only [hOut, pLo, wrapPLo, wrapCHi, wrapCLo, wrapWsAddr, wrapCfgAddr,
          wrapAccTailAddr, wrapAccHeadAddr, wrapPairsWorkAddr, wrapCsrWorkAddr] at hp_lo7' ⊢
        omega
      have hzf7 : ZeroFrom st7.mem hOut := fun a ha => by
        have hnot : ¬ RouteLoopWriteSet rcfg cfgAddr hOut cLo cHi a := by
          dsimp only [RouteLoopWriteSet, BatchWriteSet, rcfg, mkWrapLoopCfg, hOut, pLo, cLo, cHi, cfgAddr, pairsW,
            wrapPLo, wrapCHi, wrapCLo, wrapWsAddr, wrapCfgAddr, wrapAccTailAddr, wrapAccHeadAddr,
            wrapPairsWorkAddr, wrapCsrWorkAddr, pairsBAddr, pairsALenAddr, pairsADataAddr,
            localPairsSpace] at hp_lo7' ha ⊢
          rintro ((h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) | h1 | h1) <;> omega
        rw [hfr7 a hnot]
        exact hzero_ws6 a (Or.inr (by
          dsimp only [hOut, pLo, wrapPLo, wrapCHi, wrapCLo, wrapWsAddr, cfgAddr] at hp_lo7' ha ⊢; omega))
      have hfr7_low : ∀ a < h, (a < outAddr ∨ outAddr + 2 + 2 * n ≤ a) → st7.mem a = mem a :=
        fun a ha hout => by
          have hnot : ¬ RouteLoopWriteSet rcfg cfgAddr hOut cLo cHi a := by
            dsimp only [RouteLoopWriteSet, BatchWriteSet, rcfg, mkWrapLoopCfg, cLo, cHi, cfgAddr, pairsW,
              wrapPLo, wrapCHi, wrapCLo, wrapWsAddr, wrapCfgAddr, wrapAccTailAddr, wrapAccHeadAddr,
              wrapPairsWorkAddr, wrapCsrWorkAddr, pairsBAddr, pairsALenAddr, pairsADataAddr]
            rintro ((hb | hb | hb | hb | hb | hb | hb | hb | hb) | hb | hb) <;> omega
          rw [hfr7 a hnot, hmem_pre6 a (by dsimp only [cfgAddr, wrapCfgAddr, wrapAccTailAddr, wrapAccHeadAddr, wrapPairsWorkAddr, wrapCsrWorkAddr]; omega),
            hfr4_lo a (by dsimp only [pairsW, wrapPairsWorkAddr, wrapCsrWorkAddr]; omega),
            hfr2_lo a (by dsimp only [csrW, wrapCsrWorkAddr]; omega)]
      -- Stage 5: conditional sort of cut U, then return hOut
      have hr7_7 : st7.regs 7 = outAddr := by rw [hr7_oth 7 (by decide), hr6_eq, hr5_lo 7 (by decide)]; exact hr4_base.2.2.2.2.1
      have hr7_11 : st7.regs 11 = nX := by rw [hr7_oth 11 (by decide), hr6_eq, hr5_lo 11 (by decide)]; exact hr4_base.2.2.2.2.2.2.2.1
      have hr7_21 : st7.regs 21 = cfgAddr := by rw [hr7_oth 21 (by decide), hr6_eq]; exact hr5_21
      have hstage5 : ∃ st8 c5,
          Runs w p ω
            (.cond (.reg 30)
              (.call 31 (base + 1) [.bin .add (.reg 7) (.const 2), .load (.bin .add (.reg 7) (.const 1))])
              .nop)
            st7 .normal st8 c5 ∧
          st8.regs 11 = nX ∧ st8.regs 21 = cfgAddr ∧
          st8.mem (cfgAddr + 22) = st7.mem (cfgAddr + 22) ∧
          RouteOutSortedAt st8.mem outAddr (routeOrCut G X pairs Δ L b z) ∧
          (match routeOrCut G X pairs Δ L b z with
           | .matched matchings emb =>
               WalksAt st8.mem h matchings.flatten.length emb ∧
               ∀ idx < matchings.flatten.length,
                 h ≤ st8.mem (h + 1 + idx) ∧
                 st8.mem (h + 1 + idx) + 1 + (emb idx).length ≤ hOut
           | .cut _ => True) ∧
          ZeroFrom st8.mem hOut ∧
          (∀ a < h, (a < outAddr ∨ outAddr + 2 + 2 * n ≤ a) → st8.mem a = mem a) ∧
          c5 ≤ buildLocalCsrCost m nX + 20 := by
        dsimp only [rcfg, mkWrapLoopCfg] at htag7 hout7 hwalks7
        cases hres : routeOrCut G X pairs Δ L b z with
        | matched matchings emb =>
          rw [hres] at htag7 hout7 hwalks7
          have hcond0 : (Expr.reg 30).eval w st7 = some 0 := by simp [Expr.eval, hr7_30, htag7]
          refine ⟨st7, _, batch_runs_cond_zero hcond0 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), hr7_11, hr7_21, rfl, hout7, ?_,
            hzf7, hfr7_low, by dsimp only [Expr.size, buildLocalCsrCost]; omega⟩
          refine ⟨hwalks7.1, fun idx hidx => ?_⟩
          have hbnd := hwalks7.2 idx hidx
          have hp_ge_h : h ≤ pLo := by
            dsimp only [pLo, wrapPLo, wrapCHi, wrapCLo, wrapWsAddr, wrapCfgAddr,
              wrapAccTailAddr, wrapAccHeadAddr, wrapPairsWorkAddr, wrapCsrWorkAddr]; omega
          exact ⟨le_trans hp_ge_h hbnd.1, by dsimp only [hOut]; omega⟩
        | cut U =>
          rw [hres] at htag7 hout7
          rcases hout7 with ⟨ho0, U_list, hU_nd, hU_fin, ho1, hU_at⟩
          have hU_sub : U ⊆ X := by
            have hspec := routeOrCut_spec (z := z) G pairs htp hΔ hb hL hdeg hXL
            rw [hres] at hspec; exact hspec.1
          have hU_card_le : U.card ≤ nX := Finset.card_le_card hU_sub
          have hU_len : U_list.length = U.card := by rw [← hU_fin, List.toFinset_card_of_nodup hU_nd]
          have hcond1 : (Expr.reg 30).eval w st7 = some 1 := by simp [Expr.eval, hr7_30, htag7]
          have hsortArgs : evalArgs w st7 [.bin .add (.reg 7) (.const 2), .load (.bin .add (.reg 7) (.const 1))] =
              some [outAddr + 2, U.card] := by
            have h1w : outAddr + 1 < 2 ^ w := by omega
            have h2w : outAddr + 2 < 2 ^ w := by omega
            simp [evalArgs, Expr.eval, BinOp.eval, hr7_7, ho1, hU_len, h1w, h2w, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega]
          have hsortW : ∀ v ∈ [outAddr + 2, U.card], v < 2 ^ w := fun v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl <;> omega
          have hsortPre : (heapSortContract w).pre [outAddr + 2, U.card] st7.mem := by
            refine ⟨outAddr + 2, U.card, rfl, by omega, by omega, by omega, fun i hi => ?_⟩
            have hi' : i < U_list.length := by omega
            rw [hU_at i hi']
            have hmemU : U_list[i]'hi' ∈ U := by rw [← hU_fin, List.mem_toFinset]; exact List.getElem_mem hi'
            have hlt_n := Finset.mem_range.mp (hX_sub (hU_sub hmemU))
            omega
          obtain ⟨st8, cSort, _, hrunSort, hpostSort, _, hr8_oth, hcSort⟩ :=
            runs_call_of_meetsContract (r := 31) hsortMC hsortArgs hsortW hsortPre ω
          simp only [heapSortContract, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size] at hpostSort hcSort
          rcases hpostSort with ⟨_, hperm, hpw, _, hfrSort⟩
          have htab_eq : (tab U.card fun i => st7.mem (outAddr + 2 + i)) = U_list := by
            rw [← hU_len]; exact tab_eq_of_listAt hU_at
          rw [htab_eq] at hperm
          have hsorted_eq : (tab U.card fun i => st8.mem (outAddr + 2 + i)) = U.sort (· ≤ ·) :=
            list_eq_finset_sort hperm hU_nd hU_fin hpw
          have hfrSort_out : ∀ a, (a < outAddr + 2 ∨ outAddr + 2 + U.card ≤ a) → st8.mem a = st7.mem a :=
            fun a ha => hfrSort a ha
          have hlog_le : Nat.log 2 (U.card + 2) ≤ Nat.log 2 (nX + 2) := Nat.log_mono_right (by omega)
          have hsort_cost_le : 280 * (U.card * (2 * Nat.log 2 (U.card + 2) + 1) + 1) ≤ buildLocalCsrCost m nX := by
            have hmul : U.card * (2 * Nat.log 2 (U.card + 2) + 1) ≤ nX * (2 * Nat.log 2 (nX + 2) + 1) :=
              Nat.mul_le_mul hU_card_le (by omega)
            unfold buildLocalCsrCost; omega
          refine ⟨st8, _, batch_runs_cond_pos hcond1 (by decide) hrunSort,
            (hr8_oth 11 (by decide)).trans hr7_11, (hr8_oth 21 (by decide)).trans hr7_21,
            hfrSort_out _ (Or.inr (by dsimp only [cfgAddr, wrapCfgAddr, wrapAccTailAddr, wrapAccHeadAddr, wrapPairsWorkAddr, wrapCsrWorkAddr]; omega)),
            ⟨(hfrSort_out outAddr (Or.inl (by omega))).trans ho0,
             (hfrSort_out (outAddr + 1) (Or.inl (by omega))).trans (ho1.trans hU_len),
             by rw [← hsorted_eq]; exact listAt_tab⟩,
            trivial,
            fun a ha => (hfrSort_out a (Or.inr (by omega))).trans (hzf7 a ha),
            fun a ha hout => (hfrSort_out a (by rcases hout with h1 | h1 <;> [left; right] <;> omega)).trans (hfr7_low a ha hout),
            by dsimp only [Expr.size]; omega⟩
      rcases hstage5 with ⟨st8, c5, hrun5, hr8_11, hr8_21, hm8_22, hout8, hwalks8, hzf8, hfr8_low, hc5⟩
      -- Final return statement: ret (mem[cfgAddr + 22] + 15 * nX)
      have hret_eval : (Expr.bin .add (.load (.bin .add (.reg 21) (.const 22)))
          (.bin .mul (.const 15) (.reg 11))).eval w st8 = some hOut := by
        have hcfg22 : cfgAddr + 22 < 2 ^ w := by have := hdisj.w_cfg; omega
        have h15n : 15 * nX < 2 ^ w := by omega
        have hOut_w : hOut < 2 ^ w := by omega
        simp [Expr.eval, BinOp.eval, hr8_21, hr8_11, hm8_22, hcfg22, h15n, hOut_w, hOut,
          show 22 < 2 ^ w by omega, show 15 < 2 ^ w by omega]
      obtain ⟨cRet, hrunRet, hcRet⟩ :
          ∃ cRet, Runs w p ω (.ret (.bin .add (.load (.bin .add (.reg 21) (.const 22)))
            (.bin .mul (.const 15) (.reg 11)))) st8 (.returned hOut) st8 cRet ∧ cRet ≤ 15 := by
        have h0 : ∃ o s cRet,
            Runs w p ω (.ret (.bin .add (.load (.bin .add (.reg 21) (.const 22)))
              (.bin .mul (.const 15) (.reg 11)))) st8 o s cRet ∧
            (o = .returned hOut ∧ s = st8) ∧ 0 + cRet ≤ 15 :=
          runs_ret_le (v := hOut) hret_eval ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, cRet, hrun, ⟨rfl, rfl⟩, hcRet⟩; exact ⟨cRet, hrun, by omega⟩
      -- Chain all runs into `routeOrCutPairsProc`
      have hrun_3b4 : Runs w p ω
          (seqStmts
            [ writeRouteLoopCfgStmt, .call 30 (base + 11) [.reg 21]
            , .cond (.reg 30)
                (.call 31 (base + 1) [.bin .add (.reg 7) (.const 2), .load (.bin .add (.reg 7) (.const 1))])
                .nop
            , .ret (.bin .add (.load (.bin .add (.reg 21) (.const 22))) (.bin .mul (.const 15) (.reg 11))) ])
          st5 (.returned hOut) st8 (c3b + (c4 + (c5 + cRet + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st6, c3b, _, hrun3b,
          runs_seq_iff.mpr (Or.inr ⟨st7, c4, _, hrun4,
            runs_seq_iff.mpr (Or.inr ⟨st8, c5, cRet, hrun5, hrunRet, rfl⟩), rfl⟩), rfl⟩)
      obtain ⟨c34, hrun34, hc34⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun3a hrun_3b4
      have hrun_2b34 := runs_cons_seqStmts (by simp) hrun2b hrun34
      obtain ⟨c234, hrun234, hc234⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun2a hrun_2b34
      have hrun_1234 := runs_cons_seqStmts (by simp) hrun1 hrun234
      obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun0 hrun_1234
      refine ⟨routeOrCutPairsProc (base + 1) (base + 2) (base + 3) (base + 11), hp12,
        .returned hOut, st8, cAll, hrunAll, ?_, ?_⟩
      · dsimp only [routeOrCutPairsWithWalksContract, Outcome.value]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        intro G' X' pairs' hGA' _ hX' _ hP'
        have hGe : G' = G := graphAt_unique hGA' hGA
        have hXe : X' = X := vertSetAt_unique hX' hX
        have hPe : pairs' = pairs := pairsAt_unique hP' hP
        subst hGe; subst hXe; subst hPe
        exact ⟨hout8, hwalks8, hOut_ge, hOut_le, hzf8, hfr8_low⟩
      · dsimp only [routeOrCutPairsWithWalksContract, List.getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some]
        rw [readGraph_eq_of_graphAt hGA, (readLenPrefixedList_of_vertSetAt hX).1,
          readPairs_of_pairsAt hP, hGm_mem, hX_mem, hPk_mem]
        dsimp only [rcfg, mkWrapLoopCfg] at hc4
        dsimp only [k, routeOrCutPairsTotalCost, routeOrCutPairsSetupCost, argsSize, Expr.size,
          List.length_cons, List.length_nil] at hc0 hc1 hc2a hc2b hc3a hc3b hc4 hc5 hcRet hc34 hc234 hcAll ⊢
        omega

end MinCostFlow.ExpanderDecomp
