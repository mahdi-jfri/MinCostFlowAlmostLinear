module

public import MinCostFlow.ExpanderDecomp.RouteProgWrap

import Mathlib.Tactic.Linarith

/-!
# Top-Level `RouteOrCut` Contracts, Program Assembly, and Contract Bridges (`RouteProg`)

Completes the deterministic Word-RAM formalization of `RouteOrCut`:
- `routeOrCutMultiWithWalksContract`: top-level contract on the flat multi-pair layout
  `[gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h]` (`GraphAt`, `LenListAt`, `MultiPairsAt`),
  writing `RouteOutSortedAt` at `outAddr` (with cut `U` in strictly increasing vertex order
  `U.sort (· ≤ ·)`) and, when matched, `WalksAt` at `h + 1 + 2 * k` with every walk inside `[h, v)`.
- `routeOrCutMulti_meetsContract`: relocatable contract proof for `base + 13` in `routerProcs base`
  (and standalone corollaries `routeOrCutProgram_pairs_meetsContract`,
  `routeOrCutProgram_multi_meetsContract` for the 14-procedure deterministic `routeOrCutProgram`).
- `routeOrCutMultiWithWalks_implies_multiPairRouter_of_bounds` and
  `routeOrCutMultiWithWalks_implies_routeOrCut_of_bounds`: exact bridge theorems showing that
  `routeOrCutMultiWithWalksContract` implies `multiPairRouterContract`
  (`ProgStepCSpec.lean`) and `routeOrCutContract` (`OuterProgContracts.lean`) whenever the
  input-setup cost, heap-space, and parameter word-size bounds hold.
- Non-vacuity witnesses `routeOrCutPairsWithWalksContract_pre_example` and
  `routeOrCutMultiWithWalksContract_pre_example`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Top-Level Flat Multi-Pair Contract with Walks -/

/-- Top-level contract for `routeOrCutMultiProc` (`base + 13` of `routerProcs base`) using the
exact 9-argument flat input layout `[gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h]` of
`multiPairRouterContract` (`ProgStepCSpec.lean`) and `routeOrCutContract` (`OuterProgContracts.lean`).

Outputs:
* `RouteOutSortedAt mem' outAddr (routeOrCut G X pairs Δ L b z)`: exact `RouteOutAt` at `outAddr`
  with any cut `U` written in strictly increasing vertex order `U.sort (· ≤ ·)`.
* When `.matched matchings emb`: `WalksAt mem' (h + 1 + 2 * k) matchings.flatten.length emb` with
  every walk pointer and walk word stored inside `[h, v)`.
* Bump-heap cursor `v` satisfying `h + (1 + 2 * k) + (1 + X.card) ≤ v ≤ h + routeOrCutMultiHeapSpace ...`
  and `ZeroFrom mem' v`, preserving all memory `< h` outside `[outAddr, outAddr + 2 + 2 * G.n)`. -/
noncomputable def routeOrCutMultiWithWalksContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr xAddr pairsAddr Δ L b z outAddr h : ℕ)
      (G : Graph) (X_list : List ℕ) (pairLists : List (List ℕ × List ℕ)),
      args = [gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h] ∧
      GraphAt mem gAddr G ∧ G.IsValid ∧
      LenListAt mem xAddr X_list ∧ X_list.Nodup ∧
      X_list.toFinset ⊆ Finset.range G.n ∧
      (∀ ed ∈ G.inside X_list.toFinset, ed.1 ≠ ed.2) ∧
      1 ≤ Δ ∧ (∀ v ∈ X_list.toFinset, G.degIn X_list.toFinset v ≤ Δ) ∧
      1 ≤ L ∧ X_list.toFinset.card < 2 ^ L ∧ 2 ≤ b ∧
      MultiPairsAt mem pairsAddr pairLists ∧
      (∀ pl ∈ pairLists, pl.1.Nodup ∧ pl.2.Nodup) ∧
      ValidTerminalPairs X_list.toFinset (pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset)) ∧
      ZeroFrom mem h ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + 1 + X_list.length ≤ h ∧
      pairsAddr + (encodePairs pairLists).length ≤ h ∧
      outAddr + 2 + 2 * G.n ≤ h ∧
      h + routeOrCutMultiHeapSpace G.n G.m X_list.toFinset.card pairLists.length
        (routeOrCutCost G X_list.toFinset
          (pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset)) Δ L b z) + 16 < 2 ^ w ∧
      routeOrCutParamBound G.m X_list.toFinset.card pairLists.length Δ L b z < 2 ^ w ∧
      16 < 2 ^ w
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let pairsAddr := args.getD 2 0
    let Δ := args.getD 3 0
    let L := args.getD 4 0
    let b := args.getD 5 0
    let z := args.getD 6 0
    let outAddr := args.getD 7 0
    let h := args.getD 8 0
    let G := readGraph mem gAddr
    let X := (readLenPrefixedList mem xAddr).toFinset
    let pairs := readMultiPairs mem pairsAddr
    let k := pairs.length
    let res := routeOrCut G X pairs Δ L b z
    let rcost := routeOrCutCost G X pairs Δ L b z
    RouteOutSortedAt mem' outAddr res ∧
    (match res with
     | .matched matchings emb =>
         WalksAt mem' (h + 1 + 2 * k) matchings.flatten.length emb ∧
         ∀ idx < matchings.flatten.length,
           h ≤ mem' (h + 1 + 2 * k + 1 + idx) ∧
           mem' (h + 1 + 2 * k + 1 + idx) + 1 + (emb idx).length ≤ v
     | .cut _ => True) ∧
    h + (1 + 2 * k) + (1 + X.card) ≤ v ∧
    v ≤ h + routeOrCutMultiHeapSpace G.n G.m X.card k rcost ∧
    ZeroFrom mem' v ∧
    (∀ a < h, (a < outAddr ∨ outAddr + 2 + 2 * G.n ≤ a) → mem' a = mem a)
  cost args mem :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let pairsAddr := args.getD 2 0
    let Δ := args.getD 3 0
    let L := args.getD 4 0
    let b := args.getD 5 0
    let z := args.getD 6 0
    let G := readGraph mem gAddr
    let X := (readLenPrefixedList mem xAddr).toFinset
    let pairs := readMultiPairs mem pairsAddr
    routeOrCutMultiTotalCost G.m X.card pairs.length (routeOrCutCost G X pairs Δ L b z)

/-! ## 2. Contract Proofs for `routeOrCutMultiProc` and `routeOrCutProgram` -/

/-- Relocatable contract satisfaction for `routeOrCutMultiProc` (`base + 13` in
`routerProcs base`), for every placement `base` and word size `w`. -/
theorem routeOrCutMulti_meetsContract {w base : ℕ} {p : Program}
    (hp : p.HasAt base (routerProcs base)) :
    MeetsContract w p (base + routerMultiEntryOff) (routeOrCutMultiWithWalksContract w) := by
  have hp13 : p.procs[base + routerMultiEntryOff]? =
      some (routeOrCutMultiProc (base + routerPairsEntryOff)) := by
    simpa [routerProcs, routerMultiEntryOff, routerPairsEntryOff] using hp 13 (by simp [routerProcs])
  have hpairsEntryMC := routeOrCutPairs_meetsContract (w := w) hp
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h, G, X_list, pairLists,
    rfl, hGA, hGval, hX_at, hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hmp, hpl_nd, hvtp,
    hzf, hg_h, hx_h, hp_h, hout_h, hw_sp, hw_par, hw16⟩
  set X := X_list.toFinset
  set pairs := pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset)
  set k := pairLists.length
  set rcost := routeOrCutCost G X pairs Δ L b z
  have hX_len : X_list.length = X.card := (List.toFinset_card_of_nodup hX_nd).symm
  have hX_vs : VertSetAt mem xAddr X := ⟨X_list, hX_nd, rfl, hX_at⟩
  have hmp_k : mem pairsAddr = k := by
    unfold MultiPairsAt encodePairs at hmp; rw [listAt_cons] at hmp; exact hmp.1
  have hk_pairs : pairs.length = k := by simp [pairs, k]
  have hst0_lt : gAddr < 2 ^ w ∧ xAddr < 2 ^ w ∧ pairsAddr < 2 ^ w ∧ Δ < 2 ^ w ∧ L < 2 ^ w ∧
      b < 2 ^ w ∧ z < 2 ^ w ∧ outAddr < 2 ^ w ∧ h < 2 ^ w :=
    ⟨hwords gAddr (by simp), hwords xAddr (by simp), hwords pairsAddr (by simp),
     hwords Δ (by simp), hwords L (by simp), hwords b (by simp),
     hwords z (by simp), hwords outAddr (by simp), hwords h (by simp)⟩
  have hw_pt : h + 1 + 2 * k + 5 < 2 ^ w := by
    unfold routeOrCutMultiHeapSpace at hw_sp; omega
  -- Stage 0: load k into reg 12, copy h into reg 13
  set st0 := startState [gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h] mem pos
  set st1 : State :=
    { mem := mem, regs := Function.update (Function.update st0.regs 12 k) 13 h, pos := pos }
  have hstage0 : ∃ c0,
      Runs w p ω (seqStmts [.assign 12 (.load (.reg 2)), .assign 13 (.reg 8)]) st0 .normal st1 c0 ∧
      c0 ≤ 15 := by
    have h0 : ∃ o s c0,
        Runs w p ω (seqStmts [.assign 12 (.load (.reg 2)), .assign 13 (.reg 8)]) st0 o s c0 ∧
        (o = .normal ∧ s = st1) ∧ 0 + c0 ≤ 15 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := k) (by simp [st0, startState, Expr.eval, hmp_k]) ?_
      refine runs_assign_le (v := h) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c0, hrun, ⟨rfl, rfl⟩, hc0⟩; exact ⟨c0, hrun, by omega⟩
  rcases hstage0 with ⟨c0, hrun0, hc0⟩
  -- Stage 1: multiPairsToTableStmt builds PairsAt at h
  obtain ⟨o2, st2, c1, hrun1, hpost1, hc1⟩ :=
    multiPairsToTable_triple (w := w) (p := p) hmp hpl_nd hp_h hw_pt (by omega)
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; simp [st0, startState])
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st1]; rw [Function.update_self])
      st1 ω rfl
  cases o2 with
  | returned _ => exact hpost1.elim
  | normal =>
    rcases hpost1 with ⟨hr2_lo, hP2, hPbnd2, hfr2⟩
    -- Stage 2: reg 14 := h + 1 + 2 * k
    set hSub := h + 1 + 2 * k
    set st3 : State := { st2 with regs := Function.update st2.regs 14 hSub }
    have hr2_r : ∀ r ≤ 13, st2.regs r = st1.regs r := hr2_lo
    have hstage2 : ∃ c2,
        Runs w p ω (.assign 14 (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 2) (.reg 12))))
          st2 .normal st3 c2 ∧ c2 ≤ 15 := by
      have hr2_8 : st2.regs 8 = h := by rw [hr2_r 8 (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; simp [st0, startState]
      have hr2_12 : st2.regs 12 = k := by rw [hr2_r 12 (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]
      have h0 : ∃ o s c2,
          Runs w p ω (.assign 14 (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 2) (.reg 12))))
            st2 o s c2 ∧ (o = .normal ∧ s = st3) ∧ 0 + c2 ≤ 15 :=
        runs_assign_le (v := hSub) (by dsimp only [hSub]; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, c2, hrun, ⟨rfl, rfl⟩, hc2⟩; exact ⟨c2, hrun, by omega⟩
    rcases hstage2 with ⟨c2, hrun2, hc2⟩
    -- Stage 3: call routeOrCutPairsProc (base + 12)
    have hcallArgs : evalArgs w st3 [.reg 0, .reg 1, .reg 13, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 14] =
        some [gAddr, xAddr, h, Δ, L, b, z, outAddr, hSub] := by
      have hl : ∀ r ≤ 13, st3.regs r = st1.regs r := fun r hr => by
        dsimp only [st3]; rw [Function.update_of_ne (by omega)]; exact hr2_r r hr
      have h0 : st3.regs 0 = gAddr := by rw [hl 0 (by decide)]; simp [st1, st0, startState]
      have h1 : st3.regs 1 = xAddr := by rw [hl 1 (by decide)]; simp [st1, st0, startState]
      have h13 : st3.regs 13 = h := by rw [hl 13 (by decide)]; simp [st1]
      have h3 : st3.regs 3 = Δ := by rw [hl 3 (by decide)]; simp [st1, st0, startState]
      have h4 : st3.regs 4 = L := by rw [hl 4 (by decide)]; simp [st1, st0, startState]
      have h5 : st3.regs 5 = b := by rw [hl 5 (by decide)]; simp [st1, st0, startState]
      have h6 : st3.regs 6 = z := by rw [hl 6 (by decide)]; simp [st1, st0, startState]
      have h7 : st3.regs 7 = outAddr := by rw [hl 7 (by decide)]; simp [st1, st0, startState]
      have h14 : st3.regs 14 = hSub := by dsimp only [st3]; rw [Function.update_self]
      simp [evalArgs, Expr.eval, h0, h1, h13, h3, h4, h5, h6, h7, h14]
    have hcallW : ∀ v ∈ [gAddr, xAddr, h, Δ, L, b, z, outAddr, hSub], v < 2 ^ w := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hGA2 : GraphAt st3.mem gAddr G :=
      GraphAt.of_agree_below (bound := h) hGA (by unfold Graph.encode; simp; unfold Graph.m at hg_h; omega)
        (fun a ha => hfr2 a (by omega))
    have hX2 : VertSetAt st3.mem xAddr X :=
      VertSetAt.of_agree_below (bound := h) hX_vs (by omega) (fun a ha => hfr2 a (by omega))
    have hzf2 : ZeroFrom st3.mem hSub := fun a ha => by
      rw [show st3.mem a = st2.mem a from rfl, hfr2 a (by omega)]; exact hzf a (by omega)
    have hcallPre : (routeOrCutPairsWithWalksContract w).pre
        [gAddr, xAddr, h, Δ, L, b, z, outAddr, hSub] st3.mem :=
      ⟨gAddr, xAddr, h, Δ, L, b, z, outAddr, hSub, G, X, pairs, rfl, hGA2, hGval, hX2, hX_sub,
        hGloop, hΔ, hdeg, hL, hXL, hb, hP2, hPbnd2, hvtp, hzf2,
        by omega, by omega, by omega,
        by dsimp only [hSub, rcost, pairs, k] at hw_sp ⊢; simp only [List.length_map]; unfold routeOrCutMultiHeapSpace at hw_sp; omega,
        by simpa [pairs, k] using hw_par, hw16⟩
    obtain ⟨st4, c3, vRet, hrun3, hpost3, hr4_15, _, hc3⟩ :=
      runs_call_of_meetsContract (r := 15) hpairsEntryMC hcallArgs hcallW hcallPre ω
    have hpost3' := hpost3 G X pairs hGA2 hGval hX2 hX_sub hP2
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hpost3'
    rcases hpost3' with ⟨hout4, hwalks4, hv_ge4, hv_le4, hzf4, hfr4⟩
    -- Stage 4: ret (reg 15)
    obtain ⟨cRet, hrunRet, hcRet⟩ :
        ∃ cRet, Runs w p ω (.ret (.reg 15)) st4 (.returned vRet) st4 cRet ∧ cRet ≤ 5 := by
      have h0 : ∃ o s cRet, Runs w p ω (.ret (.reg 15)) st4 o s cRet ∧
          (o = .returned vRet ∧ s = st4) ∧ 0 + cRet ≤ 5 :=
        runs_ret_le (v := vRet) (by simp [Expr.eval, hr4_15]) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, cRet, hrun, ⟨rfl, rfl⟩, hcRet⟩; exact ⟨cRet, hrun, by omega⟩
    -- Assemble full run of `routeOrCutMultiProc`
    have hrun_tail : Runs w p ω
        (seqStmts
          [ multiPairsToTableStmt
          , .assign 14 (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 2) (.reg 12)))
          , .call 15 (base + routerPairsEntryOff)
              [.reg 0, .reg 1, .reg 13, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 14]
          , .ret (.reg 15) ])
        st1 (.returned vRet) st4 (c1 + (c2 + (c3 + cRet + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st2, c1, _, hrun1,
        runs_seq_iff.mpr (Or.inr ⟨st3, c2, _, hrun2,
          runs_seq_iff.mpr (Or.inr ⟨st4, c3, cRet, hrun3, hrunRet, rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun0 hrun_tail
    have hreadG : readGraph mem gAddr = G := readGraph_eq_of_graphAt hGA
    have hreadX : (readLenPrefixedList mem xAddr).toFinset = X := by
      unfold readLenPrefixedList; rw [hX_at.1, readList_eq_of_listAt hX_at.2]
    have hreadP : readMultiPairs mem pairsAddr = pairs := readMultiPairs_eq_of_multiPairsAt hmp
    refine ⟨routeOrCutMultiProc (base + routerPairsEntryOff), hp13, .returned vRet, st4, cAll, hrunAll, ?_, ?_⟩
    · dsimp only [routeOrCutMultiWithWalksContract, Outcome.value, List.getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [hreadG, hreadX, hreadP]
      refine ⟨hout4, ?_, by dsimp only [hSub] at hv_ge4; simp only [pairs, List.length_map]; omega,
        by dsimp only [hSub, routeOrCutMultiHeapSpace] at hv_le4 ⊢; simp only [pairs, List.length_map] at hv_le4 ⊢; omega,
        hzf4, fun a ha hout => (hfr4 a (by omega) hout).trans (hfr2 a (by omega))⟩
      cases hres : routeOrCut G X pairs Δ L b z with
      | cut _ => trivial
      | matched matchings emb =>
        rw [hres] at hwalks4
        refine ⟨by simpa [hSub, pairs, k] using hwalks4.1, fun idx hidx => ?_⟩
        have hbnd := hwalks4.2 idx hidx
        simp only [hSub, pairs, k, List.length_map] at hbnd ⊢
        exact ⟨by omega, hbnd.2⟩
    · dsimp only [routeOrCutMultiWithWalksContract, List.getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some]
      rw [hreadG, hreadX, hreadP]
      dsimp only [routeOrCutPairsWithWalksContract, List.getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at hc3
      have hG3_read : readGraph st3.mem gAddr = G := readGraph_eq_of_graphAt hGA2
      have hX3_read : (readLenPrefixedList st3.mem xAddr).toFinset = X := by
        rcases hX2 with ⟨xs, _, hfin, hseq⟩
        unfold readLenPrefixedList; rw [hseq.1, readList_eq_of_listAt hseq.2, hfin]
      have hGm3 : st3.mem (gAddr + 1) = G.m := graphAt_m hGA2
      have hXn3 : st3.mem xAddr = X.card := by
        rw [show st3.mem xAddr = st2.mem xAddr from rfl, hfr2 xAddr (by omega)]
        dsimp only [st1]; rw [hX_at.1, hX_len]
      have hPk3 : st3.mem h = pairs.length := hP2.1
      have hP3_read : (List.ofFn fun i : Fin (st3.mem h) =>
          ((readLenPrefixedList st3.mem (st3.mem (h + 1 + 2 * i.1))).toFinset,
           (readLenPrefixedList st3.mem (st3.mem (h + 2 + 2 * i.1))).toFinset)) = pairs := by
        apply List.ext_getElem (by simp [hPk3])
        intro i hi _
        have hi' : i < pairs.length := by simpa [hPk3] using hi
        simp only [List.getElem_ofFn]
        have hpi := hP2.2 i hi'
        rcases hpi.1 with ⟨xs1, _, hf1, hs1⟩
        rcases hpi.2 with ⟨xs2, _, hf2, hs2⟩
        exact Prod.ext
          (by unfold readLenPrefixedList; rw [hs1.1, readList_eq_of_listAt hs1.2, hf1])
          (by unfold readLenPrefixedList; rw [hs2.1, readList_eq_of_listAt hs2.2, hf2])
      rw [hG3_read, hX3_read, hP3_read, hGm3, hXn3, hPk3] at hc3
      dsimp only [routeOrCutMultiTotalCost, routeOrCutMultiSetupCost, routeOrCutPairsTotalCost,
        routeOrCutPairsSetupCost, argsSize, Expr.size, List.length_cons, List.length_nil] at hc0 hc1 hc2 hc3 hcRet hcAll ⊢
      simp only [pairs, List.length_map] at hc3 ⊢
      omega

/-- Standalone deterministic program `routeOrCutProgram` meets `routeOrCutPairsWithWalksContract`
at entry `routerPairsEntryOff = 12`. -/
theorem routeOrCutProgram_pairs_meetsContract (w : ℕ) :
    MeetsContract w routeOrCutProgram routerPairsEntryOff (routeOrCutPairsWithWalksContract w) := by
  simpa [routeOrCutProgram, routerPairsEntryOff] using
    routeOrCutPairs_meetsContract (w := w) (base := 0) (p := routeOrCutProgram)
      (fun i hi => by simp [routeOrCutProgram, hi])

/-- Standalone deterministic program `routeOrCutProgram` meets `routeOrCutMultiWithWalksContract`
at entry `routerMultiEntryOff = 13`. -/
theorem routeOrCutProgram_multi_meetsContract (w : ℕ) :
    MeetsContract w routeOrCutProgram routerMultiEntryOff (routeOrCutMultiWithWalksContract w) := by
  simpa [routeOrCutProgram, routerMultiEntryOff] using
    routeOrCutMulti_meetsContract (w := w) (base := 0) (p := routeOrCutProgram)
      (fun i hi => by simp [routeOrCutProgram, hi])

/-! ## 3. Bridge Theorems to `multiPairRouterContract` and `routeOrCutContract` -/

/-- Exact postcondition implication: `routeOrCutMultiWithWalksContract` postcondition (with walks
and sorted cut) immediately implies `multiPairRouterContract` postcondition (dropping
walks via `RouteOutSortedAt.toRouteOutAt`) whenever the heap-space bound fits in `outerRouterSpace`. -/
theorem routeOrCutMultiWithWalks_post_implies_multiPairRouter_post
    {C_rt C_sp w : ℕ} {args : List ℕ} {mem mem' : ℕ → ℕ} {v : ℕ}
    (hpost : (routeOrCutMultiWithWalksContract w).post args mem v mem')
    (hsp :
      let G := readGraph mem (args.getD 0 0)
      let X := (readLenPrefixedList mem (args.getD 1 0)).toFinset
      let pairs := readMultiPairs mem (args.getD 2 0)
      let rcost := routeOrCutCost G X pairs (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
      routeOrCutMultiHeapSpace G.n G.m X.card pairs.length rcost ≤
        outerRouterSpace C_sp G.n (routerCallCost G X pairs (args.getD 3 0) (args.getD 4 0)
          (args.getD 5 0) (args.getD 6 0))) :
    (multiPairRouterContract C_rt C_sp w).post args mem v mem' := by
  rcases hpost with ⟨hout, _, hv_ge, hv_le, hzf, hfr⟩
  exact ⟨hout.toRouteOutAt, by omega, le_trans hv_le (Nat.add_le_add_left hsp _), hzf, hfr⟩

/-- Any procedure meeting `routeOrCutMultiWithWalksContract w` satisfies
`multiPairRouterContract C_rt C_sp w` on every input where the setup-cost, bump-heap space, and
parameter word-size bounds fit inside `C_rt`, `C_sp`, and `2 ^ w`. -/
theorem routeOrCutMultiWithWalks_implies_multiPairRouter_of_bounds
    {w f C_rt C_sp : ℕ} {p : Program}
    (hMC : MeetsContract w p f (routeOrCutMultiWithWalksContract w))
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w)
    (hpre : (multiPairRouterContract C_rt C_sp w).pre args mem)
    (hcost_fit :
      let G := readGraph mem (args.getD 0 0)
      let X := (readLenPrefixedList mem (args.getD 1 0)).toFinset
      let pairs := readMultiPairs mem (args.getD 2 0)
      let rcost := routeOrCutCost G X pairs (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
      routeOrCutMultiTotalCost G.m X.card pairs.length rcost ≤
        C_rt * routerCallCost G X pairs (args.getD 3 0) (args.getD 4 0) (args.getD 5 0)
          (args.getD 6 0) + C_rt)
    (hsp_fit :
      let G := readGraph mem (args.getD 0 0)
      let X := (readLenPrefixedList mem (args.getD 1 0)).toFinset
      let pairs := readMultiPairs mem (args.getD 2 0)
      let rcost := routeOrCutCost G X pairs (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
      routeOrCutMultiHeapSpace G.n G.m X.card pairs.length rcost ≤
        outerRouterSpace C_sp G.n (routerCallCost G X pairs (args.getD 3 0) (args.getD 4 0)
          (args.getD 5 0) (args.getD 6 0)))
    (hw_fit :
      let G := readGraph mem (args.getD 0 0)
      let X := (readLenPrefixedList mem (args.getD 1 0)).toFinset
      let pairs := readMultiPairs mem (args.getD 2 0)
      let rcost := routeOrCutCost G X pairs (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
      args.getD 8 0 + routeOrCutMultiHeapSpace G.n G.m X.card pairs.length rcost + 16 < 2 ^ w ∧
      routeOrCutParamBound G.m X.card pairs.length (args.getD 3 0) (args.getD 4 0)
        (args.getD 5 0) (args.getD 6 0) < 2 ^ w) :
    EndsAsContract w p f (multiPairRouterContract C_rt C_sp w) args mem pos ω := by
  rcases hpre with ⟨gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr, G, X_list, pairLists,
    rfl, hGA, hGval, hX_at, hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hmp, hpl_nd, hvtp,
    hzf, hg_h, hx_h, hp_h, hout_h, _, _, _, _, hw16, _, _⟩
  have hreadG : readGraph mem gAddr = G := readGraph_eq_of_graphAt hGA
  have hreadX : (readLenPrefixedList mem xAddr).toFinset = X_list.toFinset := by
    unfold readLenPrefixedList; rw [hX_at.1, readList_eq_of_listAt hX_at.2]
  have hreadP : readMultiPairs mem pairsAddr = pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset) :=
    readMultiPairs_eq_of_multiPairsAt hmp
  simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, hreadP, List.length_map] at hw_fit
  have hpreW : (routeOrCutMultiWithWalksContract w).pre
      [gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr] mem :=
    ⟨gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr, G, X_list, pairLists,
      rfl, hGA, hGval, hX_at, hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hmp, hpl_nd, hvtp,
      hzf, hg_h, hx_h, hp_h, hout_h, hw_fit.1, hw_fit.2, hw16⟩
  obtain ⟨body, hbody, o, st', c, hrun, hpostW, hcostW⟩ := hMC _ mem pos ω hwords hpreW
  refine ⟨body, hbody, o, st', c, hrun,
    routeOrCutMultiWithWalks_post_implies_multiPairRouter_post hpostW hsp_fit,
    le_trans hcostW hcost_fit⟩

/-- Single-pair specialization: any procedure meeting `routeOrCutMultiWithWalksContract w`
satisfies `routeOrCutContract C_rt C_sp w` (`OuterProgContracts.lean`) under the same
setup-cost, heap-space, and parameter word-size bounds. -/
theorem routeOrCutMultiWithWalks_implies_routeOrCut_of_bounds
    {w f C_rt C_sp : ℕ} {p : Program}
    (hMC : MeetsContract w p f (routeOrCutMultiWithWalksContract w))
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w)
    (hpre : (routeOrCutContract C_rt C_sp w).pre args mem)
    (hcost_fit :
      let G := readGraph mem (args.getD 0 0)
      let X := (readLenPrefixedList mem (args.getD 1 0)).toFinset
      let pair := readSinglePair mem (args.getD 2 0)
      let rcost := routeOrCutCost G X [pair] (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
      routeOrCutMultiTotalCost G.m X.card 1 rcost ≤
        C_rt * routerCallCost G X [pair] (args.getD 3 0) (args.getD 4 0) (args.getD 5 0)
          (args.getD 6 0) + C_rt)
    (hsp_fit :
      let G := readGraph mem (args.getD 0 0)
      let X := (readLenPrefixedList mem (args.getD 1 0)).toFinset
      let pair := readSinglePair mem (args.getD 2 0)
      let rcost := routeOrCutCost G X [pair] (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
      routeOrCutMultiHeapSpace G.n G.m X.card 1 rcost ≤
        outerRouterSpace C_sp G.n (routerCallCost G X [pair] (args.getD 3 0) (args.getD 4 0)
          (args.getD 5 0) (args.getD 6 0)))
    (hw_fit :
      let G := readGraph mem (args.getD 0 0)
      let X := (readLenPrefixedList mem (args.getD 1 0)).toFinset
      let pair := readSinglePair mem (args.getD 2 0)
      let rcost := routeOrCutCost G X [pair] (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
      args.getD 8 0 + routeOrCutMultiHeapSpace G.n G.m X.card 1 rcost + 16 < 2 ^ w ∧
      routeOrCutParamBound G.m X.card 1 (args.getD 3 0) (args.getD 4 0)
        (args.getD 5 0) (args.getD 6 0) < 2 ^ w) :
    EndsAsContract w p f (routeOrCutContract C_rt C_sp w) args mem pos ω := by
  rcases hpre with ⟨gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr, G, X_list, A_list, B_list,
    rfl, hGA, hGval, hX_at, hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hsp, hAnd, hBnd, hvtp,
    hzf, hg_h, hx_h, hp_h, hout_h, hdg, hdx, hdp, hsp_w, hw16, hGm, hzv⟩
  have hmp : MultiPairsAt mem pairsAddr [(A_list, B_list)] := singlePairAt_iff_multiPairsAt.mp hsp
  have hlen_p : (encodePairs [(A_list, B_list)]).length = 3 + A_list.length + B_list.length :=
    encodePairs_singleton_length A_list B_list
  have hread_eq : readMultiPairs mem pairsAddr = [readSinglePair mem pairsAddr] := by
    rw [readMultiPairs_eq_of_multiPairsAt hmp, readSinglePair_eq_of_singlePairAt hsp]; rfl
  have hpre_m : (multiPairRouterContract C_rt C_sp w).pre
      [gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr] mem :=
    ⟨gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr, G, X_list, [(A_list, B_list)],
      rfl, hGA, hGval, hX_at, hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hmp,
      by simp [hAnd, hBnd], by simpa using hvtp, hzf, hg_h, hx_h, by omega, hout_h,
      hdg, hdx, by rcases hdp with h1 | h1 <;> [left; right] <;> omega, by simpa using hsp_w, hw16, hGm, hzv⟩
  have hfit_c :
      let G' := readGraph mem gAddr
      let X' := (readLenPrefixedList mem xAddr).toFinset
      let ps' := readMultiPairs mem pairsAddr
      let rc' := routeOrCutCost G' X' ps' Δ L b z
      routeOrCutMultiTotalCost G'.m X'.card ps'.length rc' ≤
        C_rt * routerCallCost G' X' ps' Δ L b z + C_rt := by
    simpa only [List.getD_cons_zero, List.getD_cons_succ, hread_eq, List.length_singleton] using hcost_fit
  have hfit_s :
      let G' := readGraph mem gAddr
      let X' := (readLenPrefixedList mem xAddr).toFinset
      let ps' := readMultiPairs mem pairsAddr
      let rc' := routeOrCutCost G' X' ps' Δ L b z
      routeOrCutMultiHeapSpace G'.n G'.m X'.card ps'.length rc' ≤
        outerRouterSpace C_sp G'.n (routerCallCost G' X' ps' Δ L b z) := by
    simpa only [List.getD_cons_zero, List.getD_cons_succ, hread_eq, List.length_singleton] using hsp_fit
  have hfit_w :
      let G' := readGraph mem gAddr
      let X' := (readLenPrefixedList mem xAddr).toFinset
      let ps' := readMultiPairs mem pairsAddr
      let rc' := routeOrCutCost G' X' ps' Δ L b z
      h_ptr + routeOrCutMultiHeapSpace G'.n G'.m X'.card ps'.length rc' + 16 < 2 ^ w ∧
      routeOrCutParamBound G'.m X'.card ps'.length Δ L b z < 2 ^ w := by
    simpa only [List.getD_cons_zero, List.getD_cons_succ, hread_eq, List.length_singleton] using hw_fit
  obtain ⟨body, hbody, o, st', c, hrun, hpost_m, hcost_m⟩ :=
    routeOrCutMultiWithWalks_implies_multiPairRouter_of_bounds hMC ω hwords hpre_m hfit_c hfit_s hfit_w
  refine ⟨body, hbody, o, st', c, hrun, ?_, ?_⟩
  · simpa only [routeOrCutContract, outerRouterContract, multiPairRouterContract,
      List.getD_cons_zero, List.getD_cons_succ, hread_eq] using hpost_m
  · simpa only [routeOrCutContract, outerRouterContract, multiPairRouterContract,
      List.getD_cons_zero, List.getD_cons_succ, hread_eq] using hcost_m

/-! ## 4. Non-Vacuity Witnesses -/

/-- Non-vacuity witness showing all preconditions of `routeOrCutMultiWithWalksContract 40` hold
simultaneously on a concrete 2-vertex, 1-edge graph with 1 terminal pair. -/
theorem routeOrCutMultiWithWalksContract_pre_example :
    ∃ args mem,
      (∀ a ∈ args, a < 2 ^ 40) ∧
      (routeOrCutMultiWithWalksContract 40).pre args mem := by
  let G : Graph := ⟨2, [(0, 1)]⟩
  let X_list : List ℕ := [0, 1]
  let pairLists : List (List ℕ × List ℕ) := [([0], [1])]
  -- Layout: G at 0..3 ([2, 1, 0, 1]), X at 4..6 ([2, 0, 1]), pairs at 7..11 ([1, 1, 0, 1, 1]),
  -- out at 12..17 (6 words), heap h = 20
  let mem : ℕ → ℕ := fun a =>
    match a with
    | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 1
    | 4 => 2 | 5 => 0 | 6 => 1
    | 7 => 1 | 8 => 1 | 9 => 0 | 10 => 1 | 11 => 1
    | _ => 0
  refine ⟨[0, 4, 7, 1, 2, 2, 0, 12, 20], mem, by decide, ?_⟩
  refine ⟨0, 4, 7, 1, 2, 2, 0, 12, 20, G, X_list, pairLists, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    by decide, ?_, by decide, ?_, by decide, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, ?_, ?_, by decide⟩
  · -- GraphAt mem 0 G
    intro i hi
    have : i < 4 := by simpa [G, Graph.encode] using hi
    interval_cases i <;> rfl
  · -- G.IsValid
    intro e he; simp only [G, List.mem_singleton] at he; subst he; decide
  · -- LenListAt mem 4 X_list
    refine ⟨rfl, fun i hi => ?_⟩
    have : i < 2 := hi; interval_cases i <;> rfl
  · decide
  · decide
  · intro e he
    have : e ∈ G.edges := (List.mem_filter.mp he).1
    simp only [G, List.mem_singleton] at this; subst this; decide
  · intro v hv
    have : v = 0 ∨ v = 1 := by simpa [X_list] using hv
    rcases this with rfl | rfl <;> decide
  · decide
  · -- MultiPairsAt mem 7 pairLists
    intro i hi
    have : i < 5 := by simpa [pairLists, encodePairs, encodePair] using hi
    interval_cases i <;> rfl
  · decide
  · -- ValidTerminalPairs
    refine ⟨by intro p hp; simp only [pairLists, List.map_cons, List.map_nil, List.mem_singleton] at hp; subst hp; decide,
      by simp only [pairLists, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]; decide⟩
  · -- ZeroFrom mem 20
    intro a ha
    have : a ≥ 12 := by omega
    match a, this with
    | n + 12, _ => rfl
  · -- Heap space < 2 ^ 40 (using routeOrCutCost_le upper bound)
    have hdeg_ex : ∀ v ∈ X_list.toFinset, G.degIn X_list.toFinset v ≤ 1 := by
      intro v hv; have : v = 0 ∨ v = 1 := by simpa [X_list] using hv
      rcases this with rfl | rfl <;> decide
    have hvtp_ex : ValidTerminalPairs X_list.toFinset
        (pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset)) :=
      ⟨by intro p hp; simp only [pairLists, List.map_cons, List.map_nil, List.mem_singleton] at hp; subst hp; decide,
       by simp only [pairLists, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]; decide⟩
    have hrc : routeOrCutCost G X_list.toFinset
        (pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset)) 1 2 2 0 ≤
        20 * 1 * (2 + 1 + 1) * (routeD 1 2 2 + 1) * routeR 1 2 2 := by
      have h1 := routeOrCutCost_le G (X := X_list.toFinset)
        (pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset))
        (routeTerminalPairs_of_validTerminalPairs hvtp_ex) (Δ := 1) (L := 2) (b := 2) (z := 0)
        (by decide) (by decide) (by decide) hdeg_ex
      have hcard : X_list.toFinset.card = 2 := by decide
      have hins : (G.inside X_list.toFinset).length = 1 := by decide
      simpa [pairLists, hcard, hins, routeCostConst] using h1
    have hcard : X_list.toFinset.card = 2 := by decide
    dsimp only [G, Graph.m, pairLists, List.length_cons, List.length_nil] at hrc ⊢
    rw [hcard]
    unfold routeOrCutMultiHeapSpace routeOrCutPairsHeapSpace localCsrSpace localPairsSpace batchScratchSize
    unfold routeD routeR routeCong routeBatchH routePathLen at hrc
    omega
  · -- Parameter bound < 2 ^ 40
    have hcard : X_list.toFinset.card = 2 := by decide
    rw [hcard]
    unfold routeOrCutParamBound routeD routePathLen routeR routeCong routeHBatch routeBatchH
    decide

/-- Non-vacuity witness showing all preconditions of `routeOrCutPairsWithWalksContract 40` hold
simultaneously on the same concrete 2-vertex, 1-edge graph with 1 terminal pair. -/
theorem routeOrCutPairsWithWalksContract_pre_example :
    ∃ args mem,
      (∀ a ∈ args, a < 2 ^ 40) ∧
      (routeOrCutPairsWithWalksContract 40).pre args mem := by
  let G : Graph := ⟨2, [(0, 1)]⟩
  let X : Finset ℕ := {0, 1}
  let pairs : List (Finset ℕ × Finset ℕ) := [({0}, {1})]
  -- Layout: G at 0..3, X at 4..6, A_0 at 7..8 ([1, 0]), B_0 at 9..10 ([1, 1]),
  -- pTable at 11..13 ([1, 7, 9]), out at 14..19, heap h = 20
  let mem : ℕ → ℕ := fun a =>
    match a with
    | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 1
    | 4 => 2 | 5 => 0 | 6 => 1
    | 7 => 1 | 8 => 0 | 9 => 1 | 10 => 1
    | 11 => 1 | 12 => 7 | 13 => 9
    | _ => 0
  refine ⟨[0, 4, 11, 1, 2, 2, 0, 14, 20], mem, by decide, ?_⟩
  refine ⟨0, 4, 11, 1, 2, 2, 0, 14, 20, G, X, pairs, rfl, ?_, ?_, ?_, by decide, ?_,
    by decide, ?_, by decide, by decide, by decide, ?_, ?_, ?_, ?_, by decide, by decide,
    by decide, ?_, ?_, by decide⟩
  · intro i hi; have : i < 4 := by simpa [G, Graph.encode] using hi
    interval_cases i <;> rfl
  · intro e he; simp only [G, List.mem_singleton] at he; subst he; decide
  · refine ⟨[0, 1], by decide, by decide, rfl, fun i hi => ?_⟩
    have : i < 2 := hi; interval_cases i <;> rfl
  · intro e he; have : e ∈ G.edges := (List.mem_filter.mp he).1
    simp only [G, List.mem_singleton] at this; subst this; decide
  · intro v hv
    have : v = 0 ∨ v = 1 := by simpa [X] using hv
    rcases this with rfl | rfl <;> decide
  · refine ⟨rfl, fun i hi => ?_⟩
    have hi0 : i = 0 := by simpa [pairs] using hi
    subst hi0
    simp only [pairs, List.getElem_cons_zero]
    exact ⟨⟨[0], by decide, by decide, rfl, fun j hj => by have hj0 : j = 0 := (by simpa using hj); subst hj0; rfl⟩,
      ⟨[1], by decide, by decide, rfl, fun j hj => by have hj0 : j = 0 := (by simpa using hj); subst hj0; rfl⟩⟩
  · refine ⟨by decide, fun i hi => ?_⟩
    have hi0 : i = 0 := by simpa [pairs] using hi
    subst hi0
    simp only [pairs, List.getElem_cons_zero]; decide
  · refine ⟨by intro p hp; simp only [pairs, List.mem_singleton] at hp; subst hp; decide,
      by simp only [pairs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; decide⟩
  · intro a ha
    have : a ≥ 14 := by omega
    match a, this with
    | n + 14, _ => rfl
  · have hdeg_ex : ∀ v ∈ X, G.degIn X v ≤ 1 := by
      intro v hv; have : v = 0 ∨ v = 1 := by simpa [X] using hv
      rcases this with rfl | rfl <;> decide
    have hvtp_ex : ValidTerminalPairs X pairs :=
      ⟨by intro p hp; simp only [pairs, List.mem_singleton] at hp; subst hp; decide,
       by simp only [pairs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; decide⟩
    have hrc : routeOrCutCost G X pairs 1 2 2 0 ≤
        20 * 1 * (2 + 1 + 1) * (routeD 1 2 2 + 1) * routeR 1 2 2 := by
      have h1 := routeOrCutCost_le G (X := X) pairs
        (routeTerminalPairs_of_validTerminalPairs hvtp_ex) (Δ := 1) (L := 2) (b := 2) (z := 0)
        (by decide) (by decide) (by decide) hdeg_ex
      have hcard : X.card = 2 := by decide
      have hins : (G.inside X).length = 1 := by decide
      simpa [pairs, hcard, hins, routeCostConst] using h1
    have hcard : X.card = 2 := by decide
    dsimp only [G, Graph.m, pairs, List.length_cons, List.length_nil] at hrc ⊢
    rw [hcard]
    unfold routeOrCutPairsHeapSpace localCsrSpace localPairsSpace batchScratchSize
    unfold routeD routeR routeCong routeBatchH routePathLen at hrc
    omega
  · have hcard : X.card = 2 := by decide
    rw [hcard]
    unfold routeOrCutParamBound routeD routePathLen routeR routeCong routeHBatch routeBatchH
    decide

end MinCostFlow.ExpanderDecomp
