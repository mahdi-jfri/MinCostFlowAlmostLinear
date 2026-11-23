module

public import MinCostFlow.ExpanderDecomp.RouteProg
public import MinCostFlow.ExpanderDecomp.Used
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The router program meets the router contract of the Core

This file turns the router program of `RouteProg*.lean` into a `MultiPairRouterModule`, the
router that the expander decomposition program of `Used.lean` needs.

The router contract `multiPairRouterContract` (`ProgStepCSpec.lean`) charges
`C_rt * routerCallCost … + C_rt`. With no terminal pairs this is the constant `C_rt`, so the
program must stop at once. The entry procedure `routeOrCutEntryProc` reads the number of pairs.
If it is `0`, it writes the empty matching and returns. Otherwise it calls the flat entry
`routeOrCutMultiProc` of `routerProcs`, whose contract `routeOrCutMultiWithWalksContract`
(`RouteProg.lean`) costs `routeOrCutMultiTotalCost` and uses `routeOrCutMultiHeapSpace` words.

The work is in three bounds, each for at least one pair and a graph with at most `2 Δ |X|` edges:
* `routeOrCutMultiTotalCost_fit`: the setup cost of the program (reading the graph, sorting `X`,
  reading the pairs) is at most `5000` times the call cost `routerCallCost`;
* `routeOrCutMultiHeapSpace_fit`: its heap use fits in `outerRouterSpace 200`;
* `routeOrCutParamBound_fit`: the largest number it stores is at most `routeCallOverhead`, so
  the word-size condition of the contract also bounds it.

Main results:
* `routeOrCutEntry_meetsContract`: the entry procedure meets `multiPairRouterContract 5000 200 w`;
* `routeOrCutRouterModule : MultiPairRouterModule`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. The three bounds -/

/-- The overhead for at least one pair, as an explicit sum. -/
lemma routeCallOverhead_of_pos {nX k Δ L b : ℕ} (hk : 1 ≤ k) :
    routeCallOverhead nX k Δ L b =
      routeCong Δ b L * (k * (routePathLen Δ b L + 3) + 1) +
        (nX + 1) * (routeBatchH Δ b L + Δ + L + 2) + routePathLen Δ b L +
        16 * b * (4 * Δ * nX + Δ + 1) + k + 32 := by
  have hk0 : k ≠ 0 := by omega
  simp only [routeCallOverhead, hk0, ↓reduceIte]

/-- Two lower bounds on the overhead used below: it is at least `(|X| + 1)(Δ + L + 2) + k + 32`. -/
lemma routeCallOverhead_ge {nX k Δ L b : ℕ} (hk : 1 ≤ k) :
    (nX + 1) * (Δ + L + 2) + k + 32 ≤ routeCallOverhead nX k Δ L b := by
  rw [routeCallOverhead_of_pos hk]
  have h1 : (nX + 1) * (Δ + L + 2) ≤ (nX + 1) * (routeBatchH Δ b L + Δ + L + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- `log₂ (|X| + 2) ≤ L` when `|X| < 2^L` and `1 ≤ L`. -/
lemma log_two_add_two_le {nX L : ℕ} (hL : 1 ≤ L) (hXL : nX < 2 ^ L) :
    Nat.log 2 (nX + 2) ≤ L := by
  have hpow : nX + 2 < 2 ^ (L + 1) := by
    have h2 : 2 ≤ 2 ^ L := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
    rw [pow_succ]; omega
  have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hpow
  omega

/-- **Setup cost fits the call cost.** -/
lemma routeOrCutMultiTotalCost_fit {m nX k Δ L b rcost : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hXL : nX < 2 ^ L) (hm : m ≤ 2 * Δ * nX) :
    routeOrCutMultiTotalCost m nX k rcost + 20 ≤
      5000 * (rcost + routeCallOverhead nX k Δ L b) := by
  have hO := routeCallOverhead_ge (nX := nX) (Δ := Δ) (L := L) (b := b) hk
  set O := routeCallOverhead nX k Δ L b
  set A := (nX + 1) * (Δ + L + 2) with hA
  have hlog := log_two_add_two_le hL hXL
  have hnL : nX * (2 * Nat.log 2 (nX + 2) + 1) ≤ 2 * A := by
    have h1 : nX * (2 * Nat.log 2 (nX + 2) + 1) ≤ (nX + 1) * (2 * (Δ + L + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (nX + 1) * (2 * (Δ + L + 2)) = 2 * A := by rw [hA]; ring
    omega
  have hΔn : Δ * nX ≤ A := by
    rw [hA, Nat.mul_comm Δ nX]; exact Nat.mul_le_mul (by omega) (by omega)
  have hm' : m ≤ 2 * A := by
    have : 2 * Δ * nX = 2 * (Δ * nX) := by ring
    omega
  have hnA : nX ≤ A := by
    rw [hA]
    have : nX + 1 ≤ (nX + 1) * (Δ + L + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  unfold routeOrCutMultiTotalCost routeCsrProgCost routeOrCutMultiSetupCost
    routeOrCutPairsSetupCost buildLocalCsrCost buildLocalPairsCost
  omega

/-- **Heap use fits the space of the call.** -/
lemma routeOrCutMultiHeapSpace_fit {n m nX k Δ L b rcost : ℕ} (hk : 1 ≤ k)
    (hm : m ≤ 2 * Δ * nX) :
    routeOrCutMultiHeapSpace n m nX k rcost + 16 ≤
      outerRouterSpace 200 n (rcost + routeCallOverhead nX k Δ L b) := by
  have hO := routeCallOverhead_ge (nX := nX) (Δ := Δ) (L := L) (b := b) hk
  set O := routeCallOverhead nX k Δ L b
  set A := (nX + 1) * (Δ + L + 2) with hA
  have hΔn : Δ * nX ≤ A := by
    rw [hA, Nat.mul_comm Δ nX]; exact Nat.mul_le_mul (by omega) (by omega)
  have hm' : m ≤ 2 * A := by
    have : 2 * Δ * nX = 2 * (Δ * nX) := by ring
    omega
  have hnA : nX ≤ A := by
    rw [hA]
    have : nX + 1 ≤ (nX + 1) * (Δ + L + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hn : n ≤ (n + 3) ^ 4 := le_trans (Nat.le_add_right n 3) (Nat.le_self_pow (by norm_num) _)
  unfold routeOrCutMultiHeapSpace routeOrCutPairsHeapSpace localCsrSpace localPairsSpace
    batchScratchSize outerRouterSpace
  omega

/-- **The numbers the router stores are bounded by the overhead.** -/
lemma routeOrCutParamBound_fit {m nX k Δ L b z : ℕ} (hk : 1 ≤ k)
    (hm : m ≤ 2 * Δ * nX) (hz : z ≤ nX) :
    routeOrCutParamBound m nX k Δ L b z ≤ routeCallOverhead nX k Δ L b := by
  rw [routeCallOverhead_of_pos hk]
  unfold routeOrCutParamBound
  have h1 : 16 * b * (2 * m + Δ + 1) ≤ 16 * b * (4 * Δ * nX + Δ + 1) :=
    Nat.mul_le_mul_left _ (by
      have : 4 * Δ * nX = 2 * (2 * Δ * nX) := by ring
      omega)
  have h2 : (nX + 1) * (routeBatchH Δ b L + Δ + L + 2) =
      (nX + 1) * routeBatchH Δ b L + (nX + 1) * (Δ + L + 2) := by ring
  have h3 : nX ≤ (nX + 1) * (Δ + L + 2) := by
    have : nX + 1 ≤ (nX + 1) * (Δ + L + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  simp only [routeD, routeHBatch, routeR]
  omega

/-! ## 2. The entry procedure -/

/-- Entry procedure on `[gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h]`: with no terminal
pairs it writes the empty matching (tag `0`, length `0`) and returns `h`; otherwise it calls the
flat router entry `bMulti` with the same arguments. -/
def routeOrCutEntryProc (bMulti : ℕ) : Stmt :=
  .cond (.bin .eq (.load (.reg 2)) (.const 0))
    (seqStmts [.store (.reg 7) (.const 0), .store (.bin .add (.reg 7) (.const 1)) (.const 0),
      .ret (.reg 8)])
    (seqStmts [.call 9 bMulti [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8],
      .ret (.reg 9)])

theorem routeOrCutEntryProc_noRand (bMulti : ℕ) : (routeOrCutEntryProc bMulti).NoRand := by
  simp [routeOrCutEntryProc, seqStmts, Stmt.NoRand]

/-- The router procedures followed by the entry procedure at `base + 14`. -/
def routerModuleProcs (base : ℕ) : List Stmt :=
  routerProcs base ++ [routeOrCutEntryProc (base + routerMultiEntryOff)]

/-- Offset of the entry procedure in `routerModuleProcs`. -/
def routerEntryOff : ℕ := 14

theorem routerModuleProcs_noRand (base : ℕ) : ∀ s ∈ routerModuleProcs base, Stmt.NoRand s := by
  intro s hs
  simp only [routerModuleProcs, List.mem_append, List.mem_singleton] at hs
  rcases hs with hs | rfl
  · exact routerProcs_noRand base s hs
  · exact routeOrCutEntryProc_noRand _

lemma routerProcs_length (base : ℕ) : (routerProcs base).length = 14 := rfl

/-! ## 3. The contract proof -/

/-- **The entry procedure meets the router contract of the Core**, with `C_rt = 5000` and
`C_sp = 200`, for every placement `base` and word size `w`. -/
theorem routeOrCutEntry_meetsContract {w base : ℕ} {p : Program}
    (hp : p.HasAt base (routerModuleProcs base)) :
    MeetsContract w p (base + routerEntryOff) (multiPairRouterContract 5000 200 w) := by
  have hpR : p.HasAt base (routerProcs base) := fun i hi => by
    have h := hp i (by simp only [routerModuleProcs, List.length_append, List.length_singleton]; omega)
    rw [h]; simp [routerModuleProcs, List.getElem_append_left hi]
  have hp14 : p.procs[base + routerEntryOff]? =
      some (routeOrCutEntryProc (base + routerMultiEntryOff)) := by
    have h := hp 14 (by simp [routerModuleProcs, routerProcs_length])
    rw [show base + routerEntryOff = base + 14 from rfl, h]
    simp [routerModuleProcs, routerProcs]
  have hMulti := routeOrCutMulti_meetsContract (w := w) hpR
  refine meetsContract_of_runs hp14 fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨gA, xA, pA, Δ, L, b, z, oA, h0, G, X_list, pairLists, rfl, hGA, hGval, hX_at,
    hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hmp, hpl_nd, hvtp, hzf, hg_h, hx_h, hp_h,
    hout_h, hd1, hd2, hd3, hsp_w, hw16, hGm, hzv⟩
  have hreadG : readGraph mem gA = G := readGraph_eq_of_graphAt hGA
  have hreadX : (readLenPrefixedList mem xA).toFinset = X_list.toFinset := by
    rw [readLenPrefixedList_eq_of_lenListAt hX_at]
  have hreadP : readMultiPairs mem pA = pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset) :=
    readMultiPairs_eq_of_multiPairsAt hmp
  have hcard : X_list.toFinset.card = X_list.length := List.toFinset_card_of_nodup hX_nd
  have hk_mem : mem pA = pairLists.length := by
    have h := hmp; unfold MultiPairsAt encodePairs at h; exact (listAt_cons.mp h).1
  set pairs := pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset) with hpairs
  set X := X_list.toFinset with hX
  refine runs_start_le ?_
  refine runs_cond_le (v := if pairLists.length = 0 then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hk_mem)
      (Expr.eval_const (by omega)) (by omega)) (fun hne => ?_) (fun heq => ?_)
  · -- no pairs: return the empty matching at once
    have hk0 : pairLists.length = 0 := by by_contra h; simp [h] at hne
    have hnil : pairLists = [] := List.eq_nil_of_length_eq_zero hk0
    have hpnil : pairs = [] := by rw [hpairs, hnil]; rfl
    have hroute : routeOrCut G X [] Δ L b z = .matched [] (fun _ => []) := by
      simp [routeOrCut, routeOrCutRaw, totalDemand]
    dsimp only [seqStmts]
    refine runs_seq_store_le (x := oA) (v := 0)
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := oA + 1) (v := 0)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
        (by omega)) (Expr.eval_const (by omega)) ?_
    refine runs_ret_le (v := h0) (Expr.eval_reg_of_eq (by simp [startState])) ?_ ?_
    · dsimp only [multiPairRouterContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, hreadP,
        hpnil, hroute, routerCallCost_nil]
      refine ⟨⟨by simp, by simp, fun j hj => by simp at hj⟩, le_rfl, Nat.le_add_right _ _, ?_, ?_⟩
      · intro a ha
        have hne1 : a ≠ oA + 1 := by omega
        have hne2 : a ≠ oA := by omega
        simp [hne1, hne2, startState, hzf a ha]
      · intro a _ ha_out
        have hne1 : a ≠ oA + 1 := by rcases ha_out with h | h <;> omega
        have hne2 : a ≠ oA := by rcases ha_out with h | h <;> omega
        simp [hne1, hne2, startState]
    · dsimp only [multiPairRouterContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, hreadP,
        hpnil, routerCallCost_nil, Expr.size]
      omega
  · -- at least one pair: call the flat router entry
    have hk1 : 1 ≤ pairLists.length := by
      by_contra h; simp [show pairLists.length = 0 by omega] at heq
    have hplen : pairs.length = pairLists.length := by rw [hpairs, List.length_map]
    have hk1' : 1 ≤ pairs.length := hplen ▸ hk1
    have hGm' : G.m ≤ 2 * Δ * X.card := by rw [hX, hcard]; exact hGm
    have hzv' : z ≤ X.card := by rw [hX, hcard]; exact hzv
    set rc := routeOrCutCost G X pairs Δ L b z with hrc
    set O := routeCallOverhead X.card pairs.length Δ L b with hO
    have hcall_eq : routerCallCost G X pairs Δ L b z = rc + O := rfl
    have hheap := routeOrCutMultiHeapSpace_fit (n := G.n) (L := L) (b := b) (rcost := rc) hk1' hGm'
    have hpar := routeOrCutParamBound_fit (L := L) (b := b) hk1' hGm' hzv'
    have hcostfit := routeOrCutMultiTotalCost_fit (Δ := Δ) (b := b) (rcost := rc) hk1' hL hXL hGm'
    rw [← hO] at hheap hpar hcostfit
    rw [hcall_eq] at hsp_w
    have hO_sp : O ≤ outerRouterSpace 200 G.n (rc + O) := by unfold outerRouterSpace; omega
    have hpreW : (routeOrCutMultiWithWalksContract w).pre [gA, xA, pA, Δ, L, b, z, oA, h0] mem :=
      ⟨gA, xA, pA, Δ, L, b, z, oA, h0, G, X_list, pairLists, rfl, hGA, hGval, hX_at, hX_nd, hX_sub,
        hGloop, hΔ, hdeg, hL, hXL, hb, hmp, hpl_nd, hvtp, hzf, hg_h, hx_h, hp_h, hout_h,
        by rw [← hX, ← hpairs, ← hrc, ← hplen]; omega,
        by rw [← hX, ← hplen]; omega, hw16⟩
    dsimp only [seqStmts]
    refine runs_seq_call_le (C := routeOrCutMultiWithWalksContract w)
      (vs := [gA, xA, pA, Δ, L, b, z, oA, h0]) hMulti ?_ hwords hpreW ?_
    · simp [evalArgs, Expr.eval, startState]
    · intro v mem' pos' hpost
      refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
      · dsimp only [Outcome.value]
        refine routeOrCutMultiWithWalks_post_implies_multiPairRouter_post (C_rt := 5000) hpost ?_
        simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, hreadP,
          ← hrc, hcall_eq, hplen]
        rw [← hplen]; omega
      · have hc : (routeOrCutMultiWithWalksContract w).cost [gA, xA, pA, Δ, L, b, z, oA, h0] mem =
            routeOrCutMultiTotalCost G.m X.card pairs.length rc := by
          simp only [routeOrCutMultiWithWalksContract, List.getD_cons_zero, List.getD_cons_succ,
            hreadG, hreadX, hreadP, ← hrc]
        have hc2 : (multiPairRouterContract 5000 200 w).cost [gA, xA, pA, Δ, L, b, z, oA, h0] mem =
            5000 * (rc + O) + 5000 := by
          simp only [multiPairRouterContract, List.getD_cons_zero, List.getD_cons_succ,
            hreadG, hreadX, hreadP, hcall_eq]
        have hm : (startState [gA, xA, pA, Δ, L, b, z, oA, h0] mem pos).mem = mem := rfl
        simp only [argsSize, Expr.size, hm] at hc hc2 ⊢
        omega

/-- **The router module of the Core**: the router program with its entry procedure, meeting
`multiPairRouterContract 5000 200 w` for every placement and word size. -/
noncomputable def routeOrCutRouterModule : MultiPairRouterModule where
  procs := routerModuleProcs
  entryOff := routerEntryOff
  C_rt := 5000
  C_sp := 200
  meets := fun _ _ _ hp => routeOrCutEntry_meetsContract hp

end MinCostFlow.ExpanderDecomp
