module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCLeftoverBase

import Mathlib.Tactic.Linarith

/-!
# Step C Leftover-Injection Word-RAM Procedure (`ProgStepCLeftover`)

Implements and verifies `stepCLeftoverProc bRoute`, a deterministic (`NoRand`) Word-RAM procedure
meeting `stepCLeftoverContract cfg (C_rt + 1000) C_sp w` (`ProgStepCSpec.lean`), calling the
single-pair static router directly through `routeOrCutContract C_rt C_sp w`
(`OuterProgContracts.lean`).

Main results:
- `stepCLeftoverProc` / `stepCLeftoverProc_noRand`
- `stepCLeftoverProc_spec : MeetsContract w p base (stepCLeftoverContract cfg (C_rt + 1000) C_sp w)`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Procedure (`NoRand`) -/

/-- Full Step C leftover-injection procedure (`stepCLeftover`).
`args = [gAddr, xAddr, b, z, Δ, L, locAddr, outAddr, h]`. -/
def stepCLeftoverProc (bRoute : ℕ) : Stmt :=
  seqStmts [
    .assign 9 (.load (.reg 1)),
    .assign 10 (.bin .div (.reg 9) (.reg 2)),
    .assign 11 (.bin .mul (.reg 10) (.reg 2)),
    .assign 12 (.bin .sub (.reg 9) (.reg 11)),
    .cond (.bin .eq (.reg 12) (.const 0))
      (seqStmts [
        .store (.reg 7) (.const 0),
        .store (.bin .add (.reg 7) (.const 1)) (.const 0),
        .ret (.reg 8)
      ])
      (seqStmts [
        .store (.reg 8) (.const 1),
        .store (.bin .add (.reg 8) (.const 1)) (.reg 12),
        .assign 13 (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 11)),
        .assign 14 (.bin .add (.reg 8) (.const 2)),
        scCopySliceStmt 13 14 12 15 16,
        .store (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 12)) (.reg 11),
        .assign 13 (.bin .add (.reg 1) (.const 1)),
        .assign 14 (.bin .add (.bin .add (.reg 8) (.const 3)) (.reg 12)),
        scCopySliceStmt 13 14 11 15 16,
        .assign 13 (.bin .add (.bin .add (.reg 8) (.const 3)) (.reg 9)),
        .assign 14 (.load (.reg 0)),
        .assign 15 (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 14))),
        .call 16 bRoute [.reg 0, .reg 1, .reg 8, .reg 4, .reg 5, .const 100, .reg 3, .reg 13, .reg 15],
        .cond (.bin .eq (.load (.reg 13)) (.const 1))
          (seqStmts [
            scCopyCutStmt 13 7 17 18 19,
            .ret (.reg 16)
          ])
          scLeftoverMatchedStmt
      ])
  ]

theorem stepCLeftoverProc_noRand (bRoute : ℕ) : (stepCLeftoverProc bRoute).NoRand := by
  simp [stepCLeftoverProc, scLeftoverMatchedStmt_noRand, scCopySliceStmt_noRand, scCopyCutStmt_noRand,
    seqStmts, Stmt.NoRand]

/-! ## 2. Contract Proof (`stepCLeftoverProc_spec`) -/

/-- `stepCLeftoverProc bRoute` meets `stepCLeftoverContract cfg (C_rt + 1000) C_sp w` whenever
`bRoute` meets the single-pair `routeOrCutContract C_rt C_sp w`. -/
theorem stepCLeftoverProc_spec {cfg : CoreParams} {w base bRoute C_rt C_sp : ℕ} {p : Program}
    (hp : p.procs[base]? = some (stepCLeftoverProc bRoute))
    (hRoute : MeetsContract w p bRoute (routeOrCutContract C_rt C_sp w)) :
    MeetsContract w p base (stepCLeftoverContract cfg (C_rt + 1000) C_sp w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨gA, xA, b, z, locA, outA, h0, G, vs, rfl,
    hGA, hGval, hvs_at, hvs_s, hvs_sub, hGloop, hΔ, hdegG, hL, hvsL, hb, hmod_b,
    hloc0, hzf0, hg_h, hx_h, hloc_h, hout_h, hdl_g, hdl_x, hdl_o, hdo_g, hdo_x, hsp_w, h16, hGm, hzv⟩
  have hreadG : readGraph mem gA = G := readGraph_eq_of_graphAt hGA
  have hreadX : readLenPrefixedList mem xA = vs := readLenPrefixedList_eq_of_lenListAt hvs_at
  have hΔ_w : cfg.Δ < 2 ^ w := hwords cfg.Δ (by simp)
  have hL_w : cfg.L < 2 ^ w := hwords cfg.L (by simp)
  have hz_w : z < 2 ^ w := hwords z (by simp)
  have hvs_nd : vs.Nodup := hvs_s.imp fun h => Nat.ne_of_lt h
  have hvs_card : vs.toFinset.card = vs.length := List.toFinset_card_of_nodup hvs_nd
  have h100 : 100 < 2 ^ w := by
    have h81 : 81 ≤ (G.n + 3) ^ 4 := by
      have : (G.n + 3) ^ 4 = G.n ^ 4 + 12 * G.n ^ 3 + 54 * G.n ^ 2 + 108 * G.n + 81 := by ring
      omega
    unfold stepCLeftoverSpace at hsp_w
    have h2 : 1 * (2 * 81) ≤ (C_sp + 1) * (stepCLeftoverCost cfg routerCallCost G vs.toFinset vs b z +
        2 * (G.n + 3) ^ 4 + 20 * (vs.length + 1)) :=
      Nat.mul_le_mul (Nat.succ_pos C_sp) (by omega)
    omega
  set q := vs.length / b
  set fullLen := q * b
  set leftLen := vs.length % b
  have hsum_len : fullLen + leftLen = vs.length := by
    have hdm : b * q + leftLen = vs.length := Nat.div_add_mod vs.length b
    have hmc : fullLen = b * q := Nat.mul_comm q b
    omega
  have hsub_len : vs.length - fullLen = leftLen := by omega
  have hleft_len : (leftoverList vs b).length = leftLen := by
    unfold leftoverList numFullBlocks; rw [List.length_drop]; omega
  have hfull_len : (fullPrefix vs b).length = fullLen := by
    unfold fullPrefix numFullBlocks
    rw [List.length_take, Nat.min_eq_left (Nat.div_mul_le_self vs.length b)]
  refine runs_start_le ?_
  dsimp only [stepCLeftoverProc, seqStmts]
  refine runs_seq_assign_le (v := vs.length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hvs_at.1) ?_
  refine runs_seq_assign_le (v := q)
    (Expr.eval_div (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) ?_
  refine runs_seq_assign_le (v := fullLen)
    (Expr.eval_mul (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) ?_
  refine runs_seq_assign_le (v := leftLen)
    (hsub_len ▸ Expr.eval_sub (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
  refine runs_cond_le (v := if leftLen = 0 then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
    (fun hne0 => ?_) (fun heq0 => ?_)
  · -- Case 1: `leftLen = 0` (`leftoverVerts vs b` is empty)
    have hl0 : leftLen = 0 := by by_contra h; simp [h] at hne0
    have hnotne : ¬ (leftoverVerts vs b).Nonempty := by
      unfold leftoverVerts; simp [List.eq_nil_of_length_eq_zero (hleft_len.trans hl0)]
    refine runs_seq_store_le (x := outA) (v := 0)
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := outA + 1) (v := 0)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_const (by omega)) ?_
    refine runs_ret_le (v := h0) (Expr.eval_reg_of_eq (by simp [startState])) ?_
      (by dsimp only [stepCLeftoverContract]
          simp only [List.getD_cons_zero, List.getD_cons_succ, hreadX, stepCLeftoverCost,
            hnotne, ↓reduceIte, Expr.size]; omega)
    dsimp only [stepCLeftoverContract, Outcome.value]
    simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, stepCLeftover, hnotne, ↓reduceIte]
    refine ⟨⟨by simp, by simp [callsFakeEdges], fun j hj => by simp [callsFakeEdges] at hj⟩, ?_, le_rfl, Nat.le_add_right _ _, ?_, ?_⟩
    · intro u hu
      have hne1 : locA + u ≠ outA + 1 := by rcases hdl_o with h | h <;> omega
      have hne2 : locA + u ≠ outA := by rcases hdl_o with h | h <;> omega
      simp [hne1, hne2, startState, hloc0 u hu]
    · intro a ha
      have hne1 : a ≠ outA + 1 := by omega
      have hne2 : a ≠ outA := by omega
      simp [hne1, hne2, startState, hzf0 a ha]
    · intro a _ _ ha_out
      have hne1 : a ≠ outA + 1 := by rcases ha_out with h | h <;> omega
      have hne2 : a ≠ outA := by rcases ha_out with h | h <;> omega
      simp [hne1, hne2, startState]
  · -- Case 2: `0 < leftLen` (`leftoverVerts vs b` is nonempty)
    have hmod_pos : 0 < vs.length % b := by by_contra h; simp [leftLen, show vs.length % b = 0 by omega] at heq0
    have hb_le : b ≤ vs.length := hmod_b hmod_pos
    have hne_left : (leftoverVerts vs b).Nonempty := by
      unfold leftoverVerts
      have hne_nil : leftoverList vs b ≠ [] := by intro h; rw [h] at hleft_len; simp at hleft_len; omega
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne_nil
      exact ⟨v, List.mem_toFinset.mpr hv⟩
    set rcost := routerCallCost G vs.toFinset [(leftoverVerts vs b, fullVerts vs b)] cfg.Δ cfg.L 100 z
    have hcostL_eq : stepCLeftoverCost cfg routerCallCost G vs.toFinset vs b z = rcost + (vs.length + 1) := by
      simp [stepCLeftoverCost, hne_left, rcost, hvs_card]
    have hheadroom : h0 + (3 + vs.length) + (2 + 2 * G.n) + outerRouterSpace C_sp G.n rcost + vs.length < 2 ^ w := by
      have h1 := stepCLeftoverSpace_headroom C_sp G.n vs.length rcost
      rw [hcostL_eq] at hsp_w; omega
    set rtOut := h0 + 3 + vs.length
    set hRt := rtOut + 2 + 2 * G.n
    refine runs_seq_store_le (x := h0) (v := 1)
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := h0 + 1) (v := leftLen)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_assign_le (v := xA + 1 + fullLen)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
    refine runs_seq_assign_le (v := h0 + 2)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega)) ?_
    let mem1 := Function.update (Function.update mem h0 1) (h0 + 1) leftLen
    let stA : State :=
      { mem := mem1,
        regs := Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
          (startState [gA, xA, b, z, cfg.Δ, cfg.L, locA, outA, h0] mem pos).regs
          9 vs.length) 10 q) 11 fullLen) 12 leftLen) 13 (xA + 1 + fullLen)) 14 (h0 + 2),
        pos := pos }
    have hleft_at1 : ListAt mem1 (xA + 1 + fullLen) (leftoverList vs b) := fun i hi => by
      have hne1 : xA + 1 + fullLen + i ≠ h0 + 1 := by omega
      have hne2 : xA + 1 + fullLen + i ≠ h0 := by omega
      simp only [mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
      have hshift : xA + 1 + fullLen + i = (xA + 1) + (fullLen + i) := by omega
      rw [hshift]
      have hget : (leftoverList vs b)[i]'hi = vs[fullLen + i]'(by omega) := by
        simp [leftoverList, numFullBlocks, fullLen, q]
      rw [hget]; exact hvs_at.2 (fullLen + i) (by omega)
    refine runs_seq_triple_le
      (scCopySlice_triple (srcA := xA + 1 + fullLen) (dstA := h0 + 2) (len := leftLen)
        (rSrc := 13) (rDst := 14) (rLen := 12) (rI := 15) (rTmp := 16)
        (by decide) p mem1 (leftoverList vs b) stA hleft_len hleft_at1
        (Or.inr (by omega)) (by omega) (by omega) h16
        (by dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_self])
        (by dsimp only [stA]; rw [Function.update_self])
        (by dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
        rfl) rfl ?_
    intro stB ⟨hothB, _, hfrB, hleft_dst⟩
    have hstB_lt13 : ∀ r < 13, stB.regs r = stA.regs r := fun r hr => hothB r (by omega) (by omega)
    refine runs_seq_store_le (x := h0 + 2 + leftLen) (v := fullLen)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hstB_lt13 8 (by decide)).trans (by simp [stA, startState])))
        (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq ((hstB_lt13 12 (by decide)).trans (by simp [stA]))) (by omega))
      (Expr.eval_reg_of_eq ((hstB_lt13 11 (by decide)).trans (by simp [stA]))) ?_
    refine runs_seq_assign_le (v := xA + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq ((hstB_lt13 1 (by decide)).trans (by simp [stA, startState])))
        (Expr.eval_const (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := h0 + 3 + leftLen)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hstB_lt13 8 (by decide)]; simp [stA, startState]))
        (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hstB_lt13 12 (by decide)]; simp [stA]))
        (by omega)) ?_
    let mem2 := Function.update stB.mem (h0 + 2 + leftLen) fullLen
    let stC : State :=
      { mem := mem2, regs := Function.update (Function.update stB.regs 13 (xA + 1)) 14 (h0 + 3 + leftLen), pos := stB.pos }
    have hfull_at2 : ListAt mem2 (xA + 1) (fullPrefix vs b) := fun i hi => by
      have hne : xA + 1 + i ≠ h0 + 2 + leftLen := by omega
      simp only [mem2, Function.update_of_ne hne]
      rw [hfrB _ (Or.inl (by omega))]
      have hne1 : xA + 1 + i ≠ h0 + 1 := by omega
      have hne2 : xA + 1 + i ≠ h0 := by omega
      simp only [mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
      have hget : (fullPrefix vs b)[i]'hi = vs[i]'(by omega) := by simp [fullPrefix, numFullBlocks]
      rw [hget]; exact hvs_at.2 i (by omega)
    refine runs_seq_triple_le
      (scCopySlice_triple (srcA := xA + 1) (dstA := h0 + 3 + leftLen) (len := fullLen)
        (rSrc := 13) (rDst := 14) (rLen := 11) (rI := 15) (rTmp := 16)
        (by decide) p mem2 (fullPrefix vs b) stC hfull_len hfull_at2
        (Or.inr (by omega)) (by omega) (by omega) h16
        (by dsimp only [stC]; rw [Function.update_of_ne (by decide), Function.update_self])
        (by dsimp only [stC]; rw [Function.update_self])
        (by dsimp only [stC]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstB_lt13 11 (by decide)]; simp [stA])
        rfl) rfl ?_
    intro stD ⟨hothD, _, hfrD, hfull_dst⟩
    have hstD_lt13 : ∀ r < 13, stD.regs r = stA.regs r := fun r hr => by
      rw [hothD r (by omega) (by omega)]
      dsimp only [stC]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hstB_lt13 r hr]
    have hmemD_lt_h0 : ∀ a < h0, stD.mem a = mem a := fun a ha => by
      rw [hfrD a (Or.inl (by omega))]
      simp only [mem2, Function.update_of_ne (by omega : a ≠ h0 + 2 + leftLen)]
      rw [hfrB a (Or.inl (by omega))]
      simp only [mem1, Function.update_of_ne (by omega : a ≠ h0 + 1), Function.update_of_ne (by omega : a ≠ h0)]
    have hGA_D : GraphAt stD.mem gA G := fun i hi => by
      rw [hmemD_lt_h0 _ (by have := graph_encode_length G; omega)]; exact hGA i hi
    have hvs_D : LenListAt stD.mem xA vs :=
      ⟨by rw [hmemD_lt_h0 _ (by omega)]; exact hvs_at.1,
       fun i hi => by rw [hmemD_lt_h0 _ (by omega)]; exact hvs_at.2 i hi⟩
    have hsp_D : SinglePairAt stD.mem h0 (leftoverList vs b) (fullPrefix vs b) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hfrD h0 (Or.inl (by omega))]; simp only [mem2, Function.update_of_ne (by omega : h0 ≠ h0 + 2 + leftLen)]
        rw [hfrB h0 (Or.inl (by omega))]; simp [mem1]
      · rw [hfrD (h0 + 1) (Or.inl (by omega))]; simp only [mem2, Function.update_of_ne (by omega : h0 + 1 ≠ h0 + 2 + leftLen)]
        rw [hfrB (h0 + 1) (Or.inl (by omega))]; simp [mem1, hleft_len]
      · intro i hi
        rw [hfrD _ (Or.inl (by omega))]; simp only [mem2, Function.update_of_ne (by omega : h0 + 2 + i ≠ h0 + 2 + leftLen)]
        exact hleft_dst i hi
      · rw [hleft_len, hfrD (h0 + 2 + leftLen) (Or.inl (by omega))]; simp [mem2, hfull_len]
      · simpa [hleft_len, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfull_dst
    have hzf_D : ZeroFrom stD.mem hRt := fun a ha => by
      rw [hfrD a (Or.inr (by omega))]
      simp only [mem2, Function.update_of_ne (by omega : a ≠ h0 + 2 + leftLen)]
      rw [hfrB a (Or.inr (by omega))]
      simp only [mem1, Function.update_of_ne (by omega : a ≠ h0 + 1), Function.update_of_ne (by omega : a ≠ h0)]
      exact hzf0 a (by omega)
    refine runs_seq_assign_le (v := rtOut)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hstD_lt13 8 (by decide)).trans (by simp [stA, startState])))
        (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq ((hstD_lt13 9 (by decide)).trans (by simp [stA]))) (by omega)) ?_
    refine runs_seq_assign_le (v := G.n)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hstD_lt13 0 (by decide)]; simp [stA, startState]))
        (graphAt_n hGA_D)) ?_
    refine runs_seq_assign_le (v := hRt)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
        (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
        (by omega)) ?_
    have hvtp : ValidTerminalPairs vs.toFinset [(leftoverVerts vs b, fullVerts vs b)] :=
      leftover_validTerminalPairs hvs_nd hb hmod_pos hb_le
    have hrt_pre : (routeOrCutContract C_rt C_sp w).pre
        [gA, xA, h0, cfg.Δ, cfg.L, 100, z, rtOut, hRt] stD.mem := by
      refine ⟨gA, xA, h0, cfg.Δ, cfg.L, 100, z, rtOut, hRt, G, vs, leftoverList vs b, fullPrefix vs b,
        rfl, hGA_D, hGval, hvs_D, hvs_nd, hvs_sub, hGloop, hΔ, hdegG, hL, by rwa [hvs_card], by decide,
        hsp_D, hvs_nd.sublist (List.drop_sublist _ _), hvs_nd.sublist (List.take_sublist _ _), hvtp,
        hzf_D, by omega, by omega, by omega, le_rfl, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega),
        by change hRt + outerRouterSpace C_sp G.n rcost < 2 ^ w; omega, h16, hGm, hzv⟩
    have hread_sp : readSinglePair stD.mem h0 = (leftoverVerts vs b, fullVerts vs b) := by
      unfold readSinglePair leftoverVerts fullVerts
      rcases hsp_D with ⟨_, hlenA, hAtA, hlenB, hAtB⟩
      simp only [hlenA, hlenB, readList_eq_of_listAt hAtA, readList_eq_of_listAt hAtB]
    have hread_D : readGraph stD.mem gA = G ∧ (readLenPrefixedList stD.mem xA).toFinset = vs.toFinset :=
      ⟨readGraph_eq_of_graphAt hGA_D, by rw [readLenPrefixedList_eq_of_lenListAt hvs_D]⟩
    refine runs_seq_call_le (C := routeOrCutContract C_rt C_sp w)
      (vs := [gA, xA, h0, cfg.Δ, cfg.L, 100, z, rtOut, hRt]) hRoute ?_ ?_ hrt_pre ?_
    · simp only [evalArgs, Expr.eval, h100, ↓reduceIte]
      have hr0' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 0 = gA := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstD_lt13 0 (by decide)]; simp [stA, startState]
      have hr1' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 1 = xA := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstD_lt13 1 (by decide)]; simp [stA, startState]
      have hr8' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 8 = h0 := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstD_lt13 8 (by decide)]; simp [stA, startState]
      have hr4' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 4 = cfg.Δ := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstD_lt13 4 (by decide)]; simp [stA, startState]
      have hr5' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 5 = cfg.L := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstD_lt13 5 (by decide)]; simp [stA, startState]
      have hr3' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 3 = z := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstD_lt13 3 (by decide)]; simp [stA, startState]
      have hr13' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 13 = rtOut := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
      have hr15' : (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 15 = hRt := by
        rw [Function.update_self]
      simp only [hr0', hr1', hr8', hr4', hr5', hr3', hr13', hr15']
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · exact hΔ_w
      · exact hL_w
      · exact h100
      · exact hz_w
      · omega
      · omega
    · intro hAfterRt memE posE hrt_post
      dsimp only [routeOrCutContract, outerRouterContract] at hrt_post
      simp only [List.getD_cons_zero, List.getD_cons_succ, hread_D.1, hread_D.2, hread_sp] at hrt_post
      rcases hrt_post with ⟨hRouteOut, hhRt_le_after, hAfter_le, hzfE, hfrE⟩
      have hcost_rt_eq : (routeOrCutContract C_rt C_sp w).cost
          [gA, xA, h0, cfg.Δ, cfg.L, 100, z, rtOut, hRt] stD.mem = C_rt * rcost + C_rt := by
        simp [routeOrCutContract, outerRouterContract, hread_D.1, hread_D.2, hread_sp, rcost]
      have hmemE_lt_h0 : ∀ a < h0, memE a = mem a := fun a ha => by
        rw [hfrE a (by omega) (Or.inl (by omega)), hmemD_lt_h0 a ha]
      have hAfter_sp : hAfterRt + vs.length ≤
          h0 + stepCLeftoverSpace C_sp G.n vs.length (stepCLeftoverCost cfg routerCallCost G vs.toFinset vs b z) := by
        have h1 := stepCLeftoverSpace_headroom C_sp G.n vs.length rcost
        change hAfterRt ≤ hRt + outerRouterSpace C_sp G.n rcost at hAfter_le
        rw [hcostL_eq]; omega
      let regsE := Function.update (Function.update (Function.update (Function.update stD.regs 13 rtOut) 14 G.n) 15 hRt) 16 hAfterRt
      let stE : State := { mem := memE, regs := regsE, pos := posE }
      have hstE_lt13 : ∀ r < 13, stE.regs r = stA.regs r := fun r hr => by
        dsimp only [stE, regsE]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), hstD_lt13 r hr]
      have hr13_E : stE.regs 13 = rtOut := by
        dsimp only [stE, regsE]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self]
      have hr16_E : stE.regs 16 = hAfterRt := by dsimp only [stE, regsE]; rw [Function.update_self]
      have hspec_rt := routeOrCut_isMatchingPlayer.spec G vs.toFinset [(leftoverVerts vs b, fullVerts vs b)]
        cfg.Δ cfg.L 100 z hvs_sub hGloop hΔ hdegG hL (by rwa [hvs_card]) (by decide) hvtp
      cases hrt : routeOrCut G vs.toFinset [(leftoverVerts vs b, fullVerts vs b)] cfg.Δ cfg.L 100 z with
      | cut U =>
        rw [hrt] at hRouteOut hspec_rt
        rcases hRouteOut with ⟨htag, U_list, hUnd, hUfin, hUlen, hUat⟩
        have hU_len_le : U_list.length ≤ vs.length := by
          have hc1 : U_list.length = U.card := by rw [← hUfin, List.toFinset_card_of_nodup hUnd]
          have hc2 : U.card ≤ vs.toFinset.card := Finset.card_le_card hspec_rt.1
          omega
        refine runs_cond_le (v := 1)
          (by have he : Expr.eval w stE (.bin .eq (.load (.reg 13)) (.const 1)) = some (if 1 = 1 then 1 else 0) :=
                Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr13_E) htag)
                  (Expr.eval_const (by omega)) (by omega)
              simpa using he)
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine runs_seq_triple_le
          (scCopyCut_triple (w := w) (cap := 2 + U_list.length) (srcA := rtOut) (dstA := outA)
            (rSrc := 13) (rDst := 7) (rLen := 17) (rI := 18) (rU := 19)
            (by decide) p memE U_list stE hUlen hUat le_rfl
            (Or.inl (by omega)) (by omega) (by omega) h16 hr13_E
            ((hstE_lt13 7 (by decide)).trans (by simp [stA, startState])) rfl) rfl ?_
        intro stF ⟨hothF, _, hfrF, hU0, hU1, hUat'⟩
        refine runs_ret_le (v := hAfterRt)
          (Expr.eval_reg_of_eq ((hothF 16 (by decide) (by decide) (by decide)).trans hr16_E)) ?_
          (by dsimp only [stepCLeftoverContract]
              simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, hcostL_eq,
                hcost_rt_eq, Expr.size, argsSize]
              have hmul : (C_rt + 1000) * (rcost + (vs.length + 1)) =
                  C_rt * rcost + C_rt * vs.length + C_rt + 1000 * rcost + 1000 * vs.length + 1000 := by ring
              omega)
        dsimp only [stepCLeftoverContract, Outcome.value]
        simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, stepCLeftover, hne_left, ↓reduceIte, hrt]
        refine ⟨⟨hU0, U_list, hUnd, hUfin, hU1, hUat'⟩, ?_, by omega, by omega, ?_, ?_⟩
        · intro u hu
          have hdisj : locA + u < outA ∨ outA + (2 + U_list.length) ≤ locA + u := by
            rcases hdl_o with h | h <;> [left; right] <;> omega
          rw [hfrF _ hdisj, hmemE_lt_h0 _ (by omega)]; exact hloc0 u hu
        · intro a ha; rw [hfrF a (Or.inr (by omega))]; exact hzfE a ha
        · intro a ha_h _ ha_out
          have hdisj : a < outA ∨ outA + (2 + U_list.length) ≤ a := by rcases ha_out with h | h <;> [left; right] <;> omega
          rw [hfrF a hdisj, hmemE_lt_h0 a ha_h]
      | matched matchings emb =>
        rw [hrt] at hRouteOut hspec_rt
        rcases hRouteOut with ⟨htag, hmLen, hmAt⟩
        rcases hspec_rt with ⟨hmlen_p, hpm_p, _, _, _, _⟩
        refine runs_cond_le (v := 0)
          (by have he : Expr.eval w stE (.bin .eq (.load (.reg 13)) (.const 1)) = some (if 0 = 1 then 1 else 0) :=
                Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr13_E) htag)
                  (Expr.eval_const (by omega)) (by omega)
              simpa using he)
          (fun h => absurd rfl h) (fun _ => ?_)
        have hvs_E : LenListAt memE xA vs :=
          ⟨by rw [hmemE_lt_h0 _ (by omega)]; exact hvs_at.1,
           fun i hi => by rw [hmemE_lt_h0 _ (by omega)]; exact hvs_at.2 i hi⟩
        have hloc0_E : ∀ u < G.n, memE (locA + u) = 0 := fun u hu => by
          rw [hmemE_lt_h0 _ (by omega)]; exact hloc0 u hu
        obtain ⟨stF, cM, hrM, hm0, hm1, hmE, hlocF, hzfF, hfrF, hcM⟩ :=
          scLeftoverMatched_run (w := w) (n := G.n) (xA := xA) (b := b) (locA := locA)
            (outA := outA) (h0 := h0) (rtOut := rtOut) (hAfterRt := hAfterRt)
            hvs_E hvs_s hvs_sub hb hmod_pos hb_le hvtp (by simpa using hmlen_p)
            (hpm_p 0 (by simp)) hmLen hmAt hloc0_E hzfE hx_h hloc_h hout_h
            hdl_x hdl_o (by omega) hhRt_le_after (by omega) h16
            ((hstE_lt13 1 (by decide)).trans (by simp [stA, startState]))
            ((hstE_lt13 6 (by decide)).trans (by simp [stA, startState]))
            ((hstE_lt13 7 (by decide)).trans (by simp [stA, startState]))
            ((hstE_lt13 9 (by decide)).trans (by simp [stA]))
            ((hstE_lt13 11 (by decide)).trans (by simp [stA, fullLen, q]))
            ((hstE_lt13 12 (by decide)).trans (by simp [stA, leftLen]))
            hr13_E hr16_E rfl
        refine ⟨.returned (hAfterRt + vs.length), stF, cM, hrM, ?_, ?_⟩
        · dsimp only [stepCLeftoverContract, Outcome.value]
          simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, stepCLeftover, hne_left, ↓reduceIte, hrt]
          refine ⟨⟨hm0, by simpa [callsFakeEdges] using hm1, by simpa [callsFakeEdges] using hmE⟩,
            hlocF, by omega, hAfter_sp, hzfF, fun a ha_h ha_loc ha_out => (hfrF a ha_h ha_loc ha_out).trans (hmemE_lt_h0 a ha_h)⟩
        · dsimp only [stepCLeftoverContract]
          simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, hcostL_eq,
            hcost_rt_eq, Expr.size, argsSize]
          have hmul : (C_rt + 1000) * (rcost + (vs.length + 1)) =
              C_rt * rcost + C_rt * vs.length + C_rt + 1000 * rcost + 1000 * vs.length + 1000 := by ring
          omega

end MinCostFlow.ExpanderDecomp
