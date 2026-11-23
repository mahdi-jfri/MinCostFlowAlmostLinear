module

public import MinCostFlow.ExpanderDecomp.OuterProgGameDefs
import MinCostFlow.ExpanderDecomp.OuterProgGameStep
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Main Verification of `outerGameProc` (`OuterProgGame`)

Completes the inductive loop verification (`gameRoundBody_runs`, `gameLoop_runs`, `gameInit_runs`)
and proves `outerGameProc_spec`, re-exporting `OuterProgGameDefs`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- One complete round of `gameRoundBodyStmt idx` from a `GameLoopInv` + `GameMathInv` state at
`fuel + 1`. -/
private lemma gameRoundBody_runs {M r e pgAddr outResAddr h w C_core C_rt C_sp_core C_sp_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterGameIndices}
    {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    (g : GameGeom ParamConfig.default M r e pgAddr outResAddr h)
    (hSub : OuterGameSubprocs M r w pProg idx coreCost route routeCost C_core C_rt C_sp_core C_sp_rt C_sp routeC)
    (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hrl : r ≤ ell M)
    (hwb : bOut ParamConfig.default M < 2 ^ w) (hwM : M < 2 ^ w) (hwR : r < 2 ^ w) (hw16 : 16 < 2 ^ w)
    {fuel k : ℕ} {M_hist : ℕ → List (ℕ × ℕ)} {W_edges F_edges : List (ℕ × ℕ)} {st : State}
    (hInv : GameLoopInv g mem₀ (fuel + 1) k W_edges F_edges st)
    (hMath : GameMathInv M r e (e / DOut ParamConfig.default M r) g.Hhat M_hist k W_edges F_edges)
    (hSpace : st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1)
      ((fuel + 1) * outerGameRoundBudget ParamConfig.default M r routeC e) < 2 ^ w) :
    let lc := (fuel + 1) * outerGameRoundBudget ParamConfig.default M r routeC e
    ∃ oB stB cB,
      Runs w pProg ω (gameRoundBodyStmt idx) st oB stB cB ∧
      ((∃ h' res, oB = .returned h' ∧
          OuterGameOutAt stB.mem outResAddr h h' e res ∧
          OuterGameOutcomeSpec ParamConfig.default M r e g.Hhat res ∧
          st.regs 26 ≤ h' ∧
          h' ≤ st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc ∧
          ZeroFrom stB.mem h' ∧
          (∀ a < h, (a < outResAddr ∨ outResAddr + 4 ≤ a) → stB.mem a = mem₀ a) ∧
          cB ≤ outerGameCostFactor C_core C_rt * outerGameRoundBudget ParamConfig.default M r routeC e - 10)
       ∨
       (∃ M_k F_k M_hist',
          oB = .normal ∧
          GameLoopInv g mem₀ fuel (k + 1) (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k) stB ∧
          GameMathInv M r e (e / DOut ParamConfig.default M r) g.Hhat M_hist' (k + 1)
            (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k) ∧
          st.regs 26 ≤ stB.regs 26 ∧
          stB.regs 26 ≤ st.regs 26 + C_sp * coreSpaceBase M r *
            (outerGameRoundBudget ParamConfig.default M r routeC e + 1) +
            (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) ∧
          cB ≤ outerGameCostFactor C_core C_rt * outerGameRoundBudget ParamConfig.default M r routeC e - 10)) := by
  intro lc
  let z := e / DOut ParamConfig.default M r
  let W := Graph.mk (2 * e) W_edges
  let q := coreLevel M r (2 * e)
  let cCore := coreCost q W
  let rb := outerGameRoundBudget ParamConfig.default M r routeC e
  rcases g.bufOrder with ⟨hb_x, hb_w, hb_we, hb_f, hb_c, hb_p, hb_r, hb_fr, hb_fl, hb_hi⟩
  have hge := g.hInit_eq
  have hInit_le : g.hInit ≤ st.regs 26 := hInv.hhInit
  have he_pos : 1 ≤ e := g.he_pos
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hF_eq : g.F = 49 * LParam M + 1 := rfl
  have hk_le_F : k < g.F := by have := hInv.hk_fuel; omega
  have hk_le_delta : k ≤ deltaParam M := by unfold deltaParam tParam; omega
  have hk1_le_t : k + 1 ≤ tParam M := by unfold tParam; omega
  have h2Fe_eq : 2 * (g.F * e) = 2 * g.F * e := by ring
  have h2Fe_le : 2 * W_edges.length ≤ 2 * g.F * e := by
    have : k * e ≤ g.F * e := Nat.mul_le_mul_right e (by omega)
    have := hInv.hW_len; omega
  have h2F_len_le : 2 * F_edges.length ≤ 2 * g.F * e := by
    have : k * e ≤ g.F * e := Nat.mul_le_mul_right e (by omega)
    have := hInv.hF_len; omega
  have hq_bounds : 1 ≤ q ∧ q ≤ r ∧ (NOf M r) ^ (q - 1) < 2 * e ∧ 2 * e ≤ (NOf M r) ^ q :=
    ⟨one_le_coreLevel (show 2 ≤ 2 * e by omega), coreLevel_le g.h2e_pow,
     pow_pred_coreLevel_lt (show 2 ≤ 2 * e by omega), le_pow_coreLevel M r (2 * e)⟩
  have hW_deg_delta : ∀ v < W.n, W.deg v ≤ deltaParam M := fun v hv =>
    le_trans (hInv.hW_deg v hv) hk_le_delta
  have hcCore_le : cCore ≤ 2 * e * (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) :=
    hSub.hcoreCost q W hq_bounds.1 hq_bounds.2.1 hInv.hW_val hInv.hW_loop
      hq_bounds.2.2.1 hq_bounds.2.2.2 hW_deg_delta
  have hrb_le_lc : rb ≤ lc := Nat.le_mul_of_pos_left rb (Nat.succ_pos fuel)
  have hHhat_verts : g.Hhat.verts = Finset.range (2 * e) := by unfold Graph.verts; rw [g.hHhat_n]
  have hHhat_ins : g.Hhat.inside g.Hhat.verts = g.Hhat.edges := inside_verts_of_isValid g.hHhat_val
  have hb2 : 2 ≤ bOut ParamConfig.default M := two_le_bOut' ParamConfig.default M
  have hroute_step : ∀ A B : Finset ℕ, A ⊆ Finset.range (2 * e) → B ⊆ Finset.range (2 * e) →
      Disjoint A B → A.card ≤ B.card →
      RouteSpec g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z
        (route g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z) ∧
      routeCost g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z ≤
        routeC * ((12 * e + 1) * (dOut ParamConfig.default M + 1) * ROut ParamConfig.default M + 1) := by
    intro A B hA hB hdisj hcard
    have hvp : ValidTerminalPairs g.Hhat.verts [(A, B)] :=
      validTerminalPairs_singleton' (by rw [hHhat_verts]; exact hA) (by rw [hHhat_verts]; exact hB)
        hdisj hcard
    refine ⟨hSub.hroute.spec g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z
      (Finset.Subset.refl _) (by rw [hHhat_ins]; exact g.hHhat_loop) (by decide)
      (fun v _ => g.hHhat_deg v) (by omega) (by rw [hHhat_verts, Finset.card_range]; exact g.h2e_L)
      hb2 hvp, ?_⟩
    have hcb := hSub.hrouteC g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z
      (Finset.Subset.refl _) (by rw [hHhat_ins]; exact g.hHhat_loop) (by decide)
      (fun v _ => g.hHhat_deg v) (by omega) (by rw [hHhat_verts, Finset.card_range]; exact g.h2e_L)
      hb2 hvp
    rw [hHhat_ins, hHhat_verts, Finset.card_range, routePathLen_outer, routeCong_outer] at hcb
    simp only [List.length_singleton, one_mul] at hcb
    rw [hHhat_verts]
    have hmn : 2 * e + g.Hhat.edges.length + 1 ≤ 12 * e + 1 := by
      have := g.hHhat_m; unfold Graph.m at this; omega
    have hmul : (2 * e + g.Hhat.edges.length + 1) * (dOut ParamConfig.default M + 1) *
        ROut ParamConfig.default M ≤
        (12 * e + 1) * (dOut ParamConfig.default M + 1) * ROut ParamConfig.default M :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmn)
    exact le_trans hcb (Nat.mul_le_mul_left routeC (by omega))
  have hcCore_le_lc : cCore ≤ lc := by
    have : cCore ≤ rb := by unfold rb outerGameRoundBudget; omega
    omega
  have hCoreSpace_le : coreAdapterSpace C_sp_core M r (2 * e) cCore + 2 * e ≤
      outerGameLoopSpace C_sp M r e (fuel + 1) lc := by
    unfold coreAdapterSpace outerGameLoopSpace
    set B := coreSpaceBase M r
    have hsp_c : C_sp_core ≤ C_sp := hSub.hsp_core
    have hcore_le : C_sp_core * (B * (cCore + 1) + (2 * e + 3) ^ 5 + 1) ≤
        C_sp * B * (cCore + 1) + C_sp * ((2 * e + 3) ^ 5 + 1) := by
      have h0 := Nat.mul_le_mul_right (B * (cCore + 1) + (2 * e + 3) ^ 5 + 1) hsp_c
      have h1 : C_sp * (B * (cCore + 1) + (2 * e + 3) ^ 5 + 1) =
          C_sp * B * (cCore + 1) + C_sp * ((2 * e + 3) ^ 5 + 1) := by ring
      omega
    have h1 : C_sp * B * (cCore + 1) ≤ C_sp * B * (lc + (fuel + 1)) :=
      Nat.mul_le_mul_left (C_sp * B) (by omega)
    have h2a : 2 * C_sp * ((2 * e + 3) ^ 5 + 1) =
        C_sp * ((2 * e + 3) ^ 5 + 1) + C_sp * ((2 * e + 3) ^ 5 + 1) := by ring
    have h2 : C_sp * ((2 * e + 3) ^ 5 + 1) + 2 * e ≤
        (fuel + 1) * (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) :=
      le_trans (by omega) (Nat.le_mul_of_pos_left _ (Nat.succ_pos fuel))
    linarith
  have hSpace' : st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc < 2 ^ w := hSpace
  -- Step 1: call bCore
  have hCoreCall := runs_call_of_meetsContract (r := 26) (p := pProg) (w := w)
    (st := st) (args := [.reg 14, .reg 16, .reg 5, .reg 6, .reg 18, .reg 26])
    (vs := [q, g.wAddr, M, r, g.coreOutAddr, st.regs 26]) hSub.hCoreProg
    (by simp [evalArgs, Expr.eval, hInv.hr14, hInv.hr16, hInv.hr5, hInv.hr6, hInv.hr18, q])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨q, g.wAddr, g.coreOutAddr, st.regs 26, W, rfl, hq_bounds.1, hq_bounds.2.1, hrl, hInv.hW_g,
      hInv.hW_val, hInv.hW_loop, hq_bounds.2.2.1, hq_bounds.2.2.2, hW_deg_delta, hInv.hZero,
      by simp [W, Graph.m]; omega, by simp [W]; omega,
      Or.inr (by simp [W, Graph.m]; omega),
      by change st.regs 26 + coreAdapterSpace C_sp_core M r (2 * e) cCore < 2 ^ w; omega,
      hw16, hwM, hwR⟩ ω
  rcases hCoreCall with ⟨st1, c1, h1, hrun1, hpost1, h1_26, h1_other, hc1⟩
  simp only [coreAdapterContract, List.getD_cons_zero, List.getD_cons_succ,
    readGraph_eq_of_graphAt hInv.hW_g] at hpost1 hc1
  rcases hpost1 with ⟨⟨coreRes, hCoreOut, hcore_spec⟩, hh1_ge, hh1_le, hZero1, hFrame1⟩
  change h1 ≤ st.regs 26 + coreAdapterSpace C_sp_core M r (2 * e) cCore at hh1_le
  have hc1' : c1 ≤ C_core * cCore + C_core + 20 := by
    simp [argsSize, Expr.size] at hc1; dsimp only [cCore, W, q] at hc1 ⊢; omega
  have hround_cost_aux : ∀ (cRt : ℕ),
      cCore + cRt + 4 * e ≤ rb →
      C_core * cCore + C_core + C_rt * cRt + C_rt + 1500 * e + 1000 ≤
        outerGameCostFactor C_core C_rt * rb - 10 := by
    intro cRt hle_rb
    have hmul : outerGameCostFactor C_core C_rt * (cCore + cRt + 4 * e) =
        (2 * C_core + 2 * C_rt + 2000) * cCore + (2 * C_core + 2 * C_rt + 2000) * cRt +
          (2 * C_core + 2 * C_rt) * (4 * e) + 8000 * e := by
      unfold outerGameCostFactor; ring
    have hc1_le : C_core * cCore ≤ (2 * C_core + 2 * C_rt + 2000) * cCore :=
      Nat.mul_le_mul_right cCore (by omega)
    have hc2_le : C_rt * cRt ≤ (2 * C_core + 2 * C_rt + 2000) * cRt :=
      Nat.mul_le_mul_right cRt (by omega)
    have hc3_le : (2 * C_core + 2 * C_rt) * 4 ≤ (2 * C_core + 2 * C_rt) * (4 * e) :=
      Nat.mul_le_mul_left _ (by omega)
    have hrb_mul : outerGameCostFactor C_core C_rt * (cCore + cRt + 4 * e) ≤
        outerGameCostFactor C_core C_rt * rb := Nat.mul_le_mul_left _ hle_rb
    have hsum : C_core * cCore + C_core + C_rt * cRt + C_rt + 1500 * e + 1010 ≤
        outerGameCostFactor C_core C_rt * rb := by linarith
    exact Nat.le_sub_of_add_le hsum
  have h1_r : ∀ r', r' ≠ 26 → st1.regs r' = st.regs r' := h1_other
  have h1_pg : GraphAt st1.mem pgAddr g.Hhat := by
    intro i hi
    have hi' : i < 2 + 2 * g.Hhat.m := by rw [graph_encode_length] at hi; exact hi
    rw [hFrame1 _ (by have := g.hpgH; omega) (Or.inl (by have := g.hpgH; omega))]; exact hInv.hPg i hi
  have h1_xPort : LenListAt st1.mem g.xPortAddr (List.range (2 * e)) := by
    refine ⟨by rw [hFrame1 _ (by omega) (Or.inl (by omega))]; exact hInv.hXPort.1,
      fun j hj => by rw [hFrame1 _ (by simp at hj; omega) (Or.inl (by simp at hj; omega))]; exact hInv.hXPort.2 j hj⟩
  have h1_W : GraphAt st1.mem g.wAddr W := by
    intro i hi
    have hi' : i < 2 + 2 * W_edges.length := by rw [graph_encode_length] at hi; simpa [W, Graph.m] using hi
    rw [hFrame1 _ (by omega) (Or.inl (by omega))]; exact hInv.hW_g i hi
  have h1_F : EdgesAt st1.mem g.fAddr F_edges := by
    intro j hj; have hj' : j < F_edges.length := hj
    rw [hFrame1 _ (by omega) (Or.inl (by omega)), hFrame1 _ (by omega) (Or.inl (by omega))]
    exact hInv.hF_e j hj
  -- Branch on the existential `coreRes`
  cases coreRes with
  | expander S =>
    rcases hCoreOut with ⟨hCTag, S_list, hndS, hfinS, hLenS, hListS⟩
    obtain ⟨hSV, hS2, hSexp_q⟩ := hcore_spec
    change S ⊆ Finset.range (2 * e) at hSV
    change 2 * e ≤ 2 * S.card at hS2
    have hSexp : W.IsExpansionExpanderOn S (1 / (PParam ParamConfig.default M r : ℝ)) :=
      isExpansionExpanderOn_mono (inv_PParam_le_of_le ParamConfig.default M hq_bounds.2.1) hSexp_q
    have hSlen_le : S_list.length ≤ 2 * e := by
      have := Finset.card_le_card hSV
      rw [← hfinS, List.toFinset_card_of_nodup hndS, Finset.card_range] at this; exact this
    let st2 : State :=
      { st1 with regs := Function.update (Function.update (Function.update st1.regs 35 1) 29 S_list.length) 30 (g.coreOutAddr + 2) }
    have hLoadC : Runs w pProg ω
        (.assign 35 (.load (.reg 18)) ;;
         .assign 29 (.load (.bin .add (.reg 18) (.const 1))) ;;
         .assign 30 (.bin .add (.reg 18) (.const 2))) st1 .normal st2 14 := by
      let st1a : State := { st1 with regs := Function.update st1.regs 35 1 }
      let st1b : State := { st1a with regs := Function.update st1a.regs 29 S_list.length }
      have ha1 : Runs w pProg ω (.assign 35 (.load (.reg 18))) st1 .normal st1a 3 :=
        runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1_r 18 (by omega), hInv.hr18, hCTag],
          rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w pProg ω (.assign 29 (.load (.bin .add (.reg 18) (.const 1)))) st1a .normal st1b 5 :=
        runs_assign_iff.mpr ⟨S_list.length,
          by simp [Expr.eval, BinOp.eval, st1a, h1_r 18 (by omega), hInv.hr18, hw1,
               (by omega : g.coreOutAddr + 1 < 2 ^ w), hLenS], rfl, rfl, by simp [Expr.size]⟩
      have ha3 : Runs w pProg ω (.assign 30 (.bin .add (.reg 18) (.const 2))) st1b .normal st2 4 :=
        runs_assign_iff.mpr ⟨g.coreOutAddr + 2,
          by simp [Expr.eval, BinOp.eval, st1b, st1a, h1_r 18 (by omega), hInv.hr18, hw2,
               (by omega : g.coreOutAddr + 2 < 2 ^ w)], rfl, rfl, by simp [Expr.size]⟩
      exact runs_seq_iff.mpr (Or.inr ⟨st1a, 3, 10, ha1,
        runs_seq_iff.mpr (Or.inr ⟨st1b, 5, 4, ha2, ha3, rfl⟩), rfl⟩)
    have hInjCall := runs_call_of_meetsContract (r := 26) (p := pProg) (w := w)
      (st := st2) (args := [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26])
      (vs := [e, S_list.length, g.coreOutAddr + 2, g.pairsAddr, h1]) hSub.hInj
      (by simp [evalArgs, Expr.eval, st2, h1_r 0 (by omega), hInv.hr0,
            h1_r 19 (by omega), hInv.hr19, h1_26])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨e, S_list.length, g.coreOutAddr + 2, g.pairsAddr, h1, S_list, rfl, rfl, hndS,
        fun p hp => Finset.mem_range.mp (hSV (hfinS ▸ List.mem_toFinset.mpr hp)),
        hListS, hZero1, by omega, by omega, Or.inr (by omega),
        by unfold buildInjPairSpace; omega, by omega⟩ ω
    rcases hInjCall with ⟨st3, c3, h3, hrun3, hpost3, h3_26, h3_other, hc3⟩
    dsimp only [buildInjPairContract, st2, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hpost3 hc3
    rw [readList_eq_of_listAt hListS] at hpost3
    rcases hpost3 with ⟨hh3_eq, hZero3, hndA, hfinA, hSP3, hFrame3⟩
    set A_list := (Finset.range (2 * e) \ S_list.toFinset).sort (· ≤ ·)
    have hA_fin : A_list.toFinset = Finset.range (2 * e) \ S := by rw [hfinA, hfinS]
    have hA_card : A_list.toFinset.card = 2 * e - S.card := by
      rw [hA_fin]; have := Finset.card_sdiff_add_card_eq_card hSV; rw [Finset.card_range] at this; omega
    have hS_le : S.card ≤ 2 * e := by
      simpa [Finset.card_range] using Finset.card_le_card hSV
    have hAB_len : A_list.length + S_list.length ≤ 2 * e := by
      rw [← List.toFinset_card_of_nodup hndA, ← List.toFinset_card_of_nodup hndS, hA_card, hfinS]; omega
    obtain ⟨hrt_spec, hrt_cost⟩ := hroute_step (Finset.range (2 * e) \ S) S
      Finset.sdiff_subset hSV disjoint_sdiff_self_left (by rw [← hA_fin, hA_card]; omega)
    have hcc_rb : cCore + routeCost g.Hhat g.Hhat.verts [(Finset.range (2 * e) \ S, S)] 10
        (LParam M) (bOut ParamConfig.default M) z + 4 * e ≤ rb := by
      unfold rb outerGameRoundBudget; omega
    have hcc_le : cCore + routeCost g.Hhat g.Hhat.verts [(A_list.toFinset, S_list.toFinset)] 10
        (LParam M) (bOut ParamConfig.default M) z ≤ lc := by
      rw [hA_fin, hfinS]; omega
    have hPost := gamePostPair_runs g hSub mem₀ ω hwb hw16 hInv lc cCore hSpace 1 A_list S_list st3
      (Or.inr rfl) hndA hndS (by rw [hA_fin]; exact Finset.sdiff_subset) (by rw [hfinS]; exact hSV)
      (by rw [hA_fin, hfinS]; exact disjoint_sdiff_self_left)
      (by rw [hA_card, hfinS]; omega) (by rw [hA_card]; omega) hAB_len hSP3
      (fun i hi => by
        have hi' : i < 2 + 2 * g.Hhat.m := by rw [graph_encode_length] at hi; exact hi
        rw [hFrame3 _ (by have := g.hpgH; omega) (Or.inl (by have := g.hpgH; omega))]; exact h1_pg i hi)
      ⟨by rw [hFrame3 _ (by omega) (Or.inl (by omega))]; exact h1_xPort.1,
       fun j hj => by rw [hFrame3 _ (by simp at hj; omega) (Or.inl (by simp at hj; omega))]; exact h1_xPort.2 j hj⟩
      (fun i hi => by
        have hi' : i < 2 + 2 * W_edges.length := by rw [graph_encode_length] at hi; simpa [Graph.m] using hi
        rw [hFrame3 _ (by omega) (Or.inl (by omega))]; exact h1_W i hi)
      (fun j hj => by
        have hj' : j < F_edges.length := hj
        rw [hFrame3 _ (by omega) (Or.inl (by omega)), hFrame3 _ (by omega) (Or.inl (by omega))]
        exact h1_F j hj)
      (by simpa [h3_26] using hZero3) (by rw [h3_26, hh3_eq]; unfold buildInjPairSpace; omega)
      (by rw [h3_26, hh3_eq]; unfold buildInjPairSpace; omega) hcc_le
      (fun a ha => by rw [hFrame3 a (by omega) (Or.inl (by omega)), hFrame1 a (by omega) (Or.inl (by omega))]; exact hInv.hFrame a ha)
      (by rw [h3_other 35 (by omega)]; simp [st2])
      (fun r' hr' => by rw [h3_other r' (by omega)]; simp [st2, Function.update_of_ne (by omega : r' ≠ 30),
        Function.update_of_ne (by omega : r' ≠ 29), Function.update_of_ne (by omega : r' ≠ 35), h1_r r' (by omega)])
    rcases hPost with ⟨oR, stR, cR, hrunR, hqR⟩
    have hcond35 : Runs w pProg ω
        (.cond (.reg 35)
          (.call 26 idx.bInj [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26])
          (.call 26 idx.bPad [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26]))
        st2 .normal st3 (1 + c3 + 1) :=
      runs_cond_iff.mpr ⟨1, c3, by simp [Expr.eval, st2],
        by simp only [one_ne_zero, ↓reduceIte]; exact hrun3, by simp [Expr.size]⟩
    have hrunB := runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
      runs_seq_iff.mpr (Or.inr ⟨st2, 14, _, hLoadC,
        runs_seq_iff.mpr (Or.inr ⟨st3, 1 + c3 + 1, cR, hcond35, hrunR, rfl⟩), rfl⟩), rfl⟩)
    rw [hA_fin, hfinS] at hqR
    refine ⟨oR, stR, _, hrunB, Or.inl ?_⟩
    cases hrt' : route g.Hhat g.Hhat.verts [(Finset.range (2 * e) \ S, S)] 10 (LParam M) (bOut ParamConfig.default M) z with
    | cut U_cut =>
      rw [hrt'] at hqR hrt_spec
      rcases hqR with ⟨h', rfl, hO, hge', hle', hZ', hF', hcR⟩
      refine ⟨h', .cut U_cut, rfl, hO, hrt_spec, hge', hle', hZ', hF', ?_⟩
      simp [argsSize, Expr.size, buildInjPairCost] at hc3
      have := hround_cost_aux _ hcc_rb
      dsimp only [z, rb] at this ⊢; omega
    | matched ms emb_inj =>
      rw [hrt'] at hqR hrt_spec
      simp only [↓reduceIte] at hqR
      rcases hqR with ⟨h', rfl, hO, hge', hle', hZ', hF', hcR⟩
      have hWSpec := gameMathInv_expander_witness g.hHhat_n hk1_le_t hMath hSV hS2 hSexp hrt_spec
      refine ⟨h', _, rfl, hO, hWSpec, hge', hle', hZ', hF', ?_⟩
      simp [argsSize, Expr.size, buildInjPairCost] at hc3
      have := hround_cost_aux _ hcc_rb
      dsimp only [z, rb] at this ⊢; omega
  | cut U =>
    rcases hCoreOut with ⟨hCTag, U_list, hndU, hfinU, hLenU, hListU⟩
    obtain ⟨hUV, hU1, hU2, hUcut⟩ := hcore_spec
    change U ⊆ Finset.range (2 * e) at hUV
    change 2 * e ≤ 4 * U.card at hU1
    change 2 * e ≤ 4 * (Finset.range (2 * e) \ U).card at hU2
    change 100 * W.cut U ≤ 2 * e at hUcut
    have hUlen_le : U_list.length ≤ 2 * e := by
      have := Finset.card_le_card hUV
      rw [← hfinU, List.toFinset_card_of_nodup hndU, Finset.card_range] at this; exact this
    let st2 : State :=
      { st1 with regs := Function.update (Function.update (Function.update st1.regs 35 0) 29 U_list.length) 30 (g.coreOutAddr + 2) }
    have hLoadC : Runs w pProg ω
        (.assign 35 (.load (.reg 18)) ;;
         .assign 29 (.load (.bin .add (.reg 18) (.const 1))) ;;
         .assign 30 (.bin .add (.reg 18) (.const 2))) st1 .normal st2 14 := by
      let st1a : State := { st1 with regs := Function.update st1.regs 35 0 }
      let st1b : State := { st1a with regs := Function.update st1a.regs 29 U_list.length }
      have ha1 : Runs w pProg ω (.assign 35 (.load (.reg 18))) st1 .normal st1a 3 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h1_r 18 (by omega), hInv.hr18, hCTag],
          rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w pProg ω (.assign 29 (.load (.bin .add (.reg 18) (.const 1)))) st1a .normal st1b 5 :=
        runs_assign_iff.mpr ⟨U_list.length,
          by simp [Expr.eval, BinOp.eval, st1a, h1_r 18 (by omega), hInv.hr18, hw1,
               (by omega : g.coreOutAddr + 1 < 2 ^ w), hLenU], rfl, rfl, by simp [Expr.size]⟩
      have ha3 : Runs w pProg ω (.assign 30 (.bin .add (.reg 18) (.const 2))) st1b .normal st2 4 :=
        runs_assign_iff.mpr ⟨g.coreOutAddr + 2,
          by simp [Expr.eval, BinOp.eval, st1b, st1a, h1_r 18 (by omega), hInv.hr18, hw2,
               (by omega : g.coreOutAddr + 2 < 2 ^ w)], rfl, rfl, by simp [Expr.size]⟩
      exact runs_seq_iff.mpr (Or.inr ⟨st1a, 3, 10, ha1,
        runs_seq_iff.mpr (Or.inr ⟨st1b, 5, 4, ha2, ha3, rfl⟩), rfl⟩)
    have hPadCall := runs_call_of_meetsContract (r := 26) (p := pProg) (w := w)
      (st := st2) (args := [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26])
      (vs := [e, U_list.length, g.coreOutAddr + 2, g.pairsAddr, h1]) hSub.hPad
      (by simp [evalArgs, Expr.eval, st2, h1_r 0 (by omega), hInv.hr0,
            h1_r 19 (by omega), hInv.hr19, h1_26])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨e, U_list.length, g.coreOutAddr + 2, g.pairsAddr, h1, U_list, rfl, rfl, hndU,
        fun p hp => Finset.mem_range.mp (hUV (hfinU ▸ List.mem_toFinset.mpr hp)),
        hListU, hZero1, by omega, by omega, Or.inr (by omega),
        by unfold padToBisectionSpace; omega, by omega⟩ ω
    rcases hPadCall with ⟨st3, c3, h3, hrun3, hpost3, h3_26, h3_other, hc3⟩
    dsimp only [padToBisectionContract, st2, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hpost3 hc3
    rw [readList_eq_of_listAt hListU, hfinU] at hpost3
    rcases hpost3 with ⟨hh3_eq, hZero3, ⟨A_list, B_list, hndA, hndB, hAlen, hBlen, _, _, hAB_eq, hSP3⟩, hFrame3⟩
    have hPadSpec := padToBisection_spec hUV hU1 hU2
    have hA_eq : A_list.toFinset = (padToBisection e U).1 := congrArg Prod.fst hAB_eq
    have hB_eq : B_list.toFinset = (padToBisection e U).2 := congrArg Prod.snd hAB_eq
    obtain ⟨hrt_spec, hrt_cost⟩ := hroute_step (padToBisection e U).1 (padToBisection e U).2
      hPadSpec.2.2.2.1 hPadSpec.2.2.2.2.1 hPadSpec.2.2.2.2.2.1
      (by dsimp only [padToBisection]; rw [hPadSpec.2.2.2.2.2.2.2.1, hPadSpec.2.2.2.2.2.2.2.2.1])
    have hcc_rb : cCore + routeCost g.Hhat g.Hhat.verts [((padToBisection e U).1, (padToBisection e U).2)] 10
        (LParam M) (bOut ParamConfig.default M) z + 4 * e ≤ rb := by
      unfold rb outerGameRoundBudget; omega
    have hcc_le : cCore + routeCost g.Hhat g.Hhat.verts [(A_list.toFinset, B_list.toFinset)] 10
        (LParam M) (bOut ParamConfig.default M) z ≤ lc := by
      rw [hA_eq, hB_eq]; omega
    have hPost := gamePostPair_runs g hSub mem₀ ω hwb hw16 hInv lc cCore hSpace 0 A_list B_list st3
      (Or.inl rfl) hndA hndB
      (by rw [hA_eq]; exact hPadSpec.2.2.2.1) (by rw [hB_eq]; exact hPadSpec.2.2.2.2.1)
      (by rw [hA_eq, hB_eq]; exact hPadSpec.2.2.2.2.2.1)
      (by rw [hA_eq, hB_eq]; dsimp only [padToBisection]; rw [hPadSpec.2.2.2.2.2.2.2.1, hPadSpec.2.2.2.2.2.2.2.2.1])
      (by rw [hA_eq]; dsimp only [padToBisection]; rw [hPadSpec.2.2.2.2.2.2.2.1]) (by omega) hSP3
      (fun i hi => by
        have hi' : i < 2 + 2 * g.Hhat.m := by rw [graph_encode_length] at hi; exact hi
        rw [hFrame3 _ (by have := g.hpgH; omega) (Or.inl (by have := g.hpgH; omega))]; exact h1_pg i hi)
      ⟨by rw [hFrame3 _ (by omega) (Or.inl (by omega))]; exact h1_xPort.1,
       fun j hj => by rw [hFrame3 _ (by simp at hj; omega) (Or.inl (by simp at hj; omega))]; exact h1_xPort.2 j hj⟩
      (fun i hi => by
        have hi' : i < 2 + 2 * W_edges.length := by rw [graph_encode_length] at hi; simpa [Graph.m] using hi
        rw [hFrame3 _ (by omega) (Or.inl (by omega))]; exact h1_W i hi)
      (fun j hj => by
        have hj' : j < F_edges.length := hj
        rw [hFrame3 _ (by omega) (Or.inl (by omega)), hFrame3 _ (by omega) (Or.inl (by omega))]
        exact h1_F j hj)
      (by simpa [h3_26] using hZero3) (by rw [h3_26, hh3_eq]; unfold padToBisectionSpace; omega)
      (by rw [h3_26, hh3_eq]; unfold padToBisectionSpace; omega) hcc_le
      (fun a ha => by rw [hFrame3 a (by omega) (Or.inl (by omega)), hFrame1 a (by omega) (Or.inl (by omega))]; exact hInv.hFrame a ha)
      (by rw [h3_other 35 (by omega)]; simp [st2])
      (fun r' hr' => by rw [h3_other r' (by omega)]; simp [st2, Function.update_of_ne (by omega : r' ≠ 30),
        Function.update_of_ne (by omega : r' ≠ 29), Function.update_of_ne (by omega : r' ≠ 35), h1_r r' (by omega)])
    rcases hPost with ⟨oR, stR, cR, hrunR, hqR⟩
    have hcond35 : Runs w pProg ω
        (.cond (.reg 35)
          (.call 26 idx.bInj [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26])
          (.call 26 idx.bPad [.reg 0, .reg 29, .reg 30, .reg 19, .reg 26]))
        st2 .normal st3 (1 + c3 + 1) :=
      runs_cond_iff.mpr ⟨0, c3, by simp [Expr.eval, st2],
        by simp only [↓reduceIte]; exact hrun3, by simp [Expr.size]⟩
    have hrunB := runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
      runs_seq_iff.mpr (Or.inr ⟨st2, 14, _, hLoadC,
        runs_seq_iff.mpr (Or.inr ⟨st3, 1 + c3 + 1, cR, hcond35, hrunR, rfl⟩), rfl⟩), rfl⟩)
    rw [hA_eq, hB_eq] at hqR
    refine ⟨oR, stR, _, hrunB, ?_⟩
    cases hrt' : route g.Hhat g.Hhat.verts [((padToBisection e U).1, (padToBisection e U).2)] 10 (LParam M) (bOut ParamConfig.default M) z with
    | cut U_cut =>
      rw [hrt'] at hqR hrt_spec
      rcases hqR with ⟨h', rfl, hO, hge', hle', hZ', hF', hcR⟩
      refine Or.inl ⟨h', .cut U_cut, rfl, hO, hrt_spec, hge', hle', hZ', hF', ?_⟩
      simp [argsSize, Expr.size, padToBisectionCost] at hc3
      have := hround_cost_aux _ hcc_rb
      dsimp only [z, rb] at this ⊢; omega
    | matched ms emb_k =>
      rw [hrt'] at hqR hrt_spec
      simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hqR
      rcases hqR with ⟨rfl, hInv', hge', hle', hcR⟩
      obtain ⟨M_hist', hMath'⟩ := gameMathInv_bisection_step g.hHhat_n hMath hUV hU1 hU2 hUcut hrt_spec
      refine Or.inr ⟨ms.getD 0 [], fakeCompletion (padToBisection e U).1 (padToBisection e U).2 (ms.getD 0 []),
        M_hist', rfl, hInv', hMath', hge', ?_, ?_⟩
      · have hsum_le : cCore + routeCost g.Hhat g.Hhat.verts [((padToBisection e U).1, (padToBisection e U).2)] 10
            (LParam M) (bOut ParamConfig.default M) z + 1 ≤ rb + 1 := by omega
        have hmul_le := Nat.mul_le_mul_left (C_sp * coreSpaceBase M r) hsum_le
        dsimp only [z, rb] at hle' hmul_le ⊢; omega
      · simp [argsSize, Expr.size, padToBisectionCost] at hc3
        have := hround_cost_aux _ hcc_rb
        dsimp only [z, rb] at this ⊢; omega

/-- Inductive execution of the `outerGameProc` loop + fallback cut return, delivering an outcome
satisfying `OuterGameOutcomeSpec ParamConfig.default M r e g.Hhat res`. -/
private lemma gameLoop_runs {M r e pgAddr outResAddr h w C_core C_rt C_sp_core C_sp_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterGameIndices}
    {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    (g : GameGeom ParamConfig.default M r e pgAddr outResAddr h)
    (hSub : OuterGameSubprocs M r w pProg idx coreCost route routeCost C_core C_rt C_sp_core C_sp_rt C_sp routeC)
    (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hrl : r ≤ ell M)
    (hwb : bOut ParamConfig.default M < 2 ^ w) (hwM : M < 2 ^ w) (hwR : r < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    ∀ fuel k M_hist W_edges F_edges st,
      GameLoopInv g mem₀ fuel k W_edges F_edges st →
      GameMathInv M r e (e / DOut ParamConfig.default M r) g.Hhat M_hist k W_edges F_edges →
      let lc := fuel * outerGameRoundBudget ParamConfig.default M r routeC e
      st.regs 26 + outerGameLoopSpace C_sp M r e fuel lc < 2 ^ w →
      ∃ h' st' c res,
        Runs w pProg ω
          (.loop (.bin .lt (.const 0) (.reg 27)) (gameRoundBodyStmt idx) ;;
           (.store (.reg 3) (.const 0) ;;
            .store (.bin .add (.reg 3) (.const 1)) (.const 0) ;;
            .store (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 20) (.const 2)) ;;
            .ret (.reg 26)))
          st (.returned h') st' c ∧
        OuterGameOutAt st'.mem outResAddr h h' e res ∧
        OuterGameOutcomeSpec ParamConfig.default M r e g.Hhat res ∧
        st.regs 26 ≤ h' ∧
        h' ≤ st.regs 26 + outerGameLoopSpace C_sp M r e fuel lc ∧
        ZeroFrom st'.mem h' ∧
        (∀ a < h, (a < outResAddr ∨ outResAddr + 4 ≤ a) → st'.mem a = mem₀ a) ∧
        c ≤ outerGameCostFactor C_core C_rt * lc + 80 := by
  have hw1 : 1 < 2 ^ w := by omega
  intro fuel
  induction fuel with
  | zero =>
    intro k M_hist W_edges F_edges st hInv hMath _ _
    exfalso
    have hk_eq : k = 49 * LParam M + 1 := by have := hInv.hk_fuel; simp [GameGeom.F] at this; omega
    have hVne : (Finset.range (2 * e)).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_range]; have := g.he_pos; omega)
    have hVL : (Finset.range (2 * e)).card < 2 ^ LParam M := by
      rw [Finset.card_range]; exact g.h2e_L
    have hlt := round_bound_nat (n := 2 * e) hVne hVL hMath.hM_perf hMath.hM_cut
    omega
  | succ fuel ih =>
    intro k M_hist W_edges F_edges st hInv hMath lc hSpace
    have he_pos : 1 ≤ e := g.he_pos
    set rb := outerGameRoundBudget ParamConfig.default M r routeC e
    rcases gameRoundBody_runs g hSub mem₀ ω hrl hwb hwM hwR hw16 hInv hMath hSpace with
      ⟨oB, stB, cB, hrunB, hqB⟩
    have hguard : (Expr.bin .lt (.const 0) (.reg 27)).eval w st = some 1 := by
      simp [Expr.eval, BinOp.eval, hInv.hr27, hw1, (by omega : 0 < 2 ^ w)]
    rcases hqB with ⟨h', res, rfl, hO, hSpec, hge', hle', hZ', hF', hcB⟩ |
      ⟨M_k, F_k, M_hist', rfl, hInv', hMath', hge', hle', hcB⟩
    · have hlp := runs_loop_iff.mpr (Or.inr (Or.inl ⟨1, h', cB, hguard, by decide, hrunB, rfl, rfl⟩))
      refine ⟨h', stB, _, res, runs_seq_iff.mpr (Or.inl ⟨h', _, hlp, rfl, rfl⟩), hO, hSpec, hge', hle', hZ', hF', ?_⟩
      have hrb_lc : rb ≤ lc := Nat.le_mul_of_pos_left rb (Nat.succ_pos fuel)
      have hmul_le := Nat.mul_le_mul_left (outerGameCostFactor C_core C_rt) hrb_lc
      change cB ≤ outerGameCostFactor C_core C_rt * rb - 10 at hcB
      simp [Expr.size]; omega
    · set lcNext := fuel * rb
      have hSpaceNext : stB.regs 26 + outerGameLoopSpace C_sp M r e fuel lcNext ≤
          st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc := by
        unfold outerGameLoopSpace
        set B := coreSpaceBase M r
        have hlc_eq : lc = rb + lcNext := by
          dsimp only [lc, lcNext]; rw [Nat.succ_mul]; ring
        have h1 : C_sp * B * (lc + (fuel + 1)) =
            C_sp * B * (rb + 1) + C_sp * B * (lcNext + fuel) := by
          rw [hlc_eq]; ring
        have h2 : (fuel + 1) * (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) =
            (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) +
              fuel * (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) := by ring
        rw [h1, h2]; linarith
      rcases ih (k + 1) M_hist' (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k) stB hInv' hMath'
          (lt_of_le_of_lt hSpaceNext hSpace) with
        ⟨h', st', cNext, res, hrunNext, hO', hSpec', hge'', hle'', hZ', hF', hcNext⟩
      change h' ≤ stB.regs 26 + outerGameLoopSpace C_sp M r e fuel lcNext at hle''
      change cNext ≤ outerGameCostFactor C_core C_rt * lcNext + 80 at hcNext
      change cB ≤ outerGameCostFactor C_core C_rt * rb - 10 at hcB
      have hposF : 10 ≤ outerGameCostFactor C_core C_rt * rb := by
        have hrb4 : 4 ≤ rb := by unfold rb outerGameRoundBudget; omega
        have : 2000 * 4 ≤ outerGameCostFactor C_core C_rt * rb :=
          Nat.mul_le_mul (by unfold outerGameCostFactor; omega) hrb4
        omega
      have hlc_mul : outerGameCostFactor C_core C_rt * lc =
          outerGameCostFactor C_core C_rt * rb + outerGameCostFactor C_core C_rt * lcNext := by
        dsimp only [lc, lcNext]; rw [Nat.succ_mul]; ring
      rcases runs_seq_iff.mp hrunNext with ⟨v, cL, hlp', hret, rfl⟩ | ⟨stL, cL, cF, hlp', hfb', rfl⟩
      · injection hret with hv; subst hv
        have hlpTot := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stB, cB, cL, hguard, by decide, hrunB, hlp', rfl⟩))
        refine ⟨h', st', _, res, runs_seq_iff.mpr (Or.inl ⟨h', _, hlpTot, rfl, rfl⟩),
          hO', hSpec', by omega, by omega, hZ', hF', ?_⟩
        simp [Expr.size]; omega
      · have hlpTot := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stB, cB, cL, hguard, by decide, hrunB, hlp', rfl⟩))
        have hsqTot := runs_seq_iff.mpr (Or.inr ⟨stL, _, cF, hlpTot, hfb', rfl⟩)
        refine ⟨h', st', _, res, hsqTot, hO', hSpec', by omega, by omega, hZ', hF', ?_⟩
        simp [Expr.size]; omega

/-! ## 5. Main Specification of `outerGameProc` -/

/-- Initialization prefix of `outerGameProc`: loads params, computes `q = coreLevel`, allocates
buffers, initializes `xPort` and `W`, establishing `GameLoopInv` at `k = 0, fuel = 49 * L + 1`. -/
private lemma gameInit_runs {cfg : ParamConfig} {M r n e pgAddr paramAddr outResAddr h w : ℕ}
    {pProg : Program} {bCoreLevel : ℕ}
    (g : GameGeom cfg M r e pgAddr outResAddr h)
    (hCoreLevel : MeetsContract w pProg bCoreLevel (coreLevelContract w))
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hPg : GraphAt mem pgAddr g.Hhat)
    (hPB : OuterParamBlockAt mem paramAddr cfg n M r)
    (hDpos : 0 < DOut cfg M r)
    (hZero : ZeroFrom mem h)
    (hparH : paramAddr + 12 ≤ h)
    (hBuf_w : h + outerGameBufSpace M e < 2 ^ w)
    (hN2e_w : NOf M r * (2 * e) + 16 < 2 ^ w)
    (hw16 : 16 < 2 ^ w) :
    ∃ st4 cInit,
      Runs w pProg ω
        (gameLoadParamsStmt ;;
         .call 14 bCoreLevel [.reg 8, .reg 12] ;;
         gameAllocBufsStmt ;;
         gameInitBufsStmt)
        (startState [e, pgAddr, paramAddr, outResAddr, h] mem pos) .normal st4 cInit ∧
      GameLoopInv g mem (49 * LParam M + 1) 0 [] [] st4 ∧
      st4.regs 26 = h + outerGameBufSpace M e ∧
      cInit ≤ 40 * r + 60 * e + 320 := by
  have he_pos := g.he_pos
  have hN2 := g.hN2
  have hq_le_r : coreLevel M r (2 * e) ≤ r := coreLevel_le (M := M) (r := r) g.h2e_pow
  set st0 := startState [e, pgAddr, paramAddr, outResAddr, h] mem pos
  have hT1 := gameLoadParams_triple (cfg := cfg) (w := w) (n := n) (M := M) (r := r) (e := e)
    (paramAddr := paramAddr) pProg st0 rfl rfl hPB (by omega)
    (by unfold outerGameBufSpace at hBuf_w; omega) hDpos st0 ω rfl
  rcases hT1 with ⟨o1, st1, c1, hrun1, hq1, hc1⟩
  cases o1 with
  | returned _ => exact False.elim hq1
  | normal =>
    rcases hq1 with ⟨h1_mem, h1_5, h1_6, h1_7, h1_8, h1_9, h1_10, h1_11, h1_12, h1_13, h1_r⟩
    have hCall2 := runs_call_of_meetsContract (r := 14) (p := pProg) (w := w) (st := st1)
      (args := [.reg 8, .reg 12]) (vs := [NOf M r, 2 * e]) hCoreLevel
      (by simp [evalArgs, Expr.eval, h1_8, h1_12])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · have : NOf M r ≤ NOf M r * (2 * e) := Nat.le_mul_of_pos_right _ (by omega); omega
          · unfold outerGameBufSpace at hBuf_w; omega)
      ⟨NOf M r, 2 * e, rfl, hN2, by omega, hN2e_w⟩ ω
    rcases hCall2 with ⟨st2, c2, qVal, hrun2, hpost2, h2_14, h2_other, hc2⟩
    simp only [coreLevelContract, List.getD_cons_zero, List.getD_cons_succ] at hpost2 hc2
    rcases hpost2 with ⟨hqVal, hmem2⟩
    have h2_r : ∀ r' ≤ 13, st2.regs r' = st1.regs r' := fun r' hr' => h2_other r' (by omega)
    have h2_mem : st2.mem = mem := by rw [hmem2, h1_mem]; rfl
    have hT3 := gameAllocBufs_triple (w := w) (M := M) (e := e) (h := h) pProg st2
      (by rw [h2_r 4 (by omega), h1_r 4 (by omega)]; rfl)
      (by rw [h2_r 11 (by omega), h1_11])
      (by rw [h2_r 12 (by omega), h1_12]) hBuf_w hw16 st2 ω rfl
    rcases hT3 with ⟨o3, st3, c3, hrun3, hq3, hc3⟩
    cases o3 with
    | returned _ => exact False.elim hq3
    | normal =>
      rcases hq3 with ⟨h3_mem, h3_15, h3_16, h3_17, h3_18, h3_19, h3_20, h3_21, h3_22, h3_23,
        h3_24, h3_25, h3_26, h3_27, hInit_eq, h3_r⟩
      have h3_mem0 : st3.mem = mem := by rw [h3_mem, h2_mem]
      have hT4 := gameInitBufs_triple (w := w) (e := e) (xPortAddr := g.xPortAddr) (wAddr := g.wAddr)
        pProg st3 (by rw [h3_r 12 (by omega), h2_r 12 (by omega), h1_12]) h3_15 h3_16
        (Or.inl (by simp only [GameGeom.xPortAddr, GameGeom.wAddr]; omega))
        (by simp only [GameGeom.xPortAddr, outerGameBufSpace] at hBuf_w ⊢; omega)
        (by simp only [GameGeom.wAddr, outerGameBufSpace] at hBuf_w ⊢; omega) hw16 st3 ω rfl
      rcases hT4 with ⟨o4, st4, c4, hrun4, hq4, hc4⟩
      cases o4 with
      | returned _ => exact False.elim hq4
      | normal =>
        rcases hq4 with ⟨h4_xPort, h4_W, h4_fr, h4_kr⟩
        have h4_r2 : ∀ r' ≤ 14, st4.regs r' = st2.regs r' := fun r' hr' => by
          rw [h4_kr r' (by omega), h3_r r' hr']
        have h4_26 : st4.regs 26 = h + outerGameBufSpace M e := by
          rw [h4_kr 26 (by decide), h3_26, hInit_eq]
        have hx_le_buf : g.xPortAddr + 1 + 2 * e ≤ h + outerGameBufSpace M e := by
          simp only [GameGeom.xPortAddr, outerGameBufSpace]; omega
        have hw_le_buf : g.wAddr + 2 ≤ h + outerGameBufSpace M e := by
          simp only [GameGeom.wAddr, outerGameBufSpace]; omega
        have hh_le_x : h ≤ g.xPortAddr := le_rfl
        have hh_le_w : h ≤ g.wAddr := by simp only [GameGeom.wAddr]; omega
        have h4_zero : ZeroFrom st4.mem (st4.regs 26) := fun a ha => by
          rw [h4_26] at ha
          rw [h4_fr a (Or.inr (le_trans hx_le_buf ha)) (Or.inr (le_trans hw_le_buf ha)), h3_mem0]
          exact hZero a (le_trans (Nat.le_add_right h _) ha)
        have h4_pg : GraphAt st4.mem pgAddr g.Hhat := fun i hi => by
          have hi' : i < 2 + 2 * g.Hhat.m := by rw [graph_encode_length] at hi; exact hi
          have hlt : pgAddr + i < h := lt_of_lt_of_le (by omega) g.hpgH
          rw [h4_fr _ (Or.inl (lt_of_lt_of_le hlt hh_le_x)) (Or.inl (lt_of_lt_of_le hlt hh_le_w)), h3_mem0]
          exact hPg i hi
        have h4_frame : ∀ a < h, st4.mem a = mem a := fun a ha => by
          rw [h4_fr a (Or.inl (lt_of_lt_of_le ha hh_le_x)) (Or.inl (lt_of_lt_of_le ha hh_le_w)), h3_mem0]
        have h4_inv : GameLoopInv g mem (49 * LParam M + 1) 0 [] [] st4 :=
          { hk_fuel := by simp only [GameGeom.F, Nat.zero_add],
            hW_len := by simp, hF_len := by simp,
            hW_val := (fun _ he => by cases he),
            hW_loop := (fun _ he => by cases he),
            hW_deg := (fun _ _ => by simp [Graph.deg, Graph.degIn, Graph.inside]),
            hr0 := by rw [h4_r2 0 (by decide), h2_r 0 (by decide), h1_r 0 (by decide)]; rfl,
            hr1 := by rw [h4_r2 1 (by decide), h2_r 1 (by decide), h1_r 1 (by decide)]; rfl,
            hr3 := by rw [h4_r2 3 (by decide), h2_r 3 (by decide), h1_r 3 (by decide)]; rfl,
            hr5 := by rw [h4_r2 5 (by decide), h2_r 5 (by decide), h1_5],
            hr6 := by rw [h4_r2 6 (by decide), h2_r 6 (by decide), h1_6],
            hr7 := by rw [h4_r2 7 (by decide), h2_r 7 (by decide), h1_7],
            hr9 := by rw [h4_r2 9 (by decide), h2_r 9 (by decide), h1_9],
            hr11 := by rw [h4_r2 11 (by decide), h2_r 11 (by decide), h1_11]; rfl,
            hr12 := by rw [h4_r2 12 (by decide), h2_r 12 (by decide), h1_12],
            hr13 := by rw [h4_r2 13 (by decide), h2_r 13 (by decide), h1_13],
            hr14 := by unfold coreLevel; rw [h4_r2 14 (by decide), h2_14, hqVal],
            hr15 := by rw [h4_kr 15 (by decide), h3_15]; rfl,
            hr16 := by rw [h4_kr 16 (by decide), h3_16]; rfl,
            hr17 := by rw [h4_kr 17 (by decide), h3_17]; rfl,
            hr18 := by rw [h4_kr 18 (by decide), h3_18]; rfl,
            hr19 := by rw [h4_kr 19 (by decide), h3_19]; rfl,
            hr20 := by rw [h4_kr 20 (by decide), h3_20]; rfl,
            hr21 := by rw [h4_kr 21 (by decide), h3_21]; rfl,
            hr22 := by rw [h4_kr 22 (by decide), h3_22]; rfl,
            hr23 := by rw [h4_kr 23 (by decide), h3_23]; rfl,
            hr24 := by rw [h4_kr 24 (by decide), h3_24]; rfl,
            hr25 := by rw [h4_kr 25 (by decide), h3_25]; rfl,
            hr27 := by rw [h4_kr 27 (by decide), h3_27],
            hhInit := by rw [h4_26, g.hInit_eq],
            hZero := h4_zero, hPg := h4_pg, hXPort := h4_xPort, hW_g := h4_W,
            hF_e := fun j hj => by simp at hj,
            hFrame := h4_frame }
        have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
          runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
            runs_seq_iff.mpr (Or.inr ⟨st3, c3, c4, hrun3, hrun4, rfl⟩), rfl⟩), rfl⟩)
        refine ⟨st4, _, hrun, h4_inv, h4_26, ?_⟩
        · dsimp at hc1 hc3 hc4
          simp only [coreLevelProcCost, argsSize, Expr.size] at hc2
          have hclog : Nat.clog (NOf M r) (2 * e) ≤ r := hq_le_r
          omega

/-- Specification of `outerGameProc idx`: meets the existential `outerGameContract` against
`OuterGameOutcomeSpec` and `outerGameMaxCost`. -/
theorem outerGameProc_spec {M r w C_core C_rt C_sp_core C_sp_rt C_sp routeC : ℕ}
    {pProg : Program} {b : ℕ} {idx : OuterGameIndices}
    {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    (hp : pProg.HasAt b [outerGameProc idx])
    (hSub : OuterGameSubprocs M r w pProg idx coreCost route routeCost C_core C_rt C_sp_core C_sp_rt C_sp routeC) :
    MeetsContract w pProg b
      (outerGameContract M r C_core C_rt C_sp routeC w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, e, pgAddr, paramAddr, outResAddr, h, Hhat, rfl,
    hPg, hHhat_n, hHhat_m, hHhat_val, hHhat_loop, hHhat_deg, hPB,
    he_pos, hr_pos, hrl, hN2, h2e_pow, h2e_L, hDpos, hZero, hpgH, hparH, houtH, hdOG, hdOP,
    hSpace, hN2e_w, hwb, hwM, hwR, hw16⟩
  set g : GameGeom ParamConfig.default M r e pgAddr outResAddr h :=
    { Hhat := Hhat, hHhat_n := hHhat_n, hHhat_m := hHhat_m, hHhat_val := hHhat_val,
      hHhat_loop := hHhat_loop, hHhat_deg := hHhat_deg, he_pos := he_pos, hr_pos := hr_pos,
      hN2 := hN2, h2e_pow := h2e_pow, h2e_L := h2e_L, hpgH := hpgH, houtH := houtH, hdOG := hdOG }
  have hBuf_w : h + outerGameBufSpace M e < 2 ^ w := by unfold outerGameSpace at hSpace; omega
  rcases gameInit_runs (n := n) (paramAddr := paramAddr) g hSub.hCoreLevel mem pos ω hPg hPB hDpos hZero hparH hBuf_w hN2e_w hw16 with
    ⟨st4, cInit, hrunInit, h4_inv, h4_26, hcInit⟩
  rcases gameLoop_runs g hSub mem ω hrl hwb hwM hwR hw16 (49 * LParam M + 1) 0 (fun _ => []) [] [] st4
      h4_inv (gameMathInv_zero M r e (e / DOut ParamConfig.default M r) Hhat)
      (by rw [h4_26]; unfold outerGameSpace outerGameMaxCost at hSpace; omega) with
    ⟨h', st', cLoop, res, hrunLoop, hOut, hSpec, hge', hle', hZ', hFr', hcLoop⟩
  -- Reassociate `gameInit_runs` (left-nested or right-nested) with `outerGameProc`
  rcases runs_seq_iff.mp hrunInit with ⟨_, _, _, hno, _⟩ | ⟨st1, c1, c234, hr1, hr234, rfl⟩
  · cases hno
  rcases runs_seq_iff.mp hr234 with ⟨_, _, _, hno, _⟩ | ⟨st2, c2, c34, hr2, hr34, rfl⟩
  · cases hno
  rcases runs_seq_iff.mp hr34 with ⟨_, _, _, hno, _⟩ | ⟨st3, c3, c4, hr3, hr4, rfl⟩
  · cases hno
  have hrunAll : Runs w pProg ω (outerGameProc idx)
      (startState [e, pgAddr, paramAddr, outResAddr, h] mem pos) (.returned h') st'
      (c1 + (c2 + (c3 + (c4 + cLoop + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hr2,
        runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hr3,
          runs_seq_iff.mpr (Or.inr ⟨st4, c4, cLoop, hr4, hrunLoop, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  dsimp only [g] at hOut hSpec hle' hcLoop
  refine ⟨.returned h', st', _, hrunAll, ?_, ?_⟩
  · dsimp only [outerGameContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rw [readGraph_eq_of_graphAt hPg]
    refine ⟨⟨res, hOut, hSpec⟩, by omega, ?_, hZ', hFr'⟩
    unfold outerGameSpace outerGameMaxCost; rw [h4_26] at hle'; omega
  · dsimp only [outerGameContract, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    set lc := outerGameMaxCost ParamConfig.default M r routeC e
    unfold outerGameStepBound
    have hmul : outerGameCostFactor C_core C_rt * (lc + e + 1) =
        outerGameCostFactor C_core C_rt * lc + outerGameCostFactor C_core C_rt * e +
          outerGameCostFactor C_core C_rt := by ring
    have hge_e : 2000 * e ≤ outerGameCostFactor C_core C_rt * e :=
      Nat.mul_le_mul_right e (by unfold outerGameCostFactor; omega)
    have hge_1 : 2000 ≤ outerGameCostFactor C_core C_rt := by unfold outerGameCostFactor; omega
    change cLoop ≤ outerGameCostFactor C_core C_rt * lc + 80 at hcLoop
    omega

end MinCostFlow.ExpanderDecomp
