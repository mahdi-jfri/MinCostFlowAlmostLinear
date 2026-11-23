module

public import MinCostFlow.ExpanderDecomp.OuterProgGameDefs
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Post-Pair Step and Mathematical Invariants for `outerGameProc` (`OuterProgGameStep`)

Proves `gamePostPair_runs` (routing, fake completion, witness/fake append, and early-return /
continuation postconditions) together with the mathematical loop invariant `GameMathInv` and its
inductive maintenance lemmas.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Post-pair execution of one round (router call, cut return or fake-edge completion + witness
append + witness return / fuel decrement). -/
lemma gamePostPair_runs {M r e pgAddr outResAddr h w C_core C_rt C_sp_core C_sp_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterGameIndices}
    {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    (g : GameGeom ParamConfig.default M r e pgAddr outResAddr h)
    (hSub : OuterGameSubprocs M r w pProg idx coreCost route routeCost C_core C_rt C_sp_core C_sp_rt C_sp routeC)
    (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hwb : bOut ParamConfig.default M < 2 ^ w) (hw16 : 16 < 2 ^ w)
    {fuel k : ℕ} {W_edges F_edges : List (ℕ × ℕ)} {st : State}
    (hInv : GameLoopInv g mem₀ (fuel + 1) k W_edges F_edges st)
    (lc cCore : ℕ)
    (hSpace : st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc < 2 ^ w)
    (coreTag : ℕ) (A_list B_list : List ℕ) (st3 : State)
    (htag : coreTag = 0 ∨ coreTag = 1)
    (hndA : A_list.Nodup) (hndB : B_list.Nodup)
    (hA_sub : A_list.toFinset ⊆ Finset.range (2 * e))
    (hB_sub : B_list.toFinset ⊆ Finset.range (2 * e))
    (hdisjAB : Disjoint A_list.toFinset B_list.toFinset)
    (hAB_card : A_list.toFinset.card ≤ B_list.toFinset.card)
    (hA_le : A_list.toFinset.card ≤ e)
    (hAB_len : A_list.length + B_list.length ≤ 2 * e)
    (hSP3 : SinglePairAt st3.mem g.pairsAddr A_list B_list)
    (hPg3 : GraphAt st3.mem pgAddr g.Hhat)
    (hX3 : LenListAt st3.mem g.xPortAddr (List.range (2 * e)))
    (hW3 : GraphAt st3.mem g.wAddr (Graph.mk (2 * e) W_edges))
    (hF3 : EdgesAt st3.mem g.fAddr F_edges)
    (hZero3 : ZeroFrom st3.mem (st3.regs 26))
    (hh3_ge : st.regs 26 ≤ st3.regs 26)
    (hh3_le : st3.regs 26 ≤ st.regs 26 + coreAdapterSpace C_sp_core M r (2 * e) cCore + 2 * e)
    (hcc_le : cCore + routeCost g.Hhat g.Hhat.verts [(A_list.toFinset, B_list.toFinset)] 10
      (LParam M) (bOut ParamConfig.default M) (e / DOut ParamConfig.default M r) ≤ lc)
    (hFr3 : ∀ a < h, st3.mem a = mem₀ a)
    (h3_35 : st3.regs 35 = coreTag)
    (h3_r : ∀ r', r' ≤ 25 ∨ r' = 27 → st3.regs r' = st.regs r') :
    let z := e / DOut ParamConfig.default M r
    let A := A_list.toFinset
    let B := B_list.toFinset
    let cRoute := routeCost g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z
    ∃ oR stR cR,
      Runs w pProg ω
        (.call 26 idx.bRoute [.reg 1, .reg 15, .reg 19, .const 10, .reg 7, .reg 9, .reg 13, .reg 20, .reg 26] ;;
         .assign 28 (.load (.reg 20)) ;;
         .cond (.reg 28)
           gameWriteCutRetStmt
           ((.assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
             .assign 30 (.bin .add (.reg 20) (.const 2))) ;;
            .call 26 idx.bFake [.reg 0, .reg 19, .reg 29, .reg 30, .reg 21, .reg 22, .reg 26] ;;
            gameAppendMatchedStmt ;;
            .cond (.reg 35)
              gameWriteWitRetStmt
              (.assign 27 (.bin .sub (.reg 27) (.const 1)))))
        st3 oR stR cR ∧
      (match route g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z with
      | .cut U_cut =>
        ∃ h', oR = .returned h' ∧
          OuterGameOutAt stR.mem outResAddr h h' e (.cut U_cut) ∧
          st.regs 26 ≤ h' ∧
          h' ≤ st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc ∧
          ZeroFrom stR.mem h' ∧
          (∀ a < h, (a < outResAddr ∨ outResAddr + 4 ≤ a) → stR.mem a = mem₀ a) ∧
          cR ≤ C_rt * cRoute + C_rt + 200
      | .matched ms _ =>
        let M_k := ms.getD 0 []
        let F_k := fakeCompletion A B M_k
        if coreTag = 1 then
          ∃ h', oR = .returned h' ∧
            OuterGameOutAt stR.mem outResAddr h h' e (.witness (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k)) ∧
            st.regs 26 ≤ h' ∧
            h' ≤ st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc ∧
            ZeroFrom stR.mem h' ∧
            (∀ a < h, (a < outResAddr ∨ outResAddr + 4 ≤ a) → stR.mem a = mem₀ a) ∧
            cR ≤ C_rt * cRoute + C_rt + 800 * e + 500
        else
          oR = .normal ∧
            GameLoopInv g mem₀ fuel (k + 1) (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k) stR ∧
            st.regs 26 ≤ stR.regs 26 ∧
            stR.regs 26 ≤ st.regs 26 + C_sp * coreSpaceBase M r * (cCore + cRoute + 1) +
              (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e) ∧
            cR ≤ C_rt * cRoute + C_rt + 800 * e + 500) := by
  intro z A B cRoute
  rcases g.bufOrder with ⟨hb_x, hb_w, hb_we, hb_f, hb_c, hb_p, hb_r, hb_fr, hb_fl, hb_hi⟩
  have hge := g.hInit_eq
  have hInit_le : g.hInit ≤ st.regs 26 := hInv.hhInit
  have he_pos : 1 ≤ e := g.he_pos
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hb2 : 2 ≤ bOut ParamConfig.default M := two_le_bOut' ParamConfig.default M
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw10 : 10 < 2 ^ w := by omega
  have hHhat_verts : g.Hhat.verts = Finset.range (2 * e) := by unfold Graph.verts; rw [g.hHhat_n]
  have hHhat_ins : g.Hhat.inside g.Hhat.verts = g.Hhat.edges := inside_verts_of_isValid g.hHhat_val
  have hRange_fin : (List.range (2 * e)).toFinset = g.Hhat.verts := by
    rw [hHhat_verts]; ext x; simp
  have hvp : ValidTerminalPairs (List.range (2 * e)).toFinset [(A, B)] := by
    rw [hRange_fin, hHhat_verts]
    exact validTerminalPairs_singleton' hA_sub hB_sub hdisjAB hAB_card
  have hF_le_2Fe : g.F ≤ 2 * g.F * e := by
    calc g.F = g.F * 1 := (Nat.mul_one _).symm
      _ ≤ g.F * (2 * e) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * g.F * e := by ring
  have hAuxSp := gamePostPair_space_aux (M := M) (r := r) (e := e) (fuel := fuel)
    (lc := lc) (cCore := cCore) (cRoute := cRoute) hSub.hsp_core hSub.hsp_rt hh3_le hcc_le
  have hRtSpace : st3.regs 26 + outerRouterSpace C_sp_rt g.Hhat.n cRoute + 8 * e ≤
      st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc := by
    rw [g.hHhat_n]; exact le_trans hAuxSp.1 hAuxSp.2
  have hRtSpace_w : st3.regs 26 + outerRouterSpace C_sp_rt g.Hhat.n cRoute < 2 ^ w := by omega
  have hdegIn : ∀ v ∈ (List.range (2 * e)).toFinset, g.Hhat.degIn (List.range (2 * e)).toFinset v ≤ 10 := by
    intro v _; rw [hRange_fin]; exact g.hHhat_deg v
  have hL_w : LParam M < 2 ^ w := by
    have hF_w : 49 * LParam M + 1 ≤ 4 * (49 * LParam M + 1) * e := by
      calc 49 * LParam M + 1 = (49 * LParam M + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (49 * LParam M + 1) * (4 * e) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (49 * LParam M + 1) * e := by ring
    unfold outerGameBufSpace at hge; omega
  have hz_w : z < 2 ^ w := by have := Nat.div_le_self e (DOut ParamConfig.default M r); omega
  have hpg_w : pgAddr < 2 ^ w := by have := g.hpgH; omega
  -- Call bRoute
  have hRouteCall := runs_call_of_meetsContract (r := 26) (p := pProg) (w := w)
    (st := st3) (args := [.reg 1, .reg 15, .reg 19, .const 10, .reg 7, .reg 9, .reg 13, .reg 20, .reg 26])
    (vs := [pgAddr, g.xPortAddr, g.pairsAddr, 10, LParam M, bOut ParamConfig.default M, z, g.routeOutAddr, st3.regs 26])
    hSub.hRouteProg
    (by simp [evalArgs, Expr.eval, h3_r 1 (by omega), hInv.hr1, h3_r 15 (by omega), hInv.hr15,
          h3_r 19 (by omega), hInv.hr19, hw10, h3_r 7 (by omega), hInv.hr7,
          h3_r 9 (by omega), hInv.hr9, h3_r 13 (by omega), hInv.hr13,
          h3_r 20 (by omega), hInv.hr20, z])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨pgAddr, g.xPortAddr, g.pairsAddr, 10, LParam M, bOut ParamConfig.default M, z, g.routeOutAddr, st3.regs 26,
      g.Hhat, List.range (2 * e), A_list, B_list, rfl, hPg3, g.hHhat_val, hX3,
      List.nodup_range, by rw [hRange_fin]; exact Finset.Subset.refl _,
      by rw [hRange_fin, hHhat_ins]; exact g.hHhat_loop, by decide, hdegIn, by omega,
      by rw [hRange_fin, hHhat_verts, Finset.card_range]; exact g.h2e_L,
      hb2, hSP3, hndA, hndB, hvp, hZero3, by have := g.hpgH; omega,
      by simp; omega, by omega, by rw [g.hHhat_n]; omega,
      Or.inr (by have := g.hpgH; omega), Or.inr (by simp; omega), Or.inr (by omega),
      by simpa [cRoute, hRange_fin] using hRtSpace_w, hw16,
      by rw [List.length_range]; have := g.hHhat_m; omega,
      by rw [List.length_range]; have := Nat.div_le_self e (DOut ParamConfig.default M r); omega⟩ ω
  rcases hRouteCall with ⟨st4, c4, h4, hrun4, hpost4, h4_26, h4_other, hc4⟩
  simp only [outerRouterContract, List.getD_cons_zero, List.getD_cons_succ,
    readGraph_eq_of_graphAt hPg3, readLenPrefixedList_eq_of_lenListAt hX3,
    readSinglePair_eq_of_singlePairAt hSP3, hRange_fin] at hpost4 hc4
  rcases hpost4 with ⟨hRtOut, hh4_ge, hh4_le, hZero4, hFrame4⟩
  change h4 ≤ st3.regs 26 + outerRouterSpace C_sp_rt g.Hhat.n cRoute at hh4_le
  have hc4' : c4 ≤ C_rt * cRoute + C_rt + 20 := by
    simp [argsSize, Expr.size] at hc4; dsimp only [cRoute, A, B]; omega
  have h4_r : ∀ r', r' ≤ 25 ∨ r' = 27 → st4.regs r' = st.regs r' := fun r' hr' => by
    rw [h4_other r' (by omega), h3_r r' hr']
  have h4_35 : st4.regs 35 = coreTag := by rw [h4_other 35 (by omega), h3_35]
  have h4_fr : ∀ a < h, st4.mem a = mem₀ a := fun a ha => by
    rw [hFrame4 a (by omega) (Or.inl (by omega)), hFr3 a ha]
  have hrtSpec := hSub.hroute.spec g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z
    (Finset.Subset.refl _) (by rw [hHhat_ins]; exact g.hHhat_loop) (by decide)
    (fun v _ => g.hHhat_deg v) (by omega) (by rw [hHhat_verts, Finset.card_range]; exact g.h2e_L)
    hb2 (by simpa [hRange_fin] using hvp)
  cases hrt : route g.Hhat g.Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z with
  | cut U_cut =>
    rw [hrt] at hRtOut hrtSpec
    rcases hRtOut with ⟨hTag1, U_list, hndU, hfinU, hLenU, hListU⟩
    let st4a : State := { st4 with regs := Function.update st4.regs 28 1 }
    have ha28 : Runs w pProg ω (.assign 28 (.load (.reg 20))) st4 .normal st4a 3 :=
      runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h4_r 20 (by omega), hInv.hr20, hTag1],
        rfl, rfl, by simp [Expr.size]⟩
    have hCutT := gameWriteCutRet_triple (w := w) (outResAddr := outResAddr)
      (routeOutAddr := g.routeOutAddr) (hCur := h4) (kU := U_list.length) pProg st4a
      (by simp [st4a, h4_r 3 (by omega), hInv.hr3])
      (by simp [st4a, h4_r 20 (by omega), hInv.hr20])
      (by simp [st4a, h4_26]) hLenU (by omega) (by have := g.houtH; omega) hw16
    rcases hCutT st4a ω rfl with ⟨oC, stC, cC, hrunC, hqC, hcC⟩
    cases oC with
    | normal => exact False.elim hqC
    | returned h' =>
      rcases hqC with ⟨hh'_eq, hO0, hO1, hO2, hOfr⟩
      subst hh'_eq
      have hcond : Runs w pProg ω
          (.cond (.reg 28) gameWriteCutRetStmt
            ((.assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
              .assign 30 (.bin .add (.reg 20) (.const 2))) ;;
             .call 26 idx.bFake [.reg 0, .reg 19, .reg 29, .reg 30, .reg 21, .reg 22, .reg 26] ;;
             gameAppendMatchedStmt ;;
             .cond (.reg 35) gameWriteWitRetStmt (.assign 27 (.bin .sub (.reg 27) (.const 1)))))
          st4a (.returned h') stC (1 + cC + 1) :=
        runs_cond_iff.mpr ⟨1, cC, by simp [Expr.eval, st4a],
          by simp only [one_ne_zero, ↓reduceIte]; exact hrunC, by simp [Expr.size]⟩
      have hseq2 := runs_seq_iff.mpr (Or.inr ⟨st4a, 3, 1 + cC + 1, ha28, hcond, rfl⟩)
      have hseq1 := runs_seq_iff.mpr (Or.inr ⟨st4, c4, 3 + (1 + cC + 1) + 1, hrun4, hseq2, rfl⟩)
      have hUlen_le : U_list.length ≤ 2 * e := by
        have hsub : U_list.toFinset ⊆ Finset.range (2 * e) := by rw [hfinU, ← hHhat_verts]; exact hrtSpec.1
        have hcard := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup hndU, Finset.card_range] at hcard; exact hcard
      refine ⟨.returned h', stC, _, hseq1, h', rfl, ?_, by omega, by omega, ?_, ?_, ?_⟩
      · refine ⟨hO0, U_list, hndU, hfinU, hO1, ?_, by rw [hO2]; omega, by rw [hO2]; omega⟩
        rw [hO2]; intro j hj; rw [hOfr _ (Or.inr (by have := g.houtH; omega))]; exact hListU j hj
      · intro a ha; rw [hOfr a (Or.inr (by have := g.houtH; omega))]; exact hZero4 a ha
      · intro a haH haO; rw [hOfr a (by omega)]; exact h4_fr a haH
      · dsimp at hcC; omega
  | matched ms emb =>
    rw [hrt] at hRtOut hrtSpec
    rcases hRtOut with ⟨hTag0, hLenM, hEdM⟩
    have ⟨hflat, hpm, hM_le_A⟩ := singlePair_matched_props hrtSpec
    set M_k := ms.getD 0 []
    set F_k := fakeCompletion A B M_k
    rw [hflat] at hLenM hEdM
    have hWstep := witness_step_invariants hInv.hW_val hInv.hW_loop hInv.hW_deg
      hInv.hW_len hInv.hF_len hA_sub hB_sub hdisjAB hA_le hAB_card hpm
    rcases hWstep with ⟨hMF_le, hFk_le, hW_len', hF_len', hW_val', hW_loop', hW_deg'⟩
    change M_k.length + F_k.length ≤ e at hMF_le
    change F_k.length ≤ e at hFk_le
    change (W_edges ++ (M_k ++ F_k)).length ≤ (k + 1) * e at hW_len'
    change (F_edges ++ F_k).length ≤ (k + 1) * e at hF_len'
    have h2Fe_eq : 2 * (g.F * e) = 2 * g.F * e := by ring
    have hW_cap : W_edges.length + M_k.length + F_k.length ≤ g.F * e := by
      have h1 : (k + 1) * e ≤ g.F * e := Nat.mul_le_mul_right e (by have := hInv.hk_fuel; omega)
      simp only [List.length_append] at hW_len'; omega
    have hF_cap : F_edges.length + F_k.length ≤ g.F * e := by
      have h1 : (k + 1) * e ≤ g.F * e := Nat.mul_le_mul_right e (by have := hInv.hk_fuel; omega)
      simp only [List.length_append] at hF_len'; omega
    let st4a : State := { st4 with regs := Function.update st4.regs 28 0 }
    have ha28 : Runs w pProg ω (.assign 28 (.load (.reg 20))) st4 .normal st4a 3 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h4_r 20 (by omega), hInv.hr20, hTag0],
        rfl, rfl, by simp [Expr.size]⟩
    let st4b : State :=
      { st4a with regs := Function.update (Function.update st4a.regs 29 M_k.length) 30 (g.routeOutAddr + 2) }
    have hLoadM : Runs w pProg ω
        (.assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
         .assign 30 (.bin .add (.reg 20) (.const 2))) st4a .normal st4b 10 := by
      let st4a1 : State := { st4a with regs := Function.update st4a.regs 29 M_k.length }
      have ha1 : Runs w pProg ω (.assign 29 (.load (.bin .add (.reg 20) (.const 1)))) st4a .normal st4a1 5 :=
        runs_assign_iff.mpr ⟨M_k.length,
          by simp [Expr.eval, BinOp.eval, st4a, h4_r 20 (by omega), hInv.hr20, hw1,
               (by omega : g.routeOutAddr + 1 < 2 ^ w), hLenM],
          rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w pProg ω (.assign 30 (.bin .add (.reg 20) (.const 2))) st4a1 .normal st4b 4 :=
        runs_assign_iff.mpr ⟨g.routeOutAddr + 2,
          by simp [Expr.eval, BinOp.eval, st4a1, st4a, h4_r 20 (by omega), hInv.hr20, hw2,
               (by omega : g.routeOutAddr + 2 < 2 ^ w)],
          rfl, rfl, by simp [Expr.size]⟩
      exact runs_seq_iff.mpr (Or.inr ⟨st4a1, 5, 4, ha1, ha2, rfl⟩)
    have hSP4 : SinglePairAt st4.mem g.pairsAddr A_list B_list := by
      refine ⟨by rw [hFrame4 _ (by omega) (Or.inl (by omega))]; exact hSP3.1,
        by rw [hFrame4 _ (by omega) (Or.inl (by omega))]; exact hSP3.2.1,
        fun j hj => by rw [hFrame4 _ (by omega) (Or.inl (by omega))]; exact hSP3.2.2.1 j hj,
        by rw [hFrame4 _ (by omega) (Or.inl (by omega))]; exact hSP3.2.2.2.1,
        fun j hj => by rw [hFrame4 _ (by omega) (Or.inl (by omega))]; exact hSP3.2.2.2.2 j hj⟩
    -- Call bFake
    have hFakeCall := runs_call_of_meetsContract (r := 26) (p := pProg) (w := w)
      (st := st4b) (args := [.reg 0, .reg 19, .reg 29, .reg 30, .reg 21, .reg 22, .reg 26])
      (vs := [e, g.pairsAddr, M_k.length, g.routeOutAddr + 2, g.fRoundAddr, g.fLenAddr, h4])
      hSub.hFake
      (by simp [evalArgs, Expr.eval, st4b, st4a, h4_r 0 (by omega), hInv.hr0,
            h4_r 19 (by omega), hInv.hr19, h4_r 21 (by omega), hInv.hr21,
            h4_r 22 (by omega), hInv.hr22, h4_26])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨e, g.pairsAddr, M_k.length, g.routeOutAddr + 2, g.fRoundAddr, g.fLenAddr, h4,
        A_list, B_list, M_k, rfl, hAB_len,
        fun p hp => Finset.mem_range.mp (hA_sub (List.mem_toFinset.mpr hp)),
        fun p hp => Finset.mem_range.mp (hB_sub (List.mem_toFinset.mpr hp)),
        hSP4, rfl,
        fun ed hed => ⟨Finset.mem_range.mp (hA_sub (hpm.1 ed hed).1),
                       Finset.mem_range.mp (hB_sub (hpm.1 ed hed).2)⟩,
        hEdM, hZero4, by omega, by omega, by omega, by omega,
        Or.inr (by omega), Or.inr (by omega), Or.inl (by omega), Or.inr (by omega), Or.inr (by omega),
        by unfold fakeCompletionSpace; omega, by omega, by omega⟩ ω
    rcases hFakeCall with ⟨st5, c5, h5, hrun5, hpost5, h5_26, h5_other, hc5⟩
    dsimp only [fakeCompletionContract, st4b, st4a, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hpost5 hc5
    rw [readSinglePair_eq_of_singlePairAt hSP4, readEdges_eq_of_edgesAt hEdM] at hpost5
    rcases hpost5 with ⟨hh5_eq, hZero5, h5_fLen, h5_fEd, hFrame5⟩
    have h5_r : ∀ r', r' ≤ 25 ∨ r' = 27 → st5.regs r' = st.regs r' := fun r' hr' => by
      rw [h5_other r' (by omega)]; simp [st4b, st4a, Function.update_of_ne (by omega : r' ≠ 30),
        Function.update_of_ne (by omega : r' ≠ 29), Function.update_of_ne (by omega : r' ≠ 28),
        h4_r r' hr']
    have h5_35 : st5.regs 35 = coreTag := by rw [h5_other 35 (by omega)]; simp [st4b, st4a, h4_35]
    have h5_29 : st5.regs 29 = M_k.length := by rw [h5_other 29 (by omega)]; simp [st4b]
    have h5_30 : st5.regs 30 = g.routeOutAddr + 2 := by rw [h5_other 30 (by omega)]; simp [st4b]
    have h5_W : GraphAt st5.mem g.wAddr (Graph.mk (2 * e) W_edges) := by
      intro i hi
      have hi' : i < 2 + 2 * W_edges.length := by rw [graph_encode_length] at hi; simpa [Graph.m] using hi
      rw [hFrame5 _ (by omega) (Or.inl (by omega)) (by omega),
          hFrame4 _ (by omega) (Or.inl (by omega))]
      exact hW3 i hi
    have h5_F : EdgesAt st5.mem g.fAddr F_edges := by
      intro j hj; have hj' : j < F_edges.length := hj
      rw [hFrame5 _ (by omega) (Or.inl (by omega)) (by omega),
          hFrame4 _ (by omega) (Or.inl (by omega)),
          hFrame5 _ (by omega) (Or.inl (by omega)) (by omega),
          hFrame4 _ (by omega) (Or.inl (by omega))]
      exact hF3 j hj
    have h5_M : EdgesAt st5.mem (g.routeOutAddr + 2) M_k := by
      intro j hj; have hj' : j < M_k.length := hj
      rw [hFrame5 _ (by omega) (Or.inl (by omega)) (by omega),
          hFrame5 _ (by omega) (Or.inl (by omega)) (by omega)]
      exact hEdM j hj
    -- Call gameAppendMatchedStmt
    have hAppT := gameAppendMatched_triple (w := w) (e := e) (wAddr := g.wAddr)
      (wEdgesAddr := g.wEdgesAddr) (fAddr := g.fAddr) (routeListAddr := g.routeOutAddr + 2)
      (fRoundAddr := g.fRoundAddr) (fLenAddr := g.fLenAddr)
      (wLen := W_edges.length) (fLen := F_edges.length) (mM := M_k.length) (mF := F_k.length)
      (maxW := g.F * e) (maxF := g.F * e) pProg st5 W_edges F_edges M_k F_k
      (by rw [h5_r 16 (by decide), hInv.hr16]) (by rw [h5_r 17 (by decide), hInv.hr17])
      (by rw [h5_r 21 (by decide), hInv.hr21]) (by rw [h5_r 22 (by decide), hInv.hr22])
      (by rw [h5_r 23 (by decide), hInv.hr23]) (by rw [h5_r 24 (by decide), hInv.hr24])
      (by rw [h5_r 25 (by decide), hInv.hr25])
      h5_29 h5_30 rfl rfl rfl rfl rfl hW_cap hF_cap h5_W h5_F h5_M h5_fEd h5_fLen
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (by omega) (by omega) (by omega) (by omega) (by omega) hw16
    rcases hAppT st5 ω rfl with ⟨o6, st6, c6, hrun6, hq6, hc6⟩
    cases o6 with
    | returned _ => exact False.elim hq6
    | normal =>
      rcases hq6 with ⟨h6_W, h6_F, h6_24, h6_25, h6_fr, h6_kr⟩
      have h6_r : ∀ r', r' ≤ 23 ∨ r' = 27 → st6.regs r' = st.regs r' := fun r' hr' => by
        rw [h6_kr r' (by omega), h5_r r' (by omega)]
      have h6_26 : st6.regs 26 = h5 := by rw [h6_kr 26 (by decide), h5_26]
      have h6_35 : st6.regs 35 = coreTag := by rw [h6_kr 35 (by decide), h5_35]
      have h6_Zero : ZeroFrom st6.mem h5 := fun a ha => by
        rw [h6_fr a (Or.inr (by omega)) (Or.inr (by omega))]; exact hZero5 a ha
      have h6_fr0 : ∀ a < h, st6.mem a = mem₀ a := fun a ha => by
        rw [h6_fr a (Or.inl (by omega)) (Or.inl (by omega)),
            hFrame5 a (by omega) (Or.inl (by omega)) (by omega), h4_fr a ha]
      rcases htag with rfl | rfl
      · simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
        let st7 : State := { st6 with regs := Function.update st6.regs 27 fuel }
        have hdec : Runs w pProg ω (.assign 27 (.bin .sub (.reg 27) (.const 1))) st6 .normal st7 4 :=
          runs_assign_iff.mpr ⟨fuel,
            by simp [Expr.eval, BinOp.eval, h6_r 27 (by omega), hInv.hr27, hw1,
                 (by have := hInv.hk_fuel; omega : fuel < 2 ^ w)], rfl, rfl, by simp [Expr.size]⟩
        have hcond35 : Runs w pProg ω
            (.cond (.reg 35) gameWriteWitRetStmt (.assign 27 (.bin .sub (.reg 27) (.const 1))))
            st6 .normal st7 6 :=
          runs_cond_iff.mpr ⟨0, 4, by simp [Expr.eval, h6_35],
            by simp only [↓reduceIte]; exact hdec, by simp [Expr.size]⟩
        have hs_a := runs_seq_iff.mpr (Or.inr ⟨st6, c6, 6, hrun6, hcond35, rfl⟩)
        have hs_b := runs_seq_iff.mpr (Or.inr ⟨st5, c5, _, hrun5, hs_a, rfl⟩)
        have hs_c := runs_seq_iff.mpr (Or.inr ⟨st4b, 10, _, hLoadM, hs_b, rfl⟩)
        have hcond28 : Runs w pProg ω
            (.cond (.reg 28) gameWriteCutRetStmt
              ((.assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
                .assign 30 (.bin .add (.reg 20) (.const 2))) ;;
               .call 26 idx.bFake [.reg 0, .reg 19, .reg 29, .reg 30, .reg 21, .reg 22, .reg 26] ;;
               gameAppendMatchedStmt ;;
               .cond (.reg 35) gameWriteWitRetStmt (.assign 27 (.bin .sub (.reg 27) (.const 1)))))
            st4a .normal st7 (1 + (10 + (c5 + (c6 + 6 + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, 10 + (c5 + (c6 + 6 + 1) + 1) + 1, by simp [Expr.eval, st4a],
            by simp only [↓reduceIte]; exact hs_c, by simp [Expr.size]⟩
        have hs_d := runs_seq_iff.mpr (Or.inr ⟨st4a, 3, _, ha28, hcond28, rfl⟩)
        have hs_e := runs_seq_iff.mpr (Or.inr ⟨st4, c4, _, hrun4, hs_d, rfl⟩)
        have h7_r : ∀ r' ≤ 23, st7.regs r' = st.regs r' := fun r' hr' => by
          simp [st7, Function.update_of_ne (by omega : r' ≠ 27), h6_r r' (Or.inl hr')]
        have h7_pg : GraphAt st7.mem pgAddr g.Hhat := by
          intro i hi
          have hi' : i < 2 + 2 * g.Hhat.m := by rw [graph_encode_length] at hi; exact hi
          dsimp only [st7]
          rw [h6_fr _ (Or.inl (by have := g.hpgH; omega)) (Or.inl (by have := g.hpgH; omega)),
              hFrame5 _ (by have := g.hpgH; omega) (Or.inl (by have := g.hpgH; omega))
                (by have := g.hpgH; omega),
              hFrame4 _ (by have := g.hpgH; omega) (Or.inl (by have := g.hpgH; omega))]
          exact hPg3 i hi
        have h7_xPort : LenListAt st7.mem g.xPortAddr (List.range (2 * e)) := by
          refine ⟨by dsimp only [st7]
                     rw [h6_fr _ (Or.inl (by omega)) (Or.inl (by omega)),
                         hFrame5 _ (by omega) (Or.inl (by omega)) (by omega),
                         hFrame4 _ (by omega) (Or.inl (by omega))]
                     exact hX3.1,
            fun j hj => by
              dsimp only [st7]
              rw [h6_fr _ (Or.inl (by simp at hj; omega)) (Or.inl (by simp at hj; omega)),
                  hFrame5 _ (by simp at hj; omega) (Or.inl (by simp at hj; omega)) (by simp at hj; omega),
                  hFrame4 _ (by simp at hj; omega) (Or.inl (by simp at hj; omega))]
              exact hX3.2 j hj⟩
        refine ⟨.normal, st7, _, hs_e, rfl, ?_, by simp [st7, h6_26]; omega, ?_, ?_⟩
        · exact
            { hk_fuel := by have := hInv.hk_fuel; omega
              hW_len := hW_len', hF_len := hF_len', hW_val := hW_val', hW_loop := hW_loop',
              hW_deg := hW_deg',
              hr0 := by rw [h7_r 0 (by decide), hInv.hr0],
              hr1 := by rw [h7_r 1 (by decide), hInv.hr1],
              hr3 := by rw [h7_r 3 (by decide), hInv.hr3],
              hr5 := by rw [h7_r 5 (by decide), hInv.hr5],
              hr6 := by rw [h7_r 6 (by decide), hInv.hr6],
              hr7 := by rw [h7_r 7 (by decide), hInv.hr7],
              hr9 := by rw [h7_r 9 (by decide), hInv.hr9],
              hr11 := by rw [h7_r 11 (by decide), hInv.hr11],
              hr12 := by rw [h7_r 12 (by decide), hInv.hr12],
              hr13 := by rw [h7_r 13 (by decide), hInv.hr13],
              hr14 := by rw [h7_r 14 (by decide), hInv.hr14],
              hr15 := by rw [h7_r 15 (by decide), hInv.hr15],
              hr16 := by rw [h7_r 16 (by decide), hInv.hr16],
              hr17 := by rw [h7_r 17 (by decide), hInv.hr17],
              hr18 := by rw [h7_r 18 (by decide), hInv.hr18],
              hr19 := by rw [h7_r 19 (by decide), hInv.hr19],
              hr20 := by rw [h7_r 20 (by decide), hInv.hr20],
              hr21 := by rw [h7_r 21 (by decide), hInv.hr21],
              hr22 := by rw [h7_r 22 (by decide), hInv.hr22],
              hr23 := by rw [h7_r 23 (by decide), hInv.hr23],
              hr24 := by
                simp only [st7, Function.update_of_ne (by decide : (24 : ℕ) ≠ 27), h6_24,
                  List.length_append]
                dsimp only [M_k, F_k]; omega,
              hr25 := by
                simp only [st7, Function.update_of_ne (by decide : (25 : ℕ) ≠ 27), h6_25,
                  List.length_append]
                rfl,
              hr27 := by simp [st7],
              hhInit := by simp [st7, h6_26]; omega,
              hZero := by simpa [st7, h6_26] using h6_Zero,
              hPg := h7_pg, hXPort := h7_xPort, hW_g := h6_W, hF_e := h6_F, hFrame := h6_fr0 }
        · simp only [st7, Function.update_of_ne (by decide : (26 : ℕ) ≠ 27), h6_26]
          unfold fakeCompletionSpace at hh5_eq; rw [g.hHhat_n] at hh4_le
          have := hAuxSp.1; omega
        · dsimp at hc6; simp [argsSize, Expr.size, fakeCompletionCost] at hc5; omega
      · simp only [↓reduceIte]
        have hout_lt_h : outResAddr + 4 ≤ h := g.houtH
        have hO_lt_w : outResAddr + 4 ≤ g.wAddr := by omega
        have hO_lt_f : outResAddr + 4 ≤ g.fAddr := by omega
        have hO_lt_h5 : outResAddr + 4 ≤ h5 := by omega
        have hh5_ge : st.regs 26 ≤ h5 := by omega
        have hh5_le : h5 ≤ st.regs 26 + outerGameLoopSpace C_sp M r e (fuel + 1) lc := by
          unfold fakeCompletionSpace at hh5_eq; omega
        have hW_bd : g.wAddr + 2 + 2 * (W_edges.length + (M_k.length + F_k.length)) ≤ h5 := by omega
        have hF_bd : g.fAddr + 2 * (F_edges.length + F_k.length) ≤ h5 := by omega
        have hWitT := gameWriteWitRet_triple (w := w) (outResAddr := outResAddr)
          (wAddr := g.wAddr) (fLen := (F_edges ++ F_k).length) (fAddr := g.fAddr) (hCur := h5)
          pProg st6 (by rw [h6_r 3 (by decide), hInv.hr3])
          (by rw [h6_r 16 (by decide), hInv.hr16]) (by rw [h6_r 17 (by decide), hInv.hr17])
          (by simp [h6_25]) h6_26 (by omega) hw16
        rcases hWitT st6 ω rfl with ⟨oW, stW, cW, hrunW, hqW, hcW⟩
        cases oW with
        | normal => exact False.elim hqW
        | returned h' =>
          rcases hqW with ⟨hh'_eq, hO0, hO1, hO2, hO3, hOfr⟩
          subst hh'_eq
          have hcostW : c4 + (3 + (1 + (10 + (c5 + (c6 + (1 + cW + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
              C_rt * cRoute + C_rt + 800 * e + 500 := by
            dsimp at hc6 hcW; simp [argsSize, Expr.size, fakeCompletionCost] at hc5; omega
          have hcond35 : Runs w pProg ω
              (.cond (.reg 35) gameWriteWitRetStmt (.assign 27 (.bin .sub (.reg 27) (.const 1))))
              st6 (.returned h') stW (1 + cW + 1) :=
            runs_cond_iff.mpr ⟨1, cW, by simp [Expr.eval, h6_35],
              by simp only [one_ne_zero, ↓reduceIte]; exact hrunW, by simp [Expr.size]⟩
          have hs_a := runs_seq_iff.mpr (Or.inr ⟨st6, c6, _, hrun6, hcond35, rfl⟩)
          have hs_b := runs_seq_iff.mpr (Or.inr ⟨st5, c5, _, hrun5, hs_a, rfl⟩)
          have hs_c := runs_seq_iff.mpr (Or.inr ⟨st4b, 10, _, hLoadM, hs_b, rfl⟩)
          have hcond28 : Runs w pProg ω
              (.cond (.reg 28) gameWriteCutRetStmt
                ((.assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
                  .assign 30 (.bin .add (.reg 20) (.const 2))) ;;
                 .call 26 idx.bFake [.reg 0, .reg 19, .reg 29, .reg 30, .reg 21, .reg 22, .reg 26] ;;
                 gameAppendMatchedStmt ;;
                 .cond (.reg 35) gameWriteWitRetStmt (.assign 27 (.bin .sub (.reg 27) (.const 1)))))
              st4a (.returned h') stW (1 + (10 + (c5 + (c6 + (1 + cW + 1) + 1) + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨0, 10 + (c5 + (c6 + (1 + cW + 1) + 1) + 1) + 1, by simp [Expr.eval, st4a],
              by simp only [↓reduceIte]; exact hs_c, by simp [Expr.size]⟩
          have hs_d := runs_seq_iff.mpr (Or.inr ⟨st4a, 3, _, ha28, hcond28, rfl⟩)
          have hs_e := runs_seq_iff.mpr (Or.inr ⟨st4, c4, _, hrun4, hs_d, rfl⟩)
          refine ⟨.returned h', stW, _, hs_e, h', rfl, ?_, hh5_ge, hh5_le, ?_, ?_, hcostW⟩
          · refine ⟨hO0, ?_, ?_, hO2, ?_, ?_⟩
            · rw [hO1]; intro i hi
              rw [hOfr _ (Or.inr (le_trans hO_lt_w (Nat.le_add_right _ _)))]; exact h6_W i hi
            · rw [hO1]; simp only [List.length_append]; exact hW_bd
            · rw [hO3]; intro j hj
              rw [hOfr (g.fAddr + 2 * j) (Or.inr (le_trans hO_lt_f (Nat.le_add_right _ _))),
                  hOfr (g.fAddr + 2 * j + 1)
                    (Or.inr (le_trans hO_lt_f (le_trans (Nat.le_add_right _ _) (Nat.le_succ _))))]
              exact h6_F j hj
            · rw [hO3]; simp only [List.length_append]; exact hF_bd
          · intro a ha; rw [hOfr a (Or.inr (le_trans hO_lt_h5 ha))]; exact h6_Zero a ha
          · intro a haH haO; rw [hOfr a haO]; exact h6_fr0 a haH


end MinCostFlow.ExpanderDecomp

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- Mathematical loop invariant tracking the witness-graph matching history and embedding across
rounds of `outerGameProc` (mirroring `OuterGame.LoopInv`). -/
structure GameMathInv (M r e z : ℕ) (Hhat : Graph)
    (M_hist : ℕ → List (ℕ × ℕ)) (k : ℕ) (W_edges F_edges : List (ℕ × ℕ)) : Prop where
  hW_eq : W_edges = witnessEdges M_hist k
  hM_perf : ∀ j < k, IsPerfectMatchingOn (Finset.range (2 * e)) (M_hist j)
  hM_cut : ∀ j < k, ∃ C ⊆ Finset.range (2 * e),
    (Finset.range (2 * e)).card ≤ 4 * C.card ∧
    (∀ ed ∈ M_hist j, ¬ (ed.1 ∈ C ∧ ed.2 ∈ C)) ∧
    100 * (Graph.mk (2 * e) (witnessEdges M_hist j)).cutIn (Finset.range (2 * e)) C ≤
      (Finset.range (2 * e)).card
  hF_valid : ∀ ed ∈ F_edges, ed.1 < 2 * e ∧ ed.2 < 2 * e
  hF_len : F_edges.length ≤ k * z
  hF_deg : ∀ v < 2 * e, (Graph.mk (2 * e) F_edges).deg v ≤ k
  hemb : GameEmbInv Hhat W_edges F_edges (ROut ParamConfig.default M) k


end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma gameMathInv_zero (M r e z : ℕ) (Hhat : Graph) :
    GameMathInv M r e z Hhat (fun _ => []) 0 [] [] where
  hW_eq := rfl
  hM_perf := fun _ hj => absurd hj (Nat.not_lt_zero _)
  hM_cut := fun _ hj => absurd hj (Nat.not_lt_zero _)
  hF_valid := fun _ he => by cases he
  hF_len := by simp
  hF_deg := fun _ _ => by simp [Graph.deg, Graph.degIn, Graph.inside]
  hemb := GameEmbInv.empty Hhat (ROut ParamConfig.default M)

private lemma singlePair_matched' {Hhat : Graph} {A B : Finset ℕ} {M z : ℕ}
    {matchings : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : RouteMatchedSpec Hhat Hhat.verts [(A, B)] 10 (LParam M) (bOut ParamConfig.default M) z
      matchings emb) :
    let E := matchings.getD 0 []
    IsPartialMatching A B E ∧
      A.card - E.length ≤ z ∧
      IsEmbeddingOn ⟨Hhat.n, E⟩ Hhat Hhat.verts emb ∧
      ∀ i < Hhat.m, congestion ⟨Hhat.n, E⟩ emb i ≤ ROut ParamConfig.default M := by
  obtain ⟨hlen, hpair, hdef, hemb, _, hcong⟩ := h
  cases matchings with
  | nil => simp at hlen
  | cons E rest =>
    cases rest with
    | cons _ _ => simp at hlen
    | nil =>
      have h0 := hpair 0 (by simp)
      simp only [List.getD_cons_zero, List.getElem_cons_zero] at h0
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
        add_zero] at hdef
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
        routeCong_outer] at hemb hcong
      exact ⟨h0, hdef, hemb, hcong⟩

lemma gameMathInv_expander_witness {M r e k : ℕ} {Hhat : Graph}
    {M_hist : ℕ → List (ℕ × ℕ)} {W_edges F_edges : List (ℕ × ℕ)} {S : Finset ℕ}
    {matchings : List (List (ℕ × ℕ))} {emb_inj : ℕ → List ℕ}
    (hHhat_n : Hhat.n = 2 * e) (hk1_le_t : k + 1 ≤ tParam M)
    (hMath : GameMathInv M r e (e / DOut ParamConfig.default M r) Hhat M_hist k W_edges F_edges)
    (hSV : S ⊆ Finset.range (2 * e)) (hS2 : 2 * e ≤ 2 * S.card)
    (hSexp : (Graph.mk (2 * e) W_edges).IsExpansionExpanderOn S
      (1 / (PParam ParamConfig.default M r : ℝ)))
    (hrt_spec : RouteMatchedSpec Hhat Hhat.verts [(Finset.range (2 * e) \ S, S)] 10
      (LParam M) (bOut ParamConfig.default M) (e / DOut ParamConfig.default M r)
      matchings emb_inj) :
    let M_inj := matchings.getD 0 []
    let F_inj := fakeCompletion (Finset.range (2 * e) \ S) S M_inj
    OuterGameOutcomeSpec ParamConfig.default M r e Hhat
      (.witness (W_edges ++ (M_inj ++ F_inj)) (F_edges ++ F_inj)) := by
  intro M_inj F_inj
  let A : Finset ℕ := Finset.range (2 * e) \ S
  have hHhat_verts : Hhat.verts = Finset.range (2 * e) := by unfold Graph.verts; rw [hHhat_n]
  have hAV : A ⊆ Hhat.verts := by rw [hHhat_verts]; exact Finset.sdiff_subset
  have hSV' : S ⊆ Hhat.verts := by rw [hHhat_verts]; exact hSV
  have hdisjAS : Disjoint A S := disjoint_sdiff_self_left
  have hAcard_le : A.card ≤ S.card := by
    have hsum := Finset.card_sdiff_add_card_eq_card hSV
    rw [Finset.card_range] at hsum; dsimp only [A]; omega
  obtain ⟨hM_pm, hM_def, hemb_inj, hcong_inj⟩ := singlePair_matched' hrt_spec
  change A.card - M_inj.length ≤ e / DOut ParamConfig.default M r at hM_def
  obtain ⟨hF_len, hF_pm, hF_deg, hE_pm, _, hE_covA, _⟩ :=
    fakeCompletion_spec hdisjAS hAcard_le hM_pm
  change F_inj.length = A.card - M_inj.length at hF_len
  change ∀ n v, (Graph.mk n F_inj).deg v ≤ 1 at hF_deg
  have hPr_ge1 : (1 : ℝ) ≤ (PParam ParamConfig.default M r : ℝ) := by
    exact_mod_cast one_le_PParam ParamConfig.default M r
  have hβ0 : (0 : ℝ) ≤ 1 / (PParam ParamConfig.default M r : ℝ) := by positivity
  have hβ1 : (1 : ℝ) / (PParam ParamConfig.default M r : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hPr_ge1
  have hW_exp : (Graph.mk (2 * e) (W_edges ++ (M_inj ++ F_inj))).IsExpansionExpanderOn
      (Finset.range (2 * e)) (1 / (2 * (PParam ParamConfig.default M r : ℝ))) := by
    have h1 := isExpansionExpanderOn_of_injection (n := 2 * e) (E := W_edges)
      (M := M_inj ++ F_inj) (X := Finset.range (2 * e)) (S := S) hβ0 hβ1 hSV hSexp
      (fun ed hed => by
        have hm := hE_pm.1 ed hed
        have hA := Finset.mem_sdiff.mp hm.1
        exact ⟨hA.1, hA.2, hm.2⟩)
      hE_pm.2.2
      (fun v hvV hvS => hE_covA v (Finset.mem_sdiff.mpr ⟨hvV, hvS⟩))
    have hdiv : (1 : ℝ) / (PParam ParamConfig.default M r : ℝ) / 2 =
        1 / (2 * (PParam ParamConfig.default M r : ℝ)) := by ring
    rwa [hdiv] at h1
  have hF_all_valid : ∀ ed ∈ F_edges ++ F_inj, ed.1 < 2 * e ∧ ed.2 < 2 * e := by
    intro ed hed
    rcases List.mem_append.mp hed with h | h
    · exact hMath.hF_valid ed h
    · have hm := hF_pm.1 ed h
      exact ⟨Finset.mem_range.mp (Finset.sdiff_subset hm.1), Finset.mem_range.mp (hSV hm.2)⟩
  have hF_all_len : (F_edges ++ F_inj).length ≤ tParam M * (e / DOut ParamConfig.default M r) := by
    rw [List.length_append]
    have h1 : F_edges.length ≤ k * (e / DOut ParamConfig.default M r) := hMath.hF_len
    have h2 : F_inj.length ≤ e / DOut ParamConfig.default M r := by omega
    have h3 : (k + 1) * (e / DOut ParamConfig.default M r) ≤
        tParam M * (e / DOut ParamConfig.default M r) := Nat.mul_le_mul_right _ hk1_le_t
    have h4 : k * (e / DOut ParamConfig.default M r) + e / DOut ParamConfig.default M r =
        (k + 1) * (e / DOut ParamConfig.default M r) := by ring
    omega
  have hF_all_deg : ∀ v < 2 * e, (Graph.mk (2 * e) (F_edges ++ F_inj)).deg v ≤ tParam M := by
    intro v hv
    rw [deg_append]
    have h1 := hMath.hF_deg v hv
    have h2 := hF_deg (2 * e) v
    omega
  have hM_inj_ends : ∀ ed ∈ M_inj, ed.1 ∈ Hhat.verts ∧ ed.2 ∈ Hhat.verts := by
    intro ed hed; have hm := hM_pm.1 ed hed; exact ⟨hAV hm.1, hSV' hm.2⟩
  have hF_inj_ends : ∀ ed ∈ F_inj, ed.1 ∈ Hhat.verts ∧ ed.2 ∈ Hhat.verts := by
    intro ed hed; have hm := hF_pm.1 ed hed; exact ⟨hAV hm.1, hSV' hm.2⟩
  have hemb_next := hMath.hemb.append_round hemb_inj hcong_inj hM_inj_ends hF_inj_ends
  have h1_le_tR : 1 ≤ tParam M * ROut ParamConfig.default M :=
    Nat.mul_pos (one_le_tParam M) (one_le_ROut ParamConfig.default M)
  have hkR_le : (k + 1) * ROut ParamConfig.default M ≤ tParam M * ROut ParamConfig.default M :=
    Nat.mul_le_mul_right _ hk1_le_t
  obtain ⟨emb_out, hemb_out, hcong_out⟩ := hemb_next.congestion_le h1_le_tR hkR_le
  rw [hHhat_n, hHhat_verts] at hemb_out
  rw [hHhat_n] at hcong_out
  exact ⟨hW_exp, hF_all_valid, hF_all_len, hF_all_deg, emb_out, hemb_out, hcong_out⟩

lemma gameMathInv_bisection_step {M r e k : ℕ} {Hhat : Graph}
    {M_hist : ℕ → List (ℕ × ℕ)} {W_edges F_edges : List (ℕ × ℕ)} {U : Finset ℕ}
    {matchings : List (List (ℕ × ℕ))} {emb_k : ℕ → List ℕ}
    (hHhat_n : Hhat.n = 2 * e)
    (hMath : GameMathInv M r e (e / DOut ParamConfig.default M r) Hhat M_hist k W_edges F_edges)
    (hUV : U ⊆ Finset.range (2 * e)) (hU1 : 2 * e ≤ 4 * U.card)
    (hU2 : 2 * e ≤ 4 * (Finset.range (2 * e) \ U).card)
    (hUcut : 100 * (Graph.mk (2 * e) W_edges).cut U ≤ 2 * e)
    (hrt_spec : RouteMatchedSpec Hhat Hhat.verts
      [((padToBisection e U).1, (padToBisection e U).2)] 10
      (LParam M) (bOut ParamConfig.default M) (e / DOut ParamConfig.default M r)
      matchings emb_k) :
    let M_k := matchings.getD 0 []
    let F_k := fakeCompletion (padToBisection e U).1 (padToBisection e U).2 M_k
    ∃ M_hist',
      GameMathInv M r e (e / DOut ParamConfig.default M r) Hhat M_hist' (k + 1)
        (W_edges ++ (M_k ++ F_k)) (F_edges ++ F_k) := by
  intro M_k F_k
  have hHhat_verts : Hhat.verts = Finset.range (2 * e) := by unfold Graph.verts; rw [hHhat_n]
  obtain ⟨hCV, hC4, _, hAV, hBV, hdisjAB, hunionAB, hAcard, hBcard, _, hdisjCB, hCcut⟩ :=
    padToBisection_spec hUV hU1 hU2
  let A : Finset ℕ := (padToBisection e U).1
  let B : Finset ℕ := (padToBisection e U).2
  change A.card = e at hAcard
  change B.card = e at hBcard
  change Disjoint A B at hdisjAB
  change A ∪ B = Finset.range (2 * e) at hunionAB
  have hAV' : A ⊆ Hhat.verts := by rw [hHhat_verts]; exact hAV
  have hBV' : B ⊆ Hhat.verts := by rw [hHhat_verts]; exact hBV
  obtain ⟨hMk_pm, hMk_def, hemb_k, hcong_k⟩ := singlePair_matched' hrt_spec
  change A.card - M_k.length ≤ e / DOut ParamConfig.default M r at hMk_def
  obtain ⟨hFk_len, hFk_pm, hFk_deg, hEk_pm, _, _, hEk_perf⟩ :=
    fakeCompletion_spec hdisjAB (by omega) hMk_pm
  change F_k.length = A.card - M_k.length at hFk_len
  change ∀ n v, (Graph.mk n F_k).deg v ≤ 1 at hFk_deg
  let E_k := M_k ++ F_k
  have hEk_perfV : IsPerfectMatchingOn (Finset.range (2 * e)) E_k :=
    hEk_perf (Finset.range (2 * e)) (by omega) hunionAB
  let M_hist' : ℕ → List (ℕ × ℕ) := fun j => if j = k then E_k else M_hist j
  have hwit_eq : ∀ j ≤ k, witnessEdges M_hist' j = witnessEdges M_hist j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ m ihm =>
      simp only [witnessEdges, ihm (by omega), M_hist']
      have hne : m ≠ k := by omega
      simp [hne]
  refine ⟨M_hist', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [witnessEdges, hwit_eq k le_rfl, M_hist', ↓reduceIte, hMath.hW_eq, E_k]
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; simpa [M_hist'] using hEk_perfV
    · simpa [M_hist', hjk] using hMath.hM_perf j (by omega)
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      refine ⟨outerSmallerSide e U, hCV, by rw [Finset.card_range]; exact hC4, ?_, ?_⟩
      · intro ed hed
        simp only [M_hist', ↓reduceIte] at hed
        have hm := hEk_pm.1 ed hed
        intro ⟨_, h2⟩
        exact Finset.disjoint_left.mp hdisjCB h2 hm.2
      · rw [hwit_eq j le_rfl, ← hMath.hW_eq, hCcut, Finset.card_range]
        exact hUcut
    · obtain ⟨C, h1, h2, h3, h4⟩ := hMath.hM_cut j (by omega)
      refine ⟨C, h1, h2, ?_, ?_⟩
      · simpa [M_hist', hjk] using h3
      · rwa [hwit_eq j (by omega)]
  · intro ed hed
    rcases List.mem_append.mp hed with h | h
    · exact hMath.hF_valid ed h
    · have hm := hFk_pm.1 ed h
      exact ⟨Finset.mem_range.mp (hAV hm.1), Finset.mem_range.mp (hBV hm.2)⟩
  · rw [List.length_append]
    have h1 := hMath.hF_len
    have h2 : F_k.length ≤ e / DOut ParamConfig.default M r := by omega
    have hring : (k + 1) * (e / DOut ParamConfig.default M r) =
        k * (e / DOut ParamConfig.default M r) + e / DOut ParamConfig.default M r := by ring
    omega
  · intro v hv
    rw [deg_append]
    have h1 := hMath.hF_deg v hv
    have h2 := hFk_deg (2 * e) v
    omega
  · exact hMath.hemb.append_round hemb_k hcong_k
      (fun ed hed => ⟨hAV' (hMk_pm.1 ed hed).1, hBV' (hMk_pm.1 ed hed).2⟩)
      (fun ed hed => ⟨hAV' (hFk_pm.1 ed hed).1, hBV' (hFk_pm.1 ed hed).2⟩)

end MinCostFlow.ExpanderDecomp
