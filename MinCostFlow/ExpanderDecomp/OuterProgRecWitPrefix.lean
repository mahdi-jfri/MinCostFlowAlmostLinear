module

public import MinCostFlow.ExpanderDecomp.OuterProgRecChild
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Witness-Branch Prefix and `RemoveFake` Stage (`OuterProgRecWitPrefix`)

Proves `recWitnessPrefix_runs`, `recWitness_mid_runs`, and `recWitness_cost_aux` for the
witness branch of `outerDecompRecProc`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 3. Witness Branch (`recWitnessPrefix_runs` + `recWitness_runs`) -/

/-- Prefix of `recWitnessStmt idx` up through `bContract`, `computeRfWorkBoundStmt`, and computing
`h4 := rfWorkAddr + rfWorkBound` into `r34`. Returns `st34` and a continuation chainer into any
suffix statement. -/
lemma recWitnessPrefix_runs {cfg : ParamConfig} {M r w : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv cfg M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hCon : MeetsContract w pProg idx.bContract (outerContractEdgesContract w))
    {ω : ℕ → Bool} {H : CompactSubgraph} {h h3 : ℕ} {st st3 : State}
    {W_out F_out : List (ℕ × ℕ)}
    (hRep : H.Represents G H.vertSet) (hRoot_le : hRoot ≤ h)
    (hPB : OuterParamBlockAt st.mem paramAddr cfg G.n M r)
    (hr0 : st.regs 0 = H.verts.length) (hr2 : st.regs 2 = H.edges.length)
    (hr4 : st.regs 4 = paramAddr)
    (h3_r10 : st3.regs 10 = h) (h3_r15 : st3.regs 15 = h3)
    (h3_r14_le : st3.regs 14 + 4 ≤ h3) (h3_ge : h + 2 * H.edges.length ≤ h3)
    (hOwn3 : ListAt st3.mem h (portOwnersList H.edges))
    (hOut3 : OuterGameOutAt st3.mem (st3.regs 14) h h3 H.edges.length (.witness W_out F_out))
    (h3_regs : ∀ r' ≤ 9, st3.regs r' = st.regs r')
    (h3_belowH : ∀ a < h, st3.mem a = st.mem a)
    (hF_valid : ∀ ed ∈ F_out, ed.1 < 2 * (G.inside H.vertSet).length ∧ ed.2 < 2 * (G.inside H.vertSet).length)
    (hEnd_lt : h3 + 2 * F_out.length + 2 + 3 * H.verts.length + 2 * H.edges.length +
      rfWorkBound H.verts.length H.edges.length F_out.length (Lambda cfg M r) (LParam M) < 2 ^ w) :
    let k := H.verts.length
    let e := H.edges.length
    let mF := F_out.length
    let F' := contractEdges G H.vertSet F_out
    let f'Addr := h3
    let rhoAddr := f'Addr + 2 * mF
    let rAddr := rhoAddr + 2
    let restVAddr := rAddr + k
    let restEAddr := restVAddr + k
    let actRestAddr := restEAddr + 2 * e
    let rfWorkAddr := actRestAddr + k
    let h4 := rfWorkAddr + rfWorkBound k e F'.length (Lambda cfg M r) (LParam M)
    ∃ st34 : State,
      st34.regs 19 = f'Addr ∧ st34.regs 20 = rhoAddr ∧ st34.regs 24 = rAddr ∧
      st34.regs 25 = restVAddr ∧ st34.regs 26 = restEAddr ∧ st34.regs 27 = F'.length ∧
      st34.regs 29 = actRestAddr ∧ st34.regs 33 = rfWorkAddr ∧ st34.regs 34 = h4 ∧
      (∀ r' ≤ 9, st34.regs r' = st.regs r') ∧
      EdgesAt st34.mem f'Addr F' ∧
      st34.mem rhoAddr = 1 ∧ st34.mem (rhoAddr + 1) = Lambda cfg M r ∧
      (∀ a, a < h3 ∨ rAddr ≤ a → st34.mem a = st3.mem a) ∧
      ∀ (rest : Stmt) (oEnd : Outcome) (stEnd : State) (cRest : ℕ),
        Runs w pProg ω rest st34 oEnd stEnd cRest →
        ∃ cTot,
          Runs w pProg ω
            ((.assign 17 (.load (.bin .add (.reg 14) (.const 2))) ;;
              .assign 18 (.load (.bin .add (.reg 14) (.const 3))) ;;
              .assign 22 (.load (.bin .add (.reg 4) (.const 8))) ;;
              .assign 23 (.load (.bin .add (.reg 4) (.const 4)))) ;;
             (.assign 19 (.reg 15) ;;
              .assign 20 (.bin .add (.reg 19) (.bin .mul (.const 2) (.reg 17))) ;;
              .assign 24 (.bin .add (.reg 20) (.const 2)) ;;
              .assign 25 (.bin .add (.reg 24) (.reg 0))) ;;
             (.assign 26 (.bin .add (.reg 25) (.reg 0)) ;;
              .assign 29 (.bin .add (.reg 26) (.bin .mul (.const 2) (.reg 2))) ;;
              .assign 33 (.bin .add (.reg 29) (.reg 0))) ;;
             (.store (.reg 20) (.const 1) ;;
              .store (.bin .add (.reg 20) (.const 1)) (.reg 22)) ;;
             .call 27 idx.bContract [.reg 10, .reg 17, .reg 18, .reg 19] ;;
             computeRfWorkBoundStmt ;;
             .assign 34 (.bin .add (.reg 33) (.reg 31)) ;;
             rest) st3 oEnd stEnd cTot ∧
          cTot ≤ cRest + 80 * mF + 210 := by
  intro k e mF F' f'Addr rhoAddr rAddr restVAddr restEAddr actRestAddr rfWorkAddr h4
  set Λ := Lambda cfg M r
  set L := LParam M
  change st.regs 0 = k at hr0
  change st.regs 2 = e at hr2
  change h + 2 * e ≤ h3 at h3_ge
  change h3 + 2 * mF + 2 + 3 * k + 2 * e + rfWorkBound k e mF Λ L < 2 ^ w at hEnd_lt
  have he_eq : (G.inside H.vertSet).length = e := congrArg List.length hRep.2.2.symm
  have hL4 : 4 ≤ L := four_le_LParam M
  have hw250 : 250 < 2 ^ w := env.hw250
  have hw16 : 16 < 2 ^ w := by omega
  rcases hOut3 with ⟨_, _, _, hF_len_mem, hF_edges, hF_addr_le⟩
  change st3.mem (st3.regs 14 + 2) = mF at hF_len_mem
  set fOutAddr := st3.mem (st3.regs 14 + 3)
  have hF_addr_mem : st3.mem (st3.regs 14 + 3) = fOutAddr := rfl
  have hrf_eq : rfWorkAddr = h3 + 2 * mF + 2 + 3 * k + 2 * e := by
    dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr, rAddr, rhoAddr, f'Addr]; omega
  have hF'_le : F'.length ≤ mF := (List.length_filter_le _ _).trans (by simp [mF])
  have h4_lt : h4 < 2 ^ w := by
    have hwb : rfWorkBound k e F'.length Λ L ≤ rfWorkBound k e mF Λ L := by unfold rfWorkBound; omega
    have h4_eq : h4 = rfWorkAddr + rfWorkBound k e F'.length Λ L := rfl
    omega
  have h3_PB : OuterParamBlockAt st3.mem paramAddr cfg G.n M r := by
    have hp : ∀ j < 12, st3.mem (paramAddr + j) = st.mem (paramAddr + j) := fun j hj =>
      h3_belowH _ (by have := env.hparH; omega)
    exact ⟨by rw [hp 0 (by decide)]; exact hPB.1, by rw [hp 1 (by decide)]; exact hPB.2.1,
      by rw [hp 2 (by decide)]; exact hPB.2.2.1, by rw [hp 3 (by decide)]; exact hPB.2.2.2.1,
      by rw [hp 4 (by decide)]; exact hPB.2.2.2.2.1, by rw [hp 5 (by decide)]; exact hPB.2.2.2.2.2.1,
      by rw [hp 6 (by decide)]; exact hPB.2.2.2.2.2.2.1, by rw [hp 7 (by decide)]; exact hPB.2.2.2.2.2.2.2.1,
      by rw [hp 8 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.1, by rw [hp 9 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.1,
      by rw [hp 10 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.1, by rw [hp 11 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.2⟩
  have hW1 : Triple w pProg (fun s => s = st3)
      (.assign 17 (.load (.bin .add (.reg 14) (.const 2))) ;;
       .assign 18 (.load (.bin .add (.reg 14) (.const 3))) ;;
       .assign 22 (.load (.bin .add (.reg 4) (.const 8))) ;;
       .assign 23 (.load (.bin .add (.reg 4) (.const 4))))
      (normalPost fun s' => s'.mem = st3.mem ∧
        s'.regs 17 = mF ∧ s'.regs 18 = fOutAddr ∧ s'.regs 22 = Λ ∧ s'.regs 23 = L ∧
        (∀ r' ≤ 16, s'.regs r' = st3.regs r'))
      (fun _ => 30) := by
    intro s ω hs; subst s
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := mF)
      (by simp [Expr.eval, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : st3.regs 14 + 2 < 2 ^ w), hF_len_mem]) ?_
    refine runs_seq_assign_le (v := fOutAddr)
      (by simp [Expr.eval, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : st3.regs 14 + 3 < 2 ^ w), hF_addr_mem]) ?_
    refine runs_seq_assign_le (v := Λ)
      (by simp [Expr.eval, BinOp.eval, h3_regs 4 (by decide), hr4, (by omega : 8 < 2 ^ w),
            (by have := env.hparH; omega : paramAddr + 8 < 2 ^ w), h3_PB.2.2.2.2.2.2.2.2.1, Λ]) ?_
    refine runs_assign_le (v := L)
      (by simp [Expr.eval, BinOp.eval, h3_regs 4 (by decide), hr4, (by omega : 4 < 2 ^ w),
            (by have := env.hparH; omega : paramAddr + 4 < 2 ^ w), h3_PB.2.2.2.2.1, L])
      ⟨rfl, by simp, by simp, by simp, by simp, fun r' hr' => by
        dsimp only
        rw [Function.update_of_ne (by omega : r' ≠ 23), Function.update_of_ne (by omega : r' ≠ 22),
            Function.update_of_ne (by omega : r' ≠ 18), Function.update_of_ne (by omega : r' ≠ 17)]⟩
      (by simp [Expr.size])
  rcases hW1 st3 ω rfl with ⟨oW1, stW1, cW1, hrunW1, hqW1, hcW1⟩
  cases oW1 with
  | returned _ => exact False.elim hqW1
  | normal =>
    rcases hqW1 with ⟨hW1_mem, hW1_17, hW1_18, hW1_22, hW1_23, hW1_r⟩
    have hW2 : Triple w pProg (fun s => s = stW1)
        (.assign 19 (.reg 15) ;;
         .assign 20 (.bin .add (.reg 19) (.bin .mul (.const 2) (.reg 17))) ;;
         .assign 24 (.bin .add (.reg 20) (.const 2)) ;;
         .assign 25 (.bin .add (.reg 24) (.reg 0)))
        (normalPost fun s' => s'.mem = st3.mem ∧
          s'.regs 19 = f'Addr ∧ s'.regs 20 = rhoAddr ∧ s'.regs 24 = rAddr ∧ s'.regs 25 = restVAddr ∧
          (∀ r', r' ≤ 18 ∨ r' = 22 ∨ r' = 23 → s'.regs r' = stW1.regs r'))
        (fun _ => 25) := by
      intro s ω hs; subst s
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := f'Addr)
        (by simp [Expr.eval, hW1_r 15 (by decide), h3_r15, f'Addr]) ?_
      refine runs_seq_assign_le (v := rhoAddr)
        (by simp [Expr.eval, BinOp.eval, hW1_17, (by omega : 2 < 2 ^ w),
              (by omega : 2 * mF < 2 ^ w), (by omega : f'Addr + 2 * mF < 2 ^ w), rhoAddr]) ?_
      refine runs_seq_assign_le (v := rAddr)
        (by simp [Expr.eval, BinOp.eval, (by omega : 2 < 2 ^ w),
              (by omega : rhoAddr + 2 < 2 ^ w), rAddr]) ?_
      refine runs_assign_le (v := restVAddr)
        (by simp [Expr.eval, BinOp.eval, hW1_r 0 (by decide), h3_regs 0 (by decide), hr0,
              (by omega : rAddr + k < 2 ^ w), restVAddr])
        ⟨hW1_mem, by simp, by simp, by simp, by simp, fun r' hr' => by
          dsimp only
          rw [Function.update_of_ne (by omega : r' ≠ 25), Function.update_of_ne (by omega : r' ≠ 24),
              Function.update_of_ne (by omega : r' ≠ 20), Function.update_of_ne (by omega : r' ≠ 19)]⟩
        (by simp [Expr.size])
    rcases hW2 stW1 ω rfl with ⟨oW2, stW2, cW2, hrunW2, hqW2, hcW2⟩
    cases oW2 with
    | returned _ => exact False.elim hqW2
    | normal =>
      rcases hqW2 with ⟨hW2_mem, hW2_19, hW2_20, hW2_24, hW2_25, hW2_r⟩
      have hW3 : Triple w pProg (fun s => s = stW2)
          (.assign 26 (.bin .add (.reg 25) (.reg 0)) ;;
           .assign 29 (.bin .add (.reg 26) (.bin .mul (.const 2) (.reg 2))) ;;
           .assign 33 (.bin .add (.reg 29) (.reg 0)))
          (normalPost fun s' => s'.mem = st3.mem ∧
            s'.regs 26 = restEAddr ∧ s'.regs 29 = actRestAddr ∧ s'.regs 33 = rfWorkAddr ∧
            (∀ r' ≤ 25, s'.regs r' = stW2.regs r'))
          (fun _ => 22) := by
        intro s ω hs; subst s
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := restEAddr)
          (by simp [Expr.eval, BinOp.eval, hW2_25, hW2_r 0 (Or.inl (by decide)),
                hW1_r 0 (by decide), h3_regs 0 (by decide), hr0,
                (by omega : restVAddr + k < 2 ^ w), restEAddr]) ?_
        refine runs_seq_assign_le (v := actRestAddr)
          (by simp [Expr.eval, BinOp.eval, hW2_r 2 (Or.inl (by decide)),
                hW1_r 2 (by decide), h3_regs 2 (by decide), hr2,
                (by omega : 2 < 2 ^ w), (by omega : 2 * e < 2 ^ w),
                (by omega : restEAddr + 2 * e < 2 ^ w), actRestAddr]) ?_
        refine runs_assign_le (v := rfWorkAddr)
          (by simp [Expr.eval, BinOp.eval, hW2_r 0 (Or.inl (by decide)),
                hW1_r 0 (by decide), h3_regs 0 (by decide), hr0,
                (by omega : actRestAddr + k < 2 ^ w), rfWorkAddr])
          ⟨hW2_mem, by simp, by simp, by simp, fun r' hr' => by
            dsimp only
            rw [Function.update_of_ne (by omega : r' ≠ 33), Function.update_of_ne (by omega : r' ≠ 29),
                Function.update_of_ne (by omega : r' ≠ 26)]⟩
          (by simp [Expr.size])
      rcases hW3 stW2 ω rfl with ⟨oW3, stW3, cW3, hrunW3, hqW3, hcW3⟩
      cases oW3 with
      | returned _ => exact False.elim hqW3
      | normal =>
        rcases hqW3 with ⟨hW3_mem, hW3_26, hW3_29, hW3_33, hW3_r⟩
        have hS12 : Triple w pProg (fun s => s = stW3)
            (.store (.reg 20) (.const 1) ;;
             .store (.bin .add (.reg 20) (.const 1)) (.reg 22))
            (normalPost fun s' =>
              s'.mem rhoAddr = 1 ∧ s'.mem (rhoAddr + 1) = Λ ∧
              (∀ a, a ≠ rhoAddr → a ≠ rhoAddr + 1 → s'.mem a = st3.mem a) ∧
              s'.regs = stW3.regs)
            (fun _ => 14) := by
          intro s ω hs; subst s
          have h20 : stW3.regs 20 = rhoAddr := by rw [hW3_r 20 (by decide), hW2_20]
          have h22 : stW3.regs 22 = Λ := by rw [hW3_r 22 (by decide), hW2_r 22 (Or.inr (Or.inl rfl)), hW1_22]
          refine runs_start_le ?_
          refine runs_seq_store_le (x := rhoAddr) (v := 1)
            (by simp [Expr.eval, h20]) (by simp [Expr.eval, (by omega : 1 < 2 ^ w)]) ?_
          refine runs_store_le (x := rhoAddr + 1) (v := Λ)
            (by simp [Expr.eval, BinOp.eval, h20, (by omega : 1 < 2 ^ w), (by omega : rhoAddr + 1 < 2 ^ w)])
            (by simp [Expr.eval, h22])
            ⟨by dsimp only; rw [Function.update_of_ne (by omega : rhoAddr ≠ rhoAddr + 1), Function.update_self],
             by simp,
             fun a h1 h2 => by dsimp only; rw [Function.update_of_ne h2, Function.update_of_ne h1, hW3_mem],
             rfl⟩
            (by simp [Expr.size])
        rcases hS12 stW3 ω rfl with ⟨oS, stS, cS, hrunS, hqS, hcS⟩
        cases oS with
        | returned _ => exact False.elim hqS
        | normal =>
          rcases hqS with ⟨hS_rho0, hS_rho1, hS_fr, hS_regs⟩
          have hS_own : ListAt stS.mem h (portOwnersList H.edges) := fun i hi => by
            have hlen : (portOwnersList H.edges).length = 2 * e := portOwnersList_length H.edges
            rw [hS_fr (h + i) (by omega) (by omega)]; exact hOwn3 i hi
          have hS_F : EdgesAt stS.mem fOutAddr F_out := fun i hi =>
            ⟨by rw [hS_fr (fOutAddr + 2 * i) (by omega) (by omega)]; exact (hF_edges i hi).1,
             by rw [hS_fr (fOutAddr + 2 * i + 1) (by omega) (by omega)]; exact (hF_edges i hi).2⟩
          have hConCall := runs_call_of_meetsContract (r := 27) (p := pProg) (w := w) (st := stS)
            (args := [.reg 10, .reg 17, .reg 18, .reg 19])
            (vs := [h, mF, fOutAddr, f'Addr]) hCon
            (by simp [evalArgs, Expr.eval, hS_regs, hW3_r 10 (by decide), hW2_r 10 (Or.inl (by decide)),
                  hW1_r 10 (by decide), h3_r10, hW3_r 17 (by decide), hW2_r 17 (Or.inl (by decide)),
                  hW1_17, hW3_r 18 (by decide), hW2_r 18 (Or.inl (by decide)), hW1_18,
                  hW3_r 19 (by decide), hW2_19])
            (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                rcases hv with rfl | rfl | rfl | rfl <;> omega)
            ⟨h, mF, fOutAddr, f'Addr, 2 * e, portOwnersList H.edges, F_out, rfl,
              portOwnersList_length H.edges, rfl,
              fun ed hed => by rw [← he_eq]; exact hF_valid ed hed,
              hS_own, hS_F, by omega, by omega, by omega, hw16,
              Or.inr h3_ge, Or.inr hF_addr_le⟩ ω
          rcases hConCall with ⟨stCon, cCon, mF', hrunCon, hpostCon, hCon_27, hCon_other, hcCon⟩
          dsimp only [outerContractEdgesContract, List.getD, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some] at hpostCon hcCon
          rw [readEdges_eq_of_edgesAt hS_F] at hpostCon
          have hCon_eq : ((F_out.map fun ed => (stS.mem (h + ed.1), stS.mem (h + ed.2))).filter
              fun ed => decide (ed.1 ≠ ed.2)) = F' := by
            unfold F' contractEdges; congr 1
            apply List.map_congr_left; intro ed hed
            have h12 : ed.1 < 2 * e ∧ ed.2 < 2 * e := by rw [← he_eq]; exact hF_valid ed hed
            have ho : ∀ p < 2 * e, stS.mem (h + p) = portOwner G H.vertSet p := fun p hp => by
              have hlen : (portOwnersList H.edges).length = 2 * e := portOwnersList_length H.edges
              have h1 := hS_own p (hlen ▸ hp)
              rw [h1, ← portOwnersList_getD_eq_portOwner hRep.2.2.symm hp]
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hp)]
            rw [ho ed.1 h12.1, ho ed.2 h12.2]
          rw [hCon_eq] at hpostCon
          rcases hpostCon with ⟨hmF'_eq, hCon_F', hCon_fr⟩
          have hrfB_lt : rfWorkBound k e F'.length Λ L < 2 ^ w := by
            have h4_eq : h4 = rfWorkAddr + rfWorkBound k e F'.length Λ L := rfl; omega
          have hCompB := computeRfWorkBound_triple (w := w) (k := k) (e := e) (mF := F'.length)
            (Λ := Λ) (L := L) pProg stCon
            (by rw [hCon_other 0 (by decide), hS_regs, hW3_r 0 (by decide), hW2_r 0 (Or.inl (by decide)),
                  hW1_r 0 (by decide), h3_regs 0 (by decide), hr0])
            (by rw [hCon_other 2 (by decide), hS_regs, hW3_r 2 (by decide), hW2_r 2 (Or.inl (by decide)),
                  hW1_r 2 (by decide), h3_regs 2 (by decide), hr2])
            (by rw [hCon_27, hmF'_eq])
            (by rw [hCon_other 22 (by decide), hS_regs, hW3_r 22 (by decide),
                  hW2_r 22 (Or.inr (Or.inl rfl)), hW1_22])
            (by rw [hCon_other 23 (by decide), hS_regs, hW3_r 23 (by decide),
                  hW2_r 23 (Or.inr (Or.inr rfl)), hW1_23])
            (by omega) hrfB_lt hw250
          rcases hCompB stCon ω rfl with ⟨oCB, stCB, cCB, hrunCB, hqCB, hcCB⟩
          cases oCB with
          | returned _ => exact False.elim hqCB
          | normal =>
            rcases hqCB with ⟨hCB_mem, hCB_31, hCB_r⟩
            let st34 : State := { stCB with regs := Function.update stCB.regs 34 h4 }
            have hCB_33 : stCB.regs 33 = rfWorkAddr := by
              rw [hCB_r 33 (Or.inr (by decide)), hCon_other 33 (by decide), hS_regs, hW3_33]
            have h4_eq : rfWorkAddr + rfWorkBound k e F'.length Λ L = h4 := rfl
            have hrun34 : Runs w pProg ω (.assign 34 (.bin .add (.reg 33) (.reg 31))) stCB .normal st34 4 :=
              runs_assign_iff.mpr ⟨h4,
                by simp [Expr.eval, BinOp.eval, hCB_33, hCB_31, h4_eq, h4_lt], rfl, rfl, by simp [Expr.size]⟩
            refine ⟨st34,
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_r 19 (Or.inl (by decide)),
                    hCon_other 19 (by decide), hS_regs, hW3_r 19 (by decide), hW2_19],
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_r 20 (Or.inl (by decide)),
                    hCon_other 20 (by decide), hS_regs, hW3_r 20 (by decide), hW2_20],
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_r 24 (Or.inl (by decide)),
                    hCon_other 24 (by decide), hS_regs, hW3_r 24 (by decide), hW2_24],
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_r 25 (Or.inl (by decide)),
                    hCon_other 25 (by decide), hS_regs, hW3_r 25 (by decide), hW2_25],
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_r 26 (Or.inl (by decide)),
                    hCon_other 26 (by decide), hS_regs, hW3_26],
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_r 27 (Or.inl (by decide)),
                    hCon_27, hmF'_eq],
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_r 29 (Or.inl (by decide)),
                    hCon_other 29 (by decide), hS_regs, hW3_29],
              by dsimp only [st34]; rw [Function.update_of_ne (by decide), hCB_33],
              by simp [st34],
              fun r' hr' => by
                dsimp only [st34]
                rw [Function.update_of_ne (by omega : r' ≠ 34), hCB_r r' (Or.inl (by omega)),
                    hCon_other r' (by omega), hS_regs, hW3_r r' (by omega),
                    hW2_r r' (Or.inl (by omega)), hW1_r r' (by omega), h3_regs r' hr'],
              by dsimp only [st34]; rw [hCB_mem]; exact hCon_F',
              by dsimp only [st34]; rw [hCB_mem, hCon_fr rhoAddr (Or.inr le_rfl)]; exact hS_rho0,
              by dsimp only [st34]; rw [hCB_mem, hCon_fr (rhoAddr + 1) (Or.inr (Nat.le_succ _))]; exact hS_rho1,
              fun a ha => by
                have hfa : a < f'Addr ∨ f'Addr + 2 * mF ≤ a := by
                  rcases ha with h | h
                  · exact Or.inl h
                  · exact Or.inr (le_trans (Nat.le_add_right _ 2) h)
                have hne0 : a ≠ rhoAddr := by
                  rcases ha with h | h
                  · exact ne_of_lt (lt_of_lt_of_le h (Nat.le_add_right _ _))
                  · exact ne_of_gt (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) h)
                have hne1 : a ≠ rhoAddr + 1 := by
                  rcases ha with h | h
                  · exact ne_of_lt (lt_of_lt_of_le h (le_trans (Nat.le_add_right _ _) (Nat.le_succ _)))
                  · exact ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self (rhoAddr + 1)) h)
                dsimp only [st34]
                rw [hCB_mem, hCon_fr a hfa, hS_fr a hne0 hne1],
              fun rest oEnd stEnd cRest hRest => by
                refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨stW1, cW1, _, hrunW1,
                  runs_seq_iff.mpr (Or.inr ⟨stW2, cW2, _, hrunW2,
                    runs_seq_iff.mpr (Or.inr ⟨stW3, cW3, _, hrunW3,
                      runs_seq_iff.mpr (Or.inr ⟨stS, cS, _, hrunS,
                        runs_seq_iff.mpr (Or.inr ⟨stCon, cCon, _, hrunCon,
                          runs_seq_iff.mpr (Or.inr ⟨stCB, cCB, _, hrunCB,
                            runs_seq_iff.mpr (Or.inr ⟨st34, 4, cRest, hrun34, hRest, rfl⟩),
                            rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
                dsimp at hcW1 hcW2 hcW3 hcS hcCB
                simp only [argsSize, Expr.size, outerContractEdgesCost, Nat.add_zero] at hcCon
                omega⟩

/-- Plain-arithmetic helper bundling `RemoveFakeWordBound`, argument `< 2 ^ w`, and
`RemoveFakeDisjoint` for `recWitness_runs`. -/
private lemma rf_wordBound_aux {w n k e mF mF' Λ L vertsAddr edgesAddr h h3 locAddr hRoot witSp : ℕ}
    (hL1 : 1 ≤ L) (hmF' : mF' ≤ mF)
    (hRoot_le : hRoot ≤ h) (hh_le_h3 : h ≤ h3)
    (hVA : vertsAddr + k ≤ h) (hEA : edgesAddr + 2 * e ≤ h) (hlocH : locAddr + n ≤ hRoot)
    (hws_le : removeFakeWorkSpace k e mF' (rfHParam e mF' 1 Λ) ≤ rfWorkBound k e mF' Λ L)
    (hrfB_le : rfWorkBound k e mF' Λ L ≤ witSp)
    (hPrune_arith : 8 * rfCcap 1 Λ * (e + 2 * mF') + 4 * rfCcap 1 Λ +
      2 * (k + mF') + 2 * (e + 2 * mF') + rfHParam e mF' 1 Λ + 16 ≤ witSp)
    (hEnd : h3 + 2 * mF + 2 + 3 * k + 2 * e + witSp + 3 < 2 ^ w) :
    let f'Addr := h3
    let rhoAddr := f'Addr + 2 * mF
    let rAddr := rhoAddr + 2
    let restVAddr := rAddr + k
    let restEAddr := restVAddr + k
    let actRestAddr := restEAddr + 2 * e
    let rfWorkAddr := actRestAddr + k
    RemoveFakeWordBound w n k e mF' 1 Λ vertsAddr edgesAddr f'Addr rhoAddr locAddr rAddr rfWorkAddr ∧
    (∀ v ∈ [k, vertsAddr, e, edgesAddr, mF', f'Addr, rhoAddr, locAddr, rAddr, rfWorkAddr], v < 2 ^ w) ∧
    (DisjointRange locAddr n vertsAddr k → DisjointRange locAddr n edgesAddr (2 * e) →
      RemoveFakeDisjoint n k e mF' (rfHParam e mF' 1 Λ)
        vertsAddr edgesAddr f'Addr rhoAddr locAddr rAddr rfWorkAddr) := by
  intro f'Addr rhoAddr rAddr restVAddr restEAddr actRestAddr rfWorkAddr
  have hrf_eq : rfWorkAddr = h3 + 2 * mF + 2 + 3 * k + 2 * e := by
    dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr, rAddr, rhoAddr, f'Addr]; omega
  have h224 : 224 * Λ ≤ 224 * Λ * L := Nat.le_mul_of_pos_right _ hL1
  have h12Lam : 12 * Λ + 1 ≤ rfWorkBound k e mF' Λ L := by unfold rfWorkBound; omega
  have hPrune_end : rfPruneWorkAddr rfWorkAddr k e mF' +
      pruneWorkSpace (k + mF') (e + 2 * mF') (rfHParam e mF' 1 Λ) =
      rfWorkAddr + removeFakeWorkSpace k e mF' (rfHParam e mF' 1 Λ) := by
    unfold rfPruneWorkAddr removeFakeWorkSpace; ring
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    unfold PruneWordBound; rw [hPrune_end]
    exact max_lt (by omega) (by omega)
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro hdLV hdLE
    unfold RemoveFakeDisjoint DisjointRange
    refine ⟨hdLV, hdLE, Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩

lemma recWitness_cost_aux {C_core C_rt M r routeC e k kR mF mF' eRest lc
    c3 cTot cRF cWC cSD cCa cCb cCc eSum wSum : ℕ}
    (he1 : 1 ≤ e) (hk_le : k ≤ 2 * e) (hkR_le : kR ≤ k) (hmF_le : mF ≤ e) (hmF'_le : mF' ≤ e)
    (heRest_le : eRest ≤ e)
    (hlc_le : lc ≤ e * modelPerEdge ParamConfig.default M r routeC)
    (hrf_trim : removeFakeCost k e mF' 1 (Lambda ParamConfig.default M r) ≤
      2 ^ 30 * (e * (Lambda ParamConfig.default M r) ^ 2 * (LParam M) ^ 2))
    (hc3 : c3 ≤ outerGameCostFactor C_core C_rt * (lc + e + 1) + 40 * r + 500 +
      (220 * k + (runnerScale explicitProgram * 760 + 1900) * e + 260) + 70)
    (hcTot : cTot ≤ cRF + (cWC + (cSD + (cCa + (cCb + (cCc + 2 + 1) + 1) + 1) + 1) + 1) + 1 + 80 * mF + 210)
    (hcRF : cRF ≤ removeFakeCost k e mF' 1 (Lambda ParamConfig.default M r) + 11)
    (hcWC : cWC ≤ 30 * kR + 30)
    (hcSD : cSD ≤ 60 * k + 60 * kR + 80 + 7)
    (hcCh : cCa + (cCb + cCc + 1) + 1 ≤
      eSum * recPerEdgeCost ParamConfig.default C_core C_rt M r routeC +
      wSum * recPerWitCost ParamConfig.default M r +
      120 * (k - kR) + 90 * e + 120 * eRest + 800) :
    c3 + cTot + 20 ≤
      (e + eSum) * recPerEdgeCost ParamConfig.default C_core C_rt M r routeC +
      (e + wSum) * recPerWitCost ParamConfig.default M r + 600 := by
  set Λ := Lambda ParamConfig.default M r
  set L := LParam M
  set rs := runnerScale explicitProgram
  set c30 := (2 ^ 30 : ℕ)
  set F := outerGameCostFactor C_core C_rt
  set pe := recPerEdgeCost ParamConfig.default C_core C_rt M r routeC
  set pw := recPerWitCost ParamConfig.default M r
  have hgame_mul : F * (lc + 2 * e) + 40 * e * r ≤
      e * (F * (modelPerEdge ParamConfig.default M r routeC + 2) + 40 * r) := by
    have h1 : lc + 2 * e ≤ e * (modelPerEdge ParamConfig.default M r routeC + 2) := by
      have : e * (modelPerEdge ParamConfig.default M r routeC + 2) =
          e * modelPerEdge ParamConfig.default M r routeC + 2 * e := by ring
      linarith
    calc F * (lc + 2 * e) + 40 * e * r
        ≤ F * (e * (modelPerEdge ParamConfig.default M r routeC + 2)) + 40 * e * r :=
          Nat.add_le_add_right (Nat.mul_le_mul_left F h1) _
      _ = e * (F * (modelPerEdge ParamConfig.default M r routeC + 2) + 40 * r) := by ring
  have hF_le : F * (lc + e + 1) ≤ F * (lc + 2 * e) := Nat.mul_le_mul_left F (by omega)
  have h40r_le : 40 * r ≤ 40 * e * r := by
    calc 40 * r = 40 * 1 * r := by ring
      _ ≤ 40 * e * r := Nat.mul_le_mul_right r (Nat.mul_le_mul_left 40 he1)
  have hpe_exp : e * pe =
      e * (F * (modelPerEdge ParamConfig.default M r routeC + 2) + 40 * r) +
      (rs * 760) * e + 8000 * e := by unfold pe recPerEdgeCost; ring
  have hpw_exp : e * pw = c30 * (e * Λ ^ 2 * L ^ 2) + 2000 * e := by
    unfold pw recPerWitCost; ring
  have hdistE : (e + eSum) * pe = e * pe + eSum * pe := by ring
  have hdistW : (e + wSum) * pw = e * pw + wSum * pw := by ring
  have hpg_exp : (rs * 760 + 1900) * e = (rs * 760) * e + 1900 * e := by ring
  have hkkR : k - kR ≤ k := Nat.sub_le k kR
  have hc3' : c3 ≤ F * (lc + 2 * e) + 40 * e * r + (rs * 760) * e + 1900 * e + 220 * k + 830 := by
    linarith
  have h_lin : 1900 * e + 220 * k + 830 + 120 * mF + 260 + 11 + 30 * kR + 30 +
      60 * k + 60 * kR + 87 + 120 * (k - kR) + 90 * e + 120 * eRest + 800 + 26 ≤
      8000 * e + 2000 * e + 600 := by
    have _ := heRest_le; have _ := hmF'_le; omega
  linarith

/-- Middle block of `recWitnessStmt idx`: calls `bRF`, paints `R` via `writeConstLabelStmt`, and
calls `bSetDiff`, producing `stSD` and a continuation chainer into the recursive child call. -/
lemma recWitness_mid_runs {M r w : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv ParamConfig.default M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hRF : MeetsContract w pProg idx.bRF (removeFakeContract w))
    (hSetDiff : MeetsContract w pProg idx.bSetDiff (setDiffContract w))
    {ω : ℕ → Bool} {H : CompactSubgraph} {vertsAddr edgesAddr h h3 nl₀ mF : ℕ}
    {st st3 st34 : State} {F' : List (ℕ × ℕ)}
    (hRep : H.Represents G H.vertSet) (hXV : H.vertSet ⊆ G.verts)
    (he1 : 1 ≤ H.edges.length) (heM : H.edges.length ≤ M)
    (hk_le_2e : H.verts.length ≤ 2 * H.edges.length)
    (hmF'_le_mF : F'.length ≤ mF) (hmF'_le_e : F'.length ≤ H.edges.length)
    (hRoot_le : hRoot ≤ h)
    (hVA_h : vertsAddr + H.verts.length ≤ h) (hEA_h : edgesAddr + 2 * H.edges.length ≤ h)
    (hdLV : DisjointRange locAddr G.n vertsAddr H.verts.length)
    (hdLbV : DisjointRange labelsAddr G.n vertsAddr H.verts.length)
    (hdNV : DisjointRange nextLblAddr 1 vertsAddr H.verts.length)
    (hdLE : DisjointRange locAddr G.n edgesAddr (2 * H.edges.length))
    (hV : ListAt st.mem vertsAddr H.verts) (hE : EdgesAt st.mem edgesAddr H.edges)
    (hloc0 : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hnl : st.mem nextLblAddr = nl₀)
    (hnl_le : nl₀ + H.verts.length ≤ G.n)
    (hr0 : st.regs 0 = H.verts.length) (hr1 : st.regs 1 = vertsAddr)
    (hr2 : st.regs 2 = H.edges.length) (hr3 : st.regs 3 = edgesAddr)
    (hr5 : st.regs 5 = locAddr) (hr6 : st.regs 6 = labelsAddr) (hr7 : st.regs 7 = nextLblAddr)
    (h3_ge : h + 2 * H.edges.length ≤ h3)
    (hZero3 : ZeroFrom st3.mem h3)
    (h3_belowH : ∀ a < h, st3.mem a = st.mem a)
    (hF'_inX : ∀ ed ∈ F', ed.1 ∈ H.vertSet ∧ ed.2 ∈ H.vertSet)
    (hE_inX : ∀ ed ∈ H.edges, ed.1 ∈ H.vertSet ∧ ed.2 ∈ H.vertSet)
    (hPreRF :
      (Graph.mk G.n (H.edges ++ F')).IsConductanceExpanderOn H.vertSet
        ((1 : ℕ) / (Lambda ParamConfig.default M r : ℝ)) ∧
      ∀ v ∈ H.vertSet, 1 ≤ (Graph.mk G.n (H.edges ++ F')).degIn H.vertSet v)
    (h34_19 : st34.regs 19 = h3)
    (h34_20 : st34.regs 20 = h3 + 2 * mF)
    (h34_24 : st34.regs 24 = h3 + 2 * mF + 2)
    (h34_25 : st34.regs 25 = h3 + 2 * mF + 2 + H.verts.length)
    (h34_26 : st34.regs 26 = h3 + 2 * mF + 2 + 2 * H.verts.length)
    (h34_27 : st34.regs 27 = F'.length)
    (h34_29 : st34.regs 29 = h3 + 2 * mF + 2 + 2 * H.verts.length + 2 * H.edges.length)
    (h34_33 : st34.regs 33 = h3 + 2 * mF + 2 + 3 * H.verts.length + 2 * H.edges.length)
    (h34_34 : st34.regs 34 = h3 + 2 * mF + 2 + 3 * H.verts.length + 2 * H.edges.length +
      rfWorkBound H.verts.length H.edges.length F'.length (Lambda ParamConfig.default M r) (LParam M))
    (h34_r0_9 : ∀ r' ≤ 9, st34.regs r' = st.regs r')
    (h34_F' : EdgesAt st34.mem h3 F')
    (h34_rho0 : st34.mem (h3 + 2 * mF) = 1)
    (h34_rho1 : st34.mem (h3 + 2 * mF + 1) = Lambda ParamConfig.default M r)
    (h34_fr : ∀ a, a < h3 ∨ h3 + 2 * mF + 2 ≤ a → st34.mem a = st3.mem a)
    (hrfEnd_lt : h3 + 2 * mF + 2 + 3 * H.verts.length + 2 * H.edges.length +
      H.edges.length * recPerWitSpace ParamConfig.default M r + 3 < 2 ^ w) :
    let cfg := ParamConfig.default
    let k := H.verts.length
    let e := H.edges.length
    let Λ := Lambda cfg M r
    let L := LParam M
    let rAddr := h3 + 2 * mF + 2
    let restVAddr := rAddr + k
    let restEAddr := restVAddr + k
    let actRestAddr := restEAddr + 2 * e
    let rfWorkAddr := actRestAddr + k
    let h4 := rfWorkAddr + rfWorkBound k e F'.length Λ L
    ∃ (stSD : State) (R_list : List ℕ) (cRF cWC cSD : ℕ),
      R_list.length ≤ k ∧
      R_list.Nodup ∧
      R_list.toFinset ⊆ H.vertSet ∧
      (∀ (n : ℕ), (∀ u ∈ H.verts, u < n) →
        (Graph.mk n H.edges).IsConductanceExpanderOn R_list.toFinset ((1 : ℕ) / (Λ : ℝ) / 9) ∧
        (∀ u ∈ R_list.toFinset, 1 ≤ (Graph.mk n H.edges).degIn R_list.toFinset u) ∧
        (Graph.mk n (H.edges ++ F')).volIn H.verts.toFinset (H.verts.toFinset \ R_list.toFinset) ≤
          4 * rfCcap 1 Λ * F'.length ∧
        ((Graph.mk n (H.edges ++ F')).volIn H.verts.toFinset (H.verts.toFinset \ R_list.toFinset) : ℝ) ≤
          60 / ((1 : ℕ) / (Λ : ℝ)) * (F'.length : ℝ)) ∧
      stSD.regs 30 = (H.restrict (H.vertSet \ R_list.toFinset)).verts.length ∧
      stSD.regs 25 = restVAddr ∧ stSD.regs 26 = restEAddr ∧
      stSD.regs 29 = actRestAddr ∧ stSD.regs 34 = h4 ∧
      (∀ r' ≤ 9, stSD.regs r' = st.regs r') ∧
      ListAt stSD.mem restVAddr (H.restrict (H.vertSet \ R_list.toFinset)).verts ∧
      (∀ u ∈ R_list.toFinset, stSD.mem (labelsAddr + u) = nl₀) ∧
      stSD.mem nextLblAddr = nl₀ + 1 ∧
      (∀ u < G.n, stSD.mem (locAddr + u) = 0) ∧
      ZeroFrom stSD.mem h4 ∧
      (∀ a < h, (∀ u ∈ R_list.toFinset, a ≠ labelsAddr + u) → a ≠ nextLblAddr →
        (∀ u ∈ H.verts, a ≠ locAddr + u) → stSD.mem a = st.mem a) ∧
      cRF ≤ removeFakeCost k e F'.length 1 Λ + 11 ∧
      cWC ≤ 30 * R_list.length + 30 ∧
      cSD ≤ 60 * k + 60 * R_list.length + 80 + 7 ∧
      ∀ (rest : Stmt) (oEnd : Outcome) (stEnd : State) (cRest : ℕ),
        Runs w pProg ω rest stSD oEnd stEnd cRest →
        Runs w pProg ω
          (.call 28 idx.bRF [.reg 0, .reg 1, .reg 2, .reg 3, .reg 27, .reg 19, .reg 20, .reg 5, .reg 24, .reg 33] ;;
           writeConstLabelStmt ;;
           .call 30 idx.bSetDiff [.reg 0, .reg 1, .reg 28, .reg 24, .reg 5, .reg 25] ;;
           rest) st34 oEnd stEnd (cRF + (cWC + (cSD + cRest + 1) + 1) + 1) := by
  let cfg := ParamConfig.default
  set k := H.verts.length
  set e := H.edges.length
  set Λ := Lambda cfg M r
  set L := LParam M
  set mF' := F'.length
  set f'Addr := h3
  set rhoAddr := f'Addr + 2 * mF
  set rAddr := rhoAddr + 2
  set restVAddr := rAddr + k
  set restEAddr := restVAddr + k
  set actRestAddr := restEAddr + 2 * e
  set rfWorkAddr := actRestAddr + k
  set h4 := rfWorkAddr + rfWorkBound k e mF' Λ L
  have hL4 : 4 ≤ L := four_le_LParam M
  have hLam1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hw16 : 16 < 2 ^ w := by have := env.hw250; omega
  have hsubV : ∀ u ∈ H.verts, u < G.n := fun u hu =>
    Finset.mem_range.mp (hXV (List.mem_toFinset.mpr hu))
  have hrf_sp := rfArith_le_witSpace (cfg := cfg) (M := M) (r := r) he1 heM hk_le_2e hmF'_le_e env.h2M_L
  have hRF_ws_le : removeFakeWorkSpace k e mF' (rfHParam e mF' 1 Λ) ≤ rfWorkBound k e mF' Λ L :=
    removeFakeWorkSpace_le_rfWorkBound heM hmF'_le_e hLam1 env.h2M_L
  have hrf_eq_full : rfWorkAddr = h3 + 2 * mF + 2 + 3 * k + 2 * e := by
    dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr, rAddr, rhoAddr, f'Addr]; omega
  have hRF_aux := rf_wordBound_aux (by omega : 1 ≤ L) hmF'_le_mF hRoot_le
    (le_trans (Nat.le_add_right _ _) h3_ge) hVA_h hEA_h env.hlocH hRF_ws_le hrf_sp.2 hrf_sp.1
    hrfEnd_lt
  have h34_belowH : ∀ a < h, st34.mem a = st.mem a := fun a ha => by
    rw [h34_fr a (Or.inl (lt_of_lt_of_le ha (le_trans (Nat.le_add_right _ _) h3_ge))), h3_belowH a ha]
  have h34_V : ListAt st34.mem vertsAddr H.verts := fun i hi => by
    rw [h34_belowH (vertsAddr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi vertsAddr) hVA_h)]; exact hV i hi
  have h34_E : EdgesAt st34.mem edgesAddr H.edges := fun i hi =>
    ⟨by rw [h34_belowH (edgesAddr + 2 * i) (lt_of_lt_of_le (Nat.add_lt_add_left (by omega) edgesAddr) hEA_h)]; exact (hE i hi).1,
     by rw [h34_belowH (edgesAddr + 2 * i + 1) (lt_of_lt_of_le (by omega : edgesAddr + 2 * i + 1 < edgesAddr + 2 * e) hEA_h)]; exact (hE i hi).2⟩
  have hRFCall := runs_call_of_meetsContract (r := 28) (p := pProg) (w := w) (st := st34)
    (args := [.reg 0, .reg 1, .reg 2, .reg 3, .reg 27, .reg 19, .reg 20, .reg 5, .reg 24, .reg 33])
    (vs := [k, vertsAddr, e, edgesAddr, mF', f'Addr, rhoAddr, locAddr, rAddr, rfWorkAddr]) hRF
    (by simp [evalArgs, Expr.eval, h34_r0_9 0 (by decide), hr0, h34_r0_9 1 (by decide), hr1,
          h34_r0_9 2 (by decide), hr2, h34_r0_9 3 (by decide), hr3, h34_27, h34_19, h34_20,
          h34_r0_9 5 (by decide), hr5, h34_24, h34_33, f'Addr, rhoAddr, rAddr, rfWorkAddr,
          actRestAddr, restEAddr, restVAddr, Nat.add_assoc]; omega)
    hRF_aux.2.1
    ⟨G.n, k, vertsAddr, e, edgesAddr, mF', f'Addr, rhoAddr, locAddr, rAddr, rfWorkAddr, 1, Λ,
      H.verts, H.edges, F', rfl, rfl, hRep.1, hsubV, rfl, rfl, hE_inX, hF'_inX,
      h34_V, h34_E, h34_F', h34_rho0, h34_rho1, le_rfl, hLam1, hPreRF.1, hPreRF.2,
      hRF_aux.1, hRF_aux.2.2 hdLV hdLE⟩ ω
  rcases hRFCall with ⟨stRF, cRF, kR, hrunRF, hpostRF, hRF_28, hRF_other, hcRF⟩
  dsimp only [removeFakeContract, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hpostRF hcRF
  rw [readList_eq_of_listAt h34_V, readEdges_eq_of_edgesAt h34_E, readEdges_eq_of_edgesAt h34_F',
      h34_rho0, h34_rho1] at hpostRF
  rw [h34_rho0, h34_rho1] at hcRF
  rcases hpostRF with ⟨hkR_le, hR_nd, hRX, hRF_spec, hRF_locV, hRF_fr⟩
  set R_list := readList stRF.mem rAddr kR
  set R := R_list.toFinset
  change R ⊆ H.vertSet at hRX
  have hh_r : h ≤ rAddr := by
    have h1 : h ≤ h3 := le_trans (Nat.le_add_right _ _) h3_ge
    dsimp only [rAddr, rhoAddr, f'Addr]; linarith
  have hh_rf : h ≤ rfWorkAddr := by
    dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr]; linarith
  have hRF_belowH : ∀ a < h, (∀ u ∈ H.verts, a ≠ locAddr + u) → stRF.mem a = st.mem a :=
    fun a ha haL => by
      rw [hRF_fr a haL (Or.inl (lt_of_lt_of_le ha hh_r)) (Or.inl (lt_of_lt_of_le ha hh_rf))]
      exact h34_belowH a ha
  have hRF_loc0 : ∀ u < G.n, stRF.mem (locAddr + u) = 0 := fun u hu => by
    by_cases huV : u ∈ H.verts
    · exact hRF_locV u huV
    · rw [hRF_belowH (locAddr + u) (by have := env.hlocH; linarith) (fun v hv => by
        intro heq; exact huV ((Nat.add_left_cancel heq) ▸ hv))]
      exact hloc0 u hu
  have hRF_nl : stRF.mem nextLblAddr = nl₀ := by
    rw [hRF_belowH nextLblAddr (by have := env.hnextH; linarith)
          (fun v hv => by have := hsubV v hv; rcases env.hdLN with h1 | h1 <;> omega)]
    exact hnl
  have hR_subN : ∀ u ∈ R_list, u < G.n := fun u hu =>
    Finset.mem_range.mp (hXV (hRX (List.mem_toFinset.mpr hu)))
  have hR_at : ListAt stRF.mem rAddr R_list := fun i hi => by simp [R_list, readList]
  have hrfEnd_lt' : rfWorkAddr + e * recPerWitSpace cfg M r + 3 < 2 ^ w := by
    rw [hrf_eq_full]; exact hrfEnd_lt
  have hrfW_lt : rfWorkAddr < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt (Nat.le_add_right _ _) hrfEnd_lt')
  have hrAddr_k_le_rf : rAddr + k ≤ rfWorkAddr := by
    dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr]; omega
  have hrAddr_k_lt : rAddr + k < 2 ^ w := lt_of_le_of_lt hrAddr_k_le_rf hrfW_lt
  have hh_lt : h < 2 ^ w := lt_of_le_of_lt hh_r (lt_of_le_of_lt (Nat.le_add_right _ _) hrAddr_k_lt)
  have hWCL := writeConstLabel_triple (w := w) (n := G.n) (kR := kR) (rAddr := rAddr)
    (labelsAddr := labelsAddr) (nextLblAddr := nextLblAddr) (nl := nl₀) pProg stRF R_list
    (by rw [hRF_other 6 (by decide), h34_r0_9 6 (by decide), hr6])
    (by rw [hRF_other 7 (by decide), h34_r0_9 7 (by decide), hr7])
    (by rw [hRF_other 24 (by decide), h34_24])
    hRF_28 (by simp [R_list, readList]) hR_subN hR_at hRF_nl
    (Or.inl (le_trans env.hlblH (le_trans hRoot_le hh_r))) env.hdLbN
    (lt_of_le_of_lt (Nat.add_le_add_left hkR_le rAddr) hrAddr_k_lt)
    (lt_of_le_of_lt (le_trans env.hlblH hRoot_le) hh_lt)
    (by have := env.hwN; omega)
    (by have := env.hwN; omega) hw16
  rcases hWCL stRF ω rfl with ⟨oWC, stWC, cWC, hrunWC, hqWC, hcWC⟩
  cases oWC with
  | returned _ => exact False.elim hqWC
  | normal =>
    rcases hqWC with ⟨hWC_nl, hWC_lbl, hWC_fr, hWC_r⟩
    have hh_restV : h ≤ restVAddr := by dsimp only [restVAddr]; linarith
    have hrAddr_k_le : rAddr + k ≤ restVAddr := by dsimp only [restVAddr]; linarith
    have hrestV_k_le : restVAddr + k ≤ rfWorkAddr := by
      dsimp only [rfWorkAddr, actRestAddr, restEAddr]; linarith
    have hWC_V : ListAt stWC.mem vertsAddr H.verts := fun i hi => by
      have hi_h : vertsAddr + i < h := lt_of_lt_of_le (Nat.add_lt_add_left hi vertsAddr) hVA_h
      rw [hWC_fr (vertsAddr + i) (fun u hu => by have := hR_subN u hu; rcases hdLbV with h1 | h1 <;> omega)
            (by rcases hdNV with h1 | h1 <;> omega),
          hRF_belowH (vertsAddr + i) hi_h (fun u hu => by have := hsubV u hu; rcases hdLV with h1 | h1 <;> omega)]
      exact hV i hi
    have hWC_R : ListAt stWC.mem rAddr R_list := fun i hi => by
      rw [hWC_fr (rAddr + i) (fun u hu => by have := hR_subN u hu; have := env.hlblH; linarith)
            (by have := env.hnextH; linarith)]
      exact hR_at i hi
    have hWC_loc0 : ∀ u < G.n, stWC.mem (locAddr + u) = 0 := fun u hu => by
      rw [hWC_fr (locAddr + u) (fun v hv => by have := hR_subN v hv; rcases env.hdLLb with h1 | h1 <;> omega)
            (by rcases env.hdLN with h1 | h1 <;> omega)]
      exact hRF_loc0 u hu
    have hrestV_k_lt : restVAddr + k < 2 ^ w :=
      lt_of_le_of_lt hrestV_k_le hrfW_lt
    have hrAddr_k_lt : rAddr + k < 2 ^ w := lt_of_le_of_lt hrAddr_k_le (lt_of_le_of_lt (Nat.le_add_right _ _) hrestV_k_lt)
    have hSDCall := runs_call_of_meetsContract (r := 30) (p := pProg) (w := w) (st := stWC)
      (args := [.reg 0, .reg 1, .reg 28, .reg 24, .reg 5, .reg 25])
      (vs := [k, vertsAddr, kR, rAddr, locAddr, restVAddr]) hSetDiff
      (by simp [evalArgs, Expr.eval, hWC_r 0 (Or.inl (by decide)), hWC_r 1 (Or.inl (by decide)),
            hWC_r 28 (Or.inl (by decide)), hWC_r 24 (Or.inl (by decide)),
            hWC_r 5 (Or.inl (by decide)), hWC_r 25 (Or.inl (by decide)),
            hRF_other 0 (by decide), hRF_other 1 (by decide), hRF_28,
            hRF_other 24 (by decide), hRF_other 5 (by decide), hRF_other 25 (by decide),
            h34_r0_9 0 (by decide), h34_r0_9 1 (by decide), h34_r0_9 5 (by decide),
            h34_24, h34_25, hr0, hr1, hr5, f'Addr, rhoAddr, rAddr, restVAddr])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          have := env.hlocH
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
          · exact lt_of_le_of_lt (Nat.le_add_left _ _) hrAddr_k_lt
          · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (le_trans hVA_h hh_r)) (lt_of_le_of_lt (Nat.le_add_right _ _) hrAddr_k_lt)
          · exact lt_of_le_of_lt (le_trans hkR_le (Nat.le_add_left _ _)) hrAddr_k_lt
          · exact lt_of_le_of_lt (Nat.le_add_right _ _) hrAddr_k_lt
          · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (le_trans env.hlocH (le_trans hRoot_le hh_r))) (lt_of_le_of_lt (Nat.le_add_right _ _) hrAddr_k_lt)
          · exact lt_of_le_of_lt (Nat.le_add_right _ _) hrestV_k_lt)
      ⟨G.n, k, vertsAddr, kR, rAddr, locAddr, restVAddr, H.verts, R_list, rfl,
        rfl, hsubV, by simp [R_list, readList], hR_subN, hWC_V, hWC_R, hWC_loc0,
        lt_of_le_of_lt (le_trans hVA_h hh_r) (lt_of_le_of_lt (Nat.le_add_right _ _) hrAddr_k_lt),
        lt_of_le_of_lt (Nat.add_le_add_left hkR_le rAddr) hrAddr_k_lt,
        lt_of_le_of_lt (le_trans env.hlocH (le_trans hRoot_le hh_r)) (lt_of_le_of_lt (Nat.le_add_right _ _) hrAddr_k_lt),
        hrestV_k_lt, hw16,
        hdLV, Or.inl (le_trans env.hlocH (le_trans hRoot_le hh_r)),
        Or.inl (le_trans env.hlocH (le_trans hRoot_le hh_restV)),
        Or.inr (le_trans hVA_h hh_restV), Or.inr (le_trans (Nat.add_le_add_left hkR_le rAddr) hrAddr_k_le)⟩ ω
    rcases hSDCall with ⟨stSD, cSD, kRest, hrunSD, hpostSD, hSD_30, hSD_other, hcSD⟩
    dsimp only [setDiffContract, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hpostSD hcSD
    have hRlen : R_list.length = kR := by simp [R_list, readList]
    have hV_rd : readList stWC.mem vertsAddr k = H.verts := readList_eq_of_listAt hWC_V
    have hR_rd : readList stWC.mem rAddr kR = R_list := by
      rw [← hRlen]; exact readList_eq_of_listAt hWC_R
    simp only [hV_rd, hR_rd] at hpostSD
    have hdiff_eq : (H.verts.filter fun u => decide (u ∉ R)) = (H.restrict (H.vertSet \ R)).verts := by
      unfold CompactSubgraph.restrict
      apply List.filter_congr; intro u hu
      have huX : u ∈ H.vertSet := List.mem_toFinset.mpr hu
      simp [Finset.mem_sdiff, huX]
    rw [hdiff_eq] at hpostSD
    rcases hpostSD with ⟨hkRest_eq, hSD_restV, hSD_fr⟩
    have hSD_r0_9 : ∀ r' ≤ 9, stSD.regs r' = st.regs r' := fun r' hr' => by
      rw [hSD_other r' (by omega), hWC_r r' (Or.inl (by omega)), hRF_other r' (by omega), h34_r0_9 r' hr']
    have hrfB_le := hrf_sp.2
    refine ⟨stSD, R_list, cRF, cWC, cSD,
      by linarith only [hRlen, hkR_le], hR_nd, hRX, hRF_spec,
      by rw [hSD_30, hkRest_eq],
      by rw [hSD_other 25 (by decide), hWC_r 25 (Or.inl (by decide)), hRF_other 25 (by decide), h34_25],
      by rw [hSD_other 26 (by decide), hWC_r 26 (Or.inl (by decide)), hRF_other 26 (by decide), h34_26]; ring,
      by rw [hSD_other 29 (by decide), hWC_r 29 (Or.inl (by decide)), hRF_other 29 (by decide), h34_29]; ring,
      by rw [hSD_other 34 (by decide), hWC_r 34 (Or.inr (by decide)), hRF_other 34 (by decide), h34_34]; dsimp only [h4, rfWorkAddr, actRestAddr, restEAddr, restVAddr, Λ, cfg]; ring,
      hSD_r0_9, hSD_restV,
      fun u hu => by
        have hu_h : labelsAddr + u < h :=
          lt_of_lt_of_le (Nat.add_lt_add_left (Finset.mem_range.mp (hXV (hRX hu))) labelsAddr)
            (le_trans env.hlblH hRoot_le)
        rw [hSD_fr (labelsAddr + u) (Or.inl (lt_of_lt_of_le hu_h hh_restV))]
        exact hWC_lbl u (List.mem_toFinset.mp hu),
      by rw [hSD_fr nextLblAddr (Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self nextLblAddr) (le_trans env.hnextH hRoot_le)) hh_restV))]; exact hWC_nl,
      fun u hu => by
        rw [hSD_fr (locAddr + u) (Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hu locAddr) (le_trans env.hlocH hRoot_le)) hh_restV))]
        exact hWC_loc0 u hu,
      fun a ha => by
        have hrf_le_h4 : rfWorkAddr + rfWorkBound k e mF' Λ L ≤ a := ha
        have hrf_le_a : rfWorkAddr ≤ a := le_trans (Nat.le_add_right _ _) hrf_le_h4
        have hrestV_k_le_a : restVAddr + k ≤ a := le_trans hrestV_k_le hrf_le_a
        have hr_k_le_a : rAddr + k ≤ a := le_trans hrAddr_k_le_rf hrf_le_a
        have hr_le_a : rAddr ≤ a := le_trans (Nat.le_add_right _ _) hr_k_le_a
        have hh_le_a : h ≤ a := le_trans hh_rf hrf_le_a
        have hh3_le_a : h3 ≤ a := le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hr_le_a
        rw [hSD_fr a (Or.inr hrestV_k_le_a),
            hWC_fr a (fun u hu => ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left (hR_subN u hu) labelsAddr) (le_trans env.hlblH hRoot_le)) hh_le_a))
              (ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self nextLblAddr) (le_trans env.hnextH hRoot_le)) hh_le_a)),
            hRF_fr a (fun u hu => ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left (hsubV u hu) locAddr) (le_trans env.hlocH hRoot_le)) hh_le_a))
              (Or.inr hr_k_le_a) (Or.inr (le_trans (Nat.add_le_add_left hRF_ws_le rfWorkAddr) hrf_le_h4)),
            h34_fr a (Or.inr hr_le_a)]
        exact hZero3 a hh3_le_a,
      fun a ha haR haN haL => by
        rw [hSD_fr a (Or.inl (lt_of_lt_of_le ha hh_restV)),
            hWC_fr a (fun u hu => haR u (List.mem_toFinset.mpr hu)) haN,
            hRF_belowH a ha haL],
      by simp only [argsSize, Expr.size, Nat.add_zero] at hcRF; linarith only [hcRF],
      by dsimp at hcWC; linarith only [hcWC, hRlen],
      by simp only [argsSize, Expr.size, setDiffCost, Nat.add_zero] at hcSD; linarith only [hcSD, hRlen],
      fun rest oEnd stEnd cRest hRest =>
        runs_seq_iff.mpr (Or.inr ⟨stRF, cRF, _, hrunRF,
          runs_seq_iff.mpr (Or.inr ⟨stWC, cWC, _, hrunWC,
            runs_seq_iff.mpr (Or.inr ⟨stSD, cSD, cRest, hrunSD, hRest, rfl⟩), rfl⟩), rfl⟩)⟩


end MinCostFlow.ExpanderDecomp
