module

public import MinCostFlow.ExpanderDecomp.RouteProgResCsrBase
public import MinCostFlow.ExpanderDecomp.RouteProgCurB

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual Neighbor-Only CSR Builder Verification (`RouteProgResCsr`)

Outer loop verification (`resCsrOuterLoop_triple`) and full contract proof
(`buildResCsr_meetsContract`) for `buildResCsrProc`, re-exporting `RouteProgResCsrBase` and
`RouteProgCurB`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma resCsrOuterLoop_triple {w : ℕ} {p : Program}
    {G : Graph} {X V : Finset ℕ} {m2 offAddr nbAddr maskArrAddr maskBadVal
      resOffAddr resNbAddr : ℕ}
    (hVX : V ⊆ X)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ m2)
    (hdisj : ResCsrDisj w X.card m2 offAddr nbAddr maskArrAddr maskBadVal resOffAddr resNbAddr)
    (rem : ℕ) :
    ∀ (u : ℕ) (st0 : State),
      u + rem = X.card →
      NbCsrAt st0.mem offAddr nbAddr X (adjOf G X) →
      (∀ v < X.card, st0.mem (maskArrAddr + v) ≠ maskBadVal ↔ origOf X v ∈ V) →
      st0.regs 0 = offAddr →
      st0.regs 1 = nbAddr →
      st0.regs 2 = maskArrAddr →
      st0.regs 3 = maskBadVal →
      st0.regs 4 = X.card →
      st0.regs 5 = resOffAddr →
      st0.regs 6 = resNbAddr →
      st0.regs 7 = adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) u →
      st0.regs 8 = u →
      (∀ i < u, st0.mem (resOffAddr + i) = adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) i) →
      (∀ i < u, ∀ j (hj : j < (adjOf ⟨G.n, G.inside V⟩ X (origOf X i)).length),
        st0.mem (resNbAddr + adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) i + j) =
          locOf X ((adjOf ⟨G.n, G.inside V⟩ X (origOf X i))[j]'hj).1) →
      ∀ ω,
        ∃ st' c,
          Runs w p ω resCsrOuterLoop st0 .normal st' c ∧
          st'.regs 4 = X.card ∧
          st'.regs 5 = resOffAddr ∧
          st'.regs 7 = adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) X.card ∧
          (∀ i < X.card, st'.mem (resOffAddr + i) = adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) i) ∧
          (∀ i < X.card, ∀ j (hj : j < (adjOf ⟨G.n, G.inside V⟩ X (origOf X i)).length),
            st'.mem (resNbAddr + adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) i + j) =
              locOf X ((adjOf ⟨G.n, G.inside V⟩ X (origOf X i))[j]'hj).1) ∧
          (∀ a, ¬ ResCsrWriteSet X.card m2 resOffAddr resNbAddr a → st'.mem a = st0.mem a) ∧
          c ≤ 65 * rem + 40 * (adjCsrOff X (adjOf G X) X.card - adjCsrOff X (adjOf G X) u) + 10 := by
  have hw_off := hdisj.w_off; have hw_nb := hdisj.w_nb; have hw_mask := hdisj.w_mask
  have hw_ro := hdisj.w_ro; have hw_rn := hdisj.w_rn; have hw_nX := hdisj.w_nX
  have hw_m2 := hdisj.w_m2; have hw_mb := hdisj.w_mb; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  set adjRes := adjOf ⟨G.n, G.inside V⟩ X
  induction rem with
  | zero =>
    intro u st0 hu hcsr hmask hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hro hrn ω
    have hu_eq : u = X.card := by omega
    subst hu_eq
    have hcond : (Expr.bin .lt (.reg 8) (.reg 4)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr8, hr4]
    refine ⟨st0, (Expr.bin .lt (.reg 8) (.reg 4)).size + 1,
      runs_loop_zero hcond, hr4, hr5, hr7, hro, hrn, fun _ _ => rfl, by simp [Expr.size]⟩
  | succ rem ih =>
    intro u st0 hu hcsr hmask hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hro hrn ω
    have hu_lt : u < X.card := by omega
    have hres_le_m2 : adjCsrOff X adjRes u ≤ m2 :=
      le_trans (adjCsrOff_inside_le G hVX u) (le_trans (adjCsrOff_mono X (adjOf G X) (by omega)) hm2)
    have hres_succ : adjCsrOff X adjRes (u + 1) =
        adjCsrOff X adjRes u + (adjRes (origOf X u)).length :=
      adjCsrOff_succ X adjRes u
    have hres_succ_le_m2 : adjCsrOff X adjRes (u + 1) ≤ m2 :=
      le_trans (adjCsrOff_inside_le G hVX (u + 1)) (le_trans (adjCsrOff_mono X (adjOf G X) (by omega)) hm2)
    have hG_succ : adjCsrOff X (adjOf G X) (u + 1) =
        adjCsrOff X (adjOf G X) u + (adjOf G X (origOf X u)).length :=
      adjCsrOff_succ X (adjOf G X) u
    have hG_mono : adjCsrOff X (adjOf G X) (u + 1) ≤ adjCsrOff X (adjOf G X) X.card :=
      adjCsrOff_mono X (adjOf G X) (by omega)
    have hcond : (Expr.bin .lt (.reg 8) (.reg 4)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr8, hr4, hu_lt, hw_ne]
    -- Step 1: store resOff[u] := pos; r9 := mask[u]
    set mem1 := Function.update st0.mem (resOffAddr + u) (adjCsrOff X adjRes u)
    have hmem1_fr : ∀ a, a ≠ resOffAddr + u → mem1 a = st0.mem a :=
      fun a ha => Function.update_of_ne ha _ _
    set mval := st0.mem (maskArrAddr + u)
    have hmval_mem1 : mem1 (maskArrAddr + u) = mval :=
      hmem1_fr _ (by rcases hdisj.ro_mask with x | x <;> omega)
    set st1 : State := { mem := mem1, regs := Function.update st0.regs 9 mval, pos := st0.pos }
    have hstep1 : ∃ c1,
        Runs w p ω
          (seqStmts
            [ .store (.bin .add (.reg 5) (.reg 8)) (.reg 7)
            , .assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ])
          st0 .normal st1 c1 ∧ c1 ≤ 15 := by
      have h0 : ∃ o s c,
          Runs w p ω
            (seqStmts
              [ .store (.bin .add (.reg 5) (.reg 8)) (.reg 7)
              , .assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ])
            st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 15 := by
        dsimp only [seqStmts]
        refine runs_seq_store_le (x := resOffAddr + u) (v := adjCsrOff X adjRes u)
          (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := mval)
          (by simp only [Expr.eval, BinOp.eval, hr2, hr8, show maskArrAddr + u < 2 ^ w by omega,
                ↓reduceIte]; exact congrArg some hmval_mem1)
          ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
      exact ⟨c1, hrun, by omega⟩
    rcases hstep1 with ⟨c1, hrun1, hc1⟩
    have hcsr1 : NbCsrAt st1.mem offAddr nbAddr X (adjOf G X) :=
      hcsr.congr (fun i hi => hmem1_fr _ (by rcases hdisj.ro_off with x | x <;> omega))
        (fun j hj => hmem1_fr _ (by rcases hdisj.ro_nb with x | x <;> omega))
    have hmask1 : ∀ v < X.card, st1.mem (maskArrAddr + v) ≠ maskBadVal ↔ origOf X v ∈ V := by
      intro v hv
      rw [show st1.mem _ = mem1 _ from rfl, hmem1_fr _ (by rcases hdisj.ro_mask with x | x <;> omega)]
      exact hmask v hv
    have hmval_iff : mval ≠ maskBadVal ↔ origOf X u ∈ V := hmask u hu_lt
    -- Branch on origOf X u ∈ V
    have hcond_step : ∃ st2 c2,
        Runs w p ω
          (.cond (.bin .eq (.reg 9) (.reg 3))
            .nop
            (seqStmts
              [ .assign 10 (.load (.bin .add (.reg 0) (.reg 8)))
              , .assign 11 (.load (.bin .add (.reg 0) (.bin .add (.reg 8) (.const 1))))
              , resCsrInnerLoop ]))
          st1 .normal st2 c2 ∧
        (∀ r, r ≠ 7 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → st2.regs r = st1.regs r) ∧
        st2.regs 7 = adjCsrOff X adjRes (u + 1) ∧
        NbCsrAt st2.mem offAddr nbAddr X (adjOf G X) ∧
        (∀ v < X.card, st2.mem (maskArrAddr + v) ≠ maskBadVal ↔ origOf X v ∈ V) ∧
        (∀ i < u + 1, st2.mem (resOffAddr + i) = adjCsrOff X adjRes i) ∧
        (∀ i < u + 1, ∀ j (hj : j < (adjRes (origOf X i)).length),
          st2.mem (resNbAddr + adjCsrOff X adjRes i + j) = locOf X ((adjRes (origOf X i))[j]'hj).1) ∧
        (∀ a, ¬ ResCsrWriteSet X.card m2 resOffAddr resNbAddr a → st2.mem a = st0.mem a) ∧
        c2 ≤ 40 * (adjOf G X (origOf X u)).length + 35 := by
      by_cases huV : origOf X u ∈ V
      · have hne_mb : mval ≠ maskBadVal := hmval_iff.mpr huV
        have hlen_res : (adjRes (origOf X u)).length =
            ((adjOf G X (origOf X u)).filter fun e => decide (e.1 ∈ V)).length := by
          have := adjOf_inside_length G hVX (origOf X u); simp [adjRes, huV] at this ⊢; exact this
        have hbase_le : adjCsrOff X adjRes u +
            ((adjOf G X (origOf X u)).filter fun e => decide (e.1 ∈ V)).length ≤ m2 := by
          omega
        set lo := adjCsrOff X (adjOf G X) u
        set hi := adjCsrOff X (adjOf G X) u + (adjOf G X (origOf X u)).length
        have hhi_eq : adjCsrOff X (adjOf G X) (u + 1) = hi := hG_succ
        set st1a : State :=
          { mem := st1.mem
            regs := Function.update (Function.update st1.regs 10 lo) 11 hi
            pos := st1.pos }
        have hload_lohi : ∃ cLH,
            Runs w p ω
              (seqStmts
                [ .assign 10 (.load (.bin .add (.reg 0) (.reg 8)))
                , .assign 11 (.load (.bin .add (.reg 0) (.bin .add (.reg 8) (.const 1)))) ])
              st1 .normal st1a cLH ∧ cLH ≤ 16 := by
          have h0 : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 10 (.load (.bin .add (.reg 0) (.reg 8)))
                  , .assign 11 (.load (.bin .add (.reg 0) (.bin .add (.reg 8) (.const 1)))) ])
                st1 o s c ∧ (o = .normal ∧ s = st1a) ∧ 0 + c ≤ 16 := by
            dsimp only [seqStmts]
            have h1_0 : st1.regs 0 = offAddr := by simp [st1, hr0]
            have h1_8 : st1.regs 8 = u := by simp [st1, hr8]
            have hlo_m : st1.mem (offAddr + u) = lo := hcsr1.1 u (by omega)
            have hhi_m : st1.mem (offAddr + (u + 1)) = hi := by
              rw [← hhi_eq]; exact hcsr1.1 (u + 1) (by omega)
            refine runs_seq_assign_le (v := lo) (by rw [← hlo_m]; eval_expr) ?_
            refine runs_assign_le (v := hi) (by rw [← hhi_m]; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0 with ⟨_, _, cLH, hrun, ⟨rfl, rfl⟩, hcLH⟩
          exact ⟨cLH, hrun, by omega⟩
        rcases hload_lohi with ⟨cLH, hrunLH, hcLH⟩
        obtain ⟨st2, cIn, hrunIn, hregsIn, hr7In, hprefIn, hfrIn, hcIn⟩ :=
          resCsrInnerLoop_triple hVX hm2 hdisj hu_lt huV hbase_le
            (adjOf G X (origOf X u)).length 0 st1a (Nat.zero_add _)
            hcsr1 hmask1
            (by simp [st1a, st1, hr1]) (by simp [st1a, st1, hr2])
            (by simp [st1a, st1, hr3]) (by simp [st1a, st1, hr6])
            (by simp [st1a, st1, hr7])
            (by simp [st1a, lo]) (by simp [st1a, hi])
            (fun _ h => by simp at h) ω
        have hrun_else : Runs w p ω
            (seqStmts
              [ .assign 10 (.load (.bin .add (.reg 0) (.reg 8)))
              , .assign 11 (.load (.bin .add (.reg 0) (.bin .add (.reg 8) (.const 1))))
              , resCsrInnerLoop ])
            st1 .normal st2 (cLH + cIn + 1) := by
          dsimp only [seqStmts] at hrunLH ⊢
          rcases runs_seq_iff.mp hrunLH with ⟨_, _, _, h, _⟩ | ⟨q, cq1, cq2, hq1, hq2, rfl⟩; · cases h
          refine runs_seq_iff.mpr (Or.inr ⟨q, cq1, cq2 + cIn + 1, hq1,
            runs_seq_iff.mpr (Or.inr ⟨st1a, cq2, cIn, hq2, hrunIn, rfl⟩), by omega⟩)
        have hev_eq : (Expr.bin .eq (.reg 9) (.reg 3)).eval w st1 = some 0 := by
          simp [Expr.eval, BinOp.eval, st1, hr3, hne_mb]
        refine ⟨st2, _, runs_cond_zero hev_eq hrun_else, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro r h7 h10 h11 h12 h13
          rw [hregsIn r h7 h10 h12 h13]; simp [st1a, h10, h11]
        · rw [hr7In, hres_succ, hlen_res]
        · exact hcsr1.congr
            (fun i hi => hfrIn _ (by rcases hdisj.rn_off with x | x <;> omega))
            (fun j hj => hfrIn _ (by rcases hdisj.rn_nb with x | x <;> omega))
        · intro v hv
          rw [hfrIn _ (by rcases hdisj.rn_mask with x | x <;> omega)]
          exact hmask1 v hv
        · intro i hi
          rw [hfrIn _ (by rcases hdisj.ro_rn with x | x <;> omega)]
          by_cases hiu : i < u
          · rw [show st1a.mem _ = mem1 _ from rfl, hmem1_fr _ (by omega)]; exact hro i hiu
          · have hi_eq : i = u := by omega
            subst hi_eq; simp [st1a, st1, mem1]
        · intro i hi j hj
          by_cases hiu : i < u
          · have hlt_base : adjCsrOff X adjRes i + j < adjCsrOff X adjRes u := by
              have h1 := adjCsrOff_succ X adjRes i
              have h2 := adjCsrOff_mono X adjRes (show i + 1 ≤ u by omega)
              omega
            rw [Nat.add_assoc, hfrIn _ (by simp; omega), show st1a.mem _ = mem1 _ from rfl,
                hmem1_fr _ (by rcases hdisj.ro_rn with x | x <;> omega), ← Nat.add_assoc]
            exact hrn i hiu j hj
          · have hi_eq : i = u := by omega
            rcases hi_eq with rfl
            have hj' : j < ((adjOf G X (origOf X i)).filter fun e => decide (e.1 ∈ V)).length := by
              omega
            rw [hprefIn j hj', adjOf_inside_getElem_fst G hVX huV hj]
        · intro a ha
          rw [hfrIn a (fun h => ha (Or.inr ⟨by omega, h.2⟩)),
              show st1a.mem a = mem1 a from rfl,
              hmem1_fr a (fun h => ha (Or.inl ⟨by omega, by omega⟩))]
        · simp only [Expr.size]; omega
      · -- u ∉ V: skip inner loop, resOff[u+1] = resOff[u]
        have heq_mb : mval = maskBadVal := by by_contra hne; exact huV (hmval_iff.mp hne)
        have hlen_zero : (adjRes (origOf X u)).length = 0 := by
          have := adjOf_inside_length G hVX (origOf X u); simp [adjRes, huV] at this ⊢; exact this
        have hev_eq : (Expr.bin .eq (.reg 9) (.reg 3)).eval w st1 = some 1 := by
          simp [Expr.eval, BinOp.eval, st1, hr3, heq_mb, hw_ne]
        refine ⟨st1, _, runs_cond_pos hev_eq (by decide) (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
          fun _ _ _ _ _ _ => rfl, ?_, hcsr1, hmask1, ?_, ?_, ?_, ?_⟩
        · simp [st1, hr7, hres_succ, hlen_zero]
        · intro i hi
          by_cases hiu : i < u
          · rw [show st1.mem _ = mem1 _ from rfl, hmem1_fr _ (by omega)]; exact hro i hiu
          · have hi_eq : i = u := by omega
            subst hi_eq; simp [st1, mem1]
        · intro i hi j hj
          by_cases hiu : i < u
          · have hlt_m2 : adjCsrOff X adjRes i + j < m2 := by
              have h1 := adjCsrOff_succ X adjRes i
              have h2 := adjCsrOff_mono X adjRes (show i + 1 ≤ u by omega)
              omega
            rw [Nat.add_assoc, show st1.mem _ = mem1 _ from rfl,
                hmem1_fr _ (by rcases hdisj.ro_rn with x | x <;> omega), ← Nat.add_assoc]
            exact hrn i hiu j hj
          · have hi_eq : i = u := by omega
            subst hi_eq; omega
        · intro a ha
          exact hmem1_fr a (fun h => ha (Or.inl ⟨by omega, by omega⟩))
        · simp only [Expr.size]; omega
    rcases hcond_step with ⟨st2, c2, hrun2, hregs2, hr7_2, hcsr2, hmask2, hro2, hrn2, hfr2, hc2⟩
    -- Step 3: r8 := r8 + 1
    set st3 : State := { st2 with regs := Function.update st2.regs 8 (u + 1) }
    have h2_8 : st2.regs 8 = u := by
      rw [hregs2 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st1, hr8]
    have hrun3 : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) st2 .normal st3
        ((Expr.bin .add (.reg 8) (.const 1)).size + 1) :=
      runs_assign_iff.mpr ⟨u + 1,
        by simp [Expr.eval, BinOp.eval, h2_8, show 1 < 2 ^ w by omega, show u + 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    -- Compose body of outer loop
    have hbody_all : Runs w p ω
        (seqStmts
          [ .store (.bin .add (.reg 5) (.reg 8)) (.reg 7)
          , .assign 9 (.load (.bin .add (.reg 2) (.reg 8)))
          , .cond (.bin .eq (.reg 9) (.reg 3))
              .nop
              (seqStmts
                [ .assign 10 (.load (.bin .add (.reg 0) (.reg 8)))
                , .assign 11 (.load (.bin .add (.reg 0) (.bin .add (.reg 8) (.const 1))))
                , resCsrInnerLoop ])
          , .assign 8 (.bin .add (.reg 8) (.const 1)) ])
        st0 .normal st3 (c1 + c2 + ((Expr.bin .add (.reg 8) (.const 1)).size + 1) + 2) := by
      dsimp only [seqStmts] at hrun1 ⊢
      rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, h, _⟩ | ⟨q, cq1, cq2, hq1, hq2, rfl⟩; · cases h
      refine runs_seq_iff.mpr (Or.inr ⟨q, cq1, _, hq1,
        runs_seq_iff.mpr (Or.inr ⟨st1, cq2, _, hq2,
          runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2, hrun3, rfl⟩), rfl⟩), by omega⟩)
    -- Recurse on rem, u + 1
    obtain ⟨stF, cIH, hrunIH, hF4, hF5, hF7, hroF, hrnF, hfrF, hcIH⟩ :=
      ih (u + 1) st3 (by omega) hcsr2 hmask2
        (by simp [st3, hregs2 0 (by decide) (by decide) (by decide) (by decide) (by decide), st1, hr0])
        (by simp [st3, hregs2 1 (by decide) (by decide) (by decide) (by decide) (by decide), st1, hr1])
        (by simp [st3, hregs2 2 (by decide) (by decide) (by decide) (by decide) (by decide), st1, hr2])
        (by simp [st3, hregs2 3 (by decide) (by decide) (by decide) (by decide) (by decide), st1, hr3])
        (by simp [st3, hregs2 4 (by decide) (by decide) (by decide) (by decide) (by decide), st1, hr4])
        (by simp [st3, hregs2 5 (by decide) (by decide) (by decide) (by decide) (by decide), st1, hr5])
        (by simp [st3, hregs2 6 (by decide) (by decide) (by decide) (by decide) (by decide), st1, hr6])
        (by simp [st3, hr7_2]) (by simp [st3]) hro2 hrn2 ω
    refine ⟨stF, _, runs_loop_step hcond (by decide) hbody_all hrunIH,
      hF4, hF5, hF7, hroF, hrnF, fun a ha => (hfrF a ha).trans (hfr2 a ha), ?_⟩
    simp only [Expr.size]
    omega

/-- `buildResCsrProc` meets `buildResCsrContract` deterministically. -/
theorem buildResCsr_meetsContract {w : ℕ} {p : Program} {idx : ℕ}
    (hproc : p.procs[idx]? = some buildResCsrProc)
    (G : Graph) (X V : Finset ℕ) (m2 : ℕ) :
    MeetsContract w p idx (buildResCsrContract w G X V m2) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨hlen, hnX, hVX, hcsr, hm2, hmask, hdisj⟩
  set offAddr := args.getD 0 0
  set nbAddr := args.getD 1 0
  set maskArrAddr := args.getD 2 0
  set maskBadVal := args.getD 3 0
  set resOffAddr := args.getD 5 0
  set resNbAddr := args.getD 6 0
  set adjRes := adjOf ⟨G.n, G.inside V⟩ X
  have hw_ro := hdisj.w_ro; have hw_m2 := hdisj.w_m2; have hw4 := hdisj.w_4
  refine ⟨buildResCsrProc, hproc, ?_⟩
  set st0 := startState args mem pos
  have hst0_mem : st0.mem = mem := rfl
  have hr_arg : ∀ i < 7, st0.regs i = args.getD i 0 := fun i hi => by
    simp [st0, startState, List.getD_eq_getElem?_getD, hi, hlen]
  set st1 : State :=
    { mem := mem
      regs := Function.update (Function.update st0.regs 7 0) 8 0
      pos := pos }
  have hinit : ∃ c1,
      Runs w p ω (seqStmts [ .assign 7 (.const 0), .assign 8 (.const 0) ]) st0 .normal st1 c1 ∧
      c1 ≤ 10 := by
    have h0 : ∃ o s c,
        Runs w p ω (seqStmts [ .assign 7 (.const 0), .assign 8 (.const 0) ]) st0 o s c ∧
        (o = .normal ∧ s = st1) ∧ 0 + c ≤ 10 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
    exact ⟨c1, hrun, by omega⟩
  rcases hinit with ⟨c1, hrun1, hc1⟩
  obtain ⟨st2, c2, hrun2, h2_4, h2_5, h2_7, hro2, hrn2, hfr2, hc2⟩ :=
    resCsrOuterLoop_triple (p := p) hVX hm2 hdisj X.card 0 st1 (Nat.zero_add _)
      hcsr hmask
      (by simp [st1, hr_arg 0 (by decide), offAddr])
      (by simp [st1, hr_arg 1 (by decide), nbAddr])
      (by simp [st1, hr_arg 2 (by decide), maskArrAddr])
      (by simp [st1, hr_arg 3 (by decide), maskBadVal])
      (by simp [st1, hr_arg 4 (by decide)]; exact hnX)
      (by simp [st1, hr_arg 5 (by decide), resOffAddr])
      (by simp [st1, hr_arg 6 (by decide), resNbAddr])
      (by simp [st1, adjCsrOff]) (by simp [st1])
      (fun _ h => by omega) (fun _ h => by omega) ω
  have hres_le_m2 : adjCsrOff X adjRes X.card ≤ m2 :=
    le_trans (adjCsrOff_inside_le G hVX X.card) hm2
  set mem3 := Function.update st2.mem (resOffAddr + X.card) (adjCsrOff X adjRes X.card)
  set st3 : State := { st2 with mem := mem3 }
  have htail : ∃ c3,
      Runs w p ω (seqStmts [ .store (.bin .add (.reg 5) (.reg 4)) (.reg 7), .ret (.reg 7) ])
        st2 (.returned (adjCsrOff X adjRes X.card)) st3 c3 ∧ c3 ≤ 12 := by
    have h0 : ∃ o s c,
        Runs w p ω (seqStmts [ .store (.bin .add (.reg 5) (.reg 4)) (.reg 7), .ret (.reg 7) ])
          st2 o s c ∧ (o = .returned (adjCsrOff X adjRes X.card) ∧ s = st3) ∧ 0 + c ≤ 12 := by
      dsimp only [seqStmts]
      refine runs_seq_store_le (x := resOffAddr + X.card) (v := adjCsrOff X adjRes X.card)
        (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := adjCsrOff X adjRes X.card) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c3, hrun, ⟨rfl, rfl⟩, hc3⟩
    exact ⟨c3, hrun, by omega⟩
  rcases htail with ⟨c3, hrun3, hc3⟩
  have hrun_all : Runs w p ω buildResCsrProc st0 (.returned (adjCsrOff X adjRes X.card)) st3
      (c1 + c2 + c3 + 2) := by
    unfold buildResCsrProc; dsimp only [seqStmts] at hrun1 hrun3 ⊢
    rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, h, _⟩ | ⟨q, cq1, cq2, hq1, hq2, rfl⟩; · cases h
    refine runs_seq_iff.mpr (Or.inr ⟨q, cq1, _, hq1,
      runs_seq_iff.mpr (Or.inr ⟨st1, cq2, _, hq2,
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3, hrun2, hrun3, rfl⟩), rfl⟩), by omega⟩)
  refine ⟨.returned (adjCsrOff X adjRes X.card), st3, c1 + c2 + c3 + 2, hrun_all, ?_, ?_⟩
  · dsimp only [buildResCsrContract, Outcome.value]
    refine ⟨rfl, hres_le_m2, ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      change st3.mem (resOffAddr + i) = adjCsrOff X adjRes i
      by_cases hlt : i < X.card
      · simp only [st3, mem3, Function.update_of_ne (by omega : resOffAddr + i ≠ resOffAddr + X.card)]
        exact hro2 i hlt
      · have hi_eq : i = X.card := by omega
        subst hi_eq; simp [st3, mem3]
    · intro i hi j hj
      change st3.mem (resNbAddr + adjCsrOff X adjRes i + j) = locOf X ((adjRes (origOf X i))[j]'hj).1
      have hj' : j < (adjRes (origOf X i)).length := hj
      have hlt_m2 : adjCsrOff X adjRes i + j < m2 := by
        have h1 := adjCsrOff_succ X adjRes i
        have h2 := adjCsrOff_mono X adjRes (show i + 1 ≤ X.card by omega)
        omega
      rw [Nat.add_assoc]
      simp only [st3, mem3,
        Function.update_of_ne (by rcases hdisj.ro_rn with x | x <;> omega : resNbAddr + (adjCsrOff X adjRes i + j) ≠ resOffAddr + X.card)]
      rw [← Nat.add_assoc]
      exact hrn2 i hi j hj
    · intro a ha
      simp only [st3, mem3,
        Function.update_of_ne (fun h => ha (Or.inl ⟨by omega, by omega⟩) : a ≠ resOffAddr + X.card)]
      exact hfr2 a ha
  · dsimp only [buildResCsrContract, buildResCsrCost]
    have h0_off : adjCsrOff X (adjOf G X) 0 = 0 := by simp [adjCsrOff]
    rw [h0_off, Nat.sub_zero] at hc2
    omega


end MinCostFlow.ExpanderDecomp
