module

public import MinCostFlow.SparseCore.Program.CompCutLogStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of Forest-Cut Logging Root Closure (`CompCutLog`)

Verifies `compLogPopLoop_runs` and `compLogAddOrigRoot_runs`, proving that
`compLogAddOrigRootProc` preserves `LSFRep h`, appends the exact ordered forest cuts
`(cutE, newRoot)` to `(fDelBuf, rootsBuf)`, satisfies `CompForestCutsValid` and exact `RF`
transition, and yields `120` steps of free amortized credit per cut from the `lsfPhi` drop.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 2. Pop-loop verification -/

open Classical in
private lemma compLogPopLoop_runs {w b idxMinUp idxDgDel idxBFS rootsBuf fDelBuf cntPtr cap : ℕ}
    {p : Program} {ω : ℕ → Bool} {x0 : LSFConcrete}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x0.endAddr b < 2 ^ w)
    (hbuf : CutLogBufOk w b (x0.endAddr b) rootsBuf fDelBuf cntPtr cap)
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x0.vList x0.tOrigList))
    (hDgDel : ∀ F, MeetsContract w p idxDgDel (dgDeleteEdgeContract w x0.vCap (fECap x0.eCap x0.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F)) :
    ∀ (stk : List ℕ) (cnt : ℕ) (S : LSFState) (x : LSFConcrete) (st : State),
      cnt + stk.length ≤ cap →
      st.mem cntPtr = cnt →
      st.regs 40 = rootsBuf → st.regs 41 = fDelBuf → st.regs 42 = cntPtr →
      SameStaticConcrete x0 x →
      (LSFRep x0.h).rep b S x st.mem →
      PopRegsOk b x st.regs →
      st.regs 23 = stk.length →
      stk.length ≤ hldDepthBound x0.n0 →
      StackMemAt st.mem (auxThStackBase (lsfAuxPtr b x0.vCap x0.eCap x0.n0 x0.tM x0.L_w) x0.vCap x0.n0) stk →
      ThStackInv S x0.vList x0.thParent x0.n0 stk →
      ∃ st' c x' cuts,
        Runs w p ω (.loop (.reg 23) (compLogPopStepStmt idxMinUp idxDgDel idxBFS)) st .normal st' c ∧
        SameStaticConcrete x0 x' ∧
        (LSFRep x0.h).rep b (applyThStack S x0.vList stk) x' st'.mem ∧
        cuts.length = stk.length ∧
        st'.mem cntPtr = cnt + cuts.length ∧
        (∀ i (hi : i < cuts.length),
          st'.mem (rootsBuf + (cnt + i)) = cuts[i].2 ∧ st'.mem (fDelBuf + (cnt + i)) = cuts[i].1) ∧
        (∀ a, (a < b ∨ x0.endAddr b ≤ a) → a ≠ cntPtr →
          (a < rootsBuf + cnt ∨ rootsBuf + cnt + cuts.length ≤ a) →
          (a < fDelBuf + cnt ∨ fDelBuf + cnt + cuts.length ≤ a) →
          st'.mem a = st.mem a) ∧
        CompForestCutsValid x0.vCap S.RF cuts ∧
        cuts.foldl compApplyForestCut S.RF = (applyThStack S x0.vList stk).RF ∧
        (cuts.map Prod.fst).Nodup ∧
        (cuts.map Prod.fst).toFinset = S.RF.F.E \ (applyThStack S x0.vList stk).RF.F.E ∧
        (cuts.map Prod.snd).Nodup ∧
        (cuts.map Prod.snd).toFinset = (applyThStack S x0.vList stk).RF.R \ S.RF.R ∧
        c + 150 * stk.length + lsfPhi b x' st'.mem ≤ 5 + lsfPhi b x st.mem := by
  intro stk
  induction stk with
  | nil =>
    intro cnt S x st _ hcnt _ _ _ hsame hrep _ hr23 _ _ _
    have hcond : (Expr.reg 23).eval w st = some 0 := by
      have := Expr.eval_reg (w := w) 23 st; rwa [hr23] at this
    refine ⟨st, _, x, [], runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hsame, hrep, rfl,
      by simpa using hcnt, fun _ hi => by simp at hi, fun _ _ _ _ _ => rfl, trivial, rfl,
      List.nodup_nil, by simp [applyThStack], List.nodup_nil, by simp [applyThStack],
      by dsimp [Expr.size]; omega⟩
  | cons zIdx rest ih =>
    intro cnt S x st hcap hcnt hr40 hr41 hr42 hsame hrep hregs hr23 hlen hstk hThInv
    have hcond : (Expr.reg 23).eval w st = some (rest.length + 1) := by
      have := Expr.eval_reg (w := w) 23 st; rwa [hr23] at this
    have hend_x : x.endAddr b < 2 ^ w := hsame.endAddr b ▸ hend_ltw
    have hx_h : x.h = x0.h := hsame.2.2.2.2.2.1
    have hx_vL : x.vList = x0.vList := hsame.2.2.2.2.2.2.2.2.2.2.2.1
    have hx_tL : x.tOrigList = x0.tOrigList := hsame.2.2.2.2.2.2.2.2.2.2.1
    have hx_vC : x.vCap = x0.vCap := hsame.1
    have hx_eC : x.eCap = x0.eCap := hsame.2.1
    have hx_n0 : x.n0 = x0.n0 := hsame.2.2.1
    have hx_tM : x.tM = x0.tM := hsame.2.2.2.2.1
    have hx_Lw : x.L_w = x0.L_w := hsame.2.2.2.2.2.2.2.2.1
    have hx_thp : x.thParent = x0.thParent := hsame.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hstk_x : StackMemAt st.mem (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) (zIdx :: rest) := by
      rw [hx_vC, hx_eC, hx_n0, hx_tM, hx_Lw]; exact hstk
    have hThInv_x : ThStackInv S x.vList x.thParent x.n0 (zIdx :: rest) := by
      rw [hx_vL, hx_thp, hx_n0]; exact hThInv
    have hbuf_x : CutLogBufOk w b (x.endAddr b) rootsBuf fDelBuf cntPtr cap := by
      rw [hsame.endAddr b]; exact hbuf
    obtain ⟨st1, c1, x1, cutE, hrun1, hsame1, hrep1, hcnt1, hrm1, hfm1, hfr1, hstk1, hregs1, hr23_1,
      hr40_1, hr41_1, hr42_1, hcut_mem, hz_vCap, hz_F, hz_not_R, huniq, hRF1_eq, hc1⟩ :=
      compLogPopStep_runs hw16 hend_x hbuf_x (by simp at hcap; omega) hcnt hr40 hr41 hr42
        (hx_h.symm ▸ hrep)
        (by rw [hx_vL, hx_tL]; exact hMinUp) (by rw [hx_vC, hx_eC, hx_n0]; exact hDgDel)
        hBFS hregs hr23 (by rw [hx_n0]; exact hlen) hstk_x hThInv_x
    set z := x0.vList[zIdx]!
    have hz_eq : x.vList[zIdx]! = z := by rw [hx_vL]
    rw [hz_eq] at hrep1 hrm1 hz_vCap hz_F hz_not_R huniq hRF1_eq
    have hsame01 : SameStaticConcrete x0 x1 := hsame.trans hsame1
    have hstk1' : StackMemAt st1.mem (auxThStackBase (lsfAuxPtr b x0.vCap x0.eCap x0.n0 x0.tM x0.L_w) x0.vCap x0.n0) rest := by
      rwa [hx_vC, hx_eC, hx_n0, hx_tM, hx_Lw] at hstk1
    have hThInv_rest : ThStackInv { S with R₀_base := insert z S.R₀_base }
        x0.vList x0.thParent x0.n0 rest := hThInv.2.2.2.2
    set S1 : LSFState := { S with R₀_base := insert z S.R₀_base }
    obtain ⟨st2, c2, x2, cuts2, hrun2, hsame02, hrep2, hlen2, hcnt2, hlog2, hfr2,
      hvalid2, hfold2, hndE2, hsetE2, hndR2, hsetR2, hc2⟩ :=
      ih (cnt + 1) S1 x1 st1 (by simp at hcap; omega) hcnt1 hr40_1 hr41_1 hr42_1 hsame01
        (hx_h ▸ hrep1) hregs1 hr23_1 (by simp at hlen; omega) hstk1' hThInv_rest
    set S2 := applyThStack S1 x0.vList rest
    have hS1_E : S1.RF.F.E = S.RF.F.E.erase cutE := by rw [← hRF1_eq]; rfl
    have hS1_R : S1.RF.R = insert z S.RF.R := by rw [← hRF1_eq]; rfl
    have hsub_E : S2.RF.F.E ⊆ S1.RF.F.E := by
      have hfold_sub : ∀ (l : List (ℕ × ℕ)) (RF : RootedForest),
          (l.foldl compApplyForestCut RF).F.E ⊆ RF.F.E := by
        intro l; induction l with
        | nil => intro _; exact Finset.Subset.refl _
        | cons p tl ihtl => intro RF; exact Finset.Subset.trans (ihtl _) (Finset.erase_subset _ _)
      rw [← hfold2]; exact hfold_sub cuts2 S1.RF
    have hsub_R : S1.RF.R ⊆ S2.RF.R := by
      have hfold_sub : ∀ (l : List (ℕ × ℕ)) (RF : RootedForest),
          RF.R ⊆ (l.foldl compApplyForestCut RF).R := by
        intro l; induction l with
        | nil => intro _; exact Finset.Subset.refl _
        | cons p tl ihtl => intro RF; exact Finset.Subset.trans (Finset.subset_insert p.2 RF.R) (ihtl (compApplyForestCut RF p))
      rw [← hfold2]; exact hfold_sub cuts2 S1.RF
    have hcut_not_2 : cutE ∉ cuts2.map Prod.fst := by
      intro hm
      have hmem_s : cutE ∈ S1.RF.F.E \ S2.RF.F.E := hsetE2 ▸ List.mem_toFinset.mpr hm
      rw [Finset.mem_sdiff, hS1_E] at hmem_s; exact (Finset.mem_erase.mp hmem_s.1).1 rfl
    have hz_not_2 : z ∉ cuts2.map Prod.snd := by
      intro hm
      have hmem_s : z ∈ S2.RF.R \ S1.RF.R := hsetR2 ▸ List.mem_toFinset.mpr hm
      rw [Finset.mem_sdiff, hS1_R] at hmem_s; exact hmem_s.2 (Finset.mem_insert_self _ _)
    refine ⟨st2, _, x2, (cutE, z) :: cuts2,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨rest.length + 1, st1, c1, c2, hcond, Nat.succ_ne_zero _, hrun1, hrun2, rfl⟩)),
      hsame02, hrep2, by simp [hlen2], by simp [hcnt2]; omega, ?_, ?_,
      ⟨hcut_mem, hx_vC ▸ hz_vCap, hz_F, hz_not_R, huniq, hRF1_eq.symm ▸ hvalid2⟩,
      by rw [List.foldl_cons, hRF1_eq, hfold2]; rfl,
      List.nodup_cons.mpr ⟨hcut_not_2, hndE2⟩, ?_,
      List.nodup_cons.mpr ⟨hz_not_2, hndR2⟩, ?_, ?_⟩
    · intro i hi
      have hcnt_bd : cnt + 1 + cuts2.length ≤ cap := by simp only [List.length_cons] at hcap; omega
      cases i with
      | zero =>
        have h1 := hfr2 (rootsBuf + cnt) (by rcases hbuf with ⟨_, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, _, h, _⟩; omega) (Or.inl (by omega))
          (by rcases hbuf with ⟨_, _, _, h, _⟩; omega)
        have h2 := hfr2 (fDelBuf + cnt) (by rcases hbuf with ⟨_, _, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, _, _, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, h, _⟩; omega) (Or.inl (by omega))
        simpa [Nat.add_zero] using ⟨h1.trans hrm1, h2.trans hfm1⟩
      | succ j =>
        have hj : j < cuts2.length := by simp at hi; omega
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using hlog2 j hj
    · intro a ha hnc hnr hnf
      simp only [List.length_cons] at hnr hnf
      exact (hfr2 a ha hnc (by omega) (by omega)).trans (hfr1 a (by rw [hsame.endAddr b]; exact ha) hnc (by omega) (by omega))
    · ext e; simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, hsetE2,
        Finset.mem_sdiff, hS1_E, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨⟨_, heS⟩, he2⟩)
        · exact ⟨hcut_mem, fun hc => (Finset.mem_erase.mp (hS1_E ▸ hsub_E hc)).1 rfl⟩
        · exact ⟨heS, he2⟩
      · rintro ⟨heS, he2⟩
        by_cases hec : e = cutE
        · exact Or.inl hec
        · exact Or.inr ⟨⟨hec, heS⟩, he2⟩
    · ext v; simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, hsetR2,
        Finset.mem_sdiff, hS1_R, Finset.mem_insert]
      constructor
      · rintro (rfl | ⟨hv2, hv1⟩)
        · exact ⟨hsub_R (hS1_R ▸ Finset.mem_insert_self _ _), hz_not_R⟩
        · exact ⟨hv2, fun hvS => hv1 (Or.inr hvS)⟩
      · rintro ⟨hv2, hvS⟩
        by_cases hvz : v = z
        · exact Or.inl hvz
        · exact Or.inr ⟨hv2, fun h => h.elim hvz hvS⟩
    · simp only [List.length_cons, Expr.size]; omega

/-! ## 3. Top-level `compLogAddOrigRootProc` verification -/

open Classical in
/-- Full amortized verification of `compLogAddOrigRootProc`: inserts `u ∈ S.T₀.V` into `S.R₀_base`,
maintains `LSFRep h`, appends the exact ordered cut sequence `cuts` to `(rootsBuf, fDelBuf)` and
increments `cntPtr`, proves `CompForestCutsValid` and exact `RF` transition, and leaves `120`
steps of free amortized credit per cut (`c + 120 * cuts.length + lsfPhi' ≤ 280 + lsfPhi`). -/
theorem compLogAddOrigRoot_runs {w h b u rootsBuf fDelBuf cntPtr cap cnt idxMinUp idxDgDel idxBFS : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete}
    {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hbuf : CutLogBufOk w b (x.endAddr b) rootsBuf fDelBuf cntPtr cap)
    (hcnt_m : mem cntPtr = cnt)
    (hrep : (LSFRep h).rep b S x mem)
    (huT : u ∈ S.T₀.V)
    (hcap : cnt + (({ S with R₀_base := insert u S.R₀_base } : LSFState).R_orig \ S.R_orig).card ≤ cap)
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDel : ∀ F, MeetsContract w p idxDgDel (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F)) :
    let S' : LSFState := { S with R₀_base := insert u S.R₀_base }
    ∃ st' c x' cuts,
      Runs w p ω (compLogAddOrigRootProc idxMinUp idxDgDel idxBFS)
        (startState [b, u, rootsBuf, fDelBuf, cntPtr] mem pos) (.returned 0) st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep b S' x' st'.mem ∧
      st'.mem cntPtr = cnt + cuts.length ∧
      (∀ i (hi : i < cuts.length),
        st'.mem (rootsBuf + (cnt + i)) = cuts[i].2 ∧ st'.mem (fDelBuf + (cnt + i)) = cuts[i].1) ∧
      (∀ a, (a < b ∨ x.endAddr b ≤ a) → a ≠ cntPtr →
        (a < rootsBuf + cnt ∨ rootsBuf + cnt + cuts.length ≤ a) →
        (a < fDelBuf + cnt ∨ fDelBuf + cnt + cuts.length ≤ a) →
        st'.mem a = mem a) ∧
      CompForestCutsValid x.vCap S.RF cuts ∧
      cuts.foldl compApplyForestCut S.RF = S'.RF ∧
      (cuts.map Prod.fst).Nodup ∧
      (cuts.map Prod.fst).toFinset = S.RF.F.E \ S'.RF.F.E ∧
      (cuts.map Prod.snd).Nodup ∧
      (cuts.map Prod.snd).toFinset = S'.RF.R \ S.RF.R ∧
      c + 120 * cuts.length + lsfPhi b x' st'.mem ≤ 280 + lsfPhi b x mem := by
  intro S'
  have hxH : x.h = h := hrep.1
  subst hxH
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set isRootBase := fIsRootBase fAncPtr
  have hlay := addRoot_layout hend_ltw
  have hrep_copy := hrep
  rcases hrep with ⟨_, _, _, _, _, _, hInv, hn0, _, _, _, _, _, _, hvT_lt, _,
    _, _, _, _, hFAnc, _, _, hAux⟩
  rcases hFAnc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hIsR_mem, _⟩
  rcases hAux with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvLen, _, hvMem, _⟩
  have hu_vCap : u < vCap := hvT_lt u huT
  have hisr_u_ltw : isRootBase + u < 2 ^ w := by
    dsimp [isRootBase, fAncPtr, vCap, eCap, n0, tM, fIsRootBase, fAncSize] at hlay ⊢; omega
  have hu_in_R_iff : u ∈ S.RF.R ↔ u ∈ S.R_orig := by
    simp only [LSFState.RF, LSFState.R, Finset.mem_union]
    exact ⟨fun h => h.resolve_right (Finset.disjoint_left.mp hInv.hdisj_iso huT), Or.inl⟩
  have hInv' : LSFStructInv S' := (hInv.addOrigRoot_inv huT).1
  have hTH := hldAuxTree_isRootedTree hInv.hT₀
  let stIn := startState [b, u, rootsBuf, fDelBuf, cntPtr] mem pos
  let stS1 : State := { stIn with regs := Function.update stIn.regs 40 rootsBuf }
  let stS2 : State := { stS1 with regs := Function.update stS1.regs 41 fDelBuf }
  let stS3 : State := { stS2 with regs := Function.update stS2.regs 42 cntPtr }
  have hs1 : Runs w p ω (.assign 40 (.reg 2)) stIn .normal stS1 2 :=
    runs_assign_iff.mpr ⟨rootsBuf, by simp [stIn, Expr.eval, startState], rfl, rfl, by simp [Expr.size]⟩
  have hs2 : Runs w p ω (.assign 41 (.reg 3)) stS1 .normal stS2 2 :=
    runs_assign_iff.mpr ⟨fDelBuf, by simp [stS1, stIn, Expr.eval, startState], rfl, rfl, by simp [Expr.size]⟩
  have hs3 : Runs w p ω (.assign 42 (.reg 4)) stS2 .normal stS3 2 :=
    runs_assign_iff.mpr ⟨cntPtr, by simp [stS2, stS1, stIn, Expr.eval, startState], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨o0, st0, c0, hrun0, hq0, hc0⟩ :=
    addOrigRootHdr_triple (w := w) (b := b) (u := u) (p := p) hw16 hend_ltw hrep_copy
      stS3 ω ⟨rfl, by simp [stS3, stS2, stS1, stIn, startState], by simp [stS3, stS2, stS1, stIn, startState]⟩
  cases o0 with
  | returned _ => exact False.elim hq0
  | normal =>
    have hr0_40 : st0.regs 40 = rootsBuf :=
      (runs_reg_of_notWrites hrun0 (by dsimp [addOrigRootHdrStmt, stmtNotWritesReg]; decide)).trans
        (by simp [stS3, stS2, stS1])
    have hr0_41 : st0.regs 41 = fDelBuf :=
      (runs_reg_of_notWrites hrun0 (by dsimp [addOrigRootHdrStmt, stmtNotWritesReg]; decide)).trans
        (by simp [stS3, stS2])
    have hr0_42 : st0.regs 42 = cntPtr :=
      (runs_reg_of_notWrites hrun0 (by dsimp [addOrigRootHdrStmt, stmtNotWritesReg]; decide)).trans
        (by simp [stS3])
    rcases hq0 with ⟨hmem0, hr0_0, hr0_1, hr0_2, hr0_3, hr0_4, hr0_5, hr0_6, hr0_7, hr0_8, hr0_9, hr0_10⟩
    by_cases hu_R : u ∈ S.R_orig
    · have hcond_eval : (Expr.load (.bin .add (.reg 10) (.reg 1))).eval w st0 = some 1 :=
        Expr.eval_load_of_eq (by eval_expr) (by rw [hmem0, hIsR_mem u hu_vCap, ite_eq_left (hu_in_R_iff.mpr hu_R)])
      have hret_run : Runs w p ω (.ret (.const 0)) st0 (.returned 0) st0 ((Expr.const 0).size + 1) :=
        runs_ret_iff.mpr ⟨0, Expr.eval_const (k := 0) (by omega), rfl, rfl, rfl⟩
      have hcond_run : Runs w p ω
          (.cond (.load (.bin .add (.reg 10) (.reg 1))) (.ret (.const 0))
            (addOrigRootSetupStmt ;; addOrigRootClimbStmt ;;
             .loop (.reg 23) (compLogPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0)))
          st0 (.returned 0) st0 _ :=
        runs_cond_iff.mpr ⟨1, _, hcond_eval, by simpa using hret_run, rfl⟩
      have hfull : Runs w p ω (compLogAddOrigRootProc idxMinUp idxDgDel idxBFS) stIn (.returned 0) st0 _ :=
        runs_seq_iff.mpr (Or.inr ⟨stS1, 2, _, hs1,
          runs_seq_iff.mpr (Or.inr ⟨stS2, 2, _, hs2,
            runs_seq_iff.mpr (Or.inr ⟨stS3, 2, _, hs3,
              runs_seq_iff.mpr (Or.inr ⟨st0, c0, _, hrun0, hcond_run, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have hRorig_eq : S'.R_orig = S.R_orig := by
        ext w; change w ∈ upClosure S.TH S.r₀ (insert u S.R₀_base) ↔ w ∈ S.R_orig
        rw [mem_upClosure_iff]
        constructor
        · rintro ⟨v, hv, hwv⟩; rw [Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact upClosure_isUpwardClosed hTH hInv.hR₀_sub hu_R hwv
          · exact mem_upClosure_iff.mpr ⟨v, hv, hwv⟩
        · intro hw; obtain ⟨v, hv, hwv⟩ := mem_upClosure_iff.mp hw
          exact ⟨v, Finset.mem_insert_of_mem hv, hwv⟩
      have hRF_eq : S.RF = S'.RF := by simp only [LSFState.RF, LSFState.R, S', hRorig_eq]
      have hrep' : (LSFRep x.h).rep b S' x st0.mem :=
        lsfRep_of_R_orig_eq (S₁ := S) (S₂ := S') (hmem0.symm ▸ hrep_copy) hInv'
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hRorig_eq
      refine ⟨st0, _, x, [], hfull, SameStaticConcrete.refl x, hrep', by simpa [hmem0] using hcnt_m,
        fun _ hi => by simp at hi, fun _ _ _ _ _ => by rw [hmem0], trivial, hRF_eq,
        List.nodup_nil, by rw [← hRF_eq]; simp, List.nodup_nil, by rw [← hRF_eq]; simp, ?_⟩
      rw [hmem0]; dsimp [Expr.size] at *; omega
    · have hcond_eval : (Expr.load (.bin .add (.reg 10) (.reg 1))).eval w st0 = some 0 :=
        Expr.eval_load_of_eq (by eval_expr) (by
          rw [hmem0, hIsR_mem u hu_vCap, ite_eq_right (fun h => hu_R (hu_in_R_iff.mp h))])
      obtain ⟨uIdx, huIdx_lt, hu_get⟩ := List.mem_iff_getElem.mp ((hvMem u).mpr huT)
      have hu_bang : x.vList[uIdx]! = u := by rw [getElem!_pos x.vList uIdx huIdx_lt]; exact hu_get
      obtain ⟨o1, st1, c1, hrun1, hq1, hc1⟩ :=
        addOrigRootSetup_triple (w := w) (b := b) (u := u) (p := p) (regs_in := st0.regs)
          hw16 hend_ltw hrep_copy (by omega) hu_bang st0 ω
          ⟨hmem0, rfl, hr0_1, hr0_2, hr0_3, hr0_4, hr0_7, hr0_8, hr0_9⟩
      cases o1 with
      | returned _ => exact False.elim hq1
      | normal =>
        have hr1_40 : st1.regs 40 = rootsBuf :=
          (runs_reg_of_notWrites hrun1 (by dsimp [addOrigRootSetupStmt, stmtNotWritesReg]; decide)).trans hr0_40
        have hr1_41 : st1.regs 41 = fDelBuf :=
          (runs_reg_of_notWrites hrun1 (by dsimp [addOrigRootSetupStmt, stmtNotWritesReg]; decide)).trans hr0_41
        have hr1_42 : st1.regs 42 = cntPtr :=
          (runs_reg_of_notWrites hrun1 (by dsimp [addOrigRootSetupStmt, stmtNotWritesReg]; decide)).trans hr0_42
        rcases hq1 with ⟨hmem1, hr1_11, hr1_12, hr1_13, hr1_14, hr1_15, hr1_16, hr1_17, hr1_18,
          hr1_19, hr1_20, hr1_21, hr1_36, hr1_37, hr1_22, hr1_23, hr1_lo⟩
        have hdu_le : (S.TH.forestPath (x.vList[uIdx]!) S.r₀).length ≤ hldDepthBound n0 := by
          rw [hu_bang]; have hh := hldAuxTree_height hInv.hT₀ huT
          dsimp [depth] at hh; rw [hInv.hTV] at hh
          have hcard : S.G₀.V.card = n0 := hn0; rwa [hcard] at hh
        obtain ⟨st2, c2, stk, hrun2, hfr2, hstk2, _, _, hlen_bd, hThInv, hanc_sub, hanc_cov,
          hr2_23, hreg2, hc2⟩ :=
          addOrigRootClimb_runs hw16 hend_ltw hrep_copy
            (S.TH.forestPath (x.vList[uIdx]!) S.r₀).length uIdx [] st1
            (by omega) rfl (by simp only [List.length_nil, Nat.zero_add]; exact hdu_le)
            (fun a _ => hmem1 ▸ rfl) (fun _ hi => by simp at hi) List.nodup_nil
            (fun _ hi => by simp at hi) (fun _ hi => by simp at hi) (fun _ _ h => by cases h)
            ((hr1_lo 10 (by decide)).trans hr0_10) hr1_12 hr1_13 hr1_14 hr1_22 hr1_23
        obtain ⟨hrep2, hphi2⟩ := lsfRep_of_thStack_write hrep_copy hfr2
        have hPopRegs2 : PopRegsOk b x st2.regs :=
          ⟨(hreg2 0 (by decide) (by decide)).trans ((hr1_lo 0 (by decide)).trans hr0_0),
            (hreg2 2 (by decide) (by decide)).trans ((hr1_lo 2 (by decide)).trans hr0_2),
            (hreg2 4 (by decide) (by decide)).trans ((hr1_lo 4 (by decide)).trans hr0_4),
            (hreg2 5 (by decide) (by decide)).trans ((hr1_lo 5 (by decide)).trans hr0_5),
            (hreg2 6 (by decide) (by decide)).trans ((hr1_lo 6 (by decide)).trans hr0_6),
            (hreg2 7 (by decide) (by decide)).trans ((hr1_lo 7 (by decide)).trans hr0_7),
            (hreg2 8 (by decide) (by decide)).trans ((hr1_lo 8 (by decide)).trans hr0_8),
            (hreg2 9 (by decide) (by decide)).trans ((hr1_lo 9 (by decide)).trans hr0_9),
            (hreg2 10 (by decide) (by decide)).trans ((hr1_lo 10 (by decide)).trans hr0_10),
            (hreg2 11 (by decide) (by decide)).trans hr1_11,
            (hreg2 12 (by decide) (by decide)).trans hr1_12,
            (hreg2 14 (by decide) (by decide)).trans hr1_14,
            (hreg2 15 (by decide) (by decide)).trans hr1_15,
            (hreg2 16 (by decide) (by decide)).trans hr1_16,
            (hreg2 17 (by decide) (by decide)).trans hr1_17,
            (hreg2 18 (by decide) (by decide)).trans hr1_18,
            (hreg2 19 (by decide) (by decide)).trans hr1_19,
            (hreg2 20 (by decide) (by decide)).trans hr1_20,
            (hreg2 21 (by decide) (by decide)).trans hr1_21,
            (hreg2 36 (by decide) (by decide)).trans hr1_36,
            (hreg2 37 (by decide) (by decide)).trans hr1_37⟩
        have hr2_40 : st2.regs 40 = rootsBuf := (hreg2 40 (by decide) (by decide)).trans hr1_40
        have hr2_41 : st2.regs 41 = fDelBuf := (hreg2 41 (by decide) (by decide)).trans hr1_41
        have hr2_42 : st2.regs 42 = cntPtr := (hreg2 42 (by decide) (by decide)).trans hr1_42
        have hfr2_out : ∀ a_addr, a_addr < b ∨ x.endAddr b ≤ a_addr → st2.mem a_addr = mem a_addr := fun a_addr ha =>
          hfr2 a_addr (fun hc => by
            dsimp [auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
              auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
              auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase] at hlay hc; omega)
        have hcnt_m2 : st2.mem cntPtr = cnt := (hfr2_out cntPtr hbuf.1).trans hcnt_m
        have hflds := applyThStack_fields S x.vList stk
        have hRorig_eq : S'.R_orig = (applyThStack S x.vList stk).R_orig := by
          ext w
          have hTH_eq : (applyThStack S x.vList stk).TH = S.TH := by
            simp only [LSFState.TH, hflds.2.2.1, hflds.2.2.2.1]
          change w ∈ upClosure S.TH S.r₀ (insert u S.R₀_base) ↔
            w ∈ upClosure (applyThStack S x.vList stk).TH (applyThStack S x.vList stk).r₀
              (applyThStack S x.vList stk).R₀_base
          rw [hTH_eq, hflds.2.2.2.1, hflds.2.2.2.2.2.2.2.2.2.2.2.2.2, mem_upClosure_iff, mem_upClosure_iff]
          constructor
          · rintro ⟨v, hv, hwv⟩; rw [Finset.mem_insert] at hv
            rcases hv with rfl | hv
            · rw [← hu_bang] at hwv
              rcases hanc_cov w hwv with hwR | ⟨idx, hidx, rfl⟩
              · obtain ⟨v0, hv0, hwv0⟩ := mem_upClosure_iff.mp hwR
                exact ⟨v0, Finset.mem_union_left _ hv0, hwv0⟩
              · exact ⟨x.vList[idx]!, Finset.mem_union_right _
                  (List.mem_toFinset.mpr (List.mem_map.mpr ⟨idx, hidx, rfl⟩)), isAncestor_refl _ _ _⟩
            · exact ⟨v, Finset.mem_union_left _ hv, hwv⟩
          · rintro ⟨v, hv, hwv⟩; rw [Finset.mem_union] at hv
            rcases hv with hv | hv
            · exact ⟨v, Finset.mem_insert_of_mem hv, hwv⟩
            · obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
              have hv_anc : IsAncestor S.TH S.r₀ (x.vList[idx]!) u := by
                rcases hanc_sub _ ⟨idx, hidx, rfl⟩ with h1 | ⟨_, h2, _⟩
                · rwa [hu_bang] at h1
                · simp at h2
              exact ⟨u, Finset.mem_insert_self _ _, isAncestor_trans hTH huT hwv hv_anc⟩
        have hRF_eq : (applyThStack S x.vList stk).RF = S'.RF := by
          simp only [LSFState.RF, LSFState.R, hflds.2.2.1, hflds.2.2.2.1, hflds.2.2.2.2.1,
            hflds.2.2.2.2.2.2.1, hflds.2.2.2.2.2.2.2.2.1, ← hRorig_eq]; rfl
        have hstk_len_le : stk.length ≤ (S'.R_orig \ S.R_orig).card := by
          have hcard_le : ∀ (l : List ℕ) (T : LSFState),
              ThStackInv T x.vList x.thParent x.n0 l →
              l.length ≤ ((applyThStack T x.vList l).R_orig \ T.R_orig).card := by
            intro l; induction l with
            | nil => intro _ _; simp
            | cons a tl ihtl =>
              intro T hTI
              set T1 : LSFState := { T with R₀_base := insert (x.vList[a]!) T.R₀_base }
              have ha_not : x.vList[a]! ∉ T.R_orig := hTI.2.1
              have hT1_sub : T1.R_orig ⊆ (applyThStack T1 x.vList tl).R_orig := by
                have hf := applyThStack_fields T1 x.vList tl
                intro v hv; change v ∈ upClosure _ _ _
                rw [show (applyThStack T1 x.vList tl).TH = T1.TH by simp [LSFState.TH, hf.2.2.1, hf.2.2.2.1],
                  hf.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.2.2.2]
                obtain ⟨v0, hv0, hvv0⟩ := mem_upClosure_iff.mp hv
                exact mem_upClosure_iff.mpr ⟨v0, Finset.mem_union_left _ hv0, hvv0⟩
              have ha_in_T1 : x.vList[a]! ∈ T1.R_orig :=
                mem_upClosure_iff.mpr ⟨x.vList[a]!, Finset.mem_insert_self _ _, isAncestor_refl _ _ _⟩
              have hss : (applyThStack T1 x.vList tl).R_orig \ T1.R_orig ⊂
                  (applyThStack T x.vList (a :: tl)).R_orig \ T.R_orig := by
                rw [Finset.ssubset_iff_of_subset]
                · refine ⟨x.vList[a]!, Finset.mem_sdiff.mpr ⟨hT1_sub ha_in_T1, ha_not⟩,
                    fun hc => (Finset.mem_sdiff.mp hc).2 ha_in_T1⟩
                · intro v hv; rw [Finset.mem_sdiff] at hv ⊢
                  exact ⟨hv.1, fun hT => hv.2 (by
                    obtain ⟨v0, hv0, hvv0⟩ := mem_upClosure_iff.mp hT
                    exact mem_upClosure_iff.mpr ⟨v0, Finset.mem_insert_of_mem hv0, hvv0⟩)⟩
              have hlt := Finset.card_lt_card hss
              have hrec := ihtl T1 hTI.2.2.2.2
              simp only [List.length_cons]; omega
          rw [hRorig_eq]; exact hcard_le stk S hThInv
        obtain ⟨st3, c3, x', cuts, hrun3, hsame', hrep3, hlen3, hcnt3, hlog3, hfr3,
          hvalid3, hfold3, hndE3, hsetE3, hndR3, hsetR3, hc3⟩ :=
          compLogPopLoop_runs hw16 hend_ltw hbuf hMinUp hDgDel hBFS stk cnt S x st2
            (Nat.le_trans (Nat.add_le_add_left hstk_len_le cnt) hcap) hcnt_m2 hr2_40 hr2_41 hr2_42
            (SameStaticConcrete.refl x) hrep2 hPopRegs2 hr2_23 hlen_bd hstk2 hThInv
        have hret_run : Runs w p ω (.ret (.const 0)) st3 (.returned 0) st3 ((Expr.const 0).size + 1) :=
          runs_ret_iff.mpr ⟨0, Expr.eval_const (k := 0) (by omega), rfl, rfl, rfl⟩
        have hseq3 : Runs w p ω
            (.loop (.reg 23) (compLogPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0))
            st2 (.returned 0) st3 (c3 + ((Expr.const 0).size + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hrun3, hret_run, rfl⟩)
        have hseq2 : Runs w p ω
            (addOrigRootClimbStmt ;;
             .loop (.reg 23) (compLogPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0))
            st1 (.returned 0) st3 (c2 + (c3 + ((Expr.const 0).size + 1) + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2, hseq3, rfl⟩)
        have hseq1 : Runs w p ω
            (addOrigRootSetupStmt ;; addOrigRootClimbStmt ;;
             .loop (.reg 23) (compLogPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0))
            st0 (.returned 0) st3 (c1 + (c2 + (c3 + ((Expr.const 0).size + 1) + 1) + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1, hseq2, rfl⟩)
        have hcond_run : Runs w p ω
            (.cond (.load (.bin .add (.reg 10) (.reg 1))) (.ret (.const 0))
              (addOrigRootSetupStmt ;; addOrigRootClimbStmt ;;
               .loop (.reg 23) (compLogPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0)))
            st0 (.returned 0) st3 _ :=
          runs_cond_iff.mpr ⟨0, _, hcond_eval, by simpa using hseq1, rfl⟩
        have hfull : Runs w p ω (compLogAddOrigRootProc idxMinUp idxDgDel idxBFS)
            stIn (.returned 0) st3 _ :=
          runs_seq_iff.mpr (Or.inr ⟨stS1, 2, _, hs1,
            runs_seq_iff.mpr (Or.inr ⟨stS2, 2, _, hs2,
              runs_seq_iff.mpr (Or.inr ⟨stS3, 2, _, hs3,
                runs_seq_iff.mpr (Or.inr ⟨st0, c0, _, hrun0, hcond_run, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        have hrep_final : (LSFRep x.h).rep b S' x' st3.mem :=
          lsfRep_of_R_orig_eq hrep3 hInv'
            hflds.1.symm hflds.2.1.symm hflds.2.2.1.symm hflds.2.2.2.1.symm hflds.2.2.2.2.1.symm
            hflds.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.2.1.symm
            hflds.2.2.2.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.2.2.2.1.symm
            hflds.2.2.2.2.2.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.2.2.2.2.2.1.symm
            hflds.2.2.2.2.2.2.2.2.2.2.2.2.1.symm hRorig_eq
        refine ⟨st3, _, x', cuts, hfull, hsame', hrep_final, hcnt3, hlog3,
          fun a ha hnc hnr hnf => (hfr3 a ha hnc hnr hnf).trans (hfr2_out a ha),
          hvalid3, hfold3.trans hRF_eq, hndE3, hRF_eq ▸ hsetE3, hndR3, hRF_eq ▸ hsetR3, ?_⟩
        dsimp only [Expr.size] at hc0 hc1 hc2 hc3 ⊢
        simp only [List.length_nil, Nat.sub_zero] at hc2
        rw [hphi2] at hc3; rw [hlen3]; omega

/-- Combine two sequential valid cut logs into a single valid cut log with disjoint edges/roots. -/
lemma compPreLog_two_cuts_combine {vCap : ℕ} {RF0 RF1 RF2 : RootedForest}
    {c1 c2 : List (ℕ × ℕ)}
    (hv1 : CompForestCutsValid vCap RF0 c1) (hf1 : c1.foldl compApplyForestCut RF0 = RF1)
    (hndE1 : (c1.map Prod.fst).Nodup) (hsE1 : (c1.map Prod.fst).toFinset = RF0.F.E \ RF1.F.E)
    (hndR1 : (c1.map Prod.snd).Nodup) (hsR1 : (c1.map Prod.snd).toFinset = RF1.R \ RF0.R)
    (hv2 : CompForestCutsValid vCap RF1 c2) (hf2 : c2.foldl compApplyForestCut RF1 = RF2)
    (hndE2 : (c2.map Prod.fst).Nodup) (hsE2 : (c2.map Prod.fst).toFinset = RF1.F.E \ RF2.F.E)
    (hndR2 : (c2.map Prod.snd).Nodup) (hsR2 : (c2.map Prod.snd).toFinset = RF2.R \ RF1.R) :
    CompForestCutsValid vCap RF0 (c1 ++ c2) ∧
    (c1 ++ c2).foldl compApplyForestCut RF0 = RF2 ∧
    ((c1 ++ c2).map Prod.fst).Nodup ∧
    ((c1 ++ c2).map Prod.fst).toFinset = RF0.F.E \ RF2.F.E ∧
    ((c1 ++ c2).map Prod.snd).Nodup ∧
    ((c1 ++ c2).map Prod.snd).toFinset = RF2.R \ RF0.R := by
  have hsubE : ∀ (l : List (ℕ × ℕ)) (RF : RootedForest), (l.foldl compApplyForestCut RF).F.E ⊆ RF.F.E := by
    intro l; induction l with
    | nil => intro _; exact Finset.Subset.refl _
    | cons p tl ih => intro RF; exact Finset.Subset.trans (ih _) (Finset.erase_subset _ _)
  have hsubR : ∀ (l : List (ℕ × ℕ)) (RF : RootedForest), RF.R ⊆ (l.foldl compApplyForestCut RF).R := by
    intro l; induction l with
    | nil => intro _; exact Finset.Subset.refl _
    | cons p tl ih => intro RF; exact Finset.Subset.trans (Finset.subset_insert p.2 RF.R) (ih (compApplyForestCut RF p))
  have hE10 : RF1.F.E ⊆ RF0.F.E := hf1 ▸ hsubE c1 RF0
  have hE21 : RF2.F.E ⊆ RF1.F.E := hf2 ▸ hsubE c2 RF1
  have hR01 : RF0.R ⊆ RF1.R := hf1 ▸ hsubR c1 RF0
  have hR12 : RF1.R ⊆ RF2.R := hf2 ▸ hsubR c2 RF1
  refine ⟨compForestCutsValid_append hv1 (hf1.symm ▸ hv2), by rw [List.foldl_append, hf1, hf2], ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndE1, hndE2, fun e1 he1 e2 he2 heq => ?_⟩
    subst heq
    exact (Finset.mem_sdiff.mp (hsE1 ▸ List.mem_toFinset.mpr he1)).2
      (Finset.mem_sdiff.mp (hsE2 ▸ List.mem_toFinset.mpr he2)).1
  · rw [List.map_append, List.toFinset_append, hsE1, hsE2]
    ext e; simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun ⟨h0, h1⟩ => ⟨h0, fun hc => h1 (hE21 hc)⟩) (fun ⟨h1, h2⟩ => ⟨hE10 h1, h2⟩),
      fun ⟨h0, h2⟩ => by by_cases h1 : e ∈ RF1.F.E; exact Or.inr ⟨h1, h2⟩; exact Or.inl ⟨h0, h1⟩⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndR1, hndR2, fun r1 hr1 r2 hr2 heq => ?_⟩
    subst heq
    exact (Finset.mem_sdiff.mp (hsR2 ▸ List.mem_toFinset.mpr hr2)).2
      (Finset.mem_sdiff.mp (hsR1 ▸ List.mem_toFinset.mpr hr1)).1
  · rw [List.map_append, List.toFinset_append, hsR1, hsR2]
    ext r; simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun ⟨h1, h0⟩ => ⟨hR12 h1, h0⟩) (fun ⟨h2, h1⟩ => ⟨h2, fun hc => h1 (hR01 hc)⟩),
      fun ⟨h2, h0⟩ => by by_cases h1 : r ∈ RF1.R; exact Or.inl ⟨h1, h0⟩; exact Or.inr ⟨h2, h1⟩⟩

end

end MinCostFlow.SparseCore.Program
