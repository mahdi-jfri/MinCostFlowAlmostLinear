module

public import MinCostFlow.ExpanderDecomp.CoreProgPeelLoop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of the Recursive `Core` Procedure (`CoreProgOn`)

Proves `coreOnProc_meetsContract` via `WordRAM.meetsContract_of_rec` on the recursion level `q`,
combining:
* base cases `q = 0` or `k < 2` (returning `X` as a trivial expander via `copyWords`),
* size delegation `k ≤ N ^ (q - 1)` (recursive call to `idx.coreOn` at `q - 1`), and
* peeling `N ^ (q - 1) < k` (`corePeelLoop_triple` over `oneShotProc_meetsContract`, followed by
  returning the expander or copying the accumulated balanced sparse cut `U` to `outAddr`).
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Helper for the two base-case branches (`q = 0` and `k < 2`) of `coreOnProc`:
writes `CoreOutAt mem' outAddr (.expander X)` using `idx.copyWords` and returns `h`. -/
private lemma coreBaseExpander_runs {w : ℕ} {p : Program} {idx : CoreIdx}
    (hCopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    {st : State} {ω : ℕ → Bool} {k xAddr locAddr outAddr h n : ℕ} {X : Finset ℕ}
    {Pcost : ℕ → Prop} {Q : Outcome → State → Prop}
    (hX : VertsAt st.mem xAddr k X) (hXrange : X ⊆ Finset.range n)
    (hx_h : xAddr + k ≤ h) (hloc_h : locAddr + n ≤ h) (hout_h : outAddr + 2 + k ≤ h)
    (hd_lo : DisjointRange locAddr n outAddr (2 + k))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hloc : ∀ u < n, st.mem (locAddr + u) = 0)
    (hZero : ZeroFrom st.mem h) (hw : h + 16 < 2 ^ w)
    (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = xAddr)
    (hr6 : st.regs 6 = outAddr) (hr7 : st.regs 7 = h)
    (hQ : ∀ st',
      CoreOutAt st'.mem outAddr (.expander X) →
      ZeroFrom st'.mem h →
      (∀ u < n, st'.mem (locAddr + u) = 0) →
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = st.mem a) →
      Q (.returned h) st')
    (hB : ∀ c, c ≤ copyWordsCost k + 30 → Pcost c) :
    ∃ o st' c,
      Runs w p ω
        (seqStmts
          [ .store (.reg 6) (.const 1)
          , .store (.bin .add (.reg 6) (.const 1)) (.reg 2)
          , .call 17 idx.copyWords [.reg 2, .reg 3, .bin .add (.reg 6) (.const 2)]
          , .ret (.reg 7) ])
        st o st' c ∧ Q o st' ∧ Pcost c := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  suffices hrun : ∃ o st' c,
      Runs w p ω
        (seqStmts
          [ .store (.reg 6) (.const 1)
          , .store (.bin .add (.reg 6) (.const 1)) (.reg 2)
          , .call 17 idx.copyWords [.reg 2, .reg 3, .bin .add (.reg 6) (.const 2)]
          , .ret (.reg 7) ])
        st o st' c ∧ Q o st' ∧ 0 + c ≤ copyWordsCost k + 30 by
    obtain ⟨o, st', c, hr, hq, hc⟩ := hrun
    exact ⟨o, st', c, hr, hq, hB c (by omega)⟩
  dsimp only [seqStmts]
  refine runs_seq_store_le (x := outAddr) (v := 1)
    (Expr.eval_reg_of_eq hr6) (Expr.eval_const hw1) ?_
  refine runs_seq_store_le (x := outAddr + 1) (v := k)
    (Expr.eval_add (Expr.eval_reg_of_eq hr6) (Expr.eval_const hw1) (by omega))
    (Expr.eval_reg_of_eq hr2) ?_
  set mem1 := Function.update (Function.update st.mem outAddr 1) (outAddr + 1) k
  have hmem1_x : ∀ i < k, mem1 (xAddr + i) = st.mem (xAddr + i) := fun i hi => by
    have hdisj : outAddr + 2 + k ≤ xAddr ∨ xAddr + k ≤ outAddr := by
      rcases hd_ox with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr h2]
    have hne1 : xAddr + i ≠ outAddr + 1 := by omega
    have hne0 : xAddr + i ≠ outAddr := by omega
    simp [mem1, Function.update_of_ne hne1, Function.update_of_ne hne0]
  have hCp_pre : (copyWordsContract w).pre [k, xAddr, outAddr + 2] mem1 := by
    refine ⟨k, xAddr, outAddr + 2, rfl, by omega, by omega, by omega, by omega,
      by rcases hd_ox with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
      fun i hi => ?_⟩
    rw [hmem1_x i hi]
    have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort, ← hX.1]
    have hi' : i < (X.sort (· ≤ ·)).length := by omega
    rw [hX.2 i hi']
    have hmem : (X.sort (· ≤ ·))[i] ∈ X := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi')
    have hlt : (X.sort (· ≤ ·))[i] < n := Finset.mem_range.mp (hXrange hmem)
    omega
  refine runs_seq_call_le (vs := [k, xAddr, outAddr + 2]) hCopy
    (by simp [evalArgs, Expr.eval, hr2, hr3, hr6, hw2, show outAddr + 2 < 2 ^ w by omega])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    hCp_pre ?_
  intro _v2 mem2 _pos2 hpostCp
  simp only [copyWordsContract, List.getD_cons_zero, List.getD_cons_succ] at hpostCp
  rcases hpostCp with ⟨_, hcp_eq, hfr2⟩
  refine runs_ret_le (v := h) (by simp [Expr.eval, hr7]) ?_ ?_
  · refine hQ _ ?_ ?_ ?_ ?_
    · refine ⟨?_, X.sort (· ≤ ·), Finset.sort_nodup X (· ≤ ·), by ext v; simp, ?_, ?_⟩
      · dsimp only; rw [hfr2 outAddr (Or.inl (by omega))]; simp [mem1]
      · dsimp only; rw [hfr2 (outAddr + 1) (Or.inl (by omega))]
        simp [mem1, Finset.length_sort, hX.1]
      · intro i hi
        have hkX : k = X.card := hX.1
        have hik : i < k := by rw [Finset.length_sort] at hi; omega
        dsimp only; rw [hcp_eq i hik, hmem1_x i hik]
        exact hX.2 i hi
    · intro a ha
      dsimp only; rw [hfr2 a (Or.inr (by omega))]
      have hne1 : a ≠ outAddr + 1 := by omega
      have hne0 : a ≠ outAddr := by omega
      simp [mem1, Function.update_of_ne hne1, Function.update_of_ne hne0, hZero a ha]
    · intro u hu
      have hout_loc : locAddr + u < outAddr ∨ outAddr + 2 + k ≤ locAddr + u := by
        rcases hd_lo with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
      dsimp only; rw [hfr2 (locAddr + u) (by omega)]
      have hne1 : locAddr + u ≠ outAddr + 1 := by omega
      have hne0 : locAddr + u ≠ outAddr := by omega
      simp [mem1, Function.update_of_ne hne1, Function.update_of_ne hne0, hloc u hu]
    · intro a ha hno
      dsimp only; rw [hfr2 a (by omega)]
      have hne1 : a ≠ outAddr + 1 := by omega
      have hne0 : a ≠ outAddr := by omega
      simp [mem1, Function.update_of_ne hne1, Function.update_of_ne hne0]
  · have hargC : argsSize [.reg 2, .reg 3, .bin .add (.reg 6) (.const 2)] = 5 := by decide
    simp only [copyWordsContract, Expr.size, hargC, List.getD_cons_zero]
    omega

/-- **Core-theorem Word-RAM contract (`coreOnProc`)**:
proves by well-founded recursion on `q` (`meetsContract_of_rec`) that `coreOnProc idx` meets
`coreOnContract` with `K_C = stepCTimeConst C_stepC C_left` and `S_C = stepCSpaceConst C_sp`. -/
theorem coreOnProc_meetsContract {w : ℕ} {p : Program} {idx : CoreIdx}
    {cfg : ParamConfig} {M r K_B C_stepC C_left S_B C_sp : ℕ}
    (hself : p.procs[idx.coreOn]? = some (coreOnProc idx))
    (hOneShotProc : p.procs[idx.oneShot]? = some (oneShotProc idx))
    (hCopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hDiff : MeetsContract w p idx.filterDiff (filterSetContract w false))
    (hCloud : MeetsContract w p idx.cloudExpander (cloudExpanderContract w))
    (hCol : MeetsContract w p idx.edgeColor17 (edgeColor17Contract w))
    (hStepC : MeetsContract w p idx.stepCMacro
      (stepCContract (coreParamsOf cfg M r) cloud C_stepC C_sp w))
    (hLeft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) C_left C_sp w))
    (hStepD : MeetsContract w p idx.stepD (stepDContract w))
    (hStepB_rec : ∀ q, 2 ≤ q → q ≤ r →
      MeetsContract w p idx.coreOn
        ((coreOnContract cfg M r w K_B (stepCTimeConst C_stepC C_left)
            S_B (stepCSpaceConst C_sp)).below (fun args _ => args.getD 0 0) q) →
      MeetsContract w p idx.stepB
        (oneShotStepBContract cfg M r q w K_B S_B
          (coreProgTime K_B (stepCTimeConst C_stepC C_left) cfg M r (q - 1))
          (coreProgSpace S_B (stepCSpaceConst C_sp) cfg M r (q - 1)))) :
    MeetsContract w p idx.coreOn
      (coreOnContract cfg M r w K_B (stepCTimeConst C_stepC C_left)
        S_B (stepCSpaceConst C_sp)) := by
  set K_C := stepCTimeConst C_stepC C_left
  set S_C := stepCSpaceConst C_sp
  refine meetsContract_of_rec (fun args _ => args.getD 0 0) hself ?_
  intro q_meas ih args mem pos ω _ hpre hmeas
  rcases hpre with ⟨q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h, G, X,
    rfl, ha0, ha, hrl, hqr, hP, hG, hGvalid, hGn, hX, hXrange, hGloop, hkNq, hdegG, hmG,
    hloc0, hg_h, hx_h, hp_h, hloc_h, hout_h,
    hd_lg, hd_lx, hd_lp, hd_lo, hd_og, hd_ox, hd_op, hZero, hw⟩
  simp only [List.getD_cons_zero] at hmeas
  subst hmeas
  set cp := coreParamsOf cfg M r
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hsp4000 : 4000 ≤ coreProgSpace S_B S_C cfg M r q :=
    coreProgSpace_base_ge S_B S_C cfg M r q
  have htm4000 : 4000 ≤ coreProgTime K_B K_C cfg M r q :=
    coreProgTime_base_ge K_B K_C cfg M r q
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hcs : coreParamsSize r = 7 + 3 * r := rfl
  -- Helper to discharge the universally quantified `coreOnContract.post`
  have hpost_wrap : ∀ (v : ℕ) (mem' : ℕ → ℕ),
      (∃ res : CoreResult, CoreOutAt mem' outAddr res ∧ CoreSpec cp q G X res) →
      h ≤ v → v ≤ h + coreProgSpace S_B S_C cfg M r q →
      ZeroFrom mem' v →
      (∀ u < G.n, mem' (locAddr + u) = 0) →
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem' a = mem a) →
      (coreOnContract cfg M r w K_B K_C S_B S_C).post
        [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h] mem v mem' := by
    intro v mem' hres hv1 hv2 hZv hlocv hfrv
      q' gAddr' k' xAddr' pAddr' locAddr' outAddr' h' G' X' hargs'
      _ _ _ _ _ hG' _ _ hX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    simp only [List.cons.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs'
    have hG_eq : G = G' := by
      rw [← readGraph_eq_of_graphAt hG, readGraph_eq_of_graphAt hG']
    rcases hG_eq with rfl
    have hX_eq : X = X' := by
      have h1' := readList_eq_of_listAt hX.2
      have h2' := readList_eq_of_listAt hX'.2
      rw [Finset.length_sort, ← hX.1] at h1'
      rw [Finset.length_sort, ← hX'.1] at h2'
      simpa [Finset.sort_toFinset] using congrArg List.toFinset (h1'.symm.trans h2')
    rcases hX_eq with rfl
    exact ⟨hres, hv1, hv2, hZv, hlocv, hfrv⟩
  refine runs_start_le ?_
  dsimp only [coreOnProc]
  -- Branch 1: `q = 0`
  refine runs_cond_le (v := if q = 0 then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) hw1) ?_ ?_
  · -- Case `q = 0`: `k ≤ N ^ 0 = 1`
    intro hne0
    have hq0 : q = 0 := by by_contra hne; simp [hne] at hne0
    have hk1 : k ≤ 1 := by subst hq0; simpa using hkNq
    apply coreBaseExpander_runs hCopy (k := k) (xAddr := xAddr) (locAddr := locAddr)
      (outAddr := outAddr) (h := h) (n := G.n) (X := X)
      hX hXrange hx_h hloc_h hout_h hd_lo hd_ox hloc0 hZero (by omega)
      (by simp [startState]) (by simp [startState]) (by simp [startState]) (by simp [startState])
    · intro st' hOut hZ' hloc' hfr'
      exact hpost_wrap h st'.mem
        ⟨.expander X, hOut, Finset.Subset.refl X, by omega,
          isExpansionExpanderOn_of_card_le_one G (by rw [← hX.1]; exact hk1) _⟩
        le_rfl (by omega) hZ' hloc' hfr'
    · intro c hc
      simp only [coreOnContract, Expr.size, copyWordsCost, List.getD_cons_zero] at hc ⊢
      omega
  · -- Case `1 ≤ q`
    intro hzero0
    have hq1 : 1 ≤ q := by split_ifs at hzero0; omega
    -- Branch 2: `k < 2`
    refine runs_cond_le (v := if k < 2 then 1 else 0)
      (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const hw2) hw1) ?_ ?_
    · -- Case `k < 2` (`k ≤ 1`)
      intro hne2
      have hk1 : k ≤ 1 := by by_contra hge; simp [show ¬ k < 2 by omega] at hne2
      apply coreBaseExpander_runs hCopy (k := k) (xAddr := xAddr) (locAddr := locAddr)
        (outAddr := outAddr) (h := h) (n := G.n) (X := X)
        hX hXrange hx_h hloc_h hout_h hd_lo hd_ox hloc0 hZero (by omega)
        (by simp [startState]) (by simp [startState]) (by simp [startState]) (by simp [startState])
      · intro st' hOut hZ' hloc' hfr'
        exact hpost_wrap h st'.mem
          ⟨.expander X, hOut, Finset.Subset.refl X, by omega,
            isExpansionExpanderOn_of_card_le_one G (by rw [← hX.1]; exact hk1) _⟩
          le_rfl (by omega) hZ' hloc' hfr'
      · intro c hc
        simp only [coreOnContract, Expr.size, copyWordsCost, List.getD_cons_zero] at hc ⊢
        omega
    · -- Case `1 ≤ q` and `2 ≤ k`: read `r` and `N ^ (q - 1)` from `CoreParamsAt`
      intro hzero2
      have hk2 : 2 ≤ k := by by_contra hlt; simp [Nat.lt_of_not_ge hlt] at hzero2
      dsimp only [seqStmts]
      -- `r8 := mem[pAddr + 3] = r`
      refine runs_seq_assign_le (v := r)
        (hP.2.2.2.1 ▸ Expr.eval_load (Expr.eval_add
          (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))) ?_
      -- `r9 := mem[pAddr + 6 + 2 * r + (q - 1)] = cp.N ^ (q - 1)`
      refine runs_seq_assign_le (v := cp.N ^ (q - 1))
        (hP.2.2.2.2.2.2 (q - 1) (by omega) ▸ Expr.eval_load (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const hw2) (Expr.eval_reg_of_eq (by simp)) (by omega))
            (by omega))
          (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [startState]))
            (Expr.eval_const hw1) (by omega))
          (by omega))) ?_
      -- Branch 3: `N ^ (q - 1) < k` (peel) vs `k ≤ N ^ (q - 1)` (delegate to `q - 1`)
      refine runs_cond_le (v := if cp.N ^ (q - 1) < k then 1 else 0)
        (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_reg_of_eq (by simp [startState])) hw1) ?_ ?_
      · -- Case `N ^ (q - 1) < k`: run `corePeelLoopStmt` over `oneShotProc`
        intro hneGt
        have hkgt : cp.N ^ (q - 1) < k := by by_contra hle; simp [hle] at hneGt
        have h2D_le : 2 * DCore cfg M q + 1 ≤ coreProgSpace S_B S_C cfg M r q :=
          two_mul_DCore_lt_coreProgSpace S_B S_C cfg M r q hq1
        have hsp_rec : 2 * k + 2 * DCore cfg M q *
            oneShotProgSpace S_B S_C cfg M r q (coreProgSpace S_B S_C cfg M r (q - 1)) ≤
            coreProgSpace S_B S_C cfg M r q :=
          coreProgSpace_rec S_B S_C cfg M r q k hq1 hkNq
        have htm_rec := coreProgTime_rec K_B K_C cfg M r q k hq1 hkNq
        have hOneShot : MeetsContract w p idx.oneShot
            (oneShotContract cfg M r q w K_B K_C S_B S_C
              (coreProgTime K_B K_C cfg M r (q - 1)) (coreProgSpace S_B S_C cfg M r (q - 1))) :=
          oneShotProc_meetsContract hOneShotProc hCopy hCloud hCol
            (fun hq2 => hStepB_rec q hq2 hqr ih) hStepC hLeft hStepD
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := h) (Expr.eval_reg_of_eq (by simp [startState])) ?_
        refine runs_seq_assign_le (v := h + k)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
            (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) ?_
        refine runs_seq_assign_le (v := h + 2 * k)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
            (Expr.eval_mul (Expr.eval_const hw2) (Expr.eval_reg_of_eq (by simp [startState]))
              (by omega)) (by omega)) ?_
        refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
        refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
        refine runs_seq_assign_le (v := 2 * DCore cfg M q)
          (Expr.eval_mul (Expr.eval_const hw2)
            ((show mem (pAddr + 5 + r + q) = DCore cfg M q from hP.2.2.2.2.2.1 q hqr) ▸
              Expr.eval_load (Expr.eval_add
                (Expr.eval_add
                  (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
                    (Expr.eval_const (by omega)) (by omega))
                  (Expr.eval_reg_of_eq (by simp)) (by omega))
                (Expr.eval_reg_of_eq (by simp [startState])) (by omega)))
            (by omega)) ?_
        -- Splice `corePeelLoop_triple`
        have hLoop := corePeelLoop_triple hDiff hCopy hOneShot ha0 ha hrl hq1 hqr
          hP hG hGvalid hGn hX hXrange hGloop hkgt hkNq hdegG hmG
          hg_h hx_h hp_h hloc_h hout_h hd_lg hd_lx hd_lp hd_lo hd_og hd_ox hd_op hw
          (fun st =>
            st.regs 0 = q ∧ st.regs 1 = gAddr ∧ st.regs 2 = k ∧ st.regs 3 = xAddr ∧
            st.regs 4 = pAddr ∧ st.regs 5 = locAddr ∧ st.regs 6 = outAddr ∧ st.regs 7 = h ∧
            st.regs 10 = h ∧ st.regs 11 = h + k ∧ st.regs 12 = h + 2 * k ∧
            st.regs 13 = 0 ∧ st.regs 14 = 0 ∧ st.regs 15 = 2 * DCore cfg M q ∧
            ZeroFrom st.mem (h + 2 * k) ∧
            (∀ u < G.n, st.mem (locAddr + u) = 0) ∧
            (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem a))
          (fun _ hInit => hInit)
        refine runs_seq_triple_le hLoop
          ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
           by simp [startState], by simp [startState], by simp [startState], by simp [startState],
           by simp, by simp, by simp, by simp, by simp, by simp,
           fun a ha => hZero a (by omega), hloc0, fun _ _ _ => rfl⟩ ?_
        intro st₁ hInvEnd
        rcases hInvEnd with ⟨_, _, _, _, _, _, hr6_1, _, hr10_1, _, _, _,
          hhFin_lo, hhFin_hi, hZero1, hloc1, hfr1, hdisjEnd⟩
        set hFin := st₁.regs 12
        have hhFin_space : hFin ≤ h + coreProgSpace S_B S_C cfg M r q := by
          change hFin ≤ h + 2 * k + 2 * DCore cfg M q *
            oneShotProgSpace S_B S_C cfg M r q (coreProgSpace S_B S_C cfg M r (q - 1)) at hhFin_hi
          omega
        -- Post-loop branch on `st₁.regs 14 = 1`
        refine runs_cond_le (v := if st₁.regs 14 = 1 then 1 else 0)
          (Expr.eval_eq_op (Expr.eval_reg _ _ _) (Expr.eval_const hw1) hw1) ?_ ?_
        · -- `r14 = 1`: expander already written at `outAddr`, return `hFin`
          intro hne14
          have hr14_1 : st₁.regs 14 = 1 := by by_contra hne; simp [hne] at hne14
          have hRcase : ∃ R : Finset ℕ,
              CoreOutAt st₁.mem outAddr (.expander R) ∧ CoreSpec cp q G X (.expander R) := by
            rcases hdisjEnd with ⟨h0, _⟩ | ⟨_, hR⟩
            · omega
            · exact hR
          obtain ⟨R, hRout, hRspec⟩ := hRcase
          refine runs_ret_le (v := hFin) (Expr.eval_reg _ _ _)
            (hpost_wrap hFin st₁.mem ⟨.expander R, hRout, hRspec⟩
              (by omega) hhFin_space hZero1 hloc1 hfr1) ?_
          simp only [coreOnContract, Expr.size, List.getD_cons_zero]
          linarith only [htm_rec]
        · -- `r14 = 0`: `U` is a balanced sparse cut; copy `[h, h + uLen)` to `outAddr + 2`, return `hFin`
          intro hzero14
          have hr14_0 : st₁.regs 14 = 0 := by
            rcases hdisjEnd with ⟨h0, _⟩ | ⟨h1, _⟩
            · exact h0
            · simp [h1] at hzero14
          have hUcase : ∃ U : Finset ℕ,
              NodupVertsAt st₁.mem h (st₁.regs 13) U ∧ U ⊆ X ∧
              100 * G.cutIn X U ≤ U.card ∧ X.card ≤ 4 * (X \ U).card ∧
              2 * cp.D q * X.card ≤
                8 * cp.D q * U.card + 3 * (2 * cp.D q - 2 * DCore cfg M q) * X.card := by
            rcases hdisjEnd with ⟨_, hU⟩ | ⟨h1, _⟩
            · exact hU
            · omega
          obtain ⟨U, hUat, hUX, hUcut, hUbal, hUfuel⟩ := hUcase
          set uLen := st₁.regs 13
          have hUcard : U.card = uLen := nodupVertsAt_card hUat
          have huLen_le : uLen ≤ k := by rw [← hUcard, hX.1]; exact Finset.card_le_card hUX
          have h4U : X.card ≤ 4 * U.card := by
            have hsub0 : 2 * cp.D q - 2 * DCore cfg M q = 0 := Nat.sub_self _
            rw [hsub0, mul_zero, zero_mul, add_zero] at hUfuel
            have hmul : 2 * cp.D q * X.card ≤ 2 * cp.D q * (4 * U.card) := by
              calc 2 * cp.D q * X.card ≤ 8 * cp.D q * U.card := hUfuel
                _ = 2 * cp.D q * (4 * U.card) := by ring
            have hDq : 0 < cp.D q := hcfg.hD_pos hq1 hqr
            exact Nat.le_of_mul_le_mul_left hmul (by omega)
          have hUcutX : 100 * G.cutIn X U ≤ X.card := le_trans hUcut (Finset.card_le_card hUX)
          have hUspec : CoreSpec cp q G X (.cut U) := ⟨hUX, h4U, hUbal, hUcutX⟩
          obtain ⟨U_list, hUnd, hUfin, huLen_eq, hUlat⟩ := nodupVertsAt_iff_exists_listAt.mp hUat
          refine runs_seq_store_le (x := outAddr) (v := 0)
            (Expr.eval_reg_of_eq hr6_1) (Expr.eval_const (by omega)) ?_
          refine runs_seq_store_le (x := outAddr + 1) (v := uLen)
            (Expr.eval_add (Expr.eval_reg_of_eq hr6_1) (Expr.eval_const hw1) (by omega))
            (Expr.eval_reg _ _ _) ?_
          set mem2 := Function.update (Function.update st₁.mem outAddr 0) (outAddr + 1) uLen
          have hmem2_u : ∀ i < uLen, mem2 (h + i) = st₁.mem (h + i) := fun i hi => by
            have hne1 : h + i ≠ outAddr + 1 := by omega
            have hne0 : h + i ≠ outAddr := by omega
            simp [mem2, Function.update_of_ne hne1, Function.update_of_ne hne0]
          have hCp_pre : (copyWordsContract w).pre [uLen, h, outAddr + 2] mem2 := by
            refine ⟨uLen, h, outAddr + 2, rfl, by omega, by omega, by omega, by omega,
              Or.inl (by omega), fun i hi => ?_⟩
            rw [hmem2_u i hi, hUlat i (by omega)]
            have hmem : U_list[i]'(by omega) ∈ U :=
              hUfin ▸ List.mem_toFinset.mpr (List.getElem_mem (by omega))
            have hlt : U_list[i]'(by omega) < G.n := Finset.mem_range.mp (hXrange (hUX hmem))
            omega
          refine runs_seq_call_le (vs := [uLen, h, outAddr + 2]) hCopy
            (by simp [evalArgs, Expr.eval, hr10_1, hr6_1, uLen, hw2, show outAddr + 2 < 2 ^ w by omega])
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
            hCp_pre ?_
          intro _v3 mem3 _pos3 hpostCp
          simp only [copyWordsContract, List.getD_cons_zero, List.getD_cons_succ] at hpostCp
          rcases hpostCp with ⟨_, hcp_eq, hfr3⟩
          refine runs_ret_le (v := hFin) (by simp [Expr.eval, hFin]) ?_ ?_
          · refine hpost_wrap hFin mem3 ⟨.cut U, ?_, hUspec⟩ (by omega) hhFin_space ?_ ?_ ?_
            · refine ⟨?_, U_list, hUnd, hUfin, ?_, ?_⟩
              · rw [hfr3 outAddr (Or.inl (by omega))]; simp [mem2]
              · rw [hfr3 (outAddr + 1) (Or.inl (by omega))]; simp [mem2, huLen_eq]
              · intro i hi
                rw [hcp_eq i (by omega), hmem2_u i (by omega)]
                exact hUlat i hi
            · intro a ha
              rw [hfr3 a (Or.inr (by omega))]
              have hne1 : a ≠ outAddr + 1 := by omega
              have hne0 : a ≠ outAddr := by omega
              simp [mem2, Function.update_of_ne hne1, Function.update_of_ne hne0, hZero1 a ha]
            · intro u hu
              have hout_loc : locAddr + u < outAddr ∨ outAddr + 2 + k ≤ locAddr + u := by
                rcases hd_lo with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
              rw [hfr3 (locAddr + u) (by omega)]
              have hne1 : locAddr + u ≠ outAddr + 1 := by omega
              have hne0 : locAddr + u ≠ outAddr := by omega
              simp [mem2, Function.update_of_ne hne1, Function.update_of_ne hne0, hloc1 u hu]
            · intro a ha hno
              rw [hfr3 a (by omega)]
              have hne1 : a ≠ outAddr + 1 := by omega
              have hne0 : a ≠ outAddr := by omega
              simp [mem2, Function.update_of_ne hne1, Function.update_of_ne hne0, hfr1 a ha hno]
          · have hargC : argsSize [.reg 13, .reg 10, .bin .add (.reg 6) (.const 2)] = 5 := by decide
            simp only [coreOnContract, copyWordsContract, Expr.size, hargC, List.getD_cons_zero]
            have hcp_le : copyWordsCost uLen ≤ copyWordsCost k := by unfold copyWordsCost; omega
            linarith only [htm_rec, hcp_le]
      · -- Case `k ≤ N ^ (q - 1)`: delegate to `idx.coreOn` at level `q - 1` via `ih`
        intro hzeroGt
        have hkle : k ≤ cp.N ^ (q - 1) := by by_contra hgt; simp [Nat.lt_of_not_ge hgt] at hzeroGt
        have hTB_mono : coreTimeBound cfg M r (q - 1) + 1 ≤ coreTimeBound cfg M r q :=
          coreTimeBound_mono_succ cfg M r q hq1
        have hsp_mono : coreProgSpace S_B S_C cfg M r (q - 1) ≤ coreProgSpace S_B S_C cfg M r q :=
          Nat.mul_le_mul_left _ (by omega)
        have htm_mono : coreProgTime K_B K_C cfg M r (q - 1) + 1000 ≤
            coreProgTime K_B K_C cfg M r q := by
          unfold coreProgTime coreTimeConst
          have hK1000 : 1000 ≤ max (K_B + K_C + 2) 1000 := le_max_right _ _
          have hmul := Nat.mul_le_mul_left (max (K_B + K_C + 2) 1000) hTB_mono
          rw [Nat.mul_add, Nat.mul_one] at hmul
          linarith only [hK1000, hmul]
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := q - 1)
          (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [startState]))
            (Expr.eval_const hw1) (by omega)) ?_
        have hrec_pre : ((coreOnContract cfg M r w K_B K_C S_B S_C).below
            (fun args _ => args.getD 0 0) q).pre
            [q - 1, gAddr, k, xAddr, pAddr, locAddr, outAddr, h] mem :=
          ⟨⟨q - 1, gAddr, k, xAddr, pAddr, locAddr, outAddr, h, G, X,
            rfl, ha0, ha, hrl, by omega, hP, hG, hGvalid, hGn, hX, hXrange, hGloop, hkle,
            hdegG, hmG, hloc0, hg_h, hx_h, hp_h, hloc_h, hout_h,
            hd_lg, hd_lx, hd_lp, hd_lo, hd_og, hd_ox, hd_op, hZero, by omega⟩,
           by simp; omega⟩
        refine runs_seq_call_le
          (vs := [q - 1, gAddr, k, xAddr, pAddr, locAddr, outAddr, h]) ih
          (by simp [evalArgs, Expr.eval, startState])
          (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
          hrec_pre ?_
        intro hFin memFin _posFin hpostRec
        have hrec_res := hpostRec (q - 1) gAddr k xAddr pAddr locAddr outAddr h G X
          rfl ha0 ha hrl (by omega) hP hG hGvalid hGn hX hXrange hGloop hkle
          hdegG hmG hloc0 hg_h hx_h hp_h hloc_h hout_h
          hd_lg hd_lx hd_lp hd_lo hd_og hd_ox hd_op hZero (by omega)
        rcases hrec_res with ⟨⟨res, hResOut, hResSpec⟩, hhFin_lo, hhFin_hi, hZeroFin, hlocFin, hfrFin⟩
        have hSpec_q : CoreSpec cp q G X res := by
          cases res with
          | cut U => exact hResSpec
          | expander R =>
            rcases hResSpec with ⟨hRX, h2R, hRexp⟩
            have hPpos : (0 : ℝ) < cp.P (q - 1) := Nat.cast_pos.mpr (hcfg.hP_pos (by omega))
            have hPmono : (cp.P (q - 1) : ℝ) ≤ cp.P q := by
              have h1 := hcfg.hPmono (q - 1) (by omega)
              have hqeq : q - 1 + 1 = q := by omega
              rw [hqeq] at h1
              exact_mod_cast h1
            exact ⟨hRX, h2R, IsExpansionExpanderOn.mono (one_div_le_one_div_of_le hPpos hPmono) hRexp⟩
        refine runs_ret_le (v := hFin) (by simp [Expr.eval])
          (hpost_wrap hFin memFin ⟨res, hResOut, hSpec_q⟩ hhFin_lo (by omega) hZeroFin hlocFin hfrFin) ?_
        have hargRec : argsSize [.reg 17, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6,
          .reg 7] = 8 := by decide
        simp only [Contract.below, coreOnContract, Expr.size, hargRec, List.getD_cons_zero]
        omega

end MinCostFlow.ExpanderDecomp
