module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleBounds

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Word-RAM `innerVerts` fold model and `forRange` loop spec for `t2MiddleEdgeBody` -/

noncomputable def t2MiddleInnerFold (embJH : ℕ → Walk) (procVerts : Finset ℕ)
    (vcong0 : ℕ → ℕ) (thresh wVal eJ k : ℕ) (init : Finset ℕ × List ℕ) : Finset ℕ × List ℕ :=
  (List.range k).foldl (fun (S, q) idx =>
    let x := (embJH eJ).verts.getD idx 0
    if x ∈ S then (S, q)
    else if x ∉ procVerts ∧ thresh ≤ vcong0 x + wVal then (insert x S, q ++ [x])
    else (insert x S, q)) init

lemma t2MiddleInnerFold_step {embJH : ℕ → Walk} {procVerts : Finset ℕ}
    {vcong0 : ℕ → ℕ} {thresh wVal eJ k : ℕ} {init : Finset ℕ × List ℕ} :
    t2MiddleInnerFold embJH procVerts vcong0 thresh wVal eJ (k + 1) init =
      let p := t2MiddleInnerFold embJH procVerts vcong0 thresh wVal eJ k init
      let x := (embJH eJ).verts.getD k 0
      if x ∈ p.1 then p
      else if x ∉ procVerts ∧ thresh ≤ vcong0 x + wVal then (insert x p.1, p.2 ++ [x])
      else (insert x p.1, p.2) := by
  simp [t2MiddleInnerFold, List.range_succ, List.foldl_append]

lemma t2Middle_innerVerts_forRange {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {eJ walkPtr wVal : ℕ} (heJ : eJ < inp.J.m)
    (heVerts_lt : ∀ x ∈ (inp.embJH eJ).verts, x < inp.H'.n)
    (heVerts_len_w : (inp.embJH eJ).verts.length < 2 ^ w)
    (hwk_e : WalkAt memStart walkPtr (inp.embJH eJ))
    (hwp_bd : walkPtr + (inp.embJH eJ).encode.length ≤ inp.t1OutAddr)
    (ht1_v1 : inp.t1OutAddr ≤ inp.v1)
    {vcong0 : ℕ → ℕ}
    (S_in : Finset ℕ) (q_in : List ℕ)
    (hS_sub : S_in ⊆ Finset.range inp.H'.n)
    (hq_sub : q_in.toFinset ⊆ S_in) (hq_nd : q_in.Nodup)
    (hq_spec : ∀ x, x ∈ q_in ↔ x ∈ S_in ∧ x ∉ g₀.procVerts ∧
      memStart (inp.v1 + 28) ≤ vcong0 x + wVal)
    (hvc_bd : ∀ x < inp.H'.n, vcong0 x + wVal < 2 ^ w)
    (hH_w : inp.H'.n < 2 ^ w) (hw_bd : Task2Input.maxWordBound impl inp < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (mem : ℕ → ℕ)
    (hmem_walk : ∀ k < (inp.embJH eJ).verts.length, mem (walkPtr + 1 + k) = memStart (walkPtr + 1 + k))
    (hm_ew : ∀ x < inp.H'.n, mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) =
      if x ∈ S_in then g₀.queryId + 1 else memStart (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x))
    (hm_vc : ∀ x < inp.H'.n, mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
      vcong0 x + (if x ∈ S_in then wVal else 0))
    (hm_ps : ∀ x < inp.H'.n, mem (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) =
      if x ∈ q_in then g₀.η₁ else memStart (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x))
    (hm_q : ∀ (k : ℕ) (hk : k < q_in.length), mem (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + k) = q_in[k]'hk)
    (hr_init : ℕ → ℕ)
    (hr25 : hr_init 25 = g₀.queryId + 1) (hr26 : hr_init 26 = wVal)
    (hr28 : hr_init 28 = inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr29 : hr_init 29 = inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr30 : hr_init 30 = inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr31 : hr_init 31 = memStart (inp.v1 + 28)) (hr32 : hr_init 32 = g₀.η₁)
    (hr33 : hr_init 33 = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr34 : hr_init 34 = q_in.length) (hr38 : hr_init 38 = walkPtr)
    (hr39 : hr_init 39 = (inp.embJH eJ).verts.length)
    (pos₀ : ℕ) (ω : ℕ → Bool) :
    let ewA := inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length
    let vcA := inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length
    let psA := inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length
    let qA := inp.queueAddr ctx.wd.W.m ctx.wd.comps.length
    let body :=
      Stmt.assign 41 (t2Ld (.reg 38) (t2Add (.const 1) (.reg 40))) ;;
      Stmt.cond (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)) (
        t2St (.reg 28) (.reg 41) (.reg 25) ;;
        Stmt.assign 42 (t2Add (t2Ld (.reg 29) (.reg 41)) (.reg 26)) ;;
        t2St (.reg 29) (.reg 41) (.reg 42) ;;
        Stmt.cond (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)) (
          Stmt.cond (t2Le (.reg 31) (.reg 42)) (
            t2St (.reg 30) (.reg 41) (.reg 32) ;;
            t2St (.reg 33) (.reg 34) (.reg 41) ;;
            Stmt.assign 34 (t2Add (.reg 34) (.const 1))
          ) Stmt.nop
        ) Stmt.nop
      ) Stmt.nop
    let res := t2MiddleInnerFold inp.embJH g₀.procVerts vcong0
      (memStart (inp.v1 + 28)) wVal eJ (inp.embJH eJ).verts.length (S_in, q_in)
    ∃ st' c_run,
      Runs w p ω (forRange 40 (.const 0) (.reg 39) body) ⟨mem, hr_init, pos₀⟩ .normal st' c_run ∧
      (∀ r ≤ 39, r ≠ 34 → st'.regs r = hr_init r) ∧
      st'.regs 34 = res.2.length ∧
      (∀ a, ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → st'.mem a = mem a) ∧
      res.1 = S_in ∪ (inp.embJH eJ).verts.toFinset ∧
      res.1 ⊆ Finset.range inp.H'.n ∧
      res.2.toFinset ⊆ res.1 ∧
      res.2.Nodup ∧
      (∀ x, x ∈ res.2 ↔ x ∈ res.1 ∧ x ∉ g₀.procVerts ∧ memStart (inp.v1 + 28) ≤ vcong0 x + wVal) ∧
      (∀ x < inp.H'.n, st'.mem (ewA + x) = if x ∈ res.1 then g₀.queryId + 1 else memStart (ewA + x)) ∧
      (∀ x < inp.H'.n, st'.mem (vcA + x) = vcong0 x + (if x ∈ res.1 then wVal else 0)) ∧
      (∀ x < inp.H'.n, st'.mem (psA + x) = if x ∈ res.2 then g₀.η₁ else memStart (psA + x)) ∧
      (∀ (k : ℕ) (hk : k < res.2.length), st'.mem (qA + k) = res.2[k]'hk) ∧
      c_run ≤ (inp.embJH eJ).verts.length * 75 + 7 := by
  intro ewA vcA psA qA body res
  let innerIf2 : Stmt :=
    Stmt.cond (t2Le (.reg 31) (.reg 42))
      (t2St (.reg 30) (.reg 41) (.reg 32) ;;
       t2St (.reg 33) (.reg 34) (.reg 41) ;;
       Stmt.assign 34 (t2Add (.reg 34) (.const 1))) Stmt.nop
  let innerIf1 : Stmt := Stmt.cond (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)) innerIf2 Stmt.nop
  let innerThen : Stmt :=
    t2St (.reg 28) (.reg 41) (.reg 25) ;;
    Stmt.assign 42 (t2Add (t2Ld (.reg 29) (.reg 41)) (.reg 26)) ;;
    t2St (.reg 29) (.reg 41) (.reg 42) ;;
    innerIf1
  let innerCond : Stmt := Stmt.cond (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)) innerThen Stmt.nop
  have db := drain_bounds ctx stc
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc; have _ := db.h_mhe
  have hw_qA : qA + inp.H'.n < 2 ^ w := by
    dsimp only [qA] at *; omega
  have hw_ewA : ewA + inp.H'.n < 2 ^ w := by
    dsimp only [ewA] at *; omega
  have hw_vcA : vcA + inp.H'.n < 2 ^ w := by
    dsimp only [vcA] at *; omega
  have hw_psA : psA + inp.H'.n < 2 ^ w := by
    dsimp only [psA] at *; omega
  have hvc_ps : vcA + inp.H'.n = psA := db.e_vc
  have hps_ew : psA + inp.H'.n = ewA := db.e_ps
  have hew_q : ewA + inp.H'.n = qA := db.e_ew
  have hqId_w : g₀.queryId + 1 < 2 ^ w := by
    have h1 : g₀.queryId ≤ ctx.wd.W.m := by
      have hj0 : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
        rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
      have := hS.hGetC; have := hS.hQid; omega
    have hmW := ctx.hmW_le
    have hle1 : g₀.queryId + 1 ≤ Task1Input.mwCap impl inp.J + 1 :=
      Nat.add_le_add_right (le_trans h1 hmW) 1
    have h2 : Task1Input.mwCap impl inp.J + 1 ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      exact le_trans (by omega) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    exact Nat.lt_of_le_of_lt (le_trans hle1 h2) hw_bd
  have hη_w : g₀.η₁ < 2 ^ w := by
    have h1 : eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J :=
      ctx.hWInpJ ▸ task2_eta1Bound_le_cap ctx.hstat ctx.hφ_lb
    have hJm_pos : 1 ≤ inp.J.m := Nat.lt_of_le_of_lt (Nat.zero_le eJ) heJ
    have hη_le : Task2Input.eta1Cap impl inp.J ≤ Task2Input.eta1Cap impl inp.J * inp.J.m :=
      Nat.le_mul_of_pos_right _ hJm_pos
    have h2 : Task2Input.eta1Cap impl inp.J ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      exact le_trans hη_le
        (le_trans (Nat.le_add_right _ _)
          (le_trans (Nat.le_add_right _ 2)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
    exact Nat.lt_of_le_of_lt (le_trans hS.hη_bd (le_trans h1 h2)) hw_bd
  have hth_w : memStart (inp.v1 + 28) < 2 ^ w := by
    rw [hS.h28]
    have hη_c : eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J :=
      ctx.hWInpJ ▸ task2_eta1Bound_le_cap ctx.hstat ctx.hφ_lb
    have hτ := ctx.tau1Int_le_cap
    have hpd : ctx.wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J :=
      ctx.hWInpJ ▸ task2_phiDen_le_cap ctx.hstat ctx.hφ_cap
    have h1 : g₀.η₁ * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
        ctx.wInp.prep.phiDen_dec ≤ Task2Input.maxWordBound impl inp := by
      have hm1 := Nat.mul_le_mul (Nat.mul_le_mul (le_trans hS.hη_bd hη_c) hτ) hpd
      unfold Task2Input.maxWordBound
      exact le_trans (le_trans hm1 (Nat.le_add_right _ _))
        (le_trans (Nat.le_add_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
    exact Nat.lt_of_le_of_lt h1 hw_bd
  let foldK := fun k => t2MiddleInnerFold inp.embJH g₀.procVerts vcong0
    (memStart (inp.v1 + 28)) wVal eJ k (S_in, q_in)
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ r ≤ 39, r ≠ 34 → st.regs r = hr_init r) ∧ st.regs 40 = k ∧ st.regs 34 = (foldK k).2.length ∧
    (∀ a, ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → st.mem a = mem a) ∧
    (foldK k).1 = S_in ∪ ((inp.embJH eJ).verts.take k).toFinset ∧
    (foldK k).1 ⊆ Finset.range inp.H'.n ∧
    (foldK k).2.toFinset ⊆ (foldK k).1 ∧
    (foldK k).2.Nodup ∧
    (∀ x, x ∈ (foldK k).2 ↔ x ∈ (foldK k).1 ∧ x ∉ g₀.procVerts ∧ memStart (inp.v1 + 28) ≤ vcong0 x + wVal) ∧
    (∀ x < inp.H'.n, st.mem (ewA + x) = if x ∈ (foldK k).1 then g₀.queryId + 1 else memStart (ewA + x)) ∧
    (∀ x < inp.H'.n, st.mem (vcA + x) = vcong0 x + (if x ∈ (foldK k).1 then wVal else 0)) ∧
    (∀ x < inp.H'.n, st.mem (psA + x) = if x ∈ (foldK k).2 then g₀.η₁ else memStart (psA + x)) ∧
    (∀ idx (hidx : idx < (foldK k).2.length), st.mem (qA + idx) = (foldK k).2[idx]'hidx)
  let P0 : State → Prop := fun st =>
    (∀ r ≤ 39, r ≠ 34 → st.regs r = hr_init r) ∧ st.regs 34 = q_in.length ∧
    (∀ a, ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → st.mem a = mem a) ∧
    (∀ x < inp.H'.n, st.mem (ewA + x) = if x ∈ S_in then g₀.queryId + 1 else memStart (ewA + x)) ∧
    (∀ x < inp.H'.n, st.mem (vcA + x) = vcong0 x + (if x ∈ S_in then wVal else 0)) ∧
    (∀ x < inp.H'.n, st.mem (psA + x) = if x ∈ q_in then g₀.η₁ else memStart (psA + x)) ∧
    (∀ idx (hidx : idx < q_in.length), st.mem (qA + idx) = q_in[idx]'hidx)
  have htrip : Triple w p P0 (forRange 40 (.const 0) (.reg 39) body)
      (normalPost (Inv (inp.embJH eJ).verts.length))
      (fun _ => (inp.embJH eJ).verts.length * 75 + 7) := by
    have hfor := Triple.forRange_const (w := w) (p := p) (P := P0) (r := 40) (lo := .const 0)
      (hi := .reg 39) (body := body) (Inv := Inv) (stepBound := 66) (loVal := 0)
      (hiVal := (inp.embJH eJ).verts.length) (Nat.zero_le _) hw1 (fun _ => heVerts_len_w)
      (fun st hP0 => by
        refine ⟨Expr.eval_const (by omega), ?_⟩
        rcases hP0 with ⟨hr, hr34, hagr, hew, hvc, hps, hq⟩
        refine ⟨fun r hr_le hne => ?_, by simp, ?_, hagr, ?_, hS_sub, hq_sub, hq_nd, hq_spec,
          hew, hvc, hps, hq⟩
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r hr_le hne
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr34
        · simp [foldK, t2MiddleInnerFold])
      (fun k _ _ _ hI => hI.2.1)
      (fun k st _ _ hI => Expr.eval_reg_of_eq ((hI.1 39 (by omega) (by omega)).trans hr39))
      fun k _ hk => by
        intro st ω_run hI
        rcases hI with ⟨hregs, hr40, hr34, hagr, hF1, hF1_sub, hF2_sub, hF2_nd, hF2_spec,
          hm_ew_k, hm_vc_k, hm_ps_k, hm_q_k⟩
        set pK := foldK k
        set x := (inp.embJH eJ).verts[k]'hk
        have hx_H : x < inp.H'.n := heVerts_lt x (List.getElem_mem hk)
        have hx_eq_getD : (inp.embJH eJ).verts.getD k 0 = x := List.getD_eq_getElem _ _ hk
        have hstep_fold : foldK (k + 1) =
            if x ∈ pK.1 then pK
            else if x ∉ g₀.procVerts ∧ memStart (inp.v1 + 28) ≤ vcong0 x + wVal then
              (insert x pK.1, pK.2 ++ [x])
            else (insert x pK.1, pK.2) := by
          dsimp only [foldK, pK]; rw [t2MiddleInnerFold_step, hx_eq_getD]
        have htk_succ : ((inp.embJH eJ).verts.take (k + 1)).toFinset =
            insert x ((inp.embJH eJ).verts.take k).toFinset := by
          ext z
          rw [List.mem_toFinset, Finset.mem_insert, List.mem_toFinset, List.take_add_one,
            List.getElem?_eq_getElem hk]
          simp only [Option.toList_some, List.mem_append, List.mem_singleton, x]
          tauto
        have hwk_pos : walkPtr + 1 + k < walkPtr + (inp.embJH eJ).encode.length := by
          rw [walk_encode_length]; omega
        have hwk_w : walkPtr + (1 + k) < 2 ^ w := by omega
        have hmem_x : st.mem (walkPtr + (1 + k)) = x := by
          rw [hagr _ (by omega), show walkPtr + (1 + k) = walkPtr + 1 + k by omega,
            hmem_walk k hk]
          exact hwk_e.verts_listAt k hk
        have hs1 : Runs w p ω_run (Stmt.assign 41 (t2Ld (.reg 38) (t2Add (.const 1) (.reg 40)))) st .normal
            { st with regs := Function.update st.regs 41 x } 7 := by
          have ha1 := Expr.eval_add (w := w) (Expr.eval_const hw1) (Expr.eval_reg_of_eq hr40) (by omega)
          have ha2 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hregs 38 (by omega) (by omega)).trans hr38)) ha1 hwk_w
          exact runs_assign_iff.mpr ⟨x, by simpa only [t2Ld, hmem_x] using Expr.eval_load ha2,
            rfl, rfl, by simp [Expr.size]⟩
        set st1 : State := { st with regs := Function.update st.regs 41 x }
        have hr1 : ∀ r ≤ 40, st1.regs r = st.regs r := fun r hr => by
          dsimp only [st1]; rw [Function.update_of_ne (by omega)]
        have h41_1 : st1.regs 41 = x := by simp [st1]
        have hew_x_lt : memStart (ewA + x) < g₀.queryId + 1 := by
          have : memStart (ewA + x) ≤ g₀.queryId := hS.hEwSt x hx_H
          omega
        have hcond_ew : (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)).eval w st1 =
            some (if x ∈ pK.1 then 0 else 1) := by
          have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr1 28 (by omega)).trans ((hregs 28 (by omega) (by omega)).trans hr28)))
            (Expr.eval_reg_of_eq h41_1) (by omega)
          have hld := Expr.eval_load ha
          have hmem1 : st1.mem (ewA + x) = st.mem (ewA + x) := rfl
          rw [hmem1, hm_ew_k x hx_H] at hld
          have h25 := Expr.eval_reg_of_eq (w := w) ((hr1 25 (by omega)).trans ((hregs 25 (by omega) (by omega)).trans hr25))
          have h_eq := Expr.eval_eq_op hld h25 hw1
          have h0 : (Expr.const 0).eval w st1 = some 0 := Expr.eval_const (by omega)
          by_cases hx_in : x ∈ pK.1
          · simp only [hx_in, ↓reduceIte] at h_eq ⊢
            simpa [t2Ne] using Expr.eval_eq_op h_eq h0 hw1
          · have hne_q : memStart (ewA + x) ≠ g₀.queryId + 1 := by omega
            simp only [hx_in, ↓reduceIte, hne_q] at h_eq ⊢
            simpa [t2Ne] using Expr.eval_eq_op h_eq h0 hw1
        by_cases hx_in : x ∈ pK.1
        · have hc_skip : (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)).eval w st1 = some 0 := by
            simpa [hx_in] using hcond_ew
          have hcr : Runs w p ω_run innerCond st1 .normal st1 (8 + 1 + 1) :=
            runs_cond_iff.mpr ⟨0, 1, hc_skip, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
          have hr_b : Runs w p ω_run body st .normal st1 (7 + (8 + 1 + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st1, 7, 10, hs1, hcr, rfl⟩)
          have hF1' : (foldK (k + 1)).1 = S_in ∪ ((inp.embJH eJ).verts.take (k + 1)).toFinset := by
            rw [hstep_fold]; simp only [hx_in, ↓reduceIte]
            calc pK.1 = insert x pK.1 := (Finset.insert_eq_of_mem hx_in).symm
              _ = insert x (S_in ∪ ((inp.embJH eJ).verts.take k).toFinset) := by rw [hF1]
              _ = S_in ∪ insert x ((inp.embJH eJ).verts.take k).toFinset := by rw [Finset.union_insert]
              _ = S_in ∪ ((inp.embJH eJ).verts.take (k + 1)).toFinset := by rw [htk_succ]
          have hf_eq : foldK (k + 1) = pK := by rw [hstep_fold]; simp [hx_in]
          refine ⟨.normal, st1, 7 + (8 + 1 + 1) + 1, hr_b,
            ⟨?_, (hr1 40 (by omega)).trans hr40⟩, by dsimp only; omega⟩
          refine ⟨fun r hr hne => by
              dsimp only
              rw [Function.update_of_ne (show r ≠ 40 by omega)]
              exact (hr1 r (by omega)).trans (hregs r hr hne),
            by simp, ?_, hagr, hF1', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hf_eq]; exact (hr1 34 (by omega)).trans hr34
          · rw [hf_eq]; exact hF1_sub
          · rw [hf_eq]; exact hF2_sub
          · rw [hf_eq]; exact hF2_nd
          · intro y; rw [hf_eq]; exact hF2_spec y
          · intro y hy; rw [hf_eq]; exact hm_ew_k y hy
          · intro y hy; rw [hf_eq]; exact hm_vc_k y hy
          · intro y hy; rw [hf_eq]; exact hm_ps_k y hy
          · intro idx hidx; simp only [hf_eq] at hidx ⊢; exact hm_q_k idx hidx
        · have hc_go : (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)).eval w st1 = some 1 := by
            simpa [hx_in] using hcond_ew
          have hx_n2 : x ∉ pK.2 := fun hm => hx_in (hF2_sub (List.mem_toFinset.mpr hm))
          have hs_ew : Runs w p ω_run (t2St (.reg 28) (.reg 41) (.reg 25)) st1 .normal
              { st1 with mem := Function.update st1.mem (ewA + x) (g₀.queryId + 1) } 5 := by
            have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr1 28 (by omega)).trans ((hregs 28 (by omega) (by omega)).trans hr28)))
              (Expr.eval_reg_of_eq h41_1) (by omega)
            have hv := Expr.eval_reg_of_eq (w := w) ((hr1 25 (by omega)).trans ((hregs 25 (by omega) (by omega)).trans hr25))
            exact runs_store_iff.mpr ⟨ewA + x, g₀.queryId + 1, ha, hv, rfl, rfl, by simp [Expr.size]⟩
          set st2 : State := { st1 with mem := Function.update st1.mem (ewA + x) (g₀.queryId + 1) }
          have hm_vc_x : st2.mem (vcA + x) = vcong0 x := by
            dsimp only [st2, st1]
            rw [Function.update_of_ne (by omega)]
            simp only [hm_vc_k x hx_H, hx_in, ↓reduceIte, add_zero]
          have hs_42 : Runs w p ω_run (Stmt.assign 42 (t2Add (t2Ld (.reg 29) (.reg 41)) (.reg 26))) st2 .normal
              { st2 with regs := Function.update st2.regs 42 (vcong0 x + wVal) } 7 := by
            have ha := Expr.eval_add (w := w)
              (Expr.eval_reg_of_eq (show st2.regs 29 = vcA from (hr1 29 (by omega)).trans ((hregs 29 (by omega) (by omega)).trans hr29)))
              (Expr.eval_reg_of_eq (show st2.regs 41 = x from h41_1)) (by omega)
            have hld := Expr.eval_load ha
            change Expr.eval w st2 (t2Ld (.reg 29) (.reg 41)) = some (st2.mem (vcA + x)) at hld
            rw [hm_vc_x] at hld
            have hv := Expr.eval_reg_of_eq (w := w) ((hr1 26 (by omega)).trans ((hregs 26 (by omega) (by omega)).trans hr26))
            exact runs_assign_iff.mpr ⟨vcong0 x + wVal, Expr.eval_add hld hv (hvc_bd x hx_H), rfl, rfl, by simp [Expr.size]⟩
          set st3 : State := { st2 with regs := Function.update st2.regs 42 (vcong0 x + wVal) }
          have hr3 : ∀ r ≤ 41, st3.regs r = st1.regs r := fun r hr => by
            dsimp only [st3, st2]; rw [Function.update_of_ne (by omega)]
          have hs_vc : Runs w p ω_run (t2St (.reg 29) (.reg 41) (.reg 42)) st3 .normal
              { st3 with mem := Function.update st3.mem (vcA + x) (vcong0 x + wVal) } 5 := by
            have ha := Expr.eval_add (w := w)
              (Expr.eval_reg_of_eq ((hr3 29 (by omega)).trans ((hr1 29 (by omega)).trans ((hregs 29 (by omega) (by omega)).trans hr29))))
              (Expr.eval_reg_of_eq ((hr3 41 (by omega)).trans h41_1)) (by omega)
            have hv := Expr.eval_reg_of_eq (w := w) (show st3.regs 42 = vcong0 x + wVal by simp [st3])
            exact runs_store_iff.mpr ⟨vcA + x, vcong0 x + wVal, ha, hv, rfl, rfl, by simp [Expr.size]⟩
          set st4 : State := { st3 with mem := Function.update st3.mem (vcA + x) (vcong0 x + wVal) }
          have hm_ps_x : st4.mem (psA + x) = memStart (psA + x) := by
            dsimp only [st4, st3, st2, st1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            simp only [hm_ps_k x hx_H, hx_n2, ↓reduceIte]
          have hr4 : ∀ r ≤ 41, st4.regs r = st1.regs r := fun r hr => by
            dsimp only [st4, st3, st2]; rw [Function.update_of_ne (by omega)]
          have hps_cond : (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)).eval w st4 =
              some (if x ∉ g₀.procVerts then 1 else 0) := by
            have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr4 30 (by omega)).trans ((hr1 30 (by omega)).trans ((hregs 30 (by omega) (by omega)).trans hr30))))
              (Expr.eval_reg_of_eq ((hr4 41 (by omega)).trans h41_1)) (by omega)
            have hld := Expr.eval_load ha
            rw [hm_ps_x] at hld
            have hv := Expr.eval_reg_of_eq (w := w) ((hr4 32 (by omega)).trans ((hr1 32 (by omega)).trans ((hregs 32 (by omega) (by omega)).trans hr32)))
            have hps_le : memStart (psA + x) ≤ g₀.η₁ := (hS.hProcS x hx_H).1
            have hlt_eval := Expr.eval_lt_op (w := w) hld hv hw1
            by_cases hnp : x ∉ g₀.procVerts
            · have hne : memStart (psA + x) ≠ g₀.η₁ := fun h => hnp ((hS.hProcS x hx_H).2.mp h)
              simpa [t2Lt, t2Ld, hnp, show memStart (psA + x) < g₀.η₁ by omega] using hlt_eval
            · push Not at hnp
              have heq : memStart (psA + x) = g₀.η₁ := (hS.hProcS x hx_H).2.mpr hnp
              simpa [t2Lt, t2Ld, hnp, heq] using hlt_eval
          have htail : ∃ stF c_tail,
              Runs w p ω_run innerIf1 st4 .normal stF c_tail ∧
              c_tail ≤ 29 ∧
              (∀ r ≤ 40, r ≠ 34 → stF.regs r = st4.regs r) ∧
              stF.regs 34 = (foldK (k + 1)).2.length ∧
              (∀ a, ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → stF.mem a = mem a) ∧
              (foldK (k + 1)).2.toFinset ⊆ (foldK (k + 1)).1 ∧
              (foldK (k + 1)).2.Nodup ∧
              (∀ y, y ∈ (foldK (k + 1)).2 ↔ y ∈ (foldK (k + 1)).1 ∧ y ∉ g₀.procVerts ∧
                memStart (inp.v1 + 28) ≤ vcong0 y + wVal) ∧
              (∀ y < inp.H'.n, stF.mem (ewA + y) =
                if y ∈ (foldK (k + 1)).1 then g₀.queryId + 1 else memStart (ewA + y)) ∧
              (∀ y < inp.H'.n, stF.mem (vcA + y) =
                vcong0 y + (if y ∈ (foldK (k + 1)).1 then wVal else 0)) ∧
              (∀ y < inp.H'.n, stF.mem (psA + y) =
                if y ∈ (foldK (k + 1)).2 then g₀.η₁ else memStart (psA + y)) ∧
              ∀ idx (hidx : idx < (foldK (k + 1)).2.length), stF.mem (qA + idx) = (foldK (k + 1)).2[idx]'hidx := by
            have hst4_agr : ∀ a, ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → st4.mem a = mem a := fun a ha => by
              dsimp only [st4, st3, st2, st1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hagr a ha
            have hst4_ew : ∀ y < inp.H'.n, st4.mem (ewA + y) =
                if y ∈ insert x pK.1 then g₀.queryId + 1 else memStart (ewA + y) := fun y hy => by
              dsimp only [st4, st3, st2, st1]
              rw [Function.update_of_ne (by omega)]
              by_cases hyx : y = x
              · subst hyx; rw [Function.update_self]; simp
              · rw [Function.update_of_ne (by omega), hm_ew_k y hy]; simp [hyx]
            have hst4_vc : ∀ y < inp.H'.n, st4.mem (vcA + y) =
                vcong0 y + (if y ∈ insert x pK.1 then wVal else 0) := fun y hy => by
              dsimp only [st4, st3, st2, st1]
              by_cases hyx : y = x
              · subst hyx; rw [Function.update_self]; simp
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm_vc_k y hy]
                simp [hyx]
            have hst4_ps : ∀ y < inp.H'.n, st4.mem (psA + y) =
                if y ∈ pK.2 then g₀.η₁ else memStart (psA + y) := fun y hy => by
              dsimp only [st4, st3, st2, st1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm_ps_k y hy]
            have hst4_q : ∀ idx (hidx : idx < pK.2.length), st4.mem (qA + idx) = pK.2[idx]'hidx := fun idx hidx => by
              have hlt_H : pK.2.length ≤ inp.H'.n := by
                have := Finset.card_le_card (Finset.Subset.trans hF2_sub hF1_sub)
                rw [List.toFinset_card_of_nodup hF2_nd, Finset.card_range] at this; omega
              dsimp only [st4, st3, st2, st1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm_q_k idx hidx]
            by_cases hnp : x ∉ g₀.procVerts
            · have hc_p1 : (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)).eval w st4 = some 1 := by
                simpa [hnp] using hps_cond
              have hle_eval : (t2Le (.reg 31) (.reg 42)).eval w st4 =
                  some (if memStart (inp.v1 + 28) ≤ vcong0 x + wVal then 1 else 0) := by
                have hr31 := Expr.eval_reg_of_eq (w := w) ((hr4 31 (by omega)).trans ((hr1 31 (by omega)).trans ((hregs 31 (by omega) (by omega)).trans hr31)))
                have hr42 := Expr.eval_reg_of_eq (w := w) (show st4.regs 42 = vcong0 x + wVal by simp [st4, st3])
                have hlt_op := Expr.eval_lt_op (w := w) hr42 hr31 hw1
                have h0 : (Expr.const 0).eval w st4 = some 0 := Expr.eval_const (by omega)
                by_cases hle_v : memStart (inp.v1 + 28) ≤ vcong0 x + wVal
                · have hnot_lt : ¬(vcong0 x + wVal < memStart (inp.v1 + 28)) := by omega
                  simp only [hle_v, ↓reduceIte, hnot_lt] at hlt_op ⊢
                  simpa [t2Le] using Expr.eval_eq_op hlt_op h0 hw1
                · have hlt_v : vcong0 x + wVal < memStart (inp.v1 + 28) := by omega
                  simp only [hle_v, ↓reduceIte, hlt_v] at hlt_op ⊢
                  simpa [t2Le] using Expr.eval_eq_op hlt_op h0 hw1
              by_cases hth_le : memStart (inp.v1 + 28) ≤ vcong0 x + wVal
              · have hc_t : (t2Le (.reg 31) (.reg 42)).eval w st4 = some 1 := by simpa [hth_le] using hle_eval
                have hlen_lt_H : pK.2.length < inp.H'.n := by
                  have hsub_e : pK.2.toFinset ⊆ (Finset.range inp.H'.n).erase x := by
                    intro y hy
                    rw [Finset.mem_erase]
                    exact ⟨fun h => hx_n2 (h ▸ List.mem_toFinset.mp hy), hF1_sub (hF2_sub hy)⟩
                  have hcard := Finset.card_le_card hsub_e
                  rw [List.toFinset_card_of_nodup hF2_nd, Finset.card_erase_of_mem (Finset.mem_range.mpr hx_H),
                    Finset.card_range] at hcard
                  omega
                have hp_t : Runs w p ω_run (t2St (.reg 30) (.reg 41) (.reg 32)) st4 .normal
                    { st4 with mem := Function.update st4.mem (psA + x) g₀.η₁ } 5 := by
                  have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr4 30 (by omega)).trans ((hr1 30 (by omega)).trans ((hregs 30 (by omega) (by omega)).trans hr30))))
                    (Expr.eval_reg_of_eq ((hr4 41 (by omega)).trans h41_1)) (by omega)
                  have hv := Expr.eval_reg_of_eq (w := w) ((hr4 32 (by omega)).trans ((hr1 32 (by omega)).trans ((hregs 32 (by omega) (by omega)).trans hr32)))
                  exact runs_store_iff.mpr ⟨psA + x, g₀.η₁, ha, hv, rfl, rfl, by simp [Expr.size]⟩
                set st5 : State := { st4 with mem := Function.update st4.mem (psA + x) g₀.η₁ }
                have hq_t : Runs w p ω_run (t2St (.reg 33) (.reg 34) (.reg 41)) st5 .normal
                    { st5 with mem := Function.update st5.mem (qA + pK.2.length) x } 5 := by
                  have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr4 33 (by omega)).trans ((hr1 33 (by omega)).trans ((hregs 33 (by omega) (by omega)).trans hr33))))
                    (Expr.eval_reg_of_eq ((hr4 34 (by omega)).trans ((hr1 34 (by omega)).trans hr34))) (by omega)
                  have hv := Expr.eval_reg_of_eq (w := w) ((hr4 41 (by omega)).trans h41_1)
                  exact runs_store_iff.mpr ⟨qA + pK.2.length, x, ha, hv, rfl, rfl, by simp [Expr.size]⟩
                set st6 : State := { st5 with mem := Function.update st5.mem (qA + pK.2.length) x }
                have ha_t : Runs w p ω_run (Stmt.assign 34 (t2Add (.reg 34) (.const 1))) st6 .normal
                    { st6 with regs := Function.update st6.regs 34 (pK.2.length + 1) } 4 := by
                  have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr4 34 (by omega)).trans ((hr1 34 (by omega)).trans hr34)))
                    (Expr.eval_const hw1) (by omega)
                  exact runs_assign_iff.mpr ⟨pK.2.length + 1, ha, rfl, rfl, by simp [Expr.size]⟩
                set st7 : State := { st6 with regs := Function.update st6.regs 34 (pK.2.length + 1) }
                have hc_inner : Runs w p ω_run innerIf2 st4 .normal
                    st7 (5 + (5 + 1 + (5 + 1 + 4)) + 1) :=
                  runs_cond_iff.mpr ⟨1, 5 + 1 + (5 + 1 + 4), hc_t,
                    runs_seq_iff.mpr (Or.inr ⟨st5, 5, 5 + 1 + 4, hp_t,
                      runs_seq_iff.mpr (Or.inr ⟨st6, 5, 4, hq_t, ha_t, rfl⟩), rfl⟩),
                    by simp [Expr.size]⟩
                have hc_outer : Runs w p ω_run innerIf1
                    st4 .normal st7 (6 + (5 + (5 + 1 + (5 + 1 + 4)) + 1) + 1) :=
                  runs_cond_iff.mpr ⟨1, 5 + (5 + 1 + (5 + 1 + 4)) + 1, hc_p1, hc_inner, by simp [Expr.size]⟩
                have hf_eq : foldK (k + 1) = (insert x pK.1, pK.2 ++ [x]) := by
                  rw [hstep_fold]; simp [hx_in, hnp, hth_le]
                refine ⟨st7, _, hc_outer, by omega, fun r hr hne => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · dsimp only [st7, st6, st5]; rw [Function.update_of_ne hne]
                · simp [st7, hf_eq]
                · intro a ha; dsimp only [st7, st6, st5]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst4_agr a ha]
                · intro y hy; rw [hf_eq] at hy ⊢; simp only [List.toFinset_append, List.toFinset_cons,
                    List.toFinset_nil, insert_empty_eq, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hy ⊢
                  rcases hy with hy | rfl
                  · exact Or.inr (hF2_sub hy)
                  · exact Or.inl rfl
                · rw [hf_eq]; exact List.nodup_append.mpr ⟨hF2_nd, List.nodup_singleton x,
                    fun a ha1 b hb2 hab => by simp at hb2; subst hb2; exact absurd (hab ▸ ha1) hx_n2⟩
                · intro y; rw [hf_eq]; simp only [List.mem_append, List.mem_singleton, Finset.mem_insert]
                  constructor
                  · rintro (hy | rfl)
                    · obtain ⟨h1, h2, h3⟩ := (hF2_spec y).mp hy; exact ⟨Or.inr h1, h2, h3⟩
                    · exact ⟨Or.inl rfl, hnp, hth_le⟩
                  · rintro ⟨rfl | hy1, h2, h3⟩
                    · exact Or.inr rfl
                    · exact Or.inl ((hF2_spec y).mpr ⟨hy1, h2, h3⟩)
                · intro y hy; rw [hf_eq]; dsimp only [st7, st6, st5]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst4_ew y hy]
                · intro y hy; rw [hf_eq]; dsimp only [st7, st6, st5]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst4_vc y hy]
                · intro y hy; rw [hf_eq]; dsimp only [st7, st6, st5]
                  rw [Function.update_of_ne (by omega)]
                  by_cases hyx : y = x
                  · subst hyx; rw [Function.update_self]; simp
                  · rw [Function.update_of_ne (by omega), hst4_ps y hy]; simp [hyx]
                · intro idx hidx; simp only [hf_eq] at hidx ⊢
                  dsimp only [st7, st6, st5]
                  by_cases hlast : idx = pK.2.length
                  · subst hlast; rw [Function.update_self]; simp
                  · have hidx_lt : idx < pK.2.length := by simp [List.length_append] at hidx; omega
                    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst4_q idx hidx_lt]
                    exact (List.getElem_append_left hidx_lt).symm
              · have hc_f : (t2Le (.reg 31) (.reg 42)).eval w st4 = some 0 := by simpa [hth_le] using hle_eval
                have hc_inner : Runs w p ω_run innerIf2 st4 .normal st4 (5 + 1 + 1) :=
                  runs_cond_iff.mpr ⟨0, 1, hc_f, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
                have hc_outer : Runs w p ω_run innerIf1 st4 .normal st4 (6 + (5 + 1 + 1) + 1) :=
                  runs_cond_iff.mpr ⟨1, 5 + 1 + 1, hc_p1, hc_inner, by simp [Expr.size]⟩
                have hf_eq : foldK (k + 1) = (insert x pK.1, pK.2) := by
                  rw [hstep_fold]; simp [hx_in, hnp, hth_le]
                refine ⟨st4, _, hc_outer, by omega, fun _ _ _ => rfl, ?_, hst4_agr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · rw [hf_eq]; exact (hr4 34 (by omega)).trans ((hr1 34 (by omega)).trans hr34)
                · rw [hf_eq]; exact Finset.Subset.trans hF2_sub (Finset.subset_insert _ _)
                · rw [hf_eq]; exact hF2_nd
                · intro y; rw [hf_eq]; simp only [Finset.mem_insert]
                  constructor
                  · intro hy; obtain ⟨h1, h2, h3⟩ := (hF2_spec y).mp hy; exact ⟨Or.inr h1, h2, h3⟩
                  · rintro ⟨rfl | hy1, h2, h3⟩
                    · exact absurd h3 hth_le
                    · exact (hF2_spec y).mpr ⟨hy1, h2, h3⟩
                · intro y hy; rw [hf_eq]; exact hst4_ew y hy
                · intro y hy; rw [hf_eq]; exact hst4_vc y hy
                · intro y hy; rw [hf_eq]; exact hst4_ps y hy
                · intro idx hidx; simp only [hf_eq] at hidx ⊢; exact hst4_q idx hidx
            · have hc_p0 : (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)).eval w st4 = some 0 := by
                simpa [hnp] using hps_cond
              have hc_outer : Runs w p ω_run innerIf1 st4 .normal st4 (6 + 1 + 1) :=
                runs_cond_iff.mpr ⟨0, 1, hc_p0, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
              have hf_eq : foldK (k + 1) = (insert x pK.1, pK.2) := by
                rw [hstep_fold]; simp [hx_in, hnp]
              refine ⟨st4, _, hc_outer, by omega, fun _ _ _ => rfl, ?_, hst4_agr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hf_eq]; exact (hr4 34 (by omega)).trans ((hr1 34 (by omega)).trans hr34)
              · rw [hf_eq]; exact Finset.Subset.trans hF2_sub (Finset.subset_insert _ _)
              · rw [hf_eq]; exact hF2_nd
              · intro y; rw [hf_eq]; simp only [Finset.mem_insert]
                constructor
                · intro hy; obtain ⟨h1, h2, h3⟩ := (hF2_spec y).mp hy; exact ⟨Or.inr h1, h2, h3⟩
                · rintro ⟨rfl | hy1, h2, h3⟩
                  · exact absurd h2 hnp
                  · exact (hF2_spec y).mpr ⟨hy1, h2, h3⟩
              · intro y hy; rw [hf_eq]; exact hst4_ew y hy
              · intro y hy; rw [hf_eq]; exact hst4_vc y hy
              · intro y hy; rw [hf_eq]; exact hst4_ps y hy
              · intro idx hidx; simp only [hf_eq] at hidx ⊢; exact hst4_q idx hidx
          rcases htail with ⟨stF, c_tail, hrt, hc_tail, hregsF, hr34F, hagrF, hF2_subF, hF2_ndF,
            hF2_specF, hewF, hvcF, hpsF, hqF⟩
          have hr_then : Runs w p ω_run innerThen st1 .normal stF (5 + 1 + 7 + 1 + 5 + 1 + c_tail) :=
            runs_seq_iff.mpr (Or.inr ⟨st2, 5, 7 + (5 + c_tail + 1) + 1, hs_ew,
              runs_seq_iff.mpr (Or.inr ⟨st3, 7, 5 + c_tail + 1, hs_42,
                runs_seq_iff.mpr (Or.inr ⟨st4, 5, c_tail, hs_vc, hrt, rfl⟩), rfl⟩), by omega⟩)
          have hr_cond : Runs w p ω_run innerCond st1 .normal stF
              (8 + (5 + 1 + 7 + 1 + 5 + 1 + c_tail) + 1) :=
            runs_cond_iff.mpr ⟨1, 5 + 1 + 7 + 1 + 5 + 1 + c_tail, hc_go, hr_then, by simp [Expr.size]⟩
          have hr_b : Runs w p ω_run body st .normal stF
              (7 + (8 + (5 + 1 + 7 + 1 + 5 + 1 + c_tail) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st1, 7, 8 + (5 + 1 + 7 + 1 + 5 + 1 + c_tail) + 1, hs1, hr_cond, rfl⟩)
          have hF1' : (foldK (k + 1)).1 = S_in ∪ ((inp.embJH eJ).verts.take (k + 1)).toFinset := by
            have : (foldK (k + 1)).1 = insert x pK.1 := by
              rw [hstep_fold]; split_ifs <;> rfl
            rw [this, hF1, htk_succ, Finset.union_insert]
          have hF1_sub' : (foldK (k + 1)).1 ⊆ Finset.range inp.H'.n := by
            intro y hy
            have : (foldK (k + 1)).1 = insert x pK.1 := by rw [hstep_fold]; split_ifs <;> rfl
            rw [this, Finset.mem_insert] at hy
            rcases hy with rfl | hy
            · exact Finset.mem_range.mpr hx_H
            · exact hF1_sub hy
          refine ⟨.normal, stF, _, hr_b,
            ⟨⟨fun r hr hne => by
                dsimp only
                rw [Function.update_of_ne (show r ≠ 40 by omega)]
                exact (hregsF r (by omega) hne).trans ((hr4 r (by omega)).trans ((hr1 r (by omega)).trans (hregs r hr hne))),
              by simp, hr34F, hagrF, hF1', hF1_sub', hF2_subF, hF2_ndF, hF2_specF, hewF, hvcF, hpsF, hqF⟩,
             (hregsF 40 (by omega) (by omega)).trans ((hr4 40 (by omega)).trans ((hr1 40 (by omega)).trans hr40))⟩,
            by dsimp only; omega⟩
    exact hfor.mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega
  obtain ⟨o, st', c_run, hr, hq, hc⟩ := htrip ⟨mem, hr_init, pos₀⟩ ω
    ⟨fun _ _ _ => rfl, hr34, fun _ _ => rfl, hm_ew, hm_vc, hm_ps, fun idx hidx => hm_q idx hidx⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hregs, _, hr34', hagr, hF1, hF1_sub, hF2_sub, hF2_nd, hF2_spec, hew, hvc, hps, hq_o⟩
    rw [List.take_of_length_le (le_refl _)] at hF1
    exact ⟨st', c_run, hr, hregs, hr34', hagr, hF1, hF1_sub, hF2_sub, hF2_nd, hF2_spec,
      hew, hvc, hps, hq_o, by omega⟩

end MinCostFlow.Spanner
