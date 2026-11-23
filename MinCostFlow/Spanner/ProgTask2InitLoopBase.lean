module

public import MinCostFlow.Spanner.ProgTask2SetupPreamble
public import MinCostFlow.Spanner.ProgTask2StepsMiddleBounds
public import MinCostFlow.Spanner.ProgTask2BuildInc
public import MinCostFlow.Spanner.ProgTask2

@[expose] public section

/-!
# Supporting Lemmas for Task 2 Round Initialization

Proves `t2_eta1Bound_le_eta1Cap`, `t2_maxWord_scalars`, `t2Init_loop_step`, and
`pathDS_nonempty_tau` used by `ProgTask2InitLoopProof` to prove `t2Round_init_loop_ptriple`.
-/

namespace MinCostFlow.Spanner

open WordRAM

lemma t2_eta1Bound_le_eta1Cap {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J := by
  unfold eta1Bound Task2Input.eta1Cap
  have hsc := ctx.wInp.mkWitnessData_scalars impl.constructExpander impl.pathDS.params ctx.WSubs ctx.hstat
  have hcdeg_eq : ctx.wd.c_deg = 2 * (impl.constructExpander.c_deg_int : ℝ) := by
    simp [WitnessCoreInput.mkWitnessData]
  have hφ_pos := impl.decompose.hφ_lb_pos (stripLoops inp.J).m
  have hφ_le : impl.decompose.φ_lb (stripLoops inp.J).m ≤ ctx.wd.φ_dec := by
    rw [← ctx.ds_bounds.2.2.2.1]
    simpa [WitnessCoreInput.mkWitnessData] using ctx.hφ_lb
  have hcdeg_nn : (0 : ℝ) ≤ ctx.wd.c_deg := by
    have := ctx.hw_okW.c_deg_ge; linarith
  have hdiv : ctx.wd.c_deg * (inp.J.m : ℝ) / (2 * ctx.wd.φ_dec) ≤
      2 * (impl.constructExpander.c_deg_int : ℝ) * (inp.J.m : ℝ) /
        (2 * impl.decompose.φ_lb (stripLoops inp.J).m) := by
    rw [hcdeg_eq]
    exact div_le_div₀ (by positivity) le_rfl (by positivity) (by linarith)
  have hlog := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (Nat.ceil_mono hdiv) 1)
  dsimp only
  rw [hcdeg_eq] at hlog ⊢
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)) 1

lemma t2_maxWord_scalars {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) :
    let mW := ctx.wd.W.m
    let K := ctx.wd.comps.length
    inp.v1 + 32 ≤ stc.dsBaseAddr ∧
    inp.dsHandlesAddr mW + K ≤ stc.dsBaseAddr ∧
    ctx.wInp.prep.aComps + 7 * K < 2 ^ w ∧
    inp.v1 + 32 < 2 ^ w ∧
    ctx.wInp.prep.phiNum_dec < 2 ^ w ∧
    ctx.wInp.prep.phiDen_dec < 2 ^ w ∧
    ctx.wd.J0_strip.m < 2 ^ w ∧
    Task2Input.eta1Cap impl inp.J * inp.J.m < 2 ^ w ∧
    Task2Input.eta1Cap impl inp.J * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
      ctx.wInp.prep.phiDen_dec < 2 ^ w ∧
    Task2Input.eta1Cap impl inp.J < 2 ^ w := by
  have db := drain_bounds ctx stc
  have hv1_ds : inp.v1 + 32 ≤ stc.dsBaseAddr := by
    have h1 := le_trans db.e_v1.le (le_trans (Nat.le_add_right _ _) db.e_emb.le)
    have h2 := le_trans h1 (le_trans (Nat.le_add_right _ _) db.e_hdl.le)
    have h3 := le_trans h2 (le_trans (Nat.le_add_right _ _) db.e_ceb.le)
    have h4 := le_trans h3 (le_trans (Nat.le_add_right _ _) db.e_vho.le)
    have h5 := le_trans h4 (le_trans (Nat.le_add_right _ _) db.e_del.le)
    have h6 := le_trans h5 (le_trans (Nat.le_add_right _ _) db.e_vh.le)
    have h7 := le_trans h6 (le_trans (Nat.le_add_right _ _) db.e_vhd.le)
    have h8 := le_trans h7 (le_trans (Nat.le_add_right _ _) db.e_vc.le)
    have h9 := le_trans h8 (le_trans (Nat.le_add_right _ _) db.e_ps.le)
    have h10 := le_trans h9 (le_trans (Nat.le_add_right _ _) db.e_ew.le)
    have h11 := le_trans h10 (le_trans (Nat.le_add_right _ _) db.e_q.le)
    exact le_trans h11 (le_trans db.h_nlo (Nat.le_add_right _ _))
  have hdl_ds : inp.dsHandlesAddr ctx.wd.W.m + ctx.wd.comps.length ≤ stc.dsBaseAddr := by
    have h2 := db.e_hdl.le
    have h3 := le_trans h2 (le_trans (Nat.le_add_right _ _) db.e_ceb.le)
    have h4 := le_trans h3 (le_trans (Nat.le_add_right _ _) db.e_vho.le)
    have h5 := le_trans h4 (le_trans (Nat.le_add_right _ _) db.e_del.le)
    have h6 := le_trans h5 (le_trans (Nat.le_add_right _ _) db.e_vh.le)
    have h7 := le_trans h6 (le_trans (Nat.le_add_right _ _) db.e_vhd.le)
    have h8 := le_trans h7 (le_trans (Nat.le_add_right _ _) db.e_vc.le)
    have h9 := le_trans h8 (le_trans (Nat.le_add_right _ _) db.e_ps.le)
    have h10 := le_trans h9 (le_trans (Nat.le_add_right _ _) db.e_ew.le)
    have h11 := le_trans h10 (le_trans (Nat.le_add_right _ _) db.e_q.le)
    exact le_trans h11 (le_trans db.h_nlo (Nat.le_add_right _ _))
  have hds_w : stc.dsBaseAddr < 2 ^ w :=
    lt_of_le_of_lt (le_trans db.h_dsc (le_trans db.h_stc db.h_mhe)) db.h_mwb
  rcases t2_prep_chain_bounds ctx with ⟨_, _, hpc3, hpc4⟩
  have hdsb := ctx.ds_bounds
  have hpd_cap : ctx.wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J := by
    unfold Task1Input.phiDenCap; rw [← hdsb.2.2.2.1]; exact ctx.hφ_cap
  have hmwb := ctx.hww.2.2
  have htau_cap := ctx.tau1Int_le_cap
  have hmw_ge1 : 1 ≤ Task1Input.mwCap impl inp.J := by unfold Task1Input.mwCap; omega
  have hdeg_ge1 : 1 ≤ vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1 := by omega
  have hm_eta : Task2Input.eta1Cap impl inp.J * inp.J.m < 2 ^ w := by
    have h1 : Task2Input.eta1Cap impl inp.J * inp.J.m ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
    exact lt_of_le_of_lt h1 hmwb
  have htau_bd : Task2Input.eta1Cap impl inp.J *
      ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec < 2 ^ w := by
    have hmul2 : Task2Input.eta1Cap impl inp.J *
        ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec ≤
        Task2Input.maxWordBound impl inp := by
      refine le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ htau_cap) hpd_cap) ?_
      unfold Task2Input.maxWordBound
      exact le_max_of_le_right (le_max_of_le_left
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    exact lt_of_le_of_lt hmul2 hmwb
  have hm0_le : ctx.wd.J0_strip.m ≤ inp.J.m := by
    rw [hdsb.2.2.2.1]; exact stripLoops_m_le inp.J
  have hη_ge1 : 1 ≤ Task2Input.eta1Cap impl inp.J := by
    unfold Task2Input.eta1Cap; exact Nat.le_add_right 1 _
  have hm_lt_w : inp.J.m < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_trans (by simpa using Nat.mul_le_mul_right inp.J.m hη_ge1) le_rfl) hm_eta
  have hdJ_ge1 : 1 ≤ Task1Input.dJCap impl inp.J :=
    Nat.one_le_ceil_iff.mpr (div_pos one_pos (impl.decompose.hφ_lb_pos _))
  have hpo_ge1 : 1 ≤ impl.pathDS.params.phiOutDen (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m := by
    have := impl.pathDS.params.hphiOutDen_ge _ (stripLoops inp.J).m hdJ_ge1; omega
  have hge_ge1 : 1 ≤ Task2Input.gammaExpCap impl inp.J := by
    have := impl.pathDS.params.hgExp_ge _ (stripLoops inp.J).m hdJ_ge1
    exact le_trans (le_trans hpo_ge1 this) (le_max_left _ _)
  have hgd_ge1 : 1 ≤ impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m :=
    impl.pathDS.params.hgDel_ge _ (stripLoops inp.J).m hdJ_ge1
  let τ₁Cap := 2 * Task2Input.gammaExpCap impl inp.J *
      max (impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
        (impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J)) *
      max (impl.pathDS.params.phiOutDen (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
        (impl.pathDS.params.phiOutDen (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J)) *
      (length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)
  have hτcap_pos : 1 ≤ τ₁Cap :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hge_ge1)
      (le_max_of_le_left hgd_ge1)) (le_max_of_le_left hpo_ge1))
      (Nat.succ_pos _)) (Nat.succ_pos _)
  have hpd_w : ctx.wInp.prep.phiDen_dec < 2 ^ w := by
    have hmul_p : Task1Input.phiDenCap impl inp.J ≤ Task2Input.maxWordBound impl inp := by
      have h1 : Task1Input.phiDenCap impl inp.J ≤
          Task2Input.eta1Cap impl inp.J * τ₁Cap * Task1Input.phiDenCap impl inp.J := by
        calc Task1Input.phiDenCap impl inp.J = 1 * 1 * Task1Input.phiDenCap impl inp.J := by simp
          _ ≤ Task2Input.eta1Cap impl inp.J * τ₁Cap * Task1Input.phiDenCap impl inp.J :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hη_ge1 hτcap_pos)
      unfold Task2Input.maxWordBound
      exact le_max_of_le_right (le_max_of_le_left
        (le_trans h1 (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
    exact lt_of_le_of_lt (le_trans hpd_cap hmul_p) hmwb
  have hη_w : Task2Input.eta1Cap impl inp.J < 2 ^ w := by
    have hpd_cap_pos : 1 ≤ Task1Input.phiDenCap impl inp.J :=
      le_trans (le_trans hdsb.2.2.2.2.1 hdsb.2.2.2.2.2.1) hpd_cap
    have h1 : Task2Input.eta1Cap impl inp.J ≤ Task2Input.maxWordBound impl inp := by
      have hmul : Task2Input.eta1Cap impl inp.J ≤
          Task2Input.eta1Cap impl inp.J * τ₁Cap * Task1Input.phiDenCap impl inp.J := by
        calc Task2Input.eta1Cap impl inp.J = Task2Input.eta1Cap impl inp.J * 1 * 1 := by simp
          _ ≤ Task2Input.eta1Cap impl inp.J * τ₁Cap * Task1Input.phiDenCap impl inp.J :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hτcap_pos) hpd_cap_pos
      unfold Task2Input.maxWordBound
      exact le_max_of_le_right (le_max_of_le_left
        (le_trans hmul (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
    exact lt_of_le_of_lt h1 hmwb
  have hv1_w : inp.v1 + 32 < 2 ^ w := (t2SetupHdr_word_bounds ctx).2.2.2.2.2.2.2.1
  refine ⟨hv1_ds, hdl_ds, ?_, hv1_w, ?_, hpd_w, ?_, hm_eta, htau_bd, hη_w⟩
  · exact lt_of_le_of_lt (le_trans hpc3 (le_trans hpc4 (Nat.le_add_right inp.v1 32))) hv1_w
  · exact lt_of_le_of_lt hdsb.2.2.2.2.2.1 hpd_w
  · exact lt_of_le_of_lt hm0_le hm_lt_w

def t2InitBody (dsBase : ℕ) : Stmt :=
  Stmt.assign 21 (t2Add (.reg 31) (t2Mul (.const 7) (.reg 20))) ;;
  Stmt.assign 22 (t2Ld (.reg 21) (.const 3)) ;;
  Stmt.assign 23 (t2Ld (.reg 21) (.const 6)) ;;
  t2St (.reg 4) (.const 3) (t2Add (t2Ld (.reg 4) (.const 3)) (.reg 23)) ;;
  t2St (.reg 36) (.reg 20) (.reg 18) ;;
  Stmt.call 18 dsBase [.reg 22, .reg 33, .reg 34, .reg 35, .reg 18]

def sumCompEdgesUpTo (comps : List CompInfo) (upTo : ℕ) : ℕ :=
  ((comps.take upTo).map fun c => c.J_sub.m).sum

lemma sumCompEdgesUpTo_succ {comps : List CompInfo} {i : ℕ} (hi : i < comps.length) :
    sumCompEdgesUpTo comps (i + 1) = sumCompEdgesUpTo comps i + comps[i].J_sub.m := by
  unfold sumCompEdgesUpTo
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

lemma sumCompEdgesUpTo_le_J {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (upTo : ℕ) :
    sumCompEdgesUpTo ctx.wd.comps upTo ≤ inp.J.m := by
  have h1 : sumCompEdgesUpTo ctx.wd.comps upTo ≤ (ctx.wd.comps.map fun c => c.J_sub.m).sum := by
    have hsub := (ctx.wd.comps.take_append_drop upTo).symm
    have hsum : (ctx.wd.comps.map fun c => c.J_sub.m).sum =
        sumCompEdgesUpTo ctx.wd.comps upTo + ((ctx.wd.comps.drop upTo).map fun c => c.J_sub.m).sum := by
      conv_lhs => rw [hsub, List.map_append, List.sum_append]
      rfl
    omega
  have h2 := ctx.hWInpJ ▸ mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
  change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m at h2
  omega

structure T2InitLoopInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (r_done : ℕ)
    (mem_hdr : ℕ → ℕ) (hCur0 del0 gp0 : ℕ) (upTo : ℕ)
    (hCur : ℕ) (states : ℕ → PathDSAbsState) (reps : ℕ → impl.pathDS.R.τ)
    (st : State) (Φ : ℕ) : Prop where
  hr4 : st.regs 4 = inp.v1
  hr10 : st.regs 10 = ctx.wd.comps.length
  hr12 : st.regs 12 = ctx.wd.W.m
  hr20 : st.regs 20 = upTo
  hr31 : st.regs 31 = ctx.wInp.prep.aComps
  hr32 : st.regs 32 = mem_hdr (ctx.wInp.h + 12)
  hr33 : st.regs 33 = ctx.wInp.prep.phiNum_dec
  hr34 : st.regs 34 = ctx.wInp.prep.phiDen_dec
  hr35 : st.regs 35 = ctx.wd.J0_strip.m
  hr36 : st.regs 36 = inp.dsHandlesAddr ctx.wd.W.m
  hr37 : st.regs 37 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length
  hr38 : st.regs 38 = inp.embWJAddr
  hr39 : st.regs 39 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length
  hr40 : st.regs 40 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec
  hr41 : st.regs 41 = r_done + 1
  hr18 : st.regs 18 = hCur
  hCur_lo : hCur0 ≤ hCur
  hCur_le : hCur ≤ stc.dsBaseAddr + (r_done * ctx.wd.comps.length + upTo + del0 + gp0) * t2DsOne impl inp.J
  h3 : st.mem (inp.v1 + 3) = r_done * (ctx.wd.comps.map fun c => c.J_sub.m).sum + sumCompEdgesUpTo ctx.wd.comps upTo
  hframe : ∀ a < stc.dsBaseAddr, a ≠ inp.v1 + 3 →
    (∀ ci < upTo, a ≠ inp.dsHandlesAddr ctx.wd.W.m + ci) → st.mem a = mem_hdr a
  hDS : DSArrayAt impl.pathDS ctx.wd.comps ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
    ctx.wd.J0_strip.m w stc.dsBaseAddr (inp.dsHandlesAddr ctx.wd.W.m) hCur st.mem upTo states reps
  hEmpty : ∀ ci < upTo, (states ci).Vhat = ∅ ∧ (states ci).deleted = ∅
  hΦ : Φ = dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) upTo reps st.mem

def T2InitLoopState {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (r_done : ℕ)
    (mem_hdr : ℕ → ℕ) (hCur0 del0 gp0 : ℕ) (upTo : ℕ) (st : State) (Φ : ℕ) : Prop :=
  ∃ (hCur : ℕ) (states : ℕ → PathDSAbsState) (reps : ℕ → impl.pathDS.R.τ),
    T2InitLoopInv ctx stc r_done mem_hdr hCur0 del0 gp0 upTo hCur states reps st Φ

private lemma t2_heapCur_le_maxHeapEnd {impl : SpannerToolImpl} {inp : Task2Input}
    {stcBase dsUsed : ℕ}
    (hBase : stcBase ≤ Task2Input.staticEndCap impl inp)
    (hUsed : dsUsed ≤ Task2Input.eta1Cap impl inp.J * inp.J.m +
      Task2Input.eta1Cap impl inp.J * inp.J.m + Task1Input.mwCap impl inp.J) :
    stcBase + dsUsed * t2DsOne impl inp.J ≤ Task2Input.maxHeapEnd impl inp := by
  unfold Task2Input.maxHeapEnd
  change stcBase + dsUsed * t2DsOne impl inp.J ≤ Task2Input.staticEndCap impl inp +
    Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
    Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
    Task1Input.mwCap impl inp.J * t2DsOne impl inp.J
  nlinarith

lemma t2Init_loop_step {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    {r_done : ℕ} {mem_hdr : ℕ → ℕ} {hCur0 del0 gp0 ci : ℕ}
    (hEta : r_done + 1 ≤ Task2Input.eta1Cap impl inp.J)
    (hDel : del0 ≤ r_done * inp.J.m)
    (hGp : gp0 ≤ ctx.wd.W.m)
    (hAgr_hdr : ∀ x < inp.v1, mem_hdr x = mem₀ x)
    (hci : ci < ctx.wd.comps.length) :
    let γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
    PTriple w p
      (T2InitLoopState ctx stc r_done mem_hdr hCur0 del0 gp0 ci)
      (t2InitBody dsBase)
      (pNormalPost fun st₁ Φ₁ =>
        T2InitLoopState ctx stc r_done mem_hdr hCur0 del0 gp0 (ci + 1)
          { st₁ with regs := Function.update st₁.regs 20 (ci + 1) } Φ₁ ∧ st₁.regs 20 = ci)
      (fun _ => ctx.wd.comps[ci].J_sub.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 42) := by
  intro γJ st Φ ω hs0
  rcases hs0 with ⟨hCur, states, reps, hs⟩
  have db := drain_bounds ctx stc
  have hm := t2_maxWord_scalars ctx stc
  rcases hm with ⟨hv1_ds, hdl_ds, haComps_w, _hv1_w, hphiN_w, hphiD_w, hM_w, hm_eta, _, _⟩
  have hm_lt_w : inp.J.m < 2 ^ w := by
    have hη_ge1 : 1 ≤ Task2Input.eta1Cap impl inp.J := by
      unfold Task2Input.eta1Cap; exact Nat.le_add_right 1 _
    exact lt_of_le_of_lt (by simpa using Nat.mul_le_mul_right inp.J.m hη_ge1) hm_eta
  have haComps_lt : ctx.wInp.prep.aComps + 7 * ci + 6 < inp.v1 := by
    have h1 := (t2_prep_comp_ptrs_le ctx hci).1
    have h2 := (t2_prep_chain_bounds ctx).2.2.2
    omega
  have h1_lt : 2 ^ w > 1 := ctx.hww.1
  have hci_w : ci < 2 ^ w := by omega
  have h7ci_w : 7 * ci < 2 ^ w := by omega
  have haC_ci_w : ctx.wInp.prep.aComps + 7 * ci < 2 ^ w := by omega
  have haC_3_w : ctx.wInp.prep.aComps + 7 * ci + 3 < 2 ^ w := by omega
  have haC_6_w : ctx.wInp.prep.aComps + 7 * ci + 6 < 2 ^ w := by omega
  have hAgr_pre : ∀ x < inp.v1, st.mem x = mem₀ x := fun x hx =>
    (hs.hframe x (lt_of_lt_of_le hx (le_trans (Nat.le_add_right inp.v1 32) hv1_ds))
      (by omega) (fun k _ => by have := db.e_v1; have := db.e_emb; omega)).trans (hAgr_hdr x hx)
  have hstat_st := ctx.agrees_preserves_static hAgr_pre
  have hcdt := hstat_st.2.2.2.2.2.1
  have hlen_raw : ctx.wd.comps.length = ctx.wInp.prep.rawComps.length :=
    ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hci_raw : ci < ctx.wInp.prep.rawComps.length := hlen_raw ▸ hci
  have hcomp_ci := hcdt ci hci_raw
  have hc_bang : ctx.wInp.prep.rawComps[ci]! = ctx.wInp.prep.rawComps[ci] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci_raw, Option.getD_some]
  rw [hc_bang] at hcomp_ci
  have hJsub_eq := t2_prep_cJSub_m_eq ctx hci
  set c := ctx.wd.comps[ci]
  have hgAddr_eq : st.mem (ctx.wInp.prep.aComps + 7 * ci + 3) = ctx.wInp.prep.cJSubPtr ci :=
    hcomp_ci.2.2.2.1
  have hJm_eq : st.mem (ctx.wInp.prep.aComps + 7 * ci + 6) = c.J_sub.m := by
    simpa [c, hJsub_eq.1] using hcomp_ci.2.2.2.2.2.2.1
  have hG_at : GraphAt st.mem (ctx.wInp.prep.cJSubPtr ci) c.J_sub := by
    simpa [c, hJsub_eq.1] using hcomp_ci.2.2.2.2.2.2.2.1
  have hgAddr_end : ctx.wInp.prep.cJSubPtr ci + c.J_sub.encode.length ≤ inp.v1 := by
    have h1 := (t2_prep_comp_ptrs_le ctx hci).2
    have h2 := (t2_prep_chain_bounds ctx).2.2.2
    have hlen : c.J_sub.encode.length = 2 + 2 * c.J_sub.m := graph_encode_length c.J_sub
    have horig : ctx.wInp.prep.cJOrigPtr ci = ctx.wInp.prep.cJSubPtr ci + 2 + 2 * c.J_sub.m := by
      unfold PrepInput.cJOrigPtr
      rw [List.getD_eq_getElem _ _ hci_raw, ← hJsub_eq.1]
    omega
  have hgAddr_w : ctx.wInp.prep.cJSubPtr ci < 2 ^ w := by omega
  have hJm_w : c.J_sub.m < 2 ^ w := by
    have h1 := sumCompEdgesUpTo_le_J ctx (ci + 1)
    rw [sumCompEdgesUpTo_succ hci] at h1
    exact lt_of_le_of_lt (Nat.le_add_left _ _) (lt_of_le_of_lt h1 hm_lt_w)
  have he_init_sum : r_done * (ctx.wd.comps.map fun c => c.J_sub.m).sum +
      sumCompEdgesUpTo ctx.wd.comps ci + c.J_sub.m ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := by
    have hs1 : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m := by
      have h1 := ctx.hWInpJ ▸ mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
      change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m at h1
      omega
    have hs2 : sumCompEdgesUpTo ctx.wd.comps ci + c.J_sub.m ≤ inp.J.m := by
      rw [← sumCompEdgesUpTo_succ hci]; exact sumCompEdgesUpTo_le_J ctx (ci + 1)
    have h3 : r_done * inp.J.m + 1 * inp.J.m ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hEta
    nlinarith
  have he_sum_w : r_done * (ctx.wd.comps.map fun c => c.J_sub.m).sum +
      sumCompEdgesUpTo ctx.wd.comps ci + c.J_sub.m < 2 ^ w :=
    lt_of_le_of_lt he_init_sum hm_eta
  have hv1_3_w : inp.v1 + 3 < 2 ^ w := by omega
  have hdl_ci_w : inp.dsHandlesAddr ctx.wd.W.m + ci < 2 ^ w := by
    have hds_w : stc.dsBaseAddr < 2 ^ w :=
      lt_of_le_of_lt (le_trans db.h_dsc (le_trans db.h_stc db.h_mhe)) db.h_mwb
    omega
  have hmhe_w : Task2Input.maxHeapEnd impl inp < 2 ^ w :=
    lt_of_le_of_lt (by unfold Task2Input.maxWordBound; exact le_trans (Nat.le_add_right _ 3) (le_max_left _ _))
      ctx.hww.2.2
  have hCur_w : hCur < 2 ^ w := by
    have ha : r_done * ctx.wd.comps.length + ci ≤ (r_done + 1) * ctx.wd.comps.length := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left (le_of_lt hci) _
    have hb : (r_done + 1) * ctx.wd.comps.length ≤ Task2Input.eta1Cap impl inp.J * inp.J.m :=
      Nat.mul_le_mul hEta ctx.hK_le
    have hc : del0 ≤ Task2Input.eta1Cap impl inp.J * inp.J.m :=
      le_trans hDel (Nat.mul_le_mul_right _ (by omega))
    have hd : gp0 ≤ Task1Input.mwCap impl inp.J := le_trans hGp ctx.hmW_le
    have h1 := t2_heapCur_le_maxHeapEnd (dsUsed := r_done * ctx.wd.comps.length + ci + del0 + gp0)
      db.h_dsc (by omega)
    exact lt_of_le_of_lt (le_trans hs.hCur_le h1) hmhe_w
  have hds_bd := t2_ds_bounds ctx.hWInpJ ctx.hstat ctx.hw_okW ctx.hφ_cap ctx.hφ_lb ctx.hww
  have hc_bd := hds_bd.1 ci hci
  have hCur_space_w : hCur + impl.pathDS.params.initSpace ctx.wInp.prep.phiNum_dec
      ctx.wInp.prep.phiDen_dec c.J_sub.n c.J_sub.m ctx.wd.J0_strip.m < 2 ^ w := by
    have ha : r_done * ctx.wd.comps.length + ci + 1 ≤ (r_done + 1) * ctx.wd.comps.length := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left hci _
    have hb : (r_done + 1) * ctx.wd.comps.length ≤ Task2Input.eta1Cap impl inp.J * inp.J.m :=
      Nat.mul_le_mul hEta ctx.hK_le
    have hc : del0 ≤ Task2Input.eta1Cap impl inp.J * inp.J.m :=
      le_trans hDel (Nat.mul_le_mul_right _ (by omega))
    have hd : gp0 ≤ Task1Input.mwCap impl inp.J := le_trans hGp ctx.hmW_le
    have hcur1 : hCur + t2DsOne impl inp.J ≤
        stc.dsBaseAddr + (r_done * ctx.wd.comps.length + ci + del0 + gp0 + 1) * t2DsOne impl inp.J := by
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]; exact Nat.add_le_add hs.hCur_le le_rfl
    have h1 := le_trans hcur1 (t2_heapCur_le_maxHeapEnd
      (dsUsed := r_done * ctx.wd.comps.length + ci + del0 + gp0 + 1) db.h_dsc (by omega))
    exact lt_of_le_of_lt (le_trans (Nat.add_le_add_left hc_bd.1 _) h1) hmhe_w
  let s21 : State := { mem := st.mem, regs := Function.update st.regs 21 (ctx.wInp.prep.aComps + 7 * ci), pos := st.pos }
  have hr21 : Runs w p ω (Stmt.assign 21 (t2Add (.reg 31) (t2Mul (.const 7) (.reg 20)))) st .normal s21 6 := by
    have he := Expr.eval_add (Expr.eval_reg_of_eq hs.hr31)
      (Expr.eval_mul (Expr.eval_const (by omega : 7 < 2 ^ w)) (Expr.eval_reg_of_eq hs.hr20) h7ci_w) haC_ci_w
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, by simp [Expr.size]⟩
  let s22 : State := { mem := st.mem, regs := Function.update s21.regs 22 (ctx.wInp.prep.cJSubPtr ci), pos := st.pos }
  have hr22 : Runs w p ω (Stmt.assign 22 (t2Ld (.reg 21) (.const 3))) s21 .normal s22 5 := by
    have hr21_21 : s21.regs 21 = ctx.wInp.prep.aComps + 7 * ci := by
      dsimp only [s21]; exact Function.update_self _ _ _
    have he := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr21_21) (Expr.eval_const (by omega : 3 < 2 ^ w)) haC_3_w)
    rw [hgAddr_eq] at he
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, by simp [Expr.size]⟩
  let s23 : State := { mem := st.mem, regs := Function.update s22.regs 23 c.J_sub.m, pos := st.pos }
  have hr23 : Runs w p ω (Stmt.assign 23 (t2Ld (.reg 21) (.const 6))) s22 .normal s23 5 := by
    have hr22_21 : s22.regs 21 = ctx.wInp.prep.aComps + 7 * ci := by
      simp (disch := decide) only [s22, s21, Function.update_of_ne, Function.update_self]
    have he := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr22_21) (Expr.eval_const (by omega : 6 < 2 ^ w)) haC_6_w)
    rw [hJm_eq] at he
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, by simp [Expr.size]⟩
  let memA := Function.update st.mem (inp.v1 + 3)
    (r_done * (ctx.wd.comps.map fun c => c.J_sub.m).sum + sumCompEdgesUpTo ctx.wd.comps (ci + 1))
  let sA : State := { mem := memA, regs := s23.regs, pos := st.pos }
  have hrA : Runs w p ω (t2St (.reg 4) (.const 3) (t2Add (t2Ld (.reg 4) (.const 3)) (.reg 23))) s23 .normal sA 10 := by
    have hr23_4 : s23.regs 4 = inp.v1 := by
      simp (disch := decide) only [s23, s22, s21, Function.update_of_ne, hs.hr4]
    have hr23_23 : s23.regs 23 = c.J_sub.m := by
      dsimp only [s23]; exact Function.update_self _ _ _
    have he_a := Expr.eval_add (Expr.eval_reg_of_eq hr23_4) (Expr.eval_const (by omega : 3 < 2 ^ w)) hv1_3_w
    have he_ld := Expr.eval_load he_a
    change (t2Ld (.reg 4) (.const 3)).eval w s23 = some (st.mem (inp.v1 + 3)) at he_ld
    rw [hs.h3] at he_ld
    have he_v := Expr.eval_add he_ld (Expr.eval_reg_of_eq hr23_23) he_sum_w
    have he_v' : (t2Add (t2Ld (.reg 4) (.const 3)) (.reg 23)).eval w s23 =
        some (r_done * (ctx.wd.comps.map fun c => c.J_sub.m).sum + sumCompEdgesUpTo ctx.wd.comps (ci + 1)) := by
      simpa only [sumCompEdgesUpTo_succ hci, Nat.add_assoc] using he_v
    exact runs_store_iff.mpr ⟨inp.v1 + 3, _, he_a, he_v', rfl, rfl, by simp [Expr.size]⟩
  let memB := Function.update memA (inp.dsHandlesAddr ctx.wd.W.m + ci) hCur
  let sB : State := { mem := memB, regs := s23.regs, pos := st.pos }
  have hrB : Runs w p ω (t2St (.reg 36) (.reg 20) (.reg 18)) sA .normal sB 5 := by
    have hsA_36 : sA.regs 36 = inp.dsHandlesAddr ctx.wd.W.m := by
      simp (disch := decide) only [sA, s23, s22, s21, Function.update_of_ne, hs.hr36]
    have hsA_20 : sA.regs 20 = ci := by
      simp (disch := decide) only [sA, s23, s22, s21, Function.update_of_ne, hs.hr20]
    have hsA_18 : sA.regs 18 = hCur := by
      simp (disch := decide) only [sA, s23, s22, s21, Function.update_of_ne, hs.hr18]
    have he_a := Expr.eval_add (Expr.eval_reg_of_eq hsA_36) (Expr.eval_reg_of_eq hsA_20) hdl_ci_w
    exact runs_store_iff.mpr ⟨inp.dsHandlesAddr ctx.wd.W.m + ci, hCur, he_a,
      Expr.eval_reg_of_eq hsA_18, rfl, rfl, by simp [Expr.size]⟩
  have hDS_B_phi := hs.hDS.frame_range hSpec.1 (mem' := memB)
    (fun k hk => by
      have hne1 : inp.dsHandlesAddr ctx.wd.W.m + k ≠ inp.dsHandlesAddr ctx.wd.W.m + ci := by omega
      have hne2 : inp.dsHandlesAddr ctx.wd.W.m + k ≠ inp.v1 + 3 := by
        have := db.e_v1; have := db.e_emb; omega
      simp only [memB, memA, Function.update_of_ne hne1, Function.update_of_ne hne2])
    (fun a ha1 _ => by
      have hds_a : stc.dsBaseAddr ≤ a := ha1
      have hne1 : a ≠ inp.dsHandlesAddr ctx.wd.W.m + ci := by omega
      have hne2 : a ≠ inp.v1 + 3 := by omega
      simp only [memB, memA, Function.update_of_ne hne1, Function.update_of_ne hne2])
    (fun a ha => by
      have hds_a : stc.dsBaseAddr ≤ a := le_trans hs.hDS.h_ge ha
      have hne1 : a ≠ inp.dsHandlesAddr ctx.wd.W.m + ci := by omega
      have hne2 : a ≠ inp.v1 + 3 := by omega
      simp only [memB, memA, Function.update_of_ne hne1, Function.update_of_ne hne2]
      exact hs.hDS.zero_from a ha)
  have hG_at_B : GraphAt memB (ctx.wInp.prep.cJSubPtr ci) c.J_sub := fun i hi => by
    have hlt_v1 : ctx.wInp.prep.cJSubPtr ci + i < inp.v1 := lt_of_lt_of_le (Nat.add_lt_add_left hi _) hgAddr_end
    have hne1 : ctx.wInp.prep.cJSubPtr ci + i ≠ inp.dsHandlesAddr ctx.wd.W.m + ci := by
      have := db.e_v1; have := db.e_emb; omega
    have hne2 : ctx.wInp.prep.cJSubPtr ci + i ≠ inp.v1 + 3 := by omega
    simpa [memB, memA, hne1, hne2] using hG_at i hi
  have hcprops := ctx.hw_okW.comp_props ci hci
  have hgAddr_end_cur : ctx.wInp.prep.cJSubPtr ci + c.J_sub.encode.length ≤ hCur :=
    le_trans hgAddr_end (le_trans (Nat.le_add_right inp.v1 32) (le_trans hv1_ds (le_trans hs.hDS.h_ge le_rfl)))
  have hstep_init := hDS_B_phi.1.step_init (pos := st.pos) (ω := ω) hSpec hci (by exact hdl_ds) hgAddr_w hphiN_w hphiD_w hM_w hCur_w
    hgAddr_end_cur hG_at_B hds_bd.2.2.2.2.1 hds_bd.2.2.2.2.2.1 hcprops.2.2.2.2.2.2.1 hcprops.2.2.2.2.2.2.2.1
    hcprops.2.2.2.2.2.2.2.2.1 (fun v hv => hcprops.2.2.2.2.2.2.2.2.2.1 v (hcprops.2.2.2.2.2.1 ▸ hv))
    hcprops.2.2.2.2.2.2.2.2.2.2.1 hc_bd.2.2.2.1 hCur_space_w
  rcases hstep_init with ⟨body, o_ds, st_ds, c_ds, s', x', hbody, hruns_ds, ho_le, ho_ge,
    hst_ds_lt, hs'_vh, hs'_del, hDS', hPhi_ds⟩
  set hCur' := o_ds.value
  have h_upd_eq : Function.update st_ds.mem (inp.dsHandlesAddr ctx.wd.W.m + ci) hCur = st_ds.mem := by
    ext a
    by_cases ha : a = inp.dsHandlesAddr ctx.wd.W.m + ci
    · subst ha
      have hge := hs.hDS.h_ge
      rw [Function.update_self, hst_ds_lt _ (by omega)]
      simp only [memB, Function.update_self]
    · rw [Function.update_of_ne ha]
  rw [h_upd_eq] at hDS' hPhi_ds
  let s18 : State := { mem := st_ds.mem, regs := Function.update sB.regs 18 hCur', pos := st_ds.pos }
  have hr_c18 : Runs w p ω (Stmt.call 18 dsBase [.reg 22, .reg 33, .reg 34, .reg 35, .reg 18])
      sB .normal s18 (5 + c_ds + 1) := by
    have hb22 : sB.regs 22 = ctx.wInp.prep.cJSubPtr ci := by
      simp (disch := decide) only [sB, s23, s22, Function.update_of_ne, Function.update_self]
    have hb33 : sB.regs 33 = ctx.wInp.prep.phiNum_dec := by
      simp (disch := decide) only [sB, s23, s22, s21, Function.update_of_ne, hs.hr33]
    have hb34 : sB.regs 34 = ctx.wInp.prep.phiDen_dec := by
      simp (disch := decide) only [sB, s23, s22, s21, Function.update_of_ne, hs.hr34]
    have hb35 : sB.regs 35 = ctx.wd.J0_strip.m := by
      simp (disch := decide) only [sB, s23, s22, s21, Function.update_of_ne, hs.hr35]
    have hb18 : sB.regs 18 = hCur := by
      simp (disch := decide) only [sB, s23, s22, s21, Function.update_of_ne, hs.hr18]
    refine runs_call_iff.mpr
      ⟨[ctx.wInp.prep.cJSubPtr ci, ctx.wInp.prep.phiNum_dec, ctx.wInp.prep.phiDen_dec,
        ctx.wd.J0_strip.m, hCur], body, o_ds, st_ds, c_ds, ?_, hbody, hruns_ds,
        rfl, rfl, by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval_reg_of_eq hb22, Expr.eval_reg_of_eq hb33,
      Expr.eval_reg_of_eq hb34, Expr.eval_reg_of_eq hb35, Expr.eval_reg_of_eq hb18]
  have hrun_tot := runs_seq_iff.mpr (Or.inr ⟨s21, 6, _, hr21,
    runs_seq_iff.mpr (Or.inr ⟨s22, 5, _, hr22,
      runs_seq_iff.mpr (Or.inr ⟨s23, 5, _, hr23,
        runs_seq_iff.mpr (Or.inr ⟨sA, 10, _, hrA,
          runs_seq_iff.mpr (Or.inr ⟨sB, 5, _, hrB, hr_c18, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  let stOut := { s18 with regs := Function.update s18.regs 20 (ci + 1) }
  have hinv_next : T2InitLoopInv ctx stc r_done mem_hdr hCur0 del0 gp0 (ci + 1) hCur'
      (Function.update states ci s') (Function.update reps ci x') stOut
      (dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) (ci + 1)
        (Function.update reps ci x') st_ds.mem) :=
    { hr4 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr4]
      hr10 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr10]
      hr12 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr12]
      hr20 := by dsimp only [stOut]; exact Function.update_self _ _ _
      hr31 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr31]
      hr32 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr32]
      hr33 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr33]
      hr34 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr34]
      hr35 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr35]
      hr36 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr36]
      hr37 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr37]
      hr38 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr38]
      hr39 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr39]
      hr40 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr40]
      hr41 := by simp (disch := decide) only [stOut, s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr41]
      hr18 := by simp (disch := decide) only [stOut, s18, Function.update_of_ne, Function.update_self]
      hCur_lo := le_trans hs.hCur_lo ho_ge
      hCur_le := by
        have hsp1 : impl.pathDS.params.initSpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
            c.J_sub.n c.J_sub.m ctx.wd.J0_strip.m ≤ t2DsOne impl inp.J := hc_bd.1
        have ho' : hCur' ≤ hCur + t2DsOne impl inp.J := le_trans ho_le (Nat.add_le_add_left hsp1 _)
        have hmul : (r_done * ctx.wd.comps.length + (ci + 1) + del0 + gp0) * t2DsOne impl inp.J =
            (r_done * ctx.wd.comps.length + ci + del0 + gp0) * t2DsOne impl inp.J + t2DsOne impl inp.J := by ring
        rw [hmul, ← Nat.add_assoc]
        exact le_trans ho' (Nat.add_le_add_right hs.hCur_le _)
      h3 := by
        have hge := hs.hDS.h_ge
        change st_ds.mem (inp.v1 + 3) = _
        rw [hst_ds_lt _ (by omega : inp.v1 + 3 < hCur)]
        have hne : inp.v1 + 3 ≠ inp.dsHandlesAddr ctx.wd.W.m + ci := by
          have := db.e_v1; have := db.e_emb; omega
        simp only [memB, memA, Function.update_of_ne hne, Function.update_self]
      hframe := fun a ha h3 hdl => by
        have ha_cur : a < hCur := lt_of_lt_of_le ha hs.hDS.h_ge
        change st_ds.mem a = mem_hdr a
        rw [hst_ds_lt a ha_cur]
        have hne_ci : a ≠ inp.dsHandlesAddr ctx.wd.W.m + ci := hdl ci (Nat.lt_succ_self ci)
        simp only [memB, memA, Function.update_of_ne hne_ci, Function.update_of_ne h3]
        exact hs.hframe a ha h3 fun k hk => hdl k (Nat.lt_succ_of_lt hk)
      hDS := hDS'
      hEmpty := fun k hk => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
        · simp [Function.update_of_ne (Nat.ne_of_lt hk'), hs.hEmpty k hk']
        · simp [Function.update_self, hs'_vh, hs'_del]
      hΦ := rfl }
  have hs18_20 : s18.regs 20 = ci := by
    simp (disch := decide) only [s18, sB, s23, s22, s21, Function.update_of_ne, hs.hr20]
  have hcost_le : (6 + (5 + (5 + (10 + (5 + (5 + c_ds + 1) + 1) + 1) + 1) + 1) + 1) +
      dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) (ci + 1)
        (Function.update reps ci x') st_ds.mem ≤
      (c.J_sub.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 42) + Φ := by
    rw [hs.hΦ, ← hDS_B_phi.2]
    have hceil : ⌈impl.pathDS.params.K_init * (c.J_sub.m : ℝ) *
        impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ))
          ctx.wd.J0_strip.m⌉₊ ≤
        c.J_sub.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ := hc_bd.2.2.2.2
    dsimp only [c] at hceil ⊢
    omega
  exact ⟨.normal, s18, _, _, hrun_tot, ⟨⟨hCur', _, _, hinv_next⟩, hs18_20⟩, hcost_le⟩

lemma t2Round_init_cost_arith {m K KinitGamma c_f Φ_f rc : ℕ}
    (hK : K ≤ m) (hrc : rc ≤ m * KinitGamma + 42 * m) (hcf : c_f + Φ_f ≤ rc + K * 9 + 7) :
    (7 + (5 + (7 + (10 + c_f + 1) + 1) + 1) + 1) + Φ_f ≤ m * KinitGamma + 52 * m + 45 := by
  nlinarith

lemma pathDS_nonempty_tau (pds : PathDSImpl) : Nonempty pds.R.τ := by
  let G : Cited.Graph := ⟨1, [(0, 0)]⟩
  let φ_r : ℝ := (1 : ℝ) / (1 : ℝ)
  let M_val : ℕ := 1
  let wBig := pds.params.cw * (Nat.log 2 (G.n + G.m + 1 + M_val +
    Nat.ceil (pds.params.γ_ExpPath φ_r M_val) + 2) + 1) +
    4 + pds.params.initSpace 1 1 G.n G.m M_val + 4
  have hBig_lt : 4 + pds.params.initSpace 1 1 G.n G.m M_val < 2 ^ wBig :=
    lt_of_lt_of_le (by omega) (le_of_lt (Nat.lt_two_pow_self (n := wBig)))
  let pBig : Program := { procs := pds.procs 0 }
  have hHas : pBig.HasAt 0 (pds.procs 0) := fun i hi => by simp [pBig, hi]
  have hSpec := pds.spec wBig pBig 0 hHas
  let memBig : ℕ → ℕ := fun i => G.encode.getD i 0
  have hArgs : ∀ a ∈ ([0, 1, 1, 1, 4] : List ℕ), a < 2 ^ wBig := fun a ha => by
    have ha4 : a ≤ 4 := by simp at ha; omega
    exact lt_of_le_of_lt (le_trans ha4 (Nat.le_add_right _ _)) hBig_lt
  have hGat : GraphAt memBig 0 G := by
    intro i hi
    simp only [G, Cited.Graph.encode, Cited.Graph.m, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_cons, List.length_nil] at hi ⊢
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  have hPre : (pathDSDataStructure pds.params wBig).initPre [0, 1, 1, 1, 4] memBig := by
    refine ⟨0, 1, 1, 1, 4, G, rfl, by simp [G, Cited.Graph.encode, Cited.Graph.m], hGat,
      le_rfl, le_rfl, ?_, by simp [G, Cited.Graph.m], by simp [G, Cited.Graph.m], ?_, ?_, ?_⟩
    · intro e he; simp [G] at he; subst he; simp [G]
    · intro v hv; have : v = 0 := by simpa [G] using hv
      subst this; simp [Cited.Graph.deg, Cited.Graph.degIn, Cited.Graph.inside, Cited.Graph.verts, G]
    · intro S hS hSne hSneX
      have hV : G.verts = {0} := by simp [Cited.Graph.verts, G]
      rw [hV] at hS hSneX
      rcases Finset.subset_singleton_iff.mp hS with rfl | rfl
      · exact False.elim (Finset.not_nonempty_empty hSne)
      · exact False.elim (hSneX rfl)
    · have hcast : ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = φ_r := by simp [φ_r]
      rw [hcast]; dsimp only [wBig, M_val]; omega
  have hZero : WordRAM.ZeroFrom memBig (heapArg [0, 1, 1, 1, 4]) := fun a ha => by
    have ha4 : 4 ≤ a := by simpa [heapArg] using ha
    simp only [memBig, G, Cited.Graph.encode, Cited.Graph.m]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
  have hSpace : heapArg [0, 1, 1, 1, 4] +
      (pathDSDataStructure pds.params wBig).initSpace [0, 1, 1, 1, 4] memBig < 2 ^ wBig := by
    have hread : Cited.readGraph memBig 0 = G := graphAt_iff_readGraph.mp hGat
    simp only [pathDSDataStructure, heapArg, List.getLastD_cons, List.getLastD_nil,
      List.getD_cons_zero, List.getD_cons_succ, hread]
    exact hBig_lt
  obtain ⟨_, _, _, _, _, _, _, x', _⟩ :=
    hSpec.2.1 [0, 1, 1, 1, 4] memBig 0 (fun _ => false) hArgs hPre hZero hSpace
  exact ⟨x'⟩

end MinCostFlow.Spanner
