module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueA
import WordRAM.Tactic

/-!
# Nonempty affected-set branch of a `0 < j` step: glue part B

Provides glue theorems 3 and 4 for `dsStepPosNonEmptyStmt`:
* `stepPosNE_finPre`: builds `UTCtx`, `RBCtx`, and `dsStepFinishContract.pre` after `dsReembStage`.
* `stepPosNE_dCtx`: builds `DCtx` for `dsCollectD` after `dsStepFinish` and `gen++`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

lemma StepPosNECtx.dPtr_lt (ctx : StepPosNECtx) {retSp retReemb : ℕ}
    (hretSp : retSp ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase
      ctx.G' ctx.J ctx.embJH + dsShortcutHeapSpace ctx.eAff ctx.out.emb)
    (hRe : retReemb - (retSp + ctx.eCap) ≤
      reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff) :
    retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
      5 * (retReemb - (retSp + ctx.eCap)) + 1 + 2 * ctx.oldBucketsSum +
      4 * ctx.out.Jtilde.m + (2 * ctx.lenSum + ctx.eAff.length) < 2 ^ ctx.w := by
  have h1 : ∀ (spEnd retS ec el ls rd rn ob jtm tw : ℕ),
      spEnd + ec + 16 * el + 14 * ls + 5 * rn + 1 + 2 * ob + 4 * jtm + 2 * ls + el < tw →
      retS ≤ spEnd → rd ≤ rn →
      retS + ec + 16 * el + 14 * ls + 5 * rd + 1 + 2 * ob + 4 * jtm + (2 * ls + el) < tw := by
    intros; omega
  exact h1 _ _ _ _ _ _ _ _ _ _ ctx.hEnd_ltw hretSp hRe

lemma slw_frame_of_range {b L vCap eCap j h0 ret a : ℕ}
    (hj : j ≤ L) (hfix : b + dsFixedSize L vCap eCap ≤ h0) (h0r : h0 ≤ ret)
    (ha : (a < dsDomGenBase b L vCap eCap ∧ a ≠ b + dsGenOff) ∨
          (dsSGenBase b L vCap eCap ≤ a ∧ a < dsVStampBase b L vCap eCap) ∨
          (dsEStampBase b L vCap eCap ≤ a ∧ a < h0) ∨
          ret ≤ a) :
    dsLevelWalksFrameCond L vCap eCap b j h0 ret a := by
  have hfl := fixed_layout_order b L vCap eCap
  rcases ha with ⟨h1, hne⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · refine ⟨hne, by omega,
      fun e he => by omega, fun e he => by omega,
      fun v hv => by omega, fun v hv => by omega,
      fun v hv => by omega, Or.inl (by omega)⟩
  · refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e he => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he; omega,
      fun e he => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he; omega,
      fun v hv => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) hv; omega,
      fun v hv => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) hv; omega,
      fun v hv => by omega, Or.inl (by omega)⟩
  · refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e he => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he; omega,
      fun e he => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he; omega,
      fun v hv => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) hv; omega,
      fun v hv => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) hv; omega,
      fun v hv => by omega, Or.inl h2⟩
  · refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e he => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he; omega,
      fun e he => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he; omega,
      fun v hv => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) hv; omega,
      fun v hv => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) hv; omega,
      fun v hv => by omega, Or.inr h1⟩

lemma slw_frame_of_other_lvl {b L vCap eCap j i h0 ret a : ℕ}
    (hj : j ≤ L) (hi : i ≤ L) (hne_ij : i ≠ j) (hfix : b + dsFixedSize L vCap eCap ≤ h0)
    (ha : a = dsDomGenBase b L vCap eCap + i ∨
          (∃ e < eCap, a = dsEdgeDomGenBase b L vCap eCap + i * eCap + e) ∨
          (∃ e < eCap, a = dsPiPtrBase b L vCap eCap + i * eCap + e) ∨
          (∃ v < vCap, a = dsRevGenBase b L vCap eCap + i * vCap + v) ∨
          (∃ v < vCap, a = dsRevHeadBase b L vCap eCap + i * vCap + v)) :
    dsLevelWalksFrameCond L vCap eCap b j h0 ret a := by
  have hfl := fixed_layout_order b L vCap eCap
  have hmul_ne : ∀ (m x y : ℕ), x < m → y < m → i * m + x ≠ j * m + y := by
    intro m x y hx hy heq
    have h1 : (i * m + x) / m = i := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hx, Nat.add_zero]
    have h2 : (j * m + y) / m = j := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hy, Nat.add_zero]
    exact hne_ij (h1.symm.trans ((congrArg (· / m) heq).trans h2))
  rcases ha with rfl | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e he => by omega, fun e he => by omega,
      fun v hv => by omega, fun v hv => by omega,
      fun v hv => by omega, Or.inl (by omega)⟩
  · have hidx := idx_lt_mul (i := i) (n := L + 1) (by omega) he
    refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e' he' h => hmul_ne eCap e e' he he' (by omega),
      fun e' he' => by omega,
      fun v hv => by omega, fun v hv => by omega,
      fun v hv => by omega, Or.inl (by omega)⟩
  · have hidx := idx_lt_mul (i := i) (n := L + 1) (by omega) he
    refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e' he' => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he'; omega,
      fun e' he' h => hmul_ne eCap e e' he he' (by omega),
      fun v hv => by omega, fun v hv => by omega,
      fun v hv => by omega, Or.inl (by omega)⟩
  · have hidx := idx_lt_mul (i := i) (n := L + 1) (by omega) hv
    refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e' he' => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he'; omega,
      fun e' he' => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he'; omega,
      fun v' hv' h => hmul_ne vCap v v' hv hv' (by omega),
      fun v' hv' => by omega,
      fun v' hv' => by omega, Or.inl (by omega)⟩
  · have hidx := idx_lt_mul (i := i) (n := L + 1) (by omega) hv
    refine ⟨by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega, by omega,
      fun e' he' => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he'; omega,
      fun e' he' => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) he'; omega,
      fun v' hv' => by have := idx_lt_mul (i := j) (n := L + 1) (by omega) hv'; omega,
      fun v' hv' h => hmul_ne vCap v v' hv hv' (by omega),
      fun v' hv' => by omega, Or.inl (by omega)⟩

lemma tail_frame_of_range {b L vCap eCap hdr c_size a : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ hdr)
    (ha : a < dsHPtr b vCap eCap ∨
          (dsAuxPtr b vCap eCap ≤ a ∧ a < dsMinHBase b vCap eCap) ∨
          (dsEdgeDomGenBase b L vCap eCap ≤ a ∧ a < dsSGenBase b L vCap eCap) ∨
          (dsSGenBase b L vCap eCap + (L + 1) ≤ a ∧ a < hdr) ∨
          hdr + 1 + c_size ≤ a) :
    (a < hdr ∨ hdr + 1 + c_size ≤ a) ∧
    (a < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ a) ∧
    (a < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ a) ∧
    ¬ ((dsDomGenBase b L vCap eCap ≤ a ∧ a < dsDomGenBase b L vCap eCap + (L + 1)) ∨
       (dsSGenBase b L vCap eCap ≤ a ∧ a < dsSGenBase b L vCap eCap + (L + 1))) := by
  have hfl := fixed_layout_order b L vCap eCap
  rcases ha with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · refine ⟨Or.inl (by omega), Or.inl h, Or.inl (by omega), ?_⟩
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> omega
  · refine ⟨Or.inl (by omega), Or.inr (by omega), Or.inl h2, ?_⟩
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> omega
  · refine ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), ?_⟩
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> omega
  · refine ⟨Or.inl h2, Or.inr (by omega), Or.inr (by omega), ?_⟩
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> omega
  · refine ⟨Or.inr h, Or.inr (by omega), Or.inr (by omega), ?_⟩
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> omega

lemma genOff_lt_hPtr (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    b + dsGenOff < dsHPtr b vCap eCap ∧
    b + dsGenOff < dsMinHBase b vCap eCap ∧
    b + dsGenOff < dsDomGenBase b L vCap eCap ∧
    b + dsGenOff < dsSGenBase b L vCap eCap ∧
    b + dsGenOff < dsVStampBase b L vCap eCap ∧
    b + dsGenOff < b + dsFixedSize L vCap eCap := by
  have hfl := fixed_layout_order b L vCap eCap
  simp only [dsGenOff, dsHdrSize] at hfl ⊢
  omega

/-! ## Glue 3: Precondition of `dsStepFinish` -/

private lemma stepPosNE_minH_after (ctx : StepPosNECtx) :
    ∀ e < ctx.eCap, ctx.mem2 (dsMinHBase ctx.b ctx.vCap ctx.eCap + e) =
      minHAfter ctx.u (ctx.mem0 (dsMinHBase ctx.b ctx.vCap ctx.eCap + e)) e := by
  intro e he
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have h0 := ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
  have h2 := ctx.hmin_after.1 e he
  have hmem_mid : ∀ k' : Fin (ctx.L + 1), (ctx.H_mid k').E = (ctx.st.H_level k').E ∩ ctx.G'.E := by
    intro k'
    have hsub := (ctx.hPref ctx.k (le_refl _)).H_level_sub k'
    have hV := (ctx.hPref ctx.k (le_refl _)).H_level_V k'
    exact (isSubgraph_restrictUpdate ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hsub)
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hV)
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hdu.1) hdu.2).2.2.2.1
  cases hu_eq : ctx.u with
  | insert _ _ _ => rw [hu_eq] at hdu; exact hdu.2.elim
  | delete d =>
    simp only [minHAfter]
    by_cases hed : e = d
    · subst hed
      have hnot : e ∉ delSet (Update.delete e) ctx.st.H.E := by simp [delSet]
      simp only [↓reduceIte]
      exact h2.1.mpr (hu_eq ▸ hnot)
    · simp only [hed, ↓reduceIte]
      by_cases heH : e ∈ ctx.st.H.E
      · have heD : e ∈ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, hed, heH]
        obtain ⟨i, hi_eq, hi_mem, hi_min⟩ := h0.2 heH
        obtain ⟨i', hi'_eq, hi'_mem, hi'_min⟩ := h2.2 heD
        have heG' : e ∈ ctx.G'.E := by
          have heG : e ∈ ctx.st.G.E := (ctx.hPref ctx.k (le_refl _)).G_eq ▸
            (ctx.hPref ctx.k (le_refl _)).H_sub.2.1 heH
          change e ∈ (ctx.st.G.applyUpdate ctx.u).E
          rw [applyUpdate_E_delSet hdu.2, hu_eq]; simp [delSet, hed, heG]
        have hmem_iff : ∀ k' : Fin (ctx.L + 1), e ∈ (ctx.H_mid k').E ↔ e ∈ (ctx.st.H_level k').E :=
          fun k' => by rw [hmem_mid k', Finset.mem_inter]; exact ⟨And.left, fun h => ⟨h, heG'⟩⟩
        have hle1 : ¬ i'.1 < i.1 := fun hlt => hi_min i' hlt ((hmem_iff i').mp hi'_mem)
        have hle2 : ¬ i.1 < i'.1 := fun hlt => hi'_min i hlt ((hmem_iff i).mpr hi_mem)
        omega
      · have hnot : e ∉ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, heH]
        rw [h0.1.mpr heH, h2.1.mpr hnot]
  | split v v' St Sh =>
    simp only [minHAfter]
    by_cases heH : e ∈ ctx.st.H.E
    · have heD : e ∈ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, heH]
      obtain ⟨i, hi_eq, hi_mem, hi_min⟩ := h0.2 heH
      obtain ⟨i', hi'_eq, hi'_mem, hi'_min⟩ := h2.2 heD
      have heG' : e ∈ ctx.G'.E := by
        have heG : e ∈ ctx.st.G.E := (ctx.hPref ctx.k (le_refl _)).G_eq ▸
          (ctx.hPref ctx.k (le_refl _)).H_sub.2.1 heH
        change e ∈ (ctx.st.G.applyUpdate ctx.u).E
        rw [applyUpdate_E_delSet hdu.2, hu_eq]; simp [delSet, heG]
      have hmem_iff : ∀ k' : Fin (ctx.L + 1), e ∈ (ctx.H_mid k').E ↔ e ∈ (ctx.st.H_level k').E :=
        fun k' => by rw [hmem_mid k', Finset.mem_inter]; exact ⟨And.left, fun h => ⟨h, heG'⟩⟩
      have hle1 : ¬ i'.1 < i.1 := fun hlt => hi_min i' hlt ((hmem_iff i').mp hi'_mem)
      have hle2 : ¬ i.1 < i'.1 := fun hlt => hi'_min i hlt ((hmem_iff i).mpr hi_mem)
      omega
    · have hnot : e ∉ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, heH]
      rw [h0.1.mpr heH, h2.1.mpr hnot]

private lemma hAff_emb_clean (ctx : StepPosNECtx) {e : ℕ} (he : e ∈ ctx.eAff) :
    ctx.wpPtr + ctx.eAff.length ≤ ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e) ∧
    ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e) + (2 * (ctx.embJH e).length + 1) ≤
      ctx.wpPtr + ctx.eAff.length + projHeapNeed ctx.piLt_mid ctx.eAff ∧
    MWalkAt ctx.memAff (ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e)) (ctx.embJH e) :=
  ctx.hAff_emb e he

private lemma stepPosNE_res_facts (ctx : StepPosNECtx) (hne : ctx.E_aff.Nonempty)
    (hcanon : ctx.out = canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH) :
    ctx.res.state.G = ctx.G' ∧
    ctx.res.state.H.IsValid ∧
    ctx.res.state.H.V = ctx.G'.V ∧
    ctx.res.state.H.E ⊆ ctx.G'.E ∧
    (∀ e ∈ ctx.eAff, ctx.res.state.H.IsWalk (ctx.G'.tail e) (ctx.G'.head e)
      (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e)) := by
  have hk1_inv := (step_inv ctx.hVG₀ (by
      have := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
      have := ctx.hj_pos; omega)
    ctx.hq ctx.hGm₀ (canonicalSparsify_spec_absorb ctx.impl ctx.mMax) ctx.hBV ctx.hds ctx.hu_some
    ctx.hPref).1
  have hst1_eq : runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us (ctx.k + 1) =
      ctx.res.state := by simp [runState, StepPosNECtx.res, StepPosNECtx.st, ctx.hu_some]
  have hcl : chooseLevel ctx.L ctx.st.q (ctx.st.t + 1) = ctx.j := by
    rw [(ctx.hPref ctx.k (le_refl _)).q_eq, (ctx.hPref ctx.k (le_refl _)).t_eq]
  have hne0 : ctx.j ≠ 0 := Nat.ne_of_gt ctx.hj_pos
  have hG1 : ctx.res.state.G = ctx.G' := by
    dsimp only [StepPosNECtx.res, step]; simp only [hcl, hne0, ↓reduceDIte]
  have hH'val : ctx.res.state.H.IsValid := hst1_eq ▸ hk1_inv.H_valid
  have hH'V : ctx.res.state.H.V = ctx.G'.V := by
    have h1 := hk1_inv.H_V
    rw [hst1_eq, ← hk1_inv.G_eq, hst1_eq, hG1] at h1; exact h1
  have hH'E_sub : ctx.res.state.H.E ⊆ ctx.G'.E := by
    have h1 := hk1_inv.H_sub.2.1
    rw [hst1_eq, ← hk1_inv.G_eq, hst1_eq, hG1] at h1; exact h1
  refine ⟨hG1, hH'val, hH'V, hH'E_sub, fun e he => ?_⟩
  have hjle : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  let jF : Fin (ctx.L + 1) := ⟨ctx.j, by omega⟩
  have hin : e ∈ ctx.res.state.inDom jF := by
    dsimp only [StepPosNECtx.res, step]
    simp only [hcl, hne0, ↓reduceDIte, jF, lt_irrefl, ↓reduceIte]
    exact (ctx.hAff_iff e).mp he
  have hPi_eq : ctx.res.state.Pi_level jF e =
      reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e := by
    dsimp only [StepPosNECtx.res, step]
    simp only [hcl, hne0, ↓reduceDIte, jF, lt_irrefl, ↓reduceIte, hne, ← hcanon]
  have heG' : e ∈ ctx.G'.E := (Finset.mem_filter.mp ((ctx.hAff_iff e).mp he)).1
  have heG1 : e ∈ (ctx.G₀.applyBatch (ctx.us.take (ctx.k + 1))).E := by
    rw [← hk1_inv.G_eq, hst1_eq, hG1]; exact heG'
  have hpi_eq : piLe ctx.res.state ctx.j e = ctx.res.state.Pi_level jF e := by
    have h0 : e ∈ ctx.res.state.inDom ⟨0, Nat.zero_lt_succ ctx.L⟩ := by
      rw [← hst1_eq, hk1_inv.inDom0]; exact heG1
    have h1 := piLtFrom_eq_self_of_mem ctx.res.state.Pi_level ctx.res.state.inDom
      h0 (j := jF) hin
    simpa [piLe, piLt] using h1
  have hw := (hk1_inv.emb_at jF (le_refl _)).2 e heG1
  rw [hst1_eq, hpi_eq, hPi_eq, ← hk1_inv.G_eq, hst1_eq, hG1] at hw
  refine MGraph.isWalk_of_isSubgraph (G := ctx.res.state.H)
    (H := unionGraphLt ctx.G' ctx.res.state.H_level (jF.1 + 1)) ?_ hw
  refine ⟨by rw [hH'V]; exact Finset.Subset.rfl, ?_, fun e' he' => ?_⟩
  · have hHE : ctx.res.state.H.E = unionEdgesLt ctx.res.state.H_level (ctx.L + 1) :=
      hst1_eq ▸ hk1_inv.H_E
    rw [hHE]
    exact unionEdgesLt_mono ctx.res.state.H_level (by omega)
  · have hHsub : ctx.G'.IsSubgraph ctx.res.state.H := by
      have h1 := hk1_inv.H_sub
      rw [hst1_eq, ← hk1_inv.G_eq, hst1_eq, hG1] at h1; exact h1
    have heH : e' ∈ ctx.res.state.H.E := by
      have hHE : ctx.res.state.H.E = unionEdgesLt ctx.res.state.H_level (ctx.L + 1) :=
        hst1_eq ▸ hk1_inv.H_E
      rw [hHE]
      exact unionEdgesLt_mono ctx.res.state.H_level (by omega) he'
    exact ⟨(hHsub.2.2 e' heH).1.symm, (hHsub.2.2 e' heH).2.symm⟩

private lemma stepPosNE_reembFacts (ctx : StepPosNECtx) {memSp memReemb : ℕ → ℕ} {retSp retReemb : ℕ}
    {rc : RSCtx} (hJt_E : ctx.out.Jtilde.E ⊆ ctx.E_aff)
    (hrc : rc.w = ctx.w ∧ rc.vCap = ctx.vCap ∧ rc.eCap = ctx.eCap ∧
      rc.G = ctx.G' ∧ rc.embLt = ctx.piLt_mid ∧ rc.embJH = ctx.embJH ∧
      rc.outEmb = ctx.outEmb ∧ rc.S = ctx.S_prev ∧ rc.es = ctx.eAff ∧
      rc.gPtr = dsGPtr ctx.b ∧ rc.sBitPtr = dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      rc.tab = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧ rc.piTab = retSp ∧
      rc.esPtr = ctx.eAffPtr ∧ rc.wpPtr = ctx.wpPtr ∧ rc.heap = retSp + ctx.eCap ∧
      rc.mem0 = memSp)
    (hSpInfo : ctx.guestBase ≤ memSp ctx.scratchPtr ∧
      memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp ∧
      DynGraphAt memSp (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ctx.out.Jtilde ∧
      ZeroFrom memSp retSp)
    (hRePost : (dsReembStageContract rc).post [] memSp retReemb memReemb) :
    let heapReemb := retSp + ctx.eCap
    let heapFin := heapReemb + 16 * ctx.eAff.length + 14 * ctx.lenSum + 3 * (retReemb - heapReemb)
    let uhTailHdr := heapFin + 2 * (retReemb - heapReemb)
    let Pi_j := reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev
    ∃ jtEList : List ℕ,
      jtEList.Nodup ∧ jtEList.length = ctx.out.Jtilde.m ∧ jtEList.length ≤ ctx.eCap ∧
      (∀ e, e ∈ jtEList ↔ e ∈ ctx.out.Jtilde.E) ∧
      ListAt memReemb (dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap) jtEList ∧
      (∀ e < ctx.eCap, memReemb (dgEPresBase (memSp ctx.scratchPtr) ctx.vCap + e) =
        if e ∈ jtEList.toFinset then 1 else 0) ∧
      heapReemb ≤ retReemb ∧
      retReemb - heapReemb ≤ reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff ∧
      heapReemb + reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff ≤ heapFin ∧
      retReemb ≤ heapFin ∧
      heapFin + 2 * (ctx.eAff.map fun e => (Pi_j e).length + 1).sum ≤ uhTailHdr ∧
      ZeroFrom memReemb heapFin ∧
      (∀ addr, addr < retSp → memReemb addr = memSp addr) ∧
      (∀ e ∈ ctx.eAff,
        heapReemb + ctx.eAff.length + compHeapNeed ctx.embJH ctx.outEmb ctx.eAff ≤ memReemb (retSp + e) ∧
        memReemb (retSp + e) + (mWalkEncode (Pi_j e)).length ≤ retReemb ∧
        MWalkAt memReemb (memReemb (retSp + e)) (Pi_j e)) := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  obtain ⟨_, _, _, hrc_G, hrc_lt, hrc_jh, hrc_out, hrc_S, hrc_es, _, _, _, hrc_pi, _, _, hrc_hp, _⟩ := hrc
  obtain ⟨hgb_jt, hjt_sp, hDynJt, hZeroSp⟩ := hSpInfo
  obtain ⟨hReWalks, hReRet, hReFrame⟩ := hRePost
  rw [hrc_G, hrc_lt, hrc_jh, hrc_out, hrc_S, hrc_es, hrc_pi, hrc_hp] at hReWalks
  rw [hrc_G, hrc_lt, hrc_jh, hrc_out, hrc_S, hrc_es, hrc_hp] at hReRet
  rw [hrc_lt, hrc_jh, hrc_out, hrc_es, hrc_pi, hrc_hp] at hReFrame
  have hRe_lt : ∀ addr, addr < retSp → memReemb addr = memSp addr := fun addr ha =>
    hReFrame addr (Or.inl (by omega)) (fun e _ => by omega)
  have hReAll :=
    reembStageNeed_le_from_ret ctx.G' ctx.piLt_mid ctx.embJH ctx.outEmb ctx.S_prev ctx.eAff
      (retSp + ctx.eCap)
  dsimp only at hReAll
  rw [← hReRet] at hReAll
  obtain ⟨hret_ge_hr, hret_le_hf, hRe_bounds⟩ := hReAll
  have hSet_bounds :=
    setLevelWalks_space_le_from_ret ctx.G' ctx.piLt_mid ctx.embJH ctx.outEmb ctx.S_prev ctx.eAff
      (retSp + ctx.eCap)
  dsimp only at hSet_bounds
  rw [← hReRet] at hSet_bounds
  have hreemb_le_need : retReemb - (retSp + ctx.eCap) ≤
      reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff := by
    have hsum_le : ∀ (f g : ℕ → ℕ) (l : List ℕ), (∀ e ∈ l, f e ≤ g e) →
        (l.map f).sum ≤ (l.map g).sum := by
      intro f g l hfg
      induction l with
      | nil => simp
      | cons e es ih =>
        simp only [List.map_cons, List.sum_cons]
        have h1 := hfg e List.mem_cons_self
        have h2 := ih (fun x hx => hfg x (List.mem_cons_of_mem _ hx))
        omega
    have h1 := hsum_le (reembOutLen ctx.G' ctx.piLt_mid (ctx.embJH.comp ctx.outEmb) ctx.S_prev)
      (fun e => 14 * (ctx.piLt_mid e).length + 4 * (ctx.embJH.comp ctx.outEmb e).length + 15)
      ctx.eAff (fun e _ => by
        have := reembOutLen_le ctx.G' ctx.piLt_mid (ctx.embJH.comp ctx.outEmb) ctx.S_prev e; omega)
    simp only [reembHeapAt, List.take_length] at hReRet
    unfold reembStageNeed reembHeapNeed
    omega
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hGE'_cap : ∀ e ∈ ctx.G'.E, e < ctx.eCap := fun e he =>
    ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu.2 he)
  have hZeroFin : ZeroFrom memReemb (retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
      3 * (retReemb - (retSp + ctx.eCap))) := by
    intro a ha
    have h1 : memReemb a = memSp a :=
      hReFrame a (Or.inr (le_trans hRe_bounds ha)) (fun e he => by
        have heG' : e ∈ ctx.G'.E := (Finset.mem_filter.mp ((ctx.hAff_iff e).mp he)).1
        have heC : e < ctx.eCap := hGE'_cap e heG'
        omega)
    rw [h1]
    exact hZeroSp a (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hjtPres_sp, hjtEList_ex, _, _⟩ := hDynJt
  rcases hjtEList_ex with ⟨jtEList, hjt_len, hjt_nd, hjt_iff, hjt_at_sp, _⟩
  have hjt_le_cap : jtEList.length ≤ ctx.eCap := by
    have hsub : jtEList.toFinset ⊆ Finset.range ctx.eCap := by
      intro e he
      exact Finset.mem_range.mpr
        (hGE'_cap e (Finset.mem_filter.mp (hJt_E ((hjt_iff e).mp (List.mem_toFinset.mp he)))).1)
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hjt_nd, Finset.card_range] at hcard
    exact hcard
  have hjt_at : ListAt memReemb (dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap) jtEList :=
    listAt_of_agree (fun k' hk' =>
      hRe_lt _ (by simp only [dgEListBase, dynGraphSize] at hjt_sp ⊢; omega)) hjt_at_sp
  have hjt_pres : ∀ e < ctx.eCap, memReemb (dgEPresBase (memSp ctx.scratchPtr) ctx.vCap + e) =
      if e ∈ jtEList.toFinset then 1 else 0 := by
    intro e he
    rw [hRe_lt _ (by simp only [dgEPresBase, dynGraphSize] at hjt_sp ⊢; omega), hjtPres_sp e he]
    congr 1; simp [hjt_iff]
  have hPi_congr : ∀ e, reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e =
      reembedWalk ctx.G' ctx.G' ctx.piLt_mid ctx.embMid ctx.S_prev e := fun e =>
    (reembedWalk_congr_host (G' := ctx.G') (H_lt := ctx.H_lt)
      (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).tail = ctx.G'.tail)
      (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).head = ctx.G'.head) _ _ _ _).symm
  have hSet_bounds' : 2 * (ctx.eAff.map fun e =>
      (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e).length + 1).sum ≤
      2 * (retReemb - (retSp + ctx.eCap)) := by
    simpa only [hPi_congr] using hSet_bounds
  refine ⟨jtEList, hjt_nd, hjt_len, hjt_le_cap, hjt_iff, hjt_at, hjt_pres, hret_ge_hr,
    hreemb_le_need, hRe_bounds, hret_le_hf, by omega, hZeroFin, hRe_lt, fun e he => ?_⟩
  have hrew := hReWalks e he
  have hlen_le : (mWalkEncode (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e)).length ≤
      reembOutLen ctx.G' ctx.piLt_mid ctx.embMid ctx.S_prev e := by
    rw [hPi_congr e, mWalkEncode_length, reembOutLen, Nat.add_comm]
  exact ⟨hrew.1, le_trans (Nat.add_le_add_left hlen_le _) hrew.2.1, by rw [hPi_congr e]; exact hrew.2.2⟩

/-- Build `UTCtx`, `RBCtx`, and `dsStepFinishContract.pre` on `memReemb` after `dsReembStage`. -/
theorem stepPosNE_finPre (ctx : StepPosNECtx) {memSp memReemb : ℕ → ℕ} {retSp retReemb : ℕ}
    {rc : RSCtx}
    (hne : ctx.E_aff.Nonempty)
    (hcanon : ctx.out = canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH)
    (hJt_E : ctx.out.Jtilde.E ⊆ ctx.E_aff)
    (hrc : rc.w = ctx.w ∧ rc.vCap = ctx.vCap ∧ rc.eCap = ctx.eCap ∧
      rc.G = ctx.G' ∧ rc.embLt = ctx.piLt_mid ∧ rc.embJH = ctx.embJH ∧
      rc.outEmb = ctx.outEmb ∧ rc.S = ctx.S_prev ∧ rc.es = ctx.eAff ∧
      rc.gPtr = dsGPtr ctx.b ∧ rc.sBitPtr = dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      rc.tab = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧ rc.piTab = retSp ∧
      rc.esPtr = ctx.eAffPtr ∧ rc.wpPtr = ctx.wpPtr ∧ rc.heap = retSp + ctx.eCap ∧
      rc.mem0 = memSp)
    (hSpInfo : ctx.guestBase ≤ memSp ctx.scratchPtr ∧
      memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp ∧
      retSp ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase ctx.G' ctx.J ctx.embJH +
        dsShortcutHeapSpace ctx.eAff ctx.out.emb ∧
      DynGraphAt memSp (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ctx.out.Jtilde ∧
      ZeroFrom memSp retSp ∧
      (∀ v < ctx.vCap, memSp (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) ≤
        ctx.memAff (ctx.b + dsGenOff)) ∧
      (∀ addr, addr < ctx.scratchPtr →
        (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
        memSp addr = ctx.memAff addr))
    (hRePost : (dsReembStageContract rc).post [] memSp retReemb memReemb) :
    let jtPtr := memSp ctx.scratchPtr
    let heapReemb := retSp + ctx.eCap
    let reembDelta := retReemb - heapReemb
    let heapFin := heapReemb + 16 * ctx.eAff.length + 14 * ctx.lenSum + 3 * reembDelta
    let uhTailHdr := heapFin + 2 * reembDelta
    let jtPres := dgEPresBase jtPtr ctx.vCap
    let jtEListPtr := dgEListBase jtPtr ctx.vCap ctx.eCap
    let Pi_j := reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev
    ∃ (c : UTCtx) (r : RBCtx) (jtEList : List ℕ),
      jtEList.Nodup ∧ jtEList.length = ctx.out.Jtilde.m ∧
      (∀ e, e ∈ jtEList ↔ e ∈ ctx.out.Jtilde.E) ∧
      ListAt memReemb jtEListPtr jtEList ∧
      heapReemb ≤ retReemb ∧
      retReemb - heapReemb ≤ reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff ∧
      heapReemb + reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff ≤ heapFin ∧
      retReemb ≤ heapFin ∧
      heapFin + 2 * (ctx.eAff.map fun e => (Pi_j e).length + 1).sum ≤ uhTailHdr ∧
      ZeroFrom memReemb heapFin ∧
      c.da.w = ctx.w ∧ c.vCap = ctx.vCap ∧ c.da.eCap = ctx.eCap ∧
      c.da.lo = ctx.j ∧ c.da.hi = ctx.L + 1 ∧ c.da.out = uhTailHdr + 1 ∧
      c.es = jtEList ∧ c.size ≤ 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m ∧
      (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length = ctx.oldBucketsSum ∧
      r.L = ctx.L ∧ r.vCap = ctx.vCap ∧ r.eCap = ctx.eCap ∧ r.b = ctx.b ∧ r.j = ctx.j ∧
      r.es = jtEList ∧
      (bucketsCat r.B r.j (r.L + 1 - r.j)).length = ctx.oldBucketsSum ∧
      (restrictUpdate ctx.u ctx.st.H ++ c.recs).Perm ctx.res.UH ∧
      (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)).applyBatch c.recs = ctx.res.state.H ∧
      (∀ u' ∈ c.recs, isDelOrIns u') ∧
      (∀ e < ctx.eCap,
        (minHRebuild ctx.j jtEList.toFinset r.m0 e = 0 ↔ e ∉ ctx.res.state.H.E) ∧
        (e ∈ ctx.res.state.H.E → ∃ i : Fin (ctx.L + 1),
          minHRebuild ctx.j jtEList.toFinset r.m0 e = i.1 + 1 ∧
          e ∈ (ctx.res.state.H_level i).E ∧
          ∀ k' : Fin (ctx.L + 1), k'.1 < i.1 → e ∉ (ctx.res.state.H_level k').E)) ∧
      (∀ i : Fin (ctx.L + 1), ∀ e, e ∈ r.newB i.1 ↔
        e ∈ ctx.res.state.H.E ∧ minHRebuild ctx.j jtEList.toFinset r.m0 e = i.1 + 1) ∧
      (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)) uhTailHdr r
        ctx.G' ctx.eAff Pi_j (fun _ => False) ctx.eAffPtr retSp heapFin).pre
        ([dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          jtPres, uhTailHdr + 1, jtEListPtr, jtEList.length,
          dgEPresBase (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap,
          dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, uhTailHdr] ++
         [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b, jtEListPtr, jtEList.length] ++
         [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
          ctx.j + 1, ctx.j, ctx.L + 1] ++
         [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, retSp, heapFin]) memReemb ∧
      (∀ addr, addr < retSp → memReemb addr = memSp addr) := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  obtain ⟨hgb_jt, hjt_sp, hretSp_le, hDynJt, hZeroSp, hVSt_sp, hlt_scr_ag⟩ := hSpInfo
  obtain ⟨jtEList, hjt_nd, hjt_len, hjt_le_cap, hjt_iff, hjt_at, hjt_pres, hret_ge_hr,
    hreemb_le_need, hRe_bounds, hret_le_hf, hSet_bounds', hZeroFin, hRe_lt, hReWalks'⟩ :=
    stepPosNE_reembFacts ctx hJt_E hrc ⟨hgb_jt, hjt_sp, hDynJt, hZeroSp⟩ hRePost
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hGE'_cap : ∀ e ∈ ctx.G'.E, e < ctx.eCap := fun e he =>
    ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu.2 he)
  have hEnd_d := ctx.dPtr_lt hretSp_le hreemb_le_need
  have hmin2_eq := stepPosNE_minH_after ctx
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hgen_re : memReemb (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) :=
    (hRe_lt _ (by omega)).trans (hlt_scr_ag _ (by omega) (fun v hv => by omega))
  have hgen_0aff : ctx.mem0 (ctx.b + dsGenOff) ≤ ctx.memAff (ctx.b + dsGenOff) := by
    have := ctx.hgen_02; have := ctx.hAff_gen; omega
  have hdom_re_ag : ∀ a, dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a →
      a < dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap → memReemb a = ctx.mem0 a := by
    intro a ha1 ha2
    exact (hRe_lt a (by omega)).trans ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
      ((ctx.hAff_frame a (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
        (ctx.hDom_02 a ha1 ha2)))
  have hDG'_re : DynGraphAt memReemb (dsGPtr ctx.b) ctx.vCap ctx.eCap ctx.G' :=
    dynGraphAt_of_agree ctx.hG'_graph fun a ha1 ha2 =>
      (hRe_lt a (by omega)).trans ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
        (ctx.hAff_frame a (by omega) (by omega)
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))))
  have hDHmid_re : DynGraphAt memReemb (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap ctx.eCap
      (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)) :=
    dynGraphAt_of_agree ctx.hHmid_graph fun a ha1 ha2 =>
      (hRe_lt a (by omega)).trans ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
        (ctx.hAff_frame a (by omega) (by omega)
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))))
  have hHdr_re_ag : ∀ a, ctx.b ≤ a → a < ctx.b + dsHdrSize → a ≠ ctx.b + dsGenOff →
      memReemb a = ctx.mem0 a := fun a ha1 ha2 hne' =>
    (hRe_lt a (by omega)).trans ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
      ((ctx.hAff_frame a (by omega) hne' (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega))).trans (ctx.hHdr_02 a ha1 ha2 hne')))
  have hBk_re_ag : ∀ a, dsMinHBase ctx.b ctx.vCap ctx.eCap ≤ a →
      a < dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap → memReemb a = ctx.mem2 a := fun a ha1 ha2 =>
    (hRe_lt a (by omega)).trans ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
      (ctx.hAff_frame a (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))))
  have heAff_at_re : ListAt memReemb ctx.eAffPtr ctx.eAff :=
    listAt_of_agree (fun k' hk' =>
      (hRe_lt _ (by omega)).trans (hlt_scr_ag _ (by omega) (fun v hv => by omega))) ctx.hAff_at
  have hRe_arith :
      let hf := retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum + 3 * (retReemb - (retSp + ctx.eCap))
      let hdr := hf + 2 * (retReemb - (retSp + ctx.eCap))
      ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ hf ∧
      hf ≤ hdr ∧
      hf + 2 * (ctx.eAff.map fun e =>
        (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e).length + 1).sum < 2 ^ ctx.w ∧
      ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.eAffPtr ∧
      ctx.eAffPtr + ctx.eAff.length ≤ hf ∧
      ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ retSp ∧
      retSp + ctx.eCap ≤ hf ∧
      ctx.memAff (ctx.b + dsGenOff) + 1 + ctx.eAff.length < 2 ^ ctx.w ∧
      dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.vCap ≤ retSp ∧
      ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ retSp + ctx.eCap + ctx.eAff.length +
        compHeapNeed ctx.embJH ctx.outEmb ctx.eAff := by
    have := ctx.hGen_ltw
    dsimp only; omega
  have hDom_bounds :
      dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ dsEdgeDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dsEdgeDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.L + 1) * ctx.eCap ≤
        dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ dsRevGenBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dsRevGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.L + 1) * ctx.vCap ≤
        dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap := by omega
  let uhTailHdr := (retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
    3 * (retReemb - (retSp + ctx.eCap))) + 2 * (retReemb - (retSp + ctx.eCap))
  have hbf_arith :
      ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap < 2 ^ ctx.w ∧
      ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ uhTailHdr ∧
      ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ∧
      dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap + jtEList.length ≤ uhTailHdr ∧
      dgEPresBase (memSp ctx.scratchPtr) ctx.vCap + ctx.eCap ≤ uhTailHdr ∧
      uhTailHdr + 1 + (2 * (bucketsCat (fun i => delErase ctx.u
        (if hi : i < ctx.L + 1 then ctx.x.hBuckets ⟨i, hi⟩ else []))
        ctx.j (ctx.L + 1 - ctx.j)).length + 4 * jtEList.length) < 2 ^ ctx.w := by
    have hsz : 2 * (bucketsCat (fun i => delErase ctx.u
      (if hi : i < ctx.L + 1 then ctx.x.hBuckets ⟨i, hi⟩ else []))
      ctx.j (ctx.L + 1 - ctx.j)).length + 4 * jtEList.length ≤
      2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m := by rw [ctx.hOldSum, hjt_len]
    dsimp only [uhTailHdr, dgEListBase, dgEPresBase, dynGraphSize] at hjt_sp ⊢; omega
  have hjle : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hdomJ0 := ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨ctx.j, Nat.lt_succ_of_le hjle⟩
  have hbf := buildFinishCtx
    (mem0 := ctx.mem0) (mem2 := ctx.mem2) (mem := memReemb)
    (jtEList := jtEList)
    (jtPresPtr := dgEPresBase (memSp ctx.scratchPtr) ctx.vCap)
    (jtEListPtr := dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap)
    (hdr := uhTailHdr)
    ctx.hVG₀ ctx.hq ctx.hGm₀ ctx.hBV ctx.hds ctx.hu_some
    ctx.hPref ctx.hj_pos ctx.hw16 ctx.hState ctx.hGV'_cap
    hbf_arith.1 hbf_arith.2.1
    ctx.hBk_mem2 hmin2_eq
    hHdr_re_ag hBk_re_ag hDG'_re hDHmid_re
    hjt_nd
    (fun e => by simp only [hne, ↓reduceIte, ← hcanon]; exact hjt_iff e)
    hjt_at hjt_pres
    hbf_arith.2.2.1 hbf_arith.2.2.2.1 hbf_arith.2.2.2.2.1 hbf_arith.2.2.2.2.2
  rcases hbf with ⟨c, r, hc_w, hc_e, hc_v, _, _, _, _, hc_lo, hc_hi, _, hc_out, hc_B, _, hc_es,
    _, _, _, hr_L, hr_v, hr_e, hr_b, hr_j, hr_es, _, hr_B, _, hpreTail, hApplyRecs, hPermRecs, hDelIns,
    _, hminNew, hnewB⟩
  have hG'val : ctx.G'.IsValid :=
    isValid_applyUpdate_of_delOrSplit ctx.hState.2.2.2.2.1
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hdu.1) hdu.2
  obtain ⟨_, hH'val, hH'V, hH'E_sub, hPi_walk⟩ := stepPosNE_res_facts ctx hne hcanon
  have hc_bk : (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length = ctx.oldBucketsSum := by
    rw [hc_B, hc_lo, hc_hi, ← ctx.hOldSum]
  have hr_bk : (bucketsCat r.B r.j (r.L + 1 - r.j)).length = ctx.oldBucketsSum := by
    rw [hr_B, hr_j, hr_L, ← ctx.hOldSum]
  have hc_size_le : c.size ≤ 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m := by
    simp only [UTCtx.size, hc_B, hc_lo, hc_hi, hc_es, ← ctx.hOldSum, hjt_len]
    exact le_refl _
  clear hfl hch hgo hEnd_d hjt_sp hgb_jt hretSp_le hmin2_eq hdu hne hcanon hJt_E hjt_le_cap
    hZeroSp hlt_scr_ag hDynJt hrc hRePost hbf_arith hHdr_re_ag hBk_re_ag hDHmid_re
  refine ⟨c, r, jtEList, hjt_nd, hjt_len, hjt_iff, hjt_at, hret_ge_hr, hreemb_le_need,
    hRe_bounds, hret_le_hf, hSet_bounds', hZeroFin, hc_w, hc_v, hc_e, hc_lo, hc_hi, hc_out,
    hc_es, hc_size_le, hc_bk, hr_L, hr_v, hr_e, hr_b, hr_j, hr_es, hr_bk, hPermRecs, hApplyRecs,
    hDelIns, hminNew, hnewB, ?_, hRe_lt⟩
  refine ⟨by rw [hr_b, hr_v, hr_e]; exact hpreTail,
    by simp [hr_b, hr_j], by rw [hc_v, hr_v], by rw [hc_e, hr_e],
    by rw [hr_b]; exact ctx.hState.2.2.2.1,
    by rw [hr_b, hr_L, hr_v, hr_e]; exact hRe_arith.1, hRe_arith.2.1,
    by rw [hc_w]; exact hRe_arith.2.2.1,
    by rw [hr_b, hr_L, hr_v, hr_e]; exact hRe_arith.2.2.2.1, hRe_arith.2.2.2.2.1,
    by rw [hr_b, hr_L, hr_v, hr_e]; exact hRe_arith.2.2.2.2.2.1,
    by rw [hr_e]; exact hRe_arith.2.2.2.2.2.2.1,
    by rw [hr_b, hgen_re, hc_w]; exact hRe_arith.2.2.2.2.2.2.2.1,
    fun v hv => by
      rw [hr_v] at hv; rw [hr_b, hr_L, hr_v, hr_e, hgen_re]
      rw [hRe_lt _ (lt_of_lt_of_le (Nat.add_lt_add_left hv _) hRe_arith.2.2.2.2.2.2.2.2.1)]
      exact hVSt_sp v hv,
    fun e he => by
      rw [hr_e] at he; rw [hr_b, hr_L, hr_v, hr_e, hr_j, hgen_re]
      have hidx : ctx.j * ctx.eCap + e < (ctx.L + 1) * ctx.eCap := idx_lt_mul (Nat.lt_succ_of_le hjle) he
      rw [hdom_re_ag _ (le_trans (le_trans hDom_bounds.1 (Nat.le_add_right _ _)) (Nat.le_add_right _ _))
        (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left hidx _) hDom_bounds.2.1)]
      exact le_trans (hdomJ0.2.1 e he).1 hgen_0aff,
    fun v hv => by
      rw [hr_v] at hv; rw [hr_b, hr_L, hr_v, hr_e, hr_j, hgen_re]
      have hidx : ctx.j * ctx.vCap + v < (ctx.L + 1) * ctx.vCap := idx_lt_mul (Nat.lt_succ_of_le hjle) hv
      rw [hdom_re_ag _ (le_trans (le_trans hDom_bounds.2.2.1 (Nat.le_add_right _ _)) (Nat.le_add_right _ _))
        (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left hidx _) hDom_bounds.2.2.2)]
      exact le_trans (hdomJ0.2.2.2.2.2 v hv).1 hgen_0aff,
    fun _ hf => hf.elim,
    ctx.hAff_eNd, heAff_at_re,
    by rw [hr_b, hr_v, hr_e]; exact hDG'_re,
    hG'val, by rw [hr_v]; exact ctx.hGV'_cap, by rw [hr_e]; exact hGE'_cap,
    hApplyRecs ▸ hH'val, by rw [hApplyRecs, hH'V],
    by rw [hApplyRecs, hr_v, hH'V]; exact ctx.hGV'_cap,
    by rw [hApplyRecs, hr_e]; exact fun e he => hGE'_cap e (hH'E_sub he),
    fun e he => ?_⟩
  have hrew := hReWalks' e he
  have heG' : e ∈ ctx.G'.E := (Finset.mem_filter.mp ((ctx.hAff_iff e).mp he)).1
  refine ⟨by rw [hr_e]; exact hGE'_cap e heG', heG', hApplyRecs ▸ hPi_walk e he, hrew.2.2,
    by rw [hr_b, hr_L, hr_v, hr_e]; exact le_trans hRe_arith.2.2.2.2.2.2.2.2.2 hrew.1,
    le_trans hrew.2.1 hret_le_hf⟩

/-! ## Glue 4: `dsStepFinish` frame and `DCtx` for `dsCollectD` -/

/-- Extract the generation update and `[dsEStampBase .. retSp)` frame from `dsStepFinishContract.post`. -/
theorem stepPosNE_finFrame (ctx : StepPosNECtx) {memSp memReemb memFin : ℕ → ℕ}
    {retSp retReemb retFin heapFin uhTailHdr : ℕ} {c : UTCtx} {r : RBCtx} {jtEList : List ℕ}
    (hhf : heapFin = retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
      3 * (retReemb - (retSp + ctx.eCap)))
    (hhdr : uhTailHdr = heapFin + 2 * (retReemb - (retSp + ctx.eCap)))
    (hSpInfo : ctx.guestBase ≤ memSp ctx.scratchPtr ∧
      memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp ∧
      (∀ addr, addr < ctx.scratchPtr →
        (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
        memSp addr = ctx.memAff addr))
    (hRe_lt : ∀ addr, addr < retSp → memReemb addr = memSp addr)
    (hc_info : c.vCap = ctx.vCap ∧ c.da.eCap = ctx.eCap ∧ c.da.out = uhTailHdr + 1)
    (hr_info : r.L = ctx.L ∧ r.vCap = ctx.vCap ∧ r.eCap = ctx.eCap ∧ r.b = ctx.b ∧ r.j = ctx.j)
    (hFinPost : (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
        uhTailHdr r ctx.G' ctx.eAff
        (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev) (fun _ => False)
        ctx.eAffPtr retSp heapFin).post
        ([dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dgEPresBase (memSp ctx.scratchPtr) ctx.vCap, uhTailHdr + 1,
          dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap, jtEList.length,
          dgEPresBase (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap,
          dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, uhTailHdr] ++
         [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b,
          dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap, jtEList.length] ++
         [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
          ctx.j + 1, ctx.j, ctx.L + 1] ++
         [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, retSp, heapFin])
        memReemb retFin memFin) :
    memFin (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) + 1 + ctx.eAff.length ∧
    (∀ a, dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a → a < retSp →
      memFin a = memReemb a) := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  obtain ⟨hgb_jt, hjt_sp, hlt_scr_ag⟩ := hSpInfo
  obtain ⟨hc_v, hc_e, hc_out⟩ := hc_info
  obtain ⟨hr_L, hr_v, hr_e, hr_b, hr_j⟩ := hr_info
  rcases hFinPost with ⟨midFin, _, hTailPost, hSLWPost⟩
  have hTailFr := hTailPost.2.2.2.2.2.2.2.2
  rcases hSLWPost with ⟨_, _, _, hSLW_args, hSLW_rest⟩
  have hSLW_ge := hSLW_rest.1
  have hSLW_gen := hSLW_rest.2.2.1
  have hSLW_fr := hSLW_rest.2.2.2.2.2.2.2.2.2
  simp only [List.cons.injEq, and_true] at hSLW_args
  obtain ⟨-, -, rfl, -, rfl, rfl⟩ := hSLW_args
  clear hTailPost hSLW_rest
  have hfix_le_retSp : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ retSp := by omega
  have hretSp_le_hf : retSp ≤ heapFin := by omega
  have hretSp_le_hdr : retSp ≤ uhTailHdr := by omega
  have hjle : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hgen_re : memReemb (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) :=
    (hRe_lt _ (lt_of_lt_of_le hgo.2.2.2.2.2.2 hfix_le_retSp)).trans
      (hlt_scr_ag _ (by omega) (fun v hv => by omega))
  have hgen_mid : midFin (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) := by
    rw [← hgen_re]
    refine hTailFr _ (Or.inl (lt_of_lt_of_le hgo.2.2.2.2.2.2 (le_trans hfix_le_retSp hretSp_le_hdr)))
      (Or.inl (by rw [hr_b, hr_v, hr_e]; exact hgo.2.1))
      (Or.inl (by rw [hr_b, hr_v, hr_e]; exact hgo.2.2.1)) (fun hg => ?_)
    dsimp only [RBCtx.GenWord] at hg; rw [hr_b, hr_L, hr_v, hr_e] at hg
    rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  refine ⟨by rw [hr_b] at hSLW_gen; rw [hSLW_gen, hgen_mid], fun a ha1 ha2 => ?_⟩
  have hfr_slw : memFin a = midFin a := by
    refine hSLW_fr a ?_
    rw [hr_b, hr_L, hr_v, hr_e, hr_j]
    exact slw_frame_of_range hjle (le_trans hfix_le_retSp hretSp_le_hf) hSLW_ge
      (Or.inr (Or.inr (Or.inl ⟨ha1, lt_of_lt_of_le ha2 hretSp_le_hf⟩)))
  rw [hfr_slw]
  have htf := tail_frame_of_range (b := ctx.b) (L := ctx.L) (vCap := ctx.vCap)
    (eCap := ctx.eCap) (hdr := uhTailHdr) (c_size := c.size) (a := a)
    (le_trans hfix_le_retSp hretSp_le_hdr)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, lt_of_lt_of_le ha2 hretSp_le_hdr⟩))))
  refine hTailFr a (by rw [hc_out]; exact htf.1)
    (by rw [hr_b, hr_v, hr_e, hc_v, hc_e]; exact htf.2.1)
    (by rw [hr_b, hr_L, hr_v, hr_e]; exact htf.2.2.1)
    (fun hg => htf.2.2.2 (by
      dsimp only [RBCtx.GenWord] at hg; rw [hr_b, hr_L, hr_v, hr_e] at hg
      rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨le_trans (Nat.le_add_right _ _) h1, h2⟩
      · exact Or.inr ⟨le_trans (Nat.le_add_right _ _) h1, h2⟩))

/-- Build `DCtx` on `memGen` right after `dsStepFinish` and incrementing `gen`. -/
theorem stepPosNE_dCtx (ctx : StepPosNECtx) {memSp memReemb memFin memGen : ℕ → ℕ}
    {retSp retReemb heapFin uhTailHdr : ℕ} {jtEList : List ℕ}
    (hJt_E : ctx.out.Jtilde.E ⊆ ctx.E_aff)
    (hembCap : ∀ e ∈ ctx.E_aff, ∀ x ∈ ctx.embJH e, x.1 < ctx.eCap)
    (hhf : heapFin = retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
      3 * (retReemb - (retSp + ctx.eCap)))
    (hhdr : uhTailHdr = heapFin + 2 * (retReemb - (retSp + ctx.eCap)))
    (hSpInfo : ctx.guestBase ≤ memSp ctx.scratchPtr ∧
      memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp ∧
      retSp ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase ctx.G' ctx.J ctx.embJH +
        dsShortcutHeapSpace ctx.eAff ctx.out.emb ∧
      (∀ addr, addr < ctx.scratchPtr →
        (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
        memSp addr = ctx.memAff addr))
    (hRe_lt : ∀ addr, addr < retSp → memReemb addr = memSp addr)
    (hRe_le : retReemb - (retSp + ctx.eCap) ≤
      reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff)
    (hjt_info : jtEList.Nodup ∧ jtEList.length = ctx.out.Jtilde.m ∧
      (∀ e, e ∈ jtEList ↔ e ∈ ctx.out.Jtilde.E) ∧
      ListAt memReemb (dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap) jtEList)
    (hFinFr : memFin (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) + 1 + ctx.eAff.length ∧
      (∀ a, dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a → a < retSp →
        memFin a = memReemb a))
    (hGenEq : memGen = Function.update memFin (ctx.b + dsGenOff) (memFin (ctx.b + dsGenOff) + 1)) :
    let dPtr := uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m
    let jtEListPtr := dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap
    ∃ dc : DCtx,
      dc.w = ctx.w ∧ dc.eCap = ctx.eCap ∧ dc.T = ctx.embJH ∧ dc.es = jtEList ∧
      dc.esPtr = jtEListPtr ∧ dc.tab = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dc.stamp = dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dc.g = memGen (ctx.b + dsGenOff) ∧ dc.out = dPtr ∧ dc.mem0 = memGen ∧
      dTotal ctx.embJH jtEList ≤ 2 * ctx.lenSum + ctx.eAff.length := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  obtain ⟨hgb_jt, hjt_sp, hretSp_le, hlt_scr_ag⟩ := hSpInfo
  obtain ⟨hjt_nd, hjt_len, hjt_iff, hjt_at⟩ := hjt_info
  obtain ⟨hgen_fin, hfin_re⟩ := hFinFr
  have hgen_g : memGen (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) + 2 + ctx.eAff.length := by
    rw [hGenEq, Function.update_self, hgen_fin]; omega
  have hag_fin_re : ∀ a, dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a → a < retSp →
      memGen a = memReemb a := by
    intro a ha1 ha2
    have hne_g : a ≠ ctx.b + dsGenOff := by omega
    rw [hGenEq, Function.update_of_ne hne_g]
    exact hfin_re a ha1 ha2
  have hAff_mpr : ∀ e, e ∈ ctx.E_aff → e ∈ ctx.eAff := fun e he => (ctx.hAff_iff e).mpr he
  have hdTot : dTotal ctx.embJH jtEList ≤ 2 * ctx.lenSum + ctx.eAff.length := by
    have hproj_eq : projWalk ctx.G' ctx.G' ctx.piLt_mid ctx.S_prev = ctx.embJH := by
      funext e
      exact projWalk_congr_host (G' := ctx.G') (H_lt := ctx.H_lt)
        (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).tail = ctx.G'.tail)
        (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).head = ctx.G'.head) _ _ _
    rw [← hproj_eq]
    exact dTotal_jt_le ctx.hAff_eNd hjt_nd fun e he => hAff_mpr e (hJt_E ((hjt_iff e).mp he))
  let dPtr := uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m
  have hEnd_d : dPtr + (2 * ctx.lenSum + ctx.eAff.length) < 2 ^ ctx.w := by
    have h1 := ctx.dPtr_lt hretSp_le hRe_le
    have hhdr' : uhTailHdr = retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
        5 * (retReemb - (retSp + ctx.eCap)) := by omega
    show uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m +
        (2 * ctx.lenSum + ctx.eAff.length) < 2 ^ ctx.w
    rw [hhdr']
    exact h1
  have hprojH : projHeapNeed ctx.piLt_mid ctx.eAff ≤ 14 * ctx.lenSum + 15 * ctx.eAff.length :=
    projHeapNeed_le_linear ctx.piLt_mid ctx.eAff
  have hwp_le_scr : ctx.wpPtr + ctx.eAff.length + projHeapNeed ctx.piLt_mid ctx.eAff ≤
      ctx.scratchPtr := by omega
  clear hGenEq hRe_le hfin_re hgen_fin
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hGE'_cap : ∀ e ∈ ctx.G'.E, e < ctx.eCap := fun e he =>
    ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu.2 he)
  have hjt_le_cap : jtEList.length ≤ ctx.eCap := by
    have hsub : jtEList.toFinset ⊆ Finset.range ctx.eCap := by
      intro e he
      exact Finset.mem_range.mpr
        (hGE'_cap e (Finset.mem_filter.mp (hJt_E ((hjt_iff e).mp (List.mem_toFinset.mp he)))).1)
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hjt_nd, Finset.card_range] at hcard
    exact hcard
  have hag_gen_aff : ∀ a, dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a → a < ctx.scratchPtr →
      memGen a = ctx.memAff a := by
    intro a ha1 ha2
    have hscr_lt_ret : ctx.scratchPtr < retSp := by omega
    have hvst_lt_a : ∀ v < ctx.vCap, a ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v := by
      intro v hv; omega
    exact (hag_fin_re a ha1 (lt_trans ha2 hscr_lt_ret)).trans
      ((hRe_lt a (lt_trans ha2 hscr_lt_ret)).trans (hlt_scr_ag a ha2 hvst_lt_a))
  have hmt_in : ∀ e < ctx.eCap, dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ≤
      dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e ∧
      dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e < ctx.scratchPtr := by
    intro e he; omega
  have hest_in : ∀ e < ctx.eCap, dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ≤
      dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + e ∧
      dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + e < ctx.scratchPtr := by
    intro e he; omega
  have hest_le_wp : dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap ≤ ctx.wpPtr + ctx.eAff.length := by
    omega
  have hscr_le_dPtr : ctx.scratchPtr ≤ dPtr := by omega
  have hdPtr_lt_w : dPtr < 2 ^ ctx.w := by omega
  have hDC_arith :
      dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap + jtEList.length < 2 ^ ctx.w ∧
      dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap < 2 ^ ctx.w ∧
      dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap < 2 ^ ctx.w ∧
      dPtr + dTotal ctx.embJH jtEList < 2 ^ ctx.w ∧
      ctx.memAff (ctx.b + dsGenOff) + 2 + ctx.eAff.length < 2 ^ ctx.w ∧
      dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap ≤
        dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ∧
      dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap ≤
        dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap + jtEList.length ≤ dPtr ∧
      dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap ≤ dPtr ∧
      dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap ≤ dPtr ∧
      dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ≤
        dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ∧
      dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap + jtEList.length ≤ retSp := by
    have := ctx.hGen_ltw
    dsimp only [dgEListBase, dynGraphSize] at hjt_sp ⊢
    omega
  clear hfl hch hgo hEnd_d hjt_sp hgb_jt hretSp_le hprojH hdu hjt_le_cap hhf hhdr hRe_lt hlt_scr_ag
  let dc : DCtx :=
    { w := ctx.w, eCap := ctx.eCap, T := ctx.embJH, es := jtEList
      esPtr := dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap
      tab := dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap
      stamp := dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap
      g := memGen (ctx.b + dsGenOff), out := dPtr, mem0 := memGen
      hw16 := ctx.hw16
      hesB := hDC_arith.1
      htB := hDC_arith.2.1
      hsB := hDC_arith.2.2.1
      hoB := hDC_arith.2.2.2.1
      hg := hgen_g.symm ▸ hDC_arith.2.2.2.2.1
      dSE := Or.inl hDC_arith.2.2.2.2.2.1
      dST := Or.inl hDC_arith.2.2.2.2.2.2.1
      dOE := Or.inr hDC_arith.2.2.2.2.2.2.2.1
      dOT := Or.inr hDC_arith.2.2.2.2.2.2.2.2.1
      dOS := Or.inr hDC_arith.2.2.2.2.2.2.2.2.2.1
      hes := listAt_of_agree (fun k' hk' =>
        hag_fin_re _ (le_trans hDC_arith.2.2.2.2.2.2.2.2.2.2.1 (Nat.le_add_right _ _))
          (lt_of_lt_of_le (Nat.add_lt_add_left hk' _) hDC_arith.2.2.2.2.2.2.2.2.2.2.2)) hjt_at
      hk := fun k' hk' => by
        let e := jtEList[k']
        have he_jt : e ∈ ctx.out.Jtilde.E := (hjt_iff e).mp (List.getElem_mem hk')
        have he_aff : e ∈ ctx.E_aff := hJt_E he_jt
        have he_mem : e ∈ ctx.eAff := hAff_mpr e he_aff
        have heC : e < ctx.eCap := hGE'_cap e (Finset.mem_filter.mp he_aff).1
        obtain ⟨hemb_ge, h1, hmw⟩ := hAff_emb_clean ctx he_mem
        have hemb_bnd : ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e) +
            (2 * (ctx.embJH e).length + 1) ≤ ctx.scratchPtr :=
          le_trans h1 hwp_le_scr
        have htab_eq : memGen (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e) =
            ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e) :=
          hag_gen_aff _ (hmt_in e heC).1 (hmt_in e heC).2
        have hW : MWalkAt memGen (memGen (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e))
            (ctx.embJH e) := by
          rw [htab_eq]
          exact hmw.of_agree fun a ha1 ha2 =>
            hag_gen_aff a (le_trans (le_trans (Nat.le_add_right _ _) hest_le_wp) (le_trans hemb_ge ha1))
              (lt_of_lt_of_le (by
                have hadd : ∀ p m : ℕ, p + 1 + m = p + (m + 1) := fun p m => by omega
                rw [← hadd]; exact ha2) hemb_bnd)
        refine ⟨heC, hW, by rw [htab_eq]; exact lt_of_le_of_lt (le_trans hemb_bnd hscr_le_dPtr) hdPtr_lt_w,
          Or.inl (by rw [htab_eq]; exact le_trans hest_le_wp hemb_ge),
          Or.inr (by rw [htab_eq]; exact le_trans hemb_bnd hscr_le_dPtr),
          fun y hy => hembCap e he_aff y hy⟩
      hstamp := fun x hx => by
        rw [hag_gen_aff _ (hest_in x hx).1 (hest_in x hx).2, hgen_g]
        exact lt_of_le_of_lt (ctx.hAff_eStamp x hx)
          (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) (Nat.le_add_right _ _)) }
  exact ⟨dc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hdTot⟩

end

end MinCostFlow.DynSpanner.Program
