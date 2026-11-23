module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullCtx
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPos
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullPre
import WordRAM.Tactic

/-!
# The whole step of Algorithm 6 for `0 < j`: the contract theorem

Proves `dsStepPosFull_meetsContract`: `dsStepPosFullStmt` (`DynSpannerStepPosFullDefs.lean`),
run on the state before the step, ends in the post `StepOutPost` of a step, with its heap below
`dsStepPosFullEnd` and its cost below `dsStepPosFullCost`.

The proof follows the procedure. It computes the addresses of the state block, then calls
`dsStepHead` with the preconditions of `stepPos_updS_pre` and `stepPos_prefix_pre`, `dsWordSum`
for the total length of the buckets of the levels `j, …, L` (`wordSum_eq_oldSum`), and `dsAffStage` on the context that
`buildAffCtx_of_stepHead` builds. Then it reads the lengths of the lists of `S_{j-1}` and of
the candidates from the heap, and calls `dsStepPos` on the context `stepPosFullCtx`, whose post is
the post of the step.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

private lemma list_sum_range_eq (f : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- Evaluate a list of register arguments, reading each register through the updates of the
register file and not through the hypotheses (which may be large). -/
local macro "eval_regs" : tactic =>
  `(tactic| (repeat (first
      | exact evalArgs_nil _ _
      | refine evalArgs_cons (Expr.eval_reg_of_eq ?_) ?_
        (try simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, startState,
          List.getD_cons_zero, List.getD_cons_succ, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some])
        (try rfl))))

public section

/-- The words `hDeg[i]` for `j ≤ i ≤ L` add up to the total length of the buckets of these
levels. -/
lemma wordSum_eq_oldSum {mem : ℕ → ℕ} {L vCap eCap b j : ℕ} {B : ℕ → List ℕ}
    (hB : BucketsAt mem L vCap eCap b B) (hj : j ≤ L + 1) :
    ∑ i ∈ Finset.Ico j (L + 1), mem (dsHDegDummyBase b L vCap eCap + i) =
      (bucketsCat B j (L + 1 - j)).length := by
  rw [bucketsCat_length_eq_sum_range, list_sum_range_eq, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Finset.mem_range.mp hd
  exact (hB (j + d) (by omega)).2

/-- The arguments of `dsStepPos` are below the end of the heap of the step, so they are words. -/
lemma StepPosCtx.args_lt (ctx : StepPosCtx) :
    ctx.eAffPtr + ctx.eAff.length + ctx.cand.length + ctx.oldBucketsSum + ctx.prefWords <
      2 ^ ctx.w := by
  have h : ctx.midEnd + ctx.prefWords + 4 * ctx.res.UH.length < 2 ^ ctx.w := ctx.hEnd_ltw
  simp only [StepPosCtx.midEnd, StepPosCtx.wpPtr, StepPosCtx.retAffE, StepPosCtx.eAffPtr] at h ⊢
  split_ifs at h
  · simp only [dsStepPosNonEmptyEnd, spOutBound] at h
    refine Nat.lt_of_le_of_lt ?_ h
    generalize ctx.J.m * (1 + 2 * ⌈ctx.impl.γ_ℓ ctx.mMax⌉₊) = P
    generalize 2 ^ (wordSize ctx.impl.cw (canonSparsifyInput ctx.G' ctx.J ctx.embJH) + 1) = Q
    omega
  · omega

set_option maxHeartbeats 2000000 in
/-- The whole step of Algorithm 6 (Theorem 8.2, page 64) for `0 < j`: `dsStepPosFullStmt` meets
`dsStepPosFullContract`. -/
theorem dsStepPosFull_meetsContract (m : StepPosModel) (mMax w vCap eCap b len : ℕ)
    (x : DynSpannerMeta m.L) {p : Program} {bs : StepPosFullBases}
    (hp : HasStepPosFullProcs m.impl p bs) :
    MeetsContract w p (bs.bFull + stepPosFullIdx)
      (dsStepPosFullContract m mMax w vCap eCap b len x) := by
  refine meetsContract_of_runs
    (hp.hFull.get (i := stepPosFullIdx) (by simp [stepPosFullProcs, stepPosFullIdx])) ?_
  rintro args mem pos ω hW ⟨updPtr, heapStep, rfl, hw16, hL1, hq, hVG₀, hGm₀, hE₀_cap, hBV, hds,
    hu_some, hj_pos, hPref, hRev, hState, hfix, hfoot, hZero, hEnd, hAffEnd, hGen, ht, hfixU,
    hupd_le, hupd_foot, hupd_w, hupd_at, hupd_cap⟩
  simp only [stepPosFullProcs, stepPosFullIdx, List.getElem_cons_zero]
  dsimp only [dsStepPosFullStmt]
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14, hl15, hl16,
    hl17, hl18, hl19, hl20⟩ := stepPosLayout b m.L vCap eCap
  have hpos := dsFixedSize_pos m.L vCap eCap
  have hmL : mem (b + dsLOff) = m.L := hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmV : mem (b + dsVCapOff) = vCap := hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmE : mem (b + dsECapOff) = eCap := hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hjL : m.j ≤ m.L := chooseLevel_le m.L m.q (m.k + 1)
  have hjj : m.j = chooseLevel m.L m.q (m.k + 1) := rfl
  have hAE := hAffEnd
  simp only [dsStepPosFullAffEnd] at hAE
  have hLo : dsLOff < dsHdrSize := by decide
  have hVo : dsVCapOff < dsHdrSize := by decide
  have hEo : dsECapOff < dsHdrSize := by decide
  -- The word bounds of the addresses, from the bound on the end of the heap of the stage.
  have hwHS : heapStep + 5 + len + 4 * m.j < 2 ^ w := by omega
  have hwV : vCap < 2 ^ w := by omega
  have hwE : eCap < 2 ^ w := by omega
  have hwD : dynGraphSize vCap eCap < 2 ^ w := by omega
  have hwG : dsGPtr b < 2 ^ w := by omega
  have hwH : dsHPtr b vCap eCap < 2 ^ w := by omega
  have hwM : dsMinHBase b vCap eCap < 2 ^ w := by omega
  have hwP : dsHPtr b vCap eCap + 4 + 7 * vCap < 2 ^ w := by omega
  have hwP' : dsHPtr b vCap eCap + 4 < 2 ^ w := by omega
  have hw7V : 7 * vCap < 2 ^ w := by omega
  have hw9E : 9 * eCap < 2 ^ w := by omega
  have hw47 : 4 + 7 * vCap < 2 ^ w := by omega
  have hwGH : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hwHH : dsHPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hwS5 : heapStep + 5 < 2 ^ w := by omega
  have hwS5L : heapStep + 5 + len < 2 ^ w := by omega
  have hwbV : b + dsVCapOff < 2 ^ w := by omega
  have hwbE : b + dsECapOff < 2 ^ w := by omega
  have hwbH : b + dsHdrSize < 2 ^ w := by omega
  have hw4j : 4 * m.j < 2 ^ w := by omega
  have hc1 : 1 < 2 ^ w := by omega
  have hc2 : 2 < 2 ^ w := by omega
  have hc3 : 3 < 2 ^ w := by omega
  have hc4 : 4 < 2 ^ w := by omega
  have hc5 : 5 < 2 ^ w := by omega
  have hc7 : 7 < 2 ^ w := by omega
  have hc9 : 9 < 2 ^ w := by omega
  have hcH : dsHdrSize < 2 ^ w := by omega
  have hcL : dsLOff < 2 ^ w := by omega
  have hcV : dsVCapOff < 2 ^ w := by omega
  have hcE : dsECapOff < 2 ^ w := by omega
  have hwj : m.j < 2 ^ w := by omega
  have hwU : updPtr < 2 ^ w := by omega
  have hwb : b < 2 ^ w := by omega
  have hgj : mem (b + dsGenOff) + m.j < 2 ^ w := by omega
  have hupw : updPtr + len < 2 ^ w := by omega
  have hfixS5 : b + dsFixedSize m.L vCap eCap ≤ heapStep + 5 := by omega
  have hfixw : b + dsFixedSize m.L vCap eCap < 2 ^ w := by omega
  have hfootS5 : ∀ a, heapFoot x a → a < heapStep + 5 + len := fun a ha => by
    have := hfoot a ha; omega
  have hfootS : ∀ a, heapFoot x a → a < heapStep + 5 := fun a ha => by
    have := hfoot a ha; omega
  have hfixS : b + dsFixedSize m.L vCap eCap ≤ heapStep + 5 + len := by omega
  have hupd5 : updPtr + len ≤ heapStep + 5 + len := by omega
  have hupd55 : heapStep + 5 + len ≤ heapStep + 5 + len := le_rfl
  have hwL1 : m.L + 1 < 2 ^ w := by omega
  have hwbL : b + dsLOff < 2 ^ w := by omega
  have hHD : dsMinHBase b vCap eCap + 3 * eCap + (m.L + 1) = dsHDegDummyBase b m.L vCap eCap ∧
      True := ⟨by omega, trivial⟩
  have hwHD : dsHDegDummyBase b m.L vCap eCap + (m.L + 1) < 2 ^ w := by omega
  have hw3E : 3 * eCap < 2 ^ w := by omega
  have hwM3 : dsMinHBase b vCap eCap + 3 * eCap < 2 ^ w := by omega
  have hwM3L : dsMinHBase b vCap eCap + 3 * eCap + (m.L + 1) < 2 ^ w := by omega
  have hwHA : heapStep + 5 + len + 4 * m.j + 2 < 2 ^ w := by omega
  -- Hide the big bounds behind variables, so that `assumption` does not unfold them.
  clear hAE
  generalize hEndV : dsStepPosFullEnd m mMax vCap eCap len x heapStep = endV at hEnd
  generalize hAffV : dsStepPosFullAffEnd m vCap eCap len heapStep = affV at hAffEnd
  replace hEndV := And.intro hEndV True.intro
  replace hAffV := And.intro hAffV True.intro
  refine runs_start_le ?_
  -- The addresses of the state block.
  refine runs_seq_assign_le (v := vCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := eCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap) (by rw [hl20]; eval_expr) ?_
  refine runs_seq_assign_le (v := dsGPtr b) (by rw [hl18]; eval_expr) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap) (by rw [← hl3]; eval_expr) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap) (by rw [← hl5, ← hl4]; eval_expr) ?_
  refine runs_seq_assign_le (v := dgEPresBase (dsHPtr b vCap eCap) vCap)
    (by
      rw [hl19]
      exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const hc4) hwP')
        (Expr.eval_mul (Expr.eval_const hc7) (Expr.eval_reg_of_eq (by simp [startState])) hw7V)
        hwP) ?_
  refine runs_seq_assign_le (v := heapStep + 5) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heapStep + 5 + len) (by eval_expr) ?_
  -- Call 1: `dsStepHead`.
  refine runs_seq_call_le (vs := [b, m.j, updPtr, heapStep + 5 + len, dsGPtr b,
      dsHPtr b vCap eCap, dsMinHBase b vCap eCap, dgEPresBase (dsHPtr b vCap eCap) vCap,
      heapStep + 5])
    (dsStepHead_meetsContract (w := w) (L := m.L) (vCap := vCap) (eCap := eCap) (b := b)
      (j := m.j) (G := m.st.G) (H := m.st.H) (u := m.u) (len := len) (B := stepPosBmid0 x)
      (S_level := m.st.S_level) (sLists := x.sLists) (foot0 := heapFoot x) (updPtr := updPtr)
      (heapPtr := heapStep + 5 + len) (out := heapStep + 5)
      hp.hAffP hp.hPos.hNE.hpBatch hp.hPos.hNE.hpEdge hp.hPos.hNE.hpSplit hp.hPos.hNE.hpOps
      hp.hPos.hNE.hpPhase hp.hD hp.hU hp.hF hp.hR hp.hPref hp.hHead)
    (by rw [hl19]; eval_regs)
    (by wram_words)
    ⟨rfl, stepPos_updS_pre (len := len) (updPtr := updPtr)
      (heapPtr := heapStep + 5 + len) hBV hds hu_some hPref hw16 hj_pos hState hfixS
      hfootS5 hwHS hgj hupw hupd_at hupd_cap,
     stepPos_prefix_pre (len := len) (updPtr := updPtr) (heapStep := heapStep)
      hBV hds hu_some hPref hw16 hState hfix hwS5L hupd_le hupd_foot hupd_w hupd_at hupd_cap,
     hfixU, Or.inl hupd5, Or.inl hupd55⟩ ?_
  rintro prefWords mem2 pos₂ ⟨mid, r₁, hUpdS, hPrefP⟩
  -- The facts after `dsStepHead`.
  have hHeadPost := And.intro hUpdS hPrefP
  obtain ⟨_, _, hargsS, hr₁lo, hr₁hi, hgen₁, hgen₂, _, _, hfrS⟩ := hUpdS
  simp only [List.cons.injEq, and_true] at hargsS
  obtain ⟨_, _, rfl, rfl⟩ := hargsS
  dsimp only [startState] at hgen₁ hgen₂ hfrS
  obtain ⟨hpw, hPrefBody, hG', hHmid, hBk, hminP, hfrP⟩ := hPrefP
  have hkeep := stepPosHead_keep hfix hr₁hi hfrS hfrP
  have hm2L : mem2 (b + dsLOff) = m.L := by
    rw [hkeep.1 _ (by rw [hl18]; omega) (by simp only [dsLOff, dsGenOff]; omega)]; exact hmL
  have hgen2 : mem2 (b + dsGenOff) + 1 < 2 ^ w := by rw [hkeep.2.2.2.2.1]; omega
  -- The context of `dsAffStage`.
  obtain ⟨sLists', a, haw, haL, havC, haeC, hab, haj, hah, haG, haH, hapi, haS, has, ham, haF,
      haE, haCs, haC, hSL2⟩ :=
    buildAffCtx_of_stepHead (heapAff := heapStep + 5 + len + 4 * m.j) hVG₀ hL1 hq hGm₀
      (canonicalSparsify_spec_absorb m.impl mMax) hE₀_cap hBV hds hu_some hPref hRev hj_pos hw16
      hState hG'.2.1 hfootS hfixS5 le_rfl le_rfl
      hfixw hwS5 hgen2 hHeadPost
  refine runs_seq_assign_le (v := heapStep + 5 + len + 4 * m.j) (by eval_expr) ?_
  refine runs_seq_assign_le (v := m.L + 1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap + 3 * eCap + (m.L + 1)) (by eval_expr) ?_
  -- Call 2: the total length of the buckets of the levels `j, …, L`.
  have hsum := wordSum_eq_oldSum hBk (Nat.le_succ_of_le hjL)
  rw [← hHD.1] at hsum
  have hOld := stepPosOldSum_le_end m mMax vCap eCap len x heapStep
  rw [hEndV.1] at hOld
  refine runs_seq_call_le (vs := [dsMinHBase b vCap eCap + 3 * eCap + (m.L + 1), m.j, m.L + 1])
    (dsWordSum_meetsContract (w := w) (base := dsMinHBase b vCap eCap + 3 * eCap + (m.L + 1))
      (lo := m.j) (hi := m.L + 1) hp.hSum)
    (by eval_expr) (by wram_words)
    ⟨rfl, by omega, by omega, by omega, by rw [hsum]; exact lt_of_le_of_lt hOld hEnd⟩ ?_
  rintro oldS mem3 pos₃ ⟨hm3, hOldS⟩
  subst mem3
  rw [hsum] at hOldS
  subst hOldS
  -- Call 3: `dsAffStage`.
  have hAS : MeetsContract w p (bs.bAS + affStageIdx) (dsAffStageContract a) :=
    haw ▸ dsAffStage_meetsContract a hp.hAffP hp.hPos.hNE.hpOps hp.hPos.hNE.hpEdge hp.hProj
      hp.hPos.hNE.hpEmb hp.hBP hp.hWP hp.hPS hp.hAS
  have hpreA : (dsAffStageContract a).pre [b, m.j, heapStep + 5 + len + 4 * m.j] mem2 := by
    have hB : a.heapPtr + 2 + a.vCap + 3 * a.eCap +
        ∑ e ∈ a.G'.E, (14 * (a.piLt_mid e).length + 15) < 2 ^ a.w := by
      rw [hah, havC, haeC, haG, hapi, haw]
      have h := hAffEnd
      rw [← hAffV.1] at h
      exact h
    have h := stepPosAff_pre a hB
    rw [hab, haj, hah, ham] at h
    exact h
  refine runs_seq_call_le (vs := [b, m.j, heapStep + 5 + len + 4 * m.j]) hAS
    (by eval_regs) (by wram_words) hpreA ?_
  rintro eAffLen memAff pos₄ hpostA
  obtain ⟨cand, eAff, rfl, hA⟩ :=
    stepPosAff_facts a haL havC haeC hab hah haG hapi haS has ham haF haE hpostA
  -- The context of `dsStepPos`.
  have hjL1 : m.j - 1 < m.L + 1 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le hjL)
  have hSprev := hSL2 ⟨m.j - 1, hjL1⟩
  simp only [show m.j - 1 < m.j by omega, ↓reduceIte] at hSprev
  have hsp_card : (sLists' ⟨m.j - 1, hjL1⟩).length = m.S_prev.card :=
    list_length_eq_card hSprev.2.2.2.2.1 hSprev.2.2.2.2.2.1
  have hsp_perm : (sLists' ⟨m.j - 1, hjL1⟩).Perm m.S_prev.toList :=
    perm_toList_of_nodup_iff hSprev.2.2.2.2.1 hSprev.2.2.2.2.2.1
  have hcand : cand.length ≤ m.G'.m := by
    have hsub : cand.toFinset ⊆ m.G'.E := fun e he => hA.2.1 e (List.mem_toFinset.mp he)
    rw [← List.toFinset_card_of_nodup hA.1]
    exact Finset.card_le_card hsub
  have hendle := stepPosFull_end_le m mMax vCap eCap len x heapStep (sPrevList :=
    sLists' ⟨m.j - 1, hjL1⟩) (cand := cand) hA.2.2.1 hA.2.2.2.1 hcand hsp_card hpw
  have hEnd' : dsStepPosFullEnd m mMax vCap eCap len x heapStep < 2 ^ w := by
    rw [hEndV.1]; exact hEnd
  let ctx := stepPosFullCtx m mMax w vCap eCap b len x mem mid mem2 memAff heapStep r₁ prefWords
    sLists' cand eAff hw16 hVG₀ hq hGm₀ hE₀_cap hBV hds hu_some hPref hj_pos hRev hState hfix hfoot
    hZero hEnd' hGen ht hr₁lo hr₁hi hgen₁ hgen₂ hfrS hfrP hpw hPrefBody hG' hHmid hBk hminP hSL2 hA
  have hargs : heapStep + 5 + len + 4 * m.j + 2 + (sLists' ⟨m.j - 1, hjL1⟩).length +
      cand.length + eAff.length + cand.length + stepPosOldSum m.u x m.j + prefWords < 2 ^ w :=
    StepPosCtx.args_lt ctx
  have hmS : memAff (heapStep + 5 + len + 4 * m.j) = (sLists' ⟨m.j - 1, hjL1⟩).length :=
    hA.2.2.2.2.1
  have hmC : memAff (heapStep + 5 + len + 4 * m.j + 1) = cand.length := hA.2.2.2.2.2.1
  have hwSl : (sLists' ⟨m.j - 1, hjL1⟩).length < 2 ^ w := by omega
  have hwCl : cand.length < 2 ^ w := by omega
  have hwA1 : heapStep + 5 + len + 4 * m.j + 1 < 2 ^ w := by omega
  have hwA2S : heapStep + 5 + len + 4 * m.j + 2 + (sLists' ⟨m.j - 1, hjL1⟩).length < 2 ^ w := by
    omega
  have hwPtr : heapStep + 5 + len + 4 * m.j + 2 + (sLists' ⟨m.j - 1, hjL1⟩).length +
      cand.length < 2 ^ w := by omega
  refine runs_seq_assign_le (v := (sLists' ⟨m.j - 1, hjL1⟩).length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := cand.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heapStep + 5 + len + 4 * m.j + 2 +
    (sLists' ⟨m.j - 1, hjL1⟩).length + cand.length) (by eval_expr) ?_
  -- Call 4: `dsStepPos`.
  refine runs_seq_call_le (vs := [b, m.j, heapStep + 5 + len + 4 * m.j + 2 +
      (sLists' ⟨m.j - 1, hjL1⟩).length + cand.length, eAff.length, cand.length,
      stepPosOldSum m.u x m.j, heapStep, prefWords, heapStep + 5 + len + 4 * m.j,
      (sLists' ⟨m.j - 1, hjL1⟩).length])
    (dsStepPos_meetsContract ctx hp.hPos) (by eval_regs) (by wram_words) ⟨rfl, rfl⟩ ?_
  rintro ret0 mem' pos₅ ⟨hpost, hret, hgenP, huhP, hAffAt, hAffLe⟩
  have hret2_le : ret0 + 2 ≤ dsStepPosFullEnd m mMax vCap eCap len x heapStep := by
    have h1 : ret0 + 2 ≤ ctx.midEnd + prefWords + 4 * m.res.UH.length + 2 := Nat.add_le_add_right hret 2
    exact le_trans h1 hendle
  have hret2_lt : ret0 + 2 < 2 ^ w := lt_of_le_of_lt hret2_le hEnd'
  have hret1_lt : ret0 + 1 < 2 ^ w := by omega
  have hret0_lt : ret0 < 2 ^ w := by omega
  have hret0_ge_hs5 : heapStep + 5 ≤ ret0 := by
    obtain ⟨uhP, uhW, dP, _, dL, _, _, _, _, _, _, hdP, hdL, huh, _⟩ := hpost
    dsimp only [ctx, stepPosFullCtx] at hdP
    omega
  refine runs_seq_store_le (x := ret0)
    (v := heapStep + 5 + len + 4 * m.j + 2 + (sLists' ⟨m.j - 1, hjL1⟩).length + cand.length)
    (Expr.eval_reg_of_eq (by simp))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := ret0 + 1) (v := eAff.length)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const hc1) hret1_lt)
    (Expr.eval_reg_of_eq (by simp)) ?_
  let memFinal := Function.update
    (Function.update mem' ret0
      (heapStep + 5 + len + 4 * m.j + 2 + (sLists' ⟨m.j - 1, hjL1⟩).length + cand.length))
    (ret0 + 1) eAff.length
  have hgenF : memFinal (b + dsGenOff) ≤ mem (b + dsGenOff) + m.j + 3 + m.G'.m := by
    have hJm : ctx.J.m ≤ m.G'.m := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : ctx.mem2 (b + dsGenOff) ≤ mem (b + dsGenOff) + m.j := by
      show mem2 (b + dsGenOff) ≤ _
      rw [hkeep.2.2.2.2.1]; exact hgen₂
    have hP : mem' (b + dsGenOff) ≤ ctx.mem2 (b + dsGenOff) + 3 + ctx.J.m := hgenP
    have hne0 : b + dsGenOff ≠ ret0 := by simp only [dsGenOff] at *; omega
    have hne1 : b + dsGenOff ≠ ret0 + 1 := by simp only [dsGenOff] at *; omega
    simp only [memFinal, Function.update_of_ne hne1, Function.update_of_ne hne0]
    omega
  have huhF : memFinal (heapStep + 2) ≤ len + 4 * m.res.UH.length := by
    have hne0 : heapStep + 2 ≠ ret0 := by omega
    have hne1 : heapStep + 2 ≠ ret0 + 1 := by omega
    simp only [memFinal, Function.update_of_ne hne1, Function.update_of_ne hne0]
    exact le_trans huhP (Nat.add_le_add_right hpw _)
  have hReembSet : eAff.toFinset = stepReembSet m.st m.u := by
    have hk := hPref m.k le_rfl
    have hjne : chooseLevel m.L m.st.q (m.st.t + 1) ≠ 0 := by
      rw [hk.q_eq, hk.t_eq]; exact Nat.ne_of_gt hj_pos
    rw [stepReembSet_eq_pos m.st m.u hjne]
    simp only [hk.q_eq, hk.t_eq]
    ext e
    rw [List.mem_toFinset]
    exact hA.2.2.2.1 e
  have hReembPost : StepReembOutPost m.G₀ m.L m.q vCap eCap b m.k m.impl m.us m.u mem x heapStep
      memFinal (ret0 + 2) :=
    ⟨mem', ret0, ctx.eAffPtr, eAff, rfl, hpost, rfl, hA.2.2.1, hReembSet,
      Or.inr ⟨by dsimp only [StepPosCtx.eAffPtr, ctx, stepPosFullCtx]; omega, hAffLe⟩, hAffAt⟩
  refine runs_ret_le (v := ret0 + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const hc2) hret2_lt)
    ⟨updPtr, heapStep, rfl, hReembPost, hret2_le, hgenF, huhF⟩ ?_
  -- The cost.
  have hcA := stepPosAff_cost a (C := candRevSum m.L m.j x.revLists m.S_prev.toList)
    (haC.trans (candRevSum_perm _ _ _ hsp_perm)) haCs haE [b, m.j, heapStep + 5 + len + 4 * m.j]
    mem2
  rw [haj, has, hapi, hsp_card] at hcA
  replace hcA : (dsAffStageContract a).cost [b, m.j, heapStep + 5 + len + 4 * m.j] mem2 ≤
      dsStepPosFullAffCost m x := by
    simp only [dsStepPosFullAffCost, stepPosCandSet]; exact hcA.le
  have hcP : (dsStepPosContract ctx).cost [b, m.j, heapStep + 5 + len + 4 * m.j + 2 +
      (sLists' ⟨m.j - 1, hjL1⟩).length + cand.length, eAff.length, cand.length,
      stepPosOldSum m.u x m.j, heapStep, prefWords, heapStep + 5 + len + 4 * m.j,
      (sLists' ⟨m.j - 1, hjL1⟩).length] memAff ≤
      dsStepPosCost m.impl mMax m.L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH m.S_prev
        m.E_aff.toList (stepPosOldSum m.u x m.j) m.S_prev.card len m.res.UH.length := by
    show dsStepPosCost m.impl mMax m.L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH m.S_prev eAff
      (stepPosOldSum m.u x m.j) (sLists' ⟨m.j - 1, hjL1⟩).length prefWords m.res.UH.length ≤ _
    rw [dsStepPosCost_perm m.impl mMax m.L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH m.S_prev
      (perm_toList_of_nodup_iff hA.2.2.1 hA.2.2.2.1), hsp_card]
    exact dsStepPosCost_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpw
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons,
    argsSize_nil, dsStepHeadContract, dsWordSumContract, dsStepPosFullContract, dsStepPosFullCost]
  omega

end

end MinCostFlow.DynSpanner.Program
