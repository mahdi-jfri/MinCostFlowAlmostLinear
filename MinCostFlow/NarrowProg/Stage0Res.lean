module

public import MinCostFlow.NarrowProg.Stage0ResWork
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 5: top-level `stage0Res`, `stage0Res_meets_direct`, and `stage0ResMod`

Computes `totCost := stage0ResCostSum(pEdges, m)`, allocates `stage0ResSpace m L totCost` words
(`= 16 * m + 3 * m * L + 2 * totCost + 12`), runs `stage0ResWork`, writes `[pHFwd, pHRev]` to
`pResOut`, and proves the explicit `w`-independent cost bound `stage0Res_meets_direct`,
`stage0ResMod_meets_direct`, `stage0Res_meetsO`, and `stage0ResMod_meets`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
open MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowProg

/-! ### Top-level `stage0Res` -/

wram_def stage0Res (costSum resWork : ℕ)
    (pEdges, pShCapBuf, pFeasFlow, n, m, L, k, pResOut, h) {
  totCost := costSum(pEdges, m)
  cap := 2 * m
  pIn2 := h
  pOut2 := pIn2 + 10
  pTail2 := pOut2 + 2
  pHead2 := pTail2 + cap
  pCapPtr2 := pHead2 + cap
  pCapLen2 := pCapPtr2 + cap
  pCostSign2 := pCapLen2 + cap
  pCostPtr2 := pCostSign2 + cap
  pCostLen2 := pCostPtr2 + cap
  pOrigIdx2 := pCostLen2 + cap
  pCapBuf2 := pOrigIdx2 + cap
  pCostBuf2 := pCapBuf2 + m * L
  pHFwd := pCostBuf2 + 2 * totCost
  pHRev := pHFwd + m * L
  hWork := pHRev + m * L
  hEnd := resWork(pEdges, pShCapBuf, pFeasFlow, n, m, L, k,
    pIn2, pOut2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2,
    pOrigIdx2, pCapBuf2, pCostBuf2, pHFwd, pHRev, hWork)
  mem[pResOut] := pHFwd
  mem[pResOut + 1] := pHRev
  return hEnd
}

structure Stage0ResData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  outBuf : List ℕ

def stage0ResSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0ResData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pResOut : ℕ) (h : ℕ),
    let k := narrowLimbWidth d.I
    let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
    ⌜args = [pEdges, pShCapBuf, pFeasFlow, d.I.n, d.I.m, d.L, k, pResOut, h] ∧
      d.L < 2 ^ k ∧ 2 * k + 1 ≤ w ∧ (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      d.I.n + 1 < 2 ^ w ∧ d.outBuf.length = 2 ∧
      h + stage0ResSpace d.I.m d.L (totCostLimbs d.I) + stage1CircSpace R' k S < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    Assn.list pResOut d.outBuf * Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pResOut : ℕ) (h : ℕ)
      (pHFwd : ℕ) (pHRev : ℕ) (g : Fin (d.I.m + d.I.m) → ℤ),
    let k := narrowLimbWidth d.I
    let R := (FlowReduction.shiftedGraph d.I d.hv).residual d.f
    let R' := R.withoutZeroEdges
    ⌜args = [pEdges, pShCapBuf, pFeasFlow, d.I.n, d.I.m, d.L, k, pResOut, h] ∧
      h + stage0ResSpace d.I.m d.L (totCostLimbs d.I) ≤ h' ∧
      h' ≤ h + stage0ResSpace d.I.m d.L (totCostLimbs d.I) + stage1CircSpace R' k S ∧
      pHFwd + d.I.m * d.L ≤ 2 ^ w ∧ pHRev + d.I.m * d.L ≤ 2 ^ w ∧
      R.Optimal (fun a => (g a : ℝ)) ∧
      (∀ e : Fin d.I.m, 0 ≤ g (Fin.castAdd d.I.m e) ∧ 0 ≤ g (Fin.natAdd d.I.m e)) ∧
      (∀ e : Fin d.I.m, (g (Fin.natAdd d.I.m e)).toNat ≤ (d.f e).toNat) ∧
      (∀ e : Fin d.I.m, (d.f e).toNat + (g (Fin.castAdd d.I.m e)).toNat ≤
        (FlowReduction.shiftedGraph d.I d.hv).capacity e)⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHFwd + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.castAdd d.I.m ⟨e, hlt⟩)).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHRev + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.natAdd d.I.m ⟨e, hlt⟩)).toNat) d.L else [])) *
    Assn.list pResOut [pHFwd, pHRev] * Assn.free h' (2 ^ w - h') * Assn.gc

theorem stage0Res_meets {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ} {f costSum resWork : ℕ}
    {Tcs : Instance → ℕ} {Tw : Stage0ResWorkData → ℕ}
    (hp : p.procs[f]? = some (stage0Res costSum resWork))
    (hcs : Meets w p costSum ((stage0ResCostSumSpec w).withCost fun I _ => Tcs I))
    (hwk : Meets w p resWork ((stage0ResWorkSpec w S).withCost fun d _ => Tw d)) :
    Meets w p f ((stage0ResSpec w S).withCost fun d _ =>
      Tcs d.I + Tw ⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge⟩ + 160) := by
  sep_enter d with hLlt h2k1 hclip hpE h11m hpSC hpFF hmL hn1W hout hfit
  set k := narrowLimbWidth d.I
  set totC := totCostLimbs d.I
  have hsp_eq : h + stage0ResSpace d.I.m d.L totC =
      h + 10 + 2 + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m +
        2 * d.I.m + 2 * d.I.m + 2 * d.I.m + d.I.m * d.L + 2 * totC + d.I.m * d.L + d.I.m * d.L := by
    unfold stage0ResSpace; ring
  have hfit0 : h + stage0ResSpace d.I.m d.L totC < 2 ^ w := by omega
  have htotW : totC < 2 ^ w := by unfold stage0ResSpace at hfit0; omega
  have hw16 : 16 < 2 ^ w := by
    have hk3 := three_le_narrowLimbWidth d.I
    have hpow : 2 ^ 7 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  generalize hPre0 :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ i ∈ Finset.range d.I.m,
       Assn.list (pShCapBuf + i * d.L)
         (if hlt : i < d.I.m then
           padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
         else [])) *
     (∏ i ∈ Finset.range d.I.m,
       Assn.list (pFeasFlow + i * d.L)
         (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
     Assn.list pResOut d.outBuf * Assn.free h (2 ^ w - h)) = Pre0
  sep_apply hPre0
  sep_step from d.I
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  subst Pre0; sep_norm
  subst hWork pHRev pHFwd pCostBuf2 pCapBuf2 pCostLen2 pCostSign2 pCapPtr2 pTail2 cap totCost
  sep_apply split_free_res (h := h) (m := d.I.m) (L := d.L) (totCost := totC) (w := w) hfit0
  have hfit_work : (h + 10 + 2 + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m +
      2 * d.I.m + 2 * d.I.m + 2 * d.I.m + d.I.m * d.L + 2 * totCostLimbs d.I + d.I.m * d.L + d.I.m * d.L) +
      stage1CircSpace ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
      (narrowLimbWidth d.I) S < 2 ^ w := by
    dsimp only [totC, k] at hfit hsp_eq; omega
  sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge⟩ : Stage0ResWorkData)
    with hh_lo hh_hi hopt_g hg_nn hg_rev hg_fwd
  sep_apply list_split_two (p := pResOut) hout
  sep_step; sep_step
  sep_apply list_join_two pResOut
    (h + 10 + 2 + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m +
      2 * d.I.m + 2 * d.I.m + 2 * d.I.m + d.I.m * d.L + 2 * totC)
    (h + 10 + 2 + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m + 2 * d.I.m +
      2 * d.I.m + 2 * d.I.m + 2 * d.I.m + d.I.m * d.L + 2 * totC + d.I.m * d.L)
  sep_step
  · dsimp only [totC] at hsp_eq; omega
  · dsimp only [totC] at hsp_eq; omega

/-! ### Explicit `w`-independent cost (`stage0Res_meets_direct`), `MeetsO`, and `stage0ResMod` -/

/-- Direct `Meets` theorem for `stage0Res` with an explicit `w`-independent overhead constant
(`2500`) plus one Stage 1 call `B n (2 * m) (2 * maxCapacity) maxCost`. -/
theorem stage0Res_meets_direct {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {B : ℕ → ℕ → ℕ → ℕ → ℕ}
    {f pCopy cLen lSub copyFl costSum resEmit copyCost revSign fwdEmit revEmit
      fwdSub fwdStep revStep passFwd passRev writeHdr resBuild scatSlice resScatter resRun resWork stage1Circ : ℕ}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : p.procs[f]? = some (stage0Res costSum resWork))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hcLen : p.procs[cLen]? = some canonLen)
    (hlSub : p.procs[lSub]? = some limbsSub)
    (hcopyFl : p.procs[copyFl]? = some (copyFlowLimbs cLen pCopy))
    (hcostSum : p.procs[costSum]? = some stage0ResCostSum)
    (hresEmit : p.procs[resEmit]? = some stage0ResEmit)
    (hcopyCost : p.procs[copyCost]? = some (stage0ResCopyCost pCopy))
    (hrevSign : p.procs[revSign]? = some stage0ResRevSign)
    (hfwdEmit : p.procs[fwdEmit]? = some (stage0ResFwdEmit copyCost resEmit))
    (hrevEmit : p.procs[revEmit]? = some (stage0ResRevEmit copyCost revSign resEmit))
    (hfwdSub : p.procs[fwdSub]? = some (stage0ResFwdSub lSub cLen))
    (hfwdStep : p.procs[fwdStep]? = some (stage0ResFwdStep fwdSub fwdEmit))
    (hrevStep : p.procs[revStep]? = some (stage0ResRevStep cLen revEmit))
    (hpassFwd : p.procs[passFwd]? = some (stage0ResPassFwd fwdStep))
    (hpassRev : p.procs[passRev]? = some (stage0ResPassRev revStep))
    (hwriteHdr : p.procs[writeHdr]? = some writeStage1Hdr)
    (hresBuild : p.procs[resBuild]? = some (stage0ResBuild passFwd passRev writeHdr))
    (hscatSlice : p.procs[scatSlice]? = some (stage0ResScatterSlice copyFl))
    (hresScatter : p.procs[resScatter]? = some (stage0ResScatter scatSlice))
    (hresRun : p.procs[resRun]? = some (stage0ResRun stage1Circ resScatter))
    (hresWork : p.procs[resWork]? = some (stage0ResWork resBuild resRun))
    (hstage1 : Meets w p stage1Circ ((stage1CircSpec w S).withCost fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1))) :
    Meets w p f ((stage0ResSpec w S).withCost fun d _ =>
      2500 * (d.I.m * (d.L + narrowMaxCostLimbs d.I + 1) + 1) +
        B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost) := by
  by_cases hw : 2 < 2 ^ w
  · have hw1 : 1 < 2 ^ w := by omega
    have mCan := canonLen_meets (w := w) hcLen
    have mPad := padCopy_meets (w := w) hw1 hpCopy
    have mSub := limbsSub_meets (w := w) hlSub
    have mCopyFl := copyFlowLimbs_meets (Tcan := fun n => 45 * n + 25) (Tpad := fun n => 55 * n + 35) hcopyFl mCan mPad
    have mCostSum := stage0ResCostSum_meets (w := w) hw1 hcostSum
    have mEmit := stage0ResEmit_meets (w := w) hresEmit
    have mCopyCost0 := stage0ResCopyCost_meets (w := w) (Tpad := fun n => 55 * n + 35) hcopyCost mPad
    have mCopyCost : Meets w p copyCost ((stage0ResCopyCostSpec w).withCost fun x _ =>
        (55 * narrowMaxCostLimbs x.I + 35) + 60) :=
      Meets.withCost_mono mCopyCost0 fun x _ => by
        have hk1 := one_le_narrowLimbWidth x.I
        have hb : 1 < 2 ^ narrowLimbWidth x.I := by have := two_le_pow hk1; omega
        have hle := digits_length_mono hb (cost_natAbs_le_maxCost' x.I x.e)
        unfold narrowMaxCostLimbs; omega
    have mRevSign := stage0ResRevSign_meets (w := w) hw1 hrevSign
    have mFwdEmit := stage0ResFwdEmit_meets (Tcopy := fun c => (55 * c + 35) + 60) (Temit := 70)
      hfwdEmit mCopyCost mEmit
    have mRevEmit := stage0ResRevEmit_meets (Tcopy := fun c => (55 * c + 35) + 60) (Trev := 30) (Temit := 70)
      hrevEmit mCopyCost mRevSign mEmit
    have mFwdSub := stage0ResFwdSub_meets
      (Tsub := fun n => 60 * n + 30) (Tcan := fun n => 45 * n + 25) hfwdSub mSub mCan
    have mFwdStep := stage0ResFwdStep_meets
      (Tfsub := fun l => (60 * l + 30) + (45 * l + 25) + 30)
      (Tfe := fun c => ((55 * c + 35) + 60) + 70 + 60)
      hfwdStep mFwdSub mFwdEmit
    have mRevStep := stage0ResRevStep_meets
      (Tcan := fun n => 45 * n + 25)
      (Tre := fun c => ((55 * c + 35) + 60) + 30 + 70 + 70)
      hrevStep mCan mRevEmit
    have mPassFwd := stage0ResPassFwd_meets
      (Tstep := fun c l => ((60 * l + 30) + (45 * l + 25) + 30) + (((55 * c + 35) + 60) + 70 + 60) + 70)
      hpassFwd mFwdStep
    have mPassRev := stage0ResPassRev_meets
      (Tstep := fun c l => (45 * l + 25) + (((55 * c + 35) + 60) + 30 + 70 + 70) + 70)
      hpassRev mRevStep
    have mWriteHdr := writeStage1Hdr_meets (w := w) hwriteHdr
    have mBuild := stage0ResBuild_meets
      (Tfwd := fun d => (((60 * d.L + 30) + (45 * d.L + 25) + 30) + (((55 * narrowMaxCostLimbs d.I + 35) + 60) + 70 + 60) + 70 + 65) * d.I.m + 50)
      (Trev := fun d => ((45 * d.L + 25) + (((55 * narrowMaxCostLimbs d.I + 35) + 60) + 30 + 70 + 70) + 70 + 65) * d.I.m + 50)
      (Thdr := 70)
      hresBuild mPassFwd mPassRev mWriteHdr
    have mSlice := stage0ResScatterSlice_meets
      (Tcf := fun a b => (45 * a + 25) + (55 * b + 35) + 30) hscatSlice mCopyFl
    have mScatter := stage0ResScatter_meets
      (Tsl := fun k2 l s => (((45 * k2 + 25) + (55 * l + 35) + 30) + 60) * s + 40)
      hresScatter mSlice
    have mRun := stage0ResRun_meets
      (T1 := fun R' => B R'.n R'.m (circMaxCapacity R') (circMaxCost R'))
      (Tsc := fun k2 l sf sr =>
        ((((45 * k2 + 25) + (55 * l + 35) + 30) + 60) * sf + 40) +
        ((((45 * k2 + 25) + (55 * l + 35) + 30) + 60) * sr + 40) + 100)
      hresRun hstage1 mScatter
    have mWork := stage0ResWork_meets hresWork mBuild mRun (fun _ _ _ _ _ _ _ _ _ => rfl)
    have mRes := stage0Res_meets hp mCostSum mWork
    refine Meets.withCost_mono mRes fun d _ => ?_
    dsimp only
    set R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
    set fwd := resFwdPos d.I d.hv d.f d.I.m
    set rev := resRevPos d.I d.f d.I.m
    set K2 := bitScalingPhases R' / narrowLimbWidth d.I + 2
    have hm_le : R'.m ≤ 2 * d.I.m := res_m_le_two_m d.I d.hv d.f
    have hfwd_le : fwd.length ≤ d.I.m := resFwdPos_length_le d.I d.hv d.f d.I.m
    have hrev_le : rev.length ≤ d.I.m := resRevPos_length_le d.I d.f d.I.m
    have hB_le : B R'.n R'.m (circMaxCapacity R') (circMaxCost R') ≤
        B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost :=
      hB_mono R'.n d.I.n R'.m (2 * d.I.m) (circMaxCapacity R') (2 * d.I.maxCapacity)
        (circMaxCost R') d.I.maxCost
        (le_refl _) hm_le (residual_withoutZeroEdges_maxCapacity_le d.I d.hv d.f d.hf)
        (residual_withoutZeroEdges_maxCost_le d.I d.hv d.f)
    have h2U_le_bud : 2 * d.I.maxCapacity ≤ FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity := by
      unfold FlowReduction.scalingCapacityBudget
      have : 2 * (d.I.m + 1) * d.I.maxCapacity = 2 * d.I.m * d.I.maxCapacity + 2 * d.I.maxCapacity := by ring
      omega
    have hK2_le : K2 ≤ d.L + 2 := by
      have h1 := stage1_Kcap_le_maxCapLimbs d.I d.hv R'
        (le_trans (residual_withoutZeroEdges_maxCapacity_le d.I d.hv d.f d.hf) h2U_le_bud)
      have h2 := d.hLge
      omega
    have hmul1 : (K2 + d.L + 1) * fwd.length ≤ (2 * d.L + 3) * d.I.m :=
      Nat.mul_le_mul (by omega) hfwd_le
    have hmul2 : (K2 + d.L + 1) * rev.length ≤ (2 * d.L + 3) * d.I.m :=
      Nat.mul_le_mul (by omega) hrev_le
    nlinarith
  · sep_enter d with _ h2k1
    exfalso; apply hw
    have hk3 := three_le_narrowLimbWidth d.I
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))

theorem stage0Res_meetsO {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {B : ℕ → ℕ → ℕ → ℕ → ℕ}
    {f pCopy cLen lSub copyFl costSum resEmit copyCost revSign fwdEmit revEmit
      fwdSub fwdStep revStep passFwd passRev writeHdr resBuild scatSlice resScatter resRun resWork stage1Circ : ℕ}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : p.procs[f]? = some (stage0Res costSum resWork))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hcLen : p.procs[cLen]? = some canonLen)
    (hlSub : p.procs[lSub]? = some limbsSub)
    (hcopyFl : p.procs[copyFl]? = some (copyFlowLimbs cLen pCopy))
    (hcostSum : p.procs[costSum]? = some stage0ResCostSum)
    (hresEmit : p.procs[resEmit]? = some stage0ResEmit)
    (hcopyCost : p.procs[copyCost]? = some (stage0ResCopyCost pCopy))
    (hrevSign : p.procs[revSign]? = some stage0ResRevSign)
    (hfwdEmit : p.procs[fwdEmit]? = some (stage0ResFwdEmit copyCost resEmit))
    (hrevEmit : p.procs[revEmit]? = some (stage0ResRevEmit copyCost revSign resEmit))
    (hfwdSub : p.procs[fwdSub]? = some (stage0ResFwdSub lSub cLen))
    (hfwdStep : p.procs[fwdStep]? = some (stage0ResFwdStep fwdSub fwdEmit))
    (hrevStep : p.procs[revStep]? = some (stage0ResRevStep cLen revEmit))
    (hpassFwd : p.procs[passFwd]? = some (stage0ResPassFwd fwdStep))
    (hpassRev : p.procs[passRev]? = some (stage0ResPassRev revStep))
    (hwriteHdr : p.procs[writeHdr]? = some writeStage1Hdr)
    (hresBuild : p.procs[resBuild]? = some (stage0ResBuild passFwd passRev writeHdr))
    (hscatSlice : p.procs[scatSlice]? = some (stage0ResScatterSlice copyFl))
    (hresScatter : p.procs[resScatter]? = some (stage0ResScatter scatSlice))
    (hresRun : p.procs[resRun]? = some (stage0ResRun stage1Circ resScatter))
    (hresWork : p.procs[resWork]? = some (stage0ResWork resBuild resRun))
    (hstage1 : MeetsO w p stage1Circ (stage1CircSpec w S) fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) :
    MeetsO w p f (stage0ResSpec w S) fun d _ =>
      d.I.m * (d.L + narrowMaxCostLimbs d.I + 1) +
        B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost + 1 := by
  obtain ⟨K1c, hstage1_m⟩ := hstage1
  have hd := stage0Res_meets_direct (B := fun n m U C => K1c * B n m U C)
    (fun _ _ _ _ _ _ _ _ h1 h2 h3 h4 => Nat.mul_le_mul_left K1c (hB_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4))
    hp hpCopy hcLen hlSub hcopyFl hcostSum hresEmit hcopyCost hrevSign hfwdEmit hrevEmit
    hfwdSub hfwdStep hrevStep hpassFwd hpassRev
    hwriteHdr hresBuild hscatSlice hresScatter hresRun hresWork hstage1_m
  exact MeetsO.of_meets hd ⟨K1c + 2500, fun ⟨d, _⟩ => by
    dsimp only
    set X := d.I.m * (d.L + narrowMaxCostLimbs d.I + 1)
    set Y := B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost
    nlinarith⟩

/-! ### Polymorphic module -/

/-- Procedure names for `stage0ResMod`, polymorphic over any name type `ι`.
`stage1Circ` is an imported procedure name (supplied by the Stage 1 module). -/
structure Stage0ResNames (ι : Type) where
  padCopy : ι
  canonLen : ι
  limbsSub : ι
  copyFlowLimbs : ι
  resCostSum : ι
  resEmit : ι
  resCopyCost : ι
  resRevSign : ι
  resFwdEmit : ι
  resRevEmit : ι
  resFwdSub : ι
  resFwdStep : ι
  resRevStep : ι
  resPassFwd : ι
  resPassRev : ι
  writeStage1Hdr : ι
  resBuild : ι
  resScatterSlice : ι
  resScatter : ι
  resRun : ι
  resWork : ι
  stage0Res : ι
  stage1Circ : ι

/-- Polymorphic module for Stage 0 item 5 (`stage0Res`), calling `names.stage1Circ`. -/
def stage0ResMod {ι : Type} (names : Stage0ResNames ι) : Module ι :=
  ⟨[(names.padCopy, fun _ => padCopy),
    (names.canonLen, fun _ => canonLen),
    (names.limbsSub, fun _ => limbsSub),
    (names.copyFlowLimbs, fun idx => copyFlowLimbs (idx names.canonLen) (idx names.padCopy)),
    (names.resCostSum, fun _ => stage0ResCostSum),
    (names.resEmit, fun _ => stage0ResEmit),
    (names.resCopyCost, fun idx => stage0ResCopyCost (idx names.padCopy)),
    (names.resRevSign, fun _ => stage0ResRevSign),
    (names.resFwdEmit, fun idx =>
      stage0ResFwdEmit (idx names.resCopyCost) (idx names.resEmit)),
    (names.resRevEmit, fun idx =>
      stage0ResRevEmit (idx names.resCopyCost) (idx names.resRevSign) (idx names.resEmit)),
    (names.resFwdSub, fun idx =>
      stage0ResFwdSub (idx names.limbsSub) (idx names.canonLen)),
    (names.resFwdStep, fun idx =>
      stage0ResFwdStep (idx names.resFwdSub) (idx names.resFwdEmit)),
    (names.resRevStep, fun idx =>
      stage0ResRevStep (idx names.canonLen) (idx names.resRevEmit)),
    (names.resPassFwd, fun idx => stage0ResPassFwd (idx names.resFwdStep)),
    (names.resPassRev, fun idx => stage0ResPassRev (idx names.resRevStep)),
    (names.writeStage1Hdr, fun _ => writeStage1Hdr),
    (names.resBuild, fun idx =>
      stage0ResBuild (idx names.resPassFwd) (idx names.resPassRev) (idx names.writeStage1Hdr)),
    (names.resScatterSlice, fun idx => stage0ResScatterSlice (idx names.copyFlowLimbs)),
    (names.resScatter, fun idx => stage0ResScatter (idx names.resScatterSlice)),
    (names.resRun, fun idx => stage0ResRun (idx names.stage1Circ) (idx names.resScatter)),
    (names.resWork, fun idx => stage0ResWork (idx names.resBuild) (idx names.resRun)),
    (names.stage0Res, fun idx => stage0Res (idx names.resCostSum) (idx names.resWork))]⟩

theorem stage0ResMod_noRand {ι : Type} (names : Stage0ResNames ι) :
    (stage0ResMod names).NoRand := by
  wram_no_rand

theorem stage0ResMod_meets_direct {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {S : ℕ → ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ} {names : Stage0ResNames ι}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : (stage0ResMod names).Placed p idx)
    (hstage1 : Meets w p (idx names.stage1Circ) ((stage1CircSpec w S).withCost fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1))) :
    Meets w p (idx names.stage0Res) ((stage0ResSpec w S).withCost fun d _ =>
      2500 * (d.I.m * (d.L + narrowMaxCostLimbs d.I + 1) + 1) +
        B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost) :=
  stage0Res_meets_direct hB_mono
    (hp.get (n := names.stage0Res) (b := fun idx => stage0Res (idx names.resCostSum) (idx names.resWork)) (by simp [stage0ResMod]))
    (hp.get (n := names.padCopy) (b := fun _ => padCopy) (by simp [stage0ResMod]))
    (hp.get (n := names.canonLen) (b := fun _ => canonLen) (by simp [stage0ResMod]))
    (hp.get (n := names.limbsSub) (b := fun _ => limbsSub) (by simp [stage0ResMod]))
    (hp.get (n := names.copyFlowLimbs) (b := fun idx => copyFlowLimbs (idx names.canonLen) (idx names.padCopy)) (by simp [stage0ResMod]))
    (hp.get (n := names.resCostSum) (b := fun _ => stage0ResCostSum) (by simp [stage0ResMod]))
    (hp.get (n := names.resEmit) (b := fun _ => stage0ResEmit) (by simp [stage0ResMod]))
    (hp.get (n := names.resCopyCost) (b := fun idx => stage0ResCopyCost (idx names.padCopy)) (by simp [stage0ResMod]))
    (hp.get (n := names.resRevSign) (b := fun _ => stage0ResRevSign) (by simp [stage0ResMod]))
    (hp.get (n := names.resFwdEmit) (b := fun idx => stage0ResFwdEmit (idx names.resCopyCost) (idx names.resEmit)) (by simp [stage0ResMod]))
    (hp.get (n := names.resRevEmit) (b := fun idx => stage0ResRevEmit (idx names.resCopyCost) (idx names.resRevSign) (idx names.resEmit)) (by simp [stage0ResMod]))
    (hp.get (n := names.resFwdSub) (b := fun idx => stage0ResFwdSub (idx names.limbsSub) (idx names.canonLen)) (by simp [stage0ResMod]))
    (hp.get (n := names.resFwdStep) (b := fun idx => stage0ResFwdStep (idx names.resFwdSub) (idx names.resFwdEmit)) (by simp [stage0ResMod]))
    (hp.get (n := names.resRevStep) (b := fun idx => stage0ResRevStep (idx names.canonLen) (idx names.resRevEmit)) (by simp [stage0ResMod]))
    (hp.get (n := names.resPassFwd) (b := fun idx => stage0ResPassFwd (idx names.resFwdStep)) (by simp [stage0ResMod]))
    (hp.get (n := names.resPassRev) (b := fun idx => stage0ResPassRev (idx names.resRevStep)) (by simp [stage0ResMod]))
    (hp.get (n := names.writeStage1Hdr) (b := fun _ => writeStage1Hdr) (by simp [stage0ResMod]))
    (hp.get (n := names.resBuild) (b := fun idx => stage0ResBuild (idx names.resPassFwd) (idx names.resPassRev) (idx names.writeStage1Hdr)) (by simp [stage0ResMod]))
    (hp.get (n := names.resScatterSlice) (b := fun idx => stage0ResScatterSlice (idx names.copyFlowLimbs)) (by simp [stage0ResMod]))
    (hp.get (n := names.resScatter) (b := fun idx => stage0ResScatter (idx names.resScatterSlice)) (by simp [stage0ResMod]))
    (hp.get (n := names.resRun) (b := fun idx => stage0ResRun (idx names.stage1Circ) (idx names.resScatter)) (by simp [stage0ResMod]))
    (hp.get (n := names.resWork) (b := fun idx => stage0ResWork (idx names.resBuild) (idx names.resRun)) (by simp [stage0ResMod]))
    hstage1

theorem stage0ResMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {S : ℕ → ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ} {names : Stage0ResNames ι}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : (stage0ResMod names).Placed p idx)
    (hstage1 : MeetsO w p (idx names.stage1Circ) (stage1CircSpec w S) fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) :
    MeetsO w p (idx names.stage0Res) (stage0ResSpec w S) fun d _ =>
      d.I.m * (d.L + narrowMaxCostLimbs d.I + 1) +
        B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost + 1 := by
  obtain ⟨K1c, hstage1_m⟩ := hstage1
  have hd := stage0ResMod_meets_direct (B := fun n m U C => K1c * B n m U C)
    (fun _ _ _ _ _ _ _ _ h1 h2 h3 h4 => Nat.mul_le_mul_left K1c (hB_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4))
    hp hstage1_m
  exact MeetsO.of_meets hd ⟨K1c + 2500, fun ⟨d, _⟩ => by
    dsimp only
    set X := d.I.m * (d.L + narrowMaxCostLimbs d.I + 1)
    set Y := B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost
    nlinarith⟩

end MinCostFlow.NarrowProg
