module

public import MinCostFlow.NarrowProg.Stage0FeasWork
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 4: top-level `stage0Feas`, `stage0Feas_meets_direct`, and `stage0FeasMod`

Allocates `stage0FeasSpace m L = 25 * m + m * L + 12` words, runs `stage0FeasWork`, writes
`[ok, pFeasFlow]` to `pFeasOut`, and proves the explicit `w`-independent cost bound
`stage0Feas_meets_direct`, `stage0FeasMod_meets_direct`, `stage0Feas_meetsO`, and `stage0FeasMod_meets`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
open MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowProg

/-! ### Top-level `stage0Feas` (allocates `stage0FeasSpace m L` and writes `[ok, pFeasFlow]`) -/

wram_def stage0Feas (feasWork : ℕ)
    (pEdges, pLabels, n, m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign, pShDemLen, L, k,
     pFeasOut, h) {
  cap := 3 * m
  pIn1 := h
  pOut1 := pIn1 + 10
  pTail1 := pOut1 + 2
  pHead1 := pTail1 + cap
  pCapPtr1 := pHead1 + cap
  pCapLen1 := pCapPtr1 + cap
  pCostSign1 := pCapLen1 + cap
  pCostPtr1 := pCostSign1 + cap
  pCostLen1 := pCostPtr1 + cap
  pOrigIdx1 := pCostLen1 + cap
  pOneCells := pOrigIdx1 + m
  pFeasFlow := pOneCells + cap
  hWork := pFeasFlow + m * L
  hEnd := feasWork(pEdges, pLabels, n, m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign, pShDemLen,
    L, k, pIn1, pOut1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1,
    pOrigIdx1, pOneCells, pFeasFlow, hWork, pFeasOut)
  mem[pFeasOut + 1] := pFeasFlow
  return hEnd
}

structure Stage0FeasData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  act : List ℕ
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  outBuf : List ℕ

def stage0FeasSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0FeasData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pFeasOut : ℕ) (h : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pFeasOut, h] ∧
      ActiveInv el d.act ∧ d.L < 2 ^ k ∧
      2 * k + 1 ≤ w ∧ (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pLabels + d.I.n ≤ 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pShCapLen + d.I.m ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w ∧
      pShDemSign + el.count ≤ 2 ^ w ∧ pShDemLen + el.count ≤ 2 ^ w ∧
      d.I.n + 2 < 2 ^ w ∧ d.outBuf.length = 2 ∧
      h + stage0FeasSpace d.I.m d.L + stage1CircSpace P' k S < 2 ^ w⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pFeasOut d.outBuf * Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pFeasOut : ℕ) (h : ℕ)
      (ok : ℕ) (pFeasFlow : ℕ) (f : Fin d.I.m → ℤ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pFeasOut, h] ∧
      h + stage0FeasSpace d.I.m d.L ≤ h' ∧
      h' ≤ h + stage0FeasSpace d.I.m d.L + stage1CircSpace P' k S ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ ok ≤ 1 ∧
      (ok = 1 →
        (∀ e : Fin d.I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ)) ∧
        d.I.IsFeasible (FlowReduction.restore d.I (fun e => (f e : ℝ)))) ∧
      (ok = 0 → ∀ x, ¬ d.I.IsFeasible x)⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    (if ok = 1 then
      (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨e, hlt⟩).toNat) d.L else []))
     else 1) *
    Assn.list pFeasOut [ok, pFeasFlow] * Assn.free h' (2 ^ w - h') * Assn.gc

theorem stage0Feas_meets {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ} {f feasWork : ℕ}
    {Tw : Stage0FeasWorkData → ℕ}
    (hp : p.procs[f]? = some (stage0Feas feasWork))
    (hwk : Meets w p feasWork ((stage0FeasWorkSpec w S).withCost fun d _ => Tw d))
    (hTw_indep : ∀ d₁ d₂ : Stage0FeasWorkData,
      d₁.I = d₂.I → d₁.L = d₂.L → Tw d₁ = Tw d₂) :
    Meets w p f ((stage0FeasSpec w S).withCost fun d _ =>
      Tw ⟨d.I, d.hv, d.hiso, d.act, d.L, d.hLge, 0⟩ + 130) := by
  sep_enter d with hact hLlt h2k1 hclip hcaps hpE h11m hpLab hpCap hmL hpLen
    hpDem hcntL hpS hpL hn2W hout hfit
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  set k := narrowLimbWidth d.I
  set P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
  have hsp_eq : h + stage0FeasSpace d.I.m d.L =
      h + 10 + 2 + 3 * d.I.m + 3 * d.I.m + 3 * d.I.m + 3 * d.I.m + 3 * d.I.m +
        3 * d.I.m + 3 * d.I.m + d.I.m + 3 * d.I.m + d.I.m * d.L := by
    unfold stage0FeasSpace; ring
  have hfit0 : h + stage0FeasSpace d.I.m d.L < 2 ^ w := by omega
  have hw16 : 16 < 2 ^ w := by
    have hk3 := three_le_narrowLimbWidth d.I
    have hpow : 2 ^ 7 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  generalize hPre0 :
    ((∏ i ∈ Finset.range d.I.m,
        Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pLabels (List.ofFn el.table) *
     (∏ i ∈ Finset.range d.I.m,
        Assn.list (pShCapBuf + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
          else [])) *
     Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
       (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
     (∏ c ∈ Finset.range el.count,
        Assn.list (pShDemBuf + c * d.L)
          (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
     Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
       if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
     Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
       (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
     Assn.list pFeasOut d.outBuf * Assn.free h (2 ^ w - h)) = Pre0
  sep_apply hPre0
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  subst Pre0; sep_norm
  sep_apply split_free_feas (h := h) (m := d.I.m) (L := d.L) (w := w) hfit0
  sep_apply list_split_two (p := pFeasOut) hout
  have hTw_eq : Tw ⟨d.I, d.hv, d.hiso, d.act, d.L, d.hLge, d.outBuf[0]'(by omega)⟩ =
      Tw ⟨d.I, d.hv, d.hiso, d.act, d.L, d.hLge, 0⟩ :=
    hTw_indep _ _ rfl rfl
  have hfit_work : hWork + stage1CircSpace (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
      (narrowLimbWidth d.I) S < 2 ^ w := by
    dsimp only [P', k] at hfit; omega
  sep_step from (⟨d.I, d.hv, d.hiso, d.act, d.L, d.hLge, d.outBuf[0]'(by omega)⟩ : Stage0FeasWorkData)
    with hh_lo hh_hi hok_le hok1 hok0
  sep_step
  sep_apply list_join_two pFeasOut ok
    (h + 10 + 2 + 3 * d.I.m + 3 * d.I.m + 3 * d.I.m + 3 * d.I.m + 3 * d.I.m +
      3 * d.I.m + 3 * d.I.m + d.I.m + 3 * d.I.m)
  sep_step

/-! ### Explicit `w`-independent cost (`stage0Feas_meets_direct`), `MeetsO`, and `stage0FeasMod` -/

/-- Direct `Meets` theorem for `stage0Feas` with an explicit `w`-independent overhead constant
(`2500`) plus one Stage 1 call `B (n + 1) (3 * m) (scalingCapacityBudget I I.maxCapacity) 1`. -/
theorem stage0Feas_meets_direct {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {B : ℕ → ℕ → ℕ → ℕ → ℕ}
    {f pCopy lCmp cLen copyFl pass1 artEmit artPass artBoth writeHdr feasBuild
      chkOne satCheck scatter feasPost feasPostWrap feasRun feasWork stage1Circ : ℕ}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : p.procs[f]? = some (stage0Feas feasWork))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hlCmp : p.procs[lCmp]? = some limbsCmp)
    (hcLen : p.procs[cLen]? = some canonLen)
    (hcopyFl : p.procs[copyFl]? = some (copyFlowLimbs cLen pCopy))
    (hpass1 : p.procs[pass1]? = some stage0FeasPass1)
    (hartEmit : p.procs[artEmit]? = some stage0FeasArtEmit)
    (hartPass : p.procs[artPass]? = some (stage0FeasArtPass artEmit))
    (hartBoth : p.procs[artBoth]? = some (stage0FeasArtBoth artPass))
    (hwriteHdr : p.procs[writeHdr]? = some writeStage1Hdr)
    (hfeasBuild : p.procs[feasBuild]? = some (stage0FeasBuild pass1 artBoth writeHdr))
    (hchkOne : p.procs[chkOne]? = some (stage0FeasCheckOne cLen lCmp))
    (hsatCheck : p.procs[satCheck]? = some (stage0FeasSatCheck chkOne))
    (hscatter : p.procs[scatter]? = some (stage0FeasScatter copyFl))
    (hfeasPost : p.procs[feasPost]? = some (stage0FeasPost satCheck scatter))
    (hfeasPostWrap : p.procs[feasPostWrap]? = some (stage0FeasPostWrap feasPost))
    (hfeasRun : p.procs[feasRun]? = some (stage0FeasRun stage1Circ feasPostWrap))
    (hfeasWork : p.procs[feasWork]? = some (stage0FeasWork feasBuild feasRun))
    (hstage1 : Meets w p stage1Circ ((stage1CircSpec w S).withCost fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1))) :
    Meets w p f ((stage0FeasSpec w S).withCost fun d _ =>
      2500 * (d.I.n + d.I.m * (d.L + 1) + 1) +
        B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1) := by
  by_cases hw : 2 < 2 ^ w
  · have hw1 : 1 < 2 ^ w := by omega
    have mCan := canonLen_meets (w := w) hcLen
    have mPad := padCopy_meets (w := w) hw1 hpCopy
    have mCmp := limbsCmp_meets (w := w) hw hlCmp
    have mCopyFl := copyFlowLimbs_meets (Tcan := fun n => 45 * n + 25) (Tpad := fun n => 55 * n + 35) hcopyFl mCan mPad
    have mPass1 := stage0FeasPass1_meets (w := w) hw hpass1
    have mArtEmit := stage0FeasArtEmit_meets (w := w) hw hartEmit
    have mArtPass := stage0FeasArtPass_meets (w := w) hw hartPass mArtEmit
    have mArtBoth := stage0FeasArtBoth_meets (Tart := fun n => (70 + 115) * n + 40) hartBoth mArtPass
    have mWriteHdr := writeStage1Hdr_meets (w := w) hwriteHdr
    have mBuild := stage0FeasBuild_meets
      (Tp1 := fun m => 95 * m + 40) (Tboth := fun n => 2 * ((70 + 115) * n + 40) + 60) (Thdr := 70)
      hfeasBuild mPass1 mArtBoth mWriteHdr
    have mChkOne := stage0FeasCheckOne_meets
      (Tcan := fun n => 45 * n + 25) (Tcmp := fun n => 40 * n + 20) hw (fun _ _ h => by omega)
      hchkOne mCan mCmp
    have mSat := stage0FeasSatCheck_meets (w := w)
      (Tchk := fun n => (45 * n + 25) + (40 * n + 20) + 50) hw hsatCheck mChkOne
    have mScat := stage0FeasScatter_meets
      (Tcf := fun a b => (45 * a + 25) + (55 * b + 35) + 30) hscatter mCopyFl
    have mPost := stage0FeasPost_meets
      (Tsat := fun k1 d1 => (((45 * k1 + 25) + (40 * k1 + 20) + 50) + 75) * d1 + 45)
      (Tsc := fun k1 l o => (((45 * k1 + 25) + (55 * l + 35) + 30) + 75) * o + 40)
      hfeasPost mSat mScat
    have mPostWrap := stage0FeasPostWrap_meets
      (Tp := fun k1 l d1 o =>
        ((((45 * k1 + 25) + (40 * k1 + 20) + 50) + 75) * d1 + 45) +
        ((((45 * k1 + 25) + (55 * l + 35) + 30) + 75) * o + 40) + 70)
      hfeasPostWrap mPost
    have mRun := stage0FeasRun_meets
      (T1 := fun P' => B P'.n P'.m (circMaxCapacity P') (circMaxCost P'))
      (Tp := fun k1 l d1 o =>
        (((((45 * k1 + 25) + (40 * k1 + 20) + 50) + 75) * d1 + 45) +
         ((((45 * k1 + 25) + (55 * l + 35) + 30) + 75) * o + 40) + 70) + 50)
      hfeasRun hstage1 mPostWrap
    have mWork := stage0FeasWork_meets
      (Tb := fun m n => (95 * m + 40) + (2 * ((70 + 115) * n + 40) + 60) + 70 + 100)
      hfeasWork mBuild mRun (fun d₁ d₂ hI hL => by
        cases d₁; cases d₂; dsimp only at hI hL; subst hI hL; rfl)
    have mFeas := stage0Feas_meets hp mWork (fun d₁ d₂ hI hL => by
      cases d₁; cases d₂; dsimp only at hI hL; subst hI hL; rfl)
    refine Meets.withCost_mono mFeas fun d _ => ?_
    dsimp only
    set P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    set orig := feasOrigPos d.I d.hv d.I.m
    set K1 := bitScalingPhases P' / narrowLimbWidth d.I + 2
    have hm_le : P'.m ≤ 3 * d.I.m := feas_m_le_three_m d.I d.hv d.hiso
    have horig_le : orig.length ≤ d.I.m := by
      have h1 := List.length_filter_le (fun e => decide (0 < (FlowReduction.shiftedGraph d.I d.hv).capacity e))
        ((List.finRange d.I.m).take d.I.m)
      simp only [List.length_take, List.length_finRange, Nat.min_self] at h1
      exact h1
    have hB_le : B P'.n P'.m (circMaxCapacity P') (circMaxCost P') ≤
        B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1 :=
      hB_mono P'.n (d.I.n + 1) P'.m (3 * d.I.m) (circMaxCapacity P')
        (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) (circMaxCost P') 1
        (le_refl _) hm_le (feasibility_withoutZeroEdges_maxCapacity_le d.I d.hv)
        (feasibility_withoutZeroEdges_maxCost_le d.I d.hv)
    have hK1_le : K1 ≤ d.L + 2 := by
      have h1 := stage1_Kcap_le_maxCapLimbs d.I d.hv P' (feasibility_withoutZeroEdges_maxCapacity_le d.I d.hv)
      have h2 := d.hLge
      omega
    have hdiff_le : P'.m - orig.length ≤ 3 * d.I.m := by omega
    have hmul1 : (K1 + 1) * (P'.m - orig.length) ≤ 3 * d.I.m * (d.L + 3) := by
      have h1 : (K1 + 1) * (P'.m - orig.length) ≤ (d.L + 3) * (3 * d.I.m) :=
        Nat.mul_le_mul (by omega) hdiff_le
      linarith
    have hmul2 : (K1 + d.L + 1) * orig.length ≤ d.I.m * (2 * d.L + 3) := by
      have h1 : (K1 + d.L + 1) * orig.length ≤ (2 * d.L + 3) * d.I.m :=
        Nat.mul_le_mul (by omega) horig_le
      linarith
    nlinarith
  · sep_enter d with _ _ h2k1
    exfalso; apply hw
    have hk3 := three_le_narrowLimbWidth d.I
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))

theorem stage0Feas_meetsO {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {B : ℕ → ℕ → ℕ → ℕ → ℕ}
    {f pCopy lCmp cLen copyFl pass1 artEmit artPass artBoth writeHdr feasBuild
      chkOne satCheck scatter feasPost feasPostWrap feasRun feasWork stage1Circ : ℕ}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : p.procs[f]? = some (stage0Feas feasWork))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hlCmp : p.procs[lCmp]? = some limbsCmp)
    (hcLen : p.procs[cLen]? = some canonLen)
    (hcopyFl : p.procs[copyFl]? = some (copyFlowLimbs cLen pCopy))
    (hpass1 : p.procs[pass1]? = some stage0FeasPass1)
    (hartEmit : p.procs[artEmit]? = some stage0FeasArtEmit)
    (hartPass : p.procs[artPass]? = some (stage0FeasArtPass artEmit))
    (hartBoth : p.procs[artBoth]? = some (stage0FeasArtBoth artPass))
    (hwriteHdr : p.procs[writeHdr]? = some writeStage1Hdr)
    (hfeasBuild : p.procs[feasBuild]? = some (stage0FeasBuild pass1 artBoth writeHdr))
    (hchkOne : p.procs[chkOne]? = some (stage0FeasCheckOne cLen lCmp))
    (hsatCheck : p.procs[satCheck]? = some (stage0FeasSatCheck chkOne))
    (hscatter : p.procs[scatter]? = some (stage0FeasScatter copyFl))
    (hfeasPost : p.procs[feasPost]? = some (stage0FeasPost satCheck scatter))
    (hfeasPostWrap : p.procs[feasPostWrap]? = some (stage0FeasPostWrap feasPost))
    (hfeasRun : p.procs[feasRun]? = some (stage0FeasRun stage1Circ feasPostWrap))
    (hfeasWork : p.procs[feasWork]? = some (stage0FeasWork feasBuild feasRun))
    (hstage1 : MeetsO w p stage1Circ (stage1CircSpec w S) fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) :
    MeetsO w p f (stage0FeasSpec w S) fun d _ =>
      d.I.n + d.I.m * (d.L + 1) +
        B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1 + 1 := by
  obtain ⟨K1c, hstage1_m⟩ := hstage1
  have hd := stage0Feas_meets_direct (B := fun n m U C => K1c * B n m U C)
    (fun _ _ _ _ _ _ _ _ h1 h2 h3 h4 => Nat.mul_le_mul_left K1c (hB_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4))
    hp hpCopy hlCmp hcLen hcopyFl hpass1 hartEmit hartPass hartBoth hwriteHdr hfeasBuild
    hchkOne hsatCheck hscatter hfeasPost hfeasPostWrap hfeasRun hfeasWork hstage1_m
  exact MeetsO.of_meets hd ⟨K1c + 2500, fun ⟨d, _⟩ => by
    dsimp only
    set X := d.I.n + d.I.m * (d.L + 1)
    set Y := B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1
    nlinarith⟩

/-! ### Polymorphic module -/

/-- Procedure names for `stage0FeasMod`, polymorphic over any name type `ι`.
`stage1Circ` is an imported procedure name (supplied by the Stage 1 module). -/
structure Stage0FeasNames (ι : Type) where
  padCopy : ι
  limbsCmp : ι
  canonLen : ι
  copyFlowLimbs : ι
  feasPass1 : ι
  feasArtEmit : ι
  feasArtPass : ι
  feasArtBoth : ι
  writeStage1Hdr : ι
  feasBuild : ι
  feasCheckOne : ι
  feasSatCheck : ι
  feasScatter : ι
  feasPost : ι
  feasPostWrap : ι
  feasRun : ι
  feasWork : ι
  stage0Feas : ι
  stage1Circ : ι

/-- Polymorphic module for Stage 0 item 4 (`stage0Feas`), calling `names.stage1Circ`. -/
def stage0FeasMod {ι : Type} (names : Stage0FeasNames ι) : Module ι :=
  ⟨[(names.padCopy, fun _ => padCopy),
    (names.limbsCmp, fun _ => limbsCmp),
    (names.canonLen, fun _ => canonLen),
    (names.copyFlowLimbs, fun idx => copyFlowLimbs (idx names.canonLen) (idx names.padCopy)),
    (names.feasPass1, fun _ => stage0FeasPass1),
    (names.feasArtEmit, fun _ => stage0FeasArtEmit),
    (names.feasArtPass, fun idx => stage0FeasArtPass (idx names.feasArtEmit)),
    (names.feasArtBoth, fun idx => stage0FeasArtBoth (idx names.feasArtPass)),
    (names.writeStage1Hdr, fun _ => writeStage1Hdr),
    (names.feasBuild, fun idx =>
      stage0FeasBuild (idx names.feasPass1) (idx names.feasArtBoth) (idx names.writeStage1Hdr)),
    (names.feasCheckOne, fun idx => stage0FeasCheckOne (idx names.canonLen) (idx names.limbsCmp)),
    (names.feasSatCheck, fun idx => stage0FeasSatCheck (idx names.feasCheckOne)),
    (names.feasScatter, fun idx => stage0FeasScatter (idx names.copyFlowLimbs)),
    (names.feasPost, fun idx =>
      stage0FeasPost (idx names.feasSatCheck) (idx names.feasScatter)),
    (names.feasPostWrap, fun idx => stage0FeasPostWrap (idx names.feasPost)),
    (names.feasRun, fun idx =>
      stage0FeasRun (idx names.stage1Circ) (idx names.feasPostWrap)),
    (names.feasWork, fun idx =>
      stage0FeasWork (idx names.feasBuild) (idx names.feasRun)),
    (names.stage0Feas, fun idx => stage0Feas (idx names.feasWork))]⟩

theorem stage0FeasMod_noRand {ι : Type} (names : Stage0FeasNames ι) :
    (stage0FeasMod names).NoRand := by
  wram_no_rand

theorem stage0FeasMod_meets_direct {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {S : ℕ → ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ} {names : Stage0FeasNames ι}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : (stage0FeasMod names).Placed p idx)
    (hstage1 : Meets w p (idx names.stage1Circ) ((stage1CircSpec w S).withCost fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1))) :
    Meets w p (idx names.stage0Feas) ((stage0FeasSpec w S).withCost fun d _ =>
      2500 * (d.I.n + d.I.m * (d.L + 1) + 1) +
        B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1) :=
  stage0Feas_meets_direct hB_mono
    (hp.get (n := names.stage0Feas) (b := fun idx => stage0Feas (idx names.feasWork)) (by simp [stage0FeasMod]))
    (hp.get (n := names.padCopy) (b := fun _ => padCopy) (by simp [stage0FeasMod]))
    (hp.get (n := names.limbsCmp) (b := fun _ => limbsCmp) (by simp [stage0FeasMod]))
    (hp.get (n := names.canonLen) (b := fun _ => canonLen) (by simp [stage0FeasMod]))
    (hp.get (n := names.copyFlowLimbs) (b := fun idx => copyFlowLimbs (idx names.canonLen) (idx names.padCopy)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasPass1) (b := fun _ => stage0FeasPass1) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasArtEmit) (b := fun _ => stage0FeasArtEmit) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasArtPass) (b := fun idx => stage0FeasArtPass (idx names.feasArtEmit)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasArtBoth) (b := fun idx => stage0FeasArtBoth (idx names.feasArtPass)) (by simp [stage0FeasMod]))
    (hp.get (n := names.writeStage1Hdr) (b := fun _ => writeStage1Hdr) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasBuild) (b := fun idx => stage0FeasBuild (idx names.feasPass1) (idx names.feasArtBoth) (idx names.writeStage1Hdr)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasCheckOne) (b := fun idx => stage0FeasCheckOne (idx names.canonLen) (idx names.limbsCmp)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasSatCheck) (b := fun idx => stage0FeasSatCheck (idx names.feasCheckOne)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasScatter) (b := fun idx => stage0FeasScatter (idx names.copyFlowLimbs)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasPost) (b := fun idx => stage0FeasPost (idx names.feasSatCheck) (idx names.feasScatter)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasPostWrap) (b := fun idx => stage0FeasPostWrap (idx names.feasPost)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasRun) (b := fun idx => stage0FeasRun (idx names.stage1Circ) (idx names.feasPostWrap)) (by simp [stage0FeasMod]))
    (hp.get (n := names.feasWork) (b := fun idx => stage0FeasWork (idx names.feasBuild) (idx names.feasRun)) (by simp [stage0FeasMod]))
    hstage1

theorem stage0FeasMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {S : ℕ → ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ} {names : Stage0FeasNames ι}
    (hB_mono : ∀ n₁ n₂ m₁ m₂ U₁ U₂ C₁ C₂,
      n₁ ≤ n₂ → m₁ ≤ m₂ → U₁ ≤ U₂ → C₁ ≤ C₂ → B n₁ m₁ U₁ C₁ ≤ B n₂ m₂ U₂ C₂)
    (hp : (stage0FeasMod names).Placed p idx)
    (hstage1 : MeetsO w p (idx names.stage1Circ) (stage1CircSpec w S) fun x _ =>
      B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) :
    MeetsO w p (idx names.stage0Feas) (stage0FeasSpec w S) fun d _ =>
      d.I.n + d.I.m * (d.L + 1) +
        B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1 + 1 := by
  obtain ⟨K1c, hstage1_m⟩ := hstage1
  have hd := stage0FeasMod_meets_direct (B := fun n m U C => K1c * B n m U C)
    (fun _ _ _ _ _ _ _ _ h1 h2 h3 h4 => Nat.mul_le_mul_left K1c (hB_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4))
    hp hstage1_m
  exact MeetsO.of_meets hd ⟨K1c + 2500, fun ⟨d, _⟩ => by
    dsimp only
    set X := d.I.n + d.I.m * (d.L + 1)
    set Y := B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1
    nlinarith⟩

end MinCostFlow.NarrowProg
