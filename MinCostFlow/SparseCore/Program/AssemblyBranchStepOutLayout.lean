module

public import MinCostFlow.SparseCore.Program.AssemblyBranchValue

/-!
# Companion step-output layout for the branch module (`AssemblyBranchStepOutLayout`)

Defines `AsmBranchStepOutLayout BR edMul`, strengthening `AsmBranchAt.step_runs`
(`AssemblyTopIface.lean`) without modifying `AsmBranchAt` itself. For every branch step it adds:
* every word in the emitted output order-edits buffer `[ePtr, ePtr + eW)` is `< 2 ^ w`;
* both output buffers `[bPtr, bPtr + bW)` and `[ePtr, ePtr + eW)` are disjoint from the updated
  branch footprint `BR.rep.foot brH x'`;
* the output order-edits word count satisfies
  `eW ≤ edMul * (branchStepCharge … + (words + editWords + 1) * bundleLogFactor M N)` with
  `1 ≤ edMul`.

`asmBranchAt_value_stepOutLayout` discharges this companion structure for the concrete branch
module `asmBranchAt_value` (`AssemblyBranchValue.lean`) with
`edMul := asmBrEdMul (K.stepYs capExp limbMul)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Read

/-- Companion step-output layout and edit-word bound for an `AsmBranchAt` module, with
input-independent multiplier `edMul ≥ 1`. -/
structure AsmBranchStepOutLayout {S : AsmBranchSpec} {CFS : AsmCompFamilySpec} {lsfInit : LSFInit}
    {C_lsst : ℝ} {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs}
    (BR : AsmBranchAt S CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p
      fCFInit fCFBatch CF bp)
    (edMul : ℕ) : Prop where
  edMul_pos : 1 ≤ edMul
  step_outLayout_runs :
    ∀ (brH cfH j batch words edits editWords fChgPtr fChgEnd outSlotPtr reembSlotPtr h
        k M N vCap eCap n : ℕ)
      (tr : BundleTreeState depth) (ord : ℕ → List End) (x : BR.rep.τ)
      (cfsOld cfsNew : CompFamilyAbs) (xcf : CF.rep.τ)
      (U : List Update) (ed : List OrdEdit)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → 0 < k → j < k →
      tr.m₀ = M → tr.n₀ = N → 1 ≤ depth → depth ≤ bundleLogFactor M N →
      depth ≤ Expander.chosenL ((M + N) ^ 2) →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w →
      BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      CF.rep.rep cfH cfsNew xcf mem →
      cfsOld j = tr.cs → cfsNew j = compLSFBatch tr.cs U →
      CompFamilyChgAt w k mem fChgPtr fChgEnd cfsOld U →
      CompSplitListAt w k mem (fChgPtr + k) fChgEnd cfsOld U →
      fChgEnd ≤ h →
      SmallBatchAt mem batch tr.cs.G U words → tr.cs.G.BatchIsValid U →
      BatchWithinCaps vCap eCap U →
      OrdEditsAt mem edits ed editWords → OrderedBatch tr.cs.G U ord (applyOrdEdits ord ed) →
      OrdEditsValidFor vCap eCap ord ed →
      OrdEditsForBatch tr.cs.G U ed →
      (∀ t < words, mem (batch + t) < 2 ^ w) → (∀ t < editWords, mem (edits + t) < 2 ^ w) →
      batch + words ≤ h → edits + editWords ≤ h →
      outSlotPtr + 4 ≤ h → reembSlotPtr + 2 ≤ h →
      (∀ a, outSlotPtr ≤ a → a < outSlotPtr + 4 → ¬ (reembSlotPtr ≤ a ∧ a < reembSlotPtr + 2)) →
      (∀ a, BR.rep.foot brH x a → a < h) →
      (∀ a, CF.rep.foot cfH xcf a → a < h) →
      (∀ a, BR.rep.foot brH x a → ¬ CF.rep.foot cfH xcf a) →
      (∀ a, outSlotPtr ≤ a → a < outSlotPtr + 4 →
        ¬ BR.rep.foot brH x a ∧ ¬ CF.rep.foot cfH xcf a) →
      (∀ a, reembSlotPtr ≤ a → a < reembSlotPtr + 2 →
        ¬ BR.rep.foot brH x a ∧ ¬ CF.rep.foot cfH xcf a) →
      (∀ a, batch ≤ a → a < batch + words → ¬ BR.rep.foot brH x a) →
      (∀ a, edits ≤ a → a < edits + editWords → ¬ BR.rep.foot brH x a) →
      (∀ a, fChgPtr ≤ a → a < fChgEnd → ¬ BR.rep.foot brH x a) →
      fChgPtr + j < 2 ^ w → mem (fChgPtr + j) < 2 ^ w →
      (∀ a ∈ [brH, cfH, j, batch, words, edits, editWords, fChgPtr, outSlotPtr, reembSlotPtr, h],
        a < 2 ^ w) →
      ZeroFrom mem h →
      h + (S.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords) <
        2 ^ w →
      let ord' := applyOrdEdits ord ed
      let info := stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord'
      ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N →
      BranchUpdatesBelow impl tr n →
      BranchUpdatesBelow impl info.state (n + U.length) →
      AsmBrModelFacts impl vCap eCap tr ord →
      AsmBrModelFacts impl vCap eCap info.state ord' →
      ∃ body, p.procs[bp.fStep]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState
          [brH, cfH, j, batch, words, edits, editWords, fChgPtr, outSlotPtr, reembSlotPtr, h,
            fChgPtr + k] mem pos) o st' c ∧
        BR.rep.rep brH ⟨info.state, ord', vCap, eCap⟩ x' st'.mem ∧
        SmallBatchAt st'.mem (st'.mem outSlotPtr) tr.S_cur info.U_S (st'.mem (outSlotPtr + 1)) ∧
        h ≤ st'.mem outSlotPtr ∧
        st'.mem outSlotPtr + st'.mem (outSlotPtr + 1) ≤ o.value ∧
        (∃ outEd : List OrdEdit,
          OrdEditsAt st'.mem (st'.mem (outSlotPtr + 2)) outEd (st'.mem (outSlotPtr + 3)) ∧
          applyOrdEdits (tr.outOrder ord) outEd = info.state.outOrder ord' ∧
          OrdEditsValidFor vCap eCap (tr.outOrder ord) outEd ∧
          OrdEditsForBatch tr.S_cur info.U_S outEd) ∧
        h ≤ st'.mem (outSlotPtr + 2) ∧
        st'.mem (outSlotPtr + 2) + st'.mem (outSlotPtr + 3) ≤ o.value ∧
        readList st'.mem (st'.mem reembSlotPtr) (st'.mem (reembSlotPtr + 1)) =
          brReemb tr U ord ord' ∧
        h ≤ st'.mem reembSlotPtr ∧
        st'.mem reembSlotPtr + st'.mem (reembSlotPtr + 1) ≤ o.value ∧
        h ≤ o.value ∧
        o.value ≤ h + (S.stepSpace capExp).eval
          (M + N + k + vCap + eCap + L + depth + words + editWords) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ BR.rep.foot brH x a →
          ¬ (outSlotPtr ≤ a ∧ a < outSlotPtr + 4) →
          ¬ (reembSlotPtr ≤ a ∧ a < reembSlotPtr + 2) → st'.mem a = mem a) ∧
        (∀ a, BR.rep.foot brH x' a → BR.rep.foot brH x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ t < st'.mem (outSlotPtr + 3), st'.mem (st'.mem (outSlotPtr + 2) + t) < 2 ^ w) ∧
        (∀ a, st'.mem outSlotPtr ≤ a → a < st'.mem outSlotPtr + st'.mem (outSlotPtr + 1) →
          ¬ BR.rep.foot brH x' a) ∧
        (∀ a, st'.mem (outSlotPtr + 2) ≤ a →
          a < st'.mem (outSlotPtr + 2) + st'.mem (outSlotPtr + 3) → ¬ BR.rep.foot brH x' a) ∧
        st'.mem (outSlotPtr + 3) ≤
          edMul * (branchStepCharge (fun _ => canonicalSparsify impl) tr U ord ord' +
            (words + editWords + 1) * bundleLogFactor M N) ∧
        c + BR.rep.phi brH x' st'.mem ≤
          S.mul capExp limbMul * (branchStepCharge (fun _ => canonicalSparsify impl) tr U ord ord' +
            (words + editWords + 1) * bundleLogFactor M N) + BR.rep.phi brH x mem

/-- The concrete branch module `asmBranchAt_value` satisfies `AsmBranchStepOutLayout` with
multiplier `asmBrEdMul (K.stepYs capExp limbMul)`. -/
theorem asmBranchAt_value_stepOutLayout {K : AsmBrConsts} {CFS : AsmCompFamilySpec}
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ}
    {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs} {I : AsmBrProcIdx} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {Ψ : BundleTreeState depth → ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    (hΨ : AsmWalkPotRestartOK impl depth Ψ)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ K.Cγ * (m + 2) ^ K.cγ)
    (hRe : ∀ tr U ord ord', brReemb tr U ord ord' =
      stepBundleTree_reembList (fun _ => canonicalSparsify impl) tr U ord ord')
    (hP : HasAsmBrProcs p bp impl CF.fRoot I)
    (X : AsmBrPieces K lsfInit depth w fmt L capExp limbMul impl p I TR B5 Ψ CF.rep) :
    AsmBranchStepOutLayout
      (asmBranchAt_value (C_lsst := C_lsst) hTR hB5 hTh hΨ hγ hRe hP X)
      (asmBrEdMul (K.stepYs capExp limbMul)) where
  edMul_pos := by unfold asmBrEdMul; omega
  step_outLayout_runs := by
    intro brH cfH j batch words edits editWords fChgPtr fChgEnd outSlotPtr reembSlotPtr h k M N
      vCap eCap n tr ord x cfsOld cfsNew xcf U ed mem pos ω _ _ hj hM hN hdepth hdepth_lg hdepth_ch hcap hword hrep _ hold _
      hC hSp hCend hBat hBU hcaps hEd hord hEdV hEdB hbW heW hbE heE hos hrs hslots hfoot _ _ hosF
      hrsF hbF heF hCF hfj hchgW hargs hz hsp ord' info hThU hBUn hBUn' hmf hmf'
    have hWE : asmP10WordExp capExp ≤ asmBrWordExp K capExp := le_max_left _ _
    have h16 : 16 ≤ 2 ^ w :=
      Nat.le_of_lt <| lt_of_le_of_lt (show 16 ≤ (M + N + 2) ^ asmBrWordExp K capExp * (L + 1) from
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ (M + N + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
          _ ≤ (M + N + 2) ^ asmBrWordExp K capExp :=
              Nat.pow_le_pow_right (by omega) ((asmP10WordExp_ge_four capExp).trans hWE)
          _ ≤ (M + N + 2) ^ asmBrWordExp K capExp * (L + 1) := Nat.le_mul_of_pos_right _ (by omega))
        hword
    obtain ⟨c, hcAt, hcEx, hCin⟩ := compFamilyChgAt_branch hC hj hold hCend hCF
    obtain ⟨hSpAt, hSpin, hspW⟩ := compSplitListAt_branch hSp hj hold hCend
      (fun a h1 h2 => hCF a (by omega) h2)
    have hspjW : fChgPtr + k + j < 2 ^ w := by
      have hhW : h < 2 ^ w := hargs h (by simp)
      have := hSp.1; omega
    have hRB := asmBrFull_readBranchAt (Q := CF.toRootQueryAt)
      (asmBrReadAt_of_hasReadProcs hP.read) hWE hM hN hcap hword hrep k
      ⟨impl, 0, w, 0, 0, 0, 0⟩ 0 rfl (Nat.zero_le _)
    have hsp' : h + (asmBrStepPoly X.JS.spaceP readBranchMul K.OS.querySpace capExp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) < 2 ^ w := by
      rw [X.JS_space]; exact hsp
    obtain ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
        h14, h15, h16', hEdLt, hDisjB, hDisjE, hEdW, hcost⟩ :=
      Classical.choose_spec (asmBrFull_step_runs_clause sig_outStepSmall_blocks_runs_outProcs) X.JS hB5
        hTR X.out hTh hP.out hP.step brH cfH j batch words edits editWords fChgPtr outSlotPtr
        reembSlotPtr h (fChgPtr + k) k M N vCap eCap n tr ord x U ed c ⟨impl, 0, w, 0, 0, 0, 0⟩ 0
        mem pos ω hRB hM hN hdepth hdepth_lg hdepth_ch hcap h16 hword hThU hBUn hBUn' hrep hmf hmf' hBat hBU hcaps hEd hord
        hEdV hEdB hcAt hcEx hSpAt
        (inputAt_of hbW hbE hbF) (inputAt_of heW heE heF) hCin hSpin hos hrs hslots
        (fun a h1 h2 => (hosF a h1 h2).1) (fun a h1 h2 => (hrsF a h1 h2).1) hfoot hargs hchgW hfj
        hspW hspjW (capSq_lt_of_wordExp hcap hWE hword) hz hsp'
    refine ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, ?_, h10, h11, h12, ?_,
      h14, h15, h16', hEdLt, hDisjB, hDisjE, ?_, ?_⟩
    · rw [hRe]; exact h9
    · rw [X.JS_space] at h13; exact h13
    · rw [← X.JS_ys]; exact hEdW
    · refine hcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _)
      rw [X.JS_mul, X.JS_ys]; exact asmBrSpec_mul_step

end MinCostFlow.SparseCore.Program
