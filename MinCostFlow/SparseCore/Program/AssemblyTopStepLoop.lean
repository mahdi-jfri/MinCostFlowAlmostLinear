module

public import MinCostFlow.SparseCore.Program.AssemblyTopIface
public import WordRAM.Logic

/-!
# Amortized `k`-branch step loop for the top-layer sparse-core program (`AssemblyTopStepLoop`)

Runs `BR.step_runs` on every branch `j = 0, …, k - 1`, writing `BranchOutAt` entries at
`outPtr + 1 + 4 * j` and `reembList` entries at `outPtr + 1 + 4 * k + 2 * j`, while preserving
pairwise disjointness and amortized potential bounds.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

def asmStepBranchStep (fBrStep : ℕ) : Stmt :=
  .assign 16 (.load (.bin .add (.reg 12) (.reg 15))) ;;
  .assign 17 (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 4) (.reg 15))) ;;
  .assign 18 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 4) (.reg 10)))
    (.bin .mul (.const 2) (.reg 15))) ;;
  .call 14 fBrStep [.reg 16, .reg 11, .reg 15, .reg 2, .reg 3, .reg 4, .reg 5,
    .reg 13, .reg 17, .reg 18, .reg 14, .bin .add (.reg 13) (.reg 10)] ;;
  .assign 15 (.bin .add (.reg 15) (.const 1))

/-- Loop stepping all `k` branches `j = 0 .. k - 1` and writing `BranchOutReembAt` at `outPtr`. -/
def asmStepBranchesLoop (fBrStep : ℕ) : Stmt :=
  .assign 15 (.const 0) ;;
  .loop (.bin .lt (.reg 15) (.reg 10)) (asmStepBranchStep fBrStep)

theorem asmStepBranchesLoop_noRand (fBrStep : ℕ) : (asmStepBranchesLoop fBrStep).NoRand := by
  simp [asmStepBranchesLoop, asmStepBranchStep, Stmt.NoRand]

private theorem sum_Ico_cons {i k : ℕ} (h : i < k) (f : ℕ → ℕ) :
    (Finset.Ico i k).sum f = f i + (Finset.Ico (i + 1) k).sum f := by
  have h1 : Finset.Ico i k = insert i (Finset.Ico (i + 1) k) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [h1, Finset.sum_insert (by simp)]

/-! ## Verification of `asmStepBranchesLoop` -/

/-- Branch `j`'s output slots and payloads at `outPtr` are valid and live inside `[hStart, hCur)`. -/
private def BranchSlotDone {depth : ℕ} {impl : SparsifyImpl}
    (brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (mem : ℕ → ℕ) (outPtr k vCap eCap hStart hCur : ℕ)
    (tr : ℕ → BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End) (j : ℕ) : Prop :=
  let info := stepBundleTree (fun _ => canonicalSparsify impl) (tr j) U ord ord'
  SmallBatchAt mem (mem (outPtr + 1 + 4 * j)) (tr j).S_cur info.U_S (mem (outPtr + 2 + 4 * j)) ∧
  hStart ≤ mem (outPtr + 1 + 4 * j) ∧
  mem (outPtr + 1 + 4 * j) + mem (outPtr + 2 + 4 * j) ≤ hCur ∧
  (∃ outEd, OrdEditsAt mem (mem (outPtr + 3 + 4 * j)) outEd (mem (outPtr + 4 + 4 * j)) ∧
    applyOrdEdits ((tr j).outOrder ord) outEd = info.state.outOrder ord' ∧
    OrdEditsValidFor vCap eCap ((tr j).outOrder ord) outEd ∧
    OrdEditsForBatch (tr j).S_cur info.U_S outEd) ∧
  hStart ≤ mem (outPtr + 3 + 4 * j) ∧
  mem (outPtr + 3 + 4 * j) + mem (outPtr + 4 + 4 * j) ≤ hCur ∧
  readList mem (mem (outPtr + 1 + 4 * k + 2 * j)) (mem (outPtr + 2 + 4 * k + 2 * j)) =
    brReemb (tr j) U ord ord' ∧
  hStart ≤ mem (outPtr + 1 + 4 * k + 2 * j) ∧
  mem (outPtr + 1 + 4 * k + 2 * j) + mem (outPtr + 2 + 4 * k + 2 * j) ≤ hCur

private theorem branchSlotDone_frame {depth : ℕ} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {mem₁ mem₂ : ℕ → ℕ} {outPtr k vCap eCap hStart hCur hNext : ℕ}
    {tr : ℕ → BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End} {j : ℕ}
    (hdone : BranchSlotDone (impl := impl) brReemb mem₁ outPtr k vCap eCap hStart hCur tr U ord ord' j)
    (hle : hCur ≤ hNext)
    (hslots : mem₂ (outPtr + 1 + 4 * j) = mem₁ (outPtr + 1 + 4 * j) ∧
      mem₂ (outPtr + 2 + 4 * j) = mem₁ (outPtr + 2 + 4 * j) ∧
      mem₂ (outPtr + 3 + 4 * j) = mem₁ (outPtr + 3 + 4 * j) ∧
      mem₂ (outPtr + 4 + 4 * j) = mem₁ (outPtr + 4 + 4 * j) ∧
      mem₂ (outPtr + 1 + 4 * k + 2 * j) = mem₁ (outPtr + 1 + 4 * k + 2 * j) ∧
      mem₂ (outPtr + 2 + 4 * k + 2 * j) = mem₁ (outPtr + 2 + 4 * k + 2 * j))
    (hpay : ∀ a, hStart ≤ a → a < hCur → mem₂ a = mem₁ a) :
    BranchSlotDone (impl := impl) brReemb mem₂ outPtr k vCap eCap hStart hNext tr U ord ord' j := by
  rcases hdone with ⟨hSB, huLo, huHi, ⟨outEd, hOE, hOEeq, hOEV, hOEB⟩, heLo, heHi, hRL, hrLo, hrHi⟩
  rcases hslots with ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩
  refine ⟨?_, by omega, by omega, ⟨outEd, ?_, hOEeq, hOEV, hOEB⟩, by omega, by omega, ?_, by omega, by omega⟩
  · rw [hs1, hs2]
    exact smallBatchAt_of_agree hSB fun a ha1 ha2 => hpay a (by omega) (by omega)
  · rw [hs3, hs4]
    exact ordEditsAt_of_agree hOE fun a ha1 ha2 => hpay a (by omega) (by omega)
  · rw [hs5, hs6]
    exact (readList_of_agree fun a ha1 ha2 => hpay a (by omega) (by omega)).trans hRL

private theorem asmStepBranchesLoop_go
    {S : AsmBranchSpec} {CFS : AsmCompFamilySpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs}
    (BR : AsmBranchAt S CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    {batch words edits editWords outPtr k M N vCap eCap cfH tbl fChgPtr fChgEnd hStart : ℕ}
    {tr : ℕ → BundleTreeState depth} {ord : ℕ → List End} {cfsOld cfsNew : CompFamilyAbs}
    {xcf : CF.rep.τ} {U : List Update} {ed : List OrdEdit} {brH : ℕ → ℕ}
    (hfmt : fmt.limbBits = 4) (hk : 0 < k)
    (hMN : ∀ j < k, (tr j).m₀ = M ∧ (tr j).n₀ = N ∧ (tr j).cs.G = (tr 0).cs.G)
    (hdepth : 1 ≤ depth) (hdepth_lg : depth ≤ bundleLogFactor M N)
    (hdepth_ch : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hwBR : (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hcfsOld : ∀ j < k, cfsOld j = (tr j).cs)
    (hcfsNew : ∀ j < k, cfsNew j = compLSFBatch (tr j).cs U)
    (hUval : (tr 0).cs.G.BatchIsValid U) (hUcap : BatchWithinCaps vCap eCap U)
    (hOrdB : OrderedBatch (tr 0).cs.G U ord (applyOrdEdits ord ed))
    (hEdVal : OrdEditsValidFor vCap eCap ord ed)
    (hEdBlocks : OrdEditsForBatch (tr 0).cs.G U ed)
    (hB_le : batch + words ≤ hStart) (hE_le : edits + editWords ≤ hStart)
    (hout_le : outPtr + 1 + 6 * k ≤ hStart) (htbl_le : tbl + k ≤ hStart)
    (hfChg_le : fChgEnd ≤ hStart)
    (hcfFoot : ∀ a, CF.rep.foot cfH xcf a → a < hStart)
    (hcf_disj_out : ∀ a, outPtr ≤ a → a < outPtr + 1 + 6 * k → ¬ CF.rep.foot cfH xcf a)
    (hB_disj_out : ∀ a, batch ≤ a → a < batch + words → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (hE_disj_out : ∀ a, edits ≤ a → a < edits + editWords → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (htbl_disj_out : ∀ a, tbl ≤ a → a < tbl + k → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (hfChg_disj_out : ∀ a, fChgPtr ≤ a → a < fChgEnd → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (hargsW : ∀ a ∈ [cfH, batch, words, edits, editWords, outPtr, k, tbl, fChgPtr], a < 2 ^ w)
    (hbrW : ∀ j < k, brH j < 2 ^ w)
    (hsp : hStart + k * (S.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords) < 2 ^ w)
    {n : ℕ}
    (hThr : ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N)
    (hUpdPre : ∀ j < k, BranchUpdatesBelow impl (tr j) n)
    (hUpdPost : ∀ j < k, BranchUpdatesBelow impl
      (stepBundleTree (fun _ => canonicalSparsify impl) (tr j) U ord (applyOrdEdits ord ed)).state
      (n + U.length))
    (hModPre : ∀ j < k, AsmBrModelFacts impl vCap eCap (tr j) ord)
    (hModPost : ∀ j < k, AsmBrModelFacts impl vCap eCap
      (stepBundleTree (fun _ => canonicalSparsify impl) (tr j) U ord (applyOrdEdits ord ed)).state
      (applyOrdEdits ord ed))
    (ω : ℕ → Bool) :
    let stepSp := (S.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords)
    let ord' := applyOrdEdits ord ed
    let info := fun j => stepBundleTree (fun _ => canonicalSparsify impl) (tr j) U ord ord'
    ∀ (rem i : ℕ) (st : State) (xCur : ℕ → BR.rep.τ),
      i + rem = k →
      st.regs 2 = batch → st.regs 3 = words → st.regs 4 = edits →
      st.regs 5 = editWords → st.regs 8 = outPtr → st.regs 10 = k →
      st.regs 11 = cfH → st.regs 12 = tbl → st.regs 13 = fChgPtr → st.regs 15 = i →
      hStart ≤ st.regs 14 → st.regs 14 ≤ hStart + i * stepSp →
      ZeroFrom st.mem (st.regs 14) →
      CF.rep.rep cfH cfsNew xcf st.mem →
      CompFamilyChgAt w k st.mem fChgPtr fChgEnd cfsOld U →
      CompSplitListAt w k st.mem (fChgPtr + k) fChgEnd cfsOld U →
      SmallBatchAt st.mem batch (tr 0).cs.G U words →
      OrdEditsAt st.mem edits ed editWords →
      (∀ t < words, st.mem (batch + t) < 2 ^ w) → (∀ t < editWords, st.mem (edits + t) < 2 ^ w) →
      (∀ j < k, st.mem (tbl + j) = brH j) →
      (∀ j < i, BR.rep.rep (brH j) ⟨(info j).state, ord', vCap, eCap⟩ (xCur j) st.mem) →
      (∀ j, i ≤ j → j < k → BR.rep.rep (brH j) ⟨tr j, ord, vCap, eCap⟩ (xCur j) st.mem ∧
        ∀ a, BR.rep.foot (brH j) (xCur j) a → a < hStart) →
      (∀ j < k, ∀ a, BR.rep.foot (brH j) (xCur j) a → a < st.regs 14 ∧ ¬ CF.rep.foot cfH xcf a ∧
        ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k) ∧ ¬ (tbl ≤ a ∧ a < tbl + k) ∧
        ¬ (batch ≤ a ∧ a < batch + words) ∧ ¬ (edits ≤ a ∧ a < edits + editWords) ∧
        ¬ (fChgPtr ≤ a ∧ a < fChgEnd)) →
      (∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ → ∀ a,
        BR.rep.foot (brH j₁) (xCur j₁) a → ¬ BR.rep.foot (brH j₂) (xCur j₂) a) →
      (∀ j < i, BranchSlotDone (impl := impl) brReemb st.mem outPtr k vCap eCap hStart (st.regs 14) tr U ord ord' j) →
      ∃ (st' : State) (c : ℕ) (xNew : ℕ → BR.rep.τ),
        Runs w p ω (.loop (.bin .lt (.reg 15) (.reg 10)) (asmStepBranchStep bp.fStep)) st .normal st' c ∧
        st.regs 14 ≤ st'.regs 14 ∧ st'.regs 14 ≤ hStart + k * stepSp ∧
        ZeroFrom st'.mem (st'.regs 14) ∧
        (∀ j < i, xNew j = xCur j) ∧
        (∀ a < st.regs 14, (∀ j, i ≤ j → j < k → ¬ BR.rep.foot (brH j) (xCur j) a) →
          ¬ (outPtr + 1 + 4 * i ≤ a ∧ a < outPtr + 1 + 4 * k) →
          ¬ (outPtr + 1 + 4 * k + 2 * i ≤ a ∧ a < outPtr + 1 + 6 * k) →
          st'.mem a = st.mem a) ∧
        (∀ j < k, BR.rep.rep (brH j) ⟨(info j).state, ord', vCap, eCap⟩ (xNew j) st'.mem) ∧
        (∀ j < k, ∀ a, BR.rep.foot (brH j) (xNew j) a →
          BR.rep.foot (brH j) (xCur j) a ∨ (st.regs 14 ≤ a ∧ a < st'.regs 14)) ∧
        (∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ → ∀ a,
          BR.rep.foot (brH j₁) (xNew j₁) a → ¬ BR.rep.foot (brH j₂) (xNew j₂) a) ∧
        (∀ j < k, BranchSlotDone (impl := impl) brReemb st'.mem outPtr k vCap eCap hStart (st'.regs 14) tr U ord ord' j) ∧
        c + (Finset.Ico i k).sum (fun j => BR.rep.phi (brH j) (xNew j) st'.mem) ≤
          (Finset.Ico i k).sum (fun j => S.mul capExp limbMul *
            (branchStepCharge (fun _ => canonicalSparsify impl) (tr j) U ord ord' +
              (words + editWords + 1) * bundleLogFactor M N)) +
          70 * rem + 10 +
          (Finset.Ico i k).sum (fun j => BR.rep.phi (brH j) (xCur j) st.mem) := by
  intro stepSp ord' info rem
  change hStart + k * stepSp < 2 ^ w at hsp
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hcfW, hbW, hwW, heW, hewW, houtW, hkW, htblW, hfChgW⟩
  induction rem with
  | zero =>
    intro i st xCur hik r2 r3 r4 r5 r8 r10 r11 r12 r13 r15 hlo hhi hz hcf hchg _hspL hB hEd
      hBw hEw htbl hdone htodo hft hdisj hout
    have hi : i = k := by omega
    subst hi
    have hlt0 : (Expr.bin .lt (.reg 15) (.reg 10)).eval w st = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq r15) (Expr.eval_reg_of_eq r10) (le_refl _) h1w
    refine ⟨st, _, xCur, runs_loop_iff.mpr (Or.inl ⟨hlt0, rfl, rfl, rfl⟩),
      le_rfl, hhi, hz, fun _ _ => rfl, fun _ _ _ _ _ => rfl, hdone, fun _ _ _ ha => Or.inl ha,
      hdisj, hout, ?_⟩
    simp [Expr.size]
  | succ rem ih =>
    intro i st xCur hik r2 r3 r4 r5 r8 r10 r11 r12 r13 r15 hlo hhi hz hcf hchg hspL hB hEd
      hBw hEw htbl hdone htodo hft hdisj hout
    have hilt : i < k := by omega
    set hCur := st.regs 14 with hhCur_def
    have hhCur_w : hCur < 2 ^ w := by
      have : i * stepSp ≤ k * stepSp := Nat.mul_le_mul_right _ (by omega)
      omega
    have hsp_i : hCur + stepSp < 2 ^ w := by
      have : (i + 1) * stepSp ≤ k * stepSp := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_one_mul] at this; omega
    have hlt1 : (Expr.bin .lt (.reg 15) (.reg 10)).eval w st = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq r15) (Expr.eval_reg_of_eq r10) hilt h1w
    -- Step 1: r16 := mem[tbl + i], r17 := outPtr + 1 + 4 * i, r18 := outPtr + 1 + 4 * k + 2 * i
    have ha16 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 12) (.reg 15)))) st .normal
        { st with regs := Function.update st.regs 16 (brH i) } _ :=
      runs_assign_iff.mpr ⟨brH i,
        Expr.eval_load_of_eq (w := w)
          (Expr.eval_add (Expr.eval_reg_of_eq r12) (Expr.eval_reg_of_eq r15) (by omega))
          (htbl i hilt), rfl, rfl, rfl⟩
    set st1 : State := { st with regs := Function.update st.regs 16 (brH i) }
    set slotP := outPtr + 1 + 4 * i
    have ha17 : Runs w p ω (.assign 17 (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 4) (.reg 15)))) st1 .normal
        { st1 with regs := Function.update st1.regs 17 slotP } _ :=
      runs_assign_iff.mpr ⟨slotP,
        Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (v := outPtr) (by simp [st1, r8])) (Expr.eval_const h1w) (by omega))
          (Expr.eval_mul (Expr.eval_const hw4) (Expr.eval_reg_of_eq (v := i) (by simp [st1, r15])) (by omega))
          (by omega), rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 17 slotP }
    set rSlotP := outPtr + 1 + 4 * k + 2 * i
    have ha18 : Runs w p ω (.assign 18 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 1))
        (.bin .mul (.const 4) (.reg 10))) (.bin .mul (.const 2) (.reg 15)))) st2 .normal
        { st2 with regs := Function.update st2.regs 18 rSlotP } _ :=
      runs_assign_iff.mpr ⟨rSlotP,
        Expr.eval_add
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := outPtr) (by simp [st2, st1, r8])) (Expr.eval_const h1w) (by omega))
            (Expr.eval_mul (Expr.eval_const hw4) (Expr.eval_reg_of_eq (v := k) (by simp [st2, st1, r10])) (by omega))
            (by omega))
          (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (v := i) (by simp [st2, st1, r15])) (by omega))
          (by omega), rfl, rfl, rfl⟩
    set st3 : State := { st2 with regs := Function.update st2.regs 18 rSlotP }
    -- Step 2: call BR.step_runs on branch i
    have hMN_i := hMN i hilt
    have hGi : (tr i).cs.G = (tr 0).cs.G := hMN_i.2.2
    have hargs_step : ∀ a ∈ [brH i, cfH, i, batch, words, edits, editWords, fChgPtr, slotP, rSlotP, hCur], a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hbrW i hilt
      all_goals omega
    obtain ⟨body, hbody, oB, stB, cB, xi', hrunB, hrepBi', hSBi', huLo, huHi, hEdi', heLo, heHi,
        hRLi', hrLo, hrHi, hB_lo, hB_hi, hzB, hB_fr, hB_ft, hcostB⟩ :=
      BR.step_runs (brH i) cfH i batch words edits editWords fChgPtr fChgEnd slotP rSlotP hCur
        k M N vCap eCap n (tr i) ord (xCur i) cfsOld cfsNew xcf U ed st3.mem st3.pos ω
        hfmt hk hilt hMN_i.1 hMN_i.2.1 hdepth hdepth_lg hdepth_ch hcap hwBR
        (htodo i le_rfl hilt).1 hcf (hcfsOld i hilt) (hcfsNew i hilt) hchg hspL (by omega)
        (hGi ▸ hB) (hGi ▸ hUval) hUcap hEd (hGi ▸ hOrdB) hEdVal (hGi ▸ hEdBlocks) hBw hEw
        (by omega) (by omega) (by omega) (by omega) (fun a ha1 ha2 => by omega)
        (fun a ha => (hft i hilt a ha).1) (fun a ha => by have := hcfFoot a ha; omega)
        (fun a ha => (hft i hilt a ha).2.1)
        (fun a ha1 ha2 => ⟨fun hfi => (hft i hilt a hfi).2.2.1 ⟨by omega, by omega⟩,
          hcf_disj_out a (by omega) (by omega)⟩)
        (fun a ha1 ha2 => ⟨fun hfi => (hft i hilt a hfi).2.2.1 ⟨by omega, by omega⟩,
          hcf_disj_out a (by omega) (by omega)⟩)
        (fun a ha1 ha2 hfi => (hft i hilt a hfi).2.2.2.2.1 ⟨ha1, ha2⟩)
        (fun a ha1 ha2 hfi => (hft i hilt a hfi).2.2.2.2.2.1 ⟨ha1, ha2⟩)
        (fun a ha1 ha2 hfi => (hft i hilt a hfi).2.2.2.2.2.2 ⟨ha1, ha2⟩)
        (by have := hchg.1; omega)
        (by have := hchg.1; exact hchg.2.1 (fChgPtr + i) (by omega) (by omega))
        hargs_step hz hsp_i hThr (hUpdPre i hilt) (hUpdPost i hilt) (hModPre i hilt) (hModPost i hilt)
    set hNext := oB.value
    have hcall : Runs w p ω (.call 14 bp.fStep [.reg 16, .reg 11, .reg 15, .reg 2, .reg 3,
        .reg 4, .reg 5, .reg 13, .reg 17, .reg 18, .reg 14, .bin .add (.reg 13) (.reg 10)]) st3 .normal
        { stB with regs := Function.update st3.regs 14 hNext }
        (argsSize [.reg 16, .reg 11, .reg 15, .reg 2, .reg 3,
          .reg 4, .reg 5, .reg 13, .reg 17, .reg 18, .reg 14, .bin .add (.reg 13) (.reg 10)] + cB + 1) := by
      have hfChg_k_w : fChgPtr + k < 2 ^ w := by have := hchg.1; omega
      refine (runs_call_iff (r := 14) (f := bp.fStep) (st := st3) (o := .normal)
        (st' := { stB with regs := Function.update st3.regs 14 hNext })).mpr
        ⟨[brH i, cfH, i, batch, words, edits, editWords, fChgPtr, slotP, rSlotP, hCur, fChgPtr + k],
          body, oB, stB, cB, ?_, hbody, hrunB, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, BinOp.eval, hfChg_k_w, st3, st2, st1, r2, r3, r4, r5, r10, r11, r13, r15, hhCur_def]
    set st4 : State := { stB with regs := Function.update st3.regs 14 hNext }
    have hinc : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 1))) st4 .normal
        { st4 with regs := Function.update st4.regs 15 (i + 1) } _ :=
      runs_assign_iff.mpr ⟨i + 1,
        Expr.eval_add (Expr.eval_reg_of_eq (v := i) (by simp [st4, st3, st2, st1, r15])) (Expr.eval_const h1w) (by omega),
        rfl, rfl, rfl⟩
    set st5 : State := { st4 with regs := Function.update st4.regs 15 (i + 1) }
    have hstep_run := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha16,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, ha17,
        runs_seq_iff.mpr (Or.inr ⟨st3, _, _, ha18,
          runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcall, hinc, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    -- Frame all invariants across BR.step_runs
    set xMid := Function.update xCur i xi'
    have hmem_fr : ∀ a < hCur, ¬ BR.rep.foot (brH i) (xCur i) a →
        ¬ (slotP ≤ a ∧ a < slotP + 4) → ¬ (rSlotP ≤ a ∧ a < rSlotP + 2) →
        st5.mem a = st.mem a := hB_fr
    have hcf5 : CF.rep.rep cfH cfsNew xcf st5.mem :=
      (CF.rep_local cfH cfsNew xcf st.mem st5.mem fun a ha =>
        (hmem_fr a (by have := hcfFoot a ha; omega)
          (fun hf => (hft i hilt a hf).2.1 ha)
          (fun hr => hcf_disj_out a (by omega) (by omega) ha)
          (fun hr => hcf_disj_out a (by omega) (by omega) ha)).symm).1 hcf
    have hchg5 : CompFamilyChgAt w k st5.mem fChgPtr fChgEnd cfsOld U :=
      compFamilyChgAt_congr (fun a ha1 ha2 =>
        (hmem_fr a (by omega)
          (fun hf => (hft i hilt a hf).2.2.2.2.2.2 ⟨ha1, ha2⟩)
          (fun hr => hfChg_disj_out a ha1 ha2 ⟨by omega, by omega⟩)
          (fun hr => hfChg_disj_out a ha1 ha2 ⟨by omega, by omega⟩)).symm) hchg
    have hspL5 : CompSplitListAt w k st5.mem (fChgPtr + k) fChgEnd cfsOld U :=
      compSplitListAt_congr (fun a ha1 ha2 =>
        (hmem_fr a (by omega)
          (fun hf => (hft i hilt a hf).2.2.2.2.2.2 ⟨by omega, ha2⟩)
          (fun hr => hfChg_disj_out a (by omega) ha2 ⟨by omega, by omega⟩)
          (fun hr => hfChg_disj_out a (by omega) ha2 ⟨by omega, by omega⟩)).symm) hspL
    have hB5 : SmallBatchAt st5.mem batch (tr 0).cs.G U words :=
      smallBatchAt_of_agree hB fun a ha1 ha2 =>
        hmem_fr a (by omega)
          (fun hf => (hft i hilt a hf).2.2.2.2.1 ⟨ha1, ha2⟩)
          (fun hr => hB_disj_out a ha1 ha2 ⟨by omega, by omega⟩)
          (fun hr => hB_disj_out a ha1 ha2 ⟨by omega, by omega⟩)
    have hEd5 : OrdEditsAt st5.mem edits ed editWords :=
      ordEditsAt_of_agree hEd fun a ha1 ha2 =>
        hmem_fr a (by omega)
          (fun hf => (hft i hilt a hf).2.2.2.2.2.1 ⟨ha1, ha2⟩)
          (fun hr => hE_disj_out a ha1 ha2 ⟨by omega, by omega⟩)
          (fun hr => hE_disj_out a ha1 ha2 ⟨by omega, by omega⟩)
    have hBw5 : ∀ t < words, st5.mem (batch + t) < 2 ^ w := fun t ht => by
      rw [hmem_fr (batch + t) (by omega)
        (fun hf => (hft i hilt _ hf).2.2.2.2.1 ⟨by omega, by omega⟩)
        (fun hr => hB_disj_out (batch + t) (by omega) (by omega) ⟨by omega, by omega⟩)
        (fun hr => hB_disj_out (batch + t) (by omega) (by omega) ⟨by omega, by omega⟩)]
      exact hBw t ht
    have hEw5 : ∀ t < editWords, st5.mem (edits + t) < 2 ^ w := fun t ht => by
      rw [hmem_fr (edits + t) (by omega)
        (fun hf => (hft i hilt _ hf).2.2.2.2.2.1 ⟨by omega, by omega⟩)
        (fun hr => hE_disj_out (edits + t) (by omega) (by omega) ⟨by omega, by omega⟩)
        (fun hr => hE_disj_out (edits + t) (by omega) (by omega) ⟨by omega, by omega⟩)]
      exact hEw t ht
    have htbl5 : ∀ j < k, st5.mem (tbl + j) = brH j := fun j hj => by
      rw [hmem_fr (tbl + j) (by omega)
        (fun hf => (hft i hilt _ hf).2.2.2.1 ⟨by omega, by omega⟩)
        (fun hr => htbl_disj_out (tbl + j) (by omega) (by omega) ⟨by omega, by omega⟩)
        (fun hr => htbl_disj_out (tbl + j) (by omega) (by omega) ⟨by omega, by omega⟩)]
      exact htbl j hj
    have hdone5 : ∀ j < i + 1, BR.rep.rep (brH j) ⟨(info j).state, ord', vCap, eCap⟩ (xMid j) st5.mem := by
      intro j hj
      by_cases hji : j = i
      · subst hji; simp only [xMid, Function.update_self]; exact hrepBi'
      · simp only [xMid, Function.update_of_ne hji]
        exact (BR.rep_local (brH j) ⟨(info j).state, ord', vCap, eCap⟩ (xCur j) st.mem st5.mem fun a ha =>
          (hmem_fr a (hft j (by omega) a ha).1
            (fun hfi => hdisj j (by omega) i hilt hji a ha hfi)
            (fun hr => (hft j (by omega) a ha).2.2.1 ⟨by omega, by omega⟩)
            (fun hr => (hft j (by omega) a ha).2.2.1 ⟨by omega, by omega⟩)).symm).1
          (hdone j (by omega))
    have htodo5 : ∀ j, i + 1 ≤ j → j < k →
        BR.rep.rep (brH j) ⟨tr j, ord, vCap, eCap⟩ (xMid j) st5.mem ∧
        ∀ a, BR.rep.foot (brH j) (xMid j) a → a < hStart := by
      intro j hj1 hj2
      have hji : j ≠ i := by omega
      simp only [xMid, Function.update_of_ne hji]
      refine ⟨?_, (htodo j (by omega) hj2).2⟩
      exact (BR.rep_local (brH j) ⟨tr j, ord, vCap, eCap⟩ (xCur j) st.mem st5.mem fun a ha =>
        (hmem_fr a (hft j hj2 a ha).1
          (fun hfi => hdisj j hj2 i hilt hji a ha hfi)
          (fun hr => (hft j hj2 a ha).2.2.1 ⟨by omega, by omega⟩)
          (fun hr => (hft j hj2 a ha).2.2.1 ⟨by omega, by omega⟩)).symm).1
        (htodo j (by omega) hj2).1
    have hft5 : ∀ j < k, ∀ a, BR.rep.foot (brH j) (xMid j) a → a < st5.regs 14 ∧ ¬ CF.rep.foot cfH xcf a ∧
        ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k) ∧ ¬ (tbl ≤ a ∧ a < tbl + k) ∧
        ¬ (batch ≤ a ∧ a < batch + words) ∧ ¬ (edits ≤ a ∧ a < edits + editWords) ∧
        ¬ (fChgPtr ≤ a ∧ a < fChgEnd) := by
      intro j hj a ha
      have hr14_5 : st5.regs 14 = hNext := by simp [st5, st4]
      rw [hr14_5]
      by_cases hji : j = i
      · subst hji
        simp only [xMid, Function.update_self] at ha
        rcases hB_ft a ha with hold | hnew
        · have h := hft j hj a hold
          exact ⟨by omega, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
        · exact ⟨hnew.2, fun hcf_a => by have := hcfFoot a hcf_a; omega,
            by omega, by omega, by omega, by omega, by omega⟩
      · simp only [xMid, Function.update_of_ne hji] at ha
        have h := hft j hj a ha
        exact ⟨by omega, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
    have hdisj5 : ∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ → ∀ a,
        BR.rep.foot (brH j₁) (xMid j₁) a → ¬ BR.rep.foot (brH j₂) (xMid j₂) a := by
      intro j₁ h₁ j₂ h₂ hne a ha1 ha2
      by_cases h1i : j₁ = i
      · subst h1i
        have h2i : j₂ ≠ j₁ := Ne.symm hne
        simp only [xMid, Function.update_self, Function.update_of_ne h2i] at ha1 ha2
        rcases hB_ft a ha1 with hold | hnew
        · exact hdisj j₁ h₁ j₂ h₂ hne a hold ha2
        · have := (hft j₂ h₂ a ha2).1; omega
      · by_cases h2i : j₂ = i
        · subst h2i
          simp only [xMid, Function.update_self, Function.update_of_ne h1i] at ha1 ha2
          rcases hB_ft a ha2 with hold | hnew
          · exact hdisj j₁ h₁ j₂ h₂ hne a ha1 hold
          · have := (hft j₁ h₁ a ha1).1; omega
        · simp only [xMid, Function.update_of_ne h1i, Function.update_of_ne h2i] at ha1 ha2
          exact hdisj j₁ h₁ j₂ h₂ hne a ha1 ha2
    have hout5 : ∀ j < i + 1, BranchSlotDone (impl := impl) brReemb st5.mem outPtr k vCap eCap hStart (st5.regs 14) tr U ord ord' j := by
      intro j hj
      have hr14_5 : st5.regs 14 = hNext := by simp [st5, st4]
      rw [hr14_5]
      by_cases hji : j = i
      · subst hji
        have hslot0 : outPtr + 1 + 4 * j = slotP := rfl
        have hslot1 : outPtr + 2 + 4 * j = slotP + 1 := by omega
        have hslot2 : outPtr + 3 + 4 * j = slotP + 2 := by omega
        have hslot3 : outPtr + 4 + 4 * j = slotP + 3 := by omega
        have hrslot0 : outPtr + 1 + 4 * k + 2 * j = rSlotP := rfl
        have hrslot1 : outPtr + 2 + 4 * k + 2 * j = rSlotP + 1 := by omega
        unfold BranchSlotDone
        rw [hslot0, hslot1, hslot2, hslot3, hrslot0, hrslot1]
        exact ⟨hSBi', le_trans hlo huLo, huHi, hEdi', le_trans hlo heLo, heHi, hRLi', le_trans hlo hrLo, hrHi⟩
      · have hjlt : j < i := by omega
        refine branchSlotDone_frame (hout j hjlt) hB_lo ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (fun a ha1 ha2 => ?_)
        · exact hmem_fr _ (by omega) (fun hf => (hft i hilt _ hf).2.2.1 ⟨by omega, by omega⟩)
            (by omega) (by omega)
        · exact hmem_fr _ (by omega) (fun hf => (hft i hilt _ hf).2.2.1 ⟨by omega, by omega⟩)
            (by omega) (by omega)
        · exact hmem_fr _ (by omega) (fun hf => (hft i hilt _ hf).2.2.1 ⟨by omega, by omega⟩)
            (by omega) (by omega)
        · exact hmem_fr _ (by omega) (fun hf => (hft i hilt _ hf).2.2.1 ⟨by omega, by omega⟩)
            (by omega) (by omega)
        · exact hmem_fr _ (by omega) (fun hf => (hft i hilt _ hf).2.2.1 ⟨by omega, by omega⟩)
            (by omega) (by omega)
        · exact hmem_fr _ (by omega) (fun hf => (hft i hilt _ hf).2.2.1 ⟨by omega, by omega⟩)
            (by omega) (by omega)
        · exact hmem_fr a ha2 (fun hf => by have := (htodo i le_rfl hilt).2 a hf; omega)
            (by omega) (by omega)
    -- Invoke induction hypothesis on rem
    obtain ⟨st', cRest, xNew, hrunRest, hlo', hhi', hz', hkeep', hfr', hdone', hft', hdisj', hout', hcostRest⟩ :=
      ih (i + 1) st5 xMid (by omega)
        (by simp [st5, st4, st3, st2, st1, r2]) (by simp [st5, st4, st3, st2, st1, r3])
        (by simp [st5, st4, st3, st2, st1, r4]) (by simp [st5, st4, st3, st2, st1, r5])
        (by simp [st5, st4, st3, st2, st1, r8]) (by simp [st5, st4, st3, st2, st1, r10])
        (by simp [st5, st4, st3, st2, st1, r11]) (by simp [st5, st4, st3, st2, st1, r12])
        (by simp [st5, st4, st3, st2, st1, r13]) (by simp [st5])
        (by simp [st5, st4]; omega)
        (by simp [st5, st4]; rw [Nat.add_one_mul]; omega)
        (by simpa [st5, st4] using hzB) hcf5 hchg5 hspL5 hB5 hEd5 hBw5 hEw5 htbl5
        hdone5 htodo5 hft5 hdisj5 hout5
    have hfull : Runs w p ω (.loop (.bin .lt (.reg 15) (.reg 10)) (asmStepBranchStep bp.fStep)) st .normal st' _ :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st5, _, _, hlt1, Nat.one_ne_zero, hstep_run, hrunRest, rfl⟩))
    -- Relate potentials across step i and rest
    have hphi_i_new : BR.rep.phi (brH i) (xNew i) st'.mem = BR.rep.phi (brH i) xi' stB.mem := by
      have hxni : xNew i = xi' := (hkeep' i (by omega)).trans (by simp [xMid])
      rw [hxni]
      refine (BR.rep_local (brH i) ⟨(info i).state, ord', vCap, eCap⟩ xi' stB.mem st'.mem fun a ha => ?_).2.symm
      rcases hB_ft a ha with hold | hnew
      · have ha_lt : a < hNext := by have := (htodo i le_rfl hilt).2 a hold; omega
        exact (hfr' a (by simp [st5, st4]; exact ha_lt)
          (fun j hj1 hj2 hfj => by
            simp only [xMid, Function.update_of_ne (by omega : j ≠ i)] at hfj
            exact hdisj i hilt j hj2 (by omega) a hold hfj)
          (fun hr => (hft i hilt a hold).2.2.1 ⟨by omega, by omega⟩)
          (fun hr => (hft i hilt a hold).2.2.1 ⟨by omega, by omega⟩)).symm
      · exact (hfr' a (by simp [st5, st4]; exact hnew.2)
          (fun j hj1 hj2 hfj => by
            have := (htodo5 j hj1 hj2).2 a hfj; omega)
          (by omega) (by omega)).symm
    have hphi_tail_eq :
        (Finset.Ico (i + 1) k).sum (fun j => BR.rep.phi (brH j) (xMid j) st5.mem) =
        (Finset.Ico (i + 1) k).sum (fun j => BR.rep.phi (brH j) (xCur j) st.mem) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj1 := (Finset.mem_Ico.mp hj).1
      have hj2 := (Finset.mem_Ico.mp hj).2
      have hji : j ≠ i := by omega
      simp only [xMid, Function.update_of_ne hji]
      exact (BR.rep_local (brH j) ⟨tr j, ord, vCap, eCap⟩ (xCur j) st.mem st5.mem fun a ha =>
        (hmem_fr a (hft j hj2 a ha).1
          (fun hfi => hdisj j hj2 i hilt hji a ha hfi)
          (fun hr => (hft j hj2 a ha).2.2.1 ⟨by omega, by omega⟩)
          (fun hr => (hft j hj2 a ha).2.2.1 ⟨by omega, by omega⟩)).symm).2.symm
    have hNext_le : hNext ≤ st'.regs 14 := by
      simpa [st5, st4] using hlo'
    refine ⟨st', _, xNew, hfull, le_trans hB_lo hNext_le, hhi', hz',
      fun j hj => (hkeep' j (by omega)).trans (by simp [xMid, show j ≠ i by omega]),
      ?_, hdone', ?_, hdisj', hout', ?_⟩
    · intro a ha hnf hns1 hns2
      have hfr1 : st'.mem a = st5.mem a :=
        hfr' a (by simp [st5, st4]; omega)
          (fun j hj1 hj2 hfj => by
            simp only [xMid, Function.update_of_ne (by omega : j ≠ i)] at hfj
            exact hnf j (by omega) hj2 hfj)
          (by omega) (by omega)
      rw [hfr1]
      exact hmem_fr a ha (hnf i le_rfl hilt) (by omega) (by omega)
    · intro j hj a ha
      rcases hft' j hj a ha with hmid | hnew
      · by_cases hji : j = i
        · subst hji
          simp only [xMid, Function.update_self] at hmid
          rcases hB_ft a hmid with hold | hbi
          · exact Or.inl hold
          · exact Or.inr ⟨hbi.1, lt_of_lt_of_le hbi.2 hNext_le⟩
        · simp only [xMid, Function.update_of_ne hji] at hmid
          exact Or.inl hmid
      · simp only [st5, st4, Function.update_of_ne (by decide : (14 : ℕ) ≠ 15), Function.update_self] at hnew
        exact Or.inr ⟨by omega, hnew.2⟩
    · rw [sum_Ico_cons hilt, sum_Ico_cons hilt, sum_Ico_cons hilt, hphi_i_new]
      rw [hphi_tail_eq] at hcostRest
      change cB + BR.rep.phi (brH i) xi' stB.mem ≤
          S.mul capExp limbMul * (branchStepCharge (fun _ => canonicalSparsify impl) (tr i) U ord ord' +
            (words + editWords + 1) * bundleLogFactor M N) +
          BR.rep.phi (brH i) (xCur i) st.mem at hcostB
      simp only [argsSize_cons, argsSize_nil, Expr.size, Nat.mul_succ]
      omega

/-- **Execution of `asmStepBranchesLoop`**: steps all `k` branches `j = 0 .. k - 1`, writes
`BranchOutReembAt` payloads inside `[hStart, st'.regs 14)` and pointers at `outPtr + 1 .. outPtr + 6 * k`,
preserves pairwise disjointness and all memory below `hStart` outside branch footprints and the
output pointer slots, and meets the amortized cost bound. -/
theorem asmStepBranchesLoop_runs
    {S : AsmBranchSpec} {CFS : AsmCompFamilySpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs}
    (BR : AsmBranchAt S CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    {batch words edits editWords outPtr k M N vCap eCap cfH tbl fChgPtr fChgEnd hStart : ℕ}
    {tr : ℕ → BundleTreeState depth} {ord : ℕ → List End} {cfsOld cfsNew : CompFamilyAbs}
    {xcf : CF.rep.τ} {U : List Update} {ed : List OrdEdit} {brH : ℕ → ℕ} {xCur : ℕ → BR.rep.τ}
    (st : State) (ω : ℕ → Bool)
    (hfmt : fmt.limbBits = 4) (hk : 0 < k)
    (hMN : ∀ j < k, (tr j).m₀ = M ∧ (tr j).n₀ = N ∧ (tr j).cs.G = (tr 0).cs.G)
    (hdepth : 1 ≤ depth) (hdepth_lg : depth ≤ bundleLogFactor M N)
    (hdepth_ch : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hwBR : (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hcfsOld : ∀ j < k, cfsOld j = (tr j).cs)
    (hcfsNew : ∀ j < k, cfsNew j = compLSFBatch (tr j).cs U)
    (hUval : (tr 0).cs.G.BatchIsValid U) (hUcap : BatchWithinCaps vCap eCap U)
    (hOrdB : OrderedBatch (tr 0).cs.G U ord (applyOrdEdits ord ed))
    (hEdVal : OrdEditsValidFor vCap eCap ord ed)
    (hEdBlocks : OrdEditsForBatch (tr 0).cs.G U ed)
    (hB_le : batch + words ≤ hStart) (hE_le : edits + editWords ≤ hStart)
    (hout_le : outPtr + 1 + 6 * k ≤ hStart) (htbl_le : tbl + k ≤ hStart)
    (hfChg_le : fChgEnd ≤ hStart)
    (hcfFoot : ∀ a, CF.rep.foot cfH xcf a → a < hStart)
    (hcf_disj_out : ∀ a, outPtr ≤ a → a < outPtr + 1 + 6 * k → ¬ CF.rep.foot cfH xcf a)
    (hB_disj_out : ∀ a, batch ≤ a → a < batch + words → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (hE_disj_out : ∀ a, edits ≤ a → a < edits + editWords → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (htbl_disj_out : ∀ a, tbl ≤ a → a < tbl + k → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (hfChg_disj_out : ∀ a, fChgPtr ≤ a → a < fChgEnd → ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k))
    (hargsW : ∀ a ∈ [cfH, batch, words, edits, editWords, outPtr, k, tbl, fChgPtr], a < 2 ^ w)
    (hbrW : ∀ j < k, brH j < 2 ^ w)
    (hsp : hStart + k * (S.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords) < 2 ^ w)
    {n : ℕ}
    (hThr : ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N)
    (hUpdPre : ∀ j < k, BranchUpdatesBelow impl (tr j) n)
    (hUpdPost : ∀ j < k, BranchUpdatesBelow impl
      (stepBundleTree (fun _ => canonicalSparsify impl) (tr j) U ord (applyOrdEdits ord ed)).state
      (n + U.length))
    (hModPre : ∀ j < k, AsmBrModelFacts impl vCap eCap (tr j) ord)
    (hModPost : ∀ j < k, AsmBrModelFacts impl vCap eCap
      (stepBundleTree (fun _ => canonicalSparsify impl) (tr j) U ord (applyOrdEdits ord ed)).state
      (applyOrdEdits ord ed))
    (r2 : st.regs 2 = batch) (r3 : st.regs 3 = words)
    (r4 : st.regs 4 = edits) (r5 : st.regs 5 = editWords) (r8 : st.regs 8 = outPtr)
    (r10 : st.regs 10 = k) (r11 : st.regs 11 = cfH) (r12 : st.regs 12 = tbl)
    (r13 : st.regs 13 = fChgPtr) (r14 : st.regs 14 = hStart)
    (hz : ZeroFrom st.mem hStart) (hcf : CF.rep.rep cfH cfsNew xcf st.mem)
    (hchg : CompFamilyChgAt w k st.mem fChgPtr fChgEnd cfsOld U)
    (hspL : CompSplitListAt w k st.mem (fChgPtr + k) fChgEnd cfsOld U)
    (hB : SmallBatchAt st.mem batch (tr 0).cs.G U words)
    (hEd : OrdEditsAt st.mem edits ed editWords)
    (hBw : ∀ t < words, st.mem (batch + t) < 2 ^ w)
    (hEw : ∀ t < editWords, st.mem (edits + t) < 2 ^ w)
    (htbl : ∀ j < k, st.mem (tbl + j) = brH j)
    (hbrRep : ∀ j < k, BR.rep.rep (brH j) ⟨tr j, ord, vCap, eCap⟩ (xCur j) st.mem)
    (hbrFt : ∀ j < k, ∀ a, BR.rep.foot (brH j) (xCur j) a → a < hStart ∧ ¬ CF.rep.foot cfH xcf a ∧
      ¬ (outPtr ≤ a ∧ a < outPtr + 1 + 6 * k) ∧ ¬ (tbl ≤ a ∧ a < tbl + k) ∧
      ¬ (batch ≤ a ∧ a < batch + words) ∧ ¬ (edits ≤ a ∧ a < edits + editWords) ∧
      ¬ (fChgPtr ≤ a ∧ a < fChgEnd))
    (hdisj : ∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ → ∀ a,
      BR.rep.foot (brH j₁) (xCur j₁) a → ¬ BR.rep.foot (brH j₂) (xCur j₂) a) :
    let stepSp := (S.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords)
    let ord' := applyOrdEdits ord ed
    let info := fun j => stepBundleTree (fun _ => canonicalSparsify impl) (tr j) U ord ord'
    ∃ (st' : State) (c : ℕ) (xNew : ℕ → BR.rep.τ),
      Runs w p ω (asmStepBranchesLoop bp.fStep) st .normal st' c ∧
      hStart ≤ st'.regs 14 ∧ st'.regs 14 ≤ hStart + k * stepSp ∧
      ZeroFrom st'.mem (st'.regs 14) ∧
      (∀ a < hStart, (∀ j < k, ¬ BR.rep.foot (brH j) (xCur j) a) →
        ¬ (outPtr + 1 ≤ a ∧ a < outPtr + 1 + 6 * k) → st'.mem a = st.mem a) ∧
      (∀ j < k, BR.rep.rep (brH j) ⟨(info j).state, ord', vCap, eCap⟩ (xNew j) st'.mem) ∧
      (∀ j < k, ∀ a, BR.rep.foot (brH j) (xNew j) a →
        BR.rep.foot (brH j) (xCur j) a ∨ (hStart ≤ a ∧ a < st'.regs 14)) ∧
      (∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ → ∀ a,
        BR.rep.foot (brH j₁) (xNew j₁) a → ¬ BR.rep.foot (brH j₂) (xNew j₂) a) ∧
      (∀ j < k,
        SmallBatchAt st'.mem (st'.mem (outPtr + 1 + 4 * j)) (tr j).S_cur (info j).U_S (st'.mem (outPtr + 2 + 4 * j)) ∧
        (∃ outEd, OrdEditsAt st'.mem (st'.mem (outPtr + 3 + 4 * j)) outEd (st'.mem (outPtr + 4 + 4 * j)) ∧
          applyOrdEdits ((tr j).outOrder ord) outEd = (info j).state.outOrder ord' ∧
          OrdEditsValidFor vCap eCap ((tr j).outOrder ord) outEd ∧
          OrdEditsForBatch (tr j).S_cur (info j).U_S outEd) ∧
        readList st'.mem (st'.mem (outPtr + 1 + 4 * k + 2 * j)) (st'.mem (outPtr + 2 + 4 * k + 2 * j)) =
          brReemb (tr j) U ord ord') ∧
      c + (Finset.range k).sum (fun j => BR.rep.phi (brH j) (xNew j) st'.mem) ≤
        (Finset.range k).sum (fun j => S.mul capExp limbMul *
          (branchStepCharge (fun _ => canonicalSparsify impl) (tr j) U ord ord' +
            (words + editWords + 1) * bundleLogFactor M N)) +
        70 * k + 20 +
        (Finset.range k).sum (fun j => BR.rep.phi (brH j) (xCur j) st.mem) := by
  intro stepSp ord' info
  have h15 : Runs w p ω (.assign 15 (.const 0)) st .normal
      { st with regs := Function.update st.regs 15 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st0 : State := { st with regs := Function.update st.regs 15 0 }
  obtain ⟨st', cL, xNew, hrunL, hlo, hhi, hz', _, hfr, hdone, hft', hdisj', hout, hcost⟩ :=
    asmStepBranchesLoop_go BR hfmt hk hMN hdepth hdepth_lg hdepth_ch hcap hwBR hw4 hcfsOld hcfsNew hUval hUcap hOrdB hEdVal hEdBlocks
      hB_le hE_le hout_le htbl_le hfChg_le hcfFoot hcf_disj_out hB_disj_out
      hE_disj_out htbl_disj_out hfChg_disj_out hargsW hbrW hsp hThr hUpdPre hUpdPost hModPre hModPost ω
      k 0 st0 xCur (Nat.zero_add k)
      (by simp [st0, r2]) (by simp [st0, r3]) (by simp [st0, r4]) (by simp [st0, r5])
      (by simp [st0, r8]) (by simp [st0, r10]) (by simp [st0, r11]) (by simp [st0, r12])
      (by simp [st0, r13]) (by simp [st0])
      (by simp [st0, r14]) (by simp [st0, r14]) (by simpa [st0, r14] using hz)
      hcf hchg hspL hB hEd hBw hEw htbl
      (fun _ hj => absurd hj (Nat.not_lt_zero _))
      (fun j _ hj => ⟨hbrRep j hj, fun a ha => (hbrFt j hj a ha).1⟩)
      (by simpa [st0, r14] using hbrFt)
      hdisj
      (fun _ hj => absurd hj (Nat.not_lt_zero _))
  rw [Nat.Ico_zero_eq_range] at hcost
  change cL + (Finset.range k).sum (fun j => BR.rep.phi (brH j) (xNew j) st'.mem) ≤
      (Finset.range k).sum (fun j => S.mul capExp limbMul *
        (branchStepCharge (fun _ => canonicalSparsify impl) (tr j) U ord ord' +
          (words + editWords + 1) * bundleLogFactor M N)) +
      70 * k + 10 + (Finset.range k).sum (fun j => BR.rep.phi (brH j) (xCur j) st.mem) at hcost
  refine ⟨st', _, xNew, runs_seq_iff.mpr (Or.inr ⟨st0, _, _, h15, hrunL, rfl⟩),
    by simpa [st0, r14] using hlo, hhi, hz', ?_, hdone, by simpa [st0, r14] using hft', hdisj', ?_,
    by simp [Expr.size]; omega⟩
  · intro a ha hnf hno
    exact hfr a (by simpa [st0, r14] using ha) (fun j _ hj => hnf j hj) (by omega) (by omega)
  · intro j hj
    have hd := hout j hj
    exact ⟨hd.1, hd.2.2.2.1, hd.2.2.2.2.2.2.1⟩

end MinCostFlow.SparseCore.Program
