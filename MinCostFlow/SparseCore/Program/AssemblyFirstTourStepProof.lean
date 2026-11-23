module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepLoop
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCode

import Mathlib.Tactic

/-!
# End-to-end verification of `asmFirstTourBlockStepStmt` (`AssemblyFirstTourStepProof`)

Assembles the prologue (`copyWords` + initial `asmFirstTourConsumeRelStmt`), the main inductive
update loop (`tourBlock_loop_runs`), the trailing rotation tail (`tourBlock_tail_rot_runs`), and
the epilogue (`mem[h] := splitPtr; ret hEnd`) of `asmFirstTourBlockStepStmt` into:

1. `asmFirstTourBlockStep_runs`: complete correctness, `OutMarksOf`, `OutSplitListsAt`, mark
   potential bound, quadratic `limbMul`-free space bound (`tourBlockStepSpace`), frame, footprint,
   and `O((Σ|Y| + batchEnc + words + editWords + 1) * log eCap)` amortized cost on `tourAsmRep`.
2. `asmFirstTourBlockStep_Ys_sum_le`: deduces the `(1 + 4 * capExp) * batchEnc * (log(M₀+N₀+2)+1)`
   bound on `(Ys.map List.length).sum` directly from the mark-potential bound of
   `asmFirstTourBlockStep_runs`.
3. `scProg_asmFirstTourBlockStep_runs`: lifts `asmFirstTourBlockStep_runs` directly into
   `scProg impl cf asmFirstStepSubCode firstInit` at `L.bFirstS + asmFirstStepSubCode.offMain`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. Space and cost constants -/

@[expose] public section

/-- Parametric cost multiplier of `asmFirstTourBlockStepStmt`. -/
def tourBlockStepMulFn (mRel mLoop mCase : ℕ) : ℕ :=
  mRel + mLoop + mCase + 100

end

public section

/-- Concrete cost multiplier of `asmFirstTourBlockStepStmt`. Kept non-exposed so downstream proofs
never unfold `tourMul` during unification. -/
noncomputable def tourBlockStepMul : ℕ :=
  tourBlockStepMulFn tourConsumeRelMul tourBlockLoopMul tourBlockCaseMul

theorem tourBlockStepMul_eq :
    tourBlockStepMul = tourBlockStepMulFn tourConsumeRelMul tourBlockLoopMul tourBlockCaseMul := by
  unfold tourBlockStepMul; rfl

end

/-! ## 2. Pure helpers -/

private theorem ordEditsValidFor_within {vCap eCap : ℕ} :
    ∀ (eds : List OrdEdit) (ord : ℕ → List End),
      OrdEditsValidFor vCap eCap ord eds → OrdEditsWithin vCap eCap eds
  | [], _, _ => fun _ h => by cases h
  | d :: ds, ord, h => by
    obtain ⟨h1, h2⟩ := ordEditsValidFor_cons h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact h1 x List.mem_cons_self
    · exact ordEditsValidFor_within ds (applyOrdEdit ord d) h2 x hmem

private theorem outCoreOrder_eq_coreTour {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {depth : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} (ρ : Rotation tr.cs.G)
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hρ : ρ.order = ord) :
    outCoreOrder tr ord = coreTour ord tr.cs.RF := by
  classical
  have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ tr.cs) (ρ' : Rotation tr.cs.G), ρ'.order = ord :=
    ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  have hok : TourCordOK ord tr.cs.RF (outCoreOrder tr ord) := by
    refine ⟨tr.cs, ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.choose,
      hex.choose_spec.choose_spec.choose_spec.choose,
      hex.choose_spec.choose_spec.choose_spec.choose_spec, ?_⟩, rfl⟩
    simp only [outCoreOrder, hex, ↓reduceDIte]
  funext r
  exact tourCordOK_eq_coreTour hok r

private theorem stepBundleTree_cs_eq {depth : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree sp tr U ord ord').state.cs = compLSFBatch tr.cs U := rfl

private theorem stepBundleTree_U_core_eq {depth : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree sp tr U ord ord').U_core = canonCoreBatch tr.cs U := rfl

/-! ## 3. Main verification of `asmFirstTourBlockStepStmt` -/

public section

set_option maxHeartbeats 600000 in
/-- **Complete verification of `asmFirstTourBlockStepStmt`** on `tourAsmRep`:
applies `OrdEditsForBatch tr.cs.G U ed` block by block alongside `batch` and `spPtr`, interleaved
with forest cuts and P7's `outSmallSide`, followed by the trailing `rotateTo` block `editRotBlock`,
writing `splitPtr` at `h` and returning `hEnd`. -/
theorem asmFirstTourBlockStep_runs {w vCap eCap depth bSelf bTour bOut bCopy
      tourH batch words edits editWords spPtr h pos : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpC : p.HasAt bCopy [copyWords])
    (hpSelf : p.HasAt bSelf (asmFirstTourBlockProcs bSelf bTour bOut bCopy))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit}
    {mk : Finset End} {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hready : OutStepReady sp tr U ord (applyOrdEdits ord ed))
    (hRlt : ∀ r ∈ (compLSFBatch tr.cs U).RF.R, r < vCap)
    (hOFB : OrdEditsForBatch tr.cs.G U ed)
    (hOVF : OrdEditsValidFor vCap eCap ord ed)
    (hMarks : OutMarksOf ⟨coreTour ord tr.cs.RF, mk⟩ (outCoreOrder tr ord) tr.S_cur.E)
    (hRep : (tourAsmRep vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx mem)
    (hFoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < h)
    (hZero : ZeroFrom mem h)
    (hBatch : BatchAt mem batch tr.cs.G U words)
    (hEdits : OrdEditsAt mem edits ed editWords)
    (hSpAt : SplitEntriesAt mem spPtr (canonSplitList tr.cs U))
    (hBatch_le : batch + words ≤ h) (hEdits_le : edits + editWords ≤ h)
    (hSp_le : spPtr + 1 + 4 * (canonSplitList tr.cs U).length ≤ h)
    (hBF : ∀ a, batch ≤ a → a < batch + words → ¬ (tourAsmRep vCap eCap).foot tourH tx a)
    (hSF : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * (canonSplitList tr.cs U).length →
      ¬ (tourAsmRep vCap eCap).foot tourH tx a)
    (hRoom : h + tourBlockStepSpace vCap eCap words editWords < 2 ^ w) :
    let ord' := applyOrdEdits ord ed
    let info := stepBundleTree sp tr U ord ord'
    let keep := outKeep sp tr U ord ord'
    let G₁ := tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete)
    ∃ body, p.procs[bSelf + 2]? = some body ∧
      ∃ hEnd st' cost tx' splitPtr mk' M Ys,
        Runs w p ω body
          (startState [tourH, batch, words, edits, editWords, spPtr, h] mem pos)
          (.returned hEnd) st' cost ∧
        (tourAsmRep vCap eCap).rep tourH ⟨ord', info.state.cs.RF, mk'⟩ tx' st'.mem ∧
        keep ⊆ M ∧ M ⊆ tr.S_cur.E ∧
        OutMarksOf ⟨coreTour ord' info.state.cs.RF, mk'⟩ (outCoreOrder info.state ord') M ∧
        OutSplitListsAt st'.mem hEnd (fun a => a < h + 1 ∨ (tourAsmRep vCap eCap).foot tourH tx' a)
          keep tr.S_cur.E splitPtr G₁ (restrictSplits keep info.U_core) Ys ∧
        (Ys.map List.length).sum ≤
          G₁.batchEnc (restrictSplits keep info.U_core) +
            markPot keep tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf) ∧
        st'.mem h = splitPtr ∧
        h + 1 ≤ hEnd ∧ hEnd ≤ h + tourBlockStepSpace vCap eCap words editWords ∧
        ZeroFrom st'.mem hEnd ∧
        (∀ a < h, ¬ (tourAsmRep vCap eCap).foot tourH tx a → st'.mem a = mem a) ∧
        (∀ a, (tourAsmRep vCap eCap).foot tourH tx' a →
          (tourAsmRep vCap eCap).foot tourH tx a ∨ (h + 1 ≤ a ∧ a < hEnd)) ∧
        cost + (tourAsmRep vCap eCap).phi tourH tx' st'.mem ≤
          tourBlockStepMul *
              ((Ys.map List.length).sum + tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
            ordStoreLog eCap +
          (tourAsmRep vCap eCap).phi tourH tx mem := by
  intro ord' info keep G₁
  obtain ⟨C_lsst, ℓ₀, hI, hBU, hOB, hSval, _, hSub, _⟩ := hready
  obtain ⟨ρ, σ, hρ, hσ, hrot0⟩ := hOB
  have hpRel : p.procs[bSelf + 0]? = some (asmFirstTourConsumeRelStmt (tourOp bTour 1) (outIdxSmallSide bOut)) := by
    simpa [asmFirstTourBlockProcs] using hpSelf 0 (by simp [asmFirstTourBlockProcs])
  have hpMove : p.procs[bSelf + 1]? = some (asmFirstTourApplyMoveStmt (bTour + 75) (tourOp bTour 0)) := by
    simpa [asmFirstTourBlockProcs] using hpSelf 1 (by simp [asmFirstTourBlockProcs])
  have hpMain : p.procs[bSelf + 2]? =
      some (asmFirstTourBlockStepStmt bCopy (bSelf + 0) (bSelf + 1) (tourOp bTour 0)
        (tourOp bTour 1) (tourOp bTour 3) (outIdxSmallSide bOut)) := by
    simpa [asmFirstTourBlockProcs] using hpSelf 2 (by simp [asmFirstTourBlockProcs])
  -- Initial tour state `s₀` and invariants
  set s₀ : TourAbs := ⟨ord, tr.cs.RF, mk⟩
  set L := canonSplitList tr.cs U
  have hRep0 : TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s₀ tx mem := hRep
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hL_le_vCap : L.length ≤ vCap :=
    asmFirstCanonSplitList_length_le_vCap hI hBU ⟨ρ, σ, hρ, hσ, hrot0⟩ hRlt
  have hL_le_bEnc : L.length ≤ tr.S_cur.batchEnc info.U_S :=
    asmFirstCanonSplitList_length_le_batchEnc sp tr U ord ord'
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hRep0 hFoot (by unfold tourBlockStepSpace at hRoom; omega)).2
  have hordH : ordHandleOf tourH vCap eCap ≤ h := hRep0.fixed_le_heap hFoot
  have hCore0 : outCoreOrder tr ord = coreTour ord tr.cs.RF := outCoreOrder_eq_coreTour ρ hI hρ
  have hM0 : TourMarksAt s₀ tr.S_cur.E := (tourMarksAt_iff_outMarksOf hRep0.valid).mpr (by rwa [hCore0] at hMarks)
  have hOrdG0 : ∀ v x, x ∈ s₀.ord v ↔ x.1 ∈ tr.cs.G.E ∧ tr.cs.G.src x = v := fun v x => by
    change x ∈ ord v ↔ _; rw [← hρ]; exact ρ.mem_order v x
  have hSubE : tr.S_cur.E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E := hSub.2.1
  have hM0_G : tr.S_cur.E ⊆ tr.cs.G.E := fun e he => (Finset.mem_sdiff.mp (hSubE he)).1
  have hM0_disj : Disjoint tr.S_cur.E tr.cs.RF.F.E :=
    Finset.disjoint_left.mpr fun e he => (Finset.mem_sdiff.mp (hSubE he)).2
  have hkM0 : keep ⊆ tr.S_cur.E := (outKeep_subset sp tr U ord ord').1
  have hKdisj : Disjoint keep (batchDeletes U) :=
    Finset.disjoint_left.mpr fun e he =>
      (Finset.mem_sdiff.mp (outKeep_subset_sdiff_batchDeletes sp tr U ord ord' he)).2
  have hK0 : TourKeepMatch keep s₀ G₁ := by
    refine ⟨outStep_G₁_E sp tr U ord ord', fun x hx => ?_⟩
    have hxS : x.1 ∈ tr.S_cur.E := hkM0 hx
    have hxC : x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E := hSubE hxS
    have hxG : x.1 ∈ tr.cs.G.E := (Finset.mem_sdiff.mp hxC).1
    have hxOpen : x.1 ∉ tr.cs.RF.F.E := (Finset.mem_sdiff.mp hxC).2
    have hmem : x ∈ s₀.ord (tr.cs.G.src x) := (hOrdG0 _ _).mpr ⟨hxG, rfl⟩
    refine ⟨⟨tr.cs.G.src x, hmem⟩, hxOpen, ?_⟩
    rw [hRep0.valid.compat.ordSrc_eq hmem]
    have hd : ∀ (l : List ℕ) (G : MGraph),
        (G.applyBatch (l.map Update.delete)).tail = G.tail ∧
          (G.applyBatch (l.map Update.delete)).head = G.head := by
      intro l; induction l with
      | nil => intro _; exact ⟨rfl, rfl⟩
      | cons e ls ih => intro G; exact ih (G.applyUpdate (.delete e))
    have hd1 := hd (outDelList sp tr U ord ord') tr.S_cur
    have hSub_th := hSub.2.2 x.1 hxS
    obtain ⟨f, b⟩ := x; cases b
    · change tr.cs.RF.root (tr.cs.G.head f) = G₁.head f
      rw [hd1.2, hSub_th.2]; rfl
    · change tr.cs.RF.root (tr.cs.G.tail f) = G₁.tail f
      rw [hd1.1, hSub_th.1]; rfl
  -- Decompose `U` into leading quiet prefix `Uq₀` and wall tail `Uwall₀`
  set Uq₀ := (splitQuietPrefix tr.cs U).1
  set Uwall₀ := (splitQuietPrefix tr.cs U).2
  set cs_wall₀ := compLSFBatch tr.cs Uq₀
  set relL₀ := canonSplitList tr.cs Uq₀
  set splitsRest := canonSplitList cs_wall₀ Uwall₀
  have hBU_q : tr.cs.G.BatchIsValid Uq₀ := by
    have h := hBU; rw [← splitQuietPrefix_append tr.cs U] at h; exact (batchIsValid_append.mp h).1
  have hKdisj_q : Disjoint keep (batchDeletes Uq₀) :=
    Disjoint.mono_right (fun e he => by
      obtain ⟨u, hu, hd⟩ := (mem_batchDeletes_iff _ _).mp he
      exact (mem_batchDeletes_iff _ _).mpr ⟨u, by rw [← splitQuietPrefix_append tr.cs U]; exact List.mem_append_left _ hu, hd⟩) hKdisj
  have hRlt_q : ∀ r ∈ cs_wall₀.RF.R, r < vCap := fun r hr => by
    have hBU_w : cs_wall₀.G.BatchIsValid Uwall₀ := by
      have h := hBU; rw [← splitQuietPrefix_append tr.cs U, batchIsValid_append] at h
      simpa [cs_wall₀, compLSFBatch_G tr.cs Uq₀] using h.2
    have hI_q : CompLSFInv C_lsst ℓ₀ cs_wall₀ := compLSFBatch_inv hI hBU_q
    have hdec := (compLSFBatch_decremental hI_q hBU_w).2 hr
    have heq : compLSFBatch cs_wall₀ Uwall₀ = compLSFBatch tr.cs U := by
      rw [← compLSFBatch_append, splitQuietPrefix_append]
    exact hRlt r (heq ▸ hdec)
  have hL_decomp : L = relL₀ ++ splitsRest := by
    dsimp only [L, relL₀, splitsRest, cs_wall₀, Uq₀, Uwall₀]
    conv_lhs => rw [← splitQuietPrefix_append tr.cs U, asmFirstCanonSplitList_append]
  have hPs_decomp : restrictSplits keep info.U_core =
      restrictSplits keep (canonCoreBatch tr.cs Uq₀) ++
        restrictSplits keep (canonCoreBatch cs_wall₀ Uwall₀) := by
    rw [stepBundleTree_U_core_eq]
    conv_lhs => rw [← splitQuietPrefix_append tr.cs U, canonCoreBatch_append, restrictSplits_append]
  obtain ⟨s₁, S₁, hChain₀, hOrd₁, hMk₁, hFeq₁, hReq₁, hv₁, hM₁, hK₁⟩ :=
    tourRelChain_of_quietPrefix Uq₀ tr.cs s₀ G₁ hI hBU_q (splitQuietPrefix_all_quiet tr.cs U)
      hRlt_q hRep0.valid (graphEq_refl _) rfl hM0 hM0_disj hK0 hKdisj_q
      (fun f hf => by
        have hfG := hM0_G (hkM0 hf)
        exact ⟨hfG, hRep0.valid.compat.ordSrc_eq ((hOrdG0 _ _).mpr ⟨hfG, rfl⟩),
          hRep0.valid.compat.ordSrc_eq ((hOrdG0 _ _).mpr ⟨hfG, rfl⟩)⟩)
  have hMdisj₁ : Disjoint tr.S_cur.E cs_wall₀.RF.F.E :=
    Disjoint.mono_right (compLSFBatch_decremental hI hBU_q).1 hM0_disj
  -- Decode `BatchAt` and `OrdEditsAt` lengths
  have hU_lt : U.length < 2 ^ w := by
    have := hBatch.2.1
    have h1 : U.length ≤ words := by
      have : ∀ {m a G B t}, BatchBodyAt m a G B t → B.length ≤ t := by
        intro m a G B; induction B generalizing a G with
        | nil => intro _ _; exact Nat.zero_le _
        | cons u Bs ih =>
          intro t ⟨len, hle, hu, hrest⟩
          have hpos : 1 ≤ len := by
            cases u with
            | insert _ _ _ => obtain ⟨rfl, _⟩ := hu; omega
            | delete _ => obtain ⟨rfl, _⟩ := hu; omega
            | split _ _ _ _ => rcases hu with ⟨_, _, _, _, _, _, hlen, _⟩ | ⟨_, _, _, _, _, _, hlen, _⟩ <;> omega
          have := ih hrest; simp; omega
      have := this hBatch.2.2; omega
    unfold tourBlockStepSpace at hRoom; omega
  have hed_len_eq : mem edits = ed.length := by
    have h1 : (decodeOrdEdits mem (mem edits) (edits + 1)).1 = ed := hEdits.1
    have h2 := (decodeOrdEdits_length mem (mem edits) (edits + 1)).1
    rw [h1] at h2; exact h2.symm
  have hed_lt : ed.length < 2 ^ w := by
    have h1 : ed.length ≤ (decodeOrdEdits mem (mem edits) (edits + 1)).2.sum := by
      have : ∀ (n a : ℕ), n ≤ (decodeOrdEdits mem n a).2.sum := by
        intro n; induction n with
        | zero => intro _; exact Nat.zero_le _
        | succ k ih =>
          intro a; simp only [decodeOrdEdits, List.sum_cons]
          have hpos : 1 ≤ (decodeOrdEdit mem a).2 := by
            unfold decodeOrdEdit; split_ifs <;> omega
          have := ih (a + (decodeOrdEdit mem a).2); omega
      rw [← hed_len_eq]; exact this _ _
    have := hEdits.2.1; unfold tourBlockStepSpace at hRoom; omega
  -- Prologue: `r7 := h + 1`, `r8 := h + 4`, `copyWords [edits, edCopy, editWords]`, `r9 := edCopy + editWords`, `r10 := L.length`
  set sStart := startState [tourH, batch, words, edits, editWords, spPtr, h] mem pos
  set statePtr := h + 1
  set edCopy := h + 4
  set hCur₀ := edCopy + editWords
  set r7 := Function.update sStart.regs 7 statePtr
  set r8 := Function.update r7 8 edCopy
  have ha7 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.const 1))) sStart .normal ⟨mem, r7, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨statePtr, Expr.eval_add (Expr.eval_reg_of_eq (by simp [sStart, startState]))
      (Expr.eval_const (by omega)) (by unfold tourBlockStepSpace at hRoom; omega), rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 6) (.const 4))) ⟨mem, r7, pos⟩ .normal ⟨mem, r8, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨edCopy, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7, sStart, startState]))
      (Expr.eval_const (by omega)) (by unfold tourBlockStepSpace at hRoom; omega), rfl, rfl, rfl⟩
  obtain ⟨bdC, hbdC, oC, stC, cC, hrunC, hpostC, hcostC⟩ :=
    copyWords_meetsContract (w := w) hpC [edits, edCopy, editWords] mem pos ω
      (fun a ha => by simp at ha; rcases ha with rfl | rfl | rfl <;> (unfold tourBlockStepSpace at hRoom; omega))
      ⟨edits, edCopy, editWords, rfl, by omega, by unfold tourBlockStepSpace at hRoom; omega,
       by unfold tourBlockStepSpace at hRoom; omega, Or.inr (by omega)⟩
  obtain ⟨_, _, _, heqC, hoC0, hcpC, hfrC⟩ := hpostC
  injection heqC with h1C h2C; injection h2C with h2C h3C; injection h3C with h3C _
  subst h1C h2C h3C
  set r15C := Function.update r8 15 oC.value
  have hcallC : Runs w p ω (.call 15 bCopy [.reg 3, .reg 8, .reg 4]) ⟨mem, r8, pos⟩ .normal
      ⟨stC.mem, r15C, stC.pos⟩ (argsSize [.reg 3, .reg 8, .reg 4] + cC + 1) :=
    runs_call_iff.mpr ⟨_, bdC, oC, stC, cC,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r8, r7, sStart, startState])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r8])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r8, r7, sStart, startState])) <| evalArgs_nil _ _,
      hbdC, hrunC, rfl, rfl, rfl⟩
  set r9 := Function.update r15C 9 hCur₀
  set r10 := Function.update r9 10 L.length
  have ha9 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 4))) ⟨stC.mem, r15C, stC.pos⟩ .normal
      ⟨stC.mem, r9, stC.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨hCur₀, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15C, r8]))
      (Expr.eval_reg_of_eq (by simp [r15C, r8, r7, sStart, startState]))
      (by unfold tourBlockStepSpace at hRoom; omega), rfl, rfl, rfl⟩
  have hsp_stC : SplitEntriesAt stC.mem spPtr L :=
    asmFirstSplitEntriesAt_congr hSpAt fun x hx1 hx2 => hfrC x (Or.inl (by omega))
  have ha10 : Runs w p ω (.assign 10 (.load (.reg 5))) ⟨stC.mem, r9, stC.pos⟩ .normal
      ⟨stC.mem, r10, stC.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨L.length, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (by simp [r9, r15C, r8, r7, sStart, startState])) hsp_stC.1, rfl, rfl, rfl⟩
  -- Initial `fConsumeRel` for leading quiet prefix `Uq₀`
  have hlocC := tourAsmRep_local vCap eCap tourH (tourToAsmTour s₀) tx mem stC.mem
    fun a ha => (hfrC a (Or.inl (lt_trans (hFoot a ha) (by omega)))).symm
  have hstC_zero : ZeroFrom stC.mem hCur₀ := fun a ha =>
    (hfrC a (Or.inr (by omega))).trans (hZero a (by omega))
  have hstC_st : stC.mem statePtr = 0 ∧ stC.mem (statePtr + 1) = 0 ∧ stC.mem (statePtr + 2) = 0 :=
    ⟨(hfrC statePtr (Or.inl (by omega))).trans (hZero statePtr (by omega)),
     (hfrC (statePtr + 1) (Or.inl (by omega))).trans (hZero (statePtr + 1) (by omega)),
     (hfrC (statePtr + 2) (Or.inl (by omega))).trans (hZero (statePtr + 2) (by omega))⟩
  have hstF0 : ∀ j < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx (statePtr + j) := fun j hj hf =>
    absurd (hFoot _ hf) (by omega)
  have hroomRel : hCur₀ + relL₀.length * tourSplitStepSpace eCap + 1 < 2 ^ w := by
    have hle : relL₀.length ≤ vCap := by rw [hL_decomp, List.length_append] at hL_le_vCap; omega
    have hmul : relL₀.length * tourSplitStepSpace eCap ≤ vCap * tourSplitStepSpace eCap :=
      Nat.mul_le_mul_right _ hle
    unfold tourBlockStepSpace at hRoom; omega
  obtain ⟨hCur₁, stRel, cRel, tx₁, splitPtr₁, last₁, Ys₀, hrunRel, hrep₁, hM₁', hK₁',
    hStRel0, hStRel1, hStRel2, hLast₁, hPre₁, hPot₁, hhLo₁, hhHi₁, hZero₁, hFr₁, hFt₁, hCost₁⟩ :=
    asmFirstTourConsumeRel_runs (p := p) (pos := stC.pos) (ω := ω) hpT hpO hw (hlocC.1 hRep)
      (fun a ha => lt_trans (hFoot a ha) (by omega)) hstC_zero hsp_stC (by omega) hSF hstC_st
      (by omega) hstF0 (Or.inr (by omega)) (Or.inl rfl) (Or.inl rfl)
      (Nat.zero_le _) (by simpa using hL_decomp) (splitQuietPrefix_snd_stop tr.cs U)
      hChain₀ hM0 hkM0 (Finset.Subset.rfl) hK0
      (outSplitPrefixAt_nil stC.mem hCur₀ _ keep tr.S_cur.E G₁) hroomRel
  set r9Rel := Function.update r10 9 hCur₁
  have hcallRel : Runs w p ω (.call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
      ⟨stC.mem, r10, stC.pos⟩ .normal ⟨stRel.mem, r9Rel, stRel.pos⟩
      (argsSize [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9] + cRel + 1) :=
    runs_call_iff.mpr ⟨_, _, .returned hCur₁, stRel, cRel,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r10, r9, r15C, r8, r7, sStart, startState])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r10, r9, r15C, r8, r7, sStart, startState])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r10])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r10, r9, r15C, r8, r7])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r10, r9])) <| evalArgs_nil _ _,
      hpRel, hrunRel, rfl, rfl, rfl⟩
  -- Initialize loop registers `r11..r15`
  have hRel_eq_C : ∀ a < hCur₀, ¬ (tourAsmRep vCap eCap).foot tourH tx a →
      (a < statePtr ∨ statePtr + 3 ≤ a) → stRel.mem a = stC.mem a :=
    fun a ha hnf hst => hFr₁ a ha hnf hst (Or.inl rfl)
  have hRel_eq_mem : ∀ a < h, ¬ (tourAsmRep vCap eCap).foot tourH tx a → stRel.mem a = mem a :=
    fun a ha hnf => (hRel_eq_C a (by omega) hnf (Or.inl (by omega))).trans (hfrC a (Or.inl (by omega)))
  set r11 := Function.update r9Rel 11 U.length
  set r12 := Function.update r11 12 (batch + 1)
  set r13 := Function.update r12 13 (edCopy + 1)
  set r14 := Function.update r13 14 0
  set r15 := Function.update r14 15 0
  have ha11 : Runs w p ω (.assign 11 (.load (.reg 1))) ⟨stRel.mem, r9Rel, stRel.pos⟩ .normal
      ⟨stRel.mem, r11, stRel.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨U.length, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (by simp [r9Rel, r10, r9, r15C, r8, r7, sStart, startState]))
      ((hRel_eq_mem batch (by have := hBatch.1; omega) (hBF batch (le_refl _) (by have := hBatch.1; omega))).trans hBatch.2.1),
      rfl, rfl, rfl⟩
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 1) (.const 1))) ⟨stRel.mem, r11, stRel.pos⟩ .normal
      ⟨stRel.mem, r12, stRel.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨batch + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState]))
      (Expr.eval_const (by omega)) (by have := hBatch.1; unfold tourBlockStepSpace at hRoom; omega), rfl, rfl, rfl⟩
  have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 8) (.const 1))) ⟨stRel.mem, r12, stRel.pos⟩ .normal
      ⟨stRel.mem, r13, stRel.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨edCopy + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r12, r11, r9Rel, r10, r9, r15C, r8]))
      (Expr.eval_const (by omega)) (by unfold tourBlockStepSpace at hRoom; omega), rfl, rfl, rfl⟩
  have ha14 : Runs w p ω (.assign 14 (.const 0)) ⟨stRel.mem, r13, stRel.pos⟩ .normal
      ⟨stRel.mem, r14, stRel.pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.const 0)) ⟨stRel.mem, r14, stRel.pos⟩ .normal
      ⟨stRel.mem, r15, stRel.pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  -- Invoke `tourBlock_loop_runs` on `U`
  have hEF0 : ∀ a, edCopy ≤ a → a < edCopy + editWords → ¬ (tourAsmRep vCap eCap).foot tourH tx a :=
    fun a h1 _ hf => absurd (hFoot a hf) (by omega)
  obtain ⟨hfoot₁, hBF₁, hEF₁, hSF₁, hStF₁⟩ := tourLoop_foot_transport hhLo₁ (by omega)
    (le_refl _) (by omega) (by omega) (fun a ha => lt_trans (hFoot a ha) (by omega))
    hBF hEF0 hSF hstF0 hFt₁
  have hDec_copy := decodeOrdEdits_shift (mem := mem) (mem' := stRel.mem) ed.length (edits + 1) (edCopy + 1)
    (fun k hk => by
      have hk_lt : k + 1 < editWords := by
        have h1 := hEdits.2.1; rw [hed_len_eq] at h1; omega
      have hrel := hRel_eq_C (edCopy + 1 + k) (by omega) (hEF0 _ (by omega) (by omega)) (Or.inr (by omega))
      have hcp := hcpC (1 + k) (by omega)
      rw [show edCopy + 1 + k = edCopy + (1 + k) by omega] at hrel ⊢
      rw [show edits + 1 + k = edits + (1 + k) by omega]; exact hrel.trans hcp)
  have hDec₁ : (decodeOrdEdits stRel.mem ed.length (edCopy + 1)).1 = ed := by
    rw [hDec_copy, ← hed_len_eq]; exact hEdits.1
  have hSum₁ : (decodeOrdEdits stRel.mem ed.length (edCopy + 1)).2.sum = editWords - 1 := by
    rw [hDec_copy, ← hed_len_eq]; have := hEdits.2.1; omega
  have hdrop₁ : L.drop relL₀.length = splitsRest := by rw [hL_decomp, List.drop_left]
  have hroomLoop : hCur₁ + 159 * ((words - 1) + (editWords - 1)) +
      splitsRest.length * tourSplitStepSpace eCap + 4 < 2 ^ w := by
    have hmul : (relL₀.length + splitsRest.length) * tourSplitStepSpace eCap ≤ vCap * tourSplitStepSpace eCap :=
      Nat.mul_le_mul_right _ (by rw [hL_decomp, List.length_append] at hL_le_vCap; exact hL_le_vCap)
    rw [Nat.add_mul] at hmul; unfold tourBlockStepSpace at hRoom
    have hB1 := hBatch.1; have hE1 := hEdits.2.1
    dsimp only [hCur₀, edCopy, relL₀, splitsRest] at hhHi₁ hmul ⊢
    clear * - hRoom hhHi₁ hmul hB1 hE1; omega
  obtain ⟨hCur₂, stL, cLoop, tx₂, splitPtr₂, last₂, ePtrF, sEnd, MEnd, SEnd, YsLoop, hrunLoop,
    hR0L, hR4L, hR6L, hR7L, hR8L, hR9L, hR13L, hR14L, _, hePtrLo, hePtrHi, hDecL, hSumL,
    _, hStL1, _, hRepL, hOrdL, hFeqL, hReqL, hOVFL, hML, hkML, hMsubL, hKL,
    hPreL, hPotL, hhLoL, hhHiL, hZeroL, hFrL, hFtL, hCostL⟩ :=
    tourBlock_loop_runs (C_lsst := C_lsst) (ℓ₀ := ℓ₀) (edits := edits) (statePtr := statePtr) (edCopy := edCopy) (ω := ω)
      hpT hpO hpC hpRel hpMove hw
      (L := L) (keep := keep) (E₀ := tr.S_cur.E) (G₀ := G₁)
      rfl rfl hBatch_le hSp_le (Or.inr (by omega))
      (by unfold tourBlockStepSpace at hRoom; omega) (by unfold tourBlockStepSpace at hRoom; omega)
      hU_lt hed_lt
      U tr.cs ed (batch + 1) (words - 1) (edCopy + 1) (editWords - 1) 0 0
      relL₀.length splitPtr₁ last₁ hCur₁ s₁ tx₁ ⟨stRel.mem, r15, stRel.pos⟩
      tr.S_cur.E S₁ (restrictSplits keep (canonCoreBatch tr.cs Uq₀)) Ys₀
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7, sStart, startState])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8, r7])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10, r9, r15C, r8])
      (by simp [r15, r14, r13, r12, r11, r9Rel])
      (by simp [r15, r14, r13, r12, r11, r9Rel, r10])
      (by simp [r15, r14, r13, r12, r11])
      (by simp [r15, r14, r13, r12]) (by simp [r15, r14, r13]) (by simp [r15, r14]) (by simp [r15])
      (Nat.zero_add _) (by omega) (by have := hBatch.1; omega) (by have := hEdits.2.1; omega)
      (by omega) hhLo₁ hordH (Nat.zero_add _) hI hBU hRlt hOFB (by rw [hOrd₁]; exact hOVF)
      (batchBodyAt_congr hBatch.2.2 fun x hx1 hx2 => hRel_eq_mem x (by omega) (hBF x (by omega) (by omega)))
      hBF₁ hEF₁ hSF₁ hStF₁ hDec₁ hSum₁
      (asmFirstSplitEntriesAt_congr hSpAt fun x hx1 hx2 => hRel_eq_mem x (by omega) (hSF x hx1 hx2))
      ⟨by simpa using hStRel0, hStRel1, hStRel2⟩ hLast₁
      (by rw [hL_decomp, List.length_append]; omega) hdrop₁
      hrep₁ hfoot₁ hZero₁ (by rw [hOrd₁]; exact hOrdG0) hFeq₁ hReq₁
      hM₁' hkM0 (Finset.Subset.rfl) hM0_G hMdisj₁ hKdisj hK₁'
      (by simpa only [List.nil_append] using hPre₁) hroomLoop
  -- Trailing rotation block `tourBlock_tail_rot_runs`
  obtain ⟨hbl_le, _, hrot⟩ := ordEditsForBatch_take_drop hOFB
  set rotEds := ed.drop (batchEditBlocksLen U)
  have hRepL' : TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH sEnd tx₂ stL.mem := hRepL
  have hrot_valid : TourEditsValid vCap eCap sEnd rotEds :=
    (ordEditsValidFor_rot_tourEditsValid rotEds sEnd hrot (ordEditsValidFor_within _ _ hOVFL) hRepL'.valid).1
  have hfoot₂ : ∀ a, (tourAsmRep vCap eCap).foot tourH tx₂ a → a < hCur₂ := fun a ha => by
    rcases hFtL a ha with h1 | ⟨_, hlt⟩; exact lt_of_lt_of_le (hfoot₁ a h1) hhLoL; exact hlt
  have hstL_edCopy : stL.mem edCopy = ed.length := by
    have h1 := hFrL edCopy (by omega) (hEF₁ edCopy (le_refl _) (by have := hEdits.2.1; omega))
      (Or.inr (by omega)) (by rcases hLast₁ with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega))
    have h2 := hRel_eq_C edCopy (by have := hEdits.2.1; omega) (hEF0 edCopy (le_refl _) (by have := hEdits.2.1; omega)) (Or.inr (by omega))
    have h3 := hcpC 0 (by have := hEdits.2.1; omega)
    simpa [hed_len_eq] using h1.trans (h2.trans h3)
  have hroomRot : hCur₂ + 13 * (edCopy + editWords - ePtrF) + 25 < 2 ^ w := by
    have hmul : (relL₀.length + splitsRest.length) * tourSplitStepSpace eCap ≤ vCap * tourSplitStepSpace eCap :=
      Nat.mul_le_mul_right _ (by rw [hL_decomp, List.length_append] at hL_le_vCap; exact hL_le_vCap)
    rw [Nat.add_mul] at hmul; unfold tourBlockStepSpace at hRoom
    have hB1 := hBatch.1; have hE1 := hEdits.2.1
    dsimp only [hCur₀, edCopy, relL₀, splitsRest, cs_wall₀, Uq₀, Uwall₀] at hhHi₁ hhHiL hmul ⊢
    clear * - hRoom hhHi₁ hhHiL hmul hePtrLo hePtrHi hB1 hE1; omega
  have hrotLen : ed.length - batchEditBlocksLen U = rotEds.length := by simp [rotEds]
  obtain ⟨hEnd, stT, cRot, txFinal, hrunRot, hr9T, hregsT, hrepT, hhLoT, hhHiT, hZeroT, hFrT, hFtT, hCostT⟩ :=
    tourBlock_tail_rot_runs (ω := ω) hpT hpC hw hR0L hR4L hR8L hR9L hR13L (by simpa using hR14L)
      hRepL hfoot₂ hZeroL hstL_edCopy hed_lt hbl_le hePtrHi (by omega)
      (by rwa [hrotLen]) (by rwa [hrotLen]) hrot hrot_valid hroomRot
  -- Epilogue: `mem[h] := mem[statePtr + 1]`, `ret hEnd`
  have hStF₂ : ∀ j < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx₂ (statePtr + j) := fun j hj hf => by
    rcases hFtL _ hf with h1 | ⟨hge, _⟩; exact hStF₁ j hj h1; omega
  have hstT_sp : stT.mem (statePtr + 1) = splitPtr₂ :=
    (hFrT (statePtr + 1) (by omega) (hStF₂ 1 (by decide))).trans hStL1
  set memF := Function.update stT.mem h splitPtr₂
  have hstoreH : Runs w p ω (.store (.reg 6) (.load (.bin .add (.reg 7) (.const 1))))
      stT .normal { stT with mem := memF } 6 :=
    runs_store_iff.mpr ⟨h, splitPtr₂,
      Expr.eval_reg_of_eq ((hregsT 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hR6L),
      Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq ((hregsT 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hR7L))
          (Expr.eval_const (by omega)) (by unfold tourBlockStepSpace at hRoom; omega)) hstT_sp,
      rfl, rfl, rfl⟩
  have hretE : Runs w p ω (.ret (.reg 9)) { stT with mem := memF } (.returned hEnd) { stT with mem := memF } 2 :=
    runs_ret_iff.mpr ⟨hEnd, Expr.eval_reg_of_eq hr9T, rfl, rfl, rfl⟩
  have hseqAny : ∀ {A B : Stmt} {s0 sm s1 : State} {o : Outcome} {cA cB : ℕ},
      Runs w p ω A s0 .normal sm cA → Runs w p ω B sm o s1 cB →
      Runs w p ω (A ;; B) s0 o s1 (cA + cB + 1) :=
    fun hA hB => runs_seq_iff.mpr (Or.inr ⟨_, _, _, hA, hB, rfl⟩)
  have hrunTail : Runs w p ω
      (.assign 16 (.load (.reg 8)) ;; .assign 17 (.bin .sub (.reg 16) (.reg 14)) ;;
       .cond (.bin .lt (.const 0) (.reg 17))
         (.assign 18 (.bin .sub (.bin .add (.reg 8) (.reg 4)) (.reg 13)) ;;
          .store (.reg 9) (.reg 17) ;;
          .call 19 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .reg 18] ;;
          .assign 20 (.bin .add (.const 1) (.reg 18)) ;;
          .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .reg 20, .bin .add (.reg 9) (.reg 20)])
         .nop ;;
       .store (.reg 6) (.load (.bin .add (.reg 7) (.const 1))) ;; .ret (.reg 9))
      stL (.returned hEnd) { stT with mem := memF } (cRot + (6 + 2 + 1) + 1) := by
    have h1 := hseqAny hstoreH hretE
    rcases runs_seq_iff.mp hrunRot with ⟨_, _, _, hEq, _⟩ | ⟨sm1, c1, c23, hA1, hB23, rfl⟩
    · cases hEq
    · rcases runs_seq_iff.mp hB23 with ⟨_, _, _, hEq, _⟩ | ⟨sm2, c2, c3, hA2, hA3, rfl⟩
      · cases hEq
      · have := hseqAny hA1 (hseqAny hA2 (hseqAny hA3 h1))
        convert this using 1
  have hrunAll : Runs w p ω (asmFirstTourBlockStepStmt bCopy (bSelf + 0) (bSelf + 1)
      (tourOp bTour 0) (tourOp bTour 1) (tourOp bTour 3) (outIdxSmallSide bOut))
      sStart (.returned hEnd) { stT with mem := memF } _ :=
    hseqAny ha7 (hseqAny ha8 (hseqAny hcallC (hseqAny ha9
      (hseqAny ha10 (hseqAny hcallRel (hseqAny ha11
        (hseqAny ha12 (hseqAny ha13 (hseqAny ha14
          (hseqAny ha15 (hseqAny hrunLoop hrunTail)))))))))))
  -- Final tour state, `OutMarksOf`, `OutSplitListsAt`, mark-potential, frame, footprint, and cost
  set sFinal := tourApplyEdits sEnd rotEds
  have hOrdFinal : sFinal.ord = ord' := by
    have h1 : ∀ (l : List OrdEdit) (s : TourAbs), (tourApplyEdits s l).ord = applyOrdEdits s.ord l := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons d ds ih =>
        intro s
        have hstep : (tourApplyEdit s d).ord = applyOrdEdit s.ord d := by cases d <;> rfl
        exact (ih (tourApplyEdit s d)).trans (by rw [hstep]; rfl)
    rw [h1 rotEds sEnd, hOrdL, hOrd₁]
    change List.foldl applyOrdEdit (List.foldl applyOrdEdit ord (ed.take (batchEditBlocksLen U)))
        (ed.drop (batchEditBlocksLen U)) = List.foldl applyOrdEdit ord ed
    rw [← List.foldl_append, List.take_append_drop]
  have hRfFinal : sFinal.rf = sEnd.rf := by
    have : ∀ (l : List OrdEdit) (s : TourAbs), (∀ d ∈ l, d.IsRotate) → (tourApplyEdits s l).rf = s.rf := by
      intro l; induction l with
      | nil => intro _ _; rfl
      | cons d ds ih =>
        intro s hd
        have hd0 := hd d List.mem_cons_self
        cases d with
        | rotateTo _ _ => exact ih _ (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        | dropEdge _ | moveEnds _ _ _ _ | insertBefore _ _ _ => simp [OrdEdit.IsRotate] at hd0
    exact this rotEds sEnd hrot
  have hFtAll : ∀ a, (tourAsmRep vCap eCap).foot tourH txFinal a →
      (tourAsmRep vCap eCap).foot tourH tx a ∨ (h + 1 ≤ a ∧ a < hEnd) := fun a ha => by
    rcases hFtT a ha with h2 | ⟨hge, hlt⟩
    · rcases hFtL a h2 with h1 | ⟨hge1, hlt1⟩
      · rcases hFt₁ a h1 with h0 | ⟨hge0, hlt0⟩
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, hlt⟩
  have hnotFootH : ¬ (tourAsmRep vCap eCap).foot tourH txFinal h := fun hf => by
    rcases hFtAll h hf with h0 | ⟨hge, _⟩; exact absurd (hFoot h h0) (by omega); omega
  have hlocF := tourAsmRep_local vCap eCap tourH (tourToAsmTour sFinal) txFinal stT.mem memF
    fun a ha => (Function.update_of_ne (fun (heq : a = h) => hnotFootH (heq ▸ ha)) splitPtr₂ stT.mem).symm
  have hRepFinal : (tourAsmRep vCap eCap).rep tourH ⟨ord', info.state.cs.RF, sFinal.marked⟩ txFinal memF :=
    tourAsmRep_congr_graphEq (a₁ := tourToAsmTour sFinal) (a₂ := ⟨ord', info.state.cs.RF, sFinal.marked⟩)
      hOrdFinal rfl (by change GraphEq sFinal.rf.F (compLSFBatch tr.cs U).RF.F; rw [hRfFinal]; exact hFeqL)
      (by change sFinal.rf.R = (compLSFBatch tr.cs U).RF.R; rw [hRfFinal]; exact hReqL) (hlocF.1 hrepT)
  have hRepT' : TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH sFinal txFinal stT.mem := hrepT
  obtain ⟨hMFinal, _, hPotRot⟩ := tourMarkPot_rotate hrot hRepL'.valid hRepT'.valid hML hKL
  have hOutMarks : OutMarksOf ⟨coreTour ord' info.state.cs.RF, sFinal.marked⟩ (outCoreOrder info.state ord') MEnd := by
    have hRepF' : TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord', info.state.cs.RF, sFinal.marked⟩ txFinal memF := hRepFinal
    have hMF2 : TourMarksAt ⟨ord', info.state.cs.RF, sFinal.marked⟩ MEnd := fun z => by
      change z ∈ sFinal.marked ↔ (∃ v, z ∈ ord' v) ∧ z.1 ∉ (compLSFBatch tr.cs U).RF.F.E ∧ z.1 ∈ MEnd
      rw [hMFinal z, hOrdFinal, hRfFinal, hFeqL.2.1]
    have hOM := (tourMarksAt_iff_outMarksOf hRepF'.valid).mp hMF2
    have hGeq : info.state.cs.G = tr.cs.G.applyBatch U := compLSFBatch_G tr.cs U
    have hcast : ∀ {G₁ G₂ : MGraph} (h : G₁ = G₂) (ρ' : Rotation G₁), (h ▸ ρ').order = ρ'.order := by
      intro _ _ h _; cases h; rfl
    have hCoreF : outCoreOrder info.state ord' = coreTour ord' info.state.cs.RF :=
      outCoreOrder_eq_coreTour (hGeq.symm ▸ σ) (compLSFBatch_inv hI hBU) ((hcast hGeq.symm σ).trans hσ)
    rw [hCoreF]; exact hOM
  have hOutLists : OutSplitListsAt memF hEnd (fun a => a < h + 1 ∨ (tourAsmRep vCap eCap).foot tourH txFinal a)
      keep tr.S_cur.E splitPtr₂ G₁ (restrictSplits keep info.U_core) (Ys₀ ++ YsLoop) := by
    have hPreT := outSplitPrefixAt_mono
      (avoid' := fun a => (tourAsmRep vCap eCap).foot tourH txFinal a ∨ a < statePtr + 3)
      hPreL hhLoT
      (fun a ha hna h2 => h2.elim
        (fun hf => (hFtT a hf).elim (fun h0 => hna (Or.inl h0)) fun h => by omega)
        (fun hex => hna (Or.inr hex)))
      (fun a ha hna => hFrT a ha fun hf => hna (Or.inl hf))
    have hres := hPreT.2.2.2 memF hEnd (fun a => a < h + 1 ∨ (tourAsmRep vCap eCap).foot tourH txFinal a) 0 [] []
      (le_refl _) (fun a _ hna hf => hf.elim (fun hlt => hna (Or.inr (by omega))) (fun hf => hna (Or.inl hf)))
      (fun a _ hna _ => Function.update_of_ne (fun heq => hna (Or.inr (by omega))) _ _)
      (fun hne => by
        have hPne : restrictSplits keep (canonCoreBatch tr.cs Uq₀) ++
            restrictSplits keep (canonCoreBatch cs_wall₀ Uwall₀) ≠ [] :=
          fun hE => hne (hPreT.2.1 hE).2.1
        have hlast_ne_h : last₂ + 4 ≠ h := fun heq =>
          (hPreT.2.2.1 hPne).2.2.2.1 (Or.inr (by omega))
        exact (Function.update_of_ne hlast_ne_h _ _).trans (hPreT.2.2.1 hPne).2.2.2.2)
      rfl
    rw [List.append_nil, List.append_nil, ← hPs_decomp] at hres
    by_cases hs0 : splitPtr₂ = 0
    · simpa [hs0] using hres
    · simpa [hs0] using hres
  have hYs_pot : ((Ys₀ ++ YsLoop).map List.length).sum ≤
      G₁.batchEnc (restrictSplits keep info.U_core) + markPot keep tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf) := by
    have hMP0 : tourMarkPot keep s₀ = markPot keep tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf) :=
      tourMarkPot_eq_markPot ρ hI.hG_val (compLSF_RF_isRSF hI) hRep0.valid hρ.symm rfl hM0 hSubE
    rw [hPs_decomp, outBatchEnc_append, List.map_append, List.sum_append]
    have hS₁ : S₁ = G₁.applyBatch (restrictSplits keep (canonCoreBatch tr.cs Uq₀)) := by
      simpa only [List.nil_append] using hPre₁.1
    rw [← hS₁, ← hMP0]
    dsimp only [cs_wall₀, Uq₀, Uwall₀] at hPot₁ hPotL ⊢
    clear * - hPot₁ hPotL; omega
  have hhEnd_hi : hEnd ≤ h + tourBlockStepSpace vCap eCap words editWords := by
    have hmul : (relL₀.length + splitsRest.length) * tourSplitStepSpace eCap ≤ vCap * tourSplitStepSpace eCap :=
      Nat.mul_le_mul_right _ (by rw [hL_decomp, List.length_append] at hL_le_vCap; exact hL_le_vCap)
    rw [Nat.add_mul] at hmul; unfold tourBlockStepSpace
    have hB1 := hBatch.1; have hE1 := hEdits.2.1
    dsimp only [hCur₀, edCopy, relL₀, splitsRest, cs_wall₀, Uq₀, Uwall₀] at hhHi₁ hhHiL hhHiT hmul ⊢
    clear * - hhHi₁ hhHiL hhHiT hmul hePtrLo hePtrHi hB1 hE1; omega
  refine ⟨_, hpMain, hEnd, { stT with mem := memF }, _, txFinal, splitPtr₂, sFinal.marked, MEnd,
    Ys₀ ++ YsLoop, hrunAll, hRepFinal, hkML, hMsubL, hOutMarks, hOutLists, hYs_pot,
    Function.update_self _ _ _, by omega, hhEnd_hi,
    fun a ha => (Function.update_of_ne (by omega) _ _).trans (hZeroT a ha),
    fun a ha hnf => (Function.update_of_ne (by omega) _ _).trans
      ((hFrT a (by omega) (fun hf => by rcases hFtL a hf with h1 | ⟨hge, _⟩; rcases hFt₁ a h1 with h0 | ⟨hge0, _⟩; exact hnf h0; omega; omega)).trans
        ((hFrL a (by omega) (fun hf => by rcases hFt₁ a hf with h0 | ⟨hge0, _⟩; exact hnf h0; omega)
          (Or.inl (by omega)) (by rcases hLast₁ with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega))).trans
          (hRel_eq_mem a ha hnf))),
    hFtAll, ?_⟩
  -- Amortized cost assembly
  simp only [copyWordsContract, argsSize, Expr.size, List.map_append, List.sum_append] at hcostC ⊢
  rw [← hlocF.2]
  have hphiC : (tourAsmRep vCap eCap).phi tourH tx stC.mem = (tourAsmRep vCap eCap).phi tourH tx mem :=
    hlocC.2.symm
  rw [hphiC] at hCost₁
  have hphiL : (tourAsmRep vCap eCap).phi tourH tx₁ ({ mem := stRel.mem, regs := r15, pos := stRel.pos } : State).mem =
      (tourAsmRep vCap eCap).phi tourH tx₁ stRel.mem := rfl
  set Z := (Ys₀.map List.length).sum + (YsLoop.map List.length).sum + tr.S_cur.batchEnc info.U_S +
    words + editWords + 1
  have hZ1 : (Ys₀.map List.length).sum + relL₀.length + 1 ≤ Z := by
    have : relL₀.length ≤ tr.S_cur.batchEnc info.U_S := by
      rw [hL_decomp, List.length_append] at hL_le_bEnc; omega
    dsimp only [Z]; omega
  have hZ2 : (YsLoop.map List.length).sum + splitsRest.length + (words - 1) + (ePtrF - (edCopy + 1)) ≤ Z := by
    have : splitsRest.length ≤ tr.S_cur.batchEnc info.U_S := by
      rw [hL_decomp, List.length_append] at hL_le_bEnc; omega
    dsimp only [Z]; omega
  have hZ_rot : (edCopy + editWords - ePtrF) + 2 ≤ Z := by
    have hE1 := hEdits.2.1; have hB1 := hBatch.1; dsimp only [Z]; clear * - hE1 hB1 hePtrLo hePtrHi; omega
  have hm1 : tourConsumeRelMul * ((Ys₀.map List.length).sum + relL₀.length + 1) * ordStoreLog eCap ≤
      tourConsumeRelMul * Z * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZ1)
  have hm2 : tourBlockLoopMul * ((YsLoop.map List.length).sum + splitsRest.length + (words - 1) +
        (ePtrF - (edCopy + 1))) * ordStoreLog eCap ≤ tourBlockLoopMul * Z * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZ2)
  have hm3' : tourBlockCaseMul * ((edCopy + editWords - ePtrF) + 2) * ordStoreLog eCap ≤
      tourBlockCaseMul * Z * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZ_rot)
  have hov : 17 * editWords + 100 ≤ 100 * Z * ordStoreLog eCap :=
    le_trans (by dsimp only [Z]; omega) (Nat.le_mul_of_pos_right _ htl)
  have hmul_sum : tourConsumeRelMul * Z * ordStoreLog eCap + tourBlockLoopMul * Z * ordStoreLog eCap +
      tourBlockCaseMul * Z * ordStoreLog eCap + 100 * Z * ordStoreLog eCap =
      tourBlockStepMul * Z * ordStoreLog eCap := by
    rw [tourBlockStepMul_eq, tourBlockStepMulFn]
    repeat rw [← Nat.add_mul]
  dsimp only [relL₀, splitsRest, cs_wall₀, Uq₀, Uwall₀] at hCost₁ hCostL hm1 hm2
  clear * - hcostC hCost₁ hCostL hCostT hphiL hm1 hm2 hm3' hov hmul_sum
  omega

/-- **The `Σ |Y|` bound of `AsmBrCoreStepAt`** deduced directly from `asmFirstTourBlockStep_runs`'s
mark-potential bound via `markPot_le` and `log_two_mul_eCap_add_one_le`. -/
theorem asmFirstTourBlockStep_Ys_sum_le {depth capExp vCap eCap M₀ N₀ : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End)
    (hEcard : tr.S_cur.E.card ≤ eCap) (hcap : vCap + eCap + 2 ≤ (M₀ + N₀ + 2) ^ capExp)
    {Ys : List (List End)}
    (hPot : (Ys.map List.length).sum ≤
      (tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete)).batchEnc
        (restrictSplits (outKeep sp tr U ord ord') (stepBundleTree sp tr U ord ord').U_core) +
      markPot (outKeep sp tr U ord ord') tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf)) :
    (Ys.map List.length).sum ≤
      (1 + 4 * capExp) * tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S *
        (Nat.log 2 (M₀ + N₀ + 2) + 1) := by
  have hBE : tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S =
      (outDelList sp tr U ord ord').length +
        (tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete)).batchEnc
          (restrictSplits (outKeep sp tr U ord ord') (stepBundleTree sp tr U ord ord').U_core) +
        (tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete ++
          outSplitBatch sp tr U ord ord')).batchEnc (outInsBatch sp tr U ord ord') := by
    rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_dels]; rfl
  have hdelLen : (outDelList sp tr U ord ord').length = (tr.S_cur.E \ outKeep sp tr U ord ord').card := by
    simp [outDelList]
  have hMP := markPot_le (outKeep sp tr U ord ord') tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf)
  have hlog : Nat.log 2 (2 * tr.S_cur.E.card + 1) ≤ capExp * (Nat.log 2 (M₀ + N₀ + 2) + 1) :=
    le_trans (Nat.log_mono_right (by omega)) (log_two_mul_eCap_add_one_le hcap)
  have h1 : 2 * (tr.S_cur.E \ outKeep sp tr U ord ord').card * (2 * Nat.log 2 (2 * tr.S_cur.E.card + 1)) ≤
      4 * capExp * (outDelList sp tr U ord ord').length * (Nat.log 2 (M₀ + N₀ + 2) + 1) := by
    rw [hdelLen]
    calc 2 * (tr.S_cur.E \ outKeep sp tr U ord ord').card * (2 * Nat.log 2 (2 * tr.S_cur.E.card + 1))
        = 4 * (tr.S_cur.E \ outKeep sp tr U ord ord').card * Nat.log 2 (2 * tr.S_cur.E.card + 1) := by ring
      _ ≤ 4 * (tr.S_cur.E \ outKeep sp tr U ord ord').card * (capExp * (Nat.log 2 (M₀ + N₀ + 2) + 1)) :=
          Nat.mul_le_mul_left _ hlog
      _ = 4 * capExp * (tr.S_cur.E \ outKeep sp tr U ord ord').card * (Nat.log 2 (M₀ + N₀ + 2) + 1) := by ring
  have h2 : (tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete)).batchEnc
        (restrictSplits (outKeep sp tr U ord ord') (stepBundleTree sp tr U ord ord').U_core) ≤
      tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S * (Nat.log 2 (M₀ + N₀ + 2) + 1) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have h3 : 4 * capExp * (outDelList sp tr U ord ord').length * (Nat.log 2 (M₀ + N₀ + 2) + 1) ≤
      4 * capExp * tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S * (Nat.log 2 (M₀ + N₀ + 2) + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h4 : tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S * (Nat.log 2 (M₀ + N₀ + 2) + 1) +
      4 * capExp * tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S * (Nat.log 2 (M₀ + N₀ + 2) + 1) =
      (1 + 4 * capExp) * tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S * (Nat.log 2 (M₀ + N₀ + 2) + 1) := by ring
  omega

/-- Lift of `asmFirstTourBlockStep_runs` directly into `scProg impl cf asmFirstStepSubCode firstInit`
at `L.bFirstS + asmFirstStepSubCode.offMain`. -/
theorem scProg_asmFirstTourBlockStep_runs (impl : SparsifyImpl) (cf : ScCompCode)
    (firstInit : ScSubCode) {w vCap eCap depth tourH batch words edits editWords spPtr h pos : ℕ}
    {ω : ℕ → Bool} (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit}
    {mk : Finset End} {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hready : OutStepReady sp tr U ord (applyOrdEdits ord ed))
    (hRlt : ∀ r ∈ (compLSFBatch tr.cs U).RF.R, r < vCap)
    (hOFB : OrdEditsForBatch tr.cs.G U ed)
    (hOVF : OrdEditsValidFor vCap eCap ord ed)
    (hMarks : OutMarksOf ⟨coreTour ord tr.cs.RF, mk⟩ (outCoreOrder tr ord) tr.S_cur.E)
    (hRep : (tourAsmRep vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx mem)
    (hFoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < h)
    (hZero : ZeroFrom mem h)
    (hBatch : BatchAt mem batch tr.cs.G U words)
    (hEdits : OrdEditsAt mem edits ed editWords)
    (hSpAt : SplitEntriesAt mem spPtr (canonSplitList tr.cs U))
    (hBatch_le : batch + words ≤ h) (hEdits_le : edits + editWords ≤ h)
    (hSp_le : spPtr + 1 + 4 * (canonSplitList tr.cs U).length ≤ h)
    (hBF : ∀ a, batch ≤ a → a < batch + words → ¬ (tourAsmRep vCap eCap).foot tourH tx a)
    (hSF : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * (canonSplitList tr.cs U).length →
      ¬ (tourAsmRep vCap eCap).foot tourH tx a)
    (hRoom : h + tourBlockStepSpace vCap eCap words editWords < 2 ^ w) :
    let L := scLayout impl cf asmFirstStepSubCode firstInit
    let p := scProg impl cf asmFirstStepSubCode firstInit
    let ord' := applyOrdEdits ord ed
    let info := stepBundleTree sp tr U ord ord'
    let keep := outKeep sp tr U ord ord'
    let G₁ := tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete)
    ∃ body, p.procs[L.bFirstS + asmFirstStepSubCode.offMain]? = some body ∧
      ∃ hEnd st' cost tx' splitPtr mk' M Ys,
        Runs w p ω body
          (startState [tourH, batch, words, edits, editWords, spPtr, h] mem pos)
          (.returned hEnd) st' cost ∧
        (tourAsmRep vCap eCap).rep tourH ⟨ord', info.state.cs.RF, mk'⟩ tx' st'.mem ∧
        keep ⊆ M ∧ M ⊆ tr.S_cur.E ∧
        OutMarksOf ⟨coreTour ord' info.state.cs.RF, mk'⟩ (outCoreOrder info.state ord') M ∧
        OutSplitListsAt st'.mem hEnd (fun a => a < h + 1 ∨ (tourAsmRep vCap eCap).foot tourH tx' a)
          keep tr.S_cur.E splitPtr G₁ (restrictSplits keep info.U_core) Ys ∧
        (Ys.map List.length).sum ≤
          G₁.batchEnc (restrictSplits keep info.U_core) +
            markPot keep tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf) ∧
        st'.mem h = splitPtr ∧
        h + 1 ≤ hEnd ∧ hEnd ≤ h + tourBlockStepSpace vCap eCap words editWords ∧
        ZeroFrom st'.mem hEnd ∧
        (∀ a < h, ¬ (tourAsmRep vCap eCap).foot tourH tx a → st'.mem a = mem a) ∧
        (∀ a, (tourAsmRep vCap eCap).foot tourH tx' a →
          (tourAsmRep vCap eCap).foot tourH tx a ∨ (h + 1 ≤ a ∧ a < hEnd)) ∧
        cost + (tourAsmRep vCap eCap).phi tourH tx' st'.mem ≤
          tourBlockStepMul *
              ((Ys.map List.length).sum + tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
            ordStoreLog eCap +
          (tourAsmRep vCap eCap).phi tourH tx mem := by
  dsimp only
  have hidx : (scLayout impl cf asmFirstStepSubCode firstInit).bFirstS + asmFirstStepSubCode.offMain =
      (scLayout impl cf asmFirstStepSubCode firstInit).bFirstS + firstStepOffTourBlock + 2 := by
    simp [asmFirstStepSubCode, firstStepOffTourMain, firstStepOffTourBlock]
  rw [hidx]
  exact asmFirstTourBlockStep_runs
    (scProg_hasTour impl cf asmFirstStepSubCode firstInit)
    (scProg_hasOut impl cf asmFirstStepSubCode firstInit)
    (scProg_hasCopy impl cf asmFirstStepSubCode firstInit)
    (scProg_hasFirstTourBlockProcs impl cf firstInit)
    hw sp hready hRlt hOFB hOVF hMarks hRep hFoot hZero hBatch hEdits hSpAt
    hBatch_le hEdits_le hSp_le hBF hSF hRoom

end

end MinCostFlow.SparseCore.Program
