module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStepFrame
import MinCostFlow.SparseCore.CompLSFBridge

/-!
# The step of a branch (`AssemblyBranchStep`)

An update of the sparse-core tool steps every branch by `stepBundleTree` (`AsmBranchAt.step_runs`,
`AssemblyTopIface.lean`). The program of the step (`asmBrStepStmt`) makes three calls: the first
phase (`AsmBrCoreStepAt`: the tour, the bundles, the spanners, the embedding table), P7's output
step, and P10's update of the readout data. Then it copies P7's four output words and the two words
of the list of re-embedded edges to the places the caller names.

This file puts the three calls together (`asmBrFull_step_runs`). The branch after the step keeps
its record, its caps and its output graph cells. It holds:
* the embedding table and the bundle side that the first phase leaves;
* the tour that P7 leaves, with the marks of the new output graph;
* the readout data that P10 leaves, which hold the view of the model (`asmBr_readStep_runs`).

The proof follows the cells. Each call writes only in the cells of its own part or above its heap
pointer, and the parts lie apart, so every call keeps the other parts. The first phase puts all
the cells of the branch below the heap pointer of P7, P7 puts its new cells of the tour below the
heap pointer of P10, and P10 puts its new cells above it. So the six parts stay apart
(`asmBrDisjoint_of_grow`).

The cost is the cost of the first phase (the charge of the model), plus the cost of P7's step, plus
the cost of P10's update, plus `150` for the steps of the program. The last two are stated here in
the sizes that the calls see: the size of the output batch `U_S`, the split lists and the list `T₀`
bounded by the first phase, and the size of the change record of P4 (`lsfChangeSize`). The space
is `asmBrStepSpace`, a function of the caps and the sizes of the inputs.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Read

/-- **The step of a branch.** Let `J` be the first phase, P7's output step meet its signature on
P7's view of P2's tour (`AsmBrOutProj`), and P10 meet `ReadBranchAt` at the caps of the branch.
Let the branch hold the state `tr` with input order `ord`, the facts of the model hold before and
after the step, the order edits come in one block per update (`OrdEditsForBatch`, passed on to
`J`), and the input batch, the order edits and the change record of P4 for the branch lie below
`h` outside the cells of the branch. Then the step runs, the branch holds the state after
`stepBundleTree` with the order `ord'`, and:
* the output batch `U_S` and the edits of the output order are at the four words at `outSlot`,
  and the list of re-embedded edges is at the two words at `reembSlot`, all in new cells;
* the space is at most `asmBrStepSpace`, the frame and the growth of the cells hold;
* the cost is the charge of the first phase, plus P7's step, plus P10's update, plus `150`. -/
theorem asmBrFull_step_runs {HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop} {idx : ℕ → ℕ}
    (hsig : sig_outStepSmall_blocks_runs HasOutProcs idx) :
    ∃ mulOut : ℕ, ∀ {OS : OutTourSpec} {w : ℕ} {p : Program} {nm sm fm lm : ℕ}
      {TR : ℕ → ℕ → DSRep AsmTourAbs}
      {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
      {impl : SparsifyImpl} {depth P L capExp limbMul wordExp fCore : ℕ}
      {Ψ : BundleTreeState depth → ℕ}
      (J : AsmBrCoreStepAt TR B5 impl depth P L capExp limbMul wordExp w Ψ p fCore)
      {bOut bR fRoot readMul f : ℕ} {readIdx : ℕ → ℕ} {Q : RootQueryAt w p fRoot},
      (∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local) →
      (∀ vCap eCap, (TR vCap eCap).Local) → AsmBrOutProj OS TR w p nm sm fm lm →
      (∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH) →
      HasOutProcs p bOut nm sm fm lm →
      p.procs[f]? = some (asmBrStepStmt fCore (idx bOut) (bR + readIdx 2)) →
      let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
      ∀ (b cfH j batch words edits editWords fChgPtr outSlot reembSlot h fSplitPtr k M N vCap eCap n : ℕ)
        (tr : BundleTreeState depth) (ord : ℕ → List End) (x : R.τ) (U : List Update)
        (ed : List OrdEdit) (c : LSFChange) (SP : DSParams) (cap : ℕ) (mem : ℕ → ℕ) (pos : ℕ)
        (ω : ℕ → Bool),
      let ord' := applyOrdEdits ord ed
      let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
        fun _ => canonicalSparsify impl
      let info := stepBundleTree sparsify tr U ord ord'
      let chg := mem (fChgPtr + j)
      let spPtr := mem (fSplitPtr + j)
      ReadBranchAt (readRep vCap eCap x.tCap x.L_w P) w vCap eCap x.tCap x.L_w P SP cap p
        bR readIdx fRoot Q readMul →
      tr.m₀ = M → tr.n₀ = N →
      1 ≤ depth → depth ≤ bundleLogFactor M N → depth ≤ Expander.chosenL ((M + N) ^ 2) →
      16 ≤ 2 ^ w →
      (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w →
      ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N →
      BranchUpdatesBelow impl tr n →
      BranchUpdatesBelow impl info.state (n + U.length) →
      R.rep b ⟨tr, ord, vCap, eCap⟩ x mem →
      AsmBrModelFacts impl vCap eCap tr ord →
      AsmBrModelFacts impl vCap eCap info.state ord' →
      SmallBatchAt mem batch tr.cs.G U words → tr.cs.G.BatchIsValid U →
      BatchWithinCaps vCap eCap U →
      OrdEditsAt mem edits ed editWords → OrderedBatch tr.cs.G U ord ord' →
      OrdEditsValidFor vCap eCap ord ed →
      OrdEditsForBatch tr.cs.G U ed →
      LSFChangeAt mem chg c → c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf →
      SplitEntriesAt mem spPtr (canonSplitList tr.cs U) →
      InputAt w mem (R.foot b x) batch words h → InputAt w mem (R.foot b x) edits editWords h →
      InputAt w mem (R.foot b x) chg c.words h →
      InputAt w mem (R.foot b x) spPtr (splitEntriesWords (canonSplitList tr.cs U)) h →
      outSlot + 4 ≤ h → reembSlot + 2 ≤ h →
      (∀ a, outSlot ≤ a → a < outSlot + 4 → ¬ (reembSlot ≤ a ∧ a < reembSlot + 2)) →
      (∀ a, outSlot ≤ a → a < outSlot + 4 → ¬ R.foot b x a) →
      (∀ a, reembSlot ≤ a → a < reembSlot + 2 → ¬ R.foot b x a) →
      (∀ a, R.foot b x a → a < h) →
      (∀ a ∈ [b, cfH, j, batch, words, edits, editWords, fChgPtr, outSlot, reembSlot, h],
        a < 2 ^ w) →
      chg < 2 ^ w → fChgPtr + j < 2 ^ w → spPtr < 2 ^ w → fSplitPtr + j < 2 ^ w →
      (vCap + eCap + 2) ^ 2 < 2 ^ w →
      ZeroFrom mem h →
      h + asmBrStepSpace J.space readMul OS k M N L depth vCap eCap x.tCap x.L_w words editWords <
        2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' cst x',
        Runs w p ω body
          (startState [b, cfH, j, batch, words, edits, editWords, fChgPtr, outSlot, reembSlot, h,
            fSplitPtr] mem pos) o st' cst ∧
        R.rep b ⟨info.state, ord', vCap, eCap⟩ x' st'.mem ∧
        SmallBatchAt st'.mem (st'.mem outSlot) tr.S_cur info.U_S (st'.mem (outSlot + 1)) ∧
        h ≤ st'.mem outSlot ∧ st'.mem outSlot + st'.mem (outSlot + 1) ≤ o.value ∧
        (∃ outEd : List OrdEdit,
          OrdEditsAt st'.mem (st'.mem (outSlot + 2)) outEd (st'.mem (outSlot + 3)) ∧
          applyOrdEdits (tr.outOrder ord) outEd = info.state.outOrder ord' ∧
          OrdEditsValidFor vCap eCap (tr.outOrder ord) outEd ∧
          OrdEditsForBatch tr.S_cur info.U_S outEd) ∧
        h ≤ st'.mem (outSlot + 2) ∧ st'.mem (outSlot + 2) + st'.mem (outSlot + 3) ≤ o.value ∧
        readList st'.mem (st'.mem reembSlot) (st'.mem (reembSlot + 1)) =
          stepBundleTree_reembList sparsify tr U ord ord' ∧
        h ≤ st'.mem reembSlot ∧ st'.mem reembSlot + st'.mem (reembSlot + 1) ≤ o.value ∧
        h ≤ o.value ∧
        o.value ≤
          h + asmBrStepSpace J.space readMul OS k M N L depth vCap eCap x.tCap x.L_w words editWords ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ R.foot b x a → ¬ (outSlot ≤ a ∧ a < outSlot + 4) →
          ¬ (reembSlot ≤ a ∧ a < reembSlot + 2) → st'.mem a = mem a) ∧
        (∀ a, R.foot b x' a → R.foot b x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ t < st'.mem (outSlot + 3), st'.mem (st'.mem (outSlot + 2) + t) < 2 ^ w) ∧
        (∀ a, st'.mem outSlot ≤ a → a < st'.mem outSlot + st'.mem (outSlot + 1) → ¬ R.foot b x' a) ∧
        (∀ a, st'.mem (outSlot + 2) ≤ a → a < st'.mem (outSlot + 2) + st'.mem (outSlot + 3) →
          ¬ R.foot b x' a) ∧
        st'.mem (outSlot + 3) ≤
          5 * (2 * tr.S_cur.batchEnc info.U_S +
            J.ysMul * (tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
              (Nat.log 2 (M + N + 2) + 1)) + 1 ∧
        cst + R.phi b x' st'.mem ≤
          J.mul * (branchStepCharge sparsify tr U ord ord' +
              (words + editWords + 1) * bundleLogFactor M N) +
            mulOut * (OS.mul + 1) *
              (tr.S_cur.batchEnc info.U_S +
                J.ysMul * (tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
                  (Nat.log 2 (M + N + 2) + 1) + 1) * ordStoreLog eCap +
            readMul * ((words + (5 * tr.S_cur.batchEnc info.U_S + 1) + 1) * (x.L_w + 1) +
              lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf) + 150 +
            R.phi b x mem := by
  obtain ⟨mulOut, hOut⟩ := asmBrStep_out_runs hsig
  refine ⟨mulOut, ?_⟩
  intro OS w p nm sm fm lm TR B5 impl depth P L capExp limbMul wordExp fCore Ψ J bOut bR fRoot
    readMul f readIdx Q hB5 hTR hOP hTh hHas hf R b cfH j batch words edits editWords fChgPtr
    outSlot reembSlot h fSplitPtr k M N vCap eCap n tr ord x U ed c SP cap mem pos ω ord' sparsify
    info chg spPtr hB hM hN hdepth hdepth_lg hdepth_ch h16 hword hThU hBUn hBUn' hrep hold hnew hBat hBU hcaps hEd hord hEdV
    hEdB hC hc hSpAt hBin hEin hCin hSpin hos hrs hslots hosF hrsF hfoot hargs hchgW hchgjW hspW
    hspjW hw2 hz hspace
  obtain ⟨hrepA, hV5, hE5, hvc, hec, htc, hsc, hlw, hγ⟩ := hrep
  subst hvc hec
  obtain ⟨hw0, hw1, hw2', hw3, hw4, hw5, hw6, hw7, hw8, hG, hlsf, hS, hinv, hRrep, -, -, -, hOrep,
    -, -, -, -, hcapB, hLwB, hdisj⟩ := id hrepA
  have hrecLt : b + ASM_BR_SIZE ≤ h := asmBr_record_lt hfoot
  have hhw : h < 2 ^ w := hargs h (by simp)
  -- the word size gives room for the caps
  have hvew : x.vCap + x.eCap + 2 < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_self_pow (by norm_num) _) hw2
  have h4w : 4 ≤ 2 ^ w := by
    have : 2 ^ 2 ≤ (x.vCap + x.eCap + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  -- the change record of P4 is small
  obtain ⟨C', ℓ', hI', -⟩ := hnew.2.1
  have hRnew : ∀ v ∈ (compLSFBatch tr.cs U).lsf.F.R, v < x.vCap := fun v hv =>
    hnew.2.2.2.2.2.2.2.1 v ((compLSF_RF_isRSF hI').2.2.1 hv)
  have hFold : ∀ e ∈ tr.cs.lsf.F.F.E, e < x.eCap := by
    rw [← hlsf]
    intro e he
    exact hinv.2.2.1 e (hinv.2.2.2.2.2.2.2.2.2.1.2.1 he)
  have hcw : c.words ≤ x.vCap + x.eCap + 2 := lsfChange_words_le hc hRnew hFold
  have hspace' := hspace
  unfold asmBrStepSpace at hspace'
  have hspJ : h + J.space (M + N + k + x.vCap + x.eCap + L + depth + words + editWords) < 2 ^ w := by
    omega
  -- the first phase
  have hargsJ : ∀ a ∈ [b, batch, words, edits, editWords, chg, spPtr, h], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hchgW
    · exact hspW
    · exact hhw
  obtain ⟨bodyC, hbC, oC, stC, cC, yEmb, sTour, xTour, xRest, Ys, T₀, hrunC, hembC, hdomC,
    hembAgC, hTC, hmkC, hXC, hSC, hV5C, hE5C, hdisjC, hkeepC, hInC, hrot1, hrot2, hrfree, hTnd,
    hTv, hcov,
    hreembL, hreembLo, hreembFree, hwordsC, hYs, hoC_lo, hoC_hi, hzC, hfrC, hgrowC, hcostC⟩ :=
    J.runs b batch words edits editWords chg spPtr h k M N n tr ord x U ed c mem pos ω hM hN
      hdepth hdepth_lg hdepth_ch h16 hword hThU hBUn hBUn' ⟨hrepA, hV5, hE5, rfl, rfl, htc, hsc, hlw, hγ⟩
      hnew hBat hBU hcaps hEd hord hEdV hEdB hC hc hSpAt hBin hEin hCin hSpin hfoot hargsJ hz hspJ
  simp only [ASM_ST_SIZE] at hoC_lo hreembLo hgrowC
  simp only [ASM_ST_REEMB, ASM_ST_REEMBLEN] at hreembL hreembLo hreembFree
  have hx1lt : ∀ a, R.foot b (x.afterCore yEmb sTour xTour xRest) a → a < oC.value :=
    fun a ha => by
      rcases hgrowC a ha with h1 | h1
      · have := hfoot a h1; omega
      · omega
  -- P7's output step, on P7's view of the new tour
  obtain ⟨⟨repT, hloc7, hn7, hs7, hf7, hl7⟩, hrepT⟩ :=
    hOP x.vCap x.eCap ord' info.state.cs.lsf.F (outCoreOrder info.state ord')
  subst hrepT
  let TT : OutTourAt OS w x.vCap x.eCap p nm sm fm lm := ⟨_, hloc7, hn7, hs7, hf7, hl7⟩
  have hspO : oC.value + outStepSpace OS x.vCap x.eCap < 2 ^ w := by omega
  have hOS := outStepSpace_ge OS x.vCap x.eCap
  obtain ⟨bodyO, hbO, oO, stO, cO, tx', s', hrunO, hOutRep, hTO, hmkO, hUSO, hEdO, hEdWordsLt,
    hUSlo, hUS12, hEd23, hoO_hi, hzO, hfrO, hgrowO, hcostO⟩ :=
    hOut (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) P L capExp bOut impl x.vCap x.eCap b
      h tr ord U ed x TT mem stC oC sTour xTour Ys T₀ stC.pos ω hHas (hTh x.vCap x.eCap) hw2 hrepA
      hold hnew hBU hord (fun a ha => hkeepC a (ha.elim Or.inl fun h3 => Or.inr (Or.inr h3)))
      hTC hmkC hInC hrot1 hrot2 hrfree hTnd hTv hcov hwordsC
      (fun a ha => by have := hfoot a ⟨3, by decide, ha⟩; omega)
      (fun a ha => hx1lt a ⟨4, by decide, ha⟩)
      (fun a ha => hdisjC 3 (by decide) 4 (by decide) (by decide) a ha) hzC hspO
  have hoCO : oC.value + 4 ≤ oO.value := by omega
  -- what the first two calls keep
  have hnT : ∀ a < h, ¬ R.foot b x a → ¬ TT.rep.foot x.tourH xTour a :=
    fun a ha hna h4 => by
      rcases hgrowC a ⟨4, by decide, h4⟩ with h1 | h1
      · exact hna h1
      · omega
  have hkeepCO : ∀ a < h, ¬ R.foot b x a → stO.mem a = mem a := fun a ha hna =>
    (hfrO a (by omega) (fun h3 => hna ⟨3, by decide, h3⟩) (hnT a ha hna)).trans
      (hfrC a ha hna)
  have hkeepO : ∀ i < 6, i ≠ 3 → i ≠ 4 → ∀ a,
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b
        (x.afterCore yEmb sTour xTour xRest) i a → stO.mem a = stC.mem a :=
    fun i hi h3 h4 a ha => hfrO a (hx1lt a ⟨i, hi, ha⟩)
      (fun ho => hdisjC i hi 3 (by decide) h3 a ha ho)
      (fun ht => hdisjC i hi 4 (by decide) h4 a ha ht)
  have hkeepRec : ∀ a, asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 0 a →
      stO.mem a = mem a := fun a ha =>
    (hkeepO 0 (by decide) (by decide) (by decide) a ha).trans (hkeepC a (Or.inl ha))
  have hkeepRd : ∀ a, asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 1 a →
      stO.mem a = mem a := fun a ha =>
    (hkeepO 1 (by decide) (by decide) (by decide) a ha).trans (hkeepC a (Or.inr (Or.inl ha)))
  have hreadW : stO.mem (b + ASM_BR_READ) = x.readH := by
    rw [hkeepRec _ ⟨by omega, by simp [ASM_BR_READ, ASM_BR_SIZE]⟩]; exact hw0
  have hRO : (readRep x.vCap x.eCap x.tCap x.L_w P).rep x.readH x.yRead.view x.yRead stO.mem :=
    ((readRep_local x.vCap x.eCap x.tCap x.L_w P) x.readH x.yRead.view x.yRead mem stO.mem
      (fun a ha => (hkeepRd a ha).symm)).1 hRrep
  -- the inputs of P10, unchanged
  have hinNF : ∀ {a0 n0 : ℕ}, InputAt w mem (R.foot b x) a0 n0 h →
      ∀ a, a0 ≤ a → a < a0 + n0 → stO.mem a = mem a := fun {a0 n0} hI a h1 h2 => by
    have hn := (hI.2 (a - a0) (by omega)).2
    rw [show a0 + (a - a0) = a by omega] at hn
    exact hkeepCO a (by have := hI.1; omega) hn
  have hInO : ∀ {a0 n0 : ℕ}, InputAt w mem (R.foot b x) a0 n0 h →
      InputAt w stO.mem (readFoot x.vCap x.eCap x.tCap x.L_w x.readH x.yRead) a0 n0 oO.value :=
    fun {a0 n0} hI => ⟨by have := hI.1; omega, fun i hi =>
      ⟨by rw [hinNF hI (a0 + i) (by omega) (by omega)]; exact (hI.2 i hi).1,
        fun hr => (hI.2 i hi).2 ⟨1, by decide, hr⟩⟩⟩
  have hBatO : BatchAt stO.mem batch tr.cs.G U words :=
    (smallBatchAt_of_agree hBat fun a h1 h2 => hinNF hBin a h1 h2).1
  have hCO : LSFChangeAt stO.mem chg c := lsfChangeAt_of_agree hC fun a h1 h2 => hinNF hCin a h1 h2
  -- P10's update
  have hus : stO.mem oC.value + stO.mem (oC.value + 1) ≤ oO.value := by omega
  have husF : ∀ i < stO.mem (oC.value + 1),
      ¬ readFoot x.vCap x.eCap x.tCap x.L_w x.readH x.yRead (stO.mem oC.value + i) :=
    fun i _ hr => by have := hfoot _ ⟨1, by decide, hr⟩; omega
  have hrdLt : x.readH < h := hfoot _ ⟨1, by decide, Or.inl ⟨le_rfl, by simp [readFullWords]⟩⟩
  have hargsR : ∀ a ∈ [x.readH, batch, words, chg, stO.mem oC.value, oO.value], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hchgW
    · omega
    · omega
  have husOS : stO.mem (oC.value + 1) ≤ outStepSpace OS x.vCap x.eCap := by omega
  have hRmono := readSpace_mono (mul := readMul) (vCap := x.vCap) (tCap := x.tCap) (L_w := x.L_w)
    (show words + c.words + stO.mem (oC.value + 1) ≤
      words + (x.vCap + x.eCap + 2) + outStepSpace OS x.vCap x.eCap by omega)
  have hspR : oO.value + readSpace readMul x.vCap x.tCap x.L_w
      (words + c.words + stO.mem (oC.value + 1)) < 2 ^ w := by omega
  obtain ⟨bodyR, hbR, oR, stR, cR, y', hrunR, hRR, hy'v, hInv', hoR_lo, hoR_hi, hzR, hfrR,
    hgrowR, hcostR⟩ :=
    asmBr_readStep_runs hB impl x.readH batch words chg (stO.mem oC.value)
      (stO.mem (oC.value + 1)) oO.value tr ord U ed c x.yRead stO.mem stO.pos ω hargsR hG hlsf
      hS hinv hRO (fun a ha => by have := hfoot a ⟨1, by decide, ha⟩; omega) hzO hold hnew hBU
      hord hBatO hcaps (hInO hBin) hCO hc (hInO hCin) hUSO.1 hus husF (by omega) h4w (by omega)
      (by omega) hspR
  rw [← hreadW] at hrunR
  -- the program
  obtain ⟨st', cst, hrun, hmem', hcst⟩ :=
    asmBrStepStmt_runs (cfH := cfH) (edits := edits) (editWords := editWords)
      (outSlot := outSlot) (reembSlot := reembSlot) (fSplitPtr := fSplitPtr) (by omega) hchgjW hspjW
      (by simp only [ASM_ST_SIZE]; omega) (by omega)
      (by omega) (by omega) hbC hbO hbR hrunC hrunO hrunR
  -- what the last call and the copies keep
  have hkeepR_hi : ∀ a, h ≤ a → a < oO.value → stR.mem a = stO.mem a := fun a h1 h2 =>
    hfrR a h2 (fun hr => by have := hfoot a ⟨1, by decide, hr⟩; omega)
  have hor := slots_apart hslots
  have hkeepS : ∀ a, ¬ (outSlot ≤ a ∧ a < outSlot + 4) → ¬ (reembSlot ≤ a ∧ a < reembSlot + 2) →
      st'.mem a = stR.mem a := fun a h1 h2 => by rw [hmem']; exact asmBrStepCopy_keep h1 h2
  have hkeepS_hi : ∀ a, h ≤ a → st'.mem a = stR.mem a := fun a ha =>
    hkeepS a (by omega) (by omega)
  have hnO_hi : ∀ a, h ≤ a → ¬ (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a :=
    fun a h1 h3 => by have := hfoot a ⟨3, by decide, h3⟩; omega
  have hnT_hi : ∀ a, h ≤ a → a < h + 6 → ¬ TT.rep.foot x.tourH xTour a :=
    fun a h1 h2 h4 => by
      rcases hgrowC a ⟨4, by decide, h4⟩ with h5 | h5
      · have := hfoot a h5; omega
      · omega
  have hkeepC_hi : ∀ a, h ≤ a → a < oC.value →
      ¬ (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a →
      ¬ TT.rep.foot x.tourH xTour a → st'.mem a = stC.mem a :=
    fun a h1 h2 h3 h4 => by
      rw [hkeepS_hi a h1, hkeepR_hi a h1 (by omega)]
      exact hfrO a h2 h3 h4
  have hfreeKeep : ∀ {a0 n0 : ℕ}, h ≤ a0 → OutCellsFree a0 n0 oC.value (fun a =>
      (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a ∨
        TT.rep.foot x.tourH xTour a) →
      ∀ a, a0 ≤ a → a < a0 + n0 → st'.mem a = stC.mem a := fun {a0 n0} hlo hF a h1 h2 => by
    have hn := hF.2 (a - a0) (by omega)
    rw [show a0 + (a - a0) = a by omega] at hn
    exact hkeepC_hi a (by omega) (by have := hF.1; omega) (fun ho => hn (Or.inl ho))
      (fun ht => hn (Or.inr ht))
  -- the words that the copies write
  have hcpO : ∀ i < 4, st'.mem (outSlot + i) = stO.mem (oC.value + i) := fun i hi => by
    have hc := asmBrStepCopy_out (m := stR.mem) (h₁ := oC.value) (h := h) hor
      (Or.inl (show outSlot + 4 ≤ oC.value by omega)) hi
    rw [hmem', hc]
    exact hkeepR_hi _ (by omega) (by omega)
  have hU0 : st'.mem outSlot = stO.mem oC.value := by simpa using hcpO 0 (by norm_num)
  have hU1 : st'.mem (outSlot + 1) = stO.mem (oC.value + 1) := hcpO 1 (by norm_num)
  have hU2 : st'.mem (outSlot + 2) = stO.mem (oC.value + 2) := hcpO 2 (by norm_num)
  have hU3 : st'.mem (outSlot + 3) = stO.mem (oC.value + 3) := hcpO 3 (by norm_num)
  have hcpR : ∀ i < 2, st'.mem (reembSlot + i) = stC.mem (h + (4 + i)) := fun i hi => by
    have hc := asmBrStepCopy_reemb (m := stR.mem) (o := outSlot) (r := reembSlot) (h₁ := oC.value)
      (h := h)
      (Or.inl (by simp only [ASM_ST_REEMB]; omega)) (Or.inl (by simp only [ASM_ST_REEMB]; omega))
      hi
    simp only [ASM_ST_REEMB] at hc
    rw [hmem', hc, hkeepR_hi _ (by omega) (by omega), show h + 4 + i = h + (4 + i) by omega]
    exact hfrO _ (by omega) (hnO_hi _ (by omega)) (hnT_hi _ (by omega) (by omega))
  have hRe0 : st'.mem reembSlot = stC.mem (h + 4) := by simpa using hcpR 0 (by norm_num)
  have hRe1 : st'.mem (reembSlot + 1) = stC.mem (h + 5) := hcpR 1 (by norm_num)
  -- the branch after the step
  let x' : AsmBrConc TR (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).τ :=
    { x with yRead := y', yEmb := yEmb, sTour := s', xTour := tx', xRest := xRest }
  have hpart' : ∀ i < 6, ∀ a, asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x' i a →
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b
          (x.afterCore yEmb sTour xTour xRest) i a ∨
        ((i = 1 ∧ oO.value ≤ a ∧ a < oR.value) ∨ (i = 4 ∧ oC.value ≤ a ∧ a < oO.value)) := by
    intro i hi a ha
    interval_cases i
    · exact Or.inl ha
    · rcases hgrowR a ha with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
    · exact Or.inl ha
    · exact Or.inl ha
    · rcases hgrowO a ha with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨rfl, by omega, h1.2⟩)
    · exact Or.inl ha
  have hdisj' : AsmBrDisjoint (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x' :=
    asmBrDisjoint_of_grow
      (fun i a => (i = 1 ∧ oO.value ≤ a ∧ a < oR.value) ∨ (i = 4 ∧ oC.value ≤ a ∧ a < oO.value))
      hdisjC hpart'
      (fun i _ a hN hf => by
        have := hx1lt a hf
        rcases hN with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega)
      (fun i _ j _ hij a h1 h2 => by
        rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases h2 with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;> omega)
  have hfoot' : ∀ a, R.foot b x' a → R.foot b x a ∨ (h ≤ a ∧ a < oR.value) := by
    rintro a ⟨i, hi, ha⟩
    rcases hpart' i hi a ha with h1 | h1
    · rcases hgrowC a ⟨i, hi, h1⟩ with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases h1 with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
      · exact Or.inr ⟨by omega, h2⟩
      · exact Or.inr ⟨by omega, by omega⟩
  -- the representation after the step, on the memory after the last call
  have hkeepR1 : ∀ i < 6, i ≠ 1 → ∀ a,
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b
        (x.afterCore yEmb sTour xTour xRest) i a → stR.mem a = stO.mem a :=
    fun i hi h1 a ha => hfrR a (by have := hx1lt a ⟨i, hi, ha⟩; omega)
      (fun hr => hdisjC i hi 1 (by decide) h1 a ha hr)
  have hagT : ∀ a, TT.rep.foot x.tourH tx' a → stO.mem a = stR.mem a :=
    fun a ha => by
      rcases hgrowO a ha with h1 | h1
      · exact (hkeepR1 4 (by decide) (by decide) a h1).symm
      · exact (hkeepR_hi a (by omega) h1.2).symm
  have hTloc := TT.rep_local x.tourH s' tx' stO.mem stR.mem hagT
  have hXloc := (asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ) x.restH
    ⟨info.state, ord', x.vCap, x.eCap⟩
    xRest stC.mem stR.mem (fun a ha =>
      ((hkeepR1 5 (by decide) (by decide) a ha).trans
        (hkeepO 5 (by decide) (by decide) (by decide) a ha)).symm)
  have hrec : ∀ i < ASM_BR_SIZE, stR.mem (b + i) = mem (b + i) := fun i hi =>
    (hkeepR1 0 (by decide) (by decide) _ ⟨by omega, by omega⟩).trans
      (hkeepRec _ ⟨by omega, by omega⟩)
  have hrepR : R.rep b ⟨info.state, ord', x.vCap, x.eCap⟩ x' stR.mem := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdomC, hembAgC, ?_, ?_,
      hmkO, hXloc.1 hXC, hnew.2.2.1.2.1, hcapB, hLwB, hdisj'⟩, hV5C, hE5C, rfl, rfl, htc,
      hSC ▸ hsc, hlw, hγ⟩
    · rw [hrec _ (by decide)]; exact hw0
    · rw [hrec _ (by decide)]; exact hw1
    · rw [hrec _ (by decide)]; exact hw2'
    · rw [hrec _ (by decide)]; exact hw3
    · rw [hrec _ (by decide)]; exact hw4
    · rw [hrec _ (by decide)]; exact hw5
    · rw [hrec _ (by decide)]; exact hw6
    · rw [hrec _ (by decide)]; exact hw7
    · rw [hrec _ (by decide)]; exact hw8
    · show y'.view.G = _
      rw [hy'v]
    · show y'.view.lsf = _
      rw [hy'v]
    · show y'.view.S = _
      rw [hy'v]
    · show y'.view.Inv x.vCap x.eCap x.tCap
      rw [hy'v]; exact hInv'
    · show (readRep x.vCap x.eCap x.tCap x.L_w P).rep x.readH y'.view y' stR.mem
      rw [hy'v]; exact hRR
    · exact ((embRep_local x.eCap) x.embH yEmb.view yEmb stC.mem stR.mem (fun a ha =>
        ((hkeepR1 2 (by decide) (by decide) a ha).trans
          (hkeepO 2 (by decide) (by decide) (by decide) a ha)).symm)).1 hembC
    · exact ((outGraphRep_local x.vCap x.eCap) x.outH info.state.S_cur x.gOut stO.mem stR.mem
        (fun a ha => (hkeepR1 3 (by decide) (by decide) a ha).symm)).1 hOutRep
    · exact hTloc.1 hTO
  have hRloc := asmBrFullRep_local (depth := depth) (TR := TR) hTR hB5 (impl := impl) (w := w) (P :=
    P) (L := L) (capExp := capExp) (limbMul := limbMul) (Ψ := Ψ)
  have hagS : ∀ a, R.foot b x' a → stR.mem a = st'.mem a := fun a ha => by
    rcases hfoot' a ha with h1 | h1
    · exact (hkeepS a (fun h2 => hosF a h2.1 h2.2 h1) (fun h2 => hrsF a h2.1 h2.2 h1)).symm
    · exact (hkeepS_hi a h1.1).symm
  have hRS := hRloc b ⟨info.state, ord', x.vCap, x.eCap⟩ x' stR.mem st'.mem hagS
  -- the cost
  have hphi' : R.phi b x' st'.mem = readPotMul * treePot y'.view.G y'.view.lsf.T +
      TT.rep.phi x.tourH tx' stO.mem +
      (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).phi x.restH xRest stC.mem := by
    rw [← hRS.2]
    show readPotMul * treePot y'.view.G y'.view.lsf.T +
      TT.rep.phi x.tourH tx' stR.mem +
      (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).phi x.restH xRest stR.mem = _
    rw [← hTloc.2, ← hXloc.2]
  have hC' : cC + (readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
      TT.rep.phi x.tourH xTour stC.mem +
      (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).phi x.restH xRest stC.mem) ≤
      J.mul * (branchStepCharge sparsify tr U ord ord' +
        (words + editWords + 1) * bundleLogFactor M N) + R.phi b x mem := hcostC
  have hO' : cO + TT.rep.phi x.tourH tx' stO.mem ≤
      mulOut * (OS.mul + 1) *
        (tr.S_cur.batchEnc info.U_S + (Ys.map List.length).sum + T₀.length + 1) *
        ordStoreLog x.eCap + TT.rep.phi x.tourH xTour stC.mem := hcostO
  have hR' : cR + readPotMul * treePot y'.view.G y'.view.lsf.T ≤
      readMul * ((words + stO.mem (oC.value + 1) + 1) * (x.L_w + 1) + c.size) +
        readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T := hcostR
  have hYs' : (Ys.map List.length).sum + T₀.length ≤
      J.ysMul * (tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
        (Nat.log 2 (M + N + 2) + 1) := hYs
  have hOle : mulOut * (OS.mul + 1) *
        (tr.S_cur.batchEnc info.U_S + (Ys.map List.length).sum + T₀.length + 1) *
        ordStoreLog x.eCap ≤
      mulOut * (OS.mul + 1) *
        (tr.S_cur.batchEnc info.U_S +
          J.ysMul * (tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
            (Nat.log 2 (M + N + 2) + 1) + 1) * ordStoreLog x.eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hsz := lsfChange_size_eq hc
  have husW : stO.mem (oC.value + 1) ≤ 5 * tr.S_cur.batchEnc info.U_S + 1 := hUSO.2
  have hRle : readMul * ((words + stO.mem (oC.value + 1) + 1) * (x.L_w + 1) + c.size) ≤
      readMul * ((words + (5 * tr.S_cur.batchEnc info.U_S + 1) + 1) * (x.L_w + 1) +
        lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega))
  obtain ⟨outEd, hEdAt, hEdApply, hEdEnc, hEdW, hEdU, hEdFB⟩ := hEdO
  have hfoot_no_mid : ∀ a, oC.value ≤ a →
      a < stO.mem (oC.value + 2) + stO.mem (oC.value + 3) → ¬ R.foot b x' a := by
    rintro a ha1 ha2 ⟨i, hi, ha⟩
    interval_cases i
    · exact absurd (hx1lt a ⟨0, by decide, ha⟩) (by omega)
    · rcases hgrowR a ha with h1 | h1
      · exact absurd (hx1lt a ⟨1, by decide, h1⟩) (by omega)
      · omega
    · exact absurd (hx1lt a ⟨2, by decide, ha⟩) (by omega)
    · exact absurd (hx1lt a ⟨3, by decide, ha⟩) (by omega)
    · rcases hgrowO a ha with h1 | h1
      · exact absurd (hx1lt a ⟨4, by decide, h1⟩) (by omega)
      · omega
    · exact absurd (hx1lt a ⟨5, by decide, ha⟩) (by omega)
  refine ⟨_, hf, .returned oR.value, st', cst, x', hrun, hRS.1 hrepR, ?_, ?_, ?_,
    ⟨outEd, ?_, hEdApply, ⟨hEdW, hEdU⟩, hEdFB⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [Outcome.value.eq_1]
  · rw [hU0, hU1]
    exact smallBatchAt_of_agree hUSO fun a h1 h2 => by
      rw [hkeepS_hi a (by omega), hkeepR_hi a (by omega) (by omega)]
  · rw [hU0]; omega
  · rw [hU0, hU1]; omega
  · rw [hU2, hU3]
    exact ordEditsAt_of_agree hEdAt fun a h1 h2 => by
      rw [hkeepS_hi a (by omega), hkeepR_hi a (by omega) (by omega)]
  · rw [hU2]; omega
  · rw [hU2, hU3]; omega
  · rw [hRe0, hRe1, readList_of_agree (hfreeKeep (by omega) hreembFree)]
    exact hreembL
  · rw [hRe0]; omega
  · rw [hRe0, hRe1]; have := hreembFree.1; omega
  · omega
  · unfold asmBrStepSpace; omega
  · rw [hmem']; exact zeroFrom_asmBrStepCopy hzR (by omega) (by omega)
  · intro a ha hna hno hnr
    rw [hkeepS a hno hnr, hfrR a (by omega) (fun hr => hna ⟨1, by decide, hr⟩)]
    exact hkeepCO a ha hna
  · exact hfoot'
  · intro t ht
    rw [hU3] at ht
    rw [hU2, hkeepS_hi _ (by omega), hkeepR_hi _ (by omega) (by omega)]
    exact hEdWordsLt t ht
  · intro a ha1 ha2
    rw [hU0] at ha1
    rw [hU0, hU1] at ha2
    exact hfoot_no_mid a (by omega) (by omega)
  · intro a ha1 ha2
    rw [hU2] at ha1
    rw [hU2, hU3] at ha2
    exact hfoot_no_mid a (by omega) (by omega)
  · rw [hU3]
    have hEd3 : stO.mem (oC.value + 3) ≤ 5 * ordEditsEnc outEd + 1 := hEdAt.2.2
    have hEdEnc' : ordEditsEnc outEd ≤ 2 * tr.S_cur.batchEnc info.U_S + T₀.length := hEdEnc
    omega
  · rw [hphi']
    omega

end MinCostFlow.SparseCore.Program
