module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStepIface
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepOutBlocks

/-!
# The second call of the step of a branch: P7's output step (`AssemblyBranchStepOut`)

The step program of a branch (`asmBrStepStmt`, `AssemblyBranchStepIface.lean`) calls P7's output
step second, on the words that the branch record and the first phase left in memory. This file
shows that this call runs, with the post of `sig_outStepSmall_runs`, from the representation of the
branch before the step, the facts of the old and the new state, and the post of the first phase
(`asmBrStep_out_runs`). The steps are:
* the two handle words of the record and the output graph are unchanged by the first phase, so
  the output graph still holds the old `S_cur` (`outGraphRep_local`);
* P7's model preconditions come from the facts (`AssemblyBranchStepModel.lean`);
* the arguments are words: the handles lie in their own cells, below the end of the first call.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- **P7's output step runs as the second call of the step.** Let `x` be the concrete state of the
branch before the step, and `stC`, `oC` the state and the outcome of the first phase, which leaves
the tour at `xTour` with abstract state `sTour`. If the first phase keeps the record and the output
graph, leaves P7's input records at `h`, and puts the cells of the output graph and of the new tour
below `oC.value`, then P7's step runs on the handle words of the record, the four words at `h` and
`oC.value`, with the post of `sig_outStepSmall_runs`. The tour is any P7 tour `TT` at the caps of
the branch; the step takes P7's view of P2's tour (`AsmBrOutProj`). -/
theorem asmBrStep_out_runs {HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop} {idx : ℕ → ℕ}
    (hsig : sig_outStepSmall_blocks_runs HasOutProcs idx) :
    ∃ mulOut : ℕ, ∀ {OS : OutTourSpec} {w : ℕ} {p : Program} {nm sm fm lm : ℕ}
      {TR : ℕ → ℕ → DSRep AsmTourAbs}
      {depth : ℕ} (X : DSRep (AsmBranchAbs depth)) (P L capExp : ℕ) (bOut : ℕ)
      (impl : SparsifyImpl) (vC eC b h : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (U : List Update) (ed : List OrdEdit) (x : AsmBrConc TR X.τ)
      (TT : OutTourAt OS w x.vCap x.eCap p nm sm fm lm) (mem : ℕ → ℕ) (stC : State)
      (oC : Outcome) (sTour : OutTourAbs) (xTour : TT.rep.τ)
      (Ys : List (List End)) (T₀ : List ℕ) (pos : ℕ) (ω : ℕ → Bool),
      let ord' := applyOrdEdits ord ed
      let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
        fun _ => canonicalSparsify impl
      let info := stepBundleTree sparsify tr U ord ord'
      let avoid : ℕ → Prop := fun a =>
        (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a ∨
          TT.rep.foot x.tourH xTour a
      HasOutProcs p bOut nm sm fm lm →
      (∀ tourH (tx : TT.rep.τ), TT.rep.foot tourH tx tourH) →
      (x.vCap + x.eCap + 2) ^ 2 < 2 ^ w →
      AsmBrRepAt TR X P L capExp b ⟨tr, ord, vC, eC⟩ x mem →
      AsmBrModelFacts impl vC eC tr ord →
      AsmBrModelFacts impl x.vCap x.eCap info.state ord' →
      tr.cs.G.BatchIsValid U → OrderedBatch tr.cs.G U ord ord' →
      (∀ a, asmBrPart X b x 0 a ∨ asmBrPart X b x 3 a → stC.mem a = mem a) →
      TT.rep.rep x.tourH sTour xTour stC.mem →
      (∃ E₀ : Finset ℕ, outKeep sparsify tr U ord ord' ⊆ E₀ ∧ E₀ ⊆ tr.S_cur.E ∧
        OutMarksOf sTour (outCoreOrder info.state ord') E₀) →
      OutStepInAt stC.mem (stC.mem (h + ASM_ST_DEL)) (stC.mem (h + ASM_ST_SPLIT))
        (stC.mem (h + ASM_ST_INS)) oC.value avoid sparsify tr U ord ord' Ys →
      stC.mem (stC.mem (h + ASM_ST_ROT)) = T₀.length →
      ListAt stC.mem (stC.mem (h + ASM_ST_ROT) + 1) T₀ →
      OutCellsFree (stC.mem (h + ASM_ST_ROT)) (1 + T₀.length) oC.value avoid →
      T₀.Nodup → (∀ v ∈ T₀, v < x.vCap) → OutRotCover sparsify tr U ord ord' T₀ →
      (∀ i < ASM_ST_SIZE, stC.mem (h + i) < 2 ^ w) →
      (∀ a, asmBrPart X b x 3 a → a < oC.value) →
      (∀ a, TT.rep.foot x.tourH xTour a → a < oC.value) →
      (∀ a, asmBrPart X b x 3 a → ¬ TT.rep.foot x.tourH xTour a) →
      ZeroFrom stC.mem oC.value → oC.value + outStepSpace OS x.vCap x.eCap < 2 ^ w →
      ∃ body, p.procs[idx bOut]? = some body ∧ ∃ o st' c tx' s',
        Runs w p ω body
          (startState [stC.mem (b + ASM_BR_OUT), stC.mem (b + ASM_BR_TOUR),
            stC.mem (h + ASM_ST_DEL), stC.mem (h + ASM_ST_SPLIT), stC.mem (h + ASM_ST_INS),
            stC.mem (h + ASM_ST_ROT), oC.value] stC.mem pos) o st' c ∧
        (outGraphRep x.vCap x.eCap).rep x.outH info.state.S_cur x.gOut st'.mem ∧
        TT.rep.rep x.tourH s' tx' st'.mem ∧
        OutMarksOf s' (outCoreOrder info.state ord') info.state.S_cur.E ∧
        SmallBatchAt st'.mem (st'.mem oC.value) tr.S_cur info.U_S (st'.mem (oC.value + 1)) ∧
        (∃ edits : List OrdEdit,
          OrdEditsAt st'.mem (st'.mem (oC.value + 2)) edits (st'.mem (oC.value + 3)) ∧
          applyOrdEdits (tr.outOrder ord) edits = info.state.outOrder ord' ∧
          ordEditsEnc edits ≤ 2 * tr.S_cur.batchEnc info.U_S + T₀.length ∧
          OrdEditsWithin x.vCap x.eCap edits ∧
          OrdEditsUniqueWithin x.vCap x.eCap (tr.outOrder ord) edits ∧
          OrdEditsForBatch tr.S_cur info.U_S edits) ∧
        (∀ t < st'.mem (oC.value + 3), st'.mem (st'.mem (oC.value + 2) + t) < 2 ^ w) ∧
        oC.value + 4 ≤ st'.mem oC.value ∧
        st'.mem oC.value + st'.mem (oC.value + 1) ≤ st'.mem (oC.value + 2) ∧
        st'.mem (oC.value + 2) + st'.mem (oC.value + 3) ≤ o.value ∧
        o.value ≤ oC.value + outStepSpace OS x.vCap x.eCap ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < oC.value, ¬ (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a →
          ¬ TT.rep.foot x.tourH xTour a → st'.mem a = stC.mem a) ∧
        (∀ a, TT.rep.foot x.tourH tx' a →
          TT.rep.foot x.tourH xTour a ∨
            (st'.mem (oC.value + 2) + st'.mem (oC.value + 3) ≤ a ∧ a < o.value)) ∧
        c + TT.rep.phi x.tourH tx' st'.mem ≤
          mulOut * (OS.mul + 1) *
            (tr.S_cur.batchEnc info.U_S + (Ys.map List.length).sum + T₀.length + 1) *
            ordStoreLog x.eCap + TT.rep.phi x.tourH xTour stC.mem := by
  obtain ⟨mulOut, hmul⟩ := hsig
  refine ⟨mulOut, ?_⟩
  intro OS w p nm sm fm lm TR depth X P L capExp bOut impl vC eC b h tr ord U ed x TT mem stC oC
    sTour xTour Ys T₀ pos ω ord' sparsify info avoid hHas hTh hwcap hrep hold hnew hBU hord hfr
    hrepT hmk hIn hrot1 hrot2 hrfree hTnd hTv hcov hwords hOlt hTlt hOT hz hsp
  obtain ⟨-, -, hOw, hTw, -, -, -, -, -, -, -, -, -, -, -, -, -, hrepO, -⟩ := hrep
  -- the handle words and the output graph are unchanged by the first phase
  have hOw' : stC.mem (b + ASM_BR_OUT) = x.outH := by
    rw [hfr _ (Or.inl ⟨by omega, by simp [ASM_BR_OUT, ASM_BR_SIZE]⟩)]; exact hOw
  have hTw' : stC.mem (b + ASM_BR_TOUR) = x.tourH := by
    rw [hfr _ (Or.inl ⟨by omega, by simp [ASM_BR_TOUR, ASM_BR_SIZE]⟩)]; exact hTw
  have hrepO' : (outGraphRep x.vCap x.eCap).rep x.outH tr.S_cur x.gOut stC.mem :=
    ((outGraphRep_local x.vCap x.eCap) x.outH tr.S_cur x.gOut mem stC.mem
      (fun a ha => (hfr a (Or.inr ha)).symm)).1 hrepO
  -- the model preconditions
  have hready := asmBr_outStepReady sparsify hold hnew hBU hord
  have hflags := asmBr_outFlagsOk sparsify hold hnew hBU hord
  have hR := asmBr_newRoots_lt sparsify hnew
  have hE' := asmBr_newOut_lt sparsify hnew
  -- the arguments are words
  have hwlt : oC.value < 2 ^ w := by omega
  have hargs : ∀ a ∈ [x.outH, x.tourH, stC.mem (h + ASM_ST_DEL), stC.mem (h + ASM_ST_SPLIT),
      stC.mem (h + ASM_ST_INS), stC.mem (h + ASM_ST_ROT), oC.value], a < 2 ^ w := by
    have h0 : x.outH < oC.value := hOlt _ (Or.inl rfl)
    have h1 : x.tourH < oC.value := hTlt _ (hTh _ _)
    have h2 := hwords ASM_ST_DEL (by decide)
    have h3 := hwords ASM_ST_SPLIT (by decide)
    have h4 := hwords ASM_ST_INS (by decide)
    have h5 := hwords ASM_ST_ROT (by decide)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [hOw', hTw']
  exact hmul OS w x.vCap x.eCap p bOut nm sm fm lm hHas hwcap TT depth sparsify
    tr U ord ord' Ys T₀ x.outH x.tourH _ _ _ _ oC.value x.gOut sTour xTour stC.mem pos ω hready
    hflags hR hE' hmk hrepO' hrepT hIn hrot1 hrot2 hrfree hTnd hTv hcov hargs hOlt hTlt hOT hz hsp

end MinCostFlow.SparseCore.Program
