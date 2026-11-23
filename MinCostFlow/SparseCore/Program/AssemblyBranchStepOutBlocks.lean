module

public import MinCostFlow.SparseCore.Program.OutProcs
public import MinCostFlow.SparseCore.Program.OutEditsBlocks

/-!
# Block-aligned output-step statement for piece P7 (`AssemblyBranchStepOutBlocks`)

Strengthens `sig_outStepSmall_runs` (`OutStepSpecSmall.lean`) with `OrdEditsForBatch st.S_cur
info.U_S edits` in the postcondition, without editing any `Out*.lean` file. The proof runs
`osStep_runs` (`OutStepJoin.lean`) identically to `sig_outStepSmall_runs_of`
(`OutStepSmallProof.lean`) and invokes `outStepEditsSmall_post_blocks` (`OutEditsBlocks.lean`)
instead of `outStepEditsSmall_post`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

/-- **Statement of P7's compact output step with block alignment** (`OrdEditsForBatch` on the
written output order edits for `st.S_cur` and `info.U_S`). Identical to `sig_outStepSmall_runs`
with one extra conjunct in the postcondition. -/
def sig_outStepSmall_blocks_runs (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (outStepIdx : ℕ → ℕ) : Prop :=
  ∃ mul : ℕ, ∀ (S : OutTourSpec) (w vCap eCap : ℕ) (p : Program) (b nm sm fm lm : ℕ),
    HasOutProcs p b nm sm fm lm → (vCap + eCap + 2) ^ 2 < 2 ^ w →
    ∀ (T : OutTourAt S w vCap eCap p nm sm fm lm) (L : ℕ)
      (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
      (Ys : List (List End)) (T₀ : List ℕ)
      (outH tourH delPtr splitPtr insPtr rotPtr h g : ℕ)
      (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      let info := stepBundleTree sparsify st U ord ord'
      let avoid : ℕ → Prop := fun a =>
        (outGraphRep vCap eCap).foot outH g a ∨ T.rep.foot tourH tx a
      let n := st.S_cur.batchEnc info.U_S + (Ys.map List.length).sum + T₀.length + 1
      OutStepReady sparsify st U ord ord' →
      OutFlagsOk sparsify st U ord ord' vCap →
      (∀ v ∈ info.state.cs.RF.R, v < vCap) → (∀ e ∈ info.state.S_cur.E, e < eCap) →
      (∃ E₀ : Finset ℕ, outKeep sparsify st U ord ord' ⊆ E₀ ∧ E₀ ⊆ st.S_cur.E ∧
        OutMarksOf s (outCoreOrder info.state ord') E₀) →
      (outGraphRep vCap eCap).rep outH st.S_cur g mem → T.rep.rep tourH s tx mem →
      OutStepInAt mem delPtr splitPtr insPtr h avoid sparsify st U ord ord' Ys →
      mem rotPtr = T₀.length → ListAt mem (rotPtr + 1) T₀ →
      OutCellsFree rotPtr (1 + T₀.length) h avoid →
      T₀.Nodup → (∀ v ∈ T₀, v < vCap) → OutRotCover sparsify st U ord ord' T₀ →
      (∀ a ∈ [outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h], a < 2 ^ w) →
      (∀ a, (outGraphRep vCap eCap).foot outH g a → a < h) →
      (∀ a, T.rep.foot tourH tx a → a < h) →
      (∀ a, (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a) →
      ZeroFrom mem h → h + outStepSpace S vCap eCap < 2 ^ w →
      ∃ body, p.procs[outStepIdx b]? = some body ∧ ∃ o st' c tx' s',
        Runs w p ω body
          (startState [outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h] mem pos) o st' c ∧
        (outGraphRep vCap eCap).rep outH info.state.S_cur g st'.mem ∧
        T.rep.rep tourH s' tx' st'.mem ∧
        OutMarksOf s' (outCoreOrder info.state ord') info.state.S_cur.E ∧
        SmallBatchAt st'.mem (st'.mem h) st.S_cur info.U_S (st'.mem (h + 1)) ∧
        (∃ edits : List OrdEdit, OrdEditsAt st'.mem (st'.mem (h + 2)) edits (st'.mem (h + 3)) ∧
          applyOrdEdits (st.outOrder ord) edits = info.state.outOrder ord' ∧
          ordEditsEnc edits ≤ 2 * st.S_cur.batchEnc info.U_S + T₀.length ∧
          OrdEditsWithin vCap eCap edits ∧ OrdEditsUniqueWithin vCap eCap (st.outOrder ord) edits ∧
          OrdEditsForBatch st.S_cur info.U_S edits) ∧
        (∀ t < st'.mem (h + 3), st'.mem (st'.mem (h + 2) + t) < 2 ^ w) ∧
        h + 4 ≤ st'.mem h ∧ st'.mem h + st'.mem (h + 1) ≤ st'.mem (h + 2) ∧
        st'.mem (h + 2) + st'.mem (h + 3) ≤ o.value ∧
        o.value ≤ h + outStepSpace S vCap eCap ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a →
          st'.mem a = mem a) ∧
        (∀ a, T.rep.foot tourH tx' a →
          T.rep.foot tourH tx a ∨ (st'.mem (h + 2) + st'.mem (h + 3) ≤ a ∧ a < o.value)) ∧
        c + T.rep.phi tourH tx' st'.mem ≤
          mul * (S.mul + 1) * n * ordStoreLog eCap + T.rep.phi tourH tx mem

/-- **The output step meets `sig_outStepSmall_blocks_runs`** when `outStepBody` and its helper
procedures are in place (same proof as `sig_outStepSmall_runs_of`, using
`outStepEditsSmall_post_blocks`). -/
theorem sig_outStepSmall_blocks_runs_of (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (idx au gd flt wk : ℕ → ℕ)
    (hH : ∀ p b nm sm fm lm, HasOutProcs p b nm sm fm lm →
      p.procs[idx b]? = some (outStepBody nm sm fm (au b) (gd b) (flt b) (wk b)) ∧
      (∀ w vCap eCap G H u len,
        MeetsContract w p (au b) (dgApplyUpdateContract w vCap eCap G H u len)) ∧
      (∀ w vCap eCap G, MeetsContract w p (gd b) (dgGetDegContract w vCap eCap G)) ∧
      p.procs[flt b]? = some outFilterBody ∧ p.procs[wk b]? = some outWalkBody) :
    sig_outStepSmall_blocks_runs HasOutProcs idx := by
  refine ⟨5000, ?_⟩
  intro S w vCap eCap p b nm sm fm lm hP hw T L sparsify st U ord ord' Ys T₀ outH tourH delPtr
    splitPtr insPtr rotPtr h g s tx mem pos ω
  dsimp only
  intro hready hflags hR hE' hmk hrepG hrepT hIn hcnt hT hrfree hTnd hTv hcov hargs hfootG
    hfootT hdisj hz hspace
  obtain ⟨hidx, hau, hgd, hflt, hwk⟩ := hH p b nm sm fm lm hP
  refine ⟨_, hidx, ?_⟩
  obtain ⟨hdel, hdfree, hsl, hins, hifree⟩ := hIn
  obtain ⟨E₀, hE₀_lo, hE₀_hi, hmk⟩ := hmk
  have hS₀cap : ∀ e ∈ st.S_cur.E, e < eCap := hrepG.2.2.2.2.1
  obtain ⟨-, hvD, hvP, hvI⟩ := outStep_valid sparsify st U ord ord' hready
  have hS₀val : st.S_cur.IsValid := hrepG.2.2.1
  have hGv := isValid_applyBatch _ hS₀val hvD
  obtain ⟨hcap, hpl, hEp⟩ := outStep_splits_caps sparsify st U ord ord' hready hR hS₀cap
  have hdsub : ∀ e ∈ outDelList sparsify st U ord ord', e ∈ st.S_cur.E := fun e he =>
    (Finset.mem_sdiff.mp ((Finset.mem_sort _).mp he)).1
  have hinsE : ∀ e ∈ outInsList sparsify st U ord ord',
      e ∈ (stepBundleTree sparsify st U ord ord').state.S_cur.E ∧
        e ∉ outKeep sparsify st U ord ord' := fun e he =>
    Finset.mem_sdiff.mp ((Finset.mem_sort _).mp he)
  have hvI' : ((st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).applyBatch
      (outSplitBatch sparsify st U ord ord')).BatchIsValid
      ((outInsList sparsify st U ord ord').map fun e =>
        Update.insert e ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e))
          ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.head e))) := by
    have h := hvI; rw [applyBatch_append] at h; exact h
  have hS'eq : (stepBundleTree sparsify st U ord ord').state.S_cur =
      ((st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).applyBatch
        (outSplitBatch sparsify st U ord ord')).applyBatch
        ((outInsList sparsify st U ord ord').map fun e =>
          Update.insert e ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e))
            ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.head e))) := by
    rw [outStep_S_eq, applyBatch_append]; rfl
  have hS'val : (stepBundleTree sparsify st U ord ord').state.S_cur.IsValid := by
    rw [hS'eq]; exact isValid_applyBatch _ (isValid_applyBatch _ hGv hvP) hvI'
  have hV' := outStep_V sparsify st U ord ord' hready
  have hends := outStep_ins_ends sparsify st U ord ord'
  have hsrc : ∀ e ∈ outInsList sparsify st U ord ord',
      (stepBundleTree sparsify st U ord ord').state.S_cur.src (e, true) =
        (stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e) ∧
      (stepBundleTree sparsify st U ord ord').state.S_cur.src (e, false) =
        (stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.head e) := by
    intro e he; simp only [MGraph.src, ↓reduceIte, Bool.false_eq_true]; exact hends e he
  have hcord : ∀ e ∈ outInsList sparsify st U ord ord',
      (e, true) ∈ outCoreOrder (stepBundleTree sparsify st U ord ord').state ord'
        ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e)) ∧
      (e, false) ∈ outCoreOrder (stepBundleTree sparsify st U ord ord').state ord'
        ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.head e)) := by
    intro e he
    have h1 := outStep_cord_mem sparsify st U ord ord' hready e (hinsE e he).1 true
    have h2 := outStep_cord_mem sparsify st U ord ord' hready e (hinsE e he).1 false
    rw [(hsrc e he).1] at h1; rw [(hsrc e he).2] at h2; exact ⟨h1, h2⟩
  have hival : ∀ j (hj : j < (outInsList sparsify st U ord ord').length),
      (((st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).applyBatch
        (outSplitBatch sparsify st U ord ord')).applyBatch
        (((outInsList sparsify st U ord ord').take j).map fun e =>
          Update.insert e ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e))
            ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.head e)))).UpdateIsValid
        (.insert (outInsList sparsify st U ord ord')[j]
          ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.tail
              (outInsList sparsify st U ord ord')[j]))
          ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.head
              (outInsList sparsify st U ord ord')[j]))) := by
    intro j hj
    have h := outBatchIsValid_get _ hvI' j (by rw [List.length_map]; exact hj)
    simp only [← List.map_take, List.getElem_map] at h; exact h
  obtain ⟨o, st', c, tx', s₂, hrun, hrepG', hrepT', hmk₂, hbatch, hedits, htags, h1, h2, h3, h4, h5,
      h6, h7, hcost⟩ :=
    osStep_runs (nm := nm) (sm := sm) (fm := fm) (ω := ω) (pos := pos)
      ⟨outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h, g, (vCap + 1) * (eCap + 1) * 16⟩
      (hau w vCap eCap) (hgd w vCap eCap) hflt hwk hw rfl
      (delL := outDelList sparsify st U ord ord') (insL := outInsList sparsify st U ord ord')
      (P := outSplitBatch sparsify st U ord ord') (keep := outKeep sparsify st U ord ord')
      (cord := outCoreOrder (stepBundleTree sparsify st U ord ord').state ord')
      hrepG hrepT hmk ⟨hE₀_lo, hE₀_hi⟩ hargs hfootG hfootT hdisj hz hspace hdel hdfree
      (Finset.sort_nodup _ _) hdsub (fun e he hE b => (hflags e (hdsub e he) b).1 hE)
      (fun e he hE b => (hflags e (hdsub e he) b).2 hE)
      (outStep_keep_eq sparsify st U ord ord') hsl hGv hvP (restrictSplits_isSplit _ _) hcap hpl
      hEp hins hifree (Finset.sort_nodup _ _) hival
      (fun e he => hE' e (hinsE e he).1)
      (fun e he => by
        have hv := hS'val e (hinsE e he).1
        rw [hV'] at hv; rw [← (hends e he).1, ← (hends e he).2]
        exact ⟨hR _ hv.1, hR _ hv.2⟩)
      hcord hcnt hT hrfree hTnd hTv
  have hEeq : outKeep sparsify st U ord ord' ∪ (outInsList sparsify st U ord ord').toFinset =
      (stepBundleTree sparsify st U ord ord').state.S_cur.E := by
    ext f; rw [Finset.mem_union, List.mem_toFinset, outStep_newE sparsify st U ord ord' f]
  obtain ⟨hIE, hmk'⟩ := insEditsTour_eq
    (outOrder_eq_filter (stepBundleTree sparsify st U ord ord').state ord')
    (outInsList sparsify st U ord ord') s₂ (outKeep sparsify st U ord ord')
    (Finset.sort_nodup _ _) (fun e he => (hinsE e he).2) (outStep_newE sparsify st U ord ord')
    hsrc hcord hmk₂
  have hml : (insTourAfter s₂ (outInsList sparsify st U ord ord')).markedList =
      (stepBundleTree sparsify st U ord ord').state.outOrder ord' := by
    rw [markedList_eq_of_marks hmk', hEeq]; funext v; exact (outOrder_eq_filter _ _ v).symm
  have hedits_eq : outStepEditsSmall sparsify st U ord ord' T₀ =
      (outDelList sparsify st U ord ord').map OrdEdit.dropEdge ++
        outPrefixEditsOn (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map
          Update.delete)) (outSplitBatch sparsify st U ord ord') ++
        insEditsTour (fun e => (stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e))
          (fun e => (stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.head e)) s₂
          (outInsList sparsify st U ord ord') ++
        outRotateEdits (insTourAfter s₂ (outInsList sparsify st U ord ord')).markedList T₀ := by
    rw [hml, hIE]
    show outPrefixEditsOn st.S_cur ((outDelList sparsify st U ord ord').map Update.delete ++
        outSplitBatch sparsify st U ord ord') ++ _ ++ _ = _
    rw [outPrefixEditsOn_dels_append]; rfl
  obtain ⟨happly, henc, hwithin, hunique, hblocks⟩ :=
    outStepEditsSmall_post_blocks sparsify st U ord ord' T₀ hready hR hS₀cap hE' hTv hcov
  have hBE : st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S =
      (outDelList sparsify st U ord ord').length +
        (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).batchEnc
          (outSplitBatch sparsify st U ord ord') +
        (outInsList sparsify st U ord ord').length := by
    rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_dels]
    simp only [outInsBatch]; rw [batchEnc_inserts]
  refine ⟨o, st', c, tx', insTourAfter s₂ (outInsList sparsify st U ord ord'), hrun, ?_, hrepT',
    ?_, ?_, ⟨outStepEditsSmall sparsify st U ord ord' T₀, ?_, happly, henc, hwithin, hunique,
      hblocks⟩, ?_,
    h1, h2, h3, h4, h5, h6, h7, ?_⟩
  · rw [hS'eq]; exact hrepG'
  · rw [← hEeq]; exact hmk'
  · rw [outStep_batch_eq]; exact hbatch
  · rw [hedits_eq]; exact hedits
  · have h4w : 4 < 2 ^ w := by
      have : 4 ≤ (vCap + eCap + 2) ^ 2 := by
        have := Nat.pow_le_pow_left (show 2 ≤ vCap + eCap + 2 by omega) 2
        omega
      omega
    have hVlt : vCap < 2 ^ w := by
      have := Nat.le_self_pow (show 2 ≠ 0 by decide) (vCap + eCap + 2); omega
    have hElt : 2 * eCap < 2 ^ w := by
      have h1 : 2 * eCap ≤ (vCap + eCap + 2) * (vCap + eCap + 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [← Nat.pow_two] at h1
      omega
    have heditAt' : OrdEditsAt st'.mem (st'.mem (h + 2))
        (outStepEditsSmall sparsify st U ord ord' T₀) (st'.mem (h + 3)) := by
      rw [hedits_eq]; exact hedits
    have htags' : EditsTagsLe4 st'.mem (outStepEditsSmall sparsify st U ord ord' T₀).length
        (st'.mem (h + 2) + 1) := by
      rw [hedits_eq]; exact htags
    exact ordEditsAt_words_lt heditAt' htags' hwithin h4w hVlt hElt
      (lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) (h3.trans h4)) hspace)
  · rw [hBE]; exact hcost

/-- **P7's block `OutProcsAt` meets `sig_outStepSmall_blocks_runs`.** -/
theorem sig_outStepSmall_blocks_runs_outProcs :
    sig_outStepSmall_blocks_runs OutProcsAt outIdxStep :=
  sig_outStepSmall_blocks_runs_of OutProcsAt outIdxStep (fun b => b + 17 + dgIdxApplyUpdate)
    (fun b => b + 7 + dgIdxGetDeg) (fun b => b + 3) (fun b => b + 4)
    fun _ _ _ _ _ _ h => by
      obtain ⟨-, hE, hO, hS, hB⟩ := h.parts
      exact ⟨h.main.2.2.1, fun _ _ _ _ _ _ _ => dgApplyUpdate_meetsContract hB hE hS hO,
        fun _ _ _ _ => dgGetDeg_meetsContract hO, h.main.2.2.2.1, h.main.2.2.2.2⟩

end MinCostFlow.SparseCore.Program
