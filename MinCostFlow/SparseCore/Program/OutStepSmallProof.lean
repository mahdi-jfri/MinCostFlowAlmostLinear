module

public import MinCostFlow.SparseCore.Program.OutStepJoin

/-!
# The output step meets its statement

This file proves `sig_outStepSmall_runs` for any program that places the body `outStepBody` at
the index of the step, with the stored-graph procedures `dgApplyUpdate` and `dgGetDeg` and the
helpers `outFilter` and `outWalk` (`sig_outStepSmall_runs_of`).

The proof gives the lists of `osStep_runs` from the model of the step: the leaving edges
`outDelList`, the restricted core splits `outSplitBatch` and the entering edges `outInsList`,
read from the input record `OutStepInAt`. The facts that the phases ask for come from the pre
and from the model facts of `OutStepJoinModel.lean`. Then the edits that the program writes are
`outStepEditsSmall`, so `outStepEditsSmall_post` gives the model part of the post.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

/-- **The output step meets `sig_outStepSmall_runs`** when the step body and the procedures it
calls are in place. -/
theorem sig_outStepSmall_runs_of (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (idx au gd flt wk : ℕ → ℕ)
    (hH : ∀ p b nm sm fm lm, HasOutProcs p b nm sm fm lm →
      p.procs[idx b]? = some (outStepBody nm sm fm (au b) (gd b) (flt b) (wk b)) ∧
      (∀ w vCap eCap G H u len,
        MeetsContract w p (au b) (dgApplyUpdateContract w vCap eCap G H u len)) ∧
      (∀ w vCap eCap G, MeetsContract w p (gd b) (dgGetDegContract w vCap eCap G)) ∧
      p.procs[flt b]? = some outFilterBody ∧ p.procs[wk b]? = some outWalkBody) :
    sig_outStepSmall_runs HasOutProcs idx := by
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
  -- the model facts
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
    have h := hvI
    rw [applyBatch_append] at h
    exact h
  have hS'eq : (stepBundleTree sparsify st U ord ord').state.S_cur =
      ((st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).applyBatch
        (outSplitBatch sparsify st U ord ord')).applyBatch
        ((outInsList sparsify st U ord ord').map fun e =>
          Update.insert e ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e))
            ((stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.head e))) := by
    rw [outStep_S_eq, applyBatch_append]
    rfl
  have hS'val : (stepBundleTree sparsify st U ord ord').state.S_cur.IsValid := by
    rw [hS'eq]
    exact isValid_applyBatch _ (isValid_applyBatch _ hGv hvP) hvI'
  have hV' := outStep_V sparsify st U ord ord' hready
  have hends := outStep_ins_ends sparsify st U ord ord'
  have hsrc : ∀ e ∈ outInsList sparsify st U ord ord',
      (stepBundleTree sparsify st U ord ord').state.S_cur.src (e, true) =
        (stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e) ∧
      (stepBundleTree sparsify st U ord ord').state.S_cur.src (e, false) =
        (stepBundleTree sparsify st U ord ord').state.cs.RF.root
          ((stepBundleTree sparsify st U ord ord').state.cs.G.head e) := by
    intro e he
    simp only [MGraph.src, ↓reduceIte, Bool.false_eq_true]
    exact hends e he
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
    rw [(hsrc e he).1] at h1
    rw [(hsrc e he).2] at h2
    exact ⟨h1, h2⟩
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
    simp only [← List.map_take, List.getElem_map] at h
    exact h
  -- the run
  obtain ⟨o, st', c, tx', s₂, hrun, hrepG', hrepT', hmk₂, hbatch, hedits, -, h1, h2, h3, h4, h5,
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
        rw [hV'] at hv
        rw [← (hends e he).1, ← (hends e he).2]
        exact ⟨hR _ hv.1, hR _ hv.2⟩)
      hcord hcnt hT hrfree hTnd hTv
  -- the edits of the program are the model's
  have hEeq : outKeep sparsify st U ord ord' ∪ (outInsList sparsify st U ord ord').toFinset =
      (stepBundleTree sparsify st U ord ord').state.S_cur.E := by
    ext f
    rw [Finset.mem_union, List.mem_toFinset, outStep_newE sparsify st U ord ord' f]
  obtain ⟨hIE, hmk'⟩ := insEditsTour_eq
    (outOrder_eq_filter (stepBundleTree sparsify st U ord ord').state ord')
    (outInsList sparsify st U ord ord') s₂ (outKeep sparsify st U ord ord')
    (Finset.sort_nodup _ _) (fun e he => (hinsE e he).2) (outStep_newE sparsify st U ord ord')
    hsrc hcord hmk₂
  have hml : (insTourAfter s₂ (outInsList sparsify st U ord ord')).markedList =
      (stepBundleTree sparsify st U ord ord').state.outOrder ord' := by
    rw [markedList_eq_of_marks hmk', hEeq]
    funext v
    exact (outOrder_eq_filter _ _ v).symm
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
    rw [outPrefixEditsOn_dels_append]
    rfl
  obtain ⟨happly, henc, hwithin, hunique⟩ :=
    outStepEditsSmall_post sparsify st U ord ord' T₀ hready hR hS₀cap hE' hTv hcov
  have hBE : st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S =
      (outDelList sparsify st U ord ord').length +
        (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).batchEnc
          (outSplitBatch sparsify st U ord ord') +
        (outInsList sparsify st U ord ord').length := by
    rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_dels]
    simp only [outInsBatch]
    rw [batchEnc_inserts]
  refine ⟨o, st', c, tx', insTourAfter s₂ (outInsList sparsify st U ord ord'), hrun, ?_, hrepT',
    ?_, ?_, ⟨outStepEditsSmall sparsify st U ord ord' T₀, ?_, happly, henc, hwithin, hunique⟩,
    h1, h2, h3, h4, h5, h6, h7, ?_⟩
  · rw [hS'eq]; exact hrepG'
  · rw [← hEeq]; exact hmk'
  · rw [outStep_batch_eq]; exact hbatch
  · rw [hedits_eq]; exact hedits
  · rw [hBE]; exact hcost

end MinCostFlow.SparseCore.Program
