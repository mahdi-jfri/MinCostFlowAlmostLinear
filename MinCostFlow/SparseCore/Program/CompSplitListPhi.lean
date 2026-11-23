module

public import MinCostFlow.SparseCore.Program.CompSplitListModel
public import MinCostFlow.SparseCore.Program.CompInitProcs
public import MinCostFlow.SparseCore.Program.CompReadout
public import MinCostFlow.SparseCore.Program.CompExport
import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Tactic.Linarith

/-!
# Split-List Potential and Full Data-Structure Specification (`CompSplitListPhi`)

Extends `compLSFRep` and `compLSFDSFull` with the amortized potential `compSplitPhi` and the
per-branch canonical split-list output `CompSplitListAt` in `op 0`:

* `compSplitPhi`: `2000 * (Nat.log 2 (x.m0Total + 2) + 1) * ∑_{ec, j} F_{ec,j}.m`, read directly
  from each LSF window's `dgF.m` slot (hence 100% local to `compFoot b x`).
* `compPhiFull := compPhi + compSplitPhi` and `compLSFRepFull` with `compLSFRepFull_local`.
* `compSplitPhi_eq_sum_dirty`, `compSplitPhi_init_le`, and `compSplitPhi_step_drop`.
* `compBatchSpaceFull`, `compBatchUpdMulFull`, `CompBatchPostFull`, and `compLSFDSFullWithSplits`.
* Direct lifts of `init` and `op 1..6` (`compLSFDS_init`, `compLSFDS_op1..5`, `compLSFDS_op6`) to
  `compLSFRepFull` and `compLSFDSFullWithSplits`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Amortized split-list potential `compSplitPhi` and `compLSFRepFull` -/

/-- Amortized potential paying for canonical split-list extraction in `op 0`: reads each edgeful
window's forest edge count `dgF.m` inside `[b, x.endAddr)` and scales by
`2000 * (Nat.log 2 (x.m0Total + 2) + 1)`. -/
noncomputable def compSplitPhi (k b : ℕ) (x : CompLSFMeta k) (mem : ℕ → ℕ) : ℕ :=
  2000 * (Nat.log 2 (x.m0Total + 2) + 1) *
    (Finset.univ.sum fun ec : Fin x.numEdgeful =>
      Finset.univ.sum fun j : Fin k =>
        let hWin := x.winHandle ec j
        let xWin := x.winConc ec j
        if b ≤ hWin ∧ xWin.endAddr hWin ≤ x.endAddr then
          mem (lsfDgFPtr hWin xWin.vCap xWin.eCap xWin.tM + dgMOff)
        else 0)

/-- Combined amortized potential for `compLSFDSFullWithSplits`. -/
noncomputable def compPhiFull (k b : ℕ) (x : CompLSFMeta k) (mem : ℕ → ℕ) : ℕ :=
  compPhi b x mem + compSplitPhi k b x mem

/-- `DSRep (CompLSFFamily k)` with `compPhiFull` (identical footprint and `rep` to `compLSFRep`). -/
noncomputable def compLSFRepFull (W : LSFWindowImpl) (k : ℕ) : DSRep (CompLSFFamily k) where
  τ := CompLSFMeta k
  foot := compFoot
  rep b S x mem := CompLSFRepAt W k b S x mem
  phi := compPhiFull k

lemma compSplitPhi_congr {k b : ℕ} {x : CompLSFMeta k} {mem₁ mem₂ : ℕ → ℕ}
    (hag : ∀ a, b ≤ a → a < x.endAddr → mem₁ a = mem₂ a) :
    compSplitPhi k b x mem₁ = compSplitPhi k b x mem₂ := by
  unfold compSplitPhi
  congr 1
  refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  split_ifs with h
  · have hlt : lsfDgFPtr (x.winHandle ec j) (x.winConc ec j).vCap (x.winConc ec j).eCap (x.winConc ec j).tM + dgMOff <
        (x.winConc ec j).endAddr (x.winHandle ec j) := by
      dsimp only [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr,
        lsfHdrSize, dgMOff, dynGraphSize]
      omega
    have hge : x.winHandle ec j ≤
        lsfDgFPtr (x.winHandle ec j) (x.winConc ec j).vCap (x.winConc ec j).eCap (x.winConc ec j).tM + dgMOff := by
      dsimp only [lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr, lsfHdrSize, dgMOff]; omega
    exact hag _ (le_trans h.1 hge) (lt_of_lt_of_le hlt h.2)
  · rfl

theorem compLSFRepFull_local (W : LSFWindowImpl) (k : ℕ) : (compLSFRepFull W k).Local := by
  intro b S x mem₁ mem₂ hag
  have hloc := compLSFRep_local W k b S x mem₁ mem₂ hag
  exact ⟨hloc.1, congrArg₂ (· + ·) hloc.2 (compSplitPhi_congr fun a h1 h2 => hag a ⟨h1, h2⟩)⟩

lemma compSplitPhi_eq_sum_dirty {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {touched : List ℕ} {mem : ℕ → ℕ}
    (hrep : CompLSFRepDirty W k b S x touched mem) :
    compSplitPhi k b x mem =
      2000 * (Nat.log 2 (x.m0Total + 2) + 1) * (Finset.univ.sum fun j : Fin k => (S j).RF.F.m) := by
  classical
  obtain ⟨hk, _, _, _, _, _, _, _, _, hTE, _, ⟨ℓ₀, hBr⟩, _, hT, hCompTbl, hEf, _, _, _, _, _, _, hWins, _⟩ := hrep
  have hb_le_te : b ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize]; omega
  unfold compSplitPhi
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsum_ec : (Finset.univ.sum fun ec : Fin x.numEdgeful =>
      if b ≤ x.winHandle ec j ∧ (x.winConc ec j).endAddr (x.winHandle ec j) ≤ x.endAddr then
        mem (lsfDgFPtr (x.winHandle ec j) (x.winConc ec j).vCap (x.winConc ec j).eCap (x.winConc ec j).tM + dgMOff)
      else 0) =
      Finset.univ.sum fun ec : Fin x.numEdgeful => ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F.m := by
    refine Finset.sum_congr rfl fun ec _ => ?_
    obtain ⟨_, hwr, _, _, _, hge, hle⟩ := hWins ec j
    have hcond : b ≤ x.winHandle ec j ∧ (x.winConc ec j).endAddr (x.winHandle ec j) ≤ x.endAddr :=
      ⟨le_trans hb_le_te hge, hle⟩
    simp only [hcond, and_self, ↓reduceIte]
    exact hwr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
  rw [hsum_ec]
  have hG0_j := (hBr j).2.1
  have hF_props := compLSF_F_eq_edgeful (hBr j).1
  have hFm_eq : (S j).RF.F.m =
      (edgefulComps (S j).G₀).sum (fun C => ((S j).compSt C).RF.F.m) := by
    change (S j).RF.F.E.card = _
    rw [hF_props.1, Finset.card_biUnion fun C₁ hC₁ C₂ hC₂ hne => hF_props.2.2.1 C₁ hC₁ C₂ hC₂ hne]
    rfl
  rw [hFm_eq]
  let f : Fin x.numEdgeful → Finset ℕ := fun ec => x.compOf (x.edgefulComp ec)
  have hf_inj : Function.Injective f := fun a b hab => Fin.ext (by
    have h1 := hT.hBij.1 hab
    have h2 := (hEf a).2
    have h3 := (hEf b).2
    rw [h1] at h2; omega)
  have hf_img : Finset.univ.image f = edgefulComps (S j).G₀ := by
    ext C
    simp only [Finset.mem_image, Finset.mem_univ, true_and, edgefulComps, Finset.mem_filter, f]
    constructor
    · rintro ⟨ec, rfl⟩
      have hmem := hT.compOf_mem (x.edgefulComp ec)
      have hm := (hEf ec).1
      exact ⟨hG0_j ▸ hmem, hG0_j ▸ hm⟩
    · rintro ⟨hC, hm⟩
      obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp (hG0_j.symm ▸ hC)
      obtain ⟨ec, _, _, hec⟩ := (hCompTbl c).2.2.2 (hG0_j.symm ▸ hm)
      exact ⟨ec, congrArg x.compOf hec⟩
  rw [← hf_img, Finset.sum_image (fun a _ b _ h => hf_inj h)]

lemma compSplitPhi_init_le {W : LSFWindowImpl} {k b : ℕ} {G₀ : MGraph} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {mem : ℕ → ℕ}
    (hrep : CompLSFRepAt W k b S x mem) (hG0 : ∀ j : Fin k, (S j).G₀ = G₀) :
    compSplitPhi k b x mem ≤ 2000 * k * G₀.m * (Nat.log 2 (G₀.m + 2) + 1) := by
  have hd := compLSFRepDirty_nil_iff.mpr hrep
  rw [compSplitPhi_eq_sum_dirty hd]
  obtain ⟨hk, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀, hBr⟩, hm0_eq, _⟩ := hrep
  have hm0 : x.m0Total = G₀.m := by rw [← hm0_eq, hG0 ⟨0, hk⟩]
  rw [hm0]
  have hsum_le : (Finset.univ.sum fun j : Fin k => (S j).RF.F.m) ≤ k * G₀.m := by
    calc (Finset.univ.sum fun j : Fin k => (S j).RF.F.m)
        ≤ Finset.univ.sum fun _ : Fin k => G₀.m :=
          Finset.sum_le_sum fun j _ => by
            have := (compLSF_F_eq_edgeful (hBr j).1).2.2.2
            rwa [hG0 j] at this
      _ = k * G₀.m := by simp
  calc 2000 * (Nat.log 2 (G₀.m + 2) + 1) * (Finset.univ.sum fun j : Fin k => (S j).RF.F.m)
      ≤ 2000 * (Nat.log 2 (G₀.m + 2) + 1) * (k * G₀.m) := Nat.mul_le_mul_left _ hsum_le
    _ = 2000 * k * G₀.m * (Nat.log 2 (G₀.m + 2) + 1) := by ring

lemma compSplitPhi_step_drop {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x x1 : CompLSFMeta k} {touched touched1 : List ℕ} {u : Update} {mem mem1 : ℕ → ℕ}
    (hrep0 : CompLSFRepDirty W k b S x touched mem)
    (hrep1 : CompLSFRepDirty W k b (fun j => compLSFStepSingle (S j) u) x1 touched1 mem1)
    (hu_val : (S ⟨0, hrep0.1⟩).G.UpdateIsValid u)
    (hm0 : x1.m0Total = x.m0Total) :
    2000 * (Nat.log 2 (x.m0Total + 2) + 1) *
        (Finset.univ.sum fun j : Fin k =>
          ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card) +
      compSplitPhi k b x1 mem1 ≤ compSplitPhi k b x mem := by
  classical
  rw [compSplitPhi_eq_sum_dirty hrep0, compSplitPhi_eq_sum_dirty hrep1, hm0]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀, hBr0⟩, _⟩ := hrep0
  have hle_j : ∀ j : Fin k,
      ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card +
        (compLSFStepSingle (S j) u).RF.F.m ≤ (S j).RF.F.m := fun j => by
    have hIj := (hBr0 j).1
    have hu_j : (S j).G.UpdateIsValid u := (hBr0 j).2.2.1.symm ▸ hu_val
    have hdec := (compLSFBatch_decremental (U := [u]) hIj ⟨hu_j, trivial⟩).1
    have hsub : (forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E ⊆
        (S j).RF.F.E \ (compLSFStepSingle (S j) u).RF.F.E := fun e he => by
      have ⟨h1, h2⟩ := Finset.mem_sdiff.mp he
      refine Finset.mem_sdiff.mpr ⟨?_, h2⟩
      cases u with
      | insert _ _ _ => exact h1
      | delete _ => exact (Finset.mem_erase.mp h1).2
      | split _ _ _ _ => exact h1
    have hcard := Finset.card_le_card hsub
    have hsdiff : ((S j).RF.F.E \ (compLSFStepSingle (S j) u).RF.F.E).card +
        (compLSFStepSingle (S j) u).RF.F.E.card = (S j).RF.F.E.card :=
      Finset.card_sdiff_add_card_eq_card hdec
    dsimp only [MGraph.m]
    omega
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hle_j j
  rw [Finset.sum_add_distrib] at hsum
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ hsum

/-! ## 2. Full data-structure specification `compLSFDSFullWithSplits` -/

/-- Constant multiplier on `k * (|U| + 1)` in `op 0` with canonical split lists. -/
def compBatchUpdMulFull : ℕ := 3000

/-- Heap space above `heap` needed by `op 0` with canonical split lists. -/
def compBatchSpaceFull (k : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let b := args.getD 0 0
  let batchPtr := args.getD 1 0
  let vCap := mem (b + compOffVCap)
  let eCap := mem (b + compOffECap)
  11 + 3 * mem batchPtr + batchMemLen mem batchPtr + 2 * eCap + 8 * vCap + k * (8 + 12 * vCap)

/-- Output-pinned version of `CompBatchPostFull` tying both the returned heap end `outEnd` and the
batch `U` explicitly to the caller's values. -/
def CompBatchPostFullAt (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ) (mem : ℕ → ℕ)
    (outEnd : ℕ) (U : List Update) (S' : CompLSFFamily k) (mem' : ℕ → ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b batchPtr heap totalWords : ℕ),
    args = [b, batchPtr, heap] ∧
    BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords ∧
    S' = compLSFBatchFamily S U ∧
    mem' heap ≤ 2 * U.length ∧
    heap + 1 + mem' heap + 2 * k ≤ outEnd ∧
    outEnd ≤ heap + compBatchSpaceFull k args mem ∧
    ZeroFrom mem' outEnd ∧
    (∃ chg : Fin k → Read.LSFChange, ∀ j : Fin k,
      let chgPtr := mem' (heap + 1 + mem' heap + j.1)
      let cuts := List.zip (chg j).fDel (chg j).roots
      Read.LSFChangeAt mem' chgPtr (chg j) ∧
      (chg j).Exact (S j).lsf (S' j).lsf ∧
      (chg j).fDel.length ≤ (chg j).roots.length ∧
      CompForestCutsValid (mem (b + compOffVCap)) (S j).RF cuts ∧
      (cuts.foldl compApplyForestCut (S j).RF).F.E = (S' j).RF.F.E ∧
      heap + 1 + mem' heap + 2 * k ≤ chgPtr ∧
      chgPtr + (chg j).words ≤ outEnd) ∧
    CompSplitListAt w k mem' (heap + 1 + mem' heap + k) outEnd
      (fun j => if hj : j < k then S ⟨j, hj⟩ else S ⟨0, hk⟩) U

/-- Extended `op 0` postcondition: satisfies every clause of `CompBatchPost` (at `heap + 1 + r`)
AND simultaneously exposes `CompSplitListAt w k mem' (heap + 1 + r + k) outEnd` right after the
`k` `LSFChangeAt` pointers, with `ZeroFrom mem' outEnd`. -/
def CompBatchPostFull (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ) (mem : ℕ → ℕ)
    (S' : CompLSFFamily k) (mem' : ℕ → ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b batchPtr heap totalWords outEnd : ℕ) (U : List Update),
    args = [b, batchPtr, heap] ∧
    BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords ∧
    S' = compLSFBatchFamily S U ∧
    mem' heap ≤ 2 * U.length ∧
    heap + 1 + mem' heap + 2 * k ≤ outEnd ∧
    outEnd ≤ heap + compBatchSpaceFull k args mem ∧
    ZeroFrom mem' outEnd ∧
    (∃ chg : Fin k → Read.LSFChange, ∀ j : Fin k,
      let chgPtr := mem' (heap + 1 + mem' heap + j.1)
      let cuts := List.zip (chg j).fDel (chg j).roots
      Read.LSFChangeAt mem' chgPtr (chg j) ∧
      (chg j).Exact (S j).lsf (S' j).lsf ∧
      (chg j).fDel.length ≤ (chg j).roots.length ∧
      CompForestCutsValid (mem (b + compOffVCap)) (S j).RF cuts ∧
      (cuts.foldl compApplyForestCut (S j).RF).F.E = (S' j).RF.F.E ∧
      heap + 1 + mem' heap + 2 * k ≤ chgPtr ∧
      chgPtr + (chg j).words ≤ outEnd) ∧
    CompSplitListAt w k mem' (heap + 1 + mem' heap + k) outEnd
      (fun j => if hj : j < k then S ⟨j, hj⟩ else S ⟨0, hk⟩) U

/-- Full 7-operation per-component dynamic LSF specification with canonical split lists in `op 0`. -/
noncomputable def compLSFDSFullWithSplits (W : LSFWindowImpl) (w k : ℕ) (G₀ : MGraph) :
    DataStructure (CompLSFFamily k) where
  initPre := (compLSFDSFull W w k G₀).initPre
  initPost := (compLSFDSFull W w k G₀).initPost
  initCost args mem :=
    (compLSFDSFull W w k G₀).initCost args mem +
      2000 * k * G₀.m * (Nat.log 2 (G₀.m + 2) + 1)
  initSpace := (compLSFDSFull W w k G₀).initSpace
  pre := (compLSFDSFull W w k G₀).pre
  post i S args mem S' mem' :=
    if i = 0 then CompBatchPostFull w k S args mem S' mem'
    else (compLSFDSFull W w k G₀).post i S args mem S' mem'
  cost i S args mem :=
    if i = 0 then
      (compLSFDSFull W w k G₀).cost 0 S args mem +
        (compBatchUpdMulFull - compBatchUpdMul) * k * (mem (args.getD 1 0) + 1)
    else (compLSFDSFull W w k G₀).cost i S args mem
  space i S args mem :=
    if i = 0 then compBatchSpaceFull k args mem
    else (compLSFDSFull W w k G₀).space i S args mem

/-! ## 3. Direct lifts of `init` and `op 1..6` to `compLSFRepFull` / `compLSFDSFullWithSplits` -/

theorem compLSFDSFullWithSplits_init {W : LSFWindowImpl} {w k bBfs bDgInit bWin : ℕ} {G₀ : MGraph}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} {p : Program}
    (hpBfs : p.procs[bBfs]? = some compBfsCompProc)
    (hpDg : ∀ {vCap eCap} (G : MGraph) (vLs : List ℕ) (eLs : List (ℕ × ℕ × ℕ)),
      MeetsContract w p bDgInit (dgInitFromListsContract w vCap eCap G vLs eLs))
    (hpWin : p.HasAt bWin (W.procs bWin))
    (hpre : (compLSFDSFullWithSplits W w k G₀).initPre args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDSFullWithSplits W w k G₀).initSpace args mem < 2 ^ w) :
    ∃ o st' c,
      Runs w p ω (compInitProc W.h bBfs bDgInit (bWin + W.initOff)) (startState args mem pos) o st' c ∧
      ∃ S' x',
        CompLSFRepAt W k (heapArg args) S' x' st'.mem ∧
        (compLSFDSFullWithSplits W w k G₀).initPost args mem S' st'.mem ∧
        (compLSFRepFull W k).Respects (fun _ => False) (heapArg args)
          ((compLSFDSFullWithSplits W w k G₀).initSpace args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + compPhiFull k (heapArg args) x' st'.mem ≤
          (compLSFDSFullWithSplits W w k G₀).initCost args mem ∧
        x'.vCap = args.getD 6 0 ∧ x'.eCap = args.getD 7 0 ∧ x'.L_w = args.getD 5 0 := by
  obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', hv', he', hlw'⟩ :=
    compLSFDS_init hpBfs hpDg hpWin hpre hargs hz hsp
  have hG0 : ∀ j : Fin k, (S' j).G₀ = G₀ := fun j => by
    have hp : S' = compLSFInitFamily W.lsfInit G₀
        (compReadLen mem (args.getD 1 0) W.h W.L_in W.P_fp G₀) k := hpost'
    rw [hp]; rfl
  have hsp_le := compSplitPhi_init_le hrep' hG0
  refine ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', ?_, hv', he', hlw'⟩
  simp only [compPhiFull, compLSFDSFullWithSplits, compLSFDSFull] at hcost' ⊢
  omega

/-- Any state-preserving operation (`S' = S`) automatically preserves `compSplitPhi` identically,
because `compSplitPhi` equals `2000 * (Nat.log 2 (G₀.m + 2) + 1) * ∑ j, (S j).RF.F.m`. -/
lemma compSplitPhi_eq_of_same_state {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x x' : CompLSFMeta k} {mem mem' : ℕ → ℕ}
    (hrep : CompLSFRepAt W k b S x mem) (hrep' : CompLSFRepAt W k b S x' mem') :
    compSplitPhi k b x' mem' = compSplitPhi k b x mem := by
  rw [compSplitPhi_eq_sum_dirty (compLSFRepDirty_nil_iff.mpr hrep'),
      compSplitPhi_eq_sum_dirty (compLSFRepDirty_nil_iff.mpr hrep)]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hm0, _⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hm0', _⟩ := hrep'
  rw [hm0'.symm.trans hm0]

/-- Generic lift of any `op i` (`1 ≤ i ≤ 6`, where `post` forces `S' = S`) from
`compLSFRep` / `compLSFDSFull` to `compLSFRepFull` / `compLSFDSFullWithSplits`. -/
theorem compLSFDSFullWithSplits_lift_readonly {W : LSFWindowImpl} {w k i b : ℕ} {G₀ : MGraph}
    {stmt : Stmt} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} {p : Program}
    (hi : i ≠ 0)
    (hrep : CompLSFRepAt W k b S x mem)
    (hrun_old :
      ∃ o st' c,
        Runs w p ω stmt (startState args mem pos) o st' c ∧
        ∃ S' x',
          CompLSFRepAt W k b S' x' st'.mem ∧
          (compLSFDSFull W w k G₀).post i S args mem S' st'.mem ∧
          S' = S ∧
          (compLSFRep W k).Respects (compFoot b x) (heapArg args)
            ((compLSFDSFull W w k G₀).space i S args mem) mem o.value b x' st'.mem ∧
          c + compPhi b x' st'.mem ≤
            (compLSFDSFull W w k G₀).cost i S args mem + compPhi b x mem) :
    ∃ o st' c,
      Runs w p ω stmt (startState args mem pos) o st' c ∧
      ∃ S' x',
        CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDSFullWithSplits W w k G₀).post i S args mem S' st'.mem ∧
        (compLSFRepFull W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDSFullWithSplits W w k G₀).space i S args mem) mem o.value b x' st'.mem ∧
        c + compPhiFull k b x' st'.mem ≤
          (compLSFDSFullWithSplits W w k G₀).cost i S args mem + compPhiFull k b x mem := by
  obtain ⟨o, st', c, hrun, S', x', hrep', hpost', rfl, hresp', hcost'⟩ := hrun_old
  have hsp_eq := compSplitPhi_eq_of_same_state hrep hrep'
  refine ⟨o, st', c, hrun, S', x', hrep', by simp [compLSFDSFullWithSplits, hi, hpost'], ?_, ?_⟩
  · simp only [compLSFDSFullWithSplits, hi, ↓reduceIte]; exact hresp'
  · simp only [compLSFDSFullWithSplits, hi, ↓reduceIte, compPhiFull]; omega

end

end MinCostFlow.SparseCore.Program
