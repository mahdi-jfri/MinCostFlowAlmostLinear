module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopAux
public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopPack
public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopCollectD
import Mathlib.Tactic.Ring

/-!
# Loop context, invariant, and single-iteration proof for `dsUpdateLoopStmt`

Bundles the batch-update preconditions into `UpdateLoopCtx`, defines the per-step saved-output
predicate `SavedStepAt` and loop invariant `UpdateLoopInv`, proves pure list/summation/footprint
helpers, and verifies one iteration of the `forRange` loop in `dsUpdateLoopStmt`
(`updateLoop_step_triple`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

/-! ## Pure list, permutation, and footprint helpers -/

/-- Append one element to a `Fin n`-indexed family to obtain a `Fin (n + 1)`-indexed family. -/
@[expose] def snocFin {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) : Fin (n + 1) → α :=
  fun s => if h : s.1 < n then f ⟨s.1, h⟩ else a

lemma snocFin_lt {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) (s : Fin (n + 1)) (hs : s.1 < n) :
    snocFin f a s = f ⟨s.1, hs⟩ := by
  simp [snocFin, hs]

lemma snocFin_last {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) (s : Fin (n + 1)) (hs : s.1 = n) :
    snocFin f a s = a := by
  simp [snocFin, hs]

lemma list_take_sum_succ {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    (l.take (i + 1)).sum = (l.take i).sum + l[i]'hi := by
  rw [List.take_succ_eq_append_getElem hi, List.sum_append, List.sum_singleton]

lemma list_take_sum_le (l : List ℕ) (i : ℕ) : (l.take i).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop i l, List.sum_append]
  exact Nat.le_add_right _ _

lemma list_getD_eq_getElem {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    l.getD i 0 = l[i]'hi := by
  rw [List.getD_eq_getElem _ _ hi]

lemma sum_range_le_of_le (f : ℕ → ℕ) {i m : ℕ} (him : i ≤ m) :
    ∑ r ∈ Finset.range i, f r ≤ ∑ r ∈ Finset.range m, f r :=
  Finset.sum_le_sum_of_subset (Finset.range_mono him)

lemma sum_range_add_elem_le (f : ℕ → ℕ) {r m : ℕ} (hrm : r < m) :
    (∑ s ∈ Finset.range r, f s) + f r ≤ ∑ s ∈ Finset.range m, f s := by
  rw [← Finset.sum_range_succ]
  exact sum_range_le_of_le f (Nat.succ_le_of_lt hrm)

lemma sum_fin_eq_sum_range {m : ℕ} (f : Fin m → ℕ) (g : ℕ → ℕ)
    (hfg : ∀ i : Fin m, f i = g i.1) :
    ∑ i : Fin m, f i = ∑ r ∈ Finset.range m, g r := by
  rw [← Fin.sum_univ_eq_sum_range g m]
  exact Finset.sum_congr rfl fun i _ => hfg i

lemma sum_fin_le_sum_range {m : ℕ} (f : Fin m → ℕ) (g : ℕ → ℕ)
    (hfg : ∀ i : Fin m, f i ≤ g i.1) :
    ∑ i : Fin m, f i ≤ ∑ r ∈ Finset.range m, g r := by
  rw [← Fin.sum_univ_eq_sum_range g m]
  exact Finset.sum_le_sum fun i _ => hfg i

lemma perm_flatMap_finRange_range {α : Type*} :
    ∀ {m : ℕ} (f : Fin m → List α) (g : ℕ → List α),
      (∀ i : Fin m, (f i).Perm (g i.1)) →
      ((List.finRange m).flatMap f).Perm ((List.range m).flatMap g) := by
  intro m
  induction m with
  | zero => intro f g _; simp
  | succ m ih =>
    intro f g hfg
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_singleton, List.flatMap_singleton, List.flatMap_map]
    refine List.Perm.append ?_ (hfg ⟨m, Nat.lt_succ_self m⟩)
    exact ih (fun i => f i.castSucc) g (fun i => hfg i.castSucc)

lemma applyBatch_flatMap_finRange :
    ∀ {m : ℕ} (Hs : ℕ → MGraph) (f : Fin m → List Update),
      (∀ i : Fin m, Hs (i.1 + 1) = (Hs i.1).applyBatch (f i)) →
      (Hs 0).applyBatch ((List.finRange m).flatMap f) = Hs m := by
  intro m
  induction m with
  | zero => intro Hs f _; simp [MGraph.applyBatch]
  | succ m ih =>
    intro Hs f hstep
    rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
    simp only [MGraph.applyBatch, List.foldl_append]
    have hprev : List.foldl MGraph.applyUpdate (Hs 0)
        ((List.finRange m).flatMap fun i => f i.castSucc) = Hs m :=
      ih Hs (fun i => f i.castSucc) (fun i => hstep i.castSucc)
    rw [hprev]
    exact (hstep ⟨m, Nat.lt_succ_self m⟩).symm

lemma heapFoot_append_interval {L : ℕ} {x x' : DynSpannerMeta L} {lo hi a : ℕ}
    (hiv : x'.intervals = x.intervals ++ [(lo, hi)]) :
    heapFoot x' a ↔ heapFoot x a ∨ (lo ≤ a ∧ a < hi) := by
  simp only [heapFoot, hiv, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨iv, hiv' | rfl, h1, h2⟩
    · exact Or.inl ⟨iv, hiv', h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨iv, hiv', h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨iv, Or.inl hiv', h1, h2⟩
    · exact ⟨(lo, hi), Or.inr rfl, h1, h2⟩

lemma metaFoot_lt_of_append_ge {L : ℕ} {b lo hi a : ℕ} {x x' : DynSpannerMeta L}
    (hv : x'.vCap = x.vCap) (he : x'.eCap = x.eCap)
    (hiv : x'.intervals = x.intervals ++ [(lo, hi)]) (ha : a < lo) :
    metaFoot b x' a ↔ metaFoot b x a := by
  simp only [metaFoot, hv, he, heapFoot_append_interval hiv]
  constructor
  · rintro (h | h | ⟨h1, _⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact (Nat.not_le_of_lt ha h1).elim
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

lemma not_metaFoot_of_ge {L : ℕ} {b bound a : ℕ} {x : DynSpannerMeta L}
    (hfix : b + dsFixedSize L x.vCap x.eCap ≤ bound)
    (hfoot : ∀ p, heapFoot x p → p < bound) (ha : bound ≤ a) :
    ¬ metaFoot b x a := by
  rintro (⟨_, hlt⟩ | hhf)
  · exact Nat.not_lt_of_ge (hfix.trans ha) hlt
  · exact Nat.not_lt_of_ge ha (hfoot a hhf)

lemma runState_applyBatch_take {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us U : List Update) (k₀ : ℕ)
    (hslice : ∀ i (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    ∀ i ≤ U.length,
      (runState (L := L) G₀ q sparsify us (k₀ + i)).G =
        (runState (L := L) G₀ q sparsify us k₀).G.applyBatch (U.take i) := by
  intro i
  induction i with
  | zero => intro _; simp [MGraph.applyBatch]
  | succ i ih =>
    intro hi
    have hilt : i < U.length := Nat.lt_of_succ_le hi
    have hsome : us[k₀ + i]? = some (U[i]'hilt) := hslice i hilt
    have hstepG : (runState (L := L) G₀ q sparsify us (k₀ + (i + 1))).G =
        (runState (L := L) G₀ q sparsify us (k₀ + i)).G.applyUpdate (U[i]'hilt) := by
      rw [show k₀ + (i + 1) = (k₀ + i) + 1 by omega]
      simp only [runState, hsome, step]
      split_ifs <;> rfl
    rw [hstepG, ih (Nat.le_of_lt hilt)]
    simp only [MGraph.applyBatch, List.take_succ_eq_append_getElem hilt, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

lemma list_sum_range_lens {l : List ℕ} {m : ℕ} (hl : l.length = m) :
    ∑ r ∈ Finset.range m, l.getD r 0 = l.sum := by
  subst hl
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ, ih]
    omega

/-! ## Batch-update context and loop invariant -/

/-- Bundled fixed parameters and preconditions for `dsUpdateLoopStmt`. -/
structure UpdateLoopCtx where
  G₀ : MGraph
  impl : SparsifyImpl
  mMax : ℕ
  w : ℕ
  L : ℕ
  q : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  k₀ : ℕ
  us : List Update
  U : List Update
  lens : List ℕ
  x₀ : DynSpannerMeta L
  batchPtr : ℕ
  heapStart : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hL1 : 1 ≤ L
  hq1 : 1 ≤ q
  hVG₀ : G₀.IsValid
  hGm₀ : G₀.m ≤ mMax
  hE₀_cap : ∀ e ∈ G₀.E, e < eCap
  hBV : G₀.BatchIsValid us
  hds : ∀ u' ∈ us, isDelOrSplit u'
  hslice : ∀ i (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)
  hPref₀ : ∀ s ≤ k₀, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
    (canonicalSparsify impl) us s
  hState₀ : DynSpannerStateAt L vCap eCap b mem0 x₀
    (runState (L := L) G₀ q (canonicalSparsify impl) us k₀)
  hRev₀ : RevHistoryInv G₀ q (canonicalSparsify impl) us k₀ x₀
  hfix : b + dsFixedSize L vCap eCap ≤ heapStart
  hfoot₀ : ∀ a, heapFoot x₀ a → a < heapStart
  hz₀ : ZeroFrom mem0 heapStart
  hspace : heapStart + dsUpdateLoopSpace G₀ impl mMax L q vCap eCap us U lens k₀ < 2 ^ w
  hgen : mem0 (b + dsGenOff) + dsUpdateLoopGen G₀ impl L q us U.length k₀ < 2 ^ w
  hk_w : k₀ + U.length < 2 ^ w
  hq_w : q < 2 ^ w
  hWOK : ∀ r < U.length, dsStepWordOKAt G₀ impl w L q us (k₀ + r)
  hfixB : b + dsFixedSize L vCap eCap ≤ batchPtr
  hbatch_le : batchPtr + 1 + lens.sum ≤ heapStart
  hbatch_foot : ∀ i < 1 + lens.sum, ¬ metaFoot b x₀ (batchPtr + i)
  hbatch_w : ∀ i < 1 + lens.sum, mem0 (batchPtr + i) < 2 ^ w
  hbatch_len : mem0 batchPtr = U.length
  hbatch_body : BatchBodyLensAt mem0 (batchPtr + 1)
    (runState (L := L) G₀ q (canonicalSparsify impl) us k₀).G U lens
  hbatch_cap : BatchWithinCaps vCap eCap U

namespace UpdateLoopCtx

noncomputable abbrev stAt (c : UpdateLoopCtx) (i : ℕ) : DynSpannerState c.L :=
  runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us (c.k₀ + i)

noncomputable abbrev resAt (c : UpdateLoopCtx) (i : ℕ) : StepOut c.L :=
  runStepOut (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us (c.k₀ + i)

noncomputable abbrev reembAt (c : UpdateLoopCtx) (i : ℕ) : Finset ℕ :=
  runStepReembSet (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us (c.k₀ + i)

noncomputable abbrev stepSpace (c : UpdateLoopCtx) (r : ℕ) : ℕ :=
  dsStepSpaceAt c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us (c.k₀ + r) (c.lens.getD r 0)

noncomputable abbrev stepGen (c : UpdateLoopCtx) (r : ℕ) : ℕ :=
  dsStepGenAt c.G₀ c.impl c.L c.q c.us (c.k₀ + r)

noncomputable abbrev stepCost (c : UpdateLoopCtx) (r : ℕ) : ℕ :=
  dsStepCostAt c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us (c.k₀ + r) (c.lens.getD r 0)

/-- Running upper bound on the heap cursor after `i` steps of the batch loop. -/
@[expose] noncomputable def cursorBound (c : UpdateLoopCtx) (i : ℕ) : ℕ :=
  c.heapStart + 7 + c.U.length +
  (∑ r ∈ Finset.range i, (c.stepSpace r + 7)) +
  (∑ r ∈ Finset.range i, (c.resAt r).D.card) +
  (∑ r ∈ Finset.range i, (c.reembAt r).card) +
  (c.lens.take i).sum +
  4 * (∑ r ∈ Finset.range i, (c.resAt r).UH.length)

lemma lens_length (c : UpdateLoopCtx) : c.lens.length = c.U.length :=
  c.hbatch_body.length_eq

lemma cursorBound_zero (c : UpdateLoopCtx) :
    c.cursorBound 0 = c.heapStart + 7 + c.U.length := by
  simp [cursorBound]

lemma cursorBound_succ (c : UpdateLoopCtx) {r : ℕ} (hr : r < c.U.length) :
    c.cursorBound (r + 1) =
      c.cursorBound r + (c.stepSpace r + 7) + (c.resAt r).D.card + (c.reembAt r).card +
        c.lens.getD r 0 + 4 * (c.resAt r).UH.length := by
  have hrl : r < c.lens.length := c.lens_length.symm ▸ hr
  simp only [cursorBound, Finset.sum_range_succ, list_take_sum_succ hrl, list_getD_eq_getElem hrl]
  ring

lemma cursorBound_end_eq (c : UpdateLoopCtx) :
    c.cursorBound c.U.length +
      (∑ r ∈ Finset.range c.U.length, (c.resAt r).D.card) +
      (∑ r ∈ Finset.range c.U.length, (c.reembAt r).card) + 1 +
      (c.lens.sum + 4 * ∑ r ∈ Finset.range c.U.length, (c.resAt r).UH.length) =
    c.heapStart + dsUpdateLoopSpace c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us c.U c.lens c.k₀ := by
  have htake : c.lens.take c.U.length = c.lens := List.take_of_length_le (le_of_eq c.lens_length)
  simp only [cursorBound, dsUpdateLoopSpace, htake, stepSpace, resAt, reembAt]
  ring

lemma cursorBound_le_total (c : UpdateLoopCtx) {i : ℕ} (hi : i ≤ c.U.length) :
    c.cursorBound i ≤
      c.heapStart + dsUpdateLoopSpace c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us c.U c.lens c.k₀ := by
  have h1 := sum_range_le_of_le (fun r => c.stepSpace r + 7) hi
  have h2 := sum_range_le_of_le (fun r => (c.resAt r).D.card) hi
  have h2r := sum_range_le_of_le (fun r => (c.reembAt r).card) hi
  have h3 := list_take_sum_le c.lens i
  have h4 := sum_range_le_of_le (fun r => (c.resAt r).UH.length) hi
  have hend := c.cursorBound_end_eq
  have htake : c.lens.take c.U.length = c.lens := List.take_of_length_le (le_of_eq c.lens_length)
  simp only [cursorBound, htake] at hend ⊢
  clear * - h1 h2 h2r h3 h4 hend
  omega

lemma cursorBound_add_stepSpace_lt (c : UpdateLoopCtx) {r : ℕ} (hr : r < c.U.length) :
    c.cursorBound r + c.stepSpace r < 2 ^ c.w := by
  have hlt := c.cursorBound_le_total (show r + 1 ≤ c.U.length from Nat.succ_le_of_lt hr)
  have hs := c.cursorBound_succ hr
  have hsp := c.hspace
  clear * - hlt hs hsp
  omega

@[expose] noncomputable def loopCost_per_iter_def (c : UpdateLoopCtx) (r : ℕ) : ℕ :=
  if r < c.U.length then
    c.stepCost r + 35 * c.L + 510 + 30 * (c.resAt r).D.card + 30 * (c.reembAt r).card +
      30 * (c.lens.getD r 0 + 4 * (c.resAt r).UH.length)
  else 0

end UpdateLoopCtx

/-- Properties of the saved output of step `s < i` in memory `mem` alongside state metadata `x`. -/
@[expose] def SavedStepAt (c : UpdateLoopCtx) (i : ℕ) (mem : ℕ → ℕ) (x : DynSpannerMeta c.L)
    (heapCursor : ℕ) (savedHdrs : Fin i → ℕ) (dLists rLists : Fin i → List ℕ)
    (uhLists : Fin i → List Update) (uhWords : Fin i → ℕ) (s : Fin i) : Prop :=
  let h := savedHdrs s
  let dL := dLists s
  let rL := rLists s
  let uhL := uhLists s
  let uhW := uhWords s
  mem (c.heapStart + 7 + s.1) = h ∧
  c.heapStart + 7 + c.U.length ≤ h ∧
  h + 7 + dL.length + rL.length + uhW ≤ heapCursor ∧
  (∀ a, h ≤ a → a < h + 7 + dL.length + rL.length + uhW → ¬ metaFoot c.b x a) ∧
  mem h = h + 7 + dL.length + rL.length ∧
  mem (h + 1) = uhL.length ∧
  mem (h + 2) = uhW ∧
  mem (h + 3) = h + 7 ∧
  mem (h + 4) = dL.length ∧
  mem (h + 5) = h + 7 + dL.length ∧
  mem (h + 6) = rL.length ∧
  ListAt mem (h + 7) dL ∧
  dL.Nodup ∧ dL.toFinset = (c.resAt s.1).D ∧ (∀ e ∈ dL, e < c.eCap) ∧
  ListAt mem (h + 7 + dL.length) rL ∧
  rL.Nodup ∧ rL.toFinset = c.reembAt s.1 ∧ (∀ e ∈ rL, e < c.eCap) ∧
  BatchBodyAt mem (h + 7 + dL.length + rL.length) (c.stAt s.1).H uhL uhW ∧
  uhL.Perm (c.resAt s.1).UH ∧
  uhW ≤ c.lens.getD s.1 0 + 4 * (c.resAt s.1).UH.length

/-- Loop invariant of `dsUpdateLoopStmt`'s `forRange` loop after `i` steps (`0 ≤ i ≤ c.U.length`). -/
@[expose] def UpdateLoopInv (c : UpdateLoopCtx) (i : ℕ) (st : State) : Prop :=
  ∃ (heapCursor : ℕ) (x : DynSpannerMeta c.L)
      (savedHdrs : Fin i → ℕ) (dLists rLists : Fin i → List ℕ)
      (uhLists : Fin i → List Update) (uhWords : Fin i → ℕ),
    st.regs 0 = c.b ∧ st.regs 1 = c.batchPtr ∧ st.regs 2 = c.heapStart ∧
    st.regs 3 = c.U.length ∧ st.regs 4 = c.heapStart + 7 ∧ st.regs 5 = heapCursor ∧
    st.regs 6 = c.batchPtr + 1 + (c.lens.take i).sum ∧ st.regs 7 = i ∧
    c.heapStart + 7 + c.U.length ≤ heapCursor ∧
    heapCursor ≤ c.cursorBound i ∧
    ZeroFrom st.mem heapCursor ∧
    x.vCap = c.vCap ∧ x.eCap = c.eCap ∧
    (∀ a, heapFoot x a → a < heapCursor) ∧
    (∀ a, heapFoot x a → a < c.heapStart ∨ c.heapStart + 7 + c.U.length ≤ a) ∧
    (∀ a < c.heapStart, metaFoot c.b x a ↔ metaFoot c.b c.x₀ a) ∧
    DynSpannerStateAt c.L c.vCap c.eCap c.b st.mem x (c.stAt i) ∧
    RevHistoryInv c.G₀ c.q (canonicalSparsify c.impl) c.us (c.k₀ + i) x ∧
    (∀ s ≤ c.k₀ + i, SnapInv c.G₀ c.L c.q c.mMax (canonicalSparsifyParams c.impl c.mMax).absorbTime
      (canonicalSparsify c.impl) c.us s) ∧
    st.mem (c.b + dsGenOff) ≤ c.mem0 (c.b + dsGenOff) + ∑ r ∈ Finset.range i, c.stepGen r ∧
    (∀ a < c.heapStart, ¬ metaFoot c.b c.x₀ a → st.mem a = c.mem0 a) ∧
    ∀ s : Fin i, SavedStepAt c i st.mem x heapCursor savedHdrs dLists rLists uhLists uhWords s

/-! ## Single-iteration proof (`updateLoop_step_triple`) -/

/-- Body of the `forRange` loop inside `dsUpdateLoopStmt`. -/
@[expose] def updateLoopBody (bAux bUL : ℕ) : Stmt :=
  .call 8 (bAux + stepAuxIdxUpdateLen) [.reg 6] ;;
  .call 9 (bUL + updateLoopIdxStep) [.reg 0, .reg 6, .reg 5, .reg 8] ;;
  .store (.bin .add (.reg 4) (.reg 7)) (.reg 9) ;;
  .call 5 (bUL + updateLoopIdxSaveStep) [.reg 5, .reg 9] ;;
  .assign 6 (.bin .add (.reg 6) (.reg 8))

private lemma savedStepAt_preserve_old {c : UpdateLoopCtx} {r : ℕ}
    {mem mem' : ℕ → ℕ} {x x' : DynSpannerMeta c.L}
    {heapCursor ret0 retStep heapCursor' : ℕ}
    {savedHdrs : Fin r → ℕ} {dLists rLists : Fin r → List ℕ}
    {uhLists : Fin r → List Update} {uhWords : Fin r → ℕ}
    {dNew rNew : List ℕ} {uhNew : List Update} {uhWNew : ℕ}
    {s : Fin r}
    (hs : SavedStepAt c r mem x heapCursor savedHdrs dLists rLists uhLists uhWords s)
    (hxv : x'.vCap = x.vCap) (hxe : x'.eCap = x.eCap)
    (hiv : x'.intervals = x.intervals ++ [(heapCursor, ret0)])
    (hcur_le : heapCursor ≤ heapCursor')
    (hagree_hdr : mem' (c.heapStart + 7 + s.1) = mem (c.heapStart + 7 + s.1))
    (hagree_body : ∀ a, savedHdrs s ≤ a →
      a < savedHdrs s + 7 + (dLists s).length + (rLists s).length + uhWords s →
      mem' a = mem a) :
    SavedStepAt c (r + 1) mem' x' heapCursor'
      (snocFin savedHdrs retStep) (snocFin dLists dNew) (snocFin rLists rNew)
      (snocFin uhLists uhNew) (snocFin uhWords uhWNew)
      ⟨s.1, Nat.lt_succ_of_lt s.2⟩ := by
  rcases hs with ⟨hSlot, hHge, hHend, hHnot, hm0, hm1, hm2, hm3, hm4, hm5, hm6,
    hdAt, hdNd, hdFin, hdCap, hrAt, hrNd, hrFin, hrCap, huhBat, huhPerm, huhW⟩
  simp only [SavedStepAt, snocFin_lt _ _ ⟨s.1, Nat.lt_succ_of_lt s.2⟩ s.2, Fin.eta]
  refine ⟨hagree_hdr.trans hSlot, hHge, le_trans hHend hcur_le, fun a ha1 ha2 => ?_,
    (hagree_body _ (le_refl _) (by omega)).trans hm0,
    (hagree_body _ (by omega) (by omega)).trans hm1,
    (hagree_body _ (by omega) (by omega)).trans hm2,
    (hagree_body _ (by omega) (by omega)).trans hm3,
    (hagree_body _ (by omega) (by omega)).trans hm4,
    (hagree_body _ (by omega) (by omega)).trans hm5,
    (hagree_body _ (by omega) (by omega)).trans hm6,
    fun idx hidx => (hagree_body _ (by omega) (by omega)).trans (hdAt idx hidx),
    hdNd, hdFin, hdCap,
    fun idx hidx => (hagree_body _ (by omega) (by omega)).trans (hrAt idx hidx),
    hrNd, hrFin, hrCap,
    huhBat.of_agree (fun idx hidx => hagree_body _ (by omega) (by omega)),
    huhPerm, huhW⟩
  rw [metaFoot_lt_of_append_ge hxv hxe hiv (lt_of_lt_of_le ha2 hHend)]
  exact hHnot a ha1 ha2

/-- One iteration of `dsUpdateLoopStmt`'s `forRange` loop preserves `UpdateLoopInv` within
`c.loopCost_per_iter_def r` steps. -/
theorem updateLoop_step_triple (c : UpdateLoopCtx) {p : Program} {bs : UpdateLoopBases}
    (hps : HasUpdateLoopProcs c.impl p bs)
    {r : ℕ} (hr : r < c.U.length) :
    Triple c.w p
      (UpdateLoopInv c r)
      (updateLoopBody bs.sz.bAux bs.bUL)
      (normalPost fun st₁ =>
        UpdateLoopInv c (r + 1) { st₁ with regs := Function.update st₁.regs 7 (r + 1) } ∧
        st₁.regs 7 = r)
      (fun _ => c.loopCost_per_iter_def r) := by
  intro st ω ⟨heapCursor, x, savedHdrs, dLists, rLists, uhLists, uhWords,
    r0, r1, r2, r3, r4, r5, r6, r7, hcur_ge, hcur_le, hzCur, hxv, hxe, hfoot_lt, hfoot_gap,
    hmeta_lt, hState, hRev, hPref, hgen_le, hframe0, hSaved⟩
  set u := c.U[r]'hr
  have hrl : r < c.lens.length := c.lens_length.symm ▸ hr
  set len := c.lens[r]'hrl
  have hlen_getD : c.lens.getD r 0 = len := list_getD_eq_getElem hrl
  have hu_some : c.us[c.k₀ + r]? = some u := c.hslice r hr
  set updPtr := c.batchPtr + 1 + (c.lens.take r).sum
  have htake_succ : (c.lens.take (r + 1)).sum = (c.lens.take r).sum + len := list_take_sum_succ hrl
  have htake_le : (c.lens.take r).sum + len ≤ c.lens.sum :=
    htake_succ ▸ list_take_sum_le c.lens (r + 1)
  have hupd_le_hs : updPtr + len ≤ c.heapStart := by
    have := c.hbatch_le; clear * - htake_le this; omega
  have hupd_le_cur : updPtr + len ≤ heapCursor := le_trans hupd_le_hs (by omega)
  have hfixU : c.b + dsFixedSize c.L c.vCap c.eCap ≤ updPtr := by
    have := c.hfixB; clear * - this; omega
  have hfixCur : c.b + dsFixedSize c.L c.vCap c.eCap ≤ heapCursor := le_trans c.hfix (by omega)
  have hupd_agree : ∀ i < len, st.mem (updPtr + i) = c.mem0 (updPtr + i) := fun i hi => by
    have hlt : updPtr + i < c.heapStart := by clear * - hupd_le_hs hi; omega
    have hnf : ¬ metaFoot c.b c.x₀ (updPtr + i) := by
      have hidx : 1 + (c.lens.take r).sum + i < 1 + c.lens.sum := by
        clear * - htake_le hi; omega
      have h := c.hbatch_foot (1 + (c.lens.take r).sum + i) hidx
      rwa [show c.batchPtr + (1 + (c.lens.take r).sum + i) = updPtr + i by
        dsimp only [updPtr]; omega] at h
    exact hframe0 _ hlt hnf
  have hupd_foot : ∀ i < len, ¬ metaFoot c.b x (updPtr + i) := fun i hi => by
    have hlt : updPtr + i < c.heapStart := by clear * - hupd_le_hs hi; omega
    rw [hmeta_lt _ hlt]
    have hidx : 1 + (c.lens.take r).sum + i < 1 + c.lens.sum := by
      clear * - htake_le hi; omega
    have h := c.hbatch_foot (1 + (c.lens.take r).sum + i) hidx
    rwa [show c.batchPtr + (1 + (c.lens.take r).sum + i) = updPtr + i by
      dsimp only [updPtr]; omega] at h
  have hupd_w : ∀ i < len, st.mem (updPtr + i) < 2 ^ c.w := fun i hi => by
    rw [hupd_agree i hi]
    have hidx : 1 + (c.lens.take r).sum + i < 1 + c.lens.sum := by
      clear * - htake_le hi; omega
    have h := c.hbatch_w (1 + (c.lens.take r).sum + i) hidx
    rwa [show c.batchPtr + (1 + (c.lens.take r).sum + i) = updPtr + i by
      dsimp only [updPtr]; omega] at h
  have hupd_at0 : UpdateAt c.mem0 updPtr (c.stAt r).G u len := by
    have hg := c.hbatch_body.getElem r hr
    rw [← runState_applyBatch_take c.G₀ c.q (canonicalSparsify c.impl) c.us c.U c.k₀ c.hslice r
      (Nat.le_of_lt hr)] at hg
    simpa only [updPtr, u, len, Nat.add_assoc] using hg
  have hupd_at : UpdateAt st.mem updPtr (c.stAt r).G u len :=
    hupd_at0.copy (fun i hi => hupd_agree i hi)
  have hupd_cap : UpdateWithinCaps c.vCap c.eCap u := c.hbatch_cap u (List.getElem_mem hr)
  -- Word and space bounds for this step
  have hsp_lt : heapCursor + dsStepSpaceAt c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us
      (c.k₀ + r) len < 2 ^ c.w := by
    have h1 := c.cursorBound_add_stepSpace_lt hr
    rw [← hlen_getD]
    exact lt_of_le_of_lt (Nat.add_le_add_right hcur_le _) h1
  have hgen_step_lt : st.mem (c.b + dsGenOff) + dsStepGenAt c.G₀ c.impl c.L c.q c.us (c.k₀ + r) <
      2 ^ c.w := by
    have h1 := sum_range_add_elem_le c.stepGen hr
    have h2 := c.hgen
    dsimp only [dsUpdateLoopGen, UpdateLoopCtx.stepGen] at h1 h2 hgen_le
    clear * - hgen_le h1 h2; omega
  have hfix_w : c.b + dsFixedSize c.L c.vCap c.eCap < 2 ^ c.w := by
    have h1 := c.hfix; have h2 := c.hspace; clear * - h1 h2; omega
  have hhs_w : c.heapStart + 7 + c.U.length < 2 ^ c.w := by
    have h1 := c.hspace; dsimp only [dsUpdateLoopSpace] at h1; clear * - h1; omega
  have hcur_w : heapCursor < 2 ^ c.w := by clear * - hsp_lt; omega
  have hupd_w_ptr : updPtr + len < 2 ^ c.w := lt_of_le_of_lt hupd_le_cur hcur_w
  -- Advance `SnapInv` and get `res.D ⊆ res.state.H.E`
  have hstepInv := step_inv c.hVG₀ c.hL1 c.hq1 c.hGm₀
    (canonicalSparsify_spec_absorb c.impl c.mMax) c.hBV c.hds hu_some hPref
  have hPref_next : ∀ s ≤ c.k₀ + (r + 1), SnapInv c.G₀ c.L c.q c.mMax
      (canonicalSparsifyParams c.impl c.mMax).absorbTime (canonicalSparsify c.impl) c.us s := by
    intro s hs
    by_cases hle : s ≤ c.k₀ + r
    · exact hPref s hle
    · have heq : s = c.k₀ + r + 1 := by omega
      subst heq; exact hstepInv.1
  have hres_eq : step (c.stAt r) u (canonicalSparsify c.impl) = c.resAt r := by
    simp only [UpdateLoopCtx.resAt, UpdateLoopCtx.stAt, runStepOut, hu_some]
  have hreemb_eq : stepReembSet (c.stAt r) u = c.reembAt r := by
    simp only [UpdateLoopCtx.reembAt, UpdateLoopCtx.stAt, runStepReembSet, hu_some]
  have hst_next_eq : (step (c.stAt r) u (canonicalSparsify c.impl)).state = c.stAt (r + 1) := by
    dsimp only [UpdateLoopCtx.stAt]
    rw [show c.k₀ + (r + 1) = c.k₀ + r + 1 by omega]
    simp only [runState, hu_some]
  -- Execute the 5 statements of `updateLoopBody`
  dsimp only [updateLoopBody]
  refine runs_start_le ?_
  -- 1. `dsUpdateLen`
  refine runs_seq_call_le (vs := [updPtr])
    (dsUpdateLen_meetsContract (w := c.w) (G := (c.stAt r).G) (u := u) (len := len)
      hps.hpSZ.hpAux)
    (by simp [evalArgs, Expr.eval, r6, updPtr])
    (fun z hz => by simp only [List.mem_singleton] at hz; subst hz; omega)
    ⟨updPtr, rfl, c.hw16, hupd_w_ptr, hupd_at⟩ ?_
  rintro lenRet mem1 _ ⟨hlenRet, hm1⟩
  subst lenRet; subst mem1
  -- 2. `dsStepStmt`
  refine runs_seq_call_le (vs := [c.b, updPtr, heapCursor, len])
    (dsStep_meetsContract hps (G₀ := c.G₀) (impl := c.impl) (mMax := c.mMax) (w := c.w)
      (L := c.L) (q := c.q) (vCap := c.vCap) (eCap := c.eCap) (b := c.b) (k := c.k₀ + r)
      (us := c.us) (u := u) (len := len) (x := x))
    (by simp [evalArgs, Expr.eval, r0, r5, r6, updPtr])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨updPtr, heapCursor, rfl, c.hw16, c.hL1, c.hq1, c.hVG₀, c.hGm₀, c.hE₀_cap, c.hBV, c.hds,
      hu_some, hPref, hState, hRev, hfixCur, hfoot_lt, hzCur, hsp_lt, hgen_step_lt,
      by have := c.hk_w; omega, c.hq_w, c.hWOK r hr, hfixU, hupd_le_cur, hupd_foot, hupd_w,
      hupd_at, hupd_cap⟩ ?_
  rintro retStep mem2 _ ⟨_, _, hEqStep, hStepOut, hret_ge7, hret_leSp, hgen_step, huhW_le⟩
  simp only [List.cons.injEq, and_true] at hEqStep
  rcases hEqStep with ⟨_, rfl, rfl, _⟩
  dsimp only at hgen_step huhW_le
  -- Unpack `StepReembOutPost`
  obtain ⟨memPre, ret0, rPtr, rL_r, hret_eq, hSO, hmem2_eq, hrNd_r, hrFin_r, hrRng_r, hrAt_r⟩ :=
    hStepOut
  obtain ⟨uhPtr, uhWords_r, dPtr, uhActual_r, dL_r, x',
    hHdr0, hHdr1, hHdr2, hHdr3, hHdr4, h5d, hdU, huR, huhBat_r, huhPerm_r,
    hdNd_r, hdFin_r, hdAt_r, hzRet, hx'v, hx'e, hx'iv, hState', hRev', hFrameStep⟩ := hSO
  have hrLe_r : rPtr + rL_r.length ≤ ret0 := by
    rcases hrRng_r with h1 | ⟨_, h2⟩
    · exact le_trans h1 (le_trans hfixCur (by omega))
    · exact h2
  have hmem2_lt_ret0 : ∀ a < ret0, mem2 a = memPre a := fun a ha => by
    rw [hmem2_eq, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hmem2_ret0 : mem2 ret0 = rPtr := by
    rw [hmem2_eq, Function.update_of_ne (by omega), Function.update_self]
  have hmem2_ret01 : mem2 (ret0 + 1) = rL_r.length := by
    rw [hmem2_eq, Function.update_self]
  have hdLen_eq : dL_r.length = (c.resAt r).D.card := by
    rw [← List.toFinset_card_of_nodup hdNd_r, hdFin_r, hres_eq]
  have hrLen_eq : rL_r.length = (c.reembAt r).card := by
    rw [← List.toFinset_card_of_nodup hrNd_r, hrFin_r, hreemb_eq]
  have huhW_bound : uhWords_r ≤ len + 4 * (c.resAt r).UH.length := by
    have h2 : mem2 (heapCursor + 2) = uhWords_r :=
      (hmem2_lt_ret0 _ (by omega)).trans hHdr2
    rw [← h2, ← hres_eq]; exact huhW_le
  have hcur_next_le : retStep + 7 + dL_r.length + rL_r.length + uhWords_r ≤ c.cursorBound (r + 1) := by
    have hs := c.cursorBound_succ hr
    dsimp only [UpdateLoopCtx.stepSpace] at hs
    rw [hlen_getD] at hs
    clear * - hcur_le hret_leSp hdLen_eq hrLen_eq huhW_bound hs
    omega
  have hcur_next_lt : retStep + 7 + dL_r.length + rL_r.length + uhWords_r < 2 ^ c.w :=
    lt_of_le_of_lt hcur_next_le (lt_of_le_of_lt (c.cursorBound_le_total (Nat.succ_le_of_lt hr)) c.hspace)
  have hret_lt_w : retStep < 2 ^ c.w := by clear * - hcur_next_lt; omega
  have hstepSlot_lt : c.heapStart + 7 + r < 2 ^ c.w := by clear * - hhs_w hr; omega
  -- 3. `store [r4 + r7] r9` (`mem3[heapStart + 7 + r] := retStep`)
  refine runs_seq_store_le (x := c.heapStart + 7 + r) (v := retStep)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := c.heapStart + 7) (by simp [r4]))
      (Expr.eval_reg_of_eq (v := r) (by simp [r7])) hstepSlot_lt)
    (Expr.eval_reg_of_eq (v := retStep) (by simp)) ?_
  set mem3 := Function.update mem2 (c.heapStart + 7 + r) retStep
  have hslot_lt_cur : c.heapStart + 7 + r < heapCursor := by clear * - hcur_ge hr; omega
  have hmem3_ge_cur : ∀ a, heapCursor ≤ a → mem3 a = mem2 a := fun a ha => by
    dsimp only [mem3]; rw [Function.update_of_ne (by clear * - hslot_lt_cur ha; omega)]
  have hmem3_ne_slot : ∀ a, a ≠ c.heapStart + 7 + r → mem3 a = mem2 a := fun a hne => by
    dsimp only [mem3]; rw [Function.update_of_ne hne]
  -- 4. `dsSaveStepOut [heapCursor, retStep]`
  refine runs_seq_call_le (vs := [heapCursor, retStep])
    (dsSaveStepOut_meetsContract (w := c.w) (stepHdr := heapCursor) (retPtr := retStep)
      (uhPtr := uhPtr) (uhLen := uhActual_r.length) (uhWords := uhWords_r)
      (dPtr := dPtr) (dLen := dL_r.length) (rPtr := rPtr) (rLen := rL_r.length)
      hps.hpSZ.hpAux hps.hpUL)
    (by simp [evalArgs, Expr.eval, r5])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> omega)
    ⟨rfl, c.hw16, h5d, hdU, by omega, by omega, hcur_next_lt,
      (hmem3_ge_cur _ (le_refl _)).trans ((hmem2_lt_ret0 _ (by omega)).trans hHdr0),
      (hmem3_ge_cur _ (by omega)).trans ((hmem2_lt_ret0 _ (by omega)).trans hHdr1),
      (hmem3_ge_cur _ (by omega)).trans ((hmem2_lt_ret0 _ (by omega)).trans hHdr2),
      (hmem3_ge_cur _ (by omega)).trans ((hmem2_lt_ret0 _ (by omega)).trans hHdr3),
      (hmem3_ge_cur _ (by omega)).trans ((hmem2_lt_ret0 _ (by omega)).trans hHdr4),
      by rw [show retStep - 2 = ret0 by omega]; exact (hmem3_ge_cur _ (by omega)).trans hmem2_ret0,
      by rw [show retStep - 1 = ret0 + 1 by omega]; exact (hmem3_ge_cur _ (by omega)).trans hmem2_ret01⟩ ?_
  rintro nextCursor mem4 _ ⟨hnc_eq, hm4_0, hm4_1, hm4_2, hm4_3, hm4_4, hm4_5, hm4_6,
    hcpD, hcpR, hcpU, hFrSave⟩
  dsimp only at hcpD hcpR hcpU hFrSave
  -- 5. `assign 6 (r6 + r8)` (`updPtr + len`)
  refine runs_assign_le (v := updPtr + len)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := updPtr) (by simp [r6, updPtr]))
      (Expr.eval_reg_of_eq (v := len) (by simp)) hupd_w_ptr) ?_ ?_
  · -- Re-establish `UpdateLoopInv c (r + 1)`
    have hfoot'_lt : ∀ a, heapFoot x' a → a < ret0 := fun a ha => by
      rcases (heapFoot_append_interval hx'iv).mp ha with h1 | ⟨_, h2⟩
      · exact lt_of_lt_of_le (hfoot_lt a h1) (by omega)
      · exact h2
    have hfoot'_lt_next : ∀ a, heapFoot x' a → a < nextCursor := fun a ha =>
      lt_of_lt_of_le (hfoot'_lt a ha) (by omega)
    have hfoot'_gap : ∀ a, heapFoot x' a → a < c.heapStart ∨ c.heapStart + 7 + c.U.length ≤ a :=
      fun a ha => by
        rcases (heapFoot_append_interval hx'iv).mp ha with h1 | ⟨h1, _⟩
        · exact hfoot_gap a h1
        · exact Or.inr (le_trans hcur_ge h1)
    have hmeta'_lt : ∀ a < c.heapStart, metaFoot c.b x' a ↔ metaFoot c.b c.x₀ a := fun a ha => by
      rw [metaFoot_lt_of_append_ge (hx'v.trans hxv.symm) (hx'e.trans hxe.symm) hx'iv
        (lt_of_lt_of_le ha (by omega)), hmeta_lt a ha]
    have hmem4_eq_memPre_lt : ∀ a < ret0, a ≠ c.heapStart + 7 + r → mem4 a = memPre a :=
      fun a ha hne => by
        rw [hFrSave a (Or.inl (by omega)), hmem3_ne_slot a hne, hmem2_lt_ret0 a ha]
    have hState4 : DynSpannerStateAt c.L c.vCap c.eCap c.b mem4 x' (c.stAt (r + 1)) := by
      rw [← hst_next_eq]
      refine dynSpannerStateAt_of_collectD hState' ?_ ?_ ?_
      · have hlt := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
        rw [hmem4_eq_memPre_lt _ (lt_of_lt_of_le hlt.2 (by omega)) (by have := c.hfix; omega)]
      · intro e he
        have hlt1 := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
        have hlt2 := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
        rw [hmem4_eq_memPre_lt _ (lt_of_lt_of_le hlt2.2 (by omega)) (by have := c.hfix; omega),
            hmem4_eq_memPre_lt _ (lt_of_lt_of_le hlt1.2 (by omega)) (by have := c.hfix; omega)]
        exact (hState'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 e he).1
      · intro a _ _ hdom
        rcases hdom with hltF | hhf
        · exact hmem4_eq_memPre_lt a (lt_of_lt_of_le hltF (by omega)) (by have := c.hfix; omega)
        · have hne : a ≠ c.heapStart + 7 + r := by
            rcases hfoot'_gap a hhf with h1 | h2 <;> omega
          exact hmem4_eq_memPre_lt a (hfoot'_lt a hhf) hne
    have hgen4 : mem4 (c.b + dsGenOff) ≤ c.mem0 (c.b + dsGenOff) + ∑ s ∈ Finset.range (r + 1), c.stepGen s := by
      have hlt := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
      have hgen_eq2 : mem2 (c.b + dsGenOff) = memPre (c.b + dsGenOff) :=
        hmem2_lt_ret0 _ (lt_of_lt_of_le hlt.2 (by omega))
      rw [hmem4_eq_memPre_lt _ (lt_of_lt_of_le hlt.2 (by omega)) (by have := c.hfix; omega),
          ← hgen_eq2, Finset.sum_range_succ]
      dsimp only [UpdateLoopCtx.stepGen] at hgen_le ⊢
      clear * - hgen_le hgen_step; omega
    have hframe4 : ∀ a < c.heapStart, ¬ metaFoot c.b c.x₀ a → mem4 a = c.mem0 a := fun a ha hnf => by
      rw [hmem4_eq_memPre_lt a (lt_of_lt_of_le ha (by omega)) (by omega)]
      have hnf_x : ¬ metaFoot c.b x a := fun h => hnf ((hmeta_lt a ha).mp h)
      exact (hFrameStep a (lt_of_lt_of_le ha (by omega)) hnf_x).trans (hframe0 a ha hnf)
    have hz4 : ZeroFrom mem4 nextCursor := fun a ha => by
      rw [hFrSave a (Or.inr ha), hmem3_ge_cur a (by omega),
          hmem2_eq, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hzRet a (by omega)
    have hdCap_r : ∀ e ∈ dL_r, e < c.eCap := fun e he => by
      have heD : e ∈ (c.resAt r).D := by
        rw [← hres_eq, ← hdFin_r]; exact List.mem_toFinset.mpr he
      have heH : e ∈ (c.stAt (r + 1)).H.E := by
        have hsub := hstepInv.2.D_sub
        dsimp only [UpdateLoopCtx.stAt]
        rw [show c.k₀ + (r + 1) = c.k₀ + r + 1 by omega]
        exact hsub heD
      exact hState4.2.2.2.2.2.2.2.2.2.2.1 e (hState4.2.2.2.2.2.2.2.1 heH)
    have hrCap_r : ∀ e ∈ rL_r, e < c.eCap := fun e he => by
      have heR : e ∈ stepReembSet (c.stAt r) u := hrFin_r ▸ List.mem_toFinset.mpr he
      have heG' : e ∈ ((c.stAt r).G.applyUpdate u).E := stepReembSet_subset_G' _ _ heR
      have hdu : isDelOrSplit u := c.hds u (List.mem_of_getElem? hu_some)
      exact hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu heG')
    have hrNotSlot : ∀ idx < rL_r.length, rPtr + idx ≠ c.heapStart + 7 + r := by
      intro idx hidx
      rcases hrRng_r with h1 | ⟨h1, _⟩
      · have := c.hfix; omega
      · omega
    refine ⟨⟨nextCursor, x', snocFin savedHdrs retStep, snocFin dLists dL_r, snocFin rLists rL_r,
      snocFin uhLists uhActual_r, snocFin uhWords uhWords_r,
      by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp,
      by simp [updPtr, htake_succ, Nat.add_assoc], by simp,
      by clear * - hcur_ge hret_ge7 hnc_eq; omega,
      hnc_eq ▸ hcur_next_le, hz4, hx'v, hx'e, hfoot'_lt_next, hfoot'_gap, hmeta'_lt,
      hState4, by rw [show c.k₀ + (r + 1) = c.k₀ + r + 1 by omega]; exact hRev',
      hPref_next, hgen4, hframe4, fun s => ?_⟩, by simp [r7]⟩
    by_cases hslt : s.1 < r
    · have hsOld := hSaved ⟨s.1, hslt⟩
      have hHge_s := hsOld.2.1
      have hHend_s := hsOld.2.2.1
      have hHnot_s := hsOld.2.2.2.1
      have hslot_ag : mem4 (c.heapStart + 7 + s.1) = st.mem (c.heapStart + 7 + s.1) := by
        rw [hmem4_eq_memPre_lt _ (by omega) (by omega)]
        refine hFrameStep _ (by omega) ?_
        rintro (⟨_, hlt⟩ | hhf)
        · have := c.hfix; rw [hxv, hxe] at hlt; omega
        · rcases hfoot_gap _ hhf with h1 | h2 <;> omega
      have hbody_ag : ∀ a, savedHdrs ⟨s.1, hslt⟩ ≤ a →
          a < savedHdrs ⟨s.1, hslt⟩ + 7 + (dLists ⟨s.1, hslt⟩).length + (rLists ⟨s.1, hslt⟩).length +
            uhWords ⟨s.1, hslt⟩ →
          mem4 a = st.mem a := fun a ha1 ha2 => by
        rw [hmem4_eq_memPre_lt a (by omega) (by omega)]
        exact hFrameStep a (lt_of_lt_of_le ha2 hHend_s) (hHnot_s a ha1 ha2)
      exact savedStepAt_preserve_old hsOld (hx'v.trans hxv.symm) (hx'e.trans hxe.symm) hx'iv
        (by clear * - hret_ge7 hnc_eq; omega) hslot_ag hbody_ag
    · have hseq : s.1 = r := by omega
      simp only [SavedStepAt, snocFin_last _ _ s hseq, hseq]
      refine ⟨?_, by clear * - hcur_ge hret_ge7; omega, hnc_eq.symm ▸ le_refl _,
        fun a ha1 _ => not_metaFoot_of_ge (by rw [hx'v, hx'e]; exact le_trans hfixCur (by omega))
          (fun p hp => lt_of_lt_of_le (hfoot'_lt p hp) (by omega)) ha1,
        hm4_0, hm4_1, hm4_2, hm4_3, hm4_4, hm4_5, hm4_6, ?_, hdNd_r, by rw [hdFin_r, hres_eq],
        hdCap_r, ?_, hrNd_r, by rw [hrFin_r, hreemb_eq], hrCap_r, ?_,
        by rw [← hres_eq]; exact huhPerm_r, by rw [hlen_getD]; exact huhW_bound⟩
      · rw [hFrSave _ (Or.inl (by omega))]
        dsimp only [mem3]
        exact Function.update_self _ _ _
      · intro idx hidx
        exact (hcpD idx hidx).trans ((hmem3_ge_cur _ (by omega)).trans
          ((hmem2_lt_ret0 _ (by omega)).trans (hdAt_r idx hidx)))
      · intro idx hidx
        exact (hcpR idx hidx).trans ((hmem3_ne_slot _ (hrNotSlot idx hidx)).trans
          ((hmem2_lt_ret0 _ (by omega)).trans (hrAt_r idx hidx)))
      · exact huhBat_r.copy fun idx hidx =>
          (hcpU idx hidx).trans ((hmem3_ge_cur _ (by omega)).trans (hmem2_lt_ret0 _ (by omega)))
  · -- Cost bound for one iteration
    simp only [UpdateLoopCtx.loopCost_per_iter_def, hr, ↓reduceIte, UpdateLoopCtx.stepCost,
      dsUpdateLenContract, dsStepContract, dsSaveStepOutContract, Expr.size_reg,
      Expr.size_bin, argsSize_cons, argsSize_nil]
    rw [hlen_getD]
    clear * - hdLen_eq hrLen_eq huhW_bound
    omega

end

end MinCostFlow.DynSpanner.Program
