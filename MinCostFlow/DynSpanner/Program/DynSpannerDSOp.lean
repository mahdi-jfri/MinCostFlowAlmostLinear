module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoop

/-!
# The update operation of the data structure of Theorem 8.2

The batch loop `dsUpdateLoopStmt` reads its batch from the heap above the state block. A user of
the data structure keeps the batch in its own memory, which may lie anywhere below the heap
pointer. So the update operation `dsUpdateOpStmt` (`[b, batchPtr, W, h]`) first copies the `W`
words of the batch to the start of the heap `h`, then runs the batch loop on the copy with the
heap starting at `h + W`. The copy changes only words from `h` on, so the state block and the user
memory below `h` are the same for the loop as for the caller.

The main result is `dsUpdateOp_meetsContract`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The update operation (`[b, batchPtr, W, h]`): copy the batch to `h`, then run the batch loop
from `h` with the heap at `h + W`, and return its result. -/
def dsUpdateOpStmt (bAux bUL : ℕ) : Stmt :=
  .call 4 (bAux + stepAuxIdxCopyWords) [.reg 1, .reg 3, .reg 2] ;;
  .call 5 (bUL + updateLoopIdxUpdate) [.reg 0, .reg 3, .bin .add (.reg 3) (.reg 2)] ;;
  .ret (.reg 5)

/-- The number of extra steps of the update operation besides the copy and the batch loop. -/
def dsUpdateOpOverhead : ℕ := 20

/-- The procedures of the data structure besides the initialization: the update at index `0`. -/
def dsOpProcs (bAux bUL : ℕ) : List Stmt := [dsUpdateOpStmt bAux bUL]

lemma dsOpProcs_noRand (bAux bUL : ℕ) : ∀ s ∈ dsOpProcs bAux bUL, s.NoRand := by
  intro s hs
  simp only [dsOpProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  trivial

/-- A batch body keeps its meaning when its words are copied to another address. -/
lemma BatchBodyLensAt.shift {mem mem' : ℕ → ℕ} {a a' : ℕ} {G : MGraph} {U : List Update}
    {lens : List ℕ} (h : BatchBodyLensAt mem a G U lens)
    (hag : ∀ i < lens.sum, mem' (a' + i) = mem (a + i)) :
    BatchBodyLensAt mem' a' G U lens := by
  induction U generalizing a a' G lens with
  | nil => cases lens with
    | nil => trivial
    | cons _ _ => exact h.elim
  | cons u us ih => cases lens with
    | nil => exact h.elim
    | cons len ls =>
      obtain ⟨hu, hr⟩ := h
      refine ⟨hu.copy fun i hi => hag i (by simp only [List.sum_cons]; omega),
        ih hr fun i hi => ?_⟩
      have := hag (len + i) (by simp only [List.sum_cons]; omega)
      rwa [← Nat.add_assoc, ← Nat.add_assoc] at this

/-- The contract of `dsUpdateOpStmt`. Its pre is the pre of `dsUpdateLoopContract` with the heap
at `h + W`, except that the batch is in the caller's memory at `batchPtr`, in `W = 1 + Σ lens`
words below `h`. Its post is the post of the batch loop, where `memC` is the memory after the
copy, which agrees with the memory of the caller below `h`. -/
noncomputable def dsUpdateOpContract (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax w L q vCap eCap b k₀ : ℕ) (us U : List Update) (lens : List ℕ)
    (x₀ : DynSpannerMeta L) : Contract where
  pre args mem := ∃ batchPtr h,
    let st₀ := runState (L := L) G₀ q (canonicalSparsify impl) us k₀
    args = [b, batchPtr, 1 + lens.sum, h] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ L ∧ 1 ≤ q ∧
    G₀.IsValid ∧ G₀.m ≤ mMax ∧ (∀ e ∈ G₀.E, e < eCap) ∧
    G₀.BatchIsValid us ∧ (∀ u' ∈ us, isDelOrSplit u') ∧
    (∀ i (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) ∧
    (∀ s ≤ k₀, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s) ∧
    DynSpannerStateAt L vCap eCap b mem x₀ st₀ ∧
    RevHistoryInv G₀ q (canonicalSparsify impl) us k₀ x₀ ∧
    b + dsFixedSize L vCap eCap ≤ h ∧
    (∀ a, heapFoot x₀ a → a < h) ∧
    ZeroFrom mem h ∧
    h + (1 + lens.sum) + dsUpdateLoopSpace G₀ impl mMax L q vCap eCap us U lens k₀ < 2 ^ w ∧
    mem (b + dsGenOff) + dsUpdateLoopGen G₀ impl L q us U.length k₀ < 2 ^ w ∧
    k₀ + U.length < 2 ^ w ∧ q < 2 ^ w ∧
    (∀ r < U.length, dsStepWordOKAt G₀ impl w L q us (k₀ + r)) ∧
    batchPtr + (1 + lens.sum) ≤ h ∧
    (∀ i < 1 + lens.sum, mem (batchPtr + i) < 2 ^ w) ∧
    mem batchPtr = U.length ∧
    BatchBodyLensAt mem (batchPtr + 1) st₀.G U lens ∧
    BatchWithinCaps vCap eCap U
  post args mem ret mem' := ∃ batchPtr h memC,
    args = [b, batchPtr, 1 + lens.sum, h] ∧
    (∀ a < h, memC a = mem a) ∧
    BatchUpdateOutPost G₀ L q vCap eCap b k₀ impl us U memC x₀ (h + (1 + lens.sum)) mem' ret ∧
    h + (1 + lens.sum) + 7 ≤ ret ∧
    ret ≤ h + (1 + lens.sum) + dsUpdateLoopSpace G₀ impl mMax L q vCap eCap us U lens k₀ ∧
    mem' (b + dsGenOff) ≤ mem (b + dsGenOff) + dsUpdateLoopGen G₀ impl L q us U.length k₀
  cost _ _ := 30 * (1 + lens.sum) + 25 + dsUpdateOpOverhead +
    dsUpdateLoopCost G₀ impl mMax L q vCap eCap us U lens k₀

/-- `dsUpdateOpStmt` meets `dsUpdateOpContract`. -/
theorem dsUpdateOp_meetsContract {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k₀ : ℕ} {us U : List Update} {lens : List ℕ}
    {x₀ : DynSpannerMeta L} {p : Program} {bs : UpdateLoopBases} {bOp : ℕ}
    (hps : HasUpdateLoopProcs impl p bs) (hpOp : p.HasAt bOp (dsOpProcs bs.sz.bAux bs.bUL)) :
    MeetsContract w p bOp (dsUpdateOpContract G₀ impl mMax w L q vCap eCap b k₀ us U lens x₀) := by
  refine meetsContract_of_runs (f := bOp) (hpOp.get (i := 0) (by simp [dsOpProcs])) ?_
  rintro args mem pos ω _ ⟨batchPtr, h, rfl, hw16, hL1, hq1, hVG₀, hGm₀, hE₀, hBV, hds, hslice,
    hSnap, hState, hRev, hfix, hfoot, hz, hspace, hgen, hk, hqw, hWOK, hbat, hbatw, hbatlen,
    hbody, hcaps⟩
  simp only [dsOpProcs, List.getElem_cons_zero]
  dsimp only [dsUpdateOpStmt]
  refine runs_start_le ?_
  have hW_w : 1 + lens.sum < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have hb_w : b < 2 ^ w := by omega
  have hbp_w : batchPtr < 2 ^ w := by omega
  have hhW_w : h + (1 + lens.sum) < 2 ^ w := by omega
  refine runs_seq_call_le (vs := [batchPtr, h, 1 + lens.sum])
    (dsCopyWords_meetsContract (w := w) (n := 1 + lens.sum) hps.hpSZ.hpAux)
    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <| evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption)
    ⟨batchPtr, h, rfl, hw16, by omega, hhW_w, Or.inl hbat⟩ ?_
  rintro ret1 memC pos1 ⟨src, dst, hargs1, -, hcp, hfr⟩
  simp only [List.cons.injEq, and_true] at hargs1
  obtain ⟨rfl, rfl⟩ := hargs1
  have hagC : ∀ a < h, memC a = mem a := fun a ha => hfr a (Or.inl ha)
  have hState' : DynSpannerStateAt L vCap eCap b memC x₀
      (runState (L := L) G₀ q (canonicalSparsify impl) us k₀) :=
    dynSpannerStateAt_of_agree_lt hState hfix hfoot hagC
  have hgenC : memC (b + dsGenOff) = mem (b + dsGenOff) :=
    hagC _ (lt_of_lt_of_le ((stepZero_fixed_lt b L vCap eCap).1 dsGenOff (by decide)).2 hfix)
  have hbodyC : BatchBodyLensAt memC (h + 1)
      (runState (L := L) G₀ q (canonicalSparsify impl) us k₀).G U lens :=
    hbody.shift fun i hi => by
      rw [Nat.add_assoc, Nat.add_assoc, hcp (1 + i) (by omega)]; rfl
  have hzC : ZeroFrom memC (h + (1 + lens.sum)) := fun a ha => by
    rw [hfr a (Or.inr ha)]; exact hz a (by omega)
  have hxv : x₀.vCap = vCap := hState.1
  have hxe : x₀.eCap = eCap := hState.2.1
  have hnf : ∀ i < 1 + lens.sum, ¬ metaFoot b x₀ (h + i) := by
    intro i _ hm
    rcases hm with ⟨_, h2⟩ | hh
    · rw [hxv, hxe] at h2; omega
    · have := hfoot _ hh; omega
  refine runs_seq_call_le (vs := [b, h, h + (1 + lens.sum)])
    (dsUpdateLoop_meetsContract (G₀ := G₀) (impl := impl) (mMax := mMax) (w := w) (L := L)
      (q := q) (vCap := vCap) (eCap := eCap) (b := b) (k₀ := k₀) (us := us) (U := U)
      (lens := lens) (x₀ := x₀) hps)
    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
      evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_reg_of_eq (by simp [startState])) hhW_w) <| evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption)
    ⟨h, h + (1 + lens.sum), rfl, hw16, hL1, hq1, hVG₀, hGm₀, hE₀, hBV, hds, hslice, hSnap,
      hState', hRev, by omega, fun a ha => by have := hfoot a ha; omega, hzC,
      by omega, by show memC _ + _ < _; rw [hgenC]; exact hgen, hk, hqw, hWOK, hfix, by omega, hnf,
      fun i hi => by show memC _ < _; rw [hcp i hi]; exact hbatw i hi,
      by show memC _ = _; have h0 := hcp 0 (by omega); rw [Nat.add_zero, Nat.add_zero] at h0
         rw [h0]; exact hbatlen,
      hbodyC, hcaps⟩ ?_
  rintro ret2 mem2 pos2 ⟨bp', hs', hargs2, hPost, hlo, hhi, hgen2⟩
  simp only [List.cons.injEq, and_true] at hargs2
  obtain ⟨-, rfl, rfl⟩ := hargs2
  refine runs_ret_le (v := ret2) (Expr.eval_reg_of_eq (by simp))
    ⟨batchPtr, h, memC, rfl, hagC, hPost, hlo, hhi, by
      have hg : mem2 (b + dsGenOff) ≤ memC (b + dsGenOff) + _ := hgen2
      rw [hgenC] at hg; exact hg⟩ ?_
  simp only [dsCopyWordsContract, dsUpdateLoopContract, dsUpdateOpContract, dsUpdateOpOverhead,
    Expr.size_reg, Expr.size_bin, argsSize_cons, argsSize_nil]
  omega

end

end MinCostFlow.DynSpanner.Program
