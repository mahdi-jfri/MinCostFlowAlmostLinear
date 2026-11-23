module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCostGoal

import Mathlib.Tactic

/-!
# The records of P7's step at the end of the first step (`AssemblyFirstStepPostRec`)

Phase 4 writes at `rec` (the heap pointer `h` of the step) the places of the leaving edges, the
entering edges, the rotation list `T₀` and the list of re-embedded edges, and the lists themselves
at the heap pointer `hp` of Phase 4 or above (`AsmFirstPhase4PostAt`). After Phase 4 the driver
writes the place of the split lists at `rec + 1`. This file moves the facts of Phase 4 to that
final memory `Function.update st'.mem (rec + 1) val` (`asmFsPost_rec`). Every list lies at `hp` or
above, and `rec + 6 ≤ hp`, so the cell `rec + 1` is not one of their cells. The six words of the
record are below `2 ^ w` when `o.value` and `val` are: the lists lie below `o.value`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

set_option maxHeartbeats 800000 in
/-- **The records of Phase 4 in the final memory.** From the post of Phase 4, with the record
at `rec` and `rec + 6 ≤ hp`, for the memory `mem'` after the write of `val` at `rec + 1`: the
leaving and the entering edges (with their free cells), the rotation list `T₀`, the list of
re-embedded edges, the end `rec + 6 ≤ o.value`, and the zero cells from `o.value` on. If
`o.value < 2 ^ w` and `val < 2 ^ w`, the six words of the record are below `2 ^ w`. -/
theorem asmFsPost_rec {P : DSParams} {cap : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {mulE qE mulR qR spanTbl hp eCap vCap embH lo hi tourH rec : ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap} {tasks : List SpanUpdTask}
    {v : EmbView} {y : EmbConc} {U : List Update} {ed : List OrdEdit} {c : LSFChange} {nNew : ℕ}
    {lazyE : Fin nNew → List ℕ} {mk : Finset End} {tx₀ : (TR vCap eCap).τ}
    {avoid₀ : ℕ → Prop} {mem₀ : ℕ → ℕ} {tr : BundleTreeState P.L} {ord : ℕ → List End}
    {o : Outcome} {st' : State} {cost : ℕ}
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    {x' : BucketSpannerMeta P.L cap} {y' : EmbConc} {tx' : (TR vCap eCap).τ}
    {Ld Li Lr T₀ : List ℕ}
    (hP4 : AsmFirstPhase4PostAt P TR mulE qE mulR qR spanTbl hp eCap vCap embH lo hi tourH rec
      S6 x6 tasks v y U ed c lazyE mk tx₀ avoid₀ mem₀ tr ord o st' cost qs ns x' y' tx' Ld Li
      Lr T₀)
    (hrec : rec + 6 ≤ hp) (val : ℕ) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let ord' := applyOrdEdits ord ed
    let cs' := compLSFBatch tr.cs U
    let avoid : ℕ → Prop := fun x => avoid₀ x ∨ (TR vCap eCap).foot tourH tx' x
    let mem' := Function.update st'.mem (rec + 1) val
    OutDelAt mem' (mem' rec) ((outDelSet sp tr U ord ord').sort (· ≤ ·)) cs'.G.E ∧
    OutCellsFree (mem' rec) (1 + 2 * (outDelSet sp tr U ord ord').card) o.value avoid ∧
    OutInsAt mem' (mem' (rec + 2)) ((outInsSet sp tr U ord ord').sort (· ≤ ·))
      (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e)) ∧
    OutCellsFree (mem' (rec + 2)) (1 + 3 * (outInsSet sp tr U ord ord').card) o.value avoid ∧
    mem' (mem' (rec + 3)) = T₀.length ∧ ListAt mem' (mem' (rec + 3) + 1) T₀ ∧
    OutCellsFree (mem' (rec + 3)) (1 + T₀.length) o.value avoid ∧
    readList mem' (mem' (rec + 4)) (mem' (rec + 5)) = stepBundleTree_reembList sp tr U ord ord' ∧
    rec + 6 ≤ mem' (rec + 4) ∧
    OutCellsFree (mem' (rec + 4)) (mem' (rec + 5)) o.value avoid ∧
    rec + 6 ≤ o.value ∧ ZeroFrom mem' o.value ∧
    (o.value < 2 ^ P.w → val < 2 ^ P.w → ∀ i < 6, mem' (rec + i) < 2 ^ P.w) := by
  intro sp ord' cs' avoid mem'
  obtain ⟨-, -, -, -, -, -, -, hDel, hDelF, hIns, hInsF, hT0n, hT0L, hT0F, -, -, -, -, hRe, hRe4,
    hReF, -, -, -, hhp0, hhp2, hhp3, hov, -, hz, -⟩ := hP4
  -- The cells of `mem'` at `hp` or above and the record cells other than `rec + 1` are those
  -- of `st'.mem`.
  have hk : ∀ x, rec + 1 ≠ x → mem' x = st'.mem x := fun x hx =>
    Function.update_of_ne (Ne.symm hx) _ _
  have hk_hi : ∀ x, hp ≤ x → mem' x = st'.mem x := fun x hx => hk x (by omega)
  have e0 : mem' rec = st'.mem rec := hk _ (by omega)
  have e2 : mem' (rec + 2) = st'.mem (rec + 2) := hk _ (by omega)
  have e3 : mem' (rec + 3) = st'.mem (rec + 3) := hk _ (by omega)
  have e4 : mem' (rec + 4) = st'.mem (rec + 4) := hk _ (by omega)
  have e5 : mem' (rec + 5) = st'.mem (rec + 5) := hk _ (by omega)
  have e1 : mem' (rec + 1) = val := Function.update_self _ _ _
  rw [e0, e2, e3, e4, e5]
  refine ⟨outDelAt_of_agree hDel fun x hx _ => hk_hi x (by omega), hDelF,
    outInsAt_of_agree hIns fun x hx _ => hk_hi x (by omega), hInsF,
    by rw [hk_hi _ hhp3]; exact hT0n, hT0L.congr fun x hx _ => hk_hi x (by omega), hT0F, ?_,
    by omega, hReF, by omega, fun a ha => by rw [hk_hi a (by omega)]; exact hz a ha, ?_⟩
  · rw [← hRe]
    unfold readList
    refine List.map_congr_left fun i _ => hk_hi _ (by omega)
  · intro hw hval i hi
    have hDel1 := hDelF.1
    have hInsF1 := hInsF.1
    have hT0F1 := hT0F.1
    have hReF1 := hReF.1
    interval_cases i
    · simp only [Nat.add_zero]; rw [e0]; omega
    · rw [e1]; exact hval
    · rw [e2]; omega
    · rw [e3]; omega
    · rw [e4]; omega
    · rw [e5]; omega

end

end MinCostFlow.SparseCore.Program
