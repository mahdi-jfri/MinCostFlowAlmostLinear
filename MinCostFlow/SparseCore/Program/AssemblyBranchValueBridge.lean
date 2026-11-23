module

public import MinCostFlow.SparseCore.Program.AssemblyBranchInit
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepSpace
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartClause

/-!
# From the clauses of `AsmBranchAt` to the step of a branch (`AssemblyBranchValueBridge`)

The step clause `step_runs` of `AsmBranchAt` (`AssemblyTopIface.lean`) states its inputs in the
form of the top layer. The step of a branch (`asmBrFull_step_runs_clause`,
`AssemblyBranchStepSpace.lean`) asks them in the form of its three calls. This file gives the
small facts that turn the first form into the second:
* `capSq_lt_of_wordExp`: the word condition of the clause gives `(vCap + eCap + 2) ^ 2 < 2 ^ w`,
  which P7's output step asks, once `asmP10WordExp capExp ≤ wordExp`;
* `asmBrFull_readBranchAt`: P10 meets `ReadBranchAt` at the caps of a branch. Its word condition
  follows from the word condition of the clause and the bounds on `tCap` and `L_w` that the
  representation holds (`p10Word_of_wordExp`);
* `compFamilyChgAt_branch`: P4's table of change records (`CompFamilyChgAt`) gives the change
  record of branch `j`, in the form `LSFChangeAt` with `c.Exact` that the first phase and P10 read,
  and it lies outside the cells of the branch;
* `inputAt_of`: an input block in words, below the heap pointer and outside the cells of the
  branch is an `InputAt`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The square of the caps fits in a word.** The cap hypothesis gives
`vCap + eCap + 2 ≤ (M + N + 2) ^ capExp`, and `2 capExp ≤ asmP10WordExp capExp ≤ wordExp`. -/
theorem capSq_lt_of_wordExp {capExp limbMul L M N vCap eCap wordExp w : ℕ}
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hwe : asmP10WordExp capExp ≤ wordExp) (hw : (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w) :
    (vCap + eCap + 2) ^ 2 < 2 ^ w :=
  calc (vCap + eCap + 2) ^ 2 ≤ ((M + N + 2) ^ capExp) ^ 2 := Nat.pow_le_pow_left hcap.1 2
    _ = (M + N + 2) ^ (2 * capExp) := by rw [← pow_mul, mul_comm]
    _ ≤ (M + N + 2) ^ wordExp :=
        Nat.pow_le_pow_right (by omega) ((asmP10WordExp_ge_two_mul capExp).trans hwe)
    _ ≤ (M + N + 2) ^ wordExp * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ < 2 ^ w := hw

/-- **P10 at the caps of a branch.** For a branch in the full representation, P10 meets
`ReadBranchAt` at the caps of the branch, its `tCap` and its `L_w`, for every spanner parameters
`SP` below the caps. The representation gives `eCap ≤ tCap` (`ReadView.Inv`), `1 ≤ L_w`,
`tCap ≤ 2 (vCap + eCap + 2) ^ 2` and the limb bound on `L_w`; with the cap hypothesis and the word
condition they give P10's word condition (`p10Word_of_wordExp`). -/
theorem asmBrFull_readBranchAt {w depth P L capExp limbMul wordExp : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {Ψ : BundleTreeState depth → ℕ} {p : Program} {bR fRoot readMul : ℕ}
    {readIdx : ℕ → ℕ} {Q : ℕ → RootQueryAt w p fRoot}
    (hB : AsmBrReadAt w P p bR readIdx fRoot Q readMul) (hwe : asmP10WordExp capExp ≤ wordExp)
    {b M N vCap eCap : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ} {mem : ℕ → ℕ}
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hw : (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w)
    (hrep : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).rep b
      ⟨tr, ord, vCap, eCap⟩ x mem)
    (k : ℕ) (SP : DSParams) (cap : ℕ) (hSPw : SP.w = w)
    (hSPe : SP.eCap ≤ eCap) :
    ReadBranchAt (readRep vCap eCap x.tCap x.L_w P) w vCap eCap x.tCap x.L_w P SP cap p bR
      readIdx fRoot (Q k) readMul := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hinv, -, -, -, -, -, -, -, -, -, -, hLwB, -⟩, -, -,
    hvc, hec, htc, -, hlw, -⟩ := hrep
  have hv : x.vCap = vCap := hvc
  have he : x.eCap = eCap := hec
  have hLw : x.L_w ≤
      L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) := by
    rw [← hM, ← hN]; exact hLwB
  have htc' : x.tCap ≤ 2 * (vCap + eCap + 2) ^ 2 := by rw [← hv, ← he]; exact htc
  have heT : eCap ≤ x.tCap := by rw [← he]; exact hinv.2.2.2.1
  exact hB k vCap eCap x.tCap x.L_w SP cap hSPw hSPe heT hlw
    (p10Word_of_wordExp hcap htc' hLw hwe hw)

/-- **The change record of branch `j`.** P4's table `CompFamilyChgAt` holds at
`mem (fChgPtr + j)` a change record `c` (`LSFChangeAt`) that is exact for the LSF of branch `j`
before and after the batch. The record lies in `[fChgPtr, fChgEnd)`, so it ends by `h`, its cells
hold words, and they lie outside the cells `foot` of the branch. -/
theorem compFamilyChgAt_branch {w k j : ℕ} {mem : ℕ → ℕ} {fChgPtr fChgEnd h : ℕ}
    {cfs : CompFamilyAbs} {U : List Update} {cs : CompLSFState} {foot : ℕ → Prop}
    (hC : CompFamilyChgAt w k mem fChgPtr fChgEnd cfs U) (hj : j < k) (hcs : cfs j = cs)
    (hend : fChgEnd ≤ h) (hnf : ∀ a, fChgPtr ≤ a → a < fChgEnd → ¬ foot a) :
    ∃ c : LSFChange, LSFChangeAt mem (mem (fChgPtr + j)) c ∧
      c.Exact cs.lsf (compLSFBatch cs U).lsf ∧
      InputAt w mem foot (mem (fChgPtr + j)) c.words h := by
  obtain ⟨_, hW, chg, hchg⟩ := hC
  obtain ⟨hAt, hEx, hp1, hp2⟩ := hchg j hj
  refine ⟨chg j, hAt, by rw [← hcs]; exact hEx, by omega, fun i hi => ⟨?_, ?_⟩⟩
  · exact hW _ (by omega) (by omega)
  · exact hnf _ (by omega) (by omega)

/-- **The split list of branch `j`.** P4's table `CompSplitListAt` holds at
`mem (fSplitPtr + j)` the canonical split list `canonSplitList cs U` (`SplitEntriesAt`) lying in
`[fSplitPtr, fChgEnd)` below `h`, with every cell a word outside `foot`. -/
theorem compSplitListAt_branch {w k j : ℕ} {mem : ℕ → ℕ} {fSplitPtr fChgEnd h : ℕ}
    {cfs : CompFamilyAbs} {U : List Update} {cs : CompLSFState} {foot : ℕ → Prop}
    (hS : CompSplitListAt w k mem fSplitPtr fChgEnd cfs U) (hj : j < k) (hcs : cfs j = cs)
    (hend : fChgEnd ≤ h) (hnf : ∀ a, fSplitPtr ≤ a → a < fChgEnd → ¬ foot a) :
    SplitEntriesAt mem (mem (fSplitPtr + j)) (canonSplitList cs U) ∧
      InputAt w mem foot (mem (fSplitPtr + j)) (splitEntriesWords (canonSplitList cs U)) h ∧
      mem (fSplitPtr + j) < 2 ^ w := by
  obtain ⟨hlo, hW, hbr⟩ := hS
  obtain ⟨hAt, hp1, hp2⟩ := hbr j hj
  rw [hcs] at hAt hp2
  refine ⟨hAt, ⟨by omega, fun i hi => ⟨?_, ?_⟩⟩, hW _ (by omega) (by omega)⟩
  · exact hW _ (by omega) (by omega)
  · exact hnf _ (by omega) (by omega)

/-- An input block of words, ending by `h` and outside the cells `foot`, is an `InputAt`. -/
theorem inputAt_of {w : ℕ} {mem : ℕ → ℕ} {foot : ℕ → Prop} {a n h : ℕ}
    (hW : ∀ i < n, mem (a + i) < 2 ^ w) (hend : a + n ≤ h)
    (hnf : ∀ c, a ≤ c → c < a + n → ¬ foot c) : InputAt w mem foot a n h :=
  ⟨hend, fun i hi => ⟨hW i hi, hnf _ (by omega) (by omega)⟩⟩

end MinCostFlow.SparseCore.Program
