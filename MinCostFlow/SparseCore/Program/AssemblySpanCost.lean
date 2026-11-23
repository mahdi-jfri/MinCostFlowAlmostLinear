module

public import MinCostFlow.SparseCore.Program.SpanBucketDefs
public import MinCostFlow.SparseCore.BundleTreeCore

/-!
# The cost of a bucket-spanner update against the bound it is charged

The sparse-core program updates the spanner of each active pair of a component and a bucket
through operation `1` of `bucketSpannerDS` (piece P6). That operation costs the amortized bound
`dsUpdateAmortCost` of the update of the slot, plus `20` (`bucketUpdateCost`). The amortized bound
is the time bound of Theorem 8.2 (page 39) for the batch, `⌈C · rate · Enc(U)⌉`, plus `1440` per
word of the encoded batch and `505` (`dsUpdateAmortCost_eq`).

The model of the tool must charge each spanner update by this same bound, so that the term of the
spanners in the model cost (times the log factor `bundleLogFactor M N`) pays for the machine. The
actual cost of the guest's update can be much smaller than the bound, so it cannot be the charge.
This file proves the link in the form the assembly uses.

* `dsUpdateAmortCost_ge`: the bound is at least `505`.
* `bucketUpdateCost_eq`: on an active slot, the cost of operation `1` is the bound plus `20`.
* `bucketUpdateCost_le_charge`: if the model charges at least the bound, the cost of operation `1`
  is at most twice the charge times the log factor. The constant `2` is free of the input.
* `bucketUpdateCost_sum_le`: the same for a sum over the active slots of a step.
* `bucketUpdateCost_le_of_words`: a charge `X` that pays only the batch part of the bound (as the
  charge `⌈rate · Enc(U)⌉` of the model does) also pays the rest, `1440 · W + 525`, when it is at
  least `1` and the batch has at most `c_W · X` words. Then the cost of operation `1` is at most
  `(1440 · c_W + 526) · X`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore

/-- The amortized bound of an update, written out: the charge of Theorem 8.2 for the batch read at
`batchPtr` on the current graph, `1440` per word of the batch and `505`. -/
theorem dsUpdateAmortCost_eq (P : DSParams) (s : DSHist) (b batchPtr W h : ℕ) (mem : ℕ → ℕ) :
    dsUpdateAmortCost P s [b, batchPtr, W, h] mem =
      dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀ (s.G₀.applyBatch s.flat)
          (decodeBatch mem batchPtr (s.state P).G).1 + 1440 * W + 505 := by
  simp only [dsUpdateAmortCost, opBatch, opWords, dsUpdateOpOverhead, List.getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

/-- The amortized bound of an update is at least `505`. -/
theorem dsUpdateAmortCost_ge (P : DSParams) (s : DSHist) (args : List ℕ) (mem : ℕ → ℕ) :
    505 ≤ dsUpdateAmortCost P s args mem := by
  unfold dsUpdateAmortCost dsUpdateOpOverhead
  omega

/-- On an active slot, operation `1` of the bucket spanners costs the amortized bound of the
update of the slot plus `20`. -/
theorem bucketUpdateCost_eq (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (tbl slot batchPtr W h : ℕ) (hslot : slot < cap) (s : DSHist)
    (hs : S ⟨slot, hslot⟩ = some s) (mem : ℕ → ℕ) :
    bucketUpdateCost P cap S [tbl, slot, batchPtr, W, h] mem =
      dsUpdateAmortCost P s [0, batchPtr, W, h] mem + 20 := by
  have hslot' : [tbl, slot, batchPtr, W, h].getD 1 0 < cap := hslot
  unfold bucketUpdateCost
  simp only [hslot', ↓reduceDIte]
  have hS : S ⟨[tbl, slot, batchPtr, W, h].getD 1 0, hslot'⟩ = some s := hs
  rw [hS]
  rfl

/-- **The cost of a bucket-spanner update is paid by its charge.** If the model charges an update
of a slot at least the amortized bound of `dynSpannerDS`, then operation `1` costs at most twice
the charge times the log factor of the model. -/
theorem bucketUpdateCost_le_charge (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (tbl slot batchPtr W h : ℕ) (hslot : slot < cap) (s : DSHist)
    (hs : S ⟨slot, hslot⟩ = some s) (mem : ℕ → ℕ) (charge M N : ℕ)
    (hcharge : dsUpdateAmortCost P s [0, batchPtr, W, h] mem ≤ charge) :
    bucketUpdateCost P cap S [tbl, slot, batchPtr, W, h] mem ≤
      2 * charge * bundleLogFactor M N := by
  rw [bucketUpdateCost_eq P cap S tbl slot batchPtr W h hslot s hs mem]
  have h505 := dsUpdateAmortCost_ge P s [0, batchPtr, W, h] mem
  have hlg : 1 ≤ bundleLogFactor M N := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h2 : dsUpdateAmortCost P s [0, batchPtr, W, h] mem + 20 ≤ 2 * charge := by omega
  calc dsUpdateAmortCost P s [0, batchPtr, W, h] mem + 20 ≤ 2 * charge := h2
    _ = 2 * charge * 1 := (Nat.mul_one _).symm
    _ ≤ 2 * charge * bundleLogFactor M N := Nat.mul_le_mul_left _ hlg

/-- The sum form of `bucketUpdateCost_le_charge`: over any finite set of updates, each paid by its
charge, the costs add up to at most twice the sum of the charges times the log factor. -/
theorem bucketUpdateCost_sum_le {ι : Type} (I : Finset ι) (cost charge : ι → ℕ) (M N : ℕ)
    (h : ∀ i ∈ I, cost i ≤ 2 * charge i * bundleLogFactor M N) :
    I.sum cost ≤ 2 * I.sum charge * bundleLogFactor M N := by
  calc I.sum cost ≤ I.sum fun i => 2 * charge i * bundleLogFactor M N := Finset.sum_le_sum h
    _ = 2 * I.sum charge * bundleLogFactor M N := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- **A charge for the batch part pays the whole update.** Let `X` be at least the charge of
Theorem 8.2 for the batch, at least `1`, and let the batch have at most `c_W · X` words. Then
operation `1` costs at most `(1440 · c_W + 526) · X`. The `1440` words term is paid by the word
bound and the constant `525` by `1 ≤ X`. -/
theorem bucketUpdateCost_le_of_words (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (tbl slot batchPtr W h : ℕ) (hslot : slot < cap) (s : DSHist)
    (hs : S ⟨slot, hslot⟩ = some s) (mem : ℕ → ℕ) (X c_W : ℕ)
    (hX : dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀ (s.G₀.applyBatch s.flat)
      (decodeBatch mem batchPtr (s.state P).G).1 ≤ X)
    (hW : W ≤ c_W * X) (h1 : 1 ≤ X) :
    bucketUpdateCost P cap S [tbl, slot, batchPtr, W, h] mem ≤ (1440 * c_W + 526) * X := by
  rw [bucketUpdateCost_eq P cap S tbl slot batchPtr W h hslot s hs mem,
    dsUpdateAmortCost_eq P s 0 batchPtr W h mem]
  have hW' : 1440 * W ≤ 1440 * c_W * X := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 1440 hW
  have h525 : 525 ≤ 525 * X := Nat.le_mul_of_pos_right 525 h1
  calc _ ≤ X + 1440 * c_W * X + 525 * X := by omega
    _ = (1440 * c_W + 526) * X := by ring

end MinCostFlow.SparseCore.Program
