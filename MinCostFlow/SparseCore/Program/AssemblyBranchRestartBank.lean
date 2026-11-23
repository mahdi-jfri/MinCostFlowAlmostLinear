module

public import MinCostFlow.SparseCore.Program.RestartModelCost

/-!
# The bucket banks after a restart (`AssemblyBranchRestartBank`)

The bundle side of a branch holds the banks of the bucket spanners three times (`asmBrSideRep`).
The restart of P8 pays for the new banks once. To pay for the other two copies, this file bounds
the new banks by the old banks plus `singleBundleRestartMachCost`. A restart puts a fresh spanner
in each listed slot, and the first bank of a fresh spanner is part of the cost of its start
(`spanActivateCost`).

* `bucketPhi_eq_of_rep`: the potential of the bucket spanners is the sum of the banks of the
  histories in the slots.
* `bucketPhi_restart_le`: after a restart, the potential is at most the old one plus
  `singleBundleRestartMachCost`. Only this result is used later.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-- The bank of one slot of a bucket spanner table: the bank of its history, or `0`. -/
noncomputable def spanSlotBank (P : DSParams) : Option DSHist → ℕ
  | none => 0
  | some d => d.bank P

/-- The potential of the bucket spanners is the sum of the banks of the histories in the slots,
since the representation of each slot stores its history. -/
theorem bucketPhi_eq_of_rep {P : DSParams} {cap tbl : ℕ} {S : BucketSpannerState cap}
    {x : BucketSpannerMeta P.L cap} {mem : ℕ → ℕ}
    (h : (bucketSpannerRep P cap).rep tbl S x mem) :
    bucketPhi P x = ∑ j, spanSlotBank P (S j) := by
  unfold bucketPhi
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := h.1 j
  rcases hS : S j with _ | d <;> rcases hx : x.slots j with _ | ⟨b, m⟩ <;> rw [hS, hx] at hj
  · rfl
  · exact hj.elim
  · exact hj.elim
  · have hm : m.1 = d := hj.2.1.1
    show m.1.bank P = d.bank P
    rw [hm]

/-- **The banks after a restart**, as sums over the slots: a listed slot holds a fresh spanner,
whose bank is `dsInitBank`, and every other slot keeps its history. -/
theorem sum_spanSlotBank_restart_le (P : DSParams) {slotCap cap : ℕ} (S6 : BucketSpannerState cap)
    (S : Fin slotCap → Option BundleState) (cs : CompLSFState) (ord : ℕ → List End) (k : ℕ)
    {slots : List ℕ} (hnd : slots.Nodup) :
    ∑ j, spanSlotBank P (restartSpanState S6 S cs ord k slots j) ≤
      ∑ j, spanSlotBank P (S6 j) +
        (slots.map fun s => dsInitBank P (restartSlotGraph S cs ord k s)).sum := by
  set g := fun s => dsInitBank P (restartSlotGraph S cs ord k s) with hg
  have hpt : ∀ j : Fin cap, spanSlotBank P (restartSpanState S6 S cs ord k slots j) ≤
      spanSlotBank P (S6 j) + if j.1 ∈ slots then g j.1 else 0 := by
    intro j
    unfold restartSpanState
    split_ifs with hj
    · have hb : DSHist.bank P ⟨restartSlotGraph S cs ord k j.1, []⟩ = g j.1 := by
        simp [DSHist.bank, dsBank, dsBankTotal, dsSpent, dsInitBank, DSHist.q, g]
      show DSHist.bank P ⟨restartSlotGraph S cs ord k j.1, []⟩ ≤ _
      omega
    · omega
  have hsel : ∑ j : Fin cap, (if j.1 ∈ slots then g j.1 else 0) ≤ (slots.map g).sum := by
    rw [Fin.sum_univ_eq_sum_range (fun n => if n ∈ slots then g n else 0), ← Finset.sum_filter,
      ← List.sum_toFinset g hnd]
    exact Finset.sum_le_sum_of_subset fun n hn => List.mem_toFinset.mpr (Finset.mem_filter.mp hn).2
  calc _ ≤ ∑ j, (spanSlotBank P (S6 j) + if j.1 ∈ slots then g j.1 else 0) :=
        Finset.sum_le_sum fun j _ => hpt j
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left hsel _

/-- **The potential of the bucket spanners after a restart** is at most the old potential plus
`singleBundleRestartMachCost`. The new banks of the listed slots are at most the costs of their
starts (`spanActivateCost`), and these costs sum to at most the restart cost
(`sum_spanActivateCost_le_singleRestartInner`). -/
theorem bucketPhi_restart_le {P : DSParams} {slotCap cap tbl tbl' : ℕ} {tr : BundleTreeState P.L}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S : Fin slotCap → Option BundleState}
    {S6 : BucketSpannerState cap} {x x' : BucketSpannerMeta P.L cap} {mem mem' : ℕ → ℕ}
    {ord : ℕ → List End} (hrep : (bucketSpannerRep P cap).rep tbl S6 x mem)
    (hrep' : (bucketSpannerRep P cap).rep tbl' (restartSpanState S6 S tr.cs ord tr.k slots) x'
      mem')
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound) :
    bucketPhi P x' ≤ bucketPhi P x +
      singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  rw [bucketPhi_eq_of_rep hrep, bucketPhi_eq_of_rep hrep']
  refine le_trans (sum_spanSlotBank_restart_le P S6 S tr.cs ord tr.k hMap.1)
    (Nat.add_le_add_left ?_ _)
  have hlg : 1 ≤ bundleLogFactor tr.m₀ tr.n₀ := Nat.one_le_pow _ _ (Nat.succ_pos _)
  rw [singleBundleRestartMachCost_eq_inner]
  refine le_trans ?_ (le_trans (sum_spanActivateCost_le_singleRestartInner P ord hMap hMatch hok
    hP hC hSB) (Nat.le_mul_of_pos_right _ hlg))
  refine List.sum_le_sum fun s _ => ?_
  unfold spanActivateCost
  omega

/-- **The bucket-spanner potential after a restart (inner form)**: increases by at most
`singleRestartInner`, before multiplying by `bundleLogFactor tr.m₀ tr.n₀`. -/
theorem bucketPhi_restart_inner_le {P : DSParams} {slotCap cap tbl tbl' : ℕ}
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} {S6 : BucketSpannerState cap}
    {x x' : BucketSpannerMeta P.L cap} {mem mem' : ℕ → ℕ} {ord : ℕ → List End}
    (hrep : (bucketSpannerRep P cap).rep tbl S6 x mem)
    (hrep' : (bucketSpannerRep P cap).rep tbl' (restartSpanState S6 S tr.cs ord tr.k slots) x'
      mem')
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound) :
    bucketPhi P x' ≤ bucketPhi P x + singleRestartInner tr ord := by
  rw [bucketPhi_eq_of_rep hrep, bucketPhi_eq_of_rep hrep']
  refine le_trans (sum_spanSlotBank_restart_le P S6 S tr.cs ord tr.k hMap.1)
    (Nat.add_le_add_left ?_ _)
  refine le_trans ?_ (sum_spanActivateCost_le_singleRestartInner P ord hMap hMatch hok hP hC hSB)
  refine List.sum_le_sum fun s _ => ?_
  unfold spanActivateCost
  omega

/-- **The log-weighted bucket-spanner potential after a restart**: since
`singleBundleRestartMachCost = singleRestartInner * bundleLogFactor tr.m₀ tr.n₀`, scaling
`bucketPhi` by `bundleLogFactor tr.m₀ tr.n₀` still increases by at most one copy of
`singleBundleRestartMachCost`. -/
theorem bucketPhi_restart_mul_lg_le {P : DSParams} {slotCap cap tbl tbl' : ℕ}
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} {S6 : BucketSpannerState cap}
    {x x' : BucketSpannerMeta P.L cap} {mem mem' : ℕ → ℕ} {ord : ℕ → List End}
    (hrep : (bucketSpannerRep P cap).rep tbl S6 x mem)
    (hrep' : (bucketSpannerRep P cap).rep tbl' (restartSpanState S6 S tr.cs ord tr.k slots) x'
      mem')
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound) :
    bundleLogFactor tr.m₀ tr.n₀ * bucketPhi P x' ≤
      bundleLogFactor tr.m₀ tr.n₀ * bucketPhi P x +
        singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  have h1 := bucketPhi_restart_inner_le hrep hrep' hMap hMatch hok hP hC hSB
  rw [singleBundleRestartMachCost_eq_inner]
  calc bundleLogFactor tr.m₀ tr.n₀ * bucketPhi P x'
      ≤ bundleLogFactor tr.m₀ tr.n₀ * (bucketPhi P x + singleRestartInner tr ord) :=
        Nat.mul_le_mul_left _ h1
    _ = bundleLogFactor tr.m₀ tr.n₀ * bucketPhi P x +
          singleRestartInner tr ord * bundleLogFactor tr.m₀ tr.n₀ := by
        rw [Nat.mul_add, Nat.mul_comm (bundleLogFactor tr.m₀ tr.n₀) (singleRestartInner tr ord)]

/-- **Scaled difference bound for `asmBrSideRep.phi` across a restart**: absorbs the extra
`K - 1` copies of `bucketPhi` when `K = 320 * (capExp + 1) * lgFac` and `lgFac = bundleLogFactor`. -/
theorem bucketPhi_restart_scaled_add_le {P : DSParams} {slotCap cap tbl tbl' capExp lgFac A B : ℕ}
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} {S6 : BucketSpannerState cap}
    {x x' : BucketSpannerMeta P.L cap} {mem mem' : ℕ → ℕ} {ord : ℕ → List End}
    (hrep : (bucketSpannerRep P cap).rep tbl S6 x mem)
    (hrep' : (bucketSpannerRep P cap).rep tbl' (restartSpanState S6 S tr.cs ord tr.k slots) x'
      mem')
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound)
    (hLg : lgFac = bundleLogFactor tr.m₀ tr.n₀)
    (hBase : A + bucketPhi P x' ≤ B + bucketPhi P x) :
    A + 320 * (capExp + 1) * lgFac * bucketPhi P x' ≤
      B + 320 * (capExp + 1) *
        singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord +
      320 * (capExp + 1) * lgFac * bucketPhi P x := by
  have h1 := bucketPhi_restart_inner_le hrep hrep' hMap hMatch hok hP hC hSB
  have hlg1 : 1 ≤ lgFac := hLg ▸ Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hK1 : 1 ≤ 320 * (capExp + 1) * lgFac :=
    (show 1 ≤ 320 * (capExp + 1) by omega).trans (Nat.le_mul_of_pos_right _ hlg1)
  have hsub : (320 * (capExp + 1) * lgFac - 1) * bucketPhi P x' ≤
      (320 * (capExp + 1) * lgFac - 1) * bucketPhi P x +
      320 * (capExp + 1) *
        singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
    have hm := (Nat.mul_le_mul_left (320 * (capExp + 1) * lgFac - 1) h1).trans_eq
      (Nat.mul_add (320 * (capExp + 1) * lgFac - 1) _ _)
    refine hm.trans (Nat.add_le_add_left ?_ _)
    calc (320 * (capExp + 1) * lgFac - 1) * singleRestartInner tr ord
        ≤ (320 * (capExp + 1) * bundleLogFactor tr.m₀ tr.n₀) * singleRestartInner tr ord :=
          Nat.mul_le_mul_right _ (by rw [← hLg]; omega)
      _ = 320 * (capExp + 1) * (singleRestartInner tr ord * bundleLogFactor tr.m₀ tr.n₀) := by ring
      _ = 320 * (capExp + 1) *
            singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
          rw [singleBundleRestartMachCost_eq_inner]
  have hsplit : ∀ v, 320 * (capExp + 1) * lgFac * v =
      (320 * (capExp + 1) * lgFac - 1) * v + v := fun v => by
    conv_lhs => rw [← Nat.sub_add_cancel hK1, Nat.add_mul, one_mul]
  rw [hsplit (bucketPhi P x'), hsplit (bucketPhi P x)]
  omega

end MinCostFlow.SparseCore.Program
