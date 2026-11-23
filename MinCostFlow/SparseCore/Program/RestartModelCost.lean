module

public import MinCostFlow.SparseCore.Program.RestartModelState
public import MinCostFlow.SparseCore.Program.AssemblyModel
public import MinCostFlow.SparseCore.Program.AssemblyContract
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Link from the machine restart cost to `singleBundleRestartMachCost` (`RestartModelCost`)

Proves that the amortized machine cost of `restartBranch_runs` (`RestartMain.lean`) is at most an
input-free constant times `singleBundleRestartMachCost` (`Chain/BundleRestart.lean`) and packages
the end-to-end model-level restart theorem `restartBranch_model_runs`:

* `m_add_one_le_spanInitBound`: `Hb.m + 1 ≤ spanInitBound P_b L splitBound Hb`.
* `ordStoreLog_le_of_pow` and `ordStoreLog_le_of_capHyp`: `ordStoreLog eCap` is at most
  `(capExp + 1) * bundleLogFactor M N` under `SparseCoreCapHyp`.
* `sum_spanActivateCost_le_singleRestartInner`: the sum of P6's `spanActivateCost` over all active
  slots is at most the pre-log inner sum of `singleBundleRestartMachCost` (with constant `1`).
* `rebuildSize_restartSpanState_le_two_mul_inner`: P10's `rebuildSize + slots.length + 1` is at
  most `2` times that inner sum.
* `restartBranchCost_le_singleBundleRestartMachCost` and
  `restartBranchCost_read_le_singleBundleRestartMachCost`: the entire cost RHS of
  `RestartBranchSpec` is bounded by an explicit input-free constant times
  `singleBundleRestartMachCost`.
* `restartBranch_model_runs`: full end-to-end theorem combining `restartBranch_runs` with P10's
  `ReadBranchAt`, giving both the state link to `restartBundleTree` (`BunAgree`, literal `dyn`,
  `GraphEq` on `S_cur`) and the `O(singleBundleRestartMachCost)` amortized cost bound.
* `restartBranch_toolMach_cost_le`: expresses `singleBundleRestartMachCost` as
  `T.cost (T.restart st j) - T.cost st` for `sparseCoreBundleRestartToolMachWith`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program
open MinCostFlow.SparseCore.Program.Read

public section

/-! ## Lower bounds on `spanInitBound` and log-factor comparison -/

/-- `spanInitBound` always dominates `Hb.m + 1`. -/
theorem m_add_one_le_spanInitBound (P_b : SparsifyParams) (L splitBound : ℕ) (Hb : MGraph) :
    Hb.m + 1 ≤ spanInitBound P_b L splitBound Hb := by
  unfold spanInitBound
  have hKt : 0 ≤ P_b.K_t := P_b.hK_t
  have hKs : 0 ≤ P_b.K_s := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hlog1 : 0 ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph Hb).n, Nat.cast_nonneg (α := ℝ) Hb.m])]
  have hlog2 : 0 ≤ 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ (Hb.n : ℝ) + (Hb.m : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) Hb.n, Nat.cast_nonneg (α := ℝ) Hb.m])]
  have hlog3 : 0 ≤ 1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((Hb.n + splitBound : ℕ) : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) (Hb.n + splitBound)])]
  have ht1 : 0 ≤ P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) := by
    positivity
  have ht2 : 0 ≤ P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
      (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s := by positivity
  have ht3 : 0 ≤ (Hb.n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) := by positivity
  have hR : ((Hb.m + 1 : ℕ) : ℝ) ≤
      P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) +
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) + 1 := by
    push_cast at ht3 ⊢; linarith
  exact_mod_cast le_trans hR (Nat.le_ceil _)

/-- `dsAmortConst impl` is always at least `1`. -/
theorem one_le_dsAmortConst (impl : SparsifyImpl) : 1 ≤ dsAmortConst impl := by
  unfold dsAmortConst; omega

/-- If `e + 2 ≤ (M + N + 2) ^ capExp`, then `ordStoreLog e ≤ (capExp + 1) * bundleLogFactor M N`. -/
theorem ordStoreLog_le_of_pow (e M N capExp : ℕ) (h : e + 2 ≤ (M + N + 2) ^ capExp) :
    ordStoreLog e ≤ (capExp + 1) * bundleLogFactor M N := by
  set B := M + N + 2
  set l := Nat.log 2 B
  have hB : B < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) B
  have hcap_pos : 1 ≤ capExp := by
    by_contra h0
    have hc0 : capExp = 0 := by omega
    rw [hc0, Nat.pow_zero] at h
    omega
  have hpow : B ^ capExp < (2 ^ (l + 1)) ^ capExp :=
    Nat.pow_lt_pow_left hB (by omega)
  rw [← Nat.pow_mul] at hpow
  have hlt : e + 2 < 2 ^ ((l + 1) * capExp) := lt_of_le_of_lt h hpow
  have hlog : Nat.log 2 (e + 2) < (l + 1) * capExp :=
    Nat.log_lt_of_lt_pow (by omega) hlt
  have h1 : ordStoreLog e ≤ capExp * (l + 1) := by
    unfold ordStoreLog; rw [Nat.mul_comm] at hlog; omega
  have h2 : l + 1 ≤ bundleLogFactor M N := by
    unfold bundleLogFactor
    calc l + 1 = (l + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (l + 1) * (l + 1) := Nat.mul_le_mul_left _ (Nat.succ_pos _)
      _ = (l + 1) ^ 2 := (Nat.pow_two _).symm
  calc ordStoreLog e ≤ capExp * (l + 1) := h1
    _ ≤ (capExp + 1) * bundleLogFactor M N :=
        Nat.mul_le_mul (Nat.le_succ _) h2

/-- Under `SparseCoreCapHyp capExp limbMul L M N vCap eCap`, `ordStoreLog eCap` is at most
`(capExp + 1) * bundleLogFactor M N`. -/
theorem ordStoreLog_le_of_capHyp {capExp limbMul L M N vCap eCap : ℕ}
    (h : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    ordStoreLog eCap ≤ (capExp + 1) * bundleLogFactor M N :=
  ordStoreLog_le_of_pow eCap M N capExp (le_trans (by omega) h.1)

/-! ## Per-term bounds against `singleBundleRestartMachCost` -/

/-- The pre-log inner sum of `singleBundleRestartMachCost`: the graph scan plus the sum of
`tr.spanConst * spanInitBound` over all active component-bucket bundle graphs. -/
@[expose] noncomputable def singleRestartInner {L : ℕ} (tr : BundleTreeState L)
    (ord : ℕ → List End) : ℕ :=
  open Classical in
  tr.cs.G.m + 1 + tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
    tr.spanConst * spanInitBound tr.spanParams L tr.splitBound
      (SparseCore.normGraph (restartBucketBundle tr ord C b).graph)

theorem singleBundleRestartMachCost_eq_inner (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) :
    singleBundleRestartMachCost L sparsify tr ord =
      singleRestartInner tr ord * bundleLogFactor tr.m₀ tr.n₀ :=
  rfl

/-- `tr.cs.G.m + slots.length + 1` is at most `singleRestartInner tr ord` when `1 ≤ tr.spanConst`. -/
theorem slots_length_add_le_singleRestartInner {L slotCap cap : ℕ} {tr : BundleTreeState L}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hc : 1 ≤ tr.spanConst) :
    tr.cs.G.m + slots.length + 1 ≤ singleRestartInner tr ord := by
  have hlen : slots.length ≤ tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
      tr.spanConst * spanInitBound tr.spanParams L tr.splitBound
        (SparseCore.normGraph (restartBucketBundle tr ord C b).graph) := by
    rw [hMap.length_eq]
    refine Finset.sum_le_sum fun C _ => ?_
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun b _ => ?_
    have h1 := m_add_one_le_spanInitBound tr.spanParams L tr.splitBound
      (SparseCore.normGraph (restartBucketBundle tr ord C b).graph)
    exact Nat.le_mul_of_pos_left _ hc |> le_trans (by omega)
  unfold singleRestartInner
  omega

/-- The sum of P6's `spanActivateCost` over all active slots is at most `singleRestartInner tr ord`
with constant `1`. -/
theorem sum_spanActivateCost_le_singleRestartInner {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound) :
    (slots.map fun s => spanActivateCost P (restartSlotGraph S tr.cs ord tr.k s)).sum ≤
      singleRestartInner tr ord := by
  rw [hMap.sum_map_eq]
  unfold singleRestartInner
  refine le_trans ?_ (Nat.le_add_left _ _)
  refine Finset.sum_le_sum fun C hCmem => Finset.sum_le_sum fun b hb => ?_
  have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) (mem_activePairs.mpr ⟨hCmem, hb⟩)
  have hGeq : restartSlotGraph S tr.cs ord tr.k (slotOf (C, b)) =
      SparseCore.normGraph (restartBucketBundle tr ord C b).graph := by
    unfold restartSlotGraph
    rw [restartSlotBundle_eq_restartBucketBundle hMatch ord hCmem hb]
    rfl
  have hokCB : SpanGraphOK P (SparseCore.normGraph (restartBucketBundle tr ord C b).graph) := by
    simpa only [hGeq] using hok _ hmem
  rw [hGeq]
  have h1 := spanActivateCost_le_spanInitBound P
    (SparseCore.normGraph (restartBucketBundle tr ord C b).graph)
    hokCB.2.2.2.2.2.2.1 hokCB.2.2.2.2.2.2.2.1
  have h2 := spanInitBound_mono (L := P.L) hP hSB
    (SparseCore.normGraph (restartBucketBundle tr ord C b).graph)
  exact le_trans h1 (Nat.mul_le_mul hC h2)

/-- P10's `rebuildSize + slots.length + 1` on `restartSpanState` is at most
`2 * singleRestartInner tr ord`. -/
theorem rebuildSize_restartSpanState_le_two_mul_inner {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) (hc : 1 ≤ tr.spanConst)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s)) :
    rebuildSize P (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1 ≤
      2 * singleRestartInner tr ord := by
  set S6' := restartSpanState S6 S tr.cs ord tr.k slots
  have hsum : rebuildSize P S6' slots + slots.length ≤
      2 * (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound
          (SparseCore.normGraph (restartBucketBundle tr ord C b).graph)) := by
    unfold rebuildSize
    rw [hMap.sum_map_eq, hMap.length_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun C hC => ?_
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b hb => ?_
    have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) (mem_activePairs.mpr ⟨hC, hb⟩)
    obtain ⟨hs, d, hd, rfl, hst⟩ := restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB hC hb
    set Hb := SparseCore.normGraph (restartBucketBundle tr ord C b).graph
    have hInitEq : (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).initBunG (C, b) = Hb := by
      simp only [restartBundleTree, hC, ↓reduceIte, Hb]
    have hokHb : SpanGraphOK P Hb := by
      have h1 := hok _ hmem
      rwa [restartSlotGraph_eq_initBunG (fun _ => canonicalSparsify P.impl) hMatch ord hC hb,
        hInitEq] at h1
    have hGE : (slotGE P S6' (slotOf (C, b))).card = Hb.m := by
      rw [slotGE_restartSpanState P S6 ord hMap hMatch hSB hC hb, hInitEq]; rfl
    have hHE : (slotHE P S6' (slotOf (C, b))).card ≤ Hb.m := by
      rw [slotHE_restartSpanState P S6 ord hMap hMatch hSB hC hb]
      rw [← hst, hInitEq]
      exact Finset.card_le_card (dsHist_init_H_sub_E P hokHb.2.2.2.2.2.2.1 hokHb.2.2.2.2.2.2.2.1)
    have hBnd : Hb.m + 1 ≤ tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound Hb :=
      le_trans (m_add_one_le_spanInitBound tr.spanParams P.L tr.splitBound Hb)
        (Nat.le_mul_of_pos_left _ hc)
    omega
  unfold singleRestartInner
  omega

/-! ## Total restart cost bounded by a constant times `singleBundleRestartMachCost` -/

/-- **General restart cost link.** The entire amortized cost bound of `RestartBranchSpec` is at
most an explicit input-free constant times `singleBundleRestartMachCost`, whenever `I7.size` is at
most `cSize` times the inner sum and `ordStoreLog` is at most `logMul * bundleLogFactor`. -/
theorem restartBranchCost_le_singleBundleRestartMachCost {slotCap cap eCap k : ℕ}
    (P : DSParams) (p : Program) (fBun fScur : ℕ)
    (I5 : BunRestartAt P.w slotCap eCap k p fBun) (I7 : ScurRebuildAt P cap p fScur)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (v : I7.α)
    (ord : ℕ → List End) (cSize logMul : ℕ)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound)
    (hSize : I7.size v (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1 ≤
      cSize * singleRestartInner tr ord)
    (hLog5 : ordStoreLog eCap ≤ logMul * bundleLogFactor tr.m₀ tr.n₀)
    (hLog7 : ordStoreLog P.eCap ≤ logMul * bundleLogFactor tr.m₀ tr.n₀) :
    I5.mul * (tr.cs.G.m + slots.length + 1) * ordStoreLog eCap +
      (slots.map fun s => spanActivateCost P (restartSlotGraph S tr.cs ord tr.k s)).sum +
      (I7.mul + 2 * I7.rootCost) *
        (I7.size v (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1) *
        ordStoreLog P.eCap +
      200 * slots.length + 200 ≤
    ((I5.mul + cSize * (I7.mul + 2 * I7.rootCost)) * logMul + 201) *
      singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  set Inner := singleRestartInner tr ord
  set lg := bundleLogFactor tr.m₀ tr.n₀
  have hlg : 1 ≤ lg := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hc1 : 1 ≤ tr.spanConst := le_trans (one_le_dsAmortConst P.impl) hC
  have hSlots := slots_length_add_le_singleRestartInner ord hMap hc1
  have hSpan := sum_spanActivateCost_le_singleRestartInner P ord hMap hMatch hok hP hC hSB
  have ht1 : I5.mul * (tr.cs.G.m + slots.length + 1) * ordStoreLog eCap ≤
      (I5.mul * logMul) * (Inner * lg) := by
    calc I5.mul * (tr.cs.G.m + slots.length + 1) * ordStoreLog eCap
        ≤ I5.mul * Inner * (logMul * lg) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hSlots) hLog5
      _ = (I5.mul * logMul) * (Inner * lg) := by ring
  have ht2 : (slots.map fun s => spanActivateCost P (restartSlotGraph S tr.cs ord tr.k s)).sum ≤
      Inner * lg :=
    le_trans hSpan (Nat.le_mul_of_pos_right _ hlg)
  have ht3 : (I7.mul + 2 * I7.rootCost) *
        (I7.size v (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1) *
        ordStoreLog P.eCap ≤
      (cSize * (I7.mul + 2 * I7.rootCost) * logMul) * (Inner * lg) := by
    calc (I7.mul + 2 * I7.rootCost) *
            (I7.size v (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1) *
            ordStoreLog P.eCap
        ≤ (I7.mul + 2 * I7.rootCost) * (cSize * Inner) * (logMul * lg) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hSize) hLog7
      _ = (cSize * (I7.mul + 2 * I7.rootCost) * logMul) * (Inner * lg) := by ring
  have ht4 : 200 * slots.length + 200 ≤ 200 * (Inner * lg) := by
    have h200 : 200 * slots.length + 200 ≤ 200 * Inner := by omega
    calc 200 * slots.length + 200 ≤ 200 * Inner := h200
      _ ≤ 200 * (Inner * lg) := Nat.mul_le_mul_left 200 (Nat.le_mul_of_pos_right _ hlg)
  rw [singleBundleRestartMachCost_eq_inner]
  calc _ ≤ (I5.mul * logMul) * (Inner * lg) + Inner * lg +
          (cSize * (I7.mul + 2 * I7.rootCost) * logMul) * (Inner * lg) + 200 * (Inner * lg) := by
        omega
    _ = ((I5.mul + cSize * (I7.mul + 2 * I7.rootCost)) * logMul + 201) * (Inner * lg) := by ring

/-- **Explicit restart cost constant for P10 (`ReadBranchAt`).** -/
@[expose] def restartModelConst (bunMul readMul rootCost capExp : ℕ) : ℕ :=
  (bunMul + 2 * (readMul + 2 * rootCost)) * (capExp + 1) + 201

/-- Specialization of `restartBranchCost_le_singleBundleRestartMachCost` to P10's `ReadBranchAt`
under `SparseCoreCapHyp` (explicit input-free constant `restartModelConst`). -/
theorem restartBranchCost_read_le_singleBundleRestartMachCost
    {slotCap cap eCap vCap tCap L_w P_fp capExp limbMul L_cap k : ℕ}
    {R : DSRep ReadView} (P : DSParams) (p : Program) (fBun b : ℕ)
    (readIdx : ℕ → ℕ) (fRoot : ℕ) (Q : RootQueryAt P.w p fRoot) (readMul : ℕ)
    (I5 : BunRestartAt P.w slotCap eCap k p fBun)
    (hLoc : R.Local)
    (hB : ReadBranchAt R P.w vCap eCap tCap L_w P_fp P cap p b readIdx fRoot Q readMul)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (v : ReadView)
    (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound)
    (hCap5 : SparseCoreCapHyp capExp limbMul L_cap tr.m₀ tr.n₀ vCap eCap)
    (hCap7 : SparseCoreCapHyp capExp limbMul L_cap tr.m₀ tr.n₀ P.vCap P.eCap) :
    let I7 := scurRebuildAt_of_readBranchAt hLoc hB
    I5.mul * (tr.cs.G.m + slots.length + 1) * ordStoreLog eCap +
      (slots.map fun s => spanActivateCost P (restartSlotGraph S tr.cs ord tr.k s)).sum +
      (I7.mul + 2 * I7.rootCost) *
        (I7.size v (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1) *
        ordStoreLog P.eCap +
      200 * slots.length + 200 ≤
    restartModelConst I5.mul readMul Q.cost capExp *
      singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  have hc1 : 1 ≤ tr.spanConst := le_trans (one_le_dsAmortConst P.impl) hC
  exact restartBranchCost_le_singleBundleRestartMachCost P p fBun (b + readIdx 3) I5
    (scurRebuildAt_of_readBranchAt hLoc hB) S6 v ord 2 (capExp + 1) hMap hMatch hok hP hC
    (le_of_eq hSB) (rebuildSize_restartSpanState_le_two_mul_inner P S6 ord hMap hMatch hSB hc1 hok)
    (ordStoreLog_le_of_capHyp hCap5) (ordStoreLog_le_of_capHyp hCap7)

/-- Unit-time-factor (`P.impl.γ_t P.mMax = 1`) form of `SparsifyParamsLe` for
`tr.spanParams = canonicalSparsifyParams P.impl P.mMax` (as in `sparseCoreProgTool`). -/
theorem sparsifyParamsLe_absorb_of_unit (impl : SparsifyImpl) (mMax : ℕ)
    (hγt : impl.γ_t mMax = 1) :
    SparsifyParamsLe (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsifyParams impl mMax) := by
  rw [canonicalSparsifyParams_absorbTime_eq_of_unit impl mMax hγt]
  exact sparsifyParamsLe_refl _

/-! ## End-to-end model-linked branch restart theorem -/

/-- **Model-linked restart of a branch.** Runs `restartBranchStmt` with P5 (`I5`, whose bundle
cap is the cap `tr.k` of the branch), P6 (`bucketSpannerProcs`), and P10 (`ReadBranchAt`), and
proves that P5's invariant `I5.inv` holds again and that:
1. the new bundle table matches `tr' := restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord`
   up to `BunAgree` (and `GraphEq` on bundle graphs);
2. the new bucket spanner table holds `some ⟨tr'.initBunG (C, b), []⟩` with `DSHist.state P = tr'.dyn (C, b)`
   literally for every active `(C, b)`;
3. P10's rebuilt `ReadView` has `v'.G = tr'.cs.G`, `v'.lsf = tr'.cs.lsf`, and `GraphEq v'.S tr'.S_cur`;
4. the amortized cost is at most `restartModelConst I5.mul readMul Q.cost capExp` times
   `singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord`.
P7's marks are left untouched (P9's branch layer calls P7's reset after P8). -/
theorem restartBranch_model_runs
    {slotCap cap eCap vCap tCap L_w P_fp capExp limbMul L_cap k : ℕ}
    {R : DSRep ReadView} (P : DSParams) (p : Program)
    (f fBun bSpan bRead : ℕ) (readIdx : ℕ → ℕ) (fRoot : ℕ)
    (Q : RootQueryAt P.w p fRoot) (readMul : ℕ)
    (I5 : BunRestartAt P.w slotCap eCap k p fBun)
    (hLoc : R.Local)
    (hB : ReadBranchAt R P.w vCap eCap tCap L_w P_fp P cap p bRead readIdx fRoot Q readMul)
    (bunTbl tourH spanTbl scurH slotsPtr h b4 j : ℕ) (slots : List ℕ)
    (slotOf : Finset ℕ × ℤ → ℕ)
    (S : Fin slotCap → Option BundleState) (x : I5.rep.τ) (cord : ℕ → List End) (tx : I5.tour.τ)
    (S6 : BucketSpannerState cap) (x6 : (bucketSpannerRep P cap).τ)
    (v : ReadView) (y : R.τ) (s4 : Q.σ) (x4 : Q.R.τ)
    (tr : BundleTreeState P.L) (ord : ℕ → List End)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (spaceBound : ℕ)
    (hf : p.procs[f]? = some (restartBranchStmt fBun (bSpan + bsIdxOp0 + 0) (bRead + readIdx 3)))
    (hp : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    (hbunW : bunTbl < 2 ^ P.w) (htourW : tourH < 2 ^ P.w) (hspanW : spanTbl < 2 ^ P.w)
    (hscurW : scurH < 2 ^ P.w) (hslotsPtrW : slotsPtr < 2 ^ P.w) (hhW : h < 2 ^ P.w)
    (hb4W : b4 < 2 ^ P.w) (hjW : j < 2 ^ P.w)
    (hLW : P.L < 2 ^ P.w) (hSplitW : P.splitBound < 2 ^ P.w)
    (hVW : P.vCap < 2 ^ P.w) (hEW : P.eCap < 2 ^ P.w) (hw16 : 16 ≤ 2 ^ P.w)
    (hlist : ListAt mem slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h)
    (hfree : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length →
      ¬ I5.rep.foot bunTbl x a ∧ ¬ I5.tour.foot tourH tx a ∧
        ¬ (bucketSpannerRep P cap).foot spanTbl x6 a ∧ ¬ R.foot scurH y a)
    (hMap : SlotMapOK tr slotCap cap slots slotOf)
    (hMatch : BunTableMatches tr slotOf S)
    (hS6act : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hkk : tr.k = k) (hk : 1 ≤ tr.k) (hcord : CoreCordOf tr.cs ord cord) (hinv : I5.inv S cord)
    (hMod : RestartScurModelInv tr)
    (hvG : v.G = tr.cs.G) (hvLSF : v.lsf = tr.cs.lsf) (hvS : GraphEq v.S tr.S_cur)
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound)
    (hCap5 : SparseCoreCapHyp capExp limbMul L_cap tr.m₀ tr.n₀ vCap eCap)
    (hCap7 : SparseCoreCapHyp capExp limbMul L_cap tr.m₀ tr.n₀ P.vCap P.eCap)
    (hrep5 : I5.rep.rep bunTbl S x mem) (hrepT : I5.tour.rep tourH cord tx mem)
    (hrep6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem) (hrep7 : R.rep scurH v y mem)
    (hrep4 : Q.R.rep b4 s4 x4 mem)
    (hroots : ∀ u ∈ v.G.V, Q.ok s4 j u ∧ Q.root s4 j u = v.lsf.F.root u)
    (hdisj : FeetDisjoint (I5.rep.foot bunTbl x) (I5.tour.foot tourH tx)
      ((bucketSpannerRep P cap).foot spanTbl x6) (R.foot scurH y))
    (d54 : ∀ a, I5.rep.foot bunTbl x a → ¬ Q.R.foot b4 x4 a)
    (dT4 : ∀ a, I5.tour.foot tourH tx a → ¬ Q.R.foot b4 x4 a)
    (d64 : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → ¬ Q.R.foot b4 x4 a)
    (d74 : ∀ a, R.foot scurH y a → ¬ Q.R.foot b4 x4 a)
    (hf5 : ∀ a, I5.rep.foot bunTbl x a → a < h) (hfT : ∀ a, I5.tour.foot tourH tx a → a < h)
    (hf6 : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → a < h)
    (hf7 : ∀ a, R.foot scurH y a → a < h) (hf4 : ∀ a, Q.R.foot b4 x4 a → a < h)
    (hz : ZeroFrom mem h)
    (hspaceSum : I5.space (tr.cs.G.m + slots.length) +
        (slots.map fun s => spanActivateSpace P (restartSlotGraph S tr.cs ord tr.k s)).sum +
        readSpace readMul vCap tCap L_w
          (rebuildSize P (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length) ≤
      spaceBound)
    (hspaceW : h + spaceBound < 2 ^ P.w) :
    let tr' := restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord
    let S6' := restartSpanState S6 S tr.cs ord tr.k slots
    let v' := v.rebuild P S6' slots
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c S' x' tx' x6' y' x4',
      Runs P.w p ω body
        (startState [bunTbl, tourH, spanTbl, scurH, slots.length, slotsPtr, h, b4, j,
          P.splitBound, P.vCap, P.eCap, P.L] mem pos)
        o st' c ∧
      I5.rep.rep bunTbl S' x' st'.mem ∧ I5.tour.rep tourH cord tx' st'.mem ∧ I5.inv S' cord ∧
      (bucketSpannerRep P cap).rep spanTbl S6' x6' st'.mem ∧
      R.rep scurH v' y' st'.mem ∧ Q.R.rep b4 s4 x4' st'.mem ∧
      (∀ i : Fin slotCap, i.1 ∉ slots → S' i = S i) ∧
      BunTableMatches tr' slotOf S' ∧
      (∀ p ∈ activePairs tr, ∃ (hs : slotOf p < slotCap) (B' : BundleState),
        S' ⟨slotOf p, hs⟩ = some B' ∧ GraphEq B'.graph (tr'.bun p).graph) ∧
      (∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
        ∃ (hs : slotOf (C, b) < cap) (d : DSHist),
          S6' ⟨slotOf (C, b), hs⟩ = some d ∧ d = ⟨tr'.initBunG (C, b), []⟩ ∧
          d.state P = tr'.dyn (C, b)) ∧
      v'.G = tr'.cs.G ∧ v'.lsf = tr'.cs.lsf ∧ GraphEq v'.S tr'.S_cur ∧
      h ≤ o.value ∧ o.value ≤ h + spaceBound ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ I5.rep.foot bunTbl x a → ¬ I5.tour.foot tourH tx a →
        ¬ (bucketSpannerRep P cap).foot spanTbl x6 a → ¬ R.foot scurH y a →
        ¬ Q.R.foot b4 x4 a → st'.mem a = mem a) ∧
      (∀ a, I5.rep.foot bunTbl x' a → I5.rep.foot bunTbl x a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, I5.tour.foot tourH tx' a → I5.tour.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6' a →
        (bucketSpannerRep P cap).foot spanTbl x6 a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, R.foot scurH y' a → R.foot scurH y a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, Q.R.foot b4 x4' a → Q.R.foot b4 x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
      FeetDisjoint (I5.rep.foot bunTbl x') (I5.tour.foot tourH tx')
        ((bucketSpannerRep P cap).foot spanTbl x6') (R.foot scurH y') ∧
      (∀ a, I5.rep.foot bunTbl x' a → ¬ Q.R.foot b4 x4' a) ∧
      (∀ a, I5.tour.foot tourH tx' a → ¬ Q.R.foot b4 x4' a) ∧
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6' a → ¬ Q.R.foot b4 x4' a) ∧
      (∀ a, R.foot scurH y' a → ¬ Q.R.foot b4 x4' a) ∧
      c + I5.rep.phi bunTbl x' st'.mem + I5.tour.phi tourH tx' st'.mem +
          (bucketSpannerRep P cap).phi spanTbl x6' st'.mem + R.phi scurH y' st'.mem +
          Q.R.phi b4 x4' st'.mem ≤
        restartModelConst I5.mul readMul Q.cost capExp *
          singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord +
          (I5.rep.phi bunTbl x mem + I5.tour.phi tourH tx mem +
            (bucketSpannerRep P cap).phi spanTbl x6 mem + R.phi scurH y mem +
            Q.R.phi b4 x4 mem) := by
  intro tr' S6' v'
  subst hkk
  set I7 := scurRebuildAt_of_readBranchAt hLoc hB
  have hSact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B ∧
      B.edges ⊆ (coreGraph tr.cs.G tr.cs.lsf).E := by
    intro s hs
    obtain ⟨⟨C, b⟩, hp, rfl⟩ := hMap.2.2.1 s hs
    have ⟨hC, hb⟩ := mem_activePairs.mp hp
    obtain ⟨hs', B, hSB, hag⟩ := hMatch (C, b) hp
    exact ⟨hs', B, hSB, hag.2.1 ▸ (hMod.2.2.2.2 C hC b hb).1⟩
  obtain ⟨body, hb, o, st', c, S', x', tx', x6', y', x4', hrun, hrep5', hrepT', hinv', hrep6',
      hrep7', hrep4', hSoth, hSlot, hlo, hhi, hz', hfr, hft5, hftT, hft6, hft7, hft4, hdisj', d54',
      dT4', d64', d74', hcost⟩ :=
    restartBranch_runs P cap p f fBun bSpan (bRead + readIdx 3) I5 I7
      bunTbl tourH spanTbl scurH slotsPtr h b4 j slots S x cord tx S6 x6 v y s4 x4
      tr.cs ord mem pos ω spaceBound hf hp hbunW htourW hspanW hscurW hslotsPtrW hhW hb4W hjW
      hLW hSplitW hVW hEW hw16 hlist hlist_h hMap.1 hfree hSact hS6act hok hk hcord hinv hrep5 hrepT
      hrep6 hrep7 hrep4 hroots hdisj d54 dT4 d64 d74 hf5 hfT hf6 hf7 hf4 hz hspaceSum hspaceW
  obtain ⟨hMatch', hGraphEq'⟩ :=
    restart_bun_agree (fun _ => canonicalSparsify P.impl) hMap hMatch ord hSlot
  have hScur' := readViewRebuild_graphEq_restart_S_cur P S6 hMap hMatch hSB hcord hMod hok
    hvG hvLSF hvS
  have hCostBnd := restartBranchCost_read_le_singleBundleRestartMachCost P p fBun bRead readIdx
    fRoot Q readMul I5 hLoc hB S6 v ord hMap hMatch hok hP hC hSB hCap5 hCap7
  refine ⟨body, hb, o, st', c, S', x', tx', x6', y', x4', hrun, hrep5', hrepT', hinv', hrep6',
    hrep7', hrep4', hSoth, hMatch', hGraphEq', fun C hC b hb =>
      restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB hC hb,
    hScur'.1, hScur'.2.1, hScur'.2.2, hlo, hhi, hz', hfr, hft5, hftT, hft6, hft7, hft4, hdisj',
    d54', dT4', d64', d74', le_trans hcost (Nat.add_le_add_right hCostBnd _)⟩

/-- Links `singleBundleRestartMachCost` directly to the cost increase `T.cost (T.restart st j) - T.cost st`
of `sparseCoreBundleRestartToolMachWith` on a nonempty state with `j < st.k`. -/
theorem restartBranch_toolMach_cost_eq (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (impl : SparsifyImpl) (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) (j : ℕ) (hne : st.isNonempty = true) (hj : j < st.k) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L (fun _ => canonicalSparsify impl)
      params spanConst
    T.cost (T.restart st j) - T.cost st =
      singleBundleRestartMachCost L (fun _ => canonicalSparsify impl) (st.trees j) st.ord := by
  intro T
  rw [bundleRestartToolMachWith_restart_cost_eq lsfInit C_lsst L (fun _ => canonicalSparsify impl)
    params spanConst st j hne hj, Nat.add_sub_cancel_left]

end

end MinCostFlow.SparseCore.Program.Restart
