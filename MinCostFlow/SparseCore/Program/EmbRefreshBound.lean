module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartFrame
public import MinCostFlow.SparseCore.Program.RestartModelCost

import MinCostFlow.DynSpanner.RebuildSpec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cost bounds for the embedding-table refresh after a restart (`EmbRefreshBound`)

After a branch restart, every active slot `s` of the bucket spanners holds a freshly initialized
dynamic spanner `d = ⟨Hb, []⟩` on the normalized restarted bundle graph `Hb`. Its walks live at
level `0` and have length bounded by `γ_ℓ` (`initCore_spec`, `lenBound γ_ℓ 0 = γ_ℓ`), so the total
word length of the refreshed walks of slot `s` is at most `3 * spanInitBound Pa L splitBound Hb`.

This file defines two sharper refresh-size measures alongside `embRefreshSize`:
* `embRefreshWalkSize P S6 slots`: the word count of the walks without the `+ P.L` level-scan term
  per edge;
* `embRefreshSizeAt P S6 slots`: adds `+ P.L` per edge only for slots whose history `d.Us` is
  nonempty, and `0` for freshly initialized slots (`d.Us = []`).

Main results:
* `piTotal_init_eq` and `piTotal_init_length_le`: for `d = ⟨Hb, []⟩`, `piTotal (d.state P) e` is
  the level-`0` walk `(initCore Hb (canonicalSparsify P.impl)).2.1 e`, of length at most `Pa.γ_ℓ`.
* `embRefreshWalkSize_restartSpanState_le_inner` and `_le_machCost`:
  `embRefreshWalkSize P (restartSpanState ...) slots + slots.length + 1` is at most
  `4 * singleRestartInner tr ord` and at most `4 * singleBundleRestartMachCost ...`.
* `embRefreshSizeAt_restartSpanState_eq_walkSize` and `_le_machCost`: on `restartSpanState`,
  `embRefreshSizeAt` equals `embRefreshWalkSize`, so it is also bounded by
  `4 * singleBundleRestartMachCost ...` with no dependence on `P.L`.
* `embRefreshSize_restartSpanState_le_inner` and `_le_machCost_of_depth`: with the `+ P.L` term
  kept, `embRefreshSize P (restartSpanState ...) slots + slots.length + 1` is at most
  `(P.L + 4) * singleRestartInner tr ord`, and hence at most
  `(cL + 4) * singleBundleRestartMachCost ...` whenever `P.L ≤ cL * bundleLogFactor tr.m₀ tr.n₀`.
* `embRefreshSize_ge_L_mul_edges`: lower bound showing `P.L * ∑_{s ∈ slots} |slotGE s|` sits inside
  `embRefreshSize` (so `embRefreshSize` cannot be bounded by a constant independent of `P.L` times
  `singleBundleRestartMachCost` without either bounding `P.L` or dropping `+ P.L` on fresh slots).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Walk-only and history-adaptive refresh sizes -/

@[expose] public section

/-- The word count of a refresh without the `+ P.L` level-scan term per edge: for each listed slot
and each edge of its graph, `walkWords (slotWalk ...) + 2`, plus `1` per slot. -/
noncomputable def embRefreshWalkSize (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) : ℕ :=
  (slots.map fun s =>
    ((slotGE P S6 s).sum fun e => Read.walkWords (slotWalk P S6 s e) + 2) + 1).sum

/-- The history-adaptive refresh size: for each listed slot `s`, adds `+ P.L` per edge only when the
slot's spanner history `d.Us` is nonempty, and `+ 0` when `d.Us = []` (as after a restart). -/
noncomputable def embRefreshSizeAt (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) : ℕ :=
  (slots.map fun s =>
    if hs : s < cap then
      match S6 ⟨s, hs⟩ with
      | some d =>
          ((d.state P).G.E.sum fun e =>
            Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) + 1
      | none => 1
    else 1).sum

end

/-! ## Private helpers for `findEmbLevel` and `spanInitBound` -/

private lemma findEmbLevel_init_eq_zero {L : ℕ} (E : Finset ℕ) (e : ℕ) :
    findEmbLevel (L := L) (fun i => if i.1 = 0 then E else ∅) (L + 1) e = 0 := by
  unfold findEmbLevel
  rw [Nat.min_self]
  have hnone : ∀ l : List ℕ, (∀ i ∈ l, i ≠ 0) →
      l.find? (fun i => if h : i < L + 1 then decide (e ∈ if i = 0 then E else ∅) else false) =
        none := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.find?_cons]
      have hx : x ≠ 0 := hl x (by simp)
      have hpred : (if h : x < L + 1 then decide (e ∈ if x = 0 then E else ∅) else false) = false := by
        split_ifs with hlt
        · simp
        · rfl
      rw [hpred]
      exact ih fun y hy => hl y (by simp [hy])
  have hrev : (List.range (L + 1)).reverse =
      ((List.range L).map (· + 1)).reverse ++ [0] := by
    rw [List.range_succ_eq_map, List.reverse_cons]
  rw [hrev, List.find?_append]
  have hpos : ∀ i ∈ ((List.range L).map (· + 1)).reverse, i ≠ 0 := by
    intro i hi
    rw [List.mem_reverse, List.mem_map] at hi
    obtain ⟨k, -, rfl⟩ := hi
    omega
  rw [hnone _ hpos, Option.none_or]
  cases h : ([0] : List ℕ).find?
      (fun i => if h : i < L + 1 then decide (e ∈ if i = 0 then E else ∅) else false) with
  | none => rfl
  | some v =>
    have hv := List.mem_of_find?_eq_some h
    simp only [List.mem_singleton] at hv
    subst hv
    rfl

private lemma walk_sum_le_spanInitBound_real (P_b : SparsifyParams) (L splitBound : ℕ)
    (Hb : MGraph) :
    (3 : ℝ) * (Hb.m : ℝ) + 2 * (Hb.m : ℝ) * P_b.γ_ℓ + 1 ≤
      3 * (spanInitBound P_b L splitBound Hb : ℝ) := by
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
  have ht3 : 0 ≤ (Hb.n : ℝ) + ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) := by
    positivity
  have hB : (Hb.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ + 1 ≤
      P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) +
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) + 1 := by
    linarith
  have hceil := Nat.le_ceil
    (P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) +
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) + 1)
  have hmγ : 0 ≤ (Hb.m : ℝ) * P_b.γ_ℓ := by positivity
  push_cast at hB hceil ⊢
  linarith

/-! ## Public comparison and walk-length lemmas -/

public section

/-- `embRefreshSizeAt` is always at most `embRefreshSize`. -/
theorem embRefreshSizeAt_le_embRefreshSize (P : DSParams) {cap : ℕ}
    (S6 : BucketSpannerState cap) (slots : List ℕ) :
    embRefreshSizeAt P S6 slots ≤ embRefreshSize P S6 slots := by
  unfold embRefreshSizeAt embRefreshSize
  induction slots with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    by_cases hs : s < cap
    · simp only [hs, ↓reduceDIte, slotGE]
      cases hS : S6 ⟨s, hs⟩ with
      | none => simp
      | some d =>
        simp only [Nat.add_le_add_iff_right]
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs <;> omega
    · simp [hs, slotGE]

/-- `embRefreshWalkSize` is always at most `embRefreshSizeAt`. -/
theorem embRefreshWalkSize_le_embRefreshSizeAt (P : DSParams) {cap : ℕ}
    (S6 : BucketSpannerState cap) (slots : List ℕ) :
    embRefreshWalkSize P S6 slots ≤ embRefreshSizeAt P S6 slots := by
  unfold embRefreshWalkSize embRefreshSizeAt
  induction slots with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    by_cases hs : s < cap
    · simp only [hs, ↓reduceDIte, slotGE]
      cases hS : S6 ⟨s, hs⟩ with
      | none => simp
      | some d =>
        simp only [Nat.add_le_add_iff_right]
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs <;> omega
    · simp [hs, slotGE]

/-- When every active listed slot is freshly initialized (`d.Us = []`), `embRefreshSizeAt` equals
`embRefreshWalkSize`. -/
theorem embRefreshSizeAt_eq_walkSize (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ)
    (hfresh : ∀ s ∈ slots, ∀ (hs : s < cap) (d : DSHist), S6 ⟨s, hs⟩ = some d → d.Us = []) :
    embRefreshSizeAt P S6 slots = embRefreshWalkSize P S6 slots := by
  unfold embRefreshSizeAt embRefreshWalkSize
  congr 1
  refine List.map_congr_left fun s hsMem => ?_
  by_cases hs : s < cap
  · simp only [hs, ↓reduceDIte, slotGE]
    cases hS : S6 ⟨s, hs⟩ with
    | none => simp
    | some d =>
      have hUs := hfresh s hsMem hs d hS
      simp [hUs]
  · simp [hs, slotGE]

/-- Exact split of `embRefreshSize` into `embRefreshWalkSize` plus `P.L` per graph edge of each
listed slot. -/
theorem embRefreshSize_eq_walkSize_add (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) :
    embRefreshSize P S6 slots =
      embRefreshWalkSize P S6 slots +
        P.L * (slots.map fun s => (slotGE P S6 s).card).sum := by
  unfold embRefreshSize embRefreshWalkSize
  induction slots with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
    have hslot :
        ((slotGE P S6 s).sum fun e => Read.walkWords (slotWalk P S6 s e) + P.L + 2) =
        ((slotGE P S6 s).sum fun e => Read.walkWords (slotWalk P S6 s e) + 2) +
          P.L * (slotGE P S6 s).card := by
      have hrw : (fun e => Read.walkWords (slotWalk P S6 s e) + P.L + 2) =
          (fun e => (Read.walkWords (slotWalk P S6 s e) + 2) + P.L) := by
        funext e; omega
      rw [hrw, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    omega

/-- Lower bound showing that `P.L` times the total number of edges in the listed slots sits inside
`embRefreshSize`. -/
theorem embRefreshSize_ge_L_mul_edges (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) :
    P.L * (slots.map fun s => (slotGE P S6 s).card).sum ≤ embRefreshSize P S6 slots := by
  rw [embRefreshSize_eq_walkSize_add]
  exact Nat.le_add_left _ _

/-- In a freshly initialized spanner `d = ⟨Hb, []⟩`, `piTotal (d.state P) e` is the level-`0`
embedding `(initCore Hb (canonicalSparsify P.impl)).2.1 e`. -/
theorem piTotal_init_eq (P : DSParams) (Hb : MGraph) (e : ℕ) :
    piTotal (DSHist.state P ⟨Hb, []⟩) e =
      (initCore Hb (canonicalSparsify P.impl)).2.1 e := by
  rw [dsHist_state_nil]
  unfold piTotal piLe piLt piLtFrom init initAt
  dsimp only
  rw [findEmbLevel_init_eq_zero]
  simp

/-- Every edge `e ∈ Hb.E` of a freshly initialized spanner `⟨Hb, []⟩` has `piTotal` walk length at
most `Pa.γ_ℓ`, where `Pa = (canonicalSparsifyParams P.impl P.mMax).absorbTime`. -/
theorem piTotal_init_length_le (P : DSParams) {Hb : MGraph} (hVal : Hb.IsValid)
    (hGm : Hb.m ≤ P.mMax) {e : ℕ} (he : e ∈ Hb.E) :
    ((piTotal (DSHist.state P ⟨Hb, []⟩) e).length : ℝ) ≤
      (canonicalSparsifyParams P.impl P.mMax).absorbTime.γ_ℓ := by
  rw [piTotal_init_eq]
  have hspec := initCore_spec (canonicalSparsify_spec_absorb P.impl P.mMax) hVal hGm
  have hlen : ((initCore Hb (canonicalSparsify P.impl)).2.1 e).length ≤
      Embedding.length (initCore Hb (canonicalSparsify P.impl)).2.1 Hb :=
    Finset.le_sup (f := fun x => ((initCore Hb (canonicalSparsify P.impl)).2.1 x).length) he
  have hcast : (((initCore Hb (canonicalSparsify P.impl)).2.1 e).length : ℝ) ≤
      (Embedding.length (initCore Hb (canonicalSparsify P.impl)).2.1 Hb : ℝ) :=
    Nat.cast_le.mpr hlen
  exact le_trans hcast (by simpa [lenBound] using hspec.2.2.2.2.1)

/-- For a freshly initialized slot `S6 ⟨s, hs⟩ = some ⟨Hb, []⟩`, every edge `e ∈ Hb.E` has
`slotWalk` length at most `Pa.γ_ℓ`. -/
theorem slotWalk_init_length_le (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap}
    {s : ℕ} (hs : s < cap) {Hb : MGraph} (hS : S6 ⟨s, hs⟩ = some ⟨Hb, []⟩)
    (hVal : Hb.IsValid) (hGm : Hb.m ≤ P.mMax) {e : ℕ} (he : e ∈ Hb.E) :
    ((slotWalk P S6 s e).length : ℝ) ≤
      (canonicalSparsifyParams P.impl P.mMax).absorbTime.γ_ℓ := by
  unfold slotWalk
  simp only [hs, ↓reduceDIte, hS]
  split_ifs
  · simpa using (canonicalSparsifyParams P.impl P.mMax).absorbTime.hγ_ℓ
  · exact piTotal_init_length_le P hVal hGm he

/-- For a freshly initialized slot `S6 ⟨s, hs⟩ = some ⟨Hb, []⟩`, the walk-word sum of the slot is
at most `3 * spanInitBound Pa P.L P.splitBound Hb`. -/
theorem slotWalkWords_sum_le_spanInitBound (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap}
    {s : ℕ} (hs : s < cap) {Hb : MGraph} (hS : S6 ⟨s, hs⟩ = some ⟨Hb, []⟩)
    (hVal : Hb.IsValid) (hGm : Hb.m ≤ P.mMax) :
    ((slotGE P S6 s).sum fun e => Read.walkWords (slotWalk P S6 s e) + 2) + 1 ≤
      3 * spanInitBound (canonicalSparsifyParams P.impl P.mMax).absorbTime P.L P.splitBound Hb := by
  set Pa := (canonicalSparsifyParams P.impl P.mMax).absorbTime
  have hGE : slotGE P S6 s = Hb.E := by
    unfold slotGE
    simp only [hs, ↓reduceDIte, hS, dsHist_state_nil]
    rfl
  rw [hGE]
  have hreal :
      ((((Hb.E.sum fun e => Read.walkWords (slotWalk P S6 s e) + 2) + 1 : ℕ) : ℝ)) ≤
        3 * (spanInitBound Pa P.L P.splitBound Hb : ℝ) := by
    have hsum :
        ((Hb.E.sum fun e => Read.walkWords (slotWalk P S6 s e) + 2 : ℕ) : ℝ) ≤
          3 * (Hb.m : ℝ) + 2 * (Hb.m : ℝ) * Pa.γ_ℓ := by
      rw [Nat.cast_sum]
      calc ∑ e ∈ Hb.E, ((Read.walkWords (slotWalk P S6 s e) + 2 : ℕ) : ℝ)
          ≤ ∑ _e ∈ Hb.E, (3 + 2 * Pa.γ_ℓ) := by
            refine Finset.sum_le_sum fun e he => ?_
            have hl := slotWalk_init_length_le P hs hS hVal hGm he
            unfold Read.walkWords
            push_cast
            linarith
        _ = (Hb.m : ℝ) * (3 + 2 * Pa.γ_ℓ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; rfl
        _ = 3 * (Hb.m : ℝ) + 2 * (Hb.m : ℝ) * Pa.γ_ℓ := by ring
    have hbound := walk_sum_le_spanInitBound_real Pa P.L P.splitBound Hb
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  exact_mod_cast hreal

/-! ## Bounds on `restartSpanState` against `singleRestartInner` and `singleBundleRestartMachCost` -/

/-- The walk-word refresh size on `restartSpanState`, plus `slots.length + 1`, is at most
`4 * singleRestartInner tr ord`. -/
theorem embRefreshWalkSize_restartSpanState_le_inner {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound) :
    embRefreshWalkSize P (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1 ≤
      4 * singleRestartInner tr ord := by
  set S6' := restartSpanState S6 S tr.cs ord tr.k slots
  have hc1 : 1 ≤ tr.spanConst := le_trans (one_le_dsAmortConst P.impl) hC
  have hwalk : embRefreshWalkSize P S6' slots ≤
      3 * (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound
          (SparseCore.normGraph (restartBucketBundle tr ord C b).graph)) := by
    unfold embRefreshWalkSize
    rw [hMap.sum_map_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun C hCmem => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) (mem_activePairs.mpr ⟨hCmem, hb⟩)
    obtain ⟨hs, d, hd, rfl, -⟩ := restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB hCmem hb
    set Hb := SparseCore.normGraph (restartBucketBundle tr ord C b).graph
    have hInitEq :
        (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).initBunG (C, b) = Hb := by
      simp only [restartBundleTree, hCmem, ↓reduceIte, Hb]
    rw [hInitEq] at hd
    have hokHb : SpanGraphOK P Hb := by
      have h1 := hok _ hmem
      rwa [restartSlotGraph_eq_initBunG (fun _ => canonicalSparsify P.impl) hMatch ord hCmem hb,
        hInitEq] at h1
    have h1 := slotWalkWords_sum_le_spanInitBound P hs hd hokHb.2.2.2.2.2.2.1 hokHb.2.2.2.2.2.2.2.1
    have h2 := spanInitBound_mono (L := P.L) hP (le_of_eq hSB) Hb
    have h3 : spanInitBound tr.spanParams P.L tr.splitBound Hb ≤
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound Hb :=
      Nat.le_mul_of_pos_left _ hc1
    exact le_trans h1 (Nat.mul_le_mul_left 3 (le_trans h2 h3))
  have hslots := slots_length_add_le_singleRestartInner ord hMap hc1
  unfold singleRestartInner at hslots ⊢
  omega

/-- The walk-word refresh size on `restartSpanState`, plus `slots.length + 1`, is at most
`4 * singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord`. -/
theorem embRefreshWalkSize_restartSpanState_le_machCost {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound) :
    embRefreshWalkSize P (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1 ≤
      4 * singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  have h1 := embRefreshWalkSize_restartSpanState_le_inner P S6 ord hMap hMatch hok hP hC hSB
  have hlg : 1 ≤ bundleLogFactor tr.m₀ tr.n₀ := Nat.one_le_pow _ _ (Nat.succ_pos _)
  rw [singleBundleRestartMachCost_eq_inner]
  calc _ ≤ 4 * singleRestartInner tr ord := h1
    _ ≤ 4 * (singleRestartInner tr ord * bundleLogFactor tr.m₀ tr.n₀) :=
        Nat.mul_le_mul_left 4 (Nat.le_mul_of_pos_right _ hlg)

/-- Every active listed slot of `restartSpanState` is freshly initialized (`d.Us = []`). -/
theorem restartSpanState_fresh {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) :
    ∀ s ∈ slots, ∀ (hs : s < cap) (d : DSHist),
      restartSpanState S6 S tr.cs ord tr.k slots ⟨s, hs⟩ = some d → d.Us = [] := by
  intro s hsMem hs d hd
  obtain ⟨⟨C, b⟩, hp, rfl⟩ := hMap.2.2.1 s hsMem
  obtain ⟨hC, hb⟩ := mem_activePairs.mp hp
  obtain ⟨hs', d', hd', rfl, -⟩ := restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB hC hb
  have heq : some d = some ⟨(restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).initBunG (C, b), []⟩ := by
    rw [← hd, ← hd']
  cases Option.some.inj heq
  rfl

/-- On `restartSpanState`, `embRefreshSizeAt` equals `embRefreshWalkSize`. -/
theorem embRefreshSizeAt_restartSpanState_eq_walkSize {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hSB : P.splitBound = tr.splitBound) :
    embRefreshSizeAt P (restartSpanState S6 S tr.cs ord tr.k slots) slots =
      embRefreshWalkSize P (restartSpanState S6 S tr.cs ord tr.k slots) slots :=
  embRefreshSizeAt_eq_walkSize P _ slots (restartSpanState_fresh P S6 ord hMap hMatch hSB)

/-- The history-adaptive refresh size `embRefreshSizeAt` on `restartSpanState`, plus
`slots.length + 1`, is at most `4 * singleBundleRestartMachCost ...` (input-free constant `4`,
independent of `P.L`). -/
theorem embRefreshSizeAt_restartSpanState_le_machCost {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound) :
    embRefreshSizeAt P (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1 ≤
      4 * singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  rw [embRefreshSizeAt_restartSpanState_eq_walkSize P S6 ord hMap hMatch hSB]
  exact embRefreshWalkSize_restartSpanState_le_machCost P S6 ord hMap hMatch hok hP hC hSB

/-- The full `embRefreshSize` (including `+ P.L` per edge) on `restartSpanState`, plus
`slots.length + 1`, is at most `(P.L + 4) * singleRestartInner tr ord`. -/
theorem embRefreshSize_restartSpanState_le_inner {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound) :
    embRefreshSize P (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1 ≤
      (P.L + 4) * singleRestartInner tr ord := by
  set S6' := restartSpanState S6 S tr.cs ord tr.k slots
  have hc1 : 1 ≤ tr.spanConst := le_trans (one_le_dsAmortConst P.impl) hC
  have hwalk := embRefreshWalkSize_restartSpanState_le_inner P S6 ord hMap hMatch hok hP hC hSB
  have hedges : (slots.map fun s => (slotGE P S6' s).card).sum ≤ singleRestartInner tr ord := by
    rw [hMap.sum_map_eq]
    unfold singleRestartInner
    refine le_trans ?_ (Nat.le_add_left _ _)
    refine Finset.sum_le_sum fun C hCmem => Finset.sum_le_sum fun b hb => ?_
    set Hb := SparseCore.normGraph (restartBucketBundle tr ord C b).graph
    have hInitEq :
        (restartBundleTree P.L (fun _ => canonicalSparsify P.impl) tr ord).initBunG (C, b) = Hb := by
      simp only [restartBundleTree, hCmem, ↓reduceIte, Hb]
    have hGE : (slotGE P S6' (slotOf (C, b))).card = Hb.m := by
      rw [slotGE_restartSpanState P S6 ord hMap hMatch hSB hCmem hb, hInitEq]; rfl
    rw [hGE]
    have h1 := m_add_one_le_spanInitBound tr.spanParams P.L tr.splitBound Hb
    exact le_trans (by omega) (Nat.le_mul_of_pos_left _ hc1)
  rw [embRefreshSize_eq_walkSize_add]
  have hwalk' : embRefreshWalkSize P S6' slots + slots.length + 1 ≤ 4 * singleRestartInner tr ord :=
    hwalk
  have hLmul : P.L * (slots.map fun s => (slotGE P S6' s).card).sum ≤
      P.L * singleRestartInner tr ord :=
    Nat.mul_le_mul_left P.L hedges
  rw [Nat.add_mul]
  omega

/-- When `P.L ≤ cL * bundleLogFactor tr.m₀ tr.n₀`, the full `embRefreshSize` on `restartSpanState`,
plus `slots.length + 1`, is at most `(cL + 4) * singleBundleRestartMachCost ...`. -/
theorem embRefreshSize_restartSpanState_le_machCost_of_depth {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    {cL : ℕ} (hDepth : P.L ≤ cL * bundleLogFactor tr.m₀ tr.n₀)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound) :
    embRefreshSize P (restartSpanState S6 S tr.cs ord tr.k slots) slots + slots.length + 1 ≤
      (cL + 4) * singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  have h1 := embRefreshSize_restartSpanState_le_inner P S6 ord hMap hMatch hok hP hC hSB
  have hlg : 1 ≤ bundleLogFactor tr.m₀ tr.n₀ := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hmul : P.L + 4 ≤ (cL + 4) * bundleLogFactor tr.m₀ tr.n₀ := by
    rw [Nat.add_mul]
    have h4 : 4 ≤ 4 * bundleLogFactor tr.m₀ tr.n₀ := Nat.le_mul_of_pos_right 4 hlg
    omega
  rw [singleBundleRestartMachCost_eq_inner]
  calc _ ≤ (P.L + 4) * singleRestartInner tr ord := h1
    _ ≤ ((cL + 4) * bundleLogFactor tr.m₀ tr.n₀) * singleRestartInner tr ord :=
        Nat.mul_le_mul_right _ hmul
    _ = (cL + 4) * (singleRestartInner tr ord * bundleLogFactor tr.m₀ tr.n₀) := by ring

end

end MinCostFlow.SparseCore.Program
