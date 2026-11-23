module

public import MinCostFlow.SparseCore.Program.EmbRefreshBound
public import MinCostFlow.SparseCore.Program.SpanReadout
public import WordRAM.CopyWords

import MinCostFlow.DynSpanner.Program.DynSpannerDSPrefix
import Mathlib.Tactic.Ring

/-!
# Definitions and helper lemmas for the embedding-table refresh (`EmbRefreshDefs`)

Defines the deterministic Word-RAM refresh procedure `embRefreshStmt bCopy bPi` (with
`copyWords` at `bCopy` and `spanPiWalkPtrStmt` at `bPi`), its multiplier `embRefreshMul`, and the
pure view, layout, and fresh-spanner lemmas used by its verification (`EmbRefreshInner.lean`,
`EmbRefresh.lean`).

Given `[embH, spanH, slotsPtr, n, h]`, `embRefreshStmt` iterates over the `n` slots listed at
`slotsPtr`. For each slot `s`, it loads the bucket spanner handle `b = mem[spanH + s]` and scans
the edge list `dgEListBase (dsGPtr b) vCap eCap` of `G = (d.state P).G`:
* if `e ∈ H.E` (tested in `O(1)` via `dgEPresBase (dsHPtr b vCap eCap) vCap + e`), it writes the
  3-word encoding `[1, e, 1]` of `[(e, true)]` directly at the heap pointer `hp`, updates
  `mem[embH + 2 + e] := hp`, and advances `hp` by `3`;
* if `e ∉ H.E`, it obtains the walk pointer `wPtr` of `piTotal (d.state P) e`: directly from
  `mem[dsPiPtrBase b L vCap eCap + e]` in `O(1)` time when `mem[b + dsTOff] = 0` (a freshly
  initialized spanner, as after every restart), and via `bPi [b, e]` (`spanPiWalkPtrStmt`)
  otherwise; it then copies the `1 + 2 * mem[wPtr]` walk words to `hp` with `bCopy`, updates
  `mem[embH + 2 + e] := hp`, and advances `hp`.

Because `EmbView.refresh` selects a slot containing `e` with `Classical.choose`, a deterministic
refresh agrees with `EmbView.refresh` whenever any two listed slots that share an edge assign it
the same walk (`SlotWalkAgree`), which holds automatically when active bundles are edge-disjoint
(`slotWalkAgree_of_disjoint`, `slotWalkAgree_restartSpanState`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Procedure definitions -/

@[expose] public section

/-- Cost and space multiplier of `embRefreshStmt`. -/
def embRefreshMul : ℕ := 300

/-- Inner loop body of the embedding-table refresh: processes edge `e = mem[reg 16 + reg 21]`,
updating the embedding table (`reg 5`) and advancing the heap pointer (`reg 4`). -/
def embRefreshEdgeBody (bCopy bPi : ℕ) : Stmt :=
  .assign 22 (.load (.bin .add (.reg 16) (.reg 21))) ;;
  .assign 23 (.load (.bin .add (.reg 18) (.reg 22))) ;;
  .cond (.reg 23)
    (.store (.reg 4) (.const 1) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.reg 22) ;;
     .store (.bin .add (.reg 4) (.const 2)) (.const 1) ;;
     .store (.bin .add (.reg 5) (.reg 22)) (.reg 4) ;;
     .assign 4 (.bin .add (.reg 4) (.const 3)))
    (.cond (.reg 9)
       (.call 24 bPi [.reg 8, .reg 22])
       (.assign 24 (.load (.bin .add (.reg 19) (.reg 22)))) ;;
     .assign 25 (.bin .add (.const 1) (.bin .mul (.const 2) (.load (.reg 24)))) ;;
     .call 26 bCopy [.reg 24, .reg 4, .reg 25] ;;
     .store (.bin .add (.reg 5) (.reg 22)) (.reg 4) ;;
     .assign 4 (.bin .add (.reg 4) (.reg 25)))

/-- Outer loop body of the embedding-table refresh: loads slot `s = mem[reg 2 + reg 6]` and its
spanner handle `b = mem[reg 1 + s]`, computes the graph and level-0 walk table base addresses, and
runs the inner loop over all edges of the slot's graph. -/
def embRefreshSlotBody (bCopy bPi : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 2) (.reg 6))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.const dsTOff))) ;;
  .assign 10 (.load (.bin .add (.reg 8) (.const dsLOff))) ;;
  .assign 11 (.load (.bin .add (.reg 8) (.const dsVCapOff))) ;;
  .assign 12 (.load (.bin .add (.reg 8) (.const dsECapOff))) ;;
  .assign 13 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 11)) (.bin .mul (.const 9) (.reg 12)))) ;;
  .assign 14 (.bin .add (.reg 8) (.const dsHdrSize)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 13)) ;;
  .assign 16 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 4))
    (.bin .mul (.const 7) (.reg 11))) (.reg 12)) ;;
  .assign 17 (.load (.bin .add (.reg 14) (.const dgMOff))) ;;
  .assign 18 (.bin .add (.bin .add (.reg 15) (.const 4))
    (.bin .mul (.const 7) (.reg 11))) ;;
  .assign 20 (.bin .add (.reg 10) (.const 1)) ;;
  .assign 19 (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 13)))
    (.bin .add (.bin .mul (.const 3) (.reg 12)) (.bin .mul (.const 2) (.reg 20)))) ;;
  .assign 19 (.bin .add (.bin .add (.reg 19) (.reg 20))
    (.bin .mul (.reg 20) (.reg 12))) ;;
  forRange 21 (.const 0) (.reg 17) (embRefreshEdgeBody bCopy bPi)

/-- **The embedding-table refresh procedure**, `[embH, spanH, slotsPtr, n, h]`, calling
`copyWords` at `bCopy` and `spanPiWalkPtrStmt` at `bPi`. Returns the new heap pointer. -/
def embRefreshStmt (bCopy bPi : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  forRange 6 (.const 0) (.reg 3) (embRefreshSlotBody bCopy bPi) ;;
  .ret (.reg 4)

/-- Walk-agreement condition for `EmbView.refresh`: if two listed slots both contain edge `e`, they
assign it the same `slotWalk`. -/
def SlotWalkAgree (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (slots : List ℕ) : Prop :=
  ∀ s₁ ∈ slots, ∀ s₂ ∈ slots, ∀ e ∈ slotGE P S6 s₁, e ∈ slotGE P S6 s₂ →
    slotWalk P S6 s₁ e = slotWalk P S6 s₂ e

/-- The per-slot work unit counted in `embRefreshSizeAt`. -/
noncomputable def slotRefreshSizeAt (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) : ℕ :=
  if hs : s < cap then
    match S6 ⟨s, hs⟩ with
    | some d =>
        ((d.state P).G.E.sum fun e =>
          Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) + 1
    | none => 1
  else 1

/-- The exact walk-words allocated by refreshing slot `s`. -/
noncomputable def slotWalkWords (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) : ℕ :=
  (slotGE P S6 s).sum fun e => Read.walkWords (slotWalk P S6 s e)

end

/-! ## Determinism and pure view lemmas -/

public section

theorem embRefreshStmt_noRand (bCopy bPi : ℕ) : (embRefreshStmt bCopy bPi).NoRand := by
  simp [embRefreshStmt, embRefreshSlotBody, embRefreshEdgeBody, forRange, forUp, Stmt.NoRand]

/-- Pairwise disjointness of `slotGE` across distinct listed slots implies `SlotWalkAgree`. -/
theorem slotWalkAgree_of_disjoint {P : DSParams} {cap : ℕ} {S6 : BucketSpannerState cap}
    {slots : List ℕ}
    (hdisj : ∀ s₁ ∈ slots, ∀ s₂ ∈ slots, s₁ ≠ s₂ → Disjoint (slotGE P S6 s₁) (slotGE P S6 s₂)) :
    SlotWalkAgree P S6 slots := by
  intro s₁ hs₁ s₂ hs₂ e he₁ he₂
  by_cases heq : s₁ = s₂
  · subst heq; rfl
  · exact absurd he₂ (Finset.disjoint_left.mp (hdisj s₁ hs₁ s₂ hs₂ heq) he₁)

/-- After a branch restart, `restartSpanState` satisfies `SlotWalkAgree` under `BunDisjointInv`. -/
theorem slotWalkAgree_restartSpanState {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) {ord cord : ℕ → List End}
    (hcord : CoreCordOf tr.cs ord cord) (hMap : SlotMapOK tr slotCap cap slots slotOf)
    (hMatch : BunTableMatches tr slotOf S) (hSB : P.splitBound = tr.splitBound)
    (hBD : BunDisjointInv tr) :
    SlotWalkAgree P (restartSpanState S6 S tr.cs ord tr.k slots) slots := by
  refine slotWalkAgree_of_disjoint fun s₁ hs₁ s₂ hs₂ hne => ?_
  obtain ⟨q₁, hq₁, rfl⟩ := hMap.2.2.1 s₁ hs₁
  obtain ⟨q₂, hq₂, rfl⟩ := hMap.2.2.1 s₂ hs₂
  have hqne : q₁ ≠ q₂ := fun h => hne (congrArg slotOf h)
  have h1 := (slotGE_restart (P := P) (fun _ => canonicalSparsify P.impl) hcord hq₁
    (restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB
      (mem_activePairs.mp hq₁).1 (mem_activePairs.mp hq₁).2)).1
  have h2 := (slotGE_restart (P := P) (fun _ => canonicalSparsify P.impl) hcord hq₂
    (restartSpanState_state_eq_dyn P S6 ord hMap hMatch hSB
      (mem_activePairs.mp hq₂).1 (mem_activePairs.mp hq₂).2)).1
  rw [h1, h2]
  exact hBD.1 q₁ hq₁ q₂ hq₂ hqne

/-- Under `SlotWalkAgree`, any view whose domain is `v.dom ∪ slotsGE P S6 slots`, agreeing with
some covering slot on `slotsGE` and with `v.emb` outside `slotsGE`, equals `v.refresh P S6 slots`. -/
theorem embView_eq_refresh {P : DSParams} {cap : ℕ} {S6 : BucketSpannerState cap}
    {slots : List ℕ} {v v' : EmbView}
    (hAgree : SlotWalkAgree P S6 slots)
    (hdom : v'.dom = v.dom ∪ slotsGE P S6 slots)
    (hin : ∀ e ∈ slotsGE P S6 slots, ∃ s ∈ slots, e ∈ slotGE P S6 s ∧ v'.emb e = slotWalk P S6 s e)
    (hout : ∀ e, e ∉ slotsGE P S6 slots → v'.emb e = v.emb e) :
    v' = v.refresh P S6 slots := by
  classical
  cases v; cases v'
  simp only [EmbView.refresh, EmbView.mk.injEq] at hdom hin hout ⊢
  refine ⟨?_, hdom⟩
  funext e
  by_cases h : ∃ s ∈ slots, e ∈ slotGE P S6 s
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    have heMem : e ∈ slotsGE P S6 slots := by
      unfold slotsGE
      rw [Finset.mem_biUnion]
      obtain ⟨s, hs, he⟩ := h
      exact ⟨s, List.mem_toFinset.mpr hs, he⟩
    obtain ⟨s, hs, he, heq⟩ := hin e heMem
    rw [heq]
    exact hAgree s hs h.choose h.choose_spec.1 e he h.choose_spec.2
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have heNot : e ∉ slotsGE P S6 slots := by
      intro hm
      unfold slotsGE at hm
      rw [Finset.mem_biUnion] at hm
      obtain ⟨s, hs, he⟩ := hm
      exact h ⟨s, List.mem_toFinset.mp hs, he⟩
    exact hout e heNot

/-- `embRefreshSizeAt` equals the sum of `slotRefreshSizeAt` over `slots`. -/
theorem embRefreshSizeAt_eq_sum (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) :
    embRefreshSizeAt P S6 slots = (slots.map (slotRefreshSizeAt P S6)).sum :=
  rfl

/-- `slotWalkWords` is bounded by `slotRefreshSizeAt`. -/
theorem slotWalkWords_le_slotRefreshSizeAt (P : DSParams) {cap : ℕ}
    (S6 : BucketSpannerState cap) (s : ℕ) :
    slotWalkWords P S6 s ≤ slotRefreshSizeAt P S6 s := by
  unfold slotWalkWords slotRefreshSizeAt slotGE
  by_cases hs : s < cap
  · simp only [hs, ↓reduceDIte]
    cases S6 ⟨s, hs⟩ with
    | none => simp
    | some d =>
      refine le_trans (Finset.sum_le_sum fun e _ => ?_) (Nat.le_succ _)
      split_ifs <;> omega
  · simp [hs]

/-- Encoding a single forward edge `[(e, true)]` as `[1, e, 1]` satisfies `MWalkAt`. -/
theorem mWalkAt_single_true {mem : ℕ → ℕ} {a e : ℕ}
    (h0 : mem a = 1) (h1 : mem (a + 1) = e) (h2 : mem (a + 2) = 1) :
    MWalkAt mem a [(e, true)] := by
  intro i hi
  simp only [mWalkEncode, List.flatMap_cons, List.flatMap_nil, List.append_nil, ↓reduceIte,
    List.length_cons, List.length_nil] at hi ⊢
  rcases i with _ | _ | _ | i
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · omega

/-! ## Layout word bounds and fresh-spanner level-0 walk readout -/

/-- All fixed-block addresses and intermediate values used by `embRefreshSlotBody` and
`embRefreshEdgeBody` fit below `b + dsFixedSize L vCap eCap`. -/
theorem embRefresh_fixedBounds {b L vCap eCap : ℕ} :
    b + dsTOff < b + dsFixedSize L vCap eCap ∧
    b + dsLOff < b + dsFixedSize L vCap eCap ∧
    b + dsVCapOff < b + dsFixedSize L vCap eCap ∧
    b + dsECapOff < b + dsFixedSize L vCap eCap ∧
    L + 1 < b + dsFixedSize L vCap eCap ∧
    7 * vCap < b + dsFixedSize L vCap eCap ∧
    9 * eCap < b + dsFixedSize L vCap eCap ∧
    7 * vCap + 9 * eCap < b + dsFixedSize L vCap eCap ∧
    dynGraphSize vCap eCap < b + dsFixedSize L vCap eCap ∧
    3 * dynGraphSize vCap eCap < b + dsFixedSize L vCap eCap ∧
    dsGPtr b < b + dsFixedSize L vCap eCap ∧
    dsGPtr b + dgMOff < b + dsFixedSize L vCap eCap ∧
    dsHPtr b vCap eCap < b + dsFixedSize L vCap eCap ∧
    dgEListBase (dsGPtr b) vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap ∧
    dgEPresBase (dsHPtr b vCap eCap) vCap + eCap ≤ b + dsFixedSize L vCap eCap ∧
    dsMinHBase b vCap eCap < b + dsFixedSize L vCap eCap ∧
    3 * eCap < b + dsFixedSize L vCap eCap ∧
    2 * (L + 1) < b + dsFixedSize L vCap eCap ∧
    3 * eCap + 2 * (L + 1) < b + dsFixedSize L vCap eCap ∧
    dsDomGenBase b L vCap eCap < b + dsFixedSize L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap < b + dsFixedSize L vCap eCap ∧
    (L + 1) * eCap < b + dsFixedSize L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by
  have hfs : dsFixedSize L vCap eCap =
      dsHdrSize + 3 * dynGraphSize vCap eCap + 3 * eCap + 2 * (L + 1) +
      (L + 1) + 2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap) +
      (L + 1) + (L + 1) * vCap + (L + 1) + 2 * vCap + 3 * eCap := by
    simp only [dsFixedSize, dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase,
      dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
      dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase,
      dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]
    ring
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 : dsEdgeDomGenBase b L vCap eCap = dsDomGenBase b L vCap eCap + (L + 1) := rfl
  have h4 : dsPiPtrBase b L vCap eCap = dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap := rfl
  have h5 : dsGPtr b = b + dsHdrSize := rfl
  have h6 : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hgel : dgEListBase (dsGPtr b) vCap eCap = dsGPtr b + 4 + 7 * vCap + eCap := rfl
  have hhep : dgEPresBase (dsHPtr b vCap eCap) vCap = dsHPtr b vCap eCap + 4 + 7 * vCap := rfl
  have hle_e : eCap ≤ (L + 1) * eCap := by
    calc eCap = 1 * eCap := (Nat.one_mul _).symm
      _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right _ (Nat.succ_pos _)
  simp only [dsTOff, dsLOff, dsVCapOff, dsECapOff, dsHdrSize, dgMOff] at hfs h1 h5 ⊢
  omega

/-- If `d.Us = []` then `(d.state P).t = 0`. -/
theorem dsRepAt_t_eq_zero_of_nil {P : DSParams} {d : DSHist}
    (hd : d.Us = []) : (d.state P).t = 0 := by
  have hflat : d.flat = [] := by simp [DSHist.flat, hd]
  simp [DSHist.state, hflat, runState, init, initAt]

/-- Under `DSRepAt P b d x mem`, whenever `(d.state P).t = 0`, every edge `e ∈ (d.state P).G.E`
has its `piTotal` walk pointer stored directly at `dsPiPtrBase b P.L P.vCap P.eCap + e` inside
`heapFoot x`. -/
theorem dsRepAt_fresh_piWalk {P : DSParams} {b : ℕ} {d : DSHist} {x : DynSpannerMeta P.L}
    {mem : ℕ → ℕ} (hrep : DSRepAt P b d x mem) (ht0 : (d.state P).t = 0)
    {e : ℕ} (he : e ∈ (d.state P).G.E) :
    MWalkAt mem (mem (dsPiPtrBase b P.L P.vCap P.eCap + e)) (piTotal (d.state P) e) ∧
    RangeInHeapFoot x (mem (dsPiPtrBase b P.L P.vCap P.eCap + e))
      (mem (dsPiPtrBase b P.L P.vCap P.eCap + e) + (mWalkEncode (piTotal (d.state P) e)).length) := by
  obtain ⟨hL1, hVG₀, hGm₀, _, hBVf, hdsf, _, hSt, _, _⟩ := hrep
  have hq1 : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hSnap := snapInv_of_history P hVG₀ hL1 hq1 hGm₀ hBVf hdsf d.flat.length le_rfl
  have hlen0 : d.flat.length = 0 := by
    have ht := hSnap.t_eq
    change (d.state P).t = d.flat.length at ht
    omega
  have hflat : d.flat = [] := List.eq_nil_of_length_eq_zero hlen0
  have hst : d.state P = (DynSpanner.init d.G₀ P.L (d.q P) (canonicalSparsify P.impl)).state := by
    simp [DSHist.state, hflat, runState]
  have hpi : piTotal (d.state P) e = (d.state P).Pi_level ⟨0, Nat.zero_lt_succ P.L⟩ e := by
    rw [hst]
    unfold piTotal piLe piLt piLtFrom init initAt
    dsimp only
    have hfind : findEmbLevel (L := P.L) (fun i => if i.1 = 0 then d.G₀.E else ∅) (P.L + 1) e = 0 := by
      have hpeq := piTotal_init_eq P d.G₀ e
      -- compute directly
      unfold findEmbLevel
      rw [Nat.min_self]
      have hnone : ∀ l : List ℕ, (∀ i ∈ l, i ≠ 0) →
          l.find? (fun i => if h : i < P.L + 1 then decide (e ∈ if i = 0 then d.G₀.E else ∅) else false) =
            none := by
        intro l hl
        induction l with
        | nil => rfl
        | cons y ys ih =>
          rw [List.find?_cons]
          have hy : y ≠ 0 := hl y (by simp)
          have hpred : (if h : y < P.L + 1 then decide (e ∈ if y = 0 then d.G₀.E else ∅) else false) = false := by
            split_ifs with hlt
            · simp
            · rfl
          rw [hpred]
          exact ih fun z hz => hl z (by simp [hz])
      have hrev : (List.range (P.L + 1)).reverse =
          ((List.range P.L).map (· + 1)).reverse ++ [0] := by
        rw [List.range_succ_eq_map, List.reverse_cons]
      rw [hrev, List.find?_append]
      have hpos : ∀ i ∈ ((List.range P.L).map (· + 1)).reverse, i ≠ 0 := by
        intro i hi
        rw [List.mem_reverse, List.mem_map] at hi
        obtain ⟨k, -, rfl⟩ := hi
        omega
      rw [hnone _ hpos, Option.none_or]
      cases h : ([0] : List ℕ).find?
          (fun i => if h : i < P.L + 1 then decide (e ∈ if i = 0 then d.G₀.E else ∅) else false) with
      | none => rfl
      | some v =>
        have hv := List.mem_of_find?_eq_some h
        simp only [List.mem_singleton] at hv
        subst hv
        rfl
    rw [hfind]
    simp
  have he0 : e ∈ (d.state P).inDom ⟨0, Nat.zero_lt_succ P.L⟩ := by
    rw [hst] at he ⊢
    exact he
  have hInDom := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWalk := (hInDom ⟨0, Nat.zero_lt_succ P.L⟩).2.2.2.2.1 e he0
  dsimp only at hWalk
  simp only [Nat.zero_mul, Nat.add_zero] at hWalk
  rw [hpi]
  exact hWalk

/-- Any cell in `RangeInHeapFoot x lo hi` lies below `h` when `bucketFoot spanH x6` lies below `h`. -/
theorem rangeInHeapFoot_lt_h {L cap spanH h b lo hi : ℕ} {x6 : BucketSpannerMeta L cap}
    {j : Fin cap} {m : DSHist × DynSpannerMeta L}
    (hslot : x6.slots j = some (b, m))
    (hfoot : ∀ a, bucketFoot spanH x6 a → a < h)
    (hrng : RangeInHeapFoot m.2 lo hi) (hne : lo < hi) : hi ≤ h := by
  have ha := hrng (hi - 1) (by omega) (by omega)
  have hlt := hfoot (hi - 1) (Or.inr ⟨j, b, m, hslot, Or.inr ha⟩)
  omega

/-- The fixed block of an active slot `[b, b + dsFixedSize L vCap eCap)` lies in `[0, h]` when
`bucketFoot spanH x6` lies below `h`. -/
theorem slot_fixedSize_le_h {P : DSParams} {cap spanH h b : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} {mem : ℕ → ℕ} {j : Fin cap} {d : DSHist}
    {m : DSHist × DynSpannerMeta P.L}
    (hS6 : (bucketSpannerRep P cap).rep spanH S6 x6 mem)
    (hSj : S6 j = some d) (hxm : x6.slots j = some (b, m))
    (hfoot : ∀ a, bucketFoot spanH x6 a → a < h) :
    b + dsFixedSize P.L P.vCap P.eCap ≤ h := by
  have hslot := hS6.1 j
  rw [hSj, hxm] at hslot
  have hvcap : m.2.vCap = P.vCap := hslot.2.1.2.1.2.2.2.2.2.2.2.1.1
  have hecap : m.2.eCap = P.eCap := hslot.2.1.2.1.2.2.2.2.2.2.2.1.2.1
  have hpos : 0 < dsFixedSize P.L P.vCap P.eCap := by
    have := (embRefresh_fixedBounds (b := 0) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)).1
    omega
  have hmem : bucketFoot spanH x6 (b + dsFixedSize P.L P.vCap P.eCap - 1) :=
    Or.inr ⟨j, b, m, hxm, Or.inl ⟨by omega, by rw [hvcap, hecap]; omega⟩⟩
  have hlt := hfoot _ hmem
  omega

end

end MinCostFlow.SparseCore.Program
