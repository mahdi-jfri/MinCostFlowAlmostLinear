module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActLoopDefs
public import MinCostFlow.SparseCore.Program.CompSplitListModel
public import MinCostFlow.SparseCore.CanonCoreValid
public import MinCostFlow.SparseCore.Program.BundleCapHeadroomStep
public import MinCostFlow.DynSpanner.Program.MergeSort

import Mathlib.Tactic

/-!
# Phase 3 pre-tour & split-group builders (`AssemblyFirstStepBunPrepProg`)

Defines the two deterministic Word-RAM builders that prepare P5's `bundleStep` inputs:
1. `asmFirstBuildDelTriplesStmt fReadParent` (`[bunH, tourH, delEdgesPtr, nDel, h]`):
   runs **before** the tour update while `tourH` still holds `tr.cs.RF`, reads `edgeSlot[e]` and
   `endBundle[2*e .. 2*e+1]` from `bunH`, queries `fReadParent` for deleted edges in active
   bundles, and writes `readDelTriples` at `[h, h + 3 * nDel)`.
2. `asmFirstBuildGroupsStmt bSort` (`[spPtr, vCap, h]`):
   scans P4's ordered split list `SplitEntriesAt mem spPtr (canonSplitList tr.cs U)` in order,
   tracks each fresh root's ancestor root in `tr.cs.RF.R` via a zero-initialized `vCap`-word
   table `anc`, sorts/dedups the touched old roots, and emits `readGroups` for P5's
   `bunTableHeadroom_step_model_runs_on` (`0` tour queries, `O(m log m + 1)` time).

Also proves the general graph-batch ancestor lemma `applyBatch_anc_spec` directly by induction on
`MGraph.BatchIsValid`, establishing every split-group and root-partition precondition of
`bunTableHeadroom_step_model_runs_on`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Deterministic Word-RAM builders -/

@[expose] public section

/-- **Pre-tour deletion-triples builder**, `[bunH, tourH, delEdgesPtr, nDel, h]`:
writes `readDelTriples` at `[h, h + 3 * nDel)` (`[e, p_true, p_false]`, querying `fReadParent`
for edges belonging to an active bundle, leaving `0, 0` otherwise) and returns `hp`. -/
def asmFirstBuildDelTriplesStmt (fReadParent : ℕ) : Stmt :=
  .assign 5 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 3))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const btOffEdgeSlot))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const btOffEndBundle))) ;;
  forRange 8 (.const 0) (.reg 3)
    (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
     .store (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.reg 9) ;;
     .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
     .cond (.reg 10)
       (.assign 11 (.bin .sub (.reg 10) (.const 1)) ;;
        .assign 12 (.load (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9)))) ;;
        .assign 13 (.load (.bin .add (.reg 7) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1)))) ;;
        .assign 14 (.reg 5) ;;
        .call 5 fReadParent [.reg 0, .reg 1, .reg 11, .reg 12, .reg 5] ;;
        .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 1)) (.load (.reg 14)) ;;
        .assign 14 (.reg 5) ;;
        .call 5 fReadParent [.reg 0, .reg 1, .reg 11, .reg 13, .reg 5] ;;
        .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 2)) (.load (.reg 14)))
       .nop) ;;
  .ret (.reg 5)

/-- Space bound of `asmFirstBuildDelTriplesStmt` for `nDel` deleted edges. -/
def buildDelTriplesSpace (TS : BundleTourSpec) (nDel : ℕ) : ℕ :=
  3 * nDel + 2 * nDel * TS.querySpace

/-- Amortized cost bound of `asmFirstBuildDelTriplesStmt` for `nDel` deleted edges. -/
def buildDelTriplesCost (TS : BundleTourSpec) (eCap nDel : ℕ) : ℕ :=
  (2 * TS.mul * ordStoreLog eCap + 280) * nDel + 60

/-- **Split-groups builder from `SplitEntriesAt`**, `[spPtr, vCap, h]`:
writes `[nGroups, groupPtr]` at `[h, h + 2)`, emits `readGroups` at `groupPtr`, and returns `hEnd`.
Registers: `0 = spPtr`, `1 = vCap`, `2 = h`, `3 = m`, `4 = ancBase`, `5 = oldArr`,
`6 = oldSorted`, `7 = scr`, `8 = uniqOld`, `9 = loopIdx`, `10..13` scratch, `14 = nG`,
`15 = grpOf`, `16 = cnt`, `17 = cur`, `18 = groupPtr`, `19 = off`. -/
def asmFirstBuildGroupsStmt (bSort : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .cond (.bin .eq (.reg 3) (.const 0))
    (.store (.reg 2) (.const 0) ;;
     .store (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 2) (.const 2)) ;;
     .ret (.bin .add (.reg 2) (.const 2)))
    (.assign 4 (.bin .add (.reg 2) (.const 2)) ;;
     .assign 5 (.bin .add (.reg 4) (.reg 1)) ;;
     .assign 6 (.bin .add (.reg 5) (.reg 3)) ;;
     .assign 7 (.bin .add (.reg 6) (.reg 3)) ;;
     .assign 8 (.bin .add (.reg 7) (.reg 3)) ;;
     forRange 9 (.const 0) (.reg 3)
       (.assign 10 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 4) (.reg 9)))) ;;
        .assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9)))) ;;
        .assign 12 (.load (.bin .add (.reg 4) (.reg 10))) ;;
        .cond (.bin .eq (.reg 12) (.const 0))
          (.assign 13 (.reg 10))
          (.assign 13 (.bin .sub (.reg 12) (.const 1))) ;;
        .store (.bin .add (.reg 4) (.reg 11)) (.bin .add (.reg 13) (.const 1)) ;;
        .store (.bin .add (.reg 5) (.reg 9)) (.reg 13) ;;
        .store (.bin .add (.reg 6) (.reg 9)) (.reg 13)) ;;
     .call 14 (bSort + sortIdxMergeSort) [.reg 6, .reg 3, .reg 7] ;;
     .call 14 (bSort + sortIdxDedup) [.reg 6, .reg 3, .reg 8] ;;
     .assign 15 (.bin .add (.reg 8) (.reg 14)) ;;
     .assign 16 (.bin .add (.reg 15) (.reg 3)) ;;
     .assign 17 (.bin .add (.reg 16) (.reg 14)) ;;
     .assign 18 (.bin .add (.reg 17) (.reg 14)) ;;
     forRange 9 (.const 0) (.reg 14)
       (.store (.bin .add (.reg 16) (.reg 9)) (.const 1)) ;;
     forRange 9 (.const 0) (.reg 3)
       (.assign 11 (.load (.bin .add (.reg 5) (.reg 9))) ;;
        .call 10 (bSort + sortIdxBinSearch) [.reg 8, .reg 14, .reg 11] ;;
        .store (.bin .add (.reg 15) (.reg 9)) (.reg 10) ;;
        .assign 12 (.load (.bin .add (.reg 16) (.reg 10))) ;;
        .store (.bin .add (.reg 16) (.reg 10)) (.bin .add (.reg 12) (.const 1))) ;;
     .assign 19 (.const 0) ;;
     forRange 9 (.const 0) (.reg 14)
       (.assign 10 (.load (.bin .add (.reg 16) (.reg 9))) ;;
        .assign 11 (.load (.bin .add (.reg 8) (.reg 9))) ;;
        .store (.bin .add (.reg 18) (.reg 19)) (.reg 10) ;;
        .store (.bin .add (.reg 18) (.bin .add (.reg 19) (.const 1))) (.reg 11) ;;
        .store (.bin .add (.reg 17) (.reg 9)) (.bin .add (.reg 19) (.const 2)) ;;
        .assign 19 (.bin .add (.bin .add (.reg 19) (.const 1)) (.reg 10))) ;;
     forRange 9 (.const 0) (.reg 3)
       (.assign 10 (.load (.bin .add (.reg 15) (.reg 9))) ;;
        .assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9)))) ;;
        .assign 12 (.load (.bin .add (.reg 17) (.reg 10))) ;;
        .store (.bin .add (.reg 18) (.reg 12)) (.reg 11) ;;
        .store (.bin .add (.reg 17) (.reg 10)) (.bin .add (.reg 12) (.const 1))) ;;
     .store (.reg 2) (.reg 14) ;;
     .store (.bin .add (.reg 2) (.const 1)) (.reg 18) ;;
     .ret (.bin .add (.reg 18) (.reg 19)))

/-- Space bound of `asmFirstBuildGroupsStmt` for `m` split entries and vertex cap `vCap`. -/
def buildGroupsSpace (vCap m : ℕ) : ℕ :=
  2 + vCap + 10 * m

/-- Cost bound of `asmFirstBuildGroupsStmt` for `m` split entries. -/
def buildGroupsCost (m : ℕ) : ℕ :=
  710 * m * (Nat.log 2 (m + 1) + 1) + 500

/-! ## 2. Pure ancestor-tracking fold and split-group model -/

/-- Decoded ancestor vertex from a 1-indexed ancestor table (`0` means self). -/
def ancDecode (anc : ℕ → ℕ) (v : ℕ) : ℕ :=
  if anc v = 0 then v else anc v - 1

/-- One split-pair step on the 1-indexed ancestor table. -/
def splitAncStep (anc : ℕ → ℕ) (p : ℕ × ℕ) : ℕ → ℕ :=
  Function.update anc p.2 (ancDecode anc p.1 + 1)

/-- Fold of `splitAncStep` over a list of `(kept, fresh)` split pairs. -/
def splitAncFold (pairs : List (ℕ × ℕ)) (anc₀ : ℕ → ℕ) : ℕ → ℕ :=
  pairs.foldl splitAncStep anc₀

/-- Per-pair ancestor list (`r_old` for each `(kept, fresh)` pair in order). -/
def splitOldList (pairs : List (ℕ × ℕ)) (anc₀ : ℕ → ℕ) : List ℕ :=
  match pairs with
  | [] => []
  | p :: rest => ancDecode anc₀ p.1 :: splitOldList rest (splitAncStep anc₀ p)

/-- Sorted deduplicated list of distinct touched old roots. -/
def splitOldRoots (pairs : List (ℕ × ℕ)) : List ℕ :=
  (splitOldList pairs (fun _ => 0)).toFinset.sort (· ≤ ·)

/-- Split groups built from `pairs`: for each `r ∈ splitOldRoots pairs`, `[r]` followed by all
`fresh` entries in `pairs` whose decoded ancestor is `r` (in list order). -/
def splitGroupsOf (pairs : List (ℕ × ℕ)) : List (List ℕ) :=
  let anc := splitAncFold pairs (fun _ => 0)
  (splitOldRoots pairs).map fun r =>
    r :: (pairs.filter fun p => ancDecode anc p.2 = r).map Prod.snd

end

/-! ## 3. Determinism and pure graph-batch ancestor specification -/

public section

theorem asmFirstBuildDelTriplesStmt_noRand (fReadParent : ℕ) :
    (asmFirstBuildDelTriplesStmt fReadParent).NoRand := by
  simp [asmFirstBuildDelTriplesStmt, forRange, forUp, Stmt.NoRand]

theorem asmFirstBuildGroupsStmt_noRand (bSort : ℕ) :
    (asmFirstBuildGroupsStmt bSort).NoRand := by
  simp [asmFirstBuildGroupsStmt, forRange, forUp, Stmt.NoRand]

private lemma splitAncFold_append (l₁ l₂ : List (ℕ × ℕ)) (anc : ℕ → ℕ) :
    splitAncFold (l₁ ++ l₂) anc = splitAncFold l₂ (splitAncFold l₁ anc) :=
  List.foldl_append

private lemma applyUpdate_isValid_loc {G : MGraph} (hG : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) : (G.applyUpdate u).IsValid := by
  cases u with
  | insert e a b =>
    intro f hf
    simp only [MGraph.applyUpdate, Finset.mem_insert] at hf ⊢
    rcases hf with rfl | hf
    · simp [hu.2.1, hu.2.2]
    · have hne : f ≠ e := fun h => hu.1 (h ▸ hf)
      simp [hne, (hG f hf).1, (hG f hf).2]
  | delete e =>
    intro f hf
    exact hG f (Finset.mem_erase.mp hf).2
  | split v v' St Sh =>
    intro f hf
    obtain ⟨ht, hh⟩ := hG f hf
    constructor <;> (dsimp only [MGraph.applyUpdate]; split_ifs <;> simp [ht, hh])

private lemma batchDeletes_cons_loc (u : Update) (rest : List Update) :
    batchDeletes (u :: rest) = batchDeletes [u] ∪ batchDeletes rest := by
  ext e
  simp only [Finset.mem_union, mem_batchDeletes_iff, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨w, rfl | hw, rfl⟩
    · exact Or.inl ⟨_, rfl, rfl⟩
    · exact Or.inr ⟨_, hw, rfl⟩
  · rintro (⟨w, rfl, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr hw, rfl⟩

/-- **General batch ancestor invariant**: for any valid batch `UC` on `G₀`, folding `splitAncStep`
over `pairs = coreBatchSplitPairs UC` from `0` maps every vertex of `G' = G₀.applyBatch UC` back
to its unique ancestor in `G₀.V`, preserves every surviving end's ancestor (`ancRoot (G'.src x) = G₀.src x`),
keeps fresh vertices pairwise distinct and disjoint from `G₀.V`, and agrees on every pair's
recorded `oldArr` value. -/
theorem applyBatch_anc_spec (G₀ : MGraph) (UC : List Update) (hG₀ : G₀.IsValid)
    (hV : G₀.BatchIsValid UC) :
    let pairs := coreBatchSplitPairs UC
    let anc := splitAncFold pairs (fun _ => 0)
    let G' := G₀.applyBatch UC
    (∀ v ∈ G₀.V, anc v = 0) ∧
    (∀ v, v ∉ G'.V → anc v = 0) ∧
    (∀ v ∈ G'.V, ancDecode anc v ∈ G₀.V) ∧
    (∀ v, v ∈ G'.V \ G₀.V ↔ v ∈ pairs.map Prod.snd) ∧
    (pairs.map Prod.snd).Nodup ∧
    (∀ e ∈ G₀.E \ batchDeletes UC, ∀ side : Bool,
      ancDecode anc (G'.src (e, side)) = G₀.src (e, side)) ∧
    (splitOldList pairs (fun _ => 0) = pairs.map fun p => ancDecode anc p.2) ∧
    (∀ p ∈ pairs, ancDecode anc p.2 ∈ G₀.V) := by
  have hgen : ∀ (G : MGraph) (U : List Update) (anc₀ : ℕ → ℕ),
      G.IsValid →
      G.BatchIsValid U →
      (∀ v ∈ G₀.V, anc₀ v = 0) →
      (∀ v, v ∉ G.V → anc₀ v = 0) →
      (∀ v ∈ G.V, ancDecode anc₀ v ∈ G₀.V) →
      G₀.V ⊆ G.V →
      let pairs := coreBatchSplitPairs U
      let anc := splitAncFold pairs anc₀
      let G' := G.applyBatch U
      (∀ v ∈ G₀.V, anc v = 0) ∧
      (∀ v, v ∉ G'.V → anc v = 0) ∧
      (∀ v ∈ G'.V, ancDecode anc v ∈ G₀.V) ∧
      (∀ v ∈ G.V, anc v = anc₀ v) ∧
      (∀ v, v ∈ G'.V \ G.V ↔ v ∈ pairs.map Prod.snd) ∧
      (pairs.map Prod.snd).Nodup ∧
      (∀ e ∈ G.E \ batchDeletes U, ∀ side : Bool,
        ancDecode anc (G'.src (e, side)) = ancDecode anc₀ (G.src (e, side))) ∧
      (splitOldList pairs anc₀ = pairs.map fun p => ancDecode anc p.2) := by
    intro G U
    induction U generalizing G with
    | nil =>
      intro anc₀ _ _ h0 hout hin _
      refine ⟨h0, hout, hin, fun _ _ => rfl, fun v => by simp [MGraph.applyBatch, coreBatchSplitPairs],
        List.nodup_nil, fun _ _ _ => rfl, rfl⟩
    | cons u rest ih =>
      intro anc₀ hG ⟨hu, hrest⟩ h0 hout hin hsub
      have hG1_val : (G.applyUpdate u).IsValid := applyUpdate_isValid_loc hG hu
      cases u with
      | insert e a b =>
        have hVeq : (G.applyUpdate (.insert e a b)).V = G.V := rfl
        have hdel : batchDeletes (.insert e a b :: rest) = batchDeletes rest := by
          ext x; simp [mem_batchDeletes_iff]
        have hEeq : ∀ f ∈ G.E \ batchDeletes (.insert e a b :: rest),
            f ∈ (G.applyUpdate (.insert e a b)).E \ batchDeletes rest ∧
            (G.applyUpdate (.insert e a b)).tail f = G.tail f ∧
            (G.applyUpdate (.insert e a b)).head f = G.head f := fun f hf => by
          rw [Finset.mem_sdiff] at hf
          have hne : f ≠ e := fun h => hu.1 (h ▸ hf.1)
          refine ⟨Finset.mem_sdiff.mpr ⟨by simp [MGraph.applyUpdate, hf.1], hdel ▸ hf.2⟩,
            by simp [MGraph.applyUpdate, hne], by simp [MGraph.applyUpdate, hne]⟩
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
          ih (G.applyUpdate (.insert e a b)) anc₀ hG1_val hrest h0 (by simpa [hVeq] using hout)
            (by simpa [hVeq] using hin) (hVeq ▸ hsub)
        refine ⟨h1, h2, h3, h4, h5, h6, fun f hf side => ?_, h8⟩
        obtain ⟨hf', ht, hh⟩ := hEeq f hf
        have hsrc : (G.applyUpdate (.insert e a b)).src (f, side) = G.src (f, side) := by
          cases side <;> simp [MGraph.src, ht, hh]
        rw [← hsrc]; exact h7 f hf' side
      | delete e =>
        have hVeq : (G.applyUpdate (.delete e)).V = G.V := rfl
        have hdel : batchDeletes (.delete e :: rest) = insert e (batchDeletes rest) := by
          ext x; simp [mem_batchDeletes_iff, eq_comm]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
          ih (G.applyUpdate (.delete e)) anc₀ hG1_val hrest h0 (by simpa [hVeq] using hout)
            (by simpa [hVeq] using hin) (hVeq ▸ hsub)
        refine ⟨h1, h2, h3, h4, h5, h6, fun f hf side => ?_, h8⟩
        rw [Finset.mem_sdiff, hdel, Finset.mem_insert, not_or] at hf
        have hf' : f ∈ (G.applyUpdate (.delete e)).E \ batchDeletes rest :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hf.2.1, hf.1⟩, hf.2.2⟩
        exact h7 f hf' side
      | split v v' St Sh =>
        set G1 := G.applyUpdate (.split v v' St Sh)
        set anc1 := splitAncStep anc₀ (v, v')
        have hv_in : v ∈ G.V := hu.1
        have hv'_not : v' ∉ G.V := hu.2.1
        have hG1V : G1.V = insert v' G.V := rfl
        have h0_1 : ∀ x ∈ G₀.V, anc1 x = 0 := fun x hx => by
          have hne : x ≠ v' := fun h => hv'_not (hsub (h ▸ hx))
          simp [anc1, splitAncStep, Function.update_of_ne hne, h0 x hx]
        have hout_1 : ∀ x, x ∉ G1.V → anc1 x = 0 := fun x hx => by
          rw [hG1V, Finset.mem_insert, not_or] at hx
          simp [anc1, splitAncStep, Function.update_of_ne hx.1, hout x hx.2]
        have hin_1 : ∀ x ∈ G1.V, ancDecode anc1 x ∈ G₀.V := fun x hx => by
          rw [hG1V, Finset.mem_insert] at hx
          rcases hx with rfl | hxG
          · simp only [anc1, splitAncStep, ancDecode, Function.update_self, Nat.add_eq_zero_iff,
              one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
            exact hin v hv_in
          · have hne : x ≠ v' := fun h => hv'_not (h ▸ hxG)
            simp [anc1, splitAncStep, ancDecode, Function.update_of_ne hne]
            exact hin x hxG
        have hsub_1 : G₀.V ⊆ G1.V := hsub.trans (Finset.subset_insert v' G.V)
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih G1 anc1 hG1_val hrest h0_1 hout_1 hin_1 hsub_1
        have hcp : coreBatchSplitPairs (.split v v' St Sh :: rest) = (v, v') :: coreBatchSplitPairs rest := rfl
        have hanc_eq : splitAncFold (coreBatchSplitPairs (.split v v' St Sh :: rest)) anc₀ =
            splitAncFold (coreBatchSplitPairs rest) anc1 := rfl
        have hdel : batchDeletes (.split v v' St Sh :: rest) = batchDeletes rest := by
          ext x; simp [mem_batchDeletes_iff]
        have hv'_not_rest : v' ∉ (coreBatchSplitPairs rest).map Prod.snd := fun hm => by
          have := (h5 v').mpr hm
          exact (Finset.mem_sdiff.mp this).2 (Finset.mem_insert_self v' G.V)
        have hanc_v' : ancDecode (splitAncFold (coreBatchSplitPairs rest) anc1) v' = ancDecode anc₀ v := by
          rw [ancDecode, h4 v' (Finset.mem_insert_self v' G.V)]
          simp [anc1, splitAncStep]
        refine ⟨h1, h2, h3, fun x hx => by
            have hne : x ≠ v' := fun h => hv'_not (h ▸ hx)
            rw [hanc_eq, h4 x (Finset.mem_insert_of_mem hx)]
            simp [anc1, splitAncStep, Function.update_of_ne hne],
          fun x => by
            rw [hcp, List.map_cons, List.mem_cons]
            constructor
            · intro hx; rw [Finset.mem_sdiff] at hx
              by_cases hEq : x = v'
              · exact Or.inl hEq
              · right; exact (h5 x).mp (Finset.mem_sdiff.mpr ⟨hx.1, by simp [hG1V, hEq, hx.2]⟩)
            · rintro (hEq | hrest_m)
              · subst hEq
                refine Finset.mem_sdiff.mpr ⟨?_, hv'_not⟩
                by_contra hnot
                have hzero := h2 x hnot
                rw [h4 x (Finset.mem_insert_self x G.V)] at hzero
                simp [anc1, splitAncStep] at hzero
              · have hx1 := (h5 x).mpr hrest_m
                rw [Finset.mem_sdiff] at hx1
                exact Finset.mem_sdiff.mpr ⟨hx1.1, fun h => hx1.2 (Finset.mem_insert_of_mem h)⟩,
          by rw [hcp, List.map_cons]; exact List.nodup_cons.mpr ⟨hv'_not_rest, h6⟩,
          fun f hf side => by
            have hf1 : f ∈ G1.E \ batchDeletes rest := by rwa [hdel] at hf
            have hfE : f ∈ G.E := (Finset.mem_sdiff.mp hf).1
            have hsrc_in : G.src (f, side) ∈ G.V := by
              cases side with
              | true => exact (hG f hfE).1
              | false => exact (hG f hfE).2
            change ancDecode (splitAncFold (coreBatchSplitPairs rest) anc1) ((G1.applyBatch rest).src (f, side)) = _
            rw [h7 f hf1 side]
            have hsrc_cases : G1.src (f, side) = G.src (f, side) ∨
                (G1.src (f, side) = v' ∧ G.src (f, side) = v) := by
              cases side with
              | true =>
                change (if f ∈ St ∧ G.tail f = v then v' else G.tail f) = G.tail f ∨
                    ((if f ∈ St ∧ G.tail f = v then v' else G.tail f) = v' ∧ G.tail f = v)
                by_cases hc : f ∈ St ∧ G.tail f = v
                · simp [hc]
                · simp [hc]
              | false =>
                change (if f ∈ Sh ∧ G.head f = v then v' else G.head f) = G.head f ∨
                    ((if f ∈ Sh ∧ G.head f = v then v' else G.head f) = v' ∧ G.head f = v)
                by_cases hc : f ∈ Sh ∧ G.head f = v
                · simp [hc]
                · simp [hc]
            rcases hsrc_cases with hEq | ⟨h1', h2'⟩
            · rw [hEq]
              have hne : G.src (f, side) ≠ v' := fun h => hv'_not (h ▸ hsrc_in)
              simp [anc1, splitAncStep, ancDecode, Function.update_of_ne hne]
            · rw [h1', h2']; simp [anc1, splitAncStep, ancDecode],
          by
            rw [hcp, List.map_cons, splitOldList]
            change ancDecode anc₀ v :: splitOldList (coreBatchSplitPairs rest) anc1 =
              ancDecode (splitAncFold (coreBatchSplitPairs rest) anc1) v' ::
                (coreBatchSplitPairs rest).map
                  (fun p => ancDecode (splitAncFold (coreBatchSplitPairs rest) anc1) p.2)
            rw [hanc_v', h8]⟩
  obtain ⟨h1, h2, h3, _, h5, h6, h7, h8⟩ :=
    hgen G₀ UC (fun _ => 0) hG₀ hV (fun _ _ => rfl) (fun _ _ => rfl)
      (fun v hv => by simpa [ancDecode] using hv) (Finset.Subset.refl _)
  refine ⟨h1, h2, h3, h5, h6, fun e he side => by
    have := h7 e he side; simpa [ancDecode] using this, h8, fun p hp => ?_⟩
  have hp2 : p.2 ∈ (G₀.applyBatch UC).V \ G₀.V :=
    (h5 p.2).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact h3 p.2 (Finset.mem_sdiff.mp hp2).1

end

/-! ## 3. Pure list helpers for `splitGroupsOf` and `readGroups` -/

@[expose] public section

/-- Helper for grouping a list of pairs by `oldL = splitOldList pairs (fun _ => 0)`. -/
def groupMembers (pairs : List (ℕ × ℕ)) (oldL : List ℕ) (r : ℕ) : List ℕ :=
  ((List.range pairs.length).filter fun i => decide (oldL.getD i 0 = r)).map
    fun i => (pairs.getD i (0, 0)).2

end

public section

lemma splitOldList_length (pairs : List (ℕ × ℕ)) (anc : ℕ → ℕ) :
    (splitOldList pairs anc).length = pairs.length := by
  induction pairs generalizing anc with
  | nil => rfl
  | cons p rest ih => simp [splitOldList, ih]

lemma splitOldList_append (l₁ l₂ : List (ℕ × ℕ)) (anc : ℕ → ℕ) :
    splitOldList (l₁ ++ l₂) anc =
      splitOldList l₁ anc ++ splitOldList l₂ (splitAncFold l₁ anc) := by
  induction l₁ generalizing anc with
  | nil => rfl
  | cons p rest ih => simp [splitOldList, splitAncFold, ih]

lemma splitAncFold_take_succ (pairs : List (ℕ × ℕ)) (anc₀ : ℕ → ℕ) {i : ℕ}
    (hi : i < pairs.length) :
    splitAncFold (pairs.take (i + 1)) anc₀ =
      splitAncStep (splitAncFold (pairs.take i) anc₀) (pairs[i]'hi) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    splitAncFold, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl

lemma splitOldList_getElem (pairs : List (ℕ × ℕ)) (anc₀ : ℕ → ℕ) {i : ℕ}
    (hi : i < pairs.length) :
    (splitOldList pairs anc₀)[i]'(by rw [splitOldList_length]; exact hi) =
      ancDecode (splitAncFold (pairs.take i) anc₀) (pairs[i]'hi).1 := by
  have hsplit : pairs = pairs.take i ++ pairs.drop i := (List.take_append_drop i pairs).symm
  have hdrop : pairs.drop i = (pairs[i]'hi) :: pairs.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  have hlen : (splitOldList (pairs.take i) anc₀).length = i := by
    rw [splitOldList_length, List.length_take, Nat.min_eq_left (by omega)]
  have heq : splitOldList pairs anc₀ =
      splitOldList (pairs.take i) anc₀ ++
        (ancDecode (splitAncFold (pairs.take i) anc₀) (pairs[i]'hi).1 ::
          splitOldList (pairs.drop (i + 1))
            (splitAncStep (splitAncFold (pairs.take i) anc₀) (pairs[i]'hi))) := by
    conv_lhs => rw [hsplit]
    rw [splitOldList_append, hdrop, splitOldList]
  have hi' : i < (splitOldList pairs anc₀).length := by rw [splitOldList_length]; exact hi
  calc (splitOldList pairs anc₀)[i]'hi'
      = (splitOldList (pairs.take i) anc₀ ++
          (ancDecode (splitAncFold (pairs.take i) anc₀) (pairs[i]'hi).1 :: _))[i]'(by rw [← heq]; exact hi') := by
          congr 1
    _ = ancDecode (splitAncFold (pairs.take i) anc₀) (pairs[i]'hi).1 := by
          rw [List.getElem_append_right (by omega)]; simp [hlen]

lemma splitAncFold_lt (pairs : List (ℕ × ℕ)) (vCap : ℕ)
    (hlt : ∀ p ∈ pairs, p.1 < vCap ∧ p.2 < vCap) :
    ∀ (anc : ℕ → ℕ), (∀ v < vCap, anc v ≤ vCap) → (∀ v, vCap ≤ v → anc v = 0) →
      (∀ v < vCap, splitAncFold pairs anc v ≤ vCap) ∧
      (∀ v, vCap ≤ v → splitAncFold pairs anc v = 0) := by
  induction pairs with
  | nil => intro anc h1 h2; exact ⟨h1, h2⟩
  | cons p rest ih =>
    intro anc h1 h2
    have hp := hlt p List.mem_cons_self
    have hdec : ancDecode anc p.1 < vCap := by
      unfold ancDecode
      split_ifs with h0
      · exact hp.1
      · have := h1 p.1 hp.1; omega
    apply ih (fun q hq => hlt q (List.mem_cons_of_mem p hq)) (splitAncStep anc p)
    · intro v hv
      unfold splitAncStep
      by_cases heq : v = p.2
      · subst heq; rw [Function.update_self]; omega
      · rw [Function.update_of_ne heq]; exact h1 v hv
    · intro v hv
      unfold splitAncStep
      have hne : v ≠ p.2 := by omega
      rw [Function.update_of_ne hne]; exact h2 v hv

lemma readGroups_of_layout {mem : ℕ → ℕ} {base : ℕ} {gs : List (List ℕ)}
    (hgs : ∀ gi (hgi : gi < gs.length),
      let off := groupsWords (gs.take gi)
      mem (base + off) = (gs[gi]'hgi).length ∧
      ∀ j (hj : j < (gs[gi]'hgi).length), mem (base + off + 1 + j) = (gs[gi]'hgi)[j]'hj) :
    readGroups mem base gs.length = gs := by
  have haux : ∀ (k : ℕ) (hk : k ≤ gs.length),
      readGroups mem (base + groupsWords (gs.take (gs.length - k))) k =
        gs.drop (gs.length - k) := by
    intro k
    induction k with
    | zero => intro _; simp [readGroups]
    | succ m ih =>
      intro hm
      have hgi : gs.length - (m + 1) < gs.length := by omega
      have hdrop : gs.drop (gs.length - (m + 1)) =
          (gs[gs.length - (m + 1)]'hgi) :: gs.drop (gs.length - m) := by
        rw [List.drop_eq_getElem_cons hgi]
        congr 2; omega
      have htake : gs.take (gs.length - m) =
          gs.take (gs.length - (m + 1)) ++ [gs[gs.length - (m + 1)]'hgi] := by
        have hidx : gs.length - m = (gs.length - (m + 1)) + 1 := by omega
        rw [hidx, List.take_add_one, List.getElem?_eq_getElem hgi, Option.toList_some]
      have hgw : groupsWords (gs.take (gs.length - m)) =
          groupsWords (gs.take (gs.length - (m + 1))) + 1 + (gs[gs.length - (m + 1)]'hgi).length := by
        rw [htake]; unfold groupsWords
        rw [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]; omega
      obtain ⟨hlen, helt⟩ := hgs (gs.length - (m + 1)) hgi
      rw [readGroups, hdrop, hlen]
      congr 1
      · refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        exact helt j hj2
      · have ih' := ih (by omega)
        rw [hgw] at ih'
        simpa [Nat.add_assoc] using ih'
  simpa [groupsWords] using haux gs.length (le_refl _)

lemma groupsWords_eq_sum_lengths (gs : List (List ℕ)) :
    groupsWords gs = gs.length + groupsTotalLen gs := by
  induction gs with
  | nil => simp [groupsWords, groupsTotalLen]
  | cons g rest ih => simp [groupsWords, groupsTotalLen] at ih ⊢; omega

lemma groupMembers_take_succ (pairs : List (ℕ × ℕ)) (oldL : List ℕ) (r : ℕ)
    {k : ℕ} (hk : k < pairs.length) :
    groupMembers (pairs.take (k + 1)) oldL r =
      groupMembers (pairs.take k) oldL r ++
        if oldL.getD k 0 = r then [(pairs[k]'hk).2] else [] := by
  unfold groupMembers
  have h1 : (pairs.take (k + 1)).length = k + 1 := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have h2 : (pairs.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  rw [h1, h2, List.range_succ, List.filter_append, List.map_append]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hilt : i < k := List.mem_range.mp (List.mem_of_mem_filter hi)
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
      List.getElem_take, List.getElem_take]
  · simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
    split_ifs with heq
    · simp only [List.map_cons, List.map_nil]
      rw [List.getD_eq_getElem _ _ (by omega), List.getElem_take]
    · rfl

lemma groupMembers_eq_filter_snd (pairs : List (ℕ × ℕ)) (oldL : List ℕ) (anc : ℕ → ℕ)
    (hold : oldL = pairs.map fun p => ancDecode anc p.2) (r : ℕ) :
    groupMembers pairs oldL r = (pairs.filter fun p => decide (ancDecode anc p.2 = r)).map Prod.snd := by
  have haux : ∀ k (hk : k ≤ pairs.length),
      groupMembers (pairs.take k) oldL r =
        ((pairs.take k).filter fun p => decide (ancDecode anc p.2 = r)).map Prod.snd := by
    intro k
    induction k with
    | zero => intro _; simp [groupMembers]
    | succ m ih =>
      intro hm
      have hmlt : m < pairs.length := by omega
      rw [groupMembers_take_succ pairs oldL r hmlt, ih (by omega)]
      rw [List.take_add_one, List.getElem?_eq_getElem hmlt, Option.toList_some,
        List.filter_append, List.map_append]
      congr 1
      have hm_old : oldL.getD m 0 = ancDecode anc (pairs[m]'hmlt).2 := by
        rw [hold, List.getD_eq_getElem _ _ (by simp [hmlt]), List.getElem_map]
      rw [hm_old]
      by_cases h : ancDecode anc (pairs[m]'hmlt).2 = r
      · simp [h]
      · simp [h]
  simpa [List.take_length] using haux pairs.length (le_refl _)

lemma sum_groupMembers_length {pairs : List (ℕ × ℕ)} {oldL uniqL : List ℕ}
    (hlen : oldL.length = pairs.length)
    (hnd : uniqL.Nodup)
    (hmem : ∀ x, x ∈ uniqL ↔ x ∈ oldL) :
    (uniqL.map fun r => (groupMembers pairs oldL r).length).sum = pairs.length := by
  have haux : ∀ k (hk : k ≤ pairs.length),
      (uniqL.map fun r => (groupMembers (pairs.take k) oldL r).length).sum = k := by
    intro k
    induction k with
    | zero => intro _; simp [List.take_zero, groupMembers]
    | succ m ih =>
      intro hm
      have hmlt : m < pairs.length := by omega
      set x := oldL.getD m 0
      have hx_in : x ∈ uniqL := (hmem x).mpr (by
        rw [show x = oldL[m]'(by omega) from List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _)
      have hstep : ∀ r, (groupMembers (pairs.take (m + 1)) oldL r).length =
          (groupMembers (pairs.take m) oldL r).length + if r = x then 1 else 0 := fun r => by
        rw [groupMembers_take_succ pairs oldL r hmlt, List.length_append]
        change _ + (if x = r then [(pairs[m]'hmlt).2] else []).length = _
        by_cases heq : r = x
        · subst heq; simp
        · have hne : x ≠ r := Ne.symm heq
          simp [hne, heq]
      have hsum_add : ∀ (l : List ℕ) (f g : ℕ → ℕ),
          (l.map fun r => f r + g r).sum = (l.map f).sum + (l.map g).sum := by
        intro l f g; induction l with
        | nil => simp
        | cons a tl ihl => simp [ihl]; omega
      have hsum_ind : ∀ (l : List ℕ), l.Nodup → x ∈ l →
          (l.map fun r => if r = x then 1 else 0).sum = 1 := by
        intro l; induction l with
        | nil => intro _ h; cases h
        | cons a tl ihl =>
          intro hnd' hmem'
          rcases List.nodup_cons.mp hnd' with ⟨hnot, hnd_tl⟩
          rcases List.mem_cons.mp hmem' with rfl | htl
          · have h0 : (tl.map fun r => if r = x then 1 else 0).sum = 0 := by
              clear ihl hnd_tl hnd' hmem'
              induction tl with
              | nil => rfl
              | cons b bs ihb =>
                have hne : b ≠ x := fun h => hnot (h ▸ List.mem_cons_self)
                simp only [List.map_cons, List.sum_cons, hne, ↓reduceIte, Nat.zero_add]
                exact ihb fun h => hnot (List.mem_cons_of_mem b h)
            simp [h0]
          · have hne : a ≠ x := fun h => hnot (h ▸ htl)
            simp [hne, ihl hnd_tl htl]
      calc (uniqL.map fun r => (groupMembers (pairs.take (m + 1)) oldL r).length).sum
          = (uniqL.map fun r => (groupMembers (pairs.take m) oldL r).length + if r = x then 1 else 0).sum := by
              congr 1; exact List.map_congr_left fun r _ => hstep r
        _ = (uniqL.map fun r => (groupMembers (pairs.take m) oldL r).length).sum +
              (uniqL.map fun r => if r = x then 1 else 0).sum := hsum_add _ _ _
        _ = m + 1 := by rw [ih (by omega), hsum_ind uniqL hnd hx_in]
  simpa [List.take_length] using haux pairs.length (le_refl _)

lemma rangeCost_const_eq (c n : ℕ) : rangeCost (fun _ => c) 0 n = n * c := by
  have haux : ∀ k i, k = n - i → i ≤ n → rangeCost (fun _ => c) i n = k * c := by
    intro k; induction k with
    | zero =>
      intro i hk hi
      have heq : i = n := by omega
      subst heq; rw [rangeCost_of_le (le_refl _)]; simp
    | succ k ih =>
      intro i hk hi
      rw [rangeCost_step (by omega), ih (i + 1) (by omega) (by omega)]; ring
  exact haux n 0 (by omega) (Nat.zero_le _)

end

end MinCostFlow.SparseCore.Program
