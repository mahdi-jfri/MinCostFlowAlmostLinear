module

public import MinCostFlow.SparseCore.Program.OutSplitBound
public import MinCostFlow.SparseCore.BundleOutBatch
import all MinCostFlow.SparseCore.Program.OutSplitBound
import MinCostFlow.DynSpanner.Walks
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators

/-!
# The split lists of one step, in the model

At each core split of a step, the helper `outSmallSide` lists the marked ends of the side with
fewer marked ends (`OutSplitBound.lean`). This file fixes, in the model, which ends are marked at
each split, and bounds the total length of the lists.

The setting. The core graph `C` goes through the core batch `UC` of the step. The marked edges
`M` are old output edges. A deletion in `UC` removes its edge from `M`. An insertion adds no mark,
since its edge is not an edge of the graph before. So at the split of `v` into `v` and `v'`, the
marked ends at `v` and at `v'` are the ends of the edges of `M` that start there in the core
graph right after the split (`markBlock`). The list of the helper has as many ends as the smaller
of the two blocks (`cutLens`). So the lengths depend only on the core batch and the marks, and not
on the program.

* `cutLens_sum_le`: the lengths of the lists sum to at most the encoding size of the restricted
  splits on the output graph plus the start potential `markPot`. For this, the output graph must
  have the kept edges `keep ⊆ M` as its edges, with the same ends as in the core graph, and the
  core batch must not delete a kept edge.
* `cutLens_append`: the lists of a concatenation of core batches, so that a program can run the
  core batch one input update at a time.
* `markPot_le`: the start potential is at most `2 ⌊log₂ (2 |M| + 1)⌋` per leaving end, so at most
  `4 ⌊log₂ (2 |M| + 1)⌋` per edge of `M \ keep`.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner

/-- The ends of the edges of `A`. -/
def edgeEnds (A : Finset ℕ) : Finset End := A ×ˢ Finset.univ

theorem mem_edgeEnds {A : Finset ℕ} {x : End} : x ∈ edgeEnds A ↔ x.1 ∈ A := by
  simp [edgeEnds]

theorem card_edgeEnds (A : Finset ℕ) : (edgeEnds A).card = 2 * A.card := by
  simp [edgeEnds, Finset.card_product, Nat.mul_comm]

/-- The marked ends at the vertex `r` of `C`: the ends of the edges of `M` that start at `r`. -/
def markBlock (M : Finset ℕ) (C : MGraph) (r : ℕ) : Finset End :=
  (edgeEnds M).filter fun x => C.src x = r

theorem mem_markBlock {M : Finset ℕ} {C : MGraph} {r : ℕ} {x : End} :
    x ∈ markBlock M C r ↔ x.1 ∈ M ∧ C.src x = r := by
  simp [markBlock, mem_edgeEnds]

/-- The potential of the marked ends of `C`, with the kept edges `keep`: the potential
`splitPot` of the block at each vertex of `C`, summed. -/
def markPot (keep M : Finset ℕ) (C : MGraph) : ℕ :=
  ∑ r ∈ C.V, splitPot (edgeEnds keep) (markBlock M C r)

/-- The lengths of the split lists of the core batch `UC` on the core graph `C`, with the marked
edges `M`: one entry per split, the smaller number of marked ends of the two sides right after
the split. A deletion removes its edge from the marked edges. An insertion adds no mark. -/
def cutLens : Finset ℕ → MGraph → List Update → List ℕ
  | _, _, [] => []
  | M, C, .insert e a b :: UC => cutLens M (C.applyUpdate (.insert e a b)) UC
  | M, C, .delete e :: UC => cutLens (M.erase e) (C.applyUpdate (.delete e)) UC
  | M, C, .split v v' St Sh :: UC =>
    min (markBlock M (C.applyUpdate (.split v v' St Sh)) v).card
        (markBlock M (C.applyUpdate (.split v v' St Sh)) v').card ::
      cutLens M (C.applyUpdate (.split v v' St Sh)) UC

/-- The marked edges after the core batch `UC`: those of `M` that it does not delete. -/
def markAfter : Finset ℕ → List Update → Finset ℕ
  | M, [] => M
  | M, .delete e :: UC => markAfter (M.erase e) UC
  | M, _ :: UC => markAfter M UC

/-- **The lists of a concatenation.** The program runs the core batch one input update at a
time. The lists of `UC₁ ++ UC₂` are those of `UC₁`, then those of `UC₂` with the marks and the
core graph after `UC₁`. -/
theorem cutLens_append : ∀ (UC₁ UC₂ : List Update) (M : Finset ℕ) (C : MGraph),
    cutLens M C (UC₁ ++ UC₂) =
      cutLens M C UC₁ ++ cutLens (markAfter M UC₁) (C.applyBatch UC₁) UC₂
  | [], _, _, _ => by simp [cutLens, markAfter, MGraph.applyBatch]
  | .insert e a b :: UC₁, UC₂, M, C => by
    simp only [List.cons_append, cutLens, markAfter]
    exact cutLens_append UC₁ UC₂ M _
  | .delete e :: UC₁, UC₂, M, C => by
    simp only [List.cons_append, cutLens, markAfter]
    exact cutLens_append UC₁ UC₂ _ _
  | .split v v' St Sh :: UC₁, UC₂, M, C => by
    simp only [List.cons_append, cutLens, markAfter, List.cons.injEq, true_and]
    exact cutLens_append UC₁ UC₂ M _

/-! ## Facts about ends -/

/-- Where an end starts after a split: at `v'` when it moves, and where it was otherwise. -/
theorem src_applyUpdate_split (C : MGraph) (v v' : ℕ) (St Sh : Finset ℕ) (x : End) :
    (C.applyUpdate (.split v v' St Sh)).src x =
      if (if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ C.src x = v then v' else C.src x := by
  obtain ⟨e, b⟩ := x
  cases b <;> simp [MGraph.applyUpdate, MGraph.src]

/-- An insertion does not move the ends of the other edges. -/
theorem src_applyUpdate_insert_of_ne (C : MGraph) {e a b : ℕ} {x : End} (hx : x.1 ≠ e) :
    (C.applyUpdate (.insert e a b)).src x = C.src x := by
  obtain ⟨f, c⟩ := x
  simp only at hx
  cases c <;> simp [MGraph.applyUpdate, MGraph.src, Function.update_of_ne hx]

/-- In a valid graph, an end of an edge starts at a vertex. -/
theorem src_mem_V {C : MGraph} (hC : C.IsValid) {x : End} (hx : x.1 ∈ C.E) : C.src x ∈ C.V := by
  unfold MGraph.src
  split
  · exact (hC _ hx).1
  · exact (hC _ hx).2

/-- The number of ends of the edges of `A` that start at `r` is the number of edges of `A` with
tail `r` plus the number with head `r`. -/
theorem card_edgeEnds_filter_src (G : MGraph) (A : Finset ℕ) (r : ℕ) :
    ((edgeEnds A).filter fun x => G.src x = r).card =
      (A.filter fun e => G.tail e = r).card + (A.filter fun e => G.head e = r).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, edgeEnds, Finset.sum_product,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_bool]
  simp [MGraph.src]

/-- **The kept ends of a block are the degree in the output graph.** When the output graph `S`
has the kept edges as its edges, with the same ends as in `C`, the kept ends of the block at `r`
are as many as the degree of `r` in `S`. -/
theorem card_markBlock_inter_eq_deg {keep M : Finset ℕ} {C S : MGraph} (hk : keep ⊆ M)
    (hE : S.E = keep) (hends : ∀ e ∈ keep, S.tail e = C.tail e ∧ S.head e = C.head e)
    (r : ℕ) : (markBlock M C r ∩ edgeEnds keep).card = S.deg r := by
  have hsrc : ∀ x : End, x.1 ∈ keep → S.src x = C.src x := by
    intro x hx
    unfold MGraph.src
    split
    · exact (hends _ hx).1
    · exact (hends _ hx).2
  have h : markBlock M C r ∩ edgeEnds keep = (edgeEnds keep).filter fun x => S.src x = r := by
    ext x
    simp only [Finset.mem_inter, mem_markBlock, Finset.mem_filter, mem_edgeEnds]
    constructor
    · rintro ⟨⟨_, hs⟩, hx⟩
      exact ⟨hx, (hsrc x hx).trans hs⟩
    · rintro ⟨hx, hs⟩
      exact ⟨⟨hk hx, (hsrc x hx).symm.trans hs⟩, hx⟩
  rw [h, card_edgeEnds_filter_src, MGraph.deg, hE]

/-- The list of the helper has as many ends as the smaller part. -/
theorem card_splitPick {α : Type*} [DecidableEq α] (P₁ P₂ : Finset α) :
    (splitPick P₁ P₂).card = min P₁.card P₂.card := by
  unfold splitPick
  split
  · exact (min_eq_left (by assumption)).symm
  · exact (min_eq_right (by omega)).symm

/-! ## The three kinds of steps -/

/-- An insertion does not change the blocks of marked ends, since its edge is not marked. -/
theorem markPot_insert (keep M : Finset ℕ) (C : MGraph) {e a b : ℕ} (he : e ∉ M) :
    markPot keep M (C.applyUpdate (.insert e a b)) = markPot keep M C := by
  unfold markPot
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  ext x
  simp only [mem_markBlock]
  constructor
  · rintro ⟨hx, hs⟩
    have hsx : (C.applyUpdate (.insert e a b)).src x = C.src x :=
      src_applyUpdate_insert_of_ne C fun h => he (by rw [← h]; exact hx)
    exact ⟨hx, hsx.symm.trans hs⟩
  · rintro ⟨hx, hs⟩
    have hsx : (C.applyUpdate (.insert e a b)).src x = C.src x :=
      src_applyUpdate_insert_of_ne C fun h => he (by rw [← h]; exact hx)
    exact ⟨hx, hsx.trans hs⟩

/-- A deletion does not raise the potential, since the blocks only lose ends. -/
theorem markPot_delete_le (keep M : Finset ℕ) (C : MGraph) (e : ℕ) :
    markPot keep (M.erase e) (C.applyUpdate (.delete e)) ≤ markPot keep M C := by
  unfold markPot
  refine Finset.sum_le_sum fun r _ => splitPot_mono _ fun x hx => ?_
  rw [mem_markBlock] at hx ⊢
  exact ⟨Finset.mem_of_mem_erase hx.1, hx.2⟩

/-- **A split.** The list of the helper plus the new potential is at most the smaller number of
kept ends of the two sides plus the old potential (`splitPot_sum_split`). -/
theorem markPot_split (keep M : Finset ℕ) {C : MGraph} (hC : C.IsValid) (hM : M ⊆ C.E)
    {v v' : ℕ} {St Sh : Finset ℕ} (hv : v ∈ C.V) (hv' : v' ∉ C.V) :
    min (markBlock M (C.applyUpdate (.split v v' St Sh)) v).card
        (markBlock M (C.applyUpdate (.split v v' St Sh)) v').card +
      markPot keep M (C.applyUpdate (.split v v' St Sh)) ≤
      min (markBlock M (C.applyUpdate (.split v v' St Sh)) v ∩ edgeEnds keep).card
        (markBlock M (C.applyUpdate (.split v v' St Sh)) v' ∩ edgeEnds keep).card +
      markPot keep M C := by
  have hvv : v ≠ v' := fun h => hv' (h ▸ hv)
  have hsv : ∀ x : End, x.1 ∈ M → C.src x ≠ v' := fun x hx h => hv' (h ▸ src_mem_V hC (hM hx))
  have hother : ∀ u ∈ C.V, u ≠ v →
      markBlock M (C.applyUpdate (.split v v' St Sh)) u = markBlock M C u := by
    intro u hu huv
    ext x
    simp only [mem_markBlock, src_applyUpdate_split]
    constructor
    · rintro ⟨hx, hs⟩
      refine ⟨hx, ?_⟩
      by_cases h : (if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ C.src x = v
      · rw [ite_eq_left h] at hs
        exact absurd (hs ▸ hu) hv'
      · rw [ite_eq_right h] at hs
        exact hs
    · rintro ⟨hx, hs⟩
      refine ⟨hx, ?_⟩
      rw [ite_eq_right (fun h => huv (hs ▸ h.2))]
      exact hs
  have hunion : markBlock M (C.applyUpdate (.split v v' St Sh)) v ∪
      markBlock M (C.applyUpdate (.split v v' St Sh)) v' = markBlock M C v := by
    ext x
    simp only [Finset.mem_union, mem_markBlock, src_applyUpdate_split]
    by_cases h : (if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ C.src x = v
    · rw [ite_eq_left h]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact ⟨hx, h.2⟩
      · rintro ⟨hx, _⟩
        exact Or.inr ⟨hx, rfl⟩
    · rw [ite_eq_right h]
      constructor
      · rintro (⟨hx, hs⟩ | ⟨hx, hs⟩)
        · exact ⟨hx, hs⟩
        · exact absurd hs (hsv x hx)
      · rintro ⟨hx, hs⟩
        exact Or.inl ⟨hx, hs⟩
  have hd : Disjoint (markBlock M (C.applyUpdate (.split v v' St Sh)) v)
      (markBlock M (C.applyUpdate (.split v v' St Sh)) v') := by
    refine Finset.disjoint_left.mpr fun x h₁ h₂ => ?_
    rw [mem_markBlock] at h₁ h₂
    exact hvv (h₁.2.symm.trans h₂.2)
  have h := splitPot_sum_split (edgeEnds keep) C.V (markBlock M C)
    (markBlock M (C.applyUpdate (.split v v' St Sh))) hv hv' hother hunion hd
  rw [card_splitPick] at h
  exact h

/-! ## The sum of the lengths -/

/-- **The split lists of a core batch.** The lengths of the lists sum to at most the encoding
size of the restricted splits on the output graph `S`, plus the start potential. The marked
edges `M` are edges of the valid core graph `C`, the kept edges are marked, they are the edges of
`S` with the same ends as in `C`, and the core batch does not delete them. -/
theorem cutLens_sum_le (keep : Finset ℕ) : ∀ (UC : List Update) (M : Finset ℕ) (C S : MGraph),
    C.IsValid → C.BatchIsValid UC → M ⊆ C.E → keep ⊆ M → S.E = keep →
    (∀ e ∈ keep, S.tail e = C.tail e ∧ S.head e = C.head e) →
    (∀ e ∈ keep, Update.delete e ∉ UC) →
    (cutLens M C UC).sum ≤ S.batchEnc (restrictSplits keep UC) + markPot keep M C
  | [], _, _, _, _, _, _, _, _, _, _ => by simp [cutLens]
  | .insert e a b :: UC, M, C, S, hC, hB, hM, hk, hE, hends, hdel => by
    have heM : e ∉ M := fun h => hB.1.1 (hM h)
    have hends' : ∀ f ∈ keep, S.tail f = (C.applyUpdate (.insert e a b)).tail f ∧
        S.head f = (C.applyUpdate (.insert e a b)).head f := by
      intro f hf
      have hfe : f ≠ e := fun h => heM (h ▸ hk hf)
      simp only [MGraph.applyUpdate, Function.update_of_ne hfe]
      exact hends f hf
    have hM' : M ⊆ (C.applyUpdate (.insert e a b)).E := fun f hf => by
      simp only [MGraph.applyUpdate, Finset.mem_insert]
      exact Or.inr (hM hf)
    have ih := cutLens_sum_le keep UC M (C.applyUpdate (.insert e a b)) S
      (isValid_applyUpdate_any hC hB.1) hB.2 hM' hk hE hends'
      (fun f hf h => hdel f hf (List.mem_cons_of_mem _ h))
    rw [markPot_insert keep M C heM] at ih
    simpa only [cutLens, restrictSplits] using ih
  | .delete e :: UC, M, C, S, hC, hB, hM, hk, hE, hends, hdel => by
    have hek : e ∉ keep := fun h => hdel e h List.mem_cons_self
    have hk' : keep ⊆ M.erase e := fun f hf =>
      Finset.mem_erase.mpr ⟨fun h => hek (h ▸ hf), hk hf⟩
    have ih := cutLens_sum_le keep UC (M.erase e) (C.applyUpdate (.delete e)) S
      (isValid_applyUpdate_any hC hB.1) hB.2 (Finset.erase_subset_erase e hM) hk' hE hends
      (fun f hf h => hdel f hf (List.mem_cons_of_mem _ h))
    have hpot := markPot_delete_le keep M C e
    have hgoal : (cutLens M C (.delete e :: UC)).sum =
        (cutLens (M.erase e) (C.applyUpdate (.delete e)) UC).sum := by
      simp only [cutLens]
    have henc : S.batchEnc (restrictSplits keep (.delete e :: UC)) =
        S.batchEnc (restrictSplits keep UC) := by
      simp only [restrictSplits]
    rw [hgoal, henc]
    omega
  | .split v v' St Sh :: UC, M, C, S, hC, hB, hM, hk, hE, hends, hdel => by
    have hends' : ∀ f ∈ keep,
        (S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).tail f =
          (C.applyUpdate (.split v v' St Sh)).tail f ∧
        (S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).head f =
          (C.applyUpdate (.split v v' St Sh)).head f := by
      intro f hf
      simp only [MGraph.applyUpdate, Finset.mem_inter, hf, and_true]
      rw [(hends f hf).1, (hends f hf).2]
      exact ⟨rfl, rfl⟩
    have ih := cutLens_sum_le keep UC M (C.applyUpdate (.split v v' St Sh))
      (S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep)))
      (isValid_applyUpdate_any hC hB.1) hB.2 hM hk hE hends'
      (fun f hf h => hdel f hf (List.mem_cons_of_mem _ h))
    have hsplit := markPot_split keep M hC hM (St := St) (Sh := Sh) hB.1.1 hB.1.2.1
    have hE' : (S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).E = keep := hE
    rw [card_markBlock_inter_eq_deg hk hE' hends' v,
      card_markBlock_inter_eq_deg hk hE' hends' v'] at hsplit
    have hgoal : (cutLens M C (.split v v' St Sh :: UC)).sum =
        min (markBlock M (C.applyUpdate (.split v v' St Sh)) v).card
          (markBlock M (C.applyUpdate (.split v v' St Sh)) v').card +
        (cutLens M (C.applyUpdate (.split v v' St Sh)) UC).sum := by
      simp only [cutLens, List.sum_cons]
    have henc : S.batchEnc (restrictSplits keep (.split v v' St Sh :: UC)) =
        min ((S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).deg v)
          ((S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).deg v') + 1 +
        (S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).batchEnc
          (restrictSplits keep UC) := by
      simp only [restrictSplits, MGraph.batchEnc, MGraph.updateEnc]
    rw [hgoal, henc]
    omega

/-! ## The start potential -/

/-- **The start potential** is at most `2 ⌊log₂ (2 |M| + 1)⌋` per leaving end. There are two
ends per edge of `M \ keep`, and a block has at most `2 |M|` ends. -/
theorem markPot_le (keep M : Finset ℕ) (C : MGraph) :
    markPot keep M C ≤ 2 * (M \ keep).card * (2 * Nat.log 2 (2 * M.card + 1)) := by
  unfold markPot
  have hdisj : ((C.V : Set ℕ)).PairwiseDisjoint fun r => markBlock M C r \ edgeEnds keep := by
    intro r _ s _ hrs
    refine Finset.disjoint_left.mpr fun x h₁ h₂ => ?_
    rw [Finset.mem_sdiff, mem_markBlock] at h₁ h₂
    exact hrs (h₁.1.2.symm.trans h₂.1.2)
  have hsub : (C.V.biUnion fun r => markBlock M C r \ edgeEnds keep) ⊆ edgeEnds (M \ keep) := by
    intro x hx
    obtain ⟨r, _, hx⟩ := Finset.mem_biUnion.mp hx
    rw [Finset.mem_sdiff, mem_markBlock, mem_edgeEnds] at hx
    rw [mem_edgeEnds, Finset.mem_sdiff]
    exact ⟨hx.1.1, hx.2⟩
  have hsum : ∑ r ∈ C.V, (markBlock M C r \ edgeEnds keep).card ≤ 2 * (M \ keep).card := by
    rw [← Finset.card_biUnion hdisj, ← card_edgeEnds]
    exact Finset.card_le_card hsub
  calc ∑ r ∈ C.V, splitPot (edgeEnds keep) (markBlock M C r)
      ≤ ∑ r ∈ C.V, (markBlock M C r \ edgeEnds keep).card *
          (2 * Nat.log 2 (2 * M.card + 1)) := by
        refine Finset.sum_le_sum fun r _ =>
          le_trans (splitPot_le _ _) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_))
        refine Nat.log_mono_right (Nat.add_le_add_right ?_ 1)
        rw [← card_edgeEnds]
        exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (∑ r ∈ C.V, (markBlock M C r \ edgeEnds keep).card) *
          (2 * Nat.log 2 (2 * M.card + 1)) := by rw [Finset.sum_mul]
    _ ≤ 2 * (M \ keep).card * (2 * Nat.log 2 (2 * M.card + 1)) :=
        Nat.mul_le_mul_right _ hsum

/-- **The split lists of a core batch, with the log factor.** Under the hypotheses of
`cutLens_sum_le`, the lengths of the lists sum to at most the encoding size of the restricted
splits plus `4 ⌊log₂ (2 |M| + 1)⌋` per edge of `M \ keep`. -/
theorem cutLens_sum_le_log (keep : Finset ℕ) (UC : List Update) (M : Finset ℕ) (C S : MGraph)
    (hC : C.IsValid) (hB : C.BatchIsValid UC) (hM : M ⊆ C.E) (hk : keep ⊆ M) (hE : S.E = keep)
    (hends : ∀ e ∈ keep, S.tail e = C.tail e ∧ S.head e = C.head e)
    (hdel : ∀ e ∈ keep, Update.delete e ∉ UC) :
    (cutLens M C UC).sum ≤
      S.batchEnc (restrictSplits keep UC) + (M \ keep).card * (4 * Nat.log 2 (2 * M.card + 1)) := by
  have h₁ := cutLens_sum_le keep UC M C S hC hB hM hk hE hends hdel
  have h₂ := markPot_le keep M C
  have h₃ : 2 * (M \ keep).card * (2 * Nat.log 2 (2 * M.card + 1)) =
      (M \ keep).card * (4 * Nat.log 2 (2 * M.card + 1)) := by ring
  omega

end MinCostFlow.SparseCore.Program
