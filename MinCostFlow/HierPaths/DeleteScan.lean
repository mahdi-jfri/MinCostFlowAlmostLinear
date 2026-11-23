module

public import MinCostFlow.HierPaths.LossCountersRun

/-!
# The scan of a reverse list

The first part of `Delete(e)` scans the reverse list of `e`. Each listed
terminal that has not failed before is marked directly failed, and the loss counters run their
step `failStep` (`failStep_spec`) on it. The scan collects the terminals that become globally lost.

`scan_spec`: if the counters are correct for the failed set `F` and every listed terminal is below
`2 ^ x`, then after the scan the counters are correct for `F ∪ l`, and the collected list has no
repetition and is exactly the new global lost set minus the old one. `scan_updates_ge` and
`scan_enumerated_ge`: the operation counters of the loss counters only grow.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- One entry of the scan: a terminal that has not failed runs `failStep`, and its newly lost
terminals are appended to the output. -/
def scanStep (x b : ℕ) (acc : LossState × List ℕ) (t : ℕ) : LossState × List ℕ :=
  if t ∈ acc.1.failed then acc
  else ((failStep x b t acc.1).1, acc.2 ++ (failStep x b t acc.1).2)

/-- The scan of the list `l` from the counter state `st`. -/
def scan (x b : ℕ) (st : LossState) (l : List ℕ) : LossState × List ℕ :=
  l.foldl (scanStep x b) (st, [])

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open Finset

variable {x b : ℕ}

/-- The list `out` lists, without repetition, the elements of `new` that are not in `old`, and
`old ⊆ new`. -/
private def NewOut (old new : Finset ℕ) (out : List ℕ) : Prop :=
  old ⊆ new ∧ out.Nodup ∧ out.toFinset = new \ old

private theorem NewOut.append {A B C : Finset ℕ} {l l' : List ℕ} (h : NewOut A B l)
    (h' : NewOut B C l') : NewOut A C (l ++ l') := by
  obtain ⟨hAB, hl, hlB⟩ := h
  obtain ⟨hBC, hl', hlC⟩ := h'
  refine ⟨hAB.trans hBC, List.nodup_append.mpr ⟨hl, hl', ?_⟩, ?_⟩
  · intro a ha a' ha' he
    subst he
    have h1 : a ∈ B \ A := hlB ▸ List.mem_toFinset.mpr ha
    have h2 : a ∈ C \ B := hlC ▸ List.mem_toFinset.mpr ha'
    exact (mem_sdiff.mp h2).2 (mem_sdiff.mp h1).1
  · rw [List.toFinset_append, hlB, hlC]
    ext a
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro (⟨ha, hn⟩ | ⟨ha, hn⟩)
      · exact ⟨hBC ha, hn⟩
      · exact ⟨ha, fun h => hn (hAB h)⟩
    · rintro ⟨ha, hn⟩
      by_cases hb : a ∈ B
      · exact Or.inl ⟨hb, hn⟩
      · exact Or.inr ⟨ha, hb⟩

private theorem levelStep_counters (u j Δ : ℕ) (st : LossState) :
    st.updates ≤ (levelStep x b u j Δ st).1.updates ∧
      st.enumerated ≤ (levelStep x b u j Δ st).1.enumerated := by
  rw [levelStep_updates, levelStep_enumerated]
  omega

private theorem climb_counters (u : ℕ) :
    ∀ (j Δ : ℕ) (st : LossState), st.updates ≤ (climb x b u j Δ st).1.updates ∧
      st.enumerated ≤ (climb x b u j Δ st).1.enumerated
  | 0, _, st => by simp [climb]
  | j + 1, Δ, st => by
    unfold climb
    split_ifs
    · exact ⟨le_rfl, le_rfl⟩
    · have h1 := levelStep_counters (x := x) (b := b) u j Δ st
      have h2 := climb_counters u j (levelStep x b u j Δ st).2.2 (levelStep x b u j Δ st).1
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

private theorem failStep_counters (u : ℕ) (st : LossState) :
    st.updates ≤ (failStep x b u st).1.updates ∧
      st.enumerated ≤ (failStep x b u st).1.enumerated := by
  unfold failStep
  dsimp only
  have h := climb_counters (x := x) (b := b) u (leafDepth x b) 1
    (enumerate ⟨setAt st.own (leafDepth x b) (groupOf x b (leafDepth x b) u)
      (st.own (leafDepth x b) (groupOf x b (leafDepth x b) u) + 1), st.sum, insert u st.failed,
      st.glob, st.updates + 1, st.enumerated⟩ [u]).1
  simp only [enumerate] at h ⊢
  omega

private theorem scan_fold (l : List ℕ) :
    ∀ (G0 F : Finset ℕ) (acc : LossState × List ℕ), LossInv x b F acc.1 →
      NewOut G0 (globalLost x b F) acc.2 → (∀ t ∈ l, t < 2 ^ x) →
      LossInv x b (F ∪ l.toFinset) (l.foldl (scanStep x b) acc).1 ∧
        NewOut G0 (globalLost x b (F ∪ l.toFinset)) (l.foldl (scanStep x b) acc).2 ∧
        acc.1.updates ≤ (l.foldl (scanStep x b) acc).1.updates ∧
        acc.1.enumerated ≤ (l.foldl (scanStep x b) acc).1.enumerated := by
  induction l with
  | nil => intro G0 F acc h1 h2 _; simpa using ⟨h1, h2⟩
  | cons t l ih =>
    intro G0 F acc hinv hout hl
    rw [List.foldl_cons]
    have hl' : ∀ s ∈ l, s < 2 ^ x := fun s hs => hl s (List.mem_cons_of_mem _ hs)
    by_cases ht : t ∈ acc.1.failed
    · have hstep : scanStep x b acc t = acc := by simp [scanStep, ht]
      rw [hstep]
      have hF : F ∪ (t :: l).toFinset = F ∪ l.toFinset := by
        rw [hinv.failed] at ht
        ext s; simp only [mem_union, List.mem_toFinset, List.mem_cons]
        constructor
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl ht
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      rw [hF]
      exact ih G0 F acc hinv hout hl'
    · have htF : t ∉ F := by rw [← hinv.failed]; exact ht
      obtain ⟨hinv', hnd, heq⟩ := failStep_spec hinv (hl t (List.mem_cons_self ..)) htF
      have hstep : scanStep x b acc t =
          ((failStep x b t acc.1).1, acc.2 ++ (failStep x b t acc.1).2) := by
        rw [scanStep]; simp only [ht, ↓reduceIte]
      rw [hstep]
      have hout' : NewOut G0 (globalLost x b (insert t F))
          (acc.2 ++ (failStep x b t acc.1).2) :=
        hout.append ⟨globalLost_mono (subset_insert t F), hnd, heq⟩
      have hF : F ∪ (t :: l).toFinset = insert t F ∪ l.toFinset := by
        ext s; simp only [mem_union, List.mem_toFinset, List.mem_cons, mem_insert]; tauto
      obtain ⟨a1, a2, a3, a4⟩ := ih G0 (insert t F) ((failStep x b t acc.1).1, acc.2 ++ (failStep x b t acc.1).2)
        hinv' hout' hl'
      have hc := failStep_counters (x := x) (b := b) t acc.1
      rw [hF]
      exact ⟨a1, a2, hc.1.trans a3, hc.2.trans a4⟩

public section

/-- The scan keeps the loss counters correct, and outputs, without repetition, exactly the
terminals that became globally lost. -/
theorem scan_spec {F : Finset ℕ} {st : LossState} (hinv : LossInv x b F st) {l : List ℕ}
    (hl : ∀ t ∈ l, t < 2 ^ x) :
    LossInv x b (F ∪ l.toFinset) (scan x b st l).1 ∧
      (scan x b st l).2.Nodup ∧
      (scan x b st l).2.toFinset = globalLost x b (F ∪ l.toFinset) \ globalLost x b F ∧
      st.updates ≤ (scan x b st l).1.updates ∧ st.enumerated ≤ (scan x b st l).1.enumerated := by
  obtain ⟨a1, a2, a3, a4⟩ := scan_fold l (globalLost x b F) F (st, []) hinv
    ⟨Subset.rfl, List.nodup_nil, by simp⟩ hl
  exact ⟨a1, a2.2.1, a2.2.2, a3, a4⟩

end

end MinCostFlow.HierPaths
