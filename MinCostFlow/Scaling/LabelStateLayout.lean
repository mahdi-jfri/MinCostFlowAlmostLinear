module

public import MinCostFlow.Scaling.LabelTraversal
public import MinCostFlow.Scaling.SignedTableLayout
public import MinCostFlow.Scaling.BoolTableLayout
public import MinCostFlow.Scaling.AdjacencyLayout
import WordRAM.Memory

/-!
# The stored label-propagation state

The traversal state has a pending-list pointer and length, signed labels,
visited flags, and outgoing adjacency heads. These arrays occupy one fixed
prefix. Immutable edge-list nodes follow a one-cell null gap. This file
fixes the addresses and proves that fresh allocation preserves the state.
The layout contains only representations of the model's state fields.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The two-word pending-list header precedes the signed labels. -/
def labelLabels (base : ℕ) : ℕ := base+2

/-- Visited flags follow the two-word label cells. -/
def labelSeen (n base : ℕ) : ℕ := base+2+2*n

/-- Outgoing head/length records follow the visited flags. -/
def labelHeads (n base : ℕ) : ℕ := base+2+3*n

/-- Immutable node storage follows all vertex arrays and a null gap. -/
def labelNodes (n base : ℕ) : ℕ := base+3+5*n

/-- The exact stored representation of the label model's four state fields. -/
def LabelStateAt {J : Circulation} (mem : ℕ → ℕ) (base bound : ℕ)
    (s : Circulation.LabelState J) : Prop :=
  ∃ ptr, ListAt mem base [ptr, s.pending.length] ∧
    IndexListAt mem (labelNodes J.n base) bound ptr s.pending ∧
    SignedTableAt mem (labelLabels base) s.labels ∧
    BoolTableAt mem (labelSeen J.n base) s.seen ∧
    AdjacencyAt mem (labelHeads J.n base) (labelNodes J.n base) bound s.outgoing

/-- Preserving the old state cells preserves all model values, while the
allowed immutable-node range may grow with fresh allocations. -/
theorem LabelStateAt.of_agree_below {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {s : Circulation.LabelState J}
    (hat : LabelStateAt mem base bound s) (hnodes : labelNodes J.n base ≤ bound)
    (hbound : bound ≤ bound') (hframe : ∀ x < bound, mem' x = mem x) :
    LabelStateAt mem' base bound' s := by
  obtain ⟨ptr, hheader, hpending, hlabels, hseen, hout⟩ := hat
  refine ⟨ptr, hheader.of_agree_below (h₀ := bound) ?_ hframe,
    (hpending.of_agree (fun x _ hx => hframe x hx)).mono le_rfl hbound,
    hlabels.of_agree_below ?_ hframe, hseen.of_agree_below ?_ hframe,
    hout.of_agree_below ?_ hbound hframe⟩
  · change base+2 ≤ bound
    dsimp only [labelNodes] at hnodes
    omega
  · dsimp only [labelLabels, labelNodes] at *
    omega
  · dsimp only [labelSeen, labelNodes] at *
    omega
  · dsimp only [labelHeads, labelNodes] at *
    omega

/-- Preserving only the state range preserves its values, independently
of writes to an input prefix before the state. Fresh allocation may widen
the allowed immutable-node range. -/
theorem LabelStateAt.of_agree_range {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {s : Circulation.LabelState J}
    (hat : LabelStateAt mem base bound s) (hnodes : labelNodes J.n base ≤ bound)
    (hbound : bound ≤ bound')
    (hframe : ∀ x, base ≤ x → x < bound → mem' x = mem x) : LabelStateAt mem' base bound' s := by
  obtain ⟨ptr, hheader, hpending, hlabels, hseen, hout⟩ := hat
  have hn : base+3+5*J.n ≤ bound := hnodes
  refine ⟨ptr, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < 2 := hi
    exact (hframe _ (by omega) (by omega)).trans (hheader i hi)
  · apply (hpending.of_agree ?_).mono le_rfl hbound
    intro x hx hxend
    exact hframe x (by dsimp [labelNodes] at hx; omega) hxend
  · apply hlabels.of_agree
    intro x hx hxend
    exact hframe x (by dsimp [labelLabels] at hx; omega)
      (by dsimp [labelLabels] at hxend; omega)
  · apply hseen.of_agree
    intro x hx hxend
    exact hframe x (by dsimp [labelSeen] at hx; omega)
      (by dsimp [labelSeen] at hxend; omega)
  · apply hout.of_agree hbound
    · intro x hx hxend
      exact hframe x (by dsimp [labelHeads] at hx; omega)
        (by dsimp [labelHeads] at hxend; omega)
    · intro x hx hxend
      exact hframe x (by dsimp [labelNodes] at hx; omega) hxend

/-- Replacing labels and visited flags preserves the other state fields when
the pending header, outgoing heads, and old immutable nodes are unchanged. -/
theorem LabelStateAt.with_labels_seen {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {s : Circulation.LabelState J}
    (hat : LabelStateAt mem base bound s) (labels : Fin J.n → ℤ) (seen : Fin J.n → Bool)
    (hbound : bound ≤ bound') (hlabels : SignedTableAt mem' (labelLabels base) labels)
    (hseen : BoolTableAt mem' (labelSeen J.n base) seen)
    (hheader : ∀ x, base ≤ x → x < base+2 → mem' x = mem x)
    (hheads : ∀ x, labelHeads J.n base ≤ x → x < labelHeads J.n base+2*J.n → mem' x = mem x)
    (hnodes : ∀ x, labelNodes J.n base ≤ x → x < bound → mem' x = mem x) :
    LabelStateAt mem' base bound' { s with labels := labels, seen := seen } := by
  obtain ⟨ptr, hstored, hpending, _, _, hout⟩ := hat
  refine ⟨ptr, ?_, (hpending.of_agree hnodes).mono le_rfl hbound,
    hlabels, hseen, hout.of_agree hbound hheads hnodes⟩
  intro i hi
  have hi' : i < 2 := hi
  exact (hheader _ (by omega) (by omega)).trans (hstored i hi)

/-- A fresh zero tail represents the all-empty, all-zero state before its
root and outgoing lists are initialized. -/
theorem labelStateAt_empty (J : Circulation) {mem : ℕ → ℕ} {base bound : ℕ}
    (hzero : ZeroFrom mem base) : LabelStateAt mem base bound
      { labels := fun _ => 0, seen := fun _ => false, outgoing := fun _ => [], pending := [] :
        Circulation.LabelState J } := by
  refine ⟨0, ?_, .nil, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl <;> rw [hzero _ (by omega)] <;> rfl
  · intro v i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl <;> rw [hzero _ (by dsimp [labelLabels]; omega)] <;> rfl
  · apply boolTableAt_false
    intro x hx
    exact hzero x (by dsimp [labelSeen] at hx; omega)
  · apply adjacencyAt_empty
    intro x hx
    exact hzero x (by dsimp [labelHeads] at hx; omega)

/-- The empty physical state, its full array prefix, and its fresh node tail
have simultaneous witnesses for every circulation dimension. -/
theorem exists_emptyLabelStateAt (J : Circulation) :
    ∃ mem bound, labelNodes J.n 0 ≤ bound ∧ ZeroFrom mem bound ∧
      LabelStateAt mem 0 bound
        { labels := fun _ => 0, seen := fun _ => false, outgoing := fun _ => [], pending := [] :
          Circulation.LabelState J } := by
  exact ⟨fun _ => 0, labelNodes J.n 0, le_rfl, fun _ _ => rfl, labelStateAt_empty J (fun _ _ => rfl)⟩

end MinCostFlow.Scaling.Machine
