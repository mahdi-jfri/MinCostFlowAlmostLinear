module

public import MinCostFlow.IPM.Machine.InitialAuxiliaryEdge
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Output prefixes of the auxiliary-edge initialization scan

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) visits the vertices and adds one edge for each
nonzero deficit. The machine enumerates them in increasing vertex
order, as does `deficitIndex`. The output prefix concatenates the
already verified individual records. A zero deficit contributes no
words, so five words per visited vertex are a worst-case space bound.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Records emitted while visiting the first `k` vertices. -/
def initialAuxiliaryPrefix (incoming outgoing : ℕ → ℕ) (n penalty : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => initialAuxiliaryPrefix incoming outgoing n penalty k ++
      initialAuxiliaryWords k n (incoming k) (outgoing k) penalty

/-- A vertex contributes either no record or exactly five words. -/
theorem initialAuxiliaryWords_length (v n incoming outgoing penalty : ℕ) :
    (initialAuxiliaryWords v n incoming outgoing penalty).length =
      if incoming = outgoing then 0 else 5 := by
  simp only [initialAuxiliaryWords]
  split_ifs <;> rfl

/-- The emitted prefix fits in the five-word-per-vertex reservation. -/
theorem initialAuxiliaryPrefix_length_le (incoming outgoing : ℕ → ℕ) (n penalty k : ℕ) :
    (initialAuxiliaryPrefix incoming outgoing n penalty k).length ≤ 5*k := by
  induction k with
  | zero => simp [initialAuxiliaryPrefix]
  | succ k ih =>
    rw [initialAuxiliaryPrefix,List.length_append,initialAuxiliaryWords_length]
    split_ifs <;> omega

/-- The output length counts exactly the nonzero doubled deficits. -/
theorem initialAuxiliaryPrefix_length (incoming outgoing : ℕ → ℕ) (n penalty k : ℕ) :
    (initialAuxiliaryPrefix incoming outgoing n penalty k).length =
      ∑ i ∈ Finset.range k, if incoming i = outgoing i then 0 else 5 := by
  induction k with
  | zero => simp [initialAuxiliaryPrefix]
  | succ k ih =>
    rw [initialAuxiliaryPrefix,List.length_append,initialAuxiliaryWords_length,
      Finset.sum_range_succ,ih]

/-- Only the visited table coordinates affect the emitted prefix. This
allows heap-framing proofs to preserve the source tables without assuming
that two whole memories, including scratch cells, are equal. -/
theorem initialAuxiliaryPrefix_congr (incoming outgoing incoming' outgoing' : ℕ → ℕ)
    (n penalty k : ℕ) (hi : ∀ i < k, incoming i = incoming' i)
    (ho : ∀ i < k, outgoing i = outgoing' i) :
    initialAuxiliaryPrefix incoming outgoing n penalty k =
      initialAuxiliaryPrefix incoming' outgoing' n penalty k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [initialAuxiliaryPrefix,initialAuxiliaryPrefix,
      ih (fun i hh => hi i (Nat.lt_trans hh (Nat.lt_succ_self k)))
        (fun i hh => ho i (Nat.lt_trans hh (Nat.lt_succ_self k))),
      hi k (Nat.lt_succ_self k),ho k (Nat.lt_succ_self k)]

end MinCostFlow.IPM.Machine
