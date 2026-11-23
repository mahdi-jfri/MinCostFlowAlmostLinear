module

public import MinCostFlow.MinRatio.LastLevelContract

/-!
# The lengths read by the init of a branch (`AssemblyFirstInitLengths`)

The init of a branch builds the bundle state `initBundleTreeWithParams` of the input graph `G` and
its lengths `ℓ₀`. The buckets of the edges (`origBucket`) depend on `ℓ₀`, so the init must read
the lengths. It reads them as the init of P4 does (`AsmCompFamilyAt.init_runs`): one fixed-point
number of `L` limbs of `4` bits per edge, at `lengths + e L`, with precision `P`.

`BranchLengthsAt` bundles the three facts that the init of a branch asks about them, and
`BranchLengthsAt.of_agree` carries them across a change of memory that keeps their cells.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.MinRatio

/-- **The lengths of a branch init.** The lengths `ℓ₀` of `G` lie at `lengths` below `h`: the
block of `eCap` numbers of `L` limbs ends by `h`, every edge of `G` is below `eCap` and has a valid
positive number there, and `ℓ₀` is the function that these numbers give (`readEdgeValues`, with
`4`-bit limbs and precision `P`). -/
def BranchLengthsAt (mem : ℕ → ℕ) (lengths eCap L P h : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) :
    Prop :=
  lengths + eCap * L ≤ h ∧
  (∀ e ∈ G.E, e < eCap ∧ Num.Valid mem (lengths + e * L) 4 L ∧
    0 < readEdgeValues mem lengths 4 L P G.E e) ∧
  ℓ₀ = readEdgeValues mem lengths 4 L P G.E

/-- **The lengths survive a change of memory** that keeps the cells `[lengths, lengths + eCap L)`,
for any end `h'` of the block. -/
theorem BranchLengthsAt.of_agree {mem mem' : ℕ → ℕ} {lengths eCap L P h h' : ℕ} {G : MGraph}
    {ℓ₀ : ℕ → ℝ} (hb : BranchLengthsAt mem lengths eCap L P h G ℓ₀)
    (hag : ∀ a, lengths ≤ a → a < lengths + eCap * L → mem' a = mem a)
    (hh : lengths + eCap * L ≤ h') :
    BranchLengthsAt mem' lengths eCap L P h' G ℓ₀ := by
  obtain ⟨-, hAt, hℓ⟩ := hb
  have hcon : ∀ e ∈ G.E, ∀ i < L, mem' (lengths + e * L + i) = mem (lengths + e * L + i) :=
    fun e he i hi => by
      have h1 : (e + 1) * L ≤ eCap * L := Nat.mul_le_mul_right L (by have := (hAt e he).1; omega)
      rw [Nat.add_one_mul] at h1
      exact hag _ (by omega) (by omega)
  have heq : readEdgeValues mem' lengths 4 L P G.E = readEdgeValues mem lengths 4 L P G.E := by
    funext e
    unfold readEdgeValues
    by_cases he : e ∈ G.E
    · simp only [he, ↓reduceIte]
      unfold Num.fixVal
      rw [Num.intVal_congr (hcon e he)]
    · simp [he]
  refine ⟨hh, fun e he => ⟨(hAt e he).1, fun i hi => ?_, heq ▸ (hAt e he).2.2⟩, heq ▸ hℓ⟩
  rw [hcon e he i hi]
  exact (hAt e he).2.1 i hi

/-- The lengths of a branch init are positive on the edges of `G`. -/
theorem BranchLengthsAt.pos {mem : ℕ → ℕ} {lengths eCap L P h : ℕ} {G : MGraph} {ℓ₀ : ℕ → ℝ}
    (hb : BranchLengthsAt mem lengths eCap L P h G ℓ₀) : ∀ e ∈ G.E, 0 < ℓ₀ e := by
  intro e he
  rw [hb.2.2]
  exact (hb.2.1 e he).2.2

end MinCostFlow.SparseCore.Program
