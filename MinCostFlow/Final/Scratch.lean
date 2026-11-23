module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Entry

/-!
# Word bounds for the solver workspace

The scaling reduction on page 15 passes polynomially bounded circulations
to the solver. A polynomial scratch bound gives a word size at which the
solver contract applies to the encoded circulation.
-/

public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Absorb the scratch coefficient and allow two powers for the input,
output, and their sum with scratch. Degree four and coefficient one give
the original canonical multiplier five. -/
@[expose] def scratchWordMultiplier (coefficient degree : ℕ) : ℕ :=
  max 2 (Nat.clog 2 coefficient + degree) + 1

/-- The encoded circulation, its output, and polynomial scratch fit at
the canonical multiplier. -/
theorem scratch_fits (S : ℕ → ℕ → ℕ) (c d : ℕ) (J : Circulation)
    (hS : S J.n J.m ≤ c * (J.n + J.m + 2)^d) :
    J.solverWords.length + J.m + S J.n J.m <
      2^wordSize (scratchWordMultiplier c d) J.solverWords := by
  let xs := J.solverWords
  let B := xs.length + xs.foldr max 0 + 2
  let e := max 2 (Nat.clog 2 c + d)
  have hB : 2 ≤ B := by unfold B; omega
  have hb : 0 < B := by omega
  have hn : J.n ≤ xs.foldr max 0 := le_max_left _ _
  have hl : xs.length = 2 + 5 * J.m := J.solverWords_length
  have hbase : J.n + J.m + 2 ≤ B := by unfold B; omega
  have hc : c ≤ B^Nat.clog 2 c :=
    (Nat.le_pow_clog (by decide : 1 < 2) c).trans (Nat.pow_le_pow_left hB _)
  have hs : S J.n J.m ≤ B^e := calc
    _ ≤ c * (J.n + J.m + 2)^d := hS
    _ ≤ B^Nat.clog 2 c * B^d := Nat.mul_le_mul hc (Nat.pow_le_pow_left hbase _)
    _ = B^(Nat.clog 2 c + d) := (pow_add ..).symm
    _ ≤ B^e := Nat.pow_le_pow_right hb (le_max_right _ _)
  have hlen : xs.length + J.m ≤ 2 * B := by unfold B; omega
  have hout : xs.length + J.m ≤ B^e := calc
    _ ≤ 2 * B := hlen
    _ ≤ B^2 := by rw [pow_two]; exact Nat.mul_le_mul_right B hB
    _ ≤ B^e := Nat.pow_le_pow_right hb (le_max_left _ _)
  calc
    _ ≤ 2 * B^e := by change xs.length + J.m + S J.n J.m ≤ _; omega
    _ ≤ B^(e+1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hB
    _ < _ := pow_lt_two_pow_wordSize (by omega) xs

/-- The polynomial scratch policy recovers the original guest multiplier. -/
theorem scratchWordMultiplier_original : scratchWordMultiplier 1 4 = 5 := by
  decide

/-- The solver call condition holds in fresh memory at the polynomial
scratch multiplier, for every circulation with the scaling bounds. -/
theorem polynomialScratch_pre (T S : ℕ → ℕ → ℕ) (c d : ℕ) (J : Circulation)
    (hS : S J.n J.m ≤ c * (J.n + J.m + 2)^d)
    (hc : J.CostsBounded (J.m^10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) :
    let w := wordSize (scratchWordMultiplier c d) J.solverWords
    (∀ a ∈ [0,J.solverWords.length], a < 2^w) ∧
      (solverContract w T S).pre [0,J.solverWords.length] (initMem J.solverWords) := by
  dsimp only
  have hfit := scratch_fits S c d J hS
  have hcpos : 1 ≤ scratchWordMultiplier c d := by unfold scratchWordMultiplier; omega
  have hAt := listAt_initMem J.solverWords
  refine ⟨?_, ⟨?_, zeroFrom_initMem J.solverWords, ?_⟩⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  · exact ⟨0, J.solverWords.length, rfl, J, hAt, by omega,
      fun _ hx => lt_two_pow_wordSize_of_mem hcpos hx, hc, hfit, hu⟩
  · change J.solverWords.length + ((solverDimensions _ _).2 + S
      (solverDimensions _ _).1 (solverDimensions _ _).2) < _
    rw [solverDimensions_of_at J _ 0 J.solverWords.length hAt, ← Nat.add_assoc]
    exact hfit


/-- Polynomial scratch accommodates a compressed canonical call at
the same guest width as the unrestricted layout. -/
theorem polynomialScratch_compressed_pre (T S : ℕ → ℕ → ℕ) (c d : ℕ) (J : Circulation)
    (hn : J.n ≤ 2*J.m+1)
    (hS : S J.n J.m ≤ c*(J.n+J.m+2)^d)
    (hc : J.CostsBounded (J.m^10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) :
    let w := wordSize (scratchWordMultiplier c d) J.solverWords
    (∀ a ∈ [0,J.solverWords.length], a < 2^w) ∧
      (compressedSolverContract w T S).pre [0,J.solverWords.length] (initMem J.solverWords) := by
  obtain ⟨hWords, hPre⟩ := polynomialScratch_pre T S c d J hS hc hu
  refine ⟨hWords, hPre, ?_⟩
  rw [solverDimensions_of_at J _ 0 J.solverWords.length (listAt_initMem _)]
  exact hn

end MinCostFlow.Final
