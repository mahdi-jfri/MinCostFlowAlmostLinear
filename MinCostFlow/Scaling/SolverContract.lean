module

public import MinCostFlow.Scaling.SolverAdapter
public import WordRAM.Layout
import WordRAM.Entry
import Mathlib.Tactic.NormNum

/-!
# Memory interface for the bounded circulation solver

Appendix C of Chen et al., arXiv:2203.00671v2, Lemma C.1 reduces to exact
integral circulation solves with polynomial costs and capacities. A solver
call takes `[input, heap]`. The input contains `n, m`, followed by five words
per edge: tail, head, capacity, cost sign, and cost magnitude. Sign one means
negative. The output starts at the old heap and contains one nonnegative
integer per edge. All feasible circulation coordinates are nonnegative.

The contract uses the shared heap discipline. The solver preserves the input
and all other memory below the heap, returns a new heap pointer, and leaves
fresh memory after that pointer zero. Its mathematical postcondition asks
only for an integral optimum against real flows. It does not prescribe how
an algorithm chooses between several optima.
-/

@[expose] public section
namespace MinCostFlow.Scaling
namespace Circulation

/-- The five machine words of an edge in the bounded solver's input. -/
def solverEdgeWords (J : Circulation) (e : Fin J.m) : List ℕ :=
  [J.tail e, J.head e, J.capacity e, if J.cost e < 0 then 1 else 0, (J.cost e).natAbs]

/-- The solver's contiguous input layout: two header words and five per edge. -/
def solverWords (J : Circulation) : List ℕ :=
  J.n :: J.m :: (List.finRange J.m).flatMap J.solverEdgeWords

/-- The exact size needed for the solver's input. -/
theorem solverWords_length (J : Circulation) : J.solverWords.length = 2 + 5 * J.m := by
  simp only [solverWords, List.length_cons, List.length_flatMap, solverEdgeWords,
    List.length_cons, List.length_nil]
  simp
  omega

/-- Any selected list of circulation edge records uses five words per edge. -/
theorem solverEdgeRecords_length (J : Circulation) (es : List (Fin J.m)) :
    (es.flatMap J.solverEdgeWords).length = 5 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, solverEdgeWords,
      List.length_cons, List.length_nil, ih]
    omega

/-- Every selected edge-record word also occurs in the full input encoding. -/
theorem solverEdgeWord_mem (J : Circulation) (e : Fin J.m) {x : ℕ}
    (hx : x ∈ J.solverEdgeWords e) : x ∈ J.solverWords :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨e, List.mem_finRange e, hx⟩))

/-- Read the solver's output as an integral flow. No signed decoding is needed. -/
def readSolverFlow (J : Circulation) (mem : ℕ → ℕ) (a : ℕ) : Fin J.m → ℤ :=
  fun e => (mem (a + e.val) : ℤ)

/-- The representation holds for every possible integral optimum: the
nonnegative coordinate can be stored without a sign word. -/
theorem readSolverFlow_of_table (J : Circulation) (f : Fin J.m → ℤ)
    (hf : J.Feasible (fun e => (f e : ℝ))) (mem : ℕ → ℕ) (a : ℕ)
    (hat : WordRAM.ListAt mem a (List.ofFn (fun e => (f e).toNat))) :
    J.readSolverFlow mem a = f := by
  funext e
  have hh := hat e.val (by simp only [List.length_ofFn]; exact e.isLt)
  simp only [List.getElem_ofFn] at hh
  change (mem (a + e.val) : ℤ) = f e
  rw [hh]
  exact Int.toNat_of_nonneg (Int.cast_nonneg_iff.mp (hf.2 e).1)

end Circulation

namespace Machine
open WordRAM

/-- Read dimensions from the first two input words of a solver call. -/
def solverDimensions (args : List ℕ) (mem : ℕ → ℕ) : ℕ × ℕ :=
  (mem (args.getD 0 0), mem (args.getD 0 0 + 1))

/-- A cost parameter is nondecreasing in both dimensions. This is the only
regularity of `T` used when bounding the sizes of nested calls. -/
def SolverTimeMonotone (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ n n' m m', n ≤ n' → m ≤ m' → T n m ≤ T n' m'

/-- Output and scratch space reserved for one bounded circulation solve.
The polynomial scratch block is separate from the numerical time estimate. -/
def solverSpace (n m : ℕ) : ℕ := m + (n + m + 2) ^ 4

/-- Polynomial scratch policy used by the canonical adapter. -/
def solverScratch (n m : ℕ) : ℕ := (n + m + 2) ^ 4

/-- Exact bounded-circulation procedure contract. Arguments are `[input, heap]`.
The output has `m` cells at `heap`, followed by at most `S n m` scratch
cells. Both regions must fit in the caller's address space. The body costs at most `T n m`. Space is independent of the numerical
time estimate, which need not itself fit in a word. Polynomial input bounds
refer to this instance's own edge count. -/
def solverContract (w : ℕ) (T S : ℕ → ℕ → ℕ) : Contract :=
  heapContract w
    (fun args mem => ∃ a h : ℕ, args = [a, h] ∧ ∃ J : Circulation,
      ListAt mem a J.solverWords ∧ a + J.solverWords.length ≤ h ∧
      (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ J.CostsBounded (J.m ^ 10) ∧
      h + J.m + S J.n J.m < 2 ^ w ∧ ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (fun args mem mem' => ∀ J : Circulation,
      ListAt mem (args.getD 0 0) J.solverWords →
      J.Optimal (fun e => (J.readSolverFlow mem' (heapArg args) e : ℝ)))
    (fun args mem => T (solverDimensions args mem).1 (solverDimensions args mem).2)
    (fun args mem => (solverDimensions args mem).2 +
      S (solverDimensions args mem).1 (solverDimensions args mem).2)

/-- The exact bounded solver on the compressed inputs of Appendix C.
One extra vertex is allowed for the dummy loops in the positive-capacity
encoding. The output, memory and cost requirements are unchanged. -/
def compressedSolverContract (w : ℕ) (T S : ℕ → ℕ → ℕ) : Contract :=
  { solverContract w T S with
    pre := fun args mem =>
      (solverContract w T S).pre args mem ∧
      (solverDimensions args mem).1 ≤ 2 * (solverDimensions args mem).2 + 1 }

/-- An unrestricted solver also solves every compressed input. -/
theorem meets_compressedSolverContract {w entry : ℕ} {p : Program} {T S : ℕ → ℕ → ℕ}
    (h : MeetsContract w p entry (solverContract w T S)) :
    MeetsContract w p entry (compressedSolverContract w T S) := by
  intro args mem pos ω hwords hpre
  exact h args mem pos ω hwords hpre.1

/-- Dimensions in the cost and space formulas agree with the encoded graph. -/
theorem solverDimensions_of_at (J : Circulation) (mem : ℕ → ℕ) (a h : ℕ)
    (hat : ListAt mem a J.solverWords) : solverDimensions [a, h] mem = (J.n, J.m) := by
  have hn := hat 0 (by simp only [Circulation.solverWords, List.length_cons]; omega)
  have hm := hat 1 (by simp only [Circulation.solverWords, List.length_cons]; omega)
  simp only [Circulation.solverWords, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_zero] at hn hm
  simp only [solverDimensions, List.getD_cons_zero, hn, hm]

/-- A guest width that includes the advertised output and scratch block.
For arbitrary `S`, its value appears explicitly in the width's input bound. -/
def solverWordSize (S : ℕ → ℕ → ℕ) (J : Circulation) : ℕ :=
  wordSize 1 (J.solverWords ++ [J.solverWords.length + J.m + S J.n J.m + 1])

/-- Every bounded instance fits a canonical call at a width that accounts
for its advertised scratch space, with no growth restriction on `S`. -/
theorem solver_pre_wordSize (T S : ℕ → ℕ → ℕ) (J : Circulation)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) :
    (∀ a ∈ [0, J.solverWords.length], a < 2 ^ solverWordSize S J) ∧
      (solverContract (solverWordSize S J) T S).pre
        [0, J.solverWords.length] (initMem J.solverWords) := by
  let input := J.solverWords ++ [J.solverWords.length + J.m + S J.n J.m + 1]
  let w := wordSize 1 input
  have hlast : J.solverWords.length + J.m + S J.n J.m + 1 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ (List.mem_cons_self))
  have hat := listAt_initMem J.solverWords
  have hd := solverDimensions_of_at J _ 0 J.solverWords.length hat
  have houtput : J.solverWords.length + J.m + S J.n J.m < 2 ^ w := by
    omega
  change (∀ a ∈ [0, J.solverWords.length], a < 2 ^ w) ∧
    (solverContract w T S).pre [0, J.solverWords.length] (initMem J.solverWords)
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  · refine ⟨?_, zeroFrom_initMem J.solverWords, ?_⟩
    · refine ⟨0, J.solverWords.length, rfl, J, hat, ?_, ?_, hc, houtput, hu⟩
      · omega
      · intro x hx
        exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
    · change J.solverWords.length +
        ((solverDimensions [0, J.solverWords.length] (initMem J.solverWords)).2 +
        S (solverDimensions [0, J.solverWords.length] (initMem J.solverWords)).1
          (solverDimensions [0, J.solverWords.length] (initMem J.solverWords)).2) < 2 ^ w
      rw [hd]
      dsimp only
      omega

/-- The solver preconditions are jointly satisfiable for every bounded
instance and every advertised scratch-space function. -/
theorem exists_solver_pre (T S : ℕ → ℕ → ℕ) (J : Circulation)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) :
    ∃ w, (∀ a ∈ [0, J.solverWords.length], a < 2 ^ w) ∧
      (solverContract w T S).pre [0, J.solverWords.length] (initMem J.solverWords) :=
  ⟨solverWordSize S J, solver_pre_wordSize T S J hc hu⟩

end Machine
end MinCostFlow.Scaling
