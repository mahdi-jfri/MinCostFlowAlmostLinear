module

public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.DeterministicExecution
import MinCostFlow.Scaling.ExactSolver
import WordRAM.Entry
import WordRAM.Exec
import WordRAM.Memory
import Mathlib.Tactic.Linarith

/-!
# A fixed solver function for canonical calls at a fixed word size

The scaling model needs a function of the circulation instance. To obtain
one from the optimality-only machine contract, calls use the same canonical
addresses and zero initial memory, at a fixed guest word size. A later memory
relocation places that execution in fresh host memory.

For inputs not admissible at the guest word size, a finite exact solver
extends the mathematical function. That branch is not used by admissible
machine calls. It lets the round-1 theorems keep their universal mathematical
solver specification while word-size bounds are checked on actual calls.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The arguments and memory of a canonical solver call fit its machine
contract. This is an input-memory condition, not an additional solver guarantee. -/
@[expose] def CanonicalInput (w : ℕ) (T : ℕ → ℕ → ℕ) (J : Circulation) : Prop :=
  (∀ a ∈ [0, J.solverWords.length], a < 2 ^ w) ∧
    (solverContract w T solverScratch).pre [0, J.solverWords.length] (initMem J.solverWords)

private theorem canonical_output_exists
    (w : ℕ) (p : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T solverScratch))
    (J : Circulation) (hin : CanonicalInput w T J) :
    ∃ flow : Fin J.m → ℤ, J.Optimal (fun e => (flow e : ℝ)) ∧
      ∃ body o st cost, p.procs[f]? = some body ∧
        Runs w p (fun _ => false) body
          (startState [0, J.solverWords.length] (initMem J.solverWords) 0) o st cost ∧
        cost ≤ T J.n J.m ∧ flow = J.readSolverFlow st.mem J.solverWords.length := by
  obtain ⟨body, hbody, o, st, cost, hrun, hpost, hcost⟩ :=
    hproc [0, J.solverWords.length] (initMem J.solverWords) 0 (fun _ => false) hin.1 hin.2
  have hat := listAt_initMem J.solverWords
  have hout := hpost.2.2.2.2 J hat
  have hd := solverDimensions_of_at J _ 0 J.solverWords.length hat
  change cost ≤ T (solverDimensions [0, J.solverWords.length] (initMem J.solverWords)).1
    (solverDimensions [0, J.solverWords.length] (initMem J.solverWords)).2 at hcost
  rw [hd] at hcost
  exact ⟨J.readSolverFlow st.mem J.solverWords.length, hout,
    body, o, st, cost, hbody, hrun, hcost, rfl⟩

/-- The function used by the scaling model for canonical calls at word size `w`.
An exact finite solver supplies values outside the admissible machine inputs. -/
noncomputable def canonicalSolverAt
    (w : ℕ) (p : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T solverScratch))
    (J : Circulation) : Fin J.m → ℤ := by
  classical
  exact if hin : CanonicalInput w T J then
    Classical.choose (canonical_output_exists w p f T hproc J hin)
  else J.exactSolver

/-- The extracted function meets the model's mathematical specification on
all graphs. The finite extension is only a proof device outside admissible calls. -/
theorem canonicalSolverAt_optimal
    (w : ℕ) (p : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T solverScratch)) (J : Circulation) :
    J.Optimal (fun e => (canonicalSolverAt w p f T hproc J e : ℝ)) := by
  classical
  unfold canonicalSolverAt
  split
  · exact (Classical.choose_spec (canonical_output_exists w p f T hproc J ‹_›)).1
  · exact J.exactSolver_optimal

/-- Every canonical call in a deterministic program returns the same
mathematical flow, even when supplied with a different random tape. -/
theorem canonicalSolverAt_eq_of_run
    {w : ℕ} {p : Program} {f : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : MeetsContract w p f (solverContract w T solverScratch)) (hp : p.IsDeterministic)
    (J : Circulation) (hin : CanonicalInput w T J)
    {body : Stmt} {o : Outcome} {st : State} {cost : ℕ} {ω : ℕ → Bool}
    (hbody : p.procs[f]? = some body)
    (hrun : Runs w p ω body
      (startState [0, J.solverWords.length] (initMem J.solverWords) 0) o st cost) :
    J.readSolverFlow st.mem J.solverWords.length = canonicalSolverAt w p f T hproc J := by
  classical
  have hspec := Classical.choose_spec (canonical_output_exists w p f T hproc J hin)
  obtain ⟨body', o', st', cost', hb', hr', _, heq⟩ := hspec.2
  have hb : body' = body := Option.some.inj (hb'.symm.trans hbody)
  subst body'
  have hrfalse := runs_of_deterministic hp (ω' := fun _ => false)
    (hp body (List.mem_of_getElem? hbody)) hrun
  have hstates := (hrfalse.det hr').2.1
  unfold canonicalSolverAt
  rw [dite_eq_left hin, heq, hstates]

/-- A selected canonical execution exists at the chosen guest word size. -/
theorem canonicalSolverAt_has_run
    (w : ℕ) (p : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T solverScratch))
    (J : Circulation) (hin : CanonicalInput w T J) :
    ∃ body o st cost, p.procs[f]? = some body ∧
      Runs w p (fun _ => false) body
        (startState [0, J.solverWords.length] (initMem J.solverWords) 0) o st cost ∧
      cost ≤ T J.n J.m ∧
      canonicalSolverAt w p f T hproc J = J.readSolverFlow st.mem J.solverWords.length := by
  classical
  have hh := (Classical.choose_spec (canonical_output_exists w p f T hproc J hin)).2
  simpa only [canonicalSolverAt, hin, ↓reduceDIte] using hh

/-- Admissibility bounds every encoded input word, even though the contract
identifies the stored graph through an existential representation. -/
theorem CanonicalInput.words_fit {w : ℕ} {T : ℕ → ℕ → ℕ} {J : Circulation}
    (hin : CanonicalInput w T J) : ∀ x ∈ J.solverWords, x < 2 ^ w := by
  obtain ⟨a, h, hargs, K, hat, _, hwords, _, _⟩ := hin.2.1
  have ha : a = 0 := by
    have hh := congrArg (fun l : List ℕ => l.getD 0 0) hargs
    simpa only [List.getD_cons_zero] using hh.symm
  subst a
  have hd := solverDimensions_of_at K (initMem J.solverWords) 0 J.solverWords.length hat
  have hj := solverDimensions_of_at J (initMem J.solverWords) 0 J.solverWords.length
    (listAt_initMem J.solverWords)
  have hm : J.m = K.m := congrArg Prod.snd (hj.symm.trans hd)
  have hlen : J.solverWords.length = K.solverWords.length := by
    rw [J.solverWords_length, K.solverWords_length, hm]
  have heq := (listAt_initMem J.solverWords).ext hat hlen
  rw [heq]
  exact hwords

/-- The output array ends inside the guest's address space. -/
theorem CanonicalInput.output_fits {w : ℕ} {T : ℕ → ℕ → ℕ} {J : Circulation}
    (hin : CanonicalInput w T J) : J.solverWords.length + J.m < 2 ^ w := by
  obtain ⟨a, h, hargs, K, hat, _, _, _, hfit, _⟩ := hin.2.1
  have ha : a = 0 := by
    have hh := congrArg (fun l : List ℕ => l.getD 0 0) hargs
    simpa only [List.getD_cons_zero] using hh.symm
  have hh : h = J.solverWords.length := by
    have he := congrArg (fun l : List ℕ => l.getD 1 0) hargs
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using he.symm
  subst a
  subst h
  have hd := solverDimensions_of_at K (initMem J.solverWords) 0 J.solverWords.length hat
  have hj := solverDimensions_of_at J (initMem J.solverWords) 0 J.solverWords.length
    (listAt_initMem J.solverWords)
  have hm : J.m = K.m := congrArg Prod.snd (hj.symm.trans hd)
  rw [hm]
  omega

/-- Multiplier five suffices for a canonical primitive input, output, and
its advertised polynomial workspace, independently of the time estimate. -/
theorem canonicalInput_wordSize (T : ℕ → ℕ → ℕ) (J : Circulation)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) :
    CanonicalInput (wordSize 5 J.solverWords) T J := by
  have hlen := J.solverWords_length
  have hm : J.m ≤ J.solverWords.length := by omega
  have hn : J.n ≤ J.solverWords.foldr max 0 := by
    change J.n ≤ max J.n _
    exact le_max_left _ _
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  have hB : 2 ≤ B := by dsimp only [B]; omega
  have hbase : J.n + J.m + 2 ≤ B := by dsimp only [B]; omega
  have hsmall : J.solverWords.length + J.m ≤ B ^ 2 := by
    have hl : J.solverWords.length + J.m ≤ 2 * B := by dsimp only [B]; omega
    have hh : 2 * B ≤ B ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right B hB
    exact hl.trans hh
  have h24 : B ^ 2 ≤ B ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hscratch : (J.n + J.m + 2) ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hbase 4
  have htwice : 2 * B ^ 4 ≤ B ^ 5 := by
    calc
      2 * B ^ 4 ≤ B * B ^ 4 := Nat.mul_le_mul_right (B ^ 4) hB
      _ = B ^ 5 := by ring
  have hp := pow_lt_two_pow_wordSize (by decide : 1 ≤ 5) J.solverWords
  change B ^ 5 < 2 ^ wordSize 5 J.solverWords at hp
  have hspace : J.solverWords.length + solverSpace J.n J.m < 2 ^ wordSize 5 J.solverWords := by
    have hb := hsmall.trans h24
    have hs : J.solverWords.length + solverSpace J.n J.m ≤ 2 * B ^ 4 := by
      dsimp only [solverSpace]
      omega
    exact lt_of_le_of_lt (hs.trans htwice) hp
  have houtput : J.solverWords.length + J.m < 2 ^ wordSize 5 J.solverWords := by
    dsimp only [solverSpace] at hspace
    omega
  have hargs : ∀ a ∈ [0, J.solverWords.length], a < 2 ^ wordSize 5 J.solverWords := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  have hd := solverDimensions_of_at J (initMem J.solverWords) 0 J.solverWords.length
    (listAt_initMem J.solverWords)
  refine ⟨hargs, ?_, zeroFrom_initMem J.solverWords, ?_⟩
  · refine ⟨0, J.solverWords.length, rfl, J, listAt_initMem J.solverWords,
      (by omega), ?_, hc, (show J.solverWords.length + J.m + solverScratch J.n J.m < _ from by simpa only [solverSpace, solverScratch, Nat.add_assoc] using hspace), hu⟩
    intro x hx
    exact lt_two_pow_wordSize_of_mem (by decide) hx
  · change J.solverWords.length +
      solverSpace (solverDimensions [0, J.solverWords.length] (initMem J.solverWords)).1
        (solverDimensions [0, J.solverWords.length] (initMem J.solverWords)).2 <
        2 ^ wordSize 5 J.solverWords
    rw [hd]
    exact hspace

/-- A single mathematical solver function whose bounded-input values are
canonical procedure outputs. Its guest width is computed from each input. -/
noncomputable def canonicalSolver
    (Q : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w, MeetsContract w Q f (solverContract w T solverScratch))
    (J : Circulation) : Fin J.m → ℤ :=
  canonicalSolverAt (wordSize 5 J.solverWords) Q f T (hproc _) J

/-- The instance-dependent solver uses the fixed canonical width computed
from its encoded circulation. -/
theorem canonicalSolver_eq (Q : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w, MeetsContract w Q f (solverContract w T solverScratch)) (J : Circulation) :
    canonicalSolver Q f T hproc J =
      canonicalSolverAt (wordSize 5 J.solverWords) Q f T (hproc _) J := by
  rfl

/-- The canonical procedure-output function has the exact solver specification
used by the scaling model. No stable-choice property is required of `Q`. -/
theorem canonicalSolver_optimal
    (Q : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w, MeetsContract w Q f (solverContract w T solverScratch)) (J : Circulation) :
    J.Optimal (fun e => (canonicalSolver Q f T hproc J e : ℝ)) :=
  canonicalSolverAt_optimal _ _ _ _ _ J

/-- The admissible input condition is satisfiable for every bounded graph
by choosing a sufficiently large guest word size. -/
theorem exists_canonical_input (T : ℕ → ℕ → ℕ) (J : Circulation)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) :
    ∃ w, CanonicalInput w T J := exists_solver_pre T solverScratch J hc hu

end MinCostFlow.Scaling.Machine
