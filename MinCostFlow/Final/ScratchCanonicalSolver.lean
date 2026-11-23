module

public import MinCostFlow.Scaling.SolverContract
import MinCostFlow.Scaling.ExactSolver
import MinCostFlow.Scaling.DeterministicExecution
import WordRAM.Exec
import WordRAM.Memory
import WordRAM.Entry

/-!
# Canonical solver outputs with polynomial scratch

The scaling reduction on page 15 uses a fixed mathematical choice of
an optimum. For machine calls, that choice comes from running the
deterministic solver on a fresh copy at the chosen guest width.
-/

public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The arguments and memory of a canonical solver call fit its machine
contract. This is an input-memory condition, not an additional solver guarantee. -/
@[expose] def ScratchCanonicalInput (w : ℕ) (T S : ℕ → ℕ → ℕ) (J : Circulation) : Prop :=
  (∀ a ∈ [0, J.solverWords.length], a < 2 ^ w) ∧
    (solverContract w T S).pre [0, J.solverWords.length] (initMem J.solverWords)

private theorem canonical_output_exists
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T S))
    (J : Circulation) (hin : ScratchCanonicalInput w T S J) :
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
noncomputable def scratchCanonicalSolverAt
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T S))
    (J : Circulation) : Fin J.m → ℤ := by
  classical
  exact if hin : ScratchCanonicalInput w T S J then
    Classical.choose (canonical_output_exists w p f T S hproc J hin)
  else J.exactSolver

/-- The extracted function meets the model's mathematical specification on
all graphs. The finite extension is only a proof device outside admissible calls. -/
theorem scratchCanonicalSolverAt_optimal
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T S)) (J : Circulation) :
    J.Optimal (fun e => (scratchCanonicalSolverAt w p f T S hproc J e : ℝ)) := by
  classical
  unfold scratchCanonicalSolverAt
  split
  · exact (Classical.choose_spec (canonical_output_exists w p f T S hproc J ‹_›)).1
  · exact J.exactSolver_optimal

/-- Every canonical call in a deterministic program returns the same
mathematical flow, even when supplied with a different random tape. -/
theorem scratchCanonicalSolverAt_eq_of_run
    {w : ℕ} {p : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ}
    (hproc : MeetsContract w p f (solverContract w T S)) (hp : p.IsDeterministic)
    (J : Circulation) (hin : ScratchCanonicalInput w T S J)
    {body : Stmt} {o : Outcome} {st : State} {cost : ℕ} {ω : ℕ → Bool}
    (hbody : p.procs[f]? = some body)
    (hrun : Runs w p ω body
      (startState [0, J.solverWords.length] (initMem J.solverWords) 0) o st cost) :
    J.readSolverFlow st.mem J.solverWords.length = scratchCanonicalSolverAt w p f T S hproc J := by
  classical
  have hspec := Classical.choose_spec (canonical_output_exists w p f T S hproc J hin)
  obtain ⟨body', o', st', cost', hb', hr', _, heq⟩ := hspec.2
  have hb : body' = body := Option.some.inj (hb'.symm.trans hbody)
  subst body'
  have hrfalse := runs_of_deterministic hp (ω' := fun _ => false)
    (hp body (List.mem_of_getElem? hbody)) hrun
  have hstates := (hrfalse.det hr').2.1
  unfold scratchCanonicalSolverAt
  rw [dite_eq_left hin, heq, hstates]

/-- A selected canonical execution exists at the chosen guest word size. -/
theorem scratchCanonicalSolverAt_has_run
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (solverContract w T S))
    (J : Circulation) (hin : ScratchCanonicalInput w T S J) :
    ∃ body o st cost, p.procs[f]? = some body ∧
      Runs w p (fun _ => false) body
        (startState [0, J.solverWords.length] (initMem J.solverWords) 0) o st cost ∧
      cost ≤ T J.n J.m ∧
      scratchCanonicalSolverAt w p f T S hproc J = J.readSolverFlow st.mem J.solverWords.length := by
  classical
  have hh := (Classical.choose_spec (canonical_output_exists w p f T S hproc J hin)).2
  simpa only [scratchCanonicalSolverAt, hin, ↓reduceDIte] using hh

/-- The canonical input at the compressed solver interface of Appendix C. -/
@[expose] def CompressedCanonicalInput (w : ℕ) (T S : ℕ → ℕ → ℕ) (J : Circulation) : Prop :=
  (∀ a ∈ [0, J.solverWords.length], a < 2 ^ w) ∧
    (compressedSolverContract w T S).pre [0, J.solverWords.length] (initMem J.solverWords)

private theorem compressed_canonical_output_exists
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (compressedSolverContract w T S))
    (J : Circulation) (hin : CompressedCanonicalInput w T S J) :
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
noncomputable def compressedCanonicalSolverAt
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (compressedSolverContract w T S))
    (J : Circulation) : Fin J.m → ℤ := by
  classical
  exact if hin : CompressedCanonicalInput w T S J then
    Classical.choose (compressed_canonical_output_exists w p f T S hproc J hin)
  else J.exactSolver

/-- The extracted function meets the model's mathematical specification on
all graphs. The finite extension is only a proof device outside admissible calls. -/
theorem compressedCanonicalSolverAt_optimal
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (compressedSolverContract w T S)) (J : Circulation) :
    J.Optimal (fun e => (compressedCanonicalSolverAt w p f T S hproc J e : ℝ)) := by
  classical
  unfold compressedCanonicalSolverAt
  split
  · exact (Classical.choose_spec (compressed_canonical_output_exists w p f T S hproc J ‹_›)).1
  · exact J.exactSolver_optimal

/-- Every canonical call in a deterministic program returns the same
mathematical flow, even when supplied with a different random tape. -/
theorem compressedCanonicalSolverAt_eq_of_run
    {w : ℕ} {p : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ}
    (hproc : MeetsContract w p f (compressedSolverContract w T S)) (hp : p.IsDeterministic)
    (J : Circulation) (hin : CompressedCanonicalInput w T S J)
    {body : Stmt} {o : Outcome} {st : State} {cost : ℕ} {ω : ℕ → Bool}
    (hbody : p.procs[f]? = some body)
    (hrun : Runs w p ω body
      (startState [0, J.solverWords.length] (initMem J.solverWords) 0) o st cost) :
    J.readSolverFlow st.mem J.solverWords.length = compressedCanonicalSolverAt w p f T S hproc J := by
  classical
  have hspec := Classical.choose_spec (compressed_canonical_output_exists w p f T S hproc J hin)
  obtain ⟨body', o', st', cost', hb', hr', _, heq⟩ := hspec.2
  have hb : body' = body := Option.some.inj (hb'.symm.trans hbody)
  subst body'
  have hrfalse := runs_of_deterministic hp (ω' := fun _ => false)
    (hp body (List.mem_of_getElem? hbody)) hrun
  have hstates := (hrfalse.det hr').2.1
  unfold compressedCanonicalSolverAt
  rw [dite_eq_left hin, heq, hstates]

/-- A selected canonical execution exists at the chosen guest word size. -/
theorem compressedCanonicalSolverAt_has_run
    (w : ℕ) (p : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ)
    (hproc : MeetsContract w p f (compressedSolverContract w T S))
    (J : Circulation) (hin : CompressedCanonicalInput w T S J) :
    ∃ body o st cost, p.procs[f]? = some body ∧
      Runs w p (fun _ => false) body
        (startState [0, J.solverWords.length] (initMem J.solverWords) 0) o st cost ∧
      cost ≤ T J.n J.m ∧
      compressedCanonicalSolverAt w p f T S hproc J = J.readSolverFlow st.mem J.solverWords.length := by
  classical
  have hh := (Classical.choose_spec (compressed_canonical_output_exists w p f T S hproc J hin)).2
  simpa only [compressedCanonicalSolverAt, hin, ↓reduceDIte] using hh

/-- Admissibility bounds every encoded input word, even though the contract
identifies the stored graph through an existential representation. -/
theorem ScratchCanonicalInput.words_fit {w : ℕ} {T S : ℕ → ℕ → ℕ} {J : Circulation}
    (hin : ScratchCanonicalInput w T S J) : ∀ x ∈ J.solverWords, x < 2 ^ w := by
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
theorem ScratchCanonicalInput.output_fits {w : ℕ} {T S : ℕ → ℕ → ℕ} {J : Circulation}
    (hin : ScratchCanonicalInput w T S J) : J.solverWords.length + J.m < 2 ^ w := by
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

/-- A compressed canonical input also fits the underlying unrestricted layout. -/
theorem CompressedCanonicalInput.toScratch {w : ℕ} {T S : ℕ → ℕ → ℕ} {J : Circulation}
    (h : CompressedCanonicalInput w T S J) : ScratchCanonicalInput w T S J :=
  ⟨h.1,h.2.1⟩

end MinCostFlow.Final
