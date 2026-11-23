module

public import MinCostFlow.Scaling.CanonicalSolveProgram
import WordRAM.Entry

/-!
# The complete canonical solver module

This module joins the input-reading entry, the dynamic word-bound scan,
and the canonical copying wrapper. Every procedure is placed at its proved
index. With a deterministic bounded-circulation solver, the resulting
module is deterministic and returns the scaling model's solver function.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Entry, guest-bound computation, and the complete canonical wrapper. -/
def canonicalSolveModule (Q : Program) (f b : ℕ) : List Stmt :=
  canonicalSolveBody (b + 1) (b + 2) :: canonicalWordBoundBody ::
    canonicalWrapperModule Q f (b + 2)

/-- The full canonical solve module supplies the entry, word-bound scan,
and wrapper installation used in the procedure proof. -/
theorem canonicalSolveModule_layout {P Q : Program} {f b : ℕ}
    (hp : P.HasAt b (canonicalSolveModule Q f b)) :
    P.procs[b]? = some (canonicalSolveBody (b + 1) (b + 2)) ∧
    P.HasAt (b + 1) canonicalWordBoundModule ∧
    P.HasAt (b + 2) (canonicalWrapperModule Q f (b + 2)) := by
  refine ⟨hp.head, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [canonicalSolveModule, canonicalWordBoundModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [canonicalSolveModule])
  · intro i hi
    have h := hp (i + 1 + 1) (by simp only [canonicalSolveModule, List.length_cons]; omega)
    have hidx : b + (i + 1 + 1) = (b + 2) + i := by omega
    rw [hidx] at h
    simpa only [canonicalSolveModule, List.getElem_cons_succ] using h

/-- Every body in the full canonical module has no random instruction
when the supplied solver is deterministic. -/
theorem canonicalSolveModule_noRand (Q : Program) (f b : ℕ)
    (hdet : Q.IsDeterministic) : ∀ body ∈ canonicalSolveModule Q f b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact canonicalSolveBody_noRand _ _
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact canonicalWordBoundBody_noRand
    · exact canonicalWrapperModule_noRand Q f (b + 2) hdet body hb

/-- The full module realizes its own installation conditions. -/
theorem canonicalSolveModule_hasAt (Q : Program) (f : ℕ) :
    (Program.mk (canonicalSolveModule Q f 0)).HasAt 0 (canonicalSolveModule Q f 0) := by
  intro i hi
  simpa only [Nat.zero_add] using List.getElem?_eq_getElem hi

/-- The installed complete module computes exactly the solver function of
the mathematical scaling model from just `[inputAddress,heap]`. -/
theorem canonicalSolveModule_meetsContract
    {w b : ℕ} {Q P : Program} {f : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w, MeetsContract w Q f (solverContract w T solverScratch))
    (hdet : Q.IsDeterministic) (J : Circulation)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hp : P.HasAt b (canonicalSolveModule Q f b)) :
    MeetsContract w P b (canonicalSolveContract w Q f T hproc J) := by
  obtain ⟨hentry, hbound, hwrap⟩ := canonicalSolveModule_layout hp
  exact canonicalSolve_meetsContract hproc hdet J hc hu hentry hbound hwrap

/-- In particular, all required bodies occur in one deterministic program. -/
theorem canonicalSolveProgram_isDeterministic (Q : Program) (f : ℕ)
    (hdet : Q.IsDeterministic) :
    (Program.mk (canonicalSolveModule Q f 0)).IsDeterministic :=
  canonicalSolveModule_noRand Q f 0 hdet

end MinCostFlow.Scaling.Machine
