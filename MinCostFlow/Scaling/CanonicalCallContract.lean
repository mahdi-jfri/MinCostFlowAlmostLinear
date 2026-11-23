module

public import MinCostFlow.Scaling.CanonicalCallArguments
import WordRAM.Link

/-!
# Calling the relocated canonical solver as a procedure

The relocation theorem describes a body execution. This file puts that
execution in the shared procedure-contract form so the input-copying
wrapper can call it with ordinary machine instructions. The output is the
fixed canonical solver function, and memory outside the guest region is
preserved. No condition on how the solver chooses among optima is added.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A prepared relocated call, before the wrapper copies its output.
The guest region already contains the canonical input followed by zeros. -/
def canonicalCallContract (guestWidth : ℕ) (Q : Program) (f : ℕ)
    (T : ℕ → ℕ → ℕ) (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T solverScratch))
    (J : Circulation) (h : ℕ) : Contract where
  pre args mem := args = canonicalCallArgs Q J guestWidth h ∧
    ∀ a < 2 ^ guestWidth, mem (h + 1 + a) = initMem J.solverWords a
  post _ mem _ mem' :=
    J.readSolverFlow mem' (h + 1 + J.solverWords.length) =
      canonicalSolverAt guestWidth Q f T hproc J ∧
    ∀ a, a < h + 1 ∨ h + 1 + 2 ^ guestWidth ≤ a → mem' a = mem a
  cost _ _ := (Q.regBound + 6) * T J.n J.m

/-- A body placed at the relocated solver index meets the ordinary call
contract, with exactly the canonical model output and the relocation cost. -/
theorem canonicalCall_meetsContract
    {guestWidth hostWidth h b : ℕ} {Q P : Program} {f : ℕ}
    {T : ℕ → ℕ → ℕ}
    (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T solverScratch))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : CanonicalInput guestWidth T J)
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ hostWidth) (hspace : h + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth) :
    MeetsContract hostWidth P (b + 1 + f)
      (canonicalCallContract guestWidth Q f T hproc J h) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hmem⟩ := hpre
  obtain ⟨body, o, st, cost, hb, hr, hc, hout, hframe⟩ :=
    canonical_relocated_run hproc hdet J hin hmodule hw hspace hfour mem hmem
  refine ⟨relocStmt Q.regBound b body, hmodule f body hb, o, st, cost, ?_,
    ⟨hout, hframe⟩, hc⟩
  rwa [startState_canonicalCallArgs]

/-- Relocating a deterministic body adds no random instruction. -/
theorem relocStmt_noRand (R b : ℕ) (body : Stmt) (h : body.NoRand) :
    (relocStmt R b body).NoRand := by
  induction body with
  | nop => trivial
  | assign => trivial
  | store => trivial
  | rand => exact False.elim h
  | seq s t ihs iht => exact ⟨ihs h.1, iht h.2⟩
  | cond e s t ihs iht => exact ⟨ihs h.1, iht h.2⟩
  | loop e body ih => exact ih h
  | call => trivial
  | ret => trivial

end MinCostFlow.Scaling.Machine
