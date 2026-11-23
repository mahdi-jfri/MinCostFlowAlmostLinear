module

public import MinCostFlow.Scaling.CanonicalSolver
public import WordRAM.LinkDefs
import WordRAM.Link
import WordRAM.Entry

/-!
# Relocating a canonical solver call into fresh host memory

Canonical calls fix the guest addresses and word size, so a deterministic
solver defines one output function even if it reads its address or other
memory. WordRAM's relocation theorem runs that same execution at a host
base address. This file transports its integral output and cost bound.
No rule requiring the solver to ignore its machine context is assumed.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Registers for a relocated canonical body, with the two relocation
parameters above all registers referenced by the guest program. -/
def canonicalHostState (Q : Program) (J : Circulation) (guestWidth h pos : ℕ)
    (mem : ℕ → ℕ) : State where
  mem := mem
  regs := fun r => if r = Q.regBound then h + 1
    else if r = Q.regBound + 1 then 2 ^ guestWidth
    else [0, J.solverWords.length].getD r 0
  pos := pos

/-- A relocated canonical solver body returns the model's fixed output
function. Its body cost is at most `(Q.regBound+6)*T(n,m)`, and it preserves
memory outside the guest region. Input copying and the call wrapper are
accounted for by the enclosing procedure. -/
theorem canonical_relocated_run
    {guestWidth hostWidth h b pos : ℕ} {Q P : Program} {f : ℕ}
    {T : ℕ → ℕ → ℕ} {ω : ℕ → Bool}
    (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T solverScratch))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : CanonicalInput guestWidth T J)
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ hostWidth) (hspace : h + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth) (mem : ℕ → ℕ)
    (hmem : ∀ a < 2 ^ guestWidth, mem (h + 1 + a) = initMem J.solverWords a) :
    ∃ body o st cost, Q.procs[f]? = some body ∧
      Runs hostWidth P ω (relocStmt Q.regBound b body)
        (canonicalHostState Q J guestWidth h pos mem) o st cost ∧
      cost ≤ (Q.regBound + 6) * T J.n J.m ∧
      J.readSolverFlow st.mem (h + 1 + J.solverWords.length) =
        canonicalSolverAt guestWidth Q f T hproc J ∧
      (∀ a, a < h + 1 ∨ h + 1 + 2 ^ guestWidth ≤ a → st.mem a = mem a) := by
  obtain ⟨body, o, stQ, costQ, hb, hr, hc, hout⟩ :=
    canonicalSolverAt_has_run guestWidth Q f T hproc J hin
  have hnrand := hdet body (List.mem_of_getElem? hb)
  have hrtape := runs_of_deterministic hdet
    (ω' := subBits hostWidth guestWidth pos ω) hnrand hr
  obtain ⟨fuel, hfuel⟩ := hrtape
  have hregs : ∀ r < Q.regBound,
      (canonicalHostState Q J guestWidth h pos mem).regs r =
        (startState [0, J.solverWords.length] (initMem J.solverWords) 0).regs r := by
    intro r hr
    simp only [canonicalHostState, startState, ite_eq_right (by omega : r ≠ Q.regBound),
      ite_eq_right (by omega : r ≠ Q.regBound + 1)]
  have hgregs : ∀ r, (startState [0, J.solverWords.length] (initMem J.solverWords) 0).regs r <
      2 ^ guestWidth := by
    intro r
    rcases r with _ | r
    · exact hin.1 0 (List.mem_cons_self)
    · rcases r with _ | r
      · exact hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
      · simp only [startState, List.getD_cons_succ, List.getD_nil]
        exact Nat.two_pow_pos _
  have hgmem : ∀ a, initMem J.solverWords a < 2 ^ guestWidth := by
    intro a
    simp only [initMem, List.getD_eq_getElem?_getD]
    cases hx : J.solverWords[a]? with
    | none => exact Nat.two_pow_pos _
    | some x => exact hin.words_fit x (List.mem_of_getElem? hx)
  have hbase : (canonicalHostState Q J guestWidth h pos mem).regs Q.regBound = h + 1 := by
    simp only [canonicalHostState, ↓reduceIte]
  have hW : (canonicalHostState Q J guestWidth h pos mem).regs (Q.regBound + 1) = 2 ^ guestWidth := by
    simp only [canonicalHostState, ite_eq_right (by omega : Q.regBound + 1 ≠ Q.regBound), ↓reduceIte]
  have hreloc := Link.runs_relocStmt hmodule hw hspace hfour fuel body
    (startState [0, J.solverWords.length] (initMem J.solverWords) 0)
    (canonicalHostState Q J guestWidth h pos mem) 0 o stQ costQ
    (Link.regBound_le_of_mem (List.mem_of_getElem? hb)) hbase hW hregs hgregs hgmem hmem
    (by simp only [startState, Nat.zero_mul])
    (by simp only [canonicalHostState, Nat.zero_mul, Nat.add_zero]) hfuel
  obtain ⟨stH, costH, _, hrun, hcost, _, _, _, _, _, _, hmemory, hframe, _, _⟩ := hreloc
  refine ⟨body, o, stH, costH, hb, hrun,
    hcost.trans (Nat.mul_le_mul_left _ hc), ?_, hframe⟩
  have hbound := hin.output_fits
  rw [hout]
  funext e
  have he := hmemory (J.solverWords.length + e.val) (by have hh := e.isLt; omega)
  change (stH.mem (h + 1 + J.solverWords.length + e.val) : ℤ) =
    (stQ.mem (J.solverWords.length + e.val) : ℤ)
  rw [Nat.add_assoc, he]

end MinCostFlow.Scaling.Machine
