module

public import MinCostFlow.Scaling.CanonicalWrapperProgram
import WordRAM.Link

/-!
# Assembling the canonical solver wrapper

The wrapper occupies one entry, followed by preparation, contiguous copying,
and the relocated solver's procedures. This file proves that this layout
supplies every body used in the wrapper proof and preserves determinism.
Thus the installation conditions can all hold in one concrete program.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Wrapper, preparation, copying, and relocated guest procedures in order. -/
def canonicalWrapperModule (Q : Program) (f b : ℕ) : List Stmt :=
  canonicalWrapperBody Q (b + 1) (b + 3 + f) (b + 2) ::
    canonicalPrepareModule (b + 1) ++ Q.procs.map (relocStmt Q.regBound (b + 2))

/-- The assembled module provides all installation conditions of the
canonical wrapper theorem at the stated procedure indices. -/
theorem canonicalWrapperModule_layout {P Q : Program} {f b : ℕ}
    (hp : P.HasAt b (canonicalWrapperModule Q f b)) :
    P.procs[b]? = some (canonicalWrapperBody Q (b + 1) (b + 3 + f) (b + 2)) ∧
    P.HasAt (b + 1) (canonicalPrepareModule (b + 1)) ∧
    P.HasAt (b + 2) [copyWords] ∧
    (∀ k body, Q.procs[k]? = some body →
      P.procs[(b + 2) + 1 + k]? = some (relocStmt Q.regBound (b + 2) body)) := by
  have hlen : (canonicalWrapperModule Q f b).length = 3 + Q.procs.length := by
    simp only [canonicalWrapperModule, canonicalPrepareModule, List.length_cons,
      List.length_append, List.length_map, List.length_nil]
  refine ⟨hp.head, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl
    · simpa only [canonicalWrapperModule, canonicalPrepareModule,
        List.cons_append, List.nil_append, List.getElem_cons_succ,
        List.getElem_cons_zero, Nat.add_zero] using hp 1 (by rw [hlen]; omega)
    · simpa only [canonicalWrapperModule, canonicalPrepareModule,
        List.cons_append, List.nil_append, List.getElem_cons_succ,
        List.getElem_cons_zero, Nat.add_assoc] using hp 2 (by rw [hlen]; omega)
  · intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [canonicalWrapperModule, canonicalPrepareModule,
      List.cons_append, List.nil_append, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 2 (by rw [hlen]; omega)
  · intro k body hb
    obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hb
    have h := hp (k + 1 + 1 + 1) (by rw [hlen]; omega)
    have hidx : b + (k + 1 + 1 + 1) = (b + 2) + 1 + k := by omega
    rw [hidx] at h
    simpa only [canonicalWrapperModule, canonicalPrepareModule,
      List.cons_append, List.nil_append, List.getElem_cons_succ,
      List.getElem_cons_zero, List.getElem_map, he] using h

/-- A deterministic guest gives a module with no random instructions. -/
theorem canonicalWrapperModule_noRand (Q : Program) (f b : ℕ)
    (hdet : Q.IsDeterministic) :
    ∀ body ∈ canonicalWrapperModule Q f b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact canonicalWrapperBody_noRand _ _ _ _
  · rcases List.mem_append.mp hb with hb | hb
    · exact canonicalPrepareModule_noRand _ body hb
    · obtain ⟨guest, hg, rfl⟩ := List.mem_map.mp hb
      exact relocStmt_noRand _ _ _ (hdet guest hg)

/-- The installation conditions are realized by the module itself. -/
theorem canonicalWrapperModule_hasAt (Q : Program) (f : ℕ) :
    (Program.mk (canonicalWrapperModule Q f 0)).HasAt 0 (canonicalWrapperModule Q f 0) := by
  intro i hi
  simpa only [Nat.zero_add] using List.getElem?_eq_getElem hi

/-- Installing the assembled module suffices for the wrapper's correctness
and cost contract. No separate placement assumptions remain. -/
theorem canonicalWrapperModule_meetsContract
    {guestWidth w b : ℕ} {Q P : Program} {f : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T solverScratch))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : CanonicalInput guestWidth T J)
    (hp : P.HasAt b (canonicalWrapperModule Q f b)) (hw : guestWidth ≤ w) :
    MeetsContract w P b (canonicalWrapperContract w guestWidth Q f T hproc J) := by
  obtain ⟨hentry, hprepare, hcopy, hmodule⟩ := canonicalWrapperModule_layout hp
  apply canonicalWrapper_meetsContract hproc hdet J hin ?_ hprepare hcopy hmodule hw
  simpa only [show (b + 2) + 1 + f = b + 3 + f by omega] using hentry

end MinCostFlow.Scaling.Machine
