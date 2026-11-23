module

public import MinCostFlow.HierPaths.DelProgSupRefresh

/-!
# Refreshing an owner's support cursor

When a terminal is lost, read its owner from the terminal table and refresh that vertex.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read the owner of the terminal in register 48 and refresh its cursor. -/
def delRefreshOwner : Stmt :=
  .seq (.assign 39 (readSec numSec 0 1 (.reg 48))) delSupRefresh

theorem delRefreshOwner_noRand : delRefreshOwner.NoRand := by
  simp [delRefreshOwner, Stmt.NoRand, delSupRefresh_noRand]

theorem delRefreshOwner_writesBelow : Stmt.WritesBelow 49 delRefreshOwner := by
  simp [delRefreshOwner, delSupRefresh, delCursorSetup, delCsrSetup,
    advanceStmt, supTestStmt, delCursorStore, Stmt.WritesBelow]

/-- Refresh the owner stored for this terminal. -/
theorem delRefreshOwner_triple {w : ℕ} {p : Program} (x : HierConcrete) {b c : ℕ}
    {mem0 R : ℕ → ℕ} (h0 : R 0 = b) (h48 : R 48 = c)
    (hc : c < x.H.A.C.numTerm) (hb : b + x.encode.length < 2 ^ w)
    (hq : x.H.A.C.owner c < x.n)
    (hN : (x.H.A.C.supportArray (x.H.A.C.owner c)).length + 1 < 2 ^ w)
    (hold : x.ms.st.supCur (x.H.A.C.owner c) ≤ (x.H.A.C.supportArray (x.H.A.C.owner c)).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    :
    let q := x.H.A.C.owner c
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delRefreshOwner (normalPost fun s => s.regs 0 = b ∧ s.regs 39 = q ∧
        ListAt s.mem b (x.refreshSup q).encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i)
      (fun _ => 165 + (advance (x.H.A.supValid (x.H.A.surv x.ms.st) q)
        (x.H.A.C.supportArray q).length (x.ms.st.supCur q) - x.ms.st.supCur q + 1) * 280) := by
  dsimp only
  let q := x.H.A.C.owner c
  let M := fun mem => ListAt mem b x.encode ∧ mem = mem0
  have hsec : x.sections.getD 1 [] = tabList x.H.A.C.numTerm x.H.A.C.owner := rfl
  have hidx : c < (x.sections.getD 1 []).length := by rw [hsec]; simpa using hc
  have hqval : (x.sections.getD 1 [])[c] = q := by
    rw [← List.getD_eq_getElem _ 0 hidx, hsec]
    simp [tabList, List.getD_eq_getElem?_getD, hc, q]
  have hread : Triple w p (fun s => s.regs = R ∧ M s.mem)
      (.assign 39 (readSec numSec 0 1 (.reg 48)))
      (normalPost fun s => s.regs = Function.update R 39 q ∧ M s.mem)
      (fun _ => 14) := by
    refine (triple_assign_exact ?_).mono_cost (fun _ _ => by decide)
    intro s hr hm
    have h := eval_readSec (w := w) (show ListAt s.mem b (layoutList x.sections) from hm.1)
      hb (r := 0) (by rw [hr, h0]) (i := 1) (by rw [x.length_sections']; decide)
      (Expr.eval_reg_of_eq (r := 48) (by rw [hr, h48])) hidx
    rwa [x.length_sections', hqval] at h
  exact (Triple.seq_normal_const hread
    (delSupRefresh_triple x (by simpa using h0) (by simp [q]) hq hb hN hold hinel)).mono_cost
    (fun _ _ => by omega)

end MinCostFlow.HierPaths

end
