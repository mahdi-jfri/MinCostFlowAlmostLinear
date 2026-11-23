module

public import MinCostFlow.HierPaths.DelProgSupRefresh

/-!
# Refreshing a vertex in a stored connector walk

The support pass reads the vertex at the current word of the connector's walk and
refreshes its support cursor.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read a vertex from word 48's index in section 10 and refresh its support cursor. -/
def delRefreshWalkVertex : Stmt :=
  .seq (.assign 39 (readSec numSec 0 10 (.reg 48))) delSupRefresh

theorem delRefreshWalkVertex_noRand : delRefreshWalkVertex.NoRand := by
  simp [delRefreshWalkVertex, Stmt.NoRand, delSupRefresh_noRand]

theorem delRefreshWalkVertex_writesBelow : Stmt.WritesBelow 48 delRefreshWalkVertex := by
  simp [delRefreshWalkVertex, delSupRefresh, delCursorSetup, delCsrSetup,
    advanceStmt, supTestStmt, delCursorStore, Stmt.WritesBelow]

/-- Refresh the support cursor of one stored walk vertex. -/
theorem delRefreshWalkVertex_triple {w : ℕ} {p : Program} (x : HierConcrete) {b k v : ℕ}
    {mem0 R : ℕ → ℕ} (h0 : R 0 = b) (h48 : R 48 = k)
    (hk : k < (x.sections.getD 10 []).length)
    (hvertex : (x.sections.getD 10 [])[k] = v) (hb : b + x.encode.length < 2 ^ w)
    (hq : v < x.n)
    (hN : (x.H.A.C.supportArray (v)).length + 1 < 2 ^ w)
    (hold : x.ms.st.supCur (v) ≤ (x.H.A.C.supportArray (v)).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delRefreshWalkVertex (normalPost fun s => s.regs 0 = b ∧ s.regs 39 = v ∧
        ListAt s.mem b (x.refreshSup v).encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i)
      (fun _ => 165 + (advance (x.H.A.supValid (x.H.A.surv x.ms.st) v)
        (x.H.A.C.supportArray v).length (x.ms.st.supCur v) - x.ms.st.supCur v + 1) * 280) := by
  let M := fun mem => ListAt mem b x.encode ∧ mem = mem0
  have hread : Triple w p (fun s => s.regs = R ∧ M s.mem)
      (.assign 39 (readSec numSec 0 10 (.reg 48)))
      (normalPost fun s => s.regs = Function.update R 39 v ∧ M s.mem)
      (fun _ => 14) := by
    refine (triple_assign_exact ?_).mono_cost (fun _ _ => by decide)
    intro s hr hm
    have h := eval_readSec (w := w) (show ListAt s.mem b (layoutList x.sections) from hm.1)
      hb (r := 0) (by rw [hr, h0]) (i := 10) (by rw [x.length_sections']; decide)
      (Expr.eval_reg_of_eq (r := 48) (by rw [hr, h48])) hk
    rwa [x.length_sections', hvertex] at h
  exact (Triple.seq_normal_const hread
    (delSupRefresh_triple x (by simpa using h0) (by simp) hq hb hN hold hinel)).mono_cost
    (fun _ _ => by omega)

end MinCostFlow.HierPaths

end
