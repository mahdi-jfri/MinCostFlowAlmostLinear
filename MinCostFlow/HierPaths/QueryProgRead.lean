module

public import MinCostFlow.HierPaths.QueryProgMain

/-!
# Reading the hierarchy block in GetPath

The section offsets give the addresses of the query tables. A support entry either gives
the terminal directly or names a connector whose first endpoint is the terminal.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The base of a section evaluates using the checked bounds of the block. -/
theorem eval_querySection {w : ℕ} {st : State} {X : HierConcrete} {b i : ℕ}
    (h : ListAt st.mem b X.encode) (hr : st.regs 0 = b) (hi : i < 24)
    (hw : b + X.encode.length < 2 ^ w) :
    (secExpr i).eval w st = some (b + 25 + st.mem (b + i)) := by
  have hEnd := (block_sec h hi).2
  have hbase : b + 25 + st.mem (b + i) < 2 ^ w := by omega
  have h25 : 25 < 2 ^ w := by omega
  have hiw : i < 2 ^ w := by omega
  have hbi : b + i < 2 ^ w := by omega
  have hb25 : b + 25 < 2 ^ w := by omega
  unfold secExpr
  exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const h25) hb25)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const hiw) hbi) rfl)
    hbase

/-- A header field can be read through its section and offset. -/
theorem eval_queryHeader {w : ℕ} {st : State} {X : HierConcrete} {b i : ℕ}
    (h : ListAt st.mem b X.encode) (hr : st.regs 0 = b) (hi : i < X.header.length)
    (hw : b + X.encode.length < 2 ^ w) :
    (queryHeaderExpr i).eval w st = some (X.header[i]) := by
  obtain ⟨hH, hEnd⟩ := block_sec h (i := 0) (by decide)
  change ListAt st.mem _ X.header at hH
  change _ + X.header.length ≤ _ at hEnd
  have hiw : i < 2 ^ w := by omega
  have hAddr : b + 25 + st.mem (b + 0) + i < 2 ^ w := by omega
  exact Expr.eval_load_of_eq (Expr.eval_add (eval_querySection h hr (by decide) hw)
    (Expr.eval_const hiw) hAddr) (hH i hi)

/-- The branch that resolves the right support's terminal preserves memory and registers
other than its result register. -/
theorem queryRightTerm_triple {w : ℕ} {p : Program} {X : HierConcrete} {b v : ℕ}
    {mem : ℕ → ℕ} {regs : ℕ → ℕ}
    (h : ListAt mem b X.encode) (hw : b + X.encode.length < 2 ^ w)
    (hreg : regs 0 = b)
    (hTag : regs 13 = X.entryWord v 0) (hId : regs 14 = X.entryWord v 1)
    (hEntry : X.H.entryAt X.ms.st v ∈ X.H.A.C.supportArray v) :
    Triple w p (fun st => st.mem = mem ∧ st.regs = regs) queryRightTerm
      (normalPost fun st => st.mem = mem ∧
        st.regs 14 = X.H.A.C.entryTerm (X.H.entryAt X.ms.st v) ∧
        ∀ r ≠ 14, st.regs r = regs r) (fun _ => 25) := by
  intro st ω hs
  obtain ⟨hm, hregs⟩ := hs
  have hb : st.regs 0 = b := hregs ▸ hreg
  have hAt : ListAt st.mem b X.encode := hm ▸ h
  have htag : (.reg 13 : Expr).eval w st = some (X.entryWord v 0) :=
    Expr.eval_reg_of_eq (hregs ▸ hTag)
  have hid : (.reg 14 : Expr).eval w st = some (X.entryWord v 1) :=
    Expr.eval_reg_of_eq (hregs ▸ hId)
  cases he : X.H.entryAt X.ms.st v with
  | term t =>
    have ht : X.entryWord v 0 = 0 := by simp [HierConcrete.entryWord, he, entryWords]
    have hI : X.entryWord v 1 = t := by simp [HierConcrete.entryWord, he, entryWords]
    unfold queryRightTerm
    refine ⟨.normal, st, _, runs_cond_iff.mpr ⟨0, 1, ht ▸ htag, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, ?_, by change 3 ≤ 25; decide⟩
    exact ⟨hm, by rw [hregs, hId, hI, ConnectorSystem.entryTerm], fun r _ => congrFun hregs r⟩
  | onWalk c k =>
    have ht : X.entryWord v 0 = 1 := by simp [HierConcrete.entryWord, he, entryWords]
    have hI : X.entryWord v 1 = c := by simp [HierConcrete.entryWord, he, entryWords]
    have hc : c < X.H.A.C.numConn := by
      have hm' : SupportEntry.onWalk c k ∈ X.H.A.C.supportArray v := he ▸ hEntry
      rcases X.H.A.C.mem_supportArray.mp hm' with ⟨t, _, _, hEq⟩ | ⟨c', hc, k', _, hEq⟩
      · cases hEq
      · cases hEq
        exact hc
    obtain ⟨hEnd, hEndEnd⟩ := block_sec hAt (i := 2) (by decide)
    change ListAt st.mem _ (tabList X.H.A.C.numConn X.H.A.C.endA) at hEnd
    change _ + (tabList X.H.A.C.numConn X.H.A.C.endA).length ≤ _ at hEndEnd
    rw [length_tabList] at hEndEnd
    have haddr : b + 25 + st.mem (b + 2) + c < 2 ^ w := by omega
    have hEval := Expr.eval_load_of_eq
      (Expr.eval_add (eval_querySection hAt hb (i := 2) (by decide) hw)
        (hI ▸ hid) haddr) (listAt_tabList hEnd hc)
    unfold queryRightTerm
    let st' : State := { st with regs := Function.update st.regs 14 (X.H.A.C.endA c) }
    refine ⟨.normal, st', _, runs_cond_iff.mpr ⟨1, ((.bin .add (secExpr 2) (.reg 14) : Expr).load).size + 1,
      ht ▸ htag, ?_, rfl⟩, ?_, by change 14 ≤ 25; decide⟩
    · simp only [one_ne_zero, ite_false]
      exact runs_assign_iff.mpr ⟨_, hEval, rfl, rfl, rfl⟩
    · exact ⟨hm, by simp [st', ConnectorSystem.entryTerm],
        fun r hr => by simp [st', Function.update_of_ne hr, hregs]⟩

end MinCostFlow.HierPaths
