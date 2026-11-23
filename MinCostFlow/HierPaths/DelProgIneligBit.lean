module

public import MinCostFlow.HierPaths.DelProgInelig

/-!
# Setting a connector's ineligible bit

For a connector read from an incident list, test its bit and set it if it is still clear.
The test register tells the caller whether to add the connector to the work list.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The concrete state after marking one connector ineligible. -/
def HierConcrete.markInelig (x : HierConcrete) (c : ℕ) : HierConcrete :=
  x.withSt { x.ms.st with inelig := insert c x.ms.st.inelig }

theorem HierConcrete.length_encode_markInelig (x : HierConcrete) (c : ℕ) :
    (x.markInelig c).encode.length = x.encode.length := by
  show (layoutList (x.markInelig c).sections).length = (layoutList x.sections).length
  rw [markInelig, x.sections_setInelig]
  exact length_layoutList_set _ (List.length_set ..)

theorem HierConcrete.markInelig_of_mem (x : HierConcrete) {c : ℕ} (hc : c ∈ x.ms.st.inelig) :
    x.markInelig c = x := by
  simp [markInelig, Finset.insert_eq_of_mem hc, withSt]

/-- Read and set the bit of the connector in register `31`. Register `32` gets the old bit. -/
def delIneligBit : Stmt :=
  .seq (.assign 32 (readSec numSec 0 15 (.reg 31)))
    (.cond (.reg 32) .nop (.store (secAddr numSec 0 15 (.reg 31)) (.const 1)))

theorem delIneligBit_noRand : delIneligBit.NoRand := by
  simp [delIneligBit, Stmt.NoRand]

/-- Mark one connector in constant time, preserving all cells outside the block. -/
theorem delIneligBit_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b c : ℕ} {R mem0 : ℕ → ℕ} (hR0 : R 0 = b) (hRc : R 31 = c)
    (hc : c < x.H.A.C.numConn) (hb : b + x.encode.length < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delIneligBit (normalPost fun s =>
        s.regs = Function.update R 32 (if c ∈ x.ms.st.inelig then 1 else 0) ∧
        ListAt s.mem b (x.markInelig c).encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i)
      (fun _ => 45) := by
  let old := if c ∈ x.ms.st.inelig then 1 else 0
  let R' := Function.update R 32 old
  let M := fun mem => ListAt mem b x.encode ∧ mem = mem0
  let Q := fun s : State => s.regs = R' ∧ ListAt s.mem b (x.markInelig c).encode ∧
    ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i
  have hs15 : x.sections.getD 15 [] =
      bitsList x.H.A.C.numConn (fun i => decide (i ∈ x.ms.st.inelig)) := by
    simp [HierConcrete.sections]
  have hk : c < (x.sections.getD 15 []).length := by rw [hs15]; simpa using hc
  have h1 : Triple w p (fun s => s.regs = R ∧ M s.mem)
      (.assign 32 (readSec numSec 0 15 (.reg 31)))
      (normalPost fun s => s.regs = R' ∧ M s.mem)
      (fun _ => (readSec numSec 0 15 (.reg 31)).size + 1) := by
    refine triple_assign_exact fun s hr hm => ?_
    have hread := eval_readSec' (w := w)
      (show ListAt s.mem b (layoutList x.sections) from hm.1) hb
      (by rw [hr, hR0]) (i := 15) (by rw [x.length_sections']; norm_num)
      (Expr.eval_reg_of_eq (v := c) (by rw [hr, hRc])) hk
    rw [x.length_sections', hs15, List.getD_eq_getElem _ _ (by simpa using hc)] at hread
    simpa [bitsList, old] using hread
  let P := fun s : State => s.regs = R' ∧ M s.mem
  have old_reg : ∀ s, P s → s.regs 32 = old := fun s hs => by simp [hs.1, R']
  have hone : 1 < 2 ^ w := by have := x.le_length_encode; omega
  have h2 : Triple w p P
      (.cond (.reg 32) .nop (.store (secAddr numSec 0 15 (.reg 31)) (.const 1)))
      (normalPost Q) (fun _ => 25) := by
    refine (Triple.cond (val := fun s => s.regs 32) (fun _ _ => Expr.eval_reg_of_eq rfl)
      (T_t := fun _ => 1) (T_f := fun _ => (secAddr numSec 0 15 (.reg 31)).size + 2)
      (Triple.nop ?_) ?_).mono_cost ?_
    · intro s hs
      have hm : c ∈ x.ms.st.inelig := by
        by_contra hn
        exact hs.2 (by simp [old_reg s hs.1, old, hn])
      exact ⟨hs.1.1, by rw [x.markInelig_of_mem hm]; exact hs.1.2.1,
        fun i _ => congrFun hs.1.2.2 i⟩
    · have H := triple_writeSec' (w := w) (p := p) (P := fun s => P s ∧ s.regs 32 = 0)
        (bs := x.sections) (r := 0) (i := 15) (by rw [x.length_sections']; norm_num)
        (ke := .reg 31) (ve := .const 1) (k := fun _ => c) (v := fun _ => 1)
        (fun s hs => ⟨hs.1.2.1, by rw [hs.1.1]; simpa [R'] using hR0,
          Expr.eval_reg_of_eq (by rw [hs.1.1]; simpa [R'] using hRc), hk,
          Expr.eval_const hone⟩) hb
      rw [x.length_sections'] at H
      refine H.strengthen_post fun o s hs => ?_
      cases o <;> try contradiction
      obtain ⟨s0, hs0, hr, _, hm, hfr⟩ := hs
      refine ⟨hr.trans hs0.1.1, ?_, fun i hi => (hfr i hi).trans (congrFun hs0.1.2.2 i)⟩
      show ListAt s.mem b (layoutList (x.markInelig c).sections)
      rw [HierConcrete.markInelig, x.sections_setInelig]
      exact hm
    · intro s _
      split <;> simp [secAddr, Expr.size]
  exact (Triple.seq_normal_const h1 h2).mono_cost fun _ _ => by
    decide

end MinCostFlow.HierPaths

end
