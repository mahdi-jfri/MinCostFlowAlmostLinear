module

public import MinCostFlow.Scaling.VertexLabels
public import WordRAM.Layout
import WordRAM.Tactic

/-!
# Assigning one endpoint label on the machine

Vertex compression in Appendix C scans endpoints in order. A zero table
entry means unseen. The next encounter writes `count+1` only for an unseen
vertex and otherwise leaves its label unchanged. This in-place procedure
implements `VertexLabels.encounter`, returns the new count, and preserves
all cells other than the encountered entry. It costs at most 24 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Positive-label table stored at consecutive vertex addresses. -/
def LabelsAt {n : ℕ} (mem : ℕ → ℕ) (a : ℕ) (s : VertexLabels n) : Prop :=
  ∀ v : Fin n, mem (a + v.val) = s.table v

/-- Arguments `[tableAddress, count, vertex]`, returning the updated count. -/
def vertexEncounterBody : Stmt :=
  .assign 3 (.bin .add (.reg 0) (.reg 2)) ;;
  .cond (.bin .eq (.load (.reg 3)) (.const 0))
    (.store (.reg 3) (.bin .add (.reg 1) (.const 1)) ;;
      .ret (.bin .add (.reg 1) (.const 1)))
    (.ret (.reg 1))

/-- One endpoint encounter occupies a single procedure slot. -/
def vertexEncounterModule : List Stmt := [vertexEncounterBody]

/-- In-place encounter contract, indexed by the represented label table. -/
def vertexEncounterContract (w : ℕ) {n : ℕ} (s : VertexLabels n) (v : Fin n) : Contract where
  pre args mem := ∃ a, args = [a, s.count, v.val] ∧ LabelsAt mem a s ∧ s.Valid ∧
    a + n < 2 ^ w ∧ s.count + 1 < 2 ^ w
  post args mem out mem' := out = (s.encounter v).count ∧
    LabelsAt mem' (args.getD 0 0) (s.encounter v) ∧
    ∀ x, x ≠ args.getD 0 0 + v.val → mem' x = mem x
  cost _ _ := 24

/-- Encountering an endpoint uses no random instruction. -/
theorem vertexEncounterBody_noRand : vertexEncounterBody.NoRand := by
  simp only [vertexEncounterBody, Stmt.NoRand, and_self]

/-- The endpoint primitive implements exactly the model's encounter and
changes at most its one table cell, at cost at most 24. -/
theorem vertexEncounter_meetsContract {w b n : ℕ} {p : Program}
    (hp : p.HasAt b vertexEncounterModule) (s : VertexLabels n) (v : Fin n) :
    MeetsContract w p b (vertexEncounterContract w s v) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, rfl, hat, hvalid, hend, hcount⟩ := hpre
  have hvlt := v.isLt
  have haddr : a + v.val < 2 ^ w := by omega
  have hlabel : mem (a + v.val) = s.table v := hat v
  have hvalue : mem (a + v.val) < 2 ^ w := by
    have hh := hvalid.1 v
    omega
  have ha : a < 2 ^ w := hwords a (by simp)
  have hvword : v.val < 2 ^ w := hwords v.val (by simp)
  have hcword : s.count < 2 ^ w := hwords s.count (by simp)
  have hw : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold vertexEncounterBody
  wram_step
  wram_step
  · have hz : mem (a + v.val) = 0 := by simpa [startState] using hcond
    have hzero : s.table v = 0 := hlabel.symm.trans hz
    wram_step
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change s.count + 1 = (s.encounter v).count ∧
        LabelsAt (Function.update mem (a + v.val) (s.count + 1)) a (s.encounter v) ∧
        ∀ x, x ≠ a + v.val → (Function.update mem (a + v.val) (s.count + 1)) x = mem x
      simp only [VertexLabels.encounter, hzero, ↓reduceIte]
      refine ⟨trivial, ?_, fun x hx => Function.update_of_ne hx _ _⟩
      intro u
      change Function.update mem (a + v.val) (s.count + 1) (a + u.val) =
        Function.update s.table v (s.count + 1) u
      by_cases hu : u = v
      · subst u
        simp only [Function.update_self]
      · have hnat : a + u.val ≠ a + v.val := by
          intro he
          apply hu
          exact Fin.ext (Nat.add_left_cancel he)
        rw [Function.update_of_ne hnat, Function.update_of_ne hu]
        exact hat u
    · simp only [vertexEncounterContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
      omega
  · have hz : mem (a + v.val) ≠ 0 := by simpa [startState] using hcond
    have hnon : s.table v ≠ 0 := by rw [← hlabel]; exact hz
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change s.count = (s.encounter v).count ∧ LabelsAt mem a (s.encounter v) ∧
        ∀ x, x ≠ a + v.val → mem x = mem x
      simp only [VertexLabels.encounter, hnon, ↓reduceIte]
      exact ⟨trivial, hat, fun _ _ => trivial⟩
    · simp only [vertexEncounterContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
      omega

/-- The encounter precondition holds on a fresh zero table, with the model's
valid empty labeling, whenever its addresses fit. -/
theorem vertexEncounter_pre_empty {w n : ℕ} (v : Fin n)
    (hn : n < 2 ^ w) (hw : 1 < 2 ^ w) :
    (vertexEncounterContract w (VertexLabels.empty n) v).pre [0, 0, v.val] (fun _ => 0) := by
  refine ⟨0, rfl, ?_, VertexLabels.empty_valid n, ?_, hw⟩
  · intro _; rfl
  · simpa only [Nat.zero_add] using hn

end MinCostFlow.Scaling.Machine
