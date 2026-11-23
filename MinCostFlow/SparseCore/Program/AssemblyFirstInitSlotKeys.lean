module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlots
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The slots of the active pairs at the init: the keys (`AssemblyFirstInitSlotKeys`)

Loop 4 of `slotListBody` walks the edges of `G`. An edge `e` gets a key when it is not marked as
a forest edge and the flag of the component `c` of its tail is set. The key is `c · B` plus the
bucket word of `e`. The loop writes the keys in a row at `keysH`, and the pairs `(e, key)` in a row
at `asgH` (`slotKey_loop`).

The loop is stated with three functions given from outside: `cOf e`, the component of the tail of
`e`, `sel e`, whether `e` gets a key, and `keyOf e`, its key. The main run lemma
(`AssemblyFirstInitSlotRun.lean`) ties them to the model.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-- One more element of a list, filtered. -/
theorem take_succ_filter {l : List ℕ} {i : ℕ} (hi : i < l.length) (f : ℕ → Bool) :
    (l.take (i + 1)).filter f = (l.take i).filter f ++ if f l[i] then [l[i]] else [] := by
  rw [List.take_add_one, List.filter_append, List.getElem?_eq_getElem hi, Option.toList_some]
  cases h : f l[i] <;> simp [h]

/-- The edges with a key among the first `i` edges of `eL`. -/
def slotSelUpTo (eL : List ℕ) (sel : ℕ → Bool) (i : ℕ) : List ℕ := (eL.take i).filter sel

/-- The facts that loop 4 needs about one edge `e` of `eL`: the addresses it reads lie below
`keysH`, the word `cmpH + tail e` holds `cOf e`, the flag is `0` or `1`, `sel e` says that `e` is
not marked and its flag is set, and then `keyOf e` is the key and fits in a word. -/
def SlotKeyEdge (w : ℕ) (mem : ℕ → ℕ) (tsB iteB cmpH bktH ctH markH keysH B : ℕ)
    (cOf keyOf : ℕ → ℕ) (sel : ℕ → Bool) (e : ℕ) : Prop :=
  tsB + e < keysH ∧ iteB + mem (tsB + e) < keysH ∧ cmpH + mem (iteB + mem (tsB + e)) < keysH ∧
    mem (cmpH + mem (iteB + mem (tsB + e))) = cOf e ∧ ctH + 3 * cOf e < keysH ∧
    markH + e < keysH ∧ bktH + e < keysH ∧ mem (ctH + 3 * cOf e) ≤ 1 ∧
    (sel e = true ↔ mem (markH + e) = 0 ∧ mem (ctH + 3 * cOf e) ≠ 0) ∧
    (sel e = true → cOf e * B + mem (bktH + e) = keyOf e ∧ keyOf e < 2 ^ w)

/-- **Loop 4** writes the keys of the selected edges `S = eL.filter sel` at `keysH`, in order, and
the pairs `(e, key)` at `asgH`; register `29` ends at `|S|`. Only these cells change, and the
registers `25` to `29`. -/
theorem slotKey_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {eL : List ℕ}
    {eLB tsB iteB cmpH bktH ctH markH keysH asgH B : ℕ} (cOf keyOf : ℕ → ℕ) (sel : ℕ → Bool)
    (R : ℕ → ℕ) (heLA : ListAt mem eLB eL) (heL : eLB + eL.length ≤ keysH)
    (hE : ∀ e ∈ eL, SlotKeyEdge w mem tsB iteB cmpH bktH ctH markH keysH B cOf keyOf sel e)
    (hlay : keysH + eL.length ≤ asgH) (hw : asgH + 2 * eL.length + 2 < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w)
    (hR2 : R 2 = cmpH) (hR3 : R 3 = bktH) (hR6 : R 6 = B) (hR7 : R 7 = ctH)
    (hR11 : R 11 = eL.length) (hR12 : R 12 = eLB) (hR13 : R 13 = tsB) (hR14 : R 14 = iteB)
    (hR17 : R 17 = markH) (hR18 : R 18 = keysH) (hR24 : R 24 = asgH) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 29 = 0 ∧ ∀ r, r < 25 ∨ 29 < r → st.regs r = R r)
      (forRange 25 (.const 0) (.reg 11) slotKeyStep)
      (normalPost fun st => (∀ r, r < 25 ∨ 29 < r → st.regs r = R r) ∧
        st.regs 29 = (eL.filter sel).length ∧
        (∀ a, (a < keysH ∨ keysH + eL.length ≤ a) → (a < asgH ∨ asgH + 2 * eL.length ≤ a) →
          st.mem a = mem a) ∧
        ListAt st.mem keysH ((eL.filter sel).map keyOf) ∧
        ∀ t (ht : t < (eL.filter sel).length), st.mem (asgH + 2 * t) = (eL.filter sel)[t] ∧
          st.mem (asgH + 2 * t + 1) = keyOf (eL.filter sel)[t])
      (fun _ => eL.length * 110 + 10) := by
  set m := eL.length with hm
  have hw1 : 1 < 2 ^ w := by omega
  let S := slotSelUpTo eL sel
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r < 25 ∨ 29 < r → st.regs r = R r) ∧ st.regs 25 = i ∧ st.regs 29 = (S i).length ∧
    (∀ a, (a < keysH ∨ keysH + m ≤ a) → (a < asgH ∨ asgH + 2 * m ≤ a) → st.mem a = mem a) ∧
    ListAt st.mem keysH ((S i).map keyOf) ∧
    ∀ t (ht : t < (S i).length), st.mem (asgH + 2 * t) = (S i)[t] ∧
      st.mem (asgH + 2 * t + 1) = keyOf (S i)[t]
  have hSle : ∀ i, (S i).length ≤ i := fun i => by
    refine (List.length_filter_le _ _).trans ?_
    simp only [List.length_take]; omega
  have hstep : ∀ i, 0 ≤ i → i < m →
      Triple w p (Inv i) slotKeyStep
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 25 (i + 1) } ∧
            st₁.regs 25 = i)
        (fun _ => 100) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r25, r29, hfr, hkeys, hasg⟩ := hI
    have r2 : st.regs 2 = cmpH := (hR 2 (by omega)).trans hR2
    have r3 : st.regs 3 = bktH := (hR 3 (by omega)).trans hR3
    have r6 : st.regs 6 = B := (hR 6 (by omega)).trans hR6
    have r7 : st.regs 7 = ctH := (hR 7 (by omega)).trans hR7
    have r12 : st.regs 12 = eLB := (hR 12 (by omega)).trans hR12
    have r13 : st.regs 13 = tsB := (hR 13 (by omega)).trans hR13
    have r14 : st.regs 14 = iteB := (hR 14 (by omega)).trans hR14
    have r17 : st.regs 17 = markH := (hR 17 (by omega)).trans hR17
    have r18 : st.regs 18 = keysH := (hR 18 (by omega)).trans hR18
    have r24 : st.regs 24 = asgH := (hR 24 (by omega)).trans hR24
    have hiL : i < eL.length := hi
    set e := eL[i] with he_def
    have heM : e ∈ eL := List.getElem_mem hiL
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hsel, hkey⟩ := hE e heM
    have hlow : ∀ a, a < keysH → st.mem a = mem a := fun a ha =>
      hfr a (Or.inl ha) (Or.inl (by omega))
    set n := (S i).length with hn_def
    have hni : n ≤ i := hSle i
    have m1 : st.mem (eLB + i) = e := by rw [hlow _ (by omega)]; exact heLA i hiL
    have m2 : st.mem (tsB + e) = mem (tsB + e) := hlow _ h1
    have m3 : st.mem (iteB + mem (tsB + e)) = mem (iteB + mem (tsB + e)) := hlow _ h2
    have m4 : st.mem (cmpH + mem (iteB + mem (tsB + e))) = cOf e := by rw [hlow _ h3]; exact h4
    have m5 : st.mem (markH + e) = mem (markH + e) := hlow _ h6
    have m6 : st.mem (ctH + 3 * cOf e) = mem (ctH + 3 * cOf e) := hlow _ h5
    have m7 : st.mem (bktH + e) = mem (bktH + e) := hlow _ h7
    have hSsucc : S (i + 1) = S i ++ if sel e then [e] else [] := take_succ_filter hiL sel
    have hprod : (if mem (markH + e) = 0 then 1 else 0) * mem (ctH + 3 * cOf e) < 2 ^ w := by
      split_ifs <;> omega
    refine runs_start_le ?_
    unfold slotKeyStep
    refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq (by eval_expr) m1) ?_
    refine runs_seq_assign_le (v := cOf e)
      (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
        (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
          (Expr.eval_load_of_eq (by eval_expr) m2) (by omega)) m3) (by omega)) m4) ?_
    refine WordRAM.runs_cond_le
      (v := (if mem (markH + e) = 0 then 1 else 0) * mem (ctH + 3 * cOf e))
      (Expr.eval_mul (Expr.eval_eq_op (Expr.eval_load_of_eq (by eval_expr) m5)
        (Expr.eval_const (by omega)) hw1)
        (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr) (Expr.eval_mul
          (Expr.eval_const (by omega)) (by eval_expr) (by omega)) (by omega)) m6) hprod)
      (fun hv => ?_) (fun hv => ?_)
    · -- `e` gets a key
      have hs : sel e = true := hsel.mpr ⟨by by_contra h; simp [h] at hv, fun h => by
        simp [h] at hv⟩
      obtain ⟨hk1, hk2⟩ := hkey hs
      have hcB : cOf e * B < 2 ^ w := by omega
      have hS' : S (i + 1) = S i ++ [e] := by rw [hSsucc, ite_eq_left hs]
      refine runs_seq_assign_le (v := keyOf e) (Expr.eval_eq_of_eq (Expr.eval_add
        (Expr.eval_mul (by eval_expr) (by eval_expr) hcB) (Expr.eval_load_of_eq
          (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) m7) (by omega)) hk1) ?_
      refine runs_seq_store_le (x := keysH + n) (v := keyOf e)
        (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) (by eval_expr) ?_
      refine runs_seq_store_le (x := asgH + 2 * n) (v := e)
        (Expr.eval_add (by eval_expr) (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr)
          (by omega)) (by omega)) (by eval_expr) ?_
      refine runs_seq_store_le (x := asgH + 1 + 2 * n) (v := keyOf e)
        (Expr.eval_add (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr) (by omega)) (by omega))
        (by eval_expr) ?_
      refine runs_assign_le (v := n + 1)
        (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
      · refine ⟨⟨fun r hr => ?_, by simp, ?_, fun a ha ha' => ?_, ?_, ?_⟩,
          by simp [r25]⟩
        · simp [show r ≠ 25 by omega, show r ≠ 26 by omega, show r ≠ 27 by omega,
            show r ≠ 28 by omega, show r ≠ 29 by omega, hR r hr]
        · simp [hS', hn_def]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hfr a ha ha'
        · dsimp only
          rw [hS', List.map_append, List.map_singleton]
          have hsn := hkeys.snoc (keyOf e)
          rw [List.length_map] at hsn
          refine (hsn.update_outside (Or.inr ?_)).update_outside (Or.inr ?_)
          · simp only [List.length_append, List.length_map, List.length_singleton]; omega
          · simp only [List.length_append, List.length_map, List.length_singleton]; omega
        · dsimp only
          rw [hS']
          intro t ht
          simp only [List.length_append, List.length_singleton] at ht
          by_cases htn : t < n
          · have a1 : asgH + 2 * t ≠ asgH + 1 + 2 * n := by omega
            have a2 : asgH + 2 * t ≠ asgH + 2 * n := by omega
            have a3 : asgH + 2 * t ≠ keysH + n := by omega
            have b1 : asgH + 2 * t + 1 ≠ asgH + 1 + 2 * n := by omega
            have b2 : asgH + 2 * t + 1 ≠ asgH + 2 * n := by omega
            have b3 : asgH + 2 * t + 1 ≠ keysH + n := by omega
            rw [Function.update_of_ne a1, Function.update_of_ne a2, Function.update_of_ne a3,
              Function.update_of_ne b1, Function.update_of_ne b2, Function.update_of_ne b3,
              List.getElem_append_left htn]
            exact hasg t htn
          · have htn' : t = n := by omega
            subst htn'
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_singleton]
            refine ⟨?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_self]
            · rw [show asgH + 2 * (S i).length + 1 = asgH + 1 + 2 * (S i).length by omega,
                Function.update_self]
      · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
        omega
    · -- `e` gets no key
      have hs : sel e = false := by
        by_contra hs
        simp only [Bool.not_eq_false] at hs
        obtain ⟨hm0, hf⟩ := hsel.mp hs
        simp [hm0] at hv
        exact hf hv
      have hS' : S (i + 1) = S i := by simp [hSsucc, hs]
      refine runs_nop_le ?_ ?_
      · refine ⟨⟨fun r hr => ?_, by simp, ?_, fun a ha ha' => ?_, ?_, ?_⟩, by simp [r25]⟩
        · simp [show r ≠ 25 by omega, show r ≠ 26 by omega, show r ≠ 27 by omega, hR r hr]
        · simp [hS', r29, hn_def]
        · exact hfr a ha ha'
        · rw [hS']; exact hkeys
        · rw [hS']; exact hasg
      · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
        omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 25) (lo := .const 0)
    (hi := .reg 11) (body := slotKeyStep)
    (P := fun st => st.mem = mem ∧ st.regs 29 = 0 ∧ ∀ r, r < 25 ∨ 29 < r → st.regs r = R r)
    (Inv := Inv) 100 0 m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 25 by omega, hP.2.2 r hr], by simp,
      by simp [S, slotSelUpTo, hP.2.1], fun a _ _ => by simp [hP.1],
      by simp [S, slotSelUpTo, listAt_nil], fun t ht => by simp [S, slotSelUpTo] at ht⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 11 (by omega)).trans hR11)) hstep
  have hSm : S m = eL.filter sel := by
    show (eL.take eL.length).filter sel = _
    rw [List.take_length]
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, h29, hfr, hkeys, hasg⟩ := hQ
      rw [hSm] at h29 hkeys hasg
      exact ⟨hR, h29, hfr, hkeys, hasg⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

end MinCostFlow.SparseCore.Program
