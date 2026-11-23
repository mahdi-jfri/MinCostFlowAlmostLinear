module

public import MinCostFlow.HierPaths.QueryProgSteps
public import WordRAM.Tactic
public import WordRAM.Logic

/-!
# Copying the steps of a walk into the buffer

`GetPath` writes the steps of its walk into two buffers, the edges and the vertices reached
(`HierPaths/QueryProgSteps.lean`). Each piece of the walk is a stored walk (a connector walk or an
attachment), used forward or reversed. The procedure `copyProc` appends the steps of one piece.
Its registers:

* `0`, `1`: the addresses of the vertices and of the edges of the stored walk, with `ne` edges
  and `ne + 1` vertices;
* `2`: the number `ne` of edges; `3`: `1` to copy forward, `0` to copy reversed;
* `4`, `5`: the addresses of the edge buffer and of the vertex buffer; `6`: the number `cnt` of
  steps already in the buffers; `7`: the counter.

Step `i` of the walk is `(edges[i], verts[i + 1])` forward and `(edges[ne-1-i], verts[ne-1-i])`
reversed (`steps_getElem`, `steps_reverse_getElem`). The procedure returns `cnt + ne`, and costs at
most `60 ne + 16` (`copyProc_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- The body of the copy loop, for step `i` in register `7`: read the step into registers `8`
and `9`, then write it. -/
def copyStepBody : Stmt :=
  .cond (.reg 3)
    (.assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
      .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.reg 7)) (.const 1))))
    (.assign 8 (.load (.bin .add (.reg 1) (.bin .sub (.bin .sub (.reg 2) (.const 1)) (.reg 7)))) ;;
      .assign 9 (.load (.bin .add (.reg 0) (.bin .sub (.bin .sub (.reg 2) (.const 1)) (.reg 7))))) ;;
  .store (.bin .add (.bin .add (.reg 4) (.reg 6)) (.reg 7)) (.reg 8) ;;
  .store (.bin .add (.bin .add (.reg 5) (.reg 6)) (.reg 7)) (.reg 9)

/-- The copy procedure. -/
def copyProc : Stmt :=
  forRange 7 (.const 0) (.reg 2) copyStepBody ;;
  .ret (.bin .add (.reg 6) (.reg 2))

/-- The piece of walk that is copied: the stored walk, forward or reversed. -/
def copyWalk (V Ed : List ℕ) (fwd : Bool) : Walk :=
  if fwd then ⟨V, Ed⟩ else (⟨V, Ed⟩ : Walk).reverse

/-- The cells that the procedure does not write. -/
def CopyOutside (outE outY cnt ne a : ℕ) : Prop :=
  (a < outE + cnt ∨ outE + cnt + ne ≤ a) ∧ (a < outY + cnt ∨ outY + cnt + ne ≤ a)

/-- The contract of `copyProc` for the stored walk with vertices `V` and edges `Ed`. -/
def copyContract (vA eA outE outY cnt : ℕ) (V Ed : List ℕ) (fwd : Bool) : Contract where
  pre args mem := args = [vA, eA, Ed.length, if fwd then 1 else 0, outE, outY, cnt] ∧
    (Ed = [] ∨ V.length = Ed.length + 1) ∧ ListAt mem vA V ∧ ListAt mem eA Ed ∧
    (∀ j < V.length, CopyOutside outE outY cnt Ed.length (vA + j)) ∧
    (∀ j < Ed.length, CopyOutside outE outY cnt Ed.length (eA + j)) ∧
    (outE + cnt + Ed.length ≤ outY + cnt ∨ outY + cnt + Ed.length ≤ outE + cnt)
  post _ mem v mem' := v = cnt + Ed.length ∧
    ListAt mem' (outE + cnt) ((Walk.steps (copyWalk V Ed fwd)).map Prod.fst) ∧
    ListAt mem' (outY + cnt) ((Walk.steps (copyWalk V Ed fwd)).map Prod.snd) ∧
    ∀ a, CopyOutside outE outY cnt Ed.length a → mem' a = mem a
  cost _ _ := 60 * Ed.length + 16

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

public section

theorem length_steps_copyWalk {V Ed : List ℕ} (hV : V.length = Ed.length + 1) (fwd : Bool) :
    (Walk.steps (copyWalk V Ed fwd)).length = Ed.length := by
  cases fwd <;> simp [copyWalk, Walk.steps, Walk.reverse, hV]

/-- A stored empty walk has no steps even when its vertex list is empty. -/
theorem length_steps_copyWalk_empty_or {V Ed : List ℕ}
    (hV : Ed = [] ∨ V.length = Ed.length + 1) (fwd : Bool) :
    (Walk.steps (copyWalk V Ed fwd)).length = Ed.length := by
  rcases hV with rfl | hV
  · cases fwd <;> simp [copyWalk, Walk.steps]
  · exact length_steps_copyWalk hV fwd

/-- Step `i` of the stored walk. -/
theorem steps_getElem {V Ed : List ℕ} (hV : V.length = Ed.length + 1) {i : ℕ}
    (hi : i < Ed.length) :
    (Walk.steps (copyWalk V Ed true))[i]'(by rw [length_steps_copyWalk hV]; exact hi) =
      (Ed[i], V[i + 1]'(by omega)) := by
  simp [copyWalk, Walk.steps, List.getElem_zip, List.getElem_tail]

/-- Step `i` of the reversed stored walk. -/
theorem steps_reverse_getElem {V Ed : List ℕ} (hV : V.length = Ed.length + 1) {i : ℕ}
    (hi : i < Ed.length) :
    (Walk.steps (copyWalk V Ed false))[i]'(by rw [length_steps_copyWalk hV]; exact hi) =
      (Ed[Ed.length - 1 - i]'(by omega), V[Ed.length - 1 - i]'(by omega)) := by
  simp only [copyWalk, Bool.false_eq_true, ↓reduceIte, Walk.steps, Walk.reverse,
    List.getElem_zip, List.getElem_tail, List.getElem_reverse, Prod.mk.injEq]
  constructor <;> first | trivial | rfl | (congr 1; omega)

/-- The invariant of the copy loop before step `i`. -/
def CopyInv (vA eA outE outY cnt : ℕ) (V Ed : List ℕ) (fwd : Bool) (mem₀ : ℕ → ℕ) (i : ℕ)
    (st : State) : Prop :=
  st.regs 0 = vA ∧ st.regs 1 = eA ∧ st.regs 2 = Ed.length ∧ st.regs 3 = (if fwd then 1 else 0) ∧
  st.regs 4 = outE ∧ st.regs 5 = outY ∧ st.regs 6 = cnt ∧ st.regs 7 = i ∧
  ListAt st.mem (outE + cnt) (((Walk.steps (copyWalk V Ed fwd)).take i).map Prod.fst) ∧
  ListAt st.mem (outY + cnt) (((Walk.steps (copyWalk V Ed fwd)).take i).map Prod.snd) ∧
  ∀ a, CopyOutside outE outY cnt Ed.length a → st.mem a = mem₀ a

/-- The copy procedure meets its contract. -/
theorem copyProc_meetsContract {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some copyProc)
    {vA eA outE outY cnt : ℕ} {V Ed : List ℕ} {fwd : Bool} (hw : 1 < 2 ^ w)
    (hwV : vA + Ed.length < 2 ^ w) (hwE : eA + Ed.length < 2 ^ w)
    (hwoE : outE + cnt + Ed.length < 2 ^ w) (hwoY : outY + cnt + Ed.length < 2 ^ w) :
    MeetsContract w p f (copyContract vA eA outE outY cnt V Ed fwd) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hV, hLV, hLE, hoV, hoE, hdisj⟩ := hpre
  have hlen := length_steps_copyWalk_empty_or hV fwd
  refine runs_start_le ?_
  unfold copyProc
  refine runs_seq_triple_le
    (Triple.forRange_const (r := 7) (lo := .const 0) (hi := .reg 2) (body := copyStepBody)
      (Inv := CopyInv vA eA outE outY cnt V Ed fwd mem) (P := fun x => x = _)
      50 0 Ed.length (Nat.zero_le _) hw (fun _ => by omega) ?_ ?_ ?_ ?_) rfl ?_
  · rintro st rfl
    refine ⟨by eval_expr, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp [startState])
  · intro i st _ _ hI; exact hI.2.2.2.2.2.2.2.1
  · intro i st _ _ hI
    have : st.regs 2 = Ed.length := hI.2.2.1
    eval_expr
  · intro i _ hi
    have hV := hV.resolve_left (by intro h; simp [h] at hi)
    wram_enter
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hOE, hOY, hframe⟩ := hpre
    have hsucc := List.take_succ_eq_append_getElem (l := Walk.steps (copyWalk V Ed fwd))
      (i := i) (by omega)
    have hlenE : (((Walk.steps (copyWalk V Ed fwd)).take i).map Prod.fst).length = i := by
      simp; omega
    have hlenY : (((Walk.steps (copyWalk V Ed fwd)).take i).map Prod.snd).length = i := by
      simp; omega
    unfold copyStepBody
    obtain ⟨x, hx, hm1, hm2⟩ : ∃ x : ℕ × ℕ,
        (Walk.steps (copyWalk V Ed fwd))[i]'(by omega) = x ∧
        st.mem (if fwd then eA + i else eA + (Ed.length - 1 - i)) = x.1 ∧
        st.mem (if fwd then vA + i + 1 else vA + (Ed.length - 1 - i)) = x.2 := by
      cases fwd
      · refine ⟨_, steps_reverse_getElem hV hi, ?_, ?_⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hframe _ (hoE _ (by omega))]; exact hLE _ (by omega)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hframe _ (hoV _ (by omega))]; exact hLV _ (by omega)
      · refine ⟨_, steps_getElem hV hi, ?_, ?_⟩
        · simp only [↓reduceIte]
          rw [hframe _ (hoE _ hi)]; exact hLE _ hi
        · simp only [↓reduceIte]
          rw [hframe _ (by rw [Nat.add_assoc]; exact hoV _ (by omega))]
          rw [Nat.add_assoc]; exact hLV _ (by omega)
    have hxE : outE + cnt + i < outY + cnt ∨ outY + cnt + Ed.length ≤ outE + cnt + i := by
      omega
    -- After the reads, the registers `8` and `9` hold the step.
    suffices hst : ∀ st₁ : State, st₁.mem = st.mem → st₁.regs 8 = x.1 → st₁.regs 9 = x.2 →
        (∀ r, r ≠ 8 → r ≠ 9 → st₁.regs r = st.regs r) → ∀ k T, k + 21 ≤ T →
        ∃ o st' c, Runs w p ω (.store (.bin .add (.bin .add (.reg 4) (.reg 6)) (.reg 7)) (.reg 8) ;;
          .store (.bin .add (.bin .add (.reg 5) (.reg 6)) (.reg 7)) (.reg 9)) st₁ o st' c ∧
          normalPost (fun st₂ => CopyInv vA eA outE outY cnt V Ed fwd mem (i + 1)
            { st₂ with regs := Function.update st₂.regs 7 (i + 1) } ∧ st₂.regs 7 = i) o st' ∧
          k + c ≤ T by
      cases fwd
      · simp only [Bool.false_eq_true, ↓reduceIte] at h3 hm1 hm2
        wram_step
        wram_step
        wram_step
        wram_step
        apply hst
        · rfl
        · simp [h0, h2, h7, hm1]
        · simp [h0, h2, h7, hm2]
        · intro r h8 h9; simp [h8, h9]
        · wram_cost
      · simp only [↓reduceIte] at h3 hm1 hm2
        wram_step
        wram_step
        wram_step
        wram_step
        apply hst
        · rfl
        · simp [h0, h7, hm1]
        · simp [h0, h7, hm2]
        · intro r h8 h9; simp [h8, h9]
        · wram_cost
    intro st₁ hmem h8 h9 hregs k T hkT
    have g4 : st₁.regs 4 = outE := (hregs 4 (by decide) (by decide)).trans h4
    have g5 : st₁.regs 5 = outY := (hregs 5 (by decide) (by decide)).trans h5
    have g6 : st₁.regs 6 = cnt := (hregs 6 (by decide) (by decide)).trans h6
    have g7 : st₁.regs 7 = i := (hregs 7 (by decide) (by decide)).trans h7
    wram_step
    refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [hregs 0 (by decide) (by decide), h0]
      · simp [hregs 1 (by decide) (by decide), h1]
      · simp [hregs 2 (by decide) (by decide), h2]
      · simp [hregs 3 (by decide) (by decide), h3]
      · simp [g4]
      · simp [g5]
      · simp [g6]
      · simp
      · rw [hsucc, List.map_append, hx]
        have h1' := hOE.snoc x.1
        rw [hlenE] at h1'
        rw [hmem]
        refine h1'.update_outside ?_
        simp only [List.length_append, List.length_singleton, hlenE]
        omega
      · rw [hsucc, List.map_append, hx]
        have h1' := (hOY.update_outside (x := outE + cnt + i) (v := x.1)
          (by rw [hlenY]; omega)).snoc x.2
        rw [hlenY] at h1'
        rw [hmem]
        exact h1'
      · intro a ha
        obtain ⟨ha1, ha2⟩ := ha
        simp only [Function.update_apply, hmem]
        have := hframe a ⟨ha1, ha2⟩
        split_ifs <;> omega
      · simp [g7]
    · wram_cost
  · intro st₁ hI
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hOE, hOY, hframe⟩ := hI
    refine runs_ret_le (by eval_expr) ⟨?_, ?_, ?_, ?_⟩ ?_
    · simp [Outcome.value]
    · rw [List.take_of_length_le (by omega)] at hOE; exact hOE
    · rw [List.take_of_length_le (by omega)] at hOY; exact hOY
    · exact hframe
    · simp only [copyContract]
      wram_cost

end

end MinCostFlow.HierPaths
