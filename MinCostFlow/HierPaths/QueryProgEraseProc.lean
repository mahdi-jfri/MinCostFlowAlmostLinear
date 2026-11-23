module

public import MinCostFlow.HierPaths.QueryProgErase
public import WordRAM.Tactic
public import WordRAM.Logic

/-!
# The loop erasure procedure

The procedure `eraseProc` erases the loops of a walk given by its steps, as `arrFrom`
(`HierPaths/QueryProgErase.lean`) does, on arrays. Its registers:

* `0`: the address of the edges `e_0, …, e_{k-1}` of the steps;
* `1`: the address of the vertices `y_0, …, y_{k-1}` reached by the steps;
* `2`: the number `k` of steps; `3`: the start vertex `s`;
* `4`: the address of the position array, of length `n`, zero on entry and on exit;
* `5`, `6`: the addresses of the stack arrays for the edges and the vertices;
* `7`: the step counter; `8`: the length of the stack; `9`: the vertex `y_i`, and at the end the
  length of the erased stack; `10`: the length to cut the stack to.

For each step `(e, y)`, the cut length is `0` if `y = s` and the position of `y` otherwise. If it
is not zero, or `y = s`, the stack is cut to it by `popTo`, which clears the positions of the
removed entries. Otherwise the step is pushed and `y` gets position `len + 1`. At the end `popTo`
with cut length `0` clears the remaining positions, and the procedure returns the length of the
stack, saved in register `9` before.

This file proves the rule of `popTo` (`popTo_triple`), the rule of one step of the main loop
(`eraseStep_triple`), and the contract of the whole procedure (`eraseProc_meetsContract`): it
returns the length of `arrFrom s [] (E.zip Y)` and leaves its edges and vertices in the stack
arrays, with the position array zero again, at cost at most `95 k + 30`. For a walk `P` from `s`,
`loopErase_eq_eraseOut` says that this stack gives the loop erasure of `P`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Cut the stack to the length in register `10`, clearing the positions of the removed
entries. -/
def popTo : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 8))
    (.assign 8 (.bin .sub (.reg 8) (.const 1)) ;;
      .store (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 8)))) (.const 0))

/-- Push the step `(e_i, y_i)`: write it on top of the stack and give `y_i` its position. -/
def pushStep : Stmt :=
  .store (.bin .add (.reg 5) (.reg 8)) (.load (.bin .add (.reg 0) (.reg 7))) ;;
  .store (.bin .add (.reg 6) (.reg 8)) (.reg 9) ;;
  .assign 8 (.bin .add (.reg 8) (.const 1)) ;;
  .store (.bin .add (.reg 4) (.reg 9)) (.reg 8)

/-- The body of the main loop, for step `i` in register `7`. -/
def eraseStepBody : Stmt :=
  .assign 9 (.load (.bin .add (.reg 1) (.reg 7))) ;;
  .cond (.bin .eq (.reg 9) (.reg 3)) (.assign 10 (.const 0))
    (.assign 10 (.load (.bin .add (.reg 4) (.reg 9)))) ;;
  .cond (.bin .eq (.reg 9) (.reg 3)) popTo (.cond (.reg 10) popTo pushStep)

/-- The loop erasure procedure. -/
def eraseProc : Stmt :=
  .assign 8 (.const 0) ;;
  forRange 7 (.const 0) (.reg 2) eraseStepBody ;;
  .assign 9 (.reg 8) ;;
  .assign 10 (.const 0) ;;
  popTo ;;
  .ret (.reg 9)

/-- The cells that the procedure does not write: outside the position array and the stack
arrays. -/
def EraseOutside (posA stE stY n k a : ℕ) : Prop :=
  (a < posA ∨ posA + n ≤ a) ∧ (a < stE ∨ stE + k ≤ a) ∧ (a < stY ∨ stY + k ≤ a)

/-- The stack after the first `i` steps. -/
def erasePrefix (s : ℕ) (E Y : List ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  arrFrom s [] ((E.zip Y).take i)

/-- The invariant of the main loop before step `i`. -/
def EraseInv (inE inY s posA stE stY n : ℕ) (E Y : List ℕ) (mem₀ : ℕ → ℕ) (i : ℕ)
    (st : State) : Prop :=
  st.regs 0 = inE ∧ st.regs 1 = inY ∧ st.regs 2 = E.length ∧ st.regs 3 = s ∧
  st.regs 4 = posA ∧ st.regs 5 = stE ∧ st.regs 6 = stY ∧ st.regs 7 = i ∧
  st.regs 8 = (erasePrefix s E Y i).length ∧
  ListAt st.mem stE ((erasePrefix s E Y i).map Prod.fst) ∧
  ListAt st.mem stY ((erasePrefix s E Y i).map Prod.snd) ∧
  (∀ v < n, st.mem (posA + v) = stackPos (erasePrefix s E Y i) v) ∧
  ∀ a, EraseOutside posA stE stY n E.length a → st.mem a = mem₀ a

/-- What the procedure needs of its memory: the steps, a zero position array, and regions that
do not overlap. -/
structure EraseMem (inE inY s posA stE stY n : ℕ) (E Y : List ℕ) (mem₀ : ℕ → ℕ) : Prop where
  len : Y.length = E.length
  listE : ListAt mem₀ inE E
  listY : ListAt mem₀ inY Y
  vert : ∀ y ∈ Y, y < n
  start : s < n
  outE : ∀ j < E.length, EraseOutside posA stE stY n E.length (inE + j)
  outY : ∀ j < E.length, EraseOutside posA stE stY n E.length (inY + j)
  disjEA : stE + E.length ≤ posA ∨ posA + n ≤ stE
  disjYA : stY + E.length ≤ posA ∨ posA + n ≤ stY
  disjEY : stE + E.length ≤ stY ∨ stY + E.length ≤ stE


/-- The contract of `eraseProc` for the steps `(E[i], Y[i])` from `s`: it returns the length of
the erased stack `arrFrom s [] (E.zip Y)`, which it leaves in the stack arrays; the position
array is zero again, and no other cell outside the three arrays changes. -/
def eraseContract (inE inY s posA stE stY n : ℕ) (E Y : List ℕ) : Contract where
  pre args mem := args = [inE, inY, E.length, s, posA, stE, stY] ∧
    EraseMem inE inY s posA stE stY n E Y mem ∧ ∀ v < n, mem (posA + v) = 0
  post _ mem v mem' := v = (arrFrom s [] (E.zip Y)).length ∧
    ListAt mem' stE ((arrFrom s [] (E.zip Y)).map Prod.fst) ∧
    ListAt mem' stY ((arrFrom s [] (E.zip Y)).map Prod.snd) ∧
    (∀ v < n, mem' (posA + v) = 0) ∧
    ∀ a, EraseOutside posA stE stY n E.length a → mem' a = mem a
  cost _ _ := 95 * E.length + 30


end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM

public section

/-- The rule of `popTo`. From a state `st₀` whose stack `r` (vertices at register `6`) has length
`len` in register `8` and positions `stackPos (r.take len)` in the array at register `4`, it cuts
the stack to the length `q ≤ len` in register `10`. It changes only register `8` and the
position array, and costs `17` per removed entry plus `4`. -/
theorem popTo_triple {w : ℕ} {p : Program} {st₀ : State} {r : List (ℕ × ℕ)} {n posA stY q len : ℕ}
    (hnd : (r.map Prod.snd).Nodup) (hlt : ∀ x ∈ r, x.2 < n)
    (h4 : st₀.regs 4 = posA) (h6 : st₀.regs 6 = stY) (h10 : st₀.regs 10 = q)
    (h8 : st₀.regs 8 = len) (hq : q ≤ len) (hlen : len ≤ r.length)
    (hY : ListAt st₀.mem stY (r.map Prod.snd))
    (hdisj : stY + r.length ≤ posA ∨ posA + n ≤ stY)
    (hpos : ∀ v < n, st₀.mem (posA + v) = stackPos (r.take len) v)
    (hw : 1 < 2 ^ w) (hwA : posA + n < 2 ^ w) (hwY : stY + r.length < 2 ^ w) :
    Triple w p (fun st => st = st₀) popTo
      (normalPost fun st => (∀ x ≠ 8, st.regs x = st₀.regs x) ∧ st.regs 8 = q ∧
        (∀ a, a < posA ∨ posA + n ≤ a → st.mem a = st₀.mem a) ∧
        ∀ v < n, st.mem (posA + v) = stackPos (r.take q) v)
      (fun _ => 17 * (len - q) + 4) := by
  let Inv : State → Prop := fun st =>
    (∀ x ≠ 8, st.regs x = st₀.regs x) ∧ q ≤ st.regs 8 ∧ st.regs 8 ≤ r.length ∧
      (∀ a, a < posA ∨ posA + n ≤ a → st.mem a = st₀.mem a) ∧
      ∀ v < n, st.mem (posA + v) = stackPos (r.take (st.regs 8)) v
  have hloop : Triple w p Inv popTo
      (normalPost fun st => (∀ x ≠ 8, st.regs x = st₀.regs x) ∧ st.regs 8 = q ∧
        (∀ a, a < posA ∨ posA + n ≤ a → st.mem a = st₀.mem a) ∧
        ∀ v < n, st.mem (posA + v) = stackPos (r.take q) v)
      (fun st => 17 * (st.regs 8 - q) + 4) := by
    refine Triple.loop_measure (m := fun st => st.regs 8)
      (condVal := fun st => if st.regs 10 < st.regs 8 then 1 else 0) ?_ ?_ ?_
    · intro st hI
      have : st.regs 10 = q := (hI.1 10 (by decide)).trans h10
      eval_expr
    · intro st hI hc
      have h10' : st.regs 10 = q := (hI.1 10 (by decide)).trans h10
      have hle : st.regs 8 ≤ q := by
        by_contra h; simp only [h10', show q < st.regs 8 by omega, ↓reduceIte] at hc
        exact one_ne_zero hc
      have heq : st.regs 8 = q := le_antisymm hle hI.2.1
      refine ⟨⟨hI.1, heq, hI.2.2.2.1, fun v hv => by rw [hI.2.2.2.2 v hv, heq]⟩, ?_⟩
      simp
    · intro st hI hc
      obtain ⟨hregs, hqj, hjr, hframe, hposj⟩ := hI
      have h10' : st.regs 10 = q := (hregs 10 (by decide)).trans h10
      have h4' : st.regs 4 = posA := (hregs 4 (by decide)).trans h4
      have h6' : st.regs 6 = stY := (hregs 6 (by decide)).trans h6
      obtain ⟨j, hj⟩ : ∃ j, st.regs 8 = j := ⟨_, rfl⟩
      have hqj' : q < j := by
        by_contra h
        simp only [h10', hj, show ¬ q < j from h, ↓reduceIte, ne_eq, not_true_eq_false] at hc
      rw [hj] at hjr hposj
      have hj1 : j - 1 < r.length := by omega
      -- The vertex of the removed entry.
      have hz : st.mem (stY + (j - 1)) = r[j - 1].2 := by
        rw [hframe _ (by omega)]
        have := hY.getElem (i := j - 1) (by simpa using hj1)
        simpa using this
      have hzn : r[j - 1].2 < n := hlt _ (List.getElem_mem hj1)
      refine ⟨13, ?_⟩
      wram_enter
      subst hpre
      wram_step
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · intro x hx
          simp only [Function.update_of_ne hx]
          exact hregs x hx
        · simp only [Function.update_self]; omega
        · simp only [Function.update_self]; omega
        · intro a ha
          simp only
          rw [Function.update_of_ne (by omega)]
          exact hframe a ha
        · intro v hv
          simp only [Function.update_self, hz]
          by_cases hvz : v = r[j - 1].2
          · subst hvz
            rw [Function.update_self, stackPos_take, stackPos_getElem hnd hj1]
            simp
          · rw [Function.update_of_ne (by omega), hposj v hv, stackPos_take, stackPos_take]
            have hne : stackPos r v ≠ j := by
              intro h
              exact hvz (eq_of_stackPos_eq hj1 (by rw [h]; omega))
            by_cases hle : stackPos r v ≤ j
            · simp only [hle, ↓reduceIte, show stackPos r v ≤ j - 1 by omega]
            · simp only [hle, ↓reduceIte, show ¬ stackPos r v ≤ j - 1 by omega]
        · simp only [Function.update_self, hj]; omega
        · simp only [Function.update_self, hj]
          wram_cost
      · wram_cost
  refine (hloop.weaken_pre ?_).mono_cost ?_
  · rintro st rfl
    refine ⟨fun x _ => rfl, by omega, by omega, fun a _ => rfl, ?_⟩
    rw [h8]; exact hpos
  · rintro st rfl
    rw [h8]

/-! ### The stack after each step -/

theorem erasePrefix_zero (s : ℕ) (E Y : List ℕ) : erasePrefix s E Y 0 = [] := rfl

theorem erasePrefix_succ {s : ℕ} {E Y : List ℕ} (hlen : Y.length = E.length) {i : ℕ}
    (hi : i < E.length) :
    erasePrefix s E Y (i + 1) = arrStep s (erasePrefix s E Y i) (E[i], Y[i]) := by
  unfold erasePrefix
  rw [arrFrom_take_succ s [] _ (by simp [hlen]; omega)]
  simp

theorem nodup_erasePrefix (s : ℕ) (E Y : List ℕ) (i : ℕ) :
    (s :: (erasePrefix s E Y i).map Prod.snd).Nodup :=
  nodup_arrFrom s [] _ (by simp)

theorem erasePrefix_vert {s n : ℕ} {E Y : List ℕ} (hY : ∀ y ∈ Y, y < n) (i : ℕ) :
    ∀ x ∈ erasePrefix s E Y i, x.2 < n := by
  intro x hx
  rcases mem_arrFrom s [] _ x hx with h | h
  · simp at h
  · exact hY _ (List.of_mem_zip (List.mem_of_mem_take h)).2

theorem length_erasePrefix_le (s : ℕ) (E Y : List ℕ) (i : ℕ) :
    (erasePrefix s E Y i).length ≤ i := by
  have := length_arrFrom_le s [] ((E.zip Y).take i)
  simp only [List.length_nil, List.length_take, zero_add] at this
  unfold erasePrefix
  omega

theorem length_erasePrefix_succ_le {s : ℕ} {E Y : List ℕ} (hlen : Y.length = E.length) {i : ℕ}
    (hi : i < E.length) :
    (erasePrefix s E Y (i + 1)).length ≤ (erasePrefix s E Y i).length + 1 := by
  rw [erasePrefix_succ hlen hi]; exact length_arrStep_le _ _ _

/-- The cost bound of step `i`: `17` for each entry it removes, plus a constant. -/
def eraseStepCost (s : ℕ) (E Y : List ℕ) (i : ℕ) : ℕ :=
  17 * ((erasePrefix s E Y i).length + 1 - (erasePrefix s E Y (i + 1)).length) + 60

/-- A step that cuts the stack ends with the invariant of the next step. -/
theorem popTo_finish {w : ℕ} {p : Program} {inE inY s posA stE stY n : ℕ} {E Y : List ℕ}
    {mem₀ : ℕ → ℕ} (hM : EraseMem inE inY s posA stE stY n E Y mem₀) (hw : 1 < 2 ^ w)
    (hwA : posA + n < 2 ^ w) (hwY : stY + E.length < 2 ^ w) {i : ℕ} (hi : i < E.length)
    {st st₁ : State} (hI : EraseInv inE inY s posA stE stY n E Y mem₀ i st)
    (hregs : ∀ x, x ≠ 8 → x ≠ 9 → x ≠ 10 → st₁.regs x = st.regs x)
    (h8 : st₁.regs 8 = (erasePrefix s E Y i).length) {q : ℕ} (h10 : st₁.regs 10 = q)
    (hmem : st₁.mem = st.mem) (hq : erasePrefix s E Y (i + 1) = (erasePrefix s E Y i).take q)
    (hqle : q ≤ (erasePrefix s E Y i).length) :
    Triple w p (fun x => x = st₁) popTo
      (normalPost fun st' => EraseInv inE inY s posA stE stY n E Y mem₀ (i + 1)
          { st' with regs := Function.update st'.regs 7 (i + 1) } ∧ st'.regs 7 = i)
      (fun _ => 17 * ((erasePrefix s E Y i).length - q) + 4) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8', hLE, hLY, hpos, hframe⟩ := hI
  have hrl := length_erasePrefix_le s E Y i
  have hnd := (List.nodup_cons.mp (nodup_erasePrefix s E Y i)).2
  refine (popTo_triple (n := n) (posA := posA) (stY := stY) hnd
    (erasePrefix_vert hM.vert i) ((hregs 4 (by decide) (by decide) (by decide)).trans h4)
    ((hregs 6 (by decide) (by decide) (by decide)).trans h6) h10 h8 hqle le_rfl
    (by rw [hmem]; exact hLY) (by have := hM.disjYA; omega)
    (by rw [hmem, List.take_length]; exact hpos) hw hwA (by omega)).strengthen_post ?_
  intro o st' hpost
  cases o with
  | returned u => exact hpost.elim
  | normal =>
    obtain ⟨hr', hq8, hfr, hpos'⟩ := hpost
    have hreg : ∀ x, x ≠ 8 → x ≠ 9 → x ≠ 10 → st'.regs x = st.regs x := fun x a b c =>
      (hr' x a).trans (hregs x a b c)
    have hmemA : ∀ a, a < posA ∨ posA + n ≤ a → st'.mem a = st.mem a := fun a ha =>
      (hfr a ha).trans (by rw [hmem])
    have hE : ListAt st'.mem stE ((erasePrefix s E Y (i + 1)).map Prod.fst) := by
      rw [hq, List.map_take]
      refine (hLE.take q).congr fun a ha1 ha2 => hmemA a ?_
      have := hM.disjEA
      simp only [List.length_take, List.length_map] at ha2
      omega
    have hY : ListAt st'.mem stY ((erasePrefix s E Y (i + 1)).map Prod.snd) := by
      rw [hq, List.map_take]
      refine (hLY.take q).congr fun a ha1 ha2 => hmemA a ?_
      have := hM.disjYA
      simp only [List.length_take, List.length_map] at ha2
      omega
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE, hY, ?_, ?_⟩, ?_⟩
    all_goals (try simp only [Function.update_apply, ↓reduceIte, Nat.reduceEqDiff])
    · rw [hreg 0 (by decide) (by decide) (by decide), h0]
    · rw [hreg 1 (by decide) (by decide) (by decide), h1]
    · rw [hreg 2 (by decide) (by decide) (by decide), h2]
    · rw [hreg 3 (by decide) (by decide) (by decide), h3]
    · rw [hreg 4 (by decide) (by decide) (by decide), h4]
    · rw [hreg 5 (by decide) (by decide) (by decide), h5]
    · rw [hreg 6 (by decide) (by decide) (by decide), h6]
    · rw [hq8, hq, List.length_take]; omega
    · intro v hv; rw [hpos' v hv, hq]
    · intro a ha
      rw [hmemA a ha.1, hframe a ha]
    · rw [hreg 7 (by decide) (by decide) (by decide), h7]

/-- The rule of one step of the main loop. -/
theorem eraseStep_triple {w : ℕ} {p : Program} {inE inY s posA stE stY n : ℕ} {E Y : List ℕ}
    {mem₀ : ℕ → ℕ} (hM : EraseMem inE inY s posA stE stY n E Y mem₀) (hw : 1 < 2 ^ w)
    (hwA : posA + n < 2 ^ w) (hwE : stE + E.length < 2 ^ w) (hwY : stY + E.length < 2 ^ w)
    (hwiE : inE + E.length < 2 ^ w) (hwiY : inY + E.length < 2 ^ w) {i : ℕ}
    (hi : i < E.length) :
    Triple w p (EraseInv inE inY s posA stE stY n E Y mem₀ i) eraseStepBody
      (normalPost fun st₁ => EraseInv inE inY s posA stE stY n E Y mem₀ (i + 1)
          { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧ st₁.regs 7 = i)
      (fun _ => eraseStepCost s E Y i) := by
  wram_enter
  have hI := hpre
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hLE, hLY, hpos, hframe⟩ := hpre
  have hiY : i < Y.length := hM.len ▸ hi
  have hy : st.mem (inY + i) = Y[i] := by
    rw [hframe _ (hM.outY i hi)]; exact hM.listY i hiY
  have hyn : Y[i] < n := hM.vert _ (List.getElem_mem hiY)
  have hsn := hM.start
  have hrl := length_erasePrefix_le s E Y i
  have hnd := nodup_erasePrefix s E Y i
  have hvert := erasePrefix_vert (s := s) (E := E) hM.vert i
  have hsucc := erasePrefix_succ (s := s) hM.len hi
  unfold eraseStepBody
  wram_step
  wram_step
  · -- The step goes back to the start: cut the stack to length `0`.
    wram_step
    wram_step
    have hys : Y[i] = s := by rw [← hy, hcond, h3]
    have hq : erasePrefix s E Y (i + 1) = (erasePrefix s E Y i).take 0 := by
      rw [hsucc, arrStep_of_pop (Or.inl hys)]
      simp [hys]
    have hl1 : (erasePrefix s E Y (i + 1)).length = 0 := by rw [hq]; simp
    refine runs_triple_le (popTo_finish hM hw hwA hwY hi hI ?_ ?_ ?_ ?_ hq (Nat.zero_le _))
      rfl (fun _ _ h => h) ?_
    · intro x hx8 hx9 hx10
      simp [hx9, hx10]
    · simp [h8]
    · simp
    · rfl
    · unfold eraseStepCost
      rw [hl1]
      wram_cost
  · have hys : Y[i] ≠ s := by rw [← hy, ← h3]; exact hcond
    have hyn' : st.mem (inY + i) < n := by rw [hy]; exact hyn
    have hp : st.mem (posA + st.mem (inY + i)) = stackPos (erasePrefix s E Y i) Y[i] := by
      rw [hy]; exact hpos _ hyn
    wram_step
    wram_step
    wram_step
    · -- The vertex is on the stack: cut the stack to its position.
      rw [h4, hp] at hcond
      have hmem : Y[i] ∈ (erasePrefix s E Y i).map Prod.snd := by
        by_contra h; exact hcond (stackPos_eq_zero_iff.mpr h)
      have hq : erasePrefix s E Y (i + 1) =
          (erasePrefix s E Y i).take (stackPos (erasePrefix s E Y i) Y[i]) := by
        rw [hsucc, arrStep_of_pop (Or.inr hmem)]
        simp [hys]
      have hqle := stackPos_le (erasePrefix s E Y i) Y[i]
      have hl1 : (erasePrefix s E Y (i + 1)).length = stackPos (erasePrefix s E Y i) Y[i] := by
        rw [hq, List.length_take]; omega
      refine runs_triple_le (popTo_finish hM hw hwA hwY hi hI ?_ ?_ ?_ ?_ hq hqle)
        rfl (fun _ _ h => h) ?_
      · intro x hx8 hx9 hx10
        simp [hx9, hx10]
      · simp [h8]
      · simp [h4, hp]
      · rfl
      · unfold eraseStepCost
        rw [hl1]
        wram_cost
    · -- The vertex is new: push the step.
      rw [h4, hp] at hcond
      have hnot : Y[i] ∉ (erasePrefix s E Y i).map Prod.snd := stackPos_eq_zero_iff.mp hcond
      have hq : erasePrefix s E Y (i + 1) = erasePrefix s E Y i ++ [(E[i], Y[i])] := by
        rw [hsucc, arrStep_of_push hys hnot]
      have he : st.mem (inE + i) = E[i] := by
        rw [hframe _ (hM.outE i hi)]; exact hM.listE i hi
      have hl1 : (erasePrefix s E Y (i + 1)).length = (erasePrefix s E Y i).length + 1 := by
        rw [hq]; simp
      have hlk : (erasePrefix s E Y i).length < E.length := by omega
      unfold pushStep
      wram_run
      · simp only [normalPost_normal, h0, h4, h5, h6, h7, h8, he, hy]
        obtain ⟨len, hlen⟩ : ∃ len, (erasePrefix s E Y i).length = len := ⟨_, rfl⟩
        rw [hlen] at hl1 hlk hrl
        have hEA := hM.disjEA
        have hYA := hM.disjYA
        have hEY := hM.disjEY
        have hLE' : ListAt st.mem stE ((erasePrefix s E Y i).map Prod.fst) := hLE
        have hLY' : ListAt st.mem stY ((erasePrefix s E Y i).map Prod.snd) := hLY
        have hlE : ((erasePrefix s E Y i).map Prod.fst).length = len := by simp [hlen]
        have hlY : ((erasePrefix s E Y i).map Prod.snd).length = len := by simp [hlen]
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
        · simp [h4]
        · simp [h5]
        · simp [h6]
        · simp
        · simp only [Function.update_apply, ↓reduceIte, Nat.reduceEqDiff]; omega
        · -- The edge stack.
          rw [hq, List.map_append, List.map_singleton]
          dsimp only
          rw [hlen]
          have h1' := hLE'.snoc E[i]
          rw [hlE] at h1'
          refine (h1'.update_outside ?_).update_outside ?_ <;>
            simp only [List.length_append, List.length_singleton, hlE] <;> omega
        · -- The vertex stack.
          rw [hq, List.map_append, List.map_singleton]
          dsimp only
          rw [hlen]
          have h1' := (hLY'.update_outside (x := stE + len) (v := E[i]) (by rw [hlY]; omega)).snoc
            Y[i]
          rw [hlY] at h1'
          refine h1'.update_outside ?_
          simp only [List.length_append, List.length_singleton, hlY]
          omega
        · intro v hv
          rw [hq, stackPos_push hnot]
          simp only [Function.update_apply]
          have := hpos v hv
          split_ifs <;> omega
        · intro a ha
          obtain ⟨ha1, ha2, ha3⟩ := ha
          simp only [Function.update_apply]
          have := hframe a ⟨ha1, ha2, ha3⟩
          split_ifs <;> omega
        · simp [h7]
      · unfold eraseStepCost
        rw [hl1]
        wram_cost

/-- The step costs telescope: the entries removed are at most the entries pushed. -/
theorem rangeCost_eraseStepCost_le {s : ℕ} {E Y : List ℕ} (hlen : Y.length = E.length) :
    ∀ k ≤ E.length,
      rangeCost (eraseStepCost s E Y) 0 k + 17 * (erasePrefix s E Y k).length ≤ 77 * k
  | 0, _ => by simp [erasePrefix_zero]
  | k + 1, hk => by
    have ih := rangeCost_eraseStepCost_le (s := s) hlen k (by omega)
    have hle := length_erasePrefix_succ_le (s := s) hlen (i := k) (by omega)
    rw [rangeCost_zero_eq_range] at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eraseStepCost] at ih ⊢
    omega

theorem erasePrefix_length (s : ℕ) {E Y : List ℕ} (hlen : Y.length = E.length) :
    erasePrefix s E Y E.length = arrFrom s [] (E.zip Y) := by
  unfold erasePrefix
  rw [List.take_of_length_le (by simp [hlen])]

/-- The loop erasure procedure meets its contract. -/
theorem eraseProc_meetsContract {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some eraseProc)
    {inE inY s posA stE stY n : ℕ} {E Y : List ℕ} (hw : 1 < 2 ^ w)
    (hwA : posA + n < 2 ^ w) (hwE : stE + E.length < 2 ^ w) (hwY : stY + E.length < 2 ^ w)
    (hwiE : inE + E.length < 2 ^ w) (hwiY : inY + E.length < 2 ^ w) :
    MeetsContract w p f (eraseContract inE inY s posA stE stY n E Y) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hM, hzero⟩ := hpre
  refine runs_start_le ?_
  unfold eraseProc
  wram_step
  refine runs_seq_triple_le
    (Triple.forRange_le (r := 7) (lo := .const 0) (hi := .reg 2) (body := eraseStepBody)
      (Inv := EraseInv inE inY s posA stE stY n E Y mem) (P := fun x => x = _)
      (eraseStepCost s E Y) 0 E.length (Nat.zero_le _) hw (fun _ => by omega) ?_ ?_ ?_
      (fun i _ hi => eraseStep_triple hM hw hwA hwE hwY hwiE hwiY hi)) rfl ?_
  · rintro st rfl
    refine ⟨by eval_expr, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp [startState, erasePrefix_zero])
    · intro v hv; simp [hzero v hv, stackPos]
  · intro i st _ _ hI; exact hI.2.2.2.2.2.2.2.1
  · intro i st _ _ hI
    have : st.regs 2 = E.length := hI.2.2.1
    eval_expr
  · intro st₁ hI
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hLE, hLY, hpos, hframe⟩ := hI
    have hlenK := erasePrefix_length s hM.len
    have hrl := length_erasePrefix_le s E Y E.length
    have hnd := (List.nodup_cons.mp (nodup_erasePrefix s E Y E.length)).2
    wram_step
    wram_step
    refine runs_seq_triple_le (popTo_triple (n := n) (posA := posA) (stY := stY) (q := 0)
      (len := (erasePrefix s E Y E.length).length) hnd (erasePrefix_vert hM.vert _)
      ?g4 ?g6 ?g10 ?g8 (Nat.zero_le _) le_rfl ?gY
      (by have := hM.disjYA; omega) ?gpos hw hwA (by omega))
      rfl ?_
    case g4 => simp [h4]
    case g6 => simp [h6]
    case g10 => simp
    case g8 => simp [h8]
    case gY => exact hLY
    case gpos => rw [List.take_length]; exact hpos
    intro st₂ ⟨hr2, hq2, hfr2, hpos2⟩
    have hT := rangeCost_eraseStepCost_le (s := s) hM.len E.length le_rfl
    refine runs_ret_le (by eval_expr) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
    · simp only [Outcome.value]
      rw [← hlenK, hr2 9 (by decide)]; simp
    · rw [← hlenK]
      refine hLE.congr fun a ha1 ha2 => ?_
      have := hM.disjEA
      simp only [List.length_map] at ha2
      rw [hfr2 a (by omega)]
    · rw [← hlenK]
      refine hLY.congr fun a ha1 ha2 => ?_
      have := hM.disjYA
      simp only [List.length_map] at ha2
      rw [hfr2 a (by omega)]
    · intro v hv; rw [hpos2 v hv]; simp [stackPos]
    · intro a ha
      rw [hfr2 a ha.1]
      exact hframe a ha
    · simp only [eraseContract]
      wram_cost

/-- What the procedure computes for a walk: called with the edges of `P` and its vertices after
the first, it leaves the steps of the loop erasure of `P` in the stack arrays. -/
theorem loopErase_eq_eraseOut (P : Spanner.Walk) {s : ℕ} {t : List ℕ} (hv : P.verts = s :: t) :
    loopErase P = ofSteps s (arrFrom s [] (P.edges.zip t)) := by
  rw [loopErase_eq_arrFrom P hv, Walk.steps, hv, List.tail_cons]

end

end MinCostFlow.HierPaths
