module

public import MinCostFlow.HierPaths.QueryProgCopy
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.HierPaths.QueryProgRoute

/-!
# Writing the answer of `GetPath`

After loop erasure the stack arrays hold the steps `r` of the path from `s`
(`HierPaths/QueryProgEraseProc.lean`). The answer is the walk `ofSteps s r`, written in the
format `WalkAt` (`Spanner/Layouts.lean`): the number of vertices, the vertices, the number of
edges, the edges. The procedure `writeWalkProc` writes it, with `copyListBody` copying the two
arrays (`writeWalkProc_meetsContract`). The part after the two header cells is proved on its
own, for any state (`writeWalkTail_runs`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- Copy `n` words from register `0` to register `1`. -/
def copyListBody : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))

/-- The contract of `copyListBody`: it copies the list `l` from `src` to `dst`, writing only the
cells `dst, …, dst + l.length - 1`. -/
def copyListContract (src dst : ℕ) (l : List ℕ) : Contract where
  pre args mem := args = [src, dst, l.length] ∧ ListAt mem src l ∧
    (src + l.length ≤ dst ∨ dst + l.length ≤ src)
  post _ mem _ mem' := ListAt mem' dst l ∧ ∀ a, a < dst ∨ dst + l.length ≤ a → mem' a = mem a
  cost _ _ := 20 * l.length + 8

/-- The part of `writeWalkProc` after the two header cells: copy the vertices, write the
number of edges, copy the edges. -/
def writeWalkTail (fList : ℕ) : Stmt :=
  .call 5 fList [.reg 2, .bin .add (.reg 4) (.const 2), .reg 3] ;;
  .store (.bin .add (.bin .add (.reg 4) (.const 2)) (.reg 3)) (.reg 3) ;;
  .call 5 fList [.reg 1, .bin .add (.bin .add (.reg 4) (.const 3)) (.reg 3), .reg 3] ;;
  .ret (.const 0)

/-- Write the walk `ofSteps s r` at `out`, for the stack `r` with edges at `stE` and vertices at
`stY` and length `len`. Registers: `0` `s`, `1` `stE`, `2` `stY`, `3` `len`, `4` `out`. -/
def writeWalkProc (fList : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 3) (.const 0))
    (.store (.reg 4) (.const 0) ;; .store (.bin .add (.reg 4) (.const 1)) (.const 0) ;;
      .ret (.const 0))
    .nop ;;
  .store (.reg 4) (.bin .add (.reg 3) (.const 1)) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 0) ;;
  writeWalkTail fList

/-- The contract of `writeWalkProc`. -/
def writeWalkContract (s stE stY out : ℕ) (r : List (ℕ × ℕ)) : Contract where
  pre args mem := args = [s, stE, stY, r.length, out] ∧
    ListAt mem stE (r.map Prod.fst) ∧ ListAt mem stY (r.map Prod.snd) ∧
    (stE + r.length ≤ out ∨ out + 2 * r.length + 3 ≤ stE) ∧
    (stY + r.length ≤ out ∨ out + 2 * r.length + 3 ≤ stY)
  post _ mem _ mem' := WalkAt mem' out (ofSteps s r) ∧
    ∀ a, a < out ∨ out + 2 * r.length + 3 ≤ a → mem' a = mem a
  cost _ _ := 50 * r.length + 60

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

public section

/-- The list copy meets its contract. -/
theorem copyList_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some copyListBody) {src dst : ℕ} {l : List ℕ} (hw : 1 < 2 ^ w)
    (hws : src + l.length < 2 ^ w) (hwd : dst + l.length < 2 ^ w) :
    MeetsContract w p f (copyListContract src dst l) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hl, hdisj⟩ := hpre
  refine runs_start_le ?_
  unfold copyListBody
  refine runs_triple_le
    (Triple.forRange_const (r := 3) (lo := .const 0) (hi := .reg 2)
      (Inv := fun i st => st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = l.length ∧
        st.regs 3 = i ∧ ListAt st.mem dst (l.take i) ∧
        ∀ a, a < dst ∨ dst + l.length ≤ a → st.mem a = mem a)
      (P := fun x => x = _) 8 0 l.length (Nat.zero_le _) hw (fun _ => by omega) ?_ ?_ ?_ ?_)
    rfl ?_ ?_
  · rintro st rfl
    refine ⟨by eval_expr, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp [startState])
  · intro i st _ _ hI; exact hI.2.2.2.1
  · intro i st _ _ hI
    have : st.regs 2 = l.length := hI.2.2.1
    eval_expr
  · intro i _ hi
    wram_enter
    obtain ⟨h0, h1, h2, h3, hL, hfr⟩ := hpre
    have hm : st.mem (src + i) = l[i] := by
      rw [hfr _ (by omega)]; exact hl i hi
    refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · simp
      · dsimp only
        rw [List.take_succ_eq_append_getElem hi, hm]
        have := hL.snoc l[i]
        rw [List.length_take, Nat.min_eq_left hi.le] at this
        exact this
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · exact h3
    · wram_cost
  · intro o st' h
    cases o with
    | returned u => exact h.elim
    | normal =>
      obtain ⟨_, _, _, _, hL, hfr⟩ := h
      rw [List.take_of_length_le le_rfl] at hL
      exact ⟨hL, hfr⟩
  · simp only [copyListContract]
    wram_cost

/-- The encoding of the answer, for a nonempty stack. -/
theorem encode_ofSteps {s : ℕ} {r : List (ℕ × ℕ)} (hr : r ≠ []) :
    Walk.encode (ofSteps s r) =
      [r.length + 1, s] ++ (r.map Prod.snd ++ ([r.length] ++ r.map Prod.fst)) := by
  simp [Walk.encode, ofSteps, hr]

set_option maxHeartbeats 1000000 in
/-- The tail of `writeWalkProc`, from any state with the header cells written. -/
theorem writeWalkTail_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {fList : ℕ}
    (hpl : p.procs[fList]? = some copyListBody) {s stE stY out : ℕ} {r : List (ℕ × ℕ)}
    (hw : 1 < 2 ^ w) (hwE : stE + r.length < 2 ^ w) (hwY : stY + r.length < 2 ^ w)
    (hwo : out + 2 * r.length + 3 < 2 ^ w) (hr : r ≠ [])
    (hdE : stE + r.length ≤ out ∨ out + 2 * r.length + 3 ≤ stE)
    (hdY : stY + r.length ≤ out ∨ out + 2 * r.length + 3 ≤ stY)
    {mem0 : ℕ → ℕ} {st : State} (h1 : st.regs 1 = stE) (h2 : st.regs 2 = stY)
    (h3 : st.regs 3 = r.length) (h4 : st.regs 4 = out)
    (hE : ListAt st.mem stE (r.map Prod.fst)) (hY : ListAt st.mem stY (r.map Prod.snd))
    (hm0 : st.mem out = r.length + 1) (hm1 : st.mem (out + 1) = s)
    (hfr : ∀ a, a < out ∨ out + 2 ≤ a → st.mem a = mem0 a) {k T : ℕ}
    (hT : k + 50 * r.length + 40 ≤ T) :
    ∃ o st' c, Runs w p ω (writeWalkTail fList) st o st' c ∧
      (WalkAt st'.mem out (ofSteps s r) ∧
        ∀ a, a < out ∨ out + 2 * r.length + 3 ≤ a → st'.mem a = mem0 a) ∧ k + c ≤ T := by
  have hc1 := copyList_meetsContract (p := p) hpl (src := stY) (dst := out + 2)
    (l := r.map Prod.snd) hw (by simp; omega) (by simp; omega)
  have hc2 := copyList_meetsContract (p := p) hpl (src := stE) (dst := out + 3 + r.length)
    (l := r.map Prod.fst) hw (by simp; omega) (by simp; omega)
  have ho2 : out + 2 < 2 ^ w := by omega
  have ho3 : out + 3 < 2 ^ w := by omega
  have ho2l : out + 2 + r.length < 2 ^ w := by omega
  have ho3l : out + 3 + r.length < 2 ^ w := by omega
  unfold writeWalkTail
  refine runs_seq_call_le (vs := [stY, out + 2, r.length]) hc1 (by eval_expr) ?_ ?_ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    omega
  · exact ⟨by simp, hY, by simp only [List.length_map]; omega⟩
  intro v1 mem2 pos2 hpost1
  obtain ⟨hL2, hfr2⟩ := hpost1
  simp only [List.length_map] at hfr2 hL2
  refine runs_seq_store_le (x := out + 2 + r.length) (v := r.length) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_call_le (vs := [stE, out + 3 + r.length, r.length]) hc2 (by eval_expr) ?_ ?_ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    omega
  · refine ⟨by simp, ?_, by simp only [List.length_map]; omega⟩
    refine hE.congr fun a h1 h2 => ?_
    simp only [List.length_map] at h2
    dsimp only
    rw [Function.update_of_ne (by omega), hfr2 a (by omega)]
  intro v2 mem3 pos3 hpost2
  obtain ⟨hL3, hfr3⟩ := hpost2
  simp only [List.length_map] at hfr3 hL3
  try dsimp only at hfr3 hL3
  refine runs_ret_le (by eval_expr) ⟨?_, ?_⟩ ?_
  · unfold WalkAt
    rw [encode_ofSteps hr, listAt_append, listAt_append, listAt_append]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i
      · simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hfr3 _ (by omega), Function.update_of_ne (by omega), hfr2 _ (by omega), hm0]
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        rw [hfr3 _ (by omega), Function.update_of_ne (by omega), hfr2 _ (by omega), hm1]
    · refine listAt_addr (a' := out + 2) (by simp) (hL2.congr fun a h1 h2 => ?_)
      simp only [List.length_map] at h2
      dsimp only
      rw [hfr3 a (by omega), Function.update_of_ne (by omega)]
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i
      simp only [Nat.add_zero, List.getElem_cons_zero, List.length_cons, List.length_nil,
        List.length_map]
      try dsimp only
      rw [hfr3 _ (by first | omega | (simp; omega) | simp)]
      first | (simp [Function.update_apply]; done) | (simp [Function.update_apply]; omega)
    · refine listAt_addr (a' := out + 3 + r.length) (by simp; omega) hL3
  · intro a ha
    dsimp only
    rw [hfr3 a (by omega), Function.update_of_ne (by omega), hfr2 a (by omega), hfr a (by omega)]
  · have hlen : 0 < r.length := List.length_pos_iff.mpr hr
    simp only [copyListContract, List.length_map]
    wram_cost

set_option maxHeartbeats 1000000 in
/-- The procedure writing the answer meets its contract. -/
theorem writeWalkProc_meetsContract {w : ℕ} {p : Program} {f fList : ℕ}
    (hp : p.procs[f]? = some (writeWalkProc fList))
    (hpl : p.procs[fList]? = some copyListBody) {s stE stY out : ℕ} {r : List (ℕ × ℕ)}
    (hw : 1 < 2 ^ w) (hwE : stE + r.length < 2 ^ w) (hwY : stY + r.length < 2 ^ w)
    (hwo : out + 2 * r.length + 3 < 2 ^ w) :
    MeetsContract w p f (writeWalkContract s stE stY out r) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨rfl, hE, hY, hdE, hdY⟩ := hpre
  have hws : s < 2 ^ w := hwords s (by simp)
  have ho1 : out + 1 < 2 ^ w := by omega
  have hl1 : r.length + 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold writeWalkProc
  wram_step
  · -- The empty stack: the empty walk.
    have hr : r = [] := List.eq_nil_of_length_eq_zero hcond
    subst hr
    wram_step
    wram_step
    wram_step
    wram_step
    refine runs_seq_ret_le (by eval_expr) ?_ ?_
    · simp only [writeWalkContract]
      refine ⟨?_, ?_⟩
      · simp only [WalkAt, ofSteps, ↓reduceIte, Walk.empty, Walk.encode, List.length_nil,
          List.nil_append]
        intro i hi
        simp at hi
        interval_cases i
        · simp [Function.update_apply]
        · simp [Function.update_apply]
      · intro a ha
        simp only [List.length_nil] at ha
        simp only [startState, Function.update_apply]
        split_ifs <;> omega
    · simp only [writeWalkContract]; wram_cost
  have hr : r ≠ [] := fun h => hcond (by simp [h])
  wram_step
  wram_step
  refine runs_seq_store_le (x := out + 1) (v := s) (by eval_expr) (by eval_expr) ?_
  refine writeWalkTail_runs hpl hw hwE hwY hwo hr hdE hdY (mem0 := mem) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · refine hE.congr fun a h1 h2 => ?_
    simp only [List.length_map] at h2
    simp only [startState, Function.update_apply]
    split_ifs <;> omega
  · refine hY.congr fun a h1 h2 => ?_
    simp only [List.length_map] at h2
    simp only [startState, Function.update_apply]
    split_ifs <;> omega
  · simp [startState, Function.update_apply]
  · simp [startState, Function.update_apply]
  · intro a ha
    simp only [startState, Function.update_apply]
    split_ifs <;> omega
  · simp only [writeWalkContract]
    wram_cost

end

end MinCostFlow.HierPaths
