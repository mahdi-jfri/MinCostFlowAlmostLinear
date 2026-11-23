module

public import MinCostFlow.HierPaths.QueryProgPick

/-!
# Reading the support entry under the cursor

`GetPath(u, v)` starts from the support entries under the cursors of `u` and `v`
(`HierModel.entryAt`). The block stores each support array as three words per entry
(`entryWords`, section 9) and the cursors in section 20. The procedure `entryWordProc` returns
word `k` of the entry under the cursor of `v` (`entryWordProc_meetsContract`). When the cursor is
at the end of the array, the model's entry is the default entry `.term 0`, whose words are all
`0`, and the procedure returns `0`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Word `k` of the support entry under the cursor of `v`. -/
def HierConcrete.entryWord (x : HierConcrete) (v k : ℕ) : ℕ :=
  (entryWords (x.H.entryAt x.ms.st v)).getD k 0

/-- Word `k` of the support entry under the cursor of `v`. Registers: `0` the block `b`, `1` the
vertex `v`, `2` the word `k`. -/
def entryWordProc : Stmt :=
  -- `4`, `5`: the start and end of the words of the support array of `v` in section 9.
  .assign 3 (secExpr 9) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 3) (.bin .add (.reg 1) (.const 1)))) ;;
  -- `6`: the cursor (section 20); check that it is before the end of the array.
  .assign 6 (.load (.bin .add (secExpr 20) (.reg 1))) ;;
  .cond (.bin .lt (.reg 6) (.bin .div (.bin .sub (.reg 5) (.reg 4)) (.const 3))) .nop
    (.ret (.const 0)) ;;
  -- `7`: the number of vertices (header word 0).
  .assign 7 (.load (.bin .add (secExpr 0) (.const 0))) ;;
  .ret (.load (.bin .add
    (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 7) (.const 1))) (.reg 4))
    (.bin .add (.bin .mul (.reg 6) (.const 3)) (.reg 2))))

/-- The contract of `entryWordProc` for the block `x` at `b`. -/
def entryWordContract (x : HierConcrete) (b : ℕ) : Contract where
  pre args mem := ∃ v k, args = [b, v, k] ∧ v < x.n ∧ k < 3 ∧ ListAt mem b x.encode
  post args mem r mem' := mem' = mem ∧ ∀ v k, args = [b, v, k] → r = x.entryWord v k
  cost _ _ := 200

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

public section

theorem length_flatMap_entryWords : ∀ l : List SupportEntry,
    (l.flatMap entryWords).length = 3 * l.length
  | [] => rfl
  | a :: t => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_entryWords t]
    cases a <;> simp [entryWords] <;> ring

/-- Word `3 i + k` of the flattened array is word `k` of entry `i`. -/
theorem flatMap_entryWords_getD : ∀ (l : List SupportEntry) (i k : ℕ), k < 3 →
    (l.flatMap entryWords).getD (3 * i + k) 0 = (entryWords (l.getD i default)).getD k 0
  | [], i, k, hk => by
    have : (default : SupportEntry) = .term 0 := rfl
    simp only [List.flatMap_nil, List.getD_nil, this, entryWords]
    interval_cases k <;> rfl
  | a :: t, 0, k, hk => by
    have h3 : (entryWords a).length = 3 := by cases a <;> rfl
    rw [List.flatMap_cons, List.getD_append _ _ _ _ (by omega)]
    simp
  | a :: t, i + 1, k, hk => by
    have h3 : (entryWords a).length = 3 := by cases a <;> rfl
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by omega), h3,
      show 3 * (i + 1) + k - 3 = 3 * i + k by omega, flatMap_entryWords_getD t i k hk]
    simp

/-- The attachment `supportWalk (.onWalk c k)`, the reversed prefix of the walk of `c` with `k`
edges, is what `copyProc` writes for the first `k + 1` vertices and `k` edges of that walk, read
backwards. -/
theorem copyWalk_prefix {P : Walk} (hP : P.verts.length = P.edges.length + 1) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ P.edges.length) :
    copyWalk (P.verts.take (k + 1)) (P.edges.take k) false = (Walk.prefix P k).reverse := by
  obtain ⟨v0, t, hv⟩ : ∃ v0 t, P.verts = v0 :: t := by
    cases h : P.verts with
    | nil => rw [h] at hP; simp at hP
    | cons v0 t => exact ⟨v0, t, rfl⟩
  rw [hv] at hP
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hP
  have hne : (P.edges.zip t).take k ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_zip, List.length_nil] at this
    omega
  rw [Walk.prefix_eq]
  simp only [copyWalk, ofSteps, Walk.steps, hv, List.headD_cons, List.tail_cons,
    hne, ↓reduceIte, Bool.false_eq_true, List.take_succ_cons]
  congr 2
  · rw [List.map_take, List.map_snd_zip (by omega)]
  · rw [List.map_take, List.map_fst_zip (by omega)]

set_option maxHeartbeats 4000000 in
/-- `entryWordProc` meets its contract. -/
theorem entryWordProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some entryWordProc) {x : HierConcrete} {b : ℕ}
    (hw : b + x.encode.length < 2 ^ w) :
    MeetsContract w p f (entryWordContract x b) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨v, k, rfl, hv, hk, h⟩ := hpre
  obtain ⟨hL0, hE0⟩ := block_sec h (i := 0) (by norm_num)
  obtain ⟨hL9, hE9⟩ := block_sec h (i := 9) (by norm_num)
  obtain ⟨hL20, hE20⟩ := block_sec h (i := 20) (by norm_num)
  change ListAt mem _ x.header at hL0
  change ListAt mem _ (csrList x.n fun w => (x.H.A.C.supportArray w).flatMap entryWords) at hL9
  change ListAt mem _ (tabList x.n x.ms.st.supCur) at hL20
  change _ + x.header.length ≤ _ at hE0
  change _ + (csrList x.n fun w => (x.H.A.C.supportArray w).flatMap entryWords).length ≤ _
    at hE9
  change _ + (tabList x.n x.ms.st.supCur).length ≤ _ at hE20
  generalize hB0 : b + 25 + mem (b + 0) = B0 at hL0 hE0
  generalize hB9 : b + 25 + mem (b + 9) = B9 at hL9 hE9
  generalize hB20 : b + 25 + mem (b + 20) = B20 at hL20 hE20
  have hlen0 : x.header.length = 15 := rfl
  have hn : mem (B0 + 0) = x.n := hL0 0 (by simp [hlen0])
  simp only [tabList, List.length_map, List.length_range] at hE20
  obtain ⟨hS0, hS1, hT9, hT9e⟩ := csr_reads hL9 hv
  have hcur : mem (B20 + v) = x.ms.st.supCur v := listAt_tabList hL20 hv
  have hlenF : ((x.H.A.C.supportArray v).flatMap entryWords).length =
      3 * (x.H.A.C.supportArray v).length := length_flatMap_entryWords _
  refine runs_start_le ?_
  unfold entryWordProc secExpr startState
  wram_step
  simp only [hB9]
  wram_step
  simp only [hS0]
  wram_step
  simp only [hS1, Nat.add_sub_cancel_left, hlenF]
  wram_step
  simp only [hB20, hcur]
  -- The check that the cursor is before the end of the array.
  wram_step
  on_goal 2 =>
    simp only [Nat.add_sub_cancel_left, hlenF, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
      at hcond
    refine runs_seq_ret_le (by eval_expr) ⟨rfl, ?_⟩ ?_
    · intro v' k' he
      simp only [List.cons.injEq, true_and, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [HierConcrete.entryWord, HierModel.entryAt]
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hcond)]
      have : (default : SupportEntry) = .term 0 := rfl
      first | rfl | (rw [this]; interval_cases k <;> rfl)
    · simp only [entryWordContract]; wram_cost
  simp only [Nat.add_sub_cancel_left, hlenF, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    at hcond
  have hidx : x.ms.st.supCur v * 3 + k < ((x.H.A.C.supportArray v).flatMap entryWords).length := by
    rw [hlenF]; omega
  have hval := hT9 _ hidx
  wram_step
  wram_step
  simp only [hB0, hn]
  refine runs_ret_le (by eval_expr) ⟨rfl, ?_⟩ ?_
  · intro v' k' he
    simp only [List.cons.injEq, true_and, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [HierConcrete.entryWord, HierModel.entryAt]
    rw [← flatMap_entryWords_getD _ _ _ hk, show 3 * x.ms.st.supCur v + k =
      x.ms.st.supCur v * 3 + k by ring, List.getD_eq_getElem _ 0 hidx]
    exact hval
  · simp only [entryWordContract]; wram_cost

end

end MinCostFlow.HierPaths
