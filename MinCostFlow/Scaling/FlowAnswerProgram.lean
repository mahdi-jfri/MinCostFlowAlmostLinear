module

public import MinCostFlow.Scaling.SignedTableLayout
public import WordRAM.CopyWords
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Writing the encoded integral-flow answer

The main statement represents a successful answer by `1` followed by one
canonical signed pair per original edge. This procedure copies the stored
integral flow and prepends that tag. It allocates `1+2*m` words, preserves
the old heap frame, leaves a zero tail, and costs at most `40*m+100`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[flow,edgeCount,heap]`. -/
def flowAnswerBody (copy : ℕ) : Stmt :=
  .call 3 copy [.reg 0, .bin .add (.reg 2) (.const 1),
    .bin .mul (.const 2) (.reg 1)] ;;
  .store (.reg 2) (.const 1) ;;
  .ret (.bin .add (.bin .add (.reg 2) (.const 1)) (.bin .mul (.const 2) (.reg 1)))

/-- Successful answer serialization and its word-copy procedure. -/
def flowAnswerModule (b : ℕ) : List Stmt := [flowAnswerBody (b + 1), copyWords]

/-- The source is the original edge-indexed signed flow table. -/
def flowAnswerContract (w : ℕ) {m : ℕ} (f : Fin m → ℤ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ src heap, args = [src, m, heap] ∧
      SignedTableAt mem src f ∧ src + 2 * m ≤ heap ∧ 2 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (1 :: (List.finRange m).flatMap (fun j => encodeInt (f j))))
    (fun _ _ => 40 * m + 100) (fun _ _ => 1 + 2 * m)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 * m }

/-- Successful answer serialization is deterministic. -/
theorem flowAnswerModule_noRand (b : ℕ) :
    ∀ body ∈ flowAnswerModule b, body.NoRand := by
  intro body hb
  simp only [flowAnswerModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [flowAnswerBody, Stmt.NoRand, and_self]
  · simp only [copyWords, forRange, forUp, Stmt.NoRand, and_self]

/-- The stored flow is serialized exactly as required by `IsCorrectAnswer`,
with explicit cost, exact space, and the usual fresh-heap frame. -/
theorem flowAnswer_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (flowAnswerModule b)) {m : ℕ} (f : Fin m → ℤ) :
    MeetsContract w p b (flowAnswerContract w f) := by
  have hcopy : p.HasAt (b + 1) [copyWords] := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [flowAnswerModule, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.add_zero] using hp 1 (by simp [flowAnswerModule])
  have hk := copyWords_meetsContract (w := w) hcopy
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨src, heap, rfl, htable, hbefore, hw⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 * m) < 2 ^ w at hspace
  have hlen : ((List.ofFn f).flatMap encodeInt).length = 2 * m := by
    rw [integers_encode_length, List.length_ofFn]
  have hs : src < 2 ^ w := by omega
  have hh : heap < 2 ^ w := by omega
  have hh1 : heap + 1 < 2 ^ w := by omega
  have h2m : 2 * m < 2 ^ w := by omega
  have hm : m < 2 ^ w := by omega
  have hend : heap + 1 + 2 * m < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold flowAnswerBody
  refine runs_seq_call_le hk (vs := [src, heap + 1, 2 * m]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨src, heap + 1, 2 * m, rfl, hone, by omega, by omega, Or.inr (by omega)⟩
  · intro _ memC posC hpostC
    obtain ⟨src', dst', len', hargs, _, hcopied, hframe⟩ := hpostC
    have hs' : src' = src := by
      have h := congrArg (fun xs : List ℕ => xs.getD 0 0) hargs
      simpa only [List.getD_cons_zero] using h.symm
    have hd' : dst' = heap + 1 := by
      have h := congrArg (fun xs : List ℕ => xs.getD 1 0) hargs
      simpa only [List.getD_cons_succ, List.getD_cons_zero] using h.symm
    have hl' : len' = 2 * m := by
      have h := congrArg (fun xs : List ℕ => xs.getD 2 0) hargs
      simpa only [List.getD_cons_succ, List.getD_cons_zero] using h.symm
    subst src'; subst dst'; subst len'
    have hblock := copyWords_listAt htable.listAt hlen hcopied
    have hzeroC : ZeroFrom memC (heap + 1 + 2 * m) := by
      intro x hx
      exact (hframe x (Or.inr hx)).trans (hzero x (by omega))
    wram_step
    refine runs_ret_le (v := heap + 1 + 2 * m) (by eval_expr) ?_ ?_
    · change (heap ≤ heap + 1 + 2 * m ∧ heap + 1 + 2 * m ≤ heap + (1 + 2 * m) ∧
        (∀ x < heap, Function.update memC heap 1 x = mem x) ∧
        ZeroFrom (Function.update memC heap 1) (heap + 1 + 2 * m) ∧
        ListAt (Function.update memC heap 1) heap
          (1 :: (List.finRange m).flatMap (fun j => encodeInt (f j)))) ∧
        heap + 1 + 2 * m = heap + 1 + 2 * m
      refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, rfl⟩
      · intro x hx
        rw [Function.update_of_ne (by omega : x ≠ heap)]
        exact hframe x (Or.inl (by omega))
      · intro x hx
        rw [Function.update_of_ne (by omega : x ≠ heap)]
        exact hzeroC x hx
      · apply listAt_cons.mpr
        refine ⟨Function.update_self _ _ _, ?_⟩
        have heq : (List.finRange m).flatMap (fun j => encodeInt (f j)) =
            (List.ofFn f).flatMap encodeInt := by
          rw [← List.flatMap_map, ← List.ofFn_eq_map]
        rw [heq]
        exact hblock.update_lt (by omega)
    · simp only [flowAnswerContract, heapContract, copyWordsContract,
        argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

/-- The serialization premises hold together for every signed flow table. -/
theorem exists_flowAnswer_pre {m : ℕ} (f : Fin m → ℤ) :
    ∃ w mem, (∀ x ∈ [0, m, 2 * m], x < 2 ^ w) ∧
      (flowAnswerContract w f).pre [0, m, 2 * m] mem := by
  obtain ⟨mem, htable, hzero⟩ := exists_signedTableAt f
  let w := 4 * m + 4
  have hw : 4 * m + 4 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, mem, ?_, ⟨0, 2 * m, rfl, htable, by omega, by omega⟩, hzero, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · change 2 * m + (1 + 2 * m) < 2 ^ w
    omega

/-- Argument `[heap]`: write the infeasibility tag and return the next cell. -/
def infeasibleAnswerBody : Stmt :=
  .store (.reg 0) (.const 0) ;; .ret (.bin .add (.reg 0) (.const 1))

/-- The infeasible answer occupies exactly one fresh cell. -/
def infeasibleAnswerContract (w : ℕ) : Contract :=
  let C := heapContract w (fun args _ => ∃ heap, args = [heap])
    (fun args _ mem' => ListAt mem' (heapArg args) [0])
    (fun _ _ => 10) (fun _ _ => 1)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 }

/-- Writing the infeasibility tag is deterministic. -/
theorem infeasibleAnswerBody_noRand : infeasibleAnswerBody.NoRand := by
  simp only [infeasibleAnswerBody, Stmt.NoRand, and_self]

/-- The failure branch writes exactly `[0]` with constant cost. -/
theorem infeasibleAnswer_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b [infeasibleAnswerBody]) :
    MeetsContract w p b (infeasibleAnswerContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 1 < 2 ^ w at hspace
  have hh : heap < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold infeasibleAnswerBody
  wram_step
  refine runs_ret_le (v := heap + 1) (by eval_expr) ?_ ?_
  · change (heap ≤ heap + 1 ∧ heap + 1 ≤ heap + 1 ∧
      (∀ x < heap, Function.update mem heap 0 x = mem x) ∧
      ZeroFrom (Function.update mem heap 0) (heap + 1) ∧
      ListAt (Function.update mem heap 0) heap [0]) ∧ heap + 1 = heap + 1
    refine ⟨⟨by omega, le_rfl, ?_, ?_, ?_⟩, rfl⟩
    · intro x hx
      exact Function.update_of_ne (by omega : x ≠ heap) _ _
    · intro x hx
      rw [Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · apply listAt_cons.mpr
      exact ⟨Function.update_self _ _ _, listAt_nil _ _⟩
  · simp only [infeasibleAnswerContract, heapContract, Expr.size_reg,
      Expr.size_const, Expr.size_bin]; omega

/-- The infeasibility writer's allocation and argument premises can hold. -/
theorem exists_infeasibleAnswer_pre :
    (infeasibleAnswerContract 2).pre [0] (fun _ => 0) := by
  exact ⟨⟨0, rfl⟩, fun _ _ => rfl, by decide⟩

end MinCostFlow.Scaling.Machine
