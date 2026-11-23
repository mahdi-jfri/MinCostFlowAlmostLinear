module

public import MinCostFlow.Scaling.SignedScatterProgram
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Restoring an integral flow in fresh memory

The positive-edge reduction extends its solver output by zero on removed
slots. A fresh heap already contains zeros, so its first `2*n` cells are
the canonical zero signed table. This procedure reserves those cells and
scatters the retained integer values. It allocates exactly `2*n` words and
costs at most `100*count+100`, without scanning the unused zero slots.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[indices,values,count,dimension,heap]`. -/
def restoreScatterBody (scan : ℕ) : Stmt :=
  .call 5 scan [.reg 0, .reg 1, .reg 2, .reg 4] ;;
  .ret (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 3)))

/-- Flow restoration and the ordered scatter loop. -/
def restoreScatterModule (b : ℕ) : List Stmt :=
  restoreScatterBody (b + 1) :: signedScatterModule (b + 1)

/-- The retained-index and signed-value arrays are below the fresh heap. -/
def restoreScatterContract (w : ℕ) {n : ℕ} (entries : List (Fin n × ℤ)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ keys values heap, args = [keys, values, entries.length, n, heap] ∧
      ListAt mem keys (entries.map (fun e => e.1.val)) ∧
      ListAt mem values ((entries.map Prod.snd).flatMap encodeInt) ∧
      keys + entries.length ≤ heap ∧ values + 2 * entries.length ≤ heap ∧
      (∀ e ∈ entries, e.2.natAbs < 2 ^ w) ∧ 2 < 2 ^ w)
    (fun args _ mem' => SignedTableAt mem' (heapArg args) (Scatter.write (fun _ => 0) entries))
    (fun _ _ => 100 * entries.length + 100) (fun _ _ => 2 * n)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 * n }

/-- Restoring a flow uses no random instructions. -/
theorem restoreScatterModule_noRand (b : ℕ) :
    ∀ body ∈ restoreScatterModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [restoreScatterBody, Stmt.NoRand, and_self]
  · exact signedScatterModule_noRand _ body hb

/-- Fresh zero memory realizes the zero vector in canonical signed encoding. -/
theorem signedTableAt_zero {n : ℕ} {mem : ℕ → ℕ} {heap : ℕ}
    (hzero : ZeroFrom mem heap) : SignedTableAt mem heap (fun _ : Fin n => 0) := by
  intro v i hi
  have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  rcases hi' with rfl | rfl <;> rw [hzero _ (by omega)] <;> rfl

/-- Flow restoration is exactly a zero-initialized integer scatter, with an
exact heap increment, a zero tail, and the stated linear cost. -/
theorem restoreScatter_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (restoreScatterModule b)) {n : ℕ} (entries : List (Fin n × ℤ)) :
    MeetsContract w p b (restoreScatterContract w entries) := by
  have hscan : p.HasAt (b + 1) (signedScatterModule (b + 1)) := by
    intro i hi
    have h := hp (i + 1) (by simp only [restoreScatterModule, List.length_cons]; omega)
    have hidx : b + (i + 1) = b + 1 + i := by omega
    rw [hidx] at h
    simpa only [restoreScatterModule, List.getElem_cons_succ] using h
  have hk := signedScatter_meetsContract (w := w) hscan (fun _ : Fin n => 0) entries
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨keys, values, heap, rfl, hkeys, hvalues, hkend, hvend, hmags, hw⟩,
    hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 * n < 2 ^ w at hspace
  have hh : heap < 2 ^ w := by omega
  have hn : n < 2 ^ w := by omega
  have htwon : 2 * n < 2 ^ w := by omega
  have hend : heap + 2 * n < 2 ^ w := hspace
  have hkeysWord : keys < 2 ^ w := by omega
  have hvaluesWord : values < 2 ^ w := by omega
  have hlen : entries.length < 2 ^ w := hwords _ (by simp)
  apply runs_start_le
  unfold restoreScatterBody
  refine runs_seq_call_le hk (vs := [keys, values, entries.length, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨keys, values, heap, rfl, hkeys, hvalues, signedTableAt_zero hzero,
      hkend, hvend, hspace, hmags, hw⟩
  · intro _ memS posS hpostS
    obtain ⟨_, htable, hframe⟩ := hpostS
    change SignedTableAt memS heap (Scatter.write (fun _ : Fin n => 0) entries) at htable
    change (∀ x, x < heap ∨ heap + 2 * n ≤ x → memS x = mem x) at hframe
    refine runs_ret_le (v := heap + 2 * n) (by eval_expr) ?_ ?_
    · change (heap ≤ heap + 2 * n ∧ heap + 2 * n ≤ heap + 2 * n ∧
        (∀ x < heap, memS x = mem x) ∧ ZeroFrom memS (heap + 2 * n) ∧
        SignedTableAt memS heap (Scatter.write (fun _ : Fin n => 0) entries)) ∧
        heap + 2 * n = heap + 2 * n
      refine ⟨⟨by omega, le_rfl, fun x hx => hframe x (Or.inl hx), ?_, htable⟩, rfl⟩
      intro x hx
      exact (hframe x (Or.inr hx)).trans (hzero x (by omega))
    · simp only [restoreScatterContract, heapContract, signedScatterContract,
        argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

/-- The fresh-heap contract is inhabited for every retained integer vector. -/
theorem exists_restoreScatter_pre {n : ℕ} (entries : List (Fin n × ℤ)) :
    ∃ w mem, (∀ x ∈ [0, entries.length, entries.length, n, 3 * entries.length], x < 2 ^ w) ∧
      (restoreScatterContract w entries).pre
        [0, entries.length, entries.length, n, 3 * entries.length] mem := by
  let keys := entries.map (fun e => e.1.val)
  let values := (entries.map Prod.snd).flatMap encodeInt
  let mem := initMem (keys ++ values)
  have hklen : keys.length = entries.length := List.length_map ..
  have hvlen : values.length = 2 * entries.length := by
    simp only [values, integers_encode_length, List.length_map]
  have hat := listAt_append.mp (listAt_initMem (keys ++ values))
  have hv : ListAt mem entries.length values := by
    simpa only [hklen, Nat.zero_add] using hat.2
  have hz : ZeroFrom mem (3 * entries.length) := by
    simpa only [List.length_append, hklen, hvlen,
      show entries.length + 2 * entries.length = 3 * entries.length by omega] using
      zeroFrom_initMem (keys ++ values)
  let B := (entries.map (fun e => e.2.natAbs)).foldr max 0
  have hb : ∀ e ∈ entries, e.2.natAbs ≤ B := by
    intro e he
    exact Link.elem_le_foldr_max (List.mem_map.mpr ⟨e, he, rfl⟩)
  let w := B + 3 * entries.length + 2 * n + 3
  have hw : B + 3 * entries.length + 2 * n + 3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, mem, ?_, ⟨0, entries.length, 3 * entries.length, rfl, hat.1, hv,
    by omega, by omega, ?_, by omega⟩, hz, by change 3 * entries.length + 2 * n < 2 ^ w; omega⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
  · intro e he
    have hh := hb e he
    omega

end MinCostFlow.Scaling.Machine
