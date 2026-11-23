module

public import MinCostFlow.Scaling.WordPairStoreProgram
public import MinCostFlow.Scaling.SignedTableLayout
public import MinCostFlow.Scaling.Scatter
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Scattering integral flow coordinates

The edge reductions restore retained flow values to their saved original
indices. The loop reads an index array and a signed-value array, then writes
each pair to the destination table in order. It computes `Scatter.write`,
including when an index occurs more than once, and preserves memory outside
the destination table. Its cost is at most `100*count+20`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[indices,values,count,table]`. Each value occupies two words. -/
def signedScatterBody (self pair : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
    (.call 4 pair [.load (.reg 1), .load (.bin .add (.reg 1) (.const 1)),
      .bin .add (.reg 3) (.bin .mul (.const 2) (.load (.reg 0)))] ;;
     .call 5 self [.bin .add (.reg 0) (.const 1),
       .bin .add (.reg 1) (.const 2), .bin .sub (.reg 2) (.const 1), .reg 3] ;;
     .ret (.const 0))

/-- The scatter loop and its two-cell store. -/
def signedScatterModule (b : ℕ) : List Stmt :=
  [signedScatterBody b (b + 1), wordPairBody]

/-- Both source arrays precede the destination. Only the destination can change. -/
def signedScatterContract (w : ℕ) {n : ℕ} (s : Fin n → ℤ)
    (entries : List (Fin n × ℤ)) : Contract where
  pre args mem := ∃ keys values table, args = [keys, values, entries.length, table] ∧
    ListAt mem keys (entries.map (fun e => e.1.val)) ∧
    ListAt mem values ((entries.map Prod.snd).flatMap encodeInt) ∧
    SignedTableAt mem table s ∧ keys + entries.length ≤ table ∧
    values + 2 * entries.length ≤ table ∧ table + 2 * n < 2 ^ w ∧
    (∀ e ∈ entries, e.2.natAbs < 2 ^ w) ∧ 2 < 2 ^ w
  post args mem out mem' := out = 0 ∧
    SignedTableAt mem' (args.getD 3 0) (Scatter.write s entries) ∧
    ∀ x, x < args.getD 3 0 ∨ args.getD 3 0 + 2 * n ≤ x → mem' x = mem x
  cost _ _ := 100 * entries.length + 20

/-- Scattering is deterministic. -/
theorem signedScatterModule_noRand (b : ℕ) :
    ∀ body ∈ signedScatterModule b, body.NoRand := by
  intro body hb
  simp only [signedScatterModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [signedScatterBody, Stmt.NoRand, and_self]
  · exact wordPairBody_noRand

/-- The stored signed table follows the model's ordered integer scatter,
with a frame outside the table and a linear machine cost. -/
theorem signedScatter_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (signedScatterModule b)) {n : ℕ} (s : Fin n → ℤ)
    (entries : List (Fin n × ℤ)) :
    MeetsContract w p b (signedScatterContract w s entries) := by
  have hpair : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [signedScatterModule, wordPairModule, Nat.add_zero,
      List.getElem_cons_succ, List.getElem_cons_zero] using hp 1 (by simp only [signedScatterModule, List.length_cons, List.length_nil]; omega)
  have hkP := wordPairStore_meetsContract (w := w) hpair
  induction entries generalizing s with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨keys, values, table, rfl, _, _, hs, _, _, _, _, hw⟩ := hpre
    apply runs_start_le
    unfold signedScatterBody
    wram_step
    · refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
      · exact ⟨rfl, hs, fun _ _ => rfl⟩
      · simp only [signedScatterContract, List.length_nil, Expr.size_bin,
          Expr.size_reg, Expr.size_const]; omega
    · simp at hcond
  | cons e entries ih =>
    have hkR := ih (Function.update s e.1 e.2)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨keys, values, table, rfl, hkeys, hvalues, hs, hkend, hvend,
      hspace, hmags, hw⟩ := hpre
    obtain ⟨hkey, hkeysTail⟩ := listAt_cons.mp hkeys
    obtain ⟨hvalue, hvaluesTail⟩ := listAt_append.mp hvalues
    change ListAt mem values (encodeInt e.2) at hvalue
    change ListAt mem (values + 2) ((entries.map Prod.snd).flatMap encodeInt) at hvaluesTail
    have hsign := hvalue 0 (by change 0 < 2; omega)
    have hmag := hvalue 1 (by change 1 < 2; omega)
    change mem values = (if e.2 < 0 then 1 else 0) at hsign
    change mem (values + 1) = e.2.natAbs at hmag
    have he := e.1.isLt
    have hmagWord := hmags e List.mem_cons_self
    have hsignWord : (if e.2 < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hlen : (e :: entries).length < 2 ^ w := hwords _ (by simp)
    have hcell : table + 2 * e.1.val + 2 < 2 ^ w := by omega
    have hcellword : table + 2 * e.1.val < 2 ^ w := by omega
    have hkeysWord : keys + 1 < 2 ^ w := by omega
    have hvaluesWord : values + 2 < 2 ^ w := by omega
    have htableWord : table < 2 ^ w := by omega
    apply runs_start_le
    unfold signedScatterBody
    wram_step
    · simp at hcond
    · have hlength : (e :: entries).length = entries.length + 1 := rfl
      refine runs_seq_call_le hkP
        (vs := [if e.2 < 0 then 1 else 0, e.2.natAbs, table + 2 * e.1.val])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨_, _, _, rfl, hcell⟩
      · intro next memS posS hpostS
        obtain ⟨_, hstored, hframeS⟩ := hpostS
        change ListAt memS (table + 2 * e.1.val) (encodeInt e.2) at hstored
        change (∀ x, x < table + 2 * e.1.val ∨ table + 2 * e.1.val + 2 ≤ x →
          memS x = mem x) at hframeS
        have hsS : SignedTableAt memS table (Function.update s e.1 e.2) := by
          apply hs.update e.1 e.2 (heap := table + 2 * n) le_rfl hstored
          intro x _ hx0 hx1
          apply hframeS
          omega
        have hkeysS : ListAt memS (keys + 1) (entries.map (fun e => e.1.val)) := by
          apply hkeysTail.of_agree_below (h₀ := table)
          · simp only [List.length_map, List.length_cons] at *; omega
          · intro x hx; exact hframeS x (Or.inl (by omega))
        have hvaluesS : ListAt memS (values + 2) ((entries.map Prod.snd).flatMap encodeInt) := by
          apply hvaluesTail.of_agree_below (h₀ := table)
          · simp only [integers_encode_length, List.length_map, List.length_cons] at *; omega
          · intro x hx; exact hframeS x (Or.inl (by omega))
        refine runs_seq_call_le hkR (vs := [keys + 1, values + 2, entries.length, table])
          (by
            have heq : (e :: entries).length - 1 = entries.length := rfl
            rw [← heq]
            eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨keys + 1, values + 2, table, rfl, hkeysS, hvaluesS, hsS,
            by simp only [List.length_cons] at hkend; omega,
            by simp only [List.length_cons] at hvend; omega,
            hspace, fun e' he' => hmags e' (List.mem_cons_of_mem e he'), hw⟩
        · intro out memR posR hpostR
          obtain ⟨_, hsR, hframeR⟩ := hpostR
          refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
          · change 0 = 0 ∧ SignedTableAt memR table (Scatter.write s (e :: entries)) ∧
              ∀ x, x < table ∨ table + 2 * n ≤ x → memR x = mem x
            change SignedTableAt memR table (Scatter.write (Function.update s e.1 e.2) entries) at hsR
            change (∀ x, x < table ∨ table + 2 * n ≤ x → memR x = memS x) at hframeR
            refine ⟨rfl, hsR, ?_⟩
            intro x hx
            exact (hframeR x hx).trans (hframeS x (by rcases hx with hx | hx <;> omega))
          · simp only [signedScatterContract, wordPairStoreContract, List.length_cons,
              argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_reg, Expr.size_load,
              Expr.size_const]; omega

/-- Every integer table and write list admits the scan premises together. -/
theorem exists_signedScatter_pre {n : ℕ} (s : Fin n → ℤ)
    (entries : List (Fin n × ℤ)) :
    ∃ w mem, (∀ x ∈ [0, entries.length, entries.length, 3 * entries.length], x < 2 ^ w) ∧
      (signedScatterContract w s entries).pre
        [0, entries.length, entries.length, 3 * entries.length] mem := by
  let keys := entries.map (fun e => e.1.val)
  let values := (entries.map Prod.snd).flatMap encodeInt
  let table := (List.ofFn s).flatMap encodeInt
  let mem := initMem (keys ++ (values ++ table))
  have hklen : keys.length = entries.length := List.length_map ..
  have hvlen : values.length = 2 * entries.length := by
    simp only [values, integers_encode_length, List.length_map]
  have hall := listAt_append.mp (listAt_initMem (keys ++ (values ++ table)))
  have hrest := listAt_append.mp hall.2
  have hk : ListAt mem 0 keys := hall.1
  have hv : ListAt mem entries.length values := by
    simpa only [hklen, Nat.zero_add] using hrest.1
  have ht : ListAt mem (3 * entries.length) table := by
    simpa only [hklen, hvlen, Nat.zero_add, show entries.length + 2 * entries.length =
      3 * entries.length by omega] using hrest.2
  let B := (entries.map (fun e => e.2.natAbs)).foldr max 0
  have hb : ∀ e ∈ entries, e.2.natAbs ≤ B := by
    intro e he
    exact Link.elem_le_foldr_max (List.mem_map.mpr ⟨e, he, rfl⟩)
  let w := B + 3 * entries.length + 2 * n + 3
  have hw : B + 3 * entries.length + 2 * n + 3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, mem, ?_, 0, entries.length, 3 * entries.length, rfl, hk, hv,
    signedTableAt_of_listAt s _ _ ht, by omega, by omega, by omega, ?_, by omega⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro e he
    have hh := hb e he
    omega

end MinCostFlow.Scaling.Machine
