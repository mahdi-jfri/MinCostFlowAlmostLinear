module

public import MinCostFlow.MinRatio.ExplicitEdgeCount
public import MinCostFlow.Scaling.WordPairStoreProgram
import WordRAM.Tactic

/-!
# Encoding the net count of an explicit edge

Algorithm 2 (page 29) scales the circulation and adds its absolute
value to the detector. The two directional scans yield the net signed
coefficient for an explicit edge. Store it using the integer loader's
sign and magnitude layout.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Scaling.Machine

/-- Arguments are the route address, length, edge name, and output address. -/
@[expose] def explicitEdgeSignedCountBody (count store : ℕ) : Stmt :=
  .call 4 count [.reg 0, .reg 1, .reg 2, .const 1] ;;
  .call 5 count [.reg 0, .reg 1, .reg 2, .const 0] ;;
  .cond (.bin .lt (.reg 4) (.reg 5))
    (.call 6 store [.const 1, .bin .sub (.reg 5) (.reg 4), .reg 3] ;; .ret (.reg 6))
    (.call 6 store [.const 0, .bin .sub (.reg 4) (.reg 5), .reg 3] ;; .ret (.reg 6))

/-- The two output words give the exact signed count and frame all other cells. -/
@[expose] def explicitEdgeSignedCountContract (w : ℕ) (edges : List (ℕ × Bool)) (e : ℕ) :
    Contract where
  pre args mem := ∃ base dst, args = [base, edges.length, e, dst] ∧
    ExplicitEdgesAt mem base edges ∧ base + 2 * edges.length ≤ dst ∧ dst + 2 < 2 ^ w
  post args mem ret mem' := ret = heapArg args + 2 ∧
    ListAt mem' (heapArg args)
      (encodeInt ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ))) ∧
    ∀ x, x < heapArg args ∨ heapArg args + 2 ≤ x → mem' x = mem x
  cost _ _ := 68 * edges.length + 86

/-- The signed count wrapper has no random statements. -/
theorem explicitEdgeSignedCountBody_noRand (count store : ℕ) :
    (explicitEdgeSignedCountBody count store).NoRand := by
  simp [explicitEdgeSignedCountBody, Stmt.NoRand]

/-- Two scans and the sign comparison write precisely the two output words. -/
theorem explicitEdgeSignedCount_meetsContract {w entry count store : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (e : ℕ)
    (hp : p.HasAt entry [explicitEdgeSignedCountBody count store])
    (hc : ∀ dir, MeetsContract w p count (explicitEdgeCountContract w edges e dir))
    (hs : MeetsContract w p store (wordPairStoreContract w)) :
    MeetsContract w p entry (explicitEdgeSignedCountContract w edges e) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, dst, rfl, hr, hbelow, hdst⟩ := hpre
  have hb := hwords base (by simp)
  have hl := hwords edges.length (by simp)
  have he := hwords e (by simp)
  have hd := hwords dst (by simp)
  have hw : 1 < 2 ^ w := by omega
  have hz : 0 < 2 ^ w := by omega
  apply runs_start_le
  unfold explicitEdgeSignedCountBody
  refine runs_seq_call_le (hc true) (vs := [base, edges.length, e, 1])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨base, rfl, hr, by omega⟩
  · intro f mem₁ pos₁ hpost
    obtain ⟨hf, rfl⟩ := hpost
    have hfw : f < 2 ^ w := hf ▸ List.count_le_length.trans_lt hl
    refine runs_seq_call_le (hc false) (vs := [base, edges.length, e, 0])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨base, rfl, hr, by omega⟩
    · intro b mem₂ pos₂ hpost₂
      obtain ⟨hb', rfl⟩ := hpost₂
      have hbw : b < 2 ^ w := hb' ▸ List.count_le_length.trans_lt hl
      let bit : ℕ := if f < b then 1 else 0
      have hbit : bit < 2 ^ w := by dsimp [bit]; split <;> omega
      refine runs_cond_le (v := bit) (by eval_expr) ?_ ?_
      · intro hne
        have hlt : f < b := by
          by_contra hn
          exact hne (ite_eq_right hn)
        have hdiff : b - f < 2 ^ w := by omega
        refine runs_seq_call_le hs (vs := [1, b - f, dst]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨1, b - f, dst, rfl, hdst⟩
        · intro ret out pos₃ hp₃
          have hret : ret = dst + 2 := hp₃.1
          have hretw : ret < 2 ^ w := hret ▸ hdst
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · have henc := encodeInt_of_directional_counts f b
            rw [ite_eq_left hlt] at henc
            change ret = dst + 2 ∧ ListAt out dst (encodeInt ((edges.count (e, true) : ℤ) -
              (edges.count (e, false) : ℤ))) ∧ _
            rw [← hf, ← hb']
            exact ⟨hret, henc.symm ▸ hp₃.2.1, hp₃.2.2⟩
          · simp [explicitEdgeSignedCountContract, explicitEdgeCountContract, wordPairStoreContract,
              Expr.size, argsSize]
            omega
      · intro hzero
        have hle : ¬ f < b := by
          intro hlt
          have : bit = 1 := ite_eq_left hlt
          omega
        have hdiff : f - b < 2 ^ w := by omega
        refine runs_seq_call_le hs (vs := [0, f - b, dst]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨0, f - b, dst, rfl, hdst⟩
        · intro ret out pos₃ hp₃
          have hret : ret = dst + 2 := hp₃.1
          have hretw : ret < 2 ^ w := hret ▸ hdst
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · have henc := encodeInt_of_directional_counts f b
            rw [ite_eq_right hle] at henc
            change ret = dst + 2 ∧ ListAt out dst (encodeInt ((edges.count (e, true) : ℤ) -
              (edges.count (e, false) : ℤ))) ∧ _
            rw [← hf, ← hb']
            exact ⟨hret, henc.symm ▸ hp₃.2.1, hp₃.2.2⟩
          · simp [explicitEdgeSignedCountContract, explicitEdgeCountContract, wordPairStoreContract,
              Expr.size, argsSize]
            omega

/-- Return one when neither direction occurs in the supplied route prefix. -/
@[expose] def explicitEdgeAbsentBody (count : ℕ) : Stmt :=
  .call 3 count [.reg 0, .reg 1, .reg 2, .const 1] ;;
  .call 4 count [.reg 0, .reg 1, .reg 2, .const 0] ;;
  .ret (.bin .and (.bin .eq (.reg 3) (.const 0)) (.bin .eq (.reg 4) (.const 0)))

/-- The read-only absence test accepts the same layout as a directional scan. -/
@[expose] def explicitEdgeAbsentContract (w : ℕ) (edges : List (ℕ × Bool)) (e : ℕ) :
    Contract where
  pre args mem := ∃ base, args = [base, edges.length, e] ∧ ExplicitEdgesAt mem base edges ∧
    base + 2 * edges.length + 2 < 2 ^ w
  post _ mem ret mem' := ret = (if e ∉ edges.map Prod.fst then 1 else 0) ∧ mem' = mem
  cost _ _ := 68 * edges.length + 61

/-- The absence check contains no random statements. -/
theorem explicitEdgeAbsentBody_noRand (count : ℕ) : (explicitEdgeAbsentBody count).NoRand := by
  simp [explicitEdgeAbsentBody, Stmt.NoRand]

/-- The first-occurrence scan can use this test on the prefix before
the selected row. Both directional counts must be zero. -/
theorem explicitEdgeAbsent_meetsContract {w entry count : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (e : ℕ) (hp : p.HasAt entry [explicitEdgeAbsentBody count])
    (hc : ∀ dir, MeetsContract w p count (explicitEdgeCountContract w edges e dir)) :
    MeetsContract w p entry (explicitEdgeAbsentContract w edges e) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, rfl, hr, hbound⟩ := hpre
  have hb := hwords base (by simp)
  have hl := hwords edges.length (by simp)
  have he := hwords e (by simp)
  have hw : 1 < 2 ^ w := by omega
  have hz : 0 < 2 ^ w := by omega
  apply runs_start_le
  unfold explicitEdgeAbsentBody
  refine runs_seq_call_le (hc true) (vs := [base, edges.length, e, 1])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨base, rfl, hr, hbound⟩
  · intro f mem₁ pos₁ hf
    obtain ⟨hf, rfl⟩ := hf
    refine runs_seq_call_le (hc false) (vs := [base, edges.length, e, 0])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨base, rfl, hr, hbound⟩
    · intro b mem₂ pos₂ hb'
      obtain ⟨hb', rfl⟩ := hb'
      let bit : ℕ := if f = 0 ∧ b = 0 then 1 else 0
      refine runs_ret_le (v := bit) ?_ ?_ ?_
      · by_cases h₁ : f = 0 <;> by_cases h₂ : b = 0 <;>
          simp [Expr.eval, startState, Function.update_of_ne, h₁, h₂, bit, hw, hz]
      · refine ⟨?_, rfl⟩
        change bit = if e ∉ edges.map Prod.fst then 1 else 0
        simp only [bit, hf, hb', explicitEdge_counts_zero_iff]
      · simp [explicitEdgeAbsentContract, explicitEdgeCountContract, Expr.size, argsSize]
        omega

/-- Test whether a row is the first occurrence of its edge name.
The arguments are the route base and the row index. -/
@[expose] def explicitEdgeFirstBody (absent : ℕ) : Stmt :=
  .call 2 absent [.reg 0, .reg 1,
    .load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 1)))] ;;
  .ret (.reg 2)

/-- The result is one exactly when the row's name is absent from the preceding prefix. -/
@[expose] def explicitEdgeFirstContract (w : ℕ) (edges : List (ℕ × Bool)) (i : ℕ) :
    Contract where
  pre args mem := ∃ base, args = [base, i] ∧ ExplicitEdgesAt mem base edges ∧
    base + 2 * edges.length + 2 < 2 ^ w ∧
    ∃ hi : i < edges.length, edges[i].1 < 2 ^ w
  post _ mem ret mem' := ∃ hi : i < edges.length,
    ret = (if edges[i].1 ∉ (edges.take i).map Prod.fst then 1 else 0) ∧ mem' = mem
  cost _ _ := 68 * i + 78

/-- The first-occurrence test is deterministic. -/
theorem explicitEdgeFirstBody_noRand (absent : ℕ) :
    (explicitEdgeFirstBody absent).NoRand := by
  simp [explicitEdgeFirstBody, Stmt.NoRand]

/-- A single prefix test identifies the first occurrence and preserves memory. -/
theorem explicitEdgeFirst_meetsContract {w entry absent : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (i : ℕ)
    (hp : p.HasAt entry [explicitEdgeFirstBody absent])
    (ha : ∀ e, MeetsContract w p absent (explicitEdgeAbsentContract w (edges.take i) e)) :
    MeetsContract w p entry (explicitEdgeFirstContract w edges i) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, rfl, hr, hb, hi, hew⟩ := hpre
  have hbase := hwords base (by simp)
  have hiw := hwords i (by simp)
  have htwo : 2 < 2 ^ w := by omega
  have hmul : 2 * i < 2 ^ w := by omega
  have haddr : base + 2 * i < 2 ^ w := by omega
  have hread := (hr.read hi).1
  have hlen : (edges.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  apply runs_start_le
  unfold explicitEdgeFirstBody
  refine runs_seq_call_le (ha edges[i].1) (vs := [base, i, edges[i].1])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨base, by rw [hlen], hr.take i, by omega⟩
  · intro ret mem' pos' hpost
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · exact ⟨hi, hpost.1, hpost.2⟩
    · simp [explicitEdgeFirstContract, explicitEdgeAbsentContract, hlen, Expr.size, argsSize]
      omega

end MinCostFlow.MinRatio
