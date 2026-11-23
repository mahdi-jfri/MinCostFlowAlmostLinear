module

public import MinCostFlow.HierPaths.InitProgConnLocs

/-!
# Finding a connector by its static coordinates

A pair number identifies the outer CSR row. Its two children have equal
size and the matching is perfect, so the number of records is computed
from the depth. The inner CSR lookup can then read either record boundary
without scanning the row.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments give the static block, the two exponents and powers, the
pair count and number, and a position in the matching row. -/
def initConnSeek (seek : ℕ) : Stmt :=
  .assign 8 (.bin .div (.bin .div (.reg 6) (.reg 4)) (.reg 3)) ;;
  .assign 9 (queryGroupSizeExpr (.reg 1) (.reg 2) (.bin .add (.reg 8) (.const 1))) ;;
  .call 10 seek
    [.bin .add (.bin .add (.reg 0) (.const 7)) (.load (.bin .add (.reg 0) (.const 5))),
      .reg 5, .reg 6] ;;
  .call 11 seek [.reg 10, .reg 9, .reg 7] ;;
  .ret (.reg 11)

theorem initConnSeek_noRand (seek : ℕ) : (initConnSeek seek).NoRand := by
  simp [initConnSeek, Stmt.NoRand]

/-- The location of a record or the end sentinel of the matching row. -/
def initConnAddr (S : StaticData) (mem : ℕ → ℕ) (h slot i : ℕ) : ℕ :=
  initCSRAddr
    (initCSRAddr (h + 7 + mem (h + 5)) (numPairsOf S.x S.b) (staticConnRow S) slot)
    (staticConnMatching S slot).length (staticConnRecord S slot) i

def initConnSeekContract (w : ℕ) (S : StaticData) (q : InitConnLoc) (i : ℕ) : Contract where
  pre args mem := ∃ h, args =
    [h, S.x, S.b, S.numTerm, 2 ^ S.b, numPairsOf S.x S.b, q.slot S, i] ∧
    StaticOut mem h S ∧ h + S.encode.length < 2 ^ w ∧ leafDepth S.x S.b + 1 < 2 ^ w ∧
    q ∈ initConnLocs S ∧ 0 < S.b ∧ S.H.IsValid S.x S.b ∧
    i ≤ (staticConnMatching S (q.slot S)).length
  post args mem v mem' := v = initConnAddr S mem (args.getD 0 0) (q.slot S) i ∧ mem' = mem
  cost _ _ := 80

theorem initConnSeek_meetsContract {w f seek i : ℕ} {S : StaticData} {q : InitConnLoc}
    {p : Program} (hp : p.procs[f]? = some (initConnSeek seek))
    (hs : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f (initConnSeekContract w S q i) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h, rfl, hS, hroom, hD, hq, hb, hH, hi⟩ := hpre
  let P := S.numTerm
  let B := 2 ^ S.b
  let k := numPairsOf S.x S.b
  let slot := q.slot S
  let j := q.depth
  let n := (staticConnMatching S slot).length
  let a := h + 7 + mem (h + 5)
  let inner := initCSRAddr a k (staticConnRow S) slot
  have hj : j < leafDepth S.x S.b := (initConnLoc_spec hq).1
  have hslt : slot < k := initConnLoc_slot_lt hq
  have hP : P < 2 ^ w := hw _ (by simp [P])
  have hb' : S.b < 2 ^ w := hw _ (by simp)
  have hslotW : slot < 2 ^ w := hw _ (by simp [slot])
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos S.x) hP
  have hdec : slot / B / P = j := congrArg Prod.fst (initConnLoc_pairOfIdx hq)
  have hlen : n = groupSize S.x S.b (j + 1) := initConnLoc_matching_length hq hb hH
  have hj' : j + 1 < 2 ^ w := (Nat.succ_lt_succ hj).trans hD
  have htable : ListAt mem a (csrList k (staticConnRow S)) := staticConnSection S ▸ hS.section (by decide)
  have hEnd := hS.section_end_le (i := 5) (by decide)
  rw [staticConnSection] at hEnd
  change a + (csrList k (staticConnRow S)).length ≤ _ at hEnd
  have ha : a + (csrList k (staticConnRow S)).length < 2 ^ w := hEnd.trans_lt hroom
  have hinner : inner + (csrList n (staticConnRecord S slot)).length < 2 ^ w := by
    have hh := initCSRAddr_le_end (addr := a) (f := staticConnRow S) hslt
    rw [initCSRAddr_succ, staticConnRow_eq_records] at hh
    exact hh.trans_lt ha
  have hin : ListAt mem inner (csrList n (staticConnRecord S slot)) := by
    rw [← staticConnRow_eq_records]
    exact initCSRAddr_listAt htable hslt
  refine runs_start_le ?_
  unfold initConnSeek
  refine runs_seq_assign_le (v := j) (Expr.eval_eq_of_eq
    (Expr.eval_div (Expr.eval_div (Expr.eval_reg_of_eq (v := slot) rfl)
      (Expr.eval_reg_of_eq (v := B) rfl) hslotW) (Expr.eval_reg_of_eq (v := P) rfl)
      ((Nat.div_le_self _ _).trans_lt hslotW)) hdec) ?_
  refine runs_seq_assign_le (v := n) ?_ ?_
  · rw [hlen]
    exact eval_queryGroupSizeExpr (Expr.eval_reg_of_eq (v := S.x) rfl)
      (Expr.eval_reg_of_eq (v := S.b) rfl)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := j) rfl) (Expr.eval_const h1) hj')
      hP (queryDepth_mul_lt hb hj hP hb')
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := k) (f := staticConnRow S) hs)
    (vs := [a, k, slot]) ?_ ?_ ⟨a, slot, rfl, hslt.le, htable, ha⟩ ?_
  · have ah : h + 7 ≤ a := Nat.le_add_right _ _
    have aw : a < 2 ^ w := by omega
    have h7 : h + 7 < 2 ^ w := ah.trans_lt aw
    have h5 : h + 5 < 2 ^ w := by omega
    have h7' : 7 < 2 ^ w := by omega
    have h5' : 5 < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, startState, BinOp.eval, h7, h5, h7', h5', a] at aw ⊢
    simp [aw, k, slot]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · omega
    · exact hw _ (by simp [k])
    · exact hslotW
  intro v mem₁ pos₁ hp₁
  change v = inner ∧ mem₁ = mem at hp₁
  obtain ⟨hv, hm⟩ := hp₁
  subst v mem₁
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := n)
    (f := staticConnRecord S slot) hs) (vs := [inner, n, i]) rfl ?_
    ⟨inner, i, rfl, hi, hin, hinner⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · omega
    · rw [hlen]; exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans_lt hP
    · exact hw _ (by simp)
  intro r mem₂ pos₂ hp₂
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) hp₂ ?_
  simp [initCSRSeekContract, initConnSeekContract, queryGroupSizeExpr, Expr.size, argsSize]

theorem initConnAddr_record {mem : ℕ → ℕ} {h : ℕ} {S : StaticData} {q : InitConnLoc}
    (hS : StaticOut mem h S) (hq : q ∈ initConnLocs S) :
    ListAt mem (initConnAddr S mem h (q.slot S) q.index) (connWords (q.record S)) ∧
    initConnAddr S mem h (q.slot S) (q.index + 1) =
      initConnAddr S mem h (q.slot S) q.index + (connWords (q.record S)).length ∧
    initConnAddr S mem h (q.slot S) (q.index + 1) ≤ h + S.encode.length := by
  let a := h + 7 + mem (h + 5)
  let k := numPairsOf S.x S.b
  let slot := q.slot S
  let rows := staticConnRow S
  let inner := initCSRAddr a k rows slot
  let n := (staticConnMatching S slot).length
  have hsec : ListAt mem a (csrList k rows) := staticConnSection S ▸ hS.section (by decide)
  have hInner : ListAt mem inner (csrList n (staticConnRecord S slot)) := by
    rw [← staticConnRow_eq_records]
    exact initCSRAddr_listAt hsec (initConnLoc_slot_lt hq)
  have hi : q.index < n := by
    dsimp [n, staticConnMatching, slot]
    rw [initConnLoc_pairOfIdx hq]
    exact (initConnLoc_spec hq).2.2.2.2.2
  have hf : staticConnRecord S slot q.index = connWords (q.record S) := by
    dsimp [staticConnRecord, staticConnMatching, slot, InitConnLoc.record]
    rw [initConnLoc_pairOfIdx hq]
  refine ⟨hf ▸ initCSRAddr_listAt hInner hi, ?_, ?_⟩
  · change initCSRAddr inner n (staticConnRecord S slot) (q.index + 1) = _
    rw [initCSRAddr_succ, hf]
    rfl
  · have hOut := hS.section_end_le (i := 5) (by decide)
    rw [staticConnSection] at hOut
    have he := initCSRAddr_le_end (addr := a) (f := rows) (initConnLoc_slot_lt hq)
    rw [initCSRAddr_succ] at he
    change inner + (rows slot).length ≤ _ at he
    change initCSRAddr inner n (staticConnRecord S slot) (q.index + 1) ≤ _
    exact (initCSRAddr_le_end hi).trans
      ((show inner + (csrList n (staticConnRecord S slot)).length ≤ _ from he).trans hOut)

end MinCostFlow.HierPaths

end
