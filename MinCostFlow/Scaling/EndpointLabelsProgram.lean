module

public import MinCostFlow.Scaling.SolverInputLayout
public import MinCostFlow.Scaling.VertexCompression
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Allocating and computing the endpoint-label table

The vertex-compression model scans all tails, then all heads. This procedure
uses fresh zero memory for the initially empty table and invokes the verified
scan twice on the original five-word edge records. It writes the number of
labels at the old heap, leaves one padding cell, and stores the labels from
`heap+2` on. Its cost is at most `160*m+200` and its space is `n+2` cells.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem scan_append {n : ℕ} (s : VertexLabels n) (xs ys : List (Fin n)) :
    s.scan (xs ++ ys) = (s.scan xs).scan ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (s.encounter x)

/-- Arguments `[inputAddress,heap]`; `scan` is the endpoint scan entry. -/
def endpointLabelsBody (scan : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.bin .add (.reg 1) (.const 2)) ;;
  .call 5 scan [.bin .add (.reg 0) (.const 2), .reg 3, .const 5, .reg 4, .const 0] ;;
  .call 6 scan [.bin .add (.reg 0) (.const 3), .reg 3, .const 5, .reg 4, .reg 5] ;;
  .store (.reg 1) (.reg 6) ;;
  .ret (.bin .add (.reg 4) (.reg 2))

/-- Label-table entry and the two endpoint scan procedures. -/
def endpointLabelsModule (b : ℕ) : List Stmt :=
  endpointLabelsBody (b + 1) :: vertexScanModule (b + 1)

/-- The label result stores its count and its vertex-indexed table. -/
def endpointLabelsContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, h] ∧ ListAt mem a J.solverWords ∧
      a + J.solverWords.length ≤ h ∧ ∀ x ∈ J.solverWords, x < 2 ^ w)
    (fun args _ mem' => mem' (heapArg args) = J.endpointLabels.count ∧
      LabelsAt mem' (heapArg args + 2) J.endpointLabels)
    (fun _ _ => 160 * J.m + 200) (fun _ _ => J.n + 2)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args + 2 + J.n }

/-- All procedures in the label-table module are deterministic. -/
theorem endpointLabelsModule_noRand (b : ℕ) : ∀ body ∈ endpointLabelsModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with he | hmem
  · subst body
    simp only [endpointLabelsBody, Stmt.NoRand, and_self]
  · exact vertexScanModule_noRand _ body hmem

/-- The two endpoint scans compute exactly `endpointLabels`, with fresh-heap
allocation, an exact returned heap pointer, and linear cost in the edges. -/
theorem endpointLabels_meetsContract {w b : ℕ} {p : Program} (hw : 8 < 2 ^ w)
    (hp : p.HasAt b (endpointLabelsModule b)) (J : Circulation) :
    MeetsContract w p b (endpointLabelsContract w J) := by
  have hscan : p.HasAt (b + 1) (vertexScanModule (b + 1)) := by
    intro i hi
    have hh := hp (i + 1) (by simpa only [endpointLabelsModule, List.length_cons] using Nat.succ_lt_succ hi)
    simpa only [endpointLabelsModule, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hh
  let tails := List.ofFn J.tail
  let heads := List.ofFn J.head
  let s0 := VertexLabels.empty J.n
  let s1 := s0.scan tails
  let s2 := s1.scan heads
  have hs0 : s0.Valid := VertexLabels.empty_valid _
  have hs1 : s1.Valid := s0.scan_valid hs0 tails
  have hlen1 : tails.length = J.m := List.length_ofFn
  have hlen2 : heads.length = J.m := List.length_ofFn
  have hc1 : s1.count ≤ J.m := by
    have hh := s0.scan_count_le tails
    change s1.count ≤ 0 + tails.length at hh
    simpa only [zero_add, hlen1] using hh
  have hc2 : s2.count ≤ 2 * J.m := by
    have hh := s1.scan_count_le heads
    change s2.count ≤ s1.count + heads.length at hh
    rw [hlen2] at hh
    omega
  have hs2 : s2 = J.endpointLabels := by
    change ((VertexLabels.empty J.n).scan (List.ofFn J.tail)).scan (List.ofFn J.head) = _
    rw [← scan_append]
    rfl
  have hk1 := vertexScan_meetsContract (by omega : 1 < 2 ^ w) hscan tails s0
  have hk2 := vertexScan_meetsContract (by omega : 1 < 2 ^ w) hscan heads s1
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hinputend, hinputwords⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (J.n + 2) < 2 ^ w at hspace
  have ha : a < 2 ^ w := hwords a (by simp)
  have hhword : heap < 2 ^ w := hwords heap (by simp)
  have hn : mem a = J.n := by
    have hh := hat 0 (by simp only [Circulation.solverWords, List.length_cons]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using hh
  have hm : mem (a + 1) = J.m := by
    have hh := hat 1 (by simp only [Circulation.solverWords, List.length_cons]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using hh
  have hnword : J.n < 2 ^ w := by omega
  have hmword : J.m < 2 ^ w := hinputwords J.m (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hinputsize := J.solverWords_length
  have h2m : 2 * J.m + 1 < 2 ^ w := by omega
  have hlabels : LabelsAt mem (heap + 2) s0 := by
    intro v
    exact hzero _ (by omega)
  have ht := solver_tails_at J mem a hat
  have hh := solver_heads_at J mem a hat
  have htailbefore : a + 2 + 5 * tails.length < heap + 2 := by rw [hlen1]; omega
  have hheadbefore : a + 3 + 5 * heads.length < heap + 2 := by rw [hlen2]; omega
  have hlabelspace : heap + 2 + J.n < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha2 : a + 2 < 2 ^ w := by omega
  have ha3 : a + 3 < 2 ^ w := by omega
  have hlabelword : heap + 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold endpointLabelsBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  wram_step
  refine runs_seq_call_le hk1 (vs := [a + 2, J.m, 5, heap + 2, 0]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨a + 2, 5, heap + 2, by rw [hlen1]; rfl, ht, hlabels, hs0,
      htailbefore, hlabelspace, by change 0 + tails.length + 1 < 2 ^ w; rw [hlen1]; omega⟩
  · intro count1 mem1 pos1 hpost1
    obtain ⟨hc1eq, htable1, hframe1⟩ := hpost1
    change count1 = s1.count at hc1eq
    change ∀ x, x < heap + 2 ∨ heap + 2 + J.n ≤ x → mem1 x = mem x at hframe1
    have hc1word : count1 < 2 ^ w := by omega
    have hhead1 : EndpointsAt mem1 (a + 3) 5 heads := by
      intro i hi
      have hindex : a + 3 + 5 * i < heap + 2 := by
        have hmul := Nat.mul_le_mul_left 5 (Nat.le_of_lt hi)
        omega
      have hf := hframe1 _ (Or.inl hindex)
      exact hf.trans (hh i hi)
    refine runs_seq_call_le hk2 (vs := [a + 3, J.m, 5, heap + 2, s1.count]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨a + 3, 5, heap + 2, by simp only [hlen2], hhead1, htable1, hs1,
        hheadbefore, hlabelspace, by rw [hlen2]; omega⟩
    · intro count2 mem2 pos2 hpost2
      obtain ⟨hc2eq, htable2, hframe2⟩ := hpost2
      change count2 = s2.count at hc2eq
      change ∀ x, x < heap + 2 ∨ heap + 2 + J.n ≤ x → mem2 x = mem1 x at hframe2
      have hc2word : count2 < 2 ^ w := by omega
      wram_step
      refine runs_ret_le (v := heap + 2 + J.n) (by eval_expr) ?_ ?_
      · change (heap ≤ heap + 2 + J.n ∧ heap + 2 + J.n ≤ heap + (J.n + 2) ∧
          (∀ x < heap, Function.update mem2 heap count2 x = mem x) ∧
          ZeroFrom (Function.update mem2 heap count2) (heap + 2 + J.n) ∧
          Function.update mem2 heap count2 heap = J.endpointLabels.count ∧
          LabelsAt (Function.update mem2 heap count2) (heap + 2) J.endpointLabels) ∧
          heap + 2 + J.n = heap + 2 + J.n
        refine ⟨⟨by omega, by omega, ?_, ?_, ?_, ?_⟩, rfl⟩
        · intro x hx
          rw [Function.update_of_ne (by omega : x ≠ heap)]
          exact (hframe2 x (Or.inl (by omega))).trans (hframe1 x (Or.inl (by omega)))
        · intro x hx
          rw [Function.update_of_ne (by omega : x ≠ heap)]
          exact (hframe2 x (Or.inr hx)).trans ((hframe1 x (Or.inr hx)).trans (hzero x (by omega)))
        · rw [Function.update_self, hc2eq, hs2]
        · intro v
          rw [Function.update_of_ne (by omega : heap + 2 + v.val ≠ heap)]
          rw [← hs2]
          exact htable2 v
      · simp only [endpointLabelsContract, heapContract, vertexScanContract,
          hlen1, hlen2, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
          argsSize_cons, argsSize_nil]
        omega

end MinCostFlow.Scaling.Machine
