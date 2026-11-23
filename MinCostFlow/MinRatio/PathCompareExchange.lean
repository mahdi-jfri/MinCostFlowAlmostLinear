module

public import MinCostFlow.MinRatio.PathCancelCompare
public import MinCostFlow.MinRatio.PathSwapWords
import WordRAM.Tactic

/-!
# Comparing and exchanging two route destinations

Algorithm 2 (page 29) routes the chosen circulation. For two paths
in the same component, this fragment compares their original and
exchanged lengths. It writes the two destinations only on strict
improvement.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the four lengths, limb count, two destination
addresses, and scratch heap. The return bit says whether it swapped. -/
def pathCompareExchangeBody (compare swap : ℕ) : Stmt :=
  .call 8 compare [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 7] ;;
  .cond (.reg 8)
    (.call 9 swap [.reg 5, .reg 6] ;; .ret (.reg 8))
    (.ret (.reg 8))

/-- Conditional exchange with the exact frame on the earlier cells. -/
def pathCompareExchangeContract (w h : ℕ) (ab cd ad cb : ℤ) : Contract where
  pre args mem := ∃ a b c d L i j heap, args = [a,b,c,d,L,i,j,heap] ∧
    i < heap ∧ j < heap ∧ mem i < 2 ^ w ∧ mem j < 2 ^ w ∧
    (pathCancelCompareContract w h ab cd ad cb).pre [a,b,c,d,L,heap] mem
  post args mem ret mem' := ∃ a b c d L i j heap, args = [a,b,c,d,L,i,j,heap] ∧
    ret = (if ad + cb < ab + cd then 1 else 0) ∧
    (∀ x < heap, mem' x =
      if ad + cb < ab + cd then Function.update (Function.update mem i (mem j)) j (mem i) x
      else mem x) ∧ ZeroFrom mem' (heap + 2 * L)
  cost args _ := 117 * args.getD 4 0 + 155

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The conditional exchange costs at most `117 * L + 155` steps
and uses the comparator's two scratch blocks. -/
theorem pathCompareExchange_meetsContract {w h entry compare swap : ℕ} {p : Program}
    (ab cd ad cb : ℤ) (hp : p.HasAt entry [pathCompareExchangeBody compare swap])
    (hc : MeetsContract w p compare (pathCancelCompareContract w h ab cd ad cb))
    (hs : MeetsContract w p swap (pathSwapWordsContract w)) :
    MeetsContract w p entry (pathCompareExchangeContract w h ab cd ad cb) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,b,c,d,L,i,j,heap,rfl,hi,hj,hmi,hmj,hcmp⟩ := hpre
  have hcmpWords : ∀ x ∈ [a,b,c,d,L,heap], x < 2 ^ w :=
    fun x hx => hwords x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h <;> simp [h])
  have hiw := hwords i (by simp)
  have hjw := hwords j (by simp)
  have hw : 1 < 2 ^ w := by
    obtain ⟨a',b',c',d',L',heap',_,hw,_⟩ := hcmp
    exact hw
  apply runs_start_le
  unfold pathCompareExchangeBody
  refine runs_seq_call_le hc (vs := [a,b,c,d,L,heap]) (by eval_expr) hcmpWords hcmp ?_
  intro bit mem₁ pos₁ hpost
  obtain ⟨hbit, hframe, hz⟩ := hpost
  change (∀ x < heap, mem₁ x = mem x) at hframe
  change ZeroFrom mem₁ (heap + 2 * L) at hz
  have hbitw : bit < 2 ^ w := by rw [hbit]; split <;> omega
  refine runs_cond_le (v := bit) (by eval_expr) ?_ ?_
  · intro hnonzero
    have himprove : ad + cb < ab + cd := by
      by_contra h
      exact hnonzero (hbit.trans (ite_eq_right h))
    refine runs_seq_call_le hs (vs := [i,j]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨i,j,rfl,(hframe i hi).trans_lt hmi,(hframe j hj).trans_lt hmj⟩
    · intro v mem₂ pos₂ hswap
      have he := hswap.2
      change mem₂ = Function.update (Function.update mem₁ i (mem₁ j)) j (mem₁ i) at he
      have hkeep : ∀ x, x ≠ i → x ≠ j → mem₂ x = mem₁ x := by
        intro x hxi hxj
        rw [he, Function.update_of_ne hxj, Function.update_of_ne hxi]
      refine runs_ret_le (v := bit) (by eval_expr) ?_ ?_
      · refine ⟨a,b,c,d,L,i,j,heap,rfl,hbit,?_ ,?_⟩
        · intro x hx
          change mem₂ x = (if ad + cb < ab + cd then
            Function.update (Function.update mem i (mem j)) j (mem i) x else mem x)
          rw [ite_eq_left himprove, he, hframe i hi, hframe j hj]
          by_cases hxj : x = j
          · subst x
            simp
          · rw [Function.update_of_ne hxj, Function.update_of_ne hxj]
            by_cases hxi : x = i
            · subst x
              simp
            · rw [Function.update_of_ne hxi, Function.update_of_ne hxi, hframe x hx]
        · intro x hx
          exact (hkeep x (by omega) (by omega)).trans (hz x hx)
      · simp only [pathCompareExchangeContract, pathCancelCompareContract, pathSwapWordsContract,
          List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
        omega
  · intro hzero
    have hstay : ¬ (ad + cb < ab + cd) := by
      intro h
      rw [ite_eq_left h] at hbit
      omega
    refine runs_ret_le (v := bit) (by eval_expr) ?_ ?_
    · exact ⟨a,b,c,d,L,i,j,heap,rfl,hbit,fun x hx => by rw [ite_eq_right hstay]; exact hframe x hx,hz⟩
    · simp only [pathCompareExchangeContract, pathCancelCompareContract,
        List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
      omega

/-- The conditional machine fragment implements the exact list
transition used by the indexed route history. -/
theorem pathCompareExchange_pairs {w h base i j a b c d L heap ret : ℕ}
    {ab cd ad cb : ℤ} {mem mem' : ℕ → ℕ} {paths : List (ℕ × ℕ)}
    (hi : i < paths.length) (hj : j < paths.length)
    (hspace : base + 2 * paths.length ≤ heap)
    (hp : PathPairsAt mem base paths)
    (hout : (pathCompareExchangeContract w h ab cd ad cb).post
      [a,b,c,d,L,base + 2 * i + 1,base + 2 * j + 1,heap] mem ret mem') :
    ret = (if ad + cb < ab + cd then 1 else 0) ∧
      PathPairsAt mem' base (if ad + cb < ab + cd then
        (paths.set i (paths[i].1, paths[j].2)).set j (paths[j].1, paths[i].2)
        else paths) := by
  obtain ⟨a',b',c',d',L',i',j',heap',hargs,hret,hframe,_⟩ := hout
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := hargs
  refine ⟨hret, ?_⟩
  by_cases himprove : ad + cb < ab + cd
  · simp only [ite_eq_left himprove] at hframe ⊢
    let left := base + 2 * i + 1
    let right := base + 2 * j + 1
    let swapped := Function.update (Function.update mem left (mem right)) right (mem left)
    have hswap : (pathSwapWordsContract w).post [left,right] mem 0 swapped := ⟨rfl,rfl⟩
    have htable := pathSwapWords_pairs hi hj hp hswap
    intro k hk
    have hk' : k < paths.length := by simpa only [List.length_set] using hk
    exact ⟨(hframe _ (by omega)).trans (htable k hk).1,
      (hframe _ (by omega)).trans (htable k hk).2⟩
  · simp only [ite_eq_right himprove] at hframe ⊢
    intro k hk
    exact ⟨(hframe _ (by omega)).trans (hp k hk).1, (hframe _ (by omega)).trans (hp k hk).2⟩

end MinCostFlow.MinRatio
