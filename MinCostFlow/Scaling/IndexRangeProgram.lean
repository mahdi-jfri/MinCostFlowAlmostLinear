module

public import MinCostFlow.Scaling.IndexListConsProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Constructing the cycle scan's ordered candidate list

Push edge indices from `count-1` down to zero onto an immutable tail. The
result starts with the first `count` entries of `List.finRange m` in their
original order. Each push uses the shared exact two-word cons procedure,
so construction takes linear time and exactly two fresh cells per edge.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[count,tail,heap]`. -/
def indexRangeBody (self cons : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0)) (.ret (.reg 2))
    (.assign 3 (.bin .sub (.reg 0) (.const 1)) ;;
     .call 4 cons [.reg 3,.reg 1,.reg 2] ;;
     .call 5 self [.reg 3,.reg 2,.reg 4] ;;
     .ret (.reg 5))

/-- Candidate-range construction followed by immutable cons allocation. -/
def indexRangeModule (b : ℕ) : List Stmt := [indexRangeBody b (b+1),wordPairBody]

/-- The new prefix has exactly the model's increasing edge-index order. -/
def indexRangeContract (w lo m count : ℕ) (es : List (Fin m)) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ tail heap,args=[count,tail,heap] ∧ count≤m ∧
      0<heap ∧ lo≤heap ∧ IndexListAt mem lo heap tail es ∧ 2<2^w)
    (fun args _ mem' => IndexListAt mem' lo (heapArg args+2*count)
      (if count=0 then args.getD 1 0 else heapArg args+2*count-2)
      ((List.finRange m).take count++es))
    (fun _ _ => 100*count+20) (fun _ _ => 2*count)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+2*count }

/-- Range construction has no random instruction. -/
theorem indexRangeModule_noRand (b : ℕ) : ∀ body ∈ indexRangeModule b,body.NoRand := by
  simp only [indexRangeModule,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨by simp only [indexRangeBody,Stmt.NoRand,and_self],wordPairBody_noRand⟩

private theorem range_take_succ {m count : ℕ} (hc : count<m) :
    (List.finRange m).take (count+1)=(List.finRange m).take count++[⟨count,hc⟩] := by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using hc)]
  congr 2
  apply Fin.ext
  rw [List.getElem_finRange]
  rfl

/-- The procedure computes the exact increasing candidate prefix, with
linear cost, exact allocation, and preservation of all old list nodes. -/
theorem indexRange_meetsContract {w b lo m : ℕ} {p : Program}
    (hp : p.HasAt b (indexRangeModule b)) (count : ℕ) (es : List (Fin m)) :
    MeetsContract w p b (indexRangeContract w lo m count es) := by
  have hcons : p.HasAt (b+1) wordPairModule := hasAt_tail hp
  induction count generalizing es with
  | zero =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨tail,heap,rfl,_,_,_,hat,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+2*0<2^w at hs
    have hh : heap<2^w := by omega
    apply runs_start_le
    unfold indexRangeBody
    wram_step
    refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
    · change (heap≤heap ∧ heap≤heap+2*0 ∧ (∀ x<heap,mem x=mem x) ∧ ZeroFrom mem heap ∧ _ ) ∧ heap=heap+2*0
      exact ⟨⟨le_rfl,le_rfl,fun _ _ => rfl,hz,hat⟩,rfl⟩
    · simp only [indexRangeContract,heapContract,Nat.mul_zero,Nat.zero_add,Expr.size_bin,Expr.size_reg,Expr.size_const]
      omega
  | succ count ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨tail,heap,rfl,hcount,hpositive,hlo,hat,hw⟩,hz,hs⟩ := hpre
    let e : Fin m := ⟨count,by omega⟩
    have hkC := indexListCons_meetsContract (w := w) (lo := lo) hcons e es
    have hkR := ih (e::es)
    change ZeroFrom mem heap at hz
    change heap+2*(count+1)<2^w at hs
    have hh : heap<2^w := by omega
    have hh2 : heap+2<2^w := by omega
    have hcWord : count+1<2^w := hwords _ List.mem_cons_self
    have hc0 : count<2^w := by omega
    have htWord : tail<2^w := hat.pointer_le.trans_lt hh
    apply runs_start_le
    unfold indexRangeBody
    wram_step
    refine runs_seq_assign_le (v := count) (by
      conv_rhs => rw [←Nat.add_sub_cancel count 1]
      eval_expr) ?_
    refine runs_seq_call_le hkC (vs := [count,tail,heap]) (by eval_expr) (by wram_words)
      ⟨⟨tail,heap,rfl,hpositive,hlo,hat⟩,hz,hh2⟩ ?_
    intro nextHeap memC posC hpostC
    obtain ⟨⟨_,_,hframeC,hzC,hconsData⟩,hnextHeap⟩ := hpostC
    change nextHeap=heap+2 at hnextHeap
    change (∀ x<heap,memC x=mem x) at hframeC
    change ZeroFrom memC nextHeap at hzC
    change IndexListAt memC lo (heap+2) heap (e::es) at hconsData
    have hnWord : nextHeap<2^w := by omega
    refine runs_seq_call_le hkR (vs := [count,heap,nextHeap]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨heap,nextHeap,rfl,by omega,by omega,by omega,?_,hw⟩,hzC,?_⟩
      · simpa only [hnextHeap] using hconsData
      · change nextHeap+2*count<2^w
        omega
    · intro ret memR posR hpostR
      obtain ⟨⟨_,_,hframeR,hzR,hresult⟩,hret⟩ := hpostR
      change ret=nextHeap+2*count at hret
      change (∀ x<nextHeap,memR x=memC x) at hframeR
      change ZeroFrom memR ret at hzR
      change IndexListAt memR lo (nextHeap+2*count)
        (if count=0 then heap else nextHeap+2*count-2) ((List.finRange m).take count++(e::es)) at hresult
      have hr : ret<2^w := by omega
      have hdata : IndexListAt memR lo ret (ret-2) ((List.finRange m).take (count+1)++es) := by
        have hlist : (List.finRange m).take (count+1)++es=(List.finRange m).take count++(e::es) := by
          rw [range_take_succ (show count<m by omega)]
          simp only [List.append_assoc,List.singleton_append]
          rfl
        rw [hlist]
        rw [hret]
        by_cases hc : count=0
        · simp only [hc,↓reduceIte] at hresult ⊢
          simpa only [hnextHeap,Nat.mul_zero,Nat.add_zero,Nat.add_sub_cancel] using hresult
        · simpa only [hc,↓reduceIte] using hresult
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change (heap≤ret ∧ ret≤heap+2*(count+1) ∧ (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧
          IndexListAt memR lo (heap+2*(count+1)) (heap+2*(count+1)-2) ((List.finRange m).take (count+1)++es)) ∧
          ret=heap+2*(count+1)
        have heq : ret=heap+2*(count+1) := by omega
        refine ⟨⟨by omega,by omega,?_,hzR,?_⟩,heq⟩
        · intro x hx
          exact (hframeR x (by omega)).trans (hframeC x hx)
        · simpa only [heq] using hdata
      · simp only [indexRangeContract,indexListConsContract,heapContract,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega

end MinCostFlow.Scaling.Machine
