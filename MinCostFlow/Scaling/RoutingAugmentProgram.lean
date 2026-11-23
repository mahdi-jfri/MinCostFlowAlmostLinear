module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Unsigned residual augmentation arrays

The shortest-routing update adds the forward residual correction and
subtracts the reverse correction from the starting flow. This procedure
scans three unsigned arrays and writes those coordinates. A local sum
bound covers the intermediate addition. When the resulting integer is
nonnegative, the stored natural subtraction represents it exactly.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[start,forward,reverse,count,heap]`. -/
def routingAugmentBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 3) (.const 0)) (.ret (.reg 4))
    (.assign 5 (.load (.reg 0)) ;;
     .assign 6 (.load (.reg 1)) ;;
     .assign 7 (.load (.reg 2)) ;;
     .assign 8 (.bin .add (.reg 5) (.reg 6)) ;;
     .store (.reg 4) (.bin .sub (.reg 8) (.reg 7)) ;;
     .call 9 self [.bin .add (.reg 0) (.const 1),.bin .add (.reg 1) (.const 1),
       .bin .add (.reg 2) (.const 1),.bin .sub (.reg 3) (.const 1),.bin .add (.reg 4) (.const 1)] ;;
     .ret (.reg 9))

/-- A single recursive augmentation scan. -/
def routingAugmentModule (b : ℕ) : List Stmt := [routingAugmentBody b]

/-- Each triple contains the starting, forward, and reverse coordinate. -/
def routingAugmentContract (w : ℕ) (xs : List (ℕ × ℕ × ℕ)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a f r heap, args = [a,f,r,xs.length,heap] ∧
      ListAt mem a (xs.map Prod.fst) ∧ ListAt mem f (xs.map (fun x => x.2.1)) ∧
      ListAt mem r (xs.map (fun x => x.2.2)) ∧ a+xs.length ≤ heap ∧
      f+xs.length ≤ heap ∧ r+xs.length ≤ heap ∧
      (∀ x ∈ xs, x.1+x.2.1 < 2^w ∧ x.2.2 < 2^w) ∧ 1 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (xs.map (fun x => x.1+x.2.1-x.2.2)))
    (fun _ _ => 100*xs.length+20) (fun _ _ => xs.length)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+xs.length }

/-- Residual augmentation uses no random instruction. -/
theorem routingAugmentBody_noRand (b : ℕ) : (routingAugmentBody b).NoRand := by
  simp only [routingAugmentBody,Stmt.NoRand,and_self]

/-- Natural subtraction is the exact integral routing update when the
reverse correction does not exceed the starting plus forward flow. -/
theorem routingAugment_coordinate (start forward reverse : ℕ)
    (h : reverse ≤ start+forward) :
    ((start+forward-reverse : ℕ) : ℤ) = (start : ℤ)+(forward : ℤ)-(reverse : ℤ) := by
  rw [Int.ofNat_sub h,Int.natCast_add]

/-- The scan computes all augmentation coordinates with exact allocation,
linear cost, and preservation of all three source arrays. -/
theorem routingAugment_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (routingAugmentModule b)) (xs : List (ℕ × ℕ × ℕ)) :
    MeetsContract w p b (routingAugmentContract w xs) := by
  induction xs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,f,r,heap,rfl,_,_,_,_,_,_,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+0 < 2^w at hs
    have hh : heap < 2^w := by omega
    apply runs_start_le
    unfold routingAugmentBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+0 ∧ (∀ x < heap,mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [routingAugmentContract,heapContract,List.length_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | cons x xs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,f,r,heap,rfl,hat,hft,hrt,haend,hfend,hrend,hvalues,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(x::xs).length < 2^w at hs
    obtain ⟨ha,hatTail⟩ := listAt_cons.mp hat
    obtain ⟨hf,hftTail⟩ := listAt_cons.mp hft
    obtain ⟨hr,hrtTail⟩ := listAt_cons.mp hrt
    have hv := hvalues x List.mem_cons_self
    have hstart : x.1 < 2^w := by omega
    have hforward : x.2.1 < 2^w := by omega
    have hreverse : x.2.2 < 2^w := hv.2
    have hsum : x.1+x.2.1 < 2^w := hv.1
    have hresult : x.1+x.2.1-x.2.2 < 2^w := (Nat.sub_le _ _).trans_lt hsum
    have hh : heap < 2^w := by omega
    have hh1 : heap+1 < 2^w := by simp only [List.length_cons] at hs; omega
    have ha1 : a+1 < 2^w := by simp only [List.length_cons] at haend; omega
    have hf1 : f+1 < 2^w := by simp only [List.length_cons] at hfend; omega
    have hr1 : r+1 < 2^w := by simp only [List.length_cons] at hrend; omega
    have hlen := hwords (x::xs).length (by simp)
    have htailLen : xs.length < 2^w := by simp only [List.length_cons] at hlen; omega
    let memS := Function.update mem heap (x.1+x.2.1-x.2.2)
    have hzS : ZeroFrom memS (heap+1) := by
      intro z hz'
      dsimp only [memS]
      rw [Function.update_of_ne (by omega : z ≠ heap)]
      exact hz z (by omega)
    have hframeS : ∀ z < heap, memS z = mem z := by
      intro z hz'
      exact Function.update_of_ne (by omega : z ≠ heap) _ _
    apply runs_start_le
    unfold routingAugmentBody
    wram_step
    · simp at hcond
    · refine runs_seq_assign_le (v := x.1) (by eval_expr) ?_
      refine runs_seq_assign_le (v := x.2.1) (by eval_expr) ?_
      refine runs_seq_assign_le (v := x.2.2) (by eval_expr) ?_
      refine runs_seq_assign_le (v := x.1+x.2.1) (by eval_expr) ?_
      wram_step
      refine runs_seq_call_le ih (vs := [a+1,f+1,r+1,xs.length,heap+1]) ?_ (by wram_words) ?_ ?_
      · have heq : (x::xs).length-1 = xs.length := rfl
        rw [← heq]
        eval_expr
      · refine ⟨⟨a+1,f+1,r+1,heap+1,rfl,?_,?_,?_,?_,?_,?_,
          (fun z hz' => hvalues z (List.mem_cons_of_mem x hz')),hw⟩,hzS,?_⟩
        · apply hatTail.of_agree_below (h₀ := heap) _ hframeS
          simp only [List.length_map,List.length_cons] at *
          omega
        · apply hftTail.of_agree_below (h₀ := heap) _ hframeS
          simp only [List.length_map,List.length_cons] at *
          omega
        · apply hrtTail.of_agree_below (h₀ := heap) _ hframeS
          simp only [List.length_map,List.length_cons] at *
          omega
        · simp only [List.length_cons] at haend
          omega
        · simp only [List.length_cons] at hfend
          omega
        · simp only [List.length_cons] at hrend
          omega
        · change heap+1+xs.length < 2^w
          simp only [List.length_cons] at hs
          omega
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
        change ret = heap+1+xs.length at hret
        change (∀ z < heap+1,memR z = memS z) at hframeR
        change ZeroFrom memR ret at hzR
        change ListAt memR (heap+1) (xs.map (fun z => z.1+z.2.1-z.2.2)) at hatR
        have hretWord : ret < 2^w := by simp only [List.length_cons] at hs; omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(x::xs).length ∧ (∀ z < heap,memR z = mem z) ∧
            ZeroFrom memR ret ∧ ListAt memR heap ((x::xs).map (fun z => z.1+z.2.1-z.2.2))) ∧
            ret = heap+(x::xs).length
          refine ⟨⟨by omega,by simp only [List.length_cons]; omega,
            ?_,hzR,?_⟩,by simp only [List.length_cons]; omega⟩
          · intro z hz'
            exact (hframeR z (by omega)).trans (hframeS z hz')
          · apply listAt_cons.mpr
            exact ⟨(hframeR heap (by omega)).trans (Function.update_self _ _ _),hatR⟩
        · simp only [routingAugmentContract,heapContract,List.length_cons,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]; omega

end MinCostFlow.Scaling.Machine
