module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Scaling a nonnegative integral flow array

The capacity-rounded solver multiplies each returned coordinate by the
shared integer rounding unit. This procedure performs those products in
a fresh unsigned array. Local product bounds cover every arithmetic step,
and the source array remains unchanged.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,multiplier,heap]`. -/
def unsignedScaleBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 3))
    (.assign 4 (.load (.reg 0)) ;;
     .assign 5 (.bin .mul (.reg 2) (.reg 4)) ;;
     .store (.reg 3) (.reg 5) ;;
     .call 6 self [.bin .add (.reg 0) (.const 1),.bin .sub (.reg 1) (.const 1),
       .reg 2,.bin .add (.reg 3) (.const 1)] ;;
     .ret (.reg 6))

/-- A single recursive unsigned scaling procedure. -/
def unsignedScaleModule (b : ℕ) : List Stmt := [unsignedScaleBody b]

/-- The source coordinates and their products fit words; the result has
exactly one fresh word per input coordinate. -/
def unsignedScaleContract (w k : ℕ) (xs : List ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ src heap,args = [src,xs.length,k,heap] ∧ ListAt mem src xs ∧
      src+xs.length ≤ heap ∧ (∀ x ∈ xs,x < 2^w ∧ k*x < 2^w) ∧ 1 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (xs.map (fun x => k*x)))
    (fun _ _ => 80*xs.length+20) (fun _ _ => xs.length)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+xs.length }

/-- Unsigned scaling has no random instruction. -/
theorem unsignedScaleBody_noRand (b : ℕ) : (unsignedScaleBody b).NoRand := by
  simp only [unsignedScaleBody,Stmt.NoRand,and_self]

/-- The machine writes exactly the scaled unsigned vector, with linear
cost, exact allocation, and preservation of all source cells. -/
theorem unsignedScale_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (unsignedScaleModule b)) (k : ℕ) (xs : List ℕ) :
    MeetsContract w p b (unsignedScaleContract w k xs) := by
  induction xs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨src,heap,rfl,_,_,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+0 < 2^w at hs
    have hh : heap < 2^w := by omega
    apply runs_start_le
    unfold unsignedScaleBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+0 ∧ (∀ x < heap,mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [unsignedScaleContract,heapContract,List.length_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | cons x xs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨src,heap,rfl,hat,hend,hvalues,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(x::xs).length < 2^w at hs
    obtain ⟨hhead,htail⟩ := listAt_cons.mp hat
    have hx := (hvalues x List.mem_cons_self).1
    have hp := (hvalues x List.mem_cons_self).2
    have hk : k < 2^w := hwords _ (by simp)
    have hlen : (x::xs).length < 2^w := hwords _ (by simp)
    have htailLen : xs.length < 2^w := by simp only [List.length_cons] at hlen; omega
    have hh : heap < 2^w := by omega
    have hh1 : heap+1 < 2^w := by simp only [List.length_cons] at hs; omega
    have hsrc1 : src+1 < 2^w := by simp only [List.length_cons] at hend; omega
    let memS := Function.update mem heap (k*x)
    have hframeS : ∀ z < heap,memS z = mem z := by
      intro z hz'
      exact Function.update_of_ne (by omega : z ≠ heap) _ _
    have hzS : ZeroFrom memS (heap+1) := by
      intro z hz'
      dsimp only [memS]
      rw [Function.update_of_ne (by omega : z ≠ heap)]
      exact hz z (by omega)
    have htailS := htail.of_agree_below (h₀ := heap)
      (by simp only [List.length_cons] at hend; omega) hframeS
    apply runs_start_le
    unfold unsignedScaleBody
    wram_step
    · simp at hcond
    · refine runs_seq_assign_le (v := x) (by eval_expr) ?_
      refine runs_seq_assign_le (v := k*x) (by eval_expr) ?_
      wram_step
      refine runs_seq_call_le ih (vs := [src+1,xs.length,k,heap+1]) ?_ (by wram_words) ?_ ?_
      · have heq : (x::xs).length-1 = xs.length := rfl
        rw [← heq]
        eval_expr
      · refine ⟨⟨src+1,heap+1,rfl,htailS,?_,
          (fun z hz' => hvalues z (List.mem_cons_of_mem x hz')),hw⟩,hzS,?_⟩
        · simp only [List.length_cons] at hend
          omega
        · change heap+1+xs.length < 2^w
          simp only [List.length_cons] at hs
          omega
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
        change ret = heap+1+xs.length at hret
        change (∀ z < heap+1,memR z = memS z) at hframeR
        change ZeroFrom memR ret at hzR
        change ListAt memR (heap+1) (xs.map (fun z => k*z)) at hatR
        have hr : ret < 2^w := by simp only [List.length_cons] at hs; omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(x::xs).length ∧ (∀ z < heap,memR z = mem z) ∧
            ZeroFrom memR ret ∧ ListAt memR heap ((x::xs).map (fun z => k*z))) ∧ ret = heap+(x::xs).length
          refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
            by simp only [List.length_cons]; omega⟩
          · intro z hz'
            exact (hframeR z (by omega)).trans (hframeS z hz')
          · apply listAt_cons.mpr
            exact ⟨(hframeR heap (by omega)).trans (Function.update_self _ _ _),hatR⟩
        · simp only [unsignedScaleContract,heapContract,List.length_cons,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]; omega

/-- Every vector and multiplier have simultaneous input and product bounds
in canonical source memory at a finite width. -/
theorem exists_unsignedScale_pre (k : ℕ) (xs : List ℕ) :
    ∃ w,(∀ x ∈ [0,xs.length,k,xs.length],x < 2^w) ∧
      (unsignedScaleContract w k xs).pre [0,xs.length,k,xs.length] (initMem xs) := by
  let products := (xs.map (fun x => k*x)).foldr max 0
  let input := xs ++ [k+products+2*xs.length+10]
  let w := wordSize 1 input
  have hw : k+products+2*xs.length+10 < 2^w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ List.mem_cons_self)
  refine ⟨w,?_,⟨0,xs.length,rfl,listAt_initMem _,by omega,?_,by omega⟩,zeroFrom_initMem _,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro x hx
    have hprod : k*x ≤ products := Link.elem_le_foldr_max (List.mem_map.mpr ⟨x,hx,rfl⟩)
    exact ⟨lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx),by omega⟩
  · change xs.length+xs.length < 2^w
    omega

end MinCostFlow.Scaling.Machine
