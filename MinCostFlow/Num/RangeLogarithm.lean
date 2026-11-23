module

public import MinCostFlow.Num.NormalizedLogarithm
public import MinCostFlow.Num.LogarithmRangeError
public import MinCostFlow.Num.Less
public import MinCostFlow.Num.ShiftRight
import WordRAM.Memory

/-!
# Logarithm range-reduction program

Compare the input with one and two. Below one, double the input and subtract
the stored logarithm of two after the recursive call. Above two, halve the
input and add that constant. On `[1,2]`, use normalized series evaluation.
The constant is supplied as a block whose value is checked by the caller.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Space for at most `E` reductions and one normalized series evaluation. -/
def rangeLogarithmSpace (L P E : ℕ) : ℕ :=
  E*(3*L+1)+normalizedLogarithmSpace L (P+4)

/-- Cost of all comparisons, shifts, corrections, and the series evaluation. -/
def rangeLogarithmCost (L P E : ℕ) : ℕ :=
  (E+1)*(400*L+1000)+(P+4)*(500*L^2+2000*L+2000)+5000*L^2+10000*L+10000

/-- Arguments `[x,one,two,logTwo,L,P,E,heap]`. -/
def rangeLogarithmBody (self less left right sub add normalized : ℕ) : Stmt :=
  .call 8 less [.reg 0,.reg 1,.reg 4] ;;
  .cond (.reg 8)
    (.call 9 left [.reg 0,.reg 4,.const 1,.reg 7] ;;
     .call 10 self [.bin .sub (.reg 9) (.reg 4),.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,
       .bin .sub (.reg 6) (.const 1),.reg 9] ;;
     .call 11 sub [.bin .sub (.reg 10) (.reg 4),.reg 3,.reg 4,.reg 10] ;;
     .ret (.reg 11))
    (.call 9 less [.reg 2,.reg 0,.reg 4] ;;
     .cond (.reg 9)
       (.call 10 right [.reg 0,.reg 4,.const 1,.reg 7] ;;
        .call 11 self [.bin .sub (.reg 10) (.reg 4),.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,
          .bin .sub (.reg 6) (.const 1),.reg 10] ;;
        .call 12 add [.bin .sub (.reg 11) (.reg 4),.reg 3,.reg 4,.const 0,.reg 11] ;;
        .ret (.reg 12))
       (.call 10 normalized [.reg 0,.reg 1,.reg 4,.reg 5,
          .bin .add (.reg 5) (.const 4),.reg 7] ;;
        .ret (.reg 10)))

/-- Range reduction and all closed arithmetic modules. -/
def rangeLogarithmModule (b h : ℕ) : List Stmt :=
  [rangeLogarithmBody b (b+1) (b+4) (b+6) (b+10) (b+15) (b+16)] ++
    (lessModule (b+1) h ++ (shiftLeftModule (b+4) h ++
      (shiftRightModule (b+6) h ++ (subtractModule (b+10) h ++
        (addCarryModule (b+15) h ++ normalizedLogarithmModule (b+16) h)))))

/-- Range reduction computes its integer formula. The output is the last
`L` cells below the returned heap pointer. Unlike the normalized kernel, the
allocation may be smaller than its bound because recursion stops on `[1,2]`.
The input range is stated on integer numerators to avoid division in the
machine invariant. -/
def rangeLogarithmContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a one two c L P E heap,args=[a,one,two,c,L,P,E,heap] ∧
      h∣P ∧ 10≤P ∧ P+E+4≤h*L ∧ 2*P+9<2^w ∧
      a+L≤heap ∧ one+L≤heap ∧ two+L≤heap ∧ c+L≤heap ∧
      Valid mem a h L ∧ Valid mem one h L ∧ Valid mem two h L ∧ Valid mem c h L ∧
      intVal mem one h L=(2:ℤ)^P ∧ intVal mem two h L=2*(2:ℤ)^P ∧
      0 ≤ intVal mem c h L ∧ intVal mem c h L≤2*(2:ℤ)^P ∧
      (2:ℤ)^P≤(2:ℤ)^E*intVal mem a h L ∧
      intVal mem a h L≤(2:ℤ)^(E+1)*(2:ℤ)^P)
    (fun _ _ _ => True)
    (fun args _ => rangeLogarithmCost (args.getD 4 0) (args.getD 5 0) (args.getD 6 0))
    (fun args _ => rangeLogarithmSpace (args.getD 4 0) (args.getD 5 0) (args.getD 6 0))
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 4 0) h (args.getD 4 0) ∧
      intVal mem' (v-args.getD 4 0) h (args.getD 4 0)=
        (rangeLogInt (args.getD 5 0) (intVal mem (args.getD 3 0) h (args.getD 4 0))
          (args.getD 6 0) (intVal mem (args.getD 0 0) h (args.getD 4 0))) }

/-- The complete range-reduction module is deterministic. -/
theorem rangeLogarithmModule_noRand (b h : ℕ) : ∀ s∈rangeLogarithmModule b h,s.NoRand := by
  intro s hs
  simp only [rangeLogarithmModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hl | hleft | hright | hsub | hadd | hn
  · simp [rangeLogarithmBody,Stmt.NoRand]
  · exact lessModule_noRand _ _ _ hl
  · exact shiftLeftModule_noRand _ _ _ hleft
  · exact shiftRightModule_noRand _ _ _ hright
  · exact subtractModule_noRand _ _ _ hsub
  · have he : s=addCarryBody (b+15) h := by simpa [addCarryModule] using hadd
    subst s
    exact addCarryBody_noRand _ _
  · exact normalizedLogarithmModule_noRand _ _ _ hn

end MinCostFlow.Num
