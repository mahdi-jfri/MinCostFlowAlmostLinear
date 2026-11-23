module

public import MinCostFlow.Scaling.SignedAddProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# One integer potential update in cost scaling

A cost round replaces each potential numerator by twice its sum with the
extracted dual label. Add the canonical signed inputs, then double the
stored magnitude. Multiplication by two preserves the sign, including the
canonical representation of zero. The result uses two fresh cells.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments are the two signed pairs and the heap. -/
def doublePotentialSumBody (add : ℕ) : Stmt :=
  .call 5 add [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4] ;;
  .store (.bin .add (.reg 4) (.const 1))
    (.bin .mul (.const 2) (.load (.bin .add (.reg 4) (.const 1)))) ;;
  .ret (.reg 5)

/-- The update entry followed by the existing signed addition module. -/
def doublePotentialSumModule (b : ℕ) : List Stmt :=
  doublePotentialSumBody (b+1) :: signedAddModule (b+1)

/-- Twice the sum of input magnitudes bounds all arithmetic. -/
def doublePotentialSumContract (w : ℕ) (x y : ℤ) : Contract :=
  let H := heapContract w
    (fun args _ => ∃ heap,args=[if x<0 then 1 else 0,x.natAbs,if y<0 then 1 else 0,y.natAbs,heap] ∧
      2*(x.natAbs+y.natAbs)<2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (encodeInt (2*(x+y))))
    (fun _ _ => 120) (fun _ _ => 2)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+2 }

/-- Potential updating uses no random instruction. -/
theorem doublePotentialSumModule_noRand (b : ℕ) : ∀ body ∈ doublePotentialSumModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [doublePotentialSumBody,Stmt.NoRand,and_self]
  · exact signedAddModule_noRand _ body hb

private theorem twice_encode (z : ℤ) : encodeInt (2*z)=[if z<0 then 1 else 0,2*z.natAbs] := by
  have hs : 2*z<0 ↔ z<0 := by omega
  simp only [encodeInt,hs,Int.natAbs_mul]
  rfl

/-- A scalar cost-potential update returns exactly `2*(x+y)` in canonical
signed form, with constant cost, two fresh cells, and the full heap frame. -/
theorem doublePotentialSum_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (doublePotentialSumModule b)) (x y : ℤ) :
    MeetsContract w p b (doublePotentialSumContract w x y) := by
  have hk := signedAdd_meetsContract (w := w) (hasAt_tail hp) x y
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap,rfl,hbudget⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+2<2^w at hs
  have hsum : x.natAbs+y.natAbs<2^w := by omega
  have hadd : (x+y).natAbs≤x.natAbs+y.natAbs := Int.natAbs_add_le _ _
  have hdouble : 2*(x+y).natAbs<2^w := (Nat.mul_le_mul_left 2 hadd).trans_lt hbudget
  have hh : heap<2^w := by omega
  have hh1 : heap+1<2^w := by omega
  have h1 : 1<2^w := by omega
  have h2 : 2<2^w := by omega
  apply runs_start_le
  unfold doublePotentialSumBody
  refine runs_seq_call_le hk (vs := [if x<0 then 1 else 0,x.natAbs,if y<0 then 1 else 0,y.natAbs,heap])
    (by eval_expr) hwords ⟨⟨heap,rfl,hsum⟩,hz,hs⟩ ?_
  intro ret memA posA hpostA
  obtain ⟨⟨_,_,hframeA,hzA,hresult⟩,hretA⟩ := hpostA
  change ret=heap+2 at hretA
  change (∀ a<heap,memA a=mem a) at hframeA
  change ZeroFrom memA ret at hzA
  change ListAt memA heap (encodeInt (x+y)) at hresult
  have hsign : memA heap=if x+y<0 then 1 else 0 := by
    simpa only [encodeInt,Nat.add_zero,List.getElem_cons_zero] using hresult 0 (by change 0<2; decide)
  have hmag : memA (heap+1)=(x+y).natAbs := by
    simpa only [encodeInt,List.getElem_cons_succ,List.getElem_cons_zero] using hresult 1 (by change 1<2; decide)
  refine runs_seq_store_le (x := heap+1) (v := 2*(x+y).natAbs) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change (heap≤ret ∧ ret≤heap+2 ∧ (∀ a<heap,Function.update memA (heap+1) (2*(x+y).natAbs) a=mem a) ∧
      ZeroFrom (Function.update memA (heap+1) (2*(x+y).natAbs)) ret ∧
      ListAt (Function.update memA (heap+1) (2*(x+y).natAbs)) heap (encodeInt (2*(x+y)))) ∧ ret=heap+2
    refine ⟨⟨by omega,by omega,?_,?_,?_⟩,hretA⟩
    · intro a ha
      rw [Function.update_of_ne (by omega : a≠heap+1)]
      exact hframeA a ha
    · intro a ha
      rw [Function.update_of_ne (by omega : a≠heap+1)]
      exact hzA a ha
    · rw [twice_encode]
      intro i hi
      have hi' : i=0 ∨ i=1 := by change i<2 at hi; omega
      rcases hi' with rfl | rfl
      · simpa only [Nat.add_zero,List.getElem_cons_zero,Function.update_of_ne (by omega : heap≠heap+1)] using hsign
      · simp only [List.getElem_cons_succ,List.getElem_cons_zero,Function.update_self]
  · simp only [doublePotentialSumContract,signedAddContract,heapContract,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    omega

/-- Every pair of integer inputs has simultaneous full potential-update
premises on an empty heap at a finite width. -/
theorem exists_doublePotentialSum_pre (x y : ℤ) :
    ∃ w,(∀ a∈[if x<0 then 1 else 0,x.natAbs,if y<0 then 1 else 0,y.natAbs,0],a<2^w) ∧
      (doublePotentialSumContract w x y).pre
        [if x<0 then 1 else 0,x.natAbs,if y<0 then 1 else 0,y.natAbs,0] (fun _ => 0) := by
  let w := 2*(x.natAbs+y.natAbs)+4
  have hw : 2*(x.natAbs+y.natAbs)+4<2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,⟨0,rfl,by omega⟩,(fun _ _ => rfl),by change 0+2<2^w; omega⟩
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> (try split) <;> omega

end MinCostFlow.Scaling.Machine
