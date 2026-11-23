module

public import MinCostFlow.Scaling.SortCapacitiesFuelProgram
public import MinCostFlow.Scaling.ClogTwoProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# The complete deterministic sort of capacity candidates

Compute the model's depth `Nat.clog 2 (count+1)`, then invoke the proved
bounded stable merge sort. The sorted list remains in the final `count`
words before the returned heap. Its value is exactly `sortCapacities`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,heap]`. -/
def sortCapacitiesBody (log sort : ℕ) : Stmt :=
  .assign 3 (.bin .add (.reg 1) (.const 1)) ;;
  .call 4 log [.reg 3] ;;
  .call 5 sort [.reg 0,.reg 1,.reg 4,.reg 2] ;;
  .ret (.reg 5)

/-- Entry, depth computation, and bounded stable sorting. -/
def sortCapacitiesModule (b : ℕ) : List Stmt :=
  sortCapacitiesBody (b+1) (b+2) :: clogTwoBody (b+1) :: sortCapacitiesFuelModule (b+2)

/-- The model's exact sort, with an explicit cost and fresh-space bound. -/
def sortCapacitiesContract (w : ℕ) (xs : List ℕ) : Contract :=
  let fuel := Nat.clog 2 (xs.length+1)
  let H := heapContract w
    (fun args mem => ∃ a heap,args = [a,xs.length,heap] ∧ ListAt mem a xs ∧
      a+xs.length ≤ heap ∧ (∀ x ∈ xs,x < 2^w) ∧ xs.length+2 < 2^w ∧ 2 < 2^w)
    (fun _ _ _ => True)
    (fun _ _ => 200*(sortCapacities xs).2+40*fuel+700)
    (fun _ _ => (fuel+1)*xs.length)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      heapArg args+xs.length ≤ ret ∧ ListAt mem' (ret-xs.length) (sortCapacities xs).1 }

/-- Every complete sorting procedure has no random instruction. -/
theorem sortCapacitiesModule_noRand (b : ℕ) : ∀ body ∈ sortCapacitiesModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [sortCapacitiesBody,Stmt.NoRand,and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact clogTwoBody_noRand _
    · exact sortCapacitiesFuelModule_noRand _ body hb

/-- Computing the ceiling-log depth and invoking the bounded sort computes
exactly the complete model sort, with all machine operations counted. -/
theorem sortCapacities_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (sortCapacitiesModule b)) (xs : List ℕ) :
    MeetsContract w p b (sortCapacitiesContract w xs) := by
  have hlog : p.HasAt (b+1) (clogTwoModule (b+1)) := by
    intro i hi
    have hi0 : i=0 := by change i<1 at hi; omega
    subst i
    simpa only [clogTwoModule,List.getElem_cons_zero,Nat.add_zero] using (hasAt_tail hp).head
  have hsort : p.HasAt (b+2) (sortCapacitiesFuelModule (b+2)) := by
    simpa only [Nat.add_assoc] using hasAt_tail (hasAt_tail hp)
  let fuel := Nat.clog 2 (xs.length+1)
  have hkL := clogTwo_meetsContract (w := w) hlog (xs.length+1)
  have hkS := sortCapacitiesFuel_meetsContract (w := w) hsort fuel xs
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hvalues,hn,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(fuel+1)*xs.length < 2^w at hs
  have hh : heap < 2^w := by omega
  have ha : a < 2^w := by omega
  have hn1 : xs.length+1 < 2^w := by omega
  have hn0 : xs.length < 2^w := by omega
  have hone : 1 < 2^w := by omega
  have hlogBound : fuel ≤ xs.length+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hfword : fuel < 2^w := by omega
  apply runs_start_le
  unfold sortCapacitiesBody
  refine runs_seq_assign_le (v := xs.length+1) (by eval_expr) ?_
  refine runs_seq_call_le hkL (vs := [xs.length+1]) (by eval_expr) (by wram_words) ⟨rfl,hn,hw⟩ ?_
  intro fuelValue memL posL hpostL
  obtain ⟨hmem,hfuel⟩ := hpostL
  subst memL
  subst fuelValue
  refine runs_seq_call_le hkS (vs := [a,xs.length,fuel,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,heap,rfl,hat,hend,hvalues,hn1,hw⟩,hz,hs⟩
  · intro ret memS posS hpostS
    obtain ⟨⟨hlo,hhi,hframe,hzS,_⟩,hdataLower,hatS⟩ := hpostS
    change heap ≤ ret at hlo
    change ret ≤ heap+(fuel+1)*xs.length at hhi
    change (∀ x < heap,memS x = mem x) at hframe
    change ZeroFrom memS ret at hzS
    change heap+xs.length ≤ ret at hdataLower
    change ListAt memS (ret-xs.length) (sortCapacitiesFuel fuel xs).1 at hatS
    have hr : ret < 2^w := by omega
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change (heap ≤ ret ∧ ret ≤ heap+(fuel+1)*xs.length ∧ (∀ x < heap,memS x = mem x) ∧
        ZeroFrom memS ret ∧ True) ∧ heap+xs.length ≤ ret ∧ ListAt memS (ret-xs.length) (sortCapacities xs).1
      exact ⟨⟨hlo,hhi,hframe,hzS,True.intro⟩,hdataLower,hatS⟩
    · simp only [sortCapacitiesContract,sortCapacitiesFuelContract,clogTwoContract,heapContract,
        sortCapacities,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
      dsimp only [fuel]
      omega

/-- The explicit sorting cost is linear in the list size times its binary
logarithm, including constant overhead for the empty list. -/
theorem sortCapacities_cost_le (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) (xs : List ℕ) :
    (sortCapacitiesContract w xs).cost args mem ≤
      2440*(Nat.clog 2 (xs.length+1)+1)*(xs.length+1)+900 := by
  have h := sortCapacities_work xs
  change 200*(sortCapacities xs).2+40*Nat.clog 2 (xs.length+1)+700 ≤ _
  have hm := Nat.mul_le_mul_left 200 h
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_one] at hm ⊢
  omega

end MinCostFlow.Scaling.Machine
