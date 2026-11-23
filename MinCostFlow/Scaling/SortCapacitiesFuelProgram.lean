module

public import MinCostFlow.Scaling.MergeCapacitiesProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# The bounded machine merge sort for capacity candidates

Use the model's ceiling-half split and recurse with one less depth budget.
Contiguous source views realize the two halves. Merge the sorted outputs
into fresh storage. A zero depth or a list of length at most one copies
its input. The result always occupies the last input-length words before
the returned heap, with at most one full output block per depth level.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,fuel,heap]`. -/
def sortCapacitiesFuelBody (self copy merge : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0))
    (.call 12 copy [.reg 0,.reg 1,.const 1,.reg 3] ;; .ret (.reg 12))
    (.cond (.bin .lt (.reg 1) (.const 2))
      (.call 12 copy [.reg 0,.reg 1,.const 1,.reg 3] ;; .ret (.reg 12))
      (.assign 4 (.bin .div (.bin .add (.reg 1) (.const 1)) (.const 2)) ;;
       .assign 5 (.bin .sub (.reg 2) (.const 1)) ;;
       .call 6 self [.reg 0,.reg 4,.reg 5,.reg 3] ;;
       .assign 7 (.bin .sub (.reg 6) (.reg 4)) ;;
       .assign 8 (.bin .add (.reg 0) (.reg 4)) ;;
       .assign 9 (.bin .sub (.reg 1) (.reg 4)) ;;
       .call 10 self [.reg 8,.reg 9,.reg 5,.reg 6] ;;
       .assign 11 (.bin .sub (.reg 10) (.reg 9)) ;;
       .call 12 merge [.reg 7,.reg 4,.reg 11,.reg 9,.reg 10] ;;
       .ret (.reg 12)))

/-- The sorting entry, base-case copier, and stable merge module. -/
def sortCapacitiesFuelModule (b : ℕ) : List Stmt :=
  sortCapacitiesFuelBody b (b+1) (b+2) :: unsignedScaleBody (b+1) :: mergeCapacitiesModule (b+2)

/-- The output occupies the final `count` words. Space is at most
`(fuel+1)*count`; every input successor and split constant fits. -/
def sortCapacitiesFuelContract (w fuel : ℕ) (xs : List ℕ) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ a heap,args = [a,xs.length,fuel,heap] ∧ ListAt mem a xs ∧
      a+xs.length ≤ heap ∧ (∀ x ∈ xs,x < 2^w) ∧ xs.length+1 < 2^w ∧ 2 < 2^w)
    (fun _ _ _ => True)
    (fun _ _ => 200*(sortCapacitiesFuel fuel xs).2+500)
    (fun _ _ => (fuel+1)*xs.length)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      heapArg args+xs.length ≤ ret ∧ ListAt mem' (ret-xs.length) (sortCapacitiesFuel fuel xs).1 }

/-- Sorting, copying, and merging have no random instruction. -/
theorem sortCapacitiesFuelModule_noRand (b : ℕ) : ∀ body ∈ sortCapacitiesFuelModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [sortCapacitiesFuelBody,Stmt.NoRand,and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact unsignedScaleBody_noRand _
    · exact mergeCapacitiesModule_noRand _ body hb

private theorem sortCapacitiesFuel_small_eq (fuel : ℕ) (xs : List ℕ) (hs : xs.length ≤ 1) :
    sortCapacitiesFuel (fuel+1) xs=(xs,xs.length+1) := by
  rw [sortCapacitiesFuel,ite_eq_left hs]

private theorem sortCapacitiesFuel_split_eq (fuel : ℕ) (xs : List ℕ) (hs : ¬ xs.length ≤ 1) :
    sortCapacitiesFuel (fuel+1) xs =
      let cut := (xs.length+1)/2
      let left := sortCapacitiesFuel fuel (xs.take cut)
      let right := sortCapacitiesFuel fuel (xs.drop cut)
      let merged := mergeCapacities left.1 right.1
      (merged.1,left.2+right.2+merged.2+2*xs.length+3) := by
  rw [sortCapacitiesFuel,ite_eq_right hs]

private theorem sortCapacitiesFuel_space_split (fuel l r : ℕ) :
    (fuel+1)*l+(fuel+1)*r+(l+r)=(fuel+2)*(l+r) := by ring

/-- The bounded sort computes exactly the counted model, using linear
space per depth level and a constant multiple of its model work. -/
theorem sortCapacitiesFuel_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (sortCapacitiesFuelModule b)) (fuel : ℕ) (xs : List ℕ) :
    MeetsContract w p b (sortCapacitiesFuelContract w fuel xs) := by
  have hcopy : p.HasAt (b+1) (unsignedScaleModule (b+1)) := by
    intro i hi
    have hi0 : i=0 := by change i<1 at hi; omega
    subst i
    simpa only [unsignedScaleModule,List.getElem_cons_zero,Nat.add_zero] using (hasAt_tail hp).head
  have hmerge : p.HasAt (b+2) (mergeCapacitiesModule (b+2)) := by
    simpa only [Nat.add_assoc] using hasAt_tail (hasAt_tail hp)
  induction fuel generalizing xs with
  | zero =>
    have hkC := unsignedScale_meetsContract (w := w) hcopy 1 xs
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,hat,hend,hvalues,hn,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(0+1)*xs.length < 2^w at hs
    have hh : heap < 2^w := by omega
    have hnword : xs.length < 2^w := by omega
    have ha : a < 2^w := by omega
    have hone : 1 < 2^w := by omega
    apply runs_start_le
    unfold sortCapacitiesFuelBody
    wram_step
    · refine runs_seq_call_le hkC (vs := [a,xs.length,1,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨a,heap,rfl,hat,hend,(fun x hx => ⟨hvalues x hx,by simpa only [Nat.one_mul] using hvalues x hx⟩),hone⟩,
          hz,by change heap+xs.length < 2^w; omega⟩
      · intro ret memC posC hpostC
        obtain ⟨⟨_,_,hframe,hzC,hatC⟩,hret⟩ := hpostC
        change ret=heap+xs.length at hret
        change (∀ x < heap,memC x = mem x) at hframe
        change ZeroFrom memC ret at hzC
        change ListAt memC heap (xs.map (fun x => 1*x)) at hatC
        simp only [Nat.one_mul] at hatC
        change ListAt memC heap (xs.map id) at hatC
        rw [List.map_id] at hatC
        have hr : ret < 2^w := by omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(0+1)*xs.length ∧ (∀ x < heap,memC x = mem x) ∧
            ZeroFrom memC ret ∧ True) ∧ heap+xs.length ≤ ret ∧ ListAt memC (ret-xs.length) (sortCapacitiesFuel 0 xs).1
          rw [sortCapacitiesFuel]
          refine ⟨⟨by omega,by omega,hframe,hzC,True.intro⟩,by omega,?_⟩
          have heq : ret-xs.length=heap := by omega
          simpa only [heq] using hatC
        · simp only [sortCapacitiesFuelContract,sortCapacitiesFuel,heapContract,unsignedScaleContract,
            argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
          omega
  | succ fuel ih =>
    have hkC := unsignedScale_meetsContract (w := w) hcopy 1 xs
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,hat,hend,hvalues,hn,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(fuel+2)*xs.length < 2^w at hs
    have halloc : xs.length ≤ (fuel+2)*xs.length := Nat.le_mul_of_pos_left _ (by omega)
    have hh : heap < 2^w := by omega
    have hnword : xs.length < 2^w := by omega
    have ha : a < 2^w := by omega
    have hone : 1 < 2^w := by omega
    have hfword : fuel+1 < 2^w := hwords _ (by simp)
    have hfword' : fuel < 2^w := by omega
    apply runs_start_le
    unfold sortCapacitiesFuelBody
    wram_step
    wram_step
    · have hsmall : xs.length ≤ 1 := by
        have hlt : xs.length < 2 := by simpa only [startState,List.getD_cons_succ,List.getD_cons_zero] using hcond
        omega
      refine runs_seq_call_le hkC (vs := [a,xs.length,1,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨a,heap,rfl,hat,hend,(fun x hx => ⟨hvalues x hx,by simpa only [Nat.one_mul] using hvalues x hx⟩),hone⟩,
          hz,by change heap+xs.length < 2^w; omega⟩
      · intro ret memC posC hpostC
        obtain ⟨⟨_,_,hframe,hzC,hatC⟩,hret⟩ := hpostC
        change ret=heap+xs.length at hret
        change (∀ x < heap,memC x = mem x) at hframe
        change ZeroFrom memC ret at hzC
        change ListAt memC heap (xs.map (fun x => 1*x)) at hatC
        simp only [Nat.one_mul] at hatC
        change ListAt memC heap (xs.map id) at hatC
        rw [List.map_id] at hatC
        have hr : ret < 2^w := by omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(fuel+2)*xs.length ∧ (∀ x < heap,memC x = mem x) ∧
            ZeroFrom memC ret ∧ True) ∧ heap+xs.length ≤ ret ∧
            ListAt memC (ret-xs.length) (sortCapacitiesFuel (fuel+1) xs).1
          rw [sortCapacitiesFuel_small_eq fuel xs hsmall]
          refine ⟨⟨by omega,by omega,hframe,hzC,True.intro⟩,by omega,?_⟩
          have heq : ret-xs.length=heap := by omega
          simpa only [heq] using hatC
        · simp only [sortCapacitiesFuelContract,sortCapacitiesFuel_small_eq fuel xs hsmall,
            heapContract,unsignedScaleContract,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_reg,Expr.size_const]
          omega
    · have hlarge : ¬ xs.length ≤ 1 := by
        have hnlt : ¬ xs.length < 2 := by simpa only [startState,List.getD_cons_succ,List.getD_cons_zero] using hcond
        omega
      let cut := (xs.length+1)/2
      let left := xs.take cut
      let right := xs.drop cut
      let L := (sortCapacitiesFuel fuel left).1
      let R := (sortCapacitiesFuel fuel right).1
      have hcut : cut ≤ xs.length := by dsimp only [cut]; omega
      have hleftLen : left.length=cut := by simp only [left,List.length_take,Nat.min_eq_left hcut]
      have hrightLen : right.length=xs.length-cut := by simp only [right,List.length_drop]
      have hlengths : cut+right.length=xs.length := by rw [hrightLen]; omega
      have hLLen : L.length=cut := by rw [sortCapacitiesFuel_length,hleftLen]
      have hRLen : R.length=right.length := sortCapacitiesFuel_length _ _
      have hspaceSplit : (fuel+1)*cut+(fuel+1)*right.length+xs.length=(fuel+2)*xs.length := by
        have h := sortCapacitiesFuel_space_split fuel cut right.length
        simpa only [hlengths] using h
      have hcutWord : cut < 2^w := by omega
      have hrightWord : right.length < 2^w := by omega
      have hleftSucc : left.length+1 < 2^w := by rw [hleftLen]; omega
      have hrightSucc : right.length+1 < 2^w := by rw [hrightLen]; omega
      have haCut : a+cut < 2^w := by omega
      have hleftVals : ∀ x ∈ left,x < 2^w := fun x hx => hvalues x (List.mem_of_mem_take hx)
      have hrightVals : ∀ x ∈ right,x < 2^w := fun x hx => hvalues x (List.mem_of_mem_drop hx)
      have hLVals : ∀ x ∈ L,x < 2^w := by
        intro x hx
        exact hleftVals x ((sortCapacitiesFuel_perm fuel left).mem_iff.mp hx)
      have hRVals : ∀ x ∈ R,x < 2^w := by
        intro x hx
        exact hrightVals x ((sortCapacitiesFuel_perm fuel right).mem_iff.mp hx)
      have hkLeft := ih left
      have hkRight := ih right
      have hkMerge := mergeCapacities_meetsContract (w := w) hmerge L R
      refine runs_seq_assign_le (v := cut) (by change _ = some ((xs.length+1)/2); eval_expr) ?_
      refine runs_seq_assign_le (v := fuel) (by
        conv_rhs => rw [← Nat.add_sub_cancel fuel 1]
        exact Expr.eval_sub (a := .reg 2) (b := .const 1) (x := fuel+1) (y := 1)
          (by eval_expr) (by eval_expr) hfword) ?_
      refine runs_seq_call_le hkLeft (vs := [a,cut,fuel,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨a,heap,by rw [hleftLen],hat.take cut,by rw [hleftLen]; omega,
          hleftVals,hleftSucc,hw⟩,hz,?_⟩
        change heap+(fuel+1)*left.length < 2^w
        rw [hleftLen]
        omega
      · intro leftEnd memL posL hpostL
        obtain ⟨⟨_,hleftUpper,hframeL,hzL,_⟩,hleftLower,hatL⟩ := hpostL
        change leftEnd ≤ heap+(fuel+1)*left.length at hleftUpper
        rw [hleftLen] at hleftUpper
        change heap+left.length ≤ leftEnd at hleftLower
        rw [hleftLen] at hleftLower
        change (∀ x < heap,memL x = mem x) at hframeL
        change ZeroFrom memL leftEnd at hzL
        change ListAt memL (leftEnd-left.length) L at hatL
        rw [hleftLen] at hatL
        have hleftEndWord : leftEnd < 2^w := by omega
        have hleftPtrWord : leftEnd-cut < 2^w := (Nat.sub_le _ _).trans_lt hleftEndWord
        have hrightSource : ListAt memL (a+cut) right := by
          apply (hat.drop cut).of_agree_below (h₀ := heap) _ hframeL
          rw [hrightLen]
          omega
        have hrightSpace : leftEnd+(fuel+1)*right.length < 2^w := by omega
        refine runs_seq_assign_le (v := leftEnd-cut) (by eval_expr) ?_
        refine runs_seq_assign_le (v := a+cut) (by eval_expr) ?_
        refine runs_seq_assign_le (v := right.length) ?_ ?_
        · rw [hrightLen]
          eval_expr
        · refine runs_seq_call_le hkRight (vs := [a+cut,right.length,fuel,leftEnd]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨a+cut,leftEnd,rfl,hrightSource,by rw [hrightLen]; omega,hrightVals,hrightSucc,hw⟩,hzL,hrightSpace⟩
          · intro rightEnd memR posR hpostR
            obtain ⟨⟨_,hrightUpper,hframeR,hzR,_⟩,hrightLower,hatR⟩ := hpostR
            change rightEnd ≤ leftEnd+(fuel+1)*right.length at hrightUpper
            change leftEnd+right.length ≤ rightEnd at hrightLower
            change (∀ x < leftEnd,memR x = memL x) at hframeR
            change ZeroFrom memR rightEnd at hzR
            change ListAt memR (rightEnd-right.length) R at hatR
            have hrightEndWord : rightEnd < 2^w := by omega
            have hrightPtrWord : rightEnd-right.length < 2^w := (Nat.sub_le _ _).trans_lt hrightEndWord
            have hatLR : ListAt memR (leftEnd-cut) L :=
              hatL.of_agree_below (by rw [hLLen]; omega) hframeR
            have hmergeSpace : rightEnd+(cut+right.length) < 2^w := by omega
            refine runs_seq_assign_le (v := rightEnd-right.length) (by eval_expr) ?_
            refine runs_seq_call_le hkMerge
              (vs := [leftEnd-cut,cut,rightEnd-right.length,right.length,rightEnd])
              (by eval_expr) (by wram_words) ?_ ?_
            · refine ⟨⟨leftEnd-cut,rightEnd-right.length,rightEnd,by rw [hLLen,hRLen],hatLR,hatR,?_,?_,hLVals,hRVals,by omega⟩,hzR,?_⟩
              · rw [hLLen]
                omega
              · rw [hRLen]
                omega
              · change rightEnd+(L.length+R.length) < 2^w
                rw [hLLen,hRLen]
                exact hmergeSpace
            · intro ret memM posM hpostM
              obtain ⟨⟨_,_,hframeM,hzM,hatM⟩,hret⟩ := hpostM
              change ret=rightEnd+L.length+R.length at hret
              rw [hLLen,hRLen] at hret
              change (∀ x < rightEnd,memM x = memR x) at hframeM
              change ZeroFrom memM ret at hzM
              change ListAt memM rightEnd (mergeCapacities L R).1 at hatM
              have hr : ret < 2^w := by omega
              refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
              · change (heap ≤ ret ∧ ret ≤ heap+(fuel+2)*xs.length ∧ (∀ x < heap,memM x = mem x) ∧
                  ZeroFrom memM ret ∧ True) ∧ heap+xs.length ≤ ret ∧
                  ListAt memM (ret-xs.length) (sortCapacitiesFuel (fuel+1) xs).1
                rw [sortCapacitiesFuel_split_eq fuel xs hlarge]
                refine ⟨⟨by omega,by omega,?_,hzM,True.intro⟩,by omega,?_⟩
                · intro x hx
                  exact (hframeM x (by omega)).trans ((hframeR x (by omega)).trans (hframeL x hx))
                · have heq : ret-xs.length=rightEnd := by omega
                  simpa only [heq] using hatM
              · simp only [sortCapacitiesFuelContract,mergeCapacitiesContract,heapContract,
                  sortCapacitiesFuel_split_eq fuel xs hlarge,argsSize_cons,argsSize_nil,
                  Expr.size_bin,Expr.size_reg,Expr.size_const]
                dsimp only [cut,left,right,L,R]
                omega

end MinCostFlow.Scaling.Machine
