module

public import MinCostFlow.Scaling.CapacitySort
public import MinCostFlow.Scaling.UnsignedScaleProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# The machine program for the model's stable capacity merge

Compare the two head values and write the smaller one, taking the left
value on a tie. Recurse after advancing only that source. When a source
is empty, copy the other suffix. This follows `mergeCapacities` exactly
and charges a constant multiple of its counted comparisons and copies.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[left,leftCount,right,rightCount,heap]`. -/
def mergeCapacitiesBody (self copy : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.call 5 copy [.reg 2,.reg 3,.const 1,.reg 4] ;; .ret (.reg 5))
    (.cond (.bin .eq (.reg 3) (.const 0))
      (.call 5 copy [.reg 0,.reg 1,.const 1,.reg 4] ;; .ret (.reg 5))
      (.cond (.bin .lt (.load (.reg 2)) (.load (.reg 0)))
        (.store (.reg 4) (.load (.reg 2)) ;;
         .call 5 self [.reg 0,.reg 1,.bin .add (.reg 2) (.const 1),
           .bin .sub (.reg 3) (.const 1),.bin .add (.reg 4) (.const 1)] ;;
         .ret (.reg 5))
        (.store (.reg 4) (.load (.reg 0)) ;;
         .call 5 self [.bin .add (.reg 0) (.const 1),.bin .sub (.reg 1) (.const 1),
           .reg 2,.reg 3,.bin .add (.reg 4) (.const 1)] ;;
         .ret (.reg 5))))

/-- Stable merge and a suffix copier implemented by unsigned scaling by one. -/
def mergeCapacitiesModule (b : ℕ) : List Stmt :=
  mergeCapacitiesBody b (b+1) :: unsignedScaleModule (b+1)

/-- Both source arrays precede fresh merged output. The result follows the
counted model exactly and uses one fresh word per input entry. -/
def mergeCapacitiesContract (w : ℕ) (xs ys : List ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a b heap,args = [a,xs.length,b,ys.length,heap] ∧
      ListAt mem a xs ∧ ListAt mem b ys ∧ a+xs.length ≤ heap ∧ b+ys.length ≤ heap ∧
      (∀ x ∈ xs,x < 2^w) ∧ (∀ y ∈ ys,y < 2^w) ∧ 1 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (mergeCapacities xs ys).1)
    (fun _ _ => 100*(mergeCapacities xs ys).2+200) (fun _ _ => xs.length+ys.length)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret=heapArg args+xs.length+ys.length }

/-- Stable merge and suffix copying contain no random instruction. -/
theorem mergeCapacitiesModule_noRand (b : ℕ) : ∀ body ∈ mergeCapacitiesModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [mergeCapacitiesBody,Stmt.NoRand,and_self]
  · have he : body = unsignedScaleBody (b+1) := by simpa only [unsignedScaleModule,List.mem_singleton] using hb
    subst body
    exact unsignedScaleBody_noRand _

private theorem mergeCapacities_nil_left_eq (ys : List ℕ) : mergeCapacities [] ys=(ys,ys.length) := by
  rw [mergeCapacities]

private theorem mergeCapacities_nil_right_eq (xs : List ℕ) : mergeCapacities xs []=(xs,xs.length) := by
  cases xs <;> simp only [mergeCapacities]

private theorem mergeCapacities_cons_left_eq (x : ℕ) (xs : List ℕ) (y : ℕ) (ys : List ℕ)
    (h : x ≤ y) : mergeCapacities (x::xs) (y::ys) =
      (x::(mergeCapacities xs (y::ys)).1,5+(mergeCapacities xs (y::ys)).2) := by
  rw [mergeCapacities,ite_eq_left h]

private theorem mergeCapacities_cons_right_eq (x : ℕ) (xs : List ℕ) (y : ℕ) (ys : List ℕ)
    (h : ¬ x ≤ y) : mergeCapacities (x::xs) (y::ys) =
      (y::(mergeCapacities (x::xs) ys).1,5+(mergeCapacities (x::xs) ys).2) := by
  rw [mergeCapacities,ite_eq_right h]

/-- The machine computes the paper-model stable merge with exact allocation
and cost at most one hundred times its model counter plus 200. -/
theorem mergeCapacities_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (mergeCapacitiesModule b)) (xs ys : List ℕ) :
    MeetsContract w p b (mergeCapacitiesContract w xs ys) := by
  have hcopy := hasAt_tail hp
  induction xs,ys using mergeCapacities.induct with
  | case1 ys =>
    have hk := unsignedScale_meetsContract (w := w) hcopy 1 ys
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,src,heap,rfl,_,hat,_,hend,_,hvalues,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(0+ys.length) < 2^w at hs
    have hh : heap < 2^w := by omega
    have hsrc : src < 2^w := hwords _ (by simp)
    have hn : ys.length < 2^w := hwords _ (by simp)
    apply runs_start_le
    unfold mergeCapacitiesBody
    wram_step
    · refine runs_seq_call_le hk (vs := [src,ys.length,1,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨src,heap,rfl,hat,hend,(fun y hy => ⟨hvalues y hy,by simpa only [Nat.one_mul] using hvalues y hy⟩),hw⟩,
          hz,by change heap+ys.length < 2^w; omega⟩
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframe,hzR,hatR⟩,hret⟩ := hpostR
        change ret=heap+ys.length at hret
        change (∀ x < heap,memR x = mem x) at hframe
        change ZeroFrom memR ret at hzR
        change ListAt memR heap (ys.map (fun y => 1*y)) at hatR
        have harr : ListAt memR heap ys := by
          simp only [Nat.one_mul] at hatR
          change ListAt memR heap (ys.map id) at hatR
          rw [List.map_id] at hatR
          exact hatR
        have hr : ret < 2^w := by omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(0+ys.length) ∧ (∀ x < heap,memR x = mem x) ∧
            ZeroFrom memR ret ∧ ListAt memR heap (mergeCapacities [] ys).1) ∧ ret=heap+0+ys.length
          rw [mergeCapacities_nil_left_eq]
          exact ⟨⟨by omega,by omega,hframe,hzR,harr⟩,by omega⟩
        · simp only [mergeCapacitiesContract,mergeCapacities,heapContract,unsignedScaleContract,
            argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | case2 xs hxs =>
    have hk := unsignedScale_meetsContract (w := w) hcopy 1 xs
    have hnonempty : xs.length ≠ 0 := fun h => hxs (List.length_eq_zero_iff.mp h)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨src,a,heap,rfl,hat,_,hend,_,hvalues,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(xs.length+0) < 2^w at hs
    have hh : heap < 2^w := by omega
    have hsrc : src < 2^w := hwords _ (by simp)
    have hn : xs.length < 2^w := hwords _ (by simp)
    apply runs_start_le
    unfold mergeCapacitiesBody
    wram_step
    wram_step
    · refine runs_seq_call_le hk (vs := [src,xs.length,1,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨src,heap,rfl,hat,hend,(fun y hy => ⟨hvalues y hy,by simpa only [Nat.one_mul] using hvalues y hy⟩),hw⟩,
          hz,by change heap+xs.length < 2^w; omega⟩
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframe,hzR,hatR⟩,hret⟩ := hpostR
        change ret=heap+xs.length at hret
        change (∀ x < heap,memR x = mem x) at hframe
        change ZeroFrom memR ret at hzR
        change ListAt memR heap (xs.map (fun y => 1*y)) at hatR
        have harr : ListAt memR heap xs := by
          simp only [Nat.one_mul] at hatR
          change ListAt memR heap (xs.map id) at hatR
          rw [List.map_id] at hatR
          exact hatR
        have hr : ret < 2^w := by omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(xs.length+0) ∧ (∀ x < heap,memR x = mem x) ∧
            ZeroFrom memR ret ∧ ListAt memR heap (mergeCapacities xs []).1) ∧ ret=heap+xs.length+0
          rw [mergeCapacities_nil_right_eq]
          exact ⟨⟨by omega,by omega,hframe,hzR,harr⟩,by omega⟩
        · simp only [mergeCapacitiesContract,mergeCapacities_nil_right_eq,heapContract,unsignedScaleContract,
            argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | case3 x xs y ys hxy ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,c,heap,rfl,hatA,hatB,hendA,hendB,hvaluesA,hvaluesB,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+((x::xs).length+(y::ys).length) < 2^w at hs
    obtain ⟨ha,htailA⟩ := listAt_cons.mp hatA
    obtain ⟨hc,htailB⟩ := listAt_cons.mp hatB
    have hx : x < 2^w := hvaluesA x List.mem_cons_self
    have hy : y < 2^w := hvaluesB y List.mem_cons_self
    have hh : heap < 2^w := by omega
    have hh1 : heap+1 < 2^w := by simp only [List.length_cons] at hs; omega
    have ha1 : a+1 < 2^w := by simp only [List.length_cons] at hendA; omega
    have hc1 : c+1 < 2^w := by simp only [List.length_cons] at hendB; omega
    have ha0 : a < 2^w := by omega
    have hc0 : c < 2^w := by omega
    have hnA : (x::xs).length < 2^w := hwords _ (by simp)
    have hnB : (y::ys).length < 2^w := hwords _ (by simp)
    have htailLen : xs.length < 2^w := by simp only [List.length_cons] at hnA; omega
    let memS := Function.update mem heap x
    have hframeS : ∀ z < heap,memS z = mem z := by
      intro z hz'
      exact Function.update_of_ne (by omega : z≠heap) _ _
    have hzS : ZeroFrom memS (heap+1) := by
      intro z hz'
      dsimp only [memS]
      rw [Function.update_of_ne (by omega : z≠heap)]
      exact hz z (by omega)
    have htailAS := htailA.of_agree_below (h₀ := heap)
      (by simp only [List.length_cons] at hendA; omega) hframeS
    have hatBS := hatB.of_agree_below hendB hframeS
    apply runs_start_le
    unfold mergeCapacitiesBody
    wram_step
    · simp at hcond
    · wram_step
      · simp at hcond
      · wram_step
        · have hlt : y < x := by simpa only [startState,hc,ha] using hcond
          omega
        · refine runs_seq_store_le (x := heap) (v := x) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_call_le ih (vs := [a+1,xs.length,c,(y::ys).length,heap+1]) ?_ (by wram_words) ?_ ?_
          · have heq : (x::xs).length-1=xs.length := rfl
            rw [← heq]
            eval_expr
          · refine ⟨⟨a+1,c,heap+1,rfl,htailAS,hatBS,?_,?_,
              (fun z hz' => hvaluesA z (List.mem_cons_of_mem x hz')),hvaluesB,hw⟩,hzS,?_⟩
            · simp only [List.length_cons] at hendA
              omega
            · omega
            · change heap+1+(xs.length+(y::ys).length) < 2^w
              simp only [List.length_cons] at hs ⊢
              omega
          · intro ret memR posR hpostR
            obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
            change ret=heap+1+xs.length+(y::ys).length at hret
            simp only [List.length_cons] at hret
            change (∀ z < heap+1,memR z = memS z) at hframeR
            change ZeroFrom memR ret at hzR
            change ListAt memR (heap+1) (mergeCapacities xs (y::ys)).1 at hatR
            have hr : ret < 2^w := by simp only [List.length_cons] at hs; omega
            refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
            · change (heap ≤ ret ∧ ret ≤ heap+((x::xs).length+(y::ys).length) ∧
                (∀ z < heap,memR z = mem z) ∧ ZeroFrom memR ret ∧
                ListAt memR heap (mergeCapacities (x::xs) (y::ys)).1) ∧
                ret=heap+(x::xs).length+(y::ys).length
              rw [mergeCapacities_cons_left_eq x xs y ys hxy]
              refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
                by simp only [List.length_cons]; omega⟩
              · intro z hz'
                exact (hframeR z (by omega)).trans (hframeS z hz')
              · apply listAt_cons.mpr
                exact ⟨(hframeR heap (by omega)).trans (Function.update_self _ _ _),hatR⟩
            · simp only [mergeCapacitiesContract,heapContract,
                mergeCapacities_cons_left_eq x xs y ys hxy,List.length_cons,
                argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
              omega
  | case4 x xs y ys hxy ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,c,heap,rfl,hatA,hatB,hendA,hendB,hvaluesA,hvaluesB,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+((x::xs).length+(y::ys).length) < 2^w at hs
    obtain ⟨ha,htailA⟩ := listAt_cons.mp hatA
    obtain ⟨hc,htailB⟩ := listAt_cons.mp hatB
    have hx : x < 2^w := hvaluesA x List.mem_cons_self
    have hy : y < 2^w := hvaluesB y List.mem_cons_self
    have hh : heap < 2^w := by omega
    have hh1 : heap+1 < 2^w := by simp only [List.length_cons] at hs; omega
    have ha1 : a+1 < 2^w := by simp only [List.length_cons] at hendA; omega
    have hc1 : c+1 < 2^w := by simp only [List.length_cons] at hendB; omega
    have ha0 : a < 2^w := by omega
    have hc0 : c < 2^w := by omega
    have hnA : (x::xs).length < 2^w := hwords _ (by simp)
    have hnB : (y::ys).length < 2^w := hwords _ (by simp)
    have htailLen : ys.length < 2^w := by simp only [List.length_cons] at hnB; omega
    let memS := Function.update mem heap y
    have hframeS : ∀ z < heap,memS z = mem z := by
      intro z hz'
      exact Function.update_of_ne (by omega : z≠heap) _ _
    have hzS : ZeroFrom memS (heap+1) := by
      intro z hz'
      dsimp only [memS]
      rw [Function.update_of_ne (by omega : z≠heap)]
      exact hz z (by omega)
    have hatAS := hatA.of_agree_below hendA hframeS
    have htailBS := htailB.of_agree_below (h₀ := heap)
      (by simp only [List.length_cons] at hendB; omega) hframeS
    apply runs_start_le
    unfold mergeCapacitiesBody
    wram_step
    · simp at hcond
    · wram_step
      · simp at hcond
      · wram_step
        · refine runs_seq_store_le (x := heap) (v := y) (by eval_expr) (by eval_expr) ?_
          refine runs_seq_call_le ih (vs := [a,(x::xs).length,c+1,ys.length,heap+1]) ?_ (by wram_words) ?_ ?_
          · have heq : (y::ys).length-1=ys.length := rfl
            rw [← heq]
            eval_expr
          · refine ⟨⟨a,c+1,heap+1,rfl,hatAS,htailBS,?_,?_,
              hvaluesA,(fun z hz' => hvaluesB z (List.mem_cons_of_mem y hz')),hw⟩,hzS,?_⟩
            · omega
            · simp only [List.length_cons] at hendB
              omega
            · change heap+1+((x::xs).length+ys.length) < 2^w
              simp only [List.length_cons] at hs ⊢
              omega
          · intro ret memR posR hpostR
            obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
            change ret=heap+1+(x::xs).length+ys.length at hret
            simp only [List.length_cons] at hret
            change (∀ z < heap+1,memR z = memS z) at hframeR
            change ZeroFrom memR ret at hzR
            change ListAt memR (heap+1) (mergeCapacities (x::xs) ys).1 at hatR
            have hr : ret < 2^w := by simp only [List.length_cons] at hs; omega
            refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
            · change (heap ≤ ret ∧ ret ≤ heap+((x::xs).length+(y::ys).length) ∧
                (∀ z < heap,memR z = mem z) ∧ ZeroFrom memR ret ∧
                ListAt memR heap (mergeCapacities (x::xs) (y::ys)).1) ∧
                ret=heap+(x::xs).length+(y::ys).length
              rw [mergeCapacities_cons_right_eq x xs y ys hxy]
              refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
                by simp only [List.length_cons]; omega⟩
              · intro z hz'
                exact (hframeR z (by omega)).trans (hframeS z hz')
              · apply listAt_cons.mpr
                exact ⟨(hframeR heap (by omega)).trans (Function.update_self _ _ _),hatR⟩
            · simp only [mergeCapacitiesContract,heapContract,
                mergeCapacities_cons_right_eq x xs y ys hxy,List.length_cons,
                argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
              omega
        · have hnlt : ¬ y < x := by simpa only [startState,hc,ha] using hcond
          omega

end MinCostFlow.Scaling.Machine
