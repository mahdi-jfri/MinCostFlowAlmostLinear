module

public import MinCostFlow.IPM.Machine.WideOverlay
public import MinCostFlow.IPM.Machine.WideCapacityGuard
import MinCostFlow.IPM.Machine.GuardedNarrow
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.ShiftFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Recovering and guarding a queried flow coordinate

Add the base and queried cumulative increment at twice the stored width,
then compare the true candidate with the two capacities. Rejected targets
are safe without a feasibility premise. An accepted candidate has exactly
the ordinary stored representation, without separate coordinate rounding.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[base,increment,lower,upper,L,heap]`. -/
def guardedOverlayBody (overlay guard : ℕ) : Stmt :=
  .call 6 overlay [.reg 0,.reg 1,.reg 4,.reg 5] ;;
  .call 7 guard [.bin .sub (.reg 6) (.bin .mul (.const 2) (.reg 4)),
    .reg 2,.reg 3,.reg 4,.reg 6] ;;
  .ret (.reg 7)

/-- Both complete numerical recovery and capacity-guard modules. -/
def guardedOverlayModule (b h : ℕ) : List Stmt :=
  [guardedOverlayBody (b+1) (b+7)] ++
    (wideOverlayModule (b+1) h ++ wideCapacityGuardModule (b+7) h)

/-- The true candidate is at `heap+4L`, the acceptance bit at `heap+6L`.
On acceptance the same candidate is exact in its low L limbs. -/
def guardedOverlayContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d lo up L heap,args=[a,d,lo,up,L,heap] ∧
      a+L ≤ heap ∧ d+L ≤ heap ∧ lo+L ≤ heap ∧ up+L ≤ heap ∧
      Num.Valid mem a h L ∧ Num.Valid mem d h L ∧ Num.Valid mem lo h L ∧ Num.Valid mem up h L)
    (fun args mem mem' =>
      let L := args.getD 4 0
      let heap := heapArg args
      let sum := Num.intVal mem (args.getD 0 0) h L+Num.intVal mem (args.getD 1 0) h L
      Num.Valid mem' (heap+4*L) h (2*L) ∧ Num.intVal mem' (heap+4*L) h (2*L)=sum ∧
      mem' (heap+6*L)=(if Num.intVal mem (args.getD 2 0) h L < sum ∧
        sum < Num.intVal mem (args.getD 3 0) h L then 1 else 0) ∧
      (mem' (heap+6*L)=1 → Num.Valid mem' (heap+4*L) h L ∧ Num.intVal mem' (heap+4*L) h L=sum))
    (fun args _ => 1000*args.getD 4 0+1100) (fun args _ => 1+10*args.getD 4 0)
  {C with post := fun args mem v mem' => v=heapArg args+(1+10*args.getD 4 0) ∧ C.post args mem v mem'}

/-- Every recovery, extension, comparison and output write is deterministic. -/
theorem guardedOverlayModule_noRand (b h : ℕ) :
    ∀ body ∈ guardedOverlayModule b h,body.NoRand := by
  intro body hb
  simp only [guardedOverlayModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [guardedOverlayBody,Stmt.NoRand]
  · exact wideOverlayModule_noRand _ _ _ hb
  · exact wideCapacityGuardModule_noRand _ _ _ hb

/-- Actual Query-coordinate recovery and its capacity guard, with exact
sum and accepted narrowing, explicit total cost and fixed allocation. -/
theorem guardedOverlay_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hp : p.HasAt b (guardedOverlayModule b h)) :
    MeetsContract w p b (guardedOverlayContract w h) := by
  have ht := Num.hasAt_append_right hp
  have ho : p.HasAt (b+1) (wideOverlayModule (b+1) h) := Num.hasAt_append_left ht
  have hg : p.HasAt (b+7) (wideCapacityGuardModule (b+7) h) := by
    simpa [wideOverlayModule,Num.signExtendModule,Num.isNegativeModule,
      Num.extendCopyModule,Num.addModule,Nat.add_assoc] using Num.hasAt_append_right ht
  have hoSpec := wideOverlay_meetsContract hh hw ho
  have hgSpec := wideCapacityGuard_meetsContract hh hw hg
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,d,lo,up,L,heap,rfl,haEnd,hdEnd,hloEnd,hupEnd,hva,hvd,hvlo,hvup⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(1+10*L) < 2^w at hspace
  have haW : a < 2^w := hwords _ (by simp)
  have hdW : d < 2^w := hwords _ (by simp)
  have hloW : lo < 2^w := hwords _ (by simp)
  have hupW : up < 2^w := hwords _ (by simp)
  have hLW : L < 2^w := hwords _ (by simp)
  have hhW : heap < 2^w := hwords _ (by simp)
  have h2L : 2*L < 2^w := by omega
  have htwo : 2 < 2^w := by
    have hp2 := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 2 ≤ w by omega)
    omega
  apply runs_start_le
  unfold guardedOverlayBody
  refine runs_seq_call_le hoSpec (vs:=[a,d,L,heap]) (by eval_expr) (by wram_words)
    ⟨⟨a,d,L,heap,rfl,haEnd,hdEnd,hva,hvd⟩,hz,by change heap+6*L < 2^w; omega⟩ ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨hv0,_,_,hframe0,hfresh0,hvalid0,hvalue0⟩ := hp0
  change v0=heap+6*L at hv0
  change ∀ x < heap,mem0 x=mem x at hframe0
  change Num.Valid mem0 (heap+4*L) h (2*L) at hvalid0
  change Num.intVal mem0 (heap+4*L) h (2*L)=Num.intVal mem a h L+Num.intVal mem d h L at hvalue0
  have hptr : v0-2*L=heap+4*L := by omega
  have hv0W : v0 < 2^w := by omega
  have hptrW : v0-2*L < 2^w := by omega
  have hlot := Num.IPM.valid_frozen hframe0 hloEnd hvlo
  have hupt := Num.IPM.valid_frozen hframe0 hupEnd hvup
  have hlow := Num.IPM.value_frozen (h:=h) hframe0 hloEnd
  have hupp := Num.IPM.value_frozen (h:=h) hframe0 hupEnd
  refine runs_seq_call_le hgSpec (vs:=[v0-2*L,lo,up,L,v0]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨v0-2*L,lo,up,L,v0,rfl,by omega,by omega,by omega,hptr.symm ▸ hvalid0,hlot,hupt⟩,
      hfresh0,by change v0+(1+4*L) < 2^w; omega⟩
  · intro v1 mem1 pos1 hp1
    obtain ⟨hv1,_,_,hframe1,hfresh1,hflag⟩ := hp1
    change v1=v0+(1+4*L) at hv1
    change ∀ x < v0,mem1 x=mem0 x at hframe1
    change mem1 v0=if Num.intVal mem0 lo h L < Num.intVal mem0 (v0-2*L) h (2*L) ∧
      Num.intVal mem0 (v0-2*L) h (2*L) < Num.intVal mem0 up h L then 1 else 0 at hflag
    rw [hptr,hvalue0,hlow,hupp] at hflag
    have hvalid1 := Num.IPM.valid_frozen hframe1 (show heap+4*L+2*L ≤ v0 by omega) hvalid0
    have hvalue1 : Num.intVal mem1 (heap+4*L) h (2*L)=Num.intVal mem a h L+Num.intVal mem d h L := by
      rw [Num.IPM.value_frozen hframe1 (show heap+4*L+2*L ≤ v0 by omega),hvalue0]
    refine runs_ret_le (v:=v1) (by eval_expr) ?_ ?_
    · change v1=heap+(1+10*L) ∧ (heap ≤ v1 ∧ v1 ≤ heap+(1+10*L) ∧
        (∀ x < heap,mem1 x=mem x) ∧ ZeroFrom mem1 v1 ∧
        Num.Valid mem1 (heap+4*L) h (2*L) ∧
        Num.intVal mem1 (heap+4*L) h (2*L)=Num.intVal mem a h L+Num.intVal mem d h L ∧
        mem1 (heap+6*L)=(if Num.intVal mem lo h L < Num.intVal mem a h L+Num.intVal mem d h L ∧
          Num.intVal mem a h L+Num.intVal mem d h L < Num.intVal mem up h L then 1 else 0) ∧
        (mem1 (heap+6*L)=1 → Num.Valid mem1 (heap+4*L) h L ∧
          Num.intVal mem1 (heap+4*L) h L=Num.intVal mem a h L+Num.intVal mem d h L))
      refine ⟨by omega,by omega,by omega,?_,hfresh1,hvalid1,hvalue1,?_,?_⟩
      · intro x hx
        exact (hframe1 x (by omega)).trans (hframe0 x hx)
      · simpa only [hv0] using hflag
      · intro haccept
        have hi : Num.intVal mem lo h L < Num.intVal mem a h L+Num.intVal mem d h L ∧
            Num.intVal mem a h L+Num.intVal mem d h L < Num.intVal mem up h L := by
          rw [hv0] at hflag
          rw [haccept] at hflag
          split_ifs at hflag with hi
          · exact hi
        have hfit := fits_of_strict_capacity_interval (Num.intVal_fits hvlo) (Num.intVal_fits hvup) hi
        have hfit1 : Num.Fits h L (Num.intVal mem1 (heap+4*L) h (2*L)) := by rwa [hvalue1]
        refine ⟨fun i hi => hvalid1 i (by omega),?_⟩
        rw [Num.intVal_prefix_wrap hvalid1 (show L ≤ 2*L by omega),Num.wrap_of_fits hfit1,hvalue1]
    · simp only [guardedOverlayContract,wideOverlayContract,wideCapacityGuardContract,heapContract,
        List.getD_cons_zero,List.getD_cons_succ,Expr.size_bin,Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil]
      omega

end MinCostFlow.IPM.Machine
