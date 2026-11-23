module

public import MinCostFlow.IPM.Machine.StrictRange
public import MinCostFlow.Num.SignExtend
public import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.IPM.Machine.GuardedNarrow
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Guarding a wide queried candidate against ordinary capacities

The candidate already has twice the ordinary width. Extend the two
capacity blocks to that width, perform the exact strict interval test,
and write its Boolean answer at the incoming heap. The full candidate
and original capacities are preserved for the accepted narrowing step.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[candidate,lower,upper,L,heap]`. The answer is at heap. -/
def wideCapacityGuardBody (extend guard : ℕ) : Stmt :=
  .call 5 extend [.reg 1,.reg 3,.bin .mul (.const 2) (.reg 3),.bin .add (.reg 4) (.const 1)] ;;
  .call 6 extend [.reg 2,.reg 3,.bin .mul (.const 2) (.reg 3),.reg 5] ;;
  .call 7 guard [.bin .add (.reg 4) (.const 1),.reg 0,.reg 5,.bin .mul (.const 2) (.reg 3)] ;;
  .store (.reg 4) (.reg 7) ;;
  .ret (.reg 6)

/-- The capacity extensions and shared signed interval guard. -/
def wideCapacityGuardModule (b h : ℕ) : List Stmt :=
  [wideCapacityGuardBody (b+1) (b+4)] ++
    (Num.signExtendModule (b+1) h ++ strictRangeModule (b+4) h)

/-- The guard accepts exactly the true strict interval, even when the
candidate is outside the ordinary signed range. It uses `1+4L` cells. -/
def wideCapacityGuardContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ xp lo up L heap,args=[xp,lo,up,L,heap] ∧ xp+2*L ≤ heap ∧
      lo+L ≤ heap ∧ up+L ≤ heap ∧ Num.Valid mem xp h (2*L) ∧
      Num.Valid mem lo h L ∧ Num.Valid mem up h L)
    (fun args mem mem' => mem' (heapArg args)=if
      Num.intVal mem (args.getD 1 0) h (args.getD 3 0) <
        Num.intVal mem (args.getD 0 0) h (2*args.getD 3 0) ∧
      Num.intVal mem (args.getD 0 0) h (2*args.getD 3 0) <
        Num.intVal mem (args.getD 2 0) h (args.getD 3 0) then 1 else 0)
    (fun args _ => 600*args.getD 3 0+600) (fun args _ => 1+4*args.getD 3 0)
  {C with post := fun args mem v mem' => v=heapArg args+(1+4*args.getD 3 0) ∧ C.post args mem v mem'}

/-- All capacity extension and comparison procedures are deterministic. -/
theorem wideCapacityGuardModule_noRand (b h : ℕ) :
    ∀ body ∈ wideCapacityGuardModule b h,body.NoRand := by
  intro body hb
  simp only [wideCapacityGuardModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [wideCapacityGuardBody,Stmt.NoRand]
  · exact Num.signExtendModule_noRand _ _ _ hb
  · exact strictRangeModule_noRand _ _ _ hb

/-- The machine checks the true wide candidate against both capacities,
charging both sign extensions, comparisons and the stored answer. -/
theorem wideCapacityGuard_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hp : p.HasAt b (wideCapacityGuardModule b h)) :
    MeetsContract w p b (wideCapacityGuardContract w h) := by
  have ht := Num.hasAt_append_right hp
  have he : p.HasAt (b+1) (Num.signExtendModule (b+1) h) := Num.hasAt_append_left ht
  have hg : p.HasAt (b+4) (strictRangeModule (b+4) h) := by
    simpa [Num.signExtendModule,Num.isNegativeModule,Num.extendCopyModule,Nat.add_assoc] using Num.hasAt_append_right ht
  have hw1 : 1 < 2^w := lt_of_lt_of_le (by decide : 1 < 2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := Num.base_lt_word hw
  have heSpec := Num.signExtend_meetsContract hh hw1 hb he
  have hgSpec := strictRange_meetsContract hh hw1 hb hg
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨xp,lo,up,L,heap,rfl,hxEnd,hloEnd,hupEnd,hvx,hvlo,hvup⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(1+4*L) < 2^w at hspace
  have hxW : xp < 2^w := hwords _ (by simp)
  have hloW : lo < 2^w := hwords _ (by simp)
  have hupW : up < 2^w := hwords _ (by simp)
  have hLW : L < 2^w := hwords _ (by simp)
  have hhW : heap < 2^w := hwords _ (by simp)
  have h2L : 2*L < 2^w := by omega
  have htwo : 2 < 2^w := by
    have hh2 := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 2 ≤ w by omega)
    omega
  apply runs_start_le
  unfold wideCapacityGuardBody
  refine runs_seq_call_le heSpec (vs:=[lo,L,2*L,heap+1]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨lo,L,2*L,heap+1,rfl,by omega,by omega,hvlo⟩,
      hz.mono (h':=heap+1) (by omega),by change heap+1+2*L < 2^w; omega⟩
  · intro v0 mem0 pos0 hp0
    obtain ⟨hv0,_,_,hframe0,hfresh0,hvalid0,hvalue0⟩ := hp0
    change v0=heap+1+2*L at hv0
    change ∀ x < heap+1,mem0 x=mem x at hframe0
    change Num.Valid mem0 (heap+1) h (2*L) at hvalid0
    change Num.intVal mem0 (heap+1) h (2*L)=Num.intVal mem lo h L at hvalue0
    have hv0W : v0 < 2^w := by omega
    refine runs_seq_call_le heSpec (vs:=[up,L,2*L,v0]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨up,L,2*L,v0,rfl,by omega,by omega,
        Num.IPM.valid_frozen hframe0 (by omega : up+L ≤ heap+1) hvup⟩,
        hfresh0,by change v0+2*L < 2^w; omega⟩
    · intro v1 mem1 pos1 hp1
      obtain ⟨hv1,_,_,hframe1,hfresh1,hvalid1,hvalue1⟩ := hp1
      change v1=v0+2*L at hv1
      change ∀ x < v0,mem1 x=mem0 x at hframe1
      change Num.Valid mem1 v0 h (2*L) at hvalid1
      change Num.intVal mem1 v0 h (2*L)=Num.intVal mem0 up h L at hvalue1
      have hv1W : v1 < 2^w := by omega
      have hvalid01 := Num.IPM.valid_frozen hframe1 (show heap+1+2*L ≤ v0 by omega) hvalid0
      have hvalue01 : Num.intVal mem1 (heap+1) h (2*L)=Num.intVal mem lo h L := by
        rw [Num.IPM.value_frozen hframe1 (show heap+1+2*L ≤ v0 by omega),hvalue0]
      have hvalue11 : Num.intVal mem1 v0 h (2*L)=Num.intVal mem up h L := by
        rw [hvalue1,Num.IPM.value_frozen hframe0 (show up+L ≤ heap+1 by omega)]
      have hframe : ∀ x < heap,mem1 x=mem x := by
        intro x hx
        exact (hframe1 x (by omega)).trans (hframe0 x (by omega))
      have hvalidx := Num.IPM.valid_frozen hframe hxEnd hvx
      have hvaluex := Num.IPM.value_frozen (h:=h) hframe hxEnd
      refine runs_seq_call_le hgSpec (vs:=[heap+1,xp,v0,2*L]) (by eval_expr) (by wram_words)
        ⟨heap+1,xp,v0,2*L,rfl,by omega,by omega,by omega,hvalid01,hvalidx,hvalid1⟩ ?_
      intro v2 mem2 pos2 hp2
      obtain ⟨hm2,hv2⟩ := hp2
      change mem2=mem1 at hm2
      subst mem2
      change v2=if Num.intVal mem1 (heap+1) h (2*L) < Num.intVal mem1 xp h (2*L) ∧
        Num.intVal mem1 xp h (2*L) < Num.intVal mem1 v0 h (2*L) then 1 else 0 at hv2
      rw [hvalue01,hvalue11,hvaluex] at hv2
      have hv2b : v2 ≤ 1 := by split_ifs at hv2 <;> omega
      wram_step
      refine runs_ret_le (v:=v1) (by eval_expr) ?_ ?_
      · change v1=heap+(1+4*L) ∧ (heap ≤ v1 ∧ v1 ≤ heap+(1+4*L) ∧
          (∀ x < heap,(Function.update mem1 heap v2) x=mem x) ∧
          ZeroFrom (Function.update mem1 heap v2) v1 ∧ _)
        refine ⟨by omega,by omega,by omega,?_,?_,?_⟩
        · intro x hx
          rw [Function.update_of_ne (by omega : x ≠ heap)]
          exact hframe x hx
        · intro x hx
          rw [Function.update_of_ne (by omega : x ≠ heap)]
          exact hfresh1 x hx
        · change (Function.update mem1 heap v2) heap=if Num.intVal mem lo h L < Num.intVal mem xp h (2*L) ∧
            Num.intVal mem xp h (2*L) < Num.intVal mem up h L then 1 else 0
          simpa using hv2
      · simp only [wideCapacityGuardContract,Num.signExtendContract,strictRangeContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
        omega

/-- The stored answer decides the true strict capacity interval at any
common fixed-point precision, including a wide candidate. -/
theorem wideCapacityGuard_output {w h xp lo up L heap v P : ℕ}
    {mem mem' : ℕ → ℕ} {lower x upper : ℝ}
    (hout : (wideCapacityGuardContract w h).post [xp,lo,up,L,heap] mem v mem')
    (hlo : ScalarAt mem lo h L P lower) (hx : ScalarAt mem xp h (2*L) P x)
    (hup : ScalarAt mem up h L P upper) : mem' heap=1 ↔ lower < x ∧ x < upper := by
  have hflag := hout.2.2.2.2.2
  change mem' heap=if Num.intVal mem lo h L < Num.intVal mem xp h (2*L) ∧
    Num.intVal mem xp h (2*L) < Num.intVal mem up h L then 1 else 0 at hflag
  have hiff : mem' heap=1 ↔ Num.intVal mem lo h L < Num.intVal mem xp h (2*L) ∧
      Num.intVal mem xp h (2*L) < Num.intVal mem up h L := by
    rw [hflag]
    split_ifs <;> simp_all
  rw [hiff,← hlo.2,← hx.2,← hup.2]
  simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2^P)]
  norm_cast

/-- An accepted actual machine guard preserves the candidate and
certifies its exact representation at the ordinary stored width. -/
theorem wideCapacityGuard_narrows {w h xp lo up L heap v P : ℕ}
    {mem mem' : ℕ → ℕ} {lower x upper : ℝ}
    (hout : (wideCapacityGuardContract w h).post [xp,lo,up,L,heap] mem v mem')
    (hlo : ScalarAt mem lo h L P lower) (hx : ScalarAt mem xp h (2*L) P x)
    (hup : ScalarAt mem up h L P upper) (hxEnd : xp+2*L ≤ heap)
    (haccept : mem' heap=1) : ScalarAt mem' xp h L P x := by
  have hinside := (wideCapacityGuard_output hout hlo hx hup).mp haccept
  have hn := scalarAt_narrow_of_capacity_guard hlo hx hup hinside
  have hframe := hout.2.2.2.1
  change ∀ a < heap,mem' a=mem a at hframe
  have hend : xp+L ≤ heap := by omega
  exact ⟨Num.IPM.valid_frozen hframe hend hn.1,(Num.IPM.fixVal_frozen hframe hend).trans hn.2⟩

end MinCostFlow.IPM.Machine
