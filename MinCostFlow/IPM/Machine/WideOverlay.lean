module

public import MinCostFlow.IPM.Machine.OverlayFacts
public import MinCostFlow.Num.SignExtend
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.IPM.FixedPointFacts
public import MinCostFlow.IPM.Machine.Layout
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact wide Query overlay before the capacity guard

Sign-extend the base and queried cumulative increment to twice their
width, then add them exactly. The sum always fits at that width, even
for a target test that will be rejected. The following range guard can
therefore inspect the true candidate rather than a wrapped value.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[base,increment,L,heap]`. The sum is the last 2L cells. -/
def wideOverlayBody (extend add : ℕ) : Stmt :=
  .call 4 extend [.reg 0,.reg 2,.bin .mul (.const 2) (.reg 2),.reg 3] ;;
  .call 5 extend [.reg 1,.reg 2,.bin .mul (.const 2) (.reg 2),.reg 4] ;;
  .call 6 add [.reg 3,.reg 4,.bin .mul (.const 2) (.reg 2),.reg 5] ;;
  .ret (.reg 6)

/-- Both extensions share one module; exact addition follows it. -/
def wideOverlayModule (b h : ℕ) : List Stmt :=
  [wideOverlayBody (b+1) (b+4)] ++ (Num.signExtendModule (b+1) h ++ Num.addModule (b+4) h)

/-- Exact addition in 2L limbs, using six L-limb workspace blocks.
The two source blocks need only be valid and below the heap. -/
def wideOverlayContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L heap,args=[a,d,L,heap] ∧ a+L ≤ heap ∧ d+L ≤ heap ∧
      Num.Valid mem a h L ∧ Num.Valid mem d h L)
    (fun args mem mem' => Num.Valid mem' (heapArg args+4*args.getD 2 0) h (2*args.getD 2 0) ∧
      Num.intVal mem' (heapArg args+4*args.getD 2 0) h (2*args.getD 2 0)=
        Num.intVal mem (args.getD 0 0) h (args.getD 2 0)+
        Num.intVal mem (args.getD 1 0) h (args.getD 2 0))
    (fun args _ => 300*args.getD 2 0+300) (fun args _ => 6*args.getD 2 0)
  {C with post := fun args mem v mem' => v=heapArg args+6*args.getD 2 0 ∧ C.post args mem v mem'}

/-- Wide overlay and all its arithmetic helpers contain no randomness. -/
theorem wideOverlayModule_noRand (b h : ℕ) : ∀ body ∈ wideOverlayModule b h,body.NoRand := by
  intro body hb
  simp only [wideOverlayModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [wideOverlayBody,Stmt.NoRand]
  · exact Num.signExtendModule_noRand _ _ _ hb
  · exact Num.addModule_noRand _ _ _ hb

/-- The actual wide addition cannot overflow, and its workspace and
operation count include both sign extensions and the final addition. -/
theorem wideOverlay_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hp : p.HasAt b (wideOverlayModule b h)) :
    MeetsContract w p b (wideOverlayContract w h) := by
  have ht := Num.hasAt_append_right hp
  have he : p.HasAt (b+1) (Num.signExtendModule (b+1) h) := Num.hasAt_append_left ht
  have ha : p.HasAt (b+4) (Num.addModule (b+4) h) := by
    simpa [Num.signExtendModule,Num.isNegativeModule,Num.extendCopyModule,Nat.add_assoc] using Num.hasAt_append_right ht
  have hw1 : 1 < 2^w := lt_of_lt_of_le (by decide : 1 < 2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := Num.base_lt_word hw
  have heSpec := Num.signExtend_meetsContract hh hw1 hb he
  have haSpec := Num.add_meetsContract hh hw ha
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,d,L,heap,rfl,haEnd,hdEnd,hva,hvd⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+6*L < 2^w at hspace
  have haW : a < 2^w := hwords _ (by simp)
  have hdW : d < 2^w := hwords _ (by simp)
  have hLW : L < 2^w := hwords _ (by simp)
  have hhW : heap < 2^w := hwords _ (by simp)
  have h2L : 2*L < 2^w := by omega
  have htwo : 2 < 2^w := by
    have hh2 := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 2 ≤ w by omega)
    omega
  have hfit := overlay_sum_fits_double (Num.intVal_fits hva) (Num.intVal_fits hvd)
  apply runs_start_le
  unfold wideOverlayBody
  refine runs_seq_call_le heSpec (vs:=[a,L,2*L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,L,2*L,heap,rfl,by omega,haEnd,hva⟩,hz,by change heap+2*L < 2^w; omega⟩
  · intro v0 mem0 pos0 hp0
    obtain ⟨hv0,_,_,hframe0,hfresh0,hvalid0,hvalue0⟩ := hp0
    change v0=heap+2*L at hv0
    change ∀ x < heap,mem0 x=mem x at hframe0
    change Num.Valid mem0 heap h (2*L) at hvalid0
    change Num.intVal mem0 heap h (2*L)=Num.intVal mem a h L at hvalue0
    have hv0W : v0 < 2^w := by omega
    refine runs_seq_call_le heSpec (vs:=[d,L,2*L,v0]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨d,L,2*L,v0,rfl,by omega,by omega,Num.IPM.valid_frozen hframe0 hdEnd hvd⟩,
        hfresh0,by change v0+2*L < 2^w; omega⟩
    · intro v1 mem1 pos1 hp1
      obtain ⟨hv1,_,_,hframe1,hfresh1,hvalid1,hvalue1⟩ := hp1
      change v1=v0+2*L at hv1
      change ∀ x < v0,mem1 x=mem0 x at hframe1
      change Num.Valid mem1 v0 h (2*L) at hvalid1
      change Num.intVal mem1 v0 h (2*L)=Num.intVal mem0 d h L at hvalue1
      have hv1W : v1 < 2^w := by omega
      have hvalid01 := Num.IPM.valid_frozen hframe1 (show heap+2*L ≤ v0 by omega) hvalid0
      have hvalue01 : Num.intVal mem1 heap h (2*L)=Num.intVal mem a h L := by
        rw [Num.IPM.value_frozen hframe1 (show heap+2*L ≤ v0 by omega),hvalue0]
      have hvalue11 : Num.intVal mem1 v0 h (2*L)=Num.intVal mem d h L := by
        rw [hvalue1,Num.IPM.value_frozen hframe0 hdEnd]
      refine runs_seq_call_le haSpec (vs:=[heap,v0,2*L,v1]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨heap,v0,2*L,v1,rfl,⟨⟨heap,v0,2*L,0,v1,rfl,by omega,by omega,
          by decide,hvalid01,hvalid1⟩,hfresh1,by change v1+2*L < 2^w; omega⟩⟩
      · intro v2 mem2 pos2 hp2
        obtain ⟨hv2,_,_,hframe2,hfresh2,hlist⟩ := hp2
        change v2=v1+2*L at hv2
        change ∀ x < v1,mem2 x=mem1 x at hframe2
        change ListAt mem2 v1 (Num.digits h (2*L)
          (Num.unsignedVal mem1 heap h (2*L)+Num.unsignedVal mem1 v0 h (2*L)+0)) at hlist
        have hsumfit : Num.Fits h (2*L)
            (Num.intVal mem1 heap h (2*L)+Num.intVal mem1 v0 h (2*L)+(0:ℤ)) := by
          simpa only [hvalue01,hvalue11,add_zero] using hfit
        have hsum := Num.addCarry_value_of_fits hlist hsumfit
        have hvalid2 := (Num.addCarry_value hlist).1
        refine runs_ret_le (v:=v2) (by eval_expr) ?_ ?_
        · change v2=heap+6*L ∧ (heap ≤ v2 ∧ v2 ≤ heap+6*L ∧
            (∀ x < heap,mem2 x=mem x) ∧ ZeroFrom mem2 v2 ∧
            Num.Valid mem2 (heap+4*L) h (2*L) ∧
            Num.intVal mem2 (heap+4*L) h (2*L)=Num.intVal mem a h L+Num.intVal mem d h L)
          refine ⟨by omega,by omega,by omega,?_,hfresh2,?_,?_⟩
          · intro x hx
            exact (hframe2 x (by omega)).trans ((hframe1 x (by omega)).trans (hframe0 x hx))
          · simpa only [show v1=heap+4*L by omega] using hvalid2
          · simpa only [show v1=heap+4*L by omega,hvalue01,hvalue11,Nat.cast_zero,add_zero] using hsum
        · simp only [wideOverlayContract,Num.signExtendContract,Num.addContract,
            Num.addCarryContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
            Expr.size_bin,Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil]
          omega

/-- At any common fixed-point precision, the wide machine result is the
true sum of the base coordinate and queried cumulative increment. -/
theorem wideOverlay_output {w h a d L heap v P : ℕ} {mem mem' : ℕ → ℕ} {x y : ℝ}
    (hout : (wideOverlayContract w h).post [a,d,L,heap] mem v mem')
    (hx : ScalarAt mem a h L P x) (hy : ScalarAt mem d h L P y) :
    ScalarAt mem' (v-2*L) h (2*L) P (x+y) := by
  have hv := hout.1
  change v=heap+6*L at hv
  have hvalid := hout.2.2.2.2.2.1
  have hvalue := hout.2.2.2.2.2.2
  change Num.Valid mem' (heap+4*L) h (2*L) at hvalid
  change Num.intVal mem' (heap+4*L) h (2*L)=Num.intVal mem a h L+Num.intVal mem d h L at hvalue
  have hptr : v-2*L=heap+4*L := by omega
  refine ⟨hptr ▸ hvalid,?_⟩
  rw [hptr,Num.fixVal,hvalue,Int.cast_add,add_div]
  exact congrArg₂ (·+·) hx.2 hy.2

end MinCostFlow.IPM.Machine
