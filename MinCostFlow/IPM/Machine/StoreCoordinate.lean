module

public import MinCostFlow.IPM.Machine.GuardedOverlay
public import MinCostFlow.Num.IPM.WriteBlock
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Guarded writes of refreshed flow coordinates

Algorithm 7 of Chen et al., arXiv:2203.00671v2 (page 69), replaces a
reported stored coordinate by the base plus its cumulative increment.
For a failure-aware target test, first form and guard that exact sum.
Write its ordinary-width limbs only on acceptance. A rejected candidate
leaves the complete old heap prefix unchanged, so the target test can stop.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[base,increment,lower,upper,destination,L,heap]`. -/
def storeCoordinateBody (guard write : ℕ) : Stmt :=
  .call 7 guard [.reg 0,.reg 1,.reg 2,.reg 3,.reg 5,.reg 6] ;;
  .assign 8 (.load (.bin .add (.reg 6) (.bin .mul (.const 6) (.reg 5)))) ;;
  .cond (.reg 8)
    (.call 9 write [.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 5)),.reg 5,.reg 4] ;;
      .ret (.reg 7))
    (.ret (.reg 7))

/-- Guarded recovery followed by the existing disjoint block writer. -/
def storeCoordinateModule (b h : ℕ) : List Stmt :=
  let write := b+1+(guardedOverlayModule (b+1) h).length
  [storeCoordinateBody (b+1) write] ++
    (guardedOverlayModule (b+1) h ++ Num.IPM.writeBlockModule write)

/-- Only the designated old block may change, and only after acceptance.
The flag and allocation are those of guarded recovery. -/
def storeCoordinateContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d lo up dst L heap,args=[a,d,lo,up,dst,L,heap] ∧ dst+L ≤ heap ∧
    (guardedOverlayContract w h).pre [a,d,lo,up,L,heap] mem
  post args mem v mem' :=
    let L := args.getD 5 0
    let dst := args.getD 4 0
    let heap := heapArg args
    let sum := Num.intVal mem (args.getD 0 0) h L+Num.intVal mem (args.getD 1 0) h L
    v=heap+(1+10*L) ∧ ZeroFrom mem' v ∧
    (∀ z < heap,z < dst ∨ dst+L ≤ z → mem' z=mem z) ∧
    mem' (heap+6*L)=(if Num.intVal mem (args.getD 2 0) h L < sum ∧
      sum < Num.intVal mem (args.getD 3 0) h L then 1 else 0) ∧
    (mem' (heap+6*L)=1 → Num.Valid mem' dst h L ∧ Num.intVal mem' dst h L=sum) ∧
    (mem' (heap+6*L)=0 → ∀ z < heap,mem' z=mem z)
  cost args _ := 1100*args.getD 5 0+1300

/-- All guarded recovery and coordinate writes are deterministic. -/
theorem storeCoordinateModule_noRand (b h : ℕ) :
    ∀ body ∈ storeCoordinateModule b h,body.NoRand := by
  intro body hb
  simp only [storeCoordinateModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [storeCoordinateBody,Stmt.NoRand]
  · exact guardedOverlayModule_noRand _ _ _ hb
  · exact Num.IPM.writeBlockModule_noRand _ _ hb

/-- Actual reported-coordinate refresh writes the exact accepted sum,
preserves other old cells, and performs no old-memory write on rejection.
Both branches have the stated explicit operation and allocation bounds. -/
theorem storeCoordinate_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hp : p.HasAt b (storeCoordinateModule b h)) :
    MeetsContract w p b (storeCoordinateContract w h) := by
  have ht := Num.hasAt_append_right hp
  have hg : p.HasAt (b+1) (guardedOverlayModule (b+1) h) := Num.hasAt_append_left ht
  have hwr : p.HasAt (b+1+(guardedOverlayModule (b+1) h).length)
      (Num.IPM.writeBlockModule (b+1+(guardedOverlayModule (b+1) h).length)) := Num.hasAt_append_right ht
  have hgSpec := guardedOverlay_meetsContract hh hw hg
  have hw1 : 1 < 2^w := lt_of_lt_of_le (by decide : 1 < 2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hwrSpec := Num.IPM.writeBlock_meetsContract (h:=h) hw1 hwr
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,d,lo,up,dst,L,heap,rfl,hdst,hnum⟩ := hpre
  have hspace := hnum.2.2
  change heap+(1+10*L) < 2^w at hspace
  have hLW : L < 2^w := hwords _ (by simp)
  have hdstW : dst < 2^w := hwords _ (by simp)
  have hheapW : heap < 2^w := hwords _ (by simp)
  have hfour : 4 < 2^w := by
    have hpw := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 3 ≤ w by omega)
    omega
  have hsix : 6 < 2^w := by
    have hpw := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 3 ≤ w by omega)
    omega
  have hargWords : ∀ x ∈ [a,d,lo,up,L,heap],x < 2^w := by
    intro x hx
    apply hwords x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    tauto
  apply runs_start_le
  unfold storeCoordinateBody
  refine runs_seq_call_le hgSpec (vs:=[a,d,lo,up,L,heap]) (by eval_expr) hargWords hnum ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨hv0,_,_,hframe0,hfresh0,_,_,hflag,hnarrow⟩ := hp0
  change v0=heap+(1+10*L) at hv0
  change ∀ x < heap,mem0 x=mem x at hframe0
  change mem0 (heap+6*L)=if Num.intVal mem lo h L < Num.intVal mem a h L+Num.intVal mem d h L ∧
    Num.intVal mem a h L+Num.intVal mem d h L < Num.intVal mem up h L then 1 else 0 at hflag
  change mem0 (heap+6*L)=1 → Num.Valid mem0 (heap+4*L) h L ∧
    Num.intVal mem0 (heap+4*L) h L=Num.intVal mem a h L+Num.intVal mem d h L at hnarrow
  have hv0W : v0 < 2^w := by omega
  have hsrcW : heap+4*L < 2^w := by omega
  have hslotW : heap+6*L < 2^w := by omega
  have hbit : mem0 (heap+6*L) ≤ 1 := by split_ifs at hflag <;> omega
  wram_step
  refine runs_cond_le (v:=mem0 (heap+6*L)) (by eval_expr) ?_ ?_
  · intro hnonzero
    have haccept : mem0 (heap+6*L)=1 := by omega
    obtain ⟨hvalid,hvalue⟩ := hnarrow haccept
    refine runs_seq_call_le hwrSpec (vs:=[heap+4*L,L,dst]) (by eval_expr) (by wram_words)
      ⟨heap+4*L,L,dst,rfl,by omega,by omega,Or.inr (by omega),hvalid⟩ ?_
    intro v1 mem1 pos1 hp1
    obtain ⟨_,hframe1,_,hvalid1,hvalue1⟩ := hp1
    change ∀ z,z < dst ∨ dst+L ≤ z → mem1 z=mem0 z at hframe1
    change Num.Valid mem1 dst h L at hvalid1
    change Num.intVal mem1 dst h L=Num.intVal mem0 (heap+4*L) h L at hvalue1
    have hslot : mem1 (heap+6*L)=mem0 (heap+6*L) := hframe1 _ (Or.inr (by omega))
    refine runs_ret_le (v:=v0) (by eval_expr) ?_ ?_
    · change v0=heap+(1+10*L) ∧ ZeroFrom mem1 v0 ∧
        (∀ z < heap,z < dst ∨ dst+L ≤ z → mem1 z=mem z) ∧
        mem1 (heap+6*L)=(if Num.intVal mem lo h L < Num.intVal mem a h L+Num.intVal mem d h L ∧
          Num.intVal mem a h L+Num.intVal mem d h L < Num.intVal mem up h L then 1 else 0) ∧
        (mem1 (heap+6*L)=1 → Num.Valid mem1 dst h L ∧ Num.intVal mem1 dst h L=_) ∧
        (mem1 (heap+6*L)=0 → ∀ z < heap,mem1 z=mem z)
      refine ⟨hv0,?_,?_,hslot.trans hflag,fun _ => ⟨hvalid1,hvalue1.trans hvalue⟩,?_⟩
      · intro z hz
        rw [hframe1 z (Or.inr (by omega))]
        exact hfresh0 z hz
      · intro z hz hout
        exact (hframe1 z hout).trans (hframe0 z hz)
      · intro hzero
        rw [hslot,haccept] at hzero
        contradiction
    · simp only [storeCoordinateContract,guardedOverlayContract,Num.IPM.writeBlockContract,
        heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_bin,Expr.size_load,
        Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil]
      omega
  · intro hzero
    refine runs_ret_le (v:=v0) (by eval_expr) ?_ ?_
    · change v0=heap+(1+10*L) ∧ ZeroFrom mem0 v0 ∧
        (∀ z < heap,z < dst ∨ dst+L ≤ z → mem0 z=mem z) ∧
        mem0 (heap+6*L)=(if Num.intVal mem lo h L < Num.intVal mem a h L+Num.intVal mem d h L ∧
          Num.intVal mem a h L+Num.intVal mem d h L < Num.intVal mem up h L then 1 else 0) ∧
        (mem0 (heap+6*L)=1 → Num.Valid mem0 dst h L ∧ Num.intVal mem0 dst h L=_) ∧
        (mem0 (heap+6*L)=0 → ∀ z < heap,mem0 z=mem z)
      exact ⟨hv0,hfresh0,fun z hz _ => hframe0 z hz,hflag,
        fun ha => by rw [hzero] at ha; contradiction,fun _ => hframe0⟩
    · simp only [storeCoordinateContract,guardedOverlayContract,heapContract,
        List.getD_cons_zero,List.getD_cons_succ,Expr.size_bin,Expr.size_load,
        Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil]
      omega

/-- An accepted coordinate write stores the true base-plus-increment
at the original fixed-point precision. -/
theorem storeCoordinate_output {w h a d lo up dst L heap v P : ℕ}
    {mem mem' : ℕ → ℕ} {x y : ℝ}
    (hout : (storeCoordinateContract w h).post [a,d,lo,up,dst,L,heap] mem v mem')
    (hx : ScalarAt mem a h L P x) (hy : ScalarAt mem d h L P y)
    (haccept : mem' (heap+6*L)=1) : ScalarAt mem' dst h L P (x+y) := by
  have hh := hout.2.2.2.2.1
  change mem' (heap+6*L)=1 → Num.Valid mem' dst h L ∧
    Num.intVal mem' dst h L=Num.intVal mem a h L+Num.intVal mem d h L at hh
  obtain ⟨hvalid,hvalue⟩ := hh haccept
  refine ⟨hvalid,?_⟩
  change (Num.intVal mem' dst h L:ℝ)/(2:ℝ)^P=x+y
  rw [hvalue,Int.cast_add,add_div]
  exact congrArg₂ (·+·) hx.2 hy.2

/-- The stored acceptance flag tests the real capacity interval of the
true base-plus-increment, at any shared fixed-point precision. -/
theorem storeCoordinate_flag_output {w h a d lo up dst L heap v P : ℕ}
    {mem mem' : ℕ → ℕ} {x y lower upper : ℝ}
    (hout : (storeCoordinateContract w h).post [a,d,lo,up,dst,L,heap] mem v mem')
    (hx : ScalarAt mem a h L P x) (hy : ScalarAt mem d h L P y)
    (hlo : ScalarAt mem lo h L P lower) (hup : ScalarAt mem up h L P upper) :
    mem' (heap+6*L)=if lower < x+y ∧ x+y < upper then 1 else 0 := by
  have hflag := hout.2.2.2.1
  change mem' (heap+6*L)=if Num.intVal mem lo h L < Num.intVal mem a h L+Num.intVal mem d h L ∧
    Num.intVal mem a h L+Num.intVal mem d h L < Num.intVal mem up h L then 1 else 0 at hflag
  have hsum : ((Num.intVal mem a h L+Num.intVal mem d h L:ℤ):ℝ)/(2:ℝ)^P=x+y := by
    rw [Int.cast_add,add_div]
    exact congrArg₂ (·+·) hx.2 hy.2
  have hcond : (Num.intVal mem lo h L < Num.intVal mem a h L+Num.intVal mem d h L ∧
      Num.intVal mem a h L+Num.intVal mem d h L < Num.intVal mem up h L) ↔
      lower < x+y ∧ x+y < upper := by
    rw [← hlo.2,← hup.2,← hsum]
    simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2^P)]
    norm_cast
  simp only [hflag,hcond]

/-- Writing the caller's stored coordinate preserves a parameter data
structure whose footprint is below the heap and outside that block.
Its amortized potential is also unchanged, by the shared locality clause. -/
theorem storeCoordinate_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w h a d lo up dst L heap v b : ℕ} {mem mem' : ℕ → ℕ} {s : σ} {x : R.τ}
    (hout : (storeCoordinateContract w h).post [a,d,lo,up,dst,L,heap] mem v mem')
    (hrep : R.rep b s x mem)
    (hfoot : ∀ z,R.foot b x z → z < heap ∧ (z < dst ∨ dst+L ≤ z)) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' := by
  have hframe := hout.2.2.1
  change ∀ z < heap,z < dst ∨ dst+L ≤ z → mem' z=mem z at hframe
  have hsame : ∀ z,R.foot b x z → mem z=mem' z := by
    intro z hz
    exact (hframe z (hfoot z hz).1 (hfoot z hz).2).symm
  have hh := hlocal b s x mem mem' hsame
  exact ⟨hh.1 hrep,hh.2⟩

end MinCostFlow.IPM.Machine
