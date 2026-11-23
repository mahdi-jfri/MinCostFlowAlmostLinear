module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Num.IPM.WriteBlock
public import WordRAM.DataStructure
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Updating the two stored coefficient tables

After computing both coefficients of a reported edge, copy the results
into their reserved table blocks. The source blocks and the two destination
blocks are disjoint. The copies preserve every cell outside those two
destinations, so a disjoint min-ratio representation remains valid.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[lengthSource,gradientSource,lengthDestination,gradientDestination,L,heap]`. -/
def storeCoefficientsBody (copy : ℕ) : Stmt :=
  .call 6 copy [.reg 0,.reg 4,.reg 2] ;;
  .call 7 copy [.reg 1,.reg 4,.reg 3] ;;
  .ret (.reg 5)

/-- Two calls share one verified block-copy procedure. -/
def storeCoefficientsModule (b : ℕ) : List Stmt :=
  [storeCoefficientsBody (b+1)] ++ Num.IPM.writeBlockModule (b+1)

/-- No space is allocated. The two destination values equal the original
source values and all cells outside both destinations are preserved. -/
def storeCoefficientsContract (w h : ℕ) : Contract where
  pre args mem := ∃ ls gs ld gd L heap,args=[ls,gs,ld,gd,L,heap] ∧
    ls+L≤heap ∧ gs+L≤heap ∧ ld+L≤heap ∧ gd+L≤heap ∧ heap<2^w ∧
    (ls+L≤ld ∨ ld+L≤ls) ∧ (gs+L≤ld ∨ ld+L≤gs) ∧
    (gs+L≤gd ∨ gd+L≤gs) ∧ (ld+L≤gd ∨ gd+L≤ld) ∧
    Num.Valid mem ls h L ∧ Num.Valid mem gs h L ∧ ZeroFrom mem heap
  post args mem v mem' := v=args.getD 5 0 ∧ ZeroFrom mem' v ∧
    (∀ z,(z<args.getD 2 0 ∨ args.getD 2 0+args.getD 4 0≤z) →
      (z<args.getD 3 0 ∨ args.getD 3 0+args.getD 4 0≤z) → mem' z=mem z) ∧
    Num.Valid mem' (args.getD 2 0) h (args.getD 4 0) ∧
    Num.intVal mem' (args.getD 2 0) h (args.getD 4 0)=
      Num.intVal mem (args.getD 0 0) h (args.getD 4 0) ∧
    Num.Valid mem' (args.getD 3 0) h (args.getD 4 0) ∧
    Num.intVal mem' (args.getD 3 0) h (args.getD 4 0)=
      Num.intVal mem (args.getD 1 0) h (args.getD 4 0)
  cost args _ := 34*args.getD 4 0+100

/-- Both coefficient copies are deterministic. -/
theorem storeCoefficientsModule_noRand (b : ℕ) :
    ∀ body∈storeCoefficientsModule b,body.NoRand := by
  intro body hb
  simp only [storeCoefficientsModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [storeCoefficientsBody,Stmt.NoRand]
  · exact Num.IPM.writeBlockModule_noRand _ _ hb

/-- The two actual block-copy calls write the original coefficients with
no allocation and the full frame outside their destinations. -/
theorem storeCoefficients_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1<2^w) (hp : p.HasAt b (storeCoefficientsModule b)) :
    MeetsContract w p b (storeCoefficientsContract w h) := by
  have hcopy := Num.IPM.writeBlock_meetsContract (h:=h) hw (Num.hasAt_append_right hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨ls,gs,ld,gd,L,heap,rfl,hls,hgs,hld,hgd,hh,
    hlsld,hgsld,hgsgd,hldgd,hvl,hvg,hz⟩ := hpre
  apply runs_start_le
  unfold storeCoefficientsBody
  refine runs_seq_call_le hcopy (vs:=[ls,L,ld]) (by eval_expr)
    (by intro x hx; apply hwords x; simp_all only [List.mem_cons,List.not_mem_nil,or_false]; tauto)
    ⟨ls,L,ld,rfl,by omega,by omega,hlsld,hvl⟩ ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨_,hframe0,_,hv0,hval0⟩ := hp0
  change ∀ z,z<ld ∨ ld+L≤z → mem0 z=mem z at hframe0
  change Num.Valid mem0 ld h L at hv0
  change Num.intVal mem0 ld h L=Num.intVal mem ls h L at hval0
  have hgsFrame : ∀ i<L,mem0 (gs+i)=mem (gs+i) := by
    intro i hi
    apply hframe0
    rcases hgsld with hd | hd <;> omega
  have hvg0 : Num.Valid mem0 gs h L := by
    intro i hi
    rw [hgsFrame i hi]
    exact hvg i hi
  have hvgval : Num.intVal mem0 gs h L=Num.intVal mem gs h L := Num.intVal_congr hgsFrame
  refine runs_seq_call_le hcopy (vs:=[gs,L,gd]) (by eval_expr)
    (by intro x hx; apply hwords x; simp_all only [List.mem_cons,List.not_mem_nil,or_false]; tauto)
    ⟨gs,L,gd,rfl,by omega,by omega,hgsgd,hvg0⟩ ?_
  intro v1 mem1 pos1 hp1
  obtain ⟨_,hframe1,_,hv1,hval1⟩ := hp1
  change ∀ z,z<gd ∨ gd+L≤z → mem1 z=mem0 z at hframe1
  change Num.Valid mem1 gd h L at hv1
  change Num.intVal mem1 gd h L=Num.intVal mem0 gs h L at hval1
  have hldFrame : ∀ i<L,mem1 (ld+i)=mem0 (ld+i) := by
    intro i hi
    apply hframe1
    rcases hldgd with hd | hd <;> omega
  refine runs_ret_le (v:=heap) (by eval_expr) ?_ ?_
  · change heap=heap ∧ ZeroFrom mem1 heap ∧
      (∀ z,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem1 z=mem z) ∧
      Num.Valid mem1 ld h L ∧ Num.intVal mem1 ld h L=Num.intVal mem ls h L ∧
      Num.Valid mem1 gd h L ∧ Num.intVal mem1 gd h L=Num.intVal mem gs h L
    refine ⟨rfl,Num.IPM.zeroFrom_writeBlock hframe1 hgd
      (Num.IPM.zeroFrom_writeBlock hframe0 hld hz),?_,?_,?_,hv1,hval1.trans hvgval⟩
    · intro z hz0 hz1
      exact (hframe1 z hz1).trans (hframe0 z hz0)
    · intro i hi
      rw [hldFrame i hi]
      exact hv0 i hi
    · exact (Num.intVal_congr hldFrame).trans hval0
  · simp only [storeCoefficientsContract,Num.IPM.writeBlockContract,
      List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,argsSize_cons,argsSize_nil]
    omega

/-- Exact copies preserve the real decoded coefficient values at any
shared precision. -/
theorem storeCoefficients_output {w h ls gs ld gd L heap v P : ℕ}
    {mem mem' : ℕ → ℕ} {length gradient : ℝ}
    (hout : (storeCoefficientsContract w h).post [ls,gs,ld,gd,L,heap] mem v mem')
    (hl : ScalarAt mem ls h L P length) (hg : ScalarAt mem gs h L P gradient) :
    ScalarAt mem' ld h L P length ∧ ScalarAt mem' gd h L P gradient := by
  obtain ⟨_,_,_,hvl,hvalL,hvg,hvalG⟩ := hout
  change Num.intVal mem' ld h L=Num.intVal mem ls h L at hvalL
  change Num.intVal mem' gd h L=Num.intVal mem gs h L at hvalG
  refine ⟨⟨hvl,?_⟩,⟨hvg,?_⟩⟩
  · change (Num.intVal mem' ld h L:ℝ)/(2:ℝ)^P=length
    rw [hvalL]
    exact hl.2
  · change (Num.intVal mem' gd h L:ℝ)/(2:ℝ)^P=gradient
    rw [hvalG]
    exact hg.2

/-- Writing coefficient-table blocks preserves the parameter data
structure and its amortized potential when its footprint avoids them. -/
theorem storeCoefficients_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w h ls gs ld gd L heap v b : ℕ} {mem mem' : ℕ → ℕ} {s : σ} {x : R.τ}
    (hout : (storeCoefficientsContract w h).post [ls,gs,ld,gd,L,heap] mem v mem')
    (hrep : R.rep b s x mem)
    (hfoot : ∀ z,R.foot b x z → (z<ld ∨ ld+L≤z) ∧ (z<gd ∨ gd+L≤z)) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' := by
  have hframe := hout.2.2.1
  change ∀ z,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem' z=mem z at hframe
  have hsame : ∀ z,R.foot b x z → mem z=mem' z := by
    intro z hz
    exact (hframe z (hfoot z hz).1 (hfoot z hz).2).symm
  have hh := hlocal b s x mem mem' hsame
  exact ⟨hh.1 hrep,hh.2⟩

end MinCostFlow.IPM.Machine
