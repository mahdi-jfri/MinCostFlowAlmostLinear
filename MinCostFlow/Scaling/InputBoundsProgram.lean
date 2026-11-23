module

public import MinCostFlow.Scaling.StridedMaxProgram
public import MinCostFlow.Scaling.MaxWordsProgram
public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Scaling.InputLayout
import MinCostFlow.Scaling.InputBoundsScanFacts
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.InputMaxLayout
import WordRAM.Tactic

/-!
# Computing the input's exact cost and capacity bounds

Four scans read the lower, upper, cost, and demand magnitude fields.
Two comparisons combine the capacity fields. The procedure writes the
statement's exact cost and capacity maxima in two fresh heap cells, which
the whole program passes to the arbitrary-demand reduction.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[input,heap]`; return the end of `[maxCost,maxCapacity]`. -/
def inputBoundsBody (scan combine pair : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 scan [.bin .add (.reg 0) (.const 5),.reg 3,.const 8] ;;
  .call 5 scan [.bin .add (.reg 0) (.const 7),.reg 3,.const 8] ;;
  .call 6 scan [.bin .add (.reg 0) (.const 9),.reg 3,.const 8] ;;
  .call 7 scan [.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 8) (.reg 3)),.reg 2,.const 2] ;;
  .call 8 combine [.reg 4,.reg 5] ;;
  .call 9 combine [.reg 8,.reg 7] ;;
  .call 10 pair [.reg 6,.reg 9,.reg 1] ;;
  .ret (.reg 10)

/-- The input scanner and its three shared helpers. -/
def inputBoundsModule (b : ℕ) : List Stmt :=
  inputBoundsBody (b+1) (b+2) (b+3) ::
    (stridedMaxModule (b+1) ++ (maxWordsModule ++ wordPairModule))

/-- The source precedes the heap and has enough address slack for all
four scans. The result has exactly the pair writer's frames and layout. -/
def inputBoundsContract (w : ℕ) (I : Instance) : Contract where
  pre args mem := ∃ a heap,args=[a,heap] ∧ ListAt mem a I.encode ∧
    a+I.encode.length≤heap ∧ a+I.encode.length+10<2^w ∧
    I.maxCost<2^w ∧ I.maxCapacity<2^w ∧ ZeroFrom mem heap ∧ heap+2<2^w
  post args mem ret mem' := (wordPairContract w).post [I.maxCost,I.maxCapacity,heapArg args] mem ret mem'
  cost _ _ := 1000*(I.m+I.n+1)

/-- Reading the input bounds uses no random instruction. -/
theorem inputBoundsModule_noRand (b : ℕ) : ∀ body∈inputBoundsModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [inputBoundsBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact stridedMaxModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact maxWordsModule_noRand body hb
      · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hb
        subst body
        exact wordPairBody_noRand

set_option maxRecDepth 4096 in
/-- The entry scan computes the statement's exact bounds in linear time,
with two fresh cells and the complete heap frame. -/
theorem inputBounds_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (inputBoundsModule b)) (I : Instance) (hv : I.IsValid) :
    MeetsContract w p b (inputBoundsContract w I) := by
  have ht : p.HasAt (b+1) (stridedMaxModule (b+1) ++ (maxWordsModule ++ wordPairModule)) := hasAt_tail hp
  have hscan := hasAt_append_left ht
  have ht' : p.HasAt (b+2) (maxWordsModule ++ wordPairModule) := hasAt_append_right ht
  have hmax := hasAt_append_left ht'
  have hpair : p.HasAt (b+3) wordPairModule := hasAt_append_right ht'
  let L := (I.edges.map (fun e => e.lower.natAbs)).foldr max 0
  let H := (I.edges.map (fun e => e.upper.natAbs)).foldr max 0
  let D := (I.demand.map Int.natAbs).foldr max 0
  have hUeq : max (max L H) D=I.maxCapacity := (maxCapacity_eq_field_maxima I).symm
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hat,hend,hs,hC,hU,hzero,hspace⟩ := hpre
  obtain ⟨hpl,hph,hpc,hpd⟩ := inputBounds_scan_pre w I hv mem a hat hs hC hU
  have hlen := instance_encode_length I hv
  have h8 : 8<2^w := by omega
  have h1 : 1<2^w := by omega
  have hn : I.n<2^w := by omega
  have hm : I.m<2^w := by omega
  have hh : heap<2^w := by omega
  have ha1 : a+1<2^w := by omega
  have ha5 : a+5<2^w := by omega
  have ha7 : a+7<2^w := by omega
  have ha9 : a+9<2^w := by omega
  have ha3 : a+3<2^w := by omega
  have h8m : 8*I.m<2^w := by omega
  have had : a+3+8*I.m<2^w := by omega
  have hL : L<2^w := by obtain ⟨_,_,_,_,_,h,_⟩ := hpl; exact h
  have hH : H<2^w := by obtain ⟨_,_,_,_,_,h,_⟩ := hph; exact h
  have hD : D<2^w := by obtain ⟨_,_,_,_,_,h,_⟩ := hpd; exact h
  have hLH : max L H<2^w := max_lt hL hH
  obtain ⟨hheaderN,hheaderM⟩ := instance_header_at I mem a hat
  apply runs_start_le
  unfold inputBoundsBody
  refine runs_seq_assign_le (v := I.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
  refine runs_seq_call_le (stridedMax_meetsContract (w := w) hscan (I.edges.map (fun e => e.lower.natAbs)))
    (vs := [a+5,I.m,8]) (by eval_expr) (by wram_words) hpl ?_
  intro l memL posL hpL
  change memL=mem ∧ l=L at hpL
  obtain ⟨hmemL,hretL⟩ := hpL
  subst memL
  subst l
  refine runs_seq_call_le (stridedMax_meetsContract (w := w) hscan (I.edges.map (fun e => e.upper.natAbs)))
    (vs := [a+7,I.m,8]) (by eval_expr) (by wram_words) hph ?_
  intro h memH posH hpH
  change memH=mem ∧ h=H at hpH
  obtain ⟨hmemH,hretH⟩ := hpH
  subst memH
  subst h
  refine runs_seq_call_le (stridedMax_meetsContract (w := w) hscan (I.edges.map (fun e => e.cost.natAbs)))
    (vs := [a+9,I.m,8]) (by eval_expr) (by wram_words) hpc ?_
  intro c memC posC hpC
  change memC=mem ∧ c=I.maxCost at hpC
  obtain ⟨hmemC,hretC⟩ := hpC
  subst memC
  subst c
  refine runs_seq_call_le (stridedMax_meetsContract (w := w) hscan (I.demand.map Int.natAbs))
    (vs := [a+3+8*I.m,I.n,2]) (by eval_expr) (by wram_words) hpd ?_
  intro d memD posD hpD
  change memD=mem ∧ d=D at hpD
  obtain ⟨hmemD,hretD⟩ := hpD
  subst memD
  subst d
  refine runs_seq_call_le (maxWords_meetsContract (w := w) hmax L H)
    (vs := [L,H]) (by eval_expr) (by wram_words) ⟨rfl,h1⟩ ?_
  intro lh memLH posLH hpLH
  change memLH=mem ∧ lh=max L H at hpLH
  obtain ⟨hmemLH,hretLH⟩ := hpLH
  subst memLH
  subst lh
  refine runs_seq_call_le (maxWords_meetsContract (w := w) hmax (max L H) D)
    (vs := [max L H,D]) (by eval_expr) (by wram_words) ⟨rfl,h1⟩ ?_
  intro u memU posU hpU
  change memU=mem ∧ u=max (max L H) D at hpU
  rw [hUeq] at hpU
  obtain ⟨hmemU,hretU⟩ := hpU
  subst memU
  subst u
  refine runs_seq_call_le (wordPair_meetsContract (w := w) hpair)
    (vs := [I.maxCost,I.maxCapacity,heap]) (by eval_expr) (by wram_words)
    ⟨⟨I.maxCost,I.maxCapacity,heap,rfl⟩,hzero,hspace⟩ ?_
  intro ret memR posR hpR
  have hr : ret=heap+2 := hpR.2
  have hrw : ret<2^w := by omega
  refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
  · exact hpR
  · simp only [inputBoundsContract,stridedMaxContract,maxWordsContract,wordPairContract,heapContract,
      List.length_map,hv.2,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    have he : I.edges.length=I.m := rfl
    omega

end MinCostFlow.Scaling.Machine
