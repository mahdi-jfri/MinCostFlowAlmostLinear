module

public import MinCostFlow.Num.IPM.Slacks
public import MinCostFlow.IPM.Machine.StrictRange
import MinCostFlow.Num.WordBounds
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Checking stored slacks before numerical powers

Compute both slack differences exactly, then test each against the
represented range endpoints. Only accepted coordinates may be passed
to the power and gradient procedures. This test is valid for rejected
targets too: its exact subtraction premises follow from the preceding
capacity guard, without a global feasible-run assumption.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[lower,flow,upper,minimum,maximum,L,P,heap]`.
The acceptance bit is written after the four-block slack workspace. -/
def guardedSlacksBody (slacks range : ℕ) : Stmt :=
  .call 8 slacks [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 7] ;;
  .call 9 range [.reg 3,.bin .add (.reg 7) (.reg 5),.reg 4,.reg 5] ;;
  .call 10 range [.reg 3,.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 5)),.reg 4,.reg 5] ;;
  .store (.reg 8) (.bin .mul (.reg 9) (.reg 10)) ;;
  .ret (.bin .add (.reg 8) (.const 1))

/-- The exact slack module and the shared read-only interval guard. -/
def guardedSlacksModule (b h : ℕ) : List Stmt :=
  let range := b+1+(Num.IPM.slacksModule (b+1) h).length
  [guardedSlacksBody (b+1) range] ++
    (Num.IPM.slacksModule (b+1) h ++ strictRangeModule range h)

/-- Acceptance is exactly membership of both true slacks in the guarded
range. The old source prefix is preserved. -/
def guardedSlacksContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ lo fp up mn mx L P heap,args=[lo,fp,up,mn,mx,L,P,heap] ∧
      (Num.IPM.slacksContract w h).pre [lo,fp,up,L,P,heap] mem ∧ mn+L ≤ heap ∧ mx+L ≤ heap ∧
      Num.Valid mem mn h L ∧ Num.Valid mem mx h L)
    (fun args mem mem' =>
      let L := args.getD 5 0
      let P := args.getD 6 0
      let lo := Num.fixVal mem (args.getD 0 0) h L P
      let f := Num.fixVal mem (args.getD 1 0) h L P
      let up := Num.fixVal mem (args.getD 2 0) h L P
      let mn := Num.fixVal mem (args.getD 3 0) h L P
      let mx := Num.fixVal mem (args.getD 4 0) h L P
      mem' (heapArg args+4*L) ≤ 1 ∧
      (mem' (heapArg args+4*L)=1 ↔ (mn < up-f ∧ up-f < mx) ∧ (mn < f-lo ∧ f-lo < mx)))
    (fun args _ => 400*args.getD 5 0+600) (fun args _ => 4*args.getD 5 0+1)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+(4*args.getD 5 0+1)}

/-- Exact differences and both range guards contain no randomness. -/
theorem guardedSlacksModule_noRand (b h : ℕ) : ∀ body ∈ guardedSlacksModule b h,body.NoRand := by
  intro body hb
  simp only [guardedSlacksModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [guardedSlacksBody,Stmt.NoRand]
  · exact Num.IPM.slacksModule_noRand _ _ _ hb
  · exact strictRangeModule_noRand _ _ _ hb

/-- Actual exact slack differences are checked before numerical powers,
with both guards, all calls, allocation and the stored flag counted. -/
theorem guardedSlacks_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hp : p.HasAt b (guardedSlacksModule b h)) :
    MeetsContract w p b (guardedSlacksContract w h) := by
  have ht := Num.hasAt_append_right hp
  have hs : p.HasAt (b+1) (Num.IPM.slacksModule (b+1) h) := Num.hasAt_append_left ht
  have hg : p.HasAt (b+1+(Num.IPM.slacksModule (b+1) h).length)
      (strictRangeModule (b+1+(Num.IPM.slacksModule (b+1) h).length) h) := Num.hasAt_append_right ht
  have hw1 : 1 < 2^w := lt_of_lt_of_le (by decide : 1 < 2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := Num.base_lt_word hw
  have hsSpec := Num.IPM.slacks_meetsContract hh hw hs
  have hgSpec := strictRange_meetsContract hh hw1 hb hg
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨lo,fp,up,mn,mx,L,P,heap,rfl,hslack,hminEnd,hmaxEnd,hvmin,hvmax⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(4*L+1) < 2^w at hspace
  have hargWords : ∀ x ∈ [lo,fp,up,L,P,heap],x < 2^w := by
    intro x hx
    apply hwords x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    tauto
  have hmnW : mn < 2^w := hwords _ (by simp)
  have hmxW : mx < 2^w := hwords _ (by simp)
  have hLW : L < 2^w := hwords _ (by simp)
  have hhW : heap < 2^w := hwords _ (by simp)
  have hthree : 3 < 2^w := by
    have hw2 := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 2 ≤ w by omega)
    omega
  apply runs_start_le
  unfold guardedSlacksBody
  refine runs_seq_call_le hsSpec (vs:=[lo,fp,up,L,P,heap]) (by eval_expr) hargWords hslack ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨hv0,_,_,hframe0,hfresh0,hvu,hvd,hvalU,hvalD⟩ := hp0
  change v0=heap+4*L at hv0
  change ∀ x < heap,mem0 x=mem x at hframe0
  change Num.Valid mem0 (heap+L) h L at hvu
  change Num.Valid mem0 (heap+3*L) h L at hvd
  change Num.fixVal mem0 (heap+L) h L P=Num.fixVal mem up h L P-Num.fixVal mem fp h L P at hvalU
  change Num.fixVal mem0 (heap+3*L) h L P=Num.fixVal mem fp h L P-Num.fixVal mem lo h L P at hvalD
  have hv0W : v0 < 2^w := by omega
  have hmin0 : ScalarAt mem0 mn h L P (Num.fixVal mem mn h L P) :=
    ⟨Num.IPM.valid_frozen hframe0 hminEnd hvmin,Num.IPM.fixVal_frozen hframe0 hminEnd⟩
  have hmax0 : ScalarAt mem0 mx h L P (Num.fixVal mem mx h L P) :=
    ⟨Num.IPM.valid_frozen hframe0 hmaxEnd hvmax,Num.IPM.fixVal_frozen hframe0 hmaxEnd⟩
  refine runs_seq_call_le hgSpec (vs:=[mn,heap+L,mx,L]) (by eval_expr) (by wram_words)
    ⟨mn,heap+L,mx,L,rfl,by omega,by omega,by omega,hmin0.1,hvu,hmax0.1⟩ ?_
  intro bU mem1 pos1 hp1
  obtain ⟨hm1,hbU⟩ := hp1
  change mem1=mem0 at hm1
  subst mem1
  have hUiff := strictRange_output (w:=w) (And.intro rfl hbU) hmin0 (And.intro hvu hvalU) hmax0
  have hUb : bU ≤ 1 := by
    change bU=if _ then 1 else 0 at hbU
    split_ifs at hbU <;> omega
  refine runs_seq_call_le hgSpec (vs:=[mn,heap+3*L,mx,L]) (by eval_expr) (by wram_words)
    ⟨mn,heap+3*L,mx,L,rfl,by omega,by omega,by omega,hmin0.1,hvd,hmax0.1⟩ ?_
  intro bD mem2 pos2 hp2
  obtain ⟨hm2,hbD⟩ := hp2
  change mem2=mem0 at hm2
  subst mem2
  have hDiff := strictRange_output (w:=w) (And.intro rfl hbD) hmin0 (And.intro hvd hvalD) hmax0
  have hDb : bD ≤ 1 := by
    change bD=if _ then 1 else 0 at hbD
    split_ifs at hbD <;> omega
  have hprod : bU*bD ≤ 1 := Nat.mul_le_mul hUb hDb
  have hmul : bU*bD=1 ↔ bU=1 ∧ bD=1 := by
    rcases (show bU=0 ∨ bU=1 by omega) with rfl | rfl <;> simp
  have hprodW : bU*bD < 2^w := hprod.trans_lt hw1
  wram_step
  refine runs_ret_le (v:=v0+1) (by eval_expr) ?_ ?_
  · change (heap ≤ v0+1 ∧ v0+1 ≤ heap+(4*L+1) ∧
      (∀ x < heap,(Function.update mem0 v0 (bU*bD)) x=mem x) ∧
      ZeroFrom (Function.update mem0 v0 (bU*bD)) (v0+1) ∧
      (Function.update mem0 v0 (bU*bD)) (heap+4*L) ≤ 1 ∧
      ((Function.update mem0 v0 (bU*bD)) (heap+4*L)=1 ↔ _)) ∧ v0+1=heap+(4*L+1)
    refine ⟨⟨by omega,by omega,?_,?_,?_,?_⟩,by omega⟩
    · intro x hx
      rw [Function.update_of_ne (by omega : x ≠ v0)]
      exact hframe0 x hx
    · intro x hx
      rw [Function.update_of_ne (by omega : x ≠ v0)]
      exact hfresh0 x (by omega)
    · simpa only [← hv0,Function.update_self] using hprod
    · simp only [← hv0,Function.update_self,hmul]
      exact and_congr hUiff hDiff
  · simp only [guardedSlacksContract,Num.IPM.slacksContract,strictRangeContract,heapContract,
      List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,Expr.size_const,
      argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
