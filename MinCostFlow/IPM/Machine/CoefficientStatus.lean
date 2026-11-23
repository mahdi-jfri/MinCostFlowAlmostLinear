module

public import MinCostFlow.IPM.Machine.GuardedCoefficientFrame
public import MinCostFlow.IPM.Machine.FlagRecord
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# A uniform final status for guarded coefficient evaluation

Run the guarded coefficient procedure, then append its actual decision.
The returned heap minus one contains the status on both acceptance and
rejection. This gives the reported-edge loop a uniform stop test. Both
calls preserve a disjoint data-structure representation and its credit.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The arguments are those of `guardedCoefficientRefreshBody`. -/
def coefficientStatusBody (refresh flag : ℕ) : Stmt :=
  .call 16 refresh [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15] ;;
  .assign 17 (.load (.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 10)))) ;;
  .call 18 flag [.reg 17,.reg 16] ;;
  .ret (.reg 18)

/-- Guarded evaluation followed by a fresh status record. -/
def coefficientStatusModule (b h : ℕ) : List Stmt :=
  let f := b+1+(guardedCoefficientRefreshModule (b+1) h).length
  [coefficientStatusBody (b+1) f] ++
    (guardedCoefficientRefreshModule (b+1) h ++ flagRecordModule)

/-- The actual evaluation and final status write, with one extra word
beyond the guarded coefficient procedure's maximum workspace. -/
def coefficientStatusContract (w h q K : ℕ) : Contract where
  pre args mem := (guardedCoefficientRefreshContract w h q K).pre args mem ∧
    heapArg args+(4*args.getD 10 0+1)+args.getD 10 0+
      Num.IPM.lengthSpace (args.getD 10 0) (args.getD 11 0) (args.getD 12 0)+
      Num.IPM.gradientSpace (args.getD 10 0) (args.getD 11 0) (args.getD 12 0)+2<2^w
  post args mem v mem' := ∃ innerEnd innerMem,
    (guardedCoefficientRefreshContract w h q K).post args mem innerEnd innerMem ∧
    (flagRecordContract w).post
      [innerMem (heapArg args+4*args.getD 10 0),innerEnd] innerMem v mem'
  cost args mem := (guardedCoefficientRefreshContract w h q K).cost args mem+100

/-- The uniform-status wrapper and all its linked routines are deterministic. -/
theorem coefficientStatusModule_noRand (b h : ℕ) :
    ∀ body∈coefficientStatusModule b h,body.NoRand := by
  intro body hb
  simp only [coefficientStatusModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [coefficientStatusBody,Stmt.NoRand]
  · exact guardedCoefficientRefreshModule_noRand _ _ _ hb
  · have he : body=flagRecordBody := by simpa only [flagRecordModule,List.mem_singleton] using hb
    subst body
    exact flagRecord_noRand

/-- Both actual calls run within their full contracts and total explicit
cost, with the actual guard decision copied to the final status word. -/
theorem coefficientStatus_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (coefficientStatusModule b h)) :
    MeetsContract w p b (coefficientStatusContract w h q K) := by
  have ht := Num.hasAt_append_right hp
  have hg : p.HasAt (b+1) (guardedCoefficientRefreshModule (b+1) h) := Num.hasAt_append_left ht
  have hf := Num.hasAt_append_right ht
  have hguard := guardedCoefficientRefresh_meetsContract (q:=q) (K:=K) hh hw hg
  have hflag := flagRecord_meetsContract (w:=w) hf
  have hw4 : 4<2^w := lt_of_lt_of_le (by decide : 4<2^3)
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨hgpre,hspace⟩ := hpre
  have hdata := hgpre.1
  obtain ⟨m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap,rfl,_⟩ := hdata
  change heap+(4*L+1)+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+2<2^w at hspace
  apply runs_start_le
  unfold coefficientStatusBody
  refine runs_seq_call_le hguard
    (vs:=[m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap]) (by eval_expr) hwords hgpre ?_
  intro innerEnd innerMem innerPos hgpost
  have hframe := guardedCoefficientRefresh_frame hgpost
  have hbit := hframe.2.2.2.2
  have hupper := hframe.2.1
  have hinnerW : innerEnd<2^w := by omega
  have hslotW : heap+4*L<2^w := by omega
  have hbitW : innerMem (heap+4*L)<2^w := by omega
  wram_step
  refine runs_seq_call_le hflag (vs:=[innerMem (heap+4*L),innerEnd]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨⟨_,innerEnd,rfl,hbit⟩,hframe.2.2.1,by change innerEnd+1<2^w; omega⟩
  · intro v mem1 pos1 hfpost
    have hv := hfpost.2
    change v=innerEnd+1 at hv
    have hvW : v<2^w := by omega
    refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
    · exact ⟨innerEnd,innerMem,hgpost,hfpost⟩
    · simp only [coefficientStatusContract,guardedCoefficientRefreshContract,flagRecordContract,
        heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
        Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
      omega

/-- The status wrapper preserves a disjoint data structure and its exact
potential through both numerical evaluation and the final status write. -/
theorem coefficientStatus_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w h q K m c r lo f up a one mn mx L P E ld gd heap v b : ℕ}
    {mem mem' : ℕ → ℕ} {s : σ} {x : R.τ}
    (hout : (coefficientStatusContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem')
    (hrep : R.rep b s x mem)
    (hfoot : ∀ z,R.foot b x z → z<heap ∧ (z<ld ∨ ld+L≤z) ∧ (z<gd ∨ gd+L≤z)) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' := by
  obtain ⟨innerEnd,innerMem,hg,hf⟩ := hout
  have hkeep := guardedCoefficientRefresh_preserves_state R hlocal hg hrep hfoot
  have hlo := (guardedCoefficientRefresh_frame hg).1
  have hfinal := flagRecord_preserves_state R hlocal hf hkeep.1
    (fun z hz => (hfoot z hz).1.trans_le hlo)
  exact ⟨hfinal.1,hkeep.2.trans hfinal.2⟩

/-- The final returned-heap status is a bit on every branch. -/
theorem coefficientStatus_bit {w h q K m c r lo f up a one mn mx L P E ld gd heap v : ℕ}
    {mem mem' : ℕ → ℕ}
    (hout : (coefficientStatusContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem') : mem' (v-1)≤1 := by
  obtain ⟨innerEnd,innerMem,hg,hf⟩ := hout
  rw [flagRecord_output hf]
  exact (guardedCoefficientRefresh_frame hg).2.2.2.2

end MinCostFlow.IPM.Machine
