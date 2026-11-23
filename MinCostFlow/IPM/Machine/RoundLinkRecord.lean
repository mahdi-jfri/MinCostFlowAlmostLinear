module

public import MinCostFlow.IPM.Machine.RoundAppendBlock
import WordRAM.Tactic

/-!
# Packing an exact edge for Link

The edge identifier and endpoints precede the signed cost, exact
flow and its two availabilities. The four blocks are copied without
any arithmetic or change of scale.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [eid,u,v,cost,flow,forward,backward,L,heap], write the edge record. -/
def roundLinkRecordBody (append : ℕ) : Stmt :=
  .store (.reg 8) (.reg 0) ;;
  .store (.bin .add (.reg 8) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 8) (.const 2)) (.reg 2) ;;
  .call 9 append [.reg 3,.reg 7,.bin .add (.reg 8) (.const 3)] ;;
  .call 9 append [.reg 4,.reg 7,.reg 9] ;;
  .call 9 append [.reg 5,.reg 7,.reg 9] ;;
  .call 9 append [.reg 6,.reg 7,.reg 9] ;;
  .ret (.reg 9)

/-- An edge record occupies exactly three words and four blocks. -/
def roundLinkRecordContract (w h P : ℕ) (e : ForestEdge) : Contract :=
  let c := heapContract w
    (fun args mem => ∃ c f a b L heap,args=[e.eid,e.u,e.v,c,f,a,b,L,heap] ∧
      c+L≤heap ∧ f+L≤heap ∧ a+L≤heap ∧ b+L≤heap ∧
      RatAt mem c h L 0 e.cost ∧ RatAt mem f h L P e.flow ∧
      RatAt mem a h L P e.availFwd ∧ RatAt mem b h L P e.availBwd)
    (fun args _ final => ForestEdgeAt final (heapArg args) h (args.getD 7 0) P e)
    (fun args _ => 68*args.getD 7 0+140) (fun args _ => 3+4*args.getD 7 0)
  {c with post := fun args mem v final => c.post args mem v final ∧ v=heapArg args+3+4*args.getD 7 0}

/-- Edge record creation consists of deterministic stores and copies. -/
theorem roundLinkRecord_noRand (append : ℕ) : (roundLinkRecordBody append).NoRand := by
  simp [roundLinkRecordBody,Stmt.NoRand]

private theorem append_pre {w src L heap : ℕ} {mem : ℕ → ℕ}
    (hs : src+L≤heap) (hw : 1<2^w) (hz : ZeroFrom mem heap) (hfit : heap+L<2^w) :
    (roundAppendBlockContract w).pre [src,L,heap] mem :=
  ⟨⟨src,L,heap,rfl,hs,hw⟩,hz,hfit⟩

private theorem append_post {w src L heap v : ℕ} {mem final : ℕ → ℕ}
    (hout : (roundAppendBlockContract w).post [src,L,heap] mem v final) :
    v=heap+L ∧ ZeroFrom final v ∧ ∀ z<heap,final z=mem z :=
  ⟨hout.2,hout.1.2.2.2.1,hout.1.2.2.1⟩

set_option maxHeartbeats 450000 in
/-- Packing preserves every allocated cell below the new record and
makes its full exact encoding available to the forest Link call. -/
theorem roundLinkRecord_meetsContract {w h P entry append : ℕ} {p : Program}
    (hBody : p.procs[entry]?=some (roundLinkRecordBody append))
    (hAppend : MeetsContract w p append (roundAppendBlockContract w))
    (e : ForestEdge) : MeetsContract w p entry (roundLinkRecordContract w h P e) := by
  apply meetsContract_of_runs hBody
  intro args mem pos ω hwords hpre
  obtain ⟨⟨ac,af,ap,ab,L,heap,rfl,hc,hf,hp,hb,hCost,hFlow,hFwd,hBwd⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(3+4*L)<2^w at hspace
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hThree : 3<2^w := by omega
  have hHeap : heap<2^w := by omega
  have hH1 : heap+1<2^w := by omega
  have hH2 : heap+2<2^w := by omega
  have hH3 : heap+3<2^w := by omega
  have hCostW : ac<2^w := hwords _ (by simp)
  have hFlowW : af<2^w := hwords _ (by simp)
  have hFwdW : ap<2^w := hwords _ (by simp)
  have hBwdW : ab<2^w := hwords _ (by simp)
  have hL : L<2^w := hwords _ (by simp)
  let hdr := Function.update (Function.update (Function.update mem heap e.eid) (heap+1) e.u) (heap+2) e.v
  have hHeader : ListAt hdr heap [e.eid,e.u,e.v] := by
    intro j hj
    have hlt : j<3 := hj
    have h : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases h with rfl | rfl | rfl <;> simp [hdr]
  have hOld : ∀ z<heap,hdr z=mem z := by
    intro z zlt
    simp [hdr,Function.update_of_ne (show z≠heap from by omega),
      Function.update_of_ne (show z≠heap+1 from by omega),Function.update_of_ne (show z≠heap+2 from by omega)]
  have hFresh : ZeroFrom hdr (heap+3) := by
    intro z hz'
    rw [show hdr z=mem z by
      simp [hdr,Function.update_of_ne (show z≠heap from by omega),
        Function.update_of_ne (show z≠heap+1 from by omega),Function.update_of_ne (show z≠heap+2 from by omega)]]
    exact hz z (by omega)
  apply runs_start_le
  unfold roundLinkRecordBody
  wram_step
  wram_step
  wram_step
  have hh₁ : heap+3+L<2^w := by omega
  refine runs_seq_call_le hAppend (vs:=[ac,L,heap+3]) (by eval_expr) (by wram_words)
    (append_pre (by omega) hOne hFresh hh₁) ?_
  intro h₁ mem₁ pos₁ hout₁
  obtain ⟨he₁,hz₁,hframe₁⟩ := append_post hout₁
  have hFit₁ : h₁<2^w := by omega
  have hFit₂ : h₁+L<2^w := by omega
  refine runs_seq_call_le hAppend (vs:=[af,L,h₁]) (by eval_expr) (by wram_words)
    (append_pre (by omega) hOne hz₁ hFit₂) ?_
  intro h₂ mem₂ pos₂ hout₂
  obtain ⟨he₂,hz₂,hframe₂⟩ := append_post hout₂
  have hFit₃ : h₂<2^w := by omega
  have hFit₃' : h₂+L<2^w := by omega
  refine runs_seq_call_le hAppend (vs:=[ap,L,h₂]) (by eval_expr) (by wram_words)
    (append_pre (by omega) hOne hz₂ hFit₃') ?_
  intro h₃ mem₃ pos₃ hout₃
  obtain ⟨he₃,hz₃,hframe₃⟩ := append_post hout₃
  have hFit₄ : h₃<2^w := by omega
  have hFit₄' : h₃+L<2^w := by omega
  refine runs_seq_call_le hAppend (vs:=[ab,L,h₃]) (by eval_expr) (by wram_words)
    (append_pre (by omega) hOne hz₃ hFit₄') ?_
  intro h₄ mem₄ pos₄ hout₄
  obtain ⟨he₄,hz₄,hframe₄⟩ := append_post hout₄
  have hf₁ : ∀ z<heap,mem₁ z=mem z := fun z h => (hframe₁ z (by omega)).trans (hOld z h)
  have hf₂ : ∀ z<heap,mem₂ z=mem z := fun z h => (hframe₂ z (by omega)).trans (hf₁ z h)
  have hf₃ : ∀ z<heap,mem₃ z=mem z := fun z h => (hframe₃ z (by omega)).trans (hf₂ z h)
  have hcd := roundAppendBlock_rat (hCost.frozen hOld hc) hout₁
  have hfd := roundAppendBlock_rat (hFlow.frozen hf₁ hf) hout₂
  have hpd := roundAppendBlock_rat (hFwd.frozen hf₂ hp) hout₃
  have hbd := roundAppendBlock_rat (hBwd.frozen hf₃ hb) hout₄
  have hcd' := ((hcd.frozen hframe₂ he₁.ge).frozen hframe₃ (by omega)).frozen hframe₄ (by omega)
  have hfd' := (hfd.frozen hframe₃ he₂.ge).frozen hframe₄ (by omega)
  have hpd' := hpd.frozen hframe₄ he₃.ge
  refine runs_ret_le (v:=h₄) rfl ?_ ?_
  · change (heap≤h₄ ∧ h₄≤heap+(3+4*L) ∧ (∀ z<heap,mem₄ z=mem z) ∧
      ZeroFrom mem₄ h₄ ∧ ForestEdgeAt mem₄ heap h L P e) ∧ h₄=heap+3+4*L
    have hHeads : ListAt mem₄ heap [e.eid,e.u,e.v] := by
      intro j hj
      have hh : j<3 := hj
      exact (hframe₄ (heap+j) (by omega)).trans ((hframe₃ (heap+j) (by omega)).trans
        ((hframe₂ (heap+j) (by omega)).trans ((hframe₁ (heap+j) (by omega)).trans (hHeader j hj))))
    refine ⟨⟨by omega,by omega,fun z h => (hframe₄ z (by omega)).trans (hf₃ z h),hz₄,
      hHeads,hcd'.1,?_,?_,?_,?_⟩,by omega⟩
    · simpa [readRat] using hcd'.2
    · simpa only [he₁] using hfd'
    · rwa [show heap+3+2*L=h₂ by omega]
    · rwa [show heap+3+3*L=h₃ by omega]
  · simp only [roundLinkRecordContract,roundAppendBlockContract,heapContract,List.getD_cons_succ,
      List.getD_cons_zero,argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
