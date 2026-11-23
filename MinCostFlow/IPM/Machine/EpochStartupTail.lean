module

public import MinCostFlow.IPM.Machine.EpochStartupGuard
import WordRAM.Tactic

/-!
# Execution of the startup range scan and failure return

The coefficient scan is read-only. Its bit alone decides whether
to return the initialized endpoint or append a failure flag there.
The scan and control overhead have an explicit linear bound.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual startup continuation runs the full scan, then returns
either its original successful record or a fresh rejection record. -/
theorem epochStartupTail_runs {w h scan flag names m g l neg mx mn L heap : ℕ}
    {p : Program} (st : State) (ω : ℕ → Bool)
    (hscan : MeetsContract w p scan (coefficientRangeListContract w h))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hargs : evalArgs w st epochStartupScanArgs=some [names,m,g,l,neg,mx,mn,L])
    (hwords : ∀ z∈[names,m,g,l,neg,mx,mn,L],z<2^w)
    (hpre : (coefficientRangeListContract w h).pre [names,m,g,l,neg,mx,mn,L] st.mem)
    (hheap : st.regs 18=heap) (hbit : st.mem (heap-1)=1)
    (hz : ZeroFrom st.mem heap) (hfit : heap+1<2^w) (hOne : 1<2^w) :
    ∃ v final cost bit,
      Runs w p ω (epochStartupTail scan flag) st (.returned v) final cost ∧
      (coefficientRangeListContract w h).post [names,m,g,l,neg,mx,mn,L] st.mem bit st.mem ∧
      (if bit=1 then v=heap ∧ final.mem=st.mem else
        (flagRecordContract w).post [0,heap] st.mem v final.mem) ∧
      final.mem (v-1)=bit ∧ cost≤m*(164*L+500)+150 := by
  obtain ⟨body,hbody,o,s,c,hRun,hPost,hCost⟩ :=
    hscan [names,m,g,l,neg,mx,mn,L] st.mem st.pos ω hwords hpre
  let after : State := ⟨s.mem,Function.update st.regs 19 o.value,s.pos⟩
  have hcall : Runs w p ω (.call 19 scan epochStartupScanArgs) st .normal after (c+15) := by
    apply runs_call_iff.mpr
    refine ⟨_,body,o,s,c,hargs,hbody,hRun,rfl,?_,?_⟩
    · cases s
      rfl
    · change c+15=14+c+1
      omega
  have hmem : after.mem=st.mem := hPost.1
  have hpost : (coefficientRangeListContract w h).post [names,m,g,l,neg,mx,mn,L] st.mem o.value st.mem :=
    hPost.1 ▸ hPost
  have hc : c≤m*(164*L+500)+100 := hCost
  have hreg : after.regs 18=heap := by simp [after,hheap]
  have readBit : Expr.eval w after (.reg 19)=some o.value := by simp [after,Expr.eval]
  by_cases hb : o.value=1
  · have hret : Runs w p ω (.ret (.reg 18)) after (.returned heap) after 2 :=
      runs_ret_iff.mpr ⟨heap,by simp [Expr.eval,hreg],rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.reg 19) (.ret (.reg 18))
        (.call 20 flag [.const 0,.reg 18] ;; .ret (.reg 20))) after (.returned heap) after 4 :=
      runs_cond_iff.mpr ⟨1,2,hb ▸ readBit,by simpa using hret,rfl⟩
    refine ⟨heap,after,c+20,o.value,runs_seq_iff.mpr (Or.inr ⟨after,_,_,hcall,hcond,by omega⟩),
      hpost,?_,?_,by omega⟩
    · rw [ite_eq_left hb]
      exact ⟨rfl,hmem⟩
    · rw [hmem,hbit,hb]
  · have hb0 : o.value=0 := by have hh := hPost.2.1; omega
    have hh : heap<2^w := by omega
    obtain ⟨flagBody,hflagBody,oF,sF,cF,hRF,hPF,hCF⟩ := hflag [0,heap] after.mem after.pos ω
      (by wram_words) ⟨⟨0,heap,rfl,by omega⟩,hmem.symm ▸ hz,hfit⟩
    let final : State := ⟨sF.mem,Function.update after.regs 20 oF.value,sF.pos⟩
    have hFcall : Runs w p ω (.call 20 flag [.const 0,.reg 18]) after .normal final (cF+3) := by
      apply runs_call_iff.mpr
      refine ⟨[0,heap],flagBody,oF,sF,cF,by eval_expr,hflagBody,hRF,rfl,?_,by change cF+3=2+cF+1; omega⟩
      cases sF
      rfl
    have hret : Runs w p ω (.ret (.reg 20)) final (.returned oF.value) final 2 :=
      runs_ret_iff.mpr ⟨oF.value,by simp [final,Expr.eval],rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.reg 19) (.ret (.reg 18))
        (.call 20 flag [.const 0,.reg 18] ;; .ret (.reg 20))) after (.returned oF.value) final (cF+8) :=
      runs_cond_iff.mpr ⟨0,cF+6,hb0 ▸ readBit,
        by simpa using runs_seq_iff.mpr (Or.inr ⟨final,cF+3,2,hFcall,hret,by omega⟩),by change cF+8=1+(cF+6)+1; omega⟩
    refine ⟨oF.value,final,c+cF+24,o.value,runs_seq_iff.mpr (Or.inr ⟨after,_,_,hcall,hcond,by omega⟩),
      hpost,?_,?_,?_⟩
    · rw [ite_eq_right hb]
      exact hmem ▸ hPF
    · exact (flagRecord_output hPF).trans hb0.symm
    · have hcF : cF≤20 := hCF
      omega

end MinCostFlow.IPM.Machine
