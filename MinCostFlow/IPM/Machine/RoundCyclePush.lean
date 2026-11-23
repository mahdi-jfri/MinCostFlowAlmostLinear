module

public import MinCostFlow.IPM.Machine.RoundCycleEdge
public import MinCostFlow.IPM.Machine.RoundStoreCoordinate
public import MinCostFlow.IPM.Machine.RoundCleanupProgram
public import MinCostFlow.IPM.Machine.RoundPathAdd
import WordRAM.Tactic

/-!
# Pushing the selected cycle correction

The forest path minimum chooses an exact dyadic increment. The
new coordinate is written before PathAdd so that any temporary
path answer used as the delta stays live until both uses.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [forest,from,to,availability,coordinate,L,backward,heap],
update the new edge and push the same delta through the forest. -/
def roundCyclePushBody (pathMin delta coordinate pathAdd : ℕ) : Stmt :=
  .call 8 pathMin [.reg 0,.reg 1,.reg 2,.reg 5,.reg 7] ;;
  .call 9 delta [.reg 3,.reg 7,.reg 5,.reg 8] ;;
  .call 8 coordinate [.reg 4,.reg 9,.reg 5,.reg 6,.reg 8] ;;
  .call 8 pathAdd [.reg 0,.reg 1,.reg 2,.reg 9,.reg 8] ;;
  .ret (.reg 8)

/-- Cycle correction uses deterministic numerical and forest calls. -/
theorem roundCyclePush_noRand (pathMin delta coordinate pathAdd : ℕ) :
    (roundCyclePushBody pathMin delta coordinate pathAdd).NoRand := by
  simp [roundCyclePushBody,Stmt.NoRand]

set_option maxHeartbeats 650000 in
/-- The machine correction uses the exact path minimum and updates
both the table and forest at that increment. The frame excludes
only the changed table coordinate below the forest handle. -/
theorem roundCyclePush_runs {w h L P pathMin delta coordinate pathAdd A : ℕ}
    (D : DynForest) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hMin : p.procs[pathMin]?=some (roundForestPathMinBody (op 4)))
    (hDelta : ∀ q hit,MeetsContract w p delta (roundDeltaContract w h P q hit))
    (hCoord : ∀ q δ backward,MeetsContract w p coordinate (roundStoreCoordinateContract w h P q δ backward))
    (hAdd : p.procs[pathAdd]?=some (roundPathAddBody (op 3)))
    (hAlloc : ∀ b u v a heap,allocation 4 [b,u,v,heap]≤A ∧ allocation 3 [b,u,v,a,heap]≤A)
    (b u v ap fp heap : ℕ) (backward : Bool) (q avail : ℚ)
    (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hWords : ∀ z∈[b,u,v,ap,fp,L,backward.toNat,heap],z<2^w)
    (hL : 0<L) (hAp : ap+L≤heap) (hApart : fp+L≤ap) (hFp : fp+L≤b) (hb : b≤heap)
    (hQ : RatAt mem fp h L P q) (hAvail : RatAt mem ap h L P avail)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s) (hComp : (D.toForest s).SameComp u v)
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hAvailFrame : ∀ z,R.foot b x z → z<ap ∨ ap+L≤z)
    (hFresh : ZeroFrom mem heap) (hSpace : heap+2*A+4+4*L<2^w)
    (hFitting : let δ := (D.pathMin s u v).elim avail (fun e => min avail e.avail)
      RatFits h L P (if backward then q-δ else q+δ) ∧ ForestFits D h L P (D.pathAdd s u v δ)) :
    let δ := (D.pathMin s u v).elim avail (fun e => min avail e.avail)
    ∃ out final cost y,
      Runs w p ω (roundCyclePushBody pathMin delta coordinate pathAdd)
        (startState [b,u,v,ap,fp,L,backward.toNat,heap] mem pos) (.returned out) final cost ∧
      R.rep b (D.pathAdd s u v δ) y final.mem ∧
      RatAt final.mem fp h L P (if backward then q-δ else q+δ) ∧
      heap≤out ∧ out≤heap+2*A+4+4*L ∧ ZeroFrom final.mem out ∧
      (∀ z<b,z<fp ∨ fp+L≤z → final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤2*rate (D.toForest s).n+132*L+250+R.phi b x mem := by
  dsimp only at hFitting ⊢
  let value := (D.pathMin s u v).elim avail (fun e => min avail e.avail)
  let parent := startState [b,u,v,ap,fp,L,backward.toNat,heap] mem pos
  have hw₀ : ∀ z∈[b,u,v,L,heap],z<2^w := by
    intro z hz
    apply hWords
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  have ha₀ := (hAlloc b u v ap heap).1
  obtain ⟨h₁,raw₁,c₁,x₁,hR₁,hHit,hRep₁,hLo₁,hHi₁,hW₁,hZero₁,hMem₁,hFoot₁,hC₁⟩ :=
    roundForestPathMin_runs D rate allocation R himpl b u v heap s x mem pos ω hw₀ (by omega)
      hInv hFit hComp hRep (fun z hz => (hFoot z hz).2) hFresh (by omega)
  have hFrame₁ : ∀ z<b,raw₁.mem z=mem z :=
    fun z hz => hMem₁ z (hz.trans_le hb) (fun hf => (Nat.not_le_of_lt hz) (hFoot z hf).1)
  have hFoot₁' : ∀ z,R.foot b x₁ z → b≤z ∧ z<h₁ := by
    intro z hz
    rcases hFoot₁ z hz with ho | ⟨hl,hh⟩
    · exact ⟨(hFoot z ho).1,(hFoot z ho).2.trans_le (by omega)⟩
    · exact ⟨hb.trans hl,hh⟩
  let s₁ : State := ⟨raw₁.mem,Function.update parent.regs 8 h₁,raw₁.pos⟩
  have hArgs₁ : evalArgs w parent [.reg 0,.reg 1,.reg 2,.reg 5,.reg 7]=some [b,u,v,L,heap] := rfl
  have hCall₁ := round_returning_call (dst:=8) hMin hArgs₁ hR₁
  have hArgs₂ : evalArgs w s₁ [.reg 3,.reg 7,.reg 5,.reg 8]=some [ap,heap,L,h₁] := rfl
  have hw₂ : ∀ z∈[ap,heap,L,h₁],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · exact hW₁
  have hab : ap+L≤h₁ := by omega
  have hAvail₁ := hAvail.agree (mem':=s₁.mem) fun i hi =>
    hMem₁ _ (by omega) (fun hf => by
      rcases hAvailFrame (ap+i) hf with hh | hh <;> omega)
  have hPre₂ : (roundDeltaContract w h P avail (D.pathMin s u v)).pre [ap,heap,L,h₁] s₁.mem :=
    ⟨ap,heap,L,h₁,rfl,hL,hab,hLo₁,hW₁,hAvail₁,hHit⟩
  obtain ⟨s₂,c₂,dp,hCall₂,hOut₂,hDp,hRegs₂,hC₂⟩ :=
    runs_call_of_meetsContract (r:=9) (hDelta avail (D.pathMin s u v)) hArgs₂ hw₂ hPre₂ ω
  obtain ⟨hEq₂,hBt,hValue₂,hLoc₂⟩ := hOut₂
  have hm₂ : s₂.mem=raw₁.mem := hEq₂
  have hd : dp+L≤h₁ := hBt
  have hOld₂ : ∀ z<b,s₂.mem z=mem z := fun z hz => (congrFun hm₂ z).trans (hFrame₁ z hz)
  have hReg₂ (j : ℕ) (hj : j<8) : s₂.regs j=parent.regs j := by
    rw [hRegs₂ j (by omega)]
    exact Function.update_of_ne (show j≠8 by omega) _ _
  have hHeap₂ : s₂.regs 8=h₁ := (hRegs₂ 8 (by decide)).trans (by simp [s₁])
  have hSpace₃ : h₁+(if backward then 2*L else L)<2^w := by
    cases backward <;> simp <;> omega
  have hArgs₃ : evalArgs w s₂ [.reg 4,.reg 9,.reg 5,.reg 6,.reg 8]=
      some [fp,dp,L,backward.toNat,h₁] := by
    have h₄ : s₂.regs 4=fp := hReg₂ 4 (by decide)
    have h₅ : s₂.regs 5=L := hReg₂ 5 (by decide)
    have h₆ : s₂.regs 6=backward.toNat := hReg₂ 6 (by decide)
    simp [evalArgs,Expr.eval,h₄,h₅,h₆,hDp,hHeap₂]
  have hw₃ : ∀ z∈[fp,dp,L,backward.toNat,h₁],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hWords _ (by simp)
    · omega
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · exact hW₁
  have hPre₃ : (roundStoreCoordinateContract w h P q value backward).pre
      [fp,dp,L,backward.toNat,h₁] s₂.mem :=
    ⟨⟨fp,dp,L,h₁,rfl,by omega,hd,hQ.frozen hOld₂ hFp,hValue₂,hFitting.1⟩,
      by change ZeroFrom s₂.mem h₁; rw [hm₂]; exact hZero₁,hSpace₃⟩
  obtain ⟨s₃,c₃,h₃,hCall₃,hOut₃,hHeap₃,hRegs₃,hC₃⟩ :=
    runs_call_of_meetsContract (r:=8) (hCoord q value backward) hArgs₃ hw₃ hPre₃ ω
  obtain ⟨hEq₃,hZero₃,hNew,hFrame₃⟩ := hOut₃
  change h₃=h₁+(if backward then 2*L else L) at hEq₃
  change ∀ z<h₁,z<fp ∨ fp+L≤z → s₃.mem z=s₂.mem z at hFrame₃
  have hFit₃ : h₃≤heap+A+4+4*L := by cases backward <;> simp at hEq₃ <;> omega
  have hHp : h₁≤h₃ := by omega
  have hFrame₂₃ : ∀ z,R.foot b x₁ z → raw₁.mem z=s₃.mem z := by
    intro z hz
    have hh := hFoot₁' z hz
    exact ((hFrame₃ z hh.2 (Or.inr (hFp.trans hh.1))).trans (congrFun hm₂ z)).symm
  obtain ⟨hR₃,hPhi₃⟩ := himpl.1 b s x₁ raw₁.mem s₃.mem hFrame₂₃
  have hD₃ : RatAt s₃.mem dp h L P value := by
    apply hValue₂.agree
    intro i hi
    apply hFrame₃ (dp+i) ((Nat.add_lt_add_left hi dp).trans_le hd)
    change dp=ap ∨ dp=heap+4 at hLoc₂
    rcases hLoc₂ with hh | hh
    · right
      omega
    · right
      omega
  have hSafe₃ : h₃+allocation 3 [b,u,v,dp,h₃]<2^w := by
    have hAl := (hAlloc b u v dp h₃).2
    omega
  have hReg₃ (j : ℕ) (hj : j<8) : s₃.regs j=parent.regs j :=
    (hRegs₃ j (by omega)).trans (hReg₂ j hj)
  have hDP₃ : s₃.regs 9=dp := (hRegs₃ 9 (by decide)).trans hDp
  have hArgs₄ : evalArgs w s₃ [.reg 0,.reg 1,.reg 2,.reg 9,.reg 8]=some [b,u,v,dp,h₃] := by
    have h₀ : s₃.regs 0=b := hReg₃ 0 (by decide)
    have h₁' : s₃.regs 1=u := hReg₃ 1 (by decide)
    have h₂' : s₃.regs 2=v := hReg₃ 2 (by decide)
    simp [evalArgs,Expr.eval,h₀,h₁',h₂',hDP₃,hHeap₃]
  have hw₄ : ∀ z∈[b,u,v,dp,h₃],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · omega
    · omega
  obtain ⟨out,raw₄,c₄,y,hPush,hRep₄,hMem₄,hC₄⟩ :=
    roundPathAdd_runs D rate allocation R himpl b u v dp h₃ value s x₁ s₃.mem s₃.pos ω hw₄
      (hd.trans hHp) hD₃ hInv hFit hComp hFitting.2 (hR₃ hRep₁)
      (fun z hz => (hFoot₁' z hz).2.trans_le hHp) hZero₃ hSafe₃
  let final : State := ⟨raw₄.mem,Function.update s₃.regs 8 out,raw₄.pos⟩
  have hCall₄ := round_returning_call (dst:=8) hAdd hArgs₄ hPush
  have hRet : Runs w p ω (.ret (.reg 8)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
  have hFrame₄ : ∀ z<b,raw₄.mem z=s₃.mem z := by
    intro z hz
    exact hMem₄.2.2.2.1 z (by omega) (fun hf => (Nat.not_le_of_lt hz) (hFoot₁' z hf).1)
  refine ⟨out,final,(5+c₁+1)+(c₂+c₃+(5+c₄+1+2+1)+1+1)+1,y,?_,
    hRep₄,hNew.frozen hFrame₄ hFp,?_,?_,hMem₄.2.2.1,?_,?_,?_⟩
  · have hTail : Runs w p ω (.call 8 pathAdd [.reg 0,.reg 1,.reg 2,.reg 9,.reg 8] ;;
          .ret (.reg 8)) s₃ (.returned out) final (5+c₄+1+2+1) :=
      runs_seq_iff.mpr (Or.inr ⟨final,5+c₄+1,2,hCall₄,hRet,rfl⟩)
    have hRest : Runs w p ω (.call 8 coordinate [.reg 4,.reg 9,.reg 5,.reg 6,.reg 8] ;;
          .call 8 pathAdd [.reg 0,.reg 1,.reg 2,.reg 9,.reg 8] ;; .ret (.reg 8))
        s₂ (.returned out) final (c₃+(5+c₄+1+2+1)+1) :=
      runs_seq_iff.mpr (Or.inr ⟨s₃,_,_,hCall₃,hTail,rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s₁,_,_,hCall₁,runs_seq_iff.mpr
      (Or.inr ⟨s₂,_,_,hCall₂,hRest,by omega⟩),rfl⟩)
  · have hh : h₃≤out := hMem₄.1
    omega
  · have hh : out≤h₃+allocation 3 [b,u,v,dp,h₃] := hMem₄.2.1
    have hb' := (hAlloc b u v dp h₃).2
    omega
  · intro z hz hsep
    exact (hFrame₄ z hz).trans ((hFrame₃ z (by omega) hsep).trans (hOld₂ z hz))
  · intro z hz
    rcases hMem₄.2.2.2.2 z hz with hf | ⟨hlo,hhi⟩
    · exact ⟨(hFoot₁' z hf).1,(hFoot₁' z hf).2.trans_le (hHp.trans hMem₄.1)⟩
    · exact ⟨by change h₃≤z at hlo; omega,hhi⟩
  · change c₂≤4+(41*L+80)+1 at hC₂
    change c₃≤5+(91*L+100)+1 at hC₃
    change c₄+R.phi b y raw₄.mem≤rate (D.toForest s).n+9+R.phi b x₁ s₃.mem at hC₄
    change _+R.phi b y raw₄.mem≤_
    omega

end MinCostFlow.IPM.Machine
