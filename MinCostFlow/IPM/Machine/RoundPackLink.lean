module

public import MinCostFlow.IPM.Machine.RoundLink
public import MinCostFlow.IPM.Machine.RoundCleanupProgram
import WordRAM.Tactic

/-!
# Adding a fractional edge to the rounding forest

A new edge record is packed above the existing heap and then
passed to Link. The forest representation has the same potential
before and after packing.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [b,eid,u,v,cost,flow,forward,backward,L,heap], pack and link. -/
def roundPackLinkBody (pack link : ℕ) : Stmt :=
  .call 10 pack [.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9] ;;
  .call 11 link [.reg 0,.reg 9,.reg 10] ;;
  .ret (.reg 11)

/-- This composite Link branch uses deterministic calls. -/
theorem roundPackLink_noRand (pack link : ℕ) : (roundPackLinkBody pack link).NoRand := by
  simp [roundPackLinkBody,Stmt.NoRand]

/-- Packing and Link insert the exact mathematical edge without
altering the working flow below the forest handle. -/
theorem roundPackLink_runs {w h L P pack link : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hPack : ∀ e, MeetsContract w p pack (roundLinkRecordContract w h P e))
    (hLink : p.procs[link]?=some (roundLinkBody (op 1)))
    (e : ForestEdge) (b c f af ab heap : ℕ) (s : D.State) (x : R.τ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hWords : ∀ z∈[b,e.eid,e.u,e.v,c,f,af,ab,L,heap],z<2^w)
    (hBlocks : c+L≤heap ∧ f+L≤heap ∧ af+L≤heap ∧ ab+L≤heap)
    (hC : RatAt mem c h L 0 e.cost) (hF : RatAt mem f h L P e.flow)
    (hAf : RatAt mem af h L P e.availFwd) (hAb : RatAt mem ab h L P e.availBwd)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hFits : Num.Fits h L e.cost ∧ RatFits h L P e.flow ∧ RatFits h L P e.availFwd ∧ RatFits h L P e.availBwd)
    (hu : e.u<(D.toForest s).n) (hv : e.v<(D.toForest s).n)
    (hDis : ¬(D.toForest s).SameComp e.u e.v)
    (hFresh : ∀ e'∈(D.toForest s).edges,e'.eid≠e.eid)
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap) (hZero : ZeroFrom mem heap)
    (hb : b≤heap)
    (hSpace : heap+3+4*L+allocation 1 [b,heap,heap+3+4*L]<2^w) :
    ∃ out final cost y,
      Runs w p ω (roundPackLinkBody pack link)
        (startState [b,e.eid,e.u,e.v,c,f,af,ab,L,heap] mem pos) (.returned out) final cost ∧
      R.rep b (D.link s e) y final.mem ∧ heap≤out ∧
      out≤heap+3+4*L+allocation 1 [b,heap,heap+3+4*L] ∧
      ZeroFrom final.mem out ∧ (∀ z<b,final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤rate (D.toForest s).n+68*L+170+R.phi b x mem := by
  let args := [e.eid,e.u,e.v,c,f,af,ab,L,heap]
  let parent := startState (b::args) mem pos
  let exprs : List Expr := [.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9]
  have hw : ∀ z∈args,z<2^w := fun z hz => hWords z (List.mem_cons_of_mem b hz)
  have hp : (roundLinkRecordContract w h P e).pre args mem := by
    refine ⟨⟨c,f,af,ab,L,heap,rfl,hBlocks.1,hBlocks.2.1,hBlocks.2.2.1,hBlocks.2.2.2,
      hC,hF,hAf,hAb⟩,hZero,?_⟩
    change heap+(3+4*L)<2^w
    omega
  obtain ⟨body,hBody,o,raw,c₁,hRun,hout,hCost⟩ := hPack e args mem pos ω hw hp
  obtain ⟨⟨hLo,hHi,hFrame,hZero₁,hEdge⟩,hEnd⟩ := hout
  change o.value=heap+3+4*L at hEnd
  change ∀ z<heap,raw.mem z=mem z at hFrame
  obtain ⟨hRep₁,hPhi⟩ := himpl.1 b s x mem raw.mem
    (fun z hz => (hFrame z (hFoot z hz).2).symm)
  let mid : State := ⟨raw.mem,Function.update parent.regs 10 o.value,raw.pos⟩
  have hCall : Runs w p ω (.call 10 pack exprs) parent .normal mid (9+c₁+1) :=
    runs_call_iff.mpr ⟨args,body,o,raw,c₁,rfl,hBody,hRun,rfl,by cases raw; rfl,rfl⟩
  have hWords₁ : ∀ z∈[b,heap,o.value],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · omega
  obtain ⟨out,raw₂,c₂,y,hRun₂,hRep₂,hFrame₂,hC₂⟩ :=
    roundLink_runs D rate allocation R himpl b heap o.value e s x mid.mem mid.pos ω hWords₁
      hEnd.ge hEdge hInv hFit (hWords _ (by simp)) hu hv hDis hFresh
      (hFit.link hD hInv hu hv hDis hFresh hFits) (hRep₁ hRep)
      (fun z hz => (hFoot z hz).2.trans_le hLo) hZero₁ (by rwa [hEnd])
  have hArgs₂ : evalArgs w mid [.reg 0,.reg 9,.reg 10]=some [b,heap,o.value] := rfl
  have hCall₂ := round_returning_call (dst:=11) hLink hArgs₂ hRun₂
  let final : State := ⟨raw₂.mem,Function.update mid.regs 11 out,raw₂.pos⟩
  have hRet : Runs w p ω (.ret (.reg 11)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
  refine ⟨out,final,9+c₁+1+(3+c₂+1+2+1)+1,y,?_,hRep₂,?_,?_,hFrame₂.2.2.1,?_,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hCall,runs_seq_iff.mpr (Or.inr
      ⟨final,_,_,hCall₂,hRet,rfl⟩),rfl⟩)
  · exact hLo.trans hFrame₂.1
  · simpa only [hEnd] using hFrame₂.2.1
  · intro z hz
    exact (hFrame₂.2.2.2.1 z (by omega)
      (fun h => (Nat.not_le_of_lt hz) (hFoot z h).1)).trans (hFrame z (hz.trans_le hb))
  · intro z hz
    rcases hFrame₂.2.2.2.2 z hz with he | ⟨hl,hh⟩
    · exact ⟨(hFoot z he).1,(hFoot z he).2.trans_le (hLo.trans hFrame₂.1)⟩
    · exact ⟨by change o.value≤z at hl; omega,hh⟩
  · change c₁≤68*L+140 at hCost
    change c₂+R.phi b y raw₂.mem≤rate (D.toForest s).n+7+R.phi b x raw.mem at hC₂
    change 9+c₁+1+(3+c₂+1+2+1)+1+R.phi b y raw₂.mem≤_
    omega

end MinCostFlow.IPM.Machine
