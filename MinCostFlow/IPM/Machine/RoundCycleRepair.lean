module

public import MinCostFlow.IPM.Machine.RoundCyclePush
public import MinCostFlow.IPM.Machine.RoundCleanup
import WordRAM.Tactic

/-!
# Pushing a rounding cycle and cleaning its forest path

Kang and Payor's Section 4 corrects the new edge and its return path,
then removes every forest edge made integral by the correction.
This procedure implements those two steps with the same dyadic
increment and carries the forest potential through both.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [forest,from,to,availability,coordinate,L,backward,base,fuel,heap],
push the cycle correction, then cut its integral forest edges. -/
def roundCycleRepairBody (push cleanup : ℕ) : Stmt :=
  .call 10 push [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 9] ;;
  .call 10 cleanup [.reg 0,.reg 1,.reg 2,.reg 7,.reg 5,.reg 10,.reg 8] ;;
  .ret (.reg 10)

/-- Pushing and cleaning the rounding cycle uses deterministic calls. -/
theorem roundCycleRepair_noRand (push cleanup : ℕ) :
    (roundCycleRepairBody push cleanup).NoRand := by
  simp [roundCycleRepairBody,Stmt.NoRand]

set_option maxHeartbeats 850000 in
/-- The machine passes the updated forest and coordinate table to
cleanup. The two exact model stages agree component by component. -/
theorem roundCycleRepair_runs {w h L P pathMin delta coordinate pathAdd push cleanup pm zeroEntry flush copy A : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hPush : p.procs[push]?=some (roundCyclePushBody pathMin delta coordinate pathAdd))
    (hMin : p.procs[pathMin]?=some (roundForestPathMinBody (op 4)))
    (hDelta : ∀ q hit,MeetsContract w p delta (roundDeltaContract w h P q hit))
    (hCoord : ∀ q δ backward,MeetsContract w p coordinate (roundStoreCoordinateContract w h P q δ backward))
    (hAdd : p.procs[pathAdd]?=some (roundPathAddBody (op 3)))
    (hCleanup : p.procs[cleanup]?=some (roundCleanupBody cleanup pm zeroEntry flush))
    (hPM : p.procs[pm]?=some (roundForestPathMinBody (op 4)))
    (hZero : MeetsContract w p zeroEntry (roundPathZeroContract w h P))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hFlush : p.procs[flush]?=some (roundFlushCutBody copy (op 2)))
    (hAlloc : ∀ b u v a heap,allocation 4 [b,u,v,heap]≤A ∧ allocation 3 [b,u,v,a,heap]≤A ∧
      allocation 2 [b,u,v,heap]≤A)
    (I : Instance) (f arr : Fin I.m → ℚ) (j : Fin I.m)
    (b u v ap base fuel heap : ℕ) (backward : Bool) (avail : ℚ)
    (cnt : RoundCounts) (rats : List ℚ) (steps : List PathStep) (s : D.State) (x : R.τ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hWords : ∀ z∈[b,u,v,ap,base+j.val*L,L,backward.toNat,base,fuel,heap],z<2^w)
    (hL : 0<L) (hAp : ap+L≤heap) (hApart : b≤ap) (hb : b≤heap) (hTable : base+I.m*L≤b)
    (hFlow : RoundFlowAt I mem base h L P arr) (hAvail : RatAt mem ap h L P avail)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hPath : findSteps (D.toForest s).edges u v=some steps)
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hAvailFrame : ∀ z,R.foot b x z → z<ap ∨ ap+L≤z) (hFresh : ZeroFrom mem heap)
    (hN : (D.toForest s).n≤2^w) (hFuel : (D.toForest s).edges.length<fuel)
    (hStrict : ∀ e∈(D.toForest s).edges,ForestEdgeStrictInv I f e)
    (hFP : ∀ e∈(D.toForest s).edges,IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd)
    (hNi : 0≤avail)
    (hSpace : heap+2*A+4+4*L+roundCleanupCharge (A+4+2*L) A (D.toForest s).edges.length<2^w)
    (hFitting : let δ := (D.pathMin s u v).elim avail (fun e => min avail e.avail)
      RatFits h L P (if backward then arr j-δ else arr j+δ) ∧ ForestFits D h L P (D.pathAdd s u v δ)) :
    let δ := (D.pathMin s u v).elim avail (fun e => min avail e.avail)
    let newFlow := if backward then arr j-δ else arr j+δ
    let s₁ := D.pathAdd s u v δ
    let result := removeZeroEdges D I s₁ (fun k => if k=j then newFlow else arr k) cnt rats u v fuel
    let r := (D.toForest s).edges.length-(D.toForest result.1).edges.length
    ∃ out final cost y,
      Runs w p ω (roundCycleRepairBody push cleanup)
        (startState [b,u,v,ap,base+j.val*L,L,backward.toNat,base,fuel,heap] mem pos) (.returned out) final cost ∧
      R.rep b result.1 y final.mem ∧ RoundFlowAt I final.mem base h L P result.2.1 ∧
      heap≤out ∧ out≤heap+2*A+4+4*L+roundCleanupCharge (A+4+2*L) A r ∧
      ZeroFrom final.mem out ∧ (∀ z<base,final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤2*rate (D.toForest s).n+132*L+275+
        roundCleanupCharge (rate (D.toForest s).n+19*L+80) (rate (D.toForest s).n+17*L+115) r+
        R.phi b x mem := by
  dsimp only at hFitting ⊢
  let fp := base+j.val*L
  let δ := (D.pathMin s u v).elim avail (fun e => min avail e.avail)
  let value := if backward then arr j-δ else arr j+δ
  let arr' := fun k => if k=j then value else arr k
  let s' := D.pathAdd s u v δ
  let parent := startState [b,u,v,ap,fp,L,backward.toNat,base,fuel,heap] mem pos
  have hFp : fp+L≤b := by
    have hJ := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hJ
    dsimp [fp]
    omega
  have hw₀ : ∀ z∈[b,u,v,ap,fp,L,backward.toNat,heap],z<2^w := by
    intro z hz
    apply hWords
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  have hV := hD.2.1 s hInv
  obtain ⟨hw,_⟩ := findSteps_sound hV.2.1 hPath
  have hComp : (D.toForest s).SameComp u v := ⟨_,hw.to_isWalk⟩
  obtain ⟨out₁,raw₁,c₁,x₁,hRun₁,hRep₁,hNew,hLo₁,hHi₁,hZero₁,hMem₁,hFoot₁,hC₁⟩ :=
    roundCyclePush_runs D rate allocation R himpl hMin hDelta hCoord hAdd
      (fun b u v a heap => ⟨(hAlloc b u v a heap).1,(hAlloc b u v a heap).2.1⟩)
      b u v ap fp heap backward (arr j) avail s x mem pos ω hw₀ hL hAp (hFp.trans hApart) hFp hb
      (hFlow j) hAvail hInv hFit hComp hRep hFoot hAvailFrame hFresh (by omega) hFitting
  have hFlow₁ : RoundFlowAt I raw₁.mem base h L P arr' :=
    hFlow.update j value hNew (fun z hz => hMem₁ z (hz.trans_le hTable))
  have hArgs₁ : evalArgs w parent [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 9]=
      some [b,u,v,ap,fp,L,backward.toNat,heap] := rfl
  have hCall₁ := round_returning_call (dst:=10) hPush hArgs₁ hRun₁
  let mid : State := ⟨raw₁.mem,Function.update parent.regs 10 out₁,raw₁.pos⟩
  have hδ := roundDelta_nonnegative hD hInv hPath avail hNi (fun t ht => by
    have he := hStrict t.edge (hw.mem_edges t ht)
    cases hF : t.fwd
    · exact le_of_lt (by simpa [PathStep.dirAvail,hF] using he.2.2 : 0<t.dirAvail)
    · exact le_of_lt (by simpa [PathStep.dirAvail,hF] using he.2.1 : 0<t.dirAvail))
  have hδP := roundDelta_fixed hD hInv hPath avail hAvail.fixed (fun t ht => by
    have he := hFP t.edge (hw.mem_edges t ht)
    cases hF : t.fwd
    · simpa [PathStep.dirAvail,hF] using he.2.2
    · simpa [PathStep.dirAvail,hF] using he.2.1)
  obtain ⟨hInv₁,hN₁,hLen₁,hPath₁,hWeak₁,hBounds₁⟩ :=
    roundPathAdd_invariants hD hInv hPath hStrict hFP hδ hδP (roundDelta_path hD hInv hPath avail).2.1
  change (D.toForest s').n=(D.toForest s).n at hN₁
  change (D.toForest s').edges.length=(D.toForest s).edges.length at hLen₁
  have hs₁ : out₁+roundCleanupCharge (A+4+2*L) A (D.toForest s').edges.length<2^w := by
    rw [hLen₁]
    omega
  have hw₁ : ∀ z∈[b,u,v,base,L,out₁,fuel],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · exact hWords _ (by simp)
    · omega
    · exact hWords _ (by simp)
  obtain ⟨out,raw₂,c₂,y,hRun₂,hRep₂,hFlow₂,hLo₂,hHi₂,hZero₂,hFoot₂,hMem₂,hC₂⟩ :=
    roundCleanup_runs D hD rate allocation R himpl hCleanup hPM hZero hCopy hFlush
      (fun b u v heap => ⟨(hAlloc b u v 0 heap).2.2,(hAlloc b u v 0 heap).1⟩)
      I f ω hL fuel b u v base out₁ s' x₁ mid.mem mid.pos arr' cnt rats _ hw₁
      (hN₁.trans_le hN) hTable (hb.trans hLo₁) hInv₁ hFitting.2 hPath₁ (hLen₁ ▸ hFuel)
      (fun e he => (hWeak₁ e he).1) hBounds₁ hFlow₁ hRep₁ hFoot₁ hZero₁ hs₁
  have hArgs₂ : evalArgs w mid [.reg 0,.reg 1,.reg 2,.reg 7,.reg 5,.reg 10,.reg 8]=
      some [b,u,v,base,L,out₁,fuel] := rfl
  have hCall₂ := round_returning_call (dst:=10) hCleanup hArgs₂ hRun₂
  let final : State := ⟨raw₂.mem,Function.update mid.regs 10 out,raw₂.pos⟩
  have hRet : Runs w p ω (.ret (.reg 10)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
  refine ⟨out,final,8+c₁+1+(7+c₂+1+2+1)+1,y,?_,hRep₂,hFlow₂,hLo₁.trans hLo₂,?_,hZero₂,?_,hFoot₂,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hCall₁,runs_seq_iff.mpr (Or.inr
      ⟨final,_,_,hCall₂,hRet,rfl⟩),rfl⟩)
  · have hh := Nat.add_le_add_right hHi₁
      (roundCleanupCharge (A+4+2*L) A
        ((D.toForest s').edges.length-(D.toForest (removeZeroEdges D I s' arr' cnt rats u v fuel).1).edges.length))
    exact hHi₂.trans (hLen₁ ▸ hh)
  · intro z hz
    exact (hMem₂ z hz).trans (hMem₁ z (by omega) (Or.inl (by dsimp [fp]; omega)))
  · rw [hN₁,hLen₁] at hC₂
    let r := (D.toForest s).edges.length-(D.toForest (removeZeroEdges D I s' arr' cnt rats u v fuel).1).edges.length
    let charge := roundCleanupCharge (rate (D.toForest s).n+19*L+80) (rate (D.toForest s).n+17*L+115) r
    change c₂+R.phi b y raw₂.mem≤charge+R.phi b x₁ raw₁.mem at hC₂
    change _+R.phi b y raw₂.mem≤2*rate (D.toForest s).n+132*L+275+charge+R.phi b x mem
    omega

end MinCostFlow.IPM.Machine
