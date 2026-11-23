module

public import MinCostFlow.IPM.Machine.RoundForestCall
public import MinCostFlow.IPM.Machine.RoundFlowTable
public import MinCostFlow.IPM.Machine.RoundPathRead
import WordRAM.Tactic

/-!
# Flushing an edge before cutting it

Copy the path hit's flow into its assigned table block and remove
the edge from the dynamic forest. This is the cut branch of the
path cleanup in Kang and Payor's Section 4.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [forest,hit,flow,L,heap], write the hit flow and cut its endpoints. -/
def roundFlushCutBody (copy cut : ℕ) : Stmt :=
  .call 5 copy [
    .bin .add (.bin .add (.reg 1) (.const 4)) (.reg 3),
    .bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.const 1))) (.reg 3)),
    .reg 3] ;;
  .call 6 cut [.reg 0,.load (.bin .add (.reg 1) (.const 2)),
    .load (.bin .add (.reg 1) (.const 3)),.reg 4] ;;
  .ret (.reg 6)

/-- A flush and cut uses only deterministic memory operations and calls. -/
theorem roundFlushCut_noRand (copy cut : ℕ) : (roundFlushCutBody copy cut).NoRand := by
  simp [roundFlushCutBody,Stmt.NoRand]

set_option maxHeartbeats 450000 in
/-- The flush changes the selected coordinate, removes the hit edge,
and charges the copy plus one amortized forest operation. -/
theorem roundFlushCut_runs {w h L P copy : ℕ} (D : DynForest) (hD : D.IsSpec)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (I : Instance) (e : Fin I.m) (hit : PathHit) (heid : hit.eid=e.val)
    (b a base heap : ℕ) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (flow : Fin I.m → ℚ) (hflow : RoundFlowAt I mem base h L P flow)
    (hhit : PathHitAt mem a h L P (some hit)) (hL : 0<L)
    (hTable : base+I.m*L≤b) (hb : b≤a) (hBlock : a+4+2*L≤heap)
    (hX : hit.x<2^w) (hY : hit.y<2^w)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hz : ZeroFrom mem heap) (hSpace : heap+allocation 2 [b,hit.x,hit.y,heap]<2^w) :
    ∃ out final cost y,
      Runs w p ω (roundFlushCutBody copy (op 2)) (startState [b,a,base,L,heap] mem pos)
        (.returned out) final cost ∧
      R.rep b (D.cut s hit.x hit.y) y final.mem ∧
      R.Respects (fun z => R.foot b x z ∨ base+e.val*L≤z ∧ z<base+e.val*L+L)
        heap (allocation 2 [b,hit.x,hit.y,heap]) mem out b y final.mem ∧
      (∀ z,R.foot b y z → R.foot b x z ∨ heap≤z ∧ z<out) ∧
      RoundFlowAt I final.mem base h L P (fun j => if j=e then hit.flow else flow j) ∧
      cost+R.phi b y final.mem≤rate (D.toForest s).n+(copyWordsContract w).cost [a+4+L,base+e.val*L,L] mem
        +50+R.phi b x mem := by
  let src := a+4+L
  let dest := base+e.val*L
  have hdest : dest+L≤b := by
    have hm := Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt)
    rw [Nat.succ_mul] at hm
    dsimp only [dest]
    omega
  have hsrc : src+L≤heap := by dsimp only [src]; omega
  have hS : src<2^w := by omega
  have hD' : dest<2^w := by omega
  have hM : e.val*L<2^w := by dsimp only [dest] at hD'; omega
  have hHeap : heap<2^w := by omega
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hThree : 3<2^w := by omega
  have hFour : 4<2^w := by omega
  have ha1 : a+1<2^w := by omega
  have ha2 : a+2<2^w := by omega
  have ha3 : a+3<2^w := by omega
  have ha4 : a+4<2^w := by omega
  have hcoord := pathHit_words hhit
  have hid : mem (a+1)=e.val := hcoord.2.1.trans heid
  have hId : e.val<2^w := by
    have hle := Nat.le_mul_of_pos_right e.val hL
    omega
  let st := startState [b,a,base,L,heap] mem pos
  let copyExprs : List Expr := [
    .bin .add (.bin .add (.reg 1) (.const 4)) (.reg 3),
    .bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.const 1))) (.reg 3)),
    .reg 3]
  have hArgs : evalArgs w st copyExprs=some [src,dest,L] := by
    dsimp only [st,copyExprs,src,dest]
    eval_expr
  have hCW : ∀ z∈[src,dest,L],z<2^w := by wram_words
  have hPre : (copyWordsContract w).pre [src,dest,L] mem := by
    refine ⟨src,dest,L,rfl,?_,?_,?_⟩
    all_goals omega
  obtain ⟨body,hBody,o,raw,c,hRun,hout,hC⟩ := hcopy [src,dest,L] mem pos ω hCW hPre
  let mid : State := ⟨raw.mem,Function.update st.regs 5 o.value,raw.pos⟩
  have hCopyRun : Runs w p ω (.call 5 copy copyExprs) st .normal mid (argsSize copyExprs+c+1) := by
    apply runs_call_iff.mpr
    refine ⟨_,body,o,raw,c,hArgs,hBody,hRun,rfl,?_,rfl⟩
    cases raw
    rfl
  obtain ⟨hFlow',hFrame⟩ := round_copy_flow e hit.flow hhit.2.2 hflow hout
  obtain ⟨hRep',hCredit⟩ := round_copy_preserves_forest R himpl.1 hrep
    (fun z hz' => Or.inr (hdest.trans (hfoot z hz').1)) hout
  have hMX : mid.mem (a+2)=hit.x := (hFrame _ (Or.inr (by omega))).trans hcoord.2.2.1
  have hMY : mid.mem (a+3)=hit.y := (hFrame _ (Or.inr (by omega))).trans hcoord.2.2.2
  let cutExprs : List Expr :=
    [.reg 0,.load (.bin .add (.reg 1) (.const 2)),.load (.bin .add (.reg 1) (.const 3)),.reg 4]
  have hCutArgs : evalArgs w mid cutExprs=some [b,hit.x,hit.y,heap] := by
    dsimp only [cutExprs]
    eval_expr
  have hCutWords : ∀ z∈[b,hit.x,hit.y,heap],z<2^w := by wram_words
  have hPreCut : (forestMachineContract D w h L P rate allocation).pre 2 s
      [b,hit.x,hit.y,heap] mid.mem :=
    ⟨hInv,hFit,⟨b,hit.x,hit.y,heap,rfl,hFit.cut hD hInv⟩⟩
  obtain ⟨out,final,c',s',y,hCut,hReg,_,hState,hRep,hMem,hCost⟩ :=
    roundForest_call_runs D rate allocation R himpl mid ω s x cutExprs _ hCutArgs
      hCutWords rfl hRep' hPreCut (fun z hz' => (hfoot z hz').2)
      (fun z hz' => (hFrame z (Or.inr (hdest.trans (show b≤z from by change heap≤z at hz'; omega)))).trans (hz z hz')) hSpace
  change s'=D.cut s hit.x hit.y at hState
  subst s'
  have hOut : out<2^w := hMem.2.1.trans_lt hSpace
  have hRet : Runs w p ω (.ret (.reg 6)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,by simpa [Expr.eval] using congrArg some hReg,rfl,rfl,rfl⟩
  refine ⟨out,final,argsSize copyExprs+c+1+(c'+3)+1,y,?_,hRep,?_,hMem.2.2.2.2,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,c'+3,hCopyRun,
      runs_seq_iff.mpr (Or.inr ⟨final,c',2,hCut,hRet,rfl⟩),rfl⟩)
  · refine ⟨hMem.1,hMem.2.1,hMem.2.2.1,?_,?_⟩
    · intro z hz' hn
      exact (hMem.2.2.2.1 z hz' (fun h => hn (Or.inl h))).trans
        (hFrame z (by
          by_cases hl : z<dest
          · exact Or.inl hl
          · exact Or.inr (by
              change ¬ z<base+e.val*L at hl
              by_contra hh
              exact hn (Or.inr ⟨by omega,by omega⟩))))
    · intro z hz'
      exact (hMem.2.2.2.2 z hz').imp Or.inl id
  · intro j
    have hj := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hj
    refine (hFlow' j).frozen (heap:=b) ?_ (by omega)
    intro i hhi
    exact hMem.2.2.2.1 i (show i<heap from by omega) (fun hh => by have := (hfoot _ hh).1; omega)
  · change c≤_ at hC
    change c'+R.phi b y final.mem≤rate (D.toForest s).n+argsSize cutExprs+1+R.phi b x mid.mem at hCost
    have hcSize : argsSize copyExprs=14 := rfl
    have htSize : argsSize cutExprs=10 := rfl
    change R.phi b x mem=R.phi b x mid.mem at hCredit
    change c≤(copyWordsContract w).cost [a+4+L,base+e.val*L,L] mem at hC
    omega

end MinCostFlow.IPM.Machine
