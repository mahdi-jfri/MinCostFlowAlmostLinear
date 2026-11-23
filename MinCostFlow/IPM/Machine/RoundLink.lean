module

public import MinCostFlow.IPM.Machine.RoundLinkRecord
public import MinCostFlow.IPM.Machine.RoundForestCall
import WordRAM.Tactic

/-!
# Linking a fractional rounding edge

The copied record describes one mathematical edge. Link inserts
that edge into the forest, while the caller's arrays remain below
the forest's private memory.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- The forest edge layout determines every payload field. -/
theorem ForestEdgeAt.unique {mem : ℕ → ℕ} {a h L P : ℕ} {e g : ForestEdge}
    (he : ForestEdgeAt mem a h L P e) (hg : ForestEdgeAt mem a h L P g) : e=g := by
  have hid : e.eid=g.eid := (he.1 0 (by simp)).symm.trans (hg.1 0 (by simp))
  have hu : e.u=g.u := (he.1 1 (by simp)).symm.trans (hg.1 1 (by simp))
  have hv : e.v=g.v := (he.1 2 (by simp)).symm.trans (hg.1 2 (by simp))
  have hc := he.2.2.1.symm.trans hg.2.2.1
  have hf := he.2.2.2.1.2.symm.trans hg.2.2.2.1.2
  have ha := he.2.2.2.2.1.2.symm.trans hg.2.2.2.2.1.2
  have hb := he.2.2.2.2.2.2.symm.trans hg.2.2.2.2.2.2
  cases e
  cases g
  congr

/-- A new fitting forest edge and fitting old edges suffice for the
representation bound of the result of Link. -/
theorem ForestFits.link {D : DynForest} (hD : D.IsSpec) {h L P : ℕ} {s : D.State}
    {e : ForestEdge} (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hu : e.u<(D.toForest s).n) (hv : e.v<(D.toForest s).n)
    (hConn : ¬(D.toForest s).SameComp e.u e.v)
    (hFresh : ∀ e'∈(D.toForest s).edges,e'.eid≠e.eid)
    (he : Num.Fits h L e.cost ∧ RatFits h L P e.flow ∧
      RatFits h L P e.availFwd ∧ RatFits h L P e.availBwd) :
    ForestFits D h L P (D.link s e) := by
  have hs := (hD.2.2.2.1 s e hInv hu hv hConn hFresh).2.2
  intro g hg
  have hm := hs.mem_iff.mp hg
  change g∈e::(D.toForest s).edges at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact he
  · exact hFit _ hm

/-- On [forest,record,heap], call Link and return its heap. -/
def roundLinkBody (link : ℕ) : Stmt :=
  .call 3 link [.reg 0,.reg 1,.reg 2] ;; .ret (.reg 3)

/-- The Link wrapper is deterministic. -/
theorem roundLink_noRand (link : ℕ) : (roundLinkBody link).NoRand := by
  simp [roundLinkBody,Stmt.NoRand]

/-- A verified call of Link on the exact input edge transfers the
forest state, credited cost, and allocation to the rounder. -/
theorem roundLink_runs {w h L P : ℕ} (D : DynForest)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (b a heap : ℕ) (e : ForestEdge) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool) (hWords : ∀ z∈[b,a,heap],z<2^w)
    (hblock : a+3+4*L≤heap) (hEdge : ForestEdgeAt mem a h L P e)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s) (hId : e.eid<2^w)
    (hu : e.u<(D.toForest s).n) (hv : e.v<(D.toForest s).n)
    (hDis : ¬(D.toForest s).SameComp e.u e.v)
    (hFresh : ∀ e'∈(D.toForest s).edges,e'.eid≠e.eid)
    (hFit' : ForestFits D h L P (D.link s e))
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → z<heap) (hZero : ZeroFrom mem heap)
    (hSpace : heap+allocation 1 [b,a,heap]<2^w) :
    ∃ out final c y,
      Runs w p ω (roundLinkBody (op 1)) (startState [b,a,heap] mem pos) (.returned out) final c ∧
      R.rep b (D.link s e) y final.mem ∧
      R.Respects (R.foot b x) heap (allocation 1 [b,a,heap]) mem out b y final.mem ∧
      c+R.phi b y final.mem≤rate (D.toForest s).n+7+R.phi b x mem := by
  let parent := startState [b,a,heap] mem pos
  let exprs : List Expr := [.reg 0,.reg 1,.reg 2]
  have hArgs : evalArgs w parent exprs=some [b,a,heap] := rfl
  have hPre : (forestMachineContract D w h L P rate allocation).pre 1 s [b,a,heap] mem :=
    ⟨hInv,hFit,⟨b,a,heap,e,rfl,hblock,hEdge,hId,hu,hv,hDis,hFresh,hFit'⟩⟩
  obtain ⟨out,st,c,s',y,hRun,hReg,_,hout,hRep',hMem,hCost⟩ :=
    roundForest_call_runs (i:=1) (dst:=3) D rate allocation R himpl
      parent ω s x exprs [b,a,heap] hArgs hWords rfl hRep hPre hFoot hZero hSpace
  change ∃ g,ForestEdgeAt mem a h L P g ∧ s'=D.link s g at hout
  obtain ⟨g,hg,hs'⟩ := hout
  rw [hEdge.unique hg] at *
  subst s'
  have hret : Runs w p ω (.ret (.reg 3)) st (.returned out) st 2 :=
    runs_ret_iff.mpr ⟨out,congrArg some hReg,rfl,rfl,rfl⟩
  refine ⟨out,st,c+3,y,runs_seq_iff.mpr (Or.inr ⟨st,c,2,hRun,hret,rfl⟩),hRep',hMem,?_⟩
  change c+R.phi b y st.mem≤rate (D.toForest s).n+3+1+R.phi b x mem at hCost
  omega

end MinCostFlow.IPM.Machine
