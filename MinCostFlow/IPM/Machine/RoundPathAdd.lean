module

public import MinCostFlow.IPM.Machine.ForestContract
public import MinCostFlow.IPM.Machine.RoundForestCall
import WordRAM.Tactic

/-!
# Applying an exact rounding increment to a forest path

PathAdd consumes a fixed-point delta and updates the forest without
changing the caller's separate flow table.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [forest,from,to,delta,heap], call PathAdd and return its heap. -/
def roundPathAddBody (pathAdd : ℕ) : Stmt :=
  .call 5 pathAdd [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4] ;; .ret (.reg 5)

/-- The PathAdd wrapper is deterministic. -/
theorem roundPathAdd_noRand (pathAdd : ℕ) : (roundPathAddBody pathAdd).NoRand := by
  simp [roundPathAddBody,Stmt.NoRand]

/-- The exact dyadic delta is the increment in the abstract forest. -/
theorem roundPathAdd_runs {w h L P : ℕ} (D : DynForest)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (b u v a heap : ℕ) (δ : ℚ) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool) (hWords : ∀ z∈[b,u,v,a,heap],z<2^w)
    (hblock : a+L≤heap) (hDelta : RatAt mem a h L P δ)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hConn : (D.toForest s).SameComp u v)
    (hFit' : ForestFits D h L P (D.pathAdd s u v δ))
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → z<heap) (hZero : ZeroFrom mem heap)
    (hSpace : heap+allocation 3 [b,u,v,a,heap]<2^w) :
    ∃ out final c y,
      Runs w p ω (roundPathAddBody (op 3)) (startState [b,u,v,a,heap] mem pos) (.returned out) final c ∧
      R.rep b (D.pathAdd s u v δ) y final.mem ∧
      R.Respects (R.foot b x) heap (allocation 3 [b,u,v,a,heap]) mem out b y final.mem ∧
      c+R.phi b y final.mem≤rate (D.toForest s).n+9+R.phi b x mem := by
  let parent := startState [b,u,v,a,heap] mem pos
  let exprs : List Expr := [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4]
  have hArgs : evalArgs w parent exprs=some [b,u,v,a,heap] := rfl
  have hPre : (forestMachineContract D w h L P rate allocation).pre 3 s [b,u,v,a,heap] mem :=
    ⟨hInv,hFit,⟨b,u,v,a,heap,rfl,hblock,hDelta.1,hConn,hDelta.2.symm ▸ hFit'⟩⟩
  obtain ⟨out,st,c,s',y,hRun,hReg,_,hout,hRep',hMem,hCost⟩ :=
    roundForest_call_runs (i:=3) (dst:=5) D rate allocation R himpl
      parent ω s x exprs [b,u,v,a,heap] hArgs hWords rfl hRep hPre hFoot hZero hSpace
  change s'=D.pathAdd s u v (readRat mem a h L P) at hout
  rw [hDelta.2] at hout
  subst s'
  have hret : Runs w p ω (.ret (.reg 5)) st (.returned out) st 2 :=
    runs_ret_iff.mpr ⟨out,congrArg some hReg,rfl,rfl,rfl⟩
  refine ⟨out,st,c+3,y,runs_seq_iff.mpr (Or.inr ⟨st,c,2,hRun,hret,rfl⟩),hRep',hMem,?_⟩
  change c+R.phi b y st.mem≤rate (D.toForest s).n+5+1+R.phi b x mem at hCost
  omega

end MinCostFlow.IPM.Machine
