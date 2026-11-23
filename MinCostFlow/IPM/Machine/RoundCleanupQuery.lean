module

public import MinCostFlow.IPM.Machine.RoundCleanupProgram
import WordRAM.Tactic

/-!
# Query and zero test for a cleanup step

PathMin reserves the full answer before the zero test reads it.
The result leaves both the working flow and the forest state available
for either the leaf return or the flush-and-cut branch.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- The first call in a positive-fuel cleanup step. -/
def roundCleanupPathArgs : List Expr := [.reg 0,.reg 1,.reg 2,.reg 4,.reg 5]

/-- The read-only second call in a positive-fuel cleanup step. -/
def roundCleanupZeroArgs : List Expr := [.reg 5,.reg 4]

/-- The first two cleanup calls preserve the abstract forest and test
exactly the availability of its selected edge. -/
theorem roundCleanupQuery_runs {w h L P entryMin entryZero : ℕ}
    (D : DynForest) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hMin : p.procs[entryMin]?=some (roundForestPathMinBody (op 4)))
    (hZero : MeetsContract w p entryZero (roundPathZeroContract w h P))
    (b u v base heap fuel : ℕ) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool) (hw : ∀ z∈[b,u,v,base,L,heap,fuel],z<2^w)
    (hb : b≤heap) (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hcomp : (D.toForest s).SameComp u v) (hrep : R.rep b s x mem)
    (hfoot : ∀ z,R.foot b x z → b≤z ∧ z<heap) (hz : ZeroFrom mem heap)
    (hspace : heap+allocation 4 [b,u,v,heap]+4+2*L<2^w) :
    ∃ out mid c y,
      Runs w p ω (.call 7 entryMin roundCleanupPathArgs ;; .call 8 entryZero roundCleanupZeroArgs)
        (startState [b,u,v,base,L,heap,fuel] mem pos) .normal mid c ∧
      mid.regs 7=out ∧ mid.regs 8=pathHitZeroValue (D.pathMin s u v) ∧
      (∀ j<7,mid.regs j=(startState [b,u,v,base,L,heap,fuel] mem pos).regs j) ∧
      PathHitAt mid.mem heap h L P (D.pathMin s u v) ∧ R.rep b s y mid.mem ∧
      heap+4+2*L≤out ∧ out≤heap+allocation 4 [b,u,v,heap]+4+2*L ∧
      ZeroFrom mid.mem out ∧ (∀ z<b,mid.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      c+R.phi b y mid.mem≤rate (D.toForest s).n+19*L+70+R.phi b x mem := by
  have hw' : ∀ z∈[b,u,v,L,heap],z<2^w := by
    intro z hz'
    apply hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz' ⊢
    tauto
  obtain ⟨out,st,c,y,hRun,hHit,hRep,hLo,hHi,hFitOut,hZ,hMem,hFoot,hC⟩ :=
    roundForestPathMin_runs D rate allocation R himpl b u v heap s x mem pos ω hw' (by omega)
      hInv hFit hcomp hrep (fun z hz' => (hfoot z hz').2) hz hspace
  let parent := startState [b,u,v,base,L,heap,fuel] mem pos
  have hArgs : evalArgs w parent roundCleanupPathArgs=some [b,u,v,L,heap] := rfl
  have hCall := round_returning_call (dst:=7) hMin hArgs hRun
  let st₁ : State := ⟨st.mem,Function.update parent.regs 7 out,st.pos⟩
  have hArgs' : evalArgs w st₁ roundCleanupZeroArgs=some [heap,L] := rfl
  have hWZ : ∀ z∈[heap,L],z<2^w := by
    intro z hz'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz'
    rcases hz' with rfl | rfl
    all_goals exact hw _ (by simp)
  have hPre : (roundPathZeroContract w h P).pre [heap,L] st.mem :=
    ⟨heap,L,_,rfl,hHit,by omega⟩
  obtain ⟨body,hBody,o,st₂,c',hRun',hout,hC'⟩ :=
    hZero [heap,L] st.mem st.pos ω hWZ hPre
  have hEq : st₂.mem=st.mem := hout.1
  have hBit : o.value=pathHitZeroValue (D.pathMin s u v) := hout.2 _ hHit
  let mid : State := ⟨st₂.mem,Function.update st₁.regs 8 o.value,st₂.pos⟩
  have hCall' : Runs w p ω (.call 8 entryZero roundCleanupZeroArgs)
      st₁ .normal mid (c'+3) := by
    apply runs_call_iff.mpr
    refine ⟨_,body,o,st₂,c',hArgs',hBody,hRun',rfl,?_,?_⟩
    · cases st₂
      rfl
    · change c'+3=2+c'+1
      omega
  have hm : mid.mem=st.mem := hEq
  refine ⟨out,mid,5+c+1+(c'+3)+1,y,?_,?_,?_,?_,hm ▸ hHit,hm ▸ hRep,hLo,hHi,hm ▸ hZ,?_,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨st₁,_,_,hCall,hCall',rfl⟩)
  · simp [mid,st₁]
  · simpa [mid] using hBit
  · intro j hj
    have h7 : j≠7 := by omega
    have h8 : j≠8 := by omega
    simp [mid,st₁,h7,h8,parent]
  · intro z hz'
    rw [hm]
    exact hMem z (hz'.trans_le hb) (fun hh => (Nat.not_le_of_lt hz') (hfoot z hh).1)
  · intro z hz'
    rcases hFoot z hz' with hh | ⟨h₁,h₂⟩
    · exact ⟨(hfoot z hh).1,(hfoot z hh).2.trans_le (by omega)⟩
    · exact ⟨hb.trans h₁,h₂⟩
  · rw [hm]
    change c'≤19*L+30 at hC'
    omega

end MinCostFlow.IPM.Machine
