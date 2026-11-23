module

public import MinCostFlow.IPM.Machine.RoundCleanupCut
import WordRAM.Tactic

/-!
# Cost and correctness of the recursive path cleanup

The execution follows Kang and Payor's recursive split. A leaf
performs one path query. A cut gives two children, so the sum of
their charges is linear in the number of edges actually cut.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Each visited path and each cut is charged once. A binary
cleanup with r cuts has 2*r+1 path queries. -/
def roundCleanupCharge (query cut r : ℕ) : ℕ := query+(2*query+cut)*r

/-- Splitting once charges the parent query, one cut, and both child
executions. -/
theorem roundCleanupCharge_split (q c r₁ r₂ : ℕ) :
    roundCleanupCharge q c (r₁+r₂+1)=q+c+roundCleanupCharge q c r₁+roundCleanupCharge q c r₂ := by
  simp only [roundCleanupCharge,Nat.mul_add,Nat.mul_one]
  omega

private theorem cleanupCuts_split {m m₀ m₁ m₂ : ℕ}
    (h₀ : m₀+1=m) (h₁ : m₁≤m₀) (h₂ : m₂≤m₁) :
    m-m₂=(m₀-m₁)+(m₁-m₂)+1 := by omega

private theorem cleanup_return_leaf {w c out : ℕ} {p : Program} {ω : ℕ → Bool}
    {entry pathMin pathZero flushCut fuel : ℕ} {start mid : State}
    (hFuel : start.regs 6=fuel+1) (ret : mid.regs 7=out) (zero : mid.regs 8=0)
    (hRun : Runs w p ω (.call 7 pathMin roundCleanupPathArgs ;;
      .call 8 pathZero roundCleanupZeroArgs) start .normal mid c) :
    Runs w p ω (roundCleanupBody entry pathMin pathZero flushCut) start (.returned out) mid (c+7) := by
  unfold roundCleanupBody
  have hret : Runs w p ω (.ret (.reg 7)) mid (.returned out) mid 2 :=
    runs_ret_iff.mpr ⟨out,congrArg some ret,rfl,rfl,rfl⟩
  have hseq := runs_seq_iff.mp hRun
  rcases hseq with ⟨oo,_,hh,ho,_⟩ | ⟨mid₁,c₁,c₂,h₁,h₂,hc⟩
  · cases ho
  · have hcond := fun branch =>
      (runs_cond_iff (w:=w) (p:=p) (ω:=ω) (e:=.reg 8) (s:=branch)
        (t:=.ret (.reg 7)) (st:=mid) (o:=.returned out) (st':=mid) (c:=4)).mpr
      ⟨0,2,congrArg some zero,hret,rfl⟩
    apply runs_cond_iff.mpr
    refine ⟨fuel+1,c+5,congrArg some hFuel,?_,by change c+7=1+(c+5)+1; omega⟩
    simp only [Nat.succ_ne_zero,ite_false]
    exact runs_seq_iff.mpr (Or.inr ⟨mid₁,c₁,c₂+5,h₁,
      runs_seq_iff.mpr (Or.inr ⟨mid,c₂,4,h₂,hcond _,rfl⟩),by omega⟩)

private theorem cleanup_return_cut {w c c₀ c₁ c₂ out : ℕ} {p : Program} {ω : ℕ → Bool}
    {entry pathMin pathZero flushCut fuel : ℕ} {start mid cut left final : State}
    (hFuel : start.regs 6=fuel+1) (ret : final.regs 7=out) (bit : mid.regs 8=1)
    (hRun : Runs w p ω (.call 7 pathMin roundCleanupPathArgs ;;
      .call 8 pathZero roundCleanupZeroArgs) start .normal mid c)
    (hCut : Runs w p ω (roundCleanupSave ;; .call 7 flushCut roundCleanupCutArgs) mid .normal cut c₀)
    (hLeft : Runs w p ω (.call 7 entry [.reg 0,.reg 1,.reg 9,.reg 3,.reg 4,.reg 7,.reg 11]) cut .normal left c₁)
    (hRight : Runs w p ω (.call 7 entry [.reg 0,.reg 10,.reg 2,.reg 3,.reg 4,.reg 7,.reg 11])
      left .normal final c₂) :
    Runs w p ω (roundCleanupBody entry pathMin pathZero flushCut) start (.returned out) final
      (c+c₀+c₁+c₂+10) := by
  unfold roundCleanupBody
  have hret : Runs w p ω (.ret (.reg 7)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,congrArg some ret,rfl,rfl,rfl⟩
  rcases runs_seq_iff.mp hRun with ⟨_,_,_,ho,_⟩ | ⟨one,t₁,t₂,h₁,h₂,hc⟩
  · cases ho
  rcases runs_seq_iff.mp hCut with ⟨_,_,_,ho,_⟩ | ⟨three,t₃,t₄,h₃,h₄,hc₀⟩
  · cases ho
  apply runs_cond_iff.mpr
  refine ⟨fuel+1,c+c₀+c₁+c₂+8,congrArg some hFuel,?_,by change _=1+_+1; omega⟩
  simp only [Nat.succ_ne_zero,ite_false]
  apply runs_seq_iff.mpr
  refine Or.inr ⟨one,t₁,t₂+c₀+c₁+c₂+8,h₁,?_,by omega⟩
  apply runs_seq_iff.mpr
  refine Or.inr ⟨mid,t₂,c₀+c₁+c₂+7,h₂,?_,by omega⟩
  apply runs_cond_iff.mpr
  refine ⟨1,c₀+c₁+c₂+5,congrArg some bit,?_,by change _=1+_+1; omega⟩
  simp only [Nat.one_ne_zero,ite_false]
  exact runs_seq_iff.mpr (Or.inr ⟨three,t₃,t₄+c₁+c₂+5,h₃,
    runs_seq_iff.mpr (Or.inr ⟨cut,t₄,c₁+c₂+4,h₄,
      runs_seq_iff.mpr (Or.inr ⟨left,c₁,c₂+3,hLeft,
        runs_seq_iff.mpr (Or.inr ⟨final,c₂,2,hRight,hret,rfl⟩),by omega⟩),by omega⟩),by omega⟩)

set_option maxHeartbeats 900000 in
/-- The recursive machine cleanup follows the exact model, using one
charge per path query and cut. The edge-count drop measures cuts, so
the bound composes across all rounding steps. -/
theorem roundCleanup_runs {w h L P entry pathMin pathZero flushCut copy A : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hBody : p.procs[entry]?=some (roundCleanupBody entry pathMin pathZero flushCut))
    (hMin : p.procs[pathMin]?=some (roundForestPathMinBody (op 4)))
    (hZero : MeetsContract w p pathZero (roundPathZeroContract w h P))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hCut : p.procs[flushCut]?=some (roundFlushCutBody copy (op 2)))
    (hAlloc : ∀ b u v heap,allocation 2 [b,u,v,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A)
    (I : Instance) (f : Fin I.m → ℚ) (ω : ℕ → Bool) (hL : 0<L) :
    ∀ fuel b u v base heap s (x : R.τ) mem pos arr cnt rats steps,
      (∀ z∈[b,u,v,base,L,heap,fuel],z<2^w) →
      (D.toForest s).n≤2^w → base+I.m*L≤b → b≤heap →
      D.Inv s → ForestFits D h L P s →
      findSteps (D.toForest s).edges u v=some steps → (D.toForest s).edges.length<fuel →
      (∀ e∈(D.toForest s).edges,ForestEdgeWeakInv I f e) →
      (∀ t∈steps,0≤t.dirAvail ∧ 0<t.flip.dirAvail) →
      RoundFlowAt I mem base h L P arr → R.rep b s x mem →
      (∀ z,R.foot b x z → b≤z ∧ z<heap) → ZeroFrom mem heap →
      heap+roundCleanupCharge (A+4+2*L) A (D.toForest s).edges.length<2^w →
      let result := removeZeroEdges D I s arr cnt rats u v fuel
      let r := (D.toForest s).edges.length-(D.toForest result.1).edges.length
      ∃ out final c y,
        Runs w p ω (roundCleanupBody entry pathMin pathZero flushCut)
          (startState [b,u,v,base,L,heap,fuel] mem pos) (.returned out) final c ∧
        R.rep b result.1 y final.mem ∧ RoundFlowAt I final.mem base h L P result.2.1 ∧
        heap≤out ∧ out≤heap+roundCleanupCharge (A+4+2*L) A r ∧ ZeroFrom final.mem out ∧
        (∀ z,R.foot b y z → b≤z ∧ z<out) ∧ (∀ z<base,final.mem z=mem z) ∧
        c+R.phi b y final.mem≤roundCleanupCharge
          (rate (D.toForest s).n+19*L+80) (rate (D.toForest s).n+17*L+115) r+R.phi b x mem := by
  intro fuel
  induction fuel with
  | zero =>
    intro b u v base heap s x mem pos arr cnt rats steps hw hN hTable hb hInv hFit hPath hFuel
    omega
  | succ fuel ih =>
    intro b u v base heap s x mem pos arr cnt rats steps hw hN hTable hb hInv hFit hPath hFuel
      hWeak hBounds hFlow hRep hFoot hZ hSpace
    dsimp only
    let Q := A+4+2*L
    let n := (D.toForest s).n
    let Cq := rate n+19*L+80
    let Cc := rate n+17*L+115
    have hInitial : heap+roundCleanupCharge Q A (D.toForest s).edges.length<2^w := hSpace
    have hQ : heap+Q<2^w := by
      unfold roundCleanupCharge at hInitial
      omega
    have hQAlloc := (hAlloc b u v heap).2
    have hValid := hD.2.1 s hInv
    obtain ⟨hWalk,_⟩ := findSteps_sound hValid.2.1 hPath
    have hConn : (D.toForest s).SameComp u v := ⟨_,hWalk.to_isWalk⟩
    obtain ⟨h₁,st₁,c₁,x₁,hQuery,hHeap,hBit,hRegs,hHit,hRep₁,hLo,hHi,hZero₁,hMem₁,hFoot₁,hC₁⟩ :=
      roundCleanupQuery_runs D rate allocation R himpl hMin hZero b u v base heap (fuel+1) s x
        mem pos ω hw hb hInv hFit hConn hRep hFoot hZ (by dsimp [Q] at hQ; omega)
    have hEnd₁ : h₁≤heap+Q := by dsimp [Q]; omega
    have hFlow₁ : RoundFlowAt I st₁.mem base h L P arr := by
      intro j
      have hj := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at hj
      exact (hFlow j).frozen hMem₁ (by omega)
    have hCQuery : c₁+R.phi b x₁ st₁.mem+7≤Cq+R.phi b x mem := by dsimp [Cq,n]; omega
    have hLeaf (bz : st₁.regs 8=0) :
        Runs w p ω (roundCleanupBody entry pathMin pathZero flushCut)
          (startState [b,u,v,base,L,heap,fuel+1] mem pos) (.returned h₁) st₁ (c₁+7) :=
      cleanup_return_leaf rfl hHeap bz hQuery
    rw [removeZeroEdges]
    cases hSel : D.pathMin s u v with
    | none =>
      exact ⟨h₁,st₁,c₁+7,x₁,hLeaf (by simpa [hSel,pathHitZeroValue] using hBit),hRep₁,hFlow₁,by omega,
        by simpa [roundCleanupCharge,Q] using hEnd₁,hZero₁,hFoot₁,
        fun z hz => hMem₁ z (by omega),by simpa [roundCleanupCharge,Cq,n,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hCQuery⟩
    | some hit =>
      dsimp only
      obtain ⟨hNonneg,hId,hX,hY,hPos⟩ :=
        roundCleanup_hit hD hInv hPath hWeak (fun t ht => (hBounds t ht).1) hSel
      by_cases hPositive : 0<hit.avail
      · rw [ite_eq_left hPositive]
        have bz : st₁.regs 8=0 := by simpa [hSel,pathHitZeroValue,hPos.mpr hPositive] using hBit
        exact ⟨h₁,st₁,c₁+7,x₁,hLeaf bz,hRep₁,hFlow₁,by omega,
          by simpa [roundCleanupCharge,Q] using hEnd₁,hZero₁,hFoot₁,
          fun z hz => hMem₁ z (by omega),
          by simpa [roundCleanupCharge,Cq,n,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hCQuery⟩
      · rw [ite_eq_right hPositive]
        have hZeroHit : hit.avail=0 := le_antisymm (le_of_not_gt hPositive) hNonneg
        have b₁ : st₁.regs 8=1 := by simpa [hSel,pathHitZeroValue,hZeroHit] using hBit
        obtain ⟨pre,post,hInv₂,hN₂,hLen₂,hFuel₂,hSub,hPre,hPreIn,hPostIn,hPost⟩ :=
          roundCleanup_split hD hInv hPath hFuel hSel
        let s₂ := D.cut s hit.x hit.y
        let arr₂ := fun j : Fin I.m => if j.val=hit.eid then hit.flow else arr j
        let cnt₂ := { cnt with pathMinOps := cnt.pathMinOps+1,cutOps := cnt.cutOps+1,otherSteps := cnt.otherSteps+3 }
        let rats₂ := hit.flow::hit.avail::rats
        have hN₂' : (D.toForest s₂).n=n := hN₂
        have hE₂ : (D.toForest s₂).edges.length+1=(D.toForest s).edges.length := hLen₂
        have hChargeN :
            roundCleanupCharge Q A (D.toForest s).edges.length =
              Q+A+roundCleanupCharge Q A (D.toForest s₂).edges.length+Q := by
          rw [← hE₂]
          simp only [roundCleanupCharge,Nat.mul_add,Nat.mul_one]
          omega
        have hW : fuel+1<2^w := hw _ (by simp)
        have hH₁ : h₁+allocation 2 [b,hit.x,hit.y,h₁]<2^w := by
          rw [hChargeN] at hInitial
          have := (hAlloc b hit.x hit.y h₁).1
          omega
        have hR (j : ℕ) (hj : j<7) :
            st₁.regs j=(startState [b,u,v,base,L,heap,fuel+1] mem pos).regs j := hRegs j hj
        obtain ⟨h₂,st₂,c₂,x₂,hCutRun,hRep₂,hFlow₂,hLo₂,hHi₂,hZero₂,hFoot₂,hMem₂,hRegs₂,
          hReg₂,hRx,hRy,hRf,hC₂⟩ :=
          roundCleanupCut_runs D hD rate allocation R himpl hCopy hCut I ⟨hit.eid,hId⟩ hit rfl
            b heap base h₁ fuel s x₁ st₁ ω
            ⟨hR 0 (by decide),hR 3 (by decide),hR 4 (by decide),hR 5 (by decide),hR 6 (by decide),hHeap⟩
            hW arr hFlow₁ (by simpa [hSel] using hHit) hL hTable hb hLo (hX.trans_le hN) (hY.trans_le hN)
            hInv hFit hRep₁ hFoot₁ hZero₁ hH₁
        have hEnd₂ : h₂≤heap+Q+A := by have := (hAlloc b hit.x hit.y h₁).1; omega
        change c₂+R.phi b x₂ st₂.mem≤rate n+(17*L+10)+80+R.phi b x₁ st₁.mem at hC₂
        have hFit₂ : ForestFits D h L P s₂ := hFit.cut hD hInv
        have hWeak₂ : ∀ e∈(D.toForest s₂).edges,ForestEdgeWeakInv I f e :=
          fun e he => hWeak e (hSub e he)
        have hB₂ : ∀ t∈pre,0≤t.dirAvail ∧ 0<t.flip.dirAvail :=
          fun t ht => hBounds t (hPreIn t ht)
        have hSpace₂ : h₂+roundCleanupCharge Q A (D.toForest s₂).edges.length<2^w := by omega
        have hW₂ : ∀ z∈[b,u,hit.x,base,L,h₂,fuel],z<2^w := by
          intro z hz
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hw _ (by simp)
          · exact hw _ (by simp)
          · exact hX.trans_le hN
          · exact hw _ (by simp)
          · exact hw _ (by simp)
          · omega
          · omega
        let res₁ := removeZeroEdges D I s₂ arr₂ cnt₂ rats₂ u hit.x fuel
        obtain ⟨hInv₃,_,hSub₃,hKeep₃,_,_,_,_,_,_,_,_,_,hlen₃,_,_,_,_,_,_⟩ :=
          removeZeroEdges_spec hD (f:=f) fuel s₂ arr₂ cnt₂ rats₂ u hit.x pre
            hInv₂ hPre hFuel₂ hWeak₂ hB₂
        have hN₃ : (D.toForest res₁.1).n=n :=
          (roundCleanup_n hD f fuel s₂ arr₂ cnt₂ rats₂ u hit.x pre
            hInv₂ hPre hFuel₂ hWeak₂ hB₂).trans hN₂'
        have h₁call : b≤h₂ := by omega
        obtain ⟨h₃,st₃,c₃,x₃,hLeft,hRep₃,hFlow₃,hLo₃,hHi₃,hZero₃,hFoot₃,hMem₃,hC₃⟩ :=
          ih b u hit.x base h₂ s₂ x₂ st₂.mem st₂.pos arr₂ cnt₂ rats₂ pre hW₂
            (hN₂'.trans_le hN) hTable h₁call hInv₂ hFit₂ hPre hFuel₂ hWeak₂ hB₂
            hFlow₂ hRep₂ hFoot₂ hZero₂ hSpace₂
        let r₁ := (D.toForest s₂).edges.length-(D.toForest res₁.1).edges.length
        have hr₁ : r₁+(D.toForest res₁.1).edges.length=(D.toForest s₂).edges.length := by
          dsimp [r₁]
          change (D.toForest res₁.1).edges.length≤(D.toForest s₂).edges.length at hlen₃
          omega
        change h₃≤h₂+roundCleanupCharge Q A r₁ at hHi₃
        have hHi₃' : h₃≤heap+Q+A+roundCleanupCharge Q A r₁ := by omega
        have hSpace₃ : h₃+roundCleanupCharge Q A (D.toForest res₁.1).edges.length<2^w := by
          have hSum :
              roundCleanupCharge Q A r₁+roundCleanupCharge Q A (D.toForest res₁.1).edges.length =
                roundCleanupCharge Q A (D.toForest s₂).edges.length+Q := by
            have hx := congrArg (fun z => (2*Q+A)*z) hr₁
            change (2*Q+A)*(r₁+(D.toForest res₁.1).edges.length)=(2*Q+A)*(D.toForest s₂).edges.length at hx
            rw [Nat.mul_add] at hx
            simp only [roundCleanupCharge]
            omega
          omega
        have hW₃ : ∀ z∈[b,hit.y,v,base,L,h₃,fuel],z<2^w := by
          intro z hz
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hw _ (by simp)
          · exact hY.trans_le hN
          · exact hw _ (by simp)
          · exact hw _ (by simp)
          · exact hw _ (by simp)
          · omega
          · omega
        have hPath₃ := hPost res₁.1 hInv₃ hKeep₃
        have hB₃ : ∀ t∈post,0≤t.dirAvail ∧ 0<t.flip.dirAvail :=
          fun t ht => hBounds t (hPostIn t ht)
        have hWeak₃ : ∀ e∈(D.toForest res₁.1).edges,ForestEdgeWeakInv I f e :=
          fun e he => hWeak₂ e (hSub₃ e he)
        let res₂ := removeZeroEdges D I res₁.1 res₁.2.1 res₁.2.2.1 res₁.2.2.2 hit.y v fuel
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hlen₄,_,_,_,_,_,_⟩ :=
          removeZeroEdges_spec hD (f:=f) fuel res₁.1 res₁.2.1 res₁.2.2.1 res₁.2.2.2 hit.y v post
            hInv₃ hPath₃ (hlen₃.trans_lt hFuel₂) hWeak₃ hB₃
        have h₃call : b≤h₃ := by omega
        obtain ⟨h₄,st₄,c₄,x₄,hRight,hRep₄,hFlow₄,hLo₄,hHi₄,hZero₄,hFoot₄,hMem₄,hC₄⟩ :=
          ih b hit.y v base h₃ res₁.1 x₃ st₃.mem st₃.pos res₁.2.1 res₁.2.2.1 res₁.2.2.2 post
            hW₃ (hN₃.trans_le hN) hTable h₃call hInv₃ (fun e he => hFit₂ e (hSub₃ e he))
            hPath₃ (hlen₃.trans_lt hFuel₂) hWeak₃ hB₃ hFlow₃ hRep₃ hFoot₃ hZero₃ hSpace₃
        let left : State := ⟨st₃.mem,Function.update st₂.regs 7 h₃,st₃.pos⟩
        let final : State := ⟨st₄.mem,Function.update left.regs 7 h₄,st₄.pos⟩
        have regs₂ (j : ℕ) (hj : j<7) :
            st₂.regs j=(startState [b,u,v,base,L,heap,fuel+1] mem pos).regs j :=
          (hRegs₂ j hj).trans (hR j hj)
        have hArgsL : evalArgs w st₂ [.reg 0,.reg 1,.reg 9,.reg 3,.reg 4,.reg 7,.reg 11]=
            some [b,u,hit.x,base,L,h₂,fuel] := by
          have r₀ : st₂.regs 0=b := regs₂ 0 (by decide)
          have r₁' : st₂.regs 1=u := regs₂ 1 (by decide)
          have r₃ : st₂.regs 3=base := regs₂ 3 (by decide)
          have r₄ : st₂.regs 4=L := regs₂ 4 (by decide)
          simp [evalArgs,Expr.eval,r₀,r₁',r₃,r₄,hRx,hReg₂,hRf]
        have hArgsR : evalArgs w left [.reg 0,.reg 10,.reg 2,.reg 3,.reg 4,.reg 7,.reg 11]=
            some [b,hit.y,v,base,L,h₃,fuel] := by
          have r₀ : st₂.regs 0=b := regs₂ 0 (by decide)
          have r₂ : st₂.regs 2=v := regs₂ 2 (by decide)
          have r₃ : st₂.regs 3=base := regs₂ 3 (by decide)
          have r₄ : st₂.regs 4=L := regs₂ 4 (by decide)
          simp [evalArgs,Expr.eval,left,r₀,r₂,r₃,r₄,hRy,hRf]
        have hExec := cleanup_return_cut (fuel:=fuel) (out:=h₄) (final:=final) (by rfl)
          (by simp [final]) b₁ hQuery hCutRun
          (round_returning_call hBody hArgsL hLeft) (round_returning_call hBody hArgsR hRight)
        let r₂ := (D.toForest res₁.1).edges.length-(D.toForest res₂.1).edges.length
        have hlenEq : (D.toForest s).edges.length-(D.toForest res₂.1).edges.length=r₁+r₂+1 :=
          cleanupCuts_split hE₂ hlen₃ hlen₄
        refine ⟨h₄,final,_,x₄,hExec,hRep₄,hFlow₄,by omega,?_,hZero₄,hFoot₄,?_,?_⟩
        · change h₄≤heap+roundCleanupCharge Q A ((D.toForest s).edges.length-(D.toForest res₂.1).edges.length)
          rw [hlenEq,roundCleanupCharge_split]
          change h₄≤h₃+roundCleanupCharge Q A r₂ at hHi₄
          omega
        · intro z hz
          exact (hMem₄ z hz).trans ((hMem₃ z hz).trans ((hMem₂ z hz).trans (hMem₁ z (by omega))))
        · change c₁+c₂+(7+c₃+1)+(7+c₄+1)+10+R.phi b x₄ st₄.mem≤
            roundCleanupCharge Cq Cc ((D.toForest s).edges.length-(D.toForest res₂.1).edges.length)+R.phi b x mem
          rw [hlenEq,roundCleanupCharge_split]
          rw [hN₂'] at hC₃
          rw [hN₃] at hC₄
          change c₃+R.phi b x₃ st₃.mem≤roundCleanupCharge Cq Cc r₁+R.phi b x₂ st₂.mem at hC₃
          change c₄+R.phi b x₄ st₄.mem≤roundCleanupCharge Cq Cc r₂+R.phi b x₃ st₃.mem at hC₄
          change c₁+R.phi b x₁ st₁.mem≤rate n+19*L+70+R.phi b x mem at hC₁
          have hCosts : c₁+c₂+26+R.phi b x₂ st₂.mem≤Cq+Cc+R.phi b x mem := by
            dsimp only [Cq,Cc]
            have hRaw : c₂+R.phi b x₂ st₂.mem≤rate n+17*L+90+R.phi b x₁ st₁.mem := by omega
            omega
          omega

end MinCostFlow.IPM.Machine
