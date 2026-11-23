module

public import MinCostFlow.IPM.Machine.TargetSearchInvariant

/-!
# The bounded bisection loop

Every active iteration tests one midpoint. The actual comparison
narrowing preserves the optimum offset and halves the span. After
collapse, an iteration only advances the outer counter.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 400000 in
/-- Find the unique optimal offset with at most the binary length of
the initial span in target tests. Workspace grows by at most one
test reservation per round. -/
theorem targetSearch_loop_runs {w offsetTest : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (qp source heap limit radius tick space price : ℕ)
    (mem : ℕ → ℕ) (first : State) (ω : ℕ → Bool) {p : Program} {body : Stmt}
    (hbody : p.procs[offsetTest]?=some body)
    (hTwo : 2<2^w) (hRadius : 2*radius<2^w)
    (hRound : targetSearchRounds radius<2^w)
    (hSpace : heap+(targetSearchRounds radius+1)*space<2^w)
    (hfirst : TargetSearchInvariant F I L qp source heap limit radius tick space mem 0 first)
    (hTrial : ∀ (st : State) (offset : ℕ) (stream : ℕ → Bool),
      offset≤2*radius → heap≤st.regs 21 →
      (∀ b<heap,st.mem b=mem b) → ZeroFrom st.mem (st.regs 21) →
      st.regs 21+space<2^w →
      ∃ v final cost,
        Runs w p stream body
          (startState (targetOffsetPacket L F I offset qp source (st.regs 21) limit radius) st.mem st.pos)
          (.returned v) final cost ∧
        TargetOffsetResult F I L.exponent (st.regs 21) v (offsetTarget radius offset)
          (offsetTarget radius tick) st.mem final.mem ∧
        v≤st.regs 21+space ∧ cost≤price) :
    ∃ final cost,
      Runs w p ω (forUp 28 (.reg 25) (targetSearchStep offsetTest)) first .normal final cost ∧
      TargetSearchInvariant F I L qp source heap limit radius tick space mem (targetSearchRounds radius) final ∧
      cost≤targetSearchRounds radius*(price+69)+4 := by
  let rounds := targetSearchRounds radius
  change heap+(rounds+1)*space<2^w at hSpace
  let Inv := TargetSearchInvariant F I L qp source heap limit radius tick space mem
  have hOne : 1<2^w := by omega
  have hLoop := Triple.forUp_const (r:=28) (hi:=.reg 25) (body:=targetSearchStep offsetTest)
    (Inv:=Inv) (price+60) 0 rounds (Nat.zero_le _) hOne (fun _ => hRound) (fun _ _ _ _ h => h.1)
    (fun _ st _ _ h => by change some (st.regs 25)=some rounds; exact congrArg some h.2.1)
    (by
      intro i _ hi st stream h
      let lo := st.regs 26
      let up := st.regs 27
      let cur := st.regs 21
      obtain ⟨hIndex,hLimit,hFixed,hlo,hup,hRad,hSpan,hHeap,hHeapBound,hFrame,hZero⟩ := h
      have hFuel : rounds-i=(rounds-(i+1))+1 := by omega
      have hNextSpace : i*space+space≤rounds*space := by
        rw [← Nat.add_one_mul]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
      have hLargeSpace : heap+rounds*space<2^w := by
        rw [Nat.add_one_mul] at hSpace
        omega
      by_cases hActive : lo<up
      · let mid := lo+(up-lo)/2
        let parent := targetSearchMidState st lo up
        have hMid : mid≤2*radius := (targetSearch_midpoint lo up hActive).2.le.trans hRad
        have hWord : up<2^w := hRad.trans_lt hRadius
        have hFit : st.regs 21+space<2^w := by omega
        obtain ⟨v,res,c,hCall,hResult,hEnd,hCost⟩ := hTrial st mid stream hMid hHeap hFrame hZero hFit
        have hArgs := targetSearch_args F I L mid qp source cur limit radius 29 parent (by simp [parent,targetSearchMidState,mid]) (by
          intro j hj h6
          have hf := hFixed j hj h6
          have hs := targetOffsetPacket_fixed F I L 0 mid qp source cur cur limit radius j hj h6
          by_cases h21 : j=21
          · subst j
            simp [parent,targetSearchMidState,cur,targetOffsetPacket,targetEpochPacket]
          · have hsame : parent.regs j=st.regs j := by
              simp [parent,targetSearchMidState,Function.update_of_ne (by omega : j≠29)]
            exact hsame.trans (hf.trans (hs h21)))
        obtain ⟨hVLo,hVWord,hVZero,hVFrame,hBit,hDecision,_⟩ := hResult
        have hMidBit : res.mem (v-1)=1 ↔ tick≤mid := hDecision.trans (offsetTarget_le_offsetTarget radius tick mid)
        obtain ⟨next,d,hRun,hMem,hNewHeap,hNewLo,hNewHi,hRegFrame,hTime⟩ :=
          targetSearchStep_active st res hbody rfl rfl hActive hWord hTwo hVWord hArgs hCall hBit
        rw [hFuel] at hSpan
        obtain ⟨_,hlo',hhi',hHiOld,hSpan'⟩ :=
          targetSearch_narrow lo up tick (rounds-(i+1)) hlo hup hSpan hActive (res.mem (v-1)) hMidBit
        let current : State := {next with regs := Function.update next.regs 28 (i+1)}
        have hRegs : ∀ j<25,j≠6 → current.regs j=
            (targetOffsetPacket L F I 0 qp source v limit radius).getD j 0 := by
          intro j hj h6
          by_cases h21 : j=21
          · subst j
            change current.regs 21=v
            simpa only [current,Function.update_of_ne (by decide : 21≠28)] using hNewHeap
          · have hv := hRegFrame j h21 (by omega) (by omega) (by omega) (by omega) (by omega)
            simp only [current,Function.update_of_ne (by omega : j≠28)]
            exact hv.trans ((hFixed j hj h6).trans
              (targetOffsetPacket_fixed F I L 0 0 qp source cur v limit radius j hj h6 h21))
        have hCurrentLo : current.regs 26=next.regs 26 := by simp [current]
        have hCurrentHi : current.regs 27=next.regs 27 := by simp [current]
        have hCurrentHeap : current.regs 21=v := by simpa [current] using hNewHeap
        have hNewInv : Inv (i+1) current := by
          unfold Inv TargetSearchInvariant
          dsimp only
          rw [hCurrentHeap,hCurrentLo,hCurrentHi,hNewLo,hNewHi]
          refine ⟨by simp [current],?_,hRegs,hlo',hhi',hHiOld.trans hRad,hSpan',by omega,?_,?_,?_⟩
          · simpa [current,hLimit,rounds] using hRegFrame 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · rw [Nat.add_one_mul]
            omega
          · intro j hj
            change next.mem j=mem j
            rw [hMem,(hVFrame j (hj.trans_le hHeap)),hFrame j hj]
          · change ZeroFrom next.mem v
            rw [hMem]
            exact hVZero
        refine ⟨.normal,next,d,hRun,⟨hNewInv,?_⟩,?_⟩
        · exact (hRegFrame 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIndex
        · change d≤price+60
          omega
      · have hLe : up≤lo := Nat.le_of_not_gt hActive
        have hEqual : up-lo=0 := Nat.sub_eq_zero_of_le hLe
        have hRun := targetSearchStep_inactive (offsetTest:=offsetTest) (p:=p) (ω:=stream) st hLe hOne
        let current : State := {st with regs:=Function.update st.regs 28 (i+1)}
        have hSpan' : up-lo<2^(rounds-(i+1)) := by rw [hEqual]; exact Nat.pow_pos (by decide)
        have hv : st.regs 21≤heap+(i+1)*space := by rw [Nat.add_one_mul]; omega
        have hNewInv : Inv (i+1) current := by
          refine ⟨by simp [current],by simpa [current] using hLimit,?_,?_,?_,?_,?_,?_,?_,hFrame,?_⟩
          · intro j hj hj6
            simpa only [current,Function.update_of_ne (by omega : j≠28),Function.update_of_ne (by decide : 21≠28)] using hFixed j hj hj6
          · simpa [current] using hlo
          · simpa [current] using hup
          · simpa [current] using hRad
          · simpa [current] using hSpan'
          · simpa [current] using hHeap
          · simpa [current] using hv
          · simpa [current] using hZero
        exact ⟨.normal,st,6,hRun,⟨hNewInv,hIndex⟩,by change 6≤price+60; omega⟩)
  obtain ⟨o,final,c,hRun,hPost,hCost⟩ := hLoop first ω hfirst
  cases o with
  | returned _ => exact False.elim hPost
  | normal =>
    refine ⟨final,c,hRun,hPost,?_⟩
    change c≤(rounds-0)*(price+60+1+8)+(1+3) at hCost
    simpa only [Nat.sub_zero,Nat.add_assoc,Nat.reduceAdd] using hCost

/-- `V`-passing variant of `targetSearch_loop_runs`: preserves `V` in `.reg 32`. -/
theorem targetSearchWithV_loop_runs {w offsetTest : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (qp source heap limit radius tick space price V : ℕ)
    (mem : ℕ → ℕ) (first : State) (ω : ℕ → Bool) {p : Program} {body : Stmt}
    (hbody : p.procs[offsetTest]?=some body)
    (hTwo : 2<2^w) (hRadius : 2*radius<2^w) (_hV : V<2^w)
    (hRound : targetSearchRounds radius<2^w)
    (hSpace : heap+(targetSearchRounds radius+1)*space<2^w)
    (hfirst : TargetSearchInvariant F I L qp source heap limit radius tick space mem 0 first ∧ first.regs 32=V)
    (hTrial : ∀ (st : State) (offset : ℕ) (stream : ℕ → Bool),
      offset≤2*radius → heap≤st.regs 21 →
      (∀ b<heap,st.mem b=mem b) → ZeroFrom st.mem (st.regs 21) →
      st.regs 21+space<2^w →
      ∃ v final cost,
        Runs w p stream body
          (startState (targetOffsetPacketWithV L F I offset qp source (st.regs 21) limit radius V) st.mem st.pos)
          (.returned v) final cost ∧
        TargetOffsetResult F I L.exponent (st.regs 21) v (offsetTarget radius offset)
          (offsetTarget radius tick) st.mem final.mem ∧
        v≤st.regs 21+space ∧ cost≤price) :
    ∃ final cost,
      Runs w p ω (forUp 28 (.reg 25) (targetSearchStepWithV offsetTest)) first .normal final cost ∧
      TargetSearchInvariant F I L qp source heap limit radius tick space mem (targetSearchRounds radius) final ∧
      final.regs 32=V ∧
      cost≤targetSearchRounds radius*(price+69)+4 := by
  let rounds := targetSearchRounds radius
  change heap+(rounds+1)*space<2^w at hSpace
  let Inv := fun i st => TargetSearchInvariant F I L qp source heap limit radius tick space mem i st ∧ st.regs 32=V
  have hOne : 1<2^w := by omega
  have hLoop := Triple.forUp_const (r:=28) (hi:=.reg 25) (body:=targetSearchStepWithV offsetTest)
    (Inv:=Inv) (price+60) 0 rounds (Nat.zero_le _) hOne (fun _ => hRound) (fun _ _ _ _ h => h.1.1)
    (fun _ st _ _ h => by change some (st.regs 25)=some rounds; exact congrArg some h.1.2.1)
    (by
      intro i _ hi st stream h
      let lo := st.regs 26
      let up := st.regs 27
      let cur := st.regs 21
      have h32 : st.regs 32=V := h.2
      obtain ⟨hIndex,hLimit,hFixed,hlo,hup,hRad,hSpan,hHeap,hHeapBound,hFrame,hZero⟩ := h.1
      have hFuel : rounds-i=(rounds-(i+1))+1 := by omega
      have hNextSpace : i*space+space≤rounds*space := by
        rw [← Nat.add_one_mul]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
      have hLargeSpace : heap+rounds*space<2^w := by
        rw [Nat.add_one_mul] at hSpace
        omega
      by_cases hActive : lo<up
      · let mid := lo+(up-lo)/2
        let parent := targetSearchMidState st lo up
        have hMid : mid≤2*radius := (targetSearch_midpoint lo up hActive).2.le.trans hRad
        have hWord : up<2^w := hRad.trans_lt hRadius
        have hFit : st.regs 21+space<2^w := by omega
        obtain ⟨v,res,c,hCall,hResult,hEnd,hCost⟩ := hTrial st mid stream hMid hHeap hFrame hZero hFit
        have hArgs0 := targetSearch_args F I L mid qp source cur limit radius 29 parent (by simp [parent,targetSearchMidState,mid]) (by
          intro j hj h6
          have hf := hFixed j hj h6
          have hs := targetOffsetPacket_fixed F I L 0 mid qp source cur cur limit radius j hj h6
          by_cases h21 : j=21
          · subst j
            simp [parent,targetSearchMidState,cur,targetOffsetPacket,targetEpochPacket]
          · have hsame : parent.regs j=st.regs j := by
              simp [parent,targetSearchMidState,Function.update_of_ne (by omega : j≠29)]
            exact hsame.trans (hf.trans (hs h21)))
        have hp32 : parent.regs 32=V := by
          simpa [parent,targetSearchMidState,Function.update_of_ne (by decide : (32:ℕ)≠29)] using h32
        have hArgs : evalArgs w parent (targetSearchArgsWithV 29)=
            some (targetOffsetPacketWithV L F I mid qp source cur limit radius V) :=
          evalArgs_append hArgs0 (by simp [evalArgs,Expr.eval,hp32])
        obtain ⟨hVLo,hVWord,hVZero,hVFrame,hBit,hDecision,_⟩ := hResult
        have hMidBit : res.mem (v-1)=1 ↔ tick≤mid := hDecision.trans (offsetTarget_le_offsetTarget radius tick mid)
        obtain ⟨next,d,hRun,hMem,hNewHeap,hNewLo,hNewHi,hRegFrame,hTime⟩ :=
          targetSearchStepWithV_active st res hbody rfl rfl hActive hWord hTwo hVWord hArgs hCall hBit
        rw [hFuel] at hSpan
        obtain ⟨_,hlo',hhi',hHiOld,hSpan'⟩ :=
          targetSearch_narrow lo up tick (rounds-(i+1)) hlo hup hSpan hActive (res.mem (v-1)) hMidBit
        let current : State := {next with regs := Function.update next.regs 28 (i+1)}
        have hRegs : ∀ j<25,j≠6 → current.regs j=
            (targetOffsetPacket L F I 0 qp source v limit radius).getD j 0 := by
          intro j hj h6
          by_cases h21 : j=21
          · subst j
            change current.regs 21=v
            simpa only [current,Function.update_of_ne (by decide : 21≠28)] using hNewHeap
          · have hv := hRegFrame j h21 (by omega) (by omega) (by omega) (by omega) (by omega)
            simp only [current,Function.update_of_ne (by omega : j≠28)]
            exact hv.trans ((hFixed j hj h6).trans
              (targetOffsetPacket_fixed F I L 0 0 qp source cur v limit radius j hj h6 h21))
        have hCurrentLo : current.regs 26=next.regs 26 := by simp [current]
        have hCurrentHi : current.regs 27=next.regs 27 := by simp [current]
        have hCurrentHeap : current.regs 21=v := by simpa [current] using hNewHeap
        have hCurrent32 : current.regs 32=V := by
          have h32' := hRegFrame 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          simpa [current,Function.update_of_ne (by decide : (32:ℕ)≠28),h32] using h32'
        have hNewInv : Inv (i+1) current := by
          refine ⟨?_,hCurrent32⟩
          unfold TargetSearchInvariant
          dsimp only
          rw [hCurrentHeap,hCurrentLo,hCurrentHi,hNewLo,hNewHi]
          refine ⟨by simp [current],?_,hRegs,hlo',hhi',hHiOld.trans hRad,hSpan',by omega,?_,?_,?_⟩
          · simpa [current,hLimit,rounds] using hRegFrame 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · rw [Nat.add_one_mul]
            omega
          · intro j hj
            change next.mem j=mem j
            rw [hMem,(hVFrame j (hj.trans_le hHeap)),hFrame j hj]
          · change ZeroFrom next.mem v
            rw [hMem]
            exact hVZero
        refine ⟨.normal,next,d,hRun,⟨hNewInv,?_⟩,?_⟩
        · exact (hRegFrame 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIndex
        · change d≤price+60
          omega
      · have hLe : up≤lo := Nat.le_of_not_gt hActive
        have hEqual : up-lo=0 := Nat.sub_eq_zero_of_le hLe
        have hRun := targetSearchStepWithV_inactive (offsetTest:=offsetTest) (p:=p) (ω:=stream) st hLe hOne
        let current : State := {st with regs:=Function.update st.regs 28 (i+1)}
        have hSpan' : up-lo<2^(rounds-(i+1)) := by rw [hEqual]; exact Nat.pow_pos (by decide)
        have hv : st.regs 21≤heap+(i+1)*space := by rw [Nat.add_one_mul]; omega
        have hNewInv : Inv (i+1) current := by
          refine ⟨⟨by simp [current],by simpa [current] using hLimit,?_,?_,?_,?_,?_,?_,?_,hFrame,?_⟩,?_⟩
          · intro j hj hj6
            simpa only [current,Function.update_of_ne (by omega : j≠28),Function.update_of_ne (by decide : 21≠28)] using hFixed j hj hj6
          · simpa [current] using hlo
          · simpa [current] using hup
          · simpa [current] using hRad
          · simpa [current] using hSpan'
          · simpa [current] using hHeap
          · simpa [current] using hv
          · simpa [current] using hZero
          · simpa [current] using h32
        exact ⟨.normal,st,6,hRun,⟨hNewInv,hIndex⟩,by change 6≤price+60; omega⟩)
  obtain ⟨o,final,c,hRun,hPost,hCost⟩ := hLoop first ω hfirst
  cases o with
  | returned _ => exact False.elim hPost
  | normal =>
    refine ⟨final,c,hRun,hPost.1,hPost.2,?_⟩
    change c≤(rounds-0)*(price+60+1+8)+(1+3) at hCost
    simpa only [Nat.sub_zero,Nat.add_assoc,Nat.reduceAdd] using hCost

end MinCostFlow.IPM.Machine
