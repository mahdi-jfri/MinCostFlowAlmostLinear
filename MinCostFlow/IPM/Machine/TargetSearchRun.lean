module

public import MinCostFlow.IPM.Machine.TargetSearchLoop
public import MinCostFlow.IPM.Machine.TargetSearchEndpoints

/-!
# Complete machine bisection

Execute the counted midpoint loop, then test the unique optimal
target once more. That final successful record provides the
fixed-point flow needed by the rounding procedure.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The bisection and final call use at most one test per round
and one additional test. The final returned bit is one at the
exact integer optimum. -/
theorem targetSearch_runs_of_offset {w offsetTest : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (qp source heap limit radius space price : ℕ)
    (z : ℤ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {body : Stmt}
    (hbody : p.procs[offsetTest]?=some body)
    (hTwo : 2<2^w) (hRadius : 2*radius<2^w) (hRound : targetSearchRounds radius<2^w)
    (hSpace : heap+(targetSearchRounds radius+1)*space<2^w)
    (hlo : -(radius:ℤ)≤z) (hhi : z≤(radius:ℤ)) (hzero : ZeroFrom mem heap)
    (hTrial : ∀ (st : State) (offset : ℕ) (stream : ℕ → Bool),
      offset≤2*radius → heap≤st.regs 21 →
      (∀ b<heap,st.mem b=mem b) → ZeroFrom st.mem (st.regs 21) →
      st.regs 21+space<2^w →
      ∃ v final cost,
        Runs w p stream body
          (startState (targetOffsetPacket L F I offset qp source (st.regs 21) limit radius) st.mem st.pos)
          (.returned v) final cost ∧
        TargetOffsetResult F I L.exponent (st.regs 21) v (offsetTarget radius offset) z st.mem final.mem ∧
        v≤st.regs 21+space ∧ cost≤price) :
    let rounds := targetSearchRounds radius
    ∃ v final cost,
      Runs w p ω (targetSearchBody offsetTest)
        (startState (targetOffsetPacket L F I 0 qp source heap limit radius++[rounds]) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I L.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+(rounds+1)*space ∧ cost≤(rounds+1)*(price+69) := by
  dsimp only
  let rounds := targetSearchRounds radius
  change heap+(rounds+1)*space<2^w at hSpace
  obtain ⟨tick,htick,heq⟩ := offsetTarget_optimum radius z hlo hhi
  obtain ⟨first,hInit,hInv⟩ :=
    targetSearch_init_runs F I L qp source heap limit radius tick space mem pos ω hRadius hTwo htick hzero
  obtain ⟨st,c,hLoop,hEnd,hCost⟩ :=
    targetSearch_loop_runs F I L qp source heap limit radius tick space price mem first ω hbody
      hTwo hRadius hRound hSpace hInv (heq.symm ▸ hTrial)
  obtain ⟨ht, _⟩ := targetSearch_final_offset F I L qp source heap limit radius tick space mem st hEnd
  obtain ⟨_,_,hFixed,_,_,_,_,hLo,hHi,hFrame,hZero⟩ := hEnd
  have hHeapSpace : st.regs 21+space<2^w := by
    rw [Nat.add_one_mul] at hSpace
    have hh : st.regs 21≤heap+rounds*space := hHi
    omega
  obtain ⟨v,res,d,hRun,hResult,hEndOut,hCostOut⟩ :=
    hTrial st tick ω htick hLo hFrame hZero hHeapSpace
  have hArgs := targetSearch_args F I L tick qp source (st.regs 21) limit radius 26 st ht (by
    intro j hj h6
    by_cases h21 : j=21
    · subst j
      rfl
    · exact (hFixed j hj h6).trans
        (targetOffsetPacket_fixed F I L 0 tick qp source _ _ limit radius j hj h6 h21))
  obtain ⟨final,hRet,hMem⟩ := targetSearch_finish_runs st res hbody hArgs hRun
  rw [heq] at hResult
  obtain ⟨hvLo,hvWord,hZero',hFrame',hBool,hDecision,hFeas⟩ := hResult
  have hResult' : TargetOffsetResult F I L.exponent heap v z z mem final.mem := by
    rw [hMem]
    exact ⟨by omega,hvWord,hZero',fun j hj => (hFrame' j (hj.trans_le hLo)).trans (hFrame j hj),hBool,hDecision,hFeas⟩
  have hBit : final.mem (v-1)=1 := by rw [hMem]; exact hDecision.mpr le_rfl
  have htail : Runs w p ω (forUp 28 (.reg 25) (targetSearchStep offsetTest) ;; targetSearchFinish offsetTest)
      first (.returned v) final (c+d+30) :=
    runs_seq_iff.mpr (Or.inr ⟨st,c,d+29,hLoop,hRet,by omega⟩)
  refine ⟨v,final,10+(c+d+30)+1,runs_seq_iff.mpr (Or.inr ⟨first,10,c+d+30,hInit,htail,rfl⟩),
    hResult',hBit,?_,?_⟩
  · change v≤heap+(rounds+1)*space
    rw [Nat.add_one_mul]
    have hh : st.regs 21≤heap+rounds*space := hHi
    omega
  · change 10+(c+d+30)+1≤(rounds+1)*(price+69)
    rw [Nat.add_one_mul]
    have hh : c≤rounds*(price+69)+4 := hCost
    omega

/-- `V`-passing variant of `targetSearch_runs_of_offset`. -/
theorem targetSearchWithV_runs_of_offset {w offsetTest : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (qp source heap limit radius space price V : ℕ)
    (z : ℤ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {body : Stmt}
    (hbody : p.procs[offsetTest]?=some body)
    (hTwo : 2<2^w) (hRadius : 2*radius<2^w) (hV : V<2^w) (hRound : targetSearchRounds radius<2^w)
    (hSpace : heap+(targetSearchRounds radius+1)*space<2^w)
    (hlo : -(radius:ℤ)≤z) (hhi : z≤(radius:ℤ)) (hzero : ZeroFrom mem heap)
    (hTrial : ∀ (st : State) (offset : ℕ) (stream : ℕ → Bool),
      offset≤2*radius → heap≤st.regs 21 →
      (∀ b<heap,st.mem b=mem b) → ZeroFrom st.mem (st.regs 21) →
      st.regs 21+space<2^w →
      ∃ v final cost,
        Runs w p stream body
          (startState (targetOffsetPacketWithV L F I offset qp source (st.regs 21) limit radius V) st.mem st.pos)
          (.returned v) final cost ∧
        TargetOffsetResult F I L.exponent (st.regs 21) v (offsetTarget radius offset) z st.mem final.mem ∧
        v≤st.regs 21+space ∧ cost≤price) :
    let rounds := targetSearchRounds radius
    ∃ v final cost,
      Runs w p ω (targetSearchBodyWithV offsetTest)
        (startState (targetOffsetPacket L F I 0 qp source heap limit radius++[rounds,V]) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I L.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+(rounds+1)*space ∧ cost≤(rounds+1)*(price+69) := by
  dsimp only
  let rounds := targetSearchRounds radius
  change heap+(rounds+1)*space<2^w at hSpace
  let initial := startState (targetOffsetPacket L F I 0 qp source heap limit radius++[rounds,V]) mem pos
  let saved : State := {initial with regs := Function.update initial.regs 32 V}
  have hlen : (targetOffsetPacket L F I 0 qp source heap limit radius).length=25 :=
    targetOffsetPacket_length F I L 0 qp source heap limit radius
  have hsaveReg : initial.regs 26=V := by
    simp [initial,startState,targetOffsetPacket,targetEpochPacket]
  have hsave : Runs w p ω (.assign 32 (.reg 26)) initial .normal saved 2 :=
    runs_assign_iff.mpr ⟨V,by simp [Expr.eval,hsaveReg],rfl,rfl,rfl⟩
  have hsavedRegs : ∀ j<26,saved.regs j=
      (targetOffsetPacket L F I 0 qp source heap limit radius++[rounds]).getD j 0 := by
    intro j hj
    have h0 : saved.regs j=initial.regs j := by simp [saved,Function.update_of_ne (by omega : j≠32)]
    rw [h0]
    by_cases h25 : j<25
    · change (targetOffsetPacket L F I 0 qp source heap limit radius++[rounds,V]).getD j 0=_
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left (by rw [hlen]; exact h25)]
    · have hj25 : j=25 := by omega
      subst j
      simp [initial,startState,targetOffsetPacket,targetEpochPacket]
  obtain ⟨tick,htick,heq⟩ := offsetTarget_optimum radius z hlo hhi
  obtain ⟨first,hInit,hInv,hFirst32⟩ :=
    targetSearchWithV_init_runs F I L qp source heap limit radius tick space V mem saved ω
      hRadius hTwo htick hzero rfl hsavedRegs (by simp [saved])
  obtain ⟨st,c,hLoop,hEnd,hSt32,hCost⟩ :=
    targetSearchWithV_loop_runs F I L qp source heap limit radius tick space price V mem first ω hbody
      hTwo hRadius hV hRound hSpace ⟨hInv,hFirst32⟩ (heq.symm ▸ hTrial)
  obtain ⟨ht, _⟩ := targetSearch_final_offset F I L qp source heap limit radius tick space mem st hEnd
  obtain ⟨_,_,hFixed,_,_,_,_,hLo,hHi,hFrame,hZero⟩ := hEnd
  have hHeapSpace : st.regs 21+space<2^w := by
    rw [Nat.add_one_mul] at hSpace
    have hh : st.regs 21≤heap+rounds*space := hHi
    omega
  obtain ⟨v,res,d,hRun,hResult,hEndOut,hCostOut⟩ :=
    hTrial st tick ω htick hLo hFrame hZero hHeapSpace
  have hArgs0 := targetSearch_args F I L tick qp source (st.regs 21) limit radius 26 st ht (by
    intro j hj h6
    by_cases h21 : j=21
    · subst j
      rfl
    · exact (hFixed j hj h6).trans
        (targetOffsetPacket_fixed F I L 0 tick qp source _ _ limit radius j hj h6 h21))
  have hArgs : evalArgs w st (targetSearchArgsWithV 26)=
      some (targetOffsetPacketWithV L F I tick qp source (st.regs 21) limit radius V) :=
    evalArgs_append hArgs0 (by simp [evalArgs,Expr.eval,hSt32])
  obtain ⟨final,hRet,hMem⟩ := targetSearchWithV_finish_runs st res hbody hArgs hRun
  rw [heq] at hResult
  obtain ⟨hvLo,hvWord,hZero',hFrame',hBool,hDecision,hFeas⟩ := hResult
  have hResult' : TargetOffsetResult F I L.exponent heap v z z mem final.mem := by
    rw [hMem]
    exact ⟨by omega,hvWord,hZero',fun j hj => (hFrame' j (hj.trans_le hLo)).trans (hFrame j hj),hBool,hDecision,hFeas⟩
  have hBit : final.mem (v-1)=1 := by rw [hMem]; exact hDecision.mpr le_rfl
  have htail : Runs w p ω (forUp 28 (.reg 25) (targetSearchStepWithV offsetTest) ;; targetSearchFinishWithV offsetTest)
      first (.returned v) final (c+d+31) :=
    runs_seq_iff.mpr (Or.inr ⟨st,c,d+30,hLoop,hRet,by omega⟩)
  have hinner : Runs w p ω (targetSearchInit ;;
      forUp 28 (.reg 25) (targetSearchStepWithV offsetTest) ;; targetSearchFinishWithV offsetTest)
      saved (.returned v) final (10+(c+d+31)+1) :=
    runs_seq_iff.mpr (Or.inr ⟨first,10,c+d+31,hInit,htail,rfl⟩)
  refine ⟨v,final,2+(10+(c+d+31)+1)+1,runs_seq_iff.mpr (Or.inr ⟨saved,2,10+(c+d+31)+1,hsave,hinner,rfl⟩),
    hResult',hBit,?_,?_⟩
  · change v≤heap+(rounds+1)*space
    rw [Nat.add_one_mul]
    have hh : st.regs 21≤heap+rounds*space := hHi
    omega
  · change 2+(10+(c+d+31)+1)+1≤(rounds+1)*(price+69)
    rw [Nat.add_one_mul]
    have hh : c≤rounds*(price+69)+4 := hCost
    omega

end MinCostFlow.IPM.Machine
