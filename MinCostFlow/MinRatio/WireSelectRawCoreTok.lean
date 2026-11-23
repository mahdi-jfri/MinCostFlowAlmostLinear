module

public import MinCostFlow.MinRatio.WireSelectRawStitch
import WordRAM.Tactic

/-!
# Execution of the `i < d` branch of `selectRawRouteBody`

Verifies `selectRawRoute_branch_lt_runs`: the `i < d` branch of `selectRawRouteBody` loads
`embPtr[i]` directly from `smEntryAddr metaPtr d 5 i`, reads `wPtr = mem[embPtr + eBest]` and
`embLen = mem[wPtr]`, and composes `selectFillRev`, `selectSplitSteps`, and `selectEmitStitches`
with no sparse-core `opCore 4` readout.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program

set_option maxHeartbeats 600000 in
/-- Executes the `i < d` branch of `selectRawRouteBody` from `⟨mem, regsP, posP⟩`, reading
`embPtr[i]` directly from `metaPtr` and composing `fillRev`, `splitSteps`, and `emitStitches`. -/
theorem selectRawRoute_branch_lt_runs
    {w fillRev splitSteps emitStitches hb descBase workHeap eBest i d slots
      intToExt tailSlot headSlot metaPtr embPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {regsP : ℕ → ℕ} {posP : ℕ}
    {G0 F : MGraph} {embP : List (ℕ × Bool)} {flip : Bool}
    (hw16 : 16 < 2 ^ w)
    (hFillRev : MeetsContract w p fillRev (selectFillRevContract w embP))
    (hSplitSteps : MeetsContract w p splitSteps
      (selectSplitStepsContract w G0 F ((eBest, true) :: walkRev embP) flip))
    (hEmitStitches : MeetsContract w p emitStitches
      (selectEmitStitchesContract w G0 ((eBest, true) :: walkRev embP) flip
        (((orientWalkSteps ((eBest, true) :: walkRev embP) flip).filter
          (fun x => decide (x.1 ∈ F.E))).map (fun x => (G0.src x, G0.dst x)))))
    (hr1 : regsP 1 = hb) (hr2 : regsP 2 = descBase) (hr3 : regsP 3 = workHeap)
    (hr9 : regsP 9 = eBest) (hr10 : regsP 10 = i) (hr14 : regsP 14 = if flip then 1 else 0)
    (hr16 : regsP 16 = d) (hr17 : regsP 17 = slots)
    (hr21 : regsP 21 = intToExt) (hr22 : regsP 22 = tailSlot) (hr23 : regsP 23 = headSlot)
    (hMetaHdr : mem (hb + shMetaOff) = metaPtr)
    (hEmbPtrRd : mem (smEntryAddr metaPtr d 5 i) = embPtr)
    (hHbW : hb + shMetaOff < 2 ^ w)
    (hMetaW : metaPtr + selectLevelMetaSize d < 2 ^ w)
    (hiLt : i < d) (hdb6 : descBase + 6 = workHeap)
    (hwork1W : workHeap + 8 * (embP.length + 1) < 2 ^ w)
    (hEmbPtr : embPtr + eBest < workHeap)
    (hWPtrHi : mem (embPtr + eBest) + 1 + 2 * embP.length ≤ workHeap)
    (hMW1 : MWalkAt mem (mem (embPtr + eBest)) embP)
    (hEmbPw : ∀ j (hj : j < embP.length), embP[j].1 < 2 ^ w)
    (hWE_ends : ∀ x ∈ (eBest, true) :: walkRev embP,
      mem (intToExt + mem (tailSlot + x.1)) = G0.tail x.1 ∧
      mem (intToExt + mem (headSlot + x.1)) = G0.head x.1 ∧
      tailSlot + x.1 < descBase ∧ headSlot + x.1 < descBase ∧
      intToExt + mem (tailSlot + x.1) < descBase ∧
      intToExt + mem (headSlot + x.1) < descBase ∧
      G0.tail x.1 < 2 ^ w ∧ G0.head x.1 < 2 ^ w)
    (hWE_slot : ∀ x ∈ (eBest, true) :: walkRev embP,
      x.1 ∈ G0.E ∧ (x.1 ∈ F.E ↔ mem (slots + x.1) ≠ 0) ∧
      slots + x.1 < descBase ∧ x.1 < 2 ^ w)
    (hRegW : slots < 2 ^ w ∧ intToExt < 2 ^ w ∧ tailSlot < 2 ^ w ∧ headSlot < 2 ^ w) :
    let W := (eBest, true) :: walkRev embP
    let K := embP.length + 1
    let edgesBase := workHeap + 2 * K
    let pathsBase := workHeap + 4 * K
    let work1 := workHeap + 8 * K
    ∃ st' c,
      Runs w p ω
        (.assign 27 (.load (.bin .add (.reg 1) (.const shMetaOff))) ;;
         .assign 28 (.bin .add (.bin .add (.reg 27) (.const smTableOff))
           (.bin .add (.bin .mul (.const 5) (.bin .add (.reg 16) (.const 1))) (.reg 10))) ;;
         .assign 30 (.load (.reg 28)) ;;
         .assign 31 (.load (.bin .add (.reg 30) (.reg 9))) ;;
         .assign 32 (.load (.reg 31)) ;;
         .assign 33 (.bin .add (.reg 32) (.const 1)) ;;
         .assign 34 (.reg 3) ;;
         .assign 35 (.bin .add (.reg 34) (.bin .mul (.const 2) (.reg 33))) ;;
         .assign 36 (.bin .add (.reg 35) (.bin .mul (.const 2) (.reg 33))) ;;
         .assign 37 (.bin .add (.reg 36) (.bin .mul (.const 4) (.reg 33))) ;;
         .store (.reg 34) (.reg 9) ;;
         .store (.bin .add (.reg 34) (.const 1)) (.const 1) ;;
         .call 38 fillRev [.reg 31, .reg 32, .reg 34, .const 0] ;;
         .store (.bin .add (.reg 2) (.const 2)) (.reg 35) ;;
         .store (.bin .add (.reg 2) (.const 3)) (.const 0) ;;
         .store (.bin .add (.reg 2) (.const 4)) (.reg 36) ;;
         .store (.bin .add (.reg 2) (.const 5)) (.const 0) ;;
         .call 38 splitSteps [.reg 17, .reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
           .reg 35, .reg 36, .reg 2, .const 0] ;;
         .call 38 emitStitches [.reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
           .reg 36, .reg 2, .const 0] ;;
         .ret (.reg 37))
        ⟨mem, regsP, posP⟩ (.returned work1) st' c ∧
      st'.mem (descBase + 2) = edgesBase ∧
      st'.mem (descBase + 3) = (rawEdgesOfWalk F W flip).length ∧
      st'.mem (descBase + 4) = pathsBase ∧
      st'.mem (descBase + 5) = (rawPathsOfWalk G0 F W flip).length ∧
      ExplicitEdgesAt st'.mem edgesBase (rawEdgesOfWalk F W flip) ∧
      PathEndpointsAt st'.mem pathsBase (rawPathsOfWalk G0 F W flip) ∧
      (∀ a, (a < descBase ∨ work1 ≤ a) → st'.mem a = mem a) ∧
      c ≤ 350 * K + 195 := by
  dsimp only
  set W := (eBest, true) :: walkRev embP
  set K := embP.length + 1
  set wPtr := mem (embPtr + eBest)
  set edgesBase := workHeap + 2 * K
  set pathsBase := workHeap + 4 * K
  set work1 := workHeap + 8 * K
  have hWlen : W.length = K := by simp [W, walkRev, K]
  have hEmbLenRd : mem wPtr = embP.length := (mWalkAt_read hMW1).1
  have heBestW : eBest < 2 ^ w := (hWE_slot (eBest, true) List.mem_cons_self).2.2.2
  have hflW : (if flip then 1 else 0) < 2 ^ w := by split <;> omega
  have hwPtrW : wPtr < 2 ^ w := by omega
  have hembLenW : embP.length < 2 ^ w := by omega
  have hKW : K < 2 ^ w := by omega
  have hwhW : workHeap < 2 ^ w := by omega
  have hedgesW : edgesBase < 2 ^ w := by omega
  have hpathsW : pathsBase < 2 ^ w := by omega
  have hdbW : descBase < 2 ^ w := by omega
  have hmsz : selectLevelMetaSize d = 2 + 8 * (d + 1) := rfl
  have hp0Def :
      (((orientWalkSteps W flip).filter (fun x => decide (x.1 ∈ F.E))).map
        (fun x => (G0.src x, G0.dst x))).length ≤ K := by
    rw [List.length_map]
    refine (List.length_filter_le _ _).trans ?_
    unfold orientWalkSteps; cases flip <;> simp [hWlen]
  have hRawPathsLen : (rawPathsOfWalk G0 F W flip).length =
      (((orientWalkSteps W flip).filter (fun x => decide (x.1 ∈ F.E))).map
        (fun x => (G0.src x, G0.dst x))).length + K := by
    unfold rawPathsOfWalk
    rw [List.length_append]
    have h2 : (if flip then (cycleSegments G0 W).2.map Prod.swap else (cycleSegments G0 W).2).length = K := by
      cases flip <;> simp [(cycleSegments_eq G0 W).2, hWlen]
    rw [h2]
  have hrun : ∃ o st' c, Runs w p ω
      (.assign 27 (.load (.bin .add (.reg 1) (.const shMetaOff))) ;;
       .assign 28 (.bin .add (.bin .add (.reg 27) (.const smTableOff))
         (.bin .add (.bin .mul (.const 5) (.bin .add (.reg 16) (.const 1))) (.reg 10))) ;;
       .assign 30 (.load (.reg 28)) ;;
       .assign 31 (.load (.bin .add (.reg 30) (.reg 9))) ;;
       .assign 32 (.load (.reg 31)) ;;
       .assign 33 (.bin .add (.reg 32) (.const 1)) ;;
       .assign 34 (.reg 3) ;;
       .assign 35 (.bin .add (.reg 34) (.bin .mul (.const 2) (.reg 33))) ;;
       .assign 36 (.bin .add (.reg 35) (.bin .mul (.const 2) (.reg 33))) ;;
       .assign 37 (.bin .add (.reg 36) (.bin .mul (.const 4) (.reg 33))) ;;
       .store (.reg 34) (.reg 9) ;;
       .store (.bin .add (.reg 34) (.const 1)) (.const 1) ;;
       .call 38 fillRev [.reg 31, .reg 32, .reg 34, .const 0] ;;
       .store (.bin .add (.reg 2) (.const 2)) (.reg 35) ;;
       .store (.bin .add (.reg 2) (.const 3)) (.const 0) ;;
       .store (.bin .add (.reg 2) (.const 4)) (.reg 36) ;;
       .store (.bin .add (.reg 2) (.const 5)) (.const 0) ;;
       .call 38 splitSteps [.reg 17, .reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
         .reg 35, .reg 36, .reg 2, .const 0] ;;
       .call 38 emitStitches [.reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
         .reg 36, .reg 2, .const 0] ;;
       .ret (.reg 37))
      ⟨mem, regsP, posP⟩ o st' c ∧
      (o = .returned work1 ∧
       st'.mem (descBase + 2) = edgesBase ∧
       st'.mem (descBase + 3) = (rawEdgesOfWalk F W flip).length ∧
       st'.mem (descBase + 4) = pathsBase ∧
       st'.mem (descBase + 5) = (rawPathsOfWalk G0 F W flip).length ∧
       ExplicitEdgesAt st'.mem edgesBase (rawEdgesOfWalk F W flip) ∧
       PathEndpointsAt st'.mem pathsBase (rawPathsOfWalk G0 F W flip) ∧
       (∀ a, (a < descBase ∨ work1 ≤ a) → st'.mem a = mem a)) ∧
      c ≤ 350 * K + 195 := by
    apply runs_start_le
    refine runs_seq_assign_flat (v := metaPtr)
      (by simp only [shMetaOff] at hMetaHdr hHbW
          simp [Expr.eval, BinOp.eval, hr1, shMetaOff, show 13 < 2 ^ w by omega,
            show hb + 13 < 2 ^ w by omega, hMetaHdr]) ?_
    refine runs_seq_assign_flat (v := smEntryAddr metaPtr d 5 i)
      (by simp only [smEntryAddr, smTableOff]
          have h1 : metaPtr + 2 < 2 ^ w := by omega
          have h2 : d + 1 < 2 ^ w := by omega
          have h3 : 5 * (d + 1) < 2 ^ w := by omega
          have h4 : 5 * (d + 1) + i < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, hr10, hr16, show 1 < 2 ^ w by omega,
            show 2 < 2 ^ w by omega, show 5 < 2 ^ w by omega, h1, h2, h3, h4, Nat.add_assoc]; omega) ?_
    refine runs_seq_assign_flat (v := embPtr)
      (by simp [Expr.eval, hEmbPtrRd]) ?_
    refine runs_seq_assign_flat (v := wPtr)
      (by simp [Expr.eval, BinOp.eval, hr9, show embPtr + eBest < 2 ^ w by omega, wPtr]) ?_
    refine runs_seq_assign_flat (v := embP.length) (by simp [Expr.eval, hEmbLenRd]) ?_
    refine runs_seq_assign_flat (v := K)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show embP.length + 1 < 2 ^ w by omega, K]) ?_
    refine runs_seq_assign_flat (v := workHeap) (by simp [Expr.eval, hr3]) ?_
    refine runs_seq_assign_flat (v := edgesBase)
      (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 2 * K < 2 ^ w by omega,
            show workHeap + 2 * K < 2 ^ w by omega, edgesBase]) ?_
    refine runs_seq_assign_flat (v := pathsBase)
      (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 2 * K < 2 ^ w by omega,
            show edgesBase + 2 * K < 2 ^ w by dsimp only [edgesBase]; omega]
          dsimp only [edgesBase, pathsBase]; omega) ?_
    refine runs_seq_assign_flat (v := work1)
      (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show 4 * K < 2 ^ w by omega,
            show pathsBase + 4 * K < 2 ^ w by dsimp only [pathsBase]; omega]
          dsimp only [pathsBase, work1]; omega) ?_
    refine runs_seq_store_flat (x := workHeap) (v := eBest) (by eval_expr) (by simp [Expr.eval, hr9]) ?_
    refine runs_seq_store_flat (x := workHeap + 1) (v := 1)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show workHeap + 1 < 2 ^ w by omega])
      (by eval_expr) ?_
    set mem2 := Function.update (Function.update mem workHeap eBest) (workHeap + 1) 1
    have hm2_out (a : ℕ) (h0 : a ≠ workHeap) (h1 : a ≠ workHeap + 1) : mem2 a = mem a := by
      change Function.update (Function.update mem _ _) _ _ a = _
      rw [Function.update_of_ne h1, Function.update_of_ne h0]
    have hm2_0 : mem2 workHeap = eBest := by
      change Function.update (Function.update mem _ _) _ _ _ = _
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hm2_1 : mem2 (workHeap + 1) = 1 := by
      change Function.update _ _ _ _ = _; exact Function.update_self ..
    clear_value mem2
    have hMW2 : MWalkAt mem2 wPtr embP := fun j hj => by
      have hlen := mWalkEncode_length embP
      exact (hm2_out _ (by omega) (by omega)).trans (hMW1 j hj)
    -- Call `fillRev`
    refine runs_seq_call_flat hFillRev (vs := [wPtr, embP.length, workHeap, 0])
      (by simp [evalArgs, Expr.eval]) (by wram_words) ?_ ?_
    · exact ⟨wPtr, workHeap, 0, rfl, hw16, Nat.zero_le _, hMW2, hWPtrHi, by omega, hEmbPw,
        fun j hj => by simp at hj⟩
    · intro _ mem3 pos3 hp3
      obtain ⟨hRev3, hfr3⟩ := hp3
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hRev3 hfr3
      have hWAt3 : ExplicitEdgesAt mem3 workHeap W := by
        intro j hj
        simp only [List.length_map, hWlen] at hj
        simp only [List.getElem_map]
        cases j with
        | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, W, List.getElem_cons_zero]
          exact ⟨(hfr3 workHeap (Or.inl (by omega))).trans hm2_0,
            (hfr3 (workHeap + 1) (Or.inl (by omega))).trans hm2_1⟩
        | succ m =>
          have hmLt : m < (walkRev embP).length := by simp [walkRev]; omega
          have h0 := hRev3.read hmLt
          simp only [W, List.getElem_cons_succ]
          rw [show workHeap + 2 * (m + 1) = workHeap + 2 + 2 * m by omega,
            show workHeap + 2 + 2 * m + 1 = workHeap + 2 + 2 * m + 1 from rfl]
          exact h0
      -- Store `[edgesBase, 0, pathsBase, 0]` at `descBase + 2 .. descBase + 5`
      refine runs_seq_store_flat (x := descBase + 2) (v := edgesBase)
        (by simp [Expr.eval, BinOp.eval, hr2, show 2 < 2 ^ w by omega, show descBase + 2 < 2 ^ w by omega])
        (by eval_expr) ?_
      refine runs_seq_store_flat (x := descBase + 3) (v := 0)
        (by simp [Expr.eval, BinOp.eval, hr2, show 3 < 2 ^ w by omega, show descBase + 3 < 2 ^ w by omega])
        (by eval_expr) ?_
      refine runs_seq_store_flat (x := descBase + 4) (v := pathsBase)
        (by simp [Expr.eval, BinOp.eval, hr2, show 4 < 2 ^ w by omega, show descBase + 4 < 2 ^ w by omega])
        (by eval_expr) ?_
      refine runs_seq_store_flat (x := descBase + 5) (v := 0)
        (by simp [Expr.eval, BinOp.eval, hr2, show 5 < 2 ^ w by omega, show descBase + 5 < 2 ^ w by omega])
        (by eval_expr) ?_
      set mem4 := Function.update (Function.update (Function.update (Function.update mem3
        (descBase + 2) edgesBase) (descBase + 3) 0) (descBase + 4) pathsBase) (descBase + 5) 0
      have hm4_out (a : ℕ) (h2 : a ≠ descBase + 2) (h3 : a ≠ descBase + 3)
          (h4 : a ≠ descBase + 4) (h5 : a ≠ descBase + 5) : mem4 a = mem3 a := by
        change Function.update (Function.update (Function.update (Function.update mem3 _ _) _ _) _ _) _ _ a = _
        rw [Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2]
      have hm4_lt (a : ℕ) (ha : a < descBase) : mem4 a = mem a :=
        (hm4_out a (by omega) (by omega) (by omega) (by omega)).trans
          ((hfr3 a (Or.inl (by omega))).trans (hm2_out a (by omega) (by omega)))
      have hm4_d2 : mem4 (descBase + 2) = edgesBase := by
        change Function.update (Function.update (Function.update (Function.update mem3 _ _) _ _) _ _) _ _ _ = _
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
      have hm4_d3 : mem4 (descBase + 3) = 0 := by
        change Function.update (Function.update (Function.update (Function.update mem3 _ _) _ _) _ _) _ _ _ = _
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      have hm4_d4 : mem4 (descBase + 4) = pathsBase := by
        change Function.update (Function.update (Function.update (Function.update mem3 _ _) _ _) _ _) _ _ _ = _
        rw [Function.update_of_ne (by omega), Function.update_self]
      have hm4_d5 : mem4 (descBase + 5) = 0 := by
        change Function.update _ _ _ _ = _; exact Function.update_self ..
      clear_value mem4
      have hWAt4 : ExplicitEdgesAt mem4 workHeap W :=
        hWAt3.congr fun x hx1 _ => hm4_out x (by omega) (by omega) (by omega) (by omega)
      -- Call `splitSteps`
      refine runs_seq_call_flat hSplitSteps
        (vs := [slots, intToExt, tailSlot, headSlot, workHeap, K, (if flip then 1 else 0),
          edgesBase, pathsBase, descBase, 0])
        (by simp [evalArgs, Expr.eval, hr2, hr14, hr17, hr21, hr22, hr23])
        (by wram_words) ?_ ?_
      · refine ⟨slots, intToExt, tailSlot, headSlot, workHeap, edgesBase, pathsBase, descBase, 0,
          by rw [hWlen], hw16, Nat.zero_le _, hWAt4, fun x hx => ?_, fun x hx => ?_,
          by omega, by omega, by omega, by omega, by omega, fun a ha x hx => ?_,
          by simpa [rawEdgesOfWalk, orientWalkSteps] using hm4_d3, fun j hj => by simp [rawEdgesOfWalk, orientWalkSteps] at hj,
          by simpa [orientWalkSteps] using hm4_d5, fun j hj => by simp [orientWalkSteps] at hj⟩
        · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hWE_ends x hx
          rw [hm4_lt _ a3, hm4_lt _ a4, hm4_lt _ a5, hm4_lt _ a6]
          exact ⟨a1, a2, by omega, by omega, by omega, by omega, a7, a8⟩
        · obtain ⟨b1, b2, b3, b4⟩ := hWE_slot x hx
          rw [hm4_lt _ b3]; exact ⟨b1, b2, by omega, b4⟩
        · obtain ⟨_, _, a3, a4, a5, a6, _, _⟩ := hWE_ends x hx
          obtain ⟨_, _, b3, _⟩ := hWE_slot x hx
          rw [hm4_lt _ a3, hm4_lt _ a4]
          unfold splitWriteRegion at ha
          exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      · intro _ mem5 pos5 hp5
        obtain ⟨hd3_5, hEd5, hd5_5, hp0_5, hfr5⟩ := hp5
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hd3_5 hEd5 hd5_5 hp0_5 hfr5
        have hm5_lt (a : ℕ) (ha : a < descBase) : mem5 a = mem a :=
          (hfr5 a (by unfold splitWriteRegion; omega)).trans (hm4_lt a ha)
        have hWAt5 : ExplicitEdgesAt mem5 workHeap W :=
          hWAt4.congr fun x hx1 hx2 => hfr5 x (by unfold splitWriteRegion; omega)
        -- Call `emitStitches`
        refine runs_seq_call_flat hEmitStitches
          (vs := [intToExt, tailSlot, headSlot, workHeap, K, (if flip then 1 else 0),
            pathsBase, descBase, 0])
          (by simp [evalArgs, Expr.eval, hr2, hr14, hr21, hr22, hr23])
          (by wram_words) ?_ ?_
        · refine ⟨intToExt, tailSlot, headSlot, workHeap, pathsBase, descBase, 0,
            by rw [hWlen], hw16, by omega, Nat.zero_le _, hWAt5, fun x hx => ?_,
            fun x hx => ⟨(hWE_slot x hx).1, (hWE_slot x hx).2.2.2⟩,
            by omega, by omega, by omega, by omega, fun a ha x hx => ?_,
            by simpa using hd5_5, by simpa using hp0_5⟩
          · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hWE_ends x hx
            rw [hm5_lt _ a3, hm5_lt _ a4, hm5_lt _ a5, hm5_lt _ a6]
            exact ⟨a1, a2, by omega, by omega, by omega, by omega, a7, a8⟩
          · obtain ⟨_, _, a3, a4, a5, a6, _, _⟩ := hWE_ends x hx
            rw [hm5_lt _ a3, hm5_lt _ a4]
            unfold stitchWriteRegion at ha
            exact ⟨by omega, by omega, by omega, by omega⟩
        · intro _ mem6 pos6 hp6
          obtain ⟨hd5_6, hPt6, hfr6⟩ := hp6
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hd5_6 hPt6 hfr6
          have hfr56 (a : ℕ) (hno : a < pathsBase ∨ work1 ≤ a) (hne5 : a ≠ descBase + 5) :
              mem6 a = mem5 a :=
            hfr6 a (by unfold stitchWriteRegion; omega)
          have hEdLeK : (rawEdgesOfWalk F W flip).length ≤ K := by
            unfold rawEdgesOfWalk
            refine (List.length_filter_le _ _).trans ?_
            unfold orientWalkSteps; cases flip <;> simp [hWlen]
          refine WordRAM.runs_ret_le (v := work1) (by eval_expr) ?_ ?_
          · dsimp only
            refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, hPt6, ?_⟩
            · exact (hfr56 _ (Or.inl (by omega)) (by omega)).trans
                ((hfr5 _ (by unfold splitWriteRegion; omega)).trans hm4_d2)
            · exact (hfr56 _ (Or.inl (by omega)) (by omega)).trans hd3_5
            · exact (hfr56 _ (Or.inl (by omega)) (by omega)).trans
                ((hfr5 _ (by unfold splitWriteRegion; omega)).trans hm4_d4)
            · rw [hd5_6, hRawPathsLen, hWlen]
            · exact hEd5.congr fun x hx1 hx2 =>
                hfr56 x (Or.inl (by dsimp only [edgesBase, pathsBase] at hx1 hx2 ⊢; omega)) (by omega)
            · intro a ha
              have h65 : mem6 a = mem5 a := hfr6 a (by unfold stitchWriteRegion; omega)
              have h54 : mem5 a = mem4 a := hfr5 a (by unfold splitWriteRegion; omega)
              have h43 : mem4 a = mem3 a := hm4_out a (by omega) (by omega) (by omega) (by omega)
              have h32 : mem3 a = mem2 a := hfr3 a (by omega)
              have h21 : mem2 a = mem a := hm2_out a (by omega) (by omega)
              exact h65.trans (h54.trans (h43.trans (h32.trans h21)))
          · simp only [selectFillRevContract, selectSplitStepsContract, selectEmitStitchesContract,
              List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, hWlen, Expr.size, argsSize]
            omega
  obtain ⟨o, st', c, hrun', ⟨rfl, hd2, hd3, hd4, hd5, hEd, hPt, hfr⟩, hc⟩ := hrun
  exact ⟨st', c, hrun', hd2, hd3, hd4, hd5, hEd, hPt, hfr, hc⟩

end MinCostFlow.MinRatio
