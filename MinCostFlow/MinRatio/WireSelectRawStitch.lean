module

public import MinCostFlow.MinRatio.WireSelectRawLoops
import WordRAM.Tactic

/-!
# Verification of `selectEmitStitchesBody`

Verifies the tail-recursive stitching-pair loop `selectEmitStitchesBody` (`WireSelectQuery.lean`):
appends the `|W|` stitching endpoint pairs of `(cycleSegments G0 W).2` (swapped when `flip = true`)
into `pathsBase` in `≤ 130 * |W| + 15` steps, producing exact `rawPathsOfWalk`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain DynSpanner.Program

/-- Write footprint of `selectEmitStitchesBody`. -/
def stitchWriteRegion (pathsBase descBase p0Len t K a : ℕ) : Prop :=
  (pathsBase + 2 * (p0Len + t) ≤ a ∧ a < pathsBase + 2 * (p0Len + K)) ∨ a = descBase + 5

/-- Contract for `selectEmitStitchesBody`
(`[intToExt, tailSlot, headSlot, stepsBase, K, flip, pathsBase, descBase, t]`). -/
def selectEmitStitchesContract (w : ℕ) (G0 : MGraph) (W : List (ℕ × Bool)) (flip : Bool)
    (p0 : List (ℕ × ℕ)) : Contract where
  pre args mem :=
    ∃ intToExt tailSlot headSlot stepsBase pathsBase descBase t,
      args = [intToExt, tailSlot, headSlot, stepsBase, W.length,
        (if flip then 1 else 0), pathsBase, descBase, t] ∧
      16 < 2 ^ w ∧ 0 < W.length ∧ t ≤ W.length ∧
      ExplicitEdgesAt mem stepsBase W ∧
      (∀ x ∈ W,
        mem (intToExt + mem (tailSlot + x.1)) = G0.tail x.1 ∧
        mem (intToExt + mem (headSlot + x.1)) = G0.head x.1 ∧
        tailSlot + x.1 < 2 ^ w ∧ headSlot + x.1 < 2 ^ w ∧
        intToExt + mem (tailSlot + x.1) < 2 ^ w ∧ intToExt + mem (headSlot + x.1) < 2 ^ w ∧
        G0.tail x.1 < 2 ^ w ∧ G0.head x.1 < 2 ^ w) ∧
      (∀ x ∈ W, x.1 ∈ G0.E ∧ x.1 < 2 ^ w) ∧
      descBase + 5 < stepsBase ∧
      descBase + 5 < pathsBase ∧
      stepsBase + 2 * W.length ≤ pathsBase ∧
      pathsBase + 2 * (p0.length + W.length) < 2 ^ w ∧
      (∀ a, stitchWriteRegion pathsBase descBase p0.length 0 W.length a →
        ∀ x ∈ W, a ≠ tailSlot + x.1 ∧ a ≠ headSlot + x.1 ∧
          a ≠ intToExt + mem (tailSlot + x.1) ∧ a ≠ intToExt + mem (headSlot + x.1)) ∧
      let stAll := if flip then (cycleSegments G0 W).2.map Prod.swap else (cycleSegments G0 W).2
      mem (descBase + 5) = p0.length + t ∧
      PathEndpointsAt mem pathsBase (p0 ++ stAll.take t)
  post args mem _ mem' :=
    let pathsBase := args.getD 6 0
    let descBase := args.getD 7 0
    let t := args.getD 8 0
    let stAll := if flip then (cycleSegments G0 W).2.map Prod.swap else (cycleSegments G0 W).2
    mem' (descBase + 5) = p0.length + W.length ∧
    PathEndpointsAt mem' pathsBase (p0 ++ stAll) ∧
    ∀ a, ¬ stitchWriteRegion pathsBase descBase p0.length t W.length a → mem' a = mem a
  cost args _ := (W.length - args.getD 8 0) * 140 + 15

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain DynSpanner.Program

/-! ## 5. Verification of `selectEmitStitchesBody` -/

theorem selectEmitStitches_meetsContract {w self : ℕ} {G0 : MGraph} {W : List (ℕ × Bool)}
    {flip : Bool} {p0 : List (ℕ × ℕ)} {p : Program}
    (hp : p.procs[self]? = some (selectEmitStitchesBody self)) :
    MeetsContract w p self (selectEmitStitchesContract w G0 W flip p0) := by
  apply meetsContract_of_rec (fun args _ => W.length - args.getD 8 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨intToExt, tailSlot, headSlot, stepsBase, pathsBase, descBase, t,
    rfl, hw16, hWpos, htLe, hWAt, hEnds, hWinfo, hdbSt, hdbPt, hstPt, hptW, hDisj,
    hpLen, hpPref⟩ := hpre
  change W.length - t = rem at hremEq
  subst hremEq
  have hi2eW : intToExt < 2 ^ w := hwords intToExt (by simp)
  have htsW : tailSlot < 2 ^ w := hwords tailSlot (by simp)
  have hhsW : headSlot < 2 ^ w := hwords headSlot (by simp)
  have hsbW : stepsBase < 2 ^ w := hwords stepsBase (by simp)
  have hKW : W.length < 2 ^ w := hwords W.length (by simp)
  have hflW : (if flip then 1 else 0) < 2 ^ w := by split <;> omega
  have hptBaseW : pathsBase < 2 ^ w := hwords pathsBase (by simp)
  have hdbW : descBase < 2 ^ w := hwords descBase (by simp)
  have htW : t < 2 ^ w := hwords t (by simp)
  set stAll := if flip then (cycleSegments G0 W).2.map Prod.swap else (cycleSegments G0 W).2
  have hstLen : stAll.length = W.length := by
    dsimp only [stAll]; split <;> simp [(cycleSegments_eq G0 W).2]
  apply runs_start_le
  dsimp only [startState]
  unfold selectEmitStitchesBody
  by_cases hlt : t < W.length
  · set nxt := (t + 1) % W.length
    have hnxtLt : nxt < W.length := Nat.mod_lt _ hWpos
    set f0 := W[t].1
    set d0 := W[t].2
    set f1 := W[nxt].1
    set d1 := W[nxt].2
    obtain ⟨hf0G0, hf0W⟩ := hWinfo W[t] (List.getElem_mem hlt)
    obtain ⟨hf1G0, hf1W⟩ := hWinfo W[nxt] (List.getElem_mem hnxtLt)
    obtain ⟨hT0, hH0, hts0, hhs0, hi2eT0, hi2eH0, hT0W, hH0W⟩ := hEnds W[t] (List.getElem_mem hlt)
    obtain ⟨hT1, hH1, hts1, hhs1, hi2eT1, hi2eH1, hT1W, hH1W⟩ := hEnds W[nxt] (List.getElem_mem hnxtLt)
    obtain ⟨hRdF0, hRdD0⟩ := hWAt.read hlt
    obtain ⟨hRdF1, hRdD1⟩ := hWAt.read hnxtLt
    have hdstW : G0.dst W[t] < 2 ^ w := by cases hd : d0 <;> simp [MGraph.dst, d0, hd, hT0W, hH0W]
    have hsrcW : G0.src W[nxt] < 2 ^ w := by cases hd : d1 <;> simp [MGraph.src, d1, hd, hT1W, hH1W]
    have hstElem : stAll[t]'(by omega) =
        if flip then (G0.src W[nxt], G0.dst W[t]) else (G0.dst W[t], G0.src W[nxt]) := by
      dsimp only [stAll]
      cases flip
      · simpa [nxt] using cycleSegments_snd_getElem G0 W hlt
      · simp [cycleSegments_snd_getElem G0 W hlt, nxt]
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, show 1 < 2 ^ w by omega])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assign_flat (v := f0)
      (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 2 * t < 2 ^ w by omega,
            show stepsBase + 2 * t < 2 ^ w by omega, hRdF0, f0]) ?_
    refine runs_seq_assign_flat (v := if d0 then 1 else 0)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            show 2 * t < 2 ^ w by omega, show stepsBase + 2 * t < 2 ^ w by omega,
            show stepsBase + 2 * t + 1 < 2 ^ w by omega, hRdD0, d0]) ?_
    refine runs_seq_assign_flat (v := nxt)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show t + 1 < 2 ^ w by omega,
            show nxt < 2 ^ w by omega, nxt]) ?_
    refine runs_seq_assign_flat (v := f1)
      (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 2 * nxt < 2 ^ w by omega,
            show stepsBase + 2 * nxt < 2 ^ w by omega, hRdF1, f1]) ?_
    refine runs_seq_assign_flat (v := if d1 then 1 else 0)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            show 2 * nxt < 2 ^ w by omega, show stepsBase + 2 * nxt < 2 ^ w by omega,
            show stepsBase + 2 * nxt + 1 < 2 ^ w by omega, hRdD1, d1]) ?_
    -- Continuation after evaluating `dst(W[t])` into reg 14 and `src(W[nxt])` into reg 15
    have hAfterEnds : ∀ (regs1 : ℕ → ℕ) (k0 : ℕ),
        regs1 0 = intToExt → regs1 1 = tailSlot → regs1 2 = headSlot → regs1 3 = stepsBase →
        regs1 4 = W.length → regs1 5 = (if flip then 1 else 0) → regs1 6 = pathsBase →
        regs1 7 = descBase → regs1 8 = t →
        regs1 14 = G0.dst W[t] → regs1 15 = G0.src W[nxt] →
        k0 + (W.length - (t + 1)) * 140 + 70 ≤ (W.length - t) * 140 + 15 →
        ∃ o st' c, Runs w p ω
          (.assign 16 (.load (.bin .add (.reg 7) (.const 5))) ;;
           .cond (.reg 5)
             (.store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.reg 15) ;;
              .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 14))
             (.store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.reg 14) ;;
              .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 15)) ;;
           .store (.bin .add (.reg 7) (.const 5)) (.bin .add (.reg 16) (.const 1)) ;;
           .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
             .bin .add (.reg 8) (.const 1)] ;;
           .ret (.const 0))
          ⟨mem, regs1, pos⟩ o st' c ∧
          (selectEmitStitchesContract w G0 W flip p0).post
            [intToExt, tailSlot, headSlot, stepsBase, W.length,
              (if flip then 1 else 0), pathsBase, descBase, t] mem o.value st'.mem ∧
          k0 + c ≤ (selectEmitStitchesContract w G0 W flip p0).cost
            [intToExt, tailSlot, headSlot, stepsBase, W.length,
              (if flip then 1 else 0), pathsBase, descBase, t] mem := by
      intro regs1 k0 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr14 hr15 hk0
      refine runs_seq_assign_flat (v := p0.length + t)
        (by simp [Expr.eval, BinOp.eval, hr7, show 5 < 2 ^ w by omega, show descBase + 5 < 2 ^ w by omega, hpLen]) ?_
      have hAfterPair : ∀ (u v : ℕ) (huv : (u, v) = stAll[t]'(by omega))
          (mem1 : ℕ → ℕ) (regs2 : ℕ → ℕ) (k1 : ℕ),
          regs2 0 = intToExt → regs2 1 = tailSlot → regs2 2 = headSlot → regs2 3 = stepsBase →
          regs2 4 = W.length → regs2 5 = (if flip then 1 else 0) → regs2 6 = pathsBase →
          regs2 7 = descBase → regs2 8 = t → regs2 16 = p0.length + t →
          mem1 = Function.update (Function.update mem (pathsBase + 2 * (p0.length + t)) u)
            (pathsBase + 2 * (p0.length + t) + 1) v →
          k1 + (W.length - (t + 1)) * 140 + 42 ≤ (W.length - t) * 140 + 15 →
          ∃ o st' c, Runs w p ω
            (.store (.bin .add (.reg 7) (.const 5)) (.bin .add (.reg 16) (.const 1)) ;;
             .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
               .bin .add (.reg 8) (.const 1)] ;;
             .ret (.const 0))
            ⟨mem1, regs2, pos⟩ o st' c ∧
            (selectEmitStitchesContract w G0 W flip p0).post
              [intToExt, tailSlot, headSlot, stepsBase, W.length,
                (if flip then 1 else 0), pathsBase, descBase, t] mem o.value st'.mem ∧
            k1 + c ≤ (selectEmitStitchesContract w G0 W flip p0).cost
              [intToExt, tailSlot, headSlot, stepsBase, W.length,
                (if flip then 1 else 0), pathsBase, descBase, t] mem := by
        intro u v huv mem1 regs2 k1 r0 r1 r2 r3 r4 r5 r6 r7 r8 r16 hmem1 hk1
        refine runs_seq_store_flat (x := descBase + 5) (v := p0.length + t + 1)
          (by simp [Expr.eval, BinOp.eval, r7, show 5 < 2 ^ w by omega, show descBase + 5 < 2 ^ w by omega])
          (by simp [Expr.eval, BinOp.eval, r16, show 1 < 2 ^ w by omega, show p0.length + t + 1 < 2 ^ w by omega]) ?_
        set mem2 := Function.update mem1 (descBase + 5) (p0.length + t + 1)
        have hfr2 : ∀ a, ¬ stitchWriteRegion pathsBase descBase p0.length t W.length a → mem2 a = mem a := by
          intro a ha
          have hne5 : a ≠ descBase + 5 := fun h => ha (Or.inr h)
          have hneP0 : a ≠ pathsBase + 2 * (p0.length + t) := fun h => ha (Or.inl ⟨by omega, by omega⟩)
          have hneP1 : a ≠ pathsBase + 2 * (p0.length + t) + 1 := fun h => ha (Or.inl ⟨by omega, by omega⟩)
          change Function.update mem1 _ _ a = mem a
          rw [Function.update_of_ne hne5, hmem1, Function.update_of_ne hneP1, Function.update_of_ne hneP0]
        have hWAt2 : ExplicitEdgesAt mem2 stepsBase W :=
          hWAt.congr fun x hx1 hx2 => hfr2 x (by unfold stitchWriteRegion; omega)
        have hpPref2 : PathEndpointsAt mem2 pathsBase (p0 ++ stAll.take (t + 1)) := by
          intro j hj
          rw [List.length_append, List.length_take, hstLen] at hj
          have hjLt : j < p0.length + (t + 1) := by omega
          by_cases hjEq : j = p0.length + t
          · subst j
            have hge : p0.length ≤ p0.length + t := Nat.le_add_right _ _
            rw [List.getElem_append_right hge, List.getElem_take]
            simp only [Nat.add_sub_cancel_left]
            change Function.update mem1 _ _ _ = _ ∧ Function.update mem1 _ _ _ = _
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmem1,
              Function.update_of_ne (by omega), Function.update_self, Function.update_self]
            exact ⟨congrArg Prod.fst huv, congrArg Prod.snd huv⟩
          · have hj0 : j < (p0 ++ stAll.take t).length := by
              rw [List.length_append, List.length_take, hstLen]; omega
            have h0 := hpPref j hj0
            have hsame : (p0 ++ stAll.take (t + 1))[j]'(by rw [List.length_append, List.length_take, hstLen]; omega) =
                (p0 ++ stAll.take t)[j]'hj0 := by
              by_cases hjp : j < p0.length
              · simp [List.getElem_append_left hjp]
              · have hge : p0.length ≤ j := by omega
                simp [List.getElem_append_right hge]
            rw [hsame]
            exact ⟨(hfr2 _ (by unfold stitchWriteRegion; omega)).trans h0.1,
              (hfr2 _ (by unfold stitchWriteRegion; omega)).trans h0.2⟩
        have hm2_read (x : ℕ × Bool) (hx : x ∈ W) :
            mem2 (tailSlot + x.1) = mem (tailSlot + x.1) ∧
            mem2 (headSlot + x.1) = mem (headSlot + x.1) ∧
            mem2 (intToExt + mem (tailSlot + x.1)) = mem (intToExt + mem (tailSlot + x.1)) ∧
            mem2 (intToExt + mem (headSlot + x.1)) = mem (intToExt + mem (headSlot + x.1)) := by
          have hsub : ∀ a, stitchWriteRegion pathsBase descBase p0.length t W.length a →
              stitchWriteRegion pathsBase descBase p0.length 0 W.length a := fun a ha => by
            unfold stitchWriteRegion at ha ⊢; omega
          exact ⟨hfr2 _ fun hr => (hDisj _ (hsub _ hr) x hx).1 rfl,
            hfr2 _ fun hr => (hDisj _ (hsub _ hr) x hx).2.1 rfl,
            hfr2 _ fun hr => (hDisj _ (hsub _ hr) x hx).2.2.1 rfl,
            hfr2 _ fun hr => (hDisj _ (hsub _ hr) x hx).2.2.2 rfl⟩
        refine runs_seq_call_flat ih
          (vs := [intToExt, tailSlot, headSlot, stepsBase, W.length,
            (if flip then 1 else 0), pathsBase, descBase, t + 1])
          (by simp [evalArgs, Expr.eval, BinOp.eval, r0, r1, r2, r3, r4, r5, r6, r7, r8,
                show 1 < 2 ^ w by omega, show t + 1 < 2 ^ w by omega])
          (by wram_words) ?_ ?_
        · refine ⟨⟨intToExt, tailSlot, headSlot, stepsBase, pathsBase, descBase, t + 1, rfl,
            hw16, hWpos, by omega, hWAt2, fun x hx => ?_,
            hWinfo, hdbSt, hdbPt, hstPt, hptW, fun a ha x hx => ?_,
            by change Function.update mem1 _ _ _ = _; rw [Function.update_self]; omega, hpPref2⟩,
            by change W.length - (t + 1) < W.length - t; omega⟩
          · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hEnds x hx
            have hr := hm2_read x hx
            rw [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
            exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
          · obtain ⟨b1, b2, b3, b4⟩ := hDisj a ha x hx
            rw [(hm2_read x hx).1, (hm2_read x hx).2.1]
            exact ⟨b1, b2, b3, b4⟩
        · intro ret mem3 pos3 hp3
          obtain ⟨hpL3, hpA3, hfr3⟩ := hp3
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hpL3 hpA3 hfr3
          refine WordRAM.runs_ret_le (v := 0) (by eval_expr) ?_ ?_
          · dsimp only [selectEmitStitchesContract]
            simp only [List.getD_cons_zero, List.getD_cons_succ]
            exact ⟨hpL3, hpA3, fun a ha => (hfr3 a (fun h => ha (by unfold stitchWriteRegion at h ⊢; omega))).trans (hfr2 a ha)⟩
          · simp only [Contract.below, selectEmitStitchesContract, List.getD_cons_zero,
              List.getD_cons_succ, Expr.size, argsSize]; omega
      by_cases hfl : flip = true
      · refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval, hr5, hfl]) ?_ (fun h => absurd h (by decide))
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_store_flat (x := pathsBase + 2 * (p0.length + t)) (v := G0.src W[nxt])
          (by simp [Expr.eval, BinOp.eval, hr6, show 2 < 2 ^ w by omega,
                show 2 * (p0.length + t) < 2 ^ w by omega, show pathsBase + 2 * (p0.length + t) < 2 ^ w by omega])
          (by simp [Expr.eval, hr15]) ?_
        refine runs_seq_store_flat (x := pathsBase + 2 * (p0.length + t) + 1) (v := G0.dst W[t])
          (by simp [Expr.eval, BinOp.eval, hr6, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
                show 2 * (p0.length + t) < 2 ^ w by omega, show pathsBase + 2 * (p0.length + t) < 2 ^ w by omega,
                show pathsBase + 2 * (p0.length + t) + 1 < 2 ^ w by omega])
          (by simp [Expr.eval, hr14]) ?_
        apply hAfterPair (G0.src W[nxt]) (G0.dst W[t]) (by simpa [hfl] using hstElem.symm)
        all_goals first | rfl | (simp [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hfl]; done) | (simp [Expr.size]; omega)
      · refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval, hr5, hfl]) (fun h => absurd rfl h) ?_
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_store_flat (x := pathsBase + 2 * (p0.length + t)) (v := G0.dst W[t])
          (by simp [Expr.eval, BinOp.eval, hr6, show 2 < 2 ^ w by omega,
                show 2 * (p0.length + t) < 2 ^ w by omega, show pathsBase + 2 * (p0.length + t) < 2 ^ w by omega])
          (by simp [Expr.eval, hr14]) ?_
        refine runs_seq_store_flat (x := pathsBase + 2 * (p0.length + t) + 1) (v := G0.src W[nxt])
          (by simp [Expr.eval, BinOp.eval, hr6, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
                show 2 * (p0.length + t) < 2 ^ w by omega, show pathsBase + 2 * (p0.length + t) < 2 ^ w by omega,
                show pathsBase + 2 * (p0.length + t) + 1 < 2 ^ w by omega])
          (by simp [Expr.eval, hr15]) ?_
        apply hAfterPair (G0.dst W[t]) (G0.src W[nxt]) (by simpa [hfl] using hstElem.symm)
        all_goals first | rfl | (simp [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hfl]; done) | (simp [Expr.size]; omega)
    -- Evaluate `dst(W[t])` and `src(W[nxt])` by cases on `(d0, d1)`
    have hAfterD0 : ∀ (regs0 : ℕ → ℕ) (k0 : ℕ),
        regs0 0 = intToExt → regs0 1 = tailSlot → regs0 2 = headSlot → regs0 3 = stepsBase →
        regs0 4 = W.length → regs0 5 = (if flip then 1 else 0) → regs0 6 = pathsBase →
        regs0 7 = descBase → regs0 8 = t → regs0 12 = f1 → regs0 13 = (if d1 then 1 else 0) →
        regs0 14 = G0.dst W[t] →
        k0 + (W.length - (t + 1)) * 140 + 83 ≤ (W.length - t) * 140 + 15 →
        ∃ o st' c, Runs w p ω
          (.cond (.reg 13)
             (.assign 15 (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 1) (.reg 12))))))
             (.assign 15 (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 2) (.reg 12)))))) ;;
           .assign 16 (.load (.bin .add (.reg 7) (.const 5))) ;;
           .cond (.reg 5)
             (.store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.reg 15) ;;
              .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 14))
             (.store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.reg 14) ;;
              .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 15)) ;;
           .store (.bin .add (.reg 7) (.const 5)) (.bin .add (.reg 16) (.const 1)) ;;
           .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
             .bin .add (.reg 8) (.const 1)] ;;
           .ret (.const 0))
          ⟨mem, regs0, pos⟩ o st' c ∧
          (selectEmitStitchesContract w G0 W flip p0).post
            [intToExt, tailSlot, headSlot, stepsBase, W.length,
              (if flip then 1 else 0), pathsBase, descBase, t] mem o.value st'.mem ∧
          k0 + c ≤ (selectEmitStitchesContract w G0 W flip p0).cost
            [intToExt, tailSlot, headSlot, stepsBase, W.length,
              (if flip then 1 else 0), pathsBase, descBase, t] mem := by
      intro regs0 k0 r0 r1 r2 r3 r4 r5 r6 r7 r8 r12 r13 r14 hk0
      cases hd1 : d1
      · refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval, r13, hd1]) (fun h => absurd rfl h) ?_
        intro _
        refine runs_seq_assign_flat (v := G0.head f1)
          (by simp [Expr.eval, BinOp.eval, r0, r2, r12, f1, hhs1, hi2eH1, hH1]) ?_
        apply hAfterEnds
        all_goals first | (simp [r0, r1, r2, r3, r4, r5, r6, r7, r8, r14, MGraph.src, d1, hd1, f1]; done) | (simp [Expr.size]; omega)
      · refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval, r13, hd1]) ?_ (fun h => absurd h (by decide))
        intro _
        refine runs_seq_assign_flat (v := G0.tail f1)
          (by simp [Expr.eval, BinOp.eval, r0, r1, r12, f1, hts1, hi2eT1, hT1]) ?_
        apply hAfterEnds
        all_goals first | (simp [r0, r1, r2, r3, r4, r5, r6, r7, r8, r14, MGraph.src, d1, hd1, f1]; done) | (simp [Expr.size]; omega)
    cases hd0 : d0
    · refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval]) (fun h => absurd rfl h) ?_
      intro _
      refine runs_seq_assign_flat (v := G0.tail f0)
        (by simp [Expr.eval, BinOp.eval, f0, hts0, hi2eT0, hT0]) ?_
      apply hAfterD0
      all_goals first | (simp [MGraph.dst, d0, hd0, f0]; done) | (simp [Expr.size]; omega)
    · refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval]) ?_ (fun h => absurd h (by decide))
      intro _
      refine runs_seq_assign_flat (v := G0.head f0)
        (by simp [Expr.eval, BinOp.eval, f0, hhs0, hi2eH0, hH0]) ?_
      apply hAfterD0
      all_goals first | (simp [MGraph.dst, d0, hd0, f0]; done) | (simp [Expr.size]; omega)
  · have hteq : t = W.length := by omega
    subst hteq
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine WordRAM.runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · dsimp only [selectEmitStitchesContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [List.take_of_length_le (by omega : stAll.length ≤ W.length)] at hpPref
      exact ⟨hpLen, hpPref, fun _ _ => trivial⟩
    · simp only [selectEmitStitchesContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size]; omega

end MinCostFlow.MinRatio
