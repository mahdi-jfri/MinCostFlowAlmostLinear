module

public import MinCostFlow.MinRatio.DetectOffTreeDrainBase
import WordRAM.Tactic

/-!
# Off-tree edge record install and `offReadyList` push for `Update`

When `Update` installs a newly allocated `PathEdgeAt` block at `newRec` for an internal
edge `ei` that is currently off-tree (`slots[ei] = 0`), `offTreePushBody` stores
`edgeRecords[ei] := newRec`, checks `¬ isNegative (newRec + 2 + 3 * L) L`, and when
`0 ≤ detector` and `inOffReady[ei] = 0`, appends `ei` to `offReadyList[offReadyCount]`,
sets `inOffReady[ei] := 1`, and increments `offReadyCount` at `root + 11`.

Proves `offTreePushBody_runs`, maintaining `OffReadyInv` and bounding raw cost by `95`
(amortized cost `≤ detectOffTreeDrainUnit L + 95` including the `+drainUnit` potential
increase when a new entry is pushed).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Fixed deterministic procedure taking `[root, ei, newRec, L]`.
Stores `edgeRecords[ei] := newRec`, tests whether the detector at `newRec + 2 + 3 * L`
is nonnegative, and pushes `ei` onto `offReadyList` if not already marked in `inOffReady`. -/
@[expose] def offTreePushBody (isNeg : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .store (.bin .add (.reg 4) (.reg 1)) (.reg 2) ;;
  .assign 5 (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 3) (.reg 3))) ;;
  .call 6 isNeg [.reg 5, .reg 3] ;;
  .cond (.reg 6)
    .nop
    (.assign 7 (.load (.bin .add (.reg 0) (.const 13))) ;;
     .cond (.load (.bin .add (.reg 7) (.reg 1)))
       .nop
       (.assign 8 (.load (.bin .add (.reg 0) (.const 11))) ;;
        .assign 9 (.load (.bin .add (.reg 0) (.const 12))) ;;
        .store (.bin .add (.reg 7) (.reg 1)) (.const 1) ;;
        .store (.bin .add (.reg 9) (.reg 8)) (.reg 1) ;;
        .store (.bin .add (.reg 0) (.const 11)) (.bin .add (.reg 8) (.const 1)))) ;;
  .ret (.const 0)

theorem offTreePushBody_noRand (isNeg : ℕ) : (offTreePushBody isNeg).NoRand := by
  simp [offTreePushBody, Stmt.NoRand]

/-- If `OffReadyInv` holds and `ei < intCap` has `mem (inOffReady + ei) = 0`, then
`offReadyCount < intCap`, so appending `ei` never overflows `offReadyList`. -/
theorem offReadyCount_lt_of_zero {mem : ℕ → ℕ} {cnt list inOff intCap ei : ℕ}
    (hoff : OffReadyInv mem cnt list inOff intCap)
    (hei : ei < intCap) (hzero : mem (inOff + ei) = 0) :
    cnt < intCap := by
  by_contra hge
  have heq : cnt = intCap := by have := hoff.1; omega
  let f : Fin cnt → Fin intCap := fun j => ⟨mem (list + j.val), (hoff.2.1 j.val j.isLt).1⟩
  have hinj : Function.Injective f := fun j₁ j₂ h => by
    ext
    by_contra hne
    exact hoff.2.2.1 j₁.val j₁.isLt j₂.val j₂.isLt hne (congrArg Fin.val h)
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp [heq]⟩).2
  obtain ⟨j, hj⟩ := hsurj ⟨ei, hei⟩
  have h1 := (hoff.2.1 j.val j.isLt).2
  have hval : mem (list + j.val) = ei := congrArg Fin.val hj
  rw [hval, hzero] at h1
  omega

/-- Running `offTreePushBody` updates `edgeRecords[ei] := newRec`, preserves `OffReadyInv`
(increasing `offReadyCount` by at most `1`), ensures `0 ≤ val.detector → out.mem (inOffReady + ei) = 1`,
and leaves all memory outside `edgeRecords[ei]`, `inOffReady[ei]`, `offReadyList[offReadyCount]`,
and `root + 11` unchanged. Disjointness of the five regions is witnessed by a tag function `tag`. -/
theorem offTreePushBody_runs {w isNeg root ei newRec L pos : ℕ}
    {offReadyCount offReadyList inOffReady edgeRecords intCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {val : PathEdgeValue}
    (tag : ℕ → ℕ)
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hoff : OffReadyInv mem offReadyCount offReadyList inOffReady intCap)
    (hei : ei < intCap)
    (hdir10 : mem (root + 10) = edgeRecords)
    (hdir11 : mem (root + 11) = offReadyCount)
    (hdir12 : mem (root + 12) = offReadyList)
    (hdir13 : mem (root + 13) = inOffReady)
    (hvalAt : PathEdgeAt mem newRec 4 L (some val))
    (ht1 : ∀ j < 14, tag (root + j) = 1)
    (ht13 : tag (edgeRecords + ei) = 13)
    (ht14 : ∀ k < intCap, tag (offReadyList + k) = 14)
    (ht15 : ∀ k < intCap, tag (inOffReady + k) = 15)
    (ht18 : ∀ x < 2 + 4 * L, tag (newRec + x) = 18)
    (hw13 : 13 < 2 ^ w) (hroot13W : root + 13 < 2 ^ w)
    (herW : edgeRecords + ei < 2 ^ w) (hioW : inOffReady + ei < 2 ^ w)
    (holW : offReadyList + intCap ≤ 2 ^ w) (hcapW : intCap < 2 ^ w)
    (hrecEndW : newRec + (2 + 4 * L) < 2 ^ w) (hLW : L < 2 ^ w) :
    ∃ cost out cnt',
      Runs w p ω (offTreePushBody isNeg)
        (startState [root, ei, newRec, L] mem pos) (.returned 0) out cost ∧
      cost ≤ 95 ∧
      (cnt' = offReadyCount ∨ cnt' = offReadyCount + 1) ∧
      out.mem (root + 11) = cnt' ∧
      out.mem (edgeRecords + ei) = newRec ∧
      OffReadyInv out.mem cnt' offReadyList inOffReady intCap ∧
      (0 ≤ val.detector → out.mem (inOffReady + ei) = 1) ∧
      (∀ k < intCap, mem (inOffReady + k) = 1 → out.mem (inOffReady + k) = 1) ∧
      (∀ a, a ≠ edgeRecords + ei → a ≠ inOffReady + ei →
        (cnt' = offReadyCount + 1 → a ≠ offReadyList + offReadyCount) →
        a ≠ root + 11 → out.mem a = mem a) := by
  have hneOfTag {a b u v : ℕ} (ha : tag a = u) (hb : tag b = v) (huv : u ≠ v) : a ≠ b :=
    fun h => huv (ha.symm.trans (h ▸ hb))
  let s0 := startState [root, ei, newRec, L] mem pos
  let detPtr := newRec + 2 + 3 * L
  let s1 : State := { s0 with regs := Function.update s0.regs 4 edgeRecords }
  let s2 : State := { s1 with mem := Function.update s1.mem (edgeRecords + ei) newRec }
  let s3 : State := { s2 with regs := Function.update s2.regs 5 detPtr }
  have r1 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 10)))) s0 .normal s1 5 :=
    runs_assign_iff.mpr ⟨edgeRecords, by
      simp [Expr.eval, BinOp.eval, s0, startState, show 10 < 2 ^ w by omega,
        show root + 10 < 2 ^ w by omega, hdir10], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 1)) (.reg 2)) s1 .normal s2 5 :=
    runs_store_iff.mpr ⟨edgeRecords + ei, newRec,
      by simp [Expr.eval, BinOp.eval, s1, s0, startState, herW],
      by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 5 (.bin .add (.bin .add (.reg 2) (.const 2))
      (.bin .mul (.const 3) (.reg 3)))) s2 .normal s3 8 :=
    runs_assign_iff.mpr ⟨detPtr, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState,
        show 2 < 2 ^ w by omega, show 3 < 2 ^ w by omega,
        show newRec + 2 < 2 ^ w by omega, show 3 * L < 2 ^ w by omega,
        show newRec + 2 + 3 * L < 2 ^ w by omega, detPtr], rfl, rfl, rfl⟩
  have hvalAt2 : PathEdgeAt s2.mem newRec 4 L (some val) :=
    hvalAt.congr (fun a ha1 ha2 => by
      have haIdx : a = newRec + (a - newRec) := by omega
      have ht18a : tag a = 18 := by have h := ht18 (a - newRec) (by omega); rwa [← haIdx] at h
      have hne : a ≠ edgeRecords + ei := hneOfTag ht18a ht13 (by decide)
      simp [s2, s1, s0, startState, Function.update_of_ne hne])
  have hdetValid : Num.Valid s2.mem detPtr 4 L := hvalAt2.2.2.2.2.2.1
  have hdetVal : Num.intVal s2.mem detPtr 4 L = val.detector := hvalAt2.2.2.2.2.2.2
  obtain ⟨bodyN, hbodyN, oN, stN, cN, hrN, ⟨hmemN, hnegVal⟩, hcN⟩ :=
    hIsNeg [detPtr, L] s3.mem s3.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> omega)
      ⟨detPtr, L, rfl, by omega, hdetValid⟩
  change oN.value = (if Num.intVal s2.mem detPtr 4 L < 0 then 1 else 0) at hnegVal
  rw [hdetVal] at hnegVal
  change stN.mem = s2.mem at hmemN
  change cN ≤ 13 at hcN
  let s4 : State := { regs := Function.update s3.regs 6 oN.value, mem := stN.mem, pos := stN.pos }
  have r4 : Runs w p ω (.call 6 isNeg [.reg 5, .reg 3]) s3 .normal s4 (cN + 3) :=
    runs_call_iff.mpr ⟨[detPtr, L], bodyN, oN, stN, cN,
      by simp [evalArgs, Expr.eval, s3, s2, s1, s0, startState], hbodyN, hrN, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hs4_mem (a : ℕ) : stN.mem a = Function.update mem (edgeRecords + ei) newRec a := by
    rw [hmemN]; rfl
  have hs4_dir (j : ℕ) (hj : j < 14) : stN.mem (root + j) = mem (root + j) := by
    rw [hs4_mem, Function.update_of_ne (hneOfTag (ht1 j hj) ht13 (by decide))]
  have hs4_ol (k : ℕ) (hk : k < intCap) : stN.mem (offReadyList + k) = mem (offReadyList + k) := by
    rw [hs4_mem, Function.update_of_ne (hneOfTag (ht14 k hk) ht13 (by decide))]
  have hs4_io (k : ℕ) (hk : k < intCap) : stN.mem (inOffReady + k) = mem (inOffReady + k) := by
    rw [hs4_mem, Function.update_of_ne (hneOfTag (ht15 k hk) ht13 (by decide))]
  have hoff4 : OffReadyInv s4.mem offReadyCount offReadyList inOffReady intCap := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hoff
    refine ⟨h1, fun j hj => ?_, fun j₁ hj₁ j₂ hj₂ hne => ?_, fun k hk => ?_, fun k hk h1' => ?_⟩
    · rw [hs4_ol j (lt_of_lt_of_le hj h1)]
      exact ⟨(h2 j hj).1, (hs4_io _ (h2 j hj).1).trans (h2 j hj).2⟩
    · rw [hs4_ol j₁ (lt_of_lt_of_le hj₁ h1), hs4_ol j₂ (lt_of_lt_of_le hj₂ h1)]
      exact h3 j₁ hj₁ j₂ hj₂ hne
    · rw [hs4_io k hk]; exact h4 k hk
    · rw [hs4_io k hk] at h1'
      obtain ⟨j, hj, hje⟩ := h5 k hk h1'
      exact ⟨j, hj, (hs4_ol j (lt_of_lt_of_le hj h1)).trans hje⟩
  let pushBody : Stmt :=
    .assign 7 (.load (.bin .add (.reg 0) (.const 13))) ;;
    .cond (.load (.bin .add (.reg 7) (.reg 1)))
      .nop
      (.assign 8 (.load (.bin .add (.reg 0) (.const 11))) ;;
       .assign 9 (.load (.bin .add (.reg 0) (.const 12))) ;;
       .store (.bin .add (.reg 7) (.reg 1)) (.const 1) ;;
       .store (.bin .add (.reg 9) (.reg 8)) (.reg 1) ;;
       .store (.bin .add (.reg 0) (.const 11)) (.bin .add (.reg 8) (.const 1)))
  let finish {st : State} {cCond : ℕ}
      (rCond : Runs w p ω (.cond (.reg 6) .nop pushBody) s4 .normal st cCond) :
      Runs w p ω (offTreePushBody isNeg) s0 (.returned 0) st
        (5 + (5 + (8 + ((cN + 3) + (cCond + 2 + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 8, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, cN + 3, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨st, cCond, 2, rCond,
        runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩,
        rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  by_cases hneg : val.detector < 0
  · have hnb1 : oN.value = 1 := by rw [hnegVal, ite_eq_left hneg]
    have rCond : Runs w p ω (.cond (.reg 6) .nop pushBody) s4 .normal s4 3 :=
      runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, s4, hnb1],
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
        by simp [Expr.size]⟩
    refine ⟨_, s4, offReadyCount, finish rCond, by omega, Or.inl rfl,
      (hs4_dir 11 (by omega)).trans hdir11, by rw [hs4_mem, Function.update_self],
      hoff4, fun hn => by omega,
      fun k hk h1 => (hs4_io k hk).trans h1,
      fun a hneEr _ _ _ => by rw [hs4_mem, Function.update_of_ne hneEr]⟩
  · have hnb0 : oN.value = 0 := by rw [hnegVal, ite_eq_right hneg]
    let s5 : State := { s4 with regs := Function.update s4.regs 7 inOffReady }
    have r7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 13)))) s4 .normal s5 5 :=
      runs_assign_iff.mpr ⟨inOffReady, by
        simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, hw13, hroot13W,
          hs4_dir 13 (by omega), hdir13], rfl, rfl, rfl⟩
    rcases hoff.2.2.2.1 ei hei with hio0 | hio1
    · -- Push `ei` onto `offReadyList`
      have hcntLt : offReadyCount < intCap := offReadyCount_lt_of_zero hoff hei hio0
      have hcntNextW : offReadyCount + 1 < 2 ^ w := by omega
      have holPosW : offReadyList + offReadyCount < 2 ^ w := by omega
      let s6 : State := { s5 with regs := Function.update s5.regs 8 offReadyCount }
      let s7 : State := { s6 with regs := Function.update s6.regs 9 offReadyList }
      let s8 : State := { s7 with mem := Function.update s7.mem (inOffReady + ei) 1 }
      let s9 : State := { s8 with mem := Function.update s8.mem (offReadyList + offReadyCount) ei }
      let s10 : State := { s9 with mem := Function.update s9.mem (root + 11) (offReadyCount + 1) }
      have r8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 11)))) s5 .normal s6 5 :=
        runs_assign_iff.mpr ⟨offReadyCount, by
          simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState,
            show 11 < 2 ^ w by omega, show root + 11 < 2 ^ w by omega,
            hs4_dir 11 (by omega), hdir11], rfl, rfl, rfl⟩
      have r9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 12)))) s6 .normal s7 5 :=
        runs_assign_iff.mpr ⟨offReadyList, by
          simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState,
            show 12 < 2 ^ w by omega, show root + 12 < 2 ^ w by omega,
            hs4_dir 12 (by omega), hdir12], rfl, rfl, rfl⟩
      have rStIO : Runs w p ω (.store (.bin .add (.reg 7) (.reg 1)) (.const 1)) s7 .normal s8 5 :=
        runs_store_iff.mpr ⟨inOffReady + ei, 1,
          by simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState, hioW],
          by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have rStOL : Runs w p ω (.store (.bin .add (.reg 9) (.reg 8)) (.reg 1)) s8 .normal s9 5 :=
        runs_store_iff.mpr ⟨offReadyList + offReadyCount, ei,
          by simp [Expr.eval, BinOp.eval, s8, s7, s6, holPosW],
          by simp [Expr.eval, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
      have rStCnt : Runs w p ω (.store (.bin .add (.reg 0) (.const 11)) (.bin .add (.reg 8) (.const 1)))
          s9 .normal s10 7 :=
        runs_store_iff.mpr ⟨root + 11, offReadyCount + 1,
          by simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState,
            show 11 < 2 ^ w by omega, show root + 11 < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, show 1 < 2 ^ w by omega, hcntNextW],
          rfl, rfl, rfl⟩
      have rPushSeq : Runs w p ω
          (.assign 8 (.load (.bin .add (.reg 0) (.const 11))) ;;
           .assign 9 (.load (.bin .add (.reg 0) (.const 12))) ;;
           .store (.bin .add (.reg 7) (.reg 1)) (.const 1) ;;
           .store (.bin .add (.reg 9) (.reg 8)) (.reg 1) ;;
           .store (.bin .add (.reg 0) (.const 11)) (.bin .add (.reg 8) (.const 1)))
          s5 .normal s10 31 :=
        runs_seq_iff.mpr (Or.inr ⟨s6, 5, 25, r8,
          runs_seq_iff.mpr (Or.inr ⟨s7, 5, 19, r9,
          runs_seq_iff.mpr (Or.inr ⟨s8, 5, 13, rStIO,
          runs_seq_iff.mpr (Or.inr ⟨s9, 5, 7, rStOL, rStCnt, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have rCondIn : Runs w p ω (.cond (.load (.bin .add (.reg 7) (.reg 1))) .nop
          (.assign 8 (.load (.bin .add (.reg 0) (.const 11))) ;;
           .assign 9 (.load (.bin .add (.reg 0) (.const 12))) ;;
           .store (.bin .add (.reg 7) (.reg 1)) (.const 1) ;;
           .store (.bin .add (.reg 9) (.reg 8)) (.reg 1) ;;
           .store (.bin .add (.reg 0) (.const 11)) (.bin .add (.reg 8) (.const 1))))
          s5 .normal s10 36 :=
        runs_cond_iff.mpr ⟨0, 31, by
          simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, hioW,
            hs4_io ei hei, hio0],
          by simp only [↓reduceIte]; exact rPushSeq, by simp [Expr.size]⟩
      have rCond : Runs w p ω (.cond (.reg 6) .nop pushBody) s4 .normal s10 44 :=
        runs_cond_iff.mpr ⟨0, 42, by simp [Expr.eval, s4, hnb0],
          by simp only [↓reduceIte]; exact runs_seq_iff.mpr (Or.inr ⟨s5, 5, 36, r7, rCondIn, rfl⟩),
          by simp [Expr.size]⟩
      have hs10_ol (k : ℕ) (hk : k < intCap) :
          s10.mem (offReadyList + k) =
            if k = offReadyCount then ei else mem (offReadyList + k) := by
        have hne11 : offReadyList + k ≠ root + 11 := hneOfTag (ht14 k hk) (ht1 11 (by omega)) (by decide)
        have hneIO : offReadyList + k ≠ inOffReady + ei := hneOfTag (ht14 k hk) (ht15 ei hei) (by decide)
        dsimp only [s10, s9, s8, s7, s6, s5]
        rw [Function.update_of_ne hne11]
        by_cases hke : k = offReadyCount
        · subst hke; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne hneIO, hs4_ol k hk,
            ite_eq_right hke]
      have hs10_io (k : ℕ) (hk : k < intCap) :
          s10.mem (inOffReady + k) = if k = ei then 1 else mem (inOffReady + k) := by
        have hne11 : inOffReady + k ≠ root + 11 := hneOfTag (ht15 k hk) (ht1 11 (by omega)) (by decide)
        have hneOL : inOffReady + k ≠ offReadyList + offReadyCount :=
          hneOfTag (ht15 k hk) (ht14 offReadyCount hcntLt) (by decide)
        dsimp only [s10, s9, s8, s7, s6, s5]
        rw [Function.update_of_ne hne11, Function.update_of_ne hneOL]
        by_cases hke : k = ei
        · subst hke; simp
        · rw [Function.update_of_ne (by omega), hs4_io k hk, ite_eq_right hke]
      have hoff10 : OffReadyInv s10.mem (offReadyCount + 1) offReadyList inOffReady intCap := by
        refine ⟨hcntLt, ?_, ?_, ?_, ?_⟩
        · intro j hj
          rw [hs10_ol j (lt_of_lt_of_le hj hcntLt)]
          by_cases hje : j = offReadyCount
          · rw [ite_eq_left hje, hs10_io ei hei, ite_eq_left rfl]; exact ⟨hei, rfl⟩
          · rw [ite_eq_right hje]
            have hjOld : j < offReadyCount := by omega
            have hcapJ := (hoff.2.1 j hjOld).1
            rw [hs10_io _ hcapJ]
            by_cases hej : mem (offReadyList + j) = ei
            · rw [ite_eq_left hej]; exact ⟨hcapJ, rfl⟩
            · rw [ite_eq_right hej]; exact hoff.2.1 j hjOld
        · intro j₁ hj₁ j₂ hj₂ hne
          rw [hs10_ol j₁ (lt_of_lt_of_le hj₁ hcntLt), hs10_ol j₂ (lt_of_lt_of_le hj₂ hcntLt)]
          by_cases h1 : j₁ = offReadyCount <;> by_cases h2 : j₂ = offReadyCount
          · exact False.elim (hne (h1.trans h2.symm))
          · rw [ite_eq_left h1, ite_eq_right h2]
            intro heq
            have := (hoff.2.1 j₂ (by omega)).2
            rw [← heq, hio0] at this; omega
          · rw [ite_eq_right h1, ite_eq_left h2]
            intro heq
            have := (hoff.2.1 j₁ (by omega)).2
            rw [heq, hio0] at this; omega
          · rw [ite_eq_right h1, ite_eq_right h2]
            exact hoff.2.2.1 j₁ (by omega) j₂ (by omega) hne
        · intro k hk
          rw [hs10_io k hk]
          by_cases hke : k = ei
          · rw [ite_eq_left hke]; exact Or.inr rfl
          · rw [ite_eq_right hke]; exact hoff.2.2.2.1 k hk
        · intro k hk h1'
          rw [hs10_io k hk] at h1'
          by_cases hke : k = ei
          · subst hke
            exact ⟨offReadyCount, Nat.lt_succ_self _, by rw [hs10_ol offReadyCount hcntLt, ite_eq_left rfl]⟩
          · rw [ite_eq_right hke] at h1'
            obtain ⟨j, hj, hje⟩ := hoff.2.2.2.2 k hk h1'
            exact ⟨j, by omega, by rw [hs10_ol j (lt_of_lt_of_le hj hoff.1), ite_eq_right (by omega), hje]⟩
      refine ⟨_, s10, offReadyCount + 1, finish rCond, by omega, Or.inr rfl,
        by simp [s10], ?_, hoff10, fun _ => by rw [hs10_io ei hei, ite_eq_left rfl],
        fun k hk h1 => by rw [hs10_io k hk]; by_cases hke : k = ei <;> simp [hke, h1],
        fun a hneEr hneIO hneOL hne11 => by
          dsimp only [s10, s9, s8, s7, s6, s5]
          rw [Function.update_of_ne hne11, Function.update_of_ne (hneOL rfl),
            Function.update_of_ne hneIO, hs4_mem, Function.update_of_ne hneEr]⟩
      dsimp only [s10, s9, s8, s7, s6, s5, s4]
      rw [Function.update_of_ne (hneOfTag ht13 (ht1 11 (by omega)) (by decide)),
        Function.update_of_ne (hneOfTag ht13 (ht14 offReadyCount hcntLt) (by decide)),
        Function.update_of_ne (hneOfTag ht13 (ht15 ei hei) (by decide)),
        hs4_mem, Function.update_self]
    · -- Already in `offReadyList`: `inOffReady[ei] = 1`, no push needed
      have rCondIn : Runs w p ω (.cond (.load (.bin .add (.reg 7) (.reg 1))) .nop
          (.assign 8 (.load (.bin .add (.reg 0) (.const 11))) ;;
           .assign 9 (.load (.bin .add (.reg 0) (.const 12))) ;;
           .store (.bin .add (.reg 7) (.reg 1)) (.const 1) ;;
           .store (.bin .add (.reg 9) (.reg 8)) (.reg 1) ;;
           .store (.bin .add (.reg 0) (.const 11)) (.bin .add (.reg 8) (.const 1))))
          s5 .normal s5 6 :=
        runs_cond_iff.mpr ⟨1, 1, by
          simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, hioW,
            hs4_io ei hei, hio1],
          by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
          by simp [Expr.size]⟩
      have rCond : Runs w p ω (.cond (.reg 6) .nop pushBody) s4 .normal s5 14 :=
        runs_cond_iff.mpr ⟨0, 12, by simp [Expr.eval, s4, hnb0],
          by simp only [↓reduceIte]; exact runs_seq_iff.mpr (Or.inr ⟨s5, 5, 6, r7, rCondIn, rfl⟩),
          by simp [Expr.size]⟩
      refine ⟨_, s5, offReadyCount, finish rCond, by omega, Or.inl rfl,
        (hs4_dir 11 (by omega)).trans hdir11, by rw [show s5.mem = s4.mem from rfl, hs4_mem, Function.update_self],
        hoff4, fun _ => (hs4_io ei hei).trans hio1,
        fun k hk h1 => (hs4_io k hk).trans h1,
        fun a hneEr _ _ _ => by rw [show s5.mem = s4.mem from rfl, hs4_mem, Function.update_of_ne hneEr]⟩

end MinCostFlow.MinRatio
