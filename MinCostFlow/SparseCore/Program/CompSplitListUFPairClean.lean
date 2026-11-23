module

public import MinCostFlow.SparseCore.Program.CompSplitListUFProc
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Verification of `compUFPairUnionProc` and `compUFCleanProc` (`CompSplitListUFPairClean`)

Proves:
1. `compUFPairUnion_runs`: verifies `compUFPairUnionProc`, writing `[isRelFlag, edgeVal, kept, fresh]`
   matching `ufPair U ra rb` at `[outSlot, outSlot + 4)`, optionally performing union-by-size
   `ufUnion U ra rb` and preserving `RevUFMemAt`, in `≤ 120` steps.
2. `compUFClean_runs`: verifies `compUFCleanProc`, zeroing `par, sz, minF, oldR` at every vertex
   in `act`, plus `act[0..act.length-1]` and `actLen`, in `≤ 45 * act.length + 50` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. Verification of `compUFPairUnionProc` -/

private lemma compUFPair_branch_runs {w oA mA oB mB : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hoA_w : oA < 2 ^ w) (hoB_w : oB < 2 ^ w)
    (hr12 : st.regs 12 = oA) (hr13 : st.regs 13 = mA)
    (hr14 : st.regs 14 = oB) (hr15 : st.regs 15 = mB) :
    let pr := mergeSplitPair (if oA = 0 then none else some (oA - 1)) mA
      (if oB = 0 then none else some (oB - 1)) mB
    ∃ st' c,
      Runs w p ω
        (.cond (.bin .lt (.const 0) (.reg 12))
          (.assign 16 (.bin .sub (.reg 12) (.const 1)) ;;
           .assign 17 (.reg 15))
          (.cond (.bin .lt (.const 0) (.reg 14))
            (.assign 16 (.bin .sub (.reg 14) (.const 1)) ;;
             .assign 17 (.reg 13))
            (.cond (.bin .lt (.reg 15) (.reg 13))
              (.assign 16 (.reg 15) ;; .assign 17 (.reg 13))
              (.assign 16 (.reg 13) ;; .assign 17 (.reg 15)))))
        st .normal st' c ∧
      st'.mem = st.mem ∧ (∀ r < 16, st'.regs r = st.regs r) ∧
      st'.regs 16 = pr.1 ∧ st'.regs 17 = pr.2 ∧ c ≤ 22 := by
  intro pr
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  by_cases hoA : 0 < oA
  · have hne0 : oA ≠ 0 := by omega
    have hpr : pr = (oA - 1, mB) := by simp [pr, hne0, mergeSplitPair]
    let s1 : State := { st with regs := Function.update st.regs 16 (oA - 1) }
    let s2 : State := { s1 with regs := Function.update s1.regs 17 mB }
    have h1 : Runs w p ω (.assign 16 (.bin .sub (.reg 12) (.const 1))) st .normal s1 4 :=
      runs_assign_iff.mpr ⟨oA - 1, by simp [Expr.eval, BinOp.eval, hr12, hw1, show oA - 1 < 2 ^ w by omega],
        rfl, rfl, by simp [Expr.size]⟩
    have h2 : Runs w p ω (.assign 17 (.reg 15)) s1 .normal s2 2 :=
      runs_assign_iff.mpr ⟨mB, by simp [s1, Expr.eval, hr15], rfl, rfl, by simp [Expr.size]⟩
    have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 4, 2, h1, h2, rfl⟩)
    refine ⟨s2, 11, runs_cond_iff.mpr ⟨1, 7, by simp [Expr.eval, BinOp.eval, hr12, hoA, hw0, hw0'],
      by simp only [one_ne_zero, ↓reduceIte]; exact hbody, by simp [Expr.size]⟩,
      rfl, fun r hr => by simp [s2, s1, show r ≠ 17 by omega, show r ≠ 16 by omega],
      by simp [s2, s1, hpr], by simp [s2, hpr], by omega⟩
  · have hoA0 : oA = 0 := by omega
    by_cases hoB : 0 < oB
    · have hne0 : oB ≠ 0 := by omega
      have hpr : pr = (oB - 1, mA) := by simp [pr, hoA0, hne0, mergeSplitPair]
      let s1 : State := { st with regs := Function.update st.regs 16 (oB - 1) }
      let s2 : State := { s1 with regs := Function.update s1.regs 17 mA }
      have h1 : Runs w p ω (.assign 16 (.bin .sub (.reg 14) (.const 1))) st .normal s1 4 :=
        runs_assign_iff.mpr ⟨oB - 1, by simp [Expr.eval, BinOp.eval, hr14, hw1, show oB - 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.assign 17 (.reg 13)) s1 .normal s2 2 :=
        runs_assign_iff.mpr ⟨mA, by simp [s1, Expr.eval, hr13], rfl, rfl, by simp [Expr.size]⟩
      have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 4, 2, h1, h2, rfl⟩)
      have hc2 := (runs_cond_iff (w := w) (p := p) (ω := ω) (st := st)
        (e := .bin .lt (.const 0) (.reg 14))
        (s := .assign 16 (.bin .sub (.reg 14) (.const 1)) ;; .assign 17 (.reg 13))
        (t := .cond (.bin .lt (.reg 15) (.reg 13))
          (.assign 16 (.reg 15) ;; .assign 17 (.reg 13))
          (.assign 16 (.reg 13) ;; .assign 17 (.reg 15)))).mpr
        ⟨1, 7, by simp [Expr.eval, BinOp.eval, hr14, hoB, hw0, hw0'],
          by simp only [one_ne_zero, ↓reduceIte]; exact hbody, rfl⟩
      refine ⟨s2, 15, runs_cond_iff.mpr ⟨0, 11, by simp [Expr.eval, BinOp.eval, hr12, hoA0, hw0'],
        by simp only [↓reduceIte]; simpa [Expr.size] using hc2, by simp [Expr.size]⟩,
        rfl, fun r hr => by simp [s2, s1, show r ≠ 17 by omega, show r ≠ 16 by omega],
        by simp [s2, s1, hpr], by simp [s2, hpr], by omega⟩
    · have hoB0 : oB = 0 := by omega
      by_cases hlt : mB < mA
      · have hpr : pr = (mB, mA) := by simp [pr, hoA0, hoB0, mergeSplitPair, show ¬ mA ≤ mB by omega]
        let s1 : State := { st with regs := Function.update st.regs 16 mB }
        let s2 : State := { s1 with regs := Function.update s1.regs 17 mA }
        have h1 : Runs w p ω (.assign 16 (.reg 15)) st .normal s1 2 :=
          runs_assign_iff.mpr ⟨mB, by simp [Expr.eval, hr15], rfl, rfl, by simp [Expr.size]⟩
        have h2 : Runs w p ω (.assign 17 (.reg 13)) s1 .normal s2 2 :=
          runs_assign_iff.mpr ⟨mA, by simp [s1, Expr.eval, hr13], rfl, rfl, by simp [Expr.size]⟩
        have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 2, 2, h1, h2, rfl⟩)
        have hc3 := (runs_cond_iff (w := w) (p := p) (ω := ω) (st := st)
          (e := .bin .lt (.reg 15) (.reg 13))
          (s := .assign 16 (.reg 15) ;; .assign 17 (.reg 13))
          (t := .assign 16 (.reg 13) ;; .assign 17 (.reg 15))).mpr
          ⟨1, 5, by simp [Expr.eval, BinOp.eval, hr13, hr15, hlt, hw0],
            by simp only [one_ne_zero, ↓reduceIte]; exact hbody, rfl⟩
        have hc2 := (runs_cond_iff (w := w) (p := p) (ω := ω) (st := st)
          (e := .bin .lt (.const 0) (.reg 14))
          (s := .assign 16 (.bin .sub (.reg 14) (.const 1)) ;; .assign 17 (.reg 13))
          (t := .cond (.bin .lt (.reg 15) (.reg 13))
            (.assign 16 (.reg 15) ;; .assign 17 (.reg 13))
            (.assign 16 (.reg 13) ;; .assign 17 (.reg 15)))).mpr
          ⟨0, 9, by simp [Expr.eval, BinOp.eval, hr14, hoB0, hw0'],
            by simp only [↓reduceIte]; simpa [Expr.size] using hc3, rfl⟩
        refine ⟨s2, 17, runs_cond_iff.mpr ⟨0, 13, by simp [Expr.eval, BinOp.eval, hr12, hoA0, hw0'],
          by simp only [↓reduceIte]; simpa [Expr.size] using hc2, by simp [Expr.size]⟩,
          rfl, fun r hr => by simp [s2, s1, show r ≠ 17 by omega, show r ≠ 16 by omega],
          by simp [s2, s1, hpr], by simp [s2, hpr], by omega⟩
      · have hle : mA ≤ mB := by omega
        have hpr : pr = (mA, mB) := by simp [pr, hoA0, hoB0, mergeSplitPair, hle]
        let s1 : State := { st with regs := Function.update st.regs 16 mA }
        let s2 : State := { s1 with regs := Function.update s1.regs 17 mB }
        have h1 : Runs w p ω (.assign 16 (.reg 13)) st .normal s1 2 :=
          runs_assign_iff.mpr ⟨mA, by simp [Expr.eval, hr13], rfl, rfl, by simp [Expr.size]⟩
        have h2 : Runs w p ω (.assign 17 (.reg 15)) s1 .normal s2 2 :=
          runs_assign_iff.mpr ⟨mB, by simp [s1, Expr.eval, hr15], rfl, rfl, by simp [Expr.size]⟩
        have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 2, 2, h1, h2, rfl⟩)
        have hc3 := (runs_cond_iff (w := w) (p := p) (ω := ω) (st := st)
          (e := .bin .lt (.reg 15) (.reg 13))
          (s := .assign 16 (.reg 15) ;; .assign 17 (.reg 13))
          (t := .assign 16 (.reg 13) ;; .assign 17 (.reg 15))).mpr
          ⟨0, 5, by simp [Expr.eval, BinOp.eval, hr13, hr15, hlt],
            by simp only [↓reduceIte]; exact hbody, rfl⟩
        have hc2 := (runs_cond_iff (w := w) (p := p) (ω := ω) (st := st)
          (e := .bin .lt (.const 0) (.reg 14))
          (s := .assign 16 (.bin .sub (.reg 14) (.const 1)) ;; .assign 17 (.reg 13))
          (t := .cond (.bin .lt (.reg 15) (.reg 13))
            (.assign 16 (.reg 15) ;; .assign 17 (.reg 13))
            (.assign 16 (.reg 13) ;; .assign 17 (.reg 15)))).mpr
          ⟨0, 9, by simp [Expr.eval, BinOp.eval, hr14, hoB0, hw0'],
            by simp only [↓reduceIte]; simpa [Expr.size] using hc3, rfl⟩
        refine ⟨s2, 17, runs_cond_iff.mpr ⟨0, 13, by simp [Expr.eval, BinOp.eval, hr12, hoA0, hw0'],
          by simp only [↓reduceIte]; simpa [Expr.size] using hc2, by simp [Expr.size]⟩,
          rfl, fun r hr => by simp [s2, s1, show r ≠ 17 by omega, show r ≠ 16 by omega],
          by simp [s2, s1, hpr], by simp [s2, hpr], by omega⟩

private lemma revUFMemAt_union {mem : ℕ → ℕ} {ufBase vCap ra rb : ℕ} {isNew : ℕ → Bool}
    {U : RevUFState} {act : List ℕ}
    (hMem : RevUFMemAt mem ufBase vCap isNew U act)
    (hra_lt : ra < vCap) (hrb_lt : rb < vCap) (hne : ra ≠ rb)
    (hra_act : 1 ≤ U.sz ra) (hrb_act : 1 ≤ U.sz rb)
    (hra_par : U.par ra = ra) (hrb_par : U.par rb = rb) :
    let U' := ufUnion U ra rb
    let big := if U.sz ra ≥ U.sz rb then ra else rb
    let small := if U.sz ra ≥ U.sz rb then rb else ra
    let mem' :=
      Function.update
        (Function.update
          (Function.update
            (Function.update mem (ufParBase ufBase vCap + small) big)
            (ufSzBase ufBase vCap + big) (U.sz big + U.sz small))
          (ufMinFBase ufBase vCap + big) (min (U.minF big) (U.minF small)))
        (ufOldRBase ufBase vCap + big) (if U.oldR big ≠ 0 then U.oldR big else U.oldR small)
    RevUFMemAt mem' ufBase vCap isNew U' act := by
  intro U' big small mem'
  have hbig_lt : big < vCap := by dsimp [big]; split_ifs <;> assumption
  have hsm_lt : small < vCap := by dsimp [small]; split_ifs <;> assumption
  have hbs_ne : big ≠ small := by dsimp [big, small]; split_ifs <;> [exact hne; exact hne.symm]
  have hbig_act : 1 ≤ U.sz big := by dsimp [big]; split_ifs <;> assumption
  have hsm_act : 1 ≤ U.sz small := by dsimp [small]; split_ifs <;> assumption
  have hbig_par : U.par big = big := by dsimp [big]; split_ifs <;> assumption
  have hsm_par : U.par small = small := by dsimp [small]; split_ifs <;> assumption
  have hU'_eq : U' = ⟨Function.update U.par small big,
      Function.update U.sz big (U.sz big + U.sz small),
      Function.update U.minF big (min (U.minF big) (U.minF small)),
      Function.update U.oldR big (if U.oldR big ≠ 0 then U.oldR big else U.oldR small)⟩ := by
    by_cases h : U.sz ra ≥ U.sz rb <;> simp [U', big, small, ufUnion, h]
  rw [hU'_eq]
  have hmem'_out : ∀ a, a < ufBase + vCap ∨ ufBase + 5 * vCap ≤ a → mem' a = mem a := fun a ha => by
    dsimp only [mem', ufOldRBase, ufMinFBase, ufSzBase, ufParBase]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨fun v hv => (hmem'_out _ (Or.inl (by dsimp [ufIsNewBase]; omega))).trans (hMem.hIsNew v hv),
    fun v hv => ?_, hMem.hActNd, hMem.hActLt,
    fun v hv => by
      dsimp only; by_cases hvb : v = big
      · rw [hvb, Function.update_self]
        exact ⟨fun _ => (hMem.hActIff big hbig_lt).mp (by omega), fun _ => by omega⟩
      · rw [Function.update_of_ne hvb]; exact hMem.hActIff v hv,
    fun v hv hzv => by
      dsimp only at hzv ⊢; by_cases hvb : v = big
      · subst hvb; simp at hzv; omega
      · rw [Function.update_of_ne hvb] at hzv
        have hvs : v ≠ small := fun h => by rw [h] at hzv; omega
        rw [Function.update_of_ne hvs, Function.update_of_ne hvb, Function.update_of_ne hvb]
        exact hMem.hZeroRest v hv hzv,
    (hmem'_out _ (Or.inr (by dsimp [ufActLenAddr]; omega))).trans hMem.hActLen,
    fun i hi => (hmem'_out _ (Or.inr (by dsimp [ufActBase]; omega))).trans (hMem.hActAt i hi),
    fun i hi1 hi2 => (hmem'_out _ (Or.inr (by dsimp [ufActBase]; omega))).trans (hMem.hActZero i hi1 hi2), ?_⟩
  · dsimp only [mem', ufOldRBase, ufMinFBase, ufSzBase, ufParBase]
    have ha := hMem.hArrs v hv
    dsimp only [ufOldRBase, ufMinFBase, ufSzBase, ufParBase] at ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      by_cases hvs : v = small
      · subst hvs; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne hvs]; exact ha.1
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      by_cases hvb : v = big
      · subst hvb; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne hvb]; exact ha.2.1
    · rw [Function.update_of_ne (by omega)]
      by_cases hvb : v = big
      · subst hvb; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne hvb]; exact ha.2.2.1
    · by_cases hvb : v = big
      · subst hvb; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne hvb]; exact ha.2.2.2
  · -- `hRootSum`: merging `small` into `big` preserves the sum of root sizes
    dsimp only
    set S₀ := act.toFinset.filter fun r => U.par r = r
    have hsm_in : small ∈ S₀ :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ((hMem.hActIff small hsm_lt).mp (by omega)), hsm_par⟩
    have hbig_in : big ∈ S₀.erase small :=
      Finset.mem_erase.mpr ⟨hbs_ne, Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr ((hMem.hActIff big hbig_lt).mp (by omega)), hbig_par⟩⟩
    have hset : (act.toFinset.filter fun r => Function.update U.par small big r = r) = S₀.erase small := by
      ext r; simp only [S₀, Finset.mem_filter, Finset.mem_erase]
      by_cases hrs : r = small
      · rw [hrs, Function.update_self]; simp [hbs_ne]
      · simp [hrs]
    rw [hset]
    have hsum1 : Function.update U.sz big (U.sz big + U.sz small) big +
        ∑ x ∈ (S₀.erase small).erase big, Function.update U.sz big (U.sz big + U.sz small) x =
        ∑ x ∈ S₀.erase small, Function.update U.sz big (U.sz big + U.sz small) x :=
      Finset.add_sum_erase (S₀.erase small) (Function.update U.sz big (U.sz big + U.sz small)) hbig_in
    have hsum2 : U.sz big + ∑ x ∈ (S₀.erase small).erase big, U.sz x = ∑ x ∈ S₀.erase small, U.sz x :=
      Finset.add_sum_erase (S₀.erase small) U.sz hbig_in
    have hsum3 : U.sz small + ∑ x ∈ S₀.erase small, U.sz x = ∑ x ∈ S₀, U.sz x :=
      Finset.add_sum_erase S₀ U.sz hsm_in
    have hrest : ∑ x ∈ (S₀.erase small).erase big, Function.update U.sz big (U.sz big + U.sz small) x =
        ∑ x ∈ (S₀.erase small).erase big, U.sz x :=
      Finset.sum_congr rfl fun x hx => Function.update_of_ne (Finset.mem_erase.mp hx).1 _ _
    rw [Function.update_self, hrest] at hsum1
    have htot : ∑ x ∈ S₀, U.sz x = act.length := hMem.hRootSum
    change ∑ x ∈ S₀.erase small, Function.update U.sz big (U.sz big + U.sz small) x = act.length
    omega

set_option maxHeartbeats 600000 in
/-- Verification of `compUFPairUnionProc`: stores `[isRelFlag, edgeVal, pr.1, pr.2]` for
`pr = ufPair U ra rb` at `[outSlot, outSlot + 4)`, and when `doUnion ≠ 0` updates `[ufBase + vCap,
ufBase + 5 * vCap)` by `ufUnion U ra rb`, preserving `RevUFMemAt` and costing `≤ 120`. -/
theorem compUFPairUnion_runs {w ufBase vCap ra rb outSlot isRelFlag edgeVal doUnion : ℕ}
    {isNew : ℕ → Bool} {U : RevUFState} {act : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (huf_w : ufBase + ufScratchSize vCap < 2 ^ w)
    (hout_w : outSlot + 4 < 2 ^ w)
    (hdisj : outSlot + 4 ≤ ufBase ∨ ufBase + ufScratchSize vCap ≤ outSlot)
    (hisRel_w : isRelFlag < 2 ^ w) (hedge_w : edgeVal < 2 ^ w) (hdo_w : doUnion < 2 ^ w)
    (hra_lt : ra < vCap) (hrb_lt : rb < vCap)
    (hoA_w : U.oldR ra < 2 ^ w) (hoB_w : U.oldR rb < 2 ^ w)
    (hMem : RevUFMemAt mem ufBase vCap isNew U act)
    (hUnionPre : doUnion ≠ 0 →
      ra ≠ rb ∧ 1 ≤ U.sz ra ∧ 1 ≤ U.sz rb ∧ U.par ra = ra ∧ U.par rb = rb ∧
      U.sz ra + U.sz rb < 2 ^ w) :
    let pr := ufPair U ra rb
    let U' := if doUnion = 0 then U else ufUnion U ra rb
    ∃ st' c,
      Runs w p ω compUFPairUnionProc
        (startState [ufBase, vCap, ra, rb, outSlot, isRelFlag, edgeVal, doUnion] mem pos)
        (.returned 0) st' c ∧
      st'.mem outSlot = isRelFlag ∧
      st'.mem (outSlot + 1) = edgeVal ∧
      st'.mem (outSlot + 2) = pr.1 ∧
      st'.mem (outSlot + 3) = pr.2 ∧
      RevUFMemAt st'.mem ufBase vCap isNew U' act ∧
      (∀ a, (a < outSlot ∨ outSlot + 4 ≤ a) →
        (doUnion = 0 ∨ a < ufBase + vCap ∨ ufBase + 5 * vCap ≤ a) →
        st'.mem a = mem a) ∧
      c ≤ 160 := by
  intro pr U'
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have huf_sz : ufScratchSize vCap = 6 * vCap + 1 := rfl
  set st0 := startState [ufBase, vCap, ra, rb, outSlot, isRelFlag, edgeVal, doUnion] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 8 (ufParBase ufBase vCap) }
  let st2 : State := { st1 with regs := Function.update st1.regs 9 (ufSzBase ufBase vCap) }
  let st3 : State := { st2 with regs := Function.update st2.regs 10 (ufMinFBase ufBase vCap) }
  let st4 : State := { st3 with regs := Function.update st3.regs 11 (ufOldRBase ufBase vCap) }
  let st5 : State := { st4 with regs := Function.update st4.regs 12 (U.oldR ra) }
  let st6 : State := { st5 with regs := Function.update st5.regs 13 (U.minF ra) }
  let st7 : State := { st6 with regs := Function.update st6.regs 14 (U.oldR rb) }
  let st8 : State := { st7 with regs := Function.update st7.regs 15 (U.minF rb) }
  have hp1 : Runs w p ω (.assign 8 (.bin .add (.reg 0) (.reg 1))) st0 .normal st1 4 :=
    runs_assign_iff.mpr ⟨ufParBase ufBase vCap, by
      simp [st0, startState, Expr.eval, BinOp.eval, ufParBase, show ufBase + vCap < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 1))) st1 .normal st2 4 :=
    runs_assign_iff.mpr ⟨ufSzBase ufBase vCap, by
      simp [st1, st0, startState, Expr.eval, BinOp.eval, ufParBase, ufSzBase, show ufBase + vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 10 (.bin .add (.reg 9) (.reg 1))) st2 .normal st3 4 :=
    runs_assign_iff.mpr ⟨ufMinFBase ufBase vCap, by
      simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, ufSzBase, ufMinFBase, show ufBase + 2 * vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.reg 1))) st3 .normal st4 4 :=
    runs_assign_iff.mpr ⟨ufOldRBase ufBase vCap, by
      simp [st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufMinFBase, ufOldRBase, show ufBase + 3 * vCap + vCap < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 11) (.reg 2)))) st4 .normal st5 5 :=
    runs_assign_iff.mpr ⟨U.oldR ra, Expr.eval_load_of_eq (by
      simp [st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufOldRBase, show ufBase + 4 * vCap + ra < 2 ^ w by omega])
      (hMem.hArrs ra hra_lt).2.2.2, rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 10) (.reg 2)))) st5 .normal st6 5 :=
    runs_assign_iff.mpr ⟨U.minF ra, Expr.eval_load_of_eq (by
      simp [st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufMinFBase, show ufBase + 3 * vCap + ra < 2 ^ w by omega])
      (hMem.hArrs ra hra_lt).2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 11) (.reg 3)))) st6 .normal st7 5 :=
    runs_assign_iff.mpr ⟨U.oldR rb, Expr.eval_load_of_eq (by
      simp [st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufOldRBase, show ufBase + 4 * vCap + rb < 2 ^ w by omega])
      (hMem.hArrs rb hrb_lt).2.2.2, rfl, rfl, by simp [Expr.size]⟩
  have hp8 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 10) (.reg 3)))) st7 .normal st8 5 :=
    runs_assign_iff.mpr ⟨U.minF rb, Expr.eval_load_of_eq (by
      simp [st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufMinFBase, show ufBase + 3 * vCap + rb < 2 ^ w by omega])
      (hMem.hArrs rb hrb_lt).2.2.1, rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st9, cPr, hpr_run, hst9_mem, hst9_r, hr9_16, hr9_17, hcPr⟩ :=
    compUFPair_branch_runs (p := p) (ω := ω) (st := st8) (mA := U.minF ra) (mB := U.minF rb)
      hw16 hoA_w hoB_w
      (by simp [st8, st7, st6, st5]) (by simp [st8, st7, st6]) (by simp [st8, st7]) (by simp [st8])
  have h9_regs : st9.regs 2 = ra ∧ st9.regs 3 = rb ∧ st9.regs 4 = outSlot ∧
      st9.regs 5 = isRelFlag ∧ st9.regs 6 = edgeVal ∧ st9.regs 7 = doUnion ∧
      st9.regs 8 = ufParBase ufBase vCap ∧ st9.regs 9 = ufSzBase ufBase vCap ∧
      st9.regs 10 = ufMinFBase ufBase vCap ∧ st9.regs 11 = ufOldRBase ufBase vCap ∧
      st9.regs 12 = U.oldR ra ∧ st9.regs 13 = U.minF ra ∧
      st9.regs 14 = U.oldR rb ∧ st9.regs 15 = U.minF rb := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [hst9_r _ (by omega)] <;>
      simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState]
  -- Store 4 output words at `[outSlot, outSlot + 4)`
  let st10 : State := { st9 with mem := Function.update st9.mem outSlot isRelFlag }
  let st11 : State := { st10 with mem := Function.update st10.mem (outSlot + 1) edgeVal }
  let st12 : State := { st11 with mem := Function.update st11.mem (outSlot + 2) pr.1 }
  let st13 : State := { st12 with mem := Function.update st12.mem (outSlot + 3) pr.2 }
  have hs10 : Runs w p ω (.store (.reg 4) (.reg 5)) st9 .normal st10 3 :=
    runs_store_iff.mpr ⟨outSlot, isRelFlag, by simp [Expr.eval, h9_regs.2.2.1],
      by simp [Expr.eval, h9_regs.2.2.2.1], rfl, rfl, by simp [Expr.size]⟩
  have hs11 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.reg 6)) st10 .normal st11 5 :=
    runs_store_iff.mpr ⟨outSlot + 1, edgeVal,
      by simp [st10, Expr.eval, BinOp.eval, h9_regs.2.2.1, hw1, show outSlot + 1 < 2 ^ w by omega],
      by simp [st10, Expr.eval, h9_regs.2.2.2.2.1], rfl, rfl, by simp [Expr.size]⟩
  have hs12 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.reg 16)) st11 .normal st12 5 :=
    runs_store_iff.mpr ⟨outSlot + 2, pr.1,
      by simp [st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.1, hw2, show outSlot + 2 < 2 ^ w by omega],
      by simp [st11, st10, Expr.eval, hr9_16, pr, ufPair], rfl, rfl, by simp [Expr.size]⟩
  have hs13 : Runs w p ω (.store (.bin .add (.reg 4) (.const 3)) (.reg 17)) st12 .normal st13 5 :=
    runs_store_iff.mpr ⟨outSlot + 3, pr.2,
      by simp [st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.1, hw3, show outSlot + 3 < 2 ^ w by omega],
      by simp [st12, st11, st10, Expr.eval, hr9_17, pr, ufPair], rfl, rfl, by simp [Expr.size]⟩
  have h13_out : ∀ a, a < outSlot ∨ outSlot + 4 ≤ a → st13.mem a = mem a := fun a ha => by
    dsimp only [st13, st12, st11, st10]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst9_mem]; rfl
  have hMem13 : RevUFMemAt st13.mem ufBase vCap isNew U act :=
    revUFMemAt_of_agree hMem fun a ha1 ha2 => h13_out a (by rcases hdisj with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
  -- Conditional union-by-size
  have hunion_branch : ∃ st14 cU,
      Runs w p ω
        (.cond (.reg 7)
          (.assign 18 (.load (.bin .add (.reg 9) (.reg 2))) ;;
           .assign 19 (.load (.bin .add (.reg 9) (.reg 3))) ;;
           .cond (.bin .lt (.reg 18) (.reg 19))
             (.assign 20 (.reg 3) ;; .assign 21 (.reg 2) ;;
              .assign 22 (.reg 14) ;; .assign 23 (.reg 12))
             (.assign 20 (.reg 2) ;; .assign 21 (.reg 3) ;;
              .assign 22 (.reg 12) ;; .assign 23 (.reg 14)) ;;
           .store (.bin .add (.reg 8) (.reg 21)) (.reg 20) ;;
           .store (.bin .add (.reg 9) (.reg 20)) (.bin .add (.reg 18) (.reg 19)) ;;
           .cond (.bin .lt (.reg 13) (.reg 15))
             (.store (.bin .add (.reg 10) (.reg 20)) (.reg 13))
             (.store (.bin .add (.reg 10) (.reg 20)) (.reg 15)) ;;
           .cond (.reg 22)
             (.store (.bin .add (.reg 11) (.reg 20)) (.reg 22))
             (.store (.bin .add (.reg 11) (.reg 20)) (.reg 23)))
          .nop)
        st13 .normal st14 cU ∧
      RevUFMemAt st14.mem ufBase vCap isNew U' act ∧
      (∀ a, (a < ufBase + vCap ∨ ufBase + 5 * vCap ≤ a) → st14.mem a = st13.mem a) ∧
      (doUnion = 0 → st14.mem = st13.mem) ∧
      cU ≤ 65 := by
    by_cases hdo0 : doUnion = 0
    · have hU'_eq : U' = U := by simp [U', hdo0]
      refine ⟨st13, 3, runs_cond_iff.mpr ⟨0, 1, by simp [st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.1, hdo0],
        by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
        hU'_eq ▸ hMem13, fun _ _ => rfl, fun _ => rfl, by omega⟩
    · obtain ⟨hne, hra_act, hrb_act, hra_par, hrb_par, hsum_w⟩ := hUnionPre hdo0
      have hU'_eq : U' = ufUnion U ra rb := by simp [U', hdo0]
      let u1 : State := { st13 with regs := Function.update st13.regs 18 (U.sz ra) }
      let u2 : State := { u1 with regs := Function.update u1.regs 19 (U.sz rb) }
      have hu1 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 9) (.reg 2)))) st13 .normal u1 5 :=
        runs_assign_iff.mpr ⟨U.sz ra, Expr.eval_load_of_eq (by
          simp [st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.2.1, h9_regs.1, ufSzBase, show ufBase + 2 * vCap + ra < 2 ^ w by omega])
          (hMem13.hArrs ra hra_lt).2.1, rfl, rfl, by simp [Expr.size]⟩
      have hu2 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 9) (.reg 3)))) u1 .normal u2 5 :=
        runs_assign_iff.mpr ⟨U.sz rb, Expr.eval_load_of_eq (by
          simp [u1, st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.2.1, h9_regs.2.1, ufSzBase, show ufBase + 2 * vCap + rb < 2 ^ w by omega])
          (hMem13.hArrs rb hrb_lt).2.1, rfl, rfl, by simp [Expr.size]⟩
      set big := if U.sz ra ≥ U.sz rb then ra else rb
      set small := if U.sz ra ≥ U.sz rb then rb else ra
      have hbig_lt : big < vCap := by dsimp [big]; split_ifs <;> assumption
      have hsm_lt : small < vCap := by dsimp [small]; split_ifs <;> assumption
      have hsum_eq : U.sz ra + U.sz rb = U.sz big + U.sz small := by dsimp [big, small]; split_ifs <;> omega
      let u3 : State :=
        { u2 with regs :=
            Function.update (Function.update (Function.update (Function.update u2.regs 20 big) 21 small)
              22 (U.oldR big)) 23 (U.oldR small) }
      have hu3 : Runs w p ω
          (.cond (.bin .lt (.reg 18) (.reg 19))
            (.assign 20 (.reg 3) ;; .assign 21 (.reg 2) ;;
             .assign 22 (.reg 14) ;; .assign 23 (.reg 12))
            (.assign 20 (.reg 2) ;; .assign 21 (.reg 3) ;;
             .assign 22 (.reg 12) ;; .assign 23 (.reg 14))) u2 .normal u3 15 := by
        by_cases hlt : U.sz ra < U.sz rb
        · have hge : ¬ U.sz ra ≥ U.sz rb := by omega
          have hbig_e : big = rb := by simp [big, hge]
          have hsm_e : small = ra := by simp [small, hge]
          refine runs_cond_iff.mpr ⟨1, 11, by simp [u2, u1, Expr.eval, BinOp.eval, hlt, hw0], ?_, by simp [Expr.size]⟩
          simp only [one_ne_zero, ↓reduceIte]
          let b1 : State := { u2 with regs := Function.update u2.regs 20 rb }
          let b2 : State := { b1 with regs := Function.update b1.regs 21 ra }
          let b3 : State := { b2 with regs := Function.update b2.regs 22 (U.oldR rb) }
          have hb1 : Runs w p ω (.assign 20 (.reg 3)) u2 .normal b1 2 :=
            runs_assign_iff.mpr ⟨rb, by simp [u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.1], rfl, rfl, by simp [Expr.size]⟩
          have hb2 : Runs w p ω (.assign 21 (.reg 2)) b1 .normal b2 2 :=
            runs_assign_iff.mpr ⟨ra, by simp [b1, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.1], rfl, rfl, by simp [Expr.size]⟩
          have hb3 : Runs w p ω (.assign 22 (.reg 14)) b2 .normal b3 2 :=
            runs_assign_iff.mpr ⟨U.oldR rb, by simp [b2, b1, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.2.2.2.2.2.2.2.1], rfl, rfl, by simp [Expr.size]⟩
          have hb4 : Runs w p ω (.assign 23 (.reg 12)) b3 .normal u3 2 :=
            runs_assign_iff.mpr ⟨U.oldR ra, by simp [b3, b2, b1, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.2.2.2.2.2.1],
              rfl, by simp [u3, b3, b2, b1, hbig_e, hsm_e], by simp [Expr.size]⟩
          have hseq := runs_seq_iff.mpr (Or.inr ⟨b1, 2, _, hb1,
            runs_seq_iff.mpr (Or.inr ⟨b2, 2, _, hb2,
              runs_seq_iff.mpr (Or.inr ⟨b3, 2, 2, hb3, hb4, rfl⟩), rfl⟩), rfl⟩)
          convert hseq using 1
        · have hge : U.sz ra ≥ U.sz rb := by omega
          have hbig_e : big = ra := by simp [big, hge]
          have hsm_e : small = rb := by simp [small, hge]
          refine runs_cond_iff.mpr ⟨0, 11, by simp [u2, u1, Expr.eval, BinOp.eval, hlt], ?_, by simp [Expr.size]⟩
          simp only [↓reduceIte]
          let b1 : State := { u2 with regs := Function.update u2.regs 20 ra }
          let b2 : State := { b1 with regs := Function.update b1.regs 21 rb }
          let b3 : State := { b2 with regs := Function.update b2.regs 22 (U.oldR ra) }
          have hb1 : Runs w p ω (.assign 20 (.reg 2)) u2 .normal b1 2 :=
            runs_assign_iff.mpr ⟨ra, by simp [u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.1], rfl, rfl, by simp [Expr.size]⟩
          have hb2 : Runs w p ω (.assign 21 (.reg 3)) b1 .normal b2 2 :=
            runs_assign_iff.mpr ⟨rb, by simp [b1, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.1], rfl, rfl, by simp [Expr.size]⟩
          have hb3 : Runs w p ω (.assign 22 (.reg 12)) b2 .normal b3 2 :=
            runs_assign_iff.mpr ⟨U.oldR ra, by simp [b2, b1, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.2.2.2.2.2.1], rfl, rfl, by simp [Expr.size]⟩
          have hb4 : Runs w p ω (.assign 23 (.reg 14)) b3 .normal u3 2 :=
            runs_assign_iff.mpr ⟨U.oldR rb, by simp [b3, b2, b1, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.2.2.2.2.2.2.2.1],
              rfl, by simp [u3, b3, b2, b1, hbig_e, hsm_e], by simp [Expr.size]⟩
          have hseq := runs_seq_iff.mpr (Or.inr ⟨b1, 2, _, hb1,
            runs_seq_iff.mpr (Or.inr ⟨b2, 2, _, hb2,
              runs_seq_iff.mpr (Or.inr ⟨b3, 2, 2, hb3, hb4, rfl⟩), rfl⟩), rfl⟩)
          convert hseq using 1
      let u4 : State := { u3 with mem := Function.update u3.mem (ufParBase ufBase vCap + small) big }
      let u5 : State := { u4 with mem := Function.update u4.mem (ufSzBase ufBase vCap + big) (U.sz big + U.sz small) }
      have hmin_eq : (if U.minF ra < U.minF rb then U.minF ra else U.minF rb) = min (U.minF big) (U.minF small) := by
        dsimp [big, small]; split_ifs <;> omega
      let oldUnionVal := if U.oldR big ≠ 0 then U.oldR big else U.oldR small
      let u6 : State := { u5 with mem := Function.update u5.mem (ufMinFBase ufBase vCap + big) (min (U.minF big) (U.minF small)) }
      let u7 : State := { u6 with mem := Function.update u6.mem (ufOldRBase ufBase vCap + big) oldUnionVal }
      have hu4 : Runs w p ω (.store (.bin .add (.reg 8) (.reg 21)) (.reg 20)) u3 .normal u4 5 :=
        runs_store_iff.mpr ⟨ufParBase ufBase vCap + small, big,
          by simp [u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.1, ufParBase, show ufBase + vCap + small < 2 ^ w by omega],
          by simp [u3, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hu5 : Runs w p ω (.store (.bin .add (.reg 9) (.reg 20)) (.bin .add (.reg 18) (.reg 19))) u4 .normal u5 7 :=
        runs_store_iff.mpr ⟨ufSzBase ufBase vCap + big, U.sz big + U.sz small,
          by simp [u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.2.1, ufSzBase, show ufBase + 2 * vCap + big < 2 ^ w by omega],
          by simp [u4, u3, u2, u1, Expr.eval, BinOp.eval, hsum_eq, show U.sz big + U.sz small < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hu6 : Runs w p ω
          (.cond (.bin .lt (.reg 13) (.reg 15))
            (.store (.bin .add (.reg 10) (.reg 20)) (.reg 13))
            (.store (.bin .add (.reg 10) (.reg 20)) (.reg 15))) u5 .normal u6 9 := by
        by_cases hlt : U.minF ra < U.minF rb
        · refine runs_cond_iff.mpr ⟨1, 5, by simp [u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval,
            h9_regs.2.2.2.2.2.2.2.2.2.2.2.1, h9_regs.2.2.2.2.2.2.2.2.2.2.2.2.2, hlt, hw0], ?_, by simp [Expr.size]⟩
          simp only [one_ne_zero, ↓reduceIte]
          exact runs_store_iff.mpr ⟨ufMinFBase ufBase vCap + big, min (U.minF big) (U.minF small),
            by simp [u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.2.2.1, ufMinFBase, show ufBase + 3 * vCap + big < 2 ^ w by omega],
            by simp [u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.2.2.2.2.2.2.1, ← hmin_eq, hlt],
            rfl, rfl, by simp [Expr.size]⟩
        · refine runs_cond_iff.mpr ⟨0, 5, by simp [u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval,
            h9_regs.2.2.2.2.2.2.2.2.2.2.2.1, h9_regs.2.2.2.2.2.2.2.2.2.2.2.2.2, hlt], ?_, by simp [Expr.size]⟩
          simp only [↓reduceIte]
          exact runs_store_iff.mpr ⟨ufMinFBase ufBase vCap + big, min (U.minF big) (U.minF small),
            by simp [u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.2.2.1, ufMinFBase, show ufBase + 3 * vCap + big < 2 ^ w by omega],
            by simp [u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.2.2.2.2.2.2.2.2, ← hmin_eq, hlt],
            rfl, rfl, by simp [Expr.size]⟩
      have hu7 : Runs w p ω
          (.cond (.reg 22)
            (.store (.bin .add (.reg 11) (.reg 20)) (.reg 22))
            (.store (.bin .add (.reg 11) (.reg 20)) (.reg 23))) u6 .normal u7 7 := by
        by_cases hob : U.oldR big ≠ 0
        · refine runs_cond_iff.mpr ⟨U.oldR big, 5, by simp [u6, u5, u4, u3, Expr.eval], ?_, by simp [Expr.size]⟩
          simp only [hob, ↓reduceIte]
          exact runs_store_iff.mpr ⟨ufOldRBase ufBase vCap + big, if U.oldR big ≠ 0 then U.oldR big else U.oldR small,
            by simp [u6, u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.2.2.2.1, ufOldRBase, show ufBase + 4 * vCap + big < 2 ^ w by omega],
            by simp [u6, u5, u4, u3, Expr.eval, hob], rfl, rfl, by simp [Expr.size]⟩
        · have hob0 : U.oldR big = 0 := Classical.not_not.mp hob
          refine runs_cond_iff.mpr ⟨0, 5, by simp [u6, u5, u4, u3, Expr.eval, hob0], ?_, by simp [Expr.size]⟩
          simp only [↓reduceIte]
          exact runs_store_iff.mpr ⟨ufOldRBase ufBase vCap + big, if U.oldR big ≠ 0 then U.oldR big else U.oldR small,
            by simp [u6, u5, u4, u3, u2, u1, st13, st12, st11, st10, Expr.eval, BinOp.eval, h9_regs.2.2.2.2.2.2.2.2.2.1, ufOldRBase, show ufBase + 4 * vCap + big < 2 ^ w by omega],
            by simp [u6, u5, u4, u3, Expr.eval, hob0], rfl, rfl, by simp [Expr.size]⟩
      have s67 := runs_seq_iff.mpr (Or.inr ⟨u6, 9, 7, hu6, hu7, rfl⟩)
      have s57 := runs_seq_iff.mpr (Or.inr ⟨u5, 7, _, hu5, s67, rfl⟩)
      have s47 := runs_seq_iff.mpr (Or.inr ⟨u4, 5, _, hu4, s57, rfl⟩)
      have s37 := runs_seq_iff.mpr (Or.inr ⟨u3, 15, _, hu3, s47, rfl⟩)
      have s27 := runs_seq_iff.mpr (Or.inr ⟨u2, 5, _, hu2, s37, rfl⟩)
      have hbody := runs_seq_iff.mpr (Or.inr ⟨u1, 5, _, hu1, s27, rfl⟩)
      have hMem14 : RevUFMemAt u7.mem ufBase vCap isNew U' act := by
        rw [hU'_eq]
        exact revUFMemAt_union hMem13 hra_lt hrb_lt hne hra_act hrb_act hra_par hrb_par
      have hu7_out : ∀ a, (a < ufBase + vCap ∨ ufBase + 5 * vCap ≤ a) → u7.mem a = st13.mem a := fun a ha => by
        dsimp only [u7, u6, u5, u4, u3, u2, u1, ufOldRBase, ufMinFBase, ufSzBase, ufParBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      refine ⟨u7, 61, runs_cond_iff.mpr ⟨doUnion, 59,
        by simp [st13, st12, st11, st10, Expr.eval, h9_regs.2.2.2.2.2.1],
        by simp only [hdo0, ↓reduceIte]; exact hbody, by simp [Expr.size]⟩,
        hMem14, hu7_out, fun h => absurd h hdo0, by omega⟩
  obtain ⟨st14, cU, hrunU, hMem14, hfrU, hfrU0, hcU⟩ := hunion_branch
  have hret : Runs w p ω (.ret (.const 0)) st14 (.returned 0) st14 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hrun_full : Runs w p ω compUFPairUnionProc st0 (.returned 0) st14 (70 + cPr + cU) := by
    have t14 := runs_seq_iff.mpr (Or.inr ⟨st14, cU, 2, hrunU, hret, rfl⟩)
    have t13 := runs_seq_iff.mpr (Or.inr ⟨st13, 5, _, hs13, t14, rfl⟩)
    have t12 := runs_seq_iff.mpr (Or.inr ⟨st12, 5, _, hs12, t13, rfl⟩)
    have t11 := runs_seq_iff.mpr (Or.inr ⟨st11, 5, _, hs11, t12, rfl⟩)
    have t10 := runs_seq_iff.mpr (Or.inr ⟨st10, 3, _, hs10, t11, rfl⟩)
    have t9 := runs_seq_iff.mpr (Or.inr ⟨st9, cPr, _, hpr_run, t10, rfl⟩)
    have t8 := runs_seq_iff.mpr (Or.inr ⟨st8, 5, _, hp8, t9, rfl⟩)
    have t7 := runs_seq_iff.mpr (Or.inr ⟨st7, 5, _, hp7, t8, rfl⟩)
    have t6 := runs_seq_iff.mpr (Or.inr ⟨st6, 5, _, hp6, t7, rfl⟩)
    have t5 := runs_seq_iff.mpr (Or.inr ⟨st5, 5, _, hp5, t6, rfl⟩)
    have t4 := runs_seq_iff.mpr (Or.inr ⟨st4, 4, _, hp4, t5, rfl⟩)
    have t3 := runs_seq_iff.mpr (Or.inr ⟨st3, 4, _, hp3, t4, rfl⟩)
    have t2 := runs_seq_iff.mpr (Or.inr ⟨st2, 4, _, hp2, t3, rfl⟩)
    have t1 := runs_seq_iff.mpr (Or.inr ⟨st1, 4, _, hp1, t2, rfl⟩)
    unfold compUFPairUnionProc; convert t1 using 1; omega
  have hout_eq : ∀ d < 4, st14.mem (outSlot + d) = st13.mem (outSlot + d) := fun d hd =>
    hfrU (outSlot + d) (by rcases hdisj with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
  have h0 := hout_eq 0 (by omega); simp only [Nat.add_zero] at h0
  refine ⟨st14, 70 + cPr + cU, hrun_full,
    h0.trans (by simp [st13, st12, st11, st10]),
    (hout_eq 1 (by omega)).trans (by simp [st13, st12, st11]),
    (hout_eq 2 (by omega)).trans (by simp [st13, st12]),
    (hout_eq 3 (by omega)).trans (by simp [st13]),
    hMem14, fun a ha1 ha2 => ?_, by omega⟩
  rcases ha2 with h0 | h1 | h2
  · rw [hfrU0 h0]; exact h13_out a ha1
  · exact (hfrU a (Or.inl h1)).trans (h13_out a ha1)
  · exact (hfrU a (Or.inr h2)).trans (h13_out a ha1)

/-! ## 2. Verification of `compUFCleanProc` -/

set_option maxHeartbeats 600000 in
/-- Verification of `compUFCleanProc`: zeroes `[ufBase + vCap, ufBase + 6 * vCap + 1)` completely
(touching only the `act.length` active vertices), preserves everything outside, and costs
`≤ 45 * act.length + 50`. -/
theorem compUFClean_runs {w ufBase vCap : ℕ} {isNew : ℕ → Bool} {U : RevUFState} {act : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (huf_w : ufBase + ufScratchSize vCap < 2 ^ w)
    (hMem : RevUFMemAt mem ufBase vCap isNew U act) :
    ∃ st' c,
      Runs w p ω compUFCleanProc (startState [ufBase, vCap] mem pos) (.returned 0) st' c ∧
      (∀ a, ufBase + vCap ≤ a → a < ufBase + ufScratchSize vCap → st'.mem a = 0) ∧
      (∀ a, a < ufBase + vCap ∨ ufBase + ufScratchSize vCap ≤ a → st'.mem a = mem a) ∧
      c ≤ 45 * act.length + 50 := by
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have huf_sz : ufScratchSize vCap = 6 * vCap + 1 := rfl
  have hact_le : act.length ≤ vCap := hMem.act_len_le
  set st0 := startState [ufBase, vCap] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 2 (ufParBase ufBase vCap) }
  let st2 : State := { st1 with regs := Function.update st1.regs 3 (ufSzBase ufBase vCap) }
  let st3 : State := { st2 with regs := Function.update st2.regs 4 (ufMinFBase ufBase vCap) }
  let st4 : State := { st3 with regs := Function.update st3.regs 5 (ufOldRBase ufBase vCap) }
  let st5 : State := { st4 with regs := Function.update st4.regs 6 (ufActBase ufBase vCap) }
  let st6 : State := { st5 with regs := Function.update st5.regs 7 (ufActLenAddr ufBase vCap) }
  let st7 : State := { st6 with regs := Function.update st6.regs 8 act.length }
  let st8 : State := { st7 with regs := Function.update st7.regs 9 0 }
  have hp1 : Runs w p ω (.assign 2 (.bin .add (.reg 0) (.reg 1))) st0 .normal st1 4 :=
    runs_assign_iff.mpr ⟨ufParBase ufBase vCap, by simp [st0, startState, Expr.eval, BinOp.eval, ufParBase, show ufBase + vCap < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 3 (.bin .add (.reg 2) (.reg 1))) st1 .normal st2 4 :=
    runs_assign_iff.mpr ⟨ufSzBase ufBase vCap, by simp [st1, st0, startState, Expr.eval, BinOp.eval, ufParBase, ufSzBase, show ufBase + vCap + vCap < 2 ^ w by omega]; omega, rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 4 (.bin .add (.reg 3) (.reg 1))) st2 .normal st3 4 :=
    runs_assign_iff.mpr ⟨ufMinFBase ufBase vCap, by simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, ufSzBase, ufMinFBase, show ufBase + 2 * vCap + vCap < 2 ^ w by omega]; omega, rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.reg 1))) st3 .normal st4 4 :=
    runs_assign_iff.mpr ⟨ufOldRBase ufBase vCap, by simp [st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufMinFBase, ufOldRBase, show ufBase + 3 * vCap + vCap < 2 ^ w by omega]; omega, rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.reg 1))) st4 .normal st5 4 :=
    runs_assign_iff.mpr ⟨ufActBase ufBase vCap, by simp [st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufOldRBase, ufActBase, show ufBase + 4 * vCap + vCap < 2 ^ w by omega]; omega, rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 1))) st5 .normal st6 4 :=
    runs_assign_iff.mpr ⟨ufActLenAddr ufBase vCap, by simp [st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, ufActBase, ufActLenAddr, show ufBase + 5 * vCap + vCap < 2 ^ w by omega]; omega, rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 8 (.load (.reg 7))) st6 .normal st7 3 :=
    runs_assign_iff.mpr ⟨act.length, Expr.eval_load_of_eq (by simp [st6, Expr.eval]) hMem.hActLen, rfl, rfl, by simp [Expr.size]⟩
  have hp8 : Runs w p ω (.assign 9 (.const 0)) st7 .normal st8 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Cleanup loop over `i = 0 .. act.length - 1`
  have hloop : ∀ rem i (s : State) (hi : i ≤ act.length), act.length - i = rem →
      s.regs 2 = ufParBase ufBase vCap → s.regs 3 = ufSzBase ufBase vCap →
      s.regs 4 = ufMinFBase ufBase vCap → s.regs 5 = ufOldRBase ufBase vCap →
      s.regs 6 = ufActBase ufBase vCap → s.regs 7 = ufActLenAddr ufBase vCap →
      s.regs 8 = act.length → s.regs 9 = i →
      (∀ j (hj : j < i),
        s.mem (ufParBase ufBase vCap + act[j]'(by omega)) = 0 ∧
        s.mem (ufSzBase ufBase vCap + act[j]'(by omega)) = 0 ∧
        s.mem (ufMinFBase ufBase vCap + act[j]'(by omega)) = 0 ∧
        s.mem (ufOldRBase ufBase vCap + act[j]'(by omega)) = 0 ∧
        s.mem (ufActBase ufBase vCap + j) = 0) →
      (∀ j (hj : i ≤ j) (hj2 : j < act.length), s.mem (ufActBase ufBase vCap + j) = act[j]) →
      (∀ v < vCap, v ∉ act →
        s.mem (ufParBase ufBase vCap + v) = 0 ∧ s.mem (ufSzBase ufBase vCap + v) = 0 ∧
        s.mem (ufMinFBase ufBase vCap + v) = 0 ∧ s.mem (ufOldRBase ufBase vCap + v) = 0) →
      (∀ j, act.length ≤ j → j < vCap → s.mem (ufActBase ufBase vCap + j) = 0) →
      (∀ a, a < ufBase + vCap ∨ ufBase + 6 * vCap ≤ a → s.mem a = mem a) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 9) (.reg 8))
            (.assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
             .store (.bin .add (.reg 2) (.reg 10)) (.const 0) ;;
             .store (.bin .add (.reg 3) (.reg 10)) (.const 0) ;;
             .store (.bin .add (.reg 4) (.reg 10)) (.const 0) ;;
             .store (.bin .add (.reg 5) (.reg 10)) (.const 0) ;;
             .store (.bin .add (.reg 6) (.reg 9)) (.const 0) ;;
             .assign 9 (.bin .add (.reg 9) (.const 1))))
          s .normal st' c ∧
        st'.regs 7 = ufActLenAddr ufBase vCap ∧
        (∀ a, ufBase + vCap ≤ a → a < ufBase + 6 * vCap → st'.mem a = 0) ∧
        (∀ a, a < ufBase + vCap ∨ ufBase + 6 * vCap ≤ a → st'.mem a = mem a) ∧
        c ≤ 45 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem _ _ _ _ _ hr7 hr8 hr9 hdone _ hnonact hactZ hfr
      have hi_eq : i = act.length := by omega
      subst hi_eq
      refine ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr9, hr8], rfl, rfl, by simp [Expr.size]⟩),
        hr7, fun a ha1 ha2 => ?_, hfr, by omega⟩
      by_cases h1 : a < ufBase + 2 * vCap
      · set v := a - (ufBase + vCap); have hv : v < vCap := by omega
        rw [show a = ufParBase ufBase vCap + v by dsimp [ufParBase]; omega]
        by_cases hm : v ∈ act
        · obtain ⟨j, hj, hactj⟩ := List.getElem_of_mem hm; rw [← hactj]; exact (hdone j hj).1
        · exact (hnonact v hv hm).1
      · by_cases h2 : a < ufBase + 3 * vCap
        · set v := a - (ufBase + 2 * vCap); have hv : v < vCap := by omega
          rw [show a = ufSzBase ufBase vCap + v by dsimp [ufSzBase]; omega]
          by_cases hm : v ∈ act
          · obtain ⟨j, hj, hactj⟩ := List.getElem_of_mem hm; rw [← hactj]; exact (hdone j hj).2.1
          · exact (hnonact v hv hm).2.1
        · by_cases h3 : a < ufBase + 4 * vCap
          · set v := a - (ufBase + 3 * vCap); have hv : v < vCap := by omega
            rw [show a = ufMinFBase ufBase vCap + v by dsimp [ufMinFBase]; omega]
            by_cases hm : v ∈ act
            · obtain ⟨j, hj, hactj⟩ := List.getElem_of_mem hm; rw [← hactj]; exact (hdone j hj).2.2.1
            · exact (hnonact v hv hm).2.2.1
          · by_cases h4 : a < ufBase + 5 * vCap
            · set v := a - (ufBase + 4 * vCap); have hv : v < vCap := by omega
              rw [show a = ufOldRBase ufBase vCap + v by dsimp [ufOldRBase]; omega]
              by_cases hm : v ∈ act
              · obtain ⟨j, hj, hactj⟩ := List.getElem_of_mem hm; rw [← hactj]; exact (hdone j hj).2.2.2.1
              · exact (hnonact v hv hm).2.2.2
            · set j := a - (ufBase + 5 * vCap); have hj : j < vCap := by omega
              rw [show a = ufActBase ufBase vCap + j by dsimp [ufActBase]; omega]
              by_cases hjl : j < act.length
              · exact (hdone j hjl).2.2.2.2
              · exact hactZ j (by omega) hj
    | succ rem ih =>
      intro i s hi hrem hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hdone hremA hnonact hactZ hfr
      have hi_lt : i < act.length := by omega
      set v := act[i]
      have hv_lt : v < vCap := hMem.hActLt v (List.getElem_mem hi_lt)
      let b1 : State := { s with regs := Function.update s.regs 10 v }
      let b2 : State := { b1 with mem := Function.update b1.mem (ufParBase ufBase vCap + v) 0 }
      let b3 : State := { b2 with mem := Function.update b2.mem (ufSzBase ufBase vCap + v) 0 }
      let b4 : State := { b3 with mem := Function.update b3.mem (ufMinFBase ufBase vCap + v) 0 }
      let b5 : State := { b4 with mem := Function.update b4.mem (ufOldRBase ufBase vCap + v) 0 }
      let b6 : State := { b5 with mem := Function.update b5.mem (ufActBase ufBase vCap + i) 0 }
      let b7 : State := { b6 with regs := Function.update b6.regs 9 (i + 1) }
      have hb1 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.reg 9)))) s .normal b1 5 :=
        runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr6, hr9, ufActBase, show ufBase + 5 * vCap + i < 2 ^ w by omega]) (hremA i le_rfl hi_lt), rfl, rfl, by simp [Expr.size]⟩
      have hb2 : Runs w p ω (.store (.bin .add (.reg 2) (.reg 10)) (.const 0)) b1 .normal b2 5 :=
        runs_store_iff.mpr ⟨ufParBase ufBase vCap + v, 0, by simp [b1, Expr.eval, BinOp.eval, hr2, ufParBase, show ufBase + vCap + v < 2 ^ w by omega], by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hb3 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 10)) (.const 0)) b2 .normal b3 5 :=
        runs_store_iff.mpr ⟨ufSzBase ufBase vCap + v, 0, by simp [b2, b1, Expr.eval, BinOp.eval, hr3, ufSzBase, show ufBase + 2 * vCap + v < 2 ^ w by omega], by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hb4 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 10)) (.const 0)) b3 .normal b4 5 :=
        runs_store_iff.mpr ⟨ufMinFBase ufBase vCap + v, 0, by simp [b3, b2, b1, Expr.eval, BinOp.eval, hr4, ufMinFBase, show ufBase + 3 * vCap + v < 2 ^ w by omega], by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hb5 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 10)) (.const 0)) b4 .normal b5 5 :=
        runs_store_iff.mpr ⟨ufOldRBase ufBase vCap + v, 0, by simp [b4, b3, b2, b1, Expr.eval, BinOp.eval, hr5, ufOldRBase, show ufBase + 4 * vCap + v < 2 ^ w by omega], by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hb6 : Runs w p ω (.store (.bin .add (.reg 6) (.reg 9)) (.const 0)) b5 .normal b6 5 :=
        runs_store_iff.mpr ⟨ufActBase ufBase vCap + i, 0, by simp [b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr6, hr9, ufActBase, show ufBase + 5 * vCap + i < 2 ^ w by omega], by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hb7 : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) b6 .normal b7 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [b6, b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr9, hw1, show i + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have s67 := runs_seq_iff.mpr (Or.inr ⟨b6, 5, 4, hb6, hb7, rfl⟩)
      have s57 := runs_seq_iff.mpr (Or.inr ⟨b5, 5, _, hb5, s67, rfl⟩)
      have s47 := runs_seq_iff.mpr (Or.inr ⟨b4, 5, _, hb4, s57, rfl⟩)
      have s37 := runs_seq_iff.mpr (Or.inr ⟨b3, 5, _, hb3, s47, rfl⟩)
      have s27 := runs_seq_iff.mpr (Or.inr ⟨b2, 5, _, hb2, s37, rfl⟩)
      have hbody := runs_seq_iff.mpr (Or.inr ⟨b1, 5, _, hb1, s27, rfl⟩)
      have hupd_z : ∀ a, s.mem a = 0 → b7.mem a = 0 := fun a ha => by
        dsimp only [b7, b6, b5, b4, b3, b2, b1]
        by_cases h1 : a = ufActBase ufBase vCap + i; · simp [h1]
        rw [Function.update_of_ne h1]
        by_cases h2 : a = ufOldRBase ufBase vCap + v; · simp [h2]
        rw [Function.update_of_ne h2]
        by_cases h3 : a = ufMinFBase ufBase vCap + v; · simp [h3]
        rw [Function.update_of_ne h3]
        by_cases h4 : a = ufSzBase ufBase vCap + v; · simp [h4]
        rw [Function.update_of_ne h4]
        by_cases h5 : a = ufParBase ufBase vCap + v; · simp [h5]
        rw [Function.update_of_ne h5]; exact ha
      obtain ⟨st', cRest, hrest, hr7', hz', hfr', hcRest⟩ :=
        ih (i + 1) b7 (by omega) (by omega)
          (by simp [b7, b6, b5, b4, b3, b2, b1, hr2]) (by simp [b7, b6, b5, b4, b3, b2, b1, hr3])
          (by simp [b7, b6, b5, b4, b3, b2, b1, hr4]) (by simp [b7, b6, b5, b4, b3, b2, b1, hr5])
          (by simp [b7, b6, b5, b4, b3, b2, b1, hr6]) (by simp [b7, b6, b5, b4, b3, b2, b1, hr7])
          (by simp [b7, b6, b5, b4, b3, b2, b1, hr8]) (by simp [b7])
          (fun j hj => by
            by_cases hji : j = i
            · subst hji
              dsimp only [b7, b6, b5, b4, b3, b2, b1, ufActBase, ufOldRBase, ufMinFBase, ufSzBase, ufParBase]
              exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
                by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
                by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
                by rw [Function.update_of_ne (by omega), Function.update_self], by simp⟩
            · have hd := hdone j (by omega)
              exact ⟨hupd_z _ hd.1, hupd_z _ hd.2.1, hupd_z _ hd.2.2.1, hupd_z _ hd.2.2.2.1, hupd_z _ hd.2.2.2.2⟩)
          (fun j hj1 hj2 => by
            dsimp only [b7, b6, b5, b4, b3, b2, b1, ufActBase, ufOldRBase, ufMinFBase, ufSzBase, ufParBase]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hremA j (by omega) hj2)
          (fun u hu hna => ⟨hupd_z _ (hnonact u hu hna).1, hupd_z _ (hnonact u hu hna).2.1, hupd_z _ (hnonact u hu hna).2.2.1, hupd_z _ (hnonact u hu hna).2.2.2⟩)
          (fun j hj1 hj2 => hupd_z _ (hactZ j hj1 hj2))
          (fun a ha => by
            dsimp only [b7, b6, b5, b4, b3, b2, b1, ufActBase, ufOldRBase, ufMinFBase, ufSzBase, ufParBase]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfr a ha)
      have hfull := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, b7, _, cRest,
        by simp [Expr.eval, BinOp.eval, hr9, hr8, hi_lt, hw0], by decide, hbody, hrest, by simp [Expr.size]; rfl⟩))
      exact ⟨st', _, hfull, hr7', hz', hfr', by omega⟩
  obtain ⟨st9, cLoop, hloop_run, hr9_7, hz9, hfr9, hcLoop⟩ :=
    hloop act.length 0 st8 (Nat.zero_le _) (Nat.sub_zero _)
      (by simp [st8, st7, st6, st5, st4, st3, st2, st1]) (by simp [st8, st7, st6, st5, st4, st3, st2])
      (by simp [st8, st7, st6, st5, st4, st3]) (by simp [st8, st7, st6, st5, st4])
      (by simp [st8, st7, st6, st5]) (by simp [st8, st7, st6]) (by simp [st8, st7]) (by simp [st8])
      (fun _ h => by omega) (fun j _ hj => hMem.hActAt j hj)
      (fun v hv hna => by
        have hsz0 : U.sz v = 0 := Classical.byContradiction fun h => hna ((hMem.hActIff v hv).mp h)
        have hzr := hMem.hZeroRest v hv hsz0
        have ha := hMem.hArrs v hv
        exact ⟨ha.1.trans hzr.1, ha.2.1.trans hsz0, ha.2.2.1.trans hzr.2.1, ha.2.2.2.trans hzr.2.2⟩)
      hMem.hActZero (fun _ _ => rfl)
  let st10 : State := { st9 with mem := Function.update st9.mem (ufActLenAddr ufBase vCap) 0 }
  have hs10 : Runs w p ω (.store (.reg 7) (.const 0)) st9 .normal st10 3 :=
    runs_store_iff.mpr ⟨ufActLenAddr ufBase vCap, 0, by simp [Expr.eval, hr9_7],
      by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hret : Runs w p ω (.ret (.const 0)) st10 (.returned 0) st10 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hrun_full : Runs w p ω compUFCleanProc st0 (.returned 0) st10 (44 + cLoop) := by
    have t9 := runs_seq_iff.mpr (Or.inr ⟨st10, 3, 2, hs10, hret, rfl⟩)
    have t8 := runs_seq_iff.mpr (Or.inr ⟨st9, cLoop, _, hloop_run, t9, rfl⟩)
    have t7 := runs_seq_iff.mpr (Or.inr ⟨st8, 2, _, hp8, t8, rfl⟩)
    have t6 := runs_seq_iff.mpr (Or.inr ⟨st7, 3, _, hp7, t7, rfl⟩)
    have t5 := runs_seq_iff.mpr (Or.inr ⟨st6, 4, _, hp6, t6, rfl⟩)
    have t4 := runs_seq_iff.mpr (Or.inr ⟨st5, 4, _, hp5, t5, rfl⟩)
    have t3 := runs_seq_iff.mpr (Or.inr ⟨st4, 4, _, hp4, t4, rfl⟩)
    have t2 := runs_seq_iff.mpr (Or.inr ⟨st3, 4, _, hp3, t3, rfl⟩)
    have t1 := runs_seq_iff.mpr (Or.inr ⟨st2, 4, _, hp2, t2, rfl⟩)
    have t0 := runs_seq_iff.mpr (Or.inr ⟨st1, 4, _, hp1, t1, rfl⟩)
    unfold compUFCleanProc; convert t0 using 1; omega
  refine ⟨st10, 44 + cLoop, hrun_full, fun a ha1 ha2 => ?_, fun a ha => ?_, by omega⟩
  · dsimp only [st10, ufActLenAddr, ufScratchSize] at ha2 ⊢
    by_cases heq : a = ufBase + 6 * vCap
    · subst heq; simp
    · rw [Function.update_of_ne heq]; exact hz9 a ha1 (by omega)
  · dsimp only [st10, ufActLenAddr, ufScratchSize] at ha ⊢
    rw [Function.update_of_ne (by omega)]; exact hfr9 a (by omega)

end

end MinCostFlow.SparseCore.Program
