module

public import MinCostFlow.ExpanderDecomp.OuterProgMatchingBase
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Verification of `buildInjPairProc` (`OuterProgMatchingInj`)

Proves `buildInjPairProc_spec` using the definitions and list/finset bridges from
`OuterProgMatchingBase.lean`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 6. Verification of `buildInjPairProc` -/

private lemma injScan_triple {w e flagAddr aBase : ℕ}
    (pProg : Program) (st₀ : State) (S : Finset ℕ)
    (h4 : st₀.regs 4 = flagAddr) (h5 : st₀.regs 5 = 2 * e) (h9 : st₀.regs 9 = aBase)
    (hflag : ∀ p < 2 * e, st₀.mem (flagAddr + p) = 0 ↔ p ∉ S)
    (hdAF : DisjointRange aBase (2 * e) flagAddr (2 * e))
    (hwF : flagAddr + 2 * e < 2 ^ w) (hwA : aBase + 2 * e < 2 ^ w) (hwE : 4 * e + 16 < 2 ^ w) :
    let aList := (List.range (2 * e)).filter fun p => decide (p ∉ S)
    Triple w pProg (fun s => s = st₀) injScanStmt
      (normalPost fun s' =>
        s'.regs 11 = aList.length ∧
        ListAt s'.mem aBase aList ∧
        (∀ a, a < aBase ∨ aBase + aList.length ≤ a → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≤ 6 ∨ r = 9 ∨ r = 10 → s'.regs r = st₀.regs r))
      (fun _ => 90 * e + 30) := by
  intro aList s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [injScanStmt]
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st1 : State := { st₀ with regs := Function.update st₀.regs 11 0 }
  have hloop := Triple.forRange_const (p := pProg) (r := 7) (lo := .const 0) (hi := .reg 5)
    (body :=
      .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
      .cond (.bin .eq (.reg 8) (.const 0))
        (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
         .assign 11 (.bin .add (.reg 11) (.const 1)))
        .nop)
    (P := fun s => s = st1)
    (Inv := fun i s =>
      let cur := (List.range i).filter fun p => decide (p ∉ S)
      s.regs 7 = i ∧
      s.regs 11 = cur.length ∧
      ListAt s.mem aBase cur ∧
      (∀ a, a < aBase ∨ aBase + cur.length ≤ a → s.mem a = st₀.mem a) ∧
      (∀ r, r ≤ 6 ∨ r = 9 ∨ r = 10 → s.regs r = st₀.regs r))
    32 0 (2 * e) (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp, by simp [st1],
        fun j hj => by simp at hj, fun _ _ => rfl,
        fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 7),
          Function.update_of_ne (by omega : r ≠ 11)]⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr5 : s.regs 5 = 2 * e := by rw [hi.2.2.2.2 5 (by omega), h5]
      simp [Expr.eval, hr5])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, h11, hL, hfr, hkr⟩
      set cur := (List.range i).filter fun p => decide (p ∉ S)
      have hcur_le : cur.length ≤ i :=
        (List.length_filter_le _ _).trans (by simp)
      have hmF : s.mem (flagAddr + i) = st₀.mem (flagAddr + i) :=
        hfr _ (Or.elim hdAF (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
      have hr4 : s.regs 4 = flagAddr := by rw [hkr 4 (by omega), h4]
      have hr9 : s.regs 9 = aBase := by rw [hkr 9 (by omega), h9]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := st₀.mem (flagAddr + i))
        (by simp [Expr.eval, BinOp.eval, hr4, hiReg, (by omega : flagAddr + i < 2 ^ w), hmF]) ?_
      let stA : State := { s with regs := Function.update s.regs 8 (st₀.mem (flagAddr + i)) }
      have hA_r : ∀ r, r ≠ 8 → stA.regs r = s.regs r :=
        fun r hr => Function.update_of_ne hr _ _
      by_cases hiS : i ∈ S
      · have hmv : st₀.mem (flagAddr + i) ≠ 0 := fun h => ((hflag i hilt).mp h) hiS
        have hcur' : (List.range (i + 1)).filter (fun p => decide (p ∉ S)) = cur := by
          rw [List.range_succ, List.filter_append]; simp [cur, hiS]
        refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨0, 1,
            by simp [Expr.eval, BinOp.eval, stA, hmv, (by omega : 0 < 2 ^ w)],
            by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp,
          by rw [hcur']; dsimp only; rw [Function.update_of_ne (by decide), hA_r 11 (by omega), h11],
          by rw [hcur']; exact hL,
          by rw [hcur']; exact hfr, fun r hr => by
            simp [Function.update_of_ne (by omega : r ≠ 7), hA_r r (by omega), hkr r hr]⟩,
          by rw [hA_r 7 (by omega), hiReg]⟩
      · have hmv : st₀.mem (flagAddr + i) = 0 := (hflag i hilt).mpr hiS
        let memB := Function.update s.mem (aBase + cur.length) i
        let stB : State := { stA with mem := memB }
        let stC : State := { stB with regs := Function.update stB.regs 11 (cur.length + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7)) stA .normal stB 5 := by
          rw [runs_store_iff]
          exact ⟨aBase + cur.length, i,
            by simp [Expr.eval, BinOp.eval, hA_r 9 (by omega), hr9, hA_r 11 (by omega), h11,
                 (by omega : aBase + cur.length < 2 ^ w)],
            by simp [Expr.eval, hA_r 7 (by omega), hiReg], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.assign 11 (.bin .add (.reg 11) (.const 1))) stB .normal stC 4 := by
          rw [runs_assign_iff]
          exact ⟨cur.length + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_r 11 (by omega), h11, hw1,
                 (by omega : cur.length + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        have hcur' : (List.range (i + 1)).filter (fun p => decide (p ∉ S)) = cur ++ [i] := by
          rw [List.range_succ, List.filter_append]; simp [cur, hiS]
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨1, 10,
            by simp [Expr.eval, BinOp.eval, stA, hmv, hw1, (by omega : 0 < 2 ^ w)],
            by simp only [one_ne_zero, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp,
          by rw [hcur', List.length_append, List.length_singleton]
             dsimp only [stC]; rw [Function.update_of_ne (by decide), Function.update_self], ?_, ?_, fun r hr => by
            simp [stC, stB, Function.update_of_ne (by omega : r ≠ 7),
              Function.update_of_ne (by omega : r ≠ 11), hA_r r (by omega), hkr r hr]⟩,
          by simp [stC, stB, hA_r 7 (by omega), hiReg]⟩
        · rw [hcur']; simpa [stC, stB, memB] using hL.snoc i
        · intro a ha; rw [hcur', List.length_append, List.length_singleton] at ha
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (by omega)]
          exact hfr a (by omega))
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_11, h2_L, h2_fr, h2_kr⟩
      exact ⟨h2_11, h2_L, h2_fr, h2_kr⟩)
    (by simp [Expr.size]; omega)

private lemma injCopy_triple {w kS sAddr bBase : ℕ}
    (pProg : Program) (st₀ : State) (sList : List ℕ)
    (h1 : st₀.regs 1 = kS) (h2 : st₀.regs 2 = sAddr) (h10 : st₀.regs 10 = bBase)
    (hlen : sList.length = kS) (hL : ListAt st₀.mem sAddr sList)
    (hdBS : DisjointRange bBase kS sAddr kS)
    (hwS : sAddr + kS < 2 ^ w) (hwB : bBase + kS < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) injCopyStmt
      (normalPost fun s' =>
        ListAt s'.mem bBase sList ∧
        (∀ a, a < bBase ∨ bBase + kS ≤ a → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≠ 7 → r ≠ 8 → s'.regs r = st₀.regs r))
      (fun _ => 30 * kS + 20) := by
  intro s ω hs; subst s
  have hloop := Triple.forRange_const (p := pProg) (r := 7) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 8 (.load (.bin .add (.reg 2) (.reg 7))) ;;
      .store (.bin .add (.reg 10) (.reg 7)) (.reg 8))
    (P := fun s => s = st₀)
    (Inv := fun i s =>
      s.regs 7 = i ∧
      ListAt s.mem bBase (sList.take i) ∧
      (∀ a, a < bBase ∨ bBase + i ≤ a → s.mem a = st₀.mem a) ∧
      (∀ r, r ≠ 7 → r ≠ 8 → s.regs r = st₀.regs r))
    20 0 kS (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun j hj => by simp at hj, fun _ _ => rfl,
        fun r hr7 _ => Function.update_of_ne hr7 _ _⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr1 : s.regs 1 = kS := by rw [hi.2.2.2 1 (by omega) (by omega), h1]
      simp [Expr.eval, hr1])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hLB, hfr, hkr⟩
      have hiLen : i < sList.length := by omega
      have hms : s.mem (sAddr + i) = sList[i]'hiLen := by
        rw [hfr _ (Or.elim hdBS (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hL i hiLen
      have hr2 : s.regs 2 = sAddr := by rw [hkr 2 (by omega) (by omega), h2]
      have hr10 : s.regs 10 = bBase := by rw [hkr 10 (by omega) (by omega), h10]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := sList[i]'hiLen)
        (by simp [Expr.eval, BinOp.eval, hr2, hiReg, (by omega : sAddr + i < 2 ^ w), hms]) ?_
      let stA : State := { s with regs := Function.update s.regs 8 (sList[i]'hiLen) }
      let stB : State := { stA with mem := Function.update s.mem (bBase + i) (sList[i]'hiLen) }
      refine ⟨.normal, stB, 5, runs_store_iff.mpr ⟨bBase + i, sList[i]'hiLen,
          by simp [Expr.eval, BinOp.eval, stA, hr10, hiReg, (by omega : bBase + i < 2 ^ w)],
          by simp [Expr.eval, stA], rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
      refine ⟨⟨by simp, ?_, ?_, fun r hr7 hr8 => by
          simp [stB, stA, Function.update_of_ne hr7, Function.update_of_ne hr8, hkr r hr7 hr8]⟩,
        by simp [stB, stA, hiReg]⟩
      · rw [List.take_succ_eq_append_getElem hiLen]
        have htlen : (sList.take i).length = i := by rw [List.length_take]; omega
        simpa [stB, htlen] using hLB.snoc (sList[i]'hiLen)
      · intro a ha; dsimp only [stB]
        rw [Function.update_of_ne (by omega)]
        exact hfr a (by omega))
  refine runs_start_le ?_
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_L, h2_fr, h2_kr⟩
      have htake : sList.take kS = sList := by rw [← hlen, List.take_length]
      rw [htake] at h2_L
      exact ⟨h2_L, h2_fr, h2_kr⟩)
    (by simp [Expr.size]; omega)

private lemma injHeader_triple {w e kS outPairsAddr : ℕ}
    (pProg : Program) (st₀ : State)
    (h1 : st₀.regs 1 = kS) (h3 : st₀.regs 3 = outPairsAddr) (h6 : st₀.regs 6 = 2 * e - kS)
    (hkS_le : kS ≤ 2 * e) (hwP : outPairsAddr + 3 + 2 * e < 2 ^ w) (hwE : 4 * e + 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀)
      (.store (.reg 3) (.const 1) ;;
       .store (.bin .add (.reg 3) (.const 1)) (.reg 6) ;;
       .store (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 6)) (.reg 1) ;;
       .assign 9 (.bin .add (.reg 3) (.const 2)) ;;
       .assign 10 (.bin .add (.bin .add (.reg 3) (.const 3)) (.reg 6)))
      (normalPost fun s' =>
        s'.mem outPairsAddr = 1 ∧
        s'.mem (outPairsAddr + 1) = 2 * e - kS ∧
        s'.mem (outPairsAddr + 2 + (2 * e - kS)) = kS ∧
        (∀ a, a ≠ outPairsAddr → a ≠ outPairsAddr + 1 → a ≠ outPairsAddr + 2 + (2 * e - kS) →
          s'.mem a = st₀.mem a) ∧
        s'.regs 9 = outPairsAddr + 2 ∧
        s'.regs 10 = outPairsAddr + 3 + (2 * e - kS) ∧
        (∀ r ≤ 6, s'.regs r = st₀.regs r))
      (fun _ => 35) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_seq_store_le (x := outPairsAddr) (v := 1)
    (by simp [Expr.eval, h3]) (by simp [Expr.eval, hw1]) ?_
  refine runs_seq_store_le (x := outPairsAddr + 1) (v := 2 * e - kS)
    (by simp [Expr.eval, BinOp.eval, h3, hw1, (by omega : outPairsAddr + 1 < 2 ^ w)])
    (by simp [Expr.eval, h6]) ?_
  refine runs_seq_store_le (x := outPairsAddr + 2 + (2 * e - kS)) (v := kS)
    (by simp [Expr.eval, BinOp.eval, h3, h6, hw2, (by omega : outPairsAddr + 2 < 2 ^ w),
          (by omega : outPairsAddr + 2 + (2 * e - kS) < 2 ^ w)])
    (by simp [Expr.eval, h1]) ?_
  refine runs_seq_assign_le (v := outPairsAddr + 2)
    (by simp [Expr.eval, BinOp.eval, h3, hw2, (by omega : outPairsAddr + 2 < 2 ^ w)]) ?_
  let stA : State := {
    mem := Function.update (Function.update (Function.update st₀.mem outPairsAddr 1)
      (outPairsAddr + 1) (2 * e - kS)) (outPairsAddr + 2 + (2 * e - kS)) kS
    regs := Function.update st₀.regs 9 (outPairsAddr + 2)
    pos := st₀.pos }
  let stB : State := { stA with regs := Function.update stA.regs 10 (outPairsAddr + 3 + (2 * e - kS)) }
  refine ⟨.normal, stB, 6, runs_assign_iff.mpr ⟨outPairsAddr + 3 + (2 * e - kS),
      by simp [Expr.eval, BinOp.eval, stA, h3, h6, hw3, (by omega : outPairsAddr + 3 < 2 ^ w),
           (by omega : outPairsAddr + 3 + (2 * e - kS) < 2 ^ w)],
      rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
  refine ⟨?_, ?_, ?_, ?_, by simp [stB, stA], by simp [stB], fun r hr => by
    simp [stB, stA, Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 9)]⟩
  · simp [stB, stA, Function.update_of_ne (by omega : outPairsAddr ≠ outPairsAddr + 2 + (2 * e - kS)),
      Function.update_of_ne (by omega : outPairsAddr ≠ outPairsAddr + 1)]
  · simp [stB, stA, Function.update_of_ne (by omega : outPairsAddr + 1 ≠ outPairsAddr + 2 + (2 * e - kS))]
  · simp [stB, stA]
  · intro a h1 h2 h3
    simp [stB, stA, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]

/-- Specification of `buildInjPairProc`. -/
theorem buildInjPairProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [buildInjPairProc]) :
    MeetsContract w pProg b (buildInjPairContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨e, kS, sAddr, outPairsAddr, h, sList, rfl, hlenS, hndS, hs_lt,
    hlistS, hzero, hsH, hpH, hdPS, hwH, hwE⟩
  unfold buildInjPairSpace at hwH
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  set V := Finset.range (2 * e)
  set S := sList.toFinset
  have hS_sub : S ⊆ V := fun p hp => Finset.mem_range.mpr (hs_lt p (List.mem_toFinset.mp hp))
  have hS_card : S.card = kS := by rw [List.toFinset_card_of_nodup hndS, hlenS]
  have hkS_le : kS ≤ 2 * e := by
    have := Finset.card_le_card hS_sub; rw [Finset.card_range, hS_card] at this; exact this
  set A_list := (V \ S).sort (· ≤ ·)
  have hA_eq : (List.range (2 * e)).filter (fun p => decide (p ∉ S)) = A_list := by
    have h1 : (List.range (2 * e)).filter (fun p => decide (p ∉ S)) =
        (List.range (2 * e)).filter (fun p => decide (p ∈ V \ S)) := by
      apply List.filter_congr
      intro p hp
      simp [V, Finset.mem_sdiff, Finset.mem_range.mpr (List.mem_range.mp hp)]
    rw [h1]
    exact list_range_filter_eq_finset_sort Finset.sdiff_subset
  have hA_len : A_list.length = 2 * e - kS := by
    rw [Finset.length_sort]
    have := Finset.card_sdiff_add_card_eq_card hS_sub
    rw [Finset.card_range, hS_card] at this; omega
  refine runs_start_le ?_
  dsimp only [buildInjPairProc]
  refine runs_seq_assign_le (v := 2 * e)
    (by simp [Expr.eval, BinOp.eval, startState, hw2, (by omega : 2 * e < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 2 * e - kS)
    (by simp [Expr.eval, BinOp.eval, startState, (by omega : 2 * e - kS < 2 ^ w)]) ?_
  let st1 : State := { startState [e, kS, sAddr, outPairsAddr, h] mem pos with
    regs := Function.update (Function.update
      (startState [e, kS, sAddr, outPairsAddr, h] mem pos).regs 5 (2 * e)) 6 (2 * e - kS) }
  have h1_r : ∀ r ≤ 4, st1.regs r = (startState [e, kS, sAddr, outPairsAddr, h] mem pos).regs r :=
    fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 6),
      Function.update_of_ne (by omega : r ≠ 5)]
  -- Stage 1: markVertsStmt
  refine runs_seq_triple_le
    (markVerts_triple (n := 2 * e) (len := kS) (listAddr := sAddr) (locAddr := h) (val := 1)
      pProg st1 sList (by decide) (by rw [h1_r 1 (by omega)]; rfl)
      (by rw [h1_r 2 (by omega)]; rfl) (by rw [h1_r 4 (by omega)]; rfl)
      hlenS hs_lt hlistS (Or.inr hsH) (by omega) (by omega) hw1 hw1) rfl ?_
  intro st2 ⟨h2_mark, h2_fr, h2_kr⟩
  have h2_r : ∀ r ≤ 6, st2.regs r = st1.regs r := fun r hr => h2_kr r (by omega) (by omega)
  have h2_flag : ∀ p < 2 * e, st2.mem (h + p) = 0 ↔ p ∉ S := by
    intro p hp
    by_cases hpS : p ∈ S
    · have h1 := h2_mark p (List.mem_toFinset.mp hpS)
      simp [h1, hpS]
    · have h0 : st2.mem (h + p) = 0 := by
        rw [h2_fr (h + p) (fun u hu hEq => hpS (List.mem_toFinset.mpr (by
          have : u = p := by omega
          subst this; exact hu)))]
        exact hzero (h + p) (by omega)
      simp [h0, hpS]
  -- Stage 2: injHeader
  refine runs_seq_triple_le
    (injHeader_triple (e := e) (kS := kS) (outPairsAddr := outPairsAddr) pProg st2
      (by rw [h2_r 1 (by omega), h1_r 1 (by omega)]; rfl)
      (by rw [h2_r 3 (by omega), h1_r 3 (by omega)]; rfl)
      (by rw [h2_r 6 (by omega)]; simp [st1])
      hkS_le (by omega) hwE) rfl ?_
  intro st3 ⟨h3_p0, h3_p1, h3_pA, h3_fr, h3_9, h3_10, h3_r⟩
  have h3_flag : ∀ p < 2 * e, st3.mem (h + p) = 0 ↔ p ∉ S := by
    intro p hp
    rw [h3_fr (h + p) (by omega) (by omega) (by omega)]
    exact h2_flag p hp
  -- Stage 3: injScan
  refine runs_seq_triple_le
    (injScan_triple (e := e) (flagAddr := h) (aBase := outPairsAddr + 2) pProg st3 S
      (by rw [h3_r 4 (by omega), h2_r 4 (by omega), h1_r 4 (by omega)]; rfl)
      (by rw [h3_r 5 (by omega), h2_r 5 (by omega)]; simp [st1])
      h3_9 h3_flag (Or.inl (by omega)) (by omega) (by omega) hwE) rfl ?_
  intro st4 ⟨h4_11, h4_LA, h4_fr, h4_kr⟩
  rw [hA_eq] at h4_11 h4_LA h4_fr
  rw [hA_len] at h4_fr
  -- Note: st4.mem at sAddr is unchanged!
  have h4_sL : ListAt st4.mem sAddr sList := by
    intro j hj
    have hj' : j < kS := by omega
    rw [h4_fr (sAddr + j) (Or.elim hdPS (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
    rw [h3_fr (sAddr + j) (disjointRange_ne hdPS (by omega) (by omega) (by omega) (by omega)).symm
      (disjointRange_ne hdPS (by omega) (by omega) (by omega) (by omega)).symm
      (disjointRange_ne hdPS (by omega) (by omega) (by omega) (by omega)).symm]
    rw [h2_fr (sAddr + j) (fun u hu => by omega)]
    exact hlistS j hj
  -- Stage 4: injCopy
  refine runs_seq_triple_le
    (injCopy_triple (kS := kS) (sAddr := sAddr) (bBase := outPairsAddr + 3 + (2 * e - kS))
      pProg st4 sList
      (by rw [h4_kr 1 (by omega), h3_r 1 (by omega), h2_r 1 (by omega), h1_r 1 (by omega)]; rfl)
      (by rw [h4_kr 2 (by omega), h3_r 2 (by omega), h2_r 2 (by omega), h1_r 2 (by omega)]; rfl)
      (by rw [h4_kr 10 (by omega), h3_10])
      hlenS h4_sL (Or.elim hdPS (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      (by omega) (by omega) hw1) rfl ?_
  intro st5 ⟨h5_LB, h5_fr, h5_kr⟩
  -- Return h + 2 * e
  refine runs_ret_le (v := h + 2 * e)
    (by simp [Expr.eval, BinOp.eval, h5_kr 4 (by omega) (by omega), h4_kr 4 (by omega),
          h3_r 4 (by omega), h2_r 4 (by omega), h1_r 4 (by omega),
          h5_kr 5 (by omega) (by omega), h4_kr 5 (by omega), h3_r 5 (by omega),
          h2_r 5 (by omega), st1, startState, (by omega : h + 2 * e < 2 ^ w)]) ?_ ?_
  · dsimp only [buildInjPairContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadS : readList mem sAddr kS = sList := by
      rw [← hlenS]; exact readList_eq_of_listAt hlistS
    simp only [hreadS]
    refine ⟨rfl, ?_, Finset.sort_nodup _ _, by ext x; simp [A_list, Finset.mem_sort], ?_, ?_⟩
    · intro a ha
      rw [h5_fr a (Or.inr (by omega)), h4_fr a (Or.inr (by omega)),
        h3_fr a (by omega) (by omega) (by omega),
        h2_fr a (fun u hu => by have := hs_lt u hu; omega)]
      exact hzero a (by omega)
    · -- SinglePairAt
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [h5_fr outPairsAddr (Or.inl (by omega)), h4_fr outPairsAddr (Or.inl (by omega)), h3_p0]
      · rw [h5_fr (outPairsAddr + 1) (Or.inl (by omega)),
          h4_fr (outPairsAddr + 1) (Or.inl (by omega)), h3_p1, hA_len]
      · intro j hj
        have hj' : j < 2 * e - kS := by rw [← hA_len]; exact hj
        rw [h5_fr (outPairsAddr + 2 + j) (Or.inl (by omega))]
        exact h4_LA j hj
      · rw [hA_len, h5_fr (outPairsAddr + 2 + (2 * e - kS)) (Or.inl (by omega)),
          h4_fr (outPairsAddr + 2 + (2 * e - kS)) (Or.inr (by omega)), h3_pA, hlenS]
      · rw [hA_len]; exact h5_LB
    · -- Frame
      intro a haH haP
      rw [h5_fr a (by omega), h4_fr a (by omega),
        h3_fr a (by omega) (by omega) (by omega),
        h2_fr a (fun u hu => by omega)]
      rfl
  · simp only [buildInjPairContract, buildInjPairCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega


end MinCostFlow.ExpanderDecomp
