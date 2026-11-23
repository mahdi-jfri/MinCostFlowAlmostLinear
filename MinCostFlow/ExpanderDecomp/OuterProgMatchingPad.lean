module

public import MinCostFlow.ExpanderDecomp.OuterProgMatchingBase
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Verification of `padToBisectionProc` (`OuterProgMatchingPad`)

Proves `padToBisectionProc_spec` using the definitions and list/finset bridges from
`OuterProgMatchingBase.lean`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 5. Verification of `padToBisectionProc` -/

private lemma padPass1_triple {w e flagAddr aBase target : ℕ}
    (pProg : Program) (st₀ : State) (C : Finset ℕ)
    (h5 : st₀.regs 5 = 2 * e) (h4 : st₀.regs 4 = flagAddr)
    (h6 : st₀.regs 6 = target) (h9 : st₀.regs 9 = aBase)
    (hC_sub : C ⊆ Finset.range (2 * e))
    (hflag : ∀ p < 2 * e, st₀.mem (flagAddr + p) = target ↔ p ∈ C)
    (hdFA : DisjointRange aBase (2 * e) flagAddr (2 * e))
    (hwF : flagAddr + 2 * e < 2 ^ w) (hwA : aBase + 2 * e < 2 ^ w) (hwE : 4 * e + 16 < 2 ^ w) :
    let cList := (List.range (2 * e)).filter fun p => decide (p ∈ C)
    Triple w pProg (fun s => s = st₀) padPass1Stmt
      (normalPost fun s' =>
        s'.regs 11 = cList.length ∧
        ListAt s'.mem aBase cList ∧
        (∀ a, a < aBase ∨ aBase + cList.length ≤ a → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≤ 6 ∨ r = 9 ∨ r = 10 → s'.regs r = st₀.regs r))
      (fun _ => 90 * e + 30) := by
  intro cList s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [padPass1Stmt]
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st1 : State := { st₀ with regs := Function.update st₀.regs 11 0 }
  have hloop := Triple.forRange_const (p := pProg) (r := 7) (lo := .const 0) (hi := .reg 5)
    (body :=
      .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
      .cond (.bin .eq (.reg 8) (.reg 6))
        (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
         .assign 11 (.bin .add (.reg 11) (.const 1)))
        .nop)
    (P := fun s => s = st1)
    (Inv := fun i s =>
      let cur := (List.range i).filter fun p => decide (p ∈ C)
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
      set cur := (List.range i).filter fun p => decide (p ∈ C)
      have hcur_le : cur.length ≤ i := by
        have := List.length_filter_le (fun p => decide (p ∈ C)) (List.range i)
        simpa using this
      have hmF : s.mem (flagAddr + i) = st₀.mem (flagAddr + i) :=
        hfr _ (Or.elim hdFA (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
      have hr4 : s.regs 4 = flagAddr := by rw [hkr 4 (by omega), h4]
      have hr6 : s.regs 6 = target := by rw [hkr 6 (by omega), h6]
      have hr9 : s.regs 9 = aBase := by rw [hkr 9 (by omega), h9]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := st₀.mem (flagAddr + i))
        (by simp [Expr.eval, BinOp.eval, hr4, hiReg, (by omega : flagAddr + i < 2 ^ w), hmF]) ?_
      let stA : State := { s with regs := Function.update s.regs 8 (st₀.mem (flagAddr + i)) }
      have hA_r : ∀ r, r ≠ 8 → stA.regs r = s.regs r :=
        fun r hr => Function.update_of_ne hr _ _
      by_cases hiC : i ∈ C
      · have hmv : st₀.mem (flagAddr + i) = target := (hflag i hilt).mpr hiC
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
        have hcur' : (List.range (i + 1)).filter (fun p => decide (p ∈ C)) = cur ++ [i] := by
          rw [List.range_succ, List.filter_append]; simp [cur, hiC]
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨1, 10,
            by simp [Expr.eval, BinOp.eval, stA, hA_r 6 (by omega), hr6, hmv, hw1],
            by simp only [one_ne_zero, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, by simp [stC, hcur'], ?_, ?_, fun r hr => by
            simp [stC, stB, Function.update_of_ne (by omega : r ≠ 7),
              Function.update_of_ne (by omega : r ≠ 11), hA_r r (by omega), hkr r hr]⟩,
          by simp [stC, stB, hA_r 7 (by omega), hiReg]⟩
        · rw [hcur']; simpa [stC, stB, memB] using hL.snoc i
        · intro a ha; rw [hcur', List.length_append, List.length_singleton] at ha
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (by omega)]
          exact hfr a (by omega)
      · have hmv : st₀.mem (flagAddr + i) ≠ target := fun h => hiC ((hflag i hilt).mp h)
        have hcur' : (List.range (i + 1)).filter (fun p => decide (p ∈ C)) = cur := by
          rw [List.range_succ, List.filter_append]; simp [cur, hiC]
        refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨0, 1,
            by simp [Expr.eval, BinOp.eval, stA, hA_r 6 (by omega), hr6, hmv],
            by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, by simp [hcur', hA_r 11 (by omega), h11], by rw [hcur']; exact hL,
          by rw [hcur']; exact hfr, fun r hr => by
            simp [Function.update_of_ne (by omega : r ≠ 7), hA_r r (by omega), hkr r hr]⟩,
          by rw [hA_r 7 (by omega), hiReg]⟩)
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_11, h2_L, h2_fr, h2_kr⟩
      exact ⟨h2_11, h2_L, h2_fr, h2_kr⟩)
    (by simp [Expr.size]; omega)

private lemma padPass2_triple {w e flagAddr aBase bBase target : ℕ}
    (pProg : Program) (st₀ : State) (C : Finset ℕ) (cList : List ℕ)
    (h0 : st₀.regs 0 = e) (h4 : st₀.regs 4 = flagAddr) (h5 : st₀.regs 5 = 2 * e)
    (h6 : st₀.regs 6 = target) (h9 : st₀.regs 9 = aBase) (h10 : st₀.regs 10 = bBase)
    (h11 : st₀.regs 11 = cList.length)
    (hcList_le : cList.length ≤ e)
    (hL0 : ListAt st₀.mem aBase cList)
    (hflag : ∀ p < 2 * e, st₀.mem (flagAddr + p) = target ↔ p ∈ C)
    (hdAF : DisjointRange aBase e flagAddr (2 * e))
    (hdBF : DisjointRange bBase e flagAddr (2 * e))
    (hdAB : DisjointRange aBase e bBase e)
    (hwF : flagAddr + 2 * e < 2 ^ w) (hwA : aBase + e < 2 ^ w) (hwB : bBase + e < 2 ^ w)
    (hwE : 4 * e + 16 < 2 ^ w)
    (hcomp_len : ((List.range (2 * e)).filter fun p => decide (p ∉ C)).length = 2 * e - cList.length) :
    let comp := (List.range (2 * e)).filter fun p => decide (p ∉ C)
    let need := e - cList.length
    Triple w pProg (fun s => s = st₀) padPass2Stmt
      (normalPost fun s' =>
        ListAt s'.mem aBase (cList ++ comp.take need) ∧
        ListAt s'.mem bBase (comp.drop need) ∧
        (∀ a, (a < aBase ∨ aBase + e ≤ a) → (a < bBase ∨ bBase + e ≤ a) → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≤ 6 ∨ r = 9 ∨ r = 10 → s'.regs r = st₀.regs r))
      (fun _ => 110 * e + 30) := by
  intro comp need s ω hs; subst s
  have hcomp_len' : comp.length = 2 * e - cList.length := hcomp_len
  have hneed_eq : need = e - cList.length := rfl
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [padPass2Stmt]
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st1 : State := { st₀ with regs := Function.update st₀.regs 12 0 }
  have hloop := Triple.forRange_const (p := pProg) (r := 7) (lo := .const 0) (hi := .reg 5)
    (body :=
      .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
      .cond (.bin .eq (.reg 8) (.reg 6))
        .nop
        (.cond (.bin .lt (.reg 11) (.reg 0))
          (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
           .assign 11 (.bin .add (.reg 11) (.const 1)))
          (.store (.bin .add (.reg 10) (.reg 12)) (.reg 7) ;;
           .assign 12 (.bin .add (.reg 12) (.const 1)))))
    (P := fun s => s = st1)
    (Inv := fun i s =>
      let seen := (List.range i).filter fun p => decide (p ∉ C)
      let aCur := cList ++ seen.take need
      let bCur := seen.drop need
      s.regs 7 = i ∧
      s.regs 11 = aCur.length ∧
      s.regs 12 = bCur.length ∧
      ListAt s.mem aBase aCur ∧
      ListAt s.mem bBase bCur ∧
      (∀ a, (a < aBase ∨ aBase + e ≤ a) → (a < bBase ∨ bBase + e ≤ a) → s.mem a = st₀.mem a) ∧
      (∀ r, r ≤ 6 ∨ r = 9 ∨ r = 10 → s.regs r = st₀.regs r))
    40 0 (2 * e) (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        by simp [st1, h11], by simp [st1], by simpa using hL0, fun j hj => by simp at hj,
        fun _ _ _ => rfl,
        fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 7),
          Function.update_of_ne (by omega : r ≠ 12)]⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr5 : s.regs 5 = 2 * e := by rw [hi.2.2.2.2.2.2 5 (by omega), h5]
      simp [Expr.eval, hr5])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hr11, hr12, hLA, hLB, hfr, hkr⟩
      set seen := (List.range i).filter fun p => decide (p ∉ C)
      have hseen_le_comp : seen.length ≤ comp.length := by
        have hsub : List.range (2 * e) = List.range i ++ (List.range (2 * e)).drop i := by
          conv_lhs => rw [← List.take_append_drop i (List.range (2 * e))]
          rw [List.take_range, Nat.min_eq_left (by omega)]
        calc seen.length
            ≤ seen.length + (((List.range (2 * e)).drop i).filter fun p => decide (p ∉ C)).length :=
              Nat.le_add_right _ _
          _ = ((List.range i ++ (List.range (2 * e)).drop i).filter fun p => decide (p ∉ C)).length := by
              rw [List.filter_append, List.length_append]
          _ = comp.length := by rw [← hsub]
      have haLen_le : (cList ++ seen.take need).length ≤ e := by
        rw [List.length_append, List.length_take]; omega
      have hbLen_le : (seen.drop need).length ≤ e := by
        rw [List.length_drop]; omega
      have hmF : s.mem (flagAddr + i) = st₀.mem (flagAddr + i) :=
        hfr _ (Or.elim hdAF (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
              (Or.elim hdBF (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
      have hr0 : s.regs 0 = e := by rw [hkr 0 (by omega), h0]
      have hr4 : s.regs 4 = flagAddr := by rw [hkr 4 (by omega), h4]
      have hr6 : s.regs 6 = target := by rw [hkr 6 (by omega), h6]
      have hr9 : s.regs 9 = aBase := by rw [hkr 9 (by omega), h9]
      have hr10 : s.regs 10 = bBase := by rw [hkr 10 (by omega), h10]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := st₀.mem (flagAddr + i))
        (by simp [Expr.eval, BinOp.eval, hr4, hiReg, (by omega : flagAddr + i < 2 ^ w), hmF]) ?_
      let stA : State := { s with regs := Function.update s.regs 8 (st₀.mem (flagAddr + i)) }
      have hA_r : ∀ r, r ≠ 8 → stA.regs r = s.regs r :=
        fun r hr => Function.update_of_ne hr _ _
      by_cases hiC : i ∈ C
      · have hmv : st₀.mem (flagAddr + i) = target := (hflag i hilt).mpr hiC
        have hseen' : (List.range (i + 1)).filter (fun p => decide (p ∉ C)) = seen := by
          rw [List.range_succ, List.filter_append]; simp [seen, hiC]
        refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨1, 1,
            by simp [Expr.eval, BinOp.eval, stA, hA_r 6 (by omega), hr6, hmv, hw1],
            by simp only [one_ne_zero, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp,
          by rw [hseen']; dsimp only; rw [Function.update_of_ne (by decide), hA_r 11 (by omega), hr11],
          by rw [hseen']; dsimp only; rw [Function.update_of_ne (by decide), hA_r 12 (by omega), hr12],
          by rw [hseen']; exact hLA,
          by rw [hseen']; exact hLB, hfr, fun r hr => by
            simp [Function.update_of_ne (by omega : r ≠ 7), hA_r r (by omega), hkr r hr]⟩,
          by rw [hA_r 7 (by omega), hiReg]⟩
      · have hmv : st₀.mem (flagAddr + i) ≠ target := fun h => hiC ((hflag i hilt).mp h)
        have hseen' : (List.range (i + 1)).filter (fun p => decide (p ∉ C)) = seen ++ [i] := by
          rw [List.range_succ, List.filter_append]; simp [seen, hiC]
        have hseen'_le_comp : (seen ++ [i]).length ≤ comp.length := by
          have hsub : List.range (2 * e) = List.range (i + 1) ++ (List.range (2 * e)).drop (i + 1) := by
            conv_lhs => rw [← List.take_append_drop (i + 1) (List.range (2 * e))]
            rw [List.take_range, Nat.min_eq_left (by omega)]
          calc (seen ++ [i]).length
              = ((List.range (i + 1)).filter fun p => decide (p ∉ C)).length := by rw [hseen']
            _ ≤ ((List.range (i + 1)).filter fun p => decide (p ∉ C)).length +
                (((List.range (2 * e)).drop (i + 1)).filter fun p => decide (p ∉ C)).length :=
                Nat.le_add_right _ _
            _ = comp.length := by rw [← List.length_append, ← List.filter_append, ← hsub]
        by_cases hlt : (cList ++ seen.take need).length < e
        · have hseen_lt : seen.length < need := by
            rw [List.length_append, List.length_take] at hlt; omega
          set aLen := (cList ++ seen.take need).length
          have hr11' : stA.regs 11 = aLen := by rw [hA_r 11 (by omega), hr11]
          let memB := Function.update s.mem (aBase + aLen) i
          let stB : State := { stA with mem := memB }
          let stC : State := { stB with regs := Function.update stB.regs 11 (aLen + 1) }
          have hs1 : Runs w pProg ω (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7)) stA .normal stB 5 := by
            rw [runs_store_iff]
            exact ⟨aBase + aLen, i,
              by simp [Expr.eval, BinOp.eval, hA_r 9 (by omega), hr9, hr11',
                   (by omega : aBase + aLen < 2 ^ w)],
              by simp [Expr.eval, hA_r 7 (by omega), hiReg], rfl, rfl, by simp [Expr.size]⟩
          have hs2 : Runs w pProg ω (.assign 11 (.bin .add (.reg 11) (.const 1))) stB .normal stC 4 := by
            rw [runs_assign_iff]
            exact ⟨aLen + 1,
              by simp [Expr.eval, BinOp.eval, stB, hr11', hw1, (by omega : aLen + 1 < 2 ^ w)],
              rfl, rfl, by simp [Expr.size]⟩
          have htake' : (seen ++ [i]).take need = seen.take need ++ [i] := by
            rw [list_take_append_singleton_lt hseen_lt, List.take_of_length_le (by omega)]
          have hdrop' : (seen ++ [i]).drop need = seen.drop need := by
            rw [list_drop_append_singleton_lt hseen_lt, List.drop_eq_nil_of_le (by omega)]
          have hlt' : aLen < e := hlt
          have hinner : Runs w pProg ω
              (.cond (.bin .lt (.reg 11) (.reg 0))
                (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
                 .assign 11 (.bin .add (.reg 11) (.const 1)))
                (.store (.bin .add (.reg 10) (.reg 12)) (.reg 7) ;;
                 .assign 12 (.bin .add (.reg 12) (.const 1)))) stA .normal stC 14 :=
            runs_cond_iff.mpr ⟨1, 10,
              by simp [Expr.eval, BinOp.eval, hr11', hA_r 0 (by omega), hr0, hlt', hw1],
              by simp only [one_ne_zero, ↓reduceIte]
                 exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
              by simp [Expr.size]⟩
          refine ⟨.normal, stC, 18, runs_cond_iff.mpr ⟨0, 14,
              by simp [Expr.eval, BinOp.eval, stA, hA_r 6 (by omega), hr6, hmv],
              by simp only [↓reduceIte]; exact hinner,
              by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
          refine ⟨⟨by simp,
            by rw [hseen', htake', ← List.append_assoc, List.length_append, List.length_singleton]
               dsimp only [stC]; rw [Function.update_of_ne (by decide), Function.update_self],
            by rw [hseen', hdrop']
               dsimp only [stC, stB]
               rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hA_r 12 (by omega), hr12],
            ?_, ?_, ?_, fun r hr => by
              simp [stC, stB, Function.update_of_ne (by omega : r ≠ 7),
                Function.update_of_ne (by omega : r ≠ 11), hA_r r (by omega), hkr r hr]⟩,
            by simp [stC, stB, hA_r 7 (by omega), hiReg]⟩
          · rw [hseen', htake', ← List.append_assoc]
            simpa [stC, stB, memB, aLen] using hLA.snoc i
          · rw [hseen', hdrop']; intro j hj; dsimp only [stC, stB, memB]
            rw [Function.update_of_ne (disjointRange_ne hdAB (by omega) (by omega) (by omega) (by omega)).symm]
            exact hLB j hj
          · intro a haA haB; dsimp only [stC, stB, memB]
            rw [Function.update_of_ne (by omega)]
            exact hfr a haA haB
        · have hseen_ge : need ≤ seen.length := by
            rw [List.length_append, List.length_take] at hlt; omega
          set bLen := (seen.drop need).length
          have hr12' : stA.regs 12 = bLen := by rw [hA_r 12 (by omega), hr12]
          set aLen := (cList ++ seen.take need).length
          have hlt' : ¬ aLen < e := hlt
          have hr11' : stA.regs 11 = aLen := by rw [hA_r 11 (by omega), hr11]
          have hbLen_lt : bLen < e := by
            simp only [bLen, List.length_drop]; simp at hseen'_le_comp; omega
          let memB := Function.update s.mem (bBase + bLen) i
          let stB : State := { stA with mem := memB }
          let stC : State := { stB with regs := Function.update stB.regs 12 (bLen + 1) }
          have hs1 : Runs w pProg ω (.store (.bin .add (.reg 10) (.reg 12)) (.reg 7)) stA .normal stB 5 := by
            rw [runs_store_iff]
            exact ⟨bBase + bLen, i,
              by simp [Expr.eval, BinOp.eval, hA_r 10 (by omega), hr10, hr12',
                   (by omega : bBase + bLen < 2 ^ w)],
              by simp [Expr.eval, hA_r 7 (by omega), hiReg], rfl, rfl, by simp [Expr.size]⟩
          have hs2 : Runs w pProg ω (.assign 12 (.bin .add (.reg 12) (.const 1))) stB .normal stC 4 := by
            rw [runs_assign_iff]
            exact ⟨bLen + 1,
              by simp [Expr.eval, BinOp.eval, stB, hr12', hw1, (by omega : bLen + 1 < 2 ^ w)],
              rfl, rfl, by simp [Expr.size]⟩
          have htake' : (seen ++ [i]).take need = seen.take need :=
            list_take_append_singleton_ge hseen_ge
          have hdrop' : (seen ++ [i]).drop need = seen.drop need ++ [i] :=
            list_drop_append_singleton_ge hseen_ge
          have hinner : Runs w pProg ω
              (.cond (.bin .lt (.reg 11) (.reg 0))
                (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
                 .assign 11 (.bin .add (.reg 11) (.const 1)))
                (.store (.bin .add (.reg 10) (.reg 12)) (.reg 7) ;;
                 .assign 12 (.bin .add (.reg 12) (.const 1)))) stA .normal stC 14 :=
            runs_cond_iff.mpr ⟨0, 10,
              by simp [Expr.eval, BinOp.eval, hr11', hA_r 0 (by omega), hr0, hlt'],
              by simp only [↓reduceIte]
                 exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
              by simp [Expr.size]⟩
          refine ⟨.normal, stC, 18, runs_cond_iff.mpr ⟨0, 14,
              by simp [Expr.eval, BinOp.eval, stA, hA_r 6 (by omega), hr6, hmv],
              by simp only [↓reduceIte]; exact hinner,
              by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
          refine ⟨⟨by simp,
            by rw [hseen', htake']
               dsimp only [stC, stB]
               rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr11'],
            by rw [hseen', hdrop', List.length_append, List.length_singleton]
               dsimp only [stC]; rw [Function.update_of_ne (by decide), Function.update_self],
            ?_, ?_, ?_, fun r hr => by
              simp [stC, stB, Function.update_of_ne (by omega : r ≠ 7),
                Function.update_of_ne (by omega : r ≠ 12), hA_r r (by omega), hkr r hr]⟩,
            by simp [stC, stB, hA_r 7 (by omega), hiReg]⟩
          · rw [hseen', htake']; intro j hj; dsimp only [stC, stB, memB]
            rw [Function.update_of_ne (disjointRange_ne hdAB (by omega) (by omega) (by omega) (by omega))]
            exact hLA j hj
          · rw [hseen', hdrop']
            simpa [stC, stB, memB, bLen] using hLB.snoc i
          · intro a haA haB; dsimp only [stC, stB, memB]
            rw [Function.update_of_ne (by omega)]
            exact hfr a haA haB)
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, _, _, h2_LA, h2_LB, h2_fr, h2_kr⟩
      exact ⟨h2_LA, h2_LB, h2_fr, h2_kr⟩)
    (by simp [Expr.size]; omega)

private lemma padSetup_triple {w e kU uAddr outPairsAddr h : ℕ}
    (pProg : Program) (st₀ : State)
    (h0 : st₀.regs 0 = e) (h1 : st₀.regs 1 = kU)
    (hwE : 4 * e + 16 < 2 ^ w) :
    let target := if e < kU then 0 else 1
    Triple w pProg (fun s => s = st₀)
      (.assign 5 (.bin .mul (.const 2) (.reg 0)) ;;
       .cond (.bin .lt (.reg 0) (.reg 1))
         (.assign 6 (.const 0))
         (.assign 6 (.const 1)))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧
        s'.regs 5 = 2 * e ∧
        s'.regs 6 = target ∧
        (∀ r ≤ 4, s'.regs r = st₀.regs r))
      (fun _ => 20) := by
  intro target s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 2 * e)
    (by simp [Expr.eval, BinOp.eval, h0, hw2, (by omega : 2 * e < 2 ^ w)]) ?_
  let stA : State := { st₀ with regs := Function.update st₀.regs 5 (2 * e) }
  by_cases hlt : e < kU
  · let stB : State := { stA with regs := Function.update stA.regs 6 0 }
    have hbr : Runs w pProg ω (.assign 6 (.const 0)) stA .normal stB 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, by simp [Expr.size]⟩
    refine ⟨.normal, stB, 6, runs_cond_iff.mpr ⟨1, 2,
        by simp [Expr.eval, BinOp.eval, stA, h0, h1, hlt, hw1],
        by simp only [one_ne_zero, ↓reduceIte]; exact hbr,
        by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
    exact ⟨rfl, by simp [stB, stA], by simp [stB, target, hlt],
      fun r hr => by simp [stB, stA, Function.update_of_ne (by omega : r ≠ 6),
        Function.update_of_ne (by omega : r ≠ 5)]⟩
  · let stB : State := { stA with regs := Function.update stA.regs 6 1 }
    have hbr : Runs w pProg ω (.assign 6 (.const 1)) stA .normal stB 2 :=
      runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
    refine ⟨.normal, stB, 6, runs_cond_iff.mpr ⟨0, 2,
        by simp [Expr.eval, BinOp.eval, stA, h0, h1, hlt],
        by simp only [↓reduceIte]; exact hbr,
        by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
    exact ⟨rfl, by simp [stB, stA], by simp [stB, target, hlt],
      fun r hr => by simp [stB, stA, Function.update_of_ne (by omega : r ≠ 6),
        Function.update_of_ne (by omega : r ≠ 5)]⟩

private lemma padHeader_triple {w e outPairsAddr : ℕ}
    (pProg : Program) (st₀ : State)
    (h0 : st₀.regs 0 = e) (h3 : st₀.regs 3 = outPairsAddr)
    (hwP : outPairsAddr + 3 + 2 * e < 2 ^ w) (hwE : 4 * e + 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀)
      (.store (.reg 3) (.const 1) ;;
       .store (.bin .add (.reg 3) (.const 1)) (.reg 0) ;;
       .store (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 0)) (.reg 0) ;;
       .assign 9 (.bin .add (.reg 3) (.const 2)) ;;
       .assign 10 (.bin .add (.bin .add (.reg 3) (.const 3)) (.reg 0)))
      (normalPost fun s' =>
        s'.mem outPairsAddr = 1 ∧
        s'.mem (outPairsAddr + 1) = e ∧
        s'.mem (outPairsAddr + 2 + e) = e ∧
        (∀ a, a ≠ outPairsAddr → a ≠ outPairsAddr + 1 → a ≠ outPairsAddr + 2 + e →
          s'.mem a = st₀.mem a) ∧
        s'.regs 9 = outPairsAddr + 2 ∧
        s'.regs 10 = outPairsAddr + 3 + e ∧
        (∀ r ≤ 6, s'.regs r = st₀.regs r))
      (fun _ => 35) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_seq_store_le (x := outPairsAddr) (v := 1)
    (by simp [Expr.eval, h3]) (by simp [Expr.eval, hw1]) ?_
  refine runs_seq_store_le (x := outPairsAddr + 1) (v := e)
    (by simp [Expr.eval, BinOp.eval, h3, hw1, (by omega : outPairsAddr + 1 < 2 ^ w)])
    (by simp [Expr.eval, h0]) ?_
  refine runs_seq_store_le (x := outPairsAddr + 2 + e) (v := e)
    (by simp [Expr.eval, BinOp.eval, h3, h0, hw2, (by omega : outPairsAddr + 2 < 2 ^ w),
          (by omega : outPairsAddr + 2 + e < 2 ^ w)])
    (by simp [Expr.eval, h0]) ?_
  refine runs_seq_assign_le (v := outPairsAddr + 2)
    (by simp [Expr.eval, BinOp.eval, h3, hw2, (by omega : outPairsAddr + 2 < 2 ^ w)]) ?_
  let stA : State := {
    mem := Function.update (Function.update (Function.update st₀.mem outPairsAddr 1)
      (outPairsAddr + 1) e) (outPairsAddr + 2 + e) e
    regs := Function.update st₀.regs 9 (outPairsAddr + 2)
    pos := st₀.pos }
  let stB : State := { stA with regs := Function.update stA.regs 10 (outPairsAddr + 3 + e) }
  refine ⟨.normal, stB, 6, runs_assign_iff.mpr ⟨outPairsAddr + 3 + e,
      by simp [Expr.eval, BinOp.eval, stA, h3, h0, hw3, (by omega : outPairsAddr + 3 < 2 ^ w),
           (by omega : outPairsAddr + 3 + e < 2 ^ w)],
      rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
  refine ⟨?_, ?_, ?_, ?_, by simp [stB, stA], by simp [stB], fun r hr => by
    simp [stB, stA, Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 9)]⟩
  · simp [stB, stA, Function.update_of_ne (by omega : outPairsAddr ≠ outPairsAddr + 2 + e),
      Function.update_of_ne (by omega : outPairsAddr ≠ outPairsAddr + 1)]
  · simp [stB, stA, Function.update_of_ne (by omega : outPairsAddr + 1 ≠ outPairsAddr + 2 + e)]
  · simp [stB, stA]
  · intro a h1 h2 h3
    simp [stB, stA, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]

/-- Specification of `padToBisectionProc`. -/
theorem padToBisectionProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [padToBisectionProc]) :
    MeetsContract w pProg b (padToBisectionContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨e, kU, uAddr, outPairsAddr, h, uList, rfl, hlenU, hndU, hu_lt,
    hlistU, hzero, huH, hpH, hdPU, hwH, hwE⟩
  unfold padToBisectionSpace at hwH
  have hw1 : 1 < 2 ^ w := by omega
  set V := Finset.range (2 * e)
  set U := uList.toFinset
  have hU_sub : U ⊆ V := fun p hp => Finset.mem_range.mpr (hu_lt p (List.mem_toFinset.mp hp))
  have hU_card : U.card = kU := by rw [List.toFinset_card_of_nodup hndU, hlenU]
  have hVU_card : (V \ U).card = 2 * e - kU := by
    have := Finset.card_sdiff_add_card_eq_card hU_sub
    rw [Finset.card_range, hU_card] at this; omega
  have hkU_le : kU ≤ 2 * e := by
    have := Finset.card_le_card hU_sub; rw [Finset.card_range, hU_card] at this; exact this
  set C := outerSmallerSide e U
  set target := if e < kU then 0 else 1
  have hC_eq : C = if e < kU then V \ U else U := by
    unfold C outerSmallerSide
    change (if U.card ≤ (V \ U).card then U else V \ U) = if e < kU then V \ U else U
    rw [hU_card, hVU_card]
    by_cases hlt : e < kU
    · rw [if_pos hlt, if_neg (by omega)]
    · rw [if_neg hlt, if_pos (by omega)]
  have hC_sub : C ⊆ V := by
    rw [hC_eq]; split_ifs; exact Finset.sdiff_subset; exact hU_sub
  have hC_card_le : C.card ≤ e := by
    rw [hC_eq]; split_ifs <;> omega
  set cList := (List.range (2 * e)).filter fun p => decide (p ∈ C)
  set comp := (List.range (2 * e)).filter fun p => decide (p ∉ C)
  have hcList_sort : cList = C.sort (· ≤ ·) := list_range_filter_eq_finset_sort hC_sub
  have hcomp_sort : comp = (V \ C).sort (· ≤ ·) := by
    have h1 : comp = (List.range (2 * e)).filter fun p => decide (p ∈ V \ C) := by
      apply List.filter_congr
      intro p hp
      have hpV : p ∈ V := Finset.mem_range.mpr (List.mem_range.mp hp)
      simp [Finset.mem_sdiff, hpV]
    rw [h1]
    exact list_range_filter_eq_finset_sort Finset.sdiff_subset
  have hcList_len : cList.length = C.card := by rw [hcList_sort, Finset.length_sort]
  have hcomp_len : comp.length = 2 * e - cList.length := by
    rw [hcomp_sort, Finset.length_sort, hcList_len]
    have := Finset.card_sdiff_add_card_eq_card hC_sub
    rw [Finset.card_range] at this; omega
  set st0 := startState [e, kU, uAddr, outPairsAddr, h] mem pos
  refine runs_start_le ?_
  dsimp only [padToBisectionProc]
  -- Stage 1: padSetup
  refine runs_seq_triple_le
    (padSetup_triple pProg st0 (e := e) (kU := kU) (uAddr := uAddr) (outPairsAddr := outPairsAddr)
      (h := h) rfl rfl hwE) rfl ?_
  intro st1 ⟨h1_mem, h1_5, h1_6, h1_r⟩
  -- Stage 2: markVertsStmt
  refine runs_seq_triple_le
    (markVerts_triple (n := 2 * e) (len := kU) (listAddr := uAddr) (locAddr := h) (val := 1)
      pProg st1 uList (by decide) (by rw [h1_r 1 (by omega)]; rfl)
      (by rw [h1_r 2 (by omega)]; rfl) (by rw [h1_r 4 (by omega)]; rfl)
      hlenU hu_lt (by rw [h1_mem]; exact hlistU) (Or.inr huH)
      (by omega) (by omega) hw1 hw1) rfl ?_
  intro st2 ⟨h2_mark, h2_fr, h2_kr⟩
  have h2_r : ∀ r ≤ 6, st2.regs r = st1.regs r := fun r hr => h2_kr r (by omega) (by omega)
  have h2_flag : ∀ p < 2 * e, st2.mem (h + p) = target ↔ p ∈ C := by
    intro p hp
    have hst2_p : st2.mem (h + p) = if p ∈ U then 1 else 0 := by
      by_cases hpU : p ∈ U
      · simp only [hpU, ↓reduceIte]
        exact h2_mark p (List.mem_toFinset.mp hpU)
      · simp only [hpU, ↓reduceIte]
        rw [h2_fr (h + p) (fun u hu hEq => hpU (List.mem_toFinset.mpr (by
          have : u = p := by omega
          subst this; exact hu))), h1_mem]
        exact hzero (h + p) (by omega)
    rw [hst2_p, hC_eq]
    dsimp only [target]
    by_cases hlt : e < kU <;> by_cases hpU : p ∈ U <;>
      simp [hlt, hpU, V, Finset.mem_sdiff, Finset.mem_range.mpr hp]
  -- Stage 3: padHeader
  refine runs_seq_triple_le
    (padHeader_triple (e := e) (outPairsAddr := outPairsAddr) pProg st2
      (by rw [h2_r 0 (by omega), h1_r 0 (by omega)]; rfl)
      (by rw [h2_r 3 (by omega), h1_r 3 (by omega)]; rfl)
      (by omega) hwE) rfl ?_
  intro st3 ⟨h3_p0, h3_p1, h3_pe, h3_fr, h3_9, h3_10, h3_r⟩
  have h3_flag : ∀ p < 2 * e, st3.mem (h + p) = target ↔ p ∈ C := by
    intro p hp
    rw [h3_fr (h + p) (by omega) (by omega) (by omega)]
    exact h2_flag p hp
  -- Stage 4: padPass1Stmt
  refine runs_seq_triple_le
    (padPass1_triple (e := e) (flagAddr := h) (aBase := outPairsAddr + 2) (target := target)
      pProg st3 C
      (by rw [h3_r 5 (by omega), h2_r 5 (by omega), h1_5])
      (by rw [h3_r 4 (by omega), h2_r 4 (by omega), h1_r 4 (by omega)]; rfl)
      (by rw [h3_r 6 (by omega), h2_r 6 (by omega), h1_6])
      h3_9 hC_sub h3_flag (Or.inl (by omega)) (by omega) (by omega) hwE) rfl ?_
  intro st4 ⟨h4_11, h4_LA, h4_fr, h4_kr⟩
  have hcList_le : cList.length ≤ e := by omega
  change ∀ a, a < outPairsAddr + 2 ∨ outPairsAddr + 2 + cList.length ≤ a → st4.mem a = st3.mem a at h4_fr
  have h4_flag : ∀ p < 2 * e, st4.mem (h + p) = target ↔ p ∈ C := by
    intro p hp
    rw [h4_fr (h + p) (Or.inr (by omega))]
    exact h3_flag p hp
  -- Stage 5: padPass2Stmt
  refine runs_seq_triple_le
    (padPass2_triple (e := e) (flagAddr := h) (aBase := outPairsAddr + 2)
      (bBase := outPairsAddr + 3 + e) (target := target)
      pProg st4 C cList
      (by rw [h4_kr 0 (by omega), h3_r 0 (by omega), h2_r 0 (by omega), h1_r 0 (by omega)]; rfl)
      (by rw [h4_kr 4 (by omega), h3_r 4 (by omega), h2_r 4 (by omega), h1_r 4 (by omega)]; rfl)
      (by rw [h4_kr 5 (by omega), h3_r 5 (by omega), h2_r 5 (by omega), h1_5])
      (by rw [h4_kr 6 (by omega), h3_r 6 (by omega), h2_r 6 (by omega), h1_6])
      (by rw [h4_kr 9 (by omega), h3_9])
      (by rw [h4_kr 10 (by omega), h3_10])
      h4_11 (by omega) h4_LA h4_flag
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (by omega) (by omega) (by omega) hwE hcomp_len) rfl ?_
  intro st5 ⟨h5_LA, h5_LB, h5_fr, h5_kr⟩
  -- Return h + 2 * e
  refine runs_ret_le (v := h + 2 * e)
    (by simp [Expr.eval, BinOp.eval, h5_kr 4 (by omega), h4_kr 4 (by omega), h3_r 4 (by omega),
          h2_r 4 (by omega), h1_r 4 (by omega), h5_kr 5 (by omega), h4_kr 5 (by omega),
          h3_r 5 (by omega), h2_r 5 (by omega), h1_5, st0, startState,
          (by omega : h + 2 * e < 2 ^ w)]) ?_ ?_
  · dsimp only [padToBisectionContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadU : readList mem uAddr kU = uList := by
      rw [← hlenU]; exact readList_eq_of_listAt hlistU
    simp only [hreadU]
    set need := e - cList.length
    set A_list := cList ++ comp.take need
    set B_list := comp.drop need
    refine ⟨rfl, ?_, ⟨A_list, B_list, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro a ha
      rw [h5_fr a (Or.inr (by omega)) (Or.inr (by omega)), h4_fr a (Or.inr (by omega)),
        h3_fr a (by omega) (by omega) (by omega),
        h2_fr a (fun u hu => by have := hu_lt u hu; omega), h1_mem]
      exact hzero a (by omega)
    · -- A_list.Nodup
      rw [List.nodup_append]
      refine ⟨List.nodup_range.filter _, (List.nodup_range.filter _).take, fun x hx y hy => ?_⟩
      simp only [cList, List.mem_filter, decide_eq_true_eq] at hx
      have hy' := List.mem_of_mem_take hy
      simp only [comp, List.mem_filter, decide_eq_true_eq] at hy'
      rintro rfl; exact hy'.2 hx.2
    · -- B_list.Nodup
      exact (List.nodup_range.filter _).drop
    · -- A_list.length = e
      simp only [A_list, List.length_append, List.length_take]; omega
    · -- B_list.length = e
      simp only [B_list, List.length_drop]; omega
    · -- ∀ p ∈ A_list, p < 2 * e
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact List.mem_range.mp (List.mem_filter.mp hp).1
      · exact List.mem_range.mp (List.mem_filter.mp (List.mem_of_mem_take hp)).1
    · -- ∀ p ∈ B_list, p < 2 * e
      intro p hp
      exact List.mem_range.mp (List.mem_filter.mp (List.mem_of_mem_drop hp)).1
    · -- (A_list.toFinset, B_list.toFinset) = padToBisection e U
      have hA_fin : A_list.toFinset = C ∪ (((V \ C).sort (· ≤ ·)).take (e - C.card)).toFinset := by
        simp only [A_list, List.toFinset_append, hcList_sort, hcomp_sort, need, hcList_len]
        ext x; simp [Finset.mem_sort]
      have hB_fin : B_list.toFinset = V \ A_list.toFinset := by
        ext x
        simp only [B_list, A_list, List.mem_toFinset, Finset.mem_sdiff, List.mem_append, not_or]
        have hcomp_split : comp = comp.take need ++ comp.drop need := (List.take_append_drop need comp).symm
        constructor
        · intro hx
          have hx_comp : x ∈ comp := List.mem_of_mem_drop hx
          have hxV : x ∈ V := Finset.mem_range.mpr (List.mem_range.mp (List.mem_filter.mp hx_comp).1)
          have hxC : x ∉ C := of_decide_eq_true (List.mem_filter.mp hx_comp).2
          have hx_not_cList : x ∉ cList := fun h => hxC (of_decide_eq_true (List.mem_filter.mp h).2)
          have hx_not_take : x ∉ comp.take need := by
            have hnd_comp : comp.Nodup := List.nodup_range.filter _
            rw [hcomp_split, List.nodup_append] at hnd_comp
            intro hxt; exact hnd_comp.2.2 x hxt x hx rfl
          exact ⟨hxV, hx_not_cList, hx_not_take⟩
        · rintro ⟨hxV, hx_not_cList, hx_not_take⟩
          have hxC : x ∉ C := fun hxC =>
            hx_not_cList (List.mem_filter.mpr ⟨List.mem_range.mpr (Finset.mem_range.mp hxV), decide_eq_true hxC⟩)
          have hx_comp : x ∈ comp :=
            List.mem_filter.mpr ⟨List.mem_range.mpr (Finset.mem_range.mp hxV), decide_eq_true hxC⟩
          rw [hcomp_split, List.mem_append] at hx_comp
          exact hx_comp.resolve_left hx_not_take
      rw [Prod.ext_iff]
      exact ⟨hA_fin, by rw [hB_fin, hA_fin]; rfl⟩
    · -- SinglePairAt
      have hAlen : A_list.length = e := by
        simp only [A_list, List.length_append, List.length_take]; omega
      have hBlen : B_list.length = e := by
        simp only [B_list, List.length_drop]; omega
      refine ⟨?_, ?_, h5_LA, ?_, ?_⟩
      · rw [h5_fr outPairsAddr (Or.inl (by omega)) (Or.inl (by omega)),
          h4_fr outPairsAddr (Or.inl (by omega)), h3_p0]
      · rw [h5_fr (outPairsAddr + 1) (Or.inl (by omega)) (Or.inl (by omega)),
          h4_fr (outPairsAddr + 1) (Or.inl (by omega)), h3_p1, hAlen]
      · rw [hAlen, h5_fr (outPairsAddr + 2 + e) (Or.inr (by omega)) (Or.inl (by omega)),
          h4_fr (outPairsAddr + 2 + e) (Or.inr (by omega)), h3_pe, hBlen]
      · rw [hAlen]; exact h5_LB
    · -- Frame
      intro a haH haP
      rw [h5_fr a (by omega) (by omega), h4_fr a (by omega),
        h3_fr a (by omega) (by omega) (by omega),
        h2_fr a (fun u hu => by omega), h1_mem]
      rfl
  · simp only [padToBisectionContract, padToBisectionCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega


end MinCostFlow.ExpanderDecomp
