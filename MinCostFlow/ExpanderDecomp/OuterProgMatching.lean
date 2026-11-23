module

public import MinCostFlow.ExpanderDecomp.OuterProgMatchingBase
public import MinCostFlow.ExpanderDecomp.OuterProgMatchingPad
public import MinCostFlow.ExpanderDecomp.OuterProgMatchingInj
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Verification of `fakeCompletionProc` (`OuterProgMatching`)

Proves `fakeCompletionProc_spec` and re-exports `OuterProgMatchingBase`, `OuterProgMatchingPad`,
and `OuterProgMatchingInj`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 7. Verification of `fakeCompletionProc` -/

private lemma fcSetup1_triple {w e pairsAddr h : ℕ}
    (pProg : Program) (st₀ : State)
    (h0 : st₀.regs 0 = e) (h6 : st₀.regs 6 = h)
    (hwH : h + 8 * e < 2 ^ w) (hwE : 4 * e + 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀)
      (.assign 7 (.bin .mul (.const 2) (.reg 0)) ;;
       .assign 8 (.reg 6) ;;
       .assign 9 (.bin .add (.reg 8) (.reg 7)) ;;
       .assign 10 (.bin .add (.reg 9) (.reg 7)) ;;
       .assign 11 (.bin .add (.reg 10) (.reg 7)))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧
        s'.regs 7 = 2 * e ∧
        s'.regs 8 = h ∧
        s'.regs 9 = h + 2 * e ∧
        s'.regs 10 = h + 4 * e ∧
        s'.regs 11 = h + 6 * e ∧
        (∀ r ≤ 6, s'.regs r = st₀.regs r))
      (fun _ => 25) := by
  intro s ω hs; subst s
  have hw2 : 2 < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 2 * e)
    (by simp [Expr.eval, BinOp.eval, h0, hw2, (by omega : 2 * e < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := h)
    (by simp [Expr.eval, h6]) ?_
  refine runs_seq_assign_le (v := h + 2 * e)
    (by simp [Expr.eval, BinOp.eval, (by omega : h + 2 * e < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := h + 4 * e)
    (by simp [Expr.eval, BinOp.eval, (by omega : h + 2 * e + 2 * e < 2 ^ w)]; omega) ?_
  let stA : State :=
    { st₀ with regs := Function.update (Function.update (Function.update
        (Function.update st₀.regs 7 (2 * e)) 8 h) 9 (h + 2 * e)) 10 (h + 4 * e) }
  let stB : State := { stA with regs := Function.update stA.regs 11 (h + 6 * e) }
  refine ⟨.normal, stB, 4, runs_assign_iff.mpr ⟨h + 6 * e,
      by simp [Expr.eval, BinOp.eval, stA, (by omega : h + 4 * e + 2 * e < 2 ^ w)]; omega,
      rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
  exact ⟨rfl, by simp [stB, stA], by simp [stB, stA], by simp [stB, stA], by simp [stB, stA],
    by simp [stB], fun r hr => by
      simp [stB, stA, Function.update_of_ne (by omega : r ≠ 11),
        Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 9),
        Function.update_of_ne (by omega : r ≠ 8), Function.update_of_ne (by omega : r ≠ 7)]⟩

private lemma fcSetup2_triple {w pairsAddr : ℕ}
    (pProg : Program) (st₀ : State) (A_list B_list : List ℕ)
    (h1 : st₀.regs 1 = pairsAddr)
    (hSP : SinglePairAt st₀.mem pairsAddr A_list B_list)
    (hwP : pairsAddr + 3 + A_list.length + B_list.length < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀)
      (.assign 12 (.load (.bin .add (.reg 1) (.const 1))) ;;
       .assign 13 (.bin .add (.reg 1) (.const 2)) ;;
       .assign 14 (.load (.bin .add (.reg 13) (.reg 12))) ;;
       .assign 15 (.bin .add (.bin .add (.reg 13) (.reg 12)) (.const 1)))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧
        s'.regs 12 = A_list.length ∧
        s'.regs 13 = pairsAddr + 2 ∧
        s'.regs 14 = B_list.length ∧
        s'.regs 15 = pairsAddr + 3 + A_list.length ∧
        (∀ r ≤ 11, s'.regs r = st₀.regs r))
      (fun _ => 25) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  rcases hSP with ⟨_, hLenA, _, hLenB, _⟩
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := A_list.length)
    (by simp [Expr.eval, BinOp.eval, h1, hw1, (by omega : pairsAddr + 1 < 2 ^ w), hLenA]) ?_
  refine runs_seq_assign_le (v := pairsAddr + 2)
    (by simp [Expr.eval, BinOp.eval, h1, hw2, (by omega : pairsAddr + 2 < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := B_list.length)
    (by simp [Expr.eval, BinOp.eval, (by omega : pairsAddr + 2 + A_list.length < 2 ^ w), hLenB]) ?_
  let stA : State :=
    { st₀ with regs := Function.update (Function.update
        (Function.update st₀.regs 12 A_list.length) 13 (pairsAddr + 2)) 14 B_list.length }
  let stB : State := { stA with regs := Function.update stA.regs 15 (pairsAddr + 3 + A_list.length) }
  refine ⟨.normal, stB, 6, runs_assign_iff.mpr ⟨pairsAddr + 3 + A_list.length,
      by simp [Expr.eval, BinOp.eval, stA, hw1, (by omega : pairsAddr + 2 + A_list.length < 2 ^ w),
           (by omega : pairsAddr + 2 + A_list.length + 1 < 2 ^ w)]; omega,
      rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
  exact ⟨rfl, by simp [stB, stA], by simp [stB, stA], by simp [stB, stA], by simp [stB],
    fun r hr => by
      simp [stB, stA, Function.update_of_ne (by omega : r ≠ 15),
        Function.update_of_ne (by omega : r ≠ 14), Function.update_of_ne (by omega : r ≠ 13),
        Function.update_of_ne (by omega : r ≠ 12)]⟩

private lemma fcUnmark_triple {w e mM mAddr flagA flagB : ℕ}
    (pProg : Program) (st₀ : State) (M : List (ℕ × ℕ))
    (h2 : st₀.regs 2 = mM) (h3 : st₀.regs 3 = mAddr)
    (h8 : st₀.regs 8 = flagA) (h9 : st₀.regs 9 = flagB)
    (hlenM : M.length = mM) (hM_lt : ∀ ed ∈ M, ed.1 < 2 * e ∧ ed.2 < 2 * e)
    (hEdgesM : EdgesAt st₀.mem mAddr M)
    (hdAM : DisjointRange flagA (2 * e) mAddr (2 * mM))
    (hdBM : DisjointRange flagB (2 * e) mAddr (2 * mM))
    (hdAB : DisjointRange flagA (2 * e) flagB (2 * e))
    (hwM : mAddr + 2 * mM < 2 ^ w) (hwFA : flagA + 2 * e < 2 ^ w) (hwFB : flagB + 2 * e < 2 ^ w)
    (hw2 : 2 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) fcUnmarkStmt
      (normalPost fun s' =>
        (∀ ed ∈ M, s'.mem (flagA + ed.1) = 0 ∧ s'.mem (flagB + ed.2) = 0) ∧
        (∀ a, (∀ ed ∈ M, a ≠ flagA + ed.1 ∧ a ≠ flagB + ed.2) → s'.mem a = st₀.mem a) ∧
        (∀ r ≤ 15, s'.regs r = st₀.regs r))
      (fun _ => 50 * mM + 20) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := pProg) (r := 16) (lo := .const 0) (hi := .reg 2)
    (body :=
      .assign 17 (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 16)))) ;;
      .assign 18 (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 16))) (.const 1))) ;;
      .store (.bin .add (.reg 8) (.reg 17)) (.const 0) ;;
      .store (.bin .add (.reg 9) (.reg 18)) (.const 0))
    (P := fun s => s = st₀)
    (Inv := fun i s =>
      s.regs 16 = i ∧
      (∀ ed ∈ M.take i, s.mem (flagA + ed.1) = 0 ∧ s.mem (flagB + ed.2) = 0) ∧
      (∀ a, (∀ ed ∈ M.take i, a ≠ flagA + ed.1 ∧ a ≠ flagB + ed.2) → s.mem a = st₀.mem a) ∧
      (∀ r ≤ 15, s.regs r = st₀.regs r))
    38 0 mM (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun _ h => by simp at h, fun _ _ => rfl,
        fun r hr => Function.update_of_ne (by omega : r ≠ 16) _ _⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr2 : s.regs 2 = mM := by rw [hi.2.2.2 2 (by omega), h2]
      simp [Expr.eval, hr2])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hclr, hfr, hkr⟩
      have hiLen : i < M.length := by omega
      set ed := M[i]'hiLen
      have hed_lt := hM_lt ed (List.getElem_mem hiLen)
      have hmu : s.mem (mAddr + 2 * i) = ed.1 := by
        rw [hfr _ (fun ed' hed' => by
          have hlt' := hM_lt ed' (List.mem_of_mem_take hed')
          exact ⟨(disjointRange_ne hdAM (by omega) (by omega) (by omega) (by omega)).symm,
                 (disjointRange_ne hdBM (by omega) (by omega) (by omega) (by omega)).symm⟩)]
        exact (hEdgesM i hiLen).1
      have hmv : s.mem (mAddr + 2 * i + 1) = ed.2 := by
        rw [hfr _ (fun ed' hed' => by
          have hlt' := hM_lt ed' (List.mem_of_mem_take hed')
          exact ⟨(disjointRange_ne hdAM (by omega) (by omega) (by omega) (by omega)).symm,
                 (disjointRange_ne hdBM (by omega) (by omega) (by omega) (by omega)).symm⟩)]
        exact (hEdgesM i hiLen).2
      have hr3 : s.regs 3 = mAddr := by rw [hkr 3 (by omega), h3]
      have hr8 : s.regs 8 = flagA := by rw [hkr 8 (by omega), h8]
      have hr9 : s.regs 9 = flagB := by rw [hkr 9 (by omega), h9]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := ed.1)
        (by simp [Expr.eval, BinOp.eval, hr3, hiReg, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : mAddr + 2 * i < 2 ^ w), hmu]) ?_
      refine runs_seq_assign_le (v := ed.2)
        (by simp [Expr.eval, BinOp.eval, hr3, hiReg, hw1, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : mAddr + 2 * i < 2 ^ w), (by omega : mAddr + 2 * i + 1 < 2 ^ w), hmv]) ?_
      refine runs_seq_store_le (x := flagA + ed.1) (v := 0)
        (by simp [Expr.eval, BinOp.eval, hr8, (by omega : flagA + ed.1 < 2 ^ w)])
        (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
      let stA : State := {
        mem := Function.update s.mem (flagA + ed.1) 0
        regs := Function.update (Function.update s.regs 17 ed.1) 18 ed.2
        pos := s.pos }
      let stB : State := { stA with mem := Function.update stA.mem (flagB + ed.2) 0 }
      refine ⟨.normal, stB, 5, runs_store_iff.mpr ⟨flagB + ed.2, 0,
          by simp [Expr.eval, BinOp.eval, stA, hr9, (by omega : flagB + ed.2 < 2 ^ w)],
          by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, by simp [Expr.size]⟩,
        ?_, by simp [Expr.size]⟩
      refine ⟨⟨by simp, ?_, ?_, fun r hr => by
          simp [stB, stA, Function.update_of_ne (by omega : r ≠ 16),
            Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 17),
            hkr r hr]⟩,
        by simp [stB, stA, hiReg]⟩
      · intro ed' hed'
        rw [List.take_succ_eq_append_getElem hiLen, List.mem_append, List.mem_singleton] at hed'
        have hlt' : ed'.1 < 2 * e ∧ ed'.2 < 2 * e := by
          rcases hed' with h | rfl
          · exact hM_lt ed' (List.mem_of_mem_take h)
          · exact hed_lt
        have hneAB : flagA + ed'.1 ≠ flagB + ed.2 :=
          disjointRange_ne hdAB (by omega) (by omega) (by omega) (by omega)
        have hneBA : flagB + ed'.2 ≠ flagA + ed.1 :=
          (disjointRange_ne hdAB (by omega) (by omega) (by omega) (by omega)).symm
        rcases hed' with h | rfl
        · constructor
          · dsimp only [stB, stA]
            rw [Function.update_of_ne hneAB]
            by_cases heq : flagA + ed'.1 = flagA + ed.1
            · rw [heq, Function.update_self]
            · rw [Function.update_of_ne heq]; exact (hclr ed' h).1
          · dsimp only [stB, stA]
            by_cases heq : flagB + ed'.2 = flagB + ed.2
            · rw [heq, Function.update_self]
            · rw [Function.update_of_ne heq, Function.update_of_ne hneBA]; exact (hclr ed' h).2
        · exact ⟨by dsimp only [stB, stA]; rw [Function.update_of_ne hneAB, Function.update_self],
                 by dsimp only [stB]; rw [Function.update_self]⟩
      · intro a ha
        have hmem_cur : ed ∈ M.take (i + 1) := by
          rw [List.take_succ_eq_append_getElem hiLen]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have ⟨hne1, hne2⟩ := ha ed hmem_cur
        dsimp only [stB, stA]
        rw [Function.update_of_ne hne2, Function.update_of_ne hne1]
        exact hfr a fun ed' hed' => ha ed' (by
          rw [List.take_succ_eq_append_getElem hiLen]; exact List.mem_append_left _ hed'))
  refine runs_start_le ?_
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_clr, h2_fr, h2_kr⟩
      have htake : M.take mM = M := by rw [← hlenM, List.take_length]
      rw [htake] at h2_clr h2_fr
      exact ⟨h2_clr, h2_fr, h2_kr⟩)
    (by simp [Expr.size]; omega)

private lemma collectFlag_triple {w n flagAddr outAddr rLen rFlag rOut rI rVal rCnt : ℕ}
    (pProg : Program) (st₀ : State) (S : Finset ℕ)
    (hdReg : [rLen, rFlag, rOut, rI, rVal, rCnt].Nodup)
    (hrLen : st₀.regs rLen = n) (hrFlag : st₀.regs rFlag = flagAddr)
    (hrOut : st₀.regs rOut = outAddr)
    (hf : ∀ p < n, 0 < st₀.mem (flagAddr + p) ↔ p ∈ S)
    (hdOF : DisjointRange outAddr n flagAddr n)
    (hwF : flagAddr + n < 2 ^ w) (hwO : outAddr + n < 2 ^ w) (hwN : n + 16 < 2 ^ w) :
    let l := (List.range n).filter fun p => decide (p ∈ S)
    Triple w pProg (fun s => s = st₀) (collectFlagStmt rLen rFlag rOut rI rVal rCnt)
      (normalPost fun s' =>
        s'.regs rCnt = l.length ∧
        ListAt s'.mem outAddr l ∧
        (∀ a, a < outAddr ∨ outAddr + n ≤ a → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≠ rI → r ≠ rVal → r ≠ rCnt → s'.regs r = st₀.regs r))
      (fun _ => 45 * n + 25) := by
  intro l s ω hs; subst s
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hdReg
  rcases hdReg with ⟨⟨_, _, hLI, hLV, hLC⟩, ⟨_, hFI, hFV, hFC⟩, ⟨hOI, hOV, hOC⟩, ⟨hIV, hIC⟩, hVC, _⟩
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [collectFlagStmt]
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st1 : State := { st₀ with regs := Function.update st₀.regs rCnt 0 }
  have hloop := Triple.forRange_const (p := pProg) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body :=
      .assign rVal (.load (.bin .add (.reg rFlag) (.reg rI))) ;;
      .cond (.bin .lt (.const 0) (.reg rVal))
        (.store (.bin .add (.reg rOut) (.reg rCnt)) (.reg rI) ;;
         .assign rCnt (.bin .add (.reg rCnt) (.const 1)))
        .nop)
    (P := fun s => s = st1)
    (Inv := fun i s =>
      let cur := (List.range i).filter fun p => decide (p ∈ S)
      s.regs rI = i ∧
      s.regs rCnt = cur.length ∧
      ListAt s.mem outAddr cur ∧
      (∀ a, a < outAddr ∨ outAddr + n ≤ a → s.mem a = st₀.mem a) ∧
      (∀ r, r ≠ rI → r ≠ rVal → r ≠ rCnt → s.regs r = st₀.regs r))
    32 0 n (Nat.zero_le n) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        by simp [st1, Function.update_of_ne (Ne.symm hIC)], fun j hj => by simp at hj,
        fun _ _ => rfl,
        fun r hrI _ hrC => by simp [st1, Function.update_of_ne hrI, Function.update_of_ne hrC]⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hrl : s.regs rLen = n := by rw [hi.2.2.2.2 rLen hLI hLV hLC, hrLen]
      simp [Expr.eval, hrl])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hcnt, hL, hfr, hkr⟩
      set cur := (List.range i).filter fun p => decide (p ∈ S)
      have hcur_le : cur.length ≤ i := by
        have := List.length_filter_le (fun p => decide (p ∈ S)) (List.range i); simpa using this
      have hmF : s.mem (flagAddr + i) = st₀.mem (flagAddr + i) :=
        hfr _ (Or.elim hdOF (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
      have hrf : s.regs rFlag = flagAddr := by rw [hkr rFlag hFI hFV hFC, hrFlag]
      have hro : s.regs rOut = outAddr := by rw [hkr rOut hOI hOV hOC, hrOut]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := st₀.mem (flagAddr + i))
        (by simp [Expr.eval, BinOp.eval, hrf, hiReg, (by omega : flagAddr + i < 2 ^ w), hmF]) ?_
      let stA : State := { s with regs := Function.update s.regs rVal (st₀.mem (flagAddr + i)) }
      have hA_r : ∀ r, r ≠ rVal → stA.regs r = s.regs r := fun r hr => Function.update_of_ne hr _ _
      by_cases hiS : i ∈ S
      · have hpos : 0 < st₀.mem (flagAddr + i) := (hf i hilt).mpr hiS
        let memB := Function.update s.mem (outAddr + cur.length) i
        let stB : State := { stA with mem := memB }
        let stC : State := { stB with regs := Function.update stB.regs rCnt (cur.length + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg rOut) (.reg rCnt)) (.reg rI)) stA .normal stB 5 :=
          runs_store_iff.mpr ⟨outAddr + cur.length, i,
            by simp [Expr.eval, BinOp.eval, hA_r rOut hOV, hro, hA_r rCnt (Ne.symm hVC), hcnt,
                 (by omega : outAddr + cur.length < 2 ^ w)],
            by simp [Expr.eval, hA_r rI hIV, hiReg], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.assign rCnt (.bin .add (.reg rCnt) (.const 1))) stB .normal stC 4 :=
          runs_assign_iff.mpr ⟨cur.length + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_r rCnt (Ne.symm hVC), hcnt, hw1,
                 (by omega : cur.length + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        have hcur' : (List.range (i + 1)).filter (fun p => decide (p ∈ S)) = cur ++ [i] := by
          rw [List.range_succ, List.filter_append]; simp [cur, hiS]
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨1, 10,
            by simp [Expr.eval, BinOp.eval, hpos, hw1, (by omega : 0 < 2 ^ w)],
            by simp only [one_ne_zero, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, by simp [stC, hcur', Function.update_of_ne (Ne.symm hIC)], ?_, ?_,
            fun r hrI hrV hrC => by
              simp [stC, stB, Function.update_of_ne hrI, Function.update_of_ne hrC, hA_r r hrV,
                hkr r hrI hrV hrC]⟩,
          by simp [stC, stB, Function.update_of_ne hIC, hA_r rI hIV, hiReg]⟩
        · rw [hcur']; simpa [stC, stB, memB] using hL.snoc i
        · intro a ha; dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (by omega)]
          exact hfr a ha
      · have h0 : ¬ 0 < st₀.mem (flagAddr + i) := fun h => hiS ((hf i hilt).mp h)
        have hcur' : (List.range (i + 1)).filter (fun p => decide (p ∈ S)) = cur := by
          rw [List.range_succ, List.filter_append]; simp [cur, hiS]
        refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨0, 1,
            by simp [Expr.eval, BinOp.eval, h0, (by omega : 0 < 2 ^ w)],
            by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp,
          by rw [hcur']; simp [Function.update_of_ne (Ne.symm hIC), hA_r rCnt (Ne.symm hVC), hcnt],
          by rw [hcur']; exact hL, hfr,
          fun r hrI hrV hrC => by simp [Function.update_of_ne hrI, hA_r r hrV, hkr r hrI hrV hrC]⟩,
          by rw [hA_r rI hIV, hiReg]⟩)
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_cnt, h2_L, h2_fr, h2_kr⟩
      exact ⟨h2_cnt, h2_L, h2_fr, h2_kr⟩)
    (by simp [Expr.size]; omega)

private lemma fcZip_triple {w e unA unB outFAddr outLenAddr : ℕ}
    (pProg : Program) (st₀ : State) (lA lB : List ℕ)
    (h4 : st₀.regs 4 = outFAddr) (h5 : st₀.regs 5 = outLenAddr)
    (h10 : st₀.regs 10 = unA) (h11 : st₀.regs 11 = unB)
    (h19 : st₀.regs 19 = lA.length) (h20 : st₀.regs 20 = lB.length)
    (hmin_le : min lA.length lB.length ≤ e)
    (hLA : ListAt st₀.mem unA lA) (hLB : ListAt st₀.mem unB lB)
    (hdFA : DisjointRange outFAddr (2 * e) unA lA.length)
    (hdFB : DisjointRange outFAddr (2 * e) unB lB.length)
    (hdFL : DisjointRange outFAddr (2 * e) outLenAddr 1)
    (hwUA : unA + lA.length < 2 ^ w) (hwUB : unB + lB.length < 2 ^ w)
    (hwOF : outFAddr + 2 * e < 2 ^ w) (hwOL : outLenAddr < 2 ^ w)
    (hwE : 4 * e + 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) fcZipStmt
      (normalPost fun s' =>
        s'.mem outLenAddr = (lA.zip lB).length ∧
        EdgesAt s'.mem outFAddr (lA.zip lB) ∧
        (∀ a, (a < outFAddr ∨ outFAddr + 2 * e ≤ a) → a ≠ outLenAddr → s'.mem a = st₀.mem a) ∧
        (∀ r ≤ 15, s'.regs r = st₀.regs r))
      (fun _ => 50 * e + 40) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  set mF := min lA.length lB.length
  -- Step 1: compute reg 21 := min (reg 19) (reg 20)
  have hmin_triple : Triple w pProg (fun s => s = st₀)
      (.cond (.bin .lt (.reg 19) (.reg 20)) (.assign 21 (.reg 19)) (.assign 21 (.reg 20)))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧ s'.regs 21 = mF ∧ (∀ r ≤ 20, s'.regs r = st₀.regs r))
      (fun _ => 12) := by
    intro s1 ω1 hs1; subst s1
    by_cases hlt : lA.length < lB.length
    · let stA : State := { st₀ with regs := Function.update st₀.regs 21 lA.length }
      have hbr : Runs w pProg ω1 (.assign 21 (.reg 19)) st₀ .normal stA 2 :=
        runs_assign_iff.mpr ⟨lA.length, by simp [Expr.eval, h19], rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, stA, 6, runs_cond_iff.mpr ⟨1, 2,
          by simp [Expr.eval, BinOp.eval, h19, h20, hlt, hw1],
          by simp only [one_ne_zero, ↓reduceIte]; exact hbr,
          by simp [Expr.size]⟩, ?_, by dsimp; omega⟩
      exact ⟨rfl, by simp [stA, mF]; omega,
        fun r hr => Function.update_of_ne (by omega : r ≠ 21) _ _⟩
    · let stA : State := { st₀ with regs := Function.update st₀.regs 21 lB.length }
      have hbr : Runs w pProg ω1 (.assign 21 (.reg 20)) st₀ .normal stA 2 :=
        runs_assign_iff.mpr ⟨lB.length, by simp [Expr.eval, h20], rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, stA, 6, runs_cond_iff.mpr ⟨0, 2,
          by simp [Expr.eval, BinOp.eval, h19, h20, hlt],
          by simp only [↓reduceIte]; exact hbr,
          by simp [Expr.size]⟩, ?_, by dsimp; omega⟩
      exact ⟨rfl, by simp [stA, mF]; omega,
        fun r hr => Function.update_of_ne (by omega : r ≠ 21) _ _⟩
  refine runs_start_le ?_
  dsimp only [fcZipStmt]
  refine runs_seq_triple_le hmin_triple rfl ?_
  intro st1 ⟨h1_mem, h1_21, h1_r⟩
  -- Step 2: loop 0 .. mF copying (unA[i], unB[i]) to outFAddr[2*i, 2*i+1]
  have hloop := Triple.forRange_const (p := pProg) (r := 16) (lo := .const 0) (hi := .reg 21)
    (body :=
      .assign 17 (.load (.bin .add (.reg 10) (.reg 16))) ;;
      .assign 18 (.load (.bin .add (.reg 11) (.reg 16))) ;;
      .store (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 16))) (.reg 17) ;;
      .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 18))
    (P := fun s => s = st1)
    (Inv := fun i s =>
      s.regs 16 = i ∧
      EdgesAt s.mem outFAddr ((lA.zip lB).take i) ∧
      (∀ a, a < outFAddr ∨ outFAddr + 2 * e ≤ a → s.mem a = st₀.mem a) ∧
      (∀ r, r ≤ 15 ∨ r = 21 → s.regs r = st1.regs r))
    38 0 mF (Nat.zero_le mF) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun j hj => by simp at hj, fun _ _ => h1_mem ▸ rfl,
        fun r hr => Function.update_of_ne (by omega : r ≠ 16) _ _⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr21 : s.regs 21 = mF := by rw [hi.2.2.2 21 (Or.inr rfl), h1_21]
      simp [Expr.eval, hr21])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hEd, hfr, hkr⟩
      have hiA : i < lA.length := by omega
      have hiB : i < lB.length := by omega
      have hiZ : i < (lA.zip lB).length := by rw [List.length_zip]; omega
      have hmA : s.mem (unA + i) = lA[i]'hiA := by
        rw [hfr _ (Or.elim hdFA (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hLA i hiA
      have hmB : s.mem (unB + i) = lB[i]'hiB := by
        rw [hfr _ (Or.elim hdFB (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hLB i hiB
      have hr4 : s.regs 4 = outFAddr := by rw [hkr 4 (Or.inl (by omega)), h1_r 4 (by omega), h4]
      have hr10 : s.regs 10 = unA := by rw [hkr 10 (Or.inl (by omega)), h1_r 10 (by omega), h10]
      have hr11 : s.regs 11 = unB := by rw [hkr 11 (Or.inl (by omega)), h1_r 11 (by omega), h11]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := lA[i]'hiA)
        (by simp [Expr.eval, BinOp.eval, hr10, hiReg, (by omega : unA + i < 2 ^ w), hmA]) ?_
      refine runs_seq_assign_le (v := lB[i]'hiB)
        (by simp [Expr.eval, BinOp.eval, hr11, hiReg, (by omega : unB + i < 2 ^ w), hmB]) ?_
      refine runs_seq_store_le (x := outFAddr + 2 * i) (v := lA[i]'hiA)
        (by simp [Expr.eval, BinOp.eval, hr4, hiReg, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : outFAddr + 2 * i < 2 ^ w)])
        (by simp [Expr.eval]) ?_
      let stA : State := {
        mem := Function.update s.mem (outFAddr + 2 * i) (lA[i]'hiA)
        regs := Function.update (Function.update s.regs 17 (lA[i]'hiA)) 18 (lB[i]'hiB)
        pos := s.pos }
      let stB : State := { stA with mem := Function.update stA.mem (outFAddr + 2 * i + 1) (lB[i]'hiB) }
      refine ⟨.normal, stB, 9, runs_store_iff.mpr ⟨outFAddr + 2 * i + 1, lB[i]'hiB,
          by simp [Expr.eval, BinOp.eval, hr4, hiReg, hw1, hw2, (by omega : 2 * i < 2 ^ w),
               (by omega : outFAddr + 2 * i < 2 ^ w), (by omega : outFAddr + 2 * i + 1 < 2 ^ w)],
          by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
      refine ⟨⟨by simp, ?_, ?_, fun r hr => by
          simp [stB, stA, Function.update_of_ne (by omega : r ≠ 16),
            Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 17),
            hkr r hr]⟩,
        by simp [stB, stA, hiReg]⟩
      · intro j hj
        rw [List.length_take] at hj
        have hji : j < i + 1 := by omega
        by_cases hlt : j < i
        · have hj1 : j < ((lA.zip lB).take i).length := by rw [List.length_take]; omega
          have heq : ((lA.zip lB).take (i + 1))[j] = ((lA.zip lB).take i)[j] := by simp
          rw [heq]; dsimp only [stB, stA]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hEd j hj1
        · have hjeq : j = i := by omega
          subst j
          have heq : ((lA.zip lB).take (i + 1))[i] = (lA[i]'hiA, lB[i]'hiB) := by simp
          rw [heq]; dsimp only [stB, stA]
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
                 by rw [Function.update_self]⟩
      · intro a ha; dsimp only [stB, stA]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha)
  refine runs_seq_triple_le hloop rfl ?_
  intro st2 ⟨_, h2_Ed, h2_fr, h2_kr⟩
  have htake : (lA.zip lB).take mF = lA.zip lB := by
    rw [List.take_of_length_le]; rw [List.length_zip]
  rw [htake] at h2_Ed
  refine runs_store_le (x := outLenAddr) (v := mF)
    (by simp [Expr.eval, h2_kr 5 (Or.inl (by omega)), h1_r 5 (by omega), h5])
    (by simp [Expr.eval, h2_kr 21 (Or.inr rfl), h1_21]) ?_
    (by simp [Expr.size]; omega)
  refine ⟨by simp [mF, List.length_zip], ?_, ?_, fun r hr => by
      simp [h2_kr r (Or.inl hr), h1_r r (by omega)]⟩
  · intro j hj
    have hj_lt : j < e := by rw [List.length_zip] at hj; omega
    dsimp only
    rw [Function.update_of_ne (disjointRange_ne hdFL (by omega) (by omega) (by omega) (by omega)),
        Function.update_of_ne (disjointRange_ne hdFL (by omega) (by omega) (by omega) (by omega))]
    exact h2_Ed j hj
  · intro a haF haL; dsimp only
    rw [Function.update_of_ne haL]
    exact h2_fr a haF

/-- Specification of `fakeCompletionProc`. -/
theorem fakeCompletionProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [fakeCompletionProc]) :
    MeetsContract w pProg b (fakeCompletionContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨e, pairsAddr, mM, mAddr, outFAddr, outLenAddr, h, A_list, B_list, M, rfl,
    hAB_len, hA_lt, hB_lt, hSP, hlenM, hM_lt, hEdgesM, hzero, hpH, hmH, hofH, holH,
    hdFP, hdFM, hdFL, hdLP, hdLM, hwH, hwE, hwM⟩
  unfold fakeCompletionSpace at hwH
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  set A := A_list.toFinset
  set B := B_list.toFinset
  set SA := A \ (M.map Prod.fst).toFinset
  set SB := B \ (M.map Prod.snd).toFinset
  have hSA_sub : SA ⊆ Finset.range (2 * e) := fun p hp =>
    Finset.mem_range.mpr (hA_lt p (List.mem_toFinset.mp (Finset.mem_sdiff.mp hp).1))
  have hSB_sub : SB ⊆ Finset.range (2 * e) := fun p hp =>
    Finset.mem_range.mpr (hB_lt p (List.mem_toFinset.mp (Finset.mem_sdiff.mp hp).1))
  set lA := (List.range (2 * e)).filter fun p => decide (p ∈ SA)
  set lB := (List.range (2 * e)).filter fun p => decide (p ∈ SB)
  have hlA_eq : lA = SA.sort (· ≤ ·) := list_range_filter_eq_finset_sort hSA_sub
  have hlB_eq : lB = SB.sort (· ≤ ·) := list_range_filter_eq_finset_sort hSB_sub
  have hlA_le : lA.length ≤ A_list.length := by
    rw [hlA_eq, Finset.length_sort]
    exact (Finset.card_le_card Finset.sdiff_subset).trans (List.toFinset_card_le A_list)
  have hlB_le : lB.length ≤ B_list.length := by
    rw [hlB_eq, Finset.length_sort]
    exact (Finset.card_le_card Finset.sdiff_subset).trans (List.toFinset_card_le B_list)
  have hmin_le : min lA.length lB.length ≤ e := by omega
  set st0 := startState [e, pairsAddr, mM, mAddr, outFAddr, outLenAddr, h] mem pos
  refine runs_start_le ?_
  dsimp only [fakeCompletionProc]
  -- Stage 1: fcSetup1
  refine runs_seq_triple_le
    (fcSetup1_triple (e := e) (pairsAddr := pairsAddr) (h := h) pProg st0 rfl rfl hwH hwE) rfl ?_
  intro st1 ⟨h1_mem, h1_7, h1_8, h1_9, h1_10, h1_11, h1_r⟩
  -- Stage 2: fcSetup2
  refine runs_seq_triple_le
    (fcSetup2_triple (pairsAddr := pairsAddr) pProg st1 A_list B_list
      (by rw [h1_r 1 (by omega)]; rfl) (by rw [h1_mem]; exact hSP) (by omega) hw2) rfl ?_
  intro st2 ⟨h2_mem, h2_12, h2_13, h2_14, h2_15, h2_r⟩
  have h2_mem0 : st2.mem = mem := by rw [h2_mem, h1_mem]; rfl
  -- Stage 3: markVerts A into flagA (h)
  refine runs_seq_triple_le
    (markVerts_triple (n := 2 * e) (len := A_list.length) (listAddr := pairsAddr + 2)
      (locAddr := h) (val := 1) pProg st2 A_list (by decide)
      h2_12 h2_13 (by rw [h2_r 8 (by omega), h1_8]) rfl hA_lt
      (by rw [h2_mem0]; exact hSP.2.2.1) (Or.inr (by omega)) (by omega) (by omega) hw1 hw1) rfl ?_
  intro st3 ⟨h3_mark, h3_fr, h3_kr⟩
  have h3_r : ∀ r ≤ 15, st3.regs r = st2.regs r := fun r hr => h3_kr r (by omega) (by omega)
  have h3_bList : ListAt st3.mem (pairsAddr + 3 + A_list.length) B_list := by
    intro j hj
    rw [h3_fr _ (fun u hu => by omega), h2_mem0]
    exact hSP.2.2.2.2 j hj
  -- Stage 4: markVerts B into flagB (h + 2 * e)
  refine runs_seq_triple_le
    (markVerts_triple (n := 2 * e) (len := B_list.length)
      (listAddr := pairsAddr + 3 + A_list.length) (locAddr := h + 2 * e) (val := 1)
      pProg st3 B_list (by decide)
      (by rw [h3_r 14 (by omega), h2_14]) (by rw [h3_r 15 (by omega), h2_15])
      (by rw [h3_r 9 (by omega), h2_r 9 (by omega), h1_9]) rfl hB_lt h3_bList
      (Or.inr (by omega)) (by omega) (by omega) hw1 hw1) rfl ?_
  intro st4 ⟨h4_mark, h4_fr, h4_kr⟩
  have h4_r : ∀ r ≤ 15, st4.regs r = st2.regs r := fun r hr => by
    rw [h4_kr r (by omega) (by omega), h3_r r hr]
  have h4_edgesM : EdgesAt st4.mem mAddr M := by
    intro j hj
    have hj' : j < mM := by omega
    rw [h4_fr _ (fun u hu => by omega), h3_fr _ (fun u hu => by omega), h2_mem0,
        h4_fr _ (fun u hu => by omega), h3_fr _ (fun u hu => by omega), h2_mem0]
    exact hEdgesM j hj
  -- Stage 5: fcUnmarkStmt
  refine runs_seq_triple_le
    (fcUnmark_triple (e := e) (mM := mM) (mAddr := mAddr) (flagA := h) (flagB := h + 2 * e)
      pProg st4 M
      (by rw [h4_r 2 (by omega), h2_r 2 (by omega), h1_r 2 (by omega)]; rfl)
      (by rw [h4_r 3 (by omega), h2_r 3 (by omega), h1_r 3 (by omega)]; rfl)
      (by rw [h4_r 8 (by omega), h2_r 8 (by omega), h1_8])
      (by rw [h4_r 9 (by omega), h2_r 9 (by omega), h1_9])
      hlenM hM_lt h4_edgesM (Or.inr hmH) (Or.inr (by omega)) (Or.inl (by omega))
      (by omega) (by omega) (by omega) hw2) rfl ?_
  intro st5 ⟨h5_clr, h5_fr, h5_kr⟩
  have h5_r : ∀ r ≤ 15, st5.regs r = st2.regs r := fun r hr => by rw [h5_kr r hr, h4_r r hr]
  have h5_flagA : ∀ p < 2 * e, 0 < st5.mem (h + p) ↔ p ∈ SA := by
    intro p hp
    by_cases hpM : p ∈ (M.map Prod.fst).toFinset
    · rcases List.mem_map.mp (List.mem_toFinset.mp hpM) with ⟨ed, hed, rfl⟩
      have h0 := (h5_clr ed hed).1
      simp [SA, hpM, h0]
    · have hneM : ∀ ed ∈ M, h + p ≠ h + ed.1 ∧ h + p ≠ h + 2 * e + ed.2 := by
        intro ed hed
        refine ⟨fun hEq => hpM (List.mem_toFinset.mpr (List.mem_map.mpr ⟨ed, hed, by omega⟩)),
                by omega⟩
      rw [h5_fr (h + p) hneM, h4_fr (h + p) (fun u hu => by omega)]
      by_cases hpA : p ∈ A
      · have h1 := h3_mark p (List.mem_toFinset.mp hpA)
        simp [SA, hpA, hpM, h1]
      · have h0 : st3.mem (h + p) = 0 := by
          rw [h3_fr (h + p) (fun u hu hEq => hpA (List.mem_toFinset.mpr ((by omega : u = p) ▸ hu))), h2_mem0]
          exact hzero (h + p) (by omega)
        simp [SA, hpA, h0]
  have h5_flagB : ∀ p < 2 * e, 0 < st5.mem (h + 2 * e + p) ↔ p ∈ SB := by
    intro p hp
    by_cases hpM : p ∈ (M.map Prod.snd).toFinset
    · rcases List.mem_map.mp (List.mem_toFinset.mp hpM) with ⟨ed, hed, rfl⟩
      have h0 := (h5_clr ed hed).2
      simp [SB, hpM, h0]
    · have hneM : ∀ ed ∈ M, h + 2 * e + p ≠ h + ed.1 ∧ h + 2 * e + p ≠ h + 2 * e + ed.2 := by
        intro ed hed
        have hlt := hM_lt ed hed
        refine ⟨by omega, fun hEq => hpM (List.mem_toFinset.mpr (List.mem_map.mpr ⟨ed, hed, by omega⟩))⟩
      rw [h5_fr (h + 2 * e + p) hneM]
      by_cases hpB : p ∈ B
      · have h1 := h4_mark p (List.mem_toFinset.mp hpB)
        simp [SB, hpB, hpM, h1]
      · have h0 : st4.mem (h + 2 * e + p) = 0 := by
          rw [h4_fr (h + 2 * e + p) (fun u hu hEq => hpB (List.mem_toFinset.mpr ((by omega : u = p) ▸ hu))),
            h3_fr (h + 2 * e + p) (fun u hu => by have := hA_lt u hu; omega), h2_mem0]
          exact hzero (h + 2 * e + p) (by omega)
        simp [SB, hpB, h0]
  -- Stage 6: fcCollectStmt (two collectFlagStmt calls)
  have hCollect : Triple w pProg (fun s => s = st5) fcCollectStmt
      (normalPost fun s' =>
        s'.regs 19 = lA.length ∧
        s'.regs 20 = lB.length ∧
        ListAt s'.mem (h + 4 * e) lA ∧
        ListAt s'.mem (h + 6 * e) lB ∧
        (∀ a, (a < h + 4 * e ∨ h + 6 * e ≤ a) → (a < h + 6 * e ∨ h + 8 * e ≤ a) → s'.mem a = st5.mem a) ∧
        (∀ r ≤ 15, s'.regs r = st5.regs r))
      (fun _ => 200 * e + 60) := by
    intro s ω hs; subst s
    refine runs_start_le ?_
    dsimp only [fcCollectStmt]
    refine runs_seq_triple_le
      (collectFlag_triple (w := w) (n := 2 * e) (flagAddr := h) (outAddr := h + 4 * e)
        (rLen := 7) (rFlag := 8) (rOut := 10) (rI := 16) (rVal := 17) (rCnt := 19)
        pProg st5 SA (by decide)
        (by rw [h5_r 7 (by omega), h2_r 7 (by omega), h1_7])
        (by rw [h5_r 8 (by omega), h2_r 8 (by omega), h1_8])
        (by rw [h5_r 10 (by omega), h2_r 10 (by omega), h1_10])
        h5_flagA (Or.inr (by omega)) (by omega) (by omega) (by omega)) rfl ?_
    intro st6 ⟨h6_19, h6_LA, h6_fr, h6_kr⟩
    have h6_r : ∀ r ≤ 15, st6.regs r = st2.regs r := fun r hr => by
      rw [h6_kr r (by omega) (by omega) (by omega), h5_r r hr]
    have h6_flagB : ∀ p < 2 * e, 0 < st6.mem (h + 2 * e + p) ↔ p ∈ SB := by
      intro p hp; rw [h6_fr (h + 2 * e + p) (Or.inl (by omega))]; exact h5_flagB p hp
    refine runs_triple_le
      (collectFlag_triple (w := w) (n := 2 * e) (flagAddr := h + 2 * e) (outAddr := h + 6 * e)
        (rLen := 7) (rFlag := 9) (rOut := 11) (rI := 16) (rVal := 17) (rCnt := 20)
        pProg st6 SB (by decide)
        (by rw [h6_r 7 (by omega), h2_r 7 (by omega), h1_7])
        (by rw [h6_r 9 (by omega), h2_r 9 (by omega), h1_9])
        (by rw [h6_r 11 (by omega), h2_r 11 (by omega), h1_11])
        h6_flagB (Or.inr (by omega)) (by omega) (by omega) (by omega)) rfl
      (fun o st7 h7 => by
        cases o with
        | returned _ => exact False.elim h7
        | normal =>
          rcases h7 with ⟨h7_20, h7_LB, h7_fr, h7_kr⟩
          refine ⟨by rw [h7_kr 19 (by omega) (by omega) (by omega), h6_19], h7_20,
            fun j hj => by
              have hj_lt : j < 2 * e := by omega
              rw [h7_fr (h + 4 * e + j) (Or.inl (by omega))]; exact h6_LA j hj,
            h7_LB,
            fun a haA haB => by rw [h7_fr a (by omega), h6_fr a (by omega)],
            fun r hr => by
              rw [h7_kr r (by omega) (by omega) (by omega),
                  h6_kr r (by omega) (by omega) (by omega)]⟩)
      (by omega)
  refine runs_seq_triple_le hCollect rfl ?_
  intro st7 ⟨h7_19, h7_20, h7_LA, h7_LB, h7_fr, h7_kr⟩
  have h7_r : ∀ r ≤ 15, st7.regs r = st2.regs r := fun r hr => by rw [h7_kr r hr, h5_r r hr]
  -- Stage 7: fcZipStmt
  refine runs_seq_triple_le
    (fcZip_triple (e := e) (unA := h + 4 * e) (unB := h + 6 * e)
      (outFAddr := outFAddr) (outLenAddr := outLenAddr) pProg st7 lA lB
      (by rw [h7_r 4 (by omega), h2_r 4 (by omega), h1_r 4 (by omega)]; rfl)
      (by rw [h7_r 5 (by omega), h2_r 5 (by omega), h1_r 5 (by omega)]; rfl)
      (by rw [h7_r 10 (by omega), h2_r 10 (by omega), h1_10])
      (by rw [h7_r 11 (by omega), h2_r 11 (by omega), h1_11])
      h7_19 h7_20 hmin_le h7_LA h7_LB
      (Or.inl (by omega)) (Or.inl (by omega)) hdFL
      (by omega) (by omega) (by omega) (by omega) hwE) rfl ?_
  intro st8 ⟨h8_len, h8_Ed, h8_fr, h8_kr⟩
  -- Return h + 8 * e
  refine runs_ret_le (v := h + 8 * e)
    (by simp [Expr.eval, BinOp.eval, h8_kr 11 (by omega), h7_r 11 (by omega), h2_r 11 (by omega),
          h1_11, h8_kr 7 (by omega), h7_r 7 (by omega), h2_r 7 (by omega), h1_7,
          (by omega : h + 6 * e + 2 * e < 2 ^ w)]; omega) ?_ ?_
  · dsimp only [fakeCompletionContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadAB : readSinglePair mem pairsAddr = (A, B) :=
      readSinglePair_eq_of_singlePairAt hSP
    have hreadM : readEdges mem mAddr mM = M := by
      rw [← hlenM]; exact readEdges_eq_of_edgesAt hEdgesM
    have hFC_eq : fakeCompletion A B M = lA.zip lB := by
      unfold fakeCompletion; rw [hlA_eq, hlB_eq]
    simp only [hreadAB, hreadM, hFC_eq]
    refine ⟨rfl, ?_, h8_len, h8_Ed, ?_⟩
    · intro a ha
      rw [h8_fr a (Or.inr (by omega)) (by omega),
          h7_fr a (Or.inr (by omega)) (Or.inr (by omega)),
          h5_fr a (fun ed hed => by have := hM_lt ed hed; omega),
          h4_fr a (fun u hu => by have := hB_lt u hu; omega),
          h3_fr a (fun u hu => by have := hA_lt u hu; omega),
          h2_mem0]
      exact hzero a (by omega)
    · intro a haH haF haL
      rw [h8_fr a haF haL, h7_fr a (Or.inl (by omega)) (Or.inl (by omega)),
          h5_fr a (fun ed hed => by omega), h4_fr a (fun u hu => by omega),
          h3_fr a (fun u hu => by omega), h2_mem0]
  · simp only [fakeCompletionContract, fakeCompletionCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega

end MinCostFlow.ExpanderDecomp
