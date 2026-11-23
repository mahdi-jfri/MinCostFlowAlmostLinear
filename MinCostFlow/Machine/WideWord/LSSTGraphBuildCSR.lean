module

public import MinCostFlow.Machine.WideWord.LSSTGraphBuildCSRBase
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic WordRAM CSR construction (`buildCSR`, phases 3–4 and contract)

This file completes the verification of `buildCSR` using `buildCSR_phase1` and `buildCSR_phase2`
from `LSSTGraphBuildCSRBase.lean`, proving the prefix-sum and adjacency-fill loop triples
(`buildCSR_phase3`, `buildCSR_phase4`) and `buildCSR_meetsContract`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM
open MinCostFlow
open MinCostFlow.LSF

private def offSpec (G : IndexedGraph) (u : ℕ) : ℕ :=
  ∑ x ∈ Finset.range u, (nlEndpoints G (nonloopEdges G)).count x

private lemma buildCSR_phase3 {G : IndexedGraph} {nlArr tailArr headArr heap w : ℕ}
    {mem : ℕ → ℕ} {p : Program}
    (hG : G.Valid) (hw16 : 16 ≤ 2 ^ w)
    (hnew_w : heap + 3 + 5 * G.n + 2 * (nonloopEdges G).length < 2 ^ w) :
    let nl := nonloopEdges G
    let nlCnt := nl.length
    let vListPtr := heap + 2
    let inactPtr := heap + 2 + G.n
    let offPtr := heap + 2 + 2 * G.n
    let adjPtr := heap + 3 + 3 * G.n
    let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
    let curPtr := heap + 3 + 4 * G.n + 2 * nlCnt
    let newHeap := heap + 3 + 5 * G.n + 2 * nlCnt
    Triple w p
      (fun st => CSRRegs G nlArr tailArr headArr heap st ∧
        st.regs 13 = 0 ∧ st.mem offPtr = 0 ∧
        (∀ x < G.n, st.mem (degPtr + x) = (nlEndpoints G nl).count x) ∧
        st.mem heap = (activeVertsList G).length ∧
        st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
        ListAt st.mem vListPtr (activeVertsList G) ∧
        ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
        (∀ a, a < heap ∨ (adjPtr ≤ a ∧ a < degPtr) ∨ newHeap ≤ a → st.mem a = mem a))
      buildCSRLoop3
      (normalPost fun st => CSRRegs G nlArr tailArr headArr heap st ∧
        (∀ x ≤ G.n, st.mem (offPtr + x) = offSpec G x) ∧
        (∀ x < G.n, st.mem (curPtr + x) = offSpec G x) ∧
        st.mem heap = (activeVertsList G).length ∧
        st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
        ListAt st.mem vListPtr (activeVertsList G) ∧
        ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
        (∀ a, a < heap ∨ (adjPtr ≤ a ∧ a < degPtr) ∨ newHeap ≤ a → st.mem a = mem a))
      (fun _ => G.n * 40 + 10) := by
  let nl := nonloopEdges G
  let nlCnt := nl.length
  let vListPtr := heap + 2
  let inactPtr := heap + 2 + G.n
  let offPtr := heap + 2 + 2 * G.n
  let adjPtr := heap + 3 + 3 * G.n
  let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
  let curPtr := heap + 3 + 4 * G.n + 2 * nlCnt
  let newHeap := heap + 3 + 5 * G.n + 2 * nlCnt
  have hw1 : 1 < 2 ^ w := by omega
  have hn_w : G.n < 2 ^ w := by omega
  have hend_bnd := nlEndpoints_bnd hG
  have hoff_bnd : ∀ u ≤ G.n, offSpec G u ≤ 2 * nlCnt := fun u hu => by
    calc offSpec G u ≤ offSpec G G.n := Finset.sum_le_sum_of_subset (Finset.range_mono hu)
      _ = 2 * nlCnt := nlEndpoints_sum_count hend_bnd
  let inv3 : ℕ → State → Prop := fun u st =>
    CSRRegs G nlArr tailArr headArr heap st ∧
    st.regs 12 = u ∧ st.regs 13 = offSpec G u ∧
    (∀ x ≤ u, st.mem (offPtr + x) = offSpec G x) ∧
    (∀ x < u, st.mem (curPtr + x) = offSpec G x) ∧
    (∀ x < G.n, st.mem (degPtr + x) = (nlEndpoints G nl).count x) ∧
    st.mem heap = (activeVertsList G).length ∧
    st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
    ListAt st.mem vListPtr (activeVertsList G) ∧
    ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
    (∀ a, a < heap ∨ (adjPtr ≤ a ∧ a < degPtr) ∨ newHeap ≤ a → st.mem a = mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 14 (.load (.bin .add (.reg 10) (.reg 12))) ;;
      .store (.bin .add (.reg 11) (.reg 12)) (.reg 13) ;;
      .assign 13 (.bin .add (.reg 13) (.reg 14)) ;;
      .store (.bin .add (.reg 8) (.bin .add (.reg 12) (.const 1))) (.reg 13))
    (P := fun st => CSRRegs G nlArr tailArr headArr heap st ∧
      st.regs 13 = 0 ∧ st.mem offPtr = 0 ∧
      (∀ x < G.n, st.mem (degPtr + x) = (nlEndpoints G nl).count x) ∧
      st.mem heap = (activeVertsList G).length ∧
      st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
      ListAt st.mem vListPtr (activeVertsList G) ∧
      ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
      (∀ a, a < heap ∨ (adjPtr ≤ a ∧ a < degPtr) ∨ newHeap ≤ a → st.mem a = mem a))
    (Inv := inv3)
    30 0 G.n (Nat.zero_le G.n) hw1 (fun _ => hn_w)
    (fun st ⟨hregs, h13, ho0, hdeg, hh0, hh1, hvL, hiL, hfr⟩ =>
      ⟨by eval_expr, csrRegs_update_ge12 (by omega) hregs, by simp,
        by dsimp only; rw [Function.update_of_ne (by omega), h13]; rfl,
        fun x hx => by
          have hxz : x = 0 := by omega
          rw [hxz, Nat.add_zero]
          exact ho0,
        fun _ h => absurd h (Nat.not_lt_zero _), hdeg, hh0, hh1, hvL, hiL, hfr⟩)
    (fun _ st _ _ hi => hi.2.1)
    (fun _ st _ _ hi => by have h0 := hi.1.r0; eval_expr)
    (fun u _ hult => by
      intro st _ ⟨hregs, h12, h13, hoff, hcur, hdeg, hh0, hh1, hvL, hiL, hfr⟩
      have hnl_len : nlCnt = (nonloopEdges G).length := rfl
      have hdu_eq := hdeg u hult
      have hsum_step : offSpec G u + (nlEndpoints G nl).count u = offSpec G (u + 1) := by
        dsimp only [offSpec]; rw [Finset.sum_range_succ]
      have hacc_w : offSpec G u + (nlEndpoints G nl).count u < 2 ^ w := by
        rw [hsum_step]; have := hoff_bnd (u + 1) hult; omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hregs.r10) (Expr.eval_reg_of_eq h12)
          (by omega)) (rfl : st.mem (degPtr + u) = _)) ?_
      have hregs1 := csrRegs_update_ge12 (r := 14) (v := st.mem (degPtr + u)) (by omega) hregs
      refine runs_seq_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq hregs1.r11)
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), h12] : _ = u))
          (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), h13] : _ = offSpec G u)) ?_
      have hregs2 := csrRegs_with_mem
        (m' := Function.update st.mem (curPtr + u) (offSpec G u)) hregs1
      refine runs_seq_assign_le (Expr.eval_add
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), h13] : _ = offSpec G u))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self, hdu_eq] : _ = (nlEndpoints G nl).count u))
        hacc_w) ?_
      have hregs3 := csrRegs_update_ge12 (r := 13) (v := offSpec G u + (nlEndpoints G nl).count u)
        (by omega) hregs2
      refine runs_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq hregs3.r8)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h12] : _ = u))
            (Expr.eval_const (by omega)) (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self, hsum_step] : _ = offSpec G (u + 1))) ?_ ?_
      · dsimp only
        have hregs4 := csrRegs_with_mem
          (m' := Function.update (Function.update st.mem (curPtr + u) (offSpec G u))
            (offPtr + (u + 1)) (offSpec G (u + 1))) hregs3
        have hvlen_le : (activeVertsList G).length ≤ G.n := by
          have := List.length_filter_le
            (fun u => (nonloopEdges G).any (fun e => G.tail e == u || G.head e == u)) (List.range G.n)
          simpa [activeVertsList] using this
        have hilen_le : (inactiveVertsList G.n (activeVertsList G)).length ≤ G.n := by
          have := List.length_filter_le (fun u => !(activeVertsList G).contains u) (List.range G.n)
          simpa [inactiveVertsList] using this
        refine ⟨⟨csrRegs_update_ge12 (r := 12) (v := u + 1) (by omega) hregs4,
          by simp, by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self, hsum_step],
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h12]⟩
        · intro x hx
          dsimp only
          by_cases hxu : x = u + 1
          · subst hxu; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [offPtr, curPtr] at *; omega)]
            exact hoff x (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by dsimp only [offPtr, curPtr] at *; omega)]
          by_cases hxu : x = u
          · subst hxu; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hcur x (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by dsimp only [offPtr, degPtr] at *; omega),
            Function.update_of_ne (by dsimp only [curPtr, degPtr] at *; omega)]
          exact hdeg x hx
        · dsimp only
          rw [Function.update_of_ne (by dsimp only [offPtr] at *; omega),
            Function.update_of_ne (by dsimp only [curPtr] at *; omega)]; exact hh0
        · dsimp only
          rw [Function.update_of_ne (by dsimp only [offPtr] at *; omega),
            Function.update_of_ne (by dsimp only [curPtr] at *; omega)]; exact hh1
        · exact listAt_congr' (fun i hi => by
            dsimp only
            rw [Function.update_of_ne (by dsimp only [offPtr, vListPtr] at *; omega),
              Function.update_of_ne (by dsimp only [curPtr, vListPtr] at *; omega)]) hvL
        · exact listAt_congr' (fun i hi => by
            dsimp only
            rw [Function.update_of_ne (by dsimp only [offPtr, inactPtr] at *; omega),
              Function.update_of_ne (by dsimp only [curPtr, inactPtr] at *; omega)]) hiL
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by dsimp only [offPtr, adjPtr, degPtr, curPtr, newHeap] at *; omega),
            Function.update_of_ne (by dsimp only [offPtr, adjPtr, degPtr, curPtr, newHeap] at *; omega)]
          exact hfr a ha
      · wram_cost)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨hregs, _, _, hoff, hcur, _, hh0, hh1, hvL, hiL, hfr⟩
      exact ⟨hregs, hoff, hcur, hh0, hh1, hvL, hiL, hfr⟩
  · intro st _; simp only [Expr.size_reg, Expr.size_const]; omega

private lemma buildCSR_phase4 {G : IndexedGraph} {nlArr tailArr headArr heap w : ℕ}
    {mem : ℕ → ℕ} {p : Program}
    (hG : G.Valid) (hw16 : 16 ≤ 2 ^ w)
    (hnl_h : nlArr + (nonloopEdges G).length ≤ heap)
    (htl_h : tailArr + G.m ≤ heap) (hhd_h : headArr + G.m ≤ heap)
    (hnew_w : heap + 3 + 5 * G.n + 2 * (nonloopEdges G).length < 2 ^ w)
    (hnlm : ListAt mem nlArr (nonloopEdges G))
    (htm : ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhm : ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i)) :
    let nl := nonloopEdges G
    let nlCnt := nl.length
    let vListPtr := heap + 2
    let inactPtr := heap + 2 + G.n
    let offPtr := heap + 2 + 2 * G.n
    let adjPtr := heap + 3 + 3 * G.n
    let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
    let curPtr := heap + 3 + 4 * G.n + 2 * nlCnt
    let newHeap := heap + 3 + 5 * G.n + 2 * nlCnt
    Triple w p
      (fun st => CSRRegs G nlArr tailArr headArr heap st ∧
        (∀ x ≤ G.n, st.mem (offPtr + x) = offSpec G x) ∧
        (∀ x < G.n, st.mem (curPtr + x) = offSpec G x) ∧
        st.mem heap = (activeVertsList G).length ∧
        st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
        ListAt st.mem vListPtr (activeVertsList G) ∧
        ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
        (∀ a, a < heap ∨ (adjPtr ≤ a ∧ a < degPtr) ∨ newHeap ≤ a → st.mem a = mem a))
      buildCSRLoop4
      (normalPost fun st => CSRRegs G nlArr tailArr headArr heap st ∧
        CSRAdjacencySpec G st.mem offPtr adjPtr ∧
        st.mem heap = (activeVertsList G).length ∧
        st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
        ListAt st.mem vListPtr (activeVertsList G) ∧
        ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
        (∀ a, a < heap ∨ newHeap ≤ a → st.mem a = mem a))
      (fun _ => nlCnt * 85 + 10) := by
  let nl := nonloopEdges G
  let nlCnt := nl.length
  let vListPtr := heap + 2
  let inactPtr := heap + 2 + G.n
  let offPtr := heap + 2 + 2 * G.n
  let adjPtr := heap + 3 + 3 * G.n
  let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
  let curPtr := heap + 3 + 4 * G.n + 2 * nlCnt
  let newHeap := heap + 3 + 5 * G.n + 2 * nlCnt
  have hnl_len : nlCnt = (nonloopEdges G).length := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hnlCnt_w : nlCnt < 2 ^ w := by omega
  have hend_bnd := nlEndpoints_bnd hG
  have hoff_bnd : ∀ u ≤ G.n, offSpec G u ≤ 2 * nlCnt := fun u hu => by
    calc offSpec G u ≤ offSpec G G.n := Finset.sum_le_sum_of_subset (Finset.range_mono hu)
      _ = 2 * nlCnt := nlEndpoints_sum_count hend_bnd
  let seen : ℕ → ℕ → ℕ := fun i x => (nlEndpoints G (nl.take i)).count x
  let inv4 : ℕ → State → Prop := fun i st =>
    CSRRegs G nlArr tailArr headArr heap st ∧
    st.regs 12 = i ∧
    (∀ x < G.n, st.mem (curPtr + x) = offSpec G x + seen i x) ∧
    (∀ x < G.n, ∀ q, offSpec G x ≤ q → q < offSpec G x + seen i x →
      ∃ e ∈ nl, (G.tail e = x ∧ st.mem (adjPtr + q) = G.head e) ∨
        (G.head e = x ∧ st.mem (adjPtr + q) = G.tail e)) ∧
    (∀ j, j < i → ∀ hj : j < nlCnt,
      (∃ q, offSpec G (G.tail (nl[j]'hj)) ≤ q ∧
        q < offSpec G (G.tail (nl[j]'hj)) + seen i (G.tail (nl[j]'hj)) ∧
        st.mem (adjPtr + q) = G.head (nl[j]'hj)) ∧
      (∃ q, offSpec G (G.head (nl[j]'hj)) ≤ q ∧
        q < offSpec G (G.head (nl[j]'hj)) + seen i (G.head (nl[j]'hj)) ∧
        st.mem (adjPtr + q) = G.tail (nl[j]'hj))) ∧
    (∀ x ≤ G.n, st.mem (offPtr + x) = offSpec G x) ∧
    st.mem heap = (activeVertsList G).length ∧
    st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
    ListAt st.mem vListPtr (activeVertsList G) ∧
    ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
    (∀ a, a < heap ∨ newHeap ≤ a → st.mem a = mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 13 (.load (.bin .add (.reg 2) (.reg 12))) ;;
      .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
      .assign 15 (.load (.bin .add (.reg 4) (.reg 13))) ;;
      .assign 16 (.load (.bin .add (.reg 11) (.reg 14))) ;;
      .store (.bin .add (.reg 9) (.reg 16)) (.reg 15) ;;
      .store (.bin .add (.reg 11) (.reg 14)) (.bin .add (.reg 16) (.const 1)) ;;
      .assign 17 (.load (.bin .add (.reg 11) (.reg 15))) ;;
      .store (.bin .add (.reg 9) (.reg 17)) (.reg 14) ;;
      .store (.bin .add (.reg 11) (.reg 15)) (.bin .add (.reg 17) (.const 1)))
    (P := fun st => CSRRegs G nlArr tailArr headArr heap st ∧
      (∀ x ≤ G.n, st.mem (offPtr + x) = offSpec G x) ∧
      (∀ x < G.n, st.mem (curPtr + x) = offSpec G x) ∧
      st.mem heap = (activeVertsList G).length ∧
      st.mem (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
      ListAt st.mem vListPtr (activeVertsList G) ∧
      ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
      (∀ a, a < heap ∨ (adjPtr ≤ a ∧ a < degPtr) ∨ newHeap ≤ a → st.mem a = mem a))
    (Inv := inv4)
    72 0 nlCnt (Nat.zero_le nlCnt) hw1 (fun _ => hnlCnt_w)
    (fun st ⟨hregs, hoff, hcur, hh0, hh1, hvL, hiL, hfr⟩ =>
      ⟨by eval_expr, csrRegs_update_ge12 (by omega) hregs, by simp,
        fun x hx => by simp [seen, nlEndpoints, hcur x hx],
        fun _ _ _ h1 h2 => by simp [seen, nlEndpoints] at h2; omega,
        fun _ hj => absurd hj (Nat.not_lt_zero _),
        hoff, hh0, hh1, hvL, hiL, fun a ha => hfr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (Or.inr h)])⟩)
    (fun _ st _ _ hi => hi.2.1)
    (fun _ st _ _ hi => by have h1 := hi.1.r1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨hregs, h12, hcur, hwr, hproc, hoff4, qh0, qh1, qvL, qiL, hfr⟩
      have hei := mem_nonloopEdges_iff.mp (List.getElem_mem hilt)
      set e := nl[i]
      set u := G.tail e
      set v' := G.head e
      have hu_lt := (hG.2 e hei.1).1
      have hv_lt := (hG.2 e hei.1).2
      have huv : u ≠ v' := hei.2
      have hnli : st.mem (nlArr + i) = e := by rw [hfr _ (by omega)]; exact hnlm i hilt
      have hti : st.mem (tailArr + e) = u := by rw [hfr _ (by omega)]; exact mem_ofFn_eq htm hei.1
      have hhi : st.mem (headArr + e) = v' := by rw [hfr _ (by omega)]; exact mem_ofFn_eq hhm hei.1
      have htake : nl.take (i + 1) = nl.take i ++ [e] := List.take_succ_eq_append_getElem hilt
      have htake_le : ∀ x, seen (i + 1) x ≤ (nlEndpoints G nl).count x := fun _ => nlEndpoints_count_le
      have hseen_u : seen (i + 1) u = seen i u + 1 := by
        dsimp only [seen, nlEndpoints]
        rw [htake, List.flatMap_append, List.flatMap_singleton,
          List.count_append, List.count_cons, List.count_cons, List.count_nil]
        dsimp only [e, u, v'] at huv ⊢
        simp only [beq_iff_eq]
        split_ifs <;> omega
      have hseen_v : seen (i + 1) v' = seen i v' + 1 := by
        dsimp only [seen, nlEndpoints]
        rw [htake, List.flatMap_append, List.flatMap_singleton,
          List.count_append, List.count_cons, List.count_cons, List.count_nil]
        dsimp only [e, u, v'] at huv ⊢
        simp only [beq_iff_eq]
        split_ifs <;> omega
      have hseen_other : ∀ x, x ≠ u → x ≠ v' → seen (i + 1) x = seen i x := by
        intro x hxu hxv
        dsimp only [seen, nlEndpoints]
        rw [htake, List.flatMap_append, List.flatMap_singleton,
          List.count_append, List.count_cons, List.count_cons, List.count_nil]
        dsimp only [e, u, v'] at hxu hxv ⊢
        simp [beq_iff_eq, hxu.symm, hxv.symm]
      set pu := offSpec G u + seen i u
      set pv := offSpec G v' + seen i v'
      have hpu_eq : st.mem (curPtr + u) = pu := hcur u hu_lt
      have hpv_eq : st.mem (curPtr + v') = pv := hcur v' hv_lt
      have hpu_lt_n : pu < offSpec G (u + 1) := by
        have := htake_le u
        have hstep : offSpec G (u + 1) = offSpec G u + (nlEndpoints G nl).count u := by
          dsimp only [offSpec]; rw [Finset.sum_range_succ]
        omega
      have hpv_lt_n : pv < offSpec G (v' + 1) := by
        have := htake_le v'
        have hstep : offSpec G (v' + 1) = offSpec G v' + (nlEndpoints G nl).count v' := by
          dsimp only [offSpec]; rw [Finset.sum_range_succ]
        omega
      have hpu_lt_2nl : pu + 1 ≤ 2 * nlCnt := by have := hoff_bnd (u + 1) hu_lt; omega
      have hpv_lt_2nl : pv + 1 ≤ 2 * nlCnt := by have := hoff_bnd (v' + 1) hv_lt; omega
      have hmono : ∀ a b, a < b → offSpec G (a + 1) ≤ offSpec G b := fun a b hab =>
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      have hdisj_lt : ∀ {x y q}, x < G.n → y < G.n → x ≠ y →
          offSpec G x + seen i x < offSpec G (x + 1) →
          offSpec G y ≤ q → q < offSpec G (y + 1) → q ≠ offSpec G x + seen i x := by
        intro x y q _ _ hxy hstrict hq1 hq2 heq
        rcases lt_or_gt_of_ne hxy with h1 | h2
        · have := hmono x y h1; omega
        · have := hmono y x h2; omega
      have hdisj_slot : pu ≠ pv := by
        rcases lt_or_gt_of_ne huv with h1 | h2
        · have := hmono u v' h1; omega
        · have := hmono v' u h2; omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hregs.r2) (Expr.eval_reg_of_eq h12) (by omega)) hnli) ?_
      have hregs1 := csrRegs_update_ge12 (r := 13) (v := e) (by omega) hregs
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hregs1.r3)
          (Expr.eval_reg_of_eq (by simp : _ = e)) (by omega)) hti) ?_
      have hregs2 := csrRegs_update_ge12 (r := 14) (v := u) (by omega) hregs1
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r4)
          (Expr.eval_reg_of_eq (by simp : _ = e)) (by omega)) hhi) ?_
      have hregs3 := csrRegs_update_ge12 (r := 15) (v := v') (by omega) hregs2
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hregs3.r11)
          (Expr.eval_reg_of_eq (by simp : _ = u)) (by omega)) hpu_eq) ?_
      have hregs4 := csrRegs_update_ge12 (r := 16) (v := pu) (by omega) hregs3
      refine runs_seq_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq hregs4.r9) (Expr.eval_reg_of_eq (by simp : _ = pu))
          (by omega))
        (Expr.eval_reg_of_eq (by simp : _ = v')) ?_
      set m1 := Function.update st.mem (adjPtr + pu) v'
      have hregs5 := csrRegs_with_mem (m' := m1) hregs4
      refine runs_seq_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq hregs5.r11) (Expr.eval_reg_of_eq (by simp : _ = u))
          (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp : _ = pu)) (Expr.eval_const (by omega))
          (by omega)) ?_
      set m2 := Function.update m1 (curPtr + u) (pu + 1)
      have hregs6 := csrRegs_with_mem (m' := m2) hregs5
      have hm2_pv : m2 (curPtr + v') = pv := by
        dsimp only [m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega)]
        exact hpv_eq
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hregs6.r11) (Expr.eval_reg_of_eq (by simp : _ = v'))
          (by omega)) hm2_pv) ?_
      have hregs7 := csrRegs_update_ge12 (r := 17) (v := pv) (by omega) hregs6
      refine runs_seq_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq hregs7.r9) (Expr.eval_reg_of_eq (by simp : _ = pv))
          (by omega))
        (Expr.eval_reg_of_eq (by simp : _ = u)) ?_
      set m3 := Function.update m2 (adjPtr + pv) u
      have hregs8 := csrRegs_with_mem (m' := m3) hregs7
      refine runs_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq hregs8.r11) (Expr.eval_reg_of_eq (by simp : _ = v'))
          (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp : _ = pv)) (Expr.eval_const (by omega))
          (by omega)) ?_ ?_
      · dsimp only
        set m4 := Function.update m3 (curPtr + v') (pv + 1)
        have hregs9 := csrRegs_with_mem (m' := m4) hregs8
        have hnli_mem : e ∈ nl := List.getElem_mem hilt
        refine ⟨⟨csrRegs_update_ge12 (r := 12) (v := i + 1) (by omega) hregs9,
          by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), h12]⟩
        · intro x hx
          dsimp only [m4, m3, m2, m1]
          rw [Function.update_apply, Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega)]
          by_cases hxv : x = v'
          · subst hxv; dsimp only [pv]; simp [hseen_v]; omega
          · rw [ite_eq_right (by omega), Function.update_apply,
              Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega)]
            by_cases hxu : x = u
            · subst hxu; dsimp only [pu]; simp [hseen_u]; omega
            · rw [ite_eq_right (by omega), hseen_other x hxu hxv, hcur x hx]
        · intro x hx q hq1 hq2
          dsimp only [m4, m3, m2, m1]
          have hstep : offSpec G (x + 1) = offSpec G x + (nlEndpoints G nl).count x := by
            dsimp only [offSpec]; rw [Finset.sum_range_succ]
          have hq_2nl : q < 2 * nlCnt :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hq2
              ((Nat.add_le_add_left (htake_le x) _).trans_eq hstep.symm)) (hoff_bnd (x + 1) hx)
          rw [Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega)]
          by_cases hqv : adjPtr + q = adjPtr + pv
          · have hqeq : q = pv := by omega
            have hxv' : x = v' := by
              by_contra hne
              have hq_lt : q < offSpec G (x + 1) :=
                Nat.lt_of_lt_of_le hq2 ((Nat.add_le_add_left (htake_le x) _).trans_eq hstep.symm)
              exact absurd hqeq (hdisj_lt hv_lt hx (Ne.symm hne) hpv_lt_n hq1 hq_lt)
            subst hxv'; rw [hqv, Function.update_self]; exact ⟨e, hnli_mem, Or.inr ⟨rfl, rfl⟩⟩
          · rw [Function.update_of_ne hqv, Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega)]
            by_cases hqu : adjPtr + q = adjPtr + pu
            · have hqeq : q = pu := by omega
              have hxu' : x = u := by
                by_contra hne
                have hq_lt : q < offSpec G (x + 1) :=
                  Nat.lt_of_lt_of_le hq2 ((Nat.add_le_add_left (htake_le x) _).trans_eq hstep.symm)
                exact absurd hqeq (hdisj_lt hu_lt hx (Ne.symm hne) hpu_lt_n hq1 hq_lt)
              subst hxu'; rw [hqu, Function.update_self]; exact ⟨e, hnli_mem, Or.inl ⟨rfl, rfl⟩⟩
            · rw [Function.update_of_ne hqu]
              have hq_old : q < offSpec G x + seen i x := by
                by_cases hxu : x = u
                · subst hxu; rw [hseen_u] at hq2; omega
                · by_cases hxv : x = v'
                  · subst hxv; rw [hseen_v] at hq2; omega
                  · rw [hseen_other x hxu hxv] at hq2; exact hq2
              exact hwr x hx q hq1 hq_old
        · intro j hj hj_lt
          have hstep_u : ∀ (x q : ℕ), offSpec G x ≤ q → q < offSpec G x + seen i x →
              q < offSpec G x + seen (i + 1) x := fun x q h1 h2 => by
            by_cases hxu : x = u
            · subst hxu; rw [hseen_u]; omega
            · by_cases hxv : x = v'
              · subst hxv; rw [hseen_v]; omega
              · rw [hseen_other x hxu hxv]; omega
          by_cases hji : j = i
          · subst hji
            constructor
            · refine ⟨pu, by dsimp only [pu, u, e]; omega,
                by dsimp only [pu, u, e] at *; rw [hseen_u]; omega, ?_⟩
              dsimp only [m4, m3, m2, m1]
              rw [Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega),
                Function.update_of_ne (by dsimp [pu, pv]; omega),
                Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega),
                Function.update_self]
            · refine ⟨pv, by dsimp only [pv, v', e]; omega,
                by dsimp only [pv, v', e] at *; rw [hseen_v]; omega, ?_⟩
              dsimp only [m4, m3, m2, m1]
              rw [Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega),
                Function.update_self]
          · obtain ⟨⟨q1', hq1a, hq1b, hq1c⟩, ⟨q2', hq2a, hq2b, hq2c⟩⟩ := hproc j (by omega) hj_lt
            have hej := mem_nonloopEdges_iff.mp (List.getElem_mem hj_lt)
            have htj_lt := (hG.2 (nl[j]'hj_lt) hej.1).1
            have hhj_lt := (hG.2 (nl[j]'hj_lt) hej.1).2
            have hwrite_ok : ∀ {x q}, x < G.n → offSpec G x ≤ q → q < offSpec G x + seen i x →
                st.mem (adjPtr + q) = m4 (adjPtr + q) := by
              intro x q hx h1 h2
              have hxi : seen i x ≤ (nlEndpoints G nl).count x := nlEndpoints_count_le
              have hst : offSpec G (x + 1) = offSpec G x + (nlEndpoints G nl).count x := by
                dsimp only [offSpec]; rw [Finset.sum_range_succ]
              have hq_2nl : q < 2 * nlCnt :=
                Nat.lt_of_lt_of_le (by omega : q < offSpec G (x + 1)) (hoff_bnd (x + 1) hx)
              have hne_u : q ≠ pu := by
                by_cases hxu : x = u
                · subst hxu; omega
                · exact hdisj_lt hu_lt hx (Ne.symm hxu) hpu_lt_n h1 (by omega)
              have hne_v : q ≠ pv := by
                by_cases hxv : x = v'
                · subst hxv; omega
                · exact hdisj_lt hv_lt hx (Ne.symm hxv) hpv_lt_n h1 (by omega)
              dsimp only [m4, m3, m2, m1]
              rw [Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega),
                Function.update_of_ne (by omega),
                Function.update_of_ne (by dsimp [adjPtr, curPtr]; omega),
                Function.update_of_ne (by omega)]
            exact ⟨⟨q1', hq1a, hstep_u _ _ hq1a hq1b, (hwrite_ok htj_lt hq1a hq1b).symm.trans hq1c⟩,
              ⟨q2', hq2a, hstep_u _ _ hq2a hq2b, (hwrite_ok hhj_lt hq2a hq2b).symm.trans hq2c⟩⟩
        · intro x hx
          dsimp only [m4, m3, m2, m1]
          rw [Function.update_of_ne (by dsimp [offPtr, curPtr]; omega),
            Function.update_of_ne (by dsimp [offPtr, adjPtr]; omega),
            Function.update_of_ne (by dsimp [offPtr, curPtr]; omega),
            Function.update_of_ne (by dsimp [offPtr, adjPtr]; omega)]
          exact hoff4 x hx
        · dsimp only [m4, m3, m2, m1]
          rw [Function.update_of_ne (by dsimp [curPtr]; omega),
            Function.update_of_ne (by dsimp [adjPtr]; omega),
            Function.update_of_ne (by dsimp [curPtr]; omega),
            Function.update_of_ne (by dsimp [adjPtr]; omega)]
          exact qh0
        · dsimp only [m4, m3, m2, m1]
          rw [Function.update_of_ne (by dsimp [curPtr]; omega),
            Function.update_of_ne (by dsimp [adjPtr]; omega),
            Function.update_of_ne (by dsimp [curPtr]; omega),
            Function.update_of_ne (by dsimp [adjPtr]; omega)]
          exact qh1
        · have hvlen_le : (activeVertsList G).length ≤ G.n := by
            have := List.length_filter_le
              (fun u => (nonloopEdges G).any (fun e => G.tail e == u || G.head e == u)) (List.range G.n)
            simpa [activeVertsList] using this
          exact listAt_congr' (fun k hk => by
            dsimp only [m4, m3, m2, m1]
            rw [Function.update_of_ne (by dsimp [curPtr, vListPtr]; omega),
              Function.update_of_ne (by dsimp [adjPtr, vListPtr]; omega),
              Function.update_of_ne (by dsimp [curPtr, vListPtr]; omega),
              Function.update_of_ne (by dsimp [adjPtr, vListPtr]; omega)]) qvL
        · have hilen_le : (inactiveVertsList G.n (activeVertsList G)).length ≤ G.n := by
            have := List.length_filter_le (fun u => !(activeVertsList G).contains u) (List.range G.n)
            simpa [inactiveVertsList] using this
          exact listAt_congr' (fun k hk => by
            dsimp only [m4, m3, m2, m1]
            rw [Function.update_of_ne (by dsimp [curPtr, inactPtr]; omega),
              Function.update_of_ne (by dsimp [adjPtr, inactPtr]; omega),
              Function.update_of_ne (by dsimp [curPtr, inactPtr]; omega),
              Function.update_of_ne (by dsimp [adjPtr, inactPtr]; omega)]) qiL
        · intro a ha
          dsimp only [m4, m3, m2, m1]
          rw [Function.update_of_ne (by dsimp [newHeap, curPtr] at *; omega),
            Function.update_of_ne (by dsimp [newHeap, adjPtr] at *; omega),
            Function.update_of_ne (by dsimp [newHeap, curPtr] at *; omega),
            Function.update_of_ne (by dsimp [newHeap, adjPtr] at *; omega)]
          exact hfr a ha
      · wram_cost)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨hregs, _, _, hwr, hproc, hoff4, qh0, qh1, qvL, qiL, hfr⟩
      have hseen_all : ∀ x, seen nlCnt x = (nlEndpoints G nl).count x := fun x => by
        dsimp only [seen]; rw [List.take_length]
      have hstep_eq : ∀ x, offSpec G x + seen nlCnt x = offSpec G (x + 1) := fun x => by
        rw [hseen_all]; dsimp only [offSpec]; rw [Finset.sum_range_succ]
      refine ⟨hregs, ?_, qh0, qh1, qvL, qiL, hfr⟩
      · refine ⟨hoff4 0 (Nat.zero_le _), fun u hu => ?_, ?_, fun u hu q h1 h2 => ?_, fun e he => ?_⟩
        · dsimp only [offPtr] at hoff4
          rw [hoff4 u (by omega), hoff4 (u + 1) hu]
          exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
        · dsimp only [offPtr] at hoff4
          rw [hoff4 G.n (le_refl _)]; exact nlEndpoints_sum_count hend_bnd
        · dsimp only [offPtr] at hoff4
          rw [hoff4 u (by omega)] at h1
          rw [hoff4 (u + 1) hu, ← hstep_eq u] at h2
          exact hwr u hu q h1 h2
        · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
          have hgt := hproc j (by omega) hj
          have htj := (hG.2 (nl[j]'hj) (mem_nonloopEdges_iff.mp he).1).1
          have hhj := (hG.2 (nl[j]'hj) (mem_nonloopEdges_iff.mp he).1).2
          rcases hgt with ⟨⟨q1, hq1a, hq1b, hq1c⟩, ⟨q2, hq2a, hq2b, hq2c⟩⟩
          dsimp only [offPtr, adjPtr] at hoff4 ⊢
          refine ⟨⟨q1, ?_, ?_, hq1c⟩, ⟨q2, ?_, ?_, hq2c⟩⟩
          · rw [hoff4 _ htj.le]; exact hq1a
          · rw [hoff4 _ htj, ← hstep_eq _]; exact hq1b
          · rw [hoff4 _ hhj.le]; exact hq2a
          · rw [hoff4 _ hhj, ← hstep_eq _]; exact hq2b
  · intro st _; simp only [Expr.size_reg, Expr.size_const]; omega

/-! ### Top-level `buildCSR_meetsContract` -/

theorem buildCSR_meetsContract {G : IndexedGraph} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [buildCSR]) :
    MeetsContract w p b (buildCSRContract G w) := by
  have hproc : p.procs[b]? = some buildCSR := hp 0 (by simp)
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨nlArr, tailArr, headArr, heap, rfl, hG, hw16, hnl_h, htl_h, hhd_h, hnew_w,
    hnlm, htm, hhm, hz0⟩
  set nl := nonloopEdges G
  set nlCnt := nl.length
  set vListPtr := heap + 2
  set inactPtr := heap + 2 + G.n
  set offPtr := heap + 2 + 2 * G.n
  set adjPtr := heap + 3 + 3 * G.n
  set degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
  set curPtr := heap + 3 + 4 * G.n + 2 * nlCnt
  set newHeap := heap + 3 + 5 * G.n + 2 * nlCnt
  have hnl_len : nlCnt = (nonloopEdges G).length := rfl
  have hphase1 := @buildCSR_phase1 G nlArr tailArr headArr heap w mem p hG hw16 hnl_h htl_h hhd_h
    hnew_w hnlm htm hhm hz0
  have hphase2 := @buildCSR_phase2 G nlArr tailArr headArr heap w mem p hG hw16 hnew_w
  have hphase3 := @buildCSR_phase3 G nlArr tailArr headArr heap w mem p hG hw16 hnew_w
  have hphase4 := @buildCSR_phase4 G nlArr tailArr headArr heap w mem p hG hw16 hnl_h htl_h hhd_h
    hnew_w hnlm htm hhm
  refine runs_start_le ?_
  dsimp only [buildCSR]
  have s0 : (startState [G.n, nlCnt, nlArr, tailArr, headArr, heap] mem pos).regs 0 = G.n := rfl
  have s1 : (startState [G.n, nlCnt, nlArr, tailArr, headArr, heap] mem pos).regs 1 = nlCnt := rfl
  have s2 : (startState [G.n, nlCnt, nlArr, tailArr, headArr, heap] mem pos).regs 2 = nlArr := rfl
  have s3 : (startState [G.n, nlCnt, nlArr, tailArr, headArr, heap] mem pos).regs 3 = tailArr := rfl
  have s4 : (startState [G.n, nlCnt, nlArr, tailArr, headArr, heap] mem pos).regs 4 = headArr := rfl
  have s5 : (startState [G.n, nlCnt, nlArr, tailArr, headArr, heap] mem pos).regs 5 = heap := rfl
  refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq s5) (Expr.eval_const (by omega))
    (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_add
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self] : _ = heap + 2))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), s0] : _ = G.n))
    (by dsimp only [inactPtr, vListPtr] at *; omega)) ?_
  refine runs_seq_assign_le (Expr.eval_add
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self] : _ = heap + 2 + G.n))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), s0] : _ = G.n))
    (by dsimp only [offPtr, inactPtr, vListPtr] at *; omega)) ?_
  refine runs_seq_assign_le (Expr.eval_add
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self] : _ = heap + 2 + G.n + G.n))
    (Expr.eval_add
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), s0] : _ = G.n))
      (Expr.eval_const (by omega)) (by omega))
    (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_add
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self] : _ = heap + 2 + G.n + G.n + (G.n + 1)))
    (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), s1] : _ = nlCnt)) (by omega))
    (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_add
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self] : _ = heap + 2 + G.n + G.n + (G.n + 1) + 2 * nlCnt))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), s0] : _ = G.n))
    (by omega)) ?_
  have hregs0 : CSRRegs G nlArr tailArr headArr heap
      { regs := Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (startState [G.n, nlCnt, nlArr, tailArr, headArr, heap] mem pos).regs
            6 (heap + 2)) 7 (heap + 2 + G.n)) 8 (heap + 2 + G.n + G.n))
          9 (heap + 2 + G.n + G.n + (G.n + 1)))
          10 (heap + 2 + G.n + G.n + (G.n + 1) + 2 * nlCnt))
          11 (heap + 2 + G.n + G.n + (G.n + 1) + 2 * nlCnt + G.n)
        mem := mem, pos := pos } :=
    ⟨by simp [s0], by simp [s1]; rfl, by simp [s2], by simp [s3], by simp [s4], by simp [s5],
      by simp, by simp; try omega, by simp; try omega, by simp; try omega,
      by simp; try omega, by simp; try omega⟩
  have hvlen_le : (activeVertsList G).length ≤ G.n := by
    have := List.length_filter_le
      (fun u => (nonloopEdges G).any (fun e => G.tail e == u || G.head e == u)) (List.range G.n)
    simpa [activeVertsList] using this
  have hilen_le : (inactiveVertsList G.n (activeVertsList G)).length ≤ G.n := by
    have := List.length_filter_le (fun u => !(activeVertsList G).contains u) (List.range G.n)
    simpa [inactiveVertsList] using this
  refine runs_seq_triple_le hphase1 ⟨hregs0, rfl⟩ ?_
  · intro st₁ ⟨hregs1, hdeg1, hfr1⟩
    refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
    refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
    have hregs1' := csrRegs_update_ge12 (r := 14) (v := 0) (by omega)
      (csrRegs_update_ge12 (r := 13) (v := 0) (by omega) hregs1)
    refine runs_seq_triple_le hphase2
      ⟨hregs1', by simp, by simp, hdeg1, hfr1⟩ ?_
    · intro st₂ ⟨hregs2, h13_2, h14_2, hvL2, hiL2, hdeg2, hfr2⟩
      refine runs_seq_store_le (Expr.eval_reg_of_eq hregs2.r5) (Expr.eval_reg_of_eq h13_2) ?_
      refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r5)
        (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq h14_2) ?_
      refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
      refine runs_seq_store_le (Expr.eval_reg_of_eq hregs2.r8) (Expr.eval_const (by omega)) ?_
      have hregs3 := csrRegs_with_mem
        (m' := Function.update (Function.update (Function.update st₂.mem heap (activeVertsList G).length)
          (heap + 1) (inactiveVertsList G.n (activeVertsList G)).length) offPtr 0)
        (csrRegs_update_ge12 (r := 13) (v := 0) (by omega) hregs2)
      refine runs_seq_triple_le hphase3 ⟨hregs3, by simp, by simp,
        by intro x hx; dsimp only
           rw [Function.update_of_ne (by dsimp [offPtr, degPtr]; omega),
             Function.update_of_ne (by dsimp [degPtr]; omega),
             Function.update_of_ne (by dsimp [degPtr]; omega)]; exact hdeg2 x hx,
        by dsimp only; rw [Function.update_of_ne (by dsimp [offPtr]; omega),
             Function.update_of_ne (by omega), Function.update_self],
        by dsimp only; rw [Function.update_of_ne (by dsimp [offPtr]; omega), Function.update_self],
        listAt_congr' (fun i hi => by
          dsimp only; rw [Function.update_of_ne (by dsimp [offPtr, vListPtr]; omega),
            Function.update_of_ne (by dsimp [vListPtr]; omega),
            Function.update_of_ne (by dsimp [vListPtr]; omega)]) hvL2,
        listAt_congr' (fun i hi => by
          dsimp only; rw [Function.update_of_ne (by dsimp [offPtr, inactPtr]; omega),
            Function.update_of_ne (by dsimp [inactPtr]; omega),
            Function.update_of_ne (by dsimp [inactPtr]; omega)]) hiL2,
        fun a ha => by
          dsimp only
          rw [Function.update_of_ne (by dsimp [offPtr, adjPtr, degPtr, newHeap] at *; omega),
            Function.update_of_ne (by dsimp [adjPtr, degPtr, newHeap] at *; omega),
            Function.update_of_ne (by dsimp [adjPtr, degPtr, newHeap] at *; omega)]
          exact hfr2 a (by dsimp [offPtr, adjPtr, degPtr, newHeap, vListPtr] at *; omega)⟩ ?_
      · intro st₃ ⟨hregs4, hoff4, hcur4, hh0_4, hh1_4, hvL4, hiL4, hfr4⟩
        refine runs_seq_triple_le hphase4
          ⟨hregs4, hoff4, hcur4, hh0_4, hh1_4, hvL4, hiL4, hfr4⟩ ?_
        · intro st₄ ⟨hregs5, hadj, hh0_5, hh1_5, hvL5, hiL5, hfr5⟩
          have hadj' : CSRAdjacencySpec G st₄.mem (heap + 2 + G.n + G.n) (heap + 2 + G.n + G.n + (G.n + 1)) := by
            rwa [show heap + 2 + G.n + G.n = heap + 2 + 2 * G.n by omega,
              show heap + 2 + 2 * G.n + (G.n + 1) = heap + 3 + 3 * G.n by omega]
          refine runs_ret_le (Expr.eval_add (Expr.eval_reg_of_eq hregs5.r11)
            (Expr.eval_reg_of_eq hregs5.r0) (by omega))
            ⟨nlArr, tailArr, headArr, heap, rfl,
              by simp only [Outcome.value]; omega,
              hh0_5, hh1_5, hvL5, hiL5, hadj',
              fun a ha => by rw [hfr5 a (Or.inr (by dsimp only [newHeap] at *; omega))]
                             exact hz0 a (by omega),
              fun a ha => hfr5 a (Or.inl ha)⟩ ?_
          simp only [buildCSRContract, buildCSRCost, Expr.size_bin, Expr.size_const, Expr.size_reg]
          omega

end MinCostFlow.WideWord
