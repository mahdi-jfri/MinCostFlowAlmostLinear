module

public import MinCostFlow.Machine.WideWord.LSSTGraphCSR
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic WordRAM CSR construction (`buildCSR`)

This file implements and verifies `buildCSR`, which constructs the active/inactive vertex lists
(`activeVertsList G`, `inactiveVertsList G.n _`) and undirected CSR adjacency arrays `(off, adj)`
over `nonloopEdges G` in `O(n + nlCnt + 1)` time and space.

Layout starting at `heap`:
`[vLen, inactLen | vList(n) | inactList(n) | off(n+1) | adj(2*nlCnt) | deg(n) | cur(n)]`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM
open MinCostFlow
open MinCostFlow.LSF

/-! ### Procedures and CSR specification -/

/-- Loop 1 of `buildCSR`: count non-loop degrees into `degPtr`. -/
def buildCSRLoop1 : Stmt :=
  WordRAM.forRange 12 (.const 0) (.reg 1) (
    .assign 13 (.load (.bin .add (.reg 2) (.reg 12))) ;;
    .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
    .assign 15 (.load (.bin .add (.reg 4) (.reg 13))) ;;
    .store (.bin .add (.reg 10) (.reg 14))
      (.bin .add (.load (.bin .add (.reg 10) (.reg 14))) (.const 1)) ;;
    .store (.bin .add (.reg 10) (.reg 15))
      (.bin .add (.load (.bin .add (.reg 10) (.reg 15))) (.const 1))
  )

/-- Loop 2 of `buildCSR`: partition `0 .. n - 1` into `vList` and `inactList`. -/
def buildCSRLoop2 : Stmt :=
  WordRAM.forRange 12 (.const 0) (.reg 0) (
    .cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 12))) (.const 0))
      (.store (.bin .add (.reg 7) (.reg 14)) (.reg 12) ;;
       .assign 14 (.bin .add (.reg 14) (.const 1)))
      (.store (.bin .add (.reg 6) (.reg 13)) (.reg 12) ;;
       .assign 13 (.bin .add (.reg 13) (.const 1)))
  )

/-- Loop 3 of `buildCSR`: compute prefix sums of `deg` into `off` and `cur`. -/
def buildCSRLoop3 : Stmt :=
  WordRAM.forRange 12 (.const 0) (.reg 0) (
    .assign 14 (.load (.bin .add (.reg 10) (.reg 12))) ;;
    .store (.bin .add (.reg 11) (.reg 12)) (.reg 13) ;;
    .assign 13 (.bin .add (.reg 13) (.reg 14)) ;;
    .store (.bin .add (.reg 8) (.bin .add (.reg 12) (.const 1))) (.reg 13)
  )

/-- Loop 4 of `buildCSR`: scatter undirected non-loop endpoints into `adj`. -/
def buildCSRLoop4 : Stmt :=
  WordRAM.forRange 12 (.const 0) (.reg 1) (
    .assign 13 (.load (.bin .add (.reg 2) (.reg 12))) ;;
    .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
    .assign 15 (.load (.bin .add (.reg 4) (.reg 13))) ;;
    .assign 16 (.load (.bin .add (.reg 11) (.reg 14))) ;;
    .store (.bin .add (.reg 9) (.reg 16)) (.reg 15) ;;
    .store (.bin .add (.reg 11) (.reg 14)) (.bin .add (.reg 16) (.const 1)) ;;
    .assign 17 (.load (.bin .add (.reg 11) (.reg 15))) ;;
    .store (.bin .add (.reg 9) (.reg 17)) (.reg 14) ;;
    .store (.bin .add (.reg 11) (.reg 15)) (.bin .add (.reg 17) (.const 1))
  )

/-- Build `vList`, `inactList`, and CSR adjacency `(off, adj)` starting at `heap`.
Args: `[n, nlCnt, nlArr, tailArr, headArr, heap]`. Returns `newHeap`. -/
def buildCSR : Stmt :=
  .assign 6 (.bin .add (.reg 5) (.const 2)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 0)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 0)) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .add (.reg 0) (.const 1))) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 1))) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 0)) ;;
  buildCSRLoop1 ;;
  .assign 13 (.const 0) ;;
  .assign 14 (.const 0) ;;
  buildCSRLoop2 ;;
  .store (.reg 5) (.reg 13) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 14) ;;
  .assign 13 (.const 0) ;;
  .store (.reg 8) (.const 0) ;;
  buildCSRLoop3 ;;
  buildCSRLoop4 ;;
  .ret (.bin .add (.reg 11) (.reg 0))

theorem buildCSR_noRand : buildCSR.NoRand := by
  simp [buildCSR, buildCSRLoop1, buildCSRLoop2, buildCSRLoop3, buildCSRLoop4,
    Stmt.NoRand, WordRAM.forRange, WordRAM.forUp]

def buildCSRCost (n nlCnt : ℕ) : ℕ := (n + nlCnt + 1) * 160

/-- Specification of the CSR adjacency lists built over `nonloopEdges G`. -/
def CSRAdjacencySpec (G : IndexedGraph) (mem : ℕ → ℕ) (offPtr adjPtr : ℕ) : Prop :=
  mem offPtr = 0 ∧
  (∀ u < G.n, mem (offPtr + u) ≤ mem (offPtr + (u + 1))) ∧
  mem (offPtr + G.n) = 2 * (nonloopEdges G).length ∧
  (∀ u < G.n, ∀ p, mem (offPtr + u) ≤ p → p < mem (offPtr + (u + 1)) →
    ∃ e ∈ nonloopEdges G,
      (G.tail e = u ∧ mem (adjPtr + p) = G.head e) ∨
      (G.head e = u ∧ mem (adjPtr + p) = G.tail e)) ∧
  (∀ e ∈ nonloopEdges G,
    (∃ p, mem (offPtr + G.tail e) ≤ p ∧ p < mem (offPtr + (G.tail e + 1)) ∧
      mem (adjPtr + p) = G.head e) ∧
    (∃ p, mem (offPtr + G.head e) ≤ p ∧ p < mem (offPtr + (G.head e + 1)) ∧
      mem (adjPtr + p) = G.tail e))

def buildCSRContract (G : IndexedGraph) (w : ℕ) : Contract where
  pre args mem := ∃ nlArr tailArr headArr heap,
    args = [G.n, (nonloopEdges G).length, nlArr, tailArr, headArr, heap] ∧
    G.Valid ∧ 16 ≤ 2 ^ w ∧
    nlArr + (nonloopEdges G).length ≤ heap ∧
    tailArr + G.m ≤ heap ∧ headArr + G.m ≤ heap ∧
    heap + 3 + 5 * G.n + 2 * (nonloopEdges G).length < 2 ^ w ∧
    ListAt mem nlArr (nonloopEdges G) ∧
    ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i) ∧
    ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i) ∧
    ZeroFrom mem heap
  post args mem ret mem' := ∃ nlArr tailArr headArr heap,
    args = [G.n, (nonloopEdges G).length, nlArr, tailArr, headArr, heap] ∧
    let vListPtr := heap + 2
    let inactPtr := vListPtr + G.n
    let offPtr := inactPtr + G.n
    let adjPtr := offPtr + (G.n + 1)
    let newHeap := heap + 3 + 5 * G.n + 2 * (nonloopEdges G).length
    ret = newHeap ∧
    mem' heap = (activeVertsList G).length ∧
    mem' (heap + 1) = (inactiveVertsList G.n (activeVertsList G)).length ∧
    ListAt mem' vListPtr (activeVertsList G) ∧
    ListAt mem' inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
    CSRAdjacencySpec G mem' offPtr adjPtr ∧
    ZeroFrom mem' newHeap ∧
    (∀ a < heap, mem' a = mem a)
  cost _ _ := buildCSRCost G.n (nonloopEdges G).length

/-! ### Phase invariants and per-loop triples -/

structure CSRRegs (G : IndexedGraph) (nlArr tailArr headArr heap : ℕ) (st : State) : Prop where
  r0 : st.regs 0 = G.n
  r1 : st.regs 1 = (nonloopEdges G).length
  r2 : st.regs 2 = nlArr
  r3 : st.regs 3 = tailArr
  r4 : st.regs 4 = headArr
  r5 : st.regs 5 = heap
  r6 : st.regs 6 = heap + 2
  r7 : st.regs 7 = heap + 2 + G.n
  r8 : st.regs 8 = heap + 2 + 2 * G.n
  r9 : st.regs 9 = heap + 3 + 3 * G.n
  r10 : st.regs 10 = heap + 3 + 3 * G.n + 2 * (nonloopEdges G).length
  r11 : st.regs 11 = heap + 3 + 4 * G.n + 2 * (nonloopEdges G).length

lemma csrRegs_update_ge12 {G : IndexedGraph} {nlArr tailArr headArr heap r v : ℕ}
    {st : State} (hr : 12 ≤ r) (h : CSRRegs G nlArr tailArr headArr heap st) :
    CSRRegs G nlArr tailArr headArr heap { st with regs := Function.update st.regs r v } :=
  ⟨by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r0,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r1,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r2,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r3,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r4,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r5,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r6,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r7,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r8,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r9,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r10,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r11⟩

lemma csrRegs_with_mem {G : IndexedGraph} {nlArr tailArr headArr heap : ℕ}
    {m' : ℕ → ℕ} {st : State} (h : CSRRegs G nlArr tailArr headArr heap st) :
    CSRRegs G nlArr tailArr headArr heap { st with mem := m' } :=
  ⟨h.r0, h.r1, h.r2, h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, h.r9, h.r10, h.r11⟩

lemma nlEndpoints_bnd {G : IndexedGraph} (hG : G.Valid) :
    ∀ x ∈ nlEndpoints G (nonloopEdges G), x < G.n := by
  intro x hx
  simp only [nlEndpoints, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨e, he, rfl | rfl⟩
  · exact (hG.2 e (mem_nonloopEdges_iff.mp he).1).1
  · exact (hG.2 e (mem_nonloopEdges_iff.mp he).1).2

lemma buildCSR_phase1 {G : IndexedGraph} {nlArr tailArr headArr heap w : ℕ}
    {mem : ℕ → ℕ} {p : Program}
    (hG : G.Valid) (hw16 : 16 ≤ 2 ^ w)
    (hnl_h : nlArr + (nonloopEdges G).length ≤ heap)
    (htl_h : tailArr + G.m ≤ heap) (hhd_h : headArr + G.m ≤ heap)
    (hnew_w : heap + 3 + 5 * G.n + 2 * (nonloopEdges G).length < 2 ^ w)
    (hnlm : ListAt mem nlArr (nonloopEdges G))
    (htm : ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhm : ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hz0 : ZeroFrom mem heap) :
    let nl := nonloopEdges G
    let nlCnt := nl.length
    let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
    Triple w p
      (fun st => CSRRegs G nlArr tailArr headArr heap st ∧ st.mem = mem)
      buildCSRLoop1
      (normalPost fun st => CSRRegs G nlArr tailArr headArr heap st ∧
        (∀ u < G.n, st.mem (degPtr + u) = (nlEndpoints G nl).count u) ∧
        (∀ a, a < degPtr ∨ degPtr + G.n ≤ a → st.mem a = mem a))
      (fun _ => nlCnt * 55 + 10) := by
  let nl := nonloopEdges G
  let nlCnt := nl.length
  let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
  have hnl_len : nlCnt = (nonloopEdges G).length := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hnlCnt_w : nlCnt < 2 ^ w := by omega
  have hend_bnd := nlEndpoints_bnd hG
  let inv1 : ℕ → State → Prop := fun i st =>
    CSRRegs G nlArr tailArr headArr heap st ∧
    st.regs 12 = i ∧
    (∀ u < G.n, st.mem (degPtr + u) = (nlEndpoints G (nl.take i)).count u) ∧
    (∀ a, a < degPtr ∨ degPtr + G.n ≤ a → st.mem a = mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 13 (.load (.bin .add (.reg 2) (.reg 12))) ;;
      .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
      .assign 15 (.load (.bin .add (.reg 4) (.reg 13))) ;;
      .store (.bin .add (.reg 10) (.reg 14))
        (.bin .add (.load (.bin .add (.reg 10) (.reg 14))) (.const 1)) ;;
      .store (.bin .add (.reg 10) (.reg 15))
        (.bin .add (.load (.bin .add (.reg 10) (.reg 15))) (.const 1)))
    (P := fun st => CSRRegs G nlArr tailArr headArr heap st ∧ st.mem = mem)
    (Inv := inv1)
    45 0 nlCnt (Nat.zero_le nlCnt) hw1 (fun _ => hnlCnt_w)
    (fun st ⟨hregs, hmem⟩ =>
      ⟨by eval_expr, csrRegs_update_ge12 (by omega) hregs, by simp,
        fun u _ => by rw [hmem, hz0 (degPtr + u) (by dsimp [degPtr]; omega)]; simp [nlEndpoints],
        fun a _ => by simp [hmem]⟩)
    (fun _ st _ _ hi => hi.2.1)
    (fun _ st _ _ hi => by have h1 := hi.1.r1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨hregs, h12, hdeg, hfr⟩
      have hei : nl[i] < G.m ∧ G.tail (nl[i]) ≠ G.head (nl[i]) :=
        mem_nonloopEdges_iff.mp (List.getElem_mem hilt)
      set e := nl[i]
      set u := G.tail e
      set v' := G.head e
      have hu_lt := (hG.2 e hei.1).1
      have hv_lt := (hG.2 e hei.1).2
      have hne_th : u ≠ v' := hei.2
      have hnli : st.mem (nlArr + i) = e := by
        rw [hfr _ (by dsimp [degPtr]; omega)]; exact hnlm i hilt
      have hti : st.mem (tailArr + e) = u := by
        rw [hfr _ (by dsimp [degPtr]; omega)]; exact mem_ofFn_eq htm hei.1
      have hhi : st.mem (headArr + e) = v' := by
        rw [hfr _ (by dsimp [degPtr]; omega)]; exact mem_ofFn_eq hhm hei.1
      have hdu_w : st.mem (degPtr + u) + 1 < 2 ^ w := by
        have h1 : st.mem (degPtr + u) ≤ 2 * (nonloopEdges G).length := by
          rw [hdeg _ hu_lt]
          exact le_trans nlEndpoints_count_le <|
            (Finset.single_le_sum (f := fun x => (nlEndpoints G nl).count x)
              (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hu_lt)).trans_eq
              (nlEndpoints_sum_count hend_bnd)
        omega
      have hdv_w : st.mem (degPtr + v') + 1 < 2 ^ w := by
        have h1 : st.mem (degPtr + v') ≤ 2 * (nonloopEdges G).length := by
          rw [hdeg _ hv_lt]
          exact le_trans nlEndpoints_count_le <|
            (Finset.single_le_sum (f := fun x => (nlEndpoints G nl).count x)
              (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hv_lt)).trans_eq
              (nlEndpoints_sum_count hend_bnd)
        omega
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
      have haddr_u : Expr.eval w
          { mem := st.mem,
            regs := Function.update (Function.update (Function.update st.regs 13 e) 14 u) 15 v',
            pos := st.pos }
          (.bin .add (.reg 10) (.reg 14)) = some (degPtr + u) :=
        Expr.eval_add (Expr.eval_reg_of_eq hregs3.r10)
          (Expr.eval_reg_of_eq (by simp)) (by omega)
      refine runs_seq_store_le haddr_u
        (Expr.eval_add (Expr.eval_load_of_eq haddr_u (rfl : st.mem (degPtr + u) = _))
          (Expr.eval_const (by omega)) (by omega)) ?_
      have hregs4 := csrRegs_with_mem (m' := Function.update st.mem (degPtr + u) (st.mem (degPtr + u) + 1)) hregs3
      have hmem_v : (Function.update st.mem (degPtr + u) (st.mem (degPtr + u) + 1)) (degPtr + v') =
          st.mem (degPtr + v') := by rw [Function.update_of_ne (by omega)]
      have haddr_v : Expr.eval w
          { mem := Function.update st.mem (degPtr + u) (st.mem (degPtr + u) + 1),
            regs := Function.update (Function.update (Function.update st.regs 13 e) 14 u) 15 v',
            pos := st.pos }
          (.bin .add (.reg 10) (.reg 15)) = some (degPtr + v') :=
        Expr.eval_add (Expr.eval_reg_of_eq hregs4.r10)
          (Expr.eval_reg_of_eq (by simp)) (by omega)
      refine runs_store_le haddr_v
        (Expr.eval_add (Expr.eval_load_of_eq haddr_v hmem_v)
          (Expr.eval_const (by omega)) (by omega)) ?_ ?_
      · dsimp only
        have hregs5 := csrRegs_with_mem
          (m' := Function.update (Function.update st.mem (degPtr + u) (st.mem (degPtr + u) + 1))
            (degPtr + v') (st.mem (degPtr + v') + 1)) hregs4
        refine ⟨⟨csrRegs_update_ge12 (r := 12) (v := i + 1) (by omega) hregs5,
          by simp, ?_, ?_⟩, by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), h12]⟩
        · intro x hx
          have htake : nl.take (i + 1) = nl.take i ++ [e] := List.take_succ_eq_append_getElem hilt
          dsimp only [nlEndpoints, e, u, v'] at *
          rw [htake, List.flatMap_append, List.flatMap_singleton, List.count_append,
            List.count_cons, List.count_cons, List.count_nil]
          simp only [beq_iff_eq]
          by_cases hxv : x = G.head nl[i]
          · subst hxv
            rw [Function.update_self, hdeg _ hv_lt]
            split_ifs <;> omega
          · rw [Function.update_of_ne (by omega)]
            by_cases hxu : x = G.tail nl[i]
            · subst hxu
              rw [Function.update_self, hdeg _ hu_lt]
              split_ifs <;> omega
            · rw [Function.update_of_ne (by omega), hdeg x hx]
              split_ifs <;> omega
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a ha
      · wram_cost)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      dsimp only [normalPost, inv1, nl] at h ⊢
      rw [List.take_length] at h
      exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  · intro st _; simp only [Expr.size_reg, Expr.size_const]; omega

private lemma activeVertsList_filter_eq (G : IndexedGraph) :
    (List.range G.n).filter (fun x => decide (0 < (nlEndpoints G (nonloopEdges G)).count x)) =
      activeVertsList G := by
  refine List.filter_congr fun x _ => ?_
  by_cases h : (nonloopEdges G).any (fun e => G.tail e == x || G.head e == x)
  · have h1 : 0 < (nlEndpoints G (nonloopEdges G)).count x :=
      nlEndpoints_pos_iff.mpr (by simpa [List.any_eq_true, beq_iff_eq] using h)
    simp [h, h1]
  · have h1 : ¬ (0 < (nlEndpoints G (nonloopEdges G)).count x) := by
      rw [nlEndpoints_pos_iff]; simpa [List.any_eq_true, beq_iff_eq] using h
    simp [h, h1]

private lemma inactiveVertsList_filter_eq (G : IndexedGraph) :
    (List.range G.n).filter (fun x => decide ((nlEndpoints G (nonloopEdges G)).count x = 0)) =
      inactiveVertsList G.n (activeVertsList G) := by
  refine List.filter_congr fun x hx => ?_
  rw [List.mem_range] at hx
  by_cases h : 0 < (nlEndpoints G (nonloopEdges G)).count x
  · have hm : x ∈ activeVertsList G := mem_activeVertsList_iff.mpr ⟨hx, nlEndpoints_pos_iff.mp h⟩
    simp [show (nlEndpoints G (nonloopEdges G)).count x ≠ 0 by omega, hm]
  · have hc0 : (nlEndpoints G (nonloopEdges G)).count x = 0 := by omega
    have hnm : x ∉ activeVertsList G := fun hm =>
      h (nlEndpoints_pos_iff.mpr (mem_activeVertsList_iff.mp hm).2)
    simp [hc0, hnm]

lemma buildCSR_phase2 {G : IndexedGraph} {nlArr tailArr headArr heap w : ℕ}
    {mem : ℕ → ℕ} {p : Program}
    (hG : G.Valid) (hw16 : 16 ≤ 2 ^ w)
    (hnew_w : heap + 3 + 5 * G.n + 2 * (nonloopEdges G).length < 2 ^ w) :
    let nl := nonloopEdges G
    let nlCnt := nl.length
    let vListPtr := heap + 2
    let inactPtr := heap + 2 + G.n
    let offPtr := heap + 2 + 2 * G.n
    let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
    Triple w p
      (fun st => CSRRegs G nlArr tailArr headArr heap st ∧
        st.regs 13 = 0 ∧ st.regs 14 = 0 ∧
        (∀ x < G.n, st.mem (degPtr + x) = (nlEndpoints G nl).count x) ∧
        (∀ a, a < degPtr ∨ degPtr + G.n ≤ a → st.mem a = mem a))
      buildCSRLoop2
      (normalPost fun st => CSRRegs G nlArr tailArr headArr heap st ∧
        st.regs 13 = (activeVertsList G).length ∧
        st.regs 14 = (inactiveVertsList G.n (activeVertsList G)).length ∧
        ListAt st.mem vListPtr (activeVertsList G) ∧
        ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)) ∧
        (∀ x < G.n, st.mem (degPtr + x) = (nlEndpoints G nl).count x) ∧
        (∀ a, a < vListPtr ∨ (offPtr ≤ a ∧ a < degPtr) ∨ degPtr + G.n ≤ a → st.mem a = mem a))
      (fun _ => G.n * 40 + 10) := by
  let nl := nonloopEdges G
  let nlCnt := nl.length
  let vListPtr := heap + 2
  let inactPtr := heap + 2 + G.n
  let offPtr := heap + 2 + 2 * G.n
  let degPtr := heap + 3 + 3 * G.n + 2 * nlCnt
  have hw1 : 1 < 2 ^ w := by omega
  have hn_w : G.n < 2 ^ w := by omega
  have hend_bnd := nlEndpoints_bnd hG
  let inv2 : ℕ → State → Prop := fun u st =>
    CSRRegs G nlArr tailArr headArr heap st ∧
    st.regs 12 = u ∧
    st.regs 13 = ((List.range u).filter (fun x => decide (0 < (nlEndpoints G nl).count x))).length ∧
    st.regs 14 = ((List.range u).filter (fun x => decide ((nlEndpoints G nl).count x = 0))).length ∧
    ListAt st.mem vListPtr ((List.range u).filter (fun x => decide (0 < (nlEndpoints G nl).count x))) ∧
    ListAt st.mem inactPtr ((List.range u).filter (fun x => decide ((nlEndpoints G nl).count x = 0))) ∧
    (∀ x < G.n, st.mem (degPtr + x) = (nlEndpoints G nl).count x) ∧
    (∀ a, a < vListPtr ∨ (offPtr ≤ a ∧ a < degPtr) ∨ degPtr + G.n ≤ a → st.mem a = mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 0)
    (body :=
      .cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 12))) (.const 0))
        (.store (.bin .add (.reg 7) (.reg 14)) (.reg 12) ;;
         .assign 14 (.bin .add (.reg 14) (.const 1)))
        (.store (.bin .add (.reg 6) (.reg 13)) (.reg 12) ;;
         .assign 13 (.bin .add (.reg 13) (.const 1))))
    (P := fun st => CSRRegs G nlArr tailArr headArr heap st ∧
      st.regs 13 = 0 ∧ st.regs 14 = 0 ∧
      (∀ x < G.n, st.mem (degPtr + x) = (nlEndpoints G nl).count x) ∧
      (∀ a, a < degPtr ∨ degPtr + G.n ≤ a → st.mem a = mem a))
    (Inv := inv2)
    30 0 G.n (Nat.zero_le G.n) hw1 (fun _ => hn_w)
    (fun st ⟨hregs, h13, h14, hdeg, hfr⟩ =>
      ⟨by eval_expr, csrRegs_update_ge12 (by omega) hregs, by simp,
        by simp [h13], by simp [h14], listAt_nil' _ _, listAt_nil' _ _, hdeg,
        fun a ha => hfr a (by dsimp [degPtr, offPtr, vListPtr] at *; omega)⟩)
    (fun _ st _ _ hi => hi.2.1)
    (fun _ st _ _ hi => by have h0 := hi.1.r0; eval_expr)
    (fun u _ hult => by
      intro st _ ⟨hregs, h12, h13, h14, hvL, hiL, hdeg, hfr⟩
      set prefAct := (List.range u).filter (fun x => decide (0 < (nlEndpoints G nl).count x))
      set prefInact := (List.range u).filter (fun x => decide ((nlEndpoints G nl).count x = 0))
      have hplen1 : prefAct.length ≤ u := (List.length_filter_le _ _).trans (by simp)
      have hplen2 : prefInact.length ≤ u := (List.length_filter_le _ _).trans (by simp)
      have hdu := hdeg u hult
      have hdu_w : st.mem (degPtr + u) < 2 ^ w := by
        rw [hdu]
        have h1 : (nlEndpoints G nl).count u ≤ ∑ x ∈ Finset.range G.n, (nlEndpoints G nl).count x :=
          Finset.single_le_sum (f := fun x => (nlEndpoints G nl).count x)
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hult)
        rw [nlEndpoints_sum_count hend_bnd] at h1; omega
      refine runs_start_le ?_
      refine runs_cond_le (Expr.eval_eq_op
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs.r10)
          (Expr.eval_reg_of_eq h12) (by omega)) (rfl : st.mem (degPtr + u) = _))
        (Expr.eval_const (by omega)) (by omega)) ?_ ?_
      · intro hcond
        have hdc0 : (nlEndpoints G nl).count u = 0 := by
          by_contra hne; apply hcond; simp [hdu, hne]
        have ha' : (List.range (u + 1)).filter (fun x => decide (0 < (nlEndpoints G nl).count x)) =
            prefAct := by rw [filter_range_succ_lt]; simp [hdc0, prefAct]
        have hi' : (List.range (u + 1)).filter (fun x => decide ((nlEndpoints G nl).count x = 0)) =
            prefInact ++ [u] := by rw [filter_range_succ_lt]; simp [hdc0, prefInact]
        refine runs_seq_store_le
          (Expr.eval_add (Expr.eval_reg_of_eq hregs.r7) (Expr.eval_reg_of_eq h14) (by omega))
          (Expr.eval_reg_of_eq h12) ?_
        have hregs1 := csrRegs_with_mem (m' := Function.update st.mem (inactPtr + prefInact.length) u) hregs
        refine runs_assign_le
          (Expr.eval_add (Expr.eval_reg_of_eq h14) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
        · dsimp only
          refine ⟨⟨csrRegs_update_ge12 (r := 12) (v := u + 1) (by omega)
              (csrRegs_update_ge12 (r := 14) (v := prefInact.length + 1) (by omega) hregs1),
            by simp,
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h13, ha'],
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self, hi',
                 List.length_append, List.length_singleton],
            ?_, ?_, ?_, ?_⟩,
            by dsimp only; rw [Function.update_of_ne (by omega), h12]⟩
          · rw [ha']; exact listAt_congr' (fun i hi => by
              dsimp only [inactPtr, vListPtr]
              rw [Function.update_of_ne (by omega)]) hvL
          · rw [hi']; exact listAt_snoc' hiL
          · intro x hx
            dsimp only
            rw [Function.update_of_ne (by dsimp [degPtr, inactPtr]; omega)]
            exact hdeg x hx
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by dsimp [degPtr, offPtr, inactPtr, vListPtr] at *; omega)]
            exact hfr a ha
        · wram_cost
      · intro hcond
        have hdc_pos : 0 < (nlEndpoints G nl).count u := by
          have : st.mem (degPtr + u) ≠ 0 := by intro heq; simp [heq] at hcond
          rw [hdu] at this; exact Nat.pos_of_ne_zero this
        have ha' : (List.range (u + 1)).filter (fun x => decide (0 < (nlEndpoints G nl).count x)) =
            prefAct ++ [u] := by rw [filter_range_succ_lt]; simp [hdc_pos, prefAct]
        have hi' : (List.range (u + 1)).filter (fun x => decide ((nlEndpoints G nl).count x = 0)) =
            prefInact := by rw [filter_range_succ_lt]; simp [show (nlEndpoints G nl).count u ≠ 0 by omega, prefInact]
        refine runs_seq_store_le
          (Expr.eval_add (Expr.eval_reg_of_eq hregs.r6) (Expr.eval_reg_of_eq h13) (by omega))
          (Expr.eval_reg_of_eq h12) ?_
        have hregs1 := csrRegs_with_mem (m' := Function.update st.mem (vListPtr + prefAct.length) u) hregs
        refine runs_assign_le
          (Expr.eval_add (Expr.eval_reg_of_eq h13) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
        · dsimp only
          refine ⟨⟨csrRegs_update_ge12 (r := 12) (v := u + 1) (by omega)
              (csrRegs_update_ge12 (r := 13) (v := prefAct.length + 1) (by omega) hregs1),
            by simp,
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self, ha',
                 List.length_append, List.length_singleton],
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h14, hi'],
            ?_, ?_, ?_, ?_⟩,
            by dsimp only; rw [Function.update_of_ne (by omega), h12]⟩
          · rw [ha']; exact listAt_snoc' hvL
          · rw [hi']; exact listAt_congr' (fun i hi => by
              dsimp only [inactPtr, vListPtr]
              rw [Function.update_of_ne (by omega)]) hiL
          · intro x hx
            dsimp only
            rw [Function.update_of_ne (by dsimp [degPtr, vListPtr]; omega)]
            exact hdeg x hx
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by dsimp [degPtr, offPtr, inactPtr, vListPtr] at *; omega)]
            exact hfr a ha
        · wram_cost)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨hregs, _, h13, h14, hvL, hiL, hdeg, hfr⟩
      rw [activeVertsList_filter_eq] at h13 hvL
      rw [inactiveVertsList_filter_eq] at h14 hiL
      exact ⟨hregs, h13, h14, hvL, hiL, hdeg, hfr⟩
  · intro st _; simp only [Expr.size_reg, Expr.size_const]; omega


end MinCostFlow.WideWord
