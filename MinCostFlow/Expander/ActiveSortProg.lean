module

public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import WordRAM.Entry
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.GraphCompression
public import MinCostFlow.Expander.HeapSortProg

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Active-Vertex Compression Procedures (`dedupProc`, `binSearchProc`, `compressGraphProc`)

Builds on `HeapSortProg` (`b + 0`: `siftDown`, `b + 1`: `heapSort`) to provide the complete
5-procedure `NoRand` bundle `activeSortProcs b`:
- `b + 2`: `dedupProc` (`O(n + 1)`),
- `b + 3`: `binSearchProc` (`O(log(nAct + 2) + 1)`),
- `b + 4`: `compressGraphProc b` (`O(G.m * (log(2 * G.m + 2) + 1) + 1)`),
producing sorted `actVerts` at `workAddr + 2 * G.m` and `compressGraph actVerts G` at
`workAddr + 4 * G.m` in `6 * G.m + 2` heap words, completely independent of `G.n`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. `dedupProc` (`b + 2`) -/

/-- `dedupProc`: `args = [inAddr, n, outAddr]`, deduplicates sorted input `inAddr[0..n-1]` into
`outAddr[0..k-1]` and returns `k`. -/
def dedupProc : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.ret (.const 0))
    (.seq (.assign 5 (.load (.reg 0))) -- prev := mem[inAddr]
    (.seq (.store (.reg 2) (.reg 5)) -- mem[outAddr] := prev
    (.seq (.assign 3 (.const 1)) -- k := 1
    (.seq (.assign 4 (.const 1)) -- i := 1
    (.seq (.loop (.bin .lt (.reg 4) (.reg 1))
      (.seq (.assign 6 (.load (.bin .add (.reg 0) (.reg 4))))
      (.seq (.cond (.bin .lt (.reg 5) (.reg 6))
        (.seq (.store (.bin .add (.reg 2) (.reg 3)) (.reg 6))
        (.seq (.assign 5 (.reg 6))
          (.assign 3 (.bin .add (.reg 3) (.const 1)))))
        .nop)
      (.assign 4 (.bin .add (.reg 4) (.const 1))))))
    (.ret (.reg 3)))))))

lemma dedupProc_noRand : dedupProc.NoRand := by
  simp [dedupProc, Stmt.NoRand]

/-- Contract for `dedupProc`: args `[inAddr, n, outAddr]`. -/
def dedupContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ inAddr n outAddr, args = [inAddr, n, outAddr] ∧
      inAddr + n ≤ outAddr ∧
      outAddr + n < 2 ^ w ∧
      4 ≤ 2 ^ w ∧
      (∀ i < n, mem (inAddr + i) < 2 ^ w) ∧
      (tab n fun i => mem (inAddr + i)).Pairwise (· ≤ ·)
  post args mem v mem' :=
    let inAddr := args.getD 0 0
    let n := args.getD 1 0
    let outAddr := args.getD 2 0
    let xs := tab n fun i => mem (inAddr + i)
    let ys := tab v fun i => mem' (outAddr + i)
    v ≤ n ∧
    ys.Pairwise (· < ·) ∧
    (∀ u, u ∈ ys ↔ u ∈ xs) ∧
    (∀ i < v, mem' (outAddr + i) < 2 ^ w) ∧
    MemFrame mem mem' outAddr (outAddr + n)
  cost args _ :=
    let n := args.getD 1 0
    35 * (n + 1)

theorem dedup_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [dedupProc]) :
    MeetsContract w p b (dedupContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [dedupContract] at hpre
  rcases hpre with ⟨inAddr, n, outAddr, rfl, hio, hou, hw4, hmem_lt, hsorted⟩
  have hproc : p.procs[b]? = some dedupProc := hp 0 (by simp)
  have hlt_in : inAddr < 2 ^ w := hwords inAddr (by simp)
  have hlt_n : n < 2 ^ w := hwords n (by simp)
  have hlt_out : outAddr < 2 ^ w := hwords outAddr (by simp)
  by_cases hn0 : n = 0
  · subst hn0
    have htriple :
        Triple w p
          (fun st => st = startState [inAddr, 0, outAddr] mem pos)
          dedupProc
          (fun o st' => o.value ≤ 0 ∧
            (tab o.value fun i => st'.mem (outAddr + i)).Pairwise (· < ·) ∧
            (∀ u, u ∈ (tab o.value fun i => st'.mem (outAddr + i)) ↔
              u ∈ (tab 0 fun i => mem (inAddr + i))) ∧
            (∀ i < o.value, st'.mem (outAddr + i) < 2 ^ w) ∧
            MemFrame mem st'.mem outAddr (outAddr + 0))
          (fun _ => 35) := by
      wram_enter
      · subst hpre
        dsimp only [dedupProc]
        wram_run
        · refine ⟨by simp [Outcome.value], by simp [Outcome.value, tab],
            by simp [Outcome.value, tab], fun i hi => by simp [Outcome.value] at hi,
            memFrame_refl _ _ _⟩
        · wram_cost
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [inAddr, 0, outAddr] mem pos) ω rfl
    exact ⟨dedupProc, hproc, o, st', c, hrun, hpost, hcost⟩
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hlt_0 : mem inAddr < 2 ^ w := by simpa using hmem_lt 0 hn_pos
    have htriple :
        Triple w p
          (fun st => st = startState [inAddr, n, outAddr] mem pos)
          dedupProc
          (fun o st' => o.value ≤ n ∧
            (tab o.value fun i => st'.mem (outAddr + i)).Pairwise (· < ·) ∧
            (∀ u, u ∈ (tab o.value fun i => st'.mem (outAddr + i)) ↔
              u ∈ (tab n fun i => mem (inAddr + i))) ∧
            (∀ i < o.value, st'.mem (outAddr + i) < 2 ^ w) ∧
            MemFrame mem st'.mem outAddr (outAddr + n))
          (fun _ => 35 * (n + 1)) := by
      wram_enter
      · subst hpre
        dsimp only [dedupProc]
        wram_step; wram_step; wram_step; wram_step; wram_step
        let Inv : State → Prop := fun st =>
          st.regs 0 = inAddr ∧ st.regs 1 = n ∧ st.regs 2 = outAddr ∧
          1 ≤ st.regs 3 ∧ st.regs 3 ≤ st.regs 4 ∧ st.regs 4 ≤ n ∧
          st.regs 5 = st.mem (outAddr + (st.regs 3 - 1)) ∧
          st.regs 5 = mem (inAddr + (st.regs 4 - 1)) ∧
          (tab (st.regs 3) fun i => st.mem (outAddr + i)).Pairwise (· < ·) ∧
          (∀ u, u ∈ (tab (st.regs 3) fun i => st.mem (outAddr + i)) ↔
            u ∈ (tab (st.regs 4) fun i => mem (inAddr + i))) ∧
          (∀ i < st.regs 3, st.mem (outAddr + i) < 2 ^ w) ∧
          MemFrame mem st.mem outAddr (outAddr + n)
        have hloop : Triple w p Inv
            (.loop (.bin .lt (.reg 4) (.reg 1))
              (.seq (.assign 6 (.load (.bin .add (.reg 0) (.reg 4))))
              (.seq (.cond (.bin .lt (.reg 5) (.reg 6))
                (.seq (.store (.bin .add (.reg 2) (.reg 3)) (.reg 6))
                (.seq (.assign 5 (.reg 6))
                  (.assign 3 (.bin .add (.reg 3) (.const 1)))))
                .nop)
              (.assign 4 (.bin .add (.reg 4) (.const 1))))))
            (normalPost fun st' => Inv st' ∧ st'.regs 4 = n)
            (fun st => (3 + 30 + 1) * (n - st.regs 4) + 3 + 1) := by
          refine Triple.loop_const_normal (fun st => n - st.regs 4)
            (fun st => if st.regs 4 < n then 1 else 0) 30
            (fun st hInv => by rcases hInv with ⟨_, _, _⟩; eval_expr)
            (fun st hInv h0 => by
              simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
              exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, h4n, _⟩; omega⟩)
            (fun st hInv hne => ?_)
          simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
          rcases hInv with ⟨hr0, hr1, hr2, hk1, hki, hin, hp_out, hp_in, hpair, hmem_eq, hlt_out, hframe⟩
          have hi_lt : st.regs 4 < n := hne
          have hcur_eq : st.mem (inAddr + st.regs 4) = mem (inAddr + st.regs 4) :=
            hframe (inAddr + st.regs 4) (Or.inl (by omega))
          have hcur_lt : st.mem (inAddr + st.regs 4) < 2 ^ w := by
            rw [hcur_eq]; exact hmem_lt _ hi_lt
          have hp_le_cur : st.regs 5 ≤ st.mem (inAddr + st.regs 4) := by
            rw [hp_in, hcur_eq]
            have hpl := (List.pairwise_iff_getElem.mp hsorted) (st.regs 4 - 1) (st.regs 4)
              (by simp [tab]; omega) (by simp [tab]; omega) (by omega)
            simpa [tab, hi_lt, show st.regs 4 - 1 < n by omega] using hpl
          have htab_next : ∀ u, u ∈ tab (st.regs 4 + 1) (fun i => mem (inAddr + i)) ↔
              u ∈ tab (st.regs 4) (fun i => mem (inAddr + i)) ∨ u = mem (inAddr + st.regs 4) := by
            intro u
            simp only [tab, List.range_succ, List.map_append, List.map_singleton, List.mem_append,
              List.mem_singleton]
          wram_enter
          · subst hpre
            wram_run
            · -- prev < cur
              simp only [hr2]
              have htab_eq : tab (st.regs 3 + 1)
                  (fun i => Function.update st.mem (outAddr + st.regs 3) (st.mem (inAddr + st.regs 4)) (outAddr + i)) =
                  tab (st.regs 3) (fun i => st.mem (outAddr + i)) ++ [st.mem (inAddr + st.regs 4)] := by
                simp only [tab, List.range_succ, List.map_append, List.map_singleton]
                congr 1
                · exact List.map_congr_left fun i hi =>
                    Function.update_of_ne (by simp only [List.mem_range] at hi; omega) _ _
                · simp
              refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp,
                by simp; omega, by simp; omega,
                by simp,
                by simp [hcur_eq],
                ?_, ?_, ?_, ?_⟩, by simp; omega⟩
              · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
                rw [htab_eq, List.pairwise_append]
                refine ⟨hpair, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
                simp only [List.mem_singleton] at hb; subst hb
                rw [hmem_eq] at ha
                simp only [tab, List.mem_map, List.mem_range] at ha
                rcases ha with ⟨j, hj, rfl⟩
                have hpl : mem (inAddr + j) ≤ mem (inAddr + (st.regs 4 - 1)) := by
                  rcases eq_or_lt_of_le (Nat.le_pred_of_lt hj) with rfl | hj_lt
                  · exact le_rfl
                  · have hpl' := (List.pairwise_iff_getElem.mp hsorted) j (st.regs 4 - 1)
                      (by simp [tab]; omega) (by simp [tab]; omega) hj_lt
                    simpa [tab, show j < n by omega, show st.regs 4 - 1 < n by omega] using hpl'
                rw [← hp_in] at hpl
                exact lt_of_le_of_lt hpl hcond
              · intro u
                simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
                rw [htab_eq, List.mem_append, List.mem_singleton, hmem_eq, hcur_eq, htab_next]
              · intro i hi
                simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self] at hi
                dsimp only
                by_cases hik : i = st.regs 3
                · subst hik; simpa using hcur_lt
                · rw [Function.update_of_ne (by omega)]; exact hlt_out i (by omega)
              · exact memFrame_trans hframe (memFrame_update (by omega) (by omega))
            · wram_cost
            · -- prev = cur
              have hprev_eq : st.regs 5 = mem (inAddr + st.regs 4) := by omega
              refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], hk1, by simp; omega,
                by simp; omega,
                by simp [hp_out],
                by simp [← hprev_eq],
                by simpa using hpair, ?_,
                by simpa using hlt_out, hframe⟩, by simp; omega⟩
              intro u
              simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
                Function.update_of_ne (by decide : (3 : ℕ) ≠ 6),
                Function.update_self]
              rw [hmem_eq, htab_next]
              constructor
              · exact Or.inl
              · rintro (h | rfl)
                · exact h
                · rw [← hprev_eq, hp_in]
                  simp only [tab, List.mem_map, List.mem_range]
                  exact ⟨st.regs 4 - 1, by omega, rfl⟩
            · wram_cost
        refine runs_seq_triple_le hloop ?_ (fun st' hst' => ?_)
        · refine ⟨by simp [startState], by simp [startState],
            by simp [startState], le_rfl, le_rfl, hn_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [startState]
          · simp [startState]
          · simp [tab]
          · intro u
            simp [tab]
          · intro i hi
            simp at hi
            subst hi
            simpa using hlt_0
          · exact memFrame_update le_rfl (by omega)
        · wram_step
          · rcases hst' with ⟨⟨_, _, _, _, hk_le, _, _, _, hpair', hmem', hlt', hframe'⟩, hr4_eq⟩
            refine ⟨by simp [Outcome.value]; omega, hpair', ?_, hlt', hframe'⟩
            intro u
            simpa [Outcome.value, hr4_eq] using hmem' u
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load] at *
            omega
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [inAddr, n, outAddr] mem pos) ω rfl
    exact ⟨dedupProc, hproc, o, st', c, hrun, hpost, hcost⟩

/-! ## 2. `binSearchProc` (`b + 3`) -/

/-- `binSearchProc`: `args = [actAddr, nAct, key]`, binary searches strictly sorted
`actAddr[0..nAct-1]` for `key` and returns its index `idx`. -/
def binSearchProc : Stmt :=
  .seq (.assign 3 (.const 0)) -- lo := 0
  (.seq (.assign 4 (.reg 1)) -- hi := nAct
  (.seq (.assign 5 (.const 1)) -- flag := 1
  (.seq (.assign 8 (.const 0)) -- res := 0
  (.seq (.loop (.reg 5)
    (.seq (.assign 6 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))))
    (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 6))))
    (.cond (.bin .eq (.reg 7) (.reg 2))
      (.seq (.assign 8 (.reg 6)) (.assign 5 (.const 0)))
      (.cond (.bin .lt (.reg 7) (.reg 2))
        (.assign 3 (.bin .add (.reg 6) (.const 1)))
        (.assign 4 (.reg 6)))))))
  (.ret (.reg 8))))))

lemma binSearchProc_noRand : binSearchProc.NoRand := by
  simp [binSearchProc, Stmt.NoRand]

/-- Contract for `binSearchProc`: args `[actAddr, nAct, key]`. -/
def binSearchContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ actAddr nAct key, args = [actAddr, nAct, key] ∧
      actAddr + nAct < 2 ^ w ∧
      4 ≤ 2 ^ w ∧
      (∀ i < nAct, mem (actAddr + i) < 2 ^ w) ∧
      (tab nAct fun i => mem (actAddr + i)).Pairwise (· < ·) ∧
      key ∈ tab nAct fun i => mem (actAddr + i)
  post args mem v mem' :=
    let actAddr := args.getD 0 0
    let nAct := args.getD 1 0
    let key := args.getD 2 0
    let ys := tab nAct fun i => mem (actAddr + i)
    mem' = mem ∧
    v < nAct ∧
    v = ys.idxOf key ∧
    mem (actAddr + v) = key
  cost args _ :=
    let nAct := args.getD 1 0
    35 * (Nat.log 2 (nAct + 2) + 2)

theorem binSearch_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [binSearchProc]) :
    MeetsContract w p b (binSearchContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [binSearchContract] at hpre
  rcases hpre with ⟨actAddr, nAct, key, rfl, han, hw4, hmem_lt, hstrict, hkey⟩
  have hproc : p.procs[b]? = some binSearchProc := hp 0 (by simp)
  have hlt_a : actAddr < 2 ^ w := hwords actAddr (by simp)
  have hlt_n : nAct < 2 ^ w := hwords nAct (by simp)
  have hlt_k : key < 2 ^ w := hwords key (by simp)
  set ys := tab nAct fun i => mem (actAddr + i)
  have hk_lt_ys : ys.idxOf key < ys.length := List.idxOf_lt_length_of_mem hkey
  have hk_lt : ys.idxOf key < nAct := by simpa [ys, tab] using hk_lt_ys
  have hk_get : mem (actAddr + ys.idxOf key) = key := by
    have hg := List.getElem_idxOf hk_lt_ys
    simpa only [ys, tab, List.getElem_map, List.getElem_range] using hg
  have htriple :
      Triple w p
        (fun st => st = startState [actAddr, nAct, key] mem pos)
        binSearchProc
        (fun o st' => st'.mem = mem ∧ o.value = ys.idxOf key)
        (fun _ => 35 * (Nat.log 2 (nAct + 2) + 2)) := by
    wram_enter
    · subst hpre
      dsimp only [binSearchProc]
      wram_step; wram_step; wram_step; wram_step
      let Inv : State → Prop := fun st =>
        st.mem = mem ∧
        st.regs 0 = actAddr ∧ st.regs 1 = nAct ∧ st.regs 2 = key ∧
        (st.regs 5 = 0 ∨ st.regs 5 = 1) ∧
        st.regs 3 ≤ ys.idxOf key ∧ ys.idxOf key < st.regs 4 ∧ st.regs 4 ≤ nAct ∧
        (st.regs 5 = 0 → st.regs 8 = ys.idxOf key)
      let meas : State → ℕ := fun st =>
        if st.regs 5 = 0 then 0 else Nat.log 2 (st.regs 4 - st.regs 3) + 1
      have hloop : Triple w p Inv
          (.loop (.reg 5)
            (.seq (.assign 6 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))))
            (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 6))))
            (.cond (.bin .eq (.reg 7) (.reg 2))
              (.seq (.assign 8 (.reg 6)) (.assign 5 (.const 0)))
              (.cond (.bin .lt (.reg 7) (.reg 2))
                (.assign 3 (.bin .add (.reg 6) (.const 1)))
                (.assign 4 (.reg 6)))))))
          (normalPost fun st' => Inv st' ∧ st'.regs 5 = 0)
          (fun st => (1 + 30 + 1) * meas st + 1 + 1) := by
        refine Triple.loop_const_normal meas (fun st => st.regs 5) 30
          (fun st hInv => by rcases hInv with ⟨_, _, _, _, _⟩; eval_expr)
          (fun st hInv h0 => ⟨hInv, h0⟩)
          (fun st hInv hne => ?_)
        rcases hInv with ⟨hmem, hr0, hr1, hr2, hfl, hlo, hhi, hhn, hdone⟩
        have hfl1 : st.regs 5 = 1 := by omega
        set d := st.regs 4 - st.regs 3
        have hd_pos : 0 < d := by omega
        set mid := st.regs 3 + d / 2
        have hmid_lt : mid < nAct := by omega
        have hval_lt : st.mem (actAddr + mid) < 2 ^ w := by rw [hmem]; exact hmem_lt mid hmid_lt
        have hmid_cmp : ∀ i j, i < j → j < nAct → mem (actAddr + i) < mem (actAddr + j) := by
          intro i j hij hj
          have hp := pairwise_lt_getElem_lt hstrict hij (by simpa [ys, tab] using hj)
          simpa [ys, tab, hj, Nat.lt_trans hij hj] using hp
        wram_enter
        · subst hpre
          wram_step; wram_step; wram_step
          · -- val = key
            have hmem_mid : mem (actAddr + mid) = key := by simpa [hr0, hr2, hmem] using hcond
            have hmid_idx : mid = ys.idxOf key := by
              rcases lt_trichotomy mid (ys.idxOf key) with h | h | h
              · have := hmid_cmp _ _ h hk_lt; rw [hmem_mid, hk_get] at this; exact absurd this (lt_irrefl _)
              · exact h
              · have := hmid_cmp _ _ h hmid_lt; rw [hmem_mid, hk_get] at this; exact absurd this (lt_irrefl _)
            wram_run
            · refine ⟨⟨hmem, by simp [hr0], by simp [hr1], by simp [hr2], Or.inl (by simp),
                by simp; omega, by simp; omega, by simp; omega,
                fun _ => by simp; exact hmid_idx⟩, ?_⟩
              dsimp only [meas]; simp [hfl1]
            · wram_cost
          · -- val ≠ key
            have hne_key : mem (actAddr + mid) ≠ key := by simpa [hr0, hr2, hmem] using hcond
            wram_run
            · -- val < key
              have hlt_k' : mem (actAddr + mid) < key := by simpa [hr0, hr2, hmem] using hcond
              have hmid_lt_idx : mid < ys.idxOf key := by
                by_contra hge
                rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
                · rw [← heq, hk_get] at hlt_k'; exact lt_irrefl _ hlt_k'
                · have := hmid_cmp _ _ hgt hmid_lt; rw [hk_get] at this; omega
              refine ⟨⟨hmem, by simp [hr0], by simp [hr1], by simp [hr2], Or.inr (by simp [hfl1]),
                by simp; omega, by simp; omega, by simp; omega,
                fun h => by simp [hfl1] at h⟩, ?_⟩
              have hd'_le : st.regs 4 - (mid + 1) ≤ d / 2 := by omega
              have hd_ge2 : 2 ≤ d := by omega
              have hlog_drop : Nat.log 2 (st.regs 4 - (mid + 1)) < Nat.log 2 d := by
                have h1 : Nat.log 2 (st.regs 4 - (mid + 1)) ≤ Nat.log 2 (d / 2) :=
                  Nat.log_mono_right hd'_le
                rw [Nat.log_div_base] at h1
                have hlog_pos : 1 ≤ Nat.log 2 d := Nat.le_log_of_pow_le (by decide) (by simpa using hd_ge2)
                omega
              dsimp only [meas]; simp only [hfl1, one_ne_zero, ↓reduceIte, Function.update_of_ne
                (by decide : (5 : ℕ) ≠ 6), Function.update_of_ne (by decide : (5 : ℕ) ≠ 7),
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 3),
                Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (4 : ℕ) ≠ 7),
                Function.update_of_ne (by decide : (4 : ℕ) ≠ 3),
                Function.update_self]
              dsimp only [mid, d] at hlog_drop
              omega
            · wram_cost
            · -- key < val
              have hgt_k' : key < mem (actAddr + mid) := by
                have hle' : key ≤ mem (actAddr + mid) := by simpa [hr0, hr2, hmem] using hcond
                omega
              have hidx_lt_mid : ys.idxOf key < mid := by
                by_contra hge
                rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hlt
                · rw [heq, hk_get] at hgt_k'; exact lt_irrefl _ hgt_k'
                · have := hmid_cmp _ _ hlt hk_lt; rw [hk_get] at this; omega
              refine ⟨⟨hmem, by simp [hr0], by simp [hr1], by simp [hr2], Or.inr (by simp [hfl1]),
                by simp; omega, by simp; omega, by simp; omega,
                fun h => by simp [hfl1] at h⟩, ?_⟩
              have hd'_le : mid - st.regs 3 ≤ d / 2 := by omega
              have hd_ge2 : 2 ≤ d := by omega
              have hlog_drop : Nat.log 2 (mid - st.regs 3) < Nat.log 2 d := by
                have h1 : Nat.log 2 (mid - st.regs 3) ≤ Nat.log 2 (d / 2) :=
                  Nat.log_mono_right hd'_le
                rw [Nat.log_div_base] at h1
                have hlog_pos : 1 ≤ Nat.log 2 d := Nat.le_log_of_pow_le (by decide) (by simpa using hd_ge2)
                omega
              dsimp only [meas]; simp only [hfl1, one_ne_zero, ↓reduceIte, Function.update_of_ne
                (by decide : (5 : ℕ) ≠ 6), Function.update_of_ne (by decide : (5 : ℕ) ≠ 7),
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 4),
                Function.update_self,
                Function.update_of_ne (by decide : (3 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (3 : ℕ) ≠ 7),
                Function.update_of_ne (by decide : (3 : ℕ) ≠ 4)]
              dsimp only [mid, d] at hlog_drop
              omega
            · wram_cost
      refine runs_seq_triple_le hloop ?_ (fun st' hst' => ?_)
      · refine ⟨by simp [startState], by simp [startState], by simp [startState],
          by simp [startState], Or.inr (by simp), by simp, by simp [hk_lt], by simp,
          fun h => by simp at h⟩
      · wram_step
        · rcases hst' with ⟨⟨hmem', _, _, _, _, _, _, _, hdone⟩, hr5⟩
          exact ⟨hmem', by simpa [Outcome.value] using hdone hr5⟩
        · have hlog_le : Nat.log 2 nAct ≤ Nat.log 2 (nAct + 2) := Nat.log_mono_right (by omega)
          let st0_init : State :=
            { mem := mem,
              regs := Function.update (Function.update (Function.update (Function.update
                (startState [actAddr, nAct, key] mem pos).regs 3 0) 4 nAct) 5 1) 8 0,
              pos := pos }
          have hmeas_le : meas st0_init ≤ Nat.log 2 (nAct + 2) + 1 := by
            dsimp only [meas, st0_init, startState]
            simp
            omega
          simp only [Expr.size_const, Expr.size_reg] at *
          nlinarith [hmeas_le]
  obtain ⟨o, st', c, hrun, ⟨hmem', ho'⟩, hcost⟩ := htriple (startState [actAddr, nAct, key] mem pos) ω rfl
  refine ⟨binSearchProc, hproc, o, st', c, hrun, ⟨hmem', ?_, ho', ?_⟩, hcost⟩
  · simpa [ho'] using hk_lt
  · simpa [ho'] using hk_get

/-! ## 3. `compressGraphProc` (`b + 4`) and `activeSortProcs` -/

/-- `compressGraphProc b`: `args = [gAddr, workAddr]`, builds `actVerts` at `workAddr + 2*m` and
`compressGraph actVerts G` at `workAddr + 4*m`, returning `actVerts.length`.
Calls `b + 1` (`heapSort`), `b + 2` (`dedup`), `b + 3` (`binSearch`). -/
def compressGraphProc (b : ℕ) : Stmt :=
  .seq (.assign 2 (.load (.bin .add (.reg 0) (.const 1)))) -- m := mem[gAddr + 1]
  (.cond (.bin .eq (.reg 2) (.const 0))
    (.seq (.store (.reg 1) (.const 0))
    (.seq (.store (.bin .add (.reg 1) (.const 1)) (.const 0))
      (.ret (.const 0))))
    (.seq (.assign 3 (.bin .mul (.const 2) (.reg 2))) -- m2 := 2 * m
    (.seq (.assign 4 (.bin .add (.reg 1) (.reg 3))) -- actAddr := workAddr + 2 * m
    (.seq (.assign 5 (.bin .add (.reg 4) (.reg 3))) -- gActAddr := workAddr + 4 * m
    (.seq (.assign 7 (.const 0)) -- j := 0
    (.seq (.loop (.bin .lt (.reg 7) (.reg 3))
      (.seq (.store (.bin .add (.reg 1) (.reg 7))
        (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 7))))
        (.assign 7 (.bin .add (.reg 7) (.const 1)))))
    (.seq (.call 10 (b + 1) [.reg 1, .reg 3]) -- heapSort workAddr m2
    (.seq (.call 6 (b + 2) [.reg 1, .reg 3, .reg 4]) -- nAct := dedup workAddr m2 actAddr
    (.seq (.store (.reg 5) (.reg 6)) -- mem[gActAddr] := nAct
    (.seq (.store (.bin .add (.reg 5) (.const 1)) (.reg 2)) -- mem[gActAddr + 1] := m
    (.seq (.assign 7 (.const 0)) -- j := 0
    (.seq (.loop (.bin .lt (.reg 7) (.reg 3))
      (.seq (.assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 7))))
      (.seq (.call 9 (b + 3) [.reg 4, .reg 6, .reg 8])
      (.seq (.store (.bin .add (.bin .add (.reg 5) (.const 2)) (.reg 7)) (.reg 9))
        (.assign 7 (.bin .add (.reg 7) (.const 1)))))))
    (.ret (.reg 6))))))))))))))

lemma compressGraphProc_noRand (b : ℕ) : (compressGraphProc b).NoRand := by
  simp [compressGraphProc, Stmt.NoRand]

/-- Contract for `compressGraphProc b`: args `[gAddr, workAddr]`. -/
def compressGraphContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr workAddr : ℕ) (G : Cited.Graph),
      args = [gAddr, workAddr] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      G.n < 2 ^ w ∧
      gAddr + G.encode.length ≤ workAddr ∧
      workAddr + 6 * G.m + 2 < 2 ^ w ∧
      4 ≤ 2 ^ w
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let workAddr := args.getD 1 0
    let G := Cited.readGraph mem gAddr
    let actVerts := tab v fun i => mem' (workAddr + 2 * G.m + i)
    v ≤ 2 * G.m ∧
    ActVertsSpec G actVerts ∧
    GraphAt mem' (workAddr + 4 * G.m) (compressGraph actVerts G) ∧
    MemFrame mem mem' workAddr (workAddr + 6 * G.m + 2)
  cost args mem :=
    let G := Cited.readGraph mem (args.getD 0 0)
    950 * (G.m * (2 * Nat.log 2 (2 * G.m + 2) + 1) + 1)

theorem compressGraph_spec {w : ℕ} {p : Program} {b : ℕ}
    (hp0 : p.HasAt b [siftDownProc])
    (hp1 : p.HasAt (b + 1) [heapSortProc b])
    (hp2 : p.HasAt (b + 2) [dedupProc])
    (hp3 : p.HasAt (b + 3) [binSearchProc])
    (hp4 : p.HasAt (b + 4) [compressGraphProc b]) :
    MeetsContract w p (b + 4) (compressGraphContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [compressGraphContract] at hpre
  rcases hpre with ⟨gAddr, workAddr, G, rfl, hG, hval, hn_lt, hdisj, hwbound, hw4⟩
  have hproc : p.procs[b + 4]? = some (compressGraphProc b) := hp4 0 (by simp)
  have hread : Cited.readGraph mem gAddr = G := graphAt_iff_readGraph.mp hG
  have hlt_g : gAddr < 2 ^ w := hwords gAddr (by simp)
  have hlt_w : workAddr < 2 ^ w := hwords workAddr (by simp)
  have hm_mem : mem (gAddr + 1) = G.m := graphAt_m hG
  have hm_lt_w : mem (gAddr + 1) < 2 ^ w := by rw [hm_mem]; omega
  have henc_len : G.encode.length = 2 + 2 * G.m := graph_encode_length G
  have hsort := heapSort_spec (w := w) hp0 hp1
  have hdedup := dedup_spec (w := w) hp2
  have hbs := binSearch_spec (w := w) hp3
  by_cases hm0 : G.m = 0
  · have hedges0 : G.edges = [] := List.eq_nil_of_length_eq_zero (by simpa [Cited.Graph.m] using hm0)
    have htriple :
        Triple w p
          (fun st => st = startState [gAddr, workAddr] mem pos)
          (compressGraphProc b)
          (fun o st' => o = .returned 0 ∧
            ActVertsSpec G (tab o.value fun i => st'.mem (workAddr + 2 * G.m + i)) ∧
            GraphAt st'.mem (workAddr + 4 * G.m)
              (compressGraph (tab o.value fun i => st'.mem (workAddr + 2 * G.m + i)) G) ∧
            MemFrame mem st'.mem workAddr (workAddr + 6 * G.m + 2))
          (fun _ => 950) := by
      wram_enter
      · subst hpre
        dsimp only [compressGraphProc]
        wram_step; wram_step; wram_step; wram_step; wram_step
        · refine ⟨rfl, ⟨by simp [Outcome.value, tab],
            by simp [Outcome.value, tab], by simp [hedges0]⟩, ?_, ?_⟩
          · rw [hm0]
            refine graphAt_of_cells
              (by simp [compressGraph, Outcome.value, tab])
              (by simp [compressGraph, Cited.Graph.m, compressEdges, hedges0])
              (fun j hj => by simp [compressGraph, Cited.Graph.m, compressEdges, hedges0] at hj)
          · rw [hm0]
            exact memFrame_trans (memFrame_update le_rfl (by omega)) (memFrame_update (by omega) (by omega))
        · wram_cost
    obtain ⟨o, st', c, hrun, ⟨rfl, hpost⟩, hcost⟩ := htriple (startState [gAddr, workAddr] mem pos) ω rfl
    refine ⟨compressGraphProc b, hproc, .returned 0, st', c, hrun, ?_, ?_⟩
    · refine ⟨by simp [Outcome.value], ?_⟩
      simpa [compressGraphContract, hread, Outcome.value] using hpost
    · simpa [compressGraphContract, hread, hm0] using hcost
  · have hm_pos : 0 < G.m := Nat.pos_of_ne_zero hm0
    let flatEdges : List ℕ := G.edges.flatMap fun e => [e.1, e.2]
    have hflat_len : flatEdges.length = 2 * G.m := by
      have := graph_encode_length G
      simp [Cited.Graph.encode, flatEdges] at this ⊢
      omega
    have hflat_get : ∀ j < 2 * G.m, mem (gAddr + 2 + j) = flatEdges.getD j 0 ∧
        mem (gAddr + 2 + j) < G.n := by
      intro j hj
      have hes : ListAt mem (gAddr + 2) flatEdges := by
        simpa [Nat.add_assoc] using (listAt_cons.mp (listAt_cons.mp hG).2).2
      have hge := hes.getElem (by omega : j < flatEdges.length)
      refine ⟨by simpa [List.getD_eq_getElem?_getD, hflat_len, hj] using hge, ?_⟩
      rcases Nat.even_or_odd' j with ⟨eIdx, rfl | rfl⟩
      · have he_lt : eIdx < G.m := by omega
        rw [graphAt_edge_fst hG he_lt]
        exact (hval _ (List.getElem_mem he_lt)).1
      · have he_lt : eIdx < G.m := by omega
        rw [show gAddr + 2 + (2 * eIdx + 1) = gAddr + 3 + 2 * eIdx by omega, graphAt_edge_snd hG he_lt]
        exact (hval _ (List.getElem_mem he_lt)).2
    let m2 := 2 * G.m
    let actAddr := workAddr + m2
    let gActAddr := actAddr + m2
    have htriple :
        Triple w p
          (fun st => st = startState [gAddr, workAddr] mem pos)
          (compressGraphProc b)
          (fun o st' => o.value ≤ m2 ∧
            ActVertsSpec G (tab o.value fun i => st'.mem (workAddr + 2 * G.m + i)) ∧
            GraphAt st'.mem (workAddr + 4 * G.m)
              (compressGraph (tab o.value fun i => st'.mem (workAddr + 2 * G.m + i)) G) ∧
            MemFrame mem st'.mem workAddr (workAddr + 6 * G.m + 2))
          (fun _ => 950 * (G.m * (2 * Nat.log 2 (2 * G.m + 2) + 1) + 1)) := by
      wram_enter
      · subst hpre
        dsimp only [compressGraphProc]
        wram_step; wram_step
        wram_step; wram_step; wram_step; wram_step
        let InvCopy : State → Prop := fun st =>
          st.regs 0 = gAddr ∧ st.regs 1 = workAddr ∧ st.regs 2 = G.m ∧
          st.regs 3 = m2 ∧ st.regs 4 = actAddr ∧ st.regs 5 = gActAddr ∧
          st.regs 7 ≤ m2 ∧
          (∀ j < st.regs 7, st.mem (workAddr + j) = mem (gAddr + 2 + j)) ∧
          MemFrame mem st.mem workAddr (workAddr + m2)
        have hloop_copy : Triple w p InvCopy
            (.loop (.bin .lt (.reg 7) (.reg 3))
              (.seq (.store (.bin .add (.reg 1) (.reg 7))
                (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 7))))
                (.assign 7 (.bin .add (.reg 7) (.const 1)))))
            (normalPost fun st' => InvCopy st' ∧ st'.regs 7 = m2)
            (fun st => (3 + 18 + 1) * (m2 - st.regs 7) + 3 + 1) := by
          refine Triple.loop_const_normal (fun st => m2 - st.regs 7)
            (fun st => if st.regs 7 < m2 then 1 else 0) 18
            (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
            (fun st hInv h0 => by
              simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
              exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, _, h7le, _⟩; omega⟩)
            (fun st hInv hne => ?_)
          simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
          rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr7, hcp, hfr⟩
          have hj_lt : st.regs 7 < m2 := hne
          have hmem_src : st.mem (gAddr + 2 + st.regs 7) = mem (gAddr + 2 + st.regs 7) :=
            hfr (gAddr + 2 + st.regs 7) (Or.inl (by omega))
          have hval_lt : st.mem (gAddr + 2 + st.regs 7) < 2 ^ w := by
            rw [hmem_src]; exact lt_trans (hflat_get _ hj_lt).2 hn_lt
          wram_enter
          · subst hpre
            wram_run
            · refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
                by simp [hr5], by simp; omega, ?_, ?_⟩, by simp; omega⟩
              · intro j hj
                simp only [Function.update_self] at hj
                dsimp only
                by_cases hjj : j = st.regs 7
                · subst hjj; rw [Function.update_self, hmem_src]
                · rw [Function.update_of_ne (by omega)]; exact hcp j (by omega)
              · exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
            · wram_cost
        refine runs_seq_triple_le hloop_copy ?_ (fun st1 hst1 => ?_)
        · refine ⟨by simp [startState], by simp [startState], by simp [startState, hm_mem],
            by simp [startState, m2, hm_mem], by simp [startState, actAddr, m2, hm_mem],
            by simp [startState, gActAddr, actAddr, m2, hm_mem], by simp,
            fun j hj => by simp at hj, memFrame_refl _ _ _⟩
        rcases hst1 with ⟨⟨hs1_0, hs1_1, hs1_2, hs1_3, hs1_4, hs1_5, _, hcp1, hfr1⟩, hs1_7⟩
        have hbuf_eq : tab m2 (fun i => st1.mem (workAddr + i)) = tab m2 (fun i => mem (gAddr + 2 + i)) := by
          simp only [tab]; refine List.map_congr_left fun i hi => hcp1 i (by simpa [hs1_7] using List.mem_range.mp hi)
        have hbuf_lt : ∀ i < m2, st1.mem (workAddr + i) < 2 ^ w := by
          intro i hi
          rw [hcp1 i (by omega)]
          exact lt_trans (hflat_get i hi).2 hn_lt
        refine runs_seq_call_le hsort (by eval_expr) (by wram_words) ⟨workAddr, m2, rfl, by omega, by omega, hw4, hbuf_lt⟩ ?_
        · intro v2 mem2 pos2 hpost2
          rcases hpost2 with ⟨_, hperm2, hpair2, hlt2, hfr2⟩
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hperm2 hpair2 hlt2 hfr2
          let st2 : State := { mem := mem2, regs := Function.update st1.regs 10 v2, pos := pos2 }
          have hfr12 : MemFrame mem mem2 workAddr (workAddr + m2) := memFrame_trans hfr1 hfr2
          refine runs_seq_call_le hdedup (by eval_expr)
            (by wram_words) ⟨workAddr, m2, actAddr, rfl, le_rfl, by omega, hw4, hlt2, hpair2⟩ ?_
          · intro nAct mem3 pos3 hpost3
            rcases hpost3 with ⟨hnAct_le, hstrict3, hmem_iff3, hlt3, hfr3⟩
            simp only [List.getD_cons_zero, List.getD_cons_succ] at hnAct_le hstrict3 hmem_iff3 hlt3 hfr3
            let st3 : State := { mem := mem3, regs := Function.update st2.regs 6 nAct, pos := pos3 }
            have hfr_all3 : MemFrame mem mem3 workAddr (workAddr + 4 * G.m) :=
              memFrame_trans (memFrame_mono hfr12 le_rfl (by omega)) (memFrame_mono hfr3 (by omega) (by omega))
            have hact_eq : ∀ u, u ∈ tab nAct (fun i => mem3 (actAddr + i)) ↔
                u ∈ tab m2 (fun i => mem (gAddr + 2 + i)) := by
              intro u
              rw [hmem_iff3, hperm2.mem_iff, hbuf_eq]
            have hact_spec : ActVertsSpec G (tab nAct fun i => mem3 (actAddr + i)) := by
              refine ⟨hstrict3, fun u hu => ?_, fun e he => ?_⟩
              · rw [hact_eq] at hu
                simp only [tab, List.mem_map, List.mem_range] at hu
                rcases hu with ⟨j, hj, rfl⟩
                exact (hflat_get j hj).2
              · rcases List.getElem_of_mem he with ⟨eIdx, he_lt, rfl⟩
                have he1 : G.edges[eIdx].1 = mem (gAddr + 2 + 2 * eIdx) := (graphAt_edge_fst hG he_lt).symm
                have he2 : G.edges[eIdx].2 = mem (gAddr + 2 + (2 * eIdx + 1)) := by
                  rw [show gAddr + 2 + (2 * eIdx + 1) = gAddr + 3 + 2 * eIdx by omega]
                  exact (graphAt_edge_snd hG he_lt).symm
                constructor
                · rw [hact_eq, he1]
                  simp only [tab, List.mem_map, List.mem_range]
                  exact ⟨2 * eIdx, by dsimp only [m2, Cited.Graph.m] at *; omega, rfl⟩
                · rw [hact_eq, he2]
                  simp only [tab, List.mem_map, List.mem_range]
                  exact ⟨2 * eIdx + 1, by dsimp only [m2, Cited.Graph.m] at *; omega, rfl⟩
            have hs3_2 : st3.regs 2 = G.m := by simp [st3, st2, hs1_2]
            have hs3_5 : st3.regs 5 = gActAddr := by simp [st3, st2, hs1_5]
            have hs3_6 : st3.regs 6 = nAct := by simp [st3, st2]
            wram_step; wram_step; wram_step
            let mem3_hdr : ℕ → ℕ :=
              Function.update (Function.update mem3 gActAddr nAct) (gActAddr + 1) G.m
            let InvMap : State → Prop := fun st =>
              st.regs 0 = gAddr ∧ st.regs 1 = workAddr ∧ st.regs 2 = G.m ∧
              st.regs 3 = m2 ∧ st.regs 4 = actAddr ∧ st.regs 5 = gActAddr ∧
              st.regs 6 = nAct ∧ st.regs 7 ≤ m2 ∧
              MemFrame mem3_hdr st.mem (gActAddr + 2) (workAddr + 6 * G.m + 2) ∧
              (∀ j < st.regs 7,
                st.mem (gActAddr + 2 + j) =
                  (tab nAct fun i => mem3 (actAddr + i)).idxOf (mem (gAddr + 2 + j)))
            let BMap := 35 * (Nat.log 2 (2 * G.m + 2) + 2) + 32
            have hloop_map : Triple w p InvMap
                (.loop (.bin .lt (.reg 7) (.reg 3))
                  (.seq (.assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 7))))
                  (.seq (.call 9 (b + 3) [.reg 4, .reg 6, .reg 8])
                  (.seq (.store (.bin .add (.bin .add (.reg 5) (.const 2)) (.reg 7)) (.reg 9))
                    (.assign 7 (.bin .add (.reg 7) (.const 1)))))))
                (normalPost fun st' => InvMap st' ∧ st'.regs 7 = m2)
                (fun st => (3 + BMap + 1) * (m2 - st.regs 7) + 3 + 1) := by
              refine Triple.loop_const_normal (fun st => m2 - st.regs 7)
                (fun st => if st.regs 7 < m2 then 1 else 0) BMap
                (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
                (fun st hInv h0 => by
                  simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
                  exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, _, _, h7le, _⟩; omega⟩)
                (fun st hInv hne => ?_)
              simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
              rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hfr_map, hmap⟩
              have hj_lt : st.regs 7 < m2 := hne
              have hsrc_eq3 : st.mem (gAddr + 2 + st.regs 7) = mem3 (gAddr + 2 + st.regs 7) := by
                have h1 := hfr_map (gAddr + 2 + st.regs 7)
                  (Or.inl (by dsimp only [gActAddr, actAddr, m2] at *; omega))
                dsimp only [mem3_hdr] at h1
                rw [h1, Function.update_of_ne (by dsimp only [gActAddr, actAddr, m2]; omega),
                  Function.update_of_ne (by dsimp only [gActAddr, actAddr, m2]; omega)]
              have hsrc_eq : st.mem (gAddr + 2 + st.regs 7) = mem (gAddr + 2 + st.regs 7) := by
                rw [hsrc_eq3]; exact hfr_all3 (gAddr + 2 + st.regs 7) (Or.inl (by omega))
              have hval_lt : st.mem (gAddr + 2 + st.regs 7) < 2 ^ w := by
                rw [hsrc_eq]; exact lt_trans (hflat_get _ hj_lt).2 hn_lt
              have hact_unchanged : ∀ i < nAct, st.mem (actAddr + i) = mem3 (actAddr + i) := by
                intro i hi
                have h1 := hfr_map (actAddr + i)
                  (Or.inl (by dsimp only [gActAddr, actAddr, m2] at *; omega))
                dsimp only [mem3_hdr] at h1
                rw [h1, Function.update_of_ne (by dsimp only [gActAddr, actAddr, m2]; omega),
                  Function.update_of_ne (by dsimp only [gActAddr, actAddr, m2]; omega)]
              have htab_same : tab nAct (fun i => st.mem (actAddr + i)) =
                  tab nAct (fun i => mem3 (actAddr + i)) := by
                simp only [tab]; exact List.map_congr_left fun i hi =>
                  hact_unchanged i (List.mem_range.mp hi)
              have hkey_mem : mem (gAddr + 2 + st.regs 7) ∈ tab nAct (fun i => st.mem (actAddr + i)) := by
                rw [htab_same, hact_eq]
                simp only [tab, List.mem_map, List.mem_range]
                exact ⟨st.regs 7, hj_lt, rfl⟩
              wram_enter
              · subst hpre
                wram_step
                refine runs_seq_call_le hbs (by eval_expr) (by wram_words) ?_ ?_
                · refine ⟨actAddr, nAct, mem (gAddr + 2 + st.regs 7), rfl, by omega, hw4,
                    fun i hi => by rw [hact_unchanged i hi]; exact hlt3 i hi,
                    by rw [htab_same]; exact hstrict3, hkey_mem⟩
                · intro vIdx mem4 pos4 hpost4
                  rcases hpost4 with ⟨rfl, hidx_lt, hidx_eq, _⟩
                  simp only [List.getD_cons_zero, List.getD_cons_succ, htab_same] at hidx_lt hidx_eq
                  wram_run
                  · refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3],
                        by simp [hr4], by simp [hr5], by simp [hr6], by simp; omega,
                        ?_, ?_⟩, by simp; omega⟩
                    · exact memFrame_trans hfr_map
                        (memFrame_update (by dsimp only [gActAddr, actAddr, m2] at *; omega)
                          (by dsimp only [gActAddr, actAddr, m2] at *; omega))
                    · intro j hj
                      simp at hj
                      dsimp only
                      by_cases hjj : j = st.regs 7
                      · subst hjj; rw [hr5, Function.update_self, hidx_eq]
                      · rw [hr5, Function.update_of_ne (by omega)]; exact hmap j (by omega)
                  · have hlog_le : Nat.log 2 (nAct + 2) ≤ Nat.log 2 (2 * G.m + 2) :=
                      Nat.log_mono_right (by omega)
                    simp [binSearchContract]
                    dsimp only [BMap]
                    wram_cost
            refine runs_seq_triple_le hloop_map ?_ (fun stEnd hstEnd => ?_)
            · refine ⟨by simp [hs1_0], by simp [hs1_1],
                by simp [hs1_2], by simp [hs1_3],
                by simp [hs1_4], by simp [hs1_5],
                by simp, Nat.zero_le _, memFrame_refl _ _ _, fun j hj => by simp at hj⟩
            · wram_step
              · rcases hstEnd with ⟨⟨_, _, _, _, _, _, hr6', _, hfr_map', hmap'⟩, hr7_eq⟩
                have hgAct0 : stEnd.mem gActAddr = nAct := by
                  have h1 := hfr_map' gActAddr (Or.inl (by dsimp only [gActAddr, actAddr, m2]; omega))
                  dsimp only [mem3_hdr] at h1
                  rw [h1, Function.update_of_ne (by omega), Function.update_self]
                have hgAct1 : stEnd.mem (gActAddr + 1) = G.m := by
                  have h1 := hfr_map' (gActAddr + 1) (Or.inl (by dsimp only [gActAddr, actAddr, m2]; omega))
                  dsimp only [mem3_hdr] at h1
                  rw [h1, Function.update_self]
                have hact_final : ∀ i < nAct, stEnd.mem (actAddr + i) = mem3 (actAddr + i) := by
                  intro i hi
                  have h1 := hfr_map' (actAddr + i) (Or.inl (by dsimp only [gActAddr, actAddr, m2]; omega))
                  dsimp only [mem3_hdr] at h1
                  rw [h1, Function.update_of_ne (by dsimp only [gActAddr, actAddr, m2]; omega),
                    Function.update_of_ne (by dsimp only [gActAddr, actAddr, m2]; omega)]
                have htab_final : tab nAct (fun i => stEnd.mem (actAddr + i)) =
                    tab nAct (fun i => mem3 (actAddr + i)) := by
                  simp only [tab]; exact List.map_congr_left fun i hi => hact_final i (List.mem_range.mp hi)
                have hgAct_graph : GraphAt stEnd.mem (workAddr + 4 * G.m)
                    (compressGraph (tab nAct fun i => stEnd.mem (actAddr + i)) G) := by
                  rw [htab_final, show workAddr + 4 * G.m = gActAddr by dsimp only [gActAddr, actAddr, m2]; omega]
                  refine graphAt_of_cells (by simpa [compressGraph, tab] using hgAct0)
                    (by simpa [compressGraph_m] using hgAct1) (fun j hj => ?_)
                  have hjG : j < G.m := by simpa [compressGraph_m] using hj
                  have hjE : j < G.edges.length := by simpa [Cited.Graph.m] using hjG
                  have hce : ((compressGraph (tab nAct fun i => mem3 (actAddr + i)) G).edges[j]'(by
                      simpa [compressGraph_m, Cited.Graph.m] using hj)) =
                      ((tab nAct fun i => mem3 (actAddr + i)).idxOf (G.edges[j]'hjE).1,
                        (tab nAct fun i => mem3 (actAddr + i)).idxOf (G.edges[j]'hjE).2) := by
                    simp [compressGraph, compressEdges]
                  rw [hce]
                  have h1 := hmap' (2 * j) (by rw [hr7_eq]; dsimp only [m2, Cited.Graph.m] at *; omega)
                  have h2 := hmap' (2 * j + 1) (by rw [hr7_eq]; dsimp only [m2, Cited.Graph.m] at *; omega)
                  rw [show gActAddr + 2 + (2 * j + 1) = gActAddr + 3 + 2 * j by omega,
                    show gAddr + 2 + (2 * j + 1) = gAddr + 3 + 2 * j by omega] at h2
                  rw [h1, h2, graphAt_edge_fst hG hjE, graphAt_edge_snd hG hjE]
                  exact ⟨rfl, rfl⟩
                have hfr_final : MemFrame mem stEnd.mem workAddr (workAddr + 6 * G.m + 2) := by
                  have hfr_m3 : MemFrame mem mem3 workAddr (workAddr + 6 * G.m + 2) :=
                    memFrame_mono hfr_all3 le_rfl (by omega)
                  have hfr_3e : MemFrame mem3 stEnd.mem workAddr (workAddr + 6 * G.m + 2) := by
                    have hfr_hdr : MemFrame mem3 mem3_hdr gActAddr (workAddr + 6 * G.m + 2) :=
                      memFrame_trans
                        (memFrame_update le_rfl (by dsimp only [gActAddr, actAddr, m2]; omega))
                        (memFrame_update (by dsimp only [gActAddr, actAddr, m2]; omega)
                          (by dsimp only [gActAddr, actAddr, m2]; omega))
                    exact memFrame_mono (memFrame_trans hfr_hdr (memFrame_mono hfr_map'
                      (by dsimp only [gActAddr, actAddr, m2]; omega) le_rfl))
                      (by dsimp only [gActAddr, actAddr, m2]; omega) le_rfl
                  exact memFrame_trans hfr_m3 hfr_3e
                refine ⟨by simp [Outcome.value, hr6']; dsimp only [m2]; exact hnAct_le,
                  ?_, ?_, hfr_final⟩
                · rw [show workAddr + 2 * G.m = actAddr by dsimp only [actAddr, m2]]
                  simpa [Outcome.value, hr6', htab_final] using hact_spec
                · simpa [Outcome.value, hr6'] using hgAct_graph
              · dsimp only [heapSortContract, dedupContract, BMap, m2, startState]
                simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
                  argsSize_cons, argsSize_nil, Function.update_apply, ite_true,
                  Nat.sub_zero, List.getD_cons_zero, List.getD_cons_succ, hm_mem]
                set L := Nat.log 2 (2 * G.m + 2)
                ring_nf
                set ML := G.m * L
                omega
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [gAddr, workAddr] mem pos) ω rfl
    refine ⟨compressGraphProc b, hproc, o, st', c, hrun, ?_, ?_⟩
    · simpa [compressGraphContract, hread] using hpost
    · simpa [compressGraphContract, hread] using hcost

/-- Procedure bundle for active-vertex compression (`5` procedures at `b, …, b + 4`):
`siftDown` (`b + 0`), `heapSort` (`b + 1`), `dedup` (`b + 2`), `binSearch` (`b + 3`),
and `compressGraph` (`b + 4`). -/
def activeSortProcs (b : ℕ) : List Stmt :=
  [siftDownProc, heapSortProc b, dedupProc, binSearchProc, compressGraphProc b]

lemma activeSortProcs_length (b : ℕ) : (activeSortProcs b).length = 5 := rfl

lemma activeSortProcs_noRand (b : ℕ) : ∀ s ∈ activeSortProcs b, s.NoRand := by
  intro s hs
  simp only [activeSortProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact siftDownProc_noRand
  · exact heapSortProc_noRand b
  · exact dedupProc_noRand
  · exact binSearchProc_noRand
  · exact compressGraphProc_noRand b

theorem compressGraph_meets {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (activeSortProcs b)) :
    MeetsContract w p (b + 4) (compressGraphContract w) :=
  compressGraph_spec
    (fun i hi => by simp at hi; subst hi; exact hp 0 (by simp [activeSortProcs]))
    (fun i hi => by simp at hi; subst hi; exact hp 1 (by simp [activeSortProcs]))
    (fun i hi => by simp at hi; subst hi; exact hp 2 (by simp [activeSortProcs]))
    (fun i hi => by simp at hi; subst hi; exact hp 3 (by simp [activeSortProcs]))
    (fun i hi => by simp at hi; subst hi; exact hp 4 (by simp [activeSortProcs]))

end MinCostFlow.Expander
