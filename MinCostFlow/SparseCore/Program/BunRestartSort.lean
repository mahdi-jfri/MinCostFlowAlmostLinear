module

public import MinCostFlow.SparseCore.Program.BunRestartPhaseD
public import MinCostFlow.DynSpanner.Program.MergeSort

import WordRAM.Tactic

/-!
# The restart of the bundles: the sort of the owners (`BunRestartSort`)

After phase C, the owners of the `2 E` keys are at `h + 6 n + 4 E`. The sort step sorts them in
place, with the scratch array at `h + 6 n + 6 E`, and writes them without repeats at
`h + 6 n + 8 E` (`brSort_runs`). This list is `rList`, the vertices whose tour lists P5's
initialization of slots walks.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

variable {w : ℕ} {p : Program} {ω : ℕ → Bool} {n h E : ℕ}

/-- A strictly increasing list whose members are those of `L` is not longer than `L`. -/
theorem length_le_of_pairwise_lt {L R : List ℕ} (hR : R.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ R ↔ x ∈ L) : R.length ≤ L.length := by
  have hnd : R.Nodup := hR.imp fun h => Nat.ne_of_lt h
  rw [← List.toFinset_card_of_nodup hnd]
  have : R.toFinset = L.toFinset := by
    ext x; simp only [List.mem_toFinset]; exact hmem x
  rw [this]
  exact List.toFinset_card_le L

/-- **The sort step.** With the owners `L` (`2 E` words) at `h + 6 n + 4 E`, the sort step writes
a strictly increasing list `rList` with the members of `L` at `h + 6 n + 8 E`, and its length in
register `26`. It changes only registers `21` and `26` and the memory in
`[h + 6 n + 4 E, h + 6 n + 10 E)`. -/
theorem brSort_runs {bSort : ℕ} (hpSort : p.HasAt bSort (sortProcs bSort)) {st : State}
    {L : List ℕ} (hL : BRRegsL st.regs h n E) (hw : 16 ≤ 2 ^ w) (hfit : h + 6 * n + 10 * E < 2 ^ w)
    (hlen : L.length = 2 * E) (hlist : ListAt st.mem (h + 6 * n + 4 * E) L)
    (hLw : ∀ x ∈ L, x < 2 ^ w) :
    ∃ st' c rList, Runs w p ω (brSortStmt bSort) st .normal st' c ∧
      rList.Pairwise (· < ·) ∧ (∀ x, x ∈ rList ↔ x ∈ L) ∧ rList.length ≤ 2 * E ∧
      ListAt st'.mem (h + 6 * n + 8 * E) rList ∧ st'.regs 26 = rList.length ∧
      (∀ r, r ≠ 21 → r ≠ 26 → st'.regs r = st.regs r) ∧
      (∀ a, (a < h + 6 * n + 4 * E ∨ h + 6 * n + 10 * E ≤ a) → st'.mem a = st.mem a) ∧
      c ≤ 400 * E * (Nat.log 2 (2 * E + 1) + 1) + 90 * E + 100 := by
  have h9 := hL.r9
  have h15 := hL.r15
  have h16 := hL.r16
  have h17 := hL.r17
  have hms := mergeSort_meetsContract (w := w) (p := p) (b := bSort) (bSort := bSort) (L := L)
    hpSort hpSort
  obtain ⟨st', c, hr, ⟨rList, h1, h2, h3, h4, h5, h6, h7⟩, hc⟩ := normal_of_fwd (w := w)
    (p := p) (ω := ω) (s := brSortStmt bSort) (st := st)
    (K := 400 * E * (Nat.log 2 (2 * E + 1) + 1) + 90 * E + 100)
    (P := fun st' => ∃ rList, rList.Pairwise (· < ·) ∧ (∀ x, x ∈ rList ↔ x ∈ L) ∧
      rList.length ≤ 2 * E ∧ ListAt st'.mem (h + 6 * n + 8 * E) rList ∧
      st'.regs 26 = rList.length ∧ (∀ r, r ≠ 21 → r ≠ 26 → st'.regs r = st.regs r) ∧
      (∀ a, (a < h + 6 * n + 4 * E ∨ h + 6 * n + 10 * E ≤ a) → st'.mem a = st.mem a)) (by
    unfold brSortStmt
    refine runs_seq_call_le hms (vs := [h + 6 * n + 4 * E, L.length, h + 6 * n + 6 * E])
      (by rw [hlen]; eval_expr) (by intro v hv; simp at hv; omega)
      ⟨_, _, rfl, hw, by omega, by omega, Or.inl (by omega), hlist, hLw⟩
      (fun v mem' pos' hpost => ?_)
    obtain ⟨a, scr, L', hargs, -, hperm, hsorted, hlist', hfr'⟩ := hpost
    simp only [List.cons.injEq, and_true, true_and] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    have hlen' : L'.length = L.length := hperm.length_eq
    have hL'w : ∀ x ∈ L', x < 2 ^ w := fun x hx => hLw x (hperm.subset hx)
    have hdd := dedup_meetsContract (w := w) (p := p) (b := bSort) (bSort := bSort) (L := L')
      hpSort
    have h15' : Function.update st.regs 21 v 15 = h + 6 * n + 4 * E := by simp [h15]
    have h17' : Function.update st.regs 21 v 17 = h + 6 * n + 8 * E := by simp [h17]
    have h9' : Function.update st.regs 21 v 9 = E := by simp [h9]
    refine runs_call_le hdd (vs := [h + 6 * n + 4 * E, L'.length, h + 6 * n + 8 * E])
      (by rw [hlen', hlen]; eval_expr) (by intro v hv; simp at hv; omega)
      ⟨_, _, rfl, hw, by omega, by omega, Or.inl (by omega), hsorted, hlist', hL'w⟩
      (fun v' mem'' pos'' hpost' => ?_)
    obtain ⟨src, dst, hargs', hret, hlt, hmem, hlist'', hfr''⟩ := hpost'
    simp only [List.cons.injEq, and_true, true_and] at hargs'
    obtain ⟨rfl, rfl⟩ := hargs'
    have hrlen : (sortedDedup L').length ≤ 2 * E := by
      rw [← hlen, ← hlen']
      exact length_le_of_pairwise_lt hlt hmem
    refine ⟨⟨sortedDedup L', hlt, fun x => (hmem x).trans hperm.mem_iff, hrlen, hlist'',
      by simp [hret], fun r h1 h2 => by simp [h1, h2], fun a ha => ?_⟩, ?_⟩
    · show mem'' a = st.mem a
      rw [hfr'' a (by omega)]
      exact hfr' a (by omega) (by omega)
    · simp only [mergeSortContract, dedupContract, argsSize_cons, argsSize_nil, Expr.size,
        hlen', hlen]
      have hlog := Nat.mul_le_mul_left (2 * E) (Nat.le_refl (Nat.log 2 (2 * E + 1) + 1))
      nlinarith)
  exact ⟨st', c, rList, hr, h1, h2, h3, h4, h5, h6, h7, hc⟩

end

end MinCostFlow.SparseCore.Program.Restart
