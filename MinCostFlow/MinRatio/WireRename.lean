module

public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.MinRatio.FreshTables
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Renaming the internal edges at a rebuild of level `0`

A rebuild of level `0` of Algorithm 1 (page 20) starts every level from scratch, so the ordered
model gives the live internal edges the names `0, …, |E| - 1` in increasing order of their old
names (`Chain.Ordered.level0E2I`, `level0I2E`, `level0NF`). This keeps the number of internal
names bounded. This file gives the Word-RAM procedure that does the same renaming on the name
tables, and proves that it produces exactly the tables of the model.

The procedure `level0RenameBody` takes `[bits, cap, forward, extCap, inverse, counter, heap]`.
The cells `bits + j` for `j < cap` hold the presence bits of the live set `E` (for example the
edge presence table of a `DynGraphAt` block). It runs three passes.
1. One pass over the bits computes the rank `compactRank E j` of every `j < cap` into
   `heap + j`, and writes the `r`-th smallest live name `compactUnrank E r` into
   `heap + cap + r`.
2. One pass over the forward table replaces `e2i e` by `compactRank E (e2i e)`. A name at or
   above `cap` has rank `|E|`.
3. One pass over `j < |E|` replaces the inverse entry `i2e j` by `i2e (compactUnrank E j)`. The
   pass works in place: since `j ≤ compactUnrank E j`, the entry it reads has not been
   overwritten yet. Entries at `j ≥ |E|` stay, as `compactUnrank E j = j` there.
Then it sets the counter to `|E|` and returns `|E|`. The cost is linear in `cap + extCap`.

The main result is `level0RenameBody_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain.Ordered

/-- Pass 1: ranks into `heap + j`, sorted live names into `heap + cap + r`, count in `reg 11`. -/
@[expose] def renameRankLoop : Stmt :=
  .assign 11 (.const 0) ;;
  forRange 10 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 6) (.reg 10)) (.reg 11) ;;
     .cond (.load (.bin .add (.reg 0) (.reg 10)))
       (.store (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 11)) (.reg 10) ;;
        .assign 11 (.bin .add (.reg 11) (.const 1)))
       .nop)

/-- Pass 2: rewrite the forward table through the ranks. -/
@[expose] def renameForwardLoop : Stmt :=
  forRange 12 (.const 0) (.reg 3)
    (.assign 13 (.load (.bin .add (.reg 2) (.reg 12))) ;;
     .cond (.bin .lt (.reg 13) (.reg 1))
       (.store (.bin .add (.reg 2) (.reg 12)) (.load (.bin .add (.reg 6) (.reg 13))))
       (.store (.bin .add (.reg 2) (.reg 12)) (.reg 11)))

/-- Pass 3: rewrite the inverse table in place through the sorted live names. -/
@[expose] def renameInverseLoop : Stmt :=
  forRange 14 (.const 0) (.reg 11)
    (.store (.bin .add (.reg 4) (.reg 14))
      (.load (.bin .add (.reg 4) (.load (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 14))))))

/-- The renaming procedure `[bits, cap, forward, extCap, inverse, counter, heap]`. -/
@[expose] def level0RenameBody : Stmt :=
  renameRankLoop ;;
  renameForwardLoop ;;
  renameInverseLoop ;;
  .store (.reg 5) (.reg 11) ;;
  .ret (.reg 11)

theorem level0RenameBody_noRand : level0RenameBody.NoRand := by
  simp [level0RenameBody, renameRankLoop, renameForwardLoop, renameInverseLoop, forRange, forUp,
    Stmt.NoRand]

/-! ### Facts on ranks -/

private theorem compactRank_zero (E : Finset ℕ) : compactRank E 0 = 0 := by
  simp [compactRank]

private theorem compactRank_succ (E : Finset ℕ) (j : ℕ) :
    compactRank E (j + 1) = compactRank E j + if j ∈ E then 1 else 0 := by
  unfold compactRank
  by_cases h : j ∈ E
  · rw [ite_eq_left h, show E.filter (· < j + 1) = insert j (E.filter (· < j)) from ?_,
      Finset.card_insert_of_notMem (by simp)]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
      · exact Or.inr ⟨hx, h'⟩
      · exact Or.inl h'
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨h, by omega⟩
      · exact ⟨hx, by omega⟩
  · rw [ite_eq_right h, add_zero]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hlt⟩
      refine ⟨hx, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | rfl
      · exact h'
      · exact absurd hx h
    · rintro ⟨hx, hlt⟩
      exact ⟨hx, by omega⟩

private theorem compactRank_le_self (E : Finset ℕ) (j : ℕ) : compactRank E j ≤ j := by
  unfold compactRank
  calc (E.filter (· < j)).card ≤ (Finset.range j).card :=
        Finset.card_le_card (fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2)
    _ = j := Finset.card_range j

private theorem compactRank_of_ge {E : Finset ℕ} {cap v : ℕ} (hE : ∀ x ∈ E, x < cap)
    (hv : cap ≤ v) : compactRank E v = E.card := by
  unfold compactRank
  rw [Finset.filter_true_of_mem (fun x hx => lt_of_lt_of_le (hE x hx) hv)]

private theorem le_compactUnrank (E : Finset ℕ) (j : ℕ) : j ≤ compactUnrank E j := by
  by_cases h : j < E.card
  · have := compactRank_le_self E (compactUnrank E j)
    rwa [compactRank_unrank h] at this
  · simp [compactUnrank, h]

private theorem compactUnrank_of_ge {E : Finset ℕ} {j : ℕ} (h : ¬ j < E.card) :
    compactUnrank E j = j := by
  simp [compactUnrank, h]

/-! ### Pass 1 -/

private theorem renameRankLoop_runs {w bits cap heap : ℕ} {E : Finset ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (hr0 : st.regs 0 = bits) (hr1 : st.regs 1 = cap) (hr6 : st.regs 6 = heap)
    (hbits : ∀ j < cap, st.mem (bits + j) = if j ∈ E then 1 else 0)
    (hE : ∀ x ∈ E, x < cap) (hbitsHeap : bits + cap ≤ heap)
    (hW : heap + 2 * cap < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω renameRankLoop st .normal out cost ∧
      cost ≤ 40 * cap + 20 ∧
      out.regs 11 = E.card ∧
      (∀ r, r ≠ 10 → r ≠ 11 → out.regs r = st.regs r) ∧
      (∀ x < cap, out.mem (heap + x) = compactRank E x) ∧
      (∀ j < E.card, out.mem (heap + cap + j) = compactUnrank E j) ∧
      (∀ a, a < heap ∨ heap + 2 * cap ≤ a → out.mem a = st.mem a) := by
  let s1 : State := { st with regs := Function.update st.regs 11 0 }
  have r1 : Runs w p ω (.assign 11 (.const 0)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ cap ∧ s.regs 10 = j ∧ s.regs 11 = compactRank E j ∧
    (∀ r, r ≠ 10 → r ≠ 11 → s.regs r = st.regs r) ∧
    (∀ x < j, s.mem (heap + x) = compactRank E x) ∧
    (∀ r < compactRank E j, s.mem (heap + cap + r) = compactUnrank E r) ∧
    (∀ a, a < heap ∨ heap + 2 * cap ≤ a → s.mem a = st.mem a)
  have hstep : ∀ j, 0 ≤ j → j < cap →
      Triple w p (Inv j)
        (.store (.bin .add (.reg 6) (.reg 10)) (.reg 11) ;;
         .cond (.load (.bin .add (.reg 0) (.reg 10)))
           (.store (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 11)) (.reg 10) ;;
            .assign 11 (.bin .add (.reg 11) (.const 1)))
           .nop)
        (normalPost fun s' => Inv (j + 1) { s' with regs := Function.update s'.regs 10 (j + 1) } ∧
          s'.regs 10 = j) (fun _ => 30) := by
    intro j _ hj s bits' ⟨_, hjr, hcr, hregs, hrank, hunr, hfr⟩
    have hcle : compactRank E j ≤ j := compactRank_le_self E j
    have h6 : s.regs 6 = heap := (hregs 6 (by decide) (by decide)).trans hr6
    have h0 : s.regs 0 = bits := (hregs 0 (by decide) (by decide)).trans hr0
    have h1 : s.regs 1 = cap := (hregs 1 (by decide) (by decide)).trans hr1
    let c := compactRank E j
    let sa : State := { s with mem := Function.update s.mem (heap + j) c }
    have ra : Runs w p bits' (.store (.bin .add (.reg 6) (.reg 10)) (.reg 11)) s .normal sa 5 :=
      runs_store_iff.mpr ⟨heap + j, c,
        by simp [Expr.eval, BinOp.eval, h6, hjr, show heap + j < 2 ^ w by omega],
        by simp [Expr.eval, hcr, c], rfl, rfl, by simp [Expr.size]⟩
    have hbitv : sa.mem (bits + j) = if j ∈ E then 1 else 0 := by
      simp only [sa, Function.update_of_ne (show bits + j ≠ heap + j by omega)]
      rw [hfr _ (Or.inl (by omega))]
      exact hbits j hj
    by_cases hjE : j ∈ E
    · let sb : State := { sa with mem := Function.update sa.mem (heap + cap + c) j }
      let sc : State := { sb with regs := Function.update sb.regs 11 (c + 1) }
      have rb : Runs w p bits' (.store (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 11)) (.reg 10))
          sa .normal sb 7 :=
        runs_store_iff.mpr ⟨heap + cap + c, j,
          by simp [Expr.eval, BinOp.eval, sa, h6, h1, hcr, c, show heap + cap < 2 ^ w by omega,
            show heap + cap + compactRank E j < 2 ^ w by omega],
          by simp [Expr.eval, sa, hjr], rfl, rfl, by simp [Expr.size]⟩
      have rc : Runs w p bits' (.assign 11 (.bin .add (.reg 11) (.const 1))) sb .normal sc 4 :=
        runs_assign_iff.mpr ⟨c + 1,
          by simp [Expr.eval, BinOp.eval, sb, sa, hcr, c, show 1 < 2 ^ w from hw1,
            show compactRank E j + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have rthen : Runs w p bits'
          (.store (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 11)) (.reg 10) ;;
            .assign 11 (.bin .add (.reg 11) (.const 1))) sa .normal sc 12 :=
        runs_seq_iff.mpr (Or.inr ⟨sb, 7, 4, rb, rc, rfl⟩)
      have rcond : Runs w p bits'
          (.cond (.load (.bin .add (.reg 0) (.reg 10)))
            (.store (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 11)) (.reg 10) ;;
              .assign 11 (.bin .add (.reg 11) (.const 1))) .nop) sa .normal sc 17 :=
        runs_cond_iff.mpr ⟨1, 12,
          by rw [show (Expr.load (.bin .add (.reg 0) (.reg 10))).eval w sa = some (sa.mem (bits + j))
              by simp [Expr.eval, BinOp.eval, show sa.regs = s.regs from rfl, h0, hjr,
                show bits + j < 2 ^ w by omega], hbitv, ite_eq_left hjE],
          by simpa using rthen, by simp [Expr.size]⟩
      refine ⟨.normal, sc, 23, runs_seq_iff.mpr (Or.inr ⟨sa, 5, 17, ra, rcond, rfl⟩), ⟨⟨by omega,
        by simp, ?_, ?_, ?_, ?_, ?_⟩, by simp [sc, sb, sa, hjr]⟩, by dsimp only; omega⟩
      · simp [sc, compactRank_succ, hjE, c]
      · intro r hr10 hr11
        simp [sc, sb, sa, Function.update_of_ne hr10, Function.update_of_ne hr11, hregs r hr10 hr11]
      · intro x hx
        simp only [sc, sb, sa]
        rw [Function.update_of_ne (show heap + x ≠ heap + cap + c by omega)]
        by_cases hxj : x = j
        · subst hxj; simp [c]
        · rw [Function.update_of_ne (show heap + x ≠ heap + j by omega)]
          exact hrank x (by omega)
      · intro r hr
        rw [compactRank_succ, ite_eq_left hjE] at hr
        simp only [sc, sb, sa]
        by_cases hrc : r = c
        · subst hrc; simp [compactUnrank_rank hjE, c]
        · rw [Function.update_of_ne (show heap + cap + r ≠ heap + cap + c by omega),
            Function.update_of_ne (show heap + cap + r ≠ heap + j by omega)]
          exact hunr r (by omega)
      · intro a ha
        simp only [sc, sb, sa]
        rw [Function.update_of_ne (show a ≠ heap + cap + c by omega),
          Function.update_of_ne (show a ≠ heap + j by omega)]
        exact hfr a ha
    · have rcond : Runs w p bits'
          (.cond (.load (.bin .add (.reg 0) (.reg 10)))
            (.store (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 11)) (.reg 10) ;;
              .assign 11 (.bin .add (.reg 11) (.const 1))) .nop) sa .normal sa 6 :=
        runs_cond_iff.mpr ⟨0, 1,
          by rw [show (Expr.load (.bin .add (.reg 0) (.reg 10))).eval w sa = some (sa.mem (bits + j))
              by simp [Expr.eval, BinOp.eval, show sa.regs = s.regs from rfl, h0, hjr,
                show bits + j < 2 ^ w by omega], hbitv, ite_eq_right hjE],
          by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ :
            Runs w p bits' .nop sa .normal sa 1), by simp [Expr.size]⟩
      refine ⟨.normal, sa, 12, runs_seq_iff.mpr (Or.inr ⟨sa, 5, 6, ra, rcond, rfl⟩), ⟨⟨by omega,
        by simp, ?_, ?_, ?_, ?_, ?_⟩, by simp [sa, hjr]⟩, by dsimp only; omega⟩
      · simp [sa, compactRank_succ, hjE, hcr]
      · intro r hr10 hr11
        simp [sa, Function.update_of_ne hr10, hregs r hr10 hr11]
      · intro x hx
        simp only [sa]
        by_cases hxj : x = j
        · subst hxj; simp [c]
        · rw [Function.update_of_ne (show heap + x ≠ heap + j by omega)]
          exact hrank x (by omega)
      · intro r hr
        rw [compactRank_succ, ite_eq_right hjE, add_zero] at hr
        simp only [sa]
        rw [Function.update_of_ne (show heap + cap + r ≠ heap + j by omega)]
        exact hunr r hr
      · intro a ha
        simp only [sa]
        rw [Function.update_of_ne (show a ≠ heap + j by omega)]
        exact hfr a ha
  have hcapW : cap < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = s1) (Inv := Inv)
    (r := 10) (lo := .const 0) (hi := .reg 1) 30 0 cap (Nat.zero_le _) hw1 (fun _ => hcapW)
    (by
      intro s hs; subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        by simp [s1, compactRank_zero], fun r hr10 hr11 => by
          simp [s1, Function.update_of_ne hr10, Function.update_of_ne hr11],
        fun x hx => by omega, fun r hr => by simp [compactRank_zero] at hr, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.2.1 1 (by decide) (by decide)).trans hr1])
    hstep
  obtain ⟨o, out, cost, hr, hInv, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv
  | normal =>
    obtain ⟨_, _, h11, hregs, hrank, hunr, hfr⟩ := hInv
    have hcard : compactRank E cap = E.card := compactRank_of_ge hE le_rfl
    refine ⟨out, 2 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨s1, 2, cost, r1, hr, rfl⟩), ?_,
      h11.trans hcard, fun r hr10 hr11 => hregs r hr10 hr11, hrank,
      fun j hj => hunr j (by omega), hfr⟩
    simp [Expr.size] at hc
    omega

/-! ### Pass 2 -/

private theorem renameForwardLoop_runs {w forward extCap cap heap : ℕ} {E : Finset ℕ}
    {e2i : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hr1 : st.regs 1 = cap) (hr2 : st.regs 2 = forward) (hr3 : st.regs 3 = extCap)
    (hr6 : st.regs 6 = heap) (hr11 : st.regs 11 = E.card)
    (hfwd : ∀ e < extCap, st.mem (forward + e) = e2i e)
    (hrank : ∀ x < cap, st.mem (heap + x) = compactRank E x)
    (hE : ∀ x ∈ E, x < cap) (hfH : forward + extCap ≤ heap)
    (hW : heap + cap < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω renameForwardLoop st .normal out cost ∧
      cost ≤ 40 * extCap + 20 ∧
      (∀ r, r ≠ 12 → r ≠ 13 → out.regs r = st.regs r) ∧
      (∀ e < extCap, out.mem (forward + e) = compactRank E (e2i e)) ∧
      (∀ a, a < forward ∨ forward + extCap ≤ a → out.mem a = st.mem a) := by
  let Inv (e : ℕ) (s : State) : Prop :=
    e ≤ extCap ∧ s.regs 12 = e ∧
    (∀ r, r ≠ 12 → r ≠ 13 → s.regs r = st.regs r) ∧
    (∀ x < e, s.mem (forward + x) = compactRank E (e2i x)) ∧
    (∀ a, a < forward ∨ forward + e ≤ a → s.mem a = st.mem a)
  have hstep : ∀ e, 0 ≤ e → e < extCap →
      Triple w p (Inv e)
        (.assign 13 (.load (.bin .add (.reg 2) (.reg 12))) ;;
         .cond (.bin .lt (.reg 13) (.reg 1))
           (.store (.bin .add (.reg 2) (.reg 12)) (.load (.bin .add (.reg 6) (.reg 13))))
           (.store (.bin .add (.reg 2) (.reg 12)) (.reg 11)))
        (normalPost fun s' => Inv (e + 1) { s' with regs := Function.update s'.regs 12 (e + 1) } ∧
          s'.regs 12 = e) (fun _ => 30) := by
    intro e _ he s bits' ⟨_, her, hregs, hdone, hfr⟩
    have h1 : s.regs 1 = cap := (hregs 1 (by decide) (by decide)).trans hr1
    have h2 : s.regs 2 = forward := (hregs 2 (by decide) (by decide)).trans hr2
    have h6 : s.regs 6 = heap := (hregs 6 (by decide) (by decide)).trans hr6
    have h11 : s.regs 11 = E.card := (hregs 11 (by decide) (by decide)).trans hr11
    have hfeW : forward + e < 2 ^ w := by omega
    let v := e2i e
    have hv : s.mem (forward + e) = v := (hfr _ (Or.inr le_rfl)).trans (hfwd e he)
    let sa : State := { s with regs := Function.update s.regs 13 v }
    have ra : Runs w p bits' (.assign 13 (.load (.bin .add (.reg 2) (.reg 12)))) s .normal sa 5 :=
      runs_assign_iff.mpr ⟨v, by simp [Expr.eval, BinOp.eval, h2, her, hfeW, hv], rfl, rfl,
        by simp [Expr.size]⟩
    let sb : State := { sa with mem := Function.update sa.mem (forward + e) (compactRank E v) }
    have hcond : ∃ c, Runs w p bits'
        (.cond (.bin .lt (.reg 13) (.reg 1))
          (.store (.bin .add (.reg 2) (.reg 12)) (.load (.bin .add (.reg 6) (.reg 13))))
          (.store (.bin .add (.reg 2) (.reg 12)) (.reg 11))) sa .normal sb c ∧ c ≤ 12 := by
      have haddr : (Expr.bin .add (.reg 2) (.reg 12)).eval w sa = some (forward + e) := by
        simp [Expr.eval, BinOp.eval, sa, h2, her, hfeW]
      by_cases hvc : v < cap
      · have hval : (Expr.load (.bin .add (.reg 6) (.reg 13))).eval w sa = some (compactRank E v) := by
          simp [Expr.eval, BinOp.eval, sa, h6, show heap + v < 2 ^ w by omega,
            hfr _ (Or.inr (show forward + e ≤ heap + v by omega)),
            ← hrank v hvc]
        refine ⟨3 + 8 + 1, runs_cond_iff.mpr ⟨1, 8,
          by simp [Expr.eval, BinOp.eval, sa, h1, hvc, hw1], ?_, rfl⟩, le_rfl⟩
        simpa using (runs_store_iff.mpr ⟨forward + e, compactRank E v, haddr, hval, rfl, rfl,
          by simp [Expr.size]⟩ : Runs w p bits' (.store (.bin .add (.reg 2) (.reg 12))
            (.load (.bin .add (.reg 6) (.reg 13)))) sa .normal sb 8)
      · have hval : (Expr.reg 11).eval w sa = some (compactRank E v) := by
          simp [Expr.eval, sa, h11, compactRank_of_ge hE (not_lt.mp hvc)]
        refine ⟨3 + 5 + 1, runs_cond_iff.mpr ⟨0, 5,
          by simp [Expr.eval, BinOp.eval, sa, h1, hvc], ?_, rfl⟩, by omega⟩
        simpa using (runs_store_iff.mpr ⟨forward + e, compactRank E v, haddr, hval, rfl, rfl,
          by simp [Expr.size]⟩ : Runs w p bits' (.store (.bin .add (.reg 2) (.reg 12))
            (.reg 11)) sa .normal sb 5)
    obtain ⟨c, rc, hc⟩ := hcond
    refine ⟨.normal, sb, 5 + c + 1, runs_seq_iff.mpr (Or.inr ⟨sa, 5, c, ra, rc, rfl⟩),
      ⟨⟨by omega, by simp, ?_, ?_, ?_⟩, by simp [sb, sa, her]⟩, by dsimp only; omega⟩
    · intro r hr12 hr13
      simp [sb, sa, Function.update_of_ne hr12, Function.update_of_ne hr13, hregs r hr12 hr13]
    · intro x hx
      simp only [sb, sa]
      by_cases hxe : x = e
      · subst hxe; simp [v]
      · rw [Function.update_of_ne (show forward + x ≠ forward + e by omega)]
        exact hdone x (by omega)
    · intro a ha
      simp only [sb, sa]
      rw [Function.update_of_ne (show a ≠ forward + e by omega)]
      exact hfr a (by omega)
  have hextW : extCap < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = st) (Inv := Inv)
    (r := 12) (lo := .const 0) (hi := .reg 3) 30 0 extCap (Nat.zero_le _) hw1 (fun _ => hextW)
    (by
      intro s hs; subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r hr12 _ => by simp [Function.update_of_ne hr12], fun x hx => by omega,
        fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.1 3 (by decide) (by decide)).trans hr3])
    hstep
  obtain ⟨o, out, cost, hr, hInv, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv
  | normal =>
    obtain ⟨_, _, hregs, hdone, hfr⟩ := hInv
    refine ⟨out, cost, hr, ?_, hregs, hdone, hfr⟩
    simp [Expr.size] at hc
    omega

/-! ### Pass 3 -/

private theorem renameInverseLoop_runs {w inverse intCap cap heap : ℕ} {E : Finset ℕ}
    {i2e : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hr1 : st.regs 1 = cap) (hr4 : st.regs 4 = inverse) (hr6 : st.regs 6 = heap)
    (hr11 : st.regs 11 = E.card)
    (hinv : ∀ j < intCap, st.mem (inverse + j) = i2e j)
    (hunr : ∀ j < E.card, st.mem (heap + cap + j) = compactUnrank E j)
    (hE : ∀ x ∈ E, x < cap) (hcapI : cap ≤ intCap) (hiH : inverse + intCap ≤ heap)
    (hW : heap + 2 * cap < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω renameInverseLoop st .normal out cost ∧
      cost ≤ 30 * E.card + 20 ∧
      (∀ r, r ≠ 14 → out.regs r = st.regs r) ∧
      (∀ j < intCap, out.mem (inverse + j) = i2e (compactUnrank E j)) ∧
      (∀ a, a < inverse ∨ inverse + E.card ≤ a → out.mem a = st.mem a) := by
  have hcard : E.card ≤ cap := by
    have := compactRank_le_self E cap
    rwa [compactRank_of_ge hE le_rfl] at this
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ E.card ∧ s.regs 14 = j ∧
    (∀ r, r ≠ 14 → s.regs r = st.regs r) ∧
    (∀ x < j, s.mem (inverse + x) = i2e (compactUnrank E x)) ∧
    (∀ a, a < inverse ∨ inverse + j ≤ a → s.mem a = st.mem a)
  have hstep : ∀ j, 0 ≤ j → j < E.card →
      Triple w p (Inv j)
        (.store (.bin .add (.reg 4) (.reg 14))
          (.load (.bin .add (.reg 4) (.load (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 14))))))
        (normalPost fun s' => Inv (j + 1) { s' with regs := Function.update s'.regs 14 (j + 1) } ∧
          s'.regs 14 = j) (fun _ => 20) := by
    intro j _ hj s bits' ⟨_, hjr, hregs, hdone, hfr⟩
    have h1 : s.regs 1 = cap := (hregs 1 (by decide)).trans hr1
    have h4 : s.regs 4 = inverse := (hregs 4 (by decide)).trans hr4
    have h6 : s.regs 6 = heap := (hregs 6 (by decide)).trans hr6
    let u := compactUnrank E j
    have hu : u < cap := hE u (compactUnrank_mem hj)
    have hju : j ≤ u := le_compactUnrank E j
    have hsu : s.mem (heap + cap + j) = u :=
      (hfr _ (Or.inr (by omega))).trans (hunr j hj)
    have hiu : s.mem (inverse + u) = i2e u := by
      rw [hfr _ (Or.inr (by omega))]
      exact hinv u (by omega)
    let sa : State := { s with mem := Function.update s.mem (inverse + j) (i2e u) }
    have ra : Runs w p bits'
        (.store (.bin .add (.reg 4) (.reg 14))
          (.load (.bin .add (.reg 4) (.load (.bin .add (.bin .add (.reg 6) (.reg 1)) (.reg 14))))))
        s .normal sa 13 :=
      runs_store_iff.mpr ⟨inverse + j, i2e u,
        by simp [Expr.eval, BinOp.eval, h4, hjr, show inverse + j < 2 ^ w by omega],
        by simp [Expr.eval, BinOp.eval, h4, h6, h1, hjr, show heap + cap < 2 ^ w by omega,
          show heap + cap + j < 2 ^ w by omega, hsu, show inverse + u < 2 ^ w by omega, hiu],
        rfl, rfl, by simp [Expr.size]⟩
    refine ⟨.normal, sa, 13, ra, ⟨⟨by omega, by simp, ?_, ?_, ?_⟩, by simp [sa, hjr]⟩,
      by dsimp only; omega⟩
    · intro r hr14
      simp [sa, Function.update_of_ne hr14, hregs r hr14]
    · intro x hx
      simp only [sa]
      by_cases hxj : x = j
      · subst hxj; simp [u]
      · rw [Function.update_of_ne (show inverse + x ≠ inverse + j by omega)]
        exact hdone x (by omega)
    · intro a ha
      simp only [sa]
      rw [Function.update_of_ne (show a ≠ inverse + j by omega)]
      exact hfr a (by omega)
  have hcW : E.card < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = st) (Inv := Inv)
    (r := 14) (lo := .const 0) (hi := .reg 11) 20 0 E.card (Nat.zero_le _) hw1 (fun _ => hcW)
    (by
      intro s hs; subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r hr14 => by simp [Function.update_of_ne hr14], fun x hx => by omega,
        fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.1 11 (by decide)).trans hr11])
    hstep
  obtain ⟨o, out, cost, hr, hInv, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv
  | normal =>
    obtain ⟨_, _, hregs, hdone, hfr⟩ := hInv
    refine ⟨out, cost, hr, ?_, hregs, ?_, hfr⟩
    · simp [Expr.size] at hc
      omega
    · intro j hj
      by_cases hjc : j < E.card
      · exact hdone j hjc
      · rw [compactUnrank_of_ge hjc, hfr _ (Or.inr (by omega))]
        exact hinv j hj

/-! ### The whole procedure -/

/-- **The renaming at a rebuild of level `0`.** Started on
`[bits, cap, forward, extCap, inverse, counter, heap]`, where `bits + j` holds the presence bit
of `j ∈ G.E` for `j < cap` and the cells at `forward`, `inverse` and `counter` hold the name
tables of `e2i`, `i2e` and `nf`, `level0RenameBody` returns `|E(G)|` and leaves the tables of
`level0E2I true G e2i`, `level0I2E true G i2e` and `level0NF true G nf`: the tables of the
ordered model after a rebuild of level `0` from `G` (`Chain.Ordered.algorithm2_updateWith`).
It writes only the three tables and the scratch block `[heap, heap + 2 * cap)`, and it costs
`O(cap + extCap)`. -/
theorem level0RenameBody_runs {w bits cap forward extCap inverse intCap counter heap nf pos : ℕ}
    {G : MGraph} {e2i i2e : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hbits : ∀ j < cap, mem (bits + j) = if j ∈ G.E then 1 else 0)
    (hE : ∀ x ∈ G.E, x < cap) (hcapI : cap ≤ intCap)
    (htab : FreshTablesAt mem forward inverse counter extCap intCap e2i i2e nf)
    (hbitsH : bits + cap ≤ heap) (hfH : forward + extCap ≤ heap) (hiH : inverse + intCap ≤ heap)
    (hcH : counter < heap)
    (hfi : forward + extCap ≤ inverse ∨ inverse + intCap ≤ forward)
    (hcf : counter < forward ∨ forward + extCap ≤ counter)
    (hci : counter < inverse ∨ inverse + intCap ≤ counter)
    (hW : heap + 2 * cap < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω level0RenameBody
        (startState [bits, cap, forward, extCap, inverse, counter, heap] mem pos)
        (.returned G.m) out cost ∧
      cost ≤ 70 * cap + 40 * extCap + 80 ∧
      FreshTablesAt out.mem forward inverse counter extCap intCap
        (level0E2I true G e2i) (level0I2E true G i2e) (level0NF true G nf) ∧
      (∀ a < heap, ¬ (forward ≤ a ∧ a < forward + extCap) →
        ¬ (inverse ≤ a ∧ a < inverse + intCap) → a ≠ counter → out.mem a = mem a) ∧
      (∀ a, heap + 2 * cap ≤ a → out.mem a = mem a) := by
  obtain ⟨hcnt, hfwd, hinv⟩ := htab
  let s0 := startState [bits, cap, forward, extCap, inverse, counter, heap] mem pos
  have hcard : G.E.card ≤ cap := by
    have := compactRank_le_self G.E cap
    rwa [compactRank_of_ge hE le_rfl] at this
  obtain ⟨s1, c1, r1, hc1, h11, hregs1, hrank, hunr, hfr1⟩ :=
    renameRankLoop_runs (w := w) (bits := bits) (cap := cap) (heap := heap) (E := G.E) (p := p)
      (ω := ω) (st := s0) (by simp [s0, startState]) (by simp [s0, startState])
      (by simp [s0, startState]) (fun j hj => by simpa [s0, startState] using hbits j hj) hE hbitsH
      hW hw1
  have g1 (r : ℕ) (h10 : r ≠ 10) (h11 : r ≠ 11) : s1.regs r = s0.regs r := hregs1 r h10 h11
  obtain ⟨s2, c2, r2, hc2, hregs2, hfwd2, hfr2⟩ :=
    renameForwardLoop_runs (w := w) (forward := forward) (extCap := extCap) (cap := cap)
      (heap := heap) (E := G.E) (e2i := e2i) (p := p) (ω := ω) (st := s1)
      (by rw [g1 1 (by decide) (by decide)]; simp [s0, startState])
      (by rw [g1 2 (by decide) (by decide)]; simp [s0, startState])
      (by rw [g1 3 (by decide) (by decide)]; simp [s0, startState])
      (by rw [g1 6 (by decide) (by decide)]; simp [s0, startState]) h11
      (fun e he => by rw [hfr1 _ (Or.inl (by omega))]; exact hfwd e he)
      hrank hE hfH (by omega) hw1
  have g2 (r : ℕ) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) :
      s2.regs r = s0.regs r := (hregs2 r h12 h13).trans (g1 r h10 h11)
  obtain ⟨s3, c3, r3, hc3, hregs3, hinv3, hfr3⟩ :=
    renameInverseLoop_runs (w := w) (inverse := inverse) (intCap := intCap) (cap := cap)
      (heap := heap) (E := G.E) (i2e := i2e) (p := p) (ω := ω) (st := s2)
      (by rw [g2 1 (by decide) (by decide) (by decide) (by decide)]; simp [s0, startState])
      (by rw [g2 4 (by decide) (by decide) (by decide) (by decide)]; simp [s0, startState])
      (by rw [g2 6 (by decide) (by decide) (by decide) (by decide)]; simp [s0, startState])
      (by rw [hregs2 11 (by decide) (by decide)]; exact h11)
      (fun j hj => by
        rw [hfr2 _ (by omega), hfr1 _ (Or.inl (by omega))]
        exact hinv j hj)
      (fun j hj => by rw [hfr2 _ (by omega)]; exact hunr j hj)
      hE hcapI hiH hW hw1
  have h5 : s3.regs 5 = counter := by
    rw [hregs3 5 (by decide), g2 5 (by decide) (by decide) (by decide) (by decide)]
    simp [s0, startState]
  have h11' : s3.regs 11 = G.E.card := by
    rw [hregs3 11 (by decide), hregs2 11 (by decide) (by decide)]
    exact h11
  let s4 : State := { s3 with mem := Function.update s3.mem counter G.E.card }
  have r4 : Runs w p ω (.store (.reg 5) (.reg 11)) s3 .normal s4 3 :=
    runs_store_iff.mpr ⟨counter, G.E.card, by simp [Expr.eval, h5], by simp [Expr.eval, h11'],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.ret (.reg 11)) s4 (.returned G.m) s4 2 :=
    runs_ret_iff.mpr ⟨G.E.card, by simp [Expr.eval, s4, h11'], rfl, rfl, rfl⟩
  refine ⟨s4, c1 + (c2 + (c3 + (3 + 2 + 1) + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, c3, _, r3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 3, 2, r4, r5, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, ⟨by simp [s4, level0NF, MGraph.m], ?_, ?_⟩, ?_, ?_⟩
  · intro e he
    simp only [s4, level0E2I, ite_true]
    rw [Function.update_of_ne (show forward + e ≠ counter by omega), hfr3 _ (by omega)]
    exact hfwd2 e he
  · intro j hj
    simp only [s4, level0I2E, ite_true]
    rw [Function.update_of_ne (show inverse + j ≠ counter by omega)]
    exact hinv3 j hj
  · intro a ha hnf hni hnc
    simp only [s4]
    rw [Function.update_of_ne hnc, hfr3 _ (by omega), hfr2 _ (by omega), hfr1 _ (Or.inl ha)]
    rfl
  · intro a ha
    simp only [s4]
    rw [Function.update_of_ne (show a ≠ counter by omega), hfr3 _ (by omega), hfr2 _ (by omega),
      hfr1 _ (Or.inr ha)]
    rfl

/-- Companion to `level0RenameBody_runs` that additionally exposes the sorted live-name table
`out.mem (heap + cap + j) = compactUnrank G.E j` for every `j < G.m` written during Pass 1 and
preserved by Passes 2 and 3. -/
theorem level0RenameBody_runs_with_unrank
    {w bits cap forward extCap inverse intCap counter heap nf pos : ℕ}
    {G : MGraph} {e2i i2e : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hbits : ∀ j < cap, mem (bits + j) = if j ∈ G.E then 1 else 0)
    (hE : ∀ x ∈ G.E, x < cap) (hcapI : cap ≤ intCap)
    (htab : FreshTablesAt mem forward inverse counter extCap intCap e2i i2e nf)
    (hbitsH : bits + cap ≤ heap) (hfH : forward + extCap ≤ heap) (hiH : inverse + intCap ≤ heap)
    (hcH : counter < heap)
    (hfi : forward + extCap ≤ inverse ∨ inverse + intCap ≤ forward)
    (hcf : counter < forward ∨ forward + extCap ≤ counter)
    (hci : counter < inverse ∨ inverse + intCap ≤ counter)
    (hW : heap + 2 * cap < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω level0RenameBody
        (startState [bits, cap, forward, extCap, inverse, counter, heap] mem pos)
        (.returned G.m) out cost ∧
      cost ≤ 70 * cap + 40 * extCap + 80 ∧
      FreshTablesAt out.mem forward inverse counter extCap intCap
        (level0E2I true G e2i) (level0I2E true G i2e) (level0NF true G nf) ∧
      (∀ j < G.m, out.mem (heap + cap + j) = compactUnrank G.E j) ∧
      (∀ a < heap, ¬ (forward ≤ a ∧ a < forward + extCap) →
        ¬ (inverse ≤ a ∧ a < inverse + intCap) → a ≠ counter → out.mem a = mem a) ∧
      (∀ a, heap + 2 * cap ≤ a → out.mem a = mem a) := by
  obtain ⟨hcnt, hfwd, hinv⟩ := htab
  let s0 := startState [bits, cap, forward, extCap, inverse, counter, heap] mem pos
  have hcard : G.E.card ≤ cap := by
    have := compactRank_le_self G.E cap
    rwa [compactRank_of_ge hE le_rfl] at this
  obtain ⟨s1, c1, r1, hc1, h11, hregs1, hrank, hunr, hfr1⟩ :=
    renameRankLoop_runs (w := w) (bits := bits) (cap := cap) (heap := heap) (E := G.E) (p := p)
      (ω := ω) (st := s0) (by simp [s0, startState]) (by simp [s0, startState])
      (by simp [s0, startState]) (fun j hj => by simpa [s0, startState] using hbits j hj) hE hbitsH
      hW hw1
  have g1 (r : ℕ) (h10 : r ≠ 10) (h11 : r ≠ 11) : s1.regs r = s0.regs r := hregs1 r h10 h11
  obtain ⟨s2, c2, r2, hc2, hregs2, hfwd2, hfr2⟩ :=
    renameForwardLoop_runs (w := w) (forward := forward) (extCap := extCap) (cap := cap)
      (heap := heap) (E := G.E) (e2i := e2i) (p := p) (ω := ω) (st := s1)
      (by rw [g1 1 (by decide) (by decide)]; simp [s0, startState])
      (by rw [g1 2 (by decide) (by decide)]; simp [s0, startState])
      (by rw [g1 3 (by decide) (by decide)]; simp [s0, startState])
      (by rw [g1 6 (by decide) (by decide)]; simp [s0, startState]) h11
      (fun e he => by rw [hfr1 _ (Or.inl (by omega))]; exact hfwd e he)
      hrank hE hfH (by omega) hw1
  have g2 (r : ℕ) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) :
      s2.regs r = s0.regs r := (hregs2 r h12 h13).trans (g1 r h10 h11)
  obtain ⟨s3, c3, r3, hc3, hregs3, hinv3, hfr3⟩ :=
    renameInverseLoop_runs (w := w) (inverse := inverse) (intCap := intCap) (cap := cap)
      (heap := heap) (E := G.E) (i2e := i2e) (p := p) (ω := ω) (st := s2)
      (by rw [g2 1 (by decide) (by decide) (by decide) (by decide)]; simp [s0, startState])
      (by rw [g2 4 (by decide) (by decide) (by decide) (by decide)]; simp [s0, startState])
      (by rw [g2 6 (by decide) (by decide) (by decide) (by decide)]; simp [s0, startState])
      (by rw [hregs2 11 (by decide) (by decide)]; exact h11)
      (fun j hj => by
        rw [hfr2 _ (by omega), hfr1 _ (Or.inl (by omega))]
        exact hinv j hj)
      (fun j hj => by rw [hfr2 _ (by omega)]; exact hunr j hj)
      hE hcapI hiH hW hw1
  have h5 : s3.regs 5 = counter := by
    rw [hregs3 5 (by decide), g2 5 (by decide) (by decide) (by decide) (by decide)]
    simp [s0, startState]
  have h11' : s3.regs 11 = G.E.card := by
    rw [hregs3 11 (by decide), hregs2 11 (by decide) (by decide)]
    exact h11
  let s4 : State := { s3 with mem := Function.update s3.mem counter G.E.card }
  have r4 : Runs w p ω (.store (.reg 5) (.reg 11)) s3 .normal s4 3 :=
    runs_store_iff.mpr ⟨counter, G.E.card, by simp [Expr.eval, h5], by simp [Expr.eval, h11'],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.ret (.reg 11)) s4 (.returned G.m) s4 2 :=
    runs_ret_iff.mpr ⟨G.E.card, by simp [Expr.eval, s4, h11'], rfl, rfl, rfl⟩
  refine ⟨s4, c1 + (c2 + (c3 + (3 + 2 + 1) + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, c3, _, r3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 3, 2, r4, r5, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, ⟨by simp [s4, level0NF, MGraph.m], ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e he
    simp only [s4, level0E2I, ite_true]
    rw [Function.update_of_ne (show forward + e ≠ counter by omega), hfr3 _ (by omega)]
    exact hfwd2 e he
  · intro j hj
    simp only [s4, level0I2E, ite_true]
    rw [Function.update_of_ne (show inverse + j ≠ counter by omega)]
    exact hinv3 j hj
  · intro j hj
    simp only [s4]
    rw [Function.update_of_ne (show heap + cap + j ≠ counter by omega), hfr3 _ (by omega),
      hfr2 _ (by omega)]
    exact hunr j hj
  · intro a ha hnf hni hnc
    simp only [s4]
    rw [Function.update_of_ne hnc, hfr3 _ (by omega), hfr2 _ (by omega), hfr1 _ (Or.inl ha)]
    rfl
  · intro a ha
    simp only [s4]
    rw [Function.update_of_ne (show a ≠ counter by omega), hfr3 _ (by omega), hfr2 _ (by omega),
      hfr1 _ (Or.inr ha)]
    rfl

end MinCostFlow.MinRatio

end
