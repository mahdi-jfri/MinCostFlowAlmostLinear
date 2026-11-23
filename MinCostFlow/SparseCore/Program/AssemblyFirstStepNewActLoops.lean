module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstOutEdges

import WordRAM.Tactic

/-!
# Verification of single newly active component initializer (`AssemblyFirstStepNewActOne`)

Verifies `asmFirstInitOneCompStmt fVertRoot fTourList bSort fInitSlots`
(`AssemblyFirstStepNewActProg.lean`) on `[restH, tourH, c, v, lazySlotPtr, h]`:

* Uses `AsmFirstTourRootAt`, `AsmFirstTourBundleProj`, `sortProcs` (`mergeSort`, `dedup`,
  `binSearch`), and `bunTableHeadroom_initSlots_runs` (called ONCE per component with
  `rList = [r_c]`), together with `tableAfterInitSlots_bunAgree`.
* Produces the updated bundle table `S'`, updated `ctH`/`cslPtr`/`cslL`, updated `slotsPtr`/
  `ASM_SD_NSLOTS`, `lazySlotPtr` pointing to the sorted core edge list `uniqE[0..m_C)` of `C`,
  `BunAgree` with `tr.bun (C, b)` for every newly initialized bucket `b ∈ tr.activeBuckets C`,
  `bunRestartInv`, frame, footprint growth, `ZeroFrom`, linear space bound `newActOneSpace`, and
  cost bound `newActOneCost`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

/-! ## 1. Pure list / counting helpers -/

theorem list_filter_count_eq_card_slotEdgesOf {uniqE uniqB : List ℕ} {origB : ℕ → ℤ}
    {nSlots bi : ℕ} (hndE : uniqE.Nodup) :
    let assigns : List (ℕ × ℕ) := uniqE.map fun e => (e, nSlots + uniqB.idxOf (bucketCode (origB e)))
    (uniqE.filter fun e => decide (uniqB.idxOf (bucketCode (origB e)) = bi)).length =
      (slotEdgesOf assigns (nSlots + bi)).card := by
  intro assigns
  have hndF : (uniqE.filter fun e => decide (uniqB.idxOf (bucketCode (origB e)) = bi)).Nodup :=
    hndE.filter _
  rw [← List.toFinset_card_of_nodup hndF]
  congr 1
  ext e
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, slotEdgesOf, assigns,
    List.mem_map, beq_iff_eq]
  constructor
  · rintro ⟨he, hidx⟩
    exact ⟨(e, nSlots + bi), ⟨⟨e, he, by rw [hidx]⟩, rfl⟩, rfl⟩
  · rintro ⟨⟨e', s'⟩, ⟨⟨e0, he0, hp⟩, hs⟩, heq⟩
    simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩; subst heq
    dsimp only at hs ⊢
    exact ⟨he0, by omega⟩

theorem slotEdgesOf_eq_bucketCoreEdges {G_core : MGraph} {origB : ℕ → ℤ} {C : Finset ℕ}
    {uniqE uniqB : List ℕ} {nSlots bi : ℕ}
    (hEeq : ∀ e, e ∈ uniqE ↔ e ∈ G_core.E ∧ G_core.tail e ∈ C)
    (hBpw : uniqB.Pairwise (· < ·)) (hbi : bi < uniqB.length) :
    let assigns : List (ℕ × ℕ) := uniqE.map fun e => (e, nSlots + uniqB.idxOf (bucketCode (origB e)))
    slotEdgesOf assigns (nSlots + bi) = bucketCoreEdges G_core origB C (bucketCodeInv (uniqB[bi]'hbi)) := by
  intro assigns
  have hndB : uniqB.Nodup := hBpw.imp fun h => Nat.ne_of_lt h
  ext e
  simp only [slotEdgesOf, assigns, List.mem_toFinset, List.mem_filter, List.mem_map,
    beq_iff_eq, bucketCoreEdges, Finset.mem_filter]
  constructor
  · rintro ⟨⟨e', s'⟩, ⟨⟨e0, he0, hp⟩, hs⟩, heq⟩
    simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩; subst heq
    dsimp only at hs ⊢
    have hidx : uniqB.idxOf (bucketCode (origB e0)) = bi := by omega
    have hget : uniqB[bi]'hbi = bucketCode (origB e0) := by
      have := List.getElem_idxOf (xs := uniqB) (x := bucketCode (origB e0))
        (by rw [hidx]; exact hbi)
      simpa [hidx] using this
    have hb_eq : origB e0 = bucketCodeInv (uniqB[bi]'hbi) := by
      rw [hget, bucketCodeInv_left]
    exact ⟨((hEeq e0).mp he0).1, ((hEeq e0).mp he0).2, hb_eq⟩
  · rintro ⟨heG, htC, hb⟩
    have heU : e ∈ uniqE := (hEeq e).mpr ⟨heG, htC⟩
    have hbc : bucketCode (origB e) = uniqB[bi]'hbi := by rw [hb, bucketCodeInv_right]
    have hidx : uniqB.idxOf (bucketCode (origB e)) = bi := by
      rw [hbc]
      exact (List.Nodup.getElem_inj_iff hndB).mp (List.getElem_idxOf (by
        exact List.idxOf_lt_length_of_mem (List.getElem_mem hbi)))
    exact ⟨(e, nSlots + bi), ⟨⟨e, heU, by rw [hidx]⟩, rfl⟩, rfl⟩

theorem sum_filter_idxOf_eq_length {α : Type*} (L : List α) (f : α → ℕ) (r : ℕ)
    (hf : ∀ x ∈ L, f x < r) :
    ((List.range r).map fun bi => (L.filter fun x => decide (f x = bi)).length).sum = L.length := by
  induction L with
  | nil => simp
  | cons a xs ih =>
    have hfa : f a < r := hf a List.mem_cons_self
    have ih' := ih fun x hx => hf x (List.mem_cons_of_mem a hx)
    have hsplit : ((List.range r).map fun bi =>
        ((a :: xs).filter fun x => decide (f x = bi)).length).sum =
        ((List.range r).map fun bi =>
          (if f a = bi then 1 else 0) + (xs.filter fun x => decide (f x = bi)).length).sum := by
      congr 1; apply List.map_congr_left; intro bi _
      simp only [List.filter_cons]; split_ifs <;> simp_all; omega
    rw [hsplit]
    have hadd : ∀ (l : List ℕ) (g₁ g₂ : ℕ → ℕ),
        (l.map fun x => g₁ x + g₂ x).sum = (l.map g₁).sum + (l.map g₂).sum := by
      intro l g₁ g₂; induction l with | nil => simp | cons y ys ihl => simp [ihl]; omega
    rw [hadd, ih']
    have hind : ∀ (n k : ℕ), k < n → ((List.range n).map fun bi => if k = bi then 1 else 0).sum = 1 := by
      intro n
      induction n with
      | zero => intro k hk; omega
      | succ m ihm =>
        intro k hk
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        by_cases hkm : k = m
        · subst hkm
          have hz : ((List.range k).map fun bi => if k = bi then 1 else 0).sum = 0 :=
            List.sum_eq_zero fun x hx => by
              rcases List.mem_map.mp hx with ⟨bi, hbi, rfl⟩
              have := List.mem_range.mp hbi; simp [show k ≠ bi by omega]
          simp [hz]
        · rw [ihm k (by omega)]; simp [hkm]
    rw [hind r (f a) hfa]; simp [Nat.add_comm]

theorem slotBlocksSpace_specs_eq {nSlots r m_C : ℕ} {cntFn : ℕ → ℕ}
    (hsum : ((List.range r).map cntFn).sum = m_C) :
    slotBlocksSpace ((List.range r).map fun bi => (nSlots + bi, 4 * cntFn bi)) =
      3 * r + 24 * m_C := by
  unfold slotBlocksSpace
  rw [List.map_map]
  have h1 : ∀ (l : List ℕ), (l.map fun bi => bundleSlotBlockSize (4 * cntFn bi)).sum =
      3 * l.length + 24 * (l.map cntFn).sum := by
    intro l; induction l with
    | nil => simp
    | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, List.map_cons, List.sum_cons, ih]
      unfold bundleSlotBlockSize; omega
  simpa only [Function.comp_def, List.length_range, hsum] using h1 (List.range r)

theorem sortedDedup_length_le_local : ∀ (L : List ℕ), (sortedDedup L).length ≤ L.length := by
  have haux : ∀ (prev : ℕ) (xs : List ℕ), (sortedDedupAux prev xs).length ≤ xs.length := by
    intro prev xs; induction xs generalizing prev with
    | nil => simp [sortedDedupAux]
    | cons x xs ih =>
      unfold sortedDedupAux; split_ifs
      · exact le_trans (ih prev) (Nat.le_succ _)
      · simp only [List.length_cons]; exact Nat.succ_le_succ (ih x)
  intro L; cases L with
  | nil => simp [sortedDedup]
  | cons x xs => simp only [sortedDedup, List.length_cons]; exact Nat.succ_le_succ (haux x xs)

/-! ## 2. Four inner `forRange` loop verifications -/

/-- Loop 1: extracts `rawE[j] = endKey (cord r_c)[j] / 2 = ((cord r_c)[j]).1` for `j < len`. -/
theorem newAct_loop1_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {h1 rawE : ℕ} {xs : List End} {st0 : State}
    (hw16 : 16 ≤ 2 ^ w) (hr6 : st0.regs 6 = h1) (hr9 : st0.regs 9 = xs.length)
    (hr11 : st0.regs 11 = rawE)
    (hEnd : EndListAt st0.mem h1 xs) (hEndW : ∀ x ∈ xs, endKey x < 2 ^ w)
    (hdisj : h1 + 1 + xs.length ≤ rawE) (hfit : rawE + xs.length < 2 ^ w) :
    ∃ st1 c1,
      Runs w p ω (forRange 14 (.const 0) (.reg 9)
        (.store (.bin .add (.reg 11) (.reg 14))
          (.bin .div (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 14))) (.const 2))))
        st0 .normal st1 c1 ∧
      (∀ r, r ≠ 14 → st1.regs r = st0.regs r) ∧
      ListAt st1.mem rawE (xs.map Prod.fst) ∧
      (∀ a, a < rawE ∨ rawE + xs.length ≤ a → st1.mem a = st0.mem a) ∧
      c1 ≤ 30 * xs.length + 20 := by
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  let inv : ℕ → State → Prop := fun j st =>
    (∀ r, r ≠ 14 → st.regs r = st0.regs r) ∧ st.regs 14 = j ∧
    (∀ i < j, ∀ hi : i < xs.length, st.mem (rawE + i) = (xs[i]'hi).1) ∧
    (∀ a, a < rawE ∨ rawE + j ≤ a → st.mem a = st0.mem a)
  have htr : Triple w p (fun st => st = st0)
      (forRange 14 (.const 0) (.reg 9)
        (.store (.bin .add (.reg 11) (.reg 14))
          (.bin .div (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 14))) (.const 2))))
      (normalPost (inv xs.length))
      (fun _ => rangeCost (fun _ => 20) 0 xs.length +
        (xs.length - 0) * ((Expr.reg 9).size + 8) + ((Expr.const 0).size + (Expr.reg 9).size + 5)) := by
    refine Triple.forRange_le (fun _ => 20) 0 xs.length (Nat.zero_le _) h1w (fun _ => by omega)
      ?_ (fun _ _ _ _ h => h.2.1)
      (fun _ _ _ _ h => Expr.eval_reg_of_eq ((h.1 9 (by decide)).trans hr9)) ?_
    · rintro st rfl
      exact ⟨Expr.eval_const (by omega), fun r hr => Function.update_of_ne hr _ _,
        by simp, fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩
    · intro j _ hj st ω' ⟨hregs, hr14, hdat, hfr⟩
      have hkey : st.mem (h1 + 1 + j) = endKey (xs.getD j (0, true)) := by
        rw [hfr _ (Or.inl (by omega))]; exact hEnd.2 j hj
      rw [List.getD_eq_getElem xs (0, true) hj] at hkey
      have haddr : (Expr.bin .add (.reg 11) (.reg 14)).eval w st = some (rawE + j) :=
        Expr.eval_add (Expr.eval_reg_of_eq ((hregs 11 (by decide)).trans hr11))
          (Expr.eval_reg_of_eq hr14) (by omega)
      have hval : (Expr.bin .div (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 14)))
          (.const 2)).eval w st = some (xs[j]'hj).1 :=
        Expr.eval_eq_of_eq
          (Expr.eval_div
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_add (Expr.eval_reg_of_eq ((hregs 6 (by decide)).trans hr6))
                  (Expr.eval_const h1w) (by omega))
                (Expr.eval_reg_of_eq hr14) (by omega)) hkey)
            (Expr.eval_const h2w) (by have := hEndW _ (List.getElem_mem hj); omega))
          (endKey_div_two (xs[j]'hj))
      refine ⟨.normal, { st with mem := Function.update st.mem (rawE + j) (xs[j]'hj).1 }, _,
        runs_store_iff.mpr ⟨_, _, haddr, hval, rfl, rfl, rfl⟩,
        ⟨⟨fun r hr => by simp [Function.update_of_ne hr, hregs r hr], by simp, ?_, ?_⟩, hr14⟩,
        by simp [Expr.size]⟩
      · intro i hi hix
        by_cases hij : i = j
        · subst hij; simp
        · change Function.update st.mem (rawE + j) (xs[j]'hj).1 (rawE + i) = _
          rw [Function.update_of_ne (by omega)]; exact hdat i (by omega) hix
      · intro a ha
        change Function.update st.mem (rawE + j) (xs[j]'hj).1 a = _
        rw [Function.update_of_ne (by omega)]; exact hfr a (by omega)
  obtain ⟨o, st1, c1, hrun, hpost, hc⟩ := htr st0 ω rfl
  cases o with
  | returned _ => exact absurd hpost (by simp)
  | normal =>
    obtain ⟨hregs, _, hdat, hfr⟩ := hpost
    have hrc : rangeCost (fun _ => 20) 0 xs.length = 20 * xs.length := by
      simp [rangeCost, Nat.mul_comm]
    refine ⟨st1, c1, hrun, hregs, ?_, hfr, by rw [hrc] at hc; simp [Expr.size] at hc; omega⟩
    intro i hi
    have hi' : i < xs.length := by simpa using hi
    simpa [List.getElem_map] using hdat i hi' hi'

/-- Loop 2: extracts `rawB[j] = mem[bktH + uniqE[j]] = bucketCode (origB uniqE[j])` for `j < m_C`. -/
theorem newAct_loop2_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {uniqE_ptr bktH rawB : ℕ} {uniqE : List ℕ} {origB : ℕ → ℤ} {st0 : State}
    (hw16 : 16 ≤ 2 ^ w) (hr13 : st0.regs 13 = uniqE_ptr) (hr15 : st0.regs 15 = uniqE.length)
    (hr16 : st0.regs 16 = bktH) (hr17 : st0.regs 17 = rawB)
    (hEAt : ListAt st0.mem uniqE_ptr uniqE)
    (hBkt : ∀ e ∈ uniqE, bktH + e < 2 ^ w ∧ st0.mem (bktH + e) = bucketCode (origB e))
    (hdisjE : uniqE_ptr + uniqE.length ≤ rawB)
    (hdisjB : ∀ e ∈ uniqE, bktH + e < rawB ∨ rawB + uniqE.length ≤ bktH + e)
    (hfit : rawB + uniqE.length < 2 ^ w) :
    ∃ st1 c1,
      Runs w p ω (forRange 14 (.const 0) (.reg 15)
        (.assign 25 (.load (.bin .add (.reg 13) (.reg 14))) ;;
         .store (.bin .add (.reg 17) (.reg 14)) (.load (.bin .add (.reg 16) (.reg 25)))))
        st0 .normal st1 c1 ∧
      (∀ r, r ≠ 14 → r ≠ 25 → st1.regs r = st0.regs r) ∧
      ListAt st1.mem rawB (uniqE.map fun e => bucketCode (origB e)) ∧
      (∀ a, a < rawB ∨ rawB + uniqE.length ≤ a → st1.mem a = st0.mem a) ∧
      c1 ≤ 30 * uniqE.length + 20 := by
  have h1w : 1 < 2 ^ w := by omega
  let inv : ℕ → State → Prop := fun j st =>
    (∀ r, r ≠ 14 → r ≠ 25 → st.regs r = st0.regs r) ∧ st.regs 14 = j ∧
    (∀ i < j, ∀ hi : i < uniqE.length, st.mem (rawB + i) = bucketCode (origB (uniqE[i]'hi))) ∧
    (∀ a, a < rawB ∨ rawB + j ≤ a → st.mem a = st0.mem a)
  have htr : Triple w p (fun st => st = st0)
      (forRange 14 (.const 0) (.reg 15)
        (.assign 25 (.load (.bin .add (.reg 13) (.reg 14))) ;;
         .store (.bin .add (.reg 17) (.reg 14)) (.load (.bin .add (.reg 16) (.reg 25)))))
      (normalPost (inv uniqE.length))
      (fun _ => rangeCost (fun _ => 20) 0 uniqE.length +
        (uniqE.length - 0) * ((Expr.reg 15).size + 8) + ((Expr.const 0).size + (Expr.reg 15).size + 5)) := by
    refine Triple.forRange_le (fun _ => 20) 0 uniqE.length (Nat.zero_le _) h1w (fun _ => by omega)
      ?_ (fun _ _ _ _ h => h.2.1)
      (fun _ _ _ _ h => Expr.eval_reg_of_eq ((h.1 15 (by decide) (by decide)).trans hr15)) ?_
    · rintro st rfl
      exact ⟨Expr.eval_const (by omega), fun r h1 _ => Function.update_of_ne h1 _ _,
        by simp, fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩
    · intro j _ hj st ω' ⟨hregs, hr14, hdat, hfr⟩
      set e := uniqE[j]'hj
      have he_mem : st.mem (uniqE_ptr + j) = e := by
        rw [hfr _ (Or.inl (by omega))]; exact hEAt j hj
      have hb_ok := hBkt e (List.getElem_mem hj)
      have hb_mem : st.mem (bktH + e) = bucketCode (origB e) := by
        rw [hfr _ (by rcases hdisjB e (List.getElem_mem hj) with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])]
        exact hb_ok.2
      have ha25 : (Expr.load (.bin .add (.reg 13) (.reg 14))).eval w st = some e :=
        Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hregs 13 (by decide) (by decide)).trans hr13))
          (Expr.eval_reg_of_eq hr14) (by omega)) he_mem
      set stA : State := { st with regs := Function.update st.regs 25 e }
      have hst_addr : (Expr.bin .add (.reg 17) (.reg 14)).eval w stA = some (rawB + j) :=
        Expr.eval_add
          (Expr.eval_reg_of_eq (v := rawB) (by simp [stA, hregs 17 (by decide) (by decide), hr17]))
          (Expr.eval_reg_of_eq (v := j) (by simp [stA, hr14])) (by omega)
      have hst_val : (Expr.load (.bin .add (.reg 16) (.reg 25))).eval w stA =
          some (bucketCode (origB e)) :=
        Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := bktH) (by simp [stA, hregs 16 (by decide) (by decide), hr16]))
            (Expr.eval_reg_of_eq (v := e) (by simp [stA])) hb_ok.1) hb_mem
      refine ⟨.normal, { stA with mem := Function.update st.mem (rawB + j) (bucketCode (origB e)) },
        _, runs_seq_iff.mpr (Or.inr ⟨stA, _, _, runs_assign_iff.mpr ⟨_, ha25, rfl, rfl, rfl⟩,
          runs_store_iff.mpr ⟨_, _, hst_addr, hst_val, rfl, rfl, rfl⟩, rfl⟩),
        ⟨⟨fun r h1 h2 => by simp [stA, Function.update_of_ne h1, Function.update_of_ne h2, hregs r h1 h2],
          by simp, ?_, ?_⟩, by simp [stA, hr14]⟩, by simp [Expr.size]⟩
      · intro i hi hix
        by_cases hij : i = j
        · subst hij; simp [e]
        · change Function.update st.mem (rawB + j) (bucketCode (origB e)) (rawB + i) = _
          rw [Function.update_of_ne (by omega)]; exact hdat i (by omega) hix
      · intro a ha
        change Function.update st.mem (rawB + j) (bucketCode (origB e)) a = _
        rw [Function.update_of_ne (by omega)]; exact hfr a (by omega)
  obtain ⟨o, st1, c1, hrun, hpost, hc⟩ := htr st0 ω rfl
  cases o with
  | returned _ => exact absurd hpost (by simp)
  | normal =>
    obtain ⟨hregs, _, hdat, hfr⟩ := hpost
    have hrc : rangeCost (fun _ => 20) 0 uniqE.length = 20 * uniqE.length := by
      simp [rangeCost, Nat.mul_comm]
    refine ⟨st1, c1, hrun, hregs, ?_, hfr, by rw [hrc] at hc; simp [Expr.size] at hc; omega⟩
    intro i hi
    have hi' : i < uniqE.length := by simpa using hi
    simpa [List.getElem_map] using hdat i hi' hi'

/-- Loop 3: binary-searches each edge's bucket code in `uniqB`, increments `cnt[bi]`, and writes
`assigns[2*j .. 2*j+1] = [e, nSlots + bi]`. -/
theorem newAct_loop3_runs {w bSort : ℕ} {p : Program} {ω : ℕ → Bool}
    (hpSort : p.HasAt bSort (sortProcs bSort))
    {uniqE_ptr bktH uniqB_ptr cnt assigns nSlots : ℕ} {uniqE uniqB : List ℕ} {origB : ℕ → ℤ}
    {st0 : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hr13 : st0.regs 13 = uniqE_ptr) (hr15 : st0.regs 15 = uniqE.length)
    (hr16 : st0.regs 16 = bktH) (hr19 : st0.regs 19 = uniqB_ptr)
    (hr20 : st0.regs 20 = uniqB.length) (hr21 : st0.regs 21 = cnt)
    (hr22 : st0.regs 22 = assigns) (hr23 : st0.regs 23 = nSlots)
    (hEAt : ListAt st0.mem uniqE_ptr uniqE)
    (hBAt : ListAt st0.mem uniqB_ptr uniqB)
    (hBpw : uniqB.Pairwise (· < ·)) (hBw : ∀ x ∈ uniqB, x < 2 ^ w)
    (hBkt : ∀ e ∈ uniqE, bktH + e < 2 ^ w ∧ st0.mem (bktH + e) = bucketCode (origB e) ∧
      bucketCode (origB e) ∈ uniqB)
    (hCnt0 : ∀ bi < uniqB.length, st0.mem (cnt + bi) = 0)
    (hGeom : uniqE_ptr + uniqE.length ≤ cnt ∧ uniqB_ptr + uniqB.length ≤ cnt ∧
      cnt + uniqB.length ≤ assigns ∧
      (∀ e ∈ uniqE, bktH + e < cnt ∨ assigns + 2 * uniqE.length ≤ bktH + e) ∧
      nSlots + uniqB.length < 2 ^ w ∧ assigns + 2 * uniqE.length < 2 ^ w) :
    let assignsL := uniqE.map fun e => (e, nSlots + uniqB.idxOf (bucketCode (origB e)))
    ∃ st1 c1,
      Runs w p ω (forRange 14 (.const 0) (.reg 15)
        (.assign 25 (.load (.bin .add (.reg 13) (.reg 14))) ;;
         .assign 26 (.load (.bin .add (.reg 16) (.reg 25))) ;;
         .call 27 (bSort + sortIdxBinSearch) [.reg 19, .reg 20, .reg 26] ;;
         .assign 28 (.load (.bin .add (.reg 21) (.reg 27))) ;;
         .store (.bin .add (.reg 21) (.reg 27)) (.bin .add (.reg 28) (.const 1)) ;;
         .store (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.reg 25) ;;
         .store (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.const 1))
           (.bin .add (.reg 23) (.reg 27))))
        st0 .normal st1 c1 ∧
      (∀ r, r ≠ 14 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → st1.regs r = st0.regs r) ∧
      (∀ bi < uniqB.length,
        st1.mem (cnt + bi) = (uniqE.filter fun e => decide (uniqB.idxOf (bucketCode (origB e)) = bi)).length) ∧
      bundleReadPairs st1.mem assigns uniqE.length = assignsL ∧
      (∀ a, a < cnt ∨ assigns + 2 * uniqE.length ≤ a → st1.mem a = st0.mem a) ∧
      c1 ≤ uniqE.length * (45 * (Nat.log 2 (uniqB.length + 1) + 1) + 80) + 20 := by
  intro assignsL
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  rcases hGeom with ⟨hEc, hBc, hca, hBktD, hnsW, haW⟩
  let stepC := 45 * (Nat.log 2 (uniqB.length + 1) + 1) + 70
  let inv : ℕ → State → Prop := fun j st =>
    (∀ r, r ≠ 14 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → st.regs r = st0.regs r) ∧
    st.regs 14 = j ∧
    (∀ bi < uniqB.length,
      st.mem (cnt + bi) = ((uniqE.take j).filter fun e => decide (uniqB.idxOf (bucketCode (origB e)) = bi)).length) ∧
    (∀ i < j, ∀ hi : i < uniqE.length,
      st.mem (assigns + 2 * i) = uniqE[i]'hi ∧
      st.mem (assigns + 2 * i + 1) = nSlots + uniqB.idxOf (bucketCode (origB (uniqE[i]'hi)))) ∧
    (∀ a, a < cnt ∨ (cnt + uniqB.length ≤ a ∧ a < assigns) ∨ assigns + 2 * j ≤ a → st.mem a = st0.mem a)
  have htr : Triple w p (fun st => st = st0)
      (forRange 14 (.const 0) (.reg 15)
        (.assign 25 (.load (.bin .add (.reg 13) (.reg 14))) ;;
         .assign 26 (.load (.bin .add (.reg 16) (.reg 25))) ;;
         .call 27 (bSort + sortIdxBinSearch) [.reg 19, .reg 20, .reg 26] ;;
         .assign 28 (.load (.bin .add (.reg 21) (.reg 27))) ;;
         .store (.bin .add (.reg 21) (.reg 27)) (.bin .add (.reg 28) (.const 1)) ;;
         .store (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.reg 25) ;;
         .store (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.const 1))
           (.bin .add (.reg 23) (.reg 27))))
      (normalPost (inv uniqE.length))
      (fun _ => rangeCost (fun _ => stepC) 0 uniqE.length +
        (uniqE.length - 0) * ((Expr.reg 15).size + 8) + ((Expr.const 0).size + (Expr.reg 15).size + 5)) := by
    refine Triple.forRange_le (fun _ => stepC) 0 uniqE.length (Nat.zero_le _) h1w (fun _ => by omega)
      ?_ (fun _ _ _ _ h => h.2.1)
      (fun _ _ _ _ h => Expr.eval_reg_of_eq ((h.1 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr15)) ?_
    · rintro st rfl
      exact ⟨Expr.eval_const (by omega), fun r h1 _ _ _ _ => Function.update_of_ne h1 _ _,
        by simp, fun bi hbi => by simp [hCnt0 bi hbi],
        fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩
    · intro j _ hj st ω' ⟨hregs, hr14, hcnt, hass, hfr⟩
      set e := uniqE[j]'hj
      set bc := bucketCode (origB e)
      set bi := uniqB.idxOf bc
      have hbk := hBkt e (List.getElem_mem hj)
      have hbi_lt : bi < uniqB.length := List.idxOf_lt_length_of_mem hbk.2.2
      have hmemE : st.mem (uniqE_ptr + j) = e := by rw [hfr _ (Or.inl (by omega))]; exact hEAt j hj
      have hmemBkt : st.mem (bktH + e) = bc := by
        rw [hfr _ (by rcases hBktD e (List.getElem_mem hj) with h | h <;> [exact Or.inl h; exact Or.inr (Or.inr (by omega))])]
        exact hbk.2.1
      have hBAt_st : ListAt st.mem uniqB_ptr uniqB := fun i hi => by
        rw [hfr _ (Or.inl (by omega))]; exact hBAt i hi
      have hcnt_j : st.mem (cnt + bi) =
          ((uniqE.take j).filter fun x => decide (uniqB.idxOf (bucketCode (origB x)) = bi)).length :=
        hcnt bi hbi_lt
      have hcnt_le : st.mem (cnt + bi) ≤ j := by
        rw [hcnt_j]; exact (List.length_filter_le _ _).trans (by simp)
      have hr13s := (hregs 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr13
      have hr16s := (hregs 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr16
      have hr19s := (hregs 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr19
      have hr20s := (hregs 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr20
      have hr21s := (hregs 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr21
      have hr22s := (hregs 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr22
      have hr23s := (hregs 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr23
      have ha1 : (Expr.load (.bin .add (.reg 13) (.reg 14))).eval w st = some e :=
        Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr13s) (Expr.eval_reg_of_eq hr14) (by omega)) hmemE
      set st1 : State := { st with regs := Function.update st.regs 25 e }
      have ha2 : (Expr.load (.bin .add (.reg 16) (.reg 25))).eval w st1 = some bc :=
        Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := bktH) (by simp [st1, hr16s]))
          (Expr.eval_reg_of_eq (v := e) (by simp [st1])) hbk.1) hmemBkt
      set st2 : State := { st1 with regs := Function.update st1.regs 26 bc }
      have hpreBS : (binSearchContract w uniqB bc).pre [uniqB_ptr, uniqB.length, bc] st2.mem :=
        ⟨uniqB_ptr, rfl, hw16, by omega, hBpw, hbk.2.2, hBAt_st, hBw⟩
      have hargsW : ∀ a ∈ [uniqB_ptr, uniqB.length, bc], a < 2 ^ w := by
        intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · omega
        · omega
        · exact hBw bc hbk.2.2
      obtain ⟨bodyBS, hbodyBS, retBS, stBS, cBS, hrunBS, hpostBS, hcBS⟩ :=
        binSearch_meetsContract hpSort [uniqB_ptr, uniqB.length, bc] st2.mem st2.pos ω' hargsW hpreBS
      obtain ⟨_, _, hmemBS, hretBS, _⟩ := hpostBS
      have hcallBS : Runs w p ω' (.call 27 (bSort + sortIdxBinSearch) [.reg 19, .reg 20, .reg 26])
          st2 .normal { stBS with regs := Function.update st2.regs 27 bi }
          (argsSize [.reg 19, .reg 20, .reg 26] + cBS + 1) := by
        have hbi_eq : bi = retBS.value := hretBS.symm
        rw [hbi_eq]
        exact runs_call_iff.mpr ⟨[uniqB_ptr, uniqB.length, bc], bodyBS, retBS, stBS, cBS,
          by simp [evalArgs, Expr.eval, st2, st1, hr19s, hr20s], hbodyBS, hrunBS, rfl, rfl, rfl⟩
      set st3 : State := { stBS with regs := Function.update st2.regs 27 bi }
      have hst3m : st3.mem = st.mem := hmemBS
      have ha4 : (Expr.load (.bin .add (.reg 21) (.reg 27))).eval w st3 = some (st.mem (cnt + bi)) :=
        Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := cnt) (by simp [st3, st2, st1, hr21s]))
          (Expr.eval_reg_of_eq (v := bi) (by simp [st3])) (by omega)) (by rw [hst3m])
      set st4 : State := { st3 with regs := Function.update st3.regs 28 (st.mem (cnt + bi)) }
      set m1 := Function.update st.mem (cnt + bi) (st.mem (cnt + bi) + 1)
      set m2 := Function.update m1 (assigns + 2 * j) e
      set m3 := Function.update m2 (assigns + 2 * j + 1) (nSlots + bi)
      have hs1 : Runs w p ω' (.store (.bin .add (.reg 21) (.reg 27)) (.bin .add (.reg 28) (.const 1)))
          st4 .normal { st4 with mem := m1 } _ :=
        runs_store_iff.mpr ⟨cnt + bi, st.mem (cnt + bi) + 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, hr21s]))
            (Expr.eval_reg_of_eq (by simp [st4, st3])) (by omega),
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4])) (Expr.eval_const h1w) (by omega),
          rfl, by simp [st4, hst3m, m1], rfl⟩
      have hs2 : Runs w p ω' (.store (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.reg 25))
          { st4 with mem := m1 } .normal { st4 with mem := m2 } _ :=
        runs_store_iff.mpr ⟨assigns + 2 * j, e,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, hr22s]))
            (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, hr14])) (by omega))
            (by omega),
          Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1]), rfl, rfl, rfl⟩
      have hs3 : Runs w p ω'
          (.store (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.const 1))
            (.bin .add (.reg 23) (.reg 27)))
          { st4 with mem := m2 } .normal { st4 with mem := m3 } _ :=
        runs_store_iff.mpr ⟨assigns + 2 * j + 1, nSlots + bi,
          Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, hr22s]))
              (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, hr14])) (by omega))
              (by omega))
            (Expr.eval_const h1w) (by omega),
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, hr23s]))
            (Expr.eval_reg_of_eq (by simp [st4, st3])) (by omega), rfl, rfl, rfl⟩
      have hbody := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, runs_assign_iff.mpr ⟨_, ha1, rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨st2, _, _, runs_assign_iff.mpr ⟨_, ha2, rfl, rfl, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hcallBS,
            runs_seq_iff.mpr (Or.inr ⟨st4, _, _, runs_assign_iff.mpr ⟨_, ha4, rfl, rfl, rfl⟩,
              runs_seq_iff.mpr (Or.inr ⟨{ st4 with mem := m1 }, _, _, hs1,
                runs_seq_iff.mpr (Or.inr ⟨{ st4 with mem := m2 }, _, _, hs2, hs3, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      refine ⟨.normal, { st4 with mem := m3 }, _, hbody, ⟨⟨?_, by simp, ?_, ?_, ?_⟩, by simp [st4, st3, st2, st1, hr14]⟩, ?_⟩
      · intro r h14 h25 h26 h27 h28
        simp [st4, st3, st2, st1, Function.update_of_ne h14, Function.update_of_ne h25,
          Function.update_of_ne h26, Function.update_of_ne h27, Function.update_of_ne h28,
          hregs r h14 h25 h26 h27 h28]
      · intro bi' hbi'
        rw [List.take_succ_eq_append_getElem hj, List.filter_append, List.length_append]
        change m3 (cnt + bi') = _
        have hm3 : m3 (cnt + bi') = m1 (cnt + bi') := by
          simp [m3, m2, Function.update_of_ne (by omega : cnt + bi' ≠ assigns + 2 * j + 1),
            Function.update_of_ne (by omega : cnt + bi' ≠ assigns + 2 * j)]
        rw [hm3]
        by_cases hEq : bi' = bi
        · subst hEq
          simp [m1, hcnt bi hbi', bi, bc, e]
        · simp [m1, Function.update_of_ne (by omega : cnt + bi' ≠ cnt + bi), hcnt bi' hbi',
            Ne.symm hEq, bi, bc, e]
      · intro i hi hix
        by_cases hij : i = j
        · subst hij
          exact ⟨by simp [m3, m2, e], by simp [m3, bi, bc, e]⟩
        · have h1 := hass i (by omega) hix
          exact ⟨by simp [m3, m2, m1, Function.update_of_ne (by omega : assigns + 2 * i ≠ assigns + 2 * j + 1),
              Function.update_of_ne (by omega : assigns + 2 * i ≠ assigns + 2 * j),
              Function.update_of_ne (by omega : assigns + 2 * i ≠ cnt + bi), h1.1],
            by simp [m3, m2, m1, Function.update_of_ne (by omega : assigns + 2 * i + 1 ≠ assigns + 2 * j + 1),
              Function.update_of_ne (by omega : assigns + 2 * i + 1 ≠ assigns + 2 * j),
              Function.update_of_ne (by omega : assigns + 2 * i + 1 ≠ cnt + bi), h1.2]⟩
      · intro a ha
        change m3 a = st0.mem a
        simp only [m3, m2, m1, Function.update_of_ne (by omega : a ≠ assigns + 2 * j + 1),
          Function.update_of_ne (by omega : a ≠ assigns + 2 * j),
          Function.update_of_ne (by omega : a ≠ cnt + bi)]
        exact hfr a (by omega)
      · dsimp only [binSearchContract] at hcBS
        simp only [stepC, argsSize, Expr.size] at hcBS ⊢; omega
  obtain ⟨o, st1, c1, hrun, hpost, hc⟩ := htr st0 ω rfl
  cases o with
  | returned _ => exact absurd hpost (by simp)
  | normal =>
    obtain ⟨hregs, _, hcnt, hass, hfr⟩ := hpost
    have hrc : rangeCost (fun _ => stepC) 0 uniqE.length = stepC * uniqE.length := by
      simp [rangeCost, Nat.mul_comm]
    have hRP : bundleReadPairs st1.mem assigns uniqE.length = assignsL := by
      apply List.ext_getElem
      · simp [bundleReadPairs, assignsL]
      · intro i hi1 hi2
        have hi : i < uniqE.length := by simpa [bundleReadPairs] using hi1
        simp only [bundleReadPairs, List.getElem_map, List.getElem_range, assignsL]
        exact Prod.ext (hass i hi hi).1 (hass i hi hi).2
    refine ⟨st1, c1, hrun, hregs, fun bi hbi => by simpa using hcnt bi hbi, hRP,
      fun a ha => hfr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (Or.inr h)]), ?_⟩
    rw [hrc] at hc; simp only [stepC, Expr.size, Nat.sub_zero] at hc
    have hcomm : (45 * (Nat.log 2 (uniqB.length + 1) + 1) + 70) * uniqE.length + 10 * uniqE.length =
        uniqE.length * (45 * (Nat.log 2 (uniqB.length + 1) + 1) + 80) := by ring
    omega

/-- Loop 4: writes `specs[0..2*r)`, `csl[0..2*r)`, and `slotsPtr[nSlots .. nSlots + r)`. -/
theorem newAct_loop4_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {uniqB_ptr cnt nSlots specs csl slotsPtr : ℕ} {uniqB : List ℕ} {cntFn : ℕ → ℕ} {st0 : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hr19 : st0.regs 19 = uniqB_ptr) (hr20 : st0.regs 20 = uniqB.length)
    (hr21 : st0.regs 21 = cnt) (hr23 : st0.regs 23 = nSlots)
    (hr24 : st0.regs 24 = specs) (hr25 : st0.regs 25 = csl) (hr28 : st0.regs 28 = slotsPtr)
    (hBAt : ListAt st0.mem uniqB_ptr uniqB)
    (hCntAt : ∀ bi < uniqB.length, st0.mem (cnt + bi) = cntFn bi ∧ 4 * cntFn bi < 2 ^ w)
    (hGeom : uniqB_ptr + uniqB.length ≤ specs ∧ cnt + uniqB.length ≤ specs ∧
      specs + 2 * uniqB.length ≤ csl ∧
      slotsPtr + nSlots + uniqB.length ≤ uniqB_ptr ∧
      slotsPtr + nSlots + uniqB.length ≤ cnt ∧
      nSlots + uniqB.length < 2 ^ w ∧ csl + 2 * uniqB.length < 2 ^ w) :
    let specsL := (List.range uniqB.length).map fun bi => (nSlots + bi, 4 * cntFn bi)
    ∃ st1 c1,
      Runs w p ω (forRange 14 (.const 0) (.reg 20)
        (.assign 29 (.bin .add (.reg 23) (.reg 14)) ;;
         .assign 27 (.load (.bin .add (.reg 21) (.reg 14))) ;;
         .store (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.reg 29) ;;
         .store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.const 1))
           (.bin .mul (.const 4) (.reg 27)) ;;
         .assign 27 (.load (.bin .add (.reg 19) (.reg 14))) ;;
         .store (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.reg 27) ;;
         .store (.bin .add (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.const 1))
           (.reg 29) ;;
         .store (.bin .add (.reg 28) (.reg 29)) (.reg 29)))
        st0 .normal st1 c1 ∧
      (∀ r, r ≠ 14 → r ≠ 27 → r ≠ 29 → st1.regs r = st0.regs r) ∧
      bundleReadPairs st1.mem specs uniqB.length = specsL ∧
      (∀ bi (hbi : bi < uniqB.length),
        st1.mem (csl + 2 * bi) = uniqB[bi]'hbi ∧ st1.mem (csl + 2 * bi + 1) = nSlots + bi) ∧
      (∀ bi < uniqB.length, st1.mem (slotsPtr + (nSlots + bi)) = nSlots + bi) ∧
      (∀ a, ¬ (specs ≤ a ∧ a < csl + 2 * uniqB.length) →
        ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + uniqB.length) → st1.mem a = st0.mem a) ∧
      c1 ≤ 90 * uniqB.length + 20 := by
  intro specsL
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  rcases hGeom with ⟨hBs, hCs, hsc, hSlB, hSlC, hnsW, hcslW⟩
  let inv : ℕ → State → Prop := fun j st =>
    (∀ r, r ≠ 14 → r ≠ 27 → r ≠ 29 → st.regs r = st0.regs r) ∧ st.regs 14 = j ∧
    (∀ bi < j, st.mem (specs + 2 * bi) = nSlots + bi ∧ st.mem (specs + 2 * bi + 1) = 4 * cntFn bi) ∧
    (∀ bi < j, ∀ hbi : bi < uniqB.length,
      st.mem (csl + 2 * bi) = uniqB[bi]'hbi ∧ st.mem (csl + 2 * bi + 1) = nSlots + bi) ∧
    (∀ bi < j, st.mem (slotsPtr + (nSlots + bi)) = nSlots + bi) ∧
    (∀ a, ¬ (specs ≤ a ∧ a < specs + 2 * j) → ¬ (csl ≤ a ∧ a < csl + 2 * j) →
      ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + j) → st.mem a = st0.mem a)
  have htr : Triple w p (fun st => st = st0)
      (forRange 14 (.const 0) (.reg 20)
        (.assign 29 (.bin .add (.reg 23) (.reg 14)) ;;
         .assign 27 (.load (.bin .add (.reg 21) (.reg 14))) ;;
         .store (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.reg 29) ;;
         .store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.const 1))
           (.bin .mul (.const 4) (.reg 27)) ;;
         .assign 27 (.load (.bin .add (.reg 19) (.reg 14))) ;;
         .store (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.reg 27) ;;
         .store (.bin .add (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.const 1))
           (.reg 29) ;;
         .store (.bin .add (.reg 28) (.reg 29)) (.reg 29)))
      (normalPost (inv uniqB.length))
      (fun _ => rangeCost (fun _ => 75) 0 uniqB.length +
        (uniqB.length - 0) * ((Expr.reg 20).size + 8) + ((Expr.const 0).size + (Expr.reg 20).size + 5)) := by
    refine Triple.forRange_le (fun _ => 75) 0 uniqB.length (Nat.zero_le _) h1w (fun _ => by omega)
      ?_ (fun _ _ _ _ h => h.2.1)
      (fun _ _ _ _ h => Expr.eval_reg_of_eq ((h.1 20 (by decide) (by decide) (by decide)).trans hr20)) ?_
    · rintro st rfl
      exact ⟨Expr.eval_const (by omega), fun r h1 _ _ => Function.update_of_ne h1 _ _,
        by simp, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ _ _ => rfl⟩
    · intro j _ hj st ω' ⟨hregs, hr14, hsp, hcsl, hsl, hfr⟩
      have hr19s := (hregs 19 (by decide) (by decide) (by decide)).trans hr19
      have hr21s := (hregs 21 (by decide) (by decide) (by decide)).trans hr21
      have hr23s := (hregs 23 (by decide) (by decide) (by decide)).trans hr23
      have hr24s := (hregs 24 (by decide) (by decide) (by decide)).trans hr24
      have hr25s := (hregs 25 (by decide) (by decide) (by decide)).trans hr25
      have hr28s := (hregs 28 (by decide) (by decide) (by decide)).trans hr28
      have hcntJ := hCntAt j hj
      have hmemCnt : st.mem (cnt + j) = cntFn j := by
        rw [hfr _ (by omega) (by omega) (by omega)]; exact hcntJ.1
      have hmemB : st.mem (uniqB_ptr + j) = uniqB[j]'hj := by
        rw [hfr _ (by omega) (by omega) (by omega)]; exact hBAt j hj
      set s := nSlots + j
      set m1 := Function.update st.mem (specs + 2 * j) s
      set m2 := Function.update m1 (specs + 2 * j + 1) (4 * cntFn j)
      set m3 := Function.update m2 (csl + 2 * j) (uniqB[j]'hj)
      set m4 := Function.update m3 (csl + 2 * j + 1) s
      set m5 := Function.update m4 (slotsPtr + s) s
      set rA := Function.update st.regs 29 s
      set rB := Function.update rA 27 (cntFn j)
      set rC := Function.update rB 27 (uniqB[j]'hj)
      have hm2_B : m2 (uniqB_ptr + j) = uniqB[j]'hj := by
        simp only [m2, m1, Function.update_of_ne (by omega : uniqB_ptr + j ≠ specs + 2 * j + 1),
          Function.update_of_ne (by omega : uniqB_ptr + j ≠ specs + 2 * j), hmemB]
      obtain ⟨cB, hrB, hcB⟩ : ∃ c, Runs w p ω'
          (.assign 29 (.bin .add (.reg 23) (.reg 14)) ;;
           .assign 27 (.load (.bin .add (.reg 21) (.reg 14))) ;;
           .store (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.reg 29) ;;
           .store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.const 1))
             (.bin .mul (.const 4) (.reg 27)) ;;
           .assign 27 (.load (.bin .add (.reg 19) (.reg 14))) ;;
           .store (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.reg 27) ;;
           .store (.bin .add (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.const 1))
             (.reg 29) ;;
           .store (.bin .add (.reg 28) (.reg 29)) (.reg 29))
          st .normal ⟨m5, rC, st.pos⟩ c ∧ 0 + c ≤ 75 := by
        refine rAssignLe (v := s)
          (Expr.eval_add (Expr.eval_reg_of_eq hr23s) (Expr.eval_reg_of_eq hr14) (by omega)) ?_
        refine rAssignLe (v := cntFn j)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr21s]))
            (Expr.eval_reg_of_eq (by simp [hr14])) (by omega)) hmemCnt) ?_
        refine rStoreLe
          (Expr.eval_add (Expr.eval_reg_of_eq (v := specs) (by simp [hr24s]))
            (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (v := j) (by simp [hr14])) (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := s) (by simp)) ?_
        refine rStoreLe
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := specs) (by simp [hr24s]))
              (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (v := j) (by simp [hr14])) (by omega)) (by omega))
            (Expr.eval_const h1w) (by omega))
          (Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq (v := cntFn j) (by simp)) hcntJ.2) ?_
        refine rAssignLe (v := uniqB[j]'hj)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := uniqB_ptr) (by simp [hr19s]))
            (Expr.eval_reg_of_eq (v := j) (by simp [hr14])) (by omega)) hm2_B) ?_
        refine rStoreLe
          (Expr.eval_add (Expr.eval_reg_of_eq (v := csl) (by simp [hr25s]))
            (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (v := j) (by simp [hr14])) (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := uniqB[j]'hj) (by simp)) ?_
        refine rStoreLe
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := csl) (by simp [hr25s]))
              (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (v := j) (by simp [hr14])) (by omega)) (by omega))
            (Expr.eval_const h1w) (by omega))
          (Expr.eval_reg_of_eq (v := s) (by simp)) ?_
        exact ⟨_, runs_store_iff.mpr ⟨slotsPtr + s, s,
          Expr.eval_add (Expr.eval_reg_of_eq (v := slotsPtr) (by simp [hr28s])) (Expr.eval_reg_of_eq (v := s) (by simp)) (by omega),
          Expr.eval_reg_of_eq (v := s) (by simp), rfl, rfl, rfl⟩, by simp only [Expr.size]; omega⟩
      refine ⟨.normal, ⟨m5, rC, st.pos⟩, cB, hrB, ⟨⟨?_, by simp, ?_, ?_, ?_, ?_⟩, by simp [rC, rB, rA, hr14]⟩, by dsimp only; omega⟩
      · intro r h14 h27 h29
        simp [rC, rB, rA, Function.update_of_ne h14, Function.update_of_ne h27,
          Function.update_of_ne h29, hregs r h14 h27 h29]
      · intro bi hbi
        by_cases hEq : bi = j
        · subst hEq
          exact ⟨by simp [m5, m4, m3, m2, m1, Function.update_of_ne (by omega : specs + 2 * bi ≠ slotsPtr + s),
              Function.update_of_ne (by omega : specs + 2 * bi ≠ csl + 2 * bi + 1),
              Function.update_of_ne (by omega : specs + 2 * bi ≠ csl + 2 * bi), s],
            by simp [m5, m4, m3, m2, Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ slotsPtr + s),
              Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ csl + 2 * bi + 1),
              Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ csl + 2 * bi)]⟩
        · have h1 := hsp bi (by omega)
          exact ⟨by simp [m5, m4, m3, m2, m1, Function.update_of_ne (by omega : specs + 2 * bi ≠ slotsPtr + s),
              Function.update_of_ne (by omega : specs + 2 * bi ≠ csl + 2 * j + 1),
              Function.update_of_ne (by omega : specs + 2 * bi ≠ csl + 2 * j),
              Function.update_of_ne (by omega : specs + 2 * bi ≠ specs + 2 * j + 1),
              Function.update_of_ne (by omega : specs + 2 * bi ≠ specs + 2 * j), h1.1],
            by simp [m5, m4, m3, m2, m1, Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ slotsPtr + s),
              Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ csl + 2 * j + 1),
              Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ csl + 2 * j),
              Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ specs + 2 * j + 1),
              Function.update_of_ne (by omega : specs + 2 * bi + 1 ≠ specs + 2 * j), h1.2]⟩
      · intro bi hbi hblt
        by_cases hEq : bi = j
        · subst hEq
          exact ⟨by simp [m5, m4, m3, Function.update_of_ne (by omega : csl + 2 * bi ≠ slotsPtr + s)],
            by simp [m5, m4, Function.update_of_ne (by omega : csl + 2 * bi + 1 ≠ slotsPtr + s), s]⟩
        · have h1 := hcsl bi (by omega) hblt
          exact ⟨by simp [m5, m4, m3, m2, m1, Function.update_of_ne (by omega : csl + 2 * bi ≠ slotsPtr + s),
              Function.update_of_ne (by omega : csl + 2 * bi ≠ csl + 2 * j + 1),
              Function.update_of_ne (by omega : csl + 2 * bi ≠ csl + 2 * j),
              Function.update_of_ne (by omega : csl + 2 * bi ≠ specs + 2 * j + 1),
              Function.update_of_ne (by omega : csl + 2 * bi ≠ specs + 2 * j), h1.1],
            by simp [m5, m4, m3, m2, m1, Function.update_of_ne (by omega : csl + 2 * bi + 1 ≠ slotsPtr + s),
              Function.update_of_ne (by omega : csl + 2 * bi + 1 ≠ csl + 2 * j + 1),
              Function.update_of_ne (by omega : csl + 2 * bi + 1 ≠ csl + 2 * j),
              Function.update_of_ne (by omega : csl + 2 * bi + 1 ≠ specs + 2 * j + 1),
              Function.update_of_ne (by omega : csl + 2 * bi + 1 ≠ specs + 2 * j), h1.2]⟩
      · intro bi hbi
        by_cases hEq : bi = j
        · subst hEq; simp [m5, s]
        · have h1 := hsl bi (by omega)
          simp [m5, m4, m3, m2, m1,
            Function.update_of_ne (by omega : slotsPtr + (nSlots + bi) ≠ slotsPtr + s),
            Function.update_of_ne (by omega : slotsPtr + (nSlots + bi) ≠ csl + 2 * j + 1),
            Function.update_of_ne (by omega : slotsPtr + (nSlots + bi) ≠ csl + 2 * j),
            Function.update_of_ne (by omega : slotsPtr + (nSlots + bi) ≠ specs + 2 * j + 1),
            Function.update_of_ne (by omega : slotsPtr + (nSlots + bi) ≠ specs + 2 * j), h1]
      · intro a h1 h2 h3
        change m5 a = st0.mem a
        simp only [m5, m4, m3, m2, m1,
          Function.update_of_ne (by omega : a ≠ slotsPtr + s),
          Function.update_of_ne (by omega : a ≠ csl + 2 * j + 1),
          Function.update_of_ne (by omega : a ≠ csl + 2 * j),
          Function.update_of_ne (by omega : a ≠ specs + 2 * j + 1),
          Function.update_of_ne (by omega : a ≠ specs + 2 * j)]
        exact hfr a (by omega) (by omega) (by omega)
  obtain ⟨o, st1, c1, hrun, hpost, hc⟩ := htr st0 ω rfl
  cases o with
  | returned _ => exact absurd hpost (by simp)
  | normal =>
    obtain ⟨hregs, _, hsp, hcsl, hsl, hfr⟩ := hpost
    have hrc : rangeCost (fun _ => 75) 0 uniqB.length = 75 * uniqB.length := by
      simp [rangeCost, Nat.mul_comm]
    have hRP : bundleReadPairs st1.mem specs uniqB.length = specsL := by
      apply List.ext_getElem
      · simp [bundleReadPairs, specsL]
      · intro i hi1 hi2
        have hi : i < uniqB.length := by simpa [bundleReadPairs] using hi1
        simp only [bundleReadPairs, List.getElem_map, List.getElem_range, specsL]
        exact Prod.ext (hsp i hi).1 (hsp i hi).2
    refine ⟨st1, c1, hrun, hregs, hRP, fun bi hbi => hcsl bi hbi hbi, hsl,
      fun a ha1 ha2 => hfr a (by omega) (by omega) ha2, ?_⟩
    rw [hrc] at hc; simp only [Expr.size, Nat.sub_zero] at hc; omega


end

end MinCostFlow.SparseCore.Program
