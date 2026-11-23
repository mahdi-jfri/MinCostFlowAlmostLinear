module

public import MinCostFlow.SparseCore.Program.AssemblyFirstOutEdges

/-!
# Verification of the entering-edges output builder (`AssemblyFirstOutIns`)

Verifies `asmFirstBuildInsStmt bSort` (`AssemblyFirstOutEdges.lean`), which takes a candidate
superset `supL` of the entering output edges (`outInsSet`), filters it via `OutSelFlagsAt`,
sorts and deduplicates it into `insL = S.sort (· ≤ ·)` via `filterSortDedup_runs`, and formats
`OutInsAt` (`[|insL|, e₀, tl₀, hd₀, …]`) using `OutInsEndsAt` with `OutCellsFree`, `ZeroFrom`,
frame below `h`, linear heap space `≤ 2 + 6 * supL.length`, and time
`O((supL.length + 1) * (Nat.log 2 (supL.length + 1) + 1))`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

public section

/-- **Verification of `asmFirstBuildInsStmt bSort` (`OutInsAt`)**: given any superset `supL` of
`S` (such as `outInsSet sparsify tr U ord ord'`) and `O(1)` membership and endpoint tables
`OutSelFlagsAt` and `OutInsEndsAt`, writes `insPtr` at `h`, writes
`OutInsAt st'.mem insPtr (S.sort (· ≤ ·)) tl hd` with `OutCellsFree` against any `avoid` lying
below `h`, preserves memory below `h`, maintains `ZeroFrom`, uses at most `2 + 6 * supL.length`
words of heap, and runs in `O((supL.length + 1) * (Nat.log 2 (supL.length + 1) + 1))` time. -/
theorem asmFirstBuildIns_runs {w : ℕ} {p : Program} {bSort : ℕ}
    (hp : p.HasAt bSort (sortProcs bSort))
    {supPtr selPtr tlPtr hdPtr eCap h pos : ℕ} {supL : List ℕ} {S : Finset ℕ}
    {tl hd : ℕ → ℕ} {avoid : ℕ → Prop} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hsup : ListAt mem₀ supPtr supL) (hsup_lt : supPtr + supL.length ≤ h)
    (hsup_cap : ∀ e ∈ supL, e < eCap) (hsup_cov : ∀ e ∈ S, e ∈ supL)
    (hsel : OutSelFlagsAt mem₀ selPtr eCap S) (hsel_lt : selPtr + eCap ≤ h)
    (hends : OutInsEndsAt mem₀ tlPtr hdPtr eCap tl hd)
    (htl_lt : tlPtr + eCap ≤ h) (hhd_lt : hdPtr + eCap ≤ h)
    (havoid : ∀ a, avoid a → a < h)
    (heCap_w : eCap < 2 ^ w)
    (hz : ZeroFrom mem₀ h)
    (hspace : h + 2 + 6 * supL.length < 2 ^ w) :
    let insL := S.sort (· ≤ ·)
    ∃ o st' c,
      Runs w p ω (asmFirstBuildInsStmt bSort)
        (startState [supPtr, supL.length, selPtr, tlPtr, hdPtr, h] mem₀ pos) o st' c ∧
      OutInsAt st'.mem (st'.mem h) insL tl hd ∧
      OutCellsFree (st'.mem h) (1 + 3 * insL.length) o.value avoid ∧
      h + 1 ≤ st'.mem h ∧ st'.mem h < o.value ∧
      h + 2 ≤ o.value ∧ o.value ≤ h + 2 + 6 * supL.length ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      c ≤ outBuildCost supL.length := by
  intro insL
  have hw1 : 1 < 2 ^ w := by omega
  set st0 := startState [supPtr, supL.length, selPtr, tlPtr, hdPtr, h] mem₀ pos
  set r0 := Function.update st0.regs 5 (h + 1)
  have hr_a5 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 1))) st0 .normal
      ⟨mem₀, r0, pos⟩ ((Expr.bin .add (.reg 5) (.const 1)).size + 1) :=
    runs_assign_iff.mpr ⟨h + 1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  obtain ⟨st1, c1, hr_fsd, h10, h11, h12, h13, h14, h15, h16, h19, h110,
      hflt_le, hins_le, hlat1, hfr1, hc1⟩ :=
    filterSortDedup_runs (r3 := tlPtr) (r4 := hdPtr) (regs₀ := r0) (pos := pos) (ω := ω) hp hw16
      (by simp [r0, st0, startState]) (by simp [r0, st0, startState])
      (by simp [r0, st0, startState]) (by simp [r0, st0, startState])
      (by simp [r0, st0, startState]) (by simp [r0])
      hsup hsup_lt hsup_cap hsup_cov hsel hsel_lt heCap_w (by omega)
  set fltLen := (supL.filter (fun e => decide (e ∈ S))).length
  have hil_le : insL.length ≤ fltLen := hins_le
  set outPtr := h + 1 + 2 * fltLen
  set insPtr := outPtr + insL.length
  have hip_eq : insPtr = h + 1 + 2 * fltLen + insL.length := rfl
  set r1 := Function.update st1.regs 11 insPtr
  have hr_a11 : Runs w p ω (.assign 11 (.bin .add (.reg 9) (.reg 10))) st1 .normal
      ⟨st1.mem, r1, st1.pos⟩ ((Expr.bin .add (.reg 9) (.reg 10)).size + 1) :=
    runs_assign_iff.mpr ⟨insPtr,
      Expr.eval_add (Expr.eval_reg_of_eq h19) (Expr.eval_reg_of_eq h110) (by omega), rfl, rfl, rfl⟩
  set mem2 := Function.update st1.mem h insPtr
  have hr_sh : Runs w p ω (.store (.bin .sub (.reg 5) (.const 1)) (.reg 11))
      ⟨st1.mem, r1, st1.pos⟩ .normal ⟨mem2, r1, st1.pos⟩
      ((Expr.bin .sub (.reg 5) (.const 1)).size + (Expr.reg 11).size + 1) := by
    refine runs_store_iff.mpr ⟨h, insPtr, ?_, Expr.eval_reg_of_eq (by simp [r1]), rfl, rfl, rfl⟩
    have hsub : (h + 1) - 1 = h := by omega
    rw [← hsub]
    exact Expr.eval_sub (Expr.eval_reg_of_eq (by simp [r1, h15]))
      (Expr.eval_const (by omega)) (by omega)
  set mem3 := Function.update mem2 insPtr insL.length
  have hr_sd : Runs w p ω (.store (.reg 11) (.reg 10)) ⟨mem2, r1, st1.pos⟩ .normal
      ⟨mem3, r1, st1.pos⟩ ((Expr.reg 11).size + (Expr.reg 10).size + 1) :=
    runs_store_iff.mpr ⟨insPtr, insL.length,
      Expr.eval_reg_of_eq (by simp [r1]),
      Expr.eval_reg_of_eq (by simp only [r1, Function.update_of_ne (by decide : (10 : ℕ) ≠ 11), h110]; rfl),
      rfl, rfl, rfl⟩
  let WInv : ℕ → State → Prop := fun j st =>
    st.regs 3 = tlPtr ∧ st.regs 4 = hdPtr ∧ st.regs 9 = outPtr ∧ st.regs 10 = insL.length ∧
    st.regs 11 = insPtr ∧ st.regs 12 = j ∧
    st.mem h = insPtr ∧ st.mem insPtr = insL.length ∧
    (∀ i < j, st.mem (insPtr + 1 + 3 * i) = insL.getD i 0 ∧
      st.mem (insPtr + 2 + 3 * i) = tl (insL.getD i 0) ∧
      st.mem (insPtr + 3 + 3 * i) = hd (insL.getD i 0)) ∧
    (∀ a, a < insPtr + 1 ∨ insPtr + 1 + 3 * j ≤ a → st.mem a = mem3 a)
  have hWbody : ∀ j < insL.length,
      Triple w p (WInv j)
        (.assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
         .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
         .assign 15 (.load (.bin .add (.reg 4) (.reg 13))) ;;
         .store (.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 3) (.reg 12))) (.reg 13) ;;
         .store (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 3) (.reg 12))) (.reg 14) ;;
         .store (.bin .add (.bin .add (.reg 11) (.const 3)) (.bin .mul (.const 3) (.reg 12))) (.reg 15))
        (normalPost fun st₁ =>
          WInv (j + 1) { st₁ with regs := Function.update st₁.regs 12 (j + 1) } ∧ st₁.regs 12 = j)
        (fun _ => 70) := by
    intro j hj st ω' ⟨hr3, hr4, hr9, hr10, hr11, hr12, hmh, hmd, hout, hfrW⟩
    set e := insL[j]'hj
    have he_S : e ∈ S := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hj)
    have he_cap : e < eCap := hsup_cap e (hsup_cov e he_S)
    have hme : st.mem (outPtr + j) = e := by
      rw [hfrW (outPtr + j) (Or.inl (by omega))]
      simp only [mem3, mem2, Function.update_of_ne (show outPtr + j ≠ insPtr by omega),
        Function.update_of_ne (show outPtr + j ≠ h by omega)]
      exact hlat1 j hj
    have hmtl : st.mem (tlPtr + e) = tl e := by
      rw [hfrW (tlPtr + e) (Or.inl (by omega))]
      simp only [mem3, mem2, Function.update_of_ne (show tlPtr + e ≠ insPtr by omega),
        Function.update_of_ne (show tlPtr + e ≠ h by omega)]
      rw [hfr1 (tlPtr + e) (Or.inl (by omega))]
      exact (hends e he_cap).1
    have hmhd : st.mem (hdPtr + e) = hd e := by
      rw [hfrW (hdPtr + e) (Or.inl (by omega))]
      simp only [mem3, mem2, Function.update_of_ne (show hdPtr + e ≠ insPtr by omega),
        Function.update_of_ne (show hdPtr + e ≠ h by omega)]
      rw [hfr1 (hdPtr + e) (Or.inl (by omega))]
      exact (hends e he_cap).2
    have he13 : (Expr.load (.bin .add (.reg 9) (.reg 12))).eval w st = some e :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_reg_of_eq hr12)
        (by omega)) hme
    set rA := Function.update st.regs 13 e
    have he14 : (Expr.load (.bin .add (.reg 3) (.reg 13))).eval w ⟨st.mem, rA, st.pos⟩ =
        some (tl e) :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr3]))
        (Expr.eval_reg_of_eq (by simp [rA])) (by omega)) hmtl
    set rB := Function.update rA 14 (tl e)
    have he15 : (Expr.load (.bin .add (.reg 4) (.reg 13))).eval w ⟨st.mem, rB, st.pos⟩ =
        some (hd e) :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr4]))
        (Expr.eval_reg_of_eq (by simp [rB, rA])) (by omega)) hmhd
    set rC := Function.update rB 15 (hd e)
    have heA1 : (Expr.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 3) (.reg 12))).eval w
        ⟨st.mem, rC, st.pos⟩ = some (insPtr + 1 + 3 * j) :=
      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr11]))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr12])) (by omega)) (by omega)
    set mA := Function.update st.mem (insPtr + 1 + 3 * j) e
    have heA2 : (Expr.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 3) (.reg 12))).eval w
        ⟨mA, rC, st.pos⟩ = some (insPtr + 2 + 3 * j) :=
      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr11]))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr12])) (by omega)) (by omega)
    set mB := Function.update mA (insPtr + 2 + 3 * j) (tl e)
    have heA3 : (Expr.bin .add (.bin .add (.reg 11) (.const 3)) (.bin .mul (.const 3) (.reg 12))).eval w
        ⟨mB, rC, st.pos⟩ = some (insPtr + 3 + 3 * j) :=
      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr11]))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr12])) (by omega)) (by omega)
    set mC := Function.update mB (insPtr + 3 + 3 * j) (hd e)
    have hr13 : Runs w p ω' (.assign 13 _) st .normal ⟨st.mem, rA, st.pos⟩ _ :=
      runs_assign_iff.mpr ⟨e, he13, rfl, rfl, rfl⟩
    have hr14 : Runs w p ω' (.assign 14 _) ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩ _ :=
      runs_assign_iff.mpr ⟨tl e, he14, rfl, rfl, rfl⟩
    have hr15 : Runs w p ω' (.assign 15 _) ⟨st.mem, rB, st.pos⟩ .normal ⟨st.mem, rC, st.pos⟩ _ :=
      runs_assign_iff.mpr ⟨hd e, he15, rfl, rfl, rfl⟩
    have hrS1 : Runs w p ω' (.store _ (.reg 13)) ⟨st.mem, rC, st.pos⟩ .normal ⟨mA, rC, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨_, e, heA1, Expr.eval_reg_of_eq (by simp [rC, rB, rA]), rfl, rfl, rfl⟩
    have hrS2 : Runs w p ω' (.store _ (.reg 14)) ⟨mA, rC, st.pos⟩ .normal ⟨mB, rC, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨_, tl e, heA2, Expr.eval_reg_of_eq (by simp [rC, rB]), rfl, rfl, rfl⟩
    have hrS3 : Runs w p ω' (.store _ (.reg 15)) ⟨mB, rC, st.pos⟩ .normal ⟨mC, rC, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨_, hd e, heA3, Expr.eval_reg_of_eq (by simp [rC]), rfl, rfl, rfl⟩
    have hrAll := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr13,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr14,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr15,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrS1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrS2, hrS3, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨.normal, _, _, hrAll, ⟨⟨by simp [rC, rB, rA, hr3], by simp [rC, rB, rA, hr4],
      by simp [rC, rB, rA, hr9], by simp [rC, rB, rA, hr10], by simp [rC, rB, rA, hr11], by simp,
      by simp [mC, mB, mA, Function.update_of_ne (show h ≠ insPtr + 3 + 3 * j by omega),
          Function.update_of_ne (show h ≠ insPtr + 2 + 3 * j by omega),
          Function.update_of_ne (show h ≠ insPtr + 1 + 3 * j by omega), hmh],
      by simp [mC, mB, mA, Function.update_of_ne (show insPtr ≠ insPtr + 3 + 3 * j by omega),
          Function.update_of_ne (show insPtr ≠ insPtr + 2 + 3 * j by omega),
          Function.update_of_ne (show insPtr ≠ insPtr + 1 + 3 * j by omega), hmd],
      ?_, ?_⟩, by simp [rC, rB, rA, hr12]⟩, by simp [Expr.size]⟩
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hij | heq
      · simp only [mC, mB, mA,
          Function.update_of_ne (show insPtr + 1 + 3 * i ≠ insPtr + 3 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 1 + 3 * i ≠ insPtr + 2 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 1 + 3 * i ≠ insPtr + 1 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 2 + 3 * i ≠ insPtr + 3 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 2 + 3 * i ≠ insPtr + 2 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 2 + 3 * i ≠ insPtr + 1 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 3 + 3 * i ≠ insPtr + 3 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 3 + 3 * i ≠ insPtr + 2 + 3 * j by omega),
          Function.update_of_ne (show insPtr + 3 + 3 * i ≠ insPtr + 1 + 3 * j by omega)]
        exact hout i hij
      · subst heq
        have hgetD : insL.getD i 0 = e := List.getD_eq_getElem _ _ hj
        rw [hgetD]
        simp [mC, mB, mA]
    · intro a ha
      simp only [mC, mB, mA,
        Function.update_of_ne (show a ≠ insPtr + 3 + 3 * j by omega),
        Function.update_of_ne (show a ≠ insPtr + 2 + 3 * j by omega),
        Function.update_of_ne (show a ≠ insPtr + 1 + 3 * j by omega)]
      exact hfrW a (by omega)
  have hWloop := Triple.forRange_le
    (P := fun st => st.mem = mem3 ∧ st.regs 3 = tlPtr ∧ st.regs 4 = hdPtr ∧
      st.regs 9 = outPtr ∧ st.regs 10 = insL.length ∧ st.regs 11 = insPtr)
    (fun _ => 70) 0 insL.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hm, hr3, hr4, hr9, hr10, hr11⟩ =>
      ⟨Expr.eval_const (by omega),
       ⟨by simp [hr3], by simp [hr4], by simp [hr9], by simp [hr10], by simp [hr11], by simp,
        by simp [hm, mem3, mem2, Function.update_of_ne (show h ≠ insPtr by omega)],
        by simp [hm, mem3], fun i hi => absurd hi (Nat.not_lt_zero _),
        fun a _ => by rw [hm]⟩⟩)
    (fun j st _ _ hI => hI.2.2.2.2.2.1)
    (fun j st _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.1)
    (fun j _ hj => hWbody j hj)
  obtain ⟨oW, stW, cW, hrW, hpostW, hcW⟩ := hWloop ⟨mem3, r1, st1.pos⟩ ω
    ⟨rfl, by simp [r1, h13], by simp [r1, h14], by simp [r1, h19],
     by simp only [r1, Function.update_of_ne (by decide : (10 : ℕ) ≠ 11), h110]; rfl, by simp [r1]⟩
  cases oW with
  | returned _ => cases hpostW
  | normal =>
  obtain ⟨-, -, -, hr10W, hr11W, -, hmhW, hmdW, houtW, hfrW⟩ := hpostW
  have hil_le : insL.length ≤ fltLen := hins_le
  have hip_eq : insPtr = h + 1 + 2 * fltLen + insL.length := rfl
  set hEnd := insPtr + 1 + 3 * insL.length
  have hend_eq : hEnd = insPtr + 1 + 3 * insL.length := rfl
  have heRet : (Expr.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 3) (.reg 10))).eval w stW =
      some hEnd :=
    Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr11W) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr10W) (by omega)) (by omega)
  have hr_ret : Runs w p ω (.ret _) stW (.returned hEnd) stW _ :=
    runs_ret_iff.mpr ⟨hEnd, heRet, rfl, rfl, rfl⟩
  have hr_full := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a5,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_fsd,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a11,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_sh,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_sd,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrW, hr_ret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨.returned hEnd, stW, _, hr_full, ?_, ?_, by rw [hmhW]; omega,
    by simp only [Outcome.value]; rw [hmhW]; omega,
    by simp only [Outcome.value]; omega, by simp only [Outcome.value]; omega, ?_, ?_, ?_⟩
  · rw [hmhW]; exact ⟨hmdW, houtW⟩
  · rw [hmhW]
    exact ⟨by simp only [Outcome.value]; omega, fun i _ ha => by have := havoid _ ha; omega⟩
  · intro a ha
    change hEnd ≤ a at ha
    rw [hfrW a (Or.inr ha)]
    simp only [mem3, mem2, Function.update_of_ne (show a ≠ insPtr by omega),
      Function.update_of_ne (show a ≠ h by omega)]
    rw [hfr1 a (Or.inr (by omega))]
    exact hz a (by omega)
  · intro a ha
    rw [hfrW a (Or.inl (by omega))]
    simp only [mem3, mem2, Function.update_of_ne (show a ≠ insPtr by omega),
      Function.update_of_ne (show a ≠ h by omega)]
    exact hfr1 a (Or.inl (by omega))
  · have hrcW : rangeCost (fun _ => 70) 0 insL.length = 70 * insL.length := by
      simp [rangeCost, Nat.mul_comm]
    dsimp only at hcW
    simp only [outBuildCost, Expr.size, Nat.sub_zero, hrcW] at hcW ⊢
    have hil : insL.length ≤ supL.length := le_trans hins_le hflt_le
    set L := Nat.log 2 (supL.length + 1) + 1
    have hL1 : 1 ≤ L := Nat.succ_pos _
    have h100 : 100 * supL.length ≤ 100 * supL.length * L := Nat.le_mul_of_pos_right _ hL1
    have hdist : 280 * supL.length * L + 100 * supL.length * L ≤ 380 * (supL.length + 1) * L := by
      have : 280 * supL.length * L + 100 * supL.length * L = 380 * supL.length * L := by
        rw [← Nat.add_mul, ← Nat.add_mul]
      rw [this]
      exact Nat.mul_le_mul_right L (Nat.mul_le_mul_left 380 (Nat.le_succ _))
    clear hmdW hmhW
    omega

end

end MinCostFlow.SparseCore.Program
