module

public import MinCostFlow.LSF.Program.UArith
public import MinCostFlow.LSF.Program.Lca
public import MinCostFlow.LSF.Program.TopDownPass

/-!
# The tree distance of two vertices

`treeDistProc` finds the lowest common ancestor `l` of two indices `x` and `y` (`lcaProc`) and
writes into a block `dst` the value `Ld x + Ld y - 2 Ld l`, where `Ld` are the weighted depths of
`WDepth.lean`. It works modulo the capacity: it zeroes `dst`, adds `Ld x` and `Ld y` and
subtracts `Ld l` twice (`uAccProc`). When the true values are small enough the result is exact
(`distMod_eq`). It returns `l`. The cost is `O(logCap + LB)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

/-- The value that `treeDistProc` writes, modulo the capacity `c`. -/
def distMod (c X Y Z : ℕ) : ℕ := ((((X % c + Y) % c) + (c - Z)) % c + (c - Z)) % c

lemma distMod_eq {c X Y Z : ℕ} (hZX : Z ≤ X) (hZY : Z ≤ Y) (hXY : X + Y < c) :
    distMod c X Y Z = X + Y - 2 * Z := by
  unfold distMod
  have hX : X < c := by omega
  rw [Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hXY]
  have h1 : (X + Y + (c - Z)) % c = X + Y - Z := by
    rw [show X + Y + (c - Z) = (X + Y - Z) + c by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, show X + Y - Z + (c - Z) = (X + Y - 2 * Z) + c by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- Args: `[dst, x, y, ldBase, LB, logCap, upPtr, depPtr, parPtr]`. Register `9` is the lowest
common ancestor, `10` is the zero loop index. -/
def treeDistProc (bAcc bLca : ℕ) : Stmt :=
  .call 9 bLca [.reg 1, .reg 2, .reg 5, .reg 6, .reg 7, .reg 8] ;;
  forRange 10 (.const 0) (.reg 4) (.store (.bin .add (.reg 0) (.reg 10)) (.const 0)) ;;
  .call 11 bAcc [.reg 0, .bin .add (.reg 3) (.bin .mul (.reg 1) (.reg 4)), .reg 4, .const 1,
    .const 0] ;;
  .call 11 bAcc [.reg 0, .bin .add (.reg 3) (.bin .mul (.reg 2) (.reg 4)), .reg 4, .const 1,
    .const 0] ;;
  .call 11 bAcc [.reg 0, .bin .add (.reg 3) (.bin .mul (.reg 9) (.reg 4)), .reg 4, .const 0,
    .const 1] ;;
  .call 11 bAcc [.reg 0, .bin .add (.reg 3) (.bin .mul (.reg 9) (.reg 4)), .reg 4, .const 0,
    .const 1] ;;
  .ret (.reg 9)

lemma treeDistProc_noRand (bAcc bLca : ℕ) : (treeDistProc bAcc bLca).NoRand := by
  simp [treeDistProc, forRange, forUp, Stmt.NoRand]

/-- The contract of `treeDistProc`. The block `dst` meets none of the weighted-depth blocks. -/
def treeDistContract (w h : ℕ) : Contract where
  pre args mem := ∃ (dst x y ldBase LB logCap upPtr depPtr parPtr n tM r : ℕ)
      (tl hd par pe dep : ℕ → ℕ),
    args = [dst, x, y, ldBase, LB, logCap, upPtr, depPtr, parPtr] ∧ 16 ≤ 2 ^ w ∧
    RootedArrays n tM r tl hd par pe dep ∧ x < n ∧ y < n ∧
    LcaTables w n logCap upPtr depPtr parPtr par dep mem ∧
    (∀ z < n, Valid mem (ldBase + z * LB) h LB) ∧
    (dst + LB ≤ ldBase ∨ ldBase + n * LB ≤ dst) ∧ ldBase + n * LB < 2 ^ w ∧ dst + LB < 2 ^ w
  post args mem ret mem' := ∃ (dst x y ldBase LB logCap upPtr depPtr parPtr : ℕ),
    args = [dst, x, y, ldBase, LB, logCap, upPtr, depPtr, parPtr] ∧
    (∀ a, a < dst ∨ dst + LB ≤ a → mem' a = mem a) ∧ Valid mem' dst h LB ∧
    unsignedVal mem' dst h LB = distMod (capacity h LB) (unsignedVal mem (ldBase + x * LB) h LB)
      (unsignedVal mem (ldBase + y * LB) h LB) (unsignedVal mem (ldBase + ret * LB) h LB) ∧
    ∀ (n tM r : ℕ) (tl hd par pe dep : ℕ → ℕ), RootedArrays n tM r tl hd par pe dep →
      x < n → y < n → LcaTables w n logCap upPtr depPtr parPtr par dep mem →
      ret < n ∧ IsLcaOf par dep ret x y
  cost args _ := 100 * args.getD 5 0 + 400 * args.getD 4 0 + 300

theorem treeDist_meetsContract {w h : ℕ} {p : Program} {b bAcc bLca : ℕ}
    (hAcc : MeetsContract w p bAcc (uAccContract w h))
    (hLca : MeetsContract w p bLca (lcaContract w)) (hh : 1 ≤ h) (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (treeDistProc bAcc bLca)) :
    MeetsContract w p b (treeDistContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨dst, x, y, ldBase, LB, logCap, upPtr, depPtr, parPtr, n, tM, r, tl, hd, par, pe, dep,
    rfl, h16, hR, hx, hy, hT, hval, hdisj, hldw, hdw⟩ := hpre
  have hB0 : 0 < base h := base_pos h
  have hw1 : 1 < 2 ^ w := by omega
  set args := [dst, x, y, ldBase, LB, logCap, upPtr, depPtr, parPtr] with hargs
  have hR0 : ∀ i < 9, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hLw : LB < 2 ^ w := by omega
  have hbx := blk_end LB hx
  have hby := blk_end LB hy
  refine runs_start_le ?_
  unfold treeDistProc
  -- the lowest common ancestor
  refine runs_seq_call_le (vs := [x, y, logCap, upPtr, depPtr, parPtr]) hLca
    (evalArgs_cons (by have := hR0 1 (by omega); eval_expr)
      (evalArgs_cons (by have := hR0 2 (by omega); eval_expr)
      (evalArgs_cons (by have := hR0 5 (by omega); eval_expr)
      (evalArgs_cons (by have := hR0 6 (by omega); eval_expr)
      (evalArgs_cons (by have := hR0 7 (by omega); eval_expr)
      (evalArgs_cons (by have := hR0 8 (by omega); eval_expr) (evalArgs_nil _ _)))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hwords _ (by simp [hargs]))
    ⟨x, y, logCap, upPtr, depPtr, parPtr, n, tM, r, tl, hd, par, pe, dep, rfl, h16, hR, hx, hy,
      hT⟩ ?_
  rintro l mem₀ pos₀ ⟨hm₀, hlca⟩
  obtain ⟨hln, hlcaOf⟩ := hlca x y logCap upPtr depPtr parPtr n tM r tl hd par pe dep rfl hR hx hy
    hT
  have hm' : mem = mem₀ := hm₀.symm
  subst hm'
  have hbl := blk_end LB hln
  -- the zero loop
  let Inv1 : ℕ → State → Prop := fun i st =>
    (∀ j < 9, st.regs j = args.getD j 0) ∧ st.regs 9 = l ∧ st.regs 10 = i ∧
    (∀ a, a < dst ∨ dst + i ≤ a → st.mem a = mem a) ∧ ∀ j < i, st.mem (dst + j) = 0
  have hloop1 : Triple w p
      (fun st => (∀ j < 9, st.regs j = args.getD j 0) ∧ st.regs 9 = l ∧ st.mem = mem)
      (forRange 10 (.const 0) (.reg 4) (.store (.bin .add (.reg 0) (.reg 10)) (.const 0)))
      (normalPost (Inv1 LB))
      (fun _ => (LB - 0) * (10 + (Expr.reg 4).size + 8) +
        ((Expr.const 0).size + (Expr.reg 4).size + 5)) := by
    refine Triple.forRange_const 10 0 LB (by omega) hw1 (fun _ => hLw) ?_ ?_ ?_ ?_
    · rintro st ⟨hr0, hr9, hm⟩
      refine ⟨by eval_expr, fun j hj => ?_, by simp [hr9], by simp, fun a _ => by rw [hm],
        fun j hj => absurd hj (by omega)⟩
      simp only [Function.update_of_ne (show j ≠ 10 by omega)]; exact hr0 j hj
    · intro i st _ _ hI; exact hI.2.2.1
    · intro i st _ _ hI
      have r4 : st.regs 4 = LB := hI.1 4 (by omega)
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨hR', h9, h10, hfr, hz⟩ := hI
      have r0 : st.regs 0 = dst := hR' 0 (by omega)
      refine runs_start_le ?_
      refine runs_store_le (x := dst + i) (v := 0) (by eval_expr) (by eval_expr)
        ⟨⟨fun j hj => ?_, by simpa using h9, by simp, fun a ha => ?_, fun j hj => ?_⟩,
          by simpa using h10⟩ (by simp [Expr.size])
      · simp only [Function.update_of_ne (show j ≠ 10 by omega)]; exact hR' j hj
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]; exact hz j hj
        · rw [Function.update_self]
  refine runs_seq_triple_le hloop1 ⟨fun j hj => ?_, by simp, rfl⟩ ?_
  · simp only [Function.update_of_ne (show j ≠ 9 by omega)]; exact hR0 j hj
  rintro st₁ ⟨hr₁, h9₁, -, hfr₁, hz₁⟩
  have r0 : st₁.regs 0 = dst := hr₁ 0 (by omega)
  have r1 : st₁.regs 1 = x := hr₁ 1 (by omega)
  have r2 : st₁.regs 2 = y := hr₁ 2 (by omega)
  have r3 : st₁.regs 3 = ldBase := hr₁ 3 (by omega)
  have r4 : st₁.regs 4 = LB := hr₁ 4 (by omega)
  -- the blocks of the weighted depths are untouched by the writes to `dst`
  have hLd : ∀ (m : ℕ → ℕ), (∀ a, a < dst ∨ dst + LB ≤ a → m a = mem a) → ∀ z < n,
      Valid m (ldBase + z * LB) h LB ∧
        unsignedVal m (ldBase + z * LB) h LB = unsignedVal mem (ldBase + z * LB) h LB := by
    intro m hm z hz
    have := blk_end LB hz
    have hag : ∀ i < LB, m (ldBase + z * LB + i) = mem (ldBase + z * LB + i) :=
      fun i hi => hm _ (by omega)
    exact ⟨fun i hi => by rw [hag i hi]; exact hval z hz i hi, unsignedVal_congr hag⟩
  have hfr₁' : ∀ a, a < dst ∨ dst + LB ≤ a → st₁.mem a = mem a := fun a ha => hfr₁ a ha
  have hvd₁ : Valid st₁.mem dst h LB := fun j hj => by rw [hz₁ j hj]; exact hB0
  have hU₁ : unsignedVal st₁.mem dst h LB = 0 := unsignedVal_zero fun j hj => hz₁ j hj
  -- the four accumulations
  have hargsw : ∀ z < n, ldBase + z * LB < 2 ^ w := fun z hz => by
    have := blk_end LB hz; omega
  have step : ∀ (st : State) (z k neg : ℕ), z < n → neg ≤ 1 → k < base h →
      (∀ a, a < dst ∨ dst + LB ≤ a → st.mem a = mem a) → Valid st.mem dst h LB →
      (uAccContract w h).pre [dst, ldBase + z * LB, LB, k, neg] st.mem := by
    intro st z k neg hz hneg hk hm hv
    exact ⟨_, _, _, _, _, rfl, hneg, hk, hv, (hLd st.mem hm z hz).1,
      by have := blk_end LB hz; omega, by omega,
      by have := blk_end LB hz; omega⟩
  have hk1 : 1 < base h := by
    rw [base]; exact Nat.one_lt_two_pow (by omega)
  refine runs_seq_call_le (vs := [dst, ldBase + x * LB, LB, 1, 0]) hAcc
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    (step st₁ x 1 0 hx (by omega) hk1 hfr₁' hvd₁) ?_
  rintro v₂ mem₂ pos₂ ⟨d₂, a₂, L₂, k₂, n₂, heq₂, -, hfr₂, hv₂, hu₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  have hm₂ : ∀ a, a < dst ∨ dst + LB ≤ a → mem₂ a = mem a :=
    fun a ha => (hfr₂ a ha).trans (hfr₁' a ha)
  refine runs_seq_call_le (vs := [dst, ldBase + y * LB, LB, 1, 0]) hAcc
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    (step ⟨mem₂, _, _⟩ y 1 0 hy (by omega) hk1 hm₂ hv₂) ?_
  rintro v₃ mem₃ pos₃ ⟨d₃, a₃, L₃, k₃, n₃, heq₃, -, hfr₃, hv₃, hu₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  have hm₃ : ∀ a, a < dst ∨ dst + LB ≤ a → mem₃ a = mem a :=
    fun a ha => (hfr₃ a ha).trans (hm₂ a ha)
  refine runs_seq_call_le (vs := [dst, ldBase + l * LB, LB, 0, 1]) hAcc
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    (step ⟨mem₃, _, _⟩ l 0 1 hln (by omega) hB0 hm₃ hv₃) ?_
  rintro v₄ mem₄ pos₄ ⟨d₄, a₄, L₄, k₄, n₄, heq₄, -, hfr₄, hv₄, hu₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  have hm₄ : ∀ a, a < dst ∨ dst + LB ≤ a → mem₄ a = mem a :=
    fun a ha => (hfr₄ a ha).trans (hm₃ a ha)
  refine runs_seq_call_le (vs := [dst, ldBase + l * LB, LB, 0, 1]) hAcc
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    (step ⟨mem₄, _, _⟩ l 0 1 hln (by omega) hB0 hm₄ hv₄) ?_
  rintro v₅ mem₅ pos₅ ⟨d₅, a₅, L₅, k₅, n₅, heq₅, -, hfr₅, hv₅, hu₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  have hm₅ : ∀ a, a < dst ∨ dst + LB ≤ a → mem₅ a = mem a :=
    fun a ha => (hfr₅ a ha).trans (hm₄ a ha)
  refine runs_ret_le (v := l) (by eval_expr) ⟨dst, x, y, ldBase, LB, logCap, upPtr, depPtr,
    parPtr, rfl, hm₅, hv₅, ?_, fun n' tM' r' tl' hd' par' pe' dep' hR' hx' hy' hT' =>
      hlca x y logCap upPtr depPtr parPtr n' tM' r' tl' hd' par' pe' dep' rfl hR' hx' hy' hT'⟩ ?_
  · rw [hu₅, hu₄, hu₃, hu₂, hU₁]
    simp only [accTerm, if_pos rfl, if_neg (show (0 : ℕ) ≠ 1 by omega), one_mul, zero_add]
    rw [(hLd _ hfr₁' x hx).2, (hLd _ hm₂ y hy).2, (hLd _ hm₃ l hln).2, (hLd _ hm₄ l hln).2]
    rfl
  · simp only [treeDistContract, hargs, uAccContract, lcaContract, List.getD_cons_zero,
      List.getD_cons_succ, argsSize, Expr.size_const, Expr.size_reg, Expr.size_bin,
      Expr.size_load]
    omega

end

end MinCostFlow.LSF.Program
