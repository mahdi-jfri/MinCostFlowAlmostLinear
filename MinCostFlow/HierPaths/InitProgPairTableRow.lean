module

public import MinCostFlow.HierPaths.InitProgConnDepth

/-!
# A row of the pair lookup table

At a fixed depth each table entry names a child and a position among
its siblings. The writer finds that sibling by quotient and remainder,
then computes the symmetric pair number.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The row at depth `j` of section 12. -/
def initPairTableRow (x b j : ℕ) : List ℕ :=
  let br := branching x b j
  tabList (numGroups x b (j + 1) * br) fun i =>
    pairIdxOf x b j (i / br) (i / br / br * br + i % br)

private theorem initPairTable_sibling_lt {x b j i : ℕ}
    (hi : i < numGroups x b (j + 1) * branching x b j) :
    i / branching x b j < numGroups x b (j + 1) ∧
      i / branching x b j / branching x b j * branching x b j + i % branching x b j <
        numGroups x b (j + 1) := by
  let br := branching x b j
  have hp : 0 < br := branching_pos
  have hc : i / br < numGroups x b (j + 1) := (Nat.div_lt_iff_lt_mul hp).mpr hi
  have hz : (i / br / br + 1) * br ≤ numGroups x b (j + 1) := by
    rw [initNumGroups_succ]
    apply Nat.mul_le_mul_right
    apply Nat.succ_le_of_lt
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [br, initNumGroups_succ] using hc)
  refine ⟨hc, lt_of_lt_of_le ?_ hz⟩
  rw [Nat.succ_mul]
  exact Nat.add_lt_add_left (Nat.mod_lt _ hp) _

/-- At a valid depth the symmetric number fits in the full pair table. -/
theorem initPairTable_pair_lt {x b j Y Z : ℕ} (hj : j < leafDepth x b)
    (hY : Y < 2 ^ x) : pairIdxOf x b j Y Z < numPairsOf x b := by
  unfold pairIdxOf numPairsOf
  have hm := (min_le_left _ Z).trans_lt hY
  calc
    _ < (j * 2 ^ x + min Y Z) * 2 ^ b + 2 ^ b :=
      Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _
    _ = (j * 2 ^ x + min Y Z + 1) * 2 ^ b := (Nat.succ_mul _ _).symm
    _ ≤ (leafDepth x b * 2 ^ x) * 2 ^ b := by
      apply Nat.mul_le_mul_right
      calc
        _ ≤ j * 2 ^ x + 2 ^ x := by omega
        _ = (j + 1) * 2 ^ x := (Nat.succ_mul _ _).symm
        _ ≤ leafDepth x b * 2 ^ x := Nat.mul_le_mul_right _ hj

/-- The loop index is register 7. Registers 3 and 4 hold the powers of two
and register 5 holds the number of siblings. -/
def initPairTableRowStep : Stmt :=
  .assign 8 (.bin .div (.reg 7) (.reg 5)) ;;
  .assign 9 (.bin .add (.bin .mul (.bin .div (.reg 8) (.reg 5)) (.reg 5))
    (.bin .mod (.reg 7) (.reg 5))) ;;
  .assign 10 (.bin .sub (.reg 8) (.bin .sub (.reg 8) (.reg 9))) ;;
  .assign 11 (.bin .add (.reg 9) (.bin .sub (.reg 8) (.reg 9))) ;;
  .store (.bin .add (.reg 0) (.reg 7))
    (.bin .add (.bin .mul (.bin .add (.bin .mul (.reg 2) (.reg 3)) (.reg 10)) (.reg 4))
      (.bin .mod (.reg 11) (.reg 4)))

/-- Arguments are destination, row length, depth, terminal count, branching
limit and number of siblings. -/
def initPairTableRowProc : Stmt :=
  forRange 7 (.const 0) (.reg 1) initPairTableRowStep ;;
  .ret (.bin .add (.reg 0) (.reg 1))

theorem initPairTableRowProc_noRand : initPairTableRowProc.NoRand := by
  simp [initPairTableRowProc, initPairTableRowStep, forRange, forUp, Stmt.NoRand]

/-- The procedure writes one whole row and preserves the other cells. -/
def initPairTableRowContract (w x b j : ℕ) : Contract where
  pre args _ := ∃ dst, args = [dst, (initPairTableRow x b j).length, j, 2 ^ x, 2 ^ b,
    branching x b j] ∧ j < leafDepth x b ∧ numPairsOf x b < 2 ^ w ∧
    dst + (initPairTableRow x b j).length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ dst, args = [dst, (initPairTableRow x b j).length,
    j, 2 ^ x, 2 ^ b, branching x b j] ∧ v = dst + (initPairTableRow x b j).length ∧
    ListAt mem' dst (initPairTableRow x b j) ∧
    ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := 70 * (initPairTableRow x b j).length + 20

private theorem initPairTableRowStep_triple {w x b j i dst : ℕ} {p : Program} {s : State}
    (hi : i < (initPairTableRow x b j).length) (hj : j < leafDepth x b)
    (hk : numPairsOf x b < 2 ^ w) (hd : dst + (initPairTableRow x b j).length < 2 ^ w)
    (r0 : s.regs 0 = dst) (r2 : s.regs 2 = j) (r3 : s.regs 3 = 2 ^ x)
    (r4 : s.regs 4 = 2 ^ b) (r5 : s.regs 5 = branching x b j) (r7 : s.regs 7 = i) :
    Triple w p (fun t => t = s) initPairTableRowStep
      (normalPost fun t =>
        (∀ r ≤ 7, t.regs r = s.regs r) ∧
          t.mem = Function.update s.mem (dst + i) ((initPairTableRow x b j)[i]'hi))
      (fun _ => 50) := by
  let br := branching x b j
  let Y := i / br
  let Z := Y / br * br + i % br
  have hi' : i < numGroups x b (j + 1) * branching x b j := by
    simpa [initPairTableRow] using hi
  obtain ⟨hY, hZ⟩ := initPairTable_sibling_lt hi'
  have hy := hY.trans_le (numGroups_le_pow (j + 1))
  have hz := hZ.trans_le (numGroups_le_pow (j + 1))
  have hk' := (initPairTable_pair_lt (Z := Z) hj hy).trans hk
  have hx : 2 ^ x < 2 ^ w := by
    apply lt_of_le_of_lt _ hk
    unfold numPairsOf
    exact (Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt hj)).trans
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hmin : Y - (Y - Z) = min Y Z := Nat.sub_sub_eq_min _ _
  have hmax : Z + (Y - Z) = max Y Z := by rw [Nat.add_comm, Nat.sub_add_eq_max]
  have hP : j * 2 ^ x ≤ (j * 2 ^ x + min Y Z) * 2 ^ b :=
    (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hQ : j * 2 ^ x + min Y Z ≤ (j * 2 ^ x + min Y Z) * 2 ^ b :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hB : (j * 2 ^ x + min Y Z) * 2 ^ b < 2 ^ w :=
    (Nat.le_add_right _ _).trans_lt hk'
  have hZmul : Y / br * br < 2 ^ w := (Nat.le_add_right _ _).trans_lt (hz.trans hx)
  have hMax : max Y Z < 2 ^ w := (max_lt hy hz).trans hx
  have hiw : i < 2 ^ w := by omega
  intro st ω hs
  subst st
  refine runs_start_le ?_
  unfold initPairTableRowStep
  refine runs_seq_assign_le (v := Y) (Expr.eval_div (Expr.eval_reg_of_eq r7)
    (Expr.eval_reg_of_eq r5) hiw) ?_
  refine runs_seq_assign_le (v := Z) (Expr.eval_add
    (Expr.eval_mul (Expr.eval_div (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq (by simpa using r5))
      (hy.trans hx)) (Expr.eval_reg_of_eq (by simpa using r5)) hZmul)
    (Expr.eval_mod (Expr.eval_reg_of_eq (by simpa using r7))
      (Expr.eval_reg_of_eq (by simpa using r5)) hiw) (hz.trans hx)) ?_
  refine runs_seq_assign_le (v := min Y Z) (Expr.eval_eq_of_eq
    (Expr.eval_sub (Expr.eval_reg_of_eq (v := Y) rfl)
      (Expr.eval_sub (Expr.eval_reg_of_eq (v := Y) rfl) (Expr.eval_reg_of_eq (v := Z) rfl)
        (hy.trans hx)) (hy.trans hx)) hmin) ?_
  refine runs_seq_assign_le (v := max Y Z) (Expr.eval_eq_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq (v := Z) rfl)
      (Expr.eval_sub (Expr.eval_reg_of_eq (v := Y) rfl) (Expr.eval_reg_of_eq (v := Z) rfl)
        (hy.trans hx)) (hmax ▸ hMax)) hmax) ?_
  refine runs_store_le (x := dst + i) (v := pairIdxOf x b j Y Z)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r0))
      (Expr.eval_reg_of_eq (by simpa using r7)) (by omega)) ?_ ?_ ?_
  · exact Expr.eval_add (Expr.eval_mul
      (Expr.eval_add (Expr.eval_mul (Expr.eval_reg_of_eq (by simpa using r2))
        (Expr.eval_reg_of_eq (by simpa using r3)) (hP.trans_lt hB))
        (Expr.eval_reg_of_eq rfl) (hQ.trans_lt hB))
      (Expr.eval_reg_of_eq (by simpa using r4)) hB)
      (Expr.eval_mod (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq (by simpa using r4)) hMax) hk'
  · refine ⟨fun r hr => ?_, ?_⟩
    · change Function.update (Function.update (Function.update (Function.update s.regs 8 Y)
        9 Z) 10 (min Y Z)) 11 (max Y Z) r = s.regs r
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · have he : (initPairTableRow x b j)[i]'hi = pairIdxOf x b j Y Z := by
        simp [initPairTableRow, tabList, Y, Z, br]
      rw [he]
  · simp [Expr.size]

theorem initPairTableRowProc_meetsContract {w x b j f : ℕ} {p : Program}
    (hp : p.procs[f]? = some initPairTableRowProc) :
    MeetsContract w p f (initPairTableRowContract w x b j) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨dst, rfl, hj, hk, hdst, h1⟩ := hpre
  let row := initPairTableRow x b j
  let len := row.length
  let initial := startState [dst, len, j, 2 ^ x, 2 ^ b, branching x b j] mem pos
  let Regs := fun (s : State) => s.regs 0 = dst ∧ s.regs 1 = len ∧ s.regs 2 = j ∧
    s.regs 3 = 2 ^ x ∧ s.regs 4 = 2 ^ b ∧ s.regs 5 = branching x b j
  let Inv := fun (i : ℕ) (s : State) => Regs s ∧ s.regs 7 = i ∧ i ≤ len ∧
    (∀ k < i, s.mem (dst + k) = row.getD k 0) ∧
    ∀ y, y < dst ∨ dst + i ≤ y → s.mem y = mem y
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 7) (hi := .reg 1)
    (lo := .const 0) (P := fun s => s = initial) (Inv := Inv) (body := initPairTableRowStep)
    50 0 len (Nat.zero_le _) h1 (fun _ => hw _ (by simp [len, row]))
    (fun s hs => by
      subst s
      exact ⟨Expr.eval_const (Nat.two_pow_pos w), ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
        by simp, Nat.zero_le _, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.1.2.1)
    (fun i _ hi => by
      intro s ω' ⟨⟨r0, r1, r2, r3, r4, r5⟩, r7, _, hwds, hf⟩
      obtain ⟨o, t, c, hr, ht, hc⟩ :=
        initPairTableRowStep_triple hi hj hk hdst r0 r2 r3 r4 r5 r7 s ω' rfl
      cases o with
      | returned => exact False.elim ht
      | normal =>
        obtain ⟨hregs, hm⟩ := ht
        refine ⟨.normal, t, c, hr, ⟨⟨?_, ?_, Nat.succ_le_of_lt hi, ?_, ?_⟩,
          (hregs 7 le_rfl).trans r7⟩, hc⟩
        · exact ⟨(hregs 0 (by decide)).trans r0, (hregs 1 (by decide)).trans r1,
            (hregs 2 (by decide)).trans r2, (hregs 3 (by decide)).trans r3,
            (hregs 4 (by decide)).trans r4, (hregs 5 (by decide)).trans r5⟩
        · simp
        · intro k hk'
          change t.mem (dst + k) = row.getD k 0
          rw [hm]
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk') with hlt | rfl
          · exact (Function.update_of_ne (by omega) _ _).trans (hwds k hlt)
          · exact (Function.update_self ..).trans (List.getD_eq_getElem _ _ hi).symm
        · intro y hy
          rw [hm]
          exact (Function.update_of_ne (by omega) _ _).trans (hf y (by omega)))
  refine runs_start_le ?_
  unfold initPairTableRowProc
  refine runs_seq_triple_le hloop rfl ?_
  intro s ⟨⟨r0, r1, _, _, _, _⟩, _, _, hwds, hf⟩
  refine runs_ret_le (v := dst + len)
    (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r1) hdst)
    ⟨dst, rfl, rfl, ?_, hf⟩ ?_
  · intro k hk'
    rw [← List.getD_eq_getElem _ _ hk']
    exact hwds k hk'
  · simp [initPairTableRowContract, Expr.size, len, row]
    omega

end MinCostFlow.HierPaths

end
