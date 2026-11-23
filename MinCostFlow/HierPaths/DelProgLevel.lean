module

public import MinCostFlow.HierPaths.DelProgEnum

/-!
# One whole level of the climb in the `Delete` program

`levelStmt` is one call of `levelStep` (`HierPaths/LossCounters.lean`): the counter update
`ctrStmt`, then, if the own count has just become the group size, the enumeration `enumStmt` of
the group, and then the change `Δ' = o' - o` to pass up, in register `12`.

`level_triple` says that afterwards the block holds the concrete state whose loss counters are
those of `levelStep`, the work list is extended by the new lost terminals of `levelStep`, the
registers that the climb keeps (`0`, `10`, `11`, `22`) are unchanged, and every other cell
outside the block and the new part of the work list is unchanged. The encoding does not hold the
step counters `updates` and `enumerated` of `LossState` (`encode_withLoss_congr`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

/-- The concrete state with new loss counters. -/
def HierConcrete.withLoss (x : HierConcrete) (L : LossState) : HierConcrete :=
  x.withSt { x.ms.st with loss := L }

theorem HierConcrete.encode_withLoss_congr (x : HierConcrete) {L L' : LossState}
    (h1 : L.own = L'.own) (h2 : L.sum = L'.sum) (h3 : L.failed = L'.failed)
    (h4 : L.glob = L'.glob) : (x.withLoss L).encode = (x.withLoss L').encode := by
  cases L; cases L'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- The test whether the group has just become full: `o' = sz` and `o ≠ sz`. -/
def fullTest : Expr :=
  .bin .and (.bin .eq (.reg 18) (.reg 15)) (.bin .sub (.const 1) (.bin .eq (.reg 17) (.reg 15)))

theorem fullTest_val (o o' sz : ℕ) :
    ((if o' = sz then 1 else 0) &&& (1 - if o = sz then 1 else 0) ≠ 0) ↔ (o' = sz ∧ o ≠ sz) := by
  by_cases h1 : o' = sz <;> by_cases h2 : o = sz <;> simp [h1, h2]

/-- One level of the climb. -/
def levelStmt : Stmt :=
  .seq ctrStmt (.seq (.cond fullTest enumStmt .nop) (.assign 12 (.bin .sub (.reg 18) (.reg 17))))

theorem levelStmt_noRand : levelStmt.NoRand := by
  simp [levelStmt, Stmt.NoRand, ctrStmt_noRand, enumStmt_noRand]

theorem HierConcrete.length_encode_setCtr (x : HierConcrete) {j X : ℕ} (hj : j ≤ x.depth)
    (hX : X < numGroups x.H.A.x x.H.A.b j) (o s : ℕ) :
    (x.setCtr j X o s).encode.length = x.encode.length := by
  let x1 := x.withSt { x.ms.st with loss := { x.ms.st.loss with
    own := setAt x.ms.st.loss.own j X o } }
  have h1 : x1.encode.length = x.encode.length := by
    show (layoutList x1.sections).length = (layoutList x.sections).length
    rw [x.sections_setOwn hj hX o, length_layoutList_set_set]
  have h2 : (x.setCtr j X o s).encode.length = x1.encode.length := by
    show (layoutList (x.setCtr j X o s).sections).length = (layoutList x1.sections).length
    rw [show (x.setCtr j X o s).sections = _ from x1.sections_setSum hj hX s,
      length_layoutList_set_set]
  rw [h2, h1]

/-- Charge enumeration only when the level becomes wholly lost. -/
def delLevelCost (x b u j Δ : ℕ) (L : LossState) : ℕ :=
  130 * (if levelCond x b u j Δ L then groupSize x b j else 0) + 600

theorem delLevelCost_le (x b u j Δ : ℕ) (L : LossState) :
    delLevelCost x b u j Δ L ≤ 130 * groupSize x b j + 600 := by
  unfold delLevelCost
  split <;> omega

theorem delLevelCost_eq (x b u j Δ : ℕ) (L : LossState) :
    delLevelCost x b u j Δ L =
      130 * ((levelStep x b u j Δ L).1.enumerated - L.enumerated) + 600 := by
  simp [delLevelCost, levelStep_enumerated]

/-- **One level of the climb.** -/
theorem level_triple {w : ℕ} {p : Program} (x : HierConcrete) {b u j Δ WB c0 : ℕ}
    {R : ℕ → ℕ} {L0 : List ℕ} {mem0 : ℕ → ℕ}
    (hR0 : R 0 = b) (hR10 : R 10 = u) (hR11 : R 11 = j) (hR12 : R 12 = Δ) (hR22 : R 22 = WB)
    (hR23 : R 23 = c0) (hL0 : L0.length = c0) (hnt : x.H.A.C.numTerm = 2 ^ x.H.A.x)
    (hu : u < 2 ^ x.H.A.x) (hj : j ≤ x.depth) (hb : b + x.encode.length < 2 ^ w)
    (hjb : j * x.H.A.b < 2 ^ w) (h2x : 2 ^ x.H.A.x < 2 ^ w)
    (hs4 : 4 * (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) < 2 ^ w)
    (hblk : b + x.encode.length ≤ WB) (hw : WB + c0 + groupSize x.H.A.x x.H.A.b j < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem WB L0 ∧
        s.mem = mem0) levelStmt
      (normalPost fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 11 = j ∧ s.regs 22 = WB ∧
        s.regs 12 = (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.2 ∧
        s.regs 23 = c0 + (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1.length ∧
        ListAt s.mem b (x.withLoss (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).1).encode ∧
        ListAt s.mem WB (L0 ++ (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1) ∧
        ∀ a, (a < b ∨ b + x.encode.length ≤ a) →
          (a < WB + c0 ∨ WB + c0 + (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1.length ≤ a) →
          s.mem a = mem0 a)
      (fun _ => delLevelCost x.H.A.x x.H.A.b u j Δ x.ms.st.loss) := by
  refine fun st₀ ω₀ hst₀ => ?_
  have hL0m : ListAt mem0 WB L0 := by rw [← hst₀.2.2.2]; exact hst₀.2.2.1
  revert st₀ ω₀ hst₀
  show Triple _ _ _ _ _ _
  have h25 := x.le_length_encode
  have hXlt : groupOf x.H.A.x x.H.A.b j u < numGroups x.H.A.x x.H.A.b j := groupOf_lt_numGroups hu
  have hmul := numGroups_mul_groupSize (x := x.H.A.x) (b := x.H.A.b) (j := j)
  have hXsz : groupOf x.H.A.x x.H.A.b j u * groupSize x.H.A.x x.H.A.b j +
      groupSize x.H.A.x x.H.A.b j ≤ 2 ^ x.H.A.x := by
    rw [← hmul, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hXlt
  -- the model step
  have hown := levelStep_own (x := x.H.A.x) (b := x.H.A.b) (u := u) (j := j) (Δ := Δ)
    (st := x.ms.st.loss)
  have hsum := levelStep_sum (x := x.H.A.x) (b := x.H.A.b) (u := u) (j := j) (Δ := Δ)
    (st := x.ms.st.loss)
  have hfail := levelStep_failed (x := x.H.A.x) (b := x.H.A.b) (u := u) (j := j) (Δ := Δ)
    (st := x.ms.st.loss)
  have hdelta := levelStep_delta (x := x.H.A.x) (b := x.H.A.b) (u := u) (j := j) (Δ := Δ)
    (st := x.ms.st.loss)
  have hstep : ∀ (c : Prop) [Decidable c], c = levelCond x.H.A.x x.H.A.b u j Δ x.ms.st.loss →
      ((levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).1.glob = if c then
        enumSet x.ms.st.loss.glob
          (groupOf x.H.A.x x.H.A.b j u * groupSize x.H.A.x x.H.A.b j)
          (groupOf x.H.A.x x.H.A.b j u * groupSize x.H.A.x x.H.A.b j +
            groupSize x.H.A.x x.H.A.b j) else x.ms.st.loss.glob) ∧
      (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1 = if c then
        enumOut x.ms.st.loss.glob
          (groupOf x.H.A.x x.H.A.b j u * groupSize x.H.A.x x.H.A.b j)
          (groupOf x.H.A.x x.H.A.b j u * groupSize x.H.A.x x.H.A.b j +
            groupSize x.H.A.x x.H.A.b j) else [] := by
    intro c _ hc
    subst hc
    have he := enumerate_eq_enum
      ⟨setAt x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)
        (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)),
       setAt x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u)
        (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ), x.ms.st.loss.failed,
       x.ms.st.loss.glob, x.ms.st.loss.updates + 1, x.ms.st.loss.enumerated⟩
      x.H.A.x x.H.A.b j (groupOf x.H.A.x x.H.A.b j u)
    unfold levelStep; dsimp only
    split_ifs with h
    · exact ⟨he.1, he.2⟩
    · exact ⟨rfl, rfl⟩
  have t0 := ctr_triple (w := w) (p := p) x (mem0 := mem0) hR0 hR10 hR11 hR12 hu hj hb hjb h2x
    hs4
  obtain ⟨CR, hCR⟩ : ∃ CR, CR = ctrRegs R (x.H.A.x - j * x.H.A.b) (groupOf x.H.A.x x.H.A.b j u) (groupSize x.H.A.x x.H.A.b j) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) := ⟨_, rfl⟩
  rw [← hCR] at t0
  have cr : ∀ r, r < 13 ∨ 18 < r → CR r = R r := by
    intro r hr; rw [hCR]; simp only [ctrRegs, Function.update_apply]
    split_ifs <;> first | rfl | omega
  have cr14 : CR 14 = (groupOf x.H.A.x x.H.A.b j u) := by rw [hCR]; simp [ctrRegs]
  have cr15 : CR 15 = (groupSize x.H.A.x x.H.A.b j) := by rw [hCR]; simp [ctrRegs]
  have cr17 : CR 17 = (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) := by rw [hCR]; simp [ctrRegs]
  have cr18 : CR 18 = (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) := by rw [hCR]; simp [ctrRegs]
  set x1 := x.setCtr j (groupOf x.H.A.x x.H.A.b j u) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) with hx1
  have hlen1 : x1.encode.length = x.encode.length := x.length_encode_setCtr hj hXlt _ _
  let Fr0 : (ℕ → ℕ) → Prop := fun m => ∀ a, (a < b ∨ b + x.encode.length ≤ a) → m a = mem0 a
  let Q1 : State → Prop := fun s => s.regs = CR ∧ ListAt s.mem b x1.encode ∧
    ListAt s.mem WB L0 ∧ Fr0 s.mem
  let FrF : (ℕ → ℕ) → Prop := fun m => ∀ a, (a < b ∨ b + x.encode.length ≤ a) →
    (a < WB + c0 ∨ WB + c0 + (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1.length ≤ a) → m a = mem0 a
  let Q2 : State → Prop := fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 11 = j ∧
    s.regs 22 = WB ∧ s.regs 17 = (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) ∧ s.regs 18 = (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) ∧ s.regs 23 = c0 + (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1.length ∧
    ListAt s.mem b (x.withLoss (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).1).encode ∧ ListAt s.mem WB (L0 ++ (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1) ∧ FrF s.mem
  -- after the counters
  have t0' : Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem WB L0 ∧
      s.mem = mem0) ctrStmt (normalPost Q1) (fun _ => 400) := by
    refine t0.conseq (fun s h => ⟨h.1, h.2.1, fun a _ => by rw [h.2.2.2]⟩) (fun o s h => ?_)
      (fun _ _ => le_refl _)
    · cases o with
      | returned => exact h.elim
      | normal =>
        refine ⟨h.1, h.2.1, ?_, h.2.2⟩
        exact listAt_congr (fun k _ => (h.2.2 (WB + k) (Or.inr (by omega))).symm) hL0m
  have hx1L : x1 = x.withLoss { x.ms.st.loss with own := setAt x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)), sum := setAt x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ) } := rfl
  have hev : ∀ s, Q1 s → fullTest.eval w s =
      some ((if (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0) &&& (1 - if (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0)) := by
    intro s hs
    unfold fullTest
    exact Expr.eval_and (Expr.eval_eq_op (Expr.eval_reg_of_eq (by rw [hs.1, cr18]))
      (Expr.eval_reg_of_eq (by rw [hs.1, cr15])) (by omega))
      (Expr.eval_sub (Expr.eval_const (by omega)) (Expr.eval_eq_op
        (Expr.eval_reg_of_eq (by rw [hs.1, cr17])) (Expr.eval_reg_of_eq (by rw [hs.1, cr15]))
        (by omega)) (by omega)) (by split_ifs <;> omega)
  have tB : Triple w p Q1 (.cond fullTest enumStmt .nop) (normalPost Q2)
      (fun _ => 130 * (if levelCond x.H.A.x x.H.A.b u j Δ x.ms.st.loss then groupSize x.H.A.x x.H.A.b j else 0) + 150) := by
    by_cases hc : (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (groupSize x.H.A.x x.H.A.b j) ∧ (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) ≠ (groupSize x.H.A.x x.H.A.b j)
    · have hval := (fullTest_val (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) (groupSize x.H.A.x x.H.A.b j)).mpr hc
      have hst := hstep _ rfl
      have hc' : levelCond x.H.A.x x.H.A.b u j Δ x.ms.st.loss := hc
      rw [if_pos hc', if_pos hc'] at hst
      obtain ⟨hglob, hout⟩ := hst
      have TT : Triple w p (fun s => Q1 s ∧
          ((if (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0) &&& (1 - if (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0)) ≠ 0) enumStmt
          (normalPost Q2) (fun _ => 130 * (groupSize x.H.A.x x.H.A.b j) + 30) := by
        intro st ω ⟨hq, _⟩
        have tA := triple_assign_exact (w := w) (p := p) (R := CR) (M := fun m => m = st.mem)
          (r := 21) (e := .bin .add (.bin .mul (.reg 14) (.reg 15)) (.reg 15)) (v := ((groupOf x.H.A.x x.H.A.b j u) * (groupSize x.H.A.x x.H.A.b j) + (groupSize x.H.A.x x.H.A.b j)))
          fun s hs _ => Expr.eval_add (Expr.eval_mul (Expr.eval_reg_of_eq (by rw [hs, cr14]))
            (Expr.eval_reg_of_eq (by rw [hs, cr15])) (by omega))
            (Expr.eval_reg_of_eq (by rw [hs, cr15])) (by omega)
        have tL := enumLoop_triple (w := w) (p := p) x1 (b := b) (WB := WB) (X := (groupOf x.H.A.x x.H.A.b j u)) (sz := (groupSize x.H.A.x x.H.A.b j))
          (c0 := c0) (R := Function.update CR 21 ((groupOf x.H.A.x x.H.A.b j u) * (groupSize x.H.A.x x.H.A.b j) + (groupSize x.H.A.x x.H.A.b j))) (L0 := L0) (mem0 := st.mem)
          (by rw [Function.update_of_ne (by norm_num), cr 0 (by omega), hR0])
          (by rw [Function.update_of_ne (by norm_num), cr14])
          (by rw [Function.update_of_ne (by norm_num), cr15]) (by simp)
          (by rw [Function.update_of_ne (by norm_num), cr 22 (by omega), hR22])
          (by rw [Function.update_of_ne (by norm_num), cr 23 (by omega), hR23]) hL0
          (by show _ ≤ x.H.A.C.numTerm; rw [hnt]; exact hXsz) (by rw [hlen1]; exact hblk) hw
          (by omega)
        obtain ⟨o, st', c, hrun, hpost, hcost⟩ := (Triple.seq_normal tA (tL.weaken_pre
          fun s h => ⟨h.1, by rw [h.2]; exact hq.2.1, by rw [h.2]; exact hq.2.2.1, h.2⟩)
          (fun _ _ _ _ => le_refl _)) st ω ⟨hq.1, rfl⟩
        refine ⟨o, st', c, hrun, ?_, ?_⟩
        · cases o with
          | returned => exact hpost.elim
          | normal =>
            obtain ⟨_, hR', h23, hblock, hwl, hfr⟩ := hpost
            have rr : ∀ r, r ≠ 20 → r ≠ 23 → r ≠ 24 → r ≠ 21 → st'.regs r = CR r := by
              intro r h1 h2 h3 h4; rw [hR' r h1 h2 h3, Function.update_of_ne h4]
            refine ⟨by rw [rr 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
                cr 0 (by omega), hR0],
              by rw [rr 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
                cr 10 (by omega), hR10],
              by rw [rr 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
                cr 11 (by omega), hR11],
              by rw [rr 22 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
                cr 22 (by omega), hR22],
              by rw [rr 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num), cr17],
              by rw [rr 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num), cr18],
              by rw [h23, hout]; rfl, ?_, by rw [hout]; exact hwl, ?_⟩
            · have e : (x1.withGlob (enumSet x1.ms.st.loss.glob ((groupOf x.H.A.x x.H.A.b j u) * (groupSize x.H.A.x x.H.A.b j)) ((groupOf x.H.A.x x.H.A.b j u) * (groupSize x.H.A.x x.H.A.b j) + (groupSize x.H.A.x x.H.A.b j)))).encode =
                  (x.withLoss (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).1).encode := by
                show (x.withLoss { x.ms.st.loss with own := setAt x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)), sum := setAt x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ), glob := enumSet x.ms.st.loss.glob ((groupOf x.H.A.x x.H.A.b j u) * (groupSize x.H.A.x x.H.A.b j)) ((groupOf x.H.A.x x.H.A.b j u) * (groupSize x.H.A.x x.H.A.b j) + (groupSize x.H.A.x x.H.A.b j)) }).encode = _
                exact x.encode_withLoss_congr hown.symm hsum.symm hfail.symm hglob.symm
              rw [← e]; exact hblock
            · intro a h1 h2
              rw [hfr a (by rw [hlen1]; exact h1) (by show _ ∨ _ ≤ _; rw [show x1.ms.st.loss.glob = x.ms.st.loss.glob from rfl, ← hout]; exact h2)]
              exact hq.2.2.2 a h1
        · simp [Expr.size] at hcost ⊢; omega
      refine (Triple.cond (val := fun _ => (if (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0) &&&
          (1 - if (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0)) hev TT (fun s ω h => absurd h.2 hval)
          (T_f := fun _ => 0)).mono_cost (fun _ _ => ?_)
      rw [ite_eq_left hc']
      simp [hval, fullTest, Expr.size] <;> omega
    · have hval : ((if (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0) &&& (1 - if (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0)) = 0 := by
        by_contra h; exact hc ((fullTest_val (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) (groupSize x.H.A.x x.H.A.b j)).mp h)
      have hst := hstep _ rfl
      have hc' : ¬ levelCond x.H.A.x x.H.A.b u j Δ x.ms.st.loss := hc
      rw [if_neg hc', if_neg hc'] at hst
      obtain ⟨hglob, hout⟩ := hst
      refine (Triple.cond (val := fun _ => (if (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0) &&&
          (1 - if (x.ms.st.loss.own j (groupOf x.H.A.x x.H.A.b j u)) = (groupSize x.H.A.x x.H.A.b j) then 1 else 0)) hev (fun s ω h => absurd hval h.2) (T_t := fun _ => 0)
          (Triple.nop fun s hs => ?_)).mono_cost (fun _ _ => ?_)
      · obtain ⟨⟨hr, hblock, hwl, hfr⟩, _⟩ := hs
        refine ⟨by rw [hr, cr 0 (by omega), hR0], by rw [hr, cr 10 (by omega), hR10],
          by rw [hr, cr 11 (by omega), hR11], by rw [hr, cr 22 (by omega), hR22],
          by rw [hr, cr17], by rw [hr, cr18], by rw [hr, cr 23 (by omega), hR23, hout]; rfl,
          ?_, by rw [hout, List.append_nil]; exact hwl, fun a h1 _ => hfr a h1⟩
        have e : x1.encode = (x.withLoss (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).1).encode := by
          rw [hx1L]
          exact x.encode_withLoss_congr hown.symm hsum.symm hfail.symm hglob.symm
        rw [← e]; exact hblock
      · simp [hval, hc', fullTest, Expr.size] <;> omega
  have tC : Triple w p Q2 (.assign 12 (.bin .sub (.reg 18) (.reg 17)))
      (normalPost fun s => s.regs 0 = b ∧ s.regs 10 = u ∧ s.regs 11 = j ∧ s.regs 22 = WB ∧
        s.regs 12 = (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.2 ∧ s.regs 23 = c0 + (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1.length ∧
        ListAt s.mem b (x.withLoss (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).1).encode ∧ ListAt s.mem WB (L0 ++ (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.1) ∧ FrF s.mem)
      (fun _ => 4) := by
    refine Triple.assign (val := fun _ => (levelStep x.H.A.x x.H.A.b u j Δ x.ms.st.loss).2.2) (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨_, _, _, _, h17, h18, _⟩ := hs
      rw [hdelta]
      exact Expr.eval_sub (Expr.eval_reg_of_eq h18) (Expr.eval_reg_of_eq h17) (by
        have : (newOwn x.H.A.x x.H.A.b j (x.ms.st.loss.sum j (groupOf x.H.A.x x.H.A.b j u) + Δ)) ≤ 2 ^ x.H.A.x := by
          unfold newOwn; split_ifs <;> omega
        omega)
    · obtain ⟨h0, h10, h11, h22, _, _, h23, hblock, hwl, hfr⟩ := hs
      exact ⟨by simpa [Function.update_apply] using h0, by simpa [Function.update_apply] using h10,
        by simpa [Function.update_apply] using h11, by simpa [Function.update_apply] using h22,
        by simp, by simpa [Function.update_apply] using h23, hblock, hwl, hfr⟩
  exact (Triple.seq_normal t0' (Triple.seq_normal tB tC (fun _ _ _ _ => le_refl _))
    (fun _ _ _ _ => by unfold delLevelCost; omega))

end MinCostFlow.HierPaths

end
