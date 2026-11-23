module

public import MinCostFlow.LSF.Program.BinaryLift

/-!
# Binary lifting: the smallest edge on each jump

Besides the ancestor table `upV`, the aux block stores for each vertex index `i` and level `j` the
tree edge index `upMinIdx i j` that is first in the order `π` among the edges on the way from `i`
up `2^j` steps (`AuxAt`). Level `0` is the parent edge. Level `j + 1` joins the two halves: the
jump of `i` at level `j`, and the jump of its level-`j` ancestor `u` at level `j`. When `u` is the
root the second half is empty, so the first half is kept.

`liftMin` is this table as a function of the ancestor table. `upMinProc` fills it at
`minPtr + (i * logCap + j)`, level by level, in time `O(n · logCap)` (`upMin_meetsContract`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- The smallest edge index (in the order `piv`) on the jump of `i` at level `j`, given the
ancestor table `U` and the parent edges `pe`. -/
def liftMin (U : ℕ → ℕ → ℕ) (pe piv : ℕ → ℕ) (r : ℕ) : ℕ → ℕ → ℕ
  | i, 0 => pe i
  | i, j + 1 =>
    if U i j = r then liftMin U pe piv r i j
    else if piv (liftMin U pe piv r (U i j) j) < piv (liftMin U pe piv r i j) then
      liftMin U pe piv r (U i j) j
    else liftMin U pe piv r i j

/-- Every value of the table is a parent edge index. -/
lemma liftMin_mem {U : ℕ → ℕ → ℕ} {pe piv : ℕ → ℕ} {r n L : ℕ}
    (hU : ∀ i < n, ∀ j < L, U i j < n) : ∀ j, j < L → ∀ i < n, ∃ k < n,
      liftMin U pe piv r i j = pe k := by
  intro j
  induction j with
  | zero => intro _ i hi; exact ⟨i, hi, rfl⟩
  | succ j ih =>
    intro hj i hi
    simp only [liftMin]
    split_ifs
    · exact ih (by omega) i hi
    · exact ih (by omega) _ (hU i hi j (by omega))
    · exact ih (by omega) i hi

/-! ## The procedure -/

/-- Level `0`: `min[i * logCap] = pe[i]`, for `i` in register `8`. -/
def upMin0Body : Stmt :=
  .store (.bin .add (.reg 6) (.bin .mul (.reg 8) (.reg 1))) (.load (.bin .add (.reg 4) (.reg 8)))

/-- Level `j + 1` (register `7` is `j`) at `i` (register `8`). Registers: `9 = a`, `10 = u`,
`11 = c`, `12 = [u = r]`. -/
def upMinStepBody : Stmt :=
  .assign 9 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 8) (.reg 1)) (.reg 7)))) ;;
  .assign 10 (.load (.bin .add (.reg 3) (.bin .add (.bin .mul (.reg 8) (.reg 1)) (.reg 7)))) ;;
  .assign 11 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 10) (.reg 1)) (.reg 7)))) ;;
  .assign 12 (.bin .eq (.reg 10) (.reg 2)) ;;
  .cond (.reg 12)
    (.store (.bin .add (.reg 6) (.bin .add (.bin .add (.bin .mul (.reg 8) (.reg 1)) (.reg 7))
      (.const 1))) (.reg 9))
    (.cond (.bin .lt (.load (.bin .add (.reg 5) (.reg 11))) (.load (.bin .add (.reg 5) (.reg 9))))
      (.store (.bin .add (.reg 6) (.bin .add (.bin .add (.bin .mul (.reg 8) (.reg 1)) (.reg 7))
        (.const 1))) (.reg 11))
      (.store (.bin .add (.reg 6) (.bin .add (.bin .add (.bin .mul (.reg 8) (.reg 1)) (.reg 7))
        (.const 1))) (.reg 9)))

/-- Args: `[n, logCap, r, upPtr, pePtr, piPtr, minPtr]`. -/
def upMinProc : Stmt :=
  forRange 8 (.const 0) (.reg 0) upMin0Body ;;
  forRange 7 (.const 0) (.bin .sub (.reg 1) (.const 1))
    (forRange 8 (.const 0) (.reg 0) upMinStepBody) ;;
  .ret (.const 0)

lemma upMinProc_noRand : upMinProc.NoRand := by
  simp [upMinProc, upMin0Body, upMinStepBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `upMinProc`. The ancestor table, the parent edges and the order lie below
`minPtr`. -/
def upMinContract (w : ℕ) : Contract where
  pre args mem := ∃ (n logCap r upPtr pePtr piPtr minPtr : ℕ),
    args = [n, logCap, r, upPtr, pePtr, piPtr, minPtr] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ logCap ∧
    (∀ i < n, ∀ j < logCap, mem (upPtr + (i * logCap + j)) < n) ∧
    upPtr + n * logCap ≤ minPtr ∧ pePtr + n ≤ minPtr ∧
    (∀ i < n, piPtr + mem (pePtr + i) < minPtr) ∧ minPtr + n * logCap < 2 ^ w
  post args mem ret mem' := ∃ (n logCap r upPtr pePtr piPtr minPtr : ℕ),
    args = [n, logCap, r, upPtr, pePtr, piPtr, minPtr] ∧ ret = 0 ∧
    (∀ i < n, ∀ j < logCap,
      mem' (minPtr + (i * logCap + j)) =
        liftMin (fun i j => mem (upPtr + (i * logCap + j))) (fun x => mem (pePtr + x))
          (fun x => mem (piPtr + x)) r i j) ∧
    ∀ a, a < minPtr ∨ minPtr + n * logCap ≤ a → mem' a = mem a
  cost args _ := 100 * args.getD 0 0 * args.getD 1 0 + 40 * args.getD 1 0 + 40

/-! ## Proof -/

private lemma idx_lt' {i j n L : ℕ} (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  have : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right _ hi
  nlinarith

private lemma idx_inj' {a b c d L : ℕ} (hb : b < L) (hd : d < L) (h : a * L + b = c * L + d) :
    a = c ∧ b = d := by
  have hL : 0 < L := by omega
  have h1 : (a * L + b) / L = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hb, Nat.zero_add]
  have h2 : (c * L + d) / L = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hd, Nat.zero_add]
  have hac : a = c := by rw [← h1, ← h2, h]
  subst hac
  omega

/-- The argument registers `0, …, 6`. -/
def MinRegs (st : State) (n logCap r upPtr pePtr piPtr minPtr : ℕ) : Prop :=
  st.regs 0 = n ∧ st.regs 1 = logCap ∧ st.regs 2 = r ∧ st.regs 3 = upPtr ∧ st.regs 4 = pePtr ∧
    st.regs 5 = piPtr ∧ st.regs 6 = minPtr

lemma MinRegs.upd {st : State} {n logCap r upPtr pePtr piPtr minPtr : ℕ}
    (h : MinRegs st n logCap r upPtr pePtr piPtr minPtr) (q v : ℕ) (hq : 7 ≤ q) :
    MinRegs { st with regs := Function.update st.regs q v } n logCap r upPtr pePtr piPtr minPtr := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  simp only [MinRegs, Function.update_of_ne (show (0 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (1 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (2 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (3 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (4 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (5 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (6 : ℕ) ≠ q by omega)]
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

theorem upMin_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some upMinProc) :
    MeetsContract w p b (upMinContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, L, r, upPtr, pePtr, piPtr, minPtr, rfl, hw, hL, hU, hupl, hpel, hpil, hword⟩ := hpre
  have hnw : n < 2 ^ w := hwords n (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  set U : ℕ → ℕ → ℕ := fun i j => mem (upPtr + (i * L + j)) with hUdef
  set PE : ℕ → ℕ := fun x => mem (pePtr + x) with hPE
  set PI : ℕ → ℕ := fun x => mem (piPtr + x) with hPI
  have hUlt : ∀ i < n, ∀ j, j < L → U i j < n := hU
  let Frame : (ℕ → ℕ) → Prop := fun m => ∀ a, a < minPtr ∨ minPtr + n * L ≤ a → m a = mem a
  -- level `0`
  let Inv0 : ℕ → State → Prop := fun i st =>
    MinRegs st n L r upPtr pePtr piPtr minPtr ∧ st.regs 8 = i ∧ Frame st.mem ∧
    ∀ i' < i, st.mem (minPtr + (i' * L + 0)) = liftMin U PE PI r i' 0
  have hloop0 : Triple w p
      (fun st => st = startState [n, L, r, upPtr, pePtr, piPtr, minPtr] mem pos)
      (forRange 8 (.const 0) (.reg 0) upMin0Body) (normalPost (Inv0 n))
      (fun _ => n * (20 + Expr.size (.reg 0) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 0) + 5)) := by
    refine Triple.forRange_const 20 0 n (Nat.zero_le _) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, ⟨by simp [startState], by simp [startState], by simp [startState],
        by simp [startState], by simp [startState], by simp [startState], by simp [startState]⟩,
        by simp, fun _ _ => rfl, fun i hi => absurd hi (by omega)⟩
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h; have := h.1.1; eval_expr
    · intro i _ hi st ω' ⟨hR, h8, hfr, hdone⟩
      obtain ⟨r0, r1, r2, r3, r4, r5, r6⟩ := hR
      have hidx := idx_lt' (j := 0) hi hL
      have hPi : st.mem (pePtr + i) = PE i := hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      unfold upMin0Body
      refine runs_store_le (x := minPtr + i * L) (v := PE i) (by eval_expr) (by
        rw [← hPi]; eval_expr) ⟨⟨(MinRegs.upd ⟨r0, r1, r2, r3, r4, r5, r6⟩ 8 (i + 1) (by omega)),
          by simp, ?_, ?_⟩, h8⟩ ?_
      · intro a ha
        simp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro i' hi'
        simp only [Nat.add_zero]
        by_cases hii : i' = i
        · subst hii; rw [Function.update_self]; rfl
        · rw [Function.update_of_ne (by
            intro h
            have := idx_inj' (b := 0) (d := 0) (by omega) (by omega)
              (show i' * L + 0 = i * L + 0 by omega)
            omega)]
          simpa using hdone i' (by omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- levels `j + 1`
  let InvJ : ℕ → State → Prop := fun j st =>
    MinRegs st n L r upPtr pePtr piPtr minPtr ∧ st.regs 7 = j ∧ Frame st.mem ∧
    ∀ i' < n, ∀ j' ≤ j, st.mem (minPtr + (i' * L + j')) = liftMin U PE PI r i' j'
  let InvI : ℕ → ℕ → State → Prop := fun j i st =>
    MinRegs st n L r upPtr pePtr piPtr minPtr ∧ st.regs 7 = j ∧ st.regs 8 = i ∧ Frame st.mem ∧
    (∀ i' < n, ∀ j' ≤ j, st.mem (minPtr + (i' * L + j')) = liftMin U PE PI r i' j') ∧
    ∀ i' < i, st.mem (minPtr + (i' * L + (j + 1))) = liftMin U PE PI r i' (j + 1)
  have hinner : ∀ j, j < L - 1 →
      Triple w p (InvJ j) (forRange 8 (.const 0) (.reg 0) upMinStepBody)
      (normalPost fun st₁ =>
        InvJ (j + 1) { st₁ with regs := Function.update st₁.regs 7 (j + 1) } ∧ st₁.regs 7 = j)
      (fun _ => n * (80 + Expr.size (.reg 0) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 0) + 5)) := by
    intro j hj
    refine (Triple.forRange_const (Inv := InvI j) 80 0 n (Nat.zero_le _) hw1 (fun _ => hnw)
      ?_ ?_ ?_ ?_).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
    · rintro st ⟨hR, h7, hfr, hdone⟩
      exact ⟨by eval_expr, hR.upd 8 0 (by omega), by simpa using h7, by simp, hfr, hdone,
        fun i hi => absurd hi (by omega)⟩
    · intro i st _ _ h; exact h.2.2.1
    · intro i st _ _ h; have := h.1.1; eval_expr
    · intro i _ hi st ω' ⟨hR, h7, h8, hfr, hlev, hdone⟩
      obtain ⟨r0, r1, r2, r3, r4, r5, r6⟩ := hR
      have hjL : j < L := by omega
      have hj1 : j + 1 < L := by omega
      have hidx := idx_lt' (j := j) hi hjL
      have hidx1 := idx_lt' hi hj1
      have hu := hUlt i hi j hjL
      have hidx2 := idx_lt' (j := j) hu hjL
      -- the three reads
      set a := liftMin U PE PI r i j
      set u := U i j
      set c := liftMin U PE PI r u j
      have hva : st.mem (minPtr + (i * L + j)) = a := hlev i hi j le_rfl
      have hvu : st.mem (upPtr + (i * L + j)) = u := hfr _ (Or.inl (by omega))
      have hvc : st.mem (minPtr + (u * L + j)) = c := hlev _ hu j le_rfl
      obtain ⟨ka, hka, hka'⟩ := liftMin_mem (pe := PE) (piv := PI) (r := r) hU j hjL i hi
      obtain ⟨kc, hkc, hkc'⟩ := liftMin_mem (pe := PE) (piv := PI) (r := r) hU j hjL u hu
      have hpa : st.mem (piPtr + a) = PI a := hfr _ (Or.inl (by rw [show a = PE ka from hka']; exact hpil ka hka))
      have hpc : st.mem (piPtr + c) = PI c := hfr _ (Or.inl (by rw [show c = PE kc from hkc']; exact hpil kc hkc))
      have hpaw : piPtr + a < 2 ^ w := by
        have h2 : a = mem (pePtr + ka) := hka'
        have := hpil ka hka; omega
      have hpcw : piPtr + c < 2 ^ w := by
        have h2 : c = mem (pePtr + kc) := hkc'
        have := hpil kc hkc; omega
      clear hka' hkc'
      -- what a store of the right value gives
      have hpost : ∀ V, V = liftMin U PE PI r i (j + 1) →
          (∀ a', a' < minPtr ∨ minPtr + n * L ≤ a' →
            Function.update st.mem (minPtr + (i * L + j + 1)) V a' = mem a') ∧
          (∀ i' < n, ∀ j' ≤ j, Function.update st.mem (minPtr + (i * L + j + 1)) V
            (minPtr + (i' * L + j')) = liftMin U PE PI r i' j') ∧
          (∀ i' < i + 1, Function.update st.mem (minPtr + (i * L + j + 1)) V
            (minPtr + (i' * L + (j + 1))) = liftMin U PE PI r i' (j + 1)) := by
        intro V hV
        refine ⟨fun a' ha' => ?_, fun i' hi' j' hj' => ?_, fun i' hi' => ?_⟩
        · rw [Function.update_of_ne (by omega)]
          exact hfr a' ha'
        · rw [Function.update_of_ne (by
            intro h
            have := idx_inj' (show j' < L by omega) hj1
              (show i' * L + j' = i * L + (j + 1) by omega)
            omega)]
          exact hlev i' hi' j' hj'
        · by_cases hii : i' = i
          · subst hii
            rw [show minPtr + (i' * L + (j + 1)) = minPtr + (i' * L + j + 1) by ring,
              Function.update_self]
            exact hV
          · rw [Function.update_of_ne (by
              intro h
              have := idx_inj' hj1 hj1 (show i' * L + (j + 1) = i * L + (j + 1) by omega)
              omega)]
            exact hdone i' (by omega)
      refine runs_start_le ?_
      unfold upMinStepBody
      refine runs_seq_assign_le (v := a) (by rw [← hva]; eval_expr) ?_
      refine runs_seq_assign_le (v := u) (by rw [← hvu]; eval_expr) ?_
      refine runs_seq_assign_le (v := c) (by rw [← hvc]; eval_expr) ?_
      refine runs_seq_assign_le (v := if u = r then 1 else 0) (by eval_expr) ?_
      have hregs : ∀ (V : ℕ), MinRegs
          { st with regs := Function.update (Function.update (Function.update (Function.update
            (Function.update st.regs 9 a) 10 u) 11 c) 12 (if u = r then 1 else 0)) 8 (i + 1) }
          n L r upPtr pePtr piPtr minPtr := fun _ =>
        ((((MinRegs.upd ⟨r0, r1, r2, r3, r4, r5, r6⟩ 9 _ (by omega)).upd 10 _ (by omega)).upd
          11 _ (by omega)).upd 12 _ (by omega)).upd 8 (i + 1) (by omega)
      refine WordRAM.runs_cond_le (v := if u = r then 1 else 0) (by eval_expr) ?_ ?_
      · intro hne
        have hur : u = r := by by_contra h; simp [h] at hne
        obtain ⟨hA, hB, hC⟩ := hpost a (by
          show a = liftMin U PE PI r i (j + 1)
          simp only [liftMin]
          rw [if_pos hur])
        refine runs_store_le (x := minPtr + (i * L + j + 1)) (v := a) (by eval_expr)
          (by eval_expr) ⟨⟨hregs a, by simpa using h7, by simp, hA, hB, hC⟩, by simpa using h8⟩ ?_
        simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
      · intro hz
        have hur : u ≠ r := by intro h; simp [h] at hz
        refine WordRAM.runs_cond_le (v := if PI c < PI a then 1 else 0)
          (by rw [← hpa, ← hpc]; eval_expr) ?_ ?_
        · intro hne
          have hlt : PI c < PI a := by by_contra h; simp [h] at hne
          obtain ⟨hA, hB, hC⟩ := hpost c (by
            show c = liftMin U PE PI r i (j + 1)
            simp only [liftMin]
            rw [if_neg hur, if_pos hlt])
          refine runs_store_le (x := minPtr + (i * L + j + 1)) (v := c) (by eval_expr)
            (by eval_expr) ⟨⟨hregs c, by simpa using h7, by simp, hA, hB, hC⟩,
              by simpa using h8⟩ ?_
          simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
        · intro hz'
          have hlt : ¬ PI c < PI a := by intro h; simp [h] at hz'
          obtain ⟨hA, hB, hC⟩ := hpost a (by
            show a = liftMin U PE PI r i (j + 1)
            simp only [liftMin]
            rw [if_neg hur, if_neg hlt])
          refine runs_store_le (x := minPtr + (i * L + j + 1)) (v := a) (by eval_expr)
            (by eval_expr) ⟨⟨hregs a, by simpa using h7, by simp, hA, hB, hC⟩,
              by simpa using h8⟩ ?_
          simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
    · intro o st h
      cases o with
      | returned v => exact h
      | normal =>
        obtain ⟨hR, h7, -, hfr, hlev, hdone⟩ := h
        refine ⟨⟨hR.upd 7 _ (by omega), by simp, hfr, fun i' hi' j' hj' => ?_⟩, h7⟩
        rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
        · exact hlev i' hi' j' (by omega)
        · exact hdone i' hi'
  have hloop1 : Triple w p (fun st => MinRegs st n L r upPtr pePtr piPtr minPtr ∧ Frame st.mem ∧
        ∀ i' < n, ∀ j' ≤ 0, st.mem (minPtr + (i' * L + j')) = liftMin U PE PI r i' j')
      (forRange 7 (.const 0) (.bin .sub (.reg 1) (.const 1))
        (forRange 8 (.const 0) (.reg 0) upMinStepBody)) (normalPost (InvJ (L - 1)))
      (fun _ => (L - 1) * ((n * (80 + Expr.size (.reg 0) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 0) + 5)) + Expr.size (.bin .sub (.reg 1) (.const 1)) + 8) +
        (Expr.size (.const 0) + Expr.size (.bin .sub (.reg 1) (.const 1)) + 5)) := by
    refine Triple.forRange_const (Inv := InvJ) _ 0 (L - 1) (Nat.zero_le _) hw1
      (fun _ => by omega) ?_ ?_ ?_ (fun j _ hj => hinner j hj)
    · rintro st ⟨hR, hfr, hlev⟩
      exact ⟨by eval_expr, hR.upd 7 0 (by omega), by simp, hfr, hlev⟩
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have := h.1.2.1
      eval_expr
  -- the whole procedure
  refine runs_start_le ?_
  unfold upMinProc
  refine runs_seq_triple_le hloop0 rfl ?_
  rintro st₁ ⟨hR, -, hfr, hdone⟩
  refine runs_seq_triple_le hloop1 ⟨hR, hfr, fun i' hi' j' hj' => by
    have : j' = 0 := by omega
    subst this
    exact hdone i' hi'⟩ ?_
  rintro st₂ ⟨-, -, hfr2, hlev2⟩
  refine runs_ret_le (by eval_expr) ⟨n, L, r, upPtr, pePtr, piPtr, minPtr, rfl, rfl,
    fun i hi j hj => hlev2 i hi j (by omega), hfr2⟩ ?_
  simp only [upMinContract, Expr.size_const, Expr.size_reg, Expr.size_bin, List.getD_cons_zero,
    List.getD_cons_succ]
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith

end

end MinCostFlow.LSF.Program
