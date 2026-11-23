module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Two loops of the preprocessing: a table and a filter

Several steps of the preprocessing fill an array by one loop over `i < M`. This file proves two
such loops once, for any expression.

* `tabP e` writes `e` to `DST + i` for every `i < M` (`tabP_spec`). The expression may read
  any cell outside the written range, so its value is a function `F` of the memory at the start.
* `filtP c e s` keeps the indices `i < M` for which `c` is not `0`. It writes `e` for the `j`-th
  kept index to `DST + s j` and returns the number of kept indices (`filtP_spec`). Every other
  cell keeps its value.

Both take `args = M :: DST :: rest` with at most `15` arguments; the loop counter is register
`15`, and `filtP` counts in register `16`. The cost is linear in `M`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### The table loop -/

/-- The body of `tabP e`: `DST[i] := e`. -/
def tabB (e : Expr) : Stmt := .store (.bin .add (.reg 1) (.reg 15)) e

/-- `tabP e` with `args = M :: DST :: rest`. -/
def tabP (e : Expr) : Stmt := .seq (forRange 15 (.const 0) (.reg 0) (tabB e)) (.ret (.const 0))

theorem tabP_noRand (e : Expr) : (tabP e).NoRand := by
  simp [tabP, tabB, forRange, forUp, Stmt.NoRand]

/-- The contract of `tabP e`: `F args mem i` is the value of `e` at step `i`. -/
def tabC (w : ℕ) (e : Expr) (Pre : List ℕ → (ℕ → ℕ) → Prop)
    (F : List ℕ → (ℕ → ℕ) → ℕ → ℕ) : Contract where
  pre args mem := Pre args mem ∧ args.length ≤ 15 ∧ args.getD 1 0 + args.getD 0 0 + 1 < 2 ^ w
  post args mem _ mem' := (∀ i < args.getD 0 0, mem' (args.getD 1 0 + i) = F args mem i) ∧
    ∀ a, (a < args.getD 1 0 ∨ args.getD 1 0 + args.getD 0 0 ≤ a) → mem' a = mem a
  cost args _ := args.getD 0 0 * (e.size + 20) + 20

/-- The registers of a state of a loop: the arguments, and the counter `i` in register `15`. -/
def LoopRegs (args : List ℕ) (st : State) : Prop := ∀ r < 15, st.regs r = args.getD r 0

theorem LoopRegs.upd {args : List ℕ} {st : State} (h : LoopRegs args st) {r : ℕ} (hr : 15 ≤ r)
    (v : ℕ) : LoopRegs args { st with regs := Function.update st.regs r v } := by
  intro r' hr'
  show Function.update st.regs r v r' = _
  rw [Function.update_of_ne (by omega)]
  exact h r' hr'

theorem LoopRegs.mem {args : List ℕ} {st : State} (h : LoopRegs args st) (M : ℕ → ℕ) :
    LoopRegs args { st with mem := M } := h

theorem LoopRegs.start {args : List ℕ} (mem : ℕ → ℕ) (pos : ℕ) :
    LoopRegs args (startState args mem pos) := fun _ _ => rfl

theorem startState_regs_ge {args : List ℕ} {mem : ℕ → ℕ} {pos r : ℕ} (h : args.length ≤ r) :
    (startState args mem pos).regs r = 0 := by
  simp [startState, List.getElem?_eq_none h]

/-- **The table loop.** If `e` evaluates to `F args mem i` at step `i` whenever the cells outside
the written range hold their first values, then `tabP e` meets `tabC`. -/
theorem tabP_spec {w : ℕ} {p : Program} {b : ℕ} {e : Expr} {Pre : List ℕ → (ℕ → ℕ) → Prop}
    {F : List ℕ → (ℕ → ℕ) → ℕ → ℕ} (hp : p.HasAt b [tabP e])
    (hE : ∀ args mem, Pre args mem → ∀ st : State, LoopRegs args st →
      st.regs 15 < args.getD 0 0 →
      (∀ a, (a < args.getD 1 0 ∨ args.getD 1 0 + args.getD 0 0 ≤ a) → st.mem a = mem a) →
      e.eval w st = some (F args mem (st.regs 15))) :
    MeetsContract w p b (tabC w e Pre F) := by
  intro args mem pos ω _ ⟨hpre, hlen, hbd⟩
  have hproc : p.procs[b]? = some (tabP e) := hp 0 (by simp)
  set M := args.getD 0 0 with hM
  set D := args.getD 1 0 with hD
  have hw1 : 1 < 2 ^ w := by omega
  let I : ℕ → State → Prop := fun i st => LoopRegs args st ∧ st.regs 15 = i ∧
    (∀ i' < i, st.mem (D + i') = F args mem i') ∧ ∀ a, (a < D ∨ D + i ≤ a) → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := tabB e) (P := fun st => LoopRegs args st ∧ st.mem = mem) (Inv := I) (e.size + 4) 0 M
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨Expr.eval_const (by omega), hr.upd le_rfl 0, by simp,
      fun _ h => absurd h (by omega), fun a _ => by simp [hm]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by simp [Expr.eval, hI.1 0 (by omega), hM])
    (fun i _ hi st ω hI => by
      obtain ⟨hR, h15, hdone, hfr⟩ := hI
      have he := hE args mem hpre st hR (by rw [h15]; exact hi)
        (fun a ha => hfr a (by rcases ha with ha | ha <;> [left; right] <;> omega))
      rw [h15] at he
      have ha : (Expr.bin .add (.reg 1) (.reg 15)).eval w st = some (D + i) := by
        have : D + i < 2 ^ w := by omega
        exact Expr.eval_add (Expr.eval_reg_of_eq (hR 1 (by omega))) (Expr.eval_reg_of_eq h15) this
      refine runs_start_le (runs_store_le ha he ?_ (by simp [Expr.size]; omega))
      refine ⟨⟨hR.mem _ |>.upd le_rfl _, by simp, fun i' hi' => ?_, fun a ha' => ?_⟩, h15⟩
      · dsimp only
        by_cases h : i' = i
        · subst h; simp
        · rw [Function.update_of_ne (by omega)]; exact hdone i' (by omega)
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a (by omega))
  refine ⟨tabP e, hproc, ?_⟩
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨LoopRegs.start mem pos, rfl⟩ (fun st hI => ?_)
  obtain ⟨-, -, hdone, hfr⟩ := hI
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨fun i hi => hdone i hi, fun a ha => hfr a ha⟩ ?_
  simp only [Expr.size, tabC]
  have : 0 + (M - 0) * (e.size + 4 + 1 + 8) + (1 + 1 + 5) + 1 + (1 + 1) ≤
      M * (e.size + 20) + 20 := by
    have : M * (e.size + 4 + 1 + 8) ≤ M * (e.size + 20) := Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.sub_zero]; omega
  exact this

/-! ### The filter loop -/

/-- The indices `i < M` with `C i ≠ 0`, in increasing order. -/
def kept (C : ℕ → ℕ) (M : ℕ) : List ℕ := (List.range M).filter fun i => C i ≠ 0

theorem kept_succ (C : ℕ → ℕ) (M : ℕ) :
    kept C (M + 1) = kept C M ++ (if C M ≠ 0 then [M] else []) := by
  unfold kept
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : C M = 0 <;> simp [h]

theorem kept_length_le (C : ℕ → ℕ) (M : ℕ) : (kept C M).length ≤ M := by
  unfold kept
  exact (List.length_filter_le _ _).trans (by simp)

theorem mem_kept {C : ℕ → ℕ} {M i : ℕ} : i ∈ kept C M ↔ i < M ∧ C i ≠ 0 := by
  simp [kept]

theorem kept_nodup (C : ℕ → ℕ) (M : ℕ) : (kept C M).Nodup := (List.nodup_range).filter _

/-- The body of `filtP c e s`: if `c` holds, `DST[s · k] := e` and `k := k + 1`. -/
def filtB (c e : Expr) (s : ℕ) : Stmt :=
  .cond c (.seq (.store (.bin .add (.reg 1) (.bin .mul (.const s) (.reg 16))) e)
    (.assign 16 (.bin .add (.reg 16) (.const 1)))) .nop

/-- `filtP c e s` with `args = M :: DST :: rest`. It returns the number of kept indices. -/
def filtP (c e : Expr) (s : ℕ) : Stmt :=
  .seq (.assign 16 (.const 0)) (.seq (forRange 15 (.const 0) (.reg 0) (filtB c e s))
    (.ret (.reg 16)))

theorem filtP_noRand (c e : Expr) (s : ℕ) : (filtP c e s).NoRand := by
  simp [filtP, filtB, forRange, forUp, Stmt.NoRand]

/-- The contract of `filtP c e s`: `C args mem i` is the value of the test `c` at step `i`, and
`F args mem i` the value of `e`. -/
def filtC (w : ℕ) (c e : Expr) (s : ℕ) (Pre : List ℕ → (ℕ → ℕ) → Prop)
    (C F : List ℕ → (ℕ → ℕ) → ℕ → ℕ) : Contract where
  pre args mem := Pre args mem ∧ args.length ≤ 15 ∧ 1 ≤ s ∧
    args.getD 1 0 + s * args.getD 0 0 + 1 < 2 ^ w
  post args mem v mem' :=
    v = (kept (C args mem) (args.getD 0 0)).length ∧
    (∀ j < (kept (C args mem) (args.getD 0 0)).length,
      mem' (args.getD 1 0 + s * j) = F args mem ((kept (C args mem) (args.getD 0 0)).getD j 0)) ∧
    ∀ a, (∀ j < (kept (C args mem) (args.getD 0 0)).length, a ≠ args.getD 1 0 + s * j) →
      mem' a = mem a
  cost args _ := args.getD 0 0 * (c.size + e.size + 30) + 30

/-- **The filter loop.** If at step `i` the test `c` evaluates to `C args mem i`, and `e` to
`F args mem i` when the test holds, whenever the cells outside the written range hold their first
values, then `filtP c e s` meets `filtC`. -/
theorem filtP_spec {w : ℕ} {p : Program} {b : ℕ} {c e : Expr} {s : ℕ}
    {Pre : List ℕ → (ℕ → ℕ) → Prop} {C F : List ℕ → (ℕ → ℕ) → ℕ → ℕ}
    (hp : p.HasAt b [filtP c e s])
    (hC : ∀ args mem, Pre args mem → ∀ st : State, LoopRegs args st →
      st.regs 15 < args.getD 0 0 →
      (∀ a, (a < args.getD 1 0 ∨ args.getD 1 0 + s * args.getD 0 0 ≤ a) → st.mem a = mem a) →
      c.eval w st = some (C args mem (st.regs 15)) ∧
        (C args mem (st.regs 15) ≠ 0 → e.eval w st = some (F args mem (st.regs 15)))) :
    MeetsContract w p b (filtC w c e s Pre C F) := by
  intro args mem pos ω _ ⟨hpre, hlen, hs, hbd⟩
  have hproc : p.procs[b]? = some (filtP c e s) := hp 0 (by simp)
  set M := args.getD 0 0 with hM
  set D := args.getD 1 0 with hD
  set K := C args mem with hK
  have hw1 : 1 < 2 ^ w := by omega
  have hsM : ∀ j < M, s * j < s * M := fun j hj => Nat.mul_lt_mul_of_pos_left hj (by omega)
  have hMs : M ≤ s * M := Nat.le_mul_of_pos_left M hs
  let I : ℕ → State → Prop := fun i st => LoopRegs args st ∧ st.regs 15 = i ∧
    st.regs 16 = (kept K i).length ∧
    (∀ j < (kept K i).length, st.mem (D + s * j) = F args mem ((kept K i).getD j 0)) ∧
    ∀ a, (∀ j < (kept K i).length, a ≠ D + s * j) → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := filtB c e s) (P := fun st => LoopRegs args st ∧ st.regs 16 = 0 ∧ st.mem = mem)
    (Inv := I) (c.size + e.size + 12) 0 M (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, h16, hm⟩ => ⟨Expr.eval_const (by omega), hr.upd le_rfl 0, by simp,
      by simp [h16, kept], fun _ h => absurd h (by simp [kept]), fun a _ => by simp [hm]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by simp [Expr.eval, hI.1 0 (by omega), hM])
    (fun i _ hi st ω hI => by
      obtain ⟨hR, h15, h16, hdone, hfr⟩ := hI
      have hkl := kept_length_le K i
      have hout : ∀ a, (a < D ∨ D + s * M ≤ a) → st.mem a = mem a := fun a ha =>
        hfr a fun j hj => by have := hsM j (by omega); omega
      obtain ⟨hc, he⟩ := hC args mem hpre st hR (by rw [h15]; exact hi) hout
      rw [h15] at hc he
      refine runs_start_le (runs_cond_le hc (fun hv => ?_) (fun hv => ?_))
      · -- the index is kept
        have he' := he hv
        have hsl : s * (kept K i).length < s * M := hsM _ (by omega)
        have hs1 : s ≤ s * M := Nat.le_mul_of_pos_right s (by omega)
        have hsl' : s * (kept K i).length < 2 ^ w := by omega
        have ha : (Expr.bin .add (.reg 1) (.bin .mul (.const s) (.reg 16))).eval w st =
            some (D + s * (kept K i).length) :=
          Expr.eval_add (Expr.eval_reg_of_eq (hR 1 (by omega)))
            (Expr.eval_bin (op := .mul) (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h16)
              (by simpa using hsl')) (by omega)
        refine runs_seq_store_le ha he' (runs_assign_le (v := (kept K i).length + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h16])) (Expr.eval_const (by omega))
            (by omega)) ?_ (by simp [Expr.size]; omega))
        have hks : kept K (i + 1) = kept K i ++ [i] := by rw [kept_succ]; simp [hK, hv]
        refine ⟨⟨(hR.mem _).upd (by omega) _ |>.upd le_rfl _, by simp, by simp [hks], ?_, ?_⟩,
          by simp [h15]⟩
        · intro j hj
          rw [hks, List.length_append, List.length_singleton] at hj
          dsimp only
          rw [hks]
          by_cases hjl : j = (kept K i).length
          · subst hjl; simp
          · have hj' : j < (kept K i).length := by omega
            have hne : D + s * j ≠ D + s * (kept K i).length := by
              have : s * j < s * (kept K i).length := Nat.mul_lt_mul_of_pos_left hj' (by omega)
              omega
            rw [Function.update_of_ne hne, hdone j hj', List.getD_append _ _ _ _ hj']
        · intro a ha
          rw [hks, List.length_append, List.length_singleton] at ha
          dsimp only
          rw [Function.update_of_ne (ha _ (by omega))]
          exact hfr a fun j hj => ha j (by omega)
      · -- the index is not kept
        have hks : kept K (i + 1) = kept K i := by rw [kept_succ]; simp [hK, hv]
        refine runs_nop_le ⟨⟨hR.upd le_rfl _, by simp, ?_, ?_, ?_⟩, h15⟩ (by simp; omega)
        · rw [hks]; simp [h16]
        · rw [hks]; exact hdone
        · rw [hks]; exact hfr)
  refine ⟨filtP c e s, hproc, ?_⟩
  refine runs_start_le (runs_seq_assign_le (Expr.eval_const (by omega)) ?_)
  refine runs_seq_triple_le hloop ⟨(LoopRegs.start mem pos).upd (by omega) _, by simp, rfl⟩
    (fun st hI => ?_)
  obtain ⟨-, -, h16, hdone, hfr⟩ := hI
  refine runs_ret_le (Expr.eval_reg_of_eq h16) ⟨rfl, hdone, hfr⟩ ?_
  simp only [Expr.size, filtC]
  have : M * (c.size + e.size + 12 + 1 + 8) ≤ M * (c.size + e.size + 30) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [← hM, Nat.sub_zero]
  omega

end MinCostFlow.LowStretch
