module

public import WordRAM.Logic
public import WordRAM.Tactic
public import Mathlib.Data.Nat.Log

/-!
# Union-find: the root of an element

The union-find structure is an array `UF` of parents on `0, …, n - 1`; an element is a root when
it is its own parent. A *depth* function `dep` is consistent with it (`UFCons`) when roots have
depth `0` and every other element is one deeper than its parent. Then `rt x`, the element reached
from `x` after `dep x` parent steps, is a root. `findP` walks up from `x` to `rt x`; its cost is
`O(dep x)`, and union by size keeps `2^(dep x) ≤ n` (`findP_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The depth `dep` is consistent with the parents `M (UF + x)`. -/
def UFCons (M : ℕ → ℕ) (UF n : ℕ) (dep : ℕ → ℕ) : Prop :=
  ∀ x < n, M (UF + x) < n ∧ (M (UF + x) = x ↔ dep x = 0) ∧
    (M (UF + x) ≠ x → dep x = dep (M (UF + x)) + 1)

/-- The root of `x`. -/
def rt (M : ℕ → ℕ) (UF : ℕ) (dep : ℕ → ℕ) (x : ℕ) : ℕ := (fun y => M (UF + y))^[dep x] x

section

variable {M : ℕ → ℕ} {UF n : ℕ} {dep : ℕ → ℕ}

theorem UFCons.iter_lt (h : UFCons M UF n dep) {x : ℕ} (hx : x < n) (i : ℕ) :
    (fun y => M (UF + y))^[i] x < n := by
  induction i with
  | zero => exact hx
  | succ i ih => rw [Function.iterate_succ_apply']; exact (h _ ih).1

theorem UFCons.rt_lt (h : UFCons M UF n dep) {x : ℕ} (hx : x < n) : rt M UF dep x < n :=
  h.iter_lt hx _

/-- Going up one step does not change the root. -/
theorem UFCons.rt_par (h : UFCons M UF n dep) {x : ℕ} (hx : x < n) (hne : M (UF + x) ≠ x) :
    rt M UF dep (M (UF + x)) = rt M UF dep x := by
  unfold rt
  rw [(h x hx).2.2 hne, Function.iterate_succ_apply]

theorem UFCons.rt_root (h : UFCons M UF n dep) {x : ℕ} (hx : x < n) (hr : M (UF + x) = x) :
    rt M UF dep x = x := by
  unfold rt; rw [((h x hx).2.1.mp hr)]; rfl

/-- The root is a root. -/
theorem UFCons.rt_is_root (h : UFCons M UF n dep) {x : ℕ} (hx : x < n) :
    M (UF + rt M UF dep x) = rt M UF dep x := by
  suffices ∀ d, ∀ x < n, dep x = d → M (UF + rt M UF dep x) = rt M UF dep x from this _ x hx rfl
  intro d
  induction d with
  | zero => intro x hx hd; unfold rt; rw [hd]; exact (h x hx).2.1.mpr hd
  | succ d ih =>
    intro x hx hd
    have hne : M (UF + x) ≠ x := fun e => by have := (h x hx).2.1.mp e; omega
    have hd' : dep (M (UF + x)) = d := by have := (h x hx).2.2 hne; omega
    rw [← h.rt_par hx hne]
    exact ih _ (h x hx).1 hd'

/-- The depth is determined by the parents. -/
theorem UFCons.unique {dep' : ℕ → ℕ} (h : UFCons M UF n dep) (h' : UFCons M UF n dep') {x : ℕ}
    (hx : x < n) : dep' x = dep x := by
  suffices ∀ d, ∀ x < n, dep x = d → dep' x = d from this _ x hx rfl
  intro d
  induction d with
  | zero => intro x hx hd; exact (h' x hx).2.1.mp ((h x hx).2.1.mpr hd)
  | succ d ih =>
    intro x hx hd
    have hne : M (UF + x) ≠ x := fun e => by have := (h x hx).2.1.mp e; omega
    have hd' : dep (M (UF + x)) = d := by have := (h x hx).2.2 hne; omega
    rw [(h' x hx).2.2 hne, ih _ (h x hx).1 hd']

theorem UFCons.rt_eq {dep' : ℕ → ℕ} (h : UFCons M UF n dep) (h' : UFCons M UF n dep') {x : ℕ}
    (hx : x < n) : rt M UF dep' x = rt M UF dep x := by
  unfold rt; rw [h.unique h' hx]

end

/-- `findP` with `args = [UF, x, n]`: the root of `x`. -/
def findP : Stmt :=
  .seq (.loop (.bin .sub (.const 1) (.bin .eq (.load (.bin .add (.reg 0) (.reg 1))) (.reg 1)))
    (.assign 1 (.load (.bin .add (.reg 0) (.reg 1)))))
  (.ret (.reg 1))

theorem findP_noRand : findP.NoRand := by simp [findP, Stmt.NoRand]

/-- The contract of `findP`. -/
def findC (w : ℕ) : Contract where
  pre args mem := ∃ UF x n dep, args = [UF, x, n] ∧ UFCons mem UF n dep ∧ x < n ∧
    2 ^ dep x ≤ n ∧ UF + n < 2 ^ w
  post args mem v mem' := mem' = mem ∧ ∀ dep, UFCons mem (args.getD 0 0) (args.getD 2 0) dep →
    args.getD 1 0 < args.getD 2 0 → v = rt mem (args.getD 0 0) dep (args.getD 1 0)
  cost args _ := 20 * (Nat.log 2 (args.getD 2 0) + 2)

theorem findP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [findP]) :
    MeetsContract w p b (findC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨UF, x, n, dep, rfl, hc, hx, hdep, hw⟩ := hpre
  have hproc : p.procs[b]? = some findP := hp 0 (by simp)
  clear hp
  have hdl : dep x ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hdep
  let I : State → Prop := fun st => st.regs 0 = UF ∧ st.mem = mem ∧ st.regs 1 < n ∧
    rt mem UF dep (st.regs 1) = rt mem UF dep x ∧ dep (st.regs 1) ≤ dep x
  have hloop := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .sub (.const 1) (.bin .eq (.load (.bin .add (.reg 0) (.reg 1))) (.reg 1)))
    (body := .assign 1 (.load (.bin .add (.reg 0) (.reg 1)))) (Inv := I)
    (Q := fun st => st.regs 0 = UF ∧ st.mem = mem ∧ st.regs 1 = rt mem UF dep x)
    (fun st => dep (st.regs 1))
    (fun st => 1 - (if st.mem (UF + st.regs 1) = st.regs 1 then 1 else 0)) 10
    (fun st hI => by
      obtain ⟨h0, hm, h1, -, -⟩ := hI
      have : st.mem (st.regs 0 + st.regs 1) < 2 ^ w := by
        rw [h0, hm]; have := (hc _ h1).1; omega
      eval_expr)
    (fun st hI hv => by
      obtain ⟨h0, hm, h1, hr, -⟩ := hI
      refine ⟨h0, hm, ?_⟩
      have hroot : st.mem (UF + st.regs 1) = st.regs 1 := by
        by_contra hne; simp [hne] at hv
      rw [← hr, hm] at *
      exact (hc.rt_root h1 hroot).symm)
    (fun st hI hv => by
      obtain ⟨h0, hm, h1, hr, hd⟩ := hI
      have hne : st.mem (UF + st.regs 1) ≠ st.regs 1 := by
        intro e; simp [e] at hv
      rw [hm] at hne
      intro st' ω' hst
      subst hst
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨by simp [h0], by simp [hm], ?_, ?_, ?_⟩, ?_⟩
        · simp [h0, hm]; exact (hc _ h1).1
        · simp [h0, hm]; rw [hc.rt_par h1 hne, hr]
        · simp [h0, hm]; have := (hc _ h1).2.2 hne; omega
        · simp [h0, hm]; have := (hc _ h1).2.2 hne; omega
      · wram_cost)
  refine ⟨findP, hproc, ?_⟩
  dsimp only [findP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨rfl, rfl, hx, rfl, le_rfl⟩ (fun st hQ => ?_)
  obtain ⟨h0, hm, h1⟩ := hQ
  refine runs_ret_le (by eval_expr) ⟨hm, fun dep' hc' _ => ?_⟩ ?_
  · show rt mem UF dep x = rt mem UF dep' x
    rw [hc.rt_eq hc' hx]
  · simp only [findC, List.getD_cons_zero, List.getD_cons_succ, Expr.size, startState]
    nlinarith

end MinCostFlow.LowStretch
