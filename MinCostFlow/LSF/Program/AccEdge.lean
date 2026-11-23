module

public import MinCostFlow.LSF.Program.UArith

/-!
# One edge of one level of the stretch sum

At level `i`, an edge with end indices `u` and `v` adds to its accumulator block the tree
distance of `u` and `v` when both have the same forest root (`ru = rv`), and otherwise the
distances of `u` to `ru` and of `v` to `rv`. These distances are read from blocks
(`duv` for the first case, `du` and `dv` for the second).

`accEdgeProc` does this with one or two calls of `uAccProc`, modulo the capacity
(`accLevelVal`). `accLevelVal_same` and `accLevelVal_ne` give the exact value when nothing
overflows.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- The value that `accEdgeProc` writes, modulo the capacity `c`. -/
def accLevelVal (c X D du dv ru rv : ℕ) : ℕ :=
  if ru = rv then (X + D) % c else ((X + du) % c + dv) % c

lemma accLevelVal_same {c X D du dv ru rv : ℕ} (h : ru = rv) (hfit : X + D < c) :
    accLevelVal c X D du dv ru rv = X + D := by
  rw [accLevelVal, if_pos h, Nat.mod_eq_of_lt hfit]

lemma accLevelVal_ne {c X D du dv ru rv : ℕ} (h : ru ≠ rv) (hfit : X + du + dv < c) :
    accLevelVal c X D du dv ru rv = X + du + dv := by
  rw [accLevelVal, if_neg h, Nat.mod_eq_of_lt (show X + du < c by omega),
    Nat.mod_eq_of_lt hfit]

/-- Args: `[d, duv, adu, adv, LB, ru, rv]`: the accumulator block, the block of the tree
distance of the ends, the blocks of the distances of the ends to their roots, the width and the
two roots. -/
def accEdgeProc (bAcc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 5) (.reg 6))
    (.call 7 bAcc [.reg 0, .reg 1, .reg 4, .const 1, .const 0] ;; .ret (.const 0))
    (.call 7 bAcc [.reg 0, .reg 2, .reg 4, .const 1, .const 0] ;;
     .call 7 bAcc [.reg 0, .reg 3, .reg 4, .const 1, .const 0] ;;
     .ret (.const 0))

lemma accEdgeProc_noRand (bAcc : ℕ) : (accEdgeProc bAcc).NoRand := by
  simp [accEdgeProc, Stmt.NoRand]

/-- A source block of `LB` limbs that does not meet the block `d`. -/
def SrcBlock (w h : ℕ) (mem : ℕ → ℕ) (d a LB : ℕ) : Prop :=
  Valid mem a h LB ∧ (a + LB ≤ d ∨ d + LB ≤ a) ∧ a + LB < 2 ^ w

lemma SrcBlock.of_frame {w h : ℕ} {mem mem' : ℕ → ℕ} {d a LB : ℕ} (hs : SrcBlock w h mem d a LB)
    (hfr : ∀ x, x < d ∨ d + LB ≤ x → mem' x = mem x) :
    SrcBlock w h mem' d a LB ∧ unsignedVal mem' a h LB = unsignedVal mem a h LB := by
  obtain ⟨hv, hd, hw⟩ := hs
  have hag : ∀ i < LB, mem' (a + i) = mem (a + i) := fun i hi => hfr _ (by omega)
  exact ⟨⟨fun i hi => by rw [hag i hi]; exact hv i hi, hd, hw⟩, unsignedVal_congr hag⟩

/-- The contract of `accEdgeProc`. -/
def accEdgeContract (w h : ℕ) : Contract where
  pre args mem := ∃ (d duv adu adv LB ru rv : ℕ),
    args = [d, duv, adu, adv, LB, ru, rv] ∧ Valid mem d h LB ∧ d + LB < 2 ^ w ∧
    SrcBlock w h mem d duv LB ∧ SrcBlock w h mem d adu LB ∧ SrcBlock w h mem d adv LB
  post args mem ret mem' := ∃ (d duv adu adv LB ru rv : ℕ),
    args = [d, duv, adu, adv, LB, ru, rv] ∧ ret = 0 ∧
    (∀ x, x < d ∨ d + LB ≤ x → mem' x = mem x) ∧ Valid mem' d h LB ∧
    unsignedVal mem' d h LB = accLevelVal (capacity h LB) (unsignedVal mem d h LB)
      (unsignedVal mem duv h LB) (unsignedVal mem adu h LB) (unsignedVal mem adv h LB) ru rv
  cost args _ := 150 * args.getD 4 0 + 100

theorem accEdge_meetsContract {w h : ℕ} {p : Program} {b bAcc : ℕ}
    (hAcc : MeetsContract w p bAcc (uAccContract w h)) (hh : 1 ≤ h) (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (accEdgeProc bAcc)) :
    MeetsContract w p b (accEdgeContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨d, duv, adu, adv, LB, ru, rv, rfl, hvd, hdw, hs0, hs1, hs2⟩ := hpre
  have hB0 : 0 < base h := base_pos h
  have hk1 : 1 < base h := by
    rw [base]; exact Nat.one_lt_two_pow (by omega)
  have hBw : base h < 2 ^ w := base_lt_word hw
  set args := [d, duv, adu, adv, LB, ru, rv] with hargs
  have hR : ∀ i < 7, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have r0 := hR 0 (by omega); have r1 := hR 1 (by omega); have r2 := hR 2 (by omega)
  have r3 := hR 3 (by omega); have r4 := hR 4 (by omega); have r5 := hR 5 (by omega)
  have r6 := hR 6 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r2 r3 r4 r5 r6
  have hw5 : ru < 2 ^ w := hwords ru (by simp [hargs])
  have hw6 : rv < 2 ^ w := hwords rv (by simp [hargs])
  have hpre : ∀ (m : ℕ → ℕ) (a : ℕ), Valid m d h LB →
      SrcBlock w h m d a LB → (uAccContract w h).pre [d, a, LB, 1, 0] m :=
    fun m a hv hs => ⟨_, _, _, _, _, rfl, by omega, hk1, hv, hs.1, hs.2.1, hdw, hs.2.2⟩
  have hargw : ∀ a : ℕ, a < 2 ^ w → ∀ v ∈ [d, a, LB, 1, 0], v < 2 ^ w := by
    intro a ha v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
  refine runs_start_le ?_
  unfold accEdgeProc
  refine runs_cond_le (v := if ru = rv then 1 else 0) (by eval_expr) ?_ ?_
  · -- the same root: one addition
    intro hne
    have hsame : ru = rv := by by_contra hc; simp [hc] at hne
    refine runs_seq_call_le (vs := [d, duv, LB, 1, 0]) hAcc
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
      (hargw duv (by have := hs0.2.2; omega)) (hpre _ duv hvd hs0) ?_
    rintro v₁ mem₁ pos₁ ⟨d₁, a₁, L₁, k₁, n₁, heq₁, -, hfr₁, hv₁, hu₁⟩
    simp only [List.cons.injEq, and_true] at heq₁
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₁
    refine runs_ret_le (v := 0) (by eval_expr) ⟨d, duv, adu, adv, LB, ru, rv, rfl, rfl,
      hfr₁, hv₁, ?_⟩ ?_
    · rw [hu₁, accLevelVal, if_pos hsame, accTerm, if_neg (by omega), one_mul]
      rfl
    · simp only [accEdgeContract, uAccContract, hargs, List.getD_cons_zero,
        List.getD_cons_succ, argsSize, Expr.size_const, Expr.size_reg, Expr.size_bin]
      omega
  · -- different roots: two additions
    intro heq0
    have hne : ru ≠ rv := by intro hc; simp [hc] at heq0
    refine runs_seq_call_le (vs := [d, adu, LB, 1, 0]) hAcc
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
      (hargw adu (by have := hs1.2.2; omega)) (hpre _ adu hvd hs1) ?_
    rintro v₁ mem₁ pos₁ ⟨d₁, a₁, L₁, k₁, n₁, heq₁, -, hfr₁, hv₁, hu₁⟩
    simp only [List.cons.injEq, and_true] at heq₁
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₁
    obtain ⟨hs2₁, hU2₁⟩ := hs2.of_frame hfr₁
    refine runs_seq_call_le (vs := [d, adv, LB, 1, 0]) hAcc
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
      (hargw adv (by have := hs2.2.2; omega)) (hpre _ adv hv₁ hs2₁) ?_
    rintro v₂ mem₂ pos₂ ⟨d₂, a₂, L₂, k₂, n₂, heq₂, -, hfr₂, hv₂, hu₂⟩
    simp only [List.cons.injEq, and_true] at heq₂
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₂
    have hfr₁₂ : ∀ x, x < d ∨ d + LB ≤ x → mem₂ x = mem x :=
      fun x hx => (hfr₂ x hx).trans (hfr₁ x hx)
    refine runs_ret_le (v := 0) (by eval_expr) ⟨d, duv, adu, adv, LB, ru, rv, rfl, rfl,
      hfr₁₂, hv₂, ?_⟩ ?_
    · rw [hu₂, hu₁]
      dsimp only
      rw [hU2₁, accLevelVal, if_neg hne]
      simp only [accTerm, if_neg (show (0 : ℕ) ≠ 1 by omega), one_mul]
      rfl
    · simp only [accEdgeContract, uAccContract, hargs, List.getD_cons_zero,
        List.getD_cons_succ, argsSize, Expr.size_const, Expr.size_reg, Expr.size_bin]
      omega

end MinCostFlow.LSF.Program
