module

public import MinCostFlow.Num.IsNegative
public import MinCostFlow.Num.UnsignedLess
import MinCostFlow.Num.OrderFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Signed less-than

Different signs decide the order immediately. With equal signs, the offsets used in
signed decoding are equal, so unsigned comparison gives the signed order. The public
entry links two read-only helpers and costs at most `41*L + 51`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, L]`, sign-bit entry `neg`, unsigned comparison entry `less`. -/
def lessBody (neg less : ℕ) : Stmt :=
  .call 3 neg [.reg 0, .reg 2] ;;
  .call 4 neg [.reg 1, .reg 2] ;;
  .cond (.bin .eq (.reg 3) (.reg 4))
    (.call 5 less [.reg 0, .reg 1, .reg 2] ;; .ret (.reg 5))
    (.ret (.reg 3))

/-- Signed less-than and the two helpers it calls. -/
def lessModule (b h : ℕ) : List Stmt :=
  [lessBody (b + 1) (b + 2), isNegativeBody h, unsignedLessBody (b + 2)]

/-- Return one exactly when the first signed integer is smaller than the second. -/
def lessContract (w h : ℕ) : Contract where
  pre := (unsignedLessContract w h).pre
  post args mem v mem' := mem' = mem ∧ v =
    if intVal mem (args.getD 0 0) h (args.getD 2 0) <
      intVal mem (args.getD 1 0) h (args.getD 2 0) then 1 else 0
  cost args _ := 41 * args.getD 2 0 + 51

/-- The complete signed comparison is deterministic. -/
theorem lessModule_noRand (b h : ℕ) : ∀ s ∈ lessModule b h, s.NoRand := by
  simp only [lessModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by simp [lessBody, Stmt.NoRand], isNegativeBody_noRand _, unsignedLessBody_noRand _⟩

private theorem same_sign_of_words {x y : ℤ} {u v : ℕ}
    (hu : u = if x < 0 then 1 else 0) (hv : v = if y < 0 then 1 else 0)
    (he : u = v) : x < 0 ↔ y < 0 := by
  split_ifs at hu hv <;> omega

private theorem less_of_different_sign_words {x y : ℤ} {u v : ℕ}
    (hu : u = if x < 0 then 1 else 0) (hv : v = if y < 0 then 1 else 0)
    (he : u ≠ v) : u = if x < y then 1 else 0 := by
  split_ifs at hu hv ⊢ <;> omega

/-- Signed less-than meets its contract in linear time and preserves all memory. -/
theorem less_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (lessModule b h)) : MeetsContract w p b (lessContract w h) := by
  have hneg : p.HasAt (b + 1) (isNegativeModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [lessModule, isNegativeModule] using hp 1 (by simp [lessModule])
  have hunsigned : p.HasAt (b + 2) (unsignedLessModule (b + 2)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [lessModule, unsignedLessModule] using hp 2 (by simp [lessModule])
  have hn := isNegative_meetsContract hh hw hb hneg
  have hl := unsignedLess_meetsContract (h := h) hw hunsigned
  have hentry : p.procs[b]? = some (lessBody (b + 1) (b + 2)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨a, d, L, rfl, ha, hd, hva, hvd⟩ := hpre
  have haw : a < 2 ^ w := hwords a (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  apply runs_start_le
  unfold lessBody
  refine runs_seq_call_le hn (vs := [a, L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a, L, rfl, ha, hva⟩
  · intro u mem' pos' hpost
    rcases hpost with ⟨he, hu⟩
    subst mem'
    change u = if intVal mem a h L < 0 then 1 else 0 at hu
    have huw : u < 2 ^ w := by split_ifs at hu <;> omega
    refine runs_seq_call_le hn (vs := [d, L]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨d, L, rfl, hd, hvd⟩
    · intro v mem' pos'' hpost
      rcases hpost with ⟨he, hv⟩
      subst mem'
      change v = if intVal mem d h L < 0 then 1 else 0 at hv
      have hvw : v < 2 ^ w := by split_ifs at hv <;> omega
      refine runs_cond_le (v := if u = v then 1 else 0) (by eval_expr) ?_ ?_
      · intro he
        have heq : u = v := by
          by_contra hne
          simp [hne] at he
        have hs := same_sign_of_words hu hv heq
        refine runs_seq_call_le hl (vs := [a, d, L]) (by eval_expr) hwords ?_ ?_
        · exact ⟨a, d, L, rfl, ha, hd, hva, hvd⟩
        · intro r mem' pos''' hpst
          rcases hpst with ⟨hmem, hr⟩
          subst mem'
          change r = if unsignedVal mem a h L < unsignedVal mem d h L then 1 else 0 at hr
          have hrw : r < 2 ^ w := by split_ifs at hr <;> omega
          refine runs_ret_le (v := r) (by eval_expr) ?_ ?_
          · change mem = mem ∧ r = if intVal mem a h L < intVal mem d h L then 1 else 0
            refine ⟨rfl, ?_⟩
            simpa only [intVal_lt_iff_of_same_sign hva hvd hs] using hr
          · simp only [lessContract, isNegativeContract, unsignedLessContract,
              List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, Expr.size_bin,
              argsSize_cons, argsSize_nil]
            omega
      · intro he
        have hne : u ≠ v := by
          intro heq
          simp [heq] at he
        refine runs_ret_le (v := u) (by eval_expr) ?_ ?_
        · change mem = mem ∧ u = if intVal mem a h L < intVal mem d h L then 1 else 0
          exact ⟨rfl, less_of_different_sign_words hu hv hne⟩
        · simp only [lessContract, isNegativeContract, List.getD_cons_zero,
            List.getD_cons_succ, Expr.size_reg, Expr.size_bin, argsSize_cons, argsSize_nil]
          omega

end MinCostFlow.Num
