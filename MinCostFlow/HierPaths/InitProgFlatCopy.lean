module

public import MinCostFlow.HierPaths.InitCopy
public import MinCostFlow.Spanner.ProgRevCopy

/-!
# Appending an embedding in the direction of traversal

The source list is copied forward when the current terminal is the first end of the host
edge. Otherwise it is copied backward. Both branches return the same output end.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- Append an embedding with arguments destination, source, length and two terminals to compare. -/
def initFlatCopy (forward backward : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 3) (.reg 4))
    (.call 5 forward [.reg 0, .reg 1, .reg 2] ;; .ret (.reg 5))
    (.call 5 backward [.reg 0, .reg 1, .reg 2] ;;
      .ret (.bin .add (.reg 0) (.reg 2)))

theorem initFlatCopy_noRand (forward backward : ℕ) : (initFlatCopy forward backward).NoRand := by
  simp [initFlatCopy, Stmt.NoRand]

/-- The copied embedding is the only change to memory. -/
def initFlatCopyContract (w : ℕ) (xs : List ℕ) : Contract where
  pre args mem := ∃ dst src u first, args = [dst, src, xs.length, u, first] ∧
    ListAt mem src xs ∧ src + xs.length ≤ dst ∧ dst + xs.length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ dst src u first,
    args = [dst, src, xs.length, u, first] ∧ v = dst + xs.length ∧
    ListAt mem' dst (if u = first then xs else xs.reverse) ∧
    ∀ y, y < dst ∨ dst + xs.length ≤ y → mem' y = mem y
  cost _ _ := 30 * xs.length + 40

theorem initFlatCopy_meetsContract {w f forward backward : ℕ} {xs : List ℕ} {p : Program}
    (hp : p.procs[f]? = some (initFlatCopy forward backward))
    (hF : p.procs[forward]? = some copyUp) (hR : p.procs[backward]? = some revCopyBody) :
    MeetsContract w p f (initFlatCopyContract w xs) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨dst, src, u, first, rfl, hm, hsep, hroom, h1⟩ := hpre
  have hw' : ∀ v ∈ ([dst, src, xs.length] : List ℕ), v < 2 ^ w := by
    intro v hv
    exact hw v (by simp at hv ⊢; tauto)
  refine runs_start_le ?_
  unfold initFlatCopy
  refine runs_cond_le (v := if u = first then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h1) ?_ ?_
  · intro hn
    have he : u = first := by by_contra h; simp [h] at hn
    refine runs_seq_call_le (copyUp_meetsContract hF)
      (vs := [dst, src, xs.length]) rfl hw' ⟨dst, src, xs.length, rfl, hsep, hroom, h1⟩ ?_
    intro v mem' pos' hpost
    obtain ⟨dst', src', len', hargs, hv, hcopy, hframe⟩ := hpost
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨hd, hs, hl⟩ := hargs
    subst dst' src' len'
    refine runs_ret_le (v := v) (by simp [Expr.eval])
      ⟨dst, src, u, first, rfl, hv, ?_, hframe⟩ ?_
    · simp only [he, ↓reduceIte]
      intro i hi
      exact (hcopy i hi).trans (hm i hi)
    · simp [copyUpContract, initFlatCopyContract, argsSize, Expr.size]
      omega
  · intro hz
    have hn : u ≠ first := by intro he; simp [he] at hz
    have hpreR : RevCopyPre mem dst src xs.length xs w := ⟨hm, rfl, hsep, hroom, h1⟩
    refine runs_seq_call_le (revCopy_meetsContract hR)
      (vs := [dst, src, xs.length]) rfl hw' ⟨dst, src, xs.length, xs, rfl, hpreR⟩ ?_
    intro v mem' pos' hpost
    obtain ⟨hrev, hframe⟩ := hpost dst src xs.length xs rfl hpreR
    refine runs_ret_le (v := dst + xs.length)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hroom)
      ⟨dst, src, u, first, rfl, rfl, by simpa [hn] using hrev, hframe⟩ ?_
    simp [revCopyContract, initFlatCopyContract, argsSize, Expr.size]
    omega

end MinCostFlow.HierPaths

end
