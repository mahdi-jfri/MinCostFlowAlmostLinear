module

public import WordRAM.Logic
public import MinCostFlow.Expander.DecomposePhiProg

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Loops for the evaluator of `Γ`

Two loops of the Word-RAM evaluator of `Γ` (`BoundsProg.lean`) and their Hoare triples:
`rootLoop` finds the integer `k`-th root of a register by counting up from zero, with one
comparison per candidate, and `log2Loop_triple'` counts the halvings of a register to find its
`⌊log₂⌋`. They are the loops of `Expander/PathDSProg/BoundsLoopProg.lean`, restated here so that
the evaluator does not depend on the parameters of the cited path data structure.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Expander

/-- Linear root-finding loop: increments `rRoot` while `powE < rT + 1`, maintaining `rCur = rRoot + 1`. -/
def rootLoop (rRoot rCur rT : ℕ) (powE : Expr) : Stmt :=
  .loop (.bin .lt powE (.bin .add (.reg rT) (.const 1)))
    (.assign rRoot (.bin .add (.reg rRoot) (.const 1)) ;;
     .assign rCur (.bin .add (.reg rRoot) (.const 1)))

lemma rootLoop_noRand (rRoot rCur rT : ℕ) (powE : Expr) :
    (rootLoop rRoot rCur rT powE).NoRand := by
  simp [rootLoop, Stmt.NoRand]

/-- Generic `Triple` for `rootLoop` parameterized by exponent `k ≥ 1` and power expression `powE`. -/
theorem rootLoop_triple {w : ℕ} {p : Program}
    (rRoot rCur rT k target ans : ℕ) (powE : Expr)
    (hnd : [rRoot, rCur, rT].Nodup)
    (hk : 1 ≤ k)
    (hans : ans ^ k ≤ target ∧ target < (ans + 1) ^ k)
    (hpow_eval : ∀ st, st.regs rCur ≤ ans + 1 → powE.eval w st = some (st.regs rCur ^ k))
    (ht2w : target + 1 < 2 ^ w) (hpow2w : (ans + 1) ^ k < 2 ^ w)
    (st₀ : State) (hrr₀ : st₀.regs rRoot = 0) (hrc₀ : st₀.regs rCur = 1) (hrt₀ : st₀.regs rT = target) :
    Triple w p (fun st => st = st₀) (rootLoop rRoot rCur rT powE)
      (normalPost fun st' => st'.regs rRoot = ans ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        ∀ r, r ≠ rRoot → r ≠ rCur → st'.regs r = st₀.regs r)
      (fun _ => (powE.size + 14) * ans + (powE.size + 5)) := by
  have hrc_ne : rRoot ≠ rCur := fun h => by subst h; simp at hnd
  have hrt_ne : rRoot ≠ rT := fun h => by subst h; simp at hnd
  have hct_ne : rCur ≠ rT := fun h => by subst h; simp at hnd
  have h1w : 1 < 2 ^ w := by omega
  have hans_lt_2w : ans + 1 < 2 ^ w := by
    have : ans + 1 ≤ (ans + 1) ^ k := Nat.le_self_pow (by omega) _
    omega
  let Inv : State → Prop := fun st =>
    st.regs rT = target ∧ st.regs rCur = st.regs rRoot + 1 ∧ st.regs rRoot ≤ ans ∧
      st.mem = st₀.mem ∧ st.pos = st₀.pos ∧ (∀ r, r ≠ rRoot → r ≠ rCur → st.regs r = st₀.regs r)
  have hloop := Triple.loop_const_normal (p := p) (w := w)
    (e := .bin .lt powE (.bin .add (.reg rT) (.const 1)))
    (body := .assign rRoot (.bin .add (.reg rRoot) (.const 1)) ;;
      .assign rCur (.bin .add (.reg rRoot) (.const 1)))
    (Inv := Inv)
    (Q := fun st' => st'.regs rRoot = ans ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
      ∀ r, r ≠ rRoot → r ≠ rCur → st'.regs r = st₀.regs r)
    (m := fun st => ans - st.regs rRoot)
    (condVal := fun st => if st.regs rCur ^ k < target + 1 then 1 else 0)
    (bodyBound := 9)
    (hcond := fun st hInv => by
      rcases hInv with ⟨hrt, hrc, hle, _, _, _⟩
      have he1 : powE.eval w st = some (st.regs rCur ^ k) := hpow_eval st (by omega)
      have he2 : (Expr.bin .add (.reg rT) (.const 1)).eval w st = some (target + 1) :=
        Expr.eval_add (Expr.eval_reg_of_eq hrt) (Expr.eval_const h1w) ht2w
      exact Expr.eval_lt_op he1 he2 h1w)
    (hexit := fun st hInv hv => by
      rcases hInv with ⟨hrt, hrc, hle, hm, hp, hf⟩
      have hge : target + 1 ≤ (st.regs rRoot + 1) ^ k := by
        by_contra hlt
        simp [hrc, show (st.regs rRoot + 1) ^ k < target + 1 by omega] at hv
      have heq : st.regs rRoot = ans := by
        by_contra hne
        have hlt1 : st.regs rRoot + 1 ≤ ans := by omega
        have hpow_le : (st.regs rRoot + 1) ^ k ≤ ans ^ k := Nat.pow_le_pow_left hlt1 k
        omega
      exact ⟨heq, hm, hp, hf⟩)
    (hstep := fun st hInv hv => by
      rcases hInv with ⟨hrt, hrc, hle, hm, hp, hf⟩
      have hlt_pow : (st.regs rRoot + 1) ^ k < target + 1 := by
        by_contra hge
        have : ¬ st.regs rCur ^ k < target + 1 := by rw [hrc]; exact hge
        simp [this] at hv
      have hlt_ans : st.regs rRoot < ans := by
        by_contra hge
        have heq : st.regs rRoot = ans := by omega
        rw [heq] at hlt_pow
        omega
      have ha1 : st.regs rRoot + 1 < 2 ^ w := by omega
      have ha2 : st.regs rRoot + 2 < 2 ^ w := by omega
      intro s ω' hs; subst s
      let st₁ : State := { st with regs := Function.update st.regs rRoot (st.regs rRoot + 1) }
      let st₂ : State := { st₁ with regs := Function.update st₁.regs rCur (st.regs rRoot + 2) }
      have hr1 : Runs w p ω' (.assign rRoot (.bin .add (.reg rRoot) (.const 1))) st .normal st₁ 4 :=
        runs_assign_iff.mpr ⟨st.regs rRoot + 1,
          Expr.eval_add (Expr.eval_reg _ _ _) (Expr.eval_const h1w) ha1, rfl, rfl, by simp⟩
      have hr2 : Runs w p ω' (.assign rCur (.bin .add (.reg rRoot) (.const 1))) st₁ .normal st₂ 4 :=
        runs_assign_iff.mpr ⟨st.regs rRoot + 2,
          Expr.eval_eq_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp [st₁]; rw [Function.update_self]))
              (Expr.eval_const h1w) ha2) (by omega), rfl, rfl, by simp⟩
      refine ⟨.normal, st₂, 9, runs_seq_iff.mpr (Or.inr ⟨st₁, 4, 4, hr1, hr2, rfl⟩), ?_, le_rfl⟩
      refine ⟨⟨?_, ?_, ?_, hm, hp, ?_⟩, ?_⟩
      · dsimp [st₂, st₁]
        rw [Function.update_of_ne hct_ne.symm, Function.update_of_ne hrt_ne.symm, hrt]
      · dsimp [st₂, st₁]
        rw [Function.update_self, Function.update_of_ne hrc_ne, Function.update_self]
      · dsimp [st₂, st₁]
        rw [Function.update_of_ne hrc_ne, Function.update_self]
        omega
      · intro r hr1' hr2'
        dsimp [st₂, st₁]
        rw [Function.update_of_ne hr2', Function.update_of_ne hr1']
        exact hf r hr1' hr2'
      · dsimp [st₂, st₁]
        rw [Function.update_of_ne hrc_ne, Function.update_self]
        omega)
  refine hloop.conseq (by
      intro s hs; subst s
      dsimp only [Inv]
      rw [hrr₀, hrc₀]
      exact ⟨hrt₀, by omega, Nat.zero_le _, rfl, rfl, fun _ _ _ => rfl⟩)
    (fun o s' hq => hq)
    (by
      intro s hs; subst s
      rw [hrr₀, Nat.sub_zero]
      have hsz : (Expr.bin .lt powE (.bin .add (.reg rT) (.const 1))).size = powE.size + 4 := by
        simp
      rw [hsz, show powE.size + 4 + 9 + 1 = powE.size + 14 by omega]
      omega)

/-- `Triple` wrapper around `DecomposePhiProg.DecomposePhiProg.log2_loop_runs`. -/
lemma log2Loop_triple' {w : ℕ} {p : Program}
    (rCur rCnt x : ℕ) (hne : rCur ≠ rCnt) (hx : x < 2 ^ w) (h4 : 4 ≤ 2 ^ w)
    (hk2w : Nat.log 2 x < 2 ^ w) (st₀ : State) (hrc : st₀.regs rCur = x) (hrk : st₀.regs rCnt = 0) :
    Triple w p (fun st => st = st₀)
      (.loop (.bin .lt (.const 1) (.reg rCur))
        (.assign rCur (.bin .div (.reg rCur) (.const 2)) ;;
         .assign rCnt (.bin .add (.reg rCnt) (.const 1))))
      (normalPost fun st' => st'.regs rCnt = Nat.log 2 x ∧ st'.mem = st₀.mem ∧
        st'.pos = st₀.pos ∧ ∀ r, r ≠ rCur → r ≠ rCnt → st'.regs r = st₀.regs r)
      (fun _ => 13 * (Nat.log 2 x + 1)) := by
  intro s ω hs; subst s
  obtain ⟨st', c, hr, hrCnt, hm, hp, hf, hc⟩ :=
    log2_loop_runs (w := w) (p := p) (ω := ω) rCur rCnt hne x hx h4 st₀ hrc hrk hk2w
  exact ⟨.normal, st', c, by simpa only [seqStmts] using hr, ⟨hrCnt, hm, hp, hf⟩, hc⟩

end MinCostFlow.HierPaths
