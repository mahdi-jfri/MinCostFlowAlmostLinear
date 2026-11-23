module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Copying a block of words

The writers of the sections of the static output (`StaticData.encode`) copy lists that the
construction has already built into their place in the output. `buildCopyProc`, called with
`[src, n, dst]`, copies the `n` words at `src, …, src + n − 1` to `dst, …, dst + n − 1` and changes
no other cell (`buildCopyProc_meetsContract`). The source lies below the target. The cost is
`17 n + 12`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- `for r3 in [0, n): mem[dst + r3] := mem[src + r3]`; return `0`. -/
def buildCopyProc : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 1)
      (.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))))
    (.ret (.const 0))

/-- The contract of `buildCopyProc`. -/
def buildCopyContract (w : ℕ) : Contract where
  pre args _ := ∃ src n dst, args = [src, n, dst] ∧ src + n ≤ dst ∧ dst + n < 2 ^ w ∧ 1 < 2 ^ w
  post args mem _ mem' := ∃ src n dst, args = [src, n, dst] ∧
    (∀ j < n, mem' (dst + j) = mem (src + j)) ∧
    ∀ x, (x < dst ∨ dst + n ≤ x) → mem' x = mem x
  cost args _ := 17 * args.getD 1 0 + 12

/-- Forward copying also moves a block toward lower addresses, even when
the source and destination overlap. -/
def buildCopyDownContract (w : ℕ) : Contract where
  pre args _ := ∃ src n dst, args = [src,n,dst] ∧ dst ≤ src ∧ src+n < 2^w ∧ 1 < 2^w
  post args mem v mem' := (buildCopyContract w).post args mem v mem'
  cost args mem := (buildCopyContract w).cost args mem

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

private theorem copy_triple_of_order {w src n dst : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hsd : src + n ≤ dst ∨ dst ≤ src)
    (hsn : src+n < 2^w) (hdn : dst + n < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.mem = mem₀)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost fun st' => (∀ j < n, st'.mem (dst + j) = mem₀ (src + j)) ∧
        ∀ x, (x < dst ∨ dst + n ≤ x) → st'.mem x = mem₀ x)
      (fun _ => 17 * n + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
    (P := fun st => st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + j) = mem₀ (src + j)) ∧
      (∀ x, (x < dst ∨ dst + i ≤ x) → st.mem x = mem₀ x))
    8 0 n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp,
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = n := hi.2.1
      simp [Expr.eval, h1])
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, hz, hf⟩
      have hsi : st.mem (src + i) = mem₀ (src + i) := hf _ (by
        rcases hsd with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) (mem₀ (src + i)) },
        8, ?_, ?_, by simp⟩
      · have hsw : src + i < 2 ^ w := by omega
        have hdw : dst + i < 2 ^ w := by omega
        refine runs_store_iff.mpr ⟨dst + i, mem₀ (src + i), ?_, ?_, rfl, rfl, by simp⟩
        · simp [Expr.eval, h2, h3, hdw]
        · simp [Expr.eval, h0, h3, hsw, hsi]
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · rw [hji, Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            exact hz j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hf x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨_, _, _, _, hz, hf⟩ := hpost
      exact ⟨hz, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- The copying loop for a source below the destination. -/
theorem copy_triple {w src n dst : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2^w) (hsd : src+n ≤ dst) (hdn : dst+n < 2^w) :
    Triple w p (fun st => st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.mem = mem₀)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost fun st' => (∀ j < n, st'.mem (dst + j) = mem₀ (src + j)) ∧
        ∀ x, (x < dst ∨ dst + n ≤ x) → st'.mem x = mem₀ x)
      (fun _ => 17*n+7) :=
  copy_triple_of_order p mem₀ hw (Or.inl hsd) (by omega) hdn

/-- **`buildCopyProc` meets its contract.** -/
theorem buildCopyProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some buildCopyProc) :
    MeetsContract w p f (buildCopyContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨src, n, dst, rfl, hsd, hdn, hw⟩
  refine runs_start_le ?_
  dsimp only [buildCopyProc]
  refine runs_seq_triple_le (copy_triple p mem hw hsd hdn)
    ⟨by simp [startState], by simp [startState], by simp [startState], rfl⟩ ?_
  intro st₁ ⟨hz, hf⟩
  refine runs_ret_le (v := 0) ?_ ⟨src, n, dst, rfl, hz, hf⟩ ?_
  · eval_expr
  · simp only [buildCopyContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_const]
    omega

/-- The same procedure copies toward lower addresses at the same cost. -/
theorem buildCopyProc_meetsDownContract {w f : ℕ} {p : Program}
    (hp : p.procs[f]? = some buildCopyProc) : MeetsContract w p f (buildCopyDownContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hPre => ?_
  obtain ⟨src,n,dst,rfl,hOrder,hEnd,hw⟩ := hPre
  refine runs_start_le ?_
  unfold buildCopyProc
  refine runs_seq_triple_le (copy_triple_of_order p mem hw (Or.inr hOrder) hEnd (by omega))
    ⟨rfl,rfl,rfl,rfl⟩ ?_
  intro st ⟨hOutput,hFrame⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
    ⟨src,n,dst,rfl,hOutput,hFrame⟩ ?_
  simp [buildCopyDownContract,buildCopyContract,Expr.size]

end MinCostFlow.HierPaths
