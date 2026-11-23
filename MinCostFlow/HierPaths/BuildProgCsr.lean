module

public import MinCostFlow.HierPaths.BuildProgCopy
public import MinCostFlow.HierPaths.BuildProgOffsets
public import MinCostFlow.HierPaths.InitLayout

/-!
# Writing a list of lists in compressed form

Sections 3–5 of the static output are lists of lists in compressed form (`csrList k f`), and the
whole output is one too (`layoutList`). The construction builds the lists `f 0, …, f (k − 1)` one
after the other (the data part `csrData k f`) and keeps their lengths in a table. `csrProc`,
called with `[lens, k, src, dst]`, then writes `csrList k f` at `dst`: first the offsets, by
`offsetsProc`, then the data, by `buildCopyProc` (`csrProc_meetsContract`). The lengths and the data
lie below `dst`. The cost is linear in `k` plus the total length.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- `r4 := offsets(lens, k, dst); r5 := copy(src, r4, dst + k + 1); return r4`. -/
def csrProc (fOff fCopy : ℕ) : Stmt :=
  .seq (.call 4 fOff [.reg 0, .reg 1, .reg 3])
    (.seq (.call 5 fCopy [.reg 2, .reg 4, .bin .add (.bin .add (.reg 3) (.reg 1)) (.const 1)])
      (.ret (.reg 4)))

/-- The contract of `csrProc` for the lists `f`. -/
def csrContract (w : ℕ) (f : ℕ → List ℕ) : Contract where
  pre args mem := ∃ lens k src dst, args = [lens, k, src, dst] ∧
    (∀ j < k, mem (lens + j) = (f j).length) ∧ ListAt mem src (csrData k f) ∧
    lens + k ≤ dst ∧ src + (csrData k f).length ≤ dst ∧
    dst + k + 1 + (csrData k f).length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ lens k src dst, args = [lens, k, src, dst] ∧
    v = (csrData k f).length ∧ ListAt mem' dst (csrList k f) ∧
    ∀ x, (x < dst ∨ dst + k + 1 + (csrData k f).length ≤ x) → mem' x = mem x
  cost args _ := 22 * args.getD 1 0 + 17 * (csrData (args.getD 1 0) f).length + 80

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- **`csrProc` writes a list of lists in compressed form.** -/
theorem csrProc_meetsContract {w : ℕ} {f : ℕ → List ℕ} {p : Program} {fc fOff fCopy : ℕ}
    (hp : p.procs[fc]? = some (csrProc fOff fCopy))
    (hO : p.procs[fOff]? = some offsetsProc) (hC : p.procs[fCopy]? = some buildCopyProc) :
    MeetsContract w p fc (csrContract w f) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨lens, k, src, dst, rfl, hlen, hdata, hld, hsd, hdw, hw⟩
  set T := (csrData k f).length
  have hT : psum (fun j => mem (lens + j)) k = T := by
    show _ = (csrData k f).length
    rw [psum_eq_sum, length_csrData_eq]
    congr 1
    exact List.map_congr_left fun j hj => hlen j (by simp at hj; omega)
  refine runs_start_le ?_
  dsimp only [csrProc]
  -- the offsets
  refine runs_seq_call_le (offsetsProc_meetsContract (w := w) hO) (vs := [lens, k, dst])
    (by simp [evalArgs, Expr.eval, startState]) ?_
    ⟨lens, k, dst, rfl, hld, by omega, by simp only [startState]; omega, hw⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₁ mem₁ pos₁ hpost₁
  obtain ⟨_, _, _, hargs₁, hv₁, hoff₁, hf₁⟩ := hpost₁
  simp only [List.cons.injEq, and_true] at hargs₁
  obtain ⟨rfl, rfl, rfl⟩ := hargs₁
  simp only [startState] at hv₁ hoff₁ hf₁
  rw [hT] at hv₁
  subst hv₁
  -- the data
  have hk1 : dst + k + 1 < 2 ^ w := by omega
  have hk0 : dst + k < 2 ^ w := by omega
  refine runs_seq_call_le (buildCopyProc_meetsContract (w := w) hC) (vs := [src, T, dst + k + 1])
    (by simp [evalArgs, Expr.eval, BinOp.eval, Function.update, startState, hk0, hk1, hw]) ?_
    ⟨src, T, dst + k + 1, rfl, by omega, by omega, hw⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨_, _, _, hargs₂, hcp₂, hf₂⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl, rfl⟩ := hargs₂
  dsimp only at hcp₂ hf₂
  refine runs_ret_le (v := T) (by simp [Expr.eval, Function.update]) ⟨lens, k, src, dst, rfl,
    rfl, ?_, ?_⟩ ?_
  · dsimp only
    rw [csrList, listAt_append, length_csrOffsets]
    refine ⟨?_, fun i hi => ?_⟩
    · have := listAt_csrOffsets (mem' := mem₁) (dst := dst) hlen hoff₁
      intro i hi
      have hik : i ≤ k := by simp at hi; omega
      rw [hf₂ _ (Or.inl (by omega))]
      exact this i hi
    · have hiT : i < T := hi
      rw [show dst + (k + 1) + i = dst + k + 1 + i by omega, hcp₂ i hiT, hf₁ _ (Or.inl (by omega))]
      exact hdata i hi
  · intro x hx
    dsimp only
    rw [hf₂ x (by omega), hf₁ x (by omega)]
  · simp only [csrContract, offsetsContract, buildCopyContract, List.getD_cons_succ,
      List.getD_cons_zero, argsSize, Expr.size_reg, Expr.size_bin, Expr.size_const]
    omega

end MinCostFlow.HierPaths
