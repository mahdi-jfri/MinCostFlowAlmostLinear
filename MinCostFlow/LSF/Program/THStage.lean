module

public import MinCostFlow.LSF.Program.THProc

/-!
# The parents of `T_H`, in the aux block

`thStageProc` runs `thProc` in scratch space at `base`, copies the parents in `T_H` into the aux
array at `thDst`, and stores the root as its own parent (the aux block asks for that). The depths
in `T_H` stay in the scratch space at `base + 7n`, where a later stage reads them.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- Args: `[n, qPtr, parPtr, depPtr, base, r, thDst]`. -/
def thStageProc (bTH bCopy : ℕ) : Stmt :=
  .call 7 bTH [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 7 bCopy [.reg 6, .bin .add (.reg 4) (.bin .mul (.const 6) (.reg 0)), .reg 0] ;;
  .store (.bin .add (.reg 6) (.reg 5)) (.reg 5) ;;
  .ret (.const 0)

lemma thStageProc_noRand (bTH bCopy : ℕ) : (thStageProc bTH bCopy).NoRand := by
  simp [thStageProc, Stmt.NoRand]

/-- The contract of `thStageProc`: the pre of `thContract`, with the root `r` and the output array
`thDst` below the scratch space. -/
def thStageContract (w : ℕ) (T₀ : MGraph) (vList : List ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr depPtr base r thDst tM : ℕ) (Q : List ℕ)
      (fid tl hd pe : ℕ → ℕ),
    args = [n, qPtr, parPtr, depPtr, base, r, thDst] ∧ 0 < n ∧ vList.length = n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    TreeIdx T₀ vList tM r fid tl hd (fun x => mem (parPtr + x)) pe (fun x => mem (depPtr + x)) ∧
    (∀ x < n, mem (depPtr + x) < n) ∧
    qPtr + n ≤ base ∧ parPtr + n ≤ base ∧ depPtr + n ≤ base ∧ thDst + n ≤ base ∧
    base + 8 * n < 2 ^ w ∧
    thBound n + 2 * n + 8 < 2 ^ w ∧ (∀ a, base ≤ a → a < base + 8 * n → mem a = 0)
  post args mem ret mem' := ∃ (n qPtr parPtr depPtr base r thDst : ℕ),
    args = [n, qPtr, parPtr, depPtr, base, r, thDst] ∧ ret = 0 ∧
    (∀ x < n, x ≠ r → mem' (thDst + x) < n ∧
      vList.getD (mem' (thDst + x)) 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0)) ∧
    mem' (thDst + r) = r ∧
    (∀ x < n, mem' (base + 7 * n + x) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0)) ∧
    ∀ a, (a < thDst ∨ thDst + n ≤ a) → (a < base ∨ base + 8 * n ≤ a) → mem' a = mem a
  cost args _ := args.getD 0 0 * (bstLoopCost (args.getD 0 0) + 500) + 20 * args.getD 0 0 + 600

theorem thStage_meetsContract {w : ℕ} {T₀ : MGraph} {vList : List ℕ} {p : Program}
    {b bTH bCopy : ℕ}
    (hp : p.procs[b]? = some (thStageProc bTH bCopy))
    (hTH : MeetsContract w p bTH (thContract w))
    (hCopy : MeetsContract w p bCopy (memCopyContract w)) :
    MeetsContract w p b (thStageContract w T₀ vList) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, depPtr, base, r, thDst, tM, Q, fid, tl, hd, pe, rfl, hn, hvn, hQ,
    hQat, hI, hdep, hqb, hpb, hdb, htb, hbw, hBw, hz⟩ := hpre
  set args := [n, qPtr, parPtr, depPtr, base, r, thDst] with hargs
  have hR0 : ∀ i < 7, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 7, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hrn : r < n := by
    have h0 := hQ.head_eq hn
    rw [← h0]; exact hQ.lt _ (List.getElem_mem _)
  refine runs_start_le ?_
  unfold thStageProc
  have r0 := hR0 0 (by omega)
  have r1 := hR0 1 (by omega)
  have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega)
  have r4 := hR0 4 (by omega)
  have r5 := hR0 5 (by omega)
  have r6 := hR0 6 (by omega)
  -- 1. `T_H`
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, depPtr, base]) hTH
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega))
    ⟨n, qPtr, parPtr, depPtr, base, r, tM, Q, T₀, vList, fid, tl, hd, pe, rfl, hn, hvn, hQ, hQat,
      hI, hdep, hqb, hpb, hdb, hbw, hBw, hz⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨n', qPtr', parPtr', depPtr', base', heq₁, -, hfr₁, hout₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hfr₁ hout₁
  have hO := hout₁ Q r tM T₀ vList fid tl hd pe hvn hQ hQat hI hdep
  -- 2. copy the parents
  have h6 : 6 * n ≤ 8 * n := by omega
  have hsrc : base + 6 * n < 2 ^ w := by omega
  refine runs_seq_call_le (vs := [thDst, base + 6 * n, n]) hCopy
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr <;> omega)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hwa 6 (by omega)
      · exact hsrc
      · exact hwa 0 (by omega))
    ⟨thDst, base + 6 * n, n, rfl, by omega, by omega, Or.inl (by omega)⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨dst', src', len', heq₂, -, hcp₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hcp₂ hfr₂
  -- 3. the root is its own parent
  refine runs_seq_store_le (x := thDst + r) (v := r) (by eval_expr <;> omega) (by eval_expr) ?_
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, depPtr, base, r, thDst, rfl, rfl,
    fun x hx hxr => ?_, ?_, fun x hx => ?_, fun a ha1 ha2 => ?_⟩ ?_
  · try dsimp only
    rw [Function.update_of_ne (by omega), hcp₂ x hx]
    exact (hO x hx).2 hxr
  · try dsimp only
    rw [Function.update_self]
  · try dsimp only
    rw [Function.update_of_ne (by omega), hfr₂ _ (by omega)]
    exact (hO x hx).1
  · try dsimp only
    rw [Function.update_of_ne (by omega), hfr₂ _ ha1, hfr₁ _ ha2]; rfl
  · simp only [thStageContract, thContract, memCopyContract, argsSize, Expr.size_const,
      Expr.size_reg, Expr.size_bin, List.getD_cons_zero, List.getD_cons_succ, hargs]
    omega

end

end MinCostFlow.LSF.Program
