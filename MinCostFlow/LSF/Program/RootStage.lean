module

public import MinCostFlow.LSF.Program.RootTree
public import MinCostFlow.LSF.Program.BinaryLift
public import MinCostFlow.LSF.Program.T0Rooted
public import MinCostFlow.LSF.Program.SubtreeSumMath

/-!
# Rooting `T₀`, in one procedure

`rootStageProc` roots the tree given by its edge arrays and fills the ancestor table:
1. `rootTreeProc` computes the parent, parent-edge and depth arrays in fresh cells above the
   heap pointer, and a search order in which each vertex comes after its parent;
2. `memCopyStmt` copies the three arrays to their places in the aux block;
3. `upVProc` fills the ancestor table `liftF` right after them.

The aux block lies below the edge arrays, so the copy is needed: `rootTreeProc` asks its output to
lie above its input. `rootStage_meetsContract` gives `RootedArrays` and `TopDownOrder` for the
copied arrays, and the table. The cost is `O(n log n + m)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- `liftF` depends only on the parents of the vertices below `n`. -/
lemma liftF_congr {par par' : ℕ → ℕ} {n : ℕ} (hpar : ∀ x < n, par x < n)
    (heq : ∀ x < n, par x = par' x) (j : ℕ) : ∀ i < n, liftF par i j = liftF par' i j := by
  induction j with
  | zero => intro i hi; exact heq i hi
  | succ j ih =>
    intro i hi
    simp only [liftF]
    rw [← ih i hi]
    exact ih _ (liftF_lt hpar j i hi)

/-- `RootedArrays` depends only on the ends of the edges below `tM`. -/
lemma RootedArrays.congr_ends {n tM r : ℕ} {tl hd tl' hd' par pe dep : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) (htl : ∀ f < tM, tl f = tl' f)
    (hhd : ∀ f < tM, hd f = hd' f) : RootedArrays n tM r tl' hd' par pe dep := by
  refine ⟨hR.par_r, hR.dep_r, hR.par_lt, fun x hx hxr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hR.step x hx hxr
  refine ⟨h1, ?_, h3⟩
  unfold RTJoin at h2 ⊢
  rw [← htl _ h1, ← hhd _ h1]
  exact h2

/-- Args: `[n, m, tailArr, headArr, r, outPtr, sPtr, auxParPtr, logCap]`. -/
def rootStageProc (bRT bCopy bUp : ℕ) : Stmt :=
  .call 9 bRT [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  .call 9 bCopy [.reg 7, .reg 5, .bin .mul (.const 3) (.reg 0)] ;;
  .call 9 bUp [.reg 0, .reg 8, .reg 7, .bin .add (.reg 7) (.bin .mul (.const 3) (.reg 0))] ;;
  .ret (.const 0)

lemma rootStageProc_noRand (bRT bCopy bUp : ℕ) : (rootStageProc bRT bCopy bUp).NoRand := by
  simp [rootStageProc, Stmt.NoRand]

/-- The contract of `rootStageProc`. The aux arrays (`3 n` words, then the table of `n logCap`
words) lie below the edge arrays. -/
def rootStageContract (w : ℕ) : Contract where
  pre args mem := ∃ (n m tailArr headArr r outPtr sPtr auxParPtr logCap : ℕ) (tl hd : ℕ → ℕ),
    args = [n, m, tailArr, headArr, r, outPtr, sPtr, auxParPtr, logCap] ∧
    RTInput w n m tailArr headArr r outPtr sPtr tl hd mem ∧
    (∀ i < n, mem (sPtr + i) = 0) ∧ (∀ i < n, mem (sPtr + n + 2 * m + i) = 0) ∧
    (∀ x < n, Relation.ReflTransGen (rtAdj m tl hd) r x) ∧
    1 ≤ logCap ∧ auxParPtr + 3 * n + n * logCap ≤ tailArr ∧ auxParPtr + 3 * n ≤ headArr
  post args mem ret mem' := ∃ (n m tailArr headArr r outPtr sPtr auxParPtr logCap : ℕ)
      (tl hd : ℕ → ℕ),
    args = [n, m, tailArr, headArr, r, outPtr, sPtr, auxParPtr, logCap] ∧ ret = 0 ∧
    (∀ f < m, mem (tailArr + f) = tl f ∧ mem (headArr + f) = hd f) ∧
    RootedArrays n m r tl hd (fun x => mem' (auxParPtr + x)) (fun x => mem' (auxParPtr + n + x))
      (fun x => mem' (auxParPtr + n + n + x)) ∧
    (∃ Q, TopDownOrder n r (fun x => mem' (auxParPtr + x)) Q ∧
      ListAt mem' (sPtr + n + 2 * m + n) Q) ∧
    (∀ i < n, ∀ j < logCap, mem' (auxParPtr + 3 * n + (i * logCap + j)) =
      liftF (fun x => mem' (auxParPtr + x)) i j) ∧
    ∀ a, (a < auxParPtr ∨ auxParPtr + 3 * n + n * logCap ≤ a) →
      (a < outPtr ∨ (outPtr + 3 * n ≤ a ∧ a < sPtr) ∨ sPtr + 4 * n + 2 * m ≤ a) → mem' a = mem a
  cost args _ := 400 * args.getD 0 0 + 400 * args.getD 1 0 +
    60 * args.getD 0 0 * args.getD 8 0 + 40 * args.getD 8 0 + 400

theorem rootStage_meetsContract {w : ℕ} {p : Program} {b bRT bCopy bUp : ℕ}
    (hp : p.procs[b]? = some (rootStageProc bRT bCopy bUp))
    (hRT : MeetsContract w p bRT (rootTreeContract w))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hUp : MeetsContract w p bUp (upVContract w)) :
    MeetsContract w p b (rootStageContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, m, tailArr, headArr, r, outPtr, sPtr, auxParPtr, logCap, tl, hd, rfl, hI, hz1, hz2,
    hreach, hL, hax, hax2⟩ := hpre
  have hI' := hI
  obtain ⟨hw16, hr, htl, hhd, htA, hhA, hout, hword⟩ := hI'
  set args := [n, m, tailArr, headArr, r, outPtr, sPtr, auxParPtr, logCap] with hargs
  have hR0 : ∀ i < 9, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 9, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hnL : n * logCap ≤ tailArr := by omega
  refine runs_start_le ?_
  unfold rootStageProc
  have r0 := hR0 0 (by omega)
  have r1 := hR0 1 (by omega)
  have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega)
  have r4 := hR0 4 (by omega)
  have r5 := hR0 5 (by omega)
  have r6 := hR0 6 (by omega)
  have r7 := hR0 7 (by omega)
  have r8 := hR0 8 (by omega)
  -- 1. root the tree
  refine runs_seq_call_le (vs := [n, m, tailArr, headArr, r, outPtr, sPtr]) hRT
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 6 (by omega))
    ⟨n, m, tailArr, headArr, r, outPtr, sPtr, tl, hd, rfl, hI, hz1, hz2, hreach⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨n', m', tailArr', headArr', r', outPtr', sPtr', tl', hd', heq₁, hth, -,
    hroot, hord, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  have htl' : ∀ f < m, tl' f = tl f ∧ hd' f = hd f := fun f hf =>
    ⟨(hth f hf).1.symm.trans (htl f hf).1, (hth f hf).2.symm.trans (hhd f hf).1⟩
  have hR₁ := rootedArrays_of_rtRooted hroot
  -- 2. copy the three arrays to the aux block
  have h3n : 3 * n < 2 ^ w := by omega
  refine runs_seq_call_le (vs := [auxParPtr, outPtr, 3 * n]) hCopy
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hwa 7 (by omega)
      · exact hwa 5 (by omega)
      · exact h3n)
    ⟨auxParPtr, outPtr, 3 * n, rfl, by omega, by omega, Or.inl (by omega)⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨dst', src', len', heq₂, -, hcp₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hcp₂ hfr₂
  have hpar₂ : ∀ x < n, mem₂ (auxParPtr + x) = mem₁ (outPtr + x) := fun x hx => hcp₂ x (by omega)
  have hpe₂ : ∀ x < n, mem₂ (auxParPtr + n + x) = mem₁ (outPtr + n + x) := fun x hx => by
    rw [show auxParPtr + n + x = auxParPtr + (n + x) by omega, hcp₂ _ (by omega)]
    congr 1; omega
  have hdep₂ : ∀ x < n, mem₂ (auxParPtr + n + n + x) = mem₁ (outPtr + n + n + x) := fun x hx => by
    rw [show auxParPtr + n + n + x = auxParPtr + (n + n + x) by omega, hcp₂ _ (by omega)]
    congr 1; omega
  have hR₂ : RootedArrays n m r tl hd (fun x => mem₂ (auxParPtr + x))
      (fun x => mem₂ (auxParPtr + n + x)) (fun x => mem₂ (auxParPtr + n + n + x)) := by
    have h := hR₁.congr (par' := fun x => mem₂ (auxParPtr + x)) hr
      (pe' := fun x => mem₂ (auxParPtr + n + x)) (dep' := fun x => mem₂ (auxParPtr + n + n + x))
      (fun x hx => (hpar₂ x hx).symm) (fun x hx => (hpe₂ x hx).symm)
      (fun x hx => (hdep₂ x hx).symm)
    exact h.congr_ends (fun f hf => (htl' f hf).1) (fun f hf => (htl' f hf).2)
  -- 3. the ancestor table
  refine runs_seq_call_le (vs := [n, logCap, auxParPtr, auxParPtr + 3 * n]) hUp
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _)))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 8 (by omega)
      · exact hwa 7 (by omega)
      · omega)
    ⟨n, logCap, auxParPtr, auxParPtr + 3 * n, rfl, hw16, hL, fun i hi => hR₂.par_lt i hi,
      by omega, by omega⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨n', logCap', parPtr', upPtr', heq₃, -, hup₃, hfr₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hup₃ hfr₃
  have hA3 : ∀ x < 3 * n, mem₃ (auxParPtr + x) = mem₂ (auxParPtr + x) := fun x hx =>
    hfr₃ _ (Or.inl (by omega))
  have hR₃ : RootedArrays n m r tl hd (fun x => mem₃ (auxParPtr + x))
      (fun x => mem₃ (auxParPtr + n + x)) (fun x => mem₃ (auxParPtr + n + n + x)) :=
    hR₂.congr hr (fun x hx => (hA3 x (by omega)).symm)
      (fun x hx => by rw [add_assoc, hA3 _ (by omega), ← add_assoc])
      (fun x hx => by rw [add_assoc, add_assoc, hA3 _ (by omega), ← add_assoc, ← add_assoc])
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, m, tailArr, headArr, r, outPtr, sPtr, auxParPtr,
    logCap, tl, hd, rfl, rfl, fun f hf => ⟨(htl f hf).1, (hhd f hf).1⟩, hR₃, ?_,
    fun i hi j hj => ?_, fun a ha hb => ?_⟩ ?_
  · -- the order
    obtain ⟨Q, hlen, hnd, hcov, hlt, hQat, hafter⟩ := hord
    refine ⟨Q, ⟨hlen, hnd, hcov, hlt, fun j hj hne => ?_⟩, fun i hi => ?_⟩
    · have hq := hlt _ (List.getElem_mem hj)
      show mem₃ (auxParPtr + Q[j]) ∈ Q.take j
      rw [hA3 _ (by omega), hpar₂ _ hq]
      exact hafter j hj hne
    · try dsimp only
      rw [hfr₃ _ (Or.inr (by omega)), hfr₂ _ (Or.inr (by omega))]
      exact hQat i hi
  · -- the table
    try dsimp only
    rw [show auxParPtr + 3 * n + (i * logCap + j) = auxParPtr + 3 * n + (i * logCap + j) from rfl,
      hup₃ i hi j hj]
    exact liftF_congr (fun x hx => hR₂.par_lt x hx) (fun x hx => (hA3 x (by omega)).symm) j i hi
  · -- the frame
    try dsimp only
    rw [hfr₃ a (by omega), hfr₂ a (by omega)]
    exact hfr₁ a hb
  · -- the cost
    simp only [rootStageContract, rootTreeContract, memCopyContract, upVContract, argsSize,
      Expr.size_const, Expr.size_reg, Expr.size_bin, List.sum_cons, List.sum_nil, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ, hargs]
    omega

end

end MinCostFlow.LSF.Program
