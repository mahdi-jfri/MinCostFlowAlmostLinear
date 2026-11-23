module

public import MinCostFlow.HierPaths.QueryProgMain

/-!
# Finishing a GetPath call

The loop eraser restores the position array and leaves the simple walk in two scratch
arrays. The writer copies it to the output. A final sweep clears the scratch space.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM Spanner

/-- The registers passed to the tail of a query after the step buffers have been filled. -/
structure QueryFinishRegs (st : State) (s out cap inE inY stE stY k : ℕ) : Prop where
  start : st.regs 1 = s
  output : st.regs 3 = out
  capacity : st.regs 6 = cap
  inputE : st.regs 7 = inE
  inputY : st.regs 8 = inY
  stackE : st.regs 9 = stE
  stackY : st.regs 10 = stY
  length : st.regs 18 = k

/-- After erasure and writing, the output is the walk of the erased steps. The original cells
below the heap pointer are restored, and memory from the returned pointer is zero. -/
theorem queryFinish_runs {w : ℕ} {p : Program} {fErase fWrite fList fZero : ℕ}
    (hErase : p.procs[fErase]? = some eraseProc)
    (hWrite : p.procs[fWrite]? = some (writeWalkProc fList))
    (hList : p.procs[fList]? = some copyListBody)
    (hZero : p.procs[fZero]? = some zeroProc)
    {s out cap inE inY stE stY posA n : ℕ} {E Y : List ℕ} {st : State} (ω : ℕ → Bool)
    (hregs : QueryFinishRegs st s out cap inE inY stE stY E.length)
    (hpos : (secExpr 22).eval w st = some posA)
    (hM : EraseMem inE inY s posA stE stY n E Y st.mem)
    (hposZero : ∀ v < n, st.mem (posA + v) = 0)
    (hbefore : ∀ a, out ≤ a → a < inE → st.mem a = 0)
    (hafter : ZeroFrom st.mem (inE + 4 * cap))
    (hcap : E.length ≤ cap) (hposEnd : posA + n ≤ out)
    (hIn : inE = out + 2 * cap + 3) (hInY : inY = inE + cap)
    (hStE : stE = inY + cap) (hStY : stY = stE + cap)
    (hw : inE + 4 * cap < 2 ^ w) (h4 : 4 < 2 ^ w) :
    let R := arrFrom s [] (E.zip Y)
    let out' := out + 2 * R.length + 3
    ∃ st' c, Runs w p ω (queryFinish fErase fWrite fZero) st (.returned out') st' c ∧
      WalkAt st'.mem out (ofSteps s R) ∧
      (∀ a < out, st'.mem a = st.mem a) ∧ ZeroFrom st'.mem out' ∧
      c ≤ 145 * E.length + 60 * cap + 200 := by
  let R := arrFrom s [] (E.zip Y)
  let out' := out + 2 * R.length + 3
  have hR : R.length ≤ E.length := by
    simpa [R, List.length_zip, hM.len] using length_arrFrom_le s [] (E.zip Y)
  have hsw : s < 2 ^ w := by
    have := hM.start
    omega
  have hw₁ : 1 < 2 ^ w := by omega
  have hE := eraseProc_meetsContract (p := p) hErase (w := w) (E := E) (Y := Y)
    (inE := inE) (inY := inY) (s := s) (posA := posA) (n := n) (stE := stE) (stY := stY)
    hw₁ (by omega) (by omega) (by omega) (by omega) (by omega)
  have hW := writeWalkProc_meetsContract (p := p) hWrite hList (w := w)
    (s := s) (stE := stE) (stY := stY) (out := out) (r := R)
    hw₁ (by omega) (by omega) (by omega)
  have hZ := zeroProc_meetsContract (w := w) hZero
  have hr1 := hregs.start
  have hr3 := hregs.output
  have hr6 := hregs.capacity
  have hr7 := hregs.inputE
  have hr8 := hregs.inputY
  have hr9 := hregs.stackE
  have hr10 := hregs.stackY
  have hr18 := hregs.length
  suffices hrun : ∃ o st' c, Runs w p ω (queryFinish fErase fWrite fZero) st o st' c ∧
      (o = .returned out' ∧ WalkAt st'.mem out (ofSteps s R) ∧
        (∀ a < out, st'.mem a = st.mem a) ∧ ZeroFrom st'.mem out') ∧
      0 + c ≤ 145 * E.length + 60 * cap + 200 by
    obtain ⟨o, st', c, he, ⟨rfl, hWalk, hFrame, hTail⟩, hcost⟩ := hrun
    exact ⟨st', c, he, hWalk, hFrame, hTail, by omega⟩
  unfold queryFinish
  refine runs_seq_call_le hE (vs := [inE, inY, E.length, s, posA, stE, stY]) ?_ ?_
    ⟨rfl, hM, hposZero⟩ ?_
  · exact evalArgs_cons (Expr.eval_reg_of_eq hr7) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr8) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr18) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr1) <|
      evalArgs_cons hpos <| evalArgs_cons (Expr.eval_reg_of_eq hr9) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr10) (evalArgs_nil _ _)
  · wram_words
  intro len m₁ p₁ hpost
  obtain ⟨hlen, he, hy, hp0, hf₁⟩ := hpost
  change len = R.length at hlen
  subst len
  wram_step
  · exact ⟨rfl, he, hy, Or.inr (by omega), Or.inr (by omega)⟩
  intro r m₂ p₂ hpost
  obtain ⟨hWalk, hf₂⟩ := hpost
  refine runs_seq_call_le hZ (vs := [inE, 4 * cap]) ?_ (by wram_words)
    ⟨inE, 4 * cap, rfl, hw, hw₁⟩ ?_
  · refine evalArgs_cons (by eval_expr) (evalArgs_cons ?_ (evalArgs_nil _ _))
    exact Expr.eval_mul (Expr.eval_const h4) (by eval_expr) (by omega)
  intro r' m₃ p₃ hpost
  obtain ⟨base, len, heq, hz, hf₃⟩ := hpost
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hlo : out' ≤ inE := by dsimp [out']; omega
  have hbelow₁ : ∀ a < out, m₁ a = st.mem a := by
    intro a ha
    by_cases hhit : posA ≤ a ∧ a < posA + n
    · have hidx : a - posA < n := by omega
      have heq : posA + (a - posA) = a := by omega
      rw [← heq, hp0 _ hidx, hposZero _ hidx]
    · apply hf₁
      unfold EraseOutside
      omega
  have hretW : out' < 2 ^ w := by omega
  have htwice : 2 * R.length < 2 ^ w := by dsimp [out'] at hretW; omega
  have hsizeW : 2 * R.length + 3 < 2 ^ w := by dsimp [out'] at hretW; omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  refine runs_ret_le (v := out')
    (Expr.eval_add (a := .reg 3) (x := out) (y := 2 * R.length + 3) (Expr.eval_reg_of_eq (by simpa using hr3))
      (Expr.eval_add (x := 2 * R.length) (y := 3) (Expr.eval_mul (x := 2) (y := R.length) (Expr.eval_const h2w)
        (b := .reg 19) (Expr.eval_reg_of_eq (by simp)) htwice)
        (Expr.eval_const h3w) hsizeW) hretW) ?_ ?_
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · change WalkAt m₃ out (ofSteps s R)
      unfold WalkAt at hWalk ⊢
      refine hWalk.congr fun a _ hhigh => hf₃ a (Or.inl ?_)
      have hsize := walk_encode_length (ofSteps s R)
      have hvlen : (ofSteps s R).verts.length ≤ R.length + 1 := by
        cases R with
        | nil => simp [ofSteps, Walk.empty]
        | cons step rest => simp [ofSteps]
      have helen : (ofSteps s R).edges.length = R.length := by simp [edges_ofSteps]
      dsimp [out'] at hlo
      omega
    · intro a ha
      change m₃ a = st.mem a
      have hai : a < inE := by omega
      exact (hf₃ a (Or.inl hai)).trans ((hf₂ a (Or.inl ha)).trans (hbelow₁ a ha))
    · intro a ha
      change m₃ a = 0
      have hf₂' : ∀ a, out' ≤ a → m₂ a = m₁ a := fun a ha => hf₂ a (Or.inr ha)
      have hf₃' : ∀ a, a < inE ∨ inE + 4 * cap ≤ a → m₃ a = m₂ a := hf₃
      by_cases hsmall : a < inE
      · rw [hf₃' _ (Or.inl hsmall), hf₂' _ ha, hf₁ _]
        · exact hbefore a (by dsimp [out'] at ha; omega) hsmall
        · unfold EraseOutside
          dsimp [out'] at ha
          omega
      by_cases hhigh : inE + 4 * cap ≤ a
      · rw [hf₃' _ (Or.inr hhigh), hf₂' _ ha, hf₁ _]
        · exact hafter _ hhigh
        · unfold EraseOutside
          omega
      · have hi : a - inE < 4 * cap := by omega
        have haddr : inE + (a - inE) = a := by omega
        rw [← haddr, hz _ hi]
  · simp only [eraseContract, writeWalkContract, zeroContract, List.getD_cons_succ,
      List.getD_cons_zero, secExpr]
    change _ + _ ≤ _
    wram_cost

end MinCostFlow.HierPaths
