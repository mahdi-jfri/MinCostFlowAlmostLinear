module

public import MinCostFlow.Final.Scratch
public import MinCostFlow.Final.ScratchWordBoundProgram
public import MinCostFlow.Final.ScratchWrapper
public import MinCostFlow.Scaling.CanonicalSolveModule
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Canonical entry for polynomial scratch

The solver entry reads the circulation header and computes its guest
bound from the encoded input. It then uses the shared copying wrapper
with the polynomial reservation and runs the solver at that guest width.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The solver entry and scan precede the shared relocation wrapper. -/
def scratchSolveModule (Q : Program) (f b c d : ℕ) : List Stmt :=
  canonicalSolveBody (b + 1) (b + 2) ::
    scratchWordBoundBody (scratchWordMultiplier c d) ::
    canonicalWrapperModule Q f (b + 2)

/-- The original scratch policy gives the same canonical solver module. -/
theorem scratchSolveModule_original (Q : Program) (f b : ℕ) :
    scratchSolveModule Q f b 1 4 = canonicalSolveModule Q f b := by
  unfold scratchSolveModule canonicalSolveModule
  rw [scratchWordMultiplier_original]
  rfl

/-- The canonical module preserves determinism when wrapping the solver. -/
theorem scratchSolveModule_noRand (Q : Program) (f b c d : ℕ)
    (hdet : Q.IsDeterministic) :
    ∀ body ∈ scratchSolveModule Q f b c d, body.NoRand := by
  intro body hbody
  rcases List.mem_cons.mp hbody with rfl | hbody
  · exact canonicalSolveBody_noRand _ _
  · rcases List.mem_cons.mp hbody with rfl | hbody
    · exact scratchWordBoundBody_noRand _
    · exact canonicalWrapperModule_noRand Q f _ hdet body hbody

/-- The complete canonical solve returns the model function with fresh-heap
framing and the costs of guest setup, copying, and the solver itself. -/
def scratchSolveContract (w : ℕ) (Q : Program) (f : ℕ)
    (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (solverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, h] ∧ ListAt mem a J.solverWords ∧
      a + J.solverWords.length ≤ h ∧
      2 ^ (wordSize (scratchWordMultiplier c d) J.solverWords + 1) + 2 ≤ 2 ^ w)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args) = scratchCanonicalSolverAt (wordSize (scratchWordMultiplier c d) J.solverWords) Q f T S (hproc J) J)
    (fun _ _ => (Q.regBound + 6) * T J.n J.m +
      80 * J.solverWords.length + 40 * wordSize (scratchWordMultiplier c d) J.solverWords + Q.regBound + 300)
    (fun _ _ => 1 + 2 ^ wordSize (scratchWordMultiplier c d) J.solverWords)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 ^ wordSize (scratchWordMultiplier c d) J.solverWords }

/-- The executable canonical entry computes exactly `canonicalSolver` on
bounded circulations, at the stated setup and solver cost. -/
theorem scratchSolve_meetsContract
    {w entry bound wrapper : ℕ} {Q P : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (solverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hdet : Q.IsDeterministic) (J : Circulation)
    (hS : S J.n J.m ≤ c * (J.n + J.m + 2)^d)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hentry : P.procs[entry]? = some (canonicalSolveBody bound wrapper))
    (hbound : P.HasAt bound (scratchWordBoundModule (scratchWordMultiplier c d)))
    (hwrap : P.HasAt wrapper (canonicalWrapperModule Q f wrapper)) :
    MeetsContract w P entry (scratchSolveContract w Q f T S c d hproc J) := by
  let guestWidth := wordSize (scratchWordMultiplier c d) J.solverWords
  have hin : ScratchCanonicalInput guestWidth T S J := polynomialScratch_pre T S c d J hS hc hu
  have hkB := scratchWordBound_meetsContract (w := w) hbound J
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hdoubled⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 ^ guestWidth) < 2 ^ w at hspace
  change 2 ^ (guestWidth + 1) + 2 ≤ 2 ^ w at hdoubled
  have hw : guestWidth ≤ w := by
    have hW : 2 ^ guestWidth < 2 ^ w := by omega
    exact Nat.le_of_lt (Nat.pow_lt_pow_iff_right (by decide : 1 < 2) |>.mp hW)
  have hkW := scratchWrapper_meetsContract (hproc J) hdet J hin
    (canonicalWrapperModule_layout hwrap).1 (canonicalWrapperModule_layout hwrap).2.1
    (canonicalWrapperModule_layout hwrap).2.2.1 (canonicalWrapperModule_layout hwrap).2.2.2 hw
  have hsize := J.solverWords_length
  have hlen : J.solverWords.length < 2 ^ guestWidth :=
    hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hl : J.solverWords.length < 2 ^ w := by omega
  have h5m : 5 * J.m < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hfive : 5 < 2 ^ w := by
    have hlen2 : 2 < 2 ^ guestWidth := by omega
    have hp : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
    rw [Nat.pow_succ] at hdoubled
    omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have hmcell : mem (a + 1) = J.m := by
    have hh := hat 1 (by rw [hsize]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ,
      List.getElem_cons_zero] using hh
  apply runs_start_le
  unfold canonicalSolveBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.solverWords.length) (by
    conv_rhs => rw [hsize]
    apply Expr.eval_add (Expr.eval_const htwo)
      (Expr.eval_mul (Expr.eval_const hfive) ?_ h5m) (hsize ▸ hl)
    simp only [Expr.eval_reg, Function.update_self]) ?_
  refine runs_seq_call_le hkB (vs := [a, J.solverWords.length]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨a, rfl, hat, by omega, hdoubled⟩
  · intro W memB posB hpostB
    obtain ⟨hmemB, hW⟩ := hpostB
    change memB = mem at hmemB
    subst memB
    change W = 2 ^ guestWidth at hW
    have hWword : W < 2 ^ w := by omega
    refine runs_seq_call_le hkW (vs := [a, J.solverWords.length, W, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · rw [hW]
      exact ⟨⟨a, heap, rfl, hat, hend⟩, hzero, hspace⟩
    · intro out memW posW hpostW
      rw [hW] at hpostW
      have hptr := hpostW.2
      change out = heap + 1 + 2 ^ guestWidth at hptr
      have hout : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + (1 + 2 ^ guestWidth) ∧
          (∀ x < heap, memW x = mem x) ∧ ZeroFrom memW out ∧
          J.readSolverFlow memW heap = scratchCanonicalSolverAt (wordSize (scratchWordMultiplier c d) J.solverWords) Q f T S (hproc J) J) ∧
          out = heap + 1 + 2 ^ guestWidth
        exact hpostW
      · simp only [scratchSolveContract, heapContract, scratchWordBoundContract,
          scratchWrapperContract, Expr.size_load, Expr.size_bin, Expr.size_reg,
          Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- The installed module meets the canonical call contract using the solver
contract only at the widths selected from circulation encodings. -/
theorem scratchSolveModule_meetsContract
    {w b : ℕ} {Q P : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (solverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hdet : Q.IsDeterministic) (J : Circulation)
    (hS : S J.n J.m ≤ c * (J.n + J.m + 2)^d)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hp : P.HasAt b (scratchSolveModule Q f b c d)) :
    MeetsContract w P b (scratchSolveContract w Q f T S c d hproc J) := by
  apply scratchSolve_meetsContract hproc hdet J hS hc hu hp.head
  · intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [scratchSolveModule, scratchWordBoundModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [scratchSolveModule])
  · intro i hi
    have h := hp (i + 1 + 1) (by simp only [scratchSolveModule, List.length_cons]; omega)
    have hidx : b + (i + 1 + 1) = (b + 2) + i := by omega
    rw [hidx] at h
    simpa only [scratchSolveModule, List.getElem_cons_succ] using h


/-- The complete canonical solve returns the model function with fresh-heap
framing and the costs of guest setup, copying, and the solver itself. -/
def compressedSolveContract (w : ℕ) (Q : Program) (f : ℕ)
    (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, h] ∧ ListAt mem a J.solverWords ∧
      a + J.solverWords.length ≤ h ∧
      2 ^ (wordSize (scratchWordMultiplier c d) J.solverWords + 1) + 2 ≤ 2 ^ w)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args) = compressedCanonicalSolverAt (wordSize (scratchWordMultiplier c d) J.solverWords) Q f T S (hproc J) J)
    (fun _ _ => (Q.regBound + 6) * T J.n J.m +
      80 * J.solverWords.length + 40 * wordSize (scratchWordMultiplier c d) J.solverWords + Q.regBound + 300)
    (fun _ _ => 1 + 2 ^ wordSize (scratchWordMultiplier c d) J.solverWords)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 ^ wordSize (scratchWordMultiplier c d) J.solverWords }

/-- The executable canonical entry computes exactly `canonicalSolver` on
bounded circulations, at the stated setup and solver cost. -/
theorem compressedSolve_meetsContract
    {w entry bound wrapper : ℕ} {Q P : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hn : J.n ≤ 2*J.m+1)
    (hS : S J.n J.m ≤ c * (J.n + J.m + 2)^d)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hentry : P.procs[entry]? = some (canonicalSolveBody bound wrapper))
    (hbound : P.HasAt bound (scratchWordBoundModule (scratchWordMultiplier c d)))
    (hwrap : P.HasAt wrapper (canonicalWrapperModule Q f wrapper)) :
    MeetsContract w P entry (compressedSolveContract w Q f T S c d hproc J) := by
  let guestWidth := wordSize (scratchWordMultiplier c d) J.solverWords
  have hin : CompressedCanonicalInput guestWidth T S J := polynomialScratch_compressed_pre T S c d J hn hS hc hu
  have hkB := scratchWordBound_meetsContract (w := w) hbound J
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hdoubled⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 ^ guestWidth) < 2 ^ w at hspace
  change 2 ^ (guestWidth + 1) + 2 ≤ 2 ^ w at hdoubled
  have hw : guestWidth ≤ w := by
    have hW : 2 ^ guestWidth < 2 ^ w := by omega
    exact Nat.le_of_lt (Nat.pow_lt_pow_iff_right (by decide : 1 < 2) |>.mp hW)
  have hkW := compressedWrapper_meetsContract (hproc J) hdet J hin
    (canonicalWrapperModule_layout hwrap).1 (canonicalWrapperModule_layout hwrap).2.1
    (canonicalWrapperModule_layout hwrap).2.2.1 (canonicalWrapperModule_layout hwrap).2.2.2 hw
  have hsize := J.solverWords_length
  have hlen : J.solverWords.length < 2 ^ guestWidth :=
    hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hl : J.solverWords.length < 2 ^ w := by omega
  have h5m : 5 * J.m < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hfive : 5 < 2 ^ w := by
    have hlen2 : 2 < 2 ^ guestWidth := by omega
    have hp : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
    rw [Nat.pow_succ] at hdoubled
    omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have hmcell : mem (a + 1) = J.m := by
    have hh := hat 1 (by rw [hsize]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ,
      List.getElem_cons_zero] using hh
  apply runs_start_le
  unfold canonicalSolveBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.solverWords.length) (by
    conv_rhs => rw [hsize]
    apply Expr.eval_add (Expr.eval_const htwo)
      (Expr.eval_mul (Expr.eval_const hfive) ?_ h5m) (hsize ▸ hl)
    simp only [Expr.eval_reg, Function.update_self]) ?_
  refine runs_seq_call_le hkB (vs := [a, J.solverWords.length]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨a, rfl, hat, by omega, hdoubled⟩
  · intro W memB posB hpostB
    obtain ⟨hmemB, hW⟩ := hpostB
    change memB = mem at hmemB
    subst memB
    change W = 2 ^ guestWidth at hW
    have hWword : W < 2 ^ w := by omega
    refine runs_seq_call_le hkW (vs := [a, J.solverWords.length, W, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · rw [hW]
      exact ⟨⟨a, heap, rfl, hat, hend⟩, hzero, hspace⟩
    · intro out memW posW hpostW
      rw [hW] at hpostW
      have hptr := hpostW.2
      change out = heap + 1 + 2 ^ guestWidth at hptr
      have hout : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + (1 + 2 ^ guestWidth) ∧
          (∀ x < heap, memW x = mem x) ∧ ZeroFrom memW out ∧
          J.readSolverFlow memW heap = compressedCanonicalSolverAt (wordSize (scratchWordMultiplier c d) J.solverWords) Q f T S (hproc J) J) ∧
          out = heap + 1 + 2 ^ guestWidth
        exact hpostW
      · simp only [compressedSolveContract, heapContract, scratchWordBoundContract,
          compressedWrapperContract, Expr.size_load, Expr.size_bin, Expr.size_reg,
          Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- The installed module meets the canonical call contract using the solver
contract only at the widths selected from circulation encodings. -/
theorem compressedSolveModule_meetsContract
    {w b : ℕ} {Q P : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hn : J.n ≤ 2*J.m+1)
    (hS : S J.n J.m ≤ c * (J.n + J.m + 2)^d)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hp : P.HasAt b (scratchSolveModule Q f b c d)) :
    MeetsContract w P b (compressedSolveContract w Q f T S c d hproc J) := by
  apply compressedSolve_meetsContract hproc hdet J hn hS hc hu hp.head
  · intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [scratchSolveModule, scratchWordBoundModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [scratchSolveModule])
  · intro i hi
    have h := hp (i + 1 + 1) (by simp only [scratchSolveModule, List.length_cons]; omega)
    have hidx : b + (i + 1 + 1) = (b + 2) + i := by omega
    rw [hidx] at h
    simpa only [scratchSolveModule, List.getElem_cons_succ] using h

end MinCostFlow.Final
