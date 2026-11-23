module

public import MinCostFlow.LSF.Program.InitSegE
public import MinCostFlow.LSF.Program.StoreArgs

/-!
# The init driver, steps `65 … 67`

The last segment writes the header of the aux block (`20` words after `auxPtr`) and the header
of the state (`24` words after the handle `b`), and computes the end `useEnd` of the used memory,
which the body returns. Two words of the state header are read from memory: the number of roots
at `fAncPtr` and the root `r₀` at the start of the vertex list.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- The `20` words of the aux header. -/
def auxHdrVals (V : InitVals) : List ℕ :=
  let base := V.auxPtr + auxHdrSize
  let vl := base + V.vCap
  let par := vl + V.n0
  let pti := par + V.n0
  let dep := pti + V.n0
  let upV := dep + V.n0
  let upMin := upV + V.n0 * auxLogCap V.n0
  let thP := upMin + V.n0 * auxLogCap V.n0
  let ov := thP + V.n0
  let iov := ov + V.vCap
  let qa := iov + V.vCap
  let qb := qa + V.vCap
  let va := qb + V.vCap
  let vb := va + V.vCap
  let ts := vb + V.vCap
  let fs := ts + (hldDepthBound V.n0 + 2)
  [base, vl, par, pti, dep, auxLogCap V.n0, upV, upMin, thP, ov, iov, qa, qb, va, vb, ts, fs, 0,
    0, 0]

/-- The `24` words of the state header. `nR` and `r₀` are read from memory. -/
def lsfHdrVals (V : InitVals) (h P_fp kk nR r₀ : ℕ) : List ℕ :=
  [V.vCap, V.eCap, V.n0, V.m0, V.gPtr, V.tPtr, V.fPtr, V.fAncPtr, V.wPtr, V.numSt, V.denSt,
    V.L_w, h, P_fp, V.L_in, 0, nR, 0, V.auxPtr, V.endA, r₀, kk, V.tM, 0]

/-- The cost of the last segment. -/
def segFCost : ℕ := 1700

lemma InitVals.auxHdr_le (V : InitVals) :
    V.auxPtr + auxHdrSize + V.vCap + V.n0 + V.n0 + V.n0 + V.n0 + V.n0 * auxLogCap V.n0 +
      V.n0 * auxLogCap V.n0 + V.n0 + V.vCap + V.vCap + V.vCap + V.vCap + V.vCap + V.vCap +
      (hldDepthBound V.n0 + 2) ≤ V.endA := by
  obtain ⟨-, -, -, -, -, -, e7, e8, e9, -⟩ := V.aux_order
  simp only [auxSize] at e7
  omega

/-- The places of the static blocks are below `endA`. -/
lemma InitVals.static_le (V : InitVals) :
    V.b + 24 = V.gPtr ∧ V.gPtr + 4 + 7 * V.vCap + 9 * V.eCap ≤ V.tPtr ∧ V.tPtr ≤ V.fPtr ∧
    V.fPtr ≤ V.fAncPtr ∧ V.fAncPtr + 6 + 5 * V.vCap ≤ V.wPtr ∧ V.wPtr ≤ V.auxPtr ∧
    V.auxPtr + 20 + V.vCap = V.vListPtr ∧ V.vListPtr + V.n0 ≤ V.numSt ∧ V.numSt ≤ V.denSt ∧
    V.denSt ≤ V.endA := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hvI : V.vIdx = V.auxPtr + 20 := rfl
  simp only [dynGraphSize, fAncSize, tBlockSize, auxSize, auxHdrSize, lsfHdrSize, wBlockSize,
    fAncHdrSize, wHdrSize, tHdrSize] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

lemma auxHdrVals_lt {w : ℕ} (V : InitVals) (hW : V.endA < 2 ^ w) (hn1 : 1 ≤ V.n0) :
    ∀ x ∈ V.auxPtr :: auxHdrVals V, x < 2 ^ w := by
  have hF := V.auxHdr_le
  have hl : auxLogCap V.n0 ≤ V.n0 * auxLogCap V.n0 := Nat.le_mul_of_pos_left _ hn1
  dsimp only [auxHdrVals]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  simp only [auxHdrSize] at hF ⊢
  have := Nat.two_pow_pos w
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega

set_option maxHeartbeats 1000000 in
lemma auxHdr_eval {w : ℕ} {regs mem : ℕ → ℕ} (V : InitVals) (hW : V.endA < 2 ^ w)
    (r7 : regs 7 = V.vCap) (a10 : regs 10 = V.n0) (a15 : regs 15 = auxLogCap V.n0)
    (a16 : regs 16 = hldDepthBound V.n0) (a25 : regs 25 = V.auxPtr) :
    evalArgsAt w regs mem auxHdrArgs = some (V.auxPtr :: auxHdrVals V) := by
  have hF := V.auxHdr_le
  simp only [auxHdrSize] at hF
  show evalArgs _ _ _ = _
  dsimp only [auxHdrArgs, auxHdrVals, rAux, rVc, rN, rLog, rD]
  eval_expr
  all_goals (try simp only [auxHdrSize])
  all_goals omega

lemma lsfHdrVals_lt {w h P_fp kk nR r₀ : ℕ} (V : InitVals) (hW : V.endA < 2 ^ w)
    (hLw : V.L_w < 2 ^ w) (hLin : V.L_in < 2 ^ w) (hm : V.m0 < 2 ^ w) (hh : h < 2 ^ w)
    (hP : P_fp < 2 ^ w) (hk : kk < 2 ^ w) (hR : nR < 2 ^ w) (hr : r₀ < 2 ^ w) :
    ∀ x ∈ V.b :: lsfHdrVals V h P_fp kk nR r₀, x < 2 ^ w := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := V.static_le
  have htM : V.tM ≤ V.n0 := Nat.sub_le _ _
  have := Nat.two_pow_pos w
  simp only [lsfHdrVals, List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega

lemma lsfHdr_eval {w h P_fp kk : ℕ} {regs mem : ℕ → ℕ} (V : InitVals) (hh : h < 2 ^ w)
    (r4 : regs 4 = P_fp) (r5 : regs 5 = kk) (r6 : regs 6 = V.L_w) (r3 : regs 3 = V.L_in)
    (r7 : regs 7 = V.vCap) (r8 : regs 8 = V.eCap) (r9 : regs 9 = V.b)
    (a10 : regs 10 = V.n0) (a11 : regs 11 = V.m0) (a12 : regs 12 = V.tM)
    (a20 : regs 20 = V.gPtr) (a21 : regs 21 = V.tPtr) (a22 : regs 22 = V.fPtr)
    (a23 : regs 23 = V.fAncPtr) (a24 : regs 24 = V.wPtr) (a25 : regs 25 = V.auxPtr)
    (a26 : regs 26 = V.numSt) (a27 : regs 27 = V.denSt) (a28 : regs 28 = V.endA)
    (c52 : regs 52 = V.vListPtr) :
    evalArgsAt w regs mem (lsfHdrArgs h) =
      some (V.b :: lsfHdrVals V h P_fp kk (mem V.fAncPtr) (mem V.vListPtr)) := by
  show evalArgs _ _ _ = _
  dsimp only [lsfHdrArgs, lsfHdrVals, rB, rVc, rEc, rN, rM, rGP, rTP, rFP, rFA, rWP, rNumSt,
    rDenSt, rLw, rPfp, rLin, rAux, rEnd, rVL, rKn, rTM]
  eval_expr

lemma useEnd_eval {w : ℕ} {regs mem : ℕ → ℕ} (V : InitVals) (hU : V.useEnd < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) (hn1 : 1 ≤ V.n0)
    (a10 : regs 10 = V.n0) (a15 : regs 15 = auxLogCap V.n0) (a73 : regs 73 = V.wBase) :
    evalAt w regs mem (add (r rWB) (add (mul (r rN) (mul (k 3) (r rLog))) (mul (k 3) (r rN)))) =
      some V.useEnd := by
  have hn : 3 * auxLogCap V.n0 ≤ V.n0 * (3 * auxLogCap V.n0) := Nat.le_mul_of_pos_left _ hn1
  have hl : 1 ≤ auxLogCap V.n0 := by unfold auxLogCap; omega
  simp only [InitVals.useEnd, wWorkSize] at hU ⊢
  show Expr.eval _ _ _ = _
  dsimp only [rWB, rN, rLog]
  eval_expr
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem segF_wp {w h : ℕ} {p : Program} {I : InitIdx} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {regs mem : ℕ → ℕ} {B P_fp kk nOrig : ℕ} (V : InitVals)
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    (r4 : regs rPfp = P_fp) (r5 : regs rKn = kk) (r6 : regs rLw = V.L_w)
    (r3 : regs rLin = V.L_in) (r7 : regs rVc = V.vCap) (r8 : regs rEc = V.eCap)
    (r9 : regs rB = V.b)
    (hA : ∀ j < 19, regs (10 + j) = (segAVals V).getD j 0)
    (hCv : ∀ j < 14, regs (50 + j) = (segCVals V nOrig).getD j 0)
    (a73 : regs 73 = V.wBase)
    (hw16 : 16 ≤ 2 ^ w) (hn1 : 1 ≤ V.n0) (hW : V.endA < 2 ^ w) (hU : V.useEnd < 2 ^ w) (hLw : V.L_w < 2 ^ w)
    (hLin : V.L_in < 2 ^ w) (hm : V.m0 < 2 ^ w) (hh : h < 2 ^ w) (hPw : P_fp < 2 ^ w)
    (hk : kk < 2 ^ w) (hFA : mem V.fAncPtr < 2 ^ w) (hVL : mem V.vListPtr < 2 ^ w)
    (hB : segFCost ≤ B)
    (hnext : ∀ v₁ mem₁ v₂ mem₂ regs',
      (storeArgsContract w 20).post (V.auxPtr :: auxHdrVals V) mem v₁ mem₁ →
      (storeArgsContract w 24).post
        (V.b :: lsfHdrVals V h P_fp kk (mem V.fAncPtr) (mem V.vListPtr)) mem₁ v₂ mem₂ →
      (∀ j < 75, regs' j = regs j) → regs' 77 = V.useEnd →
      P regs' mem₂ (B - segFCost)) :
    SeqWPR w p 10 P 65 (segF I h) regs mem B := by
  have a10 : regs 10 = V.n0 := hA 0 (by omega)
  have a11 : regs 11 = V.m0 := hA 1 (by omega)
  have a12 : regs 12 = V.tM := hA 2 (by omega)
  have a15 : regs 15 = auxLogCap V.n0 := hA 5 (by omega)
  have a16 : regs 16 = hldDepthBound V.n0 := hA 6 (by omega)
  have a20 : regs 20 = V.gPtr := hA 10 (by omega)
  have a21 : regs 21 = V.tPtr := hA 11 (by omega)
  have a22 : regs 22 = V.fPtr := hA 12 (by omega)
  have a23 : regs 23 = V.fAncPtr := hA 13 (by omega)
  have a24 : regs 24 = V.wPtr := hA 14 (by omega)
  have a25 : regs 25 = V.auxPtr := hA 15 (by omega)
  have a26 : regs 26 = V.numSt := hA 16 (by omega)
  have a27 : regs 27 = V.denSt := hA 17 (by omega)
  have a28 : regs 28 = V.endA := hA 18 (by omega)
  have c52 : regs 52 = V.vListPtr := hCv 2 (by omega)
  have hF := V.auxHdr_le
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := V.static_le
  have hsz1 : argsSize auxHdrArgs ≤ 600 := by simp [auxHdrArgs, argsSize, Expr.size]
  have hsz2 : argsSize (lsfHdrArgs h) ≤ 600 := by simp [lsfHdrArgs, argsSize, Expr.size]
  have hsz3 : (add (r rWB) (add (mul (r rN) (mul (k 3) (r rLog))) (mul (k 3) (r rN)))).size ≤
    20 := by simp [Expr.size]
  unfold segFCost at hB
  simp only [segF]
  -- step 65: the aux header
  refine SeqWPR.call hP (storeArgsContract w 20) (V.auxPtr :: auxHdrVals V) 800 hs20
    (auxHdr_eval V hW r7 a10 a15 a16 a25) (auxHdrVals_lt V hW hn1)
    ⟨V.auxPtr, auxHdrVals V, rfl, rfl, by simp only [auxHdrSize] at hF; omega⟩
    (by simp only [storeArgsContract]; omega) (by omega) ?_
  intro v₁ mem₁ hpost₁
  have hpost₁' := hpost₁
  obtain ⟨b₁, vs₁, heq₁, -, -, hfr₁⟩ := hpost₁
  simp only [List.cons.injEq] at heq₁
  obtain ⟨rfl, rfl⟩ := heq₁
  have m1 : mem₁ V.fAncPtr = mem V.fAncPtr := hfr₁ _ (Or.inl (by omega))
  have m2 : mem₁ V.vListPtr = mem V.vListPtr := hfr₁ _ (Or.inr (by omega))
  have u : ∀ j, j ≠ 75 → Function.update regs (10 + 65) v₁ j = regs j :=
    fun j hj => Function.update_of_ne hj _ _
  -- step 66: the state header
  refine SeqWPR.call hP (storeArgsContract w 24)
    (V.b :: lsfHdrVals V h P_fp kk (mem V.fAncPtr) (mem V.vListPtr)) 800 hs24
    (by
      rw [← m1, ← m2]
      exact lsfHdr_eval V hh ((u 4 (by omega)).trans r4) ((u 5 (by omega)).trans r5)
        ((u 6 (by omega)).trans r6) ((u 3 (by omega)).trans r3) ((u 7 (by omega)).trans r7)
        ((u 8 (by omega)).trans r8) ((u 9 (by omega)).trans r9) ((u 10 (by omega)).trans a10)
        ((u 11 (by omega)).trans a11) ((u 12 (by omega)).trans a12)
        ((u 20 (by omega)).trans a20) ((u 21 (by omega)).trans a21)
        ((u 22 (by omega)).trans a22) ((u 23 (by omega)).trans a23)
        ((u 24 (by omega)).trans a24) ((u 25 (by omega)).trans a25)
        ((u 26 (by omega)).trans a26) ((u 27 (by omega)).trans a27)
        ((u 28 (by omega)).trans a28) ((u 52 (by omega)).trans c52))
    (lsfHdrVals_lt V hW hLw hLin hm hh hPw hk hFA hVL)
    ⟨V.b, _, rfl, rfl, by omega⟩
    (by simp only [storeArgsContract]; omega) (by omega) ?_
  intro v₂ mem₂ hpost₂
  have u2 : ∀ j, j ≠ 75 → j ≠ 76 →
      Function.update (Function.update regs (10 + 65) v₁) (10 + (65 + 1)) v₂ j = regs j :=
    fun j hj hj' => by rw [Function.update_of_ne hj', Function.update_of_ne hj]
  -- step 67: the end of the used memory
  refine SeqWPR.assign hP V.useEnd _
    (useEnd_eval V hU hw16 hn1 ((u2 10 (by omega) (by omega)).trans a10)
      ((u2 15 (by omega) (by omega)).trans a15) ((u2 73 (by omega) (by omega)).trans a73))
    le_rfl (by omega) ?_
  refine hP _ _ _ _ ?_ (hnext v₁ mem₁ v₂ mem₂ _ hpost₁' hpost₂ (fun j hj => ?_) ?_)
  · unfold segFCost
    omega
  · rw [Function.update_of_ne (by omega)]; exact u2 j (by omega) (by omega)
  · rw [Function.update_apply, if_pos rfl]

end

end MinCostFlow.LSF.Program
