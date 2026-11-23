module

public import MinCostFlow.LSF.Program.TreeDist
public import MinCostFlow.LSF.Program.CongScatterBase

/-!
# The tree distance of the ends of every edge

`duvProc` runs `treeDistProc` for every edge position `t < m0`, with end indices `eu t` and
`ev t`, and writes the result into the block `duv t`. The cost is `O(m0 (logCap + LB))`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

/-- One edge (register `10` is `t`). Registers: `11 = eu t`, `12 = ev t`. -/
def duvBody (bDist : ℕ) : Stmt :=
  .assign 11 (.load (.bin .add (.reg 1) (.reg 10))) ;;
  .assign 12 (.load (.bin .add (.reg 2) (.reg 10))) ;;
  .call 13 bDist [.bin .add (.reg 3) (.bin .mul (.reg 10) (.reg 5)), .reg 11, .reg 12, .reg 4,
    .reg 5, .reg 6, .reg 7, .reg 8, .reg 9]

/-- Args: `[m0, euPtr, evPtr, duvBase, ldBase, LB, logCap, upPtr, depPtr, parPtr]`. -/
def duvProc (bDist : ℕ) : Stmt :=
  forRange 10 (.const 0) (.reg 0) (duvBody bDist) ;;
  .ret (.const 0)

lemma duvProc_noRand (bDist : ℕ) : (duvProc bDist).NoRand := by
  simp [duvProc, duvBody, forRange, forUp, Stmt.NoRand]

/-- What `duvProc` gives for the edge position `t`: the block holds `distMod` of the weighted
depths of the ends and of some index `l`, and `l` is the lowest common ancestor index for every
choice of tree arrays that the memory describes. -/
def DuvOut (w h : ℕ) (mem mem' : ℕ → ℕ) (euPtr evPtr duvBase ldBase LB logCap upPtr depPtr
    parPtr t : ℕ) : Prop :=
  Valid mem' (duvBase + t * LB) h LB ∧
  ∃ l, unsignedVal mem' (duvBase + t * LB) h LB =
      distMod (capacity h LB) (unsignedVal mem (ldBase + mem (euPtr + t) * LB) h LB)
        (unsignedVal mem (ldBase + mem (evPtr + t) * LB) h LB)
        (unsignedVal mem (ldBase + l * LB) h LB) ∧
    ∀ (n tM r : ℕ) (tl hd par pe dep : ℕ → ℕ), RootedArrays n tM r tl hd par pe dep →
      mem (euPtr + t) < n → mem (evPtr + t) < n →
      LcaTables w n logCap upPtr depPtr parPtr par dep mem →
      upPtr + n * logCap ≤ duvBase → depPtr + n ≤ duvBase → parPtr + n ≤ duvBase →
      l < n ∧ IsLcaOf par dep l (mem (euPtr + t)) (mem (evPtr + t))

/-- The contract of `duvProc`. Everything that is read lies below the blocks `duv`. -/
def duvContract (w h : ℕ) : Contract where
  pre args mem := ∃ (m0 euPtr evPtr duvBase ldBase LB logCap upPtr depPtr parPtr n tM r : ℕ)
      (tl hd par pe dep : ℕ → ℕ),
    args = [m0, euPtr, evPtr, duvBase, ldBase, LB, logCap, upPtr, depPtr, parPtr] ∧
    16 ≤ 2 ^ w ∧ RootedArrays n tM r tl hd par pe dep ∧
    LcaTables w n logCap upPtr depPtr parPtr par dep mem ∧
    (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧
    (∀ x < n, Valid mem (ldBase + x * LB) h LB) ∧
    euPtr + m0 ≤ duvBase ∧ evPtr + m0 ≤ duvBase ∧ ldBase + n * LB ≤ duvBase ∧
    upPtr + n * logCap ≤ duvBase ∧ depPtr + n ≤ duvBase ∧ parPtr + n ≤ duvBase ∧
    duvBase + m0 * LB < 2 ^ w
  post args mem ret mem' := ∃ (m0 euPtr evPtr duvBase ldBase LB logCap upPtr depPtr parPtr : ℕ),
    args = [m0, euPtr, evPtr, duvBase, ldBase, LB, logCap, upPtr, depPtr, parPtr] ∧ ret = 0 ∧
    (∀ a, a < duvBase ∨ duvBase + m0 * LB ≤ a → mem' a = mem a) ∧
    ∀ t < m0, DuvOut w h mem mem' euPtr evPtr duvBase ldBase LB logCap upPtr depPtr parPtr t
  cost args _ := args.getD 0 0 * (100 * args.getD 6 0 + 400 * args.getD 5 0 + 400) + 20

theorem duv_meetsContract {w h : ℕ} {p : Program} {b bDist : ℕ}
    (hDist : MeetsContract w p bDist (treeDistContract w h))
    (hp : p.procs[b]? = some (duvProc bDist)) :
    MeetsContract w p b (duvContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m0, euPtr, evPtr, duvBase, ldBase, LB, logCap, upPtr, depPtr, parPtr, n, tM, r, tl, hd,
    par, pe, dep, rfl, h16, hR, hT, hend, hld, heu, hev, hldp, hup, hdp, hpp, hdw⟩ := hpre
  set args := [m0, euPtr, evPtr, duvBase, ldBase, LB, logCap, upPtr, depPtr, parPtr] with hargs
  have hm0w : m0 < 2 ^ w := hwords m0 (by simp [hargs])
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 10, st.regs i = args.getD i 0) ∧ st.regs 10 = j ∧
    (∀ a, a < duvBase ∨ duvBase + j * LB ≤ a → st.mem a = mem a) ∧
    ∀ t < j, DuvOut w h mem st.mem euPtr evPtr duvBase ldBase LB logCap upPtr depPtr parPtr t
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 10 (.const 0) (.reg 0) (duvBody bDist)) (normalPost (Inv m0))
      (fun _ => (m0 - 0) * ((100 * logCap + 400 * LB + 390) + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (100 * logCap + 400 * LB + 390) 0 m0 (by omega) hw1
      (fun _ => hm0w) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl,
        fun t ht => absurd ht (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 10 by omega)]
      interval_cases i <;> simp [startState, hargs]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = m0 := hI.1 0 (by omega)
      eval_expr
    · intro t _ htm st ω' hI
      obtain ⟨hRg, h10, hfr, hdone⟩ := hI
      have r1 : st.regs 1 = euPtr := hRg 1 (by omega)
      have r2 : st.regs 2 = evPtr := hRg 2 (by omega)
      have r3 : st.regs 3 = duvBase := hRg 3 (by omega)
      have r4 : st.regs 4 = ldBase := hRg 4 (by omega)
      have r5 : st.regs 5 = LB := hRg 5 (by omega)
      have r6 : st.regs 6 = logCap := hRg 6 (by omega)
      have r7 : st.regs 7 = upPtr := hRg 7 (by omega)
      have r8 : st.regs 8 = depPtr := hRg 8 (by omega)
      have r9 : st.regs 9 = parPtr := hRg 9 (by omega)
      have hbt := blk_end LB htm
      have hlow : ∀ a, a < duvBase → st.mem a = mem a := fun a ha => hfr a (Or.inl ha)
      obtain ⟨hun, hvn⟩ := hend t htm
      set u := mem (euPtr + t) with hu
      set v := mem (evPtr + t) with hv
      have hmu : st.mem (euPtr + t) = u := hlow _ (by omega)
      have hmv : st.mem (evPtr + t) = v := hlow _ (by omega)
      have hT' : LcaTables w n logCap upPtr depPtr parPtr par dep st.mem :=
        hT.of_agree (B := duvBase) hlow hup hdp hpp
      have hldv : ∀ z < n, Valid st.mem (ldBase + z * LB) h LB ∧
          unsignedVal st.mem (ldBase + z * LB) h LB = unsignedVal mem (ldBase + z * LB) h LB := by
        intro z hz
        have := blk_end LB hz
        have hag : ∀ i < LB, st.mem (ldBase + z * LB + i) = mem (ldBase + z * LB + i) :=
          fun i hi => hlow _ (by omega)
        exact ⟨fun i hi => by rw [hag i hi]; exact hld z hz i hi, unsignedVal_congr hag⟩
      have hnw : n < 2 ^ w := by omega
      refine runs_start_le ?_
      unfold duvBody
      refine runs_seq_assign_le (v := u) (by rw [← hmu]; eval_expr) ?_
      refine runs_seq_assign_le (v := v) (by rw [← hmv]; eval_expr) ?_
      refine runs_call_le (vs := [duvBase + t * LB, u, v, ldBase, LB, logCap, upPtr, depPtr,
          parPtr]) hDist
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons
            (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
              (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))))
        (by
          have b1 : duvBase + t * LB < 2 ^ w := by omega
          have b2 : u < 2 ^ w := by omega
          have b3 : v < 2 ^ w := by omega
          have b4 : ldBase < 2 ^ w := by omega
          have b5 : LB < 2 ^ w := hwords LB (by simp [hargs])
          have b6 : logCap < 2 ^ w := hwords logCap (by simp [hargs])
          have b7 : upPtr < 2 ^ w := by omega
          have b8 : depPtr < 2 ^ w := by omega
          have b9 : parPtr < 2 ^ w := by omega
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h | h | h | h | h | h | h <;> rw [h] <;> assumption)
        ⟨_, _, _, _, _, _, _, _, _, n, tM, r, tl, hd, par, pe, dep, rfl, h16, hR, hun, hvn, hT',
          fun z hz => (hldv z hz).1, Or.inr (by omega), by omega, by omega⟩ ?_
      rintro l mem₁ pos₁ ⟨d₁, x₁, y₁, a₁, L₁, c₁, e₁, f₁, g₁, heq₁, hfr₁, hv₁, hu₁, hlca⟩
      simp only [List.cons.injEq, and_true] at heq₁
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
      obtain ⟨hln, -⟩ := hlca n tM r tl hd par pe dep hR hun hvn hT'
      refine ⟨⟨⟨fun i hi => ?_, ?_, fun a ha => ?_, fun t' ht' => ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        simp only [Function.update_of_ne (show i ≠ 10 by omega),
          Function.update_of_ne (show i ≠ 13 by omega), Function.update_of_ne (show i ≠ 12 by omega),
          Function.update_of_ne (show i ≠ 11 by omega)]
        exact hRg i hi
      · simp
      · dsimp only
        have hs : (t + 1) * LB = t * LB + LB := Nat.succ_mul t LB
        rw [hfr₁ a (by omega)]
        exact hfr a (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
        · have hb' := blk_end LB ht'
          have hd' := blk_disj LB (show t' ≠ t by omega)
          have hag : ∀ i < LB, mem₁ (duvBase + t' * LB + i) = st.mem (duvBase + t' * LB + i) :=
            fun i hi => hfr₁ _ (by omega)
          obtain ⟨hv', l', hu', hl'⟩ := hdone t' ht'
          exact ⟨fun i hi => by rw [hag i hi]; exact hv' i hi, l', by
            rw [unsignedVal_congr hag, hu'], hl'⟩
        · refine ⟨hv₁, l, ?_, fun n' tM' r' tl' hd' par' pe' dep' hR' hx' hy' hT'' => ?_⟩
          · rw [hu₁, (hldv u hun).2, (hldv v hvn).2, (hldv l hln).2]
          · intro h1 h2 h3
            exact hlca n' tM' r' tl' hd' par' pe' dep' hR' hx' hy'
              (hT''.of_agree (B := duvBase) (fun a ha => (hlow a ha)) h1 h2 h3)
      · simp only [Function.update_of_ne (show (10 : ℕ) ≠ 13 by omega),
          Function.update_of_ne (show (10 : ℕ) ≠ 12 by omega),
          Function.update_of_ne (show (10 : ℕ) ≠ 11 by omega)]
        exact h10
      · simp only [treeDistContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
          Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        omega
  refine runs_start_le ?_
  unfold duvProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨m0, euPtr, evPtr, duvBase, ldBase, LB, logCap,
    upPtr, depPtr, parPtr, rfl, rfl, hfr, hdone⟩ ?_
  simp only [duvContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg]
  have h1 : (m0 - 0) * (100 * logCap + 400 * LB + 390 + 1 + 8) ≤
      m0 * (100 * logCap + 400 * LB + 400) := Nat.mul_le_mul (by omega) (by omega)
  omega

end

end MinCostFlow.LSF.Program
