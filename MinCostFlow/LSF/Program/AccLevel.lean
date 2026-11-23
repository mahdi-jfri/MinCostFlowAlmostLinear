module

public import MinCostFlow.LSF.Program.AccEdge
public import MinCostFlow.LSF.Program.TopDownPass

/-!
# One level of the stretch sum, over all edges

`accLevelProc` runs `accEdgeProc` for each edge position `t < m0`, with end indices
`u = eu t`, `v = ev t`, the forest roots `rt u`, `rt v` of the current level and the blocks
`dR u`, `dR v` of the distances to the roots. Each accumulator block gets the value
`accLevelVal` of `AccEdge.lean`. The cost is `O(m0 LB)`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- One edge (register `8` is `t`). Registers: `10 = u`, `11 = v`, `12 = rt u`, `13 = rt v`. -/
def accLevelBody (bEdge : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.reg 8))) ;;
  .assign 12 (.load (.bin .add (.reg 3) (.reg 10))) ;;
  .assign 13 (.load (.bin .add (.reg 3) (.reg 11))) ;;
  .call 14 bEdge [.bin .add (.reg 6) (.bin .mul (.reg 8) (.reg 7)),
    .bin .add (.reg 5) (.bin .mul (.reg 8) (.reg 7)),
    .bin .add (.reg 4) (.bin .mul (.reg 10) (.reg 7)),
    .bin .add (.reg 4) (.bin .mul (.reg 11) (.reg 7)), .reg 7, .reg 12, .reg 13]

/-- Args: `[m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase, LB]`. -/
def accLevelProc (bEdge : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 0) (accLevelBody bEdge) ;;
  .ret (.const 0)

lemma accLevelProc_noRand (bEdge : ℕ) : (accLevelProc bEdge).NoRand := by
  simp [accLevelProc, accLevelBody, forRange, forUp, Stmt.NoRand]

/-- The value of the accumulator of edge position `t` after one level. -/
def accLevelAt (h LB : ℕ) (mem : ℕ → ℕ) (euPtr evPtr rtPtr dRBase duvBase accBase t : ℕ) : ℕ :=
  let u := mem (euPtr + t)
  let v := mem (evPtr + t)
  let dR := fun z => unsignedVal mem (dRBase + z * LB) h LB
  accLevelVal (capacity h LB) (unsignedVal mem (accBase + t * LB) h LB)
    (unsignedVal mem (duvBase + t * LB) h LB) (dR u) (dR v) (mem (rtPtr + u)) (mem (rtPtr + v))

/-- The contract of `accLevelProc`. Everything that is read lies below the accumulators. -/
def accLevelContract (w h : ℕ) : Contract where
  pre args mem := ∃ (m0 euPtr evPtr rtPtr dRBase duvBase accBase LB n : ℕ),
    args = [m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase, LB] ∧ 16 ≤ 2 ^ w ∧
    (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧ (∀ x < n, mem (rtPtr + x) < n) ∧
    (∀ x < n, Valid mem (dRBase + x * LB) h LB) ∧
    (∀ t < m0, Valid mem (duvBase + t * LB) h LB ∧ Valid mem (accBase + t * LB) h LB) ∧
    euPtr + m0 ≤ accBase ∧ evPtr + m0 ≤ accBase ∧ rtPtr + n ≤ accBase ∧
    dRBase + n * LB ≤ accBase ∧ duvBase + m0 * LB ≤ accBase ∧ accBase + m0 * LB < 2 ^ w
  post args mem ret mem' := ∃ (m0 euPtr evPtr rtPtr dRBase duvBase accBase LB : ℕ),
    args = [m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase, LB] ∧ ret = 0 ∧
    (∀ a, a < accBase ∨ accBase + m0 * LB ≤ a → mem' a = mem a) ∧
    ∀ t < m0, Valid mem' (accBase + t * LB) h LB ∧
      unsignedVal mem' (accBase + t * LB) h LB =
        accLevelAt h LB mem euPtr evPtr rtPtr dRBase duvBase accBase t
  cost args _ := args.getD 0 0 * (150 * args.getD 7 0 + 160) + 20

theorem accLevel_meetsContract {w h : ℕ} {p : Program} {b bEdge : ℕ}
    (hEdge : MeetsContract w p bEdge (accEdgeContract w h))
    (hp : p.procs[b]? = some (accLevelProc bEdge)) :
    MeetsContract w p b (accLevelContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase, LB, n, rfl, h16, hend, hrt, hdR, hblk,
    heu, hev, hrtp, hdRp, hduvp, haccw⟩ := hpre
  set args := [m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase, LB] with hargs
  have hm0w : m0 < 2 ^ w := hwords m0 (by simp [hargs])
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 8, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧
    (∀ a, a < accBase ∨ accBase + j * LB ≤ a → st.mem a = mem a) ∧
    ∀ t < j, Valid st.mem (accBase + t * LB) h LB ∧
      unsignedVal st.mem (accBase + t * LB) h LB =
        accLevelAt h LB mem euPtr evPtr rtPtr dRBase duvBase accBase t
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 8 (.const 0) (.reg 0) (accLevelBody bEdge)) (normalPost (Inv m0))
      (fun _ => (m0 - 0) * ((150 * LB + 150) + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (150 * LB + 150) 0 m0 (by omega) hw1 (fun _ => hm0w) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl,
        fun t ht => absurd ht (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 8 by omega)]
      interval_cases i <;> simp [startState, hargs]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = m0 := hI.1 0 (by omega)
      eval_expr
    · intro t _ htm st ω' hI
      obtain ⟨hR, h8, hfr, hdone⟩ := hI
      have r1 : st.regs 1 = euPtr := hR 1 (by omega)
      have r2 : st.regs 2 = evPtr := hR 2 (by omega)
      have r3 : st.regs 3 = rtPtr := hR 3 (by omega)
      have r4 : st.regs 4 = dRBase := hR 4 (by omega)
      have r5 : st.regs 5 = duvBase := hR 5 (by omega)
      have r6 : st.regs 6 = accBase := hR 6 (by omega)
      have r7 : st.regs 7 = LB := hR 7 (by omega)
      have hbt := blk_end LB htm
      have hlow : ∀ a, a < accBase → st.mem a = mem a := fun a ha => hfr a (Or.inl ha)
      obtain ⟨hun, hvn⟩ := hend t htm
      set u := mem (euPtr + t) with hu
      set v := mem (evPtr + t) with hv
      have hru := hrt u hun
      have hrv := hrt v hvn
      set ru := mem (rtPtr + u) with hrudef
      set rv := mem (rtPtr + v) with hrvdef
      have hmu : st.mem (euPtr + t) = u := hlow _ (by omega)
      have hmv : st.mem (evPtr + t) = v := hlow _ (by omega)
      have hmru : st.mem (rtPtr + u) = ru := hlow _ (by omega)
      have hmrv : st.mem (rtPtr + v) = rv := hlow _ (by omega)
      have hbu := blk_end LB hun
      have hbv := blk_end LB hvn
      have hbru := blk_end LB hru
      have hbrv := blk_end LB hrv
      have hbn : n * LB ≤ accBase := by omega
      have hbm : m0 * LB < 2 ^ w := by omega
      -- the source blocks
      have hsrc : ∀ a, a + LB ≤ accBase → Valid mem a h LB →
          SrcBlock w h st.mem (accBase + t * LB) a LB ∧
            unsignedVal st.mem a h LB = unsignedVal mem a h LB := by
        intro a ha hva
        have hag : ∀ i < LB, st.mem (a + i) = mem (a + i) := fun i hi => hlow _ (by omega)
        exact ⟨⟨fun i hi => by rw [hag i hi]; exact hva i hi, Or.inl (by omega), by omega⟩,
          unsignedVal_congr hag⟩
      have hsd := hsrc (duvBase + t * LB) (by omega) (hblk t htm).1
      have hsu := hsrc (dRBase + u * LB) (by omega) (hdR u hun)
      have hsv := hsrc (dRBase + v * LB) (by omega) (hdR v hvn)
      have hacc : ∀ i < LB, st.mem (accBase + t * LB + i) = mem (accBase + t * LB + i) :=
        fun i hi => hfr _ (Or.inr (by omega)) |>.trans rfl
      refine runs_start_le ?_
      unfold accLevelBody
      refine runs_seq_assign_le (v := u) (by rw [← hmu]; eval_expr) ?_
      refine runs_seq_assign_le (v := v) (by rw [← hmv]; eval_expr) ?_
      refine runs_seq_assign_le (v := ru) (by rw [← hmru]; eval_expr) ?_
      refine runs_seq_assign_le (v := rv) (by rw [← hmrv]; eval_expr) ?_
      refine runs_call_le (vs := [accBase + t * LB, duvBase + t * LB, dRBase + u * LB,
          dRBase + v * LB, LB, ru, rv]) hEdge
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons
            (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
        (by
          have b1 : accBase + t * LB < 2 ^ w := by omega
          have b2 : duvBase + t * LB < 2 ^ w := by omega
          have b3 : dRBase + u * LB < 2 ^ w := by omega
          have b5 : dRBase + v * LB < 2 ^ w := by omega
          have b7 : LB < 2 ^ w := hwords LB (by simp [hargs])
          have b8 : ru < 2 ^ w := by omega
          have b9 : rv < 2 ^ w := by omega
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h | h | h | h | h <;> rw [h] <;> assumption)
        ⟨_, _, _, _, _, _, _, rfl,
          fun i hi => by rw [hacc i hi]; exact (hblk t htm).2 i hi, by omega,
          hsd.1, hsu.1, hsv.1⟩ ?_
      rintro v₁ mem₁ pos₁ ⟨d₁, a₁, b₁, c₁, L₁, x₁, y₁, heq₁, -, hfr₁, hv₁, hu₁⟩
      simp only [List.cons.injEq, and_true] at heq₁
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
      have hU0 : unsignedVal st.mem (accBase + t * LB) h LB =
          unsignedVal mem (accBase + t * LB) h LB := unsignedVal_congr hacc
      refine ⟨⟨⟨fun i hi => ?_, ?_, fun a ha => ?_, fun t' ht' => ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        simp only [Function.update_of_ne (show i ≠ 8 by omega),
          Function.update_of_ne (show i ≠ 14 by omega), Function.update_of_ne (show i ≠ 13 by omega),
          Function.update_of_ne (show i ≠ 12 by omega), Function.update_of_ne (show i ≠ 11 by omega),
          Function.update_of_ne (show i ≠ 10 by omega)]
        exact hR i hi
      · simp
      · dsimp only
        have hs : (t + 1) * LB = t * LB + LB := Nat.succ_mul t LB
        rw [hfr₁ a (by omega)]
        exact hfr a (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
        · have hb' := blk_end LB ht'
          have hd' := blk_disj LB (show t' ≠ t by omega)
          have hag : ∀ i < LB, mem₁ (accBase + t' * LB + i) = st.mem (accBase + t' * LB + i) :=
            fun i hi => hfr₁ _ (by omega)
          obtain ⟨hv', hu'⟩ := hdone t' ht'
          exact ⟨fun i hi => by rw [hag i hi]; exact hv' i hi, by rw [unsignedVal_congr hag, hu']⟩
        · refine ⟨hv₁, ?_⟩
          rw [hu₁, hU0, hsd.2, hsu.2, hsv.2]
          rfl
      · simp only [Function.update_of_ne (show (8 : ℕ) ≠ 14 by omega),
          Function.update_of_ne (show (8 : ℕ) ≠ 13 by omega),
          Function.update_of_ne (show (8 : ℕ) ≠ 12 by omega),
          Function.update_of_ne (show (8 : ℕ) ≠ 11 by omega),
          Function.update_of_ne (show (8 : ℕ) ≠ 10 by omega)]
        exact h8
      · simp only [accEdgeContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
          Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        omega
  refine runs_start_le ?_
  unfold accLevelProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase,
    LB, rfl, rfl, hfr, hdone⟩ ?_
  simp only [accLevelContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg]
  have h1 : (m0 - 0) * (150 * LB + 150 + 1 + 8) ≤ m0 * (150 * LB + 159) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : m0 * (150 * LB + 159) ≤ m0 * (150 * LB + 160) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end MinCostFlow.LSF.Program
