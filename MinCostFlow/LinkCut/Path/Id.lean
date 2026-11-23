module

public import MinCostFlow.LinkCut.Path.Rev
public import MinCostFlow.Num.IsZero
public import WordRAM.CopyWords

/-!
# The identity-tag steps of the path payload

`pathIsIdBody` tests whether the tag of a record is the zero tag, with two zero tests.
`pathSetIdBody` writes the zero tag by copying `2 K` zero words from the heap pointer, which the
payload contracts promise to be zero.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.Gen.NodeLayout

/-- `isId [a, heap]` for the path payload. -/
def pathIsIdBody (isZeroProc : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .call 2 isZeroProc [kAddr 13 7, .reg 15] ;;
  .cond (.reg 2)
    (.call 3 isZeroProc [kAddr 13 8, .reg 15] ;;
     .ret (.reg 3))
    (.ret (.const 0))

/-- `setId [a, heap]` for the path payload. -/
def pathSetIdBody (copyProc : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .call 2 copyProc [.reg 1, kAddr 13 7, .bin .mul (.const 2) (.reg 15)] ;;
  .ret (.const 0)

theorem pathIsIdBody_noRand (b : ℕ) : (pathIsIdBody b).NoRand := by
  simp [pathIsIdBody, Stmt.NoRand]

theorem pathSetIdBody_noRand (b : ℕ) : (pathSetIdBody b).NoRand := by
  simp [pathSetIdBody, Stmt.NoRand]

/-- `pathIsIdBody` meets the identity-test contract of the path payload. -/
theorem pathIsId_meetsContract {w h K f isZeroProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (pathIsIdBody isZeroProc))
    (hz0 : MeetsContract w p isZeroProc (isZeroContract w h)) :
    MeetsContract w p f
      (isIdContract pathPayload (pathLayout h K) w (pathCost K) (pathSpace K)) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, heap, rfl, hah, ⟨v, hv⟩, t, ht⟩, hz, hroom⟩
  have hK : mem (a + 9) = K := (hv : PathValAt mem (a + 6) h K v).2.2.2.1
  change ZeroFrom mem heap at hz
  change heap + (8 * K + 8) < 2 ^ w at hroom
  rw [pathLayout_stride] at hah
  rw [pathLayout_offTag] at ht
  change PathTagAt mem (a + (13 + 7 * K)) h K t at ht
  -- The post, once the returned value is known.
  have post : ∀ v, (v = if t = PathTag.zero then 1 else 0) →
      (isIdContract pathPayload (pathLayout h K) w (pathCost K) (pathSpace K)).post
        [a, heap] mem v mem := by
    intro v hv
    refine ⟨hz, fun _ _ _ => rfl, fun t' ht' => ?_⟩
    change (pathLayout h K).TagAt mem (a + (pathLayout h K).offTag) t' at ht'
    rw [pathLayout_offTag] at ht'
    obtain rfl := pathTagAt_unique ht (ht' : PathTagAt mem (a + (13 + 7 * K)) h K t')
    simpa [pathPayload] using hv
  apply runs_start_le
  unfold pathIsIdBody
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hK) ?_
  refine runs_seq_call_le hz0 (vs := [a + (13 + 7 * K), K]) (by eval_expr) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    ⟨_, _, rfl, by omega, ht.1.1⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨hm₁, hv₁⟩
  subst mem₁
  simp only [startState, List.getD_cons_zero, List.getD_cons_succ, ht.1.2] at hv₁
  refine runs_cond_le (v := v₁) (by eval_expr) ?_ ?_
  · intro hne
    have hf0 : t.flow = 0 := by
      by_contra hc; simp [hc] at hv₁; exact hne hv₁
    have hdt : PathIntAt mem (a + (13 + 8 * K)) h K t.detector := by
      have := ht.2; rwa [show a + (13 + 7 * K) + K = a + (13 + 8 * K) by omega] at this
    refine runs_seq_call_le hz0 (vs := [a + (13 + 8 * K), K]) (by eval_expr) (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
      ⟨_, _, rfl, by omega, hdt.1⟩ ?_
    rintro v₂ mem₂ pos₂ ⟨hm₂, hv₂⟩
    subst mem₂
    simp only [startState, List.getD_cons_zero, List.getD_cons_succ] at hv₂
    rw [hdt.2] at hv₂
    refine runs_ret_le (by eval_expr) (post v₂ ?_) ?_
    · rw [hv₂]
      by_cases hd0 : t.detector = 0
      · have : t = PathTag.zero := PathTag.ext hf0 hd0
        simp [this, PathTag.zero]
      · have : t ≠ PathTag.zero := fun h' => hd0 (by rw [h']; rfl)
        simpa [this] using hd0
    · simp only [pathCost, isZeroContract, isIdContract, payloadContract, Expr.size_reg, Expr.size_const, Expr.size_bin,
        argsSize_cons, argsSize_nil, List.getD_cons_zero, List.getD_cons_succ, kAddr, kOff,
        Expr.size_load]
      omega
  · intro h0
    refine runs_ret_le (by eval_expr) (post 0 ?_) ?_
    · have hf0 : t.flow ≠ 0 := by
        intro hc; simp [hc] at hv₁; omega
      have : t ≠ PathTag.zero := fun h' => hf0 (by rw [h']; rfl)
      simp [this]
    · simp only [pathCost, isZeroContract, isIdContract, payloadContract, Expr.size_reg, Expr.size_const, Expr.size_bin,
        argsSize_cons, argsSize_nil, List.getD_cons_zero, List.getD_cons_succ, kAddr, kOff,
        Expr.size_load]
      omega

/-- `pathSetIdBody` meets the identity-write contract of the path payload. -/
theorem pathSetId_meetsContract {w h K f copyProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (pathSetIdBody copyProc))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p f
      (setIdContract pathPayload (pathLayout h K) w (pathCost K) (pathSpace K)) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, heap, rfl, hah, v₀, hv₀⟩, hz, hroom⟩
  have hK : mem (a + 9) = K := (hv₀ : PathValAt mem (a + 6) h K v₀).2.2.2.1
  change ZeroFrom mem heap at hz
  change heap + (8 * K + 8) < 2 ^ w at hroom
  rw [pathLayout_stride] at hah
  apply runs_start_le
  unfold pathSetIdBody
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hK) ?_
  refine runs_seq_call_le hcopy (vs := [heap, a + (13 + 7 * K), 2 * K]) (by eval_expr) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    ⟨_, _, _, rfl, by omega, by omega, by omega, Or.inl (by omega)⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨s₁, d₁, l₁, heq₁, -, hc₁, ho₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  have hcell : ∀ i < 2 * K, mem₁ (a + (13 + 7 * K) + i) = 0 := fun i hi => by
    rw [hc₁ i hi]; exact hz _ (by omega)
  have hkeep : ∀ y, ¬ (a + (13 + 7 * K) ≤ y ∧ y < a + (13 + 9 * K)) → mem₁ y = mem y :=
    fun y hy => ho₁ y (by omega)
  refine runs_ret_le (by eval_expr) ?_ ?_
  · refine ⟨fun y hy => by change heap ≤ y at hy; show mem₁ y = 0; rw [hkeep y (by omega)]; exact hz y hy, fun y hy hn => ?_, ?_, ?_, ?_⟩
    · change y < heap at hy
      change ¬ (a + 6 ≤ y ∧ y < a + (pathLayout h K).nodeStride) at hn
      rw [pathLayout_stride] at hn
      exact hkeep y (by omega)
    · intro v hv
      show PathValAt mem₁ (a + 6) h K v
      exact pathValAt_move (hv : PathValAt mem (a + 6) h K v) fun i hi =>
        hkeep _ (by omega)
    · intro s hs
      change (pathLayout h K).SumAt mem (a + (pathLayout h K).offSum) s at hs
      show (pathLayout h K).SumAt mem₁ (a + (pathLayout h K).offSum) s
      rw [pathLayout_offSum] at hs ⊢
      exact pathSummaryAt_move hs fun i hi => hkeep _ (by omega)
    · show (pathLayout h K).TagAt mem₁ (a + (pathLayout h K).offTag) PathTag.zero
      rw [pathLayout_offTag]
      refine ⟨⟨fun i hi => ?_, intVal_zero fun i hi => hcell i (by omega)⟩,
        ⟨fun i hi => ?_, intVal_zero fun i hi => ?_⟩⟩
      · rw [hcell i (by omega)]; exact base_pos h
      · rw [show a + (13 + 7 * K) + K + i = a + (13 + 7 * K) + (K + i) by omega,
          hcell _ (by omega)]
        exact base_pos h
      · rw [show a + (13 + 7 * K) + K + i = a + (13 + 7 * K) + (K + i) by omega]
        exact hcell _ (by omega)
  · simp only [pathCost, copyWordsContract, setIdContract, payloadContract, Expr.size_reg, Expr.size_const, Expr.size_bin,
      argsSize_cons, argsSize_nil, kAddr, kOff, Expr.size_load]
    omega

end MinCostFlow.LinkCut.Path
