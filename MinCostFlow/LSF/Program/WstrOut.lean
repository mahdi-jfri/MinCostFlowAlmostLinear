module

public import MinCostFlow.LSF.Program.WstrEdge
public import MinCostFlow.LSF.Program.TopDownPass

/-!
# The stretches of all edges

`wstrOutProc` runs `wstrEdgeProc` (`WstrEdge.lean`) for each edge position `t < m0` of the edge
list of `G₀`. Edge `e = eList[t]` gets its numerator and denominator at `numPtr + e L_w` and
`denPtr + e L_w`, the layout of `WstrAt`, and its "high" flag at `highPtr + t`. The edges of the
list are distinct, so no edge overwrites another. The cost is `O(m0 LB²)`.

`WstrEdgeOut` is the post of one edge in a form that can be moved between memories.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- The output of one edge: the blocks written in `mem'`, from the sources in `mem`, and the
flag `ret`. -/
def WstrEdgeOut (h LB Lw : ℕ) (mem mem' : ℕ → ℕ) (numOut denOut acc le th k2 ret : ℕ) : Prop :=
  Valid mem' numOut h Lw ∧ Valid mem' denOut h Lw ∧
  (wstrNumVal (capacity h LB) (unsignedVal mem acc h LB) (unsignedVal mem k2 h LB)
      (unsignedVal mem le h LB) <
    unsignedVal mem th h LB * unsignedVal mem le h LB % capacity h LB →
    ret = 0 ∧ unsignedVal mem' numOut h Lw =
      wstrNumVal (capacity h LB) (unsignedVal mem acc h LB) (unsignedVal mem k2 h LB)
        (unsignedVal mem le h LB) % capacity h Lw ∧
    unsignedVal mem' denOut h Lw = unsignedVal mem le h LB % capacity h Lw) ∧
  (¬ wstrNumVal (capacity h LB) (unsignedVal mem acc h LB) (unsignedVal mem k2 h LB)
      (unsignedVal mem le h LB) <
    unsignedVal mem th h LB * unsignedVal mem le h LB % capacity h LB →
    ret = 1 ∧ unsignedVal mem' numOut h Lw = 1 % capacity h Lw ∧
    unsignedVal mem' denOut h Lw = 1 % capacity h Lw)

/-- The output stays when the two output blocks keep their limbs. -/
lemma WstrEdgeOut.of_dst {h LB Lw : ℕ} {mem mem' mem'' : ℕ → ℕ}
    {numOut denOut acc le th k2 ret : ℕ}
    (hO : WstrEdgeOut h LB Lw mem mem' numOut denOut acc le th k2 ret)
    (hn : ∀ i < Lw, mem'' (numOut + i) = mem' (numOut + i))
    (hd : ∀ i < Lw, mem'' (denOut + i) = mem' (denOut + i)) :
    WstrEdgeOut h LB Lw mem mem'' numOut denOut acc le th k2 ret := by
  obtain ⟨hvn, hvd, h1, h2⟩ := hO
  refine ⟨fun i hi => by rw [hn i hi]; exact hvn i hi, fun i hi => by rw [hd i hi]; exact hvd i hi,
    ?_, ?_⟩
  · intro hlt
    obtain ⟨r1, r2, r3⟩ := h1 hlt
    exact ⟨r1, by rw [unsignedVal_congr hn, r2], by rw [unsignedVal_congr hd, r3]⟩
  · intro hlt
    obtain ⟨r1, r2, r3⟩ := h2 hlt
    exact ⟨r1, by rw [unsignedVal_congr hn, r2], by rw [unsignedVal_congr hd, r3]⟩

/-- The output stays when the four source blocks keep their values. -/
lemma WstrEdgeOut.of_src {h LB Lw : ℕ} {mem mem₀ mem' : ℕ → ℕ}
    {numOut denOut acc le th k2 ret : ℕ}
    (hO : WstrEdgeOut h LB Lw mem mem' numOut denOut acc le th k2 ret)
    (ha : unsignedVal mem acc h LB = unsignedVal mem₀ acc h LB)
    (hl : unsignedVal mem le h LB = unsignedVal mem₀ le h LB)
    (ht : unsignedVal mem th h LB = unsignedVal mem₀ th h LB)
    (hk : unsignedVal mem k2 h LB = unsignedVal mem₀ k2 h LB) :
    WstrEdgeOut h LB Lw mem₀ mem' numOut denOut acc le th k2 ret := by
  unfold WstrEdgeOut at hO ⊢
  rw [ha, hl, ht, hk] at hO
  exact hO

/-! ## The loop -/

/-- One edge (register `13` is `t`). Register `14` is `e = eList[t]`, register `15` the flag. -/
def wstrOutBody (bEdge : ℕ) : Stmt :=
  .assign 14 (.load (.bin .add (.reg 1) (.reg 13))) ;;
  .call 15 bEdge [.bin .add (.reg 2) (.bin .mul (.reg 14) (.reg 11)),
    .bin .add (.reg 3) (.bin .mul (.reg 14) (.reg 11)),
    .bin .add (.reg 4) (.bin .mul (.reg 13) (.reg 10)),
    .bin .add (.reg 5) (.bin .mul (.reg 13) (.reg 10)),
    .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11] ;;
  .store (.bin .add (.reg 12) (.reg 13)) (.reg 15)

/-- Args: `[m0, eList, numPtr, denPtr, accBase, leBase, th, k2, tmp1, tmp2, LB, Lw, highPtr]`. -/
def wstrOutProc (bEdge : ℕ) : Stmt :=
  forRange 13 (.const 0) (.reg 0) (wstrOutBody bEdge) ;;
  .ret (.const 0)

lemma wstrOutProc_noRand (bEdge : ℕ) : (wstrOutProc bEdge).NoRand := by
  simp [wstrOutProc, wstrOutBody, forRange, forUp, Stmt.NoRand]

/-- The layout of `wstrOutProc`: the edge list, then the two output arrays, then the sources,
then the two scratch blocks and the flags. -/
def WstrOutLayout (w h : ℕ) (mem : ℕ → ℕ)
    (m0 eList numPtr denPtr accBase leBase th k2 tmp1 tmp2 LB Lw highPtr eCap : ℕ) : Prop :=
  16 ≤ 2 ^ w ∧ Lw ≤ LB ∧
  (∀ t < m0, mem (eList + t) < eCap) ∧
  (∀ t < m0, ∀ t' < m0, mem (eList + t) = mem (eList + t') → t = t') ∧
  (∀ t < m0, Valid mem (accBase + t * LB) h LB ∧ Valid mem (leBase + t * LB) h LB) ∧
  Valid mem th h LB ∧ Valid mem k2 h LB ∧
  eList + m0 ≤ numPtr ∧ numPtr + eCap * Lw ≤ denPtr ∧
  denPtr + eCap * Lw ≤ accBase ∧ denPtr + eCap * Lw ≤ leBase ∧ denPtr + eCap * Lw ≤ th ∧
  denPtr + eCap * Lw ≤ k2 ∧
  accBase + m0 * LB ≤ tmp1 ∧ leBase + m0 * LB ≤ tmp1 ∧ th + LB ≤ tmp1 ∧ k2 + LB ≤ tmp1 ∧
  tmp1 + LB ≤ tmp2 ∧ tmp2 + LB ≤ highPtr ∧ highPtr + m0 < 2 ^ w

/-- The contract of `wstrOutProc`. -/
def wstrOutContract (w h : ℕ) : Contract where
  pre args mem := ∃ (m0 eList numPtr denPtr accBase leBase th k2 tmp1 tmp2 LB Lw highPtr eCap : ℕ),
    args = [m0, eList, numPtr, denPtr, accBase, leBase, th, k2, tmp1, tmp2, LB, Lw, highPtr] ∧
    WstrOutLayout w h mem m0 eList numPtr denPtr accBase leBase th k2 tmp1 tmp2 LB Lw highPtr eCap
  post args mem ret mem' := ∃ (m0 eList numPtr denPtr accBase leBase th k2 tmp1 tmp2 LB Lw
      highPtr : ℕ),
    args = [m0, eList, numPtr, denPtr, accBase, leBase, th, k2, tmp1, tmp2, LB, Lw, highPtr] ∧
    ret = 0 ∧
    (∀ a, a < tmp1 → (∀ t < m0, (a < numPtr + mem (eList + t) * Lw ∨
        numPtr + mem (eList + t) * Lw + Lw ≤ a) ∧ (a < denPtr + mem (eList + t) * Lw ∨
        denPtr + mem (eList + t) * Lw + Lw ≤ a)) → mem' a = mem a) ∧
    (∀ a, highPtr + m0 ≤ a → mem' a = mem a) ∧
    ∀ t < m0, WstrEdgeOut h LB Lw mem mem' (numPtr + mem (eList + t) * Lw)
      (denPtr + mem (eList + t) * Lw) (accBase + t * LB) (leBase + t * LB) th k2
      (mem' (highPtr + t))
  cost args _ := args.getD 0 0 * (200 * args.getD 10 0 * args.getD 10 0 +
    600 * args.getD 10 0 + 600) + 20

theorem wstrOut_meetsContract {w h : ℕ} {p : Program} {b bEdge : ℕ}
    (hEdge : MeetsContract w p bEdge (wstrEdgeContract w h))
    (hp : p.procs[b]? = some (wstrOutProc bEdge)) :
    MeetsContract w p b (wstrOutContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m0, eList, numPtr, denPtr, accBase, leBase, th, k2, tmp1, tmp2, LB, Lw, highPtr, eCap,
    rfl, h16, hLw, heC, heInj, hblk, hvt, hvk, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12,
    l13⟩ := hpre
  set args := [m0, eList, numPtr, denPtr, accBase, leBase, th, k2, tmp1, tmp2, LB, Lw, highPtr]
    with hargs
  have hm0w : m0 < 2 ^ w := hwords m0 (by simp [hargs])
  have hw1 : 1 < 2 ^ w := by omega
  set E := fun t => mem (eList + t) with hE
  -- the parts of memory that no step writes
  let Keep : ℕ → Prop := fun a => (a < tmp1 → ∀ t < m0, (a < numPtr + E t * Lw ∨
      numPtr + E t * Lw + Lw ≤ a) ∧ (a < denPtr + E t * Lw ∨ denPtr + E t * Lw + Lw ≤ a))
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 13, st.regs i = args.getD i 0) ∧ st.regs 13 = j ∧
    (∀ a, a < tmp1 → (∀ t < m0, (a < numPtr + E t * Lw ∨ numPtr + E t * Lw + Lw ≤ a) ∧
      (a < denPtr + E t * Lw ∨ denPtr + E t * Lw + Lw ≤ a)) → st.mem a = mem a) ∧
    (∀ a, highPtr + j ≤ a → st.mem a = mem a) ∧
    (∀ a, denPtr + eCap * Lw ≤ a → a < tmp1 → st.mem a = mem a) ∧
    ∀ t < j, WstrEdgeOut h LB Lw mem st.mem (numPtr + E t * Lw) (denPtr + E t * Lw)
      (accBase + t * LB) (leBase + t * LB) th k2 (st.mem (highPtr + t))
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 13 (.const 0) (.reg 0) (wstrOutBody bEdge)) (normalPost (Inv m0))
      (fun _ => (m0 - 0) * ((200 * LB * LB + 600 * LB + 580) + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (200 * LB * LB + 600 * LB + 580) 0 m0 (by omega) hw1
      (fun _ => hm0w) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ _ => rfl, fun a _ => rfl,
        fun a _ _ => rfl, fun t ht => absurd ht (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 13 by omega)]
      interval_cases i <;> simp [startState, hargs]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = m0 := hI.1 0 (by omega)
      eval_expr
    · intro t _ htm st ω' hI
      obtain ⟨hR, h13, hk3, hk4, hk5, hdone⟩ := hI
      have r1 : st.regs 1 = eList := hR 1 (by omega)
      have r2 : st.regs 2 = numPtr := hR 2 (by omega)
      have r3 : st.regs 3 = denPtr := hR 3 (by omega)
      have r4 : st.regs 4 = accBase := hR 4 (by omega)
      have r5 : st.regs 5 = leBase := hR 5 (by omega)
      have r6 : st.regs 6 = th := hR 6 (by omega)
      have r7 : st.regs 7 = k2 := hR 7 (by omega)
      have r8 : st.regs 8 = tmp1 := hR 8 (by omega)
      have r9 : st.regs 9 = tmp2 := hR 9 (by omega)
      have r10 : st.regs 10 = LB := hR 10 (by omega)
      have r11 : st.regs 11 = Lw := hR 11 (by omega)
      have r12 : st.regs 12 = highPtr := hR 12 (by omega)
      have hbt := blk_end LB htm
      have heC' : ∀ t' < m0, E t' * Lw + Lw ≤ eCap * Lw := fun t' ht' => blk_end Lw (heC t' ht')
      have hbe := heC' t htm
      set e := E t with hedef
      have hme : st.mem (eList + t) = e := by
        refine hk3 _ (by omega) fun t' ht' => ?_
        have := heC' t' ht'
        constructor <;> left <;> omega
      have hLBw : LB < 2 ^ w := hwords LB (by simp [hargs])
      have hLww : Lw < 2 ^ w := hwords Lw (by simp [hargs])
      have hthw : th < 2 ^ w := hwords th (by simp [hargs])
      have hk2w : k2 < 2 ^ w := hwords k2 (by simp [hargs])
      -- the sources
      have hsrc : ∀ x, denPtr + eCap * Lw ≤ x → x + LB ≤ tmp1 → ∀ i < LB,
          st.mem (x + i) = mem (x + i) := fun x hx1 hx2 i hi => hk5 _ (by omega) (by omega)
      have hsA := hsrc (accBase + t * LB) (by omega) (by omega)
      have hsL := hsrc (leBase + t * LB) (by omega) (by omega)
      have hsT := hsrc th (by omega) (by omega)
      have hsK := hsrc k2 (by omega) (by omega)
      have hV : ∀ x, (∀ i < LB, st.mem (x + i) = mem (x + i)) → Valid mem x h LB →
          Valid st.mem x h LB := fun x hx hv i hi => by rw [hx i hi]; exact hv i hi
      refine runs_start_le ?_
      unfold wstrOutBody
      refine runs_seq_assign_le (v := e) (by rw [← hme]; eval_expr) ?_
      refine runs_seq_call_le (vs := [numPtr + e * Lw, denPtr + e * Lw, accBase + t * LB,
          leBase + t * LB, th, k2, tmp1, tmp2, LB, Lw]) hEdge
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons
            (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
              (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
                (evalArgs_nil _ _)))))))))))
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨_, _, _, _, _, _, _, _, _, _, rfl, h16, hLw, hV _ hsA (hblk t htm).1,
          hV _ hsL (hblk t htm).2, hV _ hsT hvt, hV _ hsK hvk, by omega, by omega, by omega,
          by omega, by omega, by omega,
          ⟨denPtr + eCap * Lw, by omega, by omega, by omega, by omega, by omega, by omega⟩,
          Or.inl (by omega)⟩ ?_
      rintro v₁ mem₁ pos₁ ⟨d₁, d₁', a₁, l₁, t₁, k₁, x₁, y₁, L₁, W₁, heq₁, hfr₁, hvn₁, hvd₁, hlt₁,
        hge₁⟩
      simp only [List.cons.injEq, and_true] at heq₁
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
      try dsimp only at hfr₁ hvn₁ hvd₁ hlt₁ hge₁
      have hO₁ : WstrEdgeOut h LB Lw mem mem₁ (numPtr + e * Lw) (denPtr + e * Lw)
          (accBase + t * LB) (leBase + t * LB) th k2 v₁ :=
        WstrEdgeOut.of_src ⟨hvn₁, hvd₁, hlt₁, hge₁⟩ (unsignedVal_congr hsA)
          (unsignedVal_congr hsL) (unsignedVal_congr hsT) (unsignedVal_congr hsK)
      refine runs_store_le (x := highPtr + t) (v := v₁) (by eval_expr) (by eval_expr)
        ⟨⟨fun i hi => ?_, ?_, fun a ha hout => ?_, fun a ha => ?_, fun a ha1 ha2 => ?_,
          fun t' ht' => ?_⟩, ?_⟩ ?_
      · dsimp only
        simp only [Function.update_of_ne (show i ≠ 13 by omega),
          Function.update_of_ne (show i ≠ 15 by omega),
          Function.update_of_ne (show i ≠ 14 by omega)]
        exact hR i hi
      · simp
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        obtain ⟨hn, hd⟩ := hout t htm
        rw [hfr₁ a hn hd (Or.inl ha)]
        exact hk3 a ha hout
      · dsimp only
        rw [Function.update_of_ne (by omega), hfr₁ a (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega))]
        exact hk4 a (by omega)
      · dsimp only
        rw [Function.update_of_ne (by omega), hfr₁ a (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inl ha2)]
        exact hk5 a ha1 ha2
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
        · have hne : E t' ≠ e := fun hc => by
            have := heInj t' (by omega) t htm hc
            omega
          have hd' := blk_disj Lw hne
          have hbe' := heC' t' (by omega)
          rw [Function.update_of_ne (show highPtr + t' ≠ highPtr + t by omega),
            hfr₁ _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
          refine (hdone t' ht').of_dst (fun i hi => ?_) (fun i hi => ?_)
          · rw [Function.update_of_ne (by omega)]
            exact hfr₁ _ (by omega) (by omega) (Or.inl (by omega))
          · rw [Function.update_of_ne (by omega)]
            exact hfr₁ _ (by omega) (by omega) (Or.inl (by omega))
        · rw [Function.update_self]
          refine hO₁.of_dst (fun i hi => ?_) (fun i hi => ?_)
          · rw [Function.update_of_ne (by omega)]
          · rw [Function.update_of_ne (by omega)]
      · simp only [Function.update_of_ne (show (13 : ℕ) ≠ 15 by omega),
          Function.update_of_ne (show (13 : ℕ) ≠ 14 by omega)]
        exact h13
      · simp only [wstrEdgeContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
          Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        omega
  refine runs_start_le ?_
  unfold wstrOutProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hk3, hk4, -, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨m0, eList, numPtr, denPtr, accBase, leBase, th, k2,
    tmp1, tmp2, LB, Lw, highPtr, rfl, rfl, hk3, hk4, hdone⟩ ?_
  simp only [wstrOutContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg]
  have h1 : (m0 - 0) * (200 * LB * LB + 600 * LB + 580 + 1 + 8) ≤
      m0 * (200 * LB * LB + 600 * LB + 600) := Nat.mul_le_mul (by omega) (by omega)
  omega

end MinCostFlow.LSF.Program
