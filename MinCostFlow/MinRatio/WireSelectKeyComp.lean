module

public import MinCostFlow.MinRatio.WireSelectKeyMath
public import MinCostFlow.Num.Multiply
public import MinCostFlow.Num.Absolute
public import MinCostFlow.Num.UnsignedLess
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Word-RAM exact cross-multiplication comparator for candidate keys

Implements `keyCompareBody` (`args = [e₁, n₁Ptr, d₁Ptr, e₂, n₂Ptr, d₂Ptr, L, heap]`):
1. Computes the exact `2L`-limb signed products `n₁ * d₂` and `n₂ * d₁` via `Num.multiply`.
2. Takes their unsigned magnitudes `|n₁ * d₂| = |n₁| · |d₂|` and `|n₂ * d₁| = |n₂| · |d₁|` via
   `Num.absolute` (at `2L` limbs).
3. Compares the two `2L`-limb unsigned magnitudes using `Num.unsignedLess`, breaking ties by
   `e₁ < e₂`.

Returns `1` iff `keyBetter e₁ (intVal n₁) (intVal d₁) e₂ (intVal n₂) (intVal d₂) = true`, and `0`
otherwise. Uses `16 * L` scratch words and costs at most `304 * L^2 + 720 * L + 340` steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num

/-- Procedure body comparing candidate keys `(e₁, n₁, d₁)` and `(e₂, n₂, d₂)`.
Arguments: `[e₁, n₁Ptr, d₁Ptr, e₂, n₂Ptr, d₂Ptr, L, heap]` (`reg 0 .. reg 7`).
Calls `mul` (`Num.multiply`), `abs` (`Num.absolute`), and `ult` (`Num.unsignedLess`). -/
def keyCompareBody (mul abs ult : ℕ) : Stmt :=
  .assign 8 (.bin .mul (.const 2) (.reg 6)) ;;
  .assign 9 (.bin .add (.reg 7) (.bin .mul (.const 4) (.reg 6))) ;;
  .call 10 mul [.reg 1, .reg 5, .reg 6, .reg 7] ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.const 4) (.reg 6))) ;;
  .call 12 mul [.reg 4, .reg 2, .reg 6, .reg 10] ;;
  .call 13 abs [.reg 9, .reg 8, .reg 12] ;;
  .call 14 abs [.reg 11, .reg 8, .reg 13] ;;
  .call 15 ult [.reg 13, .reg 12, .reg 8] ;;
  .cond (.reg 15)
    (.ret (.const 1))
    (.call 16 ult [.reg 12, .reg 13, .reg 8] ;;
     .cond (.reg 16)
       (.ret (.const 0))
       (.ret (.bin .lt (.reg 0) (.reg 3))))

/-- Self-contained relocatable module for `keyCompareBody` at base `b` with `h`-bit limbs:
- `b + 0`: `keyCompareBody`
- `b + 1 .. b + 5`: `Num.multiplyModule (b + 1) h` (length `5`)
- `b + 6 .. b + 10`: `Num.absoluteModule (b + 6) h` (length `5`)
- `b + 11`: `Num.unsignedLessModule (b + 11)` (length `1`).
Total length: `12`. -/
def keyCompareModule (b h : ℕ) : List Stmt :=
  [keyCompareBody (b + 1) (b + 6) (b + 11)] ++
    Num.multiplyModule (b + 1) h ++
    Num.absoluteModule (b + 6) h ++
    Num.unsignedLessModule (b + 11)

theorem keyCompareModule_length (b h : ℕ) : (keyCompareModule b h).length = 12 := by
  simp [keyCompareModule, Num.multiplyModule, Num.absoluteModule, Num.negateModule,
    Num.copyModule, Num.unsignedLessModule]

theorem keyCompareBody_noRand (mul abs ult : ℕ) : (keyCompareBody mul abs ult).NoRand := by
  simp [keyCompareBody, Stmt.NoRand]

theorem keyCompareModule_noRand (b h : ℕ) : ∀ s ∈ keyCompareModule b h, s.NoRand := by
  intro s hs
  simp only [keyCompareModule, List.mem_append, List.mem_singleton] at hs
  rcases hs with ((rfl | hm) | ha) | hu
  · exact keyCompareBody_noRand _ _ _
  · exact Num.multiplyModule_noRand _ _ _ hm
  · exact Num.absoluteModule_noRand _ _ _ ha
  · simp only [Num.unsignedLessModule, List.mem_singleton] at hu
    subst hu; exact Num.unsignedLessBody_noRand _

/-- Exact scratch space (in words) used by `keyCompareBody` at `L` limbs. -/
def keyCompareSpace (L : ℕ) : ℕ := 16 * L

/-- Exact step-cost bound for `keyCompareBody` at `L` limbs. -/
def keyCompareCost (L : ℕ) : ℕ := 304 * L ^ 2 + 720 * L + 400

/-- Contract for `keyCompareBody`: compares `(e₁, intVal n₁, intVal d₁)` against
`(e₂, intVal n₂, intVal d₂)`, preserving all memory below `heap` and leaving `ZeroFrom`
above `heap + 16 * L`. -/
def keyCompareContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ e₁ n₁ d₁ e₂ n₂ d₂ L heap,
      args = [e₁, n₁, d₁, e₂, n₂, d₂, L, heap] ∧
      n₁ + L ≤ heap ∧ d₁ + L ≤ heap ∧ n₂ + L ≤ heap ∧ d₂ + L ≤ heap ∧
      Num.Valid mem n₁ h L ∧ Num.Valid mem d₁ h L ∧
      Num.Valid mem n₂ h L ∧ Num.Valid mem d₂ h L ∧
      ZeroFrom mem heap ∧ heap + keyCompareSpace L < 2 ^ w
  post args mem v mem' :=
    let e₁ := args.getD 0 0
    let n₁ := args.getD 1 0
    let d₁ := args.getD 2 0
    let e₂ := args.getD 3 0
    let n₂ := args.getD 4 0
    let d₂ := args.getD 5 0
    let L := args.getD 6 0
    let heap := args.getD 7 0
    v = (if keyBetter e₁ (intVal mem n₁ h L) (intVal mem d₁ h L)
            e₂ (intVal mem n₂ h L) (intVal mem d₂ h L) then 1 else 0) ∧
    (∀ x < heap, mem' x = mem x) ∧
    ZeroFrom mem' (heap + keyCompareSpace L)
  cost args _ := keyCompareCost (args.getD 6 0)

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num

private lemma runs_seq_assign_flat' {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {mem regs : ℕ → ℕ} {pos v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hrest : ∃ o st' c, Runs w p ω s ⟨mem, Function.update regs r v, pos⟩ o st' c ∧
      Q o st' ∧ (k + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.assign r e) s) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_assign_le he hrest

private lemma runs_seq_call_flat' {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {C : Contract} {s : Stmt} {mem regs : ℕ → ℕ} {pos : ℕ} {vs : List ℕ} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f C)
    (hargs : evalArgs w ⟨mem, regs, pos⟩ args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs mem)
    (hrest : ∀ v mem' pos', C.post vs mem v mem' →
      ∃ o st' c, Runs w p ω s ⟨mem', Function.update regs r v, pos'⟩ o st' c ∧
        Q o st' ∧ (k + argsSize args + C.cost vs mem + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_call_le hf hargs hwords hpre hrest

private theorem keyCompare_arith_cost (L : ℕ) :
    ((2 * L) * (38 * (2 * L) + 35) + 120 * L + 99) +
    ((2 * L) * (38 * (2 * L) + 35) + 120 * L + 99) +
    (36 * (2 * L) + 40) + (36 * (2 * L) + 40) +
    (41 * (2 * L) + 6) + (41 * (2 * L) + 6) + 110 ≤
    keyCompareCost L := by
  unfold keyCompareCost
  nlinarith

/-- `keyCompareModule b h` meets `keyCompareContract w h` with `16 * L` scratch words and
quadratic `O(L^2)` cost. -/
theorem keyCompare_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (keyCompareModule b h)) :
    MeetsContract w p b (keyCompareContract w h) := by
  have hb := Num.base_lt_word hw
  have hb2 : 1 < Num.base h := Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)
  have hw1 : 1 < 2 ^ w := lt_trans hb2 hb
  have hw4 : 4 < 2 ^ w := lt_of_lt_of_le (by decide : 4 < 2 ^ 4)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hmulAt : p.HasAt (b + 1) (Num.multiplyModule (b + 1) h) := by
    intro i hi
    have hi' : i < 5 := by simpa [Num.multiplyModule] using hi
    have hproc := hp (1 + i) (by rw [keyCompareModule_length]; omega)
    rw [show b + 1 + i = b + (1 + i) by omega, hproc]
    have hidx : (keyCompareModule b h)[1 + i]'(by rw [keyCompareModule_length]; omega) =
        (Num.multiplyModule (b + 1) h)[i]'hi := by
      simp [keyCompareModule, Num.multiplyModule, Num.absoluteModule, Num.negateModule,
        Num.copyModule, Num.unsignedLessModule]
      rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | omega
    exact congrArg some hidx
  have habsAt : p.HasAt (b + 6) (Num.absoluteModule (b + 6) h) := by
    intro i hi
    have hi' : i < 5 := by
      simpa [Num.absoluteModule, Num.negateModule, Num.copyModule] using hi
    have hproc := hp (6 + i) (by rw [keyCompareModule_length]; omega)
    rw [show b + 6 + i = b + (6 + i) by omega, hproc]
    have hidx : (keyCompareModule b h)[6 + i]'(by rw [keyCompareModule_length]; omega) =
        (Num.absoluteModule (b + 6) h)[i]'hi := by
      simp [keyCompareModule, Num.multiplyModule, Num.absoluteModule, Num.negateModule,
        Num.copyModule, Num.unsignedLessModule]
      rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | omega
    exact congrArg some hidx
  have hultAt : p.HasAt (b + 11) (Num.unsignedLessModule (b + 11)) := by
    intro i hi
    have hi0 : i = 0 := by simpa [Num.unsignedLessModule] using hi
    subst hi0
    have hproc := hp 11 (by rw [keyCompareModule_length]; omega)
    simpa [keyCompareModule, Num.multiplyModule, Num.absoluteModule, Num.negateModule,
      Num.copyModule, Num.unsignedLessModule] using hproc
  have hmul := Num.multiply_meetsContract hh hw hmulAt
  have habs := Num.absolute_meetsContract hh hw1 hb habsAt
  have hult := Num.unsignedLess_meetsContract (h := h) hw1 hultAt
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨e₁, n₁, d₁, e₂, n₂, d₂, L, heap, rfl, hn₁, hd₁, hn₂, hd₂, hvn₁, hvd₁, hvn₂, hvd₂, hz, hroom⟩ := hpre
  change heap + 16 * L < 2 ^ w at hroom
  have he₁w : e₁ < 2 ^ w := hwords e₁ (by simp)
  have hn₁w : n₁ < 2 ^ w := hwords n₁ (by simp)
  have hd₁w : d₁ < 2 ^ w := hwords d₁ (by simp)
  have he₂w : e₂ < 2 ^ w := hwords e₂ (by simp)
  have hn₂w : n₂ < 2 ^ w := hwords n₂ (by simp)
  have hd₂w : d₂ < 2 ^ w := hwords d₂ (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have h2Lw : 2 * L < 2 ^ w := by omega
  have h4Lw : 4 * L < 2 ^ w := by omega
  have hp1w : heap + 4 * L < 2 ^ w := by omega
  have hcostB := keyCompare_arith_cost L
  let r0 := (startState [e₁, n₁, d₁, e₂, n₂, d₂, L, heap] mem pos).regs
  apply runs_start_le
  change ∃ o st' c, Runs w p ω (keyCompareBody (b + 1) (b + 6) (b + 11)) ⟨mem, r0, pos⟩ o st' c ∧ _
  unfold keyCompareBody
  refine runs_seq_assign_flat' (v := 2 * L) (by simp [Expr.eval, BinOp.eval, r0, startState, show 2 < 2 ^ w by omega, h2Lw]) ?_
  refine runs_seq_assign_flat' (v := heap + 4 * L) (by simp [Expr.eval, BinOp.eval, r0, startState, hw4, h4Lw, hp1w]) ?_
  -- Call 1: mul [n₁, d₂, L, heap] -> v10 = heap + 6 * L, product at heap + 4 * L
  refine runs_seq_call_flat' hmul (vs := [n₁, d₂, L, heap])
    (by simp [evalArgs, Expr.eval, r0, startState]) (by wram_words) ?_ ?_
  · exact ⟨⟨n₁, d₂, L, heap, rfl, hn₁, hd₂, hvn₁, hvd₂⟩, hz, by change heap + 6 * L < 2 ^ w; omega⟩
  · intro v10 mem1 pos1 hp1
    rcases hp1 with ⟨hv10, _, _, hf1, hz1, hvP1, hvalP1⟩
    change v10 = heap + 6 * L at hv10
    change (∀ x < heap, mem1 x = mem x) at hf1
    change ZeroFrom mem1 v10 at hz1
    change Num.Valid mem1 (heap + 4 * L) h (2 * L) at hvP1
    change intVal mem1 (heap + 4 * L) h (2 * L) = intVal mem n₁ h L * intVal mem d₂ h L at hvalP1
    have hv10w : v10 < 2 ^ w := by omega
    have hp2w : v10 + 4 * L < 2 ^ w := by omega
    have hvn₂1 : Num.Valid mem1 n₂ h L := fun i hi => by rw [hf1 _ (by omega)]; exact hvn₂ i hi
    have hvd₁1 : Num.Valid mem1 d₁ h L := fun i hi => by rw [hf1 _ (by omega)]; exact hvd₁ i hi
    have hvalN₂1 : intVal mem1 n₂ h L = intVal mem n₂ h L := intVal_congr (fun i hi => hf1 _ (by omega))
    have hvalD₁1 : intVal mem1 d₁ h L = intVal mem d₁ h L := intVal_congr (fun i hi => hf1 _ (by omega))
    refine runs_seq_assign_flat' (v := v10 + 4 * L) (by simp [Expr.eval, BinOp.eval, r0, startState, hw4, h4Lw, hp2w]) ?_
    -- Call 2: mul [n₂, d₁, L, v10] -> v12 = v10 + 6 * L, product at v10 + 4 * L
    refine runs_seq_call_flat' hmul (vs := [n₂, d₁, L, v10])
      (by simp [evalArgs, Expr.eval, r0, startState]) (by wram_words) ?_ ?_
    · exact ⟨⟨n₂, d₁, L, v10, rfl, by omega, by omega, hvn₂1, hvd₁1⟩, hz1,
        by change v10 + 6 * L < 2 ^ w; omega⟩
    · intro v12 mem2 pos2 hp2
      rcases hp2 with ⟨hv12, _, _, hf2, hz2, hvP2, hvalP2⟩
      change v12 = v10 + 6 * L at hv12
      change (∀ x < v10, mem2 x = mem1 x) at hf2
      change ZeroFrom mem2 v12 at hz2
      change Num.Valid mem2 (v10 + 4 * L) h (2 * L) at hvP2
      change intVal mem2 (v10 + 4 * L) h (2 * L) = intVal mem1 n₂ h L * intVal mem1 d₁ h L at hvalP2
      rw [hvalN₂1, hvalD₁1] at hvalP2
      have hv12w : v12 < 2 ^ w := by omega
      have hvP1_2 : Num.Valid mem2 (heap + 4 * L) h (2 * L) :=
        fun i hi => by rw [hf2 _ (by omega)]; exact hvP1 i hi
      have hvalP1_2 : intVal mem2 (heap + 4 * L) h (2 * L) = intVal mem n₁ h L * intVal mem d₂ h L :=
        (intVal_congr (fun i hi => hf2 _ (by omega))).trans hvalP1
      -- Call 3: abs [heap + 4 * L, 2 * L, v12] -> v13 = v12 + 2 * L, unsigned |n₁ * d₂| at v12
      refine runs_seq_call_flat' habs (vs := [heap + 4 * L, 2 * L, v12])
        (by simp [evalArgs, Expr.eval, r0, startState]) (by wram_words) ?_ ?_
      · exact ⟨⟨heap + 4 * L, 2 * L, v12, rfl, by omega, hvP1_2⟩, hz2,
          by change v12 + 2 * L < 2 ^ w; omega⟩
      · intro v13 mem3 pos3 hp3
        rcases hp3 with ⟨hv13, _, _, hf3, hz3, hvA1, hvalA1⟩
        change v13 = v12 + 2 * L at hv13
        change (∀ x < v12, mem3 x = mem2 x) at hf3
        change ZeroFrom mem3 v13 at hz3
        change Num.Valid mem3 v12 h (2 * L) at hvA1
        change unsignedVal mem3 v12 h (2 * L) = (intVal mem2 (heap + 4 * L) h (2 * L)).natAbs at hvalA1
        rw [hvalP1_2] at hvalA1
        have hv13w : v13 < 2 ^ w := by omega
        have hvP2_3 : Num.Valid mem3 (v10 + 4 * L) h (2 * L) :=
          fun i hi => by rw [hf3 _ (by omega)]; exact hvP2 i hi
        have hvalP2_3 : intVal mem3 (v10 + 4 * L) h (2 * L) = intVal mem n₂ h L * intVal mem d₁ h L :=
          (intVal_congr (fun i hi => hf3 _ (by omega))).trans hvalP2
        -- Call 4: abs [v10 + 4 * L, 2 * L, v13] -> v14 = v13 + 2 * L, unsigned |n₂ * d₁| at v13
        refine runs_seq_call_flat' habs (vs := [v10 + 4 * L, 2 * L, v13])
          (by simp [evalArgs, Expr.eval, r0, startState]) (by wram_words) ?_ ?_
        · exact ⟨⟨v10 + 4 * L, 2 * L, v13, rfl, by omega, hvP2_3⟩, hz3,
            by change v13 + 2 * L < 2 ^ w; omega⟩
        · intro v14 mem4 pos4 hp4
          rcases hp4 with ⟨hv14, _, _, hf4, hz4, hvA2, hvalA2⟩
          change v14 = v13 + 2 * L at hv14
          change (∀ x < v13, mem4 x = mem3 x) at hf4
          change ZeroFrom mem4 v14 at hz4
          change Num.Valid mem4 v13 h (2 * L) at hvA2
          change unsignedVal mem4 v13 h (2 * L) = (intVal mem3 (v10 + 4 * L) h (2 * L)).natAbs at hvalA2
          rw [hvalP2_3] at hvalA2
          have hvA1_4 : Num.Valid mem4 v12 h (2 * L) :=
            fun i hi => by rw [hf4 _ (by omega)]; exact hvA1 i hi
          have hvalA1_4 : unsignedVal mem4 v12 h (2 * L) = (intVal mem n₁ h L * intVal mem d₂ h L).natAbs :=
            (unsignedVal_congr (fun i hi => hf4 _ (by omega))).trans hvalA1
          have hframeAll : ∀ x < heap, mem4 x = mem x := fun x hx =>
            (hf4 x (by omega)).trans ((hf3 x (by omega)).trans ((hf2 x (by omega)).trans (hf1 x hx)))
          have hzAll : ZeroFrom mem4 (heap + keyCompareSpace L) := fun x hx =>
            hz4 x (by unfold keyCompareSpace at hx; omega)
          -- Call 5: ult [v13, v12, 2 * L] (1 iff |n₂ * d₁| < |n₁ * d₂|)
          refine runs_seq_call_flat' hult (vs := [v13, v12, 2 * L])
            (by simp [evalArgs, Expr.eval, r0, startState]) (by wram_words) ?_ ?_
          · exact ⟨v13, v12, 2 * L, rfl, by omega, by omega, hvA2, hvA1_4⟩
          · intro b1 mem5 pos5 hp5
            rcases hp5 with ⟨hmem5, hb1⟩
            subst mem5
            change b1 = (if unsignedVal mem4 v13 h (2 * L) < unsignedVal mem4 v12 h (2 * L) then 1 else 0) at hb1
            rw [hvalA2, hvalA1_4] at hb1
            have hb1w : b1 < 2 ^ w := by rw [hb1]; split <;> omega
            refine runs_cond_le (v := b1) (by simp [Expr.eval]) ?_ ?_
            · intro hnz1
              have hlt1 : (intVal mem n₂ h L * intVal mem d₁ h L).natAbs <
                  (intVal mem n₁ h L * intVal mem d₂ h L).natAbs := by
                by_contra h
                rw [ite_eq_right h] at hb1; exact hnz1 hb1
              have hkb : keyBetter e₁ (intVal mem n₁ h L) (intVal mem d₁ h L)
                  e₂ (intVal mem n₂ h L) (intVal mem d₂ h L) = true :=
                (keyBetter_iff_mul_natAbs ..).mpr (Or.inl hlt1)
              refine runs_ret_le (v := 1) (by simp [Expr.eval, hw1]) ?_ ?_
              · dsimp only [keyCompareContract]
                refine ⟨?_, hframeAll, hzAll⟩
                simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hkb, ↓reduceIte]
              · simp only [keyCompareContract, Num.multiplyContract, Num.absoluteContract,
                  Num.unsignedLessContract, heapContract, List.getD_cons_zero, List.getD_cons_succ,
                  Expr.size, argsSize]
                linarith [hcostB]
            · intro hz1b
              have hge1 : ¬ (intVal mem n₂ h L * intVal mem d₁ h L).natAbs <
                  (intVal mem n₁ h L * intVal mem d₂ h L).natAbs := by
                intro h; rw [ite_eq_left h] at hb1; omega
              -- Call 6: ult [v12, v13, 2 * L] (1 iff |n₁ * d₂| < |n₂ * d₁|)
              refine runs_seq_call_flat' hult (vs := [v12, v13, 2 * L])
                (by simp [evalArgs, Expr.eval, r0, startState]) (by wram_words) ?_ ?_
              · exact ⟨v12, v13, 2 * L, rfl, by omega, by omega, hvA1_4, hvA2⟩
              · intro b2 mem6 pos6 hp6
                rcases hp6 with ⟨hmem6, hb2⟩
                subst mem6
                change b2 = (if unsignedVal mem4 v12 h (2 * L) < unsignedVal mem4 v13 h (2 * L) then 1 else 0) at hb2
                rw [hvalA1_4, hvalA2] at hb2
                have hb2w : b2 < 2 ^ w := by rw [hb2]; split <;> omega
                refine runs_cond_le (v := b2) (by simp [Expr.eval]) ?_ ?_
                · intro hnz2
                  have hlt2 : (intVal mem n₁ h L * intVal mem d₂ h L).natAbs <
                      (intVal mem n₂ h L * intVal mem d₁ h L).natAbs := by
                    by_contra h; rw [ite_eq_right h] at hb2; exact hnz2 hb2
                  have hkb : keyBetter e₁ (intVal mem n₁ h L) (intVal mem d₁ h L)
                      e₂ (intVal mem n₂ h L) (intVal mem d₂ h L) = false :=
                    Bool.eq_false_iff.mpr fun h => by
                      rw [keyBetter_iff_mul_natAbs] at h; omega
                  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
                  · dsimp only [keyCompareContract]
                    refine ⟨?_, hframeAll, hzAll⟩
                    simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hkb, Bool.false_eq_true, ↓reduceIte]
                  · simp only [keyCompareContract, Num.multiplyContract, Num.absoluteContract,
                      Num.unsignedLessContract, heapContract, List.getD_cons_zero, List.getD_cons_succ,
                      Expr.size, argsSize]
                    linarith [hcostB]
                · intro hz2b
                  have hge2 : ¬ (intVal mem n₁ h L * intVal mem d₂ h L).natAbs <
                      (intVal mem n₂ h L * intVal mem d₁ h L).natAbs := by
                    intro h; rw [ite_eq_left h] at hb2; omega
                  have heqM : (intVal mem n₂ h L * intVal mem d₁ h L).natAbs =
                      (intVal mem n₁ h L * intVal mem d₂ h L).natAbs := by omega
                  have hkbIff : keyBetter e₁ (intVal mem n₁ h L) (intVal mem d₁ h L)
                      e₂ (intVal mem n₂ h L) (intVal mem d₂ h L) = true ↔ e₁ < e₂ := by
                    rw [keyBetter_iff_mul_natAbs, heqM]; simp
                  refine runs_ret_le (v := if e₁ < e₂ then 1 else 0)
                    (by by_cases hlt : e₁ < e₂ <;>
                      simp [Expr.eval, BinOp.eval, r0, startState, hlt, hw1, show 0 < 2 ^ w by omega]) ?_ ?_
                  · dsimp only [keyCompareContract]
                    refine ⟨?_, hframeAll, hzAll⟩
                    simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
                    by_cases hlt : e₁ < e₂
                    · simp only [hlt, ↓reduceIte, hkbIff.mpr hlt]
                    · have hkbF : keyBetter e₁ (intVal mem n₁ h L) (intVal mem d₁ h L)
                          e₂ (intVal mem n₂ h L) (intVal mem d₂ h L) = false :=
                        Bool.eq_false_iff.mpr (fun h => hlt (hkbIff.mp h))
                      simp only [hlt, hkbF, Bool.false_eq_true, ↓reduceIte]
                  · simp only [keyCompareContract, Num.multiplyContract, Num.absoluteContract,
                      Num.unsignedLessContract, heapContract, List.getD_cons_zero, List.getD_cons_succ,
                      Expr.size, argsSize]
                    linarith [hcostB]

end MinCostFlow.MinRatio
