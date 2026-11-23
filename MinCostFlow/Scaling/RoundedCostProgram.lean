module

public import MinCostFlow.Scaling.CostNumeratorProgram
public import MinCostFlow.Scaling.RoundClipProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# One edge cost of the rounded residual instance

The cost-scaling loop forms an integer reduced-cost numerator, rounds it
with denominator `C+1`, and clips it to `[-(2*m)^8,(2*m)^9]`. This procedure
performs exactly that model operation. The first ten allocated cells are
scratch and the final two hold the rounded instance's edge cost. The cost
is at most 1200 steps and the module uses no random instructions.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments: cost pair, endpoint potential pairs, `(2*m)^8`, `(2*m)^9`,
state power, `C+1`, and heap. -/
def roundedCostBody (numerator roundClip : ℕ) : Stmt :=
  .call 11 numerator [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5,
    .reg 6, .reg 8, .reg 9, .reg 10] ;;
  .call 12 roundClip [.load (.bin .add (.reg 10) (.const 6)),
    .load (.bin .add (.reg 10) (.const 7)), .reg 9, .reg 6, .reg 7, .reg 11] ;;
  .ret (.reg 12)

/-- The edge-cost entry, exact numerator, and rounding/clipping modules. -/
def roundedCostModule (b : ℕ) : List Stmt :=
  roundedCostBody (b + 1) (b + 14) ::
    (costNumeratorModule (b + 1) ++ roundClipModule (b + 14))

/-- Local budgets cover the numerator arithmetic and rounding adjustment.
The represented state contains only its flow, potentials, and power. -/
def roundedCostContract (w : ℕ) {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m + I.m)) : Contract :=
  let c := (I.residual s.flow).cost e
  let x := s.potential ((I.residual s.flow).tail e)
  let y := s.potential ((I.residual s.flow).head e)
  let B := I.m + I.m
  let factor := B^8*s.power
  let d := C+1
  let H := heapContract w
    (fun args _ => ∃ heap, args =
      [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
        if y < 0 then 1 else 0, y.natAbs, B^8, B^9, s.power, d, heap] ∧
      factor < 2 ^ w ∧ c.natAbs*factor < 2 ^ w ∧ x.natAbs+y.natAbs < 2 ^ w ∧
      (x-y).natAbs*d < 2 ^ w ∧ (c*(factor : ℤ)).natAbs+((x-y)*(d : ℤ)).natAbs < 2 ^ w ∧
      (s.costNumerator C e).natAbs+d/2 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args + 10)
      (encodeInt ((s.roundedInstance C).cost e)))
    (fun _ _ => 1200) (fun _ _ => 12)
  { H with post := fun args mem out mem' => H.post args mem out mem' ∧ out = heapArg args + 12 }

/-- Computing a rounded residual cost is deterministic. -/
theorem roundedCostModule_noRand (b : ℕ) : ∀ body ∈ roundedCostModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [roundedCostBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact costNumeratorModule_noRand _ body hb
    · exact roundClipModule_noRand _ body hb

/-- The machine computes exactly the edge cost used by the cost-scaling
model, with twelve allocated cells and cost at most 1200. -/
theorem roundedCost_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (roundedCostModule b)) {I : Circulation} (s : CostState I)
    (C : ℕ) (e : Fin (I.m + I.m)) :
    MeetsContract w p b (roundedCostContract w s C e) := by
  have htail := hasAt_tail hp
  have hnum := hasAt_append_left htail
  have hround : p.HasAt (b + 14) (roundClipModule (b + 14)) := by
    have h := hasAt_append_right htail
    simpa only [costNumeratorModule, reducedNumeratorModule, signedScaleModule,
      scaledDifferenceModule, signedSubtractModule, signedAddModule, List.length_cons,
      List.length_nil, List.length_append, Nat.reduceAdd, Nat.add_assoc] using h
  have hkN := costNumerator_meetsContract (w := w) hnum s C e
  have hkR := roundClip_meetsContract (w := w) hround (s.costNumerator C e) (C+1)
    ((I.m+I.m)^8) ((I.m+I.m)^9)
  let c := (I.residual s.flow).cost e
  let x := s.potential ((I.residual s.flow).tail e)
  let y := s.potential ((I.residual s.flow).head e)
  let B := I.m+I.m
  let d := C+1
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hfactor, hcost, hxy, hpot, hsum, hadjust⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 12 < 2 ^ w at hspace
  change (∀ a ∈ [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
    if y < 0 then 1 else 0, y.natAbs, B^8, B^9, s.power, d, heap], a < 2 ^ w) at hwords
  have hc : c.natAbs < 2 ^ w := hwords _ (by simp)
  have hx : x.natAbs < 2 ^ w := by change x.natAbs+y.natAbs < 2 ^ w at hxy; omega
  have hy : y.natAbs < 2 ^ w := by change x.natAbs+y.natAbs < 2 ^ w at hxy; omega
  have hB8 : B^8 < 2 ^ w := hwords _ (by simp)
  have hB9 : B^9 < 2 ^ w := hwords _ (by simp)
  have hpower : s.power < 2 ^ w := hwords _ (by simp)
  have hd : d < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := by omega
  have hh6 : heap+6 < 2 ^ w := by omega
  have hh7 : heap+7 < 2 ^ w := by omega
  have hh8 : heap+8 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hsix : 6 < 2 ^ w := by omega
  have hseven : 7 < 2 ^ w := by omega
  have hsc : (if c < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hmag : (s.costNumerator C e).natAbs < 2 ^ w := by
    change (s.costNumerator C e).natAbs+d/2 < 2 ^ w at hadjust
    omega
  have hsign : (if s.costNumerator C e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  apply runs_start_le
  unfold roundedCostBody
  refine runs_seq_call_le hkN
    (vs := [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
      if y < 0 then 1 else 0, y.natAbs, B^8, s.power, d, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hfactor, hcost, hxy, hpot, hsum⟩, hzero, hh8⟩
  · intro next memN posN hpostN
    obtain ⟨⟨_, _, hframeN, hzeroN, hpairN⟩, hnext⟩ := hpostN
    change next = heap+8 at hnext
    change (∀ a < heap, memN a = mem a) at hframeN
    change ZeroFrom memN next at hzeroN
    change ListAt memN (heap+6) (encodeInt (s.costNumerator C e)) at hpairN
    have hsN : memN (heap+6) = if s.costNumerator C e < 0 then 1 else 0 := by
      simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using hpairN 0 (by change 0 < 2; decide)
    have hmN : memN (heap+7) = (s.costNumerator C e).natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero,
        show heap+6+1 = heap+7 by omega] using hpairN 1 (by change 1 < 2; decide)
    have hnextword : next < 2 ^ w := by omega
    refine runs_seq_call_le hkR
      (vs := [if s.costNumerator C e < 0 then 1 else 0, (s.costNumerator C e).natAbs,
        C+1, B^8, B^9, next]) (by eval_expr) ?_ ?_ ?_
    · change ∀ a ∈ [if s.costNumerator C e < 0 then 1 else 0, (s.costNumerator C e).natAbs,
        d, B^8, B^9, next], a < 2 ^ w
      wram_words
    · refine ⟨⟨next, rfl, Nat.succ_pos C, hadjust⟩, hzeroN, ?_⟩
      change next+4 < 2 ^ w
      omega
    · intro out memR posR hpostR
      obtain ⟨⟨_, _, hframeR, hzeroR, hpairR⟩, hout⟩ := hpostR
      change out = next+4 at hout
      change (∀ a < next, memR a = memN a) at hframeR
      change ZeroFrom memR out at hzeroR
      change ListAt memR (next+2) (encodeInt ((s.roundedInstance C).cost e)) at hpairR
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap+12 ∧ (∀ a < heap, memR a = mem a) ∧
          ZeroFrom memR out ∧ ListAt memR (heap+10) (encodeInt ((s.roundedInstance C).cost e))) ∧
          out = heap+12
        refine ⟨⟨by omega, by omega, ?_, hzeroR, ?_⟩, by omega⟩
        · intro a ha
          exact (hframeR a (by omega)).trans (hframeN a ha)
        · simpa only [hnext, Nat.add_assoc] using hpairR
      · simp only [roundedCostContract, heapContract, costNumeratorContract, roundClipContract,
          argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg,
          Expr.size_const]; omega

/-- All local budgets can hold together for every represented cost state. -/
theorem exists_roundedCost_pre {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m+I.m)) :
    ∃ w args, (∀ a ∈ args, a < 2 ^ w) ∧
      (roundedCostContract w s C e).pre args (fun _ => 0) := by
  let c := (I.residual s.flow).cost e
  let x := s.potential ((I.residual s.flow).tail e)
  let y := s.potential ((I.residual s.flow).head e)
  let B := I.m+I.m
  let factor := B^8*s.power
  let d := C+1
  let z := s.costNumerator C e
  let w := c.natAbs+x.natAbs+y.natAbs+B^8+B^9+s.power+factor+c.natAbs*factor+
    (x-y).natAbs*d+d+z.natAbs+13
  have hw : c.natAbs+x.natAbs+y.natAbs+B^8+B^9+s.power+factor+c.natAbs*factor+
      (x-y).natAbs*d+d+z.natAbs+13 < 2 ^ w := Nat.lt_two_pow_self
  have hhalf := Nat.div_le_self d 2
  refine ⟨w, [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
    if y < 0 then 1 else 0, y.natAbs, B^8, B^9, s.power, d, 0], ?_,
    ⟨0, rfl, by change factor < 2 ^ w; omega, by change c.natAbs*factor < 2 ^ w; omega,
      by change x.natAbs+y.natAbs < 2 ^ w; omega,
      by change (x-y).natAbs*d < 2 ^ w; omega, ?_, by change z.natAbs+d/2 < 2 ^ w; omega⟩,
    (fun _ _ => rfl), ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · split <;> omega
    · omega
    · split <;> omega
    · omega
    · split <;> omega
    all_goals omega
  · change (c*(factor : ℤ)).natAbs+((x-y)*(d : ℤ)).natAbs < 2 ^ w
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    omega
  · change 0+12 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
