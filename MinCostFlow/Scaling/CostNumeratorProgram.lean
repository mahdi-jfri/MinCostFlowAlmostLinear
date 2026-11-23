module

public import MinCostFlow.Scaling.ReducedNumeratorProgram
public import MinCostFlow.Scaling.CostLoopModel
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import Mathlib.Tactic.Ring

/-!
# The cost-scaling model's exact numerator

A cost state stores integer potential numerators and a denominator power.
This procedure multiplies `(2*m)^8` by that power, then invokes the proved
reduced-numerator program on the edge cost and endpoint potentials. Its
output is exactly `CostState.costNumerator`, in the final two of eight
allocated words, at cost at most 800.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments are the cost pair, the two endpoint-potential pairs,
`(2*m)^8`, the state power, `C+1`, and the heap. -/
def costNumeratorBody (numerator : ℕ) : Stmt :=
  .call 10 numerator [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5,
    .bin .mul (.reg 6) (.reg 7), .reg 8, .reg 9] ;; .ret (.reg 10)

/-- The model numerator entry followed by the arithmetic implementation. -/
def costNumeratorModule (b : ℕ) : List Stmt :=
  costNumeratorBody (b + 1) :: reducedNumeratorModule (b + 1)

/-- The model's multiplication order agrees with the scalar program's. -/
theorem costNumerator_eq_reduced {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m + I.m)) :
    s.costNumerator C e =
      (I.residual s.flow).cost e * ((((I.m + I.m)^8) * s.power : ℕ) : ℤ) -
        (s.potential ((I.residual s.flow).tail e) - s.potential ((I.residual s.flow).head e)) *
          ((C+1 : ℕ) : ℤ) := by
  simp only [CostState.costNumerator, Nat.cast_mul]
  ring

/-- Each arithmetic operation has a magnitude budget. No mathematical
invariant or future output is assumed as part of the state representation. -/
def costNumeratorContract (w : ℕ) {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m + I.m)) : Contract :=
  let c := (I.residual s.flow).cost e
  let x := s.potential ((I.residual s.flow).tail e)
  let y := s.potential ((I.residual s.flow).head e)
  let b := (I.m + I.m)^8 * s.power
  let d := C+1
  let H := heapContract w
    (fun args _ => ∃ heap, args =
      [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
        if y < 0 then 1 else 0, y.natAbs, (I.m + I.m)^8, s.power, d, heap] ∧
      b < 2 ^ w ∧ c.natAbs*b < 2 ^ w ∧ x.natAbs+y.natAbs < 2 ^ w ∧
      (x-y).natAbs*d < 2 ^ w ∧ (c*(b : ℤ)).natAbs+((x-y)*(d : ℤ)).natAbs < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args + 6) (encodeInt (s.costNumerator C e)))
    (fun _ _ => 800) (fun _ _ => 8)
  { H with post := fun args mem out mem' => H.post args mem out mem' ∧ out = heapArg args + 8 }

/-- The model numerator program has no random instructions. -/
theorem costNumeratorModule_noRand (b : ℕ) :
    ∀ body ∈ costNumeratorModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costNumeratorBody, Stmt.NoRand, and_self]
  · exact reducedNumeratorModule_noRand _ body hb

/-- The procedure computes the model's exact residual cost numerator,
with eight allocated words and cost at most 800. -/
theorem costNumerator_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (costNumeratorModule b)) {I : Circulation} (s : CostState I)
    (C : ℕ) (e : Fin (I.m + I.m)) :
    MeetsContract w p b (costNumeratorContract w s C e) := by
  let c := (I.residual s.flow).cost e
  let x := s.potential ((I.residual s.flow).tail e)
  let y := s.potential ((I.residual s.flow).head e)
  let factor := (I.m + I.m)^8 * s.power
  let d := C+1
  have hk := reducedNumerator_meetsContract (w := w) (hasAt_tail hp) c x y factor d
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hfactor, hcost, hxy, hpot, hsum⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 8 < 2 ^ w at hspace
  change factor < 2 ^ w at hfactor
  change (∀ a ∈ [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
    if y < 0 then 1 else 0, y.natAbs, (I.m + I.m)^8, s.power, d, heap], a < 2 ^ w) at hwords
  have hc : c.natAbs < 2 ^ w := hwords _ (by simp)
  have hx : x.natAbs < 2 ^ w := by change x.natAbs + y.natAbs < 2 ^ w at hxy; omega
  have hy : y.natAbs < 2 ^ w := by change x.natAbs + y.natAbs < 2 ^ w at hxy; omega
  have hbase : (I.m + I.m)^8 < 2 ^ w := hwords _ (by simp)
  have hpower : s.power < 2 ^ w := hwords _ (by simp)
  have hd : d < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hsc : (if c < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  apply runs_start_le
  unfold costNumeratorBody
  refine runs_seq_call_le hk
    (vs := [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
      if y < 0 then 1 else 0, y.natAbs, factor, d, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hcost, hxy, hpot, hsum⟩, hzero, hspace⟩
  · intro out memN posN hpost
    have hptr := hpost.2
    change out = heap + 8 at hptr
    have hout : out < 2 ^ w := by omega
    refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
    · change (heap ≤ out ∧ out ≤ heap + 8 ∧ (∀ a < heap, memN a = mem a) ∧
        ZeroFrom memN out ∧ ListAt memN (heap + 6) (encodeInt (s.costNumerator C e))) ∧ out = heap + 8
      rw [costNumerator_eq_reduced]
      exact hpost
    · simp only [costNumeratorContract, heapContract, reducedNumeratorContract,
        argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_reg]; omega

/-- Arbitrary cost states have simultaneous witnesses for all local numeric and allocation premises
at one sufficiently large width. -/
theorem exists_costNumerator_pre {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m + I.m)) :
    ∃ w args, (∀ a ∈ args, a < 2 ^ w) ∧
      (costNumeratorContract w s C e).pre args (fun _ => 0) := by
  let c := (I.residual s.flow).cost e
  let x := s.potential ((I.residual s.flow).tail e)
  let y := s.potential ((I.residual s.flow).head e)
  let B := (I.m + I.m)^8
  let factor := B*s.power
  let d := C+1
  let w := c.natAbs+x.natAbs+y.natAbs+B+s.power+factor+c.natAbs*factor+(x-y).natAbs*d+d+9
  have hw : c.natAbs+x.natAbs+y.natAbs+B+s.power+factor+c.natAbs*factor+(x-y).natAbs*d+d+9 < 2 ^ w :=
    Nat.lt_two_pow_self
  refine ⟨w, [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
    if y < 0 then 1 else 0, y.natAbs, B, s.power, d, 0], ?_,
    ⟨0, rfl, by change factor < 2 ^ w; omega, by change c.natAbs*factor < 2 ^ w; omega,
      by change x.natAbs+y.natAbs < 2 ^ w; omega,
      by change (x-y).natAbs*d < 2 ^ w; omega, ?_⟩, (fun _ _ => rfl), ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · split <;> omega
    · omega
    · split <;> omega
    · omega
    · split <;> omega
    all_goals omega
  · change (c*(factor : ℤ)).natAbs+((x-y)*(d : ℤ)).natAbs < 2 ^ w
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    omega
  · change 0 + 8 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
