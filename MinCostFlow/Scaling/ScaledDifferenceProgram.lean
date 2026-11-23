module

public import MinCostFlow.Scaling.SignedSubtractProgram
public import MinCostFlow.Scaling.SignedScaleProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# The scaled potential difference in reduced costs

The integer cost numerator subtracts `(C+1)` times the difference between
two stored vertex potentials. This procedure subtracts two signed inputs
and multiplies their difference by a natural factor. The subtraction pair
is scratch and the resulting pair follows it. The procedure allocates four
words, preserves the old heap frame, and costs at most 300 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[xSign,xMagnitude,ySign,yMagnitude,factor,heap]`. -/
def scaledDifferenceBody (subtract scale : ℕ) : Stmt :=
  .call 6 subtract [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5] ;;
  .call 7 scale [.load (.reg 5), .load (.bin .add (.reg 5) (.const 1)), .reg 4, .reg 6] ;;
  .ret (.reg 7)

/-- The entry, subtraction module, and multiplication module. -/
def scaledDifferenceModule (b : ℕ) : List Stmt :=
  scaledDifferenceBody (b + 1) (b + 4) ::
    (signedSubtractModule (b + 1) ++ signedScaleModule (b + 4))

/-- Both the subtraction budget and the magnitude product fit a word. -/
def scaledDifferenceContract (w : ℕ) (x y : ℤ) (d : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args =
      [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, d, heap] ∧
      x.natAbs + y.natAbs < 2 ^ w ∧ (x-y).natAbs * d < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args + 2) (encodeInt ((x-y) * (d : ℤ))))
    (fun _ _ => 300) (fun _ _ => 4)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 4 }

/-- Scaled differences and all their helpers use no random instructions. -/
theorem scaledDifferenceModule_noRand (b : ℕ) :
    ∀ body ∈ scaledDifferenceModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [scaledDifferenceBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact signedSubtractModule_noRand _ body hb
    · exact signedScaleModule_noRand _ body hb

/-- The composed machine procedure computes the exact scaled potential
difference, with four allocated words and constant cost. -/
theorem scaledDifference_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (scaledDifferenceModule b)) (x y : ℤ) (d : ℕ) :
    MeetsContract w p b (scaledDifferenceContract w x y d) := by
  have htail := hasAt_tail hp
  have hsub := hasAt_append_left htail
  have hscale : p.HasAt (b + 4) (signedScaleModule (b + 4)) := by
    have h := hasAt_append_right htail
    simpa only [signedSubtractModule, signedAddModule, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.add_assoc] using h
  have hkS := signedSubtract_meetsContract (w := w) hsub x y
  have hkM := signedScale_meetsContract (w := w) hscale (x-y) d
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hsum, hproduct⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 4 < 2 ^ w at hspace
  have hx : x.natAbs < 2 ^ w := by omega
  have hy : y.natAbs < 2 ^ w := by omega
  have hd : d < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := by omega
  have hh1 : heap + 1 < 2 ^ w := by omega
  have hh2 : heap + 2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hdiff : (x-y).natAbs < 2 ^ w := by
    have hbound : (x-y).natAbs ≤ x.natAbs + y.natAbs := Int.natAbs_sub_le x y
    omega
  have hsdiff : (if x-y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  apply runs_start_le
  unfold scaledDifferenceBody
  refine runs_seq_call_le hkS
    (vs := [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, heap])
    (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hsum⟩, hzero, hh2⟩
  · intro next memS posS hpostS
    obtain ⟨⟨_, _, hframeS, hzeroS, hpairS⟩, hnext⟩ := hpostS
    change next = heap + 2 at hnext
    change (∀ a < heap, memS a = mem a) at hframeS
    change ZeroFrom memS next at hzeroS
    change ListAt memS heap (encodeInt (x-y)) at hpairS
    have hsign : memS heap = if x-y < 0 then 1 else 0 := by
      simpa only [encodeInt, Nat.add_zero, List.getElem_cons_zero] using hpairS 0 (by change 0 < 2; decide)
    have hmag : memS (heap + 1) = (x-y).natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using hpairS 1 (by change 1 < 2; decide)
    have hnextword : next < 2 ^ w := by omega
    refine runs_seq_call_le hkM
      (vs := [if x-y < 0 then 1 else 0, (x-y).natAbs, d, next]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨next, rfl, hproduct⟩, hzeroS, ?_⟩
      change next + 2 < 2 ^ w
      omega
    · intro out memM posM hpostM
      obtain ⟨⟨_, _, hframeM, hzeroM, hpairM⟩, hout⟩ := hpostM
      change out = next + 2 at hout
      change (∀ a < next, memM a = memS a) at hframeM
      change ZeroFrom memM out at hzeroM
      change ListAt memM next (encodeInt ((x-y) * (d : ℤ))) at hpairM
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 4 ∧ (∀ a < heap, memM a = mem a) ∧
          ZeroFrom memM out ∧ ListAt memM (heap + 2) (encodeInt ((x-y) * (d : ℤ)))) ∧
          out = heap + 4
        refine ⟨⟨by omega, by omega, ?_, hzeroM, ?_⟩, by omega⟩
        · intro a ha
          exact (hframeM a (by omega)).trans (hframeS a ha)
        · simpa only [hnext] using hpairM
      · simp only [scaledDifferenceContract, heapContract, signedSubtractContract,
          signedScaleContract, argsSize_cons, argsSize_nil, Expr.size_bin,
          Expr.size_load, Expr.size_reg, Expr.size_const]; omega

/-- The scaled-difference hypotheses can hold together for any operands. -/
theorem exists_scaledDifference_pre (x y : ℤ) (d : ℕ) :
    ∃ w, (∀ a ∈ [if x < 0 then 1 else 0, x.natAbs,
        if y < 0 then 1 else 0, y.natAbs, d, 0], a < 2 ^ w) ∧
      (scaledDifferenceContract w x y d).pre
        [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, d, 0]
        (fun _ => 0) := by
  let w := x.natAbs + y.natAbs + (x-y).natAbs * d + d + 5
  have hw : x.natAbs + y.natAbs + (x-y).natAbs * d + d + 5 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, ?_, ⟨0, rfl, by omega, by omega⟩, (fun _ _ => rfl), ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · split <;> omega
    · omega
    · split <;> omega
    all_goals omega
  · change 0 + 4 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
