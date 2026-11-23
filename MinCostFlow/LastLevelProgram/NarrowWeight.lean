module

public import MinCostFlow.LastLevelProgram.WidenWeight
public import MinCostFlow.Num.Copy
import MinCostFlow.Num.ShiftFacts
import WordRAM.Tactic

/-!
# Writing a rounded weight at storage width

The weight update of Lemma 5.5 (page 18) uses wider scratch blocks
for the intermediate product. Once the final weight is known to
fit the storage width, copy its low limbs back to that width.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open Num WordRAM

/-- Update the weight and append a storage-width result.
Arguments are `[weight, stretch, scaled denominator, L, heap]`. -/
def narrowWeightBody (update copy : ℕ) : Stmt :=
  .call 5 update [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4] ;;
  .call 6 copy [.bin .sub (.reg 5) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)),
    .reg 3,.reg 5] ;;
  .ret (.reg 6)

/-- Space for the working allocation and the storage-width result. -/
def narrowWeightSpace (L : ℕ) : ℕ := widenWeightSpace L + L

/-- The narrowed update adds one linear-time block copy. -/
def narrowWeightCost (L : ℕ) : ℕ := widenWeightCost L + 17 * L + 40

/-- Execute the update and write its exact result in the original format,
assuming the final numerator fits. -/
theorem narrowWeight_runs {w h update copy : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (htwo : 2 < 2 ^ w)
    (hu : MeetsContract w p update (widenWeightContract w h))
    (hc : p.HasAt copy (copyModule copy))
    (a b d L heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (ha : a + L ≤ heap) (hb : b + L ≤ heap) (hd : d + L ≤ heap)
    (hva : Valid mem a h L) (hvb : Valid mem b h L) (hvd : Valid mem d h L)
    (hpos : 0 < intVal mem d h L) (hz : ZeroFrom mem heap)
    (hroom : heap + narrowWeightSpace L < 2 ^ w)
    (hfit : Fits h L (intVal mem a h L +
      intVal mem a h L * intVal mem b h L / intVal mem d h L)) :
    ∃ o st c, Runs w p ω (narrowWeightBody update copy)
      (startState [a,b,d,L,heap] mem pos) o st c ∧
      (o.value = heap + narrowWeightSpace L ∧ Valid st.mem (o.value - L) h L ∧
        intVal st.mem (o.value - L) h L =
          intVal mem a h L + intVal mem a h L * intVal mem b h L / intVal mem d h L ∧
        (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem o.value) ∧
      c ≤ narrowWeightCost L := by
  have hroom' : heap + widenWeightSpace L + L < 2 ^ w := by
    simpa only [narrowWeightSpace, Nat.add_assoc] using hroom
  have hW : 2 * L + 1 ≤ widenWeightSpace L := by
    change 2 * L + 1 ≤ 3 * (2 * L + 1) + weightUpdateSpace (2 * L + 1)
    omega
  apply runs_start_le
  unfold narrowWeightBody
  refine runs_seq_call_le hu (vs := [a,b,d,L,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a,b,d,L,heap,rfl,ha,hb,hd,hva,hvb,hvd,hpos⟩,hz,by
      change heap + widenWeightSpace L < 2^w
      omega⟩
  · intro r₁ m₁ pos₁ hpost
    obtain ⟨hr₁, ⟨_, _, hf₁, hz₁, _⟩, hv₁, hval₁⟩ := hpost
    change r₁ = heap + widenWeightSpace L at hr₁
    change ∀ x < heap, m₁ x = mem x at hf₁
    change ZeroFrom m₁ r₁ at hz₁
    change Valid m₁ (r₁ - (2 * L + 1)) h (2 * L + 1) at hv₁
    change intVal m₁ (r₁ - (2 * L + 1)) h (2 * L + 1) =
      intVal mem a h L + intVal mem a h L * intVal mem b h L / intVal mem d h L at hval₁
    have hvsmall : Valid m₁ (r₁ - (2 * L + 1)) h L :=
      fun i hi => hv₁ i (by omega)
    refine runs_seq_call_le (copy_meetsContract (h := h) hw hc)
      (vs := [r₁ - (2 * L + 1),L,r₁]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,L,r₁,rfl,by omega,hvsmall⟩,hz₁,by
        change r₁ + L < 2^w
        omega⟩
    · intro r₂ m₂ pos₂ hpost₂
      obtain ⟨hr₂, _, _, hf₂, hz₂, _, hv₂, hval₂⟩ := hpost₂
      change r₂ = r₁ + L at hr₂
      change ∀ x < r₁, m₂ x = m₁ x at hf₂
      change ZeroFrom m₂ r₂ at hz₂
      change Valid m₂ r₁ h L at hv₂
      change intVal m₂ r₁ h L = intVal m₁ (r₁ - (2 * L + 1)) h L at hval₂
      rw [intVal_prefix_wrap hv₁ (show L ≤ 2 * L + 1 by omega), hval₁, wrap_of_fits hfit] at hval₂
      refine runs_ret_le (v := r₂) (by eval_expr) ?_ ?_
      · have hbase : r₂ - L = r₁ := by omega
        refine ⟨by change r₂ = _; unfold narrowWeightSpace; omega,
          by simpa only [Outcome.value,hbase] using hv₂,
          by simpa only [Outcome.value,hbase] using hval₂, ?_, hz₂⟩
        intro x hx
        exact (hf₂ x (by omega)).trans (hf₁ x hx)
      · simp [narrowWeightCost, widenWeightContract, copyContract, heapContract,
          argsSize, Expr.size]
        omega

/-- Heap contract for one complete edge-weight update. -/
def narrowWeightContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a b d L heap, args = [a,b,d,L,heap] ∧
      a + L ≤ heap ∧ b + L ≤ heap ∧ d + L ≤ heap ∧
      Valid mem a h L ∧ Valid mem b h L ∧ Valid mem d h L ∧ 0 < intVal mem d h L ∧
      Fits h L (intVal mem a h L + intVal mem a h L * intVal mem b h L / intVal mem d h L))
    (fun _ _ _ => True)
    (fun args _ => narrowWeightCost (args.getD 3 0))
    (fun args _ => narrowWeightSpace (args.getD 3 0))
  { C with post := fun args mem ret out =>
      let L := args.getD 3 0
      let a := intVal mem (args.getD 0 0) h L
      let b := intVal mem (args.getD 1 0) h L
      let d := intVal mem (args.getD 2 0) h L
      ret = heapArg args + narrowWeightSpace L ∧ C.post args mem ret out ∧
        Valid out (ret - L) h L ∧ intVal out (ret - L) h L = a + a * b / d }

/-- Link the storage-width update as a procedure for the edge loop. -/
theorem narrowWeight_meetsContract {w h entry update copy : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (htwo : 2 < 2 ^ w)
    (he : p.procs[entry]? = some (narrowWeightBody update copy))
    (hu : MeetsContract w p update (widenWeightContract w h))
    (hc : p.HasAt copy (copyModule copy)) :
    MeetsContract w p entry (narrowWeightContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨⟨a,b,d,L,heap,rfl,ha,hb,hd,hva,hvb,hvd,hpos,hfit⟩,hz,hroom⟩ := hpre
  obtain ⟨o, st, cost, hrun, ⟨hret, hv, hval, hframe, hzero⟩, hcost⟩ :=
    narrowWeight_runs hw htwo hu hc a b d L heap pos mem ω ha hb hd hva hvb hvd hpos hz hroom hfit
  have hle : heap ≤ o.value := hret ▸ Nat.le_add_right _ _
  exact ⟨o, st, cost, hrun, ⟨hret, ⟨hle, hret.le, hframe, hzero, trivial⟩, hv, hval⟩, hcost⟩

end MinCostFlow.LastLevelProgram
