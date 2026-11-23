module

public import MinCostFlow.LastLevelProgram.IntegerUpdate
public import MinCostFlow.Num.FixedMultiply
public import MinCostFlow.Num.IntegerDivide
public import MinCostFlow.Num.AddCarry
import WordRAM.Tactic

/-!
# A WordRAM weight update

The last-level builder uses one signed product, one floor division,
and one addition to perform the update of Lemma 5.5 (page 18).
Working blocks use a width that holds the product before division.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Read the weight, stretch, and scaled denominator blocks and write the
updated weight at the end of the working allocation.
Arguments are `[weight, stretch, denominator, L, heap]`. -/
def weightUpdateBody (mul divide add : ℕ) : Stmt :=
  .call 5 mul [.reg 0, .reg 1, .reg 3, .const 0, .reg 4] ;;
  .call 6 divide [.bin .sub (.reg 5) (.reg 3), .reg 2, .reg 3, .reg 5] ;;
  .call 7 add [.reg 0, .bin .sub (.reg 6) (.reg 3), .reg 3, .const 0, .reg 6] ;;
  .ret (.reg 7)

/-- Scratch blocks and the final updated weight. -/
def weightUpdateSpace (L : ℕ) : ℕ :=
  (11 * L + 1) + integerDivideSpace L + L

/-- The total cost of the three arithmetic calls and the call overhead. -/
def weightUpdateCost (L : ℕ) : ℕ :=
  (2 * L) * (38 * (2 * L) + 35) + L * (300 * L + 644) + 487 * L + 750

/-- The weight update body itself uses no random bits. -/
theorem weightUpdateBody_noRand (mul divide add : ℕ) :
    (weightUpdateBody mul divide add).NoRand := by
  simp [weightUpdateBody, Stmt.NoRand]

private theorem block_frame {mem mem' : ℕ → ℕ} {a h L heap : ℕ}
    (ha : a + L ≤ heap) (hf : ∀ x < heap, mem' x = mem x) :
    (Valid mem a h L → Valid mem' a h L) ∧ intVal mem' a h L = intVal mem a h L := by
  have hcopy (i : ℕ) (hi : i < L) := hf (a + i) (by omega)
  exact ⟨fun hv i hi => (hcopy i hi).trans_lt (hv i hi), intVal_congr hcopy⟩

/-- The linked arithmetic writes the rounded weight and preserves the
input. The scaled denominator is stored as an integer, and the exact
product and final sum fit the working width. -/
theorem weightUpdate_runs {w h mul divide add : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w)
    (hmul : p.HasAt mul (fixedMultiplyModule mul h))
    (hdiv : p.HasAt divide (integerDivideModule divide h))
    (hadd : p.HasAt add (addCarryModule add h))
    (a b d L heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (ha : a + L ≤ heap) (hb : b + L ≤ heap) (hd : d + L ≤ heap)
    (hva : Valid mem a h L) (hvb : Valid mem b h L) (hvd : Valid mem d h L)
    (hz : ZeroFrom mem heap) (hroom : heap + weightUpdateSpace L < 2 ^ w)
    (hpos : 0 < intVal mem d h L)
    (hproduct : Fits h L (intVal mem a h L * intVal mem b h L))
    (hincrement : Fits h L (intVal mem a h L * intVal mem b h L / intVal mem d h L))
    (hsum : Fits h L (intVal mem a h L +
      intVal mem a h L * intVal mem b h L / intVal mem d h L)) :
    ∃ o st cost, Runs w p ω (weightUpdateBody mul divide add)
      (startState [a,b,d,L,heap] mem pos) o st cost ∧
      (o.value = heap + weightUpdateSpace L ∧
        Valid st.mem (heap + (11 * L + 1) + integerDivideSpace L) h L ∧
        intVal st.mem (heap + (11 * L + 1) + integerDivideSpace L) h L =
          intVal mem a h L + intVal mem a h L * intVal mem b h L / intVal mem d h L ∧
        (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem o.value) ∧
      cost ≤ weightUpdateCost L := by
  have hw0 : 0 < 2 ^ w := Nat.two_pow_pos _
  have hroom' : heap + (11 * L + 1) + integerDivideSpace L + L < 2 ^ w := by
    simpa only [weightUpdateSpace, Nat.add_assoc] using hroom
  apply runs_start_le
  unfold weightUpdateBody
  refine runs_seq_call_le (fixedMultiply_meetsContract hh (by omega) hmul)
    (vs := [a,b,L,0,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a,b,L,0,heap,rfl,dvd_zero _,ha,hb,hva,hvb⟩,hz,by
      change heap + (11 * L + 1) < 2^w
      omega⟩
  · intro r₁ mem₁ pos₁ hpost
    obtain ⟨hr₁, _, _, hf₁, hz₁, hvp, hpval⟩ := hpost
    change r₁ = heap + (11 * L + 1) at hr₁
    change ZeroFrom mem₁ r₁ at hz₁
    change Valid mem₁ (heap + 10 * L + 1) h L at hvp
    change intVal mem₁ (heap + 10 * L + 1) h L =
      wrap h L ((intVal mem a h L * intVal mem b h L) / (2 : ℤ)^0) at hpval
    simp only [pow_zero, Int.ediv_one, wrap_of_fits hproduct] at hpval
    change ∀ x < heap, mem₁ x = mem x at hf₁
    have ha₁ := block_frame (h := h) ha hf₁
    have hd₁ := block_frame (h := h) hd hf₁
    have hpbase : r₁ - L = heap + 10 * L + 1 := by omega
    have hpos₁ : 0 < intVal mem₁ d h L := hd₁.2 ▸ hpos
    refine runs_seq_call_le (integerDivide_meetsContract hh hw hdiv)
      (vs := [r₁-L,d,L,r₁]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,by simpa only [hpbase] using hvp,
        hd₁.1 hvd,hpos₁.ne'⟩,hz₁,by
          change r₁ + integerDivideSpace L < 2^w
          omega⟩
    · intro r₂ mem₂ pos₂ hpost₂
      obtain ⟨hr₂, _, _, hf₂, hz₂, hvq, hqval⟩ := hpost₂
      change r₂ = r₁ + integerDivideSpace L at hr₂
      change ∀ x < r₁, mem₂ x = mem₁ x at hf₂
      change ZeroFrom mem₂ r₂ at hz₂
      have hqbase : r₂ - L = r₁ + 2 * L + unsignedDivideSpace L := by
        unfold integerDivideSpace at hr₂
        omega
      change Valid mem₂ (r₁ + 2 * L + unsignedDivideSpace L) h L at hvq
      change intVal mem₂ (r₁ + 2 * L + unsignedDivideSpace L) h L =
        wrap h L (floorDiv (intVal mem₁ (r₁-L) h L) (intVal mem₁ d h L)) at hqval
      rw [hpbase, hpval, hd₁.2, floorDiv, ite_eq_right (not_lt.mpr hpos.le),
        wrap_of_fits hincrement] at hqval
      have ha₂ := block_frame (h := h) (show a + L ≤ r₁ by omega) hf₂
      refine runs_seq_call_le (addCarry_meetsContract hh (by omega) hadd)
        (vs := [a,r₂-L,L,0,r₂]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by omega,
          ha₂.1 (ha₁.1 hva),by simpa only [hqbase] using hvq⟩,hz₂,by
            change r₂ + L < 2^w
            omega⟩
      · intro r₃ mem₃ pos₃ hpost₃
        obtain ⟨hr₃, _, _, hf₃, hz₃, hdigits⟩ := hpost₃
        change r₃ = r₂ + L at hr₃
        change ZeroFrom mem₃ r₃ at hz₃
        change ∀ x < r₂, mem₃ x = mem₂ x at hf₃
        change ListAt mem₃ r₂ (digits h L
          (unsignedVal mem₂ a h L + unsignedVal mem₂ (r₂-L) h L + 0)) at hdigits
        have hv := addCarry_value hdigits
        rw [ha₂.2, ha₁.2, hqbase, hqval, Nat.cast_zero, add_zero, wrap_of_fits hsum] at hv
        have hret : r₃ < 2^w := by omega
        refine runs_ret_le (v := r₃) (by eval_expr) ?_ ?_
        · have hr₂' : r₂ = heap + (11 * L + 1) + integerDivideSpace L := by omega
          refine ⟨by change r₃ = heap + weightUpdateSpace L; unfold weightUpdateSpace; omega,
            by simpa only [hr₂'] using hv.1, by simpa only [hr₂'] using hv.2,
            fun x hx => (hf₃ x (by omega)).trans ((hf₂ x (by omega)).trans (hf₁ x hx)),hz₃⟩
        · simp [weightUpdateCost, fixedMultiplyContract, integerDivideContract,
            addCarryContract, heapContract, argsSize, Expr.size]
          omega

/-- Heap contract for the linked weight update at its working width. -/
def weightUpdateContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a b d L heap, args = [a,b,d,L,heap] ∧
      a + L ≤ heap ∧ b + L ≤ heap ∧ d + L ≤ heap ∧
      Valid mem a h L ∧ Valid mem b h L ∧ Valid mem d h L ∧
      0 < intVal mem d h L ∧
      Fits h L (intVal mem a h L * intVal mem b h L) ∧
      Fits h L (intVal mem a h L * intVal mem b h L / intVal mem d h L) ∧
      Fits h L (intVal mem a h L +
        intVal mem a h L * intVal mem b h L / intVal mem d h L))
    (fun args mem out =>
      let L := args.getD 3 0
      let result := heapArg args + (11 * L + 1) + integerDivideSpace L
      let a := intVal mem (args.getD 0 0) h L
      let b := intVal mem (args.getD 1 0) h L
      let d := intVal mem (args.getD 2 0) h L
      Valid out result h L ∧ intVal out result h L = a + a * b / d)
    (fun args _ => weightUpdateCost (args.getD 3 0))
    (fun args _ => weightUpdateSpace (args.getD 3 0))
  { C with post := fun args mem ret out =>
      ret = heapArg args + weightUpdateSpace (args.getD 3 0) ∧ C.post args mem ret out }

/-- Install the update as a procedure that can be called from the
last-level edge loop. -/
theorem weightUpdate_meetsContract {w h entry mul divide add : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w)
    (he : p.procs[entry]? = some (weightUpdateBody mul divide add))
    (hmul : p.HasAt mul (fixedMultiplyModule mul h))
    (hdiv : p.HasAt divide (integerDivideModule divide h))
    (hadd : p.HasAt add (addCarryModule add h)) :
    MeetsContract w p entry (weightUpdateContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨⟨a,b,d,L,heap,rfl,ha,hb,hd,hva,hvb,hvd,hpos,hprod,hquot,hsum⟩,hz,hroom⟩ := hpre
  obtain ⟨o, st, c, hr, ⟨hret, hvalid, hval, hframe, hzero⟩, hcost⟩ :=
    weightUpdate_runs hh hw hmul hdiv hadd a b d L heap pos mem ω ha hb hd hva hvb hvd
      hz hroom hpos hprod hquot hsum
  refine ⟨o, st, c, hr, ⟨hret, ?_, hret.le, hframe, hzero, hvalid, hval⟩, hcost⟩
  change heap ≤ o.value
  rw [hret]
  exact Nat.le_add_right _ _

end MinCostFlow.LastLevelProgram
