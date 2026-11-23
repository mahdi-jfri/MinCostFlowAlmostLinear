module

public import MinCostFlow.LastLevelProgram.StretchDivide
public import MinCostFlow.Num.AddCarry
public import MinCostFlow.Num.NegateCarry
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The rounded stretch from a path block

Definition 5.3 (page 17) adds one to the ratio of path length and
edge length. Form the numerator for that ratio, divide its negative
with floor rounding, then restore the sign to round upward.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open Num WordRAM

/-- Arguments are `[path, edge, L, precision, heap]`. -/
def stretchFromLengthBody (add neg divide : ℕ) : Stmt :=
  .call 5 add [.reg 0,.reg 1,.reg 2,.const 0,.reg 4] ;;
  .call 6 neg [.reg 4,.reg 2,.const 1,.reg 5] ;;
  .call 7 divide [.reg 5,.reg 1,.reg 2,.reg 3,.reg 6] ;;
  .call 8 neg [.bin .sub (.reg 7) (.reg 2),.reg 2,.const 1,.reg 7] ;;
  .ret (.reg 8)

/-- Space used by the rounded stretch arithmetic. -/
def stretchFromLengthSpace (L : ℕ) : ℕ := 2*L + fixedDivideSpace L + L

/-- Cost of the rounded stretch arithmetic. -/
def stretchFromLengthCost (L : ℕ) : ℕ :=
  (3*L)*(900*L+644) + 1010*L + 850

private theorem blockFrame {mem out : ℕ → ℕ} {a heap h L : ℕ}
    (ha : a + L ≤ heap) (hf : ∀ x < heap, out x = mem x) :
    (Valid mem a h L → Valid out a h L) ∧ intVal out a h L = intVal mem a h L := by
  have hc (i : ℕ) (hi : i < L) := hf (a+i) (by omega)
  exact ⟨fun hv i hi => (hc i hi).trans_lt (hv i hi),intVal_congr hc⟩

/-- The linked arithmetic writes the exact upward-rounded stretch in
the last allocated block when the intermediate signed values fit. -/
theorem stretchFromLength_runs {w h add neg divide : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3*h+2 ≤ w)
    (ha : p.HasAt add (addCarryModule add h)) (hn : p.HasAt neg (negateCarryModule neg h))
    (hd : p.HasAt divide (fixedDivideModule divide h))
    (path edge L P heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hp : path+L ≤ heap) (he : edge+L ≤ heap)
    (hvp : Valid mem path h L) (hve : Valid mem edge h L)
    (hPword : P < 2^w)
    (hz : ZeroFrom mem heap) (hroom : heap+stretchFromLengthSpace L < 2^w)
    (hpositive : 0 < intVal mem edge h L)
    (hsum : Fits h L (intVal mem path h L + intVal mem edge h L))
    (hneg : Fits h L (-(intVal mem path h L + intVal mem edge h L)))
    (hquot : Fits h L (floorDiv (-(intVal mem path h L + intVal mem edge h L)*(2:ℤ)^P)
      (intVal mem edge h L)))
    (hout : Fits h L (-(floorDiv (-(intVal mem path h L + intVal mem edge h L)*(2:ℤ)^P)
      (intVal mem edge h L)))) :
    ∃ o st c, Runs w p ω (stretchFromLengthBody add neg divide)
      (startState [path,edge,L,P,heap] mem pos) o st c ∧
      (o.value = heap+stretchFromLengthSpace L ∧ Valid st.mem (o.value-L) h L ∧
        fixVal st.mem (o.value-L) h L P =
          roundStretch P (1 + (intVal mem path h L : ℝ) / (intVal mem edge h L : ℝ)) ∧
        (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem o.value) ∧
      c ≤ stretchFromLengthCost L := by
  have hbound : heap + 2*L + fixedDivideSpace L + L < 2^w := by
    simpa only [stretchFromLengthSpace, Nat.add_assoc] using hroom
  have htwo : 1 < 2^w := (by decide : 1 < 2^2) |>.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hbase : base h < 2^w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hmc := negateCarry_meetsContract htwo hbase hn
  apply runs_start_le
  unfold stretchFromLengthBody
  refine runs_seq_call_le (addCarry_meetsContract hh (by omega) ha)
    (vs := [path,edge,L,0,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨path,edge,L,0,heap,rfl,hp,he,by decide,hvp,hve⟩,hz,by
      change heap+L < 2^w; omega⟩
  · intro r₁ m₁ pos₁ hpost
    obtain ⟨hr₁,_,_,hf₁,hz₁,hlist⟩ := hpost
    change r₁ = heap+L at hr₁
    change ∀ a < heap, m₁ a = mem a at hf₁
    change ListAt m₁ heap (digits h L (unsignedVal mem path h L + unsignedVal mem edge h L + 0)) at hlist
    obtain ⟨hv₁,hval₁⟩ := addCarry_value hlist
    rw [Nat.cast_zero,add_zero,wrap_of_fits hsum] at hval₁
    refine runs_seq_call_le hmc (vs := [heap,L,1,r₁]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨heap,L,1,r₁,rfl,hr₁.ge,by decide,hv₁⟩,hz₁,by change r₁+L < 2^w; omega⟩
    · intro r₂ m₂ pos₂ hpost₂
      obtain ⟨hr₂,_,_,hf₂,hz₂,hlist₂⟩ := hpost₂
      change r₂ = r₁+L at hr₂
      change ∀ a < r₁, m₂ a = m₁ a at hf₂
      change ListAt m₂ r₁ (digits h L (capacity h L - 1 - unsignedVal m₁ heap h L + 1)) at hlist₂
      obtain ⟨hv₂,hval₂⟩ := negateCarry_value_one hv₁ hlist₂
      rw [hval₁,wrap_of_fits hneg] at hval₂
      have hedge := blockFrame (h := h) he (fun a ha' => (hf₂ a (by omega)).trans (hf₁ a ha'))
      refine runs_seq_call_le (stretchFixedDivide_meetsContract hh hw hd)
        (vs := [r₁,edge,L,P,r₂]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨⟨r₁,edge,L,P,r₂,rfl,hr₂.ge,by omega,hv₂,hedge.1 hve,
          by rw [hedge.2]; exact hpositive.ne',?_⟩,hz₂,?_⟩
        · rwa [hval₂,hedge.2]
        · change r₂+fixedDivideSpace L < 2^w
          omega
      · intro r₃ m₃ pos₃ hpost₃
        obtain ⟨hr₃,_,_,hf₃,hz₃,hv₃,hval₃⟩ := hpost₃
        change r₃ = r₂+fixedDivideSpace L at hr₃
        change ∀ a < r₂, m₃ a = m₂ a at hf₃
        have hbase₃ : r₃-L = r₂+9*L+integerDivideSpace (3*L) := by
          unfold fixedDivideSpace at hr₃
          omega
        change Valid m₃ (r₂+9*L+integerDivideSpace (3*L)) h L at hv₃
        change intVal m₃ (r₂+9*L+integerDivideSpace (3*L)) h L =
          floorDiv (intVal m₂ r₁ h L*(2:ℤ)^P) (intVal m₂ edge h L) at hval₃
        rw [hval₂,hedge.2] at hval₃
        refine runs_seq_call_le hmc (vs := [r₃-L,L,1,r₃]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨⟨_,_,_,_,rfl,by omega,by decide,by rwa [hbase₃]⟩,hz₃,by
            change r₃+L < 2^w; omega⟩
        · intro r₄ m₄ pos₄ hpost₄
          obtain ⟨hr₄,_,_,hf₄,hz₄,hlist₄⟩ := hpost₄
          change r₄ = r₃+L at hr₄
          change ∀ a < r₃, m₄ a = m₃ a at hf₄
          change ListAt m₄ r₃ (digits h L (capacity h L - 1 - unsignedVal m₃ (r₃-L) h L + 1)) at hlist₄
          have hv₃' : Valid m₃ (r₃-L) h L := by rwa [hbase₃]
          obtain ⟨hvalid,hval⟩ := negateCarry_value_one hv₃' hlist₄
          rw [hbase₃,hval₃,wrap_of_fits hout] at hval
          refine runs_ret_le (v := r₄) (by eval_expr) ?_ ?_
          · have hres : r₄-L = r₃ := by omega
            refine ⟨by change r₄ = _; unfold stretchFromLengthSpace; omega,
              by simpa only [Outcome.value,hres] using hvalid,?_,?_,hz₄⟩
            · change fixVal m₄ (r₄-L) h L P = _
              rw [hres,fixVal,hval,roundStretch_of_integer_lengths P _ _ hpositive,
                floorDiv,ite_eq_right (not_lt.mpr hpositive.le),neg_mul,add_comm
                  (intVal mem path h L) (intVal mem edge h L)]
              push_cast
              rfl
            · intro a ha'
              exact (hf₄ a (by omega)).trans ((hf₃ a (by omega)).trans
                ((hf₂ a (by omega)).trans (hf₁ a ha')))
          · simp [stretchFromLengthCost, addCarryContract, negateCarryContract,
              stretchFixedDivideContract, heapContract, argsSize, Expr.size]
            omega

/-- All signed intermediates of the rounded quotient fit their blocks. -/
def stretchArithmeticFits (h L P : ℕ) (a d : ℤ) : Prop :=
  let q := floorDiv (-(a + d) * (2 : ℤ)^P) d
  Fits h L (a + d) ∧ Fits h L (-(a + d)) ∧ Fits h L q ∧ Fits h L (-q)

/-- Heap interface for computing a rounded stretch from the two lengths. -/
def stretchFromLengthContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L P heap, args = [a,d,L,P,heap] ∧
      a+L ≤ heap ∧ d+L ≤ heap ∧ Valid mem a h L ∧ Valid mem d h L ∧
      0 < intVal mem d h L ∧
      stretchArithmeticFits h L P (intVal mem a h L) (intVal mem d h L))
    (fun args mem out =>
      let L := args.getD 2 0
      let P := args.getD 3 0
      let result := heapArg args + stretchFromLengthSpace L - L
      Valid out result h L ∧ fixVal out result h L P =
        roundStretch P (1 + (intVal mem (args.getD 0 0) h L : ℝ) /
          (intVal mem (args.getD 1 0) h L : ℝ)))
    (fun args _ => stretchFromLengthCost (args.getD 2 0))
    (fun args _ => stretchFromLengthSpace (args.getD 2 0))
  { C with post := fun args mem ret out =>
      ret = heapArg args + stretchFromLengthSpace (args.getD 2 0) ∧ C.post args mem ret out }

/-- Expose the rounded stretch arithmetic as a callable procedure. -/
theorem stretchFromLength_meetsContract {w h entry add neg divide : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3*h+2 ≤ w)
    (he : p.procs[entry]? = some (stretchFromLengthBody add neg divide))
    (ha : p.HasAt add (addCarryModule add h)) (hn : p.HasAt neg (negateCarryModule neg h))
    (hd : p.HasAt divide (fixedDivideModule divide h)) :
    MeetsContract w p entry (stretchFromLengthContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,d,L,P,heap,rfl,ha',hd',hva,hvd,hpos,hs,hn',hq,ho⟩,hz,hroom⟩ := hpre
  obtain ⟨o, st, c, hr, ⟨hret, hv, hval, hf, hz'⟩, hcost⟩ :=
    stretchFromLength_runs hh hw ha hn hd a d L P heap pos mem ω ha' hd' hva hvd
      (hwords P (by simp)) hz hroom hpos hs hn' hq ho
  have hle : heap ≤ o.value := hret ▸ Nat.le_add_right _ _
  rw [hret] at hv hval
  exact ⟨o, st, c, hr, ⟨hret,hle,hret.le,hf,hz',hv,hval⟩, hcost⟩

/-- The stretch ceiling bounds both signs of the quotient numerator
used by the divide and sign restoration calls. -/
theorem stretchQuotient_fits {h L P : ℕ} {path edge : ℤ} {B : ℝ}
    (hpath : 0 ≤ path) (hedge : 0 < edge)
    (hB : roundStretch P (1 + (path : ℝ) / (edge : ℝ)) ≤ B)
    (hwidth : 2 * (2 : ℝ)^P * B < capacity h L) :
    let q := floorDiv (-(path + edge) * (2 : ℤ)^P) edge
    Fits h L q ∧ Fits h L (-q) := by
  intro q
  have he : (-(q : ℝ)) / (2 : ℝ)^P = roundStretch P (1 + (path : ℝ) / (edge : ℝ)) := by
    dsimp only [q]
    rw [roundStretch_of_integer_lengths P path edge hedge, floorDiv,
      ite_eq_right (not_lt.mpr hedge.le), neg_mul, add_comm path edge]
  have hq₀ : q ≤ 0 := by
    dsimp only [q]
    rw [floorDiv, ite_eq_right (not_lt.mpr hedge.le)]
    apply Int.lt_add_one_iff.mp
    apply (Int.ediv_lt_iff_lt_mul hedge).mpr
    rw [zero_add, one_mul]
    exact (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (add_nonneg hpath hedge.le)) (by positivity)).trans_lt hedge
  have hb := (div_le_iff₀ (by positivity : (0 : ℝ) < 2^P)).mp (he.trans_le hB)
  have hreal : 2 * (-(q : ℝ)) < capacity h L := by
    have hh := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 2 by norm_num)
    linarith only [hh,hwidth]
  have hint : 2 * (-q) < (capacity h L : ℤ) := by exact_mod_cast hreal
  have hc : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  exact ⟨⟨by omega,by omega⟩,⟨by omega,hint⟩⟩

end MinCostFlow.LastLevelProgram
