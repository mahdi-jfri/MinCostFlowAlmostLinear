module

public import MinCostFlow.Num.ShiftRight
public import MinCostFlow.Num.DivisionSigns
import WordRAM.Logic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Floor of a fixed-point value

An arithmetic right shift by the precision computes the floor of the represented real
number. The procedure shares the verified right-shift bodies and their linear cost.
Its output represents an unscaled integer.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Fixed-point floor uses the arithmetic right-shift module, arguments `[a,L,P,heap]`. -/
def floorModule (b h : ℕ) : List Stmt := shiftRightModule b h

/-- The exact signed quotient by the precision scale is the real floor. -/
theorem floor_fixVal (mem : ℕ→ℕ) (a h L P : ℕ) :
    ⌊fixVal mem a h L P⌋=intVal mem a h L/(2:ℤ)^P := by
  have hp : (0:ℤ)≤(2:ℤ)^P := le_of_lt (pow_pos (by decide) _)
  have he := floorDiv_eq_floor (intVal mem a h L) ((2:ℤ)^P)
  simpa only [floorDiv,ite_eq_right (not_lt.mpr hp),Int.cast_pow,Int.cast_ofNat,fixVal] using he.symm

/-- Exact floor, stored as an unscaled integer at the standard right-shift output. -/
def floorContract (w h : ℕ) : Contract :=
  let C := shiftRightContract w h
  { C with post := fun args mem v mem' =>
      v=heapArg args+2*args.getD 1 0+1 ∧
      heapArg args≤v ∧ v≤heapArg args+(2*args.getD 1 0+1) ∧
      (∀ z<heapArg args,mem' z=mem z) ∧ ZeroFrom mem' v ∧
      Valid mem' (heapArg args+args.getD 1 0+1) h (args.getD 1 0) ∧
      intVal mem' (heapArg args+args.getD 1 0+1) h (args.getD 1 0)=
        ⌊fixVal mem (args.getD 0 0) h (args.getD 1 0) (args.getD 2 0)⌋ }

/-- Floor uses no random statement. -/
theorem floorModule_noRand (b h : ℕ) : ∀ s∈floorModule b h,s.NoRand := shiftRightModule_noRand b h

/-- Fixed-point floor meets its exact contract at cost `66*L+106`. -/
theorem floor_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 1<2^w) (hb : base h<2^w)
    (hp : p.HasAt b (floorModule b h)) : MeetsContract w p b (floorContract w h) := by
  intro args mem pos ω hwords hpre
  obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := shiftRight_meetsContract hh hw hb hp args mem pos ω hwords hpre
  refine ⟨body,hbody,o,st,c,hr,?_,hcost⟩
  simpa only [floorContract,shiftRightContract,heapContract,floor_fixVal,Nat.add_assoc] using hpost

end MinCostFlow.Num
