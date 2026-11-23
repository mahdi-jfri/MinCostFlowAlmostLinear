module

public import MinCostFlow.IPM.Machine.ForestContract
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.Num.Floor
import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity

/-!
# Reading the rounder's exact arithmetic outputs

A fitting rational specifies its integer numerator uniquely. The
rounder's arithmetic can therefore read the existing wrapped
fixed-point operations exactly when their rational result fits.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The rational reading of a valid block preserves its value under a
memory frame covering that block. -/
theorem RatAt.frozen {mem mem' : ℕ → ℕ} {p h L P heap : ℕ} {q : ℚ}
    (hq : RatAt mem p h L P q) (hframe : ∀ z<heap,mem' z=mem z) (hend : p+L≤heap) :
    RatAt mem' p h L P q := by
  exact ⟨Num.IPM.valid_frozen hframe hend hq.1,by
    unfold readRat at *
    rw [Num.IPM.value_frozen hframe hend]
    exact hq.2⟩

/-- Pointwise agreement on the block suffices to preserve its exact value. -/
theorem RatAt.agree {mem mem' : ℕ → ℕ} {p h L P : ℕ} {q : ℚ}
    (hq : RatAt mem p h L P q) (hframe : ∀ i<L,mem' (p+i)=mem (p+i)) :
    RatAt mem' p h L P q := by
  refine ⟨fun i hi => (hframe i hi).symm ▸ hq.1 i hi,?_⟩
  unfold readRat
  rw [Num.intVal_congr hframe]
  exact hq.2

/-- A fitting value represented by a specified numerator gives the
signed fit of that numerator. -/
theorem ratFits_numerator {h L P : ℕ} {z : ℤ}
    (hf : RatFits h L P ((z:ℚ)/(2:ℚ)^P)) : Num.Fits h L z := by
  obtain ⟨r,hr,he⟩ := hf
  have heq := (div_left_inj' (by positivity : (2:ℚ)^P≠0)).mp he
  have h : z=r := by exact_mod_cast heq
  exact h.symm ▸ hr

/-- The subtraction output is exact for a fitting rational difference. -/
theorem round_subtract_output {w h L P a b heap v : ℕ} {mem final : ℕ → ℕ} {x y : ℚ}
    (ha : RatAt mem a h L P x) (hb : RatAt mem b h L P y) (hfit : RatFits h L P (x-y))
    (hout : (Num.subtractContract w h).post [a,b,L,heap] mem v final) :
    v=heap+2*L ∧ (∀ z<heap,final z=mem z) ∧ ZeroFrom final v ∧
      RatAt final (heap+L) h L P (x-y) := by
  obtain ⟨hv,_,_,hframe,hzero,hvalid,hvalue⟩ := hout
  have he : x-y=((Num.intVal mem a h L-Num.intVal mem b h L:ℤ):ℚ)/(2:ℚ)^P := by
    rw [← ha.2,← hb.2]
    simp only [readRat,Int.cast_sub,sub_div]
  have hf : Num.Fits h L (Num.intVal mem a h L-Num.intVal mem b h L) :=
    ratFits_numerator (he ▸ hfit)
  change Num.intVal final (heap+L) h L=Num.wrap h L (Num.intVal mem a h L-Num.intVal mem b h L) at hvalue
  rw [Num.wrap_of_fits hf] at hvalue
  refine ⟨hv,hframe,hzero,hvalid,?_⟩
  rw [readRat,hvalue,he]

/-- The unscaled floor returned by the machine is the rational floor. -/
theorem round_floor_output {w h L P a heap v : ℕ} {mem final : ℕ → ℕ} {x : ℚ}
    (ha : RatAt mem a h L P x)
    (hout : (Num.floorContract w h).post [a,L,P,heap] mem v final) :
    v=heap+2*L+1 ∧ (∀ z<heap,final z=mem z) ∧ ZeroFrom final v ∧
      Num.Valid final (heap+L+1) h L ∧ Num.intVal final (heap+L+1) h L=⌊x⌋ := by
  obtain ⟨hv,_,_,hframe,hzero,hvalid,hvalue⟩ := hout
  have hr : Num.fixVal mem a h L P=(x:ℝ) := by
    rw [← ha.2]
    simp only [readRat,Num.fixVal,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat]
  change Num.intVal final (heap+L+1) h L=⌊Num.fixVal mem a h L P⌋ at hvalue
  rw [hr,Rat.floor_cast] at hvalue
  exact ⟨hv,hframe,hzero,hvalid,hvalue⟩

/-- Loading the floor back at the working scale preserves its exact
integer value when the scaled block fits. -/
theorem round_shift_output {w h L P a heap v : ℕ} {mem final : ℕ → ℕ} {z : ℤ}
    (hz : Num.intVal mem a h L=z) (hfit : RatFits h L P (z:ℚ))
    (hout : (Num.shiftLeftContract w h).post [a,L,P,heap] mem v final) :
    v=heap+L ∧ (∀ x<heap,final x=mem x) ∧ ZeroFrom final v ∧ RatAt final heap h L P z := by
  obtain ⟨hv,_,_,hframe,hzero,hvalid,hvalue⟩ := hout
  have he : (z:ℚ)=((z*(2:ℤ)^P:ℤ):ℚ)/(2:ℚ)^P := by
    simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    rw [mul_div_cancel_right₀ _ (by positivity)]
  have hf : Num.Fits h L (z*(2:ℤ)^P) := ratFits_numerator (he ▸ hfit)
  change Num.intVal final heap h L=Num.wrap h L (Num.intVal mem a h L*(2:ℤ)^P) at hvalue
  rw [hz,Num.wrap_of_fits hf] at hvalue
  refine ⟨hv,hframe,hzero,hvalid,?_⟩
  rw [readRat,hvalue,← he]

end MinCostFlow.IPM.Machine
