module

public import MinCostFlow.Num.FixedDivide
public import MinCostFlow.Num.ReciprocalFacts
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Relative-error reciprocal

Divide a stored fixed-point one by the positive input using fixed-point floor
division. The constant one is supplied as a reusable block. The precision and
width inequalities imply the required error and signed range bounds. All scratch
space, word bounds, and memory preservation come from the division procedure.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[one,x,L,P,heap]`, with `one` a stored fixed-point one. -/
def reciprocalModule (b h : ℕ) : List Stmt := fixedDivideModule b h

/-- Reciprocal on inputs in `[2⁻ᴱ,2ᴱ]`. The result occupies the last `L`
cells below the returned heap pointer. Precision must satisfy `E+q≤P` and
`P+E+2≤h*L`. Space and cost are exactly those of fixed-point division. -/
def reciprocalContract (w h E q : ℕ) : Contract where
  pre args mem := (∃ one a L P heap, args=[one,a,L,P,heap] ∧ h∣P ∧
    one+L≤heap ∧ a+L≤heap ∧ Valid mem one h L ∧ Valid mem a h L ∧
    intVal mem one h L=(2:ℤ)^P ∧
    1/(2:ℝ)^E≤fixVal mem a h L P ∧ fixVal mem a h L P≤(2:ℝ)^E ∧
    E+q≤P ∧ P+E+2≤h*L) ∧
    ZeroFrom mem (heapArg args) ∧
    heapArg args+fixedDivideSpace (args.getD 2 0)<2^w
  post args mem v mem' := (fixedDivideContract w h).post args mem v mem' ∧
    |fixVal mem' (v-args.getD 2 0) h (args.getD 2 0) (args.getD 3 0)-
      1/fixVal mem (args.getD 1 0) h (args.getD 2 0) (args.getD 3 0)| ≤
      (1/(2:ℝ)^q)/fixVal mem (args.getD 1 0) h (args.getD 2 0) (args.getD 3 0)
  cost := (fixedDivideContract w h).cost

/-- The reciprocal procedure is deterministic. -/
theorem reciprocalModule_noRand (b h : ℕ) : ∀ s∈reciprocalModule b h,s.NoRand :=
  fixedDivideModule_noRand b h

/-- Division by the input proves the reciprocal contract. The lower input
bound ensures positivity and a fitting output. The upper bound controls the
relative error from the single final rounding. -/
theorem reciprocal_meetsContract {w h b E q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (reciprocalModule b h)) :
    MeetsContract w p b (reciprocalContract w h E q) := by
  have hc := fixedDivide_meetsContract hh hw hp
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨one,a,L,P,heap,rfl,hP,ho,ha,hvo,hva,hone,hlo,hhi,hprec,hwidth⟩,hz,hbound⟩
  have hpos : 0<fixVal mem a h L P := lt_of_lt_of_le (by positivity) hlo
  have hne : intVal mem a h L≠0 := by
    intro he
    have hzv : fixVal mem a h L P=0 := by simp only [fixVal,he,Int.cast_zero,zero_div]
    rw [hzv] at hpos
    exact (lt_irrefl 0) hpos
  have hfit : Fits h L (floorDiv (intVal mem one h L*(2:ℤ)^P) (intVal mem a h L)) := by
    rw [reciprocal_floorDiv hone]
    exact reciprocal_floor_fits hlo hwidth
  have hold : (fixedDivideContract w h).pre [one,a,L,P,heap] mem :=
    ⟨⟨one,a,L,P,heap,rfl,hP,ho,ha,hvo,hva,hne,hfit⟩,hz,hbound⟩
  obtain ⟨body,hbody,o,st,c,hrun,hpost,hcost⟩ := hc _ _ pos ω hwords hold
  refine ⟨body,hbody,o,st,c,hrun,⟨hpost,?_⟩,hcost⟩
  rcases hpost with ⟨hv,_,_,_,_,_,hval⟩
  change o.value=heap+fixedDivideSpace L at hv
  change intVal st.mem (heap+9*L+integerDivideSpace (3*L)) h L=
    floorDiv (intVal mem one h L*(2:ℤ)^P) (intVal mem a h L) at hval
  have hptr : o.value-L=heap+9*L+integerDivideSpace (3*L) := by
    rw [hv]; unfold fixedDivideSpace; omega
  change |fixVal st.mem (o.value-L) h L P-1/fixVal mem a h L P|≤
    (1/(2:ℝ)^q)/fixVal mem a h L P
  rw [hptr]
  change |(intVal st.mem (heap+9*L+integerDivideSpace (3*L)) h L : ℝ)/(2:ℝ)^P-
    1/fixVal mem a h L P|≤_
  rw [hval,reciprocal_floorDiv hone]
  exact reciprocal_floor_relative hpos hhi hprec

end MinCostFlow.Num
