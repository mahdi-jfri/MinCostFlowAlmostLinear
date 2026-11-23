module

public import MinCostFlow.Final.ScratchCapacityStep
public import MinCostFlow.Scaling.CapacityResidualSpace
import MinCostFlow.Scaling.CapacityRoundedSpace
import MinCostFlow.Scaling.CapacityNumericFacts
import MinCostFlow.Scaling.BottleneckGuestSpace
import WordRAM.LinkDefs

/-!
# A uniform word bound for capacity steps

The common numerical base bounds the encoded residual and the clipped
solve. Raising the guest bounds of the base to the ratio of the word
multipliers gives polynomial reservations for both solver calls.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The factor by which the new multiplier can increase an old guest width. -/
def scratchWidthFactor (c d : ℕ) : ℕ :=
  (scratchWordMultiplier c d + 4) / 5

theorem scratchWidthFactor_pos (c d : ℕ) : 1 ≤ scratchWidthFactor c d := by
  unfold scratchWidthFactor scratchWordMultiplier
  omega

theorem scratchWordSize_le (c d : ℕ) (xs : List ℕ) :
    wordSize (scratchWordMultiplier c d) xs ≤ wordSize 5 xs * scratchWidthFactor c d := by
  have h : scratchWordMultiplier c d ≤ 5 * scratchWidthFactor c d := by
    unfold scratchWidthFactor
    omega
  unfold wordSize
  rw [Nat.mul_right_comm 5]
  exact Nat.mul_le_mul_right _ h

theorem scratchWordCapacity_le (c d : ℕ) (xs : List ℕ) :
    2 ^ wordSize (scratchWordMultiplier c d) xs ≤
      (2 ^ wordSize 5 xs) ^ scratchWidthFactor c d := by
  rw [←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (scratchWordSize_le c d xs)

theorem scratchBottleneckGuestBound_le (c d : ℕ) (J : Circulation) (xs : List ℕ) :
    scratchBottleneckGuestBound c d J xs ≤ bottleneckGuestBound J xs * scratchWidthFactor c d := by
  apply List.max_le_of_forall_le
  intro x hx
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
  exact (scratchWordSize_le c d _).trans (Nat.mul_le_mul_right _ (bottleneckGuest_le J hu))

private theorem widen_power {x y n e f : ℕ} (h : 2^x ≤ (2^y)^f) (hy : 2^y ≤ n^e) :
    2^x ≤ n^(e*f) := h.trans (by rw [pow_mul]; exact Nat.pow_le_pow_left hy f)

theorem scratchBottleneckGuest_region (c d : ℕ) (J : Circulation) (xs : List ℕ) :
    2^scratchBottleneckGuestBound c d J xs ≤
      (J.solverWords.length+J.solverWords.foldr max 0+2)^(10*scratchWidthFactor c d) := by
  apply widen_power _ (bottleneckGuestBound_space_le J xs)
  rw [←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (scratchBottleneckGuestBound_le c d J xs)

theorem scratchRoundedGuest_region (c d : ℕ) (J : Circulation) (B N : ℕ) (hN : 4≤N)
    (hn : J.n≤N) (hm : J.m≤N) (hc : J.CostsBounded N) (hpos : 0<J.m) (hB : 0<B) :
    2^wordSize (scratchWordMultiplier c d) (J.scaledRoundedInstance B).positiveInstance.solverWords ≤
      N^(215*scratchWidthFactor c d) :=
  widen_power (scratchWordCapacity_le c d _) (capacityRoundedGuest_space_le J B N hN hn hm hc hpos hB)

/-- Uniform per-step reserve exponent. At coefficient one and degree four
it equals the original exponent 256. -/
def scratchCapacityExponent (c d : ℕ) : ℕ := 256*scratchWidthFactor c d

theorem scratchCapacityExponent_original : scratchCapacityExponent 1 4 = 256 := by
  decide

/-- The widened approximation and rounded solve fit one uniform step reserve. -/
theorem scratchCapacityStepSpace_le (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ)
    (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (hm : 0<J.m)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) :
    scratchCapacityStepSpace solver entry T S c d hproc J s ≤
      (capacityStepNumberBase J C U)^scratchCapacityExponent c d := by
  let D := capacityStepNumberBase J C U
  let f := scratchWidthFactor c d
  let R := J.residual s.flow
  let solve := fun K : Circulation => compressedCanonicalSolverAt _ solver entry T S (hproc K) K
  let B := (polyApproxModel solve R).value.magnitude
  let L := Nat.clog 2 (R.m+1)
  let G := scratchBottleneckGuestBound c d R (sortCapacities (List.ofFn R.capacity)).1
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hDpos : 0<D := by omega
  have hfpos : 1≤f := scratchWidthFactor_pos c d
  have hRm : R.m = J.m+J.m := rfl
  have hRn : R.n = J.n := rfl
  have hmD : R.m≤D := by omega
  have hnD : R.n≤D := by omega
  have hL : L+1≤D := by
    have hlog : L≤R.m+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    omega
  have hguest : 2^G≤D^(40*f) := by
    have h := Nat.pow_le_pow_left (capacityResidual_encoding_bounds J s C U hf hC hu).2 (10*f)
    rw [←pow_mul, show 4*(10*f)=40*f by omega] at h
    exact (scratchBottleneckGuest_region c d R _).trans h
  have hD40 : D≤D^(40*f) := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right hDpos (show 1≤40*f by omega)
  have hbody : 12+15*R.m+2^G≤32*D^(40*f) := by omega
  have hsearch : (L+1)*(12+15*R.m+2^G)≤32*D^(40*f+1) := by
    have h := Nat.mul_le_mul hL hbody
    simpa only [Nat.mul_left_comm D, ←pow_succ'] using h
  have hsmall : (L+1)*R.m≤D^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul hL hmD
  have hD2 : D≤D^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hDpos (show 1≤2 by decide)
  have hpowSmall : D^2≤D^(215*f) := Nat.pow_le_pow_right hDpos (by omega)
  have hpowSearch : D^(40*f+1)≤D^(215*f) := Nat.pow_le_pow_right hDpos (by omega)
  have hr : scratchCapacityRoundedSpace c d R B≤16*D^(215*f) := by
    have hDlarge := hD2.trans hpowSmall
    by_cases hb : B=0
    · simp only [scratchCapacityRoundedSpace,hb,↓reduceIte]
      omega
    · have hcost : R.CostsBounded D := fun e => (J.residual_costsBounded s.flow C hC e).trans (by omega)
      have hg := scratchRoundedGuest_region c d R B D hD4 hnD hmD hcost (by omega) (Nat.pos_of_ne_zero hb)
      change _ ≤ D^(215*f) at hg
      simp only [scratchCapacityRoundedSpace,hb,↓reduceIte]
      omega
  have hpow : 128*D^(215*f)≤D^(256*f) := by
    have h128 : 128≤D^4 := (by decide : 128≤4^4).trans (Nat.pow_le_pow_left hD4 4)
    have h := Nat.mul_le_mul_right (D^(215*f)) h128
    rw [←pow_add] at h
    exact h.trans (Nat.pow_le_pow_right hDpos (by omega))
  apply le_trans _ hpow
  change 2+10*J.m+(R.m+(L+1)*R.m+5+(L+1)*(12+15*R.m+2^G)+10+3*R.n+33*R.m+12)+
    scratchCapacityRoundedSpace c d R B+J.m+2+4≤128*D^(215*f)
  have hDlarge := hD2.trans hpowSmall
  have hsearch' := hsearch.trans (Nat.mul_le_mul_left 32 hpowSearch)
  omega

/-- All numerical and workspace premises of a capacity step follow from
one uniform reserve and the original graph's coordinate bounds. -/
theorem scratchCapacityStep_pre_of_space {w : ℕ} (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hm : 0<J.m) (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e)
    (hC : J.CostsBounded C) (hu : ∀ e,J.capacity e≤U)
    (a state heap : ℕ) (mem : ℕ → ℕ) (hgraph : ListAt mem a J.solverWords)
    (hgraphEnd : a+J.solverWords.length≤heap) (hstateEnd : state+2=heap)
    (hstate : CapacityStateAt mem state heap s) (hz : ZeroFrom mem heap)
    (hspace : heap+(capacityStepNumberBase J C U)^(scratchCapacityExponent c d)<2^w) :
    (scratchCapacityStepContract w solver entry T S c d hproc J s C U).pre [a,state,heap] mem := by
  let D := capacityStepNumberBase J C U
  let R := J.residual s.flow
  let B := (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) R).value.magnitude
  let G := scratchBottleneckGuestBound c d R (sortCapacities (List.ofFn R.capacity)).1
  let g := wordSize (scratchWordMultiplier c d) (R.scaledRoundedInstance B).positiveInstance.solverWords
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hDpos : 0<D := by omega
  have hpower : D^(scratchCapacityExponent c d)<2^w := by change heap+D^(scratchCapacityExponent c d)<2^w at hspace; omega
  have h2 : 16≤D^2 := Nat.pow_le_pow_left hD4 2
  have hlinear : 4*D≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul_right D hD4
  have hexp : 256 ≤ scratchCapacityExponent c d := by
    have h := scratchWidthFactor_pos c d
    unfold scratchCapacityExponent
    omega
  have hD256 : D≤D^(scratchCapacityExponent c d) := by simpa only [pow_one] using Nat.pow_le_pow_right hDpos (by omega : 1≤scratchCapacityExponent c d)
  have h2_256 : D^2≤D^(scratchCapacityExponent c d) := Nat.pow_le_pow_right hDpos (by omega)
  have h3_256 : D^3≤D^(scratchCapacityExponent c d) := Nat.pow_le_pow_right hDpos (by omega)
  have h4_256 : D^4≤D^(scratchCapacityExponent c d) := Nat.pow_le_pow_right hDpos (by omega)
  have h23_256 : D^23≤D^(scratchCapacityExponent c d) := Nat.pow_le_pow_right hDpos (by omega)
  have hRn : R.n=J.n := rfl
  have hRm : R.m=J.m+J.m := rfl
  have hRmD : R.m≤D := by rw [hRm]; omega
  have hCD : C≤D := by omega
  have hUD : U≤D := by omega
  have hC_R := J.residual_costsBounded s.flow C hC
  have hRcap := J.residual_capacities_le s.flow (integral_capacity_bounds_cast J s.flow hf) U hu
  have hpolyR := J.residual_polynomialCosts s.flow hc
  have hsourceMax : J.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J D
    (by omega) (by omega) (fun e => (hu e).trans hUD) (fun e => (hC e).trans hCD) (by omega)
  have hresidual := capacityResidual_encoding_bounds J s C U hf hC hu
  have hresMax : R.solverWords.foldr max 0≤D^2 := hresidual.1
  have hresBase : R.solverWords.length+R.solverWords.foldr max 0+2≤D^4 := hresidual.2
  have hsourceWords : ∀ x∈J.solverWords,x<2^w := fun x hx =>
    ((Link.elem_le_foldr_max hx).trans hsourceMax).trans_lt (hD256.trans_lt hpower)
  have hresWords : ∀ x∈R.solverWords,x<2^w := fun x hx =>
    ((Link.elem_le_foldr_max hx).trans hresMax).trans_lt (h2_256.trans_lt hpower)
  have hmass : R.m*C≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul hRmD hCD
  have hbudget : (6*R.m+2)*C≤D^4 := by
    have hfactor : 6*R.m+2≤8*D := by omega
    have hmul : (6*R.m+2)*C≤8*D^2 := by
      simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul hfactor hCD
    have h4 : 16*D^2≤D^4 := by
      have h := Nat.mul_le_mul_right (D^2) h2
      simpa only [←pow_add] using h
    omega
  have hproduct : R.m*(C*U)≤D^3 := by
    simpa only [pow_succ',pow_two,pow_zero,Nat.mul_one] using Nat.mul_le_mul hRmD (Nat.mul_le_mul hCD hUD)
  have hB : B≤D^3 :=
    (scratchPolyApprox_magnitude_le solver entry T S c d hproc R C U hpolyR hC_R hRcap).trans hproduct
  have hround : B*R.m^20≤D^23 := by
    have h := Nat.mul_le_mul hB (Nat.pow_le_pow_left hRmD 20)
    simpa only [←pow_add] using h
  let f := scratchWidthFactor c d
  have hfpos : 1≤f := scratchWidthFactor_pos c d
  have he : scratchCapacityExponent c d = 256*f := rfl
  have hguest : 2^G≤D^(40*f) := by
    have h := Nat.pow_le_pow_left hresBase (10*f)
    rw [←pow_mul, show 4*(10*f)=40*f by omega] at h
    exact (scratchBottleneckGuest_region c d R _).trans h
  have hmargin {x e : ℕ} (hx : 2^x≤D^e) (he' : e+1≤scratchCapacityExponent c d) :
      2^(x+1)+2≤2^w := by
    have hp : 1≤D^e := Nat.one_le_pow e _ (by omega)
    have hnext : 4*D^e≤D^(e+1) :=
      (Nat.mul_le_mul_right (D^e) hD4).trans_eq (pow_succ' D e).symm
    have htot : 2^(x+1)+2≤4*D^e := by rw [pow_succ]; omega
    exact (htot.trans (hnext.trans (Nat.pow_le_pow_right hDpos he'))).trans hpower.le
  have hguestMargin : 2^(G+1)+2≤2^w := hmargin hguest (by omega)
  have hroundMargin : B=0 ∨ 2^(g+1)+2≤2^w := by
    by_cases hb : B=0
    · exact Or.inl hb
    · right
      have hcost : R.CostsBounded D := fun e => (hC_R e).trans hCD
      have hg := scratchRoundedGuest_region c d R B D hD4
        (by rw [hRn]; omega) hRmD hcost (by rw [hRm]; omega) (Nat.pos_of_ne_zero hb)
      change 2^g≤D^(215*f) at hg
      exact hmargin hg (by omega)
  have hreserve := scratchCapacityStepSpace_le solver entry T S c d hproc J s C U hm hf hC hu
  refine ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hsourceWords,hresWords,hf,hC,hu,hm,hz,
    (Nat.add_le_add_left hreserve heap).trans_lt hspace,?_,hmass.trans_lt (h2_256.trans_lt hpower),
    hguestMargin,hbudget.trans_lt (h4_256.trans_lt hpower),
    hproduct.trans_lt (h3_256.trans_lt hpower),hround.trans_lt (h23_256.trans_lt hpower),hroundMargin,?_,?_⟩
  · have hsmall : R.m+2≤D^2 := by omega
    exact (hsmall.trans h2_256).trans_lt hpower
  · have hadd : 2*U≤D^2 := by omega
    exact (hadd.trans h2_256).trans_lt hpower
  · omega


end MinCostFlow.Final
