module

public import MinCostFlow.IPM.Machine.EpochStaticInputs
public import MinCostFlow.IPM.Machine.TargetEpochResult
public import MinCostFlow.IPM.Machine.EpochNextLayout
import MinCostFlow.IPM.Machine.ReportedTableLayout
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Immutable numerical sources of a target test

Each stage reads the original graph and scalar tables. The fresh
epoch adds only the previous explicit flow, its residual and a
mutable copy. Feasibility bounds the copied base using the same
capacity bound as the original tables.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Addresses and exact immutable values needed by each stage of the
target test. Geometric bounds place these blocks below the old heap. -/
structure TargetFixedInputs {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp heap : ℕ) (target normalization a : ℝ) (mem : ℕ → ℕ) : Prop where
  rows : ListAt mem L.graph (zeroLowerWords I)
  rowsEnd : L.graph+(zeroLowerWords I).length≤heap
  rowsWords : ∀ v∈zeroLowerWords I,v<2^w
  graph : GraphAt mem L.initGraph (namedInstance I)
  graphEnd : L.initGraph+(graphWords (namedInstance I)).length≤heap
  graphWordsFit : ∀ v∈graphWords (namedInstance I),v<2^w
  arrays : ∀ p∈[L.cost,L.lower,L.upper],p+I.m*F.limbs≤heap
  scalars : ∀ p∈[tp,qp,L.alpha,L.one,L.slackMin,L.slackMax,
    L.request,L.gradientMin,L.gradientMax,L.lengthMin],p+F.limbs≤heap
  cost : ∀ e : Fin I.m,ScalarAt mem (L.cost+e.val*F.limbs) F.fmt.limbBits F.limbs 0 (I.edge e).cost
  lower : ∀ e : Fin I.m,ScalarAt mem (L.lower+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision (I.edge e).lower
  upper : ∀ e : Fin I.m,ScalarAt mem (L.upper+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision (I.edge e).upper
  alpha : ScalarAt mem L.alpha F.fmt.limbBits F.limbs F.fmt.precision a
  one : ScalarAt mem L.one F.fmt.limbBits F.limbs F.fmt.precision 1
  targetValue : ScalarAt mem tp F.fmt.limbBits F.limbs F.fmt.precision target
  quarter : ScalarAt mem qp F.fmt.limbBits F.limbs F.fmt.precision (1/4)
  slackMin : ScalarAt mem L.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^L.exponent)
  slackMax : ScalarAt mem L.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^L.exponent)
  request : ScalarAt mem L.request F.fmt.limbBits F.limbs F.fmt.precision normalization
  gradientMin : ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent)
  gradientMax : ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent)
  lengthMin : ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ)))

/-- The fixed tables survive any stage that preserves its incoming
prefix. The next stage can therefore use the same static pointers. -/
theorem TargetFixedInputs.frozen {w : ℕ} {F : MinRatioFormat w} {I : Instance} {L : EpochLayout}
    {tp qp heap next : ℕ} {target normalization a : ℝ} {mem final : ℕ → ℕ}
    (h : TargetFixedInputs F I L tp qp heap target normalization a mem)
    (hframe : ∀ z<heap,final z=mem z) (hle : heap≤next) :
    TargetFixedInputs F I L tp qp next target normalization a final := by
  have scalar (p : ℕ) (hp : p+F.limbs≤heap) {prec : ℕ} {value : ℝ}
      (hs : ScalarAt mem p F.fmt.limbBits F.limbs prec value) :
      ScalarAt final p F.fmt.limbBits F.limbs prec value :=
    ⟨Num.IPM.valid_frozen hframe hp hs.1,(Num.IPM.fixVal_frozen hframe hp).trans hs.2⟩
  have entry (p : ℕ) (hp : p∈[L.cost,L.lower,L.upper]) (e : Fin I.m) :
      p+e.val*F.limbs+F.limbs≤heap := (reported_entry_end p F.limbs e.val I.m e.isLt).trans (h.arrays p hp)
  refine ⟨h.rows.congr (fun z _ hz => hframe z (hz.trans_le h.rowsEnd)),h.rowsEnd.trans hle,h.rowsWords,
    h.graph.congr (fun z _ hz => hframe z (hz.trans_le h.graphEnd)),h.graphEnd.trans hle,h.graphWordsFit,
    fun p hp => (h.arrays p hp).trans hle,fun p hp => (h.scalars p hp).trans hle,
    fun e => scalar _ (entry L.cost (by simp) e) (h.cost e),
    fun e => scalar _ (entry L.lower (by simp) e) (h.lower e),
    fun e => scalar _ (entry L.upper (by simp) e) (h.upper e),
    scalar _ (h.scalars L.alpha (by simp)) h.alpha,
    scalar _ (h.scalars L.one (by simp)) h.one,
    scalar _ (h.scalars tp (by simp)) h.targetValue,
    scalar _ (h.scalars qp (by simp)) h.quarter,
    scalar _ (h.scalars L.slackMin (by simp)) h.slackMin,
    scalar _ (h.scalars L.slackMax (by simp)) h.slackMax,
    scalar _ (h.scalars L.request (by simp)) h.request,
    scalar _ (h.scalars L.gradientMin (by simp)) h.gradientMin,
    scalar _ (h.scalars L.gradientMax (by simp)) h.gradientMax,
    scalar _ (h.scalars L.lengthMin (by simp)) h.lengthMin⟩

/-- Replace only the target operand after writing a new exact block. -/
theorem TargetFixedInputs.retarget {w : ℕ} {F : MinRatioFormat w} {I : Instance} {L : EpochLayout}
    {tp qp heap newTarget : ℕ} {target value normalization a : ℝ} {mem : ℕ → ℕ}
    (h : TargetFixedInputs F I L tp qp heap target normalization a mem)
    (hend : newTarget+F.limbs≤heap)
    (hvalue : ScalarAt mem newTarget F.fmt.limbBits F.limbs F.fmt.precision value) :
    TargetFixedInputs F I L newTarget qp heap value normalization a mem := by
  refine { h with targetValue := hvalue, scalars := ?_ }
  intro p hp
  rw [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hend
  · exact h.scalars p (List.mem_cons_of_mem _ hp)

/-- The explicit flow of a stage is strictly inside the capacity box. -/
theorem TargetStageFlow.inside {w E source heap : ℕ} {F : MinRatioFormat w} {I : Instance}
    {mem : ℕ → ℕ} (h : TargetStageFlow F I E source heap mem) :
    StrictlyInside I (epochVector F I mem source) := by
  intro e
  have hs := (h.2.2 e).2
  have hp : 0<1/(2:ℝ)^E := by positivity
  exact ⟨sub_pos.mp (hp.trans hs.2.1),sub_pos.mp (hp.trans hs.1.1)⟩

/-- The original immutable tables and the next exact base encode
every fixed input of the newly initialized epoch. -/
theorem TargetFixedInputs.epoch_static_at {w : ℕ} {F : MinRatioFormat w}
    {I : Instance} {U R : ℕ} {old : EpochLayout} {base rp fp heap names tp qp : ℕ}
    {κ α eps target normalization a : ℝ} {mem : ℕ → ℕ}
    (h : TargetFixedInputs F I old tp qp fp target normalization a mem)
    (hI : I.IsValid) (hnums : NumbersBounded I U) (hU : 0<U) (hm : 0<I.m)
    (hzero : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hbase : I.IsFeasible (epochVector F I mem base))
    (hbaseEnd : base+I.m*F.limbs≤fp) (hrEnd : rp+F.limbs≤fp)
    (ha0 : 0≤a) (ha1 : a≤1) (heps : 0<eps) (heps' : eps≤1)
    (hformat : F.rangeExponent=R)
    (hNormLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization)
    (hNormHi : normalization≤(2:ℝ)^F.rangeExponent)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+I.m.size+30≤F.fmt.precision)
    (hwords : ∀ z∈(old.next F I base rp fp heap names).packet F I 0,z<2^w) :
    EpochStaticInputsAt F I U R κ α eps (old.next F I base rp fp heap names) (U:ℝ) normalization mem := by
  let L := old.next F I base rp fp heap names
  have ha : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hs
    · exact hbaseEnd
    · exact h.arrays p hs
  have hs : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hs
    · exact hrEnd
    · exact h.scalars p (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hs ⊢
        tauto)
  have hg : ∀ p∈[old.request,old.gradientMin,old.gradientMax,old.lengthMin],p+F.limbs≤fp := by
    intro p hp
    exact h.scalars p (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
      tauto)
  have hUdyadic := twice_capacity_le_dyadic I.m U hm hU
  have hCap : (U:ℝ)≤(2:ℝ)^(slackRangeExponent I.m U) := by
    have hu : 0≤(U:ℝ) := Nat.cast_nonneg _
    linarith only [hUdyadic,hu]
  refine ⟨hwords,hI,h.rows,h.rowsEnd,h.rowsWords,ha,hs,hg,h.request,hNormLo,hNormHi,
    h.gradientMin,h.gradientMax,h.lengthMin,hquality,hprec,hCap,?_,?_,?_,hformat,heps,heps'⟩
  · intro j hj
    let e : Fin I.m := ⟨j,Finset.mem_range.mp hj⟩
    have he := hbase.2 e
    have hbound := hnums.2 e
    change |epochVector F I mem base e|≤U ∧ |epochVector F I mem old.lower e|≤U ∧ |epochVector F I mem old.upper e|≤U
    rw [show epochVector F I mem old.lower e=(I.edge e).lower from (h.lower e).2,
      show epochVector F I mem old.upper e=(I.edge e).upper from (h.upper e).2]
    exact ⟨abs_le.mpr ⟨(abs_le.mp hbound.1).1.trans he.1,he.2.trans (le_abs_self _ |>.trans hbound.2.1)⟩,
      hbound.1,hbound.2.1⟩
  · intro j hj
    let e : Fin I.m := ⟨j,Finset.mem_range.mp hj⟩
    change 0≤epochVector F I mem old.lower e
    rw [show epochVector F I mem old.lower e=(I.edge e).lower from (h.lower e).2]
    exact_mod_cast hzero e
  · change 0≤Num.fixVal mem old.alpha F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem old.alpha F.fmt.limbBits F.limbs F.fmt.precision≤1
    rw [h.alpha.2]
    exact ⟨ha0,ha1⟩

/-- The original immutable tables and the next exact base encode
every fixed input of the newly initialized epoch. -/
theorem TargetFixedInputs.epoch_static {w : ℕ} {F : MinRatioFormat w}
    {I : Instance} {U : ℕ} {old : EpochLayout} {base rp fp heap names tp qp : ℕ}
    {κ α eps target normalization a : ℝ} {mem : ℕ → ℕ}
    (h : TargetFixedInputs F I old tp qp fp target normalization a mem)
    (hI : I.IsValid) (hnums : NumbersBounded I U) (hU : 0<U) (hm : 0<I.m)
    (hzero : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hbase : I.IsFeasible (epochVector F I mem base))
    (hbaseEnd : base+I.m*F.limbs≤fp) (hrEnd : rp+F.limbs≤fp)
    (ha0 : 0≤a) (ha1 : a≤1) (heps : 0<eps) (heps' : eps≤1)
    (hformat : F.rangeExponent=ipmRangeExponent I.m U)
    (hNormLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization)
    (hNormHi : normalization≤(2:ℝ)^F.rangeExponent)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+I.m.size+30≤F.fmt.precision)
    (hwords : ∀ z∈(old.next F I base rp fp heap names).packet F I 0,z<2^w) :
    EpochStaticInputs F I U κ α eps (old.next F I base rp fp heap names) (U:ℝ) normalization mem :=
  h.epoch_static_at hI hnums hU hm hzero hbase hbaseEnd hrEnd ha0 ha1 heps heps'
    hformat hNormLo hNormHi hquality hprec hwords

end MinCostFlow.IPM.Machine
