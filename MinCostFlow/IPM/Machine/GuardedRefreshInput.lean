module

public import MinCostFlow.IPM.Machine.GuardedEdgeInput
public import MinCostFlow.IPM.Machine.EdgeCoefficientRefresh

/-!
# Scalar source conditions before checking the slack range

The held residual, cost, alpha and one have the fixed-point conditions
required by the numerical gradient procedure. The flow and capacities
are valid blocks, but their slack ranges have not yet been accepted.
The actual slack guard supplies those missing ranges before either
power routine runs. This separates input arithmetic conditions from the
acceptance test without assuming that the candidate flow is feasible.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Numeric source and precision conditions, excluding the slack ranges
that the machine guard will check. These are input side conditions only. -/
def scalarCoefficientSourceConditions (w h q K m c r lo f up a one mn mx L P E heap : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  h∣P ∧ q+4*E+42≤P ∧ P+K+4*E+30≤h*L ∧ 2*P+9<2^w ∧
  20*m<2^w ∧ 20*m≤2^K ∧ |20*(m:ℤ)*Num.intVal mem c h L|≤(2:ℤ)^K ∧
  c+L≤heap ∧ r+L≤heap ∧ lo+L≤heap ∧ f+L≤heap ∧ up+L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
  Num.Valid mem c h L ∧ Num.Valid mem r h L ∧ Num.Valid mem lo h L ∧ Num.Valid mem f h L ∧
  Num.Valid mem up h L ∧ Num.Valid mem a h L ∧ Num.Valid mem one h L ∧
  Num.intVal mem one h L=(2:ℤ)^P ∧
  1/(2:ℝ)^E≤Num.fixVal mem r h L P ∧ Num.fixVal mem r h L P≤(2:ℝ)^E ∧
  0≤Num.fixVal mem a h L P ∧ Num.fixVal mem a h L P≤1 ∧
  ScalarAt mem mn h L P (1/(2:ℝ)^E) ∧ ScalarAt mem mx h L P ((2:ℝ)^E)

/-- The actual accepted guard completes the scalar numeric conditions
and hence every input premise of the coefficient refresh and its writes. -/
theorem edgeCoefficient_pre_of_source_conditions {w h q K m c r lo f up a one mn mx L P E ld gd heap v : ℕ}
    {mem mem' : ℕ → ℕ}
    (hs : scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E heap mem)
    (hout : (guardedSlacksContract w h).post [lo,f,up,mn,mx,L,P,heap] mem v mem')
    (haccept : mem' (heap+4*L)=1)
    (hld : ld+L≤heap) (hgd : gd+L≤heap) (hdis : ld+L≤gd ∨ gd+L≤ld)
    (hspace : v+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1<2^w) :
    (edgeCoefficientRefreshContract w h q K).pre [m,c,r,lo,f,up,a,one,L,P,E,ld,gd,v] mem' := by
  obtain ⟨hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hlo,hf,hup,ha,ho,
    hvc,hvr,hvl,hvf,hvu,hva,hvo,hone,hrl,hrh,ha0,ha1,hmin,hmax⟩ := hs
  have honeAt : ScalarAt mem one h L P 1 := by
    refine ⟨hvo,?_⟩
    unfold Num.fixVal
    rw [hone]
    norm_num
  have hd := guardedSlacks_edgeData hout ⟨hvl,rfl⟩ ⟨hvf,rfl⟩ ⟨hvu,rfl⟩
    hmin hmax ⟨hva,rfl⟩ honeAt hlo hf hup ha ho ha0 ha1 haccept
  obtain ⟨hvl',hvf',hvu',hva',hvo',hone',hul,huh,hdl,hdh,ha0',ha1'⟩ := hd
  have hframe := hout.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hframe
  have hv := hout.2
  change v=heap+(4*L+1) at hv
  have hz := hout.1.2.2.2.1
  change ZeroFrom mem' v at hz
  have hcB' : |20*(m:ℤ)*Num.intVal mem' c h L|≤(2:ℤ)^K := by
    rw [Num.IPM.value_frozen (h:=h) hframe hc]
    exact hcB
  have hrl' : 1/(2:ℝ)^E≤Num.fixVal mem' r h L P := by
    rw [Num.IPM.fixVal_frozen hframe hr]; exact hrl
  have hrh' : Num.fixVal mem' r h L P≤(2:ℝ)^E := by
    rw [Num.IPM.fixVal_frozen hframe hr]; exact hrh
  have hlen : (Num.IPM.lengthContract w h q).pre [lo,f,up,a,one,L,P,E,v] mem' := by
    exact ⟨⟨lo,f,up,a,one,L,P,E,v,rfl,hP,by omega,by omega,hPw,
      by omega,by omega,by omega,by omega,by omega,
      hvl',hvf',hvu',hva',hvo',hone',hul,huh,hdl,hdh,ha0',ha1'⟩,hz,
      by change v+Num.IPM.lengthSpace L P E<2^w; omega⟩
  have hgrad : (Num.IPM.gradientContract w h q K).pre [m,c,r,lo,f,up,a,one,L,P,E,v] mem' := by
    exact ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,v,rfl,hP,hprec,hwidth,hPw,hmw,hmB,hcB',
      by omega,by omega,by omega,by omega,by omega,by omega,by omega,
      Num.IPM.valid_frozen hframe hc hvc,Num.IPM.valid_frozen hframe hr hvr,
      hvl',hvf',hvu',hva',hvo',hone',hrl',hrh',hul,huh,hdl,hdh,ha0',ha1'⟩,hz,
      by change v+Num.IPM.gradientSpace L P E<2^w; omega⟩
  exact ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,ld,gd,v,rfl,by omega,by omega,hdis,hlen,hgrad⟩,hspace⟩

end MinCostFlow.IPM.Machine
