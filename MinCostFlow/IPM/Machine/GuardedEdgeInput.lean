module

public import MinCostFlow.IPM.Machine.GuardedSlacks
public import MinCostFlow.IPM.Machine.LengthArrayPrecision
import WordRAM.Memory

/-!
# Numerical edge inputs certified by actual slack guards

An accepted slack check gives both range conditions needed by the
numerical power routines. The check preserves all original scalar
blocks, including alpha and one. Consequently the next numerical call
gets its full `EdgeData` from computed values and the actual acceptance
bit, without assuming a potential bound for a rejected target.
-/

public section
namespace MinCostFlow.IPM.Machine

private theorem scalar_frozen {mem mem' : ℕ → ℕ} {a h L P heap : ℕ} {x : ℝ}
    (hf : ∀ z < heap,mem' z=mem z) (ha : a+L ≤ heap)
    (hx : ScalarAt mem a h L P x) : ScalarAt mem' a h L P x :=
  ⟨Num.IPM.valid_frozen hf ha hx.1,(Num.IPM.fixVal_frozen hf ha).trans hx.2⟩

/-- The actual accepted guard, exact source blocks, and stored alpha/one
supply every edge-data premise for the following length or gradient call. -/
theorem guardedSlacks_edgeData {w h lo fp up mn mx ap one L P E heap v : ℕ}
    {mem mem' : ℕ → ℕ} {lower flow upper a : ℝ}
    (hout : (guardedSlacksContract w h).post [lo,fp,up,mn,mx,L,P,heap] mem v mem')
    (hlo : ScalarAt mem lo h L P lower) (hf : ScalarAt mem fp h L P flow)
    (hup : ScalarAt mem up h L P upper)
    (hmin : ScalarAt mem mn h L P (1/(2:ℝ)^E)) (hmax : ScalarAt mem mx h L P ((2:ℝ)^E))
    (ha : ScalarAt mem ap h L P a) (hone : ScalarAt mem one h L P 1)
    (hloEnd : lo+L ≤ heap) (hfEnd : fp+L ≤ heap) (hupEnd : up+L ≤ heap)
    (haEnd : ap+L ≤ heap) (honeEnd : one+L ≤ heap)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haccept : mem' (heap+4*L)=1) :
    Num.IPM.EdgeData mem' lo fp up ap one h L P E := by
  have hframe := hout.1.2.2.1
  change ∀ z < heap,mem' z=mem z at hframe
  have hiff := hout.1.2.2.2.2.2
  change mem' (heap+4*L)=1 ↔
    (Num.fixVal mem mn h L P < Num.fixVal mem up h L P-Num.fixVal mem fp h L P ∧
      Num.fixVal mem up h L P-Num.fixVal mem fp h L P < Num.fixVal mem mx h L P) ∧
    (Num.fixVal mem mn h L P < Num.fixVal mem fp h L P-Num.fixVal mem lo h L P ∧
      Num.fixVal mem fp h L P-Num.fixVal mem lo h L P < Num.fixVal mem mx h L P) at hiff
  have hs := hiff.mp haccept
  rw [hmin.2,hmax.2,hlo.2,hf.2,hup.2] at hs
  exact edgeData_of_scalarAt (scalar_frozen hframe hloEnd hlo) (scalar_frozen hframe hfEnd hf)
    (scalar_frozen hframe hupEnd hup) (scalar_frozen hframe haEnd ha)
    (scalar_frozen hframe honeEnd hone) hs.1.1.le hs.1.2.le hs.2.1.le hs.2.2.le ha0 ha1

end MinCostFlow.IPM.Machine
