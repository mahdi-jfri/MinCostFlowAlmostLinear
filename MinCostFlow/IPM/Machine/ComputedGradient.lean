module

public import MinCostFlow.Num.IPM.Gradient
public import MinCostFlow.Num.IPM.GradientArray
public import MinCostFlow.IPM.GradientStability
import Mathlib.Tactic.Ring

/-!
# Numerical gradients with a stored epoch residual

Within an epoch, the residual estimate is fixed while individual flow
coordinates are refreshed. It need not equal the residual at the mixed
stored flow. The numerical gradient routines accept that residual block
directly. Their output is the `gradientWithResidual` of Chen et al.,
arXiv:2203.00671v2, Lemma 4.10 (page 30), as used by Lemma 9.1 (page 70).
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- A supplied residual is the exact residual for a shifted target. -/
theorem gradient_at_stored_residual (I : Instance) (a r : ℝ)
    (f : Fin I.m → ℝ) :
    gradient I a (I.cost f-r) f=gradientWithResidual I a r f := by
  funext e
  unfold gradient gradientWithResidual residual
  rw [sub_sub_cancel]
  ring

/-- A refreshed numerical gradient entry uses the epoch's stored
residual, including when the stored flow has changed on other edges. -/
theorem computed_gradient_output (I : Instance) (f : Fin I.m → ℝ) (e : Fin I.m)
    {w h q K cp rp lo fp up ap one L P E heap v : ℕ} {mem mem' : ℕ → ℕ} {a r : ℝ}
    (hout : (Num.IPM.gradientContract w h q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem v mem')
    (hc : Num.intVal mem cp h L=(I.edge e).cost)
    (hr : Num.fixVal mem rp h L P=r)
    (hlo : Num.fixVal mem lo h L P=(I.edge e).lower)
    (hf : Num.fixVal mem fp h L P=f e)
    (hup : Num.fixVal mem up h L P=(I.edge e).upper)
    (ha : Num.fixVal mem ap h L P=a) :
    |Num.fixVal mem' (v-L) h L P-gradientWithResidual I a r f e| ≤
      (1/(2:ℝ)^q)*lengths I a f e := by
  have hh := Num.IPM.gradient_output I f e (F:=I.cost f-r) hout hc
    (by simpa only [sub_sub_cancel] using hr) hlo hf hup ha
  rw [gradient_at_stored_residual] at hh
  exact hh

/-- The full numerical refresh has the stored-residual gradient
accuracy required by the computed epoch-tolerance theorem. -/
theorem computed_gradientArray_output (I : Instance) (f : Fin I.m → ℝ)
    {w h q K cp rp lo fp up ap one L P E heap v : ℕ} {mem mem' : ℕ → ℕ} {a r : ℝ}
    (hpre : (Num.IPM.gradientArrayContract w h q K).pre
      [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem)
    (hout : (Num.IPM.gradientArrayContract w h q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem v mem')
    (hc : ∀ e : Fin I.m,Num.intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hr : Num.fixVal mem rp h L P=r)
    (hlo : ∀ e : Fin I.m,Num.fixVal mem (lo+e.val*L) h L P=(I.edge e).lower)
    (hf : ∀ e : Fin I.m,Num.fixVal mem (fp+e.val*L) h L P=f e)
    (hup : ∀ e : Fin I.m,Num.fixVal mem (up+e.val*L) h L P=(I.edge e).upper)
    (ha : Num.fixVal mem ap h L P=a) :
    GradientTolerance (lengths I a f)
      (fun e : Fin I.m => Num.fixVal mem' (heap+e.val*L) h L P)
      (gradientWithResidual I a r f) (1/(2:ℝ)^q) := by
  have hh := Num.IPM.gradientArray_output I f (F:=I.cost f-r) hpre hout hc
    (by simpa only [sub_sub_cancel] using hr) hlo hf hup ha
  rw [gradient_at_stored_residual] at hh
  exact hh

end MinCostFlow.IPM.Machine
