module

public import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Exact numerators for cost-flow dot products

Integer costs multiply fixed-point flow numerators without changing their
scale. A left-to-right scan of consecutive limb blocks therefore computes
the exact dot product. The lemmas below describe the empty scan, one scan
step, heap framing, and conversion back to real numbers.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM

/-- The first `n` integer-cost times flow-numerator products. -/
def dotNumerator (mem : ℕ→ℕ) (c f h L n : ℕ) : ℤ :=
  ∑ i∈Finset.range n,intVal mem (c+i*L) h L*intVal mem (f+i*L) h L

/-- An empty dot product has zero numerator. -/
theorem dotNumerator_zero (mem : ℕ→ℕ) (c f h L : ℕ) : dotNumerator mem c f h L 0=0 := by
  simp [dotNumerator]

/-- Scanning the first edge leaves the same problem on the next blocks. -/
theorem dotNumerator_succ (mem : ℕ→ℕ) (c f h L n : ℕ) :
    dotNumerator mem c f h L (n+1)=intVal mem c h L*intVal mem f h L+
      dotNumerator mem (c+L) (f+L) h L n := by
  simp only [dotNumerator,Finset.sum_range_succ',zero_mul,add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hc : c+(i+1)*L=(c+L)+i*L := by ring
  have hf : f+(i+1)*L=(f+L)+i*L := by ring
  rw [hc,hf]

/-- Preserving an array's memory prefix preserves its dot-product numerator. -/
theorem dotNumerator_frozen {mem mem' : ℕ→ℕ} {c f h L n heap : ℕ}
    (hfrozen : ∀z<heap,mem' z=mem z) (hc : c+n*L≤heap) (hf : f+n*L≤heap) :
    dotNumerator mem' c f h L n=dotNumerator mem c f h L n := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i<n := Finset.mem_range.mp hi
  have hib : i*L+L≤n*L := by
    have ht := Nat.mul_le_mul_right L (show i+1≤n by omega)
    simpa only [Nat.add_mul,one_mul] using ht
  rw [value_frozen (h:=h) hfrozen (show c+i*L+L≤heap by omega),
      value_frozen (h:=h) hfrozen (show f+i*L+L≤heap by omega)]

/-- The exact numerator decodes as the real integer-cost dot product. -/
theorem dotNumerator_scaled (mem : ℕ→ℕ) (c f h L n P : ℕ) :
    (dotNumerator mem c f h L n:ℝ)/(2:ℝ)^P=
      ∑ i∈Finset.range n,(intVal mem (c+i*L) h L:ℝ)*fixVal mem (f+i*L) h L P := by
  simp only [dotNumerator,Int.cast_sum,Int.cast_mul,Finset.sum_div,fixVal,mul_div_assoc]

end MinCostFlow.Num.IPM
