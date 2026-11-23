module

public import MinCostFlow.IPM.Machine.Layout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Dense scalar tables survive a caller-prefix frame

Each fitting edge block ends within its reserved dense table. Equality
below the incoming heap therefore preserves every block's validity
and the entire zero-extended vector read from that table. These facts
transfer checked coefficient invariants across fresh metadata writes.
-/

public section
namespace MinCostFlow.IPM.Machine

private theorem entry_end {p L e m heap : ℕ} (he : e<m) (hend : p+m*L≤heap) : p+e*L+L≤heap := by
  have hh := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  simp only [Nat.succ_mul] at hh
  omega

/-- A fresh-prefix frame preserves validity of every dense-table block. -/
theorem vector_valid_of_agree_below {mem mem' : ℕ → ℕ} {p h L m heap : ℕ}
    (hframe : ∀ z<heap,mem' z=mem z) (hend : p+m*L≤heap)
    (hvalid : ∀ e<m,Num.Valid mem (p+e*L) h L) :
    ∀ e<m,Num.Valid mem' (p+e*L) h L := by
  intro e he
  exact Num.IPM.valid_frozen hframe (entry_end he hend) (hvalid e he)

/-- Equality on the old caller prefix preserves the exact full vector,
including its zero extension outside the dense table. -/
theorem readVector_eq_of_agree_below {mem mem' : ℕ → ℕ} {p h L P m heap : ℕ}
    (hframe : ∀ z<heap,mem' z=mem z) (hend : p+m*L≤heap) :
    readVector mem' p h L P m=readVector mem p h L P m := by
  funext e
  by_cases he : e<m
  · have hh := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe (entry_end he hend)
    simpa only [readVector,he,↓reduceIte] using hh
  · simp only [readVector,he,↓reduceIte]

end MinCostFlow.IPM.Machine
