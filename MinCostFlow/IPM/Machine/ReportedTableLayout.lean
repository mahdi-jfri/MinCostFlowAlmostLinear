module

public import MinCostFlow.IPM.Machine.GuardedCoefficientFrame

/-!
# Dense table separation in the reported-list loop

Each edge occupies one block of the same limb count. Table extents and
separation therefore imply the corresponding conditions for every
selected entry. Distinct names in a Detect answer select disjoint flow
blocks even when the answer order is arbitrary.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- A selected entry ends within its table's full reserved extent. -/
theorem reported_entry_end (base L e m : ℕ) (he : e<m) :
    base+e*L+L≤base+m*L := by
  have hh := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  simp only [Nat.succ_mul] at hh
  omega

/-- Separation of whole tables implies separation of any two entries. -/
theorem reported_entries_separated (base other L e j m : ℕ)
    (he : e<m) (hj : j<m)
    (hdis : base+m*L≤other ∨ other+m*L≤base) :
    base+e*L+L≤other+j*L ∨ other+j*L+L≤base+e*L := by
  have heEnd := reported_entry_end base L e m he
  have hjEnd := reported_entry_end other L j m hj
  rcases hdis with hh | hh
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- A shared scalar disjoint from a flow table is disjoint from its
selected flow entry. -/
theorem reported_scalar_separated (p base L e m : ℕ) (he : e<m)
    (hdis : p+L≤base ∨ base+m*L≤p) :
    p+L≤base+e*L ∨ base+e*L+L≤p := by
  have heEnd := reported_entry_end base L e m he
  rcases hdis with hh | hh
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Every selected pointer and its offset fit when the full table ends
below a word-sized allocation endpoint. -/
theorem reported_entry_words (w base L e m heap : ℕ) (he : e<m)
    (hend : base+m*L≤heap) (hheap : heap<2^w) :
    base+e*L<2^w ∧ e*L<2^w ∧ base+e*L+L≤heap := by
  have heEnd := reported_entry_end base L e m he
  exact ⟨by omega,by omega,heEnd.trans hend⟩

end MinCostFlow.IPM.Machine
