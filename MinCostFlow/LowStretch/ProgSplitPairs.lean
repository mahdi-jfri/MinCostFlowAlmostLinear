module

public import MinCostFlow.LowStretch.ProgSplitGrp
public import MinCostFlow.LowStretch.ProgCSR

/-!
# The pairs grouped at the split nodes

When the offsets and the items at `GOFF` and `GPR` group the pairs by their lowest common node
`lf p` (as `csrB` leaves them, see `GlobL.Ok`), the items that `grpCopyP` copies for the key `u`
are the pairs with `lf p = u` (`GCE.blk_eq`). So for distinct keys the copied list holds each
pair whose lowest common node is a key, once (`GCE.mem_seq`, `GCE.seq_nodup`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace GCE

variable {E : GCE} {lf : ℕ → ℕ} {m N : ℕ}

/-- The pairs of key `u` in the grouped order. -/
theorem mem_grp {u p : ℕ} : p ∈ grp lf m u ↔ p < m ∧ lf p = u := by
  simp [grp]

/-- The items copied for a key are the pairs grouped at it. -/
theorem blk_eq (hoff : ∀ u ≤ N, E.mem0 (E.GOFF + u) = offOf lf m u)
    (hgpr : ∀ u < N, ∀ j < (grp lf m u).length,
      E.mem0 (E.GPR + offOf lf m u + j) = (grp lf m u).getD j 0)
    {i : ℕ} (hk : E.key i < N) : E.blk i = grp lf m (E.key i) := by
  have hlo : E.lo i = offOf lf m (E.key i) := hoff _ (by omega)
  have hhi : E.hi i = offOf lf m (E.key i) + (grp lf m (E.key i)).length := by
    unfold hi
    rw [Nat.add_assoc, hoff (E.key i + 1) (by omega), offOf_succ]
  unfold blk
  rw [hhi, hlo, Nat.add_sub_cancel_left, List.range'_eq_map_range, List.map_map]
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [← Nat.add_assoc, hgpr _ hk j (by simpa using h1), List.getD_eq_getElem _ _ h2]

/-- **The copied pairs** are the pairs whose lowest common node is a key. -/
theorem mem_seq (hoff : ∀ u ≤ N, E.mem0 (E.GOFF + u) = offOf lf m u)
    (hgpr : ∀ u < N, ∀ j < (grp lf m u).length,
      E.mem0 (E.GPR + offOf lf m u + j) = (grp lf m u).getD j 0)
    (hk : ∀ i < E.nsp, E.key i < N) {p : ℕ} :
    p ∈ E.seq ↔ p < m ∧ ∃ i < E.nsp, lf p = E.key i := by
  unfold seq
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [blk_eq hoff hgpr (hk i hi), mem_grp] at hp
    exact ⟨hp.1, i, hi, hp.2⟩
  · rintro ⟨hp, i, hi, he⟩
    exact ⟨i, hi, by rw [blk_eq hoff hgpr (hk i hi), mem_grp]; exact ⟨hp, he⟩⟩

/-- For distinct keys, each copied pair is copied once. -/
theorem seq_nodup (hoff : ∀ u ≤ N, E.mem0 (E.GOFF + u) = offOf lf m u)
    (hgpr : ∀ u < N, ∀ j < (grp lf m u).length,
      E.mem0 (E.GPR + offOf lf m u + j) = (grp lf m u).getD j 0)
    (hk : ∀ i < E.nsp, E.key i < N)
    (hnd : ∀ i < E.nsp, ∀ j < E.nsp, E.key i = E.key j → i = j) : E.seq.Nodup := by
  unfold seq
  refine List.nodup_flatMap.mpr ⟨fun i hi => ?_, ?_⟩
  · rw [blk_eq hoff hgpr (hk i (List.mem_range.mp hi))]
    exact (List.nodup_range).filter _
  · refine (List.nodup_range).pairwise_of_forall_ne fun i hi j hj hij => ?_
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    rw [Function.onFun, blk_eq hoff hgpr (hk i hi'), blk_eq hoff hgpr (hk j hj')]
    refine List.disjoint_left.mpr fun p h1 h2 => hij (hnd i hi' j hj' ?_)
    rw [mem_grp] at h1 h2
    rw [← h1.2, h2.2]

end GCE

end MinCostFlow.LowStretch
