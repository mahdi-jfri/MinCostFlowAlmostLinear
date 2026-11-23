module

public import MinCostFlow.LSF.Program.FlagMerge
public import MinCostFlow.Basic.Graph

/-!
# The merged flags are the first root set

`mergedFlag_iff` shows that the flags of `flagMergeProc` mark exactly the vertices of
`C_reps ∪ B ∪ ends of the edges with P`, the form of the first root set in `initLSFWith`. It uses
three facts about the inputs: the boundary flags mark `B`, the representatives are vertices whose
index plus one is in the table `vIdx`, and the high flag of each edge position is `P` of its edge,
with the vertex indices of its ends in `eu`, `ev`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

theorem mergedFlag_iff {mem : ℕ → ℕ} {cnt m0 bndPtr repPtr vIdxPtr highPtr euPtr evPtr : ℕ}
    {vList repList : List ℕ} {G₀ : MGraph} {B : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    {eL : ℕ → ℕ}
    (hnd : vList.Nodup)
    (hbnd : ∀ x < vList.length, mem (bndPtr + x) = 1 ↔ vList.getD x 0 ∈ B)
    (hrep : ListAt mem repPtr repList) (hcnt : repList.length = cnt)
    (hrepV : ∀ v ∈ repList, v ∈ vList)
    (hvIdx : ∀ i (hi : i < vList.length), mem (vIdxPtr + vList[i]) = i + 1)
    (heMem : ∀ e, e ∈ G₀.E ↔ ∃ t < m0, eL t = e)
    (hhigh : ∀ t < m0, mem (highPtr + t) = 1 ↔ P (eL t))
    (heu : ∀ t < m0, mem (euPtr + t) < vList.length ∧
      vList.getD (mem (euPtr + t)) 0 = G₀.tail (eL t))
    (hev : ∀ t < m0, mem (evPtr + t) < vList.length ∧
      vList.getD (mem (evPtr + t)) 0 = G₀.head (eL t)) :
    ∀ x < vList.length, (MergedFlag mem cnt m0 bndPtr repPtr vIdxPtr highPtr euPtr evPtr x ↔
      vList.getD x 0 ∈ repList.toFinset ∪ B ∪
        (G₀.E.filter P).biUnion (fun e => {G₀.tail e, G₀.head e})) := by
  intro x hx
  have hinj : ∀ a < vList.length, ∀ b < vList.length, vList.getD a 0 = vList.getD b 0 → a = b := by
    intro a ha b hb h
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
    exact (hnd.getElem_inj_iff).mp h
  -- the representatives
  have hR : (∃ j < cnt, repIdx mem repPtr vIdxPtr j = x) ↔ vList.getD x 0 ∈ repList := by
    constructor
    · rintro ⟨j, hj, hjx⟩
      have hj' : j < repList.length := by omega
      obtain ⟨i, hi, hvi⟩ := List.getElem_of_mem (hrepV _ (List.getElem_mem hj'))
      have hidx : repIdx mem repPtr vIdxPtr j = i := by
        unfold repIdx
        rw [hrep j hj', ← hvi, hvIdx i hi]
        omega
      rw [← hjx, hidx, List.getD_eq_getElem _ _ hi, hvi]
      exact List.getElem_mem hj'
    · intro hmem
      obtain ⟨j, hj, hvj⟩ := List.getElem_of_mem hmem
      refine ⟨j, by omega, ?_⟩
      unfold repIdx
      rw [hrep j hj, hvj, List.getD_eq_getElem _ _ hx, hvIdx x hx]
      omega
  -- the high edges
  have hE : (∃ t < m0, mem (highPtr + t) = 1 ∧
      (mem (euPtr + t) = x ∨ mem (evPtr + t) = x)) ↔
      vList.getD x 0 ∈ (G₀.E.filter P).biUnion (fun e => {G₀.tail e, G₀.head e}) := by
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨t, ht, hh, hends⟩
      refine ⟨eL t, ⟨(heMem _).mpr ⟨t, ht, rfl⟩, (hhigh t ht).mp hh⟩, ?_⟩
      rcases hends with h | h
      · left; rw [← (heu t ht).2, h]
      · right; rw [← (hev t ht).2, h]
    · rintro ⟨e, ⟨he, hP⟩, hends⟩
      obtain ⟨t, ht, rfl⟩ := (heMem e).mp he
      refine ⟨t, ht, (hhigh t ht).mpr hP, ?_⟩
      rcases hends with h | h
      · left
        exact hinj _ (heu t ht).1 _ hx (by rw [(heu t ht).2, h])
      · right
        exact hinj _ (hev t ht).1 _ hx (by rw [(hev t ht).2, h])
  unfold MergedFlag
  rw [hbnd x hx, hR, hE, Finset.mem_union, Finset.mem_union, List.mem_toFinset]
  tauto

end

end MinCostFlow.LSF.Program
