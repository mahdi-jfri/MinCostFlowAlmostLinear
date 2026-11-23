module

public import MinCostFlow.LSF.Program.T0Index
public import MinCostFlow.LSF.Program.InitTreeLSSTLift
public import MinCostFlow.LSF.Program.InitTreeCopies

/-!
# What the copy arrays hold

`initTreeCopiesProc` writes the copies of the edges of `G₀` one edge after another: copy `k` of
the `j`-th edge of `eList` sits at position `q = mult 0 + … + mult (j - 1) + k`. This is the
order of `copyList`, so these arrays are the graph `copyIndexedGraph` that the `[AN19]` call gets.

* `copyArraysAt_of_copies`: the arrays hold the edge and the end indices of each copy
  (`CopyArraysAt`), the form that `t0IndexArrays_of_lift` uses.
* `copyTails_listAt`, `copyHeads_listAt`: the end arrays are the lists of tails and heads of
  `copyIndexedGraph`, as the `[AN19]` call asks.
* `copyLens_spec`, `copyWts_spec`: the length blocks hold the length of the original edge, and
  the weight blocks hold `1` (the real value `2 ^ (-P)`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.WideWord

@[expose] public section

variable {G₀ : MGraph} {vList eList : List ℕ} {mult : ℕ → ℕ}

/-- The facts of `initTreeCopiesContract` about the end and edge arrays, per copy. -/
def CopiesWritten (mem' : ℕ → ℕ) (copyTailPtr copyHeadPtr copyOrigIdxPtr m0 : ℕ)
    (G₀ : MGraph) (vList eList : List ℕ) (mult : ℕ → ℕ) : Prop :=
  ∀ j < m0, ∀ k < mult j,
    mem' (copyTailPtr + (((List.range j).map mult).sum + k)) < G₀.n ∧
    vList[mem' (copyTailPtr + (((List.range j).map mult).sum + k))]? =
      some (G₀.tail (eList.getD j 0)) ∧
    mem' (copyHeadPtr + (((List.range j).map mult).sum + k)) < G₀.n ∧
    vList[mem' (copyHeadPtr + (((List.range j).map mult).sum + k))]? =
      some (G₀.head (eList.getD j 0)) ∧
    mem' (copyOrigIdxPtr + (((List.range j).map mult).sum + k)) = eList.getD j 0

/-- Position `q` of the copy list is copy `k` of edge `j`. -/
lemma copyList_getD_coords {m0 q : ℕ} (hq : q < (copyList eList mult m0).length) :
    ∃ j < m0, ∃ k < mult j, q = ((List.range j).map mult).sum + k ∧
      (copyList eList mult m0).getD q (0, 0) = (eList.getD j 0, k) := by
  obtain ⟨j, hj, k, hk, hqe, hget⟩ := exists_coords_of_lt_copyList eList mult hq
  exact ⟨j, hj, k, hk, hqe, by rw [List.getD_eq_getElem _ _ hq, hget]⟩

lemma getD_of_getElem?_eq {l : List ℕ} {i x : ℕ} (h : l[i]? = some x) : l.getD i 0 = x := by
  rw [List.getD_eq_getElem?_getD, h, Option.getD_some]

lemma lt_of_getElem?_eq {l : List ℕ} {i x : ℕ} (h : l[i]? = some x) : i < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem copyArraysAt_of_copies {mem' : ℕ → ℕ} {copyTailPtr copyHeadPtr copyOrigIdxPtr : ℕ}
    (hC : CopiesWritten mem' copyTailPtr copyHeadPtr copyOrigIdxPtr G₀.E.card G₀ vList eList
      mult) :
    CopyArraysAt mem' copyTailPtr copyHeadPtr copyOrigIdxPtr G₀ vList
      (copyList eList mult G₀.E.card) := by
  intro q hq
  obtain ⟨j, hj, k, hk, rfl, hget⟩ := copyList_getD_coords hq
  obtain ⟨-, ht, -, hh, ho⟩ := hC j hj k hk
  rw [hget]
  exact ⟨ho, lt_of_getElem?_eq ht, getD_of_getElem?_eq ht, lt_of_getElem?_eq hh,
    getD_of_getElem?_eq hh⟩

lemma idxOf_eq_of_getElem? {l : List ℕ} (hnd : l.Nodup) {i x : ℕ} (h : l[i]? = some x) :
    l.idxOf x = i := by
  have hi := lt_of_getElem?_eq h
  rw [List.getElem?_eq_getElem hi, Option.some_inj] at h
  rw [← h]
  exact idxOf_getElem_of_nodup hnd hi

theorem copyTails_listAt {mem' : ℕ → ℕ} {copyTailPtr copyHeadPtr copyOrigIdxPtr : ℕ}
    (hnd : vList.Nodup)
    (hC : CopiesWritten mem' copyTailPtr copyHeadPtr copyOrigIdxPtr G₀.E.card G₀ vList eList
      mult) :
    ListAt mem' copyTailPtr
      (List.ofFn fun i : Fin (copyIndexedGraph G₀ vList eList mult).m =>
        (copyIndexedGraph G₀ vList eList mult).tail i.1) := by
  intro q hq
  rw [List.length_ofFn] at hq
  rw [List.getElem_ofFn]
  obtain ⟨j, hj, k, hk, rfl, hget⟩ := copyList_getD_coords hq
  dsimp only [copyIndexedGraph]
  rw [hget]
  exact (idxOf_eq_of_getElem? hnd (hC j hj k hk).2.1).symm

theorem copyHeads_listAt {mem' : ℕ → ℕ} {copyTailPtr copyHeadPtr copyOrigIdxPtr : ℕ}
    (hnd : vList.Nodup)
    (hC : CopiesWritten mem' copyTailPtr copyHeadPtr copyOrigIdxPtr G₀.E.card G₀ vList eList
      mult) :
    ListAt mem' copyHeadPtr
      (List.ofFn fun i : Fin (copyIndexedGraph G₀ vList eList mult).m =>
        (copyIndexedGraph G₀ vList eList mult).head i.1) := by
  intro q hq
  rw [List.length_ofFn] at hq
  rw [List.getElem_ofFn]
  obtain ⟨j, hj, k, hk, rfl, hget⟩ := copyList_getD_coords hq
  dsimp only [copyIndexedGraph]
  rw [hget]
  exact (idxOf_eq_of_getElem? hnd (hC j hj k hk).2.2.2.1).symm

/-- The length block of each copy holds the length of its edge. -/
theorem copyLens_spec {mem mem' : ℕ → ℕ} {ℓ₀ : ℕ → ℝ} {lenArr copyLenPtr h L_in P_fp : ℕ}
    (heMem : ∀ e, e ∈ eList ↔ e ∈ G₀.E) (heLen : eList.length = G₀.E.card)
    (hlen : ∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧
      Num.fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hC : ∀ j < G₀.E.card, ∀ k < mult j, ∀ i < L_in,
      mem' (copyLenPtr + (((List.range j).map mult).sum + k) * L_in + i) =
        mem (lenArr + eList.getD j 0 * L_in + i)) :
    ∀ q < (copyIndexedGraph G₀ vList eList mult).m,
      Num.Valid mem' (copyLenPtr + q * L_in) h L_in ∧
      Num.fixVal mem' (copyLenPtr + q * L_in) h L_in P_fp =
        ℓ₀ ((copyList eList mult G₀.E.card).getD q (0, 0)).1 ∧
      0 < ℓ₀ ((copyList eList mult G₀.E.card).getD q (0, 0)).1 := by
  intro q hq
  obtain ⟨j, hj, k, hk, rfl, hget⟩ := copyList_getD_coords hq
  rw [hget]
  have he : eList.getD j 0 ∈ G₀.E := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact (heMem _).mp (List.getElem_mem _)
  obtain ⟨hv, hf, hpos⟩ := hlen _ he
  have heq : ∀ i < L_in, mem' (copyLenPtr + (((List.range j).map mult).sum + k) * L_in + i) =
      mem (lenArr + eList.getD j 0 * L_in + i) := hC j hj k hk
  refine ⟨fun i hi => by rw [heq i hi]; exact hv i hi, ?_, hpos⟩
  rw [← hf]
  unfold Num.fixVal
  rw [Num.intVal_congr heq]

/-- The weight block of each copy holds `1`, so its real value is `2 ^ (-P)`. -/
theorem copyWts_spec {mem mem' : ℕ → ℕ} {copyWtPtr h L_in P_fp : ℕ} (hh : 1 ≤ h)
    (hhL : 2 ≤ h * L_in)
    (hC : ∀ j < G₀.E.card, ∀ k < mult j,
      mem' (copyWtPtr + (((List.range j).map mult).sum + k) * L_in) = 1 ∧
      ∀ i, 0 < i → i < L_in →
        mem' (copyWtPtr + (((List.range j).map mult).sum + k) * L_in + i) =
          mem (copyWtPtr + (((List.range j).map mult).sum + k) * L_in + i))
    (hz : ∀ q < (copyIndexedGraph G₀ vList eList mult).m, ∀ i, 0 < i → i < L_in →
      mem (copyWtPtr + q * L_in + i) = 0) :
    ∀ q < (copyIndexedGraph G₀ vList eList mult).m,
      Num.Valid mem' (copyWtPtr + q * L_in) h L_in ∧
      Num.fixVal mem' (copyWtPtr + q * L_in) h L_in P_fp = (2 : ℝ)⁻¹ ^ P_fp ∧
      0 < (2 : ℝ)⁻¹ ^ P_fp := by
  intro q hq
  obtain ⟨j, hj, k, hk, hqe, -⟩ := copyList_getD_coords hq
  obtain ⟨h0, hrest⟩ := hC j hj k hk
  rw [← hqe] at h0 hrest
  have hL1 : 1 ≤ L_in := by
    rcases Nat.eq_zero_or_pos L_in with h0' | h0'
    · rw [h0'] at hhL; omega
    · exact h0'
  have hcell : ∀ i < L_in, mem' (copyWtPtr + q * L_in + i) = if i = 0 then 1 else 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using h0
    · rw [hrest i hi0 hi, hz q hq i hi0 hi, if_neg (by omega)]
  have hbase : 1 < Num.base h := by
    unfold Num.base
    exact Nat.one_lt_two_pow (by omega)
  refine ⟨fun i hi => by rw [hcell i hi]; split_ifs <;> omega, ?_, by positivity⟩
  -- the block reads `1`
  have hu : Num.unsignedVal mem' (copyWtPtr + q * L_in) h L_in = 1 := by
    obtain ⟨L', rfl⟩ : ∃ L', L_in = L' + 1 := ⟨L_in - 1, by omega⟩
    rw [Num.unsignedVal, Num.unsignedVal_zero (fun i hi => ?_)]
    · simpa using hcell 0 (by omega)
    · rw [show copyWtPtr + q * (L' + 1) + 1 + i = copyWtPtr + q * (L' + 1) + (i + 1) by omega,
        hcell (i + 1) (by omega), if_neg (by omega)]
  have hcap : 2 < Num.capacity h L_in := by
    rw [Num.capacity_eq_two_pow]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (h * L_in) := Nat.pow_le_pow_right (by norm_num) hhL
  unfold Num.fixVal Num.intVal Num.signedVal
  rw [hu, if_neg (by omega)]
  simp [inv_pow]

end

end MinCostFlow.LSF.Program
