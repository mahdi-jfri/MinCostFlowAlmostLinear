module

public import MinCostFlow.LSF.Program.DecompDeg
public import MinCostFlow.LSF.Program.DecompGenSpec

/-!
# The counts of the degree pass are the vertex weights

For unit weights `vWeight G₀ 1 v` counts the edge ends at `v`. When the endpoint indices `eu`,
`ev` describe the edge list of `G₀` (as `endpointIdx_spec` gives), the count of
`decompDegProc` at the index of `v` is this number (`degCount_eq_vWeight`). With the integer
threshold `decompThetaNat` the written weight is `decompNu` (`degNu_eq_decompNu`).
-/

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program.DecompGen

@[expose] public section

/-- The threshold `θ = 4 k (hldDepthBound n + 1)` of the decomposition, as an integer. -/
def decompThetaNat (G₀ : MGraph) (k : ℕ) : ℕ := 4 * k * (hldDepthBound G₀.n + 1)

lemma decompTheta_eq {G₀ : MGraph} (hE : G₀.E.Nonempty) (k : ℕ) :
    decompTheta G₀ (fun _ => 1) (decompParam G₀ (k : ℝ)) = (decompThetaNat G₀ k : ℝ) := by
  have hm : (G₀.E.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hE).ne'
  unfold decompTheta decompParam decompThetaNat
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  push_cast
  field_simp

theorem degCount_eq_vWeight {G₀ : MGraph} {eList vList : List ℕ} {eu ev : ℕ → ℕ}
    (hnd : eList.Nodup) (hE : ∀ e, e ∈ eList ↔ e ∈ G₀.E) (hvnd : vList.Nodup)
    (hu : ∀ t < eList.length, eu t < vList.length ∧ vList.getD (eu t) 0 = G₀.tail (eList.getD t 0))
    (hv : ∀ t < eList.length, ev t < vList.length ∧ vList.getD (ev t) 0 = G₀.head (eList.getD t 0))
    {x : ℕ} (hx : x < vList.length) :
    (degCount eu ev eList.length x : ℝ) = vWeight G₀ (fun _ => 1) (vList.getD x 0) := by
  classical
  set g : ℕ → ℕ := fun t => eList.getD t 0 with hg
  have himg : G₀.E = (Finset.range eList.length).image g := by
    ext e
    rw [← hE, Finset.mem_image]
    constructor
    · intro he
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
      exact ⟨t, Finset.mem_range.mpr ht, by simp only [hg]; rw [List.getD_eq_getElem _ _ ht]⟩
    · rintro ⟨t, ht, rfl⟩
      have ht' := Finset.mem_range.mp ht
      simp only [hg, List.getD_eq_getElem _ _ ht']
      exact List.getElem_mem ht'
  have hinj : Set.InjOn g (Finset.range eList.length) := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    simp only [hg, List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at hab
    exact (hnd.getElem_inj_iff).mp hab
  unfold vWeight
  rw [himg, Finset.sum_image hinj]
  unfold degCount
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have ht' := Finset.mem_range.mp ht
  obtain ⟨hu1, hu2⟩ := hu t ht'
  obtain ⟨hv1, hv2⟩ := hv t ht'
  have h1 : (eu t = x) ↔ (G₀.tail (g t) = vList.getD x 0) := by
    rw [show G₀.tail (g t) = vList.getD (eu t) 0 from hu2.symm]
    exact ⟨fun h => by rw [h], fun h => getD_inj hvnd hu1 hx h⟩
  have h2 : (ev t = x) ↔ (G₀.head (g t) = vList.getD x 0) := by
    rw [show G₀.head (g t) = vList.getD (ev t) 0 from hv2.symm]
    exact ⟨fun h => by rw [h], fun h => getD_inj hvnd hv1 hx h⟩
  simp only [← h1, ← h2]

theorem degNu_eq_decompNu {G₀ : MGraph} (hE : G₀.E.Nonempty) (k : ℕ) {v : ℕ} (hv : v ∈ G₀.V)
    {d : ℕ} (hd : (d : ℝ) = vWeight G₀ (fun _ => 1) v) :
    (degNu (decompThetaNat G₀ k) d : ℝ) = decompNu G₀ (fun _ => 1) (decompParam G₀ (k : ℝ)) v := by
  classical
  unfold decompNu decompHeavy degNu
  rw [decompTheta_eq hE]
  simp only [Finset.mem_filter, hv, true_and, ← hd, Nat.cast_lt]
  split_ifs <;> simp

end

end MinCostFlow.LSF.Program
