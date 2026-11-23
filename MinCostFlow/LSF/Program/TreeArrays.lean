module

public import MinCostFlow.LSF.Program.T0Rooted
public import MinCostFlow.LSF.Program.BinaryLift
import Mathlib.Tactic.Linarith

/-!
# Ancestors in the rooted arrays

The init programs of the LSF work with the rooted arrays `par`, `dep` over vertex indices
(`RootedArrays`), where `t0Rooted_isAncestor_iff` says that the ancestors of `x` in `(T₀, r₀)`
are the iterated parents `par^[k] x` with `k ≤ dep x`. Here we prove the facts about these
iterates that the lowest-common-ancestor search needs:

* `RootedArrays.dep_iterate`: each step up lowers the depth by one, until the root, which is
  its own parent at depth `0`;
* `AncOf` (the ancestor relation of the arrays) is reflexive and transitive, and two ancestors
  of `x` with the same depth are equal (`AncOf.eq_of_dep_eq`);
* `IsLcaOf z x y`: `z` is a common ancestor of `x` and `y`, and every common ancestor is an
  ancestor of `z`.
-/

namespace MinCostFlow.LSF.Program

@[expose] public section

variable {n tM r : ℕ} {tl hd par pe dep : ℕ → ℕ}

lemma RootedArrays.iterate_lt (hR : RootedArrays n tM r tl hd par pe dep) {x : ℕ} (hx : x < n)
    (k : ℕ) : par^[k] x < n := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact hR.par_lt _ ih

lemma RootedArrays.eq_r_of_dep_zero (hR : RootedArrays n tM r tl hd par pe dep) {x : ℕ}
    (hx : x < n) (h0 : dep x = 0) : x = r := by
  by_contra hne
  have := (hR.step x hx hne).2.2
  omega

/-- Each step up lowers the depth by one, until the root. -/
lemma RootedArrays.dep_iterate (hR : RootedArrays n tM r tl hd par pe dep) {x : ℕ} (hx : x < n)
    (k : ℕ) : dep (par^[k] x) = dep x - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hlt := hR.iterate_lt hx k
    by_cases hr' : par^[k] x = r
    · rw [hr', hR.par_r, hR.dep_r]
      rw [hr', hR.dep_r] at ih
      omega
    · have := (hR.step _ hlt hr').2.2
      omega

lemma RootedArrays.iterate_dep (hR : RootedArrays n tM r tl hd par pe dep) {x : ℕ} (hx : x < n)
    {k : ℕ} (hk : dep x ≤ k) : par^[k] x = r := by
  have h := hR.dep_iterate hx k
  have hz : dep (par^[k] x) = 0 := by omega
  exact hR.eq_r_of_dep_zero (hR.iterate_lt hx k) hz

/-- A depth is below `n`: the walk up from `x` visits `dep x + 1` indices, all different (their
depths differ) and all below `n`. -/
lemma RootedArrays.dep_lt (hR : RootedArrays n tM r tl hd par pe dep) {x : ℕ} (hx : x < n) :
    dep x < n := by
  classical
  have hinj : Set.InjOn (fun k => par^[k] x) (Finset.range (dep x + 1) : Set ℕ) := by
    intro k hk k' hk' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    have h1 := hR.dep_iterate hx k
    have h2 := hR.dep_iterate hx k'
    simp only at heq
    rw [heq] at h1
    omega
  have hmaps : Set.MapsTo (fun k => par^[k] x) (Finset.range (dep x + 1) : Set ℕ)
      (Finset.range n : Set ℕ) := fun k _ => by
    simp only [Finset.coe_range, Set.mem_Iio]; exact hR.iterate_lt hx k
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simp only [Finset.card_range] at this
  omega

/-- Different non-root vertices have different parent edges: an edge shared by `x` and `x'`
would make each the parent of the other, one level up from each other. -/
lemma RootedArrays.pe_inj (hR : RootedArrays n tM r tl hd par pe dep) {x x' : ℕ} (hx : x < n)
    (hx' : x' < n) (hxr : x ≠ r) (hx'r : x' ≠ r) (he : pe x = pe x') : x = x' := by
  obtain ⟨-, hj, hdx⟩ := hR.step x hx hxr
  obtain ⟨-, hj', hdx'⟩ := hR.step x' hx' hx'r
  rw [he] at hj
  unfold RTJoin at hj hj'
  by_contra hne
  have h1 : x = par x' ∧ par x = x' := by
    rcases hj with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hj' with ⟨c, d⟩ | ⟨c, d⟩ <;>
      first | (exfalso; apply hne; omega) | (constructor <;> omega)
  rw [← h1.1] at hdx'
  rw [h1.2] at hdx
  omega

/-- `z` is an ancestor of `x` in the arrays (possibly `x` itself). -/
def AncOf (par dep : ℕ → ℕ) (z x : ℕ) : Prop := ∃ k ≤ dep x, par^[k] x = z

lemma AncOf.refl (par dep : ℕ → ℕ) (x : ℕ) : AncOf par dep x x := ⟨0, Nat.zero_le _, rfl⟩

lemma ancOf_iterate (hR : RootedArrays n tM r tl hd par pe dep) {x : ℕ} (hx : x < n) (k : ℕ) :
    AncOf par dep (par^[k] x) x := by
  by_cases hk : k ≤ dep x
  · exact ⟨k, hk, rfl⟩
  · exact ⟨dep x, le_rfl, by rw [hR.iterate_dep hx le_rfl, hR.iterate_dep hx (by omega)]⟩

lemma AncOf.lt (hR : RootedArrays n tM r tl hd par pe dep) {z x : ℕ} (hx : x < n)
    (h : AncOf par dep z x) : z < n := by
  obtain ⟨k, -, rfl⟩ := h; exact hR.iterate_lt hx k

lemma AncOf.dep_le (hR : RootedArrays n tM r tl hd par pe dep) {z x : ℕ} (hx : x < n)
    (h : AncOf par dep z x) : dep z ≤ dep x := by
  obtain ⟨k, -, rfl⟩ := h; rw [hR.dep_iterate hx]; omega

/-- The ancestor of `x` at depth `dep x - k` is `par^[k] x`. -/
lemma AncOf.eq_iterate (hR : RootedArrays n tM r tl hd par pe dep) {z x : ℕ} (hx : x < n)
    (h : AncOf par dep z x) : z = par^[dep x - dep z] x := by
  obtain ⟨k, hk, rfl⟩ := h
  rw [hR.dep_iterate hx]
  congr 1
  omega

/-- Two ancestors of `x` with the same depth are equal. -/
lemma AncOf.eq_of_dep_eq (hR : RootedArrays n tM r tl hd par pe dep) {z z' x : ℕ} (hx : x < n)
    (h : AncOf par dep z x) (h' : AncOf par dep z' x) (hd : dep z = dep z') : z = z' := by
  rw [h.eq_iterate hR hx, h'.eq_iterate hR hx, hd]

lemma AncOf.trans (hR : RootedArrays n tM r tl hd par pe dep) {z y x : ℕ} (hx : x < n)
    (hzy : AncOf par dep z y) (hyx : AncOf par dep y x) : AncOf par dep z x := by
  obtain ⟨a, ha, rfl⟩ := hyx
  obtain ⟨b, hb, rfl⟩ := hzy
  rw [← Function.iterate_add_apply]
  exact ancOf_iterate hR hx _

/-- An ancestor of `x` that is at most as deep as an ancestor `y` of `x` is an ancestor of
`y`. -/
lemma AncOf.of_dep_le (hR : RootedArrays n tM r tl hd par pe dep) {z y x : ℕ} (hx : x < n)
    (hz : AncOf par dep z x) (hy : AncOf par dep y x) (hd : dep z ≤ dep y) :
    AncOf par dep z y := by
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb, rfl⟩ := hy
  rw [hR.dep_iterate hx, hR.dep_iterate hx] at hd
  refine ⟨a - b, by rw [hR.dep_iterate hx]; omega, ?_⟩
  rw [← Function.iterate_add_apply]
  congr 1
  omega

/-- `z` is the lowest common ancestor of `x` and `y`. -/
def IsLcaOf (par dep : ℕ → ℕ) (z x y : ℕ) : Prop :=
  AncOf par dep z x ∧ AncOf par dep z y ∧
    ∀ c, AncOf par dep c x → AncOf par dep c y → AncOf par dep c z

/-! ## Arrays that agree on the vertex indices

The procedures read `par` and `dep` from memory, so their contracts can only pin these functions
on the indices `0, …, n - 1`. The ancestor relation of an index below `n` depends only on these
values, because the iterated parents of such an index stay below `n`. -/

lemma iterate_congr_of_lt {n : ℕ} {par par' : ℕ → ℕ} (hpar : ∀ x < n, par x = par' x)
    (hlt : ∀ x < n, par x < n) {x : ℕ} (hx : x < n) (k : ℕ) : par^[k] x = par'^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hpar x hx]
    exact ih (hlt x hx)

lemma ancOf_congr {n : ℕ} {par par' dep dep' : ℕ → ℕ} (hpar : ∀ x < n, par x = par' x)
    (hdep : ∀ x < n, dep x = dep' x) (hlt : ∀ x < n, par x < n) {z x : ℕ} (hx : x < n) :
    AncOf par dep z x ↔ AncOf par' dep' z x := by
  unfold AncOf
  simp only [iterate_congr_of_lt hpar hlt hx, hdep x hx]

/-- Rooted arrays only depend on their values at the indices below `n`. -/
lemma RootedArrays.congr {par' pe' dep' : ℕ → ℕ} (hR : RootedArrays n tM r tl hd par pe dep)
    (hr : r < n) (hpar : ∀ x < n, par x = par' x) (hpe : ∀ x < n, pe x = pe' x)
    (hdep : ∀ x < n, dep x = dep' x) : RootedArrays n tM r tl hd par' pe' dep' := by
  refine ⟨by rw [← hpar r hr, hR.par_r], by rw [← hdep r hr, hR.dep_r],
    fun x hx => by rw [← hpar x hx]; exact hR.par_lt x hx, fun x hx hxr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hR.step x hx hxr
  have hp := hR.par_lt x hx
  rw [← hpar x hx, ← hpe x hx, ← hdep x hx, ← hdep _ hp]
  exact ⟨h1, h2, h3⟩

lemma isLcaOf_congr {n : ℕ} {par par' dep dep' : ℕ → ℕ} (hpar : ∀ x < n, par x = par' x)
    (hdep : ∀ x < n, dep x = dep' x) (hlt : ∀ x < n, par x < n) {z x y : ℕ} (hx : x < n)
    (hy : y < n) (hz : z < n) :
    IsLcaOf par dep z x y ↔ IsLcaOf par' dep' z x y := by
  unfold IsLcaOf
  simp only [ancOf_congr hpar hdep hlt hx, ancOf_congr hpar hdep hlt hy,
    ancOf_congr hpar hdep hlt hz]

end

end MinCostFlow.LSF.Program
