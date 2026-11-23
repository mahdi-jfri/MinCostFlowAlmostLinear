module

public import MinCostFlow.LSF.Program.TreeArrays
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Subtree sums along a top-down order

We want, for every vertex index `y`, the sum of a value `D₀ z` over all descendants `z` of `y`
(the `z` with `AncOf par dep y z`). The program walks a top-down order `Q` of the vertices (each
vertex comes after its parent; this is the search order of `rootTreeProc`) from the back, and for
each `x = Q[k]` with `k ≥ 1` adds the current value at `x` to the value at its parent.

To describe the state in the middle, call `z` *collected* at `y` after stage `k` when `y` is an
ancestor of `z` and every vertex on the way from `z` up to `y`, except `y` itself, sits at a
position at least `k` in `Q` (`Collected`). After the positions `k, …, n - 1` are processed, the
value at `y` is the sum of `D₀ z` over the `z` collected at `y` (`stageSum`).

* `stageSum_last`: before any step, only `y` itself is collected at `y`.
* `stageSum_step`: processing `x = Q[k]` adds the sum at `x` to the sum at its parent, which is
  what the program does.
* `stageSum_one`: after all steps, every descendant is collected, because the only vertex at
  position `0` is the root, and the root is never strictly between a vertex and its ancestor.
-/

namespace MinCostFlow.LSF.Program

@[expose] public section

variable {n tM r : ℕ} {tl hd par pe dep : ℕ → ℕ} {Q : List ℕ}

/-- The top-down order `Q` of the vertex indices `0, …, n - 1`: each vertex other than the root
comes after its parent. -/
structure TopDownOrder (n r : ℕ) (par : ℕ → ℕ) (Q : List ℕ) : Prop where
  len : Q.length = n
  nodup : Q.Nodup
  cover : ∀ x < n, x ∈ Q
  lt : ∀ x ∈ Q, x < n
  after : ∀ j (hj : j < Q.length), Q[j] ≠ r → par Q[j] ∈ Q.take j

/-- `z` is collected at `y` after stage `k`. -/
def Collected (par dep : ℕ → ℕ) (Q : List ℕ) (k y z : ℕ) : Prop :=
  AncOf par dep y z ∧ ∀ i < dep z - dep y, par^[i] z ∉ Q.take k

open Classical in
/-- The sum of `D₀` over the vertices collected at `y` after stage `k`. -/
noncomputable def stageSum (par dep : ℕ → ℕ) (Q : List ℕ) (n : ℕ) (D₀ : ℕ → ℤ) (k y : ℕ) : ℤ :=
  ∑ z ∈ Finset.range n, if Collected par dep Q k y z then D₀ z else 0

/-- A top-down order only depends on the parents of the indices below `n`. -/
lemma TopDownOrder.congr {par' : ℕ → ℕ} (hQ : TopDownOrder n r par Q)
    (hpar : ∀ x < n, par x = par' x) : TopDownOrder n r par' Q :=
  ⟨hQ.len, hQ.nodup, hQ.cover, hQ.lt, fun j hj hne => by
    rw [← hpar _ (hQ.lt _ (List.getElem_mem hj))]; exact hQ.after j hj hne⟩

lemma TopDownOrder.head_eq (hQ : TopDownOrder n r par Q) (hn : 0 < n) :
    Q[0]'(by rw [hQ.len]; exact hn) = r := by
  by_contra hne
  have := hQ.after 0 (by rw [hQ.len]; exact hn) hne
  simp at this

lemma TopDownOrder.not_mem_take (hQ : TopDownOrder n r par Q) {k : ℕ} (hk : k < Q.length) :
    Q[k] ∉ Q.take k := by
  intro hmem
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hmem
  rw [List.length_take] at hi
  rw [List.getElem_take] at hik
  have := (hQ.nodup.getElem_inj_iff (hi := by omega) (hj := hk)).mp hik
  omega

/-- Before any step only `y` is collected at `y`. -/
lemma stageSum_last (hR : RootedArrays n tM r tl hd par pe dep) (hQ : TopDownOrder n r par Q)
    (D₀ : ℕ → ℤ) {y : ℕ} (hy : y < n) : stageSum par dep Q n D₀ n y = D₀ y := by
  classical
  unfold stageSum
  have hiff : ∀ z ∈ Finset.range n, Collected par dep Q n y z ↔ z = y := by
    intro z hz
    rw [Finset.mem_range] at hz
    constructor
    · rintro ⟨hanc, hall⟩
      by_contra hne
      have hdz : dep y < dep z := by
        have hle := hanc.dep_le hR hz
        rcases Nat.lt_or_ge (dep y) (dep z) with h | h
        · exact h
        · exact absurd (hanc.eq_of_dep_eq hR hz (AncOf.refl par dep z) (by omega)) (Ne.symm hne)
      have := hall 0 (by omega)
      rw [Function.iterate_zero_apply, List.take_of_length_le (by rw [hQ.len])] at this
      exact this (hQ.cover z hz)
    · rintro rfl
      exact ⟨AncOf.refl par dep z, fun i hi => by omega⟩
  rw [Finset.sum_congr rfl (fun z hz => if_congr (hiff z hz) rfl rfl)]
  rw [Finset.sum_ite_eq' (Finset.range n) y D₀, if_pos (Finset.mem_range.mpr hy)]

/-- After all steps every descendant of `y` is collected at `y`. -/
lemma stageSum_one (hR : RootedArrays n tM r tl hd par pe dep) (hQ : TopDownOrder n r par Q)
    (hn : 0 < n) (D₀ : ℕ → ℤ) (y : ℕ) :
    stageSum par dep Q n D₀ 1 y =
      open Classical in ∑ z ∈ Finset.range n, if AncOf par dep y z then D₀ z else 0 := by
  classical
  unfold stageSum
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [Finset.mem_range] at hz
  refine if_congr ⟨fun h => h.1, fun hanc => ⟨hanc, fun i hi hmem => ?_⟩⟩ rfl rfl
  have htake : Q.take 1 = [Q[0]'(by rw [hQ.len]; exact hn)] := by
    rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [hQ.len]; exact hn)]
    rfl
  rw [htake, hQ.head_eq hn, List.mem_singleton] at hmem
  have h1 := hR.dep_iterate hz i
  rw [hmem, hR.dep_r] at h1
  have := hanc.dep_le hR hz
  omega

/-- The pointwise form of `stageSum_step`. -/
private lemma collected_step (hR : RootedArrays n tM r tl hd par pe dep)
    (hQ : TopDownOrder n r par Q) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < Q.length) {y z : ℕ}
    (hz : z < n) :
    (Collected par dep Q k y z ↔
      Collected par dep Q (k + 1) y z ∨ (y = par Q[k] ∧ Collected par dep Q (k + 1) Q[k] z)) ∧
    ¬ (Collected par dep Q (k + 1) y z ∧ y = par Q[k] ∧
      Collected par dep Q (k + 1) Q[k] z) := by
  set x := Q[k] with hx
  have hn : 0 < n := by rw [← hQ.len]; omega
  have hxn : x < n := hQ.lt x (List.getElem_mem _)
  have hxr : x ≠ r := by
    intro h
    have h0 := hQ.head_eq hn
    rw [← h0, hx] at h
    have := (hQ.nodup.getElem_inj_iff).mp h
    omega
  have hpx : par x ∈ Q.take k := hQ.after k hk hxr
  have hxk : x ∉ Q.take k := hQ.not_mem_take hk
  have htake : ∀ v, v ∈ Q.take (k + 1) ↔ v ∈ Q.take k ∨ v = x := by
    intro v
    rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.mem_append,
      List.mem_singleton]
  have hdx : dep x = dep (par x) + 1 := (hR.step x hxn hxr).2.2
  -- `x` itself is never strictly between `z` and `par x`'s chain below `x`
  have hiter_x : ∀ i, par^[i] z = x → AncOf par dep x z ∧ i = dep z - dep x := by
    intro i hi
    have hanc : AncOf par dep x z := hi ▸ ancOf_iterate hR hz i
    refine ⟨hanc, ?_⟩
    have h1 := hR.dep_iterate hz i
    rw [hi] at h1
    by_cases hle : i ≤ dep z
    · omega
    · -- past the root the iterate is the root, which is not `x`
      exact (hxr (hi ▸ hR.iterate_dep hz (by omega : dep z ≤ i))).elim
  refine ⟨⟨fun ⟨hanc, hall⟩ => ?_, fun h => ?_⟩, fun ⟨⟨hanc, hall⟩, hyp, ⟨hanc', hall'⟩⟩ => ?_⟩
  · -- a collected `z` after stage `k`
    by_cases hpass : ∃ i < dep z - dep y, par^[i] z = x
    · obtain ⟨i, hi, hix⟩ := hpass
      obtain ⟨hax, hieq⟩ := hiter_x i hix
      have hpar : par^[i + 1] z = par x := by
        rw [Function.iterate_succ_apply', hix]
      have hJ : i + 1 = dep z - dep y := by
        by_contra hne
        exact hall (i + 1) (by omega) (hpar ▸ hpx)
      have hyz : y = par^[dep z - dep y] z := hanc.eq_iterate hR hz
      refine Or.inr ⟨by rw [hyz, ← hJ, hpar], hax, fun i' hi' hmem => ?_⟩
      rcases (htake _).mp hmem with hmem | hmem
      · exact hall i' (by omega) hmem
      · have := (hiter_x i' hmem).2
        omega
    · push Not at hpass
      refine Or.inl ⟨hanc, fun i hi hmem => ?_⟩
      rcases (htake _).mp hmem with hmem | hmem
      · exact hall i hi hmem
      · exact hpass i hi hmem
  · rcases h with ⟨hanc, hall⟩ | ⟨hyp, hanc, hall⟩
    · exact ⟨hanc, fun i hi hmem => hall i hi ((htake _).mpr (Or.inl hmem))⟩
    · -- `z` collected at `x` after stage `k + 1` is collected at `par x` after stage `k`
      subst hyp
      have hpa : AncOf par dep (par x) x := by
        simpa using ancOf_iterate hR hxn 1
      have hxz := hanc.dep_le hR hz
      refine ⟨hpa.trans hR hz hanc, fun i hi hmem => ?_⟩
      by_cases hlt : i < dep z - dep x
      · exact hall i hlt ((htake _).mpr (Or.inl hmem))
      · have hieq : i = dep z - dep x := by omega
        have hxi : par^[i] z = x := by rw [hieq]; exact (hanc.eq_iterate hR hz).symm
        exact hxk (hxi ▸ hmem)
  · -- the two parts are disjoint: the chain from `z` to `par x` passes through `x`
    subst hyp
    have hxz := hanc'.dep_le hR hz
    have hxi : par^[dep z - dep x] z = x := (hanc'.eq_iterate hR hz).symm
    exact hall (dep z - dep x) (by omega) ((htake _).mpr (Or.inr hxi))

/-- Processing `x = Q[k]` adds the sum at `x` to the sum at its parent. -/
lemma stageSum_step (hR : RootedArrays n tM r tl hd par pe dep) (hQ : TopDownOrder n r par Q)
    (D₀ : ℕ → ℤ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < Q.length) (y : ℕ) :
    stageSum par dep Q n D₀ k y =
      stageSum par dep Q n D₀ (k + 1) y +
        if y = par Q[k] then stageSum par dep Q n D₀ (k + 1) Q[k] else 0 := by
  classical
  unfold stageSum
  split_ifs with hyp
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [Finset.mem_range] at hz
    obtain ⟨hiff, hdisj⟩ := collected_step hR hQ hk1 hk (y := y) hz
    by_cases h1 : Collected par dep Q (k + 1) y z
    · have h2 : ¬ Collected par dep Q (k + 1) Q[k] z := fun h2 => hdisj ⟨h1, hyp, h2⟩
      rw [if_pos (hiff.mpr (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : Collected par dep Q (k + 1) Q[k] z
      · rw [if_pos (hiff.mpr (Or.inr ⟨hyp, h2⟩)), if_neg h1, if_pos h2, zero_add]
      · have h3 : ¬ Collected par dep Q k y z := fun h3 => by
          rcases hiff.mp h3 with h | ⟨-, h⟩
          · exact h1 h
          · exact h2 h
        rw [if_neg h3, if_neg h1, if_neg h2, add_zero]
  · rw [add_zero]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [Finset.mem_range] at hz
    obtain ⟨hiff, -⟩ := collected_step hR hQ hk1 hk (y := y) hz
    refine if_congr ⟨fun h => ?_, fun h => hiff.mpr (Or.inl h)⟩ rfl rfl
    rcases hiff.mp h with h | ⟨h, -⟩
    · exact h
    · exact absurd h hyp

end

end MinCostFlow.LSF.Program
