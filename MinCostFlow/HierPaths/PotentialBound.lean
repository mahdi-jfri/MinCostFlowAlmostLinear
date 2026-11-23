module

public import MinCostFlow.HierPaths.PotentialCount
public import MinCostFlow.HierPaths.PotentialVol

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The event count bound and the potential

The amortized bound bounds the total work of any prefix of deletions linearly in the
number of deletions. Here it takes the form of a bound on the event count of
`HierPaths/Potential.lean`: `events_le` shows, for a state with the invariant after `t` deleted
edges,
`E ≤ 12 · (1 + ξ)(L + 2) 4^L (1 + κ)(1 + λ) · t`,
where `L` is the leaf depth, `ξ` bounds the reverse lists, `κ` the connectors of a terminal, and
`λ` the connector walks. Every part of `E` is charged to the directly failed terminals (at most
`ξ t`) and the lost terminals (at most `4^L ξ t`, by `card_globalLost_le`), with the counting facts of
`HierPaths/PotentialCount.lean`.

The potential is `Φ = B_d · t − 2E` with `B_d = 24 · (1 + ξ)(L + 2) 4^L (1 + κ)(1 + λ)`, twice the
coefficient `delCoeff` of `HierPaths/Params.lean` with `κ` in place of `h B` (each terminal has at most `h (B − 1)` connectors).
`potential_amortized`: `2E ≤ B_d t`, so `Φ` is a natural number without truncation, and each
`Delete(e)` of a new edge costs at most `B_d + 2(1 + ξ)` plus the drop of `Φ`.
-/

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

public section

/-- The coefficient `(1 + ξ)(L + 2) 4^L (1 + κ)(1 + λ)` of the event count bound `events_le`, with `L` the leaf depth. -/
@[expose] def delCoef (ξ κ lam : ℕ) : ℕ :=
  (1 + ξ) * (leafDepth A.x A.b + 2) * 4 ^ leafDepth A.x A.b * (1 + κ) * (1 + lam)

theorem delCoef_eq (ξ κ lam : ℕ) : A.delCoef ξ κ lam =
    (1 + ξ) * (leafDepth A.x A.b + 2) * 4 ^ leafDepth A.x A.b * (1 + κ) * (1 + lam) := rfl

/-- The walk of a connector has at most `λ + 1` vertices. -/
theorem verts_length_le (hA : A.Spec G ξ κ) {lam : ℕ}
    (hlam : ∀ c < A.C.numConn, (A.C.walk c).edges.length ≤ lam) {c : ℕ}
    (hc : c < A.C.numConn) : (A.C.walk c).verts.length ≤ lam + 1 := by
  have hw := (hA.fits.2 c hc).2.2
  have hl := hlam c hc
  rcases hw.2.2 with ⟨hv, _⟩ | ⟨_, hlen, _⟩
  · rw [hv]; exact Nat.zero_le _
  · omega

/-- The amortized bound, as a bound on the event count: after `t` deleted edges,
`E ≤ 12 · (1 + ξ)(L + 2) 4^L (1 + κ)(1 + λ) · t`. -/
theorem events_le {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) {lam : ℕ}
    (hlam : ∀ c < A.C.numConn, (A.C.walk c).edges.length ≤ lam) :
    A.events G.n st ≤ 12 * A.delCoef ξ κ lam * st.deleted.card := by
  set L := leafDepth A.x A.b
  set F := st.loss.failed.card
  set g := st.loss.glob.card
  set I := st.inelig.card
  set t := st.deleted.card
  set X := 4 ^ L
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by norm_num)
  have hF : F ≤ ξ * t := A.card_failed_le hA hinv
  have hg : g ≤ X * F := by
    have := card_globalLost_le (x := A.x) (b := A.b) (F := st.loss.failed)
    rw [← hinv.loss.glob] at this
    exact this
  have hU : st.loss.updates ≤ (L + 1) * F := hinv.loss.updates
  have hEn : st.loss.enumerated ≤ (L + 1) * g := by
    have := hinv.loss.enumerated_le fun u hu => by
      have h := hinv.failed_sub hu
      obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp h
      rw [← hA.numTerm_eq]; exact hA.rev_lt e u (List.mem_toFinset.mp he)
    rw [← hinv.loss.glob] at this
    exact this
  have hT : ∑ u ∈ st.loss.glob, A.termWeight u ≤ g * (2 + κ) := by
    have := Finset.sum_le_card_nsmul st.loss.glob A.termWeight (2 + κ) fun u _ => by
      show 2 + (A.termConns u).length ≤ 2 + κ
      have := hA.termConns_length u; omega
    rw [smul_eq_mul] at this
    exact this
  have hI : I ≤ κ * g := A.card_inelig_le hA hinv
  have hvl : ∀ c ∈ st.inelig, (A.C.walk c).verts.length ≤ lam + 1 := fun c hc => by
    rw [hinv.inelig_eq, Finset.mem_filter, Finset.mem_range] at hc
    exact A.verts_length_le hA hlam hc.1
  have hC : ∑ c ∈ st.inelig, A.connWeight c ≤ I * (3 + lam) := by
    have := Finset.sum_le_card_nsmul st.inelig A.connWeight (3 + lam) fun c hc => by
      show 2 + (A.C.walk c).verts.length ≤ 3 + lam
      have := hvl c hc; omega
    rw [smul_eq_mul] at this
    exact this
  have hS : ∑ w ∈ Finset.range G.n, st.supCur w ≤ g + I * (lam + 1) := by
    refine (A.sum_supCur_le hinv).trans (Nat.add_le_add_left ?_ _)
    have := Finset.sum_le_card_nsmul st.inelig (fun c => (A.C.walk c).verts.length) (lam + 1) hvl
    rw [smul_eq_mul] at this
    exact this
  have hP : ∑ p ∈ Finset.range A.numPairs, st.pairCur p ≤ I := A.sum_pairCur_le hA hinv
  have hI3 : I * (3 + lam) ≤ κ * g * (3 + lam) := Nat.mul_le_mul_right _ hI
  have hI1 : I * (lam + 1) ≤ κ * g * (lam + 1) := Nat.mul_le_mul_right _ hI
  -- The event count in terms of `F` and `g`.
  have hA1 : A.events G.n st ≤ (L + 2) * F + (L + 4 + 6 * κ + 2 * (κ * lam)) * g := by
    unfold events
    nlinarith
  -- The coefficients in terms of `K = (L + 2)(1 + κ)(1 + λ)`.
  set K := (L + 2) * (1 + κ) * (1 + lam)
  have hKe : K = L * κ * lam + 2 * (κ * lam) + L * κ + 2 * κ + L * lam + 2 * lam + L + 2 := by
    simp only [K]; ring
  have hc1 : L + 2 ≤ K := by rw [hKe]; omega
  have hc2 : L + 4 + 6 * κ + 2 * (κ * lam) ≤ 10 * K := by rw [hKe]; omega
  have h1 : A.events G.n st ≤ K * F + 10 * K * g := by
    have := Nat.mul_le_mul_right F hc1
    have := Nat.mul_le_mul_right g hc2
    omega
  have h2 : K * g ≤ K * (X * F) := Nat.mul_le_mul_left _ hg
  have h3 : K * F ≤ K * (X * F) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hX)
  have h4 : K * (X * F) ≤ K * (X * ((1 + ξ) * t)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hF.trans (Nat.mul_le_mul_right _ (by omega))))
  have h5 : K * (X * ((1 + ξ) * t)) = A.delCoef ξ κ lam * t := by
    simp only [K, X, L, delCoef]; ring
  have h6 : 10 * K * g = 10 * (K * g) := by ring
  rw [h6] at h1
  have h7 : 12 * A.delCoef ξ κ lam * t = 12 * (A.delCoef ξ κ lam * t) := by ring
  rw [h7]
  omega

/-- The potential `Φ = B_d · t − 2E` with `B_d = 24 · delCoef`. -/
@[expose] def potential (n ξ κ lam : ℕ) (st : DelState) : ℕ :=
  24 * A.delCoef ξ κ lam * st.deleted.card - 2 * A.events n st

/-- The amortized bound of `Delete`. The potential needs no truncation (`2E ≤ B_d t`), and one
`Delete(e)` of an edge not yet deleted costs at most `B_d + 2(1 + ξ)` plus the drop of the
potential, with `B_d = 24 · (1 + ξ)(L + 2) 4^L (1 + κ)(1 + λ)`. -/
theorem potential_amortized {st : DelState} (hA : A.Spec G ξ κ) (hG : G.IsValid)
    (hinv : A.DelInv G st) {lam : ℕ}
    (hlam : ∀ c < A.C.numConn, (A.C.walk c).edges.length ≤ lam) {e : ℕ}
    (he : e ∉ st.deleted) :
    2 * A.events G.n st ≤ 24 * A.delCoef ξ κ lam * st.deleted.card ∧
      A.deleteCost st e + A.potential G.n ξ κ lam (A.deleteState st e) ≤
        A.potential G.n ξ κ lam st + 24 * A.delCoef ξ κ lam + 2 * (1 + ξ) := by
  have hE := A.events_le hA hinv hlam
  obtain ⟨hinv', hdel⟩ := A.deleteState_inv hA hinv e
  have hE' := A.events_le hA hinv' hlam
  obtain ⟨hmono, hcost⟩ := A.deleteCost_le hA hG hinv e
  have hcard : (A.deleteState st e).deleted.card = st.deleted.card + 1 := by
    rw [hdel, Finset.card_insert_of_notMem he]
  rw [hcard] at hE'
  have hB : 24 * A.delCoef ξ κ lam * (st.deleted.card + 1) =
      24 * A.delCoef ξ κ lam * st.deleted.card + 24 * A.delCoef ξ κ lam := by ring
  have hB12 : 2 * (12 * A.delCoef ξ κ lam * st.deleted.card) =
      24 * A.delCoef ξ κ lam * st.deleted.card := by ring
  have hB12' : 2 * (12 * A.delCoef ξ κ lam * (st.deleted.card + 1)) =
      24 * A.delCoef ξ κ lam * (st.deleted.card + 1) := by ring
  refine ⟨by omega, ?_⟩
  unfold potential
  rw [hcard]
  omega

end

end StaticArrays

end MinCostFlow.HierPaths
