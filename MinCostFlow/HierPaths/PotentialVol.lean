module

public import MinCostFlow.HierPaths.DeleteStep
public import MinCostFlow.HierPaths.Params
public import MinCostFlow.Spanner.PathDSContract

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The volume of the pruned set

The last field of `PathDSAbsState.Valid` (`Spanner/PathDSContract.lean`) bounds the volume of the
pruned set `V̂` by `γ_del · t / φ_out` after `t` deletions. For the hierarchy, `γ_del = 1` and
`φ_out = 1/Γ`, so the bound is `Γ · t`.

`vol_prunedSet_le_deleted`: for a state with the invariant, `vol_G(V̂) ≤ 4^L ξ t`, with `L` the
leaf depth and `t` the number of deleted edges. This combines `vol_prunedSet_le` (the the
volume is at most the number of lost terminals) and `card_globalLost_le` (at most `4^L`
times the directly failed ones), and each deleted edge fails at most `ξ` terminals.

With the numbers of `HierPaths/Params.lean`, `4^h ξ ≤ Γ` (`lossFactor_le_gamma`), and the leaf
depth `⌈x / b⌉` is at most `h` when `b = ⌈x / h⌉` (`leafDepth_le_depth`). This gives
`vol_prunedSet_le_gamma` and the real form `vol_prunedSet_le_valid` of the field of `Valid`.
-/

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

public section

/-- The directly failed terminals number at most `ξ` per deleted edge. -/
theorem card_failed_le {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) :
    st.loss.failed.card ≤ ξ * st.deleted.card := by
  refine (Finset.card_le_card hinv.failed_sub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  rw [mul_comm]
  refine Finset.sum_le_card_nsmul _ _ _ fun e _ => ?_
  exact (List.toFinset_card_le _).trans (hA.rev_length e)

/-- The terminals that do not survive are the globally lost ones. -/
theorem card_not_surv {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) :
    (Finset.range A.C.numTerm \ A.surv st).card = (globalLost A.x A.b st.loss.failed).card := by
  rw [surv, Finset.sdiff_sdiff_eq_self (?_ : st.loss.glob ⊆ Finset.range A.C.numTerm),
    hinv.loss.glob]
  rw [hinv.loss.glob, hA.numTerm_eq]
  exact globalLost_subset_range

/-- The volume of the pruned set after `t` deletions is at most `4^L ξ t` (by `card_globalLost_le` and `vol_prunedSet_le`), when
each vertex owns at least its degree in terminals. -/
theorem vol_prunedSet_le_deleted {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st)
    (hdeg : ∀ w < G.n, G.deg w ≤ (A.C.ownedBy w).card) :
    G.vol (A.C.prunedSet G (A.surv st)) ≤
      4 ^ leafDepth A.x A.b * ξ * st.deleted.card := by
  refine (A.C.vol_prunedSet_le hdeg (A.surv st)).trans ?_
  rw [A.card_not_surv hA hinv, mul_assoc]
  exact card_globalLost_le.trans (Nat.mul_le_mul_left _ (A.card_failed_le hA hinv))

end

end StaticArrays

private theorem le_mul_ceilDiv (x h : ℕ) (hh : 0 < h) : x ≤ h * ((x + h - 1) / h) := by
  have h1 := Nat.div_add_mod (x + h - 1) h
  have h2 := Nat.mod_lt (x + h - 1) hh
  omega

public section

/-- The leaf depth `⌈x / ⌈x / h⌉⌉` is at most `h`. -/
theorem leafDepth_le_depth (x h : ℕ) (hh : 0 < h) : leafDepth x ((x + h - 1) / h) ≤ h := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = (x + h - 1) / h := ⟨_, rfl⟩
  have hq : x ≤ h * q := hqdef ▸ le_mul_ceilDiv x h hh
  rw [← hqdef]
  unfold leafDepth
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · rw [h0]; simp
  · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hpos, Nat.succ_mul]
    omega

/-- The leaf depth of the hierarchy with the numbers of `xOf` and `branchBits` is at most its depth `h`. -/
theorem leafDepth_le_depthOf (m : ℕ) : leafDepth (xOf m) (branchBits m) ≤ depthOf m :=
  leafDepth_le_depth _ _ (by have := two_le_depthOf m; omega)

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

/-- With the numbers of `HierPaths/Params.lean`: if the leaf depth is at most `h = depthOf m` for the
edge count `m ≤ M` and the reverse lists have at most `ξ` entries, the volume of the pruned
set after `t` deletions is at most `Γ · t`. -/
theorem vol_prunedSet_le_gamma {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st)
    (hdeg : ∀ w < G.n, G.deg w ≤ (A.C.ownedBy w).card) {a d m M : ℕ} (hmM : m ≤ M)
    (hL : leafDepth A.x A.b ≤ depthOf m) (hξ : ξ ≤ xiOf a d m) :
    G.vol (A.C.prunedSet G (A.surv st)) ≤ gammaHP a d M * st.deleted.card := by
  refine (A.vol_prunedSet_le_deleted hA hinv hdeg).trans (Nat.mul_le_mul_right _ ?_)
  refine le_trans ?_ (lossFactor_le_gamma a d hmM)
  unfold lossFactor
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hL) hξ

/-- The volume field of `PathDSAbsState.Valid` for parameters with `γ_del = 1` and
`φ_out = 1/Γ`: `vol_G(V̂) ≤ γ_del · t / φ_out`. -/
theorem vol_prunedSet_le_valid {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st)
    (hdeg : ∀ w < G.n, G.deg w ≤ (A.C.ownedBy w).card) {a m M : ℕ} (hmM : m ≤ M)
    (hL : leafDepth A.x A.b ≤ depthOf m) (p : PathDSParams) (φ : ℝ)
    (hξ : ξ ≤ xiOf a (Nat.ceil (1 / φ)) m)
    (hdel : p.γ_del φ M = 1) (hout : p.φ_out φ M = 1 / (gammaHP a (Nat.ceil (1 / φ)) M : ℝ)) :
    (G.vol (A.C.prunedSet G (A.surv st)) : ℝ) ≤
      p.γ_del φ M * (st.deleted.card : ℝ) / p.φ_out φ M := by
  rw [hdel, hout, one_mul, div_div_eq_mul_div, div_one, mul_comm]
  exact_mod_cast A.vol_prunedSet_le_gamma hA hinv hdeg hmM hL hξ

end StaticArrays

end

end MinCostFlow.HierPaths
