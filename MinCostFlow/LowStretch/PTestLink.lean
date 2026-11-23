module

public import MinCostFlow.LowStretch.PSumLink
public import MinCostFlow.LowStretch.ProgPTest

/-!
# What `ptest` decides

When the five cells at `SUM` hold the sums `ESum` of the settled list, and the settled list is the
petal of radius `r`, the test of `ptest` is the pair of tests of region growing for the petal of
radius `r` in bucket `q` (`pass_iff`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

open Classical

variable {G : PG} {P : Par} {c : Cl}

theorem inEnd_mem {Y W : Finset ℕ} {p : ℕ} (h : Leaves G Y W p) : inEnd G W p ∈ W := by
  unfold inEnd
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]; exact h1
  · rw [if_neg (Finset.mem_sdiff.mp h2).2]; exact h1

/-- **The test of `ptest`.** -/
theorem pass_iff (hcw : ∀ p, P.cw p = 1) {M : ℕ} (wt : ℕ → ℕ)
    (hwt : ∀ p ∈ c.act G P, wt p * G.pω p = M) (hM : 0 < M) {Y : Finset ℕ} {pd : PD} {r q : ℕ}
    {sv : ℕ → ℕ} {n : ℕ} {pr ea eb : ℕ → ℕ} {ok : ℕ → Prop} {δ : ℕ → ℕ} {ℓ : List ℕ}
    (hE : c.ELink G P Y (c.carve G Y (pd.withR r)) (pd.withR r) sv n pr ea eb ok δ ℓ)
    (F : PT) (mem : ℕ → ℕ) (hr : F.r = r) (hFM : F.M = M) (hκ : F.κ = P.κ)
    (hsq : F.sq = c.sq G P q) (hP2 : F.P2 = 2 ^ lam P q) (hn : F.nact = (c.act G P).card)
    (hs : ∀ t : Fin 5, mem (F.SUM + t) = ESum ea eb (wt ∘ pr) ok δ n ℓ t) :
    F.Pass mem ↔ (c.cost G P Y (pd.withR r) * c.sq G P q ≤ 8 * c.vol G P Y (pd.withR r) ∧
      c.vol G P Y (pd.withR r) ≤ c.T G P q) := by
  obtain ⟨e0, e1, e3⟩ := esum_link hE wt
  have s0 : mem F.SUM = ESum ea eb (wt ∘ pr) ok δ n ℓ 0 := hs 0
  have s1 : mem (F.SUM + 1) = ESum ea eb (wt ∘ pr) ok δ n ℓ 1 := hs 1
  have s2 : mem (F.SUM + 2) = ESum ea eb (wt ∘ pr) ok δ n ℓ 2 := hs 2
  have s3 : mem (F.SUM + 3) = ESum ea eb (wt ∘ pr) ok δ n ℓ 3 := hs 3
  have s4 : mem (F.SUM + 4) = ESum ea eb (wt ∘ pr) ok δ n ℓ 4 := hs 4
  have hI : ((c.act G P).filter (Inside G (c.carve G Y (pd.withR r)) ·)).card = F.I mem := by
    unfold PT.I; rw [s0, e0]
  have hC : ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y (pd.withR r)) ·), wt p =
      F.C mem := by
    unfold PT.C; rw [s1, s2, e1]; omega
  have hV : ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y (pd.withR r)) ·),
      wt p * c.ent G Y (pd.withR r) (inEnd G (c.carve G Y (pd.withR r)) p) = F.V mem := by
    unfold PT.V; rw [s3, s4, e3]; omega
  have hent : ∀ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y (pd.withR r)) ·),
      c.ent G Y (pd.withR r) (inEnd G (c.carve G Y (pd.withR r)) p) ≤ (pd.withR r).r :=
    fun p hp => ent_le_of_carve (inEnd_mem (Finset.mem_filter.mp hp).2)
  have t1 := (test1_iff (s := c.sq G P q) hcw wt hwt hM Y (pd.withR r) hent hI hC hV).2
  have t2 := test2_iff (q := q) hcw wt hwt hM Y (pd.withR r) hent hI hC hV
  unfold PT.Pass PT.vol8 PT.rhs
  rw [hr, hFM, hκ, hsq, hP2, hn, t1, t2]
  simp only [PD.withR]

end Cl

end MinCostFlow.LowStretch
