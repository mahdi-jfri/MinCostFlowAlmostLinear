module

public import MinCostFlow.LowStretch.ProgChildMid2

/-!
# The child step: the bound on the stored pairs

The loop invariant `CInv` says that child `j` stores at most `cntK j + visK j` pairs: the active
pairs whose key is `j`, and on a reset the pairs made visible at the split nodes. The keys put
each active pair in at most one group, and the active pairs are listed once each, so the groups
hold at most `|act c|` pairs in all (`sum_cntK_le`). This gives the last conjunct of `ChildPost`
(`stor_sum`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The groups of the keys below `n` hold `offOf f M n` items. -/
theorem sum_grp_length (f : ℕ → ℕ) (M n : ℕ) :
    ∑ k ∈ Finset.range n, (grp f M k).length = offOf f M n := by
  induction n with
  | zero => simp [offOf_zero]
  | succ n ih => rw [Finset.sum_range_succ, ih, offOf_succ]

namespace CS

variable {S : CS} {w : ℕ} {M1 : ℕ → ℕ}

/-- **The key groups hold at most the active pairs.** -/
theorem sum_cntK_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    ∑ k ∈ Finset.range S.nch, S.cntK M1 k ≤ (S.c.act S.G S.P).card := by
  classical
  have h1 : ∑ k ∈ Finset.range S.nch, S.cntK M1 k ≤ S.nA := by
    simp only [cntK]
    rw [sum_grp_length]
    unfold offOf
    exact (List.length_filter_le _ _).trans (by simp)
  have hnd : (S.X.actL S.mem).Nodup := hpre.pet.act_nodup
  have hlen : (S.X.actL S.mem).length = S.nA := by simp [PetL.actL, nA]
  have h2 : (S.X.actL S.mem).toFinset ⊆ S.c.act S.G S.P := fun p hp =>
    (hpre.pet.act p).mp (List.mem_toFinset.mp hp)
  have h3 := Finset.card_le_card h2
  rw [List.toFinset_card_of_nodup hnd, hlen] at h3
  omega

/-- **The stored pairs of all children**, from the loop invariant after the last child. -/
theorem stor_sum (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {H : ℕ} {Rs : ℕ → Rec} {M : ℕ → ℕ} (hI : CInv w S M1 S.nch H Rs M) :
    ∑ k ∈ Finset.range S.nch, (Rs k).S.length ≤
      (S.c.act S.G S.P).card + ∑ k ∈ Finset.range S.nch, S.T.visW S.G (S.raw k) (S.csOf k).θ := by
  have h1 : ∑ k ∈ Finset.range S.nch, (Rs k).S.length ≤
      ∑ k ∈ Finset.range S.nch, (S.cntK M1 k + S.visK k) :=
    Finset.sum_le_sum fun k hk => hI.stor k (Finset.mem_range.mp hk)
  rw [Finset.sum_add_distrib] at h1
  have h2 := sum_cntK_le (M1 := M1) hpre
  simp only [visK] at h1
  omega

end CS

end MinCostFlow.LowStretch
