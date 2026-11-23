module

public import MinCostFlow.LowStretch.ProgChildTopC
public import MinCostFlow.LowStretch.CountVis

/-!
# The top level: words, cost and heap

The children together do at most as much split work as the merge tree has (`Cl.sum_vis_le`,
`KT.visTot_le`), so their heap fits in the words that `ChildPre.room` gives
(`CS.top_room`). The cost of the top level and of the children fits in `childCost`
(`CS.top_cost_le`), and the heap they use fits in `(J + 1) childCost` (`CS.top_space_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {k : ℕ}

/-- **Every child meets `Next`.** -/
theorem next_csOf (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) : Next S.G S.P (S.raw k) (S.csOf k) := by
  by_cases hq : S.resetQ k
  · exact next_reset hpre hk hq
  · have hcs : S.csOf k = S.raw k := by unfold csOf; rw [if_neg hq]
    rw [hcs]
    refine Or.inl ⟨rfl, ?_⟩
    unfold resetQ at hq
    by_cases h2 : 2 ≤ (S.raw k).X.card
    · exact Or.inr (by have := hq; push Not at this; exact this h2)
    · exact Or.inl (by omega)

/-- **The split work of all children** is at most that of the merge tree. -/
theorem sum_visK_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    ∑ k ∈ Finset.range S.nch, S.visK k ≤ S.G.n * (Nat.log 2 S.G.n + 1) + S.G.m + S.T.N := by
  have h1 := Cl.sum_vis_le (cs := S.csOf) hpre.ok.tree hpre.ok.sub hpre.ok.inv.one_le
    (fun k hk => next_csOf hpre hk) (fun k _ => Cl.sat_raw hpre.ok k)
  have h2 : ∑ k ∈ Finset.range S.nch, S.visK k ≤
      ∑ k ∈ Finset.range S.D.nch, (S.T.visW S.G (S.c.raw S.G S.D k) (S.csOf k).θ +
        S.T.hidW S.G (S.csOf k)) :=
    Finset.sum_le_sum fun k _ => Nat.le_add_right _ _
  have h3 := KT.hidW_le_visTot (T := S.T) (G := S.G) S.c
  have h4 := KT.visTot_le hpre.ok.tree hpre.ok.hG
  omega

/-- The heap of all children, summed. -/
theorem sum_spaceK (M1 : ℕ → ℕ) : ∑ k ∈ Finset.range S.nch, S.spaceK M1 k =
    (S.E.J + 1) * (50 * ∑ k ∈ Finset.range S.nch, S.cntK M1 k +
      50 * ∑ k ∈ Finset.range S.nch, S.sNK M1 k + 50 * S.nch +
        10 * ∑ k ∈ Finset.range S.nch, S.visK k) := by
  unfold spaceK
  rw [← Finset.mul_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, mul_one, Finset.sum_const,
    Finset.card_range, smul_eq_mul]
  ring

/-- The heap of the children and the scratch arrays, as a sum of the sizes. -/
theorem H0_eq : S.H0 = S.h + 13 * S.nch + 3 * S.s + 2 * S.nA + 4 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := S.lay
  omega

/-- **The words are large enough** for the scratch arrays, the heap of all children and the
work array of the split walk. -/
theorem top_room (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (M1 : ℕ → ℕ) :
    S.H0 + ∑ k ∈ Finset.range S.nch, S.spaceK M1 k + 3 * (S.s + S.T.N + 1) + S.nch + 10 <
      2 ^ w := by
  obtain ⟨Mw, -, -, hroom⟩ := hpre.room
  have hJ : S.E.J = (GlobL.read S.mem S.GB).J := rfl
  rw [← hJ] at hroom
  rw [sum_spaceK, H0_eq]
  set J := S.E.J
  set X := S.T.N + S.G.m + 2 with hX
  have hcnt := sum_cntK_le (M1 := M1) hpre
  have hsN := sum_sNK_le (S := S) M1
  have hv := sum_visK_le hpre
  have hnch := nch_le hpre
  have hsN' := s_le_N hpre
  have hnA := nA_le hpre
  have hact := act_le S
  have hnN := hpre.ok.tree.n_lt
  have hlog := Nat.log_le_self 2 S.G.n
  -- the split work is at most `X²`
  have hV : S.G.n * (Nat.log 2 S.G.n + 1) + S.G.m + S.T.N ≤ X * X := by
    have a1 : S.G.n * (Nat.log 2 S.G.n + 1) ≤ S.T.N * S.T.N :=
      Nat.mul_le_mul (by omega) (by omega)
    have a2 : S.T.N * S.T.N + (S.G.m + S.T.N) ≤ X * X := by
      have : X * X = S.T.N * S.T.N + (S.G.m + 2) * (2 * S.T.N + S.G.m + 2) := by
        rw [hX]; ring
      rw [this]
      have : S.G.m + S.T.N ≤ (S.G.m + 2) * (2 * S.T.N + S.G.m + 2) := by nlinarith
      omega
    omega
  have hX2 : 2 ≤ X := by omega
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  -- everything is at most `200 (J + 1) X²`
  have hY : 13 * S.nch + 3 * S.s + 2 * S.nA + 4 +
      (J + 1) * (50 * ∑ k ∈ Finset.range S.nch, S.cntK M1 k +
        50 * ∑ k ∈ Finset.range S.nch, S.sNK M1 k + 50 * S.nch +
          10 * ∑ k ∈ Finset.range S.nch, S.visK k) + 3 * (S.s + S.T.N + 1) + S.nch + 10 ≤
      (J + 1) * (200 * (X * X)) := by
    have b1 : 50 * ∑ k ∈ Finset.range S.nch, S.cntK M1 k +
        50 * ∑ k ∈ Finset.range S.nch, S.sNK M1 k + 50 * S.nch +
          10 * ∑ k ∈ Finset.range S.nch, S.visK k ≤ 150 * X + 10 * (X * X) := by omega
    have b2 := Nat.mul_le_mul_left (J + 1) b1
    have b3 : 14 * S.nch + 6 * S.s + 2 * S.nA + 3 * S.T.N + 17 ≤ 40 * (X * X) := by omega
    have b4 : 40 * (X * X) ≤ (J + 1) * (40 * (X * X)) := Nat.le_mul_of_pos_left _ (by omega)
    have b5 : (J + 1) * (150 * X + 10 * (X * X)) + (J + 1) * (40 * (X * X)) ≤
        (J + 1) * (200 * (X * X)) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hJ2 : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self
  have hp : 2 ^ (2 * J + 20) = 2 ^ J * 2 ^ J * 2 ^ 20 := by
    rw [← pow_add, ← pow_add]; ring_nf
  have hM : 1 ≤ (Mw + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hZ : (J + 1) * (200 * (X * X)) ≤ 2 ^ (2 * J + 20) * X ^ 2 * (Mw + 2) ^ 2 := by
    have c1 : (J + 1) * (200 * (X * X)) ≤ 2 ^ J * (2 ^ J * 2 ^ 20) * (X * X) := by
      have : 200 ≤ 2 ^ J * 2 ^ 20 := by
        have : 1 ≤ 2 ^ J := Nat.one_le_two_pow
        have : (2 : ℕ) ^ 20 = 1048576 := by norm_num
        nlinarith
      calc (J + 1) * (200 * (X * X)) = (J + 1) * 200 * (X * X) := by ring
        _ ≤ 2 ^ J * (2 ^ J * 2 ^ 20) * (X * X) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hJ2 this)
    calc (J + 1) * (200 * (X * X)) ≤ 2 ^ J * (2 ^ J * 2 ^ 20) * (X * X) := c1
      _ = 2 ^ (2 * J + 20) * X ^ 2 * 1 := by rw [hp]; ring
      _ ≤ 2 ^ (2 * J + 20) * X ^ 2 * (Mw + 2) ^ 2 := Nat.mul_le_mul_left _ hM
  omega

/-- One child's part of `childCost`. -/
noncomputable def ccK (S : CS) (k : ℕ) : ℕ :=
  10000 * (S.E.J + 1) + log2Cost (Cl.resetS S.T S.G S.P (S.raw k) /
    (4 * S.P.B * (S.raw k).X.card)) + 10000 * S.T.visW S.G (S.raw k) (S.csOf k).θ

theorem childCost_eq (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    childCost S.T S.G S.P S.c S.R S.D S.csOf S.E.J =
      100000 * (Nat.log 2 S.E.J + 2) * ((S.c.act S.G S.P).card + S.s + 1) +
        ∑ k ∈ Finset.range S.nch, S.ccK k := by
  rw [(pre_of hpre).s]
  rfl

/-- **The cost of the child step** fits in `childCost`. -/
theorem top_cost_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (M1 : ℕ → ℕ) :
    400 + S.topCost + ∑ k ∈ Finset.range S.nch, (S.costK M1 k + 100) ≤
      childCost S.T S.G S.P S.c S.R S.D S.csOf S.E.J := by
  rw [childCost_eq hpre]
  have hk : ∀ k ∈ Finset.range S.nch, S.costK M1 k + 100 + 400 ≤
      (400 * (Nat.log 2 S.E.J + 2) + 9000) * S.cntK M1 k +
        (400 * (Nat.log 2 S.E.J + 2) + 9000) * S.sNK M1 k + S.ccK k := by
    intro k _
    unfold costK ccK visK
    rw [mul_add]
    omega
  have h1 := Finset.sum_le_sum hk
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum] at h1
  set L := Nat.log 2 S.E.J + 2
  have hcnt := sum_cntK_le (M1 := M1) hpre
  have hsN := sum_sNK_le (S := S) M1
  have hnA := nA_le hpre
  have hc : S.topCost = 1000 + 300 * (S.s + S.nch + S.nA) := rfl
  have hL : 2 ≤ L := by omega
  set a := (S.c.act S.G S.P).card
  have m1 : (400 * L + 9000) * ∑ k ∈ Finset.range S.nch, S.cntK M1 k ≤ (400 * L + 9000) * a :=
    Nat.mul_le_mul_left _ hcnt
  have m2 : (400 * L + 9000) * ∑ k ∈ Finset.range S.nch, S.sNK M1 k ≤ (400 * L + 9000) * S.s :=
    Nat.mul_le_mul_left _ hsN
  have m3 : 100000 * L * (a + S.s + 1) = 400 * L * a + 400 * L * S.s + 99600 * L * a +
      99600 * L * S.s + 100000 * L := by ring
  have m4 : (400 * L + 9000) * a = 400 * L * a + 9000 * a := by ring
  have m5 : (400 * L + 9000) * S.s = 400 * L * S.s + 9000 * S.s := by ring
  have m6 : 2 * a ≤ L * a := Nat.mul_le_mul_right _ hL
  have m7 : 2 * S.s ≤ L * S.s := Nat.mul_le_mul_right _ hL
  have m8 : 99600 * L * a = 99600 * (L * a) := by ring
  have m9 : 99600 * L * S.s = 99600 * (L * S.s) := by ring
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

/-- **The heap of the child step** fits in `(J + 1) childCost`. -/
theorem top_space_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (M1 : ℕ → ℕ) :
    S.H0 + ∑ k ∈ Finset.range S.nch, S.spaceK M1 k ≤
      S.h + (S.E.J + 1) * childCost S.T S.G S.P S.c S.R S.D S.csOf S.E.J := by
  rw [sum_spaceK, H0_eq, childCost_eq hpre]
  set L := Nat.log 2 S.E.J + 2
  have hk : ∀ k ∈ Finset.range S.nch, 10000 + 10000 * S.visK k ≤ S.ccK k := by
    intro k _
    unfold ccK visK
    have : 10000 ≤ 10000 * (S.E.J + 1) := by omega
    omega
  have h1 := Finset.sum_le_sum hk
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum] at h1
  have hcnt := sum_cntK_le (M1 := M1) hpre
  have hsN := sum_sNK_le (S := S) M1
  have hnA := nA_le hpre
  set a := (S.c.act S.G S.P).card
  set V := ∑ k ∈ Finset.range S.nch, S.visK k
  set C := 100000 * L * (a + S.s + 1) + ∑ k ∈ Finset.range S.nch, S.ccK k
  have hL : 2 ≤ L := by omega
  have hC1 : 100000 * 2 * (a + S.s + 1) ≤ 100000 * L * (a + S.s + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hW : 50 * ∑ k ∈ Finset.range S.nch, S.cntK M1 k +
      50 * ∑ k ∈ Finset.range S.nch, S.sNK M1 k + 50 * S.nch + 10 * V +
        (13 * S.nch + 3 * S.s + 2 * S.nA + 4) ≤ C := by omega
  have h2 := Nat.mul_le_mul_left (S.E.J + 1) hW
  rw [Nat.mul_add] at h2
  have h3 : 13 * S.nch + 3 * S.s + 2 * S.nA + 4 ≤
      (S.E.J + 1) * (13 * S.nch + 3 * S.s + 2 * S.nA + 4) := Nat.le_mul_of_pos_left _ (by omega)
  omega

end CS

end MinCostFlow.LowStretch
