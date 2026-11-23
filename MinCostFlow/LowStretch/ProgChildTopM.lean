module

public import MinCostFlow.LowStretch.ProgChildTopA
public import MinCostFlow.LowStretch.ProgChildStor
public import MinCostFlow.LowStretch.ProgChildIdx
public import MinCostFlow.LowStretch.ProgChildKey

/-!
# The top level: the petal lists and the sizes

`chxP` reads the settled lists of the petals as positions `PO[k] ≤ j < PO[k + 1]` of the array
`PL` (`CS.chxE`). This file proves its precondition (`CS.chxE_ok`): the lists of two petals have
no common node, since a node lies in one piece only. The same fact bounds the total length of
the lists by the number of nodes (`CS.po_span_le`), which bounds the cost of `chxP`.

It also bounds the sizes that the cost and the heap of the child step use: the number of petals
by `n` (each petal has its center, `Cl.xc_mem`), the number of nodes by `N`, the active entries by
`m`, and the nodes of all children by `s`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- The petal lists, as `chxP` reads them. -/
def chxE : CXE := ⟨S.X.nP, S.X.PL, S.X.PO, S.CHX, S.mem⟩

variable {S} {w : ℕ}

theorem mem_nodesOf {k u : ℕ} :
    u ∈ S.X.nodesOf S.mem k ↔ ∃ j, S.chxE.In k j ∧ S.chxE.nd j = u := by
  unfold PetL.nodesOf CXE.In CXE.nd CXE.o chxE
  dsimp only
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨S.mem (S.X.PO + k) + j, ⟨by omega, by omega⟩, by congr 1; omega⟩
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
    exact ⟨j - S.mem (S.X.PO + k), by omega, by congr 1; omega⟩

theorem chxE_nodes (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {k : ℕ} (hk : k < S.X.nP) {j : ℕ} (hj : S.chxE.In k j) :
    ∃ v ∈ S.c.W S.G S.D k, S.R.sv S.T S.c v = S.chxE.nd j :=
  (hpre.pet.nodes k hk _).mp (mem_nodesOf.mpr ⟨j, hj, rfl⟩)

/-- Two petal lists with a common node are the same list. -/
theorem chxE_disj (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {k1 k2 j1 j2 : ℕ} (hk1 : k1 < S.X.nP) (hk2 : k2 < S.X.nP) (h1 : S.chxE.In k1 j1)
    (h2 : S.chxE.In k2 j2) (he : S.chxE.nd j1 = S.chxE.nd j2) : k1 = k2 := by
  obtain ⟨v1, hv1, e1⟩ := chxE_nodes hpre hk1 h1
  obtain ⟨v2, hv2, e2⟩ := chxE_nodes hpre hk2 h2
  have hnP : S.X.nP = S.D.ps.length := hpre.pet.nP
  have hv1' : v1 ∈ (S.c.raw S.G S.D (k1 + 1)).X := hv1
  have hv2' : v2 ∈ (S.c.raw S.G S.D (k2 + 1)).X := hv2
  have hv := hpre.ok.raw_of_sv (Cl.W_subset_X k1 hv1) (Cl.W_subset_X k2 hv2)
    (e1.trans (he.trans e2.symm)) (k1 + 1) hv1'
  have := Cl.raw_unique (D := S.D) (by unfold Cl.Dec.nch; omega) (by unfold Cl.Dec.nch; omega)
    hv hv2'
  omega

/-- **The precondition of `chxP`.** -/
theorem chxE_ok (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hb : S.CHX + S.s < 2 ^ w) : S.chxE.Ok w S.s where
  mono k hk := hpre.pet.po k hk
  nd_lt k hk j hj := (pre_of hpre).nd_lt k hk _ (mem_nodesOf.mpr ⟨j, hj, rfl⟩)
  disj _ hk1 _ hk2 _ _ h1 h2 he := chxE_disj hpre hk1 hk2 h1 h2 he
  l1 := by
    have hr : (S.X.PL, S.mem (S.X.PO + S.X.nP)) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
      simp [readRegs, PetL.regs]
    have := hpre.below _ hr
    have e : S.CHX = S.h + 9 * S.nch := rfl
    show S.X.PL + S.mem (S.X.PO + S.X.nP) ≤ S.CHX
    dsimp only at this
    omega
  l2 := by
    have hr : (S.X.PO, S.X.nP + 1) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
      simp [readRegs, PetL.regs]
    have := hpre.below _ hr
    have e : S.CHX = S.h + 9 * S.nch := rfl
    show S.X.PO + S.X.nP + 1 ≤ S.CHX
    dsimp only at this
    omega
  l3 := hb

/-- Every position between the start of the first list and the end of list `n - 1` lies in one
of the first `n` lists. -/
theorem exists_In (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) {j : ℕ}
    (h0 : S.chxE.o 0 ≤ j) : ∀ n ≤ S.X.nP, j < S.chxE.o n → ∃ k < n, S.chxE.In k j := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ n ih =>
    intro hn h
    by_cases hj : j < S.chxE.o n
    · obtain ⟨k, hk, hk'⟩ := ih (by omega) hj
      exact ⟨k, by omega, hk'⟩
    · exact ⟨n, by omega, by omega, h⟩

/-- **The petal lists have at most `s` positions in all**, since their nodes are distinct nodes
of `c`. -/
theorem po_span_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.mem (S.X.PO + S.X.nP) - S.mem S.X.PO ≤ S.s := by
  have e0 : S.chxE.o 0 = S.mem S.X.PO := rfl
  have eN : S.chxE.o S.X.nP = S.mem (S.X.PO + S.X.nP) := rfl
  rw [← e0, ← eN, ← Nat.card_Ico, ← Finset.card_range S.s]
  refine Finset.card_le_card_of_injOn S.chxE.nd (fun j hj => ?_) (fun j1 hj1 j2 hj2 he => ?_)
  · obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
    obtain ⟨k, hk, hkj⟩ := exists_In hpre h1 _ le_rfl h2
    exact Finset.mem_range.mpr ((pre_of hpre).nd_lt k hk _ (mem_nodesOf.mpr ⟨j, hkj, rfl⟩))
  · obtain ⟨a1, a2⟩ := Finset.mem_Ico.mp hj1
    obtain ⟨b1, b2⟩ := Finset.mem_Ico.mp hj2
    obtain ⟨k1, hk1, i1⟩ := exists_In hpre a1 _ le_rfl a2
    obtain ⟨k2, hk2, i2⟩ := exists_In hpre b1 _ le_rfl b2
    have hkk := chxE_disj hpre hk1 hk2 i1 i2 he
    subst hkk
    have hnd : (S.X.nodesOf S.mem k1).Nodup := hpre.pet.nodup k1 hk1
    unfold PetL.nodesOf at hnd
    obtain ⟨c1, c2⟩ := i1
    obtain ⟨d1, d2⟩ := i2
    have e1 : S.chxE.nd j1 = S.mem (S.X.PL + S.mem (S.X.PO + k1) + (j1 - S.chxE.o k1)) := by
      show S.mem (S.X.PL + j1) = _; congr 1; have : S.chxE.o k1 = S.mem (S.X.PO + k1) := rfl; omega
    have e2 : S.chxE.nd j2 = S.mem (S.X.PL + S.mem (S.X.PO + k1) + (j2 - S.chxE.o k1)) := by
      show S.mem (S.X.PL + j2) = _; congr 1; have : S.chxE.o k1 = S.mem (S.X.PO + k1) := rfl; omega
    have hlen : S.chxE.o (k1 + 1) - S.chxE.o k1 =
        S.mem (S.X.PO + (k1 + 1)) - S.mem (S.X.PO + k1) := rfl
    have := List.inj_on_of_nodup_map hnd (List.mem_range.mpr (show j1 - S.chxE.o k1 < _ by omega))
      (List.mem_range.mpr (show j2 - S.chxE.o k1 < _ by omega)) (e1.symm.trans (he.trans e2))
    omega

/-- The number of petals is at most `n`: the center of each petal lies in it, and the petals are
disjoint. -/
theorem nP_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.X.nP ≤ S.G.n := by
  have hnP : S.X.nP = S.D.ps.length := hpre.pet.nP
  rw [hnP, ← Finset.card_range S.D.ps.length, ← Finset.card_range S.G.n]
  refine Finset.card_le_card_of_injOn (fun k => S.D.xc S.G k) (fun k hk => ?_)
    (fun k1 hk1 k2 hk2 he => ?_)
  · have hk' := Finset.mem_range.mp hk
    exact hpre.ok.sub (Cl.W_subset_X k (Cl.xc_mem hpre.dec hk'))
  · have h1 := Cl.xc_mem hpre.dec (Finset.mem_range.mp hk1)
    have h2 := Cl.xc_mem hpre.dec (Finset.mem_range.mp hk2)
    dsimp only at he
    rw [he] at h1
    rcases Nat.lt_trichotomy k1 k2 with h | h | h
    · exact (Cl.W_disj h h1 h2).elim
    · exact h
    · exact (Cl.W_disj h h2 h1).elim

theorem nch_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.nch ≤ S.G.n + 1 := by
  have := nch_eq hpre
  have := nP_le hpre
  omega

/-- The nodes of `c` are distinct nodes of the merge tree. -/
theorem s_le_N (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.s ≤ S.T.N := by
  classical
  rw [(pre_of hpre).s, ← List.toFinset_card_of_nodup hpre.ok.nodup]
  exact (Finset.card_le_card (fun j hj => Finset.mem_range.mpr
    (hpre.ok.node_lt j (List.mem_toFinset.mp hj)))).trans (by simp)

/-- The active entries are distinct active pairs. -/
theorem nA_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.nA ≤ (S.c.act S.G S.P).card := by
  classical
  have hnd : (S.X.actL S.mem).Nodup := hpre.pet.act_nodup
  have hlen : (S.X.actL S.mem).length = S.nA := by simp [PetL.actL, nA]
  have h2 : (S.X.actL S.mem).toFinset ⊆ S.c.act S.G S.P := fun p hp =>
    (hpre.pet.act p).mp (List.mem_toFinset.mp hp)
  have h3 := Finset.card_le_card h2
  rw [List.toFinset_card_of_nodup hnd, hlen] at h3
  exact h3

theorem act_le (S : CS) : (S.c.act S.G S.P).card ≤ S.G.m := by
  classical
  unfold Cl.act
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The node groups hold at most the `s` nodes. -/
theorem sum_sNK_le (M1 : ℕ → ℕ) : ∑ k ∈ Finset.range S.nch, S.sNK M1 k ≤ S.s := by
  simp only [sNK]
  rw [sum_grp_length]
  exact offOf_le' _ _ _

end CS

end MinCostFlow.LowStretch
