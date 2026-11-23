module

public import MinCostFlow.HierPaths.BuildHierAux

/-!
# The whole static construction: the hosts

The static construction builds the hosts of the hierarchy depth by depth.
The root host is a given graph `H0` on the `2^x` terminals (in the application, the host of
`lemma_2`). At a group `g` of depth `j` with host `host j g`, the child construction `lemma_3` plays one
batched game for all children `g · B + i`, `i < B` (`B = branching x b j`). The host of child
`i` is the child host of that game, shifted to the child's terminals.

`BuildHyp` collects the conditions on the numbers: the root host has degree at most `Δ` and
expansion `β`; `β ≤ 1/(2 P_r)`, so child hosts expand at least as well as the root; every child
host has degree at most `T + 1 = 49 L' + 2 ≤ Δ`; and the core's size and degree limits hold.

`hostOK_all` proves by induction over the depth that every host of a group of size above one
meets the router's conditions with the same `Δ`, `L` and `β` (`HostOK`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The parameters of the construction: the router, the core, the core's numbers `M` and `r`, the
degree bound `Δ` and the size exponent `L` of the router calls, the round exponent `L'` (each
game has `49 L' + 1` rounds), and the shape `x`, `b` of the hierarchy. -/
structure BuildParams where
  /-- The router of Lemma 1. -/
  route : RouterFn
  /-- The core cut player. -/
  core : ℕ → Graph → CoreResult
  /-- The core's size parameter. -/
  M : ℕ
  /-- The core's depth. -/
  r : ℕ
  /-- The degree bound of all hosts. -/
  Δ : ℕ
  /-- The size exponent of the router calls. -/
  L : ℕ
  /-- The round exponent of the games. -/
  L' : ℕ
  /-- There are `2^x` terminals. -/
  x : ℕ
  /-- Each split has at most `2^b` children. -/
  b : ℕ

namespace BuildParams

variable (B : BuildParams)

/-- The number of rounds of each game. -/
def T : ℕ := 49 * B.L' + 1

/-- The offset of child `i` of group `g` at depth `j`. -/
def off (j g i : ℕ) : ℕ := (g * branching B.x B.b j + i) * groupSize B.x B.b (j + 1)

/-- The local edges of the host of child `i` of group `g` at depth `j`, whose host is `Hg`. -/
def localEdges (Hg : Graph) (j g i : ℕ) : List (ℕ × ℕ) :=
  childEdges B.route Hg (members B.x B.b j g) B.Δ B.L B.core B.M B.r (groupSize B.x B.b (j + 1))
    (branching B.x B.b j) (B.off j g) B.T i

/-- The local edges of the host of child `i`, each with its walk in `Hg`. -/
def localFamily (Hg : Graph) (j g i : ℕ) : List ((ℕ × ℕ) × List ℕ) :=
  childFamily B.route Hg (members B.x B.b j g) B.Δ B.L B.core B.M B.r (groupSize B.x B.b (j + 1))
    (branching B.x B.b j) (B.off j g) B.T i

/-- The host of group `c` at depth `j`. -/
def host (H0 : Graph) : ℕ → ℕ → Graph
  | 0, _ => H0
  | j + 1, c =>
    ⟨2 ^ B.x, shiftEdges (B.off j (parentGroup B.x B.b j c) (c % branching B.x B.b j))
      (B.localEdges (host H0 j (parentGroup B.x B.b j c)) j (parentGroup B.x B.b j c)
        (c % branching B.x B.b j))⟩

/-- The walk in the parent host of edge `e` of the host of group `c` at depth `j + 1`. -/
def emb (H0 : Graph) (j c e : ℕ) : List ℕ :=
  ((B.localFamily (B.host H0 j (parentGroup B.x B.b j c)) j (parentGroup B.x B.b j c)
    (c % branching B.x B.b j)).getD e ((0, 0), [])).2

/-- The connectors between the groups `c` and `c'` at depth `j + 1`: one full-routing call between the two groups in the
host of their parent. -/
def conn (H0 : Graph) (j c c' : ℕ) : List (ℕ × ℕ × List ℕ) :=
  (siblingConns B.route (B.host H0 j (parentGroup B.x B.b j c)) (members B.x B.b j (parentGroup B.x B.b j c))
      B.Δ B.L (fun i => members B.x B.b (j + 1) (parentGroup B.x B.b j c * branching B.x B.b j + i))
      (c % branching B.x B.b j) (c' % branching B.x B.b j)).map
    fun q => (q.1.1, q.1.2, q.2)

/-- The output of the construction. -/
def hier (H0 : Graph) : HierData := ⟨B.host H0, B.emb H0, B.conn H0⟩

/-- The conditions on the numbers of the construction. -/
structure BuildHyp (cfg : ParamConfig) (H0 : Graph) (β : ℕ → ℝ) (bh : ℕ → ℕ) : Prop where
  root_n : H0.n = 2 ^ B.x
  root_valid : H0.IsValid
  root_loopless : H0.IsLoopless
  root_deg : ∀ v, H0.deg v ≤ B.Δ
  root_exp : H0.IsExpansionExpanderOn (Finset.range (2 ^ B.x)) (β 0)
  β_pos : ∀ j, 0 < β j
  β_le : ∀ j, β (j + 1) ≤ 1 / (2 * PParam cfg B.M B.r : ℝ)
  bh_ge : ∀ j, max 2 (2 / β j) ≤ (bh j : ℝ)
  deg_le : 49 * B.L' + 2 ≤ B.Δ
  L_pos : 1 ≤ B.L
  x_lt_L : B.x < B.L
  x_lt_L' : B.x < B.L'
  size_le : 2 ^ B.x ≤ (NOf B.M B.r) ^ B.r
  core_deg : 49 * B.L' ≤ deltaParam B.M

/-- The host of group `g` at depth `j` meets the router's conditions with `Δ`, `L`, expansion
`β`, and has its edges inside the group. -/
def HostOK (H0 : Graph) (β : ℕ → ℝ) (j g : ℕ) : Prop :=
  HostPre (B.host H0 j g) (members B.x B.b j g) B.Δ B.L ∧
    (B.host H0 j g).IsExpansionExpanderOn (members B.x B.b j g) (β j) ∧
    ∀ e ∈ (B.host H0 j g).edges, e.1 ∈ members B.x B.b j g ∧ e.2 ∈ members B.x B.b j g

end BuildParams

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

namespace BuildParams

variable {B : BuildParams}

theorem childSet_eq (j g i : ℕ) :
    shiftSet (B.off j g i) (Finset.range (groupSize B.x B.b (j + 1))) =
      members B.x B.b (j + 1) (g * branching B.x B.b j + i) := by
  rw [members_eq_shiftSet]
  rfl

theorem child_mod {x b j g i : ℕ} (hi : i < branching x b j) :
    (g * branching x b j + i) % branching x b j = i := by
  rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi]

theorem child_lt {x b j g i : ℕ} (hg : g < numGroups x b j) (hi : i < branching x b j) :
    g * branching x b j + i < numGroups x b (j + 1) := by
  rw [numGroups_succ]
  have : (g + 1) * branching x b j ≤ numGroups x b j * branching x b j :=
    Nat.mul_le_mul_right _ hg
  rw [add_mul, one_mul] at this
  omega

/-- The children of a group, as shifted intervals. -/
theorem isChildren_group {j g : ℕ} :
    IsChildren (members B.x B.b j g)
      (fun i => shiftSet (B.off j g i) (Finset.range (groupSize B.x B.b (j + 1))))
      (branching B.x B.b j) (groupSize B.x B.b (j + 1)) := by
  refine ⟨groupSize_pos, fun i hi => ⟨?_, ?_⟩, fun i hi i' hi' h => ?_⟩
  · simp only
    rw [childSet_eq]
    have h := members_succ_subset (x := B.x) (b := B.b) (j := j) (g * branching B.x B.b j + i)
    rw [parentGroup_child g hi] at h
    exact h
  · simp only
    rw [card_shiftSet, Finset.card_range]
  · simp only
    rw [childSet_eq, childSet_eq]
    exact disjoint_members (by omega)

/-- **The child construction `lemma_3` at a group of the hierarchy.** -/
theorem lemma3_at {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) {j g : ℕ}
    (hs : 1 < groupSize B.x B.b (j + 1)) (hok : B.HostOK H0 β j g) :
    (∀ i < branching B.x B.b j,
      (Graph.mk (groupSize B.x B.b (j + 1)) (B.localEdges (B.host H0 j g) j g i)).IsExpansionExpanderOn
        (Finset.range (groupSize B.x B.b (j + 1))) (1 / (2 * PParam cfg B.M B.r : ℝ)) ∧
      (Graph.mk (groupSize B.x B.b (j + 1)) (B.localEdges (B.host H0 j g) j g i)).IsValid ∧
      (Graph.mk (groupSize B.x B.b (j + 1)) (B.localEdges (B.host H0 j g) j g i)).IsLoopless ∧
      (∀ v, (Graph.mk (groupSize B.x B.b (j + 1)) (B.localEdges (B.host H0 j g) j g i)).deg v ≤
        49 * B.L' + 2) ∧
      (B.localFamily (B.host H0 j g) j g i).map Prod.fst = B.localEdges (B.host H0 j g) j g i ∧
      ∀ en ∈ B.localFamily (B.host H0 j g) j g i,
        EntryOK (B.host H0 j g) (members B.x B.b j g) (B.off j g i) (routePathLen B.Δ (bh j) B.L) en) ∧
    ∀ e < (B.host H0 j g).m, ∑ i ∈ Finset.range (branching B.x B.b j),
        occLoad (walkFamily (B.localFamily (B.host H0 j g) j g i)) e ≤
      (49 * B.L' + 2) * routeCong B.Δ (bh j) B.L := by
  have hsx : groupSize B.x B.b (j + 1) ≤ 2 ^ B.x := Nat.pow_le_pow_right (by norm_num) (by omega)
  have heven : groupSize B.x B.b (j + 1) % 2 = 0 := Nat.even_iff.mp (even_groupSize hs)
  have hsL : groupSize B.x B.b (j + 1) < 2 ^ B.L' :=
    lt_of_le_of_lt hsx (Nat.pow_lt_pow_right (by norm_num) hyp.x_lt_L')
  exact lemma_3 hrouter hok.1 (hyp.β_pos _) hok.2.1 (hyp.bh_ge _) hcore isChildren_group branching_pos heven
    (hsx.trans hyp.size_le) hyp.core_deg hsL

/-- The host of child `i` of group `g`. -/
theorem host_child (H0 : Graph) {j g i : ℕ} (hi : i < branching B.x B.b j) :
    B.host H0 (j + 1) (g * branching B.x B.b j + i) =
      ⟨2 ^ B.x, shiftEdges (B.off j g i) (B.localEdges (B.host H0 j g) j g i)⟩ := by
  simp only [host, parentGroup_child g hi, child_mod hi]

/-- **One depth of the induction.** -/
theorem hostOK_child {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) {j g : ℕ}
    (hg : g < numGroups B.x B.b j) (hs : 1 < groupSize B.x B.b (j + 1)) (hok : B.HostOK H0 β j g)
    {i : ℕ} (hi : i < branching B.x B.b j) :
    B.HostOK H0 β (j + 1) (g * branching B.x B.b j + i) := by
  obtain ⟨hl3, _⟩ := lemma3_at hrouter hcore hyp hs hok
  obtain ⟨hexpL, hvalid, hloop, hdeg, _, _⟩ := hl3 i hi
  set s := groupSize B.x B.b (j + 1)
  set o := B.off j g i
  set E := B.localEdges (B.host H0 j g) j g i
  have hX : members B.x B.b (j + 1) (g * branching B.x B.b j + i) = shiftSet o (Finset.range s) :=
    (childSet_eq j g i).symm
  unfold HostOK
  rw [host_child H0 hi, hX]
  have hsx : s ≤ 2 ^ B.x := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmem : ∀ e ∈ shiftEdges o E, ∃ f ∈ E, e = (o + f.1, o + f.2) := by
    intro e he
    unfold shiftEdges at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact ⟨f, hf, rfl⟩
  have hdl := hyp.deg_le
  refine ⟨⟨?_, ?_, by omega, ?_, hyp.L_pos, ?_⟩, ?_, ?_⟩
  · rw [← hX]
    exact members_subset_range (child_lt hg hi)
  · intro e he
    rw [inside_shift _ s] at he
    unfold shiftEdges at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    have := hloop f (List.mem_of_mem_filter hf)
    simp only
    omega
  · intro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    rw [degIn_shift _ s]
    exact (hdeg u).trans (by omega)
  · rw [card_shiftSet, Finset.card_range]
    exact lt_of_le_of_lt hsx (Nat.pow_lt_pow_right (by norm_num) hyp.x_lt_L)
  · exact isExpansionExpanderOn_mono (hyp.β_le j) (isExpansionExpanderOn_shift hexpL)
  · intro e he
    obtain ⟨f, hf, rfl⟩ := hmem e he
    have := hvalid f hf
    exact ⟨mem_shiftSet.mpr (Finset.mem_range.mpr this.1), mem_shiftSet.mpr (Finset.mem_range.mpr this.2)⟩

/-- The root host meets the conditions. -/
theorem hostOK_root {cfg : ParamConfig} {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ}
    (hyp : B.BuildHyp cfg H0 β bh) (g : ℕ) (hg : g < numGroups B.x B.b 0) :
    B.HostOK H0 β 0 g := by
  have hg0 : g = 0 := by
    have : numGroups B.x B.b 0 = 1 := by simp [numGroups]
    omega
  subst hg0
  have hX : members B.x B.b 0 0 = Finset.range (2 ^ B.x) := by
    ext u
    simp [members, groupSize_zero]
  have hH : B.host H0 0 0 = H0 := rfl
  unfold HostOK
  rw [hH, hX]
  have hdl := hyp.deg_le
  have hverts : Finset.range (2 ^ B.x) = H0.verts := by rw [Graph.verts, hyp.root_n]
  refine ⟨⟨by rw [hyp.root_n], fun e he => hyp.root_loopless e (List.mem_of_mem_filter he),
    by omega, fun v _ => ?_, hyp.L_pos, ?_⟩, hyp.root_exp, fun e he => ?_⟩
  · rw [hverts]
    exact hyp.root_deg v
  · rw [Finset.card_range]
    exact Nat.pow_lt_pow_right (by norm_num) hyp.x_lt_L
  · have := hyp.root_valid e he
    rw [hyp.root_n] at this
    exact ⟨Finset.mem_range.mpr this.1, Finset.mem_range.mpr this.2⟩

/-- **Every host meets the conditions.** -/
theorem hostOK_all {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) :
    ∀ j g, 1 < groupSize B.x B.b j → g < numGroups B.x B.b j → B.HostOK H0 β j g := by
  intro j
  induction j with
  | zero => exact fun g _ hg => hostOK_root hyp g hg
  | succ j ih =>
    intro c hs hc
    have hp := parentGroup_lt hc
    have hs' : 1 < groupSize B.x B.b j := lt_of_lt_of_le hs (groupSize_succ_le _ _ _)
    have h := hostOK_child hrouter hcore hyp hp hs (ih _ hs' hp)
      (Nat.mod_lt c branching_pos)
    rw [child_eq] at h
    exact h

end BuildParams

end MinCostFlow.HierPaths
