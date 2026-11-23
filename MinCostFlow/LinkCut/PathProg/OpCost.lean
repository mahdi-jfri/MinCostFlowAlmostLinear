module

public import MinCostFlow.LinkCut.PathProg.ExposeCost
public import MinCostFlow.LinkCut.Gen.Cut
public import MinCostFlow.LinkCut.ForestModelSplice
public import MinCostFlow.LinkCut.PathTree.AccOps

/-!
# The cost of the tree operations against the model's counts

Each tree operation of `LinkCut/Gen` costs at most `opRate S` per unit that the model counts:
half rotations, splices, and one more. Reroot, link and the path operations are made of exposes,
so their bounds follow from `exposeCost_le`. A cut also splays the slot it removes, but only in a
tree of three nodes (`cutSplayCost_le`), so that splay costs a constant.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen SplayState

variable {α σ τ : Type*}

/-- The cost of one counted unit of a tree operation. -/
def opRate {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : ℕ :=
  2 * exposeRate S + 2 * S.cost + singleCost S + pushDownCost S + 2 * splayRate S + 2000

section Bounds

variable {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
  {ok : PayloadOk α σ τ}

theorem lctExposeCost_iters_pos (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    1 ≤ (lctExposeCost P st v).2.2 := by
  show 1 ≤ 1 + _
  omega

/-- An expose costs at most `2 * exposeRate S` per counted unit; the splices count at least one. -/
theorem exposeCost_le' (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {v : ℕ} (hv : v ∈ trees.flatMap AuxTree.toList) :
    exposeCost S st v ≤
      2 * exposeRate S * ((lctExposeCost P st v).2.1 + (lctExposeCost P st v).2.2) := by
  have h1 := exposeCost_le hL S W hv
  have h2 := lctExposeCost_iters_pos P st v
  generalize (lctExposeCost P st v).2.1 = a at h1 ⊢
  generalize (lctExposeCost P st v).2.2 = b at h1 h2 ⊢
  nlinarith

/-- A reroot costs at most `opRate S` per counted unit. -/
theorem rerootCost_le (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {v : ℕ} (hv : v ∈ trees.flatMap AuxTree.toList) :
    rerootCost S st v ≤
      opRate S * ((lctRerootCost P st v).2.1 + (lctRerootCost P st v).2.2) := by
  have h1 := exposeCost_le' hL S W hv
  have h2 := lctExposeCost_iters_pos P st v
  change exposeCost S st v + S.cost + 100 ≤
    opRate S * ((lctExposeCost P st v).2.1 + (lctExposeCost P st v).2.2)
  unfold opRate
  generalize (lctExposeCost P st v).2.1 = a at h1 ⊢
  generalize (lctExposeCost P st v).2.2 = b at h1 h2 ⊢
  generalize exposeCost S st v = e at h1 ⊢
  generalize exposeRate S = r at h1 ⊢
  generalize S.cost = c
  generalize singleCost S = s
  generalize pushDownCost S = q
  generalize splayRate S = t
  nlinarith

/-- A reroot at a vertex followed by an expose at a vertex costs at most `opRate S` per unit
that `lctPathSummaryCost` counts. -/
theorem rerootExposeCost_le (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {u v : ℕ} (hu : isVertex st.n u) (hv : isVertex st.n v) :
    rerootExposeCost S st u v ≤
      opRate S * ((lctPathSummaryCost P st u v).2.2.1 + (lctPathSummaryCost P st u v).2.2.2) := by
  have hu_act := isVertex_mem_active W hu
  obtain ⟨tu, htu, hut⟩ := List.mem_flatMap.mp hu_act
  obtain ⟨trees1, Lu, depth1, -, hW1, hact1, -⟩ := lctReroot_spec hL W htu hut hu
  have hv1 : v ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (isVertex_mem_active W hv)
  have h1 := rerootCost_le hL S W hu_act
  have h2 := exposeCost_le' hL S hW1 hv1
  have h3 := lctExposeCost_iters_pos P (lctRerootCost P st u).1 v
  change rerootCost S st u + exposeCost S (lctRerootCost P st u).1 v + 100 ≤
    opRate S * (((lctRerootCost P st u).2.1 + (lctExposeCost P (lctRerootCost P st u).1 v).2.1) +
      ((lctRerootCost P st u).2.2 + (lctExposeCost P (lctRerootCost P st u).1 v).2.2))
  generalize (lctExposeCost P (lctRerootCost P st u).1 v).2.1 = a at h2 ⊢
  generalize (lctExposeCost P (lctRerootCost P st u).1 v).2.2 = b at h2 h3 ⊢
  generalize exposeCost S (lctRerootCost P st u).1 v = e at h2 ⊢
  generalize rerootCost S st u = r at h1 ⊢
  unfold opRate at h1 ⊢
  generalize exposeRate S = x at h1 h2 ⊢
  generalize S.cost = c at h1 ⊢
  generalize singleCost S = s at h1 ⊢
  generalize pushDownCost S = q at h1 ⊢
  generalize splayRate S = t at h1 ⊢
  nlinarith

/-- A link of two vertices that are not connected costs at most `opRate S` per counted unit,
plus `opRate S`. -/
theorem linkCost_le (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {u v : ℕ} (hu : isVertex st.n u) (hv : isVertex st.n v)
    (huv : u ≠ v) (hf : st.freeHead ≠ 0) (e : α) :
    linkCost S st u v ≤
      opRate S * ((lctLinkCost P st u v e).2.1 + (lctLinkCost P st u v e).2.2 + 1) := by
  have hv_act := isVertex_mem_active W hv
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv_act
  obtain ⟨trees1, Lv, depth1, -, hW1, hact1, -⟩ := lctReroot_spec hL W htv hvt hv
  have hu1 : u ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (isVertex_mem_active W hu)
  have h1 := rerootCost_le hL S W hv_act
  have h2 := rerootCost_le hL S hW1 hu1
  have hfh : (lctRerootCost P (lctRerootCost P st v).1 u).1.freeHead = st.freeHead := by
    rw [lctRerootCost_freeHead, lctRerootCost_freeHead]
  have hcost : (lctLinkCost P st u v e).2.1 =
        (lctRerootCost P st v).2.1 + (lctRerootCost P (lctRerootCost P st v).1 u).2.1 ∧
      (lctLinkCost P st u v e).2.2 =
        (lctRerootCost P st v).2.2 + (lctRerootCost P (lctRerootCost P st v).1 u).2.2 + 1 := by
    have hu0 := isVertex_ne_zero hu
    have hv0 := isVertex_ne_zero hv
    unfold lctLinkCost
    rw [ite_eq_right (by simp [hu0, hv0, huv, hf])]
    simp only [hfh, beq_iff_eq, hf, ite_false]
    exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩
  rw [hcost.1, hcost.2]
  unfold linkCost
  generalize rerootCost S st v = r1 at h1 ⊢
  change rerootCost S (lctReroot P st v) u ≤ _ at h2
  generalize rerootCost S (lctReroot P st v) u = r2 at h2 ⊢
  unfold opRate at h1 h2 ⊢
  generalize singleCost S = s at h1 h2 ⊢
  generalize (lctRerootCost P st v).2.1 = a1 at h1 ⊢
  generalize (lctRerootCost P st v).2.2 = b1 at h1 ⊢
  generalize (lctRerootCost P (lctRerootCost P st v).1 u).2.1 = a2 at h2 ⊢
  generalize (lctRerootCost P (lctRerootCost P st v).1 u).2.2 = b2 at h2 ⊢
  generalize exposeRate S = x at h1 h2 ⊢
  generalize S.cost = c at h1 h2 ⊢
  generalize pushDownCost S = q at h1 h2 ⊢
  generalize splayRate S = t at h1 h2 ⊢
  nlinarith

end Bounds

end MinCostFlow.LinkCut.PathProg

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen SplayState

variable {α σ τ : Type*}

section Cut

variable {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
  {ok : PayloadOk α σ τ}

/-- A cut that passes its guard counts at least the units of its reroot and expose. -/
theorem lctCutCost_ge {st : LctState α σ τ} {u v : ℕ}
    (hg : ¬ (u = 0 ∨ v = 0 ∨ u = v ∨ st.n < u ∨ st.n < v)) :
    (lctPathSummaryCost P st u v).2.2.1 ≤ (lctCutCost P st u v).2.1 ∧
      (lctPathSummaryCost P st u v).2.2.2 ≤ (lctCutCost P st u v).2.2 := by
  unfold lctCutCost
  rw [ite_eq_right (by simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]; tauto)]
  dsimp only
  split_ifs <;> exact ⟨by dsimp only [lctPathSummaryCost]; omega,
    by dsimp only [lctPathSummaryCost]; omega⟩

/-- When a cut splays its slot, the slot lies in a tree of three nodes, so the splay costs at
most `2 * splayRate S`. -/
theorem cutSplayCost_le (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {u v : ℕ} (hu : isVertex st.n u) (hv : isVertex st.n v) :
    cutSplayCost S st u v ≤ 2 * splayRate S := by
  unfold cutSplayCost
  split_ifs with hc
  swap
  · omega
  obtain ⟨hsz, -⟩ := hc
  have hu_act := isVertex_mem_active W hu
  obtain ⟨tu, htu, hut⟩ := List.mem_flatMap.mp hu_act
  obtain ⟨trees1, Lu, depth1, -, hW1, hact1, -⟩ := lctReroot_spec hL W htu hut hu
  have hv1 : v ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (isVertex_mem_active W hv)
  obtain ⟨tv1, htv1, hvt1⟩ := List.mem_flatMap.mp hv1
  obtain ⟨trees2, Lv, ht2, hW2, -, -, -, -, -, hrev2, -⟩ := lctExpose_spec hL hW1 htv1 hvt1
  have hmid : (lctExposeCost P (lctRerootCost P st u).1 v).1 = cutMid P st u v := rfl
  rw [hmid] at hW2 hrev2
  have ht2_inv := hW2.treesInv _ ht2
  have hsz_v : ((cutMid P st u v).splay.nodes v).sz = 1 + Lv.countNodes := by
    have h := ht2_inv.sub.2.2.2.2.2.1
    simpa [AuxTree.countNodes] using h
  have hLv : Lv ≠ .leaf := by
    rintro rfl; simp [AuxTree.countNodes] at hsz_v; omega
  have hl0 : cutL0 P st u v = Lv.rootId := by
    have h := ht2_inv.sub.2.1
    show ((cutMid P st u v).splay.nodes v).left = _
    simpa [hrev2] using h
  have hl0_mem : cutL0 P st u v ∈ (AuxTree.node v Lv .leaf).toList := by
    rw [hl0]; simp [AuxTree.toList, AuxTree.rootId_mem hLv]
  obtain ⟨hpd, hperm, -⟩ := pushDown_preserves_TreeInv hL ht2_inv hl0_mem
  change TreeInv P (cutPd P st u v) _ at hpd
  generalize pushDownTree (cutMid P st u v).splay (cutL0 P st u v) (AuxTree.node v Lv .leaf) = t
    at hpd hperm
  have hl0_t : cutL0 P st u v ∈ t.toList := hperm.symm.mem_iff.mp hl0_mem
  have hne : cutNe P st u v ∈ t.toList := by
    unfold cutNe
    split_ifs with hr
    · exact hl0_t
    · exact (SubtreeInv.child_mem hpd.sub hl0_t).2 hr
  have hcnt : t.countNodes = 3 := by
    rw [← AuxTree.length_toList, hperm.length_eq, AuxTree.length_toList]
    simp only [AuxTree.countNodes] at hsz_v ⊢
    omega
  have hdep := depthOf_lt_countNodes hne
  have hn1 := hu.2
  have hu1 := hu.1
  have hf : t.depthOf (cutNe P st u v) < 2 * st.n + 1 := by omega
  have h := splayCost_le hL S hpd hne hf
  rw [splayDepth_eq_depthOf hpd hne hf] at h
  have h2 : t.depthOf (cutNe P st u v) / 2 + 1 ≤ 2 := by omega
  calc _ ≤ _ := h
    _ ≤ 2 * splayRate S := Nat.mul_le_mul_right (splayRate S) h2

/-- A cut of two vertices costs at most `opRate S` per counted unit, plus `opRate S`. -/
theorem cutCost_le (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {u v : ℕ} (hu : isVertex st.n u) (hv : isVertex st.n v) :
    cutCost S st u v ≤
      opRate S * ((lctCutCost P st u v).2.1 + (lctCutCost P st u v).2.2 + 1) := by
  have hR : 1000 ≤ opRate S := by unfold opRate; omega
  unfold cutCost
  split_ifs with hg
  · calc 1000 ≤ opRate S * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have h1 := rerootExposeCost_le hL S W hu hv
  have h2 := cutSplayCost_le hL S W hu hv
  have h3 := lctCutCost_ge (P := P) hg
  generalize rerootExposeCost S st u v = r at h1 ⊢
  generalize cutSplayCost S st u v = cs at h2 ⊢
  generalize (lctPathSummaryCost P st u v).2.2.1 = a at h1 h3
  generalize (lctPathSummaryCost P st u v).2.2.2 = b at h1 h3
  generalize (lctCutCost P st u v).2.1 = a' at h3 ⊢
  generalize (lctCutCost P st u v).2.2 = b' at h3 ⊢
  obtain ⟨h3a, h3b⟩ := h3
  have h4 : opRate S * (a + b) ≤ opRate S * (a' + b') := Nat.mul_le_mul_left _ (by omega)
  have h5 : pushDownCost S + cs + S.cost + 1000 ≤ opRate S := by unfold opRate; omega
  rw [Nat.mul_add (opRate S) (a' + b') 1]
  omega

end Cut

end MinCostFlow.LinkCut.PathProg
