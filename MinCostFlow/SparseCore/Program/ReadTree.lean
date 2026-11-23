module

public import MinCostFlow.SparseCore.Program.ReadSpec

/-!
# The tree of the LSF view under updates: live and frozen parts

The tree `T` of the LSF view changes by deletions and vertex splits (`tViewUpdate`), matching
`CompLSFState.T`. Any edge of `T` not in `G` (if any were present in an initial view) stays in the
"frozen" part; deletions remove deleted edges from `T` and leave the frozen part unchanged. A split
lists the moved ends (tag `2`) or the kept ends (tag `3`) of the edges of `G` at the split vertex.
With tag `3`, every unlisted end moves, but a frozen end must stay. So the readout data keep three
graphs for `T`:

* `T` itself, for the readout;
* the live part `liveT G T`: the tree edges that are edges of `G`, with the ends of `G`. It is a
  subgraph of `G` with the vertices of `G`, so the library applies the batch to it in restricted
  mode;
* the frozen part `frozenT G T`: the tree edges that are not edges of `G`, with the ends of `T`.

This file proves how the three graphs change under one update (`liveT_step`, `frozenT_step_*`),
which lists a split of `T` may use (`split_tag2_cond`, `split_move_cond`, `split_keep_cond`), and
how the potential `treePot G T = Σ_x min(deg_live x, deg_frozen x)` changes
(`treePot_insert`, `treePot_delete_le`, `treePot_split`). A tag-`3` split of `T` costs at most the
kept ends plus `min(deg_live v', deg_frozen v)`, and the drop of the potential pays the second term
(`split_amortized`). Graphs are compared by `SameGraph` (same vertices, edges and ends on the
edges), which is all that a graph in memory (`DynGraphAt`) sees.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Graphs with the same vertices, edges and ends -/

/-- Two graphs have the same vertices, the same edges and the same ends on the edges. -/
def SameGraph (H K : MGraph) : Prop :=
  H.V = K.V ∧ H.E = K.E ∧ ∀ e ∈ H.E, H.tail e = K.tail e ∧ H.head e = K.head e

theorem SameGraph.refl (H : MGraph) : SameGraph H H := ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem SameGraph.symm {H K : MGraph} (h : SameGraph H K) : SameGraph K H :=
  ⟨h.1.symm, h.2.1.symm, fun e he => by
    obtain ⟨h1, h2⟩ := h.2.2 e (h.2.1 ▸ he); exact ⟨h1.symm, h2.symm⟩⟩

theorem SameGraph.trans {H K M : MGraph} (h₁ : SameGraph H K) (h₂ : SameGraph K M) :
    SameGraph H M :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun e he => by
    obtain ⟨a1, a2⟩ := h₁.2.2 e he
    obtain ⟨b1, b2⟩ := h₂.2.2 e (h₁.2.1 ▸ he)
    exact ⟨a1.trans b1, a2.trans b2⟩⟩

/-- A graph in memory is also every graph with the same vertices, edges and ends. -/
theorem DynGraphAt.of_same {mem : ℕ → ℕ} {a vCap eCap : ℕ} {H K : MGraph}
    (h : DynGraphAt mem a vCap eCap H) (hs : SameGraph H K) : DynGraphAt mem a vCap eCap K :=
  DynGraphAt.congr_ends hs.1 hs.2.1 hs.2.2 h

/-- The degree depends only on the edges and their ends. -/
theorem SameGraph.deg_eq {H K : MGraph} (h : SameGraph H K) (x : ℕ) : H.deg x = K.deg x := by
  unfold MGraph.deg
  rw [← h.2.1]
  congr 2
  · exact Finset.filter_congr fun e he => by rw [(h.2.2 e he).1]
  · exact Finset.filter_congr fun e he => by rw [(h.2.2 e he).2]

/-! ## The live and the frozen part of the tree -/

/-- The live part of the tree: the edges of `T` that are edges of `G`, with the ends of `G`, on
the vertices of `G`. -/
def liveT (G T : MGraph) : MGraph :=
  { V := G.V, E := T.E ∩ G.E, tail := G.tail, head := G.head }

/-- The frozen part of the tree: the edges of `T` that are not edges of `G`, with the ends of `T`,
on the vertices of `G`. -/
def frozenT (G T : MGraph) : MGraph :=
  { V := G.V, E := T.E \ G.E, tail := T.tail, head := T.head }

/-- The tree agrees with `G`: both are valid graphs on the same vertices, and an edge of both has
the same ends in both. -/
def TreeAgree (G T : MGraph) : Prop :=
  G.IsValid ∧ T.IsValid ∧ T.V = G.V ∧
    ∀ e ∈ T.E, e ∈ G.E → T.tail e = G.tail e ∧ T.head e = G.head e

/-- The live part is a subgraph of `G` with the vertices of `G`. -/
theorem liveT_sub (G T : MGraph) : G.IsSubgraph (liveT G T) ∧ (liveT G T).V = G.V :=
  ⟨⟨subset_refl _, Finset.inter_subset_right, fun _ _ => ⟨rfl, rfl⟩⟩, rfl⟩

/-- The live part is a valid graph. -/
theorem liveT_valid {G T : MGraph} (hG : G.IsValid) : (liveT G T).IsValid :=
  fun e he => hG e (Finset.mem_inter.mp he).2

/-- The frozen part is a valid graph. -/
theorem frozenT_valid {G T : MGraph} (h : TreeAgree G T) : (frozenT G T).IsValid := by
  intro e he
  have heT := (Finset.mem_sdiff.mp he).1
  obtain ⟨h1, h2⟩ := h.2.1 e heT
  exact ⟨h.2.2.1 ▸ h1, h.2.2.1 ▸ h2⟩

/-! ## One update -/

/-- The restricted update of the library applies the restricted batch. -/
theorem dgBatchTarget_zero (H : MGraph) (u : Update) :
    dgBatchTarget 0 H u = H.applyBatch (restrictUpdate u H) := by
  simp [dgBatchTarget]

/-- The tree still agrees with `G` after a valid update that does not insert a tree edge. -/
theorem treeAgree_step {G T : MGraph} {u : Update} (h : TreeAgree G T) (hu : G.UpdateIsValid u)
    (hins : ∀ e x z, u = .insert e x z → e ∉ T.E) :
    TreeAgree (G.applyUpdate u) (tViewUpdate T u) := by
  obtain ⟨hG, hT, hV, hends⟩ := h
  cases u with
  | insert e x z =>
    have heT := hins e x z rfl
    obtain ⟨heG, hx, hz⟩ := hu
    refine ⟨fun f hf => ?_, hT, hV, fun f hf hfG => ?_⟩
    · simp only [MGraph.applyUpdate] at hf ⊢
      rcases Finset.mem_insert.mp hf with rfl | hf
      · simp [hx, hz]
      · have hne : f ≠ e := fun h => heG (h ▸ hf)
        simp only [Function.update_of_ne hne]; exact hG f hf
    · have hne : f ≠ e := fun h => heT (h ▸ hf)
      simp only [tViewUpdate, MGraph.applyUpdate, Function.update_of_ne hne] at hfG ⊢
      exact hends f hf ((Finset.mem_insert.mp hfG).resolve_left hne)
  | delete e =>
    refine ⟨fun f hf => hG f (Finset.mem_of_mem_erase hf),
      fun f hf => hT f (Finset.mem_of_mem_erase hf), hV, fun f hf hfG => ?_⟩
    exact hends f (Finset.mem_of_mem_erase hf) (Finset.mem_of_mem_erase hfG)
  | split v v' St Sh =>
    obtain ⟨hv, hv', hS, _⟩ := hu
    refine ⟨fun f hf => ?_, fun f hf => ?_, ?_, fun f hf hfG => ?_⟩
    · simp only [MGraph.applyUpdate] at hf ⊢
      obtain ⟨h1, h2⟩ := hG f hf
      constructor <;> split_ifs <;> simp_all
    · simp only [tViewUpdate, MGraph.applyUpdate] at hf ⊢
      obtain ⟨h1, h2⟩ := hT f hf
      constructor <;> split_ifs <;> simp_all
    · simp [tViewUpdate, MGraph.applyUpdate, hV]
    · simp only [tViewUpdate, MGraph.applyUpdate] at hf hfG ⊢
      obtain ⟨h1, h2⟩ := hends f hf hfG
      rw [h1, h2]
      exact ⟨rfl, rfl⟩

/-- The live part follows the restricted update of the library (`dgBatchTarget 0`). -/
theorem liveT_step {G T : MGraph} {u : Update} (hins : ∀ e x z, u = .insert e x z → e ∉ T.E) :
    SameGraph (dgBatchTarget 0 (liveT G T) u)
      (liveT (G.applyUpdate u) (tViewUpdate T u)) := by
  cases u with
  | insert e x z =>
    have heT := hins e x z rfl
    refine ⟨rfl, ?_, fun f hf => ?_⟩
    · simp only [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, List.foldl_nil,
        liveT, tViewUpdate, MGraph.applyUpdate]
      ext f
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
      · rintro ⟨h1, rfl | h2⟩
        · exact absurd h1 heT
        · exact ⟨h1, h2⟩
    · simp only [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, List.foldl_nil,
        liveT] at hf ⊢
      have hne : f ≠ e := fun h => heT (h ▸ (Finset.mem_inter.mp hf).1)
      simp [MGraph.applyUpdate, Function.update_of_ne hne]
  | delete e =>
    have hE : (dgBatchTarget 0 (liveT G T) (.delete e)).E = (liveT G T).E.erase e := by
      simp only [dgBatchTarget_zero, restrictUpdate]
      split_ifs with he
      · simp [MGraph.applyBatch, MGraph.applyUpdate]
      · simp [MGraph.applyBatch, Finset.erase_eq_of_notMem he]
    have hO : ∀ f, (dgBatchTarget 0 (liveT G T) (.delete e)).tail f = G.tail f ∧
        (dgBatchTarget 0 (liveT G T) (.delete e)).head f = G.head f := by
      intro f
      simp only [dgBatchTarget_zero, restrictUpdate]
      split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, liveT]
    have hVv : (dgBatchTarget 0 (liveT G T) (.delete e)).V = G.V := by
      simp only [dgBatchTarget_zero, restrictUpdate]
      split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, liveT]
    refine ⟨hVv, ?_, fun f _ => ⟨(hO f).1, (hO f).2⟩⟩
    rw [hE]
    ext f
    simp [liveT, tViewUpdate, MGraph.applyUpdate, Finset.mem_erase]
    tauto
  | split v v' St Sh =>
    refine ⟨?_, ?_, fun f hf => ?_⟩
    · simp [dgBatchTarget, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate, liveT]
    · simp [dgBatchTarget, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate, liveT,
        tViewUpdate]
    · simp only [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch, List.foldl_cons,
        List.foldl_nil, MGraph.applyUpdate, liveT] at hf ⊢
      have hfE : f ∈ T.E ∩ G.E := hf
      simp only [Finset.mem_inter] at hfE ⊢
      constructor
      · by_cases h1 : f ∈ St ∧ G.tail f = v
        · simp [h1, hfE]
        · have : ¬ ((f ∈ St ∧ f ∈ T.E ∧ f ∈ G.E) ∧ G.tail f = v) := by tauto
          simp [h1, this]
      · by_cases h1 : f ∈ Sh ∧ G.head f = v
        · simp [h1, hfE]
        · have : ¬ ((f ∈ Sh ∧ f ∈ T.E ∧ f ∈ G.E) ∧ G.head f = v) := by tauto
          simp [h1, this]

/-- An insertion leaves the frozen part. -/
theorem frozenT_step_insert {G T : MGraph} {e x z : ℕ} (heT : e ∉ T.E) :
    SameGraph (frozenT G T) (frozenT (G.applyUpdate (.insert e x z))
      (tViewUpdate T (.insert e x z))) := by
  refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  ext f
  simp only [frozenT, tViewUpdate, MGraph.applyUpdate, Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h.elim (fun h => heT (h ▸ h1)) h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inr h)⟩

/-- Deleting an edge that is not a tree edge leaves the frozen part. -/
theorem frozenT_step_delete_not {G T : MGraph} {e : ℕ} (heT : e ∉ T.E) :
    SameGraph (frozenT G T) (frozenT (G.applyUpdate (.delete e)) (tViewUpdate T (.delete e))) := by
  refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  ext f
  simp only [frozenT, tViewUpdate, MGraph.applyUpdate, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨fun he => heT (he ▸ h1), h1⟩, fun h => h2 h.2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    refine ⟨h1, fun h => h2 ⟨fun he => heT (he ▸ h1), h⟩⟩

/-- Deleting an edge of `G` leaves the frozen part unchanged, because `tViewUpdate` deletes the
edge from `T` as well. -/
theorem frozenT_step_delete {G T : MGraph} {e : ℕ} (heG : e ∈ G.E) :
    SameGraph (frozenT G T) (frozenT (G.applyUpdate (.delete e)) (tViewUpdate T (.delete e))) := by
  refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  ext f
  simp only [frozenT, tViewUpdate, MGraph.applyUpdate, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    have hne : f ≠ e := fun h => h2 (h ▸ heG)
    exact ⟨⟨hne, h1⟩, fun h => h2 h.2⟩
  · rintro ⟨⟨hne, h1⟩, h2⟩
    exact ⟨h1, fun hfG => h2 ⟨hne, hfG⟩⟩

/-- A split adds the new vertex to the frozen part and moves none of its edges. -/
theorem frozenT_step_split {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (hu : G.UpdateIsValid (.split v v' St Sh)) :
    SameGraph { frozenT G T with V := insert v' (frozenT G T).V }
      (frozenT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))) := by
  obtain ⟨_, _, hS, _⟩ := hu
  refine ⟨rfl, rfl, fun f hf => ?_⟩
  have hfG : f ∉ G.E := (Finset.mem_sdiff.mp hf).2
  have hSt : f ∉ St := fun h => hfG (hS (Finset.mem_union_left _ h))
  have hSh : f ∉ Sh := fun h => hfG (hS (Finset.mem_union_right _ h))
  simp [frozenT, tViewUpdate, MGraph.applyUpdate, hSt, hSh]

/-- The split that the library applies to `T` (with the moved sets cut to the edges of `T`) is the
split of the model. -/
theorem tree_split_same (T : MGraph) (v v' : ℕ) (St Sh : Finset ℕ) :
    SameGraph (T.applyUpdate (.split v v' (St ∩ T.E) (Sh ∩ T.E)))
      (tViewUpdate T (.split v v' St Sh)) := by
  refine ⟨rfl, rfl, fun f hf => ?_⟩
  simp only [MGraph.applyUpdate, tViewUpdate, Finset.mem_inter] at hf ⊢
  simp [hf]

/-! ## The lists of a split of `T` -/

/-- With tag `2`, the moved lists of a split of `G` are also moved lists of the split of `T`. -/
theorem split_tag2_cond {G T : MGraph} {v v' : ℕ} {St : Finset ℕ} {Sh : Finset ℕ}
    (h : TreeAgree G T) (hu : G.UpdateIsValid (.split v v' St Sh)) {L : List ℕ}
    (hL : ∀ e, e ∈ L ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∈ St) :
    ∀ e ∈ T.E, e ∈ L ↔ T.tail e = v ∧ e ∈ St := by
  intro e heT
  obtain ⟨_, _, hS, _⟩ := hu
  rw [hL]
  by_cases heG : e ∈ G.E
  · rw [(h.2.2.2 e heT heG).1]; simp [heG]
  · have : e ∉ St := fun hs => heG (hS (Finset.mem_union_left _ hs))
    simp [heG, this]

/-- The same for the heads. -/
theorem split_tag2_cond_head {G T : MGraph} {v v' : ℕ} {St : Finset ℕ} {Sh : Finset ℕ}
    (h : TreeAgree G T) (hu : G.UpdateIsValid (.split v v' St Sh)) {L : List ℕ}
    (hL : ∀ e, e ∈ L ↔ e ∈ G.E ∧ G.head e = v ∧ e ∈ Sh) :
    ∀ e ∈ T.E, e ∈ L ↔ T.head e = v ∧ e ∈ Sh := by
  intro e heT
  obtain ⟨_, _, hS, _⟩ := hu
  rw [hL]
  by_cases heG : e ∈ G.E
  · rw [(h.2.2.2 e heT heG).2]; simp [heG]
  · have : e ∉ Sh := fun hs => heG (hS (Finset.mem_union_right _ hs))
    simp [heG, this]

/-- The ends at the new vertex `v'` of the live part after a split are moved lists of the split
of `T` (tails). -/
theorem split_move_cond {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (h : TreeAgree G T) (hu : G.UpdateIsValid (.split v v' St Sh)) {L : List ℕ}
    (hL : ∀ e, e ∈ L ↔ e ∈ (liveT (G.applyUpdate (.split v v' St Sh))
      (tViewUpdate T (.split v v' St Sh))).E ∧
      (liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))).tail e = v') :
    ∀ e ∈ T.E, e ∈ L ↔ T.tail e = v ∧ e ∈ St := by
  intro e heT
  obtain ⟨hv, hv', hS, _⟩ := hu
  rw [hL]
  simp only [liveT, tViewUpdate, MGraph.applyUpdate, Finset.mem_inter]
  by_cases heG : e ∈ G.E
  · have htv : G.tail e ≠ v' := fun h' => hv' (h' ▸ (h.1 e heG).1)
    rw [(h.2.2.2 e heT heG).1]
    by_cases hc : e ∈ St ∧ G.tail e = v
    · simp [hc, heT, heG]
    · simp only [hc, ite_false, htv, and_false]
      tauto
  · have : e ∉ St := fun hs => heG (hS (Finset.mem_union_left _ hs))
    simp [heG, this]

/-- The same for the heads. -/
theorem split_move_cond_head {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (h : TreeAgree G T) (hu : G.UpdateIsValid (.split v v' St Sh)) {L : List ℕ}
    (hL : ∀ e, e ∈ L ↔ e ∈ (liveT (G.applyUpdate (.split v v' St Sh))
      (tViewUpdate T (.split v v' St Sh))).E ∧
      (liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))).head e = v') :
    ∀ e ∈ T.E, e ∈ L ↔ T.head e = v ∧ e ∈ Sh := by
  intro e heT
  obtain ⟨hv, hv', hS, _⟩ := hu
  rw [hL]
  simp only [liveT, tViewUpdate, MGraph.applyUpdate, Finset.mem_inter]
  by_cases heG : e ∈ G.E
  · have htv : G.head e ≠ v' := fun h' => hv' (h' ▸ (h.1 e heG).2)
    rw [(h.2.2.2 e heT heG).2]
    by_cases hc : e ∈ Sh ∧ G.head e = v
    · simp [hc, heT, heG]
    · simp only [hc, ite_false, htv, and_false]
      tauto
  · have : e ∉ Sh := fun hs => heG (hS (Finset.mem_union_right _ hs))
    simp [heG, this]

/-- With tag `3`, the kept list of `G` followed by the frozen tails at `v` is a kept list of the
split of `T`. -/
theorem split_keep_cond {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (h : TreeAgree G T) (hu : G.UpdateIsValid (.split v v' St Sh)) {Lt Ft : List ℕ}
    (hL : ∀ e, e ∈ Lt ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∉ St)
    (hF : ∀ e, e ∈ Ft ↔ e ∈ (frozenT G T).E ∧ (frozenT G T).tail e = v) :
    ∀ e ∈ T.E, e ∈ Lt ++ Ft ↔ T.tail e = v ∧ e ∉ St := by
  intro e heT
  obtain ⟨_, _, hS, _⟩ := hu
  rw [List.mem_append, hL, hF]
  simp only [frozenT, Finset.mem_sdiff]
  by_cases heG : e ∈ G.E
  · rw [(h.2.2.2 e heT heG).1]; simp [heG]
  · have : e ∉ St := fun hs => heG (hS (Finset.mem_union_left _ hs))
    simp [heG, this, heT]

/-- The same for the heads. -/
theorem split_keep_cond_head {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (h : TreeAgree G T) (hu : G.UpdateIsValid (.split v v' St Sh)) {Lh Fh : List ℕ}
    (hL : ∀ e, e ∈ Lh ↔ e ∈ G.E ∧ G.head e = v ∧ e ∉ Sh)
    (hF : ∀ e, e ∈ Fh ↔ e ∈ (frozenT G T).E ∧ (frozenT G T).head e = v) :
    ∀ e ∈ T.E, e ∈ Lh ++ Fh ↔ T.head e = v ∧ e ∉ Sh := by
  intro e heT
  obtain ⟨_, _, hS, _⟩ := hu
  rw [List.mem_append, hL, hF]
  simp only [frozenT, Finset.mem_sdiff]
  by_cases heG : e ∈ G.E
  · rw [(h.2.2.2 e heT heG).2]; simp [heG]
  · have : e ∉ Sh := fun hs => heG (hS (Finset.mem_union_right _ hs))
    simp [heG, this, heT]

/-! ## Degrees -/

/-- The degree as a sum over the edges. -/
theorem deg_eq_sum (H : MGraph) (x : ℕ) :
    H.deg x = ∑ e ∈ H.E, ((if H.tail e = x then 1 else 0) + (if H.head e = x then 1 else 0)) := by
  unfold MGraph.deg
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]

/-- A split does not change the degree of a vertex other than the two halves. -/
theorem deg_split_other (H : MGraph) {v v' x : ℕ} (St Sh : Finset ℕ) (hx : x ≠ v)
    (hx' : x ≠ v') : (H.applyUpdate (.split v v' St Sh)).deg x = H.deg x := by
  rw [deg_eq_sum, deg_eq_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [MGraph.applyUpdate]
  split_ifs <;> simp_all

/-- A split keeps the sum of the degrees of the two halves. -/
theorem deg_split_pair (H : MGraph) {v v' : ℕ} (St Sh : Finset ℕ) (hvv : v ≠ v') :
    (H.applyUpdate (.split v v' St Sh)).deg v + (H.applyUpdate (.split v v' St Sh)).deg v' =
      H.deg v + H.deg v' := by
  rw [deg_eq_sum, deg_eq_sum, deg_eq_sum H v, deg_eq_sum H v', ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [MGraph.applyUpdate]
  split_ifs <;> simp_all

/-- A vertex that is not in a valid graph has degree `0`. -/
theorem deg_eq_zero_of_notMem {H : MGraph} (hH : H.IsValid) {x : ℕ} (hx : x ∉ H.V) :
    H.deg x = 0 := by
  rw [deg_eq_sum]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨h1, h2⟩ := hH e he
  have ht : H.tail e ≠ x := fun h => hx (h ▸ h1)
  have hh : H.head e ≠ x := fun h => hx (h ▸ h2)
  simp [ht, hh]

/-- Inserting a new edge adds its two ends to the degrees. -/
theorem deg_insert {H : MGraph} {e a b : ℕ} (he : e ∉ H.E) (x : ℕ) :
    (H.applyUpdate (.insert e a b)).deg x =
      H.deg x + ((if a = x then 1 else 0) + (if b = x then 1 else 0)) := by
  rw [deg_eq_sum, deg_eq_sum]
  simp only [MGraph.applyUpdate]
  rw [Finset.sum_insert he, add_comm]
  simp only [Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun f hf => ?_
  have hne : f ≠ e := fun h => he (h ▸ hf)
  simp only [Function.update_of_ne hne]

/-- Fewer edges with the same ends give a smaller degree. -/
theorem deg_le_of_subset {H K : MGraph} (hE : H.E ⊆ K.E) (ht : H.tail = K.tail)
    (hh : H.head = K.head) (x : ℕ) : H.deg x ≤ K.deg x := by
  unfold MGraph.deg
  rw [ht, hh]
  exact Nat.add_le_add (Finset.card_le_card (Finset.filter_subset_filter _ hE))
    (Finset.card_le_card (Finset.filter_subset_filter _ hE))

/-- A list of distinct elements with the members of a finite set has its size as length. -/
theorem length_eq_card_of_mem_iff {L : List ℕ} {S : Finset ℕ} (hnd : L.Nodup)
    (hL : ∀ e, e ∈ L ↔ e ∈ S) : L.length = S.card := by
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e
  simp [hL]

/-! ## The potential `Σ_x min(deg_live x, deg_frozen x)` -/

/-- The potential of the tree: the sum over the vertices of the smaller of the live and the
frozen degree. A tag-`3` split pays the smaller of the moved live ends and the frozen ends at the
split vertex from this potential. -/
def treePot (G T : MGraph) : ℕ :=
  ∑ x ∈ G.V, min ((liveT G T).deg x) ((frozenT G T).deg x)

/-- The potential depends only on the vertices of `G` and the two parts, up to `SameGraph`. -/
theorem treePot_congr {G T G' T' : MGraph} (hV : G'.V = G.V)
    (hl : SameGraph (liveT G T) (liveT G' T')) (hf : SameGraph (frozenT G T) (frozenT G' T')) :
    treePot G' T' = treePot G T := by
  unfold treePot
  rw [hV]
  exact Finset.sum_congr rfl fun x _ => by rw [hl.deg_eq, hf.deg_eq]

/-- An insertion keeps the potential. -/
theorem treePot_insert {G T : MGraph} {e x z : ℕ} (heT : e ∉ T.E) :
    treePot (G.applyUpdate (.insert e x z)) (tViewUpdate T (.insert e x z)) = treePot G T := by
  refine treePot_congr rfl ?_ (frozenT_step_insert heT)
  have h := liveT_step (u := .insert e x z) (G := G) (T := T)
    (fun e' x' z' hu => by cases hu; exact heT)
  simpa [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch] using h

/-- Deleting an edge that is not a tree edge keeps the potential. -/
theorem treePot_delete_not {G T : MGraph} {e : ℕ} (heT : e ∉ T.E) :
    treePot (G.applyUpdate (.delete e)) (tViewUpdate T (.delete e)) = treePot G T := by
  refine treePot_congr rfl ?_ (frozenT_step_delete_not heT)
  refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  ext f
  simp only [liveT, tViewUpdate, MGraph.applyUpdate, Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨fun h => heT (h ▸ h1), h1⟩, fun h => heT (h ▸ h1), h2⟩
  · rintro ⟨⟨_, h1⟩, _, h2⟩; exact ⟨h1, h2⟩

/-- Deleting an edge of `G` does not raise the potential. -/
theorem treePot_delete_le {G T : MGraph} {e : ℕ} (heG : e ∈ G.E) :
    treePot (G.applyUpdate (.delete e)) (tViewUpdate T (.delete e)) ≤ treePot G T := by
  have hf : ∀ x, (frozenT (G.applyUpdate (.delete e)) (tViewUpdate T (.delete e))).deg x =
      (frozenT G T).deg x := fun x => (frozenT_step_delete heG).deg_eq x |>.symm
  have hl : ∀ x, (liveT (G.applyUpdate (.delete e)) (tViewUpdate T (.delete e))).deg x ≤
      (liveT G T).deg x := fun x => by
    refine deg_le_of_subset
      (H := liveT (G.applyUpdate (.delete e)) (tViewUpdate T (.delete e))) (K := liveT G T)
      ?_ rfl rfl x
    intro f hf'
    have hf'' : f ∈ T.E.erase e ∩ G.E.erase e := hf'
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hf'').1,
       Finset.mem_of_mem_erase (Finset.mem_inter.mp hf'').2⟩
  unfold treePot
  refine Finset.sum_le_sum fun x _ => ?_
  rw [hf x]
  exact min_le_min_right _ (hl x)

/-- **A split and the potential.** With `K` and `M` the live degrees of `v` and `v'` after the
split and `F` the frozen degree of `v`, the potential after the split plus `min(K + M, F)` is the
potential before plus `min(K, F)`. -/
theorem treePot_split {G T : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (h : TreeAgree G T)
    (hu : G.UpdateIsValid (.split v v' St Sh)) :
    let G' := G.applyUpdate (.split v v' St Sh)
    let T' := tViewUpdate T (.split v v' St Sh)
    treePot G' T' + min ((liveT G' T').deg v + (liveT G' T').deg v') ((frozenT G T).deg v) =
      treePot G T + min ((liveT G' T').deg v) ((frozenT G T).deg v) := by
  intro G' T'
  obtain ⟨hv, hv', hS, _⟩ := hu
  have hvv : v ≠ v' := fun h' => hv' (h' ▸ hv)
  -- the live part after the split is the split of the live part
  have hl : SameGraph ((liveT G T).applyUpdate
      (.split v v' (St ∩ (liveT G T).E) (Sh ∩ (liveT G T).E))) (liveT G' T') := by
    have := liveT_step (G := G) (T := T) (u := .split v v' St Sh) (fun _ _ _ h => by cases h)
    simpa [dgBatchTarget_zero, restrictUpdate, MGraph.applyBatch] using this
  have hfr : SameGraph { frozenT G T with V := insert v' (frozenT G T).V } (frozenT G' T') :=
    frozenT_step_split ⟨hv, hv', hS, by assumption⟩
  have hdl : ∀ x, x ≠ v → x ≠ v' → (liveT G' T').deg x = (liveT G T).deg x := fun x h1 h2 =>
    (hl.deg_eq x).symm.trans (deg_split_other _ _ _ h1 h2)
  have hdl0 : (liveT G T).deg v' = 0 := deg_eq_zero_of_notMem (liveT_valid h.1) hv'
  have hpair : (liveT G' T').deg v + (liveT G' T').deg v' = (liveT G T).deg v := by
    rw [← hl.deg_eq, ← hl.deg_eq, deg_split_pair _ _ _ hvv, hdl0, Nat.add_zero]
  have hdf : ∀ x, (frozenT G' T').deg x = (frozenT G T).deg x := fun x =>
    (hfr.deg_eq x).symm.trans (by unfold MGraph.deg; rfl)
  have hdf0 : (frozenT G T).deg v' = 0 :=
    deg_eq_zero_of_notMem (frozenT_valid h) (by simpa [frozenT] using hv')
  have hV' : G'.V = insert v' G.V := rfl
  unfold treePot
  rw [hV', Finset.sum_insert hv', hdf v', hdf0, Nat.min_zero, Nat.zero_add,
    ← Finset.add_sum_erase _ _ hv, ← Finset.add_sum_erase _ _ hv, hdf v, hpair]
  have hrest : ∑ x ∈ G.V.erase v, min ((liveT G' T').deg x) ((frozenT G' T').deg x) =
      ∑ x ∈ G.V.erase v, min ((liveT G T).deg x) ((frozenT G T).deg x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    have hxv' : x ≠ v' := fun h' => hv' (h' ▸ Finset.mem_of_mem_erase hx)
    rw [hdl x hxv hxv', hdf x]
  rw [hrest]
  omega

/-- **The cost of a tag-`3` split of `T` is paid.** The kept live ends `K`, the smaller of the
moved live ends `M` and the frozen ends `F`: `min(M, F) + min(K, F) ≤ K + min(K + M, F)`. -/
theorem split_amortized (K M F : ℕ) : min M F + min K F ≤ K + min (K + M) F := by omega

/-- The potential is at most twice the number of tree edges. -/
theorem treePot_le {G T : MGraph} (hG : G.IsValid) : treePot G T ≤ 2 * T.E.card := by
  unfold treePot
  calc ∑ x ∈ G.V, min ((liveT G T).deg x) ((frozenT G T).deg x)
      ≤ ∑ x ∈ G.V, (liveT G T).deg x := Finset.sum_le_sum fun x _ => Nat.min_le_left _ _
    _ = 2 * (liveT G T).m := sum_deg_eq_two_mul_m (liveT_valid hG)
    _ ≤ 2 * T.E.card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card Finset.inter_subset_left)

end MinCostFlow.SparseCore.Program.Read
