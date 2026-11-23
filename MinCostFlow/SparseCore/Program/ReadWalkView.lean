module

public import MinCostFlow.SparseCore.Program.ReadRep
public import MinCostFlow.SparseCore.Program.ReadTree

/-!
# The data after one update of the input batch

The update of the readout data walks over the input batch `U` and applies each update `u` to the
parts of the data that follow `U`: the graph `G`, the tree `T` (`tViewUpdate`), the forest `F`
(restricted, `dgBatchTarget 0`), the stretches and the pairs. `walkView v u` is the data after
this one update. After the whole batch, the walk gives the parts of `v.step U c U_S` that do not
depend on the change record `c` and on `U_S` (`walkView_fold`).

The file then proves what one update keeps and what it costs in potential.
* `walkView_agree`: the tree still agrees with `G`, and `ReadKeep` still holds.
* `walkView_pot_insert`, `walkView_pot_delete`: an insertion keeps the potential `treePot`, and a
  deletion raises it by at most `2`.
* `walkView_pot_split`: for a split encoded in `len` words, `800 · min(M, F)` plus `1000` times the
  new potential is at most `1000 · len` plus `1000` times the old potential. Here `M` is the live
  degree of the new vertex after the split and `F` the frozen degree of the split vertex. So the
  potential pays the split of `T` (`splitT_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- The data after one update `u` of the input batch: `G`, `T`, `F` (restricted), the stretches
and the pairs follow `u`. The roots and `S` stay. -/
noncomputable def walkView (v : ReadView) (u : Update) : ReadView :=
  { G := v.G.applyUpdate u
    lsf := { T := tViewUpdate v.lsf.T u
             F := { F := dgBatchTarget 0 v.lsf.F.F u, R := v.lsf.F.R }
             wstr := wstrViewUpdate v.lsf.wstr u }
    S := v.S
    num := pairViewUpdate v.num u
    den := pairViewUpdate v.den u }

/-- The walk over a batch gives the parts of the data that follow the batch. -/
theorem walkView_fold (U : List Update) (v : ReadView) :
    (U.foldl walkView v).G = v.G.applyBatch U ∧
    (U.foldl walkView v).lsf.T = U.foldl tViewUpdate v.lsf.T ∧
    (U.foldl walkView v).lsf.F.F = U.foldl (dgBatchTarget 0) v.lsf.F.F ∧
    (U.foldl walkView v).lsf.F.R = v.lsf.F.R ∧
    (U.foldl walkView v).lsf.wstr = U.foldl wstrViewUpdate v.lsf.wstr ∧
    (U.foldl walkView v).S = v.S ∧
    (U.foldl walkView v).num = U.foldl pairViewUpdate v.num ∧
    (U.foldl walkView v).den = U.foldl pairViewUpdate v.den := by
  induction U generalizing v with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons u U ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih (walkView v u)
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- An update never adds edges to the tree. -/
theorem tViewUpdate_E_subset (T : MGraph) (u : Update) : (tViewUpdate T u).E ⊆ T.E := by
  cases u with
  | insert _ _ _ => exact Finset.Subset.rfl
  | delete e => exact Finset.erase_subset e T.E
  | split _ _ _ _ => exact Finset.Subset.rfl

/-- One update keeps the tree in agreement with `G` and keeps `ReadKeep`, if it is valid and does
not insert an edge of the tree. -/
theorem walkView_agree {v : ReadView} {u : Update} (hag : TreeAgree v.G v.lsf.T)
    (hk : ReadKeep v) (hu : v.G.UpdateIsValid u)
    (hins : ∀ e x z, u = .insert e x z → e ∉ v.lsf.T.E) :
    TreeAgree (walkView v u).G (walkView v u).lsf.T ∧ ReadKeep (walkView v u) := by
  have hag' := treeAgree_step hag hu hins
  have hF := dgBatchTarget_preserves_subgraph hu hk.2.2.2 hk.2.2.1
  refine ⟨hag', hag'.2.2.1, hag'.2.2.2, ?_, ?_⟩
  · show (dgBatchTarget 0 v.lsf.F.F u).V = (v.G.applyUpdate u).V
    rw [dgBatchTarget_zero]; exact hF.2
  · show (v.G.applyUpdate u).IsSubgraph (dgBatchTarget 0 v.lsf.F.F u)
    rw [dgBatchTarget_zero]; exact hF.1

/-! ## The potential -/

/-- An insertion of an edge that is not a tree edge keeps the potential. -/
theorem walkView_pot_insert {v : ReadView} {e x z : ℕ} (heT : e ∉ v.lsf.T.E) :
    treePot (walkView v (.insert e x z)).G (walkView v (.insert e x z)).lsf.T =
      treePot v.G v.lsf.T :=
  treePot_insert heT

/-- A deletion of an edge of `G` does not raise the potential (and hence raises it by at most `2`). -/
theorem walkView_pot_delete {v : ReadView} {e : ℕ} (heG : e ∈ v.G.E) :
    treePot (walkView v (.delete e)).G (walkView v (.delete e)).lsf.T ≤
      treePot v.G v.lsf.T + 2 :=
  (treePot_delete_le heG).trans (Nat.le_add_right _ _)

/-- After a split of a valid graph, the edges with tail at the new vertex are the moved tails. -/
theorem split_tail_new {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (hG : G.IsValid)
    (hv' : v' ∉ G.V) (e : ℕ) :
    (e ∈ (G.applyUpdate (.split v v' St Sh)).E ∧
      (G.applyUpdate (.split v v' St Sh)).tail e = v') ↔ (e ∈ G.E ∧ G.tail e = v ∧ e ∈ St) := by
  simp only [MGraph.applyUpdate]
  constructor
  · rintro ⟨he, h⟩
    split_ifs at h with hc
    · exact ⟨he, hc.2, hc.1⟩
    · exact absurd (h ▸ (hG e he).1) hv'
  · rintro ⟨he, h1, h2⟩
    exact ⟨he, by simp [h1, h2]⟩

/-- After a split of a valid graph, the edges with head at the new vertex are the moved heads. -/
theorem split_head_new {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (hG : G.IsValid)
    (hv' : v' ∉ G.V) (e : ℕ) :
    (e ∈ (G.applyUpdate (.split v v' St Sh)).E ∧
      (G.applyUpdate (.split v v' St Sh)).head e = v') ↔ (e ∈ G.E ∧ G.head e = v ∧ e ∈ Sh) := by
  simp only [MGraph.applyUpdate]
  constructor
  · rintro ⟨he, h⟩
    split_ifs at h with hc
    · exact ⟨he, hc.2, hc.1⟩
    · exact absurd (h ▸ (hG e he).2) hv'
  · rintro ⟨he, h1, h2⟩
    exact ⟨he, by simp [h1, h2]⟩

/-- After a split, the edges with tail at the split vertex are the kept tails. -/
theorem split_tail_old {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (hvv : v ≠ v') (e : ℕ) :
    (e ∈ (G.applyUpdate (.split v v' St Sh)).E ∧
      (G.applyUpdate (.split v v' St Sh)).tail e = v) ↔ (e ∈ G.E ∧ G.tail e = v ∧ e ∉ St) := by
  simp only [MGraph.applyUpdate]
  constructor
  · rintro ⟨he, h⟩
    split_ifs at h with hc
    · exact absurd h.symm hvv
    · exact ⟨he, h, fun hS => hc ⟨hS, h⟩⟩
  · rintro ⟨he, h1, h2⟩
    exact ⟨he, by simp [h1, h2]⟩

/-- After a split, the edges with head at the split vertex are the kept heads. -/
theorem split_head_old {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (hvv : v ≠ v') (e : ℕ) :
    (e ∈ (G.applyUpdate (.split v v' St Sh)).E ∧
      (G.applyUpdate (.split v v' St Sh)).head e = v) ↔ (e ∈ G.E ∧ G.head e = v ∧ e ∉ Sh) := by
  simp only [MGraph.applyUpdate]
  constructor
  · rintro ⟨he, h⟩
    split_ifs at h with hc
    · exact absurd h.symm hvv
    · exact ⟨he, h, fun hS => hc ⟨hS, h⟩⟩
  · rintro ⟨he, h1, h2⟩
    exact ⟨he, by simp [h1, h2]⟩

/-- If two lists without repeats list the edges with tail and with head at `x`, the degree of `x`
is the sum of their lengths. -/
theorem deg_eq_of_lists {H : MGraph} {x : ℕ} {Lt Lh : List ℕ} (ht : Lt.Nodup) (hh : Lh.Nodup)
    (hLt : ∀ e, e ∈ Lt ↔ e ∈ H.E ∧ H.tail e = x) (hLh : ∀ e, e ∈ Lh ↔ e ∈ H.E ∧ H.head e = x) :
    H.deg x = Lt.length + Lh.length := by
  unfold MGraph.deg
  rw [length_eq_card_of_mem_iff ht (S := H.E.filter fun e => H.tail e = x)
      (fun e => by rw [hLt, Finset.mem_filter]),
    length_eq_card_of_mem_iff hh (S := H.E.filter fun e => H.head e = x)
      (fun e => by rw [hLh, Finset.mem_filter])]

/-- The live part has at most the degree of `G`. -/
theorem liveT_deg_le (G T : MGraph) (x : ℕ) : (liveT G T).deg x ≤ G.deg x :=
  deg_le_of_subset (H := liveT G T) (K := G) Finset.inter_subset_right rfl rfl x

/-- **A split and the potential.** For a split encoded in `len` words, with `M` the live degree of
the new vertex after the split and `F` the frozen degree of the split vertex,
`800 · min(M, F) + 1000 · φ' ≤ 1000 · len + 1000 · φ`. With tag `2`, the moved ends are listed,
so `M ≤ len`, and the potential does not rise. With tag `3`, the kept ends are listed, so the kept
live degree `K` is at most `len`, and `split_amortized` gives the bound. -/
theorem walkView_pot_split {mem : ℕ → ℕ} {a len : ℕ} {G T : MGraph} {v v' : ℕ}
    {St Sh : Finset ℕ} (hag : TreeAgree G T) (hu : G.UpdateIsValid (.split v v' St Sh))
    (hU : UpdateAt mem a G (.split v v' St Sh) len) :
    800 * min ((liveT (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh))).deg
        v') ((frozenT G T).deg v) +
      1000 * treePot (G.applyUpdate (.split v v' St Sh)) (tViewUpdate T (.split v v' St Sh)) ≤
      1000 * len + 1000 * treePot G T := by
  have hpot := treePot_split hag hu
  obtain ⟨hvG, hv'G, _, _⟩ := hu
  have hvv : v ≠ v' := fun h => hv'G (h ▸ hvG)
  simp only at hpot
  set G' := G.applyUpdate (.split v v' St Sh)
  set T' := tViewUpdate T (.split v v' St Sh)
  rcases hU with ⟨Lt, Lh, hLtnd, hLhnd, hLtm, hLhm, rfl, -⟩ | ⟨Lt, Lh, hLtnd, hLhnd, hLtm, hLhm,
    rfl, -⟩
  · have hdeg : G'.deg v' = Lt.length + Lh.length := deg_eq_of_lists hLtnd hLhnd
      (fun e => by rw [hLtm, split_tail_new hag.1 hv'G])
      (fun e => by rw [hLhm, split_head_new hag.1 hv'G])
    have hM := liveT_deg_le G' T' v'
    omega
  · have hdeg : G'.deg v = Lt.length + Lh.length := deg_eq_of_lists hLtnd hLhnd
      (fun e => by rw [hLtm, split_tail_old hvv])
      (fun e => by rw [hLhm, split_head_old hvv])
    have hK := liveT_deg_le G' T' v
    have ham := split_amortized ((liveT G' T').deg v) ((liveT G' T').deg v') ((frozenT G T).deg v)
    omega

end MinCostFlow.SparseCore.Program.Read
