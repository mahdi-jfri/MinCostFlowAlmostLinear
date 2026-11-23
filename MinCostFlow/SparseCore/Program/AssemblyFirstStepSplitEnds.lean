module

public import MinCostFlow.SparseCore.BundleCompStep
public import MinCostFlow.SparseCore.Program.AssemblyUpdateOutAux

import MinCostFlow.Bundle.SplitValid
import MinCostFlow.SparseCore.BundleRunsFacts
import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Tactic

/-!
# The splits of the bundle step name live ends at the split vertex (`AssemblyFirstStepSplitEnds`)

A bucket spanner reads its batch from memory (`decodeBatch`). A split `split v v' St Sh` is
stored as the lists of the tails in `St` and the heads in `Sh` that lie at `v`, so the batch read
back is the batch of the step only if every edge of `St` has its tail at `v` and every edge of
`Sh` has its head at `v` when the split comes (`BatchSplitEndsExact`). This file proves that the
bundle step `bundleCompStep` of a component has this property on the bundle graph
(`bundleCompStep_splitEndsExact`).

The batch of the canonical step `bundleRunsStep` first deletes edges, then, bundle by bundle,
splits off the runs of the bundle after the first one (`bundleRunUpdates`). A run is a list of
ends of its bundle, and the runs of one bundle have no end in common (`bundleRunsOf_nodup`). A
split moves only the ends of its own run. So when a run is split off, its ends still lie at the
old bundle vertex: the earlier runs of the same bundle hold other ends, and the splits of the
other bundles move only ends at other vertices. This is the same argument as the validity of the
batch (`bundleRunUpdates_valid`), with the side of each end kept apart.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner

/-- An edge is in the set of tails (or heads) of a run exactly when its end of that side is in
the run. -/
private theorem mem_runSide_iff (e : ℕ) (side : Bool) (run : List End) :
    e ∈ ((run.filter fun x => x.2 == side).map Prod.fst).toFinset ↔ (e, side) ∈ run := by
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨f, b⟩, ⟨hm, hb⟩, hf⟩
    simp only at hb hf
    simpa only [hb, hf] using hm
  · intro h
    exact ⟨(e, side), ⟨h, rfl⟩, rfl⟩

private theorem mem_runTails_iff (e : ℕ) (run : List End) :
    e ∈ ((run.filter Prod.snd).map Prod.fst).toFinset ↔ (e, true) ∈ run := by
  have h := mem_runSide_iff e true run
  simp only [beq_true] at h
  exact h

private theorem mem_runHeads_iff (e : ℕ) (run : List End) :
    e ∈ ((run.filter fun x => !x.2).map Prod.fst).toFinset ↔ (e, false) ∈ run := by
  have h := mem_runSide_iff e false run
  simp only [beq_false] at h
  exact h

/-- **The splits of the runs of one bundle.** If the runs have no end in common and every end of
a run is an end at `b` of an edge of `C`, then each split names only tails and heads at `b`. -/
private theorem runSplits_splitEndsExact (b : ℕ) :
    ∀ (runs : List (List End)) (C : MGraph) (next : ℕ), runs.flatten.Nodup →
      (∀ x ∈ runs.flatten, x.1 ∈ C.E ∧ C.src x = b) →
      BatchSplitEndsExact C ((runs.zipIdx next).map fun (run, fresh) =>
        Update.split b fresh ((run.filter Prod.snd).map Prod.fst).toFinset
          ((run.filter fun x => !x.2).map Prod.fst).toFinset)
  | [], _, _, _, _ => trivial
  | run :: runs, C, next, hn, hEnds => by
    rw [List.flatten_cons, List.nodup_append] at hn
    simp only [List.zipIdx_cons, List.map_cons]
    refine ⟨fun e he => ?_, fun e he => ?_, ?_⟩
    · have h := hEnds (e, true) (List.mem_append_left _ ((mem_runTails_iff e run).mp he))
      exact ⟨h.1, h.2⟩
    · have h := hEnds (e, false) (List.mem_append_left _ ((mem_runHeads_iff e run).mp he))
      exact ⟨h.1, h.2⟩
    · refine runSplits_splitEndsExact b runs _ (next + 1) hn.2.1 fun x hx => ?_
      have hx₀ := hEnds x (List.mem_append_right _ hx)
      have hnx : x ∉ run := fun h => hn.2.2 x h x hx rfl
      obtain ⟨e, side⟩ := x
      refine ⟨hx₀.1, ?_⟩
      cases side
      · have hnot : e ∉ ((run.filter fun x => !x.2).map Prod.fst).toFinset :=
          fun h => hnx ((mem_runHeads_iff e run).mp h)
        have hsrc : C.head e = b := hx₀.2
        simp only [MGraph.src, MGraph.applyUpdate, Bool.false_eq_true, ↓reduceIte, hnot,
          false_and]
        exact hsrc
      · have hnot : e ∉ ((run.filter Prod.snd).map Prod.fst).toFinset :=
          fun h => hnx ((mem_runTails_iff e run).mp h)
        have hsrc : C.tail e = b := hx₀.2
        simp only [MGraph.src, MGraph.applyUpdate, ↓reduceIte, hnot, false_and]
        exact hsrc

/-- The splits that split off the runs of one bundle after the first one name only tails and
heads at the bundle vertex. -/
private theorem bundleRunUpdates_splitEndsExact (C : MGraph) (b next : ℕ)
    (runs : List (List End)) (hn : runs.flatten.Nodup)
    (hEnds : ∀ x ∈ runs.flatten, x.1 ∈ C.E ∧ C.src x = b) :
    BatchSplitEndsExact C (bundleRunUpdates b next runs) := by
  have hsub : (runs.drop 1).flatten.Sublist runs.flatten := by
    rw [List.flatten_eq_flatMap, List.flatten_eq_flatMap]
    exact (List.drop_sublist 1 runs).flatMap _
  exact runSplits_splitEndsExact b (runs.drop 1) C next (hn.sublist hsub)
    fun x hx => hEnds x (hsub.subset hx)

/-- **The fold over the bundles.** If the bundles of the plan are distinct, and the runs of each
bundle have no end in common and hold only ends at that bundle, then the splits that the fold
adds name only tails and heads at the split vertex. -/
private theorem runsFold_splitEndsExact :
    ∀ (plan : List (ℕ × List (ℕ × List End))) (ops : List Update) (st : BundleState),
      (plan.map Prod.fst).Nodup →
      (∀ p ∈ plan, ((p.2.map Prod.snd).flatten).Nodup ∧
        ∀ x ∈ (p.2.map Prod.snd).flatten, x.1 ∈ st.graph.E ∧ st.graph.src x = p.1) →
      ∃ newOps, (plan.foldl runsFoldStep (ops, st)).1 = ops ++ newOps ∧
        BatchSplitEndsExact st.graph newOps
  | [], ops, _, _, _ => ⟨[], (List.append_nil ops).symm, trivial⟩
  | (b, vruns) :: rest, ops, st, hnd, hruns => by
    set newOps := bundleRunUpdates b (st.vertices.sup id + 1) (vruns.map Prod.snd) with hnew
    set s' := runsFoldStep (ops, st) (b, vruns) with hs'
    have h1 : s'.1 = ops ++ newOps := rfl
    have h2 : s'.2.graph = st.graph.applyBatch newOps := bundleGraph_of_applied _ _
    obtain ⟨hn₀, hE₀⟩ := hruns _ List.mem_cons_self
    have hbr : b ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
    have hruns' : ∀ q ∈ rest, ((q.2.map Prod.snd).flatten).Nodup ∧
        ∀ x ∈ (q.2.map Prod.snd).flatten, x.1 ∈ s'.2.graph.E ∧ s'.2.graph.src x = q.1 := by
      intro q hq
      obtain ⟨hn, hE⟩ := hruns q (List.mem_cons_of_mem _ hq)
      refine ⟨hn, fun x hx => ?_⟩
      obtain ⟨hxE, hxs⟩ := hE x hx
      have hqb : st.graph.src x ≠ b := by
        rw [hxs]
        exact fun h => hbr (List.mem_map.mpr ⟨q, hq, h⟩)
      rw [h2, bundleRunUpdates_edges, bundleRunUpdates_src_unchanged _ _ _ _ _ (Or.inr hqb)]
      exact ⟨hxE, hxs⟩
    obtain ⟨newOps', hF, hX⟩ :=
      runsFold_splitEndsExact rest s'.1 s'.2 (List.nodup_cons.mp hnd).2 hruns'
    refine ⟨newOps ++ newOps', ?_, batchSplitEndsExact_append
      (bundleRunUpdates_splitEndsExact st.graph b _ _ hn₀ hE₀) (h2 ▸ hX)⟩
    have hfold : (((b, vruns) :: rest).foldl runsFoldStep (ops, st)) =
        rest.foldl runsFoldStep (s'.1, s'.2) := rfl
    rw [hfold, hF, h1, List.append_assoc]

public section

/-- **The canonical bundle step names only live ends at the split vertex.** Here the order of the
core rotation after the batch (`coreOrderOf`) lists each end at most once at each vertex and at
one vertex only; this holds when the order comes from a rotation. -/
theorem bundleRunsStep_splitEndsExact {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord' : ℕ → List End} {U : List Update}
    (hn : ∀ v, (coreOrderOf (compLSFBatch cs U) ord' v).Nodup)
    (hdis : ∀ v v' x, x ∈ coreOrderOf (compLSFBatch cs U) ord' v →
      x ∈ coreOrderOf (compLSFBatch cs U) ord' v' → v = v') :
    BatchSplitEndsExact B.graph (bundleRunsStep cs B k ord' U).1 := by
  classical
  let cord := coreOrderOf (compLSFBatch cs U) ord'
  let E := B.edges \ batchDeletes U
  let dels := ((B.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete
  let st : BundleState := { B with edges := E }
  let plan := (B.vertices.sort (· ≤ ·)).map fun b =>
    (b, bundleRunsOf (compLSFBatch cs U).RF.R cord E B b)
  have hR : bundleRunsStep cs B k ord' U = plan.foldl runsFoldStep (dels, st) := rfl
  have hfst : (plan.map Prod.fst).Nodup := by
    simp only [plan, List.map_map, Function.comp_def, List.map_id']
    exact Finset.sort_nodup _ _
  have hruns : ∀ p ∈ plan, ((p.2.map Prod.snd).flatten).Nodup ∧
      ∀ x ∈ (p.2.map Prod.snd).flatten, x.1 ∈ st.graph.E ∧ st.graph.src x = p.1 := by
    intro p hp
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hp
    refine ⟨bundleRunsOf_nodup _ _ _ _ _ hn hdis, fun x hx => ?_⟩
    obtain ⟨-, -, -, hxE, hxb⟩ := (mem_bundleRunsOf_flatten _ _ _ _ _ x).mp hx
    exact ⟨hxE, (BundleState.graph_src st x).trans hxb⟩
  obtain ⟨newOps, hF, hX⟩ := runsFold_splitEndsExact plan dels st hfst hruns
  have hdel := applyBatch_deletes B.graph ((B.edges ∩ batchDeletes U).sort (· ≤ ·))
    (Finset.sort_nodup _ _) (fun e he => (Finset.mem_inter.mp ((Finset.mem_sort _).mp he)).1)
  have hset : B.edges \ (B.edges ∩ batchDeletes U) = E := by
    ext e
    simp only [E, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hg : st.graph = B.graph.applyBatch dels := by
    rw [hdel.2, Finset.sort_toFinset]
    change (⟨B.vertices, E, _, _⟩ : MGraph) =
      ⟨B.vertices, B.edges \ (B.edges ∩ batchDeletes U), _, _⟩
    rw [hset]
    rfl
  rw [hR, hF]
  refine batchSplitEndsExact_append (batchSplitEndsExact_of_noSplit fun u hu => ?_) (hg ▸ hX)
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hu
  trivial

/-- **The bundle step names only live ends at the split vertex.** Every split
`split v v' St Sh` of the batch of `bundleCompStep` names, at its turn, only edges of the bundle
graph whose tail (for `St`) or head (for `Sh`) is `v`. On ordered input the step is the canonical
step, and the order after the batch is that of a core rotation (`BundleStepReady`); otherwise the
batch is empty. -/
theorem bundleCompStep_splitEndsExact (cs : CompLSFState) (B : BundleState) (k : ℕ)
    (ord ord' : ℕ → List End) (U : List Update) :
    BatchSplitEndsExact B.graph (bundleCompStep cs B k ord ord' U).1 := by
  by_cases h : BundleStepReady cs B k ord ord' U
  · rw [bundleCompStep_eq h]
    obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, -, hσ, -, hU, -⟩ := h
    have hI' := compLSFBatch_inv hI hU
    have hGeq : cs.G.applyBatch U = (compLSFBatch cs U).G := (compLSFBatch_G cs U).symm
    let σ' : Rotation (compLSFBatch cs U).G := hGeq ▸ σ
    have hσ' : σ'.order = ord' := by
      have key : ∀ (G H : MGraph) (h : G = H) (τ : Rotation G), (h ▸ τ : Rotation H).order =
          τ.order := by
        intro G H h τ
        cases h
        rfl
      exact (key _ _ hGeq σ).trans hσ
    have hcord := coreOrderOf_eq σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
    refine bundleRunsStep_splitEndsExact (fun v => ?_) (fun v v' x hx hx' => ?_)
    · rw [← hcord]
      exact (coreRotation (L := (compLSFBatch cs U).lsf) σ' hI'.hG_val
        (compLSF_RF_isRSF hI')).nodup v
    · rw [← hcord] at hx hx'
      have h₁ := ((coreRotation (L := (compLSFBatch cs U).lsf) σ' hI'.hG_val
        (compLSF_RF_isRSF hI')).mem_order v x).mp hx
      have h₂ := ((coreRotation (L := (compLSFBatch cs U).lsf) σ' hI'.hG_val
        (compLSF_RF_isRSF hI')).mem_order v' x).mp hx'
      exact h₁.2.symm.trans h₂.2
  · rw [bundleCompStep_of_not h]
    trivial

end

end MinCostFlow.SparseCore.Program
