module

public import MinCostFlow.SparseCore.BundleTreeCore
public import MinCostFlow.SparseCore.CanonCoreSpec
public import MinCostFlow.SparseCore.Program.AssemblyModel

import MinCostFlow.LSF.Lemma54Split
import MinCostFlow.DynSpanner.Walks

/-!
# Vertex-split traces through `compLSFBatch`, `buildUSOrd`, and `stepBundleTree` (`SplitTrace`)

Tracks how vertex endpoints move across valid update batches and through the component-wise LSF
and sparsified-core output batch `buildUSOrd`:

1. **Batch splits and traces (`batchSplits`, `SplitTrace`, `SplitsValid`):**
   * `batchSplits U` extracts the `(v, v')` pairs of all `.split` updates in `U` in order.
   * `SplitTrace splits a b` holds when vertex `a` can reach `b` by staying or following splits
     `(v, v')` along `splits` in order (allowing chained splits `v ↦ v' ↦ v''`).
   * `SplitsValid.of_batchIsValid` and `applyBatch_splitTrace_of_noInsert`: every valid batch `U`
     produces valid fresh splits from `G.V`, and every surviving edge `e` not inserted by `U`
     traces its tail and head along `batchSplits U`.
2. **Core-root propagation (`compLSFBatch_root_splitTrace`, `stepBundleTree_S_cur_splitTrace`):**
   * `batchSplits_buildUSOrd`: `buildUSOrd` has the exact same split pairs as `canonCoreBatch`.
   * `compLSFBatch_root_splitTrace`: if `SplitTrace (batchSplits U) a b` for `a ∈ cs.G.V`, then
     `SplitTrace (batchSplits (canonCoreBatch cs U)) (cs.RF.root a) ((compLSFBatch cs U).RF.root b)`.
   * `stepBundleTree_S_cur_splitTrace`: transfers `SplitTrace` on endpoints of surviving edges from
     the input graph `tr.cs.G` to the sparsified core `tr.S_cur` along `info.U_S` (including edges
     re-inserted because of `D_reins`).
   * `compLSFBatch_forest_splitTrace`: every edge surviving in `(compLSFBatch cs U).RF.F` belonged
     to `cs.RF.F` and traces its tail and head along `batchSplits U`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner
open MinCostFlow.SparseCore.Program

/-! ## 1. `batchSplits`, `SplitTrace`, and `SplitsValid` -/

/-- The list of vertex-split pairs `(v, v')` appearing in a batch `U`, in batch order. -/
def batchSplits : List Update → List (ℕ × ℕ)
  | [] => []
  | .split v v' _ _ :: rest => (v, v') :: batchSplits rest
  | _ :: rest => batchSplits rest

theorem batchSplits_append (U₁ U₂ : List Update) :
    batchSplits (U₁ ++ U₂) = batchSplits U₁ ++ batchSplits U₂ := by
  induction U₁ with
  | nil => rfl
  | cons u rest ih =>
    cases u <;> simp [batchSplits, ih]

theorem batchSplits_map_delete (es : List ℕ) :
    batchSplits (es.map Update.delete) = [] := by
  induction es with
  | nil => rfl
  | cons _ rest ih => simp [batchSplits, ih]

theorem batchSplits_map_insert (es : List ℕ) (f : ℕ → ℕ) (g : ℕ → ℕ) :
    batchSplits (es.map fun e => Update.insert e (f e) (g e)) = [] := by
  induction es with
  | nil => rfl
  | cons _ rest ih => simp [batchSplits, ih]

theorem batchSplits_restrictSplits (keep : Finset ℕ) (UC : List Update) :
    batchSplits (restrictSplits keep UC) = batchSplits UC := by
  induction UC with
  | nil => rfl
  | cons u rest ih =>
    cases u <;> simp [restrictSplits, batchSplits, ih]

/-- `buildUSOrd` carries the exact same vertex-split pairs `(v, v')` as its core batch `UC`. -/
theorem batchSplits_buildUSOrd (UC U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) :
    batchSplits (buildUSOrd UC U cs_new S_prev targetE D_reins) = batchSplits UC := by
  unfold buildUSOrd
  rw [batchSplits_append, batchSplits_append, batchSplits_map_delete, batchSplits_restrictSplits,
    batchSplits_map_insert, List.nil_append, List.append_nil]

/-- `SplitTrace splits a b` holds when vertex `a` can reach `b` by staying or following splits
`(v, v')` in `splits` in order (allowing chained splits `v ↦ v' ↦ v''`). -/
inductive SplitTrace : List (ℕ × ℕ) → ℕ → ℕ → Prop
  | nil (a : ℕ) : SplitTrace [] a a
  | stay {v v' : ℕ} {rest : List (ℕ × ℕ)} {a b : ℕ} :
      SplitTrace rest a b → SplitTrace ((v, v') :: rest) a b
  | step {v v' : ℕ} {rest : List (ℕ × ℕ)} {b : ℕ} :
      SplitTrace rest v' b → SplitTrace ((v, v') :: rest) v b

theorem SplitTrace.refl : ∀ (splits : List (ℕ × ℕ)) (a : ℕ), SplitTrace splits a a
  | [], a => SplitTrace.nil a
  | (_, _) :: rest, a => SplitTrace.stay (SplitTrace.refl rest a)

theorem SplitTrace.append {s₁ s₂ : List (ℕ × ℕ)} {a b c : ℕ}
    (h₁ : SplitTrace s₁ a b) (h₂ : SplitTrace s₂ b c) :
    SplitTrace (s₁ ++ s₂) a c := by
  induction h₁ with
  | nil _ => exact h₂
  | stay _ ih => exact SplitTrace.stay (ih h₂)
  | step _ ih => exact SplitTrace.step (ih h₂)

theorem SplitTrace.singleton_iff {v v' a b : ℕ} :
    SplitTrace [(v, v')] a b ↔ b = a ∨ (a = v ∧ b = v') := by
  constructor
  · intro h
    cases h with
    | stay h' => cases h'; exact Or.inl rfl
    | step h' => cases h'; exact Or.inr ⟨rfl, rfl⟩
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact SplitTrace.stay (SplitTrace.nil _)
    · exact SplitTrace.step (SplitTrace.nil _)

/-- Every split `(v, v')` in `splits` introduces a fresh vertex `v'` not yet in the current vertex
set `V`. -/
def SplitsValid : Finset ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | V, (v, v') :: rest => v ∈ V ∧ v' ∉ V ∧ SplitsValid (insert v' V) rest

/-- Every valid batch `U` on `G` produces fresh splits `SplitsValid G.V (batchSplits U)`. -/
theorem SplitsValid.of_batchIsValid {G : MGraph} {U : List Update} (hB : G.BatchIsValid U) :
    SplitsValid G.V (batchSplits U) := by
  induction U generalizing G with
  | nil => trivial
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hB
    cases u with
    | insert _ _ _ => exact ih (G := G.applyUpdate _) hrest
    | delete _ => exact ih (G := G.applyUpdate _) hrest
    | split v v' St Sh =>
      exact ⟨hu.1, hu.2.1, ih (G := G.applyUpdate _) hrest⟩

private theorem not_mem_applyBatch_of_not_ins {H : MGraph} {U : List Update} {e : ℕ}
    (hn : e ∉ H.E) (hni : ∀ u ∈ U, ¬ u.Inserts e) : e ∉ (H.applyBatch U).E := by
  induction U generalizing H with
  | nil => exact hn
  | cons x xs ih =>
    apply ih (H := H.applyUpdate x) _ (fun y hy => hni y (List.mem_cons_of_mem _ hy))
    cases x with
    | delete _ => exact fun hm => hn (Finset.mem_of_mem_erase hm)
    | split _ _ _ _ => exact hn
    | insert e₁ _ _ =>
      have hne1 : e ≠ e₁ := fun h =>
        hni (.insert e₁ _ _) List.mem_cons_self (by simpa [Update.Inserts] using h.symm)
      exact fun hm => hn ((Finset.mem_insert.mp hm).resolve_left hne1)

/-- Every surviving edge `e` of `G` that is not inserted by a valid batch `U` traces both its tail
and its head along `batchSplits U`. -/
theorem applyBatch_splitTrace_of_noInsert {G : MGraph} {U : List Update}
    (hB : G.BatchIsValid U) {e : ℕ} (heG : e ∈ G.E) (heG' : e ∈ (G.applyBatch U).E)
    (hNoIns : ∀ u ∈ U, ¬ u.Inserts e) :
    SplitTrace (batchSplits U) (G.tail e) ((G.applyBatch U).tail e) ∧
    SplitTrace (batchSplits U) (G.head e) ((G.applyBatch U).head e) := by
  induction U generalizing G with
  | nil => exact ⟨SplitTrace.nil _, SplitTrace.nil _⟩
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hB
    have hni_u : ¬ u.Inserts e := hNoIns u List.mem_cons_self
    have hni_rest : ∀ x ∈ rest, ¬ x.Inserts e := fun x hx => hNoIns x (List.mem_cons_of_mem _ hx)
    have hE' : e ∈ ((G.applyUpdate u).applyBatch rest).E := heG'
    cases u with
    | insert e₀ a b =>
      have hne : e ≠ e₀ := fun h => hni_u (by simpa [Update.Inserts] using h.symm)
      have he1 : e ∈ (G.applyUpdate (.insert e₀ a b)).E := Finset.mem_insert_of_mem heG
      have h1 := ih hrest he1 hE' hni_rest
      have hteq : (G.applyUpdate (.insert e₀ a b)).tail e = G.tail e := by
        simp [MGraph.applyUpdate, Function.update_of_ne hne]
      have hheq : (G.applyUpdate (.insert e₀ a b)).head e = G.head e := by
        simp [MGraph.applyUpdate, Function.update_of_ne hne]
      rw [hteq, hheq] at h1
      exact h1
    | delete e₀ =>
      have hne : e ≠ e₀ := by
        intro hEq
        subst hEq
        exact not_mem_applyBatch_of_not_ins (Finset.notMem_erase _ _) hni_rest hE'
      have he1 : e ∈ (G.applyUpdate (.delete e₀)).E := Finset.mem_erase.mpr ⟨hne, heG⟩
      exact ih hrest he1 hE' hni_rest
    | split v v' St Sh =>
      have h1 := ih hrest heG hE' hni_rest
      simp only [batchSplits]
      refine ⟨?_, ?_⟩
      · by_cases ht : e ∈ St ∧ G.tail e = v
        · have hteq : (G.applyUpdate (.split v v' St Sh)).tail e = v' := by
            simp [MGraph.applyUpdate, ht]
          rw [hteq] at h1
          rw [ht.2]
          exact SplitTrace.step h1.1
        · have hteq : (G.applyUpdate (.split v v' St Sh)).tail e = G.tail e := by
            simp [MGraph.applyUpdate, ht]
          rw [hteq] at h1
          exact SplitTrace.stay h1.1
      · by_cases hh : e ∈ Sh ∧ G.head e = v
        · have hheq : (G.applyUpdate (.split v v' St Sh)).head e = v' := by
            simp [MGraph.applyUpdate, hh]
          rw [hheq] at h1
          rw [hh.2]
          exact SplitTrace.step h1.2
        · have hheq : (G.applyUpdate (.split v v' St Sh)).head e = G.head e := by
            simp [MGraph.applyUpdate, hh]
          rw [hheq] at h1
          exact SplitTrace.stay h1.2

/-! ## 2. Core-root propagation through `compLSFBatch` and `canonCoreBatch` -/

private theorem isWalk_eraseForestEdge_of_notMem {F : MGraph} {e a b : ℕ} {W : List End}
    (hW : F.IsWalk a b W) (hnot : e ∉ walkEdges W) :
    (eraseForestEdge F e).IsWalk a b W := by
  induction hW with
  | nil u => exact MGraph.IsWalk.nil u
  | @cons u w x rest hxE hsrc hrest ih =>
    have hne : x.1 ≠ e := fun h => hnot (by simp [walkEdges, h])
    have hnot' : e ∉ walkEdges rest := fun h => hnot (by
      simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert]
      exact Or.inr (by simpa [walkEdges] using h))
    exact MGraph.IsWalk.cons (Finset.mem_erase.mpr ⟨hne, hxE⟩) hsrc (ih hnot')

private theorem isWalk_connected_tail_of_mem_walkEdges {F : MGraph} {a b e : ℕ} {W : List End}
    (hW : F.IsWalk a b W) (he : e ∈ walkEdges W) : F.Connected a (F.tail e) := by
  induction hW with
  | nil _ => simp [walkEdges] at he
  | @cons u w x rest hxE hsrc hrest ih =>
    have hstep : F.Connected u (F.dst x) :=
      ⟨[x], MGraph.IsWalk.cons hxE hsrc (MGraph.IsWalk.nil _)⟩
    have he' : e = x.1 ∨ e ∈ walkEdges rest := by simpa [walkEdges] using he
    rcases he' with hEq | hRest
    · subst hEq
      cases hx2 : x.2
      · have hdst : F.dst x = F.tail x.1 := by simp [MGraph.dst, hx2]
        exact hdst ▸ hstep
      · have hsrc' : F.tail x.1 = u := by simpa [MGraph.src, hx2] using hsrc
        exact hsrc'.symm ▸ MGraph.connected_refl F u
    · exact connected_trans hstep (ih hRest)

theorem eraseForestEdge_root_eq_or_fresh {G H : MGraph} {L L' : LSF} {e fresh : ℕ}
    (hF : L.F.IsRootedSpanningForestOf G) (hF' : L'.F.IsRootedSpanningForestOf H)
    (hV : H.V = G.V) (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) (hFresh : fresh ∉ L.F.R)
    {a : ℕ} (ha : a ∈ G.V) :
    L'.F.root a = L.F.root a ∨ (L.F.root a = L.F.root (L.F.F.tail e) ∧ L'.F.root a = fresh) := by
  obtain ⟨hr'R, hconn'⟩ := root_mem_R hF' (hV.symm ▸ ha)
  have hsub : L.F.F.IsSubgraph L'.F.F := by rw [hCut]; exact eraseForestEdge_subgraph _ _
  rw [hRoots] at hr'R
  rcases Finset.mem_insert.mp hr'R with hEqFresh | hOldR
  · right
    refine ⟨?_, hEqFresh⟩
    by_contra hne
    obtain ⟨hrR, W, hW⟩ := root_mem_R hF ha
    have hnotE : e ∉ walkEdges W := by
      intro heW
      have hconn_te := isWalk_connected_tail_of_mem_walkEdges hW heW
      have hteV : L.F.F.tail e ∈ G.V := hF.2.1 ▸ (hF.1.1 e he).1
      exact hne (root_eq_of_connected hF ha hteV hconn_te)
    have hW' : L'.F.F.IsWalk a (L.F.root a) W := by
      rw [hCut]; exact isWalk_eraseForestEdge_of_notMem hW hnotE
    have hrR' : L.F.root a ∈ L'.F.R := by rw [hRoots]; exact Finset.mem_insert_of_mem hrR
    have hreq : L'.F.root a = L.F.root a := by
      have h1 := root_eq_of_connected hF' (hV.symm ▸ ha) (hF'.2.2.1 hrR') ⟨W, hW'⟩
      rwa [root_eq_of_mem_R hF' hrR'] at h1
    rw [hEqFresh] at hreq
    exact hFresh (hreq ▸ hrR)
  · left
    have hconn := connected_of_subgraph hsub hconn'
    have h1 := root_eq_of_connected hF ha (hF.2.2.1 hOldR) hconn
    rw [root_eq_of_mem_R hF hOldR] at h1
    exact h1.symm

private theorem isWalk_split_of_not_connected {F : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    {a b : ℕ} {W : List End} (hW : F.IsWalk a b W) (hnc : ¬ F.Connected a v) :
    (F.applyUpdate (.split v v' St Sh)).IsWalk a b W := by
  induction hW with
  | nil u => exact MGraph.IsWalk.nil u
  | @cons u w x rest hxE hsrc hrest ih =>
    have hu_ne : u ≠ v := fun h => hnc (h ▸ MGraph.connected_refl F u)
    have hstep : F.Connected u (F.dst x) :=
      ⟨[x], MGraph.IsWalk.cons hxE hsrc (MGraph.IsWalk.nil _)⟩
    have hdst_ne : F.dst x ≠ v := fun h => hnc (h ▸ hstep)
    have hnc' : ¬ F.Connected (F.dst x) v := fun hc => hnc (connected_trans hstep hc)
    have htail_ne : F.tail x.1 ≠ v := by
      cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2] at hsrc hu_ne hdst_ne <;>
        first | exact hsrc ▸ hu_ne | exact hdst_ne
    have hhead_ne : F.head x.1 ≠ v := by
      cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2] at hsrc hu_ne hdst_ne <;>
        first | exact hsrc ▸ hu_ne | exact hdst_ne
    have hsrc' : (F.applyUpdate (.split v v' St Sh)).src x = u := by
      cases hx2 : x.2 <;> simp [MGraph.src, MGraph.applyUpdate, hx2, htail_ne, hhead_ne] at hsrc ⊢ <;>
        exact hsrc
    have hdst' : (F.applyUpdate (.split v v' St Sh)).dst x = F.dst x := by
      cases hx2 : x.2 <;> simp [MGraph.dst, MGraph.applyUpdate, hx2, htail_ne, hhead_ne]
    exact MGraph.IsWalk.cons hxE hsrc' (hdst'.symm ▸ ih hnc')

theorem applySplit_root_eq_or_fresh {G : MGraph} {L L' : LSF} {v v' fresh : ℕ}
    {St Sh : Finset ℕ}
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.split v v' St Sh)))
    (hSplit : L'.F.F = L.F.F.applyUpdate (.split v v' St Sh))
    (hRoots : L'.F.R = insert fresh L.F.R) (hFresh : fresh ∉ L.F.R)
    (hu : G.UpdateIsValid (.split v v' St Sh))
    {a b : ℕ} (ha : a ∈ G.V) (hb : b = a ∨ (a = v ∧ b = v')) :
    L'.F.root b = L.F.root a ∨ (L.F.root a = L.F.root v ∧ L'.F.root b = fresh) := by
  have hbV : b ∈ (G.applyUpdate (.split v v' St Sh)).V := by
    rcases hb with hba | ⟨_, hbv⟩
    · rw [hba]; exact Finset.mem_insert_of_mem ha
    · rw [hbv]; exact Finset.mem_insert_self _ _
  have hvf : v' ∉ L.F.F.V := fun h => hu.2.1 (hF.2.1 ▸ h)
  let P : ℕ → ℕ := fun w => if w = v' then v else w
  have hPb : P b = a := by
    rcases hb with hba | ⟨hav, hbv⟩
    · rw [hba]
      have hne : a ≠ v' := fun h => hu.2.1 (h ▸ ha)
      simp [P, hne]
    · rw [hav, hbv]; simp [P]
  obtain ⟨hr'R, hconn'⟩ := root_mem_R hF' hbV
  rw [hRoots] at hr'R
  rcases Finset.mem_insert.mp hr'R with hEqFresh | hOldR
  · right
    refine ⟨?_, hEqFresh⟩
    by_contra hne
    have hav : a ≠ v := fun h => hne (by rw [h])
    have hba : b = a := hb.resolve_right (fun h => hav h.1)
    have hnc : ¬ L.F.F.Connected a v := fun hc => hne (root_eq_of_connected hF ha hu.1 hc)
    obtain ⟨hrR, W, hW⟩ := root_mem_R hF ha
    have hW' : L'.F.F.IsWalk a (L.F.root a) W := by
      rw [hSplit]; exact isWalk_split_of_not_connected hW hnc
    have hrR' : L.F.root a ∈ L'.F.R := by rw [hRoots]; exact Finset.mem_insert_of_mem hrR
    have hreq : L'.F.root a = L.F.root a := by
      have h1 := root_eq_of_connected hF' (hba ▸ hbV) (hF'.2.2.1 hrR') ⟨W, hW'⟩
      rwa [root_eq_of_mem_R hF' hrR'] at h1
    have hfresh_eq : fresh = L.F.root a := hEqFresh.symm.trans (hba.symm ▸ hreq)
    exact hFresh (hfresh_eq ▸ hrR)
  · left
    have hne : L'.F.root b ≠ v' := fun h => hu.2.1 (h ▸ hF.2.2.1 hOldR)
    have hproj := connected_applySplit_proj hF.1.1 hvf St Sh (hSplit ▸ hconn')
    change L.F.F.Connected (P b) (P (L'.F.root b)) at hproj
    rw [hPb] at hproj
    simp only [P, hne, ↓reduceIte] at hproj
    have h1 := root_eq_of_connected hF ha (hF.2.2.1 hOldR) hproj
    rw [root_eq_of_mem_R hF hOldR] at h1
    exact h1.symm

private theorem releasesBatch_root_splitTrace {G : MGraph} {L L' : LSF} (cuts : List ℕ)
    (hF : L.F.IsRootedSpanningForestOf G) (hF' : L'.F.IsRootedSpanningForestOf G)
    (hR : L.F.R ⊆ L'.F.R) (hCut : cuts.foldl eraseForestEdge L.F.F = L'.F.F)
    (hMem : ∀ e ∈ cuts, e ∈ L.F.F.E) (hn : cuts.Nodup) {a : ℕ} (ha : a ∈ G.V) :
    SplitTrace (batchSplits (releasesBatch G L'.F.R L cuts)) (L.F.root a) (L'.F.root a) := by
  induction cuts generalizing L with
  | nil =>
    have hFE : L.F.F = L'.F.F := hCut
    have hRC : L.F.R.card = L'.F.R.card := by
      rw [← rootedForest_components_card hF, ← rootedForest_components_card hF', hFE]
    have hRE : L.F.R = L'.F.R := Finset.eq_of_subset_of_card_le hR hRC.ge
    have hRF_eq : L.F = L'.F := by
      cases h1 : L.F; cases h2 : L'.F
      rw [h1, h2] at hFE hRE
      exact congrArg₂ RootedForest.mk hFE hRE
    simp only [releasesBatch, batchSplits, hRF_eq]
    exact SplitTrace.nil _
  | cons e cuts ih =>
    let K := eraseForestEdge L.F.F e
    have he := hMem e List.mem_cons_self
    have hKn := isForest_eraseEdge hF.1 e
    have hKV : K.V = G.V := hF.2.1
    have hKsub : L.F.F.IsSubgraph K := eraseForestEdge_subgraph _ _
    have hKG : G.IsSubgraph K :=
      ⟨hF.2.2.2.2.1, fun _ hf => hF.2.2.2.2.2.1 (Finset.mem_of_mem_erase hf),
        fun f hf => hF.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    have hrest : cuts.foldl eraseForestEdge K = L'.F.F := hCut
    have hFinalK : K.IsSubgraph L'.F.F := by
      rw [← hrest, foldl_eraseForestEdge]
      exact ⟨Finset.Subset.rfl, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hsep : ∀ r₁ ∈ L.F.R, ∀ r₂ ∈ L.F.R, K.Connected r₁ r₂ → r₁ = r₂ := by
      intro r₁ hr₁ r₂ hr₂ hConn
      have hr := root_eq_of_connected hF (hF.2.2.1 hr₁) (hF.2.2.1 hr₂)
        (connected_of_subgraph hKsub hConn)
      rwa [root_eq_of_mem_R hF hr₁, root_eq_of_mem_R hF hr₂] at hr
    obtain ⟨hIncl, hSub, hMid⟩ := canonRoots_spec hKn hKV hKG hF' hFinalK hR hsep
    let Lmid : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R L'.F.R⟩, L.wstr⟩
    have hComp := forest_eraseEdge_components_card hF.1 he
    change (components K).card = _ at hComp
    have hRc : (canonRoots K L.F.R L'.F.R).card = L.F.R.card + 1 := by
      rw [← rootedForest_components_card hMid, ← rootedForest_components_card hF]
      exact hComp
    obtain ⟨fresh, hf, heq⟩ := roots_insert_of_card hIncl hRc
    have hnew : newRoot Lmid.F.R L.F.R = fresh := newRoot_eq heq hf
    have hMemRest : ∀ f ∈ cuts, f ∈ K.E := fun f hf' =>
      Finset.mem_erase.mpr ⟨fun h => (List.nodup_cons.mp hn).1 (h ▸ hf'),
        hMem f (List.mem_cons_of_mem _ hf')⟩
    have htail := ih (L := Lmid) hMid hSub hrest hMemRest (List.nodup_cons.mp hn).2
    have hstep := eraseForestEdge_root_eq_or_fresh (L' := Lmid) hF hMid rfl he rfl heq hf ha
    simp only [releasesBatch, refineSplit, batchSplits]
    rw [hnew]
    rcases hstep with hsame | ⟨hfrom, hto⟩
    · exact SplitTrace.stay (hsame ▸ htail)
    · rw [hfrom]
      exact SplitTrace.step (hto ▸ htail)

theorem compLSF_forestAfterInput' {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    let K := forestAfterInput cs.RF.F u
    let cs' := compLSFStepSingle cs u
    K.IsForest ∧ (cs.G.applyUpdate u).IsSubgraph K ∧ K.IsSubgraph cs'.RF.F ∧
      K.V = cs'.RF.F.V := by
  intro K cs'
  have hF := compLSF_RF_isRSF hI
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF' := compLSF_RF_isRSF hI'
  have hdec := compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩
  have hFE : cs'.RF.F.E ⊆ cs.RF.F.E := hdec.1
  have hFG : cs.RF.F.E ⊆ cs.G.E := hF.2.2.2.2.2.1
  have hFG' : cs'.RF.F.E ⊆ cs'.G.E := hF'.2.2.2.2.2.1
  have hFV : cs.RF.F.V = cs.G.V := hF.2.1
  have hFV' : cs'.RF.F.V = cs'.G.V := hF'.2.1
  have hKG : (cs.G.applyUpdate u).IsSubgraph K := by
    cases u with
    | insert e a b =>
      refine ⟨hFV.le, hFG.trans (Finset.subset_insert _ _), fun f hf => ?_⟩
      have hfe : f ≠ e := fun h => hu.1 (h ▸ hFG hf)
      change cs.G.tail f = Function.update cs.G.tail e a f ∧
        cs.G.head f = Function.update cs.G.head e b f
      simp [Function.update_of_ne hfe]
    | delete e =>
      exact ⟨hFV.le, Finset.erase_subset_erase e hFG, fun _ _ => ⟨rfl, rfl⟩⟩
    | split v v' St Sh =>
      refine ⟨?_, hFG, fun _ _ => ⟨rfl, rfl⟩⟩
      change insert v' cs.RF.F.V ⊆ insert v' cs.G.V
      rw [hFV]
  have hKV : K.V = cs'.G.V := by
    cases u with
    | insert => exact hFV
    | delete => exact hFV
    | split v v' St Sh =>
      change insert v' cs.RF.F.V = insert v' cs.G.V
      rw [hFV]
  refine ⟨?_, hKG, ?_, hKV.trans hFV'.symm⟩
  · cases u with
    | insert => exact hF.1
    | delete e => exact isForest_eraseEdge hF.1 e
    | split v v' St Sh =>
      exact applyUpdate_split_isForest hF.1 (hFV ▸ hu.1) (hFV ▸ hu.2.1) St Sh
  · have hKE : cs'.RF.F.E ⊆ K.E := by
      cases u with
      | insert => exact hFE
      | split => exact hFE
      | delete e =>
        intro f hf
        refine Finset.mem_erase.mpr ⟨?_, hFE hf⟩
        rintro rfl
        have := hFG' hf
        change f ∈ cs.G.E.erase f at this
        simp at this
    refine ⟨hFV'.trans hKV.symm |>.le, hKE, fun f hf => ?_⟩
    obtain ⟨h1, h2⟩ := hKG.2.2 f (hKE hf)
    exact ⟨h1.symm, h2.symm⟩

theorem forestAfterInput_root_sep' {G : MGraph} {RF : RootedForest} {u : Update}
    (hF : RF.IsRootedSpanningForestOf G) (hu : G.UpdateIsValid u)
    {a b : ℕ} (ha : a ∈ RF.R) (hb : b ∈ RF.R)
    (hc : (forestAfterInput RF.F u).Connected a b) : a = b := by
  have hconn : RF.F.Connected a b := by
    cases u with
    | insert => exact hc
    | delete e => exact connected_of_subgraph (eraseForestEdge_subgraph _ e) hc
    | split v v' St Sh =>
      have hvf : v' ∉ RF.F.V := fun he => hu.2.1 (hF.2.1 ▸ he)
      have ha' : a ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 ha)
      have hb' : b ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 hb)
      exact by simpa [ha', hb'] using connected_applySplit_proj hF.1.1 hvf St Sh hc
  have hEq := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb) hconn
  rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hEq

/-- One step of `compLSFStepSingle` propagates `SplitTrace` from input vertices to core roots
along `canonStepCore` (with no rotation hypotheses). -/
theorem compLSFStepSingle_root_splitTrace {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u)
    {a b : ℕ} (ha : a ∈ cs.G.V) (hab : SplitTrace (batchSplits [u]) a b) :
    SplitTrace (batchSplits (canonStepCore cs u))
      (cs.RF.root a) ((compLSFStepSingle cs u).RF.root b) := by
  set cs' := compLSFStepSingle cs u
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF := compLSF_RF_isRSF hI
  have hF' : cs'.RF.IsRootedSpanningForestOf (cs.G.applyUpdate u) := compLSF_RF_isRSF hI'
  have hR : cs.RF.R ⊆ cs'.RF.R := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).2
  obtain ⟨hK, hKG, hsub, hKV⟩ := compLSF_forestAfterInput' hI hu
  let K := forestAfterInput cs.RF.F u
  let cuts := (K.E \ cs'.RF.F.E).sort (· ≤ ·)
  let Fc := cuts.foldl eraseForestEdge K
  have hFcE : Fc.E = cs'.RF.F.E := by
    simp only [Fc, cuts, foldl_eraseForestEdge, Finset.sort_toFinset]
    exact Finset.sdiff_sdiff_eq_self hsub.2.1
  have hFcK : K.IsSubgraph Fc := by
    refine ⟨?_, ?_, fun _ _ => by simp [Fc, foldl_eraseForestEdge]⟩
    · simp only [Fc, foldl_eraseForestEdge]; exact Finset.Subset.rfl
    · simp only [Fc, foldl_eraseForestEdge]; exact Finset.sdiff_subset
  have hEqF : GraphEq Fc cs'.RF.F := by
    refine ⟨?_, hFcE, fun f hf => ?_⟩
    · simp only [Fc, foldl_eraseForestEdge]; exact hKV
    · obtain ⟨h1, h2⟩ := hsub.2.2 f (hFcE ▸ hf)
      simp only [Fc, foldl_eraseForestEdge]
      exact ⟨h1.symm, h2.symm⟩
  let L'' : LSF := ⟨cs'.lsf.T, ⟨Fc, cs'.RF.R⟩, cs'.lsf.wstr⟩
  have hL'' : L''.F.IsRootedSpanningForestOf (cs.G.applyUpdate u) :=
    isRootedSpanningForestOf_congr hF' rfl (graphEq_symm hEqF)
  have hKV' : K.V = (cs.G.applyUpdate u).V := hKV.trans hF'.2.1
  have hIntermediate := canonRoots_spec hK hKV' hKG hL'' hFcK hR
    (fun _ hr₁ _ hr₂ hc => forestAfterInput_root_sep' hF hu hr₁ hr₂ hc)
  have hbV : b ∈ (cs.G.applyUpdate u).V := by
    cases u with
    | insert _ _ _ =>
      cases hab; exact ha
    | delete _ =>
      cases hab; exact ha
    | split v v' St Sh =>
      rcases SplitTrace.singleton_iff.mp hab with rfl | ⟨_, rfl⟩
      · exact Finset.mem_insert_of_mem ha
      · exact Finset.mem_insert_self _ _
  have hRootCon : L''.F.root b = cs'.RF.root b := by
    obtain ⟨hrR, hc⟩ := root_mem_R hL'' hbV
    have hSubEq : cs'.RF.F.IsSubgraph Fc :=
      ⟨hEqF.1.le, hEqF.2.1.le, fun f hf => hEqF.2.2 f hf⟩
    have hc' : cs'.RF.F.Connected b (L''.F.root b) := connected_of_subgraph hSubEq hc
    have h1 := root_eq_of_connected hF' hbV (hF'.2.2.1 hrR) hc'
    rw [root_eq_of_mem_R hF' hrR] at h1
    exact h1.symm
  -- Half 1: `inputCoreBatch cs u` from `cs.lsf` to `inputMid cs u`.
  have hMidData :
      ∃ hm : (inputMid cs u).F.IsRootedSpanningForestOf (cs.G.applyUpdate u),
        (inputMid cs u).F.F = K ∧ (inputMid cs u).F.R ⊆ cs'.RF.R ∧
        SplitTrace (batchSplits (inputCoreBatch cs u)) (cs.RF.root a) ((inputMid cs u).F.root b) := by
    cases u with
    | insert e x y =>
      cases hab
      have hm : cs.lsf.F.IsRootedSpanningForestOf (cs.G.applyUpdate (.insert e x y)) :=
        ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hKG⟩
      exact ⟨hm, rfl, hR, SplitTrace.nil _⟩
    | delete e =>
      cases hab
      by_cases he : e ∈ cs.RF.F.E
      · obtain ⟨hRo, hRf, hm⟩ := hIntermediate
        let R := canonRoots K cs.RF.R cs'.RF.R
        let mid : LSF := ⟨cs.lsf.T, ⟨K, R⟩, cs.lsf.wstr⟩
        have hM : inputMid cs (.delete e) = mid := by
          simp only [inputMid, he, ↓reduceIte]; rfl
        have hB : inputCoreBatch cs (.delete e) =
            [refineSplit (coreGraph cs.G cs.lsf) (coreGraph (cs.G.applyUpdate (.delete e)) mid)
              (cs.RF.root (cs.RF.F.tail e)) (newRoot R cs.RF.R)] := by
          simp only [inputCoreBatch, he, ↓reduceIte, hM]; rfl
        have hcount : R.card = cs.RF.R.card + 1 := by
          rw [← rootedForest_components_card hm, ← rootedForest_components_card hF]
          exact forest_eraseEdge_components_card hF.1 he
        obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
        have hstep := eraseForestEdge_root_eq_or_fresh (L := cs.lsf) (L' := mid) hF hm rfl he rfl hR' hnew ha
        have hnr : newRoot R cs.RF.R = fresh := newRoot_eq hR' hnew
        refine ⟨hM.symm ▸ hm, by rw [hM], by rw [hM]; exact hRf, ?_⟩
        rw [hB, hM]
        simp only [refineSplit, batchSplits]
        rw [hnr]
        exact SplitTrace.singleton_iff.mpr hstep
      · have hK_eq : K = cs.RF.F := by
          change { cs.RF.F with E := cs.RF.F.E.erase e } = cs.RF.F
          exact congrArg (fun E => { cs.RF.F with E := E }) (Finset.erase_eq_of_notMem he)
        have hM : inputMid cs (.delete e) = cs.lsf := by simp only [inputMid, he, ↓reduceIte]
        have hB : inputCoreBatch cs (.delete e) = [.delete e] := by
          simp only [inputCoreBatch, he, ↓reduceIte]
        have hm : cs.lsf.F.IsRootedSpanningForestOf (cs.G.applyUpdate (.delete e)) :=
          ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hK_eq ▸ hKG⟩
        refine ⟨hM.symm ▸ hm, by rw [hM, hK_eq]; rfl, by rw [hM]; exact hR, ?_⟩
        rw [hB, hM]; exact SplitTrace.nil _
    | split v v' St Sh =>
      obtain ⟨hRo, hRf, hm⟩ := hIntermediate
      let R := canonRoots K cs.RF.R cs'.RF.R
      let mid : LSF := ⟨cs.lsf.T, ⟨K, R⟩, cs.lsf.wstr⟩
      have hcount : R.card = cs.RF.R.card + 1 := by
        have ho := rootedForest_R_add_edges hF
        have hn := rootedForest_R_add_edges hm
        have hv : (cs.G.applyUpdate (.split v v' St Sh)).V.card = cs.G.V.card + 1 :=
          Finset.card_insert_of_notMem hu.2.1
        change R.card + cs.RF.F.E.card = (cs.G.applyUpdate (.split v v' St Sh)).V.card at hn
        omega
      obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
      have hstep := applySplit_root_eq_or_fresh (L := cs.lsf) (L' := mid) hF hm rfl hR' hnew hu ha
        (SplitTrace.singleton_iff.mp hab)
      have hnr : newRoot R cs.RF.R = fresh := newRoot_eq hR' hnew
      refine ⟨hm, rfl, hRf, ?_⟩
      simp only [inputCoreBatch, refineSplit, batchSplits]
      change SplitTrace [(cs.RF.root v, newRoot R cs.RF.R)] (cs.RF.root a) (mid.F.root b)
      rw [hnr]
      exact SplitTrace.singleton_iff.mpr hstep
  obtain ⟨hm, hmidF, hmR, htr₁⟩ := hMidData
  -- Half 2: `releasesBatch` from `inputMid cs u` to `L''` (whose root equals `cs'.RF.root`).
  have hCut : cuts.foldl eraseForestEdge (inputMid cs u).F.F = L''.F.F := by rw [hmidF]
  have hMem : ∀ e ∈ cuts, e ∈ (inputMid cs u).F.F.E := fun e he => by
    rw [hmidF]
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1
  have htr₂ := releasesBatch_root_splitTrace (L := inputMid cs u) (L' := L'') cuts hm hL'' hmR
    hCut hMem (Finset.sort_nodup _ _) hbV
  rw [hRootCon] at htr₂
  unfold canonStepCore
  rw [batchSplits_append]
  exact htr₁.append htr₂

/-- A valid batch `U` on `cs` propagates `SplitTrace` from input vertices to core roots along
`canonCoreBatch cs U`. -/
theorem compLSFBatch_root_splitTrace {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    {a b : ℕ} (ha : a ∈ cs.G.V) (hab : SplitTrace (batchSplits U) a b) :
    SplitTrace (batchSplits (canonCoreBatch cs U))
      (cs.RF.root a) ((compLSFBatch cs U).RF.root b) := by
  induction U generalizing cs a with
  | nil =>
    cases hab
    exact SplitTrace.nil _
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hU
    have hI1 : CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs u) := compLSFInv_step hI hu
    -- Factor `hab` at `u` into one step `a → m` and the remaining trace `m → b`.
    obtain ⟨m, hmV, hstep_u, hrest_tr⟩ :
        ∃ m ∈ (cs.G.applyUpdate u).V,
          SplitTrace (batchSplits [u]) a m ∧ SplitTrace (batchSplits rest) m b := by
      cases u with
      | insert _ _ _ => exact ⟨a, ha, SplitTrace.nil a, hab⟩
      | delete _ => exact ⟨a, ha, SplitTrace.nil a, hab⟩
      | split v v' St Sh =>
        cases hab with
        | stay h => exact ⟨a, Finset.mem_insert_of_mem ha, SplitTrace.stay (SplitTrace.nil _), h⟩
        | step h => exact ⟨v', Finset.mem_insert_self _ _, SplitTrace.step (SplitTrace.nil _), h⟩
    have h1 := compLSFStepSingle_root_splitTrace hI hu ha hstep_u
    have h2 := ih hI1 hrest hmV hrest_tr
    change SplitTrace (batchSplits (canonStepCore cs u ++ canonCoreBatch (compLSFStepSingle cs u) rest)) _ _
    rw [batchSplits_append]
    exact h1.append h2

/-- Every edge surviving in the active forest `(compLSFBatch cs U).RF.F` belonged to `cs.RF.F`
and traces its tail and head along `batchSplits U`. -/
theorem compLSFBatch_forest_splitTrace {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    {f : ℕ} (hf' : f ∈ (compLSFBatch cs U).RF.F.E) :
    f ∈ cs.RF.F.E ∧
    SplitTrace (batchSplits U) (cs.RF.F.tail f) ((compLSFBatch cs U).RF.F.tail f) ∧
    SplitTrace (batchSplits U) (cs.RF.F.head f) ((compLSFBatch cs U).RF.F.head f) := by
  induction U generalizing cs with
  | nil => exact ⟨hf', SplitTrace.nil _, SplitTrace.nil _⟩
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hU
    have hI1 : CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs u) := compLSFInv_step hI hu
    obtain ⟨hf1, ht1, hh1⟩ := ih hI1 hrest hf'
    have hF := compLSF_RF_isRSF hI
    have hF1 := compLSF_RF_isRSF hI1
    obtain ⟨_, hKG, hsub, _⟩ := compLSF_forestAfterInput' hI hu
    have hfK : f ∈ (forestAfterInput cs.RF.F u).E := hsub.2.1 hf1
    have h1end := hsub.2.2 f hf1
    have hf0 : f ∈ cs.RF.F.E := by
      cases u with
      | insert _ _ _ => exact hfK
      | delete _ => exact Finset.mem_of_mem_erase hfK
      | split _ _ _ _ => exact hfK
    refine ⟨hf0, ?_, ?_⟩
    · cases u with
      | insert _ _ _ =>
        change SplitTrace (batchSplits rest) _ _
        rw [h1end.1] at ht1; exact ht1
      | delete _ =>
        change SplitTrace (batchSplits rest) _ _
        rw [h1end.1] at ht1; exact ht1
      | split v v' St Sh =>
        simp only [batchSplits]
        by_cases ht : f ∈ St ∧ cs.RF.F.tail f = v
        · have hteq : (compLSFStepSingle cs (.split v v' St Sh)).RF.F.tail f = v' := by
            rw [h1end.1]; simp [forestAfterInput, MGraph.applyUpdate, ht]
          rw [hteq] at ht1
          rw [ht.2]
          exact SplitTrace.step ht1
        · have hteq : (compLSFStepSingle cs (.split v v' St Sh)).RF.F.tail f = cs.RF.F.tail f := by
            rw [h1end.1]; simp [forestAfterInput, MGraph.applyUpdate, ht]
          rw [hteq] at ht1
          exact SplitTrace.stay ht1
    · cases u with
      | insert _ _ _ =>
        change SplitTrace (batchSplits rest) _ _
        rw [h1end.2] at hh1; exact hh1
      | delete _ =>
        change SplitTrace (batchSplits rest) _ _
        rw [h1end.2] at hh1; exact hh1
      | split v v' St Sh =>
        simp only [batchSplits]
        by_cases hh : f ∈ Sh ∧ cs.RF.F.head f = v
        · have hheq : (compLSFStepSingle cs (.split v v' St Sh)).RF.F.head f = v' := by
            rw [h1end.2]; simp [forestAfterInput, MGraph.applyUpdate, hh]
          rw [hheq] at hh1
          rw [hh.2]
          exact SplitTrace.step hh1
        · have hheq : (compLSFStepSingle cs (.split v v' St Sh)).RF.F.head f = cs.RF.F.head f := by
            rw [h1end.2]; simp [forestAfterInput, MGraph.applyUpdate, hh]
          rw [hheq] at hh1
          exact SplitTrace.stay hh1

/-- **Output-graph endpoint trace through `stepBundleTree`.** If a surviving edge `e` of `S_cur`
traces its endpoints in `tr.cs.G` along `batchSplits U`, then it traces its endpoints in `S_cur`
along `batchSplits info.U_S` (even when `buildUSOrd` deletes and re-inserts `e` via `D_reins`). -/
theorem stepBundleTree_S_cur_splitTrace {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hS_sub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur)
    (hS_sub' : (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).IsSubgraph
      (stepBundleTree sparsify tr U ord ord').state.S_cur)
    {e : ℕ} (he : e ∈ tr.S_cur.E) (he' : e ∈ (stepBundleTree sparsify tr U ord ord').state.S_cur.E)
    (ht : SplitTrace (batchSplits U) (tr.cs.G.tail e) ((compLSFBatch tr.cs U).G.tail e))
    (hh : SplitTrace (batchSplits U) (tr.cs.G.head e) ((compLSFBatch tr.cs U).G.head e)) :
    let info := stepBundleTree sparsify tr U ord ord'
    SplitTrace (batchSplits info.U_S) (tr.S_cur.tail e) (info.state.S_cur.tail e) ∧
    SplitTrace (batchSplits info.U_S) (tr.S_cur.head e) (info.state.S_cur.head e) := by
  intro info
  have hUS_splits : batchSplits info.U_S = batchSplits (canonCoreBatch tr.cs U) :=
    batchSplits_buildUSOrd _ _ _ _ _ _
  have heG : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp (hS_sub.2.1 he)).1
  have hEnds := hI.hG_val e heG
  have hOld := hS_sub.2.2 e he
  have hNew := hS_sub'.2.2 e he'
  rw [hUS_splits, hOld.1, hOld.2, hNew.1, hNew.2]
  exact ⟨compLSFBatch_root_splitTrace hI hU hEnds.1 ht,
    compLSFBatch_root_splitTrace hI hU hEnds.2 hh⟩

end MinCostFlow.SparseCore
