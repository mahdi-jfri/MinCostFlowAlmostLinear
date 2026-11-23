module

public import MinCostFlow.SparseCore.BundleRunsFacts

/-!
# The canonical bundle step is a partition, and is no larger than any other

This file proves the main facts about `bundleRunsStep` (`bundleRunsStep_core`). Fix a rotation
`σ` of the graph after the batch, with the order that the step reads. Fix also some other result
`Bw` of a bundle step that meets the specification: it is a partition for the core rotation
after the batch, it comes from the old bundles by a valid batch of deletions and splits, and its
edges are the old bundle edges that the input batch keeps. Such a result exists
(`bundleStepSpec_exists`). Then:

* The canonical result is a partition for the same core rotation. Each run lies at one core
  vertex, is an arc there (`cycRuns_isArc`), and has at most as many ends as its old bundle.
* It has at most as many bundles as `Bw`. A bundle of `Bw` holds ends of one old bundle
  (`delSplit_back`) at one core vertex, and it is an arc there. So all its ends lie in one run
  (`cycRuns_block`). Sending a run to the bundle of `Bw` of one of its ends is then one-to-one.
* Each bundle either has the parent of a bundle of `Bw`, or is an old bundle with its old parent.

The counting facts on the emitted batch do not need `σ` or `Bw`, but their proof shares the
setup, so they are proved here too.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner

private theorem split_tags (op : Update) (h : isSplit op = true) :
    deleteTag op = false ∧ isDelOrSplit op := by
  cases op with
  | insert => simp [isSplit] at h
  | delete => simp [isSplit] at h
  | split => exact ⟨rfl, trivial⟩

theorem bundleRunsStep_core {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord' : ℕ → List End} {U : List Update}
    (hlive : ∀ x ∈ edgeEnds B.edges, B.bundleOf x ∈ B.vertices)
    (hk : ∀ b ∈ B.vertices, (B.ends b).card ≤ k)
    (hpar0 : ∀ b ∈ B.vertices, B.parent b ∈ (compLSFBatch cs U).RF.R)
    (σ : Rotation (compLSFBatch cs U).G) (hG : (compLSFBatch cs U).G.IsValid)
    (hF : (compLSFBatch cs U).RF.IsRootedSpanningForestOf (compLSFBatch cs U).G)
    (hσ : σ.order = ord') {UBw : List Update} {Bw : BundleState}
    (hwp : Bw.IsPartition (coreRotation (L := (compLSFBatch cs U).lsf) σ hG hF) k)
    (hwv : B.graph.BatchIsValid UBw) (hwg : Bw.graph = B.graph.applyBatch UBw)
    (hwt : ∀ op ∈ UBw, isDelOrSplit op) (hwE : Bw.edges = B.edges \ batchDeletes U) :
    let R := bundleRunsStep cs B k ord' U
    R.2.IsPartition (coreRotation (L := (compLSFBatch cs U).lsf) σ hG hF) k ∧
    R.2.vertices.card ≤ Bw.vertices.card ∧
    (∀ c ∈ R.2.vertices, (∃ x ∈ R.2.ends c, R.2.parent c = Bw.parent (Bw.bundleOf x)) ∨
      (c ∈ B.vertices ∧ R.2.parent c = B.parent c)) ∧
    (∀ c ∉ R.2.vertices, R.2.parent c = B.parent c) ∧
    B.graph.BatchIsValid R.1 ∧ R.2.graph = B.graph.applyBatch R.1 ∧
    (∀ op ∈ R.1, isDelOrSplit op) ∧
    (∀ op ∈ R.1, deleteTag op = true → ∃ e ∈ B.edges, op = .delete e ∧ e ∈ batchDeletes U) ∧
    R.1.countP deleteTag ≤ U.length ∧
    R.2.vertices.card = B.vertices.card + batchSplitCount R.1 ∧
    R.2.edges = B.edges \ batchDeletes U ∧ B.vertices ⊆ R.2.vertices := by
  classical
  intro R
  let cord := coreOrderOf (compLSFBatch cs U) ord'
  let xs : ℕ → List End := fun v => (cord v).filter fun x => decide (x.1 ∈ B.edges \ batchDeletes U)
  let pb : ℕ → End → Bool := fun b x => decide (B.bundleOf x = b)
  let dels := ((B.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete
  let st : BundleState := { B with edges := B.edges \ batchDeletes U }
  let plan := (B.vertices.sort (· ≤ ·)).map fun b =>
    (b, bundleRunsOf (compLSFBatch cs U).RF.R cord (B.edges \ batchDeletes U) B b)
  have hR : R = plan.foldl runsFoldStep (dels, st) := rfl
  -- Facts about the core rotation after the batch, read off the witness `Bw`.
  have hcord : (coreRotation (L := (compLSFBatch cs U).lsf) σ hG hF).order = cord :=
    coreOrderOf_eq σ hG hF hσ
  have hE₁B : B.edges \ batchDeletes U ⊆ B.edges := Finset.sdiff_subset
  have hE₁C : B.edges \ batchDeletes U ⊆
      (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).E := hwE ▸ hwp.1
  have hw3 : ∀ x : End, x.1 ∈ B.edges \ batchDeletes U → Bw.bundleOf x ∈ Bw.vertices ∧
      Bw.parent (Bw.bundleOf x) = (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src x :=
    fun x hx => hwp.2.2.1 x ((mem_edgeEnds _ _).mpr (hwE ▸ hx))
  have hsrcR : ∀ x : End, x.1 ∈ B.edges \ batchDeletes U →
      (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src x ∈ (compLSFBatch cs U).RF.R :=
    fun x hx => (hw3 x hx).2 ▸ hwp.2.1 _ (hw3 x hx).1
  have hmemcord : ∀ v x, x ∈ cord v ↔ x.1 ∈ (coreGraph (compLSFBatch cs U).G
      (compLSFBatch cs U).lsf).E ∧ (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src x = v :=
    fun v x => hcord ▸ (coreRotation (L := (compLSFBatch cs U).lsf) σ hG hF).mem_order v x
  have hncord : ∀ v, (cord v).Nodup :=
    fun v => hcord ▸ (coreRotation (L := (compLSFBatch cs U).lsf) σ hG hF).nodup v
  have hmemxs : ∀ v x, x ∈ xs v ↔ x.1 ∈ B.edges \ batchDeletes U ∧
      (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src x = v := by
    intro v x
    change x ∈ (cord v).filter _ ↔ _
    rw [List.mem_filter, hmemcord, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨-, h⟩, hE⟩
      exact ⟨hE, h⟩
    · rintro ⟨hE, h⟩
      exact ⟨⟨hE₁C hE, h⟩, hE⟩
  have hxsnd : ∀ v, (xs v).Nodup := fun v => (hncord v).filter _
  have hdis : ∀ v v' x, x ∈ cord v → x ∈ cord v' → v = v' := fun v v' x h h' =>
    ((hmemcord v x).mp h).2.symm.trans ((hmemcord v' x).mp h').2
  -- The hypotheses of the fold.
  have hlive' : ∀ x : End, x.1 ∈ st.edges → st.bundleOf x ∈ st.vertices :=
    fun x hx => hlive x ((mem_edgeEnds _ _).mpr (hE₁B hx))
  have hfst : plan.map Prod.fst = B.vertices.sort (· ≤ ·) := by
    simp [plan, List.map_map, Function.comp_def]
  have hplan_mem : ∀ p ∈ plan, p.1 ∈ B.vertices ∧
      p.2 = bundleRunsOf (compLSFBatch cs U).RF.R cord (B.edges \ batchDeletes U) B p.1 := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    exact ⟨(Finset.mem_sort _).mp hb, rfl⟩
  have hcover : ∀ b x, x ∈ ((bundleRunsOf (compLSFBatch cs U).RF.R cord
      (B.edges \ batchDeletes U) B b).map Prod.snd).flatten ↔
      x.1 ∈ B.edges \ batchDeletes U ∧ B.bundleOf x = b := by
    intro b x
    rw [mem_bundleRunsOf_flatten]
    constructor
    · rintro ⟨v, -, -, hE, hb⟩
      exact ⟨hE, hb⟩
    · rintro ⟨hE, hb⟩
      exact ⟨_, hsrcR x hE, (hmemcord _ x).mpr ⟨hE₁C hE, rfl⟩, hE, hb⟩
  have hruns : ∀ p ∈ plan, ((p.2.map Prod.snd).flatten).Nodup ∧
      ∀ x, x ∈ (p.2.map Prod.snd).flatten ↔ x.1 ∈ st.edges ∧ st.bundleOf x = p.1 := by
    intro p hp
    rw [(hplan_mem p hp).2]
    exact ⟨bundleRunsOf_nodup _ _ _ _ _ hncord hdis, hcover p.1⟩
  have hdel := applyBatch_deletes B.graph ((B.edges ∩ batchDeletes U).sort (· ≤ ·))
    (Finset.sort_nodup _ _) (fun e he => (Finset.mem_inter.mp ((Finset.mem_sort _).mp he)).1)
  have hset : B.edges \ (B.edges ∩ batchDeletes U) = B.edges \ batchDeletes U := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hg : st.graph = B.graph.applyBatch dels := by
    rw [hdel.2, Finset.sort_toFinset]
    change (⟨B.vertices, B.edges \ batchDeletes U, _, _⟩ : MGraph) =
      ⟨B.vertices, B.edges \ (B.edges ∩ batchDeletes U), _, _⟩
    rw [hset]
    rfl
  have hmem' : ∀ p ∈ plan, p.1 ∈ st.vertices := fun p hp => (hplan_mem p hp).1
  obtain ⟨f1, f2, f3, ⟨newOps, f4a, f4b, f4c⟩, f5, f6, -, f8, f9⟩ :=
    runsFold_spec B.graph plan dels st (hfst ▸ Finset.sort_nodup _ _) hmem' hlive' hruns hg hdel.1
  have f10 := runsFold_parent_out plan (dels, st) hmem'
  rw [hR]
  generalize plan.foldl runsFoldStep (dels, st) = F at f1 f2 f3 f4a f5 f6 f8 f9 f10
  -- What each new bundle is: a run, or an old bundle with no ends left.
  have hclass : ∀ c ∈ F.2.vertices,
      (∃ b ∈ B.vertices, ∃ v, ∃ r ∈ cycRuns (pb b) (xs v),
        F.2.ends c = r.toFinset ∧ F.2.parent c = v ∧ v ∈ (compLSFBatch cs U).RF.R) ∨
      (c ∈ B.vertices ∧
        bundleRunsOf (compLSFBatch cs U).RF.R cord (B.edges \ batchDeletes U) B c = [] ∧
        F.2.ends c = ∅ ∧ F.2.parent c = B.parent c) := by
    intro c hc
    rcases f9 c hc with ⟨hcs, hcn⟩ | ⟨p, hp, vr, hvr, e1, e2⟩ | ⟨p, hp, hp2, rfl, e1, e2⟩
    · exact absurd (hfst ▸ (Finset.mem_sort _).mpr hcs) hcn
    · obtain ⟨hb, hp2⟩ := hplan_mem p hp
      rw [hp2] at hvr
      obtain ⟨hv, hr⟩ := mem_bundleRunsOf hvr
      exact Or.inl ⟨p.1, hb, vr.1, vr.2, hr, e1, e2, hv⟩
    · obtain ⟨hb, hp2'⟩ := hplan_mem p hp
      exact Or.inr ⟨hb, hp2'.symm.trans hp2, e1, e2⟩
  have hrun : ∀ b v r, r ∈ cycRuns (pb b) (xs v) → ∀ x ∈ r,
      x.1 ∈ B.edges \ batchDeletes U ∧
        (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src x = v ∧ B.bundleOf x = b := by
    intro b v r hr x hx
    obtain ⟨hxv, hxb⟩ := (cycRuns_spec _ _ r hr).2 x hx
    exact ⟨((hmemxs v x).mp hxv).1, ((hmemxs v x).mp hxv).2, by simpa [pb] using hxb⟩
  have hendsE : ∀ c x, x ∈ F.2.ends c → x.1 ∈ B.edges \ batchDeletes U := fun c x hx => by
    have h := ((BundleState.mem_ends _ _ _).mp hx).1
    rw [f1] at h
    exact h
  have hempty : ∀ c ∈ F.2.vertices, ¬ (F.2.ends c).Nonempty → c ∈ B.vertices ∧
      bundleRunsOf (compLSFBatch cs U).RF.R cord (B.edges \ batchDeletes U) B c = [] := by
    intro c hc hne
    rcases hclass c hc with ⟨b, -, v, r, hr, e1, -, -⟩ | ⟨hcB, hnil, -, -⟩
    · obtain ⟨hrne, -⟩ := cycRuns_spec _ _ r hr
      exact absurd ⟨r.head hrne, by rw [e1]; exact List.mem_toFinset.mpr (List.head_mem hrne)⟩ hne
    · exact ⟨hcB, hnil⟩
  -- The partition.
  have hpart : F.2.IsPartition (coreRotation (L := (compLSFBatch cs U).lsf) σ hG hF) k := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [f1]
      exact hE₁C
    · intro c hc
      rcases hclass c hc with ⟨b, -, v, r, -, -, e2, hv⟩ | ⟨hcB, -, -, e2⟩
      · rw [e2]
        exact hv
      · rw [e2]
        exact hpar0 c hcB
    · intro x hx
      have hxE : x.1 ∈ B.edges \ batchDeletes U := by
        rw [mem_edgeEnds, f1] at hx
        exact hx
      obtain ⟨rr, hrr, hxr⟩ := List.mem_flatten.mp ((hcover (B.bundleOf x) x).mpr ⟨hxE, rfl⟩)
      obtain ⟨vr, hvr, rfl⟩ := List.mem_map.mp hrr
      have hpB : (B.bundleOf x, bundleRunsOf (compLSFBatch cs U).RF.R cord
          (B.edges \ batchDeletes U) B (B.bundleOf x)) ∈ plan :=
        List.mem_map.mpr ⟨B.bundleOf x, (Finset.mem_sort _).mpr (hlive' x hxE), rfl⟩
      obtain ⟨c, hc, e1, e2⟩ := f8 _ hpB vr hvr
      have hxc : x ∈ F.2.ends c := by
        rw [e1]
        exact List.mem_toFinset.mpr hxr
      rw [((BundleState.mem_ends _ _ _).mp hxc).2, e2]
      exact ⟨hc, (hrun _ _ _ (mem_bundleRunsOf hvr).2 x hxr).2.1.symm⟩
    · intro c hc
      rcases hclass c hc with ⟨b, hb, v, r, hr, e1, e2, -⟩ | ⟨-, -, e1, -⟩
      · rw [e1, e2, f1, hcord]
        refine ⟨(Finset.card_le_card fun x hx => ?_).trans (hk b hb), ?_⟩
        · obtain ⟨hxE, -, hxb⟩ := hrun b v r hr x (List.mem_toFinset.mp hx)
          exact (BundleState.mem_ends _ _ _).mpr ⟨hE₁B hxE, hxb⟩
        · have hp : (fun x => decide (x ∈ r.toFinset)) = fun x => decide (x ∈ r) := by
            funext x
            simp
          rw [hp]
          exact cycRuns_isArc (pb b) (hxsnd v) hr
      · rw [e1]
        exact ⟨by simp, ⟨[], _, List.IsRotated.refl _, by simp, by simp⟩⟩
  -- Going back from `Bw` to the old bundles.
  obtain ⟨o, ho1, ho2, ho3, -⟩ := delSplit_back hwv hwt fun e he =>
    ⟨hlive (e, true) ((mem_edgeEnds _ _).mpr he), hlive (e, false) ((mem_edgeEnds _ _).mpr he)⟩
  have hoBw : ∀ x : End, x.1 ∈ B.edges \ batchDeletes U → o (Bw.bundleOf x) = B.bundleOf x := by
    intro x hx
    have hxw : x.1 ∈ (B.graph.applyBatch UBw).E := by
      rw [← hwg]
      change x.1 ∈ Bw.edges
      rw [hwE]
      exact hx
    obtain ⟨t, h⟩ := ho2 x.1 hxw
    obtain ⟨e, side⟩ := x
    cases side
    · have h' : Bw.bundleOf (e, false) = (B.graph.applyBatch UBw).head e := by rw [← hwg]; rfl
      rw [h']
      exact h
    · have h' : Bw.bundleOf (e, true) = (B.graph.applyBatch UBw).tail e := by rw [← hwg]; rfl
      rw [h']
      exact t
  have hBVw : B.vertices ⊆ Bw.vertices := by
    have h : Bw.vertices = (B.graph.applyBatch UBw).V := by rw [← hwg]; rfl
    rw [h]
    exact ho3
  -- All ends that share a bundle of `Bw` with an end of a run lie in that run.
  have hK : ∀ c ∈ F.2.vertices, ∀ x ∈ F.2.ends c, ∀ y : End, y.1 ∈ B.edges \ batchDeletes U →
      Bw.bundleOf y = Bw.bundleOf x → y ∈ F.2.ends c := by
    intro c hc x hx y hy hxy
    rcases hclass c hc with ⟨b, -, v, r, hr, e1, -, -⟩ | ⟨-, -, e1, -⟩
    swap
    · rw [e1] at hx
      simp at hx
    rw [e1, List.mem_toFinset] at hx ⊢
    obtain ⟨hxE, hxs, hxb⟩ := hrun b v r hr x hx
    obtain ⟨hwV, hwpar⟩ := hw3 x hxE
    have harc := (hwp.2.2.2 _ hwV).2
    rw [hwpar, hxs, hcord, hwE] at harc
    have hinw : ∀ z : End, z.1 ∈ B.edges \ batchDeletes U → Bw.bundleOf z = Bw.bundleOf x →
        decide (z ∈ Bw.ends (Bw.bundleOf x)) = true := fun z hz h =>
      decide_eq_true ((BundleState.mem_ends _ _ _).mpr ⟨hwE ▸ hz, h⟩)
    have hqp : ∀ z ∈ xs v, decide (z ∈ Bw.ends (Bw.bundleOf x)) = true → pb b z = true := by
      intro z hz hq
      have hzw := (BundleState.mem_ends _ _ _).mp (of_decide_eq_true hq)
      have hzE : z.1 ∈ B.edges \ batchDeletes U := hwE ▸ hzw.1
      have h := hoBw z hzE
      rw [hzw.2, hoBw x hxE, hxb] at h
      simp [pb, ← h]
    have hxv : x ∈ xs v := (hmemxs v x).mpr ⟨hxE, hxs⟩
    obtain ⟨r', hr', hall⟩ := cycRuns_block (pb b) _ harc hqp ⟨x, hxv, hinw x hxE rfl⟩
    have hyv : y ∈ xs v := (hmemxs v y).mpr ⟨hy, (hw3 y hy).2.symm.trans (by
      rw [hxy]
      exact hwpar.trans hxs)⟩
    have hrr := runs_eq_of_mem (cycRuns_flatten_nodup (pb b) (hxsnd v)) hr hr' hx
      (hall x hxv (hinw x hxE rfl))
    rw [hrr]
    exact hall y hyv (hinw y hy hxy)
  -- The count.
  let f : ℕ → ℕ := fun c => if h : (F.2.ends c).Nonempty then Bw.bundleOf h.choose else c
  have hf1 : ∀ c (h : (F.2.ends c).Nonempty), f c = Bw.bundleOf h.choose :=
    fun c h => dite_eq_left h
  have hf2 : ∀ c, ¬ (F.2.ends c).Nonempty → f c = c := fun c h => dite_eq_right h
  have hcard : F.2.vertices.card ≤ Bw.vertices.card := by
    refine Finset.card_le_card_of_injOn f (fun c hc => ?_) (fun c1 hc1 c2 hc2 heq => ?_)
    · by_cases h : (F.2.ends c).Nonempty
      · rw [hf1 c h]
        exact (hw3 _ (hendsE c _ h.choose_spec)).1
      · rw [hf2 c h]
        exact hBVw (hempty c hc h).1
    · -- An old bundle without ends is not the image of a run.
      have hmixed : ∀ c c', c ∈ F.2.vertices → c' ∈ F.2.vertices → (h : (F.2.ends c).Nonempty) →
          ¬ (F.2.ends c').Nonempty → Bw.bundleOf h.choose ≠ c' := by
        intro c c' _ hc' h h' heq'
        obtain ⟨hc'B, hnil⟩ := hempty c' hc' h'
        have hxE := hendsE c _ h.choose_spec
        have hb := hoBw _ hxE
        rw [heq', ho1 c' hc'B] at hb
        have hmem := (hcover c' h.choose).mpr ⟨hxE, hb.symm⟩
        rw [hnil] at hmem
        simp at hmem
      by_cases h1 : (F.2.ends c1).Nonempty <;> by_cases h2 : (F.2.ends c2).Nonempty
      · rw [hf1 c1 h1, hf1 c2 h2] at heq
        have hin := hK c1 hc1 _ h1.choose_spec _ (hendsE c2 _ h2.choose_spec) heq.symm
        exact ((BundleState.mem_ends _ _ _).mp hin).2.symm.trans
          ((BundleState.mem_ends _ _ _).mp h2.choose_spec).2
      · rw [hf1 c1 h1, hf2 c2 h2] at heq
        exact absurd heq (hmixed c1 c2 hc1 hc2 h1 h2)
      · rw [hf2 c1 h1, hf1 c2 h2] at heq
        exact absurd heq.symm (hmixed c2 c1 hc2 hc1 h2 h1)
      · rw [hf2 c1 h1, hf2 c2 h2] at heq
        exact heq
  -- The parents.
  have hpar3 : ∀ c ∈ F.2.vertices,
      (∃ x ∈ F.2.ends c, F.2.parent c = Bw.parent (Bw.bundleOf x)) ∨
        (c ∈ B.vertices ∧ F.2.parent c = B.parent c) := by
    intro c hc
    rcases hclass c hc with ⟨b, -, v, r, hr, e1, e2, -⟩ | ⟨hcB, -, -, e2⟩
    · obtain ⟨hne, -⟩ := cycRuns_spec _ _ r hr
      have hxr : r.head hne ∈ r := List.head_mem hne
      obtain ⟨hxE, hxs, -⟩ := hrun b v r hr _ hxr
      refine Or.inl ⟨r.head hne, by rw [e1]; exact List.mem_toFinset.mpr hxr, ?_⟩
      rw [e2, (hw3 _ hxE).2, hxs]
    · exact Or.inr ⟨hcB, e2⟩
  -- The emitted batch.
  have hdelsplit : ∀ op ∈ dels, ∃ e ∈ B.edges, op = .delete e ∧ e ∈ batchDeletes U := by
    intro op hop
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hop
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp ((Finset.mem_sort _).mp he)
    exact ⟨e, h1, rfl, h2⟩
  have hnewDel : ∀ op ∈ newOps, deleteTag op = false := by
    intro op hop
    exact (split_tags op (f4b op hop)).1
  have hdelsSplit : batchSplitCount dels = 0 := by
    rw [batchSplitCount, List.countP_eq_zero]
    intro op hop
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hop
    simp [isSplit]
  have hz : newOps.countP deleteTag = 0 :=
    List.countP_eq_zero.mpr fun op hop => by rw [hnewDel op hop]; simp
  refine ⟨hpart, hcard, hpar3, fun c hc => f10 c hc, f3, f2, ?_, ?_, ?_, ?_, f1, f6⟩
  · intro op hop
    rw [f4a] at hop
    rcases List.mem_append.mp hop with hop | hop
    · obtain ⟨e, -, rfl, -⟩ := hdelsplit op hop
      trivial
    · exact (split_tags op (f4b op hop)).2
  · intro op hop hdt
    rw [f4a] at hop
    rcases List.mem_append.mp hop with hop | hop
    · exact hdelsplit op hop
    · rw [hnewDel op hop] at hdt
      exact absurd hdt (by simp)
  · rw [f4a, List.countP_append, hz, Nat.add_zero]
    refine (List.countP_le_length).trans ?_
    rw [List.length_map, Finset.length_sort]
    exact (Finset.card_le_card Finset.inter_subset_right).trans (batchDeletes_card_le U)
  · rw [f5, f4a, batchSplitCount_append, hdelsSplit, f4c, Nat.zero_add]

end MinCostFlow.SparseCore
