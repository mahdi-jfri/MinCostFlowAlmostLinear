module

public import MinCostFlow.Bundle.SplitFibers
import MinCostFlow.SparseCore.GraphHelpers
import MinCostFlow.DynSpanner.Walks

/-!
# Preservation of the bundle partition

A run inherits its arc from the restricted core rotation. The fold keeps
the contents of every bundle that it has not reached and preserves each
bundle whose split it has completed.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.SparseCore

private def GoodAt {C : MGraph} (B : BundleState) (ρ : Rotation C) (k b : ℕ) : Prop :=
  B.parent b ∈ C.V ∧
  (∀ x ∈ B.ends b, C.src x = B.parent b) ∧
  (B.ends b).card ≤ k ∧
  IsArc (fun x => decide (x ∈ B.ends b)) (restrictedEnds ρ B.edges (B.parent b))

private theorem goodAt_congr {C : MGraph} {ρ : Rotation C} {k b : ℕ} {B B' : BundleState}
    (hE : B'.edges = B.edges) (he : B'.ends b = B.ends b)
    (hp : B'.parent b = B.parent b) (h : GoodAt B ρ k b) : GoodAt B' ρ k b := by
  unfold GoodAt at h ⊢
  rw [hE, he, hp]
  exact h

private theorem goodAt_empty {C : MGraph} {ρ : Rotation C} {k b : ℕ} {B : BundleState}
    (he : B.ends b = ∅) (hv : B.parent b ∈ C.V) : GoodAt B ρ k b := by
  refine ⟨hv, ?_, ?_, ?_⟩
  · simp [he]
  · simp [he]
  · refine ⟨[], restrictedEnds ρ B.edges (B.parent b), ?_, by simp, by simp [he]⟩
    rw [List.nil_append]

private theorem restricted_side {C : MGraph} {ρ : Rotation C} {β v v' : ℕ} {St Sh : Finset ℕ}
    {σ : Rotation (C.applyUpdate (.split v v' St Sh))}
    (h : RotationStep β (.split v v' St Sh) ρ σ) (E : Finset ℕ) (side : Bool) :
    (restrictedEnds σ E (if side then v' else v)).IsRotated
      ((restrictedEnds ρ E v).filter fun x => splitEnds St Sh x == side) := by
  let q : End → Bool := fun x => decide (x.1 ∈ E)
  have hcomm (p : End → Bool) :
      ((ρ.order v).filter p).filter q = ((ρ.order v).filter q).filter p := by
    simp only [List.filter_filter, Bool.and_comm]
  cases side
  · have hh := isRotated_filter q h.1
    rw [hcomm] at hh
    have htest : (fun x => splitEnds St Sh x == false) = fun x => !(splitEnds St Sh x) := by
      funext x; cases splitEnds St Sh x <;> rfl
    simp only [htest]
    exact hh
  · have hh := isRotated_filter q h.2.1
    rw [hcomm] at hh
    have htest : (fun x => splitEnds St Sh x == true) = splitEnds St Sh := by
      funext x; cases splitEnds St Sh x <;> rfl
    simp only [htest]
    exact hh

private theorem goodAt_run {C : MGraph} {ρ : Rotation C} {v v' β k : ℕ} {St Sh : Finset ℕ}
    {σ : Rotation (C.applyUpdate (.split v v' St Sh))}
    (h : RotationStep β (.split v v' St Sh) ρ σ) (hv : v ∈ C.V)
    {B : BundleState} {b : ℕ} {run : List End}
    (hends : B.ends b = run.toFinset)
    (hpar : B.parent b = if run.head?.any (splitEnds St Sh) then v' else v)
    (hSrc : ∀ x ∈ run, C.src x = v)
    (hRun : run.length ≤ k ∧ ∃ side : Bool, (∀ x ∈ run, splitEnds St Sh x = side) ∧
      IsArc (fun x => run.contains x) ((restrictedEnds ρ B.edges v).filter
        fun x => splitEnds St Sh x == side)) :
    GoodAt B σ k b := by
  have hV : B.parent b ∈ (C.applyUpdate (.split v v' St Sh)).V := by
    rw [hpar]
    change (if run.head?.any (splitEnds St Sh) then v' else v) ∈ insert v' C.V
    split
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem hv
  cases run with
  | nil => exact goodAt_empty (by simpa using hends) hV
  | cons x xs =>
    obtain ⟨hlen, side, hs, harc⟩ := hRun
    have hhead : (x :: xs).head?.any (splitEnds St Sh) = side := hs x List.mem_cons_self
    rw [hhead] at hpar
    refine ⟨hV, ?_, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ x :: xs := List.mem_toFinset.mp (hends ▸ hy)
      rw [src_applySplit, hSrc y hy', hs y hy', hpar]
      simp
    · rw [hends]
      exact (List.toFinset_card_le _).trans hlen
    · rw [hpar, hends]
      apply IsArc.congr_on (harc.of_isRotated (restricted_side h B.edges side))
      intro y _
      apply Bool.eq_iff_iff.mpr
      simp

private theorem goodAt_unaffected {C : MGraph} {ρ : Rotation C} {v v' β k : ℕ} {St Sh : Finset ℕ}
    {σ : Rotation (C.applyUpdate (.split v v' St Sh))}
    (h : RotationStep β (.split v v' St Sh) ρ σ) (hf : v' ∉ C.V)
    {B : BundleState} {b : ℕ} (hp : B.parent b ≠ v)
    (h0 : GoodAt B ρ k b) : GoodAt B σ k b := by
  obtain ⟨hv, hsrc, hsize, harc⟩ := h0
  have hp' : B.parent b ≠ v' := fun h => hf (h ▸ hv)
  refine ⟨Finset.mem_insert_of_mem hv, ?_, hsize, ?_⟩
  · intro x hx
    rw [src_applySplit, hsrc x hx]
    simp [hp]
  · exact harc.of_isRotated (isRotated_filter _ (h.2.2.2 _ hp hp'))


private theorem plan_parent {C : MGraph} (B : BundleState) (ρ : Rotation C) (v b : ℕ)
    (moved : End → Bool) (rs : List (List End))
    (h : (b, rs) ∈ bundleSplitPlan ρ B v moved) : B.parent b = v := by
  obtain ⟨c, hc, he⟩ := List.mem_map.mp h
  have hab : c = b := (Prod.mk.inj he).1
  subst c
  exact (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hc)).2

private theorem plan_names {C : MGraph} (B : BundleState) (ρ : Rotation C) (v : ℕ)
    (moved : End → Bool) :
    (bundleSplitPlan ρ B v moved).map Prod.fst =
      (B.vertices.filter fun b => B.parent b = v).sort (· ≤ ·) := by
  simp [bundleSplitPlan, List.map_map, Function.comp_def]

private theorem valid_applyBatch_bundle {G : MGraph} (hG : G.IsValid) {U : List Update}
    (hU : G.BatchIsValid U) : (G.applyBatch U).IsValid := by
  induction U generalizing G with
  | nil => exact hG
  | cons u us ih =>
    exact ih (MinCostFlow.DynSpanner.isValid_applyUpdate_any hG hU.1) hU.2

/-- The run splits preserve the partition into arcs of size at most the
bundle cap, with parents in the new core graph. -/
theorem BundleState.split_preserves {C : MGraph} {ρ : Rotation C} {B : BundleState}
    {k v v' β : ℕ} {St Sh : Finset ℕ}
    {σ : Rotation (C.applyUpdate (.split v v' St Sh))}
    (h : B.IsPartition ρ k) (hu : C.UpdateIsValid (.split v v' St Sh))
    (hσ : RotationStep β (.split v v' St Sh) ρ σ) :
    (B.split ρ v v' St Sh).2.IsPartition σ k := by
  let p := splitEnds St Sh
  let full := bundleSplitPlan ρ B v p
  let step := bundleSplitFoldStep v v' p
  let C' := C.applyUpdate (.split v v' St Sh)
  have hv' : v' ∈ C'.V := Finset.mem_insert_self _ _
  have hvold : v ∈ C'.V := Finset.mem_insert_of_mem hu.1
  have hAux : ∀ (plan : List (ℕ × List (List End))) (s : List Update × BundleState),
      plan ⊆ full → (plan.map Prod.fst).Nodup →
      s.2.edges = B.edges → s.2.graph.IsValid →
      (∀ (b : ℕ) (runs : List (List End)), (b, runs) ∈ plan →
        b ∈ s.2.vertices ∧ s.2.ends b = B.ends b ∧ s.2.parent b = B.parent b) →
      (∀ b ∈ s.2.vertices, b ∉ plan.map Prod.fst → GoodAt s.2 σ k b) →
      let st := (plan.foldl step s).2
      st.edges = B.edges ∧ st.graph.IsValid ∧ ∀ b ∈ st.vertices, GoodAt st σ k b := by
    intro plan
    induction plan with
    | nil =>
      intro s _ _ he hv _ hg
      exact ⟨he, hv, fun b hb => hg b hb (by simp)⟩
    | cons entry rest ih =>
      intro s hsub hn he hv hPending hDone
      obtain ⟨b, runs⟩ := entry
      obtain ⟨ops, st⟩ := s
      let next := st.vertices.sup id + 1
      let s' := step (ops, st) (b, runs)
      have hEntry : (b, runs) ∈ full := hsub List.mem_cons_self
      obtain ⟨_, hnd, hEndB⟩ := bundleSplitPlan_entry h p hEntry
      obtain ⟨hb, hbEnds, hbParent⟩ := hPending b runs List.mem_cons_self
      have hp : st.parent b = v := hbParent.trans (plan_parent B ρ v b p runs hEntry)
      have hEnds (x : End) : x ∈ runs.flatten ↔ x.1 ∈ st.edges ∧ st.bundleOf x = b := by
        rw [hEndB, ← B.mem_ends, ← hbEnds, st.mem_ends]
      have hfresh : ∀ c ∈ st.vertices, c < next :=
        fun _ hc => Nat.lt_succ_of_le (Finset.le_sup (f := id) hc)
      have hlive (x : End) (hx : x.1 ∈ st.edges) : st.bundleOf x ∈ st.vertices := by
        obtain ⟨e, side⟩ := x
        have hz := hv e hx
        cases side
        · exact hz.2
        · exact hz.1
      obtain ⟨he', hvs, hunchanged, hbEnds', hbParent', hnew⟩ :=
        bundleSplitFoldStep_fibers v v' b p st ops runs hb hlive hnd hEnds
      have hEqE : s'.2.edges = B.edges := he'.trans he
      have hValid' : s'.2.graph.IsValid := by
        have hU := bundleRunUpdates_valid st.graph b next runs hb hfresh hnd (fun x hx =>
          let hh := (hEnds x).mp hx; ⟨hh.1, (st.graph_src x).trans hh.2⟩)
        have hG : s'.2.graph = st.graph.applyBatch (bundleRunUpdates b next runs) :=
          bundleGraph_of_applied _ _
        rw [hG]
        exact valid_applyBatch_bundle hv hU
      have hGoodRun (rs : List End) (hr : rs ∈ runs) (c : ℕ)
          (hEnds' : s'.2.ends c = rs.toFinset)
          (hParent' : s'.2.parent c = if rs.head?.any p then v' else v) :
          GoodAt s'.2 σ k c := by
        have hr' := bundleSplitPlan_runs_spec h p hEntry hr
        apply goodAt_run hσ hu.1 hEnds' hParent' ?_ ?_
        · intro x hx
          have hs := (hEndB x).mp (List.mem_flatten_of_mem hr hx)
          have hxe := (h.2.2.1 x ((mem_edgeEnds _ _).mpr hs.1)).2
          rw [hs.2, plan_parent B ρ v b p runs hEntry] at hxe
          exact hxe.symm
        · rw [hEqE]
          exact hr'
      simp only [List.map_cons, List.nodup_cons] at hn
      rw [List.foldl_cons]
      apply ih s' (fun _ ha => hsub (List.mem_cons_of_mem _ ha)) hn.2 hEqE hValid'
      · intro c rs hc
        have hne : c ≠ b := fun hh => hn.1 (hh ▸ List.mem_map_of_mem hc)
        obtain ⟨hcV, hcEnd, hcPar⟩ := hPending c rs (List.mem_cons_of_mem _ hc)
        obtain ⟨hEnd', hPar'⟩ := hunchanged c hcV hne
        exact ⟨(hvs c).mpr (Or.inl hcV), hEnd'.trans hcEnd, hPar'.trans hcPar⟩
      · intro c hc hcP
        rcases (hvs c).mp hc with hcOld | ⟨i, hi, rfl⟩
        · by_cases hcb : c = b
          · subst c
            cases runs with
            | nil =>
              have hp' : s'.2.parent b = v := hbParent'.trans hp
              exact goodAt_empty (by simpa using hbEnds') (hp' ▸ hvold)
            | cons r rs =>
              exact hGoodRun r List.mem_cons_self b hbEnds' hbParent'
          · obtain ⟨hcEnd, hcPar⟩ := hunchanged c hcOld hcb
            have hcDone : c ∉ ((b, runs) :: rest).map Prod.fst := by
              simp [hcb, hcP]
            exact goodAt_congr he' hcEnd hcPar (hDone c hcOld hcDone)
        · obtain ⟨hef, hpf⟩ := hnew i hi
          exact hGoodRun _ ((List.drop_sublist _ _).subset (List.getElem_mem hi)) _ hef hpf
  have hfull : (full.map Prod.fst).Nodup := by
    rw [plan_names]
    exact Finset.sort_nodup _ _
  obtain ⟨he, hv, hg⟩ := hAux full ([], B) (fun _ hx => hx) hfull rfl
    (BundleState.graph_isValid h)
    (fun b rs hr => ⟨(bundleSplitPlan_entry h p hr).1, rfl, rfl⟩)
    (fun b hb hout => by
      have hp : B.parent b ≠ v := by
        intro heq
        apply hout
        rw [plan_names]
        exact (Finset.mem_sort _).mpr (Finset.mem_filter.mpr ⟨hb, heq⟩)
      have hOld : GoodAt B ρ k b := by
        obtain ⟨hsize, harc⟩ := h.2.2.2 b hb
        refine ⟨h.2.1 b hb, ?_, hsize, harc⟩
        intro x hx
        obtain ⟨he, hxb⟩ := (B.mem_ends b x).mp hx
        exact (hxb ▸ (h.2.2.1 x ((mem_edgeEnds _ _).mpr he)).2).symm
      exact goodAt_unaffected hσ hu.2.1 hp hOld)
  let out := (B.split ρ v v' St Sh).2
  have houtE : out.edges = B.edges := he
  refine ⟨?_, fun b hb => (hg b hb).1, ?_, fun b hb => (hg b hb).2.2⟩
  · intro e he
    have h' : e ∈ B.edges := houtE ▸ he
    exact h.1 h'
  · intro x hx
    have he' := (mem_edgeEnds _ _).mp hx
    have hb : out.bundleOf x ∈ out.vertices := by
      obtain ⟨e, side⟩ := x
      have hz := hv e he'
      cases side
      · exact hz.2
      · exact hz.1
    exact ⟨hb, ((hg _ hb).2.1 x ((out.mem_ends _ _).mpr ⟨he', rfl⟩)).symm⟩

end MinCostFlow.Bundle
