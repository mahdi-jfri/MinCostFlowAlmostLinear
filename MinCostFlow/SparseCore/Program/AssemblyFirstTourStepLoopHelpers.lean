module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepWalls

import Mathlib.Tactic

/-!
# Pure helpers and loop-body syntax for `asmFirstTourBlockStepStmt` (`AssemblyFirstTourStepLoopHelpers`)

Provides:
1. Pure helpers for `OrdEditsValidFor`, `splitQuietPrefix`, `ordG_step_*`, `inputMid_wall_props`,
   and `tourMove_forest_graphEq`.
2. `wallStep_tailChain`: constructs the combined `TourRelChain` (releases of `u` followed by all
   releases of `splitQuietPrefix cs1 U_rest`) and split-list decomposition shared identically by
   forest-delete and vertex-split iterations.
3. Parametric loop cost multiplier `tourBlockLoopMul`, exact loop body `asmFirstTourLoopBody`, and
   right-associativity helpers `runs_seq_r*`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. Pure helpers for `OrdEditsValidFor`, quiet prefixes, and `inputMid` -/

public section

theorem ordEditsValidFor_cons {vCap eCap : ℕ} {ord : ℕ → List End} {d : OrdEdit} {ed : List OrdEdit}
    (h : OrdEditsValidFor vCap eCap ord (d :: ed)) :
    OrdEditsWithin vCap eCap [d] ∧ OrdEditsValidFor vCap eCap (applyOrdEdit ord d) ed := by
  refine ⟨fun x hx => h.1 x (by simp at hx; subst hx; exact List.mem_cons_self),
    fun x hx => h.1 x (List.mem_cons_of_mem _ hx), fun k hk => ?_⟩
  have h1 := h.2 (k + 1) (Nat.succ_le_succ hk)
  simpa [applyOrdEdits, List.take_succ_cons] using h1

theorem ordEditsValidFor_rot_tourEditsValid {vCap eCap : ℕ} :
    ∀ (rotEds : List OrdEdit) (s : TourAbs),
      (∀ d ∈ rotEds, d.IsRotate) →
      OrdEditsWithin vCap eCap rotEds →
      TourValid vCap eCap s →
      TourEditsValid vCap eCap s rotEds ∧ TourValid vCap eCap (tourApplyEdits s rotEds)
  | [], s, _, _, hv => ⟨trivial, hv⟩
  | d :: ds, s, hrot, hwin, hv => by
    have hd : d.IsRotate := hrot d List.mem_cons_self
    cases d with
    | rotateTo v y =>
      have hw0 : v < vCap ∧ y.1 < eCap := hwin (.rotateTo v y) List.mem_cons_self
      have hv1 : TourValid vCap eCap (tourApplyEdit s (.rotateTo v y)) :=
        tourValid_applyEdit_rotateTo hv hw0.1
      have ih := ordEditsValidFor_rot_tourEditsValid ds (tourApplyEdit s (.rotateTo v y))
        (fun x hx => hrot x (List.mem_cons_of_mem _ hx))
        (fun x hx => hwin x (List.mem_cons_of_mem _ hx)) hv1
      exact ⟨⟨hw0, ih.1⟩, ih.2⟩
    | dropEdge _ | moveEnds _ _ _ _ | insertBefore _ _ _ => simp [OrdEdit.IsRotate] at hd

theorem splitQuietPrefix_all_quiet (cs : CompLSFState) :
    ∀ (U : List Update) (i : ℕ) (hi : i < (splitQuietPrefix cs U).1.length),
      isQuietUpdate (compLSFBatch cs ((splitQuietPrefix cs U).1.take i))
        ((splitQuietPrefix cs U).1[i]'hi) = true
  | [], _, hi => by simp [splitQuietPrefix] at hi
  | u :: U, i, hi => by
    unfold splitQuietPrefix at hi ⊢
    by_cases hq : isQuietUpdate cs u = true
    · simp only [hq, ↓reduceIte] at hi ⊢
      cases i with
      | zero => simpa [compLSFBatch] using hq
      | succ j =>
        have ih := splitQuietPrefix_all_quiet (compLSFStepSingle cs u) U j (by simpa using hi)
        simpa [compLSFBatch, List.take_succ_cons] using ih
    · have hnq : isQuietUpdate cs u = false := by cases h : isQuietUpdate cs u <;> simp_all
      simp [hnq] at hi

theorem splitQuietPrefix_snd_head (cs : CompLSFState) :
    ∀ (U : List Update) (u : Update) (rest : List Update),
      (splitQuietPrefix cs U).2 = u :: rest →
      isQuietUpdate (compLSFBatch cs (splitQuietPrefix cs U).1) u = false
  | [], _, _, h => by simp [splitQuietPrefix] at h
  | a :: U, u, rest, h => by
    unfold splitQuietPrefix at h ⊢
    by_cases hq : isQuietUpdate cs a = true
    · simp only [hq, ↓reduceIte] at h ⊢
      simpa [compLSFBatch] using splitQuietPrefix_snd_head (compLSFStepSingle cs a) U u rest h
    · have hnq : isQuietUpdate cs a = false := by cases h' : isQuietUpdate cs a <;> simp_all
      simp only [hnq, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases h; simpa [compLSFBatch] using hnq

theorem splitQuietPrefix_snd_stop (cs : CompLSFState) (U : List Update) :
    ∀ e rest,
      canonSplitList (compLSFBatch cs (splitQuietPrefix cs U).1) (splitQuietPrefix cs U).2 =
        e :: rest → e.isRelease = false := by
  intro e rest h
  have h2 := splitLeadingReleases_canonSplitList cs U
  have h3 := splitLeadingReleases_snd_head (canonSplitList cs U) e rest (by rw [h2]; exact h)
  exact h3

theorem quietPrefix_G_V_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (Uq : List Update) (cs : CompLSFState),
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid Uq →
      (∀ i (hi : i < Uq.length), isQuietUpdate (compLSFBatch cs (Uq.take i)) (Uq[i]'hi) = true) →
      (compLSFBatch cs Uq).G.V = cs.G.V
  | [], _, _, _, _ => rfl
  | u :: Uq, cs, hI, hBU, hQ => by
    have hq0 : isQuietUpdate cs u = true := by simpa [compLSFBatch] using hQ 0 (Nat.zero_lt_succ _)
    have h1 := compLSFStepSingle_forest_props hI hBU.1
    have hV1 : (compLSFStepSingle cs u).G.V = cs.G.V := by
      rw [h1.2.1]; cases u with
      | insert => rfl
      | delete => rfl
      | split => simp [isQuietUpdate] at hq0
    have hQ1 : ∀ i (hi : i < Uq.length),
        isQuietUpdate (compLSFBatch (compLSFStepSingle cs u) (Uq.take i)) (Uq[i]'hi) = true :=
      fun i hi => by simpa [compLSFBatch, List.take_succ_cons] using hQ (i + 1) (Nat.succ_lt_succ hi)
    exact (quietPrefix_G_V_eq Uq (compLSFStepSingle cs u) h1.1 (h1.2.1.symm ▸ hBU.2) hQ1).trans hV1

theorem ordG_step_insert {G : MGraph} {ord : ℕ → List End} {e a b : ℕ} {y₁ y₂ : Option End}
    (hordG : ∀ v x, x ∈ ord v ↔ x.1 ∈ G.E ∧ G.src x = v) (he : e ∉ G.E) :
    let ord' := applyOrdEdits ord [.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]
    let G' := G.applyUpdate (.insert e a b)
    ∀ v x, x ∈ ord' v ↔ x.1 ∈ G'.E ∧ G'.src x = v := by
  intro ord' G' v x
  have hmem_ib : ∀ (o : ℕ → List End) (w : ℕ) (z : End) (y : Option End) (u : ℕ),
      x ∈ applyOrdEdit o (.insertBefore w z y) u ↔ (u = w ∧ x = z) ∨ x ∈ o u := by
    intro o w z y u
    change x ∈ Function.update o w (insertBeforeList z y (o w)) u ↔ _
    by_cases huw : u = w
    · subst huw; simp only [Function.update_self, true_and]
      cases y with
      | none => simp [insertBeforeList, or_comm]
      | some y0 =>
        simp only [insertBeforeList, List.mem_append, List.mem_cons]
        have hs : x ∈ o u ↔ x ∈ (o u).take ((o u).idxOf y0) ∨ x ∈ (o u).drop ((o u).idxOf y0) := by
          conv_lhs => rw [← List.take_append_drop ((o u).idxOf y0) (o u)]
          exact List.mem_append
        tauto
    · rw [Function.update_of_ne huw]; simp [huw]
  change x ∈ applyOrdEdit (applyOrdEdit ord (.insertBefore a (e, true) y₁))
    (.insertBefore b (e, false) y₂) v ↔ _
  rw [hmem_ib, hmem_ib, hordG]
  obtain ⟨f, fb⟩ := x
  by_cases hfe : f = e
  · subst hfe; cases fb <;> simp [G', MGraph.applyUpdate, MGraph.src, he, eq_comm]
  · cases fb <;> simp [G', MGraph.applyUpdate, MGraph.src, hfe]

theorem ordG_step_delete {G : MGraph} {ord : ℕ → List End} {e : ℕ}
    (hordG : ∀ v x, x ∈ ord v ↔ x.1 ∈ G.E ∧ G.src x = v) :
    let ord' := applyOrdEdit ord (.dropEdge e)
    let G' := G.applyUpdate (.delete e)
    ∀ v x, x ∈ ord' v ↔ x.1 ∈ G'.E ∧ G'.src x = v := by
  intro ord' G' v x
  change x ∈ (ord v).filter (fun z => z.1 != e) ↔ _
  simp only [List.mem_filter, bne_iff_ne, hordG, G', MGraph.applyUpdate, Finset.mem_erase, MGraph.src]
  tauto

theorem ordG_step_split {G : MGraph} {ord : ℕ → List End} {v v' : ℕ} {St Sh : Finset ℕ}
    {sel : Finset End} {c : Bool}
    (hordG : ∀ u x, x ∈ ord u ↔ x.1 ∈ G.E ∧ G.src x = u)
    (hu : G.UpdateIsValid (.split v v' St Sh)) (hG : G.IsValid)
    (hmov : ∀ x : End, x.1 ∈ G.E → G.src x = v → movedBy sel c x = splitEnds St Sh x) :
    let ord' := applyOrdEdit ord (.moveEnds v v' sel c)
    let G' := G.applyUpdate (.split v v' St Sh)
    ∀ u x, x ∈ ord' u ↔ x.1 ∈ G'.E ∧ G'.src x = u := by
  intro ord' G' u x
  have hvv' : v ≠ v' := fun h => hu.2.1 (h ▸ hu.1)
  have hnotv' : ∀ z : End, z.1 ∈ G.E → G.src z ≠ v' := fun z hz hsrc => by
    obtain ⟨f, fb⟩ := z; cases fb
    · exact hu.2.1 (hsrc ▸ (hG f hz).2)
    · exact hu.2.1 (hsrc ▸ (hG f hz).1)
  have hordv' : ord v' = [] := List.eq_nil_iff_forall_not_mem.mpr fun z hz =>
    hnotv' z ((hordG v' z).mp hz).1 ((hordG v' z).mp hz).2
  change x ∈ applyOrdEdit ord (.moveEnds v v' sel c) u ↔ x.1 ∈ G.E ∧ _
  rw [src_applyUpdate_split]
  by_cases h1 : u = v
  · subst h1
    simp only [applyOrdEdit, ↓reduceIte, List.mem_filter, Bool.not_eq_true', hordG]
    constructor
    · rintro ⟨⟨hxE, hxs⟩, hnm⟩
      refine ⟨hxE, ?_⟩
      have hsp : splitEnds St Sh x = false := (hmov x hxE hxs).symm.trans hnm
      have hcond : ¬((if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ G.src x = u) := by
        intro ⟨h1', _⟩; obtain ⟨f, fb⟩ := x; cases fb <;> simp_all [splitEnds]
      rw [ite_eq_right hcond]; exact hxs
    · rintro ⟨hxE, hxs'⟩
      by_cases hcond : (if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ G.src x = u
      · rw [ite_eq_left hcond] at hxs'; exact absurd hxs' hvv'.symm
      · rw [ite_eq_right hcond] at hxs'
        refine ⟨⟨hxE, hxs'⟩, ?_⟩
        rw [hmov x hxE hxs']
        obtain ⟨f, fb⟩ := x; cases fb <;> simp_all [splitEnds]
  · by_cases h2 : u = v'
    · subst h2
      simp only [applyOrdEdit, h1, ↓reduceIte, hordv', List.nil_append, List.mem_filter, hordG]
      constructor
      · rintro ⟨⟨hxE, hxs⟩, hm⟩
        refine ⟨hxE, ?_⟩
        have hsp : splitEnds St Sh x = true := (hmov x hxE hxs).symm.trans hm
        have hcond : (if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ G.src x = v := by
          refine ⟨?_, hxs⟩; obtain ⟨f, fb⟩ := x; cases fb <;> simp_all [splitEnds]
        rw [ite_eq_left hcond]
      · rintro ⟨hxE, hxs'⟩
        by_cases hcond : (if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ G.src x = v
        · refine ⟨⟨hxE, hcond.2⟩, ?_⟩
          rw [hmov x hxE hcond.2]
          obtain ⟨f, fb⟩ := x; cases fb <;> simp_all [splitEnds]
        · rw [ite_eq_right hcond] at hxs'; exact absurd hxs' (hnotv' x hxE)
    · simp only [applyOrdEdit, h1, h2, ↓reduceIte, hordG]
      constructor
      · rintro ⟨hxE, hxs⟩
        refine ⟨hxE, ?_⟩
        have hcond : ¬((if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ G.src x = v) := fun h => h1 (hxs.symm.trans h.2)
        rw [ite_eq_right hcond]; exact hxs
      · rintro ⟨hxE, hxs'⟩
        by_cases hcond : (if x.2 then x.1 ∈ St else x.1 ∈ Sh) ∧ G.src x = v
        · rw [ite_eq_left hcond] at hxs'; exact absurd hxs'.symm h2
        · rw [ite_eq_right hcond] at hxs'; exact ⟨hxE, hxs'⟩

theorem inputMid_wall_props {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) (hnq : isQuietUpdate cs u = false) :
    let cs1 := compLSFStepSingle cs u
    let mid := inputMid cs u
    let fresh := newRoot mid.F.R cs.RF.R
    mid.F.IsRootedSpanningForestOf cs1.G ∧
    mid.F.F = forestAfterInput cs.RF.F u ∧
    fresh ∉ cs.RF.R ∧ mid.F.R = insert fresh cs.RF.R ∧ mid.F.R ⊆ cs1.RF.R := by
  intro cs1 mid fresh
  obtain ⟨hI1, hG1, hR01, hKF, hKG, hKsub', _, _, _, _⟩ := compLSFStepSingle_forest_props hI hu
  have hF0 := compLSF_RF_isRSF hI
  have hKV : (forestAfterInput cs.RF.F u).V = cs1.G.V := by
    rw [hG1]; cases u with
    | insert => exact hF0.2.1
    | delete => exact hF0.2.1
    | split v v' _ _ => change insert v' cs.RF.F.V = insert v' cs.G.V; rw [hF0.2.1]
  have hsep : ∀ a ∈ cs.RF.R, ∀ b ∈ cs.RF.R, (forestAfterInput cs.RF.F u).Connected a b → a = b := by
    intro a ha b hb hc
    have hconn : cs.RF.F.Connected a b := by
      cases u with
      | insert => exact hc
      | delete e => exact connected_of_subgraph (eraseForestEdge_subgraph _ e) hc
      | split v v' St Sh =>
        have hvf : v' ∉ cs.RF.F.V := fun he => hu.2.1 (hF0.2.1 ▸ he)
        have ha' : a ≠ v' := fun he => hu.2.1 (he ▸ hF0.2.2.1 ha)
        have hb' : b ≠ v' := fun he => hu.2.1 (he ▸ hF0.2.2.1 hb)
        simpa [ha', hb'] using connected_applySplit_proj hF0.1.1 hvf St Sh hc
    have hEq := root_eq_of_connected hF0 (hF0.2.2.1 ha) (hF0.2.2.1 hb) hconn
    rwa [root_eq_of_mem_R hF0 ha, root_eq_of_mem_R hF0 hb] at hEq
  have hF1 := compLSF_RF_isRSF hI1
  obtain ⟨hRo, hRf, hm⟩ := canonRoots_spec hKF hKV hKG hF1 hKsub' hR01 hsep
  cases u with
  | insert _ _ _ => simp [isQuietUpdate] at hnq
  | delete e =>
    have he : e ∈ cs.RF.F.E := by simpa [isQuietUpdate] using hnq
    have hmid : mid = ⟨cs.lsf.T, ⟨forestAfterInput cs.RF.F (.delete e),
        canonRoots (forestAfterInput cs.RF.F (.delete e)) cs.RF.R cs1.RF.R⟩, cs.lsf.wstr⟩ := by
      simp only [mid, inputMid, he, ↓reduceIte]; rfl
    have hcard : mid.F.R.card = cs.RF.R.card + 1 := by
      rw [hmid, ← rootedForest_components_card hm, ← rootedForest_components_card hF0]
      exact forest_eraseEdge_components_card hF0.1 he
    obtain ⟨fr, hfrNot, hRfr⟩ := roots_insert_of_card (hmid ▸ hRo) hcard
    rw [show fresh = fr from newRoot_eq hRfr hfrNot]
    exact ⟨hmid ▸ hm, by rw [hmid], hfrNot, hRfr, hmid ▸ hRf⟩
  | split v v' St Sh =>
    have hmid : mid = ⟨cs.lsf.T, ⟨forestAfterInput cs.RF.F (.split v v' St Sh),
        canonRoots (forestAfterInput cs.RF.F (.split v v' St Sh)) cs.RF.R cs1.RF.R⟩, cs.lsf.wstr⟩ := rfl
    have hcard : mid.F.R.card = cs.RF.R.card + 1 := by
      have ho := rootedForest_R_add_edges hF0
      have hn := rootedForest_R_add_edges hm
      have hv : cs1.G.V.card = cs.G.V.card + 1 := by rw [hG1]; exact Finset.card_insert_of_notMem hu.2.1
      change cs.RF.R.card + cs.RF.F.E.card = cs.G.V.card at ho
      change (canonRoots _ _ _).card + cs.RF.F.E.card = cs1.G.V.card at hn
      rw [hmid]; dsimp only [cs1]; omega
    obtain ⟨fr, hfrNot, hRfr⟩ := roots_insert_of_card (hmid ▸ hRo) hcard
    rw [show fresh = fr from newRoot_eq hRfr hfrNot]
    exact ⟨hmid ▸ hm, by rw [hmid], hfrNot, hRfr, hmid ▸ hRf⟩

theorem tourMove_forest_graphEq {s : TourAbs} {G F_cs : MGraph} {v v' : ℕ}
    {St Sh : Finset ℕ} {sel : Finset End} {c : Bool}
    (hFeq : GraphEq s.rf.F F_cs) (hFsub : G.IsSubgraph F_cs)
    (hordG : ∀ u x, x ∈ s.ord u ↔ x.1 ∈ G.E ∧ G.src x = u)
    (hmov : ∀ x : End, x.1 ∈ G.E → G.src x = v → movedBy sel c x = splitEnds St Sh x) :
    GraphEq (tourApplyEdit s (.moveEnds v v' sel c)).rf.F
      (forestAfterInput F_cs (.split v v' St Sh)) := by
  set moved := ((s.ord v).filter (movedBy sel c)).toFinset
  set StM := (moved.filter fun x => x.2).image Prod.fst
  set ShM := (moved.filter fun x => !x.2).image Prod.fst
  refine ⟨by change insert v' s.rf.F.V = insert v' F_cs.V; rw [hFeq.1], hFeq.2.1, fun e he => ?_⟩
  have heF : e ∈ F_cs.E := hFeq.2.1 ▸ he
  have heG : e ∈ G.E := hFsub.2.1 heF
  constructor
  · change (if e ∈ StM ∧ s.rf.F.tail e = v then v' else s.rf.F.tail e) =
        (if e ∈ St ∧ F_cs.tail e = v then v' else F_cs.tail e)
    rw [(hFeq.2.2 e he).1]
    by_cases htv : F_cs.tail e = v
    · have hGt : G.src (e, true) = v := (hFsub.2.2 e heF).1.symm.trans htv
      have hiff : e ∈ StM ↔ e ∈ St := by
        simp only [StM, moved, Finset.mem_image, Finset.mem_filter, List.mem_toFinset, List.mem_filter, hordG]
        constructor
        · rintro ⟨⟨f, fb⟩, ⟨⟨⟨hfE, hfs⟩, hm⟩, hfb⟩, rfl⟩
          cases fb
          · cases hfb
          · have := (hmov (f, true) hfE hfs).symm.trans hm; simpa [splitEnds] using this
        · intro heSt
          refine ⟨(e, true), ⟨⟨⟨heG, hGt⟩, ?_⟩, rfl⟩, rfl⟩
          rw [hmov (e, true) heG hGt]; simpa [splitEnds] using heSt
      simp [htv, hiff]
    · simp [htv]
  · change (if e ∈ ShM ∧ s.rf.F.head e = v then v' else s.rf.F.head e) =
        (if e ∈ Sh ∧ F_cs.head e = v then v' else F_cs.head e)
    rw [(hFeq.2.2 e he).2]
    by_cases hhv : F_cs.head e = v
    · have hGh : G.src (e, false) = v := (hFsub.2.2 e heF).2.symm.trans hhv
      have hiff : e ∈ ShM ↔ e ∈ Sh := by
        simp only [ShM, moved, Finset.mem_image, Finset.mem_filter, List.mem_toFinset, List.mem_filter, hordG]
        constructor
        · rintro ⟨⟨f, fb⟩, ⟨⟨⟨hfE, hfs⟩, hm⟩, hfb⟩, rfl⟩
          cases fb
          · have := (hmov (f, false) hfE hfs).symm.trans hm; simpa [splitEnds] using this
          · cases hfb
        · intro heSh
          refine ⟨(e, false), ⟨⟨⟨heG, hGh⟩, ?_⟩, rfl⟩, rfl⟩
          rw [hmov (e, false) heG hGh]; simpa [splitEnds] using heSh
      simp [hhv, hiff]
    · simp [hhv]

/-! ## 2. Combined wall-tail `TourRelChain` (releases of `u` + quiet prefix of `U_rest`) -/

/-- After a wall update `u` (`isQuietUpdate cs u = false`) transitions the tour to `sWall` matching
`(inputMid cs u).F`, builds the combined `TourRelChain` for all release splits of `u` followed by
all release splits of `splitQuietPrefix cs1 U_rest`, advancing `s.rf` to
`(compLSFBatch cs1 Uq_next).RF` and matching `canonSplitList` / `restrictSplits`. -/
theorem wallStep_tailChain {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {vCap eCap : ℕ}
    {keep M : Finset ℕ} {cs : CompLSFState} {u : Update} {U_rest : List Update}
    {sWall : TourAbs} {S_wall : MGraph}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hBU : cs.G.BatchIsValid (u :: U_rest))
    (hnq : isQuietUpdate cs u = false)
    (hRlt : ∀ r ∈ (compLSFBatch cs (u :: U_rest)).RF.R, r < vCap)
    (hvW : TourValid vCap eCap sWall)
    (hFeqW : GraphEq sWall.rf.F (inputMid cs u).F.F)
    (hReqW : sWall.rf.R = (inputMid cs u).F.R)
    (hMW : TourMarksAt sWall M) (hMdisj : Disjoint M cs.RF.F.E)
    (hKW : TourKeepMatch keep sWall S_wall)
    (hKdisj1 : Disjoint keep (batchDeletes U_rest))
    (hordG1 : ∀ v x, x ∈ sWall.ord v ↔ x.1 ∈ (compLSFStepSingle cs u).G.E ∧
      (compLSFStepSingle cs u).G.src x = v)
    (hkeepG1 : ∀ f ∈ keep, f ∈ (compLSFStepSingle cs u).G.E) :
    let cs1 := compLSFStepSingle cs u
    let cuts := ((forestAfterInput cs.RF.F u).E \ cs1.RF.F.E).sort (· ≤ ·)
    let Uq1 := (splitQuietPrefix cs1 U_rest).1
    let cs_wall1 := compLSFBatch cs1 Uq1
    let relL := releasesSplitEntries cs1.RF.R (inputMid cs u) cuts ++
      canonSplitList cs1 Uq1
    let P_rel := restrictSplits keep (releasesBatch cs1.G cs1.RF.R (inputMid cs u) cuts) ++
      restrictSplits keep (canonCoreBatch cs1 Uq1)
    ∃ s_next S_next,
      TourRelChain vCap eCap keep M sWall S_wall relL P_rel s_next S_next ∧
      s_next.ord = sWall.ord ∧ s_next.marked = sWall.marked ∧
      GraphEq s_next.rf.F cs_wall1.RF.F ∧ s_next.rf.R = cs_wall1.RF.R ∧
      TourValid vCap eCap s_next ∧ TourMarksAt s_next M ∧ TourKeepMatch keep s_next S_next ∧
      Disjoint M cs_wall1.RF.F.E := by
  intro cs1 cuts Uq1 cs_wall1 relL P_rel
  set Uwall1 := (splitQuietPrefix cs1 U_rest).2
  obtain ⟨hI1, hG1, _, _, _, _, hEqF1, hFcRSF1, hcutsMem, hcutsNd⟩ :=
    compLSFStepSingle_forest_props hI hBU.1
  obtain ⟨hMidRSF, hMidF, _, _, hMidRsub⟩ := inputMid_wall_props hI hBU.1 hnq
  have hBUrest : cs1.G.BatchIsValid U_rest := hG1.symm ▸ hBU.2
  have hBUq1 : cs1.G.BatchIsValid Uq1 := by
    rw [← splitQuietPrefix_append cs1 U_rest] at hBUrest
    exact (batchIsValid_append.mp hBUrest).1
  have hR1_lt : ∀ r ∈ cs1.RF.R, r < vCap := fun r hr =>
    hRlt r (by simpa [compLSFBatch, cs1] using (compLSFBatch_decremental hI1 hBUrest).2 hr)
  have hRwall1_lt : ∀ r ∈ cs_wall1.RF.R, r < vCap := fun r hr => by
    have hBUrest' : cs1.G.BatchIsValid (Uq1 ++ Uwall1) := by rwa [splitQuietPrefix_append]
    have hIwall1 := compLSFBatch_inv hI1 hBUq1
    have hBUw1 : cs_wall1.G.BatchIsValid Uwall1 := by
      have hGeq := (compLSFBatch_step_props Uq1 hI1 hBUq1).2.1
      rw [hGeq]; exact (batchIsValid_append.mp hBUrest').2
    have hsub := (compLSFBatch_decremental hIwall1 hBUw1).2 hr
    have hcat : compLSFBatch cs_wall1 Uwall1 = compLSFBatch cs (u :: U_rest) := by
      simp only [cs_wall1, compLSFBatch, List.foldl_cons, ← List.foldl_append]
      exact congrArg (List.foldl compLSFStepSingle cs1) (splitQuietPrefix_append cs1 U_rest)
    exact hRlt r (hcat ▸ hsub)
  have hMcuts : ∀ e ∈ cuts, e ∉ M := fun e he => by
    have heK : e ∈ (forestAfterInput cs.RF.F u).E := hcutsMem e he
    have he0 : e ∈ cs.RF.F.E := by
      cases u with
      | insert => exact heK
      | delete _ => exact Finset.mem_of_mem_erase heK
      | split => exact heK
    exact Finset.disjoint_right.mp hMdisj he0
  have hkeepSrc : ∀ f ∈ keep, f ∈ cs1.G.E ∧ ordSrc sWall.ord (f, true) = cs1.G.tail f ∧
      ordSrc sWall.ord (f, false) = cs1.G.head f := fun f hf => by
    have hfG := hkeepG1 f hf
    have ht : (f, true) ∈ sWall.ord (cs1.G.tail f) := (hordG1 _ _).mpr ⟨hfG, rfl⟩
    have hh : (f, false) ∈ sWall.ord (cs1.G.head f) := (hordG1 _ _).mpr ⟨hfG, rfl⟩
    exact ⟨hfG, hvW.compat.ordSrc_eq ht, hvW.compat.ordSrc_eq hh⟩
  obtain ⟨s1, S1, hch1, hord1, hmk1, hF1, hR1, hv1, hM1, hK1⟩ :=
    tourRelChain_of_releasesBatch (G := cs1.G) (final := ⟨cuts.foldl eraseForestEdge (forestAfterInput cs.RF.F u), cs1.RF.R⟩)
      hFcRSF1 hR1_lt cuts (inputMid cs u) sWall S_wall hMidRSF hMidRsub (by rw [hMidF])
      (by rw [hMidF]; exact hcutsMem) hcutsNd hvW hFeqW hReqW hMW hMcuts hKW hkeepSrc
  have hF1_cs1 : GraphEq s1.rf.F cs1.RF.F := graphEq_trans hF1 hEqF1
  have hMdisj1 : Disjoint M cs1.RF.F.E :=
    Disjoint.mono_right (compLSFBatch_decremental (U := [u]) hI ⟨hBU.1, trivial⟩).1 hMdisj
  have hKdisjQ1 : Disjoint keep (batchDeletes Uq1) :=
    Disjoint.mono_right (fun f hf => by
      obtain ⟨u', hu', h⟩ := (mem_batchDeletes_iff _ _).mp hf
      rw [← splitQuietPrefix_append cs1 U_rest]
      exact (mem_batchDeletes_iff _ _).mpr ⟨u', List.mem_append_left _ hu', h⟩) hKdisj1
  obtain ⟨s2, S2, hch2, hord2, hmk2, hF2, hR2, hv2, hM2, hK2⟩ :=
    tourRelChain_of_quietPrefix Uq1 cs1 s1 S1 hI1 hBUq1 (splitQuietPrefix_all_quiet cs1 U_rest)
      hRwall1_lt hv1 hF1_cs1 hR1 hM1 hMdisj1 hK1 hKdisjQ1 (by rw [hord1]; exact hkeepSrc)
  have hMdisj2 : Disjoint M cs_wall1.RF.F.E :=
    Disjoint.mono_right (compLSFBatch_decremental hI1 hBUq1).1 hMdisj1
  exact ⟨s2, S2, tourRelChain_append hch1 hch2, hord2.trans hord1, hmk2.trans hmk1,
    hF2, hR2, hv2, hM2, hK2, hMdisj2⟩

/-! ## 3. Parametric loop cost multiplier and loop-body syntax -/

@[expose] def tourBlockLoopMulFn (mCase : ℕ) : ℕ := mCase + 150

theorem tourBlockLoopMulFn_eq (mCase : ℕ) : tourBlockLoopMulFn mCase = mCase + 150 := rfl

noncomputable def tourBlockLoopMul : ℕ := tourBlockLoopMulFn tourBlockCaseMul

theorem tourBlockLoopMul_eq : tourBlockLoopMul = tourBlockLoopMulFn tourBlockCaseMul := by
  unfold tourBlockLoopMul; rfl

/-- Exact loop body of `asmFirstTourBlockStepStmt` (`AssemblyFirstTourStepProg.lean:150-226`). -/
@[expose] def asmFirstTourLoopBody (bSelf bTour bOut bCopy : ℕ) : Stmt :=
  .assign 16 (.load (.reg 12)) ;;
  .cond (.bin .eq (.reg 16) (.const 0))
    (.store (.reg 9) (.const 2) ;;
     .call 17 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .const 8] ;;
     .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 9, .bin .add (.reg 9) (.const 9)] ;;
     .assign 12 (.bin .add (.reg 12) (.const 4)) ;;
     .assign 13 (.bin .add (.reg 13) (.const 8)) ;;
     .assign 14 (.bin .add (.reg 14) (.const 2)))
    (.cond (.bin .eq (.reg 16) (.const 1))
      (.assign 17 (.load (.bin .add (.reg 12) (.const 1))) ;;
       .assign 18 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
       .assign 19 (.load (.bin .add (.reg 18) (.bin .mul (.const 2) (.reg 17)))) ;;
       .assign 20 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
       .assign 21 (.load (.bin .add (.bin .add (.reg 20) (.bin .mul (.const 17) (.reg 19)))
         (.const 9))) ;;
       .cond (.bin .eq (.reg 21) (.const 0))
         (.assign 22 (.load (.reg 7)) ;;
          .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1))
            (.bin .mul (.const 4) (.reg 22))) ;;
          .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
          .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
          .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
          .call 9 (tourOp bTour 1) [.reg 0, .reg 17, .reg 25, .reg 9] ;;
          .store (.reg 9) (.const 1) ;;
          .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
          .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
          .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)] ;;
          .assign 26 (.reg 9) ;;
          .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
          .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
          .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
            (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
            .nop ;;
          .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
          .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
         (.store (.reg 9) (.const 1) ;;
          .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
          .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
          .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)]) ;;
       .assign 12 (.bin .add (.reg 12) (.const 2)) ;;
       .assign 13 (.bin .add (.reg 13) (.const 2)) ;;
       .assign 14 (.bin .add (.reg 14) (.const 1)))
      (.assign 17 (.load (.bin .add (.reg 12) (.const 1))) ;;
       .assign 18 (.load (.bin .add (.reg 12) (.const 2))) ;;
       .assign 19 (.load (.bin .add (.reg 12) (.const 3))) ;;
       .assign 20 (.load (.bin .add (.reg 12) (.const 4))) ;;
       .assign 21 (.load (.bin .add (.reg 13) (.const 3))) ;;
       .call 9 (bSelf + 1) [.reg 0, .reg 13, .reg 9] ;;
       .assign 22 (.load (.reg 7)) ;;
       .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1))
         (.bin .mul (.const 4) (.reg 22))) ;;
       .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
       .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
       .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
       .assign 26 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
       .assign 27 (.load (.bin .add (.reg 26) (.reg 18))) ;;
       .assign 28 (.reg 17) ;;
       .cond (.bin .eq (.reg 27) (.const 1)) (.assign 28 (.reg 18)) .nop ;;
       .call 9 (tourOp bTour 3) [.reg 0, .reg 28, .reg 25, .reg 9] ;;
       .assign 26 (.reg 9) ;;
       .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
       .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
       .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
         (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
         .nop ;;
       .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
       .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9] ;;
       .assign 12 (.bin .add (.bin .add (.reg 12) (.const 5))
         (.bin .add (.reg 19) (.reg 20))) ;;
       .assign 13 (.bin .add (.bin .add (.reg 13) (.const 4)) (.reg 21)) ;;
       .assign 14 (.bin .add (.reg 14) (.const 1)))) ;;
  .assign 15 (.bin .add (.reg 15) (.const 1))

theorem runs_seq_congr_r {w : ℕ} {p : Program} {ω : ℕ → Bool} {A B B' : Stmt}
    {s0 s1 : State} {c : ℕ} (h : Runs w p ω (A ;; B) s0 .normal s1 c)
    (hf : ∀ {sa sb cb}, Runs w p ω B sa .normal sb cb → Runs w p ω B' sa .normal sb cb) :
    Runs w p ω (A ;; B') s0 .normal s1 c := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hEq, _⟩ | ⟨sm, cA, cB, hA, hB, rfl⟩
  · cases hEq
  · exact runs_seq_normal hA (hf hB)

theorem runs_seq_r3 {w : ℕ} {p : Program} {ω : ℕ → Bool} {A B C D : Stmt}
    {s0 s1 : State} {c : ℕ} (h : Runs w p ω ((A ;; B ;; C) ;; D) s0 .normal s1 c) :
    Runs w p ω (A ;; B ;; C ;; D) s0 .normal s1 c :=
  runs_seq_congr_r (runs_seq_assoc h) runs_seq_assoc

theorem runs_seq_r17 {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 T : Stmt}
    {s0 s1 : State} {c : ℕ}
    (h : Runs w p ω
      ((S1 ;; S2 ;; S3 ;; S4 ;; S5 ;; S6 ;; S7 ;; S8 ;; S9 ;; S10 ;; S11 ;; S12 ;; S13 ;; S14 ;;
        S15 ;; S16 ;; S17) ;; T) s0 .normal s1 c) :
    Runs w p ω
      (S1 ;; S2 ;; S3 ;; S4 ;; S5 ;; S6 ;; S7 ;; S8 ;; S9 ;; S10 ;; S11 ;; S12 ;; S13 ;; S14 ;;
       S15 ;; S16 ;; S17 ;; T) s0 .normal s1 c :=
  runs_seq_congr_r (runs_seq_assoc h) fun h1 =>
  runs_seq_congr_r (runs_seq_assoc h1) fun h2 =>
  runs_seq_congr_r (runs_seq_assoc h2) fun h3 =>
  runs_seq_congr_r (runs_seq_assoc h3) fun h4 =>
  runs_seq_congr_r (runs_seq_assoc h4) fun h5 =>
  runs_seq_congr_r (runs_seq_assoc h5) fun h6 =>
  runs_seq_congr_r (runs_seq_assoc h6) fun h7 =>
  runs_seq_congr_r (runs_seq_assoc h7) fun h8 =>
  runs_seq_congr_r (runs_seq_assoc h8) fun h9 =>
  runs_seq_congr_r (runs_seq_assoc h9) fun h10 =>
  runs_seq_congr_r (runs_seq_assoc h10) fun h11 =>
  runs_seq_congr_r (runs_seq_assoc h11) fun h12 =>
  runs_seq_congr_r (runs_seq_assoc h12) fun h13 =>
  runs_seq_congr_r (runs_seq_assoc h13) fun h14 =>
  runs_seq_congr_r (runs_seq_assoc h14) runs_seq_assoc

end

end MinCostFlow.SparseCore.Program
