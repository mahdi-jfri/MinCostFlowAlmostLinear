module

public import MinCostFlow.SparseCore.Program.CompModel
import Mathlib.Tactic.Linarith

/-!
# Step Preservation of `CompEdgeTrack` and Projected-Split `UpdateAt` (`CompTrack`)

Proves preservation of `CompEdgeTrack` across `.insert`, `.delete`, and `.split` updates
(`compEdgeTrack_step_insert`, `compEdgeTrack_step_delete`, `compEdgeTrack_step_split`), and exact
`UpdateAt` correspondence for projected Tag-2 and Tag-3 splits (`projSplit_updateAt_tag2`,
`projSplit_updateAt_tag3`) after filtering out cross-edges.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Preservation of `CompEdgeTrack` across `.insert e a b`. Since cross-inserts are projected to
insert-then-delete self-loops, `gtList` and `ghList` remain unchanged (permanently empty). -/
lemma compEdgeTrack_step_insert {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    {e a b : ℕ} (hu : cs.G.UpdateIsValid (.insert e a b)) (heCap : e < eCap)
    {c1 c2 : Fin numComps}
    (ha : a ∈ (cs.compSt (compOf c1)).G.V) (hb : b ∈ (cs.compSt (compOf c2)).G.V) :
    let edgeC1' := Function.update edgeC1 e c1.1
    let edgeC2' := Function.update edgeC2 e c2.1
    CompEdgeTrack numComps vCap eCap compOf edgeC1' edgeC2' gtVert ghVert gtList ghList
      (compLSFStepSingle cs (.insert e a b)) := by
  classical
  intro edgeC1' edgeC2'
  set cs' := compLSFStepSingle cs (.insert e a b)
  have hGC' : ∀ c : Fin numComps,
      (cs'.compSt (compOf c)).G =
        (cs.compSt (compOf c)).G.applyBatch
          (projCompUpdateG cs.G (cs.compSt (compOf c)).G (.insert e a b)) := fun c =>
    applyLSFBatch_G_of_valid (hI.hCompLSF _ (hT.compOf_mem c)).1
      (projCompUpdateG_valid hI hu (hT.compOf_mem c))
  have ha_only : ∀ c : Fin numComps, a ∈ (cs.compSt (compOf c)).G.V ↔ c = c1 := fun c =>
    ⟨fun hac => by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hI.hV_disj _ (hT.compOf_mem c) _ (hT.compOf_mem c1) (fun h => hne (hT.hBij.1 h))) hac ha,
     fun h => h ▸ ha⟩
  have hb_only : ∀ c : Fin numComps, b ∈ (cs.compSt (compOf c)).G.V ↔ c = c2 := fun c =>
    ⟨fun hbc => by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hI.hV_disj _ (hT.compOf_mem c) _ (hT.compOf_mem c2) (fun h => hne (hT.hBij.1 h))) hbc hb,
     fun h => h ▸ hb⟩
  have hproj : ∀ c : Fin numComps,
      projCompUpdateG cs.G (cs.compSt (compOf c)).G (.insert e a b) =
        if c = c1 ∧ c = c2 then [.insert e a b]
        else if c = c1 then [.insert e a a, .delete e]
        else if c = c2 then [.insert e b b, .delete e]
        else [] := fun c => by
    simp only [projCompUpdateG, ha_only c, hb_only c]
  have hV' : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.V = (cs.compSt (compOf c)).G.V := fun c => by
    rw [hGC' c, hproj c]; split_ifs <;> rfl
  have hCross' : cs'.crossEdges = if c1 = c2 then cs.crossEdges else insert e cs.crossEdges := by
    have hex : (∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V) ↔ c1 = c2 := by
      constructor
      · rintro ⟨C, hC, haC, hbC⟩
        obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
        exact ((ha_only c).mp haC).symm.trans ((hb_only c).mp hbC)
      · rintro rfl; exact ⟨compOf c1, hT.compOf_mem c1, ha, hb⟩
    dsimp only [cs', compLSFStepSingle]
    simp only [hex]
  have he_not_E : e ∉ cs.G.E := hu.1
  refine ⟨hT.hBij, hT.hVlt, ?_, ?_, hT.hGT, hT.hGH⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · exact heCap
    · exact hT.hElt f hf'
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · refine ⟨c1, c2, by simp [edgeC1'], by simp [edgeC2'],
        by rw [hV' c1]; simpa [cs', compLSFStepSingle, MGraph.applyUpdate] using ha,
        by rw [hV' c2]; simpa [cs', compLSFStepSingle, MGraph.applyUpdate] using hb,
        ?_, ?_, ?_⟩
      · intro c
        rw [hGC' c, hproj c]
        have hf_not : f ∉ (cs.compSt (compOf c)).G.E :=
          fun hm => he_not_E (hI.hCE_sub _ (hT.compOf_mem c) hm)
        split_ifs with h12 h1 h2
        · simp [MGraph.applyBatch, MGraph.applyUpdate, h12.1, h12.2, h12.1.symm.trans h12.2]
        · have hne12 : c1 ≠ c2 := fun h => h12 ⟨h1, h1.trans h⟩
          simp [MGraph.applyBatch, MGraph.applyUpdate, hne12]
        · have hne12 : c1 ≠ c2 := fun h => h1 (h2.trans h.symm)
          simp [MGraph.applyBatch, MGraph.applyUpdate, hne12]
        · simp [MGraph.applyBatch, hf_not, h1]
      · rw [hCross']
        by_cases h12 : c1 = c2
        · simp [h12, show f ∉ cs.crossEdges from fun h => he_not_E (hI.hIns_sub (hI.hCross_sub h))]
        · simp [h12]
      · rintro rfl
        rw [hGC' c1, hproj c1]
        simp [cs', compLSFStepSingle, MGraph.applyBatch, MGraph.applyUpdate]
    · have hfne : f ≠ e := fun h => he_not_E (h ▸ hf')
      obtain ⟨d1, d2, hd1, hd2, ht1, hh2, hmem, hcr_iff, heq_ends⟩ := hT.hEdge f hf'
      have hG_tail : cs'.G.tail f = cs.G.tail f := by
        simp [cs', compLSFStepSingle, MGraph.applyUpdate, hfne]
      have hG_head : cs'.G.head f = cs.G.head f := by
        simp [cs', compLSFStepSingle, MGraph.applyUpdate, hfne]
      have hC_tail : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.tail f = (cs.compSt (compOf c)).G.tail f :=
        fun c => by rw [hGC' c, hproj c]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, hfne]
      have hC_head : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.head f = (cs.compSt (compOf c)).G.head f :=
        fun c => by rw [hGC' c, hproj c]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, hfne]
      refine ⟨d1, d2, by simp [edgeC1', hfne, hd1], by simp [edgeC2', hfne, hd2],
        by rw [hV' d1, hG_tail]; exact ht1, by rw [hV' d2, hG_head]; exact hh2,
        ?_, ?_, fun h => by rw [hC_tail d1, hC_head d1, hG_tail, hG_head]; exact heq_ends h⟩
      · intro c
        rw [hGC' c, hproj c]
        split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, hfne, hmem c]
      · rw [hCross']; split_ifs <;> simp [hfne, hcr_iff]

/-- Preservation of `CompEdgeTrack` across `.delete e`. All tracking arrays remain unchanged. -/
lemma compEdgeTrack_step_delete {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    {e : ℕ} (hu : cs.G.UpdateIsValid (.delete e)) :
    CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList
      (compLSFStepSingle cs (.delete e)) := by
  classical
  set cs' := compLSFStepSingle cs (.delete e)
  have hGC' : ∀ c : Fin numComps,
      (cs'.compSt (compOf c)).G =
        (cs.compSt (compOf c)).G.applyBatch
          (projCompUpdateG cs.G (cs.compSt (compOf c)).G (.delete e)) := fun c =>
    applyLSFBatch_G_of_valid (hI.hCompLSF _ (hT.compOf_mem c)).1
      (projCompUpdateG_valid hI hu (hT.compOf_mem c))
  have hV' : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.V = (cs.compSt (compOf c)).G.V := fun c => by
    rw [hGC' c]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
  have hT_eq : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.tail = (cs.compSt (compOf c)).G.tail := fun c => by
    rw [hGC' c]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
  have hH_eq : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.head = (cs.compSt (compOf c)).G.head := fun c => by
    rw [hGC' c]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
  refine ⟨hT.hBij, hT.hVlt, fun f hf => hT.hElt f (Finset.erase_subset _ _ hf), ?_, hT.hGT, hT.hGH⟩
  intro f hf
  have ⟨hfne, hfG⟩ := Finset.mem_erase.mp hf
  obtain ⟨d1, d2, hd1, hd2, ht1, hh2, hmem, hcr_iff, heq_ends⟩ := hT.hEdge f hfG
  refine ⟨d1, d2, hd1, hd2, by rw [hV' d1]; exact ht1, by rw [hV' d2]; exact hh2,
    ?_, ?_, fun h => by rw [hT_eq d1, hH_eq d1]; exact heq_ends h⟩
  · intro c
    rw [hGC' c]; dsimp only [projCompUpdateG]
    split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, hfne, hmem c]
  · change f ∈ cs.crossEdges.erase e ↔ d1 ≠ d2
    simp [hfne, hcr_iff]

/-- Preservation of `CompEdgeTrack` across `.split v v' St Sh`: all tracking arrays are unchanged. -/
lemma compEdgeTrack_step_split {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    {v v' : ℕ} {St Sh : Finset ℕ} (hu : cs.G.UpdateIsValid (.split v v' St Sh)) (hv'Cap : v' < vCap)
    {cv : Fin numComps} (hv : v ∈ (cs.compSt (compOf cv)).G.V) :
    CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList
      (compLSFStepSingle cs (.split v v' St Sh)) := by
  classical
  set cs' := compLSFStepSingle cs (.split v v' St Sh)
  have hGC' : ∀ c : Fin numComps,
      (cs'.compSt (compOf c)).G =
        (cs.compSt (compOf c)).G.applyBatch
          (projCompUpdateG cs.G (cs.compSt (compOf c)).G (.split v v' St Sh)) := fun c =>
    applyLSFBatch_G_of_valid (hI.hCompLSF _ (hT.compOf_mem c)).1
      (projCompUpdateG_valid hI hu (hT.compOf_mem c))
  have hv_only : ∀ c : Fin numComps, v ∈ (cs.compSt (compOf c)).G.V ↔ c = cv := fun c =>
    ⟨fun hvc => by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hI.hV_disj _ (hT.compOf_mem c) _ (hT.compOf_mem cv) (fun h => hne (hT.hBij.1 h))) hvc hv,
     fun h => h ▸ hv⟩
  have hV' : ∀ c : Fin numComps,
      (cs'.compSt (compOf c)).G.V =
        if c = cv then insert v' (cs.compSt (compOf c)).G.V else (cs.compSt (compOf c)).G.V := fun c => by
    rw [hGC' c]; simp only [projCompUpdateG, hv_only c]; split_ifs <;> rfl
  have hE' : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.E = (cs.compSt (compOf c)).G.E := fun c => by
    rw [hGC' c]; simp only [projCompUpdateG, hv_only c]; split_ifs <;> rfl
  refine ⟨hT.hBij, ?_, hT.hElt, ?_, hT.hGT, hT.hGH⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hv'Cap
    · exact hT.hVlt x hx'
  · intro e he
    obtain ⟨c1, c2, hc1, hc2, ht1, hh2, hmem, hcr_iff, heq_ends⟩ := hT.hEdge e he
    have hGt' : cs'.G.tail e = if e ∈ St ∧ cs.G.tail e = v then v' else cs.G.tail e := rfl
    have hGh' : cs'.G.head e = if e ∈ Sh ∧ cs.G.head e = v then v' else cs.G.head e := rfl
    have hCt' : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.tail e =
        if c = cv ∧ e ∈ (cs.compSt (compOf c)).G.E ∧ e ∈ St ∧
          (cs.compSt (compOf c)).G.tail e = v ∧ cs.G.tail e = v then v'
        else (cs.compSt (compOf c)).G.tail e := fun c => by
      rw [hGC' c]; simp only [projCompUpdateG, hv_only c]
      by_cases hcv : c = cv
      · subst hcv
        simp only [↓reduceIte, true_and, MGraph.applyBatch, List.foldl_cons, List.foldl_nil,
          MGraph.applyUpdate, Finset.mem_filter]
        by_cases hcond : e ∈ (cs.compSt (compOf c)).G.E ∧ e ∈ St ∧
            (cs.compSt (compOf c)).G.tail e = v ∧ cs.G.tail e = v
        · simp only [hcond, and_self, ↓reduceIte]
        · simp only [hcond, false_and, ↓reduceIte]
      · simp [hcv, MGraph.applyBatch]
    have hCh' : ∀ c : Fin numComps, (cs'.compSt (compOf c)).G.head e =
        if c = cv ∧ e ∈ (cs.compSt (compOf c)).G.E ∧ e ∈ Sh ∧
          (cs.compSt (compOf c)).G.head e = v ∧ cs.G.head e = v then v'
        else (cs.compSt (compOf c)).G.head e := fun c => by
      rw [hGC' c]; simp only [projCompUpdateG, hv_only c]
      by_cases hcv : c = cv
      · subst hcv
        simp only [↓reduceIte, true_and, MGraph.applyBatch, List.foldl_cons, List.foldl_nil,
          MGraph.applyUpdate, Finset.mem_filter]
        by_cases hcond : e ∈ (cs.compSt (compOf c)).G.E ∧ e ∈ Sh ∧
            (cs.compSt (compOf c)).G.head e = v ∧ cs.G.head e = v
        · simp only [hcond, and_self, ↓reduceIte]
        · simp only [hcond, false_and, ↓reduceIte]
      · simp [hcv, MGraph.applyBatch]
    refine ⟨c1, c2, hc1, hc2, ?_, ?_, fun c => by rw [hE' c]; exact hmem c, hcr_iff, ?_⟩
    · rw [hV' c1, hGt']
      by_cases h1 : c1 = cv <;> by_cases h2 : e ∈ St ∧ cs.G.tail e = v <;> simp only [h1, h2, ↓reduceIte]
      · exact Finset.mem_insert_self _ _
      · subst h1; exact Finset.mem_insert_of_mem ht1
      · exact absurd ((hv_only c1).mp (h2.2 ▸ ht1)) h1
      · exact ht1
    · rw [hV' c2, hGh']
      by_cases h1 : c2 = cv <;> by_cases h2 : e ∈ Sh ∧ cs.G.head e = v <;> simp only [h1, h2, ↓reduceIte]
      · exact Finset.mem_insert_self _ _
      · subst h1; exact Finset.mem_insert_of_mem hh2
      · exact absurd ((hv_only c2).mp (h2.2 ▸ hh2)) h1
      · exact hh2
    · rintro rfl
      have he1 : e ∈ (cs.compSt (compOf c1)).G.E := (hmem c1).mpr ⟨rfl, rfl⟩
      obtain ⟨hrt, hrh⟩ := heq_ends rfl
      constructor
      · rw [hCt' c1, hGt']
        by_cases hst : e ∈ St ∧ cs.G.tail e = v
        · have hcv : c1 = cv := (hv_only c1).mp (hst.2 ▸ ht1)
          rw [ite_eq_left ⟨hcv, he1, hst.1, hrt.trans hst.2, hst.2⟩, ite_eq_left hst]
        · have hno : ¬(c1 = cv ∧ e ∈ (cs.compSt (compOf c1)).G.E ∧ e ∈ St ∧
              (cs.compSt (compOf c1)).G.tail e = v ∧ cs.G.tail e = v) := fun h => hst ⟨h.2.2.1, h.2.2.2.2⟩
          rw [ite_eq_right hno, ite_eq_right hst, hrt]
      · rw [hCh' c1, hGh']
        by_cases hsh : e ∈ Sh ∧ cs.G.head e = v
        · have hcv : c1 = cv := (hv_only c1).mp (hsh.2 ▸ hh2)
          rw [ite_eq_left ⟨hcv, he1, hsh.1, hrh.trans hsh.2, hsh.2⟩, ite_eq_left hsh]
        · have hno : ¬(c1 = cv ∧ e ∈ (cs.compSt (compOf c1)).G.E ∧ e ∈ Sh ∧
              (cs.compSt (compOf c1)).G.head e = v ∧ cs.G.head e = v) := fun h => hsh ⟨h.2.2.1, h.2.2.2.2⟩
          rw [ite_eq_right hno, ite_eq_right hsh, hrh]

/-! ## 3. Exact `UpdateAt` correspondence for projected splits -/

/-- For a Tag-2 (moved-set) split `[2, v, v', kt, kh] ++ Lt ++ Lh` on `cs.G`, filtering out
cross-edges (`e ∉ cs.crossEdges`) from `Lt` and `Lh` produces an exact Tag-2 `UpdateAt` for
`projCompUpdateG cs.G (cs.compSt (compOf c)).G u` on `(cs.compSt (compOf c)).G`. -/
lemma projSplit_updateAt_tag2 {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    {c : Fin numComps} {v v' : ℕ} {St Sh : Finset ℕ}
    (hv : v ∈ (cs.compSt (compOf c)).G.V)
    {mem : ℕ → ℕ} {a : ℕ} {Lt Lh Lt' Lh' : List ℕ}
    (hLt'Nd : Lt'.Nodup) (hLh'Nd : Lh'.Nodup)
    (hLt'Mem : ∀ e, e ∈ Lt' ↔ e ∈ Lt ∧ e ∉ cs.crossEdges)
    (hLh'Mem : ∀ e, e ∈ Lh' ↔ e ∈ Lh ∧ e ∉ cs.crossEdges)
    (hLtMem : ∀ e, e ∈ Lt ↔ e ∈ cs.G.E ∧ cs.G.tail e = v ∧ e ∈ St)
    (hLhMem : ∀ e, e ∈ Lh ↔ e ∈ cs.G.E ∧ cs.G.head e = v ∧ e ∈ Sh)
    (hLA : ListAt mem a ([2, v, v', Lt'.length, Lh'.length] ++ Lt' ++ Lh')) :
    let Gc := (cs.compSt (compOf c)).G
    let StC := Gc.E.filter fun e => e ∈ St ∧ Gc.tail e = v ∧ cs.G.tail e = v
    let ShC := Gc.E.filter fun e => e ∈ Sh ∧ Gc.head e = v ∧ cs.G.head e = v
    UpdateAt mem a Gc (.split v v' StC ShC) (5 + Lt'.length + Lh'.length) := by
  classical
  intro Gc StC ShC
  refine Or.inl ⟨Lt', Lh', hLt'Nd, hLh'Nd, ?_, ?_, rfl, hLA⟩
  · intro e
    rw [hLt'Mem e, hLtMem e]
    simp only [StC, Finset.mem_filter]
    constructor
    · rintro ⟨⟨heG, htv, hSt⟩, hnc⟩
      obtain ⟨c1, c2, _, _, ht1, _, hmem, hcr_iff, heq_ends⟩ := hT.hEdge e heG
      have h12 : c1 = c2 := by by_contra hne; exact hnc (hcr_iff.mpr hne)
      have hcc1 : c = c1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hI.hV_disj _ (hT.compOf_mem c) _ (hT.compOf_mem c1) (fun h => hne (hT.hBij.1 h)))
          hv (htv ▸ ht1)
      subst hcc1
      have heC : e ∈ Gc.E := (hmem c).mpr ⟨h12, rfl⟩
      have hrt : Gc.tail e = cs.G.tail e := (heq_ends h12).1
      exact ⟨heC, hrt.trans htv, heC, hSt, hrt.trans htv, htv⟩
    · rintro ⟨heC, _, _, hSt, _, htv⟩
      exact ⟨⟨hI.hCE_sub _ (hT.compOf_mem c) heC, htv, hSt⟩,
        hI.hCompE_notCross _ (hT.compOf_mem c) e heC⟩
  · intro e
    rw [hLh'Mem e, hLhMem e]
    simp only [ShC, Finset.mem_filter]
    constructor
    · rintro ⟨⟨heG, hhv, hSh⟩, hnc⟩
      obtain ⟨c1, c2, _, _, _, hh2, hmem, hcr_iff, heq_ends⟩ := hT.hEdge e heG
      have h12 : c1 = c2 := by by_contra hne; exact hnc (hcr_iff.mpr hne)
      subst h12
      have hcc1 : c = c1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hI.hV_disj _ (hT.compOf_mem c) _ (hT.compOf_mem c1) (fun h => hne (hT.hBij.1 h)))
          hv (hhv ▸ hh2)
      subst hcc1
      have heC : e ∈ Gc.E := (hmem c).mpr ⟨rfl, rfl⟩
      have hrh : Gc.head e = cs.G.head e := (heq_ends rfl).2
      exact ⟨heC, hrh.trans hhv, heC, hSh, hrh.trans hhv, hhv⟩
    · rintro ⟨heC, _, _, hSh, _, hhv⟩
      exact ⟨⟨hI.hCE_sub _ (hT.compOf_mem c) heC, hhv, hSh⟩,
        hI.hCompE_notCross _ (hT.compOf_mem c) e heC⟩

/-- For a Tag-3 (kept-set) split `[3, v, v', kt, kh] ++ Lt ++ Lh` on `cs.G`, filtering out
cross-edges (`e ∉ cs.crossEdges`) from `Lt` and `Lh` produces an exact Tag-3 `UpdateAt` for
`projCompUpdateG cs.G (cs.compSt (compOf c)).G u` on `(cs.compSt (compOf c)).G` (zero ghost ends
exist in `Gc` since cross-inserts are projected to insert-then-delete self-loops). -/
lemma projSplit_updateAt_tag3 {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    {c : Fin numComps} {v v' : ℕ} {St Sh : Finset ℕ}
    (hv : v ∈ (cs.compSt (compOf c)).G.V)
    {mem : ℕ → ℕ} {a : ℕ} {Lt Lh Lt' Lh' : List ℕ}
    (hLt'Nd : Lt'.Nodup) (hLh'Nd : Lh'.Nodup)
    (hLt'Mem : ∀ e, e ∈ Lt' ↔ e ∈ Lt ∧ e ∉ cs.crossEdges)
    (hLh'Mem : ∀ e, e ∈ Lh' ↔ e ∈ Lh ∧ e ∉ cs.crossEdges)
    (hLtMem : ∀ e, e ∈ Lt ↔ e ∈ cs.G.E ∧ cs.G.tail e = v ∧ e ∉ St)
    (hLhMem : ∀ e, e ∈ Lh ↔ e ∈ cs.G.E ∧ cs.G.head e = v ∧ e ∉ Sh)
    (hLA : ListAt mem a ([3, v, v', Lt'.length, Lh'.length] ++ Lt' ++ Lh')) :
    let Gc := (cs.compSt (compOf c)).G
    let StC := Gc.E.filter fun e => e ∈ St ∧ Gc.tail e = v ∧ cs.G.tail e = v
    let ShC := Gc.E.filter fun e => e ∈ Sh ∧ Gc.head e = v ∧ cs.G.head e = v
    UpdateAt mem a Gc (.split v v' StC ShC) (5 + Lt'.length + Lh'.length) := by
  classical
  intro Gc StC ShC
  refine Or.inr ⟨Lt', Lh', hLt'Nd, hLh'Nd, ?_, ?_, rfl, hLA⟩
  · intro e
    rw [hLt'Mem e, hLtMem e]
    simp only [StC, Finset.mem_filter]
    constructor
    · rintro ⟨⟨heG, htv, hnSt⟩, hnc⟩
      obtain ⟨c1, c2, _, _, ht1, _, hmem, hcr_iff, heq_ends⟩ := hT.hEdge e heG
      have h12 : c1 = c2 := by by_contra hne; exact hnc (hcr_iff.mpr hne)
      have hcc1 : c = c1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hI.hV_disj _ (hT.compOf_mem c) _ (hT.compOf_mem c1) (fun h => hne (hT.hBij.1 h)))
          hv (htv ▸ ht1)
      subst hcc1
      have heC : e ∈ Gc.E := (hmem c).mpr ⟨h12, rfl⟩
      exact ⟨heC, (heq_ends h12).1.trans htv, fun h => hnSt h.2.1⟩
    · rintro ⟨heC, hCt, hnStC⟩
      have hGtv : cs.G.tail e = v := (hI.compEnds_eq (hT.compOf_mem c) heC).1.symm.trans hCt
      exact ⟨⟨hI.hCE_sub _ (hT.compOf_mem c) heC, hGtv,
          fun hSt => hnStC ⟨heC, hSt, hCt, hGtv⟩⟩,
        hI.hCompE_notCross _ (hT.compOf_mem c) e heC⟩
  · intro e
    rw [hLh'Mem e, hLhMem e]
    simp only [ShC, Finset.mem_filter]
    constructor
    · rintro ⟨⟨heG, hhv, hnSh⟩, hnc⟩
      obtain ⟨c1, c2, _, _, _, hh2, hmem, hcr_iff, heq_ends⟩ := hT.hEdge e heG
      have h12 : c1 = c2 := by by_contra hne; exact hnc (hcr_iff.mpr hne)
      subst h12
      have hcc1 : c = c1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hI.hV_disj _ (hT.compOf_mem c) _ (hT.compOf_mem c1) (fun h => hne (hT.hBij.1 h)))
          hv (hhv ▸ hh2)
      subst hcc1
      have heC : e ∈ Gc.E := (hmem c).mpr ⟨rfl, rfl⟩
      exact ⟨heC, (heq_ends rfl).2.trans hhv, fun h => hnSh h.2.1⟩
    · rintro ⟨heC, hCh, hnShC⟩
      have hGhv : cs.G.head e = v := (hI.compEnds_eq (hT.compOf_mem c) heC).2.symm.trans hCh
      exact ⟨⟨hI.hCE_sub _ (hT.compOf_mem c) heC, hGhv,
          fun hSh => hnShC ⟨heC, hSh, hCh, hGhv⟩⟩,
        hI.hCompE_notCross _ (hT.compOf_mem c) e heC⟩

end

end MinCostFlow.SparseCore.Program
