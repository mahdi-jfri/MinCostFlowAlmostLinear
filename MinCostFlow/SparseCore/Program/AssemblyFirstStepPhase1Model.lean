module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Defs

import Mathlib.Tactic

/-!
# First-phase step Phase 1 model proof (`AssemblyFirstStepPhase1Model`)

Proves `scanBatchFold_correct`: folding `scanBatchStep` over a valid batch `U` maintains
`cmpMap`, `origVert`, `actFlag`, `newComps`, `delEdges`/`delFlag`, and `insEdges`/`insFlag` in
exact correspondence with `compLSFBatch tr.cs U` and `touchedCompsBatch tr.cs U \ tr.activeComps`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

private lemma comp_of_delete_nonCross {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {e : ℕ} (he : e ∈ cs.G.E) (hnc : e ∉ cs.crossEdges)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    e ∈ (cs.compSt C).G.E ↔ cs.G.tail e ∈ (cs.compSt C).G.V := by
  constructor
  · intro heC
    rw [← (hI.hNonCross_ends C hC e heC hnc).1]
    exact ((hI.hCompLSF C hC).1.hG_val e heC).1
  · intro htC
    obtain ⟨C', hC', heC'⟩ := hI.hEdge_cover e he hnc
    have htC' : cs.G.tail e ∈ (cs.compSt C').G.V := by
      rw [← (hI.hNonCross_ends C' hC' e heC' hnc).1]
      exact ((hI.hCompLSF C' hC').1.hG_val e heC').1
    by_cases hEq : C = C'
    · subst hEq; exact heC'
    · exact absurd htC' (Finset.disjoint_left.mp (hI.hV_disj C hC C' hC' hEq) htC)

/-- Invariant carried along `scanBatchFold` for a prefix of `U`. -/
structure ScanInv (comps : List (Finset ℕ)) (initAct : Finset (Finset ℕ))
    (cs₀ cs : CompLSFState) (st : ScanBatchState) : Prop where
  v_mono : cs₀.G.V ⊆ cs.G.V
  cmp_ok : ∀ c (hc : c < comps.length), ∀ v ∈ (cs.compSt comps[c]).G.V, st.cmpMap v = c
  orig_in : ∀ v ∈ cs.G.V, traceOrigVert st.origVert v ∈ cs₀.G.V
  orig_same_comp : ∀ c (hc : c < comps.length), ∀ v ∈ (cs.compSt comps[c]).G.V,
    traceOrigVert st.origVert v ∈ (cs₀.compSt comps[c]).G.V
  orig_zero_outside : ∀ v, v ∉ cs.G.V → st.origVert v = 0
  ins_ok : ∀ e ∈ cs.G.E, st.insFlag e = false →
    e ∈ cs₀.G.E ∧
    st.cmpMap (cs₀.G.tail e) = st.cmpMap (cs.G.tail e) ∧
    st.cmpMap (cs₀.G.head e) = st.cmpMap (cs.G.head e) ∧
    (st.actFlag (st.cmpMap (cs₀.G.tail e)) = false → cs.G.tail e = cs₀.G.tail e) ∧
    (st.actFlag (st.cmpMap (cs₀.G.head e)) = false → cs.G.head e = cs₀.G.head e)
  ins_active : ∀ e, st.insFlag e = true → e ∈ cs.G.E →
    (∃ c, ∃ hc : c < comps.length, cs.G.tail e ∈ (cs.compSt comps[c]).G.V ∧ st.actFlag c = true) ∧
    (∃ c, ∃ hc : c < comps.length, cs.G.head e ∈ (cs.compSt comps[c]).G.V ∧ st.actFlag c = true)
  act_init : ∀ c (hc : c < comps.length), comps[c] ∈ initAct → st.actFlag c = true
  cross_inact : ∀ c (hc : c < comps.length), st.actFlag c = false →
    Disjoint (cs.compSt comps[c]).G.E cs.crossEdges ∧
    ∀ e ∈ cs.crossEdges,
      cs.G.tail e ∉ (cs.compSt comps[c]).G.V ∧ cs.G.head e ∉ (cs.compSt comps[c]).G.V
  new_nodup : (st.newComps.map Prod.fst).Nodup
  new_lt : ∀ p ∈ st.newComps, p.1 < comps.length
  new_iff : ∀ c (hc : c < comps.length),
    c ∈ st.newComps.map Prod.fst ↔ st.actFlag c = true ∧ comps[c] ∉ initAct
  new_wit : ∀ p ∈ st.newComps, ∀ hc : p.1 < comps.length,
    p.2 ∈ (cs₀.compSt comps[p.1]).G.V
  delFlag_iff : ∀ e, st.delFlag e = true ↔ e ∈ st.delEdges
  insFlag_iff : ∀ e, st.insFlag e = true ↔ e ∈ st.insEdges

private lemma scanActivate_preserves_new {comps : List (Finset ℕ)} {initAct : Finset (Finset ℕ)}
    {cs₀ : CompLSFState} {st : ScanBatchState} {c v : ℕ} (hc : c < comps.length)
    (hv : st.actFlag c = false → v ∈ (cs₀.compSt comps[c]).G.V)
    (hnd : (st.newComps.map Prod.fst).Nodup)
    (hlt : ∀ p ∈ st.newComps, p.1 < comps.length)
    (hiff : ∀ c' (hc' : c' < comps.length),
      c' ∈ st.newComps.map Prod.fst ↔ st.actFlag c' = true ∧ comps[c'] ∉ initAct)
    (hwit : ∀ p ∈ st.newComps, ∀ hc' : p.1 < comps.length, p.2 ∈ (cs₀.compSt comps[p.1]).G.V)
    (hinit : ∀ c' (hc' : c' < comps.length), comps[c'] ∈ initAct → st.actFlag c' = true) :
    let st' := scanActivate st c v
    (st'.newComps.map Prod.fst).Nodup ∧
    (∀ p ∈ st'.newComps, p.1 < comps.length) ∧
    (∀ c' (hc' : c' < comps.length),
      c' ∈ st'.newComps.map Prod.fst ↔ st'.actFlag c' = true ∧ comps[c'] ∉ initAct) ∧
    (∀ p ∈ st'.newComps, ∀ hc' : p.1 < comps.length, p.2 ∈ (cs₀.compSt comps[p.1]).G.V) ∧
    (∀ c' (hc' : c' < comps.length), comps[c'] ∈ initAct → st'.actFlag c' = true) := by
  intro st'; unfold st' scanActivate
  split_ifs with hact
  · exact ⟨hnd, hlt, hiff, hwit, hinit⟩
  · have hactF : st.actFlag c = false := by cases h : st.actFlag c <;> simp_all
    have hnotMem : c ∉ st.newComps.map Prod.fst := fun hm =>
      absurd ((hiff c hc).mp hm).1 (by simp [hactF])
    have hnotInit : comps[c] ∉ initAct := fun hi => by have := hinit c hc hi; simp [hactF] at this
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton c, fun x hx y hy hEq => by
        simp at hy; subst hy; exact hnotMem (hEq ▸ hx)⟩
    · intro p hp; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      exact hp.elim (hlt p) (fun h => h ▸ hc)
    · intro c' hc'
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
      by_cases hEq : c' = c
      · subst hEq; simp [hnotInit]
      · rw [Function.update_of_ne hEq]; simp [hEq, hiff c' hc']
    · intro p hp hc'; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      exact hp.elim (fun h => hwit p h hc') (fun h => by subst h; exact hv hactF)
    · intro c' hc' hi
      by_cases hEq : c' = c
      · subst hEq; simp
      · dsimp only; rw [Function.update_of_ne hEq]; exact hinit c' hc' hi

private lemma comp_idx_of_mem_V {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {comps : List (Finset ℕ)} (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hCiff : ∀ C, C ∈ comps ↔ C ∈ components cs.G₀) {v : ℕ} (hv : v ∈ cs.G.V) :
    ∃ c, ∃ hc : c < comps.length, v ∈ (cs.compSt comps[c]).G.V := by
  rw [← hI.hV_eq, Finset.mem_biUnion] at hv
  obtain ⟨C, hC, hvC⟩ := hv
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem ((hCiff C).mpr hC)
  exact ⟨c, hc, hvC⟩

private lemma proj_nil_of_actFlag_false {comps : List (Finset ℕ)} {cs : CompLSFState}
    {st st' : ScanBatchState} {u : Update}
    (hact_proj : ∀ c (hc : c < comps.length),
      st'.actFlag c = true ↔ st.actFlag c = true ∨ projCompUpdateG cs.G (cs.compSt comps[c]).G u ≠ [])
    {c : ℕ} (hc : c < comps.length) (hF : st'.actFlag c = false) :
    st.actFlag c = false ∧ projCompUpdateG cs.G (cs.compSt comps[c]).G u = [] := by
  refine ⟨?_, ?_⟩
  · by_contra hT; simp only [Bool.not_eq_false] at hT
    have := (hact_proj c hc).mpr (Or.inl hT); rw [hF] at this; cases this
  · by_contra hne
    have := (hact_proj c hc).mpr (Or.inr hne); rw [hF] at this; cases this

private lemma scanBatchStep_inv {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {comps : List (Finset ℕ)} {initAct : Finset (Finset ℕ)}
    {cs₀ cs : CompLSFState} {st : ScanBatchState} {u : Update}
    (hG0_val : cs₀.G.IsValid) (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u)
    (hCnd : comps.Nodup) (hCiff : ∀ C, C ∈ comps ↔ C ∈ components cs.G₀)
    (hS : ScanInv comps initAct cs₀ cs st)
    (hUnch : ∀ c (hc : c < comps.length), st.actFlag c = false →
      cs.compSt comps[c] = cs₀.compSt comps[c]) :
    let cs' := compLSFStepSingle cs u
    let st' := scanBatchStep cs₀.G st u
    ScanInv comps initAct cs₀ cs' st' ∧
    (∀ c (hc : c < comps.length), st'.actFlag c = false →
      cs'.compSt comps[c] = cs₀.compSt comps[c]) ∧
    (∀ c (hc : c < comps.length),
      st'.actFlag c = true ↔
        st.actFlag c = true ∨ projCompUpdateG cs.G (cs.compSt comps[c]).G u ≠ []) ∧
    st'.delEdges.toFinset = st.delEdges.toFinset ∪ batchDeletes [u] ∧
    st'.insEdges.length ≤ st.insEdges.length + 1 ∧
    st'.delEdges.length ≤ st.delEdges.length + 1 ∧
    st'.newComps.length ≤ st.newComps.length + 2 := by
  classical
  intro cs' st'
  have hact_mono : ∀ c, st.actFlag c = true → st'.actFlag c = true := fun c hc => by
    cases u with
    | insert e a b => dsimp only [st', scanBatchStep]; rw [scanActivate_actFlag, scanActivate_actFlag]; simp [hc]
    | delete e => dsimp only [st', scanBatchStep]; split_ifs; exact hc; rw [scanActivate_actFlag, scanActivate_actFlag]; simp [hc]
    | split v v' St Sh => dsimp only [st', scanBatchStep]; rw [scanActivate_actFlag]; simp [hc]
  have hact_false_of : ∀ c, st'.actFlag c = false → st.actFlag c = false := fun c hF => by
    by_contra hT; simp only [Bool.not_eq_false] at hT; rw [hact_mono c hT] at hF; cases hF
  cases u with
  | insert e a b =>
    obtain ⟨ca, hca, haV⟩ := comp_idx_of_mem_V hI hCiff hu.2.1
    obtain ⟨cb, hcb, hbV⟩ := comp_idx_of_mem_V hI hCiff hu.2.2
    have hcmpa : st.cmpMap a = ca := hS.cmp_ok ca hca a haV
    have hcmpb : st.cmpMap b = cb := hS.cmp_ok cb hcb b hbV
    set st1 : ScanBatchState := { st with insFlag := Function.update st.insFlag e true, insEdges := st.insEdges ++ [e] }
    have hst'_eq : st' = scanActivate (scanActivate st1 ca a) cb b := by
      simp [st', st1, scanBatchStep, hcmpa, hcmpb]
    have hact_iff : ∀ c, st'.actFlag c = true ↔ st.actFlag c = true ∨ c = ca ∨ c = cb := fun c => by
      rw [hst'_eq, scanActivate_actFlag, scanActivate_actFlag]; simp [st1, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    have hact_proj : ∀ c (hc : c < comps.length),
        st'.actFlag c = true ↔ st.actFlag c = true ∨ projCompUpdateG cs.G (cs.compSt comps[c]).G (.insert e a b) ≠ [] := by
      intro c hc; rw [hact_iff c]
      have hCin := (hCiff comps[c]).mp (List.getElem_mem hc)
      have ha_iff : a ∈ (cs.compSt comps[c]).G.V ↔ c = ca := ⟨fun h => by
        by_contra hne
        exact Finset.disjoint_left.mp (hI.hV_disj _ hCin _ ((hCiff _).mp (List.getElem_mem hca))
          (fun hEq => hne (hCnd.getElem_inj_iff.mp hEq))) h haV, fun h => h ▸ haV⟩
      have hb_iff : b ∈ (cs.compSt comps[c]).G.V ↔ c = cb := ⟨fun h => by
        by_contra hne
        exact Finset.disjoint_left.mp (hI.hV_disj _ hCin _ ((hCiff _).mp (List.getElem_mem hcb))
          (fun hEq => hne (hCnd.getElem_inj_iff.mp hEq))) h hbV, fun h => h ▸ hbV⟩
      simp only [projCompUpdateG]
      by_cases h1 : a ∈ (cs.compSt comps[c]).G.V <;> by_cases h2 : b ∈ (cs.compSt comps[c]).G.V <;>
        simp [h1, h2, ← ha_iff, ← hb_iff]
    have hVcomp : ∀ c (hc : c < comps.length), (cs'.compSt comps[c]).G.V = (cs.compSt comps[c]).G.V := fun c hc => by
      have hCin := (hCiff comps[c]).mp (List.getElem_mem hc)
      show ((applyLSFBatch (cs.compSt comps[c]) _).G).V = _
      rw [applyLSFBatch_G_of_valid (hI.hCompLSF _ hCin).1 (projCompUpdateG_valid hI hu hCin)]
      simp only [projCompUpdateG]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate]
    have hG_V : cs'.G.V = cs.G.V := by simp [cs', compLSFStepSingle, MGraph.applyUpdate]
    have hst1_new := scanActivate_preserves_new (st := st1) hca
      (fun hF => by rw [← hUnch ca hca hF]; exact haV)
      hS.new_nodup hS.new_lt hS.new_iff hS.new_wit hS.act_init
    have hst2_new := scanActivate_preserves_new hcb
      (fun hF => by
        have hF0 : st.actFlag cb = false := by
          by_contra hT; simp only [Bool.not_eq_false] at hT
          have := scanActivate_actFlag st1 ca a cb; simp [st1, hT] at this; rw [hF] at this; cases this
        rw [← hUnch cb hcb hF0]; exact hbV)
      hst1_new.1 hst1_new.2.1 hst1_new.2.2.1 hst1_new.2.2.2.1 hst1_new.2.2.2.2
    refine ⟨⟨by rw [hG_V]; exact hS.v_mono,
      fun c hc v hv => by rw [hst'_eq]; simp [st1]; exact hS.cmp_ok c hc v (hVcomp c hc ▸ hv),
      fun v hv => by rw [hst'_eq]; simp [st1]; exact hS.orig_in v (hG_V ▸ hv),
      fun c hc v hv => by rw [hst'_eq]; simp [st1]; exact hS.orig_same_comp c hc v (hVcomp c hc ▸ hv),
      fun v hv => by rw [hst'_eq]; simp [st1]; exact hS.orig_zero_outside v (hG_V ▸ hv),
      ?_, ?_, by rw [hst'_eq]; exact hst2_new.2.2.2.2,
      fun c hc hF => by
        obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
        exact compLSFStepSingle_crossInactive hI hu ((hCiff _).mp (List.getElem_mem hc)) hnt
          (hS.cross_inact c hc hF0).1 (hS.cross_inact c hc hF0).2,
      by rw [hst'_eq]; exact hst2_new.1, by rw [hst'_eq]; exact hst2_new.2.1,
      by rw [hst'_eq]; exact hst2_new.2.2.1, by rw [hst'_eq]; exact hst2_new.2.2.2.1,
      fun e' => by rw [hst'_eq]; simp [st1, hS.delFlag_iff e'],
      fun e' => by
        rw [hst'_eq]; simp only [scanActivate_insFlag, scanActivate_insEdges, st1]
        by_cases hEq : e' = e
        · subst hEq; simp
        · rw [Function.update_of_ne hEq]; simp [hEq, hS.insFlag_iff e']⟩,
      fun c hc hF => by
        obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
        show applyLSFBatch (cs.compSt comps[c]) _ = cs₀.compSt comps[c]; rw [hnt]; exact hUnch c hc hF0,
      hact_proj, by rw [hst'_eq]; simp [st1, batchDeletes, addDel],
      by rw [hst'_eq]; simp [st1], by rw [hst'_eq]; simp [st1],
      by rw [hst'_eq]; have h1 := scanActivate_newComps_len (scanActivate st1 ca a) cb b
         have h2 := scanActivate_newComps_len st1 ca a; have h0 : st1.newComps.length = st.newComps.length := rfl; omega⟩
    · intro e' he' hF
      rw [hst'_eq] at hF ⊢; simp only [scanActivate_insFlag, scanActivate_cmpMap, st1] at hF ⊢
      have hne : e' ≠ e := by rintro rfl; simp at hF
      rw [Function.update_of_ne hne] at hF
      have he'0 : e' ∈ cs.G.E := by simpa [cs', compLSFStepSingle, MGraph.applyUpdate, hne] using he'
      obtain ⟨h0, hct, hch, hft, hfh⟩ := hS.ins_ok e' he'0 hF
      have ht' : cs'.G.tail e' = cs.G.tail e' := by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hne]
      have hh' : cs'.G.head e' = cs.G.head e' := by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hne]
      rw [ht', hh']
      exact ⟨h0, hct, hch, fun h => hft (hact_false_of _ (by rw [hst'_eq]; exact h)),
        fun h => hfh (hact_false_of _ (by rw [hst'_eq]; exact h))⟩
    · intro e' hT he'
      rw [hst'_eq] at hT; simp only [scanActivate_insFlag, st1] at hT
      by_cases hEq : e' = e
      · subst hEq
        have ht' : cs'.G.tail e' = a := by simp [cs', compLSFStepSingle, MGraph.applyUpdate]
        have hh' : cs'.G.head e' = b := by simp [cs', compLSFStepSingle, MGraph.applyUpdate]
        exact ⟨⟨ca, hca, by rw [ht', hVcomp ca hca]; exact haV, (hact_iff ca).mpr (Or.inr (Or.inl rfl))⟩,
               ⟨cb, hcb, by rw [hh', hVcomp cb hcb]; exact hbV, (hact_iff cb).mpr (Or.inr (Or.inr rfl))⟩⟩
      · rw [Function.update_of_ne hEq] at hT
        have he'0 : e' ∈ cs.G.E := by simpa [cs', compLSFStepSingle, MGraph.applyUpdate, hEq] using he'
        obtain ⟨⟨c1, hc1, h1V, h1A⟩, ⟨c2, hc2, h2V, h2A⟩⟩ := hS.ins_active e' hT he'0
        have ht' : cs'.G.tail e' = cs.G.tail e' := by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hEq]
        have hh' : cs'.G.head e' = cs.G.head e' := by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hEq]
        exact ⟨⟨c1, hc1, by rw [ht', hVcomp c1 hc1]; exact h1V, hact_mono c1 h1A⟩,
               ⟨c2, hc2, by rw [hh', hVcomp c2 hc2]; exact h2V, hact_mono c2 h2A⟩⟩
  | delete e =>
    have heG : e ∈ cs.G.E := hu
    have hVcomp : ∀ c (hc : c < comps.length), (cs'.compSt comps[c]).G.V = (cs.compSt comps[c]).G.V := fun c hc => by
      have hCin := (hCiff comps[c]).mp (List.getElem_mem hc)
      show ((applyLSFBatch (cs.compSt comps[c]) _).G).V = _
      rw [applyLSFBatch_G_of_valid (hI.hCompLSF _ hCin).1 (projCompUpdateG_valid hI hu hCin)]
      simp only [projCompUpdateG]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate]
    have hG_V : cs'.G.V = cs.G.V := by simp [cs', compLSFStepSingle, MGraph.applyUpdate]
    set st1 : ScanBatchState := { st with delFlag := Function.update st.delFlag e true, delEdges := st.delEdges ++ [e] }
    have hproj_ne : ∀ c (hc : c < comps.length),
        projCompUpdateG cs.G (cs.compSt comps[c]).G (.delete e) ≠ [] ↔ e ∈ (cs.compSt comps[c]).G.E :=
      fun _ _ => by simp [projCompUpdateG]
    by_cases hins : st.insFlag e = true
    · have hst'_eq : st' = st1 := by simp [st', st1, scanBatchStep, hins]
      have hact_proj : ∀ c (hc : c < comps.length),
          st'.actFlag c = true ↔ st.actFlag c = true ∨ projCompUpdateG cs.G (cs.compSt comps[c]).G (.delete e) ≠ [] := by
        intro c hc; rw [hst'_eq, hproj_ne c hc]
        refine ⟨Or.inl, fun h => h.elim id fun heC => ?_⟩
        by_contra hF; simp only [Bool.not_eq_true] at hF
        have hnc : e ∉ cs.crossEdges := Finset.disjoint_left.mp (hS.cross_inact c hc hF).1 heC
        have htC := (comp_of_delete_nonCross hI heG hnc ((hCiff _).mp (List.getElem_mem hc))).mp heC
        obtain ⟨⟨c1, hc1, h1V, h1A⟩, _⟩ := hS.ins_active e hins heG
        have hEq : c = c1 := by
          by_contra hne
          exact Finset.disjoint_left.mp (hI.hV_disj _ ((hCiff _).mp (List.getElem_mem hc)) _
            ((hCiff _).mp (List.getElem_mem hc1)) (fun h => hne (hCnd.getElem_inj_iff.mp h))) htC h1V
        subst hEq; rw [h1A] at hF; cases hF
      refine ⟨⟨by rw [hG_V]; exact hS.v_mono,
        fun c hc v hv => by rw [hst'_eq]; exact hS.cmp_ok c hc v (hVcomp c hc ▸ hv),
        fun v hv => by rw [hst'_eq]; exact hS.orig_in v (hG_V ▸ hv),
        fun c hc v hv => by rw [hst'_eq]; exact hS.orig_same_comp c hc v (hVcomp c hc ▸ hv),
        fun v hv => by rw [hst'_eq]; exact hS.orig_zero_outside v (hG_V ▸ hv),
        fun e' he' hF => by
          rw [hst'_eq] at hF ⊢; exact hS.ins_ok e' (Finset.mem_erase.mp he').2 hF,
        fun e' hT he' => by
          rw [hst'_eq] at hT ⊢
          obtain ⟨⟨c1, hc1, h1V, h1A⟩, ⟨c2, hc2, h2V, h2A⟩⟩ := hS.ins_active e' hT (Finset.mem_erase.mp he').2
          exact ⟨⟨c1, hc1, by rw [hVcomp c1 hc1]; exact h1V, h1A⟩,
                 ⟨c2, hc2, by rw [hVcomp c2 hc2]; exact h2V, h2A⟩⟩,
        fun c hc hi => by rw [hst'_eq]; exact hS.act_init c hc hi,
        fun c hc hF => by
          obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
          exact compLSFStepSingle_crossInactive hI hu ((hCiff _).mp (List.getElem_mem hc)) hnt
            (hS.cross_inact c hc hF0).1 (hS.cross_inact c hc hF0).2,
        by rw [hst'_eq]; exact hS.new_nodup, by rw [hst'_eq]; exact hS.new_lt,
        fun c hc => by rw [hst'_eq]; exact hS.new_iff c hc, by rw [hst'_eq]; exact hS.new_wit,
        fun e' => by
          rw [hst'_eq]; dsimp only [st1]
          by_cases hEq : e' = e
          · subst hEq; simp
          · rw [Function.update_of_ne hEq]; simp [hEq, hS.delFlag_iff e'],
        fun e' => by rw [hst'_eq]; exact hS.insFlag_iff e'⟩,
        fun c hc hF => by
          obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
          show applyLSFBatch (cs.compSt comps[c]) _ = cs₀.compSt comps[c]; rw [hnt]; exact hUnch c hc hF0,
        hact_proj, by rw [hst'_eq]; ext x; simp [st1, batchDeletes, addDel],
        by rw [hst'_eq]; simp [st1], by rw [hst'_eq]; simp [st1], by rw [hst'_eq]; simp [st1]⟩
    · have hinsF : st.insFlag e = false := by cases h : st.insFlag e <;> simp_all
      obtain ⟨he0, hct, hch, hft, hfh⟩ := hS.ins_ok e heG hinsF
      obtain ⟨cu, hcu, huV⟩ := comp_idx_of_mem_V hI hCiff (hI.hG_val e heG).1
      obtain ⟨cv, hcv, hvV⟩ := comp_idx_of_mem_V hI hCiff (hI.hG_val e heG).2
      have hcmpu : st.cmpMap (cs₀.G.tail e) = cu := hct.trans (hS.cmp_ok cu hcu _ huV)
      have hcmpv : st.cmpMap (cs₀.G.head e) = cv := hch.trans (hS.cmp_ok cv hcv _ hvV)
      have hst'_eq : st' = scanActivate (scanActivate st1 cu (cs₀.G.tail e)) cv (cs₀.G.head e) := by
        simp [st', st1, scanBatchStep, hinsF, hcmpu, hcmpv]
      have hact_iff : ∀ c, st'.actFlag c = true ↔ st.actFlag c = true ∨ c = cu ∨ c = cv := fun c => by
        rw [hst'_eq, scanActivate_actFlag, scanActivate_actFlag]; simp [st1, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
      have hact_proj : ∀ c (hc : c < comps.length),
          st'.actFlag c = true ↔ st.actFlag c = true ∨ projCompUpdateG cs.G (cs.compSt comps[c]).G (.delete e) ≠ [] := by
        intro c hc; rw [hact_iff c, hproj_ne c hc]
        constructor
        · rintro (h | rfl | rfl)
          · exact Or.inl h
          · by_cases hA : st.actFlag c = true
            · exact Or.inl hA
            · simp only [Bool.not_eq_true] at hA
              have hnc : e ∉ cs.crossEdges := fun hcr => (hS.cross_inact c hc hA).2 e hcr |>.1 huV
              exact Or.inr ((comp_of_delete_nonCross hI heG hnc ((hCiff _).mp (List.getElem_mem hc))).mpr huV)
          · by_cases hA : st.actFlag c = true
            · exact Or.inl hA
            · simp only [Bool.not_eq_true] at hA
              have hnc : e ∉ cs.crossEdges := fun hcr => (hS.cross_inact c hc hA).2 e hcr |>.2 hvV
              obtain ⟨C', hC', heC'⟩ := hI.hEdge_cover e heG hnc
              have hhC' : cs.G.head e ∈ (cs.compSt C').G.V := by
                rw [← (hI.hNonCross_ends C' hC' e heC' hnc).2]; exact ((hI.hCompLSF C' hC').1.hG_val e heC').2
              have hCeq : comps[c] = C' := by
                by_contra hne; exact Finset.disjoint_left.mp
                  (hI.hV_disj _ ((hCiff _).mp (List.getElem_mem hc)) _ hC' hne) hvV hhC'
              exact Or.inr (hCeq ▸ heC')
        · rintro (h | heC)
          · exact Or.inl h
          · by_cases hA : st.actFlag c = true
            · exact Or.inl hA
            · simp only [Bool.not_eq_true] at hA
              have hnc : e ∉ cs.crossEdges := Finset.disjoint_left.mp (hS.cross_inact c hc hA).1 heC
              have htC := (comp_of_delete_nonCross hI heG hnc ((hCiff _).mp (List.getElem_mem hc))).mp heC
              have hEq : c = cu := by
                by_contra hne; exact Finset.disjoint_left.mp
                  (hI.hV_disj _ ((hCiff _).mp (List.getElem_mem hc)) _ ((hCiff _).mp (List.getElem_mem hcu))
                    (fun h => hne (hCnd.getElem_inj_iff.mp h))) htC huV
              exact Or.inr (Or.inl hEq)
      have hst1_new := scanActivate_preserves_new (st := st1) (v := cs₀.G.tail e) hcu
        (fun hF => by rw [← hft (by rw [hcmpu]; exact hF), ← hUnch cu hcu hF]; exact huV)
        hS.new_nodup hS.new_lt hS.new_iff hS.new_wit hS.act_init
      have hst2_new := scanActivate_preserves_new (v := cs₀.G.head e) hcv
        (fun hF => by
          have hF0 : st.actFlag cv = false := by
            by_contra hT; simp only [Bool.not_eq_false] at hT
            have := scanActivate_actFlag st1 cu (cs₀.G.tail e) cv; simp [st1, hT] at this; rw [hF] at this; cases this
          rw [← hfh (by rw [hcmpv]; exact hF0), ← hUnch cv hcv hF0]; exact hvV)
        hst1_new.1 hst1_new.2.1 hst1_new.2.2.1 hst1_new.2.2.2.1 hst1_new.2.2.2.2
      refine ⟨⟨by rw [hG_V]; exact hS.v_mono,
        fun c hc v hv => by rw [hst'_eq]; simp [st1]; exact hS.cmp_ok c hc v (hVcomp c hc ▸ hv),
        fun v hv => by rw [hst'_eq]; simp [st1]; exact hS.orig_in v (hG_V ▸ hv),
        fun c hc v hv => by rw [hst'_eq]; simp [st1]; exact hS.orig_same_comp c hc v (hVcomp c hc ▸ hv),
        fun v hv => by rw [hst'_eq]; simp [st1]; exact hS.orig_zero_outside v (hG_V ▸ hv),
        fun e' he' hF => by
          rw [hst'_eq] at hF ⊢; simp only [scanActivate_insFlag, scanActivate_cmpMap, st1] at hF ⊢
          obtain ⟨h0', hct', hch', hft', hfh'⟩ := hS.ins_ok e' (Finset.mem_erase.mp he').2 hF
          exact ⟨h0', hct', hch', fun h => hft' (hact_false_of _ (by rw [hst'_eq]; exact h)),
            fun h => hfh' (hact_false_of _ (by rw [hst'_eq]; exact h))⟩,
        fun e' hT he' => by
          rw [hst'_eq] at hT; simp only [scanActivate_insFlag, st1] at hT
          obtain ⟨⟨c1, hc1, h1V, h1A⟩, ⟨c2, hc2, h2V, h2A⟩⟩ := hS.ins_active e' hT (Finset.mem_erase.mp he').2
          exact ⟨⟨c1, hc1, by rw [hVcomp c1 hc1]; exact h1V, hact_mono c1 h1A⟩,
                 ⟨c2, hc2, by rw [hVcomp c2 hc2]; exact h2V, hact_mono c2 h2A⟩⟩,
        by rw [hst'_eq]; exact hst2_new.2.2.2.2,
        fun c hc hF => by
          obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
          exact compLSFStepSingle_crossInactive hI hu ((hCiff _).mp (List.getElem_mem hc)) hnt
            (hS.cross_inact c hc hF0).1 (hS.cross_inact c hc hF0).2,
        by rw [hst'_eq]; exact hst2_new.1, by rw [hst'_eq]; exact hst2_new.2.1,
        by rw [hst'_eq]; exact hst2_new.2.2.1, by rw [hst'_eq]; exact hst2_new.2.2.2.1,
        fun e' => by
          rw [hst'_eq]; simp only [scanActivate_delFlag, scanActivate_delEdges, st1]
          by_cases hEq : e' = e
          · subst hEq; simp
          · rw [Function.update_of_ne hEq]; simp [hEq, hS.delFlag_iff e'],
        fun e' => by rw [hst'_eq]; simp [st1, hS.insFlag_iff e']⟩,
        fun c hc hF => by
          obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
          show applyLSFBatch (cs.compSt comps[c]) _ = cs₀.compSt comps[c]; rw [hnt]; exact hUnch c hc hF0,
        hact_proj, by rw [hst'_eq]; ext x; simp [st1, batchDeletes, addDel],
        by rw [hst'_eq]; simp [st1], by rw [hst'_eq]; simp [st1],
        by rw [hst'_eq]; have h1 := scanActivate_newComps_len (scanActivate st1 cu (cs₀.G.tail e)) cv (cs₀.G.head e)
           have h2 := scanActivate_newComps_len st1 cu (cs₀.G.tail e); have h0 : st1.newComps.length = st.newComps.length := rfl; omega⟩
  | split v v' St Sh =>
    obtain ⟨cv, hcv, hvV⟩ := comp_idx_of_mem_V hI hCiff hu.1
    have hcmpv : st.cmpMap v = cv := hS.cmp_ok cv hcv v hvV
    have hv'_not : v' ∉ cs.G.V := hu.2.1
    have hG_V : cs'.G.V = insert v' cs.G.V := by simp [cs', compLSFStepSingle, MGraph.applyUpdate]
    have hG_E : cs'.G.E = cs.G.E := by simp [cs', compLSFStepSingle, MGraph.applyUpdate]
    have hVcomp : ∀ c (hc : c < comps.length),
        (cs'.compSt comps[c]).G.V =
          if c = cv then insert v' (cs.compSt comps[c]).G.V else (cs.compSt comps[c]).G.V := fun c hc => by
      have hCin := (hCiff comps[c]).mp (List.getElem_mem hc)
      show ((applyLSFBatch (cs.compSt comps[c]) _).G).V = _
      rw [applyLSFBatch_G_of_valid (hI.hCompLSF _ hCin).1 (projCompUpdateG_valid hI hu hCin)]
      by_cases hEq : c = cv
      · subst hEq; simp [projCompUpdateG, hvV, MGraph.applyBatch, MGraph.applyUpdate]
      · have hnot : v ∉ (cs.compSt comps[c]).G.V := fun h =>
          Finset.disjoint_left.mp (hI.hV_disj _ hCin _ ((hCiff _).mp (List.getElem_mem hcv))
            (fun hC => hEq (hCnd.getElem_inj_iff.mp hC))) h hvV
        simp [projCompUpdateG, hnot, hEq, MGraph.applyBatch]
    set ov' : ℕ := if st.origVert v = 0 then v + 1 else st.origVert v
    set st1 : ScanBatchState := { st with
      cmpMap := Function.update st.cmpMap v' cv, origVert := Function.update st.origVert v' ov' }
    have hst'_eq : st' = scanActivate st1 cv v := by simp [st', st1, ov', scanBatchStep, hcmpv]
    have hact_iff : ∀ c, st'.actFlag c = true ↔ st.actFlag c = true ∨ c = cv := fun c => by
      rw [hst'_eq, scanActivate_actFlag]; simp [st1, Bool.or_eq_true, decide_eq_true_eq]
    have hact_proj : ∀ c (hc : c < comps.length),
        st'.actFlag c = true ↔ st.actFlag c = true ∨ projCompUpdateG cs.G (cs.compSt comps[c]).G (.split v v' St Sh) ≠ [] := by
      intro c hc; rw [hact_iff c]
      have hCin := (hCiff comps[c]).mp (List.getElem_mem hc)
      have hv_iff : v ∈ (cs.compSt comps[c]).G.V ↔ c = cv := ⟨fun h => by
        by_contra hne; exact Finset.disjoint_left.mp (hI.hV_disj _ hCin _ ((hCiff _).mp (List.getElem_mem hcv))
          (fun hEq => hne (hCnd.getElem_inj_iff.mp hEq))) h hvV, fun h => h ▸ hvV⟩
      simp only [projCompUpdateG]; by_cases h1 : v ∈ (cs.compSt comps[c]).G.V <;> simp [h1, ← hv_iff]
    have htrace_v' : traceOrigVert st'.origVert v' = traceOrigVert st.origVert v := by
      rw [hst'_eq]; unfold traceOrigVert
      simp only [scanActivate_origVert, st1, Function.update_self, ov']
      by_cases h0 : st.origVert v = 0 <;> simp [h0]
    have hst1_new := scanActivate_preserves_new (st := st1) hcv
      (fun hF => by rw [← hUnch cv hcv hF]; exact hvV)
      hS.new_nodup hS.new_lt hS.new_iff hS.new_wit hS.act_init
    refine ⟨⟨by rw [hG_V]; exact hS.v_mono.trans (Finset.subset_insert _ _),
      ?_, ?_, ?_, ?_, ?_, ?_, by rw [hst'_eq]; exact hst1_new.2.2.2.2,
      fun c hc hF => by
        obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
        exact compLSFStepSingle_crossInactive hI hu ((hCiff _).mp (List.getElem_mem hc)) hnt
          (hS.cross_inact c hc hF0).1 (hS.cross_inact c hc hF0).2,
      by rw [hst'_eq]; exact hst1_new.1, by rw [hst'_eq]; exact hst1_new.2.1,
      by rw [hst'_eq]; exact hst1_new.2.2.1, by rw [hst'_eq]; exact hst1_new.2.2.2.1,
      fun e' => by rw [hst'_eq]; simp [st1, hS.delFlag_iff e'],
      fun e' => by rw [hst'_eq]; simp [st1, hS.insFlag_iff e']⟩,
      fun c hc hF => by
        obtain ⟨hF0, hnt⟩ := proj_nil_of_actFlag_false hact_proj hc hF
        show applyLSFBatch (cs.compSt comps[c]) _ = cs₀.compSt comps[c]; rw [hnt]; exact hUnch c hc hF0,
      hact_proj, by rw [hst'_eq]; simp [st1, batchDeletes, addDel],
      by rw [hst'_eq]; simp [st1], by rw [hst'_eq]; simp [st1],
      by rw [hst'_eq]; have h1 := scanActivate_newComps_len st1 cv v; have h0 : st1.newComps.length = st.newComps.length := rfl; omega⟩
    · intro c hc x hx; rw [hVcomp c hc] at hx; rw [hst'_eq]; simp only [scanActivate_cmpMap, st1]
      by_cases hxEq : x = v'
      · subst hxEq
        have hcEq : c = cv := by
          by_contra hne; simp only [hne, ↓reduceIte] at hx
          exact hv'_not (hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨comps[c], (hCiff _).mp (List.getElem_mem hc), hx⟩)
        subst hcEq; simp
      · rw [Function.update_of_ne hxEq]
        exact hS.cmp_ok c hc x (by split_ifs at hx; exact (Finset.mem_insert.mp hx).resolve_left hxEq; exact hx)
    · intro x hx; rw [hG_V, Finset.mem_insert] at hx
      rcases hx with rfl | hx0
      · rw [htrace_v']; exact hS.orig_in v hu.1
      · have hne : x ≠ v' := fun h => hv'_not (h ▸ hx0)
        unfold traceOrigVert; rw [hst'_eq]; simp only [scanActivate_origVert, st1, Function.update_of_ne hne]
        exact hS.orig_in x hx0
    · intro c hc x hx; rw [hVcomp c hc] at hx
      by_cases hxEq : x = v'
      · subst hxEq
        have hcEq : c = cv := by
          by_contra hne; simp only [hne, ↓reduceIte] at hx
          exact hv'_not (hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨comps[c], (hCiff _).mp (List.getElem_mem hc), hx⟩)
        subst hcEq; rw [htrace_v']; exact hS.orig_same_comp c hc v hvV
      · unfold traceOrigVert; rw [hst'_eq]; simp only [scanActivate_origVert, st1, Function.update_of_ne hxEq]
        exact hS.orig_same_comp c hc x (by split_ifs at hx; exact (Finset.mem_insert.mp hx).resolve_left hxEq; exact hx)
    · intro x hx; rw [hG_V, Finset.mem_insert, not_or] at hx
      rw [hst'_eq]; simp only [scanActivate_origVert, st1, Function.update_of_ne hx.1]
      exact hS.orig_zero_outside x hx.2
    · intro e' he' hF
      rw [hG_E] at he'; rw [hst'_eq] at hF ⊢; simp only [scanActivate_insFlag, scanActivate_cmpMap, st1] at hF ⊢
      obtain ⟨h0, hct, hch, hft, hfh⟩ := hS.ins_ok e' he' hF
      have hneT0 : cs₀.G.tail e' ≠ v' := fun h => hv'_not (h ▸ hS.v_mono (hG0_val e' h0).1)
      have hneH0 : cs₀.G.head e' ≠ v' := fun h => hv'_not (h ▸ hS.v_mono (hG0_val e' h0).2)
      have hneT : cs.G.tail e' ≠ v' := fun h => hv'_not (h ▸ (hI.hG_val e' he').1)
      have hneH : cs.G.head e' ≠ v' := fun h => hv'_not (h ▸ (hI.hG_val e' he').2)
      have hct' : Function.update st.cmpMap v' cv (cs₀.G.tail e') =
          Function.update st.cmpMap v' cv (cs'.G.tail e') := by
        rw [Function.update_of_ne hneT0]
        change st.cmpMap (cs₀.G.tail e') = Function.update st.cmpMap v' cv
          (if e' ∈ St ∧ cs.G.tail e' = v then v' else cs.G.tail e')
        split_ifs with hmv
        · simp [Function.update_self, hct, hmv.2, hcmpv]
        · rw [Function.update_of_ne hneT]; exact hct
      have hch' : Function.update st.cmpMap v' cv (cs₀.G.head e') =
          Function.update st.cmpMap v' cv (cs'.G.head e') := by
        rw [Function.update_of_ne hneH0]
        change st.cmpMap (cs₀.G.head e') = Function.update st.cmpMap v' cv
          (if e' ∈ Sh ∧ cs.G.head e' = v then v' else cs.G.head e')
        split_ifs with hmv
        · simp [Function.update_self, hch, hmv.2, hcmpv]
        · rw [Function.update_of_ne hneH]; exact hch
      refine ⟨h0, hct', hch', ?_, ?_⟩
      · intro hF'; rw [Function.update_of_ne hneT0] at hF'
        have hF0 := hact_false_of _ (by rw [hst'_eq]; exact hF')
        have hne_cv : st.cmpMap (cs₀.G.tail e') ≠ cv := fun hEq => by
          have hT := (hact_iff cv).mpr (Or.inr rfl); rw [hst'_eq] at hT; rw [hEq] at hF'
          have hF1 : (scanActivate st1 cv v).actFlag cv = false := hF'
          rw [hF1] at hT; cases hT
        have hne_v : cs.G.tail e' ≠ v := fun hEq => hne_cv (hct.trans (hEq ▸ hcmpv))
        exact (show cs'.G.tail e' = cs.G.tail e' by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hne_v]).trans (hft hF0)
      · intro hF'; rw [Function.update_of_ne hneH0] at hF'
        have hF0 := hact_false_of _ (by rw [hst'_eq]; exact hF')
        have hne_cv : st.cmpMap (cs₀.G.head e') ≠ cv := fun hEq => by
          have hT := (hact_iff cv).mpr (Or.inr rfl); rw [hst'_eq] at hT; rw [hEq] at hF'
          have hF1 : (scanActivate st1 cv v).actFlag cv = false := hF'
          rw [hF1] at hT; cases hT
        have hne_v : cs.G.head e' ≠ v := fun hEq => hne_cv (hch.trans (hEq ▸ hcmpv))
        exact (show cs'.G.head e' = cs.G.head e' by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hne_v]).trans (hfh hF0)
    · intro e' hT he'
      rw [hG_E] at he'; rw [hst'_eq] at hT; simp only [scanActivate_insFlag, st1] at hT
      obtain ⟨⟨c1, hc1, h1V, h1A⟩, ⟨c2, hc2, h2V, h2A⟩⟩ := hS.ins_active e' hT he'
      exact ⟨by by_cases hmv : e' ∈ St ∧ cs.G.tail e' = v
                · refine ⟨cv, hcv, ?_, (hact_iff cv).mpr (Or.inr rfl)⟩
                  rw [show cs'.G.tail e' = v' by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hmv], hVcomp cv hcv]; simp
                · refine ⟨c1, hc1, ?_, hact_mono c1 h1A⟩
                  rw [show cs'.G.tail e' = cs.G.tail e' by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hmv], hVcomp c1 hc1]
                  split_ifs; exact Finset.mem_insert_of_mem h1V; exact h1V,
             by by_cases hmv : e' ∈ Sh ∧ cs.G.head e' = v
                · refine ⟨cv, hcv, ?_, (hact_iff cv).mpr (Or.inr rfl)⟩
                  rw [show cs'.G.head e' = v' by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hmv], hVcomp cv hcv]; simp
                · refine ⟨c2, hc2, ?_, hact_mono c2 h2A⟩
                  rw [show cs'.G.head e' = cs.G.head e' by simp [cs', compLSFStepSingle, MGraph.applyUpdate, hmv], hVcomp c2 hc2]
                  split_ifs; exact Finset.mem_insert_of_mem h2V; exact h2V⟩

/-- **Exact correctness of `scanBatchFold` over an entire batch `U`.** -/
theorem scanBatchFold_correct {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {U : List Update} {comps : List (Finset ℕ)}
    {cmpMap₀ : ℕ → ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hCnd : comps.Nodup) (hCiff : ∀ C, C ∈ comps ↔ C ∈ components tr.cs.G₀)
    (hCmp0 : ∀ c (hc : c < comps.length), ∀ v ∈ (tr.cs.compSt comps[c]).G.V, cmpMap₀ v = c)
    (hCross : AsmFirstCrossInactiveInv tr) :
    let st0 : ScanBatchState :=
      { cmpMap := cmpMap₀
        actFlag := fun c => if hc : c < comps.length then decide (comps[c] ∈ tr.activeComps) else false
        insFlag := fun _ => false
        delFlag := fun _ => false
        origVert := fun _ => 0
        newComps := []
        delEdges := []
        insEdges := [] }
    let st' := scanBatchFold tr.cs.G st0 U
    let cs' := compLSFBatch tr.cs U
    (∀ c (hc : c < comps.length), ∀ v ∈ (cs'.compSt comps[c]).G.V, st'.cmpMap v = c) ∧
    (∀ v ∈ cs'.G.V, traceOrigVert st'.origVert v ∈ tr.cs.G.V) ∧
    (∀ c (hc : c < comps.length), ∀ v ∈ (cs'.compSt comps[c]).G.V,
      traceOrigVert st'.origVert v ∈ (tr.cs.compSt comps[c]).G.V) ∧
    (∀ c (hc : c < comps.length),
      st'.actFlag c = true ↔ comps[c] ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps)) ∧
    (st'.newComps.map Prod.fst).Nodup ∧
    (∀ p ∈ st'.newComps, p.1 < comps.length) ∧
    (∀ c (hc : c < comps.length),
      c ∈ st'.newComps.map Prod.fst ↔ comps[c] ∈ touchedCompsBatch tr.cs U \ tr.activeComps) ∧
    (∀ p ∈ st'.newComps, ∀ hc : p.1 < comps.length, p.2 ∈ (tr.cs.compSt comps[p.1]).G.V) ∧
    st'.delEdges.toFinset = batchDeletes U ∧
    (∀ e, st'.delFlag e = true ↔ e ∈ st'.delEdges) ∧
    (∀ e, st'.insFlag e = true ↔ e ∈ st'.insEdges) ∧
    st'.newComps.length ≤ 2 * U.length ∧
    st'.delEdges.length ≤ U.length ∧
    st'.insEdges.length ≤ U.length := by
  classical
  intro st0 st' cs'
  have hS0 : ScanInv comps tr.activeComps tr.cs tr.cs st0 :=
    ⟨Finset.Subset.rfl, hCmp0, fun v hv => by simp [traceOrigVert, st0, hv],
     fun c hc v hv => by simp [traceOrigVert, st0, hv], fun _ _ => rfl,
     fun e he _ => ⟨he, rfl, rfl, fun _ => rfl, fun _ => rfl⟩,
     fun _ h => by simp [st0] at h,
     fun c hc hi => by simp [st0, hc, hi],
     fun c hc hF => by
       have hni : comps[c] ∉ tr.activeComps := by intro hi; simp [st0, hc, hi] at hF
       exact hCross _ ((hCiff _).mp (List.getElem_mem hc)) hni,
     List.nodup_nil, (fun _ h => by cases h),
     (fun c hc => by simp [st0, hc]), (fun _ h => by cases h),
     fun _ => by simp [st0], fun _ => by simp [st0]⟩
  suffices H : ∀ (U : List Update) (cs : CompLSFState) (st : ScanBatchState),
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U → cs.G₀ = tr.cs.G₀ →
      ScanInv comps tr.activeComps tr.cs cs st →
      (∀ c (hc : c < comps.length), st.actFlag c = false → cs.compSt comps[c] = tr.cs.compSt comps[c]) →
      let cs₁ := compLSFBatch cs U
      let st₁ := scanBatchFold tr.cs.G st U
      ScanInv comps tr.activeComps tr.cs cs₁ st₁ ∧
      (∀ c (hc : c < comps.length),
        st₁.actFlag c = true ↔ st.actFlag c = true ∨ projCompBatchG cs.G (cs.compSt comps[c]).G U ≠ []) ∧
      st₁.delEdges.toFinset = st.delEdges.toFinset ∪ batchDeletes U ∧
      st₁.newComps.length ≤ st.newComps.length + 2 * U.length ∧
      st₁.delEdges.length ≤ st.delEdges.length + U.length ∧
      st₁.insEdges.length ≤ st.insEdges.length + U.length by
    obtain ⟨hSf, hact, hdel, hnewL, hdelL, hinsL⟩ := H U tr.cs st0 hI hU rfl hS0 (fun _ _ _ => rfl)
    have hact_eq : ∀ c (hc : c < comps.length),
        st'.actFlag c = true ↔ comps[c] ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps) := by
      intro c hc
      rw [hact c hc]
      simp only [st0, hc, ↓reduceDIte, decide_eq_true_eq, Finset.mem_union, Finset.mem_sdiff,
        touchedCompsBatch, Finset.mem_filter, (hCiff _).mp (List.getElem_mem hc), true_and]
      tauto
    refine ⟨hSf.cmp_ok, hSf.orig_in, hSf.orig_same_comp, hact_eq, hSf.new_nodup, hSf.new_lt, ?_,
      hSf.new_wit, by simpa [st0] using hdel, hSf.delFlag_iff, hSf.insFlag_iff,
      by simpa [st0] using hnewL, by simpa [st0] using hdelL, by simpa [st0] using hinsL⟩
    intro c hc
    rw [hSf.new_iff c hc, hact_eq c hc]
    simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  intro U'
  induction U' with
  | nil =>
    intro cs st _ _ _ hS _
    refine ⟨hS, fun c _ => by simp [scanBatchFold, projCompBatchG],
      by simp [scanBatchFold, batchDeletes], by simp [scanBatchFold],
      by simp [scanBatchFold], by simp [scanBatchFold]⟩
  | cons u rest ih =>
    intro cs st hIcs hUcs hG₀ hS hUnch
    have hCiff' : ∀ C, C ∈ comps ↔ C ∈ components cs.G₀ := by rw [hG₀]; exact hCiff
    obtain ⟨hS1, hUnch1, hact1, hdel1, hins1, hdelL1, hnew1⟩ :=
      scanBatchStep_inv hI.hG_val hIcs hUcs.1 hCnd hCiff' hS hUnch
    obtain ⟨hS2, hact2, hdel2, hnew2, hdelL2, hins2⟩ :=
      ih (compLSFStepSingle cs u) (scanBatchStep tr.cs.G st u)
        (compLSFInv_step hIcs hUcs.1) hUcs.2 hG₀ hS1 hUnch1
    have hdel_cons : batchDeletes (u :: rest) = batchDeletes [u] ∪ batchDeletes rest := by
      change (u :: rest).foldl addDel ∅ = _
      have hfold : ∀ (S : Finset ℕ) (L : List Update), L.foldl addDel S = S ∪ L.foldl addDel ∅ := by
        intro S L; induction L generalizing S with
        | nil => simp
        | cons x xs ihL =>
          simp only [List.foldl_cons]
          rw [ihL (addDel S x), ihL (addDel ∅ x)]
          cases x <;> simp [addDel]
      simp only [List.foldl_cons, List.foldl_nil, batchDeletes]
      exact hfold (addDel ∅ u) rest
    refine ⟨hS2, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      change (scanBatchFold tr.cs.G (scanBatchStep tr.cs.G st u) rest).actFlag c = true ↔ _
      rw [hact2 c hc, hact1 c hc]
      have hCin := (hCiff' comps[c]).mp (List.getElem_mem hc)
      have hG1 : ((compLSFStepSingle cs u).compSt comps[c]).G =
          (cs.compSt comps[c]).G.applyBatch (projCompUpdateG cs.G (cs.compSt comps[c]).G u) :=
        applyLSFBatch_G_of_valid (hIcs.hCompLSF _ hCin).1 (projCompUpdateG_valid hIcs hUcs.1 hCin)
      simp only [projCompBatchG, ne_eq, List.append_eq_nil_iff, not_and_or, ← hG1]
      change _ ↔ _ ∨ _ ∨ projCompBatchG (compLSFStepSingle cs u).G ((compLSFStepSingle cs u).compSt comps[c]).G rest ≠ []
      tauto
    · change (scanBatchFold tr.cs.G (scanBatchStep tr.cs.G st u) rest).delEdges.toFinset = _
      rw [hdel2, hdel1, hdel_cons, Finset.union_assoc]
    · change (scanBatchFold tr.cs.G (scanBatchStep tr.cs.G st u) rest).newComps.length ≤ _
      simp only [List.length_cons]; omega
    · change (scanBatchFold tr.cs.G (scanBatchStep tr.cs.G st u) rest).delEdges.length ≤ _
      simp only [List.length_cons]; omega
    · change (scanBatchFold tr.cs.G (scanBatchStep tr.cs.G st u) rest).insEdges.length ≤ _
      simp only [List.length_cons]; omega

end

end MinCostFlow.SparseCore.Program
