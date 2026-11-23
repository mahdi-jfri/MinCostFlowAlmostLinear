module

public import MinCostFlow.LinkCut.Prog.MathForestBridge

/-!
# Exposed auxiliary paths, `IsStepWalk`, `pathSum`, and `pathMin` bridges

Proves that when an auxiliary tree `t ∈ x.trees` has `OFF_PPAR = 0`, starting vertex `u + 1`,
and ending vertex `v + 1`, its `evalMemSteps` decodes to the unique simple `PathStep` walk
`findSteps F.edges u v` in `F`, giving exact correspondence for `F.pathSum u v` and
`F.pathMin u v`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

theorem wrap_listRawCost_of_stepMatches {P : ℕ} {e_list : List PathStep} {r_list : List RawStep}
    (hrel : List.Forall₂ (fun r s => ∃ ed, stepMatchesEdge P ed s.edge r ∧ s.fwd = r.fwd)
      r_list e_list) :
    listRawCost r_list = stepsCost e_list := by
  induction hrel with
  | nil => simp [listRawCost, stepsCost]
  | @cons r s rs ss hrs _ ih =>
      rcases hrs with ⟨ed, hsm, hfwd⟩
      have hsc := stepMatchesEdge_signedCost hsm
      have hf' : s.signedCost = (r.toPathStep s.edge).signedCost := by
        cases hrf : r.fwd <;> simp [PathStep.signedCost, RawStep.toPathStep, hfwd, hrf]
      simp only [listRawCost, stepsCost, List.map_cons, List.sum_cons] at ih ⊢
      have heq_sc : r.signedCost = s.signedCost := hsc.trans hf'.symm
      omega

theorem listIntMinAgg_matches_stepsMinHit {P : ℕ} {r_list : List RawStep} {e_list : List PathStep}
    (hrel : List.Forall₂ (fun r s => ∃ ed, stepMatchesEdge P ed s.edge r ∧ s.fwd = r.fwd)
      r_list e_list)
    (hne : e_list ≠ []) :
    let agg := listIntMinAgg (r_list.map fun r => (r.nodeId, r.dirAvail))
    ∃ (hit : PathHit) (rmin : RawStep) (smin : PathStep),
      stepsMinHit e_list = some hit ∧
      agg.has = true ∧
      agg.first = rmin.nodeId ∧
      (agg.val : ℚ) / ((2 : ℚ) ^ P) = hit.avail ∧
      rmin ∈ r_list ∧
      smin ∈ e_list ∧
      (∃ ed, stepMatchesEdge P ed smin.edge rmin ∧ smin.fwd = rmin.fwd) ∧
      smin.toHit = hit := by
  induction hrel with
  | nil => exact absurd rfl hne
  | @cons r s rs ss hrs hrest ih =>
      rcases hrs with ⟨ed, hsm, hfwd⟩
      have hsa : (r.dirAvail : ℚ) / ((2 : ℚ) ^ P) = s.toHit.avail := by
        rw [stepMatchesEdge_dirAvail hsm]
        cases hrf : r.fwd <;> simp [PathStep.toHit, PathStep.dirAvail, RawStep.toPathStep, hfwd, hrf]
      cases hss : ss with
      | nil =>
          have hrs_nil : rs = [] := List.forall₂_nil_right_iff.1 (hss ▸ hrest)
          subst hrs_nil
          refine ⟨s.toHit, r, s, by simp [stepsMinHit], rfl, rfl, hsa,
            List.mem_cons_self, List.mem_cons_self, ⟨ed, hsm, hfwd⟩, rfl⟩
      | cons s' ss' =>
          have hss_ne : ss ≠ [] := by simp [hss]
          subst hss
          rcases ih hss_ne with ⟨hit1, r1, s1, hsm1, hhas1, hfirst1, hav1, hr1_in, hs1_in,
            ⟨ed1, hed1, hfw1⟩, hhit1⟩
          have h2p_pos : (0 : ℚ) < (2 : ℚ) ^ P := by positivity
          have hle_iff : r.dirAvail ≤ (listIntMinAgg (rs.map fun q => (q.nodeId, q.dirAvail))).val ↔
              s.toHit.avail ≤ hit1.avail := by
            rw [← hsa, ← hav1, div_le_div_iff_of_pos_right h2p_pos, Int.cast_le]
          rcases lt_trichotomy r.dirAvail
              (listIntMinAgg (rs.map fun q => (q.nodeId, q.dirAvail))).val with hlt | heq | hgt
          · have hsle : s.toHit.avail ≤ hit1.avail := hle_iff.1 (le_of_lt hlt)
            have hnot_lt : ¬ (listIntMinAgg (rs.map fun q => (q.nodeId, q.dirAvail))).val < r.dirAvail := by
              omega
            have hne_eq : r.dirAvail ≠ (listIntMinAgg (rs.map fun q => (q.nodeId, q.dirAvail))).val := by
              omega
            refine ⟨s.toHit, r, s, ?_, ?_, ?_, ?_,
              List.mem_cons_self, List.mem_cons_self, ⟨ed, hsm, hfwd⟩, rfl⟩
            · change (match stepsMinHit (s' :: ss') with
                | none => some s.toHit
                | some h1 => if s.toHit.avail ≤ h1.avail then some s.toHit else some h1) = some s.toHit
              rw [hsm1]; simp [hsle]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, hnot_lt, hne_eq]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, hnot_lt, hne_eq]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, hnot_lt, hne_eq, hsa]
          · have hsle : s.toHit.avail ≤ hit1.avail := hle_iff.1 (le_of_eq heq)
            refine ⟨s.toHit, r, s, ?_, ?_, ?_, ?_,
              List.mem_cons_self, List.mem_cons_self, ⟨ed, hsm, hfwd⟩, rfl⟩
            · change (match stepsMinHit (s' :: ss') with
                | none => some s.toHit
                | some h1 => if s.toHit.avail ≤ h1.avail then some s.toHit else some h1) = some s.toHit
              rw [hsm1]; simp [hsle]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, ← heq]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, ← heq]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, ← heq, hsa]
          · have hnot_sle : ¬ s.toHit.avail ≤ hit1.avail := fun h => by
              have := hle_iff.2 h; omega
            refine ⟨hit1, r1, s1, ?_, ?_, ?_, ?_,
              List.mem_cons_of_mem _ hr1_in, List.mem_cons_of_mem _ hs1_in, ⟨ed1, hed1, hfw1⟩, hhit1⟩
            · change (match stepsMinHit (s' :: ss') with
                | none => some s.toHit
                | some h1 => if s.toHit.avail ≤ h1.avail then some s.toHit else some h1) = some hit1
              rw [hsm1]; simp [hnot_sle]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, hgt]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, hgt, hfirst1]
            · simp [listIntMinAgg, combineIntMinAgg, hhas1, hgt, hav1]

/-- An exposed auxiliary tree `t ∈ x.trees` with `OFF_PPAR = 0`, starting at vertex `u + 1`
and ending at vertex `v + 1`, decodes via `evalMemSteps` to the unique simple path
`findSteps F.edges u v` in `F`. -/
theorem LctMemRep.pathTree_isStepWalk {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {t : AuxTree} (ht : t ∈ x.trees)
    {u v : ℕ} (hu : u < F.n) (hv : v < F.n)
    (hpp0 : nodeField mem (lctNodesBase b) t.rootId OFF_PPAR = 0)
    (hhead : (t.evalInorder (revFlag mem (lctNodesBase b)) false).head? = some (u + 1))
    (hlast : (t.evalInorder (revFlag mem (lctNodesBase b)) false).getLast? = some (v + 1)) :
    ∃ steps : List PathStep,
      findSteps F.edges u v = some steps ∧
      IsStepWalk F.edges u v steps ∧
      (steps.map PathStep.toRaw).Nodup ∧
      List.Forall₂ (fun r s => ∃ ed, stepMatchesEdge P ed s.edge r ∧ s.fwd = r.fwd)
        (evalMemSteps mem (lctNodesBase b) h L t false 0) steps := by
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let par := lctAuxParent mem nb cap
  let seq := lctTreeSeq mem nb cap t.rootId
  have hseq_def : seq = t.evalInorder (revFlag mem nb) false := hrep.lctTreeSeq_eq ht
  rw [← hseq_def] at hhead hlast
  have hpar_tree := hrep.auxParent_of_tree ht
  have hsf_trunc := hrep.splayForestOk_trunc
  have hnd_all : (x.trees.flatMap AuxTree.toList).Nodup :=
    hsf_trunc.1.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hseq_perm : seq.Perm t.toList := by
    rw [hseq_def]; exact t.evalInorder_perm _ _
  have hseq_nd : seq.Nodup :=
    hseq_perm.nodup_iff.2 (mem_nodup_of_flatMap_nodup hnd_all ht)
  have hraw_map := evalMemSteps_map_nodeId mem nb h L t false 0
  rw [← hseq_def] at hraw_map
  have hsub := hrep.subdivOk
  have hv_par := hsub.2.2.1
  have he_par := hsub.2.2.2
  have hv_ok := hrep.vertexOk
  have hae_ok := hrep.activeEdgeOk
  have hfree_sub := hsub.2.1
  let rawSteps := evalMemSteps mem nb h L t false 0
  have hraw_nd : (rawSteps.map RawStep.nodeId).Nodup := by
    rw [show rawSteps.map RawStep.nodeId =
        seq.filter (fun z => decide (nodeField mem nb z OFF_HASE ≠ 0)) from hraw_map]
    exact hseq_nd.filter _
  have hr_unique : ∀ {r₁ r₂ : RawStep}, r₁ ∈ rawSteps → r₂ ∈ rawSteps →
      r₁.nodeId = r₂.nodeId → r₁ = r₂ := by
    intro r₁ r₂ hr1 hr2 hid
    rcases List.getElem_of_mem hr1 with ⟨i₁, hi1, rfl⟩
    rcases List.getElem_of_mem hr2 with ⟨i₂, hi2, rfl⟩
    have hmap_eq : (rawSteps.map RawStep.nodeId)[i₁]'(by simpa using hi1) =
        (rawSteps.map RawStep.nodeId)[i₂]'(by simpa using hi2) := by
      simp [hid]
    have hi_eq : i₁ = i₂ := (List.Nodup.getElem_inj_iff hraw_nd).1 hmap_eq
    subst hi_eq; rfl
  have hval := hrep.valid
  have hedge_snd := hrep.edgeMap_snd_perm
  have hfst_nd := hrep.edgeMap_fst_nodup
  have heid_nd : (x.edgeMap.map fun p => p.2.eid).Nodup := by
    have hp : (x.edgeMap.map fun p => p.2.eid).Perm (F.edges.map ForestEdge.eid) := by
      simpa [List.map_map, Function.comp_def] using hedge_snd.map ForestEdge.eid
    exact hp.nodup_iff.2 hval.2.1
  have hedge_unique : ∀ p₁ ∈ x.edgeMap, ∀ p₂ ∈ x.edgeMap, p₁.1 = p₂.1 → p₁ = p₂ :=
    (List.nodup_map_iff_inj_on hfst_nd.of_map).1 hfst_nd
  have heid_unique : ∀ p₁ ∈ x.edgeMap, ∀ p₂ ∈ x.edgeMap, p₁.2.eid = p₂.2.eid → p₁ = p₂ :=
    (List.nodup_map_iff_inj_on hfst_nd.of_map).1 heid_nd
  have hnode_lt_cap : ∀ z ∈ seq, 1 ≤ z ∧ z ≤ cap := fun z hz =>
    (hsf_trunc.1.trees_ok t ht).2.2.nodup_perm_mem (hseq_perm.mem_iff.1 hz)
  have hslot_bd : ∀ p ∈ x.edgeMap, F.n + 1 ≤ p.1 ∧ p.1 ≤ cap := fun p hp => by
    have hm := hrep.slots_perm.mem_iff.1
      (List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩))
    rcases List.mem_map.1 hm with ⟨i, hi, hei⟩
    rw [List.mem_range] at hi; dsimp only [cap, lctCap]; omega
  have hall_ed_unique_tree : ∀ {ed} {e : ForestEdge}, (ed, e) ∈ x.edgeMap → ed ∈ seq →
      ∃ s ∈ rawSteps, stepMatchesEdge P ed e s ∧
        ((s.fwd = true ∧ par ed = e.u + 1 ∧ par (e.v + 1) = ed) ∨
         (s.fwd = false ∧ par ed = e.v + 1 ∧ par (e.u + 1) = ed)) := by
    intro ed e hed_in hed_seq
    rcases hae_ok (ed, e) hed_in with ⟨_, _, _, _, _, _, _, t', ht', hed_t', s, hs_mem, hsm, hor⟩
    have ht_eq : t' = t := unique_tree_of_mem hnd_all ht' ht hed_t' (hseq_perm.mem_iff.1 hed_seq)
    subst ht_eq
    exact ⟨s, hs_mem, hsm, hor⟩
  have hlast_elem : ∀ i (hi : i < seq.length), i + 1 = seq.length → seq[i] = v + 1 := by
    intro i _ hi
    rcases List.getLast?_eq_some_iff.1 hlast with ⟨l', hl'⟩
    have hlen_l' : seq.length = l'.length + 1 := by rw [hl']; simp
    have hi_eq : i = l'.length := by omega
    subst hi_eq
    simp [hl']
  have hwalk_aux : ∀ m idx k a (hidx_lt : idx < seq.length),
      idx + 1 + m = seq.length → a < F.n → seq[idx] = a + 1 →
      k = ((seq.take idx).filter (fun z => decide (nodeField mem nb z OFF_HASE ≠ 0))).length →
      ∃ subSteps : List PathStep,
        IsStepWalk F.edges a v subSteps ∧
        (subSteps.map PathStep.toRaw).Nodup ∧
        List.Forall₂ (fun r s => ∃ ed, stepMatchesEdge P ed s.edge r ∧ s.fwd = r.fwd)
          (rawSteps.drop k) subSteps ∧
        (∀ s ∈ subSteps, s.edge.eid ∈ (x.edgeMap.filterMap fun p =>
          if p.1 ∈ seq.drop idx then some p.2.eid else none)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro idx k a hidx_lt hlen ha hseq_idx hk_len
        by_cases hm0 : m = 0
        · have hget_last : seq[idx] = v + 1 := hlast_elem idx hidx_lt (by omega)
          have hav : a = v := by omega
          subst hav
          have htake_eq : seq.take idx ++ [seq[idx]] = seq := by
            have htd := List.take_append_drop idx seq
            have hdrop1 : seq.drop idx = [seq[idx]] := by
              have hl : (seq.drop idx).length = 1 := by simp; omega
              rcases List.length_eq_one_iff.1 hl with ⟨z, hz⟩
              have hz0 : (seq.drop idx)[0] = z := by simp [hz]
              rw [List.getElem_drop] at hz0
              simpa [hz, Nat.add_zero] using hz0 ▸ rfl
            simpa [hdrop1] using htd
          have ha_hase0 : nodeField mem nb (a + 1) OFF_HASE = 0 := (hv_ok a ha).2
          have hraw_len : rawSteps.length = k := by
            have hl := congrArg List.length hraw_map
            simp only [List.length_map] at hl
            rw [hl, ← htake_eq, List.filter_append, List.length_append, hk_len]
            simp [hseq_idx, ha_hase0]
          have hdrop_nil : rawSteps.drop k = [] := List.drop_eq_nil_of_le (le_of_eq hraw_len)
          refine ⟨[], .nil a, List.nodup_nil, ?_, fun _ hs => by simp at hs⟩
          rw [hdrop_nil]; exact .nil
        · have hidx1_lt : idx + 1 < seq.length := by omega
          let ed := seq[idx + 1]
          have hed_mem : ed ∈ seq := List.getElem_mem hidx1_lt
          have hpar_ed : par ed = a + 1 := by
            have := hpar_tree (idx + 1) hidx1_lt
            simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at this
            have hge_idx : seq[idx]! = seq[idx] := by
              simp [getElem!_def, List.getElem?_eq_getElem hidx_lt]
            change lctAuxParent mem nb cap ed = seq[idx]! at this
            rw [hge_idx, hseq_idx] at this
            exact this
          have hed_b := hnode_lt_cap ed hed_mem
          have hed_in_slots : ed ∈ (x.edgeMap.map Prod.fst) ++ x.freeEdges := by
            have hnot_le_n : ¬ ed ≤ F.n := by
              intro hle_n
              rcases hv_par (ed - 1) (by omega) with h0 | ⟨p, hp_in, _, hp_eq⟩
              · rw [show ed - 1 + 1 = ed by omega] at h0
                change par ed = 0 at h0
                rw [h0] at hpar_ed; omega
              · rw [show ed - 1 + 1 = ed by omega] at hp_eq
                change par ed = p.1 at hp_eq
                have hp_ge := (hslot_bd p hp_in).1
                rw [hp_eq] at hpar_ed; omega
            have hed_range : ed ∈ (List.range F.n).map (F.n + 1 + ·) :=
              List.mem_map.2 ⟨ed - (F.n + 1), List.mem_range.2 (by dsimp only [cap, lctCap] at hed_b; omega),
                by omega⟩
            exact hrep.slots_perm.symm.mem_iff.1 hed_range
          have hed_notin_free : ed ∉ x.freeEdges := fun hf => by
            have h0 := hfree_sub ed hf
            change par ed = 0 at h0
            rw [h0] at hpar_ed; omega
          rcases List.mem_append.1 hed_in_slots with hed_map | hed_free
          · rcases List.mem_map.1 hed_map with ⟨p, hp_in, hp1⟩
            have hp_eq : p.1 = ed := hp1
            have hp_bd := hslot_bd p hp_in
            have he_in_F : p.2 ∈ F.edges := hedge_snd.mem_iff.1 (List.mem_map.2 ⟨p, hp_in, rfl⟩)
            have he_lt := hval.1 p.2 he_in_F
            rcases hall_ed_unique_tree hp_in (hp_eq ▸ hed_mem) with ⟨s, hs_raw, hsm, hor⟩
            have ha_hase0 : nodeField mem nb (a + 1) OFF_HASE = 0 := (hv_ok a ha).2
            have hed_hase1 : nodeField mem nb p.1 OFF_HASE = 1 :=
              (hae_ok p hp_in).2.2.2.1
            have hidx2_lt : idx + 2 < seq.length := by
              by_contra hge
              have hlast_eq : ed = v + 1 := hlast_elem (idx + 1) hidx1_lt (by omega)
              have hv_h0 : nodeField mem nb (v + 1) OFF_HASE = 0 := (hv_ok v hv).2
              rw [hp_eq, hlast_eq] at hed_hase1
              rw [hv_h0] at hed_hase1
              omega
            let b' := if s.fwd then p.2.v else p.2.u
            have hb_lt : b' < F.n := by
              dsimp only [b']; split_ifs <;> [exact he_lt.2.1; exact he_lt.1]
            have hseq_idx2 : seq[idx + 2] = b' + 1 := by
              have hpar2 := hpar_tree (idx + 2) hidx2_lt
              change par seq[idx + 2] = seq[idx + 1]! at hpar2
              have hge1 : seq[idx + 1]! = ed := by
                simp [getElem!_def, List.getElem?_eq_getElem hidx1_lt, ed]
              rw [hge1, ← hp_eq] at hpar2
              have hz_mem := List.getElem_mem hidx2_lt
              have hz_b := hnode_lt_cap seq[idx + 2] hz_mem
              have hz_le_n : seq[idx + 2] ≤ F.n := by
                by_contra hgt
                have hzf : seq[idx + 2] ∉ x.freeEdges := fun hf => by
                  have h0 := hfree_sub _ hf
                  change par seq[idx + 2] = 0 at h0
                  rw [hpar2] at h0; omega
                have hmem_rg : seq[idx + 2] - (F.n + 1) ∈ List.range F.n :=
                  List.mem_range.2 (by dsimp only [cap, lctCap] at hz_b; omega)
                have hz_slots : seq[idx + 2] ∈ x.edgeMap.map Prod.fst ++ x.freeEdges :=
                  hrep.slots_perm.symm.mem_iff.1
                    (List.mem_map.2 ⟨seq[idx + 2] - (F.n + 1), hmem_rg, by omega⟩)
                rcases List.mem_append.1 hz_slots with hz_e | hz_fr
                · rcases List.mem_map.1 hz_e with ⟨q, hq_in, hq1⟩
                  have hq_lt := hval.1 q.2 (hedge_snd.mem_iff.1 (List.mem_map.2 ⟨q, hq_in, rfl⟩))
                  have hq_par := he_par q hq_in
                  change (par q.1 = q.2.u + 1 ∧ par (q.2.v + 1) = q.1) ∨
                    (par q.1 = q.2.v + 1 ∧ par (q.2.u + 1) = q.1) at hq_par
                  rw [hq1, hpar2] at hq_par
                  rcases hq_par with ⟨hqp, _⟩ | ⟨hqp, _⟩ <;> omega
                · exact hzf hz_fr
              rcases hv_par (seq[idx + 2] - 1) (by omega) with h0 | ⟨q, hq_in, hq_inc, hqp⟩
              · rw [show seq[idx + 2] - 1 + 1 = seq[idx + 2] by omega] at h0
                change par seq[idx + 2] = 0 at h0
                rw [h0] at hpar2; omega
              · rw [show seq[idx + 2] - 1 + 1 = seq[idx + 2] by omega] at hqp
                change par seq[idx + 2] = q.1 at hqp
                rw [hpar2] at hqp
                have hqp_eq : q = p := hedge_unique q hq_in p hp_in hqp.symm
                subst hqp_eq
                have hne_idx : seq[idx + 2] ≠ seq[idx] := fun heq => by
                  have := (List.Nodup.getElem_inj_iff hseq_nd).1 heq; omega
                have ha_mem : a = q.2.u ∨ a = q.2.v := by
                  rcases hor with ⟨_, hpa, _⟩ | ⟨_, hpa, _⟩
                  · left; change par q.1 = q.2.u + 1 at hpa; rw [hp_eq, hpar_ed] at hpa; omega
                  · right; change par q.1 = q.2.v + 1 at hpa; rw [hp_eq, hpar_ed] at hpa; omega
                rcases hq_inc with hqu | hqv
                · rcases ha_mem with rfl | rfl
                  · rw [hseq_idx] at hne_idx; omega
                  · rcases hor with ⟨hf, hpa, _⟩ | ⟨hf, hpa, _⟩
                    · change par q.1 = q.2.u + 1 at hpa; rw [hp_eq, hpar_ed] at hpa; omega
                    · simp [b', hf]; omega
                · rcases ha_mem with rfl | rfl
                  · rcases hor with ⟨hf, hpa, _⟩ | ⟨hf, hpa, _⟩
                    · simp [b', hf]; omega
                    · change par q.1 = q.2.v + 1 at hpa; rw [hp_eq, hpar_ed] at hpa; omega
                  · rw [hseq_idx] at hne_idx; omega
            have hdrop_idx_eq : seq.drop idx = seq[idx] :: seq[idx + 1] :: seq.drop (idx + 2) := by
              rw [List.drop_eq_getElem_cons hidx_lt, List.drop_eq_getElem_cons hidx1_lt]
            have htake_idx2 : seq.take (idx + 2) = seq.take idx ++ [seq[idx], seq[idx + 1]] := by
              have h1 := List.take_succ_eq_append_getElem hidx_lt
              have h2 := List.take_succ_eq_append_getElem hidx1_lt
              rw [h2, h1, List.append_assoc]; rfl
            have hk1_len : k + 1 = ((seq.take (idx + 2)).filter
                (fun z => decide (nodeField mem nb z OFF_HASE ≠ 0))).length := by
              rw [htake_idx2, List.filter_append, List.length_append, ← hk_len]
              simp [hseq_idx, ha_hase0, show seq[idx + 1] = p.1 from hp_eq.symm, hed_hase1]
            have hraw_split : (rawSteps.drop k).map RawStep.nodeId =
                p.1 :: ((seq.drop (idx + 2)).filter
                  (fun z => decide (nodeField mem nb z OFF_HASE ≠ 0))) := by
              have hfilt_all : (seq.take idx).filter (fun z => decide (nodeField mem nb z OFF_HASE ≠ 0)) ++
                  (seq.drop idx).filter (fun z => decide (nodeField mem nb z OFF_HASE ≠ 0)) =
                  rawSteps.map RawStep.nodeId := by
                rw [hraw_map, ← List.filter_append, List.take_append_drop]
              have hfilt_drop : (rawSteps.map RawStep.nodeId).drop k =
                  (seq.drop idx).filter (fun z => decide (nodeField mem nb z OFF_HASE ≠ 0)) := by
                rw [← hfilt_all, List.drop_left' hk_len.symm]
              rw [← List.map_drop] at hfilt_drop
              rw [hfilt_drop, hdrop_idx_eq, List.filter_cons, List.filter_cons]
              have hs1_eq : seq[idx + 1] = p.1 := hp_eq.symm
              simp [hseq_idx, ha_hase0, hs1_eq, hed_hase1]
            have hdrop_k_ne : rawSteps.drop k ≠ [] := by
              intro hnil; have := congrArg (List.map RawStep.nodeId) hnil; rw [hraw_split] at this; simp at this
            rcases List.ne_nil_iff_exists_cons.1 hdrop_k_ne with ⟨r0, rs_tail, hdrop_cons⟩
            have hr0_id : r0.nodeId = p.1 := by
              have := congrArg (List.map RawStep.nodeId) hdrop_cons
              rw [hraw_split] at this
              simp only [List.map_cons, List.cons.injEq] at this
              exact this.1.symm
            have hr0_in : r0 ∈ rawSteps := by
              rw [← List.take_append_drop k rawSteps, hdrop_cons]
              exact List.mem_append_right _ List.mem_cons_self
            have hr0_eq_s : r0 = s := hr_unique hr0_in hs_raw (hr0_id.trans hsm.1.symm)
            rw [hr0_eq_s] at hdrop_cons
            have hrs_tail_eq : rs_tail = rawSteps.drop (k + 1) := by
              have htl := congrArg List.tail hdrop_cons
              simpa [List.tail_drop] using htl.symm
            rcases ih (m - 2) (by omega) (idx + 2) (k + 1) b' hidx2_lt (by omega) hb_lt
              hseq_idx2 hk1_len with ⟨tailSteps, htw, ht_nd, hfor_tail, h_eids⟩
            have hstep_walk_cons : IsStepWalk F.edges a v (s.toPathStep p.2 :: tailSteps) := by
              have hfwd_cases : (s.fwd = true ∧ p.2.u = a) ∨ (s.fwd = false ∧ p.2.v = a) := by
                rcases hor with ⟨hf, hpa, _⟩ | ⟨hf, hpa, _⟩
                · left; change par p.1 = p.2.u + 1 at hpa; rw [hp_eq, hpar_ed] at hpa
                  exact ⟨hf, by omega⟩
                · right; change par p.1 = p.2.v + 1 at hpa; rw [hp_eq, hpar_ed] at hpa
                  exact ⟨hf, by omega⟩
              rcases hfwd_cases with ⟨hf, hu_eq⟩ | ⟨hf, hv_eq⟩
              · have hs_eq : s.toPathStep p.2 = { edge := p.2, fwd := true } := by
                  simp [RawStep.toPathStep, hf]
                rw [hs_eq]
                refine .fwd he_in_F hu_eq ?_
                have hb_eq : p.2.v = b' := by simp [b', hf]
                rwa [hb_eq]
              · have hs_eq : s.toPathStep p.2 = { edge := p.2, fwd := false } := by
                  simp [RawStep.toPathStep, hf]
                rw [hs_eq]
                refine .bwd he_in_F hv_eq ?_
                have hb_eq : p.2.u = b' := by simp [b', hf]
                rwa [hb_eq]
            have hnot_in_tail : (s.toPathStep p.2).toRaw ∉ tailSteps.map PathStep.toRaw := by
              intro hmem
              rcases List.mem_map.1 hmem with ⟨ts, hts_in, hts_raw⟩
              have heid_ts := h_eids ts hts_in
              rcases List.mem_filterMap.1 heid_ts with ⟨q, hq_in, hq_res⟩
              split_ifs at hq_res with hq_drop
              injection hq_res with hqid
              have hq_eid_eq : q.2.eid = p.2.eid := by
                rw [hqid]; exact congrArg RawEdge.eid hts_raw
              have hqp_eq : q = p := heid_unique q hq_in p hp_in hq_eid_eq
              subst hqp_eq
              rcases List.getElem_of_mem hq_drop with ⟨j, hj, hseq_j⟩
              rw [List.getElem_drop] at hseq_j
              have hj_eq : idx + 2 + j = idx + 1 :=
                (List.Nodup.getElem_inj_iff hseq_nd).1 (hseq_j.trans hp_eq)
              omega
            refine ⟨s.toPathStep p.2 :: tailSteps, hstep_walk_cons,
              List.nodup_cons.2 ⟨hnot_in_tail, ht_nd⟩, ?_, ?_⟩
            · rw [hdrop_cons, hrs_tail_eq]
              exact List.Forall₂.cons ⟨p.1, hsm, rfl⟩ hfor_tail
            · intro ts hts
              rcases List.mem_cons.1 hts with rfl | hts_t
              · refine List.mem_filterMap.2 ⟨p, hp_in, ?_⟩
                have hp1_drop : p.1 ∈ seq.drop idx := by
                  rw [hdrop_idx_eq, hp_eq]
                  exact List.mem_cons_of_mem _ List.mem_cons_self
                simp [hp1_drop, RawStep.toPathStep]
              · have heid_t := h_eids ts hts_t
                rcases List.mem_filterMap.1 heid_t with ⟨q, hq_in, hq_res⟩
                split_ifs at hq_res with hq_drop
                injection hq_res with hqid
                refine List.mem_filterMap.2 ⟨q, hq_in, ?_⟩
                have hq_idx : q.1 ∈ seq.drop idx := by
                  rw [hdrop_idx_eq]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq_drop)
                simp [hq_idx, hqid]
          · exact absurd hed_free hed_notin_free
  have hseq_ne : seq ≠ [] := by
    intro hnil; simp [hnil] at hhead
  have hlen_pos : 0 < seq.length := List.length_pos_of_ne_nil hseq_ne
  have hseq0 : seq[0] = u + 1 := by
    rcases List.head?_eq_some_iff.1 hhead with ⟨tl, hcons⟩
    simp [hcons]
  rcases hwalk_aux (seq.length - 1) 0 0 u hlen_pos (by omega) hu hseq0 (by simp) with
    ⟨steps, hw, hnd_s, hfor, _⟩
  refine ⟨steps, MathForest.findSteps_eq_of_isStepWalk hval hw hnd_s, hw, hnd_s, ?_⟩
  simpa using hfor

/-- In an exposed path tree `[u + 1, ..., v + 1]` (`PPAR = 0`), `OFF_CSUM_FWD` equals
`wrap h L (F.pathSum u v)`. -/
theorem LctMemRep.pathSum_eq_wrap {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {t : AuxTree} (ht : t ∈ x.trees)
    {u v : ℕ} (hu : u < F.n) (hv : v < F.n)
    (hpp0 : nodeField mem (lctNodesBase b) t.rootId OFF_PPAR = 0)
    (hhead : (t.evalInorder (revFlag mem (lctNodesBase b)) false).head? = some (u + 1))
    (hlast : (t.evalInorder (revFlag mem (lctNodesBase b)) false).getLast? = some (v + 1)) :
    optIntVal mem h L (nodeField mem (lctNodesBase b) t.rootId OFF_CSUM_FWD) =
      wrap h L (F.pathSum u v) := by
  rcases hrep.pathTree_isStepWalk ht hu hv hpp0 hhead hlast with ⟨steps, hfs, _, _, hfor⟩
  rcases hrep.treeMemMatch ht with ⟨hne, htm⟩
  cases h_t : t with
  | leaf => exact absurd h_t hne
  | node id l r =>
      subst h_t
      have hcs := htm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
      change optIntVal mem h L (nodeField mem (lctNodesBase b) id OFF_CSUM_FWD) =
        wrap h L (listRawCost (evalMemSteps mem (lctNodesBase b) h L (.node id l r) false 0)) at hcs
      simpa [AuxTree.rootId, wrap_listRawCost_of_stepMatches hfor, MathForest.pathSum, hfs] using hcs

/-- In an exposed path tree `[u + 1, ..., v + 1]` (`PPAR = 0`) with `u ≠ v`, `OFF_MIN1_HAS = 1`
and `OFF_MIN1_FIRST` is an active edge node in `t.toList` realizing `F.pathMin u v`. -/
theorem LctMemRep.pathMin_eq {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {t : AuxTree} (ht : t ∈ x.trees)
    {u v : ℕ} (hu : u < F.n) (hv : v < F.n) (hne_uv : u ≠ v)
    (hpp0 : nodeField mem (lctNodesBase b) t.rootId OFF_PPAR = 0)
    (hhead : (t.evalInorder (revFlag mem (lctNodesBase b)) false).head? = some (u + 1))
    (hlast : (t.evalInorder (revFlag mem (lctNodesBase b)) false).getLast? = some (v + 1)) :
    ∃ (hit : PathHit) (rmin : RawStep) (smin : PathStep),
      F.pathMin u v = some hit ∧
      nodeField mem (lctNodesBase b) t.rootId OFF_MIN1_HAS = 1 ∧
      nodeField mem (lctNodesBase b) t.rootId OFF_MIN1_FIRST = rmin.nodeId ∧
      rmin.nodeId ∈ t.toList ∧
      rmin ∈ evalMemSteps mem (lctNodesBase b) h L t false 0 ∧
      (∃ ed, stepMatchesEdge P ed smin.edge rmin ∧ smin.fwd = rmin.fwd) ∧
      smin.toHit = hit := by
  rcases hrep.pathTree_isStepWalk ht hu hv hpp0 hhead hlast with ⟨steps, hfs, hw, _, hfor⟩
  have hsteps_ne : steps ≠ [] := by
    intro hnil; subst hnil; exact hne_uv (IsStepWalk.nil_iff.1 hw)
  have hraw_ne : evalMemSteps mem (lctNodesBase b) h L t false 0 ≠ [] := by
    intro hnil; rw [hnil] at hfor; cases hfor; exact hsteps_ne rfl
  rcases listIntMinAgg_matches_stepsMinHit hfor hsteps_ne with
    ⟨hit, rmin, smin, hmin_hit, _, hfirst, _, hrmin_in, _, hmatch, hhit_eq⟩
  rcases hrep.treeMemMatch ht with ⟨hne_t, htm⟩
  cases h_t : t with
  | leaf => exact absurd h_t hne_t
  | node id l r =>
      subst h_t
      have hagg := htm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hm1_has : nodeField mem (lctNodesBase b) id OFF_MIN1_HAS = 1 :=
        hagg.2.2.2.1.2 hraw_ne
      have hm1_eq : nodeIntMinAgg1 mem (lctNodesBase b) h L id =
          listIntMinAgg ((evalMemSteps mem (lctNodesBase b) h L (.node id l r) false 0).map
            fun s => (s.nodeId, s.dirAvail)) := hagg.2.2.2.2.1
      have hfirst_eq : nodeField mem (lctNodesBase b) id OFF_MIN1_FIRST = rmin.nodeId := by
        have := congrArg IntMinAgg.first hm1_eq
        simpa [nodeIntMinAgg1] using this.trans hfirst
      have hrmin_node : rmin.nodeId ∈ (AuxTree.node id l r).toList := by
        have hm_id : rmin.nodeId ∈ (evalMemSteps mem (lctNodesBase b) h L
            (.node id l r) false 0).map RawStep.nodeId := List.mem_map.2 ⟨rmin, hrmin_in, rfl⟩
        rw [evalMemSteps_map_nodeId] at hm_id
        exact ((AuxTree.evalInorder_perm _ _ _).mem_iff.1 (List.mem_filter.1 hm_id).1)
      exact ⟨hit, rmin, smin, by simp [MathForest.pathMin, hfs, hmin_hit],
        hm1_has, hfirst_eq, hrmin_node, hrmin_in, hmatch, hhit_eq⟩

end MinCostFlow.LinkCut.Prog
