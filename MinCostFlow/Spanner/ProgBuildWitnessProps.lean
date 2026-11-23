module

public import MinCostFlow.Spanner.ProgBuildWitnessMath

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# WitnessOK, Edge/Source Spec, Size Bounds, and Walk Lifting for `mkWitnessData`

Establishes `WitnessOK` and all Task 1 edge, weight, counting, cost, and walk-lifting properties
for `wd := inp.mkWitnessData ce pds WSubs` constructed from concrete Word-RAM outputs.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

namespace WitnessCoreInput

private lemma rawComps_pairwise_disj {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.prep.StaticValid mem w) :
    inp.prep.rawComps.Pairwise (fun a b => a.1 ≠ b.1 ∨ Disjoint a.2.toFinset b.2.toFinset) := by
  have hpw := hv.2.2.2.2.2.2.2.2.2.2.1
  have hprops := hv.2.2.2.2.2.2.2.2.2.2.2.1
  have hdp := hv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdisj_raw : ∀ i, 0 < i → i ≤ inp.prep.d_ℓ → (inp.prep.decomp.comps i).Pairwise Disjoint :=
    fun i hi0 hiℓ => (hdp.2.2.2 i hi0 hiℓ).1
  have hdisj := rawComps_pairwise (d := inp.prep.decomp) hdisj_raw
  have hraw_eq : inp.prep.rawComps.map (fun c => (c.1, c.2.toFinset)) =
      (List.range inp.prep.d_ℓ).flatMap fun i' =>
        (inp.prep.decomp.comps (i' + 1)).map fun X => (i' + 1, X) :=
    (mkDecomposeOutput_rawComps_eq inp.prep.d_ℓ inp.prep.level inp.prep.rawComps hpw
      fun c hc => ⟨(hprops c hc).1, (hprops c hc).2.1⟩).symm
  change List.Pairwise (fun a b => a.1 ≠ b.1 ∨ Disjoint a.2 b.2)
    ((List.range inp.prep.d_ℓ).flatMap fun i' =>
      (inp.prep.decomp.comps (i' + 1)).map fun X => (i' + 1, X)) at hdisj
  rw [← hraw_eq, List.pairwise_map] at hdisj
  exact hdisj

theorem mkWitnessData_comp_props {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hvalid : inp.Valid ce pds mem w) (hws : inp.ValidWSubs ce WSubs) :
    let wd := inp.mkWitnessData ce pds WSubs
    ∀ ci (hci : ci < wd.comps.length),
      let c := wd.comps[ci]'hci
      0 < c.level ∧ c.level ≤ wd.decomp.ℓ ∧
      c.X ⊆ inp.prep.J.verts ∧ 2 ≤ c.X.card ∧ c.verts = vertsOf c.X ∧
      c.J_sub.n = c.X.card ∧ c.J_sub.IsValid ∧ 1 ≤ c.J_sub.m ∧ c.J_sub.m ≤ wd.J0_strip.m ∧
      (∀ k < c.X.card, 1 ≤ c.J_sub.deg k) ∧
      c.J_sub.IsConductanceExpanderOn c.J_sub.verts wd.φ_dec ∧
      c.W_sub.n = c.X.card ∧ c.W_sub.IsValid ∧ 1 ≤ c.W_sub.m ∧ c.W_sub.m ≤ wd.M_W ∧
      (∀ k < c.X.card, 1 ≤ c.W_sub.deg k) ∧
      c.W_sub.IsConductanceExpanderOn c.W_sub.verts wd.φ_Const ∧
      (∀ k < c.X.card, (c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)) ≤ c.W_sub.deg k ∧
        (c.W_sub.deg k : ℝ) ≤ wd.c_deg * ((c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)))) ∧
      (∀ k < c.X.card, wd.φ_dec * (2 ^ c.level : ℝ) ≤ (c.J_sub.deg k : ℝ)) ∧
      c.jSubOrigEdges.length = c.J_sub.m ∧ c.jSubOrigEdges.Nodup ∧
      (∀ j ∈ c.jSubOrigEdges, j < inp.prep.J.m) ∧
      wd.j0Edges.length ≤ c.wStart ∧ c.wStart + c.W_sub.m ≤ wd.W.m := by
  have hv := hvalid.2.2.1
  have hJ := hv.1
  have hSL_m_le : inp.prep.J0_strip.m ≤ inp.prep.J.m := by
    rw [hv.2.2.1]; exact stripLoops_m_le inp.prep.J
  have hnl_len : inp.prep.nlIdx.length = inp.prep.J0_strip.m := by
    rw [hv.2.2.2.2.1, hv.2.2.1]; simp [stripLoops, Graph.m]
  have hnl_nodup : inp.prep.nlIdx.Nodup := by
    rw [hv.2.2.2.2.1]; exact nonloopIndices_nodup inp.prep.J
  have hnl_lt : ∀ k (hk : k < inp.prep.nlIdx.length), inp.prep.nlIdx[k]'hk < inp.prep.J.m := by
    intro k hk
    have hmem : inp.prep.nlIdx[k]'hk ∈ nonloopIndices inp.prep.J := by
      rw [← hv.2.2.2.2.1]; exact List.getElem_mem hk
    exact (mem_nonloopIndices.mp hmem).1
  have hsz := PrepInput.StaticValid.size_bounds hv
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hφ_pos : 0 < (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) :=
    div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
  have hwm_ub := mkWitnessData_W_m_upper (pds := pds) hv hws
  have haligned : CompsAligned inp.prep.j0Edges.length
      (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs) :=
    buildCompsFrom_aligned inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hclen : (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs).length =
      inp.prep.rawComps.length :=
    buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  dsimp only
  intro ci hci
  set c := (inp.mkWitnessData ce pds WSubs).comps[ci]'hci
  have hcir : ci < inp.prep.rawComps.length := by rw [← hclen]; exact hci
  obtain ⟨hlvl, hX, hverts, hJsub, hjOrig, hWsub⟩ :=
    buildCompsFrom_getElem_full inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hcir
  change c.level = _ at hlvl
  change c.X = _ at hX
  change c.verts = _ at hverts
  change c.J_sub = _ at hJsub
  change c.jSubOrigEdges = _ at hjOrig
  change c.W_sub = _ at hWsub
  have hc_props := comp_props_at hv.toValid_zeroTail hcir
  have hc_eq : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by simp [hcir]
  rw [hc_eq] at hc_props
  set rc := inp.prep.rawComps[ci]
  have hX_card : c.X.card = rc.2.length := by
    rw [hX, List.toFinset_card_of_nodup hc_props.2.2.2.2.1]
  have hc_mem : rc ∈ inp.prep.rawComps := List.getElem_mem hcir
  have hrc_p := hv.2.2.2.2.2.2.2.2.2.2.2.1 rc hc_mem
  have hX_mem : rc.2.toFinset ∈ inp.prep.decomp.comps rc.1 := by
    simp only [PrepInput.decomp, mkDecomposeOutput, List.mem_map, List.mem_filter]
    exact ⟨rc, ⟨hc_mem, decide_eq_true rfl⟩, rfl⟩
  have hdi := (hv.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2 rc.1 hrc_p.1 hrc_p.2.1).2.1 rc.2.toFinset hX_mem
  have hXJ : c.X ⊆ inp.prep.J.verts := by
    rw [hX]
    simpa [hv.2.2.1, stripLoops, Graph.verts] using hdi.1
  have hJsub_m_pos : 1 ≤ c.J_sub.m := by
    rw [hJsub]
    have hdeg_pos : ∀ k < rc.2.length, 1 ≤ (inp.prep.cJSub rc).deg k := fun k hk => by
      have hge := rawComps_deg_ge_phi hv hcir k hk
      have h2 : 0 < (2 : ℝ) ^ rc.1 := by positivity
      have hr : (0 : ℝ) < ((inp.prep.cJSub rc).deg k : ℝ) := lt_of_lt_of_le (mul_pos hφ_pos h2) hge
      exact Nat.cast_pos.mp hr
    have hvol := vol_verts_eq_two_mul_m hc_props.2.2.2.2.2.2.2
    have hcard_pos : c.X.card ≤ (inp.prep.cJSub rc).vol (inp.prep.cJSub rc).verts := by
      unfold Graph.vol Graph.volIn
      rw [Graph.verts, hc_props.2.2.2.2.2.2.1, hX_card]
      calc rc.2.length = ∑ _k ∈ Finset.range rc.2.length, 1 := by simp
        _ ≤ ∑ k ∈ Finset.range rc.2.length,
              (inp.prep.cJSub rc).degIn (Finset.range rc.2.length) k :=
            Finset.sum_le_sum fun k hk => by
              have := hdeg_pos k (Finset.mem_range.mp hk)
              simpa [Graph.deg, Graph.verts, hc_props.2.2.2.2.2.2.1] using this
    change (inp.prep.cJSub rc).m ≥ 1
    omega
  have hJsub_m_le : c.J_sub.m ≤ inp.prep.J0_strip.m := by
    have h1 : (inp.prep.cJSub rc).m ≤ (inp.prep.rawComps.map fun p => (inp.prep.cJSub p).m).sum :=
      List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨rc, hc_mem, rfl⟩)
    rw [hJsub]
    change (inp.prep.cJSub rc).m ≤ _
    omega
  have hdeg_ge_phi : ∀ k < c.X.card,
      ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level ≤
        (c.J_sub.deg k : ℝ) := by
    intro k hk
    have hk' : k < inp.prep.rawComps[ci].2.length := by rw [← hX_card]; exact hk
    rw [hlvl, hJsub]
    exact rawComps_deg_ge_phi hv hcir k hk'
  have hJdeg_pos : ∀ k < c.X.card, 1 ≤ c.J_sub.deg k := fun k hk => by
    have h2 : 0 < (2 : ℝ) ^ c.level := by positivity
    have hr : (0 : ℝ) < (c.J_sub.deg k : ℝ) := lt_of_lt_of_le (mul_pos hφ_pos h2) (hdeg_ge_phi k hk)
    exact Nat.cast_pos.mp hr
  have hJexp : c.J_sub.IsConductanceExpanderOn c.J_sub.verts
      ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) := by
    rw [hJsub]; exact inducedSubgraph_isConductanceExpander hdi.2.2.1
  have hws_ci := hws.2 ci hcir
  have hW_eq : c.W_sub = WSubs.getD ci ⟨0, []⟩ := by
    rw [hWsub, List.getD_eq_getElem _ _ (by rw [hws.1]; exact hcir)]
  rcases hws_ci with ⟨hWn, hWval, hWexp, hWdeg⟩
  have hcb := comp_weight_bounds hv hcir
  have hWdeg_cmp : ∀ k < c.X.card,
      (c.J_sub.deg k : ℝ) / (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level) ≤
        c.W_sub.deg k ∧
      (c.W_sub.deg k : ℝ) ≤ (2 * (ce.c_deg_int : ℝ)) *
        ((c.J_sub.deg k : ℝ) / (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level)) := by
    intro k hk
    have hk' : k < rc.2.length := by rw [← hX_card]; exact hk
    obtain ⟨_, hceil, _⟩ := hcb.2.2.2.1 k hk'
    have hdk := hWdeg k hk'
    have hge_real : 1 ≤ ((c.J_sub.deg k : ℝ) /
        (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level)) := by
      have hpos : 0 < ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level := by positivity
      rw [one_le_div hpos]
      exact hdeg_ge_phi k hk
    have hceil' : ((inp.compWeights rc)[k]'(by simp [compWeights]; exact hk') : ℝ) =
        Nat.ceil ((c.J_sub.deg k : ℝ) /
          (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level)) := by
      rw [hJsub, hlvl]; exact hceil
    have hlo : (c.J_sub.deg k : ℝ) /
        (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level) ≤
        ((inp.compWeights rc)[k]'(by simp [compWeights]; exact hk') : ℝ) := by
      rw [hceil']; exact Nat.le_ceil _
    have hhi : ((inp.compWeights rc)[k]'(by simp [compWeights]; exact hk') : ℝ) ≤
        2 * ((c.J_sub.deg k : ℝ) /
          (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.level)) := by
      rw [hceil']; exact real_ceil_le_two_mul hge_real
    rw [hW_eq]
    have hc_nn : (0 : ℝ) ≤ ce.c_deg_int := Nat.cast_nonneg _
    refine ⟨le_trans hlo hdk.1, le_trans hdk.2 ?_⟩
    nlinarith
  have hWdeg_pos : ∀ k < c.X.card, 1 ≤ c.W_sub.deg k := by
    intro k hk
    have hk' : k < rc.2.length := by rw [← hX_card]; exact hk
    obtain ⟨hw1, _, _⟩ := hcb.2.2.2.1 k hk'
    have hdk := (hWdeg k hk').1
    have hw_r : (1 : ℝ) ≤ ((inp.compWeights rc)[k]'(by simp [compWeights]; exact hk') : ℝ) := by
      exact_mod_cast hw1
    have hr : (1 : ℝ) ≤ (c.W_sub.deg k : ℝ) := by rw [hW_eq]; exact le_trans hw_r hdk
    exact Nat.one_le_cast.mp hr
  have hWm_pos : 1 ≤ c.W_sub.m := by
    have hWvol := vol_verts_eq_two_mul_m hWval
    have hvol : c.X.card ≤ (WSubs.getD ci ⟨0, []⟩).vol (WSubs.getD ci ⟨0, []⟩).verts := by
      unfold Graph.vol Graph.volIn
      rw [Graph.verts, hWn, hX_card]
      calc rc.2.length = ∑ _k ∈ Finset.range rc.2.length, 1 := by simp
        _ ≤ ∑ k ∈ Finset.range rc.2.length,
              (WSubs.getD ci ⟨0, []⟩).degIn (Finset.range rc.2.length) k :=
            Finset.sum_le_sum fun k hk => by
              have h1 := hWdeg_pos k (by rw [hX_card]; exact Finset.mem_range.mp hk)
              rw [hW_eq] at h1
              rw [← hWn]; simpa [Graph.deg, Graph.verts] using h1
    rw [hW_eq]; omega
  have heds_orig := comp_edges_orig_spec hv.toValid_zeroTail hcir
  have hjOrig_nodup : c.jSubOrigEdges.Nodup := by
    have heq : c.jSubOrigEdges = (inp.prep.cJOrig rc) := hjOrig
    have hsub_in : (insideIndices (inp.prep.decomp.graphAt inp.prep.J0_strip rc.1) rc.2.toFinset).Nodup :=
      insideIndices_nodup _ _
    have hed_nd : (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1).Nodup :=
      List.Nodup.filter _ List.nodup_range
    have hed_lt : ∀ b ∈ inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1, b < inp.prep.nlIdx.length := by
      intro b hb
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb
      omega
    have hidx_lt : ∀ a ∈ insideIndices (inp.prep.decomp.graphAt inp.prep.J0_strip rc.1) rc.2.toFinset,
        a < (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1).length := by
      intro a ha
      have ha' := (mem_insideIndices.mp ha).1
      simpa [DecomposeOutput.graphAt, Graph.m] using ha'
    have hcomp : c.jSubOrigEdges =
        ((insideIndices (inp.prep.decomp.graphAt inp.prep.J0_strip rc.1) rc.2.toFinset).map fun a =>
          (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1).getD a 0).map (fun b => inp.prep.nlIdx.getD b 0) := by
      rw [heq, PrepInput.cJOrig, List.map_map]; rfl
    rw [hcomp]
    refine map_getD_nodup hnl_nodup (map_getD_nodup hed_nd hsub_in hidx_lt) fun j hj => ?_
    simp only [List.mem_map] at hj
    rcases hj with ⟨a, ha, rfl⟩
    have ha' := hidx_lt a ha
    rw [List.getD_eq_getElem _ _ ha']
    exact hed_lt _ (List.getElem_mem ha')
  have hjOrig_lt : ∀ j ∈ c.jSubOrigEdges, j < inp.prep.J.m := by
    intro j hj
    rw [hjOrig] at hj
    simp only [PrepInput.cJOrig, List.mem_map] at hj
    rcases hj with ⟨a, ha, rfl⟩
    have ha_lt : a < (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1).length := by
      simpa [DecomposeOutput.graphAt, Graph.m] using (mem_insideIndices.mp ha).1
    rw [List.getD_eq_getElem _ _ ha_lt]
    have hb_mem := List.getElem_mem ha_lt
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb_mem
    have hb_nl : (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1)[a]'ha_lt < inp.prep.nlIdx.length := by
      simpa only [DecomposeOutput.edgesAt, hnl_len] using hb_mem.1
    rw [List.getD_eq_getElem _ _ hb_nl]
    exact hnl_lt _ hb_nl
  have hwStart_ge := compsAligned_wStart_ge haligned c (List.getElem_mem hci)
  have hWm_eq : (inp.mkWitnessData ce pds WSubs).W.m =
      inp.prep.j0Edges.length + (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs |>.map fun x => x.W_sub.m).sum := by
    change (inp.prep.j0Edges.map _ ++ _).length = _
    rw [List.length_append, List.length_map, compsAligned_sum_m]
  have hwEnd_le : c.wStart + c.W_sub.m ≤ (inp.mkWitnessData ce pds WSubs).W.m := by
    rw [hWm_eq]; exact compsAligned_wEnd_le haligned ci hci
  exact ⟨by omega, by rw [hlvl]; exact hc_props.2.1, hXJ, by omega, by rw [hX]; exact hverts,
    by rw [hJsub, hX_card]; simp [PrepInput.cJSub, inducedSubgraph]; rw [← hX, hX_card],
    by rw [hJsub]; exact hc_props.2.2.2.2.2.2.2,
    hJsub_m_pos, hJsub_m_le, hJdeg_pos, hJexp, by rw [hW_eq, hWn, hX_card],
    by rw [hW_eq]; exact hWval, hWm_pos, hwm_ub.2 ci hci, hWdeg_pos,
    by rw [hW_eq]; exact hWexp, hWdeg_cmp, hdeg_ge_phi,
    by rw [hJsub, hjOrig, ← hc_eq]; exact heds_orig.2.2.2,
    hjOrig_nodup, hjOrig_lt, hwStart_ge, hwEnd_le⟩

theorem mkWitnessData_ok {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max)
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hvalid : inp.Valid ce pds mem w) (hws : inp.ValidWSubs ce WSubs) :
    WitnessOK tools inp.H' inp.prep.J inp.embJH (inp.mkWitnessData ce pds WSubs) := by
  have hv := hvalid.2.2.1
  have hJ := hv.1
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hnl_len : inp.prep.nlIdx.length = inp.prep.J0_strip.m := by
    rw [hv.2.2.2.2.1, hv.2.2.1]; simp [stripLoops, Graph.m]
  have hnl_nodup : inp.prep.nlIdx.Nodup := by
    rw [hv.2.2.2.2.1]; exact nonloopIndices_nodup inp.prep.J
  have hnl_lt : ∀ k (hk : k < inp.prep.nlIdx.length), inp.prep.nlIdx[k]'hk < inp.prep.J.m := fun k hk => by
    have hmem : inp.prep.nlIdx[k]'hk ∈ nonloopIndices inp.prep.J := by
      rw [← hv.2.2.2.2.1]; exact List.getElem_mem hk
    exact (mem_nonloopIndices.mp hmem).1
  have hφ_dec_pos : 0 < (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) :=
    div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
  have hφ_dec_le : (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast lt_of_lt_of_le hpn hpnd)]
    exact_mod_cast hpnd
  have hcprops := mkWitnessData_comp_props hvalid hws
  set wd := inp.mkWitnessData ce pds WSubs
  have hnl_len_wd : wd.nlIdx.length = wd.J0_strip.m := hnl_len
  have hW_valid : wd.W.IsValid := by
    intro e he
    change e ∈ wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges at he
    rcases List.mem_append.mp he with he0 | hec
    · rcases List.mem_map.mp he0 with ⟨jOrig, hjOrig, rfl⟩
      have hj : jOrig < inp.prep.J.m := by
        simp only [wd, mkWitnessData, PrepInput.j0Edges, DecomposeOutput.edgesAt, List.mem_map,
          List.mem_filter, List.mem_range] at hjOrig
        rcases hjOrig with ⟨a, ⟨ha, _⟩, rfl⟩
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hnl_lt a (by omega)
      rw [List.getD_eq_getElem _ _ hj]
      exact hJ _ (List.getElem_mem hj)
    · rcases List.mem_flatMap.mp hec with ⟨c, hc, heW⟩
      rcases List.mem_iff_getElem.mp hc with ⟨ci, hci, rfl⟩
      rcases hcprops ci hci with
        ⟨_, _, hXJ_c, _, hverts_c, _, _, _, _, _, _, hWn_c, hWvalid_c, _⟩
      rcases List.mem_map.mp heW with ⟨eL, heL, rfl⟩
      have heL_lt := hWvalid_c eL heL
      rw [hWn_c] at heL_lt
      have h1 : (wd.comps[ci]'hci).verts.getD eL.1 0 ∈ inp.prep.J.verts := by
        rw [hverts_c]; exact hXJ_c (getD_vertsOf_mem heL_lt.1)
      have h2 : (wd.comps[ci]'hci).verts.getD eL.2 0 ∈ inp.prep.J.verts := by
        rw [hverts_c]; exact hXJ_c (getD_vertsOf_mem heL_lt.2)
      exact ⟨Finset.mem_range.mp h1, Finset.mem_range.mp h2⟩
  have hclen : wd.comps.length = inp.prep.rawComps.length :=
    buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hWm_eq : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
    change (wd.j0Edges.map _ ++ wd.comps.flatMap compWEdges).length = _
    rw [List.length_append, List.length_map, compsAligned_sum_m]
  have haligned := buildCompsFrom_aligned inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hj0_nodup : wd.j0Edges.Nodup := by
    refine map_getD_nodup hnl_nodup (List.Nodup.filter _ List.nodup_range) fun a ha => ?_
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at ha
    omega
  have hj0_lt : ∀ j ∈ wd.j0Edges, j < inp.prep.J.m := by
    intro j hj
    simp only [wd, mkWitnessData, PrepInput.j0Edges, DecomposeOutput.edgesAt, List.mem_map,
      List.mem_filter, List.mem_range] at hj
    rcases hj with ⟨a, ⟨ha, _⟩, rfl⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hnl_lt a (by omega)
  have hsc := mkWitnessData_scalars inp ce pds WSubs hv
  have hsc_m : wd.M_W = inp.mwInt ce := hsc.1
  have hφJ_pos := pds.hφ_out_pos (roundPhi wd.φ_dec) wd.J0_strip.m (roundPhi_pos hφ_dec_pos)
  have hφW_pos := pds.hφ_out_pos (roundPhi ce.φ_Const) wd.M_W (roundPhi_pos ce.hφ_Const_pos)
  have hφds_pos : 0 < wd.φ_ds := lt_min hφJ_pos hφW_pos
  have hφds_le_dec : wd.φ_ds ≤ wd.φ_dec :=
    le_trans (min_le_left _ _) (le_trans (pds.hφ_out_le _ _ (roundPhi_pos hφ_dec_pos)) (roundPhi_le hφ_dec_pos))
  have hφds_le_ce : wd.φ_ds ≤ wd.φ_Const :=
    le_trans (min_le_right _ _) (le_trans (pds.hφ_out_le _ _ (roundPhi_pos ce.hφ_Const_pos)) (roundPhi_le ce.hφ_Const_pos))
  have hφds_half : wd.φ_ds ≤ 1 / 2 :=
    le_trans (min_le_left _ _) (pds.hφ_out_half _ _ (roundPhi_pos hφ_dec_pos))
  have hγE_ge : 1 / wd.φ_ds ≤ wd.γ_ExpPath := by
    have h1 := pds.hγ_ExpPath_ge (roundPhi wd.φ_dec) wd.J0_strip.m (roundPhi_pos hφ_dec_pos)
    have h2 := pds.hγ_ExpPath_ge (roundPhi ce.φ_Const) wd.M_W (roundPhi_pos ce.hφ_Const_pos)
    change 1 / min (pds.φ_out (roundPhi wd.φ_dec) wd.J0_strip.m) (pds.φ_out (roundPhi ce.φ_Const) wd.M_W) ≤
      max (pds.γ_ExpPath (roundPhi wd.φ_dec) wd.J0_strip.m) (pds.γ_ExpPath (roundPhi ce.φ_Const) wd.M_W)
    rcases min_cases (pds.φ_out (roundPhi wd.φ_dec) wd.J0_strip.m) (pds.φ_out (roundPhi ce.φ_Const) wd.M_W) with
      ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]; exact le_trans h1 (le_max_left _ _)
    · rw [hm]; exact le_trans h2 (le_max_right _ _)
  have hγD_ge : 1 ≤ wd.γ_del :=
    le_trans (pds.hγ_del_ge (roundPhi wd.φ_dec) wd.J0_strip.m (roundPhi_pos hφ_dec_pos)) (le_max_left _ _)
  have hcdeg_ge : 1 ≤ wd.c_deg := by
    have : (1 : ℝ) ≤ (ce.c_deg_int : ℝ) := by exact_mod_cast ce.hc_deg_int
    change 1 ≤ 2 * (ce.c_deg_int : ℝ); linarith
  have hτ₁_nn : 0 ≤ wd.τ₁ := by
    have := hsc.2.2.2.2.2
    rw [this]; exact Nat.cast_nonneg _
  have hτ₂_pos : 0 < wd.τ₂ := by
    have hγE : 0 < wd.γ_ExpPath := lt_of_lt_of_le (div_pos one_pos hφds_pos) hγE_ge
    change 0 < wd.γ_ExpPath * wd.γ_del / wd.φ_ds
    positivity
  have hjSub_mem_preimage : ∀ ci (hci : ci < wd.comps.length) (jOrig : ℕ),
      jOrig ∈ (wd.comps[ci]'hci).jSubOrigEdges →
      ∃ (b : ℕ) (hb : b < wd.J0_strip.m),
        (wd.nlIdx[b]'(by omega)) = jOrig ∧
        wd.decomp.level b = (wd.comps[ci]'hci).level ∧
        (wd.J0_strip.edges[b]'(by simpa [Graph.m] using hb)).1 ∈ (wd.comps[ci]'hci).X ∧
        (wd.J0_strip.edges[b]'(by simpa [Graph.m] using hb)).2 ∈ (wd.comps[ci]'hci).X := by
    intro ci hci jOrig hj
    have hcir : ci < inp.prep.rawComps.length := by omega
    obtain ⟨hlvl, hX, _, _, hjOrig, _⟩ :=
      buildCompsFrom_getElem_full inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hcir
    set c := wd.comps[ci]'hci
    rw [show c.jSubOrigEdges = inp.prep.cJOrig inp.prep.rawComps[ci] from hjOrig,
      PrepInput.cJOrig, List.mem_map] at hj
    rcases hj with ⟨a, ha, rfl⟩
    set rc := inp.prep.rawComps[ci]
    set J_i := inp.prep.decomp.graphAt inp.prep.J0_strip rc.1
    have ha' := mem_insideIndices.mp ha
    have ha_len : a < (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1).length := by
      simpa [J_i, DecomposeOutput.graphAt, Graph.m] using ha'.1
    set b := (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1).getD a 0
    have hb_mem : b ∈ inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1 := by
      dsimp only [b]; rw [List.getD_eq_getElem _ _ ha_len]; exact List.getElem_mem ha_len
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb_mem
    have hb_m : b < wd.J0_strip.m := hb_mem.1
    have hb_inp : b < inp.prep.J0_strip.edges.length := hb_m
    have hJi_eq : J_i.edges.getD a (0, 0) = wd.J0_strip.edges[b]'(by simpa [Graph.m] using hb_m) := by
      have hba : (inp.prep.decomp.edgesAt inp.prep.J0_strip rc.1)[a]'ha_len = b :=
        (List.getD_eq_getElem _ _ ha_len).symm
      simp only [J_i, DecomposeOutput.graphAt]
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using ha_len), List.getElem_map,
        hba, List.getD_eq_getElem _ _ hb_inp]
      rfl
    refine ⟨b, hb_m, ?_, ?_, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by omega)]; rfl
    · change inp.prep.decomp.level b = c.level
      rw [show c.level = rc.1 from hlvl]
      exact hb_mem.2
    · rw [← hJi_eq]; rw [show c.X = rc.2.toFinset from hX]; exact ha'.2.1
    · rw [← hJi_eq]; rw [show c.X = rc.2.toFinset from hX]; exact ha'.2.2
  have hcomp_disj : ∀ ci₁ ci₂ (h1 : ci₁ < wd.comps.length) (h2 : ci₂ < wd.comps.length),
      ci₁ ≠ ci₂ →
      Disjoint (wd.comps[ci₁]'h1).jSubOrigEdges.toFinset (wd.comps[ci₂]'h2).jSubOrigEdges.toFinset := by
    intro ci₁ ci₂ h1 h2 hne
    rw [Finset.disjoint_left]
    intro jOrig hj1 hj2
    rw [List.mem_toFinset] at hj1 hj2
    obtain ⟨b₁, hb1m, hb1nl, hb1lvl, hb1X, _⟩ := hjSub_mem_preimage ci₁ h1 jOrig hj1
    obtain ⟨b₂, hb2m, hb2nl, hb2lvl, hb2X, _⟩ := hjSub_mem_preimage ci₂ h2 jOrig hj2
    have hb_eq : b₁ = b₂ := by rw [← hb2nl] at hb1nl; exact hnl_nodup.getElem_inj_iff.mp hb1nl
    subst hb_eq
    have hp := rawComps_pairwise_disj hv
    have h1r : ci₁ < inp.prep.rawComps.length := by omega
    have h2r : ci₂ < inp.prep.rawComps.length := by omega
    obtain ⟨hl1, hX1, _⟩ := buildCompsFrom_getElem_full inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci₁ h1r
    obtain ⟨hl2, hX2, _⟩ := buildCompsFrom_getElem_full inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci₂ h2r
    have hrel : (inp.prep.rawComps[ci₁]'h1r).1 ≠ (inp.prep.rawComps[ci₂]'h2r).1 ∨
        Disjoint (inp.prep.rawComps[ci₁]'h1r).2.toFinset (inp.prep.rawComps[ci₂]'h2r).2.toFinset := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact List.pairwise_iff_getElem.mp hp ci₁ ci₂ h1r h2r hlt
      · rcases List.pairwise_iff_getElem.mp hp ci₂ ci₁ h2r h1r hgt with hneq | hdisj
        · exact Or.inl hneq.symm
        · exact Or.inr hdisj.symm
    rw [← hl1, ← hl2, ← hX1, ← hX2] at hrel
    rcases hrel with hlvl_ne | hXdisj
    · exact hlvl_ne (hb1lvl.symm.trans hb2lvl)
    · exact Finset.disjoint_left.mp hXdisj hb1X hb2X
  have hcomp_disj_j0 : ∀ ci (hci : ci < wd.comps.length),
      Disjoint (wd.comps[ci]'hci).jSubOrigEdges.toFinset wd.j0Edges.toFinset := by
    intro ci hci
    rw [Finset.disjoint_left]
    intro jOrig hj1 hj0
    rw [List.mem_toFinset] at hj1 hj0
    obtain ⟨b₁, _, hb1nl, hb1lvl, _, _⟩ := hjSub_mem_preimage ci hci jOrig hj1
    obtain ⟨b₂, hb2m, hb2lvl, hb2nl⟩ :
        ∃ b₂ < wd.J0_strip.m, wd.decomp.level b₂ = 0 ∧ wd.nlIdx.getD b₂ 0 = jOrig := by
      change jOrig ∈ (wd.decomp.edgesAt wd.J0_strip 0).map (fun k => wd.nlIdx.getD k 0) at hj0
      simp only [DecomposeOutput.edgesAt, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at hj0
      rcases hj0 with ⟨b₂, ⟨hb2m, hb2lvl⟩, rfl⟩
      exact ⟨b₂, hb2m, hb2lvl, rfl⟩
    rw [List.getD_eq_getElem _ _ (by omega)] at hb2nl
    have hb_eq : b₁ = b₂ := hnl_nodup.getElem_inj_iff.mp (hb1nl.trans hb2nl.symm)
    subst hb_eq
    have hpos := (hcprops ci hci).1
    omega
  exact
    { W_n := rfl
      W_valid := hW_valid
      W_m_eq := hWm_eq
      aligned := haligned
      φ_dec_pos := hφ_dec_pos
      φ_dec_le := hφ_dec_le
      φ_Const_pos := ce.hφ_Const_pos
      φ_Const_le := ce.hφ_Const_le
      c_deg_ge := hcdeg_ge
      φ_ds_pos := hφds_pos
      φ_ds_le_dec := hφds_le_dec
      φ_ds_le_Const := hφds_le_ce
      φ_ds_half := hφds_half
      γ_ExpPath_ge := hγE_ge
      γ_del_ge := hγD_ge
      τ₁_nonneg := hτ₁_nn
      τ₂_pos := hτ₂_pos
      j0_nodup := hj0_nodup
      j0_lt := hj0_lt
      comp_props := hcprops
      comp_disjoint := hcomp_disj
      comp_disjoint_j0 := hcomp_disj_j0 }

/-- Every level-0 edge `eW < j0Edges.length` in `mkWitnessData` has weight
`(phiNum_dec : ℝ) / phiDen_dec`. -/
theorem mkWitnessData_wW_j0 {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {eW : ℕ}
    (heW : eW < inp.prep.j0Edges.length) :
    (inp.mkWitnessData ce pds WSubs).wW eW =
      (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) := by
  change witnessWeight _ inp.prep.j0Edges.length _ eW = _
  simp [witnessWeight, heW]

/-- Every component edge `c.wStart + eL` in `mkWitnessData` has weight
`(phiNum_dec * 2 ^ c.level : ℝ) / phiDen_dec`. -/
theorem mkWitnessData_wW_comp {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hws : inp.ValidWSubs ce WSubs)
    {ci eL : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length)
    (heL : eL < ((inp.mkWitnessData ce pds WSubs).comps[ci]'hci).W_sub.m) :
    let c := (inp.mkWitnessData ce pds WSubs).comps[ci]'hci
    (inp.mkWitnessData ce pds WSubs).wW (c.wStart + eL) =
      ((inp.prep.phiNum_dec * 2 ^ c.level : ℕ) : ℝ) / (inp.prep.phiDen_dec : ℝ) := by
  dsimp only
  set wd := inp.mkWitnessData ce pds WSubs
  set c := wd.comps[ci]'hci
  have haligned : CompsAligned inp.prep.j0Edges.length wd.comps :=
    buildCompsFrom_aligned inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hge_j0 : inp.prep.j0Edges.length ≤ c.wStart :=
    compsAligned_wStart_ge haligned c (List.getElem_mem hci)
  have hnot_lt : ¬ c.wStart + eL < inp.prep.j0Edges.length := by omega
  have hfind : List.find? (fun d : CompInfo => decide (d.wStart ≤ c.wStart + eL ∧
      c.wStart + eL < d.wStart + d.W_sub.m)) wd.comps = some c :=
    find?_comp_unique haligned hci (by simp [c]) (by dsimp only [c]; exact Nat.add_lt_add_left heL _)
  change witnessWeight ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ))
    inp.prep.j0Edges.length wd.comps (c.wStart + eL) = _
  simp only [witnessWeight, hnot_lt, ↓reduceIte, hfind, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Total vertex count and total integer vertex weights passed to `ConstructExpander` across all
components of `inp.prep.rawComps`, bounded by `2 * J0_strip.m` and `2 * J0_strip.m / φ_dec`. -/
theorem ceWeights_sum_le {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem : ℕ → ℕ} {w : ℕ} (hvalid : inp.Valid ce pds mem w) :
    let m0 := inp.prep.J0_strip.m
    let φ_dec : ℝ := (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)
    (inp.prep.rawComps.map fun rc => rc.2.length).sum ≤ 2 * m0 ∧
    (inp.prep.rawComps.map fun rc => ((inp.compWeights rc).sum : ℝ)).sum ≤
      2 * (m0 : ℝ) / φ_dec := by
  intro m0 φ_dec
  have hv := hvalid.2.2.1
  have hsz := PrepInput.StaticValid.size_bounds hv
  have hpn := hv.2.2.2.2.2.2.2.2.1
  have hpnd := hv.2.2.2.2.2.2.2.2.2.1
  have hφ_pos : 0 < φ_dec := div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
  have hjm_le : (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum ≤ m0 := by omega
  have hpt_nat : ∀ ci (hci : ci < inp.prep.rawComps.length),
      inp.prep.rawComps[ci].2.length ≤ 2 * (inp.prep.cJSub inp.prep.rawComps[ci]).m := by
    intro ci hcir
    have hcprops := comp_props_at hv.toValid_zeroTail hcir
    have hc_eq : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by simp [hcir]
    rw [hc_eq] at hcprops
    have hvol := vol_verts_eq_two_mul_m hcprops.2.2.2.2.2.2.2
    have hsum_deg : ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
        (inp.prep.cJSub inp.prep.rawComps[ci]).deg k =
        2 * (inp.prep.cJSub inp.prep.rawComps[ci]).m := by
      rw [← hvol, ← hcprops.2.2.2.2.2.2.1]; rfl
    have hdeg1 : ∀ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
        1 ≤ (inp.prep.cJSub inp.prep.rawComps[ci]).deg k := by
      intro k hk
      have hge := rawComps_deg_ge_phi hv hcir k (Finset.mem_range.mp hk)
      have h2 : (0 : ℝ) < 2 ^ inp.prep.rawComps[ci].1 := by positivity
      have hr : (0 : ℝ) < ((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) :=
        lt_of_lt_of_le (mul_pos hφ_pos h2) hge
      exact Nat.cast_pos.mp hr
    calc inp.prep.rawComps[ci].2.length
        = ∑ _k ∈ Finset.range inp.prep.rawComps[ci].2.length, 1 := by simp
      _ ≤ ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
            (inp.prep.cJSub inp.prep.rawComps[ci]).deg k := Finset.sum_le_sum hdeg1
      _ = 2 * (inp.prep.cJSub inp.prep.rawComps[ci]).m := hsum_deg
  have hpt_wt : ∀ ci (hci : ci < inp.prep.rawComps.length),
      ((inp.compWeights inp.prep.rawComps[ci]).sum : ℝ) ≤
        2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) / φ_dec := by
    intro ci hcir
    have hcb := comp_weight_bounds hv hcir
    have hcprops := comp_props_at hv.toValid_zeroTail hcir
    have hc_eq : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by simp [hcir]
    rw [hc_eq] at hcprops
    have hvol := vol_verts_eq_two_mul_m hcprops.2.2.2.2.2.2.2
    have hsum_deg : ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
        ((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) =
        2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) := by
      have hnat : ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
          (inp.prep.cJSub inp.prep.rawComps[ci]).deg k =
          2 * (inp.prep.cJSub inp.prep.rawComps[ci]).m := by
        rw [← hvol, ← hcprops.2.2.2.2.2.2.1]; rfl
      exact_mod_cast hnat
    have hdeg_pt : ∀ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
        (((inp.compWeights inp.prep.rawComps[ci]).getD k 0 : ℕ) : ℝ) ≤
          2 * (((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) /
            (φ_dec * (2 : ℝ) ^ inp.prep.rawComps[ci].1)) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      obtain ⟨_, hceil, _⟩ := hcb.2.2.2.1 k hk'
      have hge := rawComps_deg_ge_phi hv hcir k hk'
      have hw1 : 1 ≤ ((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) /
          (φ_dec * (2 : ℝ) ^ inp.prep.rawComps[ci].1) :=
        (one_le_div (by positivity)).mpr hge
      have h2 := real_ceil_le_two_mul hw1
      rw [List.getD_eq_getElem _ _ (by rw [hcb.2.2.1]; exact hk')]
      exact_mod_cast hceil ▸ h2
    have hsum_w : ((inp.compWeights inp.prep.rawComps[ci]).sum : ℝ) =
        ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
          ((inp.compWeights inp.prep.rawComps[ci]).getD k 0 : ℝ) := by
      have h1 := congrArg (Nat.cast (R := ℝ)) (sum_range_getD_nat (inp.compWeights inp.prep.rawComps[ci]) 0 id)
      simpa [hcb.2.2.1] using h1.symm
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ inp.prep.rawComps[ci].1 := by
      have h1 : 1 ≤ inp.prep.rawComps[ci].1 := hcprops.1
      have : 2 ^ 1 ≤ 2 ^ inp.prep.rawComps[ci].1 := Nat.pow_le_pow_right (by omega) h1
      exact_mod_cast this
    calc ((inp.compWeights inp.prep.rawComps[ci]).sum : ℝ)
        = ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
            ((inp.compWeights inp.prep.rawComps[ci]).getD k 0 : ℝ) := hsum_w
      _ ≤ ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
            2 * (((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) /
              (φ_dec * (2 : ℝ) ^ inp.prep.rawComps[ci].1)) := Finset.sum_le_sum hdeg_pt
      _ = 2 * (2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ)) /
            (φ_dec * (2 : ℝ) ^ inp.prep.rawComps[ci].1) := by
            simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hsum_deg]
            ring
      _ ≤ 2 * (2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ)) / (φ_dec * 2) := by
            gcongr
      _ = 2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) / φ_dec := by ring
  refine ⟨?_, ?_⟩
  · calc (inp.prep.rawComps.map fun rc => rc.2.length).sum
        = ∑ ci ∈ Finset.range inp.prep.rawComps.length,
            (inp.prep.rawComps.getD ci (0, [])).2.length :=
          (sum_range_getD_nat inp.prep.rawComps (0, []) fun rc => rc.2.length).symm
      _ ≤ ∑ ci ∈ Finset.range inp.prep.rawComps.length,
            2 * (inp.prep.cJSub (inp.prep.rawComps.getD ci (0, []))).m := by
          refine Finset.sum_le_sum fun ci hci => ?_
          have hcir := Finset.mem_range.mp hci
          rw [List.getD_eq_getElem _ _ hcir]
          exact hpt_nat ci hcir
      _ = 2 * (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum := by
          rw [← Finset.mul_sum, sum_range_getD_nat inp.prep.rawComps (0, []) fun rc => (inp.prep.cJSub rc).m]
      _ ≤ 2 * m0 := Nat.mul_le_mul_left 2 hjm_le
  · calc (inp.prep.rawComps.map fun rc => ((inp.compWeights rc).sum : ℝ)).sum
        = ∑ ci ∈ Finset.range inp.prep.rawComps.length,
            ((inp.compWeights (inp.prep.rawComps.getD ci (0, []))).sum : ℝ) :=
          (sum_range_getD_real inp.prep.rawComps (0, []) fun rc => ((inp.compWeights rc).sum : ℝ)).symm
      _ ≤ ∑ ci ∈ Finset.range inp.prep.rawComps.length,
            2 * ((inp.prep.cJSub (inp.prep.rawComps.getD ci (0, []))).m : ℝ) / φ_dec := by
          refine Finset.sum_le_sum fun ci hci => ?_
          have hcir := Finset.mem_range.mp hci
          rw [List.getD_eq_getElem _ _ hcir]
          exact hpt_wt ci hcir
      _ = (2 * ∑ ci ∈ Finset.range inp.prep.rawComps.length,
            ((inp.prep.cJSub (inp.prep.rawComps.getD ci (0, []))).m : ℝ)) / φ_dec := by
          simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = 2 * ((inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum : ℝ) / φ_dec := by
          have h1 : ∑ ci ∈ Finset.range inp.prep.rawComps.length,
              ((inp.prep.cJSub (inp.prep.rawComps.getD ci (0, []))).m : ℝ) =
              ((inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum : ℝ) := by
            have hn := sum_range_getD_nat inp.prep.rawComps (0, []) fun rc => (inp.prep.cJSub rc).m
            exact_mod_cast hn
          rw [h1]
      _ ≤ 2 * (m0 : ℝ) / φ_dec := by
          have hjm_r : ((inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum : ℝ) ≤ (m0 : ℝ) := by
            exact_mod_cast hjm_le
          gcongr

end WitnessCoreInput

end MinCostFlow.Spanner
