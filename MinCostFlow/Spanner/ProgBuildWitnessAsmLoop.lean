module

public import MinCostFlow.Spanner.ProgBuildWitnessAsmJOrig

/-!
# Witness assembly Phase 3: component-assembly loop

Defines `cePhase3Cost` and proves the component-assembly loop triples
`buildCompAsmBody_triple` and `buildCompAsmLoop_triple`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

private lemma sum_range_getElem!_eq (xs : List ℕ) :
    (∑ i ∈ Finset.range xs.length, xs[i]!) = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, Nat.add_comm]
    simpa [Nat.add_comm] using congrArg (· + x) ih

/-- Total step budget for Phase 3 (`buildAssembleStmt`). -/
def cePhase3Cost (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) : ℕ :=
  198 * inp.prep.J0_strip.m + 119 * inp.mwInt ce + 109 * inp.prep.rawComps.length + 120

private lemma rangeCost_eq_finset_sum (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = ∑ i ∈ Finset.range n, f i := by
  rw [rangeCost_zero_eq_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

private lemma deg_sum_le_mwInt {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {w : ℕ} {WSubs : List Graph}
    (hvalid : inp.Valid ce pds mem₀ w) (hws : inp.ValidWSubs ce WSubs) :
    (WSubs.map Graph.m).sum ≤ inp.mwInt ce := by
  have hceil : ∀ (i : ℕ) (hi : i < inp.prep.rawComps.length),
      2 * (WSubs.getD i { n := 0, edges := [] }).m ≤
        ce.c_deg_int * (inp.compWeights (inp.prep.rawComps[i]'hi)).sum := by
    intro i hi
    have hspec := hws.2 i hi
    set rc := inp.prep.rawComps[i]
    set W := WSubs.getD i { n := 0, edges := [] }
    have hvol : W.vol W.verts = 2 * W.m := vol_verts_eq_two_mul_m hspec.2.1
    have hclosed : ∀ e ∈ W.edges, e.1 ∈ W.verts ↔ e.2 ∈ W.verts := by
      intro e he
      have huv := hspec.2.1 e he
      simp [Graph.verts, huv.1, huv.2]
    have hsum_deg : ∑ v ∈ Finset.range rc.2.length, W.deg v = 2 * W.m := by
      have hvw : ∑ v ∈ W.verts, W.deg v = 2 * W.m := by
        rw [← hvol, Graph.vol, Graph.volIn]
        exact Finset.sum_congr rfl fun v hv => (degIn_eq_deg_of_closed hspec.2.1 hclosed hv).symm
      simpa [Graph.verts, hspec.1] using hvw
    have hle_sum : ∑ v ∈ Finset.range rc.2.length, W.deg v ≤
        ∑ v ∈ Finset.range rc.2.length, ce.c_deg_int * (inp.compWeights rc)[v]! := by
      refine Finset.sum_le_sum fun v hv => ?_
      have hvk : v < rc.2.length := Finset.mem_range.mp hv
      have hdv := (hspec.2.2.2 v hvk).2
      have hlen_w : (inp.compWeights rc).length = rc.2.length :=
        (WitnessCoreInput.comp_weight_bounds hvalid.2.2.1 hi).2.2.1
      have hget : (inp.compWeights rc)[v]'(by rw [hlen_w]; exact hvk) = (inp.compWeights rc)[v]! := by
        simp [hlen_w, hvk]
      rw [← hget]
      exact_mod_cast hdv
    have hsum_w : (∑ v ∈ Finset.range rc.2.length, ce.c_deg_int * (inp.compWeights rc)[v]!) =
        ce.c_deg_int * (inp.compWeights rc).sum := by
      rw [← Finset.mul_sum]
      congr 1
      have hlen_w : (inp.compWeights rc).length = rc.2.length :=
        (WitnessCoreInput.comp_weight_bounds hvalid.2.2.1 hi).2.2.1
      rw [← hlen_w]
      exact sum_range_getElem!_eq (inp.compWeights rc)
    omega
  have h2m_sum : 2 * (WSubs.map Graph.m).sum ≤
      ce.c_deg_int * (inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).sum := by
    have hlen : WSubs.length = inp.prep.rawComps.length := hws.1
    calc
      2 * (WSubs.map Graph.m).sum =
          2 * ∑ i ∈ Finset.range WSubs.length, (WSubs.getD i { n := 0, edges := [] }).m := by
        congr 1
        symm
        calc
          ∑ i ∈ Finset.range WSubs.length, (WSubs.getD i { n := 0, edges := [] }).m =
              ∑ i ∈ Finset.range WSubs.length, (WSubs.map Graph.m)[i]! := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' : i < WSubs.length := Finset.mem_range.mp hi
            simp [hi']
          _ = (WSubs.map Graph.m).sum := by
            have hl : (WSubs.map Graph.m).length = WSubs.length := List.length_map _
            rw [← hl]; exact sum_range_getElem!_eq (WSubs.map Graph.m)
      _ = ∑ i ∈ Finset.range inp.prep.rawComps.length,
            2 * (WSubs.getD i { n := 0, edges := [] }).m := by
        rw [Finset.mul_sum, hlen]
      _ ≤ ∑ i ∈ Finset.range inp.prep.rawComps.length,
            ce.c_deg_int * (inp.compWeights inp.prep.rawComps[i]!).sum := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < inp.prep.rawComps.length := Finset.mem_range.mp hi
        have hget_rc : inp.prep.rawComps[i]! = inp.prep.rawComps[i] := by simp [hi']
        rw [hget_rc]
        exact hceil i hi'
      _ = ce.c_deg_int * (inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).sum := by
        rw [← Finset.mul_sum]
        congr 1
        calc
          ∑ i ∈ Finset.range inp.prep.rawComps.length,
              (inp.compWeights inp.prep.rawComps[i]!).sum =
              ∑ i ∈ Finset.range (inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).length,
                (inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum)[i]! := by
            rw [List.length_map]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' : i < inp.prep.rawComps.length := Finset.mem_range.mp hi
            simp [hi']
          _ = (inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).sum :=
            sum_range_getElem!_eq _
  have hcw := (WitnessCoreInput.ceWeights_sum_le hvalid).2
  have hmw := WitnessCoreInput.mwInt_eq inp ce hvalid.2.2.1
  have hpn : (0 : ℝ) < inp.prep.phiNum_dec := by
    exact_mod_cast hvalid.2.2.1.2.2.2.2.2.2.2.2.1
  have hpd : (0 : ℝ) < inp.prep.phiDen_dec := by
    have hle := hvalid.2.2.1.2.2.2.2.2.2.2.2.2.1
    exact_mod_cast Nat.lt_of_lt_of_le hvalid.2.2.1.2.2.2.2.2.2.2.2.1 hle
  have hphi_pos : (0 : ℝ) ≤ (inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec :=
    le_of_lt (div_pos hpn hpd)
  have hreal : ((WSubs.map Graph.m).sum : ℝ) ≤
      2 * ce.c_deg_int * inp.prep.J0_strip.m / ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec) := by
    have hcast : ((List.map (fun rc => (inp.compWeights rc).sum) inp.prep.rawComps).sum : ℝ) =
        (List.map (fun rc => ((inp.compWeights rc).sum : ℝ)) inp.prep.rawComps).sum := by
      clear hceil h2m_sum hcw
      induction inp.prep.rawComps with
      | nil => simp
      | cons _ _ ih => simp [ih]
    have h2m_r : (2 : ℝ) * ((WSubs.map Graph.m).sum : ℝ) ≤
        ce.c_deg_int * (List.map (fun rc => ((inp.compWeights rc).sum : ℝ)) inp.prep.rawComps).sum := by
      rw [← hcast]
      exact_mod_cast h2m_sum
    have hmul : (ce.c_deg_int : ℝ) *
        (List.map (fun rc => ((inp.compWeights rc).sum : ℝ)) inp.prep.rawComps).sum ≤
        ce.c_deg_int * (2 * inp.prep.J0_strip.m / ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec)) :=
      mul_le_mul_of_nonneg_left hcw (by positivity)
    have hdiv_nn : (0 : ℝ) ≤
        (ce.c_deg_int : ℝ) * inp.prep.J0_strip.m / ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec) :=
      div_nonneg (by positivity) hphi_pos
    have hassoc : (ce.c_deg_int : ℝ) *
        (2 * inp.prep.J0_strip.m / ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec)) =
        2 * ((ce.c_deg_int : ℝ) * inp.prep.J0_strip.m /
          ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec)) := by ring
    have hassoc2 : 2 * (ce.c_deg_int : ℝ) * inp.prep.J0_strip.m /
        ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec) =
        2 * ((ce.c_deg_int : ℝ) * inp.prep.J0_strip.m /
          ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec)) := by ring
    linarith
  have hceil_le : (WSubs.map Graph.m).sum ≤
      ⌈2 * (ce.c_deg_int : ℝ) * inp.prep.J0_strip.m /
        ((inp.prep.phiNum_dec : ℝ) / inp.prep.phiDen_dec)⌉₊ := by
    rw [← @Nat.cast_le ℝ]
    exact le_trans hreal (Nat.le_ceil _)
  rw [hmw]
  omega

/-- Range cost of `asmCompStepCost` across all components. -/
private lemma rangeCost_asmCompStepCost {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {w : ℕ} {WSubs : List Graph}
    (hvalid : inp.Valid ce pds mem₀ w) (hws : inp.ValidWSubs ce WSubs) :
    rangeCost (asmCompStepCost inp WSubs) 0 inp.prep.rawComps.length ≤
      (asmWEdgeCost + 9) * inp.mwInt ce +
        (asmJOrigCost + 9) * (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum +
        100 * inp.prep.rawComps.length := by
  have hsum_w : (WSubs.map Graph.m).sum ≤ inp.mwInt ce := deg_sum_le_mwInt hvalid hws
  rw [rangeCost_eq_finset_sum]
  have hsplit : ∀ i ∈ Finset.range inp.prep.rawComps.length,
      asmCompStepCost inp WSubs i =
        (asmWEdgeCost + 9) * (WSubs.getD i { n := 0, edges := [] }).m +
          (asmJOrigCost + 9) * (inp.prep.cJSub inp.prep.rawComps[i]!).m + 100 := by
    intro i _
    unfold asmCompStepCost
    dsimp only
    ring
  rw [Finset.sum_congr rfl hsplit]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum]
  have hw_eq : ∑ i ∈ Finset.range inp.prep.rawComps.length,
      (WSubs.getD i { n := 0, edges := [] }).m = (WSubs.map Graph.m).sum := by
    rw [← hws.1]
    have hl : (WSubs.map Graph.m).length = WSubs.length := List.length_map _
    calc
      ∑ i ∈ Finset.range WSubs.length, (WSubs.getD i { n := 0, edges := [] }).m =
          ∑ i ∈ Finset.range (WSubs.map Graph.m).length, (WSubs.map Graph.m)[i]! := by
        rw [hl]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i < WSubs.length := Finset.mem_range.mp hi
        simp [hi']
      _ = (WSubs.map Graph.m).sum := sum_range_getElem!_eq _
  have hj_eq : ∑ i ∈ Finset.range inp.prep.rawComps.length,
      (inp.prep.cJSub inp.prep.rawComps[i]!).m =
      (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum := by
    have hl : (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).length =
        inp.prep.rawComps.length := List.length_map _
    calc
      ∑ i ∈ Finset.range inp.prep.rawComps.length, (inp.prep.cJSub inp.prep.rawComps[i]!).m =
          ∑ i ∈ Finset.range (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).length,
            (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m)[i]! := by
        rw [hl]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i < inp.prep.rawComps.length := Finset.mem_range.mp hi
        simp [hi']
      _ = (inp.prep.rawComps.map fun rc => (inp.prep.cJSub rc).m).sum :=
        sum_range_getElem!_eq _
  rw [hw_eq, hj_eq]
  nlinarith only [hsum_w]

/-- Upper bound `asmTotalCost` by `cePhase3Cost`. -/
lemma asmTotalCost_le {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {w : ℕ} {WSubs : List Graph}
    (hvalid : inp.Valid ce pds mem₀ w) (hws : inp.ValidWSubs ce WSubs) :
    asmTotalCost inp WSubs ≤ cePhase3Cost inp ce := by
  have hrc := rangeCost_asmCompStepCost hvalid hws
  have hsb := (PrepInput.StaticValid.size_bounds hvalid.2.2.1).2.2.2.1
  unfold asmTotalCost cePhase3Cost asmWEdgeCost asmJOrigCost at *
  omega

private lemma mul_two_le_four_succ (m d : ℕ) : 2 * m * d ≤ 4 * (m + 1) * d := by nlinarith

private lemma compAsm_prefix_bounds {w : ℕ} {inp : WitnessCoreInput}
    {ce : ConstructExpanderImpl} {pds : PathDSParams} {mem₀ : ℕ → ℕ} {WSubs : List Graph}
    {aCompExt wAddr ci : ℕ} {st : State}
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length)
    (hinv : AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr ci st) :
    let wd := inp.mkWitnessData ce pds WSubs
    let comp := wd.comps.getD ci defaultCompInfo
    let aComps := inp.prep.aComps
    1 < 2 ^ w ∧
    inp.h + 20 ≤ aCompExt ∧
    aComps + (6 + 7 * ci) < 2 ^ w ∧
    aCompExt + (5 + 6 * ci) < 2 ^ w ∧
    inp.prep.cVertsPtr ci < 2 ^ w ∧
    inp.prep.cJOrigPtr ci < 2 ^ w ∧
    comp.J_sub.m < 2 ^ w ∧
    comp.wStart < 2 ^ w ∧
    st.mem (aCompExt + 6 * ci + 1) < 2 ^ w ∧
    inp.prep.phiNum_dec * 2 ^ comp.level < 2 ^ w ∧
    comp.W_sub.m < 2 ^ w := by
  intro wd comp aComps
  rcases hinv with ⟨_, hbase, hr18, _, _, _, _, _, _, _, hws, ha_ext, hmax_le,
    hcomp_ext, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hwb := ce_word_bounds hvalid
  have h1w : 1 < 2 ^ w := hwb.1
  have hmax_w : inp.maxHeapEnd ce pds < 2 ^ w := hwb.2.1
  have hv := hvalid.2.2.1
  have hsb := PrepInput.StaticValid.size_bounds hv
  have hhend : inp.prep.hEnd ≤ inp.h := hvalid.2.2.2.1
  have ha_ge : inp.h + 20 ≤ aCompExt := by
    rw [← hr18]
    exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEnd_le_max : wAddr + (2 + 2 * wd.W.m) + wd.W.m + 3 * wd.W.m + 3 * inp.prep.J.m ≤
      inp.maxHeapEnd ce pds := hmax_le
  have haComps_lt : aComps + (6 + 7 * ci) < 2 ^ w := by
    unfold aComps PrepInput.aComps PrepInput.aJ0Out PrepInput.aEdgeNext PrepInput.aLvlHead
    have hhb : inp.prep.hBlocksStart ≤ inp.prep.hEnd := by
      unfold PrepInput.hEnd
      omega
    unfold PrepInput.hBlocksStart at hhb
    omega
  have haExt_lt : aCompExt + (5 + 6 * ci) < 2 ^ w := by omega
  have hcVerts_lt : inp.prep.cVertsPtr ci < 2 ^ w := by
    unfold PrepInput.cVertsPtr
    have htake_sum : (List.map (fun p => 2 + p.2.length) (List.take ci inp.prep.rawComps)).sum ≤
        (List.map (fun p => 2 + p.2.length) inp.prep.rawComps).sum := by
      have happ := congrArg (fun xs : List (ℕ × List ℕ) => (xs.map fun p => 2 + p.2.length).sum)
        (List.take_append_drop ci inp.prep.rawComps)
      rw [List.map_append, List.sum_append] at happ
      omega
    have hdec_le : inp.prep.decAddr ≤ inp.prep.h := by
      have hd := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      omega
    have hwb_prep := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    omega
  have hcJOrig_lt : inp.prep.cJOrigPtr ci < 2 ^ w := by
    unfold PrepInput.cJOrigPtr PrepInput.cJSubPtr
    have htake1 : List.take (ci + 1) inp.prep.rawComps =
        List.take ci inp.prep.rawComps ++ [inp.prep.rawComps[ci]] :=
      List.take_succ_eq_append_getElem hci
    have hsum1 : (List.map (fun p => 2 + 3 * (inp.prep.cJSub p).m + p.2.length)
        (List.take (ci + 1) inp.prep.rawComps)).sum ≤
        (List.map (fun p => 2 + 3 * (inp.prep.cJSub p).m + p.2.length) inp.prep.rawComps).sum := by
      have happ := congrArg (fun xs : List (ℕ × List ℕ) =>
          (xs.map fun p => 2 + 3 * (inp.prep.cJSub p).m + p.2.length).sum)
        (List.take_append_drop (ci + 1) inp.prep.rawComps)
      rw [List.map_append, List.sum_append] at happ
      omega
    rw [htake1, List.map_append, List.sum_append] at hsum1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum1
    have hgetd : inp.prep.rawComps.getD ci (0, []) = inp.prep.rawComps[ci] := by
      simp [List.getD_eq_getElem?_getD, hci]
    rw [hgetd]
    unfold PrepInput.hEnd at hhend
    omega
  have hclen : wd.comps.length = inp.prep.rawComps.length :=
    WitnessCoreInput.buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hceq : wd.comps[ci]'(by rw [hclen]; exact hci) = comp := by
    simp [comp, List.getD_eq_getElem?_getD, hclen, hci]
  have hw_ci := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci
  have hcomp_j : comp.J_sub = inp.prep.cJSub inp.prep.rawComps[ci] := by
    dsimp only [comp, wd, WitnessCoreInput.mkWitnessData]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci), Option.getD_some]
    exact hw_ci.2.2.2.2.2.1
  have hcomp_w : comp.W_sub = WSubs[ci]'(by rw [hws.1]; exact hci) := by
    dsimp only [comp, wd, WitnessCoreInput.mkWitnessData]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci), Option.getD_some]
    exact hw_ci.2.1
  have hcomp_lvl : comp.level = inp.prep.rawComps[ci].1 := by
    dsimp only [comp, wd, WitnessCoreInput.mkWitnessData]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci), Option.getD_some]
    exact hw_ci.2.2.1
  have hJsub_lt : comp.J_sub.m < 2 ^ w := by
    have hm_le : (inp.prep.cJSub inp.prep.rawComps[ci]).m ≤ inp.prep.J0_strip.m := by
      have hmem : (inp.prep.cJSub inp.prep.rawComps[ci]).m ≤
          (inp.prep.rawComps.map fun p => (inp.prep.cJSub p).m).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map.mpr ⟨inp.prep.rawComps[ci], List.getElem_mem hci, rfl⟩)
      omega
    have hwb_prep := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hle_j : inp.prep.h ≤ inp.h := by
      have hs : inp.prep.h ≤ inp.prep.hBlocksStart := by unfold PrepInput.hBlocksStart; omega
      have he : inp.prep.hBlocksStart ≤ inp.prep.hEnd := by unfold PrepInput.hEnd; omega
      omega
    rw [hcomp_j]
    omega
  have haligned := WitnessCoreInput.buildCompsFrom_aligned inp inp.prep.j0Edges.length
    inp.prep.rawComps WSubs hws.1
  have hwend : comp.wStart + comp.W_sub.m ≤
      inp.prep.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
    have he := compsAligned_wEnd_le haligned ci (by
      rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci)
    have heq' : (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[ci]'(by
        rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci) = comp := hceq
    change ((inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[ci]'(by
        rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci)).wStart +
      ((inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[ci]'(by
        rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci)).W_sub.m ≤ _ at he
    rw [heq'] at he
    exact he
  have hsum_eq : (wd.comps.map fun c => c.W_sub.m).sum = (WSubs.map Graph.m).sum := by
    have hcongr : List.map (fun c => c.W_sub.m) wd.comps = List.map Graph.m WSubs := by
      refine List.ext_getElem (by rw [List.length_map, List.length_map, hclen, hws.1]) fun i hi1 hi2 => ?_
      have hi : i < inp.prep.rawComps.length := by rw [List.length_map, hclen] at hi1; exact hi1
      have hwi := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 i hi
      simp only [List.getElem_map]
      change ((inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[i]'(by
          rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hi)).W_sub.m =
        (WSubs[i]'(by rw [hws.1]; exact hi)).m
      rw [hwi.2.1]
    exact congrArg List.sum hcongr
  have hwm_eq := mkWitnessData_W_m_eq_sum inp ce pds hws.1
  have hwStart_lt : comp.wStart < 2 ^ w := by omega
  have hWsub_lt : comp.W_sub.m < 2 ^ w := by omega
  have hcompExt_ci := hcomp_ext ci (by rw [hclen]; exact hci)
  have hpw_le : st.mem (aCompExt + 6 * ci + 1) ≤ wAddr :=
    Nat.le_trans (Nat.le_add_right _ _) hcompExt_ci.2.2.2.2.2.2.2
  have hw_le_hEnd : wAddr ≤ wAddr + (2 + 2 * wd.W.m) + wd.W.m + 3 * wd.W.m + 3 * inp.prep.J.m :=
    Nat.le_trans (Nat.le_add_right _ _)
      (Nat.le_trans (Nat.le_add_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
  have hp34_lt : st.mem (aCompExt + 6 * ci + 1) < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.le_trans hpw_le (Nat.le_trans hw_le_hEnd hmax_le)) hmax_w
  have hphi_lt : inp.prep.phiNum_dec * 2 ^ comp.level < 2 ^ w := by
    have hcw := (WitnessCoreInput.comp_weight_bounds hv hci).1
    rw [hcomp_lvl]
    have hm_w := hwb.2.2
    have hle1 : inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 ≤
        4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
      Nat.le_trans hcw (mul_two_le_four_succ _ _)
    have hle2 : 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec < 2 ^ w :=
      Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
        (Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
          (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hm_w))
    exact Nat.lt_of_le_of_lt hle1 hle2
  exact ⟨h1w, ha_ge, haComps_lt, haExt_lt, hcVerts_lt, hcJOrig_lt, hJsub_lt, hwStart_lt, hp34_lt,
    hphi_lt, hWsub_lt⟩

/-- Component assembly body triple: runs `W_sub` edges then `J_sub` orig edges for component `ci`. -/
theorem buildCompAsmBody_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr ci : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length) :
    Triple w p
      (AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr ci)
      buildCompAsmBody
      (normalPost fun st =>
        AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr (ci + 1)
          { st with regs := Function.update st.regs 29 (ci + 1) } ∧ st.regs 29 = ci)
      (fun _ => asmCompStepCost inp WSubs ci) := by
  intro st ω hinv
  have hpb := compAsm_prefix_bounds hvalid hci hinv
  rcases hpb with ⟨h1w, ha_ge, haComps_lt, haExt_lt, hcVerts_lt, hcJOrig_lt, hJsub_lt,
    hwStart_lt, hp34_lt, hphi_lt, hWsub_lt⟩
  set wd := inp.mkWitnessData ce pds WSubs
  set comp := wd.comps.getD ci defaultCompInfo
  rcases hinv with ⟨_, hbase, hr18, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hws, ha_ext, hmax_le,
    hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16, hm_n, hm_m,
    hprev_j0, hprev_w, hprev_j, hzero_w, hzero_j, hzf⟩
  have hclen : wd.comps.length = inp.prep.rawComps.length :=
    WitnessCoreInput.buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hceq : wd.comps[ci]'(by rw [hclen]; exact hci) = comp := by
    simp [comp, List.getD_eq_getElem?_getD, hclen, hci]
  have hw_ci := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci
  have hcdt := hvalid.2.2.2.2.2.2.2.2.2.1 ci hci
  dsimp only at hcdt
  have hcompExt_ci := hcomp_ext ci (by rw [hclen]; exact hci)
  dsimp only at hcompExt_ci
  rw [hceq] at hcompExt_ci
  have hr15 : st.regs 15 = inp.prep.aComps := hbase.2.2.2.2.2.2.2.2.2.1
  have haComps_w : inp.prep.aComps < 2 ^ w := by omega
  have haExt_w : aCompExt < 2 ^ w := by omega
  have hci_w : ci < 2 ^ w := by omega
  have h7w : 7 < 2 ^ w := by omega
  have h6w : 6 < 2 ^ w := by omega
  have h5w : 5 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h7ci_w : 7 * ci < 2 ^ w := by omega
  have h6ci_w : 6 * ci < 2 ^ w := by omega
  have haComps_h : inp.prep.aComps + (6 + 7 * ci) < inp.h := by
    have hhend : inp.prep.hEnd ≤ inp.h := hvalid.2.2.2.1
    have hhb : inp.prep.hBlocksStart ≤ inp.prep.hEnd := by unfold PrepInput.hEnd; omega
    unfold PrepInput.hBlocksStart at hhb
    unfold PrepInput.aComps PrepInput.aJ0Out PrepInput.aEdgeNext PrepInput.aLvlHead
    omega
  have hm_30 : st.mem (inp.prep.aComps + (2 + 7 * ci)) = inp.prep.cVertsPtr ci := by
    rw [show inp.prep.aComps + (2 + 7 * ci) = inp.prep.aComps + 7 * ci + 2 by omega,
      hbelow _ (by omega)]
    exact hcdt.2.2.1
  have hm_31 : st.mem (inp.prep.aComps + (4 + 7 * ci)) = inp.prep.cJOrigPtr ci := by
    rw [show inp.prep.aComps + (4 + 7 * ci) = inp.prep.aComps + 7 * ci + 4 by omega,
      hbelow _ (by omega)]
    exact hcdt.2.2.2.2.1
  have hm_32 : st.mem (inp.prep.aComps + (6 + 7 * ci)) = comp.J_sub.m := by
    rw [show inp.prep.aComps + (6 + 7 * ci) = inp.prep.aComps + 7 * ci + 6 by omega,
      hbelow _ (by omega)]
    have hj_eq : comp.J_sub = inp.prep.cJSub inp.prep.rawComps[ci] := by
      dsimp only [comp, wd, WitnessCoreInput.mkWitnessData]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci), Option.getD_some]
      exact hw_ci.2.2.2.2.2.1
    rw [hj_eq]
    have hcdt_jm := hcdt.2.2.2.2.2.2.1
    simpa [hci] using hcdt_jm
  have hm_33 : st.mem (aCompExt + 6 * ci) = comp.wStart := hcompExt_ci.1
  have hm_35 : st.mem (aCompExt + (3 + 6 * ci)) = inp.prep.phiNum_dec * 2 ^ comp.level := by
    rw [show aCompExt + (3 + 6 * ci) = aCompExt + 6 * ci + 3 by omega]
    exact hcompExt_ci.2.2.1
  have hm_36 : st.mem (aCompExt + (5 + 6 * ci)) = comp.W_sub.m := by
    rw [show aCompExt + (5 + 6 * ci) = aCompExt + 6 * ci + 5 by omega]
    exact hcompExt_ci.2.2.2.2.1
  have hstep_cost : (asmWEdgeCost * comp.W_sub.m + 9 * comp.W_sub.m + 7) +
      (asmJOrigCost * comp.J_sub.m + 9 * comp.J_sub.m + 7) + 1 ≤ asmCompStepCost inp WSubs ci - 68 := by
    have hm1 : comp.W_sub.m = (WSubs.getD ci { n := 0, edges := [] }).m := by
      dsimp only [comp, wd, WitnessCoreInput.mkWitnessData]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci), Option.getD_some,
        hw_ci.2.1]
      simp [List.getD_eq_getElem?_getD, hws.1, hci]
    have hm2 : comp.J_sub.m = (inp.prep.cJSub inp.prep.rawComps[ci]!).m := by
      dsimp only [comp, wd, WitnessCoreInput.mkWitnessData]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci), Option.getD_some,
        hw_ci.2.2.2.2.2.1]
      simp [hci]
    rw [hm1, hm2]
    unfold asmCompStepCost asmWEdgeCost asmJOrigCost
    dsimp only
    omega
  rcases st with ⟨m₀, r₀, pos₀⟩
  dsimp only at hr15 hr18 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hp34_lt hm_30 hm_31 hm_32 hm_33 hm_35 hm_36
  suffices hres : ∃ o st' c',
      Runs w p ω buildCompAsmBody { mem := m₀, regs := r₀, pos := pos₀ } o st' c' ∧
        normalPost (fun st =>
          AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr (ci + 1)
            { st with regs := Function.update st.regs 29 (ci + 1) } ∧ st.regs 29 = ci) o st' ∧
        0 + c' ≤ asmCompStepCost inp WSubs ci by
    simpa only [Nat.zero_add] using hres
  unfold buildCompAsmBody
  refine runs_seq_assign_flat (k := 0) (c_bound := asmCompStepCost inp WSubs ci)
    (v := inp.prep.cVertsPtr ci) ?_ ?_
  · exact ev_load (ev_add (ev_reg hr15 haComps_w)
      (ev_add (ev_const h2w) (ev_mul (ev_const h7w) (ev_reg hr29 hci_w) h7ci_w) (by omega))
      (by omega)) hm_30 hcVerts_lt
  refine runs_seq_assign_flat (v := inp.prep.cJOrigPtr ci) ?_ ?_
  · refine ev_load (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega)]; exact hr15) haComps_w)
      (ev_add (ev_const h4w) (ev_mul (ev_const h7w)
        (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega)]; exact hr29) hci_w) h7ci_w)
        (by omega)) (by omega)) hm_31 hcJOrig_lt
  refine runs_seq_assign_flat (v := comp.J_sub.m) ?_ ?_
  · refine ev_load (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]; exact hr15) haComps_w)
      (ev_add (ev_const h6w) (ev_mul (ev_const h7w)
        (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]; exact hr29) hci_w) h7ci_w)
        (by omega)) (by omega)) hm_32 hJsub_lt
  refine runs_seq_assign_flat (v := comp.wStart) ?_ ?_
  · refine ev_load (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr18) haExt_w)
      (ev_mul (ev_const h6w)
        (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr29) hci_w)
        h6ci_w) (by omega)) hm_33 hwStart_lt
  refine runs_seq_assign_flat (v := m₀ (aCompExt + 6 * ci + 1)) ?_ ?_
  · refine ev_load (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]; exact hr18) haExt_w)
      (ev_add (ev_const h1w) (ev_mul (ev_const h6w)
        (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]; exact hr29) hci_w) h6ci_w)
        (by omega)) (by omega)) ?_ hp34_lt
    dsimp only; rw [show aCompExt + (1 + 6 * ci) = aCompExt + 6 * ci + 1 by omega]
  refine runs_seq_assign_flat (v := inp.prep.phiNum_dec * 2 ^ comp.level) ?_ ?_
  · refine ev_load (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr18) haExt_w)
      (ev_add (ev_const h3w) (ev_mul (ev_const h6w)
        (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr29) hci_w) h6ci_w)
        (by omega)) (by omega)) hm_35 hphi_lt
  refine runs_seq_assign_flat (v := comp.W_sub.m) ?_ ?_
  · refine ev_load (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]; exact hr18) haExt_w)
      (ev_add (ev_const h5w) (ev_mul (ev_const h6w)
        (ev_reg (by dsimp only; rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]; exact hr29) hci_w) h6ci_w)
        (by omega)) (by omega)) hm_36 hWsub_lt
  -- Now run `forRange 37 0 r36 buildCompWEdgesBody ;; forRange 37 0 r32 buildCompJOrigBody`.
  have hloops := Triple.seq_normal_const
    (buildCompWEdgesLoop_triple (p := p) (aCompExt := aCompExt) (wAddr := wAddr) hvalid hci hws)
    (buildCompJOrigLoop_triple (p := p) (aCompExt := aCompExt) (wAddr := wAddr) hvalid hci)
  let r7 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update r₀ 30 (inp.prep.cVertsPtr ci)) 31 (inp.prep.cJOrigPtr ci))
    32 comp.J_sub.m) 33 comp.wStart) 34 (m₀ (aCompExt + 6 * ci + 1)))
    35 (inp.prep.phiNum_dec * 2 ^ comp.level)) 36 comp.W_sub.m
  have hcw_pre : CompWEdgesInv inp ce pds mem₀ WSubs aCompExt wAddr ci 0
      { mem := m₀, regs := Function.update r7 37 0, pos := pos₀ } := by
    unfold CompWEdgesInv
    dsimp only
    refine ⟨Nat.zero_le _, @ceBaseInv_of_agree inp ce pds mem₀ m₀ aCompExt wAddr
        { mem := m₀, regs := r₀, pos := pos₀ } hbase hr18 ha_ext (fun _ _ => rfl)
        (Function.update r7 37 0) (fun r hr => by
          dsimp only [r7]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]),
      by dsimp only [r7, comp, wd]; simp [hr18],
      by dsimp only [r7, comp, wd]; simp [hr23],
      by dsimp only [r7, comp, wd]; simp [hr24],
      by dsimp only [r7, comp, wd]; simp [hr25],
      by dsimp only [r7, comp, wd]; simp [hr26],
      by dsimp only [r7, comp, wd]; simp [hr27],
      by dsimp only [r7, comp, wd]; simp [hr28],
      by dsimp only [r7, comp, wd]; simp [hr29],
      by dsimp only [r7, comp, wd]; simp,
      by dsimp only [r7, comp, wd]; simp,
      by dsimp only [r7, comp, wd]; simp,
      by dsimp only [r7, comp, wd]; simp,
      by dsimp only [r7, comp, wd]; simp,
      by dsimp only [r7, comp, wd]; simp,
      by dsimp only [r7, comp, wd]; simp,
      by simp,
      hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16, hm_n, hm_m,
      hprev_j0, hprev_w, hprev_j, fun _ heL => (Nat.not_lt_zero _ heL).elim, ?_, hzero_j, hzf⟩
    intro k hk1 hk2
    have hw_take : inp.prep.j0Edges.length + (List.map Graph.m (List.take ci WSubs)).sum = comp.wStart := by
      dsimp only [comp, wd, WitnessCoreInput.mkWitnessData]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hci), Option.getD_some]
      exact hw_ci.1.symm
    rw [Nat.add_zero, ← hw_take] at hk1
    exact hzero_w k hk1 hk2
  rcases hloops { mem := m₀, regs := r7, pos := pos₀ } ω hcw_pre with ⟨o, st', c', hruns, hpost, hcost⟩
  refine ⟨o, st', c', hruns, hpost, ?_⟩
  simp only [Expr.size]
  dsimp only [comp, wd] at hstep_cost
  dsimp only at hcost
  omega

/-- Loop across all components `0 .. rawComps.length - 1` building `W_sub` edges and `J_sub` origins. -/
theorem buildCompAsmLoop_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) :
    Triple w p
      (fun st => AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr 0
        { st with regs := Function.update st.regs 29 0 })
      (forRange 29 (.const 0) (.reg 14) buildCompAsmBody)
      (normalPost (AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr inp.prep.rawComps.length))
      (fun _ => rangeCost (asmCompStepCost inp WSubs) 0 inp.prep.rawComps.length +
        9 * inp.prep.rawComps.length + 7) := by
  have h1w : 1 < 2 ^ w := (ce_word_bounds hvalid).1
  have h0w : 0 < 2 ^ w := lt_trans Nat.zero_lt_one h1w
  have hrc_w : inp.prep.rawComps.length < 2 ^ w := by
    have hsb := (PrepInput.StaticValid.size_bounds hvalid.2.2.1).2.1
    have hv := hvalid.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    omega
  refine (Triple.seq_normal_const
    (R := AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr 0)
    (c₁ := (Expr.const 0).size + 1)
    (c₂ := rangeCost (asmCompStepCost inp WSubs) 0 inp.prep.rawComps.length +
      (inp.prep.rawComps.length - 0) * ((Expr.reg 14).size + 8) + ((Expr.reg 14).size + 3))
    ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  · exact Triple.assign (val := fun _ => 0) (fun _ _ => ev_const h0w) fun _ hP => hP
  · exact Triple.forUp_le (asmCompStepCost inp WSubs) 0 inp.prep.rawComps.length
      (Nat.zero_le _) h1w (fun _ => hrc_w)
      (fun _ _ _ _ hP => hP.2.2.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hP => ev_reg hP.2.1.2.2.2.2.2.2.2.2.1 hrc_w)
      (fun ci _ hci => buildCompAsmBody_triple hvalid hci)


end MinCostFlow.Spanner
