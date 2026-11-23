module

public import MinCostFlow.Spanner.ProgBuildWitnessLoop

/-!
# Phase 2 Pure Helpers, Invariants, and Inner Weight-Fill Verification

Provides arithmetic word-size bounds (`ce_word_bounds`), component prefix `W.m` bounds
(`ce_prefix_w_m_bound`), preservation lemmas for `WitnessHdr0` and `CompExtPrefixAt`,
Phase 2 invariants (`CeBaseInv`, `CeLoopInv`, `CeLoopPost`), and the verified Hoare
triple `buildWeightFill_triple` for `buildWeightFillBody`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited WitnessCoreInput

/-! ## 1. Arithmetic, prefix-size, and memory-agreement helpers -/

lemma ce_word_bounds {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {w : ℕ} (hvalid : inp.Valid ce pds mem₀ w) :
    1 < 2 ^ w ∧
    inp.maxHeapEnd ce pds < 2 ^ w ∧
    4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec +
      2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec + 2 * ce.phiDen + 2 < 2 ^ w := by
  have hv := hvalid.2.2.1
  have h1w := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmb := hvalid.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hheap : inp.maxHeapEnd ce pds ≤ inp.maxWordBound ce pds := le_max_left _ _
  have hm_r : 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec +
      2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec + 2 * ce.phiDen + 2 ≤
      inp.maxWordBound ce pds := le_trans (le_max_left _ _) (le_max_right _ _)
  exact ⟨h1w, lt_of_le_of_lt hheap hmb, lt_of_le_of_lt hm_r hmb⟩

lemma nodup_lt_length_le {n : ℕ} : ∀ {xs : List ℕ},
    xs.Nodup → (∀ u ∈ xs, u < n) → xs.length ≤ n := by
  intro xs hnd hu
  rw [← List.toFinset_card_of_nodup hnd]
  calc xs.toFinset.card ≤ (Finset.range n).card :=
        Finset.card_le_card fun x hx => Finset.mem_range.mpr (hu x (List.mem_toFinset.mp hx))
    _ = n := Finset.card_range n

private lemma sum_map_getD {α : Type*} (d : α) (f : α → ℕ) : ∀ xs : List α,
    (xs.map f).sum = ∑ j ∈ Finset.range xs.length, f (xs.getD j d)
  | [] => by simp
  | x :: xs => by
    have ih := sum_map_getD d f xs
    simp only [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
    simp [ih, add_comm]

lemma ce_prefix_w_m_bound {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {w nDone : ℕ} {WSubs : List Graph}
    (hvalid : inp.Valid ce pds mem₀ w) (hle : nDone ≤ inp.prep.rawComps.length)
    (hws : inp.ValidWSubsPrefix ce nDone WSubs) :
    (WSubs.map Graph.m).sum ≤ ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec ∧
    inp.prep.j0Edges.length + (WSubs.map Graph.m).sum ≤
      inp.prep.J0_strip.m + 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by
  have hv := hvalid.2.2.1
  have hsz := PrepInput.StaticValid.size_bounds hv
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hterm : ∀ j (hj : j < nDone),
      2 * (WSubs.getD j ⟨0, []⟩).m ≤
        ce.c_deg_int * (inp.compWeights (inp.prep.rawComps[j]'(by omega))).sum := by
    intro j hj
    have hjr : j < inp.prep.rawComps.length := by omega
    rcases hws.2 j hj hjr with ⟨hWn, hWval, _, hWdeg⟩
    set rc := inp.prep.rawComps[j]
    set W := WSubs.getD j ⟨0, []⟩
    have hvol := vol_verts_eq_two_mul_m hWval
    have hsum_w : ∑ k ∈ Finset.range rc.2.length, W.deg k = 2 * W.m := by
      rw [← hvol]
      unfold Graph.vol Graph.volIn Graph.deg
      rw [Graph.verts, hWn]
    have hlen_w : (inp.compWeights rc).length = rc.2.length := by simp [compWeights]
    have hsum_cw : ∑ k ∈ Finset.range rc.2.length, (inp.compWeights rc).getD k 0 =
        (inp.compWeights rc).sum := by
      have hsm := sum_map_getD 0 (fun n : ℕ => n) (inp.compWeights rc)
      simp only [List.map_id'] at hsm
      rw [← hlen_w, hsm]
    have hpt : ∀ k ∈ Finset.range rc.2.length,
        W.deg k ≤ ce.c_deg_int * (inp.compWeights rc).getD k 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hget : (inp.compWeights rc).getD k 0 =
          (inp.compWeights rc)[k]'(by rw [hlen_w]; exact hk') :=
        List.getD_eq_getElem _ _ (by rw [hlen_w]; exact hk')
      rw [hget]
      exact_mod_cast (hWdeg k hk').2
    calc 2 * W.m
        = ∑ k ∈ Finset.range rc.2.length, W.deg k := hsum_w.symm
      _ ≤ ∑ k ∈ Finset.range rc.2.length, ce.c_deg_int * (inp.compWeights rc).getD k 0 :=
          Finset.sum_le_sum hpt
      _ = ce.c_deg_int * (inp.compWeights rc).sum := by rw [← Finset.mul_sum, hsum_cw]
  have hsum_2W : 2 * (WSubs.map Graph.m).sum ≤
      ce.c_deg_int * ((inp.prep.rawComps.take nDone).map fun rc => (inp.compWeights rc).sum).sum := by
    have h2 : 2 * (WSubs.map Graph.m).sum = ∑ j ∈ Finset.range nDone, 2 * (WSubs.getD j ⟨0, []⟩).m := by
      have hsm := sum_map_getD ⟨0, []⟩ Graph.m WSubs
      rw [hws.1] at hsm
      rw [hsm, Finset.mul_sum]
    have hrt : ((inp.prep.rawComps.take nDone).map fun rc => (inp.compWeights rc).sum).sum =
        ∑ j ∈ Finset.range nDone,
          (inp.compWeights ((inp.prep.rawComps.take nDone).getD j (0, []))).sum := by
      have := sum_map_getD (0, []) (fun rc => (inp.compWeights rc).sum) (inp.prep.rawComps.take nDone)
      rw [List.length_take_of_le hle] at this
      exact this
    rw [h2, hrt, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hget : (inp.prep.rawComps.take nDone).getD j (0, []) = inp.prep.rawComps[j]'(by omega) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_take_of_le hle]; exact hj'),
        List.getElem_take]
    rw [hget]
    exact hterm j hj'
  have htake_le : ((inp.prep.rawComps.take nDone).map fun rc => (inp.compWeights rc).sum).sum ≤
      (inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).sum := by
    conv_rhs => rw [← List.take_append_drop nDone inp.prep.rawComps, List.map_append, List.sum_append]
    exact Nat.le_add_right _ _
  have hcew := (ceWeights_sum_le hvalid).2
  have hsum_all : (inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).sum ≤
      2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by
    have hφ_pos : (0 : ℝ) < (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) :=
      div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
    have hpn_1 : (1 : ℝ) ≤ (inp.prep.phiNum_dec : ℝ) := by exact_mod_cast hpn
    have hreal : ((inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).sum : ℝ) ≤
        2 * (inp.prep.J0_strip.m : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
      have hcast : ((inp.prep.rawComps.map fun rc => (inp.compWeights rc).sum).sum : ℝ) =
          (inp.prep.rawComps.map fun rc => ((inp.compWeights rc).sum : ℝ)).sum := by
        induction inp.prep.rawComps with
        | nil => simp
        | cons x xs ih => simp [ih]
      rw [hcast]
      refine le_trans hcew ?_
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
      have hm_nn : (0 : ℝ) ≤ 2 * (inp.prep.J0_strip.m : ℝ) * (inp.prep.phiDen_dec : ℝ) := by positivity
      calc 2 * (inp.prep.J0_strip.m : ℝ) * (inp.prep.phiDen_dec : ℝ)
          = (2 * (inp.prep.J0_strip.m : ℝ) * (inp.prep.phiDen_dec : ℝ)) * 1 := (mul_one _).symm
        _ ≤ 2 * (inp.prep.J0_strip.m : ℝ) * (inp.prep.phiDen_dec : ℝ) * (inp.prep.phiNum_dec : ℝ) :=
            mul_le_mul_of_nonneg_left hpn_1 hm_nn
    exact_mod_cast hreal
  have hmul : 2 * (WSubs.map Graph.m).sum ≤
      2 * (ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec) := by
    have h1 := le_trans hsum_2W (Nat.mul_le_mul_left _ (le_trans htake_le hsum_all))
    linarith [show ce.c_deg_int * (2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec) =
      2 * (ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec) from by ring]
  have hw_le : (WSubs.map Graph.m).sum ≤ ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by
    omega
  have hw_le2 : (WSubs.map Graph.m).sum ≤ 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by
    calc (WSubs.map Graph.m).sum
        ≤ ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := hw_le
      _ = 1 * (ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec) := by ring
      _ ≤ 2 * (ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by ring
  exact ⟨hw_le, by omega⟩

private lemma compWEdges_length (c : CompInfo) : (compWEdges c).length = c.W_sub.m := by
  simp [compWEdges, Graph.m]

private lemma comps_flatMap_compWEdges_length (inp : WitnessCoreInput) :
    ∀ offset raw ws, ws.length = raw.length →
      ((inp.buildCompsFrom offset raw ws).flatMap compWEdges).length = (ws.map Graph.m).sum
  | _, [], [], _ => by simp [buildCompsFrom]
  | offset, _ :: rest, W :: ws, h => by
    simp only [List.length_cons] at h
    have ih := comps_flatMap_compWEdges_length inp (offset + W.m) rest ws (by omega)
    simp only [buildCompsFrom, List.flatMap_cons, List.length_append,
      compWEdges_length, List.map_cons, List.sum_cons, ih]

lemma mkWitnessData_W_m_eq_sum (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) {WSubs : List Graph} (hws : WSubs.length = inp.prep.rawComps.length) :
    (inp.mkWitnessData ce pds WSubs).W.m =
      inp.prep.j0Edges.length + (WSubs.map Graph.m).sum := by
  simp only [mkWitnessData, Graph.m, List.length_append, List.length_map,
    comps_flatMap_compWEdges_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws]

lemma witnessHdr0_of_agree_below {mem mem' : ℕ → ℕ} {inp : WitnessCoreInput}
    {ce : ConstructExpanderImpl} {pds : PathDSParams} {bound : ℕ}
    (h : WitnessHdr0 mem inp ce pds) (hb : inp.h + 20 ≤ bound)
    (hag : ∀ x < bound, mem' x = mem x) :
    WitnessHdr0 mem' inp ce pds := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [hag _ (by omega)]; first
      | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1
      | exact h.2.2.2.2.1 | exact h.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.1
      | exact h.2.2.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.2.2.1
      | exact h.2.2.2.2.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.2.2.2.2.1
      | exact h.2.2.2.2.2.2.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.2.2.2.2.2.2.1
      | exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2

lemma compExtPrefix_of_agree_below {mem mem' : ℕ → ℕ} {a phiNum_dec curH : ℕ}
    {cs : List CompInfo} (h : CompExtPrefixAt mem a phiNum_dec curH cs)
    (hag : ∀ x < curH, mem' x = mem x) :
    CompExtPrefixAt mem' a phiNum_dec curH cs := by
  intro j hj
  have hp := h j hj
  have hw_eq : mem' (a + 6 * j + 1) = mem (a + 6 * j + 1) :=
    hag _ (by have := hp.2.2.2.2.2.2.2; omega)
  refine ⟨(hag _ (by omega)).trans hp.1, (hag _ (by omega)).trans hp.2.1,
    (hag _ (by omega)).trans hp.2.2.1, (hag _ (by omega)).trans hp.2.2.2.1,
    (hag _ (by omega)).trans hp.2.2.2.2.1, ?_, ?_, ?_⟩
  · rw [hw_eq]
    intro k hk
    have hk_lt : mem (a + 6 * j + 1) + k < curH := by
      have hl : (cs[j].W_sub).encode.length = 2 + 2 * cs[j].W_sub.m := graph_encode_length _
      have := hp.2.2.2.2.2.2.2
      omega
    rw [hag _ hk_lt]
    exact hp.2.2.2.2.2.1 k hk
  · rw [hw_eq]; exact hp.2.2.2.2.2.2.1
  · rw [hw_eq]; exact hp.2.2.2.2.2.2.2

/-! ## 2. Cost and Phase 2 Loop Invariants -/

/-- Exact cost charged for iteration `ci` of `buildCeLoopStmt`. -/
noncomputable def ceStepCost (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (ci : ℕ) : ℕ :=
  let rc := inp.prep.rawComps[ci]!
  34 * rc.2.length +
    Nat.ceil (ce.K_ce * ((rc.2.length : ℝ) + ((inp.compWeights rc).sum : ℝ))) + 120

/-- Exact total cost upper bound charged for `buildCeLoopStmt`. -/
noncomputable def ceLoopCost (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) : ℕ :=
  rangeCost (ceStepCost inp ce) 0 inp.prep.rawComps.length +
    9 * inp.prep.rawComps.length + 10

/-- Fixed registers and static/header memory preserved throughout Phases 2 and 3. -/
def CeBaseInv (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (st : State) : Prop :=
  let aCompExt := st.regs 18
  st.regs 0 = inp.prep.jAddr ∧
  st.regs 4 = inp.h ∧
  st.regs 5 = inp.prep.J.n ∧
  st.regs 6 = inp.prep.J.m ∧
  st.regs 10 = inp.prep.phiNum_dec ∧
  st.regs 11 = inp.prep.phiDen_dec ∧
  st.regs 12 = inp.prep.j0Edges.length ∧
  st.regs 13 = inp.prep.aJ0Out ∧
  st.regs 14 = inp.prep.rawComps.length ∧
  st.regs 15 = inp.prep.aComps ∧
  st.regs 16 = inp.prep.J0_strip.m ∧
  st.mem (inp.h + 12) = aCompExt ∧
  inp.h + 20 ≤ aCompExt ∧
  aCompExt ≤ inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
    pds.boundsSpace (dWInt ce) (inp.mwInt ce) ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  WitnessHdr0 st.mem inp ce pds

/-- Outer `forRange 22 0 rawComps.length (buildCeBody ceBase)` invariant at step `ci`. -/
def CeLoopInv (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (ci : ℕ) (st : State) : Prop :=
  let aCompExt := st.regs 18
  let curH := st.regs 17
  let wStart := st.regs 23
  ci ≤ inp.prep.rawComps.length ∧
  st.regs 22 = ci ∧
  CeBaseInv inp ce pds mem₀ st ∧
  aCompExt + 6 * inp.prep.rawComps.length ≤ curH ∧
  curH ≤ aCompExt + 6 * inp.prep.rawComps.length +
    ((inp.prep.rawComps.take ci).map fun rc => rc.2.length).sum +
    ci * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) ∧
  ZeroFrom st.mem curH ∧
  ∃ WSubs : List Graph,
    inp.ValidWSubsPrefix ce ci WSubs ∧
    wStart = inp.prep.j0Edges.length + (WSubs.map Graph.m).sum ∧
    wStart ≤ inp.prep.J0_strip.m + 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec ∧
    CompExtPrefixAt st.mem aCompExt inp.prep.phiNum_dec curH
      (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs) ∧
    (∀ j < ci, aCompExt + 6 * inp.prep.rawComps.length ≤ st.mem (aCompExt + 6 * j + 1))

/-- Post-condition after `buildCeLoopStmt`, ready for Phase 3 (`buildAssembleStmt`). -/
def CeLoopPost (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (st : State) : Prop :=
  let aCompExt := st.regs 18
  let wAddr := st.regs 17
  let Wm := st.regs 23
  CeBaseInv inp ce pds mem₀ st ∧
  aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr ∧
  ZeroFrom st.mem wAddr ∧
  ∃ WSubs : List Graph,
    let wd := inp.mkWitnessData ce pds WSubs
    inp.ValidWSubs ce WSubs ∧
    Wm = wd.W.m ∧
    CompExtAt st.mem aCompExt inp.prep.phiNum_dec wAddr wd.comps ∧
    wAddr + (2 + 6 * wd.W.m + 3 * inp.prep.J.m) ≤ inp.maxHeapEnd ce pds

/-! ## 3. Inner Weight-Fill Loop Verification -/

def WeightFillInv (inp : WitnessCoreInput) (memStart : ℕ → ℕ)
    (curH ci kCard : ℕ) (regsStart : ℕ → ℕ) (k : ℕ) (st : State) : Prop :=
  let rc := inp.prep.rawComps[ci]!
  k ≤ kCard ∧
  st.regs 30 = k ∧
  (∀ r ≤ 29, st.regs r = regsStart r) ∧
  (∀ x < curH, st.mem x = memStart x) ∧
  ListAt st.mem curH ((inp.compWeights rc).take k) ∧
  ZeroFrom st.mem (curH + k)

theorem buildWeightFill_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ memStart : ℕ → ℕ} {curH ci kCard : ℕ} {regsStart : ℕ → ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length)
    (hkCard : kCard = inp.prep.rawComps[ci].2.length)
    (hcur_ge : inp.h ≤ curH) (hcurH_lt : curH + kCard < 2 ^ w)
    (hdeg_lt : inp.prep.cDegPtr ci + kCard ≤ inp.h)
    (hmem_lt : ∀ x < inp.h, memStart x = mem₀ x)
    (hr11 : regsStart 11 = inp.prep.phiDen_dec)
    (hr17 : regsStart 17 = curH)
    (hr26 : regsStart 26 = kCard)
    (hr27 : regsStart 27 = inp.prep.cDegPtr ci)
    (hr29 : regsStart 29 = inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1) :
    Triple w p (WeightFillInv inp memStart curH ci kCard regsStart 0)
      (forUp 30 (.reg 26) buildWeightFillBody)
      (normalPost (WeightFillInv inp memStart curH ci kCard regsStart kCard))
      (fun _ => kCard * 34 + 4) := by
  have hv := hvalid.2.2.1
  rcases ce_word_bounds hvalid with ⟨h1w, hheap_w, hm_w⟩
  have hcb := comp_weight_bounds hv hci
  have hcprops := comp_props_at hv.toValid_zeroTail hci
  have hc_eq : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by simp [hci]
  have hdone := hvalid.2.2.2.2.2.2.2.2.2.1 ci hci
  dsimp only at hdone
  rw [hc_eq] at hdone hcprops
  have hdeg_list : ListAt mem₀ (inp.prep.cDegPtr ci)
      ((List.range inp.prep.rawComps[ci].2.length).map (inp.prep.cJSub inp.prep.rawComps[ci]).deg) :=
    hdone.2.2.2.2.2.2.2.2.2
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hdenom1 : 1 ≤ inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 :=
    Nat.mul_pos hpn (Nat.pow_pos (by omega))
  refine (Triple.forUp_const (r := 30) (hi := .reg 26) (body := buildWeightFillBody)
    (Inv := WeightFillInv inp memStart curH ci kCard regsStart) 25 0 kCard
    (Nat.zero_le _) h1w (fun _ => by omega)
    (fun i _ _ _ hi => hi.2.1)
    (fun i _ _ _ hi => by simp [Expr.eval, hi.2.2.1 26 (by omega), hr26]) ?_).mono_cost
      (fun _ _ => by simp [Expr.size])
  intro k _ hk st ω hkInv
  cases st with | mk m regs pos =>
  rcases hkInv with ⟨_, hk30, hregs, hbelow, htake, hzf⟩
  dsimp only at hk30 hregs hbelow htake hzf
  have hk' : k < inp.prep.rawComps[ci].2.length := hkCard ▸ hk
  have hr11' : regs 11 = inp.prep.phiDen_dec := (hregs 11 (by omega)).trans hr11
  have hr17' : regs 17 = curH := (hregs 17 (by omega)).trans hr17
  have hr27' : regs 27 = inp.prep.cDegPtr ci := (hregs 27 (by omega)).trans hr27
  have hr29' : regs 29 = inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 :=
    (hregs 29 (by omega)).trans hr29
  have hm_deg : m (inp.prep.cDegPtr ci + k) = (inp.prep.cJSub inp.prep.rawComps[ci]).deg k := by
    rw [hbelow (inp.prep.cDegPtr ci + k) (by omega), hmem_lt (inp.prep.cDegPtr ci + k) (by omega)]
    have hg := hdeg_list.getElem (by rw [List.length_map, List.length_range]; exact hk')
    simpa [List.getElem_range] using hg
  have h1m : (inp.prep.cJSub inp.prep.rawComps[ci]).deg k * inp.prep.phiDen_dec ≤
      2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec :=
    Nat.mul_le_mul_right _ (hcb.2.2.2.1 k hk').2.2
  have hdenom_le : inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 ≤
      2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec := hcb.1
  have hj2 : 2 * (2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec) ≤
      4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by linarith
  have hnum_lt : (inp.prep.cJSub inp.prep.rawComps[ci]).deg k * inp.prep.phiDen_dec +
      (inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 - 1) < 2 ^ w := by omega
  set wVal := ((inp.prep.cJSub inp.prep.rawComps[ci]).deg k * inp.prep.phiDen_dec +
    (inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 - 1)) /
    (inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1)
  have hdiv_lt : wVal < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hnum_lt
  have hwVal_eq : wVal = (inp.compWeights inp.prep.rawComps[ci])[k]'(by
      simp [compWeights]; exact hk') := by
    simp only [wVal, compWeights, List.getElem_map, List.getElem_range]
  dsimp only [buildWeightFillBody]
  refine runs_start_le ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 27) (.reg 30)))
    (by simp [Expr.eval, BinOp.eval, hr27', hk30, hm_deg, show inp.prep.cDegPtr ci + k < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (v := wVal)
    (e := .bin .div (.bin .add (.bin .mul (.reg 31) (.reg 11))
      (.bin .sub (.reg 29) (.const 1))) (.reg 29)) (by
    simp only [Expr.eval, BinOp.eval, Function.update]
    dsimp only [wVal] at hdiv_lt ⊢
    simp [hr11', hr29', h1w, show inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 - 1 < 2 ^ w by omega,
      show (inp.prep.cJSub inp.prep.rawComps[ci]).deg k * inp.prep.phiDen_dec < 2 ^ w by omega,
      hnum_lt, hdiv_lt]) ?_
  refine ⟨.normal,
    { mem := Function.update m (curH + k) wVal
      regs := Function.update (Function.update regs 31 ((inp.prep.cJSub inp.prep.rawComps[ci]).deg k))
        31 wVal
      pos := pos },
    _, runs_store_iff.mpr ⟨curH + k, wVal,
      by simp [Expr.eval, BinOp.eval, Function.update, hr17', hk30, show curH + k < 2 ^ w by omega],
      by simp [Expr.eval, Function.update], rfl, rfl, rfl⟩, ?_, by simp [Expr.size]⟩
  refine ⟨⟨by omega, by simp [Function.update],
    fun r hr => by simp [Function.update, hregs r hr, show r ≠ 30 by omega, show r ≠ 31 by omega],
    fun x hx => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hbelow x hx, ?_, ?_⟩,
    by simp [Function.update, hk30]⟩
  · have hlen_w : (inp.compWeights inp.prep.rawComps[ci]!).length = inp.prep.rawComps[ci].2.length := by
      rw [hc_eq]; simp [compWeights]
    have htake_eq : (inp.compWeights inp.prep.rawComps[ci]!).take (k + 1) =
        (inp.compWeights inp.prep.rawComps[ci]!).take k ++
          [(inp.compWeights inp.prep.rawComps[ci]!)[k]'(by omega)] :=
      List.take_succ_eq_append_getElem (by omega)
    dsimp only
    rw [htake_eq]
    intro i hi
    have hlen_t : ((inp.compWeights inp.prep.rawComps[ci]!).take k).length = k :=
      List.length_take_of_le (by omega)
    rw [List.length_append, hlen_t, List.length_singleton] at hi
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi_lt | rfl
    · rw [List.getElem_append_left (by rw [hlen_t]; exact hi_lt), Function.update_of_ne (by omega)]
      exact htake i (by rw [hlen_t]; exact hi_lt)
    · rw [List.getElem_append_right (by rw [hlen_t])]
      simp only [hlen_t, Nat.sub_self, List.getElem_singleton, Function.update_self]
      simp [hc_eq, hwVal_eq]
  · intro x hx; dsimp only; rw [Function.update_of_ne (by omega)]; exact hzf x (by omega)

end MinCostFlow.Spanner
