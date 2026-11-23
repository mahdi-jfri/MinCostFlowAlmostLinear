module

public import MinCostFlow.Spanner.ProgBuildWitnessCe

/-!
# Helpers and Level-0 Loop for Phase 3 of `buildWitnessCore` (`ProgBuildWitnessAsmHelpers`)

Provides array-flattening helpers, `buildCompsFrom` indexing/disjointness lemmas,
assembly loop invariants (`AsmJ0Inv`, `AsmCompInv`, `AsmPost`), and verification of
`buildJ0AsmBody` and its `forRange` loop.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited WitnessCoreInput

/-! ## 1. Cost definitions and array-indexing helpers -/

/-- Exact cost charged per iteration of `buildCompWEdgesBody`. -/
def asmWEdgeCost : ℕ := 110

/-- Exact cost charged per iteration of `buildCompJOrigBody`. -/
def asmJOrigCost : ℕ := 45

/-- Exact cost charged per iteration `ci` of `buildCompAsmBody`. -/
def asmCompStepCost (inp : WitnessCoreInput) (WSubs : List Graph) (ci : ℕ) : ℕ :=
  let rc := inp.prep.rawComps[ci]!
  let wm := (WSubs.getD ci ⟨0, []⟩).m
  asmWEdgeCost * wm + 9 * wm + asmJOrigCost * (inp.prep.cJSub rc).m + 9 * (inp.prep.cJSub rc).m + 100

/-- Exact total cost bound for `buildAssembleStmt`. -/
def asmTotalCost (inp : WitnessCoreInput) (WSubs : List Graph) : ℕ :=
  135 * inp.prep.j0Edges.length + 9 * inp.prep.j0Edges.length +
    rangeCost (asmCompStepCost inp WSubs) 0 inp.prep.rawComps.length +
    9 * inp.prep.rawComps.length + 120

lemma list_getElem_congr_idx {α : Type*} (l : List α) {i j : ℕ}
    (h : i = j) (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst h; rfl

lemma take_map_sum_mono (a b : ℕ) (xs : List Graph) (hab : a ≤ b) :
    ((xs.take a).map Graph.m).sum ≤ ((xs.take b).map Graph.m).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs' ih =>
    cases a with
    | zero => simp
    | succ a' =>
      cases b with
      | zero => omega
      | succ b' =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        exact Nat.add_le_add_left (ih a' b' (by omega)) _

private lemma flatMap_three_length {α : Type*} {f : α → List ℕ}
    (hlen : ∀ a, (f a).length = 3) (xs : List α) :
    (xs.flatMap f).length = 3 * xs.length := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, hlen, ih]; omega

private lemma flatMap_three_getElem {α : Type*} {f : α → List ℕ}
    (hlen : ∀ a, (f a).length = 3) (xs : List α) {idx : ℕ} (hidx : idx < (xs.flatMap f).length) :
    (xs.flatMap f)[idx]'hidx =
      (f (xs[idx / 3]'(Nat.div_lt_of_lt_mul (flatMap_three_length hlen xs ▸ hidx))))[idx % 3]'(by
        rw [hlen]; exact Nat.mod_lt _ (by decide)) := by
  induction xs generalizing idx with
  | nil => simp at hidx
  | cons a as ih =>
    simp only [List.flatMap_cons] at hidx ⊢
    by_cases h3 : idx < 3
    · rw [List.getElem_append_left (by rw [hlen]; exact h3)]
      have hdiv0 : idx / 3 = 0 := Nat.div_eq_of_lt h3
      have hmod : idx % 3 = idx := Nat.mod_eq_of_lt h3
      congr 1
      · simp [hdiv0]
      · simp [hmod]
    · have hge : (f a).length ≤ idx := by rw [hlen]; omega
      rw [List.getElem_append_right hge]
      have hsub : idx - 3 < (as.flatMap f).length := by
        have := flatMap_three_length hlen as
        simp only [List.length_append, hlen a] at hidx
        omega
      have heq_sub : (as.flatMap f)[idx - (f a).length]'(by
          simp only [List.length_append] at hidx; omega) = (as.flatMap f)[idx - 3]'hsub :=
        list_getElem_congr_idx (as.flatMap f) (by rw [hlen a]) _ hsub
      rw [heq_sub, ih hsub]
      have hdiv : idx / 3 = (idx - 3) / 3 + 1 := by omega
      have hmod : idx % 3 = (idx - 3) % 3 := by omega
      have h_el : (a :: as)[idx / 3]'(Nat.div_lt_of_lt_mul
          (flatMap_three_length hlen (a :: as) ▸ hidx)) =
          as[(idx - 3) / 3]'(Nat.div_lt_of_lt_mul (flatMap_three_length hlen as ▸ hsub)) := by
        rw [list_getElem_congr_idx (a :: as) hdiv _ (by
          have := Nat.div_lt_of_lt_mul (flatMap_three_length hlen as ▸ hsub); simp; omega)]
        rfl
      simp only [h_el, hmod]

lemma listAt_flatMap_three {α : Type*} {mem : ℕ → ℕ} {base : ℕ}
    {f : α → List ℕ} (hlen : ∀ a, (f a).length = 3) (xs : List α)
    (h : ∀ i (hi : i < xs.length) t (_ : t < 3), mem (base + 3 * i + t) = (f xs[i])[t]!) :
    ListAt mem base (xs.flatMap f) := by
  intro idx hidx
  have hlen_fm := flatMap_three_length hlen xs
  have hi : idx / 3 < xs.length := Nat.div_lt_of_lt_mul (hlen_fm ▸ hidx)
  have ht : idx % 3 < 3 := Nat.mod_lt _ (by decide)
  have hadd : base + idx = base + 3 * (idx / 3) + idx % 3 := by omega
  rw [hadd, flatMap_three_getElem hlen xs hidx]
  have hf := h (idx / 3) hi (idx % 3) ht
  simpa [List.getElem!_eq_getElem?_getD, hlen xs[idx / 3], ht] using hf

/-! ## 2. Component and level-0 structural properties -/

lemma j0Edges_props {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.prep.StaticValid mem w) :
    inp.prep.j0Edges.Nodup ∧ ∀ eJ ∈ inp.prep.j0Edges, eJ < inp.prep.J.m := by
  rcases hv with ⟨_, _, hJ0, _, hnl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hnl_len : inp.prep.nlIdx.length = inp.prep.J0_strip.m := by
    rw [hnl, hJ0]; simp [nonloopIndices, stripLoops, Graph.m]
  have hnl_nd : inp.prep.nlIdx.Nodup := by rw [hnl]; exact nonloopIndices_nodup inp.prep.J
  have h_flt : ∀ b ∈ inp.prep.decomp.edgesAt inp.prep.J0_strip 0, b < inp.prep.nlIdx.length := by
    intro b hb
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb
    omega
  have hnd : inp.prep.j0Edges.Nodup :=
    map_getD_nodup hnl_nd (List.nodup_range.filter _) h_flt
  have hlt : ∀ eJ ∈ inp.prep.j0Edges, eJ < inp.prep.J.m := by
    intro eJ heJ
    simp only [PrepInput.j0Edges, List.mem_map] at heJ
    rcases heJ with ⟨b, hb, rfl⟩
    have hb_lt := h_flt b hb
    rw [List.getD_eq_getElem _ _ hb_lt]
    have hmem : inp.prep.nlIdx[b] ∈ nonloopIndices inp.prep.J := by
      rw [← hnl]; exact List.getElem_mem hb_lt
    exact (mem_nonloopIndices.mp hmem).1
  exact ⟨hnd, hlt⟩

lemma buildCompsFrom_getElem (inp : WitnessCoreInput) :
    ∀ (off : ℕ) (raw : List (ℕ × List ℕ)) (ws : List Graph)
      (hlen : ws.length = raw.length) (j : ℕ) (hj : j < raw.length),
      let cs := inp.buildCompsFrom off raw ws
      let hj_c : j < cs.length := by rw [buildCompsFrom_length inp off raw ws hlen]; exact hj
      cs[j].wStart = off + ((ws.take j).map Graph.m).sum ∧
      cs[j].W_sub = ws[j]'(by rw [hlen]; exact hj) ∧
      cs[j].level = raw[j].1 ∧
      cs[j].X = raw[j].2.toFinset ∧
      cs[j].verts = vertsOf raw[j].2.toFinset ∧
      cs[j].J_sub = inp.prep.cJSub raw[j] ∧
      cs[j].jSubOrigEdges = inp.prep.cJOrig raw[j] ∧
      off + ((ws.take (j + 1)).map Graph.m).sum ≤ off + (ws.map Graph.m).sum := by
  intro off raw ws hlen j hj
  induction raw generalizing off ws j with
  | nil => simp at hj
  | cons p ps ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws' =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      cases j with
      | zero =>
        simp only [buildCompsFrom, List.getElem_cons_zero, List.take_zero, List.map_nil,
          List.sum_nil, add_zero, true_and]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
        refine ⟨rfl, rfl, ?_⟩
        exact Nat.add_le_add_left (Nat.le_add_right _ _) off
      | succ j' =>
        simp only [buildCompsFrom, List.getElem_cons_succ, List.take_succ_cons, List.map_cons,
          List.sum_cons]
        have hj' : j' < ps.length := by simpa using hj
        rcases ih (off + w.m) ws' hlen j' hj' with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
        exact ⟨by rw [h1]; omega, h2, h3, h4, h5, h6, h7, by omega⟩

private lemma cJOrig_preimage {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.prep.StaticValid mem w) {ci : ℕ} (hci : ci < inp.prep.rawComps.length) {eJ : ℕ}
    (heJ : eJ ∈ inp.prep.cJOrig inp.prep.rawComps[ci]) :
    ∃ (b : ℕ) (hb : b < inp.prep.J0_strip.m),
      (inp.prep.nlIdx[b]'(by
        have hnl := hv.2.2.2.2.1; have hJ0 := hv.2.2.1
        have hnl_len : inp.prep.nlIdx.length = inp.prep.J0_strip.m := by
          rw [hnl, hJ0]; simp [nonloopIndices, stripLoops, Graph.m]
        omega)) = eJ ∧
      inp.prep.decomp.level b = inp.prep.rawComps[ci].1 ∧
      (inp.prep.J0_strip.edges[b]'(by simpa [Graph.m] using hb)).1 ∈ inp.prep.rawComps[ci].2.toFinset ∧
      (inp.prep.J0_strip.edges[b]'(by simpa [Graph.m] using hb)).2 ∈ inp.prep.rawComps[ci].2.toFinset := by
  have hnl := hv.2.2.2.2.1; have hJ0 := hv.2.2.1
  have hnl_len : inp.prep.nlIdx.length = inp.prep.J0_strip.m := by
    rw [hnl, hJ0]; simp [nonloopIndices, stripLoops, Graph.m]
  simp only [PrepInput.cJOrig, List.mem_map] at heJ
  rcases heJ with ⟨a, ha, rfl⟩
  set J_i := inp.prep.decomp.graphAt inp.prep.J0_strip inp.prep.rawComps[ci].1
  have ha' := mem_insideIndices.mp ha
  have ha_len : a < (inp.prep.decomp.edgesAt inp.prep.J0_strip inp.prep.rawComps[ci].1).length := by
    simpa [J_i, DecomposeOutput.graphAt, Graph.m] using ha'.1
  set b := (inp.prep.decomp.edgesAt inp.prep.J0_strip inp.prep.rawComps[ci].1).getD a 0
  have hb_mem : b ∈ inp.prep.decomp.edgesAt inp.prep.J0_strip inp.prep.rawComps[ci].1 := by
    dsimp only [b]; rw [List.getD_eq_getElem _ _ ha_len]; exact List.getElem_mem ha_len
  simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb_mem
  have hb_m : b < inp.prep.J0_strip.m := hb_mem.1
  refine ⟨b, hb_m, ?_, hb_mem.2, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega)]
  · have hJi_eq : J_i.edges.getD a (0, 0) =
        inp.prep.J0_strip.edges[b]'(by simpa [Graph.m] using hb_m) := by
      have hba : (inp.prep.decomp.edgesAt inp.prep.J0_strip inp.prep.rawComps[ci].1)[a]'ha_len = b :=
        (List.getD_eq_getElem _ _ ha_len).symm
      simp only [J_i, DecomposeOutput.graphAt]
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using ha_len), List.getElem_map,
        hba, List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb_m)]
    rw [← hJi_eq]
    exact ha'.2

lemma cJOrig_props {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.prep.StaticValid mem w) {ci : ℕ} (hci : ci < inp.prep.rawComps.length) :
    (inp.prep.cJOrig inp.prep.rawComps[ci]).length = (inp.prep.cJSub inp.prep.rawComps[ci]).m ∧
    (inp.prep.cJOrig inp.prep.rawComps[ci]).Nodup ∧
    (∀ eJ ∈ inp.prep.cJOrig inp.prep.rawComps[ci], eJ < inp.prep.J.m) ∧
    Disjoint (inp.prep.cJOrig inp.prep.rawComps[ci]).toFinset inp.prep.j0Edges.toFinset ∧
    (∀ j, ∀ _hj : j < ci, Disjoint (inp.prep.cJOrig inp.prep.rawComps[j]).toFinset
      (inp.prep.cJOrig inp.prep.rawComps[ci]).toFinset) := by
  have hnl := hv.2.2.2.2.1; have hJ0 := hv.2.2.1
  have hnl_len : inp.prep.nlIdx.length = inp.prep.J0_strip.m := by
    rw [hnl, hJ0]; simp [nonloopIndices, stripLoops, Graph.m]
  have hnl_nd : inp.prep.nlIdx.Nodup := by rw [hnl]; exact nonloopIndices_nodup inp.prep.J
  set c := inp.prep.rawComps[ci]
  set J_i := inp.prep.decomp.graphAt inp.prep.J0_strip c.1
  have hsub_m : (inp.prep.cJSub c).m = (J_i.inside c.2.toFinset).length :=
    inducedSubgraph_m J_i c.2.toFinset
  have hlen : (inp.prep.cJOrig c).length = (inp.prep.cJSub c).m := by
    simp only [PrepInput.cJOrig, List.length_map]
    rw [hsub_m, ← insideIndices_map_eq_inside J_i c.2.toFinset, List.length_map]
  have hed_len : (inp.prep.decomp.edgesAt inp.prep.J0_strip c.1).length = J_i.m := by
    simp [J_i, DecomposeOutput.graphAt, Graph.m]
  have hidx_lt : ∀ a ∈ insideIndices J_i c.2.toFinset,
      a < (inp.prep.decomp.edgesAt inp.prep.J0_strip c.1).length := fun a ha => by
    rw [hed_len]; exact (mem_insideIndices.mp ha).1
  have hed_lt : ∀ b ∈ inp.prep.decomp.edgesAt inp.prep.J0_strip c.1, b < inp.prep.nlIdx.length := by
    intro b hb
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb
    omega
  have hnd : (inp.prep.cJOrig c).Nodup := by
    have hcomp : inp.prep.cJOrig c =
        ((insideIndices J_i c.2.toFinset).map fun a =>
          (inp.prep.decomp.edgesAt inp.prep.J0_strip c.1).getD a 0).map
          fun b => inp.prep.nlIdx.getD b 0 := by
      rw [PrepInput.cJOrig, List.map_map]; rfl
    rw [hcomp]
    refine map_getD_nodup hnl_nd (map_getD_nodup (List.nodup_range.filter _)
      (insideIndices_nodup J_i c.2.toFinset) hidx_lt) fun j hj => ?_
    rcases List.mem_map.mp hj with ⟨a, ha, rfl⟩
    have ha' := hidx_lt a ha
    rw [List.getD_eq_getElem _ _ ha']
    exact hed_lt _ (List.getElem_mem ha')
  have hlt : ∀ eJ ∈ inp.prep.cJOrig c, eJ < inp.prep.J.m := by
    intro eJ heJ
    rcases cJOrig_preimage hv hci heJ with ⟨b, hb, rfl, _⟩
    have hmem : inp.prep.nlIdx[b] ∈ nonloopIndices inp.prep.J := by
      rw [← hnl]; exact List.getElem_mem (by omega)
    exact (mem_nonloopIndices.mp hmem).1
  have hdisj_j0 : Disjoint (inp.prep.cJOrig c).toFinset inp.prep.j0Edges.toFinset := by
    rw [Finset.disjoint_left]
    intro eJ he1 he2
    rw [List.mem_toFinset] at he1
    rcases cJOrig_preimage hv hci he1 with ⟨b₁, _, hb1_eq, hb1_lvl, _⟩
    simp only [List.mem_toFinset, PrepInput.j0Edges, List.mem_map] at he2
    rcases he2 with ⟨b₂, hb2, hb2_eq⟩
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb2
    rw [List.getD_eq_getElem _ _ (by omega)] at hb2_eq
    have hb_eq : b₁ = b₂ := (hnl_nd.getElem_inj_iff).mp (hb1_eq.trans hb2_eq.symm)
    subst hb_eq
    have hc_ge : 1 ≤ c.1 := (hv.2.2.2.2.2.2.2.2.2.2.2.1 c (List.getElem_mem hci)).1
    have h0 : inp.prep.decomp.level b₁ = 0 := hb2.2
    rw [hb1_lvl] at h0
    dsimp only [c] at hc_ge h0
    omega
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  have hprops_rc := hv.2.2.2.2.2.2.2.2.2.2.2.1
  have hdp_rc := hv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hraw_eq : inp.prep.rawComps.map (fun p => (p.1, p.2.toFinset)) =
      (List.range inp.prep.d_ℓ).flatMap fun i' =>
        (inp.prep.decomp.comps (i' + 1)).map fun X => (i' + 1, X) :=
    (mkDecomposeOutput_rawComps_eq inp.prep.d_ℓ inp.prep.level inp.prep.rawComps hpw_rc fun p hp =>
      ⟨(hprops_rc p hp).1, (hprops_rc p hp).2.1⟩).symm
  have hp_raw : (inp.prep.rawComps.map (fun p => (p.1, p.2.toFinset))).Pairwise
      (fun a b => a.1 ≠ b.1 ∨ Disjoint a.2 b.2) := by
    rw [hraw_eq]
    exact rawComps_pairwise (fun i hi0 hiℓ => (hdp_rc.2.2.2 i hi0 hiℓ).1)
  have hdisj_prev : ∀ j (_hj : j < ci), Disjoint (inp.prep.cJOrig inp.prep.rawComps[j]).toFinset
      (inp.prep.cJOrig c).toFinset := by
    intro j hj
    rw [Finset.disjoint_left]
    intro eJ he1 he2
    rw [List.mem_toFinset] at he1 he2
    rcases cJOrig_preimage hv (lt_trans hj hci) he1 with ⟨b₁, _, hb1_eq, hb1_lvl, hb1X, _⟩
    rcases cJOrig_preimage hv hci he2 with ⟨b₂, _, hb2_eq, hb2_lvl, hb2X, _⟩
    have hb_eq : b₁ = b₂ := (hnl_nd.getElem_inj_iff).mp (hb1_eq.trans hb2_eq.symm)
    subst hb_eq
    have hrel := List.pairwise_iff_getElem.mp hp_raw j ci (by simp; omega) (by simp; exact hci) hj
    simp only [List.getElem_map] at hrel
    rcases hrel with hne | hdisj
    · exact hne (hb1_lvl.symm.trans hb2_lvl)
    · exact Finset.disjoint_left.mp hdisj hb1X hb2X
  exact ⟨hlen, hnd, hlt, hdisj_j0, hdisj_prev⟩

/-! ## 3. Assembly invariants and level-0 assembly verification -/

/-- Partial state after writing `kDone` edges of `j0Edges` in `buildJ0AsmBody`. -/
def AsmJ0Inv (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (WSubs : List Graph) (aCompExt wAddr : ℕ) (kDone : ℕ) (st : State) : Prop :=
  let wd := inp.mkWitnessData ce pds WSubs
  let Wm := wd.W.m
  let wWNumAddr := wAddr + (2 + 2 * Wm)
  let wSrcAddr := wWNumAddr + Wm
  let jSrcAddr := wSrcAddr + 3 * Wm
  let hEnd := jSrcAddr + 3 * inp.prep.J.m
  kDone ≤ inp.prep.j0Edges.length ∧
  CeBaseInv inp ce pds mem₀ st ∧
  st.regs 18 = aCompExt ∧ st.regs 23 = Wm ∧ st.regs 24 = wAddr ∧
  st.regs 25 = wWNumAddr ∧ st.regs 26 = wSrcAddr ∧ st.regs 27 = jSrcAddr ∧
  st.regs 28 = hEnd ∧ st.regs 29 = kDone ∧
  inp.ValidWSubs ce WSubs ∧
  aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr ∧
  hEnd ≤ inp.maxHeapEnd ce pds ∧
  CompExtAt st.mem aCompExt inp.prep.phiNum_dec wAddr wd.comps ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  WitnessHdr0 st.mem inp ce pds ∧
  st.mem (inp.h + 12) = aCompExt ∧ st.mem (inp.h + 13) = wAddr ∧
  st.mem (inp.h + 14) = wWNumAddr ∧ st.mem (inp.h + 15) = wSrcAddr ∧
  st.mem (inp.h + 16) = jSrcAddr ∧
  st.mem wAddr = inp.prep.J.n ∧ st.mem (wAddr + 1) = Wm ∧
  (∀ k < kDone,
    let eJ := inp.prep.j0Edges[k]!
    let edge := inp.prep.J.edges[eJ]!
    st.mem (wAddr + 2 + 2 * k) = edge.1 ∧ st.mem (wAddr + 3 + 2 * k) = edge.2 ∧
    st.mem (wWNumAddr + k) = inp.prep.phiNum_dec ∧
    st.mem (wSrcAddr + 3 * k) = 0 ∧ st.mem (wSrcAddr + 3 * k + 1) = eJ ∧
    st.mem (wSrcAddr + 3 * k + 2) = 0 ∧
    st.mem (jSrcAddr + 3 * eJ) = 1 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = k ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = 0) ∧
  (∀ k, kDone ≤ k → k < Wm →
    st.mem (wAddr + 2 + 2 * k) = 0 ∧ st.mem (wAddr + 3 + 2 * k) = 0 ∧
    st.mem (wWNumAddr + k) = 0 ∧ (∀ t < 3, st.mem (wSrcAddr + 3 * k + t) = 0)) ∧
  (∀ eJ < inp.prep.J.m, eJ ∉ inp.prep.j0Edges.take kDone →
    ∀ t < 3, st.mem (jSrcAddr + 3 * eJ + t) = 0) ∧
  ZeroFrom st.mem hEnd

/-- Partial state after finishing components `< ciDone` in `buildCompAsmBody`. -/
def AsmCompInv (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (WSubs : List Graph) (aCompExt wAddr : ℕ) (ciDone : ℕ) (st : State) : Prop :=
  let wd := inp.mkWitnessData ce pds WSubs
  let Wm := wd.W.m
  let wWNumAddr := wAddr + (2 + 2 * Wm)
  let wSrcAddr := wWNumAddr + Wm
  let jSrcAddr := wSrcAddr + 3 * Wm
  let hEnd := jSrcAddr + 3 * inp.prep.J.m
  let wDone := inp.prep.j0Edges.length + ((WSubs.take ciDone).map Graph.m).sum
  ciDone ≤ inp.prep.rawComps.length ∧
  CeBaseInv inp ce pds mem₀ st ∧
  st.regs 18 = aCompExt ∧ st.regs 23 = Wm ∧ st.regs 24 = wAddr ∧
  st.regs 25 = wWNumAddr ∧ st.regs 26 = wSrcAddr ∧ st.regs 27 = jSrcAddr ∧
  st.regs 28 = hEnd ∧ st.regs 29 = ciDone ∧
  inp.ValidWSubs ce WSubs ∧
  aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr ∧
  hEnd ≤ inp.maxHeapEnd ce pds ∧
  CompExtAt st.mem aCompExt inp.prep.phiNum_dec wAddr wd.comps ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  WitnessHdr0 st.mem inp ce pds ∧
  st.mem (inp.h + 12) = aCompExt ∧ st.mem (inp.h + 13) = wAddr ∧
  st.mem (inp.h + 14) = wWNumAddr ∧ st.mem (inp.h + 15) = wSrcAddr ∧
  st.mem (inp.h + 16) = jSrcAddr ∧
  st.mem wAddr = inp.prep.J.n ∧ st.mem (wAddr + 1) = Wm ∧
  (∀ k < inp.prep.j0Edges.length,
    let eJ := inp.prep.j0Edges[k]!
    let edge := inp.prep.J.edges[eJ]!
    st.mem (wAddr + 2 + 2 * k) = edge.1 ∧ st.mem (wAddr + 3 + 2 * k) = edge.2 ∧
    st.mem (wWNumAddr + k) = inp.prep.phiNum_dec ∧
    st.mem (wSrcAddr + 3 * k) = 0 ∧ st.mem (wSrcAddr + 3 * k + 1) = eJ ∧
    st.mem (wSrcAddr + 3 * k + 2) = 0 ∧
    st.mem (jSrcAddr + 3 * eJ) = 1 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = k ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = 0) ∧
  (∀ (j : ℕ) (_hj : j < ciDone) (eL : ℕ)
      (_heL : eL < (wd.comps.getD j defaultCompInfo).W_sub.m),
    let comp := wd.comps.getD j defaultCompInfo
    let wIdx := comp.wStart + eL
    let eW := comp.W_sub.edges[eL]!
    st.mem (wAddr + 2 + 2 * wIdx) = comp.verts[eW.1]! ∧
    st.mem (wAddr + 3 + 2 * wIdx) = comp.verts[eW.2]! ∧
    st.mem (wWNumAddr + wIdx) = inp.prep.phiNum_dec * 2 ^ comp.level ∧
    st.mem (wSrcAddr + 3 * wIdx) = 1 ∧ st.mem (wSrcAddr + 3 * wIdx + 1) = j ∧
    st.mem (wSrcAddr + 3 * wIdx + 2) = eL) ∧
  (∀ (j : ℕ) (_hj : j < ciDone) (jL : ℕ)
      (_hjL : jL < (wd.comps.getD j defaultCompInfo).J_sub.m),
    let comp := wd.comps.getD j defaultCompInfo
    let eJ := comp.jSubOrigEdges[jL]!
    st.mem (jSrcAddr + 3 * eJ) = 2 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = j ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = jL) ∧
  (∀ k, wDone ≤ k → k < Wm →
    st.mem (wAddr + 2 + 2 * k) = 0 ∧ st.mem (wAddr + 3 + 2 * k) = 0 ∧
    st.mem (wWNumAddr + k) = 0 ∧ (∀ t < 3, st.mem (wSrcAddr + 3 * k + t) = 0)) ∧
  (∀ eJ < inp.prep.J.m,
    eJ ∉ inp.prep.j0Edges →
    (∀ j < ciDone, eJ ∉ (wd.comps.getD j defaultCompInfo).jSubOrigEdges) →
    ∀ t < 3, st.mem (jSrcAddr + 3 * eJ + t) = 0) ∧
  ZeroFrom st.mem hEnd

/-- Final postcondition of `buildAssembleStmt` (right before `.ret (.reg 28)`). -/
def AsmPost (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (st : State) : Prop :=
  ∃ (aCompExt wAddr : ℕ) (WSubs : List Graph),
    let wd := inp.mkWitnessData ce pds WSubs
    let Wm := wd.W.m
    let wWNumAddr := wAddr + (2 + 2 * Wm)
    let wSrcAddr := wWNumAddr + Wm
    let jSrcAddr := wSrcAddr + 3 * Wm
    let hEnd := jSrcAddr + 3 * inp.prep.J.m
    st.regs 28 = hEnd ∧
    inp.ValidWSubs ce WSubs ∧
    aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr ∧
    hEnd ≤ inp.maxHeapEnd ce pds ∧
    (∀ x < inp.h, st.mem x = mem₀ x) ∧
    WitnessHdr0 st.mem inp ce pds ∧
    st.mem (inp.h + 12) = aCompExt ∧ st.mem (inp.h + 13) = wAddr ∧
    st.mem (inp.h + 14) = wWNumAddr ∧ st.mem (inp.h + 15) = wSrcAddr ∧
    st.mem (inp.h + 16) = jSrcAddr ∧
    GraphAt st.mem wAddr wd.W ∧
    (∀ k < inp.prep.j0Edges.length, st.mem (wWNumAddr + k) = inp.prep.phiNum_dec) ∧
    (∀ (j : ℕ) (_ : j < wd.comps.length) (eL : ℕ)
        (_ : eL < (wd.comps.getD j defaultCompInfo).W_sub.m),
      st.mem (wWNumAddr + (wd.comps.getD j defaultCompInfo).wStart + eL) =
        inp.prep.phiNum_dec * 2 ^ (wd.comps.getD j defaultCompInfo).level) ∧
    WSourcesAt st.mem wSrcAddr wd.wSources ∧
    JSourcesAt st.mem jSrcAddr wd.jSources ∧
    CompExtAt st.mem aCompExt inp.prep.phiNum_dec wAddr wd.comps ∧
    ZeroFrom st.mem hEnd

lemma asm_preserves_static {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ m m' : ℕ → ℕ}
    {wAddr aCompExt wWNumAddr wSrcAddr jSrcAddr : ℕ}
    (hhdr0 : WitnessHdr0 m inp ce pds) (h12 : m (inp.h + 12) = aCompExt)
    (h13 : m (inp.h + 13) = wAddr) (h14 : m (inp.h + 14) = wWNumAddr)
    (h15 : m (inp.h + 15) = wSrcAddr) (h16 : m (inp.h + 16) = jSrcAddr)
    (hbelow : ∀ x < inp.h, m x = mem₀ x)
    (ha_lo : inp.h + 20 ≤ aCompExt) (ha_ext : aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr)
    (hm_agree : ∀ x < wAddr, m' x = m x) :
    (∀ x < inp.h, m' x = mem₀ x) ∧ WitnessHdr0 m' inp ce pds ∧
    m' (inp.h + 12) = aCompExt ∧ m' (inp.h + 13) = wAddr ∧
    m' (inp.h + 14) = wWNumAddr ∧ m' (inp.h + 15) = wSrcAddr ∧ m' (inp.h + 16) = jSrcAddr := by
  refine ⟨fun x hx => (hm_agree x (by omega)).trans (hbelow x hx),
    witnessHdr0_of_agree_below hhdr0 (by omega) hm_agree,
    (hm_agree _ (by omega)).trans h12, (hm_agree _ (by omega)).trans h13,
    (hm_agree _ (by omega)).trans h14, (hm_agree _ (by omega)).trans h15,
    (hm_agree _ (by omega)).trans h16⟩

lemma ceBaseInv_of_agree {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ m' : ℕ → ℕ} {aCompExt wAddr : ℕ} {st : State}
    (hbase : CeBaseInv inp ce pds mem₀ st) (hr18 : st.regs 18 = aCompExt)
    (ha_ext : aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr)
    (hm_agree : ∀ x < wAddr, m' x = st.mem x) {regs' : ℕ → ℕ}
    (hregs : ∀ r ≤ 18, regs' r = st.regs r) :
    CeBaseInv inp ce pds mem₀ ⟨m', regs', st.pos⟩ := by
  rcases hbase with ⟨h0, h4, h5, h6, h10, h11, h12, h13, h14, h15, h16, h18m, ha_lo, ha_hi, hbelow, hhdr0⟩
  have ha_lo' : inp.h + 20 ≤ regs' 18 := by rw [hregs 18 (by omega)]; exact ha_lo
  have ha_hi' : regs' 18 ≤ inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
      pds.boundsSpace (dWInt ce) (inp.mwInt ce) := by
    rw [hregs 18 (by omega)]; exact ha_hi
  refine ⟨(hregs 0 (by omega)).trans h0, (hregs 4 (by omega)).trans h4,
    (hregs 5 (by omega)).trans h5, (hregs 6 (by omega)).trans h6,
    (hregs 10 (by omega)).trans h10, (hregs 11 (by omega)).trans h11,
    (hregs 12 (by omega)).trans h12, (hregs 13 (by omega)).trans h13,
    (hregs 14 (by omega)).trans h14, (hregs 15 (by omega)).trans h15,
    (hregs 16 (by omega)).trans h16, ?_, ha_lo', ha_hi',
    fun x hx => (hm_agree x (by omega)).trans (hbelow x hx),
    witnessHdr0_of_agree_below hhdr0 (by omega) hm_agree⟩
  dsimp only
  rw [hregs 18 (by omega), hm_agree _ (by omega)]; exact h18m

lemma compExtAt_of_agree_below {m m' : ℕ → ℕ} {aCompExt phiNum_dec wAddr : ℕ}
    {comps : List CompInfo} (hce : CompExtAt m aCompExt phiNum_dec wAddr comps)
    (hm_agree : ∀ x < wAddr, m' x = m x) :
    CompExtAt m' aCompExt phiNum_dec wAddr comps := by
  intro j hj
  have hc := hce j hj
  rcases hc with ⟨h0, h2, h3, h4, h5, hg, hlo, hhi⟩
  refine ⟨(hm_agree _ (by omega)).trans h0, (hm_agree _ (by omega)).trans h2,
    (hm_agree _ (by omega)).trans h3, (hm_agree _ (by omega)).trans h4,
    (hm_agree _ (by omega)).trans h5, ?_, by rw [hm_agree _ (by omega)]; exact hlo,
    by rw [hm_agree _ (by omega)]; exact hhi⟩
  rw [hm_agree _ (by omega)]
  exact GraphAt.of_agree_below hg (show _ ≤ wAddr by rw [graph_encode_length]; exact hhi)
    fun x hx => hm_agree x hx

private lemma j0_updates_agree {m m' : ℕ → ℕ} (wAddr Wm k eJ : ℕ)
    (hm_out : ∀ x,
      x ≠ wAddr + (2 + 2 * k) → x ≠ wAddr + (3 + 2 * k) → x ≠ wAddr + (2 + 2 * Wm) + k →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + 3 * k →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + (3 * k + 1) →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + (3 * k + 2) →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + 3 * eJ →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + (3 * eJ + 1) →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + (3 * eJ + 2) →
      m' x = m x)
    (hk_wm : k < Wm) :
    (∀ x < wAddr + 2, m' x = m x) ∧
    (∀ k', k' ≠ k → k' < Wm →
      m' (wAddr + 2 + 2 * k') = m (wAddr + 2 + 2 * k') ∧
      m' (wAddr + 3 + 2 * k') = m (wAddr + 3 + 2 * k') ∧
      m' (wAddr + (2 + 2 * Wm) + k') = m (wAddr + (2 + 2 * Wm) + k') ∧
      (∀ t < 3, m' (wAddr + (2 + 2 * Wm) + Wm + 3 * k' + t) =
        m (wAddr + (2 + 2 * Wm) + Wm + 3 * k' + t))) ∧
    (∀ eJ', eJ' ≠ eJ → ∀ t < 3,
      m' (wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + 3 * eJ' + t) =
        m (wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + 3 * eJ' + t)) ∧
    (∀ Jm x, wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + 3 * Jm ≤ x → eJ < Jm → m' x = m x) := by
  refine ⟨fun x hx => hm_out x (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega),
    fun k' hne hlt =>
      ⟨hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       fun t ht => hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩,
    fun eJ' hne t ht =>
      hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    fun Jm x hx hej =>
      hm_out x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

private lemma j0_writes_cell (m : ℕ → ℕ) (wAddr Wm k eJ u v phiNum : ℕ) (hk_wm : k < Wm) :
    let wWNumAddr := wAddr + (2 + 2 * Wm)
    let wSrcAddr := wWNumAddr + Wm
    let jSrcAddr := wSrcAddr + 3 * Wm
    let m_prev := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update m (wAddr + (2 + 2 * k)) u)
        (wAddr + (3 + 2 * k)) v)
        (wWNumAddr + k) phiNum)
        (wSrcAddr + 3 * k) 0)
        (wSrcAddr + (3 * k + 1)) eJ)
        (wSrcAddr + (3 * k + 2)) 0)
        (jSrcAddr + 3 * eJ) 1)
        (jSrcAddr + (3 * eJ + 1)) k
    let m1 := Function.update m_prev (jSrcAddr + (3 * eJ + 2)) 0
    m1 (wAddr + 2 + 2 * k) = u ∧ m1 (wAddr + 3 + 2 * k) = v ∧
    m1 (wWNumAddr + k) = phiNum ∧ m1 (wSrcAddr + 3 * k) = 0 ∧
    m1 (wSrcAddr + 3 * k + 1) = eJ ∧ m1 (wSrcAddr + 3 * k + 2) = 0 ∧
    m1 (jSrcAddr + 3 * eJ) = 1 ∧ m1 (jSrcAddr + 3 * eJ + 1) = k ∧
    m1 (jSrcAddr + 3 * eJ + 2) = 0 := by
  intro wWNumAddr wSrcAddr jSrcAddr m_prev m1
  dsimp only [m1, m_prev]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      show wAddr + 2 + 2 * k = wAddr + (2 + 2 * k) by omega, Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      show wAddr + 3 + 2 * k = wAddr + (3 + 2 * k) by omega, Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      show wSrcAddr + 3 * k + 1 = wSrcAddr + (3 * k + 1) by omega, Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      show wSrcAddr + 3 * k + 2 = wSrcAddr + (3 * k + 2) by omega, Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · rw [Function.update_of_ne (by omega),
      show jSrcAddr + 3 * eJ + 1 = jSrcAddr + (3 * eJ + 1) by omega, Function.update_self]
  · rw [show jSrcAddr + 3 * eJ + 2 = jSrcAddr + (3 * eJ + 2) by omega, Function.update_self]

private theorem buildJ0AsmBody_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr k : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) :
    Triple w p
      (fun st => AsmJ0Inv inp ce pds mem₀ WSubs aCompExt wAddr k st ∧ k < inp.prep.j0Edges.length)
      buildJ0AsmBody
      (normalPost fun st =>
        AsmJ0Inv inp ce pds mem₀ WSubs aCompExt wAddr (k + 1)
          { st with regs := Function.update st.regs 29 (k + 1) } ∧ st.regs 29 = k)
      (fun _ => 135) := by
  intro st ω ⟨hinv, hk⟩
  cases st with | mk m regs pos =>
  rcases hinv with ⟨_, hbase, hr18, hr23, hr24, hr25, hr26, hr27, hr28, hr29,
    hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16,
    hm_n, hm_m, hprev, hzero_w, hzero_j, hzf⟩
  dsimp only at hr18 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hcomp_ext hbelow hhdr0
  rcases ce_word_bounds hvalid with ⟨h1w, hheap_w, hm_w⟩
  rcases hvalid.2.2.1 with ⟨hJ, hgJ, hJ0, _, _, _, _, _, hpn, hpnd, _, _, _, hjle, _, _, _, _, _, hwb⟩
  have hj0p := j0Edges_props hvalid.2.2.1
  set wd := inp.mkWitnessData ce pds WSubs
  set Wm := wd.W.m
  set wWNumAddr := wAddr + (2 + 2 * Wm)
  set wSrcAddr := wWNumAddr + Wm
  set jSrcAddr := wSrcAddr + 3 * Wm
  set hEnd := jSrcAddr + 3 * inp.prep.J.m
  have hk_wm : k < Wm := by
    change k < wd.W.m
    rw [mkWitnessData_W_m_eq_sum inp ce pds hws.1]; omega
  have h_in_lt := inp.input_reads_lt_h hvalid
  have hEnd_lt_w : hEnd < 2 ^ w := lt_of_le_of_lt hmax_le hheap_w
  have hr0 : regs 0 = inp.prep.jAddr := hbase.1
  have hr10 : regs 10 = inp.prep.phiNum_dec := hbase.2.2.2.2.1
  have hr13 : regs 13 = inp.prep.aJ0Out := hbase.2.2.2.2.2.2.2.1
  have ha_lo : inp.h + 20 ≤ aCompExt := by
    rw [← hr18]; exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hj0_at : ListAt m inp.prep.aJ0Out inp.prep.j0Edges := by
    refine listAt_of_congr hvalid.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1 fun i hi => hbelow _ ?_
    have := h_in_lt.2.2.2.2.1; omega
  have heJ_val : m (inp.prep.aJ0Out + k) = inp.prep.j0Edges[k] := hj0_at k hk
  set eJ := inp.prep.j0Edges[k]
  have heJ_eq : inp.prep.j0Edges[k]! = eJ := by simp [eJ, hk]
  have heJ_lt_m : eJ < inp.prep.J.m := hj0p.2 eJ (List.getElem_mem hk)
  have hj_le_h : inp.prep.jAddr + inp.prep.J.encode.length ≤ inp.h :=
    le_trans hjle (by have := h_in_lt.2.2.2.1; omega)
  have hJ_at : GraphAt m inp.prep.jAddr inp.prep.J :=
    GraphAt.of_agree_below hgJ hj_le_h fun x hx => hbelow x hx
  have hJ_u : m (inp.prep.jAddr + (2 + 2 * eJ)) = inp.prep.J.edges[eJ].1 := by
    simpa [Nat.add_assoc] using graphAt_edge_fst hJ_at heJ_lt_m
  have hJ_v : m (inp.prep.jAddr + (3 + 2 * eJ)) = inp.prep.J.edges[eJ].2 := by
    have hs := graphAt_edge_snd hJ_at heJ_lt_m
    simpa [show inp.prep.jAddr + 3 + 2 * eJ = inp.prep.jAddr + (3 + 2 * eJ) by omega] using hs
  have hJn_lt_w : inp.prep.J.n < 2 ^ w := by
    have h1 : inp.prep.J.n ≤ inp.prep.h + 9 + inp.prep.d_ℓ + 16 * inp.prep.J0_strip.m + 2 * inp.prep.J.n := by omega
    exact lt_of_le_of_lt h1 hwb
  have hu_lt_w : inp.prep.J.edges[eJ].1 < 2 ^ w :=
    lt_trans (hJ _ (List.getElem_mem heJ_lt_m)).1 hJn_lt_w
  have hv_lt_w : inp.prep.J.edges[eJ].2 < 2 ^ w :=
    lt_trans (hJ _ (List.getElem_mem heJ_lt_m)).2 hJn_lt_w
  have hphi_lt_w : inp.prep.phiNum_dec < 2 ^ w := by
    have hpd1 : inp.prep.phiNum_dec ≤ 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
      nlinarith only [hpn, hpnd]
    exact lt_of_le_of_lt hpd1 (by omega)
  dsimp only [buildJ0AsmBody]
  refine runs_start_le ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 13) (.reg 29)))
    (by simp [Expr.eval, BinOp.eval, hr13, hr29, show inp.prep.aJ0Out + k < 2 ^ w by omega,
      heJ_val]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 30)))))
    (by simp [Expr.eval, BinOp.eval, Function.update, hr0, show 2 < 2 ^ w by omega,
      show 2 * eJ < 2 ^ w by omega, show 2 + 2 * eJ < 2 ^ w by omega,
      show inp.prep.jAddr + (2 + 2 * eJ) < 2 ^ w by omega, hJ_u]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 30)))))
    (by simp [Expr.eval, BinOp.eval, Function.update, hr0, show 2 < 2 ^ w by omega,
      show 3 < 2 ^ w by omega, show 2 * eJ < 2 ^ w by omega, show 3 + 2 * eJ < 2 ^ w by omega,
      show inp.prep.jAddr + (3 + 2 * eJ) < 2 ^ w by omega, hJ_v]; rfl) ?_
  refine runs_seq_store_flat
    (ea := .bin .add (.reg 24) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 29))))
    (ev := .reg 31)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr24, hr29, show 2 < 2 ^ w by omega,
      show 2 * k < 2 ^ w by omega, show 2 + 2 * k < 2 ^ w by omega,
      show wAddr + (2 + 2 * k) < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update]; rfl) ?_
  refine runs_seq_store_flat
    (ea := .bin .add (.reg 24) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 29))))
    (ev := .reg 32)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr24, hr29, show 2 < 2 ^ w by omega,
      show 3 < 2 ^ w by omega, show 2 * k < 2 ^ w by omega, show 3 + 2 * k < 2 ^ w by omega,
      show wAddr + (3 + 2 * k) < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 25) (.reg 29)) (ev := .reg 10)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr25, hr29,
      show wWNumAddr + k < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update, hr10]; rfl) ?_
  refine runs_seq_store_flat
    (ea := .bin .add (.reg 26) (.bin .mul (.const 3) (.reg 29))) (ev := .const 0)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr26, hr29, show 3 < 2 ^ w by omega,
      show 3 * k < 2 ^ w by omega, show wSrcAddr + 3 * k < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, show 0 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_store_flat
    (ea := .bin .add (.reg 26) (.bin .add (.bin .mul (.const 3) (.reg 29)) (.const 1)))
    (ev := .reg 30)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr26, hr29, h1w, show 3 < 2 ^ w by omega,
      show 3 * k < 2 ^ w by omega, show 3 * k + 1 < 2 ^ w by omega,
      show wSrcAddr + (3 * k + 1) < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update]; rfl) ?_
  refine runs_seq_store_flat
    (ea := .bin .add (.reg 26) (.bin .add (.bin .mul (.const 3) (.reg 29)) (.const 2)))
    (ev := .const 0)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr26, hr29, show 2 < 2 ^ w by omega,
      show 3 < 2 ^ w by omega, show 3 * k < 2 ^ w by omega, show 3 * k + 2 < 2 ^ w by omega,
      show wSrcAddr + (3 * k + 2) < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, show 0 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_store_flat
    (ea := .bin .add (.reg 27) (.bin .mul (.const 3) (.reg 30))) (ev := .const 1)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr27, show 3 < 2 ^ w by omega,
      show 3 * eJ < 2 ^ w by omega, show jSrcAddr + 3 * eJ < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, h1w]; rfl) ?_
  refine runs_seq_store_flat
    (ea := .bin .add (.reg 27) (.bin .add (.bin .mul (.const 3) (.reg 30)) (.const 1)))
    (ev := .reg 29)
    (by simp [Expr.eval, BinOp.eval, Function.update, hr27, h1w, show 3 < 2 ^ w by omega,
      show 3 * eJ < 2 ^ w by omega, show 3 * eJ + 1 < 2 ^ w by omega,
      show jSrcAddr + (3 * eJ + 1) < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update, hr29]; rfl) ?_
  set m_prev := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update m
      (wAddr + (2 + 2 * k)) inp.prep.J.edges[eJ].1)
      (wAddr + (3 + 2 * k)) inp.prep.J.edges[eJ].2)
      (wWNumAddr + k) inp.prep.phiNum_dec)
      (wSrcAddr + 3 * k) 0)
      (wSrcAddr + (3 * k + 1)) eJ)
      (wSrcAddr + (3 * k + 2)) 0)
      (jSrcAddr + 3 * eJ) 1)
      (jSrcAddr + (3 * eJ + 1)) k
  set m' := Function.update m_prev (jSrcAddr + (3 * eJ + 2)) 0
  set regs' := Function.update (Function.update (Function.update regs 30 eJ)
    31 inp.prep.J.edges[eJ].1) 32 inp.prep.J.edges[eJ].2
  refine ⟨.normal, ⟨m', regs', pos⟩, _,
    runs_store_iff.mpr ⟨jSrcAddr + (3 * eJ + 2), 0,
      by dsimp only [regs']; simp [Expr.eval, BinOp.eval, Function.update, hr27, show 2 < 2 ^ w by omega,
        show 3 < 2 ^ w by omega, show 3 * eJ < 2 ^ w by omega, show 3 * eJ + 2 < 2 ^ w by omega,
        show jSrcAddr + (3 * eJ + 2) < 2 ^ w by omega],
      by simp [Expr.eval, show 0 < 2 ^ w by omega],
      rfl, rfl, rfl⟩,
    ?_, by norm_num [Expr.size]⟩
  have hm_out : ∀ x,
      x ≠ wAddr + (2 + 2 * k) → x ≠ wAddr + (3 + 2 * k) → x ≠ wWNumAddr + k →
      x ≠ wSrcAddr + 3 * k → x ≠ wSrcAddr + (3 * k + 1) → x ≠ wSrcAddr + (3 * k + 2) →
      x ≠ jSrcAddr + 3 * eJ → x ≠ jSrcAddr + (3 * eJ + 1) → x ≠ jSrcAddr + (3 * eJ + 2) →
      m' x = m x := by
    intro x h1 h2 h3 h4 h5 h6 h7 h8 h9
    dsimp only [m', m_prev]
    rw [Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7,
      Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
      Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  rcases j0_updates_agree wAddr Wm k eJ hm_out hk_wm with
    ⟨hm_below_w, hm_k_ne, hm_jSrc_ne, hm_zf⟩
  have hm_below_w0 : ∀ x < wAddr, m' x = m x :=
    fun x hx => hm_below_w x (Nat.lt_trans hx (Nat.lt_succ_of_lt (Nat.lt_succ_self wAddr)))
  have hst_stat := asm_preserves_static hhdr0 hm12 hm13 hm14 hm15 hm16 hbelow ha_lo ha_ext hm_below_w0
  have hr_28 : ∀ r ≤ 28, Function.update regs' 29 (k + 1) r = regs r := by
    intro r hr; dsimp only [regs']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hj0_nodup := hj0p.1
  have hr_18 : ∀ r ≤ 18, Function.update regs' 29 (k + 1) r = regs r :=
    fun r hr => hr_28 r (Nat.le_trans hr (by decide))
  refine ⟨?_, ?_⟩
  · unfold AsmJ0Inv
    dsimp only
    refine ⟨hk, @ceBaseInv_of_agree inp ce pds mem₀ m' aCompExt wAddr ⟨m, regs, pos⟩
        hbase hr18 ha_ext hm_below_w0 (Function.update regs' 29 (k + 1)) hr_18,
      (hr_28 18 (by decide)).trans hr18, (hr_28 23 (by decide)).trans hr23,
      (hr_28 24 (by decide)).trans hr24, (hr_28 25 (by decide)).trans hr25,
      (hr_28 26 (by decide)).trans hr26, (hr_28 27 (by decide)).trans hr27,
      (hr_28 28 (by decide)).trans hr28, by rw [Function.update_self],
      hws, ha_ext, hmax_le,
      compExtAt_of_agree_below hcomp_ext hm_below_w0,
      hst_stat.1, hst_stat.2.1, hst_stat.2.2.1, hst_stat.2.2.2.1, hst_stat.2.2.2.2.1,
      hst_stat.2.2.2.2.2.1, hst_stat.2.2.2.2.2.2,
      (hm_below_w wAddr (Nat.lt_succ_of_lt (Nat.lt_succ_self wAddr))).trans hm_n,
      (hm_below_w (wAddr + 1) (Nat.lt_succ_self (wAddr + 1))).trans hm_m,
      ?_, ?_, ?_, fun x hx => (hm_zf inp.prep.J.m x hx heJ_lt_m).trans (hzf x hx)⟩
    · intro k' hk'
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk') with hk_lt | hkk
      · have hp := hprev k' hk_lt
        dsimp only at hp ⊢
        set eJ' := inp.prep.j0Edges[k']!
        have hne_k : k' ≠ k := Nat.ne_of_lt hk_lt
        have hk'_wm : k' < Wm := lt_trans hk_lt hk_wm
        have hne_ej : eJ' ≠ eJ := by
          have hk'_len : k' < inp.prep.j0Edges.length := lt_trans hk_lt hk
          have hget' : eJ' = inp.prep.j0Edges[k'] := by simp [eJ', hk'_len]
          rw [hget']
          exact fun heq => absurd ((hj0_nodup.getElem_inj_iff).mp heq) hne_k
        have hkm := hm_k_ne k' hne_k hk'_wm
        have hj0 := hm_jSrc_ne eJ' hne_ej 0 (by decide)
        have hj1 := hm_jSrc_ne eJ' hne_ej 1 (by decide)
        have hj2 := hm_jSrc_ne eJ' hne_ej 2 (by decide)
        exact ⟨hkm.1.trans hp.1, hkm.2.1.trans hp.2.1, hkm.2.2.1.trans hp.2.2.1,
          (hkm.2.2.2 0 (by decide)).trans hp.2.2.2.1,
          (hkm.2.2.2 1 (by decide)).trans hp.2.2.2.2.1,
          (hkm.2.2.2 2 (by decide)).trans hp.2.2.2.2.2.1,
          hj0.trans hp.2.2.2.2.2.2.1, hj1.trans hp.2.2.2.2.2.2.2.1, hj2.trans hp.2.2.2.2.2.2.2.2⟩
      · subst hkk
        have heJ_len : eJ < inp.prep.J.edges.length := heJ_lt_m
        have hedge_eq : inp.prep.J.edges[eJ]! = inp.prep.J.edges[eJ] := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem heJ_len]; rfl
        have hc := j0_writes_cell m wAddr Wm k' eJ
          (inp.prep.J.edges[eJ].1) (inp.prep.J.edges[eJ].2) inp.prep.phiNum_dec hk_wm
        dsimp only at hc ⊢
        rw [heJ_eq, hedge_eq]
        exact hc
    · intro k' hk' hk'_wm
      have hz := hzero_w k' (by omega) hk'_wm
      have hne_k : k' ≠ k := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk')
      have hkm := hm_k_ne k' hne_k hk'_wm
      exact ⟨hkm.1.trans hz.1, hkm.2.1.trans hz.2.1, hkm.2.2.1.trans hz.2.2.1,
        fun t ht => (hkm.2.2.2 t ht).trans (hz.2.2.2 t ht)⟩
    · intro eJ' heJ'_lt hnot_mem t ht
      rw [List.take_succ_eq_append_getElem hk, List.mem_append, List.mem_singleton] at hnot_mem
      push Not at hnot_mem
      exact (hm_jSrc_ne eJ' hnot_mem.2 t ht).trans (hzero_j eJ' heJ'_lt hnot_mem.1 t ht)
  · dsimp only [regs']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hr29

/-- Verification of `forRange 29 (.const 0) (.reg 12) buildJ0AsmBody`, transitioning from
initial zeroed state to `AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr 0`. -/
theorem buildJ0AsmLoop_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) :
    Triple w p
      (fun st => AsmJ0Inv inp ce pds mem₀ WSubs aCompExt wAddr 0
        { st with regs := Function.update st.regs 29 0 })
      (forRange 29 (.const 0) (.reg 12) buildJ0AsmBody)
      (normalPost fun st => AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr 0
        { st with regs := Function.update st.regs 29 0 })
      (fun _ => 135 * inp.prep.j0Edges.length + 9 * inp.prep.j0Edges.length + 7) := by
  have h1w : 1 < 2 ^ w := (ce_word_bounds hvalid).1
  have hlen_lt_w : inp.prep.j0Edges.length < 2 ^ w := by
    have hlt := (ce_word_bounds hvalid).2.1
    have := (inp.input_reads_lt_h hvalid).2.2.2.2.1
    have hmax : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  have h0w : 0 < 2 ^ w := lt_trans Nat.zero_lt_one h1w
  refine (Triple.seq_normal_const
    (R := AsmJ0Inv inp ce pds mem₀ WSubs aCompExt wAddr 0)
    (c₁ := (Expr.const 0).size + 1)
    (c₂ := 144 * inp.prep.j0Edges.length + 4)
    ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  · exact Triple.assign (val := fun _ => 0) (fun _ _ => ev_const h0w) fun _ hP => hP
  · refine ((Triple.forUp_const 135 0 inp.prep.j0Edges.length
      (Nat.zero_le _) h1w (fun _ => hlen_lt_w)
      (fun _ _ _ _ hP => hP.2.2.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hP => by simp [Expr.eval, hP.2.1.2.2.2.2.2.2.1])
      (fun k _ hk => Triple.weaken_pre (buildJ0AsmBody_triple hvalid (k := k))
        fun _ hinv => ⟨hinv, hk⟩)).strengthen_post ?_).mono_cost
      (fun _ _ => by simp [Expr.size]; omega)
    · intro o st hpost
      cases o with
      | normal =>
        rcases hpost with ⟨_, hbase, h18, h23, h24, h25, h26, h27, h28, _,
          hws, ha_ext, hmax_le, hce, hbel, hhdr0, hm12, hm13, hm14, hm15, hm16,
          hmn, hmm, hprev, hzw, hzj, hzf⟩
        refine ⟨Nat.zero_le _, @ceBaseInv_of_agree inp ce pds mem₀ st.mem aCompExt wAddr st
            hbase h18 ha_ext (fun _ _ => rfl) (Function.update st.regs 29 0)
            (fun r hr => by rw [Function.update_of_ne (by omega)]),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hws, ha_ext, hmax_le, hce, hbel, hhdr0,
          hm12, hm13, hm14, hm15, hm16, hmn, hmm, hprev,
          fun j hj => (Nat.not_lt_zero j hj).elim, fun j hj => (Nat.not_lt_zero j hj).elim,
          by simpa using hzw,
          fun eJ heJ hnot _ => by
            simpa using hzj eJ heJ (by rw [List.take_length]; exact hnot),
          hzf⟩
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact h18
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact h23
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact h24
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact h25
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact h26
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact h27
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact h28
        · dsimp only; rw [Function.update_self]
      | returned _ => exact False.elim hpost

end MinCostFlow.Spanner
