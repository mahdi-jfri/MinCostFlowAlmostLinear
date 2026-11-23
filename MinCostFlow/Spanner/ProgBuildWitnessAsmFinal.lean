module

public import MinCostFlow.Spanner.ProgBuildWitnessAsmLoop

/-!
# Witness assembly Phase 3: final postcondition and `buildAssemble_triple`

Converts the final component-assembly invariant into `AsmPost` and proves the full
Phase 3 assembly triple `buildAssemble_triple`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-- Convert final `AsmCompInv` (at `ciDone = rawComps.length`) to `AsmPost`. -/
lemma asmCompInv_final_to_asmPost {w : ℕ} {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr : ℕ} {st : State}
    (hvalid : inp.Valid ce pds mem₀ w)
    (hinv : AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr inp.prep.rawComps.length st) :
    AsmPost inp ce pds mem₀ st := by
  set wd := inp.mkWitnessData ce pds WSubs
  rcases hinv with ⟨_, _, _, _, _, _, _, _, hr28, _, hws, ha_ext, hmax_le,
    hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16, hm_n, hm_m,
    hprev_j0, hprev_w, hprev_j, _, hzero_j, hzf⟩
  have hclen : wd.comps.length = inp.prep.rawComps.length :=
    WitnessCoreInput.buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have haligned := WitnessCoreInput.buildCompsFrom_aligned inp inp.prep.j0Edges.length
    inp.prep.rawComps WSubs hws.1
  have hsum_m : (wd.comps.map fun c => c.W_sub.m).sum = (WSubs.map Graph.m).sum := by
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
  refine ⟨aCompExt, wAddr, WSubs, hr28, hws, ha_ext, hmax_le, hbelow, hhdr0,
    hm12, hm13, hm14, hm15, hm16, ?_, ?_, ?_, ?_, ?_, hcomp_ext, hzf⟩
  · -- GraphAt st.mem wAddr wd.W
    refine graphAt_of_cells hm_n hm_m fun eW heW => ?_
    change eW < (wd.W.edges).length at heW
    rcases lt_or_ge eW inp.prep.j0Edges.length with heW_j0 | heW_comp
    · have hget := hprev_j0 eW heW_j0
      have hlen_l : (List.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) inp.prep.j0Edges).length =
          inp.prep.j0Edges.length := List.length_map _
      have hed_eq : wd.W.edges[eW] =
          (List.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) inp.prep.j0Edges ++
            wd.comps.flatMap compWEdges)[eW]'(by
              simpa [wd, WitnessCoreInput.mkWitnessData] using heW) := rfl
      have hed : wd.W.edges[eW] = inp.prep.J.edges.getD inp.prep.j0Edges[eW] (0, 0) := by
        rw [hed_eq, List.getElem_append_left (by rw [hlen_l]; exact heW_j0)]
        simp
      have he1 : inp.prep.j0Edges[eW]! = inp.prep.j0Edges[eW] := by
        simp [heW_j0]
      have he2 : inp.prep.J.edges.getD inp.prep.j0Edges[eW] (0, 0) =
          inp.prep.J.edges[inp.prep.j0Edges[eW]!]! := by
        simp [he1, List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]; rfl
      rw [hed, he2]
      exact ⟨hget.1, hget.2.1⟩
    · have heW_lt_sum : eW < inp.prep.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
        rw [hsum_m, ← hwm_eq]; exact heW
      rcases compsAligned_find_wStart haligned eW heW_comp heW_lt_sum with ⟨ci, hci_c, hws_le, hws_lt⟩
      have hci : ci < inp.prep.rawComps.length := by rwa [← hclen]
      have hws_le' : wd.comps[ci].wStart ≤ eW := hws_le
      have hws_lt' : eW < wd.comps[ci].wStart + wd.comps[ci].W_sub.m := hws_lt
      let eL := eW - wd.comps[ci].wStart
      have heL : eL < wd.comps[ci].W_sub.m := Nat.sub_lt_left_of_lt_add hws_le' hws_lt'
      have hflat := compsAligned_flatMap_getElem haligned ci hci_c eL heL
      rcases hflat with ⟨hidx_f, hval_f⟩
      have hge_off : inp.prep.j0Edges.length ≤ wd.comps[ci].wStart :=
        compsAligned_wStart_ge haligned wd.comps[ci] (List.getElem_mem hci_c)
      have hdiff : eW - inp.prep.j0Edges.length =
          (wd.comps[ci].wStart - inp.prep.j0Edges.length) + eL := by
        dsimp only [eL]; omega
      have hlen_l : (List.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) inp.prep.j0Edges).length =
          inp.prep.j0Edges.length := List.length_map _
      have hed_eq : wd.W.edges[eW] =
          (List.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) inp.prep.j0Edges ++
            wd.comps.flatMap compWEdges)[eW]'(by
              simpa [wd, WitnessCoreInput.mkWitnessData] using heW) := rfl
      have hed : wd.W.edges[eW] =
          (wd.comps[ci].verts.getD wd.comps[ci].W_sub.edges[eL].1 0,
            wd.comps[ci].verts.getD wd.comps[ci].W_sub.edges[eL].2 0) := by
        rw [hed_eq, List.getElem_append_right (by rw [hlen_l]; exact heW_comp)]
        simp only [List.length_map]
        calc
          (wd.comps.flatMap compWEdges)[eW - inp.prep.j0Edges.length]'_ =
              (wd.comps.flatMap compWEdges)[wd.comps[ci].wStart - inp.prep.j0Edges.length + eL]'hidx_f := by
            congr 1
          _ = _ := hval_f
      have hgetd_ci : wd.comps.getD ci defaultCompInfo = wd.comps[ci] := by
        dsimp only [wd, WitnessCoreInput.mkWitnessData]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci_c, Option.getD_some]
      have hcw := hprev_w ci hci eL (by rwa [hgetd_ci])
      rw [hgetd_ci] at hcw
      dsimp only at hcw
      have hwIdx : wd.comps[ci].wStart + eL = eW := Nat.add_sub_cancel' hws_le'
      rw [hwIdx] at hcw
      have heW1 : (wd.comps[ci].W_sub.edges[eL]!).1 = wd.comps[ci].W_sub.edges[eL].1 := by
        have hlen_e : eL < wd.comps[ci].W_sub.edges.length := heL
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen_e, Option.getD_some]; rfl
      have heW2 : (wd.comps[ci].W_sub.edges[eL]!).2 = wd.comps[ci].W_sub.edges[eL].2 := by
        have hlen_e : eL < wd.comps[ci].W_sub.edges.length := heL
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen_e, Option.getD_some]; rfl
      rw [hed]
      refine ⟨?_, ?_⟩
      · rw [hcw.1, heW1]; simp [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      · rw [hcw.2.1, heW2]; simp [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  · -- j0 weights
    intro k hk
    exact (hprev_j0 k hk).2.2.1
  · -- comp weights
    intro j hj eL heL
    rw [hclen] at hj
    rw [Nat.add_assoc]
    exact (hprev_w j hj eL heL).2.2.1
  · -- WSourcesAt
    intro i hi
    have hlen_ws : wd.wSources.length = wd.W.m := by
      change (List.map WEdgeSource.fromJ0 inp.prep.j0Edges ++
        List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
          (List.range x.1.W_sub.m)) (wd.comps.zipIdx 0)).length = wd.W.m
      rw [List.length_append, List.length_map, List.length_flatMap]
      have hmap : (List.map (fun x : CompInfo × ℕ =>
          (List.map (fun eL => WEdgeSource.fromComp x.2 eL) (List.range x.1.W_sub.m)).length)
          (wd.comps.zipIdx 0)) = List.map (fun c : CompInfo => c.W_sub.m) wd.comps := by
        refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
        simp
      rw [hmap, hsum_m, hwm_eq]
    rcases lt_or_ge i inp.prep.j0Edges.length with hi_j0 | hi_comp
    · have hget := hprev_j0 i hi_j0
      have hsrc_eq : wd.wSources[i] =
          (List.map WEdgeSource.fromJ0 inp.prep.j0Edges ++
            List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
              (List.range x.1.W_sub.m)) (wd.comps.zipIdx 0))[i]'(by
                simpa [wd, WitnessCoreInput.mkWitnessData] using hi) := rfl
      have hsrc : wd.wSources[i] = WEdgeSource.fromJ0 inp.prep.j0Edges[i] := by
        rw [hsrc_eq, List.getElem_append_left (by rw [List.length_map]; exact hi_j0)]
        simp
      have he1 : inp.prep.j0Edges[i]! = inp.prep.j0Edges[i] := by
        simp [hi_j0]
      rw [hsrc]
      refine ⟨hget.2.2.2.1, ?_, hget.2.2.2.2.2.1⟩
      rw [hget.2.2.2.2.1, he1]
    · have hi_lt_sum : i < inp.prep.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
        rw [hsum_m, ← hwm_eq, ← hlen_ws]; exact hi
      rcases compsAligned_find_wStart haligned i hi_comp hi_lt_sum with ⟨ci, hci_c, hws_le, hws_lt⟩
      have hci : ci < inp.prep.rawComps.length := by rwa [← hclen]
      have hws_le' : wd.comps[ci].wStart ≤ i := hws_le
      have hws_lt' : i < wd.comps[ci].wStart + wd.comps[ci].W_sub.m := hws_lt
      let eL := i - wd.comps[ci].wStart
      have heL : eL < wd.comps[ci].W_sub.m := Nat.sub_lt_left_of_lt_add hws_le' hws_lt'
      have hflat := compsAligned_flatMap_wSources (base := 0) haligned ci hci_c eL heL
      rcases hflat with ⟨hidx_f, hval_f⟩
      have hge_off : inp.prep.j0Edges.length ≤ wd.comps[ci].wStart :=
        compsAligned_wStart_ge haligned wd.comps[ci] (List.getElem_mem hci_c)
      have hdiff : i - inp.prep.j0Edges.length =
          (wd.comps[ci].wStart - inp.prep.j0Edges.length) + eL := by
        dsimp only [eL]; omega
      have hsrc_eq : wd.wSources[i] =
          (List.map WEdgeSource.fromJ0 inp.prep.j0Edges ++
            List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
              (List.range x.1.W_sub.m)) (wd.comps.zipIdx 0))[i]'(by
                simpa [wd, WitnessCoreInput.mkWitnessData] using hi) := rfl
      have hsrc : wd.wSources[i] = WEdgeSource.fromComp ci eL := by
        rw [hsrc_eq, List.getElem_append_right (by rw [List.length_map]; exact hi_comp)]
        simp only [List.length_map]
        calc
          (List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
              (List.range x.1.W_sub.m)) (wd.comps.zipIdx 0))[i - inp.prep.j0Edges.length]'_ =
              (List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
                (List.range x.1.W_sub.m)) (wd.comps.zipIdx 0))[
                wd.comps[ci].wStart - inp.prep.j0Edges.length + eL]'hidx_f := by
            congr 1
          _ = WEdgeSource.fromComp (0 + ci) eL := hval_f
          _ = WEdgeSource.fromComp ci eL := by simp
      have hgetd_ci : wd.comps.getD ci defaultCompInfo = wd.comps[ci] := by
        dsimp only [wd, WitnessCoreInput.mkWitnessData]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci_c, Option.getD_some]
      have hcw := hprev_w ci hci eL (by rwa [hgetd_ci])
      rw [hgetd_ci] at hcw
      dsimp only at hcw
      have hwIdx : wd.comps[ci].wStart + eL = i := Nat.add_sub_cancel' hws_le'
      rw [hwIdx] at hcw
      rw [hsrc]
      exact ⟨hcw.2.2.2.1, hcw.2.2.2.2.1, hcw.2.2.2.2.2⟩
  · -- JSourcesAt
    intro eJ heJ
    have heJ_m : eJ < inp.prep.J.m := by
      simpa [WitnessCoreInput.mkWitnessData, wd] using heJ
    have hjs_val : wd.jSources[eJ] =
        if eJ ∈ inp.prep.j0Edges then JEdgeSource.inJ0 (inp.prep.j0Edges.idxOf eJ)
        else match findJCompEdge eJ wd.comps 0 with
          | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
          | none => JEdgeSource.isLoop := by
      dsimp only [wd, WitnessCoreInput.mkWitnessData]
      have hmap := List.getElem_map
        (f := fun eJ =>
          if eJ ∈ inp.prep.j0Edges then JEdgeSource.inJ0 (inp.prep.j0Edges.idxOf eJ)
          else match findJCompEdge eJ
              (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs) 0 with
            | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
            | none => JEdgeSource.isLoop)
        (l := List.range inp.prep.J.m) (i := eJ) (h := by rw [List.length_map, List.length_range]; exact heJ_m)
      simp only [List.getElem_range] at hmap
      exact hmap
    rw [hjs_val]
    by_cases hj0 : eJ ∈ inp.prep.j0Edges
    · simp only [hj0, ↓reduceIte]
      let k := inp.prep.j0Edges.idxOf eJ
      have hk : k < inp.prep.j0Edges.length := List.idxOf_lt_length_of_mem hj0
      have hget := hprev_j0 k hk
      have hkeq : inp.prep.j0Edges[k]! = eJ := by
        simp [hk, k]
      rw [hkeq] at hget
      exact ⟨hget.2.2.2.2.2.2.1, hget.2.2.2.2.2.2.2.1, hget.2.2.2.2.2.2.2.2⟩
    · simp only [hj0, ↓reduceIte]
      have hspec := findJCompEdge_spec eJ wd.comps 0
      cases hfc : findJCompEdge eJ wd.comps 0 with
      | none =>
        rw [hfc] at hspec
        have hnot_c : ∀ j < inp.prep.rawComps.length,
            eJ ∉ (wd.comps.getD j defaultCompInfo).jSubOrigEdges := by
          intro j hj
          have hj_c : j < wd.comps.length := by rw [hclen]; exact hj
          have hmem : wd.comps.getD j defaultCompInfo ∈ wd.comps := by
            simp [List.getD_eq_getElem?_getD, hj_c, List.getElem_mem]
          exact hspec _ hmem
        have hz := hzero_j eJ heJ_m hj0 hnot_c
        exact ⟨hz 0 (by omega), hz 1 (by omega), hz 2 (by omega)⟩
      | some p =>
        rcases p with ⟨ci, jL⟩
        rw [hfc] at hspec
        rcases hspec with ⟨hci_c, hjL, _, heJ_eq⟩
        simp only [Nat.sub_zero] at hci_c hjL heJ_eq
        have hci : ci < inp.prep.rawComps.length := by rwa [← hclen]
        have hcj := cJOrig_props hvalid.2.2.1 hci
        have hw_ci := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci
        have hgetd_ci : wd.comps.getD ci defaultCompInfo = wd.comps[ci] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci_c, Option.getD_some]
        have hj_eq : wd.comps[ci].J_sub = inp.prep.cJSub inp.prep.rawComps[ci] := by
          dsimp only [wd, WitnessCoreInput.mkWitnessData]
          exact hw_ci.2.2.2.2.2.1
        have ho_eq : wd.comps[ci].jSubOrigEdges = inp.prep.cJOrig inp.prep.rawComps[ci] := by
          dsimp only [wd, WitnessCoreInput.mkWitnessData]
          exact hw_ci.2.2.2.2.2.2.1
        have hjL_sub : jL < (wd.comps.getD ci defaultCompInfo).J_sub.m := by
          rw [hgetd_ci, hj_eq]
          have hlen_o : wd.comps[ci].jSubOrigEdges.length =
              (inp.prep.cJSub inp.prep.rawComps[ci]).m := by
            rw [ho_eq]; exact hcj.1
          change jL < wd.comps[ci].jSubOrigEdges.length at hjL
          omega
        have hgj := hprev_j ci hci jL hjL_sub
        rw [hgetd_ci] at hgj
        dsimp only at hgj
        have heJ_bang : wd.comps[ci].jSubOrigEdges[jL]! = eJ := by
          simp [hjL, heJ_eq]
        rw [heJ_bang] at hgj
        exact hgj

/-- Phase 3 assembly triple: from `CeLoopPost` to `AsmPost` in `cePhase3Cost` steps. -/
theorem buildAssemble_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) :
    Triple w p
      (CeLoopPost inp ce pds mem₀)
      buildAssembleStmt
      (normalPost fun st => AsmPost inp ce pds mem₀ st ∧ inp.h + 20 ≤ st.mem (inp.h + 12))
      (fun _ => cePhase3Cost inp ce) := by
  intro st ω hpre
  rcases hpre with ⟨hbase, ha_ext, hzf_w, WSubs, hws, hWm, hcomp_ext, hmax_le⟩
  set aCompExt := st.regs 18
  set wAddr := st.regs 17
  set Wm := st.regs 23
  set wd := inp.mkWitnessData ce pds WSubs
  set wWNumAddr := wAddr + (2 + 2 * Wm)
  set wSrcAddr := wWNumAddr + Wm
  set jSrcAddr := wSrcAddr + 3 * Wm
  set hEnd := jSrcAddr + 3 * inp.prep.J.m
  have hwb := ce_word_bounds hvalid
  have h1w : 1 < 2 ^ w := hwb.1
  have hmax_w : inp.maxHeapEnd ce pds < 2 ^ w := hwb.2.1
  have hEnd_eq : hEnd = wAddr + (2 + 6 * wd.W.m + 3 * inp.prep.J.m) := by
    dsimp only [hEnd, jSrcAddr, wSrcAddr, wWNumAddr]
    rw [hWm]
    omega
  have hEnd_lt : hEnd < 2 ^ w := by rw [hEnd_eq]; exact lt_of_le_of_lt hmax_le hmax_w
  have hha_ge : inp.h + 20 ≤ aCompExt := hbase.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hr4 : st.regs 4 = inp.h := hbase.2.1
  have hr5 : st.regs 5 = inp.prep.J.n := hbase.2.2.1
  have hr6 : st.regs 6 = inp.prep.J.m := hbase.2.2.2.1
  have hr17 : st.regs 17 = wAddr := rfl
  have hr23 : st.regs 23 = Wm := rfl
  have hwAddr_w : wAddr < 2 ^ w := by omega
  have hwWNum_w : wWNumAddr < 2 ^ w := by omega
  have hwSrc_w : wSrcAddr < 2 ^ w := by omega
  have hjSrc_w : jSrcAddr < 2 ^ w := by omega
  have hWm_w : Wm < 2 ^ w := by omega
  have hJm_w : inp.prep.J.m < 2 ^ w := by omega
  have hJn_w : inp.prep.J.n < 2 ^ w := by
    have hv := hvalid.2.2.1
    have hwb_prep := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hhend := hvalid.2.2.2.1
    have hs : inp.prep.h ≤ inp.prep.hBlocksStart := by unfold PrepInput.hBlocksStart; omega
    have he : inp.prep.hBlocksStart ≤ inp.prep.hEnd := by unfold PrepInput.hEnd; omega
    omega
  have hh_w : inp.h < 2 ^ w := by omega
  have h16w : 16 < 2 ^ w := by omega
  have h15w : 15 < 2 ^ w := by omega
  have h14w : 14 < 2 ^ w := by omega
  have h13w : 13 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hcost_le : (135 * inp.prep.j0Edges.length + 9 * inp.prep.j0Edges.length + 7) +
      (rangeCost (asmCompStepCost inp WSubs) 0 inp.prep.rawComps.length +
        9 * inp.prep.rawComps.length + 7) + 1 ≤ cePhase3Cost inp ce - 65 := by
    have htot := asmTotalCost_le hvalid hws
    unfold asmTotalCost at htot
    omega
  rcases st with ⟨m₀, r₀, pos₀⟩
  dsimp only at hr4 hr5 hr6 hr17 hr23 hha_ge ha_ext hzf_w hmax_le hcomp_ext hbase
  suffices hres : ∃ o st' c',
      Runs w p ω buildAssembleStmt { mem := m₀, regs := r₀, pos := pos₀ } o st' c' ∧
        normalPost (fun st => AsmPost inp ce pds mem₀ st ∧ inp.h + 20 ≤ st.mem (inp.h + 12)) o st' ∧
        0 + c' ≤ cePhase3Cost inp ce by
    simpa only [Nat.zero_add] using hres
  unfold buildAssembleStmt
  refine runs_seq_assign_flat (k := 0) (c_bound := cePhase3Cost inp ce) (v := wAddr)
    (ev_reg hr17 hwAddr_w) ?_
  refine runs_seq_assign_flat (v := wWNumAddr) ?_ ?_
  · refine ev_add (ev_reg (by simp) hwAddr_w)
      (ev_add (ev_const h2w) (ev_mul (ev_const h2w)
        (ev_reg (by simp [hr23]) hWm_w) (by omega)) (by omega)) (by omega)
  refine runs_seq_assign_flat (v := wSrcAddr) ?_ ?_
  · refine ev_add (ev_reg (by simp) hwWNum_w)
      (ev_reg (by simp [hr23]) hWm_w) (by omega)
  refine runs_seq_assign_flat (v := jSrcAddr) ?_ ?_
  · refine ev_add (ev_reg (by simp) hwSrc_w)
      (ev_mul (ev_const h3w) (ev_reg (by simp [hr23]) hWm_w) (by omega)) (by omega)
  refine runs_seq_assign_flat (v := hEnd) ?_ ?_
  · refine ev_add (ev_reg (by simp) hjSrc_w)
      (ev_mul (ev_const h3w) (ev_reg (by simp; exact hr6) hJm_w) (by omega)) (by omega)
  refine runs_seq_store_flat (x := inp.h + 13) (v := wAddr) ?_ ?_ ?_
  · refine ev_add (ev_reg (by simp; exact hr4) hh_w) (ev_const h13w) (by omega)
  · exact ev_reg (by simp) hwAddr_w
  refine runs_seq_store_flat (x := inp.h + 14) (v := wWNumAddr) ?_ ?_ ?_
  · refine ev_add (ev_reg (by simp; exact hr4) hh_w) (ev_const h14w) (by omega)
  · exact ev_reg (by simp) hwWNum_w
  refine runs_seq_store_flat (x := inp.h + 15) (v := wSrcAddr) ?_ ?_ ?_
  · refine ev_add (ev_reg (by simp; exact hr4) hh_w) (ev_const h15w) (by omega)
  · exact ev_reg (by simp) hwSrc_w
  refine runs_seq_store_flat (x := inp.h + 16) (v := jSrcAddr) ?_ ?_ ?_
  · refine ev_add (ev_reg (by simp; exact hr4) hh_w) (ev_const h16w) (by omega)
  · exact ev_reg (by simp) hjSrc_w
  refine runs_seq_store_flat (x := wAddr) (v := inp.prep.J.n) ?_ ?_ ?_
  · exact ev_reg (by simp) hwAddr_w
  · exact ev_reg (by simp; exact hr5) hJn_w
  refine runs_seq_store_flat (x := wAddr + 1) (v := Wm) ?_ ?_ ?_
  · refine ev_add (ev_reg (by simp) hwAddr_w) (ev_const h1w) (by omega)
  · exact ev_reg (by simp [hr23]) hWm_w
  -- Now run J0 assembly loop then component assembly loop.
  let m6 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update m₀ (inp.h + 13) wAddr) (inp.h + 14) wWNumAddr) (inp.h + 15) wSrcAddr)
    (inp.h + 16) jSrcAddr) wAddr inp.prep.J.n) (wAddr + 1) Wm
  let r5 := Function.update (Function.update (Function.update (Function.update (Function.update
    r₀ 24 wAddr) 25 wWNumAddr) 26 wSrcAddr) 27 jSrcAddr) 28 hEnd
  have hm6_agree_below : ∀ x < aCompExt, x ≠ inp.h + 13 → x ≠ inp.h + 14 → x ≠ inp.h + 15 →
      x ≠ inp.h + 16 → m6 x = m₀ x := by
    intro x hx h13 h14 h15 h16
    dsimp only [m6]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne h16, Function.update_of_ne h15,
      Function.update_of_ne h14, Function.update_of_ne h13]
  have hm6_below : ∀ x < inp.h, m6 x = mem₀ x := fun x hx => by
    rw [hm6_agree_below x (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x hx
  have hm6_hdr0 : WitnessHdr0 m6 inp ce pds := by
    have hhdr := hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hm6_base : CeBaseInv inp ce pds mem₀
      { mem := m6, regs := Function.update r5 29 0, pos := pos₀ } := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm6_below, hm6_hdr0⟩
    · dsimp only [r5]; simp; exact hbase.1
    · dsimp only [r5]; simp; exact hr4
    · dsimp only [r5]; simp; exact hr5
    · dsimp only [r5]; simp; exact hr6
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.1
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.2.1
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.2.2.1
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.2.2.2.1
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.2.2.2.2.1
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.2.2.2.2.2.1
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.2.2.2.2.2.2.1
    · dsimp only
      rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      dsimp only [r5]; simp
      exact hbase.2.2.2.2.2.2.2.2.2.2.2.1
    · dsimp only [r5]; simp; exact hha_ge
    · dsimp only [r5]; simp; exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm6_cext : CompExtAt m6 aCompExt inp.prep.phiNum_dec wAddr wd.comps := by
    intro ci hci
    have hci_old := hcomp_ext ci hci
    dsimp only at hci_old ⊢
    have hm_ext : ∀ x, aCompExt ≤ x → x < wAddr → m6 x = m₀ x := by
      intro x hx1 hx2
      dsimp only [m6]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hpw : m6 (aCompExt + 6 * ci + 1) = m₀ (aCompExt + 6 * ci + 1) :=
      hm_ext _ (by omega) (by omega)
    rw [hpw]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hci_old.2.2.2.2.2.2.1, hci_old.2.2.2.2.2.2.2⟩
    · rw [hm_ext _ (by omega) (by omega)]; exact hci_old.1
    · rw [hm_ext _ (by omega) (by omega)]; exact hci_old.2.1
    · rw [hm_ext _ (by omega) (by omega)]; exact hci_old.2.2.1
    · rw [hm_ext _ (by omega) (by omega)]; exact hci_old.2.2.2.1
    · rw [hm_ext _ (by omega) (by omega)]; exact hci_old.2.2.2.2.1
    · intro k hk
      have hlen_e : (wd.comps[ci]).W_sub.encode.length = 2 + 2 * (wd.comps[ci]).W_sub.m := by
        simp [Graph.encode, Graph.m]; ring
      rw [hm_ext _ (by omega) (by omega)]
      exact hci_old.2.2.2.2.2.1 k hk
  have hm6_zero_above : ∀ x, wAddr + 2 ≤ x → m6 x = 0 := by
    intro x hx
    dsimp only [m6]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hzf_w x (by omega)
  have hj0_pre : AsmJ0Inv inp ce pds mem₀ WSubs aCompExt wAddr 0
      { mem := m6, regs := Function.update r5 29 0, pos := pos₀ } := by
    unfold AsmJ0Inv
    dsimp only
    refine ⟨Nat.zero_le _, hm6_base,
      by dsimp only [r5]; simp; rfl,
      by dsimp only [r5]; simp; exact hWm,
      by dsimp only [r5]; simp,
      by dsimp only [r5]; simp [wWNumAddr, hWm, wd],
      by dsimp only [r5]; simp [wSrcAddr, wWNumAddr, hWm, wd],
      by dsimp only [r5]; simp [jSrcAddr, wSrcAddr, wWNumAddr, hWm, wd],
      by dsimp only [r5]; simp [hEnd, jSrcAddr, wSrcAddr, wWNumAddr, hWm, wd],
      by simp,
      hws, ha_ext,
      (by
        rw [show wAddr + (2 + 2 * wd.W.m) + wd.W.m + 3 * wd.W.m + 3 * inp.prep.J.m =
          wAddr + (2 + 6 * wd.W.m + 3 * inp.prep.J.m) by ring]
        exact hmax_le),
      hm6_cext, hm6_below, hm6_hdr0, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun _ hk => (Nat.not_lt_zero _ hk).elim, ?_, ?_, ?_⟩
    · rw [hm6_agree_below _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hbase.2.2.2.2.2.2.2.2.2.2.2.1
    · dsimp only [m6]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · dsimp only [m6]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]; simp [wWNumAddr, hWm, wd]
    · dsimp only [m6]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]; simp [wSrcAddr, wWNumAddr, hWm, wd]
    · dsimp only [m6]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]; simp [jSrcAddr, wSrcAddr, wWNumAddr, hWm, wd]
    · dsimp only [m6]; rw [Function.update_of_ne (by omega), Function.update_self]
    · dsimp only [m6]; rw [Function.update_self, hWm]
    · intro k _ hk_lt
      exact ⟨hm6_zero_above _ (by omega), hm6_zero_above _ (by omega),
        hm6_zero_above _ (by omega), fun t _ => hm6_zero_above _ (by omega)⟩
    · intro eJ _ _ t _
      exact hm6_zero_above _ (by omega)
    · intro a ha
      exact hm6_zero_above _ (by omega)
  have hloops :
      Triple w p
        (fun st => AsmJ0Inv inp ce pds mem₀ WSubs aCompExt wAddr 0
          { st with regs := Function.update st.regs 29 0 })
        (forRange 29 (.const 0) (.reg 12) buildJ0AsmBody ;;
          forRange 29 (.const 0) (.reg 14) buildCompAsmBody)
        (normalPost fun st => AsmPost inp ce pds mem₀ st ∧ inp.h + 20 ≤ st.mem (inp.h + 12))
        (fun _ => (135 * inp.prep.j0Edges.length + 9 * inp.prep.j0Edges.length + 7) +
          (rangeCost (asmCompStepCost inp WSubs) 0 inp.prep.rawComps.length +
            9 * inp.prep.rawComps.length + 7) + 1) := by
    refine (Triple.seq_normal_const
      (buildJ0AsmLoop_triple (p := p) (WSubs := WSubs) (aCompExt := aCompExt) (wAddr := wAddr) hvalid)
      (buildCompAsmLoop_triple (p := p) (WSubs := WSubs) (aCompExt := aCompExt) (wAddr := wAddr) hvalid)).strengthen_post ?_
    intro o st' hp
    cases o with
    | normal =>
      refine ⟨asmCompInv_final_to_asmPost hvalid hp, ?_⟩
      have hbase' := hp.2.1
      rw [hbase'.2.2.2.2.2.2.2.2.2.2.2.1]
      exact hbase'.2.2.2.2.2.2.2.2.2.2.2.2.1
    | returned _ => exact hp
  rcases hloops { mem := m6, regs := r5, pos := pos₀ } ω hj0_pre with ⟨o, st', c', hruns, hpost, hcost⟩
  refine ⟨o, st', c', hruns, hpost, ?_⟩
  simp only [Expr.size]
  dsimp only at hcost
  omega

end MinCostFlow.Spanner
