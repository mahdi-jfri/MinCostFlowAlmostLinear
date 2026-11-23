module

public import MinCostFlow.ExpanderDecomp.OuterProgRecBranches
public import MinCostFlow.ExpanderDecomp.ProgDecompEntrySpec

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recursive Outer Expander Decomposition Specification (`OuterProgRec`)

Completes the Word-RAM verification of the recursive outer expander decomposition procedure
`outerDecompRecProc`:

1. `recChild_runs`: shared runner for the three-call child sequence (`restrict` → `stripIsolated` →
   recursive `outerDecompRecProc`) used twice in the cut branch and once in the witness branch.
2. `recCut_runs`: executes `recCutStmt` on a sparse port cut `U`, combining both subtrees via
   `progRecSpec_cut_combine` and `recTreeSpace_cut_step`.
3. `recWitness_runs`: executes `recWitnessStmt` on a spanning port witness `(W_out, F_out)`,
   contracting fake edges, invoking `RemoveFake`, painting `R`, and recursing on `H.vertSet \ R`
   via `progRecSpec_witness_combine` and `recTreeSpace_witness_step`.
4. `outerDecompRecProc_spec`: strong induction on `H.edges.length` proving `RecNodePost` for every
   active compact subgraph `H`.
5. `outerRec_cost_le_totalTimeRaw` and `outerRec_treeSpace_le_outerDecompSpace`: global bridges from
   per-edge/per-witness budgets to `totalTimeRaw` and `outerDecompSpace`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-- Strong-induction hypothesis for `outerDecompRecProc` on active compact subgraphs with at most
`eBound` edges. -/
def RecIH (cfg : ParamConfig) (M r w C_core C_rt C_sp routeC : ℕ)
    (pProg : Program) (idx : OuterRecIndices) (G : Graph)
    (paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ) (ω : ℕ → Bool) (eBound : ℕ) : Prop :=
  ∀ (H' : CompactSubgraph) (vertsAddr' edgesAddr' h' nl' : ℕ) (st' : State),
    H'.edges.length ≤ eBound →
    H'.Represents G H'.vertSet →
    H'.vertSet ⊆ G.verts →
    H'.verts.Pairwise (· < ·) →
    (∀ v ∈ H'.vertSet, 1 ≤ G.degIn H'.vertSet v) →
    H'.edges.length ≤ M →
    hRoot ≤ h' →
    vertsAddr' + H'.verts.length ≤ h' →
    edgesAddr' + 2 * H'.edges.length ≤ h' →
    DisjointRange locAddr G.n vertsAddr' H'.verts.length →
    DisjointRange labelsAddr G.n vertsAddr' H'.verts.length →
    DisjointRange nextLblAddr 1 vertsAddr' H'.verts.length →
    DisjointRange locAddr G.n edgesAddr' (2 * H'.edges.length) →
    DisjointRange labelsAddr G.n edgesAddr' (2 * H'.edges.length) →
    DisjointRange nextLblAddr 1 edgesAddr' (2 * H'.edges.length) →
    OuterParamBlockAt st'.mem paramAddr cfg G.n M r →
    ListAt st'.mem vertsAddr' H'.verts →
    EdgesAt st'.mem edgesAddr' H'.edges →
    (∀ u < G.n, st'.mem (locAddr + u) = 0) →
    st'.mem nextLblAddr = nl' →
    nl' + H'.verts.length ≤ G.n →
    ZeroFrom st'.mem h' →
    h' + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
      (recPerWitSpace cfg M r) H'.edges.length < 2 ^ w →
    st'.regs 0 = H'.verts.length →
    st'.regs 1 = vertsAddr' →
    st'.regs 2 = H'.edges.length →
    st'.regs 3 = edgesAddr' →
    st'.regs 4 = paramAddr →
    st'.regs 5 = locAddr →
    st'.regs 6 = labelsAddr →
    st'.regs 7 = nextLblAddr →
    st'.regs 8 = h' →
    ∃ hEnd stEnd c,
      Runs w pProg ω (outerDecompRecProc idx) st' (.returned hEnd) stEnd c ∧
      RecNodePost cfg M r C_core C_rt C_sp routeC G locAddr labelsAddr nextLblAddr
        h' H' st'.mem nl' hEnd stEnd.mem c

/-- Global step-bound multiplier bridging `RecNodePost` to `totalTimeRaw`. -/
def outerRecCostK (C_core C_rt routeC : ℕ) : ℕ :=
  outerGameCostFactor C_core C_rt * (routeC * 2 ^ 29 + 234) +
    runnerScale explicitProgram * 760 + 2 ^ 31 + 20000

/-- Global space multiplier bridging `recTreeSpace` (at `r = rOf M`) to `outerDecompSpace`. -/
def outerRecSpaceC (C_sp routeC : ℕ) : ℕ :=
  C_sp * 2 ^ 155 * (routeC * 2 ^ 29 + 300) + C_sp * 3600 + 46000

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 1. Shared Child Runner (`restrict` → `stripIsolated` → `outerDecompRecProc`) -/

lemma verts_length_le_two_mul_edges {G : Graph} {H : CompactSubgraph}
    (hRep : H.Represents G H.vertSet) (hXdeg : ∀ v ∈ H.vertSet, 1 ≤ G.degIn H.vertSet v) :
    H.verts.length ≤ 2 * H.edges.length := by
  have hcard : H.vertSet.card = H.verts.length := List.toFinset_card_of_nodup hRep.1
  have hsum : H.vertSet.card ≤ G.volIn H.vertSet H.vertSet := by
    unfold Graph.volIn; rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum hXdeg
  rw [volIn_self, ← hRep.2.2] at hsum; omega

lemma recChild_runs {cfg : ParamConfig} {M r w C_core C_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv cfg M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hSub : RecSubprocs M r w pProg idx C_core C_rt C_sp routeC)
    {ω : ℕ → Bool} {eBound : ℕ}
    (hIH : RecIH cfg M r w C_core C_rt C_sp routeC pProg idx G
      paramAddr locAddr labelsAddr nextLblAddr hRoot ω eBound)
    {H : CompactSubgraph} {S : Finset ℕ}
    (hRep : H.Represents G H.vertSet) (hXV : H.vertSet ⊆ G.verts)
    (hSorted : H.verts.Pairwise (· < ·)) (hSX : S ⊆ H.vertSet)
    (heS_le : (H.restrict S).edges.length ≤ eBound) (heS_M : (H.restrict S).edges.length ≤ M)
    {rK rV rE rAct rRest rStrip rH : ℕ}
    (hrRest_ne : rRest ≠ rK ∧ rRest ≠ rV ∧ rRest ≠ rE ∧ rRest ≠ rAct ∧ rRest ≠ rStrip ∧
      rRest ≠ rH ∧ 8 < rRest)
    (hrStrip_ne : rStrip ≠ rK ∧ rStrip ≠ rV ∧ rStrip ≠ rE ∧ rStrip ≠ rAct ∧ rStrip ≠ rH ∧
      8 < rStrip)
    (_hrH_ne : rH ≠ rK ∧ rH ≠ rV ∧ rH ≠ rE ∧ rH ≠ rAct ∧ 8 < rH)
    {edgesAddr vSAddr eSAddr actSAddr hCur nl₀ : ℕ} {st : State}
    (hRoot_le : hRoot ≤ hCur)
    (hEA_le : edgesAddr + 2 * H.edges.length ≤ hCur)
    (hvS_le : vSAddr + (H.restrict S).verts.length ≤ hCur)
    (heS_addr : eSAddr + 2 * H.edges.length ≤ hCur)
    (hactS_addr : actSAddr + (H.restrict S).verts.length ≤ hCur)
    (hdLE : DisjointRange locAddr G.n edgesAddr (2 * H.edges.length))
    (hdES_E : DisjointRange eSAddr (2 * H.edges.length) edgesAddr (2 * H.edges.length))
    (hdES_V : DisjointRange eSAddr (2 * H.edges.length) vSAddr (H.restrict S).verts.length)
    (hdAct_V : DisjointRange actSAddr (H.restrict S).verts.length vSAddr (H.restrict S).verts.length)
    (hdAct_E : DisjointRange actSAddr (H.restrict S).verts.length eSAddr (2 * H.edges.length))
    (hV_root : hRoot ≤ vSAddr) (hE_root : hRoot ≤ eSAddr) (hAct_root : hRoot ≤ actSAddr)
    (hPB : OuterParamBlockAt st.mem paramAddr cfg G.n M r)
    (hVS : ListAt st.mem vSAddr (H.restrict S).verts)
    (hE : EdgesAt st.mem edgesAddr H.edges)
    (hloc0 : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hnl : st.mem nextLblAddr = nl₀)
    (hnl_le : nl₀ + (H.restrict S).verts.length ≤ G.n)
    (hZero : ZeroFrom st.mem hCur)
    (hSp : hCur + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
      (recPerWitSpace cfg M r) (H.restrict S).edges.length < 2 ^ w)
    (hr2 : st.regs 2 = H.edges.length) (hr3 : st.regs 3 = edgesAddr)
    (hr4 : st.regs 4 = paramAddr) (hr5 : st.regs 5 = locAddr)
    (hr6 : st.regs 6 = labelsAddr) (hr7 : st.regs 7 = nextLblAddr)
    (hrK : st.regs rK = (H.restrict S).verts.length)
    (hrV : st.regs rV = vSAddr) (hrE : st.regs rE = eSAddr)
    (hrAct : st.regs rAct = actSAddr) (hrH : st.regs rH = hCur) :
    let res := (H.restrict S).stripIsolated
    let iso := res.1
    let act := res.2
    ∃ (stEnd : State) (hEnd c : ℕ) (o : OuterRecOut),
      Runs w pProg ω
        (.call rRest idx.bRestrict [.reg rK, .reg rV, .reg 2, .reg 3, .reg 5, .reg rE] ;;
         .call rStrip idx.bStripIso
           [.reg rK, .reg rV, .reg rRest, .reg rE, .reg 5, .reg 6, .reg 7, .reg rAct] ;;
         .call rH idx.bSelf
           [.reg rStrip, .reg rAct, .reg rRest, .reg rE, .reg 4, .reg 5, .reg 6, .reg 7, .reg rH])
        st .normal stEnd c ∧
      OuterRecSpec cfg M r G act o ∧
      LabelsMatchParts stEnd.mem labelsAddr S ((iso.map fun v => ({v} : Finset ℕ)) ++ o.parts)
        nl₀ (stEnd.mem nextLblAddr) ∧
      stEnd.mem nextLblAddr ≤ nl₀ + (H.restrict S).verts.length ∧
      hCur ≤ hEnd ∧
      hEnd ≤ hCur + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
        (recPerWitSpace cfg M r) act.edges.length ∧
      ZeroFrom stEnd.mem hEnd ∧
      (∀ u < G.n, stEnd.mem (locAddr + u) = 0) ∧
      (∀ a < hCur,
        (a < eSAddr ∨ eSAddr + 2 * H.edges.length ≤ a) →
        (a < actSAddr ∨ actSAddr + (H.restrict S).verts.length ≤ a) →
        (∀ u ∈ S, a ≠ labelsAddr + u) →
        a ≠ nextLblAddr →
        stEnd.mem a = st.mem a) ∧
      stEnd.regs rH = hEnd ∧
      (∀ r', r' ≠ rRest → r' ≠ rStrip → r' ≠ rH → stEnd.regs r' = st.regs r') ∧
      c ≤ o.edgeSum * recPerEdgeCost cfg C_core C_rt M r routeC +
        o.witnessEdgeSum * recPerWitCost cfg M r +
        120 * (H.restrict S).verts.length + 90 * H.edges.length + 120 * act.edges.length + 800 := by
  intro res iso act
  set HS := H.restrict S
  set kS := HS.verts.length
  set e := H.edges.length
  set eS := HS.edges.length
  have hrepS : HS.Represents G S := CompactSubgraph.restrict_represents hRep hSX
  have hstS := CompactSubgraph.stripIsolated_spec hrepS
  have heAct : act.edges = HS.edges := hstS.2.2.2.2.2.1
  have heAct_len : act.edges.length = eS := congrArg List.length heAct
  have hsubVS : ∀ u ∈ HS.verts, u < G.n := fun u hu => by
    have h1 : u ∈ S := by rw [← hrepS.2.1]; exact List.mem_toFinset.mpr hu
    exact Finset.mem_range.mp (hXV (hSX h1))
  have hsubE : ∀ ed ∈ H.edges, ed.1 < G.n ∧ ed.2 < G.n := fun ed hed =>
    env.hv ed (by rw [hRep.2.2] at hed; exact (mem_inside_iff.mp hed).1)
  have hw16 : 16 < 2 ^ w := by have := env.hw250; omega
  have hCur_lt : hCur < 2 ^ w := by omega
  have hS_toFin : HS.verts.toFinset = S := hrepS.2.1
  have hFiltEq : (H.edges.filter fun ed => decide (ed.1 ∈ HS.verts.toFinset ∧ ed.2 ∈ HS.verts.toFinset)) =
      HS.edges := by
    rw [hS_toFin]; unfold HS CompactSubgraph.restrict
    apply List.filter_congr; intro ed _; simp [Bool.decide_and]
  -- 1. Call `bRestrict`
  have hRestCall := runs_call_of_meetsContract (r := rRest) (p := pProg) (w := w) (st := st)
    (args := [.reg rK, .reg rV, .reg 2, .reg 3, .reg 5, .reg rE])
    (vs := [kS, vSAddr, e, edgesAddr, locAddr, eSAddr]) hSub.hRestrict
    (by simp [evalArgs, Expr.eval, hrK, hrV, hr2, hr3, hr5, hrE])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        have := env.hlocH; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨G.n, kS, vSAddr, e, edgesAddr, locAddr, eSAddr, HS.verts, H.edges, rfl,
      rfl, hsubVS, rfl, hsubE, hVS, hE, hloc0, by omega, by omega,
      by have := env.hlocH; omega, by omega, hw16,
      Or.inl (by have := env.hlocH; omega), hdLE,
      Or.inl (by have := env.hlocH; omega), hdES_V, hdES_E⟩ ω
  rcases hRestCall with ⟨st1, c1, v1, hrun1, hpost1, h1_rRest, h1_other, hc1⟩
  dsimp only [restrictContract, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hpost1 hc1
  rcases hpost1 with ⟨hv1_eq, h1_ES, h1_fr⟩
  have hrL : readList st.mem vSAddr kS = HS.verts := readList_eq_of_listAt hVS
  have hreadE : readEdges st.mem edgesAddr e = H.edges := readEdges_eq_of_edgesAt hE
  simp only [hrL, hreadE, hFiltEq] at hv1_eq h1_ES
  change v1 = eS at hv1_eq
  have h1_VS : ListAt st1.mem vSAddr HS.verts := fun i hi => by
    rw [h1_fr (vSAddr + i) (by rcases hdES_V with h | h <;> omega)]; exact hVS i hi
  have h1_loc0 : ∀ u < G.n, st1.mem (locAddr + u) = 0 := fun u hu => by
    rw [h1_fr (locAddr + u) (Or.inl (by have := env.hlocH; omega))]; exact hloc0 u hu
  have h1_nl : st1.mem nextLblAddr = nl₀ := by
    rw [h1_fr nextLblAddr (Or.inl (by have := env.hnextH; omega))]; exact hnl
  -- 2. Call `bStripIso`
  have heS_le_e : eS ≤ e := List.length_filter_le _ _
  have hsubES : ∀ ed ∈ HS.edges, ed.1 < G.n ∧ ed.2 < G.n := fun ed hed =>
    hsubE ed (List.mem_of_mem_filter hed)
  have hStripCall := runs_call_of_meetsContract (r := rStrip) (p := pProg) (w := w) (st := st1)
    (args := [.reg rK, .reg rV, .reg rRest, .reg rE, .reg 5, .reg 6, .reg 7, .reg rAct])
    (vs := [kS, vSAddr, eS, eSAddr, locAddr, labelsAddr, nextLblAddr, actSAddr]) hSub.hStripIso
    (by simp only [evalArgs, Expr.eval,
          h1_other rK hrRest_ne.1.symm, hrK,
          h1_other rV hrRest_ne.2.1.symm, hrV, h1_rRest, hv1_eq,
          h1_other rE hrRest_ne.2.2.1.symm, hrE,
          h1_other 5 (by omega), hr5, h1_other 6 (by omega), hr6, h1_other 7 (by omega), hr7,
          h1_other rAct hrRest_ne.2.2.2.1.symm, hrAct])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        have := env.hlocH; have := env.hlblH; have := env.hnextH
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨G.n, kS, vSAddr, eS, eSAddr, locAddr, labelsAddr, nextLblAddr, actSAddr, HS.verts, HS.edges,
      rfl, rfl, hrepS.1, hsubVS, rfl, hsubES, h1_VS, h1_ES, h1_loc0,
      ⟨by omega, by omega, by have := env.hlocH; omega, by have := env.hlblH; omega,
       by have := env.hnextH; omega, by omega,
       by rw [h1_nl]; have := env.hwN; omega, hw16⟩,
      ⟨Or.inl (by have := env.hlocH; omega), Or.inl (by have := env.hlocH; omega),
       env.hdLLb, env.hdLN, Or.inl (by have := env.hlocH; omega),
       Or.inl (by have := env.hlblH; omega), Or.inl (by have := env.hlblH; omega),
       env.hdLbN, Or.inl (by have := env.hlblH; omega),
       hdAct_V,
       by rcases hdAct_E with h | h
          · exact Or.inl h
          · exact Or.inr (by omega),
       Or.inr (by have := env.hnextH; omega),
       Or.inl (by have := env.hnextH; omega), Or.inl (by have := env.hnextH; omega)⟩⟩ ω
  rcases hStripCall with ⟨st2, c2, v2, hrun2, hpost2, h2_rStrip, h2_other, hc2⟩
  dsimp only [stripIsolatedContract, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hpost2 hc2
  rw [readList_eq_of_listAt h1_VS, readEdges_eq_of_edgesAt h1_ES, h1_nl] at hpost2
  rcases hpost2 with ⟨hv2_eq, h2_actV, h2_nl, h2_isoLbl, h2_fr⟩
  have hiso_subS : ∀ u ∈ iso, u ∈ S := fun u hu => by
    have h1 : u ∈ iso.toFinset := List.mem_toFinset.mpr hu
    rw [← hstS.2.2.1]; exact Finset.mem_union_left _ h1
  have hiso_ltN : ∀ u ∈ iso, u < G.n := fun u hu => Finset.mem_range.mp (hXV (hSX (hiso_subS u hu)))
  have h2_PB : OuterParamBlockAt st2.mem paramAddr cfg G.n M r := by
    have hp : ∀ j < 12, st2.mem (paramAddr + j) = st.mem (paramAddr + j) := fun j hj => by
      have ha_lt : paramAddr + j < hRoot := by have := env.hparH; omega
      rw [h2_fr _ (fun u hu => by have := hiso_ltN u hu; rcases env.hdPLb with h | h <;> omega)
            (by rcases env.hdPN with h | h <;> omega) (Or.inl (by omega)),
          h1_fr _ (Or.inl (by omega))]
    exact ⟨by rw [hp 0 (by decide)]; exact hPB.1, by rw [hp 1 (by decide)]; exact hPB.2.1,
      by rw [hp 2 (by decide)]; exact hPB.2.2.1, by rw [hp 3 (by decide)]; exact hPB.2.2.2.1,
      by rw [hp 4 (by decide)]; exact hPB.2.2.2.2.1, by rw [hp 5 (by decide)]; exact hPB.2.2.2.2.2.1,
      by rw [hp 6 (by decide)]; exact hPB.2.2.2.2.2.2.1, by rw [hp 7 (by decide)]; exact hPB.2.2.2.2.2.2.2.1,
      by rw [hp 8 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.1, by rw [hp 9 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.1,
      by rw [hp 10 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.1, by rw [hp 11 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.2⟩
  have h2_ES : EdgesAt st2.mem eSAddr act.edges := by
    rw [heAct]
    have hm : ∀ i < 2 * eS, st2.mem (eSAddr + i) = st1.mem (eSAddr + i) := fun i hi => by
      have heS_le_e : eS ≤ e := List.length_filter_le _ _
      exact h2_fr (eSAddr + i)
        (fun u hu => by have := hiso_ltN u hu; have := env.hlblH; omega)
        (by have := env.hnextH; omega)
        (by rcases hdAct_E with h | h
            · exact Or.inr (by omega)
            · exact Or.inl (by omega))
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [hm (2 * i) (by omega)]; exact (h1_ES i hi).1
    · rw [Nat.add_assoc, hm (2 * i + 1) (by omega), ← Nat.add_assoc]; exact (h1_ES i hi).2
  have h2_loc0 : ∀ u < G.n, st2.mem (locAddr + u) = 0 := fun u hu => by
    rw [h2_fr (locAddr + u)
          (fun v hv => by have := hiso_ltN v hv; rcases env.hdLLb with h | h <;> omega)
          (by rcases env.hdLN with h | h <;> omega)
          (Or.inl (by have := env.hlocH; omega))]
    exact h1_loc0 u hu
  have h2_zero : ZeroFrom st2.mem hCur := fun a ha => by
    rw [h2_fr a (fun v hv => by have := hiso_ltN v hv; have := env.hlblH; omega)
          (by have := env.hnextH; omega) (Or.inr (by omega)),
        h1_fr a (Or.inr (by omega))]
    exact hZero a ha
  -- 3. Recursive call `bSelf` on `act`
  have hact_sorted : act.verts.Pairwise (· < ·) :=
    pairwise_lt_filter (pairwise_lt_filter hSorted _) _
  have hact_subS : act.vertSet ⊆ S := by rw [← hstS.2.2.1]; exact Finset.subset_union_right
  have hlen_split : iso.length + act.verts.length = kS := by
    have h1 := congrArg Finset.card hstS.2.2.1
    rw [Finset.card_union_of_disjoint hstS.2.1, List.toFinset_card_of_nodup hstS.1] at h1
    dsimp only [CompactSubgraph.vertSet] at h1
    rw [List.toFinset_card_of_nodup hstS.2.2.2.2.1.1, ← hrepS.2.1,
        List.toFinset_card_of_nodup hrepS.1] at h1
    exact h1
  have hact_len_le : act.verts.length ≤ kS := by omega
  let vs3 := [act.verts.length, actSAddr, act.edges.length, eSAddr,
    paramAddr, locAddr, labelsAddr, nextLblAddr, hCur]
  have hSelf_IH := hIH act actSAddr eSAddr hCur (nl₀ + iso.length) (startState vs3 st2.mem st2.pos)
    (by rw [heAct_len]; exact heS_le) hstS.2.2.2.2.1 ((hact_subS.trans hSX).trans hXV)
    hact_sorted hstS.2.2.2.2.2.2.1 (by rw [heAct_len]; exact heS_M) hRoot_le
    (by omega) (by rw [heAct_len]; omega)
    (Or.inl (by have := env.hlocH; omega)) (Or.inl (by have := env.hlblH; omega))
    (Or.inl (by have := env.hnextH; omega))
    (Or.inl (by have := env.hlocH; omega)) (Or.inl (by have := env.hlblH; omega))
    (Or.inl (by have := env.hnextH; omega))
    h2_PB h2_actV h2_ES h2_loc0 h2_nl (by omega) h2_zero
    (by rw [heAct_len]; exact hSp)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rcases hSelf_IH with ⟨hEnd, st3_in, c3_in, hrun3_in, hpost3⟩
  rcases hpost3 with ⟨o, hoSpec, hoLbl, hoNl, hh_le, hh_hi, hZero3, hloc3, h3_fr, hc3_in⟩
  let stEnd : State := { st3_in with regs := Function.update st2.regs rH hEnd }
  have hrun3 : Runs w pProg ω
      (.call rH idx.bSelf
        [.reg rStrip, .reg rAct, .reg rRest, .reg rE, .reg 4, .reg 5, .reg 6, .reg 7, .reg rH])
      st2 .normal stEnd (argsSize [.reg rStrip, .reg rAct, .reg rRest, .reg rE, .reg 4, .reg 5, .reg 6, .reg 7, .reg rH] + c3_in + 1) := by
    refine runs_call_iff.mpr ⟨vs3, outerDecompRecProc idx, .returned hEnd, st3_in, c3_in, ?_, hSub.hSelf,
      hrun3_in, rfl, rfl, rfl⟩
    simp only [evalArgs, Expr.eval, vs3, h2_rStrip, hv2_eq,
      h2_other rAct hrStrip_ne.2.2.2.1.symm, h1_other rAct hrRest_ne.2.2.2.1.symm, hrAct,
      h2_other rRest hrRest_ne.2.2.2.2.1, h1_rRest, hv1_eq, heAct_len,
      h2_other rE hrStrip_ne.2.2.1.symm, h1_other rE hrRest_ne.2.2.1.symm, hrE,
      h2_other 4 (by omega), h1_other 4 (by omega), hr4,
      h2_other 5 (by omega), h1_other 5 (by omega), hr5,
      h2_other 6 (by omega), h1_other 6 (by omega), hr6,
      h2_other 7 (by omega), h1_other 7 (by omega), hr7,
      h2_other rH hrStrip_ne.2.2.2.2.1.symm, h1_other rH hrRest_ne.2.2.2.2.2.1.symm, hrH]; rfl
  have hrunAll := runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
    runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2, hrun3, rfl⟩), rfl⟩)
  -- LabelsMatchParts on `S = iso.toFinset ∪ act.vertSet`
  have hIsoLbl_end : LabelsMatchParts stEnd.mem labelsAddr iso.toFinset
      (iso.map fun v => ({v} : Finset ℕ)) nl₀ (nl₀ + iso.length) := by
    refine labelsMatchParts_singleton_list fun u hu => ?_
    dsimp only [stEnd]
    rw [h3_fr (labelsAddr + u) (by have := hiso_ltN u hu; have := env.hlblH; omega)
          (fun v hv => by
            have huv : u ≠ v := fun h =>
              Finset.disjoint_left.mp hstS.2.1 (List.mem_toFinset.mpr hu) (h ▸ hv)
            omega)
          (by have := hiso_ltN u hu; rcases env.hdLbN with h | h <;> omega)]
    exact h2_isoLbl u hu
  have hSLbl : LabelsMatchParts stEnd.mem labelsAddr S
      ((iso.map fun v => ({v} : Finset ℕ)) ++ o.parts) nl₀ (stEnd.mem nextLblAddr) := by
    rw [← hstS.2.2.1]
    exact labelsMatchParts_union hstS.2.1 hIsoLbl_end hoLbl
  refine ⟨stEnd, hEnd, _, o, hrunAll, hoSpec, hSLbl, by dsimp only [stEnd]; omega,
    hh_le, hh_hi, hZero3, hloc3, ?_, by simp [stEnd], ?_, ?_⟩
  · intro a ha haE haAct haS haN
    dsimp only [stEnd]
    rw [h3_fr a ha (fun u hu => haS u (hact_subS hu)) haN]
    dsimp only [startState]
    rw [h2_fr a (fun u hu => haS u (hiso_subS u hu)) haN haAct,
        h1_fr a haE]
  · intro r' h1 h2 h3
    dsimp only [stEnd]
    rw [Function.update_of_ne h3, h2_other r' h2, h1_other r' h1]
  · simp only [argsSize, Expr.size, restrictCost, stripIsolatedCost, Nat.add_zero] at hc1 hc2 ⊢
    omega


end MinCostFlow.ExpanderDecomp
