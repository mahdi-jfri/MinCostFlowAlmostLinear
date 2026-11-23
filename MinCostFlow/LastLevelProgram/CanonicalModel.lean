module

public import MinCostFlow.LastLevelProgram.QueryFit
public import MinCostFlow.LastLevelProgram.QueryFormat
public import MinCostFlow.LastLevelProgram.Spec
public import MinCostFlow.LastLevelProgram.RelocatedOracle
public import MinCostFlow.LastLevelProgram.StagedGuestWeights
import MinCostFlow.LSF.Theorem22
import MinCostFlow.Num.ModulePlacement

/-!
# Last-level correctness with the machine tree oracle

For Definition 5.8 (pages 19–20), apply the rounded potential to the
trees from Theorem 2.2 (page 7). The prefix invariant pays for the
numeric fit premise before each call.
-/

public section

namespace MinCostFlow.LastLevelProgram

open LSF SparseCore WordRAM Num
open scoped BigOperators

/-- The queried representative graph and its safe lengths and weights
meet the fixed-point LSST call premises at every live round. -/
theorem representativeRound_queryFit
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (L P j : ℕ)
    (hG : G.IsValid) (hℓ : ∀ e ∈ G.E, 0 < ℓ e)
    (hgrid : ∀ e ∈ G.E, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P)
    (hlenFit : ∀ e ∈ G.E, Fits 1 L (queryNumerator P (ℓ e))) :
    let H := representativeGraph G ℓ
    let v := weights (weightPrecision C H) (roundedScale C H)
      (stretchQuery oracle H ℓ (weightPrecision C H)) j
    weightPrecision C H ≤ P →
    2 * (2 : ℝ)^P * (2 * (H.m : ℝ)) < capacity 1 L →
    j < lastMWUK H → (∀ e ∈ H.E, 1 ≤ v e) → (∑ e ∈ H.E, v e) ≤ 2 * H.m →
    H.IsValid ∧ H.V.Nonempty ∧
      (∀ e ∈ H.E, 0 < queryNumerator P (safeLen H ℓ e) ∧
        Fits 1 L (queryNumerator P (safeLen H ℓ e))) ∧
      (∀ e ∈ H.E, 0 < queryNumerator P (v e) ∧ Fits 1 L (queryNumerator P (v e))) ∧
      (∀ e, ∃ a : ℤ, safeLen H ℓ e = (a : ℝ) / (2 : ℝ)^P) ∧
      (∀ e, ∃ a : ℤ, v e = (a : ℝ) / (2 : ℝ)^P) := by
  intro H v hprecision hwidth hj hv hsum
  have hsub := representativeGraph_subgraph hG ℓ
  have hvalid := representativeGraph_valid G ℓ
  have hm : H.m ≠ 0 := by
    intro hz
    have hzero : lastMWUK H = 0 := by simp [lastMWUK, hz]
    exact (Nat.not_lt_zero j) (hzero ▸ hj)
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hm)
  have hne : H.V.Nonempty := ⟨H.tail e, (hvalid e he).1⟩
  have hsafeFit : ∀ f ∈ H.E,
      0 < queryNumerator P (safeLen H ℓ f) ∧ Fits 1 L (queryNumerator P (safeLen H ℓ f)) := by
    intro f hf
    have hfG := hsub.2.1 hf
    rw [safeLen_eq_of_mem ℓ hf]
    refine ⟨?_, hlenFit f hfG⟩
    have hpos := hℓ f hfG
    obtain ⟨a, ha⟩ := hgrid f hfG
    rw [ha, queryNumerator_grid]
    rw [ha] at hpos
    exact_mod_cast (div_pos_iff_of_pos_right (by positivity)).mp hpos
  have hsafeGrid : ∀ f, ∃ a : ℤ, safeLen H ℓ f = (a : ℝ) / (2 : ℝ)^P := by
    intro f
    by_cases hf : f ∈ H.E
    · rw [safeLen_eq_of_mem ℓ hf]
      exact hgrid f (hsub.2.1 hf)
    · exact ⟨0, by simp [safeLen, hf]⟩
  obtain ⟨hweightFit, hweightGrid⟩ :=
    roundWeights_fit oracle C H ℓ L P j hprecision hwidth hv hsum
  exact ⟨hvalid, hne, hsafeFit, hweightFit, hsafeGrid, hweightGrid⟩

/-- The rounded last-level model meets its specification on fitting
lengths when the oracle reads the canonical LSST program output. -/
theorem canonicalModel_spec :
    ∃ K : ℝ, ∀ L P : ℕ, ∃ oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph,
      let C := 4 * max K 1 + 5
      let params := lastLevelParams (128 * max 1 C)
      let tool := fixedPointLastLevelTool oracle C
      ∀ (G : MGraph) (ℓ : ℕ → ℝ),
        G.IsValid → (∀ e ∈ G.E, 0 < ℓ e) → 1 ≤ L →
        (∀ e ∈ G.E, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P) →
        (∀ e ∈ G.E, Fits 1 L (queryNumerator P (ℓ e))) →
        weightPrecision C (representativeGraph G ℓ) ≤ P →
        2 * (2 : ℝ)^P * (2 * ((representativeGraph G ℓ).m : ℝ)) < capacity 1 L →
        let res := tool.build G ℓ
        0 < res.1 ∧
        (∀ j < res.1, (res.2 j).Holds G ℓ (params.σ_last G.n)) ∧
        (∀ e ∈ G.E,
          (∑ j ∈ Finset.range res.1, (res.2 j).wstr e) / (res.1 : ℝ) ≤ params.σ_mwu G.n) ∧
        (∀ j < res.1, ∀ u ∈ G.V, ∀ v ∈ G.V,
          G.Connected u v → (res.2 j).F.F.Connected u v) ∧
        ((tool.cost G : ℝ) ≤ params.c_last * ((G.m : ℝ) + 1)^2 *
          (Real.log ((G.m : ℝ) + (G.n : ℝ) + 2))^params.p_last) := by
  obtain ⟨_, _, K, _, hOracle⟩ := exists_relocatedTreeOracle
  refine ⟨K, ?_⟩
  intro L P
  obtain ⟨oracle, hcall⟩ := hOracle L P
  refine ⟨oracle, ?_⟩
  intro C params tool G ℓ hG hℓ hL hgrid hlenFit hprecision hwidth
  apply fixedPointLastLevelTool_spec oracle C G ℓ hG hℓ
  let H := representativeGraph G ℓ
  dsimp only
  intro j hj hv hsum
  let v := weights (weightPrecision C H) (roundedScale C H)
    (stretchQuery oracle H ℓ (weightPrecision C H)) j
  obtain ⟨hvalid, hne, hsafeFit, hweightFit, hsafeGrid, hweightGrid⟩ :=
    representativeRound_queryFit oracle C G ℓ L P j hG hℓ hgrid hlenFit
      hprecision hwidth hj hv hsum
  obtain ⟨_, _, _, _, htree, _, _⟩ :=
    hcall H (safeLen H ℓ) v hvalid hne hL hsafeFit hweightFit hsafeGrid hweightGrid
  exact htree

/-- The graph-derived format supplies all oracle premises on a dyadic
last-level input, regardless of the caller's representation. -/
theorem representativeRound_graphQueryFit
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (j : ℕ)
    (hG : G.IsValid) (hℓ : ∀ e ∈ G.E, 0 < ℓ e)
    (hgrid : ∃ Q, ∀ e ∈ G.E, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^Q) :
    let H := representativeGraph G ℓ
    let len := safeLen H ℓ
    let P := roundQueryPrecision C H len
    let L := roundQueryLimbs C H len
    let v := weights (weightPrecision C H) (roundedScale C H)
      (stretchQuery oracle H ℓ (weightPrecision C H)) j
    j < lastMWUK H → (∀ e ∈ H.E, 1 ≤ v e) → (∑ e ∈ H.E, v e) ≤ 2 * H.m →
    H.IsValid ∧ H.V.Nonempty ∧ 1 ≤ L ∧
      (∀ e ∈ H.E, 0 < queryNumerator P (len e) ∧ Fits 1 L (queryNumerator P (len e))) ∧
      (∀ e ∈ H.E, 0 < queryNumerator P (v e) ∧ Fits 1 L (queryNumerator P (v e))) ∧
      OnQueryGrid P len ∧ OnQueryGrid P v := by
  intro H len P L v hj hv hsum
  have hvalid := representativeGraph_valid G ℓ
  have hsub := (representativeGraph_subgraph hG ℓ).2.1
  have hne : H.V.Nonempty := by
    have hm : 0 < H.m := by
      by_contra! hz
      have hzero : lastMWUK H = 0 := by simp [lastMWUK, Nat.eq_zero_of_le_zero hz]
      exact (Nat.not_lt_zero j) (hzero ▸ hj)
    obtain ⟨e,he⟩ := Finset.card_pos.mp hm
    exact ⟨H.tail e,(hvalid e he).1⟩
  have hs : ∃ Q, OnQueryGrid Q len := by
    obtain ⟨Q,hQ⟩ := hgrid
    refine ⟨Q,fun e => ?_⟩
    by_cases he : e ∈ H.E
    · change ∃ a : ℤ, safeLen H ℓ e = (a : ℝ) / (2 : ℝ)^Q
      rw [safeLen_eq_of_mem ℓ he]
      exact hQ e (hsub he)
    · exact ⟨0,by simp [len,safeLen,he]⟩
  have hlen : OnQueryGrid P len := (lengthQueryPrecision_exact hs).mono (le_max_right ..)
  have hwt := roundWeights_fit oracle C H ℓ L P j (le_max_left ..)
    (roundQueryLimbs_weightCapacity C H len) hv hsum
  refine ⟨hvalid,hne,Nat.succ_le_succ (Nat.zero_le _),?_,hwt.1,hlen,hwt.2⟩
  intro e he
  have hpos : 0 < len e := by
    change 0 < safeLen H ℓ e
    rw [safeLen_eq_of_mem ℓ he]
    exact hℓ e (hsub he)
  obtain ⟨a,ha⟩ := hlen e
  have hn : 0 < queryNumerator P (len e) := by
    rw [ha,queryNumerator_grid]
    rw [ha] at hpos
    exact_mod_cast (div_pos_iff_of_pos_right (by positivity)).mp hpos
  exact ⟨hn,graphQueryLimbs_length he hn.le⟩

/-- One last-level tool meets the rounded specification on all dyadic
inputs using the same relocated LSST program and oracle. -/
theorem graphCanonicalModel_spec :
    ∃ K : ℝ, ∃ oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph,
      let C := 4 * max K 1 + 5
      let params := lastLevelParams (128 * max 1 C)
      let tool := fixedPointLastLevelTool oracle C
      ∀ (G : MGraph) (ℓ : ℕ → ℝ),
        G.IsValid → (∀ e ∈ G.E, 0 < ℓ e) →
        (∃ Q, ∀ e ∈ G.E, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^Q) →
        let res := tool.build G ℓ
        0 < res.1 ∧
        (∀ j < res.1, (res.2 j).Holds G ℓ (params.σ_last G.n)) ∧
        (∀ e ∈ G.E,
          (∑ j ∈ Finset.range res.1, (res.2 j).wstr e) / (res.1 : ℝ) ≤ params.σ_mwu G.n) ∧
        (∀ j < res.1, ∀ u ∈ G.V, ∀ v ∈ G.V,
          G.Connected u v → (res.2 j).F.F.Connected u v) ∧
        ((tool.cost G : ℝ) ≤ params.c_last * ((G.m : ℝ) + 1)^2 *
          (Real.log ((G.m : ℝ) + (G.n : ℝ) + 2))^params.p_last) := by
  obtain ⟨_,_,K,_,oracle,hcall⟩ := exists_graphRelocatedTreeOracle
    (fun K => roundQueryLimbs (4 * max K 1 + 5))
    (fun K => roundQueryPrecision (4 * max K 1 + 5))
  refine ⟨K,oracle,?_⟩
  intro C params tool G ℓ hG hℓ hgrid
  apply fixedPointLastLevelTool_spec oracle C G ℓ hG hℓ
  dsimp only
  intro j hj hv hsum
  obtain ⟨hvalid,hne,hL,hlen,hwt,hgridLen,hgridWt⟩ :=
    representativeRound_graphQueryFit oracle C G ℓ j hG hℓ hgrid hj hv hsum
  obtain ⟨_,_,_,_,htree,_,_⟩ := hcall (representativeGraph G ℓ)
    (safeLen (representativeGraph G ℓ) ℓ) _ hvalid hne hL hlen hwt hgridLen hgridWt
  exact htree

/-- The exact numeric domain on which the graph-derived guest encodes a query. -/
@[expose] def GraphQueryReady (C : ℝ) (G : MGraph) (len wt : ℕ → ℝ) : Prop :=
  let P := roundQueryPrecision C G len
  let L := roundQueryLimbs C G len
  G.IsValid ∧ G.V.Nonempty ∧ 1 ≤ L ∧
    (∀ e ∈ G.E, 0 < queryNumerator P (len e) ∧ Fits 1 L (queryNumerator P (len e))) ∧
    (∀ e ∈ G.E, 0 < queryNumerator P (wt e) ∧ Fits 1 L (queryNumerator P (wt e))) ∧
    OnQueryGrid P len ∧ OnQueryGrid P wt

/-- Extend the machine oracle to the real-valued specification by using
the mathematical Theorem 2.2 on queries outside the guest domain. -/
noncomputable def extendGraphOracle (C : ℝ)
    (machine fallback : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (len wt : ℕ → ℝ) : MGraph :=
  open Classical in
  if GraphQueryReady C G len wt then machine G len wt else fallback G len wt

/-- A fitting query uses the machine tree. -/
theorem extendGraphOracle_eq_machine {C : ℝ}
    {machine fallback : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph}
    {G : MGraph} {len wt : ℕ → ℝ} (h : GraphQueryReady C G len wt) :
    extendGraphOracle C machine fallback G len wt = machine G len wt := by
  classical
  unfold extendGraphOracle
  exact ite_eq_left h

/-- The live rounds of a dyadic input use the machine tree. -/
theorem representativeRound_graphQueryReady
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (j : ℕ)
    (hG : G.IsValid) (hℓ : ∀ e ∈ G.E, 0 < ℓ e)
    (hgrid : ∃ Q, ∀ e ∈ G.E, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^Q) :
    let H := representativeGraph G ℓ
    let v := weights (weightPrecision C H) (roundedScale C H)
      (stretchQuery oracle H ℓ (weightPrecision C H)) j
    j < lastMWUK H → (∀ e ∈ H.E, 1 ≤ v e) → (∑ e ∈ H.E, v e) ≤ 2 * H.m →
    GraphQueryReady C H (safeLen H ℓ) v :=
  representativeRound_graphQueryFit oracle C G ℓ j hG hℓ hgrid

/-- The stretch constant covers the relocated LSST and the fallback. -/
noncomputable def graphCanonicalConstant (K fallback : ℝ) : ℝ :=
  max (4 * max K 1 + 5) fallback

/-- The fixed program uses this natural constant in the integer scale. -/
noncomputable def graphCanonicalIntegerConstant (K fallback : ℝ) : ℕ :=
  ⌈graphCanonicalConstant K fallback⌉₊

/-- The compiled constant is exactly the integer constant of the model's scale. -/
theorem graphCanonicalIntegerConstant_eq (K fallback : ℝ) :
    graphCanonicalIntegerConstant K fallback = ⌈max 1 (graphCanonicalConstant K fallback)⌉₊ := by
  have hK : (1 : ℝ) ≤ max K 1 := le_max_right ..
  have hc : (1 : ℝ) ≤ graphCanonicalConstant K fallback := by
    unfold graphCanonicalConstant
    exact (show (1 : ℝ) ≤ 4*max K 1+5 by linarith).trans (le_max_left ..)
  rw [max_eq_right hc]
  rfl

/-- The model and its executable tree selector share one guest program
and one oracle. Every fitting query exposes the matching compact tree
and the relocated call that returns it. -/
theorem graphCanonicalModel_withProgram :
    ∃ (guest : Program) (c₀ : ℕ) (K Cf : ℝ), 1 ≤ c₀ ∧
      ∃ (machine oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph),
      let C := graphCanonicalConstant K Cf
      HasLSSTSpec oracle C ∧
      (fixedPointLastLevelTool oracle C).IsSpec (lastLevelParams (128 * max 1 C)) ∧
      ∀ G len wt, GraphQueryReady C G len wt →
        let L := roundQueryLimbs C G len
        let P := roundQueryPrecision C G len
        ∃ (tree : MGraph) (guestCost : ℕ),
          oracle G len wt = machine G len wt ∧
          machine G len wt = restoreTreeNames G tree ∧
          IsLSST (indexedGraph G).toMGraph (len ∘ edgeName G) (wt ∘ edgeName G)
            ((4*max K 1+5)*Real.log (↑G.n+2)^2) tree ∧
          (guestCost : ℝ) ≤ 16000 * ((G.m+G.n+1 : ℕ) : ℝ) *
            WideWord.lsstOverheadFactor guest c₀ K G.n G.m L ∧
          ∀ (host : Program) (b hostWidth heap src D : ℕ),
            let sim := WideWord.lsstLSimMin c₀ G.n G.m L 1
            let w := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
            host.HasAt b (relocatedTreeProcedures guest b) → max K 0 ≤ (D : ℝ) →
            w ≤ hostWidth → heap+1+2^w ≤ 2^hostWidth → 4 ≤ 2^hostWidth →
            MeetsContract hostWidth host b
              (relocatedTreeAtWidthContract guest c₀ w G L (queryNumerator P ∘ len)
                (queryNumerator P ∘ wt) heap src guestCost tree) := by
  classical
  obtain ⟨fallback,Cf,hfallback⟩ := theorem_2_2
  obtain ⟨guest,c₀,K,hc₀,machine,hcall⟩ := exists_graphRelocatedTreeOracle
    (fun K => roundQueryLimbs (graphCanonicalConstant K Cf))
    (fun K => roundQueryPrecision (graphCanonicalConstant K Cf))
  let C := graphCanonicalConstant K Cf
  let oracle := extendGraphOracle C machine fallback
  have hOracle : HasLSSTSpec oracle C := by
    intro G len wt hG hV hlen hwt
    have grow (A : ℝ) (hA : A ≤ C) (T : MGraph)
        (ht : IsLSST G len wt (A * Real.log ((G.n : ℝ)+2)^2) T) :
        IsLSST G len wt (C * Real.log ((G.n : ℝ)+2)^2) T := by
      obtain ⟨hst,he,hpath,hsum⟩ := ht
      refine ⟨hst,he,hpath,hsum.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (sq_nonneg _))
        (Finset.sum_nonneg fun e _ => abs_nonneg (wt e))
    by_cases h : GraphQueryReady C G len wt
    · rw [show oracle G len wt = machine G len wt from extendGraphOracle_eq_machine h]
      obtain ⟨hG',hV',hL,hl,hw,hlGrid,hwGrid⟩ := h
      obtain ⟨_,_,_,_,ht,_,_⟩ := hcall G len wt hG' hV' hL hl hw hlGrid hwGrid
      exact grow _ (show 4*max K 1+5 ≤ C from le_max_left ..) _ ht
    · have he : oracle G len wt = fallback G len wt := by simp [oracle,extendGraphOracle,h]
      rw [he]
      exact grow _ (show Cf ≤ C from le_max_right ..) _ (hfallback G len wt hG hV hlen hwt)
  refine ⟨guest,c₀,K,Cf,hc₀,machine,oracle,hOracle,
    fixedPointLastLevelTool_isSpec oracle C hOracle,?_⟩
  intro G len wt h
  have hReady := h
  obtain ⟨hG,hV,hL,hl,hw,hlGrid,hwGrid⟩ := h
  obtain ⟨tree,cost,he,ht,_,hc,hr⟩ := hcall G len wt hG hV hL hl hw hlGrid hwGrid
  exact ⟨tree,cost,extendGraphOracle_eq_machine hReady,he,ht,hc,hr⟩

/-- The constant installed for the canonical update scale also bounds
the cited algorithm's workspace constant for the runtime selector. -/
theorem graphCanonicalIntegerConstant_selectorBounds (K fallback : ℝ) :
    0 < graphCanonicalIntegerConstant K fallback ∧
      max K 0 ≤ (graphCanonicalIntegerConstant K fallback : ℝ) := by
  have hC : max K 1 ≤ graphCanonicalConstant K fallback := by
    unfold graphCanonicalConstant
    exact (show max K 1 ≤ 4*max K 1+5 by
      linarith only [le_max_right K (1 : ℝ)]).trans (le_max_left _ _)
  have hn : graphCanonicalConstant K fallback ≤
      (graphCanonicalIntegerConstant K fallback : ℝ) := Nat.le_ceil _
  have hone : (1 : ℝ) ≤ (graphCanonicalIntegerConstant K fallback : ℝ) :=
    (le_max_right K (1 : ℝ)).trans (hC.trans hn)
  exact ⟨by exact_mod_cast (zero_lt_one.trans_le hone),
    (max_le_max (le_refl K) zero_le_one).trans (hC.trans hn)⟩

/-- The runtime selector converts the caller's weight blocks before
running the relocated low-stretch tree program. -/
@[expose] def packedTreeSelectorModule (guest : Program) (D b : ℕ) : List Stmt :=
  [selectAndQueryConvertedTreeBody guest (b+1) (b+4) (b+10),
   selectPaddedGuestWidthBody (b+2) (b+3),guestWorkspaceBody guest D (b+9),
   paddedGuestWidthBody (b+9),packGuestStridedBody (b+5),
   conversionBlockBody (b+6),storeConversionBitBody (b+7),conversionBitBody (b+8),
   formatBitBody] ++
    (Scaling.Machine.clogTwoModule (b+9) ++ relocatedTreeProcedures guest (b+10))

/-- Installing the selector provides the weight conversion contract
and the relocated tree program at the fixed call addresses. -/
theorem packedTreeSelectorModule_entries {p guest : Program} {D b : ℕ}
    (hp : p.HasAt b (packedTreeSelectorModule guest D b)) (w : ℕ) :
    p.procs[b]? = some (selectAndQueryConvertedTreeBody guest (b+1) (b+4) (b+10)) ∧
    p.procs[b+1]? = some (selectPaddedGuestWidthBody (b+2) (b+3)) ∧
    p.procs[b+2]? = some (guestWorkspaceBody guest D (b+9)) ∧
    p.procs[b+3]? = some (paddedGuestWidthBody (b+9)) ∧
    p.procs[b+4]? = some (packGuestStridedBody (b+5)) ∧
    MeetsContract w p (b+5) (conversionBlockContract w) ∧
    p.HasAt (b+9) (Scaling.Machine.clogTwoModule (b+9)) ∧
    p.HasAt (b+10) (relocatedTreeProcedures guest (b+10)) := by
  unfold packedTreeSelectorModule at hp
  have hfront := Num.hasAt_append_left hp
  have hback := Num.hasAt_append_right hp
  have hconversion := conversionBlock_meetsContract (w := w)
    (hfront.get (i := 5) (show 5 < 9 by decide))
    (storeConversionBit_meetsContract (hfront.get (i := 6) (show 6 < 9 by decide))
      (conversionBit_meetsContract (hfront.get (i := 7) (show 7 < 9 by decide))
        (formatBit_meetsContract (hfront.get (i := 8) (show 8 < 9 by decide)))))
  exact ⟨hfront.head,hfront.get (i := 1) (show 1 < 9 by decide),hfront.get (i := 2) (show 2 < 9 by decide),
    hfront.get (i := 3) (show 3 < 9 by decide),hfront.get (i := 4) (show 4 < 9 by decide),hconversion,
    Num.hasAt_append_left hback,Num.hasAt_append_right hback⟩

/-- One fixed-point model supplies the selector contract for every fitting
query of Definition 5.8 (pages 19–20). -/
theorem graphCanonicalModel_withSelector :
    ∃ (guest : Program) (c₀ : ℕ) (K Cf : ℝ)
      (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph),
      1 ≤ c₀ ∧
      let C := graphCanonicalConstant K Cf
      let D := graphCanonicalIntegerConstant K Cf
      HasLSSTSpec oracle C ∧
      (fixedPointLastLevelTool oracle C).IsSpec (lastLevelParams (128 * max 1 C)) ∧
      ∀ G len wt, 0 < G.n → 0 < G.m → GraphQueryReady C G len wt →
        let L := roundQueryLimbs C G len
        let Q := roundQueryPrecision C G len
        let sim := WideWord.lsstLSimMin c₀ G.n G.m L 1
        ∃ (tree : MGraph) (guestCost : ℕ),
          oracle G len wt = restoreTreeNames G tree ∧
          IsLSST (indexedGraph G).toMGraph (len ∘ edgeName G) (wt ∘ edgeName G)
            ((4*max K 1+5)*Real.log (↑G.n+2)^2) tree ∧
          (guestCost : ℝ) ≤ 16000 * ((G.m+G.n+1 : ℕ) : ℝ) *
            WideWord.lsstOverheadFactor guest c₀ K G.n G.m L ∧
          ∀ (p : Program) (w selector staging src stride hostL P : ℕ),
            p.HasAt selector (packedTreeSelectorModule guest D selector) →
            staging+queryOriginals G L+1+
              2^paddedGuestWidth guest D G.n G.m sim (queryHeap G L) ≤ 2^w →
            MeetsContract w p selector
              (convertedTreeSelectorContract w guest D G tree L sim staging guestCost src stride
                hostL P Q (queryNumerator Q ∘ len) (queryNumerator Q ∘ wt)) := by
  obtain ⟨guest,c₀,K,Cf,hc,machine,oracle,hOracle,hspec,hquery⟩ := graphCanonicalModel_withProgram
  refine ⟨guest,c₀,K,Cf,oracle,hc,hOracle,hspec,?_⟩
  intro G len wt hn hm hready L Q sim
  obtain ⟨tree,cost,ho,ht,hs,hcost,hcall⟩ := hquery G len wt hready
  refine ⟨tree,cost,ho.trans ht,hs,hcost,?_⟩
  intro p w selector staging src stride hostL P hp hspace
  let D := graphCanonicalIntegerConstant K Cf
  obtain ⟨hD,hK⟩ := graphCanonicalIntegerConstant_selectorBounds K Cf
  obtain ⟨he,hselect,hwork,hpadded,hconvert,hblock,hlog,htree⟩ :=
    packedTreeSelectorModule_entries hp w
  have hL : 0 < L := hready.2.2.1
  exact selectAndQueryConvertedTree_meetsContract guest G tree L staging cost src stride
    hostL P Q _ _ he hn hm hL hD hc hselect hwork hpadded hlog hconvert hblock htree hK hspace
    (hcall p (selector+10) w (staging+queryOriginals G L) staging D)

/-- A single graph-formatted tool satisfies the full shared specification.
On fitting queries its oracle agrees with the relocated machine oracle. -/
theorem graphCanonicalModel_isSpec :
    ∃ (C : ℝ) (machine oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph),
      (∀ G len wt, GraphQueryReady C G len wt → oracle G len wt = machine G len wt) ∧
      (fixedPointLastLevelTool oracle C).IsSpec (lastLevelParams (128 * max 1 C)) := by
  obtain ⟨_,_,K,Cf,_,machine,oracle,_,hspec,hcall⟩ := graphCanonicalModel_withProgram
  exact ⟨graphCanonicalConstant K Cf,machine,oracle,
    fun G len wt h => by
      obtain ⟨_,_,he,_,_,_,_⟩ := hcall G len wt h
      exact he,hspec⟩

end MinCostFlow.LastLevelProgram
