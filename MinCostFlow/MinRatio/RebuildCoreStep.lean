module

public import MinCostFlow.MinRatio.RebuildGradients
import MinCostFlow.MinRatio.RebuildModelSuffix
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.LSF.Walks
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith

/-!
# One complete Rebuild suffix iteration

Algorithm 1 (page 20) reads out the selected forest, prepares the
next level's numbers and advances the loop cursors.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Each root-potential path uses a subset of the forest edges once.
A uniform edge-gradient bound therefore scales by the forest edge count. -/
theorem rebuildRootPotential_abs_le {F : MGraph} {grad : ℕ → ℝ} {B : ℝ}
    (hF : F.IsForest) (hB : 0 ≤ B) (hgrad : ∀ e ∈ F.E, |grad e| ≤ B) (v : ℕ) :
    |treeRootPot F grad v| ≤ F.m * B := by
  let path := F.forestPath v (compRoot F v)
  have hp : F.IsPath v (compRoot F v) path := LSF.forestPath_isPath hF (connected_compRoot F v)
  have hsub : walkEdges path ⊆ F.E := by
    intro e he
    rw [walkEdges, List.mem_toFinset] at he
    obtain ⟨step, hs, rfl⟩ := List.mem_map.mp he
    exact MGraph.isWalk_edges_mem hp.1 step hs
  change |walkInner grad path| ≤ _
  unfold walkInner
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _e ∈ walkEdges path, B := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul, LSF.walkFlow_abs_of_nodup (LSF.isPath_nodup_edges hp), ite_eq_left he, mul_one]
      exact hgrad e (hsub he)
    _ ≤ F.m * B := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hB

/-- The gradients passed from a rebuilt core grow by at most
(2m_F + 1) when the next graph keeps names from the current graph. -/
theorem rebuildCoreGrad_abs_le {G H : MGraph} {forest : LSF} {grad : ℕ → ℝ} {B : ℝ}
    (hF : forest.T.IsForest) (hFsub : forest.T.E ⊆ G.E) (hH : H.E ⊆ G.E)
    (hB : 0 ≤ B) (hgrad : ∀ e ∈ G.E, |grad e| ≤ B) :
    ∀ e ∈ H.E, |coreGrad G forest grad e| ≤ (2 * (forest.T.m : ℝ) + 1) * B := by
  intro e he
  rw [coreGrad]
  refine (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  have hh := rebuildRootPotential_abs_le hF hB (fun a ha => hgrad a (hFsub ha)) (G.head e)
  have ht := rebuildRootPotential_abs_le hF hB (fun a ha => hgrad a (hFsub ha)) (G.tail e)
  have hg := hgrad e (hH he)
  linarith only [hh, ht, hg]

/-- Along a periodic Rebuild suffix, a uniform forest size cap
bounds the growth in gradient magnitudes at every reconstructed level. -/
theorem rebuildSuffix_gradient_abs_le
    (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (chain : ChainState T P) (first : Fin P.d) (Gnew : MGraph) (enc cap : ℕ)
    (B : ℝ) (hB : 0 ≤ B) :
    let next := (algorithm1_rebuild T L P chain first.val Gnew enc).1
    (∀ e ∈ Gnew.E, |chain.toTreeChain.chainGrad chain.g first.val e| ≤ B) →
    (∀ j, first.val ≤ j → j < P.d →
      let forest := T.lsfs (next.scState j) 0
      forest.T.IsForest ∧ forest.T.E ⊆ (next.G j).E ∧
        (next.G (j + 1)).E ⊆ (next.G j).E ∧ forest.T.m ≤ cap) →
    ∀ n, first.val + n ≤ P.d → ∀ e ∈ (next.G (first.val + n)).E,
      |next.toTreeChain.chainGrad chain.g (first.val + n) e| ≤ (2 * (cap : ℝ) + 1) ^ n * B := by
  dsimp only
  intro hin hstep n
  let next := (algorithm1_rebuild T L P chain first.val Gnew enc).1
  have hfactor : (0 : ℝ) ≤ 2 * (cap : ℝ) + 1 := by positivity
  induction n with
  | zero =>
    intro _ e he
    obtain ⟨hG, _, hg⟩ := algorithm1_rebuild_entry T L P chain first Gnew enc
    simp only [Nat.add_zero, hG] at he
    simpa only [Nat.add_zero, pow_zero, one_mul, hg] using hin e he
  | succ n ih =>
    intro hlast e he
    have hj : first.val + n < P.d := by omega
    obtain ⟨hf, hsub, hnext, hcap⟩ := hstep (first.val + n) (by omega) hj
    have hrec := (rebuildSuffix_nextLevelNumbers T L P chain first.val (first.val + n)
      (by omega) hj Gnew enc).2
    simp only [Nat.add_succ] at he ⊢
    rw [hrec]
    have hn : 0 ≤ (2 * (cap : ℝ) + 1) ^ n * B := mul_nonneg (pow_nonneg hfactor _) hB
    have hm := rebuildCoreGrad_abs_le hf hsub hnext hn (ih hj.le) e he
    have hc : (2 * ((T.lsfs (next.scState (first.val + n)) 0).T.m : ℝ) + 1) ≤
        2 * (cap : ℝ) + 1 := by
      have hc' : (((T.lsfs (next.scState (first.val + n)) 0).T.m : ℕ) : ℝ) ≤ cap := by
        exact_mod_cast hcap
      linarith only [hc']
    calc
      _ ≤ _ := hm
      _ ≤ (2 * (cap : ℝ) + 1) * ((2 * (cap : ℝ) + 1) ^ n * B) :=
        mul_le_mul_of_nonneg_right hc hn
      _ = _ := by rw [pow_succ', mul_assoc]

/-- A model gradient bound gives the signed range needed by the scan. -/
theorem rebuildCoreGradient_fits_of_bound
    {mem : ℕ → ℕ} {base gradients h limbs precision exponent : ℕ}
    {G : MGraph} {forest : LSF} {grad : ℕ → ℝ}
    (hwidth : precision + exponent + 2 ≤ h * limbs)
    (hG : G.IsValid) (hvertices : G.V ⊆ forest.T.V)
    (hpot : ForestPotentialsAt mem base h limbs precision forest.T grad forest.T.V)
    (hgrad : EdgeValuesAt mem gradients h limbs precision G.E grad)
    {e : ℕ} (he : e ∈ G.E)
    (hbound : |coreGrad G forest grad e| ≤ (2 : ℝ) ^ exponent) :
    Num.Fits h limbs
      (Num.intVal mem (gradients + e * limbs) h limbs +
        (Num.intVal mem (base + G.head e * limbs) h limbs -
          Num.intVal mem (base + G.tail e * limbs) h limbs)) := by
  have ht := (hpot (G.tail e) (hvertices (hG e he).1)).2
  have hh := (hpot (G.head e) (hvertices (hG e he).2)).2
  have hg := (hgrad e he).2
  apply Num.IPM.fits_of_scaled_bound (P := precision) hwidth
  rw [Int.cast_add, add_div, Num.IPM.scaled_sub]
  unfold Num.fixVal at ht hh hg
  rw [hg, hh, ht]
  rw [coreGrad] at hbound
  simpa only [add_sub_assoc] using hbound

/-- Finish a periodic Rebuild iteration from its verified forest readout
and traversal inputs, preserving the concrete suffix invariant. -/
theorem rebuildCoreStep_fromReadout_runs
    {w copy sort entry a vc ec heap h limbs precision gradients base vcG ecG nextBase nextVC nextEC handle handleCell branchCell : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {init read forestOp prefixCost : ℕ} {p : Program} {start initial st : State} {ω : ℕ → Bool}
    {T : SparseCoreRestartTool} {P : ChainParams}
    (next : ChainState T P) (len grad : ℕ → ℝ) (first : ℕ) (i : Fin P.d) (hfirst : first ≤ i.val) {R : DSRep T.State} {x : R.τ}
    (hargs : Runs w p ω prepareRebuildGraphArgs
      { start with regs := Function.update (Function.update start.regs 53 (start.regs 19)) 54 (start.regs 21) }
      .normal initial 36)
    (hmem : initial.mem = start.mem)
    (hprefix : Runs w p ω (rebuildReadForestLengths init read forestOp)
      initial .normal st prefixCost)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec h limbs precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradTableEnd : gradients + ecG * limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h8 : st.regs 8 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : st.regs 7 + nextEC * limbs ≤ heap) (hcapacity : nextEC ≤ ecG)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (scanExponent : ℕ) (hscanWidth : precision + scanExponent + 2 ≤ h * limbs)
    (gradientBound : ℝ) (hboundNonneg : 0 ≤ gradientBound)
    (hgradientBound : ∀ e ∈ G.E, |g e| ≤ gradientBound)
    (hsizeBound : (2 * (forest.T.m : ℝ) + 1) * gradientBound ≤ (2 : ℝ) ^ scanExponent) :
    ∀ handleBase branchBase,
    RebuildSuffixAt R next len grad handleBase branchBase first i.val vcG ecG h limbs precision start →
    start.regs 4 = handle → handle < 2 ^ w →
    handleCell = handleBase + i.val → branchCell = branchBase + i.val →
    handleBase + P.d < handle → branchBase + P.d < handle →
    (handleBase + P.d < branchBase + first ∨ branchBase + P.d < handleBase + first) →
    H = next.G (i.val + 1) →
    forest = T.lsfs (next.scState i.val) 0 →
    G = next.G i.val →
    g = next.toTreeChain.chainGrad grad i.val →
    nextLengths = next.toTreeChain.chainLen len (i.val + 1) →
    next.toTreeChain.chainGrad grad (i.val + 1) =
      coreGrad (next.G i.val) (T.lsfs (next.scState i.val) 0)
        (next.toTreeChain.chainGrad grad i.val) →
    next.bran i.val = 0 →
    R.Local → R.rep handle (next.scState i.val) x st.mem →
    (∀ addr, R.foot handle x addr → handle ≤ addr ∧ addr < heap) →
    st.mem handleCell = handle → st.mem branchCell = 0 →
    handleCell < heap → branchCell < heap → handle ≤ heap →
    (∀ addr < handle, addr ≠ handleCell → addr ≠ branchCell → st.mem addr = initial.mem addr) →
    ∃ out cost, Runs w p ω (rebuildCoreStep init read forestOp copy sort entry)
        start .normal out cost ∧
      RebuildSuffixAt R next len grad handleBase branchBase first (i.val + 1)
        nextVC nextEC h limbs precision
        { out with regs := Function.update out.regs 19 (i.val + 1) } ∧
      out.regs 19 = i.val ∧
      out.regs 6 = nextBase ∧ handle ≤ out.regs 8 ∧
      out.mem handleCell = handle ∧ handle ≤ out.regs 4 ∧
      (∀ a < handle, a ≠ handleCell → a ≠ branchCell → out.mem a = start.mem a) ∧
      cost + R.phi handle x out.mem ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + 265 + (prefixCost + R.phi handle x st.mem) := by
  intro handleBase branchBase hin hhandle hword hhc hbc hhEnd hbEnd hsep
    hNext hForest hCurrent hGrad hLengths hnextGrad hzero hlocal hrep hfoot hcell hbranch hhBelow hbBelow
    hhandleHeap hprefixFrame
  subst handleCell
  subst branchCell
  have hroot v := rebuildRootPotential_abs_le hforest hboundNonneg
    (fun e he => hgradientBound e (hsub he)) v
  have hparentBound parent (_ : parent ∈ forest.T.V) e (he : e ∈ forest.T.E) :
      |treeRootPot forest.T g parent| + |g e| ≤ (2 : ℝ) ^ scanExponent := by
    have hp := hroot parent
    have hg := hgradientBound e (hsub he)
    have hn := mul_nonneg (Nat.cast_nonneg forest.T.m) hboundNonneg
    linarith only [hp, hg, hn, hsizeBound]
  have hscanBound e (he : e ∈ G.E) : |coreGrad G forest g e| ≤ (2 : ℝ) ^ scanExponent :=
    (rebuildCoreGrad_abs_le (H := G) hforest hsub (fun _ he => he)
      hboundNonneg hgradientBound e he).trans hsizeBound
  have hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc h limbs precision r seen →
        EdgeValuesAt s.mem gradients h limbs precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) h limbs
        Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
          ((if direction then value else 0) - (if direction then 0 else value))) := by
    dsimp only
    intro parent hp e he direction current seen r hwork hvals
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hseen, _, hunseen⟩ := hwork
    have hvalue := (hvals e (hsub he)).2
    have hparent :
        |Num.fixVal current.mem (heap + forest.T.n + parent * limbs) h limbs precision| ≤
          |treeRootPot forest.T g parent| := by
      by_cases hs : parent ∈ seen.toFinset
      · rw [(hseen parent hs).2]
      · rw [Num.fixVal, Num.intVal_zero (hunseen parent hp hs)]
        simp
    apply Num.IPM.fits_of_scaled_bound (P := precision) hscanWidth
    rw [Int.cast_add, add_div, Num.IPM.scaled_sub]
    change |Num.fixVal current.mem _ h limbs precision + _| ≤ _
    cases direction <;> simp only [Bool.false_eq_true, ite_false, ite_true, Int.cast_zero, zero_div,
      zero_sub, sub_zero]
    · unfold Num.fixVal at hvalue
      rw [hvalue]
      exact (abs_add_le _ _).trans ((add_le_add hparent le_rfl).trans (by
        simpa only [abs_neg] using hparentBound parent hp e he))
    · unfold Num.fixVal at hvalue
      rw [hvalue]
      exact (abs_add_le _ _).trans ((add_le_add hparent le_rfl).trans (hparentBound parent hp e he))
  have hfitScan (mem : ℕ → ℕ)
      (hpot : ForestPotentialsAt mem (heap + forest.T.n) h limbs precision forest.T g forest.T.V)
      (hvalues : EdgeValuesAt mem gradients h limbs precision G.E g) (e : ℕ) (he : e ∈ G.E) :=
    rebuildCoreGradient_fits_of_bound hscanWidth hG.1 hvertices hpot hvalues he
      (hscanBound e he)
  obtain ⟨mid, c, hr, hh', hb', h6', h8Lo, hrep', hphi, hg, hl, hn, hgEnd, hlEnd, hnEnd,
    hfree, hheap, hfoot', hframe, hc⟩ :=
    rebuildPrepareModelGradients_runs next len grad i hprefix
      hcopy hsort hreadout ha hh hlimbs hz hgraphEnd hsortRoom hcount hw hforest hvalues
      hsub hgradTableEnd himpl hG hGEnd hvertices hH hHEnd hHE h6 h8 h50 h15 h16 h17
      nextLengths hlen hlenEnd hcapacity hwScan hspace hfit hfitScan hNext hForest hCurrent
      hGrad hLengths hnextGrad hlocal hrep hfoot hcell hbranch hhBelow hbBelow hhandleHeap hprefixFrame
  obtain ⟨out, hout, hin', hi, ho6, ho8, houtMem, houtHeap⟩ :=
    rebuildCoreStep_suffixAt_runs _ len grad hargs hr hin hword hlocal hhandle hfirst
      hheap i.isLt hhEnd hbEnd hsep
      (fun a ha hh hb => (hframe a ha hh hb).trans (congrFun hmem a))
      hh' (hb'.trans hzero.symm) hrep' hfoot' hg hl hn hgEnd hlEnd hnEnd hfree
  refine ⟨out, c + 59, hout, hin', hi, ho6.trans h6', ho8.symm ▸ h8Lo,
    (by rw [houtMem]; exact hh'), houtHeap, ?_, ?_⟩
  · intro a ha hh hb
    exact (congrFun houtMem a).trans ((hframe a ha hh hb).trans (congrFun hmem a))
  · rw [houtMem, hphi]
    omega

/-- One sparse-core iteration of Algorithm 1 Init (page 20) advances
the two reserved descriptor tables and preserves the incoming allocations. -/
theorem solverInitCoreStep_fromReadout_runs
    {w copy sort entry a vc ec heap h limbs precision gradients base vcG ecG nextBase nextVC nextEC handle handleCell branchCell : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {init read forestOp prefixCost : ℕ} {p : Program} {start initial st : State} {ω : ℕ → Bool}
    {T : SparseCoreRestartTool} {P : ChainParams}
    {last : LastLevelTool} (lvlM : ℕ → ℕ) (N₀ : ℕ) (root : MGraph) (len grad : ℕ → ℝ) (i : Fin P.d) {R : DSRep T.State} {x : R.τ}
    (hargs : Runs w p ω prepareRebuildGraphArgs
      { start with regs := Function.update (Function.update start.regs 53 (start.regs 19)) 54 (start.regs 21) }
      .normal initial 36)
    (hmem : initial.mem = start.mem)
    (hprefix : Runs w p ω (rebuildReadForestLengths init read forestOp)
      initial .normal st prefixCost)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec h limbs precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradTableEnd : gradients + ecG * limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h8 : st.regs 8 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : st.regs 7 + nextEC * limbs ≤ heap) (hcapacity : nextEC ≤ ecG)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (scanExponent : ℕ) (hscanWidth : precision + scanExponent + 2 ≤ h * limbs)
    (gradientBound : ℝ) (hboundNonneg : 0 ≤ gradientBound)
    (hgradientBound : ∀ e ∈ G.E, |g e| ≤ gradientBound)
    (hsizeBound : (2 * (forest.T.m : ℝ) + 1) * gradientBound ≤ (2 : ℝ) ^ scanExponent) :
    let next := (algorithm1_initialize T last P lvlM N₀ root len grad).1
    ∀ tableBase,
    RebuildSuffixAt R next len grad tableBase (tableBase + (P.d + 1)) 0 i.val vcG ecG h limbs precision start →
    start.regs 4 = handle → handle < 2 ^ w →
    handleCell = tableBase + i.val → branchCell = tableBase + (P.d + 1) + i.val →
    tableBase + (P.d + 1) + (P.d + 1) ≤ handle →
    H = next.G (i.val + 1) →
    forest = T.lsfs (next.scState i.val) 0 →
    G = next.G i.val →
    g = next.toTreeChain.chainGrad grad i.val →
    nextLengths = next.toTreeChain.chainLen len (i.val + 1) →
    R.Local → R.rep handle (next.scState i.val) x st.mem →
    (∀ addr, R.foot handle x addr → handle ≤ addr ∧ addr < heap) →
    st.mem handleCell = handle → st.mem branchCell = 0 →
    handleCell < heap → branchCell < heap → handle ≤ heap →
    (∀ addr < handle, addr ≠ handleCell → addr ≠ branchCell → st.mem addr = initial.mem addr) →
    ∃ out cost, Runs w p ω (rebuildCoreStep init read forestOp copy sort entry)
        start .normal out cost ∧
      (RebuildSuffixAt R next len grad tableBase (tableBase + (P.d + 1)) 0 (i.val + 1)
        nextVC nextEC h limbs precision
        { out with regs := Function.update out.regs 19 (i.val + 1) } ∧
      out.regs 19 = i.val) ∧ out.regs 6 = nextBase ∧ start.regs 4 ≤ out.regs 8 ∧ start.regs 4 ≤ out.regs 4 ∧
      out.mem (tableBase + i.val) = start.regs 4 ∧
      (∀ a < start.regs 4, a ≠ start.regs 51 → a ≠ start.regs 52 →
        out.mem a = start.mem a) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + 265 + (prefixCost + R.phi handle x st.mem) := by
  dsimp only
  intro tableBase hin hhandle hword hhc hbc hend hNext hForest hCurrent hGrad hLengths
    hlocal hrep hfoot hcell hbranch hhBelow hbBelow hhandleHeap hframe
  obtain ⟨out, cost, hr, hs, hi, ho6, ho8, hmemCell, hheap, hf, hc⟩ :=
    rebuildCoreStep_fromReadout_runs _ len grad 0 i (Nat.zero_le _) hargs hmem hprefix
      hcopy hsort hreadout ha hh hlimbs hz hgraphEnd hsortRoom hcount hw hforest hvalues hsub
      hgradTableEnd himpl hG hGEnd hvertices hH hHEnd hHE h6 h8 h50 h15 h16 h17
      nextLengths hlen hlenEnd hcapacity hwScan hspace scanExponent hscanWidth gradientBound
      hboundNonneg hgradientBound hsizeBound tableBase (tableBase + (P.d + 1)) hin hhandle hword
      hhc hbc (by omega) (by omega) (Or.inl (by omega)) hNext hForest hCurrent hGrad hLengths
      (algorithm1_initialize_nextLevelNumbers T last P lvlM N₀ root len grad i.val i.isLt).2
      (algorithm1_initialize_coreAt T last P lvlM N₀ root len grad i.val i.isLt).2.2
      hlocal hrep hfoot hcell hbranch hhBelow hbBelow hhandleHeap hframe
  refine ⟨out, cost, hr, ⟨hs, hi⟩, ho6, hhandle ▸ ho8, hhandle ▸ hheap,
    by simpa only [← hhc, hhandle] using hmemCell, ?_, (Nat.le_add_right _ _).trans hc⟩
  simpa only [hhandle, hin.handleCursor, hin.branchCursor, ← hhc, ← hbc] using hf

end MinCostFlow.MinRatio
