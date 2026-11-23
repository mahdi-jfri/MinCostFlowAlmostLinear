module

public import MinCostFlow.MinRatio.InitLevels
public import MinCostFlow.MinRatio.InitCoreStep
import MinCostFlow.MinRatio.RebuildModelSuffix
import MinCostFlow.MinRatio.RebuildInputAgreement

/-!
# Concrete level construction for Algorithm 1 Init

Composes the exact sparse-core iteration (`solverInitCoreStep_concrete_runs`) across
all levels `0 ≤ i < P.d` and the runtime terminal builder at level `P.d` using the
existential-capacity suffix invariant, with no off-edge support assumptions.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Along Algorithm 1 Init (page 20), a uniform forest edge-count cap
bounds gradient magnitudes at every level `0 ≤ j ≤ P.d`. -/
theorem initLevels_gradient_abs_le
    (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (root : MGraph) (len₀ grad₀ : ℕ → ℝ) (cap : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    let next := (algorithm1_initialize T L P lvlM N₀ root len₀ grad₀).1
    (∀ e ∈ root.E, |grad₀ e| ≤ B) →
    (∀ j < P.d,
      let forest := T.lsfs (next.scState j) 0
      forest.T.IsForest ∧ forest.T.E ⊆ (next.G j).E ∧
        (next.G (j + 1)).E ⊆ (next.G j).E ∧ forest.T.m ≤ cap) →
    ∀ j ≤ P.d, ∀ e ∈ (next.G j).E,
      |next.toTreeChain.chainGrad grad₀ j e| ≤ (2 * (cap : ℝ) + 1) ^ j * B := by
  dsimp only
  intro hroot hstep j
  let next := (algorithm1_initialize T L P lvlM N₀ root len₀ grad₀).1
  have hfactor : (0 : ℝ) ≤ 2 * (cap : ℝ) + 1 := by positivity
  induction j with
  | zero =>
    intro _ e he
    rw [solverInit_rootGraph T L P lvlM N₀ root len₀ grad₀] at he
    simpa only [TreeChain.chainGrad, pow_zero, one_mul] using hroot e he
  | succ j ih =>
    intro hle e he
    have hj : j < P.d := Nat.lt_of_succ_le hle
    obtain ⟨hf, hsub, hnext, hcap⟩ := hstep j hj
    have hrec := (algorithm1_initialize_nextLevelNumbers T L P lvlM N₀ root len₀ grad₀ j hj).2
    rw [hrec]
    have hn : 0 ≤ (2 * (cap : ℝ) + 1) ^ j * B := mul_nonneg (pow_nonneg hfactor _) hB
    have hm := rebuildCoreGrad_abs_le hf hsub hnext hn (ih hj.le) e he
    have hc : (2 * ((T.lsfs (next.scState j) 0).T.m : ℝ) + 1) ≤ 2 * (cap : ℝ) + 1 := by
      have hc' : (((T.lsfs (next.scState j) 0).T.m : ℕ) : ℝ) ≤ cap := by exact_mod_cast hcap
      linarith only [hc']
    calc
      _ ≤ _ := hm
      _ ≤ (2 * (cap : ℝ) + 1) * ((2 * (cap : ℝ) + 1) ^ j * B) :=
        mul_le_mul_of_nonneg_right hc hn
      _ = _ := by rw [pow_succ', mul_assoc]

/-- Concrete Algorithm 1 Init (page 20) across all `P.d` sparse-core levels and
the capacity-indexed terminal level for `sparseCoreRestartTool`, additionally
exposing pairwise-disjoint core and terminal footprints. -/
theorem buildSolverInitLevels_concrete_capIndexed_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams} {L : LastLevelTool}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    {terminal : ℕ → ℕ → DSRep (ℕ × (ℕ → LSF))}
    (root : MGraph) (len₀ grad₀ : ℕ → ℝ)
    {w heap graph lengths gradient vc0 ec0 limbs init copy sort entry terminalInit : ℕ}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ}
    {multiplier stretchPrecision : ℕ}
    {M N scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
    {p : Program} {op lastOp : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = P.d)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = fmt.precision)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (P.d + 1) + (P.d + 1) < 2 ^ w)
    (hG0 : DynGraphAt st.mem graph vc0 ec0 root)
    (hLen0 : EdgeValuesAt st.mem lengths fmt.limbBits limbs fmt.precision root.E len₀)
    (hGrad0 : EdgeValuesAt st.mem gradient fmt.limbBits limbs fmt.precision root.E grad₀)
    (hgEnd0 : graph + dynGraphSize vc0 ec0 ≤ heap)
    (hlEnd0 : lengths + ec0 * limbs ≤ heap) (hcEnd0 : gradient + ec0 * limbs ≤ heap)
    (hLWord : limbs < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * limbs)
    (hPword : P.d < 2 ^ w) (hkWord : P.k < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hlocal : R.Local)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hentry : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z)) :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let chain := (algorithm1_initialize T L P M (N 0) root len₀ grad₀).1
    let levelCost := fun i =>
      let forest := T.lsfs (chain.scState i) 0
      let H := chain.G (i + 1)
      280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m +
        costs.factor (M i) (N i) * (M i + 1) * P.k + 17 * nextGraphSizeCap (i + 1) + 484
    let terminalCost := multiplier * (L.cost (chain.G P.d) + 1) + 20
    (∀ i, i < P.d → N i = N 0) →
    (∀ i, i < P.d → ∀ vc ec,
      R.Implements w p init op
        (sparseCoreMachineContract fmt limbs T (chain.G i) P.k (M i) (N i) vc ec costs (allocation i))) →
    (∀ vc ec,
      (terminal vc ec).Implements w p terminalInit lastOp
        (lastLevelRuntimeMachineContract fmt limbs L (chain.G P.d) vc ec
          multiplier stretchPrecision (lastAllocation vc ec))) →
    (∀ i, i < P.d →
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let grad := chain.toTreeChain.chainGrad grad₀ i
      let forest := T.lsfs (chain.scState i) 0
      G.m ≤ M i ∧ G.n ≤ N i ∧ (∀ e ∈ G.E, 0 < len e) ∧
      forest.T.IsForest ∧ forest.T.E ⊆ G.E ∧ G.V ⊆ forest.T.V ∧ H.E ⊆ G.E ∧
      2 * forest.T.n + 2 < 2 ^ w ∧
      fmt.precision + scanExponent i + 2 ≤ fmt.limbBits * limbs ∧
      0 ≤ gradientBound i ∧ (∀ e ∈ G.E, |grad e| ≤ gradientBound i) ∧
      (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
    (∀ (ω' : ℕ → Bool) i, i < P.d → ∀ vc ec before,
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let forest := T.lsfs (chain.scState i) 0
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 i vc ec
        fmt.limbBits limbs fmt.precision before →
      InitLevelTablesSeparated heap P.d (before.regs 6) vc ec (before.regs 8) limbs →
      heap + (P.d + 1) + (P.d + 1) ≤ before.regs 4 →
      before.regs 4 + allocation i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
      ∀ args,
        Runs w p ω' prepareRebuildGraphArgs
          { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
          .normal args 36 →
        (∀ mid top v e cost,
          Runs w p ω' (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
          mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
          mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
        (∀ mid c fv fe,
          Runs w p ω' (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
          LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
            fmt.limbBits limbs fmt.precision G.E len) ∧
        (∀ s v e fv fe c,
          Runs w p ω' (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
          DynGraphAt s.mem (s.regs 6) v e H →
          LSFAt s.mem (s.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
          s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
          s.regs 7 + e * limbs ≤ s.regs 5 ∧ e ≤ ec ∧
          s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
          s.regs 5 + forest.T.n + fv * limbs + limbs + fv + fv +
            3 * limbs * forest.T.vol forest.T.V + ec * limbs + 3 * limbs * H.m < 2 ^ w)) →
    (∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ) ^ stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len₀ P.d) e <
        Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len₀ P.d e) →
    L.build (chain.G P.d) (fun e => if e ∈ (chain.G P.d).E then
      chain.toTreeChain.chainLen len₀ P.d e else 0) =
      L.build (chain.G P.d) (chain.toTreeChain.chainLen len₀ P.d) →
    (∀ vc ec before,
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 P.d vc ec
        fmt.limbBits limbs fmt.precision before →
      before.regs 4 + lastAllocation vc ec 1 [before.regs 6, before.regs 7, limbs, fmt.precision, before.regs 4] < 2 ^ w) →
    ∃ out c, Runs w p ω (buildSolverInitLevels init (op 3) (op 2) copy sort entry terminalInit)
        st .normal out c ∧
      RebuiltCoresAt R chain out.mem heap (heap + (P.d + 1)) 0 P.d (out.regs 4) ∧
      out.mem (heap + (P.d + 1) + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
      heap + (P.d + 1) + (P.d + 1) ≤ out.regs 4 ∧
      (∃ (vcLast ecLast : ℕ) (xCore : ∀ i, i < P.d → R.τ) (y : (terminal vcLast ecLast).τ),
        (∀ i (hi : i < P.d),
          out.mem (heap + i) ≤ out.regs 4 ∧
          out.mem (heap + (P.d + 1) + i) = chain.bran i ∧
          R.rep (out.mem (heap + i)) (chain.scState i) (xCore i hi) out.mem ∧
          (∀ a, R.foot (out.mem (heap + i)) (xCore i hi) a →
            heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4 ∧
            (∀ j (hj : j < P.d), j ≠ i → ¬ R.foot (out.mem (heap + j)) (xCore j hj) a) ∧
            ¬ (terminal vcLast ecLast).foot (out.mem (heap + P.d)) y a)) ∧
        out.mem (heap + P.d) ≤ out.regs 4 ∧
        (terminal vcLast ecLast).rep (out.mem (heap + P.d)) (chain.lastK, chain.lastLSFs)
          y out.mem ∧
        (∀ a, (terminal vcLast ecLast).foot (out.mem (heap + P.d)) y a →
          heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4 ∧
          ∀ j (hj : j < P.d), ¬ R.foot (out.mem (heap + j)) (xCore j hj) a)) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ rangeCost levelCost 0 P.d + P.d * 9 + terminalCost + 43 := by
  dsimp only
  intro hNconst hcoreImpl htermImpl hmodel hreadout hstretch hposLast hagreeLast hspaceLast
  let T := sparseCoreRestartTool oracle C depth sparsify
  let chain := (algorithm1_initialize T L P M (N 0) root len₀ grad₀).1
  let DisjCores (i : ℕ) (s : State) : Prop :=
    ∃ (xCore : ∀ j, j < i → R.τ) (hi : ℕ → ℕ),
      ∀ j (hj : j < i),
        s.mem (heap + j) ≤ s.regs 4 ∧
        s.mem (heap + (P.d + 1) + j) = chain.bran j ∧
        R.rep (s.mem (heap + j)) (chain.scState j) (xCore j hj) s.mem ∧
        heap + (P.d + 1) + (P.d + 1) ≤ s.mem (heap + j) ∧
        hi j ≤ s.regs 4 ∧
        (∀ a, R.foot (s.mem (heap + j)) (xCore j hj) a → s.mem (heap + j) ≤ a ∧ a < hi j) ∧
        (∀ k, k < i → j < k → hi j ≤ s.mem (heap + k))
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ vc ec,
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 i vc ec
        fmt.limbBits limbs fmt.precision s ∧
      InitLevelTablesSeparated heap P.d (s.regs 6) vc ec (s.regs 8) limbs ∧
      DisjCores i s
  let Done (out : State) : Prop :=
    RebuiltCoresAt R chain out.mem heap (heap + (P.d + 1)) 0 P.d (out.regs 4) ∧
    out.mem (heap + (P.d + 1) + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
    heap + (P.d + 1) + (P.d + 1) ≤ out.regs 4 ∧
    ∃ (vcLast ecLast : ℕ) (xCore : ∀ i, i < P.d → R.τ) (y : (terminal vcLast ecLast).τ),
      (∀ i (hi : i < P.d),
        out.mem (heap + i) ≤ out.regs 4 ∧
        out.mem (heap + (P.d + 1) + i) = chain.bran i ∧
        R.rep (out.mem (heap + i)) (chain.scState i) (xCore i hi) out.mem ∧
        (∀ a, R.foot (out.mem (heap + i)) (xCore i hi) a →
          heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4 ∧
          (∀ j (hj : j < P.d), j ≠ i → ¬ R.foot (out.mem (heap + j)) (xCore j hj) a) ∧
          ¬ (terminal vcLast ecLast).foot (out.mem (heap + P.d)) y a)) ∧
      out.mem (heap + P.d) ≤ out.regs 4 ∧
      (terminal vcLast ecLast).rep (out.mem (heap + P.d)) (chain.lastK, chain.lastLSFs)
        y out.mem ∧
      (∀ a, (terminal vcLast ecLast).foot (out.mem (heap + P.d)) y a →
        heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4 ∧
        ∀ j (hj : j < P.d), ¬ R.foot (out.mem (heap + j)) (xCore j hj) a)
  let levelCost := fun i =>
    let forest := T.lsfs (chain.scState i) 0
    let H := chain.G (i + 1)
    280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
      forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
      (129 * limbs + 172) * H.m +
      costs.factor (M i) (N i) * (M i + 1) * P.k + 17 * nextGraphSizeCap (i + 1) + 484
  let terminalCost := multiplier * (L.cost (chain.G P.d) + 1) + 20
  obtain ⟨out, c, hr, ⟨hcores, hbr, hzero, hheapEnd, hterm⟩, hframe, hcost⟩ :=
    buildSolverInitLevels_framed_runs (Inv := Inv) (Done := Done) levelCost terminalCost
      hh hg hl hc hd hz hroom (by omega) hPword
      (by
        intro ready h51 h52 h4 h6 h7 h8 _ h21 hm hfree _ _
        refine ⟨vc0, ec0, ?_, Or.inl ⟨by simpa [Function.update_of_ne, h6] using hgEnd0,
          by simpa [Function.update_of_ne, h8] using hcEnd0⟩, ?_⟩
        · apply solverInitLevels_entry (solverInit_rootGraph T L P M (N 0) root len₀ grad₀) h21 h51 h52
          · simpa only [hm, h6] using hG0
          · simpa only [hm, h7] using hLen0
          · simpa only [hm, h8] using hGrad0
          · rw [h6, h4]; omega
          · rw [h7, h4]; omega
          · rw [h8, h4]; omega
          · intro a ha; exact hfree a (by omega)
        · exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ => 0, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      (fun _ _ _ ⟨_, _, hin, _, _⟩ => hin.index)
      (fun _ _ _ ⟨_, _, hin, _, _⟩ => hin.depth)
      (fun _ _ _ ⟨_, _, hin, _, _⟩ => solverInitLevels_descriptor_bounds hin)
      (by
        intro i hi before hend hL' _ current ω' ⟨heq, vc, ec, hin, hsep, xCore, hiB, hdisj⟩
        subst current
        obtain ⟨hm, hn, hpos, hforest, hsub, hverts, hHE, hcount, hscanW, hbNonneg, hgradB, hsizeB⟩ :=
          hmodel i hi
        obtain ⟨hroomCore, hread⟩ := hreadout ω' i hi vc ec before hin hsep hend
        obtain ⟨next, nextVC, nextEC, cost, hstep, hs, hsepNext, hheapOut, hmemCell, hframeOut, hcostStep⟩ :=
          solverInitCoreStep_concrete_runs (ω := ω') oracle C depth sparsify M (N 0) root len₀ grad₀
            ⟨i, hi⟩ rfl (hNconst i hi).symm hin hsep hend (hL'.trans h67) (hcoreImpl i hi vc ec) hcopy hsort hentry
            hm hn hpos hforest hsub hverts hHE hroomCore hkWord hw9 hcount hscanW hbNonneg
            hgradB hsizeB hread
        obtain ⟨hbrI, xI, hrepI, _, _, hfootI⟩ := hs.1.installed i (Nat.zero_le i) (Nat.lt_succ_self i)
        have hdisjNext : DisjCores (i + 1) { next with regs := Function.update next.regs 19 (i + 1) } := by
          let xNext : ∀ j, j < i + 1 → R.τ := fun j hj =>
            if hlt : j < i then xCore j hlt else xI
          refine ⟨xNext, Function.update hiB i (next.regs 4), fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · obtain ⟨hleJ, hbrJ, hrepJ, hgeJ, hhiJ, hfootJ, hordJ⟩ := hdisj j hlt
            have hcellJ : next.mem (heap + j) = before.mem (heap + j) :=
              hframeOut (heap + j) (by omega) (by rw [hin.handleCursor]; omega) (by rw [hin.branchCursor]; omega)
            have hbrJ' : next.mem (heap + (P.d + 1) + j) = before.mem (heap + (P.d + 1) + j) :=
              hframeOut (heap + (P.d + 1) + j) (by omega) (by rw [hin.handleCursor]; omega) (by rw [hin.branchCursor]; omega)
            have hneJ : j ≠ i := Nat.ne_of_lt hlt
            have hxJ : xNext j hj = xCore j hlt := dite_eq_left hlt
            refine ⟨hcellJ.symm ▸ hleJ.trans hheapOut, hbrJ'.trans hbrJ, ?_, hcellJ.symm ▸ hgeJ,
              by simp only [Function.update_of_ne hneJ]; exact hhiJ.trans hheapOut,
              fun a ha => by
                rw [hxJ, hcellJ] at ha
                simp only [Function.update_of_ne hneJ, hcellJ]
                exact hfootJ a ha,
              fun k hk hjk => ?_⟩
            · rw [hxJ, hcellJ]
              refine (hlocal _ _ _ before.mem next.mem (fun a ha => ?_)).1 hrepJ
              have hfa := hfootJ a ha
              have := hfa.1
              exact (hframeOut a (lt_of_lt_of_le hfa.2 hhiJ) (by rw [hin.handleCursor]; omega) (by rw [hin.branchCursor]; omega)).symm
            · simp only [Function.update_of_ne hneJ]
              rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hklt | rfl
              · have hcellK : next.mem (heap + k) = before.mem (heap + k) :=
                  hframeOut (heap + k) (by omega) (by rw [hin.handleCursor]; omega) (by rw [hin.branchCursor]; omega)
                rw [hcellK]; exact hordJ k hklt hjk
              · rw [hmemCell]; exact hhiJ
          · have hxI : xNext j hj = xI := dite_eq_right (Nat.lt_irrefl j)
            refine ⟨hmemCell.symm ▸ hheapOut, hbrI, by rw [hxI]; exact hrepI, hmemCell.symm ▸ hend,
              by simp only [Function.update_self]; exact le_rfl,
              fun a ha => by rw [hxI] at ha; simp only [Function.update_self]; exact hfootI a ha,
              fun k hk hjk => by omega⟩
        exact ⟨.normal, next, cost, hstep,
          ⟨⟨⟨nextVC, nextEC, hs.1, by simpa using hsepNext, hdisjNext⟩, hs.2⟩, hheapOut, hframeOut⟩, hcostStep⟩)
      (by
        intro before hend hL' hP' current ω' ⟨heq, vc, ec, hin, _, xCore, hiB, hdisj⟩
        subst current
        obtain ⟨hmodelLast, hbranchLast⟩ := algorithm1_initialize_terminal T L P M (N 0) root len₀ grad₀
        obtain ⟨out, ret, cost, y, htermRun, hhT, hbT, houtT, hrepT, hfreeT, hfootT, hframeT, hheapT, hcostT⟩ :=
          rebuildTerminalRuntimeStep_exact_runs (ω := ω') (htermImpl vc ec) rfl rfl rfl
            (hL'.trans h67) (hP'.trans h68) hLWord hPWord hFour hWidth _
            hin.graph hin.graphEnd hin.lengthsEnd hin.lengths hstretch hposLast hin.free
            (hspaceLast vc ec before hin) hagreeLast hin.handleCursor hin.branchCursor
            (by omega) (by omega) (by omega)
        rw [← houtT] at hfreeT hfootT hheapT
        have hkeepT := hin.installed.preserve hlocal hheapT (by omega) (by omega)
          (fun j hj hlt => ⟨by omega, by omega, by omega, by omega⟩)
          (Or.inl le_rfl) (Or.inr le_rfl) hframeT
        have hcellT (j : ℕ) (hj : j < P.d) : out.mem (heap + j) = before.mem (heap + j) :=
          hframeT (heap + j) (by omega) (by omega) (by omega)
        have hbrT (j : ℕ) (hj : j < P.d) : out.mem (heap + (P.d + 1) + j) = before.mem (heap + (P.d + 1) + j) :=
          hframeT (heap + (P.d + 1) + j) (by omega) (by omega) (by omega)
        refine ⟨.normal, out, cost, htermRun,
          ⟨⟨hkeepT, hbT.trans hbranchLast.symm, hfreeT, hend.trans hheapT, vc, ec, xCore, y, ?_, hhT.symm ▸ hheapT, ?_, ?_⟩, ?_⟩,
          (Nat.le_add_right _ _).trans hcostT⟩
        · intro i hi
          obtain ⟨hleI, hbrI, hrepI, hgeI, hhiI, hfootI, hordI⟩ := hdisj i hi
          rw [hcellT i hi, hbrT i hi]
          refine ⟨hleI.trans hheapT, hbrI, ?_, fun a ha => ?_⟩
          · refine (hlocal _ _ _ before.mem out.mem (fun a ha => ?_)).1 hrepI
            have hfa := hfootI a ha
            have := hfa.1
            exact (hframeT a (lt_of_lt_of_le hfa.2 hhiI) (by omega) (by omega)).symm
          · have hfa := hfootI a ha
            refine ⟨hgeI.trans hfa.1, (lt_of_lt_of_le hfa.2 hhiI).trans_le hheapT, fun j hj hne hfj => ?_, fun hft => ?_⟩
            · rw [hcellT j hj] at hfj
              obtain ⟨_, _, _, _, _, hfootJ, hordJ⟩ := hdisj j hj
              have hfj' := hfootJ a hfj
              rcases Nat.lt_or_gt_of_ne hne with hji | hij
              · exact Nat.not_lt_of_ge (le_trans (hordJ i hi hji) hfa.1) hfj'.2
              · exact Nat.not_lt_of_ge (le_trans (hordI j hj hij) hfj'.1) hfa.2
            · rw [hhT] at hft
              exact Nat.not_lt_of_ge (hfootT a hft).1 (lt_of_lt_of_le hfa.2 hhiI)
        · rw [hhT, hmodelLast]; exact hrepT
        · intro a ha
          rw [hhT] at ha
          have hfa := hfootT a ha
          refine ⟨hend.trans hfa.1, hfa.2, fun j hj hfj => ?_⟩
          rw [hcellT j hj] at hfj
          obtain ⟨_, _, _, _, hhiJ, hfootJ, _⟩ := hdisj j hj
          exact Nat.not_lt_of_ge hfa.1 (lt_of_lt_of_le (hfootJ a hfj).2 hhiJ)
        · simpa only [hin.handleCursor, hin.branchCursor] using hframeT)
  exact ⟨out, c, hr, hcores, hbr, hzero, hheapEnd, hterm, hframe, hcost⟩

/-- Specialize `buildSolverInitLevels_concrete_capIndexed_runs` to `fixedPointLastLevelTool`. -/
theorem buildSolverInitLevels_fixedPoint_capIndexed_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    {terminal : ℕ → ℕ → DSRep (ℕ × (ℕ → LSF))}
    (root : MGraph) (len₀ grad₀ : ℕ → ℝ)
    {w heap graph lengths gradient vc0 ec0 limbs init copy sort entry terminalInit : ℕ}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ}
    {multiplier stretchPrecision : ℕ}
    {M N scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
    {p : Program} {op lastOp : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = P.d)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = fmt.precision)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (P.d + 1) + (P.d + 1) < 2 ^ w)
    (hG0 : DynGraphAt st.mem graph vc0 ec0 root)
    (hLen0 : EdgeValuesAt st.mem lengths fmt.limbBits limbs fmt.precision root.E len₀)
    (hGrad0 : EdgeValuesAt st.mem gradient fmt.limbBits limbs fmt.precision root.E grad₀)
    (hgEnd0 : graph + dynGraphSize vc0 ec0 ≤ heap)
    (hlEnd0 : lengths + ec0 * limbs ≤ heap) (hcEnd0 : gradient + ec0 * limbs ≤ heap)
    (hLWord : limbs < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * limbs)
    (hPword : P.d < 2 ^ w) (hkWord : P.k < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hlocal : R.Local)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hentry : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z)) :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let L := LastLevelProgram.fixedPointLastLevelTool oracle C
    let chain := (algorithm1_initialize T L P M (N 0) root len₀ grad₀).1
    let levelCost := fun i =>
      let forest := T.lsfs (chain.scState i) 0
      let H := chain.G (i + 1)
      280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m +
        costs.factor (M i) (N i) * (M i + 1) * P.k + 17 * nextGraphSizeCap (i + 1) + 484
    let terminalCost := multiplier * (L.cost (chain.G P.d) + 1) + 20
    (∀ i, i < P.d → N i = N 0) →
    (chain.G P.d).IsValid →
    (∀ i, i < P.d → ∀ vc ec,
      R.Implements w p init op
        (sparseCoreMachineContract fmt limbs T (chain.G i) P.k (M i) (N i) vc ec costs (allocation i))) →
    (∀ vc ec,
      (terminal vc ec).Implements w p terminalInit lastOp
        (lastLevelRuntimeMachineContract fmt limbs L (chain.G P.d) vc ec
          multiplier stretchPrecision (lastAllocation vc ec))) →
    (∀ i, i < P.d →
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let grad := chain.toTreeChain.chainGrad grad₀ i
      let forest := T.lsfs (chain.scState i) 0
      G.m ≤ M i ∧ G.n ≤ N i ∧ (∀ e ∈ G.E, 0 < len e) ∧
      forest.T.IsForest ∧ forest.T.E ⊆ G.E ∧ G.V ⊆ forest.T.V ∧ H.E ⊆ G.E ∧
      2 * forest.T.n + 2 < 2 ^ w ∧
      fmt.precision + scanExponent i + 2 ≤ fmt.limbBits * limbs ∧
      0 ≤ gradientBound i ∧ (∀ e ∈ G.E, |grad e| ≤ gradientBound i) ∧
      (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
    (∀ (ω' : ℕ → Bool) i, i < P.d → ∀ vc ec before,
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let forest := T.lsfs (chain.scState i) 0
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 i vc ec
        fmt.limbBits limbs fmt.precision before →
      InitLevelTablesSeparated heap P.d (before.regs 6) vc ec (before.regs 8) limbs →
      heap + (P.d + 1) + (P.d + 1) ≤ before.regs 4 →
      before.regs 4 + allocation i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
      ∀ args,
        Runs w p ω' prepareRebuildGraphArgs
          { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
          .normal args 36 →
        (∀ mid top v e cost,
          Runs w p ω' (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
          mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
          mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
        (∀ mid c fv fe,
          Runs w p ω' (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
          LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
            fmt.limbBits limbs fmt.precision G.E len) ∧
        (∀ s v e fv fe c,
          Runs w p ω' (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
          DynGraphAt s.mem (s.regs 6) v e H →
          LSFAt s.mem (s.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
          s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
          s.regs 7 + e * limbs ≤ s.regs 5 ∧ e ≤ ec ∧
          s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
          s.regs 5 + forest.T.n + fv * limbs + limbs + fv + fv +
            3 * limbs * forest.T.vol forest.T.V + ec * limbs + 3 * limbs * H.m < 2 ^ w)) →
    (∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ) ^ stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len₀ P.d) e <
        Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len₀ P.d e) →
    (∀ vc ec before,
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 P.d vc ec
        fmt.limbBits limbs fmt.precision before →
      before.regs 4 + lastAllocation vc ec 1 [before.regs 6, before.regs 7, limbs, fmt.precision, before.regs 4] < 2 ^ w) →
    ∃ out c, Runs w p ω (buildSolverInitLevels init (op 3) (op 2) copy sort entry terminalInit)
        st .normal out c ∧
      RebuiltCoresAt R chain out.mem heap (heap + (P.d + 1)) 0 P.d (out.regs 4) ∧
      out.mem (heap + (P.d + 1) + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
      heap + (P.d + 1) + (P.d + 1) ≤ out.regs 4 ∧
      (∃ (vcLast ecLast : ℕ) (xCore : ∀ i, i < P.d → R.τ) (y : (terminal vcLast ecLast).τ),
        (∀ i (hi : i < P.d),
          out.mem (heap + i) ≤ out.regs 4 ∧
          out.mem (heap + (P.d + 1) + i) = chain.bran i ∧
          R.rep (out.mem (heap + i)) (chain.scState i) (xCore i hi) out.mem ∧
          (∀ a, R.foot (out.mem (heap + i)) (xCore i hi) a →
            heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4 ∧
            (∀ j (hj : j < P.d), j ≠ i → ¬ R.foot (out.mem (heap + j)) (xCore j hj) a) ∧
            ¬ (terminal vcLast ecLast).foot (out.mem (heap + P.d)) y a)) ∧
        out.mem (heap + P.d) ≤ out.regs 4 ∧
        (terminal vcLast ecLast).rep (out.mem (heap + P.d)) (chain.lastK, chain.lastLSFs)
          y out.mem ∧
        (∀ a, (terminal vcLast ecLast).foot (out.mem (heap + P.d)) y a →
          heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4 ∧
          ∀ j (hj : j < P.d), ¬ R.foot (out.mem (heap + j)) (xCore j hj) a)) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ rangeCost levelCost 0 P.d + P.d * 9 + terminalCost + 43 := by
  dsimp only
  intro hNconst hValidLast hcoreImpl htermImpl hmodel hreadout hstretch hposLast hspaceLast
  exact buildSolverInitLevels_concrete_capIndexed_runs oracle C depth sparsify root len₀ grad₀
    hh hg hl hc hd h67 h68 hz hroom hG0 hLen0 hGrad0 hgEnd0 hlEnd0 hcEnd0
    hLWord hPWord hFour hWidth hPword hkWord hw9 hlocal hcopy hsort hentry
    hNconst hcoreImpl htermImpl hmodel hreadout hstretch hposLast
    (fixedPointLastLevel_build_congr oracle C hValidLast (fun e he => by simp [he]))
    hspaceLast

/-- Concrete Algorithm 1 Init (page 20) with a uniform terminal `DSRep`. -/
theorem buildSolverInitLevels_concrete_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams} {L : LastLevelTool}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    {terminal : DSRep (ℕ × (ℕ → LSF))}
    (root : MGraph) (len₀ grad₀ : ℕ → ℝ)
    {w heap graph lengths gradient vc0 ec0 limbs init copy sort entry terminalInit : ℕ}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAllocation : ℕ → List ℕ → ℕ}
    {multiplier stretchPrecision : ℕ}
    {M N scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
    {p : Program} {op lastOp : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = P.d)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = fmt.precision)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (P.d + 1) + (P.d + 1) < 2 ^ w)
    (hG0 : DynGraphAt st.mem graph vc0 ec0 root)
    (hLen0 : EdgeValuesAt st.mem lengths fmt.limbBits limbs fmt.precision root.E len₀)
    (hGrad0 : EdgeValuesAt st.mem gradient fmt.limbBits limbs fmt.precision root.E grad₀)
    (hgEnd0 : graph + dynGraphSize vc0 ec0 ≤ heap)
    (hlEnd0 : lengths + ec0 * limbs ≤ heap) (hcEnd0 : gradient + ec0 * limbs ≤ heap)
    (hLWord : limbs < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * limbs)
    (hPword : P.d < 2 ^ w) (hkWord : P.k < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hlocal : R.Local)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hentry : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z)) :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let chain := (algorithm1_initialize T L P M (N 0) root len₀ grad₀).1
    let levelCost := fun i =>
      let forest := T.lsfs (chain.scState i) 0
      let H := chain.G (i + 1)
      280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m +
        costs.factor (M i) (N i) * (M i + 1) * P.k + 17 * nextGraphSizeCap (i + 1) + 484
    let terminalCost := multiplier * (L.cost (chain.G P.d) + 1) + 20
    (∀ i, i < P.d → N i = N 0) →
    (∀ i, i < P.d → ∀ vc ec,
      R.Implements w p init op
        (sparseCoreMachineContract fmt limbs T (chain.G i) P.k (M i) (N i) vc ec costs (allocation i))) →
    (∀ vc ec,
      terminal.Implements w p terminalInit lastOp
        (lastLevelRuntimeMachineContract fmt limbs L (chain.G P.d) vc ec
          multiplier stretchPrecision lastAllocation)) →
    (∀ i, i < P.d →
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let grad := chain.toTreeChain.chainGrad grad₀ i
      let forest := T.lsfs (chain.scState i) 0
      G.m ≤ M i ∧ G.n ≤ N i ∧ (∀ e ∈ G.E, 0 < len e) ∧
      forest.T.IsForest ∧ forest.T.E ⊆ G.E ∧ G.V ⊆ forest.T.V ∧ H.E ⊆ G.E ∧
      2 * forest.T.n + 2 < 2 ^ w ∧
      fmt.precision + scanExponent i + 2 ≤ fmt.limbBits * limbs ∧
      0 ≤ gradientBound i ∧ (∀ e ∈ G.E, |grad e| ≤ gradientBound i) ∧
      (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
    (∀ (ω' : ℕ → Bool) i, i < P.d → ∀ vc ec before,
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let forest := T.lsfs (chain.scState i) 0
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 i vc ec
        fmt.limbBits limbs fmt.precision before →
      InitLevelTablesSeparated heap P.d (before.regs 6) vc ec (before.regs 8) limbs →
      heap + (P.d + 1) + (P.d + 1) ≤ before.regs 4 →
      before.regs 4 + allocation i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
      ∀ args,
        Runs w p ω' prepareRebuildGraphArgs
          { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
          .normal args 36 →
        (∀ mid top v e cost,
          Runs w p ω' (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
          mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
          mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
        (∀ mid c fv fe,
          Runs w p ω' (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
          LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
            fmt.limbBits limbs fmt.precision G.E len) ∧
        (∀ s v e fv fe c,
          Runs w p ω' (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
          DynGraphAt s.mem (s.regs 6) v e H →
          LSFAt s.mem (s.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
          s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
          s.regs 7 + e * limbs ≤ s.regs 5 ∧ e ≤ ec ∧
          s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
          s.regs 5 + forest.T.n + fv * limbs + limbs + fv + fv +
            3 * limbs * forest.T.vol forest.T.V + ec * limbs + 3 * limbs * H.m < 2 ^ w)) →
    (∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ) ^ stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len₀ P.d) e <
        Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len₀ P.d e) →
    L.build (chain.G P.d) (fun e => if e ∈ (chain.G P.d).E then
      chain.toTreeChain.chainLen len₀ P.d e else 0) =
      L.build (chain.G P.d) (chain.toTreeChain.chainLen len₀ P.d) →
    (∀ vc ec before,
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 P.d vc ec
        fmt.limbBits limbs fmt.precision before →
      before.regs 4 + lastAllocation 1 [before.regs 6, before.regs 7, limbs, fmt.precision, before.regs 4] < 2 ^ w) →
    ∃ out c, Runs w p ω (buildSolverInitLevels init (op 3) (op 2) copy sort entry terminalInit)
        st .normal out c ∧
      RebuiltCoresAt R chain out.mem heap (heap + (P.d + 1)) 0 P.d (out.regs 4) ∧
      out.mem (heap + (P.d + 1) + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
      heap + (P.d + 1) + (P.d + 1) ≤ out.regs 4 ∧
      (∃ y : terminal.τ, terminal.rep (out.mem (heap + P.d)) (chain.lastK, chain.lastLSFs)
        y out.mem ∧ ∀ a, terminal.foot (out.mem (heap + P.d)) y a →
          heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ rangeCost levelCost 0 P.d + P.d * 9 + terminalCost + 43 := by
  dsimp only
  intro hNconst hcoreImpl htermImpl hmodel hreadout hstretch hposLast hagreeLast hspaceLast
  obtain ⟨out, c, hr, hcores, hbr, hz', hge, ⟨_, _, _, y, _, _, hrepY, hfootY⟩, hframe, hcost⟩ :=
    buildSolverInitLevels_concrete_capIndexed_runs (terminal := fun _ _ => terminal)
      (lastAllocation := fun _ _ => lastAllocation)
      oracle C depth sparsify root len₀ grad₀
      hh hg hl hc hd h67 h68 hz hroom hG0 hLen0 hGrad0 hgEnd0 hlEnd0 hcEnd0
      hLWord hPWord hFour hWidth hPword hkWord hw9 hlocal hcopy hsort hentry
      hNconst hcoreImpl htermImpl hmodel hreadout hstretch hposLast hagreeLast hspaceLast
  exact ⟨out, c, hr, hcores, hbr, hz', hge, ⟨y, hrepY, fun a ha => ⟨(hfootY a ha).1, (hfootY a ha).2.1⟩⟩, hframe, hcost⟩

/-- Specialize `buildSolverInitLevels_concrete_runs` to `fixedPointLastLevelTool`,
discharging terminal off-edge length agreement via `fixedPointLastLevel_build_congr`. -/
theorem buildSolverInitLevels_fixedPoint_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    {terminal : DSRep (ℕ × (ℕ → LSF))}
    (root : MGraph) (len₀ grad₀ : ℕ → ℝ)
    {w heap graph lengths gradient vc0 ec0 limbs init copy sort entry terminalInit : ℕ}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAllocation : ℕ → List ℕ → ℕ}
    {multiplier stretchPrecision : ℕ}
    {M N scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
    {p : Program} {op lastOp : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = P.d)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = fmt.precision)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (P.d + 1) + (P.d + 1) < 2 ^ w)
    (hG0 : DynGraphAt st.mem graph vc0 ec0 root)
    (hLen0 : EdgeValuesAt st.mem lengths fmt.limbBits limbs fmt.precision root.E len₀)
    (hGrad0 : EdgeValuesAt st.mem gradient fmt.limbBits limbs fmt.precision root.E grad₀)
    (hgEnd0 : graph + dynGraphSize vc0 ec0 ≤ heap)
    (hlEnd0 : lengths + ec0 * limbs ≤ heap) (hcEnd0 : gradient + ec0 * limbs ≤ heap)
    (hLWord : limbs < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * limbs)
    (hPword : P.d < 2 ^ w) (hkWord : P.k < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hlocal : R.Local)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hentry : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z)) :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let L := LastLevelProgram.fixedPointLastLevelTool oracle C
    let chain := (algorithm1_initialize T L P M (N 0) root len₀ grad₀).1
    let levelCost := fun i =>
      let forest := T.lsfs (chain.scState i) 0
      let H := chain.G (i + 1)
      280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m +
        costs.factor (M i) (N i) * (M i + 1) * P.k + 17 * nextGraphSizeCap (i + 1) + 484
    let terminalCost := multiplier * (L.cost (chain.G P.d) + 1) + 20
    (∀ i, i < P.d → N i = N 0) →
    (chain.G P.d).IsValid →
    (∀ i, i < P.d → ∀ vc ec,
      R.Implements w p init op
        (sparseCoreMachineContract fmt limbs T (chain.G i) P.k (M i) (N i) vc ec costs (allocation i))) →
    (∀ vc ec,
      terminal.Implements w p terminalInit lastOp
        (lastLevelRuntimeMachineContract fmt limbs L (chain.G P.d) vc ec
          multiplier stretchPrecision lastAllocation)) →
    (∀ i, i < P.d →
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let grad := chain.toTreeChain.chainGrad grad₀ i
      let forest := T.lsfs (chain.scState i) 0
      G.m ≤ M i ∧ G.n ≤ N i ∧ (∀ e ∈ G.E, 0 < len e) ∧
      forest.T.IsForest ∧ forest.T.E ⊆ G.E ∧ G.V ⊆ forest.T.V ∧ H.E ⊆ G.E ∧
      2 * forest.T.n + 2 < 2 ^ w ∧
      fmt.precision + scanExponent i + 2 ≤ fmt.limbBits * limbs ∧
      0 ≤ gradientBound i ∧ (∀ e ∈ G.E, |grad e| ≤ gradientBound i) ∧
      (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
    (∀ (ω' : ℕ → Bool) i, i < P.d → ∀ vc ec before,
      let G := chain.G i
      let H := chain.G (i + 1)
      let len := chain.toTreeChain.chainLen len₀ i
      let forest := T.lsfs (chain.scState i) 0
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 i vc ec
        fmt.limbBits limbs fmt.precision before →
      InitLevelTablesSeparated heap P.d (before.regs 6) vc ec (before.regs 8) limbs →
      heap + (P.d + 1) + (P.d + 1) ≤ before.regs 4 →
      before.regs 4 + allocation i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
      ∀ args,
        Runs w p ω' prepareRebuildGraphArgs
          { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
          .normal args 36 →
        (∀ mid top v e cost,
          Runs w p ω' (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
          mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
          mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
        (∀ mid c fv fe,
          Runs w p ω' (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
          LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
            fmt.limbBits limbs fmt.precision G.E len) ∧
        (∀ s v e fv fe c,
          Runs w p ω' (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
          DynGraphAt s.mem (s.regs 6) v e H →
          LSFAt s.mem (s.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
          s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
          s.regs 7 + e * limbs ≤ s.regs 5 ∧ e ≤ ec ∧
          s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
          s.regs 5 + forest.T.n + fv * limbs + limbs + fv + fv +
            3 * limbs * forest.T.vol forest.T.V + ec * limbs + 3 * limbs * H.m < 2 ^ w)) →
    (∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ) ^ stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len₀ P.d) e <
        Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len₀ P.d e) →
    (∀ vc ec before,
      RebuildSuffixAt R chain len₀ grad₀ heap (heap + (P.d + 1)) 0 P.d vc ec
        fmt.limbBits limbs fmt.precision before →
      before.regs 4 + lastAllocation 1 [before.regs 6, before.regs 7, limbs, fmt.precision, before.regs 4] < 2 ^ w) →
    ∃ out c, Runs w p ω (buildSolverInitLevels init (op 3) (op 2) copy sort entry terminalInit)
        st .normal out c ∧
      RebuiltCoresAt R chain out.mem heap (heap + (P.d + 1)) 0 P.d (out.regs 4) ∧
      out.mem (heap + (P.d + 1) + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
      heap + (P.d + 1) + (P.d + 1) ≤ out.regs 4 ∧
      (∃ y : terminal.τ, terminal.rep (out.mem (heap + P.d)) (chain.lastK, chain.lastLSFs)
        y out.mem ∧ ∀ a, terminal.foot (out.mem (heap + P.d)) y a →
          heap + (P.d + 1) + (P.d + 1) ≤ a ∧ a < out.regs 4) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ rangeCost levelCost 0 P.d + P.d * 9 + terminalCost + 43 := by
  dsimp only
  intro hNconst hValidLast hcoreImpl htermImpl hmodel hreadout hstretch hposLast hspaceLast
  exact buildSolverInitLevels_concrete_runs oracle C depth sparsify root len₀ grad₀
    hh hg hl hc hd h67 h68 hz hroom hG0 hLen0 hGrad0 hgEnd0 hlEnd0 hcEnd0
    hLWord hPWord hFour hWidth hPword hkWord hw9 hlocal hcopy hsort hentry
    hNconst hcoreImpl htermImpl hmodel hreadout hstretch hposLast
    (fixedPointLastLevel_build_congr oracle C hValidLast (fun e he => by simp [he]))
    hspaceLast

end MinCostFlow.MinRatio
