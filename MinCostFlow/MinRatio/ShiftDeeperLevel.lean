module

public import MinCostFlow.MinRatio.ShiftForestScan
public import MinCostFlow.MinRatio.RebuildLevel
import MinCostFlow.MinRatio.TreeEditFold
import MinCostFlow.MinRatio.RebuildGuard

/-!
# Starting the shifted suffix

Algorithm 1 (page 20) rebuilds the deeper chain after a branch shift.
The first deeper initialization consumes the graph and prepared length
and gradient tables through the sparse-core contract.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Restart the selected branch and initialize the first deeper tool
from its graph, lengths, and gradients (Algorithm 1, page 20). -/
@[expose] def shiftDeeperLevel (restart read forestOp copy sort cell init : ℕ) : Stmt :=
  shiftRestartPrepareGradients restart read forestOp copy sort cell ;; rebuildLevelInit init

/-- The initializer keeps any caller register outside its three outputs
once the gradient preparation has established that register's value. -/
theorem shiftDeeperLevel_preserves_regs
    {w restart read forestOp copy sort cell init cost r : ℕ}
    {p : Program} {st out : State} {ω : ℕ → Bool}
    (hrun : Runs w p ω (shiftDeeperLevel restart read forestOp copy sort cell init)
      st .normal out cost)
    (hr : 51 ≤ r) : out.regs r = st.regs r := by
  rcases runs_seq_iff.mp hrun with ⟨_, _, _, h, _⟩ | ⟨mid, c, _, hp, hi, _⟩
  · cases h
  exact (rebuildLevelInit_preserves_regs hi (by omega) (by omega) (by omega)).trans
    (shiftRestartPrepareGradients_preserves_regs hr hp)

/-- A prepared gradient run supplies the numerical inputs for the first
deeper sparse-core rebuild. The tool reads live values and extends them by zero. -/
theorem shiftDeeperLevel_runs {w L k M N vc ec inputEC restart read forestOp copy sort cell init : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G H : MGraph} {forest : LSF}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st mid : State} {ω : ℕ → Bool}
    {prefixCost : ℕ} (ℓ g : ℕ → ℝ)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool H k M N vc ec costs allocation))
    (hprep : Runs w p ω (shiftRestartPrepareGradients restart read forestOp copy sort cell) st .normal mid prefixCost)
    (hgraph : DynGraphAt mid.mem (mid.regs 6) vc ec H)
    (hlen : EdgeValuesAt mid.mem (mid.regs 7) fmt.limbBits L fmt.precision H.E ℓ)
    (hgrad : EdgeValuesAt mid.mem (mid.regs 8) fmt.limbBits L fmt.precision H.E (coreGrad G forest g))
    (hk : 0 < k) (hm : H.m ≤ M) (hn : H.n ≤ N)
    (hgEnd : mid.regs 6 + dynGraphSize vc ec ≤ mid.regs 4)
    (hlenEnd : mid.regs 7 + ec * L ≤ mid.regs 4)
    (hgradEnd : mid.regs 8 + inputEC * L ≤ mid.regs 4) (hec : ec ≤ inputEC)
    (hpos : ∀ e ∈ H.E, 0 < ℓ e) (hz : ZeroFrom mid.mem (mid.regs 4))
    (hroom : mid.regs 4 + allocation 5 [mid.regs 6, mid.regs 7, mid.regs 8, mid.regs 4] < 2 ^ w) :
    let model := tool.init k M N H (fun e => if e ∈ H.E then ℓ e else 0)
      (fun e => if e ∈ H.E then coreGrad G forest g e else 0)
    ∃ out ret cost y, Runs w p ω (shiftDeeperLevel restart read forestOp copy sort cell init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = mid.regs 4 ∧ out.regs 4 = ret ∧
      R.rep (mid.regs 4) model y out.mem ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k model H ∧
      R.Respects (fun _ => False) (mid.regs 4)
        (allocation 5 [mid.regs 6, mid.regs 7, mid.regs 8, mid.regs 4])
        mid.mem ret (mid.regs 4) y out.mem ∧
      cost + R.phi (mid.regs 4) y out.mem ≤ prefixCost + costs.factor M N * (M + 1) * k + 12 := by
  have hgradRoom : mid.regs 8 + ec * L ≤ mid.regs 4 :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right L hec) _).trans hgradEnd
  obtain ⟨out, ret, cost, y, hr, hb, hhandle, hheap, hrep, hinput, hframe, hcost⟩ :=
    rebuildLevelInit_tables_runs (ω := ω) ℓ (coreGrad G forest g) himpl rfl rfl rfl rfl
      hk hgraph hm hn hgEnd hlenEnd hgradRoom hlen hgrad hpos hz hroom
  exact ⟨out, ret, prefixCost + cost + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, cost, hprep, hr, rfl⟩),
    hb, hhandle, hheap, hrep, hinput, hframe, by omega⟩

/-- When both deeper inputs vanish off the active edge set, the decoded
initializer is the exact model initializer. -/
theorem shiftDeeperLevel_init_eq_of_support
    {tool : SparseCoreRestartTool} {G H : MGraph} {forest : LSF} {k M N : ℕ}
    {ℓ g : ℕ → ℝ}
    (hℓ : ∀ e ∉ H.E, ℓ e = 0)
    (hg : ∀ e ∉ H.E, coreGrad G forest g e = 0) :
    tool.init k M N H (fun e => if e ∈ H.E then ℓ e else 0)
      (fun e => if e ∈ H.E then coreGrad G forest g e else 0) =
      tool.init k M N H ℓ (coreGrad G forest g) := by
  congr 1
  · funext e
    by_cases he : e ∈ H.E
    · simp [he]
    · simp [he, hℓ e he]
  · funext e
    by_cases he : e ∈ H.E
    · simp [he]
    · simp [he, hg e he]

/-- Run the deeper rebuild and identify its represented tool state with
the Shift model under the two off-edge support conditions. -/
theorem shiftDeeperLevel_exact_runs {w L k M N vc ec inputEC restart read forestOp copy sort cell init : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G H : MGraph} {forest : LSF}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st mid : State} {ω : ℕ → Bool}
    {prefixCost : ℕ} (ℓ g : ℕ → ℝ)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool H k M N vc ec costs allocation))
    (hprep : Runs w p ω (shiftRestartPrepareGradients restart read forestOp copy sort cell) st .normal mid prefixCost)
    (hgraph : DynGraphAt mid.mem (mid.regs 6) vc ec H)
    (hlen : EdgeValuesAt mid.mem (mid.regs 7) fmt.limbBits L fmt.precision H.E ℓ)
    (hgrad : EdgeValuesAt mid.mem (mid.regs 8) fmt.limbBits L fmt.precision H.E (coreGrad G forest g))
    (hk : 0 < k) (hm : H.m ≤ M) (hn : H.n ≤ N)
    (hgEnd : mid.regs 6 + dynGraphSize vc ec ≤ mid.regs 4)
    (hlenEnd : mid.regs 7 + ec * L ≤ mid.regs 4)
    (hgradEnd : mid.regs 8 + inputEC * L ≤ mid.regs 4) (hec : ec ≤ inputEC)
    (hpos : ∀ e ∈ H.E, 0 < ℓ e) (hz : ZeroFrom mid.mem (mid.regs 4))
    (hℓSupport : ∀ e ∉ H.E, ℓ e = 0)
    (hgSupport : ∀ e ∉ H.E, coreGrad G forest g e = 0)
    (hroom : mid.regs 4 + allocation 5 [mid.regs 6, mid.regs 7, mid.regs 8, mid.regs 4] < 2 ^ w) :
    let model := tool.init k M N H ℓ (coreGrad G forest g)
    ∃ out ret cost y, Runs w p ω (shiftDeeperLevel restart read forestOp copy sort cell init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = mid.regs 4 ∧ out.regs 4 = ret ∧
      R.rep (mid.regs 4) model y out.mem ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k model H ∧
      R.Respects (fun _ => False) (mid.regs 4)
        (allocation 5 [mid.regs 6, mid.regs 7, mid.regs 8, mid.regs 4])
        mid.mem ret (mid.regs 4) y out.mem ∧
      cost + R.phi (mid.regs 4) y out.mem ≤ prefixCost + costs.factor M N * (M + 1) * k + 12 := by
  have hrun := shiftDeeperLevel_runs (ω := ω) ℓ g himpl hprep hgraph hlen hgrad
    hk hm hn hgEnd hlenEnd hgradEnd hec hpos hz hroom
  dsimp only at hrun ⊢
  rwa [shiftDeeperLevel_init_eq_of_support (tool := tool) (k := k) (M := M) (N := N) hℓSupport hgSupport] at hrun

/-- The Shift prefix feeds the first deeper initializer with room for all
three input blocks. The run represents the model initializer when the
length and gradient agree with the machine's zero extension. -/
theorem shiftDeeperLevel_from_readout_runs
    {w copy sort entry a vc ec heap limbs gradients base vcG ecG nextBase nextVC nextEC
      init k M N : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {restart read forestOp prefixCost : ℕ} {p : Program} {initial st : State} {ω : ℕ → Bool}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {op : ℕ → ℕ}
    (hinit : R.Implements w p init op
      (sparseCoreMachineContract fmt limbs tool H k M N nextVC nextEC costs allocation))
    (hprefix : Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      initial .normal st prefixCost)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec fmt.limbBits limbs fmt.precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + forest.T.n ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients fmt.limbBits limbs fmt.precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradEnd : ∀ e ∈ G.E, gradients + e * limbs + limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h13 : st.regs 13 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) fmt.limbBits limbs fmt.precision H.E nextLengths)
    (hlenEnd : st.regs 7 + nextEC * limbs ≤ heap) (hcapacity : nextEC ≤ ecG)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc fmt.limbBits limbs fmt.precision r seen →
        EdgeValuesAt s.mem gradients fmt.limbBits limbs fmt.precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) fmt.limbBits limbs
        Num.Fits fmt.limbBits limbs (Num.intVal s.mem (base + parent * limbs) fmt.limbBits limbs +
          ((if direction then value else 0) - (if direction then 0 else value))))
    (hfitScan : ∀ mem,
      ForestPotentialsAt mem (heap + forest.T.n) fmt.limbBits limbs fmt.precision forest.T g forest.T.V →
      EdgeValuesAt mem gradients fmt.limbBits limbs fmt.precision G.E g →
      ∀ e ∈ G.E, Num.Fits fmt.limbBits limbs
        (Num.intVal mem (gradients + e * limbs) fmt.limbBits limbs +
          (Num.intVal mem (heap + forest.T.n + G.head e * limbs) fmt.limbBits limbs -
            Num.intVal mem (heap + forest.T.n + G.tail e * limbs) fmt.limbBits limbs)))
    (hk : 0 < k) (hm : H.m ≤ M) (hn : H.n ≤ N)
    (hpos : ∀ e ∈ H.E, 0 < nextLengths e)
    (hℓSupport : ∀ e ∉ H.E, nextLengths e = 0)
    (hgSupport : ∀ e ∉ H.E, coreGrad G forest g e = 0)
    (hallocRoom : ∀ graph lengths gradient b,
      graph = nextBase → lengths = st.regs 7 →
      gradient + ecG * limbs ≤ b →
      b ≤ heap + forest.T.n + vc * limbs + limbs + vc + vc +
        3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m →
      b + allocation 5 [graph, lengths, gradient, b] < 2 ^ w) :
    let model := tool.init k M N H nextLengths (coreGrad G forest g)
    ∃ out ret cost y,
      Runs w p ω (shiftDeeperLevel restart read forestOp copy sort entry init)
        initial .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 4 = ret ∧
      R.rep (out.regs 3) model y out.mem ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k model H ∧
      heap ≤ out.regs 3 ∧ out.regs 3 ≤ ret ∧ ZeroFrom out.mem ret ∧
      (∀ addr, R.foot (out.regs 3) y addr → out.regs 3 ≤ addr ∧ addr < ret) ∧
      DynGraphAt out.mem nextBase nextVC nextEC H ∧
      EdgeValuesAt out.mem (st.regs 7) fmt.limbBits limbs fmt.precision H.E nextLengths ∧
      nextBase + dynGraphSize nextVC nextEC ≤ out.regs 3 ∧
      st.regs 7 + nextEC * limbs ≤ out.regs 3 ∧
      (∃ gradient, gradient + nextEC * limbs ≤ out.regs 3 ∧
        EdgeValuesAt out.mem gradient fmt.limbBits limbs fmt.precision H.E
          (coreGrad G forest g)) ∧
      cost + R.phi (out.regs 3) y out.mem ≤
        prefixCost + 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + costs.factor M N * (M + 1) * k + 215 := by
  obtain ⟨mid, c, hprep, h6', h7', h8', hg, hl, hgrad, hgb, hlb, hgradb, hz', hlo, hhi, _, hc⟩ :=
    shiftRestartPrepareGradients_runs hprefix hcopy hsort hreadout ha hh hlimbs hz
      hgraphEnd hlistEnd hsortRoom hcount hw hforest hvalues hsub hgradEnd
      himpl hG hGEnd hvertices hH hHEnd hHE h6 h13 h50 h15 h16 h17
      nextLengths hlen hlenEnd hcapacity hwScan hspace hfit hfitScan
  obtain ⟨out, ret, cost, y, hrun, hb, hhandle, hheap, hrep, hinput, hframe, hcost⟩ :=
    shiftDeeperLevel_exact_runs nextLengths g hinit hprep hg hl hgrad hk hm hn hgb hlb
      hgradb (Nat.le_refl _) hpos hz' hℓSupport hgSupport
      (hallocRoom _ _ _ _ h6' h7' h8' hhi)
  have hbelow (addr : ℕ) (ha : addr < mid.regs 4) : out.mem addr = mid.mem addr :=
    hframe.2.2.2.1 addr ha (fun h => h)
  have hg' := hg.of_agree (fun addr _ ha => hbelow addr (ha.trans_le hgb))
  have cellBelow (ptr e j : ℕ) (he : e ∈ H.E) (hj : j < limbs)
      (hblock : ptr + nextEC * limbs ≤ mid.regs 4) : ptr + e * limbs + j < mid.regs 4 := by
    have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt (hg.2.2.1 e he))
    rw [Nat.succ_mul] at hmul
    omega
  have hl' := hl.congr (fun e he j hj => hbelow _ (cellBelow _ e j he hj hlb))
  have hgrad' := hgrad.congr (fun e he j hj => hbelow _ (cellBelow _ e j he hj hgradb))
  refine ⟨out, ret, cost, y, hrun, hb, hheap, hhandle.symm ▸ hrep, hinput,
    hhandle.symm ▸ hlo, hhandle.symm ▸ hframe.1, hframe.2.2.1, ?_, h6' ▸ hg', h7' ▸ hl',
    hhandle.symm ▸ (h6' ▸ hgb), hhandle.symm ▸ (h7' ▸ hlb),
    ⟨mid.regs 8, hhandle.symm ▸ hgradb, hgrad'⟩, ?_⟩
  · intro addr ha
    rw [hhandle] at ha ⊢
    exact (hframe.2.2.2.2 addr ha).resolve_left (fun h => h)
  · rw [hhandle]
    omega

/-- Initialize and record the first rebuilt level after a branch shift
(Algorithm 1, page 20). -/
@[expose] def shiftInstallDeeperLevel (restart read forestOp copy sort cell init : ℕ) : Stmt :=
  shiftDeeperLevel restart read forestOp copy sort cell init ;; storeRebuiltLevel

/-- The descriptor stores the new handle and branch zero. Installing it
adds eight steps to initialization and preserves the tool potential. -/
theorem shiftInstallDeeperLevel_runs
    {w restart read forestOp copy sort cell init handleCell branchCell cost : ℕ}
    {tool : SparseCoreRestartTool} {R : DSRep tool.State} {model : tool.State} {x : R.τ}
    {p : Program} {initial mid : State} {ω : ℕ → Bool}
    (hlocal : R.Local)
    (hinit : Runs w p ω (shiftDeeperLevel restart read forestOp copy sort cell init)
      initial .normal mid cost)
    (hh : initial.regs 51 = handleCell) (hb : initial.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell)
    (hhBelow : handleCell < mid.regs 3) (hbBelow : branchCell < mid.regs 3)
    (hheap : mid.regs 3 ≤ mid.regs 4) (hzero : ZeroFrom mid.mem (mid.regs 4))
    (hfoot : ∀ a, R.foot (mid.regs 3) x a → mid.regs 3 ≤ a ∧ a < mid.regs 4)
    (hrep : R.rep (mid.regs 3) model x mid.mem) :
    ∃ out, Runs w p ω (shiftInstallDeeperLevel restart read forestOp copy sort cell init)
        initial .normal out (cost + 8) ∧
      out.mem handleCell = out.regs 3 ∧ out.mem branchCell = 0 ∧
      R.rep (out.regs 3) model x out.mem ∧
      R.phi (out.regs 3) x out.mem = R.phi (mid.regs 3) x mid.mem ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ a, R.foot (out.regs 3) x a → out.regs 3 ≤ a ∧ a < out.regs 4) ∧
      (∀ a, a ≠ handleCell → a ≠ branchCell → out.mem a = mid.mem a) ∧
      out.regs = mid.regs := by
  have hhMid := (shiftDeeperLevel_preserves_regs hinit (by decide : 51 ≤ 51)).trans hh
  have hbMid := (shiftDeeperLevel_preserves_regs hinit (by decide : 51 ≤ 52)).trans hb
  obtain ⟨out, hrun, hhandle, hbranch, hrep', hphi, hframe, hregs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) hlocal hhMid hbMid hne hhBelow hbBelow
      (fun a ha => (hfoot a ha).1) hrep
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 7, hinit, hrun, by omega⟩),
    hhandle, hbranch, hrep', hphi, ?_, hregs.symm ▸ hfoot, hframe, hregs⟩
  rw [hregs]
  intro a ha
  exact (hframe a (by omega) (by omega)).trans (hzero a ha)

/-- Installing the descriptor writes memory and keeps the caller registers
that the Shift initialization preserves. -/
theorem shiftInstallDeeperLevel_preserves_regs
    {w restart read forestOp copy sort cell init cost r : ℕ}
    {p : Program} {st out : State} {ω : ℕ → Bool}
    (hrun : Runs w p ω (shiftInstallDeeperLevel restart read forestOp copy sort cell init)
      st .normal out cost)
    (hr : 51 ≤ r) : out.regs r = st.regs r := by
  rcases runs_seq_iff.mp hrun with ⟨_, _, _, h, _⟩ | ⟨mid, _, _, hi, hs, _⟩
  · cases h
  rcases runs_seq_iff.mp hs with ⟨_, _, _, h, _⟩ | ⟨first, _, _, h₁, h₂, _⟩
  · cases h
  obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h₁
  obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h₂
  exact shiftDeeperLevel_preserves_regs (out := mid) hi hr

/-- The restarted readouts initialize and record the first deeper tool,
with both descriptor cells below its allocation (Algorithm 1, page 20). -/
theorem shiftInstallDeeperLevel_from_readout_runs
    {w copy sort entry a vc ec heap limbs gradients base vcG ecG nextBase nextVC nextEC
      init k M N handleCell branchCell : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {restart read forestOp prefixCost : ℕ} {p : Program} {initial st : State} {ω : ℕ → Bool}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {op : ℕ → ℕ}
    (hinit : R.Implements w p init op
      (sparseCoreMachineContract fmt limbs tool H k M N nextVC nextEC costs allocation))
    (hprefix : Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      initial .normal st prefixCost)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec fmt.limbBits limbs fmt.precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + forest.T.n ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients fmt.limbBits limbs fmt.precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradEnd : ∀ e ∈ G.E, gradients + e * limbs + limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h13 : st.regs 13 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) fmt.limbBits limbs fmt.precision H.E nextLengths)
    (hlenEnd : st.regs 7 + nextEC * limbs ≤ heap) (hcapacity : nextEC ≤ ecG)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc fmt.limbBits limbs fmt.precision r seen →
        EdgeValuesAt s.mem gradients fmt.limbBits limbs fmt.precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) fmt.limbBits limbs
        Num.Fits fmt.limbBits limbs (Num.intVal s.mem (base + parent * limbs) fmt.limbBits limbs +
          ((if direction then value else 0) - (if direction then 0 else value))))
    (hfitScan : ∀ mem,
      ForestPotentialsAt mem (heap + forest.T.n) fmt.limbBits limbs fmt.precision forest.T g forest.T.V →
      EdgeValuesAt mem gradients fmt.limbBits limbs fmt.precision G.E g →
      ∀ e ∈ G.E, Num.Fits fmt.limbBits limbs
        (Num.intVal mem (gradients + e * limbs) fmt.limbBits limbs +
          (Num.intVal mem (heap + forest.T.n + G.head e * limbs) fmt.limbBits limbs -
            Num.intVal mem (heap + forest.T.n + G.tail e * limbs) fmt.limbBits limbs)))
    (hk : 0 < k) (hm : H.m ≤ M) (hn : H.n ≤ N)
    (hpos : ∀ e ∈ H.E, 0 < nextLengths e)
    (hℓSupport : ∀ e ∉ H.E, nextLengths e = 0)
    (hgSupport : ∀ e ∉ H.E, coreGrad G forest g e = 0)
    (hallocRoom : ∀ graph lengths gradient b,
      graph = nextBase → lengths = st.regs 7 →
      gradient + ecG * limbs ≤ b →
      b ≤ heap + forest.T.n + vc * limbs + limbs + vc + vc +
        3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m →
      b + allocation 5 [graph, lengths, gradient, b] < 2 ^ w)
    (hhCell : initial.regs 51 = handleCell) (hbCell : initial.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap) :
    let model := tool.init k M N H nextLengths (coreGrad G forest g)
    ∃ out ret cost y,
      Runs w p ω (shiftInstallDeeperLevel restart read forestOp copy sort entry init)
        initial .normal out cost ∧
      out.mem handleCell = out.regs 3 ∧ out.mem branchCell = 0 ∧ out.regs 4 = ret ∧
      R.rep (out.regs 3) model y out.mem ∧ ZeroFrom out.mem ret ∧
      (∀ addr, R.foot (out.regs 3) y addr → out.regs 3 ≤ addr ∧ addr < ret) ∧
      cost + R.phi (out.regs 3) y out.mem ≤
        prefixCost + 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + costs.factor M N * (M + 1) * k + 223 := by
  obtain ⟨mid, ret, c, y, hrun, _, hret, hrep, _, hlo, hhi, hz', hfoot, _, _, _, _, _, hc⟩ :=
    shiftDeeperLevel_from_readout_runs hinit hprefix hcopy hsort hreadout ha hh hlimbs hz
      hgraphEnd hlistEnd hsortRoom hcount hw hforest hvalues hsub hgradEnd
      himpl hG hGEnd hvertices hH hHEnd hHE h6 h13 h50 h15 h16 h17
      nextLengths hlen hlenEnd hcapacity hwScan hspace hfit hfitScan
      hk hm hn hpos hℓSupport hgSupport hallocRoom
  obtain ⟨out, hr, hd, hb, hrep', hphi, hz'', hfoot', _, hregs⟩ :=
    shiftInstallDeeperLevel_runs hinit.1 hrun hhCell hbCell hne
      (hhBelow.trans_le hlo) (hbBelow.trans_le hlo) (hret.symm ▸ hhi)
      (hret.symm ▸ hz') (hret.symm ▸ hfoot) hrep
  have hret' : out.regs 4 = ret := hregs ▸ hret
  exact ⟨out, ret, c + 8, y, hr, hd, hb, hret', hrep', hret' ▸ hz'',
    hret' ▸ hfoot', by rw [hphi]; omega⟩

/-- The first installed deeper core represents the Shift model's state
at level `i + 1` when its inputs are the restarted graph and numbers.
The installation proof provides the representation on the right. -/
theorem shiftNextCore_rep_iff
    {T : SparseCoreRestartTool} {last : LastLevelTool} {P : ChainParams}
    (chain : ChainState T P) (i : ℕ) (hi : i + 1 < P.d)
    {R : DSRep T.State} {handle : ℕ} {x : R.τ} {mem : ℕ → ℕ} :
    let next := (algorithm1_shift T last P chain i).1
    let j := (chain.bran i + 1) % P.k
    let core := T.restart (chain.scState i) j
    let forest := T.lsfs core j
    R.rep handle (next.scState (i + 1)) x mem ↔
      R.rep handle (T.init P.k (chain.lvlM (i + 1)) chain.N₀ (T.S core j)
        (coreLen forest (chain.toTreeChain.chainLen chain.ℓ i))
        (coreGrad (chain.G i) forest (chain.toTreeChain.chainGrad chain.g i))) x mem := by
  dsimp only
  have hlt : i < P.d := by omega
  have hgraph := algorithm1_shift_graph_prefix T last P chain i (i + 1) hlt le_rfl
  simp only [ite_true] at hgraph
  obtain ⟨hlen, hgrad⟩ := shiftNextLevelNumbers T last P chain i hlt
  rw [shiftNextCoreBuild_eq T last P chain i hi, hgraph, hlen, hgrad]

/-- The first deeper descriptor identifies the shifted model's tool and
selected branch (Algorithm 1, page 20). -/
theorem shiftNextCore_descriptor
    {T : SparseCoreRestartTool} {last : LastLevelTool} {P : ChainParams}
    (chain : ChainState T P) (i : ℕ) (hi : i + 1 < P.d)
    {R : DSRep T.State} {handleCell branchCell handle : ℕ} {x : R.τ} {mem : ℕ → ℕ} :
    let next := (algorithm1_shift T last P chain i).1
    let j := (chain.bran i + 1) % P.k
    let core := T.restart (chain.scState i) j
    let forest := T.lsfs core j
    mem handleCell = handle → mem branchCell = 0 →
    R.rep handle (T.init P.k (chain.lvlM (i + 1)) chain.N₀ (T.S core j)
      (coreLen forest (chain.toTreeChain.chainLen chain.ℓ i))
      (coreGrad (chain.G i) forest (chain.toTreeChain.chainGrad chain.g i))) x mem →
    mem branchCell = next.bran (i + 1) ∧
      R.rep (mem handleCell) (next.scState (i + 1)) x mem := by
  dsimp only
  intro hh hb hrep
  rw [hh, algorithm1_shift_rebuilt_branch T last P chain i (i + 1) (Nat.lt_succ_self i) hi]
  exact ⟨hb, (shiftNextCore_rep_iff (last := last) chain i hi).2 hrep⟩

end MinCostFlow.MinRatio
