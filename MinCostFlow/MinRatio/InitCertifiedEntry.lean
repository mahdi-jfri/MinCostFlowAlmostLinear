module

public import MinCostFlow.MinRatio.InitCertifiedSolver
public import MinCostFlow.LastLevelProgram.FixedPoint
import MinCostFlow.LastLevelProgram.RepresentativeGraph

/-!
# Handoff from certified thresholds to level initialization

Preserve the rebuild table while restoring the solver format and allocating
the solver header, then pass the framed table to level construction.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM LastLevelProgram SparseCore

/-- The rounded terminal initializer uses only lengths on the input
graph. This permits the zero extension used by the machine contract. -/
theorem fixedPointLastLevel_build_congr
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    {G : MGraph} {len len' : ℕ → ℝ} (hG : G.IsValid)
    (hlen : ∀ e ∈ G.E, len e = len' e) :
    (LastLevelProgram.fixedPointLastLevelTool oracle C).build G len =
      (LastLevelProgram.fixedPointLastLevelTool oracle C).build G len' := by
  classical
  have hn (e : ℕ) (he : e ∈ nonLoopEdges G) : len e = len' e :=
    hlen e ((Finset.mem_filter.mp he).1)
  have hshort (e : ℕ) (he : e ∈ nonLoopEdges G) :
      shortestEdge G len (edgePairKey G e) = shortestEdge G len' (edgePairKey G e) := by
    obtain ⟨hf, hkey, _⟩ := shortestEdge_spec (ℓ := len) he
    conv_rhs => rw [← hkey]
    apply eq_shortestEdge_of_minimal hf
    intro g hg hgkey
    have hkey' : edgePairKey G g = edgePairKey G e := hgkey.trans hkey
    obtain ⟨_, _, hmin⟩ := shortestEdge_spec (ℓ := len) hg
    rw [hkey'] at hmin
    rw [← hn _ hf, ← hn _ hg]
    exact hmin.elim (fun h => ⟨h.le, fun heq => (h.ne heq).elim⟩)
      (fun h => ⟨h.1.le, fun _ => h.2⟩)
  have hrep : representativeGraph G len = representativeGraph G len' := by
    unfold representativeGraph
    have he : ((nonLoopEdges G).image (edgePairKey G)).image (shortestEdge G len) =
        ((nonLoopEdges G).image (edgePairKey G)).image (shortestEdge G len') := by
      apply Finset.image_congr
      intro k hk
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
      exact hshort e he
    rw [he]
  have hsafe : LSF.safeLen (representativeGraph G len') len =
      LSF.safeLen (representativeGraph G len') len' := by
    funext e
    by_cases he : e ∈ (representativeGraph G len').E
    · rw [LSF.safeLen_eq_of_mem len he, LSF.safeLen_eq_of_mem len' he]
      exact hlen e ((representativeGraph_subgraph hG len').2.1 he)
    · simp [LSF.safeLen, he]
  have hquery (P : ℕ) :
      stretchQuery oracle (representativeGraph G len') len P =
        stretchQuery oracle (representativeGraph G len') len' P := by
    unfold stretchQuery
    rw [hsafe]
  change (fixedPointLastLevelTool oracle C).build G len = _
  simp only [fixedPointLastLevelTool]
  split
  · rw [hrep]
    simp only [hquery, hsafe]
    congr 1
    funext j
    congr 1
    funext e
    split
    · rename_i he
      rw [hshort e he]
    · rfl
  · rfl

/-- At the root, the dense IPM vector and the sparse-core decoder
agree at every edge name. The named graph uses exactly the dense range. -/
theorem initNamedGraph_readEdgeValues_eq_readVector
    (I : Instance) (mem : ℕ → ℕ) (base h limbs precision : ℕ) :
    readEdgeValues mem base h limbs precision (IPM.namedInstance I).E =
      IPM.Machine.readVector mem base h limbs precision I.m := by
  classical
  funext e
  simp only [readEdgeValues, IPM.Machine.readVector, IPM.namedInstance, Finset.mem_range]

/-- The sparse-core Init postcondition at level zero matches the vectors
supplied by the IPM Init contract. -/
theorem initNamedGraph_sparseCore_model
    {w limbs k M N vc ec graph lengths gradient heap : ℕ}
    (fmt : Num.Format w) (T : Chain.SparseCoreRestartTool) (I : Instance)
    (costs : SparseCoreMachineCosts) (allocation : ℕ → List ℕ → ℕ)
    {mem mem' : ℕ → ℕ} {state : T.State}
    (hpost : (sparseCoreMachineContract fmt limbs T (IPM.namedInstance I)
      k M N vc ec costs allocation).initPost [graph, lengths, gradient, heap] mem state mem') :
    state = T.init k M N (IPM.namedInstance I)
      (IPM.Machine.readVector mem lengths fmt.limbBits limbs fmt.precision I.m)
      (IPM.Machine.readVector mem gradient fmt.limbBits limbs fmt.precision I.m) := by
  change state = T.init k M N (IPM.namedInstance I)
    (readEdgeValues mem lengths fmt.limbBits limbs fmt.precision (IPM.namedInstance I).E)
    (readEdgeValues mem gradient fmt.limbBits limbs fmt.precision (IPM.namedInstance I).E) at hpost
  simpa only [initNamedGraph_readEdgeValues_eq_readVector] using hpost

/-- The workspace and level stages compose with the certified table and
the restored solver header. -/
theorem initCertifiedWorkspaceAndLevels_runs
    {w power bits load log pack clog coefficient h extend mul shift add roundEntry c₁ c₂ c₃ c₄ : ℕ}
    {table m V depth branch psi alphaPtr quality epsilon limbs precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st saved work scaled ready finished : State}
    {levels inconclusive : Stmt} {entry : ℕ → ℕ}
    (hr : Runs w p ω saveCertifiedThresholdFormat st .normal saved 14)
    (h67 : saved.regs 128 = st.regs 67) (h68 : saved.regs 129 = st.regs 68)
    (h4 : saved.regs 130 = st.regs 4) (h0 : saved.regs 131 = st.regs 0)
    (h6 : saved.regs 132 = st.regs 6)
    (ht : Runs w p ω (initCertifiedEndpointWorkspace power bits clog coefficient h) saved .normal work c₁)
    (hu : Runs w p ω rescaleCertifiedSparsifierLength work .normal scaled c₂)
    (hv : Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
      scaled .normal ready c₃)
    (hw : 1 < 2 ^ w)
    (hx : Runs w p ω (initSparseCoreThresholdsFromEndpoints power load extend mul shift add roundEntry h)
      {ready with regs := Function.update (Function.update ready.regs 126 (ready.regs 114)) 127 (ready.regs 115)}
      .normal finished c₄)
    (h83 : finished.regs 83 = table) (h98 : finished.regs 98 = table + (depth + 1))
    (hentries : ∀ j ≤ depth, finished.mem (table + j) = entry j)
    (ha : finished.regs 101 = alphaPtr)
    (hm : st.regs 0 = m) (hV : finished.regs 102 = V) (hd : finished.regs 75 = depth)
    (hb : finished.regs 76 = branch) (hpsi : st.regs 6 = psi)
    (hq : finished.regs 72 = quality) (he : finished.regs 73 = epsilon)
    (hL : finished.regs 103 = limbs) (hP : finished.regs 104 = precision)
    (hspace : 80 * limbs + 260 < 2 ^ w)
    (hz : ZeroFrom finished.mem (table + (depth + 1)))
    (hroom : table + 3 * (depth + 1) + 17 < 2 ^ w)
    (hlevels : ∀ header,
      header.regs 74 = table + (depth + 1) →
      header.regs 77 = table + (depth + 1) + 17 →
      header.regs 77 + (depth + 1) + (depth + 1) < 2 ^ w →
      header.regs 83 = table → ZeroFrom header.mem (table + (depth + 1) + 17) →
      ChainInitParametersAt header.mem (table + (depth + 1)) m V depth branch psi alphaPtr quality epsilon →
      MinRatioNumericHeaderAt header.mem (table + (depth + 1)) limbs precision
        (20 * (4 * limbs + 8) + 100) (20 * (4 * limbs + 8) + 100) →
      (∀ j ≤ depth, header.mem (table + j) = entry j) →
      (∀ a < table + (depth + 1), header.mem a = finished.mem a) →
      header.regs 67 = st.regs 67 → header.regs 68 = st.regs 68 →
      (∀ r ∈ ([69, 70, 71, 75] : List ℕ), header.regs r = finished.regs r) →
      ∃ out cost, Runs w p ω levels header .normal out cost) :
    ∃ out cost, Runs w p ω
      (initCertifiedThresholdsWithWorkspace power bits load log pack clog coefficient h extend mul shift add roundEntry ;;
        continueSolverInit levels inconclusive)
      st .normal out (c₁ + c₂ + c₃ + c₄ + 161 + cost) := by
  obtain ⟨checked, hchecked, h67', h68', _, h0', h6', _, _, hcert, hmem, hcursor, hkeep⟩ :=
    initCertifiedThresholdsWithWorkspace_runs hr h67 h68 h4 h0 h6 ht hu hv hw hx
  have keep (r : ℕ) (h₁ : r ≠ 99 := by decide) (h₂ : r ≠ 67 := by decide)
      (h₃ : r ≠ 68 := by decide) (h₄ : r ≠ 4 := by decide) (h₀ : r ≠ 0 := by decide)
      (h₆ : r ≠ 6 := by decide) (h₅ : r ≠ 114 := by decide)
      (h₆' : r ≠ 115 := by decide) (h₇ : r ≠ 10 := by decide) :=
    hkeep r h₁ h₂ h₃ h₄ h₀ h₆ h₅ h₆' h₇
  have htable : ∀ j < depth + 1, checked.mem (table + j) = entry j :=
    fun j hj => (congrFun hmem _).trans (hentries j (Nat.le_of_lt_succ hj))
  obtain ⟨out, cost, hc⟩ :=
    continueSolverInit_thresholdTable_runs hcert hw (hcursor.trans h98) ((keep 83).trans h83)
      htable le_rfl ((keep 101).trans ha) (h0'.trans hm) ((keep 102).trans hV)
      ((keep 75).trans hd) ((keep 76).trans hb) (h6'.trans hpsi)
      ((keep 72).trans hq) ((keep 73).trans he) ((keep 103).trans hL) ((keep 104).trans hP)
      hspace (hmem.symm ▸ hz) (by omega)
      (fun header ha hb hc hd he hf hg hframe hregs =>
        hlevels header ha hb (by omega) hc hd he hf (fun j hj => hg j (Nat.lt_succ_of_le hj))
          (fun a ha => (hframe a ha).trans (congrFun hmem a))
          ((hregs 67 (by decide)).trans h67') ((hregs 68 (by decide)).trans h68')
          (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            exact (hregs r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans
              (keep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
  exact ⟨out, cost, runs_seq_iff.mpr (Or.inr ⟨checked, _, _, hchecked, hc, by omega⟩)⟩

end MinCostFlow.MinRatio
