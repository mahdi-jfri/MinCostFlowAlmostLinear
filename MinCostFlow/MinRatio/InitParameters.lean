module

public import MinCostFlow.Num.IPM.Alpha
public import MinCostFlow.IPM.Machine.PrecisionHiddenRange
public import MinCostFlow.IPM.Machine.PrecisionRecord
public import MinCostFlow.IPM.Machine.PrecisionSelection
public import MinCostFlow.IPM.Machine.SolverDataStructures
public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.Chain.Theorem5_1Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Exec
import MinCostFlow.MinRatio.ShiftForestScan
public import WordRAM.Logic

/-!
# Numeric parameters for min-ratio initialization

Definition 4.4 (page 14) uses the IPM barrier and hidden stability
parameters. The barrier block is obtained from the dyadic exponent
routine using three fewer bits of fractional precision.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Decode the seven-word Init arguments. Preserve the graph, gradient,
and length pointers in registers 69 through 71 and obtain the barrier
routine arguments from the packed graph edge count and the Init words. -/
@[expose] def prepareMinRatioInitAt (edgeOffset : ℕ) : Stmt :=
  .assign 69 (.reg 0) ;; .assign 70 (.reg 1) ;; .assign 71 (.reg 2) ;;
  .assign 0 (.load (.bin .add (.reg 0) (.const edgeOffset))) ;;
  .assign 1 (.reg 5) ;; .assign 2 (.reg 3) ;; .assign 3 (.reg 4) ;; .assign 4 (.reg 6)

/-- Init obtains `M₀ = m` and the supplied penalty directly from its
runtime inputs while retaining the three input table pointers. -/
theorem prepareMinRatioInitAt_runs {w graph gradient lengths limbs precision V heap edgeOffset m : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    (hm : mem (graph + edgeOffset) = m)
    (hroom : graph + edgeOffset < 2 ^ w) :
    ∃ out, Runs w p ω (prepareMinRatioInitAt edgeOffset)
      (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out 26 ∧
      out.regs 0 = m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧
      out.regs 3 = precision ∧ out.regs 4 = heap ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      out.mem = mem ∧ out.pos = pos := by
  let s0 := startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 69 graph }
  let s2 := { s1 with regs := Function.update s1.regs 70 gradient }
  let s3 := { s2 with regs := Function.update s2.regs 71 lengths }
  let s4 := { s3 with regs := Function.update s3.regs 0 m }
  let s5 := { s4 with regs := Function.update s4.regs 1 V }
  let s6 := { s5 with regs := Function.update s5.regs 2 limbs }
  let s7 := { s6 with regs := Function.update s6.regs 3 precision }
  let s8 := { s7 with regs := Function.update s7.regs 4 heap }
  have hoff : edgeOffset < 2 ^ w := by omega
  have hr1 : Runs w p ω (.assign 69 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨graph, rfl, rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 70 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨gradient, rfl, rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 71 (.reg 2)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨lengths, rfl, rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 0 (.load (.bin .add (.reg 0) (.const edgeOffset)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨m, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hoff, hroom, hm], rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 1 (.reg 5)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨V, rfl, rfl, rfl, rfl⟩
  have hr6 : Runs w p ω (.assign 2 (.reg 3)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨limbs, rfl, rfl, rfl, rfl⟩
  have hr7 : Runs w p ω (.assign 3 (.reg 4)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨precision, rfl, rfl, rfl, rfl⟩
  have hr8 : Runs w p ω (.assign 4 (.reg 6)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨heap, rfl, rfl, rfl, rfl⟩
  refine ⟨s8, ?_, ?_⟩
  · unfold prepareMinRatioInitAt
    refine runs_seq_iff.mpr (Or.inr ⟨s1, 2, 23, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 2, 20, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 2, 17, hr3, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s4, 5, 11, hr4, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s5, 2, 8, hr5, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s6, 2, 5, hr6, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s7, 2, 2, hr7, hr8, rfl⟩)
  · simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, startState]

/-- Decode the Init arguments for a graph already in dynamic layout. -/
@[expose] def prepareMinRatioInit : Stmt :=
  prepareMinRatioInitAt 3

/-- Read the edge count from the dynamic graph header. -/
theorem prepareMinRatioInit_runs {w graph gradient lengths limbs precision V heap vc ec : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    (hG : DynSpanner.Program.DynGraphAt mem graph vc ec G)
    (hroom : graph + 3 < 2 ^ w) :
    ∃ out, Runs w p ω prepareMinRatioInit
      (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out 26 ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧
      out.regs 3 = precision ∧ out.regs 4 = heap ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      out.mem = mem ∧ out.pos = pos :=
  prepareMinRatioInitAt_runs hG.2.2.2.2.2.2.1 hroom

/-- Read `m, V, L, P, heap` from registers 0 through 4. The alpha call
returns the advanced heap in register 5. -/
@[expose] def initMinRatioAlpha (alpha : ℕ) : Stmt :=
  .call 5 alpha [.reg 0, .reg 1, .reg 2, .bin .sub (.reg 3) (.const 3), .reg 4]

/-- The alpha block at the incoming heap represents the model's
`alphaPrime m V / 8` when read at the caller's precision. -/
theorem initMinRatioAlpha_runs
    {w h alpha m V limbs precision heap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hm : st.regs 0 = m) (hV : st.regs 1 = V) (hL : st.regs 2 = limbs)
    (hP : st.regs 3 = precision) (hh : st.regs 4 = heap)
    (hmw : m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ m * V) (hcover : Num.IPM.alphaExponent m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale m V + 1 < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (limbs + 1) < 2 ^ w) :
    ∃ out cost, Runs w p ω (initMinRatioAlpha alpha) st .normal out cost ∧
      out.regs 5 = heap + (limbs + 1) ∧
      (∀ r ≠ 5, out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (out.regs 5) ∧
      out.mem heap = Num.IPM.alphaExponent m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime m V / 8 ∧
      cost ≤ 20000 * (m.size + V.size + 1) + 8 := by
  have hthree : 3 < 2 ^ w := by omega
  have hsub : precision - 3 < 2 ^ w := by omega
  have hargs : evalArgs w st [.reg 0, .reg 1, .reg 2, .bin .sub (.reg 3) (.const 3), .reg 4] =
      some [m, V, limbs, precision - 3, heap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hm, hV, hL, hP, hh, hthree, hsub]
  have hwords : ∀ v ∈ [m, V, limbs, precision - 3, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
  have hpre : (Num.IPM.alphaContract w h).pre [m, V, limbs, precision - 3, heap] st.mem :=
    ⟨⟨m, V, limbs, precision - 3, heap, rfl, hsize, by omega, by omega, hscale⟩, hz, hroom⟩
  obtain ⟨out, c, v, hrun, hp, hv, hregs, hc⟩ :=
    runs_call_of_meetsContract (r := 5) himpl hargs hwords hpre ω
  obtain ⟨hv', _, _, hframe, hfree, hheader, hvalid, hval⟩ := hp
  change v = heap + (limbs + 1) at hv'
  change Num.fixVal out.mem (heap + 1) h limbs (precision - 3) = Num.IPM.alphaPrime m V at hval
  have halpha : Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime m V / 8 := by
    rw [← hval]
    unfold Num.fixVal
    conv_lhs => rw [show precision = (precision - 3) + 3 by omega, pow_add]
    norm_num
    ring
  refine ⟨out, c, hrun, hv.trans hv', hregs, hframe, hv.symm ▸ hfree, hheader, hvalid, halpha, ?_⟩
  change c ≤ 7 + 20000 * (m.size + V.size + 1) + 1 at hc
  calc
    c ≤ 7 + 20000 * (m.size + V.size + 1) + 1 := hc
    _ = 20000 * (m.size + V.size + 1) + (7 + 1) := by ac_rfl

/-- Read the augmented graph and penalty arguments, then allocate
the exact barrier block before building the chain. -/
@[expose] def prepareMinRatioInitAlphaAt (alpha edgeOffset : ℕ) : Stmt :=
  prepareMinRatioInitAt edgeOffset ;; initMinRatioAlpha alpha

/-- The runtime penalty and graph edge count determine the stored
barrier block. The graph and number-table pointers survive the call. -/
theorem prepareMinRatioInitAlphaAt_runs
    {w h alpha graph gradient lengths limbs precision V heap edgeOffset : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    (himpl : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hEdge : mem (graph + edgeOffset) = G.m)
    (hgraph : graph + edgeOffset < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioInitAlphaAt alpha edgeOffset)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧
      out.regs 3 = precision ∧ out.regs 4 = heap ∧ out.regs 5 = heap + (limbs + 1) ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 5) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20000 * (G.m.size + V.size + 1) + 35 := by
  obtain ⟨ready, hr, hm, hV, hL, hP, hh, hg, hgrad, hlen, hmem, _⟩ :=
    prepareMinRatioInitAt_runs (ω := ω) (gradient := gradient) (lengths := lengths)
      (limbs := limbs) (precision := precision) (V := V) (heap := heap) (pos := pos) hEdge hgraph
  obtain ⟨out, c, ha, hheap, hregs, hframe, hfree, he, hv, hval, hc⟩ :=
    initMinRatioAlpha_runs (ω := ω) himpl hm hV hL hP hh hmw hVw hLw hPw
      hsize hcover hwidth hscale (hmem.symm ▸ hz) hroom
  refine ⟨out, c + 27, runs_seq_iff.mpr (Or.inr ⟨ready, 26, c, hr, ha, by omega⟩),
    (hregs 0 (by decide)).trans hm, (hregs 1 (by decide)).trans hV,
    (hregs 2 (by decide)).trans hL, (hregs 3 (by decide)).trans hP,
    (hregs 4 (by decide)).trans hh,
    hheap, (hregs 69 (by decide)).trans hg, (hregs 70 (by decide)).trans hgrad,
    (hregs 71 (by decide)).trans hlen,
    fun a ha => (hframe a ha).trans (congrFun hmem a), hfree, he, hv, hval, ?_⟩
  exact (Nat.add_le_add_right hc 27).trans (by rw [Nat.add_assoc])

/-- Use the dynamic graph header for the numeric Init prefix. -/
@[expose] def prepareMinRatioInitAlpha (alpha : ℕ) : Stmt :=
  prepareMinRatioInitAlphaAt alpha 3

/-- The dynamic graph layout supplies the numeric prefix's edge count. -/
theorem prepareMinRatioInitAlpha_runs
    {w h alpha graph gradient lengths limbs precision V heap vc ec : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    (himpl : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hG : DynSpanner.Program.DynGraphAt mem graph vc ec G)
    (hgraph : graph + 3 < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioInitAlpha alpha)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧
      out.regs 3 = precision ∧ out.regs 4 = heap ∧ out.regs 5 = heap + (limbs + 1) ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 5) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20000 * (G.m.size + V.size + 1) + 35 :=
  prepareMinRatioInitAlphaAt_runs himpl hG.2.2.2.2.2.2.1 hgraph hmw hVw hLw hPw hsize hcover hwidth hscale hz hroom

/-- Obtain the hidden stability bound from the IPM parameter record
pointed to by register 5. The bound is a natural number stored in register 6. -/
@[expose] def initMinRatioHiddenPsi : Stmt :=
  .assign 6 (.bin .add
    (.bin .add (.load (.reg 5)) (.load (.bin .add (.reg 5) (.const 2))))
    (.const 6))

/-- The selected range words give the model's hidden stability bound
of Definition 4.4 (page 14), without changing the parameter record. -/
theorem initMinRatioHiddenPsi_runs {w m V record : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : st.regs 5 = record)
    (hat : ListAt st.mem record (IPM.Machine.precisionWords m V))
    (hroom : record + 2 < 2 ^ w)
    (hpsi : IPM.Machine.ipmRangeExponent m V + IPM.Machine.slackRangeExponent m V + 6 < 2 ^ w) :
    ∃ out, Runs w p ω initMinRatioHiddenPsi st .normal out 10 ∧
      (out.regs 6 : ℝ) = IPM.Machine.precisionHiddenPsi m V ∧
      (∀ r ≠ 6, out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let bound := IPM.Machine.ipmRangeExponent m V + IPM.Machine.slackRangeExponent m V + 6
  let out := { st with regs := Function.update st.regs 6 bound }
  have hs : st.mem record = IPM.Machine.slackRangeExponent m V := by
    simpa [IPM.Machine.precisionWords] using hat 0 (by simp [IPM.Machine.precisionWords])
  have hn : st.mem (record + 2) = IPM.Machine.ipmRangeExponent m V := by
    simpa [IPM.Machine.precisionWords] using hat 2 (by simp [IPM.Machine.precisionWords])
  refine ⟨out, runs_assign_iff.mpr ⟨bound, ?_, rfl, rfl, rfl⟩,
    by simp [out, bound, IPM.Machine.precisionHiddenPsi],
    fun r h => by simp [out, Function.update_of_ne h], rfl, rfl⟩
  have hsum : IPM.Machine.ipmRangeExponent m V + IPM.Machine.slackRangeExponent m V < 2 ^ w := by
    omega
  simp [Expr.eval, BinOp.eval, hr, hs, hn, hroom, hsum, hpsi,
    show 2 < 2 ^ w by omega, show 6 < 2 ^ w by omega, bound, Nat.add_comm
      (IPM.Machine.slackRangeExponent m V) (IPM.Machine.ipmRangeExponent m V)]

/-- Allocate the runtime range record and read its hidden stability
bound. The incoming heap is in register 5 and the returned heap in 7. -/
@[expose] def selectMinRatioHiddenPsi (select : ℕ) : Stmt :=
  .call 7 select [.reg 0, .reg 1, .reg 5] ;; initMinRatioHiddenPsi

/-- The runtime range selection supplies the two words used to compute
the exact hidden stability parameter. -/
theorem selectMinRatioHiddenPsi_runs {w select m V heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hm : st.regs 0 = m) (hV : st.regs 1 = V) (hh : st.regs 5 = heap)
    (hmw : m < 2 ^ w) (hVw : V < 2 ^ w) (hsize : 2 ≤ m * V)
    (hw : IPM.Machine.ipmParameterWordBits m V ≤ w)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 6 < 2 ^ w)
    (hpsi : IPM.Machine.ipmRangeExponent m V + IPM.Machine.slackRangeExponent m V + 6 < 2 ^ w) :
    ∃ out cost, Runs w p ω (selectMinRatioHiddenPsi select) st .normal out cost ∧
      (out.regs 6 : ℝ) = IPM.Machine.precisionHiddenPsi m V ∧ out.regs 7 = heap + 6 ∧
      (∀ r, r ≠ 6 → r ≠ 7 → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + 6) ∧
      cost ≤ 28 * (m.size + V.size) + 615 ∧
      ListAt out.mem heap (IPM.Machine.precisionWords m V) := by
  have hargs : evalArgs w st [.reg 0, .reg 1, .reg 5] = some [m, V, heap] := by
    simp [evalArgs, Expr.eval, hm, hV, hh]
  have hwords : ∀ v ∈ [m, V, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  have hpre : (IPM.Machine.precisionSelectionContract w).pre [m, V, heap] st.mem :=
    ⟨⟨m, V, heap, rfl, hsize, hw⟩, hz, hroom⟩
  obtain ⟨mid, c, v, hrun, hp, hv, hregs, hc⟩ :=
    runs_call_of_meetsContract (r := 7) himpl hargs hwords hpre ω
  obtain ⟨⟨_, _, hframe, hfree, hrecord⟩, hend⟩ := hp
  change v = heap + 6 at hend
  obtain ⟨out, hr, hΨ, hout, hmem, _⟩ :=
    initMinRatioHiddenPsi_runs (ω := ω) ((hregs 5 (by decide)).trans hh) hrecord (by omega) hpsi
  refine ⟨out, c + 11, runs_seq_iff.mpr (Or.inr ⟨mid, c, 10, hrun, hr, by omega⟩), hΨ,
    (hout 7 (by decide)).trans (hv.trans hend),
    fun r h6 h7 => (hout r h6).trans (hregs r h7), ?_, ?_, ?_, hmem.symm ▸ hrecord⟩
  · rw [hmem]
    exact hframe
  · rw [hmem, ← hend]
    exact hfree
  · change c ≤ 3 + (28 * (m.size + V.size) + 600) + 1 at hc
    omega

/-- Compute the barrier and hidden stability parameters from the
seven-word Init entry. Both use the supplied penalty and graph size. -/
@[expose] def prepareMinRatioStabilityAt (alpha select edgeOffset : ℕ) : Stmt :=
  prepareMinRatioInitAlphaAt alpha edgeOffset ;; selectMinRatioHiddenPsi select

/-- Range selection leaves the exact barrier block and caller memory
intact and returns both parameters in the chain Init format. -/
theorem prepareMinRatioStabilityAt_runs
    {w h alpha select graph gradient lengths limbs precision V heap edgeOffset : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    (halpha : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hselect : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hEdge : mem (graph + edgeOffset) = G.m)
    (hgraph : graph + edgeOffset < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hw : IPM.Machine.ipmParameterWordBits G.m V ≤ w)
    (hpsi : IPM.Machine.ipmRangeExponent G.m V + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) + 6 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioStabilityAt alpha select edgeOffset)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      out.regs 4 = heap ∧
      (out.regs 6 : ℝ) = IPM.Machine.precisionHiddenPsi G.m V ∧
      out.regs 7 = heap + (limbs + 1) + 6 ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20028 * (G.m.size + V.size) + 20651 ∧
      out.regs 5 = heap + (limbs + 1) ∧
      ListAt out.mem (heap + (limbs + 1)) (IPM.Machine.precisionWords G.m V) := by
  obtain ⟨mid, c, hr, hm, hV, hL, hP, hh, hheap, hg, hgrad, hlen, hframe, hfree, he, hv, hval, hc⟩ :=
    prepareMinRatioInitAlphaAt_runs (ω := ω) (gradient := gradient) (lengths := lengths)
      (pos := pos) halpha hEdge hgraph hmw hVw hLw hPw hsize hcover hwidth hscale hz (by omega)
  obtain ⟨out, c', hr', hΨ, hret, hregs, hframe', hfree', hc', hrecord⟩ :=
    selectMinRatioHiddenPsi_runs (ω := ω) hselect hm hV hheap hmw hVw hsize hw
      (hheap ▸ hfree) hroom hpsi
  have hblock : heap + 1 + limbs ≤ heap + (limbs + 1) := by omega
  refine ⟨out, c + c' + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, c', hr, hr', rfl⟩),
    (hregs 0 (by decide) (by decide)).trans hm, (hregs 1 (by decide) (by decide)).trans hV,
    (hregs 2 (by decide) (by decide)).trans hL, (hregs 3 (by decide) (by decide)).trans hP,
    (hregs 4 (by decide) (by decide)).trans hh,
    hΨ, hret, (hregs 69 (by decide) (by decide)).trans hg,
    (hregs 70 (by decide) (by decide)).trans hgrad, (hregs 71 (by decide) (by decide)).trans hlen,
    (fun a ha => (hframe' a (by omega)).trans (hframe a ha)), hret.symm ▸ hfree',
    (hframe' heap (by omega)).trans he, Num.IPM.valid_frozen hframe' hblock hv,
    (Num.IPM.fixVal_frozen hframe' hblock).trans hval, ?_, (hregs 5 (by decide) (by decide)).trans hheap, hrecord⟩
  omega

/-- Use the dynamic graph header for the numeric Init prefix. -/
@[expose] def prepareMinRatioStability (alpha select : ℕ) : Stmt :=
  prepareMinRatioStabilityAt alpha select 3

/-- The dynamic graph layout supplies the numeric prefix's edge count. -/
theorem prepareMinRatioStability_runs
    {w h alpha select graph gradient lengths limbs precision V heap vc ec : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    (halpha : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hselect : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hG : DynSpanner.Program.DynGraphAt mem graph vc ec G)
    (hgraph : graph + 3 < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hw : IPM.Machine.ipmParameterWordBits G.m V ≤ w)
    (hpsi : IPM.Machine.ipmRangeExponent G.m V + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) + 6 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioStability alpha select)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      out.regs 4 = heap ∧
      (out.regs 6 : ℝ) = IPM.Machine.precisionHiddenPsi G.m V ∧
      out.regs 7 = heap + (limbs + 1) + 6 ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20028 * (G.m.size + V.size) + 20651 :=
  by
    obtain ⟨out, cost, hr, hm, hV, hL, hP, hh, hΨ, hret, hg, hgrad, hlen, hf, hz', ha,
      hv, hval, hc, _, _⟩ :=
      prepareMinRatioStabilityAt_runs halpha hselect hG.2.2.2.2.2.2.1 hgraph hmw hVw hLw hPw hsize hcover hwidth hscale hw hpsi hz hroom
    exact ⟨out, cost, hr, hm, hV, hL, hP, hh, hΨ, hret, hg, hgrad, hlen, hf, hz', ha, hv, hval, hc⟩

/-- The branching factor is the least integer whose depth-th power
covers the initial edge count. This is the integer test used at Init. -/
theorem minRatioBranchCount_le_iff {depth m candidate : ℕ}
    (hd : 0 < depth) (hm : 1 ≤ m) :
    (Chain.mkChainParams depth m hd hm).k ≤ candidate ↔ m ≤ candidate ^ depth := by
  change ⌈((m : ℝ) ^ (1 / (depth : ℝ)))⌉₊ ≤ candidate ↔ m ≤ candidate ^ depth
  rw [Nat.ceil_le]
  have hd' : (0 : ℝ) < depth := Nat.cast_pos.mpr hd
  have hpow := Real.rpow_le_rpow_iff
    (Real.rpow_nonneg (Nat.cast_nonneg m) (1 / (depth : ℝ))) (Nat.cast_nonneg candidate) hd'
  rw [← Real.rpow_mul (Nat.cast_nonneg m), one_div_mul_cancel (ne_of_gt hd'),
    Real.rpow_one, Real.rpow_natCast] at hpow
  exact hpow.symm.trans (by exact_mod_cast
    (show (m : ℝ) ≤ (candidate : ℝ) ^ depth ↔ m ≤ candidate ^ depth from by norm_cast))

/-- The depth choice for exponent `23/24` requires comparing the
logarithm of the edge count plus two with an integer 48th power. -/
theorem minRatioDepth_le_iff (m candidate : ℕ) :
    Chain.chosenD (23 / 24) m ≤ candidate ↔
      Real.log ((m : ℝ) + 2) ≤ (candidate : ℝ) ^ (48 : ℕ) := by
  unfold Chain.chosenD
  rw [Nat.ceil_le, show (1 - (23 : ℝ) / 24) / 2 = 1 / 48 by norm_num]
  have hlog : 0 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) m])
  have hp := Real.rpow_le_rpow_iff (Real.rpow_nonneg hlog (1 / 48))
    (Nat.cast_nonneg (α := ℝ) candidate) (by norm_num : (0 : ℝ) < 48)
  rw [← Real.rpow_mul hlog, show (1 : ℝ) / 48 * 48 = 1 by norm_num, Real.rpow_one,
    ← show ((48 : ℕ) : ℝ) = 48 by norm_num, Real.rpow_natCast] at hp
  exact hp.symm

/-- The chain depth test can compare the input against an exponential
without first rounding the logarithm of the input. -/
theorem minRatioDepth_le_iff_exp (m candidate : ℕ) :
    Chain.chosenD (23 / 24) m ≤ candidate ↔
      (m : ℝ) + 2 ≤ Real.exp ((candidate : ℝ) ^ (48 : ℕ)) := by
  rw [minRatioDepth_le_iff, Real.log_le_iff_le_exp]
  positivity

/-- A candidate whose 48th power reaches the word-bit bound already
passes the exact depth test, regardless of the input within the word. -/
theorem minRatioDepth_le_of_word {m w candidate : ℕ}
    (hm : m < 2 ^ w) (hc : w + 1 ≤ candidate ^ 48) :
    Chain.chosenD (23 / 24) m ≤ candidate := by
  apply (minRatioDepth_le_iff m candidate).2
  have htwo : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have hadd : m + 2 ≤ 2 ^ (w + 1) := by
    rw [pow_succ]
    omega
  have hlog : Real.log ((m : ℝ) + 2) ≤ Real.log ((2 : ℝ) ^ (w + 1)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hadd
  rw [Real.log_pow] at hlog
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hbound : Real.log ((m : ℝ) + 2) ≤ (w : ℝ) + 1 := by
    exact hlog.trans (by push_cast; nlinarith only [hlogTwo, Nat.cast_nonneg (α := ℝ) w])
  exact hbound.trans (by exact_mod_cast hc)

/-- The binary length of the input gives a search limit for the exact
depth without depending on the machine's word width. -/
theorem minRatioDepth_le_size (m : ℕ) :
    Chain.chosenD (23 / 24) m ≤ m.size + 1 := by
  apply minRatioDepth_le_of_word (w := m.size) (Nat.lt_size_self m)
  exact Nat.le_self_pow (by decide : 48 ≠ 0) _

/-- A lower and an upper enclosure for the logarithm certify the
depth when the neighboring integer powers separate the enclosure. -/
theorem minRatioDepth_eq_of_logBounds (m candidate : ℕ) (lo hi : ℝ)
    (hc : 0 < candidate)
    (hlo : lo ≤ Real.log ((m : ℝ) + 2)) (hhi : Real.log ((m : ℝ) + 2) ≤ hi)
    (hprev : ((candidate - 1 : ℕ) : ℝ) ^ (48 : ℕ) < lo)
    (hnext : hi ≤ (candidate : ℝ) ^ (48 : ℕ)) :
    Chain.chosenD (23 / 24) m = candidate := by
  have hu := (minRatioDepth_le_iff m candidate).2 (hhi.trans hnext)
  have hl : ¬ Chain.chosenD (23 / 24) m ≤ candidate - 1 := by
    intro h
    exact (hprev.trans_le hlo).not_ge ((minRatioDepth_le_iff m (candidate - 1)).1 h)
  omega

/-- The machine can certify a depth with two natural-number comparisons
against the scaled powers of adjacent candidates. -/
theorem minRatioDepth_eq_of_scaledLogBounds (m candidate lo hi scale : ℕ)
    (hc : 0 < candidate) (hs : 0 < scale)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale)
    (hprev : (candidate - 1) ^ 48 * scale < lo)
    (hnext : hi ≤ candidate ^ 48 * scale) :
    Chain.chosenD (23 / 24) m = candidate := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  apply minRatioDepth_eq_of_logBounds m candidate _ _ hc hlo hhi
  · apply (lt_div_iff₀ hs').2
    exact_mod_cast hprev
  · apply (div_le_iff₀ hs').2
    exact_mod_cast hnext

/-- Test the two scaled comparisons for a candidate depth. Registers
105 and 106 hold the adjacent scaled powers, and 107 and 108 the log bounds. -/
@[expose] def checkInitDepthBounds : Stmt :=
  .assign 109 (.bin .mul (.bin .lt (.reg 105) (.reg 107))
    (.bin .sub (.const 1) (.bin .lt (.reg 106) (.reg 108))))

/-- The depth certificate flag is one exactly when both bounds pass. -/
theorem checkInitDepthBounds_runs {w prev next lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : st.regs 105 = prev) (hn : st.regs 106 = next)
    (hl : st.regs 107 = lo) (hh : st.regs 108 = hi) (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω checkInitDepthBounds st .normal out 10 ∧
      out.regs 109 = (if prev < lo ∧ hi ≤ next then 1 else 0) ∧
      out.mem = st.mem ∧ (∀ r ≠ 109, out.regs r = st.regs r) := by
  let flag := if prev < lo ∧ hi ≤ next then 1 else 0
  let out := {st with regs := Function.update st.regs 109 flag}
  refine ⟨out, runs_assign_iff.mpr ⟨flag, ?_, rfl, rfl, rfl⟩,
    by simp [out, flag], rfl, fun r hr => by simp [out, hr]⟩
  have hz : 0 < 2 ^ w := by omega
  by_cases h₁ : prev < lo <;> by_cases h₂ : next < hi <;>
    simp [Expr.eval, BinOp.eval, hp, hn, hl, hh, hw, hz, flag, h₁, h₂, Nat.not_le.mpr, Nat.le_of_not_gt]

/-- A successful machine comparison certifies the model depth. -/
theorem checkInitDepthBounds_certifies {w m candidate lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : st.regs 105 = (candidate - 1) ^ 48 * scale)
    (hn : st.regs 106 = candidate ^ 48 * scale)
    (hl : st.regs 107 = lo) (hh : st.regs 108 = hi) (hw : 1 < 2 ^ w)
    (hc : 0 < candidate) (hs : 0 < scale)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale) :
    ∃ out, Runs w p ω checkInitDepthBounds st .normal out 10 ∧
      (out.regs 109 = 1 → Chain.chosenD (23 / 24) m = candidate) ∧
      out.mem = st.mem ∧ (∀ r ≠ 109, out.regs r = st.regs r) := by
  obtain ⟨out, hr, hflag, hm, hkeep⟩ := checkInitDepthBounds_runs (ω := ω) hp hn hl hh hw
  refine ⟨out, hr, ?_, hm, hkeep⟩
  intro hcert
  split at hflag
  · rename_i hpass
    exact minRatioDepth_eq_of_scaledLogBounds m candidate lo hi scale hc hs hlo hhi hpass.1 hpass.2
  · omega

/-- Install the candidate from register 110 when its bounds certify it. -/
@[expose] def installCertifiedInitDepth (retry : Stmt) : Stmt :=
  .cond (.reg 109) (.assign 75 (.reg 110)) retry

/-- The certified branch puts the exact model depth in the header register. -/
theorem installCertifiedInitDepth_runs {w m candidate : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hflag : st.regs 109 = 1) (hc : st.regs 110 = candidate)
    (hexact : Chain.chosenD (23 / 24) m = candidate) :
    ∃ out, Runs w p ω (installCertifiedInitDepth retry) st .normal out 4 ∧
      out.regs 75 = Chain.chosenD (23 / 24) m ∧ out.mem = st.mem ∧
      (∀ r ≠ 75, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 75 candidate}
  have ha : Runs w p ω (.assign 75 (.reg 110)) st .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hc], rfl, rfl, rfl⟩
  exact ⟨out, runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, hflag], ha, rfl⟩,
    by simp [out, hexact], rfl, fun r hr => by simp [out, hr]⟩

/-- For positive inputs whose word size is below the second depth
cutoff, the exact depth is two. The bound on word size is explicit. -/
theorem minRatioDepth_eq_two_of_word {m w : ℕ}
    (hm : 0 < m) (hmw : m < 2 ^ w) (hw : w + 1 ≤ 2 ^ 48) :
    Chain.chosenD (23 / 24) m = 2 := by
  have hmAdd : m + 2 ≤ 2 ^ (w + 1) := by
    rw [pow_succ]
    have hp := Nat.two_pow_pos w
    omega
  have hupper : Real.log ((m : ℝ) + 2) ≤ (2 : ℝ) ^ (48 : ℕ) := by
    have hcast : (m : ℝ) + 2 ≤ (2 : ℝ) ^ (w + 1) := by exact_mod_cast hmAdd
    have hlog := Real.log_le_log (by positivity : 0 < (m : ℝ) + 2) hcast
    rw [Real.log_pow] at hlog
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hs : ((w + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (48 : ℕ) := by exact_mod_cast hw
    exact hlog.trans ((mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)).trans (by simpa using hs))
  have hlower : 1 < Real.log ((m : ℝ) + 2) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    exact Real.exp_one_lt_three.trans_le (by
      have hc : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hm)
      linarith only [hc])
  apply Nat.le_antisymm ((minRatioDepth_le_iff m 2).mpr hupper)
  by_contra! h
  have hle := (minRatioDepth_le_iff m 1).mp (show Chain.chosenD (23 / 24) m ≤ 1 by omega)
  exact (not_le_of_gt hlower) (by simpa using hle)

/-- Multiply the accumulator in register 4 by the positive candidate
in register 0, capping at register 2 before doing the multiplication. -/
@[expose] def multiplyBranchPowerCapped : Stmt :=
  .cond (.bin .lt (.bin .div (.reg 2) (.reg 0)) (.reg 4))
    (.assign 4 (.reg 2)) (.assign 4 (.bin .mul (.reg 4) (.reg 0)))

/-- The capped product takes at most ten steps and never evaluates an
out-of-range multiplication. -/
theorem multiplyBranchPowerCapped_runs {w candidate cap value : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbase : st.regs 0 = candidate) (hcap : st.regs 2 = cap) (hval : st.regs 4 = value)
    (hpos : 0 < candidate) (hw : 1 < 2 ^ w) (hcapWord : cap < 2 ^ w) :
    ∃ cost, Runs w p ω multiplyBranchPowerCapped st .normal
      { st with regs := Function.update st.regs 4 (min cap (value * candidate)) } cost ∧ cost ≤ 10 := by
  have hd : cap / candidate < 2 ^ w := (Nat.div_le_self _ _).trans_lt hcapWord
  by_cases hlt : cap / candidate < value
  · have hp : cap < value * candidate := by
      by_contra! h
      exact (Nat.not_le_of_gt hlt) ((Nat.le_div_iff_mul_le hpos).mpr h)
    rw [min_eq_left hp.le]
    have ha : Runs w p ω (.assign 4 (.reg 2)) st .normal
        { st with regs := Function.update st.regs 4 cap } 2 :=
      runs_assign_iff.mpr ⟨cap, by simp [Expr.eval, hcap], rfl, rfl, rfl⟩
    refine ⟨8, runs_cond_iff.mpr ⟨1, 2, ?_, ha, rfl⟩, by decide⟩
    simp [Expr.eval, BinOp.eval, hbase, hcap, hval, show w ≠ 0 by (intro he; simp [he] at hw), hd, hlt]
  · have hp : value * candidate ≤ cap := (Nat.le_div_iff_mul_le hpos).mp (Nat.le_of_not_gt hlt)
    have hmul := hp.trans_lt hcapWord
    rw [min_eq_right hp]
    have ha : Runs w p ω (.assign 4 (.bin .mul (.reg 4) (.reg 0))) st .normal
        { st with regs := Function.update st.regs 4 (value * candidate) } 4 :=
      runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hval, hbase, hmul], rfl, rfl, rfl⟩
    refine ⟨10, runs_cond_iff.mpr ⟨0, 4, ?_, ha, rfl⟩, by decide⟩
    simp [Expr.eval, BinOp.eval, hbase, hcap, hval, hd, hlt]

/-- Compute the capped depth-th power with the candidate, depth, and cap
in registers 0 through 2. The product is returned in register 4. -/
@[expose] def branchPowerCapped : Stmt :=
  .assign 4 (.const 1) ;; forRange 3 (.const 0) (.reg 1) multiplyBranchPowerCapped

/-- The branching-factor test computes the capped power in linear time
in the chain depth and leaves memory unchanged. -/
theorem branchPowerCapped_runs {w candidate depth cap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hc : st.regs 0 = candidate) (hd : st.regs 1 = depth) (hm : st.regs 2 = cap)
    (hpos : 0 < candidate) (hcap : 0 < cap) (hw : 1 < 2 ^ w)
    (hdw : depth < 2 ^ w) (hmw : cap < 2 ^ w) :
    ∃ out c, Runs w p ω branchPowerCapped st .normal out c ∧
      out.regs 4 = min cap (candidate ^ depth) ∧ out.mem = st.mem ∧ out.pos = st.pos ∧
      out.regs 0 = candidate ∧ out.regs 1 = depth ∧ out.regs 2 = cap ∧
      c ≤ 19 * depth + 10 := by
  let Inv (i : ℕ) (s : State) :=
    s.regs 3 = i ∧ s.regs 4 = min cap (candidate ^ i) ∧
    s.regs 0 = candidate ∧ s.regs 1 = depth ∧ s.regs 2 = cap ∧
    s.mem = st.mem ∧ s.pos = st.pos
  let start := { st with regs := Function.update st.regs 4 1 }
  have hstart : Runs w p ω (.assign 4 (.const 1)) st .normal start 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = start) (r := 3)
    (lo := .const 0) (hi := .reg 1) (body := multiplyBranchPowerCapped) (Inv := Inv)
    10 0 depth (Nat.zero_le _) hw (fun _ => hdw)
    (by
      intro s hs
      subst s
      simp [Expr.eval, Inv, start, hc, hd, hm, Function.update_of_ne, Nat.succ_le_of_lt hcap])
    (fun _ _ _ _ h => h.1) (by intro _ _ _ _ h; simp [Expr.eval, h.2.2.2.1])
    (by
      intro i _ _ s tape hs
      obtain ⟨hi, hpow, hc', hd', hm', hmem, hpos'⟩ := hs
      obtain ⟨c, hr, hcost⟩ := multiplyBranchPowerCapped_runs (ω := tape) hc' hm' hpow
        hpos hw hmw
      have hmul : min cap (min cap (candidate ^ i) * candidate) = min cap (candidate ^ (i + 1)) := by
        rw [pow_succ]
        by_cases h : candidate ^ i ≤ cap
        · rw [min_eq_right h]
        · have h₁ : cap ≤ cap * candidate := by
            simpa using Nat.mul_le_mul_left cap hpos
          have h₂ : cap ≤ candidate ^ i * candidate :=
            h₁.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_of_not_ge h)))
          rw [min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h)), min_eq_left h₁, min_eq_left h₂]
      refine ⟨.normal, _, c, hr, ⟨?_, ?_⟩, hcost⟩
      · simp [Inv, Function.update_of_ne, hmul, hc', hd', hm', hmem, hpos']
      · simpa [Function.update_of_ne] using hi)
  obtain ⟨o, out, cost, hr, hout, hcost⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    obtain ⟨_, hpow, hc', hd', hm', hmem, hp⟩ := hout
    have hcost' : cost ≤ depth * 19 + 7 := by simpa using hcost
    refine ⟨out, cost + 3, ?_, hpow, hmem, hp, hc', hd', hm', ?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨start, 2, cost, hstart, hr, by omega⟩)
    · omega

/-- Testing the capped result against the edge count decides whether
a candidate covers the exact model branching factor. -/
theorem branchPowerCapped_decides_branchCount {w candidate depth m : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hc : st.regs 0 = candidate) (hd : st.regs 1 = depth) (hm : st.regs 2 = m)
    (hpos : 0 < candidate) (hmpos : 1 ≤ m) (hdpos : 0 < depth) (hw : 1 < 2 ^ w)
    (hdw : depth < 2 ^ w) (hmw : m < 2 ^ w) :
    ∃ out c, Runs w p ω branchPowerCapped st .normal out c ∧
      (out.regs 4 = m ↔ (Chain.mkChainParams depth m hdpos hmpos).k ≤ candidate) ∧
      c ≤ 19 * depth + 10 := by
  obtain ⟨out, c, hr, hp, _, _, _, _, _, hcost⟩ :=
    branchPowerCapped_runs hc hd hm hpos (Nat.zero_lt_of_lt hmpos) hw hdw hmw
  refine ⟨out, c, hr, ?_, hcost⟩
  rw [hp, minRatioBranchCount_le_iff]
  exact ⟨fun h => h ▸ min_le_right _ _, min_eq_left⟩

@[expose] def branchMidpoint : Expr :=
  .bin .add (.reg 6) (.bin .div (.bin .sub (.reg 7) (.reg 6)) (.const 2))

/-- Bisect the interval in registers 6 and 7 and test its midpoint.
The depth and edge count remain in registers 1 and 2. -/
@[expose] def branchSearchStep : Stmt :=
  .assign 0 branchMidpoint ;; branchPowerCapped ;;
    .cond (.bin .eq (.reg 4) (.reg 2)) (.assign 7 (.reg 0))
      (.assign 6 (.bin .add (.reg 0) (.const 1)))

/-- One branching-factor bisection retains the exact model answer
and reduces the interval width by at least a factor of two. -/
theorem branchSearchStep_runs {w lo hi depth m : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hl : st.regs 6 = lo) (hh : st.regs 7 = hi)
    (hd : st.regs 1 = depth) (hm : st.regs 2 = m)
    (hlo : 0 < lo) (horder : lo < hi) (hhi : hi < 2 ^ w)
    (hdpos : 0 < depth) (hmpos : 1 ≤ m) (hw : 2 < 2 ^ w)
    (hdw : depth < 2 ^ w) (hmw : m < 2 ^ w)
    (hlk : lo ≤ (Chain.mkChainParams depth m hdpos hmpos).k)
    (hkh : (Chain.mkChainParams depth m hdpos hmpos).k ≤ hi) :
    ∃ out c, Runs w p ω branchSearchStep st .normal out c ∧
      lo ≤ out.regs 6 ∧ out.regs 7 ≤ hi ∧
      out.regs 6 ≤ (Chain.mkChainParams depth m hdpos hmpos).k ∧
      (Chain.mkChainParams depth m hdpos hmpos).k ≤ out.regs 7 ∧
      out.regs 7 - out.regs 6 ≤ (hi - lo) / 2 ∧
      out.regs 1 = depth ∧ out.regs 2 = m ∧ out.mem = st.mem ∧ out.pos = st.pos ∧
      c ≤ 19 * depth + 28 := by
  let mid := lo + (hi - lo) / 2
  have hmidLt : mid < hi := by dsimp [mid]; omega
  have hmidPos : 0 < mid := by dsimp [mid]; omega
  let ready := { st with regs := Function.update st.regs 0 mid }
  have hr0 : Runs w p ω (.assign 0 branchMidpoint) st .normal ready 8 :=
    runs_assign_iff.mpr ⟨mid, by
      simp [branchMidpoint, Expr.eval, BinOp.eval, hl, hh, hw, mid,
        show hi - lo < 2 ^ w by omega, show (hi - lo) / 2 < 2 ^ w by omega,
        show lo + (hi - lo) / 2 < 2 ^ w from hmidLt.trans hhi], rfl, rfl, rfl⟩
  have hd' : ready.regs 1 = depth := by simpa [ready] using hd
  have hm' : ready.regs 2 = m := by simpa [ready] using hm
  obtain ⟨tested, cost, hr, hpow, hmem, hpos', hmidReg, hdepth, hcap, hcost⟩ :=
    branchPowerCapped_runs (ω := ω) (st := ready) (by simp [ready]) hd' hm'
      hmidPos (Nat.zero_lt_of_lt hmpos) (by omega) hdw hmw
  have hkeep (r : ℕ) (hr5 : 5 ≤ r) : tested.regs r = ready.regs r :=
    runs_preserves_above hr5 (by rfl : writesBelow 5 branchPowerCapped = true) hr
  have hlow := (hkeep 6 (by decide)).trans (show ready.regs 6 = lo by simpa [ready] using hl)
  have hhigh := (hkeep 7 (by decide)).trans (show ready.regs 7 = hi by simpa [ready] using hh)
  have htest : tested.regs 4 = m ↔ (Chain.mkChainParams depth m hdpos hmpos).k ≤ mid := by
    rw [hpow, minRatioBranchCount_le_iff]
    exact ⟨fun h => h ▸ min_le_right _ _, min_eq_left⟩
  by_cases pass : tested.regs 4 = m
  · let out := { tested with regs := Function.update tested.regs 7 mid }
    have ha : Runs w p ω (.assign 7 (.reg 0)) tested .normal out 2 :=
      runs_assign_iff.mpr ⟨mid, by simp [Expr.eval, hmidReg], rfl, rfl, rfl⟩
    have hcond := (runs_cond_iff (w := w) (p := p) (ω := ω)
      (e := .bin .eq (.reg 4) (.reg 2)) (s := .assign 7 (.reg 0))
      (t := .assign 6 (.bin .add (.reg 0) (.const 1)))).mpr ⟨1, 2, by
        simp [Expr.eval, BinOp.eval, pass, hcap, show w ≠ 0 by (intro he; simp [he] at hw)], ha, rfl⟩
    refine ⟨out, cost + 16, ?_, ?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨ready, 8, cost + 7, hr0,
        runs_seq_iff.mpr (Or.inr ⟨tested, cost, 6, hr, hcond, by omega⟩), by omega⟩)
    · have hk := htest.mp pass
      simp [out, Function.update_of_ne, hlow, hhigh, hdepth, hcap, hmem, hpos', ready, mid] at *
      omega
  · let out := { tested with regs := Function.update tested.regs 6 (mid + 1) }
    have ha : Runs w p ω (.assign 6 (.bin .add (.reg 0) (.const 1))) tested .normal out 4 :=
      runs_assign_iff.mpr ⟨mid + 1, by
        simp [Expr.eval, BinOp.eval, hmidReg, show 1 < 2 ^ w by omega,
          show mid + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hcond := (runs_cond_iff (w := w) (p := p) (ω := ω)
      (e := .bin .eq (.reg 4) (.reg 2)) (s := .assign 7 (.reg 0))
      (t := .assign 6 (.bin .add (.reg 0) (.const 1)))).mpr ⟨0, 4, by
        simp [Expr.eval, BinOp.eval, pass, hcap], ha, rfl⟩
    refine ⟨out, cost + 18, ?_, ?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨ready, 8, cost + 9, hr0,
        runs_seq_iff.mpr (Or.inr ⟨tested, cost, 8, hr, hcond, by omega⟩), by omega⟩)
    · have hk := Nat.lt_of_not_ge (fun h => pass (htest.mpr h))
      simp [out, Function.update_of_ne, hlow, hhigh, hdepth, hcap, hmem, hpos', ready, mid] at *
      omega

/-- Search the interval from one to the edge count for the least
candidate that passes the capped power test. -/
@[expose] def selectMinRatioBranchCount : Stmt :=
  .assign 6 (.const 1) ;; .assign 7 (.reg 2) ;;
    .loop (.bin .lt (.reg 6) (.reg 7)) branchSearchStep

/-- Given the runtime depth, Init selects the exact model branching
factor in logarithmically many capped power tests and no scratch memory. -/
theorem selectMinRatioBranchCount_runs {w depth m : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : st.regs 1 = depth) (hm : st.regs 2 = m)
    (hdpos : 0 < depth) (hmpos : 1 ≤ m) (hw : 2 < 2 ^ w)
    (hdw : depth < 2 ^ w) (hmw : m < 2 ^ w) :
    ∃ out c, Runs w p ω selectMinRatioBranchCount st .normal out c ∧
      out.regs 6 = (Chain.mkChainParams depth m hdpos hmpos).k ∧
      out.regs 1 = depth ∧ out.regs 2 = m ∧ out.mem = st.mem ∧ out.pos = st.pos ∧
      c ≤ (19 * depth + 32) * m.size + 10 := by
  let k := (Chain.mkChainParams depth m hdpos hmpos).k
  let Inv (s : State) := 1 ≤ s.regs 6 ∧ s.regs 6 ≤ k ∧ k ≤ s.regs 7 ∧ s.regs 7 ≤ m ∧
    s.regs 1 = depth ∧ s.regs 2 = m ∧ s.mem = st.mem ∧ s.pos = st.pos
  let measure (s : State) := (s.regs 7 - s.regs 6).size
  let cond (s : State) := if s.regs 6 < s.regs 7 then 1 else 0
  have hOne : 1 < 2 ^ w := by omega
  have hne : w ≠ 0 := by intro he; simp [he] at hw
  have hloop := Triple.loop_const_normal (w := w) (p := p) (Inv := Inv)
    (Q := fun s => s.regs 6 = k ∧ s.regs 1 = depth ∧ s.regs 2 = m ∧
      s.mem = st.mem ∧ s.pos = st.pos)
    (e := .bin .lt (.reg 6) (.reg 7)) (body := branchSearchStep)
    measure cond (19 * depth + 28)
    (by
      intro s _
      by_cases h : s.regs 6 < s.regs 7 <;> simp [cond, Expr.eval, BinOp.eval, h, hne])
    (by
      intro s hs hzero
      obtain ⟨_, hlo, hhi, _, h1, h2, hmem, hpos⟩ := hs
      have hn : ¬ s.regs 6 < s.regs 7 := by
        intro h
        simp [cond, h] at hzero
      exact ⟨by omega, h1, h2, hmem, hpos⟩)
    (by
      intro s hs hnonzero current tape heq
      subst current
      obtain ⟨hpos, hlo, hhi, hcap, h1, h2, hmem, hpos'⟩ := hs
      have hlt : s.regs 6 < s.regs 7 := by
        by_contra! hn
        exact hnonzero (by simp [cond, not_lt_of_ge hn])
      obtain ⟨out, c, hr, hlow, hhigh, hkl, hkh, hhalf, hd', hm', hmem', hpos'', hcost⟩ :=
        branchSearchStep_runs (ω := tape) rfl rfl h1 h2 hpos hlt (hcap.trans_lt hmw)
          hdpos hmpos hw hdw hmw hlo hhi
      refine ⟨.normal, out, c, hr,
        ⟨⟨hpos.trans hlow, hkl, hkh, hhigh.trans hcap, hd', hm', hmem'.trans hmem,
          hpos''.trans hpos'⟩, ?_⟩, hcost⟩
      let width := s.regs 7 - s.regs 6
      have hwpos : 0 < width := Nat.sub_pos_of_lt hlt
      have hsize : 0 < width.size := Nat.size_pos.mpr hwpos
      have hltpow := Nat.lt_size_self width
      rw [show width.size = (width.size - 1) + 1 by omega, pow_succ] at hltpow
      have hout : out.regs 7 - out.regs 6 < 2 ^ (width.size - 1) := by
        change _ ≤ width / 2 at hhalf
        omega
      have hsiz := Nat.size_le.mpr hout
      change (out.regs 7 - out.regs 6).size < width.size
      omega)
  let start := { st with regs := Function.update st.regs 6 1 }
  let ready := { start with regs := Function.update start.regs 7 m }
  have hr1 : Runs w p ω (.assign 6 (.const 1)) st .normal start 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hOne], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 7 (.reg 2)) start .normal ready 2 :=
    runs_assign_iff.mpr ⟨m, by simp [Expr.eval, start, hm], rfl, rfl, rfl⟩
  have hkm : k ≤ m := (minRatioBranchCount_le_iff hdpos hmpos).mpr
    (by simpa using Nat.pow_le_pow_right (by omega : 0 < m) hdpos)
  have hready : Inv ready := by
    simp [Inv, ready, start, hd, hm, hkm, show 1 ≤ k from (Chain.mkChainParams depth m hdpos hmpos).hk]
  obtain ⟨o, out, c, hr, hdone, hcost⟩ := hloop.runs ω hready
  cases o with
  | returned _ => exact False.elim hdone
  | normal =>
    obtain ⟨hk, h1, h2, hmem, hp⟩ := hdone
    have hcost' : c ≤ (19 * depth + 32) * (m - 1).size + 4 := by
      have he : 3 + (19 * depth + 28) + 1 = 19 * depth + 32 := by omega
      simpa [measure, ready, start, Expr.size, he] using hcost
    have hsz : (m - 1).size ≤ m.size := Nat.size_le_size (Nat.sub_le _ _)
    have hcost'' := Nat.mul_le_mul_left (19 * depth + 32) hsz
    refine ⟨out, c + 6, ?_, hk, h1, h2, hmem, hp, by omega⟩
    exact runs_seq_iff.mpr (Or.inr ⟨start, 2, c + 3, hr1,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hr2, hr, by omega⟩), by omega⟩)

/-- Select depth and branching for words below the second depth cutoff.
The input edge count is in register 2. -/
@[expose] def selectMinRatioSmallDepth : Stmt :=
  .assign 1 (.const 2) ;; selectMinRatioBranchCount

/-- The bounded-word Init fragment selects the model depth and branching
factor without a logarithm evaluation. -/
theorem selectMinRatioSmallDepth_runs {w m : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hm : st.regs 2 = m) (hmpos : 1 ≤ m) (hmw : m < 2 ^ w)
    (hw : 2 < 2 ^ w) (hwidth : w + 1 ≤ 2 ^ 48) :
    let depth := Chain.chosenD (23 / 24) m
    ∃ out c, Runs w p ω selectMinRatioSmallDepth st .normal out c ∧
      out.regs 1 = depth ∧
      (∀ hd : 0 < depth, out.regs 6 = (Chain.mkChainParams depth m hd hmpos).k) ∧
      out.regs 2 = m ∧ out.mem = st.mem ∧ out.pos = st.pos ∧ c ≤ 70 * m.size + 13 := by
  dsimp only
  have hdepth := minRatioDepth_eq_two_of_word (Nat.zero_lt_of_lt hmpos) hmw hwidth
  rw [hdepth]
  let ready := { st with regs := Function.update st.regs 1 2 }
  have hsetup : Runs w p ω (.assign 1 (.const 2)) st .normal ready 2 :=
    runs_assign_iff.mpr ⟨2, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  obtain ⟨out, c, hr, hbranch, hd, hm', hmem, hpos, hc⟩ :=
    selectMinRatioBranchCount_runs (ω := ω) (st := ready)
      (by simp [ready]) (by simpa [ready] using hm) (by decide : 0 < 2) hmpos hw hw hmw
  exact ⟨out, c + 3, runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hsetup, hr, by omega⟩),
    hd, fun _ => hbranch, hm', hmem, hpos, by omega⟩

/-- Obtain the dyadic quality exponent from the same fixed procedure
used by the solver. The augmented edge count is in register 0. -/
@[expose] def selectMinRatioQuality (entry : ℕ) : Stmt :=
  .call 72 entry [.reg 0]

/-- Quality selection makes no allocation and preserves the other
Init registers. -/
theorem selectMinRatioQuality_runs {w entry m : ℕ} {k charge : ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (IPM.Machine.solverQualityContract w k charge))
    (hm : st.regs 0 = m) (hmw : m < 2 ^ w) (hkw : k m < 2 ^ w) :
    ∃ out c, Runs w p ω (selectMinRatioQuality entry) st .normal out c ∧
      out.regs 72 = k m ∧ (∀ r ≠ 72, out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ charge m + 2 := by
  have hargs : evalArgs w st [.reg 0] = some [m] := by simp [evalArgs, Expr.eval, hm]
  have hwords : ∀ v ∈ [m], v < 2 ^ w := by simpa using hmw
  have hpre : (IPM.Machine.solverQualityContract w k charge).pre [m] st.mem := ⟨m, rfl, hkw⟩
  obtain ⟨out, c, v, hr, hp, hreg, hkeep, hc⟩ :=
    runs_call_of_meetsContract (r := 72) himpl hargs hwords hpre ω
  obtain ⟨hmem, hv⟩ := hp
  change v = k m at hv
  change c ≤ 1 + charge m + 1 at hc
  exact ⟨out, c, hr, hreg.trans hv, hkeep, hmem, by omega⟩

/-- Read the barrier exponent at the heap address in register 4 and
form the exponent of the Detect threshold using the quality exponent. -/
@[expose] def selectMinRatioEpsilonExponent : Stmt :=
  .assign 73 (.bin .add (.bin .add (.load (.reg 4)) (.reg 72)) (.const 10))

/-- The computed threshold exponent represents the model's exact
dyadic Detect threshold. -/
theorem selectMinRatioEpsilonExponent_runs {w heap m V k : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 4 = heap) (hk : st.regs 72 = k)
    (ha : st.mem heap = Num.IPM.alphaExponent m V)
    (hroom : Num.IPM.alphaExponent m V + k + 10 < 2 ^ w) :
    ∃ out, Runs w p ω selectMinRatioEpsilonExponent st .normal out 7 ∧
      out.regs 73 = Num.IPM.alphaExponent m V + k + 10 ∧
      1 / (2 : ℝ) ^ out.regs 73 = (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime m V / 1024 ∧
      (∀ r ≠ 73, out.regs r = st.regs r) ∧ out.mem = st.mem := by
  let exponent := Num.IPM.alphaExponent m V + k + 10
  let out := { st with regs := Function.update st.regs 73 exponent }
  have hsum : Num.IPM.alphaExponent m V + k < 2 ^ w := by omega
  have hr : Runs w p ω selectMinRatioEpsilonExponent st .normal out 7 :=
    runs_assign_iff.mpr ⟨exponent, by
      simp [Expr.eval, BinOp.eval, hh, hk, ha, exponent, hsum, hroom, show 10 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  refine ⟨out, hr, by simp [out, exponent], ?_, fun r hn => by simp [out, Function.update_of_ne hn], rfl⟩
  simp only [out, Function.update_self, exponent, Num.IPM.alphaPrime, pow_add]
  norm_num
  ring

/-- Select both dyadic exponents after storing the barrier block. -/
@[expose] def selectMinRatioQualityAndEpsilon (entry : ℕ) : Stmt :=
  selectMinRatioQuality entry ;; selectMinRatioEpsilonExponent

/-- The selected quality and threshold use the solver's quality procedure
and preserve the graph pointers and stability blocks. -/
theorem selectMinRatioQualityAndEpsilon_runs {w entry m V heap : ℕ}
    {k charge : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (IPM.Machine.solverQualityContract w k charge))
    (hm : st.regs 0 = m) (hh : st.regs 4 = heap) (hmw : m < 2 ^ w)
    (ha : st.mem heap = Num.IPM.alphaExponent m V)
    (hroom : Num.IPM.alphaExponent m V + k m + 10 < 2 ^ w) :
    ∃ out c, Runs w p ω (selectMinRatioQualityAndEpsilon entry) st .normal out c ∧
      out.regs 72 = k m ∧ out.regs 73 = Num.IPM.alphaExponent m V + k m + 10 ∧
      1 / (2 : ℝ) ^ out.regs 73 =
        (1 / (2 : ℝ) ^ k m) * Num.IPM.alphaPrime m V / 1024 ∧
      (∀ r, r ≠ 72 → r ≠ 73 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ charge m + 10 := by
  obtain ⟨mid, c, hr, hk, hkeep, hmem, hc⟩ :=
    selectMinRatioQuality_runs (ω := ω) himpl hm hmw (by omega)
  obtain ⟨out, hrun, he, heps, hregs, hmem'⟩ :=
    selectMinRatioEpsilonExponent_runs (ω := ω) ((hkeep 4 (by decide)).trans hh)
      hk (hmem.symm ▸ ha) hroom
  exact ⟨out, c + 8, runs_seq_iff.mpr (Or.inr ⟨mid, c, 7, hr, hrun, by omega⟩),
    (hregs 72 (by decide)).trans hk, he, heps,
    fun r h72 h73 => (hregs r h73).trans (hkeep r h72), hmem'.trans hmem, by omega⟩

end MinCostFlow.MinRatio
