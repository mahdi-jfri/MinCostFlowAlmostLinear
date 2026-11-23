module

public import MinCostFlow.MinRatio.InitParameters
import WordRAM.Exec

/-!
# Min-ratio initialization entry parameters

Prepare the numeric inputs and select the number of branches for the
chain initialized by Algorithm 1 (page 20).
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Enlarge the stability bound by the extra range required for the
quality exponent in register 72. The slack exponent is in the precision record. -/
@[expose] def adjustInitQualityPsi : Stmt :=
  .assign 6 (.bin .add (.reg 6) (.bin .mul (.const 4)
    (.bin .sub (.reg 72) (.load (.reg 5)))))

/-- The adjustment gives the quality-dependent stability bound in one word. -/
theorem adjustInitQualityPsi_runs {w m V k record : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : st.regs 5 = record) (hk : st.regs 72 = k)
    (hs : st.mem record = IPM.Machine.slackRangeExponent m V)
    (hbase : st.regs 6 = IPM.Machine.ipmRangeExponent m V + IPM.Machine.slackRangeExponent m V + 6)
    (hfit : IPM.Machine.ipmQualityRangeExponent m V k +
      IPM.Machine.slackRangeExponent m V + 6 < 2 ^ w) :
    ∃ out, Runs w p ω adjustInitQualityPsi st .normal out 9 ∧
      out.regs 6 = IPM.Machine.ipmQualityRangeExponent m V k +
        IPM.Machine.slackRangeExponent m V + 6 ∧
      (∀ r ≠ 6, out.regs r = st.regs r) ∧ out.mem = st.mem := by
  let slack := IPM.Machine.slackRangeExponent m V
  let target := IPM.Machine.ipmQualityRangeExponent m V k + slack + 6
  have hsum : st.regs 6 + 4 * (k - slack) = target := by
    rw [hbase]
    unfold target slack IPM.Machine.ipmQualityRangeExponent IPM.Machine.ipmRangeExponent
      IPM.Machine.qualitySlackExponent
    omega
  have ht : target < 2 ^ w := hfit
  have hmul : 4 * (k - slack) < 2 ^ w := by omega
  have hsub : k - slack < 2 ^ w := by omega
  have hfour : 4 < 2 ^ w := by omega
  let out := {st with regs := Function.update st.regs 6 target}
  refine ⟨out, runs_assign_iff.mpr ⟨target, ?_, rfl, rfl, rfl⟩,
    by rw [show out.regs 6 = target by simp [out]], fun r hne => by simp [out, hne], rfl⟩
  have hslack : st.mem record = slack := hs
  simp [Expr.eval, BinOp.eval, hr, hk, hslack, ht, hsub, hmul, hfour, hsum]

/-- Prepare the barrier, hidden stability, quality, and Detect threshold
from the seven-word Init arguments. -/
@[expose] def prepareMinRatioNumericParametersAt (alpha select quality edgeOffset : ℕ) : Stmt :=
  prepareMinRatioStabilityAt alpha select edgeOffset ;;
  (selectMinRatioQualityAndEpsilon quality ;; adjustInitQualityPsi)

/-- The Init prefix obtains all four exact numeric parameters while
preserving the input graph and number tables. -/
theorem prepareMinRatioNumericParametersAt_runs
    {w h alpha select quality graph gradient lengths limbs precision V heap edgeOffset : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    {qualityExponent qualityCharge : ℕ → ℕ}
    (hquality : MeetsContract w p quality
      (IPM.Machine.solverQualityContract w qualityExponent qualityCharge))
    (halpha : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hselect : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hEdge : mem (graph + edgeOffset) = G.m)
    (hgraph : graph + edgeOffset < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hw : IPM.Machine.ipmParameterWordBits G.m V ≤ w)
    (hpsi : IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) + 6 < 2 ^ w)
    (hepsRoom : Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioNumericParametersAt alpha select quality edgeOffset)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      out.regs 4 = heap ∧
      out.regs 6 = IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) +
        IPM.Machine.slackRangeExponent G.m V + 6 ∧
      out.regs 7 = heap + (limbs + 1) + 6 ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      out.regs 72 = qualityExponent G.m ∧
      out.regs 73 = Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 ∧
      1 / (2 : ℝ) ^ out.regs 73 =
        (1 / (2 : ℝ) ^ qualityExponent G.m) * Num.IPM.alphaPrime G.m V / 1024 ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20028 * (G.m.size + V.size) + qualityCharge G.m + 20672 := by
  obtain ⟨mid, c, hr, hm, hV, hL, hP, hh, hΨ, hret, hg, hgrad, hlen, hframe,
    hfree, ha, hv, hval, hc, h5, hrecord⟩ :=
    prepareMinRatioStabilityAt_runs (ω := ω) (gradient := gradient) (lengths := lengths) (pos := pos)
      halpha hselect hEdge hgraph hmw hVw hLw hPw hsize hcover hwidth hscale hw (by
        have hle := IPM.Machine.slackRangeExponent_le_qualitySlackExponent G.m V (qualityExponent G.m)
        unfold IPM.Machine.ipmQualityRangeExponent at hpsi
        unfold IPM.Machine.ipmRangeExponent
        omega) hz hroom
  obtain ⟨selected, c', hr', hq, hexp, heps, hkeep, hmem, hc'⟩ :=
    selectMinRatioQualityAndEpsilon_runs (ω := ω) hquality hm hh hmw ha hepsRoom
  have hslack : selected.mem (heap + (limbs + 1)) = IPM.Machine.slackRangeExponent G.m V := by
    rw [hmem]
    simpa [IPM.Machine.precisionWords] using hrecord 0 (by simp [IPM.Machine.precisionWords])
  have hbase : selected.regs 6 =
      IPM.Machine.ipmRangeExponent G.m V + IPM.Machine.slackRangeExponent G.m V + 6 := by
    rw [hkeep 6 (by decide) (by decide)]
    unfold IPM.Machine.precisionHiddenPsi at hΨ
    exact_mod_cast hΨ
  obtain ⟨out, hadjust, hΨ', hkeep', hm'⟩ :=
    adjustInitQualityPsi_runs (w := w) (p := p) (ω := ω)
      ((hkeep 5 (by decide) (by decide)).trans h5) hq hslack hbase hpsi
  have keep (r : ℕ) (hne : r ≠ 6 := by decide) := hkeep' r hne
  have hret' := (keep 7).trans ((hkeep 7 (by decide) (by decide)).trans hret)
  refine ⟨out, c + (c' + 10) + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, c' + 10, hr,
    runs_seq_iff.mpr (Or.inr ⟨selected, c', 9, hr', hadjust, by omega⟩), rfl⟩), ?_⟩
  simp only [keep 0, keep 1, keep 2, keep 3, keep 4, keep 69, keep 70, keep 71,
    keep 72, keep 73, hm', hmem]
  exact ⟨(hkeep 0 (by decide) (by decide)).trans hm, (hkeep 1 (by decide) (by decide)).trans hV,
    (hkeep 2 (by decide) (by decide)).trans hL, (hkeep 3 (by decide) (by decide)).trans hP,
    (hkeep 4 (by decide) (by decide)).trans hh, hΨ', hret',
    (hkeep 69 (by decide) (by decide)).trans hg, (hkeep 70 (by decide) (by decide)).trans hgrad,
    (hkeep 71 (by decide) (by decide)).trans hlen, hq, hexp, heps, hframe,
    by simpa only [hret', hret] using hfree, ha, hv, hval, by omega⟩

/-- Use the dynamic graph header for the numeric Init prefix. -/
@[expose] def prepareMinRatioNumericParameters (alpha select quality : ℕ) : Stmt :=
  prepareMinRatioNumericParametersAt alpha select quality 3

/-- The dynamic graph layout supplies the numeric prefix's edge count. -/
theorem prepareMinRatioNumericParameters_runs
    {w h alpha select quality graph gradient lengths limbs precision V heap vc ec : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    {qualityExponent qualityCharge : ℕ → ℕ}
    (hquality : MeetsContract w p quality
      (IPM.Machine.solverQualityContract w qualityExponent qualityCharge))
    (halpha : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hselect : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hG : DynSpanner.Program.DynGraphAt mem graph vc ec G)
    (hgraph : graph + 3 < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hw : IPM.Machine.ipmParameterWordBits G.m V ≤ w)
    (hpsi : IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) + 6 < 2 ^ w)
    (hepsRoom : Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioNumericParameters alpha select quality)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      out.regs 4 = heap ∧
      out.regs 6 = IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) +
        IPM.Machine.slackRangeExponent G.m V + 6 ∧
      out.regs 7 = heap + (limbs + 1) + 6 ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      out.regs 72 = qualityExponent G.m ∧
      out.regs 73 = Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 ∧
      1 / (2 : ℝ) ^ out.regs 73 =
        (1 / (2 : ℝ) ^ qualityExponent G.m) * Num.IPM.alphaPrime G.m V / 1024 ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20028 * (G.m.size + V.size) + qualityCharge G.m + 20672 :=
  prepareMinRatioNumericParametersAt_runs hquality halpha hselect hG.2.2.2.2.2.2.1 hgraph hmw hVw hLw hPw hsize hcover hwidth hscale hw hpsi hz hroom hepsRoom

/-- The callable branching search takes `[depth, m]` and returns the
branch count without changing memory. -/
@[expose] def minRatioBranchCountBody : Stmt :=
  .assign 2 (.reg 1) ;; .assign 1 (.reg 0) ;;
    selectMinRatioBranchCount ;; .ret (.reg 6)

/-- Read-only procedure contract for selecting the chain branching factor. -/
@[expose] def minRatioBranchCountContract (w : ℕ) : Contract where
  pre args _ := ∃ d m, args = [d, m] ∧ 0 < d ∧ 1 ≤ m ∧ 2 < 2 ^ w
  post args mem value out := out = mem ∧ ∃ (d m : ℕ) (hd : 0 < d) (hm : 1 ≤ m),
    args = [d, m] ∧ value = (Chain.mkChainParams d m hd hm).k
  cost args _ := (19 * args.getD 0 0 + 32) * (args.getD 1 0).size + 19

/-- The fixed procedure body implements the exact branching selection
contract and counts its call-local argument setup and return. -/
theorem minRatioBranchCount_meetsContract {w entry : ℕ} {p : Program}
    (hbody : p.procs[entry]? = some minRatioBranchCountBody) :
    MeetsContract w p entry (minRatioBranchCountContract w) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨d, m, rfl, hd, hm, hw⟩ := hpre
  let s0 := startState [d, m] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 2 m }
  let ready := { s1 with regs := Function.update s1.regs 1 d }
  have h1 : Runs w p ω (.assign 2 (.reg 1)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨m, rfl, rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 1 (.reg 0)) s1 .normal ready 2 :=
    runs_assign_iff.mpr ⟨d, rfl, rfl, rfl, rfl⟩
  obtain ⟨out, c, hr, hk, _, _, hmem, _, hc⟩ :=
    selectMinRatioBranchCount_runs (ω := ω) (st := ready) (depth := d) (m := m) rfl rfl hd hm hw
      (hwords d (by simp)) (hwords m (by simp))
  have hret : Runs w p ω (.ret (.reg 6)) out (.returned (out.regs 6)) out 2 :=
    runs_ret_iff.mpr ⟨out.regs 6, rfl, rfl, rfl, rfl⟩
  refine ⟨.returned (out.regs 6), out, c + 9, ?_, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, 2, c + 6, h1,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, c + 3, h2,
        runs_seq_iff.mpr (Or.inr ⟨out, c, 2, hr, hret, by omega⟩), by omega⟩), by omega⟩)
  · exact ⟨hmem, d, m, hd, hm, rfl, hk⟩
  · change c + 9 ≤ (19 * d + 32) * m.size + 19
    omega

/-- Select the branching factor from the saved depth and edge count,
using a call so that the numeric parameters already loaded survive. -/
@[expose] def initMinRatioBranchCountFrom (entry mReg : ℕ) : Stmt :=
  .call 76 entry [.reg 75, .reg mReg]

/-- The runtime branching factor lands in its handle-store register. -/
theorem initMinRatioBranchCountFrom_runs {w entry depth m mReg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hd : st.regs 75 = depth) (hm : st.regs mReg = m)
    (hdpos : 0 < depth) (hmpos : 1 ≤ m) (hw : 2 < 2 ^ w)
    (hdw : depth < 2 ^ w) (hmw : m < 2 ^ w) :
    ∃ out c, Runs w p ω (initMinRatioBranchCountFrom entry mReg) st .normal out c ∧
      out.regs 76 = (Chain.mkChainParams depth m hdpos hmpos).k ∧
      (∀ r ≠ 76, out.regs r = st.regs r) ∧ out.mem = st.mem ∧
      c ≤ (19 * depth + 32) * m.size + 22 := by
  have hargs : evalArgs w st [.reg 75, .reg mReg] = some [depth, m] := by
    simp [evalArgs, Expr.eval, hd, hm]
  have hwords : ∀ a ∈ [depth, m], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> assumption
  have hpre : (minRatioBranchCountContract w).pre [depth, m] st.mem :=
    ⟨depth, m, rfl, hdpos, hmpos, hw⟩
  obtain ⟨out, c, v, hr, hp, hreg, hkeep, hc⟩ :=
    runs_call_of_meetsContract (r := 76) himpl hargs hwords hpre ω
  obtain ⟨hmem, d, n, hd', hn', hargs', hvalue⟩ := hp
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl⟩ := hargs'
  change c ≤ 2 + ((19 * depth + 32) * m.size + 19) + 1 at hc
  exact ⟨out, c, hr, hreg.trans hvalue, hkeep, hmem, by omega⟩

/-- Select the branching factor from the saved depth and edge count,
using a call so that the numeric parameters already loaded survive. -/
@[expose] def initMinRatioBranchCount (entry : ℕ) : Stmt :=
  initMinRatioBranchCountFrom entry 0

/-- The runtime branching factor lands in its handle-store register. -/
theorem initMinRatioBranchCount_runs {w entry depth m : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hd : st.regs 75 = depth) (hm : st.regs 0 = m)
    (hdpos : 0 < depth) (hmpos : 1 ≤ m) (hw : 2 < 2 ^ w)
    (hdw : depth < 2 ^ w) (hmw : m < 2 ^ w) :
    ∃ out c, Runs w p ω (initMinRatioBranchCount entry) st .normal out c ∧
      out.regs 76 = (Chain.mkChainParams depth m hdpos hmpos).k ∧
      (∀ r ≠ 76, out.regs r = st.regs r) ∧ out.mem = st.mem ∧
      c ≤ (19 * depth + 32) * m.size + 22 :=
  initMinRatioBranchCountFrom_runs (ω := ω) himpl hd hm hdpos hmpos hw hdw hmw

/-- Use a certified depth to select the corresponding branch count.
An inconclusive comparison enters the supplied retry body. -/
@[expose] def initMinRatioCertifiedDimensions (entry mReg : ℕ) (retry : Stmt) : Stmt :=
  .cond (.reg 109) (.assign 75 (.reg 110) ;; initMinRatioBranchCountFrom entry mReg) retry

/-- Once certified, depth and branch selection preserve the input memory. -/
theorem initMinRatioCertifiedDimensions_runs {w entry mReg m depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hflag : st.regs 109 = 1) (hc : st.regs 110 = depth)
    (hmReg : mReg ≠ 75) (hm : st.regs mReg = m)
    (hexact : depth = Chain.chosenD (23 / 24) m)
    (hdpos : 0 < depth) (hmpos : 1 ≤ m) (hw : 2 < 2 ^ w)
    (hdw : depth < 2 ^ w) (hmw : m < 2 ^ w) :
    ∃ out cost, Runs w p ω (initMinRatioCertifiedDimensions entry mReg retry) st .normal out cost ∧
      out.regs 75 = Chain.chosenD (23 / 24) m ∧
      out.regs 76 = (Chain.mkChainParams depth m hdpos hmpos).k ∧
      (∀ r, r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧ out.mem = st.mem ∧
      cost ≤ (19 * depth + 32) * m.size + 27 := by
  let mid := {st with regs := Function.update st.regs 75 depth}
  have ha : Runs w p ω (.assign 75 (.reg 110)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hc], rfl, rfl, rfl⟩
  obtain ⟨out, c, hr, hk, hregs, hmem, hcost⟩ :=
    initMinRatioBranchCountFrom_runs (ω := ω) himpl (st := mid) (mReg := mReg) (by simp [mid])
      (by simp [mid, Function.update_of_ne, hmReg, hm]) hdpos hmpos hw hdw hmw
  refine ⟨out, 2 + c + 1 + 2, runs_cond_iff.mpr ⟨1, 2 + c + 1, by simp [Expr.eval, hflag],
    runs_seq_iff.mpr (Or.inr ⟨mid, 2, c, ha, hr, rfl⟩), by simp [Expr.size_reg]; omega⟩,
    ?_, hk, ?_, hmem, by omega⟩
  · rw [hregs 75 (by decide)]
    simpa [mid] using hexact
  · intro r h75 h76
    rw [hregs r h76]
    simp [mid, Function.update_of_ne, h75]

end MinCostFlow.MinRatio
