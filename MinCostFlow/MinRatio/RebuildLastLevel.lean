module

public import MinCostFlow.MinRatio.LastLevelContract
public import WordRAM.Logic
public import MinCostFlow.IPM.Machine.PrecisionParameters
public import MinCostFlow.LastLevelProgram.OutputCapacity

/-!
# Rebuilding the terminal level

Algorithm 1 (page 20) ends the suffix rebuild at level `d`.
The terminal level builds its collection of forests on the graph and
lengths from the previous level, and selects branch zero.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Save the new terminal handle, call the last-level builder, and
select its first branch. The graph and lengths are in registers 6 and 7. Registers 67 and 68 carry the number
of limbs and the fixed-point precision. -/
@[expose] def rebuildLastLevelRuntime (init : ℕ) : Stmt :=
  .assign 3 (.reg 4) ;;
  .call 4 init [.reg 6, .reg 7, .reg 67, .reg 68, .reg 4] ;;
  .assign 2 (.const 0)

/-- The terminal rebuild produces precisely the model's collection
of forests and pays the last-level initialization budget. -/
theorem rebuildLastLevelRuntime_runs {w L init graph lengths heap vCap eCap multiplier stretchPrecision : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool} {G : MGraph}
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier stretchPrecision allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hh : st.regs 4 = heap)
    (hL : st.regs 67 = L) (hP : st.regs 68 = fmt.precision)
    (hwords : ∀ a ∈ [graph, lengths, L, fmt.precision, heap], a < 2 ^ w)
    (hpre : (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier stretchPrecision allocation).initPre
      [graph, lengths, L, fmt.precision, heap] st.mem)
    (hz : ZeroFrom st.mem heap) (hroom : heap + allocation 1 [graph, lengths, L, fmt.precision, heap] < 2 ^ w) :
    let model := tool.build G (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLastLevelRuntime init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap model y out.mem ∧
      LSFCollectionAt out.mem heap vCap eCap fmt.limbBits L fmt.precision G.E model ∧
      R.Respects (fun _ => False) heap (allocation 1 [graph, lengths, L, fmt.precision, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ multiplier * (tool.cost G + 1) + 12 := by
  dsimp only
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep, hpost, hframe, hcost⟩ :=
    himpl.2.1 [graph, lengths, L, fmt.precision, heap] st.mem st.pos ω hwords hpre hz hroom
  obtain ⟨hnext, hcollection⟩ := hpost
  change next = tool.build G (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E) at hnext
  subst next
  let first := { st with regs := Function.update st.regs 3 heap }
  let second := { after with regs := Function.update first.regs 4 o.value }
  let out := { second with regs := Function.update second.regs 2 0 }
  have hfirst : Runs w p ω (.assign 3 (.reg 4)) st .normal first 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hargs : evalArgs w first [.reg 6, .reg 7, .reg 67, .reg 68, .reg 4] = some [graph, lengths, L, fmt.precision, heap] := by
    simp [evalArgs, Expr.eval, first, Function.update_of_ne, hg, hl, hh, hL, hP]
  have hcall : Runs w p ω (.call 4 init [.reg 6, .reg 7, .reg 67, .reg 68, .reg 4])
      first .normal second (5 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  have hzero : 0 < 2 ^ w := Nat.two_pow_pos _
  have hlast : Runs w p ω (.assign 2 (.const 0)) second .normal out 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hzero], rfl, rfl, rfl⟩
  refine ⟨out, o.value, 2 + ((5 + c + 1) + 2 + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨first, 2, _, hfirst,
      runs_seq_iff.mpr (Or.inr ⟨second, _, 2, hcall, hlast, rfl⟩), rfl⟩),
    by simp [out], by simp [out, second, first, Function.update_of_ne],
    by simp [out, second, Function.update_of_ne], hrep, hcollection, hframe, ?_⟩
  change c + R.phi heap y after.mem ≤ multiplier * (tool.cost G + 1) at hcost
  change _ + R.phi heap y after.mem ≤ _
  omega

open IPM.Machine in
/-- The solver's format covers the last-level program's graph-derived
stretch precision on a terminal graph with the solver's length range. -/
theorem rebuildLastLevel_stretchCapacity {w m V k : ℕ}
    (hw : ipmQualityParameterWordBits m V k ≤ w) (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ)
    (hm : G.m ≤ 2 ^ ipmQualityRangeExponent m V k) (hn : G.n ≤ G.m + 1)
    (hℓ : ∀ e ∈ G.E, 1 / (2 : ℝ) ^ ipmQualityRangeExponent m V k ≤ ℓ e ∧
      ℓ e ≤ (2 : ℝ) ^ ipmQualityRangeExponent m V k)
    (hC : (⌈max 1 C⌉₊ : ℕ).size ≤ 4 * ipmQualityRangeExponent m V k + 30) :
    let F := ipmQualityMinRatioFormat m V k hw
    ∀ e ∈ G.E, 2 * (2 : ℝ) ^ LastLevelProgram.weightPrecision C G * lastLevelStretchBound G ℓ e <
      Num.capacity F.fmt.limbBits F.limbs := by
  intro F e he
  exact LastLevelProgram.stretchCapacity_ipmQualityFormat hw C G ℓ hm hn hℓ hC he

/-- The solver's quality format satisfies the terminal tool's limb
encoding and has enough bits for its fractional precision. -/
theorem ipmQualityMinRatioFormat_terminal_ready (m V k : ℕ) {w : ℕ}
    (hw : IPM.Machine.ipmQualityParameterWordBits m V k ≤ w) :
    let f := IPM.Machine.ipmQualityMinRatioFormat m V k hw
    f.fmt.limbBits = 4 ∧ f.fmt.precision ≤ 4 * f.limbs := by
  change 4 = 4 ∧ IPM.Machine.ipmQualityPrecision m V k ≤ 4 * IPM.Machine.ipmQualityLimbs m V k
  unfold IPM.Machine.ipmQualityLimbs
  omega

/-- Build the terminal forest collection from the prepared length table.
The builder receives the live lengths with their zero extension. -/
theorem rebuildLastLevelRuntime_tables_runs {w L init graph lengths heap vCap eCap multiplier stretchPrecision : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool} {G : MGraph}
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier stretchPrecision allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hh : st.regs 4 = heap)
    (hL : st.regs 67 = L) (hP : st.regs 68 = fmt.precision)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (ℓ : ℕ → ℝ) (hG : DynGraphAt st.mem graph vCap eCap G)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hst : ∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits L)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [graph, lengths, L, fmt.precision, heap] < 2 ^ w) :
    let model := tool.build G (fun e => if e ∈ G.E then ℓ e else 0)
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLastLevelRuntime init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap model y out.mem ∧
      LSFCollectionAt out.mem heap vCap eCap fmt.limbBits L fmt.precision G.E model ∧
      R.Respects (fun _ => False) heap (allocation 1 [graph, lengths, L, fmt.precision, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ multiplier * (tool.cost G + 1) + 12 := by
  dsimp only
  have hwords : ∀ a ∈ [graph, lengths, L, fmt.precision, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  have hdecode : readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E =
      fun e => if e ∈ G.E then ℓ e else 0 := by
    apply readEdgeValues_eq_of_support
    · exact hℓ.of_eqOn (fun e he => by simp [he])
    · intro e he
      simp [he]
  have hpre : (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier
      stretchPrecision allocation).initPre [graph, lengths, L, fmt.precision, heap] st.mem := by
    refine ⟨graph, lengths, heap, rfl, hFour, hWidth, ?_, ?_⟩
    · refine ⟨graph, lengths, heap, rfl, hG, hgraph, hLenRoom, fun e he => (hℓ e he).1, ?_⟩
      intro e he
      rw [readEdgeValues_eq hℓ he]
      exact hpos e he
    · intro length e he
      have hs : lastLevelStretchBound G (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E) e =
          lastLevelStretchBound G ℓ e := by
        unfold lastLevelStretchBound
        rw [readEdgeValues_eq hℓ he]
        congr 2
        exact Finset.sum_congr rfl (fun f hf => readEdgeValues_eq hℓ hf)
      change 2 * (2 : ℝ)^stretchPrecision *
        lastLevelStretchBound G (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E) e <
          Num.capacity fmt.limbBits L
      simpa only [hs] using hst e he
  rw [← hdecode]
  exact rebuildLastLevelRuntime_runs himpl hg hl hh hL hP hwords hpre hz hroom

end MinCostFlow.MinRatio
