module

public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.MinRatio.ShiftBranch
public import MinCostFlow.MinRatio.PassReset
public import MinCostFlow.MinRatio.RebuildLastLevel
public import MinCostFlow.MinRatio.RebuildLevel
public import MinCostFlow.MinRatio.ShiftModelPrefix
import MinCostFlow.MinRatio.ShiftForestScan

/-!
# Terminal branch selection in Shift

Algorithm 1 (page 20) advances the selected branch modulo the number
of branches. At level `d` it uses the terminal forest collection's
branch count. The branch cell is updated before applying the tree edits.
-/

public section
namespace MinCostFlow.MinRatio
open Chain WordRAM

/-- At the terminal level, the machine chooses exactly the branch
recorded by the model Shift. The branch store takes 14 steps. -/
theorem shiftLastLevel_branch_runs {w addr : ℕ} {T : SparseCoreRestartTool}
    {tool : LastLevelTool} {P : ChainParams} {model : ChainState T P}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 0 = addr) (hk : st.regs 1 = model.lastK)
    (hb : st.mem addr = model.lastBran) (hbranch : model.lastBran < model.lastK)
    (hword : model.lastK < 2 ^ w) :
    let next := (algorithm1_shift T tool P model P.d).1
    ∃ out, Runs w p ω shiftBranch st .normal out 14 ∧
      out.mem = Function.update st.mem addr next.lastBran ∧
      out.regs 2 = next.lastBran ∧
      (∀ r, r ≠ 2 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  have heq : (algorithm1_shift T tool P model P.d).1.lastBran =
      (model.lastBran + 1) % model.lastK := by
    simp [algorithm1_shift]
  simpa only [heq] using shiftBranch_runs (p := p) (ω := ω) ha hk hb hbranch hword

/-- Algorithm 2 (page 29) advances its terminal scheduling branch modulo the
schedule's branch count and records whether it wrapped in register 3. -/
@[expose] def shiftTerminalScheduleBranch : Stmt :=
  shiftBranch ;; .assign 3 (.bin .eq (.reg 2) (.const 0))

theorem shiftTerminalScheduleBranch_noRand : shiftTerminalScheduleBranch.NoRand := by
  simp [shiftTerminalScheduleBranch, shiftBranch_noRand, Stmt.NoRand]

/-- The terminal scheduling branch and wrap flag take 19 steps. The branch
cell is the only memory location written. -/
theorem shiftTerminalScheduleBranch_runs {w addr branch k : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hb : st.mem addr = branch) (hbranch : branch < k) (hword : k < 2 ^ w) :
    let next := (branch + 1) % k
    ∃ out, Runs w p ω shiftTerminalScheduleBranch st .normal out 19 ∧
      out.mem = Function.update st.mem addr next ∧ out.regs 2 = next ∧
      out.regs 3 = (if next = 0 then 1 else 0) ∧
      (∀ r, r ≠ 2 → r ≠ 3 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  dsimp only
  obtain ⟨mid, hr, hm, hn, hregs, hp⟩ :=
    shiftBranch_runs (p := p) (ω := ω) ha hk hb hbranch hword
  let flag := if (branch + 1) % k = 0 then 1 else 0
  let out := { mid with regs := Function.update mid.regs 3 flag }
  have hflag : flag < 2 ^ w := by dsimp [flag]; split <;> omega
  have hs : Runs w p ω (.assign 3 (.bin .eq (.reg 2) (.const 0))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨flag, by simp [Expr.eval, BinOp.eval, hn, flag, show (if (branch + 1) % k = 0 then 1 else 0) < 2 ^ w from hflag],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 14, 4, hr, hs, rfl⟩),
    hm, ?_, by simp [out, flag], ?_, hp⟩
  · simpa [out, Function.update_of_ne] using hn
  · intro r hr₂ hr₃
    simpa [out, Function.update_of_ne hr₃] using hregs r hr₂

/-- Algorithm 2 (page 29) advances the terminal scheduler branch and its pass.
Register 4 holds the pass table base and register 5 the terminal index. -/
@[expose] def shiftTerminalSchedule : Stmt :=
  shiftTerminalScheduleBranch ;;
  .assign 0 (.reg 4) ;;
  .assign 1 (.reg 5) ;;
  .assign 2 (.bin .add (.reg 5) (.const 1)) ;;
  advanceShiftPasses

theorem shiftTerminalSchedule_noRand : shiftTerminalSchedule.NoRand := by
  simp [shiftTerminalSchedule, shiftTerminalScheduleBranch_noRand, advanceShiftPasses_noRand,
    Stmt.NoRand]

/-- Terminal scheduling takes at most 56 steps and touches only its branch
and pass cells. The terminal index has no deeper counters. -/
theorem shiftTerminalSchedule_runs {w addr branch k base d count : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hb : st.mem addr = branch) (hbranch : branch < k) (hword : k < 2 ^ w)
    (hbase : st.regs 4 = base) (hd : st.regs 5 = d)
    (hcount : st.mem (base + d) = count)
    (hdisjoint : base + d ≠ addr) (hbound : base + (d + 1) < 2 ^ w)
    (hpass : (branch + 1) % k = 0 → count + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω shiftTerminalSchedule st .normal out cost ∧
      cost ≤ 56 ∧ out.pos = st.pos ∧
      ∀ a, out.mem a = if a = base + d ∧ (branch + 1) % k = 0 then count + 1
        else Function.update st.mem addr ((branch + 1) % k) a := by
  obtain ⟨mid, hr, hm, _, hflag, hregs, hp⟩ :=
    shiftTerminalScheduleBranch_runs (ω := ω) ha hk hb hbranch hword
  let s0 := { mid with regs := Function.update mid.regs 0 base }
  let s1 := { s0 with regs := Function.update s0.regs 1 d }
  let s2 := { s1 with regs := Function.update s1.regs 2 (d + 1) }
  have h0 : Runs w p ω (.assign 0 (.reg 4)) mid .normal s0 2 :=
    runs_assign_iff.mpr ⟨base, by simp [Expr.eval, hregs 4 (by decide) (by decide), hbase],
      rfl, rfl, rfl⟩
  have h1 : Runs w p ω (.assign 1 (.reg 5)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨d, by simp [Expr.eval, s0, Function.update_of_ne,
      hregs 5 (by decide) (by decide), hd], rfl, rfl, rfl⟩
  have hw : 1 < 2 ^ w := by omega
  have hnext : d + 1 < 2 ^ w := by omega
  have h2 : Runs w p ω (.assign 2 (.bin .add (.reg 5) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨d + 1, by simp [Expr.eval, BinOp.eval, s1, s0, Function.update_of_ne,
      hregs 5 (by decide) (by decide), hd, hw, hnext], rfl, rfl, rfl⟩
  let wrapped := decide ((branch + 1) % k = 0)
  obtain ⟨out, cost, hpassRun, hcost, hmem, hpos⟩ :=
    advanceShiftPasses_runs (ω := ω) (st := s2) wrapped
      (base := base) (i := d) (stop := d + 1) (count := count)
      (by simp [s2, s1, s0, Function.update_of_ne])
      (by simp [s2, s1, Function.update_of_ne]) (by simp [s2])
      (by simpa [s2, s1, s0, Function.update_of_ne, wrapped] using hflag)
      (by simp [s2, s1, s0, hm, Function.update_of_ne hdisjoint, hcount])
      (Nat.lt_succ_self _) hbound hw (fun h => hpass (of_decide_eq_true h))
  refine ⟨out, 19 + (2 + (2 + (4 + cost + 1) + 1) + 1) + 1, ?_,
    by omega, hpos.trans hp, fun a => ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 19, _, hr,
      runs_seq_iff.mpr (Or.inr ⟨s0, 2, _, h0,
        runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, h1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, h2, hpassRun, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  · have hnone : ¬ (base + (d + 1) ≤ a ∧ a < base + (d + 1)) := by omega
    simp [hmem, hnone, wrapped, s2, s1, s0, hm]

/-- At the terminal index of Algorithm 2 (page 29), the next scheduling
branch is the old branch advanced modulo the schedule's branch count.
The pass update affects only the terminal pass, and only on wrap. -/
theorem shiftTerminalSchedule_state_runs {cfg : Alg2Config} (model : Alg2State cfg)
    {w addr base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (ha : st.regs 0 = addr) (hk : st.regs 1 = cfg.P.k)
    (hb : st.mem addr = model.branD) (hbranch : model.branD < cfg.P.k)
    (hword : cfg.P.k < 2 ^ w) (hbase : st.regs 4 = base) (hd : st.regs 5 = cfg.P.d)
    (htable : ∀ j, st.mem (base + j.val) = model.passes j)
    (hdisjoint : ∀ j : Fin (cfg.P.d + 1), base + j.val ≠ addr)
    (hbound : base + (cfg.P.d + 1) < 2 ^ w)
    (hpass : (model.branD + 1) % cfg.P.k = 0 →
      model.passes (Fin.last cfg.P.d) + 1 < 2 ^ w) :
    let i := Fin.last cfg.P.d
    let next := (model.branD + 1) % cfg.P.k
    ∃ out cost, Runs w p ω shiftTerminalSchedule st .normal out cost ∧
      cost ≤ 56 ∧ out.pos = st.pos ∧ out.mem addr = next ∧
      ∀ j : Fin (cfg.P.d + 1), out.mem (base + j.val) =
        if i < j then 0
        else if j = i then (if next = 0 then model.passes i + 1 else model.passes i)
        else model.passes j := by
  dsimp only
  obtain ⟨out, cost, hr, hc, hp, hm⟩ :=
    shiftTerminalSchedule_runs (ω := ω) ha hk hb hbranch hword hbase hd
      (htable (Fin.last cfg.P.d)) (hdisjoint (Fin.last cfg.P.d)) hbound hpass
  refine ⟨out, cost, hr, hc, hp, ?_, fun j => ?_⟩
  · rw [hm]
    have haddr : addr ≠ base + cfg.P.d := Ne.symm (hdisjoint (Fin.last cfg.P.d))
    simp [haddr]
  · rw [hm, Function.update_of_ne (hdisjoint j), htable j]
    have hn : ¬ Fin.last cfg.P.d < j := not_lt_of_ge (Fin.le_last j)
    have heq : base + j.val = base + cfg.P.d ↔ j = Fin.last cfg.P.d := by
      rw [Nat.add_left_cancel_iff, Fin.ext_iff]
      rfl
    by_cases hj : j = Fin.last cfg.P.d
    · subst j
      simp
    · simp only [hn, ite_false, hj, heq, false_and]

/-- A shift whose deeper suffix is terminal runs the last-level builder
on the prepared graph and length table. Exact model equality uses the
zero-extension convention of the terminal initializer (page 20). -/
theorem shiftTerminalBuild_tables_runs {w limbs init graph lengths heap vc ec multiplier stretchPrecision i : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {tool : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (hi : i + 1 = P.d)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool} :
    let next := (algorithm1_shift T tool P chain i).1
    let G := next.G P.d
    let ℓ := next.toTreeChain.chainLen chain.ℓ P.d
    R.Implements w p init op (lastLevelRuntimeMachineContract fmt limbs tool G vc ec multiplier stretchPrecision allocation) →
    st.regs 67 = limbs → st.regs 68 = fmt.precision →
    limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    st.regs 6 = graph → st.regs 7 = lengths → st.regs 4 = heap →
    DynSpanner.Program.DynGraphAt st.mem graph vc ec G →
    graph + DynSpanner.Program.dynGraphSize vc ec ≤ heap → lengths + ec * limbs ≤ heap →
    EdgeValuesAt st.mem lengths fmt.limbBits limbs fmt.precision G.E ℓ →
    (∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ G.E, 0 < ℓ e) → (∀ e ∉ G.E, ℓ e = 0) →
    ZeroFrom st.mem heap → heap + allocation 1 [graph, lengths, limbs, fmt.precision, heap] < 2 ^ w →
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLastLevelRuntime init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap (next.lastK, next.lastLSFs) y out.mem ∧
      LSFCollectionAt out.mem heap vc ec fmt.limbBits limbs fmt.precision G.E
        (next.lastK, next.lastLSFs) ∧
      R.Respects (fun _ => False) heap (allocation 1 [graph, lengths, limbs, fmt.precision, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ multiplier * (tool.cost G + 1) + 12 := by
  dsimp only
  intro himpl hL hP hLWord hPWord hFour hWidth hg hl hh hgraph hgraphEnd hlenEnd htable hst hpos hsupport hz hroom
  let G := (algorithm1_shift T tool P chain i).1.G P.d
  let ℓ := (algorithm1_shift T tool P chain i).1.toTreeChain.chainLen chain.ℓ P.d
  have hmask : (fun e => if e ∈ G.E then ℓ e else 0) = ℓ := by
    funext e
    by_cases he : e ∈ G.E
    · simp [he]
    · rw [ite_eq_right he]
      exact (hsupport e he).symm
  rw [shiftTerminalBuild_eq T tool P chain i hi]
  simpa only [G, ℓ, hmask] using
    rebuildLastLevelRuntime_tables_runs (ω := ω) himpl hg hl hh hL hP hLWord hPWord hFour hWidth ℓ
      hgraph hgraphEnd hlenEnd htable hst hpos hz hroom

/-- At the terminal handoff, zero extension on the old graph carries
through multiplication. For names dropped by the restarted sparsifier,
zero extension on the new graph additionally requires the new stretch
to vanish wherever the old length is positive (Definition 5.6, page 18). -/
theorem shiftTerminalLength_support_iff {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : ℕ) (hi : i + 1 = P.d)
    (hzero : ∀ e ∉ (chain.G i).E, chain.toTreeChain.chainLen chain.ℓ i e = 0)
    (hpos : ∀ e ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen chain.ℓ i e) :
    let next := (algorithm1_shift T L P chain i).1
    let branch := (chain.bran i + 1) % P.k
    let forest := T.lsfs (T.restart (chain.scState i) branch) branch
    (∀ e ∉ (next.G P.d).E, next.toTreeChain.chainLen chain.ℓ P.d e = 0) ↔
      ∀ e ∈ (chain.G i).E, e ∉ (next.G P.d).E → forest.wstr e = 0 := by
  dsimp only
  have hlt : i < P.d := by omega
  have hlen := (shiftNextLevelNumbers T L P chain i hlt).1
  rw [hi] at hlen
  rw [hlen]
  constructor
  · intro h e he hnew
    have hm := h e hnew
    change _ * chain.toTreeChain.chainLen chain.ℓ i e = 0 at hm
    exact (mul_eq_zero.mp hm).resolve_right (ne_of_gt (hpos e he))
  · intro h e hnew
    unfold coreLen
    by_cases he : e ∈ (chain.G i).E
    · rw [h e he hnew, zero_mul]
    · rw [hzero e he, mul_zero]

/-- A dropped edge with positive length and stretch witnesses the
mismatch between the terminal model lengths and the machine decoding. -/
theorem shiftTerminalLength_ne_readEdgeValues {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : ℕ) (hi : i + 1 = P.d)
    {mem : ℕ → ℕ} {lenAddr limbBits limbs precision e : ℕ}
    (hdrop : e ∉ ((algorithm1_shift T L P chain i).1.G P.d).E)
    (hpos : 0 < chain.toTreeChain.chainLen chain.ℓ i e)
    (hst : 0 < (T.lsfs (T.restart (chain.scState i) ((chain.bran i + 1) % P.k))
      ((chain.bran i + 1) % P.k)).wstr e) :
    readEdgeValues mem lenAddr limbBits limbs precision ((algorithm1_shift T L P chain i).1.G P.d).E ≠
      (algorithm1_shift T L P chain i).1.toTreeChain.chainLen chain.ℓ P.d := by
  intro h
  have hlt : i < P.d := by omega
  have hlen := (shiftNextLevelNumbers T L P chain i hlt).1
  rw [hi] at hlen
  have hmodel := congrFun (h.trans hlen) e
  rw [readEdgeValues, ite_eq_right hdrop] at hmodel
  exact (ne_of_gt (mul_pos hst hpos)) hmodel.symm

/-- The terminal machine build satisfies the last-level guarantees
for the live model lengths, even if the model carries other values on
discarded edge names (Definition 5.8, pages 19–20). -/
theorem lastLevelDecodedBuild_spec {tool : LastLevelTool} {LP : LastLevelParams}
    (hspec : tool.IsSpec LP) {G : MGraph} {ℓ : ℕ → ℝ}
    {mem : ℕ → ℕ} {ptr h limbs precision : ℕ}
    (hG : G.IsValid) (htable : EdgeValuesAt mem ptr h limbs precision G.E ℓ)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) :
    let built := tool.build G (readEdgeValues mem ptr h limbs precision G.E)
    0 < built.1 ∧
    (∀ j < built.1, (built.2 j).Holds G ℓ (LP.σ_last G.n)) ∧
    (∀ e ∈ G.E, (∑ j ∈ Finset.range built.1, (built.2 j).wstr e) / (built.1 : ℝ) ≤ LP.σ_mwu G.n) ∧
    (∀ j < built.1, ∀ u ∈ G.V, ∀ v ∈ G.V,
      G.Connected u v → (built.2 j).F.F.Connected u v) ∧
    ((tool.cost G : ℝ) ≤ LP.c_last * ((G.m : ℝ) + 1) ^ 2 *
      (Real.log ((G.m : ℝ) + (G.n : ℝ) + 2)) ^ LP.p_last) := by
  have hread : ∀ e ∈ G.E, readEdgeValues mem ptr h limbs precision G.E e = ℓ e :=
    fun _ he => readEdgeValues_eq htable he
  have hpositive : ∀ e ∈ G.E, 0 < readEdgeValues mem ptr h limbs precision G.E e := by
    intro e he
    rw [hread e he]
    exact hpos e he
  obtain ⟨hk, hforests, hstretch, hspan, hcost⟩ :=
    hspec G (readEdgeValues mem ptr h limbs precision G.E) hG hpositive
  exact ⟨hk, fun j hj => LSF.Holds.congr_len (hforests j hj) hread, hstretch, hspan, hcost⟩

/-- Execute the terminal rebuild on the shifted graph while retaining the
last-level guarantees for its live model lengths. The represented forest
collection is the one actually built from the machine-decoded values. -/
theorem shiftTerminalBuild_decoded_runs {w limbs init graph lengths heap vc ec multiplier stretchPrecision i : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {tool : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (hi : i + 1 = P.d)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    {LP : LastLevelParams} (hspec : tool.IsSpec LP) :
    let next := (algorithm1_shift T tool P chain i).1
    let G := next.G (i + 1)
    let ℓ := next.toTreeChain.chainLen chain.ℓ P.d
    let built := tool.build G (readEdgeValues st.mem lengths fmt.limbBits limbs fmt.precision G.E)
    R.Implements w p init op (lastLevelRuntimeMachineContract fmt limbs tool G vc ec multiplier stretchPrecision allocation) →
    st.regs 67 = limbs → st.regs 68 = fmt.precision →
    limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    st.regs 6 = graph → st.regs 7 = lengths → st.regs 4 = heap →
    DynSpanner.Program.DynGraphAt st.mem graph vc ec G →
    graph + DynSpanner.Program.dynGraphSize vc ec ≤ heap → lengths + ec * limbs ≤ heap →
    EdgeValuesAt st.mem lengths fmt.limbBits limbs fmt.precision G.E ℓ →
    (∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ G.E, 0 < ℓ e) →
    ZeroFrom st.mem heap → heap + allocation 1 [graph, lengths, limbs, fmt.precision, heap] < 2 ^ w →
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLastLevelRuntime init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap built y out.mem ∧
      LSFCollectionAt out.mem heap vc ec fmt.limbBits limbs fmt.precision G.E built ∧
      R.Respects (fun _ => False) heap (allocation 1 [graph, lengths, limbs, fmt.precision, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ multiplier * (tool.cost G + 1) + 12 ∧
      0 < built.1 ∧
      (∀ j < built.1, (built.2 j).Holds G ℓ (LP.σ_last G.n)) ∧
      (∀ e ∈ G.E, (∑ j ∈ Finset.range built.1, (built.2 j).wstr e) / (built.1 : ℝ) ≤ LP.σ_mwu G.n) ∧
      (∀ j < built.1, ∀ u ∈ G.V, ∀ v ∈ G.V,
        G.Connected u v → (built.2 j).F.F.Connected u v) := by
  simp only [hi]
  intro himpl hL hP hLWord hPWord hFour hWidth hg hl hh hgraph hgraphEnd hlenEnd htable hst hpos hz hroom
  let G := (algorithm1_shift T tool P chain i).1.G P.d
  let ℓ := (algorithm1_shift T tool P chain i).1.toTreeChain.chainLen chain.ℓ P.d
  have hdecode : readEdgeValues st.mem lengths fmt.limbBits limbs fmt.precision G.E =
      fun e => if e ∈ G.E then ℓ e else 0 := by
    apply readEdgeValues_eq_of_support
    · exact htable.of_eqOn (fun e he => (ite_eq_left he).symm)
    · intro e he
      simp [he]
  obtain ⟨out, ret, cost, y, hr, hzBr, hhandle, hheap, hrep, hcollection, hframe, hcost⟩ :=
    rebuildLastLevelRuntime_tables_runs (ω := ω) himpl hg hl hh hL hP hLWord hPWord hFour hWidth _
      hgraph hgraphEnd hlenEnd htable hst hpos hz hroom
  dsimp only [G, ℓ] at hdecode
  rw [← hdecode] at hrep hcollection
  obtain ⟨hk, hholds, hstretch, hspan, _⟩ := lastLevelDecodedBuild_spec hspec hgraph.1 htable hpos
  exact ⟨out, ret, cost, y, hr, hzBr, hhandle, hheap, hrep, hcollection, hframe, hcost,
    hk, hholds, hstretch, hspan⟩

/-- If the next level of Shift is terminal, pass the free heap from the
restarted readouts straight to the terminal initializer (Algorithm 1, page 20). -/
@[expose] def shiftRebuildTerminal (restart read forestOp init : ℕ) : Stmt :=
  shiftRestartGraphAndLengths restart read forestOp ;;
    .assign 4 (.reg 5) ;; rebuildLastLevelRuntime init

/-- The terminal handoff preserves the graph and length registers and
adds four steps to the costs of the two runs. -/
theorem shiftRebuildTerminal_runs {w restart read forestOp init prefixCost : ℕ}
    {p : Program} {initial mid : State} {ω : ℕ → Bool} {Done : State → Prop}
    {budget : ℕ}
    (hp : Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      initial .normal mid prefixCost)
    (hbuild : ∃ out cost, Runs w p ω (rebuildLastLevelRuntime init)
      { mid with regs := Function.update mid.regs 4 (mid.regs 5) } .normal out cost ∧
      Done out ∧ cost ≤ budget) :
    ∃ out cost, Runs w p ω (shiftRebuildTerminal restart read forestOp init)
      initial .normal out cost ∧ Done out ∧ cost ≤ prefixCost + budget + 4 := by
  let ready := { mid with regs := Function.update mid.regs 4 (mid.regs 5) }
  have hset : Runs w p ω (.assign 4 (.reg 5)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  obtain ⟨out, c, hr, hd, hc⟩ := hbuild
  exact ⟨out, prefixCost + (2 + c + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, 2 + c + 1, hp,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hset, hr, rfl⟩), rfl⟩), hd, by omega⟩

/-- When the terminal length table has the model's off-edge support, Shift
represents the exact terminal collection after restarting the branch. -/
theorem shiftRebuildTerminal_exact_runs
    {w limbs restart read forestOp init vc ec multiplier stretchPrecision i prefixCost : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {tool : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (hi : i + 1 = P.d)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {initial mid : State} {ω : ℕ → Bool} :
    let next := (algorithm1_shift T tool P chain i).1
    let G := next.G P.d
    let ℓ := next.toTreeChain.chainLen chain.ℓ P.d
    let graph := mid.regs 6
    let lengths := mid.regs 7
    let heap := mid.regs 5
    Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      initial .normal mid prefixCost →
    R.Implements w p init op (lastLevelRuntimeMachineContract fmt limbs tool G vc ec multiplier stretchPrecision allocation) →
    mid.regs 67 = limbs → mid.regs 68 = fmt.precision →
    limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    DynSpanner.Program.DynGraphAt mid.mem graph vc ec G →
    graph + DynSpanner.Program.dynGraphSize vc ec ≤ heap → lengths + ec * limbs ≤ heap →
    EdgeValuesAt mid.mem lengths fmt.limbBits limbs fmt.precision G.E ℓ →
    (∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ G.E, 0 < ℓ e) → (∀ e ∉ G.E, ℓ e = 0) →
    ZeroFrom mid.mem heap → heap + allocation 1 [graph, lengths, limbs, fmt.precision, heap] < 2 ^ w →
    ∃ out ret cost y, Runs w p ω (shiftRebuildTerminal restart read forestOp init)
        initial .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap (next.lastK, next.lastLSFs) y out.mem ∧
      LSFCollectionAt out.mem heap vc ec fmt.limbBits limbs fmt.precision G.E
        (next.lastK, next.lastLSFs) ∧
      R.Respects (fun _ => False) heap (allocation 1 [graph, lengths, limbs, fmt.precision, heap])
        mid.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ prefixCost + multiplier * (tool.cost G + 1) + 16 := by
  dsimp only
  intro hp himpl hL hP hLWord hPWord hFour hWidth hg hgb hlb hl hst hpos hsupport hz hroom
  let ready := { mid with regs := Function.update mid.regs 4 (mid.regs 5) }
  have hset : Runs w p ω (.assign 4 (.reg 5)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  obtain ⟨out, ret, c, y, hr, hb, hhandle, hheap, hrep, hlsfs, hframe, hc⟩ :=
    shiftTerminalBuild_tables_runs (st := ready) (ω := ω) chain hi himpl
      (by simpa [ready] using hL) (by simpa [ready] using hP) hLWord hPWord hFour hWidth
      (by simp [ready, Function.update_of_ne]) (by simp [ready, Function.update_of_ne])
      (by simp [ready]) hg hgb hlb hl hst hpos hsupport hz hroom
  exact ⟨out, ret, prefixCost + (2 + c + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, 2 + c + 1, hp,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hset, hr, rfl⟩), rfl⟩),
    hb, hhandle, hheap, hrep, hlsfs, hframe, by omega⟩

private theorem shiftRebuildTerminal_preserves_descriptor_regs
    {w restart read forestOp init r cost : ℕ}
    {p : Program} {initial out : State} {ω : ℕ → Bool}
    (h : Runs w p ω (shiftRebuildTerminal restart read forestOp init)
      initial .normal out cost) (hr : 51 ≤ r) : out.regs r = initial.regs r := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hbad, _⟩ | ⟨mid, _, _, hp, ht, _⟩
  · cases hbad
  rcases runs_seq_iff.mp ht with ⟨_, _, _, hbad, _⟩ | ⟨ready, _, _, hset, hinit, _⟩
  · cases hbad
  rcases runs_seq_iff.mp hinit with ⟨_, _, _, hbad, _⟩ | ⟨first, _, _, hs, hrest, _⟩
  · cases hbad
  rcases runs_seq_iff.mp hrest with ⟨_, _, _, hbad, _⟩ | ⟨second, _, _, hc, ha, _⟩
  · cases hbad
  obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp hset
  obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp hs
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp hc
  obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp ha
  simpa [Function.update_of_ne (show r ≠ 2 by omega),
    Function.update_of_ne (show r ≠ 3 by omega), Function.update_of_ne (show r ≠ 4 by omega)]
    using shiftRestartGraphAndLengths_preserves_regs hr hp

/-- Record the new terminal collection's handle and first branch after
a Shift whose next level is terminal (Algorithm 1, page 20). -/
@[expose] def shiftInstallTerminal (restart read forestOp init : ℕ) : Stmt :=
  shiftRebuildTerminal restart read forestOp init ;; storeRebuiltLevel

/-- Installing the terminal descriptor retains the represented forest
collection and its potential and costs eight additional steps. -/
theorem shiftInstallTerminal_runs {w restart read forestOp init cost handleCell branchCell : ℕ}
    {R : DSRep (ℕ × (ℕ → LSF))} {built : ℕ × (ℕ → LSF)} {x : R.τ}
    {p : Program} {initial mid : State} {ω : ℕ → Bool}
    (hinit : Runs w p ω (shiftRebuildTerminal restart read forestOp init)
      initial .normal mid cost)
    (hlocal : R.Local) (hh : initial.regs 51 = handleCell) (hb : initial.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell)
    (hhBelow : handleCell < mid.regs 3) (hbBelow : branchCell < mid.regs 3)
    (hfoot : ∀ a, R.foot (mid.regs 3) x a → mid.regs 3 ≤ a)
    (hrep : R.rep (mid.regs 3) built x mid.mem) :
    ∃ out, Runs w p ω (shiftInstallTerminal restart read forestOp init)
        initial .normal out (cost + 8) ∧
      out.mem handleCell = out.regs 3 ∧ out.mem branchCell = 0 ∧
      R.rep (out.regs 3) built x out.mem ∧
      R.phi (out.regs 3) x out.mem = R.phi (mid.regs 3) x mid.mem ∧
      (∀ a, a ≠ handleCell → a ≠ branchCell → out.mem a = mid.mem a) ∧
      out.regs = mid.regs := by
  have hhMid := (shiftRebuildTerminal_preserves_descriptor_regs hinit (by decide : 51 ≤ 51)).trans hh
  have hbMid := (shiftRebuildTerminal_preserves_descriptor_regs hinit (by decide : 51 ≤ 52)).trans hb
  obtain ⟨out, hr, hh', hb', hrep', hphi, hframe, hregs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) hlocal hhMid hbMid hne hhBelow hbBelow hfoot hrep
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 7, hinit, hr, by omega⟩),
    hh', hb', hrep', hphi, hframe, hregs⟩

/-- The terminal installation preserves saved counter arguments. -/
theorem shiftInstallTerminal_preserves_regs {w restart read forestOp init cost r : ℕ}
    {p : Program} {initial out : State} {ω : ℕ → Bool}
    (h : Runs w p ω (shiftInstallTerminal restart read forestOp init)
      initial .normal out cost) (hr : 51 ≤ r) : out.regs r = initial.regs r := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hbad, _⟩ | ⟨mid, _, _, hi, hs, _⟩
  · cases hbad
  rcases runs_seq_iff.mp hs with ⟨_, _, _, hbad, _⟩ | ⟨first, _, _, h₁, h₂, _⟩
  · cases hbad
  obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h₁
  obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h₂
  exact shiftRebuildTerminal_preserves_descriptor_regs (out := mid) hi hr

/-- Install the exact model terminal collection after Shift when the
length support and descriptor separation conditions hold. -/
theorem shiftInstallTerminal_exact_runs
    {w limbs restart read forestOp init vc ec multiplier stretchPrecision i prefixCost handleCell branchCell : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {tool : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (hi : i + 1 = P.d)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {initial mid : State} {ω : ℕ → Bool} :
    let next := (algorithm1_shift T tool P chain i).1
    let G := next.G P.d
    let ℓ := next.toTreeChain.chainLen chain.ℓ P.d
    let graph := mid.regs 6
    let lengths := mid.regs 7
    let heap := mid.regs 5
    Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      initial .normal mid prefixCost →
    R.Implements w p init op (lastLevelRuntimeMachineContract fmt limbs tool G vc ec multiplier stretchPrecision allocation) →
    mid.regs 67 = limbs → mid.regs 68 = fmt.precision →
    limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    DynSpanner.Program.DynGraphAt mid.mem graph vc ec G →
    graph + DynSpanner.Program.dynGraphSize vc ec ≤ heap → lengths + ec * limbs ≤ heap →
    EdgeValuesAt mid.mem lengths fmt.limbBits limbs fmt.precision G.E ℓ →
    (∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ G.E, 0 < ℓ e) → (∀ e ∉ G.E, ℓ e = 0) →
    ZeroFrom mid.mem heap → heap + allocation 1 [graph, lengths, limbs, fmt.precision, heap] < 2 ^ w →
    initial.regs 51 = handleCell → initial.regs 52 = branchCell →
    handleCell ≠ branchCell → handleCell < heap → branchCell < heap →
    ∃ out ret cost y, Runs w p ω (shiftInstallTerminal restart read forestOp init)
        initial .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 4 = ret ∧ R.rep heap (next.lastK, next.lastLSFs) y out.mem ∧
      ZeroFrom out.mem ret ∧
      (∀ a, R.foot heap y a → heap ≤ a ∧ a < ret) ∧
      cost + R.phi heap y out.mem ≤ prefixCost + multiplier * (tool.cost G + 1) + 24 := by
  dsimp only
  intro hp himpl hL hP hLWord hPWord hFour hWidth hg hgb hlb hl hst hpos hsupport hz hroom hh hb hne hhBelow hbBelow
  obtain ⟨built, ret, c, y, hr, _, hhandle, hret, hrep, _, hframe, hc⟩ :=
    shiftRebuildTerminal_exact_runs chain hi hp himpl hL hP hLWord hPWord hFour hWidth hg hgb hlb hl hst hpos hsupport hz hroom
  have hfoot (a : ℕ) (ha : R.foot (mid.regs 5) y a) : mid.regs 5 ≤ a ∧ a < ret :=
    (hframe.2.2.2.2 a ha).resolve_left id
  obtain ⟨out, ho, hh', hb', hrep', hphi, hmem, hregs⟩ :=
    shiftInstallTerminal_runs hr himpl.1 hh hb hne (hhandle.symm ▸ hhBelow)
      (hhandle.symm ▸ hbBelow) (fun a ha => hhandle.symm ▸ (hfoot a (hhandle ▸ ha)).1)
      (hhandle.symm ▸ hrep)
  have houtHandle : out.regs 3 = mid.regs 5 := hregs ▸ hhandle
  have houtPhi : R.phi (mid.regs 5) y out.mem = R.phi (mid.regs 5) y built.mem := by
    simpa only [houtHandle, hhandle] using hphi
  refine ⟨out, ret, c + 8, y, ho, hh'.trans houtHandle, hb', hregs ▸ hret, houtHandle ▸ hrep',
    ?_, hfoot, ?_⟩
  · intro a ha
    have hlo := hframe.1
    exact (hmem a (by omega) (by omega)).trans (hframe.2.2.1 a ha)
  · rw [houtPhi]
    omega

end MinCostFlow.MinRatio
