module

public import MinCostFlow.MinRatio.DetectRound

/-!
# Entering the Detect reporting loop

Definition 4.5 (page 14) returns a contiguous list. Before the
search from Theorem 5.1 (pages 29–30), reserve a header and a cell
for each live edge. The report starts empty and tree allocation
begins above the reserved block.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut IPM.Machine

/-- Register 17 holds the output header, and register 18 holds the
live edge count. Begin at the first report cell. -/
@[expose] def detectStart : Stmt :=
  .assign 8 (.bin .add (.reg 17) (.const 1)) ;;
  .assign 1 (.bin .add (.reg 8) (.reg 18))

/-- The initial reservation and cursor setup are deterministic. -/
theorem detectStart_noRand : detectStart.NoRand := by
  simp [detectStart, Stmt.NoRand]

/-- Reserve the report at the incoming heap without writing to the
tree or lookup tables. This establishes the empty-prefix invariant. -/
theorem detectStart_runs {cfg : Alg2Config} {model : Alg2State cfg}
    {w handle base names inv table h L P : ℕ}
    {R : DSRep PathTreeState} {p : Program} {ω : ℕ → Bool}
    {st : State} {tree : PathTreeState} {token : R.τ}
    {trees : List AuxTree} {free : List ℕ} {depth slotOf internalOf thresholdOf : ℕ → ℕ}
    (hbase : st.regs 17 = base) (hcount : st.regs 18 = model.extG.E.card)
    (hroom : base + 1 + model.extG.E.card < 2 ^ w)
    (hz : ZeroFrom st.mem base) (hrep : R.rep handle tree token st.mem)
    (hfoot : ∀ a, R.foot handle token a → a < base)
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf ∅ tree trees)
    (hc : ∀ slot, pathTreeReady tree slot → ∃ e ∈ model.extG.E, slotOf e = slot)
    (ht : DetectTablesAt model st.mem names inv table h L P slotOf internalOf thresholdOf)
    (hbelow : ∀ e ∈ model.extG.E, ∀ a,
      (a = names + slotOf e ∨ a = inv + internalOf e ∨ a = table + slotOf e ∨
        (thresholdOf e ≤ a ∧ a < thresholdOf e + L)) → a < base ∧ ¬ R.foot handle token a) :
    ∃ out, Runs w p ω detectStart st .normal out 9 ∧ out.mem = st.mem ∧
      out.regs 1 = base + 1 + model.extG.E.card ∧
      (∀ r, r ≠ 1 → r ≠ 8 → out.regs r = st.regs r) ∧
      ∃ I : DetectLoopState model R handle base names inv table h L P slotOf internalOf thresholdOf out,
        I.tree = tree ∧ I.token = token ∧ I.written = [] := by
  let mid := { st with regs := Function.update st.regs 8 (base + 1) }
  let out := { mid with regs := Function.update mid.regs 1 (base + 1 + model.extG.E.card) }
  have hfirst : Runs w p ω (.assign 8 (.bin .add (.reg 17) (.const 1))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hbase, show 1 < 2 ^ w by omega,
      show base + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 1 (.bin .add (.reg 8) (.reg 18))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, Function.update_of_ne, hcount, hroom],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hfirst, hsecond, rfl⟩), rfl, by simp [out], ?_, ?_⟩
  · intro r h1 h8
    simp [out, mid, Function.update_of_ne, h1, h8]
  let I : DetectLoopState model R handle base names inv table h L P
      slotOf internalOf thresholdOf out :=
    { tree := tree
      token := token
      trees := trees
      free := free
      depth := depth
      written := []
      treeRep := hrep
      forestInv := hi
      accounts := by simpa using ha
      coverage := hc
      nodup := List.nodup_nil
      subset := by simp
      prefixAt := fun _ hn => False.elim (Nat.not_lt_zero _ hn)
      cursor := by simp [out, mid, Function.update_of_ne]
      reserve := by simp [out]
      zero := by
        intro a he
        apply hz
        have hb : out.regs 1 = base + 1 + model.extG.E.card := by simp [out]
        omega
      treeBound := by
        intro a he
        have hb := hfoot a he
        simp [out]
        omega
      bufferDisjoint := fun a hb _ he => (Nat.not_lt_of_ge hb) (hfoot a he)
      tables := ht
      tableDisjoint := hbelow }
  exact ⟨I, rfl, rfl, rfl⟩

/-- Detect reserves its answer and then runs the reporting loop. -/
@[expose] def detectProgram (find read report finish : ℕ) : Stmt :=
  detectStart ;; detectLoopProgram find read report finish

/-- The reservation and reporting loop contain no random instructions. -/
theorem detectProgram_noRand (find read report finish : ℕ) :
    (detectProgram find read report finish).NoRand := by
  simp [detectProgram, Stmt.NoRand, detectStart_noRand, detectLoopProgram_noRand]

/-- The entry sequence adds ten steps to the verified reporting loop. -/
theorem detectProgram_runs_of_loop {w find read report finish heap cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st start out : State}
    (hstart : Runs w p ω detectStart st .normal start 9)
    (hloop : Runs w p ω (detectLoopProgram find read report finish) start (.returned heap) out cost) :
    Runs w p ω (detectProgram find read report finish) st (.returned heap) out (9 + cost + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨start, 9, cost, hstart, hloop, rfl⟩)

/-- From an empty report, Detect returns exactly the model report
and charges a ready round for every reported edge. -/
theorem detectProgram_runs {cfg : Alg2Config} {model : Alg2State cfg}
    {w constant init handle base names inv table searchSpace readSpace writeSpace prepare entry finish m : ℕ}
    (F : MinRatioFormat w) {G : MGraph} {κ α : ℝ}
    {rate : ℕ → ℕ} {outerSpace : ℕ → List ℕ → ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {R : DSRep PathTreeState}
    {allocation : ℕ → ℕ → List ℕ → ℕ}
    {op slotOf internalOf thresholdOf : ℕ → ℕ}
    {tree : PathTreeState} {token : R.τ}
    {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (hcount : st.regs 18 = model.extG.E.card)
    (hroom : base + 1 + model.extG.E.card < 2 ^ w)
    (hz : ZeroFrom st.mem base) (hrep : R.rep handle tree token st.mem)
    (hfoot : ∀ a, R.foot handle token a → a < base)
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model F.fmt.precision slotOf ∅ tree trees)
    (hc : ∀ slot, pathTreeReady tree slot → ∃ e ∈ model.extG.E, slotOf e = slot)
    (ht : DetectTablesAt model st.mem names inv table F.fmt.limbBits F.limbs F.fmt.precision
      slotOf internalOf thresholdOf)
    (hbelow : ∀ e ∈ model.extG.E, ∀ a,
      (a = names + slotOf e ∨ a = inv + internalOf e ∨ a = table + slotOf e ∨
        (thresholdOf e ≤ a ∧ a < thresholdOf e + F.limbs)) →
      a < base ∧ ¬ R.foot handle token a)
    (himpl : R.Implements w p init op (pathTreeMachineContract F.fmt F.limbs constant allocation))
    (h0 : st.regs 0 = handle) (h6 : st.regs 6 = names) (h7 : st.regs 7 = inv)
    (h10 : st.regs 10 = F.limbs) (h14 : st.regs 14 = table) (h17 : st.regs 17 = base)
    (h15 : st.regs 15 = searchSpace) (h16 : st.regs 16 = readSpace)
    (hh : handle < 2 ^ w) (hthree : 3 < 2 ^ w)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hwords : ∀ e ∈ model.extG.E, e < 2 ^ w)
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs
      F.fmt.precision model)
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    {reset lookup emit slotReport copy negate header : ℕ}
    (hprepareCode : p.HasAt prepare [detectSlotStepBody reset slotReport])
    (hresetCode : p.HasAt reset [detectResetBody copy negate])
    (hcopyCode : p.HasAt copy [copyWords])
    (hnegateCode : p.HasAt negate (Num.negateModule negate F.fmt.limbBits))
    (hlimbWord : Num.base F.fmt.limbBits < 2 ^ w)
    (hreportCode : p.HasAt slotReport [detectSlotReportBody lookup emit])
    (hlookupCode : p.HasAt lookup [freshLookupBody])
    (hemitCode : p.HasAt emit [detectEmitBody])
    (hfinishCode : p.HasAt finish [detectFinishKeepHeapBody header])
    (hheaderCode : p.HasAt header [detectFinishBody])
    (hedge : ∀ e ∈ model.extG.E, isEdgeSlot tree.n (slotOf e))
    (htreeWord : 2 * tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tree.n + 1) ≤ F.fmt.limbBits * F.limbs)
    (hcapacity : base + 1 + model.extG.E.card + (algorithm2_detect cfg model).1.card *
      (searchSpace + readSpace + (2 + 4 * F.limbs) + writeSpace) + searchSpace + readSpace < 2 ^ w)
    (hbounds : ∀ current (J : DetectLoopState model R handle base names inv table
      F.fmt.limbBits F.limbs F.fmt.precision slotOf internalOf thresholdOf current),
      J.tree.n = tree.n →
      (pathTreeFits F.fmt.limbBits F.limbs J.tree) ∧
      (allocation 6 J.tree.n [handle, current.regs 1] ≤ searchSpace) ∧
      (2 + 4 * F.limbs ≤ readSpace) ∧
      (∀ slot, pathTreeReady J.tree slot →
      pathTreeFits F.fmt.limbBits F.limbs (lctExpose pathPayload J.tree slot) ∧
      pathTreeFits F.fmt.limbBits F.limbs (lctExpose pathPayload (lctExpose pathPayload J.tree slot) slot) ∧
      allocation 4 J.tree.n [handle, slot, current.regs 1 + searchSpace] ≤ readSpace) ∧
      (∀ slot value e, e ∈ model.extG.E → slotOf e = slot →
      ((lctExpose pathPayload J.tree slot).splay.nodes slot).val = some value →
      pathTreeFits F.fmt.limbBits F.limbs
        (pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload J.tree slot) slot)
          slot (some { value with detector := -detectorThreshold F.fmt.precision cfg.ε (model.extℓ e) }))) ∧
      (∀ slot,
      let heap := current.regs 1 + searchSpace + readSpace
      allocation 5 J.tree.n [handle, slot, heap, heap + (2 + 4 * F.limbs)] ≤ writeSpace)) :
    let budget := pathTreeBudget constant F.limbs tree.n
    ∃ heap out cost finalTree finalTrees y,
      Runs w p ω (detectProgram (op 6) (op 4) entry finish) st (.returned heap) out cost ∧
      (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate outerSpace).post
        2 model [handle, base] st.mem (algorithm2_detect cfg model).2 out.mem ∧
      DetectForestAccounts (algorithm2_detect cfg model).2 F.fmt.precision slotOf ∅ finalTree finalTrees ∧
      R.rep handle finalTree y out.mem ∧
      R.Respects (R.foot handle token) base
        (1 + model.extG.E.card + (algorithm2_detect cfg model).1.card *
          (searchSpace + readSpace + (2 + 4 * F.limbs) + writeSpace) + searchSpace)
        st.mem heap handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        ((algorithm2_detect cfg model).1).card *
          (3 * budget + 87 * F.limbs + 218) + 2 * budget + 66 + R.phi handle token st.mem := by
  dsimp only
  obtain ⟨start, hs, hmem, hheap, hregs, I, hn, htok, hnil⟩ :=
    detectStart_runs (p := p) (ω := ω) h17 hcount hroom hz hrep hfoot hi ha hc ht hbelow
  have hw : 1 < 2 ^ w := (by decide : 1 < 3).trans hthree
  have hprepare (written : List ℕ) (value : PathEdgeValue) (threshold : ℤ) :
      MeetsContract w p prepare
        (detectSlotStepContract w F.fmt.limbBits (base + 1) written value threshold) :=
    detectSlotStep_meetsContract written value threshold hprepareCode
      (detectReset_meetsContract value threshold hresetCode (copyWords_meetsContract hcopyCode)
        (Num.negate_meetsContract hw hlimbWord hnegateCode))
      (fun _ => detectSlotReport_meetsContract written hreportCode
        (freshLookup_meetsContract hlookupCode) (detectEmitReserved_meetsContract written hemitCode))
  have hfinish (written : List ℕ) (heap : ℕ) :
      MeetsContract w p finish (detectFinishKeepHeapContract w heap written) :=
    detectFinishKeepHeap_meetsContract written hfinishCode
      (detectFinishReserved_meetsContract written hheaderCode)
  obtain ⟨heap, out, cost, finalTree, finalTrees, y, hrun, hm, hacc, hrep', hz', hframe, hfoot', hlow, htreeEnd, hupper, hcost⟩ :=
    I.loop_runs (ω := ω) (m := m) (κ := κ) (α := α) (rate := rate) (outerSpace := outerSpace)
      F hw himpl
      ((hregs 0 (by decide) (by decide)).trans h0)
      ((hregs 6 (by decide) (by decide)).trans h6)
      ((hregs 7 (by decide) (by decide)).trans h7)
      ((hregs 10 (by decide) (by decide)).trans h10)
      ((hregs 14 (by decide) (by decide)).trans h14)
      ((hregs 17 (by decide) (by decide)).trans h17)
      ((hregs 15 (by decide) (by decide)).trans h15)
      ((hregs 16 (by decide) (by decide)).trans h16)
      hh hthree hinj heps hlen hwords hfit hentry hprepare hfinish (by rwa [hn])
      (by rwa [hn]) (by rwa [hn])
      (by simpa only [hheap, hnil, List.toFinset_nil, Finset.sdiff_empty] using hcapacity)
      (fun current J hJ => hbounds current J (hJ.trans (congrArg (fun t : PathTreeState => t.n) hn)))
  refine ⟨heap, out, 9 + cost + 1, finalTree, finalTrees, y,
    detectProgram_runs_of_loop hs hrun, hmem ▸ hm, hacc, hrep', ?_, ?_⟩
  · refine ⟨hlow, ?_, hz', ?_, ?_⟩
    · simpa only [hheap, hnil, List.toFinset_nil, Finset.sdiff_empty, Nat.add_assoc] using hupper
    · simpa only [htok, hmem] using hframe
    · intro a ha
      by_cases hb : a < base
      · exact Or.inl (htok ▸ hfoot' a ha hb)
      · exact Or.inr ⟨Nat.le_of_not_gt hb, htreeEnd a ha⟩
  · simp only [hn, htok, hmem, hnil, List.toFinset_nil, Finset.sdiff_empty] at hcost
    omega

/-- The Detect budget from Theorem 5.1 (pages 29–30) charges
one final search and at most three tree calls per reported edge.
A single coefficient therefore bounds the IPM rate per report,
including the empty report. -/
theorem detectCost_le_rate (budget limbs reports rate : ℕ)
    (hrate : 3 * budget + 87 * limbs + 218 ≤ rate) :
    reports * (3 * budget + 87 * limbs + 218) + 2 * budget + 66 ≤ rate * (1 + reports) := by
  have hfinal : 2 * budget + 66 ≤ rate := by omega
  calc
    reports * (3 * budget + 87 * limbs + 218) + 2 * budget + 66 ≤ reports * rate + rate := by
      rw [Nat.add_assoc]
      exact Nat.add_le_add (Nat.mul_le_mul_left reports hrate) hfinal
    _ = rate * (1 + reports) := by simp only [Nat.mul_add, Nat.mul_one, Nat.mul_comm rate reports]; exact Nat.add_comm _ _

/-- An allocation bound using the count of live edges suffices for
Detect, since the report is a subset of those edges. -/
theorem detectSpace_le_live {cfg : Alg2Config} (model : Alg2State cfg)
    (roundSpace finalSpace : ℕ) :
    1 + model.extG.E.card + (algorithm2_detect cfg model).1.card * roundSpace + finalSpace ≤
      1 + model.extG.E.card + model.extG.E.card * roundSpace + finalSpace := by
  have hsub : (algorithm2_detect cfg model).1 ⊆ model.extG.E := Finset.filter_subset _ _
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_right roundSpace (Finset.card_le_card hsub)) _) _

end MinCostFlow.MinRatio
