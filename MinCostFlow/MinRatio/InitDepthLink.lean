module

public import MinCostFlow.MinRatio.InitDepthEndpoint
public import MinCostFlow.MinRatio.InitThresholdDyadic
public import MinCostFlow.MinRatio.InitSolverDimensions
import MinCostFlow.Num.ModulePlacement

/-!
# Linked depth procedures

The chain and sparsifier share a fixed block for computing and rounding
logarithms, counting bits, and selecting the number of chain branches.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Num

/-- The depth procedures occupy fixed offsets from the start of the block. -/
@[expose] def initDepthProcedures (b h : ℕ) : List Stmt :=
  (Num.IPM.bitLengthModule b ++ loadSmallModule (b + 1) h ++
    initDepthEndpointModule (b + 2) h ++ [minRatioBranchCountBody]) ++
    logarithmModule (b + 6) h

/-- All procedures in the depth block are deterministic. -/
theorem initDepthProcedures_noRand (b h : ℕ) :
    ∀ s ∈ initDepthProcedures b h, s.NoRand := by
  intro s hs
  simp only [initDepthProcedures, List.mem_append] at hs
  rcases hs with ((((hbits | hload) | hround) | hbranch) | hlog)
  · exact Num.IPM.bitLengthModule_noRand b s hbits
  · simp only [loadSmallModule, List.mem_singleton] at hload
    subst s
    exact loadSmallBody_noRand _ _
  · simp only [initDepthEndpointModule, List.mem_cons, List.not_mem_nil, or_false] at hround
    rcases hround with rfl | rfl | rfl
    · simp [initDepthEndpointBody, Stmt.NoRand]
    · exact packWordBody_noRand _ _
    · exact isZeroBody_noRand _
  · simp only [List.mem_singleton] at hbranch
    subst s
    simp [minRatioBranchCountBody, selectMinRatioBranchCount, branchSearchStep,
      branchPowerCapped, multiplyBranchPowerCapped, forRange, forUp, Stmt.NoRand]
  · exact logarithmModule_noRand _ _ s hlog

/-- The fixed depth block supplies the numeric contracts for both depth
formulas at any working accuracy. -/
theorem initDepthProcedures_meetsContracts {w b h : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hp : p.HasAt b (initDepthProcedures b h)) :
    MeetsContract w p b Num.IPM.bitLengthContract ∧
      MeetsContract w p (b + 1) (loadSmallContract w h) ∧
      MeetsContract w p (b + 2) (initDepthEndpointContract w h) ∧
      MeetsContract w p (b + 5) (minRatioBranchCountContract w) ∧
      ∀ q, MeetsContract w p (b + 6) (logarithmContract w h q) := by
  have htwo : 2 < 2 ^ w := by
    simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
      (show 1 < w by omega)
  have hbase : base h < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  unfold initDepthProcedures at hp
  have hhead := hasAt_append_left hp
  have hlog : p.HasAt (b + 6) (logarithmModule (b + 6) h) := hasAt_append_right hp
  have hround : p.HasAt (b + 2) (initDepthEndpointModule (b + 2) h) :=
    hasAt_append_right (hasAt_append_left hhead)
  have hbits : p.HasAt b (Num.IPM.bitLengthModule b) :=
    hasAt_append_left (hasAt_append_left (hasAt_append_left hhead))
  have hload : p.HasAt (b + 1) (loadSmallModule (b + 1) h) :=
    hasAt_append_right (hasAt_append_left (hasAt_append_left hhead))
  have hbranch : p.HasAt (b + 5) [minRatioBranchCountBody] := hasAt_append_right hhead
  exact ⟨Num.IPM.bitLength_meetsContract htwo hbits,
    loadSmall_meetsContract (by omega) hbase hload,
    initDepthEndpointModule_meetsContract (by omega) hbase hround,
    minRatioBranchCount_meetsContract hbranch.head,
    fun _ => logarithm_meetsContract hh hw hlog⟩

/-- The solver Init entry uses the fixed offsets of the linked depth block.
Its remaining call targets are the solver and level construction procedures. -/
@[expose] def solverInitWithLinkedDepth
    (b h alpha select quality graphPack threshold lower upper denominator power
      factorEntry decK thr cDeg coefficient witnessDen : ℕ)
    (retry levels inconclusive : Stmt) : Stmt :=
  solverInitWithMultiwordDepth alpha select quality graphPack threshold (b + 5)
    lower upper denominator power b (b + 1) (b + 6) (b + 3) (b + 2) h
    factorEntry decK thr cDeg coefficient witnessDen retry levels inconclusive

/-- The packer used by bucket and threshold initialization is the same
read-only word conversion used by depth endpoint rounding. -/
theorem initDepthProcedures_packer_meetsContract {w b h : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hp : p.HasAt b (initDepthProcedures b h)) :
    MeetsContract w p (b + 3) (packWordContract w h) := by
  have hbase : base h < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have htwo : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  unfold initDepthProcedures at hp
  have hround : p.HasAt (b + 2) (initDepthEndpointModule (b + 2) h) :=
    hasAt_append_right (hasAt_append_left (hasAt_append_left hp))
  have hpack : p.HasAt (b + 3) (packWordModule (b + 3) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [initDepthEndpointModule, packWordModule, Nat.add_assoc] using
      hround 1 (by simp [initDepthEndpointModule])
  exact packWord_meetsContract htwo hbase hpack

/-- The linked depth block supplies the contracts for this solver depth stage. -/
theorem prepareSolverChainWithLinkedDepth_runs
    {w threshold b h a : ℕ} (I : Instance)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hw : 3 * h + 2 ≤ w) (hlink : p.HasAt b (initDepthProcedures b h))
    (hm : st.regs 0 = (IPM.namedInstance I).m)
    (hh : 0 < h) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a)
    (hM : 1 ≤ max I.m threshold) (hMw : max I.m threshold + 2 < 2 ^ w) :
    let M := max I.m threshold
    let E := (M + 2).size
    let q := 38 * (2 ^ 48 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let C := Chain.concreteChainParams M hM
    a + L + L + Num.logarithmSpace L P E < 2 ^ w →
    ∃ out cost ret, Runs w p ω (prepareSolverChainWithDepthWorkspace threshold b (b + 1) (b + 6) (b + 2) h (b + 5) retry)
        st .normal out cost ∧ out.regs 22 = M ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 22 → r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 537 := by
  dsimp only
  intro hroom
  obtain ⟨hbits, hload, hround, hbranch, hlog⟩ := initDepthProcedures_meetsContracts hh hw hlink
  have hhw : h < 2 ^ w := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)) (n := w)).trans_le' (by omega)
  exact prepareSolverChainWithDepthWorkspace_runs I hbits hload hround hbranch hm hh hhw ha hz
    hM hMw (hlog _) hroom

/-- The linked depth block supplies the contracts for this solver depth stage. -/
theorem prepareSolverSparseCoreWithLinkedDepth_runs
    {w h b a M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hw : 3 * h + 2 ≤ w) (hlink : p.HasAt b (initDepthProcedures b h))
    (hm : st.regs 22 = M) (hM : 1 ≤ M) (hMw : M ^ 2 + 2 < 2 ^ w)
    (hh : 0 < h) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a) :
    let E := (M ^ 2 + 2).size
    let q := 38 * (2 ^ 24 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let depth := Expander.chosenL (M ^ 2)
    a + L + L + Num.logarithmSpace L P E < 2 ^ w →
    ∃ out cost ret, Runs w p ω (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry)
        st .normal out cost ∧ out.regs 23 = M ^ 2 ∧ out.regs 44 = depth ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 23 → r ≠ 44 → out.regs r = st.regs r) ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E + 166 * (depth - 1) + 368 := by
  dsimp only
  intro hroom
  obtain ⟨hbits, hload, hround, _, hlog⟩ := initDepthProcedures_meetsContracts hh hw hlink
  have hhw : h < 2 ^ w := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)) (n := w)).trans_le' (by omega)
  exact prepareSolverSparseCoreWithDepthWorkspace_runs hbits hload hround hm hM hMw hh hhw ha hz
    (hlog _) hroom

/-- The linked depth stage fits the word size of the encoded circulation. -/
theorem prepareSolverChainWithLinkedDepth_wordSize_runs
    {threshold b h a cursorDegree c : ℕ} (J : Scaling.Circulation)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hw : 3 * h + 2 ≤ wordSize c J.solverWords) (hlink : p.HasAt b (initDepthProcedures b h))
    (hm : st.regs 0 = (IPM.namedInstance (IPM.Machine.solverConnectedAugmented J)).m)
    (hh : 0 < h) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a)
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold) :
    let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let d := max 2 (Nat.clog 2 threshold + 1)
    let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    a ≤ base ^ cursorDegree →
    max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c →
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let E := (M + 2).size
    let q := 38 * (2 ^ 48 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let C := Chain.concreteChainParams M hM
    ∃ out cost ret, Runs (wordSize c J.solverWords) p ω (prepareSolverChainWithDepthWorkspace threshold b (b + 1) (b + 6) (b + 2) h (b + 5) retry)
        st .normal out cost ∧ out.regs 22 = M ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ wordSize c J.solverWords ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 22 → r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 537 := by
  dsimp only
  intro hcursor hdegree
  obtain ⟨hmw, _, _, hchain, _⟩ :=
    solverDepthWordSize_bounds J (threshold := threshold) (h := h) (a := a) (b := a)
      hcursor hcursor (by simpa only [max_self] using hdegree)
  exact prepareSolverChainWithLinkedDepth_runs (IPM.Machine.solverConnectedAugmented J)
    hw hlink hm hh ha hz hM hmw hchain

/-- The linked depth stage fits the word size of the encoded circulation. -/
theorem prepareSolverSparseCoreWithLinkedDepth_wordSize_runs
    {threshold h b a cursorDegree c : ℕ} (J : Scaling.Circulation)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hw : 3 * h + 2 ≤ wordSize c J.solverWords) (hlink : p.HasAt b (initDepthProcedures b h))
    (hm : st.regs 22 = max (IPM.Machine.solverConnectedAugmented J).m threshold) (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hh : 0 < h) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a) :
    let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let d := max 2 (Nat.clog 2 threshold + 1)
    let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    a ≤ base ^ cursorDegree →
    max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c →
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let E := (M ^ 2 + 2).size
    let q := 38 * (2 ^ 24 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let depth := Expander.chosenL (M ^ 2)
    ∃ out cost ret, Runs (wordSize c J.solverWords) p ω (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry)
        st .normal out cost ∧ out.regs 23 = M ^ 2 ∧ out.regs 44 = depth ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ wordSize c J.solverWords ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 23 → r ≠ 44 → out.regs r = st.regs r) ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E + 166 * (depth - 1) + 368 := by
  dsimp only
  intro hcursor hdegree
  obtain ⟨_, hsw, _, _, hsparse⟩ :=
    solverDepthWordSize_bounds J (threshold := threshold) (h := h) (a := a) (b := a)
      hcursor hcursor (by simpa only [max_self] using hdegree)
  exact prepareSolverSparseCoreWithLinkedDepth_runs hw hlink hm hM hsw hh ha hz hsparse

/-- At the encoded solver word size, the linked chain stage and bucket
input preparation leave the model dimensions and the fresh heap ready
for the bucket calculation. -/
theorem prepareLinkedDepthBucketInputs_runs
    {threshold b h a cursorDegree c precision alphaPtr V limbs : ℕ} (J : Scaling.Circulation)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hw : 3 * h + 2 ≤ wordSize c J.solverWords)
    (hlink : p.HasAt b (initDepthProcedures b h)) (hh : 0 < h)
    (hm : st.regs 0 = (IPM.namedInstance (IPM.Machine.solverConnectedAugmented J)).m)
    (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a)
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hptr : st.regs 4 = alphaPtr)
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hp : st.regs 3 = precision) :
    let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let d := max 2 (Nat.clog 2 threshold + 1)
    let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    a ≤ base ^ cursorDegree →
    max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c →
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let C := Chain.concreteChainParams M hM
    let E := (M + 2).size
    let P := h * (38 * (2 ^ 48 * E) ^ 8 + E + E + 10)
    let L := P + E + 4
    ∃ out cost ret, Runs (wordSize c J.solverWords) p ω
        (prepareSolverChainWithDepthWorkspace threshold b (b + 1) (b + 6) (b + 2) h (b + 5) retry ;;
          stageCertifiedInitUnitScale ;; saveSolverInitArguments) st .normal out cost ∧
      out.regs 22 = M ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧
      out.regs 4 = 1 ∧ out.regs 101 = alphaPtr ∧ out.regs 102 = V ∧
      out.regs 103 = limbs ∧ out.regs 104 = precision ∧ out.regs 98 = ret ∧
      a ≤ ret ∧ ret < 2 ^ wordSize c J.solverWords ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧ ZeroFrom out.mem ret ∧
      (∀ x < a, out.mem x = st.mem x) ∧
      (∀ r < 98, r ≠ 4 → r ≠ 22 → r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 554 ∧
      cost ≤ 100915 * (h * (38 * (2 ^ 48) ^ 8 + 12) + 5) ^ 3 * E ^ 24 := by
  dsimp only
  intro hcursor hdegree
  obtain ⟨chain, cost, ret, hr, h22, hd, hk, h98, hlo, hhi, hroomRet, hm', hz', hf, hcost⟩ :=
    prepareSolverChainWithLinkedDepth_wordSize_runs J hw hlink hm hh ha hz hM hcursor hdegree
  have hw' : 1 < 2 ^ wordSize c J.solverWords := Nat.one_lt_two_pow (by omega)
  obtain ⟨scaled, hs, hOne, hAlpha, hsmem, hsk⟩ := stageCertifiedInitUnitScale_runs
    (w := wordSize c J.solverWords) (p := p) (ω := ω)
    ((hf 4 (by decide) (by decide) (by decide) (by decide)).trans hptr) hw'
  have keep (r : ℕ) (h₁ : r ≠ 4 := by decide) (h₂ : r ≠ 101 := by decide) :=
    hsk r h₁ h₂
  obtain ⟨out, ht, h102, h103, h104, hout, htm⟩ := saveSolverInitArguments_runs
    (w := wordSize c J.solverWords) (p := p) (ω := ω)
    ((keep 1).trans ((hf 1 (by decide) (by decide) (by decide) (by decide)).trans hV))
    ((keep 2).trans ((hf 2 (by decide) (by decide) (by decide) (by decide)).trans hL))
    ((keep 3).trans ((hf 3 (by decide) (by decide) (by decide) (by decide)).trans hp))
  have hmem := htm.trans hsmem
  have hkeep (r : ℕ) (h₁ : r ≠ 4) (h₂ : r < 101) : out.regs r = chain.regs r :=
    (hout r (by omega) (by omega) (by omega)).trans (keep r h₁ (by omega))
  have h4 := (hout 4 (by decide) (by decide) (by decide)).trans hOne
  have h101 := (hout 101 (by decide) (by decide) (by decide)).trans hAlpha
  have hheap := (hkeep 98 (by decide) (by decide)).trans h98
  have hzero : ZeroFrom out.mem ret := hmem.symm ▸ hz'
  have hr' := runs_seq_iff.mpr (Or.inr ⟨chain, cost, 14, hr,
    runs_seq_iff.mpr (Or.inr ⟨scaled, 5, 8, hs, ht, rfl⟩), rfl⟩)
  have hE : 1 ≤ (max (IPM.Machine.solverConnectedAugmented J).m threshold + 2).size :=
    Nat.lt_size.mpr (by norm_num)
  have hpoly := initDepthLog_runtime_cost_with_scan (h := h) (exponent := 48) hE
    (initRuntimeChainDepth_scanCost_le hM)

  exact ⟨out, cost + 15, ret, hr', (hkeep 22 (by decide) (by decide)).trans h22,
    (hkeep 75 (by decide) (by decide)).trans hd, (hkeep 76 (by decide) (by decide)).trans hk,
    h4, h101, h102, h103, h104, hheap, hlo, hhi, hroomRet, hzero,
    fun x hx => (congrFun hmem x).trans (hm' x hx),
    fun r hr h4' h22' hd' hk' => (hkeep r h4' (by omega)).trans (hf r hr h22' hd' hk'), by omega, (show cost + 15 ≤ _ by omega).trans hpoly⟩

/-- A certified bucket supplies the cursor for linked sparsifier depth
selection. The factor phase receives the restored solver format. -/
theorem prepareLinkedDepthAfterBucket_runs
    {threshold h b a cursorDegree c : ℕ} (J : Scaling.Circulation)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hw : 3 * h + 2 ≤ wordSize c J.solverWords) (hlink : p.HasAt b (initDepthProcedures b h))
    (hm : st.regs 22 = max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hh : 0 < h) (ha : st.regs 99 = a) (hz : ZeroFrom st.mem a)
    (hflag : st.regs 18 = 1) :
    let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let d := max 2 (Nat.clog 2 threshold + 1)
    let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    a ≤ base ^ cursorDegree →
    max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c →
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let E := (M ^ 2 + 2).size
    let P := h * (38 * (2 ^ 24 * E) ^ 8 + E + E + 10)
    let L := P + E + 4
    let depth := Expander.chosenL (M ^ 2)
    ∃ out cost ret, Runs (wordSize c J.solverWords) p ω
        (initThresholdsAfterBucketCap
          (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry))
        st .normal out cost ∧
      out.regs 23 = M ^ 2 ∧ out.regs 44 = depth ∧ out.regs 98 = ret ∧
      a ≤ ret ∧ ret < 2 ^ wordSize c J.solverWords ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 23 → r ≠ 44 → out.regs r = st.regs r) ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E + 166 * (depth - 1) + 375 ∧
      cost ≤ 100915 * (h * (38 * (2 ^ 24) ^ 8 + 12) + 5) ^ 3 * E ^ 24 ∧
      ret ≤ base ^ (max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1) ∧
      ∃ bodyCost, Runs (wordSize c J.solverWords) p ω
        (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry)
        {st with regs := Function.update st.regs 98 a} .normal out bodyCost ∧ cost = bodyCost + 7 := by
  dsimp only
  intro hcursor hdegree
  let mid := {st with regs := Function.update st.regs 98 a}
  obtain ⟨out, cost, ret, hr, h23, hd, h98, hlo, hhi, hroomRet, hf, hz', hk, hargs, hc⟩ :=
    prepareSolverSparseCoreWithLinkedDepth_wordSize_runs J (st := mid) hw hlink
      (by simpa [mid] using hm) hM hh (by simp [mid]) hz hcursor hdegree
  have hw' : 1 < 2 ^ wordSize c J.solverWords := Nat.one_lt_two_pow (by omega)
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let E := (M ^ 2 + 2).size
  have hE : 1 ≤ E := Nat.lt_size.mpr (by norm_num)
  have hlin := initRuntimeSparseCoreDepth_scanCost_le M
  have hscan : 166 * (Expander.chosenL (M ^ 2) - 1) + 375 ≤ 915 * E ^ 2 := by
    have hs : E ≤ E ^ 2 := Nat.le_self_pow (by decide) _
    change _ ≤ 541 * E at hlin
    omega
  have hpoly := initDepthLog_runtime_cost_with_scan (h := h) (exponent := 24) hE hscan

  let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let d := max 2 (Nat.clog 2 threshold + 1)
  let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
  have hb : 2 ≤ base := by dsimp [base]; omega
  have hcoeff : h * (38 * (2 ^ 48) ^ 8 + 12) + 5 ≤ base ^ cd :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left hb _)
  have hcoeff' : h * (38 * (2 ^ 24) ^ 8 + 12) + 5 ≤ base ^ cd := by
    apply le_trans _ hcoeff
    gcongr
    decide
  have hbits : E ≤ base ^ (2 * d) :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (solverDepthPaddedSize_power_bounds J threshold).2
  have hret := hroomRet.trans
    (initDepthLog_runtime_address_bound (exponent := 24) hb hE hbits hcursor hcoeff')
  refine ⟨out, cost + 7, ret, initThresholdsAfterBucketCap_runs hflag ha hw' hr,
    h23, hd, h98, hlo, hhi, hroomRet, hf, hz', ?_, ?_, by omega, (show cost + 7 ≤ _ by simpa only [Nat.add_assoc] using Nat.add_le_add_right hc 7).trans hpoly, hret, ⟨cost, hr, rfl⟩⟩
  · intro r hr h23' h44
    exact (hk r hr h23' h44).trans (by simp [mid, show r ≠ 98 by omega])
  · intro r hlo' hhi'
    exact (hargs r hlo' hhi').trans (by simp [mid, show r ≠ 98 by omega])

/-- The solver's quality precision already bounds the integer width
used by the bucket initializer. -/
theorem initBucketWidth_le_qualityPrecision (m V k : ℕ) :
    IPM.Machine.ipmQualityRangeExponent m V k + IPM.Machine.slackRangeExponent m V + 6 ≤
      IPM.Machine.ipmQualityPrecision m V k := by
  have hSlack := IPM.Machine.slackRangeExponent_le_qualitySlackExponent m V k
  unfold IPM.Machine.ipmQualityPrecision IPM.Machine.ipmQualityErrorBits
    IPM.Machine.ipmQualityRangeExponent
  omega

/-- The bucket width inherits the polynomial bound on the numeric
limb count. The solver precision may span several machine words. -/
theorem initBucketWidth_power_bound {base m V k degree : ℕ}
    (hlimbs : IPM.Machine.ipmQualityLimbs m V k ≤ base ^ degree) :
    IPM.Machine.ipmQualityRangeExponent m V k + IPM.Machine.slackRangeExponent m V + 6 ≤
      base ^ degree := by
  have hprecision : IPM.Machine.ipmQualityPrecision m V k ≤ IPM.Machine.ipmQualityLimbs m V k := by
    unfold IPM.Machine.ipmQualityLimbs
    omega
  exact (initBucketWidth_le_qualityPrecision m V k).trans (hprecision.trans hlimbs)

/-- The encoded solver input bounds the concrete chain dimensions used by
the integer bucket stage. The width and fixed LSST coefficient may be
charged with their own powers of the input size. -/
theorem concreteIntegerBucket_wordSize_bounds (J : Scaling.Circulation)
    {threshold lsstConstant width degree c : ℕ}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold) :
    let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let P := Chain.concreteChainParams M hM
    max 2 (Nat.clog 2 threshold + 1) + 2 ≤ degree → 10 * degree ≤ c →
    width ≤ base ^ degree → 6272 * max 1 lsstConstant ≤ base ^ degree →
    4 * M + 3 < 2 ^ wordSize c J.solverWords ∧
      max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M)) + 1 <
        2 ^ wordSize c J.solverWords ∧
      Chain.concreteBucketCap lsstConstant width P.k P.d (4 * M) < 2 ^ wordSize c J.solverWords := by
  dsimp only
  intro hdegree hc hwidth hconstant
  let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let P := Chain.concreteChainParams M hM
  let d := max 2 (Nat.clog 2 threshold + 1)
  have hb : 2 ≤ base := by dsimp [base]; omega
  have hk : P.k ≤ M := by
    change ⌈(M : ℝ) ^ (1 / ((P.d : ℕ) : ℝ))⌉₊ ≤ M
    apply Nat.ceil_le.mpr
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hd : (1 : ℝ) ≤ P.d := by exact_mod_cast P.hd
    have he : 1 / (P.d : ℝ) ≤ 1 := div_le_one_of_le₀ hd (by positivity)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm he
  have hd : P.d ≤ M + 2 := by
    change ⌈Real.log ((M : ℝ) + 2) ^ ((1 - (23 / 24 : ℝ)) / 2)⌉₊ ≤ M + 2
    apply Nat.ceil_le.mpr
    push_cast
    have hl := Chain.one_le_log_add_two_of_one hM
    have hpow := Real.rpow_le_rpow_of_exponent_le hl
      (show (1 - (23 / 24 : ℝ)) / 2 ≤ 1 by norm_num)
    rw [Real.rpow_one] at hpow
    have hlog := Real.log_le_sub_one_of_pos (show 0 < (M : ℝ) + 2 by positivity)
    exact hpow.trans (by linarith)
  have hMpower : M + 2 ≤ base ^ d := (solverDepthPaddedSize_power_bounds J threshold).1
  have hv : 4 * M + 3 ≤ base ^ degree := by
    calc
      4 * M + 3 ≤ 4 * (M + 2) := by omega
      _ ≤ base ^ 2 * base ^ d :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hb 2) hMpower
      _ = base ^ (d + 2) := by rw [← pow_add, Nat.add_comm]
      _ ≤ base ^ degree := Nat.pow_le_pow_right (by omega) hdegree
  have hMD : M + 2 ≤ base ^ degree := le_trans (by omega : M + 2 ≤ 4 * M + 3) hv
  exact integerBucketStage_wordSize_bounds J.solverWords (by omega) hc hwidth
    (hk.trans ((Nat.le_add_right M 2).trans hMD)) (hd.trans hMD) hv hconstant

/-- Run the linked chain dimension procedures and compute the integer
bucket cap before entering the sparsifier and threshold stages. -/
@[expose] def prepareLinkedIntegerBucket (threshold b h clog lsstConstant : ℕ)
    (retry : Stmt) : Stmt :=
  (prepareSolverChainWithDepthWorkspace threshold b (b + 1) (b + 6) (b + 2) h (b + 5) retry ;;
    stageCertifiedInitUnitScale ;; saveSolverInitArguments) ;;
    initConcreteIntegerBucketStage clog lsstConstant

/-- Link the verified depth prefix to the integer bucket stage. The heap
remains fresh and its cursor is passed to the following Init stage. -/
theorem prepareLinkedIntegerBucket_runs
    {threshold b h a cursorDegree c precision alphaPtr V limbs clog lsstConstant width n bucketDegree : ℕ} (J : Scaling.Circulation)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hw : 3 * h + 2 ≤ wordSize c J.solverWords)
    (hlink : p.HasAt b (initDepthProcedures b h)) (hh : 0 < h)
    (hm : st.regs 0 = (IPM.namedInstance (IPM.Machine.solverConnectedAugmented J)).m)
    (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a)
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hptr : st.regs 4 = alphaPtr)
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hp : st.regs 3 = precision)
    (hwidth : st.regs 6 = width) (hn : st.regs 92 = n)
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog)) :
    let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let d := max 2 (Nat.clog 2 threshold + 1)
    let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    a ≤ base ^ cursorDegree →
    max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c →
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let C := Chain.concreteChainParams M hM
    let stretch := max 2 (Chain.concreteBucketStretch lsstConstant C.k (4 * M))
    let cap := Chain.concreteBucketCap lsstConstant width C.k C.d (4 * M)
    d + 2 ≤ bucketDegree → 10 * bucketDegree ≤ c →
    width ≤ base ^ bucketDegree → 6272 * max 1 lsstConstant ≤ base ^ bucketDegree →
    let E := (M + 2).size
    let P := h * (38 * (2 ^ 48 * E) ^ 8 + E + E + 10)
    let L := P + E + 4
    ∃ out cost ret, Runs (wordSize c J.solverWords) p ω
        (prepareLinkedIntegerBucket threshold b h clog lsstConstant retry) st .normal out cost ∧
      out.regs 47 = cap ∧ out.regs 14 = Nat.clog 2 (4 * M + 2) ∧ out.regs 18 = 1 ∧ out.regs 99 = ret ∧
      out.regs 22 = M ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧ out.regs 92 = n ∧
      out.regs 4 = 1 ∧ out.regs 6 = width ∧ out.regs 98 = ret ∧
      out.regs 101 = alphaPtr ∧ out.regs 102 = V ∧ out.regs 103 = limbs ∧
      out.regs 104 = precision ∧
      a ≤ ret ∧ ret < 2 ^ wordSize c J.solverWords ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧ ZeroFrom out.mem ret ∧
      (∀ x < a, out.mem x = st.mem x) ∧
      (∀ r < 98, r ∉ ([4, 14, 15, 16, 17, 18, 22, 46, 47, 57, 75, 76] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 100915 * (h * (38 * (2 ^ 48) ^ 8 + 12) + 5) ^ 3 * (M + 2).size ^ 24 +
        40 * (Nat.clog 2 (4 * M + 2) + Nat.clog 2 stretch) + 121 ∧
      cost ≤ 100915 * (h * (38 * (2 ^ 48) ^ 8 + 12) + 5) ^ 3 * (M + 2).size ^ 24 +
        80 * wordSize c J.solverWords + 121 := by
  dsimp only
  intro hcursor hdegree hb hc hwBound hconstant
  obtain ⟨hvertices, hstretch, hcap⟩ :=
    concreteIntegerBucket_wordSize_bounds J hM hb hc hwBound hconstant
  obtain ⟨mid, cost, ret, hr, h22, h75, h76, h4, h101, h102, h103, h104, h98,
      hlo, hhi, hroomRet, hz', hmem, hf, _, hcost⟩ :=
    prepareLinkedDepthBucketInputs_runs (ω := ω) (retry := retry) J hw hlink hh hm ha hz hM
      hptr hV hL hp hcursor hdegree
  obtain ⟨out, cost', hr', h47, hlog, h92, h18, h99, hm', hf', hcost'⟩ :=
    initConcreteIntegerBucketStage_runs (ω := ω) hM hclog h22
      ((hf 92 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn)
      h98 ((hf 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hwidth)
      h75 h76 hvertices hstretch hcap
  have hNlog : Nat.clog 2 (4 * max (IPM.Machine.solverConnectedAugmented J).m threshold + 2) ≤
      wordSize c J.solverWords := Nat.clog_le_of_le_pow (by omega)
  have hSlog {s : ℕ} (hs : s + 1 < 2 ^ wordSize c J.solverWords) :
      Nat.clog 2 s ≤ wordSize c J.solverWords :=
    Nat.clog_le_of_le_pow (by omega)
  have hclogStretch := hSlog hstretch
  exact ⟨out, cost + cost' + 1, ret,
    runs_seq_iff.mpr (Or.inr ⟨mid, cost, cost', hr, hr', rfl⟩),
    h47, hlog, h18, h99, (hf' 22 (by decide)).trans h22, (hf' 75 (by decide)).trans h75,
    (hf' 76 (by decide)).trans h76, h92, (hf' 4 (by decide)).trans h4,
    (hf' 6 (by decide)).trans
      ((hf 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hwidth),
    (hf' 98 (by decide)).trans h98, (hf' 101 (by decide)).trans h101,
    (hf' 102 (by decide)).trans h102, (hf' 103 (by decide)).trans h103,
    (hf' 104 (by decide)).trans h104, hlo, hhi, hroomRet, hm'.symm ▸ hz',
    fun x hx => (congrFun hm' x).trans (hmem x hx),
    fun r hr hskip => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hskip
      refine (hf' r ?_).trans (hf r hr hskip.1 hskip.2.2.2.2.2.2.1 hskip.2.2.2.2.2.2.2.2.2.2.1
        hskip.2.2.2.2.2.2.2.2.2.2.2)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega, by omega, by omega⟩

/-- Solver Init entry with an exact integer bucket count. The body after
the bucket stage builds the remaining threshold and level state. -/
@[expose] def solverInitWithIntegerBucket
    (alpha select quality graphPack threshold b h clog lsstConstant : ℕ)
    (retry afterBucket : Stmt) : Stmt :=
  prepareMinRatioSolverThresholdInputs alpha select quality graphPack ;;
  prepareLinkedIntegerBucket threshold b h clog lsstConstant retry ;;
  afterBucket

/-- Compose numeric input preparation, the integer bucket prefix, and
the rest of Init with both sequence instruction costs. -/
theorem solverInitWithIntegerBucket_runs
    {w alpha select quality graphPack threshold b h clog lsstConstant : ℕ}
    {inputCost bucketCost restCost : ℕ} {p : Program} {ω : ℕ → Bool}
    {st ready bucket out : State} {retry afterBucket : Stmt} {outcome : Outcome}
    (hi : Runs w p ω (prepareMinRatioSolverThresholdInputs alpha select quality graphPack)
      st .normal ready inputCost)
    (hb : Runs w p ω (prepareLinkedIntegerBucket threshold b h clog lsstConstant retry)
      ready .normal bucket bucketCost)
    (hr : Runs w p ω afterBucket bucket outcome out restCost) :
    Runs w p ω (solverInitWithIntegerBucket alpha select quality graphPack threshold b h clog
      lsstConstant retry afterBucket) st outcome out (inputCost + bucketCost + restCost + 2) := by
  refine runs_seq_iff.mpr (Or.inr ⟨ready, inputCost, bucketCost + restCost + 1, hi, ?_, by omega⟩)
  exact runs_seq_iff.mpr (Or.inr ⟨bucket, bucketCost, restCost, hb, hr, rfl⟩)

private lemma thresholdEdgeFactor_le (n : ℕ) : 3 * n ^ 2 + 1 ≤ (n + 2) ^ 3 := by
  nlinarith only [show 0 ≤ n ^ 3 by exact Nat.zero_le _, show 0 ≤ n ^ 2 by exact Nat.zero_le _]

/-- A depth-sized coarse scale makes the terminal threshold arithmetic
fit the encoded solver word size. -/
theorem concreteIntegerThreshold_wordSize_bound (J : Scaling.Circulation)
    {threshold scale c : ℕ}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let P := Chain.concreteChainParams M hM
    0 < scale → scale ≤ 4 * (P.d + 1) →
    76 * max 2 (Nat.clog 2 threshold + 1) ≤ c →
    (3 * M ^ 2 + 1) * (M * (2 * scale) ^ (P.d + 1)) < 2 ^ wordSize c J.solverWords := by
  dsimp only
  intro hs hscale hc
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let P := Chain.concreteChainParams M hM
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let e := max 2 (Nat.clog 2 threshold + 1)
  have hB : 0 < B := by dsimp [B]; omega
  have hMsize : M + 2 ≤ B ^ e := (solverDepthPaddedSize_power_bounds J threshold).1
  have hscalePow := Chain.concreteThresholdScale_power_le M scale hM hs hscale
  change (3 * M ^ 2 + 1) * (M * (2 * scale) ^ (P.d + 1)) < 2 ^ wordSize c J.solverWords
  have hsmall := thresholdEdgeFactor_le M
  calc
    _ ≤ (M + 2) ^ 3 * ((M + 2) * (M + 2) ^ 72) :=
      Nat.mul_le_mul hsmall (Nat.mul_le_mul (Nat.le_add_right M 2) hscalePow)
    _ = (M + 2) ^ 76 := by ring
    _ ≤ (B ^ e) ^ 76 := Nat.pow_le_pow_left hMsize _
    _ ≤ B ^ c := by rw [← pow_mul]; exact Nat.pow_le_pow_right hB (by simpa only [Nat.mul_comm] using hc)
    _ < 2 ^ wordSize c J.solverWords := pow_lt_two_pow_wordSize (by omega) _

/-- The dyadic scale derived from the concrete depth fits both the
binary logarithm call and the terminal table arithmetic. -/
theorem concreteDyadicThreshold_wordSize_bounds (J : Scaling.Circulation)
    {threshold c : ℕ}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hc : 76 * max 2 (Nat.clog 2 threshold + 1) ≤ c) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let P := Chain.concreteChainParams M hM
    let scale := Chain.concreteThresholdScale P.d
    2 * (P.d + 1) + 1 < 2 ^ wordSize c J.solverWords ∧
      (3 * M ^ 2 + 1) * (M * (2 * scale) ^ (P.d + 1)) < 2 ^ wordSize c J.solverWords := by
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let P := Chain.concreteChainParams M hM
  let scale := Chain.concreteThresholdScale P.d
  have hs : 0 < scale := Nat.two_pow_pos _
  obtain ⟨hl, hu⟩ := Chain.concreteThresholdScale_bounds P.d
  change 2 * (P.d + 1) ≤ scale at hl
  have hterminal := concreteIntegerThreshold_wordSize_bound J hM hs hu hc
  change 2 * (P.d + 1) + 1 < 2 ^ wordSize c J.solverWords ∧
    (3 * M ^ 2 + 1) * (M * (2 * scale) ^ (P.d + 1)) < 2 ^ wordSize c J.solverWords
  refine ⟨?_, hterminal⟩
  have hpow : 2 * scale ≤ (2 * scale) ^ (P.d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < 2 * scale by omega)
      (Nat.succ_le_succ (Nat.zero_le P.d))
  have hle : 2 * scale ≤ (3 * M ^ 2 + 1) * (M * (2 * scale) ^ (P.d + 1)) :=
    hpow.trans ((Nat.le_mul_of_pos_left _ hM).trans (Nat.le_mul_of_pos_left _ (by omega)))
  exact (show 2 * (P.d + 1) + 1 ≤ 2 * scale by omega).trans_lt (hle.trans_lt hterminal)

/-- Run the dyadic threshold initializer at the encoded solver word
size, using the same branch count and vertex bound as the bucket stage. -/
theorem concreteDyadicThreshold_wordSize_runs
    (J : Scaling.Circulation) (TP : Chain.SparseCoreParams)
    {threshold c clog L cap work kl ku sl su ll lu err bound precision base lsstConstant : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hc : 76 * max 2 (Nat.clog 2 threshold + 1) ≤ c) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let P := Chain.concreteChainParams M hM
    let w := wordSize c J.solverWords
    let e := Nat.clog 2 (2 * (P.d + 1))
    let scale := Chain.concreteThresholdScale P.d
    let divisor := 2 ^ (precision - e)
    let exponent := max (L + 1) 3
    let first := fun s : ℕ => 3 ^ L * work ^ (exponent - (L + 1)) * s ^ (L + 1)
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * work ^ 3) * work ^ (exponent - 3)
    let lower := max (first sl) (second kl sl ll)
    let upper := max (first su) (second ku su lu)
    let a := (upper + divisor - 1) / divisor
    TP.Valid → TP.γ_ℓ (M ^ 2) ≤ M → TP.γ_ℓ (M ^ 2) ≤ P.k →
    base + P.d + 1 < 2 ^ w → ZeroFrom st.mem base →
    st.regs 20 = upper → st.regs 23 = 2 ^ precision → st.regs 22 = M →
    st.regs 14 = Nat.clog 2 (4 * M + 2) →
    st.regs 77 = base → st.regs 76 = P.k → st.regs 75 = P.d →
    2 ^ precision < 2 ^ w → e ≤ precision → upper < 2 ^ w →
    max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M)) + 1 < 2 ^ w →
    TP.γ_ℓ (M ^ 2) ≤ (upper : ℝ) / ((2 ^ precision : ℕ) : ℝ) →
    (lower : ℝ) / ((2 ^ precision : ℕ) : ℝ) ≤ TP.γ_ℓ (M ^ 2) →
    kl ≤ ku → sl ≤ su → ll ≤ lu →
    ku ≤ bound * work → su ≤ bound * work → lu ≤ bound * work →
    ku - kl ≤ err → su - sl ≤ err → lu - ll ≤ err →
    3 ^ L * (err * (L + 1) * bound ^ L) * scale ≤ work →
    33 * cap * (err * bound ^ 2) * scale ≤ work →
    work ^ exponent = 2 ^ precision →
    ∃ out cost, Runs w p ω (initDyadicIntegerThresholdTable clog) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = Chain.concreteLevelRebuildCount M P.k a scale j (4 * M) ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) ∧
      cost ≤ 50 * P.d + 40 * e + 123 := by
  dsimp only
  intro hTP hγM hγk hbase hz h20 h23 h22 h14 h77 h76 h75 hprecision he hupper hstretch hlo hlower
    hk hs hl hku hsu hlu hke hse hle hfirst hsecond hcommon
  obtain ⟨hfit, hcapacity⟩ := concreteDyadicThreshold_wordSize_bounds J hM hc
  obtain ⟨hgap₁, hgap₂⟩ :=
    assembledGrowthEndpoint_gap_of_scale hk hs hl hku hsu hlu hke hse hle hfirst hsecond
  rw [hcommon] at hgap₁ hgap₂
  have horder : max (3 ^ L * work ^ (max (L + 1) 3 - (L + 1)) * sl ^ (L + 1))
      (11 * (cap * kl * sl * ll + 115 * work ^ 3) * work ^ (max (L + 1) 3 - 3)) ≤
      max (3 ^ L * work ^ (max (L + 1) 3 - (L + 1)) * su ^ (L + 1))
        (11 * (cap * ku * su * lu + 115 * work ^ 3) * work ^ (max (L + 1) 3 - 3)) := by
    have hpos : (0 : ℝ) < ((2 ^ precision : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.two_pow_pos _)
    have hreal := (div_le_div_iff_of_pos_right hpos).mp (hlower.trans hlo)
    exact_mod_cast hreal
  have hhi := dyadicGrowthUpper_le_of_gap (Nat.two_pow_pos _) horder hlower (maxGrowthEndpoint_gap_le hgap₁ hgap₂)
  exact initDyadicIntegerThresholdTable_runs TP (Chain.concreteChainParams _ hM)
    (ω := ω) hclog hTP hγM hγk hbase hz h20 h23 h22 h14 h77 h76 h75 hfit hprecision
    (integerRebuildDenominator_fits_of_bucket hstretch) he hupper hlo hhi hcapacity

/-- Assemble the growth endpoints and initialize the integer threshold table
without deciding either of the real-valued level ceilings. -/
@[expose] def initIntegerThresholdsFromGrowth (power clog : ℕ) : Stmt :=
  assembleInitStretch power ;; initDyadicIntegerThresholdTable clog

/-- Link a run of growth assembly to a run of integer threshold initialization.
The total includes the sequence instruction. -/
theorem initIntegerThresholdsFromGrowth_runs
    {w power clog growthCost tableCost : ℕ} {p : Program} {ω : ℕ → Bool}
    {st mid out : State}
    (hg : Runs w p ω (assembleInitStretch power) st .normal mid growthCost)
    (ht : Runs w p ω (initDyadicIntegerThresholdTable clog) mid .normal out tableCost) :
    Runs w p ω (initIntegerThresholdsFromGrowth power clog)
      st .normal out (growthCost + tableCost + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨mid, growthCost, tableCost, hg, ht, rfl⟩)

/-- Choose the rebuild scales after adding the runtime logarithm error
to the bounds supplied for the other stretch factors. -/
@[expose] def initRebuildScalesWithLogAllowance (clog : ℕ) : Stmt :=
  prepareRebuildLogAllowance ;; initRebuildScalesFromCaps clog

/-- The final working scale bounds the arithmetic even during the
initial computation of the logarithm allowance. -/
theorem initRebuildScalesWithLogAllowance_runs
    {w clog M N depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (h75 : st.regs 75 = depth) (h44 : st.regs 44 = L)
    (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound)
    (hbuckets : 0 < buckets) (hb : 0 < bound) :
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let coarse := Chain.concreteThresholdScale depth
    let allowance := max err (4096 * (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2))
    let bits := growthWorkingBits L cap coarse allowance bound
    2 ^ bits < 2 ^ w →
    ∃ out cost, Runs w p ω (initRebuildScalesWithLogAllowance clog) st .normal out cost ∧
      out.regs 30 = coarse ∧ out.regs 34 = cap ∧ out.regs 37 = bits ∧
      out.regs 4 = 2 ^ bits ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 4 → r ≠ 24 → r ≠ 57 → r < 27 ∨ 38 < r → out.regs r = st.regs r) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 13 * L + 40 * bits + 166 := by
  dsimp only
  intro hwork
  let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
  let cap := (L + 1) * buckets * (2 * degree + 190)
  let coarse := Chain.concreteThresholdScale depth
  let allowance := max err (4096 * (input + 2))
  have hcap : 0 < cap := Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) hbuckets) (by omega)
  have hallowPos : 0 < allowance :=
    (Nat.mul_pos (by decide) (by omega : 0 < input + 2)).trans_le (le_max_right _ _)
  have hallow : allowance < 2 ^ w := by
    have hle : allowance ≤ 33 * cap * (allowance * bound ^ 2) * coarse :=
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)).trans
        ((Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hcap)).trans
          (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
    exact hle.trans_lt ((growthWorkingBits_bounds L cap coarse allowance bound).2.2.trans_lt hwork)
  have hinput : input < 2 ^ w :=
    (Nat.le_add_right input 2).trans_lt
      (((Nat.le_mul_of_pos_left _ (by decide : 0 < 4096)).trans (le_max_right err _)).trans_lt hallow)
  have hproduct : M ^ 2 * (2 * M ^ 2 + 60) < 2 ^ w := by
    convert hinput using 1
    dsimp [input, SparseCore.coreNMax, SparseCore.coreSplitMax]
    ring
  have hlinear := (Nat.le_mul_of_pos_left (2 * M ^ 2 + 60) (Nat.pow_pos hMpos)).trans_lt hproduct
  have hMw := (Nat.le_mul_of_pos_right (M ^ 2) (by omega : 0 < 2 * M ^ 2 + 60)).trans_lt hproduct
  obtain ⟨mid, hr₁, h35', hm₁, hf₁⟩ :=
    prepareRebuildLogAllowance_runs (p := p) (ω := ω) hM hN h35 hMw (by omega) hlinear hproduct hallow
  obtain ⟨out, c, hr₂, h30, h34, h37, h4, hm₂, hf₂, hc⟩ :=
    initRebuildScalesFromCaps_runs (ω := ω) hp
      ((hf₁ 75 (by decide) (by decide) (by decide) (by decide)).trans h75)
      ((hf₁ 44 (by decide) (by decide) (by decide) (by decide)).trans h44)
      ((hf₁ 47 (by decide) (by decide) (by decide) (by decide)).trans h47)
      ((hf₁ 48 (by decide) (by decide) (by decide) (by decide)).trans h48)
      h35' ((hf₁ 36 (by decide) (by decide) (by decide) (by decide)).trans h36)
      hbuckets hallowPos hb hwork
  refine ⟨out, 33 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 33, c, hr₁, hr₂, rfl⟩),
    h30, h34, h37, h4, hm₂.trans hm₁, ?_, by omega⟩
  intro r h4r h24r h57r hr
  exact (hf₂ r h4r hr).trans (hf₁ r h24r (by omega) (by omega) h57r)

/-- The solver word budget for the endpoint assembly also suffices to
compute the working scale from the concrete sparsifier capacities. -/
theorem initRebuildScales_concrete_runs
    (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
    {threshold c clog N err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog)) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let P := Chain.concreteChainParams M hM
    let w := wordSize c J.solverWords
    let cap := (E.L + 1) * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
    let coarse := Chain.concreteThresholdScale P.d
    let allowance := max err (4096 * (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2))
    let bits := growthWorkingBits E.L cap coarse allowance bound
    let extra := 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3)
    st.regs 22 = M → st.regs 92 = N →
    st.regs 75 = P.d → st.regs 44 = E.L →
    st.regs 47 = E.B_fn (M ^ 2) → st.regs 48 = E.d_fn (M ^ 2) →
    st.regs 35 = err → st.regs 36 = bound →
    0 < E.B_fn (M ^ 2) → 0 < bound →
    (Nat.clog 2 coarse + Nat.clog 2 allowance + Nat.clog 2 (E.L + 1) + extra) *
      max (E.L + 1) 3 + extra < w →
    ∃ out cost, Runs w p ω (initRebuildScalesWithLogAllowance clog) st .normal out cost ∧
      out.regs 30 = coarse ∧ out.regs 34 = cap ∧ out.regs 37 = bits ∧
      out.regs 4 = 2 ^ bits ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 4 → r ≠ 24 → r ≠ 57 → r < 27 ∨ 38 < r → out.regs r = st.regs r) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (P.d + 1)) + 13 * E.L + 40 * bits + 166 := by
  dsimp only
  intro h22 h92 h75 h44 h47 h48 h35 h36 hbuckets hb hbudget
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let P := Chain.concreteChainParams M hM
  let cap := (E.L + 1) * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
  let coarse := Chain.concreteThresholdScale P.d
  let allowance := max err (4096 * (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2))
  let bits := growthWorkingBits E.L cap coarse allowance bound
  have hwidth := (growthEndpoint_width_le E.L cap coarse allowance bound).trans_lt hbudget
  have hbits : bits < wordSize c J.solverWords :=
    (Nat.le_mul_of_pos_right bits (lt_of_lt_of_le (by decide : 0 < 3) (le_max_right _ _))).trans_lt
      ((Nat.le_add_right _ _).trans_lt hwidth)
  exact initRebuildScalesWithLogAllowance_runs (ω := ω) hp h22 h92 hM h75 h44 h47 h48
    h35 h36 hbuckets hb
    (Nat.pow_lt_pow_right (by decide) hbits)

/-- Compute both sparse-core stretch endpoints and fill the concrete rebuild
table when the input bounds fit the working scale. -/
theorem initIntegerThresholdsFromGrowth_concrete_runs
    (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
    {threshold c power clog kl ku sl su ll lu base lsstConstant err bound workBits : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hc : 76 * max 2 (Nat.clog 2 threshold + 1) ≤ c)
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hpow : MeetsContract (wordSize c J.solverWords) p power
      (initStretchPowerContract (wordSize c J.solverWords))) :
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let m := M ^ 2
    let P := Chain.concreteChainParams M hM
    let TP := SparseCore.sparseCoreParams E
    let w := wordSize c J.solverWords
    let e := Nat.clog 2 (2 * (P.d + 1))
    let coarse := Chain.concreteThresholdScale P.d
    let exponent := max (E.L + 1) 3
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let input := SparseCore.coreNMax m + m
    let allowance := max err (4096 * (input + 2))
    let work := 2 ^ workBits
    let precision := workBits * exponent
    let extra := 12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3)
    let factor := 3 ^ E.L * work ^ (exponent - (E.L + 1))
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * work ^ 3) * work ^ (exponent - 3)
    let upper := max (first su) (second ku su lu)
    let divisor := 2 ^ (precision - e)
    let a := (upper + divisor - 1) / divisor
    growthWorkingBits E.L cap coarse allowance bound ≤ workBits →
    TP.Valid → TP.γ_ℓ m ≤ M → TP.γ_ℓ m ≤ P.k →
    st.regs 4 = work → st.regs 44 = E.L → st.regs 47 = E.B_fn m → st.regs 48 = E.d_fn m →
    st.regs 49 = kl → st.regs 51 = ku → st.regs 50 = sl → st.regs 52 = su →
    st.regs 26 = ll → st.regs 27 = lu →
    st.regs 22 = M → st.regs 14 = Nat.clog 2 (4 * M + 2) →
    st.regs 77 = base → st.regs 76 = P.k → st.regs 75 = P.d →
    base + P.d + 1 < 2 ^ w → ZeroFrom st.mem base →
    0 < E.B_fn m → 0 < sl → work ≤ ll →
    kl ≤ ku → sl ≤ su → ll ≤ lu →
    (kl : ℝ) / work ≤ (E.P_fn m).K_s → (E.P_fn m).K_s ≤ (ku : ℝ) / work →
    (sl : ℝ) / work ≤ (E.P_fn m).γ_ℓ → (E.P_fn m).γ_ℓ ≤ (su : ℝ) / work →
    (ll : ℝ) / work ≤ SparseCore.coreLambdaS (E.P_fn m) m →
    SparseCore.coreLambdaS (E.P_fn m) m ≤ (lu : ℝ) / work →
    precision + extra < w →
    max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M)) + 1 < 2 ^ w →
    ku ≤ bound * work → su ≤ bound * work → lu ≤ (input + 3) * work →
    input + 3 ≤ bound →
    ku - kl ≤ err → su - sl ≤ err → lu - ll ≤ 4096 * (input + 2) →
    ∃ out cost, Runs w p ω (initIntegerThresholdsFromGrowth power clog) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = Chain.concreteLevelRebuildCount M P.k a coarse j (4 * M) ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold P.k (Chain.levelM TP P j) (4 * M) ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) ∧
      cost ≤ 100 * exponent + 50 * P.d + 40 * e + 295 := by
  dsimp only
  intro hbitsMin hTP hγM hγk h4 h44 h47 h48 h49 h51 h50 h52 h26 h27
    h22 h14 h77 h76 h75 hbase hz hB hsl hllScale hk hs hl
    hklB hkuB hslB hsuB hllB hluB hbudget
    hstretch hku hsu hluCap hbound hkeErr hseErr hleLog
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let coarse := Chain.concreteThresholdScale (Chain.concreteChainParams M hM).d
  let cap := (E.L + 1) * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
  let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
  let allowance := max err (4096 * (input + 2))
  obtain ⟨hcoarse, hfirst, hsecond⟩ := growthWorkingBits_bounds E.L cap coarse allowance bound
  have hworkGe : 2 ^ growthWorkingBits E.L cap coarse allowance bound ≤ 2 ^ workBits :=
    Nat.pow_le_pow_right (by decide) hbitsMin
  have hcoarse := hcoarse.trans hworkGe
  have hfirst := hfirst.trans hworkGe
  have hsecond := hsecond.trans hworkGe
  let work := 2 ^ workBits
  let precision := workBits * max (E.L + 1) 3
  have hke := hkeErr.trans (le_max_left err (4096 * (input + 2)))
  have hse := hseErr.trans (le_max_left err (4096 * (input + 2)))
  have hle := hleLog.trans (le_max_right err (4096 * (input + 2)))
  have hlu' := hluCap.trans (Nat.mul_le_mul_right work hbound)
  have hcoeff := growthEndpoint_coefficient_bits_le E.L cap bound
  have hextra :
      max (2 * E.L + Nat.clog 2 bound * (E.L + 1))
        (5 + max (Nat.clog 2 cap + Nat.clog 2 bound * 3) 7) ≤
        12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (E.L + 3) := by
    let b := Nat.clog 2 bound
    let c := Nat.clog 2 cap
    let L := E.L
    change max (2 * L + b * (L + 1)) (5 + max (c + b * 3) 7) ≤ 12 + c + (b + 2) * (L + 3)
    rw [show (b + 2) * (L + 3) = b * L + b * 3 + 2 * L + 6 by ring,
      Nat.mul_add b L 1, Nat.mul_one]
    apply max_le
    · omega
    · rw [← Nat.add_max_add_left]
      exact max_le (by omega) (by omega)
  have hwidth := (Nat.add_le_add_left (hcoeff.trans hextra) precision).trans_lt hbudget
  obtain ⟨hcommonfit, hfhi, hshi⟩ :=
    growthEndpoint_words_fit (L := E.L) (cap := cap) (bits := workBits) hku hsu hlu' hwidth
  have hwork : 0 < work := Nat.two_pow_pos _
  have hll := hwork.trans_le hllScale
  have hlu := hll.trans_le hl
  have hcommon : work ^ max (E.L + 1) 3 = 2 ^ precision := by
    exact (pow_mul 2 workBits _).symm
  have hworkPow : work ≤ work ^ max (E.L + 1) 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hwork
      (show 1 ≤ max (E.L + 1) 3 from le_trans (by decide : 1 ≤ 3) (le_max_right _ _))
  have hworkfit := (hworkPow.trans_eq hcommon).trans_lt hcommonfit
  have hsupos : 0 < su := hsl.trans_le hs
  have hb : 0 < bound := by
    by_contra! h
    have hbzero : bound = 0 := Nat.eq_zero_of_le_zero h
    simp [hbzero, hsupos.not_ge] at hsu
  have hconst : 115 ≤ 115 * work ^ 3 :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos hwork)
  have hterm : 115 * work ^ 3 ≤ cap * ku * su * lu + 115 * work ^ 3 :=
    Nat.le_add_left _ _
  have hw : 115 < 2 ^ wordSize c J.solverWords :=
    (hconst.trans hterm).trans_lt
      ((Nat.le_mul_of_pos_left _ (by decide : 0 < 11)).trans_lt
        ((Nat.le_mul_of_pos_right _ (Nat.pow_pos hwork)).trans_lt hshi))
  have hcap : cap < 2 ^ wordSize c J.solverWords := by
    let coeff := max (3 ^ E.L * bound ^ (E.L + 1)) (11 * (cap * bound ^ 3 + 115))
    have hle : cap ≤ coeff :=
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)).trans
        ((Nat.le_add_right _ _).trans
          ((Nat.le_mul_of_pos_left _ (by decide : 0 < 11)).trans (le_max_right _ _)))
    exact hle.trans_lt ((Nat.le_pow_clog Nat.one_lt_two coeff).trans_lt
      (Nat.pow_lt_pow_right (by decide) ((Nat.le_add_left _ _).trans_lt hwidth)))
  have hcoarseTwo : 2 ≤ coarse := by
    exact (by omega : 2 ≤ 2 * ((Chain.concreteChainParams M hM).d + 1)).trans
      (Chain.concreteThresholdScale_bounds _).1
  have hbits : 1 ≤ workBits := by
    by_contra! hn
    have hzbits : workBits = 0 := Nat.eq_zero_of_le_zero (Nat.lt_succ_iff.mp hn)
    have htwo : 2 ≤ 2 ^ workBits := hcoarseTwo.trans hcoarse
    simp [hzbits] at htwo
  have hefit : max (E.L + 1) 3 < 2 ^ wordSize c J.solverWords :=
    (Nat.le_mul_of_pos_left _ hbits).trans_lt
      ((Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hwidth).trans Nat.lt_two_pow_self)
  have hfactorPos : 0 < 3 ^ E.L * work ^ (max (E.L + 1) 3 - (E.L + 1)) := by
    exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos hwork)
  have hsufit : su < 2 ^ wordSize c J.solverWords := by
    have hsuPow : su ≤ su ^ (E.L + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right hsupos (Nat.succ_le_succ (Nat.zero_le E.L))
    exact (hsuPow.trans (Nat.le_mul_of_pos_left _ hfactorPos)).trans_lt hfhi
  have hfactor := (Nat.le_mul_of_pos_right _ (Nat.pow_pos hsupos)).trans_lt hfhi
  have hslo := (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left 11 (Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) hs) hl) _))).trans_lt hshi
  obtain ⟨mid, cg, hg, h23, h19, h20, hlo, hhi, hregs, hm, hgc⟩ :=
    assembleInitStretch_runs E _ (ω := ω) hpow h4 h44 h47 h48 h49 h51 h50 h52 h26 h27
      hwork hB hsl hll hlu hs hklB hkuB hslB hsuB hllB hluB hworkfit hsufit hw
      hefit (hcommon.symm ▸ hcommonfit) hfactor hcap hfhi hslo hshi
  have he : Nat.clog 2 (2 * ((Chain.concreteChainParams _ hM).d + 1)) ≤ precision := by
    apply Nat.clog_le_of_le_pow
    exact (Chain.concreteThresholdScale_bounds _).1.trans
      (hcoarse.trans (hworkPow.trans_eq hcommon))
  rw [h19, hcommon] at hlo
  rw [h20, hcommon] at hhi
  obtain ⟨out, ct, ht, h83, h98, htable, hf, hz', htc⟩ :=
    concreteDyadicThreshold_wordSize_runs J (SparseCore.sparseCoreParams E) (ω := ω) hclog hM hc
      hTP hγM hγk hbase (hm.symm ▸ hz) h20 (h23.trans hcommon)
      ((hregs 22 (by decide)).trans h22) ((hregs 14 (by decide)).trans h14)
      ((hregs 77 (by decide)).trans h77) ((hregs 76 (by decide)).trans h76)
      ((hregs 75 (by decide)).trans h75)
      hcommonfit he (max_lt hfhi hshi) hstretch hhi hlo hk hs hl hku hsu hlu' hke hse hle hfirst hsecond hcommon
  exact ⟨out, cg + ct + 1, initIntegerThresholdsFromGrowth_runs hg ht, h83, h98, htable,
    fun x hx => (hf x hx).trans (congrFun hm x), hz', by omega⟩

/-- Compute the sparse-core logarithm before writing the integer rebuild
thresholds of Algorithm 2 (page 28). The fresh cursor from the logarithm
stage is the base of the threshold table. -/
@[expose] def initIntegerThresholdsFromLog (power clog bits load log pack : ℕ) : Stmt :=
  initSparseCoreLogForThresholds bits load log pack ;; initIntegerThresholdsFromGrowth power clog

/-- The logarithm leaves its endpoints, the table cursor and a fresh
heap for the integer writer. This joins the two runs and accounts for
the sequence instruction. -/
theorem initIntegerThresholdsFromLog_runs
    {w power clog bits load log pack c budget heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st mid : State}
    {post : State → Prop}
    (hr : Runs w p ω (initSparseCoreLogForThresholds bits load log pack) st .normal mid c)
    (hheap : heap ≤ mid.regs 77) (hframe : ∀ x < heap, mid.mem x = st.mem x)
    (htable : ∃ out ct, Runs w p ω (initIntegerThresholdsFromGrowth power clog) mid .normal out ct ∧
      post out ∧ (∀ x < mid.regs 77, out.mem x = mid.mem x) ∧ ct ≤ budget) :
    ∃ out cost, Runs w p ω (initIntegerThresholdsFromLog power clog bits load log pack)
      st .normal out cost ∧ post out ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ cost ≤ c + budget + 1 := by
  obtain ⟨out, ct, ht, hpost, hf, hc⟩ := htable
  exact ⟨out, c + ct + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, ct, hr, ht, rfl⟩), hpost,
    fun x hx => (hf x (hx.trans_le hheap)).trans (hframe x hx), by omega⟩

end MinCostFlow.MinRatio
