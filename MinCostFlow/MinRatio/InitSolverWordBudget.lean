module

public import MinCostFlow.MinRatio.InitCertifiedEntry
public import MinCostFlow.MinRatio.InitCertifiedWordBudget
import MinCostFlow.IPM.Machine.SolverInitialBounds
import MinCostFlow.IPM.Machine.ConnectedSolverPolynomialSpace

/-!
# Solver-wide word budget for certified Init

Derives uniform fixed `wordSize` multipliers for all stages of certified Init:
the numeric/graph input prefix, the integer bucket stage, the sparsifier factor
phase, and the certified threshold workspace and header allocation.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- The named graph of any valid IPM instance satisfies the dense capacity
and validity conditions of the Init graph packer. -/
theorem initNamedInstance_valid_caps (I : Instance) (hI : I.IsValid) :
    (IPM.namedInstance I).IsValid ∧
    (∀ v ∈ (IPM.namedInstance I).V, v < (IPM.namedInstance I).n) ∧
    (∀ e ∈ (IPM.namedInstance I).E, e < (IPM.namedInstance I).m) := by
  refine ⟨IPM.namedInstance_valid I hI, ?_, ?_⟩
  · intro v hv
    have hn : (IPM.namedInstance I).n = I.n := Finset.card_range I.n
    rw [hn]
    exact Finset.mem_range.mp hv
  · intro e he
    rw [IPM.namedInstance_m]
    exact Finset.mem_range.mp he

/-- One word-size bound covers every numeric and packed-graph inequality
required by `prepareMinRatioSolverThresholdInputs_runs` and header allocation
at the connected solver's 4-bit quality format. -/
theorem initThresholdInputs_wordSize_bounds (J : Scaling.Circulation)
    {w c heap k q dh : ℕ}
    (hn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m)
    (hcap : ∀ e, 1 ≤ J.capacity e) (hk : 2 ^ k ≤ (J.n + J.m + 2) ^ q) :
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let I := IPM.Machine.solverConnectedAugmented J
    let V := IPM.Machine.solverPenalty J.m
    let G := IPM.namedInstance I
    let L := IPM.Machine.ipmQualityLimbs I.m V k
    let P := IPM.Machine.ipmQualityPrecision I.m V k
    let dL := max 41 q + 7
    let dCursor := max (max dh dL) 2 + 5
    heap ≤ B ^ dh →
    IPM.Machine.ipmQualityParameterWordBits I.m V k ≤ w →
    max dCursor (dL + 9) ≤ c → wordSize c J.solverWords ≤ w →
    2 ≤ G.m * V ∧
    Num.IPM.alphaExponent G.m V + 3 ≤ P ∧
    P + 2 ≤ 4 * L ∧
    IPM.Machine.ipmParameterWordBits G.m V ≤ w ∧
    G.m < 2 ^ w ∧ V < 2 ^ w ∧ L < 2 ^ w ∧ P < 2 ^ w ∧
    Num.IPM.alphaScale G.m V + 1 < 2 ^ w ∧
    IPM.Machine.ipmQualityRangeExponent G.m V k + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w ∧
    Num.IPM.alphaExponent G.m V + k + 10 < 2 ^ w ∧
    16 ≤ 2 ^ w ∧ 3 * 4 + 2 ≤ w ∧
    heap + (L + 1) + 6 + DynSpanner.Program.dynGraphSize G.n G.m ≤ B ^ dCursor ∧
    heap + (L + 1) + 6 + DynSpanner.Program.dynGraphSize G.n G.m < 2 ^ w ∧
    L ≤ B ^ dL ∧
    IPM.Machine.ipmQualityRangeExponent G.m V k + IPM.Machine.slackRangeExponent G.m V + 6 ≤ B ^ (dL + 1) ∧
    80 * L + 260 < 2 ^ w := by
  dsimp only
  intro hheap hqw hc hword
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let I := IPM.Machine.solverConnectedAugmented J
  let V := IPM.Machine.solverPenalty J.m
  let G := IPM.namedInstance I
  let L := IPM.Machine.ipmQualityLimbs I.m V k
  let P := IPM.Machine.ipmQualityPrecision I.m V k
  let dL := max 41 q + 7
  let dCursor := max (max dh dL) 2 + 5
  have hGm : G.m = I.m := IPM.namedInstance_m I
  have hB : 2 ≤ B := by dsimp [B]; omega
  obtain ⟨hMlo, hMhi⟩ := IPM.Machine.solverConnectedAugmented_size J hn hm hcap
  have hVpos : 4 ≤ V := by
    dsimp [V, IPM.Machine.solverPenalty]
    have hcb : 1 ≤ IPM.Machine.solverCapacityBound J.m := by
      unfold IPM.Machine.solverCapacityBound
      exact le_max_of_le_right (Nat.one_le_pow _ _ hm)
    have hsq : 1 ≤ IPM.Machine.solverCapacityBound J.m ^ 2 := Nat.one_le_pow _ _ hcb
    have h1 : 4 * 1 * 1 ≤ 4 * J.m * IPM.Machine.solverCapacityBound J.m ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 hm) hsq
    simpa only [Nat.mul_one] using h1
  have hsize : 2 ≤ G.m * V := by
    rw [hGm]
    have h1 : 1 * 4 ≤ I.m * V := Nat.mul_le_mul (hm.trans_le hMlo) hVpos
    omega
  have hfit := IPM.Machine.ipm_quality_parameter_words_fit I.m V k hqw
  have hparam : IPM.Machine.ipmParameterWordBits I.m V ≤ w :=
    (IPM.Machine.ipmParameterWordBits_le_quality I.m V k).trans hqw
  have hcover : Num.IPM.alphaExponent I.m V + 3 ≤ P := by
    have ha : Num.IPM.alphaExponent I.m V ≤ Num.IPM.alphaScale I.m V :=
      (Num.IPM.alphaExponent_le_iff I.m V _).mpr Nat.lt_two_pow_self.le
    dsimp only [P, IPM.Machine.ipmQualityPrecision]
    omega
  have hwidth : P + 2 ≤ 4 * L := by
    dsimp only [L, P, IPM.Machine.ipmQualityLimbs]
    omega
  have hboundLt : IPM.Machine.ipmQualityParameterBound I.m V k < 2 ^ w := by
    have hsize' : (IPM.Machine.ipmQualityParameterBound I.m V k).size ≤ w := by
      dsimp only [I, V, IPM.Machine.ipmQualityParameterWordBits] at hqw ⊢
      omega
    exact Nat.size_le.mp hsize'
  have hpsiBound :
      IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6 ≤ L := by
    have hs := IPM.Machine.slackRangeExponent_le_qualitySlackExponent I.m V k
    dsimp only [L, IPM.Machine.ipmQualityLimbs, IPM.Machine.ipmQualityRangeExponent]
    omega
  have hpsiLt :
      IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6 < 2 ^ w :=
    hpsiBound.trans_lt hfit.2.1
  have hepsLt : Num.IPM.alphaExponent I.m V + k + 10 < 2 ^ w := by
    have ha : Num.IPM.alphaExponent I.m V ≤ Num.IPM.alphaScale I.m V :=
      (Num.IPM.alphaExponent_le_iff I.m V _).mpr Nat.lt_two_pow_self.le
    have hk' : k ≤ IPM.Machine.ipmQualityRangeExponent I.m V k := by
      have := IPM.Machine.qualityExponent_le_qualitySlackExponent I.m V k
      unfold IPM.Machine.ipmQualityRangeExponent
      omega
    unfold IPM.Machine.ipmQualityParameterBound at hboundLt
    omega
  have hw16 : 16 ≤ 2 ^ w :=
    (by decide : 16 ≤ 2 ^ 14).trans (Nat.pow_le_pow_right (by decide) hfit.1)
  have hcursor :
      heap + (L + 1) + 6 + DynSpanner.Program.dynGraphSize G.n G.m ≤ B ^ dCursor :=
    initPackedQualitySolverCursor_power_bound J hn hm hcap hk hheap
  have hBpos : 0 < B := by dsimp [B]; omega
  have hcPos : 1 ≤ c := by
    have : 1 ≤ max dCursor (dL + 9) := by dsimp [dCursor]; omega
    omega
  have lift {x e : ℕ} (hx : x ≤ B ^ e) (he : e ≤ c) : x < 2 ^ w :=
    (hx.trans (Nat.pow_le_pow_right hBpos he)).trans_lt
      ((pow_lt_two_pow_wordSize hcPos J.solverWords).trans_le
        (Nat.pow_le_pow_right (by decide) hword))
  have hbase : J.n + J.m + 2 ≤ B := by
    have hn' : J.n ≤ J.solverWords.foldr max 0 := le_max_left _ _
    have hm' := J.solverWords_length
    dsimp [B]; omega
  have hLpow : L ≤ B ^ dL :=
    (IPM.Machine.ipmQualityLimbs_connected_poly J.n J.m I.m k q hm hMlo hMhi hk).trans
      (Nat.pow_le_pow_left hbase _)
  have hLpos : 1 ≤ B ^ dL := Nat.one_le_pow _ _ hBpos
  have hpsiPow :
      IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6 ≤
        B ^ (dL + 1) :=
    hpsiBound.trans (hLpow.trans (Nat.pow_le_pow_right hBpos (Nat.le_succ _)))
  have hdetectPow : 80 * L + 260 ≤ B ^ (dL + 9) := by
    have hmul : 80 * L + 260 ≤ 512 * B ^ dL := by
      have h1 : 80 * L ≤ 80 * B ^ dL := Nat.mul_le_mul_left 80 hLpow
      have h2 : 260 ≤ 260 * B ^ dL := Nat.le_mul_of_pos_right 260 hLpos
      omega
    calc
      _ ≤ 512 * B ^ dL := hmul
      _ = B ^ dL * 512 := Nat.mul_comm _ _
      _ ≤ B ^ dL * B ^ 9 := Nat.mul_le_mul_left _
        ((by decide : 512 ≤ 2 ^ 9).trans (Nat.pow_le_pow_left hB 9))
      _ = B ^ (dL + 9) := (pow_add B dL 9).symm
  have hGmLt : G.m < 2 ^ w := by
    rw [hGm]
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide : 0 < 20)) hfit.2.2.2.2.2.1
  have h34 : 3 * 4 + 2 ≤ w := hfit.1
  have hCursorW := lift hcursor ((le_max_left _ _).trans hc)
  have hDetectW := lift hdetectPow ((le_max_right _ _).trans hc)
  refine ⟨hsize, ?_, hwidth, ?_, hGmLt, hfit.2.2.2.2.2.2.2, hfit.2.1, hfit.2.2.1, ?_, ?_, ?_,
    hw16, h34, hcursor, hCursorW, hLpow, ?_, hDetectW⟩
  · rw [hGm]; exact hcover
  · rw [hGm]; exact hparam
  · rw [hGm]; exact hfit.2.2.2.2.2.2.1
  · rw [hGm]; exact hpsiLt
  · rw [hGm]; exact hepsLt
  · rw [hGm]; exact hpsiPow

/-- One uniform word-size multiplier covers both sparsifier depth selection and
the fixed-budget path factor phase for every circulation `J`. -/
theorem prepareCertifiedSparsifierFactors_uniform_runs
    (threshold h b Kγ pathC Kint cw factorEntry decK thr cDeg witnessDen cursorDegree : ℕ)
    (hK : 1 ≤ decK) (hc : 0 < cDeg) (hWitness : 0 < witnessDen) :
    ∃ multiplier, ∀ (J : Scaling.Circulation) {c a : ℕ} {p : Program} {ω : ℕ → Bool}
      {st : State} {retry : Stmt},
      let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
      let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
      let w := wordSize c J.solverWords
      let den := Expander.maxPhiDenOf decK thr (M ^ 2)
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) (M ^ 2)
      let length := (max (Expander.PathDSProg.gExpImpl Kγ pathC Kint den (M ^ 2))
        (Expander.PathDSProg.gExpImpl Kγ pathC Kint witnessDen cap)) ^ 2
      let query := max (Expander.PathDSProg.gQueryImpl Kγ pathC Kint den (M ^ 2))
        (Expander.PathDSProg.gQueryImpl Kγ pathC Kint witnessDen cap)
      3 * h + 2 ≤ w → p.HasAt b (initDepthProcedures b h) →
      MeetsContract w p factorEntry (initMachinePathFactorsContract w Kγ pathC Kint cw) →
      st.regs 22 = M → 1 ≤ M → 0 < h →
      st.regs 99 = a → ZeroFrom st.mem a → st.regs 18 = 1 → st.regs 4 = 1 →
      a ≤ B ^ cursorDegree → multiplier ≤ c →
      ∃ depthState out depthCost factorCost ret,
        Runs w p ω (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry)
          {st with regs := Function.update st.regs 98 a} .normal depthState depthCost ∧
        Runs w p ω (initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen)
          depthState .normal out factorCost ∧
        out.regs 44 = Expander.chosenL (M ^ 2) ∧ out.regs 4 = 1 ∧
        out.regs 98 = ret + 4 ∧ a ≤ ret ∧ ZeroFrom out.mem (ret + 4) ∧
        ret ≤ a + (h * (38 * (2 ^ 24 * (M ^ 2 + 2).size) ^ 8 + (M ^ 2 + 2).size + (M ^ 2 + 2).size + 10) + (M ^ 2 + 2).size + 4) +
          (h * (38 * (2 ^ 24 * (M ^ 2 + 2).size) ^ 8 + (M ^ 2 + 2).size + (M ^ 2 + 2).size + 10) + (M ^ 2 + 2).size + 4) +
          Num.logarithmSpace
            (h * (38 * (2 ^ 24 * (M ^ 2 + 2).size) ^ 8 + (M ^ 2 + 2).size + (M ^ 2 + 2).size + 10) + (M ^ 2 + 2).size + 4)
            (h * (38 * (2 ^ 24 * (M ^ 2 + 2).size) ^ 8 + (M ^ 2 + 2).size + (M ^ 2 + 2).size + 10))
            (M ^ 2 + 2).size ∧
        out.regs 50 = length ∧ out.regs 52 = length ∧ out.regs 114 = query ∧ out.regs 115 = query ∧
        length < 2 ^ w ∧ 0 < length ∧
        (∀ r < 98, r ∉ ([23, 24, 31, 32, 33, 36, 44, 50, 52, 58, 63] : List ℕ) →
          out.regs r = st.regs r) ∧
        (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
        (∀ x < a, out.mem x = st.mem x) := by
  let d := max 2 (Nat.clog 2 threshold + 1)
  let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
  let dh := max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1
  obtain ⟨factorMultiplier, hfactor⟩ :=
    initMergedSparsifierFactors_budgeted_runs Kγ pathC Kint cw factorEntry decK thr cDeg
      witnessDen (2 * d) 0 dh hK hc hWitness
  refine ⟨max dh factorMultiplier, ?_⟩
  intro J c a p ω st retry
  dsimp only
  intro hw hlink himpl h22 hM hh ha hz hflag hscale hcursor hsize
  have hd : dh ≤ c := (le_max_left _ _).trans hsize
  have hf : factorMultiplier ≤ c := (le_max_right _ _).trans hsize
  obtain ⟨depthState, _, ret, _, h23, h44, h98, hlow, _, hretSpace, hmem, hzero, hframe, hargs, _, _, hret,
      depthCost, hdepth, _⟩ :=
    prepareLinkedDepthAfterBucket_runs (b := b) (p := p) (ω := ω) (retry := retry)
      J hw hlink h22 hM hh ha hz hflag hcursor hd
  have h4 := (hframe 4 (by decide) (by decide) (by decide)).trans hscale
  have hword : wordSize factorMultiplier J.solverWords ≤ wordSize c J.solverWords :=
    Nat.mul_le_mul_right _ hf
  obtain ⟨out, factorCost, hrun, h50, h52, h114, h115, hpos, hfit, hout, _, hfree, hkeep, hmem', _⟩ :=
    hfactor J.solverWords himpl h23 h98 h4 hzero (by decide)
      (solverDepthPaddedSize_power_bounds J threshold).2 (by simp) hret hword
  refine ⟨depthState, out, depthCost, factorCost, ret, hdepth, hrun,
    (hkeep 44 (by decide)).trans h44, (hkeep 4 (by decide)).trans h4, hout, hlow, hfree, hretSpace,
    by simpa only [one_mul] using h50, by simpa only [one_mul] using h52,
    by simpa only [one_mul] using h114, by simpa only [one_mul] using h115,
    by simpa only [h52, one_mul] using hfit,
    by simpa only [h50, one_mul] using hpos, ?_, ?_, ?_⟩
  · intro r hr hn
    have hskip : r ∉ ([24, 31, 32, 33, 36, 50, 52, 58, 63, 98, 99, 114, 115, 122] : List ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      omega
    refine (hkeep r hskip).trans (hframe r hr ?_ ?_)
    · intro he; subst r; exact hn (by decide)
    · intro he; subst r; exact hn (by decide)
  · intro r h₁ h₂
    have hn : r ∉ ([24, 31, 32, 33, 36, 50, 52, 58, 63, 98, 99, 114, 115, 122] : List ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    exact (hkeep r hn).trans (hargs r h₁ h₂)
  · intro x hx
    exact (hmem' x (Or.inl (hx.trans_le hlow))).trans (hmem x hx)

/-- Explicit uniform `wordSize` multiplier for the certified threshold
workspace, both endpoint logarithms, table writing, header allocation, and
level descriptor reservation. -/
@[expose] def certifiedEndpointMultiplier (threshold coefficient h dhEnd : ℕ) : ℕ :=
  let dm := max 2 (Nat.clog 2 threshold + 1)
  let dd := dm + 2
  let df := dm
  let di := 7 + 4 * dm
  let dc := Nat.clog 2 (coefficient + 3)
  let ds := 2 * (dd + df + di) + 17 + Nat.clog 2 (coefficient + 1) + (h - 1)
  let dl := max ds di + 3
  max (max (max (df + 1) (di + 1)) (max ds dl))
    (max (max (max (dc + 2 * ds) (max (di + ds) (ds + df)) + 1)
      (max (max dhEnd (max dl dm + 6)) (11 + 3 * dl) + 2))
      (max (76 * dm) (max (6 + 3 * dm) (Nat.clog 2 h + 11))))

private theorem certifiedEndpointMultiplier_bounds {threshold coefficient h dhEnd c : ℕ}
    (hc : certifiedEndpointMultiplier threshold coefficient h dhEnd ≤ c) :
    let dm := max 2 (Nat.clog 2 threshold + 1)
    let dd := dm + 2
    let df := dm
    let di := 7 + 4 * dm
    let dc := Nat.clog 2 (coefficient + 3)
    let ds := 2 * (dd + df + di) + 17 + Nat.clog 2 (coefficient + 1) + (h - 1)
    let dl := max ds di + 3
    max (max (df + 1) (di + 1)) (max ds dl) ≤ c ∧
    max (dc + 2 * ds) (max (di + ds) (ds + df)) + 1 ≤ c ∧
    max (max dhEnd (max dl dm + 6)) (11 + 3 * dl) + 2 ≤ c ∧
    76 * dm ≤ c ∧ 6 + 3 * dm ≤ c ∧ Nat.clog 2 h ≤ c ∧ 11 ≤ c ∧ dm ≤ c := by
  dsimp only [certifiedEndpointMultiplier] at hc ⊢
  have h1 := (le_max_left _ _).trans hc
  have h2 := (le_max_right _ _).trans hc
  have h21 := (le_max_left _ _).trans h2
  have h22 := (le_max_right _ _).trans h2
  have h211 := (le_max_left _ _).trans h21
  have h212 := (le_max_right _ _).trans h21
  have h221 := (le_max_left _ _).trans h22
  have h222 := (le_max_right _ _).trans h22
  have h2221 := (le_max_left _ _).trans h222
  have h2222 := (le_max_right _ _).trans h222
  exact ⟨h1, h211, h212, h221, h2221, (Nat.le_add_right _ 11).trans h2222,
    (Nat.le_add_left 11 _).trans h2222, (Nat.le_mul_of_pos_left _ (by decide : 0 < 76)).trans h221⟩

private theorem coarseScale_le_threshold_term {M d : ℕ} (hM : 1 ≤ M) :
    concreteThresholdScale d ≤
      (3 * M ^ 2 + 1) * (M * (2 * concreteThresholdScale d) ^ (d + 1)) := by
  have hpos : 0 < concreteThresholdScale d := Nat.two_pow_pos _
  have hpow : 2 * concreteThresholdScale d ≤ (2 * concreteThresholdScale d) ^ (d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < 2 * concreteThresholdScale d by omega)
      (Nat.succ_le_succ (Nat.zero_le d))
  have h1 : 1 ≤ (3 * M ^ 2 + 1) * M := Nat.mul_pos (by omega) hM
  calc
    concreteThresholdScale d ≤ 2 * concreteThresholdScale d := by omega
    _ ≤ (2 * concreteThresholdScale d) ^ (d + 1) := hpow
    _ ≤ ((3 * M ^ 2 + 1) * M) * (2 * concreteThresholdScale d) ^ (d + 1) :=
      Nat.le_mul_of_pos_left _ h1
    _ = _ := by ring

private theorem two_mul_lt_two_pow_of_lt {p w : ℕ} (hge : 16 ≤ p) (hp : p < w) :
    2 * p < 2 ^ w := by
  have hlt := Nat.lt_two_pow_self (n := p - 1)
  have ht := Nat.mul_le_mul_right 2 (show p ≤ 2 ^ (p - 1) by omega)
  rw [← pow_succ, show p - 1 + 1 = p by omega] at ht
  exact (by simpa only [Nat.mul_comm 2 p] using ht : 2 * p ≤ 2 ^ p).trans_lt
    (Nat.pow_lt_pow_right (by decide) hp)

/-- Under `certifiedEndpointMultiplier`, run `initCertifiedThresholdsWithWorkspace`
and return the certified threshold table, restored solver format and header
registers, and remaining address room through header and level descriptor tables. -/
theorem initCertifiedThresholdsWithWorkspace_budgeted_runs
    (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
    {threshold h c dhEnd power bits load log pack clog coefficient extend mul shift add roundEntry : ℕ}
    {growth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : 1 ≤ max (IPM.Machine.solverConnectedAugmented J).m threshold)
    (hpower : MeetsContract (wordSize c J.solverWords) p power (initStretchPowerContract (wordSize c J.solverWords)))
    (hbits : MeetsContract (wordSize c J.solverWords) p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract (wordSize c J.solverWords) p load (Num.loadSmallContract (wordSize c J.solverWords) h))
    (hpack : MeetsContract (wordSize c J.solverWords) p pack (Num.packWordContract (wordSize c J.solverWords) h))
    (hext : MeetsContract (wordSize c J.solverWords) p extend (Num.extendCopyContract (wordSize c J.solverWords) h))
    (hmul : MeetsContract (wordSize c J.solverWords) p mul (Num.multiplyContract (wordSize c J.solverWords) h))
    (hshift : MeetsContract (wordSize c J.solverWords) p shift (Num.shiftLeftContract (wordSize c J.solverWords) h))
    (hadd : MeetsContract (wordSize c J.solverWords) p add (Num.addContract (wordSize c J.solverWords) h))
    (hround : MeetsContract (wordSize c J.solverWords) p roundEntry (initDepthEndpointContract (wordSize c J.solverWords) h))
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hLog : p.HasAt log (Num.logarithmModule log h))
    (hLogWord : 3 * h + 2 ≤ wordSize c J.solverWords) (hh2 : 2 ≤ h) :
    let w := wordSize c J.solverWords
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let C := Chain.concreteChainParams M hM
    st.regs 22 = M → st.regs 92 = (IPM.namedInstance (IPM.Machine.solverConnectedAugmented J)).n →
    st.regs 75 = C.d → st.regs 76 = C.k →
    st.regs 44 = E.L → st.regs 50 = growth → st.regs 4 = 1 →
    0 < growth → (E.P_fn (M ^ 2)).γ_ℓ = growth → 1 ≤ (E.P_fn (M ^ 2)).K_s →
    (E.P_fn (M ^ 2)).p_s = 1 →
    (E.P_fn (M ^ 2)).K_s = 1 + coefficient / Real.log 2 →
    (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ M →
    (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ C.k →
    st.regs 47 = E.B_fn (M ^ 2) → st.regs 48 = E.d_fn (M ^ 2) →
    st.regs 14 = Nat.clog 2 (4 * M + 2) →
    ZeroFrom st.mem (st.regs 98) → st.regs 98 ≤ B ^ dhEnd →
    certifiedEndpointMultiplier threshold coefficient h dhEnd ≤ c →
    ∃ out cost table a,
      Runs w p ω (initCertifiedThresholdsWithWorkspace power bits load log pack clog
          coefficient h extend mul shift add roundEntry) st .normal out cost ∧
      out.regs 10 = 1 ∧ out.regs 83 = table ∧ out.regs 99 = table + (C.d + 1) ∧
      st.regs 98 ≤ table ∧ table + 3 * (C.d + 1) + 17 < 2 ^ w ∧
      ZeroFrom out.mem (table + (C.d + 1)) ∧
      (∀ j ≤ C.d, out.mem (table + j) =
          Chain.concreteLevelRebuildCount C.M₀ C.k a (concreteThresholdScale C.d) j (4 * M) ∧
        (out.mem (table + j) : ℝ) ≤
          Chain.SparseCoreTool.updateThreshold C.k
            (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold C.k
            (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
          48 * ((out.mem (table + j) : ℝ) + 1)) ∧
      (∀ x < st.regs 98, out.mem x = st.mem x) ∧
      out.regs 0 = st.regs 0 ∧ out.regs 6 = st.regs 6 ∧
      out.regs 67 = st.regs 67 ∧ out.regs 68 = st.regs 68 ∧ out.regs 4 = st.regs 4 ∧
      (∀ r ∈ ([69, 70, 71, 72, 73, 75, 76, 101, 102, 103, 104] : List ℕ),
        out.regs r = st.regs r) := by
  dsimp only
  intro h22 h92 h75 h76 h44 h50 h4 hg hGrowth hK hps1 hCoeff hγM hγk h47 h48 h14
    hz hheapPow hcmult
  let w := wordSize c J.solverWords
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let C := Chain.concreteChainParams M hM
  let dm := max 2 (Nat.clog 2 threshold + 1)
  let dd := dm + 2
  let df := dm
  let di := 7 + 4 * dm
  let dc := Nat.clog 2 (coefficient + 3)
  let ds := 2 * (dd + df + di) + 17 + Nat.clog 2 (coefficient + 1) + (h - 1)
  let dl := max ds di + 3
  obtain ⟨hcWork, hcWord, hcAddr, hcDyadic, hcDen, hcH, hc11, hcDm⟩ :=
    certifiedEndpointMultiplier_bounds hcmult
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hMpow : M + 2 ≤ B ^ dm := (solverDepthPaddedSize_power_bounds J threshold).1
  have hCd_le : C.d ≤ M + 2 := by
    change ⌈Real.log ((M : ℝ) + 2) ^ ((1 - (23 / 24 : ℝ)) / 2)⌉₊ ≤ M + 2
    apply Nat.ceil_le.mpr
    push_cast
    have hl := Chain.one_le_log_add_two_of_one hM
    have hpow := Real.rpow_le_rpow_of_exponent_le hl (show (1 - (23 / 24 : ℝ)) / 2 ≤ 1 by norm_num)
    rw [Real.rpow_one] at hpow
    have hlog := Real.log_le_sub_one_of_pos (show 0 < (M : ℝ) + 2 by positivity)
    exact hpow.trans (by linarith)
  have hCk_le : C.k ≤ M := by
    change ⌈(M : ℝ) ^ (1 / ((C.d : ℕ) : ℝ))⌉₊ ≤ M
    apply Nat.ceil_le.mpr
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hd : (1 : ℝ) ≤ C.d := by exact_mod_cast C.hd
    have he : 1 / (C.d : ℝ) ≤ 1 := div_le_one_of_le₀ hd (by positivity)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm he
  have hCdPow : 2 * (C.d + 1) ≤ B ^ dd := by
    calc
      2 * (C.d + 1) ≤ 4 * (M + 2) := by omega
      _ ≤ B ^ 2 * B ^ dm := Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) hMpow
      _ = B ^ dd := by rw [← pow_add, Nat.add_comm]
  have hCdPow' : C.d ≤ B ^ dm := hCd_le.trans hMpow
  have lift {x e : ℕ} (hx : x ≤ B ^ e) (he : e ≤ c) : x < 2 ^ w :=
    (hx.trans (Nat.pow_le_pow_right (by omega) he)).trans_lt
      (pow_lt_two_pow_wordSize (by omega) J.solverWords)
  have hdyadic := concreteDyadicThreshold_wordSize_bounds J hM hcDyadic
  have hcoarseWord : concreteThresholdScale C.d < 2 ^ w :=
    (coarseScale_le_threshold_term hM).trans_lt hdyadic.2
  have hhWord : h < 2 ^ w :=
    lift ((Nat.le_pow_clog (by decide) h).trans (Nat.pow_le_pow_left hB _)) hcH
  have h1265 : 1265 < 2 ^ w :=
    lift ((by decide : 1265 ≤ 2 ^ 11).trans (Nat.pow_le_pow_left hB 11)) hc11
  have hw11 : 11 < 2 ^ w := lt_trans (by decide) h1265
  have hw3 : 3 < 2 ^ w := lt_trans (by decide) h1265
  have hw1 : 1 < 2 ^ w := lt_trans (by decide) h1265
  have hdenPow : 3 * C.k * Nat.clog 2 (4 * M + 2) ^ 2 ≤ B ^ (6 + 3 * dm) := by
    have hclog : Nat.clog 2 (4 * M + 2) ≤ 4 * (M + 2) := by
      apply Nat.clog_le_of_le_pow
      exact (show 4 * M + 2 ≤ 4 * (M + 2) by omega).trans Nat.lt_two_pow_self.le
    have hmul' : 3 * C.k * Nat.clog 2 (4 * M + 2) ^ 2 ≤ 48 * (M + 2) ^ 3 := by
      calc
        _ ≤ 3 * (M + 2) * (4 * (M + 2)) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 3 (hCk_le.trans (Nat.le_add_right M 2)))
            (Nat.pow_le_pow_left hclog 2)
        _ = 48 * (M + 2) ^ 3 := by ring
    calc
      _ ≤ 48 * (M + 2) ^ 3 := hmul'
      _ ≤ B ^ 6 * (B ^ dm) ^ 3 := Nat.mul_le_mul
        ((by decide : 48 ≤ 2 ^ 6).trans (Nat.pow_le_pow_left hB 6))
        (Nat.pow_le_pow_left hMpow 3)
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm dm 3]
  have hdenWord : 3 * C.k * Nat.clog 2 (4 * M + 2) ^ 2 < 2 ^ w := lift hdenPow hcDen
  obtain ⟨saved, hsave, h67s, h68s, h4s, h0s, h6s, hmemSave, hkeepSave⟩ :=
    saveCertifiedThresholdFormat_runs (w := w) (p := p) (ω := ω) (st := st)
  have keepS (r : ℕ) (h1 : r ≠ 128 := by decide) (h2 : r ≠ 129 := by decide)
      (h3 : r ≠ 130 := by decide) (h4 : r ≠ 131 := by decide) (h5 : r ≠ 132 := by decide) :=
    hkeepSave r h1 h2 h3 h4 h5
  obtain ⟨work, c₁, hwork, hw68, hw67, hw4, hwGap, hwDepthP, hw16, hwRange, hw35, hw92, hwDvd,
      hwMem, _⟩ :=
    initCertifiedEndpointWorkspace_atTop_runs E J.solverWords (c := c) (dd := dd) (dm := dm)
      hclog hbits ((keepS 22).trans h22) ((keepS 92).trans h92) hM hpower
      ((keepS 75).trans h75) hdyadic.1 hcoarseWord ((keepS 44).trans h44)
      ((keepS 50).trans h50) ((keepS 4).trans h4) hg hGrowth hK hγM
      ((keepS 47).trans h47) ((keepS 48).trans h48) (by omega) hhWord hw11
      hCdPow hMpow hcWork le_rfl
  obtain ⟨hf_le, hd_le, hg_le⟩ := certifiedSparseCoreGrowth_le_top E hg hGrowth hK hγM
  have hfactorPow :
      11 * (E.L + 1) * growth * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190) ≤ B ^ df :=
    hf_le.trans ((Nat.le_add_right M 2).trans hMpow)
  have hgrowthPow : growth ≤ B ^ df := hg_le.trans ((Nat.le_add_right M 2).trans hMpow)
  have hinputPow : SparseCore.coreNMax (M ^ 2) + M ^ 2 + 3 ≤ B ^ di := by
    calc
      _ ≤ 65 * (M + 2) ^ 4 := certifiedThresholdLogInput_le M
      _ ≤ B ^ 7 * (B ^ dm) ^ 4 := Nat.mul_le_mul
        ((by decide : 65 ≤ 2 ^ 7).trans (Nat.pow_le_pow_left hB 7))
        (Nat.pow_le_pow_left hMpow 4)
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm dm 4]
  have hcoefPow : coefficient + 3 ≤ B ^ dc :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left hB _)
  have hscalePow := certifiedThresholdEndpoint_scale_power_bound (h := h) (coefficient := coefficient)
    hB hCdPow hfactorPow hinputPow
  have hrange2 : 2 ≤ (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2).size :=
    Nat.lt_size.mpr (by omega)
  obtain ⟨hkWord, hlWord, hscaledGrowth, hprecLt, haddrRoom⟩ :=
    certifiedEndpointWordSize_bounds J.solverWords (c := c) hrange2 hcoefPow hinputPow hscalePow
      hgrowthPow hheapPow hCdPow' hcWord hcAddr
  have hprecLt2 := two_mul_lt_two_pow_of_lt hw16 hprecLt
  have hfactorWord : 11 * (E.L + 1) * growth * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190) < 2 ^ w :=
    lift hfactorPow hcDm
  have hMword : M < 2 ^ w := lift ((Nat.le_add_right M 2).trans hMpow) hcDm
  obtain ⟨scaled, hscale, hs68, hs67, hs4, hs50, _, hs25, hs92, hsMem, hs22, hs75, hs98, _⟩ :=
    certifiedEndpointWorkspace_rescale_runs hwork hw68 hw67 hw4 hw35 hw92 hwMem hw1 hscaledGrowth
  have keepWorkScaled (r : ℕ)
      (hS : avoidsRegister r saveCertifiedThresholdFormat = true)
      (hW : avoidsRegister r (initCertifiedEndpointWorkspace power bits clog coefficient h) = true)
      (hR : avoidsRegister r rescaleCertifiedSparsifierLength = true) :
      scaled.regs r = st.regs r :=
    (runs_preserves_register hR hscale).trans
      ((runs_preserves_register hW hwork).trans (runs_preserves_register hS hsave))
  obtain ⟨ready, finished, c₃, c₄, base, a, hready, htable, h83, h98f, hentries, hframeFin, hzFin,
      hbaseLo, hroomFin⟩ :=
    prepareAndWriteCertifiedEndpointTable_runs E C hpower
      ((keepWorkScaled 44 rfl rfl rfl).trans h44) rfl
      ((keepWorkScaled 47 rfl rfl rfl).trans h47) rfl
      ((keepWorkScaled 48 rfl rfl rfl).trans h48) rfl
      hs4 hload hext hmul hshift hadd (hs98.trans (keepS 98)) hs67 hs68 rfl hh2 hfactorWord
      ((hsMem.trans hmemSave).symm ▸ hz) h1265 hprecLt2 hround hhWord hwDvd hwDepthP hγM hγk
      rfl hGrowth hs50 hg (E.hB_pos _) (max_lt (hd_le.trans_lt hMword) hw3) hscaledGrowth
      (hs22.trans ((keepS 22).trans h22))
      ((keepWorkScaled 14 rfl rfl rfl).trans h14)
      ((keepWorkScaled 76 rfl rfl rfl).trans h76)
      (hs75.trans ((keepS 75).trans h75)) hdenWord hdyadic.2 hbits hpack hclog hLog hLogWord
      hs92 (hs25.trans hps1.symm) (by change (E.P_fn (M ^ 2)).p_s ≤ 1; rw [hps1]) hCoeff hdyadic.1 hcoarseWord hw16 hM
      rfl hwGap hkWord hlWord hwRange haddrRoom
  obtain ⟨checked, hchecked, h67c, h68c, h4c, h0c, h6c, _, _, h10c, hmemc, h99c, hkeepc⟩ :=
    initCertifiedThresholdsWithWorkspace_runs hsave h67s h68s h4s h0s h6s hwork hscale hready
      hw1 htable
  have keepFinal (r : ℕ)
      (hS : avoidsRegister r saveCertifiedThresholdFormat = true)
      (hW : avoidsRegister r (initCertifiedEndpointWorkspace power bits clog coefficient h) = true)
      (hSc : avoidsRegister r rescaleCertifiedSparsifierLength = true)
      (hR : avoidsRegister r (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog) = true)
      (hT : avoidsRegister r (initSparseCoreThresholdsFromEndpoints power load extend mul shift add roundEntry h) = true)
      (h99 : r ≠ 99 := by decide) (h67 : r ≠ 67 := by decide) (h68 : r ≠ 68 := by decide)
      (h4 : r ≠ 4 := by decide) (h0 : r ≠ 0 := by decide) (h6 : r ≠ 6 := by decide)
      (h114 : r ≠ 114 := by decide) (h115 : r ≠ 115 := by decide) (h10 : r ≠ 10 := by decide)
      (h126 : r ≠ 126 := by decide) (h127 : r ≠ 127 := by decide) :
      checked.regs r = st.regs r := by
    refine (hkeepc r h99 h67 h68 h4 h0 h6 h114 h115 h10).trans ?_
    refine (runs_preserves_register hT htable).trans ?_
    simp only [Function.update_of_ne h127, Function.update_of_ne h126]
    exact (runs_preserves_register hR hready).trans (keepWorkScaled r hS hW hSc)
  refine ⟨checked, _, base, a, hchecked, h10c,
    (hkeepc 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h83,
    h99c.trans (by simpa only [Nat.add_assoc] using h98f), hbaseLo, hroomFin,
    hmemc.symm ▸ (by simpa only [Nat.add_assoc] using hzFin),
    fun j hj => by simpa only [hmemc] using hentries j hj,
    fun x hx => (congrFun hmemc x).trans ((hframeFin x hx).trans (congrFun (hsMem.trans hmemSave) x)),
    h0c, h6c, h67c, h68c, h4c, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact keepFinal _ rfl rfl rfl rfl rfl

/-- The cursor returned by the chain-depth and integer-bucket stage has a
fixed-power bound in the encoded circulation base. -/
theorem initBucketCursor_power_bound (J : Scaling.Circulation)
    {threshold h heap afterChain dh : ℕ} :
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let d := max 2 (Nat.clog 2 threshold + 1)
    let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    let E₁ := (M + 2).size
    let P₁ := h * (38 * (2 ^ 48 * E₁) ^ 8 + E₁ + E₁ + 10)
    let L₁ := P₁ + E₁ + 4
    heap ≤ B ^ dh →
    afterChain ≤ heap + L₁ + L₁ + Num.logarithmSpace L₁ P₁ E₁ →
    afterChain ≤ B ^ (max dh (10 + 3 * (cd + 8 * d)) + 1) := by
  dsimp only
  intro hh hc
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hcoeff : h * (38 * (2 ^ 48) ^ 8 + 12) + 5 ≤ B ^ cd :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left hB _)
  have hm := (solverDepthPaddedSize_power_bounds J threshold).1
  have bits : (M + 2).size ≤ M + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  exact hc.trans (initDepthLog_runtime_address_bound (exponent := 48) hB
    (show 1 ≤ (M + 2).size from Nat.lt_size.mpr (by norm_num))
    (bits.trans hm) hh hcoeff)

end MinCostFlow.MinRatio
