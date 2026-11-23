module

public import MinCostFlow.MinRatio.InitSparsifierPathPair
public import MinCostFlow.MinRatio.InitDepthPower
public import MinCostFlow.Expander.PathDSProg.Params

/-!
# Sparsifier query factor at initialization

Add the fallback charges to the two path-length intervals and take their
maximum to enclose the query factor from Section 8.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- The Section 8 configuration uses separate length and query factors.
Length enclosures bound the square of the path-length factor, and
query enclosures bound the maximum of the two query factors. -/
theorem initSparsifierFactors_eq (tools : Spanner.SpannerTools) (costs : Spanner.SpannerToolCosts)
    (phiMin : ℝ) (hphi : 0 < phiMin) (M : ℕ) (dec : ℝ) (hdec : 0 ≤ dec) :
    let params := Spanner.sparsifyMGParamsOfDecWithTime tools costs phiMin hphi M dec hdec
    let cDeg := tools.constructExpander.c_deg
    let phiConst := tools.constructExpander.φ_Const
    let paths := tools.pathDS
    params.γ_ℓ = Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      params.γ_t = max (paths.γ_query phiMin M)
        (paths.γ_query phiConst (Spanner.capM_W cDeg phiMin M)) := by
  exact ⟨rfl, rfl⟩

/-- The machine path tool uses integer path factors at the two
reciprocal conductances. The sparsifier squares the maximum length
factor and takes the maximum query factor. -/
theorem initSparsifierMachineFactors_eq (Kγ c Kint den M : ℕ) (cDeg phiConst : ℝ)
    (paths : Spanner.PathDSTool)
    (hExp : ∀ phi cap, paths.γ_ExpPath phi cap =
      (Expander.PathDSProg.gExpImpl Kγ c Kint (Nat.ceil (1 / phi)) cap : ℝ))
    (hQuery : ∀ phi cap, paths.γ_query phi cap =
      (Expander.PathDSProg.gQueryImpl Kγ c Kint (Nat.ceil (1 / phi)) cap : ℝ)) :
    let phiMin := 1 / (den : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let witnessDen := Nat.ceil (1 / phiConst)
    Spanner.capGammaL cDeg phiConst paths phiMin M =
      (max (Expander.PathDSProg.gExpImpl Kγ c Kint den M)
        (Expander.PathDSProg.gExpImpl Kγ c Kint witnessDen cap) : ℝ) ^ 2 ∧
    Spanner.capGammaQuery cDeg phiConst paths phiMin M =
      (max (Expander.PathDSProg.gQueryImpl Kγ c Kint den M)
        (Expander.PathDSProg.gQueryImpl Kγ c Kint witnessDen cap) : ℝ) := by
  dsimp only
  have hden : Nat.ceil (1 / (1 / (den : ℝ))) = den := by simp [one_div]
  simp only [Spanner.capGammaL, Spanner.capGammaExpPath, Spanner.capGammaQuery,
    hExp, hQuery, hden, and_self]

/-- Assemble the exact query factor from the path bounds program's
conductance, cited-path and length registers and the capped fallback cost. -/
@[expose] def initMachinePathQuery (out fallback : ℕ) : Stmt :=
  .assign out (.bin .add
    (.bin .add (.bin .add (.reg 7) (.reg 9)) (.reg fallback))
    (.bin .add (.reg 17) (.reg 9)))

/-- The query assembly uses the same components as the merged path tool.
A bound on the final sum also bounds every intermediate sum. -/
theorem initMachinePathQuery_runs {w Kγ c Kint d M outReg fallback : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : st.regs 7 = Expander.PathDSProg.phiOutDenImpl Kγ c d M)
    (hc : st.regs 9 = Expander.PathDSProg.csExpFactor Kγ Kint M)
    (hf : st.regs fallback = Expander.PathDSProg.fbCostCap d M)
    (hl : st.regs 17 = Expander.PathDSProg.phiOutDenImpl Kγ c d M * Expander.PathDSProg.lenFactor M)
    (hw : Expander.PathDSProg.gQueryImpl Kγ c Kint d M < 2 ^ w) :
    ∃ out, Runs w p ω (initMachinePathQuery outReg fallback) st .normal out 10 ∧
      out.regs outReg = Expander.PathDSProg.gQueryImpl Kγ c Kint d M ∧ out.mem = st.mem ∧
      (∀ r ≠ outReg, out.regs r = st.regs r) := by
  let result := Expander.PathDSProg.gQueryImpl Kγ c Kint d M
  let out := { st with regs := Function.update st.regs outReg result }
  have h₁ : st.regs 7 + st.regs 9 < 2 ^ w := by
    rw [hd, hc]
    unfold Expander.PathDSProg.gQueryImpl Expander.PathDSProg.gBaseImpl at hw
    omega
  have h₂ : st.regs 7 + st.regs 9 + st.regs fallback < 2 ^ w := by
    rw [hd, hc, hf]
    unfold Expander.PathDSProg.gQueryImpl Expander.PathDSProg.gBaseImpl at hw
    omega
  have h₃ : st.regs 17 + st.regs 9 < 2 ^ w := by
    rw [hl, hc]
    unfold Expander.PathDSProg.gQueryImpl Expander.PathDSProg.gExpImpl at hw
    omega
  have he : st.regs 7 + st.regs 9 + st.regs fallback + (st.regs 17 + st.regs 9) = result := by
    rw [hd, hc, hf, hl]
    rfl
  exact ⟨out, runs_assign_iff.mpr ⟨result,
    by simp [Expr.eval, BinOp.eval, h₁, h₂, h₃, he, result, hw],
    rfl, rfl, rfl⟩, by simp [out, result], rfl, fun r hr => by simp [out, hr]⟩

/-- The query factor uses each path length plus the fallback cost
at that call's own input conductance. -/
theorem initSparsifierQueryFactor_eq (Kγ c M den : ℕ) (K cDeg phiConst : ℝ)
    (paths : Spanner.PathDSTool)
    (hQuery : paths.γ_query = Expander.csGammaQuery Kγ c K)
    (hden : 0 < den) :
    let phiMin := 1 / (den : ℝ)
    let witnessCap := Spanner.capM_W cDeg phiMin M
    Spanner.capGammaQuery cDeg phiConst paths phiMin M =
      max (Expander.csGammaExpPath Kγ c K phiMin M + Expander.PathDSProg.fbCostBound den)
        (Expander.csGammaExpPath Kγ c K phiConst witnessCap +
          Expander.PathDSProg.fbCostBound (Nat.ceil (1 / phiConst))) := by
  dsimp only
  rw [Spanner.capGammaQuery, hQuery, Expander.csGammaQuery, Expander.csGammaQuery]
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  rw [show (1 : ℝ) / (1 / (den : ℝ)) = den by field_simp, Nat.ceil_natCast]

/-- Add the scaled fallback charges to the path interval endpoints
before taking the maximum for the current query factor. -/
theorem initSparsifierQueryFactor_bounds
    (Kγ c M den a b d e scale : ℕ) (K cDeg phiConst : ℝ) (paths : Spanner.PathDSTool)
    (hQuery : paths.γ_query = Expander.csGammaQuery Kγ c K)
    (hden : 0 < den) (hs : 0 < scale) :
    let phiMin := 1 / (den : ℝ)
    let witnessCap := Spanner.capM_W cDeg phiMin M
    let inputCharge := scale * Expander.PathDSProg.fbCostBound den
    let witnessCharge := scale * Expander.PathDSProg.fbCostBound (Nat.ceil (1 / phiConst))
    (a : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiMin M →
    Expander.csGammaExpPath Kγ c K phiMin M ≤ (b : ℝ) / scale →
    (d : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiConst witnessCap →
    Expander.csGammaExpPath Kγ c K phiConst witnessCap ≤ (e : ℝ) / scale →
    (max (a + inputCharge) (d + witnessCharge) : ℕ) / (scale : ℝ) ≤
      Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
    Spanner.capGammaQuery cDeg phiConst paths phiMin M ≤
      (max (b + inputCharge) (e + witnessCharge) : ℕ) / (scale : ℝ) := by
  dsimp only
  intro ha hb hd he
  rw [initSparsifierQueryFactor_eq Kγ c M den K cDeg phiConst paths hQuery hden]
  have hs' : (scale : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hadd (x n : ℕ) : ((x + scale * n : ℕ) : ℝ) / scale = (x : ℝ) / scale + n := by
    push_cast
    field_simp
  push_cast
  rw [← max_div_div_right (by positivity), ← max_div_div_right (by positivity)]
  simp only [← Nat.cast_add, ← Nat.cast_mul, hadd]
  exact ⟨max_le_max (add_le_add ha le_rfl) (add_le_add hd le_rfl),
    max_le_max (add_le_add hb le_rfl) (add_le_add he le_rfl)⟩

/-- Form an adjusted query-factor endpoint from the two path endpoints.
Registers 112 and 113 hold the fallback costs at the common scale. -/
@[expose] def initSparsifierQueryEndpoint (input witness : ℕ) : Expr :=
  let a := Expr.bin .add (.reg input) (.reg 112)
  let b := Expr.bin .add (.reg witness) (.reg 113)
  .bin .add a (.bin .sub b a)

/-- The adjusted endpoint is the maximum of the two charged endpoints. -/
theorem initSparsifierQueryEndpoint_eval {w input witness a b inputCharge witnessCharge : ℕ}
    {st : State}
    (ha : st.regs input = a) (hb : st.regs witness = b)
    (hi : st.regs 112 = inputCharge) (hj : st.regs 113 = witnessCharge)
    (hfit : max (a + inputCharge) (b + witnessCharge) < 2 ^ w) :
    Expr.eval w st (initSparsifierQueryEndpoint input witness) =
      some (max (a + inputCharge) (b + witnessCharge)) := by
  have ha' := (le_max_left (a + inputCharge) (b + witnessCharge)).trans_lt hfit
  have hb' := (le_max_right (a + inputCharge) (b + witnessCharge)).trans_lt hfit
  have hdiff : b + witnessCharge - (a + inputCharge) < 2 ^ w :=
    (Nat.sub_le ..).trans_lt hb'
  have hmax : a + inputCharge + (b + witnessCharge - (a + inputCharge)) =
      max (a + inputCharge) (b + witnessCharge) := by omega
  simp [initSparsifierQueryEndpoint, Expr.eval, BinOp.eval, ha, hb, hi, hj, ha', hb', hdiff, hmax, hfit]

/-- Get the bit length of ten times the reciprocal conductance.
For positive conductance reciprocals this is the logarithmic term
in the fallback size exponent. -/
@[expose] def initFallbackBitLength (bits denReg outReg : ℕ) : Stmt :=
  .call outReg bits [.bin .mul (.const 10) (.reg denReg)]

/-- The bit-length call reads the runtime denominator and preserves memory. -/
theorem initFallbackBitLength_runs {w bits denReg outReg d : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract) (hd : st.regs denReg = d)
    (hdPos : 0 < d) (hw : 10 < 2 ^ w) (hfit : 10 * d < 2 ^ w) :
    ∃ out cost, Runs w p ω (initFallbackBitLength bits denReg outReg) st .normal out cost ∧
      out.regs outReg = Nat.log 2 (10 * d) + 1 ∧ out.mem = st.mem ∧
      (∀ r ≠ outReg, out.regs r = st.regs r) ∧ cost ≤ 14 * (10 * d).size + 10 := by
  have hargs : evalArgs w st [.bin .mul (.const 10) (.reg denReg)] = some [10 * d] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hd, hw, hfit]
  obtain ⟨out, cost, value, hr, hp, hv, hf, hc⟩ :=
    runs_call_of_meetsContract (r := outReg) hbits hargs (by simpa using hfit) ⟨_, rfl⟩ ω
  obtain ⟨hm, hval⟩ := hp
  have hUpper : (10 * d).size ≤ Nat.log 2 (10 * d) + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _)
  have hLower : ¬ (10 * d).size ≤ Nat.log 2 (10 * d) := by
    intro h
    exact (Nat.size_le.mp h).not_ge (Nat.pow_log_le_self 2 (by omega : 10 * d ≠ 0))
  have hsize : (10 * d).size = Nat.log 2 (10 * d) + 1 := by omega
  exact ⟨out, cost, hr, hv.trans (hval.trans hsize), hm, hf,
    by simp [Num.IPM.bitLengthContract, argsSize, Expr.size] at hc; omega⟩

/-- The branch-count calculator's ceiling-cube-root test can also
compute the fallback floor cube root by testing the successor input. -/
theorem initFallbackCubeRoot_of_successor {y candidate : ℕ}
    (hpos : 0 < candidate)
    (hlo : (candidate - 1) ^ 3 < y + 1) (hhi : y + 1 ≤ candidate ^ 3) :
    Expander.PathDSProg.natCbrtFloor y = candidate - 1 := by
  obtain ⟨hl, hu⟩ := Expander.PathDSProg.natCbrtFloor_spec y
  have hc : candidate - 1 + 1 = candidate := by omega
  apply Nat.le_antisymm
  · by_contra! h
    have hp := Nat.pow_le_pow_left (show candidate ≤ Expander.PathDSProg.natCbrtFloor y by omega) 3
    omega
  · by_contra! h
    have hp := Nat.pow_le_pow_left
      (show Expander.PathDSProg.natCbrtFloor y + 1 ≤ candidate - 1 by omega) 3
    omega

/-- Call the branch-count procedure for a cube root of the successor,
then subtract one to obtain the fallback floor cube root. -/
@[expose] def selectInitFallbackCubeRoot (entry input result : ℕ) : Stmt :=
  .call result entry [.const 3, .bin .add (.reg input) (.const 1)] ;;
  .assign result (.bin .sub (.reg result) (.const 1))

/-- The existing branch-count procedure supplies the exact cube root. -/
theorem selectInitFallbackCubeRoot_runs {w entry input result y : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hy : st.regs input = y) (hword : y + 1 < 2 ^ w) (hw : 3 < 2 ^ w) :
    ∃ out cost, Runs w p ω (selectInitFallbackCubeRoot entry input result) st .normal out cost ∧
      out.regs result = Expander.PathDSProg.natCbrtFloor y ∧ out.mem = st.mem ∧
      (∀ r ≠ result, out.regs r = st.regs r) ∧ cost ≤ 89 * (y + 1).size + 29 := by
  have hargs : evalArgs w st [.const 3, .bin .add (.reg input) (.const 1)] = some [3, y + 1] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hy, hword, hw, show 1 < 2 ^ w by omega]
  have hwords : ∀ x ∈ [3, y + 1], x < 2 ^ w := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpre : (minRatioBranchCountContract w).pre [3, y + 1] st.mem :=
    ⟨3, y + 1, rfl, by decide, by omega, by omega⟩
  obtain ⟨mid, cost, k, hr, hp, hk, hf, hcost⟩ :=
    runs_call_of_meetsContract (r := result) himpl hargs hwords hpre ω
  obtain ⟨hm, depth, m, hd, hpos, heq, hbranch⟩ := hp
  have hdEq : depth = 3 := (List.cons.inj heq).1.symm
  have hmEq : m = y + 1 := (List.cons.inj (List.cons.inj heq).2).1.symm
  subst depth
  subst m
  have hupper : y + 1 ≤ k ^ 3 := (minRatioBranchCount_le_iff hd hpos).mp (by rw [hbranch])
  have hpositive : 0 < k := by
    by_contra! hz
    have hzero : k = 0 := by omega
    simp [hzero] at hupper
  have hlower : (k - 1) ^ 3 < y + 1 := by
    apply Nat.lt_of_not_ge
    intro h
    have hle := (minRatioBranchCount_le_iff hd hpos).mpr h
    omega
  have hroot := initFallbackCubeRoot_of_successor hpositive hlower hupper
  have hkWord : k < 2 ^ w := by
    have hle := (minRatioBranchCount_le_iff hd hpos).mpr
      (Nat.le_self_pow (by decide : 3 ≠ 0) (y + 1))
    omega
  let out := {mid with regs := Function.update mid.regs result (k - 1)}
  have hsub : Runs w p ω (.assign result (.bin .sub (.reg result) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hk, show 1 < 2 ^ w by omega, show k - 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  simp [minRatioBranchCountContract, argsSize, Expr.size] at hcost
  exact ⟨out, cost + 5, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 4, hr, hsub, by omega⟩),
    by simp [out, hroot], hm, fun r h => by simpa [out, h] using hf r h, by omega⟩

/-- Compute the fallback size exponent from the runtime reciprocal
conductance. Register 119 holds the bit length, then its fourth power. -/
@[expose] def initFallbackSizeExponent (bits root denReg result : ℕ) : Stmt :=
  initFallbackBitLength bits denReg 119 ;;
  .assign 119 (initDepthPower (.reg 119) 4) ;;
  selectInitFallbackCubeRoot root 119 result

/-- The size exponent agrees with the fallback charge formula. -/
theorem initFallbackSizeExponent_runs {w bits root denReg result d : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w))
    (hd : st.regs denReg = d) (hdPos : 0 < d) (hw : 10 < 2 ^ w)
    (hfit : 10 * d < 2 ^ w) (hpow : (Nat.log 2 (10 * d) + 1) ^ 4 + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (initFallbackSizeExponent bits root denReg result) st .normal out cost ∧
      out.regs result = Expander.PathDSProg.zStarExp d ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 119 → r ≠ result → out.regs r = st.regs r) ∧
      cost ≤ 14 * (10 * d).size + 89 * ((Nat.log 2 (10 * d) + 1) ^ 4 + 1).size + 51 := by
  obtain ⟨mid, c₁, hr₁, hbitsVal, hm₁, hk₁, hc₁⟩ :=
    initFallbackBitLength_runs (ω := ω) (outReg := 119) hbits hd hdPos hw hfit
  let y := (Nat.log 2 (10 * d) + 1) ^ 4
  let ready := {mid with regs := Function.update mid.regs 119 y}
  have hpower : Runs w p ω (.assign 119 (initDepthPower (.reg 119) 4)) mid .normal ready 10 :=
    runs_assign_iff.mpr ⟨y, initDepthPower_eval (by simp [Expr.eval, hbitsVal]) (by omega) 4
      (by omega), rfl, rfl, rfl⟩
  obtain ⟨out, c₂, hr₂, hb, hm₂, hk₂, hc₂⟩ :=
    selectInitFallbackCubeRoot_runs (ω := ω) (input := 119) hroot (st := ready)
      (show ready.regs 119 = y by simp [ready]) hpow (by omega)
  dsimp [y] at hc₂
  exact ⟨out, c₁ + c₂ + 12, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂ + 11, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨ready, 10, c₂, hpower, hr₂, by omega⟩), by omega⟩),
    hb, hm₂.trans hm₁, fun r h119 hres =>
      (hk₂ r hres).trans (by simpa [ready, h119] using hk₁ r h119), by omega⟩

/-- Compute the pruning height used in the fallback charge from the
reciprocal conductance and the fallback size exponent. -/
@[expose] def initFallbackHeight (den exp : Expr) : Expr :=
  .bin .add (.bin .mul (.bin .mul (.const 4)
    (.bin .add (.bin .mul (.const 40) den) (.const 1)))
    (.bin .add exp (.const 2))) (.const 2)

/-- The height expression implements the height in the fallback bound. -/
theorem initFallbackHeight_eval {w d b : ℕ} {den exp : Expr} {st : State}
    (hd : Expr.eval w st den = some d) (hb : Expr.eval w st exp = some b)
    (hw : 40 < 2 ^ w) (hfit : 4 * (40 * d + 1) * (b + 2) + 2 < 2 ^ w) :
    Expr.eval w st (initFallbackHeight den exp) = some (4 * (40 * d + 1) * (b + 2) + 2) := by
  have hmul : 4 * (40 * d + 1) ≤ 4 * (40 * d + 1) * (b + 2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hbnd : b + 2 ≤ 4 * (40 * d + 1) * (b + 2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  simp [initFallbackHeight, Expr.eval, BinOp.eval, hd, hb, hw, hfit,
    show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
    show 40 * d < 2 ^ w by omega, show 40 * d + 1 < 2 ^ w by omega,
    show 4 * (40 * d + 1) < 2 ^ w by omega, show b + 2 < 2 ^ w by omega,
    show 4 * (40 * d + 1) * (b + 2) < 2 ^ w by omega]

/-- Evaluate the fallback charge after its pruning height and size
threshold have been computed. -/
@[expose] def initFallbackCost (den size height : Expr) : Expr :=
  let lin := Expr.bin .add (.bin .mul (.const 2480) size) (.bin .mul (.const 10) den)
  let h₁ := Expr.bin .add (.bin .mul (.const 4) height) (.const 14)
  let h₂ := Expr.bin .add (.bin .mul (.const 4) height) (.const 4)
  let nodes := Expr.bin .add (.bin .mul (.const 2) size) (.const 1)
  let prune := Expr.bin .mul (.const 360) (.bin .mul (.bin .mul h₁ h₂) nodes)
  .bin .add (.bin .add (.bin .add lin (.bin .mul (.const 30)
    (.bin .add height (.const 1)))) prune) (.const 1221)

set_option maxRecDepth 4096 in
/-- The expression combines the linear and pruning terms in the
fallback cost bound. -/
theorem initFallbackCost_eval {w d z H : ℕ} {den size height : Expr} {st : State}
    (hd : Expr.eval w st den = some d) (hz : Expr.eval w st size = some z)
    (hH : Expr.eval w st height = some H) (hw : 2480 < 2 ^ w)
    (hfit : 2480 * z + 10 * d + 30 * (H + 1) +
      360 * ((4 * H + 14) * (4 * H + 4) * (2 * z + 1)) + 1221 < 2 ^ w) :
    Expr.eval w st (initFallbackCost den size height) =
      some (Expander.pruneTimeBound (2 * z) z H + 2000 * z + 10 * d + 1000) := by
  let x := 4 * H + 14
  let y := 4 * H + 4
  let n := 2 * z + 1
  let prod := x * y * n
  have hp₁ : x ≤ x * y := Nat.le_mul_of_pos_right _ (by dsimp [y]; omega)
  have hp₂ : y ≤ x * y := Nat.le_mul_of_pos_left _ (by dsimp [x]; omega)
  have hp₃ : x * y ≤ prod := Nat.le_mul_of_pos_right _ (by dsimp [n]; omega)
  have hp₄ : n ≤ prod := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by dsimp [x]; omega) (by dsimp [y]; omega))
  have hp₅ : prod ≤ 360 * prod := Nat.le_mul_of_pos_left _ (by decide)
  change _ + 360 * prod + _ < 2 ^ w at hfit
  have hprod : prod < 2 ^ w := by omega
  have hlin : H + 1 ≤ 30 * (H + 1) := by omega
  have hresult : Expander.pruneTimeBound (2 * z) z H + 2000 * z + 10 * d + 1000 =
      2480 * z + 10 * d + 30 * (H + 1) + 360 * prod + 1221 := by
    unfold Expander.pruneTimeBound
    dsimp [prod, x, y, n]
    omega
  have hX : 4 * H + 14 < 2 ^ w := hp₁.trans_lt (hp₃.trans_lt hprod)
  have hY : 4 * H + 4 < 2 ^ w := hp₂.trans_lt (hp₃.trans_lt hprod)
  have hN : 2 * z + 1 < 2 ^ w := hp₄.trans_lt hprod
  have hXY : (4 * H + 14) * (4 * H + 4) < 2 ^ w := hp₃.trans_lt hprod
  have hP : (4 * H + 14) * (4 * H + 4) * (2 * z + 1) < 2 ^ w := hprod
  have hC : 360 * prod < 2 ^ w := (Nat.le_add_left _ _).trans_lt ((Nat.le_add_right _ _).trans_lt hfit)
  have hC' : 360 * ((4 * H + 14) * (4 * H + 4) * (2 * z + 1)) < 2 ^ w := hC
  have hPartial : 2480 * z + 10 * d + 30 * (H + 1) + 360 * prod < 2 ^ w := (Nat.le_add_right _ _).trans_lt hfit
  have hFinal := hfit
  dsimp [prod, x, y, n] at hPartial hFinal ⊢
  rw [hresult]
  simp [initFallbackCost, Expr.eval, BinOp.eval, hd, hz, hH, hw,
    hX, hY, hN, hXY, hP, hC', hPartial, hFinal, prod, x, y, n,
    show 4 * H < 2 ^ w by omega, show 2 * z < 2 ^ w by omega,
    show H + 1 < 2 ^ w by omega,
    show 2480 * z < 2 ^ w by omega, show 10 * d < 2 ^ w by omega,
    show 30 * (H + 1) < 2 ^ w by omega,
    show 2480 * z + 10 * d < 2 ^ w by omega,
    show 2480 * z + 10 * d + 30 * (H + 1) < 2 ^ w by omega,
    show 360 < 2 ^ w by omega, show 30 < 2 ^ w by omega, show 10 < 2 ^ w by omega,
    show 14 < 2 ^ w by omega, show 4 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
    show 1 < 2 ^ w by omega, show 1221 < 2 ^ w by omega]

/-- Compute the capped fallback size from the original pruning exponent
and the bit length of three times the edge cap plus one. -/
@[expose] def initFallbackCappedSize (exponent capBits : Expr) : Expr :=
  .bin .shiftLeft (.const 1) (.bin .sub exponent (.bin .sub exponent capBits))

/-- The shift count is the smaller of the two computed exponents. -/
theorem initFallbackCappedSize_eval {w d M : ℕ} {exponent capBits : Expr} {st : State}
    (hb : Expr.eval w st exponent = some (Expander.PathDSProg.zStarExp d))
    (hm : Expr.eval w st capBits = some (Nat.log 2 (3 * M + 1) + 1))
    (hw : 1 < 2 ^ w)
    (hExp : Expander.PathDSProg.zStarExp d < 2 ^ w)
    (hSize : Expander.PathDSProg.zCap d M < 2 ^ w) :
    Expr.eval w st (initFallbackCappedSize exponent capBits) =
      some (Expander.PathDSProg.zCap d M) := by
  let b := Expander.PathDSProg.zStarExp d
  let k := Nat.log 2 (3 * M + 1) + 1
  have hsub : b - k < 2 ^ w := (Nat.sub_le _ _).trans_lt hExp
  have hmin : b - (b - k) = min b k := by omega
  have hword : min b k < 2 ^ w := (min_le_left _ _).trans_lt hExp
  have hpow : 2 ^ min b k < 2 ^ w := hSize
  change Expr.eval w st (initFallbackCappedSize exponent capBits) = some (2 ^ min b k)
  change Expr.eval w st exponent = some b at hb
  change Expr.eval w st capBits = some k at hm
  simp [initFallbackCappedSize, Expr.eval, BinOp.eval, hb, hm, hw, hsub, hmin, hword,
    Nat.shiftLeft_eq, hpow]

/-- Compute the capped size with one bit-length call and one shift. -/
@[expose] def computeInitFallbackCappedSize (bits capReg expReg bitsReg outReg : ℕ) : Stmt :=
  .call bitsReg bits [.bin .add (.bin .mul (.const 3) (.reg capReg)) (.const 1)] ;;
  .assign outReg (initFallbackCappedSize (.reg expReg) (.reg bitsReg))

/-- The edge cap is read from a register, and the original pruning
exponent remains available when the two output registers are distinct from it. -/
theorem computeInitFallbackCappedSize_runs {w bits capReg expReg bitsReg outReg d M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hcap : st.regs capReg = M) (hexp : st.regs expReg = Expander.PathDSProg.zStarExp d)
    (hne : expReg ≠ bitsReg) (hw : 3 < 2 ^ w)
    (hfit : 3 * M + 1 < 2 ^ w)
    (hExp : Expander.PathDSProg.zStarExp d < 2 ^ w)
    (hSize : Expander.PathDSProg.zCap d M < 2 ^ w) :
    ∃ out cost, Runs w p ω (computeInitFallbackCappedSize bits capReg expReg bitsReg outReg)
        st .normal out cost ∧
      out.regs outReg = Expander.PathDSProg.zCap d M ∧ out.mem = st.mem ∧
      (∀ r, r ≠ bitsReg → r ≠ outReg → out.regs r = st.regs r) ∧
      cost ≤ 14 * (3 * M + 1).size + 21 := by
  have hargs : evalArgs w st [.bin .add (.bin .mul (.const 3) (.reg capReg)) (.const 1)] =
      some [3 * M + 1] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hcap, hw, hfit,
      show 1 < 2 ^ w by omega, show 3 * M < 2 ^ w by omega]
  obtain ⟨mid, cost, value, hr, hp, hv, hk, hc⟩ :=
    runs_call_of_meetsContract (r := bitsReg) hbits hargs (by simpa using hfit) ⟨_, rfl⟩ ω
  obtain ⟨hm, hval⟩ := hp
  have hsize : (3 * M + 1).size = Nat.log 2 (3 * M + 1) + 1 := by
    have hu := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (3 * M + 1))
    have hl : ¬ (3 * M + 1).size ≤ Nat.log 2 (3 * M + 1) := by
      intro h
      exact (Nat.size_le.mp h).not_ge (Nat.pow_log_le_self 2 (by omega : 3 * M + 1 ≠ 0))
    omega
  have he := initFallbackCappedSize_eval (w := w) (d := d) (M := M)
    (st := mid) (exponent := .reg expReg) (capBits := .reg bitsReg)
    (by simpa [Expr.eval] using (hk expReg hne).trans hexp)
    (by simpa [Expr.eval] using hv.trans (hval.trans hsize)) (by omega) hExp hSize
  let out := {mid with regs := Function.update mid.regs outReg (Expander.PathDSProg.zCap d M)}
  have hr₂ : Runs w p ω (.assign outReg (initFallbackCappedSize (.reg expReg) (.reg bitsReg)))
      mid .normal out 8 :=
    runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
  refine ⟨out, cost + 9, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 8, hr, hr₂, rfl⟩),
    by simp [out], hm, fun r hb ho => by simpa [out, ho] using hk r hb, ?_⟩
  simp [Num.IPM.bitLengthContract, argsSize, Expr.size, List.getD] at hc
  omega

set_option maxRecDepth 4096 in
/-- With the capped size and the original pruning height, the same
arithmetic expression computes the merged fallback charge exactly. -/
theorem initFallbackCost_eval_cap {w d M : ℕ} {den size height : Expr} {st : State}
    (hd : Expr.eval w st den = some d)
    (hz : Expr.eval w st size = some (Expander.PathDSProg.zCap d M))
    (hH : Expr.eval w st height =
      some (4 * (40 * d + 1) * (Expander.PathDSProg.zStarExp d + 2) + 2))
    (hw : 2480 < 2 ^ w) (hfit : Expander.PathDSProg.fbCostCap d M < 2 ^ w) :
    Expr.eval w st (initFallbackCost den size height) = some (Expander.PathDSProg.fbCostCap d M) := by
  let z := Expander.PathDSProg.zCap d M
  let H := 4 * (40 * d + 1) * (Expander.PathDSProg.zStarExp d + 2) + 2
  change Expander.pruneTimeBound (2 * z) z H + 2000 * z + 10 * d + 1000 < 2 ^ w at hfit
  have hword : 2480 * z + 10 * d + 30 * (H + 1) +
      360 * ((4 * H + 14) * (4 * H + 4) * (2 * z + 1)) + 1221 < 2 ^ w := by
    unfold Expander.pruneTimeBound at hfit
    omega
  exact initFallbackCost_eval hd hz hH hw hword

/-- Compute the fallback charge from the reciprocal conductance and
its computed size exponent. Register 118 holds the pruning height. -/
@[expose] def storeInitFallbackCost (denReg expReg resultReg : ℕ) : Stmt :=
  .assign 118 (initFallbackHeight (.reg denReg) (.reg expReg)) ;;
  .assign resultReg (initFallbackCost (.reg denReg) (.bin .shiftLeft (.const 1) (.reg expReg)) (.reg 118))

/-- From the exact size exponent, the machine computes the exact
fallback charge, preserving memory and the path interval registers. -/
theorem storeInitFallbackCost_runs {w d denReg expReg resultReg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : st.regs denReg = d) (hb : st.regs expReg = Expander.PathDSProg.zStarExp d)
    (hden : denReg ≠ 118) (hexp : expReg ≠ 118) (hw : 2480 < 2 ^ w) :
    let b := Expander.PathDSProg.zStarExp d
    let z := Expander.PathDSProg.zStarImpl d
    let H := 4 * (40 * d + 1) * (b + 2) + 2
    H < 2 ^ w → z < 2 ^ w →
    2480 * z + 10 * d + 30 * (H + 1) +
      360 * ((4 * H + 14) * (4 * H + 4) * (2 * z + 1)) + 1221 < 2 ^ w →
    ∃ out, Runs w p ω (storeInitFallbackCost denReg expReg resultReg) st .normal out 55 ∧
      out.regs resultReg = Expander.PathDSProg.fbCostBound d ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 118 → r ≠ resultReg → out.regs r = st.regs r) := by
  dsimp only
  intro hheight hz hfit
  let H := 4 * (40 * d + 1) * (Expander.PathDSProg.zStarExp d + 2) + 2
  let first := initFallbackHeight (.reg denReg) (.reg expReg)
  let second := initFallbackCost (.reg denReg) (.bin .shiftLeft (.const 1) (.reg expReg)) (.reg 118)
  let mid := {st with regs := Function.update st.regs 118 H}
  let out := {mid with regs := Function.update mid.regs resultReg (Expander.PathDSProg.fbCostBound d)}
  have hr₁ : Runs w p ω (.assign 118 first) st .normal mid (first.size + 1) :=
    runs_assign_iff.mpr ⟨_, initFallbackHeight_eval (by simp [Expr.eval, hd]) (by simp [Expr.eval, hb])
      (by omega) hheight, rfl, rfl, rfl⟩
  have hzEval : Expr.eval w mid (.bin .shiftLeft (.const 1) (.reg expReg)) =
      some (Expander.PathDSProg.zStarImpl d) := by
    simp [Expr.eval, BinOp.eval, Nat.shiftLeft_eq, mid, hexp, hb, Expander.PathDSProg.zStarImpl,
      show 1 < 2 ^ w by omega, show 2 ^ Expander.PathDSProg.zStarExp d < 2 ^ w from hz]
  have hval := initFallbackCost_eval (den := .reg denReg) (height := .reg 118)
    (st := mid) (by simp [Expr.eval, mid, hden, hd]) hzEval
    (by simp [Expr.eval, mid] : Expr.eval w mid (.reg 118) = some H) hw hfit
  have hr₂ : Runs w p ω (.assign resultReg second) mid .normal out (second.size + 1) :=
    runs_assign_iff.mpr ⟨_, hval, rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, _, _, hr₁, hr₂, rfl⟩),
    by simp [out], rfl, fun r h118 hresult => by simp [out, mid, h118, hresult]⟩

/-- Use the capped size for the cost and the uncapped exponent for the
pruning height. -/
@[expose] def storeInitFallbackCappedCost (denReg expReg sizeReg resultReg : ℕ) : Stmt :=
  .assign 118 (initFallbackHeight (.reg denReg) (.reg expReg)) ;;
  .assign resultReg (initFallbackCost (.reg denReg) (.reg sizeReg) (.reg 118))

/-- Store the exact runtime fallback charge while keeping all registers
outside the height and result registers. -/
theorem storeInitFallbackCappedCost_runs {w d M denReg expReg sizeReg resultReg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : st.regs denReg = d) (hb : st.regs expReg = Expander.PathDSProg.zStarExp d)
    (hs : st.regs sizeReg = Expander.PathDSProg.zCap d M)
    (hden : denReg ≠ 118) (hsize : sizeReg ≠ 118) (hw : 2480 < 2 ^ w)
    (hheight : 4 * (40 * d + 1) * (Expander.PathDSProg.zStarExp d + 2) + 2 < 2 ^ w)
    (hfit : Expander.PathDSProg.fbCostCap d M < 2 ^ w) :
    ∃ out, Runs w p ω (storeInitFallbackCappedCost denReg expReg sizeReg resultReg)
        st .normal out 51 ∧
      out.regs resultReg = Expander.PathDSProg.fbCostCap d M ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 118 → r ≠ resultReg → out.regs r = st.regs r) := by
  let H := 4 * (40 * d + 1) * (Expander.PathDSProg.zStarExp d + 2) + 2
  let first := initFallbackHeight (.reg denReg) (.reg expReg)
  let second := initFallbackCost (.reg denReg) (.reg sizeReg) (.reg 118)
  let mid := {st with regs := Function.update st.regs 118 H}
  let out := {mid with regs := Function.update mid.regs resultReg (Expander.PathDSProg.fbCostCap d M)}
  have hr₁ : Runs w p ω (.assign 118 first) st .normal mid (first.size + 1) :=
    runs_assign_iff.mpr ⟨_, initFallbackHeight_eval (by simp [Expr.eval, hd]) (by simp [Expr.eval, hb])
      (by omega) hheight, rfl, rfl, rfl⟩
  have hval := initFallbackCost_eval_cap (den := .reg denReg) (size := .reg sizeReg) (height := .reg 118)
    (st := mid) (by simp [Expr.eval, mid, hden, hd]) (by simp [Expr.eval, mid, hsize, hs])
    (by simp [Expr.eval, mid] : Expr.eval w mid (.reg 118) = some H) hw hfit
  have hr₂ : Runs w p ω (.assign resultReg second) mid .normal out (second.size + 1) :=
    runs_assign_iff.mpr ⟨_, hval, rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, _, _, hr₁, hr₂, rfl⟩),
    by simp [out], rfl, fun r h118 hresult => by simp [out, mid, h118, hresult]⟩

/-- Compute the fallback cost using the reciprocal conductance in a
runtime register. The exponent is saved in register 120. -/
@[expose] def computeInitFallbackCost (bits root denReg result : ℕ) : Stmt :=
  initFallbackSizeExponent bits root denReg 120 ;; storeInitFallbackCost denReg 120 result

/-- The runtime reciprocal determines the exact fallback cost. -/
theorem computeInitFallbackCost_runs {w bits root denReg result d : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w))
    (hd : st.regs denReg = d) (hdPos : 0 < d)
    (h118 : denReg ≠ 118) (h119 : denReg ≠ 119) (h120 : denReg ≠ 120)
    (hw : 2480 < 2 ^ w) (hfit : 10 * d < 2 ^ w)
    (hpow : (Nat.log 2 (10 * d) + 1) ^ 4 + 1 < 2 ^ w) :
    let b := Expander.PathDSProg.zStarExp d
    let z := Expander.PathDSProg.zStarImpl d
    let H := 4 * (40 * d + 1) * (b + 2) + 2
    H < 2 ^ w → z < 2 ^ w →
    2480 * z + 10 * d + 30 * (H + 1) +
      360 * ((4 * H + 14) * (4 * H + 4) * (2 * z + 1)) + 1221 < 2 ^ w →
    ∃ out cost, Runs w p ω (computeInitFallbackCost bits root denReg result) st .normal out cost ∧
      out.regs result = Expander.PathDSProg.fbCostBound d ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 118 → r ≠ 119 → r ≠ 120 → r ≠ result → out.regs r = st.regs r) ∧
      cost ≤ 14 * (10 * d).size + 89 * ((Nat.log 2 (10 * d) + 1) ^ 4 + 1).size + 107 := by
  dsimp only
  intro hheight hz hcost
  obtain ⟨mid, cost, hr₁, hb, hm₁, hk₁, hc⟩ :=
    initFallbackSizeExponent_runs (ω := ω) hbits hroot hd hdPos (by omega) hfit hpow
  obtain ⟨out, hr₂, hf, hm₂, hk₂⟩ :=
    storeInitFallbackCost_runs (p := p) (ω := ω) (resultReg := result)
      ((hk₁ denReg h119 h120).trans hd) hb h118 (by decide) hw hheight hz hcost
  exact ⟨out, cost + 56, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 55, hr₁, hr₂, by omega⟩),
    hf, hm₂.trans hm₁, fun r h118 h119 h120 hres => (hk₂ r h118 hres).trans (hk₁ r h119 h120), by omega⟩

/-- Compute both fallback charges for the query interval. The witness
reciprocal is a fixed parameter, and the input reciprocal is in register 63. -/
@[expose] def computeInitSparsifierQueryCosts (bits root witnessDen : ℕ) : Stmt :=
  .assign 121 (.const witnessDen) ;;
  computeInitFallbackCost bits root 63 116 ;;
  computeInitFallbackCost bits root 121 117

/-- The two computations keep the first charge available while writing the second. -/
theorem computeInitSparsifierQueryCosts_runs {w bits root d e : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {budget : ℕ → ℕ}
    (hd : st.regs 63 = d) (hw : e < 2 ^ w)
    (hcost : ∀ (den denReg result : ℕ) (ready : State),
      ready.regs denReg = den → (den = d ∧ denReg = 63 ∧ result = 116 ∨
        den = e ∧ denReg = 121 ∧ result = 117) →
      ∃ out cost, Runs w p ω (computeInitFallbackCost bits root denReg result) ready .normal out cost ∧
        out.regs result = Expander.PathDSProg.fbCostBound den ∧ out.mem = ready.mem ∧
        (∀ r, r ≠ 118 → r ≠ 119 → r ≠ 120 → r ≠ result → out.regs r = ready.regs r) ∧
        cost ≤ budget den) :
    ∃ out cost, Runs w p ω (computeInitSparsifierQueryCosts bits root e) st .normal out cost ∧
      out.regs 116 = Expander.PathDSProg.fbCostBound d ∧
      out.regs 117 = Expander.PathDSProg.fbCostBound e ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 116 → r ≠ 117 → r ≠ 118 → r ≠ 119 → r ≠ 120 → r ≠ 121 →
        out.regs r = st.regs r) ∧ cost ≤ budget d + budget e + 4 := by
  let ready := {st with regs := Function.update st.regs 121 e}
  have hr₁ : Runs w p ω (.assign 121 (.const e)) st .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  obtain ⟨mid, c₁, hr₂, h116, hm₁, hk₁, hc₁⟩ :=
    hcost d 63 116 ready (by simpa [ready] using hd) (Or.inl ⟨rfl, rfl, rfl⟩)
  obtain ⟨out, c₂, hr₃, h117, hm₂, hk₂, hc₂⟩ :=
    hcost e 121 117 mid ((hk₁ 121 (by decide) (by decide) (by decide) (by decide)).trans (by simp [ready]))
      (Or.inr ⟨rfl, rfl, rfl⟩)
  exact ⟨out, 2 + (c₁ + c₂ + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨ready, 2, c₁ + c₂ + 1, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₂, hr₃, rfl⟩), rfl⟩),
    (hk₂ 116 (by decide) (by decide) (by decide) (by decide)).trans h116,
    h117, hm₂.trans hm₁, fun r h116 h117 h118 h119 h120 h121 =>
      (hk₂ r h118 h119 h120 h117).trans ((hk₁ r h118 h119 h120 h116).trans (by simp [ready, h121])),
    by omega⟩

/-- Compute both query charges using the bit-length and cube-root
procedures. The fit conditions apply to each of the two reciprocals. -/
theorem computeInitSparsifierQueryCosts_of_fits {w bits root d e : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w))
    (hd : st.regs 63 = d) (he : e < 2 ^ w) (hw : 2480 < 2 ^ w)
    (hfit : ∀ n, n = d ∨ n = e →
      let b := Expander.PathDSProg.zStarExp n
      let z := Expander.PathDSProg.zStarImpl n
      let H := 4 * (40 * n + 1) * (b + 2) + 2
      0 < n ∧ 10 * n < 2 ^ w ∧ (Nat.log 2 (10 * n) + 1) ^ 4 + 1 < 2 ^ w ∧
        H < 2 ^ w ∧ z < 2 ^ w ∧
        2480 * z + 10 * n + 30 * (H + 1) +
          360 * ((4 * H + 14) * (4 * H + 4) * (2 * z + 1)) + 1221 < 2 ^ w) :
    let budget (n : ℕ) := 14 * (10 * n).size + 89 * ((Nat.log 2 (10 * n) + 1) ^ 4 + 1).size + 107
    ∃ out cost, Runs w p ω (computeInitSparsifierQueryCosts bits root e) st .normal out cost ∧
      out.regs 116 = Expander.PathDSProg.fbCostBound d ∧
      out.regs 117 = Expander.PathDSProg.fbCostBound e ∧ out.mem = st.mem ∧
      (∀ r, r < 112 → out.regs r = st.regs r) ∧ cost ≤ budget d + budget e + 4 := by
  dsimp only
  have hcall := computeInitSparsifierQueryCosts_runs (p := p) (ω := ω)
    (bits := bits) (root := root)
    (budget := fun n => 14 * (10 * n).size + 89 * ((Nat.log 2 (10 * n) + 1) ^ 4 + 1).size + 107)
    hd he
  specialize hcall (by
    intro n denReg result ready hn hcase
    have hden : n = d ∨ n = e := hcase.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    obtain ⟨hpos, hword, hpow, hheight, hz, hcost⟩ := hfit n hden
    have h118 : denReg ≠ 118 := by rcases hcase with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> decide
    have h119 : denReg ≠ 119 := by rcases hcase with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> decide
    have h120 : denReg ≠ 120 := by rcases hcase with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> decide
    exact computeInitFallbackCost_runs (ω := ω) hbits hroot hn hpos h118 h119 h120
      hw hword hpow hheight hz hcost)
  obtain ⟨out, cost, hr, hi, hj, hm, hk, hc⟩ := hcall
  exact ⟨out, cost, hr, hi, hj, hm,
    fun r hr => hk r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hc⟩

/-- Scale the two fallback costs in registers 116 and 117 to match
the path endpoints. -/
@[expose] def scaleInitSparsifierQueryCosts : Stmt :=
  .assign 112 (.bin .mul (.reg 4) (.reg 116)) ;;
  .assign 113 (.bin .mul (.reg 4) (.reg 117))

/-- Scaling preserves the path endpoints and the length-factor workspace. -/
theorem scaleInitSparsifierQueryCosts_runs {w scale inputCost witnessCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (hi : st.regs 116 = inputCost) (hj : st.regs 117 = witnessCost)
    (hif : scale * inputCost < 2 ^ w) (hjf : scale * witnessCost < 2 ^ w) :
    ∃ out, Runs w p ω scaleInitSparsifierQueryCosts st .normal out 9 ∧
      out.regs 112 = scale * inputCost ∧ out.regs 113 = scale * witnessCost ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 112 → r ≠ 113 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 112 (scale * inputCost)}
  let out := {mid with regs := Function.update mid.regs 113 (scale * witnessCost)}
  have hr₁ : Runs w p ω (.assign 112 (.bin .mul (.reg 4) (.reg 116))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hs, hi, hif], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 113 (.bin .mul (.reg 4) (.reg 117))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hs, hj, hjf], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r h112 h113 => by simp [out, mid, h112, h113]⟩

/-- Store the query interval alongside the separate path intervals. -/
@[expose] def finishInitSparsifierQueryFactor : Stmt :=
  .assign 114 (initSparsifierQueryEndpoint 60 40) ;;
  .assign 115 (initSparsifierQueryEndpoint 61 42)

/-- Both query endpoints are computed without changing the path intervals. -/
theorem finishInitSparsifierQueryFactor_runs {w a b d e inputCharge witnessCharge : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 60 = a) (hb : st.regs 61 = b) (hd : st.regs 40 = d) (he : st.regs 42 = e)
    (hi : st.regs 112 = inputCharge) (hj : st.regs 113 = witnessCharge)
    (hlo : max (a + inputCharge) (d + witnessCharge) < 2 ^ w)
    (hhi : max (b + inputCharge) (e + witnessCharge) < 2 ^ w) :
    ∃ out, Runs w p ω finishInitSparsifierQueryFactor st .normal out 25 ∧
      out.regs 114 = max (a + inputCharge) (d + witnessCharge) ∧
      out.regs 115 = max (b + inputCharge) (e + witnessCharge) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 114 → r ≠ 115 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 114 (max (a + inputCharge) (d + witnessCharge))}
  let out := {mid with regs := Function.update mid.regs 115 (max (b + inputCharge) (e + witnessCharge))}
  have hr₁ : Runs w p ω (.assign 114 (initSparsifierQueryEndpoint 60 40)) st .normal mid 12 :=
    runs_assign_iff.mpr ⟨_, initSparsifierQueryEndpoint_eval ha hd hi hj hlo, rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 115 (initSparsifierQueryEndpoint 61 42)) mid .normal out 12 :=
    runs_assign_iff.mpr ⟨_, initSparsifierQueryEndpoint_eval
      (by simpa [mid] using hb) (by simpa [mid] using he) (by simpa [mid] using hi)
      (by simpa [mid] using hj) hhi, rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 12, 12, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r h114 h115 => by simp [out, mid, h114, h115]⟩

/-- Compute the query enclosure from both path intervals and their
unscaled fallback charges. -/
@[expose] def encloseInitSparsifierQueryFactor : Stmt :=
  scaleInitSparsifierQueryCosts ;; finishInitSparsifierQueryFactor

/-- The machine endpoints enclose the query factor of the current
Section 8 parameters when the charged endpoints fit in a word. -/
theorem encloseInitSparsifierQueryFactor_runs
    {w Kγ c M den a b d e scale : ℕ} {K cDeg phiConst : ℝ} {paths : Spanner.PathDSTool}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hQuery : paths.γ_query = Expander.csGammaQuery Kγ c K)
    (hden : 0 < den) (hs : 0 < scale) (hscale : st.regs 4 = scale)
    (ha : st.regs 60 = a) (hb : st.regs 61 = b) (hd : st.regs 40 = d) (he : st.regs 42 = e)
    (hi : st.regs 116 = Expander.PathDSProg.fbCostBound den)
    (hj : st.regs 117 = Expander.PathDSProg.fbCostBound (Nat.ceil (1 / phiConst))) :
    let phiMin := 1 / (den : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let ci := scale * Expander.PathDSProg.fbCostBound den
    let cj := scale * Expander.PathDSProg.fbCostBound (Nat.ceil (1 / phiConst))
    (a : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiMin M →
    Expander.csGammaExpPath Kγ c K phiMin M ≤ (b : ℝ) / scale →
    (d : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiConst cap →
    Expander.csGammaExpPath Kγ c K phiConst cap ≤ (e : ℝ) / scale →
    max (a + ci) (d + cj) < 2 ^ w → max (b + ci) (e + cj) < 2 ^ w →
    ∃ out, Runs w p ω encloseInitSparsifierQueryFactor st .normal out 35 ∧
      (out.regs 114 : ℝ) / scale ≤ Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
      Spanner.capGammaQuery cDeg phiConst paths phiMin M ≤ (out.regs 115 : ℝ) / scale ∧
      out.mem = st.mem ∧ (∀ r, r < 112 → out.regs r = st.regs r) := by
  dsimp only
  intro al au dl du hfitLo hfitHi
  have hci := (le_max_left _ _).trans_lt hfitLo
  have hcj := (le_max_right _ _).trans_lt hfitLo
  obtain ⟨mid, hr₁, h112, h113, hm₁, hk⟩ :=
    scaleInitSparsifierQueryCosts_runs (p := p) (ω := ω) hscale hi hj
      ((Nat.le_add_left _ _).trans_lt hci) ((Nat.le_add_left _ _).trans_lt hcj)
  obtain ⟨out, hr₂, h114, h115, hm₂, hk₂⟩ :=
    finishInitSparsifierQueryFactor_runs (ω := ω)
      ((hk 60 (by decide) (by decide)).trans ha) ((hk 61 (by decide) (by decide)).trans hb)
      ((hk 40 (by decide) (by decide)).trans hd) ((hk 42 (by decide) (by decide)).trans he)
      h112 h113 hfitLo hfitHi
  obtain ⟨hlo, hhi⟩ :=
    initSparsifierQueryFactor_bounds Kγ c M den a b d e scale K cDeg phiConst paths
      hQuery hden hs al au dl du
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 9, 25, hr₁, hr₂, rfl⟩),
    by simpa only [h114] using hlo, by simpa only [h115] using hhi, hm₂.trans hm₁,
    fun r hr => (hk₂ r (by omega) (by omega)).trans (hk r (by omega) (by omega))⟩

/-- Compute both fallback charges and use them to enclose the query factor. -/
@[expose] def computeInitSparsifierQueryFactor (bits root witnessDen : ℕ) : Stmt :=
  computeInitSparsifierQueryCosts bits root witnessDen ;; encloseInitSparsifierQueryFactor

/-- Given the path intervals, the program computes the charged query
interval without changing the previously allocated memory. -/
theorem computeInitSparsifierQueryFactor_runs
    {w bits root cost M Kγ c den scale : ℕ} {K cDeg phiConst : ℝ} {paths : Spanner.PathDSTool}
    {p : Program} {ω : ℕ → Bool} {st charged : State}
    (hQuery : paths.γ_query = Expander.csGammaQuery Kγ c K)
    (hden : 0 < den) (hs : 0 < scale) (hscale : charged.regs 4 = scale)
    (hr : Runs w p ω (computeInitSparsifierQueryCosts bits root (Nat.ceil (1 / phiConst)))
      st .normal charged cost)
    (hi : charged.regs 116 = Expander.PathDSProg.fbCostBound den)
    (hj : charged.regs 117 = Expander.PathDSProg.fbCostBound (Nat.ceil (1 / phiConst)))
    (hm : charged.mem = st.mem)
    (hk : ∀ r, r < 112 → charged.regs r = st.regs r) :
    let phiMin := 1 / (den : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let ci := scale * Expander.PathDSProg.fbCostBound den
    let cj := scale * Expander.PathDSProg.fbCostBound (Nat.ceil (1 / phiConst))
    (charged.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiMin M →
    Expander.csGammaExpPath Kγ c K phiMin M ≤ (charged.regs 61 : ℝ) / scale →
    (charged.regs 40 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiConst cap →
    Expander.csGammaExpPath Kγ c K phiConst cap ≤ (charged.regs 42 : ℝ) / scale →
    max (charged.regs 60 + ci) (charged.regs 40 + cj) < 2 ^ w →
    max (charged.regs 61 + ci) (charged.regs 42 + cj) < 2 ^ w →
    ∃ out, Runs w p ω (computeInitSparsifierQueryFactor bits root (Nat.ceil (1 / phiConst)))
        st .normal out (cost + 36) ∧
      (out.regs 114 : ℝ) / scale ≤ Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
      Spanner.capGammaQuery cDeg phiConst paths phiMin M ≤ (out.regs 115 : ℝ) / scale ∧
      out.mem = st.mem ∧ (∀ r, r < 112 → out.regs r = st.regs r) := by
  dsimp only
  intro hlo hhi hwl hwh hfitLo hfitHi
  obtain ⟨out, hf, hl, hu, hmem, hregs⟩ :=
    encloseInitSparsifierQueryFactor_runs (ω := ω) hQuery hden hs hscale rfl rfl rfl rfl hi hj
      hlo hhi hwl hwh hfitLo hfitHi
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨charged, cost, 35, hr, hf, by omega⟩),
    hl, hu, hmem.trans hm, fun r hr => (hregs r hr).trans (hk r hr)⟩

/-- Evaluate the path pair before charging it for fallback queries. -/
@[expose] def computeInitConcreteSparsifierQuery
    (qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg
      root witnessDen : ℕ) : Stmt :=
  computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c decK thr
    coeffLo coeffHi coeffBits cDeg ;;
  computeInitSparsifierQueryFactor bits root witnessDen

/-- A completed path pair supplies the two intervals for the charged query
factor. The witness uses effective conductance at its own edge cap. -/
theorem computeInitConcreteSparsifierQuery_of_pair
    {w qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits
      M scale cDeg root pathCost chargeCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready charged : State}
    {K phiConst : ℝ} {paths : Spanner.PathDSTool}
    (hquery : paths.γ_query = Expander.csGammaQuery Kγ c K)
    (hc : 0 < c) (hs : 0 < scale) (hscale : ready.regs 4 = scale) :
    let den := Expander.maxPhiDenOf decK thr M
    let phiMin := 1 / (den : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let witnessDen := Nat.ceil (1 / phiConst)
    let ci := scale * Expander.PathDSProg.fbCostBound den
    let cj := scale * Expander.PathDSProg.fbCostBound witnessDen
    Cited.csPhi Kγ c (3 * cap) ≤ phiConst →
    Runs w p ω (computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg) st .normal ready pathCost →
    (ready.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiMin M →
    Expander.csGammaExpPath Kγ c K phiMin M ≤ (ready.regs 61 : ℝ) / scale →
    (ready.regs 40 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) cap →
    Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) cap ≤ (ready.regs 42 : ℝ) / scale →
    Runs w p ω (computeInitSparsifierQueryCosts bits root witnessDen) ready .normal charged chargeCost →
    charged.regs 116 = Expander.PathDSProg.fbCostBound den →
    charged.regs 117 = Expander.PathDSProg.fbCostBound witnessDen →
    charged.mem = ready.mem →
    (∀ r, r < 112 → charged.regs r = ready.regs r) →
    max (ready.regs 60 + ci) (ready.regs 40 + cj) < 2 ^ w →
    max (ready.regs 61 + ci) (ready.regs 42 + cj) < 2 ^ w →
    ∃ out, Runs w p ω (computeInitConcreteSparsifierQuery qEntry bits load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg root witnessDen)
        st .normal out (pathCost + (chargeCost + 36) + 1) ∧
      (out.regs 114 : ℝ) / scale ≤ Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
      Spanner.capGammaQuery cDeg phiConst paths phiMin M ≤ (out.regs 115 : ℝ) / scale ∧
      out.mem = ready.mem ∧ (∀ r, r < 112 → out.regs r = ready.regs r) := by
  dsimp only
  intro hphi hpath al au dl du hcharges hi hj hm hk hfitLo hfitHi
  have hphiEq := initSparsifierWitnessPath_conductance_eq Kγ c
    (Spanner.capM_W cDeg (1 / (Expander.maxPhiDenOf decK thr M : ℝ)) M) K phiConst hc hphi
  have h60 := hk 60 (by decide)
  have h61 := hk 61 (by decide)
  have h40 := hk 40 (by decide)
  have h42 := hk 42 (by decide)
  obtain ⟨out, hr, hl, hu, hmem, hregs⟩ :=
    computeInitSparsifierQueryFactor_runs (cDeg := (cDeg : ℝ)) hquery (Expander.maxPhiDenOf_pos decK thr M) hs
      ((hk 4 (by decide)).trans hscale) hcharges hi hj hm hk
      (by simpa only [h60] using al) (by simpa only [h61] using au)
      (by simpa only [h40, hphiEq] using dl) (by simpa only [h42, hphiEq] using du)
      (by simpa only [h60, h40] using hfitLo) (by simpa only [h61, h42] using hfitHi)
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨ready, _, _, hpath, hr, rfl⟩), hl, hu, hmem, hregs⟩

/-- Use one path pair to compute both sparsifier factors. -/
@[expose] def computeInitConcreteSparsifierFactors
    (qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg
      root witnessDen : ℕ) : Stmt :=
  computeInitConcreteSparsifierQuery qEntry bits load log pack exp shiftEntry Kγ c decK thr
    coeffLo coeffHi coeffBits cDeg root witnessDen ;;
  finishInitSparsifierLengthFactor

/-- Finishing the length factor preserves the charged query interval.
Both enclosures use the same runtime scale and the same path pair. -/
theorem computeInitConcreteSparsifierFactors_of_query
    {w qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits
      M scale cDeg root cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st pathsReady ready : State}
    {K phiConst : ℝ} {paths : Spanner.PathDSTool}
    (hpaths : paths.γ_ExpPath = Expander.csGammaExpPath Kγ c K)
    (hc : 0 < c) (hs : 0 < scale) (hscale : pathsReady.regs 4 = scale) (hw : 1 < 2 ^ w) :
    let phiMin := 1 / (Expander.maxPhiDenOf decK thr M : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let witnessDen := Nat.ceil (1 / phiConst)
    Cited.csPhi Kγ c (3 * cap) ≤ phiConst →
    (pathsReady.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiMin M →
    Expander.csGammaExpPath Kγ c K phiMin M ≤ (pathsReady.regs 61 : ℝ) / scale →
    (pathsReady.regs 40 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) cap →
    Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) cap ≤ (pathsReady.regs 42 : ℝ) / scale →
    (max (pathsReady.regs 60) (pathsReady.regs 40)) ^ 2 < 2 ^ w →
    (max (pathsReady.regs 61) (pathsReady.regs 42)) ^ 2 + (scale - 1) < 2 ^ w →
    Runs w p ω (computeInitConcreteSparsifierQuery qEntry bits load log pack exp shiftEntry
      Kγ c decK thr coeffLo coeffHi coeffBits cDeg root witnessDen) st .normal ready cost →
    (ready.regs 114 : ℝ) / scale ≤ Spanner.capGammaQuery cDeg phiConst paths phiMin M →
    Spanner.capGammaQuery cDeg phiConst paths phiMin M ≤ (ready.regs 115 : ℝ) / scale →
    (∀ r, r < 112 → ready.regs r = pathsReady.regs r) →
    ∃ out, Runs w p ω (computeInitConcreteSparsifierFactors qEntry bits load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg root witnessDen) st .normal out (cost + 47) ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤ (out.regs 52 : ℝ) / scale ∧
      (out.regs 114 : ℝ) / scale ≤ Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
      Spanner.capGammaQuery cDeg phiConst paths phiMin M ≤ (out.regs 115 : ℝ) / scale ∧
      (scale ≤ max (pathsReady.regs 60) (pathsReady.regs 40) → 0 < out.regs 50) ∧
      out.regs 50 ≤ out.regs 52 ∧ out.regs 52 < 2 ^ w ∧ out.mem = ready.mem ∧
      (∀ r, r ∉ ([31, 32, 33, 39, 41, 50, 52] : List ℕ) → out.regs r = ready.regs r) := by
  dsimp only
  intro hphi al au dl du hlo hhi hrun hql hqu hk
  have hphiEq := initSparsifierWitnessPath_conductance_eq Kγ c
    (Spanner.capM_W cDeg (1 / (Expander.maxPhiDenOf decK thr M : ℝ)) M) K phiConst hc hphi
  obtain ⟨out, hf, hll, hlu, hp, hle, hword, _, _, hmem, hregs⟩ :=
    finishInitSparsifierLengthFactor_runs (cDeg : ℝ) phiConst
      (1 / (Expander.maxPhiDenOf decK thr M : ℝ)) paths M (ω := ω)
      ((hk 4 (by decide)).trans hscale) hs
      (hk 60 (by decide)) (hk 40 (by decide)) (hk 61 (by decide)) (hk 42 (by decide))
      (by rw [hpaths]; exact al) (by rw [hpaths]; exact au)
      (by rw [hpaths, hphiEq]; exact dl) (by rw [hpaths, hphiEq]; exact du)
      hw hlo hhi
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨ready, cost, 46, hrun, hf, by omega⟩),
    hll, hlu, by simpa only [hregs 114 (by decide)] using hql,
    by simpa only [hregs 115 (by decide)] using hqu, hp, hle, hword, hmem, hregs⟩

/-- Complete both factor calculations from the path pair and the
numeric procedures, with a bound on the added machine cost. -/
theorem computeInitConcreteSparsifierFactors_of_pair
    {w qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits
      M scale cDeg root pathCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready : State}
    {K phiConst : ℝ} {paths : Spanner.PathDSTool}
    (hpaths : paths.γ_ExpPath = Expander.csGammaExpPath Kγ c K)
    (hquery : paths.γ_query = Expander.csGammaQuery Kγ c K)
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w))
    (hc : 0 < c) (hs : 0 < scale) (hscale : ready.regs 4 = scale) (hw : 2480 < 2 ^ w) :
    let den := Expander.maxPhiDenOf decK thr M
    let phiMin := 1 / (den : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let witnessDen := Nat.ceil (1 / phiConst)
    let ci := scale * Expander.PathDSProg.fbCostBound den
    let cj := scale * Expander.PathDSProg.fbCostBound witnessDen
    let budget (n : ℕ) := 14 * (10 * n).size + 89 * ((Nat.log 2 (10 * n) + 1) ^ 4 + 1).size + 107
    ready.regs 63 = den → witnessDen < 2 ^ w →
    (∀ n, n = den ∨ n = witnessDen →
      let b := Expander.PathDSProg.zStarExp n
      let z := Expander.PathDSProg.zStarImpl n
      let H := 4 * (40 * n + 1) * (b + 2) + 2
      0 < n ∧ 10 * n < 2 ^ w ∧ (Nat.log 2 (10 * n) + 1) ^ 4 + 1 < 2 ^ w ∧
        H < 2 ^ w ∧ z < 2 ^ w ∧
        2480 * z + 10 * n + 30 * (H + 1) +
          360 * ((4 * H + 14) * (4 * H + 4) * (2 * z + 1)) + 1221 < 2 ^ w) →
    Cited.csPhi Kγ c (3 * cap) ≤ phiConst →
    Runs w p ω (computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg) st .normal ready pathCost →
    (ready.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiMin M →
    Expander.csGammaExpPath Kγ c K phiMin M ≤ (ready.regs 61 : ℝ) / scale →
    (ready.regs 40 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) cap →
    Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) cap ≤ (ready.regs 42 : ℝ) / scale →
    max (ready.regs 60 + ci) (ready.regs 40 + cj) < 2 ^ w →
    max (ready.regs 61 + ci) (ready.regs 42 + cj) < 2 ^ w →
    (max (ready.regs 60) (ready.regs 40)) ^ 2 < 2 ^ w →
    (max (ready.regs 61) (ready.regs 42)) ^ 2 + (scale - 1) < 2 ^ w →
    ∃ out cost, Runs w p ω (computeInitConcreteSparsifierFactors qEntry bits load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg root witnessDen) st .normal out cost ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤ (out.regs 52 : ℝ) / scale ∧
      (out.regs 114 : ℝ) / scale ≤ Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
      Spanner.capGammaQuery cDeg phiConst paths phiMin M ≤ (out.regs 115 : ℝ) / scale ∧
      out.regs 50 ≤ out.regs 52 ∧ out.regs 52 < 2 ^ w ∧ out.mem = ready.mem ∧
      (∀ r, r < 112 → r ∉ ([31, 32, 33, 39, 41, 50, 52] : List ℕ) →
        out.regs r = ready.regs r) ∧
      cost ≤ pathCost + budget den + budget witnessDen + 88 := by
  dsimp only
  intro hd he hfit hphi hpath al au dl du hqlo hqhi hllo hlhi
  obtain ⟨charged, chargeCost, hr, hi, hj, hm, hk, hchargeCost⟩ :=
    computeInitSparsifierQueryCosts_of_fits (ω := ω) hbits hroot hd he hw hfit
  obtain ⟨query, hqr, hql, hqu, hqm, hqk⟩ :=
    computeInitConcreteSparsifierQuery_of_pair hquery hc hs hscale hphi hpath al au dl du
      hr hi hj hm hk hqlo hqhi
  obtain ⟨out, hrun, ll, lu, ql, qu, _, horder, hword, hmem, hregs⟩ :=
    computeInitConcreteSparsifierFactors_of_query hpaths hc hs hscale
      (show 1 < 2 ^ w by omega) hphi al au dl du hllo hlhi hqr hql hqu hqk
  dsimp only at hchargeCost
  exact ⟨out, _, hrun, ll, lu, ql, qu, horder, hword, hmem.trans hqm,
    fun r hr hkeep => (hregs r hkeep).trans (hqk r hr), by omega⟩

end MinCostFlow.MinRatio
