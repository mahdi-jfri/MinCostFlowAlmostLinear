module

public import MinCostFlow.MinRatio.InitSparsifierQueryFactor
public import MinCostFlow.Expander.PathDSProg.BoundsProg

/-!
# Capped fallback charge at Init

Compute the pruning exponent and cap the fallback size by the current
edge bound before evaluating the time charge.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Expander.PathDSProg

/-- A padded edge bound and the fixed decomposition parameters give
power bounds on reciprocal conductance and on the witness edge cap. -/
theorem initSparsifierConductance_power_bounds (decK thr cDeg : ℕ) :
    ∃ dc, ∀ {B M d : ℕ}, 2 ≤ B → M + 2 ≤ B ^ d →
      Expander.maxPhiDenOf decK thr M ≤ B ^ (dc + d) ∧
      Spanner.capM_W cDeg (1 / (Expander.maxPhiDenOf decK thr M : ℝ)) M ≤
        B ^ (Nat.clog 2 cDeg + dc + d + d + 1) := by
  obtain ⟨C, _, hC⟩ := Expander.maxPhiDenOf_le_linear decK thr
  refine ⟨Nat.clog 2 C, ?_⟩
  intro B M d hB hM
  have constant (a : ℕ) : a ≤ B ^ Nat.clog 2 a :=
    (Nat.le_pow_clog (by decide) a).trans (Nat.pow_le_pow_left hB _)
  have hden : Expander.maxPhiDenOf decK thr M ≤ B ^ (Nat.clog 2 C + d) := by
    rw [pow_add]
    exact (show Expander.maxPhiDenOf decK thr M ≤ C * (M + 2) by
      simpa only [pow_one] using hC M).trans (Nat.mul_le_mul (constant C) hM)
  refine ⟨hden, ?_⟩
  rw [sparsifierWitnessEdgeCap_eq _ _ _ (Expander.maxPhiDenOf_pos decK thr M)]
  let e := Nat.clog 2 cDeg + Nat.clog 2 C + d + d
  have hp : cDeg * Expander.maxPhiDenOf decK thr M * M ≤ B ^ e := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul (constant cDeg) hden)
      ((Nat.le_add_right M 2).trans hM)).trans_eq (by simp only [e, pow_add, Nat.mul_assoc])
  have hone : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 2 * B ^ e := by omega
    _ = B ^ e * 2 := Nat.mul_comm _ _
    _ ≤ B ^ e * B := Nat.mul_le_mul_left _ hB
    _ = _ := (pow_succ B e).symm

/-- The length and query factors of either sparsifier path call fit
under one fixed polynomial when conductance and edge cap do. -/
theorem initSparsifierPathFactors_power_bounds
    {B den cap d : ℕ} (hB : 2 ≤ B) (harg : den + cap + 2 ≤ B ^ d)
    (Kγ c Kint : ℕ) :
    let e := Nat.clog 2 (721 * gExpConst Kγ c Kint) + d * (gExpDeg Kγ Kint + 1)
    gExpImpl Kγ c Kint den cap ≤ B ^ e ∧
      gQueryImpl Kγ c Kint den cap ≤ B ^ e := by
  dsimp only
  have hconst : 721 * gExpConst Kγ c Kint ≤ B ^ Nat.clog 2 (721 * gExpConst Kγ c Kint) :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left hB _)
  have hQuery := (gQueryImpl_le_poly Kγ c Kint den cap).trans
    (Nat.mul_le_mul hconst (Nat.pow_le_pow_left harg (gExpDeg Kγ Kint + 1)))
  rw [← pow_mul, ← pow_add] at hQuery
  exact ⟨(gExpImpl_le_gQueryImpl Kγ c Kint den cap).trans hQuery, hQuery⟩

/-- Both Section 8 path calls have fixed-power bounds. The length
factor squares the larger path length and the query factor takes the maximum. -/
theorem initMergedSparsifierFactors_power_bounds
    (decK thr cDeg witnessDen Kγ c Kint d : ℕ) :
    ∃ a e, ∀ {B M : ℕ}, 2 ≤ B → M + 2 ≤ B ^ d →
      let den := Expander.maxPhiDenOf decK thr M
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) M
      den + M + 2 ≤ B ^ a ∧ witnessDen + cap + 2 ≤ B ^ a ∧
      (max (gExpImpl Kγ c Kint den M) (gExpImpl Kγ c Kint witnessDen cap)) ^ 2 ≤
        B ^ (2 * e) ∧
      max (gQueryImpl Kγ c Kint den M) (gQueryImpl Kγ c Kint witnessDen cap) ≤ B ^ e := by
  obtain ⟨dc, hd⟩ := initSparsifierConductance_power_bounds decK thr cDeg
  let k := Nat.clog 2 cDeg + dc + d + d + Nat.clog 2 witnessDen + 1
  let e := Nat.clog 2 (721 * gExpConst Kγ c Kint) + (k + 2) * (gExpDeg Kγ Kint + 1)
  refine ⟨k + 2, e, ?_⟩
  intro B M hB hM
  dsimp only
  let den := Expander.maxPhiDenOf decK thr M
  let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) M
  obtain ⟨hden, hcap⟩ := hd hB hM
  have hBpos : 0 < B := by omega
  have lift {x j : ℕ} (hx : x ≤ B ^ j) (hj : j ≤ k) : x ≤ B ^ k :=
    hx.trans (Nat.pow_le_pow_right hBpos hj)
  have sum {x y : ℕ} (hx : x ≤ B ^ k) (hy : y ≤ B ^ k) : x + y + 2 ≤ B ^ (k + 2) := by
    have hp : 1 ≤ B ^ k := Nat.one_le_pow _ _ hBpos
    calc
      _ ≤ B ^ k * 4 := by omega
      _ ≤ B ^ k * B ^ 2 :=
        Nat.mul_le_mul_left _ (show 4 ≤ B ^ 2 from Nat.pow_le_pow_left hB 2)
      _ = _ := (pow_add B k 2).symm
  have hw : witnessDen ≤ B ^ Nat.clog 2 witnessDen :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left hB _)
  have harg : den + M + 2 ≤ B ^ (k + 2) := sum
    (lift hden (by dsimp [k]; omega)) (lift ((Nat.le_add_right M 2).trans hM) (by dsimp [k]; omega))
  have harg' : witnessDen + cap + 2 ≤ B ^ (k + 2) := sum
    (lift hw (by dsimp [k]; omega)) (lift hcap (by dsimp [k]; omega))
  obtain ⟨hlen, hquery⟩ := initSparsifierPathFactors_power_bounds hB harg Kγ c Kint
  obtain ⟨hlen', hquery'⟩ := initSparsifierPathFactors_power_bounds hB harg' Kγ c Kint
  refine ⟨harg, harg', ?_, max_le hquery hquery'⟩
  calc
    _ ≤ (B ^ e) ^ 2 := Nat.pow_le_pow_left (max_le hlen hlen') _
    _ = B ^ (2 * e) := by rw [← pow_mul, Nat.mul_comm e 2]

/-- A polynomial bound on a path call's arguments gives the word
width required by the linked path-factor contract. -/
theorem initSparsifierPathCall_wordSize_bound
    (words : List ℕ) (Kγ c Kint cw : ℕ) {den cap d multiplier : ℕ} :
    let B := words.length + words.foldr max 0 + 2
    let e := Nat.clog 2 (721 * gExpConst Kγ c Kint) + d * (gExpDeg Kγ Kint + 1)
    let p := max (max d e) (Nat.clog 2 (190 + Kint)) + 2
    den + cap + 2 ≤ B ^ d →
    max 24 (4 * cw + 8) * (p + 1) ≤ multiplier →
    max 24 (4 * cw + 8) *
      (Nat.log 2 (den + cap + gExpImpl Kγ c Kint den cap + gDelImpl Kint den cap + 2) + 1) ≤
        wordSize multiplier words := by
  dsimp only
  intro harg hmult
  let B := words.length + words.foldr max 0 + 2
  let e := Nat.clog 2 (721 * gExpConst Kγ c Kint) + d * (gExpDeg Kγ Kint + 1)
  let q := max (max d e) (Nat.clog 2 (190 + Kint))
  let b := Nat.log 2 B + 1
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hBpos : 0 < B := by omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have lift {x j : ℕ} (hx : x ≤ B ^ j) (hj : j ≤ q) : x ≤ B ^ q :=
    hx.trans (Nat.pow_le_pow_right hBpos hj)
  obtain ⟨hExp, _⟩ := initSparsifierPathFactors_power_bounds hB harg Kγ c Kint
  have hDel : gDelImpl Kint den cap ≤ B ^ Nat.clog 2 (190 + Kint) := by
    apply le_trans _ ((Nat.le_pow_clog (by decide) (190 + Kint)).trans (Nat.pow_le_pow_left hB _))
    unfold gDelImpl
    omega
  have h₁ := lift harg ((le_max_left d e).trans (le_max_left _ _))
  have h₂ := lift hExp ((le_max_right d e).trans (le_max_left _ _))
  have h₃ := lift hDel (le_max_right _ _)
  let x := den + cap + gExpImpl Kγ c Kint den cap + gDelImpl Kint den cap + 2
  have hx : x ≤ B ^ (q + 2) := by
    calc
      _ ≤ B ^ q * 4 := by dsimp only [x]; omega
      _ ≤ B ^ q * B ^ 2 :=
        Nat.mul_le_mul_left _ (show 4 ≤ B ^ 2 from Nat.pow_le_pow_left hB 2)
      _ = _ := (pow_add B q 2).symm
  have hlog : Nat.log 2 x + 1 ≤ (q + 3) * b := by
    have hs : B ≤ 2 ^ b := (Nat.lt_pow_succ_log_self (by decide) B).le
    have hpow : x < 2 ^ ((q + 2) * b + 1) := by
      apply lt_of_le_of_lt (hx.trans (Nat.pow_le_pow_left hs _))
      rw [← pow_mul, Nat.mul_comm b]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    have hlog' : Nat.log 2 x < (q + 2) * b + 1 :=
      (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hpow
    rw [show q + 3 = (q + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega
  have hc : max 24 (4 * cw + 8) * (q + 3) ≤ multiplier := by
    simpa only [q, e, Nat.add_assoc] using hmult
  change max 24 (4 * cw + 8) * (Nat.log 2 x + 1) ≤ multiplier * b
  exact (Nat.mul_le_mul_left _ hlog).trans (by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hc)

/-- One word-size multiplier covers the two path-call widths and the
scaled factors written by the merged sparsifier Init. -/
theorem initMergedSparsifierFactors_wordSize_bounds
    (decK thr cDeg witnessDen Kγ c Kint cw d ds dh : ℕ) :
    ∃ multiplier, ∀ (words : List ℕ) (M scale heap w : ℕ),
      let B := words.length + words.foldr max 0 + 2
      M + 2 ≤ B ^ d → scale ≤ B ^ ds → heap ≤ B ^ dh → wordSize multiplier words ≤ w →
      let den := Expander.maxPhiDenOf decK thr M
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) M
      4 * M + 2 < 2 ^ w ∧ (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w ∧
      cDeg < 2 ^ w ∧ heap + 4 < 2 ^ w ∧ witnessDen < 2 ^ w ∧
      cDeg * den < 2 ^ w ∧ cDeg * den * M + 1 < 2 ^ w ∧
      max 24 (4 * cw + 8) *
        (Nat.log 2 (den + M + gExpImpl Kγ c Kint den M + gDelImpl Kint den M + 2) + 1) ≤ w ∧
      max 24 (4 * cw + 8) *
        (Nat.log 2 (witnessDen + cap + gExpImpl Kγ c Kint witnessDen cap +
          gDelImpl Kint witnessDen cap + 2) + 1) ≤ w ∧
      scale * (max (gExpImpl Kγ c Kint den M) (gExpImpl Kγ c Kint witnessDen cap)) ^ 2 < 2 ^ w ∧
      scale * max (gQueryImpl Kγ c Kint den M) (gQueryImpl Kγ c Kint witnessDen cap) < 2 ^ w := by
  obtain ⟨a, e, h⟩ := initMergedSparsifierFactors_power_bounds decK thr cDeg witnessDen Kγ c Kint d
  let pathExponent := Nat.clog 2 (721 * gExpConst Kγ c Kint) + a * (gExpDeg Kγ Kint + 1)
  let pathWidth := max 24 (4 * cw + 8) *
    (max (max a pathExponent) (Nat.clog 2 (190 + Kint)) + 2 + 1)
  obtain ⟨dc, hconductance⟩ := initSparsifierConductance_power_bounds decK thr cDeg
  let edgeDegree := Nat.clog 2 cDeg + dc + d + d + 1
  let arithmeticDegree := max (3 * (d + 2)) (max (dh + 3)
    (max (Nat.clog 2 witnessDen) edgeDegree))
  let multiplier := max (max (ds + 2 * e + 1) pathWidth) arithmeticDegree
  refine ⟨multiplier, ?_⟩
  intro words M scale heap w
  dsimp only
  intro hM hs hh hw
  let B := words.length + words.foldr max 0 + 2
  have hB : 2 ≤ B := by dsimp [B]; omega
  obtain ⟨harg, harg', hlen, hquery⟩ := h hB hM
  have fit {x j : ℕ} (hx : x ≤ B ^ j) (hj : j ≤ 2 * e) : scale * x < 2 ^ w := by
    have hpow : scale * x ≤ B ^ multiplier := by
      calc
        _ ≤ B ^ ds * B ^ j := Nat.mul_le_mul hs hx
        _ = B ^ (ds + j) := (pow_add B ds j).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by dsimp [multiplier]; omega)
    exact hpow.trans_lt ((pow_lt_two_pow_wordSize (by dsimp [multiplier]; omega) words).trans_le
      (Nat.pow_le_pow_right (by decide) hw))
  have hwidth : pathWidth ≤ multiplier := (le_max_right _ _).trans (le_max_left _ _)
  have hA : arithmeticDegree ≤ multiplier := le_max_right _ _
  have word {x j : ℕ} (hx : x ≤ B ^ j) (hj : j ≤ arithmeticDegree) : x < 2 ^ w := by
    exact (hx.trans (Nat.pow_le_pow_right (by omega) (hj.trans hA))).trans_lt
      ((pow_lt_two_pow_wordSize (by dsimp [multiplier]; omega) words).trans_le
        (Nat.pow_le_pow_right (by decide) hw))
  have constant (x : ℕ) : x ≤ B ^ Nat.clog 2 x :=
    (Nat.le_pow_clog (by decide) x).trans (Nat.pow_le_pow_left hB _)
  obtain ⟨hden, hcap⟩ := hconductance hB hM
  rw [sparsifierWitnessEdgeCap_eq _ _ _ (Expander.maxPhiDenOf_pos decK thr M)] at hcap
  have hcd : cDeg * Expander.maxPhiDenOf decK thr M ≤ B ^ (Nat.clog 2 cDeg + (dc + d)) := by
    rw [pow_add]
    exact Nat.mul_le_mul (constant cDeg) hden
  have hsize : 4 * M + 4 ≤ B ^ (d + 2) := by
    calc
      _ ≤ (M + 2) * 4 := by omega
      _ ≤ B ^ d * B ^ 2 := Nat.mul_le_mul hM
        (show 4 ≤ B ^ 2 from Nat.pow_le_pow_left hB 2)
      _ = _ := (pow_add B d 2).symm
  have hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 ≤ B ^ (3 * (d + 2)) := by
    rw [Nat.mul_comm 3, pow_mul]
    exact Nat.pow_le_pow_left (by have hlog := Nat.log_le_self 2 (4 * M + 2); omega) _
  have hheap : heap + 4 ≤ B ^ (dh + 3) := by
    have hpos : 1 ≤ B ^ dh := Nat.one_le_pow _ _ (by omega)
    have hh' : heap ≤ B ^ dh := hh
    calc
      _ ≤ B ^ dh * 8 := by omega
      _ ≤ B ^ dh * B ^ 3 := Nat.mul_le_mul_left _
        (show 8 ≤ B ^ 3 from Nat.pow_le_pow_left hB 3)
      _ = _ := (pow_add B dh 3).symm
  have hEdge : edgeDegree ≤ arithmeticDegree :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hSize : 3 * (d + 2) ≤ arithmeticDegree := le_max_left _ _
  have hHeap : dh + 3 ≤ arithmeticDegree := (le_max_left _ _).trans (le_max_right _ _)
  have hWitness : Nat.clog 2 witnessDen ≤ arithmeticDegree :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨word (show 4 * M + 2 ≤ _ from (by omega : 4 * M + 2 ≤ 4 * M + 4).trans hsize)
      (by omega), word hcube hSize, word (constant cDeg) (by dsimp [edgeDegree] at hEdge; omega),
    word hheap hHeap, word (constant witnessDen) hWitness,
    word hcd (by dsimp [edgeDegree] at hEdge; omega), word hcap hEdge,
    (initSparsifierPathCall_wordSize_bound words Kγ c Kint cw harg hwidth).trans hw,
    (initSparsifierPathCall_wordSize_bound words Kγ c Kint cw harg' hwidth).trans hw,
    fit hlen le_rfl, fit hquery (by omega)⟩

/-- Registers 118 through 121 hold the size and height intermediates. -/
@[expose] def computeInitFallbackCappedCost (bits root denReg capReg result : ℕ) : Stmt :=
  initFallbackSizeExponent bits root denReg 120 ;;
  computeInitFallbackCappedSize bits capReg 120 119 121 ;;
  storeInitFallbackCappedCost denReg 120 121 result

/-- The machine computes the capped fallback cost from the runtime
reciprocal and graph size. Only scratch and result registers change. -/
theorem computeInitFallbackCappedCost_runs {w bits root denReg capReg result d M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w))
    (hd : st.regs denReg = d) (hM : st.regs capReg = M)
    (hden : denReg ∉ ([118, 119, 120, 121] : List ℕ))
    (hcap : capReg ≠ 119) (hcap' : capReg ≠ 120)
    (hdPos : 0 < d) (hw : 2480 < 2 ^ w) (hfit : 10 * d < 2 ^ w)
    (hpow : (Nat.log 2 (10 * d) + 1) ^ 4 + 1 < 2 ^ w)
    (hcapWord : 3 * M + 1 < 2 ^ w)
    (hExp : zStarExp d < 2 ^ w) (hSize : zCap d M < 2 ^ w)
    (hheight : 4 * (40 * d + 1) * (zStarExp d + 2) + 2 < 2 ^ w)
    (hcost : fbCostCap d M < 2 ^ w) :
    ∃ out cost, Runs w p ω (computeInitFallbackCappedCost bits root denReg capReg result)
        st .normal out cost ∧
      out.regs result = fbCostCap d M ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([118, 119, 120, 121, result] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 14 * (10 * d).size + 89 * ((Nat.log 2 (10 * d) + 1) ^ 4 + 1).size +
        14 * (3 * M + 1).size + 125 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hden
  obtain ⟨powState, cp, hrp, h120, hmp, hkp, hcp⟩ :=
    initFallbackSizeExponent_runs (ω := ω) (result := 120) hbits hroot hd hdPos (by omega) hfit hpow
  obtain ⟨sized, cs, hrs, h121, hms, hks, hcs⟩ :=
    computeInitFallbackCappedSize_runs (ω := ω) (bitsReg := 119) (outReg := 121)
      hbits ((hkp capReg hcap hcap').trans hM) h120 (by decide) (by omega) hcapWord hExp hSize
  obtain ⟨out, hrf, hout, hmf, hkf⟩ :=
    storeInitFallbackCappedCost_runs (p := p) (ω := ω) (resultReg := result)
      ((hks denReg hden.2.1 hden.2.2.2).trans ((hkp denReg hden.2.1 hden.2.2.1).trans hd))
      ((hks 120 (by decide) (by decide)).trans h120) h121 hden.1 (by decide) hw hheight hcost
  refine ⟨out, cp + (cs + 51 + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨powState, cp, _, hrp,
      runs_seq_iff.mpr (Or.inr ⟨sized, cs, 51, hrs, hrf, rfl⟩), rfl⟩),
    hout, hmf.trans (hms.trans hmp), ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact (hkf r hr.1 hr.2.2.2.2).trans
    ((hks r hr.2.1 hr.2.2.2.1).trans (hkp r hr.2.1 hr.2.2.1))

/-- Combine the capped fallback charge with the path arithmetic. -/
@[expose] def computeInitMachinePathQuery (bits root denReg capReg result : ℕ) : Stmt :=
  computeInitFallbackCappedCost bits root denReg capReg 118 ;;
  initMachinePathQuery result 118

/-- With the bounds registers populated, compute the query factor of
the merged path tool. -/
theorem computeInitMachinePathQuery_runs {w bits root denReg capReg result d M Kγ c Kint : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w))
    (hd : st.regs denReg = d) (hM : st.regs capReg = M)
    (hden : denReg ∉ ([118, 119, 120, 121] : List ℕ))
    (hcap : capReg ≠ 119) (hcap' : capReg ≠ 120)
    (hdPos : 0 < d) (hw : 2480 < 2 ^ w) (hfit : 10 * d < 2 ^ w)
    (hpow : (Nat.log 2 (10 * d) + 1) ^ 4 + 1 < 2 ^ w)
    (hcapWord : 3 * M + 1 < 2 ^ w)
    (hExp : zStarExp d < 2 ^ w) (hSize : zCap d M < 2 ^ w)
    (hheight : 4 * (40 * d + 1) * (zStarExp d + 2) + 2 < 2 ^ w)
    (hcost : fbCostCap d M < 2 ^ w)
    (hphi : st.regs 7 = phiOutDenImpl Kγ c d M)
    (hcs : st.regs 9 = csExpFactor Kγ Kint M)
    (hlen : st.regs 17 = phiOutDenImpl Kγ c d M * lenFactor M)
    (hquery : gQueryImpl Kγ c Kint d M < 2 ^ w) :
    ∃ out cost, Runs w p ω (computeInitMachinePathQuery bits root denReg capReg result)
        st .normal out cost ∧
      out.regs result = gQueryImpl Kγ c Kint d M ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([118, 119, 120, 121, result] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 14 * (10 * d).size + 89 * ((Nat.log 2 (10 * d) + 1) ^ 4 + 1).size +
        14 * (3 * M + 1).size + 136 := by
  obtain ⟨mid, cost, hr, h118, hm, hk, hc⟩ :=
    computeInitFallbackCappedCost_runs (ω := ω) (result := 118) hbits hroot hd hM hden hcap hcap'
      hdPos hw hfit hpow hcapWord hExp hSize hheight hcost
  obtain ⟨out, hq, hout, hmem, hregs⟩ :=
    initMachinePathQuery_runs (ω := ω) (outReg := result)
      ((hk 7 (by decide)).trans hphi) ((hk 9 (by decide)).trans hcs) h118
      ((hk 17 (by decide)).trans hlen) hquery
  refine ⟨out, cost + 11, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 10, hr, hq, rfl⟩),
    hout, hmem.trans hm, ?_, by omega⟩
  intro r hr'
  have hres : r ≠ result := fun he => hr' (by simp [he])
  apply (hregs r hres).trans
  apply hk
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr' ⊢
  exact ⟨hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.1⟩

/-- Evaluate the shared path bounds in the entry's local registers. -/
@[expose] def initMachinePathBounds (Kγ c Kint : ℕ) : Stmt :=
  phiOutBlock Kγ c ;; csExpBlock Kγ Kint ;; lenBlock

/-- The merged path arithmetic leaves the reciprocal and cap in place
and supplies the terms needed by the length and query factors. -/
theorem initMachinePathBounds_runs {w Kγ c Kint cw d M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : 1 ≤ d)
    (hcw : max 24 (4 * cw + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c Kint d M + gDelImpl Kint d M + 2) + 1) ≤ w)
    (h0 : st.regs 0 = d) (h1 : st.regs 1 = M) :
    ∃ out cost, Runs w p ω (initMachinePathBounds Kγ c Kint) st .normal out cost ∧
      out.regs 0 = d ∧ out.regs 1 = M ∧ out.regs 2 = st.regs 2 ∧
      out.regs 7 = phiOutDenImpl Kγ c d M ∧ out.regs 9 = csExpFactor Kγ Kint M ∧
      out.regs 17 = phiOutDenImpl Kγ c d M * lenFactor M ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      cost ≤ 115 * (Nat.log 2 (d + M + 2) + 1) + 13 * (Nat.log 2 (6 * M + 2) + 1) + 452 := by
  obtain ⟨o₁, first, c₁, hr₁, hp₁, hc₁⟩ :=
    phiOutBlock_triple (p := p) (cw_cs := cw) hd hcw st h0 h1 st ω rfl
  cases o₁ <;> simp only [normalPost] at hp₁
  obtain ⟨h0₁, h1₁, h2₁, h7₁, hm₁, ht₁⟩ := hp₁
  obtain ⟨o₂, mid, c₂, hr₂, hp₂, hc₂⟩ :=
    csExpBlock_triple (p := p) (cw_cs := cw) hd hcw first h0₁ h1₁ h7₁ first ω rfl
  cases o₂ <;> simp only [normalPost] at hp₂
  obtain ⟨h0₂, h1₂, h2₂, h7₂, h9₂, hm₂, ht₂⟩ := hp₂
  obtain ⟨o₃, out, c₃, hr₃, hp₃, hc₃⟩ :=
    lenBlock_triple (p := p) (cw_cs := cw) hd hcw mid h0₂ h1₂ h7₂ h9₂ mid ω rfl
  cases o₃ <;> simp only [normalPost] at hp₃
  obtain ⟨h0₃, h1₃, h2₃, h7₃, h9₃, h17, hm₃, ht₃⟩ := hp₃
  dsimp only at hc₁ hc₂ hc₃
  exact ⟨out, c₁ + (c₂ + c₃ + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨first, c₁, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨mid, c₂, c₃, hr₂, hr₃, rfl⟩), rfl⟩),
    h0₃, h1₃, h2₃.trans (h2₂.trans h2₁), h7₃, h9₃, h17,
    hm₃.trans (hm₂.trans hm₁), ht₃.trans (ht₂.trans ht₁), by omega⟩

/-- Compute both path factors at the supplied reciprocal and edge cap.
The outputs occupy local registers 18 and 19. -/
@[expose] def initMachinePathFactors (Kγ c Kint bits root : ℕ) : Stmt :=
  initMachinePathBounds Kγ c Kint ;;
  computeInitMachinePathQuery bits root 0 1 19 ;;
  .assign 18 (.bin .add (.reg 17) (.reg 9))

/-- The shared bounds and the capped query charge give exactly the
integer factors of the machine path tool. -/
theorem initMachinePathFactors_runs {w Kγ c Kint cw bits root d M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w))
    (hd : 0 < d) (h0 : st.regs 0 = d) (h1 : st.regs 1 = M)
    (hcw : max 24 (4 * cw + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c Kint d M + gDelImpl Kint d M + 2) + 1) ≤ w)
    (hw : 2480 < 2 ^ w) (hfit : 10 * d < 2 ^ w)
    (hpow : (Nat.log 2 (10 * d) + 1) ^ 4 + 1 < 2 ^ w)
    (hcap : 3 * M + 1 < 2 ^ w) (hexp : zStarExp d < 2 ^ w) (hsize : zCap d M < 2 ^ w)
    (hh : 4 * (40 * d + 1) * (zStarExp d + 2) + 2 < 2 ^ w)
    (hcost : fbCostCap d M < 2 ^ w) (hq : gQueryImpl Kγ c Kint d M < 2 ^ w) :
    ∃ out cost, Runs w p ω (initMachinePathFactors Kγ c Kint bits root) st .normal out cost ∧
      out.regs 18 = gExpImpl Kγ c Kint d M ∧ out.regs 19 = gQueryImpl Kγ c Kint d M ∧
      out.regs 2 = st.regs 2 ∧ out.mem = st.mem ∧
      cost ≤ 115 * (Nat.log 2 (d + M + 2) + 1) + 13 * (Nat.log 2 (6 * M + 2) + 1) +
        14 * (10 * d).size + 89 * ((Nat.log 2 (10 * d) + 1) ^ 4 + 1).size +
        14 * (3 * M + 1).size + 594 := by
  obtain ⟨ready, cb, hrb, hd', hM, h2, h7, h9, h17, hm, _, hcb⟩ :=
    initMachinePathBounds_runs (p := p) (ω := ω) hd hcw h0 h1
  obtain ⟨mid, cq, hrq, h19, hm', hk, hcq⟩ :=
    computeInitMachinePathQuery_runs (ω := ω) (result := 19) hbits hroot hd' hM (by decide) (by decide)
      (by decide) hd hw hfit hpow hcap hexp hsize hh hcost h7 h9 h17 hq
  let out := {mid with regs := Function.update mid.regs 18 (gExpImpl Kγ c Kint d M)}
  have hword := (gExpImpl_le_gQueryImpl Kγ c Kint d M).trans_lt hq
  have ha : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.reg 9))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hk 17 (by decide), hk 9 (by decide), h17, h9,
        show phiOutDenImpl Kγ c d M * lenFactor M + csExpFactor Kγ Kint M < 2 ^ w from hword, gExpImpl],
      rfl, rfl, rfl⟩
  exact ⟨out, cb + (cq + 4 + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨ready, cb, _, hrb,
    runs_seq_iff.mpr (Or.inr ⟨mid, cq, 4, hrq, ha, rfl⟩), rfl⟩),
    by simp [out], by simpa [out] using h19,
    by simpa [out] using (hk 2 (by decide)).trans h2, hm'.trans hm, by omega⟩

/-- Write the two path factors at the supplied heap cursor and return
the cursor immediately after the pair. -/
@[expose] def returnInitMachinePathFactors : Stmt :=
  .store (.reg 2) (.reg 18) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 19) ;;
  .ret (.bin .add (.reg 2) (.const 2))

/-- The result pair occupies exactly two words. -/
theorem returnInitMachinePathFactors_runs {w heap path query : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 2 = heap) (hp : st.regs 18 = path) (hq : st.regs 19 = query)
    (hw : heap + 2 < 2 ^ w) :
    ∃ out, Runs w p ω returnInitMachinePathFactors st (.returned (heap + 2)) out 14 ∧
      out.mem heap = path ∧ out.mem (heap + 1) = query ∧
      (∀ a, a ≠ heap → a ≠ heap + 1 → out.mem a = st.mem a) := by
  let mid := {st with mem := Function.update st.mem heap path}
  let out := {mid with mem := Function.update mid.mem (heap + 1) query}
  have hs : Runs w p ω (.store (.reg 2) (.reg 18)) st .normal mid 3 :=
    runs_store_iff.mpr ⟨heap, path, by simp [Expr.eval, hh], by simp [Expr.eval, hp],
      rfl, rfl, rfl⟩
  have ht : Runs w p ω (.store (.bin .add (.reg 2) (.const 1)) (.reg 19))
      mid .normal out 5 :=
    runs_store_iff.mpr ⟨heap + 1, query, by
      simp [Expr.eval, BinOp.eval, mid, hh, show 1 < 2 ^ w by omega, show heap + 1 < 2 ^ w by omega],
      by simp [Expr.eval, mid, hq], rfl, rfl, rfl⟩
  have hr : Runs w p ω (.ret (.bin .add (.reg 2) (.const 2)))
      out (.returned (heap + 2)) out 4 :=
    runs_ret_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, out, mid, hh, hw, show 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 3, 10, hs,
    runs_seq_iff.mpr (Or.inr ⟨out, 5, 4, ht, hr, rfl⟩), by omega⟩),
    by simp [out, mid], by simp [out],
    fun a h₁ h₂ => by simp [out, mid, h₁, h₂]⟩

/-- Evaluate the factors in local registers and return their memory record. -/
@[expose] def initMachinePathFactorsProc (Kγ c Kint bits root : ℕ) : Stmt :=
  initMachinePathFactors Kγ c Kint bits root ;; returnInitMachinePathFactors

/-- The factor procedure receives the reciprocal, edge cap and result
address. Its word bounds cover the shared arithmetic and both results. -/
@[expose] def initMachinePathFactorsContract (w Kγ c Kint cw : ℕ) : Contract where
  pre args _ := ∃ d M heap, args = [d, M, heap] ∧
    0 < d ∧ max 24 (4 * cw + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c Kint d M + gDelImpl Kint d M + 2) + 1) ≤ w ∧
    2480 < 2 ^ w ∧ 10 * d < 2 ^ w ∧ (Nat.log 2 (10 * d) + 1) ^ 4 + 1 < 2 ^ w ∧
    3 * M + 1 < 2 ^ w ∧ zStarExp d < 2 ^ w ∧ zCap d M < 2 ^ w ∧
    4 * (40 * d + 1) * (zStarExp d + 2) + 2 < 2 ^ w ∧ fbCostCap d M < 2 ^ w ∧
    gQueryImpl Kγ c Kint d M < 2 ^ w ∧ heap + 2 < 2 ^ w
  post args mem ret out :=
    let d := args.getD 0 0
    let M := args.getD 1 0
    let heap := args.getD 2 0
    ret = heap + 2 ∧ out heap = gExpImpl Kγ c Kint d M ∧
      out (heap + 1) = gQueryImpl Kγ c Kint d M ∧
      ∀ a, a ≠ heap → a ≠ heap + 1 → out a = mem a
  cost args _ :=
    let d := args.getD 0 0
    let M := args.getD 1 0
    115 * (Nat.log 2 (d + M + 2) + 1) + 13 * (Nat.log 2 (6 * M + 2) + 1) +
      14 * (10 * d).size + 89 * ((Nat.log 2 (10 * d) + 1) ^ 4 + 1).size +
      14 * (3 * M + 1).size + 609

/-- The query factor dominates the capped fallback charge. A single
word bound on that factor covers the capped size and pruning height. -/
theorem initMachineFallbackWordBounds {w Kγ c Kint d M : ℕ}
    (hq : gQueryImpl Kγ c Kint d M < 2 ^ w) :
    zCap d M < 2 ^ w ∧
      4 * (40 * d + 1) * (zStarExp d + 2) + 2 < 2 ^ w ∧
      fbCostCap d M < 2 ^ w ∧ 10 * d < 2 ^ w := by
  have hf : fbCostCap d M ≤ gQueryImpl Kγ c Kint d M := by
    unfold gQueryImpl gBaseImpl
    omega
  have hfit := hf.trans_lt hq
  have hz := zCap_le_fbCostCap d M
  refine ⟨by omega, ?_, hfit, ?_⟩
  all_goals
    change Expander.pruneTimeBound (2 * zCap d M) (zCap d M)
      (4 * (40 * d + 1) * (zStarExp d + 2) + 2) + 2000 * zCap d M + 10 * d + 1000 < 2 ^ w at hfit
    unfold Expander.pruneTimeBound at hfit
    omega

/-- The caller needs the path tool's word budget, the query-factor
word bound and room for the result record. -/
theorem initMachinePathFactorsContract_pre_of_bounds
    {w Kγ c Kint cw d M heap : ℕ} {mem : ℕ → ℕ}
    (hd : 0 < d)
    (hcw : max 24 (4 * cw + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c Kint d M + gDelImpl Kint d M + 2) + 1) ≤ w)
    (hq : gQueryImpl Kγ c Kint d M < 2 ^ w)
    (hheap : heap + 2 < 2 ^ w) :
    (initMachinePathFactorsContract w Kγ c Kint cw).pre [d, M, heap] mem := by
  let X := d + M + gExpImpl Kγ c Kint d M + gDelImpl Kint d M + 2
  obtain ⟨h600, h24, _, _, _, _, _, _, _, _, _, hpowBudget⟩ := bounds_word_le (show 1 ≤ d by omega) hcw
  change 600 ≤ X at h600
  change X ^ 24 < 2 ^ w at h24
  have hx2 : X ^ 2 < 2 ^ w := (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 24)).trans_lt h24
  have hlarge : 2480 < X ^ 2 := lt_of_lt_of_le (by decide : 2480 < 600 ^ 2)
    (Nat.pow_le_pow_left h600 2)
  have hm : M < X := by dsimp [X]; omega
  have hcap : 3 * M + 1 < X ^ 2 := by
    have hmul : 3 * X ≤ X * X := Nat.mul_le_mul_right X (by omega)
    rw [pow_two]
    omega
  obtain ⟨hz, hH, hf, h10⟩ := initMachineFallbackWordBounds hq
  have hb : zStarExp d < 2 ^ w := by
    have ht : zStarExp d + 2 ≤ (4 * (40 * d + 1)) * (zStarExp d + 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  let n := Nat.log 2 (10 * d) + 1
  have hpow : n ^ 4 + 1 < 2 ^ w := by
    have hbase : n ^ 2 + 1 ≤ (n + 1) ^ 2 + 1 :=
      Nat.add_le_add_right (Nat.pow_le_pow_left (Nat.le_succ n) 2) 1
    have hsmall : n ^ 4 + 1 ≤ (n ^ 2 + 1) ^ 2 := by
      rw [show n ^ 4 = (n ^ 2) ^ 2 by rw [← pow_mul]]
      simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    have hbig : ((n + 1) ^ 2 + 1) ^ 2 ≤ ((n + 1) ^ 2 + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have hx8 : X ^ 8 < 2 ^ w :=
      (Nat.pow_le_pow_right (by omega) (by decide : 8 ≤ 24)).trans_lt h24
    have hbud : ((n + 1) ^ 2 + 1) ^ 3 < X ^ 8 := hpowBudget
    exact (hsmall.trans ((Nat.pow_le_pow_left hbase 2).trans hbig)).trans_lt (hbud.trans hx8)
  exact ⟨d, M, heap, rfl, hd, hcw, hlarge.trans hx2, h10, hpow, hcap.trans hx2,
    hb, hz, hH, hf, hq, hheap⟩

/-- The callable body meets the exact factor-record contract. -/
theorem initMachinePathFactorsProc_meetsContract {w Kγ c Kint cw bits root entry : ℕ}
    {p : Program}
    (hproc : p.procs[entry]? = some (initMachinePathFactorsProc Kγ c Kint bits root))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hroot : MeetsContract w p root (minRatioBranchCountContract w)) :
    MeetsContract w p entry (initMachinePathFactorsContract w Kγ c Kint cw) := by
  intro args mem pos ω _ hpre
  obtain ⟨d, M, heap, rfl, hd, hcw, hw, hfit, hpow, hcap, hexp, hsize, hh, hcost, hq, hheap⟩ := hpre
  obtain ⟨ready, cost, hr, h18, h19, h2, hm, hc⟩ :=
    initMachinePathFactors_runs (ω := ω) (d := d) (M := M) (st := startState [d, M, heap] mem pos)
      hbits hroot hd rfl rfl hcw hw hfit hpow hcap hexp hsize hh hcost hq
  obtain ⟨out, hs, hp, ht, hf⟩ :=
    returnInitMachinePathFactors_runs (p := p) (ω := ω) (heap := heap) h2 h18 h19 hheap
  refine ⟨_, hproc, .returned (heap + 2), out, cost + 15,
    runs_seq_iff.mpr (Or.inr ⟨ready, cost, 14, hr, hs, by omega⟩), ?_, ?_⟩
  · exact ⟨rfl, hp, ht, fun a ha ha' => (hf a ha ha').trans (congrFun hm a)⟩
  · change cost + 15 ≤ 115 * (Nat.log 2 (d + M + 2) + 1) + 13 * (Nat.log 2 (6 * M + 2) + 1) +
      14 * (10 * d).size + 89 * ((Nat.log 2 (10 * d) + 1) ^ 4 + 1).size +
      14 * (3 * M + 1).size + 609
    omega

/-- Call the evaluator at the current reciprocal and cap, using the
supplied heap cursor for the two returned words. -/
@[expose] def callInitMachinePathFactors (entry denReg capReg heapReg retReg : ℕ) : Stmt :=
  .call retReg entry [.reg denReg, .reg capReg, .reg heapReg]

/-- The call keeps the surrounding Init registers and memory outside
the two-word result record. -/
theorem callInitMachinePathFactors_runs
    {w Kγ c Kint cw entry denReg capReg heapReg retReg d M heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (initMachinePathFactorsContract w Kγ c Kint cw))
    (hd : st.regs denReg = d) (hM : st.regs capReg = M) (hh : st.regs heapReg = heap)
    (hwords : ∀ a ∈ [d, M, heap], a < 2 ^ w)
    (hpre : (initMachinePathFactorsContract w Kγ c Kint cw).pre [d, M, heap] st.mem) :
    ∃ out cost, Runs w p ω (callInitMachinePathFactors entry denReg capReg heapReg retReg)
        st .normal out cost ∧
      out.regs retReg = heap + 2 ∧
      out.mem heap = gExpImpl Kγ c Kint d M ∧
      out.mem (heap + 1) = gQueryImpl Kγ c Kint d M ∧
      (∀ r ≠ retReg, out.regs r = st.regs r) ∧
      (∀ a, a ≠ heap → a ≠ heap + 1 → out.mem a = st.mem a) ∧
      cost ≤ (initMachinePathFactorsContract w Kγ c Kint cw).cost [d, M, heap] st.mem + 4 := by
  have hargs : evalArgs w st [.reg denReg, .reg capReg, .reg heapReg] = some [d, M, heap] := by
    simp [evalArgs, Expr.eval, hd, hM, hh]
  obtain ⟨out, cost, ret, hr, hp, hv, hk, hc⟩ :=
    runs_call_of_meetsContract (r := retReg) himpl hargs hwords hpre ω
  obtain ⟨hret, hpath, hquery, hmem⟩ := hp
  change cost ≤ 3 + (initMachinePathFactorsContract w Kγ c Kint cw).cost [d, M, heap] st.mem + 1 at hc
  have hbound : cost ≤ (initMachinePathFactorsContract w Kγ c Kint cw).cost [d, M, heap] st.mem + 4 := by omega
  exact ⟨out, cost, hr, hv.trans hret, hpath, hquery, hk, hmem, hbound⟩

/-- Evaluate the input and witness factors in consecutive two-word records.
The witness reciprocal is fixed by the expander construction. -/
@[expose] def callInitMachineSparsifierFactors (entry witnessDen : ℕ) : Stmt :=
  .assign 122 (.const witnessDen) ;;
  callInitMachinePathFactors entry 63 23 98 99 ;;
  callInitMachinePathFactors entry 122 58 99 99

/-- Both factor records remain available at the original heap cursor. -/
theorem callInitMachineSparsifierFactors_runs
    {w Kγ c Kint cw entry den witnessDen M cap heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (initMachinePathFactorsContract w Kγ c Kint cw))
    (hd : st.regs 63 = den) (hM : st.regs 23 = M) (hh : st.regs 98 = heap)
    (hcap : st.regs 58 = cap) (hwd : witnessDen < 2 ^ w)
    (hwords : ∀ a ∈ [den, M, heap], a < 2 ^ w)
    (hwords' : ∀ a ∈ [witnessDen, cap, heap + 2], a < 2 ^ w)
    (hpre : (initMachinePathFactorsContract w Kγ c Kint cw).pre [den, M, heap] st.mem)
    (hpre' : ∀ mem, (initMachinePathFactorsContract w Kγ c Kint cw).pre [witnessDen, cap, heap + 2] mem) :
    ∃ out cost, Runs w p ω (callInitMachineSparsifierFactors entry witnessDen) st .normal out cost ∧
      out.regs 99 = heap + 4 ∧
      out.mem heap = gExpImpl Kγ c Kint den M ∧
      out.mem (heap + 1) = gQueryImpl Kγ c Kint den M ∧
      out.mem (heap + 2) = gExpImpl Kγ c Kint witnessDen cap ∧
      out.mem (heap + 3) = gQueryImpl Kγ c Kint witnessDen cap ∧
      (∀ r, r ≠ 99 → r ≠ 122 → out.regs r = st.regs r) ∧
      (∀ a, a < heap ∨ heap + 4 ≤ a → out.mem a = st.mem a) ∧
      cost ≤ (initMachinePathFactorsContract w Kγ c Kint cw).cost [den, M, heap] st.mem +
        (initMachinePathFactorsContract w Kγ c Kint cw).cost [witnessDen, cap, heap + 2] st.mem + 12 := by
  let ready := {st with regs := Function.update st.regs 122 witnessDen}
  have hs : Runs w p ω (.assign 122 (.const witnessDen)) st .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hwd], rfl, rfl, rfl⟩
  obtain ⟨mid, c₁, h₁, h99, he, hq, hk, hf, hc₁⟩ :=
    callInitMachinePathFactors_runs (ω := ω) (retReg := 99) (denReg := 63) (capReg := 23)
      (heapReg := 98) (st := ready) himpl (by simpa [ready] using hd)
      (by simpa [ready] using hM) (by simpa [ready] using hh) hwords hpre
  obtain ⟨out, c₂, h₂, h99', he', hq', hk', hf', hc₂⟩ :=
    callInitMachinePathFactors_runs (ω := ω) (retReg := 99) (denReg := 122) (capReg := 58)
      (heapReg := 99) himpl ((hk 122 (by decide)).trans (by simp [ready]))
      ((hk 58 (by decide)).trans (by simpa [ready] using hcap)) h99 hwords' (hpre' mid.mem)
  change c₁ ≤ (initMachinePathFactorsContract w Kγ c Kint cw).cost [den, M, heap] st.mem + 4 at hc₁
  change c₂ ≤ (initMachinePathFactorsContract w Kγ c Kint cw).cost [witnessDen, cap, heap + 2] st.mem + 4 at hc₂
  refine ⟨out, 2 + (c₁ + c₂ + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨ready, 2, _, hs,
      runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, h₁, h₂, rfl⟩), rfl⟩),
    h99', (hf' heap (by omega) (by omega)).trans he,
    (hf' (heap + 1) (by omega) (by omega)).trans hq, he', hq', ?_, ?_, by omega⟩
  · intro r hret hfixed
    exact (hk' r hret).trans ((hk r hret).trans (by simp [ready, hfixed]))
  · intro a ha
    exact (hf' a (by omega) (by omega)).trans (hf a (by omega) (by omega))

/-- Compute the maximum of the two unsigned path bounds. -/
@[expose] def initMachineFactorMax (a b : Expr) : Expr :=
  .bin .add b (.bin .sub a b)

/-- The intermediate subtraction fits whenever the maximum fits. -/
theorem initMachineFactorMax_eval {w a b : ℕ} {ea eb : Expr} {st : State}
    (ha : Expr.eval w st ea = some a) (hb : Expr.eval w st eb = some b)
    (hfit : max a b < 2 ^ w) :
    Expr.eval w st (initMachineFactorMax ea eb) = some (max a b) := by
  have hsub : a - b < 2 ^ w := (Nat.sub_le _ _).trans_lt ((le_max_left _ _).trans_lt hfit)
  have heq : b + (a - b) = max a b := by omega
  simp [initMachineFactorMax, Expr.eval, BinOp.eval, ha, hb, hsub, heq, hfit]

/-- Read the two records and store the squared maximum length and
maximum query charge at the working scale used by threshold Init. -/
@[expose] def finishInitMachineSparsifierFactors : Stmt :=
  .assign 50 (.bin .mul (.reg 4)
    (initDepthPower (initMachineFactorMax (.load (.reg 98))
      (.load (.bin .add (.reg 98) (.const 2)))) 2)) ;;
  .assign 52 (.reg 50) ;;
  .assign 114 (.bin .mul (.reg 4)
    (initMachineFactorMax (.load (.bin .add (.reg 98) (.const 1)))
      (.load (.bin .add (.reg 98) (.const 3))))) ;;
  .assign 115 (.reg 114)

/-- The four output registers give exact endpoints at the working scale. -/
theorem finishInitMachineSparsifierFactors_runs {w heap scale a b c d : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 98 = heap) (hs : st.regs 4 = scale) (hscale : 0 < scale)
    (ha : st.mem heap = a) (hb : st.mem (heap + 1) = b)
    (hc : st.mem (heap + 2) = c) (hd : st.mem (heap + 3) = d)
    (hw : heap + 4 < 2 ^ w)
    (hl : scale * (max a c) ^ 2 < 2 ^ w)
    (hq : scale * max b d < 2 ^ w) :
    ∃ out cost, Runs w p ω finishInitMachineSparsifierFactors st .normal out cost ∧
      out.regs 50 = scale * (max a c) ^ 2 ∧ out.regs 52 = out.regs 50 ∧
      out.regs 114 = scale * max b d ∧ out.regs 115 = out.regs 114 ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([50, 52, 114, 115] : List ℕ) → out.regs r = st.regs r) ∧ cost ≤ 80 := by
  let len := scale * (max a c) ^ 2
  let query := scale * max b d
  let le₂ : Expr := .load (.bin .add (.reg 98) (.const 2))
  let le₁ : Expr := .load (.reg 98)
  let qe₁ : Expr := .load (.bin .add (.reg 98) (.const 1))
  let qe₂ : Expr := .load (.bin .add (.reg 98) (.const 3))
  let lexpr := Expr.bin .mul (.reg 4) (initDepthPower (initMachineFactorMax le₁ le₂) 2)
  let qexpr := Expr.bin .mul (.reg 4) (initMachineFactorMax qe₁ qe₂)
  let s₁ := {st with regs := Function.update st.regs 50 len}
  let s₂ := {s₁ with regs := Function.update s₁.regs 52 len}
  let s₃ := {s₂ with regs := Function.update s₂.regs 114 query}
  let out := {s₃ with regs := Function.update s₃.regs 115 query}
  have hsq : (max a c) ^ 2 < 2 ^ w := lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ hscale) hl
  have hmax : max a c < 2 ^ w := (Nat.le_self_pow (by decide) _).trans_lt hsq
  have hlmax := initMachineFactorMax_eval (st := st) (ea := le₁) (eb := le₂)
    (by simp [le₁, Expr.eval, hh, ha])
    (by simp [le₂, Expr.eval, BinOp.eval, hh, hc, show 2 < 2 ^ w by omega,
      show heap + 2 < 2 ^ w by omega]) hmax
  have hp := initDepthPower_eval hlmax (show 1 < 2 ^ w by omega) 2 hsq
  have hr₁ : Runs w p ω (.assign 50 lexpr) st .normal s₁ (lexpr.size + 1) :=
    runs_assign_iff.mpr ⟨len, by simp [lexpr, Expr.eval, BinOp.eval, hs, hp, hl, len],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 52 (.reg 50)) s₁ .normal s₂ 2 :=
    runs_assign_iff.mpr ⟨len, by simp [Expr.eval, s₁], rfl, rfl, rfl⟩
  have hqmax := initMachineFactorMax_eval (st := s₂) (ea := qe₁) (eb := qe₂)
    (by simp [qe₁, Expr.eval, BinOp.eval, s₂, s₁, hh, hb, show 1 < 2 ^ w by omega,
      show heap + 1 < 2 ^ w by omega])
    (by simp [qe₂, Expr.eval, BinOp.eval, s₂, s₁, hh, hd, show 3 < 2 ^ w by omega,
      show heap + 3 < 2 ^ w by omega]) ((Nat.le_mul_of_pos_left _ hscale).trans_lt hq)
  have hr₃ : Runs w p ω (.assign 114 qexpr) s₂ .normal s₃ (qexpr.size + 1) :=
    runs_assign_iff.mpr ⟨query, by simp [qexpr, Expr.eval, BinOp.eval, s₂, s₁, hs, hqmax, hq, query],
      rfl, rfl, rfl⟩
  have hr₄ : Runs w p ω (.assign 115 (.reg 114)) s₃ .normal out 2 :=
    runs_assign_iff.mpr ⟨query, by simp [Expr.eval, s₃], rfl, rfl, rfl⟩
  refine ⟨out, _, runs_seq_iff.mpr (Or.inr ⟨s₁, _, _, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂, 2, _, hr₂,
      runs_seq_iff.mpr (Or.inr ⟨s₃, _, 2, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩),
    by simp [out, s₃, s₂, s₁, len], by simp [out, s₃, s₂, s₁],
    by simp [out, s₃, query], by simp [out, s₃], rfl, ?_, by decide⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [out, s₃, s₂, s₁, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

/-- Evaluate the current Section 8 factors using the runtime edge cap.
The threshold input registers stay in place, and the heap advances
past both records. -/
@[expose] def initMergedSparsifierFactors (entry decK thr cDeg witnessDen : ℕ) : Stmt :=
  computeInitSparsifierWitnessEdgeCapWithDegree decK thr cDeg ;;
  callInitMachineSparsifierFactors entry witnessDen ;;
  finishInitMachineSparsifierFactors ;;
  .assign 98 (.reg 99)

/-- The factor phase supplies the scaled endpoints and a fresh cursor
for the threshold calculation. -/
theorem initMergedSparsifierFactors_runs
    {w Kγ c Kint cw entry decK thr cDeg witnessDen M heap scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (initMachinePathFactorsContract w Kγ c Kint cw))
    (hK : 1 ≤ decK) (hM : st.regs 23 = M) (hh : st.regs 98 = heap)
    (hz : ZeroFrom st.mem heap)
    (hs : st.regs 4 = scale) (hscale : 0 < scale)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcPos : 0 < cDeg) (hcWord : cDeg < 2 ^ w) (hw : heap + 4 < 2 ^ w) :
    let den := Expander.maxPhiDenOf decK thr M
    let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) M
    let len := scale * (max (gExpImpl Kγ c Kint den M) (gExpImpl Kγ c Kint witnessDen cap)) ^ 2
    let query := scale * max (gQueryImpl Kγ c Kint den M) (gQueryImpl Kγ c Kint witnessDen cap)
    let contract := initMachinePathFactorsContract w Kγ c Kint cw
    cDeg * den < 2 ^ w → cDeg * den * M + 1 < 2 ^ w →
    0 < witnessDen → witnessDen < 2 ^ w →
    max 24 (4 * cw + 8) *
      (Nat.log 2 (den + M + gExpImpl Kγ c Kint den M + gDelImpl Kint den M + 2) + 1) ≤ w →
    max 24 (4 * cw + 8) *
      (Nat.log 2 (witnessDen + cap + gExpImpl Kγ c Kint witnessDen cap + gDelImpl Kint witnessDen cap + 2) + 1) ≤ w →
    len < 2 ^ w → query < 2 ^ w →
    ∃ out cost, Runs w p ω (initMergedSparsifierFactors entry decK thr cDeg witnessDen) st .normal out cost ∧
      out.regs 50 = len ∧ out.regs 52 = len ∧ out.regs 114 = query ∧ out.regs 115 = query ∧
      0 < out.regs 50 ∧ out.regs 52 < 2 ^ w ∧
      out.regs 98 = heap + 4 ∧ out.regs 99 = heap + 4 ∧ ZeroFrom out.mem (heap + 4) ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 50, 52, 58, 63, 98, 99, 114, 115, 122] : List ℕ) →
        out.regs r = st.regs r) ∧
      (∀ a, a < heap ∨ heap + 4 ≤ a → out.mem a = st.mem a) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + decK * (Expander.rOf (4 * M)) ^ 2 + 4) +
        contract.cost [den, M, heap] st.mem + contract.cost [witnessDen, cap, heap + 2] st.mem + 111 := by
  dsimp only
  intro hc hfit hwpos hwword hcw hcw' hlen hquery
  have hd := Expander.maxPhiDenOf_pos decK thr M
  have hmax := (Nat.le_mul_of_pos_left _ hscale).trans_lt hquery
  have hpre := initMachinePathFactorsContract_pre_of_bounds (mem := st.mem) hd hcw
    ((le_max_left _ _).trans_lt hmax) (show heap + 2 < 2 ^ w by omega)
  have hpre' (mem : ℕ → ℕ) := initMachinePathFactorsContract_pre_of_bounds (mem := mem) hwpos hcw'
    ((le_max_right _ _).trans_lt hmax) (show (heap + 2) + 2 < 2 ^ w by omega)
  have hwords : ∀ a ∈ [Expander.maxPhiDenOf decK thr M, M, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact (Nat.le_mul_of_pos_left _ hcPos).trans_lt hc
    · omega
    · omega
  have hwords' : ∀ a ∈ [witnessDen, Spanner.capM_W cDeg
      (1 / (Expander.maxPhiDenOf decK thr M : ℝ)) M, heap + 2], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hwword
    · obtain ⟨_, hX, _⟩ := bounds_word_le hwpos hcw'
      exact (Nat.le_self_pow (by decide : 24 ≠ 0) _).trans_lt hX |>.trans_le' (by omega)
    · omega
  obtain ⟨ready, c₁, hr₁, h63, h58, hm₁, hk₁, hc₁⟩ :=
    computeInitSparsifierWitnessEdgeCapWithDegree_runs (p := p) (ω := ω) hK hM hm hcube hcPos hcWord hc hfit
  obtain ⟨paired, c₂, hr₂, h99, ha, hb, hcapExp, hcapQuery, hk₂, hm₂, hc₂⟩ :=
    callInitMachineSparsifierFactors_runs (ω := ω) himpl h63 ((hk₁ 23 (by decide)).trans hM)
      ((hk₁ 98 (by decide)).trans hh) h58 hwword hwords hwords' (hm₁.symm ▸ hpre) hpre'
  obtain ⟨mid, c₃, hr₃, h50, h52, h114, h115, hm₃, hk₃, hc₃⟩ :=
    finishInitMachineSparsifierFactors_runs (p := p) (ω := ω)
      ((hk₂ 98 (by decide) (by decide)).trans ((hk₁ 98 (by decide)).trans hh))
      ((hk₂ 4 (by decide) (by decide)).trans ((hk₁ 4 (by decide)).trans hs))
      hscale ha hb hcapExp hcapQuery hw hlen hquery
  have h99' := (hk₃ 99 (by decide)).trans h99
  let out := {mid with regs := Function.update mid.regs 98 (heap + 4)}
  have hr₄ : Runs w p ω (.assign 98 (.reg 99)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, h99'], rfl, rfl, rfl⟩
  rw [hm₁] at hc₂
  have hpos : 0 < mid.regs 50 := by
    rw [h50]
    apply Nat.mul_pos hscale
    apply pow_pos
    exact (lt_of_lt_of_le (by decide : 0 < 2) (two_le_gExpImpl Kγ c Kint _ M)).trans_le (le_max_left _ _)
  have h52Word : mid.regs 52 < 2 ^ w := Nat.lt_of_le_of_lt (Nat.le_of_eq (h52.trans h50)) hlen
  refine ⟨out, c₁ + (c₂ + (c₃ + 2 + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨ready, c₁, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨paired, c₂, _, hr₂,
        runs_seq_iff.mpr (Or.inr ⟨mid, c₃, 2, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩),
    by simpa [out] using h50, by simpa [out, h50] using h52,
    by simpa [out] using h114, by simpa [out, h114] using h115,
    by simpa [out] using hpos, by simpa [out] using h52Word,
    by simp [out], by simpa [out] using h99', ?_, ?_,
    fun a ha => (congrFun hm₃ a).trans ((hm₂ a ha).trans (congrFun hm₁ a)), by omega⟩
  · intro a ha
    exact (congrFun hm₃ a).trans ((hm₂ a (Or.inr ha)).trans ((congrFun hm₁ a).trans (hz a (by omega))))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h24, h31, h32, h33, h36, h50', h52', h58', h63', h98, h99'', h114', h115', h122⟩ := hr
    exact (by simp [out, h98] : out.regs r = mid.regs r).trans <|
      (hk₃ r (by simp [h50', h52', h114', h115'])).trans <|
      (hk₂ r h99'' h122).trans (hk₁ r (by simp [h24, h31, h32, h33, h36, h58', h63']))

/-- Decode the exact scaled outputs as the length and time parameters
of the current sparsifier model. -/
theorem initMergedSparsifierFactors_decode
    {Kγ c Kint den M scale : ℕ} {cDeg phiConst : ℝ}
    {paths : Spanner.PathDSTool} {out : State}
    (hscale : 0 < scale)
    (hExp : ∀ phi cap, paths.γ_ExpPath phi cap = (gExpImpl Kγ c Kint (Nat.ceil (1 / phi)) cap : ℝ))
    (hQuery : ∀ phi cap, paths.γ_query phi cap = (gQueryImpl Kγ c Kint (Nat.ceil (1 / phi)) cap : ℝ)) :
    let phiMin := 1 / (den : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let witnessDen := Nat.ceil (1 / phiConst)
    out.regs 50 = scale * (max (gExpImpl Kγ c Kint den M) (gExpImpl Kγ c Kint witnessDen cap)) ^ 2 →
    out.regs 52 = out.regs 50 →
    out.regs 114 = scale * max (gQueryImpl Kγ c Kint den M) (gQueryImpl Kγ c Kint witnessDen cap) →
    out.regs 115 = out.regs 114 →
    (out.regs 50 : ℝ) / scale = Spanner.capGammaL cDeg phiConst paths phiMin M ∧
    (out.regs 52 : ℝ) / scale = Spanner.capGammaL cDeg phiConst paths phiMin M ∧
    (out.regs 114 : ℝ) / scale = Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
    (out.regs 115 : ℝ) / scale = Spanner.capGammaQuery cDeg phiConst paths phiMin M ∧
    0 < out.regs 50 := by
  dsimp only
  intro h50 h52 h114 h115
  obtain ⟨hl, hq⟩ := initSparsifierMachineFactors_eq Kγ c Kint den M cDeg phiConst paths hExp hQuery
  have hs : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale.ne'
  have hleft : (out.regs 50 : ℝ) / scale = Spanner.capGammaL cDeg phiConst paths (1 / (den : ℝ)) M := by
    rw [h50, hl, Nat.cast_mul, Nat.cast_pow, Nat.cast_max, mul_comm, mul_div_cancel_right₀ _ hs]
  have hright : (out.regs 114 : ℝ) / scale =
      Spanner.capGammaQuery cDeg phiConst paths (1 / (den : ℝ)) M := by
    rw [h114, hq, Nat.cast_mul, Nat.cast_max, mul_comm, mul_div_cancel_right₀ _ hs]
  refine ⟨hleft, h52.symm ▸ hleft, hright, h115.symm ▸ hright, ?_⟩
  rw [h50]
  have hbound := two_le_gExpImpl Kγ c Kint den M
  exact Nat.mul_pos hscale (pow_pos ((show 0 < gExpImpl Kγ c Kint den M by omega).trans_le (le_max_left _ _)) _)

/-- Rounding conductance to a reciprocal preserves the denominator
seen by both factor functions of the concrete path tool. -/
theorem initMachinePathTool_factors {Kγ c Kint cw : ℕ} (impl : Spanner.PathDSImpl)
    (hparams : impl.params = pathDSParams Kγ c Kint cw) (phi : ℝ) (M : ℕ) :
    (Spanner.pathDSTool_of_impl impl).γ_ExpPath phi M =
      (gExpImpl Kγ c Kint (Nat.ceil (1 / phi)) M : ℝ) ∧
    (Spanner.pathDSTool_of_impl impl).γ_query phi M =
      (gQueryImpl Kγ c Kint (Nat.ceil (1 / phi)) M : ℝ) := by
  have hround : Nat.ceil (1 / Spanner.roundPhi phi) = Nat.ceil (1 / phi) := by
    simp [Spanner.roundPhi, one_div]
  change impl.params.γ_ExpPath (Spanner.roundPhi phi) M = _ ∧
    impl.params.γ_query (Spanner.roundPhi phi) M = _
  simp only [Spanner.PathDSParams.γ_ExpPath, Spanner.PathDSParams.γ_query, hround, hparams, pathDSParams,
    and_self]

/-- The decoded threshold words supply the length and time fields of
the Section 8 sparsifier parameters at the same edge cap. -/
theorem initMergedSparsifierFactors_params
    {den M scale : ℕ} (tools : Spanner.SpannerTools) (costs : Spanner.SpannerToolCosts)
    (dec : ℝ) (hdec : 0 ≤ dec) (hden : 0 < den) {out : State} :
    let phiMin := 1 / (den : ℝ)
    let hphi : 0 < phiMin := one_div_pos.mpr (by exact_mod_cast hden)
    let cDeg := tools.constructExpander.c_deg
    let phiConst := tools.constructExpander.φ_Const
    let params := Spanner.sparsifyMGParamsOfDecWithTime tools costs phiMin hphi M dec hdec
    (out.regs 50 : ℝ) / scale = Spanner.capGammaL cDeg phiConst tools.pathDS phiMin M →
    (out.regs 52 : ℝ) / scale = Spanner.capGammaL cDeg phiConst tools.pathDS phiMin M →
    (out.regs 114 : ℝ) / scale = Spanner.capGammaQuery cDeg phiConst tools.pathDS phiMin M →
    (out.regs 115 : ℝ) / scale = Spanner.capGammaQuery cDeg phiConst tools.pathDS phiMin M →
    (out.regs 50 : ℝ) / scale = params.γ_ℓ ∧
    (out.regs 52 : ℝ) / scale = params.γ_ℓ ∧
    (out.regs 114 : ℝ) / scale = params.γ_t ∧
    (out.regs 115 : ℝ) / scale = params.γ_t := by
  dsimp only
  intro h50 h52 h114 h115
  exact ⟨h50, h52, h114, h115⟩

/-- The merged factor phase runs with one fixed word multiplier for
the path arguments, arithmetic, and its four fresh words. -/
theorem initMergedSparsifierFactors_budgeted_runs
    (Kγ c Kint cw entry decK thr cDeg witnessDen d ds dh : ℕ)
    (hK : 1 ≤ decK) (hc : 0 < cDeg) (hwitness : 0 < witnessDen) :
    ∃ multiplier, ∀ (words : List ℕ) {w M scale heap : ℕ}
      {p : Program} {ω : ℕ → Bool} {st : State},
      let B := words.length + words.foldr max 0 + 2
      let den := Expander.maxPhiDenOf decK thr M
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) M
      let len := scale * (max (gExpImpl Kγ c Kint den M) (gExpImpl Kγ c Kint witnessDen cap)) ^ 2
      let query := scale * max (gQueryImpl Kγ c Kint den M) (gQueryImpl Kγ c Kint witnessDen cap)
      MeetsContract w p entry (initMachinePathFactorsContract w Kγ c Kint cw) →
      st.regs 23 = M → st.regs 98 = heap → st.regs 4 = scale →
      ZeroFrom st.mem heap → 0 < scale →
      M + 2 ≤ B ^ d → scale ≤ B ^ ds → heap ≤ B ^ dh →
      wordSize multiplier words ≤ w →
      ∃ out cost, Runs w p ω (initMergedSparsifierFactors entry decK thr cDeg witnessDen)
          st .normal out cost ∧
        out.regs 50 = len ∧ out.regs 52 = len ∧ out.regs 114 = query ∧ out.regs 115 = query ∧
        0 < out.regs 50 ∧ out.regs 52 < 2 ^ w ∧
        out.regs 98 = heap + 4 ∧ out.regs 99 = heap + 4 ∧ ZeroFrom out.mem (heap + 4) ∧
        (∀ r, r ∉ ([24, 31, 32, 33, 36, 50, 52, 58, 63, 98, 99, 114, 115, 122] : List ℕ) →
          out.regs r = st.regs r) ∧
        (∀ a, a < heap ∨ heap + 4 ≤ a → out.mem a = st.mem a) ∧
        cost ≤ 120 * (Nat.log 2 (4 * M + 2) + decK * (Expander.rOf (4 * M)) ^ 2 + 4) +
          (initMachinePathFactorsContract w Kγ c Kint cw).cost [den, M, heap] st.mem +
          (initMachinePathFactorsContract w Kγ c Kint cw).cost [witnessDen, cap, heap + 2] st.mem + 111 := by
  obtain ⟨multiplier, hbudget⟩ :=
    initMergedSparsifierFactors_wordSize_bounds decK thr cDeg witnessDen Kγ c Kint cw d ds dh
  refine ⟨multiplier, ?_⟩
  intro words w M scale heap p ω st
  dsimp only
  intro himpl hM hh hs hz hscale hsize hscaleBound hheap hw
  obtain ⟨hm, hcube, hcword, hroom, hwitnessWord, hden, hcap, hpath, hpath', hlen, hquery⟩ :=
    hbudget words M scale heap w hsize hscaleBound hheap hw
  exact initMergedSparsifierFactors_runs himpl hK hM hh hz hs hscale hm hcube
    hc hcword hroom hden hcap hwitness hwitnessWord hpath hpath' hlen hquery

end MinCostFlow.MinRatio
