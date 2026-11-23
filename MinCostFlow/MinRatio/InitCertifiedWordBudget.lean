module

public import MinCostFlow.MinRatio.InitCertifiedEndpointWorkspace
import MinCostFlow.IPM.Machine.ConnectedSolverPolynomialSpace
import MinCostFlow.IPM.Machine.CoefficientWorkspace

/-!
# Word budget for certified solver initialization

Bound the refreshed and packed input, the depth workspaces, and the
arithmetic and addresses for the two threshold endpoints.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- The caller's refresh allocates both coefficient arrays before Init.
Their combined footprint is polynomial in a common bound on the graph
size and numeric format. -/
theorem initRefreshSpace_le {A m L P E : ℕ} (hA : 1 ≤ A)
    (hm : m ≤ A) (hL : L ≤ A) (hP : P ≤ A) (hE : E ≤ A) :
    Num.IPM.lengthArraySpace m L P E + Num.IPM.gradientArraySpace m L P E ≤
      4096 * A ^ 4 := by
  simp only [Num.IPM.lengthArraySpace, Num.IPM.gradientArraySpace,
    ← IPM.Machine.lengthWorkspace_eq, ← IPM.Machine.gradientWorkspace_eq,
    IPM.Machine.gradientWorkspace, IPM.Machine.lengthWorkspace]
  have hmono :
      270 * L * L + 409 * L + 24 + 6 * (P + 4) * (5 * L * L + 24 * L + 3) +
        2 * E * (3 * L + 1) + (4 * E + 12) * (11 * L + 1) ≤
      270 * A * A + 409 * A + 24 + 6 * (A + 4) * (5 * A * A + 24 * A + 3) +
        2 * A * (3 * A + 1) + (4 * A + 12) * (11 * A + 1) := by gcongr
  apply le_trans (b := 2 * ((A + 1) * A) +
    2 * (A * (270 * A * A + 409 * A + 24 +
      6 * (A + 4) * (5 * A * A + 24 * A + 3) +
      2 * A * (3 * A + 1) + (4 * A + 12) * (11 * A + 1))) +
    A * (45 * A * A + 65 * A + 3))
  · have h₁ : (m + 1) * L ≤ (A + 1) * A := by gcongr
    have h₂ := Nat.mul_le_mul hm hmono
    have h₃ : m * (45 * L * L + 65 * L + 3) ≤ A * (45 * A * A + 65 * A + 3) := by gcongr
    convert Nat.add_le_add (Nat.add_le_add h₁ h₂)
      (Nat.add_le_add h₁ (Nat.add_le_add h₂ h₃)) using 1 <;> ring
  · have h₂ : A ^ 2 ≤ A ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
    have h₃ : A ^ 3 ≤ A ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
    have h₁ : A ≤ A ^ 4 := Nat.le_self_pow (by decide) _
    nlinarith only [h₁, h₂, h₃]

/-- The refresh return value passed as Init's heap has a fixed-power
bound as soon as the epoch heap and numeric dimensions do. -/
theorem initRefreshCursor_power_bound {B heap m L P E dh d : ℕ}
    (hB : 2 ≤ B) (hh : heap ≤ B ^ dh)
    (hm : m ≤ B ^ d) (hL : L ≤ B ^ d) (hP : P ≤ B ^ d) (hE : E ≤ B ^ d) :
    heap + (Num.IPM.lengthArraySpace m L P E + Num.IPM.gradientArraySpace m L P E) ≤
      B ^ (max dh (12 + 4 * d) + 1) := by
  let e := max dh (12 + 4 * d)
  have hpos : 0 < B := by omega
  have hs := initRefreshSpace_le (Nat.one_le_pow _ _ hpos) hm hL hP hE
  have hs' : 4096 * (B ^ d) ^ 4 ≤ B ^ (12 + 4 * d) := by
    rw [pow_add, Nat.mul_comm 4 d, pow_mul]
    exact Nat.mul_le_mul_right _ (show 4096 ≤ B ^ 12 from Nat.pow_le_pow_left hB 12)
  have hheap : heap ≤ B ^ e :=
    hh.trans (Nat.pow_le_pow_right hpos (le_max_left _ _))
  have hrefresh : _ ≤ B ^ e :=
    hs.trans (hs'.trans (Nat.pow_le_pow_right hpos (le_max_right _ _)))
  calc
    _ ≤ 2 * B ^ e := by omega
    _ = B ^ e * 2 := Nat.mul_comm _ _
    _ ≤ B ^ e * B := Nat.mul_le_mul_left _ hB
    _ = _ := (pow_succ B e).symm

/-- The encoded circulation bounds the graph part of the packed input.
Only the caller's heap and the numeric limb count need separate bounds. -/
theorem initPackedSolverCursor_power_bound (J : Scaling.Circulation)
    {heap limbs dh dl : ℕ} :
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let G := IPM.namedInstance (IPM.Machine.solverConnectedAugmented J)
    heap ≤ B ^ dh → limbs ≤ B ^ dl →
    heap + (limbs + 1) + 6 + DynSpanner.Program.dynGraphSize G.n G.m ≤
      B ^ (max (max dh dl) 2 + 5) := by
  dsimp only
  intro hh hl
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let I := IPM.Machine.solverConnectedAugmented J
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hn : J.n ≤ J.solverWords.foldr max 0 := le_max_left _ _
  have hm := J.solverWords_length
  have hn' : (IPM.namedInstance I).n = J.n + 1 := by
    change (Finset.range (J.n + 1)).card = _
    exact Finset.card_range _
  have hm' : (IPM.namedInstance I).m ≤ J.m + 2 * J.n := by
    rw [IPM.namedInstance_m]
    simpa only [I, IPM.Machine.solverConnectedAugmented, Scaling.Circulation.toInstance_m] using
      IPM.connectedInitialInstance_m_le J.toInstance (IPM.Machine.solverPenalty J.m : ℤ)
  have hlin : J.m + 2 * J.n ≤ 2 * B := by dsimp [B]; omega
  have hpow : 2 * B ≤ B ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right B hB
  exact initPackedGraphCursor_power_bound hB hh hl
    (hn'.le.trans ((show J.n + 1 ≤ 2 * B by dsimp [B]; omega).trans hpow))
    (hm'.trans (hlin.trans hpow))

/-- At the connected solver's quality format, the packed input cursor
needs only a bound on the caller's heap and quality exponent. -/
theorem initPackedQualitySolverCursor_power_bound (J : Scaling.Circulation)
    {heap k q dh : ℕ} (hn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m)
    (hcap : ∀ e, 1 ≤ J.capacity e) (hk : 2 ^ k ≤ (J.n + J.m + 2) ^ q) :
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let I := IPM.Machine.solverConnectedAugmented J
    let G := IPM.namedInstance I
    let limbs := IPM.Machine.ipmQualityLimbs I.m (IPM.Machine.solverPenalty J.m) k
    heap ≤ B ^ dh →
    heap + (limbs + 1) + 6 + DynSpanner.Program.dynGraphSize G.n G.m ≤
      B ^ (max (max dh (max 41 q + 7)) 2 + 5) := by
  dsimp only
  intro hh
  obtain ⟨hM, hUpper⟩ := IPM.Machine.solverConnectedAugmented_size J hn hm hcap
  have hL := IPM.Machine.ipmQualityLimbs_connected_poly J.n J.m _ k q hm hM hUpper hk
  have hn' : J.n ≤ J.solverWords.foldr max 0 := le_max_left _ _
  have hm' := J.solverWords_length
  have hB : J.n + J.m + 2 ≤ J.solverWords.length + J.solverWords.foldr max 0 + 2 := by omega
  exact initPackedSolverCursor_power_bound J hh (hL.trans (Nat.pow_le_pow_left hB _))

/-- The epoch heap, coefficient refresh, and graph packing share one
polynomial address bound at the connected solver's quality format. -/
theorem initRefreshedPackedSolverCursor_power_bound (J : Scaling.Circulation)
    {heap k q dh : ℕ} (hn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m)
    (hcap : ∀ e, 1 ≤ J.capacity e) (hk : 2 ^ k ≤ (J.n + J.m + 2) ^ q) :
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let I := IPM.Machine.solverConnectedAugmented J
    let V := IPM.Machine.solverPenalty J.m
    let G := IPM.namedInstance I
    let L := IPM.Machine.ipmQualityLimbs I.m V k
    let P := IPM.Machine.ipmQualityPrecision I.m V k
    let E := IPM.Machine.ipmQualityRangeExponent I.m V k
    let d := max 41 q + 7
    heap ≤ B ^ dh →
    heap + (Num.IPM.lengthArraySpace I.m L P E + Num.IPM.gradientArraySpace I.m L P E) +
      (L + 1) + 6 + DynSpanner.Program.dynGraphSize G.n G.m ≤
        B ^ (max (max (max dh (12 + 4 * d) + 1) d) 2 + 5) := by
  dsimp only
  intro hh
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let I := IPM.Machine.solverConnectedAugmented J
  let V := IPM.Machine.solverPenalty J.m
  let L := IPM.Machine.ipmQualityLimbs I.m V k
  let d := max 41 q + 7
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hn' : J.n ≤ J.solverWords.foldr max 0 := le_max_left _ _
  have hm' := J.solverWords_length
  have hbase : J.n + J.m + 2 ≤ B := by dsimp [B]; omega
  obtain ⟨hM, hUpper⟩ := IPM.Machine.solverConnectedAugmented_size J hn hm hcap
  have hL : L ≤ B ^ d :=
    (IPM.Machine.ipmQualityLimbs_connected_poly J.n J.m I.m k q hm hM hUpper hk).trans
      (Nat.pow_le_pow_left hbase _)
  have hM' : I.m ≤ B ^ d := by
    have hJ : J.m ≤ B := by dsimp [B]; omega
    calc
      _ ≤ 7 * J.m := hUpper
      _ ≤ B ^ 3 * B := Nat.mul_le_mul
        ((by decide : 7 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left hB _)) hJ
      _ = B ^ 4 := (pow_succ B 3).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)
  have hP : IPM.Machine.ipmQualityPrecision I.m V k ≤ L := by
    simp only [L, IPM.Machine.ipmQualityLimbs]
    omega
  have hE : IPM.Machine.ipmQualityRangeExponent I.m V k ≤ L := by
    simp only [L, IPM.Machine.ipmQualityLimbs]
    omega
  exact initPackedQualitySolverCursor_power_bound J hn hm hcap hk
    (initRefreshCursor_power_bound hB hh hM' hL (hP.trans hL) (hE.trans hL))

/-- The cursor passed to the endpoint stage inherits a fixed-power
bound from the initial cursor and the two depth logarithms. -/
theorem certifiedEndpointCursor_power_bound (J : Scaling.Circulation)
    {threshold h heap afterChain afterSparse dh : ℕ} :
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let d := max 2 (Nat.clog 2 threshold + 1)
    let dc := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    let E₁ := (M + 2).size
    let E₂ := (M ^ 2 + 2).size
    let P₁ := h * (38 * (2 ^ 48 * E₁) ^ 8 + E₁ + E₁ + 10)
    let P₂ := h * (38 * (2 ^ 24 * E₂) ^ 8 + E₂ + E₂ + 10)
    let L₁ := P₁ + E₁ + 4
    let L₂ := P₂ + E₂ + 4
    heap ≤ B ^ dh →
    afterChain ≤ heap + L₁ + L₁ + Num.logarithmSpace L₁ P₁ E₁ →
    afterSparse ≤ afterChain + L₂ + L₂ + Num.logarithmSpace L₂ P₂ E₂ →
    afterSparse + 4 ≤ B ^ (max (max dh (10 + 3 * (dc + 8 * d)) + 1)
      (10 + 3 * (dc + 8 * (2 * d))) + 1 + 3) := by
  dsimp only
  intro hh hc hs
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let dc := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hcoeff : h * (38 * (2 ^ 48) ^ 8 + 12) + 5 ≤ B ^ dc :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left hB _)
  have hcoeff' : h * (38 * (2 ^ 24) ^ 8 + 12) + 5 ≤ B ^ dc := by
    apply le_trans _ hcoeff
    gcongr
    decide
  obtain ⟨hm, hm₂⟩ := solverDepthPaddedSize_power_bounds J threshold
  have bits (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have hchain := hc.trans (initDepthLog_runtime_address_bound (exponent := 48) hB
    (show 1 ≤ (M + 2).size from Nat.lt_size.mpr (by norm_num))
    ((bits _).trans hm) hh hcoeff)
  have hsparse := hs.trans (initDepthLog_runtime_address_bound (exponent := 24) hB
    (show 1 ≤ (M ^ 2 + 2).size from Nat.lt_size.mpr (by norm_num))
    ((bits _).trans hm₂) hchain hcoeff')

  let e := max (max dh (10 + 3 * (dc + 8 * max 2 (Nat.clog 2 threshold + 1))) + 1)
    (10 + 3 * (dc + 8 * (2 * max 2 (Nat.clog 2 threshold + 1)))) + 1
  have hsparse' : afterSparse ≤ B ^ e := hsparse
  have he : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)
  change afterSparse + 4 ≤ B ^ (e + 3)
  calc
    _ ≤ 8 * B ^ e := by omega
    _ = B ^ e * 8 := Nat.mul_comm _ _
    _ ≤ B ^ e * B ^ 3 :=
      Nat.mul_le_mul_left (B ^ e) (show 8 ≤ B ^ 3 from Nat.pow_le_pow_left hB 3)
    _ = B ^ (e + 3) := (pow_add B e 3).symm

/-- The installed limb count inherits a power bound from the scale and
the logarithm input. -/
theorem certifiedEndpointLimbs_power_bound
    {B input precision ds di : ℕ} (hB : 2 ≤ B)
    (hs : 2 ^ precision ≤ B ^ ds) (hi : input + 3 ≤ B ^ di) :
    precision + (input + 2).size + 4 ≤ B ^ (max ds di + 3) := by
  let e := max ds di
  have hp : precision ≤ B ^ e :=
    (show precision < 2 ^ precision from Nat.lt_two_pow_self).le.trans
      (hs.trans (Nat.pow_le_pow_right (by omega) (le_max_left ds di)))
  have hr : (input + 2).size ≤ input + 3 :=
    Nat.size_le.mpr ((show input + 2 < 2 ^ (input + 2) from Nat.lt_two_pow_self).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hi' : (input + 2).size ≤ B ^ e :=
    hr.trans (hi.trans (Nat.pow_le_pow_right (by omega) (le_max_right ds di)))
  have he : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 8 * B ^ e := by omega
    _ ≤ _ := by
      rw [pow_add, Nat.mul_comm 8]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 3)

/-- Both logarithm workspaces and the remaining table fit in one word-sized
address range when the starting cursor and workspace dimensions have fixed
power bounds. The tail includes any cells needed after the logarithms. -/
theorem certifiedEndpointAddress_wordSize_bound
    (words : List ℕ) {c heap limbs precision range tail dh dl dt : ℕ}
    (hr : 2 ≤ range) (hprec : precision ≤ limbs) (hrange : range ≤ limbs) :
    let B := words.length + words.foldr max 0 + 2
    heap ≤ B ^ dh → limbs ≤ B ^ dl → tail ≤ B ^ dt →
    max (max dh dt) (11 + 3 * dl) + 2 ≤ c →
    heap + limbs + limbs + Num.logarithmSpace limbs precision 2 +
      limbs + limbs + Num.logarithmSpace limbs precision range + tail <
        2 ^ wordSize c words := by
  dsimp only
  intro hh hl ht hc
  let B := words.length + words.foldr max 0 + 2
  let e := max (max dh dt) (11 + 3 * dl)
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hlPos : 1 ≤ limbs := by omega
  have hspace₁ := initDepthLog_space_le hlPos le_rfl hprec (hr.trans hrange)
  have hspace₂ := initDepthLog_space_le hlPos le_rfl hprec hrange
  have h2000 : 2000 ≤ B ^ 11 :=
    (by decide : 2000 ≤ 2 ^ 11).trans (Nat.pow_le_pow_left hB _)
  have hspace : 2000 * limbs ^ 3 ≤ B ^ e := by
    apply le_trans _ (Nat.pow_le_pow_right (by omega : 0 < B) (le_max_right (max dh dt) _))
    rw [pow_add, Nat.mul_comm 3 dl, pow_mul]
    exact Nat.mul_le_mul h2000 (Nat.pow_le_pow_left hl _)
  have hh' : heap ≤ B ^ e := hh.trans (Nat.pow_le_pow_right (by omega : 0 < B)
    (le_trans (le_max_left dh dt) (le_max_left (max dh dt) (11 + 3 * dl))))
  have ht' : tail ≤ B ^ e := ht.trans (Nat.pow_le_pow_right (by omega : 0 < B)
    (le_trans (le_max_right dh dt) (le_max_left (max dh dt) (11 + 3 * dl))))
  calc
    _ ≤ 3 * B ^ e := by omega
    _ ≤ B ^ c := by
      have hnext : 3 * B ^ e ≤ B ^ (e + 2) := by
        rw [pow_add, Nat.mul_comm 3]
        exact Nat.mul_le_mul_left _ ((by decide : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hB _))
      exact hnext.trans (Nat.pow_le_pow_right (by omega) hc)
    _ < _ := pow_lt_two_pow_wordSize (by omega) words

/-- The table writer reserves thirty-nine limb blocks before its
`depth + 1` entries. The solver header takes seventeen words and the level initializer
reserves two more arrays of `depth + 1` words. -/
theorem certifiedEndpointTableTail_power_bound
    {B limbs depth dl dd : ℕ} (hB : 2 ≤ B)
    (hl : limbs ≤ B ^ dl) (hd : depth ≤ B ^ dd) :
    39 * limbs + 3 * (depth + 1) + 17 ≤ B ^ (max dl dd + 6) := by
  let e := max dl dd
  have hl' : limbs ≤ B ^ e :=
    hl.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hd' : depth ≤ B ^ e :=
    hd.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have he : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 64 * B ^ e := by omega
    _ ≤ _ := by
      rw [pow_add, Nat.mul_comm 64]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 6)

/-- One multiplier covers the coefficient, graph logarithm, scaled growth,
and both endpoint allocations. -/
theorem certifiedEndpointWordSize_bounds
    (words : List ℕ) {c coefficient input precision growth heap depth dc di ds dg dh dd : ℕ}
    (hr : 2 ≤ (input + 2).size) :
    let B := words.length + words.foldr max 0 + 2
    let L := precision + (input + 2).size + 4
    let dl := max ds di + 3
    coefficient + 3 ≤ B ^ dc → input + 3 ≤ B ^ di →
    2 ^ precision ≤ B ^ ds → growth ≤ B ^ dg →
    heap ≤ B ^ dh → depth ≤ B ^ dd →
    max (dc + 2 * ds) (max (di + ds) (ds + dg)) + 1 ≤ c →
    max (max dh (max dl dd + 6)) (11 + 3 * dl) + 2 ≤ c →
    (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ wordSize c words ∧
      (input + 3) * 2 ^ precision < 2 ^ wordSize c words ∧
      2 ^ precision * growth < 2 ^ wordSize c words ∧
      precision < wordSize c words ∧
      heap + L + L + Num.logarithmSpace L precision 2 +
        L + L + Num.logarithmSpace L precision (input + 2).size +
        (39 * L + 3 * (depth + 1) + 17) <
          2 ^ wordSize c words := by
  dsimp only
  intro hc hi hs hg hh hd hwords haddr
  obtain ⟨hcoef, hin, hgrowth⟩ :=
    certifiedThresholdEndpoint_wordSize_bounds words hc hi hs hg hwords
  have hprec : precision < wordSize c words := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < input + 3)).trans_lt hin
  have hB : 2 ≤ words.length + words.foldr max 0 + 2 := by omega
  have hl := certifiedEndpointLimbs_power_bound hB hs hi
  have ht := certifiedEndpointTableTail_power_bound hB hl hd
  exact ⟨hcoef, hin, hgrowth, hprec,
    certifiedEndpointAddress_wordSize_bound words hr (by omega) (by omega)
      hh hl ht haddr⟩

/-- The workspace sizing arithmetic fits before any endpoint
logarithm is evaluated. The aligned precision exceeds the unrounded
minimum, and the remaining rounding offset is less than one limb. -/
theorem certifiedEndpointWorkspace_wordSize_bounds
    (words : List ℕ) {c depth factor coefficient input h dd df di : ℕ} :
    let B := words.length + words.foldr max 0 + 2
    let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (minimum + (h - 1)) / h * h
    let ds := 2 * (dd + df + di) + 17 + Nat.clog 2 (coefficient + 1) + (h - 1)
    0 < h → 2 * (depth + 1) ≤ B ^ dd → factor ≤ B ^ df → input + 3 ≤ B ^ di →
    max (max (df + 1) (di + 1)) (max ds (max ds di + 3)) ≤ c →
    factor + 1 < 2 ^ wordSize c words ∧ input + 4 < 2 ^ wordSize c words ∧
      minimum + (h - 1) < 2 ^ wordSize c words ∧
      precision + (input + 2).size + 4 < 2 ^ wordSize c words ∧
      2 ^ precision < 2 ^ wordSize c words := by
  dsimp only
  intro hh hd hf hi hw
  let B := words.length + words.foldr max 0 + 2
  have hB : 2 ≤ B := by dsimp [B]; omega
  have fit {x e : ℕ} (hx : x ≤ B ^ e) (he : e ≤ c) :
      x < 2 ^ wordSize c words :=
    (hx.trans (Nat.pow_le_pow_right (by omega) he)).trans_lt
      (pow_lt_two_pow_wordSize (by omega) words)
  have succBound {x e : ℕ} (hx : x ≤ B ^ e) : x + 1 ≤ B ^ (e + 1) := by
    have hp : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ B ^ e * 2 := by omega
      _ ≤ B ^ e * B := Nat.mul_le_mul_left _ hB
      _ = _ := (pow_succ B e).symm
  have hs := certifiedThresholdEndpoint_scale_power_bound (h := h) (coefficient := coefficient) hB hd hf hi
  have hl := certifiedEndpointLimbs_power_bound hB hs hi
  let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
    (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
  let precision := (minimum + (h - 1)) / h * h
  have hp : minimum + (h - 1) ≤ 2 ^ precision := by
    have hmod := Nat.mod_lt (minimum + (h - 1)) hh
    have hdiv := Nat.mod_add_div (minimum + (h - 1)) h
    rw [Nat.mul_comm h] at hdiv
    have hmin : 17 ≤ minimum := by dsimp [minimum]; omega
    have hquot : 0 < (minimum + (h - 1)) / h := Nat.div_pos (by omega) hh
    have hhlen : h ≤ precision := Nat.le_mul_of_pos_left _ hquot
    have hnonzero : 0 < precision := hh.trans_le hhlen
    have htwo : 2 * precision ≤ 2 ^ precision := by
      have hh' := Nat.lt_two_pow_self (n := precision - 1)
      have he : precision - 1 + 1 = precision := by omega
      have ht := Nat.mul_le_mul_right 2 (show precision ≤ 2 ^ (precision - 1) by omega)
      rw [← pow_succ, he] at ht
      simpa only [Nat.mul_comm 2 precision] using ht
    change _ ≤ 2 ^ precision
    change (minimum + (h - 1)) % h + precision = _ at hdiv
    omega
  exact ⟨fit (succBound hf) (by omega), fit (succBound hi) (by omega),
    fit (hp.trans hs) (by omega), fit hl (by omega), fit hs (by omega)⟩

/-- Run the endpoint workspace sizing code at a word width derived from
fixed-power bounds on its inputs. -/
theorem initCertifiedEndpointWorkspace_budgeted_runs
    (words : List ℕ)
    {w c dd df di power bits clog depth sparseDepth growth growthScale buckets degree coefficient M h vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hM : st.regs 22 = M) (hN : st.regs 92 = vertices) (hpos : 0 < M)
    (hpow : MeetsContract w p power (initStretchPowerContract w))
    (h75 : st.regs 75 = depth) (hDepth : 2 * (depth + 1) + 1 < 2 ^ w)
    (hcoarse : concreteThresholdScale depth < 2 ^ w)
    (h44 : st.regs 44 = sparseDepth) (h50 : st.regs 50 = growthScale * growth)
    (h4 : st.regs 4 = growthScale) (hs : 0 < growthScale) (hg : 0 < growth)
    (hSparseDepth : max (sparseDepth + 1) 3 < 2 ^ w)
    (hScaled : growthScale * growth < 2 ^ w)
    (hFirst : 3 ^ sparseDepth * growth ^ (sparseDepth + 1) < 2 ^ w)
    (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree) (hbPos : 0 < buckets)
    (hh : 0 < h) (hhw : h < 2 ^ w) (hw : 11 < 2 ^ w) :
    let factor := 11 * (sparseDepth + 1) * growth * buckets * (2 * degree + 190)
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (minimum + (h - 1)) / h * h
    let B := words.length + words.foldr max 0 + 2
    let ds := 2 * (dd + df + di) + 17 + Nat.clog 2 (coefficient + 1) + (h - 1)
    2 * (depth + 1) ≤ B ^ dd → factor ≤ B ^ df → input + 3 ≤ B ^ di →
    max (max (df + 1) (di + 1)) (max ds (max ds di + 3)) ≤ c → wordSize c words ≤ w →
    ∃ out cost, Runs w p ω (initCertifiedEndpointWorkspace power bits clog coefficient h)
        st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧ out.regs 4 = 2 ^ precision ∧
      Nat.clog 2 (2 * (depth + 1) * factor *
        ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision ∧
      Nat.clog 2 (2 * (depth + 1)) ≤ precision ∧ 16 ≤ precision ∧
      range + 11 ≤ precision ∧ out.regs 35 = growth ∧ out.regs 92 = vertices ∧ h ∣ precision ∧ out.mem = st.mem ∧
      cost ≤ 14 * range + 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3) +
        Nat.clog 2 (2 * (depth + 1))) + 40 * sparseDepth + 237 := by
  dsimp only
  intro hd hf hi hc hword
  obtain ⟨hf', hi', ht, hl, hs'⟩ :=
    certifiedEndpointWorkspace_wordSize_bounds words hh hd hf hi hc
  have lift {x : ℕ} (hx : x < 2 ^ wordSize c words) : x < 2 ^ w :=
    hx.trans_le (Nat.pow_le_pow_right (by decide) hword)
  exact initCertifiedEndpointWorkspace_sized_runs hp hb hM hN hpos hpow h75 hDepth hcoarse
    h44 h50 h4 hs hg hSparseDepth hScaled hFirst h47 h48 hbPos hh hhw hw
    (lift hf') (lift hi') (lift ht) (lift hl) (lift hs')

end MinCostFlow.MinRatio
