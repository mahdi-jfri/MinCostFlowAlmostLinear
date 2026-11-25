module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import WordRAM.Std.Bits
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
public import MinCostFlow.NarrowProg.Stage1Layout
public import MinCostFlow.NarrowProg.TopBitLength
import MinCostFlow.Narrow.CostBits
import MinCostFlow.Narrow.CostUnitsClip
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 1 startup Phase A (`stage1StartMeta`, `stage1WriteLayout`, `stage1StartHdr`)

Splits Phase A of Stage 1 startup into three small, low-register procedures:
- `stage1StartMeta`: computes `L`, `T_U`, `K_cap`, `p`, `q`, `lowerClip`, `upperClip`,
  `freezeThreshold`, and `numRounds`, storing the first 10 words of `pCtx` (`h[0..9]`).
- `stage1WriteLayout`: computes the derived pointers of `mkStage1Layout h n m K_cap`,
  writes `h[10..23]` and `pResIn` (`h[24..32]`), and returns `hAfter`.
- `stage1StartHdr`: loads input header fields, compresses vertices, invokes `stage1StartMeta`
  and `stage1WriteLayout`, and returns `hAfter`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
  MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

private theorem free_merge_left {a b c d s : ℕ} (h1 : a + b = c) (h2 : b + d = s) :
    Assn.free a b * Assn.free c d = Assn.free a s := by
  subst h1; subst h2; exact (Assn.free_add' a b d).symm

theorem stage1StartHdr_free_split {w h n m : ℕ}
    (hfit : h + 37 + n + 2 * m ≤ 2 ^ w) :
    let hMid := h + 37 + n + 2 * m
    Assn.free h (2 ^ w - h) =
      Assn.list h (List.replicate 10 0) *
      Assn.list (h + 10) (List.replicate 6 0) *
      Assn.list (h + 16) (List.replicate 8 0) *
      Assn.list (h + 24) (List.replicate 9 0) *
      Assn.list (h + 33) (List.replicate 4 0) *
      Assn.list (h + 37) (List.replicate n 0) *
      Assn.list (h + 37 + n) (List.replicate m 0) *
      Assn.list (h + 37 + n + m) (List.replicate m 0) *
      Assn.free hMid (2 ^ w - hMid) := by
  have hf_eq : ∀ a r : ℕ, Assn.list a (List.replicate r 0) = Assn.free a r := fun _ _ => rfl
  simp only [hf_eq]
  symm
  rw [free_merge_left (s := 16) (by omega) (by omega)]
  rw [free_merge_left (s := 24) (by omega) (by omega)]
  rw [free_merge_left (s := 33) (by omega) (by omega)]
  rw [free_merge_left (s := 37) (by omega) (by omega)]
  rw [free_merge_left (s := 37 + n) (by omega) (by omega)]
  rw [free_merge_left (s := 37 + n + m) (by omega) (by omega)]
  rw [free_merge_left (s := 37 + n + 2 * m) (by omega) (by omega)]
  exact free_merge_left (s := 2 ^ w - h) (by omega) (by omega)

theorem stage1Start_ctx_merge {h : ℕ}
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 c0 c1 c2 c3 c4 c5 c6 c7 : ℕ) :
    Assn.list h [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] *
    Assn.list (h + 10) [b0, b1, b2, b3, b4, b5] *
    Assn.list (h + 16) [c0, c1, c2, c3, c4, c5, c6, c7] =
    Assn.list h [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5,
      c0, c1, c2, c3, c4, c5, c6, c7] := by
  have h1 : Assn.list h [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] *
      Assn.list (h + 10) [b0, b1, b2, b3, b4, b5] =
      Assn.list h [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5] := by
    simpa using (Assn.list_append h [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
      [b0, b1, b2, b3, b4, b5]).symm
  rw [h1]
  simpa using (Assn.list_append h
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5]
    [c0, c1, c2, c3, c4, c5, c6, c7]).symm

/-- Opaque helper for the non-header body of `stage1Input` (keeps atom count tiny during loads). -/
def stage1InputBody (I : Circulation) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) : Assn :=
  Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
  Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list pCostPtrs costPtrs *
  Assn.list pCostLens (costLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

theorem stage1Input_split_hdr (I : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) :
    stage1Input I k capPtrs capLimbs costPtrs costLimbs
      pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens =
    Assn.list pIn [I.n, I.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
      stage1InputBody I capPtrs capLimbs costPtrs costLimbs
        pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens := by
  unfold stage1Input stage1InputBody; simp only [mul_assoc]

/-- Opaque helper for the cap/cost-limbs portion of `stage1Input`. -/
def stage1InputLimbs (I : Circulation) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) : Assn :=
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
  Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list pCostPtrs costPtrs *
  Assn.list pCostLens (costLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

theorem stage1InputBody_split_th (I : Circulation) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) :
    stage1InputBody I capPtrs capLimbs costPtrs costLimbs
      pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens =
    Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
    Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
    stage1InputLimbs I capPtrs capLimbs costPtrs costLimbs
      pCapPtrs pCapLens pCostSign pCostPtrs pCostLens := by
  unfold stage1InputBody stage1InputLimbs; simp only [mul_assoc]

/-! ### 1. Parameter metadata helper (`stage1StartMeta`) -/

/-- Compute `L`, `T_U`, `K_cap`, `p`, `q`, `loClip`, `upClip`, `theta`, `numRounds`, write the
10-word prefix `[n', m, k, L, TU, Kcap, loClip, upClip, theta, numRounds]` at `pOut`, and
return `Kcap`. -/
wram_def stage1StartMeta (topIdx clogIdx blIdx : ℕ)
    (n', m, k, pCapPtrs, pCapLens, pCostPtrs, pCostLens, pOut) {
  L := topIdx(pCostPtrs, pCostLens, m, k)
  TU := topIdx(pCapPtrs, pCapLens, m, k)
  Kcap := TU / k + 2
  t2 := 2 * m
  q := clogIdx(t2)
  t4 := t2 * t2
  t8 := t4 * t4
  t16 := t8 * t8
  p := clogIdx(t16)
  loClip := 1 <<< p
  upClip := 1 <<< (p + q)
  theta := 8 * upClip
  szN := blIdx(n' + 1)
  numRounds := L + p + 1 + szN
  mem[pOut] := n'
  mem[pOut + 1] := m
  mem[pOut + 2] := k
  mem[pOut + 3] := L
  mem[pOut + 4] := TU
  mem[pOut + 5] := Kcap
  mem[pOut + 6] := loClip
  mem[pOut + 7] := upClip
  mem[pOut + 8] := theta
  mem[pOut + 9] := numRounds
  return Kcap
}

def stage1StartMetaSpec (w : ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × List ℕ × List (List ℕ)) where
  pre := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs) args =>
    ⨆ (pCapPtrs : ℕ) (pCapLens : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ) (pOut : ℕ),
      ⌜args = [I.compress.n, I.m, k, pCapPtrs, pCapLens, pCostPtrs, pCostLens, pOut] ∧
        0 < I.m ∧ capPtrs.length = I.m ∧ capLimbs.length = I.m ∧
        costPtrs.length = I.m ∧ costLimbs.length = I.m ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (capLimbs.getD j []) ∧
          (capLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩) ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (costLimbs.getD j []) ∧
          (costLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs) ∧
        1 ≤ k ∧ 2 * k ≤ w ∧ 2 * I.m + 1 < 2 ^ k ∧
        (6 * I.m + 21) * upperClip I.m < 2 ^ w ∧
        narrowCostRounds I.compress < 2 ^ w ∧
        bitScalingPhases I / k + 2 < 2 ^ w⌝ *
      Assn.list pCapPtrs capPtrs *
      Assn.list pCapLens (capLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
      Assn.list pCostPtrs costPtrs *
      Assn.list pCostLens (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
      Assn.list pOut (List.replicate 10 0)
  post := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs) args Kcap =>
    ⨆ (pCapPtrs : ℕ) (pCapLens : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ) (pOut : ℕ),
      ⌜args = [I.compress.n, I.m, k, pCapPtrs, pCapLens, pCostPtrs, pCostLens, pOut] ∧
        Kcap = bitScalingPhases I / k + 2⌝ *
      Assn.list pCapPtrs capPtrs *
      Assn.list pCapLens (capLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
      Assn.list pCostPtrs costPtrs *
      Assn.list pCostLens (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
      Assn.list pOut [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
        bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m,
        freezeThreshold I.m, narrowCostRounds I.compress]

def stage1StartMetaCost (I : Circulation) : ℕ :=
  400 * I.m + 12 * bitScalingPhases I + 12 * costScaleBits I + 350

private def stage1MetaCap (m : ℕ) (pCapPtrs pCapLens : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ)) : Assn :=
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  (∏ j ∈ Finset.range m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))

private def stage1MetaCost (m : ℕ) (pCostPtrs pCostLens : ℕ)
    (costPtrs : List ℕ) (costLimbs : List (List ℕ)) : Assn :=
  Assn.list pCostPtrs costPtrs *
  Assn.list pCostLens (costLimbs.map List.length) *
  (∏ j ∈ Finset.range m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

private theorem stage1MetaCap_eq (m : ℕ) (pCapPtrs pCapLens : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ)) :
    Assn.list pCapPtrs capPtrs *
    Assn.list pCapLens (capLimbs.map List.length) *
    (∏ j ∈ Finset.range m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) =
    stage1MetaCap m pCapPtrs pCapLens capPtrs capLimbs := rfl

private theorem stage1MetaCost_eq (m : ℕ) (pCostPtrs pCostLens : ℕ)
    (costPtrs : List ℕ) (costLimbs : List (List ℕ)) :
    Assn.list pCostPtrs costPtrs *
    Assn.list pCostLens (costLimbs.map List.length) *
    (∏ j ∈ Finset.range m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) =
    stage1MetaCost m pCostPtrs pCostLens costPtrs costLimbs := rfl

theorem stage1StartMeta_meets {w : ℕ} {p : Program} {f topIdx clogIdx blIdx : ℕ}
    (hp : p.procs[f]? = some (stage1StartMeta topIdx clogIdx blIdx))
    (htop : Meets w p topIdx ((topBitLengthSpec w).withCost fun x _ =>
      75 * x.2.2.length + (12 * Nat.size (maxTopLimb x.2.2) + 10) + 50))
    (hclog : Meets w p clogIdx ((clog2Spec w).withCost fun x _ => 12 * Nat.size (x - 1) + 19))
    (hbl : Meets w p blIdx ((bitLengthSpec w).withCost fun x _ => 12 * Nat.size x + 10)) :
    Meets w p f ((stage1StartMetaSpec w).withCost fun x _ => stage1StartMetaCost x.1) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, costPtrs, costLimbs⟩
    with hm_pos hcp hcl hcop hcol hcapSpec hcostSpec hk h2k h2mk huc hnr hKfit
  have h2b : 2 ≤ 2 ^ k := two_le_pow hk
  have h2bw : 2 ^ k + 2 ^ k ≤ 2 ^ w := pow_lt_pow_w hk h2k
  have hCn_le : I.compress.n ≤ 2 * I.m := I.endpointLabels_count_le
  have hL_eq : Nat.size (maxLimbsVal k costLimbs) = costScaleBits I := by
    rw [costScaleBits, circMaxCost_eq_maxLimbsVal I k costLimbs hcol]
    intro j hj
    have := (hcostSpec j hj).2.2
    rwa [List.getD_eq_getElem _ _ (by omega)] at this
  have hTU_eq : Nat.size (maxLimbsVal k capLimbs) = bitScalingPhases I := by
    rw [bitScalingPhases, circMaxCapacity_eq_maxLimbsVal I k capLimbs hcl]
    intro j hj
    have := (hcapSpec j hj).2.2
    rwa [List.getD_eq_getElem _ _ (by omega)] at this
  have hcap_all : ∀ l ∈ capLimbs, CanonicalLimbs k l ∧ l.length * k < 2 ^ w := by
    intro l hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have := hcapSpec j (by omega); rw [List.getD_eq_getElem _ _ hj] at this
    exact ⟨this.1, this.2.1⟩
  have hcost_all : ∀ l ∈ costLimbs, CanonicalLimbs k l ∧ l.length * k < 2 ^ w := by
    intro l hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have := hcostSpec j (by omega); rw [List.getD_eq_getElem _ _ hj] at this
    exact ⟨this.1, this.2.1⟩
  have hpow8_le : (2 * I.m) ^ 8 ≤ lowerClip I.m := lowerClip_ge_pow8 I.m
  have hlo_le_up : lowerClip I.m ≤ upperClip I.m := lowerClip_le_upperClip I.m
  have hup_lt : upperClip I.m < 2 ^ w := by
    have : 1 * upperClip I.m ≤ (6 * I.m + 21) * upperClip I.m := Nat.mul_le_mul_right _ (by omega)
    omega
  have htheta_lt : freezeThreshold I.m < 2 ^ w := by
    unfold freezeThreshold
    have : 8 * upperClip I.m ≤ (6 * I.m + 21) * upperClip I.m := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpow2_le : (2 * I.m) ^ 2 ≤ (2 * I.m) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpow4_le : (2 * I.m) ^ 4 ≤ (2 * I.m) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp_lt_w : costPrecisionExp I.m < w := by
    have hlt : 2 ^ costPrecisionExp I.m < 2 ^ w := by change lowerClip I.m < 2 ^ w; omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  have hpq_lt_w : costPrecisionExp I.m + costClipExp I.m < w := by
    have hlt : 2 ^ (costPrecisionExp I.m + costClipExp I.m) < 2 ^ w := by
      change upperClip I.m < 2 ^ w; exact hup_lt
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  have htop_cost_le : Nat.size (maxTopLimb costLimbs) ≤ costScaleBits I := by
    have hspec := bestPairPrefix_spec hk hcost_all costLimbs.length le_rfl
    rw [List.take_length] at hspec
    rw [← hL_eq, ← hspec.1]; unfold pairBitLength maxTopLimb
    split
    · next h0 => rw [hspec.2.1 h0]; simp
    · omega
  have htop_cap_le : Nat.size (maxTopLimb capLimbs) ≤ bitScalingPhases I := by
    have hspec := bestPairPrefix_spec hk hcap_all capLimbs.length le_rfl
    rw [List.take_length] at hspec
    rw [← hTU_eq, ← hspec.1]; unfold pairBitLength maxTopLimb
    split
    · next h0 => rw [hspec.2.1 h0]; simp
    · omega
  have hsz_2m : Nat.size (2 * I.m - 1) ≤ 2 * I.m :=
    Nat.size_le.mpr (lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self)
  have hsz_pow8 : Nat.size ((2 * I.m) ^ 8 - 1) ≤ 16 * I.m := by
    have hle1 : (2 * I.m) ^ 8 - 1 < 2 ^ (16 * I.m) := by
      have hbase : 2 * I.m ≤ 2 ^ (2 * I.m) := Nat.le_of_lt Nat.lt_two_pow_self
      have hpow : (2 * I.m) ^ 8 ≤ (2 ^ (2 * I.m)) ^ 8 := Nat.pow_le_pow_left hbase 8
      rw [← pow_mul, show 2 * I.m * 8 = 16 * I.m by omega] at hpow
      have hpos : 0 < (2 * I.m) ^ 8 := Nat.pow_pos (by omega)
      omega
    exact Nat.size_le.mpr hle1
  have hsz_Cn : Nat.size (I.compress.n + 1) ≤ 2 * I.m + 1 :=
    Nat.size_le.mpr (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self)
  have hpow8_eq : ((2 * I.m) * (2 * I.m)) * ((2 * I.m) * (2 * I.m)) *
      (((2 * I.m) * (2 * I.m)) * ((2 * I.m) * (2 * I.m))) = (2 * I.m) ^ 8 := by ring
  have hlo_pow : lowerClip I.m = 2 ^ costPrecisionExp I.m := rfl
  have hup_pow : upperClip I.m = 2 ^ (costPrecisionExp I.m + costClipExp I.m) := rfl
  have hth_eq : freezeThreshold I.m = 8 * upperClip I.m := rfl
  have hnr_eq : narrowCostRounds I.compress =
      costScaleBits I + costPrecisionExp I.m + 1 + Nat.size (I.compress.n + 1) := rfl
  have hpow8_lt : (2 * I.m) ^ 8 < 2 ^ w := by omega
  have h2m_lt : 2 * I.m < 2 ^ w := by omega
  have hpow2_lt : (2 * I.m) * (2 * I.m) < 2 ^ w := by
    have : (2 * I.m) * (2 * I.m) = (2 * I.m) ^ 2 := by ring
    omega
  have hpow4_lt : ((2 * I.m) * (2 * I.m)) * ((2 * I.m) * (2 * I.m)) < 2 ^ w := by
    have : ((2 * I.m) * (2 * I.m)) * ((2 * I.m) * (2 * I.m)) = (2 * I.m) ^ 4 := by ring
    omega
  clear huc hpow8_le hlo_le_up hpow2_le hpow4_le
  generalize hq_eq : costClipExp I.m = q_val at hpq_lt_w hup_pow ⊢
  generalize hp_eq : costPrecisionExp I.m = p_val at hp_lt_w hpq_lt_w hlo_pow hup_pow hnr_eq ⊢
  generalize hlo_eq : lowerClip I.m = lo_val at hlo_pow ⊢
  generalize hup_eq : upperClip I.m = up_val at hup_lt hup_pow hth_eq ⊢
  generalize hth_eq' : freezeThreshold I.m = th_val at htheta_lt hth_eq ⊢
  generalize hnr_eq' : narrowCostRounds I.compress = nr_val at hnr hnr_eq ⊢
  have hclog_2m : Nat.clog 2 (2 * I.m) = q_val := hq_eq
  have hclog_pow8 : Nat.clog 2 ((2 * I.m) ^ 8) = p_val := hp_eq
  have hsh_lo : 1 <<< p_val = lo_val := by rw [Nat.shiftLeft_eq, one_mul, hlo_pow]
  have hsh_up : 1 <<< (p_val + q_val) = up_val := by rw [Nat.shiftLeft_eq, one_mul, hup_pow]
  have hlo_lt : lo_val < 2 ^ w := by rw [hlo_pow]; exact Nat.pow_lt_pow_right (by decide) hp_lt_w
  have hpq_lt_2w : p_val + q_val < 2 ^ w := lt_trans hpq_lt_w Nat.lt_two_pow_self
  sep_apply stage1MetaCap_eq I.m pCapPtrs pCapLens capPtrs capLimbs
  sep_step from (k, costPtrs, costLimbs)
  have hL_s : L = costScaleBits I := hL.trans hL_eq; subst hL_s
  sep_apply stage1MetaCost_eq I.m pCostPtrs pCostLens costPtrs costLimbs
  sep_apply (stage1MetaCap_eq I.m pCapPtrs pCapLens capPtrs capLimbs).symm
  sep_step from (k, capPtrs, capLimbs)
  have hTU_s : TU = bitScalingPhases I := hTU.trans hTU_eq; subst hTU_s
  sep_apply stage1MetaCap_eq I.m pCapPtrs pCapLens capPtrs capLimbs
  sep_step; sep_step
  subst ht2
  sep_step from (2 * I.m)
  have hq_s : q = q_val := hq.trans hclog_2m; subst hq_s
  sep_step; sep_step; sep_step
  sep_step from ((2 * I.m) ^ 8)
  have hp_s : p_1 = p_val := hp_1.trans hclog_pow8; subst hp_s
  sep_step; sep_step; sep_step
  sep_step from (I.compress.n + 1)
  sep_step
  sep_apply (stage1MetaCap_eq I.m pCapPtrs pCapLens capPtrs capLimbs).symm
  sep_apply (stage1MetaCost_eq I.m pCostPtrs pCostLens costPtrs costLimbs).symm
  unfold stage1StartMetaCost
  subst hKcap hupClip hnumRounds
  simp only [hsh_lo, hsh_up]
  sep_run
  simp only [List.replicate_succ, List.replicate_zero, List.set_cons_zero, List.set_cons_succ,
    List.cons.injEq, and_true, hszN]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, hlo_eq.symm, hup_eq.symm,
    by rw [← hth_eq, hth_eq'], by rw [← hnr_eq, hnr_eq']⟩

/-! ### 2. Layout pointer writer (`stage1WriteLayout`) -/

/-- Compute the derived layout pointers of `mkStage1Layout h n m Kcap`, write `h[10..23]`
and `pResIn` (`h[24..32]`), and return `hAfter`. -/
wram_def stage1WriteLayout (w8Idx w9Idx : ℕ)
    (h, n, m, k, n', Kcap, pCostSign, pCostLens) {
  pCompTail := h + 37 + n
  pCompHead := pCompTail + m
  pAdjCostPtrs := pCompHead + m
  pFrozen := pAdjCostPtrs + m
  pHSign := pFrozen + m
  pHMag := pHSign + m
  pResTail := pHMag + m
  pResHead := pResTail + 2 * m
  pResCSign := pResHead + 2 * m
  pResCMag := pResCSign + 2 * m
  pResCapPtrs := pResCMag + 2 * m
  pResCapLens := pResCapPtrs + 2 * m
  pCapBuf := pResCapLens + 2 * m
  mK := m * Kcap
  pFlow := pCapBuf + mK
  pResFwdBuf := pFlow + mK
  pTmp1 := pResFwdBuf + mK
  pTmp2 := pTmp1 + Kcap
  hAfter := pTmp2 + Kcap
  mem[h + 10] := pCompTail
  mem[h + 11] := pCompHead
  mem[h + 12] := pCostSign
  mem[h + 13] := pCostLens
  mem[h + 14] := pAdjCostPtrs
  mem[h + 15] := pCapBuf
  r := w8Idx(h + 16, pFlow, pResFwdBuf, pTmp1, pTmp2, pFrozen, pHSign, pHMag, h + 24)
  r := w9Idx(h + 24, n', 2 * m, k, pResTail, pResHead, pResCSign, pResCMag, pResCapPtrs, pResCapLens)
  return hAfter
}

def stage1WriteLayoutSpec (w : ℕ) : Spec (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) where
  pre := fun (h, n, m, k, n', K_cap, pCostSign, pCostLens) args =>
    ⌜args = [h, n, m, k, n', K_cap, pCostSign, pCostLens] ∧
      h + 37 + n + 18 * m + 3 * m * K_cap + 2 * K_cap < 2 ^ w⌝ *
    Assn.list (h + 10) (List.replicate 6 0) *
    Assn.list (h + 16) (List.replicate 8 0) *
    Assn.list (h + 24) (List.replicate 9 0)
  post := fun (h, n, m, k, n', K_cap, pCostSign, pCostLens) args hAfter =>
    let lay := mkStage1Layout h n m K_cap
    ⌜args = [h, n, m, k, n', K_cap, pCostSign, pCostLens] ∧
      hAfter = h + 37 + n + 18 * m + 3 * m * K_cap + 2 * K_cap⌝ *
    Assn.list (h + 10) [lay.pCompTail, lay.pCompHead, pCostSign, pCostLens,
      lay.pAdjCostPtrs, lay.pCapBuf] *
    Assn.list (h + 16) [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
      lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] *
    Assn.list (h + 24) [n', 2 * m, k, lay.pResTail, lay.pResHead,
      lay.pResCSign, lay.pResCMag, lay.pResCapPtrs, lay.pResCapLens]

theorem stage1WriteLayout_meets {w : ℕ} {p : Program} {f w8Idx w9Idx : ℕ}
    (hp : p.procs[f]? = some (stage1WriteLayout w8Idx w9Idx))
    (hw8 : Meets w p w8Idx ((stage1Write8Spec w).withCost fun _ _ => 70))
    (hw9 : Meets w p w9Idx ((stage1Write9Spec w).withCost fun _ _ => 80)) :
    Meets w p f ((stage1WriteLayoutSpec w).withCost fun _ _ => 340) := by
  sep_enter ⟨h, n, m, k, n', K_cap, pCostSign, pCostLens⟩ with hfit
  have h3mK : 3 * m * K_cap = 3 * (m * K_cap) := Nat.mul_assoc 3 m K_cap
  have h2mK : 2 * m * K_cap = 2 * (m * K_cap) := Nat.mul_assoc 2 m K_cap
  have hfit' : h + 37 + n + 18 * m + 3 * (m * K_cap) + 2 * K_cap < 2 ^ w := by omega
  iterate 19 sep_step
  iterate 6 sep_step
  sep_step from (h + 37 + n + 18 * m + m * K_cap,
    h + 37 + n + 18 * m + 2 * m * K_cap,
    h + 37 + n + 18 * m + 3 * m * K_cap,
    h + 37 + n + 18 * m + 3 * m * K_cap + K_cap,
    h + 37 + n + 3 * m, h + 37 + n + 4 * m, h + 37 + n + 5 * m, h + 24)
  sep_step from (n', 2 * m, k,
    h + 37 + n + 6 * m, h + 37 + n + 8 * m,
    h + 37 + n + 10 * m, h + 37 + n + 12 * m,
    h + 37 + n + 14 * m, h + 37 + n + 16 * m)
  sep_run
  simp only [List.replicate_succ, List.replicate_zero, List.set_cons_zero, List.set_cons_succ,
    List.cons.injEq, and_true, mkStage1Layout]
  refine ⟨by omega, by omega, trivial, trivial, by omega, by omega⟩

/-! ### 3. Phase A of startup (`stage1StartHdr`) -/

/-- Phase A of Stage 1 startup: compresses vertices, computes metadata, writes layout headers,
and returns `hAfter`. -/
wram_def stage1StartHdr (compressIdx metaIdx layoutIdx : ℕ) (pIn, h) {
  n := mem[pIn]
  m := mem[pIn + 1]
  k := mem[pIn + 2]
  pTail := mem[pIn + 3]
  pHead := mem[pIn + 4]
  pCapPtrs := mem[pIn + 5]
  pCapLens := mem[pIn + 6]
  pCostSign := mem[pIn + 7]
  pCostPtrs := mem[pIn + 8]
  pCostLens := mem[pIn + 9]
  pLabels := h + 37
  pCompTail := pLabels + n
  pCompHead := pCompTail + m
  n' := compressIdx(m, pTail, pHead, pCompTail, pCompHead, pLabels)
  Kcap := metaIdx(n', m, k, pCapPtrs, pCapLens, pCostPtrs, pCostLens, h)
  hAfter := layoutIdx(h, n, m, k, n', Kcap, pCostSign, pCostLens)
  return hAfter
}

def stage1StartHdrSpec (w : ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × List ℕ × List (List ℕ)) where
  pre := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs) args =>
    ⨆ (pIn : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ),
      ⌜args = [pIn, h] ∧ 0 < I.m ∧
        capPtrs.length = I.m ∧ capLimbs.length = I.m ∧
        costPtrs.length = I.m ∧ costLimbs.length = I.m ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (capLimbs.getD j []) ∧
          (capLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩) ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (costLimbs.getD j []) ∧
          (costLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs) ∧
        1 ≤ k ∧ 2 * k ≤ w ∧ 2 * I.m + 1 < 2 ^ k ∧
        6 * I.m + 4 < 2 ^ w ∧ I.n + 1 < 2 ^ w ∧
        (6 * I.m + 21) * upperClip I.m < 2 ^ w ∧
        narrowCostRounds I.compress < 2 ^ w ∧
        h + stage1StartSpace I k < 2 ^ w⌝ *
      stage1Input I k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
      Assn.free h (2 ^ w - h)
  post := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs) args hAfter =>
    ⨆ (pIn : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ),
      let C := I.compress
      let K_cap := bitScalingPhases I / k + 2
      let lay := mkStage1Layout h I.n I.m K_cap
      let hMid := h + 37 + I.n + 2 * I.m
      ⌜args = [pIn, h] ∧
        hAfter = h + 37 + I.n + 18 * I.m + 3 * I.m * K_cap + 2 * K_cap⌝ *
      stage1Input I k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
      Assn.list lay.pCtx (stage1CtxWords I k lay pCostSign pCostLens) *
      Assn.list lay.pResIn
        [C.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
         lay.pResCapPtrs, lay.pResCapLens] *
      Assn.list lay.pResOut (List.replicate 4 0) *
      Assn.list (h + 37) (List.ofFn I.endpointLabels.table) *
      Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (C.tail e).val) *
      Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (C.head e).val) *
      Assn.free hMid (2 ^ w - hMid)

def stage1StartHdrCost (I : Circulation) : ℕ :=
  550 * I.m + 12 * bitScalingPhases I + 12 * costScaleBits I + 850

theorem stage1StartHdr_meets {w : ℕ} {p : Program}
    {f compressIdx metaIdx layoutIdx : ℕ}
    (hp : p.procs[f]? = some (stage1StartHdr compressIdx metaIdx layoutIdx))
    (hcomp : Meets w p compressIdx ((stage1CompressSpec w).withCost fun x _ => 125 * x.1.m + 50))
    (hmeta : Meets w p metaIdx ((stage1StartMetaSpec w).withCost fun x _ => stage1StartMetaCost x.1))
    (hlay : Meets w p layoutIdx ((stage1WriteLayoutSpec w).withCost fun _ _ => 340)) :
    Meets w p f ((stage1StartHdrSpec w).withCost fun x _ => stage1StartHdrCost x.1) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, costPtrs, costLimbs⟩
    with hm_pos hcp hcl hcop hcol hcapSpec hcostSpec hk h2k h2mk h6m hn1 huc hnr hsp
  sep_apply stage1Input_split_hdr
  set K_cap := bitScalingPhases I / k + 2 with hKcap_def
  set hAfter := h + 37 + I.n + 18 * I.m + 3 * I.m * K_cap + 2 * K_cap with hhAfter_def
  have hKcap_bound : 2 * K_cap ≤ 2 * (I.m * K_cap) := by
    have h1 : K_cap ≤ I.m * K_cap := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right K_cap hm_pos
    omega
  have hAfter_le : hAfter ≤ h + stage1StartSpace I k := by
    unfold stage1StartSpace; dsimp only [hAfter, K_cap] at hKcap_bound ⊢
    have h3 : 3 * I.m * (bitScalingPhases I / k + 2) = 3 * (I.m * (bitScalingPhases I / k + 2)) :=
      Nat.mul_assoc _ _ _
    have h5 : 5 * I.m * (bitScalingPhases I / k + 2) = 5 * (I.m * (bitScalingPhases I / k + 2)) :=
      Nat.mul_assoc _ _ _
    omega
  have hmeta_hyps : (6 * I.m + 21) * upperClip I.m < 2 ^ w ∧ narrowCostRounds I.compress < 2 ^ w :=
    ⟨huc, hnr⟩
  clear huc hnr
  iterate 10 sep_step
  subst hn hm k_1 pTail_1 pHead_1 pCapPtrs_1 pCapLens_1 pCostSign_1 pCostPtrs_1 pCostLens_1
  iterate 3 sep_step
  sep_apply stage1StartHdr_free_split (n := I.n) (m := I.m) (by omega)
  sep_apply stage1InputBody_split_th
  sep_step from (I, List.replicate I.m 0, List.replicate I.m 0)
  unfold stage1InputLimbs
  have huc := hmeta_hyps.1
  have hnr := hmeta_hyps.2
  sep_step from (I, k, capPtrs, capLimbs, costPtrs, costLimbs)
  clear huc hnr hmeta_hyps
  subst hKcap
  have hfold_in :
      Assn.list pIn [I.n, I.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
      Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
      Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
      Assn.list pCapPtrs capPtrs *
      Assn.list pCapLens (capLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
      Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
      Assn.list pCostPtrs costPtrs *
      Assn.list pCostLens (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) =
      stage1Input I k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens := rfl
  sep_apply hfold_in
  sep_step from (h, I.n, I.m, k, I.compress.n, K_cap, pCostSign, pCostLens)
  sep_apply stage1Start_ctx_merge
  unfold stage1StartHdrCost stage1StartMetaCost
  subst hpCompTail hpCompHead
  have hlay_fold :
      Assn.list (h + 33) (List.replicate 4 0) *
      Assn.list (h + 37 + I.n) (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
      Assn.list (h + 37 + I.n + I.m) (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
      Assn.list h
        [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I, K_cap,
         lowerClip I.m, upperClip I.m, freezeThreshold I.m, narrowCostRounds I.compress,
         (mkStage1Layout h I.n I.m K_cap).pCompTail, (mkStage1Layout h I.n I.m K_cap).pCompHead,
         pCostSign, pCostLens, (mkStage1Layout h I.n I.m K_cap).pAdjCostPtrs,
         (mkStage1Layout h I.n I.m K_cap).pCapBuf, (mkStage1Layout h I.n I.m K_cap).pFlow,
         (mkStage1Layout h I.n I.m K_cap).pResFwdBuf, (mkStage1Layout h I.n I.m K_cap).pTmp1,
         (mkStage1Layout h I.n I.m K_cap).pTmp2, (mkStage1Layout h I.n I.m K_cap).pFrozen,
         (mkStage1Layout h I.n I.m K_cap).pHSign, (mkStage1Layout h I.n I.m K_cap).pHMag,
         (mkStage1Layout h I.n I.m K_cap).pResIn] *
      Assn.list (h + 24)
        [I.compress.n, 2 * I.m, k, (mkStage1Layout h I.n I.m K_cap).pResTail,
         (mkStage1Layout h I.n I.m K_cap).pResHead, (mkStage1Layout h I.n I.m K_cap).pResCSign,
         (mkStage1Layout h I.n I.m K_cap).pResCMag, (mkStage1Layout h I.n I.m K_cap).pResCapPtrs,
         (mkStage1Layout h I.n I.m K_cap).pResCapLens] =
      Assn.list (mkStage1Layout h I.n I.m K_cap).pResOut (List.replicate 4 0) *
      Assn.list (mkStage1Layout h I.n I.m K_cap).pCompTail (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
      Assn.list (mkStage1Layout h I.n I.m K_cap).pCompHead (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
      Assn.list (mkStage1Layout h I.n I.m K_cap).pCtx
        (stage1CtxWords I k (mkStage1Layout h I.n I.m K_cap) pCostSign pCostLens) *
      Assn.list (mkStage1Layout h I.n I.m K_cap).pResIn
        [I.compress.n, 2 * I.m, k, (mkStage1Layout h I.n I.m K_cap).pResTail,
         (mkStage1Layout h I.n I.m K_cap).pResHead, (mkStage1Layout h I.n I.m K_cap).pResCSign,
         (mkStage1Layout h I.n I.m K_cap).pResCMag, (mkStage1Layout h I.n I.m K_cap).pResCapPtrs,
         (mkStage1Layout h I.n I.m K_cap).pResCapLens] := rfl
  sep_apply hlay_fold
  sep_run

end MinCostFlow.NarrowProg.Stage1
