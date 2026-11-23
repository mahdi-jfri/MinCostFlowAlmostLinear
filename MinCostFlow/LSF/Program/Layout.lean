module

public import MinCostFlow.LSF.Lemma54With
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.Machine.WideWord.LSSTProgramBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed Memory Layout, Thresholds, and Overhead Bounds for LSF

This file fixes the deterministic Word-RAM memory layout and resource bounds for the dynamic
low-stretch forest data structure (`Lemma 5.4`, `arXiv:2309.16629v1` pages 17 and 48):

* Handle header (`24` words at `b`), `T` block (`tBlockPtr`), `F` ancestor/component block
  (`fAncPtr`), `W` CSR decomposition block (`wBlockPtr`), `wstr` numerator/denominator arrays
  (`wstrNumPtr`, `wstrDenPtr`), and auxiliary static/scratch block (`auxPtr`).
* Address-range containment lemmas proving every sub-block sits disjointly in `[b, lsfEndAddr)`.
* `defaultThreshNat` and `defaultThreshNat_isWstrThresh` establishing `IsWstrThresh` with
  explicit `K_σ = 294912 * (4 * Nat.ceil (max K_AN 1) + 5)` and `α = 5 / 4`.
* General-`h` LSST overhead factor `lsstOverheadFactorH` (`h = 1` equals `lsstOverheadFactor`),
  `lsstCost_le_linear_factor_h`, and combined LSF polylog overhead `lsfOverhead`.
* Computable `batchMemLen` matching `BatchAt` word length.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

/-! ## Header offsets and block sizes -/

def lsfOffVCap : ℕ := 0
def lsfOffECap : ℕ := 1
def lsfOffN0 : ℕ := 2
def lsfOffM0 : ℕ := 3
def lsfOffDgGPtr : ℕ := 4
def lsfOffTPtr : ℕ := 5
def lsfOffDgFPtr : ℕ := 6
def lsfOffFAncPtr : ℕ := 7
def lsfOffWPtr : ℕ := 8
def lsfOffWstrNumPtr : ℕ := 9
def lsfOffWstrDenPtr : ℕ := 10
def lsfOffLW : ℕ := 11
def lsfOffHLimb : ℕ := 12
def lsfOffPFp : ℕ := 13
def lsfOffLIn : ℕ := 14
def lsfOffThresh : ℕ := 15
def lsfOffRCount : ℕ := 16
def lsfOffNumUpd : ℕ := 17
def lsfOffAuxPtr : ℕ := 18
def lsfOffEnd : ℕ := 19
def lsfOffR0 : ℕ := 20
def lsfOffKNat : ℕ := 21
def lsfOffTM : ℕ := 22
def lsfOffRes : ℕ := 23
def lsfHdrSize : ℕ := 24

def tOffM : ℕ := 0
def tOffDgTPtr : ℕ := 1
def tOffOrigIdPtr : ℕ := 2
def tOffPiPtr : ℕ := 3
def tOffFrozenTailPtr : ℕ := 4
def tOffFrozenHeadPtr : ℕ := 5
def tOffIdxOfEdgePtr : ℕ := 6
def tOffSplitScratchPtr : ℕ := 7
def tHdrSize : ℕ := 8

def tDgTPtr (tPtr : ℕ) : ℕ := tPtr + tHdrSize
def tOrigIdBase (tPtr vCap tM : ℕ) : ℕ := tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1)
def tPiBase (tPtr vCap tM : ℕ) : ℕ := tOrigIdBase tPtr vCap tM + tM
def tFrozenTailBase (tPtr vCap tM : ℕ) : ℕ := tPiBase tPtr vCap tM + tM
def tFrozenHeadBase (tPtr vCap tM : ℕ) : ℕ := tFrozenTailBase tPtr vCap tM + tM
def tIdxOfEdgeBase (tPtr vCap tM : ℕ) : ℕ := tFrozenHeadBase tPtr vCap tM + tM
def tSplitScratchBase (tPtr vCap eCap tM : ℕ) : ℕ := tIdxOfEdgeBase tPtr vCap tM + eCap

def tBlockSize (vCap eCap tM : ℕ) : ℕ :=
  tHdrSize + dynGraphSize vCap (2 * tM + 1) + 4 * tM + eCap + (4 + 2 * tM)

def fOffRCount : ℕ := 0
def fOffIsRootPtr : ℕ := 1
def fOffRListPtr : ℕ := 2
def fOffCompIdPtr : ℕ := 3
def fOffCompRootPtr : ℕ := 4
def fOffCompSizePtr : ℕ := 5
def fAncHdrSize : ℕ := 6

def fIsRootBase (fAncPtr : ℕ) : ℕ := fAncPtr + fAncHdrSize
def fRListBase (fAncPtr vCap : ℕ) : ℕ := fIsRootBase fAncPtr + vCap
def fCompIdBase (fAncPtr vCap : ℕ) : ℕ := fRListBase fAncPtr vCap + vCap
def fCompRootBase (fAncPtr vCap : ℕ) : ℕ := fCompIdBase fAncPtr vCap + vCap
def fCompSizeBase (fAncPtr vCap : ℕ) : ℕ := fCompRootBase fAncPtr vCap + vCap

def fAncSize (vCap : ℕ) : ℕ := fAncHdrSize + 5 * vCap

def wOffNumPieces : ℕ := 0
def wOffVertOffPtr : ℕ := 1
def wOffVertsPtr : ℕ := 2
def wOffEdgeOffPtr : ℕ := 3
def wOffEdgesPtr : ℕ := 4
def wOffTotalVerts : ℕ := 5
def wOffTotalEdges : ℕ := 6
def wHdrSize : ℕ := 7

def wVertOffBase (wPtr : ℕ) : ℕ := wPtr + wHdrSize
def wVertsBase (wPtr n0 : ℕ) : ℕ := wVertOffBase wPtr + (n0 + 1)
def wEdgeOffBase (wPtr n0 : ℕ) : ℕ := wVertsBase wPtr n0 + 2 * n0
def wEdgesBase (wPtr n0 : ℕ) : ℕ := wEdgeOffBase wPtr n0 + (n0 + 1)

def wBlockSize (n0 : ℕ) : ℕ := wHdrSize + (n0 + 1) + 2 * n0 + (n0 + 1) + n0

def auxOffVIdxPtr : ℕ := 0
def auxOffVListPtr : ℕ := 1
def auxOffT0ParentPtr : ℕ := 2
def auxOffT0ParentTreeIdxPtr : ℕ := 3
def auxOffT0DepthPtr : ℕ := 4
def auxOffLogCap : ℕ := 5
def auxOffUpVPtr : ℕ := 6
def auxOffUpMinIdxPtr : ℕ := 7
def auxOffThParentPtr : ℕ := 8
def auxOffOrigVertPtr : ℕ := 9
def auxOffIsOrigVertPtr : ℕ := 10
def auxOffQBufAPtr : ℕ := 11
def auxOffQBufBPtr : ℕ := 12
def auxOffVisAPtr : ℕ := 13
def auxOffVisBPtr : ℕ := 14
def auxOffThStackPtr : ℕ := 15
def auxOffFSplitScratchPtr : ℕ := 16
def auxOffR0Idx : ℕ := 17
def auxOffRes1 : ℕ := 18
def auxOffRes2 : ℕ := 19
def auxHdrSize : ℕ := 20

def auxLogCap (n0 : ℕ) : ℕ := Nat.log 2 (n0 + 1) + 1

def auxVIdxBase (auxPtr : ℕ) : ℕ := auxPtr + auxHdrSize
def auxVListBase (auxPtr vCap : ℕ) : ℕ := auxVIdxBase auxPtr + vCap
def auxT0ParentBase (auxPtr vCap n0 : ℕ) : ℕ := auxVListBase auxPtr vCap + n0
def auxT0ParentTreeIdxBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxT0ParentBase auxPtr vCap n0 + n0
def auxT0DepthBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxT0ParentTreeIdxBase auxPtr vCap n0 + n0
def auxUpVBase (auxPtr vCap n0 : ℕ) : ℕ := auxT0DepthBase auxPtr vCap n0 + n0
def auxUpMinIdxBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxUpVBase auxPtr vCap n0 + n0 * auxLogCap n0
def auxThParentBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxUpMinIdxBase auxPtr vCap n0 + n0 * auxLogCap n0
def auxOrigVertBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxThParentBase auxPtr vCap n0 + n0
def auxIsOrigVertBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxOrigVertBase auxPtr vCap n0 + vCap
def auxQBufABase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxIsOrigVertBase auxPtr vCap n0 + vCap
def auxQBufBBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxQBufABase auxPtr vCap n0 + vCap
def auxVisABase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxQBufBBase auxPtr vCap n0 + vCap
def auxVisBBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxVisABase auxPtr vCap n0 + vCap
def auxThStackBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxVisBBase auxPtr vCap n0 + vCap
def auxFSplitScratchBase (auxPtr vCap n0 : ℕ) : ℕ :=
  auxThStackBase auxPtr vCap n0 + (hldDepthBound n0 + 2)

def auxSize (vCap n0 : ℕ) : ℕ :=
  auxHdrSize + 7 * vCap + 5 * n0 + 2 * (n0 * auxLogCap n0) +
    (hldDepthBound n0 + 2) + (4 + n0)

def lsfDgGPtr (b : ℕ) : ℕ := b + lsfHdrSize
def lsfTBlockPtr (b vCap eCap : ℕ) : ℕ := lsfDgGPtr b + dynGraphSize vCap eCap
def lsfDgFPtr (b vCap eCap tM : ℕ) : ℕ :=
  lsfTBlockPtr b vCap eCap + tBlockSize vCap eCap tM
/-- The edge capacity of the `F` graph. An edge of `T₀` is an edge of `G₀`, with ID below `eCap`,
or a bridge between two components of `G₀`, named `eCap + z` for a free slot `z < 2 m₀ + n₀` of
the collision table of the tree stage. Since `m₀ ≤ eCap`, every ID is below `3 eCap + n₀`. -/
def fECap (eCap n0 : ℕ) : ℕ := 3 * eCap + n0

def lsfFAncPtr (b vCap eCap n0 tM : ℕ) : ℕ :=
  lsfDgFPtr b vCap eCap tM + dynGraphSize vCap (fECap eCap n0)
def lsfWBlockPtr (b vCap eCap n0 tM : ℕ) : ℕ :=
  lsfFAncPtr b vCap eCap n0 tM + fAncSize vCap
/-- The aux block comes right after the `W` block, and the stretch arrays come last. So every
block that the stretch pass reads lies below the stretch arrays. The argument `L_w` is not used. -/
def lsfAuxPtr (b vCap eCap n0 tM _L_w : ℕ) : ℕ :=
  lsfWBlockPtr b vCap eCap n0 tM + wBlockSize n0
def lsfWstrNumPtr (b vCap eCap n0 tM : ℕ) : ℕ :=
  lsfWBlockPtr b vCap eCap n0 tM + wBlockSize n0 + auxSize vCap n0
def lsfWstrDenPtr (b vCap eCap n0 tM L_w : ℕ) : ℕ :=
  lsfWstrNumPtr b vCap eCap n0 tM + eCap * L_w

def lsfStaticSize (vCap eCap n0 tM L_w : ℕ) : ℕ :=
  lsfHdrSize + dynGraphSize vCap eCap + tBlockSize vCap eCap tM +
    dynGraphSize vCap (fECap eCap n0) + fAncSize vCap + wBlockSize n0 +
    2 * (eCap * L_w) + auxSize vCap n0

def lsfEndAddr (b vCap eCap n0 tM L_w : ℕ) : ℕ :=
  b + lsfStaticSize vCap eCap n0 tM L_w

lemma lsfEndAddr_eq_aux_add (b vCap eCap n0 tM L_w : ℕ) :
    lsfAuxPtr b vCap eCap n0 tM L_w + auxSize vCap n0 ≤ lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfEndAddr, lsfStaticSize, lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr,
    lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]
  omega

lemma lsfHdr_lt_end (b vCap eCap n0 tM L_w : ℕ) :
    b + lsfHdrSize ≤ lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfEndAddr, lsfStaticSize]; omega

lemma lsfDgG_sub_end (b vCap eCap n0 tM L_w : ℕ) :
    b + lsfHdrSize ≤ lsfDgGPtr b ∧
      lsfDgGPtr b + dynGraphSize vCap eCap ≤ lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfDgGPtr, lsfEndAddr, lsfStaticSize]; omega

lemma lsfTBlock_sub_end (b vCap eCap n0 tM L_w : ℕ) :
    lsfDgGPtr b + dynGraphSize vCap eCap ≤ lsfTBlockPtr b vCap eCap ∧
      lsfTBlockPtr b vCap eCap + tBlockSize vCap eCap tM ≤
        lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfDgGPtr, lsfTBlockPtr, lsfEndAddr, lsfStaticSize]; omega

lemma lsfDgF_sub_end (b vCap eCap n0 tM L_w : ℕ) :
    lsfTBlockPtr b vCap eCap + tBlockSize vCap eCap tM ≤ lsfDgFPtr b vCap eCap tM ∧
      lsfDgFPtr b vCap eCap tM + dynGraphSize vCap (fECap eCap n0) ≤
        lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfTBlockPtr, lsfDgFPtr, lsfDgGPtr, lsfEndAddr, lsfStaticSize]; omega

lemma lsfFAnc_sub_end (b vCap eCap n0 tM L_w : ℕ) :
    lsfDgFPtr b vCap eCap tM + dynGraphSize vCap (fECap eCap n0) ≤ lsfFAncPtr b vCap eCap n0 tM ∧
      lsfFAncPtr b vCap eCap n0 tM + fAncSize vCap ≤ lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr, lsfEndAddr, lsfStaticSize]
  omega

lemma lsfWBlock_sub_end (b vCap eCap n0 tM L_w : ℕ) :
    lsfFAncPtr b vCap eCap n0 tM + fAncSize vCap ≤ lsfWBlockPtr b vCap eCap n0 tM ∧
      lsfWBlockPtr b vCap eCap n0 tM + wBlockSize n0 ≤ lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr,
    lsfEndAddr, lsfStaticSize]
  omega

lemma lsfWstr_sub_end (b vCap eCap n0 tM L_w : ℕ) :
    lsfWBlockPtr b vCap eCap n0 tM + wBlockSize n0 = lsfAuxPtr b vCap eCap n0 tM L_w ∧
      lsfAuxPtr b vCap eCap n0 tM L_w + auxSize vCap n0 = lsfWstrNumPtr b vCap eCap n0 tM ∧
      lsfWstrNumPtr b vCap eCap n0 tM + eCap * L_w = lsfWstrDenPtr b vCap eCap n0 tM L_w ∧
      lsfWstrDenPtr b vCap eCap n0 tM L_w + eCap * L_w =
        lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfWstrNumPtr, lsfWstrDenPtr, lsfAuxPtr, lsfWBlockPtr, lsfFAncPtr,
    lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr, lsfEndAddr, lsfStaticSize]
  omega

lemma tBlock_end_eq (tPtr vCap eCap tM : ℕ) :
    tSplitScratchBase tPtr vCap eCap tM + (4 + 2 * tM) =
      tPtr + tBlockSize vCap eCap tM := by
  dsimp only [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase,
    tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]
  omega

lemma fAnc_end_eq (fAncPtr vCap : ℕ) :
    fCompSizeBase fAncPtr vCap + vCap = fAncPtr + fAncSize vCap := by
  dsimp only [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize]
  omega

lemma wBlock_end_eq (wPtr n0 : ℕ) :
    wEdgesBase wPtr n0 + n0 = wPtr + wBlockSize n0 := by
  dsimp only [wEdgesBase, wEdgeOffBase, wVertsBase, wVertOffBase, wBlockSize]
  omega

lemma aux_end_eq (auxPtr vCap n0 : ℕ) :
    auxFSplitScratchBase auxPtr vCap n0 + (4 + n0) = auxPtr + auxSize vCap n0 := by
  dsimp only [auxFSplitScratchBase, auxThStackBase, auxVisBBase, auxVisABase,
    auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
    auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase,
    auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]
  omega

/-! ## Elementary logarithm bounds and default clipping threshold -/

lemma real_log_add_two_bounds (n : ℕ) :
    (1 : ℝ) / 4 * ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) < Real.log ((n : ℝ) + 2) ∧
      Real.log ((n : ℝ) + 2) < ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := by
  have hexp1_gt2 : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  have hexp1_lt3 : Real.exp 1 < 3 := by
    have h16 : (5 / 6 : ℝ) ≤ Real.exp (-(1 / 6 : ℝ)) := by
      linarith only [Real.add_one_le_exp (-(1 / 6 : ℝ))]
    have hexp16 : Real.exp (1 / 6 : ℝ) ≤ 6 / 5 := by
      have hinv : Real.exp (1 / 6 : ℝ) = (Real.exp (-(1 / 6 : ℝ)))⁻¹ := by
        rw [← Real.exp_neg, neg_neg]
      rw [hinv]
      calc (Real.exp (-(1 / 6 : ℝ)))⁻¹ ≤ (5 / 6 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h16
        _ = 6 / 5 := by norm_num
    have hpow : (Real.exp (1 / 6 : ℝ)) ^ 6 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpow_le : Real.exp 1 ≤ (6 / 5 : ℝ) ^ 6 := by
      rw [← hpow]
      exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hexp16 6
    linarith only [hpow_le]
  have hlog2_lt1 : Real.log 2 < 1 := by
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) hexp1_gt2
      _ = 1 := Real.log_exp 1
  have hlog2_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
    have h4 : Real.exp 1 < (4 : ℝ) := by linarith
    have hl : (1 : ℝ) < Real.log 4 := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) h4
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      ring
    linarith
  set d := Nat.log 2 (n + 2)
  have hd_pos : 1 ≤ d := by
    dsimp only [d]
    exact Nat.log_pos (by decide) (by omega)
  have hpow_lo : (2 ^ d : ℝ) ≤ (n : ℝ) + 2 := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)
  have hpow_hi : (n : ℝ) + 2 < (2 ^ (d + 1) : ℝ) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 2)
  have hlog_lo : (d : ℝ) * Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
    have hp : 0 < (2 : ℝ) ^ d := by positivity
    have h1 := Real.log_le_log hp hpow_lo
    rwa [Real.log_pow] at h1
  have hlog_hi : Real.log ((n : ℝ) + 2) < ((d + 1 : ℕ) : ℝ) * Real.log 2 := by
    have hp : 0 < (n : ℝ) + 2 := by positivity
    have h1 := Real.log_lt_log hp hpow_hi
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using h1
  constructor
  · rcases eq_or_lt_of_le hd_pos with hd1 | hd2
    · have hd1' : ((d + 1 : ℕ) : ℝ) = 2 := by rw [← hd1]; norm_num
      have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ n by positivity]
      have hlog_n : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
        Real.log_le_log (by norm_num) hn_ge2
      linarith
    · have hd2_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
      have h1 : ((d + 1 : ℕ) : ℝ) ≤ 2 * (d : ℝ) := by push_cast; linarith
      have h2 : (1 : ℝ) / 4 * (2 * (d : ℝ)) < (d : ℝ) * Real.log 2 := by nlinarith
      linarith
  · have hpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hmul : ((d + 1 : ℕ) : ℝ) * Real.log 2 < ((d + 1 : ℕ) : ℝ) * 1 :=
      mul_lt_mul_of_pos_left hlog2_lt1 hpos
    linarith

lemma logLog_add_weightFactor_nonneg (n W : ℕ) (hW : 2 ≤ W) :
    0 ≤ Cited.logLogFactor n + Cited.weightFactor n W := by
  have hb := real_log_add_two_bounds n
  have hd_ge1 : (2 : ℝ) ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := by
    have : 1 ≤ Nat.log 2 (n + 2) := Nat.log_pos (by decide) (by omega)
    exact_mod_cast (by omega : 2 ≤ Nat.log 2 (n + 2) + 1)
  have hlog_n_pos : (1 : ℝ) / 2 < Real.log ((n : ℝ) + 2) := by
    nlinarith [hb.1, hd_ge1]
  have hlog2_lt1 : Real.log 2 < 1 := by
    have hexp1 : (2 : ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0); linarith
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) hexp1
      _ = 1 := Real.log_exp 1
  have hll_ge : -Real.log 2 < Real.log (Real.log ((n : ℝ) + 2)) := by
    have hinv : Real.log (1 / 2 : ℝ) < Real.log (Real.log ((n : ℝ) + 2)) :=
      Real.log_lt_log (by norm_num) hlog_n_pos
    simpa [Real.log_div, Real.log_one] using hinv
  have hW4 : (4 : ℝ) ≤ (W : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ W + 2)
  have hlog4_gt1 : (1 : ℝ) < Real.log 4 := by
    have h4_eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
    have h0 := (real_log_add_two_bounds 0).1
    have hlog1 : Nat.log 2 (0 + 2) = 1 := by decide
    rw [hlog1] at h0
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by norm_num at h0; exact h0
    linarith
  have hlogW : (1 : ℝ) < Real.log ((W : ℝ) + 2) :=
    lt_of_lt_of_le hlog4_gt1 (Real.log_le_log (by norm_num) hW4)
  have hexp_lt3 : Real.exp 1 < 3 := by
    have h16 : (5 / 6 : ℝ) ≤ Real.exp (-(1 / 6 : ℝ)) := by
      linarith only [Real.add_one_le_exp (-(1 / 6 : ℝ))]
    have hexp16 : Real.exp (1 / 6 : ℝ) ≤ 6 / 5 := by
      rw [show (1 / 6 : ℝ) = -(-(1 / 6 : ℝ)) by ring, Real.exp_neg]
      calc (Real.exp (-(1 / 6 : ℝ)))⁻¹ ≤ (5 / 6 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h16
        _ = 6 / 5 := by norm_num
    have hpow : (Real.exp (1 / 6 : ℝ)) ^ 6 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hexp16 6
    linarith [hpow]
  have hllW : (1 : ℝ) < Real.log (Real.log ((W : ℝ) + 2) + 2) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (Real.log ((W : ℝ) + 2) + 2) :=
        Real.log_lt_log (Real.exp_pos 1) (by linarith)
  dsimp only [Cited.logLogFactor, Cited.weightFactor]
  have hsum_pos : 0 < Real.log (Real.log ((n : ℝ) + 2)) + Real.log (Real.log ((W : ℝ) + 2) + 2) := by
    linarith
  have hmul : 0 < Real.log ((n : ℝ) + 2) *
      (Real.log (Real.log ((n : ℝ) + 2)) + Real.log (Real.log ((W : ℝ) + 2) + 2)) :=
    mul_pos (by linarith) hsum_pos
  linarith

noncomputable def defaultC_ceil (K_AN : ℝ) : ℕ := 4 * Nat.ceil (max K_AN 1) + 5
noncomputable def defaultK_sigma (K_AN : ℝ) : ℕ := 294912 * defaultC_ceil K_AN

noncomputable def defaultThreshNat (K_AN : ℝ) (n k_nat : ℕ) : ℕ :=
  max 1 (9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN *
    (Nat.log 2 (n + 2) + 1) ^ 2 * k_nat)

lemma defaultC_ceil_ge (K_AN : ℝ) :
    max 1 (4 * max K_AN 1 + 5) ≤ (defaultC_ceil K_AN : ℝ) ∧ 1 ≤ defaultC_ceil K_AN := by
  have h1 : max K_AN 1 ≤ (Nat.ceil (max K_AN 1) : ℝ) := Nat.le_ceil _
  constructor
  · apply max_le
    · exact_mod_cast (by dsimp [defaultC_ceil]; omega : 1 ≤ defaultC_ceil K_AN)
    · dsimp [defaultC_ceil]; push_cast; linarith
  · dsimp [defaultC_ceil]; omega

lemma defaultK_sigma_eq_K0 (K_AN : ℝ) :
    max (defaultK_sigma K_AN : ℝ)
        (max (112 * (1 + 5 / 4 : ℝ) * max 1 (4 * max K_AN 1 + 5)) 2240) =
      (defaultK_sigma K_AN : ℝ) := by
  obtain ⟨hc1, _⟩ := defaultC_ceil_ge K_AN
  have hc_ge9 : (9 : ℝ) ≤ (defaultC_ceil K_AN : ℝ) := by
    dsimp [defaultC_ceil]; push_cast
    have : 1 ≤ Nat.ceil (max K_AN 1) := Nat.one_le_ceil_iff.mpr (by positivity)
    have : (1 : ℝ) ≤ (Nat.ceil (max K_AN 1) : ℝ) := by exact_mod_cast this
    linarith
  have h1 : 112 * (1 + 5 / 4 : ℝ) * max 1 (4 * max K_AN 1 + 5) ≤ (defaultK_sigma K_AN : ℝ) := by
    have h252 : (252 : ℝ) * max 1 (4 * max K_AN 1 + 5) ≤ 294912 * (defaultC_ceil K_AN : ℝ) := by
      nlinarith
    dsimp [defaultK_sigma]; push_cast; linarith
  have h2 : (2240 : ℝ) ≤ (defaultK_sigma K_AN : ℝ) := by
    dsimp [defaultK_sigma]; push_cast; nlinarith
  exact max_eq_left (max_le h1 h2)

lemma defaultThreshNat_isWstrThresh {K_AN : ℝ} {n k_nat : ℕ} {k : ℝ}
    (hk1 : 1 ≤ k) (hk_le : k ≤ (k_nat : ℝ)) (hk_ceil : (k_nat : ℝ) ≤ 2 * k) :
    IsWstrThresh (4 * max K_AN 1 + 5) (5 / 4) n k
      (defaultThreshNat K_AN n k_nat : ℝ) (defaultK_sigma K_AN : ℝ) := by
  obtain ⟨hc_le, hc_pos⟩ := defaultC_ceil_ge K_AN
  have hk_nat_pos : 1 ≤ k_nat := by
    have : (1 : ℝ) ≤ (k_nat : ℝ) := hk1.trans hk_le
    exact_mod_cast this
  obtain ⟨hlog_lo, hlog_hi⟩ := real_log_add_two_bounds n
  have hlog_pos : 0 < Real.log ((n : ℝ) + 2) := by
    have : (0 : ℝ) < (1 : ℝ) / 4 * ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := by positivity
    linarith
  set d := Nat.log 2 (n + 2)
  have hd_pos : 1 ≤ d := Nat.log_pos (by decide) (by omega)
  have hD_le : hldDepthBound n + 1 ≤ 2 * (d + 1) ^ 2 := by
    have hlogn : Nat.log 2 n ≤ d := Nat.log_mono_right (by omega)
    dsimp only [hldDepthBound]
    nlinarith
  have hD_sq_le : ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * ((d + 1 : ℕ) : ℝ) ^ 4 := by
    have hR : ((hldDepthBound n + 1 : ℕ) : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hD_le
    have hp : 0 ≤ ((hldDepthBound n + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  refine ⟨by exact_mod_cast Nat.le_max_left _ _, ?_, ?_⟩
  · have hnine : 4 * (1 + (5 / 4 : ℝ)) = 9 := by norm_num
    have hlog_sq : (Real.log ((n : ℝ) + 2)) ^ 2 ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ hlog_pos.le hlog_hi.le 2
    have hprod :
        9 * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 * max 1 (4 * max K_AN 1 + 5) *
            (Real.log ((n : ℝ) + 2)) ^ 2 * k ≤
          ((9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat : ℕ) : ℝ) := by
      have h1 : max 1 (4 * max K_AN 1 + 5) * (Real.log ((n : ℝ) + 2)) ^ 2 * k ≤
          (defaultC_ceil K_AN : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 * (k_nat : ℝ) := by
        refine mul_le_mul (mul_le_mul hc_le hlog_sq (by positivity) (by positivity))
          hk_le (by positivity) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1
        (show 0 ≤ 9 * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 by positivity)
      push_cast at h2 ⊢
      linarith
    have hmax : (9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat : ℕ) ≤
        defaultThreshNat K_AN n k_nat := Nat.le_max_right _ _
    have hmaxR : ((9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN *
        (d + 1) ^ 2 * k_nat : ℕ) : ℝ) ≤ (defaultThreshNat K_AN n k_nat : ℝ) := by
      exact_mod_cast hmax
    rw [hnine]
    exact hprod.trans hmaxR
  · have hpos2 : 1 ≤ 9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat := by
      have h1 : 1 ≤ (hldDepthBound n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) h1) hc_pos) h2) hk_nat_pos
    have hdef : defaultThreshNat K_AN n k_nat =
        9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat :=
      Nat.max_eq_right hpos2
    have hdp_pow : ((d + 1 : ℕ) : ℝ) ^ 6 ≤ 4096 * (Real.log ((n : ℝ) + 2)) ^ 6 := by
      have h1 : ((d + 1 : ℕ) : ℝ) ≤ 4 * Real.log ((n : ℝ) + 2) := by linarith
      have hp : 0 ≤ ((d + 1 : ℕ) : ℝ) := by positivity
      calc ((d + 1 : ℕ) : ℝ) ^ 6 ≤ (4 * Real.log ((n : ℝ) + 2)) ^ 6 :=
            pow_le_pow_left₀ hp h1 6
        _ = 4096 * (Real.log ((n : ℝ) + 2)) ^ 6 := by ring
    have hc_nn : (0 : ℝ) ≤ (defaultC_ceil K_AN : ℝ) := by positivity
    rw [hdef]
    have hcast :
        ((9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat : ℕ) : ℝ) =
          9 * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 * (defaultC_ceil K_AN : ℝ) *
            ((d + 1 : ℕ) : ℝ) ^ 2 * (k_nat : ℝ) := by
      push_cast; ring
    have ha : 9 * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * (4 * ((d + 1 : ℕ) : ℝ) ^ 4) := by
      linarith
    have hb : 9 * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 * (defaultC_ceil K_AN : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 2 * (k_nat : ℝ) ≤
        9 * (4 * ((d + 1 : ℕ) : ℝ) ^ 4) * (defaultC_ceil K_AN : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 2 * (2 * k) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hc_nn)
        (by positivity)) hk_ceil (by positivity) (by positivity)
    rw [hcast]
    calc 9 * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 * (defaultC_ceil K_AN : ℝ) *
          ((d + 1 : ℕ) : ℝ) ^ 2 * (k_nat : ℝ)
        ≤ 9 * (4 * ((d + 1 : ℕ) : ℝ) ^ 4) * (defaultC_ceil K_AN : ℝ) *
            ((d + 1 : ℕ) : ℝ) ^ 2 * (2 * k) := hb
      _ = 72 * (defaultC_ceil K_AN : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 6 * k := by ring
      _ ≤ 72 * (defaultC_ceil K_AN : ℝ) * (4096 * (Real.log ((n : ℝ) + 2)) ^ 6) * k := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hdp_pow (by positivity)
      _ = (defaultK_sigma K_AN : ℝ) * k * (Real.log ((n : ℝ) + 2)) ^ 6 := by
          dsimp only [defaultK_sigma]; push_cast; ring

/-! ## General-`h` LSST overhead factor and linear cost bound -/

/-- Overhead factor of `lsstModule Q_AN _ h` for general limb bit-width `h ≥ 1`. When `h = 1`,
this equals `WideWord.lsstOverheadFactor`. -/
noncomputable def lsstOverheadFactorH (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (n m L h : ℕ) : ℝ :=
  let L_sim := WideWord.lsstLSimMin c_AN n m L h
  let W' := WideWord.w'Max c_AN n m L h
  (L_sim : ℝ) ^ 2 +
    (WideWord.simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) *
      (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) + 1)

lemma lsstOverheadFactorH_one_eq (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (n m L : ℕ) :
    lsstOverheadFactorH Q_AN c_AN K_AN n m L 1 =
      WideWord.lsstOverheadFactor Q_AN c_AN K_AN n m L := by
  simp [lsstOverheadFactorH, WideWord.lsstOverheadFactor]

lemma lsstOverheadFactorH_ge_one (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (n m L h : ℕ) (hh : 1 ≤ h) :
    1 ≤ lsstOverheadFactorH Q_AN c_AN K_AN n m L h := by
  dsimp only [lsstOverheadFactorH]
  set L_sim := WideWord.lsstLSimMin c_AN n m L h
  have h1L : 1 ≤ L_sim := by
    dsimp only [L_sim, WideWord.lsstLSimMin, WideWord.kWidthOf]
    exact le_trans (by omega) (le_max_left _ _)
  have hsq : (1 : ℝ) ≤ (L_sim : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (L_sim : ℝ) := by exact_mod_cast h1L
    nlinarith
  have hpow2 : 2 ≤ 2 ^ (L_sim * h) := by
    have : 1 ≤ L_sim * h := Nat.mul_pos h1L hh
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (L_sim * h) := Nat.pow_le_pow_right (by decide) this
  have hwf_nn : 0 ≤ Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)) :=
    logLog_add_weightFactor_nonneg n _ hpow2
  have hK1 : 0 ≤ max K_AN 1 := le_trans (by norm_num) (le_max_right K_AN 1)
  have hterm : 0 ≤ (WideWord.simScale Q_AN : ℝ) * (L_sim : ℝ) * (WideWord.w'Max c_AN n m L h : ℝ) *
      (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) + 1) := by
    refine mul_nonneg (by positivity) ?_
    linarith [mul_nonneg hK1 hwf_nn]
  linarith

private lemma lsst_base_nat_le (m n L K L_sim : ℕ)
    (h1K : 1 ≤ K) (hLK : L ≤ K) (hK : K ≤ L_sim) :
    WideWord.scanNonloopsCost m + WideWord.starPairsCost n + WideWord.buildCSRCost n m +
      WideWord.buildVertIdxCost n + WideWord.bfsBridgesCost n m +
      ((m + 1) * (WideWord.weightStepCost K + 140 * K + 600) + m * (42 * L + 200) + 300) +
      (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
      ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
        WideWord.decodeOutCost (2 * m - 1) n L_sim + 200) + 500 ≤
      16000 * ((m + n + 1) * (L_sim * L_sim)) := by
  set M := m + n + 1
  set L2 := L_sim * L_sim
  set Z := M * L2
  have h1L : 1 ≤ L_sim := le_trans h1K hK
  have h1L2 : 1 ≤ L2 := Nat.mul_pos h1L h1L
  have hL_L2 : L_sim ≤ L2 := Nat.le_mul_of_pos_right L_sim h1L
  have hK_L2 : K ≤ L2 := le_trans hK hL_L2
  have hK2_L2 : K * K ≤ L2 := Nat.mul_le_mul hK hK
  have hL0_L2 : L ≤ L2 := le_trans (le_trans hLK hK) hL_L2
  have h1M : 1 ≤ M := by omega
  have h1Z : 1 ≤ Z := Nat.mul_pos h1M h1L2
  have mulML {a b c d : ℕ} (ha : a ≤ c * M) (hb : b ≤ d * L2) : a * b ≤ (c * d) * Z := by
    calc a * b ≤ (c * M) * (d * L2) := Nat.mul_le_mul ha hb
      _ = (c * d) * Z := by dsimp only [Z]; ring
  have hpre :
      WideWord.scanNonloopsCost m + WideWord.starPairsCost n + WideWord.buildCSRCost n m +
        WideWord.buildVertIdxCost n + WideWord.bfsBridgesCost n m ≤ 580 * Z := by
    have hlin :
        WideWord.scanNonloopsCost m + WideWord.starPairsCost n + WideWord.buildCSRCost n m +
          WideWord.buildVertIdxCost n + WideWord.bfsBridgesCost n m ≤ 580 * M := by
      dsimp only [WideWord.scanNonloopsCost, WideWord.starPairsCost, WideWord.buildCSRCost,
        WideWord.buildVertIdxCost, WideWord.bfsBridgesCost, M]
      omega
    exact hlin.trans (by calc 580 * M = 580 * M * 1 := (Nat.mul_one _).symm
      _ ≤ 580 * M * L2 := Nat.mul_le_mul_left _ h1L2
      _ = 580 * Z := by dsimp only [Z]; ring)
  have hwt1 : (m + 1) * (WideWord.weightStepCost K + 140 * K + 600) ≤ 9540 * Z := by
    have hb : WideWord.weightStepCost K + 140 * K + 600 ≤ 9540 * L2 := by
      dsimp only [WideWord.weightStepCost]
      nlinarith [hK2_L2, hK_L2, h1L2]
    exact mulML (c := 1) (d := 9540) (by dsimp [M]; omega) hb
  have hwt2 : m * (42 * L + 200) ≤ 242 * Z :=
    mulML (c := 1) (d := 242) (by dsimp [M]; omega) (by nlinarith [hL0_L2, h1L2])
  have h4m : (4 * m) * (70 * L_sim + 110) ≤ 720 * Z :=
    mulML (c := 4) (d := 180) (by dsimp [M]; omega) (by nlinarith [hL_L2, h1L2])
  have hsim1 : (95 * L_sim + 115) * (2 + 3 * (4 * m)) ≤ 2940 * Z := by
    calc (95 * L_sim + 115) * (2 + 3 * (4 * m)) =
        (2 + 3 * (4 * m)) * (95 * L_sim + 115) := Nat.mul_comm _ _
      _ ≤ (14 * M) * (210 * L2) :=
          Nat.mul_le_mul (by dsimp [M]; omega) (by nlinarith [hL_L2, h1L2])
      _ = 2940 * Z := by dsimp [Z]; ring
  have hsim2 : (70 * L_sim + 80) * (2 * m - 1) ≤ 300 * Z := by
    calc (70 * L_sim + 80) * (2 * m - 1) = (2 * m - 1) * (70 * L_sim + 80) := Nat.mul_comm _ _
      _ ≤ (2 * M) * (150 * L2) :=
          Nat.mul_le_mul (by dsimp [M]; omega) (by nlinarith [hL_L2, h1L2])
      _ = 300 * Z := by dsimp [Z]; ring
  have hdec : WideWord.decodeOutCost (2 * m - 1) n L_sim ≤ 270 * Z := by
    have h1 : (2 * m - 1) * (25 * L_sim + 80) ≤ 210 * Z :=
      mulML (c := 2) (d := 105) (by dsimp [M]; omega) (by nlinarith [hL_L2, h1L2])
    have h2 : 45 * n + 60 ≤ 60 * Z := by
      calc 45 * n + 60 ≤ 60 * M := by dsimp [M]; omega
        _ = 60 * M * 1 := (Nat.mul_one _).symm
        _ ≤ 60 * M * L2 := Nat.mul_le_mul_left _ h1L2
        _ = 60 * Z := by dsimp [Z]; ring
    dsimp only [WideWord.decodeOutCost]; omega
  have hm110 : 110 * m ≤ 110 * Z := by
    calc 110 * m ≤ 110 * M := by dsimp [M]; omega
      _ ≤ 110 * M * L2 := Nat.le_mul_of_pos_right _ h1L2
      _ = 110 * Z := by dsimp [Z]; ring
  have h50L : 50 * L_sim ≤ 50 * Z := by
    calc 50 * L_sim ≤ 50 * L2 := by nlinarith [hL_L2]
      _ ≤ M * (50 * L2) := Nat.le_mul_of_pos_left _ h1M
      _ = 50 * Z := by dsimp [Z]; ring
  have hc1120 : 300 + 120 + 200 + 500 ≤ 1120 * Z :=
    Nat.le_mul_of_pos_right 1120 h1Z
  have hsum :
      WideWord.scanNonloopsCost m + WideWord.starPairsCost n + WideWord.buildCSRCost n m +
        WideWord.buildVertIdxCost n + WideWord.bfsBridgesCost n m +
        ((m + 1) * (WideWord.weightStepCost K + 140 * K + 600) + m * (42 * L + 200) + 300) +
        (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
        ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
          WideWord.decodeOutCost (2 * m - 1) n L_sim + 200) + 500 ≤
        (580 + 9540 + 242 + 720 + 2940 + 300 + 270 + 110 + 50 + 1120) * Z := by
    linarith only [hpre, hwt1, hwt2, h4m, hsim1, hsim2, hdec, hm110, h50L, hc1120]
  exact hsum.trans (Nat.mul_le_mul_right _ (by decide))

theorem lsstCost_le_linear_factor_h (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    {n m L h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) :
    (WideWord.lsstCost Q_AN K_AN c_AN n m L (WideWord.lsstLSimMin c_AN n m L h) h : ℝ) ≤
      16000 * ((m + n + 1 : ℕ) : ℝ) * lsstOverheadFactorH Q_AN c_AN K_AN n m L h := by
  set L_sim := WideWord.lsstLSimMin c_AN n m L h
  set W' := WideWord.w'Max c_AN n m L h
  set C_an := WideWord.anCostBound K_AN n m L_sim h
  set M := m + n + 1
  have hK_le : WideWord.kWidthOf m L ≤ L_sim := le_max_left _ _
  have h1K : 1 ≤ WideWord.kWidthOf m L := by dsimp only [WideWord.kWidthOf]; omega
  have hLK : L ≤ WideWord.kWidthOf m L := by dsimp only [WideWord.kWidthOf]; omega
  have hbase_nat := lsst_base_nat_le m n L (WideWord.kWidthOf m L) L_sim h1K hLK hK_le
  have hbase_real :
      ((WideWord.scanNonloopsCost m + WideWord.starPairsCost n + WideWord.buildCSRCost n m +
        WideWord.buildVertIdxCost n + WideWord.bfsBridgesCost n m + WideWord.weightsCost m L +
        (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
        ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
          WideWord.decodeOutCost (2 * m - 1) n L_sim + 200) + 500 : ℕ) : ℝ) ≤
        16000 * (M : ℝ) * (L_sim : ℝ) ^ 2 := by
    have hnat' :
        WideWord.scanNonloopsCost m + WideWord.starPairsCost n + WideWord.buildCSRCost n m +
          WideWord.buildVertIdxCost n + WideWord.bfsBridgesCost n m + WideWord.weightsCost m L +
          (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
          ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
            WideWord.decodeOutCost (2 * m - 1) n L_sim + 200) + 500 ≤
          16000 * ((m + n + 1) * (L_sim * L_sim)) := by
      simpa only [WideWord.weightsCost] using hbase_nat
    have hreal := (Nat.cast_le (α := ℝ)).mpr hnat'
    push_cast [sq] at hreal ⊢
    have hassoc :
        (16000 : ℝ) * ((↑m + ↑n + 1) * (↑L_sim * ↑L_sim)) =
          16000 * (M : ℝ) * (↑L_sim * ↑L_sim) := by
      dsimp only [M]; push_cast; ring
    linarith only [hreal, hassoc]
  have h1L : 1 ≤ L_sim := le_trans h1K hK_le
  have hpow2 : 2 ≤ 2 ^ (L_sim * h) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (L_sim * h) := Nat.pow_le_pow_right (by decide) (Nat.mul_pos h1L hh)
  have hF_nn : 0 ≤ Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)) :=
    logLog_add_weightFactor_nonneg n _ hpow2
  have hC_an :
      (C_an : ℝ) <
        max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
          (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) + 1 := by
    dsimp only [C_an, WideWord.anCostBound]
    exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) hF_nn)
  have hCan_lin :
      ((C_an + (2 + 3 * (4 * m)) + 1 : ℕ) : ℝ) ≤
        16 * (M : ℝ) *
          (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) + 1) := by
    have hKmax : max K_AN 0 ≤ max K_AN 1 := max_le_max_left K_AN (by norm_num)
    have hm4 : ((4 * m : ℕ) + 1 : ℝ) ≤ 4 * (M : ℝ) := by
      exact_mod_cast (by dsimp [M]; omega : 4 * m + 1 ≤ 4 * M)
    have hprod :
        max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
          (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) ≤
          4 * (M : ℝ) *
            (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)))) := by
      calc max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
              (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)))
          ≤ max K_AN 1 * (4 * (M : ℝ)) *
              (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hKmax hm4 (by positivity) (le_trans (by norm_num) (le_max_right K_AN 1)))
              hF_nn
        _ = 4 * (M : ℝ) *
              (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)))) := by
            ring
    have hm16 : 12 * (m : ℝ) + 4 ≤ 16 * (M : ℝ) := by
      exact_mod_cast (by dsimp [M]; omega : 12 * m + 4 ≤ 16 * M)
    have h4_le16 :
        4 * (M : ℝ) * (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)))) ≤
          16 * (M : ℝ) * (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)))) := by
      have h1 : 0 ≤ (M : ℝ) := by positivity
      have h2 : 0 ≤ max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) :=
        mul_nonneg (le_trans (by norm_num) (le_max_right K_AN 1)) hF_nn
      nlinarith
    have hm_cast : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
    have hC_an' : (C_an : ℝ) < max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
        (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) + 1 := hC_an
    have hsum_cast : ((C_an + (2 + 3 * (4 * m)) + 1 : ℕ) : ℝ) =
        (C_an : ℝ) + (2 + 3 * (4 * (m : ℝ))) + 1 := by
      push_cast; ring
    rw [hsum_cast]
    linarith
  have hsim_term :
      ((WideWord.simScale Q_AN * L_sim * W' * (C_an + (2 + 3 * (4 * m)) + 1) : ℕ) : ℝ) ≤
        16000 * (M : ℝ) *
          ((WideWord.simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) *
            (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) + 1)) := by
    have hq_nn : (0 : ℝ) ≤ (WideWord.simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hCan_lin hq_nn
    push_cast at h1 ⊢
    nlinarith
  have hsplit :
      (WideWord.lsstCost Q_AN K_AN c_AN n m L L_sim h : ℝ) =
        ((WideWord.scanNonloopsCost m + WideWord.starPairsCost n + WideWord.buildCSRCost n m +
          WideWord.buildVertIdxCost n + WideWord.bfsBridgesCost n m + WideWord.weightsCost m L +
          (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
          ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
            WideWord.decodeOutCost (2 * m - 1) n L_sim + 200) + 500 : ℕ) : ℝ) +
          ((WideWord.simScale Q_AN * L_sim * W' * (C_an + (2 + 3 * (4 * m)) + 1) : ℕ) : ℝ) := by
    dsimp only [WideWord.lsstCost, WideWord.simDecodeCost, C_an, L_sim, W']
    push_cast; ring
  dsimp only [lsstOverheadFactorH]
  rw [hsplit]
  linarith

/-- Combined LSF polylogarithmic overhead factor `F`: dominates `lsstOverheadFactorH`,
`(Nat.log 2 (n₀ + 2) + 1)^4`, and `L_w^2`. -/
noncomputable def lsfOverhead (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (n0 m0 L_in L_w h : ℕ) : ℝ :=
  lsstOverheadFactorH Q_AN c_AN K_AN n0 (2 * m0) L_in h +
    ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 4 +
    (L_w : ℝ) ^ 2 + 1

lemma lsfOverhead_ge_one (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (n0 m0 L_in L_w h : ℕ) (hh : 1 ≤ h) :
    1 ≤ lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h := by
  dsimp only [lsfOverhead]
  have h1 := lsstOverheadFactorH_ge_one Q_AN c_AN K_AN n0 (2 * m0) L_in h hh
  have h2 : (0 : ℝ) ≤ ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 4 + (L_w : ℝ) ^ 2 := by positivity
  linarith

lemma lsstOverheadFactor_le_lsfOverhead {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {n0 m0 L_in L_w h : ℕ} (hh : 1 ≤ h) :
    WideWord.lsstOverheadFactor Q_AN c_AN K_AN n0 (2 * m0) L_in ≤
      lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h := by
  rw [← lsstOverheadFactorH_one_eq]
  set L_sim1 := WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in 1
  set L_simh := WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h
  have hL_le : L_sim1 ≤ L_simh := by
    dsimp only [L_sim1, L_simh, WideWord.lsstLSimMin, WideWord.w'Max]
    exact max_le_max_left _ (Nat.mul_le_mul_left _ (by
      have : WideWord.kWidthOf (2 * m0) L_in * 1 ≤ WideWord.kWidthOf (2 * m0) L_in * h :=
        Nat.mul_le_mul_left _ hh
      omega))
  have hW'_le : WideWord.w'Max c_AN n0 (2 * m0) L_in 1 ≤
      WideWord.w'Max c_AN n0 (2 * m0) L_in h := by
    dsimp only [WideWord.w'Max]
    exact Nat.mul_le_mul_left _ (by
      have := Nat.mul_le_mul_left (WideWord.kWidthOf (2 * m0) L_in) hh
      omega)
  have hLh_le : L_sim1 * 1 ≤ L_simh * h := Nat.mul_le_mul hL_le hh
  have hpow_le : (2 ^ (L_sim1 * 1) : ℕ) ≤ 2 ^ (L_simh * h) :=
    Nat.pow_le_pow_right (by decide) hLh_le
  have h1L1 : 1 ≤ L_sim1 := by
    dsimp only [L_sim1, WideWord.lsstLSimMin, WideWord.kWidthOf]
    exact le_trans (by omega) (le_max_left _ _)
  have hpow2 : 2 ≤ 2 ^ (L_sim1 * 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (L_sim1 * 1) := Nat.pow_le_pow_right (by decide) (Nat.mul_pos h1L1 (by decide))
  have hwf1_nn := logLog_add_weightFactor_nonneg n0 _ hpow2
  have hwf_mono :
      Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_sim1 * 1)) ≤
        Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_simh * h)) := by
    refine add_le_add le_rfl ?_
    dsimp only [Cited.weightFactor]
    have hlog_n_nn : 0 ≤ Real.log ((n0 : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ n0 by positivity])
    have hpow_r1 : (2 : ℝ) ≤ ((2 ^ (L_sim1 * 1) : ℕ) : ℝ) := by exact_mod_cast hpow2
    have hpow_rh : ((2 ^ (L_sim1 * 1) : ℕ) : ℝ) ≤ ((2 ^ (L_simh * h) : ℕ) : ℝ) := by
      exact_mod_cast hpow_le
    have h1 : (0 : ℝ) < Real.log (((2 ^ (L_sim1 * 1) : ℕ) : ℝ) + 2) + 2 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ ((2 ^ (L_sim1 * 1) : ℕ) : ℝ) + 2)
      linarith
    have hlog_w : Real.log (((2 ^ (L_sim1 * 1) : ℕ) : ℝ) + 2) ≤
        Real.log (((2 ^ (L_simh * h) : ℕ) : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log h1 (by linarith)) hlog_n_nn
  have hlsst_le : lsstOverheadFactorH Q_AN c_AN K_AN n0 (2 * m0) L_in 1 ≤
      lsstOverheadFactorH Q_AN c_AN K_AN n0 (2 * m0) L_in h := by
    dsimp only [lsstOverheadFactorH]
    change (L_sim1 : ℝ) ^ 2 + (WideWord.simScale Q_AN : ℝ) * (L_sim1 : ℝ) * _ * _ ≤
      (L_simh : ℝ) ^ 2 + (WideWord.simScale Q_AN : ℝ) * (L_simh : ℝ) * _ * _
    have hsq : (L_sim1 : ℝ) ^ 2 ≤ (L_simh : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL_le) 2
    have hq1 : (WideWord.simScale Q_AN : ℝ) * (L_sim1 : ℝ) *
        (WideWord.w'Max c_AN n0 (2 * m0) L_in 1 : ℝ) ≤
        (WideWord.simScale Q_AN : ℝ) * (L_simh : ℝ) *
        (WideWord.w'Max c_AN n0 (2 * m0) L_in h : ℝ) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hL_le) (by positivity))
        (by exact_mod_cast hW'_le) (by positivity) (by positivity)
    have hK_nn : 0 ≤ max K_AN 1 := le_trans (by norm_num) (le_max_right K_AN 1)
    have hr1 : 0 ≤ max K_AN 1 * (Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_sim1 * 1))) + 1 := by
      linarith [mul_nonneg hK_nn hwf1_nn]
    have hr_le : max K_AN 1 * (Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_sim1 * 1))) + 1 ≤
        max K_AN 1 * (Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_simh * h))) + 1 := by
      linarith [mul_le_mul_of_nonneg_left hwf_mono hK_nn]
    have hmul := mul_le_mul hq1 hr_le hr1 (by positivity)
    linarith
  dsimp only [lsfOverhead]
  linarith [show (0 : ℝ) ≤ ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 4 + (L_w : ℝ) ^ 2 + 1 by positivity]

lemma lsfOverhead_bounds (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (n0 m0 L_in L_w h : ℕ) (hh : 1 ≤ h) :
    lsstOverheadFactorH Q_AN c_AN K_AN n0 (2 * m0) L_in h ≤
      lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h ∧
    ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 4 ≤
      lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h ∧
    (L_w : ℝ) ^ 2 ≤ lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h ∧
    ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 2 * (L_w : ℝ) ≤
      lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h := by
  have hF := lsstOverheadFactorH_ge_one Q_AN c_AN K_AN n0 (2 * m0) L_in h hh
  have h4 : (0 : ℝ) ≤ ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 4 := by positivity
  have hL : (0 : ℝ) ≤ (L_w : ℝ) ^ 2 := by positivity
  dsimp only [lsfOverhead]
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have hsq : 0 ≤ (((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 2 - (L_w : ℝ)) ^ 2 := sq_nonneg _
  nlinarith

/-! ## Batch word-length scanner matching `BatchAt` -/

/-- Exact word length of `count` encoded updates starting at `ptr` in `mem`. -/
def batchBodyMemLen (mem : ℕ → ℕ) (ptr : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 =>
    let len := dgUpdateMemLen mem ptr
    len + batchBodyMemLen mem (ptr + len) count

/-- Total word length of an encoded batch starting at `batchPtr` (`1 + body`). -/
def batchMemLen (mem : ℕ → ℕ) (batchPtr : ℕ) : ℕ :=
  1 + batchBodyMemLen mem (batchPtr + 1) (mem batchPtr)

lemma dgUpdateMemLen_eq_of_updateAt {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (h : UpdateAt mem a G u len) :
    dgUpdateMemLen mem a = len := by
  cases u with
  | insert e x y =>
    rcases h with ⟨rfl, hL⟩
    have h0 : mem a = 0 := by simpa using hL 0 (by simp)
    simp only [dgUpdateMemLen, h0]; rfl
  | delete e =>
    rcases h with ⟨rfl, hL⟩
    have h0 : mem a = 1 := by simpa using hL 0 (by simp)
    simp only [dgUpdateMemLen, h0]; rfl
  | split v v' St Sh =>
    rcases h with ⟨Lt, Lh, _, _, _, _, rfl, hL⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hL⟩
    · have h0 : mem a = 2 := by simpa using hL 0 (by simp)
      have h3 : mem (a + 3) = Lt.length := by
        simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hL 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := by
        simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hL 4 (by simp)
      simp only [dgUpdateMemLen, h0, h3, h4]; rfl
    · have h0 : mem a = 3 := by simpa using hL 0 (by simp)
      have h3 : mem (a + 3) = Lt.length := by
        simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hL 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := by
        simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hL 4 (by simp)
      simp only [dgUpdateMemLen, h0, h3, h4]; rfl

lemma batchBodyMemLen_eq {mem : ℕ → ℕ} :
    ∀ {a : ℕ} {G : MGraph} {U : List Update} {tw : ℕ},
      BatchBodyAt mem a G U tw → batchBodyMemLen mem a U.length = tw
  | _, _, [], tw, h => by simp only [BatchBodyAt] at h; simp [batchBodyMemLen, h]
  | a, G, u :: us, tw, h => by
    rcases h with ⟨len, hle, hu, hrest⟩
    have hlen := dgUpdateMemLen_eq_of_updateAt hu
    have hih := batchBodyMemLen_eq hrest
    simp only [List.length_cons, batchBodyMemLen, hlen, hih]
    omega

lemma batchMemLen_eq {mem : ℕ → ℕ} {batchPtr : ℕ} {G : MGraph} {U : List Update} {tw : ℕ}
    (h : BatchAt mem batchPtr G U tw) :
    batchMemLen mem batchPtr = tw := by
  rcases h with ⟨htw, hlen, hbody⟩
  dsimp only [batchMemLen]
  rw [hlen, batchBodyMemLen_eq hbody]
  omega

end MinCostFlow.LSF.Program
