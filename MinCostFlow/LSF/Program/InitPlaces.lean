module

public import MinCostFlow.LSF.Program.FPhaseGlue
public import MinCostFlow.LSF.Program.DecompGlue
public import MinCostFlow.LSF.Program.OrderPhaseFrame
public import MinCostFlow.LSF.Program.WidthsProc

/-!
# The places of the initialization

The init driver puts every array at a place that it computes from a few numbers: the arguments,
the sizes `n₀, m₀` of `G₀`, the widths `K_w, K` of the tree phase, the heap pointer `H` after the
`[AN19]` call, and the block width `LB` of the stretch pass. `InitVals` collects these numbers,
and this file defines the places from them.

The memory above the handle `b` is used in this order.

1. The static blocks of the state, from `b` to `lsfEndAddr` (`Layout.lean`).
2. Three parameter words (`D`, `logCap`, `θ`) and three width words (`K_w`, `K_q`, `K`).
3. The arrays of the tree phase: the numbers `q`, the edge multiplicities, the copies, the output
   of `[AN19]`, and the tree arrays `tOrig`, `tTail`, `tHead`. The `[AN19]` call uses the memory
   from `lsstHeap` on and returns `H`.
4. From `H` on, memory is zero. The scratch arrays of the order phase, then those of the
   decomposition phase, then the work area of the forest phase.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord

@[expose] public section

/-- The numbers that the places depend on. -/
structure InitVals where
  b : ℕ
  vCap : ℕ
  eCap : ℕ
  n0 : ℕ
  m0 : ℕ
  L_in : ℕ
  L_w : ℕ
  K_w : ℕ
  K : ℕ
  H : ℕ
  LB : ℕ

namespace InitVals

variable (V : InitVals)

/-- The number of tree edges. -/
def tM : ℕ := V.n0 - 1

-- 1. the static blocks
def gPtr : ℕ := lsfDgGPtr V.b
def tPtr : ℕ := lsfTBlockPtr V.b V.vCap V.eCap
def fPtr : ℕ := lsfDgFPtr V.b V.vCap V.eCap V.tM
def fAncPtr : ℕ := lsfFAncPtr V.b V.vCap V.eCap V.n0 V.tM
def wPtr : ℕ := lsfWBlockPtr V.b V.vCap V.eCap V.n0 V.tM
def auxPtr : ℕ := lsfAuxPtr V.b V.vCap V.eCap V.n0 V.tM V.L_w
def numSt : ℕ := lsfWstrNumPtr V.b V.vCap V.eCap V.n0 V.tM
def denSt : ℕ := lsfWstrDenPtr V.b V.vCap V.eCap V.n0 V.tM V.L_w
def endA : ℕ := lsfEndAddr V.b V.vCap V.eCap V.n0 V.tM V.L_w

-- 2. parameter and width words
def paramOut : ℕ := V.endA
def widthOut : ℕ := V.endA + 3

-- 3. the tree phase
def Kq : ℕ := V.K_w + 6
def qNat : ℕ := V.endA + 6
def mult : ℕ := V.qNat + V.m0 * V.Kq
def copyTail : ℕ := V.mult + V.m0 + 5 * V.K_w + 2 * V.Kq
def copyHead : ℕ := V.copyTail + 2 * V.m0
def copyLen : ℕ := V.copyHead + 2 * V.m0
def copyWt : ℕ := V.copyLen + 2 * V.m0 * V.L_in
def copyOrig : ℕ := V.copyWt + 2 * V.m0 * V.L_in
def copySub : ℕ := V.copyOrig + 2 * V.m0
def outOrig : ℕ := V.copySub + 2 * V.m0
def outBridge : ℕ := V.outOrig + V.n0
def outHdr : ℕ := V.outBridge + 2 * V.n0
def usedBridge : ℕ := V.outHdr + 2
def tOrig : ℕ := V.usedBridge + (2 * V.m0 + V.n0)
def tTail : ℕ := V.tOrig + V.n0
def tHead : ℕ := V.tTail + V.n0
def lsstHeap : ℕ := V.tHead + V.n0

-- 4. above `H`: the order phase
def rtOut : ℕ := V.H
def sPtr : ℕ := V.rtOut + 3 * V.n0
def eu : ℕ := V.sPtr + 4 * V.n0 + 2 * V.tM
def ev : ℕ := V.eu + V.m0
def dPtr : ℕ := V.ev + V.m0
def tmpPtr : ℕ := V.dPtr + V.n0 * V.K
def arrPtr : ℕ := V.tmpPtr + V.K
def scratchPtr : ℕ := V.arrPtr + V.n0
def thBase : ℕ := V.scratchPtr + V.n0

-- the decomposition phase
def dBase : ℕ := V.thBase + 8 * V.n0
def hiCopy : ℕ := V.dBase + 12 * V.n0
def inR : ℕ := V.hiCopy + V.m0
def numS : ℕ := V.inR + 3 * V.n0 + V.tM
def idPtr : ℕ := V.numS + 2 * (V.eCap * V.L_w)

-- the forest phase
def wBase : ℕ := wsPt V.idPtr V.n0 V.tM V.m0 V.LB 18 + V.m0

-- the aux arrays
def vIdx : ℕ := auxVIdxBase V.auxPtr
def vListPtr : ℕ := auxVListBase V.auxPtr V.vCap
def auxPar : ℕ := auxT0ParentBase V.auxPtr V.vCap V.n0
def minPtr : ℕ := auxUpMinIdxBase V.auxPtr V.vCap V.n0
def thDst : ℕ := auxThParentBase V.auxPtr V.vCap V.n0
def repPtr : ℕ := auxQBufBBase V.auxPtr V.vCap V.n0

/-- The end of the memory that the driver uses. -/
def useEnd : ℕ := V.wBase + wWorkSize V.n0 (auxLogCap V.n0)

end InitVals

/-- The places of the order phase. -/
def OrderLayout.ofVals (V : InitVals) (nOrig : ℕ) : OrderLayout where
  n := V.n0
  tM := V.tM
  tTail := V.tTail
  tHead := V.tHead
  rtOut := V.rtOut
  sPtr := V.sPtr
  auxPar := V.auxPar
  logCap := auxLogCap V.n0
  m0 := V.m0
  gPtr := V.gPtr
  vIdx := V.vIdx
  eu := V.eu
  ev := V.ev
  qPtr := V.qNat
  Kq := V.Kq
  dPtr := V.dPtr
  K := V.K
  tmpPtr := V.tmpPtr
  arrPtr := V.arrPtr
  scratchPtr := V.scratchPtr
  minPtr := V.minPtr
  tPtr := V.tPtr
  vCap := V.vCap
  eCap := V.eCap
  vListPtr := V.vListPtr
  tOrigSrc := V.tOrig
  nOrig := nOrig
  thBase := V.thBase
  thDst := V.thDst

/-- The places of the decomposition phase. -/
def DecompLayout.ofVals (V : InitVals) (nOrig θ D k lenArr cnt : ℕ) : DecompLayout :=
  DecompLayout.ofOrder (OrderLayout.ofVals V nOrig) θ V.dBase D V.L_w k V.L_in lenArr V.numS
    V.idPtr V.hiCopy cnt V.repPtr V.inR V.numSt V.denSt

/-- The places of the forest phase. -/
def FLayout.ofVals (V : InitVals) (nOrig θ D k lenArr cnt : ℕ) : FLayout :=
  FLayout.ofDecomp (DecompLayout.ofVals V nOrig θ D k lenArr cnt) V.fPtr V.vListPtr V.tTail
    V.tHead V.fAncPtr V.wBase V.wPtr

namespace InitVals

variable (V : InitVals)

/-- The upper table of the rooting ends where the minimum table starts. -/
lemma minPtr_eq : V.minPtr = V.auxPar + 3 * V.n0 + V.n0 * auxLogCap V.n0 := by
  simp only [minPtr, auxPar, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase]
  omega

/-- The aux arrays in order, inside the aux block. -/
lemma aux_order :
    V.tPtr + tBlockSize V.vCap V.eCap V.tM ≤ V.vIdx ∧ V.vIdx + V.vCap = V.vListPtr ∧
    V.vListPtr + V.n0 = V.auxPar ∧ V.minPtr + V.n0 * auxLogCap V.n0 = V.thDst ∧
    V.thDst + V.n0 ≤ V.repPtr ∧ V.repPtr + V.vCap ≤ V.auxPtr + auxSize V.vCap V.n0 ∧
    V.auxPtr + auxSize V.vCap V.n0 = V.numSt ∧ V.numSt + V.eCap * V.L_w = V.denSt ∧
    V.denSt + V.eCap * V.L_w = V.endA ∧ V.wPtr + wBlockSize V.n0 = V.auxPtr ∧
    V.fPtr + dynGraphSize V.vCap (fECap V.eCap V.n0) = V.fAncPtr ∧
    V.fAncPtr + fAncSize V.vCap = V.wPtr ∧
    V.tPtr + tBlockSize V.vCap V.eCap V.tM = V.fPtr ∧ V.gPtr + dynGraphSize V.vCap V.eCap = V.tPtr ∧
    V.b + lsfHdrSize = V.gPtr := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [tPtr, vIdx, vListPtr, auxPar, minPtr, thDst, repPtr, auxPtr, numSt, denSt, endA,
    wPtr, fPtr, fAncPtr, gPtr, lsfAuxPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr,
    lsfDgGPtr, lsfWstrNumPtr, lsfWstrDenPtr, lsfEndAddr, lsfStaticSize, auxVIdxBase, auxVListBase,
    auxT0ParentBase, auxUpMinIdxBase, auxThParentBase, auxQBufBBase, auxQBufABase,
    auxIsOrigVertBase, auxOrigVertBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase,
    auxSize] <;>
  omega

/-- The scratch arrays in order. -/
lemma scratch_order :
    V.endA + 6 = V.qNat ∧ V.qNat + V.m0 * V.Kq = V.mult ∧
    V.mult + V.m0 + 5 * V.K_w + 2 * V.Kq = V.copyTail ∧
    V.copyTail + 2 * V.m0 = V.copyHead ∧ V.copyHead + 2 * V.m0 = V.copyLen ∧
    V.copyLen + 2 * V.m0 * V.L_in = V.copyWt ∧ V.copyWt + 2 * V.m0 * V.L_in = V.copyOrig ∧
    V.copyOrig + 2 * V.m0 = V.copySub ∧ V.copySub + 2 * V.m0 = V.outOrig ∧
    V.outOrig + V.n0 = V.outBridge ∧ V.outBridge + 2 * V.n0 = V.outHdr ∧
    V.outHdr + 2 = V.usedBridge ∧ V.usedBridge + (2 * V.m0 + V.n0) = V.tOrig ∧
    V.tOrig + V.n0 = V.tTail ∧ V.tTail + V.n0 = V.tHead ∧ V.tHead + V.n0 = V.lsstHeap ∧
    V.rtOut = V.H ∧ V.rtOut + 3 * V.n0 = V.sPtr ∧ V.sPtr + 4 * V.n0 + 2 * V.tM = V.eu ∧
    V.eu + V.m0 = V.ev ∧ V.ev + V.m0 = V.dPtr ∧ V.dPtr + V.n0 * V.K = V.tmpPtr ∧
    V.tmpPtr + V.K = V.arrPtr ∧ V.arrPtr + V.n0 = V.scratchPtr ∧
    V.scratchPtr + V.n0 = V.thBase ∧ V.thBase + 8 * V.n0 = V.dBase ∧
    V.dBase + 12 * V.n0 = V.hiCopy ∧ V.hiCopy + V.m0 = V.inR ∧
    V.inR + 3 * V.n0 + V.tM = V.numS ∧ V.numS + 2 * (V.eCap * V.L_w) = V.idPtr ∧
    V.idPtr ≤ wsPt V.idPtr V.n0 V.tM V.m0 V.LB 18 ∧
    wsPt V.idPtr V.n0 V.tM V.m0 V.LB 18 + V.m0 = V.wBase :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    wsPt_mono _ _ _ _ _ (Nat.zero_le 18), rfl⟩

end InitVals

end

end MinCostFlow.LSF.Program
