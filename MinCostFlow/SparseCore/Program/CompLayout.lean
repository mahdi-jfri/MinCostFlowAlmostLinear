module

public import MinCostFlow.SparseCore.Program.CompModel
public import MinCostFlow.SparseCore.Program.CompWindow

/-!
# Memory Layout, Concrete State, Potential, and `DSRep` for Per-Component LSF (`CompLayout`)

Fixes the contiguous Word-RAM memory layout `[b, x.endAddr)` for the per-component LSF manager
implementing `CompLSFFamily k := Fin k → CompLSFState`:

* 24-word header at `b` (`compOffVCap .. compOffRes`).
* Static arrays (all zero-initialized via `ZeroFrom`, no `vCap`/`eCap` scan at init):
  - vertex-to-component table `vComp[vCap]`,
  - component metadata `compEdgeful[vCap]`, `compEdgefulIdx[vCap]`, `compN0[vCap]`, `compM0[vCap]`,
  - edge-to-component tables `edgeComp1[eCap]`, `edgeComp2[eCap]`,
  - global flags `isCross[eCap]`, `isIns[eCap]`,
  - ghost-end doubly-linked lists (`gtHead/gtCnt/ghHead/ghCnt` of size `vCap`;
    `gtPrev/gtNext/gtVert/ghPrev/ghNext/ghVert` of size `eCap`),
  - cleared-between-calls `touchMark[vCap]`,
  - constant `L_w`-limb `1` at `oneLimb[L_w]` for inserted edges' `wstrGlobal = 1`.
* Edgeful handle table `handles[m₀ * k]` storing `LSFRep h` handles for edgeful components only.
* Disjoint per-component LSF windows `[hs, hs_end)` inside `[b, x.endAddr)`.
* `compPhi`: sum of `lsfPhi` across all edgeful `(ec, j)` windows.
* `compLSFRep`: `DSRep (CompLSFFamily k)` with `compLSFRep_local`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Abstract state family -/

/-- Family of `k` component-wise dynamic LSF states (one per branch `j : Fin k`). -/
abbrev CompLSFFamily (k : ℕ) := Fin k → CompLSFState

/-- Initial family on `(G₀, ℓ₀)` using `lsfInit`. -/
noncomputable def compLSFInitFamily (lsfInit : LSFInit) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) :
    CompLSFFamily k :=
  fun j => initCompLSFWith lsfInit G₀ ℓ₀ k j.1

/-- Apply a global update batch `U` to every branch in a `CompLSFFamily k`. -/
noncomputable def compLSFBatchFamily {k : ℕ} (S : CompLSFFamily k) (U : List Update) :
    CompLSFFamily k :=
  fun j => compLSFBatch (S j) U

/-! ## 2. Header offsets and static layout -/

def compOffVCap : ℕ := 0
def compOffECap : ℕ := 1
def compOffK : ℕ := 2
def compOffLW : ℕ := 3
def compOffHLimb : ℕ := 4
def compOffLIn : ℕ := 5
def compOffPFp : ℕ := 6
def compOffNumComps : ℕ := 7
def compOffNumEdgeful : ℕ := 8
def compOffVCompPtr : ℕ := 9
def compOffEdgefulPtr : ℕ := 10
def compOffEdgefulIdxPtr : ℕ := 11
def compOffN0Ptr : ℕ := 12
def compOffM0Ptr : ℕ := 13
def compOffEdgeC1Ptr : ℕ := 14
def compOffEdgeC2Ptr : ℕ := 15
def compOffIsCrossPtr : ℕ := 16
def compOffIsInsPtr : ℕ := 17
def compOffGhostPtr : ℕ := 18
def compOffTouchMarkPtr : ℕ := 19
def compOffOneLimbPtr : ℕ := 20
def compOffHandlesPtr : ℕ := 21
def compOffEndAddr : ℕ := 22
def compOffM0Total : ℕ := 23
def compHdrSize : ℕ := 24

/-- Static array base addresses relative to handle `b`. -/
def compVCompBase (b : ℕ) : ℕ := b + compHdrSize
def compEdgefulBase (b vCap : ℕ) : ℕ := compVCompBase b + vCap
def compEdgefulIdxBase (b vCap : ℕ) : ℕ := compEdgefulBase b vCap + vCap
def compN0Base (b vCap : ℕ) : ℕ := compEdgefulIdxBase b vCap + vCap
def compM0Base (b vCap : ℕ) : ℕ := compN0Base b vCap + vCap
def compEdgeC1Base (b vCap : ℕ) : ℕ := compM0Base b vCap + vCap
def compEdgeC2Base (b vCap eCap : ℕ) : ℕ := compEdgeC1Base b vCap + eCap
def compIsCrossBase (b vCap eCap : ℕ) : ℕ := compEdgeC2Base b vCap eCap + eCap
def compIsInsBase (b vCap eCap : ℕ) : ℕ := compIsCrossBase b vCap eCap + eCap
def compGhostBase (b vCap eCap : ℕ) : ℕ := compIsInsBase b vCap eCap + eCap

/-- Sub-block offsets inside the ghost-end region starting at `gPtr = compGhostBase b vCap eCap`
(total `4 * vCap + 6 * eCap` words). -/
def ghostTHeadBase (gPtr : ℕ) : ℕ := gPtr
def ghostTCntBase (gPtr vCap : ℕ) : ℕ := gPtr + vCap
def ghostHHeadBase (gPtr vCap : ℕ) : ℕ := gPtr + 2 * vCap
def ghostHCntBase (gPtr vCap : ℕ) : ℕ := gPtr + 3 * vCap
def ghostTPrevBase (gPtr vCap : ℕ) : ℕ := gPtr + 4 * vCap
def ghostTNextBase (gPtr vCap eCap : ℕ) : ℕ := gPtr + 4 * vCap + eCap
def ghostTVertBase (gPtr vCap eCap : ℕ) : ℕ := gPtr + 4 * vCap + 2 * eCap
def ghostHPrevBase (gPtr vCap eCap : ℕ) : ℕ := gPtr + 4 * vCap + 3 * eCap
def ghostHNextBase (gPtr vCap eCap : ℕ) : ℕ := gPtr + 4 * vCap + 4 * eCap
def ghostHVertBase (gPtr vCap eCap : ℕ) : ℕ := gPtr + 4 * vCap + 5 * eCap
def compGhostSize (vCap eCap : ℕ) : ℕ := 4 * vCap + 6 * eCap

def compTouchMarkBase (b vCap eCap : ℕ) : ℕ :=
  compGhostBase b vCap eCap + compGhostSize vCap eCap
def compOneLimbBase (b vCap eCap : ℕ) : ℕ :=
  compTouchMarkBase b vCap eCap + vCap
def compStaticSize (vCap eCap L_w : ℕ) : ℕ :=
  compHdrSize + 10 * vCap + 10 * eCap + L_w
def compHandlesBase (b vCap eCap L_w : ℕ) : ℕ :=
  b + compStaticSize vCap eCap L_w

/-- End of the static + handle-table region (`handles` has `m0Total * k` words). -/
def compTablesEnd (b vCap eCap L_w m0Total k : ℕ) : ℕ :=
  compHandlesBase b vCap eCap L_w + m0Total * k

lemma compOneLimb_end_eq (b vCap eCap L_w : ℕ) :
    compOneLimbBase b vCap eCap + L_w = compHandlesBase b vCap eCap L_w := by
  dsimp only [compOneLimbBase, compTouchMarkBase, compGhostBase, compGhostSize,
    compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
    compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase,
    compHandlesBase, compStaticSize, compHdrSize]
  omega

/-! ## 3. Concrete state, header predicate, potential, and `DSRep` -/

/-- Concrete metadata tracked alongside memory `mem` for a `CompLSF` handle `b`. -/
structure CompLSFMeta (k : ℕ) where
  vCap : ℕ
  eCap : ℕ
  L_w : ℕ
  h : ℕ
  L_in : ℕ
  P_fp : ℕ
  m0Total : ℕ
  numComps : ℕ
  numEdgeful : ℕ
  endAddr : ℕ
  compOf : Fin numComps → Finset ℕ
  edgefulIdx : Fin numComps → ℕ
  edgefulComp : Fin numEdgeful → Fin numComps
  edgeC1 : ℕ → ℕ
  edgeC2 : ℕ → ℕ
  gtVert : ℕ → ℕ
  ghVert : ℕ → ℕ
  gtList : ℕ → List ℕ
  ghList : ℕ → List ℕ
  winHandle : Fin numEdgeful → Fin k → ℕ
  winConc : Fin numEdgeful → Fin k → LSFConcrete

/-- 24-word header predicate at handle `b`. -/
def compHeaderAt {k : ℕ} (mem : ℕ → ℕ) (b : ℕ) (x : CompLSFMeta k) : Prop :=
  mem (b + compOffVCap) = x.vCap ∧
  mem (b + compOffECap) = x.eCap ∧
  mem (b + compOffK) = k ∧
  mem (b + compOffLW) = x.L_w ∧
  mem (b + compOffHLimb) = x.h ∧
  mem (b + compOffLIn) = x.L_in ∧
  mem (b + compOffPFp) = x.P_fp ∧
  mem (b + compOffNumComps) = x.numComps ∧
  mem (b + compOffNumEdgeful) = x.numEdgeful ∧
  mem (b + compOffVCompPtr) = compVCompBase b ∧
  mem (b + compOffEdgefulPtr) = compEdgefulBase b x.vCap ∧
  mem (b + compOffEdgefulIdxPtr) = compEdgefulIdxBase b x.vCap ∧
  mem (b + compOffN0Ptr) = compN0Base b x.vCap ∧
  mem (b + compOffM0Ptr) = compM0Base b x.vCap ∧
  mem (b + compOffEdgeC1Ptr) = compEdgeC1Base b x.vCap ∧
  mem (b + compOffEdgeC2Ptr) = compEdgeC2Base b x.vCap x.eCap ∧
  mem (b + compOffIsCrossPtr) = compIsCrossBase b x.vCap x.eCap ∧
  mem (b + compOffIsInsPtr) = compIsInsBase b x.vCap x.eCap ∧
  mem (b + compOffGhostPtr) = compGhostBase b x.vCap x.eCap ∧
  mem (b + compOffTouchMarkPtr) = compTouchMarkBase b x.vCap x.eCap ∧
  mem (b + compOffOneLimbPtr) = compOneLimbBase b x.vCap x.eCap ∧
  mem (b + compOffHandlesPtr) = compHandlesBase b x.vCap x.eCap x.L_w ∧
  mem (b + compOffEndAddr) = x.endAddr ∧
  mem (b + compOffM0Total) = x.m0Total

lemma compHeaderAt_of_agree {k : ℕ} {mem mem' : ℕ → ℕ} {b : ℕ} {x : CompLSFMeta k}
    (h : compHeaderAt mem b x)
    (hag : ∀ a, b ≤ a → a < b + compHdrSize → mem' a = mem a) :
    compHeaderAt mem' b x := by
  have hh : ∀ off < compHdrSize, mem' (b + off) = mem (b + off) :=
    fun off hoff => hag (b + off) (Nat.le_add_right _ _) (Nat.add_lt_add_left hoff b)
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23⟩
  refine ⟨(hh _ (by decide)).trans h0, (hh _ (by decide)).trans h1,
    (hh _ (by decide)).trans h2, (hh _ (by decide)).trans h3,
    (hh _ (by decide)).trans h4, (hh _ (by decide)).trans h5,
    (hh _ (by decide)).trans h6, (hh _ (by decide)).trans h7,
    (hh _ (by decide)).trans h8, (hh _ (by decide)).trans h9,
    (hh _ (by decide)).trans h10, (hh _ (by decide)).trans h11,
    (hh _ (by decide)).trans h12, (hh _ (by decide)).trans h13,
    (hh _ (by decide)).trans h14, (hh _ (by decide)).trans h15,
    (hh _ (by decide)).trans h16, (hh _ (by decide)).trans h17,
    (hh _ (by decide)).trans h18, (hh _ (by decide)).trans h19,
    (hh _ (by decide)).trans h20, (hh _ (by decide)).trans h21,
    (hh _ (by decide)).trans h22, (hh _ (by decide)).trans h23⟩

/-- Amortized potential of the per-component LSF manager: sum of `lsfPhi` over all edgeful
components `ec` and all branches `j < k` whose footprints lie inside `[b, x.endAddr)`. Under
`CompLSFRepAt`, every `(ec, j)` window satisfies the guard (`compPhi_eq_sum`). -/
def compPhi {k : ℕ} (b : ℕ) (x : CompLSFMeta k) (mem : ℕ → ℕ) : ℕ :=
  ∑ ec : Fin x.numEdgeful, ∑ j : Fin k,
    if b ≤ x.winHandle ec j ∧ (x.winConc ec j).endAddr (x.winHandle ec j) ≤ x.endAddr then
      lsfPhi (x.winHandle ec j) (x.winConc ec j) mem
    else 0

/-- Full representation invariant for `CompLSFFamily k` at handle `b`. -/
def CompLSFRepAt (W : LSFWindowImpl) (k b : ℕ) (S : CompLSFFamily k) (x : CompLSFMeta k)
    (mem : ℕ → ℕ) : Prop :=
  ∃ hk : 1 ≤ k, x.h = W.h ∧ x.L_in = W.L_in ∧ x.P_fp = W.P_fp ∧
  1 ≤ x.L_w ∧ 2 ≤ x.h * x.L_w ∧ 1 ≤ x.eCap ∧
  x.numComps ≤ x.vCap ∧ x.numEdgeful ≤ x.m0Total ∧
  compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr ∧
  compHeaderAt mem b x ∧
  -- Shared graph/component invariants across all branches `j : Fin k`
  (∃ ℓ₀ : ℕ → ℝ, ∀ j : Fin k,
    CompLSFInv W.C_lsst ℓ₀ (S j) ∧
    (S j).G₀ = (S ⟨0, hk⟩).G₀ ∧
    (S j).G = (S ⟨0, hk⟩).G ∧
    (S j).k = k ∧
    (S j).crossEdges = (S ⟨0, hk⟩).crossEdges ∧
    (S j).insertedGlobal = (S ⟨0, hk⟩).insertedGlobal ∧
    (∀ c : Fin x.numComps, ((S j).compSt (x.compOf c)).G =
      ((S ⟨0, hk⟩).compSt (x.compOf c)).G)) ∧
  let cs0 := S ⟨0, hk⟩
  cs0.G₀.m = x.m0Total ∧
  CompEdgeTrack x.numComps x.vCap x.eCap x.compOf x.edgeC1 x.edgeC2 x.gtVert x.ghVert
    x.gtList x.ghList cs0 ∧
  -- Edgeful component indexing bijection
  (∀ c : Fin x.numComps,
    let Gc0 := compGraph cs0.G₀ (x.compOf c)
    mem (compEdgefulBase b x.vCap + c.1) = (if 1 ≤ Gc0.m then 1 else 0) ∧
    mem (compN0Base b x.vCap + c.1) = Gc0.n ∧
    mem (compM0Base b x.vCap + c.1) = Gc0.m ∧
    (1 ≤ Gc0.m → ∃ ec : Fin x.numEdgeful,
      x.edgefulIdx c = ec.1 ∧ mem (compEdgefulIdxBase b x.vCap + c.1) = ec.1 ∧
      x.edgefulComp ec = c)) ∧
  (∀ ec : Fin x.numEdgeful,
    1 ≤ (compGraph cs0.G₀ (x.compOf (x.edgefulComp ec))).m ∧
    x.edgefulIdx (x.edgefulComp ec) = ec.1) ∧
  -- Vertex-to-component array
  (∀ c : Fin x.numComps, ∀ v ∈ (cs0.compSt (x.compOf c)).G.V,
    mem (compVCompBase b + v) = c.1) ∧
  -- Edge arrays (`edgeComp1`, `edgeComp2`, `isCross`, `isIns`)
  (∀ e ∈ cs0.G.E,
    mem (compEdgeC1Base b x.vCap + e) = x.edgeC1 e ∧
    mem (compEdgeC2Base b x.vCap x.eCap + e) = x.edgeC2 e) ∧
  (∀ e < x.eCap,
    mem (compIsCrossBase b x.vCap x.eCap + e) = (if e ∈ cs0.crossEdges then 1 else 0) ∧
    mem (compIsInsBase b x.vCap x.eCap + e) = (if e ∈ cs0.insertedGlobal then 1 else 0)) ∧
  -- Ghost doubly-linked lists
  (let gPtr := compGhostBase b x.vCap x.eCap
   (∀ v < x.vCap,
     IsDoublyLinkedList mem (ghostTPrevBase gPtr x.vCap) (ghostTNextBase gPtr x.vCap x.eCap)
       (ghostTHeadBase gPtr + v) x.eCap (x.gtList v) ∧
     mem (ghostTCntBase gPtr x.vCap + v) = (x.gtList v).length ∧
     IsDoublyLinkedList mem (ghostHPrevBase gPtr x.vCap x.eCap) (ghostHNextBase gPtr x.vCap x.eCap)
       (ghostHHeadBase gPtr x.vCap + v) x.eCap (x.ghList v) ∧
     mem (ghostHCntBase gPtr x.vCap + v) = (x.ghList v).length) ∧
   (∀ e ∈ cs0.G.E, e ∈ cs0.crossEdges →
     mem (ghostTVertBase gPtr x.vCap x.eCap + e) = x.gtVert e ∧
     mem (ghostHVertBase gPtr x.vCap x.eCap + e) = x.ghVert e)) ∧
  -- Cleared `touchMark` array and static `oneLimb = [1, 0, ..., 0]`
  (∀ c < x.vCap, mem (compTouchMarkBase b x.vCap x.eCap + c) = 0) ∧
  (mem (compOneLimbBase b x.vCap x.eCap) = 1 ∧
   ∀ i, 1 ≤ i → i < x.L_w → mem (compOneLimbBase b x.vCap x.eCap + i) = 0) ∧
  -- Per-(edgeful component, branch) LSF windows, disjoint from tables and each other
  (∀ (ec : Fin x.numEdgeful) (j : Fin k),
    let hWin := x.winHandle ec j
    let xWin := x.winConc ec j
    mem (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) = hWin ∧
    (LSFRep W.h).rep hWin ((S j).compSt (x.compOf (x.edgefulComp ec))) xWin mem ∧
    xWin.vCap = x.vCap ∧ xWin.eCap = x.eCap ∧ xWin.L_w = x.L_w ∧
    compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ hWin ∧
    xWin.endAddr hWin ≤ x.endAddr) ∧
  (∀ (ec₁ ec₂ : Fin x.numEdgeful) (j₁ j₂ : Fin k),
    (ec₁ ≠ ec₂ ∨ j₁ ≠ j₂) →
    ∀ a, (LSFRep W.h).foot (x.winHandle ec₁ j₁) (x.winConc ec₁ j₁) a →
      ¬ (LSFRep W.h).foot (x.winHandle ec₂ j₂) (x.winConc ec₂ j₂) a)

/-- Contiguous footprint `[b, x.endAddr)` of a `CompLSF` handle `b`. -/
def compFoot {k : ℕ} (b : ℕ) (x : CompLSFMeta k) (a : ℕ) : Prop :=
  b ≤ a ∧ a < x.endAddr

/-- `DSRep (CompLSFFamily k)` for the per-component LSF manager. -/
def compLSFRep (W : LSFWindowImpl) (k : ℕ) : DSRep (CompLSFFamily k) where
  τ := CompLSFMeta k
  rep b S x mem := CompLSFRepAt W k b S x mem
  phi b x mem := compPhi b x mem
  foot b x := compFoot b x

/-- Under `CompLSFRepAt`, `compPhi` equals the unguarded sum of `lsfPhi` over all windows. -/
lemma compPhi_eq_sum {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {mem : ℕ → ℕ} (hrep : CompLSFRepAt W k b S x mem) :
    compPhi b x mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWins, _⟩
  unfold compPhi
  refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
  have hb_le_te : b ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize]; omega
  rw [ite_eq_left ⟨le_trans hb_le_te hge, hle⟩]

/-- Locality of `compLSFRep W k`: both `CompLSFRepAt` and `compPhi` depend only on `[b, x.endAddr)`. -/
theorem compLSFRep_local (W : LSFWindowImpl) (k : ℕ) : (compLSFRep W k).Local := by
  intro b S x mem mem' hfoot
  have hag : ∀ a, b ≤ a → a < x.endAddr → mem' a = mem a :=
    fun a ha1 ha2 => (hfoot a ⟨ha1, ha2⟩).symm
  have hphi : compPhi b x mem = compPhi b x mem' := by
    unfold compPhi
    refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · exact lsfPhi_congr fun a ha1 ha2 => (hag a (le_trans h.1 ha1) (lt_of_lt_of_le ha2 h.2)).symm
    · rfl
  refine ⟨?_, hphi⟩
  rintro ⟨hk, hxh, hxLin, hxP, hxLw, hx2h, hxeC, hnc, hne, hTE, hhdr, hBr, hm0, hTrack,
    hCompInfo, hEfInfo, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hHdrLe : b + compHdrSize ≤ x.endAddr := by
    dsimp only [compStaticSize] at hStat; omega
  have hAgreeSub : ∀ a, b ≤ a → a < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k →
      mem' a = mem a := fun a h1 h2 => hag a h1 (lt_of_lt_of_le h2 hTE)
  have hStatIn : ∀ a, b ≤ a → a < b + compStaticSize x.vCap x.eCap x.L_w → mem' a = mem a :=
    fun a h1 h2 => hag a h1 (lt_of_lt_of_le h2 hStat)
  refine ⟨hk, hxh, hxLin, hxP, hxLw, hx2h, hxeC, hnc, hne, hTE,
    compHeaderAt_of_agree hhdr (fun a h1 h2 => hag a h1 (lt_of_lt_of_le h2 hHdrLe)),
    hBr, hm0, hTrack, ?_, hEfInfo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDisj⟩
  · intro c
    obtain ⟨h1, h2, h3, h4⟩ := hCompInfo c
    have hc : c.1 < x.vCap := lt_of_lt_of_le c.2 hnc
    refine ⟨(hStatIn _ (by dsimp [compEdgefulBase, compVCompBase]; omega)
              (by dsimp [compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans h1,
      (hStatIn _ (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
        (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans h2,
      (hStatIn _ (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
        (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans h3,
      fun hm => ?_⟩
    obtain ⟨ec, he1, he2, he3⟩ := h4 hm
    exact ⟨ec, he1, (hStatIn _ (by dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
      (by dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans he2, he3⟩
  · intro c v hv
    obtain ⟨ℓ₀, hBr'⟩ := hBr
    have hvG : v ∈ (S ⟨0, by omega⟩).G.V :=
      (hBr' ⟨0, by omega⟩).1.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c, hTrack.compOf_mem c, hv⟩
    have hvlt : v < x.vCap := hTrack.hVlt v hvG
    exact (hStatIn _ (by dsimp [compVCompBase]; omega)
      (by dsimp [compVCompBase, compStaticSize]; omega)).trans (hVComp c v hv)
  · intro e he
    have helt : e < x.eCap := hTrack.hElt e he
    obtain ⟨h1, h2⟩ := hEdgeC e he
    exact ⟨(hStatIn _ (by dsimp [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
      (by dsimp [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans h1,
      (hStatIn _ (by dsimp [compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
        (by dsimp [compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans h2⟩
  · intro e he
    obtain ⟨h1, h2⟩ := hFlags e he
    exact ⟨(hStatIn _ (by dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
      (by dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans h1,
      (hStatIn _ (by dsimp [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
        (by dsimp [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize]; omega)).trans h2⟩
  · rcases hGhost with ⟨hGL, hGV⟩
    set gPtr := compGhostBase b x.vCap x.eCap
    have hgIn : ∀ off < compGhostSize x.vCap x.eCap, mem' (gPtr + off) = mem (gPtr + off) :=
      fun off hoff => hStatIn (gPtr + off)
        (by dsimp [gPtr, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base,
          compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
        (by dsimp [gPtr, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase,
          compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
          compEdgefulBase, compVCompBase, compStaticSize] at hoff ⊢; omega)
    refine ⟨fun v hv => ?_, fun e he hcr => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hGL v hv
      refine ⟨h1.of_agree (hgIn v (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := h1.2.1 e he
            simpa [ghostTPrevBase, Nat.add_assoc] using hgIn (4 * x.vCap + e) (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := h1.2.1 e he
            simpa [ghostTNextBase, Nat.add_assoc] using hgIn (4 * x.vCap + x.eCap + e) (by dsimp [compGhostSize]; omega)),
        by have h := hgIn (x.vCap + v) (by dsimp [compGhostSize]; omega)
           simpa [ghostTCntBase, Nat.add_assoc] using h.trans (by simpa [ghostTCntBase, Nat.add_assoc] using h2),
        h3.of_agree
          (by simpa [ghostHHeadBase, Nat.add_assoc] using hgIn (2 * x.vCap + v) (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := h3.2.1 e he
            simpa [ghostHPrevBase, Nat.add_assoc] using hgIn (4 * x.vCap + 3 * x.eCap + e) (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := h3.2.1 e he
            simpa [ghostHNextBase, Nat.add_assoc] using hgIn (4 * x.vCap + 4 * x.eCap + e) (by dsimp [compGhostSize]; omega)),
        by have h := hgIn (3 * x.vCap + v) (by dsimp [compGhostSize]; omega)
           simpa [ghostHCntBase, Nat.add_assoc] using h.trans (by simpa [ghostHCntBase, Nat.add_assoc] using h4)⟩
    · have helt := hTrack.hElt e he
      obtain ⟨h1, h2⟩ := hGV e he hcr
      exact ⟨by have h := hgIn (4 * x.vCap + 2 * x.eCap + e) (by dsimp [compGhostSize]; omega)
                simpa [ghostTVertBase, Nat.add_assoc] using h.trans (by simpa [ghostTVertBase, Nat.add_assoc] using h1),
        by have h := hgIn (4 * x.vCap + 5 * x.eCap + e) (by dsimp [compGhostSize]; omega)
           simpa [ghostHVertBase, Nat.add_assoc] using h.trans (by simpa [ghostHVertBase, Nat.add_assoc] using h2)⟩
  · intro c hc
    exact (hStatIn _ (by dsimp [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase,
        compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
        compEdgefulBase, compVCompBase]; omega)
      (by dsimp [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase,
        compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
        compVCompBase, compStaticSize]; omega)).trans (hTM c hc)
  · refine ⟨(hStatIn _ (by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compGhostSize,
        compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
      (by have := compOneLimb_end_eq b x.vCap x.eCap x.L_w; dsimp [compHandlesBase] at this; omega)).trans hOne.1,
      fun i hi1 hi2 => (hStatIn _ (by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase,
          compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
          compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
        (by have := compOneLimb_end_eq b x.vCap x.eCap x.L_w; dsimp [compHandlesBase] at this; omega)).trans (hOne.2 i hi1 hi2)⟩
  · intro ec j
    obtain ⟨hm, hrep, hv, he, hlw, hge, hle⟩ := hWins ec j
    have hidx : ec.1 * k + j.1 < x.m0Total * k := by
      calc ec.1 * k + j.1 < ec.1 * k + k := Nat.add_lt_add_left j.2 _
        _ = (ec.1 + 1) * k := by ring
        _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
    have hb_le_te : b ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize]; omega
    refine ⟨(hAgreeSub _ (by dsimp [compHandlesBase, compStaticSize]; omega)
        (by dsimp [compTablesEnd]; omega)).trans hm,
      (lsfRep_local W.h _ _ _ mem mem' fun a ha =>
        (hag a (le_trans hb_le_te (le_trans hge ha.1)) (lt_of_lt_of_le ha.2 hle)).symm).1 hrep,
      hv, he, hlw, hge, hle⟩

end

end MinCostFlow.SparseCore.Program
