module

public import MinCostFlow.SparseCore.Program.AssemblyBranchTour
public import MinCostFlow.SparseCore.Program.ReadRep
public import MinCostFlow.SparseCore.Program.ReadEmbOps
public import MinCostFlow.SparseCore.Program.OutSpec

/-!
# The memory of one branch of the sparse-core program (`AssemblyBranchRep`)

The sparse-core program (Lemma 5.17, page 23, with the bundle repair described in the
README) keeps `k`
branches. Each branch is the machine form of one `BundleTreeState` of the bundle tool, together
with the current input order (`AsmBranchAbs`). This file fixes where the data of one branch lives
in memory and proves that the representation is local (`asmBrRep_local`). The operations of the
branch (`AsmBranchAt`, `AssemblyTopIface.lean`) are proved in the files `AssemblyBranch*.lean`.

**The record.** A branch has a record of `16` words at its handle `b`. The first five words point
to the parts below, and the next four hold the caps and the limb count, which the procedures read:

| word | content |
| --- | --- |
| `b + 0` | handle of the readout data (P10, `readRep`) |
| `b + 1` | handle of the embedding table (P10, `embRep`) |
| `b + 2` | handle of the output graph (P7, `outGraphRep`) |
| `b + 3` | handle of the tour (P2) |
| `b + 4` | handle of the other parts (bundles P5, bucket spanners P6, activity tables) |
| `b + 5` .. `b + 8` | `vCap`, `eCap`, `tCap`, `L_w` |

**The parts and what they hold.**
* The readout data (P10) holds the view `⟨G, lsf, S, num, den⟩` with `G = tr.cs.G`,
  `lsf = tr.cs.lsf` (`tool.lsfs`) and `S = tr.S_cur` (`tool.S`). It serves readouts `2` and `3`.
* The embedding table (P10) holds, for every edge of the core graph, the walk `tr.emb e`. It
  serves readout `4` (`ReadEmbOut.mEmbAt`).
* The output graph (P7) holds `tr.S_cur`.
* The tour (P2) holds the input order, the rooted forest of the LSF and the marks. Through P7's
  view (`asmBrTourView`, `AssemblyBranchTour.lean`) it holds the core rotation lists of the input
  order, and it marks the ends of the edges of `S_cur` (`OutMarksOf`). It serves readout `5`.
* The other parts are a representation `X` of the whole abstract state. It is a parameter here.

The parts lie in pairwise disjoint cells (`AsmBrDisjoint`). The potential is the sum of the
potentials of the parts. The representation does not depend on the graph, `k`, `M`, `N` or the
caps of the instance: the caps are stored in the concrete state and in the record.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.SparseCore.Program.Read

/-! ## The record -/

/-- Offset of the handle of the readout data in the record of a branch. -/
def ASM_BR_READ : ℕ := 0
/-- Offset of the handle of the embedding table. -/
def ASM_BR_EMB : ℕ := 1
/-- Offset of the handle of the output graph. -/
def ASM_BR_OUT : ℕ := 2
/-- Offset of the handle of the tour. -/
def ASM_BR_TOUR : ℕ := 3
/-- Offset of the handle of the other parts. -/
def ASM_BR_REST : ℕ := 4
/-- Offset of the vertex cap. -/
def ASM_BR_VCAP : ℕ := 5
/-- Offset of the edge cap. -/
def ASM_BR_ECAP : ℕ := 6
/-- Offset of the cap on the names of the tree edges. -/
def ASM_BR_TCAP : ℕ := 7
/-- Offset of the limb count of the stretch tables. -/
def ASM_BR_LW : ℕ := 8
/-- The number of words of the record. -/
def ASM_BR_SIZE : ℕ := 16

/-- The concrete state of a branch: the caps and the limb count, and for each part its handle and
its concrete state. The tour part is a family of representations of P2 indexed by the caps, so its
concrete state has the type of the member at the stored caps. `sTour` is the state of P7's view
of the tour: the core lists and the marks. -/
structure AsmBrConc (TR : ℕ → ℕ → DSRep AsmTourAbs) (τX : Type) where
  vCap : ℕ
  eCap : ℕ
  tCap : ℕ
  L_w : ℕ
  readH : ℕ
  yRead : ReadConc
  embH : ℕ
  yEmb : EmbConc
  outH : ℕ
  gOut : ℕ
  tourH : ℕ
  sTour : OutTourAbs
  xTour : (TR vCap eCap).τ
  restH : ℕ
  xRest : τX

/-- The cells of part `i` of a branch with handle `b`: the record (`0`), the readout data (`1`),
the embedding table (`2`), the output graph (`3`), the tour (`4`) and the other parts (`5`). -/
def asmBrPart {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} (X : DSRep σX) (b : ℕ)
    (x : AsmBrConc TR X.τ) : ℕ → ℕ → Prop
  | 0, a => b ≤ a ∧ a < b + ASM_BR_SIZE
  | 1, a => readFoot x.vCap x.eCap x.tCap x.L_w x.readH x.yRead a
  | 2, a => embFoot x.eCap x.embH x.yEmb a
  | 3, a => (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a
  | 4, a => (TR x.vCap x.eCap).foot x.tourH x.xTour a
  | 5, a => X.foot x.restH x.xRest a
  | _, _ => False

/-- The six parts of a branch lie in pairwise disjoint cells. -/
def AsmBrDisjoint {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} (X : DSRep σX) (b : ℕ)
    (x : AsmBrConc TR X.τ) : Prop :=
  ∀ i < 6, ∀ j < 6, i ≠ j → ∀ a, asmBrPart X b x i a → ¬ asmBrPart X b x j a

/-- The cells of a branch: the union of its six parts. -/
def asmBrFoot {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} (X : DSRep σX) (b : ℕ)
    (x : AsmBrConc TR X.τ) (a : ℕ) : Prop :=
  ∃ i < 6, asmBrPart X b x i a

/-- **The memory of a branch.** The record at `b` holds the handles, the caps and the limb count;
the readout data hold `⟨tr.cs.G, tr.cs.lsf, tr.S_cur, num, den⟩` and meet `ReadView.Inv`; the
embedding table holds `tr.emb e` for every edge `e` of the core graph; the output graph is
`tr.S_cur`; the tour holds `⟨ord, tr.cs.lsf.F, marks⟩`, so that P7's view of it holds the core
rotation lists of the input order `ord`, with the ends of `S_cur` marked; the other parts hold the
abstract state for `X`. Moreover, the vertices of `S_cur`
are the roots of the forest, the caps are polynomial in `M + N` with exponent `capExp`, the limb
count meets the bound of readout `2`, and the six parts are pairwise disjoint. -/
def AsmBrRepAt {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs) (X : DSRep (AsmBranchAbs depth))
    (P L capExp b : ℕ) (a : AsmBranchAbs depth) (x : AsmBrConc TR X.τ) (mem : ℕ → ℕ) : Prop :=
  mem (b + ASM_BR_READ) = x.readH ∧ mem (b + ASM_BR_EMB) = x.embH ∧
  mem (b + ASM_BR_OUT) = x.outH ∧ mem (b + ASM_BR_TOUR) = x.tourH ∧
  mem (b + ASM_BR_REST) = x.restH ∧ mem (b + ASM_BR_VCAP) = x.vCap ∧
  mem (b + ASM_BR_ECAP) = x.eCap ∧ mem (b + ASM_BR_TCAP) = x.tCap ∧
  mem (b + ASM_BR_LW) = x.L_w ∧
  x.yRead.view.G = a.tr.cs.G ∧ x.yRead.view.lsf = a.tr.cs.lsf ∧ x.yRead.view.S = a.tr.S_cur ∧
  x.yRead.view.Inv x.vCap x.eCap x.tCap ∧
  (readRep x.vCap x.eCap x.tCap x.L_w P).rep x.readH x.yRead.view x.yRead mem ∧
  (embRep x.eCap).rep x.embH x.yEmb.view x.yEmb mem ∧
  (coreGraph a.tr.cs.G a.tr.cs.lsf).E ⊆ x.yEmb.view.dom ∧
  (∀ e ∈ (coreGraph a.tr.cs.G a.tr.cs.lsf).E, x.yEmb.view.emb e = a.tr.emb e) ∧
  (outGraphRep x.vCap x.eCap).rep x.outH a.tr.S_cur x.gOut mem ∧
  (asmBrTourView TR a x.vCap x.eCap).rep x.tourH x.sTour x.xTour mem ∧
  OutMarksOf x.sTour (outCoreOrder a.tr a.ord) a.tr.S_cur.E ∧
  X.rep x.restH a x.xRest mem ∧
  a.tr.S_cur.V = a.tr.cs.RF.R ∧
  x.vCap + x.eCap + 2 ≤ (a.tr.m₀ + a.tr.n₀ + 2) ^ capExp ∧
  x.L_w ≤
    L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (a.tr.m₀ + a.tr.n₀ + 2) + 1) ∧
  AsmBrDisjoint X b x

/-- The potential of a branch: the potentials of the readout data, the tour and the other parts
(the embedding table and the output graph have none). -/
noncomputable def asmBrPhi {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} (X : DSRep σX)
    (x : AsmBrConc TR X.τ) (mem : ℕ → ℕ) : ℕ :=
  readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
    (TR x.vCap x.eCap).phi x.tourH x.xTour mem + X.phi x.restH x.xRest mem

/-- **The representation of a branch** (`AsmBranchAt.rep`), for the tour family `TR` and the
representation `X` of the other parts, at precision `P`, input limb count `L` and cap exponent
`capExp`. -/
noncomputable def asmBrRep {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (X : DSRep (AsmBranchAbs depth)) (P L capExp : ℕ) : DSRep (AsmBranchAbs depth) where
  τ := AsmBrConc TR X.τ
  rep b a x mem := AsmBrRepAt TR X P L capExp b a x mem
  phi _ x mem := asmBrPhi X x mem
  foot b x a := asmBrFoot X b x a

/-! ## Basic facts -/

theorem asmBrRep_rep {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {X : DSRep (AsmBranchAbs depth)} {P L capExp b : ℕ} {a : AsmBranchAbs depth}
    {x : AsmBrConc TR X.τ} {mem : ℕ → ℕ} :
    (asmBrRep TR X P L capExp).rep b a x mem ↔ AsmBrRepAt TR X P L capExp b a x mem :=
  Iff.rfl

theorem asmBrRep_foot {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {X : DSRep (AsmBranchAbs depth)} {P L capExp b : ℕ} {x : AsmBrConc TR X.τ} {a : ℕ} :
    (asmBrRep TR X P L capExp).foot b x a ↔ asmBrFoot X b x a :=
  Iff.rfl

theorem asmBrRep_phi {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {X : DSRep (AsmBranchAbs depth)} {P L capExp b : ℕ} {x : AsmBrConc TR X.τ}
    {mem : ℕ → ℕ} :
    (asmBrRep TR X P L capExp).phi b x mem = asmBrPhi X x mem :=
  rfl

/-- Each part lies in the cells of the branch. -/
theorem asmBrFoot_of_part {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b : ℕ} {x : AsmBrConc TR X.τ} {i a : ℕ} (hi : i < 6) (ha : asmBrPart X b x i a) :
    asmBrFoot X b x a :=
  ⟨i, hi, ha⟩

/-- **Locality.** The representation of a branch is local when the tour family and the other
parts are. -/
theorem asmBrRep_local {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {X : DSRep (AsmBranchAbs depth)} (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hX : X.Local) (P L capExp : ℕ) : (asmBrRep TR X P L capExp).Local := by
  intro b a x mem mem' hag
  have hpart : ∀ i < 6, ∀ c, asmBrPart X b x i c → mem c = mem' c :=
    fun i hi c hc => hag c (asmBrFoot_of_part hi hc)
  have hrd := readRep_local x.vCap x.eCap x.tCap x.L_w P x.readH x.yRead.view x.yRead mem mem'
    (fun c hc => hpart 1 (by decide) c hc)
  have hem := embRep_local x.eCap x.embH x.yEmb.view x.yEmb mem mem'
    (fun c hc => hpart 2 (by decide) c hc)
  have hout := outGraphRep_local x.vCap x.eCap x.outH a.tr.S_cur x.gOut mem mem'
    (fun c hc => hpart 3 (by decide) c hc)
  have htour := asmTourView_local (hTR x.vCap x.eCap) a.ord a.tr.cs.lsf.F
    (outCoreOrder a.tr a.ord) x.tourH x.sTour x.xTour mem mem'
    (fun c hc => hpart 4 (by decide) c hc)
  have hrest := hX x.restH a x.xRest mem mem' (fun c hc => hpart 5 (by decide) c hc)
  have hrec : ∀ i < ASM_BR_SIZE, mem (b + i) = mem' (b + i) := fun i hi =>
    hpart 0 (by decide) (b + i) ⟨by omega, by omega⟩
  refine ⟨fun hrep => ?_, ?_⟩
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hG, hlsf, hS, hinv, hR, hE, hdom, hemb, hO, hT,
      hmarks, hX', hV, hcap, hLw, hdisj⟩ := hrep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hG, hlsf, hS, hinv, hrd.1 hR, hem.1 hE, hdom,
      hemb, hout.1 hO, htour.1 hT, hmarks, hrest.1 hX', hV, hcap, hLw, hdisj⟩
    · rw [← hrec ASM_BR_READ (by decide)]; exact h0
    · rw [← hrec ASM_BR_EMB (by decide)]; exact h1
    · rw [← hrec ASM_BR_OUT (by decide)]; exact h2
    · rw [← hrec ASM_BR_TOUR (by decide)]; exact h3
    · rw [← hrec ASM_BR_REST (by decide)]; exact h4
    · rw [← hrec ASM_BR_VCAP (by decide)]; exact h5
    · rw [← hrec ASM_BR_ECAP (by decide)]; exact h6
    · rw [← hrec ASM_BR_TCAP (by decide)]; exact h7
    · rw [← hrec ASM_BR_LW (by decide)]; exact h8
  · show asmBrPhi X x mem = asmBrPhi X x mem'
    unfold asmBrPhi
    have hph : (TR x.vCap x.eCap).phi x.tourH x.xTour mem =
        (TR x.vCap x.eCap).phi x.tourH x.xTour mem' := htour.2
    rw [hph, hrest.2]

/-- The record of a branch lies below `h` when its cells do. -/
theorem asmBr_record_lt {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b h : ℕ} {x : AsmBrConc TR X.τ} (hfoot : ∀ a, asmBrFoot X b x a → a < h) :
    b + ASM_BR_SIZE ≤ h := by
  have := hfoot (b + (ASM_BR_SIZE - 1)) ⟨0, by decide, by simp [asmBrPart, ASM_BR_SIZE]⟩
  simp only [ASM_BR_SIZE] at this ⊢
  omega

end MinCostFlow.SparseCore.Program
