module

public import MinCostFlow.LSF.Program.BlockRep
public import MinCostFlow.LSF.Lemma54With
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.Machine.WideWord.LSSTProgram
public import WordRAM.DataStructure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# WordRAM Data-Structure Specification for Dynamic LSF (`Lemma 5.4`)

This file defines the `WordRAM.DataStructure LSFState` specification `lsfDataStructure` and its
concrete memory representation `LSFRep` matching the static layout of `Layout.lean` and the five
block representation predicates of `BlockRep.lean`:

* `LSFStructInv`: threshold-free structural invariants of `LSFState` maintained across all dynamic
  `.insert`, `.delete`, and `.split` updates.
* `LSFConcrete`, `lsfHeaderAt`, and `LSFRep`: full WordRAM concrete state bundling `TBlockAt`,
  `FAncAt`, `WBlockAt`, `WstrAt`, `AuxAt`, `DynGraphAt` for `G` and `F`, and the 24-word header.
* `lsfPhi`: bounds-checked amortized potential function charging `minEdgeUp` (`O(log n₀)` per new
  root), `cutEdge` deletion (`O(1)` per new root), and smaller-to-larger BFS component relabeling
  (`O(|C_small|)` per component split).
* `lsfDataStructure` and linear cost bridge lemmas connecting `lsfInitCost` and `lsfBatchCost` to
  `lsfOverhead`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord

/-! ## Threshold-free structural invariant for `LSFState` -/

/-- Structural invariants of `LSFState` independent of `(thresh, K_σ, ℓ₀)`, sufficient to
execute and verify `applyLSFBatch` in `op 0`. -/
structure LSFStructInv (S : LSFState) : Prop where
  hG₀_val : S.G₀.IsValid
  hG_val : S.G.IsValid
  hV₀ : S.G₀.V.Nonempty
  hk : 1 ≤ S.k
  hT₀ : IsRootedTree S.T₀ S.r₀
  hTV : S.T₀.V = S.G₀.V
  hr₀_base : S.r₀ ∈ S.R₀_base
  hR₀_sub : S.R₀_base ⊆ S.T₀.V
  hord : IsEdgeOrder S.T₀ S.π
  hTG₀ : ∀ f ∈ S.T₀.E, f ∈ S.G₀.E → S.T₀.tail f = S.G₀.tail f ∧ S.T₀.head f = S.G₀.head f
  hT_cur_forest : S.T_cur.IsForest
  hT_cur_V : S.T_cur.V = S.G.V
  hT_cur_E : S.T_cur.E = S.T₀.E
  hF_sub_G : S.G.IsSubgraph S.RF.F
  horig_id : ∀ x ∈ S.T₀.V, S.origVert x = x
  horig_split : ∀ x ∈ S.isolatedVerts, S.origVert x ∈ S.R_orig
  horig_T : ∀ e ∈ S.T₀.E, S.origVert (S.T_cur.tail e) = S.T₀.tail e ∧ S.origVert (S.T_cur.head e) = S.T₀.head e
  hunsplit_F : ∀ x ∈ S.G.V, S.origVert x ∉ S.R_orig → ∀ f ∈ S.T₀.E,
    (S.T₀.tail f = S.origVert x → S.T_cur.tail f = x) ∧
    (S.T₀.head f = S.origVert x → S.T_cur.head f = x)
  hdisj_iso : Disjoint S.T₀.V S.isolatedVerts
  hGV_eq : S.G.V = S.T₀.V ∪ S.isolatedVerts
  hins_sub : S.insertedEdges ⊆ S.G.E
  hins_wstr : ∀ e ∈ S.insertedEdges, S.wstr e = 1 ∧ S.G.tail e ∈ S.R ∧ S.G.head e ∈ S.R

lemma LSFInvWith.toStructInv {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) : LSFStructInv S where
  hG₀_val := I.hG₀_val
  hG_val := I.hG_val
  hV₀ := I.hV₀
  hk := I.hk
  hT₀ := I.hT₀
  hTV := I.hTV
  hr₀_base := I.hr₀_base
  hR₀_sub := I.hR₀_sub
  hord := I.hord
  hTG₀ := I.hTG₀
  hT_cur_forest := I.hT_cur_forest
  hT_cur_V := I.hT_cur_V
  hT_cur_E := I.hT_cur_E
  hF_sub_G := I.hF_sub_G
  horig_id := I.horig_id
  horig_split := I.horig_split
  horig_T := I.horig_T
  hunsplit_F := I.hunsplit_F
  hdisj_iso := I.hdisj_iso
  hGV_eq := I.hGV_eq
  hins_sub := I.hins_sub
  hins_wstr := I.hins_wstr

lemma LSFStructInv.R_orig_sub {S : LSFState} (I : LSFStructInv S) : S.R_orig ⊆ S.T₀.V :=
  upClosure_subset (hldAuxTree_isRootedTree I.hT₀) I.hR₀_sub

lemma LSFStructInv.R_orig_bf {S : LSFState} (I : LSFStructInv S) : IsBranchFree S.T₀ S.r₀ S.R_orig :=
  upClosure_isBranchFree I.hT₀ I.hR₀_sub

lemma LSFStructInv.r₀_mem_R_orig {S : LSFState} (I : LSFStructInv S) : S.r₀ ∈ S.R_orig :=
  subset_upClosure I.hr₀_base

lemma LSFStructInv.origVert_mem_TV {S : LSFState} (I : LSFStructInv S) {x : ℕ}
    (hx : x ∈ S.G.V) : S.origVert x ∈ S.T₀.V := by
  rw [I.hGV_eq, Finset.mem_union] at hx
  rcases hx with hxT | hxIso
  · rwa [I.horig_id x hxT]
  · exact I.R_orig_sub (I.horig_split x hxIso)

lemma LSFStructInv.R_card_eq {S : LSFState} (I : LSFStructInv S) :
    S.R.card = S.R_orig.card + S.isolatedVerts.card := by
  have hdisj : Disjoint S.R_orig S.isolatedVerts :=
    Finset.disjoint_left.mpr fun x hx1 hx2 =>
      Finset.disjoint_left.mp I.hdisj_iso (I.R_orig_sub hx1) hx2
  exact Finset.card_union_of_disjoint hdisj

lemma LSFStructInv.RF_V_eq {S : LSFState} (I : LSFStructInv S) :
    S.RF.F.V = S.G.V := I.hT_cur_V

lemma LSFStructInv.RF_E_card_le {S : LSFState} (_I : LSFStructInv S) :
    S.RF.F.E.card ≤ S.T₀.E.card :=
  Finset.card_le_card (Finset.sdiff_subset :
    S.T₀.E \ deletedEdges S.T₀ S.r₀ S.R_orig S.π ⊆ S.T₀.E)

/-! ## Concrete state, header layout, potential, and `LSFRep` -/

/-- Concrete metadata tracked alongside memory `mem` for a handle `b`. -/
structure LSFConcrete where
  vCap : ℕ
  eCap : ℕ
  n0 : ℕ
  m0 : ℕ
  tM : ℕ
  h : ℕ
  P_fp : ℕ
  L_in : ℕ
  L_w : ℕ
  k_nat : ℕ
  tOrigList : List ℕ
  vList : List ℕ
  t0Parent : ℕ → ℕ
  t0ParentTreeIdx : ℕ → ℕ
  t0Depth : ℕ → ℕ
  thParent : ℕ → ℕ
  upV : ℕ → ℕ → ℕ
  upMinIdx : ℕ → ℕ → ℕ
  rList : List ℕ
  compId : ℕ → ℕ
  compRoot : ℕ → ℕ
  compSize : ℕ → ℕ
  activeCids : Finset ℕ

/-- End address of the static LSF footprint `[b, x.endAddr b)`. -/
def LSFConcrete.endAddr (x : LSFConcrete) (b : ℕ) : ℕ :=
  lsfEndAddr b x.vCap x.eCap x.n0 x.tM x.L_w

/-- 24-word handle header predicate at base address `b`. -/
def lsfHeaderAt (mem : ℕ → ℕ) (b : ℕ) (S : LSFState) (x : LSFConcrete) : Prop :=
  mem (b + lsfOffVCap) = x.vCap ∧
  mem (b + lsfOffECap) = x.eCap ∧
  mem (b + lsfOffN0) = x.n0 ∧
  mem (b + lsfOffM0) = x.m0 ∧
  mem (b + lsfOffDgGPtr) = lsfDgGPtr b ∧
  mem (b + lsfOffTPtr) = lsfTBlockPtr b x.vCap x.eCap ∧
  mem (b + lsfOffDgFPtr) = lsfDgFPtr b x.vCap x.eCap x.tM ∧
  mem (b + lsfOffFAncPtr) = lsfFAncPtr b x.vCap x.eCap x.n0 x.tM ∧
  mem (b + lsfOffWPtr) = lsfWBlockPtr b x.vCap x.eCap x.n0 x.tM ∧
  mem (b + lsfOffWstrNumPtr) = lsfWstrNumPtr b x.vCap x.eCap x.n0 x.tM ∧
  mem (b + lsfOffWstrDenPtr) = lsfWstrDenPtr b x.vCap x.eCap x.n0 x.tM x.L_w ∧
  mem (b + lsfOffLW) = x.L_w ∧
  mem (b + lsfOffHLimb) = x.h ∧
  mem (b + lsfOffPFp) = x.P_fp ∧
  mem (b + lsfOffLIn) = x.L_in ∧
  mem (b + lsfOffThresh) = 0 ∧
  mem (b + lsfOffRCount) = S.R.card ∧
  mem (b + lsfOffNumUpd) = 0 ∧
  mem (b + lsfOffAuxPtr) = lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w ∧
  mem (b + lsfOffEnd) = lsfEndAddr b x.vCap x.eCap x.n0 x.tM x.L_w ∧
  mem (b + lsfOffR0) = S.r₀ ∧
  mem (b + lsfOffKNat) = x.k_nat ∧
  mem (b + lsfOffTM) = x.tM ∧
  mem (b + lsfOffRes) = 0

lemma lsfHeaderAt.of_agree {mem mem' : ℕ → ℕ} {b : ℕ} {S : LSFState} {x : LSFConcrete}
    (h : lsfHeaderAt mem b S x)
    (hagree : ∀ a, b ≤ a → a < b + lsfHdrSize → mem' a = mem a) :
    lsfHeaderAt mem' b S x := by
  have hhd : ∀ off, off < lsfHdrSize → mem' (b + off) = mem (b + off) :=
    fun off hoff => hagree (b + off) (Nat.le_add_right _ _) (Nat.add_lt_add_left hoff b)
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23⟩
  refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1,
    (hhd _ (by decide)).trans h2, (hhd _ (by decide)).trans h3,
    (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
    (hhd _ (by decide)).trans h6, (hhd _ (by decide)).trans h7,
    (hhd _ (by decide)).trans h8, (hhd _ (by decide)).trans h9,
    (hhd _ (by decide)).trans h10, (hhd _ (by decide)).trans h11,
    (hhd _ (by decide)).trans h12, (hhd _ (by decide)).trans h13,
    (hhd _ (by decide)).trans h14, (hhd _ (by decide)).trans h15,
    (hhd _ (by decide)).trans h16, (hhd _ (by decide)).trans h17,
    (hhd _ (by decide)).trans h18, (hhd _ (by decide)).trans h19,
    (hhd _ (by decide)).trans h20, (hhd _ (by decide)).trans h21,
    (hhd _ (by decide)).trans h22, (hhd _ (by decide)).trans h23⟩

/-- Bounds-checked potential `Φ(b, x, mem)` summing:
* `500 * auxLogCap n₀ * (n₀ - origRootCount)` for `T_H`-closure root insertions (`minEdgeUp`),
* `1400 * edgeCountF` for decremental forest edge cuts (`dgDeleteEdge`),
* `1100 * ∑_{e ∈ F.E} ⌊log₂ max(1, compSize[compId[F.tail e]] - 1)⌋` for lock-step BFS
  smaller-to-larger component relabeling across both edge cuts and vertex splits. -/
def lsfPhi (b : ℕ) (x : LSFConcrete) (mem : ℕ → ℕ) : ℕ :=
  let fAncPtr := lsfFAncPtr b x.vCap x.eCap x.n0 x.tM
  let auxPtr := lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w
  let dgFPtr := lsfDgFPtr b x.vCap x.eCap x.tM
  let eCapF := fECap x.eCap x.n0
  let mF := mem (dgFPtr + dgMOff)
  let origRootCount := (Finset.range x.n0).sum fun i =>
    let v := mem (auxVListBase auxPtr x.vCap + i)
    if v < x.vCap then (if mem (fIsRootBase fAncPtr + v) = 1 then 1 else 0) else 0
  let phiRorig := 500 * auxLogCap x.n0 * (x.n0 - origRootCount)
  let phiCut := 1400 * mF
  let phiRelab := 1100 * (Finset.range (min mF eCapF)).sum fun i =>
    let e := mem (dgEListBase dgFPtr x.vCap eCapF + i)
    if e < eCapF then
      let s := mem (dgETailSlotBase dgFPtr x.vCap eCapF + e)
      if s < x.vCap then
        let u := mem (dgIntToExtBase dgFPtr x.vCap + s)
        if u < x.vCap then
          let cid := mem (fCompIdBase fAncPtr x.vCap + u)
          if cid < x.vCap then
            Nat.log 2 (max 1 (mem (fCompSizeBase fAncPtr x.vCap + cid) - 1))
          else 0
        else 0
      else 0
    else 0
  phiRorig + phiCut + phiRelab

lemma lsfPhi_congr {b : ℕ} {x : LSFConcrete} {mem mem' : ℕ → ℕ}
    (hagree : ∀ a, b ≤ a → a < x.endAddr b → mem a = mem' a) :
    lsfPhi b x mem = lsfPhi b x mem' := by
  dsimp only [lsfPhi, LSFConcrete.endAddr] at *
  set fAncPtr := lsfFAncPtr b x.vCap x.eCap x.n0 x.tM
  set auxPtr := lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w
  set dgFPtr := lsfDgFPtr b x.vCap x.eCap x.tM
  set eCapF := fECap x.eCap x.n0
  have hsub_aux : ∀ a, auxPtr ≤ a → a < auxPtr + auxSize x.vCap x.n0 → mem a = mem' a := by
    intro a ha1 ha2
    have hge : b ≤ auxPtr := by
      dsimp only [auxPtr, lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr,
        lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
    exact hagree a (le_trans hge ha1) (lt_of_lt_of_le ha2 (lsfEndAddr_eq_aux_add _ _ _ _ _ _))
  have hsub_fAnc : ∀ a, fAncPtr ≤ a → a < fAncPtr + fAncSize x.vCap → mem a = mem' a := by
    intro a ha1 ha2
    have hge : b ≤ fAncPtr := by
      dsimp only [fAncPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
    have hr := lsfFAnc_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
    exact hagree a (le_trans hge ha1) (lt_of_lt_of_le ha2 hr.2)
  have hsub_dgF : ∀ a, dgFPtr ≤ a → a < dgFPtr + dynGraphSize x.vCap eCapF →
      mem a = mem' a := by
    intro a ha1 ha2
    have hge : b ≤ dgFPtr := by
      dsimp only [dgFPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
    have hr := lsfDgF_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
    exact hagree a (le_trans hge ha1) (lt_of_lt_of_le ha2 hr.2)
  have hVList : ∀ i ∈ Finset.range x.n0,
      mem (auxVListBase auxPtr x.vCap + i) = mem' (auxVListBase auxPtr x.vCap + i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact hsub_aux _ (by dsimp [auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxVListBase, auxVIdxBase, auxSize]; omega)
  have hMOff : mem (dgFPtr + dgMOff) = mem' (dgFPtr + dgMOff) :=
    hsub_dgF _ (Nat.le_add_right _ _) (by dsimp [dgMOff, dynGraphSize]; omega)
  have hsum1 : (Finset.range x.n0).sum (fun i =>
      let v := mem (auxVListBase auxPtr x.vCap + i)
      if v < x.vCap then (if mem (fIsRootBase fAncPtr + v) = 1 then 1 else 0) else 0) =
      (Finset.range x.n0).sum (fun i =>
      let v := mem' (auxVListBase auxPtr x.vCap + i)
      if v < x.vCap then (if mem' (fIsRootBase fAncPtr + v) = 1 then 1 else 0) else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    dsimp only
    rw [hVList i hi]
    by_cases hv : mem' (auxVListBase auxPtr x.vCap + i) < x.vCap
    · simp only [hv, ↓reduceIte]
      have hroot : mem (fIsRootBase fAncPtr + mem' (auxVListBase auxPtr x.vCap + i)) =
          mem' (fIsRootBase fAncPtr + mem' (auxVListBase auxPtr x.vCap + i)) :=
        hsub_fAnc _ (by dsimp [fIsRootBase, fAncHdrSize]; omega)
          (by dsimp [fIsRootBase, fAncHdrSize, fAncSize]; omega)
      rw [hroot]
    · simp only [hv, ↓reduceIte]
  have hsum2 : (Finset.range (min (mem (dgFPtr + dgMOff)) eCapF)).sum (fun i =>
      let e := mem (dgEListBase dgFPtr x.vCap eCapF + i)
      if e < eCapF then
        let s := mem (dgETailSlotBase dgFPtr x.vCap eCapF + e)
        if s < x.vCap then
          let u := mem (dgIntToExtBase dgFPtr x.vCap + s)
          if u < x.vCap then
            let cid := mem (fCompIdBase fAncPtr x.vCap + u)
            if cid < x.vCap then
              Nat.log 2 (max 1 (mem (fCompSizeBase fAncPtr x.vCap + cid) - 1))
            else 0
          else 0
        else 0
      else 0) =
      (Finset.range (min (mem' (dgFPtr + dgMOff)) eCapF)).sum (fun i =>
      let e := mem' (dgEListBase dgFPtr x.vCap eCapF + i)
      if e < eCapF then
        let s := mem' (dgETailSlotBase dgFPtr x.vCap eCapF + e)
        if s < x.vCap then
          let u := mem' (dgIntToExtBase dgFPtr x.vCap + s)
          if u < x.vCap then
            let cid := mem' (fCompIdBase fAncPtr x.vCap + u)
            if cid < x.vCap then
              Nat.log 2 (max 1 (mem' (fCompSizeBase fAncPtr x.vCap + cid) - 1))
            else 0
          else 0
        else 0
      else 0) := by
    rw [hMOff]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < eCapF := lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.min_le_right _ _)
    dsimp only
    have heq : mem (dgEListBase dgFPtr x.vCap eCapF + i) =
        mem' (dgEListBase dgFPtr x.vCap eCapF + i) :=
      hsub_dgF _ (by dsimp [dgEListBase]; omega) (by dsimp [dgEListBase, dynGraphSize]; omega)
    rw [heq]
    set e := mem' (dgEListBase dgFPtr x.vCap eCapF + i)
    by_cases he : e < eCapF
    · simp only [he, ↓reduceIte]
      have hseq : mem (dgETailSlotBase dgFPtr x.vCap eCapF + e) =
          mem' (dgETailSlotBase dgFPtr x.vCap eCapF + e) :=
        hsub_dgF _ (by dsimp [dgETailSlotBase]; omega)
          (by dsimp [dgETailSlotBase, dynGraphSize]; omega)
      rw [hseq]
      set s := mem' (dgETailSlotBase dgFPtr x.vCap eCapF + e)
      by_cases hs : s < x.vCap
      · simp only [hs, ↓reduceIte]
        have hueq : mem (dgIntToExtBase dgFPtr x.vCap + s) =
            mem' (dgIntToExtBase dgFPtr x.vCap + s) :=
          hsub_dgF _ (by dsimp [dgIntToExtBase]; omega)
            (by dsimp [dgIntToExtBase, dynGraphSize]; omega)
        rw [hueq]
        set u := mem' (dgIntToExtBase dgFPtr x.vCap + s)
        by_cases hu : u < x.vCap
        · simp only [hu, ↓reduceIte]
          have hcid : mem (fCompIdBase fAncPtr x.vCap + u) =
              mem' (fCompIdBase fAncPtr x.vCap + u) :=
            hsub_fAnc _ (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]; omega)
              (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize, fAncSize]; omega)
          rw [hcid]
          set cid := mem' (fCompIdBase fAncPtr x.vCap + u)
          by_cases hlt : cid < x.vCap
          · simp only [hlt, ↓reduceIte]
            have hsz : mem (fCompSizeBase fAncPtr x.vCap + cid) =
                mem' (fCompSizeBase fAncPtr x.vCap + cid) :=
              hsub_fAnc _
                (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase,
                  fAncHdrSize]; omega)
                (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase,
                  fAncHdrSize, fAncSize]; omega)
            rw [hsz]
          · simp only [hlt, ↓reduceIte]
        · simp only [hu, ↓reduceIte]
      · simp only [hs, ↓reduceIte]
    · simp only [he, ↓reduceIte]
  rw [hsum1, hsum2, hMOff]

lemma lsfPhi_init_le {b : ℕ} {x : LSFConcrete} {mem : ℕ → ℕ}
    (hm : mem (lsfDgFPtr b x.vCap x.eCap x.tM + dgMOff) ≤ x.n0)
    (hsz : ∀ i < min (mem (lsfDgFPtr b x.vCap x.eCap x.tM + dgMOff)) (fECap x.eCap x.n0),
      let dgFPtr := lsfDgFPtr b x.vCap x.eCap x.tM
      let fAncPtr := lsfFAncPtr b x.vCap x.eCap x.n0 x.tM
      let eCapF := fECap x.eCap x.n0
      let e := mem (dgEListBase dgFPtr x.vCap eCapF + i)
      e < eCapF →
      let s := mem (dgETailSlotBase dgFPtr x.vCap eCapF + e)
      s < x.vCap →
      let u := mem (dgIntToExtBase dgFPtr x.vCap + s)
      u < x.vCap →
      let cid := mem (fCompIdBase fAncPtr x.vCap + u)
      cid < x.vCap → mem (fCompSizeBase fAncPtr x.vCap + cid) ≤ x.n0) :
    lsfPhi b x mem ≤ 3000 * (x.n0 + 1) * (Nat.log 2 (x.n0 + 2) + 1) := by
  dsimp only [lsfPhi]
  set fAncPtr := lsfFAncPtr b x.vCap x.eCap x.n0 x.tM
  set auxPtr := lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w
  set dgFPtr := lsfDgFPtr b x.vCap x.eCap x.tM
  set eCapF := fECap x.eCap x.n0
  set mF := mem (dgFPtr + dgMOff)
  set L := Nat.log 2 (x.n0 + 2) + 1
  have hlog_cap : auxLogCap x.n0 ≤ L := by
    dsimp [auxLogCap, L]
    exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have hsub_le : x.n0 - (Finset.range x.n0).sum (fun i =>
      let v := mem (auxVListBase auxPtr x.vCap + i)
      if v < x.vCap then (if mem (fIsRootBase fAncPtr + v) = 1 then 1 else 0) else 0) ≤ x.n0 :=
    Nat.sub_le _ _
  have hphiR : 500 * auxLogCap x.n0 * (x.n0 - (Finset.range x.n0).sum (fun i =>
      let v := mem (auxVListBase auxPtr x.vCap + i)
      if v < x.vCap then (if mem (fIsRootBase fAncPtr + v) = 1 then 1 else 0) else 0)) ≤
      500 * x.n0 * L := by
    calc 500 * auxLogCap x.n0 * _ ≤ 500 * L * x.n0 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 500 hlog_cap) hsub_le
      _ = 500 * x.n0 * L := by ring
  have hphiC : 1400 * mF ≤ 1400 * x.n0 * L := by
    have h1L : 1 ≤ L := by dsimp [L]; omega
    calc 1400 * mF ≤ 1400 * x.n0 := Nat.mul_le_mul_left 1400 hm
      _ = 1400 * x.n0 * 1 := (Nat.mul_one _).symm
      _ ≤ 1400 * x.n0 * L := Nat.mul_le_mul_left _ h1L
  let f : ℕ → ℕ := fun i =>
    let e := mem (dgEListBase dgFPtr x.vCap eCapF + i)
    if e < eCapF then
      let s := mem (dgETailSlotBase dgFPtr x.vCap eCapF + e)
      if s < x.vCap then
        let u := mem (dgIntToExtBase dgFPtr x.vCap + s)
        if u < x.vCap then
          let cid := mem (fCompIdBase fAncPtr x.vCap + u)
          if cid < x.vCap then
            Nat.log 2 (max 1 (mem (fCompSizeBase fAncPtr x.vCap + cid) - 1))
          else 0
        else 0
      else 0
    else 0
  have hrelab_term : ∀ i ∈ Finset.range (min mF eCapF), f i ≤ L := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    dsimp only [f]
    split_ifs with he hs hu hcid
    · have hle : max 1 (mem (fCompSizeBase fAncPtr x.vCap +
          mem (fCompIdBase fAncPtr x.vCap + mem (dgIntToExtBase dgFPtr x.vCap +
            mem (dgETailSlotBase dgFPtr x.vCap eCapF +
              mem (dgEListBase dgFPtr x.vCap eCapF + i))))) - 1) ≤ x.n0 + 2 := by
        have := hsz i hi' he hs hu hcid
        omega
      calc Nat.log 2 _ ≤ Nat.log 2 (x.n0 + 2) := Nat.log_mono_right hle
        _ ≤ L := Nat.le_succ _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hrelab_sum : (Finset.range (min mF eCapF)).sum f ≤ min mF eCapF * L := by
    calc (Finset.range (min mF eCapF)).sum f ≤ (Finset.range (min mF eCapF)).sum (fun _ => L) :=
          Finset.sum_le_sum hrelab_term
      _ = min mF eCapF * L := by simp
  have hphiRelab : 1100 * (Finset.range (min mF eCapF)).sum f ≤ 1100 * x.n0 * L := by
    calc 1100 * (Finset.range (min mF eCapF)).sum f ≤ 1100 * (min mF eCapF * L) :=
          Nat.mul_le_mul_left 1100 hrelab_sum
      _ ≤ 1100 * (x.n0 * L) :=
          Nat.mul_le_mul_left 1100 (Nat.mul_le_mul_right L (le_trans (Nat.min_le_left _ _) hm))
      _ = 1100 * x.n0 * L := by ring
  have htot : 500 * x.n0 * L + 1400 * x.n0 * L + 1100 * x.n0 * L ≤ 3000 * (x.n0 + 1) * L := by
    have : 500 * x.n0 * L + 1400 * x.n0 * L + 1100 * x.n0 * L = 3000 * x.n0 * L := by ring
    rw [this]
    exact Nat.mul_le_mul_right L (Nat.mul_le_mul_left 3000 (Nat.le_succ x.n0))
  exact (Nat.add_le_add (Nat.add_le_add hphiR hphiC) hphiRelab).trans htot

/-- Full `DSRep LSFState` representation predicate at handle `b` and limb width `h`. -/
def LSFRep (h : ℕ) : DSRep LSFState where
  τ := LSFConcrete
  rep b S x mem :=
    x.h = h ∧ 1 ≤ h ∧ 1 ≤ x.L_in ∧ 1 ≤ x.L_w ∧ 1 ≤ x.k_nat ∧
    S.k = (x.k_nat : ℝ) ∧
    LSFStructInv S ∧
    S.G₀.n = x.n0 ∧ S.G₀.E.card = x.m0 ∧ S.T₀.E.card = x.tM ∧
    x.n0 ≤ x.vCap ∧ x.m0 ≤ x.eCap ∧ x.tM ≤ x.n0 ∧ 1 ≤ x.n0 ∧
    (∀ v ∈ S.T₀.V, v < x.vCap) ∧
    (∀ e ∈ S.G₀.E, e < x.eCap) ∧
    lsfHeaderAt mem b S x ∧
    DynGraphAt mem (lsfDgGPtr b) x.vCap x.eCap S.G ∧
    TBlockAt mem (lsfTBlockPtr b x.vCap x.eCap) x.vCap x.eCap x.tM S.G S.T_cur S.T₀ S.π x.tOrigList ∧
    DynGraphAt mem (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0) S.RF.F ∧
    FAncAt mem (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap S.RF x.rList x.compId x.compRoot x.compSize x.activeCids ∧
    WBlockAt mem (lsfWBlockPtr b x.vCap x.eCap x.n0 x.tM) x.n0 S.W_init
      (forestGivenRoots S.T₀ S.r₀ (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ S.R₀_init) S.π) ∧
    WstrAt mem (lsfWstrNumPtr b x.vCap x.eCap x.n0 x.tM)
      (lsfWstrDenPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.eCap x.h x.L_w S.G S.wstr ∧
    AuxAt mem (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 x.tM S
      x.tOrigList x.vList x.t0Parent x.t0ParentTreeIdx x.t0Depth x.thParent x.upV x.upMinIdx
  phi := lsfPhi
  foot b x a := b ≤ a ∧ a < x.endAddr b

lemma lsfRep_local (h : ℕ) : (LSFRep h).Local := by
  intro b S x mem mem' hfoot
  have hagree : ∀ a, b ≤ a → a < x.endAddr b → mem a = mem' a :=
    fun a ha1 ha2 => hfoot a ⟨ha1, ha2⟩
  refine ⟨?_, lsfPhi_congr hagree⟩
  rintro ⟨hxH, hh1, hLin, hLw, hkn, hk, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvlt, helt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  have hagree_sym : ∀ a, b ≤ a → a < x.endAddr b → mem' a = mem a :=
    fun a ha1 ha2 => (hagree a ha1 ha2).symm
  have hrHdr := lsfHdr_lt_end b x.vCap x.eCap x.n0 x.tM x.L_w
  have hrDgG := lsfDgG_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
  have hrT := lsfTBlock_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
  have hrDgF := lsfDgF_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
  have hrFAnc := lsfFAnc_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
  have hrW := lsfWBlock_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
  have hrWstr := lsfWstr_sub_end b x.vCap x.eCap x.n0 x.tM x.L_w
  have hAuxEnd := lsfEndAddr_eq_aux_add b x.vCap x.eCap x.n0 x.tM x.L_w
  have hDgGGe : b ≤ lsfDgGPtr b := by dsimp [lsfDgGPtr]; omega
  have hTGe : b ≤ lsfTBlockPtr b x.vCap x.eCap := by dsimp [lsfTBlockPtr, lsfDgGPtr]; omega
  have hDgFGe : b ≤ lsfDgFPtr b x.vCap x.eCap x.tM := by dsimp [lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hFAncGe : b ≤ lsfFAncPtr b x.vCap x.eCap x.n0 x.tM := by
    dsimp [lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hWGe : b ≤ lsfWBlockPtr b x.vCap x.eCap x.n0 x.tM := by
    dsimp [lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hWstrNGe : b ≤ lsfWstrNumPtr b x.vCap x.eCap x.n0 x.tM := by
    dsimp [lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hWstrNLe : lsfWstrNumPtr b x.vCap x.eCap x.n0 x.tM + x.eCap * x.L_w ≤
      lsfEndAddr b x.vCap x.eCap x.n0 x.tM x.L_w := by
    dsimp [lsfEndAddr, lsfStaticSize, lsfWstrNumPtr, lsfWBlockPtr,
      lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hWstrDGe : b ≤ lsfWstrDenPtr b x.vCap x.eCap x.n0 x.tM x.L_w := by
    dsimp [lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hWstrDLe : lsfWstrDenPtr b x.vCap x.eCap x.n0 x.tM x.L_w + x.eCap * x.L_w ≤
      lsfEndAddr b x.vCap x.eCap x.n0 x.tM x.L_w := by
    dsimp [lsfEndAddr, lsfStaticSize, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr,
      lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hAuxGe : b ≤ lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w := by
    dsimp [lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr,
      lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  refine ⟨hxH, hh1, hLin, hLw, hkn, hk, hInv, hn0, hm0, htM, hnv, hme, htn, hn1, hvlt, helt, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hhdr.of_agree fun a ha1 ha2 => hagree_sym a ha1 (lt_of_lt_of_le ha2 hrHdr)
  · exact hdgG.of_agree fun a ha1 ha2 => hagree_sym a (le_trans hDgGGe ha1) (lt_of_lt_of_le ha2 hrDgG.2)
  · exact hT.of_agree fun a ha1 ha2 => hagree_sym a (le_trans hTGe ha1) (lt_of_lt_of_le ha2 hrT.2)
  · exact hdgF.of_agree fun a ha1 ha2 => hagree_sym a (le_trans hDgFGe ha1) (lt_of_lt_of_le ha2 hrDgF.2)
  · exact hFAnc.of_agree fun a ha1 ha2 => hagree_sym a (le_trans hFAncGe ha1) (lt_of_lt_of_le ha2 hrFAnc.2)
  · exact hW.of_agree fun a ha1 ha2 => hagree_sym a (le_trans hWGe ha1) (lt_of_lt_of_le ha2 hrW.2)
  · exact hwstr.of_agree
      (fun a ha1 ha2 => hagree_sym a (le_trans hWstrNGe ha1) (lt_of_lt_of_le ha2 hWstrNLe))
      (fun a ha1 ha2 => hagree_sym a (le_trans hWstrDGe ha1) (lt_of_lt_of_le ha2 hWstrDLe))
  · exact hAux.of_agree
      (fun a ha1 ha2 => hagree_sym a (le_trans hAuxGe ha1) (by dsimp [LSFConcrete.endAddr]; exact lt_of_lt_of_le ha2 hAuxEnd))
      hvlt

/-! ## `DataStructure LSFState` specification -/

/-- Canonical real edge weight/length function read from an `L_in`-limb array at `arr`. -/
noncomputable def memArrayReal (mem : ℕ → ℕ) (arr : ℕ) (G₀ : MGraph)
    (h L_in P_fp e : ℕ) : ℝ :=
  open Classical in
  if e ∈ G₀.E then Num.fixVal mem (arr + e * L_in) h L_in P_fp else 1

lemma memArrayReal_eq {mem : ℕ → ℕ} {arr : ℕ} {G₀ : MGraph} {h L_in P_fp e : ℕ}
    (he : e ∈ G₀.E) :
    memArrayReal mem arr G₀ h L_in P_fp e = Num.fixVal mem (arr + e * L_in) h L_in P_fp := by
  classical
  simp [memArrayReal, he]

/-- Explicit multiplicative constant on `(m₀ + n₀ + 1) * lsfOverhead` in `lsfInitCost`. -/
def lsfInitCostFactor : ℕ := 200000

/-- Explicit multiplicative constant on `(totalWords * L_w + 1)` in `lsfBatchCost`. -/
def lsfBatchCostFactor : ℕ := 10000

/-- Precondition for LSF `Initialize` (`[g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, b]`).
The word bound on `12 k (D + 1)` (`D = hldDepthBound n₀`) lets the program keep three times the
threshold `4 k (D + 1)` of the decomposition in one word. The edge capacity is at least `1`, so
that the stretch arrays leave room for the `L_w`-limb window of the decomposition phase even when
`G₀` has no edges. -/
def lsfInitPre (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ (G₀ : MGraph) (v ℓ₀ : ℕ → ℝ)
    (g0Ptr vCap0 eCap0 lenArr wtArr L_in P_fp k_nat L_w vCap eCap b : ℕ),
    args = [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, b] ∧
    1 ≤ c_AN ∧ 1 ≤ h ∧ 3 * h + 2 ≤ w ∧
    G₀.IsValid ∧ G₀.V.Nonempty ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧
    g0Ptr + dynGraphSize vCap0 eCap0 ≤ b ∧
    vCap0 ≤ vCap ∧ eCap0 ≤ eCap ∧ 1 ≤ eCap ∧
    lenArr + eCap0 * L_in ≤ b ∧ wtArr + eCap0 * L_in ≤ b ∧
    1 ≤ L_in ∧ 2 ≤ h * L_in ∧ h ∣ P_fp ∧ 1 ≤ k_nat ∧
    3 * (4 * k_nat * (hldDepthBound G₀.n + 1)) < 2 ^ w ∧
    L_in ≤ L_w ∧ 2 ≤ h * L_w ∧
    defaultThreshNat K_AN G₀.n k_nat < 2 ^ (h * (L_w - L_in)) ∧
    (∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧
      Num.fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) ∧
    (∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * L_in) h L_in ∧
      Num.fixVal mem (wtArr + e * L_in) h L_in P_fp = v e ∧ 0 < v e)

/-- Postcondition for LSF `Initialize`: builds a valid `initLSFWith` state matching `ValidLSFParams`
with `C_lsst = 4 * max K_AN 1 + 5`, `α = 5 / 4`, `thresh = defaultThreshNat K_AN G₀.n k_nat`,
`K_σ = defaultK_sigma K_AN`, and exact rational `WstrAt`. -/
def lsfInitPost (K_AN : ℝ) (h : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (s' : LSFState) (mem' : ℕ → ℕ) : Prop :=
  ∃ (G₀ : MGraph) (g0Ptr vCap0 eCap0 lenArr wtArr L_in P_fp k_nat L_w vCap eCap b : ℕ)
    (T_raw : MGraph) (C_reps : Finset ℕ) (W_T : Finset (Finset ℕ)),
    args = [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, b] ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧
    let v_mem := memArrayReal mem wtArr G₀ h L_in P_fp
    let ℓ₀_mem := memArrayReal mem lenArr G₀ h L_in P_fp
    ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
      (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
      G₀ ℓ₀_mem v_mem (k_nat : ℝ) T_raw s'.r₀ C_reps s'.π W_T ∧
    s' = initLSFWith G₀ ℓ₀_mem v_mem (k_nat : ℝ) T_raw s'.r₀ C_reps s'.π W_T
      (defaultThreshNat K_AN G₀.n k_nat : ℝ) ∧
    mem' (b + lsfOffVCap) = vCap ∧
    mem' (b + lsfOffECap) = eCap ∧
    mem' (b + lsfOffN0) = G₀.n ∧
    mem' (b + lsfOffM0) = G₀.E.card ∧
    mem' (b + lsfOffLW) = L_w ∧
    mem' (b + lsfOffWstrNumPtr) = lsfWstrNumPtr b vCap eCap G₀.n s'.T₀.E.card ∧
    mem' (b + lsfOffWstrDenPtr) = lsfWstrDenPtr b vCap eCap G₀.n s'.T₀.E.card L_w ∧
    WstrAt mem' (mem' (b + lsfOffWstrNumPtr)) (mem' (b + lsfOffWstrDenPtr))
      eCap h L_w s'.G s'.wstr

/-- Space budget above `b` consumed by `lsfInit`. Besides the static blocks it charges a scratch
copy of the two stretch arrays (`2 eCap L_w` words), the scratch of the `[AN19]` call, and the
work arrays of the other phases. -/
noncomputable def lsfInitSpace (Q_AN : Program) (K_AN : ℝ) (c_AN h : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let g0Ptr := args.getD 0 0
  let L_in := args.getD 3 0
  let L_w := args.getD 6 0
  let vCap := args.getD 7 0
  let eCap := args.getD 8 0
  let n0 := mem (g0Ptr + dgNOff)
  let m0 := mem (g0Ptr + dgMOff)
  let L_sim := lsstLSimMin c_AN n0 (2 * m0) L_in h
  lsfStaticSize vCap eCap n0 n0 L_w + 2 * (eCap * L_w) +
    lsstSpace Q_AN K_AN n0 (2 * m0) L_sim h +
    200 * (n0 + m0 + 1) * (L_w + L_sim + auxLogCap n0 + 20) + 1000

/-- Cost budget for `lsfInit` (including initial potential `lsfPhi`). It charges only the input
graph size `m₀ + n₀ + 1` times `lsfOverhead`, independent of `vCap` and `eCap`. -/
noncomputable def lsfInitCost (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let g0Ptr := args.getD 0 0
  let L_in := args.getD 3 0
  let L_w := args.getD 6 0
  let n0 := mem (g0Ptr + dgNOff)
  let m0 := mem (g0Ptr + dgMOff)
  lsfInitCostFactor *
    Nat.ceil (((m0 + n0 + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h)

/-- Precondition for LSF `ApplyBatch` (`op 0`, `[b, batchPtr, heap]`). -/
def lsfBatchPre (w : ℕ) (s : LSFState) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ b batchPtr heap U totalWords,
    args = [b, batchPtr, heap] ∧
    16 ≤ 2 ^ w ∧
    BatchAt mem batchPtr s.G U totalWords ∧
    s.G.BatchIsValid U ∧
    BatchWithinCaps (mem (b + lsfOffVCap)) (mem (b + lsfOffECap)) U ∧
    (∀ i < totalWords, mem (batchPtr + i) < 2 ^ w) ∧
    batchPtr + totalWords ≤ heap ∧
    (∀ i < totalWords, batchPtr + i < b ∨ mem (b + lsfOffEnd) ≤ batchPtr + i)

/-- Postcondition for LSF `ApplyBatch` (`op 0`). -/
def lsfBatchPost (s : LSFState) (args : List ℕ) (mem : ℕ → ℕ)
    (s' : LSFState) (_mem' : ℕ → ℕ) : Prop :=
  ∃ b batchPtr heap U totalWords,
    args = [b, batchPtr, heap] ∧
    BatchAt mem batchPtr s.G U totalWords ∧
    s' = applyLSFBatch s U

/-- Amortized cost bound for `op 0` (`lsfBatchCostFactor * (batchMemLen * L_w + 1)`). -/
def lsfBatchCost (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let b := args.getD 0 0
  let batchPtr := args.getD 1 0
  let L_w := mem (b + lsfOffLW)
  lsfBatchCostFactor * (batchMemLen mem batchPtr * L_w + 1)

/-- Full WordRAM data structure specification for Lemma 5.4 (`LSF`). -/
noncomputable def lsfDataStructure (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ) :
    DataStructure LSFState where
  initPre := lsfInitPre c_AN K_AN w h
  initPost := lsfInitPost K_AN h
  initCost := lsfInitCost Q_AN c_AN K_AN h
  initSpace := lsfInitSpace Q_AN K_AN c_AN h
  pre i s args mem := i = 0 ∧ lsfBatchPre w s args mem
  post i s args mem s' mem' := i = 0 ∧ lsfBatchPost s args mem s' mem'
  cost _ _ args mem := lsfBatchCost args mem
  space _ _ _ _ := 0

/-! ## Cost & parameter sanity lemmas -/

lemma lsfInitCost_le_linear (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) {h : ℕ} (hh : 1 ≤ h)
    (g0Ptr lenArr wtArr L_in P_fp k_nat L_w vCap eCap b : ℕ) (mem : ℕ → ℕ)
    {G₀ : MGraph} {vCap0 eCap0 : ℕ} (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) :
    let args := [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, b]
    (lsfInitCost Q_AN c_AN K_AN h args mem : ℝ) ≤
      (2 * lsfInitCostFactor : ℝ) * ((G₀.m + G₀.n + 1 : ℕ) : ℝ) *
        lsfOverhead Q_AN c_AN K_AN G₀.n G₀.m L_in L_w h := by
  intro args
  have hn : mem (g0Ptr + dgNOff) = G₀.n := hdg.2.2.2.2.2.1
  have hm : mem (g0Ptr + dgMOff) = G₀.m := hdg.2.2.2.2.2.2.1
  dsimp only [lsfInitCost, args]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [hn, hm]
  set F := lsfOverhead Q_AN c_AN K_AN G₀.n G₀.m L_in L_w h
  have hF1 : 1 ≤ F := lsfOverhead_ge_one Q_AN c_AN K_AN G₀.n G₀.m L_in L_w h hh
  set X : ℝ := ((G₀.m + G₀.n + 1 : ℕ) : ℝ) * F
  have h1X : 1 ≤ X := by
    have hmn1 : (1 : ℝ) ≤ ((G₀.m + G₀.n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ G₀.m + G₀.n + 1)
    nlinarith
  have hceil : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
  have hceil2 : (Nat.ceil X : ℝ) ≤ 2 * X := by linarith
  dsimp only [X] at hceil2
  push_cast
  have hf_nn : (0 : ℝ) ≤ (lsfInitCostFactor : ℝ) := Nat.cast_nonneg _
  have hmul : (lsfInitCostFactor : ℝ) * (Nat.ceil X : ℝ) ≤ (lsfInitCostFactor : ℝ) * (2 * (((G₀.m + G₀.n + 1 : ℕ) : ℝ) * F)) :=
    mul_le_mul_of_nonneg_left hceil2 hf_nn
  push_cast at hmul ⊢
  linarith [hmul, show (lsfInitCostFactor : ℝ) * (2 * (((G₀.m : ℝ) + (G₀.n : ℝ) + 1) * F)) =
    2 * (lsfInitCostFactor : ℝ) * ((G₀.m : ℝ) + (G₀.n : ℝ) + 1) * F by ring]

lemma lsfBatchCost_le_smallBatch {b batchPtr heap L_w : ℕ} {mem : ℕ → ℕ}
    {S : LSFState} {U : List Update} {totalWords : ℕ}
    (hLw : mem (b + lsfOffLW) ≤ L_w)
    (hSB : SmallBatchAt mem batchPtr S.G U totalWords)
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {n0 m0 L_in h : ℕ}
    (hh : 1 ≤ h) :
    (lsfBatchCost [b, batchPtr, heap] mem : ℝ) ≤
      (6 * lsfBatchCostFactor : ℝ) * ((S.G.batchEnc U + 1 : ℕ) : ℝ) *
        lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h := by
  have hlen := batchMemLen_eq hSB.1
  dsimp only [lsfBatchCost]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [hlen]
  have h1 : totalWords ≤ 5 * S.G.batchEnc U + 1 := hSB.2
  have hprod : totalWords * mem (b + lsfOffLW) + 1 ≤ 6 * (S.G.batchEnc U + 1) * max 1 L_w := by
    have hmax : 1 ≤ max 1 L_w := le_max_left 1 L_w
    calc totalWords * mem (b + lsfOffLW) + 1
        ≤ (5 * S.G.batchEnc U + 1) * L_w + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul h1 hLw) 1
      _ ≤ (5 * S.G.batchEnc U + 1) * max 1 L_w + max 1 L_w :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_right _ _)) hmax
      _ ≤ 6 * (S.G.batchEnc U + 1) * max 1 L_w := by nlinarith
  have hF1 : 1 ≤ lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h :=
    lsfOverhead_ge_one Q_AN c_AN K_AN n0 m0 L_in L_w h hh
  have hLw2 : (L_w : ℝ) ^ 2 ≤ lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h :=
    (lsfOverhead_bounds Q_AN c_AN K_AN n0 m0 L_in L_w h hh).2.2.1
  have hmax_le : ((max 1 L_w : ℕ) : ℝ) ≤ lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h := by
    by_cases h0 : L_w = 0
    · have hm1 : max 1 L_w = 1 := by omega
      rw [hm1, Nat.cast_one]
      exact hF1
    · have hL1 : (1 : ℝ) ≤ (L_w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hmax_eq : max 1 L_w = L_w := max_eq_right (Nat.pos_of_ne_zero h0)
      rw [hmax_eq]
      nlinarith
  have hreal : ((totalWords * mem (b + lsfOffLW) + 1 : ℕ) : ℝ) ≤
      (6 * (S.G.batchEnc U + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h := by
    calc ((totalWords * mem (b + lsfOffLW) + 1 : ℕ) : ℝ)
        ≤ ((6 * (S.G.batchEnc U + 1) * max 1 L_w : ℕ) : ℝ) := by exact_mod_cast hprod
      _ = (6 * (S.G.batchEnc U + 1 : ℕ) : ℝ) * ((max 1 L_w : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (6 * (S.G.batchEnc U + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h :=
          mul_le_mul_of_nonneg_left hmax_le (by positivity)
  have hcf : (0 : ℝ) ≤ (lsfBatchCostFactor : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hreal hcf
  push_cast at hmul ⊢
  linarith [hmul, show (lsfBatchCostFactor : ℝ) * (6 * ((S.G.batchEnc U : ℝ) + 1) *
      lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h) =
    6 * (lsfBatchCostFactor : ℝ) * ((S.G.batchEnc U : ℝ) + 1) *
      lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h by ring]

end MinCostFlow.LSF.Program
