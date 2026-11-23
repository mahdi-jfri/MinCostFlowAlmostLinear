module

public import MinCostFlow.SparseCore.SplitTrace
public import MinCostFlow.MinRatio.SelectBlocksSplit
public import MinCostFlow.MinRatio.WireSelectSplitPot
public import MinCostFlow.MinRatio.WireSelectActiveS

import MinCostFlow.Chain.BundleRestartBun
import MinCostFlow.Chain.BundleRestartMach
import MinCostFlow.Chain.Ordered.BudgetHelpers
import MinCostFlow.SparseCore.CanonCoreValid

/-!
# Frozen potentials and surviving-edge ends across `Update` (`WireSelectSplitPotModel`)

Connects the vertex-split trace engine (`SparseCore/SplitTrace.lean`) to `SelectBlocksSplit.splitPot`,
`WireSelectSplitPot.endPotAgree_of_split`, and `SelectPotInv` on non-rebuilt levels of an `Update`:

1. **`splitPot` across `SplitsValid` and `SplitTrace`:**
   * `splitPot_old_of_splitsValid` / `splitPot_old_of_batchIsValid`: `splitPot` preserves the
     potential of every vertex present before a valid batch.
   * `splitPot_of_splitTrace` / `splitPot_of_batchIsValid_splitTrace`: if vertex `a ∈ G.V` traces
     to `b` along `batchSplits U` (including chained splits `v ↦ v' ↦ v''`), then
     `splitPot φj (batchSplits U) b = φj a`.
2. **Per-level `SelectPotInv` preservation from `EndPotAgree` (`selectPotInvAt_of_endPotAgree`):**
   * On any level `j` whose active forest only loses edges (`(C'.activeLSF j).F.F.E ⊆
     (C.activeLSF j).F.F.E`), if `EndPotAgree C C' φ φ' j` holds and surviving edges of `G_0`
     keep their gradient `g' f = g f`, then `SelectPotInvAt C' g' φ' j` follows directly from
     `SelectPotInv C g φ`.
3. **Non-rebuilt prefix of `Update` on `sparseCoreProgTool` (`NonRebuiltBatches`):**
   * `progTool_nonRebuilt_splitTrace`: for every level `j ≤ i` in a non-rebuilt prefix, every
     surviving edge of `G_j` traces its tail and head along `batchSplits (U j)` (even when
     `buildUSOrd` re-inserts `D_reins` edges).
   * `progTool_nonRebuilt_endPotAgree`: delivers the exact premises of `endPotAgree_of_split`
     together with `EndPotAgree st.toTreeChain st'.toTreeChain φ φ' i` when
     `φ' j = splitPot (φ j) (batchSplits (U j))`.
   * `progTool_nonRebuilt_selectPotInv`: preserves `SelectPotInvAt` on all non-rebuilt levels
     `j ≤ i` (and full `SelectPotInv` when rebuilt levels `j > i` are freshly filled).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-! ## 1. `splitPot` across `SplitsValid` and `SplitTrace` -/

/-- On every vertex `u ∈ V` before a valid split sequence `splits`, `splitPot` keeps `φj u`. -/
theorem splitPot_old_of_splitsValid {V : Finset ℕ} {splits : List (ℕ × ℕ)}
    (hV : SplitsValid V splits) (φj : ℕ → ℝ) {u : ℕ} (hu : u ∈ V) :
    splitPot φj splits u = φj u := by
  induction splits generalizing V φj with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨v, v'⟩ := s
    obtain ⟨_, hv'_not, hrest⟩ := hV
    have hne : u ≠ v' := fun h => hv'_not (h ▸ hu)
    simp only [splitPot]
    rw [ih hrest _ (Finset.mem_insert_of_mem hu), Function.update_of_ne hne]

/-- Along any valid split sequence `splits` from `V`, if `a ∈ V` traces to `b` (`SplitTrace`),
including chained splits `v ↦ v' ↦ v''`, then `splitPot φj splits b = φj a`. -/
theorem splitPot_of_splitTrace {V : Finset ℕ} {splits : List (ℕ × ℕ)}
    (hV : SplitsValid V splits) (φj : ℕ → ℝ) {a b : ℕ} (ha : a ∈ V)
    (htr : SplitTrace splits a b) :
    splitPot φj splits b = φj a := by
  induction htr generalizing V φj with
  | nil _ => rfl
  | @stay v v' rest a b hrest ih =>
    obtain ⟨_, hv'_not, hVrest⟩ := hV
    have hne : a ≠ v' := fun h => hv'_not (h ▸ ha)
    simp only [splitPot]
    rw [ih hVrest _ (Finset.mem_insert_of_mem ha), Function.update_of_ne hne]
  | @step v v' rest b hrest ih =>
    obtain ⟨_, _, hVrest⟩ := hV
    simp only [splitPot]
    rw [ih hVrest _ (Finset.mem_insert_self v' V), Function.update_self]

/-- On every vertex `u ∈ G.V` before a valid batch `U`, `splitPot φj (batchSplits U) u = φj u`. -/
theorem splitPot_old_of_batchIsValid {G : MGraph} {U : List Update} (hB : G.BatchIsValid U)
    (φj : ℕ → ℝ) {u : ℕ} (hu : u ∈ G.V) :
    splitPot φj (batchSplits U) u = φj u :=
  splitPot_old_of_splitsValid (SplitsValid.of_batchIsValid hB) φj hu

/-- If `a ∈ G.V` traces to `b` along `batchSplits U` for a valid batch `U`, then
`splitPot φj (batchSplits U) b = φj a`. -/
theorem splitPot_of_batchIsValid_splitTrace {G : MGraph} {U : List Update} (hB : G.BatchIsValid U)
    (φj : ℕ → ℝ) {a b : ℕ} (ha : a ∈ G.V) (htr : SplitTrace (batchSplits U) a b) :
    splitPot φj (batchSplits U) b = φj a :=
  splitPot_of_splitTrace (SplitsValid.of_batchIsValid hB) φj ha htr

/-! ## 2. Per-level `SelectPotInv` preservation from `EndPotAgree` -/

/-- The single-level clause of `SelectPotInv` at level `j`. -/
def SelectPotInvAt (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) (j : ℕ) : Prop :=
  ∀ a b, (C.activeLSF j).F.F.Connected a b →
    walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath a b) = φ j a - φ j b

theorem selectPotInv_iff_at (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) :
    SelectPotInv C g φ ↔ ∀ j ≤ C.d, SelectPotInvAt C g φ j :=
  Iff.rfl

private theorem potGrad_eq_sub_of_selectPotInvAt {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ}
    {j : ℕ} (hF : (C.activeLSF j).F.F.IsForest) (hPot : SelectPotInvAt C g φ j)
    {f : ℕ} (hf : f ∈ (C.activeLSF j).F.F.E) :
    potGrad C g φ j f =
      φ j ((C.activeLSF j).F.F.tail f) - φ j ((C.activeLSF j).F.F.head f) := by
  let F := (C.activeLSF j).F.F
  have hW : F.IsWalk (F.tail f) (F.head f) [(f, true)] :=
    MGraph.IsWalk.cons hf rfl (MGraph.IsWalk.nil _)
  have hconn : F.Connected (F.tail f) (F.head f) := ⟨[(f, true)], hW⟩
  have hflow : ∀ e, walkFlow (F.forestPath (F.tail f) (F.head f)) e = walkFlow [(f, true)] e :=
    walkFlow_eq_of_isForest hF (MGraph.isWalk_forestPath hconn) hW
  have hinner := walkInner_eq_of_walkFlow_eq (potGrad C g φ j) hflow
  rw [walkInner_singleton] at hinner
  simp only [↓reduceIte] at hinner
  rw [← hinner]
  exact hPot (F.tail f) (F.head f) hconn

private theorem walkInner_eq_sub_of_edge_pot {F : MGraph} {h φ : ℕ → ℝ}
    (hEdge : ∀ f ∈ F.E, h f = φ (F.tail f) - φ (F.head f))
    {a b : ℕ} {W : List (ℕ × Bool)} (hW : F.IsWalk a b W) :
    walkInner h W = φ a - φ b := by
  induction hW with
  | nil u => simp [walkInner_nil]
  | @cons u w x rest hxE hsrc hrest ih =>
    rw [walkInner_cons, ih]
    have hstep : walkInner h [x] = φ u - φ (F.dst x) := by
      cases hx2 : x.2
      · simp only [walkInner_singleton, hx2, Bool.false_eq_true, ↓reduceIte, hEdge x.1 hxE]
        have h1 : F.head x.1 = u := by simpa [MGraph.src, hx2] using hsrc
        have h2 : F.dst x = F.tail x.1 := by simp [MGraph.dst, hx2]
        rw [h1, h2]; ring
      · simp only [walkInner_singleton, hx2, ↓reduceIte, hEdge x.1 hxE]
        have h1 : F.tail x.1 = u := by simpa [MGraph.src, hx2] using hsrc
        have h2 : F.dst x = F.head x.1 := by simp [MGraph.dst, hx2]
        rw [h1, h2]
    rw [hstep]; ring

/-- **Per-level `SelectPotInv` preservation across vertex splits.**
At any level `j` whose active forest only loses edges (`hFsub`), if `EndPotAgree C C' φ φ' j`
holds and surviving edges of `G_0` keep their gradient (`hgEq`), then `SelectPotInvAt C' g' φ' j`
follows from `SelectPotInv C g φ`. -/
theorem selectPotInvAt_of_endPotAgree {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ} {φ φ' : ℕ → ℕ → ℝ} {j : ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hj : j ≤ C.d) (hj' : j ≤ C'.d)
    (hPot : SelectPotInv C g φ)
    (hEP : EndPotAgree C C' φ φ' j)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (hFsub : (C'.activeLSF j).F.F.E ⊆ (C.activeLSF j).F.F.E) :
    SelectPotInvAt C' g' φ' j := by
  have hRF := (C.activeLSF_holds hH hj).2.1
  have hRF' := (C'.activeLSF_holds hH' hj').2.1
  have hSubG := hRF.2.2.2.2
  have hSubG' := hRF'.2.2.2.2
  have hEdge : ∀ f ∈ (C'.activeLSF j).F.F.E,
      potGrad C' g' φ' j f =
        φ' j ((C'.activeLSF j).F.F.tail f) - φ' j ((C'.activeLSF j).F.F.head f) := by
    intro f hf'
    have hf : f ∈ (C.activeLSF j).F.F.E := hFsub hf'
    have hfG : f ∈ (C.G j).E := hSubG.2.1 hf
    have hfG' : f ∈ (C'.G j).E := hSubG'.2.1 hf'
    have hpg : potGrad C' g' φ' j f = potGrad C g φ j f := by
      cases j with
      | zero => exact hgEq f hfG' hfG
      | succ k =>
        have hk : k ≤ C.d := Nat.le_of_lt hj
        have hk' : k ≤ C'.d := Nat.le_of_lt hj'
        have hEPk : EndPotAgree C C' φ φ' k := fun m hm => hEP m (Nat.le_succ_of_le hm)
        have hfk : f ∈ (C.G k).E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hj hfG)).1
        have hfk' : f ∈ (C'.G k).E := (Finset.mem_sdiff.mp (C'.G_succ_E_subset hH' hj' hfG')).1
        exact potGrad_eq_of_endPotAgree hH hH' hk hk' hEPk hgEq hfk' hfk
    have hOld := potGrad_eq_sub_of_selectPotInvAt hRF.1 (hPot j hj) hf
    have hEnds := hSubG.2.2 f hf
    have hEnds' := hSubG'.2.2 f hf'
    have hAg := hEP j le_rfl f hfG' hfG
    rw [hpg, hOld, hEnds.1, hEnds.2, hEnds'.1, hEnds'.2, hAg.1, hAg.2]
  intro a b hconn
  exact walkInner_eq_sub_of_edge_pot hEdge (MGraph.isWalk_forestPath hconn)

/-- Combine `selectPotInvAt_of_endPotAgree` on non-rebuilt levels `j ≤ i` with fresh potentials
on rebuilt levels `j > i` to obtain full `SelectPotInv C' g' φ'`. -/
theorem selectPotInv_of_prefix_and_suffix {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ} {φ φ' : ℕ → ℕ → ℝ} {i : ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hd : C.d = C'.d) (_hi : i ≤ C'.d)
    (hPot : SelectPotInv C g φ)
    (hEP : EndPotAgree C C' φ φ' i)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (hFsub : ∀ j ≤ i, (C'.activeLSF j).F.F.E ⊆ (C.activeLSF j).F.F.E)
    (hRebuilt : ∀ j, i < j → j ≤ C'.d → SelectPotInvAt C' g' φ' j) :
    SelectPotInv C' g' φ' := by
  intro j hj
  by_cases hji : j ≤ i
  · have hEPj : EndPotAgree C C' φ φ' j := fun m hm => hEP m (le_trans hm hji)
    exact selectPotInvAt_of_endPotAgree hH hH' (hd ▸ hj) hj hPot hEPj hgEq (hFsub j hji)
  · exact hRebuilt j (Nat.lt_of_not_ge hji) hj

/-! ## 3. Non-rebuilt prefix of `Update` on `sparseCoreProgTool` -/

/-- Describes a prefix `0, …, i` of levels that were not rebuilt between chain states `st` and
`st'`, together with the per-level update batches `U 0, …, U i` entering each level. -/
def NonRebuiltBatches (T : SparseCoreRestartTool) {P : ChainParams}
    (st st' : ChainState T P) (U : ℕ → List Update) (i : ℕ) : Prop :=
  i ≤ P.d ∧
  NoBatchReinsert (st.G 0) (U 0) ∧
  (∀ j ≤ i, st'.G j = (st.G j).applyBatch (U j) ∧ (st.G j).BatchIsValid (U j)) ∧
  (∀ j ≤ i, j < P.d →
    st'.bran j = st.bran j ∧
    ∃ ℓj gj ordj,
      st'.scState j = (T.updateOrd (st.scState j) (U j) ℓj gj ordj).1 ∧
      (j + 1 ≤ i → U (j + 1) = (T.updateOrd (st.scState j) (U j) ℓj gj ordj).2 (st.bran j))) ∧
  (i = P.d → U P.d = [] ∧ st'.lastLSFs = st.lastLSFs ∧ st'.lastBran = st.lastBran)

private theorem foldl_restart_S_cur_V {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (j : ℕ) :
    ∀ (rs : List ℕ) (st : SparseCoreBundleState L),
      (st.trees j).S_cur.V = (st.trees j).cs.RF.R →
      let st' : SparseCoreBundleState L :=
        rs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st
      (st'.trees j).S_cur.V = (st'.trees j).cs.RF.R
  | [], _, h => h
  | r :: rs, st, h => by
    dsimp only [List.foldl_cons]
    apply foldl_restart_S_cur_V sparsify j rs
    dsimp only [sparseCoreBundleRestartToolWith]
    by_cases hne : st.isNonempty = true
    · simp only [hne, ↓reduceIte]
      by_cases hjr : j = r
      · subst hjr; simp [restartBundleTree]
      · simp [hjr, h]
    · simp [hne, h]

private theorem machTool_runOrdAfterRestarts_compLSFInv {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N τ : ℕ) (hk : 1 ≤ k)
    (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord) {j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    (hne : SparseCoreBundleState.isNonempty (L := L)
      ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).runOrdAfterRestarts
        k M N D ord restarts τ) = true) :
    let st : SparseCoreBundleState L :=
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).runOrdAfterRestarts
        k M N D ord restarts τ
    CompLSFInv C_lsst (D.ℓ 0) (st.trees j).cs ∧ (st.trees j).cs.G = D.G τ ∧
      (st.trees j).S_cur.V = (st.trees j).cs.RF.R := by
  intro st
  set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L
    sparsify params spanConst k M N D ord restarts τ).2.2
  have hV₀ : (D.G 0).V.Nonempty := by
    have h1 := (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify
      k M N D ord restarts τ).2.1
    change (Tb.runOrdAfterRestarts k M N D ord restarts τ).isNonempty = decide (D.G 0).V.Nonempty at h1
    rw [← hNM.isNonempty, hne] at h1
    exact of_decide_eq_true h1.symm
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hS_V_all : ∀ t ≤ τ,
      ((Tb.runOrdAfterRestarts k M N D ord restarts t).trees j).S_cur.V =
        ((Tb.runOrdAfterRestarts k M N D ord restarts t).trees j).cs.RF.R := by
    intro t
    induction t with
    | zero =>
      intro _
      apply foldl_restart_S_cur_V sparsify j (restarts 0)
      change ((initBundleCoreWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0)).trees j).S_cur.V =
        ((initBundleCoreWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0)).trees j).cs.RF.R
      simp [initBundleCoreWith, initBundleCoreWithParams, initBundleTreeWithParams, hV₀]
    | succ s ih =>
      intro hs1
      have hs : s ≤ τ := Nat.le_of_succ_le hs1
      apply foldl_restart_S_cur_V sparsify j (restarts (s + 1))
      have hne_s : (Tb.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true :=
        (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
          (decide_eq_true hV₀)
      have hBun_s := hBun s hs
      have hbf_s : BundleBaseFieldsEq
          ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
          ((Tb.runOrdAfterUpdate k M N D ord restarts s).1.trees j) :=
        (foldl_bundleRestart_props lsfInit C_lsst L sparsify
          (Tb.runOrdAfterUpdate k M N D ord restarts s).1 (restarts s)).2.2.2.2.1 j
      have hI_s : CompLSFInv C_lsst (D.ℓ 0) ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).cs :=
        hbf_s.cs ▸ hBun_s.2.2.2.2.2.2.2.1
      have hG_s : ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).cs.G = D.G s :=
        hbf_s.cs ▸ hBun_s.2.2.2.2.2.2.2.2.1
      have hB_s : ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).cs.G.BatchIsValid (D.U (s + 1)) :=
        hG_s.symm ▸ (hD (s + 1) (Nat.succ_pos s) hs1).1
      change ((updateBundleCore sparsify (Tb.runOrdAfterRestarts k M N D ord restarts s)
          (D.U (s + 1)) (ord (s + 1))).1.trees j).S_cur.V =
        ((updateBundleCore sparsify (Tb.runOrdAfterRestarts k M N D ord restarts s)
          (D.U (s + 1)) (ord (s + 1))).1.trees j).cs.RF.R
      simp only [updateBundleCore, hne_s, ↓reduceIte, stepBundleTree, coreBatchOf_eq]
      exact buildUSOrd_applyBatch_V hI_s hB_s (ih hs) _ _
  set pre := (Tb.runOrdAfterUpdate k M N D ord restarts τ).1.trees j
  set post := (Tb.runOrdAfterRestarts k M N D ord restarts τ).trees j
  have hbf : BundleBaseFieldsEq post pre :=
    (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (Tb.runOrdAfterUpdate k M N D ord restarts τ).1 (restarts τ)).2.2.2.2.1 j
  have hEq : BundleNonMachEq (st.trees j) post := hNM.trees j
  have hcs : (st.trees j).cs = pre.cs := hEq.cs.trans hbf.cs
  refine ⟨?_, ?_, ?_⟩
  · rw [hcs]; exact (hBun τ le_rfl).2.2.2.2.2.2.2.1
  · rw [hcs]; exact (hBun τ le_rfl).2.2.2.2.2.2.2.2.1
  · rw [hEq.S_cur, hEq.cs]; exact hS_V_all τ le_rfl

/-- Extract `CompLSFInv`, `cs.G = st.G j`, and `S_cur.V = cs.RF.R` at a nonempty level `j < P.d`
of `ChainInv`. -/
theorem progTool_chainInv_level_compLSFInv {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ}
    {st : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    {j : ℕ} (hj : j < P.d) (hne : (st.scState j).isNonempty = true) :
    ∃ ℓ₀ : ℕ → ℝ,
      CompLSFInv C_lsst ℓ₀ ((st.scState j).trees (st.bran j)).cs ∧
      ((st.scState j).trees (st.bran j)).cs.G = st.G j ∧
      ((st.scState j).trees (st.bran j)).S_cur.V = ((st.scState j).trees (st.bran j)).cs.RF.R := by
  obtain ⟨H⟩ := hInv.hHist j hj
  have hne' : SparseCoreBundleState.isNonempty (L := depth)
      ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl)).runOrdAfterRestarts P.k (levelM TP P j) N₀
        H.D H.ord H.restarts H.len) = true :=
    H.hRun ▸ hne
  have hRes := machTool_runOrdAfterRestarts_compLSFInv (lsfInit := lsfInit) (C_lsst := C_lsst)
    (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)
    P.k (levelM TP P j) N₀ H.len P.hk H.D H.ord H.restarts H.hG0 (H.hℓPos 0 (Nat.zero_le _))
    H.hD H.hOrd (hInit (st.bran j) (hInv.hBran j hj)) hne'
  refine ⟨H.D.ℓ 0, ?_, ?_, ?_⟩
  · exact H.hRun.symm ▸ hRes.1
  · exact (H.hRun.symm ▸ hRes.2.1).trans H.hEndG
  · exact H.hRun.symm ▸ hRes.2.2

/-- **Vertex-split trace on surviving edges across a non-rebuilt prefix.**
For `T = sparseCoreProgTool`, at every non-rebuilt level `j ≤ i`, every surviving edge
`f ∈ (st'.G j).E ∩ (st.G j).E` traces both its tail and its head along `batchSplits (U j)`
(even if `buildUSOrd` deletes and re-inserts `f` via `D_reins`). -/
theorem progTool_nonRebuilt_splitTrace {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hH : st.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH' : st'.toTreeChain.Holds G₀' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i) :
    ∀ j ≤ i, ∀ f ∈ (st'.G j).E, f ∈ (st.G j).E →
      SplitTrace (batchSplits (U j)) ((st.G j).tail f) ((st'.G j).tail f) ∧
      SplitTrace (batchSplits (U j)) ((st.G j).head f) ((st'.G j).head f) := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  obtain ⟨hi_d, hNR₀, hGB, hStep, _⟩ := hNR
  intro j
  induction j with
  | zero =>
    intro hj f hf' hf
    obtain ⟨hG0eq, hB0⟩ := hGB 0 hj
    rw [hG0eq] at hf' ⊢
    exact applyBatch_splitTrace_of_noInsert hB0 hf hf' (hNR₀ f hf)
  | succ k ih =>
    intro hk1 f hf' hf
    have hk : k ≤ i := Nat.le_of_succ_le hk1
    have hkd : k < P.d := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_trans hk1 hi_d)
    obtain ⟨hbr, ℓk, gk, ordk, hsc', hU1⟩ := hStep k hk hkd
    have hUsucc : U (k + 1) = (T.updateOrd (st.scState k) (U k) ℓk gk ordk).2 (st.bran k) :=
      hU1 hk1
    have hGk : st.G (k + 1) = T.S (st.scState k) (st.bran k) := hInv.hGSucc k hkd
    have hGk' : st'.G (k + 1) = T.S (st'.scState k) (st'.bran k) := by
      have := (hH'.2.2.2.2.1 k hkd).2.2.2
      simpa [ChainState.toTreeChain] using this
    by_cases hne : (st.scState k).isNonempty = true
    · obtain ⟨ℓ₀, hI, hcsG, _⟩ := progTool_chainInv_level_compLSFInv hInv hInit hkd hne
      have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState k) hne (U k) ℓk gk ordk
      have hne' : (st'.scState k).isNonempty = true := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
      let tr := (st.scState k).trees (st.bran k)
      let info := stepBundleTree (fun _ => canonicalSparsify impl) tr (U k) (st.scState k).ord ordk
      have hS_eq : st.G (k + 1) = tr.S_cur := by
        rw [hGk]; exact progTool_S_of_nonempty (st.scState k) hne (st.bran k)
      have hS'_eq : st'.G (k + 1) = info.state.S_cur := by
        rw [hGk', hbr, progTool_S_of_nonempty _ hne', hsc']
        change ((T.updateOrd (st.scState k) (U k) ℓk gk ordk).1.trees (st.bran k)).S_cur = _
        rw [hup]
      have hUS_eq : U (k + 1) = info.U_S := by
        rw [hUsucc, hup]
      have hL_eq : tr.cs.lsf = st.toTreeChain.activeLSF k := by
        simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte]
        change tr.cs.lsf = if (st.scState k).isNonempty then tr.cs.lsf else emptyLSF
        simp [hne]
      have hL'_eq : (compLSFBatch tr.cs (U k)).lsf = st'.toTreeChain.activeLSF k := by
        simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte, hbr]
        change (compLSFBatch tr.cs (U k)).lsf =
          if (st'.scState k).isNonempty then ((st'.scState k).trees (st.bran k)).cs.lsf else emptyLSF
        rw [ite_eq_left hne', hsc']
        change _ = ((T.updateOrd (st.scState k) (U k) ℓk gk ordk).1.trees (st.bran k)).cs.lsf
        rw [hup]; rfl
      have hS_sub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur := by
        have hSp := ((hH.2.2.2.2.1 k hkd).2.1 (st.bran k) (hInv.hBran k hkd)).2.1
        rw [← hS_eq, hcsG, hL_eq]
        simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hGk] using hSp
      have hcsG' : (compLSFBatch tr.cs (U k)).G = st'.G k := by
        rw [compLSFBatch_G, hcsG, (hGB k hk).1]
      have hS_sub' : (coreGraph (compLSFBatch tr.cs (U k)).G (compLSFBatch tr.cs (U k)).lsf).IsSubgraph
          info.state.S_cur := by
        have hbr' : st'.bran k < st'.toTreeChain.k := (hH'.2.2.2.2.1 k hkd).1
        have hSp' := ((hH'.2.2.2.2.1 k hkd).2.1 (st'.bran k) hbr').2.1
        rw [← hS'_eq, hcsG', hL'_eq]
        simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hGk'] using hSp'
      have hfTr : f ∈ tr.S_cur.E := hS_eq ▸ hf
      have hfTr' : f ∈ info.state.S_cur.E := hS'_eq ▸ hf'
      have hfGk : f ∈ (st.G k).E := hcsG ▸ (Finset.mem_sdiff.mp (hS_sub.2.1 hfTr)).1
      have hfGk' : f ∈ (st'.G k).E := hcsG' ▸ (Finset.mem_sdiff.mp (hS_sub'.2.1 hfTr')).1
      obtain ⟨htk, hhk⟩ := ih hk f hfGk' hfGk
      have hB_tr : tr.cs.G.BatchIsValid (U k) := hcsG.symm ▸ (hGB k hk).2
      have hRes := stepBundleTree_S_cur_splitTrace (fun _ => canonicalSparsify impl) hI hB_tr
        hS_sub hS_sub' hfTr hfTr' (by rwa [hcsG, hcsG']) (by rwa [hcsG, hcsG'])
      rw [hS_eq, hS'_eq, hUS_eq]
      exact hRes
    · have hf_empty : (st.G (k + 1)).E = ∅ := by
        rw [hGk]
        change (if (st.scState k).isNonempty then _ else emptyGraph).E = ∅
        simp [Bool.eq_false_iff.mpr hne, emptyGraph]
      rw [hf_empty] at hf
      exact absurd hf (Finset.notMem_empty f)

/-- **The vertex-split trace, in the exact form `endPotAgree_of_split` asks.**
With `φ' j = splitPot (φ j) (batchSplits (U j))` on every non-rebuilt level `j ≤ i`, all four
premises of `endPotAgree_of_split` hold, yielding `EndPotAgree st.toTreeChain st'.toTreeChain φ φ' i`. -/
theorem progTool_nonRebuilt_endPotAgree {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ} {φ φ' : ℕ → ℕ → ℝ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hH : st.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH' : st'.toTreeChain.Holds G₀' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i)
    (hPhi : ∀ j ≤ i, φ' j = splitPot (φ j) (batchSplits (U j))) :
    (∀ j ≤ i, (st.toTreeChain.G j).IsValid) ∧
    (∀ j ≤ i, ∀ v ∈ (st.toTreeChain.G j).V, φ' j v = φ j v) ∧
    (∀ j ≤ i, ∀ f ∈ (st'.toTreeChain.G j).E, f ∈ (st.toTreeChain.G j).E →
      ((st'.toTreeChain.G j).tail f = (st.toTreeChain.G j).tail f ∨
        φ' j ((st'.toTreeChain.G j).tail f) = φ j ((st.toTreeChain.G j).tail f)) ∧
      ((st'.toTreeChain.G j).head f = (st.toTreeChain.G j).head f ∨
        φ' j ((st'.toTreeChain.G j).head f) = φ j ((st.toTreeChain.G j).head f))) ∧
    EndPotAgree st.toTreeChain st'.toTreeChain φ φ' i := by
  have hTr := progTool_nonRebuilt_splitTrace hInv hH hH' hInit hNR
  have hValid : ∀ j ≤ i, (st.toTreeChain.G j).IsValid := fun j hj =>
    st.toTreeChain.G_isValid hH j (le_trans hj hNR.1)
  have hOld : ∀ j ≤ i, ∀ v ∈ (st.toTreeChain.G j).V, φ' j v = φ j v := fun j hj v hv => by
    rw [hPhi j hj]
    exact splitPot_old_of_batchIsValid (hNR.2.2.1 j hj).2 (φ j) hv
  have hEnds : ∀ j ≤ i, ∀ f ∈ (st'.toTreeChain.G j).E, f ∈ (st.toTreeChain.G j).E →
      φ' j ((st'.toTreeChain.G j).tail f) = φ j ((st.toTreeChain.G j).tail f) ∧
      φ' j ((st'.toTreeChain.G j).head f) = φ j ((st.toTreeChain.G j).head f) := by
    intro j hj f hf' hf
    obtain ⟨ht, hh⟩ := hTr j hj f hf' hf
    have hV := hValid j hj f hf
    rw [hPhi j hj]
    exact ⟨splitPot_of_batchIsValid_splitTrace (hNR.2.2.1 j hj).2 (φ j) hV.1 ht,
      splitPot_of_batchIsValid_splitTrace (hNR.2.2.1 j hj).2 (φ j) hV.2 hh⟩
  have hTail : ∀ j ≤ i, ∀ f ∈ (st'.toTreeChain.G j).E, f ∈ (st.toTreeChain.G j).E →
      (st'.toTreeChain.G j).tail f = (st.toTreeChain.G j).tail f ∨
        φ' j ((st'.toTreeChain.G j).tail f) = φ j ((st.toTreeChain.G j).tail f) :=
    fun j hj f hf' hf => Or.inr (hEnds j hj f hf' hf).1
  have hHead : ∀ j ≤ i, ∀ f ∈ (st'.toTreeChain.G j).E, f ∈ (st.toTreeChain.G j).E →
      (st'.toTreeChain.G j).head f = (st.toTreeChain.G j).head f ∨
        φ' j ((st'.toTreeChain.G j).head f) = φ j ((st.toTreeChain.G j).head f) :=
    fun j hj f hf' hf => Or.inr (hEnds j hj f hf' hf).2
  exact ⟨hValid, hOld, fun j hj f hf' hf => ⟨hTail j hj f hf' hf, hHead j hj f hf' hf⟩,
    endPotAgree_of_split hValid hOld hTail hHead⟩

/-- On every non-rebuilt level `j ≤ i` of `sparseCoreProgTool`, the active forest only loses edges. -/
theorem progTool_nonRebuilt_forest_subset {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i) :
    ∀ j ≤ i, (st'.toTreeChain.activeLSF j).F.F.E ⊆ (st.toTreeChain.activeLSF j).F.F.E := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  obtain ⟨hi_d, _, hGB, hStep, hLast⟩ := hNR
  intro j hj
  by_cases hjd : j < P.d
  · obtain ⟨hbr, ℓj, gj, ordj, hsc', _⟩ := hStep j hj hjd
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjd, ↓reduceIte, hbr]
    by_cases hne : (st.scState j).isNonempty = true
    · obtain ⟨ℓ₀, hI, hcsG, _⟩ := progTool_chainInv_level_compLSFInv hInv hInit hjd hne
      have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hne (U j) ℓj gj ordj
      have hne' : (st'.scState j).isNonempty = true := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
      have hL_old : T.lsfs (st.scState j) (st.bran j) = ((st.scState j).trees (st.bran j)).cs.lsf := by
        change (if (st.scState j).isNonempty then _ else _) = _; simp [hne]
      have hL_new : T.lsfs (st'.scState j) (st.bran j) =
          (compLSFBatch ((st.scState j).trees (st.bran j)).cs (U j)).lsf := by
        change (if (st'.scState j).isNonempty then _ else _) = _
        rw [ite_eq_left hne', hsc']
        change ((T.updateOrd (st.scState j) (U j) ℓj gj ordj).1.trees (st.bran j)).cs.lsf = _
        rw [hup]; rfl
      rw [hL_old, hL_new]
      exact (compLSFBatch_decremental hI (hcsG.symm ▸ (hGB j hj).2)).1
    · have hf : (st.scState j).isNonempty = false := Bool.eq_false_iff.mpr hne
      have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hf (U j) ℓj gj ordj
      have hne' : (st'.scState j).isNonempty = false := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = false; rw [hup]; exact hf
      change (if (st'.scState j).isNonempty then _ else emptyLSF).F.F.E ⊆
        (if (st.scState j).isNonempty then _ else emptyLSF).F.F.E
      simp [hne', hf]
  · have hjeq : j = P.d := by omega
    have hieq : i = P.d := by omega
    obtain ⟨_, hLSF, hBran⟩ := hLast hieq
    subst hjeq
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl, ↓reduceIte, hLSF, hBran]
    exact Finset.Subset.rfl

/-- **`SelectPotInv` across a non-rebuilt prefix of `Update`.**
With `φ' j = splitPot (φ j) (batchSplits (U j))` on every non-rebuilt level `j ≤ i`, and
surviving edges of `G_0` keeping their gradient (`hgEq`), `SelectPotInvAt st'.toTreeChain g' φ' j`
holds at every `j ≤ i`; combining with fresh `SelectPotInvAt` on rebuilt levels `j > i` yields
full `SelectPotInv st'.toTreeChain g' φ'`. -/
theorem progTool_nonRebuilt_selectPotInv {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓ' g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ} {φ φ' : ℕ → ℕ → ℝ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hH : st.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH' : st'.toTreeChain.Holds G₀' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i)
    (hPhi : ∀ j ≤ i, φ' j = splitPot (φ j) (batchSplits (U j)))
    (hPot : SelectPotInv st.toTreeChain st.g φ)
    (hgEq : ∀ f ∈ (st'.toTreeChain.G 0).E, f ∈ (st.toTreeChain.G 0).E → g' f = st.g f) :
    (∀ j ≤ i, SelectPotInvAt st'.toTreeChain g' φ' j) ∧
    ((∀ j, i < j → j ≤ P.d → SelectPotInvAt st'.toTreeChain g' φ' j) →
      SelectPotInv st'.toTreeChain g' φ') := by
  have hEP := (progTool_nonRebuilt_endPotAgree hInv hH hH' hInit hNR hPhi).2.2.2
  have hFsub := progTool_nonRebuilt_forest_subset hInv hInit hNR
  refine ⟨fun j hj => ?_, fun hReb => ?_⟩
  · have hEPj : EndPotAgree st.toTreeChain st'.toTreeChain φ φ' j := fun m hm =>
      hEP m (le_trans hm hj)
    exact selectPotInvAt_of_endPotAgree hH hH' (le_trans hj hNR.1) (le_trans hj hNR.1)
      hPot hEPj hgEq (hFsub j hj)
  · exact selectPotInv_of_prefix_and_suffix hH hH' rfl hNR.1 hPot hEP hgEq hFsub hReb

end MinCostFlow.MinRatio
