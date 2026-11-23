module

public import MinCostFlow.SparseCore.LSFInit
public import MinCostFlow.LSF.Program.LSFModule
import Mathlib.Tactic.Linarith

/-!
# Window Initializer Interface (`CompWindow`, P3 → P4 boundary)

Defines `LSFWindowImpl`, the small interface that P4 requires from the per-component
LSF window initializer of P3 (`LSFWindow*.lean`).

Given a valid connected edgeful component graph `G_C` (`1 ≤ G_C.m`) stored in `DynGraphAt` at
`g0Ptr`, positive edge lengths `ℓ₀` stored at `lenArr`, and a fresh zeroed heap starting at
`heap`, a call to `b + initOff` with arguments
`[g0Ptr, lenArr, L_in, P_fp, k, L_w, vCap, eCap, handlesOut, heap]` writes `k` pairwise-disjoint
`LSFRep h` handles representing `lsfInit G_C ℓ₀ k j` (`j < k`) into `handlesOut[0..k-1]` inside
`[heap, endHeap)`, preserves memory below `heap` outside `handlesOut`, leaves `ZeroFrom mem' endHeap`,
and runs in cost at most `winCost k L_w G_C.n G_C.m`.

Also proves `lsfPhi_le_of_init_rep`, bounding the initial `LSFRep` potential `lsfPhi` of each
branch directly from `(LSFRep h).rep` and `S.G.V = S.G₀.V`, so `LSFWindowImpl` does not need to
carry an explicit potential bound.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## P3 window initializer interface -/

/-- Interface for the per-component LSF window initializer (P3). The library instantiates it
with `canonicalLSFInit` and its relocated-window run lemma. -/
structure LSFWindowImpl where
  /-- Underlying LSST program `[AN19]` used by `lsfModuleProcs`. -/
  Q_AN : Program
  /-- Word-size constant for `Q_AN`. -/
  c_AN : ℕ
  /-- Stretch/time constant for `Q_AN`. -/
  K_AN : ℝ
  /-- Limb bit-width `h ≥ 1`. -/
  h : ℕ
  hh : 1 ≤ h
  /-- Input fixed-point limb count and fractional precision. -/
  L_in : ℕ
  P_fp : ℕ
  /-- The abstract per-component, per-branch LSF initializer implemented by this window module. -/
  lsfInit : LSFInit
  /-- Effective LSST stretch constant for `IsValidLSFInitFor`. -/
  C_lsst : ℝ
  /-- Every branch `j < k` produced by `lsfInit` satisfies `IsValidLSFInitFor`. -/
  hInitValid : ∀ k j, 1 ≤ k → j < k → IsValidLSFInitFor lsfInit C_lsst k j
  /-- Relocatable deterministic procedure list anchored at base `b`. -/
  procs : ℕ → List Stmt
  /-- Fixed procedure count, independent of base `b`. -/
  procsLen : ℕ
  procs_length : ∀ b, (procs b).length = procsLen
  procs_noRand : ∀ b, ∀ s ∈ procs b, s.NoRand
  /-- Offset of the window-init entry procedure inside `procs b`. -/
  initOff : ℕ
  /-- Parameter precondition on `(w, k, L_w, vCap, eCap, G_C)` under which the window initializer
  may be called (e.g., word-size and fixed-point range conditions for `lemma55Program_runs`). -/
  winPre : ℕ → ℕ → ℕ → ℕ → ℕ → MGraph → Prop
  /-- Heap space budget above `heap` for one edgeful component `(k, L_w, vCap, eCap, n_C, m_C)`. -/
  winSpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  /-- Cost bound for initializing all `k` branches of one edgeful component `(k, L_w, n_C, m_C)`. -/
  winCost : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- Run specification of `b + initOff` on `[g0Ptr, lenArr, L_in, P_fp, k, L_w, vCap, eCap,
  handlesOut, heap]`: leaves `k` pairwise-disjoint `LSFRep h` handles for `lsfInit G_C ℓ₀ k j`
  (`j < k`) inside `[heap, endHeap)`, preserves memory below `heap` outside `handlesOut`, and
  maintains `ZeroFrom`. -/
  winInit_runs :
    ∀ {w b g0Ptr lenArr k L_w vCap eCap handlesOut heap : ℕ} {p : Program} {ω : ℕ → Bool}
      {G_C : MGraph} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ} (pos : ℕ),
      p.HasAt b (procs b) →
      1 ≤ k → 1 ≤ L_w → 1 ≤ eCap →
      winPre w k L_w vCap eCap G_C →
      G_C.IsValid → G_C.V.Nonempty → 1 ≤ G_C.m →
      (∀ u ∈ G_C.V, ∀ v ∈ G_C.V, G_C.Connected u v) →
      DynGraphAt mem g0Ptr vCap eCap G_C →
      (∀ e ∈ G_C.E, Valid mem (lenArr + e * L_in) h L_in ∧
        fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) →
      g0Ptr + dynGraphSize vCap eCap ≤ heap →
      lenArr + eCap * L_in ≤ heap →
      handlesOut + k ≤ heap →
      (handlesOut + k ≤ g0Ptr ∨ g0Ptr + dynGraphSize vCap eCap ≤ handlesOut) →
      (handlesOut + k ≤ lenArr ∨ lenArr + eCap * L_in ≤ handlesOut) →
      (∀ a ∈ [g0Ptr, lenArr, L_in, P_fp, k, L_w, vCap, eCap, handlesOut, heap], a < 2 ^ w) →
      ZeroFrom mem heap →
      heap + winSpace k L_w vCap eCap G_C.n G_C.m < 2 ^ w →
      ∃ body, p.procs[b + initOff]? = some body ∧
        ∃ (endHeap : ℕ) (st' : State) (c : ℕ) (x₀ : ℕ → LSFConcrete) (hs : ℕ → ℕ),
          Runs w p ω body
            (startState [g0Ptr, lenArr, L_in, P_fp, k, L_w, vCap, eCap, handlesOut, heap] mem pos)
            (.returned endHeap) st' c ∧
          heap ≤ endHeap ∧
          endHeap ≤ heap + winSpace k L_w vCap eCap G_C.n G_C.m ∧
          ZeroFrom st'.mem endHeap ∧
          (∀ z < heap, (z < handlesOut ∨ handlesOut + k ≤ z) → st'.mem z = mem z) ∧
          (∀ j < k,
            st'.mem (handlesOut + j) = hs j ∧
            (LSFRep h).rep (hs j) (lsfInit G_C ℓ₀ k j) (x₀ j) st'.mem ∧
            (x₀ j).vCap = vCap ∧ (x₀ j).eCap = eCap ∧ (x₀ j).L_w = L_w ∧
            ∀ a, (LSFRep h).foot (hs j) (x₀ j) a → heap ≤ a ∧ a < endHeap) ∧
          (∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ →
            ∀ a, (LSFRep h).foot (hs j₁) (x₀ j₁) a → ¬ (LSFRep h).foot (hs j₂) (x₀ j₂) a) ∧
          c ≤ winCost k L_w G_C.n G_C.m

/-! ## Initial potential bound from `LSFRep` -/

/-- For any freshly initialized `LSFState` with `S.G.V = S.G₀.V` represented by `LSFRep h`,
its initial potential `lsfPhi` is bounded by `3000 * (S.G₀.n + 1) * (Nat.log 2 (S.G₀.n + 2) + 1)`. -/
lemma lsfPhi_le_of_init_rep {h b : ℕ} {S : LSFState} {x : LSFConcrete} {mem : ℕ → ℕ}
    (hrep : (LSFRep h).rep b S x mem) (hVG : S.G.V = S.G₀.V) :
    (LSFRep h).phi b x mem ≤ 3000 * (S.G₀.n + 1) * (Nat.log 2 (S.G₀.n + 2) + 1) := by
  classical
  rcases hrep with ⟨_, _, _, _, _, _, hInv, hn0, _, htM, _, _, htn, _, _, _, _, _, _,
    hdgF, hFAnc, _, _, _⟩
  have hmF_eq : mem (lsfDgFPtr b x.vCap x.eCap x.tM + dgMOff) = S.RF.F.m := hdgF.2.2.2.2.2.2.1
  have hmF_le : mem (lsfDgFPtr b x.vCap x.eCap x.tM + dgMOff) ≤ x.n0 := by
    rw [hmF_eq]
    have h1 : S.RF.F.m ≤ S.T₀.E.card := hInv.RF_E_card_le
    omega
  have hsz : ∀ i < min (mem (lsfDgFPtr b x.vCap x.eCap x.tM + dgMOff)) (fECap x.eCap x.n0),
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
      cid < x.vCap → mem (fCompSizeBase fAncPtr x.vCap + cid) ≤ x.n0 := by
    intro i hi
    dsimp only
    intro _ _ _ _
    obtain ⟨eL, helen, _, hemem, heLA, _⟩ := hdgF.2.2.2.2.2.2.2.2.2.2.2.2.1
    -- Extract edge membership in S.RF.F.E
    have hi_eL : i < eL.length := by
      rw [helen, ← hmF_eq]
      exact lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have he_eq : mem (dgEListBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0) + i) =
        eL[i]'hi_eL := heLA i hi_eL
    have he_mem : eL[i]'hi_eL ∈ S.RF.F.E := (hemem _).mp (List.getElem_mem hi_eL)
    have ht_slot : mem (dgETailSlotBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0) +
        eL[i]'hi_eL) = mem (dgExtToIntBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap + S.RF.F.tail (eL[i]'hi_eL)) :=
      (hdgF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ he_mem).1
    have htV : S.RF.F.tail (eL[i]'hi_eL) ∈ S.RF.F.V := (hdgF.1 _ he_mem).1
    have hi2e : mem (dgIntToExtBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap +
        mem (dgExtToIntBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap + S.RF.F.tail (eL[i]'hi_eL))) =
        S.RF.F.tail (eL[i]'hi_eL) :=
      (hdgF.2.2.2.2.2.2.2.2.2.1 _ htV).2
    rw [he_eq, ht_slot, hi2e]
    rcases hFAnc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcid, hvspec⟩
    obtain ⟨hceq, hcact, _⟩ := hvspec _ htV
    obtain ⟨_, _, _, _, hsz_eq, _, hsz_card⟩ := hcid _ hcact
    rw [hsz_eq, hsz_card]
    have hcard_le : (S.RF.F.V.filter fun w => S.RF.F.Connected w
        (x.compRoot (mem (fCompIdBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap +
          S.RF.F.tail (eL[i]'hi_eL))))).card ≤ S.RF.F.V.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hVcard : S.RF.F.V.card = x.n0 := by
      rw [hInv.RF_V_eq, hVG]; exact hn0
    omega
  simpa only [LSFRep, hn0] using lsfPhi_init_le hmF_le hsz

end

end MinCostFlow.SparseCore.Program
