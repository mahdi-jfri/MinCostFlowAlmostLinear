module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepBunPrepProg

import Mathlib.Tactic

/-!
# Phase 3a verification: pre-tour deletion-triples builder (`AssemblyFirstStepDelTriples`)

Verifies `asmFirstBuildDelTriplesStmt (bBun + bundleIdxReadParent)` on `[bunH, tourH, delEdgesPtr,
nDel, h]` (`asmFirstBuildDelTriples_runs`), producing `readDelTriples st'.mem h nDel = dels` with
exact pre-step bundle parents `(B.parent (B.bundleOf (e, true)), B.parent (B.bundleOf (e, false)))`
for every deleted edge belonging to an active bundle, while preserving `bunTableHeadroomRep` and
`htour.rep` with amortized cost `buildDelTriplesCost TS eCap nDel`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

private lemma exists_slot_of_edgeSlot_ne_zero {slotCap vCap eCap bunH e : ℕ}
    {S : BundleTableState slotCap} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap bunH S m mem) (he : e < eCap)
    (hne : mem (btEdgeSlotBase bunH slotCap + e) ≠ 0) :
    ∃ (j : Fin slotCap) (B : BundleState), S j = some B ∧ e ∈ B.edges ∧
      mem (btEdgeSlotBase bunH slotCap + e) = j.1 + 1 := by
  have h1 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
  by_contra hno
  push Not at hno
  have hall : ∀ (j : Fin slotCap) (B : BundleState), S j = some B → e ∉ B.edges := fun j B hSB heB =>
    hno j B hSB heB (h1.1 j B hSB heB)
  exact hne (h1.2 hall)

private lemma bundleOf_mem_vertices {slotCap vCap eCap bunH : ℕ}
    {S : BundleTableState slotCap} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap bunH S m mem)
    {j : Fin slotCap} {B : BundleState} (hSB : S j = some B) {e : ℕ} (he : e ∈ B.edges)
    (side : Bool) : B.bundleOf (e, side) ∈ B.vertices := by
  have hslot := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
  cases hm : m.slotBlocks j with
  | none => simp [hSB, hm] at hslot
  | some pc =>
    simp only [hSB, hm] at hslot
    obtain ⟨nB, hV, _, _, hlt, _⟩ := hslot.2.1
    rw [hV, Finset.mem_range]
    have hx : (e, side) ∈ Bundle.edgeEnds B.edges := by simp [Bundle.mem_edgeEnds, he]
    exact hlt (e, side) hx

private lemma readDelTriples_congr {mem₁ mem₂ : ℕ → ℕ} {base n : ℕ}
    (hag : ∀ a, base ≤ a → a < base + 3 * n → mem₁ a = mem₂ a) :
    readDelTriples mem₁ base n = readDelTriples mem₂ base n := by
  unfold readDelTriples
  refine List.map_congr_left fun i hi => ?_
  have hlt := List.mem_range.mp hi
  rw [hag (base + 3 * i) (by omega) (by omega),
      hag (base + 3 * i + 1) (by omega) (by omega),
      hag (base + 3 * i + 2) (by omega) (by omega)]

public section

set_option maxHeartbeats 800000 in
/-- **Verification of `asmFirstBuildDelTriplesStmt (bBun + bundleIdxReadParent)`**:
builds `dels` at `[h, h + 3 * delEdges.length)` matching `delEdges` with exact pre-step bundle
parents for every deleted edge in an active bundle, preserving `bunTableHeadroomRep` and
`htour.rep`, allocating at most `buildDelTriplesSpace TS delEdges.length` words, and running in
amortized time `buildDelTriplesCost TS eCap delEdges.length`. -/
theorem asmFirstBuildDelTriples_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap k bBun bTourList bTourLen bTourOwner : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpBun : p.HasAt bBun (bundleProcs bBun bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {bunH tourH delEdgesPtr h pos : ℕ}
    {S : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {cord : ℕ → List End} {tx₀ : htour.rep.τ} {delEdges : List ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hvCapW : vCap < 2 ^ w) (_h2eW : 2 * eCap < 2 ^ w)
    (htbl_lt : bunH + bundleTableFixedSize slotCap eCap ≤ h)
    (htourW : tourH < 2 ^ w)
    (hrepB : (bunTableHeadroomRep slotCap vCap eCap k).rep bunH S m mem₀)
    (hrepT : htour.rep.rep tourH cord tx₀ mem₀)
    (hinv : bunRestartInv vCap eCap S cord)
    (hfootB : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot bunH m a → a < h)
    (hfootT : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (hdisjBT : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot bunH m a →
      ¬ htour.rep.foot tourH tx₀ a)
    (hDelList : ListAt mem₀ delEdgesPtr delEdges)
    (hDel_lt : delEdgesPtr + delEdges.length ≤ h)
    (hDel_disjT : ∀ a, delEdgesPtr ≤ a → a < delEdgesPtr + delEdges.length →
      ¬ htour.rep.foot tourH tx₀ a)
    (hDel_cap : ∀ e ∈ delEdges, e < eCap)
    (hZero : ZeroFrom mem₀ h)
    (hSpace : h + buildDelTriplesSpace TS delEdges.length < 2 ^ w) :
    ∃ hEnd st' c tx', ∃ (dels : List (ℕ × ℕ × ℕ)),
      Runs w p ω (asmFirstBuildDelTriplesStmt (bBun + bundleIdxReadParent))
        (startState [bunH, tourH, delEdgesPtr, delEdges.length, h] mem₀ pos)
        (.returned hEnd) st' c ∧
      dels.length = delEdges.length ∧
      dels.map Prod.fst = delEdges ∧
      readDelTriples st'.mem h delEdges.length = dels ∧
      (∀ trD ∈ dels, trD.1 < eCap ∧ trD.2.1 < 2 ^ w ∧ trD.2.2 < 2 ^ w) ∧
      (∀ i (hi : i < dels.length), ∀ (j : Fin slotCap) (B : BundleState),
        S j = some B → dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false))) ∧
      (bunTableHeadroomRep slotCap vCap eCap k).rep bunH S m st'.mem ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      h + 3 * delEdges.length ≤ hEnd ∧
      hEnd ≤ h + buildDelTriplesSpace TS delEdges.length ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + 3 * delEdges.length ≤ a ∧ a < hEnd)) ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      (∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot bunH m a → st'.mem a = mem₀ a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        buildDelTriplesCost TS eCap delEdges.length + htour.rep.phi tourH tx₀ mem₀ := by
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have hbtSlot_w : bunH + btOffEdgeSlot < 2 ^ w := by unfold btOffEdgeSlot bundleTableFixedSize at *; omega
  have hbtBun_w : bunH + btOffEndBundle < 2 ^ w := by unfold btOffEndBundle bundleTableFixedSize at *; omega
  have hOffSlot_val : mem₀ (bunH + btOffEdgeSlot) = btEdgeSlotBase bunH slotCap := hrepB.1.2.2.2.2.1
  have hOffBun_val : mem₀ (bunH + btOffEndBundle) = btEndBundleBase bunH slotCap eCap := hrepB.1.2.2.2.2.2.1
  have hSp_def : buildDelTriplesSpace TS delEdges.length =
      3 * delEdges.length + 2 * delEdges.length * TS.querySpace := rfl
  -- Prologue: `r5 := h + 3 * nDel`, `r6 := edgeSlotBase`, `r7 := endBunBase`
  set st0 := startState [bunH, tourH, delEdgesPtr, delEdges.length, h] mem₀ pos
  have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 3)))) st0 .normal
      { st0 with regs := Function.update st0.regs 5 (h + 3 * delEdges.length) } _ :=
    runs_assign_iff.mpr ⟨h + 3 * delEdges.length,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
        (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq (by simp [st0, startState])) (by omega))
        (by omega), rfl, rfl, rfl⟩
  set stA : State := { st0 with regs := Function.update st0.regs 5 (h + 3 * delEdges.length) }
  have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const btOffEdgeSlot)))) stA .normal
      { stA with regs := Function.update stA.regs 6 (btEdgeSlotBase bunH slotCap) } _ :=
    runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, st0, startState]))
        (Expr.eval_const (by unfold btOffEdgeSlot; omega)) hbtSlot_w) hOffSlot_val, rfl, rfl, rfl⟩
  set stB : State := { stA with regs := Function.update stA.regs 6 (btEdgeSlotBase bunH slotCap) }
  have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const btOffEndBundle)))) stB .normal
      { stB with regs := Function.update stB.regs 7 (btEndBundleBase bunH slotCap eCap) } _ :=
    runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stB, stA, st0, startState]))
        (Expr.eval_const (by unfold btOffEndBundle; omega)) hbtBun_w) hOffBun_val, rfl, rfl, rfl⟩
  set stC : State := { stB with regs := Function.update stB.regs 7 (btEndBundleBase bunH slotCap eCap) }
  -- Loop invariant for `forRange 8 0 (.reg 3)`
  let Inv : ℕ → htour.rep.τ → State → Prop := fun j tx st =>
    ∃ hp : ℕ,
      (∀ r, r < 8 → r ≠ 5 → st.regs r = stC.regs r) ∧
      st.regs 8 = j ∧ st.regs 5 = hp ∧
      h + 3 * delEdges.length ≤ hp ∧ hp ≤ h + 3 * delEdges.length + 2 * j * TS.querySpace ∧
      ZeroFrom st.mem hp ∧
      (∀ i, j ≤ i → i < delEdges.length →
        st.mem (h + 3 * i) = 0 ∧ st.mem (h + 3 * i + 1) = 0 ∧ st.mem (h + 3 * i + 2) = 0) ∧
      (bunTableHeadroomRep slotCap vCap eCap k).rep bunH S m st.mem ∧
      htour.rep.rep tourH cord tx st.mem ∧
      (∀ a, htour.rep.foot tourH tx a →
        htour.rep.foot tourH tx₀ a ∨ (h + 3 * delEdges.length ≤ a ∧ a < hp)) ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx₀ a → st.mem a = mem₀ a) ∧
      (∀ i (hi : i < j), ∀ (hi' : i < delEdges.length),
        st.mem (h + 3 * i) = delEdges[i]'hi' ∧
        st.mem (h + 3 * i + 1) < 2 ^ w ∧ st.mem (h + 3 * i + 2) < 2 ^ w ∧
        ∀ (js : Fin slotCap) (B : BundleState), S js = some B → delEdges[i]'hi' ∈ B.edges →
          st.mem (h + 3 * i + 1) = B.parent (B.bundleOf (delEdges[i]'hi', true)) ∧
          st.mem (h + 3 * i + 2) = B.parent (B.bundleOf (delEdges[i]'hi', false)))
  let Φ : htour.rep.τ → State → ℕ := fun tx st => htour.rep.phi tourH tx st.mem
  have hInitInv : Inv 0 tx₀ { stC with regs := Function.update stC.regs 8 0 } :=
    ⟨h + 3 * delEdges.length, fun r hr _ => by simp [Function.update_of_ne (by omega : r ≠ 8)],
      by simp, by simp [stC, stB, stA], le_refl _, by omega,
      fun a ha => hZero a (by omega),
      fun i _ hi => ⟨hZero _ (by omega), hZero _ (by omega), hZero _ (by omega)⟩,
      hrepB, hrepT, fun _ ha => Or.inl ha, fun _ _ _ => rfl, fun _ hi => by omega⟩
  have hStep : ∀ i tx st, i < delEdges.length → Inv i tx st →
      ∃ st₁ c₁ tx₁,
        Runs w p ω
          (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
           .store (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.reg 9) ;;
           .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
           .cond (.reg 10)
             (.assign 11 (.bin .sub (.reg 10) (.const 1)) ;;
              .assign 12 (.load (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9)))) ;;
              .assign 13 (.load (.bin .add (.reg 7) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1)))) ;;
              .assign 14 (.reg 5) ;;
              .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 12, .reg 5] ;;
              .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 1)) (.load (.reg 14)) ;;
              .assign 14 (.reg 5) ;;
              .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 13, .reg 5] ;;
              .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 2)) (.load (.reg 14)))
             .nop)
          st .normal st₁ c₁ ∧
        st₁.regs 8 = i ∧
        Inv (i + 1) tx₁ { st₁ with regs := Function.update st₁.regs 8 (i + 1) } ∧
        Φ tx₁ { st₁ with regs := Function.update st₁.regs 8 (i + 1) } = Φ tx₁ st₁ ∧
        c₁ + Φ tx₁ st₁ ≤ (2 * TS.mul * ordStoreLog eCap + 245) + Φ tx st := by
    intro i tx st hi ⟨hp, hregs, hr8, hr5, hhp_lo, hhp_hi, hzp, hrem0, hrepB_i, hrepT_i, hftT_i, hfr_i, hdone_i⟩
    have hr0 : st.regs 0 = bunH := (hregs 0 (by decide) (by decide)).trans (by simp [stC, stB, stA, st0, startState])
    have hr1 : st.regs 1 = tourH := (hregs 1 (by decide) (by decide)).trans (by simp [stC, stB, stA, st0, startState])
    have hr2 : st.regs 2 = delEdgesPtr := (hregs 2 (by decide) (by decide)).trans (by simp [stC, stB, stA, st0, startState])
    have hr4 : st.regs 4 = h := (hregs 4 (by decide) (by decide)).trans (by simp [stC, stB, stA, st0, startState])
    have hr6 : st.regs 6 = btEdgeSlotBase bunH slotCap := (hregs 6 (by decide) (by decide)).trans (by simp [stC, stB])
    have hr7 : st.regs 7 = btEndBundleBase bunH slotCap eCap := (hregs 7 (by decide) (by decide)).trans (by simp [stC])
    set e := delEdges[i]'hi
    have he_cap : e < eCap := hDel_cap e (List.getElem_mem hi)
    have he_mem : st.mem (delEdgesPtr + i) = e :=
      (hfr_i (delEdgesPtr + i) (by omega) (hDel_disjT _ (by omega) (by omega))).trans (hDelList i hi)
    have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 2) (.reg 8)))) st .normal
        { st with regs := Function.update st.regs 9 e } _ :=
      runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr8) (by omega)) he_mem, rfl, rfl, rfl⟩
    set st1 : State := { st with regs := Function.update st.regs 9 e }
    set mem1 := Function.update st.mem (h + 3 * i) e
    have hs_e : Runs w p ω (.store (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.reg 9)) st1 .normal
        ⟨mem1, st1.regs, st1.pos⟩ _ :=
      runs_store_iff.mpr ⟨h + 3 * i, e,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, hr4]))
          (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq (by simp [st1, hr8])) (by omega)) (by omega),
        Expr.eval_reg_of_eq (by simp [st1]), rfl, rfl, rfl⟩
    set st2 : State := ⟨mem1, st1.regs, st1.pos⟩
    have hmem1_ne : ∀ a, a ≠ h + 3 * i → mem1 a = st.mem a := fun a hne => Function.update_of_ne hne _ _
    have hrepB1 : (bunTableHeadroomRep slotCap vCap eCap k).rep bunH S m mem1 :=
      ((bunTableHeadroomRep_local slotCap vCap eCap k) bunH S m st.mem mem1 fun a ha =>
        (hmem1_ne a (by have := hfootB a ha; omega)).symm).1 hrepB_i
    have hrepT1 : htour.rep.rep tourH cord tx mem1 :=
      (htour.rep_local tourH cord tx st.mem mem1 fun a ha =>
        (hmem1_ne a (by rcases hftT_i a ha with h0 | ⟨hlo, _⟩; have := hfootT a h0; omega; omega)).symm).1 hrepT_i
    have hphiT1 : htour.rep.phi tourH tx mem1 = htour.rep.phi tourH tx st.mem :=
      (htour.rep_local tourH cord tx st.mem mem1 fun a ha =>
        (hmem1_ne a (by rcases hftT_i a ha with h0 | ⟨hlo, _⟩; have := hfootT a h0; omega; omega)).symm).2.symm
    have hes_addr_w : btEdgeSlotBase bunH slotCap + e < 2 ^ w := by
      unfold btEdgeSlotBase bundleTableFixedSize at *; omega
    set es := mem1 (btEdgeSlotBase bunH slotCap + e)
    have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.reg 9)))) st2 .normal
        { st2 with regs := Function.update st2.regs 10 es } _ :=
      runs_assign_iff.mpr ⟨es, Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, hr6]))
          (Expr.eval_reg_of_eq (by simp [st2, st1])) hes_addr_w) rfl, rfl, rfl, rfl⟩
    set st3 : State := { st2 with regs := Function.update st2.regs 10 es }
    -- Branch on `es = 0` vs `es ≠ 0`
    by_cases hes0 : es = 0
    · have hcond : (Expr.reg 10).eval w st3 = some 0 := by simp [Expr.eval, st3, hes0]
      have hbody : Runs w p ω
          (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
           .store (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.reg 9) ;;
           .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
           .cond (.reg 10)
             (.assign 11 (.bin .sub (.reg 10) (.const 1)) ;;
              .assign 12 (.load (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9)))) ;;
              .assign 13 (.load (.bin .add (.reg 7) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1)))) ;;
              .assign 14 (.reg 5) ;;
              .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 12, .reg 5] ;;
              .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 1)) (.load (.reg 14)) ;;
              .assign 14 (.reg 5) ;;
              .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 13, .reg 5] ;;
              .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 2)) (.load (.reg 14)))
             .nop) st .normal st3 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha9,
          runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hs_e,
          runs_seq_iff.mpr (Or.inr ⟨st3, _, _, ha10,
            runs_cond_iff.mpr ⟨0, 1, hcond, by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
            rfl⟩), rfl⟩), rfl⟩)
      have hno_edge : ∀ (js : Fin slotCap) (B : BundleState), S js = some B → e ∉ B.edges := fun js B hSB heB => by
        have := (hrepB1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he_cap).1 js B hSB heB
        change es = js.1 + 1 at this; omega
      refine ⟨st3, _, tx, hbody, by simp [st3, st2, st1, hr8], ?_, rfl, ?_⟩
      · refine ⟨hp, fun r hr hr5' => by simp [st3, st2, st1, Function.update_of_ne (by omega : r ≠ 8), Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 9), hregs r hr hr5'],
          by simp, by simp [st3, st2, st1, hr5], hhp_lo,
          by have h2q : 2 * (i + 1) * TS.querySpace = 2 * i * TS.querySpace + 2 * TS.querySpace := by ring
             omega,
          fun a ha => (hmem1_ne a (by omega)).trans (hzp a ha),
          fun i' hi1 hi2 => ⟨(hmem1_ne _ (by omega)).trans (hrem0 i' (by omega) hi2).1,
            (hmem1_ne _ (by omega)).trans (hrem0 i' (by omega) hi2).2.1,
            (hmem1_ne _ (by omega)).trans (hrem0 i' (by omega) hi2).2.2⟩,
          hrepB1, hrepT1, fun a ha => by rcases hftT_i a ha with h0 | ⟨hlo, hhi⟩; exact Or.inl h0; exact Or.inr ⟨hlo, hhi⟩,
          fun a ha hnt => (hmem1_ne a (by omega)).trans (hfr_i a ha hnt),
          fun i' hi' hi_lt => ?_⟩
        by_cases hlt' : i' < i
        · obtain ⟨h0', h1', h2', hp'⟩ := hdone_i i' hlt' hi_lt
          exact ⟨(hmem1_ne _ (by omega)).trans h0', by change mem1 _ < _; rw [hmem1_ne _ (by omega)]; exact h1',
            by change mem1 _ < _; rw [hmem1_ne _ (by omega)]; exact h2',
            fun js B hSB heB => ⟨(hmem1_ne _ (by omega)).trans (hp' js B hSB heB).1,
              (hmem1_ne _ (by omega)).trans (hp' js B hSB heB).2⟩⟩
        · have heq : i' = i := by omega
          subst heq
          refine ⟨by change mem1 (h + 3 * i') = e; exact Function.update_self _ _ _,
            by change mem1 _ < _; rw [hmem1_ne _ (by omega), (hrem0 i' (le_refl _) hi).2.1]; omega,
            by change mem1 _ < _; rw [hmem1_ne _ (by omega), (hrem0 i' (le_refl _) hi).2.2]; omega,
            fun js B hSB heB => absurd heB (hno_edge js B hSB)⟩
      · dsimp only [Φ, st3, st2, Expr.size]; rw [hphiT1]; omega
    · obtain ⟨js, B, hSjs, heB, hes_eq⟩ := exists_slot_of_edgeSlot_ne_zero hrepB1.1 he_cap hes0
      have hbT_in : B.bundleOf (e, true) ∈ B.vertices := bundleOf_mem_vertices hrepB1.1 hSjs heB true
      have hbF_in : B.bundleOf (e, false) ∈ B.vertices := bundleOf_mem_vertices hrepB1.1 hSjs heB false
      have hbT_mem : mem1 (btEndBundleBase bunH slotCap eCap + 2 * e) = B.bundleOf (e, true) := by
        have hx : (e, true) ∈ Bundle.edgeEnds B.edges := by simp [Bundle.mem_edgeEnds, heB]
        simpa [endKey] using hrepB1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 js B hSjs (e, true) hx
      have hbF_mem : mem1 (btEndBundleBase bunH slotCap eCap + (2 * e + 1)) = B.bundleOf (e, false) := by
        have hx : (e, false) ∈ Bundle.edgeEnds B.edges := by simp [Bundle.mem_edgeEnds, heB]
        simpa [endKey] using hrepB1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 js B hSjs (e, false) hx
      have hbun_w : btEndBundleBase bunH slotCap eCap + (2 * e + 1) < 2 ^ w := by
        unfold btEndBundleBase bundleTableFixedSize at *; omega
      have hqs_step : 2 * i * TS.querySpace + 2 * TS.querySpace ≤ 2 * delEdges.length * TS.querySpace := by
        have h1 := Nat.mul_le_mul_right TS.querySpace (show 2 * i + 2 ≤ 2 * delEdges.length by omega)
        linarith
      have hfootB1 : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot bunH m a → a < hp :=
        fun a ha => lt_of_lt_of_le (hfootB a ha) (by omega)
      have hfootT1 : ∀ a, htour.rep.foot tourH tx a → a < hp := fun a ha => by
        rcases hftT_i a ha with h0 | ⟨_, hhi⟩; exact lt_of_lt_of_le (hfootT a h0) (by omega); exact hhi
      have hdisjBT1 : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot bunH m a → ¬ htour.rep.foot tourH tx a :=
        fun a ha hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; exact hdisjBT a ha h0; have := hfootB a ha; omega
      -- First `readParent` call for `(e, true)`
      obtain ⟨bodyRP, hbodyRP, o1, stRP1, cRP1, tx1, hrunRP1, hrepB2, hrepT2, _, hval1, hh1_lo, hh1_hi, hz1, hfr1, hft1, hc1⟩ :=
        bunTableHeadroom_readParent_runs (ω := ω) (pos := st3.pos) hpBun htour hw16 hvCapW
          (by omega) htourW (by unfold buildDelTriplesSpace at hSpace; omega)
          (fun a ha => (hmem1_ne a (by omega)).trans (hzp a ha))
          hfootB1 hfootT1 hdisjBT1 hrepB1 hrepT1 hinv hSjs hbT_in
      set hp1 := o1.value
      set pT := B.parent (B.bundleOf (e, true))
      have hpT_w : pT < 2 ^ w := lt_trans (hinv.1.2 js B hSjs _ hbT_in).1 hvCapW
      -- Store `pT` at `h + 3 * i + 1`
      set mem2 := Function.update stRP1.mem (h + 3 * i + 1) pT
      have hmem2_ne : ∀ a, a ≠ h + 3 * i + 1 → mem2 a = stRP1.mem a := fun a hne => Function.update_of_ne hne _ _
      have hrepB2' : (bunTableHeadroomRep slotCap vCap eCap k).rep bunH S m mem2 :=
        ((bunTableHeadroomRep_local slotCap vCap eCap k) bunH S m stRP1.mem mem2 fun a ha =>
          (hmem2_ne a (by have := hfootB a ha; omega)).symm).1 hrepB2
      have hftT2 : ∀ a, htour.rep.foot tourH tx1 a →
          htour.rep.foot tourH tx₀ a ∨ (h + 3 * delEdges.length ≤ a ∧ a < hp1) := fun a ha => by
        rcases hft1 a ha with hp' | ⟨hlo, hhi⟩
        · rcases hftT_i a hp' with h0 | ⟨hlo0, hhi0⟩; exact Or.inl h0; exact Or.inr ⟨hlo0, by omega⟩
        · exact Or.inr ⟨by omega, hhi⟩
      have hrepT2' : htour.rep.rep tourH cord tx1 mem2 :=
        (htour.rep_local tourH cord tx1 stRP1.mem mem2 fun a ha =>
          (hmem2_ne a (by rcases hftT2 a ha with h0 | ⟨hlo, _⟩; have := hfootT a h0; omega; omega)).symm).1 hrepT2
      have hphiT2' : htour.rep.phi tourH tx1 mem2 = htour.rep.phi tourH tx1 stRP1.mem :=
        (htour.rep_local tourH cord tx1 stRP1.mem mem2 fun a ha =>
          (hmem2_ne a (by rcases hftT2 a ha with h0 | ⟨hlo, _⟩; have := hfootT a h0; omega; omega)).symm).2.symm
      have hphiB_eq1 : (bunTableHeadroomRep slotCap vCap eCap k).phi bunH m stRP1.mem =
          (bunTableHeadroomRep slotCap vCap eCap k).phi bunH m mem1 :=
        ((bunTableHeadroomRep_local slotCap vCap eCap k) bunH S m mem1 stRP1.mem fun a ha =>
          (hfr1 a (hfootB1 a ha) (hdisjBT1 a ha)).symm).2.symm
      -- Second `readParent` call for `(e, false)`
      have hdisjBT2 : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot bunH m a → ¬ htour.rep.foot tourH tx1 a :=
        fun a ha hT => by rcases hftT2 a hT with h0 | ⟨hlo, _⟩; exact hdisjBT a ha h0; have := hfootB a ha; omega
      obtain ⟨bodyRP', hbodyRP', o2, stRP2, cRP2, tx2, hrunRP2, hrepB3, hrepT3, _, hval2, hh2_lo, hh2_hi, hz2, hfr2, hft2, hc2⟩ :=
        bunTableHeadroom_readParent_runs (ω := ω) (pos := stRP1.pos) hpBun htour hw16 hvCapW
          (by omega) htourW (by unfold buildDelTriplesSpace at hSpace; omega)
          (fun a ha => (hmem2_ne a (by omega)).trans (hz1 a ha))
          (fun a ha => lt_of_lt_of_le (hfootB a ha) (by omega))
          (fun a ha => by rcases hftT2 a ha with h0 | ⟨_, hhi⟩; exact lt_of_lt_of_le (hfootT a h0) (by omega); exact hhi)
          hdisjBT2 hrepB2' hrepT2' hinv hSjs hbF_in
      set hp2 := o2.value
      set pF := B.parent (B.bundleOf (e, false))
      have hpF_w : pF < 2 ^ w := lt_trans (hinv.1.2 js B hSjs _ hbF_in).1 hvCapW
      set mem3 := Function.update stRP2.mem (h + 3 * i + 2) pF
      have hmem3_ne : ∀ a, a ≠ h + 3 * i + 2 → mem3 a = stRP2.mem a := fun a hne => Function.update_of_ne hne _ _
      have hftT3 : ∀ a, htour.rep.foot tourH tx2 a →
          htour.rep.foot tourH tx₀ a ∨ (h + 3 * delEdges.length ≤ a ∧ a < hp2) := fun a ha => by
        rcases hft2 a ha with hp' | ⟨hlo, hhi⟩
        · rcases hftT2 a hp' with h0 | ⟨hlo0, hhi0⟩; exact Or.inl h0; exact Or.inr ⟨hlo0, by omega⟩
        · exact Or.inr ⟨by omega, hhi⟩
      have hrepB3' : (bunTableHeadroomRep slotCap vCap eCap k).rep bunH S m mem3 :=
        ((bunTableHeadroomRep_local slotCap vCap eCap k) bunH S m stRP2.mem mem3 fun a ha =>
          (hmem3_ne a (by have := hfootB a ha; omega)).symm).1 hrepB3
      have hrepT3' : htour.rep.rep tourH cord tx2 mem3 :=
        (htour.rep_local tourH cord tx2 stRP2.mem mem3 fun a ha =>
          (hmem3_ne a (by rcases hftT3 a ha with h0 | ⟨hlo, _⟩; have := hfootT a h0; omega; omega)).symm).1 hrepT3
      have hphiT3' : htour.rep.phi tourH tx2 mem3 = htour.rep.phi tourH tx2 stRP2.mem :=
        (htour.rep_local tourH cord tx2 stRP2.mem mem3 fun a ha =>
          (hmem3_ne a (by rcases hftT3 a ha with h0 | ⟨hlo, _⟩; have := hfootT a h0; omega; omega)).symm).2.symm
      have hphiB_eq2 : (bunTableHeadroomRep slotCap vCap eCap k).phi bunH m stRP2.mem =
          (bunTableHeadroomRep slotCap vCap eCap k).phi bunH m mem2 :=
        ((bunTableHeadroomRep_local slotCap vCap eCap k) bunH S m mem2 stRP2.mem fun a ha =>
          (hfr2 a (lt_of_lt_of_le (hfootB a ha) (by omega)) (hdisjBT2 a ha)).symm).2.symm
      -- Execute the `then` branch statements
      set st11 := { st3 with regs := Function.update st3.regs 11 js.1 }
      set st12 := { st11 with regs := Function.update st11.regs 12 (B.bundleOf (e, true)) }
      set st13 := { st12 with regs := Function.update st12.regs 13 (B.bundleOf (e, false)) }
      set st14 := { st13 with regs := Function.update st13.regs 14 hp }
      set stC1 : State := ⟨stRP1.mem, Function.update st14.regs 5 hp1, stRP1.pos⟩
      set stS1 : State := ⟨mem2, stC1.regs, stC1.pos⟩
      set st14' : State := { stS1 with regs := Function.update stS1.regs 14 hp1 }
      set stC2 : State := ⟨stRP2.mem, Function.update st14'.regs 5 hp2, stRP2.pos⟩
      set stS2 : State := ⟨mem3, stC2.regs, stC2.pos⟩
      have hthen : ∃ cT, Runs w p ω
          (.assign 11 (.bin .sub (.reg 10) (.const 1)) ;;
           .assign 12 (.load (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9)))) ;;
           .assign 13 (.load (.bin .add (.reg 7) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1)))) ;;
           .assign 14 (.reg 5) ;;
           .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 12, .reg 5] ;;
           .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 1)) (.load (.reg 14)) ;;
           .assign 14 (.reg 5) ;;
           .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 13, .reg 5] ;;
           .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 2)) (.load (.reg 14)))
          st3 .normal stS2 cT ∧ cT ≤ cRP1 + cRP2 + 95 := by
        have hjs1_w : js.1 + 1 < 2 ^ w := by
          have := js.2; unfold bundleTableFixedSize at htbl_lt; omega
        have he11 := Expr.eval_sub
          (Expr.eval_reg_of_eq (show st3.regs 10 = js.1 + 1 by dsimp [st3]; exact (Function.update_self 10 es st2.regs).trans hes_eq))
          (Expr.eval_const h1w) hjs1_w
        rw [Nat.add_sub_cancel] at he11
        have e11 : Runs w p ω (.assign 11 (.bin .sub (.reg 10) (.const 1))) st3 .normal st11 _ :=
          runs_assign_iff.mpr ⟨js.1, he11, rfl, rfl, rfl⟩
        have e12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9))))) st11 .normal st12 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st11, st3, st2, st1, hr7]))
            (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [st11, st3, st2, st1])) (by omega)) (by omega)) hbT_mem, rfl, rfl, rfl⟩
        have e13 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 7) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1))))) st12 .normal st13 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st3, st2, st1, hr7]))
            (Expr.eval_add (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [st12, st11, st3, st2, st1])) (by omega))
              (Expr.eval_const h1w) (by omega)) hbun_w) hbF_mem, rfl, rfl, rfl⟩
        have e14 : Runs w p ω (.assign 14 (.reg 5)) st13 .normal st14 _ :=
          runs_assign_iff.mpr ⟨hp, Expr.eval_reg_of_eq (by simp [st13, st12, st11, st3, st2, st1, hr5]), rfl, rfl, rfl⟩
        have ec1 : Runs w p ω (.call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 12, .reg 5]) st14 .normal stC1 _ :=
          runs_call_iff.mpr ⟨[bunH, tourH, js.1, B.bundleOf (e, true), hp], bodyRP, o1, stRP1, cRP1,
            by simp [evalArgs, Expr.eval, st14, st13, st12, st11, st3, st2, st1, hr0, hr1, hr5], hbodyRP, hrunRP1, rfl, rfl, rfl⟩
        have es1 : Runs w p ω (.store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 1)) (.load (.reg 14)))
            stC1 .normal stS1 _ :=
          runs_store_iff.mpr ⟨h + 3 * i + 1, pT,
            Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stC1, st14, st13, st12, st11, st3, st2, st1, hr4]))
              (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq (by simp [stC1, st14, st13, st12, st11, st3, st2, st1, hr8])) (by omega)) (by omega))
              (Expr.eval_const h1w) (by omega),
            Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [stC1, st14])) hval1, rfl, rfl, rfl⟩
        have e14' : Runs w p ω (.assign 14 (.reg 5)) stS1 .normal st14' _ :=
          runs_assign_iff.mpr ⟨hp1, Expr.eval_reg_of_eq (by simp [stS1, stC1]), rfl, rfl, rfl⟩
        have ec2 : Runs w p ω (.call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 13, .reg 5]) st14' .normal stC2 _ :=
          runs_call_iff.mpr ⟨[bunH, tourH, js.1, B.bundleOf (e, false), hp1], bodyRP', o2, stRP2, cRP2,
            by simp [evalArgs, Expr.eval, st14', stS1, stC1, st14, st13, st12, st11, st3, st2, st1, hr0, hr1], hbodyRP', hrunRP2, rfl, rfl, rfl⟩
        have es2 : Runs w p ω (.store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 2)) (.load (.reg 14)))
            stC2 .normal stS2 _ :=
          runs_store_iff.mpr ⟨h + 3 * i + 2, pF,
            Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stC2, st14', stS1, stC1, st14, st13, st12, st11, st3, st2, st1, hr4]))
              (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq (by simp [stC2, st14', stS1, stC1, st14, st13, st12, st11, st3, st2, st1, hr8])) (by omega)) (by omega))
              (Expr.eval_const h2w) (by omega),
            Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [stC2, st14'])) hval2, rfl, rfl, rfl⟩
        refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st11, _, _, e11,
          runs_seq_iff.mpr (Or.inr ⟨st12, _, _, e12,
          runs_seq_iff.mpr (Or.inr ⟨st13, _, _, e13,
          runs_seq_iff.mpr (Or.inr ⟨st14, _, _, e14,
          runs_seq_iff.mpr (Or.inr ⟨stC1, _, _, ec1,
          runs_seq_iff.mpr (Or.inr ⟨stS1, _, _, es1,
          runs_seq_iff.mpr (Or.inr ⟨st14', _, _, e14',
          runs_seq_iff.mpr (Or.inr ⟨stC2, _, _, ec2, es2, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
        simp only [argsSize, Expr.size]; omega
      obtain ⟨cT, hthenRun, hcT⟩ := hthen
      have hbody : Runs w p ω
          (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
           .store (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.reg 9) ;;
           .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
           .cond (.reg 10)
             (.assign 11 (.bin .sub (.reg 10) (.const 1)) ;;
              .assign 12 (.load (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9)))) ;;
              .assign 13 (.load (.bin .add (.reg 7) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1)))) ;;
              .assign 14 (.reg 5) ;;
              .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 12, .reg 5] ;;
              .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 1)) (.load (.reg 14)) ;;
              .assign 14 (.reg 5) ;;
              .call 5 (bBun + bundleIdxReadParent) [.reg 0, .reg 1, .reg 11, .reg 13, .reg 5] ;;
              .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 8))) (.const 2)) (.load (.reg 14)))
             .nop) st .normal stS2 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha9,
          runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hs_e,
          runs_seq_iff.mpr (Or.inr ⟨st3, _, _, ha10,
            runs_cond_iff.mpr ⟨es, cT,
              Expr.eval_reg_of_eq (show st3.regs 10 = es by dsimp [st3]; exact Function.update_self 10 es st2.regs),
              by split_ifs; exact hthenRun, rfl⟩,
            rfl⟩), rfl⟩), rfl⟩)
      have hfr_all : ∀ a < h + 3 * delEdges.length, ¬ htour.rep.foot tourH tx₀ a →
          a ≠ h + 3 * i → a ≠ h + 3 * i + 1 → a ≠ h + 3 * i + 2 → mem3 a = st.mem a := fun a ha hnt hne0 hne1 hne2 => by
        have hnt1 : ¬ htour.rep.foot tourH tx a := fun hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; exact hnt h0; omega
        have hnt2 : ¬ htour.rep.foot tourH tx1 a := fun hT => by rcases hftT2 a hT with h0 | ⟨hlo, _⟩; exact hnt h0; omega
        rw [hmem3_ne a hne2, hfr2 a (by omega) hnt2, hmem2_ne a hne1, hfr1 a (by omega) hnt1, hmem1_ne a hne0]
      refine ⟨stS2, _, tx2, hbody, by simp [stS2, stC2, st14', stS1, stC1, st14, st13, st12, st11, st3, st2, st1, hr8], ?_, rfl, ?_⟩
      · refine ⟨hp2, fun r hr hr5' => by
            simp [stS2, stC2, st14', stS1, stC1, st14, st13, st12, st11, st3, st2, st1,
              Function.update_of_ne (by omega : r ≠ 8), Function.update_of_ne hr5',
              Function.update_of_ne (by omega : r ≠ 14), Function.update_of_ne (by omega : r ≠ 13),
              Function.update_of_ne (by omega : r ≠ 12), Function.update_of_ne (by omega : r ≠ 11),
              Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 9), hregs r hr hr5'],
          by simp, by simp [stS2, stC2], by omega,
          by have h2q : 2 * (i + 1) * TS.querySpace = 2 * i * TS.querySpace + 2 * TS.querySpace := by ring
             omega,
          fun a ha => (hmem3_ne a (by omega)).trans (hz2 a ha),
          fun i' hi1 hi2 => by
            have hnt_a : ∀ a, h + 3 * i' ≤ a → a < h + 3 * i' + 3 → ¬ htour.rep.foot tourH tx₀ a :=
              fun a ha1 _ hT => by have := hfootT a hT; omega
            exact ⟨(hfr_all _ (by omega) (hnt_a _ (le_refl _) (by omega)) (by omega) (by omega) (by omega)).trans (hrem0 i' (by omega) hi2).1,
              (hfr_all _ (by omega) (hnt_a _ (by omega) (by omega)) (by omega) (by omega) (by omega)).trans (hrem0 i' (by omega) hi2).2.1,
              (hfr_all _ (by omega) (hnt_a _ (by omega) (by omega)) (by omega) (by omega) (by omega)).trans (hrem0 i' (by omega) hi2).2.2⟩,
          hrepB3', hrepT3', hftT3,
          fun a ha hnt => (hfr_all a (by omega) hnt (by omega) (by omega) (by omega)).trans (hfr_i a ha hnt),
          fun i' hi' hi_lt => ?_⟩
        by_cases hlt' : i' < i
        · obtain ⟨h0', h1', h2', hp'⟩ := hdone_i i' hlt' hi_lt
          have hnt_a : ∀ a, h + 3 * i' ≤ a → a < h + 3 * i' + 3 → ¬ htour.rep.foot tourH tx₀ a :=
            fun a ha1 _ hT => by have := hfootT a hT; omega
          have heq0 := hfr_all (h + 3 * i') (by omega) (hnt_a _ (le_refl _) (by omega)) (by omega) (by omega) (by omega)
          have heq1 := hfr_all (h + 3 * i' + 1) (by omega) (hnt_a _ (by omega) (by omega)) (by omega) (by omega) (by omega)
          have heq2 := hfr_all (h + 3 * i' + 2) (by omega) (hnt_a _ (by omega) (by omega)) (by omega) (by omega) (by omega)
          exact ⟨heq0.trans h0', by change mem3 _ < _; rw [heq1]; exact h1', by change mem3 _ < _; rw [heq2]; exact h2',
            fun js' B' hSB' heB' => ⟨heq1.trans (hp' js' B' hSB' heB').1, heq2.trans (hp' js' B' hSB' heB').2⟩⟩
        · have heq : i' = i := by omega
          subst heq
          have hnt0 : ¬ htour.rep.foot tourH tx₀ (h + 3 * i') := fun hT => by have := hfootT _ hT; omega
          have hnt1 : ¬ htour.rep.foot tourH tx₀ (h + 3 * i' + 1) := fun hT => by have := hfootT _ hT; omega
          have h0_eq : mem3 (h + 3 * i') = e := by
            have hnt_a1 : ¬ htour.rep.foot tourH tx (h + 3 * i') := fun hT => by rcases hftT_i _ hT with h0 | ⟨hlo, _⟩; exact hnt0 h0; omega
            have hnt_a2 : ¬ htour.rep.foot tourH tx1 (h + 3 * i') := fun hT => by rcases hftT2 _ hT with h0 | ⟨hlo, _⟩; exact hnt0 h0; omega
            rw [hmem3_ne _ (by omega), hfr2 _ (by omega) hnt_a2, hmem2_ne _ (by omega), hfr1 _ (by omega) hnt_a1]
            exact Function.update_self _ _ _
          have h1_eq : mem3 (h + 3 * i' + 1) = pT := by
            have hnt_a2 : ¬ htour.rep.foot tourH tx1 (h + 3 * i' + 1) := fun hT => by rcases hftT2 _ hT with h0 | ⟨hlo, _⟩; exact hnt1 h0; omega
            rw [hmem3_ne _ (by omega), hfr2 _ (by omega) hnt_a2]
            exact Function.update_self _ _ _
          have h2_eq : mem3 (h + 3 * i' + 2) = pF := Function.update_self _ _ _
          refine ⟨h0_eq, by change mem3 _ < _; rw [h1_eq]; exact hpT_w, by change mem3 _ < _; rw [h2_eq]; exact hpF_w, fun js' B' hSB' heB' => ?_⟩
          have hjs_eq : js' = js := by
            by_contra hne
            exact Finset.disjoint_left.mp (hrepB1.1.2.2.2.2.2.2.2.2.2.2.2.2.1 js' js hne B' B hSB' hSjs) heB' heB
          subst hjs_eq
          have hB_eq : B' = B := Option.some.inj (hSB'.symm.trans hSjs)
          subst hB_eq
          exact ⟨h1_eq, h2_eq⟩
      · dsimp only [Φ, stS2, Expr.size]
        rw [hphiT3']
        rw [hphiB_eq1] at hc1; rw [hphiB_eq2] at hc2
        rw [hphiT1] at hc1; rw [hphiT2'] at hc2
        have hr1 : (2 * TS.mul) * ordStoreLog eCap = 2 * (TS.mul * ordStoreLog eCap) := by ring
        omega
  -- Invoke `forRange_amort`
  obtain ⟨stLoop, cLoop, tx', hrunLoop, ⟨hEnd, hregsE, _, hr5E, hhLo, hhHi, hzE, _, hrepBE, hrepTE, hftTE, hfrE, hdoneE⟩, hcostLoop⟩ :=
    forRange_amort (ω := ω) Inv Φ (fun _ => 2 * TS.mul * ordStoreLog eCap + 245)
      delEdges.length h1w (by omega) hInitInv
      (fun _ _ _ _ ⟨_, _, hr8, _⟩ => hr8)
      (fun _ _ _ _ ⟨_, hregs, _⟩ => Expr.eval_reg_of_eq ((hregs 3 (by decide) (by decide)).trans (by simp [stC, stB, stA, st0, startState])))
      hStep
  have hret : Runs w p ω (.ret (.reg 5)) stLoop (.returned hEnd) stLoop 2 :=
    runs_ret_iff.mpr ⟨hEnd, Expr.eval_reg_of_eq hr5E, rfl, rfl, rfl⟩
  have hfull := runs_seq_iff.mpr (Or.inr ⟨stA, _, _, ha5,
    runs_seq_iff.mpr (Or.inr ⟨stB, _, _, ha6,
    runs_seq_iff.mpr (Or.inr ⟨stC, _, _, ha7,
    runs_seq_iff.mpr (Or.inr ⟨stLoop, _, _, hrunLoop, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  set dels := readDelTriples stLoop.mem h delEdges.length
  have hdels_len : dels.length = delEdges.length := by simp [dels, readDelTriples]
  have hdels_fst : dels.map Prod.fst = delEdges := by
    refine List.ext_getElem (by simp [dels, readDelTriples]) fun i hi1 hi2 => ?_
    simp only [dels, readDelTriples, List.getElem_map, List.getElem_range]
    exact (hdoneE i hi2 hi2).1
  have hrc_const : rangeCost (fun _ => 2 * TS.mul * ordStoreLog eCap + 245) 0 delEdges.length =
      delEdges.length * (2 * TS.mul * ordStoreLog eCap + 245) := by
    have haux : ∀ k i, k = delEdges.length - i → i ≤ delEdges.length →
        rangeCost (fun _ => 2 * TS.mul * ordStoreLog eCap + 245) i delEdges.length =
          k * (2 * TS.mul * ordStoreLog eCap + 245) := by
      intro k; induction k with
      | zero =>
        intro i hk hi
        have heq : i = delEdges.length := by omega
        subst heq; rw [rangeCost_of_le (le_refl _)]; simp
      | succ k ih => intro i hk hi; rw [rangeCost_step (by omega), ih (i + 1) (by omega) (by omega)]; ring
    exact haux delEdges.length 0 (by omega) (Nat.zero_le _)
  refine ⟨hEnd, stLoop, _, tx', dels, hfull, hdels_len, hdels_fst, rfl, ?_, ?_,
    hrepBE, hrepTE, hhLo, by unfold buildDelTriplesSpace; omega, hzE, hftTE, hfrE,
    fun a ha => hfrE a (hfootB a ha) (hdisjBT a ha), ?_⟩
  · intro trD htrD
    rw [List.mem_iff_getElem] at htrD; rcases htrD with ⟨i, hi, rfl⟩
    have hi' : i < delEdges.length := by simpa [hdels_len] using hi
    obtain ⟨h0, h1, h2, _⟩ := hdoneE i hi' hi'
    simp only [dels, readDelTriples, List.getElem_map, List.getElem_range]
    exact ⟨h0.symm ▸ hDel_cap _ (List.getElem_mem hi'), h1, h2⟩
  · intro i hi js B hSB heB
    have hi' : i < delEdges.length := by simpa [hdels_len] using hi
    obtain ⟨h0, _, _, hp'⟩ := hdoneE i hi' hi'
    simp only [dels, readDelTriples, List.getElem_map, List.getElem_range] at heB ⊢
    rw [h0] at heB ⊢; exact hp' js B hSB heB
  · dsimp only [Φ, buildDelTriplesCost, Expr.size, stC, stB, stA, st0, startState] at hcostLoop ⊢
    rw [hrc_const] at hcostLoop
    have : delEdges.length * (2 * TS.mul * ordStoreLog eCap + 245) + delEdges.length * 9 ≤
        (2 * TS.mul * ordStoreLog eCap + 280) * delEdges.length := by nlinarith
    omega

end

end MinCostFlow.SparseCore.Program
