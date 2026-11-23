module

public import MinCostFlow.SparseCore.Program.TourGraphEq
public import MinCostFlow.SparseCore.Program.TourAsmBridge
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchInitIface
import Mathlib.Tactic

/-!
# Tour Initialization at Branch Init (`TourBranchInit`)

Provides the deterministic WordRAM procedures and verified run theorems needed by the first phase
of branch initialization (`AsmBrCoreInitAt`, `AssemblyBranchInitIface.lean`):
1. `tourBranchInitStmt` / `tourBranchInit_runs`: reads the forest edges and roots from P4's
   `CompBranchExportAt` at `expPtr`, calls `tourInit b` on the compacted order at `cOrdPtr`, and
   builds `(asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap)` with unmarked state
   `⟨outCoreOrder tr ord, ∅⟩` in linear space `tourBranchInitSpace vCap eCap`.
2. `tourMarkExportStmt` / `tourMarkExport_runs`: marks both ends of every edge in an `ExportAt`
   of `S` (`S.E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E`) via `tourOp b 7`, transitioning from unmarked
   state to `OutMarksOf sTour (outCoreOrder tr ord) S.E` with zero footprint growth and zero heap
   growth.
3. `tourBranchInitMarkedStmt` / `tourBranchInitMarked_runs` / `tourBranchInit_cost_le_machCost`:
   composes (1) and (2) directly into the exact postcondition shape of `AsmBrCoreInitAt`
   (`(asmBrTourView tourAsmRep ⟨tr₀, ord, vCap, eCap⟩ vCap eCap).rep tourH sTour xTour st'.mem ∧
   OutMarksOf sTour (outCoreOrder tr₀ ord) tr₀.S_cur.E`), with cost bounded by a constant multiple
   of `capExp * tr₀.machCost`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Helper: `OrdListAt` and `readTriples` memory agreement -/

private theorem readOrdRecords_congr {mem₁ mem₂ : ℕ → ℕ} :
    ∀ n a, (∀ k, a ≤ k → k < a + ordRecordsWords (readOrdRecords mem₁ n a) → mem₁ k = mem₂ k) →
      readOrdRecords mem₂ n a = readOrdRecords mem₁ n a
  | 0, _, _ => rfl
  | n + 1, a, hag => by
    have hw_eq : ordRecordsWords (readOrdRecords mem₁ (n + 1) a) =
        2 + mem₁ (a + 1) + ordRecordsWords (readOrdRecords mem₁ n (a + 2 + mem₁ (a + 1))) := by
      simp [readOrdRecords, ordRecordsWords, readList]
    have h0 : mem₂ a = mem₁ a := (hag a (le_refl _) (by omega)).symm
    have h1 : mem₂ (a + 1) = mem₁ (a + 1) := (hag (a + 1) (by omega) (by omega)).symm
    have hlen : ∀ i < mem₁ (a + 1), mem₂ (a + 2 + i) = mem₁ (a + 2 + i) := fun i hi =>
      (hag (a + 2 + i) (by omega) (by omega)).symm
    have hrl : readList mem₂ (a + 2) (mem₁ (a + 1)) = readList mem₁ (a + 2) (mem₁ (a + 1)) := by
      simp only [readList]
      exact List.map_congr_left fun i hi => hlen i (List.mem_range.mp hi)
    have hrest : readOrdRecords mem₂ n (a + 2 + mem₁ (a + 1)) =
        readOrdRecords mem₁ n (a + 2 + mem₁ (a + 1)) :=
      readOrdRecords_congr n (a + 2 + mem₁ (a + 1)) fun k hk1 hk2 => hag k (by omega) (by omega)
    simp only [readOrdRecords, h0, h1, hrl, hrest]

private theorem ordListAt_of_agree_lt {mem₁ mem₂ : ℕ → ℕ} {a words h : ℕ} {ord : ℕ → List End}
    (hOrd : OrdListAt mem₁ a ord words) (hle : a + words ≤ h)
    (hag : ∀ k < h, mem₂ k = mem₁ k) :
    OrdListAt mem₂ a ord words ∧ readOrdRecordsAt mem₂ a = readOrdRecordsAt mem₁ a := by
  obtain ⟨hnd, hread, hw⟩ := hOrd
  have ha0 : mem₂ a = mem₁ a := hag a (by omega)
  have hrecs : readOrdRecordsAt mem₂ a = readOrdRecordsAt mem₁ a := by
    unfold readOrdRecordsAt
    rw [ha0]
    exact readOrdRecords_congr (mem₁ a) (a + 1) fun k hk1 hk2 =>
      (hag k (by unfold readOrdRecordsAt at hw; omega)).symm
  refine ⟨⟨?_, ?_, ?_⟩, hrecs⟩
  · rw [hrecs]; exact hnd
  · unfold readOrd; rw [hrecs]; exact hread
  · rw [hrecs]; exact hw

/-! ## Step 1: Unmarked tour initialization (`tourBranchInitStmt`) -/

/-- Copy `nE` edge IDs (stride 3) from `r7` to `r10 + 1` (regs: `r6 = nE`, `r7 = ePtr`,
`r10 = fePtr`, loop var `r13`, scratch `r14`). -/
def tourCopyForestEdgesLoop : Stmt :=
  forRange 13 (.const 0) (.reg 6)
    (.assign 14 (.load (.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 13)))) ;;
     .store (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 13)) (.reg 14))

/-- Copy `nR` roots (stride 1) from `r8` to `r11 + 1` (regs: `r9 = nR`, `r8 = rootsPtr`,
`r11 = rsPtr`, loop var `r13`, scratch `r14`). -/
def tourCopyRootsLoop : Stmt :=
  forRange 13 (.const 0) (.reg 9)
    (.assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
     .store (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 13)) (.reg 14))

/-- Deterministic wrapper around `tourInit b` (`[vCap, eCap, cOrdPtr, expPtr, h]`):
extracts length-prefixed forest-edge and root lists from P4's `CompBranchExportAt` at `expPtr`,
stores `tourH := h + 3 + nE + nR` at `mem h`, calls `fTourInit`, and returns `hEnd`. -/
def tourBranchInitStmt (fTourInit : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.const 2))) ;;
  .assign 7 (.load (.bin .add (.reg 5) (.const 3))) ;;
  .assign 8 (.load (.bin .add (.reg 3) (.const 2))) ;;
  .assign 9 (.load (.bin .add (.reg 3) (.const 3))) ;;
  .assign 10 (.bin .add (.reg 4) (.const 1)) ;;
  .assign 11 (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 6)) ;;
  .assign 12 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 9)) ;;
  .store (.reg 4) (.reg 12) ;;
  .store (.reg 10) (.reg 6) ;;
  tourCopyForestEdgesLoop ;;
  .store (.reg 11) (.reg 9) ;;
  tourCopyRootsLoop ;;
  .call 15 fTourInit [.reg 0, .reg 1, .reg 2, .reg 10, .reg 11, .reg 12] ;;
  .ret (.reg 15)

theorem tourBranchInitStmt_noRand (fTourInit : ℕ) : (tourBranchInitStmt fTourInit).NoRand := by
  simp [tourBranchInitStmt, tourCopyForestEdgesLoop, tourCopyRootsLoop, forRange, forUp, Stmt.NoRand]

/-- Linear heap space bound for `tourBranchInitStmt` (and `tourBranchInitMarkedStmt`), independent
of `h`. -/
def tourBranchInitSpace (vCap eCap : ℕ) : ℕ :=
  3 + eCap + vCap + tourFixedSize vCap eCap + ordArenaSize vCap eCap + 5

/-- Cost multiplier for `tourBranchInitStmt`. -/
def tourBranchInitMul : ℕ := tourMul + 500

private theorem tourCopyForestEdgesLoop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {nE ePtr fePtr h : ℕ} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w) (hnE_w : nE < 2 ^ w)
    (_he_w : ePtr + 3 * nE < 2 ^ w) (hfe_w : fePtr + 1 + nE < 2 ^ w)
    (he_lt : ePtr + 3 * nE ≤ h) (hfe_ge : h < fePtr)
    (hr6 : st₀.regs 6 = nE) (hr7 : st₀.regs 7 = ePtr) (hr10 : st₀.regs 10 = fePtr) :
    ∃ st' c,
      Runs w p ω tourCopyForestEdgesLoop st₀ .normal st' c ∧
      (∀ r, r ≠ 13 → r ≠ 14 → st'.regs r = st₀.regs r) ∧
      (∀ i < nE, st'.mem (fePtr + 1 + i) = st₀.mem (ePtr + 3 * i)) ∧
      (∀ a, (a < fePtr + 1 ∨ fePtr + 1 + nE ≤ a) → st'.mem a = st₀.mem a) ∧
      c ≤ 30 * nE + 15 := by
  let Inv : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r, r ≠ 13 → r ≠ 14 → st.regs r = st₀.regs r) ∧
    st.regs 13 = i ∧
    (∀ j < i, st.mem (fePtr + 1 + j) = st₀.mem (ePtr + 3 * j)) ∧
    (∀ a, (a < fePtr + 1 ∨ fePtr + 1 + i ≤ a) → st.mem a = st₀.mem a)
  obtain ⟨st', c, _, hrun, hInv, hc⟩ :=
    runs_forRange_pot (w := w) (p := p) (ω := ω) (r := 13) (lo := .const 0) (hi := .reg 6)
      (phi := fun _ _ => 0) (Inv := Inv) (stepCost := fun _ => 20) nE (by omega)
      (fun _ => by omega) (st₀ := st₀) (a₀ := ())
      ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
       ⟨fun r hr13 _ => by simp [Function.update_of_ne hr13], by simp,
        fun _ hj => by omega, fun _ _ => rfl⟩, rfl⟩
      (fun _ _ _ _ hI => hI.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 6 (by decide) (by decide), hr6])
      (fun i _ st hi ⟨hregs, hr13, hdone, hfr⟩ => by
        set val := st₀.mem (ePtr + 3 * i)
        have hsrc : st.mem (ePtr + 3 * i) = val := hfr _ (Or.inl (by omega))
        set st1 : State := { st with regs := Function.update st.regs 14 val }
        have ha14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 13)))))
            st .normal st1 7 :=
          runs_assign_iff.mpr ⟨val, by
            simp [Expr.eval, BinOp.eval, hregs 7 (by decide) (by decide), hr7, hr13, hsrc,
              show 3 < 2 ^ w by omega, show 3 * i < 2 ^ w by omega, show ePtr + 3 * i < 2 ^ w by omega],
            rfl, rfl, by simp [Expr.size]⟩
        set st2 : State := { st1 with mem := Function.update st.mem (fePtr + 1 + i) val }
        have hst : Runs w p ω (.store (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 13)) (.reg 14))
            st1 .normal st2 7 :=
          runs_store_iff.mpr ⟨fePtr + 1 + i, val, by
            simp [Expr.eval, BinOp.eval, st1, hregs 10 (by decide) (by decide), hr10, hr13,
              show 1 < 2 ^ w by omega, show fePtr + 1 < 2 ^ w by omega,
              show fePtr + 1 + i < 2 ^ w by omega],
            by simp [Expr.eval, st1], rfl, rfl, by simp [Expr.size]⟩
        refine ⟨st2, 15, (), tour_runs_seq_normal ha14 hst, by simp [st2, st1, hr13],
          ⟨fun r h13 h14 => by
              simp [st2, st1, Function.update_of_ne h13, Function.update_of_ne h14, hregs r h13 h14],
           by simp,
           fun j hj => by
             by_cases hji : j = i
             · subst hji; simp [st2, val]
             · simp [st2, Function.update_of_ne (show fePtr + 1 + j ≠ fePtr + 1 + i by omega),
                 hdone j (by omega)],
           fun a ha => by
             simp only [st2]
             rw [Function.update_of_ne (by omega)]
             exact hfr a (by omega)⟩, rfl, by omega⟩)
  have hrc : rangeCost (fun _ => 20) 0 nE = 20 * nE := by unfold rangeCost; simp [Nat.mul_comm]
  rw [hrc] at hc; simp only [Expr.size] at hc
  exact ⟨st', c, hrun, hInv.1, hInv.2.2.1, hInv.2.2.2, by omega⟩

private theorem tourCopyRootsLoop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {nR rootsPtr rsPtr h : ℕ} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w) (hnR_w : nR < 2 ^ w)
    (_hr_w : rootsPtr + nR < 2 ^ w) (hrs_w : rsPtr + 1 + nR < 2 ^ w)
    (hr_lt : rootsPtr + nR ≤ h) (hrs_ge : h < rsPtr)
    (hr8 : st₀.regs 8 = rootsPtr) (hr9 : st₀.regs 9 = nR) (hr11 : st₀.regs 11 = rsPtr) :
    ∃ st' c,
      Runs w p ω tourCopyRootsLoop st₀ .normal st' c ∧
      (∀ r, r ≠ 13 → r ≠ 14 → st'.regs r = st₀.regs r) ∧
      (∀ i < nR, st'.mem (rsPtr + 1 + i) = st₀.mem (rootsPtr + i)) ∧
      (∀ a, (a < rsPtr + 1 ∨ rsPtr + 1 + nR ≤ a) → st'.mem a = st₀.mem a) ∧
      c ≤ 30 * nR + 15 := by
  let Inv : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r, r ≠ 13 → r ≠ 14 → st.regs r = st₀.regs r) ∧
    st.regs 13 = i ∧
    (∀ j < i, st.mem (rsPtr + 1 + j) = st₀.mem (rootsPtr + j)) ∧
    (∀ a, (a < rsPtr + 1 ∨ rsPtr + 1 + i ≤ a) → st.mem a = st₀.mem a)
  obtain ⟨st', c, _, hrun, hInv, hc⟩ :=
    runs_forRange_pot (w := w) (p := p) (ω := ω) (r := 13) (lo := .const 0) (hi := .reg 9)
      (phi := fun _ _ => 0) (Inv := Inv) (stepCost := fun _ => 18) nR (by omega)
      (fun _ => by omega) (st₀ := st₀) (a₀ := ())
      ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
       ⟨fun r hr13 _ => by simp [Function.update_of_ne hr13], by simp,
        fun _ hj => by omega, fun _ _ => rfl⟩, rfl⟩
      (fun _ _ _ _ hI => hI.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 9 (by decide) (by decide), hr9])
      (fun i _ st hi ⟨hregs, hr13, hdone, hfr⟩ => by
        set val := st₀.mem (rootsPtr + i)
        have hsrc : st.mem (rootsPtr + i) = val := hfr _ (Or.inl (by omega))
        set st1 : State := { st with regs := Function.update st.regs 14 val }
        have ha14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 8) (.reg 13))))
            st .normal st1 5 :=
          runs_assign_iff.mpr ⟨val, by
            simp [Expr.eval, BinOp.eval, hregs 8 (by decide) (by decide), hr8, hr13, hsrc,
              show rootsPtr + i < 2 ^ w by omega],
            rfl, rfl, by simp [Expr.size]⟩
        set st2 : State := { st1 with mem := Function.update st.mem (rsPtr + 1 + i) val }
        have hst : Runs w p ω (.store (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 13)) (.reg 14))
            st1 .normal st2 7 :=
          runs_store_iff.mpr ⟨rsPtr + 1 + i, val, by
            simp [Expr.eval, BinOp.eval, st1, hregs 11 (by decide) (by decide), hr11, hr13,
              show 1 < 2 ^ w by omega, show rsPtr + 1 < 2 ^ w by omega,
              show rsPtr + 1 + i < 2 ^ w by omega],
            by simp [Expr.eval, st1], rfl, rfl, by simp [Expr.size]⟩
        refine ⟨st2, 13, (), tour_runs_seq_normal ha14 hst, by simp [st2, st1, hr13],
          ⟨fun r h13 h14 => by
              simp [st2, st1, Function.update_of_ne h13, Function.update_of_ne h14, hregs r h13 h14],
           by simp,
           fun j hj => by
             by_cases hji : j = i
             · subst hji; simp [st2, val]
             · simp [st2, Function.update_of_ne (show rsPtr + 1 + j ≠ rsPtr + 1 + i by omega),
                 hdone j (by omega)],
           fun a ha => by
             simp only [st2]
             rw [Function.update_of_ne (by omega)]
             exact hfr a (by omega)⟩, rfl, by omega⟩)
  have hrc : rangeCost (fun _ => 18) 0 nR = 18 * nR := by unfold rangeCost; simp [Nat.mul_comm]
  rw [hrc] at hc; simp only [Expr.size] at hc
  exact ⟨st', c, hrun, hInv.1, hInv.2.2.1, hInv.2.2.2, by omega⟩

/-- **Unmarked branch tour initialization (`tourBranchInitStmt`)**: from `cOrdPtr` (`OrdListAt`)
and P4's branch export `expPtr` (`CompBranchExportAt`), builds the tour of `tourAsmRep` with
`asmBrTourView` holding `⟨outCoreOrder tr ord, ∅⟩`, handle stored at `mem h`, footprint inside
`[h, o.value)`, linear space `tourBranchInitSpace vCap eCap`, and cost
`≤ tourBranchInitMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap`. -/
theorem tourBranchInit_runs {depth w b L capExp M N vCap eCap cOrdPtr expPtr expEnd h cWords pos : ℕ}
    {p : Program} (hp : HasTourProcs p b) (ω : ℕ → Bool)
    {tr : BundleTreeState depth} {ord : ℕ → List End} {mem : ℕ → ℕ}
    (hRot : HasRotOrder tr ord)
    (hVlt : ∀ v ∈ tr.cs.G.V, v < vCap) (hElt : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hOrdAt : OrdListAt mem cOrdPtr ord cWords) (hOrdLe : cOrdPtr + cWords ≤ h)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hExpLe : expEnd ≤ h)
    (hz : ZeroFrom mem h) (hsp : h + tourBranchInitSpace vCap eCap < 2 ^ w) :
    ∃ o st' c tourH xTour,
      Runs w p ω (tourBranchInitStmt (tourInit b))
        (startState [vCap, eCap, cOrdPtr, expPtr, h] mem pos) o st' c ∧
      st'.mem h = tourH ∧ h < tourH ∧ tourH < o.value ∧
      (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH
        ⟨outCoreOrder tr ord, ∅⟩ xTour st'.mem ∧
      OutMarksOf ⟨outCoreOrder tr ord, ∅⟩ (outCoreOrder tr ord) ∅ ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → tourH ≤ a ∧ a < o.value) ∧
      h ≤ o.value ∧ o.value + 2 ≤ h + tourBranchInitSpace vCap eCap ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem a) ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour st'.mem ≤
        tourBranchInitMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap := by
  obtain ⟨_, _, hI, ρ, hρ⟩ := id hRot
  have hF := compLSF_RF_isRSF hI
  rcases hExp with ⟨hexp8, _, _, _, hfD_ge, hfExp, ⟨roots, hrLen, hrNd, hrFs, hrLA, hrLo, hrHi⟩, _⟩
  set fD := mem (expPtr + 1)
  set nE := mem (fD + 2)
  set ePtr := mem (fD + 3)
  set rootsPtr := mem (expPtr + 2)
  set nR := mem (expPtr + 3)
  obtain ⟨_, hnE_eq, _, _, heNd, heIn, heAll, hfD4, _, heLo, _, heHi⟩ := hfExp
  have hnE_le_Gm : nE ≤ tr.cs.G.m := by
    dsimp only [nE]; rw [hnE_eq]
    exact Finset.card_le_card hF.2.2.2.2.2.1
  have hnE_le_eCap : nE ≤ eCap := by
    calc nE ≤ tr.cs.G.m := hnE_le_Gm
      _ ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hElt e he)
      _ = eCap := Finset.card_range _
  have hnR_le_Gn : nR ≤ tr.cs.G.n := by
    rw [← hrLen, ← List.toFinset_card_of_nodup hrNd, hrFs]
    exact Finset.card_le_card hF.2.2.1
  have hnR_le_vCap : nR ≤ vCap := by
    calc nR ≤ tr.cs.G.n := hnR_le_Gn
      _ ≤ (Finset.range vCap).card :=
          Finset.card_le_card fun v hv => Finset.mem_range.mpr (hVlt v hv)
      _ = vCap := Finset.card_range _
  have hw16 : 16 ≤ 2 ^ w := by simp [tourBranchInitSpace, tourFixedSize, ordArenaSize] at hsp; omega
  set fePtr := h + 1
  set rsPtr := h + 2 + nE
  set tourH := h + 3 + nE + nR
  have htourH_sp : tourH + (tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3) < 2 ^ w := by
    unfold tourBranchInitSpace at hsp; omega
  set st0 := startState [vCap, eCap, cOrdPtr, expPtr, h] mem pos
  set r5 := Function.update st0.regs 5 fD
  set r6 := Function.update r5 6 nE
  set r7 := Function.update r6 7 ePtr
  set r8 := Function.update r7 8 rootsPtr
  set r9 := Function.update r8 9 nR
  set r10 := Function.update r9 10 fePtr
  set r11 := Function.update r10 11 rsPtr
  set r12 := Function.update r11 12 tourH
  set m1 := Function.update mem h tourH
  set m2 := Function.update m1 fePtr nE
  have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 3) (.const 1)))) st0 .normal { st0 with regs := r5 } 5 :=
    runs_assign_iff.mpr ⟨fD, by simp [Expr.eval, BinOp.eval, st0, startState, show 1 < 2 ^ w by omega, show expPtr + 1 < 2 ^ w by omega, fD], rfl, rfl, rfl⟩
  have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 5) (.const 2)))) { st0 with regs := r5 } .normal { st0 with regs := r6 } 5 :=
    runs_assign_iff.mpr ⟨nE, by simp [Expr.eval, BinOp.eval, r5, st0, startState, show 2 < 2 ^ w by omega, show fD + 2 < 2 ^ w by omega, nE], rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 5) (.const 3)))) { st0 with regs := r6 } .normal { st0 with regs := r7 } 5 :=
    runs_assign_iff.mpr ⟨ePtr, by simp [Expr.eval, BinOp.eval, r6, r5, st0, startState, show 3 < 2 ^ w by omega, show fD + 3 < 2 ^ w by omega, ePtr], rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 3) (.const 2)))) { st0 with regs := r7 } .normal { st0 with regs := r8 } 5 :=
    runs_assign_iff.mpr ⟨rootsPtr, by simp [Expr.eval, BinOp.eval, r7, r6, r5, st0, startState, show 2 < 2 ^ w by omega, show expPtr + 2 < 2 ^ w by omega, rootsPtr], rfl, rfl, rfl⟩
  have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 3) (.const 3)))) { st0 with regs := r8 } .normal { st0 with regs := r9 } 5 :=
    runs_assign_iff.mpr ⟨nR, by simp [Expr.eval, BinOp.eval, r8, r7, r6, r5, st0, startState, show 3 < 2 ^ w by omega, show expPtr + 3 < 2 ^ w by omega, nR], rfl, rfl, rfl⟩
  have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 4) (.const 1))) { st0 with regs := r9 } .normal { st0 with regs := r10 } 4 :=
    runs_assign_iff.mpr ⟨fePtr, by simp [Expr.eval, BinOp.eval, r9, r8, r7, r6, r5, st0, startState, show 1 < 2 ^ w by omega, show h + 1 < 2 ^ w by omega, fePtr], rfl, rfl, rfl⟩
  have ha11 : Runs w p ω (.assign 11 (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 6))) { st0 with regs := r10 } .normal { st0 with regs := r11 } 6 :=
    runs_assign_iff.mpr ⟨rsPtr, by
      simp [Expr.eval, BinOp.eval, r10, r9, r8, r7, r6,
        show 1 < 2 ^ w by omega, show fePtr + 1 < 2 ^ w by omega,
        show fePtr + 1 + nE < 2 ^ w by omega]; omega, rfl, rfl, rfl⟩
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 9))) { st0 with regs := r11 } .normal { st0 with regs := r12 } 6 :=
    runs_assign_iff.mpr ⟨tourH, by
      simp [Expr.eval, BinOp.eval, r11, r10, r9,
        show 1 < 2 ^ w by omega, show rsPtr + 1 < 2 ^ w by omega,
        show rsPtr + 1 + nR < 2 ^ w by omega]; omega, rfl, rfl, rfl⟩
  have hst0 : Runs w p ω (.store (.reg 4) (.reg 12)) { st0 with regs := r12 } .normal { mem := m1, regs := r12, pos := pos } 3 :=
    runs_store_iff.mpr ⟨h, tourH, by simp [Expr.eval, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState], by simp [Expr.eval, r12], rfl, rfl, rfl⟩
  have hst1 : Runs w p ω (.store (.reg 10) (.reg 6)) { mem := m1, regs := r12, pos := pos } .normal { mem := m2, regs := r12, pos := pos } 3 :=
    runs_store_iff.mpr ⟨fePtr, nE, by simp [Expr.eval, r12, r11, r10], by simp [Expr.eval, r12, r11, r10, r9, r8, r7, r6], rfl, rfl, rfl⟩
  obtain ⟨stL1, cL1, hrunL1, hregL1, hfe_cp, hfrL1, hcL1⟩ :=
    tourCopyForestEdgesLoop_runs (w := w) (p := p) (ω := ω)
      (nE := nE) (ePtr := ePtr) (fePtr := fePtr) (h := h)
      (st₀ := { mem := m2, regs := r12, pos := pos })
      hw16 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp [r12, r11, r10, r9, r8, r7, r6]) (by simp [r12, r11, r10, r9, r8, r7])
      (by simp [r12, r11, r10])
  set m3 := Function.update stL1.mem rsPtr nR
  have hst2 : Runs w p ω (.store (.reg 11) (.reg 9)) stL1 .normal { stL1 with mem := m3 } 3 :=
    runs_store_iff.mpr ⟨rsPtr, nR,
      by simp [Expr.eval, hregL1 11 (by decide) (by decide), r12, r11],
      by simp [Expr.eval, hregL1 9 (by decide) (by decide), r12, r11, r10, r9], rfl, rfl, rfl⟩
  obtain ⟨stL2, cL2, hrunL2, hregL2, hrs_cp, hfrL2, hcL2⟩ :=
    tourCopyRootsLoop_runs (w := w) (p := p) (ω := ω)
      (nR := nR) (rootsPtr := rootsPtr) (rsPtr := rsPtr) (h := h)
      (st₀ := { stL1 with mem := m3 })
      hw16 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp [hregL1 8 (by decide) (by decide), r12, r11, r10, r9, r8])
      (by simp [hregL1 9 (by decide) (by decide), r12, r11, r10, r9])
      (by simp [hregL1 11 (by decide) (by decide), r12, r11])
  -- Characterize `stL2.mem`
  have hlt_h : ∀ a < h, stL2.mem a = mem a := fun a ha => by
    rw [hfrL2 a (Or.inl (by omega))]
    dsimp only [m3]; rw [Function.update_of_ne (by omega)]
    rw [hfrL1 a (Or.inl (by omega))]
    dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hmem_h : stL2.mem h = tourH := by
    rw [hfrL2 h (Or.inl (by omega))]
    dsimp only [m3]; rw [Function.update_of_ne (by omega)]
    rw [hfrL1 h (Or.inl (by omega))]
    dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_self]
  have hzero_tourH : ZeroFrom stL2.mem tourH := fun a ha => by
    rw [hfrL2 a (Or.inr (by omega))]
    dsimp only [m3]; rw [Function.update_of_ne (by omega)]
    rw [hfrL1 a (Or.inr (by omega))]
    dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz a (by omega)
  have hfe_len : stL2.mem fePtr = nE := by
    rw [hfrL2 fePtr (Or.inl (by omega))]
    dsimp only [m3]; rw [Function.update_of_ne (by omega)]
    rw [hfrL1 fePtr (Or.inl (by omega))]
    dsimp only [m2]; exact Function.update_self _ _ _
  have hfe_list : readNatList stL2.mem fePtr = (readTriples mem ePtr nE).map Prod.fst := by
    unfold readNatList readList readTriples
    rw [hfe_len, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < nE := List.mem_range.mp hi
    rw [hfrL2 (fePtr + 1 + i) (Or.inl (by omega))]
    dsimp only [m3]; rw [Function.update_of_ne (by omega)]
    rw [hfe_cp i hi']
    dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rfl
  have hrs_len : stL2.mem rsPtr = nR := by
    rw [hfrL2 rsPtr (Or.inl (by omega))]
    dsimp only [m3]; exact Function.update_self _ _ _
  have hrs_list : readNatList stL2.mem rsPtr = roots := by
    apply List.ext_getElem
    · simp [readNatList, readList, hrs_len, hrLen]
    · intro i h1 h2
      have hi : i < nR := by omega
      simp only [readNatList, readList, hrs_len, List.getElem_map, List.getElem_range]
      rw [hrs_cp i hi]
      dsimp only [m3]; rw [Function.update_of_ne (by omega)]
      rw [hfrL1 (rootsPtr + i) (Or.inl (by omega))]
      dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hrLA i (by omega)
  obtain ⟨hOrd2, hrecs2⟩ := ordListAt_of_agree_lt hOrdAt hOrdLe hlt_h
  have hreadOrd2 : readOrd stL2.mem cOrdPtr = ord := hOrd2.2.1
  have hFeNd2 : (readNatList stL2.mem fePtr).Nodup := by rw [hfe_list]; exact heNd
  have hRsNd2 : (readNatList stL2.mem rsPtr).Nodup := by rw [hrs_list]; exact hrNd
  have hfe_fs : (readNatList stL2.mem fePtr).toFinset = tr.cs.lsf.F.F.E := by
    rw [hfe_list]; ext e
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨fun ⟨t, ht, hte⟩ => hte ▸ (heIn t ht).1,
      fun he => let ⟨t, ht, hte⟩ := heAll e he; ⟨t, ht, hte⟩⟩
  have hrs_fs : (readNatList stL2.mem rsPtr).toFinset = tr.cs.lsf.F.R := by
    rw [hrs_list]; exact hrFs
  have hGEq := initTourForest_graphEq_of_rsf ρ hI.hG_val hF hOrd2.1 (hreadOrd2.trans hρ.symm)
    hfe_fs hrs_fs
  have hOrdW : OrdWithin vCap eCap ρ.order :=
    ⟨ρ.nodup,
     fun v hv => by
       cases h : ρ.order v with
       | nil => rfl
       | cons x _ =>
         have hxm : x ∈ ρ.order v := by rw [h]; simp
         obtain ⟨he, hsrc⟩ := (ρ.mem_order v x).mp hxm
         have hvG : v ∈ tr.cs.G.V := by
           rw [← hsrc]; obtain ⟨e, b⟩ := x; cases b
           · exact (hI.hG_val e he).2
           · exact (hI.hG_val e he).1
         exact absurd (hVlt v hvG) (by omega),
     fun v x hx => hElt x.1 ((ρ.mem_order v x).mp hx).1⟩
  have hValid0 : TourValid vCap eCap ⟨ord, tr.cs.lsf.F, ∅⟩ := by
    rw [← hρ]; exact tourValid_of_rotation ρ hI.hG_val hF hOrdW hVlt
  have hValidInit : TourValid vCap eCap
      ⟨readOrd stL2.mem cOrdPtr,
        initTourForest (readOrdRecordsAt stL2.mem cOrdPtr) (readNatList stL2.mem fePtr)
          (readNatList stL2.mem rsPtr), ∅⟩ :=
    tourValid_of_graphEq (s₁ := ⟨ord, tr.cs.lsf.F, ∅⟩) hreadOrd2.symm rfl hGEq.2.symm
      (graphEq_symm hGEq.1) hValid0
  -- Call `tourInit b` via `tourDS_implements`
  have hImpl := (tourDS_implements w vCap eCap p b hp hw).2
  have hInitPre : (tourContract vCap eCap tourMul tourAlloc).initPre
      [vCap, eCap, cOrdPtr, fePtr, rsPtr, tourH] stL2.mem :=
    ⟨cOrdPtr, fePtr, rsPtr, tourH, cWords, rfl, by rwa [hreadOrd2], by omega,
      by rw [hfe_len]; omega, by rw [hrs_len]; omega, hFeNd2, hRsNd2, hValidInit⟩
  have hArgsLt : ∀ a ∈ [vCap, eCap, cOrdPtr, fePtr, rsPtr, tourH], a < 2 ^ w := by
    have hsp_u := htourH_sp
    simp only [tourFixedSize, ordArenaSize] at hsp_u
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨bodyI, hbodyI, oI, stI, cI, hrunI, sI, xI, hrepI, hpostI, hrespI, hcostI⟩ :=
    hImpl.2.1 [vCap, eCap, cOrdPtr, fePtr, rsPtr, tourH] stL2.mem stL2.pos ω hArgsLt hInitPre
      (by simpa [heapArg] using hzero_tourH)
      (by simpa [tourContract, tourAlloc, heapArg] using htourH_sp)
  -- Wire call + return
  have hargsI : evalArgs w stL2 [.reg 0, .reg 1, .reg 2, .reg 10, .reg 11, .reg 12] =
      some [vCap, eCap, cOrdPtr, fePtr, rsPtr, tourH] := by
    have hr0 : stL2.regs 0 = vCap := by rw [hregL2 0 (by decide) (by decide), hregL1 0 (by decide) (by decide)]; simp [r12, r11, r10, r9, r8, r7, r6, r5, st0, startState]
    have hr1 : stL2.regs 1 = eCap := by rw [hregL2 1 (by decide) (by decide), hregL1 1 (by decide) (by decide)]; simp [r12, r11, r10, r9, r8, r7, r6, r5, st0, startState]
    have hr2 : stL2.regs 2 = cOrdPtr := by rw [hregL2 2 (by decide) (by decide), hregL1 2 (by decide) (by decide)]; simp [r12, r11, r10, r9, r8, r7, r6, r5, st0, startState]
    have hr10 : stL2.regs 10 = fePtr := by rw [hregL2 10 (by decide) (by decide), hregL1 10 (by decide) (by decide)]; simp [r12, r11, r10]
    have hr11 : stL2.regs 11 = rsPtr := by rw [hregL2 11 (by decide) (by decide), hregL1 11 (by decide) (by decide)]; simp [r12, r11]
    have hr12 : stL2.regs 12 = tourH := by rw [hregL2 12 (by decide) (by decide), hregL1 12 (by decide) (by decide)]; simp [r12]
    simp [evalArgs, Expr.eval, hr0, hr1, hr2, hr10, hr11, hr12]
  set stCall : State := { stI with regs := Function.update stL2.regs 15 oI.value }
  have hcallI : Runs w p ω (.call 15 (tourInit b) [.reg 0, .reg 1, .reg 2, .reg 10, .reg 11, .reg 12])
      stL2 .normal stCall (argsSize [.reg 0, .reg 1, .reg 2, .reg 10, .reg 11, .reg 12] + cI + 1) :=
    runs_call_iff.mpr ⟨_, bodyI, oI, stI, cI, hargsI, hbodyI, hrunI, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 15)) stCall (.returned oI.value) stCall 2 :=
    runs_ret_iff.mpr ⟨oI.value, by simp [Expr.eval, stCall], rfl, rfl, rfl⟩
  have hrunAll :=
    tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7
      (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10
        (tour_runs_seq_normal ha11 (tour_runs_seq_normal ha12 (tour_runs_seq_normal hst0
          (tour_runs_seq_normal hst1 (tour_runs_seq_normal hrunL1 (tour_runs_seq_normal hst2
            (tour_runs_seq_normal hrunL2 (tour_runs_seq_normal hcallI hret)))))))))))))
  -- Transfer `TourRepAt` from `sI` to `⟨ord, tr.cs.lsf.F, ∅⟩` via `tourRep_of_graphEq`
  have hsI_eq : sI = ⟨readOrd stL2.mem cOrdPtr,
      initTourForest (readOrdRecordsAt stL2.mem cOrdPtr) (readNatList stL2.mem fePtr)
        (readNatList stL2.mem rsPtr), ∅⟩ := by
    simpa [tourContract] using hpostI
  subst hsI_eq
  have hrepFin : TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, tr.cs.lsf.F, ∅⟩ xI stI.mem :=
    tourRep_of_graphEq (s₁ := ⟨readOrd stL2.mem cOrdPtr,
      initTourForest (readOrdRecordsAt stL2.mem cOrdPtr) (readNatList stL2.mem fePtr)
        (readNatList stL2.mem rsPtr), ∅⟩)
      hreadOrd2 rfl hGEq.2 hGEq.1 hrepI
  have hok : TourCordOK ord tr.cs.lsf.F (outCoreOrder tr ord) :=
    ⟨tr.cs, coreCordOf_outCoreOrder hRot, rfl⟩
  have hfoot_bounds : ∀ a, (tourAsmRep vCap eCap).foot tourH xI a → tourH ≤ a ∧ a < oI.value := by
    intro a ha
    have hha : heapArg [vCap, eCap, cOrdPtr, fePtr, rsPtr, tourH] = tourH := by
      simp [heapArg]
    rcases hrespI.2.2.2.2 a ha with hf | hbounds
    · exact False.elim hf
    · rw [hha] at hbounds; exact hbounds
  have htourH_lt : tourH < oI.value := (hfoot_bounds tourH (tourAsmRep_handle_foot vCap eCap tourH xI)).2
  have hha : heapArg [vCap, eCap, cOrdPtr, fePtr, rsPtr, tourH] = tourH := by simp [heapArg]
  have hmem_h' : stI.mem h = tourH := by
    rw [hrespI.2.2.2.1 h (by rw [hha]; omega) (fun hf => hf), hmem_h]
  refine ⟨.returned oI.value, stCall, _, tourH, xI, hrunAll, hmem_h', by omega, htourH_lt,
    ⟨rfl, hok, hrepFin⟩, ⟨rfl, fun z => by simp⟩,
    hfoot_bounds,
    by have := hrespI.1; simp only [Outcome.value, hha] at this ⊢; omega,
    by have := hrespI.2.1; simp only [Outcome.value, tourContract, tourAlloc, hha,
         List.getD_cons_zero, List.getD_cons_succ, tourBranchInitSpace] at this ⊢; omega,
    hrespI.2.2.1,
    fun a ha => by
      rw [hrespI.2.2.2.1 a (by rw [hha]; omega) (fun hf => hf), hlt_h a ha], ?_⟩
  -- Cost arithmetic
  simp only [tourContract, tourDSRep, List.getD_cons_zero, List.getD_cons_succ] at hcostI
  rw [hrecs2, hfe_len, hrs_len] at hcostI
  have hwords_le : ordRecordsWords (readOrdRecordsAt mem cOrdPtr) ≤ cWords := by
    have := hOrdAt.2.2; omega
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hcI_le : cI + (tourAsmRep vCap eCap).phi tourH xI stI.mem ≤
      tourMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap :=
    le_trans hcostI (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
  have h500 : 500 * (1 + cWords + tr.cs.G.m + tr.cs.G.n) ≤
      500 * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap :=
    Nat.le_mul_of_pos_right _ htl
  have hmul_eq : tourBranchInitMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap =
      tourMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap +
      500 * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap := by
    unfold tourBranchInitMul; ring
  simp only [argsSize, Expr.size, stCall] at *
  omega


end MinCostFlow.SparseCore.Program
