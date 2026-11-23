module

public import MinCostFlow.SparseCore.Program.TourBranchInit
import Mathlib.Tactic

/-!
# Marking Exported `S_cur` Edges and Composed Branch Tour Init (`TourBranchInitMark`)

Completes tour initialization for the first phase of branch init (`AsmBrCoreInitAt`,
`AssemblyBranchInitIface.lean`):
* `tourMarkExportStmt` / `tourMarkExport_runs`: marks both ends of every edge in an `ExportAt` of
  `S` (`S.E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E`) via `tourOp b 7`, transitioning from unmarked
  state to `OutMarksOf sTour (outCoreOrder tr ord) S.E` with zero heap and footprint growth.
* `tourBranchInitMarkedStmt` / `tourBranchInitMarked_runs` / `tourBranchInit_cost_le_machCost`:
  composes `tourBranchInitStmt` and `tourMarkExportStmt` directly into the exact postcondition
  shape of `AsmBrCoreInitAt` (`asmBrTourView` + `OutMarksOf` + `machCost` bound).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Step 2: Marking exported `S_cur` edges (`tourMarkExportStmt`) -/

/-- Deterministic procedure (`[tourH, sExp, h]`): loops over all edges `e` in `ExportAt` at `sExp`
and calls `fSetMark` (`tourOp b 7`) on `(e, true)` and `(e, false)` with `flag = 1`. Returns `h`
with zero heap growth and zero tour footprint growth. -/
def tourMarkExportStmt (fSetMark : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 4 (.load (.bin .add (.reg 1) (.const 3))) ;;
  forRange 5 (.const 0) (.reg 3)
    (.assign 6 (.load (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 5)))) ;;
     .call 7 fSetMark [.reg 0, .bin .mul (.const 2) (.reg 6), .const 1, .reg 2] ;;
     .call 7 fSetMark [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 6)) (.const 1), .const 1, .reg 2]) ;;
  .ret (.reg 2)

theorem tourMarkExportStmt_noRand (fSetMark : ℕ) : (tourMarkExportStmt fSetMark).NoRand := by
  simp [tourMarkExportStmt, forRange, forUp, Stmt.NoRand]

/-- Cost multiplier for `tourMarkExportStmt`. -/
def tourMarkExportMul : ℕ := 2 * TOUR_FOREST_MUL + 200

/-- **Marking exported edges (`tourMarkExportStmt`)**: starting from an unmarked tour in
`asmBrTourView`, marks both ends of every edge of `S` (`S.E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E`),
producing `OutMarksOf sTour' (outCoreOrder tr ord) S.E` with zero heap growth and zero tour
footprint growth. -/
theorem tourMarkExport_runs {depth w b vCap eCap tourH sExp sExpEnd h pos : ℕ} {p : Program}
    (hp : HasTourProcs p b) (ω : ℕ → Bool)
    {tr : BundleTreeState depth} {ord : ℕ → List End} {S : MGraph}
    {xTour : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hRot : HasRotOrder tr ord)
    (hS_sub : S.E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E)
    (hS_exp : ExportAt mem sExp sExpEnd S) (hS_le : sExpEnd ≤ h)
    (hS_disj : ∀ a, sExp ≤ a → a < sExpEnd → ¬ (tourAsmRep vCap eCap).foot tourH xTour a)
    (hrep : (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH
      ⟨outCoreOrder tr ord, ∅⟩ xTour mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → a < h)
    (hz : ZeroFrom mem h) (hroom : h + 2 < 2 ^ w) :
    ∃ st' c sTour' xTour',
      Runs w p ω (tourMarkExportStmt (tourOp b 7))
        (startState [tourH, sExp, h] mem pos) (.returned h) st' c ∧
      (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH sTour' xTour' st'.mem ∧
      OutMarksOf sTour' (outCoreOrder tr ord) S.E ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH xTour' a → (tourAsmRep vCap eCap).foot tourH xTour a) ∧
      ZeroFrom st'.mem h ∧
      (∀ a < h, ¬ (tourAsmRep vCap eCap).foot tourH xTour a → st'.mem a = mem a) ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour' st'.mem ≤
        tourMarkExportMul * (S.m + 1) * tourLog eCap +
          (tourAsmRep vCap eCap).phi tourH xTour mem := by
  obtain ⟨_, _, hI, ρ, hρ⟩ := id hRot
  rcases hrep with ⟨_, hok, hR0⟩
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, tr.cs.lsf.F, ∅⟩ xTour mem at hR0
  have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR0 hfoot hroom
  obtain ⟨_, hnS_eq, _, _, _, heIn, heAll, hsExp4, _, heLo, _, heHi⟩ := hS_exp
  set nS := mem (sExp + 2)
  set ePtr := mem (sExp + 3)
  set eT := readTriples mem ePtr nS
  have heT_len : eT.length = nS := by simp [eT, readTriples]
  have htourH_lt : tourH < h := hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH xTour)
  set st0 := startState [tourH, sExp, h] mem pos
  set r3 := Function.update st0.regs 3 nS
  set r4 := Function.update r3 4 ePtr
  have ha3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 1) (.const 2)))) st0 .normal { st0 with regs := r3 } 5 :=
    runs_assign_iff.mpr ⟨nS, by simp [Expr.eval, BinOp.eval, st0, startState, show 2 < 2 ^ w by omega, show sExp + 2 < 2 ^ w by omega, nS], rfl, rfl, rfl⟩
  have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 1) (.const 3)))) { st0 with regs := r3 } .normal { st0 with regs := r4 } 5 :=
    runs_assign_iff.mpr ⟨ePtr, by simp [Expr.eval, BinOp.eval, r3, st0, startState, show 3 < 2 ^ w by omega, show sExp + 3 < 2 ^ w by omega, ePtr], rfl, rfl, rfl⟩
  let M_pref : ℕ → Finset End := fun i =>
    ((eT.take i).map Prod.fst).toFinset.biUnion fun e => {(e, true), (e, false)}
  let Inv : ℕ → (tourAsmRep vCap eCap).τ → State → Prop := fun i tx st =>
    st.regs 0 = tourH ∧ st.regs 2 = h ∧ st.regs 3 = nS ∧ st.regs 4 = ePtr ∧ st.regs 5 = i ∧
    TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, tr.cs.lsf.F, M_pref i⟩ tx st.mem ∧
    (∀ a, (tourAsmRep vCap eCap).foot tourH tx a → (tourAsmRep vCap eCap).foot tourH xTour a) ∧
    ZeroFrom st.mem h ∧
    (∀ a < h, ¬ (tourAsmRep vCap eCap).foot tourH xTour a → st.mem a = mem a)
  let C := hp.toSplayQuery (w := w) (by omega)
  let stepCost : ℕ → ℕ := fun _ => (2 * TOUR_FOREST_MUL + 60) * tourLog eCap
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  obtain ⟨stL, cL, txEnd, hrunL, hInvL, hcL⟩ :=
    runs_forRange_pot (w := w) (p := p) (ω := ω) (r := 5) (lo := .const 0) (hi := .reg 3)
      (phi := fun tx st => (tourAsmRep vCap eCap).phi tourH tx st.mem) (Inv := Inv)
      (stepCost := stepCost) nS (by omega) (fun _ => by omega)
      (st₀ := { st0 with regs := r4 }) (a₀ := xTour)
      ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
       ⟨by simp [r4, r3, st0, startState], by simp [r4, r3, st0, startState],
        by simp [r4, r3], by simp [r4], by simp,
        by simpa [M_pref, st0, startState] using hR0, fun _ ha => ha, hz, fun _ _ _ => rfl⟩, rfl⟩
      (fun _ _ _ _ hI => hI.2.2.2.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.2.2.1])
      (fun i tx st hi ⟨hr0, hr2, hr3, hr4, hr5, hR, hft, hzi, hfri⟩ => by
        have hi_eT : i < eT.length := by omega
        set e := eT[i].1
        have he_S : e ∈ S.E := (heIn eT[i] (List.getElem_mem hi_eT)).1
        have he_core : e ∈ (coreGraph tr.cs.G tr.cs.lsf).E := hS_sub he_S
        have he_G : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp he_core).1
        have he_open : e ∉ tr.cs.lsf.F.F.E := (Finset.mem_sdiff.mp he_core).2
        have he_mem_t : (e, true) ∈ ord (tr.cs.G.tail e) := by
          rw [← hρ]; exact (ρ.mem_order _ _).mpr ⟨he_G, rfl⟩
        have he_mem_f : (e, false) ∈ ord (tr.cs.G.head e) := by
          rw [← hρ]; exact (ρ.mem_order _ _).mpr ⟨he_G, rfl⟩
        have he_lt : e < eCap := hR.valid.ordWithin.2.2 _ _ he_mem_t
        have hmem_e : st.mem (ePtr + 3 * i) = e := by
          rw [hfri (ePtr + 3 * i) (by omega) (hS_disj _ (by omega) (by omega))]
          simp [e, eT, readTriples]
        set st1 : State := { st with regs := Function.update st.regs 6 e }
        have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 5)))))
            st .normal st1 7 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, hr4, hr5, hmem_e,
              show 3 < 2 ^ w by omega, show 3 * i < 2 ^ w by omega, show ePtr + 3 * i < 2 ^ w by omega],
            rfl, rfl, by simp [Expr.size]⟩
        -- Mark `(e, true)` = `endOfKey (2 * e)`
        have hft_i : ∀ a, tourFoot (ordStoreRep vCap eCap) vCap eCap tourH tx a → a < h :=
          fun a ha => hfoot a (hft a ha)
        obtain ⟨o1, stM1, c1, hrun1, hval1, x1, hrep1, hresp1, hcost1⟩ :=
          tourOp_setMark_runs (pos := st1.pos) (keyX := 2 * e) (v := tr.cs.G.tail e)
            (ordStoreRep_local vCap eCap) C ω hR
            (by simpa [tour_endOfKey_two_mul] using he_mem_t)
            (by simpa [tour_endOfKey_two_mul] using he_open) (by omega : (1 : ℕ) ≤ 1)
            hw1 (by omega) hft_i hzi hroom
        have hargs1 : evalArgs w st1 [.reg 0, .bin .mul (.const 2) (.reg 6), .const 1, .reg 2] =
            some [tourH, 2 * e, 1, h] := by
          simp [evalArgs, Expr.eval, BinOp.eval, st1, hr0, hr2,
            show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega, show 2 * e < 2 ^ w by omega]
        set st2 : State := { stM1 with regs := Function.update st1.regs 7 o1.value }
        have hcall1 : Runs w p ω (.call 7 (tourOp b 7) [.reg 0, .bin .mul (.const 2) (.reg 6), .const 1, .reg 2])
            st1 .normal st2 (argsSize [.reg 0, .bin .mul (.const 2) (.reg 6), .const 1, .reg 2] + c1 + 1) :=
          runs_call_iff.mpr ⟨_, _, o1, stM1, c1, hargs1, hp.op7_body, hrun1, rfl, rfl, rfl⟩
        have hft1_sub : ∀ a, tourFoot (ordStoreRep vCap eCap) vCap eCap tourH x1 a →
            tourFoot (ordStoreRep vCap eCap) vCap eCap tourH tx a := fun a ha => by
          rcases hresp1.2.2.2.2 a ha with h0 | ⟨h1, h2⟩
          · exact h0
          · omega
        have hft1_lt : ∀ a, tourFoot (ordStoreRep vCap eCap) vCap eCap tourH x1 a → a < h :=
          fun a ha => hft_i a (hft1_sub a ha)
        have hz1 : ZeroFrom stM1.mem h := by rw [← hval1]; exact hresp1.2.2.1
        -- Mark `(e, false)` = `endOfKey (2 * e + 1)`
        have heof2 : endOfKey (2 * e + 1) = (e, false) := by
          simp [endOfKey]; omega
        obtain ⟨o2, stM2, c2, hrun2, hval2, x2, hrep2, hresp2, hcost2⟩ :=
          tourOp_setMark_runs (pos := st2.pos) (keyX := 2 * e + 1) (v := tr.cs.G.head e)
            (ordStoreRep_local vCap eCap) C ω hrep1
            (by simpa [tourSetMark, heof2] using he_mem_f)
            (by simpa [tourSetMark, heof2] using he_open) (by omega : (1 : ℕ) ≤ 1)
            hw1 (by omega) hft1_lt hz1 hroom
        have hargs2 : evalArgs w st2
            [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 6)) (.const 1), .const 1, .reg 2] =
            some [tourH, 2 * e + 1, 1, h] := by
          simp [evalArgs, Expr.eval, BinOp.eval, st2, st1, hr0, hr2,
            show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            show 2 * e < 2 ^ w by omega, show 2 * e + 1 < 2 ^ w by omega]
        set st3 : State := { stM2 with regs := Function.update st2.regs 7 o2.value }
        have hcall2 : Runs w p ω
            (.call 7 (tourOp b 7)
              [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 6)) (.const 1), .const 1, .reg 2])
            st2 .normal st3
            (argsSize [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 6)) (.const 1), .const 1, .reg 2] + c2 + 1) :=
          runs_call_iff.mpr ⟨_, _, o2, stM2, c2, hargs2, hp.op7_body, hrun2, rfl, rfl, rfl⟩
        have hft2_sub : ∀ a, tourFoot (ordStoreRep vCap eCap) vCap eCap tourH x2 a →
            tourFoot (ordStoreRep vCap eCap) vCap eCap tourH xTour a := fun a ha => by
          rcases hresp2.2.2.2.2 a ha with h0 | ⟨h1, h2⟩
          · exact hft a (hft1_sub a h0)
          · omega
        have hz2 : ZeroFrom stM2.mem h := by rw [← hval2]; exact hresp2.2.2.1
        have hM_step : tourSetMark (tourSetMark ⟨ord, tr.cs.lsf.F, M_pref i⟩ (endOfKey (2 * e)) 1)
            (endOfKey (2 * e + 1)) 1 = ⟨ord, tr.cs.lsf.F, M_pref (i + 1)⟩ := by
          simp only [tourSetMark, ↓reduceIte, tour_endOfKey_two_mul, heof2]
          congr 1
          ext z
          simp only [M_pref, List.take_succ_eq_append_getElem hi_eT, Finset.mem_insert,
            Finset.mem_biUnion, List.mem_toFinset, List.mem_map, List.mem_append,
            List.mem_singleton, Finset.mem_singleton, e]
          constructor
          · rintro (rfl | rfl | ⟨a, ⟨x, hx, rfl⟩, hz⟩)
            · exact ⟨eT[i].1, ⟨eT[i], Or.inr rfl, rfl⟩, Or.inr rfl⟩
            · exact ⟨eT[i].1, ⟨eT[i], Or.inr rfl, rfl⟩, Or.inl rfl⟩
            · exact ⟨x.1, ⟨x, Or.inl hx, rfl⟩, hz⟩
          · rintro ⟨a, ⟨x, hx | rfl, rfl⟩, hz⟩
            · exact Or.inr (Or.inr ⟨x.1, ⟨x, hx, rfl⟩, hz⟩)
            · rcases hz with rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl rfl
        refine ⟨st3, _, x2,
          tour_runs_seq_normal ha6 (tour_runs_seq_normal hcall1 hcall2),
          by simp [st3, st2, st1, hr5],
          ⟨by simp [st3, st2, st1, hr0], by simp [st3, st2, st1, hr2],
           by simp [st3, st2, st1, hr3], by simp [st3, st2, st1, hr4], by simp,
           by rw [← hM_step]; exact hrep2,
           hft2_sub, hz2,
           fun a ha hnf => by
             have hnf1 : ¬ tourFoot (ordStoreRep vCap eCap) vCap eCap tourH x1 a :=
               fun hf => hnf (hft a (hft1_sub a hf))
             have hnf0 : ¬ tourFoot (ordStoreRep vCap eCap) vCap eCap tourH tx a :=
               fun hf => hnf (hft a hf)
             rw [hresp2.2.2.2.1 a ha hnf1, hresp1.2.2.2.1 a ha hnf0, hfri a ha hnf]⟩,
          rfl, ?_⟩
        dsimp only [stepCost, tourAsmRep, tourDSRep, st3]
        simp only [argsSize, Expr.size] at hcost1 hcost2 ⊢
        have h60 : 60 ≤ 60 * tourLog eCap := Nat.le_mul_of_pos_right 60 htl
        have hsplit : (2 * TOUR_FOREST_MUL + 60) * tourLog eCap =
            TOUR_FOREST_MUL * tourLog eCap + TOUR_FOREST_MUL * tourLog eCap + 60 * tourLog eCap := by
          ring
        omega)
  rcases hInvL with ⟨_, hr2L, _, _, _, hRL, hftL, hzL, hfrL⟩
  have hret : Runs w p ω (.ret (.reg 2)) stL (.returned h) stL 2 :=
    runs_ret_iff.mpr ⟨h, by simp [Expr.eval, hr2L], rfl, rfl, rfl⟩
  have hM_final : M_pref nS = edgeEnds S.E := by
    ext z
    have htake : eT.take nS = eT := List.take_of_length_le (by omega)
    simp only [M_pref, htake, Finset.mem_biUnion, List.mem_toFinset, List.mem_map,
      Finset.mem_insert, Finset.mem_singleton, mem_edgeEnds]
    constructor
    · rintro ⟨e, ⟨t, ht, rfl⟩, rfl | rfl⟩ <;> exact (heIn t ht).1
    · intro hzS
      obtain ⟨t, ht, hte⟩ := heAll z.1 hzS
      refine ⟨z.1, ⟨t, ht, hte⟩, ?_⟩
      cases hb : z.2
      · right; exact Prod.ext rfl hb
      · left; exact Prod.ext rfl hb
  have hMarks : OutMarksOf ⟨outCoreOrder tr ord, M_pref nS⟩ (outCoreOrder tr ord) S.E := by
    refine ⟨rfl, fun z => ?_⟩
    rw [hM_final, mem_edgeEnds]
    constructor
    · intro hzS
      refine ⟨?_, hzS⟩
      obtain ⟨v, _, hzm⟩ := exists_mem_outCoreOrder hRot (fun u hu => hR0.valid.verts_lt u
        ((compLSF_RF_isRSF hI).2.1 ▸ hu)) (hS_sub hzS) z.2
      exact ⟨v, by simpa using hzm⟩
    · intro h; exact h.2
  refine ⟨stL, _, ⟨outCoreOrder tr ord, M_pref nS⟩, txEnd,
    tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 (tour_runs_seq_normal hrunL hret)),
    ⟨rfl, hok, hRL⟩, hMarks, hftL, hzL, hfrL, ?_⟩
  have hrc : rangeCost stepCost 0 nS = nS * ((2 * TOUR_FOREST_MUL + 60) * tourLog eCap) := by
    unfold rangeCost stepCost; simp [Nat.mul_comm]
  rw [hrc, hnS_eq] at hcL
  simp only [Expr.size] at hcL
  have h1 : 100 ≤ 100 * tourLog eCap := Nat.le_mul_of_pos_right 100 htl
  have h9 : 9 * S.m ≤ 9 * S.m * tourLog eCap := Nat.le_mul_of_pos_right (9 * S.m) htl
  have h2 : S.m * ((2 * TOUR_FOREST_MUL + 60) * tourLog eCap) + 9 * S.m * tourLog eCap +
      100 * tourLog eCap ≤ tourMarkExportMul * (S.m + 1) * tourLog eCap := by
    have hmul_step : S.m * (2 * TOUR_FOREST_MUL + 69) + 100 ≤ tourMarkExportMul * (S.m + 1) := by
      have hle : 2 * TOUR_FOREST_MUL + 69 ≤ tourMarkExportMul := by unfold tourMarkExportMul; omega
      have h100 : 100 ≤ tourMarkExportMul := by unfold tourMarkExportMul; omega
      calc S.m * (2 * TOUR_FOREST_MUL + 69) + 100
          ≤ S.m * tourMarkExportMul + tourMarkExportMul :=
            Nat.add_le_add (Nat.mul_le_mul_left S.m hle) h100
        _ = tourMarkExportMul * (S.m + 1) := by ring
    have hEq : S.m * ((2 * TOUR_FOREST_MUL + 60) * tourLog eCap) + 9 * S.m * tourLog eCap +
        100 * tourLog eCap = (S.m * (2 * TOUR_FOREST_MUL + 69) + 100) * tourLog eCap := by ring
    rw [hEq]
    exact Nat.mul_le_mul_right (tourLog eCap) hmul_step
  dsimp only [tourAsmRep, tourDSRep, st0, startState] at hcL ⊢
  omega

/-! ## Step 3: Composed branch tour init with `S₀_cur` marks (`AsmBrCoreInitAt` form) -/

/-- Composed deterministic procedure (`[vCap, eCap, cOrdPtr, expPtr, sExp, h]`): initializes the
tour from `cOrdPtr` + `expPtr` (storing `tourH` at `mem h`) and marks every edge of `S_cur` from
its export at `sExp`. -/
def tourBranchInitMarkedStmt (fBranchInit fMarkExport : ℕ) : Stmt :=
  .call 6 fBranchInit [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5] ;;
  .assign 7 (.load (.reg 5)) ;;
  .call 8 fMarkExport [.reg 7, .reg 4, .reg 6] ;;
  .ret (.reg 8)

theorem tourBranchInitMarkedStmt_noRand (fBranchInit fMarkExport : ℕ) :
    (tourBranchInitMarkedStmt fBranchInit fMarkExport).NoRand := by
  simp [tourBranchInitMarkedStmt, Stmt.NoRand]

/-- Cost multiplier for `tourBranchInitMarkedStmt`. -/
def tourBranchInitMarkedMul : ℕ := tourBranchInitMul + tourMarkExportMul + 100

/-- **Tour initialization at branch init (`AsmBrCoreInitAt` postcondition form)**: builds the tour
of `tourAsmRep` with the core lists `outCoreOrder tr₀ ord` and the marks `OutMarksOf sTour
(outCoreOrder tr₀ ord) tr₀.S_cur.E` from `cOrdPtr`, P4's branch export `expPtr`, and `tr₀.S_cur`'s
export `sExp` (lying below `h`). -/
theorem tourBranchInitMarked_runs
    {depth w b fBranchInit fMarkExport L capExp M N vCap eCap cOrdPtr expPtr expEnd sExp h cWords pos : ℕ}
    {p : Program} (hp : HasTourProcs p b) (ω : ℕ → Bool)
    (hfInit : p.procs[fBranchInit]? = some (tourBranchInitStmt (tourInit b)))
    (hfMark : p.procs[fMarkExport]? = some (tourMarkExportStmt (tourOp b 7)))
    {tr : BundleTreeState depth} {ord : ℕ → List End} {mem : ℕ → ℕ}
    (hRot : HasRotOrder tr ord)
    (hVlt : ∀ v ∈ tr.cs.G.V, v < vCap) (hElt : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hS_sub : tr.S_cur.E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hOrdAt : OrdListAt mem cOrdPtr ord cWords) (hOrdLe : cOrdPtr + cWords ≤ h)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hExpLe : expEnd ≤ h)
    (hS_exp : ExportAt mem sExp h tr.S_cur)
    (hz : ZeroFrom mem h) (hsp : h + tourBranchInitSpace vCap eCap < 2 ^ w) :
    ∃ o st' c tourH sTour xTour,
      Runs w p ω (tourBranchInitMarkedStmt fBranchInit fMarkExport)
        (startState [vCap, eCap, cOrdPtr, expPtr, sExp, h] mem pos) o st' c ∧
      st'.mem h = tourH ∧ h < tourH ∧ tourH < o.value ∧
      (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH sTour xTour st'.mem ∧
      OutMarksOf sTour (outCoreOrder tr ord) tr.S_cur.E ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → tourH ≤ a ∧ a < o.value) ∧
      h ≤ o.value ∧ o.value + 2 ≤ h + tourBranchInitSpace vCap eCap ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem a) ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour st'.mem ≤
        tourBranchInitMarkedMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) *
          tourLog eCap := by
  obtain ⟨o1, st1, c1, tourH, x1, hrun1, hmh1, hlt1, htour1_lt, hrep1, _, hfoot1,
      hlo1, hhi1, hz1, hpre1, hcost1⟩ :=
    tourBranchInit_runs (pos := pos) hp ω hRot hVlt hElt hw hOrdAt hOrdLe hExp hExpLe hz hsp
  have hS_exp1 : ExportAt st1.mem sExp h tr.S_cur :=
    exportAt_congr (fun a _ ha2 => hpre1 a ha2) hS_exp
  have hS_disj1 : ∀ a, sExp ≤ a → a < h → ¬ (tourAsmRep vCap eCap).foot tourH x1 a := by
    intro a _ ha2 hf; have := (hfoot1 a hf).1; omega
  obtain ⟨st2, c2, sTour, x2, hrun2, hrep2, hMarks2, hfoot2, hz2, hfr2, hcost2⟩ :=
    tourMarkExport_runs (w := w) (pos := st1.pos) hp ω hRot hS_sub hS_exp1 hlo1 hS_disj1 hrep1
      (fun a ha => (hfoot1 a ha).2) hz1 (by omega)
  set st0 := startState [vCap, eCap, cOrdPtr, expPtr, sExp, h] mem pos
  have hargs1 : evalArgs w st0 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5] =
      some [vCap, eCap, cOrdPtr, expPtr, h] := by
    simp [evalArgs, Expr.eval, st0, startState]
  set stC1 : State := { st1 with regs := Function.update st0.regs 6 o1.value }
  have hcall1 : Runs w p ω (.call 6 fBranchInit [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5])
      st0 .normal stC1 (argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5] + c1 + 1) :=
    runs_call_iff.mpr ⟨_, _, o1, st1, c1, hargs1, hfInit, hrun1, rfl, rfl, rfl⟩
  set stA7 : State := { stC1 with regs := Function.update stC1.regs 7 tourH }
  have ha7 : Runs w p ω (.assign 7 (.load (.reg 5))) stC1 .normal stA7 3 :=
    runs_assign_iff.mpr ⟨tourH, by simp [Expr.eval, stC1, st0, startState, hmh1], rfl, rfl, rfl⟩
  have hargs2 : evalArgs w stA7 [.reg 7, .reg 4, .reg 6] = some [tourH, sExp, o1.value] := by
    simp [evalArgs, Expr.eval, stA7, stC1, st0, startState]
  set stC2 : State := { st2 with regs := Function.update stA7.regs 8 o1.value }
  have hcall2 : Runs w p ω (.call 8 fMarkExport [.reg 7, .reg 4, .reg 6])
      stA7 .normal stC2 (argsSize [.reg 7, .reg 4, .reg 6] + c2 + 1) :=
    runs_call_iff.mpr ⟨_, _, .returned o1.value, st2, c2, hargs2, hfMark, hrun2, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 8)) stC2 (.returned o1.value) stC2 2 :=
    runs_ret_iff.mpr ⟨o1.value, by simp [Expr.eval, stC2], rfl, rfl, rfl⟩
  have hrunAll := tour_runs_seq_normal hcall1 (tour_runs_seq_normal ha7 (tour_runs_seq_normal hcall2 hret))
  have hmh2 : st2.mem h = tourH := by
    rw [hfr2 h (by omega) (fun hf => by have := (hfoot1 h hf).1; omega), hmh1]
  refine ⟨.returned o1.value, stC2, _, tourH, sTour, x2, hrunAll, hmh2, hlt1, htour1_lt,
    hrep2, hMarks2, fun a ha => ⟨by have := (hfoot1 a (hfoot2 a ha)).1; omega, (hfoot1 a (hfoot2 a ha)).2⟩,
    hlo1, hhi1, hz2,
    fun a ha => by
      rw [hfr2 a (by omega) (fun hf => by have := (hfoot1 a hf).1; omega), hpre1 a ha], ?_⟩
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hc1' : c1 + (tourAsmRep vCap eCap).phi tourH x1 st1.mem ≤
      tourBranchInitMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap :=
    le_trans hcost1 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
  have hc2' : c2 + (tourAsmRep vCap eCap).phi tourH x2 st2.mem ≤
      tourMarkExportMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap +
        (tourAsmRep vCap eCap).phi tourH x1 st1.mem :=
    le_trans hcost2 (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))) _)
  have h100 : 100 ≤ 100 * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap := by
    have h1 : 1 ≤ (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap :=
      Nat.mul_pos (by omega) htl
    calc 100 = 100 * 1 := by ring
      _ ≤ 100 * ((1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap) :=
          Nat.mul_le_mul_left 100 h1
      _ = 100 * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap := by ring
  have hmul : tourBranchInitMarkedMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) *
        tourLog eCap =
      tourBranchInitMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap +
      tourMarkExportMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap +
      100 * (1 + cWords + tr.cs.G.m + tr.cs.G.n + tr.S_cur.m) * tourLog eCap := by
    unfold tourBranchInitMarkedMul; ring
  simp only [argsSize, Expr.size, stC2] at *
  omega

/-- Under `AsmBrCoreInitAt`'s bounds (`cWords ≤ 1 + 6 * G.m`, `G.n ≤ G.m + 1`, `tr₀.S_cur.m ≤ G.m`,
`eCap + 2 ≤ (M + N + 2) ^ capExp`), the tour initialization cost fits inside
`3 * tourBranchInitMarkedMul * capExp * tr₀.machCost`. -/
theorem tourBranchInit_cost_le_machCost
    {lsfInit : LSFInit} {depth : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut}
    {params : ℕ → DynSpanner.SparsifyParams} {spanConst k M N j capExp eCap cWords : ℕ}
    {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End}
    (hcWords : cWords ≤ 1 + 6 * G.m) (hGn : G.n ≤ G.m + 1)
    (hSm : (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j).S_cur.m ≤ G.m)
    (heCap : eCap + 2 ≤ (M + N + 2) ^ capExp) :
    let tr₀ := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    tourBranchInitMarkedMul * (1 + cWords + G.m + G.n + tr₀.S_cur.m) * tourLog eCap ≤
      (3 * tourBranchInitMarkedMul * capExp) * tr₀.machCost := by
  intro tr₀
  have hlog : tourLog eCap ≤ capExp * bundleLogFactor M N := by
    rw [← ordStoreLog_eq_tourLog]
    exact le_trans (ordStoreLog_le_of_cap heCap)
      (Nat.mul_le_mul_left _ (logStep_le_bundleLogFactor M N))
  have hlin : 1 + cWords + G.m + G.n + tr₀.S_cur.m ≤ 3 * (3 * G.m + 2) := by
    change tr₀.S_cur.m ≤ G.m at hSm; omega
  have hmach : (3 * G.m + 2) * bundleLogFactor M N ≤ tr₀.machCost := by
    rw [initBundleTreeWithParams_machCost]
    exact Nat.mul_le_mul_right _ (by omega)
  calc tourBranchInitMarkedMul * (1 + cWords + G.m + G.n + tr₀.S_cur.m) * tourLog eCap
      ≤ tourBranchInitMarkedMul * (3 * (3 * G.m + 2)) * (capExp * bundleLogFactor M N) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hlin) hlog
    _ = (3 * tourBranchInitMarkedMul * capExp) * ((3 * G.m + 2) * bundleLogFactor M N) := by ring
    _ ≤ (3 * tourBranchInitMarkedMul * capExp) * tr₀.machCost :=
        Nat.mul_le_mul_left _ hmach

end MinCostFlow.SparseCore.Program
