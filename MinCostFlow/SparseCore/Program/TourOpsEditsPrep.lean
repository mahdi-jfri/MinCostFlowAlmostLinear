module

public import MinCostFlow.SparseCore.Program.TourOpsEditMove
public import MinCostFlow.SparseCore.Program.TourOpsEditDrop
public import MinCostFlow.SparseCore.Program.TourOpsEditInsert
public import MinCostFlow.SparseCore.Program.TourOpsEditRotate
import Mathlib.Tactic

/-!
# Copy, deduplication, and single-edit decoding helpers for `applyEdits` (Op 0)

Provides:
- `tourDedupSelBody` (`[b, selPtr, len, outPtr]` -> `m'`): deduplicates a `moveEnds` key array into
  `outPtr` using `markArr`, restoring `markArr` to all zeros in `O(len + 1)` time so that the
  forwarded 1-edit `moveEnds` record always satisfies `words' ≤ 5 * ordEditsEnc [edit] + 1`.
- `tourEditsCopyLoop`: copies `words` words from `edits` to `heap + 1`.
- `tourDecodeEdit_shift` and single-edit `OrdEditsAt` / `OrdEditsWithin` lemmas for forwarding each
  edit to `ordStoreOp b 0`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Deduplication helper for `moveEnds` forwarding (`tourDedupSelBody`) -/

/-- `tourDedupSel [b, selPtr, len, outPtr]`: deduplicates `mem[selPtr .. selPtr + len)` into
`outPtr[0 .. m')` using `markArr`, restores `markArr` to all zeros, and returns `m' ≤ len`. -/
def tourDedupSelBody : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const HDR_MARK_ARR))) ;;
  .assign 5 (.const 0) ;;
  .assign 6 (.const 0) ;;
  .loop (.bin .lt (.reg 6) (.reg 2))
    (.assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
     .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.store (.bin .add (.reg 4) (.reg 7)) (.const 1) ;;
        .store (.bin .add (.reg 3) (.reg 5)) (.reg 7) ;;
        .assign 5 (.bin .add (.reg 5) (.const 1)))
       .nop ;;
     .assign 6 (.bin .add (.reg 6) (.const 1))) ;;
  .assign 6 (.const 0) ;;
  .loop (.bin .lt (.reg 6) (.reg 5))
    (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
     .store (.bin .add (.reg 4) (.reg 7)) (.const 0) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1))) ;;
  .ret (.reg 5)

/-- Copy `r2` words from `r1` to `r5` (`r4` starts at `0`). -/
def tourEditsCopyLoop : Stmt :=
  .loop (.bin .lt (.reg 4) (.reg 2))
    (.assign 6 (.load (.bin .add (.reg 1) (.reg 4))) ;;
     .store (.bin .add (.reg 5) (.reg 4)) (.reg 6) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1)))

theorem tourEditsPrep_noRand : tourDedupSelBody.NoRand ∧ tourEditsCopyLoop.NoRand := by
  simp [tourDedupSelBody, tourEditsCopyLoop, Stmt.NoRand]

/-! ## Verification of `tourDedupSelBody` -/

theorem tourDedupSelBody_runs {τ_ord : Type}
    {w vCap eCap b selPtr len outPtr pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ} {sel : List End}
    (h : TourCoreAt vCap eCap b s x mem)
    (hsel_len : sel.length = len)
    (hsel_mem : ∀ i (hi : i < len), mem (selPtr + i) = endKey (sel[i]'(by omega)))
    (hsel_lt : ∀ z ∈ sel, z.1 < eCap)
    (hsel_ge : ordHandleOf b vCap eCap ≤ selPtr)
    (hsel_le : selPtr + len ≤ outPtr)
    (hroom : outPtr + len + 2 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) :
    ∃ (m' : ℕ) (st' : State) (c : ℕ) (U : List End),
      Runs w p ω tourDedupSelBody
        (startState [b, selPtr, len, outPtr] mem pos) (.returned m') st' c ∧
      m' ≤ len ∧ U.length = m' ∧ U.Nodup ∧ U.toFinset = sel.toFinset ∧
      (∀ j (hj : j < U.length), st'.mem (outPtr + j) = endKey U[j]) ∧
      (∀ a, (a < outPtr ∨ outPtr + m' ≤ a) → st'.mem a = mem a) ∧
      c ≤ 95 * len + 60 := by
  classical
  have hhdr := h.header
  have hord_le : ordHandleOf b vCap eCap ≤ outPtr := by omega
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hmk_lt_sel : markArrBase b vCap eCap + 2 * eCap ≤ selPtr := by
    simp [markArrBase, ordHandleOf, tourFixedSize] at hsel_ge ⊢; omega
  -- Phase 1: dedup scan
  have hloop1 : ∀ (rem i m : ℕ) (U : List End) (stC : State),
      i + rem = len → m ≤ i → U.length = m → U.Nodup →
      stC.regs 1 = selPtr → stC.regs 2 = len → stC.regs 3 = outPtr →
      stC.regs 4 = markArrBase b vCap eCap → stC.regs 5 = m → stC.regs 6 = i →
      (∀ j (hj : j < U.length), stC.mem (outPtr + j) = endKey U[j]) →
      (∀ z, z ∈ U ↔ z ∈ sel.take i) →
      (∀ k < 2 * eCap, stC.mem (markArrBase b vCap eCap + k) = if endOfKey k ∈ U then 1 else 0) →
      (∀ a, (a < markArrBase b vCap eCap ∨ markArrBase b vCap eCap + 2 * eCap ≤ a) →
        (a < outPtr ∨ outPtr + m ≤ a) → stC.mem a = mem a) →
      ∃ (mF : ℕ) (UF : List End) (stF : State) (c1 : ℕ),
        Runs w p ω (.loop (.bin .lt (.reg 6) (.reg 2))
          (.assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
           .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
           .cond (.bin .eq (.reg 8) (.const 0))
             (.store (.bin .add (.reg 4) (.reg 7)) (.const 1) ;;
              .store (.bin .add (.reg 3) (.reg 5)) (.reg 7) ;;
              .assign 5 (.bin .add (.reg 5) (.const 1)))
             .nop ;;
           .assign 6 (.bin .add (.reg 6) (.const 1)))) stC .normal stF c1 ∧
        mF ≤ len ∧ UF.length = mF ∧ UF.Nodup ∧
        stF.regs 3 = outPtr ∧ stF.regs 4 = markArrBase b vCap eCap ∧ stF.regs 5 = mF ∧
        (∀ j (hj : j < UF.length), stF.mem (outPtr + j) = endKey UF[j]) ∧
        (∀ z, z ∈ UF ↔ z ∈ sel) ∧
        (∀ k < 2 * eCap, stF.mem (markArrBase b vCap eCap + k) = if endOfKey k ∈ UF then 1 else 0) ∧
        (∀ a, (a < markArrBase b vCap eCap ∨ markArrBase b vCap eCap + 2 * eCap ≤ a) →
          (a < outPtr ∨ outPtr + mF ≤ a) → stF.mem a = mem a) ∧
        c1 ≤ 55 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i m U stC hrem hmi hUlen hUnd hr1 hr2 hr3 hr4 hr5 hr6 hmO hUiff hmk hfr
      have hilen : i = len := by omega
      have htake : sel.take i = sel := List.take_of_length_le (by omega)
      have hcond : (Expr.bin .lt (.reg 6) (.reg 2)).eval w stC = some 0 := by
        simp [Expr.eval, hr6, hr2, hilen, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨m, U, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        by omega, hUlen, hUnd, hr3, hr4, hr5, hmO, fun z => by simpa [htake] using hUiff z,
        hmk, hfr, by simp [Expr.size]⟩
    | succ rem ih =>
      intro i m U stC hrem hmi hUlen hUnd hr1 hr2 hr3 hr4 hr5 hr6 hmO hUiff hmk hfr
      have hi_lt : i < len := by omega
      set z := sel[i]'(by omega)
      set k := endKey z
      have hk_lt : k < 2 * eCap := endKey_lt_two_mul (hsel_lt z (List.getElem_mem _))
      have hsel_eq : stC.mem (selPtr + i) = k := by
        rw [hfr (selPtr + i) (Or.inr (by omega)) (Or.inl (by omega))]; exact hsel_mem i hi_lt
      have hcond : (Expr.bin .lt (.reg 6) (.reg 2)).eval w stC = some 1 := by
        simp [Expr.eval, hr6, hr2, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      set r1 := Function.update stC.regs 7 k
      set mk := stC.mem (markArrBase b vCap eCap + k)
      set r2 := Function.update r1 8 mk
      have ha7 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 1) (rIdx := 6)
        (base := selPtr) (idx := i) (val := k) (st := stC) hr1 hr6 (by omega) hsel_eq
      have ha8 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 4) (rIdx := 7)
        (base := markArrBase b vCap eCap) (idx := k) (val := mk) (st := { stC with regs := r1 })
        (by simp [r1, hr4]) (by simp [r1]) (by omega) rfl
      have hmk_eq : mk = if z ∈ U then 1 else 0 := by
        have := hmk k hk_lt; simpa [mk, k, endOfKey_endKey] using this
      have htake_succ : sel.take (i + 1) = sel.take i ++ [z] := List.take_succ_eq_append_getElem (by omega)
      by_cases hzU : z ∈ U
      · have hmk1 : mk = 1 := by simp [hmk_eq, hzU]
        have hcmk : (Expr.bin .eq (.reg 8) (.const 0)).eval w { stC with regs := r2 } = some 0 := by
          simp [Expr.eval, r2, hmk1, BinOp.eval, (by omega : 0 < 2 ^ w)]
        set r3 := Function.update r2 6 (i + 1)
        have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1))) { stC with regs := r2 } .normal
            { stC with regs := r3 } 4 :=
          runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r2, r1, hr6, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
        obtain ⟨mF, UF, stF, c1, hrun1, hmF, hUFl, hUFnd, hF3, hF4, hF5, hFmO, hFUiff, hFmk, hFfr, hc1⟩ :=
          ih (i + 1) m U { stC with regs := r3 } (by omega) (by omega) hUlen hUnd
            (by simp [r3, r2, r1, hr1]) (by simp [r3, r2, r1, hr2]) (by simp [r3, r2, r1, hr3])
            (by simp [r3, r2, r1, hr4]) (by simp [r3, r2, r1, hr5]) (by simp [r3]) hmO
            (fun w' => by
              rw [htake_succ, List.mem_append, List.mem_singleton, ← hUiff w']
              exact ⟨Or.inl, fun h => h.elim id (fun heq => heq ▸ hzU)⟩) hmk hfr
        refine ⟨mF, UF, stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
          tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8 (tour_runs_seq_normal
            (tour_runs_cond_false hcmk (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)) ha6)), hrun1, rfl⟩)),
          hmF, hUFl, hUFnd, hF3, hF4, hF5, hFmO, hFUiff, hFmk, hFfr, by clear * - hc1; simp only [Expr.size] at *; omega⟩
      · have hmk0 : mk = 0 := by simp [hmk_eq, hzU]
        have hcmk : (Expr.bin .eq (.reg 8) (.const 0)).eval w { stC with regs := r2 } = some 1 := by
          simp [Expr.eval, r2, hmk0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
        set m1 := Function.update stC.mem (markArrBase b vCap eCap + k) 1
        set m2 := Function.update m1 (outPtr + m) k
        set r3 := Function.update r2 5 (m + 1)
        set r4 := Function.update r3 6 (i + 1)
        have hst1 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 7)) (.const 1))
            { stC with regs := r2 } .normal { stC with mem := m1, regs := r2 } 5 :=
          runs_store_iff.mpr ⟨markArrBase b vCap eCap + k, 1,
            by simp [Expr.eval, r2, r1, hr4, BinOp.eval, (by omega : markArrBase b vCap eCap + k < 2 ^ w)],
            by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have hst2 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 5)) (.reg 7))
            { stC with mem := m1, regs := r2 } .normal { stC with mem := m2, regs := r2 } 5 :=
          runs_store_iff.mpr ⟨outPtr + m, k,
            by simp [Expr.eval, r2, r1, hr3, hr5, BinOp.eval, (by omega : outPtr + m < 2 ^ w)],
            by simp [Expr.eval, r2, r1], rfl, rfl, rfl⟩
        have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 1)))
            { stC with mem := m2, regs := r2 } .normal { stC with mem := m2, regs := r3 } 4 :=
          runs_assign_iff.mpr ⟨m + 1, by simp [Expr.eval, r2, r1, hr5, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : m + 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1)))
            { stC with mem := m2, regs := r3 } .normal { stC with mem := m2, regs := r4 } 4 :=
          runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r3, r2, r1, hr6, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have hU'_nd : (U ++ [z]).Nodup := List.nodup_append.mpr ⟨hUnd, List.nodup_singleton z,
          fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb; intro heq; exact hzU (heq ▸ ha)⟩
        obtain ⟨mF, UF, stF, c1, hrun1, hmF, hUFl, hUFnd, hF3, hF4, hF5, hFmO, hFUiff, hFmk, hFfr, hc1⟩ :=
          ih (i + 1) (m + 1) (U ++ [z]) { stC with mem := m2, regs := r4 } (by omega) (by omega)
            (by simp [hUlen]) hU'_nd
            (by simp [r4, r3, r2, r1, hr1]) (by simp [r4, r3, r2, r1, hr2])
            (by simp [r4, r3, r2, r1, hr3]) (by simp [r4, r3, r2, r1, hr4]) (by simp [r4, r3]) (by simp [r4])
            (fun j hj => by
              have hj' : j < m + 1 := by simpa [hUlen] using hj
              by_cases hjm : j = m
              · subst hjm; simp [m2, hUlen, k]
              · dsimp only [m2, m1]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  hmO j (by omega), List.getElem_append_left (by omega)])
            (fun w' => by rw [htake_succ, List.mem_append, List.mem_append, List.mem_singleton, hUiff w'])
            (fun k' hk' => by
              dsimp only [m2, m1]
              rw [Function.update_of_ne (by omega)]
              by_cases hkk : k' = k
              · subst hkk; simp [k, endOfKey_endKey]
              · rw [Function.update_of_ne (by omega), hmk k' hk']
                have hne : endOfKey k' ≠ z := fun heq => hkk (by rw [← endKey_endOfKey k', heq])
                simp [hne])
            (fun a ha1 ha2 => by
              dsimp only [m2, m1]
              rw [Function.update_of_ne (by rcases ha2 with h1 | h2 <;> omega),
                Function.update_of_ne (by rcases ha1 with h1 | h2 <;> omega)]
              exact hfr a ha1 (by rcases ha2 with h1 | h2; exact Or.inl h1; exact Or.inr (by omega)))
        refine ⟨mF, UF, stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
          tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8 (tour_runs_seq_normal
            (tour_runs_cond_true (s₂ := .nop) hcmk (by omega)
              (tour_runs_seq_normal hst1 (tour_runs_seq_normal hst2 ha5))) ha6)), hrun1, rfl⟩)),
          hmF, hUFl, hUFnd, hF3, hF4, hF5, hFmO, hFUiff, hFmk, hFfr, by clear * - hc1; simp only [Expr.size] at *; omega⟩
  -- Phase 2: cleanup `markArr`
  have hloop2 : ∀ (mF : ℕ) (UF : List End) (rem j : ℕ) (stC : State),
      mF ≤ len → UF.length = mF → UF.Nodup → j + rem = mF →
      stC.regs 3 = outPtr → stC.regs 4 = markArrBase b vCap eCap → stC.regs 5 = mF → stC.regs 6 = j →
      (∀ q (hq : q < UF.length), stC.mem (outPtr + q) = endKey UF[q]) →
      (∀ z ∈ UF, z.1 < eCap) →
      (∀ k < 2 * eCap, stC.mem (markArrBase b vCap eCap + k) = if endOfKey k ∈ UF.drop j then 1 else 0) →
      (∀ a, (a < markArrBase b vCap eCap ∨ markArrBase b vCap eCap + 2 * eCap ≤ a) →
        (a < outPtr ∨ outPtr + mF ≤ a) → stC.mem a = mem a) →
      ∃ (stE : State) (c2 : ℕ),
        Runs w p ω (.loop (.bin .lt (.reg 6) (.reg 5))
          (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
           .store (.bin .add (.reg 4) (.reg 7)) (.const 0) ;;
           .assign 6 (.bin .add (.reg 6) (.const 1)))) stC .normal stE c2 ∧
        stE.regs 5 = mF ∧
        (∀ q (hq : q < UF.length), stE.mem (outPtr + q) = endKey UF[q]) ∧
        (∀ a, (a < outPtr ∨ outPtr + mF ≤ a) → stE.mem a = mem a) ∧
        c2 ≤ 25 * rem + 10 := by
    intro mF UF rem
    induction rem with
    | zero =>
      intro j stC hmF hUFl hUFnd hrem hr3 hr4 hr5 hr6 hmO hUcap hmk hfr
      have hjm : j = mF := by omega
      have hcond : (Expr.bin .lt (.reg 6) (.reg 5)).eval w stC = some 0 := by
        simp [Expr.eval, hr6, hr5, hjm, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hr5, hmO,
        fun a ha => by
          by_cases hmr : markArrBase b vCap eCap ≤ a ∧ a < markArrBase b vCap eCap + 2 * eCap
          · have hk : a - markArrBase b vCap eCap < 2 * eCap := by omega
            have hae : markArrBase b vCap eCap + (a - markArrBase b vCap eCap) = a := by omega
            rw [← hae, hmk _ hk, hjm, ← hUFl, List.drop_length, h.markArr_zero _ hk]; simp
          · exact hfr a (by omega) ha, by simp [Expr.size]⟩
    | succ rem ih =>
      intro j stC hmF hUFl hUFnd hrem hr3 hr4 hr5 hr6 hmO hUcap hmk hfr
      have hj_lt : j < mF := by omega
      set z := UF[j]'(by omega)
      set k := endKey z
      have hk_lt : k < 2 * eCap := endKey_lt_two_mul (hUcap z (List.getElem_mem _))
      have hcond : (Expr.bin .lt (.reg 6) (.reg 5)).eval w stC = some 1 := by
        simp [Expr.eval, hr6, hr5, hj_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      set r1 := Function.update stC.regs 7 k
      set m1 := Function.update stC.mem (markArrBase b vCap eCap + k) 0
      set r2 := Function.update r1 6 (j + 1)
      have ha7 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 3) (rIdx := 6)
        (base := outPtr) (idx := j) (val := k) (st := stC) hr3 hr6 (by omega) (hmO j (by omega))
      have hst0 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 7)) (.const 0))
          { stC with regs := r1 } .normal { stC with mem := m1, regs := r1 } 5 :=
        runs_store_iff.mpr ⟨markArrBase b vCap eCap + k, 0,
          by simp [Expr.eval, r1, hr4, BinOp.eval, (by omega : markArrBase b vCap eCap + k < 2 ^ w)],
          by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
      have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1)))
          { stC with mem := m1, regs := r1 } .normal { stC with mem := m1, regs := r2 } 4 :=
        runs_assign_iff.mpr ⟨j + 1, by simp [Expr.eval, r1, hr6, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : j + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hdrop_c : UF.drop j = z :: UF.drop (j + 1) := List.drop_eq_getElem_cons (by omega)
      have hz_nd : z ∉ UF.drop (j + 1) :=
        (List.nodup_cons.mp (hdrop_c ▸ hUFnd.sublist (List.drop_sublist j UF))).1
      obtain ⟨stE, c2, hrun2, hE5, hEmO, hEfr, hc2⟩ :=
        ih (j + 1) { stC with mem := m1, regs := r2 } hmF hUFl hUFnd (by omega)
          (by simp [r2, r1, hr3]) (by simp [r2, r1, hr4]) (by simp [r2, r1, hr5]) (by simp [r2])
          (fun q hq => by dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact hmO q hq) hUcap
          (fun k' hk' => by
            dsimp only [m1]
            by_cases hkk : k' = k
            · subst hkk; simp [k, endOfKey_endKey, hz_nd]
            · rw [Function.update_of_ne (by omega), hmk k' hk', hdrop_c]
              have hne : endOfKey k' ≠ z := fun heq => hkk (by rw [← endKey_endOfKey k', heq])
              simp [hne])
          (fun a ha1 ha2 => by dsimp only [m1]; rw [Function.update_of_ne (by rcases ha1 with h1 | h2 <;> omega)]; exact hfr a ha1 ha2)
      refine ⟨stE, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
        tour_runs_seq_normal ha7 (tour_runs_seq_normal hst0 ha6), hrun2, rfl⟩)),
        hE5, hEmO, hEfr, by clear * - hc2; simp only [Expr.size] at *; omega⟩
  -- Assemble full `tourDedupSelBody`
  set s0 : State := startState [b, selPtr, len, outPtr] mem pos
  set r1 := Function.update s0.regs 4 (markArrBase b vCap eCap)
  set r2 := Function.update r1 5 0
  set r3 := Function.update r2 6 0
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 0) (off := HDR_MARK_ARR)
    (b := b) (val := markArrBase b vCap eCap) (st := s0) (by simp [s0, startState])
    (by simp only [HDR_MARK_ARR]; omega) (by simp only [HDR_MARK_ARR]; omega) hhdr.2.2.2.2.2.2.2.2.2.1
  have ha5 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 5) (val := 0) (st := ⟨mem, r1, pos⟩) (by omega)
  have ha6 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 6) (val := 0) (st := ⟨mem, r2, pos⟩) (by omega)
  obtain ⟨mF, UF, stF, c1, hrun1, hmF, hUFl, hUFnd, hF3, hF4, hF5, hFmO, hFUiff, hFmk, hFfr, hc1⟩ :=
    hloop1 len 0 0 [] ⟨mem, r3, pos⟩ (by omega) (le_refl 0) rfl List.nodup_nil
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1]) (by simp [r3, r2]) (by simp [r3])
      (fun j hj => by simp at hj) (fun z => by simp)
      (fun k hk => by simp [h.markArr_zero k hk]) (fun _ _ _ => rfl)
  set rReset := Function.update stF.regs 6 0
  have haReset := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 6) (val := 0) (st := stF) (by omega)
  obtain ⟨stE, c2, hrun2, hE5, hEmO, hEfr, hc2⟩ :=
    hloop2 mF UF mF 0 { stF with regs := rReset } hmF hUFl hUFnd (by omega)
      (by simp [rReset, hF3]) (by simp [rReset, hF4]) (by simp [rReset, hF5]) (by simp [rReset])
      hFmO (fun z hz => hsel_lt z ((hFUiff z).mp hz)) (by simpa using hFmk) hFfr
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := stE) (r := 5) (v := mF) hE5
  refine ⟨mF, stE, _, UF,
    tour_runs_seq_normal ha4 (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6
      (tour_runs_seq_normal hrun1 (tour_runs_seq_normal haReset (tour_runs_seq_normal hrun2 hret))))),
    hmF, hUFl, hUFnd, by ext z; simp [hFUiff z], hEmO, hEfr, by clear * - hc1 hc2 hmF; omega⟩

/-! ## Verification of `tourEditsCopyLoop` -/

theorem tourEditsCopyLoop_runs {w src dst words : ℕ} {p : Program} (ω : ℕ → Bool)
    {st0 : State} (hr1 : st0.regs 1 = src) (hr2 : st0.regs 2 = words)
    (hr4 : st0.regs 4 = 0) (hr5 : st0.regs 5 = dst)
    (hdisj : src + words ≤ dst) (hroom : dst + words < 2 ^ w) (h1 : 1 < 2 ^ w) :
    ∃ st' c, Runs w p ω tourEditsCopyLoop st0 .normal st' c ∧
      (∀ k, k ≠ 4 → k ≠ 6 → st'.regs k = st0.regs k) ∧
      (∀ i < words, st'.mem (dst + i) = st0.mem (src + i)) ∧
      (∀ a, (a < dst ∨ dst + words ≤ a) → st'.mem a = st0.mem a) ∧
      c ≤ 25 * words + 10 := by
  suffices h : ∀ (rem i : ℕ) (stC : State), i + rem = words →
      stC.regs 1 = src → stC.regs 2 = words → stC.regs 4 = i → stC.regs 5 = dst →
      (∀ k, k ≠ 4 → k ≠ 6 → stC.regs k = st0.regs k) →
      (∀ j < i, stC.mem (dst + j) = st0.mem (src + j)) →
      (∀ a, (a < dst ∨ dst + i ≤ a) → stC.mem a = st0.mem a) →
      ∃ st' c, Runs w p ω tourEditsCopyLoop stC .normal st' c ∧
        (∀ k, k ≠ 4 → k ≠ 6 → st'.regs k = st0.regs k) ∧
        (∀ j < words, st'.mem (dst + j) = st0.mem (src + j)) ∧
        (∀ a, (a < dst ∨ dst + words ≤ a) → st'.mem a = st0.mem a) ∧
        c ≤ 25 * rem + 10 from
    h words 0 st0 (by omega) hr1 hr2 hr4 hr5 (fun _ _ _ => rfl) (fun j hj => by omega) (fun _ _ => rfl)
  intro rem
  induction rem with
  | zero =>
    intro i stC hrem _ hr2C hr4C _ hro hcp hfr
    have hiw : i = words := by omega
    have hc : (Expr.bin .lt (.reg 4) (.reg 2)).eval w stC = some 0 := by
      simp [Expr.eval, hr4C, hr2C, hiw, BinOp.eval, (by omega : 0 < 2 ^ w)]
    exact ⟨stC, _, runs_loop_iff.mpr (Or.inl ⟨hc, rfl, rfl, rfl⟩), hro, by rwa [← hiw], by rwa [← hiw], by simp [Expr.size]⟩
  | succ rem ih =>
    intro i stC hrem hr1C hr2C hr4C hr5C hro hcp hfr
    have hilt : i < words := by omega
    have hc : (Expr.bin .lt (.reg 4) (.reg 2)).eval w stC = some 1 := by
      simp [Expr.eval, hr4C, hr2C, hilt, BinOp.eval, h1]
    set val := st0.mem (src + i)
    set r1 := Function.update stC.regs 6 val
    set m1 := Function.update stC.mem (dst + i) val
    set r2 := Function.update r1 4 (i + 1)
    have ha6 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 1) (rIdx := 4)
      (base := src) (idx := i) (val := val) (st := stC) hr1C hr4C (by omega) (hfr _ (Or.inl (by omega)))
    have hst : Runs w p ω (.store (.bin .add (.reg 5) (.reg 4)) (.reg 6))
        { stC with regs := r1 } .normal { stC with mem := m1, regs := r1 } 5 :=
      runs_store_iff.mpr ⟨dst + i, val,
        by simp [Expr.eval, r1, hr5C, hr4C, BinOp.eval, (by omega : dst + i < 2 ^ w)],
        by simp [Expr.eval, r1], rfl, rfl, rfl⟩
    have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1)))
        { stC with mem := m1, regs := r1 } .normal { stC with mem := m1, regs := r2 } 4 :=
      runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r1, hr4C, BinOp.eval, h1, (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
    obtain ⟨st', c', hrun', hro', hcp', hfr', hc'⟩ :=
      ih (i + 1) { stC with mem := m1, regs := r2 } (by omega)
        (by simp [r2, r1, hr1C]) (by simp [r2, r1, hr2C]) (by simp [r2]) (by simp [r2, r1, hr5C])
        (fun k h4 h6 => by simp [r2, r1, Function.update_of_ne h4, Function.update_of_ne h6, hro k h4 h6])
        (fun j hj => by
          by_cases hji : j = i
          · subst hji; simp [m1, val]
          · dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact hcp j (by omega))
        (fun a ha => by
          dsimp only [m1]; rw [Function.update_of_ne (by rcases ha with h1 | h2 <;> omega)]
          exact hfr a (by rcases ha with h1 | h2; exact Or.inl h1; exact Or.inr (by omega)))
    exact ⟨st', _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hc, by omega,
      tour_runs_seq_normal ha6 (tour_runs_seq_normal hst ha4), hrun', rfl⟩)),
      hro', hcp', hfr', by clear * - hc'; simp only [Expr.size] at *; omega⟩

/-! ## Shifted decoding and single-edit `OrdEditsAt` / `OrdEditsWithin` lemmas -/

theorem tour_readList_shift {m₁ m₂ : ℕ → ℕ} {a₁ a₂ n : ℕ}
    (h : ∀ i < n, m₂ (a₂ + i) = m₁ (a₁ + i)) :
    readList m₂ a₂ n = readList m₁ a₁ n := by
  apply List.ext_getElem (by simp [readList_length])
  intro i hi _
  have hi' : i < n := by rw [readList_length] at hi; exact hi
  rw [readList_getElem, readList_getElem]; exact h i hi'

theorem tour_decodeOrdEdit_shift {m₁ m₂ : ℕ → ℕ} {a₁ a₂ : ℕ}
    (h : ∀ i < (decodeOrdEdit m₁ a₁).2, m₂ (a₂ + i) = m₁ (a₁ + i)) :
    decodeOrdEdit m₂ a₂ = decodeOrdEdit m₁ a₁ := by
  have hge2 := decodeOrdEdit_words_ge_two m₁ a₁
  have h0 : m₂ a₂ = m₁ a₁ := by simpa using h 0 (by omega)
  have h1 : m₂ (a₂ + 1) = m₁ (a₁ + 1) := h 1 (by omega)
  unfold decodeOrdEdit
  by_cases ht0 : m₁ a₁ = 0
  · simp [h0, ht0, h1]
  · by_cases ht12 : m₁ a₁ = 1 ∨ m₁ a₁ = 2
    · have hw : (decodeOrdEdit m₁ a₁).2 = 4 + m₁ (a₁ + 3) := by
        rcases ht12 with ht1 | ht2
        · simp [decodeOrdEdit, ht1]
        · simp [decodeOrdEdit, ht2]
      have h2 : m₂ (a₂ + 2) = m₁ (a₁ + 2) := h 2 (by omega)
      have h3 : m₂ (a₂ + 3) = m₁ (a₁ + 3) := h 3 (by omega)
      have hrl : readList m₂ (a₂ + 4) (m₁ (a₁ + 3)) = readList m₁ (a₁ + 4) (m₁ (a₁ + 3)) :=
        tour_readList_shift fun i hi => by
          have := h (4 + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
      simp [h0, ht0, ht12, h1, h2, h3, hrl]
    · by_cases ht3 : m₁ a₁ = 3
      · have hw : (decodeOrdEdit m₁ a₁).2 = 4 := by simp [decodeOrdEdit, ht3]
        have h2 : m₂ (a₂ + 2) = m₁ (a₁ + 2) := h 2 (by omega)
        have h3 : m₂ (a₂ + 3) = m₁ (a₁ + 3) := h 3 (by omega)
        simp [h0, ht3, h1, h2, h3]
      · have hw : (decodeOrdEdit m₁ a₁).2 = 3 := by simp [decodeOrdEdit, ht0, ht12, ht3]
        have h2 : m₂ (a₂ + 2) = m₁ (a₁ + 2) := h 2 (by omega)
        simp [h0, ht0, ht12, ht3, h1, h2]

theorem tour_decodeOrdEdits_shift {m₁ m₂ : ℕ → ℕ} :
    ∀ (count a₁ a₂ : ℕ),
      (∀ i < ((decodeOrdEdits m₁ count a₁).2).sum, m₂ (a₂ + i) = m₁ (a₁ + i)) →
      decodeOrdEdits m₂ count a₂ = decodeOrdEdits m₁ count a₁
  | 0, _, _, _ => rfl
  | count + 1, a₁, a₂, h => by
    have hsum : ((decodeOrdEdits m₁ (count + 1) a₁).2).sum =
        (decodeOrdEdit m₁ a₁).2 + ((decodeOrdEdits m₁ count (a₁ + (decodeOrdEdit m₁ a₁).2)).2).sum := by
      simp [decodeOrdEdits]
    have hd := tour_decodeOrdEdit_shift (m₁ := m₁) (m₂ := m₂) (a₁ := a₁) (a₂ := a₂) fun i hi =>
      h i (by omega)
    have hrest := tour_decodeOrdEdits_shift (m₁ := m₁) (m₂ := m₂) count (a₁ + (decodeOrdEdit m₁ a₁).2)
      (a₂ + (decodeOrdEdit m₁ a₁).2) fun i hi => by
        have := h ((decodeOrdEdit m₁ a₁).2 + i) (by omega)
        rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
    simp only [decodeOrdEdits, hd, hrest]

theorem tourEditValid_to_ordEditsWithin {vCap eCap : ℕ} {s : TourAbs} {edit : OrdEdit}
    (h : TourEditValid vCap eCap s edit) : OrdEditsWithin vCap eCap [edit] := by
  intro e he; simp only [List.mem_singleton] at he; subst he
  cases e with
  | dropEdge e => exact h.1
  | moveEnds v v' sel c => exact ⟨h.1, h.2.1, h.2.2.2.2.2.2⟩
  | insertBefore v x y => exact ⟨h.1, h.2.2.1, h.2.2.2.2.2⟩
  | rotateTo v y => exact h

theorem tour_singleEdit_ordEditsAt_simple {mem : ℕ → ℕ} {p : ℕ} {edit : OrdEdit} {wk : ℕ}
    (hp1 : mem p = 1) (hd : decodeOrdEdit mem (p + 1) = (edit, wk)) (hwk : wk ≤ 5) :
    OrdEditsAt mem p [edit] (1 + wk) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [readOrdEdits, hp1, decodeOrdEdits, hd]
  · simp [hp1, decodeOrdEdits, hd]
  · have henc : 1 ≤ OrdEdit.enc edit := by cases edit <;> simp [OrdEdit.enc]
    simp only [ordEditsEnc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

theorem tour_singleEdit_ordEditsAt_move {mem : ℕ → ℕ} {p v v' m' : ℕ} {c : Bool} {U : List End}
    (h0 : mem p = 1) (h1 : mem (p + 1) = if c then 2 else 1)
    (h2 : mem (p + 2) = v) (h3 : mem (p + 3) = v') (h4 : mem (p + 4) = m')
    (hUlen : U.length = m') (hUnd : U.Nodup)
    (hUmem : ∀ j (hj : j < U.length), mem (p + 5 + j) = endKey U[j]) :
    OrdEditsAt mem p [.moveEnds v v' U.toFinset c] (5 + m') := by
  have hrl : (readList mem (p + 5) m').map endOfKey = U := by
    apply List.ext_getElem (by simp [readList_length, hUlen])
    intro j hj _
    have hj' : j < m' := by simpa [readList_length] using hj
    rw [List.getElem_map, readList_getElem, hUmem j (by omega), endOfKey_endKey]
  have hd : decodeOrdEdit mem (p + 1) = (.moveEnds v v' U.toFinset c, 4 + m') := by
    cases c <;> simp [decodeOrdEdit, h1, h2, h3, h4, Nat.add_assoc, hrl]
  refine ⟨?_, ?_, ?_⟩
  · simp [readOrdEdits, h0, decodeOrdEdits, hd]
  · simp [h0, decodeOrdEdits, hd]; omega
  · have hcard : U.toFinset.card = m' := by rw [List.toFinset_card_of_nodup hUnd, hUlen]
    simp [ordEditsEnc, OrdEdit.enc, hcard]; omega

/-! ## Op 0 body, procedure bundle, space bound, and step cost helpers -/

/-- Linear heap space bound for Op 0 (`applyEdits`), independent of `heap`. -/
def tourOp0Space (words : ℕ) : ℕ := 12 * words + 12

/-- Base amortized per-`(words + 1) * tourLog` multiplier for Op 0 (excluding `mul_ord`). -/
def TOUR_OP0_BASE_MUL : ℕ := TOUR_MOVE_MUL + 2 * TOUR_EDIT_SIMPLE_MUL + 2000

/-- Amortized per-`(words + 1) * tourLog` multiplier for Op 0 (excluding `mul_ord`). -/
def TOUR_OP0_MUL : ℕ := TOUR_OP0_BASE_MUL + 200

/-- Dispatch loop for `tourOpApplyEditsBody`: processes `r4` edits starting at `r5`, advancing
heap cursor `r6` and counter `r7`, with `ordStore` handle in `r14`. -/
def tourEditsDispatchLoop (dropProc moveProc insProc rotProc dedupProc ordOp0 : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 7) (.reg 4))
    (.assign 8 (.load (.reg 5)) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
        .call 6 dropProc [.reg 0, .reg 9, .reg 6] ;;
        .assign 10 (.bin .sub (.reg 5) (.const 1)) ;;
        .store (.reg 10) (.const 1) ;;
        .assign 11 (.const 3) ;;
        .call 6 ordOp0 [.reg 14, .reg 10, .reg 11, .reg 6] ;;
        .assign 5 (.bin .add (.reg 5) (.const 2)))
       (.cond (.bin .lt (.reg 8) (.const 3))
         (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
          .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
          .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
          .assign 12 (.bin .add (.reg 5) (.const 4)) ;;
          .call 6 moveProc [.reg 0, .reg 5, .reg 6] ;;
          .store (.reg 6) (.const 1) ;;
          .store (.bin .add (.reg 6) (.const 1)) (.reg 8) ;;
          .store (.bin .add (.reg 6) (.const 2)) (.reg 9) ;;
          .store (.bin .add (.reg 6) (.const 3)) (.reg 10) ;;
          .assign 13 (.bin .add (.reg 6) (.const 5)) ;;
          .call 15 dedupProc [.reg 0, .reg 12, .reg 11, .reg 13] ;;
          .store (.bin .add (.reg 6) (.const 4)) (.reg 15) ;;
          .assign 13 (.bin .add (.const 5) (.reg 15)) ;;
          .assign 15 (.bin .add (.reg 6) (.reg 13)) ;;
          .call 6 ordOp0 [.reg 14, .reg 6, .reg 13, .reg 15] ;;
          .assign 5 (.bin .add (.reg 12) (.reg 11)))
         (.cond (.bin .eq (.reg 8) (.const 3))
           (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
            .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
            .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
            .call 6 insProc [.reg 0, .reg 9, .reg 10, .reg 11, .reg 6] ;;
            .assign 10 (.bin .sub (.reg 5) (.const 1)) ;;
            .store (.reg 10) (.const 1) ;;
            .assign 11 (.const 5) ;;
            .call 6 ordOp0 [.reg 14, .reg 10, .reg 11, .reg 6] ;;
            .assign 5 (.bin .add (.reg 5) (.const 4)))
           (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
            .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
            .call 6 rotProc [.reg 0, .reg 9, .reg 10, .reg 6] ;;
            .assign 10 (.bin .sub (.reg 5) (.const 1)) ;;
            .store (.reg 10) (.const 1) ;;
            .assign 11 (.const 4) ;;
            .call 6 ordOp0 [.reg 14, .reg 10, .reg 11, .reg 6] ;;
            .assign 5 (.bin .add (.reg 5) (.const 3))))) ;;
     .assign 7 (.bin .add (.reg 7) (.const 1)))

/-- Op 0 (`applyEdits`): args `[b, edits, words, heap]`. -/
def tourOpApplyEditsBody (dropProc moveProc insProc rotProc dedupProc ordOp0 : ℕ) : Stmt :=
  .assign 4 (.const 0) ;;
  .assign 5 (.bin .add (.reg 3) (.const 1)) ;;
  tourEditsCopyLoop ;;
  .assign 4 (.load (.reg 5)) ;;
  .assign 5 (.bin .add (.reg 5) (.const 1)) ;;
  .assign 6 (.bin .add (.bin .add (.reg 3) (.const 1)) (.reg 2)) ;;
  .assign 7 (.const 0) ;;
  .assign 14 (.load (.bin .add (.reg 0) (.const HDR_ORD_H))) ;;
  tourEditsDispatchLoop dropProc moveProc insProc rotProc dedupProc ordOp0 ;;
  .ret (.reg 6)

theorem tourOpApplyEditsBody_noRand (dP mP iP rP ddP o0 : ℕ) :
    (tourOpApplyEditsBody dP mP iP rP ddP o0).NoRand := by
  have ⟨_, hcp⟩ := tourEditsPrep_noRand
  simp [tourOpApplyEditsBody, tourEditsDispatchLoop, hcp, Stmt.NoRand]

/-- All sub-procedures required by `tourOpApplyEditsBody`, extending `TourSplayQueryProcs`. -/
structure TourEditProcs (w : ℕ) (p : Program) (ordOp0 ordOp2 : ℕ)
    extends TourSplayQueryProcs w p where
  dropOneProc : ℕ
  dropOne_body : p.procs[dropOneProc]? =
    some (tourDropOneBody deleteNode setValNode rotateFront ordOp2)
  dropProc : ℕ
  drop_body : p.procs[dropProc]? = some (tourEditDropBody dropOneProc)
  rankProc : ℕ
  rank_body : p.procs[rankProc]? = some (tourSplayRankBody splay.splay)
  siftProc : ℕ
  sift_body : p.procs[siftProc]? = some (ordSiftDownBody siftProc)
  sortProc : ℕ
  sort_body : p.procs[sortProc]? = some (ordHeapSortBody siftProc)
  collectProc : ℕ
  collect_body : p.procs[collectProc]? = some tourMoveCollectBody
  rankSortProc : ℕ
  rankSort_body : p.procs[rankSortProc]? =
    some (tourMoveRankSortNextBody rankProc sortProc ordOp2)
  splitLoopProc : ℕ
  splitLoop_body : p.procs[splitLoopProc]? =
    some (tourMoveSplitLoopBody splay.splay detachLeft join)
  walkFrontProc : ℕ
  walkFront_body : p.procs[walkFrontProc]? = some (tourWalkFrontBody walkProc splay.splay)
  moveProc : ℕ
  move_body : p.procs[moveProc]? =
    some (tourEditMoveBody splay.splay setValNode rotateFront
      collectProc rankSortProc splitLoopProc walkFrontProc)
  insProc : ℕ
  ins_body : p.procs[insProc]? =
    some (tourEditInsertBody initNode insertBefore setValNode rotateFront)
  rotProc : ℕ
  rot_body : p.procs[rotProc]? = some (tourEditRotateBody setValNode rotateFront)
  dedupProc : ℕ
  dedup_body : p.procs[dedupProc]? = some tourDedupSelBody

theorem op0_step_cost_drop (mul_ord tl : ℕ) (htl : 1 ≤ tl) :
    (2 * TOUR_EDIT_SIMPLE_MUL + 4 * mul_ord + 30) * tl + mul_ord * 4 * tl + 100 ≤
      2 * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tl := by
  have h1 : (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tl =
      TOUR_MOVE_MUL * tl + 2 * TOUR_EDIT_SIMPLE_MUL * tl + 2000 * tl + 6 * mul_ord * tl := by
    unfold TOUR_OP0_BASE_MUL; ring
  nlinarith

theorem op0_step_cost_move (len m' mul_ord tl : ℕ) (hm : m' ≤ len) (htl : 1 ≤ tl) :
    (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tl + (95 * len + 60) + mul_ord * (5 + m' + 1) * tl + 200 ≤
      (4 + len) * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tl := by
  have h1 : (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tl ≤ (4 + len) * (TOUR_MOVE_MUL + mul_ord) * tl :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have h2 : mul_ord * (5 + m' + 1) * tl ≤ (4 + len) * (2 * mul_ord) * tl := by
    have : 5 + m' + 1 ≤ 2 * (4 + len) := by omega
    have hmul : mul_ord * (5 + m' + 1) ≤ mul_ord * (2 * (4 + len)) := Nat.mul_le_mul_left _ this
    have hmul2 := Nat.mul_le_mul_right tl hmul
    have heq : mul_ord * (2 * (4 + len)) * tl = (4 + len) * (2 * mul_ord) * tl := by ring
    omega
  have h3 : (4 + len) * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tl =
      (4 + len) * (TOUR_MOVE_MUL + mul_ord) * tl + (4 + len) * (2 * mul_ord) * tl +
      (4 + len) * (2 * TOUR_EDIT_SIMPLE_MUL + 2000 + 3 * mul_ord) * tl := by
    unfold TOUR_OP0_BASE_MUL; ring
  have h4 : 95 * len + 260 ≤ (4 + len) * (2 * TOUR_EDIT_SIMPLE_MUL + 2000 + 3 * mul_ord) * tl := by
    have h4a : 95 * len + 260 ≤ (4 + len) * 2000 := by omega
    have h4b : 2000 ≤ 2 * TOUR_EDIT_SIMPLE_MUL + 2000 + 3 * mul_ord := by omega
    calc 95 * len + 260 ≤ (4 + len) * 2000 * 1 := by omega
      _ ≤ (4 + len) * (2 * TOUR_EDIT_SIMPLE_MUL + 2000 + 3 * mul_ord) * tl :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h4b) htl
  omega

theorem op0_step_cost_simple (wk mul_ord tl : ℕ) (hwk : 3 ≤ wk) (hwk' : wk ≤ 4) (htl : 1 ≤ tl) :
    TOUR_EDIT_SIMPLE_MUL * tl + mul_ord * (1 + wk + 1) * tl + 120 ≤
      wk * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tl := by
  have h1 : (1 + wk + 1) ≤ 6 * wk := by omega
  have h2 : mul_ord * (1 + wk + 1) * tl ≤ wk * (6 * mul_ord) * tl := by
    have := Nat.mul_le_mul_right tl (Nat.mul_le_mul_left mul_ord h1)
    have heq : mul_ord * (6 * wk) * tl = wk * (6 * mul_ord) * tl := by ring
    omega
  have h3 : wk * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tl =
      wk * TOUR_OP0_BASE_MUL * tl + wk * (6 * mul_ord) * tl := by ring
  have h4 : TOUR_EDIT_SIMPLE_MUL * tl + 120 ≤ wk * TOUR_OP0_BASE_MUL * tl := by
    have : TOUR_EDIT_SIMPLE_MUL + 120 ≤ wk * TOUR_OP0_BASE_MUL := by
      unfold TOUR_OP0_BASE_MUL; nlinarith
    nlinarith
  omega

end MinCostFlow.SparseCore.Program
