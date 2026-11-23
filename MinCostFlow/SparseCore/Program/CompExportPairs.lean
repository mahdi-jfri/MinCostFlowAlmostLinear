module

public import MinCostFlow.SparseCore.Program.CompExportBase
import MinCostFlow.SparseCore.Program.CompReadout
import MinCostFlow.SparseCore.CompLSFBridge
import WordRAM.Tactic

/-!
# Branch Weight-Pair Export Loop (`CompExportPairs`)

Implements and verifies `compExpPairsStmt` for `op 6` (`compExportBranchProc`):
iterates `i = 0 .. (S j).G.m - 1` over the active edge list `dgEListBase gPtr vCap0 eCap0` and
copies the `L_w`-limb numerator and denominator for `(S j).wstrGlobal e` into
`numPtr + e * L_w` and `denPtr + e * L_w`, in `O((G.m + 1) * L_w)` time.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- Inner loop of `compExpPairsStmt`: copies `r7 = L_w` limbs from `r16` to `r18` and from `r17`
to `r19`. Preserves registers `< 20`. -/
def compExpPairCopyStmt : Stmt :=
  .loop (.bin .lt (.reg 20) (.reg 7))
    (.store (.bin .add (.reg 18) (.reg 20)) (.load (.bin .add (.reg 16) (.reg 20))) ;;
     .store (.bin .add (.reg 19) (.reg 20)) (.load (.bin .add (.reg 17) (.reg 20))) ;;
     .assign 20 (.bin .add (.reg 20) (.const 1)))

/-- Export numerator and denominator limb arrays for all active edges `e ∈ (S j).G.E`.
Inputs: `r0 = b`, `r1 = j`, `r2 = k`, `r3 = eListPtr`, `r4 = mG`, `r5 = numPtr`, `r6 = denPtr`.
Preserves `r0..r6`; uses scratch registers `7..20`. -/
def compExpPairsStmt : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const compOffLW))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const compOffOneLimbPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const compOffEdgeC1Ptr))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
  .assign 13 (.const 0) ;;
  .loop (.bin .lt (.reg 13) (.reg 4))
    (.assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
     .assign 15 (.load (.bin .add (.reg 8) (.reg 14))) ;;
     .cond (.reg 15)
       (.assign 16 (.reg 9) ;;
        .assign 17 (.reg 9))
       (.assign 16 (.load (.bin .add (.reg 10) (.reg 14))) ;;
        .assign 16 (.load (.bin .add (.reg 11) (.reg 16))) ;;
        .assign 16 (.load (.bin .add (.reg 12) (.bin .add (.bin .mul (.reg 16) (.reg 2)) (.reg 1)))) ;;
        .assign 17 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrDenPtr)))
          (.bin .mul (.reg 14) (.reg 7))) ;;
        .assign 16 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrNumPtr)))
          (.bin .mul (.reg 14) (.reg 7)))) ;;
     .assign 18 (.bin .add (.reg 5) (.bin .mul (.reg 14) (.reg 7))) ;;
     .assign 19 (.bin .add (.reg 6) (.bin .mul (.reg 14) (.reg 7))) ;;
     .assign 20 (.const 0) ;;
     compExpPairCopyStmt ;;
     .assign 13 (.bin .add (.reg 13) (.const 1)))

lemma compExpPairsStmt_noRand : compExpPairsStmt.NoRand := by
  simp [compExpPairsStmt, compExpPairCopyStmt, Stmt.NoRand]

private lemma compExpPairCopy_runs {w L srcN srcD dstN dstD : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hdisjN : srcN + L ≤ dstN) (hdisjD : srcD + L ≤ dstN)
    (hND : dstN + L ≤ dstD)
    (hdstD_w : dstD + L < 2 ^ w)
    (hr7 : st.regs 7 = L) (hr16 : st.regs 16 = srcN) (hr17 : st.regs 17 = srcD)
    (hr18 : st.regs 18 = dstN) (hr19 : st.regs 19 = dstD) (hr20 : st.regs 20 = 0) :
    ∃ st' c,
      Runs w p ω compExpPairCopyStmt st .normal st' c ∧
      (∀ r < 20, st'.regs r = st.regs r) ∧
      (∀ t < L, st'.mem (dstN + t) = st.mem (srcN + t) ∧ st'.mem (dstD + t) = st.mem (srcD + t)) ∧
      (∀ a, (a < dstN ∨ dstN + L ≤ a) → (a < dstD ∨ dstD + L ≤ a) → st'.mem a = st.mem a) ∧
      c ≤ 30 * L + 5 := by
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hloop : ∀ rem t (s : State), t ≤ L → L - t = rem →
      (∀ r < 20, s.regs r = st.regs r) → s.regs 20 = t →
      (∀ q < t, s.mem (dstN + q) = st.mem (srcN + q) ∧ s.mem (dstD + q) = st.mem (srcD + q)) →
      (∀ a, (a < dstN ∨ dstN + t ≤ a) → (a < dstD ∨ dstD + t ≤ a) → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω compExpPairCopyStmt s .normal st' c ∧
        (∀ r < 20, st'.regs r = st.regs r) ∧
        (∀ q < L, st'.mem (dstN + q) = st.mem (srcN + q) ∧ st'.mem (dstD + q) = st.mem (srcD + q)) ∧
        (∀ a, (a < dstN ∨ dstN + L ≤ a) → (a < dstD ∨ dstD + L ≤ a) → st'.mem a = st.mem a) ∧
        c ≤ 30 * rem + 5 := by
    intro rem
    induction rem with
    | zero =>
      intro t s ht hrem hr_o hr20 hdone hfr
      have ht_eq : t = L := by omega
      subst ht_eq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr20, hr_o 7 (by omega), hr7],
        rfl, rfl, by simp [Expr.size]⟩), hr_o, hdone, hfr, by omega⟩
    | succ rem ih =>
      intro t s ht hrem hr_o hr20 hdone hfr
      have ht_lt : t < L := by omega
      set vN := st.mem (srcN + t)
      set vD := st.mem (srcD + t)
      have hsN : s.mem (srcN + t) = vN := hfr _ (Or.inl (by omega)) (Or.inl (by omega))
      have hsD : s.mem (srcD + t) = vD := hfr _ (Or.inl (by omega)) (Or.inl (by omega))
      let m1 := Function.update s.mem (dstN + t) vN
      let m2 := Function.update m1 (dstD + t) vD
      let s1 : State := { s with mem := m1 }
      let s2 : State := { s1 with mem := m2 }
      let s3 : State := { s2 with regs := Function.update s2.regs 20 (t + 1) }
      have h1 : Runs w p ω (.store (.bin .add (.reg 18) (.reg 20)) (.load (.bin .add (.reg 16) (.reg 20)))) s .normal s1 8 :=
        runs_store_iff.mpr ⟨dstN + t, vN,
          by simp [Expr.eval, BinOp.eval, hr_o 18 (by omega), hr18, hr20, show dstN + t < 2 ^ w by omega],
          Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr_o 16 (by omega), hr16, hr20, show srcN + t < 2 ^ w by omega]) hsN,
          rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.store (.bin .add (.reg 19) (.reg 20)) (.load (.bin .add (.reg 17) (.reg 20)))) s1 .normal s2 8 :=
        runs_store_iff.mpr ⟨dstD + t, vD,
          by simp [s1, Expr.eval, BinOp.eval, hr_o 19 (by omega), hr19, hr20, show dstD + t < 2 ^ w by omega],
          Expr.eval_load_of_eq (x := srcD + t) (by simp [s1, Expr.eval, BinOp.eval, hr_o 17 (by omega), hr17, hr20, show srcD + t < 2 ^ w by omega])
            (by dsimp only [s1, m1]; rw [Function.update_of_ne (by omega)]; exact hsD),
          rfl, rfl, by simp [Expr.size]⟩
      have h3 : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1))) s2 .normal s3 4 :=
        runs_assign_iff.mpr ⟨t + 1, by simp [s2, s1, Expr.eval, BinOp.eval, hr20, hw1, show t + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal s3 22 :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 8, _, h1, runs_seq_iff.mpr (Or.inr ⟨s2, 8, 4, h2, h3, rfl⟩), rfl⟩)
      obtain ⟨st', cRest, hrest, hr'_o, hdone', hfr', hcRest⟩ :=
        ih (t + 1) s3 (by omega) (by omega)
          (fun r hr => by simp [s3, s2, s1, show r ≠ 20 by omega, hr_o r hr]) (by simp [s3])
          (fun q hq => by
            dsimp only [s3, s2, m2, m1]
            by_cases hqt : q = t
            · subst hqt; simp [Function.update_of_ne (by omega : dstN + q ≠ dstD + q), vN, vD]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hdone q (by omega))
          (fun a haN haD => by
            dsimp only [s3, s2, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfr a (by omega) (by omega))
      have hfull : Runs w p ω compExpPairCopyStmt s .normal st' (22 + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, 22, cRest,
          by simp [Expr.eval, BinOp.eval, hr20, hr_o 7 (by omega), hr7, ht_lt, hw0], by decide,
          by simpa using hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 22 + cRest + 4, hfull, hr'_o, hdone', hfr', by omega⟩
  exact hloop L 0 st (Nat.zero_le _) (Nat.sub_zero _) (fun _ _ => rfl) hr20
    (fun _ h => by omega) (fun _ _ _ => rfl)

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compExpPairsStmt`: writes valid numerator/denominator `L_w`-limb tables
at `numPtr` and `denPtr` for every `e ∈ (S j).G.E`, preserving memory outside
`[numPtr, numPtr + eCap * L_w) ∪ [denPtr, denPtr + eCap * L_w)`, in
`≤ 35 * (S j).G.m * x.L_w + 95 * (S j).G.m + 45` steps. -/
theorem compExpPairs_runs {W : LSFWindowImpl} {w k b eListPtr numPtr denPtr : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k} {eL : List ℕ}
    {st : State} {ω : ℕ → Bool} (j : Fin k)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepAt W k b S x st.mem)
    (heL_len : eL.length = (S j).G.m)
    (heL_nd : eL.Nodup)
    (heL_mem : ∀ e, e ∈ eL ↔ e ∈ (S j).G.E)
    (heL_at : ListAt st.mem eListPtr eL)
    (heL_disj : ∀ a, numPtr ≤ a → a < numPtr + x.eCap * x.L_w → a < eListPtr ∨ eListPtr + eL.length ≤ a)
    (heL_disjD : ∀ a, denPtr ≤ a → a < denPtr + x.eCap * x.L_w → a < eListPtr ∨ eListPtr + eL.length ≤ a)
    (heL_w : eListPtr + eL.length < 2 ^ w)
    (hend_le : x.endAddr ≤ numPtr)
    (hnum_den : numPtr + x.eCap * x.L_w ≤ denPtr)
    (hden_w : denPtr + x.eCap * x.L_w < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = j.1) (hr2 : st.regs 2 = k)
    (hr3 : st.regs 3 = eListPtr) (hr4 : st.regs 4 = (S j).G.m)
    (hr5 : st.regs 5 = numPtr) (hr6 : st.regs 6 = denPtr) :
    ∃ st' c,
      Runs w p ω compExpPairsStmt st .normal st' c ∧
      (∀ r < 7, st'.regs r = st.regs r) ∧
      (∀ e ∈ (S j).G.E,
        Valid st'.mem (numPtr + e * x.L_w) W.h x.L_w ∧
        Valid st'.mem (denPtr + e * x.L_w) W.h x.L_w ∧
        1 ≤ intVal st'.mem (numPtr + e * x.L_w) W.h x.L_w ∧
        1 ≤ intVal st'.mem (denPtr + e * x.L_w) W.h x.L_w ∧
        (intVal st'.mem (numPtr + e * x.L_w) W.h x.L_w : ℝ) /
          (intVal st'.mem (denPtr + e * x.L_w) W.h x.L_w : ℝ) = (S j).wstrGlobal e) ∧
      (∀ a, (a < numPtr ∨ numPtr + x.eCap * x.L_w ≤ a) →
        (a < denPtr ∨ denPtr + x.eCap * x.L_w ≤ a) → st'.mem a = st.mem a) ∧
      (∀ a, (∀ e ∈ (S j).G.E,
        (a < numPtr + e * x.L_w ∨ numPtr + e * x.L_w + x.L_w ≤ a) ∧
        (a < denPtr + e * x.L_w ∨ denPtr + e * x.L_w + x.L_w ≤ a)) → st'.mem a = st.mem a) ∧
      c ≤ 35 * (S j).G.m * x.L_w + 95 * (S j).G.m + 45 := by
  obtain ⟨hk, hxh, _, _, hxLw, hx2h, _, hnc, hne, hTE, hhdr, ⟨ℓ₀, hBr⟩, _, hT,
    hCompInfo, _, _, hEdgeC, hFlags, _, _, hOne, hWins, _⟩ := hrep
  have ⟨hInv_j, hG0_j, hG_j, _, _, hIns_j, hCG_j⟩ := hBr j
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_hdr_lt : b + compHdrSize ≤ x.endAddr := by
    dsimp only [compStaticSize, compHdrSize] at hStat ⊢; omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_lt hoff; omega
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  -- Prefix (7 assigns)
  let s1 : State := { st with regs := Function.update st.regs 7 x.L_w }
  let s2 : State := { s1 with regs := Function.update s1.regs 8 (compIsInsBase b x.vCap x.eCap) }
  let s3 : State := { s2 with regs := Function.update s2.regs 9 (compOneLimbBase b x.vCap x.eCap) }
  let s4 : State := { s3 with regs := Function.update s3.regs 10 (compEdgeC1Base b x.vCap) }
  let s5 : State := { s4 with regs := Function.update s4.regs 11 (compEdgefulIdxBase b x.vCap) }
  let s6 : State := { s5 with regs := Function.update s5.regs 12 (compHandlesBase b x.vCap x.eCap x.L_w) }
  let s7 : State := { s6 with regs := Function.update s6.regs 13 0 }
  have hp1 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const compOffLW)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨x.L_w, Expr.eval_load_of_eq (by
      have := hb_off compOffLW (by decide); simp [Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨compIsInsBase b x.vCap x.eCap, Expr.eval_load_of_eq (by
      have := hb_off compOffIsInsPtr (by decide); simp [s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const compOffOneLimbPtr)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨compOneLimbBase b x.vCap x.eCap, Expr.eval_load_of_eq (by
      have := hb_off compOffOneLimbPtr (by decide); simp [s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const compOffEdgeC1Ptr)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨compEdgeC1Base b x.vCap, Expr.eval_load_of_eq (by
      have := hb_off compOffEdgeC1Ptr (by decide); simp [s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨compEdgefulIdxBase b x.vCap, Expr.eval_load_of_eq (by
      have := hb_off compOffEdgefulIdxPtr (by decide); simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨compHandlesBase b x.vCap x.eCap x.L_w, Expr.eval_load_of_eq (by
      have := hb_off compOffHandlesPtr (by decide); simp [s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 13 (.const 0)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Loop statement
  let loopStmt : Stmt :=
    .loop (.bin .lt (.reg 13) (.reg 4))
      (.assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
       .assign 15 (.load (.bin .add (.reg 8) (.reg 14))) ;;
       .cond (.reg 15)
         (.assign 16 (.reg 9) ;;
          .assign 17 (.reg 9))
         (.assign 16 (.load (.bin .add (.reg 10) (.reg 14))) ;;
          .assign 16 (.load (.bin .add (.reg 11) (.reg 16))) ;;
          .assign 16 (.load (.bin .add (.reg 12) (.bin .add (.bin .mul (.reg 16) (.reg 2)) (.reg 1)))) ;;
          .assign 17 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrDenPtr)))
            (.bin .mul (.reg 14) (.reg 7))) ;;
          .assign 16 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrNumPtr)))
            (.bin .mul (.reg 14) (.reg 7)))) ;;
       .assign 18 (.bin .add (.reg 5) (.bin .mul (.reg 14) (.reg 7))) ;;
       .assign 19 (.bin .add (.reg 6) (.bin .mul (.reg 14) (.reg 7))) ;;
       .assign 20 (.const 0) ;;
       compExpPairCopyStmt ;;
       .assign 13 (.bin .add (.reg 13) (.const 1)))
  have hloop : ∀ rem i (s : State) (hi : i ≤ eL.length), eL.length - i = rem →
      (∀ r < 7, s.regs r = st.regs r) →
      s.regs 7 = x.L_w → s.regs 8 = compIsInsBase b x.vCap x.eCap →
      s.regs 9 = compOneLimbBase b x.vCap x.eCap → s.regs 10 = compEdgeC1Base b x.vCap →
      s.regs 11 = compEdgefulIdxBase b x.vCap → s.regs 12 = compHandlesBase b x.vCap x.eCap x.L_w →
      s.regs 13 = i →
      (∀ q (hq : q < i),
        let e := eL[q]'(by omega)
        Valid s.mem (numPtr + e * x.L_w) W.h x.L_w ∧
        Valid s.mem (denPtr + e * x.L_w) W.h x.L_w ∧
        1 ≤ intVal s.mem (numPtr + e * x.L_w) W.h x.L_w ∧
        1 ≤ intVal s.mem (denPtr + e * x.L_w) W.h x.L_w ∧
        (intVal s.mem (numPtr + e * x.L_w) W.h x.L_w : ℝ) /
          (intVal s.mem (denPtr + e * x.L_w) W.h x.L_w : ℝ) = (S j).wstrGlobal e) →
      (∀ a, (a < numPtr ∨ numPtr + x.eCap * x.L_w ≤ a) →
        (a < denPtr ∨ denPtr + x.eCap * x.L_w ≤ a) → s.mem a = st.mem a) →
      (∀ a, (∀ e ∈ (S j).G.E,
        (a < numPtr + e * x.L_w ∨ numPtr + e * x.L_w + x.L_w ≤ a) ∧
        (a < denPtr + e * x.L_w ∨ denPtr + e * x.L_w + x.L_w ≤ a)) → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω loopStmt s .normal st' c ∧
        (∀ r < 7, st'.regs r = st.regs r) ∧
        (∀ q (hq : q < eL.length),
          let e := eL[q]'hq
          Valid st'.mem (numPtr + e * x.L_w) W.h x.L_w ∧
          Valid st'.mem (denPtr + e * x.L_w) W.h x.L_w ∧
          1 ≤ intVal st'.mem (numPtr + e * x.L_w) W.h x.L_w ∧
          1 ≤ intVal st'.mem (denPtr + e * x.L_w) W.h x.L_w ∧
          (intVal st'.mem (numPtr + e * x.L_w) W.h x.L_w : ℝ) /
            (intVal st'.mem (denPtr + e * x.L_w) W.h x.L_w : ℝ) = (S j).wstrGlobal e) ∧
        (∀ a, (a < numPtr ∨ numPtr + x.eCap * x.L_w ≤ a) →
          (a < denPtr ∨ denPtr + x.eCap * x.L_w ≤ a) → st'.mem a = st.mem a) ∧
        (∀ a, (∀ e ∈ (S j).G.E,
          (a < numPtr + e * x.L_w ∨ numPtr + e * x.L_w + x.L_w ≤ a) ∧
          (a < denPtr + e * x.L_w ∨ denPtr + e * x.L_w + x.L_w ≤ a)) → st'.mem a = st.mem a) ∧
        c ≤ 35 * rem * x.L_w + 95 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem hr_lt _ _ _ _ _ _ hr13 hdone hfr hfrE
      have hi_eq : i = eL.length := by omega
      subst hi_eq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr13, hr_lt 4 (by omega), hr4, heL_len],
        rfl, rfl, by simp [Expr.size]⟩), hr_lt, hdone, hfr, hfrE, by omega⟩
    | succ rem ih =>
      intro i s hi hrem hr_lt hr7 hr8 hr9 hr10 hr11 hr12 hr13 hdone hfr hfrE
      have hi_lt : i < eL.length := by omega
      set e := eL[i]'hi_lt
      have heG_j : e ∈ (S j).G.E := (heL_mem e).mp (List.getElem_mem hi_lt)
      have heG0 : e ∈ (S ⟨0, hk⟩).G.E := hG_j ▸ heG_j
      have helt : e < x.eCap := hT.hElt e heG0
      have heLw_le : e * x.L_w + x.L_w ≤ x.eCap * x.L_w := by
        have : (e + 1) * x.L_w ≤ x.eCap * x.L_w := Nat.mul_le_mul_right _ helt; linarith
      have hs_below : ∀ a < x.endAddr, s.mem a = st.mem a :=
        fun a ha => hfr a (Or.inl (by omega)) (Or.inl (by omega))
      have hs_eL : s.mem (eListPtr + i) = e := by
        have h1 : eListPtr + i < numPtr ∨ numPtr + x.eCap * x.L_w ≤ eListPtr + i := by
          by_contra h; push_neg at h; have := heL_disj (eListPtr + i) h.1 h.2; omega
        have h2 : eListPtr + i < denPtr ∨ denPtr + x.eCap * x.L_w ≤ eListPtr + i := by
          by_contra h; push_neg at h; have := heL_disjD (eListPtr + i) h.1 h.2; omega
        exact (hfr _ h1 h2).trans (heL_at i hi_lt)
      set insV := if e ∈ (S ⟨0, hk⟩).insertedGlobal then 1 else 0
      have hins_lt : compIsInsBase b x.vCap x.eCap + e < x.endAddr := by
        dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
          compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
      have hs_ins : s.mem (compIsInsBase b x.vCap x.eCap + e) = insV :=
        (hs_below _ hins_lt).trans (hFlags e helt).2
      let a1 : State := { s with regs := Function.update s.regs 14 e }
      let a2 : State := { a1 with regs := Function.update a1.regs 15 insV }
      have ha1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 3) (.reg 13)))) s .normal a1 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr_lt 3 (by omega), hr3, hr13, show eListPtr + i < 2 ^ w by omega])
          hs_eL, rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 8) (.reg 14)))) a1 .normal a2 5 :=
        runs_assign_iff.mpr ⟨insV, Expr.eval_load_of_eq (by
          simp [a1, Expr.eval, BinOp.eval, hr8, show compIsInsBase b x.vCap x.eCap + e < 2 ^ w by omega])
          hs_ins, rfl, rfl, by simp [Expr.size]⟩
      -- Resolve source addresses `(srcN, srcD)` via `if insV ≠ 0`
      have hsrc : ∃ srcN srcD cS,
          Runs w p ω
            (.cond (.reg 15)
              (.assign 16 (.reg 9) ;;
               .assign 17 (.reg 9))
              (.assign 16 (.load (.bin .add (.reg 10) (.reg 14))) ;;
               .assign 16 (.load (.bin .add (.reg 11) (.reg 16))) ;;
               .assign 16 (.load (.bin .add (.reg 12) (.bin .add (.bin .mul (.reg 16) (.reg 2)) (.reg 1)))) ;;
               .assign 17 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrDenPtr)))
                 (.bin .mul (.reg 14) (.reg 7))) ;;
               .assign 16 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrNumPtr)))
                 (.bin .mul (.reg 14) (.reg 7)))))
            a2 .normal
            { a2 with regs := Function.update (Function.update a2.regs 16 srcN) 17 srcD } cS ∧
          srcN + x.L_w ≤ x.endAddr ∧ srcD + x.L_w ≤ x.endAddr ∧
          Valid st.mem srcN W.h x.L_w ∧ Valid st.mem srcD W.h x.L_w ∧
          1 ≤ intVal st.mem srcN W.h x.L_w ∧ 1 ≤ intVal st.mem srcD W.h x.L_w ∧
          (intVal st.mem srcN W.h x.L_w : ℝ) / (intVal st.mem srcD W.h x.L_w : ℝ) = (S j).wstrGlobal e ∧
          cS ≤ 50 := by
        by_cases heIns0 : e ∈ (S ⟨0, hk⟩).insertedGlobal
        · have hins1 : insV = 1 := ite_eq_left heIns0
          have heIns_j : e ∈ (S j).insertedGlobal := hIns_j.symm ▸ heIns0
          have hwstr1 : (S j).wstrGlobal e = 1 := (hInv_j.hIns_wstr_R e heIns_j).1
          set onePtr := compOneLimbBase b x.vCap x.eCap
          have hone_end : onePtr + x.L_w ≤ x.endAddr := by
            have := compOneLimb_end_eq b x.vCap x.eCap x.L_w
            dsimp only [onePtr, compHandlesBase] at this ⊢; omega
          have ⟨hV1, hI1⟩ := compOneLimb_valid_and_intVal W.hh hxLw (hxh ▸ hx2h) hOne.1 hOne.2
          let u1 : State := { a2 with regs := Function.update a2.regs 16 onePtr }
          let u2 : State := { u1 with regs := Function.update u1.regs 17 onePtr }
          have hu1 : Runs w p ω (.assign 16 (.reg 9)) a2 .normal u1 2 :=
            runs_assign_iff.mpr ⟨onePtr, by simp [a2, a1, Expr.eval, hr9, onePtr], rfl, rfl, by simp [Expr.size]⟩
          have hu2 : Runs w p ω (.assign 17 (.reg 9)) u1 .normal u2 2 :=
            runs_assign_iff.mpr ⟨onePtr, by simp [u1, a2, a1, Expr.eval, hr9, onePtr], rfl, rfl, by simp [Expr.size]⟩
          have hth : Runs w p ω (.assign 16 (.reg 9) ;; .assign 17 (.reg 9)) a2 .normal u2 5 :=
            runs_seq_iff.mpr (Or.inr ⟨u1, 2, 2, hu1, hu2, rfl⟩)
          exact ⟨onePtr, onePtr, 7,
            runs_cond_iff.mpr ⟨1, 5, by simp [a2, Expr.eval, hins1], by simpa using hth, by simp [Expr.size]⟩,
            hone_end, hone_end, hV1, hV1, by omega, by omega, by simp [hI1, hwstr1], by omega⟩
        · have hins0 : insV = 0 := ite_eq_right heIns0
          have hni_j : e ∉ (S j).insertedGlobal := fun h => heIns0 (hIns_j ▸ h)
          obtain ⟨c1, c2, hc1, _, _, _, hmemE, hcr_iff, _⟩ := hT.hEdge e heG0
          have hncr0 : e ∉ (S ⟨0, hk⟩).crossEdges := fun hcr => heIns0 ((hBr ⟨0, hk⟩).1.hCross_sub hcr)
          have hc12 : c1 = c2 := by_contra fun hne' => hncr0 (hcr_iff.mpr hne')
          have heC1_0 : e ∈ ((S ⟨0, hk⟩).compSt (x.compOf c1)).G.E := (hmemE c1).mpr ⟨hc12, rfl⟩
          have hC1_mem_j : x.compOf c1 ∈ components (S j).G₀ := hG0_j.symm ▸ hT.compOf_mem c1
          have heC1_j : e ∈ ((S j).compSt (x.compOf c1)).G.E := (hCG_j c1).symm ▸ heC1_0
          have hm_ge1 : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c1)).m := by
            obtain ⟨C', hC', hm', heC', _, _⟩ := nonIns_mem_edgeful (hBr ⟨0, hk⟩).1 heG0 heIns0
            obtain ⟨c', rfl⟩ := (hT.hBij.2 C').mp hC'
            have hc'eq : c' = c1 := ((hmemE c').mp heC').2
            exact hc'eq ▸ hm'
          obtain ⟨ec, _, hec_m, hec_eq⟩ := (hCompInfo c1).2.2.2 hm_ge1
          obtain ⟨hWin_m, hWin_rep, _, heWin, hLwWin, _, hWin_le⟩ := hWins ec j
          set hWin := x.winHandle ec j
          set xWin := x.winConc ec j
          rw [hec_eq] at hWin_rep
          have hWin_h : xWin.h = W.h := hWin_rep.1
          have hWin_hdr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hWin_wstr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          set numBase := lsfWstrNumPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM
          set denBase := lsfWstrDenPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
          have hwstr_sub := lsfWstr_sub_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
          have hWin_hdr_le := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
          dsimp only [LSFConcrete.endAddr] at hWin_le
          have hWstr_e := hWin_wstr.2.2 e heC1_j
          have hwstr_eq : (S j).wstrGlobal e = ((S j).compSt (x.compOf c1)).wstr e := by
            obtain ⟨C', hC', heC', _, hw⟩ := hInv_j.hWstr_surv e heG_j hni_j
            obtain ⟨c', rfl⟩ := (hT.hBij.2 C').mp (hG0_j ▸ hC')
            have hc'eq : c' = c1 := ((hmemE c').mp ((hCG_j c') ▸ heC')).2
            exact hc'eq ▸ hw
          have hnum_end : numBase + e * x.L_w + x.L_w ≤ x.endAddr := by
            have heLw' : e * xWin.L_w + xWin.L_w ≤ xWin.eCap * xWin.L_w := by rw [heWin, hLwWin]; exact heLw_le
            rw [← hLwWin]; dsimp only [numBase, denBase, LSFConcrete.endAddr] at hwstr_sub hWin_le ⊢
            have := hwstr_sub.1; have := hwstr_sub.2; omega
          have hden_end : denBase + e * x.L_w + x.L_w ≤ x.endAddr := by
            have heLw' : e * xWin.L_w + xWin.L_w ≤ xWin.eCap * xWin.L_w := by rw [heWin, hLwWin]; exact heLw_le
            rw [← hLwWin]; dsimp only [numBase, denBase, LSFConcrete.endAddr] at hwstr_sub hWin_le ⊢
            have := hwstr_sub.1; have := hwstr_sub.2; omega
          have hec1_lt : compEdgeC1Base b x.vCap + e < x.endAddr := by
            dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
              compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
          have hefi_lt : compEdgefulIdxBase b x.vCap + c1.1 < x.endAddr := by
            have := lt_of_lt_of_le c1.2 hnc
            dsimp only [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
              compGhostSize, compHdrSize] at hStat ⊢; omega
          have hslot_lt : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) < x.endAddr := by
            have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
            have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
            dsimp only [compTablesEnd] at hTE; omega
          let u1 : State := { a2 with regs := Function.update a2.regs 16 c1.1 }
          let u2 : State := { u1 with regs := Function.update u1.regs 16 ec.1 }
          let u3 : State := { u2 with regs := Function.update u2.regs 16 hWin }
          let u4 : State := { u3 with regs := Function.update u3.regs 17 (denBase + e * x.L_w) }
          let u5 : State := { u4 with regs := Function.update u4.regs 16 (numBase + e * x.L_w) }
          have hu1 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 10) (.reg 14)))) a2 .normal u1 5 :=
            runs_assign_iff.mpr ⟨c1.1, Expr.eval_load_of_eq (x := compEdgeC1Base b x.vCap + e) (by
              simp [a2, a1, Expr.eval, BinOp.eval, hr10, show compEdgeC1Base b x.vCap + e < 2 ^ w by omega])
              ((hs_below _ hec1_lt).trans ((hEdgeC e heG0).1.trans hc1)), rfl, rfl, by simp [Expr.size]⟩
          have hu2 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 11) (.reg 16)))) u1 .normal u2 5 :=
            runs_assign_iff.mpr ⟨ec.1, Expr.eval_load_of_eq (x := compEdgefulIdxBase b x.vCap + c1.1) (by
              simp [u1, a2, a1, Expr.eval, BinOp.eval, hr11, show compEdgefulIdxBase b x.vCap + c1.1 < 2 ^ w by omega])
              ((hs_below _ hefi_lt).trans hec_m), rfl, rfl, by simp [Expr.size]⟩
          have hu3 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 12) (.bin .add (.bin .mul (.reg 16) (.reg 2)) (.reg 1))))) u2 .normal u3 9 :=
            runs_assign_iff.mpr ⟨hWin, Expr.eval_load_of_eq (x := compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) (by
              simp [u2, u1, a2, a1, Expr.eval, BinOp.eval, hr12, hr_lt 2 (by omega), hr2, hr_lt 1 (by omega), hr1,
                show ec.1 * k < 2 ^ w by omega, show ec.1 * k + j.1 < 2 ^ w by omega,
                show compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) < 2 ^ w by omega])
              ((hs_below _ hslot_lt).trans hWin_m), rfl, rfl, by simp [Expr.size]⟩
          have hu4 : Runs w p ω (.assign 17 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrDenPtr)))
              (.bin .mul (.reg 14) (.reg 7)))) u3 .normal u4 9 :=
            runs_assign_iff.mpr ⟨denBase + e * x.L_w, by
              have hld : (Expr.load (.bin .add (.reg 16) (.const lsfOffWstrDenPtr))).eval w u3 = some denBase :=
                Expr.eval_load_of_eq (x := hWin + lsfOffWstrDenPtr)
                  (by simp [u3, u2, u1, a2, a1, Expr.eval, BinOp.eval,
                    show lsfOffWstrDenPtr < 2 ^ w by dsimp only [lsfOffWstrDenPtr]; omega,
                    show hWin + lsfOffWstrDenPtr < 2 ^ w by dsimp only [lsfOffWstrDenPtr, lsfHdrSize] at hWin_hdr_le ⊢; omega])
                  ((hs_below _ (by dsimp only [lsfOffWstrDenPtr, lsfHdrSize] at hWin_hdr_le ⊢; omega)).trans
                    hWin_hdr.2.2.2.2.2.2.2.2.2.2.1)
              exact Expr.eval_add hld
                (Expr.eval_mul (by simp [u3, u2, u1, a2, a1, Expr.eval])
                  (by simp [u3, u2, u1, a2, a1, Expr.eval, hr7]) (by omega)) (by omega),
              rfl, rfl, by simp [Expr.size]⟩
          have hu5 : Runs w p ω (.assign 16 (.bin .add (.load (.bin .add (.reg 16) (.const lsfOffWstrNumPtr)))
              (.bin .mul (.reg 14) (.reg 7)))) u4 .normal u5 9 :=
            runs_assign_iff.mpr ⟨numBase + e * x.L_w, by
              have hld : (Expr.load (.bin .add (.reg 16) (.const lsfOffWstrNumPtr))).eval w u4 = some numBase :=
                Expr.eval_load_of_eq (x := hWin + lsfOffWstrNumPtr)
                  (by simp [u4, u3, u2, u1, a2, a1, Expr.eval, BinOp.eval,
                    show lsfOffWstrNumPtr < 2 ^ w by dsimp only [lsfOffWstrNumPtr]; omega,
                    show hWin + lsfOffWstrNumPtr < 2 ^ w by dsimp only [lsfOffWstrNumPtr, lsfHdrSize] at hWin_hdr_le ⊢; omega])
                  ((hs_below _ (by dsimp only [lsfOffWstrNumPtr, lsfHdrSize] at hWin_hdr_le ⊢; omega)).trans
                    hWin_hdr.2.2.2.2.2.2.2.2.2.1)
              exact Expr.eval_add hld
                (Expr.eval_mul (by simp [u4, u3, u2, u1, a2, a1, Expr.eval])
                  (by simp [u4, u3, u2, u1, a2, a1, Expr.eval, hr7]) (by omega)) (by omega),
              rfl, rfl, by simp [Expr.size]⟩
          have hel : Runs w p ω _ a2 .normal u5 41 :=
            runs_seq_iff.mpr (Or.inr ⟨u1, 5, _, hu1, runs_seq_iff.mpr (Or.inr ⟨u2, 5, _, hu2,
              runs_seq_iff.mpr (Or.inr ⟨u3, 9, _, hu3, runs_seq_iff.mpr (Or.inr ⟨u4, 9, 9, hu4, hu5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
          have hu5_eq : u5 = { a2 with regs := Function.update (Function.update a2.regs 16 (numBase + e * x.L_w)) 17 (denBase + e * x.L_w) } := by
            dsimp only [u5, u4, u3, u2, u1]
            congr 1; funext r
            by_cases h16 : r = 16
            · subst h16; simp
            · by_cases h17 : r = 17
              · subst h17; simp
              · simp [h16, h17]
          have hN_v : Valid st.mem (numBase + e * x.L_w) W.h x.L_w := by rw [← hWin_h, ← hLwWin]; exact hWstr_e.2.1
          have hD_v : Valid st.mem (denBase + e * x.L_w) W.h x.L_w := by rw [← hWin_h, ← hLwWin]; exact hWstr_e.2.2.1
          have hN_pos : 1 ≤ intVal st.mem (numBase + e * x.L_w) W.h x.L_w := by rw [← hWin_h, ← hLwWin]; exact hWstr_e.2.2.2.1
          have hD_pos : 1 ≤ intVal st.mem (denBase + e * x.L_w) W.h x.L_w := by rw [← hWin_h, ← hLwWin]; exact hWstr_e.2.2.2.2.1
          have hRat : (intVal st.mem (numBase + e * x.L_w) W.h x.L_w : ℝ) /
              (intVal st.mem (denBase + e * x.L_w) W.h x.L_w : ℝ) = (S j).wstrGlobal e := by
            rw [hwstr_eq, ← hWin_h, ← hLwWin]; exact hWstr_e.2.2.2.2.2
          exact ⟨numBase + e * x.L_w, denBase + e * x.L_w, 43,
            runs_cond_iff.mpr ⟨0, 41, by simp [a2, Expr.eval, hins0], by simpa [hu5_eq] using hel, by simp [Expr.size]⟩,
            hnum_end, hden_end, hN_v, hD_v, hN_pos, hD_pos, hRat, by omega⟩
      obtain ⟨srcN, srcD, cS, ha3, hsrcN_end, hsrcD_end, hVN, hVD, hIN, hID, hRat, hcS⟩ := hsrc
      let a3 : State := { a2 with regs := Function.update (Function.update a2.regs 16 srcN) 17 srcD }
      let a4 : State := { a3 with regs := Function.update a3.regs 18 (numPtr + e * x.L_w) }
      let a5 : State := { a4 with regs := Function.update a4.regs 19 (denPtr + e * x.L_w) }
      let a6 : State := { a5 with regs := Function.update a5.regs 20 0 }
      have ha4 : Runs w p ω (.assign 18 (.bin .add (.reg 5) (.bin .mul (.reg 14) (.reg 7)))) a3 .normal a4 6 :=
        runs_assign_iff.mpr ⟨numPtr + e * x.L_w, by
          simp [a3, a2, a1, Expr.eval, BinOp.eval, hr_lt 5 (by omega), hr5, hr7,
            show e * x.L_w < 2 ^ w by omega, show numPtr + e * x.L_w < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have ha5 : Runs w p ω (.assign 19 (.bin .add (.reg 6) (.bin .mul (.reg 14) (.reg 7)))) a4 .normal a5 6 :=
        runs_assign_iff.mpr ⟨denPtr + e * x.L_w, by
          simp [a4, a3, a2, a1, Expr.eval, BinOp.eval, hr_lt 6 (by omega), hr6, hr7,
            show e * x.L_w < 2 ^ w by omega, show denPtr + e * x.L_w < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have ha6 : Runs w p ω (.assign 20 (.const 0)) a5 .normal a6 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨a7, cCp, ha7, ha7_r, ha7_cp, ha7_fr, hcCp⟩ :=
        compExpPairCopy_runs (L := x.L_w) (srcN := srcN) (srcD := srcD)
          (dstN := numPtr + e * x.L_w) (dstD := denPtr + e * x.L_w)
          (p := p) (ω := ω) (st := a6) hw16 (by omega) (by omega) (by omega) (by omega)
          (by simp [a6, a5, a4, a3, a2, a1, hr7]) (by simp [a6, a5, a4, a3]) (by simp [a6, a5, a4, a3])
          (by simp [a6, a5, a4]) (by simp [a6, a5]) (by simp [a6])
      let a8 : State := { a7 with regs := Function.update a7.regs 13 (i + 1) }
      have ha8 : Runs w p ω (.assign 13 (.bin .add (.reg 13) (.const 1))) a7 .normal a8 4 :=
        runs_assign_iff.mpr ⟨i + 1, by
          have hr13_7 : a7.regs 13 = i := by rw [ha7_r 13 (by omega)]; simp [a6, a5, a4, a3, a2, a1, hr13]
          simp [Expr.eval, BinOp.eval, hr13_7, hw1, show i + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal a8 (35 + cS + cCp) :=
        runs_seq_iff.mpr (Or.inr ⟨a1, 5, _, ha1, runs_seq_iff.mpr (Or.inr ⟨a2, 5, _, ha2,
          runs_seq_iff.mpr (Or.inr ⟨a3, cS, _, ha3, runs_seq_iff.mpr (Or.inr ⟨a4, 6, _, ha4,
          runs_seq_iff.mpr (Or.inr ⟨a5, 6, _, ha5, runs_seq_iff.mpr (Or.inr ⟨a6, 2, _, ha6,
          runs_seq_iff.mpr (Or.inr ⟨a7, cCp, 4, ha7, ha8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
      have hcp_e : ∀ t < x.L_w,
          a8.mem (numPtr + e * x.L_w + t) = st.mem (srcN + t) ∧
          a8.mem (denPtr + e * x.L_w + t) = st.mem (srcD + t) := fun t ht => by
        have ⟨hN, hD⟩ := ha7_cp t ht
        exact ⟨hN.trans (hs_below _ (by omega)), hD.trans (hs_below _ (by omega))⟩
      obtain ⟨st', cRest, hrest, hr'_lt, hdone', hfr', hfrE', hcRest⟩ :=
        ih (i + 1) a8 (by omega) (by omega)
          (fun r hr => by rw [show a8.regs r = a7.regs r by simp [a8, show r ≠ 13 by omega], ha7_r r (by omega)]
                          simp [a6, a5, a4, a3, a2, a1, show r ≠ 14 by omega, show r ≠ 15 by omega,
                            show r ≠ 16 by omega, show r ≠ 17 by omega, show r ≠ 18 by omega,
                            show r ≠ 19 by omega, show r ≠ 20 by omega, hr_lt r hr])
          (by rw [show a8.regs 7 = a7.regs 7 by simp [a8], ha7_r 7 (by omega)]; simp [a6, a5, a4, a3, a2, a1, hr7])
          (by rw [show a8.regs 8 = a7.regs 8 by simp [a8], ha7_r 8 (by omega)]; simp [a6, a5, a4, a3, a2, a1, hr8])
          (by rw [show a8.regs 9 = a7.regs 9 by simp [a8], ha7_r 9 (by omega)]; simp [a6, a5, a4, a3, a2, a1, hr9])
          (by rw [show a8.regs 10 = a7.regs 10 by simp [a8], ha7_r 10 (by omega)]; simp [a6, a5, a4, a3, a2, a1, hr10])
          (by rw [show a8.regs 11 = a7.regs 11 by simp [a8], ha7_r 11 (by omega)]; simp [a6, a5, a4, a3, a2, a1, hr11])
          (by rw [show a8.regs 12 = a7.regs 12 by simp [a8], ha7_r 12 (by omega)]; simp [a6, a5, a4, a3, a2, a1, hr12])
          (by simp [a8])
          (fun q hq => by
            by_cases hqi : q = i
            · subst hqi
              have hN_c : intVal a8.mem (numPtr + e * x.L_w) W.h x.L_w = intVal st.mem srcN W.h x.L_w :=
                intVal_congr fun t ht => (hcp_e t ht).1
              have hD_c : intVal a8.mem (denPtr + e * x.L_w) W.h x.L_w = intVal st.mem srcD W.h x.L_w :=
                intVal_congr fun t ht => (hcp_e t ht).2
              exact ⟨fun t ht => (hcp_e t ht).1 ▸ hVN t ht, fun t ht => (hcp_e t ht).2 ▸ hVD t ht,
                hN_c ▸ hIN, hD_c ▸ hID, by rw [hN_c, hD_c]; exact hRat⟩
            · have hqlt : q < i := by omega
              set eq_e := eL[q]'(by omega)
              have hne_e : eq_e ≠ e := fun h => hqi ((List.Nodup.getElem_inj_iff heL_nd).mp h)
              have hdisj_e : ∀ t < x.L_w,
                  (numPtr + eq_e * x.L_w + t < numPtr + e * x.L_w ∨ numPtr + e * x.L_w + x.L_w ≤ numPtr + eq_e * x.L_w + t) ∧
                  (numPtr + eq_e * x.L_w + t < denPtr + e * x.L_w ∨ denPtr + e * x.L_w + x.L_w ≤ numPtr + eq_e * x.L_w + t) ∧
                  (denPtr + eq_e * x.L_w + t < numPtr + e * x.L_w ∨ numPtr + e * x.L_w + x.L_w ≤ denPtr + eq_e * x.L_w + t) ∧
                  (denPtr + eq_e * x.L_w + t < denPtr + e * x.L_w ∨ denPtr + e * x.L_w + x.L_w ≤ denPtr + eq_e * x.L_w + t) := by
                intro t ht
                have heq_lt : eq_e < x.eCap := hT.hElt eq_e (hG_j ▸ (heL_mem eq_e).mp (List.getElem_mem _))
                have heq_Lw : eq_e * x.L_w + x.L_w ≤ x.eCap * x.L_w := by
                  have : (eq_e + 1) * x.L_w ≤ x.eCap * x.L_w := Nat.mul_le_mul_right _ heq_lt; linarith
                have hsep : eq_e * x.L_w + x.L_w ≤ e * x.L_w ∨ e * x.L_w + x.L_w ≤ eq_e * x.L_w := by
                  rcases Nat.lt_or_gt_of_ne hne_e with hlt' | hgt'
                  · left; have : (eq_e + 1) * x.L_w ≤ e * x.L_w := Nat.mul_le_mul_right _ hlt'; linarith
                  · right; have : (e + 1) * x.L_w ≤ eq_e * x.L_w := Nat.mul_le_mul_right _ hgt'; linarith
                refine ⟨by rcases hsep with h | h <;> omega, Or.inl (by omega), Or.inr (by omega),
                  by rcases hsep with h | h <;> omega⟩
              have hN_ag : ∀ t < x.L_w, a8.mem (numPtr + eq_e * x.L_w + t) = s.mem (numPtr + eq_e * x.L_w + t) :=
                fun t ht => ha7_fr _ (hdisj_e t ht).1 (hdisj_e t ht).2.1
              have hD_ag : ∀ t < x.L_w, a8.mem (denPtr + eq_e * x.L_w + t) = s.mem (denPtr + eq_e * x.L_w + t) :=
                fun t ht => ha7_fr _ (hdisj_e t ht).2.2.1 (hdisj_e t ht).2.2.2
              have hprev := hdone q hqlt
              have hN_c : intVal a8.mem (numPtr + eq_e * x.L_w) W.h x.L_w = intVal s.mem (numPtr + eq_e * x.L_w) W.h x.L_w :=
                intVal_congr hN_ag
              have hD_c : intVal a8.mem (denPtr + eq_e * x.L_w) W.h x.L_w = intVal s.mem (denPtr + eq_e * x.L_w) W.h x.L_w :=
                intVal_congr hD_ag
              exact ⟨fun t ht => hN_ag t ht ▸ hprev.1 t ht, fun t ht => hD_ag t ht ▸ hprev.2.1 t ht,
                hN_c ▸ hprev.2.2.1, hD_c ▸ hprev.2.2.2.1, by rw [hN_c, hD_c]; exact hprev.2.2.2.2⟩)
          (fun a haN haD => by
            refine (ha7_fr a ?_ ?_).trans (hfr a haN haD)
            · rcases haN with h | h
              · exact Or.inl (by omega)
              · exact Or.inr (by linarith [heLw_le])
            · rcases haD with h | h
              · exact Or.inl (by omega)
              · exact Or.inr (by linarith [heLw_le]))
          (fun a haE => (ha7_fr a (haE e heG_j).1 (haE e heG_j).2).trans (hfrE a haE))
      have hfull : Runs w p ω loopStmt s .normal st' (35 + cS + cCp + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, a8, 35 + cS + cCp, cRest,
          by simp [Expr.eval, BinOp.eval, hr13, hr_lt 4 (by omega), hr4, show i < (S j).G.m by omega, hw0], by decide,
          by simpa using hbody, hrest, by simp [Expr.size]; omega⟩))
      refine ⟨st', 35 + cS + cCp + cRest + 4, hfull, hr'_lt, hdone', hfr', hfrE', ?_⟩
      have hmul : 35 * (rem + 1) * x.L_w = 35 * rem * x.L_w + 35 * x.L_w := by ring
      omega
  obtain ⟨st', cL, hrunL, hr'_lt, hdone', hfr', hfrE', hcL⟩ :=
    hloop eL.length 0 s7 (Nat.zero_le _) (Nat.sub_zero _)
      (fun r hr => by simp [s7, s6, s5, s4, s3, s2, s1, show r ≠ 7 by omega, show r ≠ 8 by omega,
        show r ≠ 9 by omega, show r ≠ 10 by omega, show r ≠ 11 by omega, show r ≠ 12 by omega, show r ≠ 13 by omega])
      (by simp [s7, s6, s5, s4, s3, s2, s1]) (by simp [s7, s6, s5, s4, s3, s2])
      (by simp [s7, s6, s5, s4, s3]) (by simp [s7, s6, s5, s4])
      (by simp [s7, s6, s5]) (by simp [s7, s6]) (by simp [s7])
      (fun _ h => by omega) (fun _ _ _ => rfl) (fun _ _ => rfl)
  have hrun : Runs w p ω compExpPairsStmt st .normal st' (39 + cL) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, 33 + cL, hp1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 27 + cL, hp2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, 21 + cL, hp3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, 15 + cL, hp4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, 9 + cL, hp5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, 3 + cL, hp6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 2, cL, hp7, hrunL, by omega⟩),
      by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  have hcL' : cL ≤ 35 * (S j).G.m * x.L_w + 95 * (S j).G.m + 4 := by
    simpa only [heL_len] using hcL
  refine ⟨st', 39 + cL, hrun, hr'_lt, fun e he => ?_, hfr', hfrE', by omega⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp ((heL_mem e).mpr he)
  exact hdone' q hq

end

end MinCostFlow.SparseCore.Program
