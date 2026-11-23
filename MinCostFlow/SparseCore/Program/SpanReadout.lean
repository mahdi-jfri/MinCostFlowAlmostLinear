module

public import MinCostFlow.DynSpanner.Program.DynSpannerDS
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# Bucket Spanner Readout Procedures (`SpanReadout`)

Deterministic, zero-allocation, memory-preserving Word-RAM procedures that read out the current
bundle graph `G`, the current spanner graph `H`, and the total embedding walk `piTotal st e` from
any `dynSpannerDS P` handle `b` satisfying `DSRepAt P b s x mem`:

* `spanGPtrStmt` (`[b]`): returns `dsGPtr b` with `DynGraphAt mem ret P.vCap P.eCap (s.state P).G`,
  in at most `10` steps.
* `spanHPtrStmt` (`[b]`): returns `dsHPtr b P.vCap P.eCap` with
  `DynGraphAt mem ret P.vCap P.eCap (s.state P).H`, in at most `35` steps.
* `spanPiWalkPtrStmt` (`[b, e]`): scans levels `0..L` to compute
  `m = findEmbLevel (s.state P).inDom (P.L + 1) e` and returns the pointer
  `mem (dsPiPtrBase b P.L P.vCap P.eCap + m * P.eCap + e)`, satisfying
  `MWalkAt mem ret (piTotal (s.state P) e)` and `RangeInHeapFoot x ret ...`, in at most
  `65 * (P.L + 1) + 120` steps.
* `spanReadoutProcs`: relocatable 3-procedure bundle.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Procedure definitions and contracts -/

@[expose] public section

def spanReadIdxGPtr : ℕ := 0
def spanReadIdxHPtr : ℕ := 1
def spanReadIdxPiWalkPtr : ℕ := 2

/-- `args = [b]`: returns `dsGPtr b = b + dsHdrSize`. -/
def spanGPtrStmt : Stmt :=
  .ret (.bin .add (.reg 0) (.const dsHdrSize))

/-- `args = [b]`: returns `dsHPtr b vCap eCap = b + dsHdrSize + dynGraphSize vCap eCap`. -/
def spanHPtrStmt : Stmt :=
  .assign 1 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .ret (.bin .add (.bin .add (.reg 0) (.const dsHdrSize))
    (.bin .add (.const 4)
      (.bin .add (.bin .mul (.const 7) (.reg 1)) (.bin .mul (.const 9) (.reg 2)))))

/-- `args = [b, e]`: returns the walk pointer for `piTotal st e` in `DynSpannerStateAt` at `b`. -/
def spanPiWalkPtrStmt : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 5 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 6 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4)))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 6))) ;;
  .assign 7 (.bin .add (.reg 7)
    (.bin .add (.bin .mul (.const 3) (.reg 4)) (.bin .mul (.const 2) (.reg 5)))) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 5)) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .mul (.reg 5) (.reg 4))) ;;
  .assign 10 (.const 0) ;;
  forRange 11 (.const 0) (.reg 5)
    (.assign 12 (.load (.bin .add (.reg 7) (.reg 11))) ;;
     .cond (.reg 12)
       (.cond (.bin .eq
           (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.reg 11) (.reg 4))) (.reg 1)))
           (.reg 12))
         (.assign 10 (.reg 11))
         .nop)
       .nop) ;;
  .ret (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.reg 10) (.reg 4))) (.reg 1)))

/-- Relocatable readout procedure bundle (`3` deterministic procedures). -/
def spanReadoutProcs : List Stmt :=
  [spanGPtrStmt, spanHPtrStmt, spanPiWalkPtrStmt]

lemma spanReadoutProcs_length : spanReadoutProcs.length = 3 := rfl

lemma spanReadoutProcs_noRand : ∀ s ∈ spanReadoutProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `spanGPtrStmt` (`[b]`): returns `dsGPtr b` with `DynGraphAt` for `(s.state P).G`. -/
def spanGPtrContract (P : DSParams) (b : ℕ) (s : DSHist) (x : DynSpannerMeta P.L) : Contract where
  pre args mem :=
    args = [b] ∧ 16 ≤ 2 ^ P.w ∧ DSRepAt P b s x mem ∧
    b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w
  post _ mem ret mem' :=
    mem' = mem ∧ ret = dsGPtr b ∧ DynGraphAt mem' ret P.vCap P.eCap (s.state P).G
  cost _ _ := 10

/-- Contract of `spanHPtrStmt` (`[b]`): returns `dsHPtr b P.vCap P.eCap` with `DynGraphAt` for
`(s.state P).H`. -/
def spanHPtrContract (P : DSParams) (b : ℕ) (s : DSHist) (x : DynSpannerMeta P.L) : Contract where
  pre args mem :=
    args = [b] ∧ 16 ≤ 2 ^ P.w ∧ DSRepAt P b s x mem ∧
    b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w
  post _ mem ret mem' :=
    mem' = mem ∧ ret = dsHPtr b P.vCap P.eCap ∧ DynGraphAt mem' ret P.vCap P.eCap (s.state P).H
  cost _ _ := 35

/-- Cost bound of `spanPiWalkPtrStmt`: `65 * (L + 1) + 120`. -/
def spanPiWalkPtrCost (L : ℕ) : ℕ := 65 * (L + 1) + 120

/-- Contract of `spanPiWalkPtrStmt` (`[b, e]`): for any edge `e ∈ (s.state P).G.E`, returns the
pointer to `MWalkAt mem ret (piTotal (s.state P) e)` inside `heapFoot x`, preserving memory. -/
def spanPiWalkPtrContract (P : DSParams) (b e : ℕ) (s : DSHist) (x : DynSpannerMeta P.L) :
    Contract where
  pre args mem :=
    args = [b, e] ∧ 16 ≤ 2 ^ P.w ∧ DSRepAt P b s x mem ∧
    e ∈ (s.state P).G.E ∧ b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w ∧
    (∀ a, heapFoot x a → a < 2 ^ P.w)
  post _ mem ret mem' :=
    mem' = mem ∧
    MWalkAt mem' ret (piTotal (s.state P) e) ∧
    RangeInHeapFoot x ret (ret + (mWalkEncode (piTotal (s.state P) e)).length)
  cost _ _ := spanPiWalkPtrCost P.L

end

/-! ## Private helpers for `findEmbLevel` and layout word bounds -/

private lemma findEmbLevel_zero {L : ℕ} (inDom : Fin (L + 1) → Finset ℕ) (e : ℕ) :
    findEmbLevel inDom 0 e = 0 := by
  simp [findEmbLevel]

private lemma findEmbLevel_succ {L : ℕ} (inDom : Fin (L + 1) → Finset ℕ) (e : ℕ)
    {k : ℕ} (hk : k < L + 1) :
    findEmbLevel inDom (k + 1) e =
      if e ∈ inDom ⟨k, hk⟩ then k else findEmbLevel inDom k e := by
  unfold findEmbLevel
  have hmin1 : min (k + 1) (L + 1) = k + 1 := Nat.min_eq_left (by omega)
  have hmin0 : min k (L + 1) = k := Nat.min_eq_left (by omega)
  rw [hmin1, hmin0, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.find?_cons]
  simp only [hk, ↓reduceDIte]
  by_cases hmem : e ∈ inDom ⟨k, hk⟩
  · simp [hmem]
  · simp [hmem]

private lemma findEmbLevel_mem {L : ℕ} (inDom : Fin (L + 1) → Finset ℕ) (e : ℕ)
    (h0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩) :
    ∀ k, 1 ≤ k → k ≤ L + 1 →
      ∃ hk : findEmbLevel inDom k e < L + 1, e ∈ inDom ⟨findEmbLevel inDom k e, hk⟩ := by
  intro k hk1 hkL
  induction k with
  | zero => omega
  | succ m ih =>
    have hmL : m < L + 1 := by omega
    rw [findEmbLevel_succ inDom e hmL]
    by_cases hm : e ∈ inDom ⟨m, hmL⟩
    · rw [ite_eq_left hm]
      exact ⟨hmL, hm⟩
    · rw [ite_eq_right hm]
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact absurd h0 hm
      · exact ih hmpos (by omega)

private lemma readout_fixed_bounds {w b L vCap eCap : ℕ}
    (hfix : b + dsFixedSize L vCap eCap < 2 ^ w) :
    b + dsLOff < 2 ^ w ∧ b + dsVCapOff < 2 ^ w ∧ b + dsECapOff < 2 ^ w ∧
    L + 1 < 2 ^ w ∧ 7 * vCap < 2 ^ w ∧ 9 * eCap < 2 ^ w ∧ 7 * vCap + 9 * eCap < 2 ^ w ∧
    dynGraphSize vCap eCap < 2 ^ w ∧ 3 * dynGraphSize vCap eCap < 2 ^ w ∧
    dsGPtr b < 2 ^ w ∧ dsHPtr b vCap eCap < 2 ^ w ∧ dsMinHBase b vCap eCap < 2 ^ w ∧
    3 * eCap < 2 ^ w ∧ 2 * (L + 1) < 2 ^ w ∧ 3 * eCap + 2 * (L + 1) < 2 ^ w ∧
    dsDomGenBase b L vCap eCap < 2 ^ w ∧ dsEdgeDomGenBase b L vCap eCap < 2 ^ w ∧
    (L + 1) * eCap < 2 ^ w ∧ dsPiPtrBase b L vCap eCap < 2 ^ w := by
  have hfs : dsFixedSize L vCap eCap =
      dsHdrSize + 3 * dynGraphSize vCap eCap + 3 * eCap + 2 * (L + 1) +
      (L + 1) + 2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap) +
      (L + 1) + (L + 1) * vCap + (L + 1) + 2 * vCap + 3 * eCap := by
    simp only [dsFixedSize, dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase,
      dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
      dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase,
      dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]
    ring
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 : dsEdgeDomGenBase b L vCap eCap = dsDomGenBase b L vCap eCap + (L + 1) := rfl
  have h4 : dsPiPtrBase b L vCap eCap = dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap := rfl
  have h5 : dsGPtr b = b + dsHdrSize := rfl
  have h6 : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  simp only [dsLOff, dsVCapOff, dsECapOff, dsHdrSize] at hfs h1 h5 ⊢
  omega

private lemma runs_cond_true_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h : ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, hq, by omega⟩

private lemma runs_cond_false_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (h : ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨0, c, he, by simpa using hr, rfl⟩, hq, by omega⟩

private def PiScanInv (L vCap eCap b e : ℕ) (inDom : Fin (L + 1) → Finset ℕ) (mem0 : ℕ → ℕ)
    (k : ℕ) (st : State) : Prop :=
  st.mem = mem0 ∧
  st.regs 1 = e ∧ st.regs 4 = eCap ∧ st.regs 5 = L + 1 ∧
  st.regs 7 = dsDomGenBase b L vCap eCap ∧
  st.regs 8 = dsEdgeDomGenBase b L vCap eCap ∧
  st.regs 9 = dsPiPtrBase b L vCap eCap ∧
  st.regs 10 = findEmbLevel inDom k e ∧
  st.regs 11 = k

/-! ## Contract verification -/

public section

/-- `spanGPtrStmt` meets `spanGPtrContract`. -/
theorem spanGPtr_meetsContract {P : DSParams} {b : ℕ} {s : DSHist} {x : DynSpannerMeta P.L}
    {p : Program} {base : ℕ} (hp : p.HasAt base spanReadoutProcs) :
    MeetsContract P.w p (base + spanReadIdxGPtr) (spanGPtrContract P b s x) := by
  refine meetsContract_of_runs
    (hp.get (i := spanReadIdxGPtr) (by simp [spanReadoutProcs, spanReadIdxGPtr])) ?_
  rintro args mem pos ω _ ⟨rfl, hw16, hrep, hfix⟩
  simp only [spanReadoutProcs, spanReadIdxGPtr, List.getElem_cons_zero]
  have hB := readout_fixed_bounds hfix
  have hG : DynGraphAt mem (dsGPtr b) P.vCap P.eCap (s.state P).G :=
    hrep.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [spanGPtrStmt]
  refine runs_start_le ?_
  refine runs_ret_le (v := dsGPtr b)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by simp [dsHdrSize]; omega)) hB.2.2.2.2.2.2.2.2.2.1)
    ⟨rfl, rfl, hG⟩ ?_
  simp only [Expr.size, spanGPtrContract]
  omega

/-- `spanHPtrStmt` meets `spanHPtrContract`. -/
theorem spanHPtr_meetsContract {P : DSParams} {b : ℕ} {s : DSHist} {x : DynSpannerMeta P.L}
    {p : Program} {base : ℕ} (hp : p.HasAt base spanReadoutProcs) :
    MeetsContract P.w p (base + spanReadIdxHPtr) (spanHPtrContract P b s x) := by
  refine meetsContract_of_runs
    (hp.get (i := spanReadIdxHPtr) (by simp [spanReadoutProcs, spanReadIdxHPtr])) ?_
  rintro args mem pos ω _ ⟨rfl, hw16, hrep, hfix⟩
  simp only [spanReadoutProcs, spanReadIdxHPtr, List.getElem_cons_succ, List.getElem_cons_zero]
  have hB := readout_fixed_bounds hfix
  have hSt := hrep.2.2.2.2.2.2.2.1
  have hmV : mem (b + dsVCapOff) = P.vCap := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmE : mem (b + dsECapOff) = P.eCap := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hH : DynGraphAt mem (dsHPtr b P.vCap P.eCap) P.vCap P.eCap (s.state P).H :=
    hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdg : 4 + (7 * P.vCap + 9 * P.eCap) = dynGraphSize P.vCap P.eCap := by
    simp only [dynGraphSize]; omega
  dsimp only [spanHPtrStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := P.vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by simp [dsVCapOff]; omega)) hB.2.1) hmV) ?_
  refine runs_seq_assign_le (v := P.eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by simp [dsECapOff]; omega)) hB.2.2.1) hmE) ?_
  refine runs_ret_le (v := dsHPtr b P.vCap P.eCap)
    (by
      change _ = some ((b + dsHdrSize) + dynGraphSize P.vCap P.eCap)
      rw [← hdg]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_const (by simp [dsHdrSize]; omega)) hB.2.2.2.2.2.2.2.2.2.1)
        (Expr.eval_add (Expr.eval_const (by omega))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.1)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.2.1)
            hB.2.2.2.2.2.2.1)
          (by rw [hdg]; exact hB.2.2.2.2.2.2.2.1))
        (by rw [hdg]; exact hB.2.2.2.2.2.2.2.2.2.2.1))
    ⟨rfl, rfl, hH⟩ ?_
  simp only [Expr.size, spanHPtrContract]
  omega

/-- `spanPiWalkPtrStmt` meets `spanPiWalkPtrContract`. -/
theorem spanPiWalkPtr_meetsContract {P : DSParams} {b e : ℕ} {s : DSHist} {x : DynSpannerMeta P.L}
    {p : Program} {base : ℕ} (hp : p.HasAt base spanReadoutProcs) :
    MeetsContract P.w p (base + spanReadIdxPiWalkPtr) (spanPiWalkPtrContract P b e s x) := by
  refine meetsContract_of_runs
    (hp.get (i := spanReadIdxPiWalkPtr) (by simp [spanReadoutProcs, spanReadIdxPiWalkPtr])) ?_
  rintro args mem pos ω _ ⟨rfl, hw16, hrep, heG, hfix, hfootW⟩
  simp only [spanReadoutProcs, spanReadIdxPiWalkPtr, List.getElem_cons_succ, List.getElem_cons_zero]
  obtain ⟨hL1, hVG₀, hGm₀, _, hBVf, hdsf, _, hSt, _, _⟩ := hrep
  have hB := readout_fixed_bounds hfix
  have hlt := stepZero_fixed_lt b P.L P.vCap P.eCap
  have heCap : e < P.eCap := hSt.2.2.2.2.2.2.2.2.2.2.1 e heG
  have hmL : mem (b + dsLOff) = P.L := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmV : mem (b + dsVCapOff) = P.vCap := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmE : mem (b + dsECapOff) = P.eCap := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hInDom := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdg : 4 + (7 * P.vCap + 9 * P.eCap) = dynGraphSize P.vCap P.eCap := by
    simp only [dynGraphSize]; omega
  dsimp only [spanPiWalkPtrStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := P.L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by simp [dsLOff]; omega)) hB.1) hmL) ?_
  refine runs_seq_assign_le (v := P.vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by simp [dsVCapOff]; omega)) hB.2.1) hmV) ?_
  refine runs_seq_assign_le (v := P.eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by simp [dsECapOff]; omega)) hB.2.2.1) hmE) ?_
  refine runs_seq_assign_le (v := P.L + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hB.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dynGraphSize P.vCap P.eCap)
    (by
      rw [← hdg]
      exact Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.1)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.2.1)
          hB.2.2.2.2.2.2.1)
        (by rw [hdg]; exact hB.2.2.2.2.2.2.2.1)) ?_
  refine runs_seq_assign_le (v := dsMinHBase b P.vCap P.eCap)
    (by
      rw [dsMinHBase_eq]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_const (by simp [dsHdrSize]; omega)) hB.2.2.2.2.2.2.2.2.2.1)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
          hB.2.2.2.2.2.2.2.2.1)
        (by rw [← dsMinHBase_eq]; exact hB.2.2.2.2.2.2.2.2.2.2.2.1)) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b P.L P.vCap P.eCap)
    (by
      rw [dsDomGenBase_eq]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
            hB.2.2.2.2.2.2.2.2.2.2.2.2.1)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
            hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
          hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (by rw [← dsDomGenBase_eq]; exact hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)) ?_
  refine runs_seq_assign_le (v := dsEdgeDomGenBase b P.L P.vCap P.eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsPiPtrBase b P.L P.vCap P.eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hloop : Triple P.w p
      (fun st => PiScanInv P.L P.vCap P.eCap b e (s.state P).inDom mem 0
        { st with regs := Function.update st.regs 11 0 })
      (forRange 11 (.const 0) (.reg 5)
        (.assign 12 (.load (.bin .add (.reg 7) (.reg 11))) ;;
         .cond (.reg 12)
           (.cond (.bin .eq
               (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.reg 11) (.reg 4))) (.reg 1)))
               (.reg 12))
             (.assign 10 (.reg 11)) .nop)
           .nop))
      (normalPost (PiScanInv P.L P.vCap P.eCap b e (s.state P).inDom mem (P.L + 1)))
      (fun _ => (P.L + 1) * (40 + (Expr.reg 5).size + 8) +
        ((Expr.const 0).size + (Expr.reg 5).size + 5)) := by
    refine Triple.forRange_const (Inv := PiScanInv P.L P.vCap P.eCap b e (s.state P).inDom mem)
      40 0 (P.L + 1) (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => ⟨Expr.eval_const (by omega), hst⟩)
      (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2)
      (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
      (fun i _ hiL => ?_)
    intro st ω' hI
    obtain ⟨hm, hr1, hr4, hr5, hr7, hr8, hr9, hr10, hr11⟩ := hI
    have hiDomW : dsDomGenBase b P.L P.vCap P.eCap + i < 2 ^ P.w :=
      lt_trans (hlt.2.2.2.2.2.2.2.2.2.1 i hiL).2 hfix
    have hiEdgeW : dsEdgeDomGenBase b P.L P.vCap P.eCap + i * P.eCap + e < 2 ^ P.w :=
      lt_trans (hlt.2.2.2.2.2.2.2.2.2.2.1 i hiL e heCap).2 hfix
    have hiMulW : i * P.eCap < 2 ^ P.w := by omega
    have hiAddW : dsEdgeDomGenBase b P.L P.vCap P.eCap + i * P.eCap < 2 ^ P.w := by omega
    have hiff : (0 < mem (dsDomGenBase b P.L P.vCap P.eCap + i) ∧
        mem (dsEdgeDomGenBase b P.L P.vCap P.eCap + i * P.eCap + e) =
          mem (dsDomGenBase b P.L P.vCap P.eCap + i)) ↔
        e ∈ (s.state P).inDom ⟨i, hiL⟩ := by
      have h1 := ((hInDom ⟨i, hiL⟩).2.1 e heCap).2
      have h2 := (hInDom ⟨i, hiL⟩).2.2.2.1
      rw [h1, h2]
      simp [heG]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := mem (dsDomGenBase b P.L P.vCap P.eCap + i))
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hr7) (Expr.eval_reg_of_eq hr11) hiDomW)
        (by rw [hm])) ?_
    by_cases hdg0 : mem (dsDomGenBase b P.L P.vCap P.eCap + i) = 0
    · refine runs_cond_false_le (Expr.eval_reg_of_eq (by simp [hdg0])) ?_
      refine runs_nop_le ?_ (by simp [Expr.size])
      have hnot : e ∉ (s.state P).inDom ⟨i, hiL⟩ := by
        rw [← hiff]; omega
      refine ⟨⟨hm, by simp [hr1], by simp [hr4], by simp [hr5], by simp [hr7], by simp [hr8],
        by simp [hr9], ?_, by simp⟩, by simp [hr11]⟩
      simp [hr10, findEmbLevel_succ _ _ hiL, hnot]
    · refine runs_cond_true_le (v := mem (dsDomGenBase b P.L P.vCap P.eCap + i))
        (Expr.eval_reg_of_eq (by simp)) hdg0 ?_
      by_cases heq : mem (dsEdgeDomGenBase b P.L P.vCap P.eCap + i * P.eCap + e) =
          mem (dsDomGenBase b P.L P.vCap P.eCap + i)
      · refine runs_cond_true_le (v := 1)
          (Expr.eval_eq_true
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr8]))
                  (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [hr11]))
                    (Expr.eval_reg_of_eq (by simp [hr4])) hiMulW) hiAddW)
                (Expr.eval_reg_of_eq (by simp [hr1])) hiEdgeW)
              (by rw [hm]))
            (Expr.eval_reg_of_eq (by simp)) heq (by omega)) (by decide) ?_
        refine runs_assign_le (v := i) (Expr.eval_reg_of_eq (by simp [hr11])) ?_
          (by simp [Expr.size])
        have hmem : e ∈ (s.state P).inDom ⟨i, hiL⟩ := hiff.mp ⟨Nat.pos_of_ne_zero hdg0, heq⟩
        refine ⟨⟨hm, by simp [hr1], by simp [hr4], by simp [hr5], by simp [hr7], by simp [hr8],
          by simp [hr9], ?_, by simp⟩, by simp [hr11]⟩
        simp [findEmbLevel_succ _ _ hiL, hmem]
      · refine runs_cond_false_le
          (Expr.eval_eq_false
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr8]))
                  (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [hr11]))
                    (Expr.eval_reg_of_eq (by simp [hr4])) hiMulW) hiAddW)
                (Expr.eval_reg_of_eq (by simp [hr1])) hiEdgeW)
              (by rw [hm]))
            (Expr.eval_reg_of_eq (by simp)) heq (by omega)) ?_
        refine runs_nop_le ?_ (by simp [Expr.size])
        have hnot : e ∉ (s.state P).inDom ⟨i, hiL⟩ := by
          rw [← hiff]; intro hc; exact heq hc.2
        refine ⟨⟨hm, by simp [hr1], by simp [hr4], by simp [hr5], by simp [hr7], by simp [hr8],
          by simp [hr9], ?_, by simp⟩, by simp [hr11]⟩
        simp [hr10, findEmbLevel_succ _ _ hiL, hnot]
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨rfl, by simp [startState], by simp, by simp, by simp, by simp, by simp,
      by simp [findEmbLevel_zero], by simp⟩
  · intro st₁ ⟨hm₁, hr1, hr4, _, _, _, hr9, hr10, _⟩
    have hq1 : 1 ≤ s.q P := le_trans (by decide) (two_le_phaseBase _ _)
    have hSnap := snapInv_of_history P hVG₀ hL1 hq1 hGm₀ hBVf hdsf s.flat.length le_rfl
    have he0 : e ∈ (s.state P).inDom ⟨0, Nat.zero_lt_succ P.L⟩ := by
      have h0 := hSnap.inDom0
      have hG := hSnap.G_eq
      change (s.state P).inDom ⟨0, Nat.zero_lt_succ P.L⟩ = _ at h0
      change (s.state P).G = _ at hG
      rw [h0, ← hG]
      exact heG
    obtain ⟨hmL, hmDom⟩ := findEmbLevel_mem (s.state P).inDom e he0 (P.L + 1) (by omega) le_rfl
    set m := findEmbLevel (s.state P).inDom (P.L + 1) e
    have hpiEq : piTotal (s.state P) e = (s.state P).Pi_level ⟨m, hmL⟩ e := by
      simp only [piTotal, piLe, piLt, piLtFrom, m, hmL, ↓reduceDIte]
    have hWalk := (hInDom ⟨m, hmL⟩).2.2.2.2.1 e hmDom
    dsimp only at hWalk
    rw [← hpiEq] at hWalk
    have hPiW : dsPiPtrBase b P.L P.vCap P.eCap + m * P.eCap + e < 2 ^ P.w :=
      lt_trans (hlt.2.2.2.2.2.2.2.2.2.2.2.1 m hmL e heCap).2 hfix
    have hMulW : m * P.eCap < 2 ^ P.w := by omega
    have hAddW : dsPiPtrBase b P.L P.vCap P.eCap + m * P.eCap < 2 ^ P.w := by omega
    refine runs_ret_le (v := mem (dsPiPtrBase b P.L P.vCap P.eCap + m * P.eCap + e))
      (Expr.eval_load_of_eq
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq hr9)
            (Expr.eval_mul (Expr.eval_reg_of_eq hr10) (Expr.eval_reg_of_eq hr4) hMulW) hAddW)
          (Expr.eval_reg_of_eq hr1) hPiW)
        (by rw [hm₁]))
      ⟨hm₁, hm₁.symm ▸ hWalk.1, hWalk.2⟩ ?_
    simp only [Expr.size, spanPiWalkPtrContract, spanPiWalkPtrCost]
    omega

end

end MinCostFlow.SparseCore.Program
