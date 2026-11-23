module

public import MinCostFlow.DynSpanner.Program.DynSpannerApplyU
public import MinCostFlow.DynSpanner.Program.DynSpannerRestrictRec
import WordRAM.Tactic

/-!
# The first part of a step: the update itself

A step of Algorithm 6 starts with the update `u`. Before `u` is applied, the step writes the
first records of `U_H`, namely `restrictUpdate u H`, because these records are defined from `H`
before the update (`dsRestrictRecStmt`, which reads the presence array of `E(H)`). Then it
applies `u` to `G`, `H` and the buckets of the levels (`dsApplyUStmt`).

`dsStepPrefixStmt` makes these two calls. `dsStepPrefix_meetsContract` proves its contract, with
cost `1320 · len + 600` for an update record of `len` words. The output records go to a buffer
`out` above the fixed block of the state, so the second call does not touch them.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [gPtr, hPtr, b, minHBase, updPtr, presH, out]`; returns the number of words of the
records of `restrictUpdate u H`. -/
def dsStepPrefixStmt (bR bU : ℕ) : Stmt :=
  .call 7 (bR + restrictRecIdx) [.reg 4, .reg 5, .reg 6] ;;
  .call 8 (bU + applyUIdx) [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .ret (.reg 7)

def stepPrefixProcs (bR bU : ℕ) : List Stmt := [dsStepPrefixStmt bR bU]

def stepPrefixIdx : ℕ := 0

lemma stepPrefixProcs_noRand (bR bU : ℕ) : ∀ s ∈ stepPrefixProcs bR bU, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsStepPrefixStmt`. -/
def dsStepPrefixContract (w L vCap eCap b : ℕ) (G H : MGraph) (u : Update) (len : ℕ)
    (B : ℕ → List ℕ) (out : ℕ) : Contract where
  pre args mem := ∃ updPtr,
    args = [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr,
      dgEPresBase (dsHPtr b vCap eCap) vCap, out] ∧
    (dsApplyUContract w L vCap eCap b G H u len B).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr] mem ∧
    out + len < 2 ^ w ∧ IvlDisj out len updPtr len ∧ b + dsFixedSize L vCap eCap ≤ out
  post _ mem ret mem' :=
    ret ≤ len ∧ BatchBodyAt mem' out H (restrictUpdate u H) ret ∧
    DynGraphAt mem' (dsGPtr b) vCap eCap (G.applyUpdate u) ∧
    DynGraphAt mem' (dsHPtr b vCap eCap) vCap eCap (H.applyBatch (restrictUpdate u H)) ∧
    BucketsAt mem' L vCap eCap b (fun i => delErase u (B i)) ∧
    (∀ e' < eCap, mem' (dsMinHBase b vCap eCap + e') =
      minHAfter u (mem (dsMinHBase b vCap eCap + e')) e') ∧
    ∀ addr, (addr < out ∨ out + len ≤ addr) →
      (addr < dsGPtr b ∨
        (dsAuxPtr b vCap eCap ≤ addr ∧ addr < dsMinHBase b vCap eCap) ∨
        dsDomGenBase b L vCap eCap ≤ addr) → mem' addr = mem addr
  cost _ _ := 1320 * len + 600

end

private lemma domGen_le'' (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
    dsEdgeDomGenBase]
  omega

public section

/-- The precondition of `dsApplyUStmt` only reads the fixed block of the state and the update
record, so it survives any change of memory outside these. -/
theorem dsApplyUContract_pre_of_agree {w L vCap eCap b : ℕ} {G H : MGraph} {u : Update}
    {len : ℕ} {B : ℕ → List ℕ} {updPtr : ℕ} {mem mem₁ : ℕ → ℕ}
    (h : (dsApplyUContract w L vCap eCap b G H u len B).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr] mem)
    (hag : ∀ addr, (addr < b + dsFixedSize L vCap eCap ∨
      (updPtr ≤ addr ∧ addr < updPtr + len)) → mem₁ addr = mem addr) :
    (dsApplyUContract w L vCap eCap b G H u len B).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr] mem₁ := by
  obtain ⟨updPtr', hargs, hw16, hbound, hubound, hudisj, huwords, hu_at, hvalid, hcaps, hds,
    heC, hG, hH, hsub, hHV, hL, hvC, heCw, hB, hdisj, hzero, hsome⟩ := h
  simp only [List.cons.injEq, and_true, true_and] at hargs
  subst hargs
  have hdom := domGen_le'' b L vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hHp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hAp : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hMp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hGp : dsGPtr b = b + dsHdrSize := rfl
  have hn : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hp : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hh : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hd : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hfix : ∀ addr, addr < b + dsFixedSize L vCap eCap → mem₁ addr = mem addr :=
    fun addr ha => hag addr (Or.inl ha)
  have hhdr : ∀ k < dsHdrSize, mem₁ (b + k) = mem (b + k) := fun k hk =>
    hfix _ (by simp only [dsHdrSize] at hk hGp; omega)
  refine ⟨updPtr, rfl, hw16, hbound, hubound, hudisj, fun i hi => ?_,
    hu_at.of_agree fun i hi => hag _ (Or.inr ⟨by omega, by omega⟩), hvalid, hcaps, hds, heC,
    dynGraphAt_of_agree hG fun addr _ h2 => hfix addr (by omega),
    dynGraphAt_of_agree hH fun addr _ h2 => hfix addr (by omega), hsub, hHV,
    (hhdr dsLOff (by decide)).trans hL, (hhdr dsVCapOff (by decide)).trans hvC,
    (hhdr dsECapOff (by decide)).trans heCw, fun i hi => ?_, hdisj,
    fun e he h0 => hzero e he (by rw [← hfix _ (by omega)]; exact h0),
    fun e he i h1 => hsome e he i (by rw [← hfix _ (by omega)]; exact h1)⟩
  · rw [hag _ (Or.inr ⟨by omega, by omega⟩)]; exact huwords i hi
  · obtain ⟨hdll, hdeg⟩ := hB i hi
    refine ⟨hdll.of_agree (hfix _ (by omega)) (fun x hx => hfix _ (by
        have := hdll.2.1 x hx; omega)) (fun x hx => hfix _ (by have := hdll.2.1 x hx; omega)),
      ?_⟩
    rw [hfix _ (by omega)]
    exact hdeg

/-- A finer form of `dsApplyUContract_pre_of_agree`: the precondition only reads the cells below
`domGen` other than the generation word, and the update record. So it survives, for example,
`dsUpdateSLevelsStmt`, which writes the generation word, the `S` arrays and the heap. -/
theorem dsApplyUContract_pre_of_agree' {w L vCap eCap b : ℕ} {G H : MGraph} {u : Update}
    {len : ℕ} {B : ℕ → List ℕ} {updPtr : ℕ} {mem mem₁ : ℕ → ℕ}
    (h : (dsApplyUContract w L vCap eCap b G H u len B).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr] mem)
    (hag : ∀ addr, ((addr < dsDomGenBase b L vCap eCap ∧ addr ≠ b + dsGenOff) ∨
      (updPtr ≤ addr ∧ addr < updPtr + len)) → mem₁ addr = mem addr) :
    (dsApplyUContract w L vCap eCap b G H u len B).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr] mem₁ := by
  obtain ⟨updPtr', hargs, hw16, hbound, hubound, hudisj, huwords, hu_at, hvalid, hcaps, hds,
    heC, hG, hH, hsub, hHV, hL, hvC, heCw, hB, hdisj, hzero, hsome⟩ := h
  simp only [List.cons.injEq, and_true, true_and] at hargs
  subst hargs
  have hdom := domGen_le'' b L vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hHp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hAp : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hMp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hGp : dsGPtr b = b + dsHdrSize := rfl
  have hn : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hp : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hh : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hd : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hfix : ∀ addr, b + dsHdrSize ≤ addr → addr < dsDomGenBase b L vCap eCap →
      mem₁ addr = mem addr :=
    fun addr h1 ha => hag addr (Or.inl ⟨ha, by simp only [dsGenOff, dsHdrSize] at h1 ⊢; omega⟩)
  have hhdr : ∀ k < dsGenOff, mem₁ (b + k) = mem (b + k) := fun k hk =>
    hag _ (Or.inl ⟨by simp only [dsGenOff, dsHdrSize] at hk hGp; omega, by omega⟩)
  refine ⟨updPtr, rfl, hw16, hbound, hubound, hudisj, fun i hi => ?_,
    hu_at.of_agree fun i hi => hag _ (Or.inr ⟨by omega, by omega⟩), hvalid, hcaps, hds, heC,
    dynGraphAt_of_agree hG fun addr h1 h2 => hfix addr (by omega) (by omega),
    dynGraphAt_of_agree hH fun addr h1 h2 => hfix addr (by omega) (by omega), hsub, hHV,
    (hhdr dsLOff (by decide)).trans hL, (hhdr dsVCapOff (by decide)).trans hvC,
    (hhdr dsECapOff (by decide)).trans heCw, fun i hi => ?_, hdisj,
    fun e he h0 => hzero e he (by rw [← hfix _ (by omega) (by omega)]; exact h0),
    fun e he i h1 => hsome e he i (by rw [← hfix _ (by omega) (by omega)]; exact h1)⟩
  · rw [hag _ (Or.inr ⟨by omega, by omega⟩)]; exact huwords i hi
  · obtain ⟨hdll, hdeg⟩ := hB i hi
    refine ⟨hdll.of_agree (hfix _ (by omega) (by omega)) (fun x hx => hfix _ (by omega) (by
        have := hdll.2.1 x hx; omega)) (fun x hx => hfix _ (by omega) (by
        have := hdll.2.1 x hx; omega)), ?_⟩
    rw [hfix _ (by omega) (by omega)]
    exact hdeg

/-- `dsStepPrefixStmt` meets `dsStepPrefixContract`. -/
theorem dsStepPrefix_meetsContract {w L vCap eCap b : ℕ} {G H : MGraph} {u : Update}
    {len : ℕ} {B : ℕ → List ℕ} {out : ℕ} {p : Program}
    {bS bR bF bU bD bPhase bOps bEdge bSplit bBatch : ℕ}
    (hpB : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpD : p.HasAt bD (levelsDeleteProcs bPhase))
    (hpU : p.HasAt bU (applyUProcs bBatch bD))
    (hpF : p.HasAt bF filterCopyProcs) (hpR : p.HasAt bR (restrictRecProcs bF))
    (hpS : p.HasAt bS (stepPrefixProcs bR bU)) :
    MeetsContract w p (bS + stepPrefixIdx)
      (dsStepPrefixContract w L vCap eCap b G H u len B out) := by
  refine meetsContract_of_runs
    (hpS.get (i := stepPrefixIdx) (by simp [stepPrefixProcs, stepPrefixIdx])) ?_
  rintro args mem pos ω hargsW ⟨updPtr, rfl, hpreU, hoB, dOU, hout⟩
  simp only [stepPrefixProcs, stepPrefixIdx, List.getElem_cons_zero]
  dsimp only [dsStepPrefixStmt]
  have hpreU' := hpreU
  obtain ⟨updPtr', hargs, hw16, hbound, hubound, hudisj, huwords, hu_at, hvalid, hcaps, hds,
    heC, hG, hH, hsub, hHV, hL, hvC, heCw, hB, hdisj, hzero, hsome⟩ := hpreU'
  simp only [List.cons.injEq, and_true, true_and] at hargs
  subst hargs
  have hdom := domGen_le'' b L vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hHp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hAp : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hMp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hEp : dgEPresBase (dsHPtr b vCap eCap) vCap = dsHPtr b vCap eCap + 4 + 7 * vCap := rfl
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hpres := hH.2.2.2.2.2.2.2.2.2.2.2.1
  refine runs_start_le ?_
  -- Call 1: the records of `restrictUpdate u H`.
  refine runs_seq_call_le (vs := [updPtr, dgEPresBase (dsHPtr b vCap eCap) vCap, out])
    (dsRestrictRec_meetsContract (w := w) (eCap := eCap) (G := G) (H := H) (u := u) (len := len)
      (updPtr := updPtr) (pres := dgEPresBase (dsHPtr b vCap eCap) vCap) (out := out) hpF hpR)
    (by eval_expr)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl) <;> omega)
    ⟨rfl, hw16, hubound, by omega, hoB, dOU, by unfold IvlDisj; omega, huwords, hu_at, hds,
      hvalid, heC, hsub, hpres⟩ ?_
  rintro r₇ mem₁ pos₁ ⟨hret, hBB, hfr₁⟩
  -- Call 2: apply `u`.
  have hpreU₁ := dsApplyUContract_pre_of_agree (mem₁ := mem₁) hpreU fun addr h => hfr₁ addr (by
    unfold IvlDisj at dOU
    omega)
  refine runs_seq_call_le (vs := [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr])
    (dsApplyU_meetsContract (w := w) (L := L) (vCap := vCap) (eCap := eCap) (b := b) (G := G)
      (H := H) (u := u) (len := len) (B := B) hpB hpEdge hpSplit hpOps hpP hpD hpU)
    (by eval_expr)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl|rfl|rfl) <;> omega)
    hpreU₁ ?_
  rintro r₈ mem₂ pos₂ ⟨hG₂, hH₂, hB₂, hmin₂, hfr₂⟩
  refine runs_ret_le (v := r₇) (Expr.eval_reg_of_eq (by simp))
    ⟨hret, hBB.of_agree fun i hi => hfr₂ _ (Or.inr (Or.inr (by omega))), hG₂, hH₂, hB₂,
      fun e' he' => ?_, fun addr h1 h2 => (hfr₂ addr h2).trans (hfr₁ addr h1)⟩ ?_
  · show mem₂ _ = _
    rw [hmin₂ e' he']
    have h1 : mem₁ (dsMinHBase b vCap eCap + e') = mem (dsMinHBase b vCap eCap + e') :=
      hfr₁ _ (Or.inl (by omega))
    exact congrArg (fun x => minHAfter u x e') h1
  · simp only [Expr.size, argsSize, dsStepPrefixContract, dsRestrictRecContract, dsApplyUContract]
    omega

end

end MinCostFlow.DynSpanner.Program
