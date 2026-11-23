module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepEnd
public import MinCostFlow.DynSpanner.Program.DynSpannerClearAbove
import WordRAM.Tactic

/-!
# The end of `step` with the empty levels

`dsStepTailStmt` calls `dsStepEndStmt` (the records of `U_H`, the new `H` and the new buckets) and
then `dsClearAboveStmt` with `domGen[i] := 0` for `i > j` and `sGen[i] := 0` for `i ≥ j`. The
generation words lie after the bucket region and away from the record buffer and `H`, so the facts
of the first call survive the second (`dsStepTail_meetsContract`). With `levels_above_clear` and
`levelSAt_clear` the zero words give the level clauses of the empty levels.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args` are the 22 arguments of `dsStepEndStmt` followed by
`[domGenBase, sGenBase, j + 1, j, L + 1]`; returns the number of records of `U_H`. -/
def dsStepTailStmt (bS bC : ℕ) : Stmt :=
  .call 27 (bS + stepEndIdx)
    [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
      .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 17, .reg 18, .reg 19, .reg 20,
      .reg 21] ;;
  .call 28 (bC + clearAboveIdx) [.reg 22, .reg 23, .reg 24, .reg 25, .reg 26] ;;
  .ret (.reg 27)

def stepTailProcs (bS bC : ℕ) : List Stmt := [dsStepTailStmt bS bC]

def stepTailIdx : ℕ := 0

lemma stepTailProcs_noRand (bS bC : ℕ) : ∀ s ∈ stepTailProcs bS bC, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The generation words `domGen[i]` (`i ≤ L`) and `sGen[i]` (`i ≤ L`). -/
def RBCtx.GenWord (r : RBCtx) (addr : ℕ) : Prop :=
  (dsDomGenBase r.b r.L r.vCap r.eCap + (r.j + 1) ≤ addr ∧
      addr < dsDomGenBase r.b r.L r.vCap r.eCap + (r.L + 1)) ∨
    (dsSGenBase r.b r.L r.vCap r.eCap + r.j ≤ addr ∧
      addr < dsSGenBase r.b r.L r.vCap r.eCap + (r.L + 1))

/-- Contract of `dsStepTailStmt`. -/
def dsStepTailContract (c : UTCtx) (H : MGraph) (hPtr hdr : ℕ) (r : RBCtx) : Contract where
  pre args mem :=
    (dsStepEndContract c H hPtr hdr r).pre (args.take 22) mem ∧
    args.drop 22 = [dsDomGenBase r.b r.L r.vCap r.eCap, dsSGenBase r.b r.L r.vCap r.eCap,
      r.j + 1, r.j, r.L + 1] ∧
    ∀ addr, ((hdr ≤ addr ∧ addr < c.da.out + c.size) ∨
      (hPtr ≤ addr ∧ addr < hPtr + dynGraphSize c.vCap c.da.eCap)) → ¬ r.GenWord addr
  post _ mem ret mem' :=
    ret = c.recs.length ∧
    DynGraphAt mem' hPtr c.vCap c.da.eCap (H.applyBatch c.recs) ∧
    mem' hdr = c.recs.length ∧
    (∀ K : MGraph, BatchBodyAt mem' c.da.out K c.recs c.words) ∧
    BucketsAt mem' r.L r.vCap r.eCap r.b r.newB ∧
    (∀ e < r.eCap, mem' (dsMinHBase r.b r.vCap r.eCap + e) = minHRebuild r.j r.es.toFinset r.m0 e) ∧
    (∀ i, r.j + 1 ≤ i → i < r.L + 1 → mem' (dsDomGenBase r.b r.L r.vCap r.eCap + i) = 0) ∧
    (∀ i, r.j ≤ i → i < r.L + 1 → mem' (dsSGenBase r.b r.L r.vCap r.eCap + i) = 0) ∧
    ∀ addr, (addr < hdr ∨ c.da.out + c.size ≤ addr) →
      (addr < hPtr ∨ hPtr + dynGraphSize c.vCap c.da.eCap ≤ addr) →
      (addr < dsMinHBase r.b r.vCap r.eCap ∨ dsDomGenBase r.b r.L r.vCap r.eCap ≤ addr) →
      ¬ r.GenWord addr → mem' addr = mem addr
  cost _ _ := 60 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length +
    60 * (c.da.hi - c.da.lo) + 210 * c.es.length + 670 * c.size +
    40 * (bucketsCat r.B r.j (r.L + 1 - r.j)).length + 60 * (r.L + 1 - r.j) +
    210 * r.es.length + 30 * (r.L + 1 - r.j) + 1300

end

private lemma sGen_le (b L vCap eCap : ℕ) :
    dsSGenBase b L vCap eCap + (L + 1) ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase]
  omega

private lemma domGen_lt_sGen (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap + (L + 1) ≤ dsSGenBase b L vCap eCap := by
  simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]
  omega

public section

/-- `dsStepTailStmt` meets `dsStepTailContract`. -/
theorem dsStepTail_meetsContract (c : UTCtx) (H : MGraph) (hPtr hdr : ℕ) (r : RBCtx)
    {p : Program}
    {bE bT bA bR bI bOps bEdge bSplit bBatch bAU bRB bC bF bPhase bSE bZ bCA bST : ℕ}
    (hpR : p.HasAt bR delRecordsProcs) (hpA : p.HasAt bA (delAllProcs bR))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpI : p.HasAt bI (insRecordsProcs bOps))
    (hpT : p.HasAt bT (uhTailProcs bA bI))
    (hpB : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpAU : p.HasAt bAU (applyUHProcs bBatch))
    (hpE : p.HasAt bE (uhEndProcs bT bAU))
    (hpC : p.HasAt bC clearBucketsProcs)
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpF : p.HasAt bF (fillLevelProcs bPhase))
    (hpRB : p.HasAt bRB (rebuildBucketsProcs bC bF))
    (hpSE : p.HasAt bSE (stepEndProcs bE bRB))
    (hpZ : p.HasAt bZ zeroRangeProcs) (hpCA : p.HasAt bCA (clearAboveProcs bZ))
    (hpST : p.HasAt bST (stepTailProcs bSE bCA)) :
    MeetsContract c.da.w p (bST + stepTailIdx) (dsStepTailContract c H hPtr hdr r) := by
  refine meetsContract_of_runs
    (hpST.get (i := stepTailIdx) (by simp [stepTailProcs, stepTailIdx])) ?_
  rintro args mem pos ω hW ⟨hpre1, hargs2, hdisj⟩
  have hwr : r.w = c.da.w := hpre1.2.2.2.1
  have hbound := r.hbound
  have hw16 := r.hw16
  have hjL := r.hjL
  have hsg := sGen_le r.b r.L r.vCap r.eCap
  have hds := domGen_lt_sGen r.b r.L r.vCap r.eCap
  rw [hwr] at hbound hw16
  have hargs : args = args.take 22 ++ args.drop 22 := (List.take_append_drop _ _).symm
  have hargs1 : args.take 22 = [c.da.nextBase, c.da.headBase, c.da.lenBase, c.da.lo, c.da.hi,
      c.da.pres, c.da.out, c.esPtr, c.es.length, c.presY, c.gPtr, hPtr, hdr] ++
      [dsHNextBase r.b r.vCap r.eCap, dsHHeadBase r.b r.vCap r.eCap,
      dsHDegDummyBase r.b r.L r.vCap r.eCap, r.j, r.L + 1, dsMinHBase r.b r.vCap r.eCap, r.b,
      r.esPtr, r.es.length] := by
    have h : (args.take 22).take 13 = _ := hpre1.1.1
    have h2 : (args.take 22).drop 13 = _ := hpre1.2.1
    rw [← List.take_append_drop 13 (args.take 22), h, h2]
  rw [hargs1, hargs2] at hargs
  subst hargs
  simp only [stepTailProcs, stepTailIdx, List.getElem_cons_zero]
  dsimp only [dsStepTailStmt]
  refine runs_start_le ?_
  -- Call 1: `U_H` and the buckets.
  refine runs_seq_call_le (vs := [c.da.nextBase, c.da.headBase, c.da.lenBase, c.da.lo, c.da.hi,
      c.da.pres, c.da.out, c.esPtr, c.es.length, c.presY, c.gPtr, hPtr, hdr,
      dsHNextBase r.b r.vCap r.eCap, dsHHeadBase r.b r.vCap r.eCap,
      dsHDegDummyBase r.b r.L r.vCap r.eCap, r.j, r.L + 1, dsMinHBase r.b r.vCap r.eCap, r.b,
      r.esPtr, r.es.length])
    (dsStepEnd_meetsContract c H hPtr hdr r hpR hpA hpOps hpI hpT hpB hpEdge hpSplit hpAU hpE
      hpC hpP hpF hpRB hpSE)
    (by eval_expr)
    (fun v hv => hW v (List.mem_append_left _ hv)) (by exact hpre1) ?_
  rintro r₁ mem₁ pos₁ ⟨hr₁, hH₁, hn₁, hB₁, hBk₁, hw₁, hfr₁⟩
  -- Call 2: the generation words.
  refine runs_seq_call_le (vs := [dsDomGenBase r.b r.L r.vCap r.eCap,
      dsSGenBase r.b r.L r.vCap r.eCap, r.j + 1, r.j, r.L + 1])
    (dsClearAbove_meetsContract (w := c.da.w) (dBase := dsDomGenBase r.b r.L r.vCap r.eCap)
      (sBase := dsSGenBase r.b r.L r.vCap r.eCap) (dLo := r.j + 1) (sLo := r.j) (hi := r.L + 1)
      hpZ hpCA)
    (by eval_expr)
    (fun v hv => hW v (List.mem_append_right _ hv))
    ⟨rfl, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨hzD, hzS, hfr₂⟩
  -- The second call writes only generation words.
  have hkeep : ∀ addr, ¬ r.GenWord addr → mem₂ addr = mem₁ addr := by
    intro addr hg
    simp only [RBCtx.GenWord, not_or, not_and, not_lt] at hg
    refine hfr₂ addr ?_ ?_
    · by_contra h
      have := hg.1 (by omega)
      omega
    · by_contra h
      have := hg.2 (by omega)
      omega
  have hout : ∀ addr, ((hdr ≤ addr ∧ addr < c.da.out + c.size) ∨
      (hPtr ≤ addr ∧ addr < hPtr + dynGraphSize c.vCap c.da.eCap)) → mem₂ addr = mem₁ addr :=
    fun addr h => hkeep addr (hdisj addr h)
  have hbk : ∀ addr, dsMinHBase r.b r.vCap r.eCap ≤ addr →
      addr < dsDomGenBase r.b r.L r.vCap r.eCap → mem₂ addr = mem₁ addr := by
    intro addr h1 h2
    refine hkeep addr ?_
    simp only [RBCtx.GenWord]
    omega
  refine runs_ret_le (v := r₁) (Expr.eval_reg_of_eq (by simp))
    ⟨hr₁, ?_, ?_, fun K => ?_, ?_, fun e he => ?_, fun i h1 h2 => ?_, hzS,
      fun addr h1 h2 h3 h4 => ?_⟩ ?_
  · exact dynGraphAt_of_agree hH₁ fun addr h1 h2 => hout addr (Or.inr ⟨h1, h2⟩)
  · show mem₂ hdr = _
    have hoB := c.hoB
    have hh := hpre1.1.2.2.1
    rw [hout hdr (Or.inl ⟨le_refl _, by simp only [UTCtx.size]; omega⟩)]
    exact hn₁
  · have hwl : c.words ≤ c.size := by
      simp only [UTCtx.words, UTCtx.size]
      have h1 : (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length ≤
          (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length := List.length_filter_le _ _
      have h2 := insList_length_le c.Y c.es
      omega
    have hhdr := hpre1.1.2.2.1
    exact (hB₁ K).of_agree fun i hi => hout _ (Or.inl ⟨by omega, by omega⟩)
  · exact hBk₁.of_agree_range hbk
  · show mem₂ _ = _
    have hd : dsDomGenBase r.b r.L r.vCap r.eCap = dsHDegDummyBase r.b r.L r.vCap r.eCap +
      (r.L + 1) := rfl
    have : dsMinHBase r.b r.vCap r.eCap + e < dsDomGenBase r.b r.L r.vCap r.eCap := by
      simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
      omega
    rw [hbk _ (Nat.le_add_right _ _) this]
    exact hw₁ e he
  · exact hzD i h1 h2
  · show mem₂ addr = _
    exact (hkeep addr h4).trans (hfr₁ addr h1 h2 h3)
  · simp only [Expr.size, argsSize, dsStepTailContract, dsStepEndContract,
      dsClearAboveContract]
    omega

end

end MinCostFlow.DynSpanner.Program
