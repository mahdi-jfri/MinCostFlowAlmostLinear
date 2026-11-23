module

public import MinCostFlow.DynSpanner.Program.DynSpannerUHEnd
public import MinCostFlow.DynSpanner.Program.DynSpannerRebuildBuckets
import WordRAM.Tactic

/-!
# The end of `step`: apply `U_H`, then rebuild the buckets

`dsStepEndStmt` calls `dsUHEndStmt`, which writes the records of `U_H` and applies them to `H`,
and then `dsRebuildBucketsStmt`, which rebuilds the buckets and the words `minH` for the new
levels. The records are written first because `dsUHEndStmt` reads the old buckets of the levels
`j..L` to find the deletions. The two calls work on disjoint parts of memory, so the facts of the
first call survive the second (`dsStepEnd_meetsContract`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args` are the 13 arguments of `dsUHEndStmt` followed by the 9 arguments of
`dsRebuildBucketsStmt`; returns the number of records of `U_H`. -/
def dsStepEndStmt (bU bR : ℕ) : Stmt :=
  .call 22 (bU + uhEndIdx)
    [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
      .reg 11, .reg 12] ;;
  .call 23 (bR + rebuildBucketsIdx)
    [.reg 13, .reg 14, .reg 15, .reg 16, .reg 17, .reg 18, .reg 19, .reg 20, .reg 21] ;;
  .ret (.reg 22)

def stepEndProcs (bU bR : ℕ) : List Stmt := [dsStepEndStmt bU bR]

def stepEndIdx : ℕ := 0

lemma stepEndProcs_noRand (bU bR : ℕ) : ∀ s ∈ stepEndProcs bU bR, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The words that `dsRebuildBucketsStmt` reads: the header of the state block, the bucket
region `[minH, domGen)` and the list `es`. -/
def RBCtx.Reads (r : RBCtx) (addr : ℕ) : Prop :=
  (r.b ≤ addr ∧ addr < dsGPtr r.b) ∨
    (dsMinHBase r.b r.vCap r.eCap ≤ addr ∧ addr < dsDomGenBase r.b r.L r.vCap r.eCap) ∨
    (r.esPtr ≤ addr ∧ addr < r.esPtr + r.es.length)

/-- Contract of `dsStepEndStmt`. The words written by `dsUHEndStmt` (the record buffer from
`hdr` and the graph `H` at `hPtr`) are outside the words that `dsRebuildBucketsStmt` reads or
writes. -/
def dsStepEndContract (c : UTCtx) (H : MGraph) (hPtr hdr : ℕ) (r : RBCtx) : Contract where
  pre args mem :=
    (dsUHEndContract c H hPtr hdr).pre (args.take 13) mem ∧
    args.drop 13 = [dsHNextBase r.b r.vCap r.eCap, dsHHeadBase r.b r.vCap r.eCap,
      dsHDegDummyBase r.b r.L r.vCap r.eCap, r.j, r.L + 1, dsMinHBase r.b r.vCap r.eCap, r.b,
      r.esPtr, r.es.length] ∧
    r.mem0 = mem ∧ r.w = c.da.w ∧
    ∀ addr, ((hdr ≤ addr ∧ addr < c.da.out + c.size) ∨
      (hPtr ≤ addr ∧ addr < hPtr + dynGraphSize c.vCap c.da.eCap)) →
      ¬ r.Reads addr ∧
      (addr < dsMinHBase r.b r.vCap r.eCap ∨ dsDomGenBase r.b r.L r.vCap r.eCap ≤ addr)
  post _ mem ret mem' :=
    ret = c.recs.length ∧
    DynGraphAt mem' hPtr c.vCap c.da.eCap (H.applyBatch c.recs) ∧
    mem' hdr = c.recs.length ∧
    (∀ K : MGraph, BatchBodyAt mem' c.da.out K c.recs c.words) ∧
    BucketsAt mem' r.L r.vCap r.eCap r.b r.newB ∧
    (∀ e < r.eCap, mem' (dsMinHBase r.b r.vCap r.eCap + e) = minHRebuild r.j r.es.toFinset r.m0 e) ∧
    ∀ addr, (addr < hdr ∨ c.da.out + c.size ≤ addr) →
      (addr < hPtr ∨ hPtr + dynGraphSize c.vCap c.da.eCap ≤ addr) →
      (addr < dsMinHBase r.b r.vCap r.eCap ∨ dsDomGenBase r.b r.L r.vCap r.eCap ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 60 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length +
    60 * (c.da.hi - c.da.lo) + 210 * c.es.length + 670 * c.size +
    40 * (bucketsCat r.B r.j (r.L + 1 - r.j)).length + 60 * (r.L + 1 - r.j) +
    210 * r.es.length + 1200

end

public section

/-- Two contexts with the same words `minH` below `eCap` have the same new buckets. -/
lemma RBCtx.newB_ofAgree (r : RBCtx) (mem : ℕ → ℕ) (hag) :
    (r.ofAgree mem hag).newB = r.newB := by
  funext i
  have hm : ∀ e < r.eCap, (r.ofAgree mem hag).m0 e = r.m0 e := fun e he => by
    show mem (dsMinHBase r.b r.vCap r.eCap + e) = r.mem0 (dsMinHBase r.b r.vCap r.eCap + e)
    exact hag _ (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by
      simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
      omega⟩))
  have hfil : (r.es.filter fun e => decide (minHClear r.j (r.ofAgree mem hag).m0 e = 0)) =
      r.es.filter fun e => decide (minHClear r.j r.m0 e = 0) :=
    List.filter_congr fun x hx => by
      unfold minHClear; rw [hm x (r.hesC x hx)]
  show (if i < r.j then r.B i else if i = r.j then
    (r.es.filter fun e => decide (minHClear r.j (r.ofAgree mem hag).m0 e = 0)).reverse
    else []) = _
  rw [hfil]
  rfl

/-- `dsStepEndStmt` meets `dsStepEndContract`. -/
theorem dsStepEnd_meetsContract (c : UTCtx) (H : MGraph) (hPtr hdr : ℕ) (r : RBCtx)
    {p : Program}
    {bE bT bA bR bI bOps bEdge bSplit bBatch bAU bRB bC bF bPhase bSE : ℕ}
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
    (hpSE : p.HasAt bSE (stepEndProcs bE bRB)) :
    MeetsContract c.da.w p (bSE + stepEndIdx) (dsStepEndContract c H hPtr hdr r) := by
  refine meetsContract_of_runs
    (hpSE.get (i := stepEndIdx) (by simp [stepEndProcs, stepEndIdx])) ?_
  rintro args mem pos ω hW ⟨hpre1, hargs2, hr0, hwr, hdisj⟩
  have hargs : args = args.take 13 ++ args.drop 13 := (List.take_append_drop _ _).symm
  have hargs1 := hpre1.1
  rw [hargs1, hargs2] at hargs
  subst hargs
  simp only [stepEndProcs, stepEndIdx, List.getElem_cons_zero]
  dsimp only [dsStepEndStmt]
  refine runs_start_le ?_
  -- Call 1: `U_H`.
  refine runs_seq_call_le (vs := [c.da.nextBase, c.da.headBase, c.da.lenBase, c.da.lo, c.da.hi,
      c.da.pres, c.da.out, c.esPtr, c.es.length, c.presY, c.gPtr, hPtr, hdr])
    (dsUHEnd_meetsContract c H hPtr hdr hpR hpA hpOps hpI hpT hpB hpEdge hpSplit hpAU hpE)
    (by eval_expr)
    (fun v hv => hW v (List.mem_append_left _ hv)) (by exact ⟨rfl, hpre1.2⟩) ?_
  rintro r₁ mem₁ pos₁ ⟨hr₁, hH₁, hn₁, hB₁, hfr₁⟩
  -- The words read by the rebuild are not changed by the first call.
  have hag : ∀ addr, r.Reads addr → mem₁ addr = r.mem0 addr := by
    intro addr hR
    rw [hr0]
    refine hfr₁ addr ?_ ?_
    · by_contra h
      exact (hdisj addr (Or.inl ⟨by omega, by omega⟩)).1 hR
    · by_contra h
      exact (hdisj addr (Or.inr ⟨by omega, by omega⟩)).1 hR
  set r' := r.ofAgree mem₁ hag with hr'
  have hRB := dsRebuildBuckets_meetsContract r' hpC hpP hpOps hpF hpRB
  rw [show r'.w = c.da.w from hwr] at hRB
  -- Call 2: the buckets.
  refine runs_seq_call_le (vs := [dsHNextBase r.b r.vCap r.eCap, dsHHeadBase r.b r.vCap r.eCap,
      dsHDegDummyBase r.b r.L r.vCap r.eCap, r.j, r.L + 1, dsMinHBase r.b r.vCap r.eCap, r.b,
      r.esPtr, r.es.length]) hRB
    (by eval_expr)
    (fun v hv => hW v (List.mem_append_right _ hv)) ⟨rfl, rfl⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨hBk₂, hw₂, hfr₂⟩
  have hfr₂' : ∀ addr, (addr < dsMinHBase r.b r.vCap r.eCap ∨
      dsDomGenBase r.b r.L r.vCap r.eCap ≤ addr) → mem₂ addr = mem₁ addr := hfr₂
  have hout : ∀ addr, ((hdr ≤ addr ∧ addr < c.da.out + c.size) ∨
      (hPtr ≤ addr ∧ addr < hPtr + dynGraphSize c.vCap c.da.eCap)) → mem₂ addr = mem₁ addr :=
    fun addr h => hfr₂' addr (hdisj addr h).2
  refine runs_ret_le (v := r₁) (Expr.eval_reg_of_eq (by simp))
    ⟨hr₁, ?_, ?_, fun K => ?_, ?_, fun e he => ?_, fun addr h1 h2 h3 => ?_⟩ ?_
  · exact dynGraphAt_of_agree hH₁ fun addr h1 h2 => hout addr (Or.inr ⟨h1, h2⟩)
  · show mem₂ hdr = _
    have hsz := c.hoB
    rw [hout hdr (Or.inl ⟨le_refl _, by have := hpre1.2.2.1; omega⟩)]
    exact hn₁
  · have hwl : c.words ≤ c.size := by
      simp only [UTCtx.words, UTCtx.size]
      have h1 : (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length ≤
          (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length := List.length_filter_le _ _
      have h2 := insList_length_le c.Y c.es
      omega
    have hhdr := hpre1.2.2.1
    exact (hB₁ K).of_agree fun i hi => hout _ (Or.inl ⟨by omega, by omega⟩)
  · have := r.newB_ofAgree mem₁ hag
    rw [← this]
    exact hBk₂
  · show mem₂ _ = _
    refine (hw₂ e he).trans ?_
    have hm : r'.m0 e = r.m0 e := by
      show mem₁ (dsMinHBase r.b r.vCap r.eCap + e) = r.mem0 (dsMinHBase r.b r.vCap r.eCap + e)
      exact hag _ (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by
        simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
        omega⟩))
    show minHRebuild r.j r.es.toFinset r'.m0 e = _
    unfold minHRebuild minHClear
    rw [hm]
  · show mem₂ addr = _
    exact (hfr₂' addr h3).trans (hfr₁ addr h1 h2)
  · simp only [Expr.size, argsSize, dsStepEndContract, dsUHEndContract,
      dsRebuildBucketsContract]
    have h1 : (bucketsCat r'.B r'.j (r'.L + 1 - r'.j)).length =
      (bucketsCat r.B r.j (r.L + 1 - r.j)).length := rfl
    have h2 : r'.es.length = r.es.length := rfl
    have h3 : r'.L + 1 - r'.j = r.L + 1 - r.j := rfl
    omega

end

end MinCostFlow.DynSpanner.Program
