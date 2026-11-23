module

public import MinCostFlow.DynSpanner.Program.DynSpannerUHTail
public import MinCostFlow.DynSpanner.Program.DynSpannerApplyUH
import WordRAM.Tactic

/-!
# The end of `U_H`: write the records and apply them to `H`

`dsUHEndStmt` calls `dsUHTailStmt`, which writes the deletions and insertions of `U_H` after
the word `hdr`, and then `dsApplyUHStmt`, which writes the number of records at `hdr` and
applies the batch to `H`. Afterwards the buffer is a batch of these records, and `H` has become
`H.applyBatch U` (`dsUHEnd_meetsContract`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [nextBase, headBase, lenBase, lo, hi, presX, out, esPtr, esLen, presY, gPtr, hPtr,
hdr]` with `out = hdr + 1`; returns the number of records. -/
def dsUHEndStmt (bT bA : ℕ) : Stmt :=
  .call 13 (bT + uhTailIdx)
    [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10] ;;
  .call 14 (bA + applyUHIdx) [.reg 11, .reg 12, .reg 13] ;;
  .ret (.reg 13)

def uhEndProcs (bT bA : ℕ) : List Stmt := [dsUHEndStmt bT bA]

def uhEndIdx : ℕ := 0

lemma uhEndProcs_noRand (bT bA : ℕ) : ∀ s ∈ uhEndProcs bT bA, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The number of words of the records. -/
def UTCtx.words (c : UTCtx) : ℕ :=
  2 * (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length +
    4 * (insList c.Y c.es).length

/-- Contract of `dsUHEndStmt` for the graph `H` at `hPtr`. -/
def dsUHEndContract (c : UTCtx) (H : MGraph) (hPtr hdr : ℕ) : Contract where
  pre args mem :=
    args = [c.da.nextBase, c.da.headBase, c.da.lenBase, c.da.lo, c.da.hi, c.da.pres, c.da.out,
      c.esPtr, c.es.length, c.presY, c.gPtr, hPtr, hdr] ∧ mem = c.da.mem0 ∧
    hdr + 1 = c.da.out ∧ hPtr + dynGraphSize c.vCap c.da.eCap < 2 ^ c.da.w ∧
    (c.da.out + c.size ≤ hPtr ∨ hPtr + dynGraphSize c.vCap c.da.eCap ≤ hdr) ∧
    DynGraphAt mem hPtr c.vCap c.da.eCap H ∧ H.BatchIsValid c.recs ∧
    BatchWithinCaps c.vCap c.da.eCap c.recs
  post _ mem ret mem' :=
    ret = c.recs.length ∧
    DynGraphAt mem' hPtr c.vCap c.da.eCap (H.applyBatch c.recs) ∧
    mem' hdr = c.recs.length ∧
    (∀ K : MGraph, BatchBodyAt mem' c.da.out K c.recs c.words) ∧
    ∀ addr, (addr < hdr ∨ c.da.out + c.size ≤ addr) →
      (addr < hPtr ∨ hPtr + dynGraphSize c.vCap c.da.eCap ≤ addr) → mem' addr = mem addr
  cost _ _ := 60 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length +
    60 * (c.da.hi - c.da.lo) + 210 * c.es.length + 670 * c.size + 1000

end

public section

/-- `dsUHEndStmt` meets `dsUHEndContract`. -/
theorem dsUHEnd_meetsContract (c : UTCtx) (H : MGraph) (hPtr hdr : ℕ) {p : Program}
    {bE bT bA bR bI bOps bEdge bSplit bBatch bAU : ℕ}
    (hpR : p.HasAt bR delRecordsProcs) (hpA : p.HasAt bA (delAllProcs bR))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpI : p.HasAt bI (insRecordsProcs bOps))
    (hpT : p.HasAt bT (uhTailProcs bA bI))
    (hpB : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpAU : p.HasAt bAU (applyUHProcs bBatch))
    (hpE : p.HasAt bE (uhEndProcs bT bAU)) :
    MeetsContract c.da.w p (bE + uhEndIdx) (dsUHEndContract c H hPtr hdr) := by
  refine meetsContract_of_runs
    (hpE.get (i := uhEndIdx) (by simp [uhEndProcs, uhEndIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, hmem, hhdr, hgB, hdisj, hH, hvalid, hcaps⟩
  subst hmem
  simp only [uhEndProcs, uhEndIdx, List.getElem_cons_zero]
  dsimp only [dsUHEndStmt]
  have hw16 := c.da.hw16
  have hoB := c.hoB
  have hwl : c.words ≤ c.size := by
    simp only [UTCtx.words, UTCtx.size]
    have h1 : (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length ≤
        (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length := List.length_filter_le _ _
    have h2 := insList_length_le c.Y c.es
    omega
  have hrl : c.recs.length ≤ c.size := by
    simp only [UTCtx.recs, UTCtx.size, insRecs, List.length_append, List.length_map]
    have h1 : (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length ≤
        (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length := List.length_filter_le _ _
    have h2 := insList_length_le c.Y c.es
    omega
  have hwdef : c.words =
      2 * (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length +
        4 * (insList c.Y c.es).length := rfl
  have hsz : c.size = 2 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length +
    4 * c.es.length := rfl
  refine runs_start_le ?_
  -- Call 1: the records.
  refine runs_seq_call_le (vs := [c.da.nextBase, c.da.headBase, c.da.lenBase, c.da.lo, c.da.hi,
      c.da.pres, c.da.out, c.esPtr, c.es.length, c.presY, c.gPtr])
    (dsUHTail_meetsContract c hpR hpA hpOps hpI hpT) (by eval_expr)
    (fun v hv => hW v (List.mem_append_left [hPtr, hdr] hv)) ⟨rfl, rfl⟩ ?_
  rintro r₁ mem₁ pos₁ ⟨hr₁, hB₁, hwd₁, hfr₁⟩
  have hH₁ : DynGraphAt mem₁ hPtr c.vCap c.da.eCap H :=
    dynGraphAt_of_agree hH fun addr h1 h2 => hfr₁ addr (by omega)
  -- Call 2: apply the batch to `H`.
  refine runs_seq_call_le (vs := [hPtr, hdr, c.recs.length])
    (dsApplyUH_meetsContract (w := c.da.w) (vCap := c.vCap) (eCap := c.da.eCap) (H := H)
      (U := c.recs) (hPtr := hPtr) (out := hdr) (total := c.words)
      hpB hpEdge hpSplit hpOps hpAU)
    (by
      simp only [evalArgs, Expr.eval]
      simp [hr₁, startState])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl)
      · omega
      · omega
      · omega)
    ⟨rfl, hw16, hgB, by omega, by omega,
      fun i hi => by rw [show hdr + 1 + i = c.da.out + i by omega]; exact hwd₁ i hi,
      by rw [hhdr]; exact hB₁ H, hvalid, hcaps, hH₁⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨hH₂, hn₂, hfr₂⟩
  refine runs_ret_le (v := r₁) (Expr.eval_reg_of_eq (by simp))
    ⟨hr₁, hH₂, hn₂, fun K => ?_, fun addr h1 h2 => ?_⟩ ?_
  · exact (hB₁ K).of_agree fun i hi => hfr₂ _ (by omega) (by omega)
  · show mem₂ addr = _
    exact (hfr₂ addr h2 (by omega)).trans (hfr₁ addr (by omega))
  · simp only [Expr.size, argsSize, dsUHEndContract, dsUHTailContract, dsApplyUHContract]
    omega

end

end MinCostFlow.DynSpanner.Program
