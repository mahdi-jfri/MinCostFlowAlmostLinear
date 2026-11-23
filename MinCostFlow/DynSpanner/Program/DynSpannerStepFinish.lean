module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepTail
public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalks
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# The end of `step` with the walks of level `j`

`dsStepFinishStmt` calls `dsStepTailStmt` (the records of `U_H`, the new `H`, the new buckets and
the empty levels above `j`) and then `dsSetLevelWalksStmt` for level `j`, which needs the walks of
level `j` to be walks in the new `H`. The record buffer of `U_H` lies at or after the heap start
of the second call, so the second call may reuse it. All words that the second call reads lie
outside the words written by the first call, so its precondition is given on the memory before
the first call, with the new `H` in place of the graph at `hPtr` (`dsStepFinish_meetsContract`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args` are the 27 arguments of `dsStepTailStmt` followed by
`[b, j, eListPtr, numEdges, mEmbPtr, heapPtr]`; returns the end of the heap used. -/
def dsStepFinishStmt (bT bLW : ℕ) : Stmt :=
  .call 33 (bT + stepTailIdx)
    [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
      .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 17, .reg 18, .reg 19, .reg 20,
      .reg 21, .reg 22, .reg 23, .reg 24, .reg 25, .reg 26] ;;
  .call 34 (bLW + lwIdxSetLevelWalks) [.reg 27, .reg 28, .reg 29, .reg 30, .reg 31, .reg 32] ;;
  .ret (.reg 34)

def stepFinishProcs (bT bLW : ℕ) : List Stmt := [dsStepFinishStmt bT bLW]

def stepFinishIdx : ℕ := 0

lemma stepFinishProcs_noRand (bT bLW : ℕ) : ∀ s ∈ stepFinishProcs bT bLW, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsStepFinishStmt`, for the level `r.j` with the list `eL` of its edges, the
walks `emb` in the table at `mEmbPtr`, and the graph `G` at `dsGPtr r.b`. -/
def dsStepFinishContract (c : UTCtx) (H : MGraph) (hdr : ℕ) (r : RBCtx) (G : MGraph)
    (eL : List ℕ) (emb : MinCostFlow.Embedding) (foot0 : ℕ → Prop)
    (eListPtr mEmbPtr heapPtr : ℕ) : Contract where
  pre args mem :=
    (dsStepTailContract c H (dsHPtr r.b r.vCap r.eCap) hdr r).pre (args.take 27) mem ∧
    args.drop 27 = [r.b, r.j, eListPtr, eL.length, mEmbPtr, heapPtr] ∧
    c.vCap = r.vCap ∧ c.da.eCap = r.eCap ∧
    1 ≤ r.b ∧ r.b + dsFixedSize r.L r.vCap r.eCap ≤ heapPtr ∧ heapPtr ≤ hdr ∧
    heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum < 2 ^ c.da.w ∧
    r.b + dsFixedSize r.L r.vCap r.eCap ≤ eListPtr ∧ eListPtr + eL.length ≤ heapPtr ∧
    r.b + dsFixedSize r.L r.vCap r.eCap ≤ mEmbPtr ∧ mEmbPtr + r.eCap ≤ heapPtr ∧
    mem (r.b + dsGenOff) + 1 + eL.length < 2 ^ c.da.w ∧
    (∀ v < r.vCap, mem (dsVStampBase r.b r.L r.vCap r.eCap + v) ≤ mem (r.b + dsGenOff)) ∧
    (∀ e < r.eCap, mem (dsEdgeDomGenBase r.b r.L r.vCap r.eCap + r.j * r.eCap + e) ≤
      mem (r.b + dsGenOff)) ∧
    (∀ v < r.vCap, mem (dsRevGenBase r.b r.L r.vCap r.eCap + r.j * r.vCap + v) ≤
      mem (r.b + dsGenOff)) ∧
    (∀ a, foot0 a → r.b + dsFixedSize r.L r.vCap r.eCap ≤ a ∧ a < heapPtr) ∧
    eL.Nodup ∧ ListAt mem eListPtr eL ∧
    DynGraphAt mem (dsGPtr r.b) r.vCap r.eCap G ∧ G.IsValid ∧
    (∀ v ∈ G.V, v < r.vCap) ∧ (∀ e ∈ G.E, e < r.eCap) ∧
    (H.applyBatch c.recs).IsValid ∧ G.V ⊆ (H.applyBatch c.recs).V ∧
    (∀ v ∈ (H.applyBatch c.recs).V, v < r.vCap) ∧ (∀ e ∈ (H.applyBatch c.recs).E, e < r.eCap) ∧
    (∀ e ∈ eL, e < r.eCap ∧ e ∈ G.E ∧ (H.applyBatch c.recs).IsWalk (G.tail e) (G.head e) (emb e) ∧
      MWalkAt mem (mem (mEmbPtr + e)) (emb e) ∧
      r.b + dsFixedSize r.L r.vCap r.eCap ≤ mem (mEmbPtr + e) ∧
      mem (mEmbPtr + e) + (mWalkEncode (emb e)).length ≤ heapPtr)
  post args mem ret mem' := ∃ mid r₁,
    (dsStepTailContract c H (dsHPtr r.b r.vCap r.eCap) hdr r).post (args.take 27) mem r₁ mid ∧
    (dsSetLevelWalksContract c.da.w r.L r.vCap r.eCap r.b r.j G (H.applyBatch c.recs) eL emb
      foot0).post [r.b, r.j, eListPtr, eL.length, mEmbPtr, heapPtr] mid ret mem'
  cost _ _ := 60 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length +
    60 * (c.da.hi - c.da.lo) + 210 * c.es.length + 670 * c.size +
    40 * (bucketsCat r.B r.j (r.L + 1 - r.j)).length + 60 * (r.L + 1 - r.j) +
    210 * r.es.length + 30 * (r.L + 1 - r.j) +
    400 * (eL.map fun e => (emb e).length).sum + 620 * eL.length + 1800

end

private lemma idx_lt_mul' {i n e m : ℕ} (hi : i < n) (he : e < m) : i * m + e < n * m := by
  calc i * m + e < i * m + m := by omega
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)

private lemma fin_layout (b L vCap eCap : ℕ) :
    dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap ∧
    dsSGenBase b L vCap eCap + (L + 1) ≤ dsVStampBase b L vCap eCap ∧
    dsRevHeadBase b L vCap eCap + (L + 1) * vCap = dsSGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap ∧
    dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap ∧
    dsGPtr b = b + 6 := by
  have hfa := dsFixedSize_add b L vCap eCap
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · rw [← hfa]; simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  · simp only [dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase]; omega
  · simp only [dsMinHBase, dsAuxPtr]; omega
  · simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]; omega

public section

/-- `dsStepFinishStmt` meets `dsStepFinishContract`. -/
theorem dsStepFinish_meetsContract (c : UTCtx) (H : MGraph) (hdr : ℕ) (r : RBCtx) (G : MGraph)
    (eL : List ℕ) (emb : MinCostFlow.Embedding) (foot0 : ℕ → Prop)
    (eListPtr mEmbPtr heapPtr : ℕ) {p : Program}
    {bE bT bA bR bI bOps bEdge bSplit bBatch bAU bRB bC bF bPhase bSE bZ bCA bST bLW bRev bFin : ℕ}
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
    (hpST : p.HasAt bST (stepTailProcs bSE bCA))
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev))
    (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpFin : p.HasAt bFin (stepFinishProcs bST bLW)) :
    MeetsContract c.da.w p (bFin + stepFinishIdx)
      (dsStepFinishContract c H hdr r G eL emb foot0 eListPtr mEmbPtr heapPtr) := by
  refine meetsContract_of_runs
    (hpFin.get (i := stepFinishIdx) (by simp [stepFinishProcs, stepFinishIdx])) ?_
  rintro args mem pos ω hW ⟨hpre1, hargs2, hvc, hec, hb1, hfixH, hHhdr, hheapMax, hEl1, hEl2,
    hME1, hME2, hgen, hvst, hedg, hrevg, hfoot, hnd, hEL, hG, hGv, hGV, hGE, hHv, hGHV, hHV, hHE,
    hedges⟩
  have hwr : r.w = c.da.w := hpre1.1.2.2.2.1
  have hw16 := r.hw16
  rw [hwr] at hw16
  have hjL := r.hjL
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := fin_layout r.b r.L r.vCap r.eCap
  have e1 : ((args.take 27).take 22).take 13 = [c.da.nextBase, c.da.headBase, c.da.lenBase,
      c.da.lo, c.da.hi, c.da.pres, c.da.out, c.esPtr, c.es.length, c.presY, c.gPtr,
      dsHPtr r.b r.vCap r.eCap, hdr] := hpre1.1.1.1
  have e2 : ((args.take 27).take 22).drop 13 = [dsHNextBase r.b r.vCap r.eCap,
      dsHHeadBase r.b r.vCap r.eCap, dsHDegDummyBase r.b r.L r.vCap r.eCap, r.j, r.L + 1,
      dsMinHBase r.b r.vCap r.eCap, r.b, r.esPtr, r.es.length] := hpre1.1.2.1
  have e3 : (args.take 27).drop 22 = [dsDomGenBase r.b r.L r.vCap r.eCap,
      dsSGenBase r.b r.L r.vCap r.eCap, r.j + 1, r.j, r.L + 1] := hpre1.2.1
  have hA := List.take_append_drop 27 args
  rw [← List.take_append_drop 22 (args.take 27), ← List.take_append_drop 13 ((args.take 27).take 22),
    e1, e2, e3, hargs2] at hA
  subst hA
  simp only [stepFinishProcs, stepFinishIdx, List.getElem_cons_zero]
  dsimp only [dsStepFinishStmt]
  refine runs_start_le ?_
  -- Call 1: the end of the step.
  refine runs_seq_call_le (vs := [c.da.nextBase, c.da.headBase, c.da.lenBase,
      c.da.lo, c.da.hi, c.da.pres, c.da.out, c.esPtr, c.es.length, c.presY, c.gPtr,
      dsHPtr r.b r.vCap r.eCap, hdr, dsHNextBase r.b r.vCap r.eCap,
      dsHHeadBase r.b r.vCap r.eCap, dsHDegDummyBase r.b r.L r.vCap r.eCap, r.j, r.L + 1,
      dsMinHBase r.b r.vCap r.eCap, r.b, r.esPtr, r.es.length, dsDomGenBase r.b r.L r.vCap r.eCap,
      dsSGenBase r.b r.L r.vCap r.eCap, r.j + 1, r.j, r.L + 1])
    (dsStepTail_meetsContract c H (dsHPtr r.b r.vCap r.eCap) hdr r hpR hpA hpOps hpI hpT hpB
      hpEdge hpSplit hpAU hpE hpC hpP hpF hpRB hpSE hpZ hpCA hpST)
    (by eval_expr)
    (fun v hv => hW v (List.mem_append_left _ hv)) (by exact hpre1) ?_
  rintro r₁ mem₁ pos₁ hpost₁
  have hpost₁' := hpost₁
  obtain ⟨-, hH₁, -, -, -, -, -, -, hfr₁⟩ := hpost₁'
  have hoB := c.hoB
  have hsz : c.size = 2 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length +
    4 * c.es.length := rfl
  have hhdr : hdr + 1 = c.da.out := hpre1.1.1.2.2.1
  -- The words read by the second call are kept by the first.
  have hK : ∀ addr, (addr < dsGPtr r.b + dynGraphSize r.vCap r.eCap ∨
      (dsEdgeDomGenBase r.b r.L r.vCap r.eCap ≤ addr ∧ addr < dsSGenBase r.b r.L r.vCap r.eCap) ∨
      (dsSGenBase r.b r.L r.vCap r.eCap + (r.L + 1) ≤ addr ∧ addr < heapPtr)) →
      mem₁ addr = mem addr := by
    intro addr h
    have hsf : dsSGenBase r.b r.L r.vCap r.eCap + (r.L + 1) ≤ r.b + dsFixedSize r.L r.vCap r.eCap := by
      omega
    refine hfr₁ addr ?_ ?_ ?_ ?_
    · left; rcases h with h | h | h <;> omega
    · rw [hvc, hec]; rcases h with h | h | h
      · left; omega
      · right; omega
      · right; omega
    · rcases h with h | h | h
      · left; omega
      · right; omega
      · right; omega
    · simp only [RBCtx.GenWord, not_or, not_and, not_lt]
      rcases h with h | h | h <;> refine ⟨fun h' => by omega, fun h' => by omega⟩
  have hr0 : r.mem0 = mem := hpre1.1.2.2.1
  have hgen₁ : mem₁ (r.b + dsGenOff) = mem (r.b + dsGenOff) :=
    hK _ (Or.inl (by simp only [dsGenOff]; omega))
  -- Call 2: the walks of level `j`.
  refine runs_seq_call_le (vs := [r.b, r.j, eListPtr, eL.length, mEmbPtr, heapPtr])
    (dsSetLevelWalks_meetsContract (w := c.da.w) (L := r.L) (vCap := r.vCap) (eCap := r.eCap)
      (b := r.b) (lvl := r.j) (G := G) (H := H.applyBatch c.recs) (eL := eL) (emb := emb)
      (foot0 := foot0) hpLW hpRev hpOps)
    (by eval_expr)
    (fun v hv => hW v (List.mem_append_right _ hv))
    ⟨eListPtr, mEmbPtr, heapPtr, rfl, hw16, hb1, hjL, hfixH, hheapMax, by omega, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfoot, ?_, ?_, hnd, ?_, ?_, hGv, hGV, hGE, ?_, hHv, hGHV, hHV,
      hHE, ?_⟩ ?_
  · show mem₁ _ = _
    rw [hK _ (Or.inl (by simp only [dsLOff]; omega)), ← hr0]; exact r.hLw
  · show mem₁ _ = _
    rw [hK _ (Or.inl (by simp only [dsVCapOff]; omega)), ← hr0]; exact r.hvw
  · show mem₁ _ = _
    rw [hK _ (Or.inl (by simp only [dsECapOff]; omega)), ← hr0]; exact r.hew
  · show mem₁ _ + 1 + _ < _
    rw [hgen₁]; exact hgen
  · intro v hv
    show mem₁ _ ≤ mem₁ _
    rw [hgen₁, hK _ (Or.inr (Or.inr ⟨by omega, by omega⟩))]
    exact hvst v hv
  · intro e he
    show mem₁ _ ≤ mem₁ _
    have := idx_lt_mul' (show r.j < r.L + 1 by omega) he
    rw [hgen₁, hK _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hedg e he
  · intro v hv
    show mem₁ _ ≤ mem₁ _
    have := idx_lt_mul' (show r.j < r.L + 1 by omega) hv
    rw [hgen₁, hK _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hrevg v hv
  · intro k hk
    refine ⟨by simp only [dsGenOff]; omega, by omega, fun e he => ?_, fun e he => ?_,
      fun v hv => ?_, fun v hv => ?_, fun v hv => by omega, Or.inl (by omega)⟩
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) he; omega
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) he; omega
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) hv; omega
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) hv; omega
  · intro e' he'
    have he'C := (hedges e' he').1
    refine ⟨by simp only [dsGenOff]; omega, by omega, fun e he => ?_, fun e he => ?_,
      fun v hv => ?_, fun v hv => ?_, fun v hv => by omega, Or.inl (by omega)⟩
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) he; omega
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) he; omega
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) hv; omega
    · have := idx_lt_mul' (show r.j < r.L + 1 by omega) hv; omega
  · exact hEL.congr fun k h1 h2 => hK k (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · exact dynGraphAt_of_agree hG fun addr h1 h2 => hK addr (Or.inl h2)
  · rw [hvc, hec] at hH₁; exact hH₁
  · intro e he
    obtain ⟨heC, heG, hwalk, hmw, hlo, hhi⟩ := hedges e he
    have hp : mem₁ (mEmbPtr + e) = mem (mEmbPtr + e) :=
      hK _ (Or.inr (Or.inr ⟨by omega, by omega⟩))
    rw [mWalkEncode_length] at hhi
    refine ⟨heG, hwalk, ?_, ?_, ?_⟩
    · show MWalkAt mem₁ (mem₁ (mEmbPtr + e)) (emb e)
      rw [hp]
      exact hmw.of_agree fun addr h1 h2 => hK addr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · show _ ≤ mem₁ _
      rw [hp]; exact hlo
    · show mem₁ _ + _ ≤ _
      rw [hp, mWalkEncode_length]; exact hhi
  rintro r₂ mem₂ pos₂ hpost₂
  refine runs_ret_le (v := r₂) (Expr.eval_reg_of_eq (by simp)) ⟨mem₁, r₁, by exact hpost₁,
    hpost₂⟩ ?_
  simp only [Expr.size, argsSize, dsStepFinishContract, dsStepTailContract,
    dsSetLevelWalksContract]
  omega

end

end MinCostFlow.DynSpanner.Program
