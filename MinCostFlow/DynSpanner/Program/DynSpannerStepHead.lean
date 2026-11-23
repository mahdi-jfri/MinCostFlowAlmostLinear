module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedUpdateS
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPrefix
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# The start of `step`: the sets `S_i`, then the update

`dsStepHeadStmt` calls `dsUpdateSLevelsStmt`, which adds the touched vertices to `S_i` for
`i < j` and empties `S_i` for `i ≥ j`, and then `dsStepPrefixStmt`, which applies `u` to `G`,
`H` and the buckets. The sets come first because the touched vertices are those of the old `G`
(`touchedVertices st.G u` in `step`). The first call writes only the generation word, the `S`
words and the heap range `[heapPtr, ret)`, all outside the words that the second call reads
(`dsApplyUContract_pre_of_agree'`). The post names the memory `mid` between the two calls
(`dsStepHead_meetsContract`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [b, j, updPtr, heapPtr, gPtr, hPtr, minH, presH, out]`, with the addresses of the
state block computed by the caller; returns the number of records of `restrictUpdate u H`. -/
def dsStepHeadStmt (bAff bS : ℕ) : Stmt :=
  .call 9 (bAff + affIdxUpdateSLevels) [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 10 (bS + stepPrefixIdx) [.reg 4, .reg 5, .reg 0, .reg 6, .reg 2, .reg 7, .reg 8] ;;
  .ret (.reg 10)

def stepHeadProcs (bAff bS : ℕ) : List Stmt := [dsStepHeadStmt bAff bS]

def stepHeadIdx : ℕ := 0

lemma stepHeadProcs_noRand (bAff bS : ℕ) : ∀ s ∈ stepHeadProcs bAff bS, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsStepHeadStmt`. -/
def dsStepHeadContract (w L vCap eCap b j : ℕ) (G H : MGraph) (u : Update) (len : ℕ)
    (B : ℕ → List ℕ) (S_level : Fin (L + 1) → Finset ℕ) (sLists : Fin (L + 1) → List ℕ)
    (foot0 : ℕ → Prop) (updPtr heapPtr out : ℕ) : Contract where
  pre args mem :=
    args = [b, j, updPtr, heapPtr, dsGPtr b, dsHPtr b vCap eCap, dsMinHBase b vCap eCap,
      dgEPresBase (dsHPtr b vCap eCap) vCap, out] ∧
    (dsUpdateSLevelsContract w L vCap eCap b j G u len S_level sLists foot0).pre
      [b, j, updPtr, heapPtr] mem ∧
    (dsStepPrefixContract w L vCap eCap b G H u len B out).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr,
        dgEPresBase (dsHPtr b vCap eCap) vCap, out] mem ∧
    b + dsFixedSize L vCap eCap ≤ updPtr ∧ (updPtr + len ≤ heapPtr ∨ heapPtr + 4 * j ≤ updPtr) ∧
    (out + len ≤ heapPtr ∨ heapPtr + 4 * j ≤ out)
  post _ mem ret mem' := ∃ mid r₁,
    (dsUpdateSLevelsContract w L vCap eCap b j G u len S_level sLists foot0).post
      [b, j, updPtr, heapPtr] mem r₁ mid ∧
    (dsStepPrefixContract w L vCap eCap b G H u len B out).post
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr,
        dgEPresBase (dsHPtr b vCap eCap) vCap, out] mid ret mem'
  cost _ _ := 500 * (L + 1) + 1320 * len + 1100

end

private lemma domGen_le_h (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
    dsEdgeDomGenBase]
  omega

private lemma sHead_le_h (b L vCap eCap : ℕ) :
    dsSHeadBase b L vCap eCap + (L + 1) ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase]
  omega

private lemma vsGen_lt_h (b L vCap eCap i v : ℕ) (hi : i ≤ L) (hv : v < vCap) :
    dsVSGenBase b L vCap eCap + i * vCap + v < dsSHeadBase b L vCap eCap := by
  have hlt : i * vCap + v < (L + 1) * vCap := by
    calc i * vCap + v < i * vCap + vCap := by omega
      _ = (i + 1) * vCap := by ring
      _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right _ (by omega)
  simp only [dsSHeadBase]
  omega

private lemma domGen_le_sGen_h (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap ≤ dsSGenBase b L vCap eCap := by
  simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]
  omega

public section

/-- `dsStepHeadStmt` meets `dsStepHeadContract`. -/
theorem dsStepHead_meetsContract {w L vCap eCap b j : ℕ} {G H : MGraph} {u : Update} {len : ℕ}
    {B : ℕ → List ℕ} {S_level : Fin (L + 1) → Finset ℕ} {sLists : Fin (L + 1) → List ℕ}
    {foot0 : ℕ → Prop} {updPtr heapPtr out : ℕ} {p : Program}
    {bAff bS bR bF bU bD bPhase bOps bEdge bSplit bBatch bH : ℕ}
    (hpAff : p.HasAt bAff (affectedProcs bOps))
    (hpB : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpD : p.HasAt bD (levelsDeleteProcs bPhase))
    (hpU : p.HasAt bU (applyUProcs bBatch bD))
    (hpF : p.HasAt bF filterCopyProcs) (hpR : p.HasAt bR (restrictRecProcs bF))
    (hpS : p.HasAt bS (stepPrefixProcs bR bU))
    (hpH : p.HasAt bH (stepHeadProcs bAff bS)) :
    MeetsContract w p (bH + stepHeadIdx)
      (dsStepHeadContract w L vCap eCap b j G H u len B S_level sLists foot0 updPtr heapPtr
        out) := by
  refine meetsContract_of_runs
    (hpH.get (i := stepHeadIdx) (by simp [stepHeadProcs, stepHeadIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, hpreS, hpreP, hUB, dUH, dOH⟩
  simp only [stepHeadProcs, stepHeadIdx, List.getElem_cons_zero]
  dsimp only [dsStepHeadStmt]
  have hdom := domGen_le_h b L vCap eCap
  have hdsg := domGen_le_sGen_h b L vCap eCap
  have hfix : b + dsFixedSize L vCap eCap ≤ heapPtr := by
    obtain ⟨u', h', hargsS, _, _, _, _, hfix, _⟩ := hpreS
    simp only [List.cons.injEq, and_true, true_and] at hargsS
    obtain ⟨rfl, rfl⟩ := hargsS
    exact hfix
  have hvs : dsSGenBase b L vCap eCap ≤ dsVSGenBase b L vCap eCap := by
    simp only [dsVSGenBase]; omega
  have hvh : dsVSGenBase b L vCap eCap ≤ dsSHeadBase b L vCap eCap := by
    simp only [dsSHeadBase]; omega
  refine runs_start_le ?_
  -- Call 1: the sets `S_i`.
  refine runs_seq_call_le (vs := [b, j, updPtr, heapPtr])
    (dsUpdateSLevels_meetsContract (w := w) (L := L) (vCap := vCap) (eCap := eCap) (b := b)
      (j := j) (uLen := len) (G := G) (u := u) (S_level := S_level) (sLists := sLists)
      (foot0 := foot0) hpAff hpOps)
    (by eval_expr)
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> exact hW _ (by simp))
    hpreS ?_
  rintro r₁ mem₁ pos₁ hpost₁
  have hpost₁' := hpost₁
  obtain ⟨updPtr', heapPtr', hargs₁, hr₁lo, hr₁hi, _, _, _, _, hfr₁⟩ := hpost₁'
  simp only [List.cons.injEq, and_true, true_and] at hargs₁
  obtain ⟨rfl, rfl⟩ := hargs₁
  -- The words read by the second call are kept by the first.
  have hkeep : ∀ addr, addr < dsDomGenBase b L vCap eCap → addr ≠ b + dsGenOff →
      mem₁ addr = mem addr := by
    intro addr h1 h2
    refine hfr₁ addr ⟨h2, fun i hi => by omega, fun i hi v hv => by omega, fun i hi => by omega,
      ?_⟩
    left; omega
  obtain ⟨updPtr'', hargsP, hpreU, hoB, dOU, hout⟩ := hpreP
  simp only [List.cons.injEq, and_true, true_and] at hargsP
  subst hargsP
  have hsh := sHead_le_h b L vCap eCap
  have hpreU₁ := dsApplyUContract_pre_of_agree' hpreU fun addr h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hkeep addr h1 h2
    · refine hfr₁ addr ⟨?_, fun i hi => ?_, fun i hi v hv => ?_, fun i hi => ?_, ?_⟩
      · have : dsGenOff < dsFixedSize L vCap eCap := by
          have := dsFixedSize_pos L vCap eCap
          simp only [dsGenOff]; omega
        omega
      · omega
      · have := vsGen_lt_h b L vCap eCap i v hi hv; omega
      · omega
      · rcases dUH with h | h
        · left; omega
        · right; omega
  -- Call 2: the update.
  refine runs_seq_call_le (vs := [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap,
      updPtr, dgEPresBase (dsHPtr b vCap eCap) vCap, out])
    (dsStepPrefix_meetsContract (w := w) (L := L) (vCap := vCap) (eCap := eCap) (b := b) (G := G)
      (H := H) (u := u) (len := len) (B := B) (out := out)
      hpB hpEdge hpSplit hpOps hpP hpD hpU hpF hpR hpS)
    (by eval_expr)
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hW _ (by simp))
    ⟨updPtr, rfl, hpreU₁, hoB, dOU, hout⟩ ?_
  rintro r₂ mem₂ pos₂ hpost₂
  refine runs_ret_le (v := r₂) (Expr.eval_reg_of_eq (by simp))
    ⟨mem₁, r₁, hpost₁, hpost₂⟩ ?_
  simp only [Expr.size, argsSize, dsStepHeadContract, dsUpdateSLevelsContract,
    dsStepPrefixContract]
  omega

end

end MinCostFlow.DynSpanner.Program
