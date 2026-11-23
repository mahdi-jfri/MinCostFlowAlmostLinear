module

public import MinCostFlow.DynSpanner.Program.DynSpannerPhase
import WordRAM.Tactic

/-!
# Deleting an edge from the levels

When a step deletes an edge `e` of `G`, the edge also leaves `H` and every level. In the layout of
`StateLayout.lean` the levels of `H` are kept through `minH` (one plus the smallest level of an
edge, `0` for an edge outside `H`) and the buckets `hBuckets i` (the edges whose smallest level is
`i`). So the deletion has to take `e` out of its bucket and set `minH[e] := 0`.
`dsLevelsDeleteStmt` reads `minH[e]` and, if it is not `0`, calls `hBucketRemoveStmt` on bucket
`minH[e] - 1`. `dsLevelsDelete_meetsContract` proves that afterwards every bucket `B i` has become
`(B i).erase e`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [b, minHBase, e]`. -/
def dsLevelsDeleteStmt (bPhase : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 1) (.reg 2))) ;;
  .cond (.reg 3)
    (.call 4 (bPhase + phaseIdxHBucketRemove) [.reg 0, .bin .sub (.reg 3) (.const 1), .reg 2])
    .nop ;;
  .ret (.const 0)

def levelsDeleteProcs (bPhase : ℕ) : List Stmt := [dsLevelsDeleteStmt bPhase]

def levelsDeleteIdx : ℕ := 0

lemma levelsDeleteProcs_noRand (bPhase : ℕ) : ∀ s ∈ levelsDeleteProcs bPhase, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The bucket facts of all levels for the bucket lists `B`. -/
def BucketsAt (mem : ℕ → ℕ) (L vCap eCap b : ℕ) (B : ℕ → List ℕ) : Prop :=
  ∀ i ≤ L, IsDoublyLinkedList mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
    (dsHHeadBase b vCap eCap + i) eCap (B i) ∧
    mem (dsHDegDummyBase b L vCap eCap + i) = (B i).length

/-- Contract of `dsLevelsDeleteStmt`. -/
def dsLevelsDeleteContract (w L vCap eCap b : ℕ) (B : ℕ → List ℕ) (e : ℕ) : Contract where
  pre args mem :=
    args = [b, dsMinHBase b vCap eCap, e] ∧ 16 ≤ 2 ^ w ∧ b + dsFixedSize L vCap eCap < 2 ^ w ∧
    e < eCap ∧ mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧
    mem (b + dsECapOff) = eCap ∧ BucketsAt mem L vCap eCap b B ∧
    (∀ i ≤ L, ∀ i' ≤ L, i ≠ i' → ∀ x ∈ B i, x ∉ B i') ∧
    (mem (dsMinHBase b vCap eCap + e) = 0 → ∀ i ≤ L, e ∉ B i) ∧
    (∀ i, mem (dsMinHBase b vCap eCap + e) = i + 1 → i ≤ L ∧ e ∈ B i)
  post _ mem _ mem' :=
    mem' (dsMinHBase b vCap eCap + e) = 0 ∧
    BucketsAt mem' L vCap eCap b (fun i => (B i).erase e) ∧
    (∀ e' < eCap, e' ≠ e → mem' (dsMinHBase b vCap eCap + e') = mem (dsMinHBase b vCap eCap + e')) ∧
    ∀ addr, (addr < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 220

end

private lemma domGen_le (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
    dsEdgeDomGenBase]
  omega

public section

/-- `dsLevelsDeleteStmt` meets `dsLevelsDeleteContract`. -/
theorem dsLevelsDelete_meetsContract {w L vCap eCap b : ℕ} {B : ℕ → List ℕ} {e : ℕ}
    {p : Program} {bD bPhase bOps bEdge : ℕ}
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge)) (hpOps : p.HasAt bOps dgOpsProcs)
    (hpD : p.HasAt bD (levelsDeleteProcs bPhase)) :
    MeetsContract w p (bD + levelsDeleteIdx) (dsLevelsDeleteContract w L vCap eCap b B e) := by
  refine meetsContract_of_runs
    (hpD.get (i := levelsDeleteIdx) (by simp [levelsDeleteProcs, levelsDeleteIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hw16, hbound, heC, hL, hvC, heCw, hB, hdisj, hzero, hsome⟩
  simp only [levelsDeleteProcs, levelsDeleteIdx, List.getElem_cons_zero]
  dsimp only [dsLevelsDeleteStmt]
  have hdom := domGen_le b L vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hnext_def : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hprev_def : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hhead_def : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hdeg_def : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hmin_ge : b ≤ dsMinHBase b vCap eCap := by
    simp only [dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
  set m := mem (dsMinHBase b vCap eCap + e) with hm
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := m)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) rfl) ?_
  refine runs_seq_cond_le (v := m) (Expr.eval_reg_of_eq (by simp)) (fun hne => ?_) (fun hz => ?_)
  · -- `e` is in bucket `m - 1`.
    obtain ⟨hiL, heB⟩ := hsome (m - 1) (by omega)
    obtain ⟨hdll, hdeg⟩ := hB (m - 1) hiL
    refine runs_seq_call_le (hBucketRemove_meetsContract (w := w) (L := L) (vCap := vCap)
        (eCap := eCap) (b := b) (L_buck := B (m - 1)) (i := m - 1) (e := e) hpP hpOps)
      (by eval_expr)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        have : b < 2 ^ w := by omega
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨by simp; rfl, hw16, hbound, hiL, heC, heB, hL, hvC, heCw, hdll, hdeg⟩ ?_
    rintro r mem₁ pos₁ ⟨_, _, hmin₁, hdll₁, hdeg₁, hfr₁⟩
    refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨hmin₁, fun i hi => ?_,
      fun e' he' hne' => ?_, fun addr h => ?_⟩
      (by simp [Expr.size, dsLevelsDeleteContract, hBucketRemoveContract])
    · show IsDoublyLinkedList mem₁ _ _ _ _ ((B i).erase e) ∧ mem₁ _ = ((B i).erase e).length
      by_cases hii : i = m - 1
      · subst hii
        refine ⟨hdll₁, ?_⟩
        rw [hdeg₁, List.length_erase_of_mem heB]
      · have heBi : e ∉ B i := hdisj (m - 1) hiL i hi (Ne.symm hii) e heB
        rw [List.erase_of_not_mem heBi]
        obtain ⟨hdlli, hdegi⟩ := hB i hi
        refine ⟨hdlli.of_agree ?_ (fun x hx => ?_) (fun x hx => ?_), ?_⟩
        · exact hfr₁ _ (by omega) (by omega) (by omega)
            (fun x h hx => by have := hdll.2.1 x hx; omega) (fun x h hx => by have := hdll.2.1 x hx; omega)
        · have hxi : x ∉ B (m - 1) := fun h => hdisj (m - 1) hiL i hi (Ne.symm hii) x h hx
          have hxC := hdlli.2.1 x hx
          exact hfr₁ _ (by omega) (by omega) (by omega)
            (fun y h => by have : y = x := by omega
                           subst this; exact hxi)
            (fun y h hy => by have := hdll.2.1 y hy; omega)
        · have hxi : x ∉ B (m - 1) := fun h => hdisj (m - 1) hiL i hi (Ne.symm hii) x h hx
          have hxC := hdlli.2.1 x hx
          exact hfr₁ _ (by omega) (by omega) (by omega)
            (fun y h hy => by have := hdll.2.1 y hy; omega)
            (fun y h => by have : y = x := by omega
                           subst this; exact hxi)
        · rw [hfr₁ _ (by omega) (by omega) (by omega) (fun x h hx => by have := hdll.2.1 x hx; omega) (fun x h hx => by have := hdll.2.1 x hx; omega)]
          exact hdegi
    · exact hfr₁ _ (by omega) (by omega) (by omega) (fun x h hx => by have := hdll.2.1 x hx; omega) (fun x h hx => by have := hdll.2.1 x hx; omega)
    · exact hfr₁ _ (by omega) (by omega) (by omega) (fun x h hx => by have := hdll.2.1 x hx; omega) (fun x h hx => by have := hdll.2.1 x hx; omega)
  · -- `e` is in no bucket.
    have hnone := hzero hz
    refine runs_seq_nop_le (runs_ret_le (v := 0) (Expr.eval_const (by omega))
      ⟨hz, fun i hi => ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
      (by simp [Expr.size, dsLevelsDeleteContract]))
    show IsDoublyLinkedList mem _ _ _ _ ((B i).erase e) ∧ mem _ = ((B i).erase e).length
    rw [List.erase_of_not_mem (hnone i hi)]
    exact hB i hi

end

end MinCostFlow.DynSpanner.Program
