module

public import MinCostFlow.MinRatio.QueryDetectPost
import WordRAM.Tactic

/-!
# Query from a resolved edge record

Section 6 (pages 29–30) uses dynamic trees to maintain flow. After a
point read exposes the edge value, the Query procedure reads its
direction bit and finds the flow block in its payload. It then writes
the single scalar in the edge's original direction.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are the edge record, block length, and output heap. -/
def queryResolvedBody (writeOutput : ℕ) : Stmt :=
  .call 3 writeOutput
    [.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 1)),
     .load (.bin .add (.reg 0) (.const 1)), .reg 1, .reg 2] ;;
  .ret (.reg 3)

/-- Read the exact original-direction flow from a resolved edge record. -/
noncomputable def queryResolvedContract (w h P : ℕ) (value : PathEdgeValue) : Contract where
  pre args mem := ∃ a L heap,
    args = [a, L, heap] ∧ 2 < 2 ^ w ∧ a + 2 + 4 * L ≤ heap ∧
      PathEdgeAt mem a h L (some value) ∧ Num.Fits h L value.originalFlow ∧
      ZeroFrom mem heap ∧ heap + L < 2 ^ w
  post args mem ret mem' :=
    ret = heapArg args + args.getD 1 0 ∧
    ScalarAt mem' (heapArg args) h (args.getD 1 0) P
      ((value.originalFlow : ℝ) / (2 : ℝ) ^ P) ∧
    (∀ x < heapArg args, mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 36 * args.getD 1 0 + 48

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- With the output routine linked, reading a resolved edge takes at most
`36 * L + 48` instructions and allocates exactly `L` words. -/
theorem queryResolved_meetsContract {w h P entry writeOutput : ℕ} {p : Program}
    (value : PathEdgeValue) (hp : p.HasAt entry [queryResolvedBody writeOutput])
    (hwrite : MeetsContract w p writeOutput (queryOutputContract w h P)) :
    MeetsContract w p entry (queryResolvedContract w h P value) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, L, heap, rfl, hw, hspace, hedge, hfit, hz, hroom⟩ := hpre
  have hsrc : a + 2 + 2 * L + L ≤ heap := by omega
  have hsrcWord : a + 2 + 2 * L < 2 ^ w := by omega
  have hdirAddr : a + 1 < 2 ^ w := by omega
  have haddr : a + 2 < 2 ^ w := by omega
  have hdouble : 2 * L < 2 ^ w := by omega
  let direction : ℕ := if value.forward then 1 else 0
  have hdir : mem (a + 1) = direction := hedge.2.1
  have hdirWord : direction < 2 ^ w := by
    change (if value.forward then 1 else 0 : ℕ) < 2 ^ w
    split <;> omega
  have hLWord := hwords L (by simp)
  have hheapWord := hwords heap (by simp)
  have hwargs : ∀ v ∈ [a + 2 + 2 * L, direction, L, heap], v < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hsrcWord, hdirWord, hLWord, hheapWord⟩
  have hcall := queryOutput_pre_of_pathEdge (P := P) hedge hfit hsrc hz hroom
  apply runs_start_le
  unfold queryResolvedBody
  refine runs_seq_call_le hwrite (vs := [a + 2 + 2 * L, direction, L, heap])
    (by eval_expr) hwargs hcall ?_
  intro ret mem' pos' hpost
  obtain ⟨hret, _, _, hframe, hzero, hval⟩ := hpost
  refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
  · refine ⟨hret, ?_, hframe, hzero⟩
    have hflow := hedge.2.2.2.2.1.2
    change ScalarAt mem' heap h L P
        (if direction = 0 then -Num.fixVal mem (a + 2 + 2 * L) h L P
          else Num.fixVal mem (a + 2 + 2 * L) h L P) at hval
    change ScalarAt mem' heap h L P ((value.originalFlow : ℝ) / (2 : ℝ) ^ P)
    cases hd : value.forward <;>
      simpa [direction, hd, PathEdgeValue.originalFlow, Num.fixVal, hflow,
        Int.cast_neg, neg_div] using hval
  · simp only [queryOutputContract, queryResolvedContract, heapContract,
      List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin, Expr.size_load, Expr.size_reg,
      Expr.size_const, argsSize_cons, argsSize_nil]
    omega

/-- A resolved edge with the modeled flow gives the actual Query
postcondition of Definition 4.5 (page 14). -/
theorem queryResolved_minRatio_post {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {m handle heap edge address ret : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {s : (algorithm2_dsWithFailure cfg).State} {mem mem' : ℕ → ℕ} {value : PathEdgeValue}
    (hflow : (value.originalFlow : ℝ) / (2 : ℝ) ^ F.fmt.precision =
      algorithm2_query cfg s edge)
    (hout : (queryResolvedContract w F.fmt.limbBits F.fmt.precision value).post
      [address, F.limbs, heap] mem ret mem') :
    (minRatioMachineContract F (algorithm2_dsWithFailure cfg) G m κ α rate allocation).post
      1 s [handle, edge, heap] mem s mem' := by
  refine ⟨rfl, ?_⟩
  have hscalar := hout.2.1
  change ScalarAt mem' heap F.fmt.limbBits F.limbs F.fmt.precision
    ((value.originalFlow : ℝ) / (2 : ℝ) ^ F.fmt.precision) at hscalar
  rw [hflow] at hscalar
  exact hscalar

end MinCostFlow.MinRatio
