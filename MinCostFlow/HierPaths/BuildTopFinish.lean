module

public import MinCostFlow.HierPaths.BuildTopRows
public import MinCostFlow.HierPaths.BuildTopPack
public import MinCostFlow.HierPaths.InitProgMove

/-!
# Finishing the static output

After the six section bodies are available, the procedure gathers them
into their final directory and moves the block to the original handle.
Its clearing cost accounts for the whole occupied interval.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the section directory, the scratch tail, and the final handle. -/
def buildTopFinish (gather move : ℕ) : Stmt :=
  .call 3 gather [.reg 0, .const 6, .reg 1] ;;
  .call 4 move [.reg 2, .reg 1, .reg 3] ;;
  .ret (.reg 4)

theorem buildTopFinish_noRand (gather move : ℕ) : (buildTopFinish gather move).NoRand := by
  simp [buildTopFinish, Stmt.NoRand]

def buildTopGatherCost (S : StaticData) : ℕ :=
  rangeCost (fun i => 17 * (buildTopSections S i).length + 70) 0 6 + 30 * 6 + 40

/-- The final copy moves the packed static output to `h` and returns the bump end
`tail + S.encode.length` in time linear in `S.encode.length` (no gap zeroing). -/
def buildTopFinishContract (w : ℕ) (S : StaticData) (src : ℕ → ℕ) : Contract where
  pre args mem := ∃ ctx tail h, args = [ctx, tail, h] ∧ h ≤ tail ∧
    buildTopRowDir ctx 6 (buildTopSections S) src tail mem ∧ ZeroFrom mem tail ∧
    tail + S.encode.length < 2 ^ w ∧ 6 < 2 ^ w
  post args mem r mem' := ∃ ctx tail h, args = [ctx, tail, h] ∧
    h + S.encode.length ≤ r ∧ r ≤ tail + S.encode.length ∧
    StaticOut mem' h S ∧ ZeroFrom mem' r ∧ ∀ x < h, mem' x = mem x
  cost _ _ := buildTopGatherCost S + 17 * S.encode.length + 75

theorem buildTopFinish_meetsContract {w f g move row copy : ℕ} {S : StaticData}
    {src : ℕ → ℕ} {p : Program} (hp : p.procs[f]? = some (buildTopFinish g move))
    (hg : p.procs[g]? = some (initCSRWrite row))
    (hr : p.procs[row]? = some (buildTopRow copy))
    (hc : p.procs[copy]? = some buildCopyProc)
    (hm : p.procs[move]? = some copyDown) :
    MeetsContract w p f (buildTopFinishContract w S src) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ctx, tail, h, rfl, hle, hdir, hzero, hroom, h6⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  let C := buildTopGather_meetsContract (w := w) (rows := buildTopSections S) (src := src)
    (ctx := ctx) (k := 6) hg hr hc
  refine runs_start_le ?_
  unfold buildTopFinish
  refine runs_seq_call_le C (vs := [ctx, 6, tail]) ?_ ?_
    ⟨tail, rfl, hdir, hzero, by simpa [buildTopSections_encode] using hroom, h1⟩ ?_
  · simp [evalArgs, Expr.eval, startState, h6]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact h6
    · exact hw _ (by simp)
  intro r mem₁ pos₁ hpost
  obtain ⟨tail', ha, hr', hout, hz, hframe⟩ := hpost
  simp only [List.cons.injEq, and_true, true_and] at ha
  subst tail'
  rw [buildTopSections_encode] at hr' hout
  refine runs_seq_call_le (copyDown_meetsContract hm) (vs := [h, tail, r]) rfl ?_
    ⟨h, tail, r, rfl, hle, by omega, by omega, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  intro r' mem₂ pos₂ hpost
  obtain ⟨h', tail', e, ha, he, hdata, hfr, hhigh⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _⟩ := ha
  subst h' tail' e
  have hsub : r - tail = S.encode.length := by omega
  refine runs_ret_le (v := r') (Expr.eval_reg_of_eq rfl)
    ⟨ctx, tail, h, rfl, by change h + S.encode.length ≤ r'; omega,
      by change r' ≤ tail + S.encode.length; omega, ?_, ?_, ?_⟩ ?_
  · change ListAt mem₂ h S.encode
    intro i hi'
    exact (hdata i (by omega)).trans (hout i hi')
  · intro y hy
    change r' ≤ y at hy
    exact (hhigh y (by omega)).trans (hz y (by omega))
  · intro y hy
    exact (hfr y hy).trans (hframe y (hy.trans_le hle))
  · simp [buildTopFinishContract, initCSRWriteContract, buildTopGatherCost, copyDownContract,
      Expr.size, argsSize, hr']
    omega

/-- Packing and copying take time linear in the static output length. -/
theorem buildTopFinish_cost_le (w ctx tail h : ℕ) (S : StaticData) (src : ℕ → ℕ)
    (mem : ℕ → ℕ) :
    (buildTopFinishContract w S src).cost [ctx, tail, h] mem ≤
      34 * S.encode.length + 715 := by
  have hEnc : S.encode.length = 7 + (csrData 6 (buildTopSections S)).length := by
    rw [← buildTopSections_encode, csrList, List.length_append, length_csrOffsets]
  have hSum (xs : List ℕ) :
      (xs.map (fun i => 17 * (buildTopSections S i).length + 70)).sum =
        17 * (xs.flatMap (buildTopSections S)).length + 70 * xs.length := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp [List.flatMap_cons, ih, Nat.mul_add]
      omega
  simp only [buildTopFinishContract, buildTopGatherCost,
    rangeCost_zero_eq_range, hSum, List.length_range]
  change 17 * (csrData 6 (buildTopSections S)).length + 70 * 6 + 30 * 6 + 40 +
    17 * S.encode.length + 75 ≤ _
  omega

end MinCostFlow.HierPaths

end
