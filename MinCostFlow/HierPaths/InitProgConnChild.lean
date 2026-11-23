module

public import MinCostFlow.HierPaths.InitProgConnIntervals

/-!
# Copying the endpoint column for one first child

The program computes the diagonal slot and the number of later siblings. A range call
then appends the endpoints of the matching with each later sibling.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The words copied for one first child. -/
def initChildEndpoints (S : StaticData) (field j g c : ℕ) : List ℕ :=
  (childList S.x S.b j g).flatMap (initPairEndpointWords S field j c)

/-- The arguments are the two exponents, depth, first child, number of children,
static connector table address, table row count, destination and field. -/
def initEndpointChild (range : ℕ) : Stmt :=
  .assign 9 (.reg 4) ;;
  .assign 4 (.reg 3) ;;
  .assign 10 initConnSlot ;;
  .call 11 range [.reg 5, .reg 6, .bin .add (.reg 10) (.const 1),
    .bin .add (.reg 10) (.bin .sub (.reg 9) (.bin .mod (.reg 3) (.reg 9))), .reg 7, .reg 8] ;;
  .ret (.reg 11)

theorem initEndpointChild_noRand (range : ℕ) : (initEndpointChild range).NoRand := by
  simp [initEndpointChild, Stmt.NoRand]

/-- The child procedure reads the static table and appends only its own matching columns. -/
def initEndpointChildContract (w : ℕ) (S : StaticData) (j g c : ℕ) : Contract where
  pre args mem := ∃ h dst field,
    args = [S.x, S.b, j, c, branching S.x S.b j, h + 7 + mem (h + 5),
      numPairsOf S.x S.b, dst, field] ∧
    StaticOut mem h S ∧ j < leafDepth S.x S.b ∧ g < numGroups S.x S.b j ∧
    c ∈ childGroups S.x S.b j g ∧ 1 < groupSize S.x S.b j ∧ field < 4 ∧
    h + S.encode.length ≤ dst ∧ dst + (initChildEndpoints S field j g c).length < 2 ^ w ∧
    1 < 2 ^ w
  post args mem v mem' := ∃ h dst field,
    args = [S.x, S.b, j, c, branching S.x S.b j, h + 7 + mem (h + 5),
      numPairsOf S.x S.b, dst, field] ∧
    v = dst + (initChildEndpoints S field j g c).length ∧
    ListAt mem' dst (initChildEndpoints S field j g c) ∧
    ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ :=
    let lo := firstChildSlotStart S.x S.b j g c
    let hi := firstChildSlotEnd S.x S.b j g c
    rangeCost (fun i => 60 * (staticConnMatching S i).length + 157) lo hi + 9 * (hi - lo) + 100

theorem initEndpointChild_meetsContract {w f range row seek count copy fill j g c : ℕ}
    {S : StaticData} {p : Program}
    (hp : p.procs[f]? = some (initEndpointChild range))
    (hR : p.procs[range]? = some (initEndpointRange row))
    (hrow : p.procs[row]? = some (initEndpointRow seek count copy fill))
    (hs : p.procs[seek]? = some initCSRSeek) (hc : p.procs[count]? = some initCSRCount)
    (hcopy : p.procs[copy]? = some initEndpointCopy)
    (hfill : p.procs[fill]? = some initFillWord) :
    MeetsContract w p f (initEndpointChildContract w S j g c) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h, dst, field, rfl, hout, hj, hg, hchild, hsz, hf, hsep, hroom, h1⟩ := hpre
  let lo := firstChildSlotStart S.x S.b j g c
  let hi := firstChildSlotEnd S.x S.b j g c
  let d := pairIdxOf S.x S.b j c c
  let br := branching S.x S.b j
  let src := h + 7 + mem (h + 5)
  let k := numPairsOf S.x S.b
  have he := endpointRangeWords_firstChild (field := field) S hg hchild hsz
  change endpointRangeWords _ _ lo hi field = initChildEndpoints S field j g c at he
  have hroom' := hroom
  rw [← he] at hroom'
  have hpre' := staticOut_endpointRange_pre hout hj hg hchild hsz hf hsep hroom' h1
  have hlo : lo ≤ hi := firstChildSlotStart_le_end hchild
  have hhi : hi ≤ k := firstChildSlotEnd_le S hj hg hchild hsz
  obtain ⟨hloEq, hhiEq⟩ := firstChildSlot_bounds_of_diag hsz hchild
  change lo = d + 1 at hloEq
  change hi = d + (br - c % br) at hhiEq
  have hkw : k < 2 ^ w := hw k (by simp [k])
  have hcw : c < 2 ^ w := hw c (by simp)
  have hbrw : br < 2 ^ w := hw br (by simp [br])
  have hlow := (hlo.trans hhi).trans_lt hkw
  have hhiw := hhi.trans_lt hkw
  have hcSmall := (childGroups_lt_numGroups hg hchild).trans_le (numGroups_le_pow (j + 1))
  refine runs_start_le ?_
  unfold initEndpointChild
  refine runs_seq_assign_le (v := br) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_assign_le (v := c) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_assign_le (v := d)
    (eval_initConnSlot rfl rfl rfl rfl rfl le_rfl hcSmall hcw hj hkw h1) ?_
  refine runs_seq_call_le (initEndpointRange_meetsContract (w := w) (k := k) (lo := lo) (hi := hi)
    (rows := staticConnRow S) (n := fun q => (staticConnMatching S q).length)
    (records := staticConnRecord S) hR hrow hs hc hcopy hfill)
    (vs := [src, k, lo, hi, dst, field]) ?_ ?_ hpre' ?_
  · have hmod := (Nat.mod_le c br).trans_lt hcw
    have hrem : br - c % br < 2 ^ w :=
      (Nat.sub_le _ _).trans_lt hbrw
    simp [evalArgs, Expr.eval, startState, BinOp.eval, src, k, h1, ← hloEq, ← hhiEq,
      hlow, hhiw, hmod, hrem]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw _ (by simp [src])
    · exact hkw
    · exact hlow
    · exact hhiw
    · exact hw _ (by simp)
    · exact hw _ (by simp)
  intro v mem' pos' hpost
  obtain ⟨src', dst', field', hargs, hv, hwords, hfr⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨_, _, _, _, hdst, hfield⟩ := hargs
  subst dst' field'
  rw [he] at hv hwords
  refine runs_ret_le (v := v) (by simp [Expr.eval]) ⟨h, dst, field, rfl, hv, hwords, hfr⟩ ?_
  simp [initEndpointRangeContract, initEndpointChildContract, argsSize, Expr.size, initConnSlot,
    lo, hi]
  omega

end MinCostFlow.HierPaths

end
