module

public import MinCostFlow.HierPaths.InitProgConnDepth
public import MinCostFlow.HierPaths.InitBuildProc
public import MinCostFlow.HierPaths.InitHeader

/-!
# Endpoint sections of the initialized data structure

Read the static header, find its connector table, and write the requested column.
The same writer supplies the two endpoint columns and the column of designated endpoints.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

def connTableExpr : Expr :=
  .bin .add (.bin .add (.reg 4) (.const 7))
    (.load (.bin .add (.reg 4) (.const 5)))

/-- The entry of an endpoint section writer. -/
def initEndpointWriter (field depth : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 4) (.const 7))) ;;
  .assign 8 (.load (.bin .add (.reg 4) (.const 8))) ;;
  .assign 9 depthExpr ;;
  .assign 10 connTableExpr ;;
  .assign 11 numPairsExpr ;;
  .assign 12 (.bin .shiftLeft (.const 1) (.reg 7)) ;;
  .call 13 depth [.reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 6, .const field, .reg 12] ;;
  .ret (.reg 13)

def initEndpointSectionCost (S : StaticData) : ℕ :=
  (initEndpointDepthContract 0 S).cost [] (fun _ => 0) + 100

/-- The endpoint entry meets the block builder's section contract. -/
theorem initEndpointWriter_meetsContract {w a f field depth level child range row seek count copy fill : ℕ}
    {S : StaticData} {G : Graph} {p : Program} (hf : field < 4)
    (hp : p.procs[f]? = some (initEndpointWriter field depth))
    (hDepth : p.procs[depth]? = some (initEndpointDepth level))
    (hLevel : p.procs[level]? = some (initEndpointLevel child))
    (hChild : p.procs[child]? = some (initEndpointChild range))
    (hR : p.procs[range]? = some (initEndpointRange row))
    (hrow : p.procs[row]? = some (initEndpointRow seek count copy fill))
    (hs : p.procs[seek]? = some initCSRSeek) (hc : p.procs[count]? = some initCSRCount)
    (hcopy : p.procs[copy]? = some initEndpointCopy)
    (hfill : p.procs[fill]? = some initFillWord) :
    MeetsContract w p f (SecContract w (buildInv w S a G)
      ⟨f, fun _ => initEndpointWords S field, fun _ => initEndpointSectionCost S, fun _ => 0⟩) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, dst, rfl, _, hI, hzero, hdst, hroom⟩ := hpre
  have ⟨h', hh', hx, hb, hh8, hxw, hb0, hkw⟩ := header_facts hI hw
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hS, hlen, _, _, _, _, hgood, _, hxi, _⟩ := hI
  change h = _ at hh'
  subst h'
  change h₁ + 25 ≤ dst at hdst
  change dst + (initEndpointWords S field).length < 2 ^ w at hroom
  have hsep : h + S.encode.length ≤ dst := by omega
  obtain ⟨_, _, henc⟩ := staticOut_owner_facts hS
  let k := numPairsOf S.x S.b
  let src := h + 7 + mem (h + 5)
  let D := leafDepth S.x S.b
  have hPw : 2 ^ S.x < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hfw : field < 2 ^ w := by omega
  have hsw : src < 2 ^ w := by
    have h := (hS.section_end_le (i := 5) (by decide)).trans hsep
    change src + _ ≤ dst at h
    omega
  have hDw : D < 2 ^ w := by
    have hP := Nat.le_mul_of_pos_right (D * 2 ^ S.x) (Nat.two_pow_pos S.b)
    have hD := Nat.le_mul_of_pos_right D (Nat.two_pow_pos S.x)
    exact (hD.trans hP).trans_lt hkw
  have hbw : S.b < 2 ^ w := by
    have hpos : 0 < depthOf G.m := (by decide : 0 < 2).trans_le (two_le_depthOf _)
    have hB : branchOf G.m ≤ branchOf G.m ^ 2 := Nat.le_self_pow (by decide) _
    have hh : branchOf G.m ^ 2 ≤ depthOf G.m * branchOf G.m ^ 2 :=
      Nat.le_mul_of_pos_left _ hpos
    have hl := Nat.le_mul_of_pos_right (depthOf G.m * branchOf G.m ^ 2)
      (one_le_lamOf a (dOf phiNum phiDen) G.m)
    exact Nat.lt_two_pow_self.trans ((hgood.branch.trans (hB.trans (hh.trans hl))).trans_lt hxi)
  refine runs_start_le ?_
  unfold initEndpointWriter
  refine runs_seq_assign_le (v := S.x) (eval_xExpr rfl hx hh8) ?_
  refine runs_seq_assign_le (v := S.b) (eval_bExpr rfl hb hh8) ?_
  refine runs_seq_assign_le (v := D) (eval_depthExpr rfl hx hb hh8 hxw hb0) ?_
  refine runs_seq_assign_le (v := src) ?_ ?_
  · unfold connTableExpr
    exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
        (Expr.eval_const (by omega)) (by omega))) hsw
  refine runs_seq_assign_le (v := k) (eval_numPairsExpr rfl hx hb hh8 hxw hb0 hkw) ?_
  refine runs_seq_assign_le (v := 2 ^ S.x) ?_ ?_
  · have hsh : (1 : ℕ) <<< S.x = 2 ^ S.x := by simp [Nat.shiftLeft_eq]
    exact Expr.eval_eq_of_eq (Expr.eval_shiftLeft (Expr.eval_const h1w)
      (Expr.eval_reg_of_eq (by simp)) (hsh ▸ hPw)) hsh
  refine runs_seq_call_le (initEndpointDepth_meetsContract hDepth hLevel hChild hR hrow hs hc hcopy hfill)
    (vs := [S.x, S.b, D, src, k, dst, field, 2 ^ S.x]) ?_ ?_
    ⟨h, dst, field, rfl, hS, hb0, hf, hsep, hroom, h1w⟩ ?_
  · simp [evalArgs, Expr.eval, startState, hfw]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hxw
    · exact hbw
    · exact hDw
    · exact hsw
    · exact hkw
    · omega
    · exact hfw
    · exact hPw
  intro v mem' pos' hpost
  obtain ⟨h', dst', field', ha, hv, hwords, hfr⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, hd, hfield, _⟩ := ha
  try subst dst'
  try subst field'
  refine runs_ret_le (v := v) (by simp [Expr.eval]) ⟨_, dst, rfl, hv, hwords, ?_, ?_⟩ ?_
  · intro y hy
    change v ≤ y at hy
    exact (hfr y (Or.inr hy)).trans (hzero y (by omega))
  · intro y hy
    exact hfr y (Or.inl hy)
  · simp [SecContract, initEndpointSectionCost, initEndpointDepthContract, connTableExpr, depthExpr,
      numPairsExpr, argsSize, Expr.size]
    omega

/-- The nine helper procedures, starting at `k`. -/
def endpointHelpers (k : ℕ) : List Stmt :=
  [initEndpointDepth (k + 1), initEndpointLevel (k + 2), initEndpointChild (k + 3),
    initEndpointRange (k + 4), initEndpointRow (k + 5) (k + 6) (k + 7) (k + 8),
    initCSRSeek, initCSRCount, initEndpointCopy, initFillWord]

/-- A relocatable writer for one endpoint column. -/
def endpointW (a field : ℕ) (hf : field < 4) : SecW a where
  body k := initEndpointWriter field k
  helpers := endpointHelpers
  l S _ _ := initEndpointWords S field
  cost S _ _ := initEndpointSectionCost S
  noRand k := ⟨by simp [initEndpointWriter, Stmt.NoRand], by
    simp [endpointHelpers, initEndpointDepth_noRand, initEndpointLevel_noRand,
      initEndpointChild_noRand, initEndpointRange_noRand, initEndpointRow_noRand,
      initCSRSeek_noRand, initCSRCount_noRand, initEndpointCopy_noRand, initFillWord_noRand]⟩
  spec w p f k hp hh S G :=
    initEndpointWriter_meetsContract hf hp (by simpa [endpointHelpers] using hh 0 (by simp [endpointHelpers]))
      (hh 1 (by simp [endpointHelpers])) (hh 2 (by simp [endpointHelpers])) (hh 3 (by simp [endpointHelpers]))
      (hh 4 (by simp [endpointHelpers])) (hh 5 (by simp [endpointHelpers])) (hh 6 (by simp [endpointHelpers])) (hh 7 (by simp [endpointHelpers])) (hh 8 (by simp [endpointHelpers]))

/-- Endpoints and designated endpoints are sections 2, 3 and 4. -/
def endpointWriters (a : ℕ) : List (SecW a) :=
  [endpointW a 0 (by decide), endpointW a 1 (by decide), endpointW a 0 (by decide)]

theorem endpointWriters_sections (S : StaticData) (a : ℕ) (G : Graph)
    (s : PathDSAbsState) (base : List ℕ) :
    (endpointWriters a).map (fun W => W.l S G base) =
      ((initConcrete S a s).sections.drop 2).take 3 := by
  obtain ⟨h2, h3, h4⟩ := initEndpointWords_sections S a s
  change [initEndpointWords S 0, initEndpointWords S 1, initEndpointWords S 0] =
    [(initConcrete S a s).sections.getD 2 [], (initConcrete S a s).sections.getD 3 [],
      (initConcrete S a s).sections.getD 4 []]
  rw [h2, h3, h4]

/-- The connector-to-pair column is section 5. -/
def connectorPairW (a : ℕ) : SecW a := endpointW a 2 (by decide)

theorem connectorPairW_section (S : StaticData) (a : ℕ) (G : Graph)
    (s : PathDSAbsState) (base : List ℕ) :
    (connectorPairW a).l S G base = (initConcrete S a s).sections.getD 5 [] :=
  (initEndpointWords_section_pair S a s).symm

end MinCostFlow.HierPaths

end
