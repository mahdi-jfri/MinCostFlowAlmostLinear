module

public import MinCostFlow.HierPaths.InitProgPairTableRow
public import MinCostFlow.HierPaths.InitProgCSRWrite
public import MinCostFlow.HierPaths.InitHeader
public import MinCostFlow.HierPaths.InitBuildProc

/-!
# Section 12 of the initialized hierarchy

The depth rows give each child direct access to the pair number of any
sibling. The section entry writes these rows with their offsets.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The pair index table with its row offsets. -/
def initPairTable (S : StaticData) : List ℕ :=
  csrList (leafDepth S.x S.b) (initPairTableRow S.x S.b)

theorem initPairTable_section (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 12 [] = initPairTable S := rfl

/-- The row takes the static block address, depth and destination. -/
def initPairDepthRow (row : ℕ) : Stmt :=
  .assign 4 (.reg 0) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.const 7))) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.const 8))) ;;
  .assign 7 (.bin .shiftLeft (.const 1) (.reg 5)) ;;
  .assign 8 (.bin .shiftLeft (.const 1) (.reg 6)) ;;
  .assign 9 (queryGroupSizeExpr (.reg 5) (.reg 6) (.reg 1)) ;;
  .assign 10 (queryGroupSizeExpr (.reg 5) (.reg 6) (.bin .add (.reg 1) (.const 1))) ;;
  .assign 11 (.bin .div (.reg 9) (.reg 10)) ;;
  .assign 12 (.bin .mul (.bin .div (.reg 7) (.reg 10)) (.reg 11)) ;;
  .call 13 row [.reg 2, .reg 12, .reg 1, .reg 7, .reg 8, .reg 11] ;;
  .ret (.reg 13)

theorem initPairDepthRow_noRand (row : ℕ) : (initPairDepthRow row).NoRand := by
  simp [initPairDepthRow, Stmt.NoRand]

def initPairTableInv (w h : ℕ) (S : StaticData) (dst : ℕ) (mem : ℕ → ℕ) : Prop :=
  StaticOut mem h S ∧ h + S.encode.length ≤ dst ∧ 0 < S.b ∧ numPairsOf S.x S.b < 2 ^ w

def initPairDepthCost (S : StaticData) (j : ℕ) : ℕ :=
  70 * (initPairTableRow S.x S.b j).length + 150

theorem initPairDepthRow_meetsContract {w f row h j : ℕ} {S : StaticData} {p : Program}
    (hj : j < leafDepth S.x S.b)
    (hp : p.procs[f]? = some (initPairDepthRow row))
    (hRow : p.procs[row]? = some initPairTableRowProc) :
    MeetsContract w p f (initCSRWriteRowContract h j (initPairTableRow S.x S.b j)
      (fun addr mem => ∃ dst, initPairTableInv w h S dst mem ∧
        dst + leafDepth S.x S.b + 1 ≤ addr ∧
        addr + (initPairTableRow S.x S.b j).length + 0 < 2 ^ w)
      (initPairDepthCost S j)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨addr, rfl, ⟨dst, ⟨hS, hsep, hb0, hk⟩, haddr, hroom⟩, hz⟩ := hpre
  obtain ⟨hx, _, hlen⟩ := staticOut_owner_facts hS
  have hb := staticOut_b hS
  let P := 2 ^ S.x
  let B := 2 ^ S.b
  let sz := groupSize S.x S.b j
  let sz' := groupSize S.x S.b (j + 1)
  let br := branching S.x S.b j
  let n := (initPairTableRow S.x S.b j).length
  have h1 : 1 < 2 ^ w := by omega
  have hh8 : h + 8 < 2 ^ w := by
    have hEnc : 8 ≤ S.encode.length := (show 8 ≤ 10 by decide).trans ((Nat.le_add_right 10 (2 ^ S.x)).trans hlen)
    have hd : dst ≤ addr := (Nat.le_add_right dst _).trans
      ((Nat.le_add_right _ 1).trans haddr)
    have ha : addr < 2 ^ w := lt_of_le_of_lt
      ((Nat.le_add_right addr _).trans (Nat.le_add_right _ 0)) hroom
    exact lt_of_le_of_lt ((Nat.add_le_add_left hEnc h).trans (hsep.trans hd)) ha
  have hPB : P * B ≤ numPairsOf S.x S.b := by
    unfold numPairsOf
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt hj))
  have hP : P < 2 ^ w := ((Nat.le_mul_of_pos_right P (Nat.two_pow_pos S.b)).trans hPB).trans_lt hk
  have hB : B < 2 ^ w := ((Nat.le_mul_of_pos_left B (Nat.two_pow_pos S.x)).trans hPB).trans_lt hk
  have hbw : S.b < 2 ^ w := Nat.lt_two_pow_self.trans hB
  have hsz : sz < 2 ^ w := (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans_lt hP
  have hsz' : sz' < 2 ^ w := (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans_lt hP
  have hj1 : j + 1 < 2 ^ w := by omega
  have hbr : br < 2 ^ w := (Nat.div_le_self sz sz').trans_lt hsz
  have hnum : P / sz' * br = n := by
    rw [initNumGroups_div_groupSize]
    simp [n, initPairTableRow, br]
  have hn : n < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold initPairDepthRow
  refine runs_seq_assign_le (v := h) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_assign_le (v := S.x) (eval_xExpr rfl hx hh8) ?_
  refine runs_seq_assign_le (v := S.b) (eval_bExpr rfl hb hh8) ?_
  refine runs_seq_assign_le (v := P) ?_ ?_
  · simpa [P, Nat.shiftLeft_eq] using
      (Expr.eval_shiftLeft (Expr.eval_const (w := w) h1) (Expr.eval_reg_of_eq (v := S.x) rfl)
        (by simpa [Nat.shiftLeft_eq] using hP))
  refine runs_seq_assign_le (v := B) ?_ ?_
  · simpa [B, Nat.shiftLeft_eq] using
      (Expr.eval_shiftLeft (Expr.eval_const (w := w) h1) (Expr.eval_reg_of_eq (v := S.b) rfl)
        (by simpa [Nat.shiftLeft_eq] using hB))
  refine runs_seq_assign_le (v := sz) (eval_queryGroupSizeExpr (Expr.eval_reg_of_eq rfl)
    (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hP
    (queryDepth_mul_lt hb0 hj.le hP hbw)) ?_
  refine runs_seq_assign_le (v := sz') (eval_queryGroupSizeExpr (Expr.eval_reg_of_eq rfl)
    (Expr.eval_reg_of_eq rfl) (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hj1)
    hP (queryDepth_mul_lt hb0 hj hP hbw)) ?_
  refine runs_seq_assign_le (v := br)
    (Expr.eval_div (Expr.eval_reg_of_eq (v := sz) rfl) (Expr.eval_reg_of_eq (v := sz') rfl) hsz) ?_
  refine runs_seq_assign_le (v := n) (Expr.eval_eq_of_eq
    (Expr.eval_mul (Expr.eval_div (Expr.eval_reg_of_eq (v := P) rfl)
      (Expr.eval_reg_of_eq (v := sz') rfl) hP) (Expr.eval_reg_of_eq (v := br) rfl)
      (hnum ▸ hn)) hnum) ?_
  refine runs_seq_call_le (initPairTableRowProc_meetsContract (w := w) (x := S.x) (b := S.b)
    (j := j) hRow) (vs := [addr, n, j, P, B, br]) rfl ?_
    ⟨addr, rfl, hj, hk, hroom, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | exact hw _ (by simp)
  intro r mem' pos' hp'
  obtain ⟨addr', hargs, hr, hwords, hf⟩ := hp'
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨ha, _⟩ := hargs
  subst addr'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨addr, rfl, hr, hwords, ?_, fun y hy => hf y (.inl hy)⟩ ?_
  · intro y hy
    change r ≤ y at hy
    exact (hf y (.inr hy)).trans (hz y (by omega))
  · simp [initPairTableRowContract, initCSRWriteRowContract, initPairDepthCost,
      queryGroupSizeExpr, Expr.size, argsSize]
    omega

/-- Load the depth count and write the pair index table as compressed rows. -/
def initPairTableWriter (write : ℕ) : Stmt :=
  .assign 7 depthExpr ;;
  .call 8 write [.reg 4, .reg 7, .reg 6] ;;
  .ret (.reg 8)

def initPairTableCost (S : StaticData) : ℕ :=
  rangeCost (initPairDepthCost S) 0 (leafDepth S.x S.b) + 30 * leafDepth S.x S.b + 100

theorem initPairTableWriter_meetsContract {w a f write row baseRow : ℕ}
    {S : StaticData} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (initPairTableWriter write))
    (hW : p.procs[write]? = some (initCSRWrite row))
    (hR : p.procs[row]? = some (initPairDepthRow baseRow))
    (hBase : p.procs[baseRow]? = some initPairTableRowProc) :
    MeetsContract w p f (SecContract w (buildInv w S a G)
      ⟨f, fun _ => initPairTable S, fun _ => initPairTableCost S, fun _ => 0⟩) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, dst, rfl, _, hI, hzero, hdst, hroom⟩ := hpre
  have ⟨h', hh', hx, hb, hh8, hxw, hb0, hkw⟩ := header_facts hI hw
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hS, hlen, _, _, _, _, _, _, _, _⟩ := hI
  change h = h' at hh'
  subst h'
  let base := [gAddr, phiNum, phiDen, M, h, h₁]
  let D := leafDepth S.x S.b
  have hDw : D < 2 ^ w := by
    apply lt_of_le_of_lt _ hkw
    unfold numPairsOf
    exact (Nat.le_mul_of_pos_right D (Nat.two_pow_pos S.x)).trans
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos S.b))
  have hsep : h + S.encode.length ≤ dst := by
    change h₁ + 25 ≤ dst at hdst
    omega
  have h1 : 1 < 2 ^ w := by omega
  have hStable (b : ℕ) (mem mem' : ℕ → ℕ) (hInv : initPairTableInv w h S b mem)
      (hf : ∀ y < b, mem' y = mem y) : initPairTableInv w h S b mem' := by
    obtain ⟨hdata, hsep, hb, hk⟩ := hInv
    exact ⟨listAt_congr (fun i hi => (hf _ (by omega)).symm) hdata, hsep, hb, hk⟩
  have hwrite := initCSRWrite_meetsContract (w := w) (ctx := h) (k := D) (scratch := 0)
    (rows := initPairTableRow S.x S.b) (cost := initPairDepthCost S) hW
    (fun _ hi => initPairDepthRow_meetsContract hi hR hBase) hStable
  refine runs_start_le ?_
  unfold initPairTableWriter
  refine runs_seq_assign_le (v := D) (eval_depthExpr rfl hx hb hh8 hxw hb0) ?_
  refine runs_seq_call_le hwrite (vs := [h, D, dst]) rfl ?_
    ⟨dst, rfl, ⟨hS, hsep, hb0, hkw⟩, hzero, hroom, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hDw
    · exact hw _ (by simp)
  intro r mem' pos' hp'
  obtain ⟨dst', ha, hr, hmem, hz, hf⟩ := hp'
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, ha⟩ := ha
  subst dst'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨base, dst, rfl, hr, hmem, hz, hf⟩ ?_
  simp [SecContract, initCSRWriteContract, initPairTableCost, depthExpr, Expr.size, argsSize, D]
  omega

/-- The relocatable writer for section 12. -/
def pairTableW (a : ℕ) : SecW a where
  body k := initPairTableWriter k
  helpers k := [initCSRWrite (k + 1), initPairDepthRow (k + 2), initPairTableRowProc]
  l S _ _ := initPairTable S
  cost S _ _ := initPairTableCost S
  noRand k := ⟨by simp [initPairTableWriter, Stmt.NoRand], by
    simp [initCSRWrite_noRand, initPairDepthRow_noRand, initPairTableRowProc_noRand]⟩
  spec _ _ _ _ hp hh _ _ := initPairTableWriter_meetsContract hp
    (by simpa using hh 0 (by simp)) (hh 1 (by simp)) (hh 2 (by simp))

/-- The table writer uses at most a fixed amount of work per output word. -/
theorem initPairTableCost_le (S : StaticData) :
    initPairTableCost S ≤ 180 * (initPairTable S).length + 100 := by
  let D := leafDepth S.x S.b
  let f := initPairTableRow S.x S.b
  have hlen : (initPairTable S).length = D + 1 + (csrData D f).length := by
    simp [initPairTable, csrList, D, f]
  have hsum : rangeCost (initPairDepthCost S) 0 D =
      70 * (csrData D f).length + 150 * D := by
    unfold initPairDepthCost
    rw [rangeCost_add, rangeCost_const, rangeCost_zero_eq_range]
    simp only [Nat.sub_zero, Nat.mul_comm 150]
    have he (l : List ℕ) : (l.map fun j => 70 * (f j).length).sum =
        70 * (l.flatMap f).length := by
      induction l with
      | nil => simp
      | cons j l ih => simp [ih, Nat.mul_add]
    rw [he]
    rfl
  unfold initPairTableCost
  change rangeCost (initPairDepthCost S) 0 D + 30 * D + 100 ≤ _
  rw [hsum, hlen]
  omega

end MinCostFlow.HierPaths

end
