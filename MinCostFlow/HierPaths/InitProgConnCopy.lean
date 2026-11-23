module

public import MinCostFlow.HierPaths.InitProgConnEndpoints
public import MinCostFlow.HierPaths.InitProgFillWord

/-!
# Reading an endpoint column from the static connector table

Two offset lookups find the bounds of the selected row. Its offset count gives the number
of connectors, and the column scan appends their endpoints to the output. No work is charged
for the edge numbers at the ends of the records.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the table address, number of rows, selected row, destination and field. -/
def initEndpointRow (seek count copy fill : ℕ) : Stmt :=
  .call 5 seek [.reg 0, .reg 1, .reg 2] ;;
  .call 6 seek [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1)] ;;
  .call 7 count [.reg 5, .bin .sub (.reg 6) (.reg 5)] ;;
  .cond (.bin .eq (.reg 4) (.const 2))
    (.call 8 fill [.reg 3, .reg 7, .reg 2] ;; .ret (.reg 8))
    (.call 8 copy [.reg 5, .reg 7, .reg 3, .reg 4] ;; .ret (.reg 8))

theorem initEndpointRow_noRand (seek count copy fill : ℕ) : (initEndpointRow seek count copy fill).NoRand := by
  simp [initEndpointRow, Stmt.NoRand]

/-- A row contributes either its pair number or the selected endpoint of each connector. -/
def initConnectorColumn (idx field n : ℕ) (records : ℕ → List ℕ) : List ℕ :=
  if field = 2 then List.replicate n idx else tabList n (initEndpointValue field records)

theorem initConnectorColumn_length (idx field n : ℕ) (records : ℕ → List ℕ) :
    (initConnectorColumn idx field n records).length = n := by
  unfold initConnectorColumn
  split <;> simp

/-- Copy an endpoint column from one row of a compressed table of connector rows. -/
def initEndpointRowContract (w k idx n : ℕ) (rows records : ℕ → List ℕ) : Contract where
  pre args mem := ∃ addr dst field, args = [addr, k, idx, dst, field] ∧ idx < k ∧
    rows idx = csrList n records ∧ ListAt mem addr (csrList k rows) ∧
    (field = 2 ∨ field = 3 ∨ ∀ i < n, field < (records i).length) ∧ addr + (csrList k rows).length ≤ dst ∧
    dst + n < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ addr dst field, args = [addr, k, idx, dst, field] ∧ v = dst + n ∧
    ListAt mem' dst (initConnectorColumn idx field n records) ∧
    ∀ y, y < dst ∨ dst + n ≤ y → mem' y = mem y
  cost _ _ := 60 * n + 150

/-- One endpoint row is appended in time linear in its number of connectors. -/
theorem initEndpointRow_meetsContract {w k idx n j seek count copy fill : ℕ} {rows records : ℕ → List ℕ}
    {p : Program} (hp : p.procs[j]? = some (initEndpointRow seek count copy fill))
    (hs : p.procs[seek]? = some initCSRSeek) (hc : p.procs[count]? = some initCSRCount)
    (hcopy : p.procs[copy]? = some initEndpointCopy)
    (hfill : p.procs[fill]? = some initFillWord) :
    MeetsContract w p j (initEndpointRowContract w k idx n rows records) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨addr, dst, field, rfl, hi, hrow, hmem, hf, hsep, hdst, h1⟩ := hpre
  let a₀ := initCSRAddr addr k rows idx
  let a₁ := initCSRAddr addr k rows (idx + 1)
  have htable : addr + (csrList k rows).length < 2 ^ w := by omega
  have hlen : k + 1 ≤ (csrList k rows).length := by rw [length_csrList]; omega
  have ha₁ : a₁ ≤ addr + (csrList k rows).length := initCSRAddr_le_end hi
  have haAdd : a₁ = a₀ + (csrList n records).length := by
    change initCSRAddr addr k rows (idx + 1) = _
    rw [initCSRAddr_succ, hrow]
  have ha₀w : a₀ < 2 ^ w := by omega
  have ha₁w : a₁ < 2 ^ w := by omega
  have hiw : idx + 1 < 2 ^ w := by omega
  have hrowMem : ListAt mem a₀ (csrList n records) := by
    rw [← hrow]
    exact initCSRAddr_listAt hmem hi
  refine runs_start_le ?_
  unfold initEndpointRow
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := k) (f := rows) hs)
    (vs := [addr, k, idx]) rfl ?_ ⟨addr, idx, rfl, hi.le, hmem, htable⟩ ?_
  · intro v hv
    exact hw v (by simp at hv ⊢; tauto)
  intro v₀ mem₀ pos₀ hpost₀
  change v₀ = a₀ ∧ mem₀ = mem at hpost₀
  obtain ⟨hv₀, hm₀⟩ := hpost₀
  subst v₀ mem₀
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := k) (f := rows) hs)
    (vs := [addr, k, idx + 1]) ?_ ?_ ⟨addr, idx + 1, rfl, hi, hmem, htable⟩ ?_
  · simp [evalArgs, Expr.eval, BinOp.eval, startState, hiw, h1]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hiw
  intro v₁ mem₁ pos₁ hpost₁
  change v₁ = a₁ ∧ mem₁ = mem at hpost₁
  obtain ⟨hv₁, hm₁⟩ := hpost₁
  subst v₁ mem₁
  have hrowLen : a₁ - a₀ = (csrList n records).length := by omega
  have hrowLenW : (csrList n records).length < 2 ^ w := by omega
  refine runs_seq_call_le (initCSRCount_meetsContract (w := w) (k := n) (f := records) hc)
    (vs := [a₀, (csrList n records).length]) ?_ ?_ ⟨a₀, rfl, hrowMem, by omega, h1⟩ ?_
  · simp [evalArgs, Expr.eval, BinOp.eval, startState, hrowLen, hrowLenW]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> omega
  intro v₂ mem₂ pos₂ hpost₂
  change v₂ = n ∧ mem₂ = mem at hpost₂
  obtain ⟨hv₂, hm₂⟩ := hpost₂
  subst v₂ mem₂
  have htwo : 2 < 2 ^ w := by omega
  refine runs_cond_le (v := if field = 2 then 1 else 0) ?_ ?_ ?_
  · by_cases he : field = 2 <;> simp [Expr.eval, startState, BinOp.eval, htwo, h1, he, Nat.two_pow_pos]
  · intro hyes
    have heq : field = 2 := by by_contra hh; simp [hh] at hyes
    refine runs_seq_call_le (initFillWord_meetsContract hfill)
      (vs := [dst, n, idx]) (by simp [evalArgs, Expr.eval, startState]) ?_
      ⟨dst, n, idx, rfl, hdst, h1⟩ ?_
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega
    intro v mem' pos' hp'
    obtain ⟨dst', n', val', hargs, hv, hwords, hfr⟩ := hp'
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨hd, hn, hval⟩ := hargs
    subst dst' n' val'
    refine runs_ret_le (v := v) (by simp [Expr.eval])
      ⟨addr, dst, field, rfl, hv, by simpa [initConnectorColumn, heq] using hwords, hfr⟩ ?_
    simp [initCSRSeekContract, initCSRCountContract, initFillWordContract,
      initEndpointRowContract, Expr.size, argsSize]
    omega
  · intro hno
    have hneq : field ≠ 2 := by intro he; simp [he] at hno
    refine runs_seq_call_le (initEndpointCopy_meetsContract (w := w) (n := n) (f := records) hcopy)
      (vs := [a₀, n, dst, field]) ?_ ?_
      ⟨a₀, dst, field, rfl, hrowMem, hf.resolve_left hneq, by omega, hdst, h1⟩ ?_
    · simp [evalArgs, Expr.eval, startState]
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ha₀w
      · omega
      · omega
      · exact hw _ (by simp)
    intro v₃ mem₃ pos₃ hpost₃
    obtain ⟨src', dst', field', hargs, hv, hwords, hframe⟩ := hpost₃
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨_, _, hdst', hfield'⟩ := hargs
    subst dst' field'
    refine runs_ret_le (v := v₃) (by simp [Expr.eval]) ⟨addr, dst, field, rfl, hv, by simpa [initConnectorColumn, hneq] using hwords, hframe⟩ ?_
    simp [initCSRSeekContract, initCSRCountContract, initEndpointContract,
      initEndpointRowContract, Expr.size, argsSize]
    omega

/-- The row program's precondition for any two ordered siblings in a static output. -/
theorem staticOut_endpointRow_pre {w h dst field j g c c' : ℕ} {S : StaticData} {mem : ℕ → ℕ}
    (hS : StaticOut mem h S) (hj : j < leafDepth S.x S.b) (hg : g < numGroups S.x S.b j)
    (hc : c ∈ childGroups S.x S.b j g) (hc' : c' ∈ childGroups S.x S.b j g) (hcc : c < c')
    (hf : field < 2) (hsep : h + S.encode.length ≤ dst)
    (hword : dst + (S.H.conn j c c').length < 2 ^ w) (h1 : 1 < 2 ^ w) :
    (initEndpointRowContract w (numPairsOf S.x S.b) (pairIdxOf S.x S.b j c c')
      (S.H.conn j c c').length (staticConnRow S)
      (fun i => connWords ((S.H.conn j c c').getD i (0, 0, [])))).pre
      [h + 7 + mem (h + 5), numPairsOf S.x S.b, pairIdxOf S.x S.b j c c', dst, field] mem := by
  have hrow := staticConnRow_of_siblings S hg hc hc' hcc
  have haddr := hS.section_end_le (i := 5) (by decide)
  rw [staticConnSection] at haddr
  refine ⟨_, dst, field, rfl, staticConnRow_index_lt S hj hg hc hcc, hrow, ?_,
    ?_, haddr.trans hsep, hword, h1⟩
  · rw [← staticConnSection]
    exact hS.section (by decide)
  · right
    right
    intro i _
    simp [connWords]
    omega

end MinCostFlow.HierPaths

end
