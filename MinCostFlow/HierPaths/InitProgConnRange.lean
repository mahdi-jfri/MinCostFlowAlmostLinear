module

public import MinCostFlow.HierPaths.InitProgConnCopy

/-!
# Copying consecutive connector rows

The row procedure appends one column. The loop below appends consecutive columns in row
order and charges each call for the number of connectors in that row.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The endpoint columns of rows from `lo` up to `hi`. -/
def endpointRangeWords (n : ℕ → ℕ) (records : ℕ → ℕ → List ℕ) (lo hi field : ℕ) : List ℕ :=
  (List.range' lo (hi - lo)).flatMap fun i => initConnectorColumn i field (n i) (records i)

private theorem endpointRangeWords_succ (n : ℕ → ℕ) (records : ℕ → ℕ → List ℕ)
    {lo i field : ℕ} (hi : lo ≤ i) :
    endpointRangeWords n records lo (i + 1) field =
      endpointRangeWords n records lo i field ++ initConnectorColumn i field (n i) (records i) := by
  have hsub : i + 1 - lo = (i - lo) + 1 := by omega
  have he : lo + (i - lo) = i := by omega
  simp [endpointRangeWords, hsub, List.range'_concat, he]

/-- The arguments are the table address, row count, two range bounds, destination and field. -/
def initEndpointRange (row : ℕ) : Stmt :=
  forRange 6 (.reg 2) (.reg 3) (.call 4 row [.reg 0, .reg 1, .reg 6, .reg 4, .reg 5]) ;;
  .ret (.reg 4)

theorem initEndpointRange_noRand (row : ℕ) : (initEndpointRange row).NoRand := by
  simp [initEndpointRange, forRange, forUp, Stmt.NoRand]

/-- Copy the given interval of rows into the output. -/
def initEndpointRangeContract (w k lo hi : ℕ) (rows : ℕ → List ℕ) (n : ℕ → ℕ)
    (records : ℕ → ℕ → List ℕ) : Contract where
  pre args mem := ∃ src dst field, args = [src, k, lo, hi, dst, field] ∧ lo ≤ hi ∧ hi ≤ k ∧
    ListAt mem src (csrList k rows) ∧
    (∀ i, lo ≤ i → i < hi → rows i = csrList (n i) (records i) ∧
      (field = 2 ∨ field = 3 ∨ ∀ j < n i, field < (records i j).length)) ∧
    src + (csrList k rows).length ≤ dst ∧
    dst + (endpointRangeWords n records lo hi field).length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ src dst field, args = [src, k, lo, hi, dst, field] ∧
    v = dst + (endpointRangeWords n records lo hi field).length ∧
    ListAt mem' dst (endpointRangeWords n records lo hi field) ∧
    ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := rangeCost (fun i => 60 * n i + 157) lo hi + 9 * (hi - lo) + 12

theorem initEndpointRange_meetsContract {w k lo hi j row seek count copy fill : ℕ}
    {rows : ℕ → List ℕ} {n : ℕ → ℕ} {records : ℕ → ℕ → List ℕ} {p : Program}
    (hp : p.procs[j]? = some (initEndpointRange row))
    (hr : p.procs[row]? = some (initEndpointRow seek count copy fill))
    (hs : p.procs[seek]? = some initCSRSeek) (hc : p.procs[count]? = some initCSRCount)
    (hcopy : p.procs[copy]? = some initEndpointCopy)
    (hfill : p.procs[fill]? = some initFillWord) :
    MeetsContract w p j (initEndpointRangeContract w k lo hi rows n records) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨src, dst, field, rfl, hlo, hhi, hmem, hrows, hsep, hroom, hw1⟩ := hpre
  let words := fun i => endpointRangeWords n records lo i field
  have hnil : words lo = [] := by simp [words, endpointRangeWords]
  have hnext (i : ℕ) (hl : lo ≤ i) :
      words (i + 1) = words i ++ initConnectorColumn i field (n i) (records i) :=
    endpointRangeWords_succ n records hl
  have hmon (i q : ℕ) (hl : lo ≤ i) (hiq : i ≤ q) : (words i).length ≤ (words q).length := by
    induction q, hiq using Nat.le_induction with
    | base => exact le_rfl
    | succ q hq ih =>
      rw [hnext q (hl.trans hq), List.length_append]
      exact ih.trans (Nat.le_add_right _ _)
  let initial := startState [src, k, lo, hi, dst, field] mem pos
  let Inv := fun i (s : State) =>
    s.regs 0 = src ∧ s.regs 1 = k ∧ s.regs 3 = hi ∧ s.regs 4 = dst + (words i).length ∧
    s.regs 5 = field ∧ s.regs 6 = i ∧ ListAt s.mem dst (words i) ∧
    ∀ y, y < dst ∨ dst + (words i).length ≤ y → s.mem y = mem y
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 6) (lo := .reg 2) (hi := .reg 3)
    (body := .call 4 row [.reg 0, .reg 1, .reg 6, .reg 4, .reg 5])
    (P := fun s => s = initial) (Inv := Inv)
    (fun i => 60 * n i + 157) lo hi hlo hw1 (fun _ => hw _ (by simp))
    (fun s he => by
      subst s
      refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, fun _ _ => rfl⟩
      · simp [hnil, initial, startState]
      · rw [hnil]; intro i hi; simp at hi)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.1)
    (fun i hl hi' => by
      intro s ω hI
      obtain ⟨h0, h1, h3, h4, h5, h6, hwords, hframe⟩ := hI
      let cur := dst + (words i).length
      have hd : cur + n i = dst + (words (i + 1)).length := by
        simp [cur, hnext i hl, Nat.add_assoc, initConnectorColumn_length]
      have hcur : cur + n i < 2 ^ w := by
        rw [hd]
        exact (Nat.add_le_add_left (hmon (i + 1) hi (by omega) hi') dst).trans_lt hroom
      have hsrc : ListAt s.mem src (csrList k rows) :=
        listAt_congr (fun x hx => (hframe _ (Or.inl (by omega))).symm) hmem
      obtain ⟨hrow, hfields⟩ := hrows i hl hi'
      refine runs_start_le ?_
      refine runs_call_le (initEndpointRow_meetsContract (w := w) (k := k) (idx := i)
        (n := n i) (rows := rows) (records := records i) hr hs hc hcopy hfill)
        (vs := [src, k, i, cur, field]) ?_ ?_ ⟨src, cur, field, rfl, hi'.trans_le hhi,
          hrow, hsrc, hfields, hsep.trans (Nat.le_add_right _ _), hcur, hw1⟩ ?_
      · simp [evalArgs, Expr.eval, h0, h1, h4, h5, h6, cur]
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact hw _ (by simp)
        · exact hw _ (by simp)
        · exact hi'.trans (hw _ (by simp))
        · omega
        · exact hw _ (by simp)
      · intro v mem' pos' hp'
        obtain ⟨src', dst', field', ha, hv, hcol, hfr⟩ := hp'
        simp only [List.cons.injEq, and_true] at ha
        obtain ⟨_, _, _, hdst', hfield'⟩ := ha
        subst dst' field' v
        refine ⟨⟨⟨by simp [h0], by simp [h1], by simp [h3], by simpa using hd, by simp [h5],
          by simp, ?_, ?_⟩, by simpa using h6⟩, ?_⟩
        · rw [hnext i hl, listAt_append]
          exact ⟨listAt_congr (fun x hx => (hfr _ (Or.inl (by omega))).symm)
            hwords, hcol⟩
        · intro y hy
          rw [← hd] at hy
          exact (hfr y (by omega)).trans (hframe y (by omega))
        · simp [initEndpointRowContract, argsSize, Expr.size] <;> omega)
  refine runs_start_le ?_
  unfold initEndpointRange
  refine runs_seq_triple_le hloop rfl ?_
  intro s ⟨_, _, _, h4, _, _, hwds, hfr⟩
  refine runs_ret_le (Expr.eval_reg_of_eq h4) ⟨src, dst, field, rfl, rfl, hwds, hfr⟩ ?_
  simp [initEndpointRangeContract, Expr.size, Nat.mul_comm 9]

end MinCostFlow.HierPaths

end
