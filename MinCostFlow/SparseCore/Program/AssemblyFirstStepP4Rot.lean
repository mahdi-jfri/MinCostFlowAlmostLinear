module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepRotEdits
public import MinCostFlow.SparseCore.Program.AssemblyFirstRotProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4RotDedup

import MinCostFlow.SparseCore.Program.AssemblyReemb
import MinCostFlow.SparseCore.Program.OrdStoreCapContract
import WordRAM.Tactic

/-!
# The list `T₀` of Phase 4 (`AssemblyFirstStepP4Rot`)

The output step of P7 needs a list `T₀` of vertices: every vertex at which the edits of the
output batch do not give the new output order must be in it (`OutRotCover`). Phase 4 collects a
raw list of candidates, deduplicates it in one linear pass using a zeroed flag array of size
`flagCap ≤ vCap` (`p4RotDedupStmt` in `AssemblyFirstStepP4RotDedup`), and then sorts the
deduplicated list. The procedure `asmFirstP4RotStmt fDirect fBatch fEdits fBuild`, with arguments
`[tourH, spPtr, insPtr, batch, edits, h]`, keeps the counter of the raw list at `h` and the raw
list at `h + 1`, with room for two vertices per split, per entering edge, per update and per
edit. Then:
1. `asmFirstCollectRotDirectStmt` copies the two vertices of each split and the two roots of the
   ends of each entering edge;
2. `asmFirstCollectRotBatchStmt` appends the roots in the tour of the vertices of the batch;
3. `asmFirstCollectRotEditsStmt` appends the roots in the tour of the vertices of the edits;
4. `p4RotDedupStmt` computes `flagCap = max_{v ∈ rawL} (v + 1) ≤ vCap` in one linear pass and
   deduplicates `rawL` into `uniqL` of length `u ≤ min |rawL| vCap` using zeroed flags at
   `[hE₃, hE₃ + flagCap)`;
5. `asmFirstBuildRotStmt` sorts `uniqL` in `O(u log(u + 1))` time.
The procedure stores the place of `T₀` at `h`, where the counter was.

The run lemma `asmFirstP4Rot_runs` is stated on the raw list of the collectors. That this list
covers the step (`asmFirstRotSet_subset_raw`) is a fact of the model, used where Phase 4 is put
together.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## The procedure -/

@[expose] public section

/-- **The list `T₀` of Phase 4**, `[tourH, spPtr, insPtr, batch, edits, h]`. Register `6` holds
the place `h + 1` of the raw list, register `7` the heap pointer of the tour queries above the
room of the raw list, registers `8` to `10` the return values of the collectors, `p4RotDedupStmt`
deduplicates the raw list at `reg 14` (length `reg 15`, end `reg 16`), and register `11` holds
the return value of `fBuild`. -/
def asmFirstP4RotStmt (fDirect fBatch fEdits fBuild : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 5) (.const 1)) ;;
  .assign 7 (.bin .add (.reg 6) (.bin .mul (.const 2)
    (.bin .add (.bin .add (.load (.reg 1)) (.load (.reg 2)))
      (.bin .add (.load (.reg 3)) (.load (.reg 4)))))) ;;
  .call 8 fDirect [.reg 1, .reg 2, .reg 6] ;;
  .store (.reg 5) (.reg 8) ;;
  .call 9 fBatch [.reg 0, .reg 3, .reg 6, .reg 5, .reg 7] ;;
  .call 10 fEdits [.reg 0, .reg 4, .reg 6, .reg 5, .reg 9] ;;
  p4RotDedupStmt ;;
  .call 11 fBuild [.reg 14, .reg 15, .reg 16] ;;
  .store (.reg 5) (.reg 16) ;;
  .ret (.reg 11)

/-- The raw list of candidates for `T₀`: the vertices of the splits, the roots of the ends of the
entering edges, and the roots in the tour of the vertices of the batch and of the edits. -/
def p4RotRaw (splits : List CompSplitEntry) (insL : List ℕ) (tl hd rt : ℕ → ℕ)
    (U : List Update) (ed : List OrdEdit) : List ℕ :=
  rotDirectList splits insL tl hd ++ rotBatchVertList rt U ++ rotEditVertList rt ed

/-- The cells that `asmFirstP4RotStmt` uses from `h` on: the counter, the room of the raw list
(`2 n` for `n` splits, entering edges, updates and edits), the cells of the tour queries, the
flag array (`≤ vCap`), the deduplicated list (`≤ 2 n`), and the cells of the sort (`1 + 3` per
deduplicated entry). -/
def p4RotSpace (vCap nSp nIns nU nEd qs : ℕ) : ℕ :=
  2 + vCap + 10 * (nSp + nIns + nU + nEd) + 2 * nU * qs + 2 * nEd * qs

/-- The cost of `asmFirstP4RotStmt`: the direct collector, two tour queries per update and per
edit (`qc` each), linear-time deduplication of the `m` raw entries, and the sort of at most
`min m vCap` distinct entries. -/
def p4RotCost (nSp nIns nU nEd m vCap qc : ℕ) : ℕ :=
  48 * (nSp + nIns) + 2 * nU * qc + 2 * nEd * qc + 100 * m +
    280 * min m vCap * (Nat.log 2 (min m vCap + 1) + 1) + 500

/-- What `asmFirstP4RotStmt` leaves, from the tour `a` (concrete state `tx₀`): at `h` the place
of the sorted list of the distinct entries of `rawL`, with its length first, below the returned
pointer and outside `avoid₀` and the cells of the tour. The tour keeps its state, every cell
below `h` outside the tour is kept, the cells of the tour grow only into `[h + 1, o)`, and the
cost is paid against the potential of the tour. -/
def P4RotPost (TR : ℕ → ℕ → DSRep AsmTourAbs) (vCap eCap tourH h : ℕ) (a : AsmTourAbs)
    (tx₀ : (TR vCap eCap).τ) (rawL : List ℕ) (avoid₀ : ℕ → Prop) (space costB : ℕ)
    (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State) (cost : ℕ) : Prop :=
  ∃ tx' : (TR vCap eCap).τ,
    (TR vCap eCap).rep tourH a tx' st'.mem ∧
    st'.mem (st'.mem h) = (rawL.toFinset.sort (· ≤ ·)).length ∧
    ListAt st'.mem (st'.mem h + 1) (rawL.toFinset.sort (· ≤ ·)) ∧
    OutCellsFree (st'.mem h) (1 + (rawL.toFinset.sort (· ≤ ·)).length) o.value
      (fun x => avoid₀ x ∨ (TR vCap eCap).foot tourH tx' x) ∧
    h + 1 ≤ st'.mem h ∧ h + 1 ≤ o.value ∧ o.value ≤ h + space ∧ ZeroFrom st'.mem o.value ∧
    (∀ x < h, ¬ (TR vCap eCap).foot tourH tx₀ x → st'.mem x = mem₀ x) ∧
    (∀ x, (TR vCap eCap).foot tourH tx' x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (h + 1 ≤ x ∧ x < o.value)) ∧
    cost + (TR vCap eCap).phi tourH tx' st'.mem ≤ costB + (TR vCap eCap).phi tourH tx₀ mem₀

end

public section

theorem asmFirstP4RotStmt_noRand (fDirect fBatch fEdits fBuild : ℕ) :
    (asmFirstP4RotStmt fDirect fBatch fEdits fBuild).NoRand := by
  simp [asmFirstP4RotStmt, p4RotDedupStmt_noRand, Stmt.NoRand]

end

/-! ## The run -/

/-- A call followed by a statement, with the cost bound carried along. -/
private theorem rot_runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ}
    (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

/-- A normal-terminating statement followed by a statement, with the cost bound carried along. -/
private theorem rot_runs_seq_normal_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st st₁ : State} {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s₂ st₁ o st' c₂ ∧ Q o st' ∧ (k + c₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, hr₂, rfl⟩), hq, by omega⟩

/-- The run of the statement from the runs of its calls and inline deduplication. -/
private theorem asmFirstP4Rot_run_of {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fDirect fBatch fEdits fBuild : ℕ} {bDirect bBatch bEdits bBuild : Stmt}
    (hfDirect : p.procs[fDirect]? = some bDirect) (hfBatch : p.procs[fBatch]? = some bBatch)
    (hfEdits : p.procs[fEdits]? = some bEdits) (hfBuild : p.procs[fBuild]? = some bBuild)
    {tourH spPtr insPtr batch edits h pos nSp nIns nU nEd : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hmS : mem₀ spPtr = nSp) (hmI : mem₀ insPtr = nIns) (hmU : mem₀ batch = nU)
    (hmE : mem₀ edits = nEd) (hsz : h + 1 + 2 * (nSp + nIns + (nU + nEd)) < 2 ^ w)
    {o₁ o₂ o₃ o₄ : Outcome} {st₁ st₂ st₃ stD st₄ : State} {c₁ c₂ c₃ cD c₄ uniqPtr u hBuild : ℕ}
    (hr₁ : Runs w p ω bDirect (startState [spPtr, insPtr, h + 1] mem₀ pos) o₁ st₁ c₁)
    (hr₂ : Runs w p ω bBatch (startState [tourH, batch, h + 1, h,
      h + 1 + 2 * (nSp + nIns + (nU + nEd))] (Function.update st₁.mem h o₁.value) st₁.pos)
      o₂ st₂ c₂)
    (hr₃ : Runs w p ω bEdits (startState [tourH, edits, h + 1, h, o₂.value] st₂.mem st₂.pos)
      o₃ st₃ c₃)
    (hrD : Runs w p ω p4RotDedupStmt
      ⟨st₃.mem,
        Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (startState [tourH, spPtr, insPtr, batch, edits, h] mem₀ pos).regs
                  6 (h + 1))
                7 (h + 1 + 2 * (nSp + nIns + (nU + nEd))))
              8 o₁.value)
            9 o₂.value)
          10 o₃.value,
        st₃.pos⟩ .normal stD cD)
    (hDr5 : stD.regs 5 = h) (hDr14 : stD.regs 14 = uniqPtr)
    (hDr15 : stD.regs 15 = u) (hDr16 : stD.regs 16 = hBuild)
    (hr₄ : Runs w p ω bBuild (startState [uniqPtr, u, hBuild] stD.mem stD.pos) o₄ st₄ c₄) :
    ∃ st' c, Runs w p ω (asmFirstP4RotStmt fDirect fBatch fEdits fBuild)
        (startState [tourH, spPtr, insPtr, batch, edits, h] mem₀ pos) (.returned o₄.value) st' c ∧
      st'.mem = Function.update st₄.mem h hBuild ∧ c ≤ c₁ + c₂ + c₃ + cD + c₄ + 120 := by
  have key : ∃ o st' c, Runs w p ω (asmFirstP4RotStmt fDirect fBatch fEdits fBuild)
      (startState [tourH, spPtr, insPtr, batch, edits, h] mem₀ pos) o st' c ∧
      (o = .returned o₄.value ∧ st'.mem = Function.update st₄.mem h hBuild) ∧
      0 + c ≤ c₁ + c₂ + c₃ + cD + c₄ + 120 := by
    unfold asmFirstP4RotStmt
    refine runs_seq_assign_le (v := h + 1) (by eval_expr) ?_
    refine runs_seq_assign_le (v := h + 1 + 2 * (nSp + nIns + (nU + nEd))) (by eval_expr) ?_
    refine rot_runs_seq_callRuns_le (by eval_expr) hfDirect hr₁ ?_
    refine runs_seq_store_le (x := h) (v := o₁.value) (by eval_expr) (by eval_expr) ?_
    refine rot_runs_seq_callRuns_le (by eval_expr) hfBatch hr₂ ?_
    refine rot_runs_seq_callRuns_le (by eval_expr) hfEdits hr₃ ?_
    refine rot_runs_seq_normal_le hrD ?_
    have heArgs : evalArgs w stD [.reg 14, .reg 15, .reg 16] = some [uniqPtr, u, hBuild] :=
      evalArgs_cons (Expr.eval_reg_of_eq hDr14) <|
      evalArgs_cons (Expr.eval_reg_of_eq hDr15) <|
      evalArgs_cons (Expr.eval_reg_of_eq hDr16) <| evalArgs_nil _ _
    refine rot_runs_seq_callRuns_le heArgs hfBuild hr₄ ?_
    refine runs_seq_store_le (x := h) (v := hBuild)
      (Expr.eval_reg_of_eq (by simp [hDr5]))
      (Expr.eval_reg_of_eq (by simp [hDr16])) ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c, hr, hm, by omega⟩

/-- **The run of `asmFirstP4RotStmt`.** The splits, the entering edges, the batch and the edits
lie below `h`, the batch and the edits outside the cells of the tour, and every entry of the raw
list is below `vCap`. Then the procedure deduplicates the raw list in linear time and leaves the
sorted list of its distinct entries, as `P4RotPost` says. -/
public theorem asmFirstP4Rot_runs {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w fVertRoot fDirect fBatch fEdits fBuild bSort vCap eCap tourH spPtr insPtr batch words
      edits editWords h pos : ℕ} {p : Program}
    (H : AsmFirstTourRootAt TR w p fVertRoot) (hTR_loc : ∀ v e, (TR v e).Local)
    (hfDirect : p.procs[fDirect]? = some asmFirstCollectRotDirectStmt)
    (hfBatch : p.procs[fBatch]? = some (asmFirstCollectRotBatchStmt fVertRoot))
    (hfEdits : p.procs[fEdits]? = some (asmFirstCollectRotEditsStmt fVertRoot))
    (hfBuild : p.procs[fBuild]? = some (asmFirstBuildRotStmt bSort))
    (hpS : p.HasAt bSort (sortProcs bSort))
    {splits : List CompSplitEntry} {insL : List ℕ} {tl hd : ℕ → ℕ} {G₀ : MGraph}
    {U : List Update} {ed : List OrdEdit} {a : AsmTourAbs} {tx₀ : (TR vCap eCap).τ}
    {avoid₀ : ℕ → Prop} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htour_w : tourH < 2 ^ w) (hvCap_w : vCap < 2 ^ w)
    (hSp : SplitEntriesAt mem₀ spPtr splits) (hSp_le : spPtr + splitEntriesWords splits ≤ h)
    (hIns : OutInsAt mem₀ insPtr insL tl hd) (hIns_le : insPtr + 1 + 3 * insL.length ≤ h)
    (hBat : BatchAt mem₀ batch G₀ U words) (hBat_le : batch + words ≤ h)
    (hEd : OrdEditsAt mem₀ edits ed editWords) (hEd_le : edits + editWords ≤ h)
    (hIn : ∀ x, (batch ≤ x ∧ x < batch + words) ∨ (edits ≤ x ∧ x < edits + editWords) →
      ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hVU : ∀ v ∈ batchVerts U, v < vCap) (hVE : ∀ v ∈ ordEditVerts ed, v < vCap)
    (hraw_cap : ∀ v ∈ p4RotRaw splits insL tl hd a.rf.root U ed, v < vCap)
    (hrep : (TR vCap eCap).rep tourH a tx₀ mem₀)
    (hfoot : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < h)
    (havoid : ∀ x, h ≤ x → ¬ avoid₀ x) (hz : ZeroFrom mem₀ h)
    (hsp : h + p4RotSpace vCap splits.length insL.length U.length ed.length H.querySpace < 2 ^ w) :
    ∃ o st' cost, Runs w p ω (asmFirstP4RotStmt fDirect fBatch fEdits fBuild)
        (startState [tourH, spPtr, insPtr, batch, edits, h] mem₀ pos) o st' cost ∧
      P4RotPost TR vCap eCap tourH h a tx₀ (p4RotRaw splits insL tl hd a.rf.root U ed) avoid₀
        (p4RotSpace vCap splits.length insL.length U.length ed.length H.querySpace)
        (p4RotCost splits.length insL.length U.length ed.length
          (p4RotRaw splits insL tl hd a.rf.root U ed).length vCap (H.mul * ordStoreLog eCap + 60))
        mem₀ o st' cost := by
  set rawL := p4RotRaw splits insL tl hd a.rf.root U ed
  -- The counts at the four inputs.
  have hnEd : mem₀ edits = ed.length := by
    have h1 : (decodeOrdEdits mem₀ (mem₀ edits) (edits + 1)).1 = ed := hEd.1
    have h2 := (decodeOrdEdits_length mem₀ (mem₀ edits) (edits + 1)).1
    rw [h1] at h2; exact h2.symm
  have hw1 : 1 ≤ words := hBat.1
  have hew1 : 1 ≤ editWords := by rw [hEd.2.1]; omega
  have hlen₁ := rotDirectList_length splits insL tl hd
  have hlenU := rotBatchVertList_length_le a.rf.root U
  have hlenE := rotEditVertList_length_le a.rf.root ed
  have hmlen : rawL.length =
      (rotDirectList splits insL tl hd).length + (rotBatchVertList a.rf.root U).length +
        (rotEditVertList a.rf.root ed).length := by
    simp only [rawL, p4RotRaw, List.length_append]
  have hSpW : splitEntriesWords splits = 1 + 4 * splits.length := rfl
  unfold p4RotSpace at hsp
  -- Step 1: the vertices of the splits and the roots of the ends of the entering edges.
  obtain ⟨st₁, c₁, hr₁, hL₁, hk₁, hc₁⟩ := asmFirstCollectRotDirect_runs (p := p) (ω := ω)
    (pos := pos) (outPtr := h + 1) hw16 hSp hIns (by omega) (by omega) (by omega)
  have hm₁ : ∀ x < h,
      Function.update st₁.mem h (rotDirectList splits insL tl hd).length x = mem₀ x := by
    intro x hx
    rw [Function.update_of_ne (by omega)]
    exact hk₁ x (Or.inl (by omega))
  have hz₁ : ZeroFrom (Function.update st₁.mem h (rotDirectList splits insL tl hd).length)
      (h + 1 + 2 * (splits.length + insL.length + (U.length + ed.length))) := by
    intro x hx
    rw [Function.update_of_ne (by omega), hk₁ x (Or.inr (by omega))]
    exact hz x (by omega)
  have hloc₀ := hTR_loc vCap eCap tourH a tx₀ mem₀
    (Function.update st₁.mem h (rotDirectList splits insL tl hd).length)
    fun x hx => (hm₁ x (hfoot x hx)).symm
  have hBat₁ : BatchAt (Function.update st₁.mem h (rotDirectList splits insL tl hd).length)
      batch G₀ U words :=
    ⟨hBat.1, (hm₁ batch (by omega)).trans hBat.2.1,
      batchBodyAt_of_agree hBat.2.2 fun x _ h2 => hm₁ x (by omega)⟩
  -- Step 2: the roots of the vertices of the batch.
  obtain ⟨hE₂, st₂, c₂, tx₂, hr₂, hrep₂, hcnt₂, hL₂, hE₂lo, hE₂hi, hz₂, hk₂, hft₂, hc₂⟩ :=
    asmFirstCollectRotBatch_runs (pos := st₁.pos) (ω := ω) (outPtr := h + 1) (cntAddr := h)
      (rotCap := 2 * (splits.length + insL.length + (U.length + ed.length)))
      (hBase := h + 1 + 2 * (splits.length + insL.length + (U.length + ed.length)))
      (L0 := rotDirectList splits insL tl hd) H hTR_loc hw16 htour_w hvCap_w hBat₁ (by omega)
      (fun x h1 h2 => ⟨hIn x (Or.inl ⟨h1, h2⟩), Or.inl (by omega), by omega⟩) hVU
      (hloc₀.1 hrep) (fun x hx => by have := hfoot x hx; omega) le_rfl (by omega)
      (Or.inl (by omega)) (fun x h1 _ hx => by have := hfoot x hx; omega)
      (fun hx => by have := hfoot h hx; omega) (by omega) (by simp) (hL₁.update_lt (by omega))
      hz₁ (by omega)
  have hk₂' : ∀ x < h, ¬ (TR vCap eCap).foot tourH tx₀ x → st₂.mem x = mem₀ x :=
    fun x hx hnf => (hk₂ x (by omega) hnf (Or.inl (by omega)) (by omega)).trans (hm₁ x hx)
  have hft₂' : ∀ x, (TR vCap eCap).foot tourH tx₂ x → (TR vCap eCap).foot tourH tx₀ x ∨
      (h + 1 + 2 * (splits.length + insL.length + (U.length + ed.length)) ≤ x ∧ x < hE₂) :=
    hft₂
  have hft₂l : ∀ x, (TR vCap eCap).foot tourH tx₂ x → x < h ∨
      (h + 1 + 2 * (splits.length + insL.length + (U.length + ed.length)) ≤ x ∧ x < hE₂) := by
    intro x hx
    rcases hft₂' x hx with h' | h'
    · exact Or.inl (hfoot x h')
    · exact Or.inr h'
  have hEd₂ : OrdEditsAt st₂.mem edits ed editWords :=
    ordEditsAt_of_agree hEd fun x h1 h2 => hk₂' x (by omega) (hIn x (Or.inr ⟨h1, h2⟩))
  -- Step 3: the roots of the vertices of the edits.
  obtain ⟨hE₃, st₃, c₃, tx₃, hr₃, hrep₃, hcnt₃, hL₃, hE₃lo, hE₃hi, hz₃, hk₃, hft₃, hc₃⟩ :=
    asmFirstCollectRotEdits_runs (pos := st₂.pos) (ω := ω) (outPtr := h + 1) (cntAddr := h)
      (rotCap := 2 * (splits.length + insL.length + (U.length + ed.length))) (hBase := hE₂)
      (L0 := rotDirectList splits insL tl hd ++ rotBatchVertList a.rf.root U) H hTR_loc hw16
      htour_w hvCap_w hEd₂ (by omega)
      (fun x h1 h2 => ⟨fun hx => by
        rcases hft₂' x hx with h' | h'
        · exact hIn x (Or.inr ⟨h1, h2⟩) h'
        · omega, Or.inl (by omega), by omega⟩) hVE hrep₂
      (fun x hx => by have := hft₂l x hx; omega) (by omega) (by omega) (Or.inl (by omega))
      (fun x h1 _ hx => by have := hft₂l x hx; omega) (fun hx => by have := hft₂l h hx; omega)
      (by simp only [List.length_append]; omega) hcnt₂ hL₂ hz₂ (by omega)
  have hft₃' : ∀ x, (TR vCap eCap).foot tourH tx₃ x → x < h ∨
      (h + 1 + 2 * (splits.length + insL.length + (U.length + ed.length)) ≤ x ∧ x < hE₃) := by
    intro x hx
    rcases hft₃ x hx with h' | h'
    · rcases hft₂' x h' with h'' | h''
      · exact Or.inl (hfoot x h'')
      · right; omega
    · right; omega
  -- Step 4a: inline linear deduplication of `rawL` into `uniqL = rotDedup rawL`.
  set flagCap := rotFlagCap rawL
  set uniqL := rotDedup rawL
  set uniqPtr := hE₃ + flagCap
  set hBuild := uniqPtr + uniqL.length
  have hfc_le : flagCap ≤ vCap := rotFlagCap_le hraw_cap
  have hu_le_m : uniqL.length ≤ rawL.length := rotDedup_length_le_length rawL
  have hu_le_min : uniqL.length ≤ min rawL.length vCap := rotDedup_length_le_min hraw_cap
  have huniq_cap : ∀ v ∈ uniqL, v < vCap := fun v hv => hraw_cap v ((mem_rotDedup rawL v).mp hv)
  have huniq_finset : uniqL.toFinset = rawL.toFinset := rotDedup_toFinset rawL
  set s0 := startState [tourH, spPtr, insPtr, batch, edits, h] mem₀ pos
  set regsMid :=
    Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update s0.regs 6 (h + 1))
            7 (h + 1 + 2 * (splits.length + insL.length + (U.length + ed.length))))
          8 (rotDirectList splits insL tl hd).length)
        9 hE₂)
      10 hE₃
  obtain ⟨stD, cD, hrD, hDr5, hDr14, hDr15, hDr16, hLAD, hzD, hkD, hcD⟩ :=
    p4RotDedup_runs (p := p) (ω := ω) (st₀ := ⟨st₃.mem, regsMid, st₃.pos⟩)
      (h := h) (rawPtr := h + 1) (hE := hE₃) (vCap := vCap) (rawL := rawL)
      hw16 (by simp [regsMid, s0, startState]) (by simp [regsMid]) (by simp [regsMid])
      hcnt₃ hL₃ (by omega) hraw_cap hvCap_w hz₃ (by omega)
  -- Step 4b: sort `uniqL` of length `u ≤ min |rawL| vCap`.
  obtain ⟨o₄, st₄, c₄, hr₄, ho₄, hcnt₄, hL₄, -, -, hlenT, hz₄, hk₄, hc₄⟩ :=
    asmFirstBuildRot_runs (pos := stD.pos) (ω := ω) (h := hBuild) (rawPtr := uniqPtr)
      (rawL := uniqL) hpS hw16 hLAD (by omega) huniq_cap hvCap_w hzD (by omega)
  -- Step 5: the run of the whole statement.
  obtain ⟨st', c, hrun, hm', hc⟩ := asmFirstP4Rot_run_of hfDirect hfBatch hfEdits hfBuild
    hw16 hSp.1 hIns.1 hBat.2.1 hnEd (by omega) hr₁ hr₂ hr₃
    hrD hDr5 hDr14 hDr15 hDr16 hr₄
  have hmh : st'.mem h = hBuild := by rw [hm']; exact Function.update_self ..
  have hagree : ∀ x, (TR vCap eCap).foot tourH tx₃ x → st₃.mem x = st'.mem x := by
    intro x hx
    have := hft₃' x hx
    rw [hm', Function.update_of_ne (by omega), hk₄ x (by omega), hkD x (by omega)]
  have hloc₃ := hTR_loc vCap eCap tourH a tx₃ st₃.mem st'.mem hagree
  have hov : (Outcome.returned o₄.value).value = o₄.value := rfl
  have hlen₂ : (rotDirectList splits insL tl hd ++ rotBatchVertList a.rf.root U).length =
      (rotDirectList splits insL tl hd).length + (rotBatchVertList a.rf.root U).length := by
    simp only [List.length_append]
  have hlen₃ : (rotDirectList splits insL tl hd ++ rotBatchVertList a.rf.root U ++
      rotEditVertList a.rf.root ed).length = (rotDirectList splits insL tl hd).length +
        (rotBatchVertList a.rf.root U).length + (rotEditVertList a.rf.root ed).length := by
    simp only [List.length_append]
  have hsort_cost : 280 * uniqL.length * (Nat.log 2 (uniqL.length + 1) + 1) ≤
      280 * min rawL.length vCap * (Nat.log 2 (min rawL.length vCap + 1) + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 280 hu_le_min)
      (Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hu_le_min 1)) 1)
  refine ⟨_, st', c, hrun, tx₃, hloc₃.1 hrep₃, ?_, ?_, ?_, by rw [hmh]; omega,
    by show h + 1 ≤ o₄.value; omega, by show o₄.value ≤ _; unfold p4RotSpace; omega,
    by rw [hm']; exact hz₄.update_lt (by omega), fun x hx hnf => ?_, fun x hx => ?_, ?_⟩
  · rw [hmh, hm', Function.update_of_ne (by omega), ← huniq_finset]
    exact hcnt₄
  · rw [hmh, hm', ← huniq_finset]
    exact hL₄.update_lt (by omega)
  · rw [hmh]
    refine ⟨by rw [← huniq_finset]; omega, fun i _ hi => ?_⟩
    rcases hi with hi | hi
    · exact havoid _ (by omega) hi
    · have := hft₃' _ hi
      omega
  · have hnf₂ : ¬ (TR vCap eCap).foot tourH tx₂ x := fun hx2 => by
      rcases hft₂' x hx2 with h' | h'
      · exact hnf h'
      · omega
    rw [hm', Function.update_of_ne (by omega), hk₄ x (by omega), hkD x (by omega),
      hk₃ x (by omega) hnf₂ (Or.inl (by omega)) (by omega)]
    exact hk₂' x hx hnf
  · rcases hft₃ x hx with h' | h'
    · rcases hft₂' x h' with h'' | h''
      · exact Or.inl h''
      · right; omega
    · right; omega
  · rw [← hloc₃.2]
    have hphi₀ := hloc₀.2
    unfold p4RotCost
    omega

end MinCostFlow.SparseCore.Program
