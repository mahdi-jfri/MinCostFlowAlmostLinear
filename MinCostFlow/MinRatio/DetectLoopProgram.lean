module

public import MinCostFlow.MinRatio.DetectReportingLoop
public import MinCostFlow.MinRatio.DetectSearchRead
public import MinCostFlow.MinRatio.DetectReadyReport
public import MinCostFlow.MinRatio.DetectExhaustedBranch
public import MinCostFlow.MinRatio.DetectTables
import WordRAM.Memory

/-!
# Linking the Detect loop body

The proof of Theorem 5.1 (pages 29–30) repeats the search until no
ready edge remains. The machine loop sets the workspace bounds,
searches and reads a slot, and either reports it or finalizes the
list. The accounting combines the search and branch costs.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- The workspace setup and ready-slot search before either branch. -/
@[expose] def detectLoopSearch (find read : ℕ) : Stmt :=
  detectWorkspaceArgs ;; detectSearchRead find read

/-- The linked Detect loop. Exhaustion returns the heap from the final search. -/
@[expose] def detectLoopProgram (find read report finish : ℕ) : Stmt :=
  detectReportingLoop (detectLoopSearch find read)
    (detectReadyReport report) (detectExhaustedBranch finish)

/-- The linked Detect loop contains no random instructions. -/
theorem detectLoopProgram_noRand (find read report finish : ℕ) :
    (detectLoopProgram find read report finish).NoRand := by
  apply detectReportingLoop_noRand
  · simp [detectLoopSearch, detectWorkspaceArgs, detectSearchRead_noRand, Stmt.NoRand]
  · exact detectReadyReport_noRand _
  · exact detectExhaustedBranch_noRand _

/-- Link the verified instructions of a Detect round and charge
three steps for sequence and branch dispatch. -/
theorem detectLoopRound_runs {w find read report finish : ℕ}
    {p : Program} {ω : ℕ → Bool} {st setup found out : State}
    {searchCost branchCost slot : ℕ} {o : Outcome}
    (hsetup : Runs w p ω detectWorkspaceArgs st .normal setup 9)
    (hsearch : Runs w p ω (detectSearchRead find read) setup .normal found searchCost)
    (hslot : found.regs 3 = slot)
    (hbranch : Runs w p ω
      (if slot = 0 then detectExhaustedBranch finish else detectReadyReport report)
      found o out branchCost) :
    Runs w p ω
      (detectLoopSearch find read ;; .cond (.reg 3) (detectReadyReport report)
        (detectExhaustedBranch finish)) st o out (searchCost + branchCost + 13) := by
  have hs : Runs w p ω (detectLoopSearch find read) st .normal found (9 + searchCost + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨setup, 9, searchCost, hsetup, hsearch, rfl⟩)
  have hb : Runs w p ω (.cond (.reg 3) (detectReadyReport report)
      (detectExhaustedBranch finish)) found o out (branchCost + 2) :=
    runs_cond_iff.mpr ⟨slot, branchCost, by simp [Expr.eval, hslot], hbranch, by
      simp [Expr.size]; omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨found, _, _, hs, hb, by omega⟩)

/-- Search and report preserve the original memory below the heap
outside the tree and the one report cell. Any new tree cell lies in
the combined allocation interval. -/
theorem detectLoopRound_frame {searchHeap reportHeap ret cursor : ℕ}
    {before found after : State} {oldFoot searchFoot reportFoot : ℕ → Prop}
    (hspace : searchHeap ≤ reportHeap) (hret : reportHeap ≤ ret)
    (hsearch : ∀ a < searchHeap, ¬ oldFoot a → found.mem a = before.mem a)
    (hsearchFoot : ∀ a, searchFoot a → oldFoot a ∨ (searchHeap ≤ a ∧ a < reportHeap))
    (hreport : ∀ a < reportHeap, ¬ searchFoot a → a ≠ cursor → after.mem a = found.mem a)
    (hreportFoot : ∀ a, reportFoot a → searchFoot a ∨ (reportHeap ≤ a ∧ a < ret)) :
    (∀ a < searchHeap, ¬ oldFoot a → a ≠ cursor → after.mem a = before.mem a) ∧
      (∀ a, reportFoot a → oldFoot a ∨ (searchHeap ≤ a ∧ a < ret)) := by
  constructor
  · intro a ha ho hc
    have hs : ¬ searchFoot a := by
      intro hf
      rcases hsearchFoot a hf with hf | ⟨hl, _⟩
      · exact ho hf
      · exact (Nat.not_le_of_lt ha) hl
    exact (hreport a (ha.trans_le hspace) hs hc).trans (hsearch a ha ho)
  · intro a ha
    rcases hreportFoot a ha with hs | ⟨hl, hu⟩
    · rcases hsearchFoot a hs with ho | ⟨hl, hu⟩
      · exact Or.inl ho
      · exact Or.inr ⟨hl, hu.trans_le hret⟩
    · exact Or.inr ⟨hspace.trans hl, hu⟩

/-- The combined round frame preserves the name and threshold tables
below the heap and outside the report and tree footprints. -/
theorem detectLoopRound_tables {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {before after : State} {heap cursor names inverse thresholds h L P : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {foot : ℕ → Prop}
    (ht : DetectTablesAt model before.mem names inverse thresholds h L P slotOf internalOf thresholdOf)
    (hdisjoint : ∀ e ∈ model.extG.E, ∀ a,
      (a = names + slotOf e ∨ a = inverse + internalOf e ∨ a = thresholds + slotOf e ∨
        (thresholdOf e ≤ a ∧ a < thresholdOf e + L)) →
      a < heap ∧ ¬ foot a ∧ a ≠ cursor)
    (hframe : ∀ a < heap, ¬ foot a → a ≠ cursor → after.mem a = before.mem a) :
    DetectTablesAt model after.mem names inverse thresholds h L P slotOf internalOf thresholdOf :=
  ht.congr fun e he a ha =>
    let hd := hdisjoint e he a ha
    hframe a hd.1 hd.2.1 hd.2.2

/-- Reserve the complete report interval before the first search.
A round's fresh tree allocation starts above it, so even report
cells that will be written in later rounds of the loop remain outside the tree. -/
theorem detectLoopRound_reserved {heap ret base capacity : ℕ}
    {oldFoot newFoot tableCell : ℕ → Prop}
    (hcap : base + 1 + capacity ≤ heap) (hheap : heap ≤ ret)
    (hfoot : ∀ a, oldFoot a → a < heap)
    (hbuffer : ∀ a, base ≤ a → a < base + 1 + capacity → ¬ oldFoot a)
    (hprotected : ∀ a, tableCell a → a < heap ∧ ¬ oldFoot a)
    (hnew : ∀ a, newFoot a → oldFoot a ∨ (heap ≤ a ∧ a < ret)) :
    base + 1 + capacity ≤ ret ∧
      (∀ a, newFoot a → a < ret) ∧
      (∀ a, base ≤ a → a < base + 1 + capacity → ¬ newFoot a) ∧
      (∀ a, tableCell a → a < ret ∧ ¬ newFoot a) := by
  have houtside {a : ℕ} (ha : a < heap) (ho : ¬ oldFoot a) : ¬ newFoot a := by
    intro hn
    rcases hnew a hn with hf | ⟨hl, _⟩
    · exact ho hf
    · exact (Nat.not_le_of_lt ha) hl
  refine ⟨hcap.trans hheap, ?_, ?_, ?_⟩
  · intro a ha
    rcases hnew a ha with ho | ⟨_, hh⟩
    · exact (hfoot a ho).trans_le hheap
    · exact hh
  · intro a ha hb
    exact houtside (hb.trans_le hcap) (hbuffer a ha hb)
  · intro a ha
    obtain ⟨hl, ho⟩ := hprotected a ha
    exact ⟨hl.trans_le hheap, houtside hl ho⟩

/-- The state carried by the Detect reporting loop. The reserved
answer interval contains the current prefix, the next cursor, and
space for every still-pending live edge. -/
structure DetectLoopState {cfg : Chain.Alg2Config} (model : Chain.Alg2State cfg)
    (R : DSRep PathTreeState) (handle base names inverse thresholds h L P : ℕ)
    (slotOf internalOf thresholdOf : ℕ → ℕ) (st : State) where
  tree : PathTreeState
  token : R.τ
  trees : List LinkCut.AuxTree
  free : List ℕ
  depth : ℕ → ℕ
  written : List ℕ
  treeRep : R.rep handle tree token st.mem
  forestInv : LinkCut.LctInvWith pathPayload tree trees free depth
  accounts : DetectForestAccounts model P slotOf written.toFinset tree trees
  coverage : ∀ slot, pathTreeReady tree slot → ∃ e ∈ model.extG.E, slotOf e = slot
  nodup : written.Nodup
  subset : written.toFinset ⊆ (Chain.algorithm2_detect cfg model).1
  prefixAt : ListAt st.mem (base + 1) written
  cursor : st.regs 8 = base + 1 + written.length
  reserve : base + 1 + model.extG.E.card ≤ st.regs 1
  zero : ZeroFrom st.mem (st.regs 1)
  treeBound : ∀ a, R.foot handle token a → a < st.regs 1
  bufferDisjoint : ∀ a, base ≤ a → a < base + 1 + model.extG.E.card → ¬ R.foot handle token a
  tables : DetectTablesAt model st.mem names inverse thresholds h L P slotOf internalOf thresholdOf
  tableDisjoint : ∀ e ∈ model.extG.E, ∀ a,
    (a = names + slotOf e ∨ a = inverse + internalOf e ∨ a = thresholds + slotOf e ∨
      (thresholdOf e ≤ a ∧ a < thresholdOf e + L)) → a < base ∧ ¬ R.foot handle token a

/-- The report prefix fits in its interval, and if a report remains,
the next cursor is strictly inside the reserve. -/
theorem DetectLoopState.cursor_bound {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {handle base names inverse thresholds h L P : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st : State}
    (I : DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf st) :
    st.regs 8 ≤ base + 1 + model.extG.E.card ∧
      (0 < ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card →
        st.regs 8 < base + 1 + model.extG.E.card) := by
  have hcard := Finset.card_le_card I.subset
  have hreport : (Chain.algorithm2_detect cfg model).1.card ≤ model.extG.E.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [List.toFinset_card_of_nodup I.nodup] at hcard
  rw [I.cursor]
  refine ⟨by omega, ?_⟩
  rw [Finset.card_sdiff_of_subset I.subset, List.toFinset_card_of_nodup I.nodup]
  omega

/-- The ready branch's updated forest, appended report, and memory
frame reestablish the concrete loop state for the next search. -/
@[expose] def DetectLoopState.append
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {handle base names inverse thresholds h L P edge : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st out : State}
    (I : DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf st)
    {tree : PathTreeState} {token : R.τ} {trees : List LinkCut.AuxTree}
    (hrep : R.rep handle tree token out.mem)
    (hinv : LinkCut.LctInvWith pathPayload tree trees I.free I.depth)
    (ha : DetectForestAccounts model P slotOf (I.written ++ [edge]).toFinset tree trees)
    (hc : ∀ slot, pathTreeReady tree slot → ∃ e ∈ model.extG.E, slotOf e = slot)
    (hn : (I.written ++ [edge]).Nodup)
    (hs : (I.written ++ [edge]).toFinset ⊆ (Chain.algorithm2_detect cfg model).1)
    (hp : ListAt out.mem (base + 1) (I.written ++ [edge]))
    (hcursor : out.regs 8 = st.regs 8 + 1)
    (hheap : st.regs 1 ≤ out.regs 1) (hz : ZeroFrom out.mem (out.regs 1))
    (hf : ∀ a < st.regs 1, ¬ R.foot handle I.token a → a ≠ st.regs 8 → out.mem a = st.mem a)
    (hnew : ∀ a, R.foot handle token a →
      R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < out.regs 1)) :
    DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf out := by
  have hbase : base ≤ st.regs 1 := by have := I.reserve; omega
  obtain ⟨hreserve, hbound, hbuffer, _⟩ :=
    detectLoopRound_reserved (tableCell := fun _ => False) I.reserve hheap I.treeBound
      I.bufferDisjoint (fun _ ha => False.elim ha) hnew
  refine ⟨tree, token, trees, I.free, I.depth, I.written ++ [edge], hrep, hinv, ha, hc,
    hn, hs, hp, ?_, hreserve, hz, hbound, hbuffer, ?_, ?_⟩
  · simp [hcursor, I.cursor, Nat.add_assoc]
  · apply detectLoopRound_tables I.tables _ hf
    intro e he a had
    obtain ⟨hb, ho⟩ := I.tableDisjoint e he a had
    exact ⟨hb.trans_le hbase, ho, by rw [I.cursor]; omega⟩
  · intro e he a had
    obtain ⟨hb, ho⟩ := I.tableDisjoint e he a had
    refine ⟨hb, ?_⟩
    intro hr
    rcases hnew a hr with h | ⟨hh, _⟩
    · exact ho h
    · exact (Nat.not_le_of_lt (hb.trans_le hbase)) hh

/-- The search and report frames give the next concrete loop state
with exactly one fewer pending edge. -/
theorem DetectLoopState.advance_after_search
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {handle base names inverse thresholds h L P edge reportHeap : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st found out : State}
    (I : DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf st)
    {tree : PathTreeState} {searchToken token : R.τ} {trees : List LinkCut.AuxTree}
    (hrep : R.rep handle tree token out.mem)
    (hinv : LinkCut.LctInvWith pathPayload tree trees I.free I.depth)
    (ha : DetectForestAccounts model P slotOf (I.written ++ [edge]).toFinset tree trees)
    (hc : ∀ slot, pathTreeReady tree slot → ∃ e ∈ model.extG.E, slotOf e = slot)
    (hn : (I.written ++ [edge]).Nodup)
    (hs : (I.written ++ [edge]).toFinset ⊆ (Chain.algorithm2_detect cfg model).1)
    (hpending : ((Chain.algorithm2_detect cfg model).1 \ (I.written ++ [edge]).toFinset).card + 1 =
      ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card)
    (hp : ListAt out.mem (base + 1) (I.written ++ [edge]))
    (hcursor : out.regs 8 = st.regs 8 + 1)
    (hheap : st.regs 1 ≤ reportHeap) (hret : reportHeap ≤ out.regs 1)
    (hz : ZeroFrom out.mem (out.regs 1))
    (hsearch : ∀ a < st.regs 1, ¬ R.foot handle I.token a → found.mem a = st.mem a)
    (hsearchFoot : ∀ a, R.foot handle searchToken a →
      R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < reportHeap))
    (hreport : ∀ a < reportHeap, ¬ R.foot handle searchToken a →
      a ≠ st.regs 8 → out.mem a = found.mem a)
    (hreportFoot : ∀ a, R.foot handle token a →
      R.foot handle searchToken a ∨ (reportHeap ≤ a ∧ a < out.regs 1)) :
    ∃ J : DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf out,
      J.tree = tree ∧ J.token = token ∧ J.written = I.written ++ [edge] ∧
      ((Chain.algorithm2_detect cfg model).1 \ J.written.toFinset).card + 1 =
        ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card := by
  obtain ⟨hf, hnew⟩ := detectLoopRound_frame hheap hret hsearch hsearchFoot hreport hreportFoot
  let J := I.append hrep hinv ha hc hn hs hp hcursor (hheap.trans hret) hz hf hnew
  exact ⟨J, rfl, rfl, rfl, hpending⟩

/-- Executing the ready branch after search produces the next loop
state and telescopes the tree potential across both operations. -/
theorem DetectLoopState.report_after_search
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {w L constant init handle base names inv slot src th heap prepare entry table P searchCost : ℕ}
    {fmt : Num.Format w} {p : Program} {st found : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op slotOf internalOf thresholdOf : ℕ → ℕ} {read : PathTreeState} {x : R.τ}
    {edge : PathEdgeValue} {threshold : ℤ}
    (I : DetectLoopState model R handle base names inv table fmt.limbBits L P
      slotOf internalOf thresholdOf st)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hr : pathTreeReady I.tree slot)
    (hread : read = LinkCut.lctExpose pathPayload (LinkCut.lctExpose pathPayload I.tree slot) slot)
    (hedge : ((LinkCut.lctExpose pathPayload I.tree slot).splay.nodes slot).val = some edge)
    (hname : ∀ e ∈ model.extG.E, slotOf e = slot → found.mem (inv + found.mem (names + slot)) = e)
    (hthreshold : threshold = detectorThreshold P cfg.ε
      (model.extℓ (found.mem (inv + found.mem (names + slot)))))
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    (hregs : found.regs 0 = handle ∧ found.regs 6 = names ∧ found.regs 7 = inv ∧
      found.regs 3 = slot ∧ found.regs 8 = st.regs 8 ∧ found.regs 4 = src ∧
      found.regs 10 = L ∧ found.regs 13 = heap ∧ found.regs 14 = table)
    (hth : found.mem (table + slot) = th) (htable : table + slot < 2 ^ w)
    (hadvance : st.regs 8 + 1 < 2 ^ w)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hp : MeetsContract w p prepare
      (detectSlotStepContract w fmt.limbBits (base + 1) I.written edge threshold))
    (hw : ∀ a ∈ [handle, names, inv, slot, st.regs 8, src, th, L, heap], a < 2 ^ w)
    (hpre : (detectSlotStepContract w fmt.limbBits (base + 1) I.written edge threshold).pre
      [names, inv, slot, st.regs 8, src, th, L, heap] found.mem)
    (hrep : R.rep handle read x found.mem)
    (hheap : st.regs 1 ≤ heap)
    (hframe : ∀ a < st.regs 1, ¬ R.foot handle I.token a → found.mem a = st.mem a)
    (hfoot : ∀ a, R.foot handle x a → R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < heap))
    (hwrite : ∀ mem', PathEdgeAt mem' heap fmt.limbBits L (some { edge with detector := -threshold }) →
      (pathTreeMachineContract fmt L constant allocation).pre 5 read
        [handle, slot, heap, heap + (2 + 4 * L)] mem')
    (hroom : heap + (2 + 4 * L) + allocation 5 read.n [handle, slot, heap, heap + (2 + 4 * L)] < 2 ^ w)
    (hcost : searchCost + R.phi handle x found.mem ≤
      2 * pathTreeBudget constant L I.tree.n + R.phi handle I.token st.mem + 14) :
    ∃ out cost, Runs w p ω (detectReadyReport entry) found .normal out cost ∧
      (∀ r, r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 11 → r ≠ 12 → out.regs r = found.regs r) ∧
      ∃ J : DetectLoopState model R handle base names inv table fmt.limbBits L P
        slotOf internalOf thresholdOf out,
        J.tree.n = I.tree.n ∧
        (∀ a < st.regs 1, ¬ R.foot handle I.token a → a ≠ st.regs 8 → out.mem a = st.mem a) ∧
        (∀ a, R.foot handle J.token a → R.foot handle I.token a ∨
          (st.regs 1 ≤ a ∧ a < out.regs 1)) ∧
        out.regs 1 ≤ heap + (2 + 4 * L) +
          allocation 5 read.n [handle, slot, heap, heap + (2 + 4 * L)] ∧
        ((Chain.algorithm2_detect cfg model).1 \ J.written.toFinset).card + 1 =
          ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card ∧
        searchCost + cost + R.phi handle J.token out.mem ≤
          2 * pathTreeBudget constant L I.tree.n + pathTreeBudget constant L read.n +
            R.phi handle I.token st.mem + 87 * L + 203 := by
  obtain ⟨e, he, hslot, _, _, hdec, _⟩ :=
    detectForestAccounts_ready_snoc model I.forestInv I.accounts hinj I.coverage heps hl
      I.nodup I.subset hr
  have hpositive : 0 < ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card := by omega
  have hcursor := I.cursor_bound.2 hpositive
  have hsearchBound : ∀ a, R.foot handle x a → a < heap := by
    intro a ha
    rcases hfoot a ha with hold | ⟨_, hnew⟩
    · exact (I.treeBound a hold).trans_le hheap
    · exact hnew
  have hbuffer : ∀ a, base ≤ a → a < base + 1 + model.extG.E.card →
      a < heap ∧ ¬ R.foot handle x a := by
    intro a ha hupper
    have hbelow := hupper.trans_le I.reserve
    refine ⟨hbelow.trans_le hheap, ?_⟩
    intro hcell
    rcases hfoot a hcell with hold | ⟨hnew, _⟩
    · exact I.bufferDisjoint a ha hupper hold
    · exact (Nat.not_le_of_lt hbelow) hnew
  have hcur := (hbuffer (st.regs 8) (by rw [I.cursor]; omega) hcursor).2
  have hreport : ∀ a, base + 1 ≤ a → a < base + 1 + I.written.length + 1 →
      a < heap ∧ ¬ R.foot handle x a := by
    intro a ha hb
    rw [I.cursor] at hcursor
    exact hbuffer a (by omega) (by omega)
  obtain ⟨trees', hi', ha', hc', hn', hs', hdec', ret, cost, out, y, hrun, hret,
    hnext, hsaved, hrep', hprefix, hz, hlo, hhi, hf, hfy, hcb⟩ :=
    detectReadyReport_model_runs (ω := ω) model I.written I.forestInv I.accounts hinj
      I.coverage heps hl I.nodup I.subset hr hread hedge hname hthreshold hentry hregs hth
      htable hadvance himpl hp hw hpre hrep hsearchBound hcur hreport hwrite hroom
  obtain ⟨J, htree, htoken, _, hJ⟩ := I.advance_after_search hrep' hi' ha' hc' hn' hs'
    hdec' hprefix hnext hheap (by rw [hret]; omega) (by rwa [hret]) hframe hfoot hf
    (by rwa [hret])
  obtain ⟨hframe', hfoot'⟩ :=
    detectLoopRound_frame hheap ((Nat.le_add_right heap _).trans hlo) hframe hfoot hf hfy
  refine ⟨out, cost, hrun, hsaved, J, ?_, hframe', ?_, hret.trans_le hhi, hJ, ?_⟩
  · rw [htree, hread]
    rfl
  · rwa [htoken, hret]
  · rw [htoken]
    omega

/-- The reserved prefix is a valid finalizer input at the current heap. -/
theorem DetectLoopState.finish_pre {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {w handle base names inverse thresholds h L P : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st : State}
    (I : DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf st) (hheap : st.regs 1 < 2 ^ w) :
    (detectFinishReservedContract w (st.regs 1) I.written).pre
      [base, I.written.length] st.mem := by
  have hprefix := (I.cursor_bound).1
  rw [I.cursor] at hprefix
  exact ⟨base, rfl, hprefix.trans I.reserve, hheap, I.nodup, I.prefixAt, I.zero⟩

/-- Searching does not change the reserved report prefix. The
finalizer may use the actual heap returned by the search. -/
theorem DetectLoopState.finish_pre_after_search
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {w handle base names inverse thresholds h L P heap : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st found : State}
    (I : DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf st)
    (hheap : st.regs 1 ≤ heap) (hword : heap < 2 ^ w)
    (hzero : ZeroFrom found.mem heap)
    (hframe : ∀ a < st.regs 1, ¬ R.foot handle I.token a → found.mem a = st.mem a) :
    (detectFinishReservedContract w heap I.written).pre [base, I.written.length] found.mem := by
  have hprefix := I.cursor_bound.1
  rw [I.cursor] at hprefix
  refine ⟨base, rfl, hprefix.trans (I.reserve.trans hheap), hword, I.nodup, ?_, hzero⟩
  apply I.prefixAt.congr
  intro a hlo hhi
  have ha := hhi.trans_le hprefix
  exact hframe a (ha.trans_le I.reserve) (I.bufferDisjoint a (by omega) ha)

/-- If the search finds no ready slot, the invariant's pending count is zero. -/
theorem DetectLoopState.exhausted_count
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {handle base names inverse thresholds h L P : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st : State}
    (I : DetectLoopState model R handle base names inverse thresholds h L P
      slotOf internalOf thresholdOf st)
    (hedge : ∀ e ∈ model.extG.E, LinkCut.isEdgeSlot I.tree.n (slotOf e))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hstop : ¬ ∃ slot, pathTreeReady I.tree slot) :
    ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card = 0 := by
  obtain ⟨heq, _⟩ := detectForestAccounts_exhausted model I.forestInv I.accounts
    hedge heps hlen I.subset (fun slot hr => hstop ⟨slot, hr⟩)
  rw [heq, Finset.sdiff_self, Finset.card_empty]

/-- The exhausted search and header write complete the final round.
The header is outside the tree, so finalizing the report preserves
both the tree representation and its potential. -/
theorem DetectLoopState.finish_after_search
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {w handle base names inverse thresholds heap finish m : ℕ}
    (F : IPM.Machine.MinRatioFormat w) {G : MGraph} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st found : State}
    {p : Program} {ω : ℕ → Bool} {y : R.τ}
    (I : DetectLoopState model R handle base names inverse thresholds F.fmt.limbBits F.limbs
      F.fmt.precision slotOf internalOf thresholdOf st)
    (hlocal : R.Local)
    (hfit : IPM.Machine.MinRatioStateFits (Chain.algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits
      F.limbs F.fmt.precision model)
    (hf : MeetsContract w p finish (detectFinishKeepHeapContract w heap I.written))
    (hbase : found.regs 17 = base) (hcursor : found.regs 8 = st.regs 8)
    (hheapReg : found.regs 2 = heap)
    (hheap : st.regs 1 ≤ heap) (hword : heap < 2 ^ w)
    (hzero : ZeroFrom found.mem heap)
    (hframe : ∀ a < st.regs 1, ¬ R.foot handle I.token a → found.mem a = st.mem a)
    (hnew : ∀ a, R.foot handle y a → R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < heap))
    (hrep : R.rep handle I.tree y found.mem)
    (hedge : ∀ e ∈ model.extG.E, LinkCut.isEdgeSlot I.tree.n (slotOf e))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hstop : ¬ ∃ slot, pathTreeReady I.tree slot) :
    ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card = 0 ∧
    ∃ out cost,
      Runs w p ω (detectExhaustedBranch finish) found (.returned heap) out cost ∧
      (IPM.Machine.minRatioMachineContract F (Chain.algorithm2_dsWithFailureWith cfg κ) G
        m κ α rate allocation).post 2 model [handle, base] found.mem
        (Chain.algorithm2_detect cfg model).2 out.mem ∧
      DetectForestAccounts (Chain.algorithm2_detect cfg model).2 F.fmt.precision
        slotOf ∅ I.tree I.trees ∧
      R.rep handle I.tree y out.mem ∧ R.phi handle y out.mem = R.phi handle y found.mem ∧
      ZeroFrom out.mem heap ∧
      (∀ a < st.regs 1, ¬ R.foot handle I.token a → a ≠ base → out.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < heap)) ∧
      cost ≤ 27 := by
  refine ⟨I.exhausted_count hedge heps hlen hstop, ?_⟩
  obtain ⟨out, cost, hrun, hmodel, haccounts, hp, hcost⟩ :=
    detectExhaustedBranch_model_runs (m := m) (κ := κ) (α := α) (rate := rate)
      (allocation := allocation) (ω := ω) F cfg I.written hf hbase (hcursor.trans I.cursor)
      hheapReg (I.finish_pre_after_search hheap hword hzero hframe) hfit
      I.forestInv I.accounts hedge heps hlen I.subset hstop
  have hframe' : ∀ a, a ≠ base → out.mem a = found.mem a := hp.2.2.2.1
  have hbaseHeap : base < st.regs 1 := by
    have := I.reserve
    omega
  have hloc := hlocal handle I.tree y found.mem out.mem (fun a ha => by
    apply Eq.symm
    apply hframe' a
    intro heq
    subst a
    rcases hnew base ha with ho | ⟨hl, _⟩
    · exact I.bufferDisjoint base le_rfl
        (by omega) ho
    · exact (Nat.not_le_of_lt hbaseHeap) hl)
  exact ⟨out, cost, hrun, hmodel, haccounts, hloc.1 hrep, hloc.2.symm, hp.2.2.2.2,
    fun a ha ho hb => (hframe' a hb).trans (hframe a ha ho), hnew, hcost⟩

/-- Set both workspace bounds, then search and read under the live
tree representation. All arguments outside the scratch registers
survive, and the returned frame refers to the original loop state. -/
theorem DetectLoopState.search_runs
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {w L constant init handle base names inv table P searchSpace readSpace : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op slotOf internalOf thresholdOf : ℕ → ℕ}
    (I : DetectLoopState model R handle base names inv table fmt.limbBits L P
      slotOf internalOf thresholdOf st)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hh : st.regs 0 = handle) (hhw : handle < 2 ^ w)
    (hs : st.regs 15 = searchSpace) (hr : st.regs 16 = readSpace)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 6 I.tree
      [handle, st.regs 1] st.mem)
    (hspace : allocation 6 I.tree.n [handle, st.regs 1] ≤ searchSpace)
    (hroom : st.regs 1 + searchSpace + readSpace < 2 ^ w)
    (hread : ∀ slot mem, pathTreeReady I.tree slot →
      (pathTreeMachineContract fmt L constant allocation).pre 4
        (LinkCut.lctExpose pathPayload I.tree slot) [handle, slot, st.regs 1 + searchSpace] mem ∧
      allocation 4 I.tree.n [handle, slot, st.regs 1 + searchSpace] ≤ readSpace) :
    let top := st.regs 1 + searchSpace
    ∃ (setup found : State) (tree : PathTreeState) (cost ret slot : ℕ) (y : R.τ),
      Runs w p ω detectWorkspaceArgs st .normal setup 9 ∧
      Runs w p ω (detectSearchRead (op 6) (op 4)) setup .normal found cost ∧
      found.regs 3 = slot ∧ found.regs 4 = top ∧ found.regs 13 = top + readSpace ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 13 → found.regs r = st.regs r) ∧
      R.rep handle tree y found.mem ∧ ZeroFrom found.mem ret ∧ st.regs 1 ≤ ret ∧
      (∀ a < st.regs 1, ¬ R.foot handle I.token a → found.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < ret)) ∧
      (if slot = 0 then tree = I.tree ∧ ret ≤ top ∧ found.regs 2 = ret ∧
        ¬ ∃ a, pathTreeReady I.tree a
      else pathTreeReady I.tree slot ∧ tree = LinkCut.lctExpose pathPayload
          (LinkCut.lctExpose pathPayload I.tree slot) slot ∧
        found.regs 5 = ret ∧ top ≤ ret ∧ ret ≤ top + readSpace ∧
        PathEdgeAt found.mem top fmt.limbBits L
          ((LinkCut.lctExpose pathPayload I.tree slot).splay.nodes slot).val) ∧
      cost + R.phi handle y found.mem ≤
        2 * pathTreeBudget constant L I.tree.n + R.phi handle I.token st.mem + 14 := by
  dsimp only
  obtain ⟨setup, hsetup, htop, hend, hregs, hmem, _⟩ :=
    detectWorkspaceArgs_runs (ω := ω) rfl hs hr hroom
  have hargs : setup.regs 0 = handle ∧ setup.regs 1 = st.regs 1 :=
    ⟨(hregs 0 (by decide) (by decide)).trans hh, hregs 1 (by decide) (by decide)⟩
  obtain ⟨tree, cost, ret, slot, found, y, hrun, hslot, hfound, hrep, hz, hlo, hf, hfoot,
    hresult, hc⟩ :=
    detectSearchRead_runs (ω := ω) himpl hargs hhw (by rwa [hmem]) (by rw [hmem]; exact I.treeRep)
      I.treeBound (by rw [hmem]; exact I.zero) (Nat.add_le_add_left hspace _) htop (by omega)
      (fun slot mem hready => by
        obtain ⟨hp, hbound⟩ := hread slot mem hready
        refine ⟨hp, ?_⟩
        change st.regs 1 + searchSpace + allocation 4 I.tree.n
          [handle, slot, st.regs 1 + searchSpace] < 2 ^ w
        exact (Nat.add_le_add_left hbound _).trans_lt hroom)
  refine ⟨setup, found, tree, cost, ret, slot, y, hsetup, hrun, hslot,
    (hfound 4 (by decide) (by decide) (by decide)).trans htop,
    (hfound 13 (by decide) (by decide) (by decide)).trans hend,
    fun r h2 h3 h4 h5 h13 => (hfound r h2 h3 h5).trans (hregs r h4 h13),
    hrep, hz, hlo, ?_, hfoot, ?_, ?_⟩
  · simpa only [hmem] using hf
  · by_cases hzslot : slot = 0 <;> simp only [hzslot, ite_true, ite_false] at hresult ⊢
    · exact hresult
    · obtain ⟨ha, ht, h5, htopRet, hret, hv⟩ := hresult
      exact ⟨ha, ht, h5, htopRet, hret.trans (Nat.add_le_add_left (hread slot found.mem ha).2 _), hv⟩
  · rwa [hmem] at hc

/-- After a ready search, the preserved tables and prefix supply the
reset and append arguments for the edge in the returned record. -/
theorem DetectLoopState.report_pre_after_search
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {R : DSRep PathTreeState} {w handle base names inv table h L P slot src heap : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {st found : State} {value : PathEdgeValue}
    (I : DetectLoopState model R handle base names inv table h L P
      slotOf internalOf thresholdOf st)
    (hready : pathTreeReady I.tree slot)
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hwords : ∀ e ∈ model.extG.E, e < 2 ^ w)
    (hthree : 3 < 2 ^ w) (hheap : st.regs 1 ≤ heap)
    (hreadEnd : src + (2 + 4 * L) ≤ heap)
    (hresetEnd : heap + (2 + 4 * L) < 2 ^ w)
    (hread : PathEdgeAt found.mem src h L (some value))
    (hz : ZeroFrom found.mem heap)
    (hf : ∀ a < st.regs 1, ¬ R.foot handle I.token a → found.mem a = st.mem a) :
    ∃ e ∈ model.extG.E, slotOf e = slot ∧
      (∀ e' ∈ model.extG.E, slotOf e' = slot → found.mem (inv + found.mem (names + slot)) = e') ∧
      found.mem (table + slot) = thresholdOf e ∧
      table + slot < 2 ^ w ∧ st.regs 8 + 1 < 2 ^ w ∧
      (detectSlotStepContract w h (base + 1) I.written value
        (detectorThreshold P cfg.ε (model.extℓ e))).pre
        [names, inv, slot, st.regs 8, src, thresholdOf e, L, heap] found.mem := by
  obtain ⟨e, he, hs⟩ := I.coverage slot hready
  have hbase : base < st.regs 1 := by have := I.reserve; omega
  have ht := I.tables.congr (mem' := found.mem) (fun e he a ha => by
    obtain ⟨hb, ho⟩ := I.tableDisjoint e he a ha
    exact hf a (hb.trans hbase) ho)
  have hnames := (I.tableDisjoint e he _ (Or.inl rfl)).1
  have hinv := (I.tableDisjoint e he _ (Or.inr (Or.inl rfl))).1
  have htable := (I.tableDisjoint e he _ (Or.inr (Or.inr (Or.inl rfl)))).1
  rw [hs] at hnames htable
  have hthEnd : thresholdOf e + L ≤ heap := by
    by_cases hL : L = 0
    · have hfit := Num.intVal_fits (ht e he).2.2.2.1
      rw [(ht e he).2.2.2.2, hL] at hfit
      have hpos := detectorThreshold_pos P cfg.ε (model.extℓ e) heps (hlen e he)
      change -(1 : ℤ) ≤ 2 * detectorThreshold P cfg.ε (model.extℓ e) ∧
        2 * detectorThreshold P cfg.ε (model.extℓ e) < 1 at hfit
      omega
    · have ha : thresholdOf e + L - 1 < base :=
        (I.tableDisjoint e he _ (Or.inr (Or.inr (Or.inr (by omega))))).1
      omega
  have hedge := ((pathTreeReady_iff_forestPairs I.forestInv slot).mp hready).1
  have hnonempty := detectForestAccounts_point model I.forestInv I.accounts he
    (hs.symm ▸ hedge) heps (hlen e he)
  obtain ⟨_, _, _, hpending⟩ := hnonempty
  have hmem := hpending.mp (hs.symm ▸ hready)
  have hcursor := I.cursor_bound.2 (Finset.card_pos.mpr ⟨e, hmem⟩)
  have hw : heap < 2 ^ w := by omega
  obtain ⟨a, hargs, _, _, _, hprefix, _⟩ := I.finish_pre_after_search hheap hw hz hf
  have ha : base = a := (List.cons.inj hargs).1
  subst a
  obtain ⟨hp, hpre⟩ := ht.slotStep_pre he hs I.cursor (by rw [I.cursor]; omega)
    (by rw [I.cursor]; omega) (hwords e he) (hcursor.trans_le (I.reserve.trans hheap))
    hthree hreadEnd hthEnd hresetEnd hread heps (hlen e he) hprefix hz
  exact ⟨e, he, hs, fun e' he' hs' => ht.externalName he' hs', hp, by omega, by
    have := I.reserve
    omega, hpre⟩

/-- The search output supplies every ready-branch argument. Only
the linked procedure and its point-write fit and allocation bounds
are needed in addition to the tree and table representations. -/
theorem DetectLoopState.ready_after_search
    {cfg : Chain.Alg2Config} {model : Chain.Alg2State cfg}
    {w L constant init handle base names inv slot src heap prepare entry table P searchCost : ℕ}
    {fmt : Num.Format w} {p : Program} {st found : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op slotOf internalOf thresholdOf : ℕ → ℕ} {read : PathTreeState} {x : R.τ}
    (I : DetectLoopState model R handle base names inv table fmt.limbBits L P
      slotOf internalOf thresholdOf st)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hr : pathTreeReady I.tree slot)
    (hread : read = LinkCut.lctExpose pathPayload (LinkCut.lctExpose pathPayload I.tree slot) slot)
    (hrecord : PathEdgeAt found.mem src fmt.limbBits L
      ((LinkCut.lctExpose pathPayload I.tree slot).splay.nodes slot).val)
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    (hregs : found.regs 0 = handle ∧ found.regs 6 = names ∧ found.regs 7 = inv ∧
      found.regs 3 = slot ∧ found.regs 8 = st.regs 8 ∧ found.regs 4 = src ∧
      found.regs 10 = L ∧ found.regs 13 = heap ∧ found.regs 14 = table)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hprepare : ∀ value threshold, MeetsContract w p prepare
      (detectSlotStepContract w fmt.limbBits (base + 1) I.written value threshold))
    (hh : handle < 2 ^ w) (hthree : 3 < 2 ^ w)
    (hwords : ∀ e ∈ model.extG.E, e < 2 ^ w)
    (hrep : R.rep handle read x found.mem)
    (hheap : st.regs 1 ≤ heap) (hreadEnd : src + (2 + 4 * L) ≤ heap)
    (hz : ZeroFrom found.mem heap)
    (hframe : ∀ a < st.regs 1, ¬ R.foot handle I.token a → found.mem a = st.mem a)
    (hfoot : ∀ a, R.foot handle x a → R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < heap))
    (hwrite : ∀ value e mem', e ∈ model.extG.E → slotOf e = slot →
      ((LinkCut.lctExpose pathPayload I.tree slot).splay.nodes slot).val = some value →
      PathEdgeAt mem' heap fmt.limbBits L
        (some { value with detector := -detectorThreshold P cfg.ε (model.extℓ e) }) →
      (pathTreeMachineContract fmt L constant allocation).pre 5 read
        [handle, slot, heap, heap + (2 + 4 * L)] mem')
    (hroom : heap + (2 + 4 * L) + allocation 5 read.n [handle, slot, heap, heap + (2 + 4 * L)] < 2 ^ w)
    (hcost : searchCost + R.phi handle x found.mem ≤
      2 * pathTreeBudget constant L I.tree.n + R.phi handle I.token st.mem + 14) :
    ∃ out cost, Runs w p ω (detectReadyReport entry) found .normal out cost ∧
      (∀ r, r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 11 → r ≠ 12 → out.regs r = found.regs r) ∧
      ∃ J : DetectLoopState model R handle base names inv table fmt.limbBits L P
        slotOf internalOf thresholdOf out,
        J.tree.n = I.tree.n ∧
        (∀ a < st.regs 1, ¬ R.foot handle I.token a → a ≠ st.regs 8 → out.mem a = st.mem a) ∧
        (∀ a, R.foot handle J.token a → R.foot handle I.token a ∨
          (st.regs 1 ≤ a ∧ a < out.regs 1)) ∧
        out.regs 1 ≤ heap + (2 + 4 * L) +
          allocation 5 read.n [handle, slot, heap, heap + (2 + 4 * L)] ∧
        ((Chain.algorithm2_detect cfg model).1 \ J.written.toFinset).card + 1 =
          ((Chain.algorithm2_detect cfg model).1 \ I.written.toFinset).card ∧
        searchCost + cost + R.phi handle J.token out.mem ≤
          3 * pathTreeBudget constant L I.tree.n + R.phi handle I.token st.mem + 87 * L + 203 := by
  obtain ⟨_, _, value, hv, _⟩ := (show pathTreeReady I.tree slot from hr)
  rw [hv] at hrecord
  have hresetEnd : heap + (2 + 4 * L) < 2 ^ w := by omega
  obtain ⟨e, he, hs, hname, hth, htword, hcursor, hpre⟩ :=
    I.report_pre_after_search hr heps hl hwords hthree hheap hreadEnd hresetEnd hrecord hz hframe
  have hthreshold : detectorThreshold P cfg.ε (model.extℓ e) =
      detectorThreshold P cfg.ε (model.extℓ (found.mem (inv + found.mem (names + slot)))) := by
    rw [hname e he hs]
  have hwordArgs : ∀ a ∈ [handle, names, inv, slot, st.regs 8, src, thresholdOf e, L, heap],
      a < 2 ^ w := by
    have hb := I.reserve
    have hn := (I.tableDisjoint e he _ (Or.inl rfl)).1
    have hi := (I.tableDisjoint e he _ (Or.inr (Or.inl rfl))).1
    obtain ⟨n, i, sl, cu, sr, th, limbs, hp, heq, hreset, _⟩ := hpre
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨sr, th, limbs, hp, heq, _, _, hthEnd, _, _, _, _, _⟩ := hreset
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨out, cost, hrun, hsaved, J, hnJ, hframe', hfoot', hheapEnd, hdec, hc⟩ :=
    I.report_after_search hinj heps hl hr hread hv hname hthreshold hentry hregs hth htword
      hcursor himpl (hprepare _ _) hwordArgs hpre hrep hheap hframe hfoot (hwrite value e · he hs hv)
      hroom hcost
  have hn : read.n = I.tree.n := by rw [hread]; rfl
  rw [hn] at hc
  exact ⟨out, cost, hrun, hsaved, J, hnJ, hframe', hfoot', hheapEnd, hdec, by omega⟩

/-- Once the search and branch proofs transport the concrete report
invariant, the linked loop returns the exhausted state and charges
one round for each remaining report plus the final search. -/
theorem detectLoopProgram_runs {w find read report finish : ℕ}
    {p : Program} {ω : ℕ → Bool}
    {Inv : ℕ → ℕ → State → Prop} {Done : ℕ → ℕ → State → Prop}
    (hw : 1 < 2 ^ w) (readyBudget finalBudget : ℕ)
    (hround : ∀ remaining potential st, Inv remaining potential st →
      ∃ setup found out searchCost branchCost slot outcome,
        Runs w p ω detectWorkspaceArgs st .normal setup 9 ∧
        Runs w p ω (detectSearchRead find read) setup .normal found searchCost ∧
        found.regs 3 = slot ∧
        Runs w p ω
          (if slot = 0 then detectExhaustedBranch finish else detectReadyReport report)
          found outcome out branchCost ∧
        match outcome with
        | .normal => ∃ nextPotential, 0 < remaining ∧ Inv (remaining - 1) nextPotential out ∧
            searchCost + branchCost + nextPotential ≤ readyBudget + potential
        | .returned ret => ∃ nextPotential, remaining = 0 ∧ Done ret nextPotential out ∧
            searchCost + branchCost + nextPotential ≤ finalBudget + potential)
    {remaining potential : ℕ} {st : State} (hin : Inv remaining potential st) :
    ∃ ret out cost finalPotential,
      Runs w p ω (detectLoopProgram find read report finish) st (.returned ret) out cost ∧
      Done ret finalPotential out ∧
      cost + finalPotential ≤ remaining * (readyBudget + 15) + finalBudget + 15 + potential := by
  unfold detectLoopProgram
  obtain ⟨ret, out, cost, phi, hrun, hdone, hc⟩ :=
    detectReportingLoop_runs (ω := ω) hw (readyBudget + 13) (finalBudget + 13)
      (search := detectLoopSearch find read) (report := detectReadyReport report)
      (finish := detectExhaustedBranch finish) (Done := Done)
      (fun remaining potential st hi => by
        obtain ⟨setup, found, out, c, d, slot, o, hs, hf, hr, hb, hp⟩ :=
          hround remaining potential st hi
        refine ⟨o, out, c + d + 13, detectLoopRound_runs hs hf hr hb, ?_⟩
        cases o with
        | normal =>
          obtain ⟨phi, hpos, hnext, hc⟩ := hp
          exact ⟨phi, hpos, hnext, by omega⟩
        | returned ret =>
          obtain ⟨phi, hzero, hdone, hc⟩ := hp
          exact ⟨phi, hzero, hdone, by omega⟩) hin
  exact ⟨ret, out, cost, phi, hrun, hdone, hc⟩

end MinCostFlow.MinRatio
