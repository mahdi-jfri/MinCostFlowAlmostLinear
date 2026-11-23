module

public import MinCostFlow.HierPaths.BuildProgApplyRow

/-!
# Applying the common matching batch

The cut indices align the router's rows with the original active children.
Each iteration appends one row to its child graph, then records that row's
walks in a shared arena. The first flattened edge number indexes the row in
the walk directory.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The immutable input to the matching-application scan. -/
structure ApplyBatchData where
  jobs : BuildGameJobs
  indices : List ℕ
  matchings : List (List (ℕ × ℕ))
  emb : ℕ → List ℕ
  host : Graph

/-- The active-child index of router row `i`. -/
def ApplyBatchData.child (D : ApplyBatchData) (i : ℕ) : ℕ := D.indices.getD i 0

/-- The child's local graph before this round. -/
def ApplyBatchData.graph (D : ApplyBatchData) (i : ℕ) : Graph := D.jobs.graph (D.child i)

/-- The base of the child graph for router row `i`. -/
def ApplyBatchData.addr (D : ApplyBatchData) (i : ℕ) : ℕ := D.jobs.addr (D.child i)

/-- The parent offset of the child for router row `i`. -/
def ApplyBatchData.offset (D : ApplyBatchData) (i : ℕ) : ℕ := D.jobs.offset (D.child i)

/-- The routed walk row of the child. -/
def ApplyBatchData.row (D : ApplyBatchData) (i : ℕ) : BuildWalkRow :=
  matchingWalkRow D.matchings D.emb i

/-- The number of endpoint pairs in the graph after the row is written. -/
def ApplyBatchData.cap (D : ApplyBatchData) (i : ℕ) : ℕ :=
  D.addr i + 2 + 2 * ((D.graph i).m + (D.row i).count)

/-- The arena cursor after the first `i` rows. -/
def ApplyBatchData.cursor (D : ApplyBatchData) (out : ℕ) : ℕ → ℕ
  | 0 => out
  | i + 1 => (D.row i).cursor (D.cursor out i) (D.row i).count

/-- The directory interval reserved to row `i`. -/
def ApplyBatchData.directory (D : ApplyBatchData) (dir i : ℕ) : ℕ :=
  dir + (D.row i).first

/-- The graph and all walk directory entries of a completed row are stored in memory. -/
def ApplyBatchData.RowAt (D : ApplyBatchData) (mem : ℕ → ℕ) (dir out i : ℕ) : Prop :=
  let r := D.row i
  GraphAt mem (D.addr i) (appendGameMatching (D.graph i) (D.offset i) (D.matchings.getD i [])) ∧
  ∀ j < r.count, mem (D.directory dir i + j) = r.cursor (D.cursor out i) j ∧
    SeqAt mem (r.cursor (D.cursor out i) j) (erase D.host.edges (r.u j) (r.raw j))

/-- The first scan input contains the candidate child indices, graph addresses, and offsets. -/
structure ApplyBatchTables (D : ApplyBatchData) (mem : ℕ → ℕ)
    (idx graphs offsets : ℕ) : Prop where
  indices : ListAt mem idx D.indices
  graphsAt : ListAt mem graphs (tabList D.jobs.count D.jobs.addr)
  offsetsAt : ListAt mem offsets (tabList D.jobs.count D.jobs.offset)
  count : D.indices.length = D.matchings.length
  child : ∀ i < D.matchings.length, D.child i < D.jobs.count
  indicesApart : ∀ i < D.matchings.length,
    idx + D.indices.length ≤ D.addr i ∨ D.cap i ≤ idx
  beforeGraph : ∀ i < D.matchings.length,
    graphs + D.jobs.count ≤ D.addr i ∧ offsets + D.jobs.count ≤ D.addr i

/-- Each row fits its own graph interval and its part of the common directory and arena. -/
structure ApplyBatchFit (w : ℕ) (D : ApplyBatchData)
    (mt tb tmp ends vs P dir out : ℕ) : Prop where
  offsetsWord : ∀ i < D.matchings.length, D.offset i < 2 ^ w
  fit : ∀ i < D.matchings.length, ApplyRowFit w D.host (D.graph i) D.matchings D.emb
    i mt tb tmp (D.addr i) ends vs P (D.directory dir i) (D.cursor out i)
  disjoint : ∀ i < D.matchings.length, ∀ j < D.matchings.length, i ≠ j →
    D.cap i ≤ D.addr j ∨ D.cap j ≤ D.addr i
  packet : tmp + 4 ≤ dir
  dirs : dir + D.matchings.flatten.length ≤ vs
  scratch : vs ≤ P
  posEnd : P + D.host.n ≤ out
  word : D.cursor out D.matchings.length < 2 ^ w
  one : 1 < 2 ^ w

/-- Read the active index and the first flattened edge, then apply that row. -/
def buildApplyBatchStep (f : ℕ) : Stmt :=
  .seq (.assign 13 (.load (.bin .add (.reg 3) (.reg 12))))
    (.seq (.assign 14 (.bin .div (.load (.bin .add (.reg 0) (.reg 12))) (.const 2)))
      (.seq (.call 15 f [.reg 0, .reg 1, .reg 2, .reg 12, .reg 6,
          .load (.bin .add (.reg 4) (.reg 13)), .load (.bin .add (.reg 5) (.reg 13)),
          .reg 7, .reg 8, .reg 9, .bin .add (.reg 10) (.reg 14), .reg 11])
        (.assign 11 (.reg 15))))

/-- Args are `[matchTable, walks, rows, indices, graphs, offsets, tmp, ends, verts,
positions, directory, heap]`. -/
def buildApplyBatchProc (f : ℕ) : Stmt :=
  .seq (forRange 12 (.const 0) (.reg 2) (buildApplyBatchStep f)) (.ret (.reg 11))

theorem buildApplyBatchProc_noRand (f : ℕ) : (buildApplyBatchProc f).NoRand := by
  simp [buildApplyBatchProc, buildApplyBatchStep, forRange, forUp, Stmt.NoRand]

/-- All original cells outside the graph updates and below the packet stay fixed. -/
def ApplyBatchData.Kept (D : ApplyBatchData) (tmp count a : ℕ) : Prop :=
  a < tmp ∧ ∀ j < count, a < D.addr j ∨ D.cap j ≤ a

/-- The batch scan cost pays for the shortcut of each raw edge occurrence. -/
def applyBatchStepCost (D : ApplyBatchData) (i : ℕ) : ℕ :=
  let R := D.row i
  rangeCost (fun j => 136 * (R.raw j).length + 330) 0 R.count + 47 * R.count + 320

/-- The application scan appends each row to its own graph and stores its walks. -/
def buildApplyBatchContract (w : ℕ) (D : ApplyBatchData) : Contract where
  pre args mem := ∃ mt tb idx graphs offsets tmp ends vs P dir out,
    args = [mt, tb, D.matchings.length, idx, graphs, offsets, tmp, ends, vs, P, dir, out] ∧
    ApplyBatchTables D mem idx graphs offsets ∧ idx + D.indices.length ≤ mt ∧ ApplyBatchFit w D mt tb tmp ends vs P dir out ∧
    D.host.IsValid ∧ ListAt mem mt (csrList D.matchings.length (matchingRowWords D.matchings)) ∧
    ListAt mem tb (csrList D.matchings.flatten.length D.emb) ∧
    ListAt mem ends (D.host.edges.flatMap fun e => [e.1, e.2]) ∧
    (∀ i < D.matchings.length, GraphAt mem (D.addr i) (D.graph i) ∧
      (∀ e ∈ D.matchings.getD i [], D.offset i ≤ e.1 ∧ D.offset i ≤ e.2 ∧ e.1 < 2 ^ w ∧ e.2 < 2 ^ w) ∧
      ∀ j < (D.row i).count, (D.row i).u j < D.host.n ∧
        IsEdgeWalk D.host.edges ((D.row i).u j) ((D.row i).v j) ((D.row i).raw j)) ∧
    ZeroFrom mem out ∧ (∀ a < D.host.n, mem (P + a) = 0)
  post args mem v mem' := ∃ mt tb idx graphs offsets tmp ends vs P dir out,
    args = [mt, tb, D.matchings.length, idx, graphs, offsets, tmp, ends, vs, P, dir, out] ∧
    v = D.cursor out D.matchings.length ∧ ZeroFrom mem' v ∧
    (∀ a < D.host.n, mem' (P + a) = 0) ∧
    (∀ a, D.Kept tmp D.matchings.length a → mem' a = mem a) ∧
    ∀ i < D.matchings.length, D.RowAt mem' dir out i
  cost _ _ := rangeCost (applyBatchStepCost D) 0 D.matchings.length + 9 * D.matchings.length + 16

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The arena grows as the application scan advances over the matching rows. -/
theorem ApplyBatchData.cursor_mono (D : ApplyBatchData) (out : ℕ) : Monotone (D.cursor out) := by
  apply monotone_nat_of_le_succ
  intro i
  exact (D.row i).cursor_mono (D.cursor out i) (Nat.zero_le _)

private theorem graphWords_length (G : Graph) : G.encode.length = 2 + 2 * G.m := by
  simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]
  omega

private theorem cap_eq_appended (D : ApplyBatchData) (i : ℕ) :
    D.addr i + (appendGameMatching (D.graph i) (D.offset i) (D.matchings.getD i [])).encode.length =
      D.cap i := by
  rw [graphWords_length]
  simp only [ApplyBatchData.cap, ApplyBatchData.row, matchingWalkRow, appendGameMatching, Graph.m,
    List.length_append, List.length_map]
  omega

private theorem ApplyBatchData.kept_next {D : ApplyBatchData} {tmp i a : ℕ}
    (h : D.Kept tmp (i + 1) a) : D.Kept tmp i a :=
  ⟨h.1, fun j hj => h.2 j (hj.trans (Nat.lt_succ_self i))⟩

private theorem ApplyBatchData.kept_of_before {D : ApplyBatchData} {tmp i a : ℕ}
    (hTmp : a < tmp) (hb : ∀ j < i, a < D.addr j) : D.Kept tmp i a :=
  ⟨hTmp, fun j hj => Or.inl (hb j hj)⟩

private theorem ApplyBatchData.keep_below_packet {D : ApplyBatchData}
    {i tmp vs P dir out a : ℕ}
    (hdir : tmp ≤ D.directory dir i)
    (ha : a < tmp) (hg : a < D.addr i ∨ D.cap i ≤ a) :
    ApplyRowKept (D.addr i + 2 + 2 * (D.graph i).m) (D.cap i)
      tmp (D.row i).count vs P (D.directory dir i) out (D.addr i) a := by
  have hb : D.addr i + 2 ≤ D.cap i := by unfold ApplyBatchData.cap; omega
  exact ⟨by omega, by omega, Or.inl ha, Or.inl (ha.trans_le hdir)⟩

private theorem ApplyBatchData.dir_start_le {D : ApplyBatchData} {dir i : ℕ} :
    dir ≤ D.directory dir i := Nat.le_add_right _ _

private theorem ApplyBatchData.dir_end_le {D : ApplyBatchData} {dir i : ℕ}
    (hi : i < D.matchings.length) :
    D.directory dir i + (D.row i).count ≤ dir + D.matchings.flatten.length := by
  have h := matchingRow_end_le hi
  change flatIndex D.matchings i 0 + (D.matchings.getD i []).length ≤ _ at h
  change dir + flatIndex D.matchings i 0 + (D.matchings.getD i []).length ≤ _
  omega

private theorem ApplyBatchData.dir_order {D : ApplyBatchData} {dir i j : ℕ}
    (hi : i < D.matchings.length) (hij : i < j) :
    D.directory dir i + (D.row i).count ≤ D.directory dir j := by
  change dir + flatIndex D.matchings i 0 + (D.matchings.getD i []).length ≤
    dir + flatIndex D.matchings j 0
  rw [Nat.add_assoc, ← matchingRow_first_succ hi]
  exact Nat.add_le_add_left (matchingRow_first_mono D.matchings (by omega)) _

private def applyBatchInv (D : ApplyBatchData) (mt tb idx graphs offsets tmp ends vs P dir out : ℕ)
    (mem : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = mt ∧ st.regs 1 = tb ∧ st.regs 2 = D.matchings.length ∧ st.regs 3 = idx ∧
    st.regs 4 = graphs ∧ st.regs 5 = offsets ∧ st.regs 6 = tmp ∧ st.regs 7 = ends ∧
    st.regs 8 = vs ∧ st.regs 9 = P ∧ st.regs 10 = dir ∧ st.regs 11 = D.cursor out i ∧
    st.regs 12 = i ∧ ZeroFrom st.mem (D.cursor out i) ∧
    (∀ a < D.host.n, st.mem (P + a) = 0) ∧ (∀ a, D.Kept tmp i a → st.mem a = mem a) ∧
    ∀ j < i, D.RowAt st.mem dir out j

private theorem applyBatch_step {w mt tb idx graphs offsets tmp ends vs P dir out i f : ℕ}
    {p : Program} {D : ApplyBatchData} {mem : ℕ → ℕ}
    (hProc : ∀ j < D.matchings.length, MeetsContract w p f
      (buildApplyRowContract w j D.host (D.graph j) D.matchings D.emb))
    (hArgs : ∀ a ∈ [mt, tb, D.matchings.length, idx, graphs, offsets, tmp, ends, vs, P, dir, out],
      a < 2 ^ w)
    (hTables : ApplyBatchTables D mem idx graphs offsets) (hIdxRoom : idx + D.indices.length ≤ mt)
    (hFit : ApplyBatchFit w D mt tb tmp ends vs P dir out)
    (hG : D.host.IsValid) (hM : ListAt mem mt (csrList D.matchings.length (matchingRowWords D.matchings)))
    (hT : ListAt mem tb (csrList D.matchings.flatten.length D.emb))
    (hE : ListAt mem ends (D.host.edges.flatMap fun e => [e.1, e.2]))
    (hRows : ∀ j < D.matchings.length, GraphAt mem (D.addr j) (D.graph j) ∧
      (∀ e ∈ D.matchings.getD j [], D.offset j ≤ e.1 ∧ D.offset j ≤ e.2 ∧ e.1 < 2 ^ w ∧ e.2 < 2 ^ w) ∧
      ∀ t < (D.row j).count, (D.row j).u t < D.host.n ∧
        IsEdgeWalk D.host.edges ((D.row j).u t) ((D.row j).v t) ((D.row j).raw t))
    (hi : i < D.matchings.length) :
    Triple w p (applyBatchInv D mt tb idx graphs offsets tmp ends vs P dir out mem i)
      (buildApplyBatchStep f)
      (normalPost fun st => applyBatchInv D mt tb idx graphs offsets tmp ends vs P dir out mem (i + 1)
        { st with regs := Function.update st.regs 12 (i + 1) } ∧ st.regs 12 = i)
      (fun _ => applyBatchStepCost D i) := by
  intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,hZero,hPos,hFrame,hPrev⟩
  let top := D.cursor out i
  let g := D.addr i
  let rowDir := D.directory dir i
  let child := D.child i
  let R := D.row i
  have hCur := hFit.fit i hi
  have htmpw := hArgs tmp (by simp)
  have hDirBound := hFit.dirs
  have hPacket := hFit.packet
  have hVsP := hFit.scratch
  have hPosEnd := hFit.posEnd
  have hTop : out ≤ top := D.cursor_mono out (Nat.zero_le i)
  have hTopW : top < 2 ^ w := (D.cursor_mono out hi.le).trans_lt hFit.word
  have hChild : child < D.jobs.count := hTables.child _ hi
  have hi' : i < D.indices.length := by rw [hTables.count]; exact hi
  have hMcap : ∀ j < D.matchings.length, D.cap j ≤ mt := fun j hj => (hFit.fit j hj).graphMatch
  have hTcap : ∀ j < D.matchings.length, D.cap j ≤ tb := fun j hj => (hFit.fit j hj).graphWalk
  have hGtmp : ∀ j < D.matchings.length, D.addr j ≤ tmp := fun j hj => by
    have hm := hMcap j hj
    have hmt := hCur.matchPacket
    unfold ApplyBatchData.cap at hm
    omega
  have hTablesBelow (a : ℕ) (ha : ∀ j < D.matchings.length, a < D.addr j) : st.mem a = mem a :=
    hFrame a (ApplyBatchData.kept_of_before ((ha i hi).trans_le (hGtmp i hi))
        (fun j hj => ha j (hj.trans hi)))
  have hCutAt : st.mem (idx + i) = child := by
    have hStable : st.mem (idx + i) = mem (idx + i) := hFrame _ (by
      have hMtTmp : mt ≤ tmp := (Nat.le_add_right ..).trans hCur.matchPacket
      refine ⟨by omega, fun j hj => ?_⟩
      rcases hTables.indicesApart j (hj.trans hi) with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    rw [hStable, hTables.indices i hi']
    exact (List.getD_eq_getElem _ _ hi').symm
  have hGraphAt : st.mem (graphs + child) = g := by
    rw [hTablesBelow _ (fun j hj => by have hh := (hTables.beforeGraph j hj).1; omega)]
    exact listAt_tabList hTables.graphsAt hChild
  have hOffAt : st.mem (offsets + child) = D.offset i := by
    rw [hTablesBelow _ (fun j hj => by have hh := (hTables.beforeGraph j hj).2; omega)]
    exact listAt_tabList hTables.offsetsAt hChild
  have hM' := WordRAM.ListAt.congr hM (mem' := st.mem) fun a ha hb =>
    hFrame a ⟨hb.trans_le hCur.matchPacket, fun j hj => Or.inr ((hMcap j (hj.trans hi)).trans ha)⟩
  have hT' := WordRAM.ListAt.congr hT (mem' := st.mem) fun a ha hb =>
    hFrame a ⟨hb.trans_le hCur.walkPacket, fun j hj => Or.inr ((hTcap j (hj.trans hi)).trans ha)⟩
  have hE' := WordRAM.ListAt.congr hE (mem' := st.mem) fun a _ hb => hTablesBelow a (fun j hj => by
    have hLen : (D.host.edges.flatMap fun e => [e.1, e.2]).length = 2 * D.host.m := by
      simp [Graph.m, List.length_flatMap, Nat.mul_comm]
    rw [hLen] at hb
    exact hb.trans_le (hFit.fit j hj).parent)
  have hLocal := WordRAM.ListAt.congr (hRows i hi).1 (mem' := st.mem) fun a ha hb => by
    change a < g + (D.graph i).encode.length at hb
    have hCap : a < D.cap i := by
      rw [graphWords_length] at hb
      unfold ApplyBatchData.cap
      omega
    refine hFrame a ⟨hCap.trans_le ((hMcap i hi).trans (Nat.le_add_right .. |>.trans hCur.matchPacket)),
      fun j hj => ?_⟩
    rcases hFit.disjoint j (hj.trans hi) i hi (ne_of_lt hj) with h | h
    · exact Or.inr (h.trans ha)
    · exact Or.inl (hCap.trans_le h)
  have hFirst : st.mem (mt + i) = 2 * R.first := (matchingRow_view hi hM').1
  have hOffFit := (hRows i hi).2.1
  have hCount := hRows i hi
  have hDirEnd : rowDir + R.count ≤ vs := D.dir_end_le hi |>.trans hDirBound
  have hGraphL : graphs + D.jobs.count ≤ g := (hTables.beforeGraph i hi).1
  have hOffL : offsets + D.jobs.count ≤ g := (hTables.beforeGraph i hi).2
  have hgW : g < 2 ^ w := (hGtmp i hi).trans_lt htmpw
  have hcutW : idx + i < 2 ^ w := by
    have hm := hArgs mt (by simp)
    omega
  have hGraphW : graphs + child < 2 ^ w := by omega
  have hOffW : offsets + child < 2 ^ w := by omega
  have hmtW : mt + i < 2 ^ w := by
    have hs : D.matchings.length + 1 ≤ (csrList D.matchings.length (matchingRowWords D.matchings)).length :=
      by simp [csrList]
    have hm := hCur.matchPacket
    omega
  have hvw := hArgs vs (by simp)
  have hrW : rowDir < 2 ^ w := by omega
  have hFirstW : R.first < 2 ^ w := by
    have he : rowDir = dir + R.first := rfl
    omega
  have hTwo : 2 < 2 ^ w := by
    have h4 := hFit.packet
    omega
  have hoffW := hFit.offsetsWord i hi
  refine runs_start_le ?_
  unfold buildApplyBatchStep
  refine runs_seq_assign_le (v := child) ?_ ?_
  · simp [Expr.eval, h3, h12, hcutW, hCutAt]
  refine runs_seq_assign_le (v := R.first) ?_ ?_
  · simp [Expr.eval, Function.update, h0, h12, hmtW, hFirst, hTwo, hFirstW]
  refine runs_seq_call_le (hProc i hi)
    (vs := [mt, tb, D.matchings.length, i, tmp, g, D.offset i, ends, vs, P, rowDir, top]) ?_ ?_
    ⟨mt,tb,tmp,g,D.offset i,ends,vs,P,rowDir,top,rfl,hCur,hLocal,hG,hM',hT',hE',hOffFit,
      hCount.2.2,hZero,hPos⟩ ?_
  · have hDirW : dir + R.first < 2 ^ w := hrW
    simp [evalArgs, Expr.eval, Function.update, h0,h1,h2,h4,h5,h6,h7,h8,h9,h10,h11,h12,
      hGraphW,hGraphAt,hOffW,hOffAt,hDirW,rowDir,ApplyBatchData.directory,R,top]
  · have ha := hArgs mt (by simp)
    have hb := hArgs tb (by simp)
    have hk := hArgs D.matchings.length (by simp)
    have he := hArgs ends (by simp)
    have hp := hArgs P (by simp)
    wram_words
  intro v mem' pos' hPost
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hEq, hGraph, hV, hZ, hKeep, hP', hDir⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := hEq
  change ∀ a, ApplyRowKept (g + 2 + 2 * (D.graph i).m) (D.cap i) tmp R.count vs P rowDir top g a →
    mem' a = st.mem a at hKeep
  have hCapLo : g + 2 ≤ D.cap i := by
    change D.addr i + 2 ≤ D.cap i
    unfold ApplyBatchData.cap
    omega
  have hCapTmp : D.cap i ≤ tmp :=
    (hMcap i hi).trans (Nat.le_add_right .. |>.trans hCur.matchPacket)
  have hV' : v = D.cursor out (i + 1) := hV
  have htd : tmp ≤ rowDir := (by
    have hb := ApplyBatchData.dir_start_le (D := D) (dir := dir) (i := i)
    change dir ≤ rowDir at hb
    omega)
  refine runs_assign_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨⟨by simpa using h0,by simpa using h1,by simpa using h2,by simpa using h3,
      by simpa using h4,by simpa using h5,by simpa using h6,by simpa using h7,by simpa using h8,
      by simpa using h9,by simpa using h10,by simp [hV'],by simp,hV' ▸ hZ,hP',?_,?_⟩,
      by simpa using h12⟩
    · intro a ha
      exact (hKeep a (ApplyBatchData.keep_below_packet htd ha.1 (ha.2 i (Nat.lt_succ_self i)))).trans
        (hFrame a (ApplyBatchData.kept_next ha))
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hOldG, hOldD⟩ := hPrev j hj
        have hCapJ := hMcap j (hj.trans hi)
        have hTmp := hCur.matchPacket
        refine ⟨WordRAM.ListAt.congr hOldG (fun a ha hb => ?_), ?_⟩
        · rw [cap_eq_appended] at hb
          have hSafe : a < g ∨ D.cap i ≤ a := by
            rcases hFit.disjoint j (hj.trans hi) i hi (ne_of_lt hj) with hl | hr
            · exact Or.inl (hb.trans_le hl)
            · exact Or.inr (hr.trans ha)
          exact hKeep a (ApplyBatchData.keep_below_packet htd (by omega) hSafe)
        · intro t ht
          obtain ⟨hOldPtr, hOldWalk⟩ := hOldD t ht
          let a := D.directory dir j + t
          have hDirBefore : a < rowDir := by
            have he := D.dir_order (dir := dir) (hj.trans hi) hj
            dsimp [a]
            omega
          have hDirAfter : tmp + 4 ≤ a := by
            have he := ApplyBatchData.dir_start_le (D := D) (dir := dir) (i := j)
            dsimp [a]
            omega
          have hDirectory : mem' a = st.mem a :=
            hKeep a ⟨by omega, Or.inr (by omega), Or.inr hDirAfter, Or.inl hDirBefore⟩
          refine ⟨hDirectory.trans hOldPtr, ?_⟩
          let R' := D.row j
          change t < R'.count at ht
          have hStart : out ≤ R'.cursor (D.cursor out j) t :=
            (D.cursor_mono out (Nat.zero_le j)).trans (R'.cursor_mono _ (Nat.zero_le t))
          have hLen : (erase D.host.edges (R'.u t) (R'.raw t)).length ≤ (R'.raw t).length :=
            (erase_spec (R'.raw t).length _ _ _ le_rfl
              ((hRows j (hj.trans hi)).2.2 t ht).2).2.1.length_le
          have hEnd : R'.cursor (D.cursor out j) t + 1 + (R'.raw t).length ≤ top :=
            (R'.cursor_mono _ (show t + 1 ≤ R'.count by omega)).trans
              (D.cursor_mono out (show j + 1 ≤ i by omega))
          exact seqAt_frame hOldWalk (fun a ha hb => hKeep a (by
            change R'.cursor (D.cursor out j) t ≤ a at ha
            change a < R'.cursor (D.cursor out j) t + 1 +
              (erase D.host.edges (R'.u t) (R'.raw t)).length at hb
            refine ⟨by omega,Or.inr (by omega),Or.inr (by omega),Or.inr (Or.inr ⟨by omega,by omega⟩)⟩))
      · exact ⟨hGraph,hDir⟩
  · simp [applyBatchStepCost, buildApplyRowContract, Expr.size, argsSize, ApplyBatchData.row]
    omega

/-- Apply the common router batch to the selected children, preserving their order
and writing each accepted edge's shortcut once. -/
theorem buildApplyBatchProc_meetsContract {w f fRow : ℕ} {D : ApplyBatchData} {p : Program}
    (hf : p.procs[f]? = some (buildApplyBatchProc fRow))
    (hRow : ∀ i < D.matchings.length, MeetsContract w p fRow
      (buildApplyRowContract w i D.host (D.graph i) D.matchings D.emb)) :
    MeetsContract w p f (buildApplyBatchContract w D) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨mt,tb,idx,graphs,offsets,tmp,ends,vs,P,dir,out,rfl,hTables,hIdxRoom,hFit,hG,hM,hT,hE,hRows,
    hZero,hPos⟩ := hPre
  let st0 := startState [mt,tb,D.matchings.length,idx,graphs,offsets,tmp,ends,vs,P,dir,out] mem pos
  have hLoop := Triple.forRange_le (p := p) (r := 12) (lo := .const 0) (hi := .reg 2)
    (body := buildApplyBatchStep fRow) (P := fun st => st = st0)
    (Inv := applyBatchInv D mt tb idx graphs offsets tmp ends vs P dir out mem)
    (applyBatchStepCost D) 0 D.matchings.length (Nat.zero_le _) hFit.one
    (fun _ => hArgs D.matchings.length (by simp))
    (fun st he => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos _),rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
        hZero,hPos,fun _ _ => rfl,fun j hj => False.elim (Nat.not_lt_zero j hj)⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ _ hi => applyBatch_step hRow hArgs hTables hIdxRoom hFit hG hM hT hE hRows hi)
  refine runs_start_le ?_
  unfold buildApplyBatchProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_,_,_,_,_,_,_,_,_,_,_,hTop,_,hZ,hP,hFrame,hOut⟩
  refine runs_ret_le (Expr.eval_reg_of_eq hTop)
    ⟨mt,tb,idx,graphs,offsets,tmp,ends,vs,P,dir,out,rfl,rfl,hZ,hP,hFrame,hOut⟩ ?_
  simp [buildApplyBatchContract, Expr.size]
  omega

end MinCostFlow.HierPaths
