module

public import MinCostFlow.HierPaths.InitProgCSRWrite
public import MinCostFlow.HierPaths.InitProgProjectAt

/-!
# Compressed rows of projected walks

Two address columns identify a connector in constant time. The row
writer reads the selected address, projects the connector, and appends
its vertex or edge column to the compressed table.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The projected row at connector index `i`. -/
def initProjectedRow (S : StaticData) (verts : Bool) (i : ℕ) : List ℕ :=
  initProjectAtWords S verts ((initConnLocs S).getD i default)

/-- The two sections in compressed form. -/
def initProjectedSection (S : StaticData) (verts : Bool) : List ℕ :=
  csrList S.numConn (initProjectedRow S verts)

private theorem initProjected_csr_congr {n : ℕ} {f g : ℕ → List ℕ}
    (h : ∀ i < n, f i = g i) : csrList n f = csrList n g := by
  unfold csrList csrOffsets csrData
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj' : j ≤ n := Nat.le_of_lt_succ (List.mem_range.mp hj)
    congr 1
    exact List.map_congr_left fun i hi => congrArg List.length (h i ((List.mem_range.mp hi).trans_le hj'))
  · exact List.flatMap_congr fun i hi => h i (List.mem_range.mp hi)

theorem initProjectedSection_eq (S : StaticData) (a : ℕ) (s : PathDSAbsState) (verts : Bool) :
    (initConcrete S a s).sections.getD (if verts then 10 else 11) [] =
      initProjectedSection S verts := by
  let C := (connSystem S.H S.x S.b S.owner S.label)
  have he (i : ℕ) (hi : i < S.numConn) :
      (connRecs S.H S.x S.b).getD i default = ((initConnLocs S).getD i default).flat S := by
    have hi' := hi
    rw [← initConnLocs_length S] at hi'
    rw [← initConnLocs_flat S, List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getD_eq_getElem _ _ hi', List.getElem_map]
  cases verts
  · change csrList S.numConn (fun i => (C.walk i).edges) = csrList S.numConn (initProjectedRow S false)
    apply initProjected_csr_congr
    intro i hi
    dsimp [C, connSystem, initProjectedRow, initProjectAtWords, initProjectedColumn]
    rw [he i hi]
  · change csrList S.numConn (fun i => (C.walk i).verts) = csrList S.numConn (initProjectedRow S true)
    apply initProjected_csr_congr
    intro i hi
    dsimp [C, connSystem, initProjectedRow, initProjectAtWords, initProjectedColumn]
    rw [he i hi]

/-- The scratch bound is the sum of the temporary words of the individual rows.
Each row returns those cells to zero before the next row uses them. -/
def initProjectedScratch (S : StaticData) (verts : Bool) : ℕ :=
  ((initConnLocs S).map fun q =>
    initConnProjectRoom S verts q.depth q.group (q.record S).1 (q.record S).2.2).sum

/-- The invariant at the start of the compressed row writer, with a small
header pointing at the address columns and root arrays. -/
def initProjectedContext (w ctx : ℕ) (S : StaticData) (G : Graph) (data : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  ∃ h host L O slots indices,
    ListAt mem ctx
      [h, S.x, S.b, S.numTerm, 2 ^ S.b, leafDepth S.x S.b, numPairsOf S.x S.b,
        host, L, O, slots, indices] ∧
    StaticOut mem h S ∧ h + S.encode.length ≤ data ∧
    InitRootAt w S G mem host L O data ∧
    ListAt mem slots (initEndpointWords S 2) ∧ ListAt mem indices (initEndpointWords S 3) ∧
    ctx + 12 ≤ data ∧ slots + S.numConn ≤ data ∧ indices + S.numConn ≤ data ∧
    0 < S.b ∧ S.H.IsValid S.x S.b ∧
    2 ^ S.b < 2 ^ w ∧ numPairsOf S.x S.b < 2 ^ w ∧ leafDepth S.x S.b + 1 < 2 ^ w

/-- Load the indicated header word. -/
def initProjectedContextLoad (i : ℕ) : Expr := .load (.bin .add (.reg 0) (.const i))

/-- Load one word from the connector address column pointed to by the header. -/
def initProjectedCoordLoad (i : ℕ) : Expr :=
  .load (.bin .add (initProjectedContextLoad i) (.reg 1))

/-- Called with the context pointer, connector number and row destination. -/
def initProjectedRowProc (project : ℕ) : Stmt :=
  .call 3 project [initProjectedContextLoad 0, initProjectedContextLoad 1,
    initProjectedContextLoad 2, initProjectedContextLoad 3, initProjectedContextLoad 4,
    initProjectedContextLoad 5, initProjectedContextLoad 6, initProjectedCoordLoad 10,
    initProjectedCoordLoad 11, initProjectedContextLoad 7, initProjectedContextLoad 8,
    initProjectedContextLoad 9, .reg 2] ;;
  .ret (.reg 3)

theorem initProjectedRowProc_noRand (project : ℕ) :
    (initProjectedRowProc project).NoRand := by simp [initProjectedRowProc, Stmt.NoRand]

theorem initProjectedRowCost_bound (w : ℕ) (S : StaticData) (G : Graph) (verts : Bool)
    (q : InitConnLoc) :
    initProjectAtCost w S G verts q = initProjectAtCost 0 S G verts q := rfl

/-- The cost of one row call, including reading its context and connector coordinates. -/
def initProjectedRowCost (S : StaticData) (G : Graph) (verts : Bool) (i : ℕ) : ℕ :=
  initProjectAtCost 0 S G verts ((initConnLocs S).getD i default) + 100

theorem initProjectedRowProc_meetsContract {w f project ctx i : ℕ} {S : StaticData} {G : Graph}
    {verts : Bool} {p : Program} (hi : i < S.numConn)
    (hp : p.procs[f]? = some (initProjectedRowProc project))
    (hProject : ∀ q, MeetsContract w p project (initProjectAtContract w S G verts q)) :
    MeetsContract w p f (initCSRWriteRowContract ctx i (initProjectedRow S verts i)
      (fun addr mem => ∃ data, initProjectedContext w ctx S G data mem ∧
        data + S.numConn + 1 ≤ addr ∧
        addr + (initProjectedRow S verts i).length + initProjectedScratch S verts < 2 ^ w)
      (initProjectedRowCost S G verts i)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨addr, rfl, ⟨data, hCtx, hdata, hroom⟩, hzero⟩ := hpre
  obtain ⟨h, host, L, O, slots, indices, hh, hS, hsep, hRoot, hslots, hindices,
    hctx, hsl, hin, hb, hH, hB, hk, hD⟩ := hCtx
  let q := (initConnLocs S).getD i default
  have hi' : i < (initConnLocs S).length := by rwa [initConnLocs_length]
  have hq : q ∈ initConnLocs S := by
    dsimp [q]
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have hs : mem (slots + i) = q.slot S := by
    rw [← initConnLocs_slots] at hslots
    have hh' := hslots i (by simpa using hi')
    rw [List.getElem_map] at hh'
    simpa only [q, List.getD_eq_getElem _ _ hi'] using hh'
  have hn : mem (indices + i) = q.index := by
    rw [← initConnLocs_indices] at hindices
    have hh' := hindices i (by simpa using hi')
    rw [List.getElem_map] at hh'
    simpa only [q, List.getD_eq_getElem _ _ hi'] using hh'
  have hAddr : addr < 2 ^ w := by omega
  have hLe : data ≤ addr := by omega
  have hI : i < 2 ^ w := hw _ (by simp)
  have hSlot : q.slot S < 2 ^ w := (initConnLoc_slot_lt hq).trans hk
  have ht : (q.record S).2.2.length < 2 ^ w := by
    have he := (initConnLoc_spec hq).2.2.2.2.2
    have hmem := initConnAddr_record (h := h) hS hq
    have hl : (connWords (q.record S)).length = 2 + (q.record S).2.2.length := by
      simp [connWords]; omega
    omega
  have hP : S.numTerm < 2 ^ w := by
    obtain ⟨_, _, hlen⟩ := staticOut_owner_facts hS
    change 10 + S.numTerm ≤ S.encode.length at hlen
    omega
  have hx : S.x < 2 ^ w := (Nat.lt_two_pow_self).trans hP
  have hbw : S.b < 2 ^ w := Nat.lt_two_pow_self.trans hB
  have hIdx : q.index < 2 ^ w := by
    have hspec := (initConnLoc_spec hq).2.2.2.2.2
    have hlen := initConnLoc_matching_length hq hb hH
    rw [staticConnMatching, initConnLoc_pairOfIdx hq] at hlen
    exact (hspec.trans_le (hlen.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))).trans hP
  have hRoot' : InitRootAt w S G mem host L O addr := by
    obtain ⟨hg, hgB, hL, hO, hLAt, hOAt, hproj, hGm⟩ := hRoot
    exact ⟨hg, hgB.trans hLe, hL.trans hLe, hO.trans hLe, hLAt, hOAt, hproj, hGm⟩
  have hlocal : initConnProjectRoom S verts q.depth q.group (q.record S).1 (q.record S).2.2 ≤
      initProjectedScratch S verts := by
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hlocalRoom : addr + initConnProjectRoom S verts q.depth q.group (q.record S).1 (q.record S).2.2 <
      2 ^ w := by omega
  let st := startState [ctx, i, addr] mem pos
  have load (j : ℕ) (hj : j < 12) (v : ℕ) (hv : mem (ctx + j) = v) :
      (initProjectedContextLoad j).eval w st = some v := by
    unfold initProjectedContextLoad
    exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := ctx) rfl)
      (Expr.eval_const (by omega)) (by omega)) hv
  have coord (j val x : ℕ) (hj : j < 12) (hv : mem (ctx + j) = val)
      (hm : mem (val + i) = x) (hb : val + i < 2 ^ w) :
      (initProjectedCoordLoad j).eval w st = some x := by
    exact Expr.eval_load_of_eq (Expr.eval_add (load j hj val hv) (Expr.eval_reg_of_eq rfl) hb) hm
  have e0 := load 0 (by decide) h (hh 0 (by simp))
  have e1 := load 1 (by decide) S.x (hh 1 (by simp))
  have e2 := load 2 (by decide) S.b (hh 2 (by simp))
  have e3 := load 3 (by decide) S.numTerm (hh 3 (by simp))
  have e4 := load 4 (by decide) (2 ^ S.b) (hh 4 (by simp))
  have e5 := load 5 (by decide) (leafDepth S.x S.b) (hh 5 (by simp))
  have e6 := load 6 (by decide) (numPairsOf S.x S.b) (hh 6 (by simp))
  have e7 := load 7 (by decide) host (hh 7 (by simp))
  have e8 := load 8 (by decide) L (hh 8 (by simp))
  have e9 := load 9 (by decide) O (hh 9 (by simp))
  have e10 := coord 10 slots (q.slot S) (by decide) (hh 10 (by simp)) hs (by omega)
  have e11 := coord 11 indices q.index (by decide) (hh 11 (by simp)) hn (by omega)
  refine runs_start_le ?_
  unfold initProjectedRowProc
  refine runs_seq_call_le (hProject q)
    (vs := [h, S.x, S.b, S.numTerm, 2 ^ S.b, leafDepth S.x S.b, numPairsOf S.x S.b,
      q.slot S, q.index, host, L, O, addr]) ?_ ?_
    ⟨h, host, L, O, addr, rfl, hq, hS, hsep.trans hLe, hRoot', hzero, hb, hH, hD, hlocalRoom⟩ ?_
  · change evalArgs w st _ = _
    simp only [evalArgs, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
    rfl
  · obtain ⟨_, hhst, hL, hO, _, _, _, _⟩ := hRoot
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | omega
  intro r mem' pos' hp'
  obtain ⟨_, _, _, _, addr', ha, hr, hwords, hz, hf⟩ := hp'
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hd⟩ := ha
  subst addr'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ⟨addr, rfl, hr, hwords, hz, hf⟩ ?_
  simp [initCSRWriteRowContract, initProjectAtContract, initProjectedRowCost,
    initProjectedContextLoad, initProjectedCoordLoad, Expr.size, argsSize, q, initProjectedRowCost_bound]
  omega

end MinCostFlow.HierPaths

end
