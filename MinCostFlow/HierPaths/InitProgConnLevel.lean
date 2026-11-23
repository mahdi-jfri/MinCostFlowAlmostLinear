module

public import MinCostFlow.HierPaths.InitProgAppend

/-!
# Writing all endpoint columns at one depth

Children at a fixed depth have consecutive numbers. Each child contributes the interval
of rows for its later siblings. The output cursor passes from one child to the next.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The column written by one depth. -/
def initLevelEndpoints (S : StaticData) (field j : ℕ) : List ℕ :=
  initAppendPrefix (fun c => initChildEndpoints S field j (parentGroup S.x S.b j c) c)
    (numGroups S.x S.b (j + 1))

theorem initNumGroups_succ (x b j : ℕ) :
    numGroups x b (j + 1) = numGroups x b j * branching x b j := by
  apply Nat.eq_of_mul_eq_mul_right (groupSize_pos (x := x) (b := b) (j := j + 1))
  rw [Nat.mul_assoc, ← groupSize_eq_mul_branching, numGroups_mul_groupSize, numGroups_mul_groupSize]

private theorem initEndpointChild_bounds {x b j c : ℕ} (hc : c < numGroups x b (j + 1)) :
    parentGroup x b j c < numGroups x b j ∧ c ∈ childGroups x b j (parentGroup x b j c) := by
  refine ⟨?_, mem_childGroups_iff.mpr rfl⟩
  unfold parentGroup
  rwa [Nat.div_lt_iff_lt_mul branching_pos, ← initNumGroups_succ]

/-- Local cost of the call for child `c`, including its arguments. -/
def initLevelChildCost (S : StaticData) (j c : ℕ) : ℕ :=
  (initEndpointChildContract 0 S j (parentGroup S.x S.b j c) c).cost [] (fun _ => 0) + 10

/-- Arguments are the exponents, depth, branching, source table address, table row count,
destination, field, and number of children at the next depth. -/
def initEndpointLevel (child : ℕ) : Stmt :=
  forRange 9 (.const 0) (.reg 8) (.call 6 child
    [.reg 0, .reg 1, .reg 2, .reg 9, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7]) ;;
  .ret (.reg 6)

theorem initEndpointLevel_noRand (child : ℕ) : (initEndpointLevel child).NoRand := by
  simp [initEndpointLevel, forRange, forUp, Stmt.NoRand]

/-- One depth's endpoint loop preserves the static table and writes its column in child order. -/
def initEndpointLevelContract (w : ℕ) (S : StaticData) (j : ℕ) : Contract where
  pre args mem := ∃ h dst field,
    args = [S.x, S.b, j, branching S.x S.b j, h + 7 + mem (h + 5),
      numPairsOf S.x S.b, dst, field, numGroups S.x S.b (j + 1)] ∧ StaticOut mem h S ∧
    j < leafDepth S.x S.b ∧ 1 < groupSize S.x S.b j ∧ field < 4 ∧
    h + S.encode.length ≤ dst ∧ dst + (initLevelEndpoints S field j).length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ h dst field,
    args = [S.x, S.b, j, branching S.x S.b j, h + 7 + mem (h + 5),
      numPairsOf S.x S.b, dst, field, numGroups S.x S.b (j + 1)] ∧
    v = dst + (initLevelEndpoints S field j).length ∧
    ListAt mem' dst (initLevelEndpoints S field j) ∧ ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := rangeCost (initLevelChildCost S j) 0 (numGroups S.x S.b (j + 1)) +
    9 * numGroups S.x S.b (j + 1) + 12

theorem initEndpointLevel_meetsContract {w f child range row seek count copy fill j : ℕ}
    {S : StaticData} {p : Program}
    (hp : p.procs[f]? = some (initEndpointLevel child))
    (hChild : p.procs[child]? = some (initEndpointChild range))
    (hR : p.procs[range]? = some (initEndpointRange row))
    (hrow : p.procs[row]? = some (initEndpointRow seek count copy fill))
    (hs : p.procs[seek]? = some initCSRSeek) (hc : p.procs[count]? = some initCSRCount)
    (hcopy : p.procs[copy]? = some initEndpointCopy)
    (hfill : p.procs[fill]? = some initFillWord) :
    MeetsContract w p f (initEndpointLevelContract w S j) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h, dst, field, rfl, hS, hj, hsize, hf, hsep, hroom, h1w⟩ := hpre
  let src := h + 7 + mem (h + 5)
  let br := branching S.x S.b j
  let k := numPairsOf S.x S.b
  let len := numGroups S.x S.b (j + 1)
  let chunks := fun c => initChildEndpoints S field j (parentGroup S.x S.b j c) c
  let R := fun (st : State) => st.regs 0 = S.x ∧ st.regs 1 = S.b ∧ st.regs 2 = j ∧
    st.regs 3 = br ∧ st.regs 4 = src ∧ st.regs 5 = k ∧ st.regs 7 = field ∧ st.regs 8 = len
  have hlen : len < 2 ^ w := hw _ (by simp [len])
  have hslot : h + 5 < dst := by
    have hh := (hS.section_end_le (i := 5) (by decide)).trans hsep
    omega
  have hloop := initAppendLoop_triple (w := w) (p := p) (dstReg := 6) (idxReg := 9)
    (hi := .reg 8) (body := .call 6 child [.reg 0, .reg 1, .reg 2, .reg 9, .reg 3, .reg 4,
      .reg 5, .reg 6, .reg 7]) R chunks (initLevelChildCost S j) len dst mem
    (by decide) h1w hlen
    (fun s q hs => by simpa [R] using hs)
    (fun s hs => Expr.eval_reg_of_eq hs.2.2.2.2.2.2.2)
    (fun c hc' st hR' hidx hdst hframe => by
      obtain ⟨hg, hcg⟩ := initEndpointChild_bounds hc'
      let g := parentGroup S.x S.b j c
      let out := dst + (initAppendPrefix chunks c).length
      have hout : out + (chunks c).length = dst + (initAppendPrefix chunks (c + 1)).length := by
        rw [initAppendPrefix_succ, List.length_append, Nat.add_assoc]
      have hrw : out + (chunks c).length < 2 ^ w := by
        rw [hout]
        exact (Nat.add_le_add_left (initAppendPrefix_length_mono chunks hc') dst).trans_lt hroom
      have hst : StaticOut st.mem h S :=
        listAt_congr (fun i hi => (hframe _ (by omega)).symm) hS
      have hsrc : h + 7 + st.mem (h + 5) = src := by rw [hframe _ hslot]
      obtain ⟨r0, r1, r2, r3, r4, r5, r7, r8⟩ := hR'
      intro st' ω he
      subst st'
      refine runs_start_le ?_
      refine runs_call_le (initEndpointChild_meetsContract (w := w) (S := S)
        (j := j) (g := g) (c := c) hChild hR hrow hs hc hcopy hfill)
        (vs := [S.x, S.b, j, c, br, src, k, out, field]) ?_ ?_ ?_ ?_
      · simp [evalArgs, Expr.eval, r0, r1, r2, r3, r4, r5, r7, hidx, hdst, out]
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact hc'.trans hlen | exact (Nat.le_add_right out (chunks c).length).trans_lt hrw | (apply hw; simp [br, src, k]; done)
      · refine ⟨h, out, field, ?_, hst, hj, hg, hcg, hsize, hf, ?_, hrw, h1w⟩
        · rw [hsrc]
        · exact hsep.trans (Nat.le_add_right _ _)
      · intro v mem' pos' hp'
        obtain ⟨hh, out', field', ha, hv, hwords, hfr⟩ := hp'
        simp only [List.cons.injEq, and_true] at ha
        obtain ⟨_, _, _, _, _, _, _, hout', hf'⟩ := ha
        subst out' field'
        refine ⟨⟨?_, by simpa using hidx, ?_, hwords, ?_⟩, ?_⟩
        · exact ⟨by simpa using r0, by simpa using r1, by simpa using r2, by simpa using r3,
            by simpa using r4, by simpa using r5, by simpa using r7, by simpa using r8⟩
        · change Function.update st.regs 6 v 6 = _
          rw [Function.update_self, ← hout]
          exact hv
        · intro y hy
          rw [← hout] at hy
          exact hfr y (by rw [hv]; exact hy)
        · change 0 + argsSize _ + _ + 1 ≤ initLevelChildCost S j c
          simp [argsSize, Expr.size, initLevelChildCost, initEndpointChildContract, g]
          omega)
  refine runs_start_le ?_
  unfold initEndpointLevel
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
  intro st ⟨_, hd, hwords, hframe⟩
  refine runs_ret_le (Expr.eval_reg_of_eq hd) ⟨h, dst, field, rfl, rfl, hwords, hframe⟩ ?_
  simp [Expr.size, initEndpointLevelContract, len, Nat.mul_comm 9]

private theorem range_flatMap_childList (x b j G : ℕ) :
    (List.range G).flatMap (childList x b j) = List.range (G * branching x b j) := by
  induction G with
  | zero => simp
  | succ G ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih, childList,
      List.range_eq_range', Nat.succ_mul]
    rw [← List.range_eq_range']
    simpa only [Nat.zero_add, List.range_eq_range'] using
      (List.range'_append_1 (s := 0) (m := G * branching x b j) (n := branching x b j))

/-- The parent-ordered and child-ordered loops produce the same level column. -/
theorem initLevelEndpoints_eq (S : StaticData) (field j : ℕ) :
    initLevelEndpoints S field j =
      (List.range (numGroups S.x S.b j)).flatMap fun g =>
        (childList S.x S.b j g).flatMap (initChildEndpoints S field j g) := by
  unfold initLevelEndpoints initAppendPrefix
  rw [initNumGroups_succ, ← range_flatMap_childList, List.flatMap_assoc]
  apply List.flatMap_congr
  intro g _
  apply List.flatMap_congr
  intro c hc
  have hp := mem_childGroups_iff.mp (mem_childList.mp hc)
  change parentGroup S.x S.b j c = g at hp
  rw [hp]

/-- Visiting the hierarchy by depths and then by child number gives the model's column. -/
theorem initAppendPrefix_levels (S : StaticData) (field : ℕ) :
    initAppendPrefix (initLevelEndpoints S field) (leafDepth S.x S.b) =
      initEndpointWords S field := by
  unfold initAppendPrefix initEndpointWords
  apply List.flatMap_congr
  intro j _
  rw [initLevelEndpoints_eq]
  rfl

end MinCostFlow.HierPaths

end
