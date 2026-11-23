module

public import MinCostFlow.HierPaths.InitProgConnLevel
public import MinCostFlow.HierPaths.QueryProgGroupSize

/-!
# Writing an endpoint column of the hierarchy

For each depth, the two successive group sizes give the branching and next child count.
The program calls the level loop with these numbers and keeps the end of the column.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- At depths before the leaves, groups have more than one member. -/
theorem initGroupSize_gt_one {x b j : ℕ} (hb : 0 < b) (hj : j < leafDepth x b) :
    1 < groupSize x b j := by
  have hmul : (j + 1) * b ≤ x + b - 1 := (Nat.le_div_iff_mul_le hb).mp hj
  rw [Nat.succ_mul] at hmul
  unfold groupSize
  apply Nat.one_lt_two_pow_iff.mpr
  omega

/-- The next child count is the number of terminals divided by the next group size. -/
theorem initNumGroups_div_groupSize (x b j : ℕ) :
    2 ^ x / groupSize x b j = numGroups x b j := by
  rw [← numGroups_mul_groupSize (j := j) (b := b), Nat.mul_div_cancel _ groupSize_pos]

/-- Compute the two group sizes and call the level loop. -/
def initEndpointDepthBody (level : ℕ) : Stmt :=
  .assign 9 (queryGroupSizeExpr (.reg 0) (.reg 1) (.reg 8)) ;;
  .assign 10 (queryGroupSizeExpr (.reg 0) (.reg 1) (.bin .add (.reg 8) (.const 1))) ;;
  .call 5 level [.reg 0, .reg 1, .reg 8, .bin .div (.reg 9) (.reg 10), .reg 3, .reg 4,
    .reg 5, .reg 6, .bin .div (.reg 7) (.reg 10)]

/-- Arguments are the two exponents, depth count, connector table address and row count,
output address, endpoint field, and terminal count. -/
def initEndpointDepth (level : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 2) (initEndpointDepthBody level) ;; .ret (.reg 5)

theorem initEndpointDepth_noRand (level : ℕ) : (initEndpointDepth level).NoRand := by
  simp [initEndpointDepth, initEndpointDepthBody, forRange, forUp, Stmt.NoRand]

def initDepthLevelCost (S : StaticData) (j : ℕ) : ℕ :=
  (initEndpointLevelContract 0 S j).cost [] (fun _ => 0) + 70

/-- The ordered column of all endpoints, with its frame and summed running time. -/
def initEndpointDepthContract (w : ℕ) (S : StaticData) : Contract where
  pre args mem := ∃ h dst field,
    args = [S.x, S.b, leafDepth S.x S.b, h + 7 + mem (h + 5), numPairsOf S.x S.b,
      dst, field, 2 ^ S.x] ∧ StaticOut mem h S ∧ 0 < S.b ∧ field < 4 ∧
    h + S.encode.length ≤ dst ∧ dst + (initEndpointWords S field).length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ h dst field,
    args = [S.x, S.b, leafDepth S.x S.b, h + 7 + mem (h + 5), numPairsOf S.x S.b,
      dst, field, 2 ^ S.x] ∧
    v = dst + (initEndpointWords S field).length ∧
    ListAt mem' dst (initEndpointWords S field) ∧ ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := rangeCost (initDepthLevelCost S) 0 (leafDepth S.x S.b) +
    9 * leafDepth S.x S.b + 12

private theorem initEndpointDepthBody_triple {w level j h dst field : ℕ}
    {S : StaticData} {p : Program} (st : State)
    (hL : MeetsContract w p level (initEndpointLevelContract w S j))
    (hout : StaticOut st.mem h S) (hj : j < leafDepth S.x S.b) (hb : 0 < S.b) (hf : field < 4)
    (hsep : h + S.encode.length ≤ dst) (hroom : dst + (initLevelEndpoints S field j).length < 2 ^ w)
    (h1w : 1 < 2 ^ w) (hD : leafDepth S.x S.b < 2 ^ w) (hB : S.b < 2 ^ w)
    (hP : 2 ^ S.x < 2 ^ w) (hsrc : h + 7 + st.mem (h + 5) < 2 ^ w)
    (hk : numPairsOf S.x S.b < 2 ^ w) (hfield : field < 2 ^ w)
    (r0 : st.regs 0 = S.x) (r1 : st.regs 1 = S.b) (r3 : st.regs 3 = h + 7 + st.mem (h + 5))
    (r4 : st.regs 4 = numPairsOf S.x S.b) (r5 : st.regs 5 = dst) (r6 : st.regs 6 = field)
    (r7 : st.regs 7 = 2 ^ S.x) (r8 : st.regs 8 = j) :
    Triple w p (fun s => s = st) (initEndpointDepthBody level)
      (normalPost fun t => t.regs 5 = dst + (initLevelEndpoints S field j).length ∧
        (∀ r, r ≠ 5 → r ≠ 9 → r ≠ 10 → t.regs r = st.regs r) ∧
        ListAt t.mem dst (initLevelEndpoints S field j) ∧
        ∀ y, y < dst ∨ dst + (initLevelEndpoints S field j).length ≤ y → t.mem y = st.mem y)
      (fun _ => initDepthLevelCost S j) := by
  let sz := groupSize S.x S.b j
  let next := groupSize S.x S.b (j + 1)
  let br := branching S.x S.b j
  let kids := numGroups S.x S.b (j + 1)
  have hjw : j + 1 < 2 ^ w := lt_of_le_of_lt (show j + 1 ≤ leafDepth S.x S.b from hj) hD
  have hm := queryDepth_mul_lt hb hj.le hP hB
  have hm' := queryDepth_mul_lt hb hj hP hB
  have hsize := initGroupSize_gt_one hb hj
  have hsz : sz < 2 ^ w :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le ..)).trans_lt hP
  have hbr : br < 2 ^ w := (Nat.div_le_self sz next).trans_lt hsz
  have hkids : kids < 2 ^ w := (numGroups_le_pow _).trans_lt hP
  intro s ω he
  subst s
  refine runs_start_le ?_
  unfold initEndpointDepthBody
  refine runs_seq_assign_le (v := sz) (eval_queryGroupSizeExpr
    (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r8) hP hm) ?_
  refine runs_seq_assign_le (v := next) (eval_queryGroupSizeExpr
    (Expr.eval_reg_of_eq (by simpa using r0)) (Expr.eval_reg_of_eq (by simpa using r1))
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r8)) (Expr.eval_const h1w) hjw) hP hm') ?_
  refine runs_call_le hL
    (vs := [S.x, S.b, j, br, h + 7 + st.mem (h + 5), numPairsOf S.x S.b, dst, field, kids])
    ?_ ?_ ⟨h, dst, field, rfl, hout, hj, hsize, hf, hsep, hroom, h1w⟩ ?_
  · have hdiv : 2 ^ S.x / next = kids := initNumGroups_div_groupSize S.x S.b (j + 1)
    have hbrEq : sz / next = br := rfl
    simp [evalArgs, Expr.eval, BinOp.eval, r0, r1, r3, r4, r5, r6, r7, r8, hdiv, hbrEq,
      hkids, hbr]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.lt_two_pow_self.trans hP
    · exact hB
    · omega
    · exact hbr
    · exact hsrc
    · exact hk
    · omega
    · exact hfield
    · exact hkids
  · intro v mem' pos' hp
    obtain ⟨h', dst', field', ha, hv, hwds, hfr⟩ := hp
    simp only [List.cons.injEq, and_true] at ha
    obtain ⟨_, _, _, _, _, _, hd, hf' , _⟩ := ha
    subst dst' field'
    refine ⟨⟨by simpa using hv, ?_, hwds, ?_⟩, ?_⟩
    · intro r h5 h9 h10
      simp [Function.update_of_ne h5, Function.update_of_ne h9, Function.update_of_ne h10]
    · intro y hy
      apply hfr
      rw [hv]
      exact hy
    · simp [initDepthLevelCost, initEndpointLevelContract, queryGroupSizeExpr, argsSize, Expr.size]
      omega

theorem initEndpointDepth_meetsContract {w f level child range row seek count copy fill : ℕ}
    {S : StaticData} {p : Program}
    (hp : p.procs[f]? = some (initEndpointDepth level))
    (hLevel : p.procs[level]? = some (initEndpointLevel child))
    (hChild : p.procs[child]? = some (initEndpointChild range))
    (hR : p.procs[range]? = some (initEndpointRange row))
    (hrow : p.procs[row]? = some (initEndpointRow seek count copy fill))
    (hs : p.procs[seek]? = some initCSRSeek) (hc : p.procs[count]? = some initCSRCount)
    (hcopy : p.procs[copy]? = some initEndpointCopy)
    (hfill : p.procs[fill]? = some initFillWord) :
    MeetsContract w p f (initEndpointDepthContract w S) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h, dst, field, rfl, hS, hb, hf, hsep, hroom, h1⟩ := hpre
  let D := leafDepth S.x S.b
  let src := h + 7 + mem (h + 5)
  let chunks := initLevelEndpoints S field
  let R := fun (s : State) => s.regs 0 = S.x ∧ s.regs 1 = S.b ∧ s.regs 2 = D ∧
    s.regs 3 = src ∧ s.regs 4 = numPairsOf S.x S.b ∧ s.regs 6 = field ∧ s.regs 7 = 2 ^ S.x
  have hpref : initAppendPrefix chunks D = initEndpointWords S field :=
    initAppendPrefix_levels S field
  have hslot : h + 5 < dst := by
    have hh := (hS.section_end_le (i := 5) (by decide)).trans hsep
    omega
  have hD : D < 2 ^ w := hw _ (by simp [D])
  have hloop := initAppendLoop_triple (w := w) (p := p) (dstReg := 5) (idxReg := 8)
    (hi := .reg 2) (body := initEndpointDepthBody level) R chunks (initDepthLevelCost S) D dst mem
    (by decide) h1 hD (fun s q hr => by simpa [R] using hr)
    (fun s hr => Expr.eval_reg_of_eq hr.2.2.1)
    (fun j hj st hreg hidx hdst hframe => by
      let out := dst + (initAppendPrefix chunks j).length
      have hlen : out + (chunks j).length = dst + (initAppendPrefix chunks (j + 1)).length := by
        rw [initAppendPrefix_succ, List.length_append, Nat.add_assoc]
      have hfit : out + (chunks j).length < 2 ^ w := by
        rw [hlen]
        exact (Nat.add_le_add_left (initAppendPrefix_length_mono chunks hj) dst).trans_lt
          (by rwa [hpref])
      have hst : StaticOut st.mem h S :=
        listAt_congr (fun i hi => (hframe _ (by omega)).symm) hS
      have he : h + 7 + st.mem (h + 5) = src := by rw [hframe _ hslot]
      obtain ⟨r0, r1, r2, r3, r4, r6, r7⟩ := hreg
      have ht := initEndpointDepthBody_triple (S := S) (h := h) (dst := out) (field := field)
        st (initEndpointLevel_meetsContract hLevel hChild hR hrow hs hc hcopy hfill)
        hst hj hb hf (hsep.trans (Nat.le_add_right _ _)) hfit h1 hD (hw _ (by simp))
        (hw _ (by simp)) (by rw [he]; exact hw _ (by simp [src]))
        (hw _ (by simp)) (hw _ (by simp)) r0 r1 (r3.trans he.symm) r4 hdst r6 r7 hidx
      refine ht.conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
      intro o t hp
      cases o with
      | returned => exact False.elim hp
      | normal =>
        obtain ⟨hp, hr, hwds, hf⟩ := hp
        refine ⟨?_, (hr 8 (by decide) (by decide) (by decide)).trans hidx,
          hp.trans hlen, hwds, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first
            | exact (hr _ (by decide) (by decide) (by decide)).trans r0
            | exact (hr _ (by decide) (by decide) (by decide)).trans r1
            | exact (hr _ (by decide) (by decide) (by decide)).trans r2
            | exact (hr _ (by decide) (by decide) (by decide)).trans r3
            | exact (hr _ (by decide) (by decide) (by decide)).trans r4
            | exact (hr _ (by decide) (by decide) (by decide)).trans r6
            | exact (hr _ (by decide) (by decide) (by decide)).trans r7
        · intro y hy
          apply hf
          rw [hlen]
          exact hy)
  refine runs_start_le ?_
  unfold initEndpointDepth
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
  intro st ⟨_, hd, hwds, hframe⟩
  rw [hpref] at hd hwds hframe
  refine runs_ret_le (Expr.eval_reg_of_eq hd) ⟨h, dst, field, rfl, rfl, hwds, hframe⟩ ?_
  simp [Expr.size, initEndpointDepthContract, D, Nat.mul_comm 9]

end MinCostFlow.HierPaths

end
