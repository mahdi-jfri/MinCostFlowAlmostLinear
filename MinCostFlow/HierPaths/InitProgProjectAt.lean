module

public import MinCostFlow.HierPaths.InitProgConnSeek
public import MinCostFlow.HierPaths.InitProgConnRoot

/-!
# Projecting a connector addressed by pair and position

Read the two boundaries of the connector record. Its first two words
give the endpoints and the remaining words are the local walk. The
first endpoint determines the group of the walk at its starting depth.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are the static address, hierarchy dimensions, record coordinates,
root arrays, and destination. -/
def initProjectAt (seek project : ℕ) : Stmt :=
  .call 13 seek [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7, .reg 8] ;;
  .call 14 seek [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7,
    .bin .add (.reg 8) (.const 1)] ;;
  .assign 15 (.bin .div (.bin .div (.reg 7) (.reg 4)) (.reg 3)) ;;
  .assign 16 (.load (.reg 13)) ;;
  .assign 17 (.bin .div (.reg 16) (queryGroupSizeExpr (.reg 1) (.reg 2) (.reg 15))) ;;
  .call 18 project [.reg 0, .reg 3, .reg 5, .reg 1, .reg 2, .reg 15, .reg 17, .reg 16,
    .load (.bin .add (.reg 13) (.const 1)), .bin .add (.reg 13) (.const 2),
    .bin .sub (.reg 14) (.bin .add (.reg 13) (.const 2)), .reg 9, .reg 10, .reg 11, .reg 12] ;;
  .ret (.reg 18)

theorem initProjectAt_noRand (seek project : ℕ) : (initProjectAt seek project).NoRand := by
  simp [initProjectAt, Stmt.NoRand]

/-- At the record's connector number the projected column comes from the flat walk. -/
def initProjectAtWords (S : StaticData) (verts : Bool) (q : InitConnLoc) : List ℕ :=
  initProjectedColumn S verts (q.flat S).endA (q.flat S).hwalk

def initProjectAtCost (w : ℕ) (S : StaticData) (G : Graph) (verts : Bool) (q : InitConnLoc) : ℕ :=
  let r := q.record S
  (initConnProjectContract w S G verts q.depth q.group r.1 r.2.1 r.2.2).cost [] (fun _ => 0) + 260

def initProjectAtContract (w : ℕ) (S : StaticData) (G : Graph) (verts : Bool) (q : InitConnLoc) :
    Contract where
  pre args mem := ∃ h host L O dst, args =
    [h, S.x, S.b, S.numTerm, 2 ^ S.b, leafDepth S.x S.b, numPairsOf S.x S.b, q.slot S, q.index,
      host, L, O, dst] ∧
    q ∈ initConnLocs S ∧ StaticOut mem h S ∧ h + S.encode.length ≤ dst ∧
    InitRootAt w S G mem host L O dst ∧
    ZeroFrom mem dst ∧ 0 < S.b ∧ S.H.IsValid S.x S.b ∧ leafDepth S.x S.b + 1 < 2 ^ w ∧
    dst + initConnProjectRoom S verts q.depth q.group (q.record S).1 (q.record S).2.2 < 2 ^ w
  post args mem v mem' := ∃ h host L O dst, args =
    [h, S.x, S.b, S.numTerm, 2 ^ S.b, leafDepth S.x S.b, numPairsOf S.x S.b, q.slot S, q.index,
      host, L, O, dst] ∧
    v = dst + (initProjectAtWords S verts q).length ∧ ListAt mem' dst (initProjectAtWords S verts q) ∧
    ZeroFrom mem' v ∧ ∀ y < dst, mem' y = mem y
  cost _ _ := initProjectAtCost w S G verts q

theorem initProjectAt_meetsContract {w f seek project : ℕ} {S : StaticData} {G : Graph}
    {verts : Bool} {q : InitConnLoc} {p : Program}
    (hp : p.procs[f]? = some (initProjectAt seek project))
    (hSeek : ∀ i, MeetsContract w p seek (initConnSeekContract w S q i))
    (hProj : ∀ t g u v es, MeetsContract w p project (initConnProjectContract w S G verts t g u v es)) :
    MeetsContract w p f (initProjectAtContract w S G verts q) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h, host, L, O, dst, rfl, hq, hS, hsep, hroot, hzero, hb, hH, hD, hroom⟩ := hpre
  let P := S.numTerm
  let B := 2 ^ S.b
  let D := leafDepth S.x S.b
  let k := numPairsOf S.x S.b
  let s := q.slot S
  let r := q.record S
  let first := initConnAddr S mem h s q.index
  let last := initConnAddr S mem h s (q.index + 1)
  have hfirst : ListAt mem first (connWords r) := (initConnAddr_record hS hq).1
  have hsum : last = first + (connWords r).length := (initConnAddr_record hS hq).2.1
  have hlast : last ≤ dst := (initConnAddr_record hS hq).2.2.trans hsep
  have hlen : (connWords r).length = 2 + r.2.2.length := by simp [connWords]; omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h1w : first + 1 < 2 ^ w := by omega
  have h2w : first + 2 < 2 ^ w := by omega
  have hlw : r.2.2.length < 2 ^ w := by omega
  have hsub : last - (first + 2) = r.2.2.length := by omega
  have hSw : h + S.encode.length < 2 ^ w := by omega
  have hs : s < 2 ^ w := hw _ (by simp [s])
  have hP : P < 2 ^ w := hw _ (by simp [P])
  have hbw : S.b < 2 ^ w := hw _ (by simp)
  have hi : q.index < (staticConnMatching S s).length := by
    dsimp [staticConnMatching, s]
    rw [initConnLoc_pairOfIdx hq]
    exact (initConnLoc_spec hq).2.2.2.2.2
  have hiw : q.index + 1 < 2 ^ w := by
    have hlen := initConnLoc_matching_length hq hb hH
    apply lt_of_le_of_lt (Nat.succ_le_of_lt hi)
    rw [show s = q.slot S from rfl, hlen]
    exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans_lt hP
  obtain ⟨hu, hv, _, hgroup, hW⟩ := initConnLoc_record_data hq hb hH
  obtain ⟨hj, hg, _, _, _, _⟩ := initConnLoc_spec hq
  have hd : s / B / P = q.depth := congrArg Prod.fst (initConnLoc_pairOfIdx hq)
  have hdw : q.depth < 2 ^ w := hj.trans (by omega)
  have hgw : q.group < 2 ^ w := (hg.trans_le (numGroups_le_pow _)).trans hP
  have hread : mem first = r.1 ∧ mem (first + 1) = r.2.1 ∧ ListAt mem (first + 2) r.2.2 := by
    obtain ⟨h₁, htail⟩ := listAt_cons.mp hfirst
    obtain ⟨h₂, hrest⟩ := listAt_cons.mp htail
    exact ⟨h₁, h₂, hrest⟩
  refine runs_start_le ?_
  unfold initProjectAt
  refine runs_seq_call_le (hSeek q.index) (vs := [h, S.x, S.b, P, B, k, s, q.index]) rfl ?_
    ⟨h, rfl, hS, hSw, hD, hq, hb, hH, hi.le⟩ ?_
  · intro a ha
    exact hw a (by simp [P, B, k, s] at ha ⊢; tauto)
  intro a mem₁ pos₁ hp₁
  change a = first ∧ mem₁ = mem at hp₁
  obtain ⟨ha, hm₁⟩ := hp₁
  subst a mem₁
  refine runs_seq_call_le (hSeek (q.index + 1))
    (vs := [h, S.x, S.b, P, B, k, s, q.index + 1]) ?_ ?_
    ⟨h, rfl, hS, hSw, hD, hq, hb, hH, hi⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, hiw, P, B, k, s]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hiw | exact hw _ (by simp [P, B, k, s])
  intro b mem₂ pos₂ hp₂
  change b = last ∧ mem₂ = mem at hp₂
  obtain ⟨ha, hm₂⟩ := hp₂
  subst b mem₂
  refine runs_seq_assign_le (v := q.depth) (Expr.eval_eq_of_eq (Expr.eval_div
    (Expr.eval_div (Expr.eval_reg_of_eq (v := s) rfl) (Expr.eval_reg_of_eq (v := B) rfl) hs)
    (Expr.eval_reg_of_eq (v := P) rfl) ((Nat.div_le_self _ _).trans_lt hs)) hd) ?_
  refine runs_seq_assign_le (v := r.1) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) hread.1) ?_
  refine runs_seq_assign_le (v := q.group) (Expr.eval_eq_of_eq
    (Expr.eval_div (Expr.eval_reg_of_eq (v := r.1) rfl)
      (eval_queryGroupSizeExpr (Expr.eval_reg_of_eq (v := S.x) rfl)
        (Expr.eval_reg_of_eq (v := S.b) rfl) (Expr.eval_reg_of_eq (v := q.depth) rfl)
        hP (queryDepth_mul_lt hb hj.le hP hbw)) (hu.trans hP)) hgroup) ?_
  refine runs_seq_call_le (hProj q.depth q.group r.1 r.2.1 r.2.2)
    (vs := [h, P, D, S.x, S.b, q.depth, q.group, r.1, r.2.1, first + 2, r.2.2.length, host, L, O, dst])
    ?_ ?_ ⟨h, first + 2, host, L, O, dst, rfl, hS, hread.2.2, by omega, hsep, hroot, hzero, hroom,
      hD, hb, hH, hj.le, initGroupSize_gt_one hb hj, hg, hu, hv, hW⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, h2, h1w, h2w,
      hread.2.1, hsub, hlw, P, D]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hdw | exact hgw | exact hu.trans hP | exact hv.trans hP | exact h2w | exact hlw | exact hw _ (by simp [P, D])
  intro z mem' pos' hp'
  obtain ⟨h', src', host', L', O', dst', ha, hv, hwords, hz, hf⟩ := hp'
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hdst⟩ := ha
  subst dst'
  refine runs_ret_le (v := z) (Expr.eval_reg_of_eq rfl)
    ⟨h, host, L, O, dst, rfl, hv, hwords, hz, hf⟩ ?_
  simp [initProjectAtContract, initProjectAtCost, initConnSeekContract, initConnProjectContract,
    queryGroupSizeExpr, Expr.size, argsSize, r]
  omega

end MinCostFlow.HierPaths

end
