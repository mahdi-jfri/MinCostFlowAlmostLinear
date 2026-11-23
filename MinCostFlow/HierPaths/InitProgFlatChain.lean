module

public import MinCostFlow.HierPaths.InitProgFlatChainModel
public import MinCostFlow.HierPaths.QueryProgGroupSize

/-!
# Flattening a walk to the root

At each depth the program appends a length-prefixed list to scratch and
continues with the parent of the current group. At depth zero it returns the
address of the last list.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are the static address, terminal count, leaf depth, group
exponents, current depth and group, start terminal, source and scratch address. -/
def initFlatChain (self level : ℕ) : Stmt :=
  .cond (.reg 5)
    (.assign 10 (.bin .sub (.reg 5) (.const 1)) ;;
      .call 11 level [.reg 0, .reg 1, .reg 2, .reg 10, .reg 6,
        .bin .add (.reg 8) (.const 1), .load (.reg 8), .reg 7,
        .bin .add (.reg 9) (.const 1)] ;;
      .store (.reg 9) (.bin .sub (.reg 11) (.bin .add (.reg 9) (.const 1))) ;;
      .assign 12 (.bin .div (.reg 6) (.bin .div
        (queryGroupSizeExpr (.reg 3) (.reg 4) (.reg 10))
        (queryGroupSizeExpr (.reg 3) (.reg 4) (.reg 5)))) ;;
      .call 13 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 10, .reg 12,
        .reg 7, .reg 9, .reg 11] ;;
      .ret (.reg 13))
    (.ret (.reg 8))

theorem initFlatChain_noRand (self level : ℕ) : (initFlatChain self level).NoRand := by
  simp [initFlatChain, Stmt.NoRand]

/-- The scratch interval holds the intermediate lists. The final list has the
same interpretation as `flatWalk` and memory outside the interval is preserved. -/
def initFlatChainContract (w : ℕ) (S : StaticData) (t g u v : ℕ) (es : List ℕ) : Contract where
  pre args mem := ∃ h src dst, args =
    [h, S.numTerm, leafDepth S.x S.b, S.x, S.b, t, g, u, src, dst] ∧
    StaticOut mem h S ∧ ListAt mem src (es.length :: es) ∧
    h + S.encode.length ≤ dst ∧ src + 1 + es.length ≤ dst ∧
    dst + initFlatScratch S t g u es < 2 ^ w ∧
    leafDepth S.x S.b + 1 < 2 ^ w ∧ 0 < S.b ∧
    S.H.IsValid S.x S.b ∧ t ≤ leafDepth S.x S.b ∧ 1 < groupSize S.x S.b t ∧
    g < numGroups S.x S.b t ∧ IsEdgeWalk (S.H.host t g).edges u v es
  post args mem r mem' := ∃ h src dst, args =
    [h, S.numTerm, leafDepth S.x S.b, S.x, S.b, t, g, u, src, dst] ∧
    let out := flatWalk S.H S.x S.b t g u es
    (if t = 0 then r = src else r + 1 + out.length = dst + initFlatScratch S t g u es) ∧
    ListAt mem' r (out.length :: out) ∧
    ∀ y, y < dst ∨ dst + initFlatScratch S t g u es ≤ y → mem' y = mem y
  cost _ _ := initFlatChainCost S t g u es

theorem initFlatChain_meetsContract {w f level : ℕ} {S : StaticData} {p : Program}
    (hp : p.procs[f]? = some (initFlatChain f level))
    (hlevel : ∀ j g u es, MeetsContract w p level (initFlatLevelContract w S j g u es)) :
    ∀ t g u v es, MeetsContract w p f (initFlatChainContract w S t g u v es) := by
  intro t
  induction t with
  | zero =>
    intro g u v es
    refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
    obtain ⟨h, src, dst, rfl, _, hsrc, _, hs, _⟩ := hpre
    refine runs_start_le ?_
    unfold initFlatChain
    refine runs_cond_le (v := 0) (Expr.eval_reg_of_eq rfl) (fun hn => (hn rfl).elim) ?_
    intro _
    refine runs_ret_le (v := src) (Expr.eval_reg_of_eq rfl)
      ⟨h, src, dst, rfl, rfl, hsrc, fun _ _ => rfl⟩ ?_
    simp [initFlatChainContract, initFlatChainCost, flatSteps, Expr.size]
  | succ j ih =>
    intro g u v es
    refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
    obtain ⟨h, src, dst, rfl, hS, hsrc, hsep, hs, hroom, hD, hb, hH, ht, hsize, hg, hwalk⟩ := hpre
    let D := leafDepth S.x S.b
    let next := initLevelWalk S j g u es
    let parent := parentGroup S.x S.b j g
    let fin := dst + 1 + next.length
    have ht' : j < D := ht
    have hP : S.numTerm < 2 ^ w := hw _ (by simp)
    have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos S.x) hP
    have hg' : g < S.numTerm := hg.trans_le (numGroups_le_pow _)
    have hpar : parent < numGroups S.x S.b j := parentGroup_lt_numGroups hg
    have hparw : parent < 2 ^ w := (hpar.trans_le (numGroups_le_pow _)).trans hP
    have hn : IsEdgeWalk (S.H.host j parent).edges u v next :=
      substWalk_isEdgeWalk hwalk fun e he => hH.emb_walk hsize hg (hwalk.lt_length e he)
    have he : ∀ e ∈ es, e < (S.H.host (j + 1) g).m ∧
        (edgeAt (S.H.host (j + 1) g).edges e).1 < 2 ^ w ∧
        (edgeAt (S.H.host (j + 1) g).edges e).2 < 2 ^ w := by
      intro e he
      have hi := hwalk.lt_length e he
      have hin := hH.host_inside (j + 1) g hsize hg e hi
      simp only [insideB, Bool.and_eq_true, decide_eq_true_eq] at hin
      exact ⟨hi, (Finset.mem_range.mp (members_subset_range hg hin.1)).trans hP,
        (Finset.mem_range.mp (members_subset_range hg hin.2)).trans hP⟩
    have hroom' : fin + initFlatScratch S j parent u next < 2 ^ w := by
      simpa [initFlatScratch, fin, next, parent, Nat.add_assoc] using hroom
    have hfin : fin < 2 ^ w := by omega
    have hlen : es.length < 2 ^ w := by omega
    have hnext : next.length < 2 ^ w := by omega
    have hsrcLen : mem src = es.length := (listAt_cons.mp hsrc).1
    have hsrcList : ListAt mem (src + 1) es := (listAt_cons.mp hsrc).2
    have hjw : j < 2 ^ w := by omega
    refine runs_start_le ?_
    unfold initFlatChain
    refine runs_cond_le (v := j + 1) (Expr.eval_reg_of_eq rfl) ?_ (by omega)
    intro _
    refine runs_seq_assign_le (v := j) ?_ ?_
    · exact Expr.eval_eq_of_eq
        (Expr.eval_sub (Expr.eval_reg_of_eq (v := j + 1) rfl) (Expr.eval_const h1)
          (hw (j + 1) (by simp))) (Nat.add_sub_cancel j 1)
    refine runs_seq_call_le (hlevel j g u es)
      (vs := [h, S.numTerm, D, j, g, src + 1, es.length, u, dst + 1]) ?_ ?_
      ⟨h, src + 1, dst + 1, rfl, hS, hsrcList, ht', hg', by omega, by omega,
        hfin, hD, he⟩ ?_
    · have hs' : src + 1 < 2 ^ w := by omega
      have hd' : dst + 1 < 2 ^ w := by omega
      simp [evalArgs, Expr.eval, startState, BinOp.eval, hsrcLen, h1, hs', hd', D]
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | omega | exact hw _ (by simp)
    intro r mem₁ pos₁ hp₁
    obtain ⟨h', src', dst', ha, hr, hwrite, hframe⟩ := hp₁
    simp only [List.cons.injEq, and_true] at ha
    obtain ⟨_, _, _, _, _, hs', _, _, hd'⟩ := ha
    subst src' dst' r
    change ∀ y, y < dst + 1 ∨ fin ≤ y → mem₁ y = mem y at hframe
    let mem₂ := Function.update mem₁ dst next.length
    have hleft (y : ℕ) (hy : y < dst) : mem₂ y = mem y := by
      rw [show mem₂ y = mem₁ y from Function.update_of_ne (by omega) _ _]
      exact hframe y (.inl (by omega))
    have hS₂ : StaticOut mem₂ h S :=
      listAt_congr (fun k hk => (hleft _ (by omega)).symm) hS
    have hbuf : ListAt mem₂ dst (next.length :: next) := by
      apply listAt_cons.mpr
      exact ⟨Function.update_self ..,
        listAt_congr (fun k _ => (Function.update_of_ne (by omega) _ _).symm) hwrite⟩
    refine runs_seq_store_le (x := dst) (v := next.length) (Expr.eval_reg_of_eq rfl) ?_ ?_
    · have hd : dst + 1 < 2 ^ w := by omega
      exact Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq (v := fin) rfl)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) rfl) (Expr.eval_const h1) hd) hfin)
        (Nat.add_sub_cancel_left _ _)
    refine runs_seq_assign_le (v := parent) ?_ ?_
    · have hbw : S.b < 2 ^ w := hw _ (by simp)
      have hjmul := queryDepth_mul_lt hb (show j ≤ D by omega) hP hbw
      have htmul := queryDepth_mul_lt hb ht hP hbw
      have hsz : groupSize S.x S.b j < 2 ^ w := by
        unfold groupSize
        exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans_lt hP
      exact Expr.eval_div (Expr.eval_reg_of_eq (v := g) rfl)
        (Expr.eval_div (eval_queryGroupSizeExpr
          (Expr.eval_reg_of_eq (v := S.x) rfl) (Expr.eval_reg_of_eq (v := S.b) rfl)
          (Expr.eval_reg_of_eq (v := j) rfl) hP hjmul)
          (eval_queryGroupSizeExpr (Expr.eval_reg_of_eq (v := S.x) rfl)
            (Expr.eval_reg_of_eq (v := S.b) rfl) (Expr.eval_reg_of_eq (v := j + 1) rfl)
            hP htmul) hsz) (hg'.trans hP)
    refine runs_seq_call_le (ih parent u v next)
      (vs := [h, S.numTerm, D, S.x, S.b, j, parent, u, dst, fin]) rfl ?_
      ⟨h, dst, fin, rfl, hS₂, hbuf, by omega, le_rfl, hroom', hD, hb, hH, ht'.le,
        hsize.trans_le (groupSize_succ_le j), hpar, hn⟩ ?_
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | exact hw _ (by simp [D])
    intro r mem₃ pos₃ hp₃
    obtain ⟨h', src', dst', ha, hend, hlast, hf⟩ := hp₃
    simp only [List.cons.injEq, and_true] at ha
    obtain ⟨_, _, _, _, _, _, _, _, hs', hd'⟩ := ha
    subst src' dst'
    have heq : dst + initFlatScratch S (j + 1) g u es =
        fin + initFlatScratch S j parent u next := by
      simp [initFlatScratch, fin, parent, next, Nat.add_assoc]
    have hout : r + 1 + (flatWalk S.H S.x S.b (j + 1) g u es).length =
        dst + initFlatScratch S (j + 1) g u es := by
      change r + 1 + (flatWalk S.H S.x S.b j parent u next).length = _
      rw [heq]
      by_cases hj : j = 0
      · have hrd : r = dst := by simpa only [hj, ↓reduceIte] using hend
        simp [hj, hrd, initFlatScratch, flatWalk, fin]
      · simpa only [hj, ↓reduceIte] using hend
    refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
      ⟨h, src, dst, rfl, by simpa only [Nat.succ_ne_zero, ↓reduceIte, Outcome.value] using hout, hlast, ?_⟩ ?_
    · intro y hy
      rcases hy with hy | hy
      · exact (hf y (.inl (by omega))).trans (hleft y hy)
      · rw [heq] at hy
        have hne : y ≠ dst := by omega
        exact (hf y (.inr hy)).trans ((Function.update_of_ne hne _ _).trans
          (hframe y (.inr (by omega))))
    · have hc := initFlatChainCost_step S j g u es
      simp only [initFlatChainContract, initFlatLevelContract, argsSize, Expr.size, queryGroupSizeExpr]
      change _ ≤ initFlatChainCost S (j + 1) g u es
      refine le_trans ?_ hc
      change _ ≤ 30 * next.length + 199 * es.length + 240 + initFlatChainCost S j parent u next
      dsimp only [next, parent]
      omega

end MinCostFlow.HierPaths

end
