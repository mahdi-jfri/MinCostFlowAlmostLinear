module

public import MinCostFlow.HierPaths.BuildTopRootSeeded

/-! # Building the root and the whole recursion schedule -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Prepare the root, the player table, and the schedule, in that order. -/
def buildTopPrepare (root players schedule : ℕ) : Stmt :=
  .call 10 root [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4] ;;
  .assign 11 (.bin .add (.bin .add (.reg 10) (.reg 2)) (.const 1)) ;;
  .assign 12 (buildTopRepliesExpr (.reg 11) (.reg 4) (.reg 5) (.reg 4)) ;;
  .call 13 players [.reg 12,.reg 4,.reg 10,.reg 5,.reg 7,.reg 8,.reg 9] ;;
  .call 13 schedule [.reg 5,.reg 6,.reg 11,.reg 4,.reg 12] ;;
  .ret (.reg 10)

theorem buildTopPrepare_noRand (root players schedule : ℕ) :
    (buildTopPrepare root players schedule).NoRand := by
  simp [buildTopPrepare, Stmt.NoRand]

/-- The intermediate layout and the first free word after preparation. -/
def buildTopPrepareTable (r x : ℕ) : ℕ := r + 2 ^ x + 1
def buildTopPrepareHeap (r x n : ℕ) : ℕ :=
  buildTopScheduleEnd (buildTopPrepareTable r x) n x + 7 * n

/-- Preparation uses the same storage layout for every choice of future replies. -/
theorem buildTopPrepare_meetsContract {w f root players schedule ga h x b n num den : ℕ}
    {p : Program} {G : Graph}
    (hf : p.procs[f]? = some (buildTopPrepare root players schedule))
    (hr : MeetsContract w p root (buildTopRootSeededContract w ga h (2 ^ x) n G))
    (hp : ∀ dst term, MeetsContract w p players (buildTopPlayerSetupContract w dst n term x G.m num den))
    (hs : ∀ table src term, MeetsContract w p schedule
      (buildTopScheduleRunContract w x b table n src term G.m (dOf num den))) :
    let P := 2 ^ x
    let graph := buildTopRootGraphAddr h G.n G.m
    MeetsContract w p f {
      pre := fun args mem => args = [ga,h,P,graph,n,x,b,G.m,num,den] ∧
        (buildTopRootSeededContract w ga h P n G).pre [ga,h,P,graph,n] mem ∧
        0 < x ∧ 0 < num ∧ 0 < den ∧ den < 2 ^ w ∧
        8 * G.m + 8 < 2 ^ w ∧ depthOf G.m ^ 3 < 2 ^ w ∧
        100 * dOf num den < 2 ^ w ∧ 4 * PParam ParamConfig.default P (depthOf G.m) < 2 ^ w ∧
        P < 2 ^ w ∧ 49 * (x + 1) + 2 < 2 ^ w ∧ n ≤ leafDepth x b ∧ 0 < b ∧ b ≤ x ∧
        buildTopPrepareHeap (h + buildTopRootSpace G.n G.m) x n < 2 ^ w
      post := fun _ mem r mem' =>
        let table := buildTopPrepareTable r x
        (∃ rootMem, (buildTopRootSeededContract w ga h P n G).post [ga,h,P,graph,n] mem r rootMem ∧
          ∀ y, y < table ∨ table + 13 * n ≤ y →
            (y < buildTopScheduleEnd table n x ∨ buildTopPrepareHeap r x n ≤ y) →
            mem' y = rootMem y) ∧
        (∀ j < n, ∀ dir addr graphs, ListAt mem' (table + 13 * j)
          ((buildTopScheduledDepth table n r x b G.m (dOf num den) j dir addr graphs).scheduleWords
            (buildTopSchedulePointer table n j) (buildTopSchedulePointer table n (j + 1)))) ∧
        ZeroFrom mem' (buildTopPrepareHeap r x n)
      cost := fun _ mem => (buildTopRootSeededContract w ga h P n G).cost [ga,h,P,graph,n] mem +
        (buildTopPlayerSetupContract w 0 n 0 x G.m num den).cost [] mem + 389 * n + 110 } := by
  dsimp only
  refine meetsContract_of_runs hf fun args mem pos ω hword hpre => ?_
  obtain ⟨rfl,hroot,hx,hnum,hden,hdenw,hm,hcube,hrootScale,hinner,hP,hdegree,hdepth,hb,hbx,hspace⟩ := hpre
  let P := 2 ^ x
  let graph := buildTopRootGraphAddr h G.n G.m
  refine runs_start_le ?_
  unfold buildTopPrepare
  refine runs_seq_call_le hr (vs := [ga,h,P,graph,n]) rfl
    (fun a ha => hword a (List.mem_append_left _ ha)) hroot ?_
  intro r mem₁ pos₁ hpost
  have hpostKeep := hpost
  obtain ⟨⟨rootMem,hraw,_⟩,_,_,_,hz⟩ := hpost
  obtain ⟨ga',h',he,_,_,_,hrhi,_,_⟩ := hraw
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl⟩ := he
  let table := buildTopPrepareTable r x
  let src := buildTopScheduleEnd table n x
  have hheap : buildTopPrepareHeap r x n < 2 ^ w := by
    apply lt_of_le_of_lt _ hspace
    unfold buildTopPrepareHeap buildTopPrepareTable buildTopScheduleEnd
      buildTopScheduleReplies buildTopSchedulePointer
    omega
  have hsrc : src + 7 * n < 2 ^ w := hheap
  have htable : table + 13 * n ≤ src := by
    unfold src buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer
    omega
  have hsrcW : src < 2 ^ w := by omega
  have htableW : table < 2 ^ w := by omega
  have hpreTable : r + 2 ^ x < 2 ^ w := Nat.lt_of_succ_lt htableW
  have hrw : r < 2 ^ w := (Nat.le_add_right _ _).trans_lt hpreTable
  have h1 : 1 < 2 ^ w := by omega
  have h13 : 13 < 2 ^ w := by
    obtain ⟨_,hh,_⟩ := hroot
    obtain ⟨_,_,_,_,_,_,_,_,_,hw⟩ := hh
    omega
  refine runs_seq_assign_le (v := table)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      hpreTable) (Expr.eval_const h1)
      htableW) ?_
  refine runs_seq_assign_le (v := src)
    (eval_buildTopRepliesExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h13 hP hsrcW) ?_
  refine runs_seq_call_le (hp src r) (vs := [src,n,r,x,G.m,num,den]) rfl ?_
    ⟨rfl,hx,hnum,hden,hdenw,hm,hcube,hrootScale,hinner,hP,hdegree,hsrc⟩ ?_
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exact hword _ (by simp)
    · exact hrw
    · exact hword _ (by simp)
    · exact hword _ (by simp)
    · exact hword _ (by simp)
    · exact hdenw
  intro a mem₂ pos₂ ⟨_,hplayers,hfp⟩
  have hwords : ∀ j < n, ∀ v ∈ buildTopPlayerWords r x G.m (dOf num den) j, v < 2 ^ w := by
    intro j _ v hv
    simp only [buildTopPlayerWords,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hrw
    · exact hP
    · exact (Nat.le_self_pow (by decide : 3 ≠ 0) _).trans_lt hcube
    · exact hdegree
    · exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 49)).trans_lt (by omega)
    · exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 49)).trans_lt (by omega)
    · split <;> assumption
  refine runs_seq_call_le (hs table src r) (vs := [x,b,table,n,src]) rfl ?_
    ⟨rfl,hdepth,hb,hbx,hP,by omega,hsrc,.inr htable,hwords,hplayers⟩ ?_
  · intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hword _ (by simp)
    · exact hword _ (by simp)
    · omega
    · exact hword _ (by simp)
    · omega
  intro v mem₃ pos₃ ⟨_,hrows,hfs⟩
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ⟨⟨mem₁,hpostKeep,?_⟩,hrows,?_⟩ ?_
  · intro y hy hz'
    exact (hfs y hy).trans (hfp y hz')
  · intro y hy
    change src + 7 * n ≤ y at hy
    change mem₃ y = 0
    refine (hfs y (.inr (by omega))).trans ((hfp y (.inr hy)).trans (hz y ?_))
    simp only [src, buildTopScheduleEnd, buildTopScheduleReplies, buildTopSchedulePointer,
      table, buildTopPrepareTable] at hy ⊢
    omega
  · simp only [Expr.size, argsSize, buildTopRepliesExpr, buildTopPointerExpr,
      buildTopScheduleRunContract, buildTopPlayerSetupContract, buildTopRootSeededContract,
      buildTopRootLayoutContract, buildTopRootContract, buildTopPortContract]
    omega

end MinCostFlow.HierPaths

end
