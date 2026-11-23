module

public import MinCostFlow.ExpanderDecomp.RouteProgDFSBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Blocking DFS Accept and Backtrack Sub-Triples (`dfsAccept_triple`, `dfsBacktrack_triple`)

Defines the shared DFS invariants (`DfsStateAt`, `DfsStackAt`, `DfsRegsAt`) and
verifies `dfsAcceptStmt` (path acceptance, walk/node heap allocation, used-vertex
marking) and `dfsBacktrackStmt` (dead-vertex marking and stack pop).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Stack Helpers, Branching Helpers, and Invariant Structures -/

lemma stackVerts_length (u : ℕ) (trail : List (ℕ × ℕ)) :
    (stackVerts u trail).length = trail.length + 1 := by
  simp [stackVerts]

lemma stackVerts_reverse_getLast (u : ℕ) (trail : List (ℕ × ℕ)) :
    (stackVerts u trail).reverse[trail.length]'(by simp [stackVerts]) = u := by
  simp [stackVerts]

lemma stackVerts_reverse_push (w u e : ℕ) (trail : List (ℕ × ℕ)) :
    (stackVerts w ((u, e) :: trail)).reverse = (stackVerts u trail).reverse ++ [w] := by
  simp [stackVerts]

lemma trail_edges_reverse_push (u e : ℕ) (trail : List (ℕ × ℕ)) :
    (((u, e) :: trail).map Prod.snd).reverse = (trail.map Prod.snd).reverse ++ [e] := by
  simp

lemma stackVerts_nodup_of_dist {u : ℕ} {trail : List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    (hdist : ∀ k (hk : k < (stackVerts u trail).reverse.length),
      dist ((stackVerts u trail).reverse[k]'hk) = some k) :
    (stackVerts u trail).reverse.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  dsimp only at heq
  have h1 := hdist i hi
  have h2 := hdist j hj
  rw [heq] at h1
  rw [h1] at h2
  exact Fin.ext (Option.some.inj h2)

lemma runs_cond_pos_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s1 s2 : Stmt}
    {st : State} {P : Outcome → State → Prop} {k bound v : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : ∃ o st' c, Runs w p ω s1 st o st' c ∧ P o st' ∧ k + (e.size + 1) + c ≤ bound) :
    ∃ o st' c, Runs w p ω (.cond e s1 s2) st o st' c ∧ P o st' ∧ k + c ≤ bound := by
  obtain ⟨o, st', c, hrun, hp, hc⟩ := h1
  exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hrun, rfl⟩,
    hp, by omega⟩

lemma runs_cond_zero_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s1 s2 : Stmt}
    {st : State} {P : Outcome → State → Prop} {k bound : ℕ}
    (he : e.eval w st = some 0)
    (h2 : ∃ o st' c, Runs w p ω s2 st o st' c ∧ P o st' ∧ k + (e.size + 1) + c ≤ bound) :
    ∃ o st' c, Runs w p ω (.cond e s1 s2) st o st' c ∧ P o st' ∧ k + c ≤ bound := by
  obtain ⟨o, st', c, hrun, hp, hc⟩ := h2
  exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨0, c, he, by simpa using hrun, rfl⟩,
    hp, by omega⟩

/-- Shared memory invariant for `dfsBlockProc` across `dfsStep` and `dfsSources`. -/
structure DfsStateAt (mem mem0 : ℕ → ℕ) (X V : Finset ℕ) (adj : ℕ → List (ℕ × ℕ))
    (cfg : DfsCfg) (cfgAddr heapLo heapPtr pathsHead pathsTail : ℕ)
    (acc : List ((ℕ × ℕ) × List ℕ)) (st : DFSState) (ul : List ℕ) : Prop where
  used_sub : st.used ⊆ V
  dead_sub : st.dead ⊆ V
  paths_le : st.paths.length ≤ st.used.card
  used_stamp : ∀ v < X.card, mem (cfg.usedStampAddr + v) = cfg.dfsGen ↔ origOf X v ∈ st.used
  dead_stamp : ∀ v < X.card, mem (cfg.deadStampAddr + v) = cfg.dfsGen ↔ origOf X v ∈ st.dead
  cur_inv : ∀ v < X.card,
    (mem (cfg.curStampAddr + v) ≠ cfg.dfsGen → st.cursor (origOf X v) = adj (origOf X v)) ∧
    (mem (cfg.curStampAddr + v) = cfg.dfsGen →
      adjCsrOff X adj v ≤ mem (cfg.curAddr + v) ∧
      mem (cfg.curAddr + v) ≤ adjCsrOff X adj (v + 1) ∧
      st.cursor (origOf X v) = (adj (origOf X v)).drop (mem (cfg.curAddr + v) - adjCsrOff X adj v))
  ul_len : ul.length = st.used.card
  ul_nd : ul.Nodup
  ul_sub : ∀ x ∈ ul, x < X.card ∧ origOf X x ∈ st.used
  ul_cov : ∀ v ∈ st.used, v ∈ X ∧ locOf X v ∈ ul
  ul_at : ListAt mem cfg.usedListAddr ul
  heap_lo : cfg.heapIn ≤ heapPtr
  heap_hi : heapPtr ≤ cfg.heapIn + 5 * st.used.card
  chain : PathChainAt mem X heapLo heapPtr pathsHead pathsTail (st.paths ++ acc)
  frame_out : ∀ a, ¬ DfsWriteSet X.card cfg cfgAddr a → mem a = mem0 a
  frame_cfgOut : ∀ a, cfgAddr + 24 ≤ a ∧ a < cfgAddr + 29 → mem a = mem0 a
  stamp_cur : ∀ v < X.card, mem (cfg.curStampAddr + v) = mem0 (cfg.curStampAddr + v) ∨
    mem (cfg.curStampAddr + v) = cfg.dfsGen
  stamp_used : ∀ v < X.card, mem (cfg.usedStampAddr + v) = mem0 (cfg.usedStampAddr + v) ∨
    mem (cfg.usedStampAddr + v) = cfg.dfsGen
  stamp_dead : ∀ v < X.card, mem (cfg.deadStampAddr + v) = mem0 (cfg.deadStampAddr + v) ∨
    mem (cfg.deadStampAddr + v) = cfg.dfsGen

/-- Stack invariant for `dfsStepLoopStmt` at tip `u`, depth `r`, and `trail`. -/
structure DfsStackAt (mem : ℕ → ℕ) (X V : Finset ℕ) (dist : ℕ → Option ℕ)
    (cfg : DfsCfg) (st : DFSState) (s u r : ℕ) (trail : List (ℕ × ℕ)) : Prop where
  r_le : r ≤ cfg.targetDepth
  trail_len : trail.length = r
  s_eq : (stackVerts u trail).reverse[0]'(by simp [stackVerts]) = s
  vert_at : ListAt mem cfg.stkVertAddr ((stackVerts u trail).reverse.map (locOf X))
  edge_at : ListAt mem cfg.stkEdgeAddr (trail.map Prod.snd).reverse
  stack_ok : ∀ k (hk : k < (stackVerts u trail).reverse.length),
    let v := (stackVerts u trail).reverse[k]'hk
    v ∈ V ∧ v ∉ st.used ∧ v ∉ st.dead ∧ dist v = some k

/-- Fixed config registers `r0 .. r21` and mutable `(r22..r26)`. -/
def DfsRegsAt (regs : ℕ → ℕ) (cfg : DfsCfg) (cfgAddr heapPtr pathsHead pathsTail usedCnt pathsCnt : ℕ) :
    Prop :=
  ∀ r ≤ 26, regs r =
    match r with
    | 0 => cfgAddr
    | 1 => cfg.offAddr | 2 => cfg.nbAddr | 3 => cfg.edgeAddr
    | 4 => cfg.maskArrAddr | 5 => cfg.maskBadVal
    | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
    | 8 => cfg.visStampAddr | 9 => cfg.bfsGen | 10 => cfg.distAddr
    | 11 => cfg.curStampAddr | 12 => cfg.curAddr
    | 13 => cfg.usedStampAddr | 14 => cfg.deadStampAddr
    | 15 => cfg.stkVertAddr | 16 => cfg.stkEdgeAddr | 17 => cfg.usedListAddr
    | 18 => cfg.dfsGen | 19 => cfg.targetDepth | 20 => cfg.srcPtr | 21 => cfg.srcLen
    | 22 => heapPtr | 23 => pathsHead | 24 => pathsTail
    | 25 => usedCnt | _ => pathsCnt

/-! ## 2. Accepted Path Sub-Triple (`dfsAccept_triple`) -/

theorem dfsAccept_triple {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    {cfg : DfsCfg} {cfgAddr m2 heapLo heapPtr pathsHead pathsTail : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {ds : DFSState} {ul : List ℕ}
    {s u r : ℕ} {trail : List (ℕ × ℕ)} {mem0 : ℕ → ℕ} {st0 : State}
    (hVX : V ⊆ X)
    (hdisj : DfsDisj w X.card m2 cfg cfgAddr)
    (hheap_lo : heapLo ≤ cfg.heapIn)
    (hacc_disj : ∀ a, heapLo ≤ a ∧ a < cfg.heapIn → ¬ DfsWriteSet X.card cfg cfgAddr a)
    (hinv : DfsStateAt st0.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds ul)
    (hstk : DfsStackAt st0.mem X V dist cfg ds s u r trail)
    (hregs : DfsRegsAt st0.regs cfg cfgAddr heapPtr pathsHead pathsTail ds.used.card ds.paths.length)
    (hr28 : st0.regs 28 = locOf X s)
    (hr30 : st0.regs 30 = r)
    (hr31 : st0.regs 31 = locOf X u) :
    let es := (trail.map Prod.snd).reverse
    let vs := stackVerts u trail
    let ds' : DFSState :=
      { used := ds.used ∪ vs.toFinset
        dead := ds.dead
        cursor := ds.cursor
        paths := ((s, u), es) :: ds.paths
        cost := ds.cost + vs.length + 1 }
    Triple w p (fun st => st = st0) dfsAcceptStmt
      (normalPost fun st' =>
        ∃ heapPtr' pathsHead' pathsTail' ul',
          DfsStateAt st'.mem mem0 X V adj cfg cfgAddr heapLo heapPtr' pathsHead' pathsTail' acc ds' ul' ∧
          DfsRegsAt st'.regs cfg cfgAddr heapPtr' pathsHead' pathsTail' ds'.used.card ds'.paths.length ∧
          st'.regs 27 = st0.regs 27 ∧
          st'.regs 29 = 0)
      (fun _ => 75 * (r + 1) + 85) := by
  set sv := (stackVerts u trail).reverse with hsv_def
  set se := (trail.map Prod.snd).reverse with hse_def
  have hsv_len : sv.length = r + 1 := by simp [hsv_def, stackVerts, hstk.trail_len]
  have hse_len : se.length = r := by simp [hse_def, hstk.trail_len]
  have hsv_nd : sv.Nodup := stackVerts_nodup_of_dist fun k hk => (hstk.stack_ok k hk).2.2.2
  have hsv_disj_used : Disjoint ds.used sv.toFinset := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact (hstk.stack_ok k hk).2.1
  have hsv_sub_V : sv.toFinset ⊆ V := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact (hstk.stack_ok k hk).1
  have hused_new_sub : ds.used ∪ sv.toFinset ⊆ V := Finset.union_subset hinv.used_sub hsv_sub_V
  have hused_new_card : (ds.used ∪ sv.toFinset).card = ds.used.card + (r + 1) := by
    rw [Finset.card_union_of_disjoint hsv_disj_used, List.toFinset_card_of_nodup hsv_nd, hsv_len]
  have hused_new_le : ds.used.card + (r + 1) ≤ X.card := by
    rw [← hused_new_card]; exact Finset.card_le_card (Finset.Subset.trans hused_new_sub hVX)
  have htoFinset_eq : (stackVerts u trail).toFinset = sv.toFinset := by simp [hsv_def]
  have hsV : s ∈ V := by
    have h0 := (hstk.stack_ok 0 (by simp [stackVerts])).1
    simpa [hstk.s_eq] using h0
  have huV : u ∈ V := by
    have hl := (hstk.stack_ok trail.length (by simp [stackVerts])).1
    rw [stackVerts_reverse_getLast u trail] at hl
    exact hl
  have hsX : s ∈ X := hVX hsV
  have huX : u ∈ X := hVX huV
  have hp_hi_new : heapPtr + 1 + r + 4 ≤ cfg.heapIn + 5 * (ds.used.card + (r + 1)) := by
    have := hinv.heap_hi; omega
  have hp_hi_X : heapPtr + 1 + r + 4 ≤ cfg.heapIn + 5 * X.card := by omega
  have hhp_lo : cfg.heapIn ≤ heapPtr := hinv.heap_lo
  have hw_hp : cfg.heapIn + 5 * X.card + 5 < 2 ^ w := hdisj.w_heap
  have hw_nX : X.card + 5 < 2 ^ w := hdisj.w_nX
  have hw4 : 4 ≤ 2 ^ w := hdisj.w4
  have hpaths_le : ds.paths.length ≤ ds.used.card := hinv.paths_le
  dsimp only
  wram_enter; subst st
  unfold dfsAcceptStmt; dsimp only [seqStmts]
  have hr22_0 : st0.regs 22 = heapPtr := hregs 22 (by decide)
  have hr23_0 : st0.regs 23 = pathsHead := hregs 23 (by decide)
  have hr24_0 : st0.regs 24 = pathsTail := hregs 24 (by decide)
  have hr25_0 : st0.regs 25 = ds.used.card := hregs 25 (by decide)
  have hr26_0 : st0.regs 26 = ds.paths.length := hregs 26 (by decide)
  -- Step 1: r34 := r22, mem[r22] := r30, r22 := r22 + 1, r32 := 0
  refine runs_seq_assign_le (v := heapPtr) (by eval_expr) ?_
  refine runs_seq_store_le (x := heapPtr) (v := r) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heapPtr + 1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st1 : State :=
    { mem := Function.update st0.mem heapPtr r
      regs := Function.update (Function.update (Function.update st0.regs 34 heapPtr) 22 (heapPtr + 1)) 32 0
      pos := st0.pos }
  have hst1_regs : ∀ k ≤ 34, k ≠ 22 → k ≠ 32 → k ≠ 34 → st1.regs k = st0.regs k := by
    intro k _ h22 h32 h34
    simp [st1, Function.update_of_ne, h22, h32, h34]
  -- Step 2: edge-copy loop (r32 = 0 .. r - 1)
  have hcopy_loop :
      Triple w p
        (fun st =>
          (∀ k ≤ 34, k ≠ 32 → st.regs k = st1.regs k) ∧
          st.regs 32 ≤ r ∧
          st.mem heapPtr = r ∧
          (∀ j < st.regs 32, st.mem (heapPtr + 1 + j) = se.getD j 0) ∧
          (∀ a, a < heapPtr ∨ heapPtr + 1 + st.regs 32 ≤ a → st.mem a = st0.mem a))
        (.loop (.bin .lt (.reg 32) (.reg 30))
          (seqStmts
            [ .store (.bin .add (.reg 22) (.reg 32)) (.load (.bin .add (.reg 16) (.reg 32)))
            , .assign 32 (.bin .add (.reg 32) (.const 1)) ]))
        (normalPost fun st =>
          (∀ k ≤ 34, k ≠ 32 → st.regs k = st1.regs k) ∧
          st.regs 32 = r ∧
          SeqAt st.mem heapPtr se ∧
          (∀ a, a < heapPtr ∨ heapPtr + 1 + r ≤ a → st.mem a = st0.mem a))
        (fun st => ((Expr.bin .lt (.reg 32) (.reg 30)).size + 20 + 1) * (r - st.regs 32) +
          (Expr.bin .lt (.reg 32) (.reg 30)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => r - st.regs 32)
      (condVal := fun st => if st.regs 32 < r then 1 else 0)
      (bodyBound := 20) ?_ ?_ ?_
    · intro st ⟨hI_regs, _, _, _, _⟩
      have h30 : st.regs 30 = r := by
        rw [hI_regs 30 (by decide) (by decide), hst1_regs 30 (by decide) (by decide) (by decide) (by decide)]
        exact hr30
      eval_expr
    · intro st ⟨hI_regs, h32_le, hhp0, hcopied, hfr⟩ hv
      have h32_eq : st.regs 32 = r := by split_ifs at hv; omega
      refine ⟨hI_regs, h32_eq,
        ⟨by rw [hhp0, hse_len], fun j hj => by
          have := hcopied j (by omega)
          rwa [List.getD_eq_getElem _ _ hj] at this⟩,
        fun a ha => hfr a (by omega)⟩
    · intro stL ⟨hI_regs, h32_le, hhp0, hcopied, hfr⟩ hv
      have h32_lt : stL.regs 32 < r := by split_ifs at hv <;> omega
      have h16 : stL.regs 16 = cfg.stkEdgeAddr := by
        rw [hI_regs 16 (by decide) (by decide), hst1_regs 16 (by decide) (by decide) (by decide) (by decide)]
        exact hregs 16 (by decide)
      have h22 : stL.regs 22 = heapPtr + 1 := by
        rw [hI_regs 22 (by decide) (by decide)]; simp [st1]
      have hse_mem : stL.mem (cfg.stkEdgeAddr + stL.regs 32) = se[stL.regs 32]'(by omega) := by
        have hdisj_se : cfg.stkEdgeAddr + stL.regs 32 < heapPtr ∨
            heapPtr + 1 + stL.regs 32 ≤ cfg.stkEdgeAddr + stL.regs 32 := by
          rcases hdisj.se_hp with h | h <;> omega
        rw [hfr _ hdisj_se]
        exact hstk.edge_at (stL.regs 32) (by rw [← hse_def, hse_len]; omega)
      have hw_se : cfg.stkEdgeAddr + X.card + 5 < 2 ^ w := hdisj.w_se
      wram_enter; subst st; dsimp only [seqStmts]
      refine runs_seq_store_le (x := heapPtr + 1 + stL.regs 32) (v := se[stL.regs 32]'(by omega))
        (by eval_expr) (by rw [← hse_mem]; eval_expr) ?_
      refine runs_assign_le (v := stL.regs 32 + 1) (by eval_expr) ?_ (by wram_cost)
      refine ⟨⟨fun k hk hne => by simp [Function.update_of_ne hne, hI_regs k hk hne],
        by simp; omega,
        by simp [Function.update_of_ne (by omega : heapPtr ≠ heapPtr + 1 + stL.regs 32), hhp0],
        fun j hj => by
          simp only [Function.update_self] at hj
          by_cases hje : j = stL.regs 32
          · subst hje
            simp only [Function.update_self]
            exact (List.getD_eq_getElem se 0 (by omega : stL.regs 32 < se.length)).symm
          · simp only [Function.update_of_ne (by omega : heapPtr + 1 + j ≠ heapPtr + 1 + stL.regs 32)]
            exact hcopied j (by omega),
        fun a ha => by
          simp only [Function.update_self] at ha
          simp only [Function.update_of_ne (by omega : a ≠ heapPtr + 1 + stL.regs 32)]
          exact hfr a (by omega)⟩, by simp; omega⟩
  refine runs_seq_triple_le hcopy_loop
    ⟨fun k _ _ => rfl, Nat.zero_le _, by simp [st1], fun j hj => by simp [st1] at hj,
      fun a ha => by
        simp only [st1] at ha ⊢
        exact Function.update_of_ne (by omega) _ _⟩
    (fun st2 hst2 => ?_)
  rcases hst2 with ⟨hst2_regs, _, hseq2, hst2_fr⟩
  have hr2_22 : st2.regs 22 = heapPtr + 1 := by rw [hst2_regs 22 (by decide) (by decide)]; simp [st1]
  have hr2_23 : st2.regs 23 = pathsHead := by
    rw [hst2_regs 23 (by decide) (by decide), hst1_regs 23 (by decide) (by decide) (by decide) (by decide)]; exact hr23_0
  have hr2_24 : st2.regs 24 = pathsTail := by
    rw [hst2_regs 24 (by decide) (by decide), hst1_regs 24 (by decide) (by decide) (by decide) (by decide)]; exact hr24_0
  have hr2_26 : st2.regs 26 = ds.paths.length := by
    rw [hst2_regs 26 (by decide) (by decide), hst1_regs 26 (by decide) (by decide) (by decide) (by decide)]; exact hr26_0
  have hr2_28 : st2.regs 28 = locOf X s := by
    rw [hst2_regs 28 (by decide) (by decide), hst1_regs 28 (by decide) (by decide) (by decide) (by decide)]; exact hr28
  have hr2_30 : st2.regs 30 = r := by
    rw [hst2_regs 30 (by decide) (by decide), hst1_regs 30 (by decide) (by decide) (by decide) (by decide)]; exact hr30
  have hr2_31 : st2.regs 31 = locOf X u := by
    rw [hst2_regs 31 (by decide) (by decide), hst1_regs 31 (by decide) (by decide) (by decide) (by decide)]; exact hr31
  have hr2_34 : st2.regs 34 = heapPtr := by rw [hst2_regs 34 (by decide) (by decide)]; simp [st1]
  -- Step 3: write 4-word PathChainAt node at nd = heapPtr + 1 + r
  set nd := heapPtr + 1 + r
  refine runs_seq_assign_le (v := nd) (by eval_expr) ?_
  refine runs_seq_store_le (x := nd) (v := locOf X s) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := nd + 1) (v := locOf X u) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := nd + 2) (v := heapPtr) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := nd + 3) (v := pathsHead) (by eval_expr) (by eval_expr) ?_
  set mem3 : ℕ → ℕ :=
    Function.update
      (Function.update
        (Function.update
          (Function.update st2.mem nd (locOf X s))
          (nd + 1) (locOf X u))
        (nd + 2) heapPtr)
      (nd + 3) pathsHead
  have hmem3_fr : ∀ a, a < heapPtr ∨ nd + 4 ≤ a → mem3 a = st0.mem a := by
    intro a ha
    have h1 : a ≠ nd := by omega
    have h2 : a ≠ nd + 1 := by omega
    have h3 : a ≠ nd + 2 := by omega
    have h4 : a ≠ nd + 3 := by omega
    simp only [mem3, Function.update_of_ne h4, Function.update_of_ne h3,
      Function.update_of_ne h2, Function.update_of_ne h1]
    exact hst2_fr a (by omega)
  have hmem3_seq : SeqAt mem3 heapPtr se :=
    seqAt_congr hseq2 (fun k hk1 hk2 => by
      rw [hse_len] at hk2
      have h1 : k ≠ nd := by omega
      have h2 : k ≠ nd + 1 := by omega
      have h3 : k ≠ nd + 2 := by omega
      have h4 : k ≠ nd + 3 := by omega
      simp only [mem3, Function.update_of_ne h4, Function.update_of_ne h3,
        Function.update_of_ne h2, Function.update_of_ne h1])
  have hmem3_chain0 : PathChainAt mem3 X heapLo heapPtr pathsHead pathsTail (ds.paths ++ acc) :=
    hinv.chain.congr (fun k _ hk2 => hmem3_fr k (Or.inl hk2))
  have hmem3_chain : PathChainAt mem3 X heapLo (nd + 4) nd
      (if pathsHead = 0 then nd else pathsTail) (((s, u), se) :: (ds.paths ++ acc)) :=
    hmem3_chain0.prepend_fresh (by omega) (by omega) le_rfl (by have := hdisj.hheap_pos; omega)
      hsX huX
      (by simp [mem3, Function.update_of_ne])
      (by simp [mem3, Function.update_of_ne])
      (by simp [mem3, Function.update_of_ne])
      (by simp [mem3])
      (by omega) (by rw [hse_len]; omega) hmem3_seq
  set newTail := if pathsHead = 0 then nd else pathsTail
  set st3a : State := { mem := mem3, regs := Function.update st2.regs 22 nd, pos := st2.pos }
  set st3b : State := { mem := mem3, regs := Function.update (Function.update st2.regs 22 nd) 24 newTail, pos := st2.pos }
  have hcond_r24 :
      Triple w p (fun st => st = st3a)
        (.cond (.bin .eq (.reg 23) (.const 0)) (.assign 24 (.reg 22)) .nop)
        (normalPost fun st => st = st3b) (fun _ => 12) := by
    wram_enter; subst st
    by_cases hph : pathsHead = 0
    · refine runs_cond_pos_le (v := 1) (by simp [Expr.eval, BinOp.eval, st3a, hr2_23, hph, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega]) (by omega) ?_
      refine runs_assign_le (v := nd) (by simp [Expr.eval, st3a]) ?_ (by wram_cost)
      simp [st3a, st3b, newTail, hph]
    · refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, st3a, hr2_23, hph, show 0 < 2 ^ w by omega]) ?_
      refine runs_nop_le ?_ (by wram_cost)
      have hupd : Function.update (Function.update st2.regs 22 nd) 24 newTail =
          Function.update st2.regs 22 nd := by
        funext k
        by_cases hk : k = 24
        · subst hk; simp [newTail, hph, hr2_24]
        · simp [Function.update_of_ne hk]
      simp [st3a, st3b, hupd]
  refine runs_seq_triple_le hcond_r24 rfl (fun st3 hst3 => ?_)
  subst hst3
  refine runs_seq_assign_le (v := nd) (by simp [Expr.eval, st3b]) ?_
  refine runs_seq_assign_le (v := nd + 4) (by simp [Expr.eval, BinOp.eval, st3b, show 4 < 2 ^ w by omega, show nd + 4 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := ds.paths.length + 1)
    (by simp [Expr.eval, BinOp.eval, st3b, hr2_26, show 1 < 2 ^ w by omega, show ds.paths.length + 1 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st4 : State :=
    { mem := mem3
      regs := Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update st2.regs 22 nd) 24 newTail)
              23 nd)
            22 (nd + 4))
          26 (ds.paths.length + 1))
        32 0
      pos := st2.pos }
  have hst4_regs : ∀ k ≤ 31, k ≠ 22 → k ≠ 23 → k ≠ 24 → k ≠ 26 → st4.regs k = st0.regs k := by
    intro k hk h22 h23 h24 h26
    have h32 : k ≠ 32 := by omega
    have h34 : k ≠ 34 := by omega
    simp only [st4, Function.update_of_ne h32, Function.update_of_ne h26,
      Function.update_of_ne h22, Function.update_of_ne h23, Function.update_of_ne h24]
    rw [hst2_regs k (by omega) h32, hst1_regs k (by omega) h22 h32 h34]
  -- Step 4: mark-used loop (r32 = 0 .. r)
  have hmark_loop :
      Triple w p
        (fun st =>
          (∀ k ≤ 31, k ≠ 25 → st.regs k = st4.regs k) ∧
          st.regs 32 ≤ r + 1 ∧
          st.regs 25 = ds.used.card + st.regs 32 ∧
          (∀ v < X.card, st.mem (cfg.usedStampAddr + v) = cfg.dfsGen ↔
            origOf X v ∈ ds.used ∨ origOf X v ∈ sv.take (st.regs 32)) ∧
          (∀ v < X.card, st.mem (cfg.usedStampAddr + v) = mem3 (cfg.usedStampAddr + v) ∨
            st.mem (cfg.usedStampAddr + v) = cfg.dfsGen) ∧
          ListAt st.mem cfg.usedListAddr (ul ++ (sv.take (st.regs 32)).map (locOf X)) ∧
          (∀ a,
            (a < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ a) →
            (a < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ a) →
            st.mem a = mem3 a))
        (.loop (.bin .lt (.reg 32) (.bin .add (.reg 30) (.const 1)))
          (seqStmts
            [ .assign 35 (.load (.bin .add (.reg 15) (.reg 32)))
            , .store (.bin .add (.reg 13) (.reg 35)) (.reg 18)
            , .store (.bin .add (.reg 17) (.reg 25)) (.reg 35)
            , .assign 25 (.bin .add (.reg 25) (.const 1))
            , .assign 32 (.bin .add (.reg 32) (.const 1)) ]))
        (normalPost fun st =>
          (∀ k ≤ 31, k ≠ 25 → st.regs k = st4.regs k) ∧
          st.regs 32 = r + 1 ∧
          st.regs 25 = ds.used.card + (r + 1) ∧
          (∀ v < X.card, st.mem (cfg.usedStampAddr + v) = cfg.dfsGen ↔
            origOf X v ∈ ds.used ∨ origOf X v ∈ sv) ∧
          (∀ v < X.card, st.mem (cfg.usedStampAddr + v) = mem3 (cfg.usedStampAddr + v) ∨
            st.mem (cfg.usedStampAddr + v) = cfg.dfsGen) ∧
          ListAt st.mem cfg.usedListAddr (ul ++ sv.map (locOf X)) ∧
          (∀ a,
            (a < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ a) →
            (a < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ a) →
            st.mem a = mem3 a))
        (fun st => ((Expr.bin .lt (.reg 32) (.bin .add (.reg 30) (.const 1))).size + 35 + 1) *
          (r + 1 - st.regs 32) + (Expr.bin .lt (.reg 32) (.bin .add (.reg 30) (.const 1))).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => r + 1 - st.regs 32)
      (condVal := fun st => if st.regs 32 < r + 1 then 1 else 0)
      (bodyBound := 35) ?_ ?_ ?_
    · intro st ⟨hI_regs, _, _, _, _, _, _⟩
      have h30 : st.regs 30 = r := by
        rw [hI_regs 30 (by decide) (by decide), hst4_regs 30 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr30
      eval_expr
    · intro st ⟨hI_regs, h32_le, h25_eq, hus, hus_m, hul, hfr⟩ hv
      have h32eq : st.regs 32 = r + 1 := by split_ifs at hv; omega
      have htake : sv.take (st.regs 32) = sv := List.take_of_length_le (by omega)
      refine ⟨hI_regs, h32eq, by omega,
        fun v hv => by rw [← htake]; exact hus v hv, hus_m,
        by rw [← htake]; exact hul, hfr⟩
    · intro stL ⟨hI_regs, h32_le, h25_eq, hus, hus_m, hul, hfr⟩ hv
      have h32_lt : stL.regs 32 < r + 1 := by split_ifs at hv <;> omega
      have h13 : stL.regs 13 = cfg.usedStampAddr := by
        rw [hI_regs 13 (by decide) (by decide), hst4_regs 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hregs 13 (by decide)
      have h15 : stL.regs 15 = cfg.stkVertAddr := by
        rw [hI_regs 15 (by decide) (by decide), hst4_regs 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hregs 15 (by decide)
      have h17 : stL.regs 17 = cfg.usedListAddr := by
        rw [hI_regs 17 (by decide) (by decide), hst4_regs 17 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hregs 17 (by decide)
      have h18 : stL.regs 18 = cfg.dfsGen := by
        rw [hI_regs 18 (by decide) (by decide), hst4_regs 18 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hregs 18 (by decide)
      set vk := sv[stL.regs 32]'(by omega)
      have hvk_X : vk ∈ X := hVX (hstk.stack_ok (stL.regs 32) (by simp [stackVerts, hstk.trail_len]; omega)).1
      have hvk_loc_lt : locOf X vk < X.card := locOf_lt hvk_X
      have hsv_mem : stL.mem (cfg.stkVertAddr + stL.regs 32) = locOf X vk := by
        have hne_us : cfg.stkVertAddr + stL.regs 32 < cfg.usedStampAddr ∨
            cfg.usedStampAddr + X.card ≤ cfg.stkVertAddr + stL.regs 32 := by
          rcases hdisj.us_sv with h | h <;> omega
        have hne_ul : cfg.stkVertAddr + stL.regs 32 < cfg.usedListAddr ∨
            cfg.usedListAddr + X.card ≤ cfg.stkVertAddr + stL.regs 32 := by
          rcases hdisj.sv_ul with h | h <;> omega
        have hne_hp : cfg.stkVertAddr + stL.regs 32 < heapPtr ∨
            nd + 4 ≤ cfg.stkVertAddr + stL.regs 32 := by
          rcases hdisj.sv_hp with h | h <;> omega
        rw [hfr _ hne_us hne_ul, hmem3_fr _ hne_hp]
        have := hstk.vert_at (stL.regs 32) (by simp [stackVerts, hstk.trail_len]; omega)
        simpa [hsv_def, vk] using this
      have hw_sv : cfg.stkVertAddr + X.card + 5 < 2 ^ w := hdisj.w_sv
      have hw_us : cfg.usedStampAddr + X.card + 5 < 2 ^ w := hdisj.w_us
      have hw_ul : cfg.usedListAddr + X.card + 5 < 2 ^ w := hdisj.w_ul
      have hw_dg : cfg.dfsGen < 2 ^ w := hdisj.w_dgen
      wram_enter; subst st; dsimp only [seqStmts]
      refine runs_seq_assign_le (v := locOf X vk) (by rw [← hsv_mem]; eval_expr) ?_
      refine runs_seq_store_le (x := cfg.usedStampAddr + locOf X vk) (v := cfg.dfsGen)
        (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.usedListAddr + (ds.used.card + stL.regs 32)) (v := locOf X vk)
        (by eval_expr) (by eval_expr) ?_
      refine runs_seq_assign_le (v := ds.used.card + stL.regs 32 + 1) (by eval_expr) ?_
      refine runs_assign_le (v := stL.regs 32 + 1) (by eval_expr) ?_ (by wram_cost)
      refine ⟨⟨?_, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩, by simp; omega⟩
      · intro k hk h25
        have h32 : k ≠ 32 := by omega
        have h35 : k ≠ 35 := by omega
        simp [Function.update_of_ne, h25, h32, h35, hI_regs k hk h25]
      · intro v hv
        have hne_ul : cfg.usedStampAddr + v ≠ cfg.usedListAddr + (ds.used.card + stL.regs 32) := by
          have := disjRange_ne hdisj.us_ul hv (by omega : ds.used.card + stL.regs 32 < X.card); omega
        simp only [Function.update_self, Function.update_of_ne hne_ul]
        rw [List.take_succ_eq_append_getElem (by omega : stL.regs 32 < sv.length)]
        simp only [List.mem_append, List.mem_singleton]
        by_cases hveq : v = locOf X vk
        · subst hveq
          simp only [Function.update_self, true_iff]
          right; right; exact origOf_locOf hvk_X
        · have hne_us : cfg.usedStampAddr + v ≠ cfg.usedStampAddr + locOf X vk := by omega
          rw [Function.update_of_ne hne_us, hus v hv]
          have hne_orig : origOf X v ≠ vk := fun h => hveq (by rw [← h, locOf_origOf hv])
          tauto
      · intro v hv
        have hne_ul : cfg.usedStampAddr + v ≠ cfg.usedListAddr + (ds.used.card + stL.regs 32) := by
          have := disjRange_ne hdisj.us_ul hv (by omega : ds.used.card + stL.regs 32 < X.card); omega
        simp only [Function.update_of_ne hne_ul]
        by_cases hveq : v = locOf X vk
        · subst hveq; exact Or.inr (Function.update_self _ _ _)
        · have hne_us : cfg.usedStampAddr + v ≠ cfg.usedStampAddr + locOf X vk := by omega
          rw [Function.update_of_ne hne_us]; exact hus_m v hv
      · intro j hj
        simp only [Function.update_self, List.length_append, List.length_map, List.length_take,
          hinv.ul_len, hsv_len] at hj ⊢
        have hlen_take : min (stL.regs 32 + 1) (r + 1) = stL.regs 32 + 1 := by omega
        rw [hlen_take] at hj
        simp only [List.take_succ_eq_append_getElem (by omega : stL.regs 32 < sv.length),
          List.map_append, List.map_singleton, ← List.append_assoc]
        by_cases hje : j = ds.used.card + stL.regs 32
        · subst hje
          simp only [Function.update_self]
          have hllen : (ul ++ (sv.take (stL.regs 32)).map (locOf X)).length = ds.used.card + stL.regs 32 := by
            simp [hinv.ul_len, hsv_len]; omega
          rw [List.getElem_append_right (by omega)]
          simp [vk]
        · have hjlt : j < ds.used.card + stL.regs 32 := by omega
          have hne_ul : cfg.usedListAddr + j ≠ cfg.usedListAddr + (ds.used.card + stL.regs 32) := by omega
          have hne_us : cfg.usedListAddr + j ≠ cfg.usedStampAddr + locOf X vk := by
            have := disjRange_ne hdisj.us_ul hvk_loc_lt (by omega : j < X.card); omega
          simp only [Function.update_of_ne hne_ul, Function.update_of_ne hne_us]
          have hllen : (ul ++ (sv.take (stL.regs 32)).map (locOf X)).length = ds.used.card + stL.regs 32 := by
            simp [hinv.ul_len, hsv_len]; omega
          rw [List.getElem_append_left (by omega)]
          exact hul j (by omega)
      · intro a ha1 ha2
        have hne_ul : a ≠ cfg.usedListAddr + (ds.used.card + stL.regs 32) := by omega
        have hne_us : a ≠ cfg.usedStampAddr + locOf X vk := by omega
        simp only [Function.update_of_ne hne_ul, Function.update_of_ne hne_us]
        exact hfr a ha1 ha2
  refine runs_seq_triple_le hmark_loop
    ⟨fun k _ _ => rfl, Nat.zero_le _,
      by simp [st4, hst2_regs 25 (by decide) (by decide),
           hst1_regs 25 (by decide) (by decide) (by decide) (by decide), hr25_0],
      fun v hv => by
        have hne_hp : cfg.usedStampAddr + v < heapPtr ∨ nd + 4 ≤ cfg.usedStampAddr + v := by
          rcases hdisj.us_hp with h | h <;> omega
        simp only [st4, Function.update_self, List.take_zero, List.not_mem_nil, or_false]
        rw [hmem3_fr _ hne_hp]; exact hinv.used_stamp v hv,
      fun _ _ => Or.inl rfl,
      by
        simp only [st4, Function.update_self, List.take_zero, List.map_nil, List.append_nil]
        intro j hj
        have hne_hp : cfg.usedListAddr + j < heapPtr ∨ nd + 4 ≤ cfg.usedListAddr + j := by
          have := hinv.ul_len; rcases hdisj.ul_hp with h | h <;> omega
        rw [hmem3_fr _ hne_hp]; exact hinv.ul_at j hj,
      fun a _ _ => rfl⟩
    (fun st5 hst5 => ?_)
  rcases hst5 with ⟨hst5_regs, _, h5_25, h5_us, h5_us_m, h5_ul, h5_fr⟩
  -- Step 5: r29 := 0
  refine runs_assign_le (v := 0) (by eval_expr) ?_ ?_
  · dsimp only [normalPost]
    set ul' := ul ++ sv.map (locOf X)
    refine ⟨nd + 4, nd, newTail, ul', ?_, ?_, ?_, by simp⟩
    · refine ⟨?_, hinv.dead_sub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h5_ul, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [htoFinset_eq]; exact hused_new_sub
      · rw [htoFinset_eq, hused_new_card]; simp only [List.length_cons]; omega
      · intro v hv
        rw [h5_us v hv, htoFinset_eq, Finset.mem_union, List.mem_toFinset]
      · intro v hv
        have hne_us : cfg.deadStampAddr + v < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ cfg.deadStampAddr + v := by
          rcases hdisj.us_ds with h | h <;> omega
        have hne_ul : cfg.deadStampAddr + v < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ cfg.deadStampAddr + v := by
          rcases hdisj.ds_ul with h | h <;> omega
        have hne_hp : cfg.deadStampAddr + v < heapPtr ∨ nd + 4 ≤ cfg.deadStampAddr + v := by
          rcases hdisj.ds_hp with h | h <;> omega
        rw [h5_fr _ hne_us hne_ul, hmem3_fr _ hne_hp]
        exact hinv.dead_stamp v hv
      · intro v hv
        have hcs_eq : st5.mem (cfg.curStampAddr + v) = st0.mem (cfg.curStampAddr + v) := by
          have h1 : cfg.curStampAddr + v < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ cfg.curStampAddr + v := by
            rcases hdisj.cs_us with h | h <;> omega
          have h2 : cfg.curStampAddr + v < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ cfg.curStampAddr + v := by
            rcases hdisj.cs_ul with h | h <;> omega
          have h3 : cfg.curStampAddr + v < heapPtr ∨ nd + 4 ≤ cfg.curStampAddr + v := by
            rcases hdisj.cs_hp with h | h <;> omega
          rw [h5_fr _ h1 h2, hmem3_fr _ h3]
        have hcur_eq : st5.mem (cfg.curAddr + v) = st0.mem (cfg.curAddr + v) := by
          have h1 : cfg.curAddr + v < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ cfg.curAddr + v := by
            rcases hdisj.cur_us with h | h <;> omega
          have h2 : cfg.curAddr + v < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ cfg.curAddr + v := by
            rcases hdisj.cur_ul with h | h <;> omega
          have h3 : cfg.curAddr + v < heapPtr ∨ nd + 4 ≤ cfg.curAddr + v := by
            rcases hdisj.cur_hp with h | h <;> omega
          rw [h5_fr _ h1 h2, hmem3_fr _ h3]
        rw [hcs_eq, hcur_eq]; exact hinv.cur_inv v hv
      · rw [htoFinset_eq, hused_new_card]; simp [ul', hinv.ul_len, hsv_len]
      · rw [List.nodup_append]
        refine ⟨hinv.ul_nd, ?_, ?_⟩
        · rw [List.nodup_map_iff_inj_on hsv_nd]
          intro x hx y hy hxy
          have hxX : x ∈ X := hVX (hsv_sub_V (List.mem_toFinset.mpr hx))
          have hyX : y ∈ X := hVX (hsv_sub_V (List.mem_toFinset.mpr hy))
          rw [← origOf_locOf hxX, hxy, origOf_locOf hyX]
        · intro x hx y hy hxy
          subst hxy
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
          have hvX : v ∈ X := hVX (hsv_sub_V (List.mem_toFinset.mpr hv))
          have hmem_used : v ∈ ds.used := by
            have := (hinv.ul_sub (locOf X v) hx).2
            rwa [origOf_locOf hvX] at this
          exact Finset.disjoint_left.mp hsv_disj_used hmem_used (List.mem_toFinset.mpr hv)
      · intro x hx
        rw [htoFinset_eq]
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact ⟨(hinv.ul_sub x hx1).1, Finset.mem_union_left _ (hinv.ul_sub x hx1).2⟩
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx2
          have hvX : v ∈ X := hVX (hsv_sub_V (List.mem_toFinset.mpr hv))
          exact ⟨locOf_lt hvX, by rw [origOf_locOf hvX]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hv)⟩
      · intro v hv
        rw [htoFinset_eq, Finset.mem_union, List.mem_toFinset] at hv
        rcases hv with hv1 | hv2
        · exact ⟨(hinv.ul_cov v hv1).1, List.mem_append_left _ (hinv.ul_cov v hv1).2⟩
        · exact ⟨hVX (hsv_sub_V (List.mem_toFinset.mpr hv2)),
            List.mem_append_right _ (List.mem_map_of_mem hv2)⟩
      · omega
      · rw [htoFinset_eq, hused_new_card]; omega
      · exact hmem3_chain.congr (fun k hk1 hk2 => by
          have h1 : k < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ k := by
            by_cases hlt : k < cfg.heapIn
            · by_contra hc; push Not at hc
              exact hacc_disj k ⟨hk1, hlt⟩ (Or.inr (Or.inr (Or.inl hc)))
            · rcases hdisj.us_hp with h | h <;> omega
          have h2 : k < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ k := by
            by_cases hlt : k < cfg.heapIn
            · by_contra hc; push Not at hc
              exact hacc_disj k ⟨hk1, hlt⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))
            · rcases hdisj.ul_hp with h | h <;> omega
          exact h5_fr k h1 h2)
      · intro a ha
        have h1 : a < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ a := by
          by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inl hc)))
        have h2 : a < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ a := by
          by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))
        have h3 : a < heapPtr ∨ nd + 4 ≤ a := by
          by_contra hc; push Not at hc
          exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))))
        rw [h5_fr a h1 h2, hmem3_fr a h3]
        exact hinv.frame_out a ha
      · intro a ha
        have h1 : a < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ a := by
          rcases hdisj.us_co with h | h <;> omega
        have h2 : a < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ a := by
          rcases hdisj.ul_co with h | h <;> omega
        have h3 : a < heapPtr ∨ nd + 4 ≤ a := by
          rcases hdisj.co_hp with h | h <;> omega
        rw [h5_fr a h1 h2, hmem3_fr a h3]
        exact hinv.frame_cfgOut a ha
      · intro v hv
        have h1 : cfg.curStampAddr + v < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ cfg.curStampAddr + v := by
          rcases hdisj.cs_us with h | h <;> omega
        have h2 : cfg.curStampAddr + v < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ cfg.curStampAddr + v := by
          rcases hdisj.cs_ul with h | h <;> omega
        have h3 : cfg.curStampAddr + v < heapPtr ∨ nd + 4 ≤ cfg.curStampAddr + v := by
          rcases hdisj.cs_hp with h | h <;> omega
        rw [h5_fr _ h1 h2, hmem3_fr _ h3]; exact hinv.stamp_cur v hv
      · intro v hv
        rcases h5_us_m v hv with h | h
        · have h3 : cfg.usedStampAddr + v < heapPtr ∨ nd + 4 ≤ cfg.usedStampAddr + v := by
            rcases hdisj.us_hp with h' | h' <;> omega
          rw [h, hmem3_fr _ h3]; exact hinv.stamp_used v hv
        · exact Or.inr h
      · intro v hv
        have h1 : cfg.deadStampAddr + v < cfg.usedStampAddr ∨ cfg.usedStampAddr + X.card ≤ cfg.deadStampAddr + v := by
          rcases hdisj.us_ds with h | h <;> omega
        have h2 : cfg.deadStampAddr + v < cfg.usedListAddr ∨ cfg.usedListAddr + X.card ≤ cfg.deadStampAddr + v := by
          rcases hdisj.ds_ul with h | h <;> omega
        have h3 : cfg.deadStampAddr + v < heapPtr ∨ nd + 4 ≤ cfg.deadStampAddr + v := by
          rcases hdisj.ds_hp with h | h <;> omega
        rw [h5_fr _ h1 h2, hmem3_fr _ h3]; exact hinv.stamp_dead v hv
    · intro k hk
      have hne29 : k ≠ 29 := by omega
      simp only [Function.update_of_ne hne29]
      by_cases h25 : k = 25
      · subst h25; rw [h5_25, htoFinset_eq, hused_new_card]
        rfl
      · rw [hst5_regs k (by omega) h25]
        by_cases h22 : k = 22
        · subst h22; simp [st4]
        · by_cases h23 : k = 23
          · subst h23; simp [st4]
          · by_cases h24 : k = 24
            · subst h24; simp [st4]
            · by_cases h26 : k = 26
              · subst h26; simp [st4]
              · rw [hst4_regs k (by omega) h22 h23 h24 h26]
                have := hregs k hk
                interval_cases k <;> omega
    · simp only [Function.update_of_ne (by decide : 27 ≠ 29)]
      rw [hst5_regs 27 (by decide) (by decide), hst4_regs 27 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only [Expr.size, st1, st4, Function.update_self, Nat.sub_zero]
    omega

/-! ## 3. Backtrack Sub-Triple (`dfsBacktrack_triple`) -/

theorem dfsBacktrack_triple {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    {cfg : DfsCfg} {cfgAddr m2 heapLo heapPtr pathsHead pathsTail : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {ds : DFSState} {ul : List ℕ}
    {s u r : ℕ} {trail : List (ℕ × ℕ)} {mem0 : ℕ → ℕ} {st0 : State}
    (hVX : V ⊆ X)
    (hdisj : DfsDisj w X.card m2 cfg cfgAddr)
    (_hheap_lo : heapLo ≤ cfg.heapIn)
    (hacc_disj : ∀ a, heapLo ≤ a ∧ a < cfg.heapIn → ¬ DfsWriteSet X.card cfg cfgAddr a)
    (hinv : DfsStateAt st0.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds ul)
    (hstk : DfsStackAt st0.mem X V dist cfg ds s u r trail)
    (hregs : DfsRegsAt st0.regs cfg cfgAddr heapPtr pathsHead pathsTail ds.used.card ds.paths.length)
    (hr28 : st0.regs 28 = locOf X s)
    (hr29 : st0.regs 29 = 1)
    (hr30 : st0.regs 30 = r)
    (hr31 : st0.regs 31 = locOf X u) :
    let ds1 : DFSState := { ds with dead := insert u ds.dead, cost := ds.cost + 1 }
    Triple w p (fun st => st = st0) dfsBacktrackStmt
      (normalPost fun st' =>
        DfsStateAt st'.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul ∧
        DfsRegsAt st'.regs cfg cfgAddr heapPtr pathsHead pathsTail ds1.used.card ds1.paths.length ∧
        st'.regs 27 = st0.regs 27 ∧
        st'.regs 28 = locOf X s ∧
        match trail with
        | [] => st'.regs 29 = 0
        | (par, _) :: rest =>
          st'.regs 29 = 1 ∧
          st'.regs 30 = r - 1 ∧
          st'.regs 31 = locOf X par ∧
          DfsStackAt st'.mem X V dist cfg ds1 s par (r - 1) rest)
      (fun _ => 25) := by
  set sv := (stackVerts u trail).reverse with hsv_def
  have hsv_len : sv.length = r + 1 := by simp [hsv_def, stackVerts, hstk.trail_len]
  have huV : u ∈ V := by
    have hl := (hstk.stack_ok trail.length (by simp [stackVerts])).1
    rw [stackVerts_reverse_getLast u trail] at hl
    exact hl
  have huX : u ∈ X := hVX huV
  have hu_loc_lt : locOf X u < X.card := locOf_lt huX
  have hr14 : st0.regs 14 = cfg.deadStampAddr := hregs 14 (by decide)
  have hr15 : st0.regs 15 = cfg.stkVertAddr := hregs 15 (by decide)
  have hr18 : st0.regs 18 = cfg.dfsGen := hregs 18 (by decide)
  have hw_ds : cfg.deadStampAddr + X.card + 5 < 2 ^ w := hdisj.w_ds
  have hw_sv : cfg.stkVertAddr + X.card + 5 < 2 ^ w := hdisj.w_sv
  have hw_dg : cfg.dfsGen < 2 ^ w := hdisj.w_dgen
  have hw_nX : X.card + 5 < 2 ^ w := hdisj.w_nX
  have hw4 : 4 ≤ 2 ^ w := hdisj.w4
  have hr_lt_X : r < X.card := by
    have hnd := stackVerts_nodup_of_dist fun k hk => (hstk.stack_ok k hk).2.2.2
    have hsub : sv.toFinset ⊆ X := fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
      exact hVX (hstk.stack_ok k hk).1
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at hcard
    rw [hsv_def] at hsv_len; omega
  set mem1 := Function.update st0.mem (cfg.deadStampAddr + locOf X u) cfg.dfsGen
  have hinv1 : DfsStateAt mem1 mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc
      { ds with dead := insert u ds.dead, cost := ds.cost + 1 } ul := by
    refine ⟨hinv.used_sub, Finset.insert_subset huV hinv.dead_sub, hinv.paths_le, ?_, ?_, ?_,
      hinv.ul_len, hinv.ul_nd, hinv.ul_sub, hinv.ul_cov, ?_, hinv.heap_lo, hinv.heap_hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      have hne : cfg.usedStampAddr + v ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.us_ds hv hu_loc_lt; omega
      simp only [mem1, Function.update_of_ne hne]; exact hinv.used_stamp v hv
    · intro v hv
      by_cases hveq : v = locOf X u
      · subst hveq; simp [mem1, origOf_locOf huX]
      · have hne : cfg.deadStampAddr + v ≠ cfg.deadStampAddr + locOf X u := by omega
        simp only [mem1, Function.update_of_ne hne, Finset.mem_insert]
        have hne_u : origOf X v ≠ u := fun h => hveq (by rw [← h, locOf_origOf hv])
        rw [hinv.dead_stamp v hv]; tauto
    · intro v hv
      have hne1 : cfg.curStampAddr + v ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.cs_ds hv hu_loc_lt; omega
      have hne2 : cfg.curAddr + v ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.cur_ds hv hu_loc_lt; omega
      simp only [mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
      exact hinv.cur_inv v hv
    · intro j hj
      have hne : cfg.usedListAddr + j ≠ cfg.deadStampAddr + locOf X u := by
        have hle := hinv.ul_len
        have hcard : ds.used.card ≤ X.card := Finset.card_le_card (Finset.Subset.trans hinv.used_sub hVX)
        have := disjRange_ne hdisj.ds_ul hu_loc_lt (by omega : j < X.card); omega
      simp only [mem1, Function.update_of_ne hne]; exact hinv.ul_at j hj
    · exact hinv.chain.congr (fun k hk1 hk2 => by
        have hne : k ≠ cfg.deadStampAddr + locOf X u := by
          by_cases hlt : k < cfg.heapIn
          · intro heq; subst heq
            exact hacc_disj _ ⟨hk1, hlt⟩ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
          · have hhi : heapPtr ≤ cfg.heapIn + 5 * X.card := by
              have := hinv.heap_hi
              have := Finset.card_le_card (Finset.Subset.trans hinv.used_sub hVX); omega
            have := disjRange_ne hdisj.ds_hp hu_loc_lt (by omega : k - cfg.heapIn < 5 * X.card); omega
        exact Function.update_of_ne hne _ _)
    · intro a ha
      have hne : a ≠ cfg.deadStampAddr + locOf X u := fun heq =>
        ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
      simp only [mem1, Function.update_of_ne hne]; exact hinv.frame_out a ha
    · intro a ha
      have hne : a ≠ cfg.deadStampAddr + locOf X u := by
        rcases hdisj.ds_co with h | h <;> omega
      simp only [mem1, Function.update_of_ne hne]; exact hinv.frame_cfgOut a ha
    · intro v hv
      have hne : cfg.curStampAddr + v ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.cs_ds hv hu_loc_lt; omega
      simp only [mem1, Function.update_of_ne hne]; exact hinv.stamp_cur v hv
    · intro v hv
      have hne : cfg.usedStampAddr + v ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.us_ds hv hu_loc_lt; omega
      simp only [mem1, Function.update_of_ne hne]; exact hinv.stamp_used v hv
    · intro v hv
      by_cases hveq : v = locOf X u
      · subst hveq; exact Or.inr (Function.update_self _ _ _)
      · have hne : cfg.deadStampAddr + v ≠ cfg.deadStampAddr + locOf X u := by omega
        simp only [mem1, Function.update_of_ne hne]; exact hinv.stamp_dead v hv
  dsimp only
  wram_enter; subst st; unfold dfsBacktrackStmt; dsimp only [seqStmts]
  refine runs_seq_store_le (x := cfg.deadStampAddr + locOf X u) (v := cfg.dfsGen)
    (by eval_expr) (by eval_expr) ?_
  cases trail with
  | nil =>
    have hr0 : r = 0 := by have := hstk.trail_len; simp at this; omega
    subst hr0
    refine runs_cond_zero_le (by eval_expr) ?_
    refine runs_assign_le (v := 0) (by eval_expr) ?_ (by wram_cost)
    refine ⟨hinv1, fun k hk => by simp [Function.update_of_ne (by omega : k ≠ 29), hregs k hk],
      by simp, by simp [hr28], by simp⟩
  | cons pe rest =>
    rcases pe with ⟨par, e⟩
    have hr_pos : 0 < r := by have := hstk.trail_len; simp at this; omega
    have hlen_r : rest.length = r - 1 := by have := hstk.trail_len; simp at this; omega
    have hpar_mem : mem1 (cfg.stkVertAddr + (r - 1)) = locOf X par := by
      have hne : cfg.stkVertAddr + (r - 1) ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.ds_sv hu_loc_lt (by omega : r - 1 < X.card); omega
      simp only [mem1, Function.update_of_ne hne]
      have h1 := hstk.vert_at (r - 1) (by simp [stackVerts]; omega)
      have hget : (stackVerts u ((par, e) :: rest)).reverse[r - 1]'(by simp [stackVerts]; omega) = par := by
        have heq : (stackVerts u ((par, e) :: rest)).reverse = (stackVerts par rest).reverse ++ [u] := by
          simp [stackVerts]
        have hlen_sv : (stackVerts par rest).reverse.length = r := by simp [stackVerts, hlen_r]; omega
        simp only [heq, List.getElem_append_left (by omega : r - 1 < (stackVerts par rest).reverse.length)]
        have := stackVerts_reverse_getLast par rest
        simpa [hlen_r] using this
      rw [List.getElem_map] at h1
      rw [hget] at h1
      exact h1
    refine runs_cond_pos_le (v := r) (by eval_expr) (by omega) ?_
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := r - 1) (by eval_expr) ?_
    refine runs_assign_le (v := locOf X par) (by rw [← hpar_mem]; eval_expr) ?_ (by wram_cost)
    refine ⟨hinv1,
      fun k hk => by simp [Function.update_of_ne (by omega : k ≠ 30), Function.update_of_ne (by omega : k ≠ 31), hregs k hk],
      by simp, by simp [hr28], by simp [hr29], by simp, by simp, ?_⟩
    have hpush : (stackVerts u ((par, e) :: rest)).reverse = (stackVerts par rest).reverse ++ [u] := by
      simp [stackVerts]
    have hepush : (((par, e) :: rest).map Prod.snd).reverse = (rest.map Prod.snd).reverse ++ [e] := by simp
    refine ⟨by have := hstk.r_le; omega, hlen_r, ?_, ?_, ?_, ?_⟩
    · have h0 := hstk.s_eq
      simp only [hpush, List.getElem_append_left (by simp [stackVerts] : 0 < (stackVerts par rest).reverse.length)] at h0
      exact h0
    · intro k hk
      simp only [List.length_map, List.length_reverse, stackVerts_length, hlen_r] at hk
      have hne : cfg.stkVertAddr + k ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.ds_sv hu_loc_lt (by omega : k < X.card); omega
      simp only [Function.update_of_ne hne]
      have h1 := hstk.vert_at k (by simp [stackVerts]; omega)
      have h1' : st0.mem (cfg.stkVertAddr + k) =
          (((stackVerts par rest).reverse.map (locOf X)) ++ [locOf X u])[k]'(by simp [stackVerts, hlen_r]; omega) := by
        simpa [hpush] using h1
      rw [List.getElem_append_left (by simp [stackVerts, hlen_r]; omega)] at h1'
      exact h1'
    · intro k hk
      simp only [List.length_reverse, List.length_map, hlen_r] at hk
      have hne : cfg.stkEdgeAddr + k ≠ cfg.deadStampAddr + locOf X u := by
        have := disjRange_ne hdisj.ds_se hu_loc_lt (by omega : k < X.card); omega
      simp only [Function.update_of_ne hne]
      have h1 := hstk.edge_at k (by simp; omega)
      have h1' : st0.mem (cfg.stkEdgeAddr + k) = ((rest.map Prod.snd).reverse ++ [e])[k]'(by simp [hlen_r]; omega) := by
        simpa [hepush] using h1
      rw [List.getElem_append_left (by simp [hlen_r]; omega)] at h1'
      exact h1'
    · intro k hk
      have hk' : k < (stackVerts u ((par, e) :: rest)).reverse.length := by
        simp only [List.length_reverse, stackVerts_length, hstk.trail_len] at hk ⊢; omega
      have hok := hstk.stack_ok k hk'
      have hget : (stackVerts u ((par, e) :: rest)).reverse[k]'hk' = (stackVerts par rest).reverse[k]'hk := by
        simp only [hpush, List.getElem_append_left hk]
      rw [hget] at hok
      refine ⟨hok.1, hok.2.1, ?_, hok.2.2.2⟩
      simp only [Finset.mem_insert, not_or]
      refine ⟨fun heq => ?_, hok.2.2.1⟩
      have hdu : dist u = some r := by
        have hlast := (hstk.stack_ok ((par, e) :: rest).length (by simp [stackVerts])).2.2.2
        rw [stackVerts_reverse_getLast u ((par, e) :: rest), hstk.trail_len] at hlast
        exact hlast
      have hd1 := hok.2.2.2
      rw [heq, hdu] at hd1
      have hkr : r = k := Option.some.inj hd1
      simp only [List.length_reverse, stackVerts_length, hlen_r] at hk
      omega

end MinCostFlow.ExpanderDecomp
