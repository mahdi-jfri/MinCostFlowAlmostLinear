module

public import MinCostFlow.SparseCore.Program.TourSplayQuery
public import MinCostFlow.SparseCore.Program.TourOpsEditCommon
import Mathlib.Tactic

/-!
# Splay helper procedures for vertex-split (`moveEnds`)

Builds and verifies on top of `TourSplayQuery`:
- `tourSplayRankBody [nb, x, fuel, heap]`: splays `x` to root and returns its 0-based in-order rank
  `t.toList.idxOf x` (`O(log (cap + 2))` amortized);
- `tourWalkFrontBody [nb, r, fuel, heap]`: brings the leftmost node of optional tree `r` to root and
  returns its id (`0` if `r = 0`, `O(log (cap + 2))` amortized);
- `tourMoveSplitLoopBody [nb, tRem, pairsPtr, nxtPtr, m, fuel, outHeap]` and its single-step
  invariant `tourMoveSplit_step` (`tourMoveSplitLoopBody_runs` is in `TourOpsMoveSplit.lean`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Constants and WordRAM procedure bodies -/

/-- Amortized per-`(m + 1) * log` cost constant for `tourMoveSplitLoopBody`. -/
def TOUR_MOVE_STEP_AMORT : ℕ := 500000

/-- `tourSplayRank [nb, x, fuel, heap]`: splay `x` to root and return the exact size of its left
subtree (`TourSum.sz` at node offset `12`), which equals `t.toList.idxOf x`. -/
def tourSplayRankBody (splayProc : ℕ) : Stmt :=
  .call 4 splayProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1)))) ;;
  .cond (.bin .eq (.reg 5) (.const 0))
    (.ret (.const 0))
    (.ret (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))) (.const 12))))

/-- `tourWalkFront [nb, r, fuel, heap]`: walk to leftmost node of tree `r`, splay it to root, and
return it (or `0` when `r = 0`). -/
def tourWalkFrontBody (walkProc splayProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.call 4 walkProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
     .call 5 splayProc [.reg 0, .reg 4, .reg 2, .reg 3] ;;
     .ret (.reg 4))

/-- `tourMoveSplitLoop [nb, tRem, pairsPtr, nxtPtr, m, fuel, outHeap]`:
iteratively splits `tRem` along `m` sorted block starts `u_i = mem[pairsPtr + 2*i + 1]` and
next-block starts `w_i = mem[nxtPtr + i]` (`0` when `u_i` is the last block) into `(tA, tB)`,
storing `tA` at `outHeap` and `tB` at `outHeap + 1` (using `outHeap + 2` as 2-word splay scratch). -/
def tourMoveSplitLoopBody (splayProc detachLeftProc joinProc : ℕ) : Stmt :=
  .assign 7 (.const 0) ;;
  .assign 8 (.const 0) ;;
  .assign 9 (.const 0) ;;
  .assign 10 (.bin .add (.reg 6) (.const 2)) ;;
  .loop (.bin .lt (.reg 9) (.reg 4))
    (.assign 11 (.load (.bin .add (.reg 2) (.bin .add (.bin .add (.reg 9) (.reg 9)) (.const 1)))) ;;
     .assign 12 (.load (.bin .add (.reg 3) (.reg 9))) ;;
     .call 13 splayProc [.reg 0, .reg 11, .reg 5, .reg 10] ;;
     .call 13 detachLeftProc [.reg 0, .reg 11, .reg 10] ;;
     .call 8 joinProc [.reg 0, .reg 8, .reg 13, .reg 5, .reg 10] ;;
     .assign 1 (.reg 11) ;;
     .cond (.bin .eq (.reg 12) (.const 0))
       (.call 7 joinProc [.reg 0, .reg 7, .reg 1, .reg 5, .reg 10] ;;
        .assign 1 (.const 0))
       (.call 13 splayProc [.reg 0, .reg 12, .reg 5, .reg 10] ;;
        .call 13 detachLeftProc [.reg 0, .reg 12, .reg 10] ;;
        .call 7 joinProc [.reg 0, .reg 7, .reg 13, .reg 5, .reg 10] ;;
        .assign 1 (.reg 12)) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1))) ;;
  .call 8 joinProc [.reg 0, .reg 8, .reg 1, .reg 5, .reg 10] ;;
  .store (.reg 6) (.reg 7) ;;
  .store (.bin .add (.reg 6) (.const 1)) (.reg 8) ;;
  .ret (.const 0)

theorem tourMoveSplay_bodies_noRand (wP sP dL jP : ℕ) :
    (tourSplayRankBody sP).NoRand ∧
    (tourWalkFrontBody wP sP).NoRand ∧
    (tourMoveSplitLoopBody sP dL jP).NoRand := by
  simp [tourSplayRankBody, tourWalkFrontBody, tourMoveSplitLoopBody, Stmt.NoRand]

/-! ## Amortized run theorem for `tourSplayRankBody` -/

theorem idxOf_left_append_cons {L R : List ℕ} {x : ℕ} (hnd : (L ++ x :: R).Nodup) :
    (L ++ x :: R).idxOf x = L.length := by
  have hxL : x ∉ L := fun hm => (List.nodup_append.mp hnd).2.2 x hm x (by simp) rfl
  rw [List.idxOf_append_of_notMem hxL, List.idxOf_cons_self, Nat.add_zero]

/-- `tourSplayRankBody [nb, x, fuel, heap]` splays `x` to root and returns `t.toList.idxOf x`. -/
theorem tourSplayRankBody_runs {w nb cap heap fuel x pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t' s' o st' c,
      Runs w p ω (tourSplayRankBody C.splay.splay)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      o.value = t.toList.idxOf x ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t' :: rest) ∧
      TourValsOk w cap s' ∧
      t'.toList = t.toList ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_FIND_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide
  have h17 : 17 < 2 ^ w := hheap.stride_lt
  have hroom := hheap.room
  have hf0 : TourForestInv cap st ([] ++ t :: rest) := hf
  have hdep : t.depthOf x < fuel := lt_trans (auxTree_depthOf_lt_countNodes hx)
    (lt_of_le_of_lt (hf.countNodes_le (by simp)) hfuel)
  obtain ⟨t', o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hout₁, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C ω hnodes hf0 hvals hx hdep hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel x
  obtain ⟨_, _, _, _, _, _, hval₁, _⟩ := tourSplay_preserves hf0 hx hdep
  cases ht'c : t' with
  | leaf => exact absurd ht'c hne₁
  | node xid L R =>
    have hxid : xid = x := by simpa [ht'c, AuxTree.rootId] using hroot₁
    subst hxid; rw [ht'c] at hinv₁ hlist₁ hcost₁
    have hsub := (hinv₁.treesInv (AuxTree.node xid L R) (by simp)).sub
    have hnd := (hinv₁.treesInv (AuxTree.node xid L R) (by simp)).nodup
    have hx_cap : xid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList])).2
    have hAx : nb + 17 * xid < 2 ^ w := by
      have := hheap.addr_lt hx_cap; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
    have h17x : 17 * xid < 2 ^ w := by omega
    have hmem_l : st₁.mem (nb + 17 * xid) = L.rootId := by
      have hnd_x := hn₁ xid hx_cap
      simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_LEFT, hsub.2.1] using hnd_x.1
    set s0 : State := startState [nb, xid, fuel, heap] mem pos
    have hc1 := runs_call_regs4 4 0 1 2 3 (st := s0) C.splay.splay_body
      (by simp [s0, startState]) (by simp [s0, startState]) (by simp [s0, startState]) (by simp [s0, startState]) hrun₁
    set r1 := Function.update s0.regs 4 o₁.value
    set r2 := Function.update r1 5 L.rootId
    have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1)))))
        { st₁ with regs := r1 } .normal { st₁ with regs := r2 } 7 :=
      runs_assign_iff.mpr ⟨L.rootId, by
        simp [Expr.eval, r1, s0, startState, BinOp.eval, h17, h17x, hAx, hmem_l], rfl, rfl, rfl⟩
    have hidx_eq : t.toList.idxOf xid = L.toList.length := by
      rw [← hlist₁]
      have htol : (AuxTree.node xid L R).toList = L.toList ++ xid :: R.toList := by simp [AuxTree.toList]
      rw [htol] at hnd ⊢; exact idxOf_left_append_cons hnd
    cases L with
    | leaf =>
      have hcond : (Expr.bin .eq (.reg 5) (.const 0)).eval w { st₁ with regs := r2 } = some 1 := by
        simp [Expr.eval, r2, AuxTree.rootId, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      have hret := runs_ret_const (w := w) (p := p) (ω := ω) (st := { st₁ with regs := r2 }) (v := 0) (by omega)
      refine ⟨AuxTree.node xid .leaf R, s₁, .returned 0, { st₁ with regs := r2 }, _,
        tour_runs_seq_normal hc1 (tour_runs_seq_normal ha5 (tour_runs_cond_true hcond (by omega) hret)),
        by simp [Outcome.value, hidx_eq, AuxTree.toList], hn₁, hfr₁, hinv₁, hvals₁, hlist₁, hval₁, hout₁, ?_⟩
      simp only [List.nil_append, Expr.size, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT] at hcost₁ ⊢; omega
    | node lid ll lr =>
      have hsubL := hsub.2.2.2.2.2.2.2.1
      have hl_nz : lid ≠ 0 := hsubL.1
      have hl_cap : lid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node xid (.node lid ll lr) R) (by simp)
        (by simp [AuxTree.toList])).2
      have hAl : nb + 17 * lid + 12 < 2 ^ w := by
        have := hheap.addr_lt hl_cap; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
      have h17l : 17 * lid < 2 ^ w := by omega
      have hnrL : ∀ z ∈ (AuxTree.node lid ll lr).toList, (s₁.nodes z).rev = false := fun z hz =>
        hinv₁.noRev z (hinv₁.mem_inCap (t := AuxTree.node xid (.node lid ll lr) R) (by simp)
          (by rw [AuxTree.toList]; exact List.mem_append_left _ (List.mem_append_left _ hz))).2
      have hsz_eq : (s₁.nodes lid).sum.sz = (AuxTree.node lid ll lr).toList.length := by
        rw [hsubL.2.2.2.2.2.2.1, tourEvalPairs_eq_map hnrL, tourPayload_listSummary_sz, List.length_map]
      have hmem_sz : st₁.mem (nb + 17 * lid + 12) = (AuxTree.node lid ll lr).toList.length := by
        have hnd_l := hn₁ lid hl_cap
        have hoff : tourLayout.offSum = 12 := rfl
        simpa [NodeLayout.nodeAddr, tourLayout_stride, hoff, Nat.add_assoc, hsz_eq] using hnd_l.2.2.2.2.2.2.2.1.1
      have hcond : (Expr.bin .eq (.reg 5) (.const 0)).eval w { st₁ with regs := r2 } = some 0 := by
        simp [Expr.eval, r2, AuxTree.rootId, hl_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hret : Runs w p ω (.ret (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))) (.const 12))))
          { st₁ with regs := r2 } (.returned (AuxTree.node lid ll lr).toList.length) { st₁ with regs := r2 } 9 :=
        runs_ret_iff.mpr ⟨(AuxTree.node lid ll lr).toList.length, by
          simp [Expr.eval, r2, r1, s0, startState, AuxTree.rootId, BinOp.eval,
            h17, (by omega : 12 < 2 ^ w), h17l, (by omega : nb + 17 * lid < 2 ^ w), hAl, hmem_sz],
          rfl, rfl, rfl⟩
      refine ⟨AuxTree.node xid (.node lid ll lr) R, s₁, .returned (AuxTree.node lid ll lr).toList.length,
        { st₁ with regs := r2 }, _,
        tour_runs_seq_normal hc1 (tour_runs_seq_normal ha5 (tour_runs_cond_false hcond hret)),
        by simp [Outcome.value, hidx_eq], hn₁, hfr₁, hinv₁, hvals₁, hlist₁, hval₁, hout₁, ?_⟩
      simp only [List.nil_append, Expr.size, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT] at hcost₁ ⊢; omega

/-! ## Amortized run theorem for `tourWalkFrontBody` -/

/-- `tourWalkFrontBody [nb, r, fuel, heap]` returns the leftmost node of optional tree `t?` (`0`
when `none`), preserving the forest and in-order list in `O(log (cap + 2))` amortized time. -/
theorem tourWalkFrontBody_runs {w nb cap heap fuel pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t? : Option AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (optTrees t? ++ rest)) (hvals : TourValsOk w cap st)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t'? s' o st' c,
      Runs w p ω (tourWalkFrontBody C.walkProc C.splay.splay)
        (startState [nb, optRoot t?, fuel, heap] mem pos) o st' c ∧
      o.value = optRoot t'? ∧
      (optList t?).head?.getD 0 = o.value ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = optList t? ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ optList t?, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees t? ++ rest) + TOUR_JOIN_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide
  cases t? with
  | none =>
    set s0 : State := startState [nb, 0, fuel, heap] mem pos
    have hcond : (Expr.bin .eq (.reg 1) (.const 0)).eval w s0 = some 1 := by
      simp [Expr.eval, s0, startState, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
    have hret := runs_ret_const (w := w) (p := p) (ω := ω) (st := s0) (v := 0) (by omega)
    refine ⟨none, st, .returned 0, s0, _, tour_runs_cond_true hcond (by omega) hret, by simp [Outcome.value, optRoot],
      by simp [Outcome.value, optList], hnodes, TreeFrame.refl hheap.zero, hf, hvals, rfl,
      fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    simp only [Expr.size, TOUR_JOIN_AMORT]; omega
  | some t =>
    have ht_mem : t ∈ optTrees (some t) ++ rest := by simp [optTrees]
    have ht_ne : t ≠ .leaf := hf.nonEmpty t ht_mem
    have hr_nz : t.rootId ≠ 0 := by
      cases t with
      | leaf => exact absurd rfl ht_ne
      | node _ _ _ => exact (hf.treesInv _ ht_mem).sub.1
    have hcnt : t.countNodes < fuel := lt_of_le_of_lt (hf.countNodes_le ht_mem) hfuel
    have hf0 : TourForestInv cap st ([] ++ t :: rest) := by simpa [optTrees] using hf
    obtain ⟨m, t', o₁, st₁, c₁, o₂, st₂, c₂, hrun₁, hv₁, hrun₂, hn₂, hfr₂, hinv₂, hvals₂,
      hne₂, hroot₂, _, hlist₂, hm_head, hout₂, hcost₂⟩ :=
      tourFindLeftmost_cost_le (pos := pos) C ω hnodes hf0 hvals hcnt hfuelW hheap
    have hdep : t.depthOf m < fuel := lt_trans (auxTree_depthOf_lt_countNodes (List.mem_of_head? hm_head)) hcnt
    obtain ⟨_, _, _, _, _, _, hval₂, _⟩ := tourSplay_preserves hf0 (List.mem_of_head? hm_head) hdep
    set s0 : State := startState [nb, t.rootId, fuel, heap] mem pos
    have hcond : (Expr.bin .eq (.reg 1) (.const 0)).eval w s0 = some 0 := by
      simp [Expr.eval, s0, startState, hr_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hc1 := runs_call_regs4 4 0 1 2 3 (st := s0) C.walk_body
      (by simp [s0, startState]) (by simp [s0, startState]) (by simp [s0, startState]) (by simp [s0, startState]) hrun₁
    set r1 := Function.update s0.regs 4 o₁.value
    have hc2 := runs_call_regs4 5 0 4 2 3 (st := { st₁ with regs := r1 }) C.splay.splay_body
      (by simp [r1, s0, startState]) (by simp [r1, hv₁]) (by simp [r1, s0, startState]) (by simp [r1, s0, startState]) hrun₂
    set r2 := Function.update r1 5 o₂.value
    have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := { st₂ with regs := r2 }) (r := 4) (v := m) (by simp [r2, r1, hv₁])
    refine ⟨some t', SplayState.splay tourPayload st fuel m, .returned m, { st₂ with regs := r2 }, _,
      tour_runs_cond_false hcond (tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 hret)),
      by simp [Outcome.value, optRoot, hroot₂], by simp [Outcome.value, optList, hm_head], hn₂, hfr₂,
      by simpa [optTrees] using hinv₂, hvals₂, by simpa [optList] using hlist₂, hval₂,
      by simpa [optList] using hout₂, ?_⟩
    simp only [optTrees, Option.toList, List.nil_append, List.cons_append, Expr.size,
      TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT] at hcost₂ ⊢; omega

/-! ## Pure block-split lemma and single-step invariant -/

theorem split_flatMap_head {f : ℕ → List ℕ} {P Q : List ℕ} {u : ℕ}
    (hnd : ((P ++ u :: Q).flatMap f).Nodup) (hhd : (f u).head? = some u) :
    ∀ L R : List ℕ, L ++ u :: R = (P ++ u :: Q).flatMap f →
      L = P.flatMap f ∧ u :: R = f u ++ Q.flatMap f := by
  intro L R heq
  cases hfu : f u with
  | nil => rw [hfu] at hhd; simp at hhd
  | cons u0 fus =>
    have hu0 : u0 = u := Option.some.inj (by simpa [hfu] using hhd)
    rcases hu0 with rfl
    have h2 : L ++ u0 :: R = P.flatMap f ++ u0 :: (fus ++ Q.flatMap f) := by
      simpa [List.flatMap_append, List.flatMap_cons, hfu, List.cons_append, List.append_assoc] using heq
    have hu_nP : u0 ∉ P.flatMap f := fun hm => by
      have hnd' : (P.flatMap f ++ u0 :: (fus ++ Q.flatMap f)).Nodup := by
        simpa [List.flatMap_append, List.flatMap_cons, hfu, List.cons_append, List.append_assoc] using hnd
      exact (List.nodup_append.mp hnd').2.2 u0 hm u0 (by simp) rfl
    have hu_nL : u0 ∉ L := fun hm => by
      have hnd' : (L ++ u0 :: R).Nodup := heq ▸ hnd
      exact (List.nodup_append.mp hnd').2.2 u0 hm u0 (by simp) rfl
    have hsub : ∀ {xs ys : List ℕ}, u0 ∉ xs → u0 ∉ ys → xs ++ u0 :: R = ys ++ u0 :: (fus ++ Q.flatMap f) → xs = ys := by
      intro xs ys hux huy hxy
      induction xs generalizing ys with
      | nil =>
        cases ys with
        | nil => rfl
        | cons y yss => exact absurd ((List.cons.inj hxy).1.symm ▸ List.mem_cons_self) huy
      | cons x xss ihx =>
        cases ys with
        | nil => exact absurd ((List.cons.inj hxy).1 ▸ List.mem_cons_self) hux
        | cons y yss =>
          have h1 := List.cons.inj hxy
          exact congrArg₂ List.cons h1.1 (ihx (fun hm => hux (by simp [hm])) (fun hm => huy (by simp [hm])) h1.2)
    have hL_eq : L = P.flatMap f := hsub hu_nL hu_nP h2
    rw [hL_eq] at h2
    exact ⟨hL_eq, by simpa [hfu] using List.append_cancel_left h2⟩

/-- Specification of the next-block sentinel `wNxt` for the remaining block-head list `Q`. -/
def NextBlockSpec (f : ℕ → List ℕ) (wNxt : ℕ) : List ℕ → Prop
  | [] => wNxt = 0
  | q0 :: _ => wNxt = q0 ∧ (f q0).head? = some q0

/-- One iteration step of `tourMoveSplitLoopBody` on splay forest `(tA?, tB?, tRem?)`. -/
theorem tourMoveSplit_step {w nb cap outHeap fuel pos u wNxt : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit}
    {tA? tB? tRem? : Option AuxTree} {rest : List AuxTree}
    {f : ℕ → List ℕ} {P Q : List ℕ}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (optTrees tA? ++ optTrees tB? ++ optTrees tRem? ++ rest))
    (hvals : TourValsOk w cap st)
    (htRem_eq : optList tRem? = (P ++ u :: Q).flatMap f)
    (hhd_u : (f u).head? = some u)
    (hw_spec : NextBlockSpec f wNxt Q)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap (outHeap + 2) 2 mem)
    {r : ℕ → ℕ} (hr0 : r 0 = nb) (_hr1 : r 1 = optRoot tRem?)
    (hr5 : r 5 = fuel) (hr7 : r 7 = optRoot tA?) (hr8 : r 8 = optRoot tB?)
    (hr10 : r 10 = outHeap + 2) (hr11 : r 11 = u) (hr12 : r 12 = wNxt) :
    ∃ tA'? tB'? tRem'? s' st' c,
      Runs w p ω
        (.call 13 C.splay.splay [.reg 0, .reg 11, .reg 5, .reg 10] ;;
         .call 13 C.detachLeft [.reg 0, .reg 11, .reg 10] ;;
         .call 8 C.join [.reg 0, .reg 8, .reg 13, .reg 5, .reg 10] ;;
         .assign 1 (.reg 11) ;;
         .cond (.bin .eq (.reg 12) (.const 0))
           (.call 7 C.join [.reg 0, .reg 7, .reg 1, .reg 5, .reg 10] ;;
            .assign 1 (.const 0))
           (.call 13 C.splay.splay [.reg 0, .reg 12, .reg 5, .reg 10] ;;
            .call 13 C.detachLeft [.reg 0, .reg 12, .reg 10] ;;
            .call 7 C.join [.reg 0, .reg 7, .reg 13, .reg 5, .reg 10] ;;
            .assign 1 (.reg 12)))
        ⟨mem, r, pos⟩ .normal st' c ∧
      (∀ k, k ≠ 1 → k ≠ 7 → k ≠ 8 → k ≠ 13 → st'.regs k = r k) ∧
      st'.regs 1 = optRoot tRem'? ∧ st'.regs 7 = optRoot tA'? ∧ st'.regs 8 = optRoot tB'? ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap (outHeap + 2) mem st'.mem ∧
      TourForestInv cap s' (optTrees tA'? ++ optTrees tB'? ++ optTrees tRem'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList tA'? = optList tA? ++ f u ∧
      optList tB'? = optList tB? ++ P.flatMap f ∧
      optList tRem'? = Q.flatMap f ∧
      (∀ z ≤ cap, (s'.nodes z).val = (st.nodes z).val) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees tA'? ++ optTrees tB'? ++ optTrees tRem'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees tA? ++ optTrees tB? ++ optTrees tRem? ++ rest) +
          (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3000) * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide
  have hu_mem_flat : u ∈ (P ++ u :: Q).flatMap f :=
    List.mem_flatMap.mpr ⟨u, by simp, List.mem_of_head? hhd_u⟩
  cases htRemc : tRem? with
  | none =>
    rw [htRemc] at htRem_eq; simp only [optList, Option.elim] at htRem_eq
    rw [← htRem_eq] at hu_mem_flat; simp at hu_mem_flat
  | some tRem =>
    rw [htRemc] at hf htRem_eq
    have htRem_list : tRem.toList = (P ++ u :: Q).flatMap f := by simpa [optList] using htRem_eq
    have hu_tRem : u ∈ tRem.toList := by rwa [htRem_list]
    have hinv_rem : TourForestInv cap st ((optTrees tA? ++ optTrees tB?) ++ tRem :: rest) := by
      simpa [optTrees, List.append_assoc] using hf
    have hdep_u : tRem.depthOf u < fuel := lt_trans (auxTree_depthOf_lt_countNodes hu_tRem)
      (lt_of_le_of_lt (hinv_rem.countNodes_le (by simp)) hfuel)
    obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, _, hcost₁⟩ :=
      tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hinv_rem hvals hu_tRem hdep_u hfuelW hheap
    set s₁ := SplayState.splay tourPayload st fuel u
    obtain ⟨_, _, _, _, _, _, hval₁, _⟩ := tourSplay_preserves hinv_rem hu_tRem hdep_u
    cases ht₁c : t₁ with
    | leaf => exact absurd ht₁c hne₁
    | node uid L₁ R₁ =>
      have huid : uid = u := by simpa [ht₁c, AuxTree.rootId] using hroot₁
      subst huid; rw [ht₁c] at hinv₁ hlist₁ hcost₁
      have hnd₁ := (hinv₁.treesInv (AuxTree.node uid L₁ R₁) (by simp)).nodup
      have ⟨hL₁_eq, hR₁_eq⟩ := split_flatMap_head (P := P) (Q := Q) (by rw [← htRem_list, ← hlist₁]; exact hnd₁) hhd_u
        L₁.toList R₁.toList (by simpa [AuxTree.toList] using hlist₁.trans htRem_list)
      have hsub₁ := (hinv₁.treesInv (AuxTree.node uid L₁ R₁) (by simp)).sub
      have hu_cap : uid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node uid L₁ R₁) (by simp) (by simp [AuxTree.toList])).2
      obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachLeftBody_runs (pos := st₁.pos)
        C.toTourSplayCoreProcs ω hn₁ hinv₁.ptrOk hu_cap
        ⟨hheap.rec_le, by have := hheap.room; omega, hfr₁.1, hheap.wide⟩
        (tourDetachLeft_sumOk hinv₁ hvals₁)
      obtain ⟨hinv₂, _, hval₂, hphi₂⟩ := tourDetachLeft_preserves hinv₁
      set s₂ := tourDetachLeft s₁ uid
      have hvals₂ : TourValsOk w cap s₂ := ⟨hvals₁.1, fun z hz => by rw [hval₂ z hz]; exact hvals₁.2 z hz⟩
      let L₁? : Option AuxTree := if L₁ = .leaf then none else some L₁
      have hL₁_root : o₂.value = optRoot L₁? := by
        simp only [hv₂, hsub₁.1, ↓reduceIte, hsub₁.2.1]; cases L₁ <;> simp [L₁?, optRoot, AuxTree.rootId]
      have hL₁_list : optList L₁? = P.flatMap f := by
        rw [← hL₁_eq]; cases L₁ <;> simp [L₁?, optList, AuxTree.toList]
      set tMid := AuxTree.node uid .leaf R₁
      have hperm₂ : ((optTrees tA? ++ optTrees tB?) ++ ((if L₁ = .leaf then [] else [L₁]) ++ [tMid]) ++ rest).Perm
          (optTrees tB? ++ optTrees L₁? ++ (optTrees tA? ++ tMid :: rest)) := by
        have h1 : (if L₁ = .leaf then [] else [L₁]) = optTrees L₁? := by cases L₁ <;> simp [L₁?, optTrees]
        rw [h1]
        have hp1 : (optTrees tA? ++ optTrees tB?).Perm (optTrees tB? ++ optTrees tA?) := List.perm_append_comm
        have hp2 := hp1.append_right (optTrees L₁? ++ [tMid] ++ rest)
        have hp3 : (optTrees tA? ++ optTrees L₁?).Perm (optTrees L₁? ++ optTrees tA?) := List.perm_append_comm
        have hp4 := (hp3.append_left (optTrees tB?)).append_right ([tMid] ++ rest)
        simp only [List.append_assoc] at hp2 hp4 ⊢
        exact hp2.trans hp4
      have hinv₂' : TourForestInv cap s₂ (optTrees tB? ++ optTrees L₁? ++ (optTrees tA? ++ tMid :: rest)) :=
        (hinv₂.perm hperm₂).1
      obtain ⟨tB'?, s₃, o₃, st₃, c₃, hrun₃, hv₃, hn₃, hfr₃, hinv₃, hvals₃, hlist₃, hval₃, _, hcost₃⟩ :=
        tourJoinBody_runs (pos := st₂.pos) C ω hn₂ hinv₂' hvals₂ hfuel hfuelW
          ⟨hheap.rec_le, hheap.room, (hfr₁.trans hfr₂).1, hheap.wide⟩
      have hc1 := runs_call_regs4 13 0 11 5 10 (st := ⟨mem, r, pos⟩) C.splay.splay_body hr0 hr11 hr5 hr10 hrun₁
      set r1 := Function.update r 13 o₁.value
      have hc2 := runs_call_regs3 13 0 11 10 (st := { st₁ with regs := r1 }) C.detachLeft_body
        (by simp [r1, hr0]) (by simp [r1, hr11]) (by simp [r1, hr10]) hrun₂
      set r2 := Function.update r1 13 o₂.value
      have hc3 := runs_call_regs5 8 0 8 13 5 10 (st := { st₂ with regs := r2 }) C.join_body
        (by simp [r2, r1, hr0]) (by simp [r2, r1, hr8]) (by simp [r2, hL₁_root])
        (by simp [r2, r1, hr5]) (by simp [r2, r1, hr10]) hrun₃
      set r3 := Function.update r2 8 o₃.value
      set r4 := Function.update r3 1 uid
      have ha1 : Runs w p ω (.assign 1 (.reg 11)) { st₃ with regs := r3 } .normal { st₃ with regs := r4 } 2 :=
        runs_assign_iff.mpr ⟨uid, by simp [Expr.eval, r3, r2, r1, hr11], rfl, rfl, rfl⟩
      have hpre_run := tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 (tour_runs_seq_normal hc3 ha1))
      have hfr13 : TreeFrame tourLayout nb cap (outHeap + 2) mem st₃.mem := hfr₁.trans (hfr₂.trans hfr₃)
      have hval13 : ∀ z ≤ cap, (s₃.nodes z).val = (st.nodes z).val := fun z hz => by
        rw [hval₃ z hz, hval₂ z hz]; exact hval₁ z hz
      have hphi_pre : c₁ + c₂ + c₃ + TOUR_PHI_MULT * forestPhi (optTrees tB'? ++ (optTrees tA? ++ tMid :: rest)) ≤
          TOUR_PHI_MULT * forestPhi (optTrees tA? ++ optTrees tB? ++ optTrees (some tRem) ++ rest) +
            (TOUR_SPLAY_AMORT + TOUR_JOIN_AMORT + 1200) * (Nat.log 2 (cap + 2) + 1) := by
        have hpeq2 := forestPhi_perm hperm₂
        have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
        have hpeq0 : forestPhi ((optTrees tA? ++ optTrees tB?) ++ tRem :: rest) =
            forestPhi (optTrees tA? ++ optTrees tB? ++ optTrees (some tRem) ++ rest) := by
          simp [optTrees, List.append_assoc]
        rw [← hpeq2] at hcost₃; rw [hpeq0] at hcost₁
        simp only [TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT] at hcost₁ hcost₃ hphi2' hc₂ ⊢
        nlinarith
      cases Q with
      | nil =>
        have hw0 : wNxt = 0 := by simpa [NextBlockSpec] using hw_spec
        have hcond : (Expr.bin .eq (.reg 12) (.const 0)).eval w { st₃ with regs := r4 } = some 1 := by
          simp [Expr.eval, r4, r3, r2, r1, hr12, hw0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
        have hperm3 : (optTrees tB'? ++ (optTrees tA? ++ tMid :: rest)).Perm
            (optTrees tA? ++ optTrees (some tMid) ++ (optTrees tB'? ++ rest)) := by
          have hp1 : (optTrees tB'? ++ optTrees tA? ++ [tMid]).Perm (optTrees tA? ++ [tMid] ++ optTrees tB'?) := by
            simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tB'?) (l₂ := optTrees tA? ++ [tMid]))
          simpa [optTrees, List.append_assoc] using hp1.append_right rest
        have hinv₃' : TourForestInv cap s₃ (optTrees tA? ++ optTrees (some tMid) ++ (optTrees tB'? ++ rest)) :=
          (hinv₃.perm hperm3).1
        obtain ⟨tA'?, s₄, o₄, st₄, c₄, hrun₄, hv₄, hn₄, hfr₄, hinv₄, hvals₄, hlist₄, hval₄, _, hcost₄⟩ :=
          tourJoinBody_runs (pos := st₃.pos) C ω hn₃ hinv₃' hvals₃ hfuel hfuelW
            ⟨hheap.rec_le, hheap.room, hfr13.1, hheap.wide⟩
        have hc4 := runs_call_regs5 7 0 7 1 5 10 (st := { st₃ with regs := r4 }) C.join_body
          (by simp [r4, r3, r2, r1, hr0]) (by simp [r4, r3, r2, r1, hr7])
          (by simp [r4, optRoot, tMid, AuxTree.rootId]) (by simp [r4, r3, r2, r1, hr5])
          (by simp [r4, r3, r2, r1, hr10]) hrun₄
        set r5 := Function.update r4 7 o₄.value
        set r6 := Function.update r5 1 0
        have ha2 : Runs w p ω (.assign 1 (.const 0)) { st₄ with regs := r5 } .normal { st₄ with regs := r6 } 2 :=
          runs_assign_const (by omega)
        have hperm4 : (optTrees tA'? ++ (optTrees tB'? ++ rest)).Perm
            (optTrees tA'? ++ optTrees tB'? ++ optTrees none ++ rest) := by
          simp [optTrees, List.append_assoc]
        refine ⟨tA'?, tB'?, none, s₄, { st₄ with regs := r6 }, _,
          runs_seqAppend hpre_run (tour_runs_cond_true hcond (by omega) (tour_runs_seq_normal hc4 ha2)),
          fun k h1 h7 h8 h13 => by simp [r6, r5, r4, r3, r2, r1, h1, h7, h8, h13],
          by simp [r6, optRoot], by simp [r6, r5, hv₄], by simp [r6, r5, r4, r3, hv₃],
          hn₄, hfr13.trans hfr₄, (hinv₄.perm hperm4).1, hvals₄,
          by rw [hlist₄]; have hmid : optList (some tMid) = f uid := by simpa [optList, tMid, AuxTree.toList] using hR₁_eq
             rw [hmid],
          by rw [hlist₃, hL₁_list], by simp [optList],
          fun z hz => (hval₄ z hz).trans (hval13 z hz), ?_⟩
        have hpeq3 := forestPhi_perm hperm3
        have hpeq4 := forestPhi_perm hperm4
        rw [← hpeq4]; rw [← hpeq3] at hcost₄
        simp only [Expr.size, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT] at hphi_pre hcost₄ ⊢
        omega
      | cons q0 Q' =>
        obtain ⟨hwq, hhd_q0⟩ : wNxt = q0 ∧ (f q0).head? = some q0 := by simpa [NextBlockSpec] using hw_spec
        have hq0_mem : q0 ∈ tMid.toList := by
          have : q0 ∈ f uid ++ (q0 :: Q').flatMap f :=
            List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨q0, by simp, List.mem_of_head? hhd_q0⟩))
          simpa [tMid, AuxTree.toList, hR₁_eq] using this
        have hinv₃_mid : TourForestInv cap s₃ ((optTrees tB'? ++ optTrees tA?) ++ tMid :: rest) := by
          simpa [List.append_assoc] using hinv₃
        have hq0_nz : q0 ≠ 0 := Nat.ne_of_gt (hinv₃_mid.mem_inCap (t := tMid) (by simp) hq0_mem).1
        have hcond : (Expr.bin .eq (.reg 12) (.const 0)).eval w { st₃ with regs := r4 } = some 0 := by
          simp [Expr.eval, r4, r3, r2, r1, hr12, hwq, hq0_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
        have hdep_q : tMid.depthOf q0 < fuel := lt_trans (auxTree_depthOf_lt_countNodes hq0_mem)
          (lt_of_le_of_lt (hinv₃_mid.countNodes_le (by simp)) hfuel)
        obtain ⟨t₄, o₄, st₄, c₄, hrun₄, hn₄, hfr₄, hinv₄, hvals₄, hne₄, hroot₄, hlist₄, _, hcost₄⟩ :=
          tourSplay_runs_amort (pos := st₃.pos) C.toTourSplayCoreProcs ω hn₃ hinv₃_mid hvals₃ hq0_mem hdep_q hfuelW
            ⟨hheap.rec_le, hheap.room, hfr13.1, hheap.wide⟩
        set s₄ := SplayState.splay tourPayload s₃ fuel q0
        obtain ⟨_, _, _, _, _, _, hval₄, _⟩ := tourSplay_preserves hinv₃_mid hq0_mem hdep_q
        cases ht₄c : t₄ with
        | leaf => exact absurd ht₄c hne₄
        | node qid L₄ R₄ =>
          have hqid : qid = q0 := by simpa [ht₄c, AuxTree.rootId] using hroot₄
          subst hqid; rw [ht₄c] at hinv₄ hlist₄ hcost₄
          have hnd₄ := (hinv₄.treesInv (AuxTree.node qid L₄ R₄) (by simp)).nodup
          have htMid_flat : tMid.toList = ([uid] ++ qid :: Q').flatMap f := by
            simpa [tMid, AuxTree.toList, List.flatMap_cons] using hR₁_eq
          have ⟨hL₄_eq, hR₄_eq⟩ := split_flatMap_head (P := [uid]) (Q := Q')
            (by rw [← htMid_flat, ← hlist₄]; exact hnd₄) hhd_q0
            L₄.toList R₄.toList (by simpa [AuxTree.toList] using hlist₄.trans htMid_flat)
          have hsub₄ := (hinv₄.treesInv (AuxTree.node qid L₄ R₄) (by simp)).sub
          have hq_cap : qid ≤ cap := (hinv₄.mem_inCap (t := AuxTree.node qid L₄ R₄) (by simp) (by simp [AuxTree.toList])).2
          obtain ⟨o₅, st₅, c₅, hrun₅, ⟨hv₅, hn₅, hfr₅⟩, hc₅⟩ := tourDetachLeftBody_runs (pos := st₄.pos)
            C.toTourSplayCoreProcs ω hn₄ hinv₄.ptrOk hq_cap
            ⟨hheap.rec_le, by have := hheap.room; omega, (hfr13.trans hfr₄).1, hheap.wide⟩
            (tourDetachLeft_sumOk hinv₄ hvals₄)
          obtain ⟨hinv₅, _, hval₅, hphi₅⟩ := tourDetachLeft_preserves hinv₄
          set s₅ := tourDetachLeft s₄ qid
          have hvals₅ : TourValsOk w cap s₅ := ⟨hvals₄.1, fun z hz => by rw [hval₅ z hz]; exact hvals₄.2 z hz⟩
          let L₄? : Option AuxTree := if L₄ = .leaf then none else some L₄
          have hL₄_root : o₅.value = optRoot L₄? := by
            simp only [hv₅, hsub₄.1, ↓reduceIte, hsub₄.2.1]; cases L₄ <;> simp [L₄?, optRoot, AuxTree.rootId]
          have hL₄_list : optList L₄? = f uid := by
            have h1 : optList L₄? = L₄.toList := by cases L₄ <;> simp [L₄?, optList, AuxTree.toList]
            rw [h1, hL₄_eq]; simp
          set tRem' := AuxTree.node qid .leaf R₄
          have hperm₅ : ((optTrees tB'? ++ optTrees tA?) ++ ((if L₄ = .leaf then [] else [L₄]) ++ [tRem']) ++ rest).Perm
              (optTrees tA? ++ optTrees L₄? ++ (optTrees tB'? ++ optTrees (some tRem') ++ rest)) := by
            have h1 : (if L₄ = .leaf then [] else [L₄]) = optTrees L₄? := by cases L₄ <;> simp [L₄?, optTrees]
            rw [h1]
            have hp1 : (optTrees tB'? ++ optTrees tA? ++ optTrees L₄?).Perm (optTrees tA? ++ optTrees L₄? ++ optTrees tB'?) := by
              simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tB'?) (l₂ := optTrees tA? ++ optTrees L₄?))
            simpa [optTrees, List.append_assoc] using hp1.append_right ([tRem'] ++ rest)
          have hinv₅' : TourForestInv cap s₅ (optTrees tA? ++ optTrees L₄? ++ (optTrees tB'? ++ optTrees (some tRem') ++ rest)) :=
            (hinv₅.perm hperm₅).1
          obtain ⟨tA'?, s₆, o₆, st₆, c₆, hrun₆, hv₆, hn₆, hfr₆, hinv₆, hvals₆, hlist₆, hval₆, _, hcost₆⟩ :=
            tourJoinBody_runs (pos := st₅.pos) C ω hn₅ hinv₅' hvals₅ hfuel hfuelW
              ⟨hheap.rec_le, hheap.room, (hfr13.trans (hfr₄.trans hfr₅)).1, hheap.wide⟩
          have hc4 := runs_call_regs4 13 0 12 5 10 (st := { st₃ with regs := r4 }) C.splay.splay_body
            (by simp [r4, r3, r2, r1, hr0]) (by simp [r4, r3, r2, r1, hr12, hwq])
            (by simp [r4, r3, r2, r1, hr5]) (by simp [r4, r3, r2, r1, hr10]) hrun₄
          set r5 := Function.update r4 13 o₄.value
          have hc5 := runs_call_regs3 13 0 12 10 (st := { st₄ with regs := r5 }) C.detachLeft_body
            (by simp [r5, r4, r3, r2, r1, hr0]) (by simp [r5, r4, r3, r2, r1, hr12, hwq])
            (by simp [r5, r4, r3, r2, r1, hr10]) hrun₅
          set r6 := Function.update r5 13 o₅.value
          have hc6 := runs_call_regs5 7 0 7 13 5 10 (st := { st₅ with regs := r6 }) C.join_body
            (by simp [r6, r5, r4, r3, r2, r1, hr0]) (by simp [r6, r5, r4, r3, r2, r1, hr7])
            (by simp [r6, hL₄_root]) (by simp [r6, r5, r4, r3, r2, r1, hr5])
            (by simp [r6, r5, r4, r3, r2, r1, hr10]) hrun₆
          set r7 := Function.update r6 7 o₆.value
          set r8 := Function.update r7 1 qid
          have ha2 : Runs w p ω (.assign 1 (.reg 12)) { st₆ with regs := r7 } .normal { st₆ with regs := r8 } 2 :=
            runs_assign_iff.mpr ⟨qid, by simp [Expr.eval, r7, r6, r5, r4, r3, r2, r1, hr12, hwq], rfl, rfl, rfl⟩
          refine ⟨tA'?, tB'?, some tRem', s₆, { st₆ with regs := r8 }, _,
            runs_seqAppend hpre_run (tour_runs_cond_false hcond
              (tour_runs_seq_normal hc4 (tour_runs_seq_normal hc5 (tour_runs_seq_normal hc6 ha2)))),
            fun k h1 h7 h8 h13 => by simp [r8, r7, r6, r5, r4, r3, r2, r1, h1, h7, h8, h13],
            by simp [r8, optRoot, tRem', AuxTree.rootId], by simp [r8, r7, hv₆],
            by simp [r8, r7, r6, r5, r4, r3, hv₃],
            hn₆, hfr13.trans (hfr₄.trans (hfr₅.trans hfr₆)),
            by simpa [List.append_assoc] using hinv₆, hvals₆,
            by rw [hlist₆, hL₄_list], by rw [hlist₃, hL₁_list],
            by simpa [optList, tRem', AuxTree.toList, List.flatMap_cons] using hR₄_eq,
            fun z hz => (hval₆ z hz).trans ((hval₅ z hz).trans ((hval₄ z hz).trans (hval13 z hz))), ?_⟩
          have hpeq5 := forestPhi_perm hperm₅
          have hphi5' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₅
          have hpeq_fin : forestPhi (optTrees tA'? ++ optTrees tB'? ++ optTrees (some tRem') ++ rest) =
              forestPhi (optTrees tA'? ++ (optTrees tB'? ++ optTrees (some tRem') ++ rest)) := by
            simp [List.append_assoc]
          have hpeq_mid : forestPhi ((optTrees tB'? ++ optTrees tA?) ++ tMid :: rest) =
              forestPhi (optTrees tB'? ++ (optTrees tA? ++ tMid :: rest)) := by
            simp [List.append_assoc]
          rw [hpeq_fin]; rw [← hpeq5] at hcost₆; rw [hpeq_mid] at hcost₄
          have hlog1 : 1 ≤ Nat.log 2 (cap + 2) + 1 := by omega
          clear * - hphi_pre hcost₄ hphi5' hcost₆ hc₅ hlog1
          simp only [Expr.size, TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT] at hphi_pre hcost₄ hphi5' hcost₆ hc₅ ⊢
          nlinarith

end MinCostFlow.SparseCore.Program
