module

public import MinCostFlow.SparseCore.Program.OrdStoreMoveFinish
import Mathlib.Tactic

/-!
# Order Store `moveEnds` Procedure

This file assembles Passes 1–7 (`OrdStoreMovePrep`, `OrdStoreMoveScan`, `OrdStoreMoveUnlink`,
`OrdStoreMoveFinish`) into `ordMoveEndsBody` on `[b, v, v', compWord, len, arrPtr, scratch]` and
proves `ordMoveEndsBody_runs` with amortized cost `ORD_MOVE_AMORT * ((len + 1) * ordStoreLog eCap)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState MinCostFlow.DynSpanner.Program

def ORD_MOVE_AMORT : ℕ := 30000

/-- `ordMoveEnds` on `[b, v, v', compWord, len, arrPtr, scratch]`: applies
`moveEnds v v' sel (compWord ≠ 0)` where `sel` is the set of `len` end keys at `arrPtr`, using
`2 * len` zero-initialized scratch words at `scratch` (restored to zero on return). -/
def ordMoveEndsBody (splayRootProc sortProc unlinkProc joinProc freeTreeProc : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 10 (.const 0) ;;
  .assign 11 (.const 0) ;;
  ordMoveMarkLoop ;;
  .assign 10 (.const 0) ;;
  ordMoveUnmarkLoop ;;
  .assign 10 (.const 0) ;;
  .assign 12 (.const 0) ;;
  (ordMovePosLoop splayRootProc ;;
   .call 17 sortProc [.reg 6, .reg 12]) ;;
  .assign 10 (.const 0) ;;
  .assign 13 (.const 0) ;;
  ordMoveUnlinkLoop unlinkProc ;;
  .assign 10 (.const 0) ;;
  ordMoveZeroLoop ;;
  ordMoveFinishBody joinProc freeTreeProc ;;
  .ret (.const 0)

theorem ordMoveEndsBody_noRand (srP sP uP jP ftP : ℕ) :
    (ordMoveEndsBody srP sP uP jP ftP).NoRand := by
  simp [ordMoveEndsBody, Stmt.NoRand, ordMoveMarkLoop_noRand, ordMoveUnmarkLoop_noRand,
    ordMovePosLoop_noRand, ordMoveUnlinkLoop_noRand, ordMoveZeroLoop_noRand, ordMoveFinishBody_noRand]

theorem ordMoveEndsBody_runs
    {w b v v' len arrPtr scratch pos rotProc stepProc splayProc splayRootProc
      siftProc sortProc walkProc joinProc unlinkProc freeTreeProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hsplayRoot : p.procs[splayRootProc]? = some (ordSplayRootBody splayProc))
    (hsift : p.procs[siftProc]? = some (ordSiftDownBody siftProc))
    (hsort : p.procs[sortProc]? = some (ordHeapSortBody siftProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (hunlink : p.procs[unlinkProc]? = some (ordUnlinkBody splayProc joinProc))
    (hfree : p.procs[freeTreeProc]? = some ordFreeTreeBody) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState} {comp : Bool}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem)
    (hv : v < S.vCap) (hv' : v' < S.vCap)
    (huniq' : OrdUniqueWithin S.vCap S.eCap
      (applyOrdEdit ord (.moveEnds v v' ((readList mem arrPtr len).map endOfKey).toFinset comp)))
    (harr_le : arrPtr + len ≤ scratch)
    (harr_disj : ∀ a, arrPtr ≤ a → a < arrPtr + len → ¬ ordFoot b S.vCap S.eCap a)
    (harr_w : ∀ j < len, mem (arrPtr + j) < 2 ^ w)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hz : ZeroFrom mem scratch) (hscr_w : scratch + 2 * len + 2 < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    let sel : Finset End := ((readList mem arrPtr len).map endOfKey).toFinset
    ∃ o st' c, Runs w p ω (ordMoveEndsBody splayRootProc sortProc unlinkProc joinProc freeTreeProc)
        (startState [b, v, v', if comp then 1 else 0, len, arrPtr, scratch] mem pos) o st' c ∧
      (∃ S' : OrdStoreState,
        OrdInv (applyOrdEdit ord (.moveEnds v v' sel comp)) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap scratch mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S +
            ORD_MOVE_AMORT * ((len + 1) * ordStoreLog S.eCap)) := by
  dsimp only
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  set sel : Finset End := ((readList mem arrPtr len).map endOfKey).toFinset with hsel_def
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  set en := ordENodeBase b S.vCap with hen
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  set st0 : State := startState [b, v, v', if comp then 1 else 0, len, arrPtr, scratch] mem pos
  -- Header setup (r7 = eCap, r8 = en, r9 = nb, r10 = 0, r11 = 0)
  have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 1)))) st0 .normal
      { st0 with regs := Function.update st0.regs 7 S.eCap } _ :=
    runs_assign_iff.mpr ⟨S.eCap, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st0, startState])) (Expr.eval_const (by omega)) (by omega))
      harena.hdr_eCap, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 7 S.eCap }
  have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 3)))) st1 .normal
      { st1 with regs := Function.update st1.regs 8 en } _ :=
    runs_assign_iff.mpr ⟨en, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st1, st0, startState])) (Expr.eval_const (by omega)) (by omega))
      harena.hdr_eNode, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 8 en }
  have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 4)))) st2 .normal
      { st2 with regs := Function.update st2.regs 9 nb } _ :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState])) (Expr.eval_const (by omega)) (by omega))
      harena.hdr_nodes, rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 9 nb }
  have ha10a : Runs w p ω (.assign 10 (.const 0)) st3 .normal
      { st3 with regs := Function.update st3.regs 10 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st4 : State := { st3 with regs := Function.update st3.regs 10 0 }
  have ha11a : Runs w p ω (.assign 11 (.const 0)) st4 .normal
      { st4 with regs := Function.update st4.regs 11 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st5 : State := { st4 with regs := Function.update st4.regs 11 0 }
  -- Pass 1: ordMoveMarkLoop
  obtain ⟨stP1, cP1, cand, hrunP1, hregP1, -, r11_P1, hcle, hnd_c, hlive_c, hiff_c, hscr_P1, -, hout_P1, hcP1⟩ :=
    ordMoveMarkLoop_runs (p := p) ω (st0 := st5) (mem0 := mem) hinv harena rfl
      harr_le (fun j hj => harr_disj (arrPtr + j) (by omega) (by omega)) harr_w hfoot (by omega) hwide
      (by simp [st5, st4, st3, st2, st1, st0, startState])
      (by simp [st5, st4, st3, st2, st1, st0, startState])
      (by simp [st5, st4, st3, st2, st1, st0, startState])
      (by simp [st5, st4, st3, st2, st1]) (by simp [st5, st4, st3, st2, hen])
      (by simp [st5, st4, st3, hnb]) (by simp [st5, st4]) (by simp [st5])
  have ha10b : Runs w p ω (.assign 10 (.const 0)) stP1 .normal
      { stP1 with regs := Function.update stP1.regs 10 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stP1' : State := { stP1 with regs := Function.update stP1.regs 10 0 }
  -- Pass 2: ordMoveUnmarkLoop
  obtain ⟨stP2, cP2, hrunP2, hregP2, harenaP2, hscr_P2, hout_P2, hcP2⟩ :=
    ordMoveUnmarkLoop_runs (p := p) ω (st0 := stP1') hinv harena hfoot (by omega) hwide hnd_c hlive_c hscr_P1 hout_P1
      (by simp [stP1', hregP1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), st5, st4, st3, st2, st1, st0, startState])
      (by simp [stP1', hregP1 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), st5, st4, st3, hnb])
      (by simp [stP1']) (by simp [stP1', r11_P1])
  have ha10c : Runs w p ω (.assign 10 (.const 0)) stP2 .normal
      { stP2 with regs := Function.update stP2.regs 10 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stP2a : State := { stP2 with regs := Function.update stP2.regs 10 0 }
  have ha12a : Runs w p ω (.assign 12 (.const 0)) stP2a .normal
      { stP2a with regs := Function.update stP2a.regs 12 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stP2' : State := { stP2a with regs := Function.update stP2a.regs 12 0 }
  have hstP2_regs : ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → stP2'.regs r = st5.regs r :=
    fun r h10 h11 h12 h13 h14 h15 => by
      simp only [stP2', stP2a, Function.update_of_ne h12, Function.update_of_ne h10]
      rw [hregP2 r h10 h13]; simp only [stP1', Function.update_of_ne h10]
      exact hregP1 r h10 h11 h12 h13 h14 h15
  have hzP2 : ZeroFrom stP2'.mem (scratch + 2 * cand.length) := fun a ha =>
    (hout_P2 a (fun i hi => by omega)).trans (hz a (by omega))
  -- Passes 3 & 4: ordMovePosLoop + ordHeapSort
  set selNodes : List ℕ := (S.trees v).toList.filter (fun u => decide (endOfKey (S.splay.nodes u).val ∈ sel))
  obtain ⟨stP4, cP4, S1, hrunP4, hregP4, r12_P4, hsel_le, hinv1, harena1, hv1, he1, hlist1, hval1, hcnt1,
    hscr_P4, hzP4, hfrP4, hphiP4⟩ :=
    ordMovePosSort_runs hrot hstep hsplay hsplayRoot hsift hsort ω (st0 := stP2') hinv harenaP2 hv hnd_c hcle hlive_c hiff_c
      hscr_P2 hzP2 hfoot hscr_w hwide
      (by rw [hstP2_regs 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP2_regs 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP2_regs 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP2_regs 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, hnb])
      (by simp [stP2', stP2a])
      (by simp only [stP2', stP2a, Function.update_of_ne (by decide : (11 : ℕ) ≠ 12), Function.update_of_ne (by decide : (11 : ℕ) ≠ 10)]
          rw [hregP2 11 (by decide) (by decide)]; simp [stP1', r11_P1])
      (by simp [stP2'])
  change selNodes.length ≤ cand.length at hsel_le
  have hselNodes_S1 : selNodes = (S1.trees v).toList.filter (fun u => decide (endOfKey (S1.splay.nodes u).val ∈ sel)) := by
    change (S.trees v).toList.filter _ = _
    rw [hlist1 v]
    exact List.filter_congr fun x hx => by rw [hval1 v hv x hx]
  have ha10d : Runs w p ω (.assign 10 (.const 0)) stP4 .normal
      { stP4 with regs := Function.update stP4.regs 10 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stP4a : State := { stP4 with regs := Function.update stP4.regs 10 0 }
  have ha13a : Runs w p ω (.assign 13 (.const 0)) stP4a .normal
      { stP4a with regs := Function.update stP4a.regs 13 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stP4' : State := { stP4a with regs := Function.update stP4a.regs 13 0 }
  have hstP4_regs : ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
      stP4'.regs r = st5.regs r := fun r h10 h11 h12 h13 h14 h15 h16 h17 => by
    simp only [stP4', stP4a, Function.update_of_ne h13, Function.update_of_ne h10]
    rw [hregP4 r h10 h12 h13 h14 h15 h16 h17]
    exact hstP2_regs r h10 h11 h12 h13 h14 h15
  -- Pass 5: ordMoveUnlinkLoop
  have hnd_sel : selNodes.Nodup := (hinv.tree_inv v hv).nodup.filter _
  have hsub_sel : ∀ u ∈ selNodes, u ∈ (S1.trees v).toList := fun u hu => by
    rw [hlist1 v]; exact (List.mem_filter.mp hu).1
  obtain ⟨stP5, cP5, sp5, tRem, hrunP5, hregP5, r13_P5, hnP5, hvrP5, hfrP5, hokR5, hppR5, hlistR5,
    hokS5, hppS5, houtS5, hvalS5, hphiP5⟩ :=
    ordMoveUnlinkLoop_runs hrot hstep hsplay hwalk hjoin hunlink ω (st0 := stP4') hinv1 harena1 (by rw [hv1]; exact hv)
      hnd_sel hsub_sel hscr_P4 (by rw [hv1, he1]; exact hfoot) (by have := hsel_le; have := hcle; omega) hwide
      (by rw [hstP4_regs 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP4_regs 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP4_regs 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, hv1, he1, hnb])
      (by simp [stP4', stP4a])
      (by simp only [stP4', stP4a, Function.update_of_ne (by decide : (12 : ℕ) ≠ 13), Function.update_of_ne (by decide : (12 : ℕ) ≠ 10)]; exact r12_P4)
      (by simp [stP4'])
  have ha10e : Runs w p ω (.assign 10 (.const 0)) stP5 .normal
      { stP5 with regs := Function.update stP5.regs 10 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stP5' : State := { stP5 with regs := Function.update stP5.regs 10 0 }
  have hnb1 : ordNodesBase b S1.vCap S1.eCap = nb := by rw [hv1, he1]
  have hnb1_end : ordNodesBase b S1.vCap S1.eCap + 8 * (S1.nextNode + 1) ≤ scratch := by
    have h1 := ordNodesBase_end b S1.vCap S1.eCap; have h2 := hinv1.next_le
    rw [hv1, he1] at h1 ⊢; rw [he1] at h2; omega
  have hnot_nd1 : ∀ a < nb, ¬ InOrdNodes (ordNodesBase b S1.vCap S1.eCap) S1.nextNode a := fun a ha h => by
    rw [hnb1] at h; unfold InOrdNodes at h; omega
  -- Pass 6: ordMoveZeroLoop
  have hzP5 : ZeroFrom stP5'.mem (scratch + 2 * cand.length) := fun a ha =>
    (hfrP5 a (fun h => by unfold InOrdNodes at h; omega) (by unfold ordVRootBase; omega)).trans (hzP4 a ha)
  have hr11_P5 : stP5'.regs 11 = cand.length := by
    simp only [stP5', Function.update_of_ne (by decide : (11 : ℕ) ≠ 10)]
    rw [hregP5 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [stP4', stP4a, Function.update_of_ne (by decide : (11 : ℕ) ≠ 13), Function.update_of_ne (by decide : (11 : ℕ) ≠ 10)]
    rw [hregP4 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [stP2', stP2a, Function.update_of_ne (by decide : (11 : ℕ) ≠ 12), Function.update_of_ne (by decide : (11 : ℕ) ≠ 10)]
    rw [hregP2 11 (by decide) (by decide)]; simp [stP1', r11_P1]
  obtain ⟨stP6, cP6, hrunP6, hregP6, hzP6, hltP6, hcP6⟩ :=
    ordMoveZeroLoop_runs (p := p) ω (st0 := stP5') hzP5 (by omega) hwide
      (by simp only [stP5', Function.update_of_ne (by decide : (6 : ℕ) ≠ 10)]
          rw [hregP5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
          rw [hstP4_regs 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [st5, st4, st3, st2, st1, st0, startState])
      (by simp [stP5']) hr11_P5
  have hstP6_lt_P5 : ∀ a < scratch, stP6.mem a = stP5.mem a := hltP6
  have hstP6_hdr : stP6.mem b = S1.vCap ∧ stP6.mem (b + 1) = S1.eCap ∧ stP6.mem (b + 2) = ordVRootBase b ∧
      stP6.mem (b + 3) = ordENodeBase b S1.vCap ∧ stP6.mem (b + 4) = ordNodesBase b S1.vCap S1.eCap ∧
      stP6.mem (b + 5) = S1.nextNode ∧ stP6.mem (b + 6) = S1.freeHead := by
    have hq : ∀ i ≤ 6, stP6.mem (b + i) = stP4.mem (b + i) := fun i hi =>
      (hstP6_lt_P5 (b + i) (by omega)).trans
        (hfrP5 (b + i) (hnot_nd1 _ (by rw [hnb]; unfold ordNodesBase; omega)) (by unfold ordVRootBase; omega))
    exact ⟨(hq 0 (by omega)).trans harena1.hdr_vCap, (hq 1 (by omega)).trans harena1.hdr_eCap,
      (hq 2 (by omega)).trans harena1.hdr_vRoot, (hq 3 (by omega)).trans harena1.hdr_eNode,
      (hq 4 (by omega)).trans harena1.hdr_nodes, (hq 5 (by omega)).trans harena1.hdr_next,
      (hq 6 (by omega)).trans harena1.hdr_free⟩
  have hstP6_vr : ∀ u < S1.vCap, stP6.mem (ordVRootBase b + u) = if u = v then tRem.rootId else S1.vRoot u := fun u hu => by
    rw [hstP6_lt_P5 (ordVRootBase b + u) (by rw [hv1] at hu; unfold ordVRootBase; omega)]
    by_cases huv : u = v
    · subst huv; simpa using hvrP5
    · simp only [huv, ite_false]
      rw [hfrP5 (ordVRootBase b + u) (hnot_nd1 _ (by rw [hv1] at hu; rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
        (by omega)]
      exact harena1.vRoot_at u hu
  have hstP6_en : ∀ k < 2 * S1.eCap, stP6.mem (ordENodeBase b S1.vCap + k) = S1.eNode k := fun k hk => by
    rw [hstP6_lt_P5 (ordENodeBase b S1.vCap + k) (by rw [he1] at hk; rw [hv1]; unfold ordENodeBase; omega),
      hfrP5 (ordENodeBase b S1.vCap + k) (hnot_nd1 _ (by rw [he1] at hk; rw [hv1, hnb]; unfold ordENodeBase ordNodesBase; omega))
        (by rw [hv1] at *; unfold ordVRootBase ordENodeBase; omega)]
    exact harena1.eNode_at k hk
  have hstP6_nodes : OrdNodesAt stP6.mem (ordNodesBase b S1.vCap S1.eCap) S1.nextNode sp5 S1.nextFree :=
    hnP5.congr fun a ha => hstP6_lt_P5 a (by unfold InOrdNodes at ha; omega)
  -- Pass 7: ordMoveFinishBody
  have hstP6_reg : ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
      stP6.regs r = st5.regs r := fun r h10 h11 h12 h13 h14 h15 h16 h17 => by
    rw [hregP6 r h10]; simp only [stP5', Function.update_of_ne h10]
    rw [hregP5 r h10 h13 h14 h15 h16]
    exact hstP4_regs r h10 h11 h12 h13 h14 h15 h16 h17
  obtain ⟨stP7, cP7, S', hrunP7, hinv', harena', hfrP7, hv', he', hphiP7⟩ :=
    ordMoveFinishBody_runs hrot hstep hsplay hwalk hjoin hfree ω (st0 := stP6)
      hinv1 (by rw [hv1]; exact hv) (by rw [hv1]; exact hv') (by rw [hv1, he1]; exact huniq')
      hselNodes_S1 hlistR5 hokR5 hppR5 hokS5 houtS5 hvalS5
      hstP6_hdr hstP6_vr hstP6_en hstP6_nodes hzP6 (by rw [hv1, he1]; exact hfoot) (by omega) hwide
      (by rw [hstP6_reg 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP6_reg 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP6_reg 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP6_reg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, st2, st1, st0, startState])
      (by rw [hstP6_reg 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st5, st4, st3, hv1, he1, hnb])
      (by rw [hregP6 13 (by decide)]; simp [stP5', r13_P5])
  have hret : Runs w p ω (.ret (.const 0)) stP7 (.returned 0) stP7 _ :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hfull : Runs w p ω (ordMoveEndsBody splayRootProc sortProc unlinkProc joinProc freeTreeProc) st0 (.returned 0) stP7 _ :=
    ord_runs_seq_normal ha7 (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha9
      (ord_runs_seq_normal ha10a (ord_runs_seq_normal ha11a (ord_runs_seq_normal hrunP1
        (ord_runs_seq_normal ha10b (ord_runs_seq_normal hrunP2 (ord_runs_seq_normal ha10c
          (ord_runs_seq_normal ha12a (ord_runs_seq_normal hrunP4 (ord_runs_seq_normal ha10d
            (ord_runs_seq_normal ha13a (ord_runs_seq_normal hrunP5 (ord_runs_seq_normal ha10e
              (ord_runs_seq_normal hrunP6 (ord_runs_seq_normal hrunP7 hret))))))))))))))))
  have hframe_all : OrdFrame b S.vCap S.eCap scratch mem stP7.mem := by
    refine ⟨hfrP7.1, fun a ha hnf => ?_⟩
    rw [hfrP7.2 a ha (by rw [hv1, he1]; exact hnf), hstP6_lt_P5 a ha]
    have hnot_nd_a : ¬ InOrdNodes (ordNodesBase b S1.vCap S1.eCap) S1.nextNode a := fun h => by
      have h1 := ordNodesBase_end b S.vCap S.eCap
      have h2 := hinv1.next_le; rw [he1] at h2
      unfold InOrdNodes at h; unfold ordFoot at hnf; rw [hv1, he1] at h
      unfold ordNodesBase at h h1; unfold ordArenaSize at hnf h1; omega
    have hnot_vrv : a ≠ ordVRootBase b + v := fun h => hnf (by subst h; unfold ordFoot ordVRootBase ordArenaSize; omega)
    rw [hfrP5 a hnot_nd_a hnot_vrv, hfrP4 a ha hnf, hout_P2 a (fun i _ => by omega)]
  refine ⟨.returned 0, stP7, _, hfull, S', hinv', harena', hframe_all, hv'.trans hv1, he'.trans he1, ?_⟩
  rw [he1] at hphiP5 hphiP7
  have hmul_sel : (ORD_UNLINK_AMORT + 120) * selNodes.length * ordStoreLog S.eCap ≤
      (ORD_UNLINK_AMORT + 120) * len * ordStoreLog S.eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hmul_1000 : (1000 * selNodes.length + ORD_JOIN_AMORT + 200) * ordStoreLog S.eCap ≤
      (1000 * len + ORD_JOIN_AMORT + 200) * ordStoreLog S.eCap :=
    Nat.mul_le_mul_right _ (by omega)
  have hlen_l : len ≤ len * ordStoreLog S.eCap := Nat.le_mul_of_pos_right len hlog
  have h1_l : 1 ≤ ordStoreLog S.eCap := hlog
  have hmul_rhs : ORD_MOVE_AMORT * ((len + 1) * ordStoreLog S.eCap) =
      ORD_MOVE_AMORT * (len * ordStoreLog S.eCap) + ORD_MOVE_AMORT * ordStoreLog S.eCap := by ring
  have hmul_p4 : 5500 * ((len + 1) * ordStoreLog S.eCap) =
      5500 * (len * ordStoreLog S.eCap) + 5500 * ordStoreLog S.eCap := by ring
  have hmul_p5 : (ORD_UNLINK_AMORT + 120) * len * ordStoreLog S.eCap =
      (ORD_UNLINK_AMORT + 120) * (len * ordStoreLog S.eCap) := by ring
  have hmul_p7 : (1000 * len + ORD_JOIN_AMORT + 200) * ordStoreLog S.eCap =
      1000 * (len * ordStoreLog S.eCap) + (ORD_JOIN_AMORT + 200) * ordStoreLog S.eCap := by ring
  unfold ORD_UNLINK_AMORT at hmul_p5 hmul_sel hphiP5
  unfold ORD_JOIN_AMORT at hmul_p7 hmul_1000 hphiP7
  unfold ORD_MOVE_AMORT at hmul_rhs ⊢
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
  omega

end MinCostFlow.SparseCore.Program
