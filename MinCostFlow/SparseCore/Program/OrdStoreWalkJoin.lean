module

public import MinCostFlow.SparseCore.Program.OrdStoreSplayRuns
import Mathlib.Tactic

/-!
# Order Store Walk-Extreme and Join Procedures

This file defines shared `Runs` combinators for order-store machine proofs and implements and
verifies two core zero-scratch auxiliary-tree procedures:

1. `ordWalkExtremeBody`: walks to the leftmost (`side = 0`) or rightmost (`side = 1`) node of a
   splay tree and splays it to the root.
2. `ordJoinBody`: joins two disjoint splay trees `t₁, t₂` into a single tree with inorder sequence
   `t₁.toList ++ t₂.toList` and root `ppar := owner`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-- Potential weight per unit of `treePhi` (chosen `≥ ORD_WALK_RATE = 750`). -/
def ORD_PHI_WEIGHT : ℕ := 1000
def ORD_WALK_RATE : ℕ := 750
def ORD_WALK_AMORT : ℕ := 4000
def ORD_JOIN_AMORT : ℕ := 5500

/-! ### Shared `Runs` combinators -/

theorem ord_runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω s st .normal st₁ c₁) (h₂ : Runs w p ω t st₁ o st₂ c₂) :
    Runs w p ω (.seq s t) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

theorem ord_runs_cond_true {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st st' : State} {o : Outcome} {v c₁ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0) (hr : Runs w p ω s st o st' c₁) :
    Runs w p ω (.cond e s t) st o st' (e.size + c₁ + 1) :=
  runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr, rfl⟩

theorem ord_runs_cond_false {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st st' : State} {o : Outcome} {c₁ : ℕ}
    (he : e.eval w st = some 0) (hr : Runs w p ω t st o st' c₁) :
    Runs w p ω (.cond e s t) st o st' (e.size + c₁ + 1) :=
  runs_cond_iff.mpr ⟨0, c₁, he, by simpa using hr, rfl⟩

theorem ord_runs_loop_false {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

theorem ord_runs_loop_true {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {v c₁ c₂ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h₁ : Runs w p ω body st .normal st₁ c₁) (h₂ : Runs w p ω (.loop e body) st₁ o st₂ c₂) :
    Runs w p ω (.loop e body) st o st₂ (e.size + c₁ + c₂ + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, h₁, h₂, rfl⟩))

/-! ### Extreme node helpers -/

/-- Extreme node ID of `t`: leftmost when `side = 0`, rightmost otherwise. -/
def extremeId (side : ℕ) (t : AuxTree) : ℕ :=
  if side = 0 then leftmostId t else rightmostId t

/-- Length of the left (`side = 0`) or right (`side ≠ 0`) spine of `t`. -/
def spineLen (side : ℕ) (t : AuxTree) : ℕ :=
  if side = 0 then leftSpineLen t else rightSpineLen t

theorem extremeId_mem {side : ℕ} {t : AuxTree} (ht : t ≠ .leaf) :
    extremeId side t ∈ t.toList := by
  unfold extremeId; split_ifs
  · exact leftmostId_mem ht
  · exact rightmostId_mem ht

theorem depthOf_extremeId {side : ℕ} {t : AuxTree} (hnd : t.toList.Nodup) (ht : t ≠ .leaf) :
    t.depthOf (extremeId side t) = spineLen side t := by
  unfold extremeId spineLen; split_ifs
  · exact depthOf_leftmostId hnd ht
  · exact depthOf_rightmostId hnd ht

theorem ordStoreLog_pos (n : ℕ) : 1 ≤ ordStoreLog n := by
  unfold ordStoreLog; omega

theorem erase_append_singleton_append {α : Type*} [DecidableEq α] {l r : List α} {x : α}
    (hnd : (l ++ [x] ++ r).Nodup) :
    (l ++ [x] ++ r).erase x = l ++ r := by
  induction l with
  | nil =>
    change (x :: r).erase x = r
    rw [List.erase_cons_head]
  | cons a tl ih =>
    rw [List.cons_append, List.cons_append] at hnd ⊢
    rcases List.nodup_cons.mp hnd with ⟨ha, htl⟩
    have hax : a ≠ x := fun h => ha (by rw [h]; simp)
    rw [List.erase_cons, beq_eq_false_iff_ne.mpr hax]
    exact congrArg (a :: ·) (ih htl)

/-! ### `ordWalkExtremeBody` -/

/-- `ordWalkExtreme` on `[nb, x, side]`: walks down `left` (`side = 0`) or `right` (`side = 1`)
from `x` to the extreme node `w`, calls `splayProc [nb, w]`, and returns `w`. -/
def ordWalkExtremeBody (splayProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (.reg 1) ;;
     .assign 4 (.load (.bin .add (ordRec 3) (.reg 2))) ;;
     .loop (.reg 4)
       (.assign 3 (.reg 4) ;;
        .assign 4 (.load (.bin .add (ordRec 3) (.reg 2)))) ;;
     .call 5 splayProc [.reg 0, .reg 3] ;;
     .ret (.reg 3))

theorem ordWalkExtremeBody_noRand (splayProc : ℕ) : (ordWalkExtremeBody splayProc).NoRand := by
  simp [ordWalkExtremeBody, ordRec, Stmt.NoRand]

theorem ordWalkExtremeBody_runs {w nb cap eCap x side pos rotProc stepProc splayProc : ℕ}
    {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState ℕ Unit Unit} {nf : ℕ → ℕ} {t : AuxTree}
    (hnodes : OrdNodesAt mem nb cap st nf) (hok : OrdTreeOk cap st t)
    (ht : t ≠ .leaf) (hx : x = t.rootId) (hside : side = 0 ∨ side = 1)
    (hcap : cap ≤ 2 * eCap) (hw : nb + 8 * (cap + 1) < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordWalkExtremeBody splayProc) (startState [nb, x, side] mem pos) o st' c ∧
      (∃ t' : AuxTree,
        let sp' := SplayState.splayLoop ordPayload st t.countNodes (extremeId side t)
        o.value = extremeId side t ∧
        OrdNodesAt st'.mem nb cap sp' nf ∧
        (∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
        OrdTreeOk cap sp' t' ∧
        t' ≠ .leaf ∧
        t'.rootId = extremeId side t ∧
        t'.toList = t.toList ∧
        t'.countNodes = t.countNodes ∧
        (∀ u ∈ t.toList, (sp'.nodes u).val = (st.nodes u).val) ∧
        (sp'.nodes (extremeId side t)).ppar = (st.nodes t.rootId).ppar ∧
        (∀ u ∉ t.toList, sp'.nodes u = st.nodes u) ∧
        c + ORD_PHI_WEIGHT * t'.treePhi (fun _ => 0) ≤
          ORD_PHI_WEIGHT * t.treePhi (fun _ => 0) + ORD_WALK_AMORT * ordStoreLog eCap) := by
  have hx_mem : x ∈ t.toList := hx ▸ AuxTree.rootId_mem ht
  have hx0 : x ≠ 0 := SplayState.SubtreeInv_nonZero hok.inv.sub hx_mem
  have hxc : x ≤ cap := (hok.ptrs_le hx_mem).1
  -- Read-only walk loop induction on any non-leaf subtree
  have hwalk : ∀ (sub : AuxTree) (par0 : ℕ) (stM : State),
      sub ≠ .leaf →
      SplayState.SubtreeInv ordPayload st par0 sub →
      (∀ u ∈ sub.toList, u ≤ cap) →
      stM.mem = mem →
      stM.regs 0 = nb → stM.regs 2 = side → stM.regs 3 = sub.rootId →
      stM.regs 4 = (if side = 0 then (st.nodes sub.rootId).left else (st.nodes sub.rootId).right) →
      ∃ stE cE, Runs w p ω
          (.loop (.reg 4)
            (.assign 3 (.reg 4) ;;
             .assign 4 (.load (.bin .add (ordRec 3) (.reg 2))))) stM .normal stE cE ∧
        stE.mem = mem ∧ stE.regs 0 = nb ∧ stE.regs 3 = extremeId side sub ∧
        cE ≤ spineLen side sub * 25 + 5 := by
    intro sub
    induction sub with
    | leaf => intro _ _ h; exact absurd rfl h
    | node id l r ihl ihr =>
      intro par0 stM _ hsub hle hmem r0 r2 r3 r4
      rcases hsub with ⟨hid0, hleft, hright, -, -, -, -, hsubL, hsubR⟩
      rcases hside with rfl | rfl
      · simp only [↓reduceIte, AuxTree.rootId] at r3 r4
        rw [hleft] at r4
        cases l with
        | leaf =>
          simp only [AuxTree.rootId] at r4
          refine ⟨stM, _, ord_runs_loop_false (Expr.eval_reg_of_eq r4), hmem, r0, ?_, ?_⟩
          · simp [extremeId, leftmostId, r3]
          · simp [spineLen, leftSpineLen, Expr.size_reg]
        | node lid ll lr =>
          have hlid_ne : AuxTree.node lid ll lr ≠ .leaf := by simp
          have hlid0 : lid ≠ 0 := SplayState.SubtreeInv_nonZero hsubL (AuxTree.rootId_mem hlid_ne)
          have hlid_le : lid ≤ cap := hle lid (by simp [AuxTree.toList])
          have hm_lid : mem (nb + 8 * lid + 0) = (st.nodes lid).left := by
            simpa [ordNodeAddr] using (hnodes lid hlid_le).1
          simp only [AuxTree.rootId] at r4
          have hstep1 : Runs w p ω (.assign 3 (.reg 4)) stM .normal
              { stM with regs := Function.update stM.regs 3 lid } ((Expr.reg 4).size + 1) :=
            runs_assign_iff.mpr ⟨lid, Expr.eval_reg_of_eq r4, rfl, rfl, rfl⟩
          have heval2 : (Expr.load (.bin .add (ordRec 3) (.reg 2))).eval w
              { stM with regs := Function.update stM.regs 3 lid } = some (st.nodes lid).left := by
            refine Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
              (Expr.eval_reg_of_eq (v := nb) (by simp [r0]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := lid) (by simp)) (by omega))
              (by omega)) (Expr.eval_reg_of_eq (v := 0) (by simp [r2])) (by omega)) (by rw [hmem]; exact hm_lid)
          set stN : State := { stM with regs := Function.update (Function.update stM.regs 3 lid) 4 (st.nodes lid).left }
          have hstep2 : Runs w p ω (.assign 4 (.load (.bin .add (ordRec 3) (.reg 2))))
              { stM with regs := Function.update stM.regs 3 lid } .normal stN
              ((Expr.load (.bin .add (ordRec 3) (.reg 2))).size + 1) :=
            runs_assign_iff.mpr ⟨(st.nodes lid).left, heval2, rfl, rfl, rfl⟩
          have hbody := ord_runs_seq_normal hstep1 hstep2
          obtain ⟨stE, cE, hrest, hmemE, r0E, r3E, hcE⟩ :=
            ihl id stN hlid_ne hsubL
              (fun u hu => hle u (List.mem_append_left _ (List.mem_append_left _ hu)))
              hmem (by simp [stN, r0]) (by simp [stN, r2]) (by simp [stN, AuxTree.rootId]) (by simp [stN, AuxTree.rootId])
          refine ⟨stE, _, ord_runs_loop_true (Expr.eval_reg_of_eq r4) hlid0 hbody hrest,
            hmemE, r0E, by simpa [extremeId, leftmostId] using r3E, ?_⟩
          simp only [spineLen, leftSpineLen, ↓reduceIte] at hcE ⊢
          simp only [ordRec, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
          omega
      · simp only [Nat.one_ne_zero, ↓reduceIte, AuxTree.rootId] at r3 r4
        rw [hright] at r4
        cases r with
        | leaf =>
          simp only [AuxTree.rootId] at r4
          refine ⟨stM, _, ord_runs_loop_false (Expr.eval_reg_of_eq r4), hmem, r0, ?_, ?_⟩
          · simp [extremeId, rightmostId, r3]
          · simp [spineLen, rightSpineLen, Expr.size_reg]
        | node rid rl rr =>
          have hrid_ne : AuxTree.node rid rl rr ≠ .leaf := by simp
          have hrid0 : rid ≠ 0 := SplayState.SubtreeInv_nonZero hsubR (AuxTree.rootId_mem hrid_ne)
          have hrid_le : rid ≤ cap := hle rid (by simp [AuxTree.toList])
          have hm_rid : mem (nb + 8 * rid + 1) = (st.nodes rid).right := (hnodes rid hrid_le).2.1
          simp only [AuxTree.rootId] at r4
          have hstep1 : Runs w p ω (.assign 3 (.reg 4)) stM .normal
              { stM with regs := Function.update stM.regs 3 rid } ((Expr.reg 4).size + 1) :=
            runs_assign_iff.mpr ⟨rid, Expr.eval_reg_of_eq r4, rfl, rfl, rfl⟩
          have heval2 : (Expr.load (.bin .add (ordRec 3) (.reg 2))).eval w
              { stM with regs := Function.update stM.regs 3 rid } = some (st.nodes rid).right := by
            refine Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
              (Expr.eval_reg_of_eq (v := nb) (by simp [r0]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := rid) (by simp)) (by omega))
              (by omega)) (Expr.eval_reg_of_eq (v := 1) (by simp [r2])) (by omega)) (by rw [hmem]; exact hm_rid)
          set stN : State := { stM with regs := Function.update (Function.update stM.regs 3 rid) 4 (st.nodes rid).right }
          have hstep2 : Runs w p ω (.assign 4 (.load (.bin .add (ordRec 3) (.reg 2))))
              { stM with regs := Function.update stM.regs 3 rid } .normal stN
              ((Expr.load (.bin .add (ordRec 3) (.reg 2))).size + 1) :=
            runs_assign_iff.mpr ⟨(st.nodes rid).right, heval2, rfl, rfl, rfl⟩
          have hbody := ord_runs_seq_normal hstep1 hstep2
          obtain ⟨stE, cE, hrest, hmemE, r0E, r3E, hcE⟩ :=
            ihr id stN hrid_ne hsubR
              (fun u hu => hle u (List.mem_append_right _ hu))
              hmem (by simp [stN, r0]) (by simp [stN, r2]) (by simp [stN, AuxTree.rootId]) (by simp [stN, AuxTree.rootId])
          refine ⟨stE, _, ord_runs_loop_true (Expr.eval_reg_of_eq r4) hrid0 hbody hrest,
            hmemE, r0E, by simpa [extremeId, rightmostId] using r3E, ?_⟩
          simp only [spineLen, rightSpineLen, Nat.one_ne_zero, ↓reduceIte] at hcE ⊢
          simp only [ordRec, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
          omega
  -- Run the full procedure
  set wnd := extremeId side t with hwnd
  have hw_mem : wnd ∈ t.toList := extremeId_mem ht
  have hw_dep : t.depthOf wnd = spineLen side t := depthOf_extremeId hok.inv.nodup ht
  have hfuel : t.depthOf wnd < t.countNodes := depthOf_lt_countNodes hw_mem
  obtain ⟨t', ht'_inv, ht'_ne, ht'_root, ht'_list, hclean', hval', hpp', hout', hcnt', hphi'⟩ :=
    ord_splay_spec hok.inv hok.clean hw_mem hfuel
  set sp' := SplayState.splayLoop ordPayload st t.countNodes wnd
  have h0_nmem : 0 ∉ t.toList := fun h0 => SplayState.SubtreeInv_nonZero hok.inv.sub h0 rfl
  have hok' : OrdTreeOk cap sp' t' :=
    { null_node := (hout' 0 h0_nmem).trans hok.null_node
      clean := hclean'
      inv := ht'_inv
      mem_le := fun u hu => hok.mem_le u (ht'_list ▸ hu)
      count_le := hcnt' ▸ hok.count_le }
  have hrk' : t'.rank (fun _ => 0) ≤ ordStoreLog eCap :=
    rank_zero_le_ordStoreLog (by have := hok'.count_le; omega)
  have hm_x : mem (nb + 8 * x + side) =
      (if side = 0 then (st.nodes x).left else (st.nodes x).right) := by
    rcases hside with rfl | rfl
    · simpa [ordNodeAddr] using (hnodes x hxc).1
    · simpa [ordNodeAddr] using (hnodes x hxc).2.1
  set st0 : State := startState [nb, x, side] mem pos
  have hst0_eq : Runs w p ω (.assign 3 (.reg 1)) st0 .normal
      { st0 with regs := Function.update st0.regs 3 x } ((Expr.reg 1).size + 1) :=
    runs_assign_iff.mpr ⟨x, Expr.eval_reg_of_eq (by simp [st0, startState]), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 3 x }
  have heval_ld : (Expr.load (.bin .add (ordRec 3) (.reg 2))).eval w st1 =
      some (if side = 0 then (st.nodes x).left else (st.nodes x).right) := by
    refine Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq (v := nb) (by simp [st1, st0, startState]))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := x) (by simp [st1])) (by omega))
      (by omega)) (Expr.eval_reg_of_eq (v := side) (by simp [st1, st0, startState])) (by rcases hside with rfl | rfl <;> omega))
      hm_x
  set v4 := if side = 0 then (st.nodes x).left else (st.nodes x).right
  set st2 : State := { st1 with regs := Function.update st1.regs 4 v4 }
  have hst1_eq : Runs w p ω (.assign 4 (.load (.bin .add (ordRec 3) (.reg 2)))) st1 .normal st2
      ((Expr.load (.bin .add (ordRec 3) (.reg 2))).size + 1) :=
    runs_assign_iff.mpr ⟨_, heval_ld, rfl, rfl, rfl⟩
  obtain ⟨stE, cE, hrunL, hmemE, r0E, r3E, hcE⟩ :=
    hwalk t 0 st2 ht hok.inv.sub hok.mem_le rfl
      (by simp [st2, st1, st0, startState]) (by simp [st2, st1, st0, startState])
      (by simp [st2, st1, hx]) (by simp [st2, v4, hx])
  obtain ⟨oS, stS, cS, hrunS, ⟨hnS, hfrS⟩, hcS⟩ :=
    ordSplayBody_runs hrot hstep ω (hmemE.symm ▸ hnodes) hok hw_mem hw hwide (pos := stE.pos)
  have hcall : Runs w p ω (.call 5 splayProc [.reg 0, .reg 3]) stE .normal
      { stS with regs := Function.update stE.regs 5 oS.value }
      (argsSize [.reg 0, .reg 3] + cS + 1) :=
    runs_call_iff.mpr ⟨[nb, wnd], ordSplayBody stepProc, oS, stS, cS,
      evalArgs_cons (Expr.eval_reg_of_eq r0E) (evalArgs_cons (Expr.eval_reg_of_eq r3E) (evalArgs_nil _ _)),
      hsplay, hrunS, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 3)) { stS with regs := Function.update stE.regs 5 oS.value }
      (.returned wnd) { stS with regs := Function.update stE.regs 5 oS.value } ((Expr.reg 3).size + 1) :=
    runs_ret_iff.mpr ⟨wnd, Expr.eval_reg_of_eq (by simp [r3E, hwnd]), rfl, rfl, rfl⟩
  have hcond_f : (Expr.bin .eq (.reg 1) (.const 0)).eval w st0 = some 0 :=
    Expr.eval_eq_false (Expr.eval_reg_of_eq (by simp [st0, startState])) (Expr.eval_const (by omega)) hx0 (by omega)
  have hbody := ord_runs_seq_normal hst0_eq (ord_runs_seq_normal hst1_eq
    (ord_runs_seq_normal hrunL (ord_runs_seq_normal hcall hret)))
  unfold ordWalkExtremeBody
  refine ⟨.returned wnd, _, _, ord_runs_cond_false hcond_f hbody, t', rfl, hnS,
    fun a ha => (hfrS a ha).trans (congrFun hmemE a),
    hok', ht'_ne, ht'_root, ht'_list, hcnt', hval', hpp', hout', ?_⟩
  have hlog : 1 ≤ ordStoreLog eCap := ordStoreLog_pos eCap
  have hsp_le : spineLen side t ≤ 2 * (t.depthOf wnd / 2) + 1 := by omega
  have hcost_walk : cE ≤ 50 * (t.depthOf wnd / 2) + 30 := by
    have := Nat.mul_le_mul_right 25 hsp_le; omega
  have hsz_e : (Expr.bin .eq (.reg 1) (.const 0)).size + (Expr.reg 1).size +
      (Expr.load (.bin .add (ordRec 3) (.reg 2))).size + argsSize [.reg 0, .reg 3] +
      (Expr.reg 3).size ≤ 30 := by
    simp [ordRec, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil]
  have htot_c : ((Expr.bin .eq (.reg 1) (.const 0)).size +
      (((Expr.reg 1).size + 1) + (((Expr.load (.bin .add (ordRec 3) (.reg 2))).size + 1) +
        (cE + ((argsSize [.reg 0, .reg 3] + cS + 1) + ((Expr.reg 3).size + 1) + 1) + 1) + 1) + 1) + 1) ≤
      (t.depthOf wnd / 2) * 700 + 800 := by
    unfold ORD_SPLAY_RATE at hcS
    omega
  have hphi_mul : ORD_PHI_WEIGHT * t'.treePhi (fun _ => 0) + ORD_PHI_WEIGHT * (t.depthOf wnd / 2) ≤
      ORD_PHI_WEIGHT * t.treePhi (fun _ => 0) + 3 * ORD_PHI_WEIGHT * ordStoreLog eCap := by
    have h1 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi'
    have h2 : ORD_PHI_WEIGHT * (t'.treePhi (fun _ => 0) + t.depthOf wnd / 2) =
        ORD_PHI_WEIGHT * t'.treePhi (fun _ => 0) + ORD_PHI_WEIGHT * (t.depthOf wnd / 2) := by ring
    have h3 : ORD_PHI_WEIGHT * (t.treePhi (fun _ => 0) + 3 * t'.rank (fun _ => 0)) =
        ORD_PHI_WEIGHT * t.treePhi (fun _ => 0) + 3 * ORD_PHI_WEIGHT * t'.rank (fun _ => 0) := by ring
    have h4 := Nat.mul_le_mul_left (3 * ORD_PHI_WEIGHT) hrk'
    omega
  unfold ORD_PHI_WEIGHT at hphi_mul ⊢; unfold ORD_WALK_AMORT
  have h700 : (t.depthOf wnd / 2) * 700 ≤ 1000 * (t.depthOf wnd / 2) := by omega
  omega

/-! ### `ordJoinBody` -/

/-- `ordJoin` on `[nb, r1, r2, owner]`: joins two disjoint auxiliary trees rooted at `r1` and `r2`
(either of which may be `0`), sets the resulting root's `ppar := owner`, and returns the new root. -/
def ordJoinBody (walkProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.cond (.reg 2)
      (.store (.bin .add (ordRec 2) (.const 3)) (.reg 3)) .nop ;;
     .ret (.reg 2))
    (.cond (.bin .eq (.reg 2) (.const 0))
      (.store (.bin .add (ordRec 1) (.const 3)) (.reg 3) ;;
       .ret (.reg 1))
      (.call 4 walkProc [.reg 0, .reg 1, .const 1] ;;
       .assign 5 (ordRec 4) ;;
       .assign 6 (ordRec 2) ;;
       .store (.bin .add (.reg 5) (.const 1)) (.reg 2) ;;
       .store (.bin .add (.reg 6) (.const 2)) (.reg 4) ;;
       .store (.bin .add (.reg 6) (.const 3)) (.const 0) ;;
       .store (.bin .add (.reg 5) (.const 3)) (.reg 3) ;;
       .assign 7 (.load (.bin .add (.reg 5) (.const 4))) ;;
       .assign 8 (.load (.bin .add (.reg 6) (.const 4))) ;;
       .store (.bin .add (.reg 5) (.const 4)) (.bin .add (.reg 7) (.reg 8)) ;;
       .ret (.reg 4)))

theorem ordJoinBody_noRand (walkProc : ℕ) : (ordJoinBody walkProc).NoRand := by
  simp [ordJoinBody, ordRec, Stmt.NoRand]

private theorem subtreeInv_setPpar_root {st : SplayState ℕ Unit Unit} {t : AuxTree} {owner : ℕ}
    (ht : TreeInv ordPayload st t) (hne : t ≠ .leaf) :
    SplayState.SubtreeInv ordPayload (st.setPpar t.rootId owner) 0 t := by
  cases t with
  | leaf => exact absurd rfl hne
  | node rid rl rr =>
    simp only [AuxTree.rootId]
    rcases ht.sub with ⟨h1, h2, h3, h4, _, h6, h7, hL, hR⟩
    rcases AuxTree.nodup_node_unfold ht.nodup with ⟨-, hnl, -, hnr, -⟩
    refine ⟨h1, by simp [SplayState.setPpar, SplayState.nodes_updateNode, h2],
      by simp [SplayState.setPpar, SplayState.nodes_updateNode, h3],
      by simp [SplayState.setPpar, SplayState.nodes_updateNode, h4], fun h => absurd rfl h,
      by simp [SplayState.setPpar, SplayState.nodes_updateNode, h6],
      by simp [SplayState.setPpar, SplayState.nodes_updateNode, h7],
      SplayState.SubtreeInv_agree hL fun u hu => by
        have hne : u ≠ rid := fun h => hnl (h ▸ hu)
        simp [SplayState.setPpar, SplayState.nodes_updateNode, hne],
      SplayState.SubtreeInv_agree hR fun u hu => by
        have hne : u ≠ rid := fun h => hnr (h ▸ hu)
        simp [SplayState.setPpar, SplayState.nodes_updateNode, hne]⟩

theorem ordJoinBody_runs {w nb cap eCap r1 r2 owner pos rotProc stepProc splayProc walkProc : ℕ}
    {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState ℕ Unit Unit} {nf : ℕ → ℕ} {t1 t2 : AuxTree}
    (hnodes : OrdNodesAt mem nb cap st nf)
    (hok1 : OrdTreeOk cap st t1) (hok2 : OrdTreeOk cap st t2)
    (hr1 : r1 = t1.rootId) (hr2 : r2 = t2.rootId)
    (hdisj : ∀ u ∈ t1.toList, u ∉ t2.toList)
    (hsum : t1.countNodes + t2.countNodes ≤ cap) (hcap : cap ≤ 2 * eCap)
    (hown_w : owner < 2 ^ w) (hw : nb + 8 * (cap + 1) < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordJoinBody walkProc) (startState [nb, r1, r2, owner] mem pos) o st' c ∧
      (∃ (sp' : SplayState ℕ Unit Unit) (t' : AuxTree),
        o.value = t'.rootId ∧
        OrdNodesAt st'.mem nb cap sp' nf ∧
        (∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
        OrdTreeOk cap sp' t' ∧
        t'.toList = t1.toList ++ t2.toList ∧
        t'.countNodes = t1.countNodes + t2.countNodes ∧
        (t' ≠ .leaf → (sp'.nodes t'.rootId).ppar = owner) ∧
        (∀ u ∈ t'.toList, (sp'.nodes u).val = (st.nodes u).val) ∧
        (∀ u, u ∉ t1.toList → u ∉ t2.toList → sp'.nodes u = st.nodes u) ∧
        c + ORD_PHI_WEIGHT * t'.treePhi (fun _ => 0) ≤
          ORD_PHI_WEIGHT * (t1.treePhi (fun _ => 0) + t2.treePhi (fun _ => 0)) +
            ORD_JOIN_AMORT * ordStoreLog eCap) := by
  have hlog : 1 ≤ ordStoreLog eCap := ordStoreLog_pos eCap
  set st0 : State := startState [nb, r1, r2, owner] mem pos
  unfold ordJoinBody
  by_cases ht1 : t1 = .leaf
  · subst ht1
    simp only [AuxTree.rootId] at hr1
    have hcond1 : (Expr.bin .eq (.reg 1) (.const 0)).eval w st0 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (by simp [st0, startState, hr1])) (Expr.eval_const (by omega)) rfl (by omega)
    by_cases ht2 : t2 = .leaf
    · subst ht2
      simp only [AuxTree.rootId] at hr2
      have hcond2 : (Expr.reg 2).eval w st0 = some 0 := Expr.eval_reg_of_eq (by simp [st0, startState, hr2])
      have hnop : Runs w p ω (.cond (.reg 2) (.store (.bin .add (ordRec 2) (.const 3)) (.reg 3)) .nop)
          st0 .normal st0 _ :=
        ord_runs_cond_false hcond2 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)
      have hret : Runs w p ω (.ret (.reg 2)) st0 (.returned 0) st0 _ :=
        runs_ret_iff.mpr ⟨0, Expr.eval_reg_of_eq (by simp [st0, startState, hr2]), rfl, rfl, rfl⟩
      refine ⟨.returned 0, _, _, ord_runs_cond_true hcond1 Nat.one_ne_zero (ord_runs_seq_normal hnop hret),
        st, .leaf, rfl, hnodes, fun _ _ => rfl, hok2,
        rfl, rfl, fun h => absurd rfl h, fun _ _ => rfl, fun _ _ _ => rfl, ?_⟩
      unfold ORD_PHI_WEIGHT ORD_JOIN_AMORT
      simp [AuxTree.treePhi, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · have hr2_nz : r2 ≠ 0 := hr2 ▸ SplayState.SubtreeInv_nonZero hok2.inv.sub (AuxTree.rootId_mem ht2)
      have hr2_c : r2 ≤ cap := hok2.mem_le r2 (hr2 ▸ AuxTree.rootId_mem ht2)
      have hcond2 : (Expr.reg 2).eval w st0 = some r2 := Expr.eval_reg_of_eq (by simp [st0, startState])
      have hst_pp : Runs w p ω (.store (.bin .add (ordRec 2) (.const 3)) (.reg 3)) st0 .normal
          { st0 with mem := Function.update mem (nb + 8 * r2 + 3) owner } _ :=
        runs_store_iff.mpr ⟨nb + 8 * r2 + 3, owner,
          Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st0, startState])) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega),
          Expr.eval_reg_of_eq (by simp [st0, startState]), rfl, rfl, rfl⟩
      have hcond_run : Runs w p ω (.cond (.reg 2) (.store (.bin .add (ordRec 2) (.const 3)) (.reg 3)) .nop)
          st0 .normal { st0 with mem := Function.update mem (nb + 8 * r2 + 3) owner } _ :=
        ord_runs_cond_true hcond2 hr2_nz hst_pp
      have hret : Runs w p ω (.ret (.reg 2))
          { st0 with mem := Function.update mem (nb + 8 * r2 + 3) owner } (.returned r2) _ _ :=
        runs_ret_iff.mpr ⟨r2, Expr.eval_reg_of_eq (by simp [st0, startState]), rfl, rfl, rfl⟩
      have hok2' : OrdTreeOk cap (st.setPpar r2 owner) t2 :=
        { null_node := by rw [SplayState.setPpar, SplayState.nodes_updateNode_ne _ (Ne.symm hr2_nz)]; exact hok2.null_node
          clean := fun u => by
            by_cases h : u = r2
            · subst h; simp [SplayState.setPpar, SplayState.nodes_updateNode, hok2.clean]
            · simp [SplayState.setPpar, SplayState.nodes_updateNode, h, hok2.clean u]
          inv := ⟨hok2.inv.nodup, hr2 ▸ subtreeInv_setPpar_root hok2.inv ht2⟩
          mem_le := hok2.mem_le
          count_le := hok2.count_le }
      refine ⟨.returned r2, _, _, ord_runs_cond_true hcond1 Nat.one_ne_zero (ord_runs_seq_normal hcond_run hret),
        st.setPpar r2 owner, t2, hr2, hnodes.setPpar hr2_c,
        fun a ha => Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩) _ _,
        hok2', by simp [AuxTree.toList], by simp [AuxTree.countNodes],
        fun _ => by rw [← hr2]; simp [SplayState.setPpar, SplayState.nodes_updateNode],
        fun u _ => by by_cases h : u = r2 <;> simp [SplayState.setPpar, SplayState.nodes_updateNode, h],
        fun u _ hu2 => by
          have hne : u ≠ r2 := fun h => hu2 (h ▸ hr2 ▸ AuxTree.rootId_mem ht2)
          simp [SplayState.setPpar, SplayState.nodes_updateNode, hne], ?_⟩
      unfold ORD_PHI_WEIGHT ORD_JOIN_AMORT
      simp [ordRec, AuxTree.treePhi, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
  · have hr1_nz : r1 ≠ 0 := hr1 ▸ SplayState.SubtreeInv_nonZero hok1.inv.sub (AuxTree.rootId_mem ht1)
    have hr1_c : r1 ≤ cap := hok1.mem_le r1 (hr1 ▸ AuxTree.rootId_mem ht1)
    have hcond1 : (Expr.bin .eq (.reg 1) (.const 0)).eval w st0 = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (by simp [st0, startState])) (Expr.eval_const (by omega)) hr1_nz (by omega)
    by_cases ht2 : t2 = .leaf
    · subst ht2
      simp only [AuxTree.rootId] at hr2
      have hcond2 : (Expr.bin .eq (.reg 2) (.const 0)).eval w st0 = some 1 :=
        Expr.eval_eq_true (Expr.eval_reg_of_eq (by simp [st0, startState, hr2])) (Expr.eval_const (by omega)) rfl (by omega)
      have hst_pp : Runs w p ω (.store (.bin .add (ordRec 1) (.const 3)) (.reg 3)) st0 .normal
          { st0 with mem := Function.update mem (nb + 8 * r1 + 3) owner } _ :=
        runs_store_iff.mpr ⟨nb + 8 * r1 + 3, owner,
          Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st0, startState])) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega),
          Expr.eval_reg_of_eq (by simp [st0, startState]), rfl, rfl, rfl⟩
      have hret : Runs w p ω (.ret (.reg 1))
          { st0 with mem := Function.update mem (nb + 8 * r1 + 3) owner } (.returned r1) _ _ :=
        runs_ret_iff.mpr ⟨r1, Expr.eval_reg_of_eq (by simp [st0, startState]), rfl, rfl, rfl⟩
      have hok1' : OrdTreeOk cap (st.setPpar r1 owner) t1 :=
        { null_node := by rw [SplayState.setPpar, SplayState.nodes_updateNode_ne _ (Ne.symm hr1_nz)]; exact hok1.null_node
          clean := fun u => by
            by_cases h : u = r1
            · subst h; simp [SplayState.setPpar, SplayState.nodes_updateNode, hok1.clean]
            · simp [SplayState.setPpar, SplayState.nodes_updateNode, h, hok1.clean u]
          inv := ⟨hok1.inv.nodup, hr1 ▸ subtreeInv_setPpar_root hok1.inv ht1⟩
          mem_le := hok1.mem_le
          count_le := hok1.count_le }
      refine ⟨.returned r1, _, _,
        ord_runs_cond_false hcond1 (ord_runs_cond_true hcond2 Nat.one_ne_zero (ord_runs_seq_normal hst_pp hret)),
        st.setPpar r1 owner, t1, hr1, hnodes.setPpar hr1_c,
        fun a ha => Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩) _ _,
        hok1', by simp [AuxTree.toList], by simp [AuxTree.countNodes],
        fun _ => by rw [← hr1]; simp [SplayState.setPpar, SplayState.nodes_updateNode],
        fun u _ => by by_cases h : u = r1 <;> simp [SplayState.setPpar, SplayState.nodes_updateNode, h],
        fun u hu1 _ => by
          have hne : u ≠ r1 := fun h => hu1 (h ▸ hr1 ▸ AuxTree.rootId_mem ht1)
          simp [SplayState.setPpar, SplayState.nodes_updateNode, hne], ?_⟩
      unfold ORD_PHI_WEIGHT ORD_JOIN_AMORT
      simp [ordRec, AuxTree.treePhi, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · -- Both t1 ≠ .leaf and t2 ≠ .leaf
      have hr2_nz : r2 ≠ 0 := hr2 ▸ SplayState.SubtreeInv_nonZero hok2.inv.sub (AuxTree.rootId_mem ht2)
      have hr2_c : r2 ≤ cap := hok2.mem_le r2 (hr2 ▸ AuxTree.rootId_mem ht2)
      have hcond2 : (Expr.bin .eq (.reg 2) (.const 0)).eval w st0 = some 0 :=
        Expr.eval_eq_false (Expr.eval_reg_of_eq (by simp [st0, startState])) (Expr.eval_const (by omega)) hr2_nz (by omega)
      obtain ⟨oW, stW, cW, hrunW, t1', hoW, hnW, hfrW, hok1', ht1'_ne, ht1'_root, ht1'_list, ht1'_cnt, hvalW, -, houtW, hphiW⟩ :=
        ordWalkExtremeBody_runs hrot hstep hsplay ω hnodes hok1 ht1 hr1 (Or.inr rfl) hcap hw hwide (pos := pos)
      set m := rightmostId t1 with hm_def
      have hm_eq : extremeId 1 t1 = m := by simp [extremeId, hm_def]
      rw [hm_eq] at hoW ht1'_root
      set sp1 := SplayState.splayLoop ordPayload st t1.countNodes m
      have hsp1_eq : SplayState.splayLoop ordPayload st t1.countNodes (extremeId 1 t1) = sp1 := by rw [hm_eq]
      rw [hsp1_eq] at hnW hok1' hvalW houtW
      have hrm_eq : rightmostId t1' = m := by
        have h1 := toList_getLast_eq_rightmostId ht1'_ne
        have h2 := toList_getLast_eq_rightmostId ht1
        rw [ht1'_list] at h1; rw [h1] at h2; exact Option.some.inj h2
      obtain ⟨l1, ht1'_eq⟩ := rightmost_splay_right_leaf hok1'.inv.nodup ht1'_ne (ht1'_root.trans hrm_eq.symm)
      rw [hrm_eq] at ht1'_eq
      have hm_mem1 : m ∈ t1.toList := rightmostId_mem ht1
      have hm_c : m ≤ cap := hok1.mem_le m hm_mem1
      have hm_nz : m ≠ 0 := SplayState.SubtreeInv_nonZero hok1.inv.sub hm_mem1
      have hm_ne_r2 : m ≠ r2 := fun h => hdisj m hm_mem1 (h ▸ hr2 ▸ AuxTree.rootId_mem ht2)
      have hsub2_W : SplayState.SubtreeInv ordPayload sp1 0 t2 :=
        SplayState.SubtreeInv_agree hok2.inv.sub fun u hu => (houtW u (fun h1 => hdisj u h1 hu)).symm
      have hinv2_W : TreeInv ordPayload sp1 t2 := ⟨hok2.inv.nodup, hsub2_W⟩
      have hdisj' : ∀ u ∈ (AuxTree.node m l1 .leaf).toList, u ∉ t2.toList := by
        intro u hu; rw [← ht1'_eq, ht1'_list] at hu; exact hdisj u hu
      have hcnt_sum : (AuxTree.node m l1 .leaf).countNodes + t2.countNodes ≤ 2 * eCap := by
        rw [← ht1'_eq, ht1'_cnt]; omega
      obtain ⟨hinvJ, hlistJ, hppJ, hphiJ⟩ :=
        join_right_leaf_treeInv (owner := owner) (ht1'_eq ▸ hok1'.inv) hinv2_W hdisj' hcnt_sum
      have hm_sz : (sp1.nodes m).sz = t1.countNodes := by
        have h1 : (sp1.nodes m).sz = (AuxTree.node m l1 .leaf).countNodes :=
          (ht1'_eq ▸ hok1'.inv.sub).2.2.2.2.2.1
        rw [← ht1'_eq, ht1'_cnt] at h1; exact h1
      have hr2_sz : (sp1.nodes r2).sz = t2.countNodes := by
        cases t2 with
        | leaf => exact absurd rfl ht2
        | node rid rl rr =>
          simp only [AuxTree.rootId] at hr2; subst hr2
          exact hsub2_W.2.2.2.2.2.1
      have hmemW_msz : stW.mem (nb + 8 * m + 4) = (sp1.nodes m).sz := (hnW m hm_c).2.2.2.2.1
      have hmemW_r2sz : stW.mem (nb + 8 * r2 + 4) = (sp1.nodes r2).sz := (hnW r2 hr2_c).2.2.2.2.1
      set spJ1 := sp1.updateNode m fun nd => { nd with right := t2.rootId, sz := nd.sz + t2.countNodes, ppar := owner }
      set spJ := spJ1.updateNode t2.rootId fun nd => { nd with par := m, ppar := 0 }
      have hspJ_eq : (if t2.rootId = 0 then spJ1 else spJ) = spJ := by simp [← hr2, hr2_nz]
      rw [hspJ_eq] at hinvJ hppJ
      have hcall : Runs w p ω (.call 4 walkProc [.reg 0, .reg 1, .const 1]) st0 .normal
          { stW with regs := Function.update st0.regs 4 m }
          (argsSize [.reg 0, .reg 1, .const 1] + cW + 1) :=
        runs_call_iff.mpr ⟨[nb, r1, 1], ordWalkExtremeBody splayProc, oW, stW, cW,
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [st0, startState]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st0, startState]))
              (evalArgs_cons (Expr.eval_const (by omega)) (evalArgs_nil _ _))),
          hwalk, hrunW, rfl, by simp [hoW], rfl⟩
      set stA : State := { stW with regs := Function.update st0.regs 4 m }
      have hrest : ∃ o st' c, Runs w p ω
          (.assign 5 (ordRec 4) ;;
           .assign 6 (ordRec 2) ;;
           .store (.bin .add (.reg 5) (.const 1)) (.reg 2) ;;
           .store (.bin .add (.reg 6) (.const 2)) (.reg 4) ;;
           .store (.bin .add (.reg 6) (.const 3)) (.const 0) ;;
           .store (.bin .add (.reg 5) (.const 3)) (.reg 3) ;;
           .assign 7 (.load (.bin .add (.reg 5) (.const 4))) ;;
           .assign 8 (.load (.bin .add (.reg 6) (.const 4))) ;;
           .store (.bin .add (.reg 5) (.const 4)) (.bin .add (.reg 7) (.reg 8)) ;;
           .ret (.reg 4)) stA o st' c ∧
          (o = .returned m ∧ OrdNodesAt st'.mem nb cap spJ nf ∧
            ∀ a, ¬ InOrdNodes nb cap a → st'.mem a = stW.mem a) ∧
          0 + c ≤ 200 := by
        refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb) (by simp [stA, st0, startState]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := m) (by simp [stA])) (by omega)) (by omega)) ?_
        refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb) (by simp [stA, st0, startState]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := r2) (by simp [stA, st0, startState])) (by omega)) (by omega)) ?_
        refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * m) (by simp)) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := r2) (by simp [stA, st0, startState])) ?_
        refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * r2) (by simp)) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := m) (by simp [stA])) ?_
        refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * r2) (by simp)) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_const (by omega)) ?_
        refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * m) (by simp)) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := owner) (by simp [stA, st0, startState])) ?_
        set mem4 := Function.update (Function.update (Function.update (Function.update stW.mem
          (nb + 8 * m + 1) r2) (nb + 8 * r2 + 2) m) (nb + 8 * r2 + 3) 0) (nb + 8 * m + 3) owner
        have hm4_msz : mem4 (nb + 8 * m + 4) = (sp1.nodes m).sz := by
          dsimp only [mem4]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hmemW_msz
        have hm4_r2sz : mem4 (nb + 8 * r2 + 4) = (sp1.nodes r2).sz := by
          dsimp only [mem4]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hmemW_r2sz
        refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * m) (by simp))
          (Expr.eval_const (by omega)) (by omega)) hm4_msz) ?_
        refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * r2) (by simp))
          (Expr.eval_const (by omega)) (by omega)) hm4_r2sz) ?_
        refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * m) (by simp)) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_add (Expr.eval_reg_of_eq (v := (sp1.nodes m).sz) (by simp))
            (Expr.eval_reg_of_eq (v := (sp1.nodes r2).sz) (by simp)) (by omega)) ?_
        refine runs_ret_le (Expr.eval_reg_of_eq (v := m) (by simp [stA])) ?_ ?_
        · refine ⟨rfl, ?_, fun a ha => ?_⟩
          · have hn4 : OrdNodesAt (Function.update mem4 (nb + 8 * m + 4) ((sp1.nodes m).sz + (sp1.nodes r2).sz)) nb cap
                ((((sp1.setRight m r2).setPar r2 m).setPpar r2 0).setPpar m owner |>.updateNode m
                  fun nd => { nd with sz := (sp1.nodes m).sz + (sp1.nodes r2).sz }) nf := by
              have h1 := (((hnW.setRight hm_c (v := r2)).setPar hr2_c (v := m)).setPpar hr2_c (v := 0)).setPpar hm_c (v := owner)
              exact h1.setSz hm_c
            have hsp_eq : ((((sp1.setRight m r2).setPar r2 m).setPpar r2 0).setPpar m owner |>.updateNode m
                  fun nd => { nd with sz := (sp1.nodes m).sz + (sp1.nodes r2).sz }) = spJ := by
              have hfun : ∀ u, ((((sp1.setRight m r2).setPar r2 m).setPpar r2 0).setPpar m owner |>.updateNode m
                  fun nd => { nd with sz := (sp1.nodes m).sz + (sp1.nodes r2).sz }).nodes u = spJ.nodes u := by
                intro u
                by_cases hum : u = m
                · subst hum
                  simp [spJ, spJ1, SplayState.setRight, SplayState.setPar, SplayState.setPpar,
                    SplayState.nodes_updateNode, ← hr2, hr2_sz, hm_ne_r2]
                · by_cases hur : u = r2
                  · subst hur
                    simp [spJ, spJ1, SplayState.setRight, SplayState.setPar, SplayState.setPpar,
                      SplayState.nodes_updateNode, ← hr2, Ne.symm hm_ne_r2]
                  · simp [spJ, spJ1, SplayState.setRight, SplayState.setPar, SplayState.setPpar,
                      SplayState.nodes_updateNode, ← hr2, hum, hur]
              cases h1 : ((((sp1.setRight m r2).setPar r2 m).setPpar r2 0).setPpar m owner |>.updateNode m
                  fun nd => { nd with sz := (sp1.nodes m).sz + (sp1.nodes r2).sz })
              cases h2 : spJ
              congr 1; funext u; have := hfun u; rwa [h1, h2] at this
            rw [← hsp_eq]; exact hn4
          · dsimp only [mem4]
            rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
                Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
                Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
                Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
                Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
        · simp only [ordRec, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]; omega
      obtain ⟨oR, stR, cR, hrunR, ⟨hoR, hnR, hfrR⟩, hcR⟩ := hrest
      have hokJ : OrdTreeOk cap spJ (.node m l1 t2) :=
        { null_node := by
            simp only [spJ, spJ1, SplayState.nodes_updateNode, Ne.symm hr2_nz, Ne.symm hm_nz, ← hr2, ite_false]
            exact hok1'.null_node
          clean := fun u => by
            by_cases hur : u = r2
            · subst hur; simp [spJ, spJ1, SplayState.nodes_updateNode, ← hr2, Ne.symm hm_ne_r2, hok1'.clean]
            · by_cases hum : u = m
              · subst hum; simp [spJ, spJ1, SplayState.nodes_updateNode, ← hr2, hm_ne_r2, hok1'.clean]
              · simp [spJ, spJ1, SplayState.nodes_updateNode, ← hr2, hur, hum, hok1'.clean]
          inv := hinvJ
          mem_le := fun u hu => by
            rw [hlistJ, ← ht1'_eq, ht1'_list, List.mem_append] at hu
            rcases hu with h1 | h2
            · exact hok1.mem_le u h1
            · exact hok2.mem_le u h2
          count_le := by
            have : (AuxTree.node m l1 t2).countNodes = t1.countNodes + t2.countNodes := by
              have h1 : (AuxTree.node m l1 .leaf).countNodes = t1.countNodes := ht1'_eq ▸ ht1'_cnt
              simp [AuxTree.countNodes] at h1 ⊢; omega
            omega }
      refine ⟨oR, stR, _, ord_runs_cond_false hcond1 (ord_runs_cond_false hcond2 (ord_runs_seq_normal hcall hrunR)),
        spJ, .node m l1 t2, by rw [hoR]; rfl, hnR,
        fun a ha => (hfrR a ha).trans (hfrW a ha), hokJ,
        by rw [hlistJ, ← ht1'_eq, ht1'_list],
        by have h1 : (AuxTree.node m l1 .leaf).countNodes = t1.countNodes := ht1'_eq ▸ ht1'_cnt
           simp [AuxTree.countNodes] at h1 ⊢; omega,
        fun _ => by simpa [AuxTree.rootId] using hppJ,
        fun u hu => by
          have hvalJ : (spJ.nodes u).val = (sp1.nodes u).val := by
            by_cases hur : u = r2
            · subst hur; simp [spJ, spJ1, SplayState.nodes_updateNode, ← hr2, Ne.symm hm_ne_r2]
            · by_cases hum : u = m
              · subst hum; simp [spJ, spJ1, SplayState.nodes_updateNode, ← hr2, hm_ne_r2]
              · simp [spJ, spJ1, SplayState.nodes_updateNode, ← hr2, hur, hum]
          rw [hvalJ]
          rw [hlistJ, ← ht1'_eq, ht1'_list, List.mem_append] at hu
          rcases hu with h1 | h2
          · exact hvalW u h1
          · rw [houtW u (fun h1 => hdisj u h1 h2)],
        fun u hu1 hu2 => by
          have hur : u ≠ r2 := fun h => hu2 (h ▸ hr2 ▸ AuxTree.rootId_mem ht2)
          have hum : u ≠ m := fun h => hu1 (h ▸ hm_mem1)
          simp only [spJ, spJ1, SplayState.nodes_updateNode, ← hr2, hur, hum, ite_false]
          exact houtW u hu1, ?_⟩
      have hphiJ' : (AuxTree.node m l1 t2).treePhi (fun _ => 0) ≤
          t1'.treePhi (fun _ => 0) + t2.treePhi (fun _ => 0) + ordStoreLog eCap := by
        rw [ht1'_eq]; exact hphiJ
      have hmulJ := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphiJ'
      have hsz_cond : (Expr.bin .eq (.reg 1) (.const 0)).size + (Expr.bin .eq (.reg 2) (.const 0)).size +
          argsSize [.reg 0, .reg 1, .const 1] ≤ 15 := by
        simp [Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
      unfold ORD_PHI_WEIGHT at hphiW hmulJ ⊢
      unfold ORD_WALK_AMORT at hphiW; unfold ORD_JOIN_AMORT
      omega

end MinCostFlow.SparseCore.Program
