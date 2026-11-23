module

public import MinCostFlow.HierPaths.QueryProgCopy
public import MinCostFlow.HierPaths.Layout
public import MinCostFlow.HierPaths.QueryProgGroupSize

/-!
# The routing recursion as a procedure

The procedure `routeProc` writes the steps of the walk `route k j u v`
(`HierPaths/QueryRoute.lean`) into the step buffers, after the `cnt` steps already there. It is
recursive: a call for height `k + 1` makes at most two calls for height `k`, so the depth of the
recursion is the leaf depth, and each call uses a fixed number of registers.

Its arguments: `k`, `j`, `u`, `v`, `cnt`, and the capped branching exponent, addresses `eaA`, `ebA` (the endpoints of the connectors), `wvA`, `weA` (the vertices and edges of the
connector walks, in `csrList` form), the number `nc` of connectors, the buffers `outE`, `outY`,
the context `ctx` of the procedure that picks connectors, and the root exponent `x`.

The connector between two children is read by a separate procedure, given here only by its
contract (`pickContract`): it returns `pickFor (groupOf x b) pick j u v` and writes nothing. The
connector walk is copied by `copyProc` (`HierPaths/QueryProgCopy.lean`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- The arguments of a call of `routeProc` that stay fixed in the recursion. -/
def routeFixed (b eaA ebA wvA weA nc outE outY ctx x : ℕ) : List ℕ :=
  [b, eaA, ebA, wvA, weA, nc, outE, outY, ctx, x]

/-- The fixed arguments as expressions: registers `5` to `14`. -/
def routeFixedRegs : List Expr :=
  [.reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14]

/-- The routing recursion, with procedure `fRoute` itself, `fPick` the connector choice and
`fCopy` the copy procedure. -/
def routeProc (fRoute fPick fCopy : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0)) (.ret (.reg 4)) .nop ;;
  .cond (.bin .eq (.reg 2) (.reg 3)) (.ret (.reg 4)) .nop ;;
  .assign 22 (queryGroupSizeExpr (.reg 14) (.reg 5) (.bin .add (.reg 1) (.const 1))) ;;
  .assign 27 (.bin .div (.reg 2) (.reg 22)) ;;
  .assign 15 (.bin .div (.reg 3) (.reg 22)) ;;
  .cond (.bin .eq (.reg 27) (.reg 15))
    (.call 26 fRoute
        ([.bin .sub (.reg 0) (.const 1), .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4] ++
          routeFixedRegs) ;;
      .ret (.reg 26))
    .nop ;;
  .call 16 fPick [.reg 13, .reg 1, .reg 2, .reg 3] ;;
  .assign 17 (.load (.bin .add (.reg 6) (.reg 16))) ;;
  .assign 18 (.load (.bin .add (.reg 7) (.reg 16))) ;;
  .assign 19 (.bin .eq (.bin .div (.reg 17) (.reg 22)) (.reg 27)) ;;
  .cond (.reg 19) (.assign 20 (.reg 17) ;; .assign 21 (.reg 18))
    (.assign 20 (.reg 18) ;; .assign 21 (.reg 17)) ;;
  .call 4 fRoute
    ([.bin .sub (.reg 0) (.const 1), .bin .add (.reg 1) (.const 1), .reg 2, .reg 20, .reg 4] ++
      routeFixedRegs) ;;
  .assign 23 (.bin .add (.bin .add (.reg 8) (.bin .add (.reg 10) (.const 1)))
    (.load (.bin .add (.reg 8) (.reg 16)))) ;;
  .assign 24 (.bin .add (.bin .add (.reg 9) (.bin .add (.reg 10) (.const 1)))
    (.load (.bin .add (.reg 9) (.reg 16)))) ;;
  .assign 25 (.bin .sub (.load (.bin .add (.bin .add (.reg 9) (.reg 16)) (.const 1)))
    (.load (.bin .add (.reg 9) (.reg 16)))) ;;
  .call 4 fCopy [.reg 23, .reg 24, .reg 25, .reg 19, .reg 11, .reg 12, .reg 4] ;;
  .call 4 fRoute
    ([.bin .sub (.reg 0) (.const 1), .bin .add (.reg 1) (.const 1), .reg 21, .reg 3, .reg 4] ++
      routeFixedRegs) ;;
  .ret (.reg 4)

/-- The contract of the procedure that picks connectors: called with `[ctx, j, u, v]` in a memory
with `Ctx`, it returns `pickFor (groupOf x b) pick j u v`, writes nothing, and costs at most
`Kp`. -/
def pickContract (x b : ℕ) (pick : ℕ → ℕ → ℕ → ℕ) (ctx : ℕ) (Ctx : (ℕ → ℕ) → Prop) (Kp : ℕ) :
    Contract where
  pre args mem := ∃ j u v, args = [ctx, j, u, v] ∧ Ctx mem
  post args mem r mem' := mem' = mem ∧
    ∀ j u v, args = [ctx, j, u, v] → r = pickFor (groupOf x b) pick j u v
  cost _ _ := Kp

/-- The static tables that `routeProc` reads. -/
structure RouteMem (C : ConnectorSystem) (eaA ebA wvA weA : ℕ)
    (Ctx : (ℕ → ℕ) → Prop) (mem : ℕ → ℕ) : Prop where
  ea : ListAt mem eaA (tabList C.numConn C.endA)
  eb : ListAt mem ebA (tabList C.numConn C.endB)
  wv : ListAt mem wvA (csrList C.numConn fun c => (C.walk c).verts)
  we : ListAt mem weA (csrList C.numConn fun c => (C.walk c).edges)
  ctx : Ctx mem

/-- The cells that a call with `cnt` steps already in the buffers does not write. -/
def RouteOutside (outE outY cap cnt a : ℕ) : Prop :=
  a < outE + cnt ∨ (outE + cap ≤ a ∧ a < outY + cnt) ∨ outY + cap ≤ a

/-- The steps of the walk of Lemma 10. -/
def routeSteps (C : ConnectorSystem) (x b : ℕ) (pick : ℕ → ℕ → ℕ → ℕ) (k j u v : ℕ) :
    List (ℕ × ℕ) :=
  Walk.steps (C.route (groupOf x b) pick k j u v)

/-- The cost bound of a call. -/
def routeCost (C : ConnectorSystem) (x b : ℕ) (pick : ℕ → ℕ → ℕ → ℕ) (Kp : ℕ) :
    List ℕ → ℕ
  | k :: j :: u :: v :: _ => (Kp + 300) * C.routeOps (groupOf x b) pick k j u v
  | _ => 0

/-- The contract of `routeProc`. -/
def routeContract (C : ConnectorSystem) (x b : ℕ) (pick : ℕ → ℕ → ℕ → ℕ)
    (Lmax eaA ebA wvA weA outE outY cap ctx : ℕ) (Ctx : (ℕ → ℕ) → Prop) (Kp : ℕ) :
    Contract where
  pre args mem := ∃ k j u v cnt,
    args = [k, j, u, v, cnt] ++ routeFixed (min x b) eaA ebA wvA weA C.numConn outE outY ctx x ∧
    j + k ≤ Lmax ∧ cnt + (routeSteps C x b pick k j u v).length ≤ cap ∧
    RouteMem C eaA ebA wvA weA Ctx mem ∧ C.RouteReady (groupOf x b) pick k j u v
  post args mem r mem' := ∀ k j u v cnt,
    args = [k, j, u, v, cnt] ++ routeFixed (min x b) eaA ebA wvA weA C.numConn outE outY ctx x →
    r = cnt + (routeSteps C x b pick k j u v).length ∧
    ListAt mem' (outE + cnt) ((routeSteps C x b pick k j u v).map Prod.fst) ∧
    ListAt mem' (outY + cnt) ((routeSteps C x b pick k j u v).map Prod.snd) ∧
    ∀ a, RouteOutside outE outY cap cnt a → mem' a = mem a
  cost args _ := routeCost C x b pick Kp args

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

public section

/-- A `ret` followed by more statements. -/
theorem runs_seq_ret_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hq : Q (.returned v) st) (hc : k + (e.size + 2) ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.ret e) s) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.returned v, st, e.size + 1 + 1,
    runs_seq_iff.mpr (Or.inl ⟨v, e.size + 1, runs_ret_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, rfl, rfl⟩),
    hq, by omega⟩

/-- The sums of the first lists grow. -/
theorem sum_range_map_succ (g : ℕ → ℕ) (c : ℕ) :
    ((List.range (c + 1)).map g).sum = ((List.range c).map g).sum + g c := by
  rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem sum_range_map_mono (g : ℕ → ℕ) {c k : ℕ} (h : c ≤ k) :
    ((List.range c).map g).sum ≤ ((List.range k).map g).sum := by
  induction k with
  | zero => have : c = 0 := by omega
            subst this; simp
  | succ k ih =>
    rcases Nat.lt_or_ge c (k + 1) with h' | h'
    · have := ih (by omega); rw [sum_range_map_succ]; omega
    · have : c = k + 1 := by omega
      subst this; exact le_rfl

theorem length_csrList_q (k : ℕ) (f : ℕ → List ℕ) :
    (csrList k f).length = k + 1 + ((List.range k).map fun j => (f j).length).sum := by
  simp [csrList, csrData, List.length_flatMap]

/-- The end of list `c` lies inside the compressed form. -/
theorem csr_end_le (k : ℕ) (f : ℕ → List ℕ) {c : ℕ} (hc : c < k) :
    k + 1 + ((List.range c).map fun j => (f j).length).sum + (f c).length ≤
      (csrList k f).length := by
  rw [length_csrList_q]
  have := sum_range_map_mono (fun j => (f j).length) (show c + 1 ≤ k by omega)
  rw [sum_range_map_succ] at this
  omega

/-- The routing walk at height `0` and for equal ends has no step. -/
theorem routeSteps_zero (C : ConnectorSystem) (x b : ℕ) (pick : ℕ → ℕ → ℕ → ℕ) (j u v : ℕ) :
    routeSteps C x b pick 0 j u v = [] := by
  simp [routeSteps, ConnectorSystem.route, Walk.steps, Walk.empty]

theorem routeSteps_self (C : ConnectorSystem) (x b : ℕ) (pick : ℕ → ℕ → ℕ → ℕ) (k j u : ℕ) :
    routeSteps C x b pick (k + 1) j u u = [] := by
  simp [routeSteps, ConnectorSystem.route, Walk.steps, Walk.empty]

/-- A list in memory at an address given by another expression. -/
theorem listAt_addr {mem : ℕ → ℕ} {a a' : ℕ} {l : List ℕ} (h : a = a') (hl : ListAt mem a' l) :
    ListAt mem a l := h ▸ hl

variable {C : ConnectorSystem} {x b : ℕ} {pick : ℕ → ℕ → ℕ → ℕ}

/-- The tables depend only on the cells below the buffers. -/
theorem RouteMem.congr {eaA ebA wvA weA outE : ℕ} {Ctx : (ℕ → ℕ) → Prop}
    {mem mem' : ℕ → ℕ} (h : RouteMem C eaA ebA wvA weA Ctx mem)
    (hCtx : ∀ mem mem', (∀ a < outE, mem' a = mem a) → Ctx mem → Ctx mem')
    (heaEnd : eaA + C.numConn ≤ outE)
    (hebEnd : ebA + C.numConn ≤ outE)
    (hwvEnd : wvA + (csrList C.numConn fun c => (C.walk c).verts).length ≤ outE)
    (hweEnd : weA + (csrList C.numConn fun c => (C.walk c).edges).length ≤ outE)
    (heq : ∀ a < outE, mem' a = mem a) : RouteMem C eaA ebA wvA weA Ctx mem' where
  ea := h.ea.congr fun a _ ha => heq a (by simp at ha; omega)
  eb := h.eb.congr fun a _ ha => heq a (by simp at ha; omega)
  wv := h.wv.congr fun a _ ha => heq a (by omega)
  we := h.we.congr fun a _ ha => heq a (by omega)
  ctx := hCtx mem mem' heq h.ctx

set_option maxHeartbeats 4000000 in
/-- The procedure `routeProc` meets its contract. -/
theorem routeProc_meetsContract {w : ℕ} {p : Program} {fRoute fPick fCopy : ℕ}
    {Lmax eaA ebA wvA weA outE outY cap ctx : ℕ} {Ctx : (ℕ → ℕ) → Prop} {Kp : ℕ}
    (hp : p.procs[fRoute]? = some (routeProc fRoute fPick fCopy))
    (hpc : p.procs[fCopy]? = some copyProc)
    (hpick : MeetsContract w p fPick (pickContract x b pick ctx Ctx Kp))
    (hCtx : ∀ mem mem', (∀ a < outE, mem' a = mem a) → Ctx mem → Ctx mem')
    (heaEnd : eaA + C.numConn ≤ outE)
    (hebEnd : ebA + C.numConn ≤ outE)
    (hwvEnd : wvA + (csrList C.numConn fun c => (C.walk c).verts).length ≤ outE)
    (hweEnd : weA + (csrList C.numConn fun c => (C.walk c).edges).length ≤ outE)
    (hL : Lmax ≤ leafDepth x b) (hb : 0 < b) (hxw : 2 ^ x < 2 ^ w)
    (hbuf : outE + cap ≤ outY) (hwOut : outY + cap < 2 ^ w) (hw : 1 < 2 ^ w)
    (hWF : ∀ c < C.numConn, WellFormed (C.walk c))
    (hendW : ∀ c < C.numConn, C.endA c < 2 ^ w ∧ C.endB c < 2 ^ w) :
    MeetsContract w p fRoute
      (routeContract C x b pick Lmax eaA ebA wvA weA outE outY cap ctx Ctx Kp) := by
  refine meetsContract_of_rec (fun args _ => args.headD 0) hp ?_
  intro n ih args mem pos ω hwords hpre hn
  obtain ⟨k, j, u, v, cnt, rfl, hjk, hcap, hM, hready⟩ := hpre
  simp only [List.cons_append, List.headD_cons] at hn
  subst hn
  simp only [routeFixed, List.cons_append, List.nil_append, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at hwords
  obtain ⟨hwk, hwj, hwu, hwv, hwc, hwb, hwea, hweb, hwwv, hwwe, hwnc, hwoE, hwoY, hwctx, hwx⟩ := hwords
  have hpost_eq : ∀ {k' j' u' v' cnt' : ℕ},
      [k', j', u', v', cnt'] ++ routeFixed (min x b) eaA ebA wvA weA C.numConn outE outY ctx x =
        [k, j, u, v, cnt] ++ routeFixed (min x b) eaA ebA wvA weA C.numConn outE outY ctx x →
      k' = k ∧ j' = j ∧ u' = u ∧ v' = v ∧ cnt' = cnt := by
    intro k' j' u' v' cnt' h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  -- The trivial calls: nothing is written.
  have hnone : routeSteps C x b pick k j u v = [] →
      (routeContract C x b pick Lmax eaA ebA wvA weA outE outY cap ctx Ctx Kp).post
        ([k, j, u, v, cnt] ++ routeFixed (min x b) eaA ebA wvA weA C.numConn outE outY ctx x) mem cnt mem := by
    intro h0 k' j' u' v' cnt' h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpost_eq h.symm
    rw [h0]
    exact ⟨by simp, listAt_nil _ _, listAt_nil _ _, fun _ _ => rfl⟩
  have hops : 1 ≤ C.routeOps (groupOf x b) pick k j u v := by
    cases k with
    | zero => simp [ConnectorSystem.routeOps]
    | succ k => simp only [ConnectorSystem.routeOps]; split_ifs <;> omega
  have hcost1 : (Kp + 300) * 1 ≤ (Kp + 300) * C.routeOps (groupOf x b) pick k j u v :=
    Nat.mul_le_mul_left _ hops
  simp only [routeFixed, List.cons_append, List.nil_append] at hnone ⊢
  refine runs_start_le ?_
  unfold routeProc
  simp only [routeFixedRegs, List.cons_append, List.nil_append]
  wram_step
  · -- Height `0`: nothing to write.
    subst hcond
    refine runs_seq_ret_le (by eval_expr) (hnone (routeSteps_zero C x b pick j u v)) ?_
    simp only [routeContract, routeCost]
    try simp only [queryGroupSizeExpr]
    wram_cost
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  wram_step
  wram_step
  · -- Equal ends: nothing to write.
    subst hcond
    refine runs_seq_ret_le (by eval_expr) (hnone (routeSteps_self C x b pick k j u)) ?_
    simp only [routeContract, routeCost]
    try simp only [queryGroupSizeExpr]
    wram_cost
  have hGpos : 0 < groupSize x b (j + 1) := Nat.two_pow_pos _
  have hdu : u / groupSize x b (j + 1) < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hwu
  have hdv : v / groupSize x b (j + 1) < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hwv
  have hsteps := C.steps_route_ready (groupOf x b) pick hWF k j u v hready
  simp only [hcond, ↓reduceIte] at hsteps
  have hgrp : ∀ y, groupOf x b (j + 1) y = y / groupSize x b (j + 1) := fun _ => rfl
  have hnext : j + 1 ≤ leafDepth x b := by omega
  have hxpos : 0 < x := by
    by_contra! h
    have hx : x = 0 := by omega
    have hd : leafDepth x b = 0 := by
      rw [hx]
      exact Nat.div_eq_of_lt (by unfold leafDepth at *; omega : (0 + b - 1) < b)
    omega
  have hjw : j + 1 < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ (lt_min hxpos hb)).trans_lt
      (queryDepth_mul_min_lt hb hnext hxw)
  wram_step
  refine runs_seq_assign_le
    (eval_queryGroupSizeExpr (xe := .reg 14) (be := .reg 5)
      (je := .bin .add (.reg 1) (.const 1)) (by eval_expr) (by eval_expr)
      (Expr.eval_add (a := .reg 1) (by eval_expr) (Expr.eval_const hw) hjw) hxw
      (queryDepth_mul_min_lt hb hnext hxw)) ?_
  simp only [groupSize_query_min_branch]
  have hGw : groupSize x b (j + 1) < 2 ^ w :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le ..)).trans_lt hxw
  wram_step
  wram_step
  wram_step
  · -- The two ends lie in one child: one call one level down.
    have hsame : groupOf x b (j + 1) u = groupOf x b (j + 1) v := by rw [hgrp, hgrp]; exact hcond
    simp only [hsame, ↓reduceIte] at hsteps
    simp only [ConnectorSystem.RouteReady, hsame, show u ≠ v by assumption, ↓reduceIte] at hready
    have huv : u ≠ v := by assumption
    have hopsEq : C.routeOps (groupOf x b) pick (k + 1) j u v =
        1 + C.routeOps (groupOf x b) pick k (j + 1) u v := by
      simp [ConnectorSystem.routeOps, huv, hsame]
    wram_step
    wram_step
    · refine ⟨⟨k, j + 1, u, v, cnt, by simp [routeFixed], by omega, ?_, hM, hready⟩, by simp⟩
      unfold routeSteps at hcap ⊢
      rw [hsteps] at hcap
      exact hcap
    · intro r mem' pos' hpost
      obtain ⟨hr, hLE, hLY, hfr⟩ := hpost k (j + 1) u v cnt (by simp [routeFixed])
      refine runs_seq_ret_le (by eval_expr) ?_ ?_
      · intro k' j' u' v' cnt' h
        simp only [routeFixed, List.cons_append, List.nil_append, List.cons.injEq] at h
        obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
        subst h1 h2 h3 h4 h5
        simp only [routeSteps, Outcome.value] at hr hLE hLY ⊢
        rw [hsteps]
        exact ⟨by omega, hLE, hLY, hfr⟩
      · simp only [Contract.below, routeContract, routeCost, Nat.add_sub_cancel]
        rw [hopsEq, Nat.mul_add]
        try simp only [queryGroupSizeExpr]
        wram_cost
  -- The two ends lie in different children: pick the connector between them.
  have hdiff : groupOf x b (j + 1) u ≠ groupOf x b (j + 1) v := by rw [hgrp, hgrp]; exact hcond
  have huv : u ≠ v := by assumption
  simp only [hdiff, ↓reduceIte] at hsteps
  simp only [ConnectorSystem.RouteReady, huv, hdiff, ↓reduceIte] at hready
  wram_step
  wram_step
  · exact ⟨j, u, v, rfl, hM.ctx⟩
  intro cc mem1 pos1 hpost
  obtain ⟨hmem1, hcc⟩ := hpost
  have hcc' := hcc j u v rfl
  subst hmem1 hcc'
  set c := pickFor (groupOf x b) pick j u v with hc
  have hcn : c < C.numConn := hready.1
  have hea : mem1 (eaA + c) = C.endA c := listAt_tabList hM.ea hcn
  have heb : mem1 (ebA + c) = C.endB c := listAt_tabList hM.eb hcn
  have hwA := (hendW c hcn).1
  have hwB := (hendW c hcn).2
  have hwA' : mem1 (eaA + c) < 2 ^ w := by rw [hea]; exact hwA
  have hwB' : mem1 (ebA + c) < 2 ^ w := by rw [heb]; exact hwB
  have hdA : C.endA c / groupSize x b (j + 1) < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hwA
  have hcw : C.connWalk (groupOf x b) pick j u v =
      copyWalk (C.walk c).verts (C.walk c).edges (decide (C.fwd (groupOf x b) pick j u v)) := by
    unfold ConnectorSystem.connWalk copyWalk
    by_cases hF : C.fwd (groupOf x b) pick j u v <;> simp [hF, ← hc]
  wram_step
  wram_step
  wram_step
  wram_step
  · -- The connector is used in its stored direction.
    rw [hea] at hcond
    have hF : C.fwd (groupOf x b) pick j u v := by
      unfold ConnectorSystem.fwd; rw [hgrp, hgrp, ← hc]; exact hcond
    have hfrom : C.connFrom (groupOf x b) pick j u v = mem1 (eaA + c) := by
      simp [ConnectorSystem.connFrom, hF, hea, ← hc]
    have hto : C.connTo (groupOf x b) pick j u v = mem1 (ebA + c) := by
      simp [ConnectorSystem.connTo, hF, heb, ← hc]
    have hflag : (if mem1 (eaA + c) / groupSize x b (j + 1) = u / groupSize x b (j + 1) then 1 else 0)
        = if decide (C.fwd (groupOf x b) pick j u v) = true then 1 else 0 := by
      simp [hea, hcond, hF]
    wram_step
    wram_step
    wram_step
    -- The first half, from `u` to the connector.
    have hL : cnt + ((routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v)).length +
        ((Walk.steps (C.connWalk (groupOf x b) pick j u v)).length +
          (routeSteps C x b pick k (j + 1) (C.connTo (groupOf x b) pick j u v) v).length)) ≤ cap := by
      have := hcap; unfold routeSteps at this ⊢; rw [hsteps] at this
      simpa only [List.length_append] using this
    have hne : (Walk.steps (C.connWalk (groupOf x b) pick j u v)).length = (C.walk c).edges.length := by
      rw [hcw]; exact length_steps_copyWalk_empty_or (hWF c hcn) _
    rw [hne] at hL
    wram_step
    · refine ⟨⟨k, j + 1, u, C.connFrom (groupOf x b) pick j u v, cnt,
        by simp [routeFixed, hfrom, hea, heb], by omega, by omega, hM, hready.2.1⟩, by simp⟩
    intro cnt1 mem2 pos2 hpost1
    obtain ⟨hr1, hLE1, hLY1, hfr1⟩ := hpost1 k (j + 1) u (C.connFrom (groupOf x b) pick j u v) cnt
      (by simp [routeFixed, hfrom, hea, heb])
    have hbelow2 : ∀ a < outE, mem2 a = mem1 a := fun a ha => hfr1 a (Or.inl (by omega))
    -- The connector walk in the tables.
    have hVend := csr_end_le C.numConn (fun c => (C.walk c).verts) hcn
    have hEend := csr_end_le C.numConn (fun c => (C.walk c).edges) hcn
    have hlv := hWF c hcn
    have hlenVE : (C.walk c).edges.length ≤ (C.walk c).verts.length := by
      rcases hlv with h | h
      · rw [h]; exact Nat.zero_le _
      · omega
    have hoffV : mem2 (wvA + c) =
        ((List.range c).map fun i => (C.walk i).verts.length).sum := by
      rw [hbelow2 _ (by omega)]; exact csrList_offset hM.wv hcn.le
    have hoffE : mem2 (weA + c) =
        ((List.range c).map fun i => (C.walk i).edges.length).sum := by
      rw [hbelow2 _ (by omega)]; exact csrList_offset hM.we hcn.le
    have hoffE1 : mem2 (weA + c + 1) =
        ((List.range (c + 1)).map fun i => (C.walk i).edges.length).sum := by
      rw [hbelow2 _ (by omega), Nat.add_assoc]; exact csrList_offset hM.we hcn
    have hsum1 := sum_range_map_succ (fun i => (C.walk i).edges.length) c
    have hcp := copyProc_meetsContract (p := p) hpc (w := w)
      (vA := wvA + (C.numConn + 1) + ((List.range c).map fun i => (C.walk i).verts.length).sum)
      (eA := weA + (C.numConn + 1) + ((List.range c).map fun i => (C.walk i).edges.length).sum)
      (outE := outE) (outY := outY) (cnt := cnt + (routeSteps C x b pick k (j + 1) u
        (C.connFrom (groupOf x b) pick j u v)).length)
      (V := (C.walk c).verts) (Ed := (C.walk c).edges)
      (fwd := decide (C.fwd (groupOf x b) pick j u v)) hw (by omega) (by omega) (by omega)
      (by omega)
    wram_step
    wram_step
    wram_step
    wram_step
    · rw [hoffV, hoffE, hoffE1]
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
        and_true]
      refine ⟨by omega, by omega, by omega, by split <;> omega, by omega, by omega, by omega⟩
    · rw [hoffV, hoffE, hoffE1]
      refine ⟨?_, hlv, ?_, ?_, ?_, ?_, by omega⟩
      · simp only [List.cons.injEq, and_true, true_and]
        omega
      · exact (listAt_csrList_get hM.wv hcn).congr fun a _ ha => hbelow2 a (by omega)
      · exact (listAt_csrList_get hM.we hcn).congr fun a _ ha => hbelow2 a (by omega)
      · intro i hi; unfold CopyOutside; omega
      · intro i hi; unfold CopyOutside; omega
    intro cnt2 mem3 pos3 hpost2
    obtain ⟨hr2, hLE2, hLY2, hfr2⟩ := hpost2
    have hbelow3 : ∀ a < outE, mem3 a = mem1 a := fun a ha =>
      (hfr2 a ⟨Or.inl (by omega), Or.inl (by omega)⟩).trans (hbelow2 a ha)
    -- The second half, from the connector to `v`.
    wram_step
    · refine ⟨⟨k, j + 1, C.connTo (groupOf x b) pick j u v, v, cnt2,
        by simp [routeFixed, hto, hea, heb, hr2], by omega, by omega,
        hM.congr hCtx heaEnd hebEnd hwvEnd hweEnd hbelow3, hready.2.2⟩, by simp⟩
    intro cnt3 mem4 pos4 hpost3
    obtain ⟨hr3, hLE3, hLY3, hfr3⟩ := hpost3 k (j + 1) (C.connTo (groupOf x b) pick j u v) v cnt2
      (by simp [routeFixed, hto, hea, heb, hr2])
    refine runs_ret_le (by eval_expr) ?_ ?_
    · intro k' j' u' v' cnt' h
      simp only [routeFixed, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
      subst h1 h2 h3 h4 h5
      dsimp only
      try dsimp only at hfr1
      try dsimp only at hfr2
      try dsimp only at hfr3
      try dsimp only at hLE1
      try dsimp only at hLY1
      try dsimp only at hLE2
      try dsimp only at hLY2
      try dsimp only at hLE3
      try dsimp only at hLY3
      have hS : routeSteps C x b pick (k + 1) j u v =
          routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v) ++
            (Walk.steps (copyWalk (C.walk c).verts (C.walk c).edges
                (decide (C.fwd (groupOf x b) pick j u v))) ++
              routeSteps C x b pick k (j + 1) (C.connTo (groupOf x b) pick j u v) v) := by
        unfold routeSteps; rw [hsteps, hcw]
      have hlc := length_steps_copyWalk_empty_or hlv (decide (C.fwd (groupOf x b) pick j u v))
      rw [hS]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [Outcome.value, List.length_append]; omega
      · rw [List.map_append, List.map_append, listAt_append, listAt_append]
        refine ⟨?_, listAt_addr (a' := outE + (cnt + (routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v)).length))
          (by simp only [List.length_map]; omega) ?_,
          listAt_addr (by simp only [List.length_map]; omega) hLE3⟩
        · refine hLE1.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inl (by omega)), hfr2 a ⟨Or.inl (by omega), Or.inl (by omega)⟩]
        · refine hLE2.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inl (by omega))]
      · rw [List.map_append, List.map_append, listAt_append, listAt_append]
        refine ⟨?_, listAt_addr (a' := outY + (cnt + (routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v)).length))
          (by simp only [List.length_map]; omega) ?_,
          listAt_addr (by simp only [List.length_map]; omega) hLY3⟩
        · refine hLY1.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inr (Or.inl ⟨by omega, by omega⟩)),
            hfr2 a ⟨Or.inr (by omega), Or.inl (by omega)⟩]
        · refine hLY2.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      · intro a ha
        unfold RouteOutside at ha
        rw [hfr3 a (by unfold RouteOutside; omega), hfr2 a (by unfold CopyOutside; omega),
          hfr1 a (by unfold RouteOutside; omega)]
    · have hcwlen : (C.connWalk (groupOf x b) pick j u v).edges.length = (C.walk c).edges.length := by
        unfold ConnectorSystem.connWalk; split_ifs <;> simp [← hc]
      have hopsEq : C.routeOps (groupOf x b) pick (k + 1) j u v =
          1 + C.routeOps (groupOf x b) pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v) +
            ((C.walk c).edges.length + 1) +
            C.routeOps (groupOf x b) pick k (j + 1) (C.connTo (groupOf x b) pick j u v) v := by
        simp only [ConnectorSystem.routeOps, huv, hdiff, ↓reduceIte]; rw [hcwlen]
      rw [hfrom, hto] at hopsEq
      simp only [hea, heb] at hopsEq
      simp only [Contract.below, routeContract, copyContract, routeCost, Nat.add_sub_cancel,
        pickContract, hea, heb]
      rw [hopsEq, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_add _ _ 1,
        Nat.mul_one]
      have := Nat.mul_le_mul_right (C.walk c).edges.length (show 60 ≤ Kp + 300 by omega)
      try simp only [queryGroupSizeExpr]
      wram_cost
  · -- The connector is used reversed.
    rw [hea] at hcond
    have hF : ¬ C.fwd (groupOf x b) pick j u v := by
      unfold ConnectorSystem.fwd; rw [hgrp, hgrp, ← hc]; exact hcond
    have hfrom : C.connFrom (groupOf x b) pick j u v = mem1 (ebA + c) := by
      simp [ConnectorSystem.connFrom, hF, heb, ← hc]
    have hto : C.connTo (groupOf x b) pick j u v = mem1 (eaA + c) := by
      simp [ConnectorSystem.connTo, hF, hea, ← hc]
    have hflag : (if mem1 (eaA + c) / groupSize x b (j + 1) = u / groupSize x b (j + 1) then 1 else 0)
        = if decide (C.fwd (groupOf x b) pick j u v) = true then 1 else 0 := by
      simp [hea, hcond, hF]
    wram_step
    wram_step
    wram_step
    -- The first half, from `u` to the connector.
    have hL : cnt + ((routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v)).length +
        ((Walk.steps (C.connWalk (groupOf x b) pick j u v)).length +
          (routeSteps C x b pick k (j + 1) (C.connTo (groupOf x b) pick j u v) v).length)) ≤ cap := by
      have := hcap; unfold routeSteps at this ⊢; rw [hsteps] at this
      simpa only [List.length_append] using this
    have hne : (Walk.steps (C.connWalk (groupOf x b) pick j u v)).length = (C.walk c).edges.length := by
      rw [hcw]; exact length_steps_copyWalk_empty_or (hWF c hcn) _
    rw [hne] at hL
    wram_step
    · refine ⟨⟨k, j + 1, u, C.connFrom (groupOf x b) pick j u v, cnt,
        by simp [routeFixed, hfrom, hea, heb], by omega, by omega, hM, hready.2.1⟩, by simp⟩
    intro cnt1 mem2 pos2 hpost1
    obtain ⟨hr1, hLE1, hLY1, hfr1⟩ := hpost1 k (j + 1) u (C.connFrom (groupOf x b) pick j u v) cnt
      (by simp [routeFixed, hfrom, hea, heb])
    have hbelow2 : ∀ a < outE, mem2 a = mem1 a := fun a ha => hfr1 a (Or.inl (by omega))
    -- The connector walk in the tables.
    have hVend := csr_end_le C.numConn (fun c => (C.walk c).verts) hcn
    have hEend := csr_end_le C.numConn (fun c => (C.walk c).edges) hcn
    have hlv := hWF c hcn
    have hlenVE : (C.walk c).edges.length ≤ (C.walk c).verts.length := by
      rcases hlv with h | h
      · rw [h]; exact Nat.zero_le _
      · omega
    have hoffV : mem2 (wvA + c) =
        ((List.range c).map fun i => (C.walk i).verts.length).sum := by
      rw [hbelow2 _ (by omega)]; exact csrList_offset hM.wv hcn.le
    have hoffE : mem2 (weA + c) =
        ((List.range c).map fun i => (C.walk i).edges.length).sum := by
      rw [hbelow2 _ (by omega)]; exact csrList_offset hM.we hcn.le
    have hoffE1 : mem2 (weA + c + 1) =
        ((List.range (c + 1)).map fun i => (C.walk i).edges.length).sum := by
      rw [hbelow2 _ (by omega), Nat.add_assoc]; exact csrList_offset hM.we hcn
    have hsum1 := sum_range_map_succ (fun i => (C.walk i).edges.length) c
    have hcp := copyProc_meetsContract (p := p) hpc (w := w)
      (vA := wvA + (C.numConn + 1) + ((List.range c).map fun i => (C.walk i).verts.length).sum)
      (eA := weA + (C.numConn + 1) + ((List.range c).map fun i => (C.walk i).edges.length).sum)
      (outE := outE) (outY := outY) (cnt := cnt + (routeSteps C x b pick k (j + 1) u
        (C.connFrom (groupOf x b) pick j u v)).length)
      (V := (C.walk c).verts) (Ed := (C.walk c).edges)
      (fwd := decide (C.fwd (groupOf x b) pick j u v)) hw (by omega) (by omega) (by omega)
      (by omega)
    wram_step
    wram_step
    wram_step
    wram_step
    · rw [hoffV, hoffE, hoffE1]
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
        and_true]
      refine ⟨by omega, by omega, by omega, by split <;> omega, by omega, by omega, by omega⟩
    · rw [hoffV, hoffE, hoffE1]
      refine ⟨?_, hlv, ?_, ?_, ?_, ?_, by omega⟩
      · simp only [List.cons.injEq, and_true, true_and]
        omega
      · exact (listAt_csrList_get hM.wv hcn).congr fun a _ ha => hbelow2 a (by omega)
      · exact (listAt_csrList_get hM.we hcn).congr fun a _ ha => hbelow2 a (by omega)
      · intro i hi; unfold CopyOutside; omega
      · intro i hi; unfold CopyOutside; omega
    intro cnt2 mem3 pos3 hpost2
    obtain ⟨hr2, hLE2, hLY2, hfr2⟩ := hpost2
    have hbelow3 : ∀ a < outE, mem3 a = mem1 a := fun a ha =>
      (hfr2 a ⟨Or.inl (by omega), Or.inl (by omega)⟩).trans (hbelow2 a ha)
    -- The second half, from the connector to `v`.
    wram_step
    · refine ⟨⟨k, j + 1, C.connTo (groupOf x b) pick j u v, v, cnt2,
        by simp [routeFixed, hto, hea, heb, hr2], by omega, by omega,
        hM.congr hCtx heaEnd hebEnd hwvEnd hweEnd hbelow3, hready.2.2⟩, by simp⟩
    intro cnt3 mem4 pos4 hpost3
    obtain ⟨hr3, hLE3, hLY3, hfr3⟩ := hpost3 k (j + 1) (C.connTo (groupOf x b) pick j u v) v cnt2
      (by simp [routeFixed, hto, hea, heb, hr2])
    refine runs_ret_le (by eval_expr) ?_ ?_
    · intro k' j' u' v' cnt' h
      simp only [routeFixed, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
      subst h1 h2 h3 h4 h5
      dsimp only
      try dsimp only at hfr1
      try dsimp only at hfr2
      try dsimp only at hfr3
      try dsimp only at hLE1
      try dsimp only at hLY1
      try dsimp only at hLE2
      try dsimp only at hLY2
      try dsimp only at hLE3
      try dsimp only at hLY3
      have hS : routeSteps C x b pick (k + 1) j u v =
          routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v) ++
            (Walk.steps (copyWalk (C.walk c).verts (C.walk c).edges
                (decide (C.fwd (groupOf x b) pick j u v))) ++
              routeSteps C x b pick k (j + 1) (C.connTo (groupOf x b) pick j u v) v) := by
        unfold routeSteps; rw [hsteps, hcw]
      have hlc := length_steps_copyWalk_empty_or hlv (decide (C.fwd (groupOf x b) pick j u v))
      rw [hS]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [Outcome.value, List.length_append]; omega
      · rw [List.map_append, List.map_append, listAt_append, listAt_append]
        refine ⟨?_, listAt_addr (a' := outE + (cnt + (routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v)).length))
          (by simp only [List.length_map]; omega) ?_,
          listAt_addr (by simp only [List.length_map]; omega) hLE3⟩
        · refine hLE1.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inl (by omega)), hfr2 a ⟨Or.inl (by omega), Or.inl (by omega)⟩]
        · refine hLE2.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inl (by omega))]
      · rw [List.map_append, List.map_append, listAt_append, listAt_append]
        refine ⟨?_, listAt_addr (a' := outY + (cnt + (routeSteps C x b pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v)).length))
          (by simp only [List.length_map]; omega) ?_,
          listAt_addr (by simp only [List.length_map]; omega) hLY3⟩
        · refine hLY1.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inr (Or.inl ⟨by omega, by omega⟩)),
            hfr2 a ⟨Or.inr (by omega), Or.inl (by omega)⟩]
        · refine hLY2.congr fun a h1 h2 => ?_
          simp only [List.length_map] at h2
          rw [hfr3 a (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      · intro a ha
        unfold RouteOutside at ha
        rw [hfr3 a (by unfold RouteOutside; omega), hfr2 a (by unfold CopyOutside; omega),
          hfr1 a (by unfold RouteOutside; omega)]
    · have hcwlen : (C.connWalk (groupOf x b) pick j u v).edges.length = (C.walk c).edges.length := by
        unfold ConnectorSystem.connWalk; split_ifs <;> simp [← hc]
      have hopsEq : C.routeOps (groupOf x b) pick (k + 1) j u v =
          1 + C.routeOps (groupOf x b) pick k (j + 1) u (C.connFrom (groupOf x b) pick j u v) +
            ((C.walk c).edges.length + 1) +
            C.routeOps (groupOf x b) pick k (j + 1) (C.connTo (groupOf x b) pick j u v) v := by
        simp only [ConnectorSystem.routeOps, huv, hdiff, ↓reduceIte]; rw [hcwlen]
      rw [hfrom, hto] at hopsEq
      simp only [hea, heb] at hopsEq
      simp only [Contract.below, routeContract, copyContract, routeCost, Nat.add_sub_cancel,
        pickContract, hea, heb]
      rw [hopsEq, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_add _ _ 1,
        Nat.mul_one]
      have := Nat.mul_le_mul_right (C.walk c).edges.length (show 60 ≤ Kp + 300 by omega)
      try simp only [queryGroupSizeExpr]
      wram_cost

end

end MinCostFlow.HierPaths
