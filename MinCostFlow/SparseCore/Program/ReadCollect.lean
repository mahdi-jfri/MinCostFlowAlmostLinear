module

public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.Logic
import MinCostFlow.LSF.Program.BatchBFSMath
import MinCostFlow.DynSpanner.Program.DynGraphEdges
public import WordRAM.Tactic

/-!
# Listing the edges with a given end at a vertex

A split of the tree `T` with tag `3` needs, at the split vertex, the list of the frozen edges with
their tail (or head) there, or the list of the live edges at the new vertex. A graph in memory
(`DynGraphAt`) keeps, for each vertex, a doubly linked list of the half-edges at it: `2 e` for the
tail of `e`, `2 e + 1` for its head. The procedure `collectStmt` (`[gPtr, v, par, out]`) walks this
list at `v` and writes at `out` the edges whose half-edge has parity `par`: the edges with tail `v`
for `par = 0`, with head `v` for `par = 1`. It returns their number and costs a constant per
half-edge at `v`, so at most `60 · deg v + 100` (`collect_meetsContract`).
-/

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner.Program MinCostFlow.LSF.Program

public section

/-- The end of the edge `e` that `par` names: its tail for `par = 0`, its head otherwise. -/
@[expose] def endAt (G : MGraph) (par e : ℕ) : ℕ := if par = 0 then G.tail e else G.head e

/-- The incidence list at a vertex `v` of a graph in memory: a doubly linked list of the
half-edges at `v` (`2 e` for a tail, `2 e + 1` for a head), with `deg v` entries. -/
theorem dg_incList {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) {v : ℕ} (hv : v ∈ G.V) :
    ∃ L : List ℕ, IsDoublyLinkedList mem (dgHePrevBase a vCap eCap) (dgHeNextBase a vCap eCap)
        (dgIncHeadBase a vCap + mem (dgExtToIntBase a vCap + v)) (2 * eCap) L ∧
      L.length = G.deg v ∧
      ∀ h, h ∈ L ↔ h < 2 * eCap ∧ h / 2 ∈ G.E ∧ endAt G (h % 2) (h / 2) = v := by
  have hdeg := hG.slotDeg_eq_deg hv
  rcases hG with ⟨hval, hvCap, heCap, _, _, _, _, _, _, heti0, _, _, _, hets_ehs, ⟨incL, hincL⟩⟩
  set s := mem (dgExtToIntBase a vCap + v)
  have hsV : s ∈ G.V := (heti0 v hv).1
  have hs_cap : s < vCap := hvCap s hsV
  rcases hincL s hs_cap with ⟨hdll, hsdeg, hmem_iff⟩
  refine ⟨incL s, hdll, hsdeg.symm.trans hdeg, fun h => ?_⟩
  rw [hmem_iff]
  refine and_congr_right fun _ => and_congr_right fun heE => ?_
  rcases hets_ehs _ heE with ⟨ht_eq, hh_eq⟩
  rcases hval _ heE with ⟨htV, hhV⟩
  have hinj : ∀ x ∈ G.V, mem (dgExtToIntBase a vCap + x) = s ↔ x = v := fun x hx =>
    ⟨fun hxs => by
      have := congrArg (fun y => mem (dgIntToExtBase a vCap + y)) hxs
      rw [(heti0 x hx).2, (heti0 v hv).2] at this
      exact this, fun hxv => hxv ▸ rfl⟩
  unfold endAt
  by_cases heven : h % 2 = 0
  · simp only [heven, ↓reduceIte, ht_eq]; exact hinj _ htV
  · simp only [heven, ↓reduceIte, hh_eq]; exact hinj _ hhV

/-- The edges of the half-edges of parity `par` in a list of half-edges. -/
@[expose] def halfEdges (par : ℕ) (L : List ℕ) : List ℕ :=
  (L.filter fun h => h % 2 = par).map (· / 2)

theorem halfEdges_append (par : ℕ) (L₁ L₂ : List ℕ) :
    halfEdges par (L₁ ++ L₂) = halfEdges par L₁ ++ halfEdges par L₂ := by
  simp [halfEdges, List.filter_append]

theorem halfEdges_singleton_of (par h : ℕ) (hp : h % 2 = par) : halfEdges par [h] = [h / 2] := by
  simp [halfEdges, hp]

theorem halfEdges_singleton_not (par h : ℕ) (hp : ¬ h % 2 = par) : halfEdges par [h] = [] := by
  simp [halfEdges, hp]

theorem halfEdges_nodup {par : ℕ} {L : List ℕ} (hL : L.Nodup) : (halfEdges par L).Nodup := by
  refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (hL.filter _)
  have hx' := (List.mem_filter.mp hx).2
  have hy' := (List.mem_filter.mp hy).2
  simp only [decide_eq_true_eq] at hx' hy'
  omega

/-- The procedure body for one half-edge `h` (register `7` holds `h + 1`): move register `7` to
the next half-edge, and write `h / 2` if `h` has parity `par` (register `2`). -/
@[expose] def collectBody : Stmt :=
  .assign 10 (.bin .sub (.reg 7) (.const 1)) ;;
  .assign 7 (.load (.bin .add (.reg 8) (.reg 10))) ;;
  .cond (.bin .eq (.bin .mod (.reg 10) (.const 2)) (.reg 2))
    (.store (.bin .add (.reg 3) (.reg 9)) (.bin .div (.reg 10) (.const 2)) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1)))
    .nop

/-- `[gPtr, v, par, out]`: write at `out` the edges with tail (`par = 0`) or head (`par = 1`) at
`v`, and return their number. -/
@[expose] def collectStmt : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 6 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 3) (.reg 4))) (.reg 1))) ;;
  .assign 7 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 6) (.reg 4))) (.reg 6))) ;;
  .assign 8 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 4))) (.bin .mul (.const 7) (.reg 5))) ;;
  .assign 9 (.const 0) ;;
  .loop (.reg 7) collectBody ;;
  .ret (.reg 9)

theorem collectStmt_noRand : collectStmt.NoRand := by
  simp [collectStmt, collectBody, Stmt.NoRand]

/-- Contract of `collectStmt` on the graph `G`: the list `L` it writes holds each edge with the
named end at `v` once, and memory outside `[out, out + |L|)` is unchanged. -/
@[expose] def collectContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr v par out, args = [gPtr, v, par, out] ∧ 16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ out + eCap < 2 ^ w ∧ v ∈ G.V ∧ par < 2 ∧
    DynGraphAt mem gPtr vCap eCap G ∧
    (∀ i < eCap, out + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ out + i)
  post args mem ret mem' := ∃ gPtr v par out, args = [gPtr, v, par, out] ∧
    ∃ L : List ℕ, L.Nodup ∧ (∀ e, e ∈ L ↔ e ∈ G.E ∧ endAt G par e = v) ∧ ret = L.length ∧
      ListAt mem' out L ∧ (∀ a, a < out ∨ out + L.length ≤ a → mem' a = mem a)
  cost args _ := 60 * G.deg (args.getD 1 0) + 100

/-- The edges of the half-edges of parity `par` at `v` are the edges with that end at `v`. -/
theorem halfEdges_mem_iff {G : MGraph} {eCap v par : ℕ} {L : List ℕ} (hpar : par < 2)
    (heCap : ∀ e ∈ G.E, e < eCap)
    (hL : ∀ h, h ∈ L ↔ h < 2 * eCap ∧ h / 2 ∈ G.E ∧ endAt G (h % 2) (h / 2) = v) (e : ℕ) :
    e ∈ halfEdges par L ↔ e ∈ G.E ∧ endAt G par e = v := by
  unfold halfEdges
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨h, ⟨hhL, hpar'⟩, rfl⟩
    obtain ⟨_, he, hend⟩ := (hL h).mp hhL
    exact ⟨he, hpar' ▸ hend⟩
  · rintro ⟨he, hend⟩
    have hlt := heCap e he
    refine ⟨2 * e + par, ⟨(hL _).mpr ⟨by omega, ?_, ?_⟩, by omega⟩, by omega⟩
    · rwa [show (2 * e + par) / 2 = e by omega]
    · rwa [show (2 * e + par) / 2 = e by omega, show (2 * e + par) % 2 = par by omega]

end

/-! ## The proof -/

/-- The loop invariant with `xs` half-edges left: the first part `pre` of the list is done, its
edges of parity `par` are written at `out`, and register `7` points to the rest. -/
private def CollectInv (mem : ℕ → ℕ) (gPtr v par out heNext eCap : ℕ) (L : List ℕ)
    (xs : List ℕ) (st : State) : Prop :=
  ∃ pre, pre ++ xs = L ∧ st.regs 0 = gPtr ∧ st.regs 1 = v ∧ st.regs 2 = par ∧
    st.regs 3 = out ∧ st.regs 8 = heNext ∧ st.regs 9 = (halfEdges par pre).length ∧
    ListAt st.mem out (halfEdges par pre) ∧
    (∀ a, a < out ∨ out + (halfEdges par pre).length ≤ a → st.mem a = mem a) ∧
    DllTailAt mem heNext (2 * eCap) xs (st.regs 7)

private theorem halfEdges_length_le {par eCap : ℕ} {L pre xs : List ℕ} (hL : L.Nodup)
    (hlt : ∀ h ∈ L, h < 2 * eCap) (hpre : pre ++ xs = L) : (halfEdges par pre).length ≤ eCap := by
  have hnd : pre.Nodup := (hpre ▸ hL).sublist (List.sublist_append_left _ _)
  refine nodup_length_le_cap (halfEdges_nodup hnd) fun e he => ?_
  unfold halfEdges at he
  simp only [List.mem_map, List.mem_filter] at he
  obtain ⟨h, ⟨hh, _⟩, rfl⟩ := he
  have := hlt h (hpre ▸ List.mem_append_left _ hh)
  omega

/-- `collectStmt` meets `collectContract`. -/
public theorem collect_meetsContract {w : ℕ} {p : Program} {f vCap eCap : ℕ} {G : MGraph}
    (hp : p.procs[f]? = some collectStmt) :
    MeetsContract w p f (collectContract w vCap eCap G) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨gPtr, v, par, out, rfl, hw16, hbound, hout, hv, hpar, hG, hdisj⟩
  have hG' := hG
  obtain ⟨L, hdll, hlen, hmemL⟩ := dg_incList hG hv
  have heCap : ∀ e ∈ G.E, e < eCap := hG.2.2.1
  have hvc : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hec : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  have hsV : mem (dgExtToIntBase gPtr vCap + v) ∈ G.V := (hG.2.2.2.2.2.2.2.2.2.1 v hv).1
  have hs_lt : mem (dgExtToIntBase gPtr vCap + v) < vCap := hG.2.1 _ hsV
  have hv_lt : v < vCap := hG.2.1 _ hv
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  set s := mem (dgExtToIntBase gPtr vCap + v) with hs
  set heNext := dgHeNextBase gPtr vCap eCap with hheNext
  have htail0 : DllTailAt mem heNext (2 * eCap) L (mem (dgIncHeadBase gPtr vCap + s)) :=
    dllTailAt_of_isDll hdll
  have hLnd : L.Nodup := hdll.1
  have hLlt : ∀ h ∈ L, h < 2 * eCap := hdll.2.1
  have hgw : gPtr < 2 ^ w := by omega
  have hhead_lt : mem (dgIncHeadBase gPtr vCap + s) ≤ 2 * eCap := by
    cases L with
    | nil => simp only [DllTailAt] at htail0; omega
    | cons x xs => obtain ⟨h1, h2, _⟩ := htail0; omega
  -- the loop
  have hloop : Triple w p (CollectInv mem gPtr v par out heNext eCap L L) (.loop (.reg 7) collectBody)
      (normalPost (CollectInv mem gPtr v par out heNext eCap L []))
      (fun _ => (L.map fun _ => 40).sum + L.length * ((Expr.reg 7).size + 1) +
        (Expr.reg 7).size + 1) := by
    refine Triple.loop_list (fun _ => 40) (fun st hInv => ?_) (fun x xs st hInv => ?_) L
    · obtain ⟨pre, hpre, h0, h1, h2, h3, h8, h9, hW, hfr, h7⟩ := hInv
      exact ⟨Expr.eval_reg_of_eq h7, ⟨pre, hpre, h0, h1, h2, h3, h8, h9, hW, hfr, h7⟩⟩
    · obtain ⟨pre, hpre, h0, h1, h2, h3, h8, h9, hW, hfr, h7⟩ := hInv
      obtain ⟨hcur, hxlt, hrest⟩ := h7
      refine ⟨x + 1, Expr.eval_reg_of_eq hcur, by omega, ?_⟩
      intro st' ω' hst'
      subst hst'
      have hWle : (halfEdges par pre).length ≤ eCap :=
        halfEdges_length_le hLnd hLlt hpre
      have hWle' : (halfEdges par (pre ++ [x])).length ≤ eCap :=
        halfEdges_length_le hLnd hLlt (xs := xs) (by simpa using hpre)
      -- the next pointer is in the graph block, outside the written cells
      have hnext_eq : st'.mem (heNext + x) = mem (heNext + x) := by
        refine hfr _ ?_
        by_contra hc
        have hc' : out ≤ heNext + x ∧ heNext + x < out + eCap := by omega
        have := hdisj (heNext + x - out) (by omega)
        simp only [hheNext, dgHeNextBase, dynGraphSize] at this hc'
        omega
      apply runs_start_le
      refine runs_seq_assign_le (v := x) (Expr.eval_sub (Expr.eval_reg_of_eq hcur)
        (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := mem (heNext + x)) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h8])) (Expr.eval_reg_of_eq (by simp))
            (by simp only [hheNext, dgHeNextBase]; omega))
          hnext_eq) ?_
      by_cases hx : x % 2 = par
      · -- write the edge `x / 2`
        refine WordRAM.runs_cond_le (v := 1) (Expr.eval_eq_true (Expr.eval_mod
          (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (by simp [h2])) hx (by omega)) (fun _ => ?_) (fun h => by omega)
        refine runs_seq_store_le (x := out + (halfEdges par pre).length) (v := x / 2)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h3])) (Expr.eval_reg_of_eq (by simp [h9]))
            (by omega))
          (Expr.eval_div (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega)) ?_
        refine runs_assign_le (v := (halfEdges par pre).length + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h9])) (Expr.eval_const (by omega))
            (by omega)) ?_ ?_
        · have hW' : halfEdges par (pre ++ [x]) = halfEdges par pre ++ [x / 2] := by
            rw [halfEdges_append, halfEdges_singleton_of _ _ hx]
          refine ⟨pre ++ [x], by simpa using hpre, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [h0]
          · simp [h1]
          · simp [h2]
          · simp [h3]
          · simp [h8]
          · simp [hW']
          · rw [hW']
            intro i hi
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hi' : i < (halfEdges par pre).length
            · simp only [Function.update_apply, show out + i ≠ out + (halfEdges par pre).length by
                omega, ite_false, List.getElem_append_left hi']
              exact hW i hi'
            · have : i = (halfEdges par pre).length := by omega
              subst this
              simp
          · intro a ha
            rw [hW'] at ha
            simp only [List.length_append, List.length_singleton] at ha
            simp only [Function.update_apply, show a ≠ out + (halfEdges par pre).length by omega,
              ite_false]
            exact hfr a (by omega)
          · simpa using hrest
        · simp only [Expr.size]; omega
      · -- skip the half-edge
        refine WordRAM.runs_cond_le (v := 0) (Expr.eval_eq_false (Expr.eval_mod
          (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (by simp [h2])) hx (by omega)) (fun h => by omega) (fun _ => ?_)
        refine runs_nop_le ?_ ?_
        · have hW' : halfEdges par (pre ++ [x]) = halfEdges par pre := by
            rw [halfEdges_append, halfEdges_singleton_not _ _ hx, List.append_nil]
          refine ⟨pre ++ [x], by simpa using hpre, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [h0]
          · simp [h1]
          · simp [h2]
          · simp [h3]
          · simp [h8]
          · simp [hW', h9]
          · rw [hW']; exact hW
          · rw [hW']; exact hfr
          · simpa using hrest
        · simp only [Expr.size]; omega
  -- the run
  apply runs_start_le
  dsimp only [collectStmt]
  refine runs_seq_assign_le (v := vCap) (Expr.eval_load_of_eq (by eval_expr)
    (by simpa [startState] using hvc)) ?_
  refine runs_seq_assign_le (v := eCap) (Expr.eval_load_of_eq (by eval_expr)
    (by simpa [startState] using hec)) ?_
  refine runs_seq_assign_le (v := s) (Expr.eval_load_of_eq
    (x := dgExtToIntBase gPtr vCap + v) (by simp only [dgExtToIntBase]; eval_expr) rfl) ?_
  refine runs_seq_assign_le (v := mem (dgIncHeadBase gPtr vCap + s)) (Expr.eval_load_of_eq
    (x := dgIncHeadBase gPtr vCap + s) (by simp only [dgIncHeadBase]; eval_expr) rfl) ?_
  refine runs_seq_assign_le (v := heNext)
    (by simp only [hheNext, dgHeNextBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨[], by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, ?_⟩
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp
    · simp [halfEdges]
    · intro i hi; simp [halfEdges] at hi
    · simpa using htail0
  · rintro st ⟨pre, hpre, h0, h1, h2, h3, h8, h9, hW, hfr, _⟩
    rw [List.append_nil] at hpre
    subst hpre
    refine runs_ret_le (Expr.eval_reg_of_eq h9) ⟨gPtr, v, par, out, rfl, halfEdges par pre,
      halfEdges_nodup hLnd, halfEdges_mem_iff hpar heCap hmemL, rfl, hW, hfr⟩ ?_
    simp only [collectContract, List.map_const', List.sum_replicate, smul_eq_mul, Expr.size,
      List.getD_cons_succ, List.getD_cons_zero, ← hlen]
    omega

end MinCostFlow.SparseCore.Program.Read
