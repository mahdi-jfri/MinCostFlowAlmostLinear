module

public import MinCostFlow.ExpanderDecomp.ProgPortGraphBase

import Mathlib.Tactic.Linarith

/-!
# Port Graph Word-RAM Procedure — Stages 2, 3, and 4 (`ProgPortGraphStages`)

Verifies the three linear-time counting/bucketing stages of `portGraphEntry`:
- Stage 2 (`pgOrigAndDeg_triple`): scans `inEdges = G.inside X`, writes `portOwner G X` at
  `outOwnerAddr`, writes `origPortEdges e` at `outGraphAddr + 2`, and counts cloud degrees into
  `curAddr[0..k-1]` (`O(e + 1)`).
- Stage 3 (`pgPrefixSum_triple`): computes prefix sums `cloudOff` into `offAddr[0..k]` and sets
  `curAddr[i] := cloudOff i` (`O(k + 1)`).
- Stage 4 (`pgScatterPorts_triple`): scatters ports `0 .. 2 * e - 1` into `portsAddr`, storing each
  `cloudPortsList G X (verts.getD i 0)` contiguously in strictly increasing port order (`O(e + 1)`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Stage 2 triple: writes `portOwner` for `p < 2 * e`, `origPortEdges e` at `outGraphAddr + 2`,
and counts cloud degrees into `curAddr[0..k-1]`. -/
lemma pgOrigAndDeg_triple {w n k e va ea la oa ga wa h : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (inEdges : List (ℕ × ℕ)) (st₀ : State)
    (hvlen : verts.length = k) (hnd : verts.Nodup)
    (helen : inEdges.length = e)
    (hE_inX : ∀ ed ∈ inEdges, ed.1 ∈ verts ∧ ed.2 ∈ verts)
    (hverts_lt : ∀ u ∈ verts, u < n)
    (hE_at : EdgesAt mem ea inEdges)
    (hloc_map : ∀ u < n, mem (la + u) = if u ∈ verts then verts.idxOf u + 1 else 0)
    (hcur0 : ∀ i < k, mem (wa + k + 2 + i) = 0)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h)
    (hd : PortGraphDisjoint n k e va ea la oa ga wa)
    (hregs : PgRegs k va e ea la oa ga wa h st₀) (hmem : st₀.mem = mem) :
    let X := verts.toFinset
    let G_in := Graph.mk 0 inEdges
    Triple w p (fun st => st = st₀) pgOrigAndDegStmt
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧ st'.pos = st₀.pos ∧
        (∀ a, (a < oa ∨ oa + 2 * e ≤ a) → (a < ga + 2 ∨ ga + 2 + 2 * e ≤ a) →
          (a < wa + k + 2 ∨ wa + 2 * k + 2 ≤ a) → st'.mem a = mem a) ∧
        (∀ q < 2 * e, st'.mem (oa + q) = portOwner G_in X q) ∧
        EdgesAt st'.mem (ga + 2) (origPortEdges e) ∧
        (∀ i < k, st'.mem (wa + k + 2 + i) = (cloudPortsList G_in X (verts.getD i 0)).length))
      (fun _ => 145 * e + 20) := by
  intro X G_in
  rcases hb with ⟨_, hea_h, hla_h, hoa_h, hga_h, hws_h, hhw, hw16⟩
  rcases hd with ⟨_, hd_le, hd_lo, hd_lg, hd_lw, _, hd_oe, hd_og, hd_ow, _, hd_ge, hd_gw, _, hd_we⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  have hinside_eq : G_in.inside X = inEdges := by
    unfold Graph.inside
    exact List.filter_eq_self.mpr fun ed hed => by
      have h12 := hE_inX ed hed
      simp [X, h12.1, h12.2]
  let curAddr := wa + k + 2
  let Inv : ℕ → State → Prop := fun j st =>
    PgRegs k va e ea la oa ga wa h st ∧ st.regs pgI = j ∧ st.pos = st₀.pos ∧
    (∀ a, (a < oa ∨ oa + 2 * e ≤ a) → (a < ga + 2 ∨ ga + 2 + 2 * e ≤ a) →
      (a < curAddr ∨ curAddr + k ≤ a) → st.mem a = mem a) ∧
    (∀ q < 2 * j, st.mem (oa + q) = portOwner G_in X q) ∧
    EdgesAt st.mem (ga + 2) (origPortEdges j) ∧
    (∀ t < k, st.mem (curAddr + t) = (cloudPortsPrefix G_in X (verts.getD t 0) (2 * j)).length)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := pgI) (lo := .const 0) (hi := .reg pgE)
    (body := seqStmts [
      .assign pgU (.load (.bin .add (.reg pgEdges) (.bin .mul (.const 2) (.reg pgI)))),
      .assign pgV (.load (.bin .add (.bin .add (.reg pgEdges) (.bin .mul (.const 2) (.reg pgI))) (.const 1))),
      .store (.bin .add (.reg pgOutOwner) (.bin .mul (.const 2) (.reg pgI))) (.reg pgU),
      .store (.bin .add (.bin .add (.reg pgOutOwner) (.bin .mul (.const 2) (.reg pgI))) (.const 1)) (.reg pgV),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 2)) (.bin .mul (.const 2) (.reg pgI)))
        (.bin .mul (.const 2) (.reg pgI)),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 3)) (.bin .mul (.const 2) (.reg pgI)))
        (.bin .add (.bin .mul (.const 2) (.reg pgI)) (.const 1)),
      .assign pgTmp1 (.bin .sub (.load (.bin .add (.reg pgLoc) (.reg pgU))) (.const 1)),
      .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgTmp1))),
      .store (.bin .add (.reg pgCur) (.reg pgTmp1)) (.bin .add (.reg pgTmp2) (.const 1)),
      .assign pgTmp1 (.bin .sub (.load (.bin .add (.reg pgLoc) (.reg pgV))) (.const 1)),
      .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgTmp1))),
      .store (.bin .add (.reg pgCur) (.reg pgTmp1)) (.bin .add (.reg pgTmp2) (.const 1))])
    (P := fun st => st = st₀) (Inv := Inv) 128 0 e (Nat.zero_le e) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), pgRegs_update_ge (r := pgI) (by decide) hregs,
        by simp, rfl, fun a _ _ _ => by simp [hmem],
        fun q hq => absurd hq (by omega),
        fun t ht => by simp [origPortEdges] at ht,
        fun t ht => by simp [hmem, curAddr, hcur0 t ht, cloudPortsPrefix]⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_e)
    (fun j _ hjlt => by
      intro st ω ⟨hr, hj, hpos, hfr, hown, horig, hdeg⟩
      have hj_len : j < inEdges.length := helen.symm ▸ hjlt
      set ed := inEdges[j]'hj_len
      have hed_m := hE_inX ed (List.getElem_mem hj_len)
      have hu_lt : ed.1 < n := hverts_lt ed.1 hed_m.1
      have hv_lt : ed.2 < n := hverts_lt ed.2 hed_m.2
      set iu := verts.idxOf ed.1
      set iv := verts.idxOf ed.2
      have hiu_lt : iu < k := hvlen ▸ List.idxOf_lt_length_of_mem hed_m.1
      have hiv_lt : iv < k := hvlen ▸ List.idxOf_lt_length_of_mem hed_m.2
      have hpo0 : portOwner G_in X (2 * j) = ed.1 := by
        rw [portOwner_two_mul, hinside_eq, List.getD_eq_getElem _ _ hj_len]
      have hpo1 : portOwner G_in X (2 * j + 1) = ed.2 := by
        rw [portOwner_two_mul_succ, hinside_eq, List.getD_eq_getElem _ _ hj_len]
      have hmem_u : st.mem (ea + 2 * j) = ed.1 := by
        rw [hfr (ea + 2 * j)
          (disjointRange_outside hd_oe (by omega) (by omega))
          (by rcases hd_ge with h1 | h1 <;> [right; left] <;> omega)
          (by rcases hd_we with h1 | h1 <;> [right; left] <;> omega)]
        exact (hE_at j hj_len).1
      have hmem_v : st.mem (ea + 2 * j + 1) = ed.2 := by
        rw [hfr (ea + 2 * j + 1)
          (disjointRange_outside hd_oe (by omega) (by omega))
          (by rcases hd_ge with h1 | h1 <;> [right; left] <;> omega)
          (by rcases hd_we with h1 | h1 <;> [right; left] <;> omega)]
        exact (hE_at j hj_len).2
      have hloc_u : st.mem (la + ed.1) = iu + 1 := by
        rw [hfr (la + ed.1)
          (disjointRange_outside hd_lo.symm (by omega) (by omega))
          (by rcases hd_lg with h1 | h1 <;> [left; right] <;> omega)
          (by rcases hd_lw with h1 | h1 <;> [left; right] <;> omega),
          hloc_map ed.1 hu_lt]
        simp [iu, hed_m.1]
      have hloc_v : st.mem (la + ed.2) = iv + 1 := by
        rw [hfr (la + ed.2)
          (disjointRange_outside hd_lo.symm (by omega) (by omega))
          (by rcases hd_lg with h1 | h1 <;> [left; right] <;> omega)
          (by rcases hd_lw with h1 | h1 <;> [left; right] <;> omega),
          hloc_map ed.2 hv_lt]
        simp [iv, hed_m.2]
      have hdu_val : st.mem (curAddr + iu) = (cloudPortsPrefix G_in X ed.1 (2 * j)).length := by
        rw [hdeg iu hiu_lt, nodup_getD_idxOf hed_m.1]
      have hdu_le : (cloudPortsPrefix G_in X ed.1 (2 * j)).length ≤ 2 * j := by
        calc (cloudPortsPrefix G_in X ed.1 (2 * j)).length
            ≤ (List.range (2 * j)).length := List.length_filter_le _ _
          _ = 2 * j := List.length_range
      have hdv_le : (cloudPortsPrefix G_in X ed.2 (2 * j)).length ≤ 2 * j := by
        calc (cloudPortsPrefix G_in X ed.2 (2 * j)).length
            ≤ (List.range (2 * j)).length := List.length_filter_le _ _
          _ = 2 * j := List.length_range
      refine runs_start_le ?_
      dsimp only [seqStmts]
      -- Load u, v
      refine runs_seq_assign_le (v := ed.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_edges)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hj) (by omega))
            (by omega)) hmem_u) ?_
      refine runs_seq_assign_le (v := ed.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := ea) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_edges]))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hj])) (by omega))
              (by omega))
            (Expr.eval_const (by omega)) (by omega)) hmem_v) ?_
      -- Store portOwner[2*j] := u, portOwner[2*j+1] := v
      refine runs_seq_store_le (x := oa + 2 * j) (v := ed.1)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := oa)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_outOwner]))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := j)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]))
            (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := ed.1) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) ?_
      refine runs_seq_store_le (x := oa + 2 * j + 1) (v := ed.2)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := oa)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_outOwner]))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := j)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]))
              (by omega)) (by omega))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := ed.2) (by simp)) ?_
      -- Store origPortEdges[j] = (2*j, 2*j+1)
      refine runs_seq_store_le (x := ga + 2 + 2 * j) (v := 2 * j)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ga)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_outGraph]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := j)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]))
            (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (v := j)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]))
          (by omega)) ?_
      refine runs_seq_store_le (x := ga + 3 + 2 * j) (v := 2 * j + 1)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ga)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_outGraph]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := j)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]))
            (by omega)) (by omega))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := j)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]))
            (by omega))
          (Expr.eval_const (by omega)) (by omega)) ?_
      let mem4 := Function.update (Function.update (Function.update (Function.update st.mem
        (oa + 2 * j) ed.1) (oa + 2 * j + 1) ed.2) (ga + 2 + 2 * j) (2 * j)) (ga + 3 + 2 * j) (2 * j + 1)
      have hmem4_loc_u : mem4 (la + ed.1) = iu + 1 := by
        dsimp only [mem4]
        rw [Function.update_of_ne (by rcases hd_lg with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_lg with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_lo with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_lo with h1 | h1 <;> omega), hloc_u]
      have hmem4_cur_u : mem4 (curAddr + iu) = (cloudPortsPrefix G_in X ed.1 (2 * j)).length := by
        dsimp only [mem4]
        rw [Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega), hdu_val]
      -- Increment curAddr[iu]
      refine runs_seq_assign_le (v := iu)
        (Expr.eval_eq_of_eq
          (Expr.eval_sub
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_reg_of_eq (v := la)
                  (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_loc]))
                (Expr.eval_reg_of_eq (v := ed.1)
                  (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega))
              hmem4_loc_u)
            (Expr.eval_const (by omega)) (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := (cloudPortsPrefix G_in X ed.1 (2 * j)).length)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := curAddr)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr.r_cur]))
            (Expr.eval_reg_of_eq (v := iu) (by simp)) (by omega))
          hmem4_cur_u) ?_
      refine runs_seq_store_le (x := curAddr + iu)
        (v := (cloudPortsPrefix G_in X ed.1 (2 * j)).length + 1)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := curAddr)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_cur]))
          (Expr.eval_reg_of_eq (v := iu)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq (v := (cloudPortsPrefix G_in X ed.1 (2 * j)).length) (by simp))
          (Expr.eval_const (by omega)) (by omega)) ?_
      let mem5 := Function.update mem4 (curAddr + iu) ((cloudPortsPrefix G_in X ed.1 (2 * j)).length + 1)
      have hmem5_loc_v : mem5 (la + ed.2) = iv + 1 := by
        dsimp only [mem5, mem4]
        rw [Function.update_of_ne (by rcases hd_lw with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_lg with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_lg with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_lo with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_lo with h1 | h1 <;> omega), hloc_v]
      have hmem5_cur_v : mem5 (curAddr + iv) =
          (cloudPortsPrefix G_in X ed.2 (2 * j)).length + (if iu = iv then 1 else 0) := by
        dsimp only [mem5]
        by_cases heq : iu = iv
        · have he12 : ed.1 = ed.2 := by
            have h1 := congrArg (fun idx => verts.getD idx 0) heq
            rw [show verts.getD iu 0 = ed.1 from nodup_getD_idxOf hed_m.1,
              show verts.getD iv 0 = ed.2 from nodup_getD_idxOf hed_m.2] at h1
            exact h1
          rw [heq, Function.update_self, he12]; simp
        · rw [Function.update_of_ne (by omega)]
          dsimp only [mem4]
          rw [Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega),
            hdeg iv hiv_lt, nodup_getD_idxOf hed_m.2,
            ite_eq_right_iff.mpr (fun h => absurd h heq), add_zero]
      -- Increment curAddr[iv]
      refine runs_seq_assign_le (v := iv)
        (Expr.eval_eq_of_eq
          (Expr.eval_sub
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_reg_of_eq (v := la)
                  (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                    Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_loc]))
                (Expr.eval_reg_of_eq (v := ed.2)
                  (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                    Function.update_self])) (by omega))
              hmem5_loc_v)
            (Expr.eval_const (by omega)) (by omega)) (by omega)) ?_
      refine runs_seq_assign_le
        (v := (cloudPortsPrefix G_in X ed.2 (2 * j)).length + (if iu = iv then 1 else 0))
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := curAddr)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr.r_cur]))
            (Expr.eval_reg_of_eq (v := iv) (by simp)) (by omega))
          hmem5_cur_v) ?_
      refine runs_store_le (x := curAddr + iv)
        (v := (cloudPortsPrefix G_in X ed.2 (2 * j)).length + (if iu = iv then 1 else 0) + 1)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := curAddr)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_cur]))
          (Expr.eval_reg_of_eq (v := iv)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega))
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := (cloudPortsPrefix G_in X ed.2 (2 * j)).length + (if iu = iv then 1 else 0))
            (by simp))
          (Expr.eval_const (by omega)) (by split_ifs <;> omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨pgRegs_update_ge (r := pgI) (by decide)
          (pgRegs_update_mem (pgRegs_update_ge (r := pgTmp2) (by decide)
            (pgRegs_update_ge (r := pgTmp1) (by decide)
              (pgRegs_update_mem (pgRegs_update_ge (r := pgTmp2) (by decide)
                (pgRegs_update_ge (r := pgTmp1) (by decide)
                  (pgRegs_update_mem (pgRegs_update_mem (pgRegs_update_mem (pgRegs_update_mem
                    (pgRegs_update_ge (r := pgV) (by decide)
                      (pgRegs_update_ge (r := pgU) (by decide) hr)))))))))))),
        by simp, hpos, ?_, ?_, ?_, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]⟩
      · intro a hao hag hac
        dsimp only [mem5, mem4]
        rw [Function.update_of_ne (by rcases hac with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hac with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hag with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hag with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hao with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hao with h1 | h1 <;> omega)]
        exact hfr a hao hag hac
      · intro q hq
        dsimp only [mem5, mem4]
        rw [Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_og with h1 | h1 <;> omega),
          Function.update_of_ne (by rcases hd_og with h1 | h1 <;> omega)]
        by_cases hq1 : q = 2 * j + 1
        · subst hq1; rw [← Nat.add_assoc, Function.update_self, hpo1]
        · rw [Function.update_of_ne (by omega)]
          by_cases hq0 : q = 2 * j
          · subst hq0; rw [Function.update_self, hpo0]
          · rw [Function.update_of_ne (by omega)]; exact hown q (by omega)
      · intro t ht
        have ht' : t < j + 1 := by simpa [origPortEdges] using ht
        dsimp only [mem5, mem4]
        simp only [origPortEdges, List.getElem_map, List.getElem_range]
        by_cases htj : t = j
        · subst t
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by omega), Function.update_self]
          · rw [show ga + 2 + 2 * j + 1 = ga + 3 + 2 * j by omega,
              Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_self]
        · have ht_lt : t < (origPortEdges j).length := by simp [origPortEdges]; omega
          have h1 := (horig t ht_lt).1
          have h2 := (horig t ht_lt).2
          simp only [origPortEdges, List.getElem_map, List.getElem_range] at h1 h2
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by rcases hd_og with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_og with h1 | h1 <;> omega), h1]
          · rw [Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by rcases hd_og with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_og with h1 | h1 <;> omega), h2]
      · intro t ht
        dsimp only [mem5, mem4]
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega,
          cloudPortsPrefix_succ, cloudPortsPrefix_succ, List.length_append, List.length_append,
          hpo0, hpo1]
        have htu : ed.1 = verts.getD t 0 ↔ iu = t := by
          constructor
          · intro h1; dsimp only [iu]; rw [h1]; exact nodup_idxOf_getD hnd (hvlen.symm ▸ ht)
          · intro h1; rw [← h1]; exact (nodup_getD_idxOf hed_m.1).symm
        have htv : ed.2 = verts.getD t 0 ↔ iv = t := by
          constructor
          · intro h1; dsimp only [iv]; rw [h1]; exact nodup_idxOf_getD hnd (hvlen.symm ▸ ht)
          · intro h1; rw [← h1]; exact (nodup_getD_idxOf hed_m.2).symm
        by_cases htiv : iv = t
        · subst htiv
          rw [Function.update_self, show ed.2 = verts.getD iv 0 from (nodup_getD_idxOf hed_m.2).symm]
          simp only [htu]
          by_cases hiuiv : iu = iv <;> simp [hiuiv]
        · rw [Function.update_of_ne (by omega)]
          by_cases htiu : iu = t
          · subst htiu
            rw [Function.update_self, show ed.1 = verts.getD iu 0 from (nodup_getD_idxOf hed_m.1).symm]
            simp only [htv]
            simp [htiv]
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega),
              Function.update_of_ne (by rcases hd_ow with h1 | h1 <;> omega), hdeg t ht]
            simp only [htu, htv]
            simp [htiu, htiv])
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hpos, hfr, hown, horig, hdeg⟩
    refine ⟨hr, hpos, ?_, hown, horig, fun i hi => ?_⟩
    · intro a hao hag hac
      exact hfr a hao hag (by rcases hac with h1 | h1 <;> [left; right] <;> omega)
    · have h1 := hdeg i hi
      rwa [show 2 * e = 2 * (G_in.inside X).length by rw [hinside_eq, helen],
        cloudPortsPrefix_full] at h1
  · exact False.elim hq

/-- Stage 3 triple: computes `offAddr[0..k]` = `cloudOff` and sets `curAddr[i] := off[i]`. -/
lemma pgPrefixSum_triple {w n k e va ea la oa ga wa h : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (G : Graph) (st₀ : State)
    (hvlen : verts.length = k) (hnd : verts.Nodup)
    (he_eq : (G.inside verts.toFinset).length = e)
    (hcur_deg : ∀ i < k, mem (wa + k + 2 + i) = (cloudPortsList G verts.toFinset (verts.getD i 0)).length)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h)
    (hregs : PgRegs k va e ea la oa ga wa h st₀) (hmem : st₀.mem = mem) :
    let X := verts.toFinset
    Triple w p (fun st => st = st₀) pgPrefixSumStmt
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧ st'.pos = st₀.pos ∧
        MemFrame mem st'.mem (wa + 1) (wa + 2 * k + 2) ∧
        (∀ i ≤ k, st'.mem (wa + 1 + i) = cloudOff verts G X i) ∧
        (∀ i < k, st'.mem (wa + k + 2 + i) = cloudOff verts G X i))
      (fun _ => 60 * k + 30) := by
  intro X
  rcases hb with ⟨_, _, _, _, _, hws_h, hhw, hw16⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  let offAddr := wa + 1
  let curAddr := wa + k + 2
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [pgPrefixSumStmt, seqStmts]
  refine runs_seq_store_le (x := offAddr) (v := 0)
    (Expr.eval_reg_of_eq hregs.r_off) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st1 : State :=
    { mem := Function.update st₀.mem offAddr 0,
      regs := Function.update st₀.regs pgTmp1 0,
      pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun i st =>
    PgRegs k va e ea la oa ga wa h st ∧ st.regs pgI = i ∧ st.pos = st₀.pos ∧
    st.regs pgTmp1 = cloudOff verts G X i ∧
    MemFrame mem st.mem offAddr (wa + 2 * k + 2) ∧
    (∀ t ≤ i, st.mem (offAddr + t) = cloudOff verts G X t) ∧
    (∀ t < i, st.mem (curAddr + t) = cloudOff verts G X t) ∧
    (∀ t, i ≤ t → t < k → st.mem (curAddr + t) = (cloudPortsList G X (verts.getD t 0)).length)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := pgI) (lo := .const 0) (hi := .reg pgK)
    (body := seqStmts [
      .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgI))),
      .store (.bin .add (.reg pgCur) (.reg pgI)) (.reg pgTmp1),
      .assign pgTmp1 (.bin .add (.reg pgTmp1) (.reg pgTmp2)),
      .store (.bin .add (.bin .add (.reg pgOff) (.reg pgI)) (.const 1)) (.reg pgTmp1)])
    (P := fun st => st = st1) (Inv := Inv) 44 0 k (Nat.zero_le k) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega),
        pgRegs_update_ge (r := pgI) (by decide)
          (pgRegs_update_ge (r := pgTmp1) (by decide) (pgRegs_update_mem hregs)),
        by simp, rfl, by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]; rfl,
        hmem ▸ memFrame_update (by omega) (by omega),
        fun t ht => by
          have ht0 : t = 0 := by omega
          subst ht0; simp [st1, cloudOff],
        fun t ht => absurd ht (Nat.not_lt_zero _),
        fun t _ htk => by
          dsimp only [st1]
          rw [Function.update_of_ne (by omega), hmem, hcur_deg t htk]⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hacc, hfr, hoff, hcur_d, hcur_r⟩
      have hd_val : st.mem (curAddr + i) = (cloudPortsList G X (verts.getD i 0)).length :=
        hcur_r i le_rfl hilt
      have hnext_le : cloudOff verts G X (i + 1) ≤ 2 * e := by
        rw [← he_eq]; exact cloudOff_le_two_mul_e hnd G (by omega)
      have hnext_eq : cloudOff verts G X i + (cloudPortsList G X (verts.getD i 0)).length =
          cloudOff verts G X (i + 1) := (cloudOff_succ verts G X i).symm
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := (cloudPortsList G X (verts.getD i 0)).length)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_cur) (Expr.eval_reg_of_eq hi) (by omega))
          hd_val) ?_
      refine runs_seq_store_le (x := curAddr + i) (v := cloudOff verts G X i)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := curAddr) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_cur]))
          (Expr.eval_reg_of_eq (v := i) (by dsimp only; rw [Function.update_of_ne (by decide), hi])) (by omega))
        (Expr.eval_reg_of_eq (v := cloudOff verts G X i)
          (by dsimp only; rw [Function.update_of_ne (by decide), hacc])) ?_
      refine runs_seq_assign_le (v := cloudOff verts G X (i + 1))
        (Expr.eval_eq_of_eq
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := cloudOff verts G X i)
              (by dsimp only; rw [Function.update_of_ne (by decide), hacc]))
            (Expr.eval_reg_of_eq (v := (cloudPortsList G X (verts.getD i 0)).length) (by simp))
            (by omega)) hnext_eq) ?_
      refine runs_store_le (x := offAddr + i + 1) (v := cloudOff verts G X (i + 1))
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := offAddr)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_off]))
            (Expr.eval_reg_of_eq (v := i)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hi])) (by omega))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := cloudOff verts G X (i + 1)) (by simp)) ?_
        (by simp [Expr.size])
      refine ⟨⟨pgRegs_update_ge (r := pgI) (by decide)
          (pgRegs_update_mem (pgRegs_update_ge (r := pgTmp1) (by decide)
            (pgRegs_update_mem (pgRegs_update_ge (r := pgTmp2) (by decide) hr)))),
        by simp, hpos,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self],
        memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
          (memFrame_update (by omega) (by omega))), ?_, ?_, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hi]⟩
      · intro t ht
        dsimp only
        by_cases hti : t = i + 1
        · subst hti
          rw [show offAddr + (i + 1) = offAddr + i + 1 by omega, Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hoff t (by omega)
      · intro t ht
        dsimp only
        rw [Function.update_of_ne (by omega)]
        by_cases hti : t = i
        · subst hti; rw [Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hcur_d t (by omega)
      · intro t hti htk
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hcur_r t (by omega) htk)
  rcases hloop st1 ω rfl with ⟨o, st', c, hr, hq, hc⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hr', _, hpos', _, hfr', hoff', hcur_d', _⟩
    exact ⟨.normal, st', c, hr, ⟨hr', hpos', hfr', hoff', hcur_d'⟩, by simp [Expr.size] at hc ⊢; omega⟩

/-- Stage 4 triple: scatters ports `0 .. 2 * e - 1` into `portsAddr` in exact `cloudPortsList` order. -/
lemma pgScatterPorts_triple {w n k e va ea la oa ga wa h : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (G : Graph) (st₀ : State)
    (hvlen : verts.length = k) (hnd : verts.Nodup)
    (he_eq : (G.inside verts.toFinset).length = e)
    (hverts_lt : ∀ u ∈ verts, u < n)
    (hloc_map : ∀ u < n, mem (la + u) = if u ∈ verts then verts.idxOf u + 1 else 0)
    (hown_at : ∀ q < 2 * e, mem (oa + q) = portOwner G verts.toFinset q)
    (hcur_off : ∀ i < k, mem (wa + k + 2 + i) = cloudOff verts G verts.toFinset i)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h)
    (hd : PortGraphDisjoint n k e va ea la oa ga wa)
    (hregs : PgRegs k va e ea la oa ga wa h st₀) (hmem : st₀.mem = mem) :
    let X := verts.toFinset
    Triple w p (fun st => st = st₀) pgScatterPortsStmt
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧ st'.pos = st₀.pos ∧
        MemFrame mem st'.mem (wa + k + 2) (wa + 2 * k + 2 + 2 * e) ∧
        (∀ i < k, ListAt st'.mem (wa + 2 * k + 2 + cloudOff verts G X i)
          (cloudPortsList G X (verts.getD i 0))))
      (fun _ => 130 * e + 20) := by
  intro X
  rcases hb with ⟨_, _, hla_h, hoa_h, _, hws_h, hhw, hw16⟩
  rcases hd with ⟨_, _, _, _, hd_lw, _, _, _, hd_ow, _, _, _, _, _⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  let curAddr := wa + k + 2
  let portsAddr := wa + 2 * k + 2
  let Inv : ℕ → State → Prop := fun q st =>
    PgRegs k va e ea la oa ga wa h st ∧ st.regs pgI = q ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem curAddr (portsAddr + 2 * e) ∧
    (∀ t < k, st.mem (curAddr + t) =
      cloudOff verts G X t + (cloudPortsPrefix G X (verts.getD t 0) q).length) ∧
    (∀ t < k, ListAt st.mem (portsAddr + cloudOff verts G X t)
      (cloudPortsPrefix G X (verts.getD t 0) q))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := pgI)
    (lo := .const 0) (hi := .bin .mul (.const 2) (.reg pgE))
    (body := seqStmts [
      .assign pgV (.load (.bin .add (.reg pgOutOwner) (.reg pgI))),
      .assign pgTmp1 (.bin .sub (.load (.bin .add (.reg pgLoc) (.reg pgV))) (.const 1)),
      .assign pgTmp2 (.load (.bin .add (.reg pgCur) (.reg pgTmp1))),
      .store (.bin .add (.reg pgPorts) (.reg pgTmp2)) (.reg pgI),
      .store (.bin .add (.reg pgCur) (.reg pgTmp1)) (.bin .add (.reg pgTmp2) (.const 1))])
    (P := fun st => st = st₀) (Inv := Inv) 50 0 (2 * e) (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), pgRegs_update_ge (r := pgI) (by decide) hregs,
        by simp, rfl, hmem ▸ memFrame_refl _ _ _,
        fun t ht => by dsimp only [X]; simp [hmem, curAddr, hcur_off t ht, cloudPortsPrefix],
        fun t _ j hj => by simp [cloudPortsPrefix] at hj⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv =>
      Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hInv.1.r_e) (by omega))
    (fun q _ hqlt => by
      intro st ω ⟨hr, hq, hpos, hfr, hcur, hpts⟩
      set v := portOwner G X q
      have hvX : v ∈ X := portOwner_mem (he_eq.symm ▸ hqlt)
      have hvm : v ∈ verts := List.mem_toFinset.mp hvX
      have hv_lt : v < n := hverts_lt v hvm
      set iv := verts.idxOf v
      have hiv_lt : iv < k := hvlen ▸ List.idxOf_lt_length_of_mem hvm
      have hv_getD : verts.getD iv 0 = v := nodup_getD_idxOf hvm
      have hmem_v : st.mem (oa + q) = v := by
        rw [hfr (oa + q) (by rcases hd_ow with h1 | h1 <;> [left; right] <;> omega)]
        exact hown_at q hqlt
      have hloc_v : st.mem (la + v) = iv + 1 := by
        rw [hfr (la + v) (by rcases hd_lw with h1 | h1 <;> [left; right] <;> omega),
          hloc_map v hv_lt]
        simp [iv, hvm]
      set posQ := cloudOff verts G X iv + (cloudPortsPrefix G X v q).length
      have hcur_iv : st.mem (curAddr + iv) = posQ := by
        rw [hcur iv hiv_lt, hv_getD]
      have hpref_lt : (cloudPortsPrefix G X v q).length < (cloudPortsList G X v).length := by
        have h1 : (cloudPortsPrefix G X v (q + 1)).length ≤ (cloudPortsList G X v).length := by
          rw [← cloudPortsPrefix_full, he_eq]
          exact cloudPortsPrefix_length_le G X v (by omega)
        rw [cloudPortsPrefix_succ] at h1
        have hv_eq : portOwner G X q = v := rfl
        rw [hv_eq] at h1
        simp only [↓reduceIte, List.length_append, List.length_singleton] at h1
        omega
      have hposQ_lt : posQ < 2 * e := by
        have h1 : cloudOff verts G X (iv + 1) ≤ 2 * e := by
          rw [← he_eq]; exact cloudOff_le_two_mul_e hnd G (by omega)
        rw [cloudOff_succ, hv_getD] at h1
        omega
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := v)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_outOwner) (Expr.eval_reg_of_eq hq) (by omega))
          hmem_v) ?_
      refine runs_seq_assign_le (v := iv)
        (Expr.eval_eq_of_eq
          (Expr.eval_sub
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_reg_of_eq (v := la) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_loc]))
                (Expr.eval_reg_of_eq (v := v) (by simp)) (by omega))
              hloc_v)
            (Expr.eval_const (by omega)) (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := posQ)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := curAddr)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_cur]))
            (Expr.eval_reg_of_eq (v := iv) (by simp)) (by omega))
          hcur_iv) ?_
      refine runs_seq_store_le (x := portsAddr + posQ) (v := q)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := portsAddr)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), hr.r_ports]))
          (Expr.eval_reg_of_eq (v := posQ) (by simp)) (by omega))
        (Expr.eval_reg_of_eq (v := q)
          (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hq])) ?_
      refine runs_store_le (x := curAddr + iv) (v := posQ + 1)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := curAddr)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), hr.r_cur]))
          (Expr.eval_reg_of_eq (v := iv)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq (v := posQ) (by simp))
          (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨pgRegs_update_ge (r := pgI) (by decide)
          (pgRegs_update_mem (pgRegs_update_mem
            (pgRegs_update_ge (r := pgTmp2) (by decide)
              (pgRegs_update_ge (r := pgTmp1) (by decide)
                (pgRegs_update_ge (r := pgV) (by decide) hr))))),
        by simp, hpos,
        memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
          (memFrame_update (by omega) (by omega))), ?_, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hq]⟩
      · intro t ht
        dsimp only
        rw [cloudPortsPrefix_succ]
        have htv : portOwner G X q = verts.getD t 0 ↔ iv = t := by
          constructor
          · intro h1; dsimp only [iv, v]; rw [h1]; exact nodup_idxOf_getD hnd (hvlen.symm ▸ ht)
          · intro h1; rw [← h1]; exact hv_getD.symm
        by_cases htiv : iv = t
        · subst htiv
          rw [Function.update_self, htv.mpr rfl]
          dsimp only [posQ]; rw [hv_getD]; simp; omega
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            ite_eq_right_iff.mpr (fun h1 => absurd (htv.mp h1) htiv), List.append_nil]
          exact hcur t ht
      · intro t ht j hj
        dsimp only
        have htv : portOwner G X q = verts.getD t 0 ↔ iv = t := by
          constructor
          · intro h1; dsimp only [iv, v]; rw [h1]; exact nodup_idxOf_getD hnd (hvlen.symm ▸ ht)
          · intro h1; rw [← h1]; exact hv_getD.symm
        rw [Function.update_of_ne (by omega)]
        by_cases htiv : iv = t
        · subst htiv
          have hsucc : cloudPortsPrefix G X (verts.getD iv 0) (q + 1) =
              cloudPortsPrefix G X (verts.getD iv 0) q ++ [q] := by
            rw [cloudPortsPrefix_succ, ite_eq_left_iff.mpr (fun h1 => absurd (htv.mpr rfl) h1)]
          have hj' : j < (cloudPortsPrefix G X (verts.getD iv 0) q).length + 1 := by
            have := hj; rw [hsucc, List.length_append, List.length_singleton] at this; exact this
          by_cases hjeq : j = (cloudPortsPrefix G X (verts.getD iv 0) q).length
          · subst hjeq
            have haddr : portsAddr + cloudOff verts G X iv +
                (cloudPortsPrefix G X (verts.getD iv 0) q).length = portsAddr + posQ := by
              dsimp only [posQ]; rw [hv_getD]; omega
            rw [haddr, Function.update_self]
            simp only [hsucc]
            rw [List.getElem_append_right (le_refl _)]
            simp
          · have hjlt : j < (cloudPortsPrefix G X (verts.getD iv 0) q).length := by omega
            have hne_pos : portsAddr + cloudOff verts G X iv + j ≠ portsAddr + posQ := by
              dsimp only [posQ]; rw [← hv_getD]; omega
            rw [Function.update_of_ne hne_pos]
            have hget : (cloudPortsPrefix G X (verts.getD iv 0) (q + 1))[j]'hj =
                (cloudPortsPrefix G X (verts.getD iv 0) q)[j]'hjlt := by
              simp only [hsucc]; exact List.getElem_append_left hjlt
            rw [hget]
            exact hpts iv ht j hjlt
        · have hsucc : cloudPortsPrefix G X (verts.getD t 0) (q + 1) =
              cloudPortsPrefix G X (verts.getD t 0) q := by
            rw [cloudPortsPrefix_succ,
              ite_eq_right_iff.mpr (fun h1 => absurd (htv.mp h1) htiv), List.append_nil]
          have hjlt : j < (cloudPortsPrefix G X (verts.getD t 0) q).length := by
            have := hj; rw [hsucc] at this; exact this
          have hpos_ne : cloudOff verts G X t + j ≠ posQ := by
            have hj_le_full : (cloudPortsPrefix G X (verts.getD t 0) q).length ≤
                (cloudPortsList G X (verts.getD t 0)).length := by
              rw [← cloudPortsPrefix_full, he_eq]
              exact cloudPortsPrefix_length_le G X _ (by omega)
            rcases lt_or_gt_of_ne htiv with hlt | hgt
            · have h1 := cloudOff_succ verts G X iv
              have h2 := cloudOff_mono verts G X (show iv + 1 ≤ t by omega)
              rw [hv_getD] at h1
              omega
            · have h1 := cloudOff_succ verts G X t
              have h2 := cloudOff_mono verts G X (show t + 1 ≤ iv by omega)
              omega
          rw [Function.update_of_ne (by omega)]
          have hget : (cloudPortsPrefix G X (verts.getD t 0) (q + 1))[j]'hj =
              (cloudPortsPrefix G X (verts.getD t 0) q)[j]'hjlt := by
            simp only [hsucc]
          rw [hget]
          exact hpts t ht j hjlt)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hpos, hfr, _, hpts⟩
    refine ⟨hr, hpos, hfr, fun i hi => ?_⟩
    have h1 := hpts i hi
    rwa [← he_eq, cloudPortsPrefix_full] at h1
  · exact False.elim hq

end MinCostFlow.ExpanderDecomp
