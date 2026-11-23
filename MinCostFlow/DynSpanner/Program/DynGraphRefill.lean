module

public import MinCostFlow.DynSpanner.Program.DynGraphRefillClear
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop
import MinCostFlow.DynSpanner.Program.DynGraphInsert
import WordRAM.Tactic

/-!
# Verification of `dgFillEmptyFromLists` and `dgRefillFromLists` (`DynGraphRefill`)

Proves:
* `dgFillEmptyFromLists_meetsContract`: populates an empty `DynGraphAt` from disjoint vertex and
  edge-triple lists in `O(V_len + E_len + 1)` steps.
* `dgRefillFromLists_meetsContract` and `dgRefillModule_meetsContract`: full in-place refill in
  `O(G_old.n + G_old.m + V_len + E_len + 1)` steps with zero scratch.
* `dgRefillFromLists_pre_nonvacuous`: concrete witness showing the precondition is satisfiable.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

/-! ## Helpers for `dgFillEmptyFromLists` -/

private def refillAddVStep (H : MGraph) (v : ℕ) : MGraph :=
  { V := insert v H.V, E := H.E, tail := H.tail, head := H.head }

private def refillAddEStep (H : MGraph) (t : ℕ × ℕ × ℕ) : MGraph :=
  H.applyUpdate (.insert t.1 t.2.1 t.2.2)

private lemma refill_foldl_addV_V :
    ∀ (vs : List ℕ) (H : MGraph) (v : ℕ),
      v ∈ (vs.foldl refillAddVStep H).V ↔ v ∈ H.V ∨ v ∈ vs
  | [], _, _ => by simp
  | u :: us, H, v => by
    simp only [List.foldl_cons, refill_foldl_addV_V, List.mem_cons]
    have hV : (refillAddVStep H u).V = insert u H.V := rfl
    rw [hV, Finset.mem_insert]
    tauto

private lemma refill_foldl_addV_E :
    ∀ (vs : List ℕ) (H : MGraph),
      (vs.foldl refillAddVStep H).E = H.E
  | [], _ => rfl
  | u :: us, H => by
    simpa [List.foldl_cons, refillAddVStep] using refill_foldl_addV_E us (refillAddVStep H u)

private lemma refill_foldl_addEStep_V :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph),
      (es.foldl refillAddEStep H).V = H.V
  | [], _ => rfl
  | t :: ts, H => by
    simpa [List.foldl_cons, refillAddEStep, MGraph.applyUpdate] using
      refill_foldl_addEStep_V ts (refillAddEStep H t)

private lemma refill_foldl_addEStep_E :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph) (e : ℕ),
      e ∈ (es.foldl refillAddEStep H).E ↔ e ∈ H.E ∨ ∃ t ∈ es, t.1 = e
  | [], H, e => by simp
  | t :: ts, H, e => by
    simp only [List.foldl_cons, refill_foldl_addEStep_E, List.mem_cons]
    have hE : (refillAddEStep H t).E = insert t.1 H.E := rfl
    rw [hE, Finset.mem_insert]
    constructor
    · rintro ((rfl | heH) | ⟨t', ht', rfl⟩)
      · exact Or.inr ⟨t, Or.inl rfl, rfl⟩
      · exact Or.inl heH
      · exact Or.inr ⟨t', Or.inr ht', rfl⟩
    · rintro (heH | ⟨t', rfl | ht', rfl⟩)
      · exact Or.inl (Or.inr heH)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨t', ht', rfl⟩

private lemma refill_foldl_addEStep_preserve :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph) (e : ℕ),
      (∀ y ∈ es, y.1 ≠ e) →
      (es.foldl refillAddEStep H).tail e = H.tail e ∧
      (es.foldl refillAddEStep H).head e = H.head e
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: xs, H, e, hne => by
    have hx_ne : x.1 ≠ e := hne x List.mem_cons_self
    have hxs_ne : ∀ y ∈ xs, y.1 ≠ e := fun y hy => hne y (List.mem_cons_of_mem _ hy)
    have ih := refill_foldl_addEStep_preserve xs (refillAddEStep H x) e hxs_ne
    have ht : (refillAddEStep H x).tail e = H.tail e := by
      simp [refillAddEStep, MGraph.applyUpdate, hx_ne.symm]
    have hh : (refillAddEStep H x).head e = H.head e := by
      simp [refillAddEStep, MGraph.applyUpdate, hx_ne.symm]
    exact ⟨ih.1.trans ht, ih.2.trans hh⟩

private lemma refill_foldl_addEStep_ends :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph) (t : ℕ × ℕ × ℕ),
      t ∈ es →
      (es.map Prod.fst).Nodup →
      (es.foldl refillAddEStep H).tail t.1 = t.2.1 ∧
      (es.foldl refillAddEStep H).head t.1 = t.2.2
  | [], _, _, ht, _ => absurd ht List.not_mem_nil
  | x :: xs, H, t, ht, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases hnd with ⟨hx_not, hxs_nd⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ht with rfl | ht_xs
    · have hne : ∀ y ∈ xs, y.1 ≠ t.1 := fun y hy hc =>
        hx_not (List.mem_map.mpr ⟨y, hy, hc⟩)
      have hp := refill_foldl_addEStep_preserve xs (refillAddEStep H t) t.1 hne
      have ht0 : (refillAddEStep H t).tail t.1 = t.2.1 := by
        simp [refillAddEStep, MGraph.applyUpdate]
      have hh0 : (refillAddEStep H t).head t.1 = t.2.2 := by
        simp [refillAddEStep, MGraph.applyUpdate]
      exact ⟨hp.1.trans ht0, hp.2.trans hh0⟩
    · exact refill_foldl_addEStep_ends xs (refillAddEStep H x) t ht_xs hxs_nd

private lemma refill_take_nodup_map {α β : Type*} (f : α → β) :
    ∀ (k : ℕ) (L : List α), (L.map f).Nodup → ((L.take k).map f).Nodup
  | 0, _, _ => by simp
  | _ + 1, [], _ => by simp
  | k + 1, x :: xs, hnd => by
    simp only [List.take_succ_cons, List.map_cons, List.nodup_cons] at hnd ⊢
    refine ⟨fun hc => hnd.1 ?_, refill_take_nodup_map f k xs hnd.2⟩
    rcases List.mem_map.mp hc with ⟨y, hy, hyf⟩
    exact List.mem_map.mpr ⟨y, List.mem_of_mem_take hy, hyf⟩

private lemma refill_nodup_getElem_not_mem_take {α β : Type*} (f : α → β)
    {L : List α} {k : ℕ} (hk : k < L.length) (hnd : (L.map f).Nodup) :
    ∀ t ∈ L.take k, f t ≠ f L[k] := by
  intro t ht hc
  have hnd1 : ((L.take (k + 1)).map f).Nodup := refill_take_nodup_map f (k + 1) L hnd
  rw [List.take_succ_eq_append_getElem hk, List.map_append, List.map_cons, List.map_nil] at hnd1
  have hdisj := List.nodup_append'.mp hnd1
  exact hdisj.2.2 (List.mem_map.mpr ⟨t, ht, hc⟩) List.mem_cons_self

/-! ## Verification of `dgFillEmptyFromListsStmt` -/

/-- `dgFillEmptyFromListsStmt` fills an empty `DynGraphAt` from disjoint vertex and edge-triple
lists in `O(V_len + E_len + 1)` steps. -/
theorem dgFillEmptyFromLists_meetsContract {w : ℕ} {p : Program}
    {bOps bEdge bRefill vCap eCap : ℕ} {G : MGraph} {vL : List ℕ}
    {eEdges : List (ℕ × ℕ × ℕ)}
    (hp : p.HasAt bRefill (dgRefillProcs bOps bEdge bRefill))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bRefill + dgIdxFillEmptyFromLists)
      (dgFillEmptyFromListsContract w vCap eCap G vL eEdges) := by
  refine meetsContract_of_runs
    (hp.get (i := dgIdxFillEmptyFromLists) (by simp [dgRefillProcs, dgIdxFillEmptyFromLists]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, hw16, hbound, hG0,
    hG_val, hvCap, heCap, hvL_len, hvL_at, hvL_mem, hV_bound, hV_disj,
    heL_len, heNd, heL_at, heL_spec, heL_cov, hE_bound, hE_disj⟩
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_vc : vCap < 2 ^ w := by dsimp [dynGraphSize] at hbound; omega
  have hlt_ec : eCap < 2 ^ w := by dsimp [dynGraphSize] at hbound; omega
  have hlt_Vl : V_len < 2 ^ w := hargs V_len (by simp)
  have hlt_Vp : V_ptr < 2 ^ w := hargs V_ptr (by simp)
  have hlt_El : E_len < 2 ^ w := hargs E_len (by simp)
  have hlt_Ep : E_ptr < 2 ^ w := hargs E_ptr (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgRefillProcs, dgIdxFillEmptyFromLists, List.getElem_cons_succ,
    List.getElem_cons_zero, dgFillEmptyFromListsStmt]
  let PV : State → Prop := fun st =>
    st.regs 0 = gPtr ∧ st.regs 1 = V_len ∧ st.regs 2 = V_ptr ∧
    st.regs 3 = E_len ∧ st.regs 4 = E_ptr ∧
    DynGraphAt st.mem gPtr vCap eCap dgEmptyGraph ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let InvV : ℕ → State → Prop := fun k st =>
    k ≤ V_len ∧
    st.regs 0 = gPtr ∧ st.regs 1 = V_len ∧ st.regs 2 = V_ptr ∧
    st.regs 3 = E_len ∧ st.regs 4 = E_ptr ∧ st.regs 5 = k ∧
    DynGraphAt st.mem gPtr vCap eCap ((vL.take k).foldl refillAddVStep dgEmptyGraph) ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let bodyV : Stmt :=
    .assign 6 (.load (.bin .add (.reg 2) (.reg 5))) ;;
    .call 7 (bOps + dgIdxAddVertex) [.reg 0, .reg 6]
  have hLoopV : Triple w p PV (forRange 5 (.const 0) (.reg 1) bodyV) (normalPost (InvV V_len))
      (fun _ => (V_len - 0) * (119 + Expr.size (.reg 1) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 1) + 5)) := by
    refine Triple.forRange_const 119 0 V_len (Nat.zero_le _) h1_lt (fun _ => hlt_Vl)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h3, h4, hG, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
            by simp, by simpa using hG, hfr⟩⟩)
      (fun k st _ _ hk => hk.2.2.2.2.2.2.1)
      (fun k st _ _ hk => by simp [Expr.eval, hk.2.2.1])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hGk, hfrk⟩
        have hlt_Vp_k : V_ptr + k < 2 ^ w := by omega
        have hk_vL : k < vL.length := hvL_len.symm ▸ hk_lt
        have hvk_mem : st.mem (V_ptr + k) = vL[k] := by
          rw [hfrk _ (hV_disj k hk_lt)]
          exact hvL_at k hk_vL
        have hvk_cap : vL[k] < vCap := hvCap vL[k] ((hvL_mem vL[k]).mp (List.getElem_mem hk_vL))
        have hvk_ltw : vL[k] < 2 ^ w := lt_trans hvk_cap hlt_vc
        suffices h : ∃ o st₁ c, Runs w p ω' bodyV st o st₁ c ∧
            (normalPost fun st₁ =>
              InvV (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 5 (k + 1), pos := st₁.pos } ∧
                st₁.regs 5 = k) o st₁ ∧
            0 + c ≤ 119 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyV]
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := vL[k])
          (by simp [Expr.eval, BinOp.eval, hr2, hr5, hlt_Vp_k]) hvk_mem) ?_
        let stA : State := { mem := st.mem, regs := Function.update st.regs 6 vL[k], pos := st.pos }
        have hpre_v : (dgAddVertexContract w vCap eCap _).pre [gPtr, vL[k]] stA.mem :=
          ⟨gPtr, vL[k], rfl, hw16, hbound, hvk_cap, hGk⟩
        have hargs_eval_v : evalArgs w stA [Expr.reg 0, Expr.reg 6] = some [gPtr, vL[k]] := by
          simp [stA, evalArgs, Expr.eval, hr0]
        rcases runs_call_of_meetsContract (r := 7) (dgAddVertex_meetsContract hpOps)
          hargs_eval_v
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl) <;> assumption)
          hpre_v ω'
          with ⟨st₁, c_call, ret, hruns_call, hpost_call, _, hregs_call, hcost_call⟩
        rcases hpost_call with ⟨_, _, hEqv, _, hGk1, hfrv⟩
        simp only [List.cons.injEq, and_true] at hEqv
        rcases hEqv with ⟨hva, hvb⟩
        subst hva hvb
        refine ⟨.normal, st₁, c_call, hruns_call, ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · exact (hregs_call 0 (by decide)).trans (by simp [stA, hr0])
        · exact (hregs_call 1 (by decide)).trans (by simp [stA, hr1])
        · exact (hregs_call 2 (by decide)).trans (by simp [stA, hr2])
        · exact (hregs_call 3 (by decide)).trans (by simp [stA, hr3])
        · exact (hregs_call 4 (by decide)).trans (by simp [stA, hr4])
        · simp
        · rw [List.take_succ_eq_append_getElem hk_vL, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact hGk1
        · intro addr hout
          exact (hfrv addr hout).trans (hfrk addr hout)
        · exact (hregs_call 5 (by decide)).trans (by simp [stA, hr5])
        · dsimp only [dgAddVertexContract, argsSize, Expr.size] at hcost_call ⊢
          omega)
  refine runs_seq_triple_le hLoopV ?_ ?_
  · refine ⟨by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], hG0, fun _ _ => rfl⟩
  intro stV ⟨_, hr0V, hr1V, hr2V, hr3V, hr4V, _, hGV, hfrV⟩
  let baseV : MGraph := vL.foldl refillAddVStep dgEmptyGraph
  have hGV' : DynGraphAt stV.mem gPtr vCap eCap baseV := by
    simpa [baseV, List.take_of_length_le hvL_len.le] using hGV
  have hbaseV_V : ∀ v, v ∈ baseV.V ↔ v ∈ G.V := fun v => by
    simpa [baseV, dgEmptyGraph, refill_foldl_addV_V] using hvL_mem v
  have hbaseV_E : baseV.E = ∅ := refill_foldl_addV_E vL dgEmptyGraph
  let PE : State → Prop := fun st =>
    st.regs 0 = gPtr ∧ st.regs 1 = V_len ∧ st.regs 2 = V_ptr ∧
    st.regs 3 = E_len ∧ st.regs 4 = E_ptr ∧
    DynGraphAt st.mem gPtr vCap eCap baseV ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let InvE : ℕ → State → Prop := fun k st =>
    k ≤ E_len ∧
    st.regs 0 = gPtr ∧ st.regs 1 = V_len ∧ st.regs 2 = V_ptr ∧
    st.regs 3 = E_len ∧ st.regs 4 = E_ptr ∧ st.regs 5 = k ∧
    DynGraphAt st.mem gPtr vCap eCap ((eEdges.take k).foldl refillAddEStep baseV) ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let bodyE : Stmt :=
    .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 5))) ;;
    .assign 7 (.load (.reg 6)) ;;
    .assign 8 (.load (.bin .add (.reg 6) (.const 1))) ;;
    .assign 9 (.load (.bin .add (.reg 6) (.const 2))) ;;
    .call 10 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 7, .reg 8, .reg 9]
  have hLoopE : Triple w p PE (forRange 5 (.const 0) (.reg 3) bodyE) (normalPost (InvE E_len))
      (fun _ => (E_len - 0) * (478 + Expr.size (.reg 3) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 3) + 5)) := by
    refine Triple.forRange_const 478 0 E_len (Nat.zero_le _) h1_lt (fun _ => hlt_El)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h3, h4, hG, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
            by simp, by simpa using hG, hfr⟩⟩)
      (fun k st _ _ hk => hk.2.2.2.2.2.2.1)
      (fun k st _ _ hk => by simp [Expr.eval, hk.2.2.2.2.1])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hGk, hfrk⟩
        have hk_eL : k < eEdges.length := heL_len.symm ▸ hk_lt
        let t := eEdges[k]
        have hlt_3k : 3 * k < 2 ^ w := by omega
        have hlt_Ep_3k0 : E_ptr + 3 * k < 2 ^ w := by omega
        have hlt_Ep_3k1 : E_ptr + 3 * k + 1 < 2 ^ w := by omega
        have hlt_Ep_3k2 : E_ptr + 3 * k + 2 < 2 ^ w := by omega
        rcases heL_at k hk_eL with ⟨hm0, hm1, hm2⟩
        have ht0_mem : st.mem (E_ptr + 3 * k) = t.1 := by
          rw [hfrk _ (hE_disj (3 * k) (by omega))]
          exact hm0
        have ht1_mem : st.mem (E_ptr + 3 * k + 1) = t.2.1 := by
          rw [Nat.add_assoc E_ptr (3 * k) 1, hfrk _ (hE_disj (3 * k + 1) (by omega)), ← Nat.add_assoc]
          exact hm1
        have ht2_mem : st.mem (E_ptr + 3 * k + 2) = t.2.2 := by
          rw [Nat.add_assoc E_ptr (3 * k) 2, hfrk _ (hE_disj (3 * k + 2) (by omega)), ← Nat.add_assoc]
          exact hm2
        rcases heL_spec t (List.getElem_mem hk_eL) with ⟨he_G, hu_eq, hv_eq⟩
        have he_cap : t.1 < eCap := heCap t.1 he_G
        have hu_V : t.2.1 ∈ G.V := hu_eq ▸ (hG_val t.1 he_G).1
        have hv_V : t.2.2 ∈ G.V := hv_eq ▸ (hG_val t.1 he_G).2
        have hlt_e : t.1 < 2 ^ w := lt_trans he_cap hlt_ec
        have hlt_u : t.2.1 < 2 ^ w := lt_trans (hvCap t.2.1 hu_V) hlt_vc
        have hlt_v : t.2.2 < 2 ^ w := lt_trans (hvCap t.2.2 hv_V) hlt_vc
        have hu_Gk : t.2.1 ∈ ((eEdges.take k).foldl refillAddEStep baseV).V := by
          rw [refill_foldl_addEStep_V]; exact (hbaseV_V _).mpr hu_V
        have hv_Gk : t.2.2 ∈ ((eEdges.take k).foldl refillAddEStep baseV).V := by
          rw [refill_foldl_addEStep_V]; exact (hbaseV_V _).mpr hv_V
        have he_not_Gk : t.1 ∉ ((eEdges.take k).foldl refillAddEStep baseV).E := by
          rw [refill_foldl_addEStep_E, hbaseV_E]
          rintro (hc | ⟨y, hy, hyf⟩)
          · cases hc
          · exact refill_nodup_getElem_not_mem_take Prod.fst hk_eL heNd y hy hyf
        suffices h : ∃ o st₁ c, Runs w p ω' bodyE st o st₁ c ∧
            (normalPost fun st₁ =>
              InvE (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 5 (k + 1), pos := st₁.pos } ∧
                st₁.regs 5 = k) o st₁ ∧
            0 + c ≤ 478 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyE]
        refine runs_seq_assign_le (v := E_ptr + 3 * k)
          (by simp [Expr.eval, BinOp.eval, h3_lt, hr4, hr5, hlt_3k, hlt_Ep_3k0]) ?_
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := t.1) (by eval_expr) ht0_mem) ?_
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := t.2.1)
          (by simp [Expr.eval, BinOp.eval, h1_lt, hlt_Ep_3k1]) ht1_mem) ?_
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := t.2.2)
          (by simp [Expr.eval, BinOp.eval, h2_lt, hlt_Ep_3k2]) ht2_mem) ?_
        let stE : State := {
          mem := st.mem,
          regs := Function.update (Function.update (Function.update (Function.update st.regs
            6 (E_ptr + 3 * k)) 7 t.1) 8 t.2.1) 9 t.2.2,
          pos := st.pos }
        have hpre_e : (dgInsertEdgeContract w vCap eCap _).pre [gPtr, t.1, t.2.1, t.2.2] stE.mem :=
          ⟨gPtr, t.1, t.2.1, t.2.2, rfl, hw16, hbound, hu_Gk, hv_Gk, hGk⟩
        have hargs_eval_e : evalArgs w stE [Expr.reg 0, Expr.reg 7, Expr.reg 8, Expr.reg 9] =
            some [gPtr, t.1, t.2.1, t.2.2] := by
          simp [stE, evalArgs, Expr.eval, hr0]
        rcases runs_call_of_meetsContract (r := 10) (dgInsertEdge_meetsContract hpEdge hpOps)
          hargs_eval_e
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl|rfl) <;> assumption)
          hpre_e ω'
          with ⟨st₁, c_call, ret, hruns_call, hpost_call, _, hregs_call, hcost_call⟩
        rcases hpost_call with ⟨_, _, _, _, hEqe, _, hGk1, hfre⟩
        simp only [List.cons.injEq, and_true] at hEqe
        rcases hEqe with ⟨hea, heb, hec, hed⟩
        subst hea heb hec hed
        refine ⟨.normal, st₁, c_call, hruns_call, ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · exact (hregs_call 0 (by decide)).trans (by simp [stE, hr0])
        · exact (hregs_call 1 (by decide)).trans (by simp [stE, hr1])
        · exact (hregs_call 2 (by decide)).trans (by simp [stE, hr2])
        · exact (hregs_call 3 (by decide)).trans (by simp [stE, hr3])
        · exact (hregs_call 4 (by decide)).trans (by simp [stE, hr4])
        · simp
        · simp only [he_cap, he_not_Gk] at hGk1
          rw [List.take_succ_eq_append_getElem hk_eL, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact hGk1
        · intro addr hout
          exact (hfre addr hout).trans (hfrk addr hout)
        · exact (hregs_call 5 (by decide)).trans (by simp [stE, hr5])
        · dsimp only [dgInsertEdgeContract, argsSize, Expr.size] at hcost_call ⊢
          omega)
  refine runs_seq_triple_le hLoopE ⟨hr0V, hr1V, hr2V, hr3V, hr4V, hGV', hfrV⟩ ?_
  intro stE ⟨_, hr0E, _, _, _, _, _, hGE, hfrE⟩
  have hGE_full : DynGraphAt stE.mem gPtr vCap eCap (eEdges.foldl refillAddEStep baseV) := by
    simpa [List.take_of_length_le heL_len.le] using hGE
  have hGE_G : DynGraphAt stE.mem gPtr vCap eCap G := by
    refine DynGraphAt.congr_ends ?_ ?_ ?_ hGE_full
    · rw [refill_foldl_addEStep_V]
      exact Finset.ext hbaseV_V
    · ext e
      rw [refill_foldl_addEStep_E, hbaseV_E]
      simp only [Finset.notMem_empty, false_or]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact (heL_spec t ht).1
      · intro heG; exact heL_cov e heG
    · intro e he_fold
      rw [refill_foldl_addEStep_E, hbaseV_E] at he_fold
      rcases he_fold with hc | ⟨t, ht, rfl⟩
      · cases hc
      · have h1 := refill_foldl_addEStep_ends eEdges baseV t ht heNd
        rcases heL_spec t ht with ⟨_, ht_tail, ht_head⟩
        exact ⟨h1.1.trans ht_tail, h1.2.trans ht_head⟩
  refine runs_ret_le (by simp [Expr.eval, hr0E])
    ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, rfl, hGE_G, hfrE⟩ ?_
  simp only [dgFillEmptyFromListsContract, dgFillEmptyFromListsCost, List.getD_cons_zero,
    List.getD_cons_succ, Expr.size]
  omega

/-! ## Verification of `dgRefillFromListsStmt` and `dgRefillModule` -/

/-- `dgRefillFromListsStmt` meets `dgRefillFromListsContract` in
`O(G_old.n + G_old.m + V_len + E_len + 1)` steps using zero scratch. -/
theorem dgRefillFromLists_meetsContract {w : ℕ} {p : Program}
    {bOps bEdge bRefill vCap eCap : ℕ} {G_old G_new : MGraph} {vL : List ℕ}
    {eEdges : List (ℕ × ℕ × ℕ)}
    (hp : p.HasAt bRefill (dgRefillProcs bOps bEdge bRefill))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bRefill + dgIdxRefillFromLists)
      (dgRefillFromListsContract w vCap eCap G_old G_new vL eEdges) := by
  have hClear := dgClear_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (G := G_old) hp
  have hFill := dgFillEmptyFromLists_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
    (G := G_new) (vL := vL) (eEdges := eEdges) hp hpEdge hpOps
  refine meetsContract_of_runs
    (hp.get (i := dgIdxRefillFromLists) (by simp [dgRefillProcs, dgIdxRefillFromLists]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, hw16, hbound, hOld,
    hVal, hvCap, heCap, hvL_len, hvL_at, hvL_mem, hV_bound, hV_disj,
    heL_len, heNd, heL_at, heL_spec, heL_cov, hE_bound, hE_disj⟩
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_Vl : V_len < 2 ^ w := hargs V_len (by simp)
  have hlt_Vp : V_ptr < 2 ^ w := hargs V_ptr (by simp)
  have hlt_El : E_len < 2 ^ w := hargs E_len (by simp)
  have hlt_Ep : E_ptr < 2 ^ w := hargs E_ptr (by simp)
  refine runs_start_le ?_
  dsimp only [dgRefillProcs, dgIdxRefillFromLists, List.getElem_cons_succ,
    List.getElem_cons_zero, dgRefillFromListsStmt]
  refine runs_seq_call_le hClear (vs := [gPtr]) (by eval_expr)
    (by simp [hlt_gp]) ⟨gPtr, rfl, hw16, hbound, hOld⟩ ?_
  rintro ret1 mem1 pos1 ⟨_, hEq1, _, hEmpty1, hfr1⟩
  simp only [List.cons.injEq, and_true] at hEq1
  subst hEq1
  have hvL_at1 : ListAt mem1 V_ptr vL := fun i hi => by
    rw [hfr1 _ (hV_disj i (hvL_len ▸ hi))]
    exact hvL_at i hi
  have heL_at1 : ∀ i (hi : i < eEdges.length),
      mem1 (E_ptr + 3 * i) = eEdges[i].1 ∧
      mem1 (E_ptr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem1 (E_ptr + 3 * i + 2) = eEdges[i].2.2 := fun i hi => by
    rcases heL_at i hi with ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hfr1 _ (hE_disj (3 * i) (by omega))]; exact h0
    · rw [Nat.add_assoc E_ptr (3 * i) 1, hfr1 _ (hE_disj (3 * i + 1) (by omega)), ← Nat.add_assoc]; exact h1
    · rw [Nat.add_assoc E_ptr (3 * i) 2, hfr1 _ (hE_disj (3 * i + 2) (by omega)), ← Nat.add_assoc]; exact h2
  refine runs_seq_call_le hFill (vs := [gPtr, V_len, V_ptr, E_len, E_ptr]) (by eval_expr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl|rfl|rfl) <;> assumption)
    ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, hw16, hbound, hEmpty1, hVal, hvCap, heCap,
      hvL_len, hvL_at1, hvL_mem, hV_bound, hV_disj, heL_len, heNd, heL_at1, heL_spec, heL_cov,
      hE_bound, hE_disj⟩ ?_
  rintro ret2 mem2 pos2 ⟨_, _, _, _, _, hEq2, hret2, hNew2, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq2
  rcases hEq2 with ⟨h2a, h2b, h2c, h2d, h2e⟩
  subst h2a h2b h2c h2d h2e
  have hret2_lt : ret2 < 2 ^ w := hret2 ▸ hlt_gp
  refine runs_ret_le (v := ret2) (by eval_expr)
    ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, hret2, hNew2, fun addr hout =>
      (hfr2 addr hout).trans (hfr1 addr hout)⟩ ?_
  simp only [dgRefillFromListsContract, dgClearContract, dgFillEmptyFromListsContract,
    dgRefillFromListsCost, dgClearCost, dgFillEmptyFromListsCost, startState,
    List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
  omega

/-- The self-contained 12-procedure `dgRefillModule b` meets `dgRefillFromListsContract` at
`b + 11`. -/
theorem dgRefillModule_meetsContract {w b vCap eCap : ℕ} {p : Program}
    {G_old G_new : MGraph} {vL : List ℕ} {eEdges : List (ℕ × ℕ × ℕ)}
    (hp : p.HasAt b (dgRefillModule b)) :
    MeetsContract w p (b + 11)
      (dgRefillFromListsContract w vCap eCap G_old G_new vL eEdges) := by
  have hOps : p.HasAt b dgOpsProcs := by
    intro i hi
    have hi7 : i < 7 := by simpa [dgOpsProcs_length] using hi
    have h := hp i (by rw [dgRefillModule_length]; omega)
    rw [h]
    congr 1
    simp only [dgRefillModule, List.append_assoc]
    exact List.getElem_append_left hi
  have hEdge : p.HasAt (b + 7) (dgEdgeProcs b) := by
    intro i hi
    have hi2 : i < 2 := by simpa [dgEdgeProcs_length] using hi
    have h := hp (7 + i) (by rw [dgRefillModule_length]; omega)
    rw [show b + 7 + i = b + (7 + i) by omega, h]
    congr 1
    simp only [dgRefillModule, List.append_assoc]
    rw [List.getElem_append_right (by rw [dgOpsProcs_length]; omega),
      List.getElem_append_left (by rw [dgOpsProcs_length, dgEdgeProcs_length]; omega)]
    simp [dgOpsProcs_length]
  have hRef : p.HasAt (b + 9) (dgRefillProcs b (b + 7) (b + 9)) := by
    intro i hi
    have hi3 : i < 3 := by simpa [dgRefillProcs_length] using hi
    have h := hp (9 + i) (by rw [dgRefillModule_length]; omega)
    rw [show b + 9 + i = b + (9 + i) by omega, h]
    congr 1
    simp only [dgRefillModule, List.append_assoc]
    rw [List.getElem_append_right (by rw [dgOpsProcs_length]; omega),
      List.getElem_append_right (by rw [dgOpsProcs_length, dgEdgeProcs_length]; omega)]
    simp [dgOpsProcs_length, dgEdgeProcs_length, show 9 + i - 7 - 2 = i by omega]
  simpa [dgIdxRefillFromLists, Nat.add_assoc] using
    dgRefillFromLists_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
      (G_old := G_old) (G_new := G_new) (vL := vL) (eEdges := eEdges) hRef hEdge hOps

/-! ## Non-vacuity witness -/

/-- The precondition of `dgRefillFromListsContract` is simultaneously satisfiable (with input lists
above the graph block, matching the select-level refill setting). -/
theorem dgRefillFromLists_pre_nonvacuous :
    ∃ args mem,
      (dgRefillFromListsContract 8 2 2 dgEmptyGraph dgEmptyGraph [] []).pre args mem := by
  let mem : ℕ → ℕ := fun a => if a = 0 then 2 else if a = 1 then 2 else 0
  have hEmpty : DynGraphAt mem 0 2 2 dgEmptyGraph := by
    refine ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
      by simp [mem, dgVCapOff], by simp [mem, dgECapOff], by simp [mem, dgNOff, dgEmptyGraph, MGraph.n],
      by simp [mem, dgMOff, dgEmptyGraph, MGraph.m],
      (fun v hv => by simp [mem, dgVPresBase, dgEmptyGraph]; omega),
      ⟨[], by simp [dgEmptyGraph, MGraph.n], List.nodup_nil, (fun _ => by simp [dgEmptyGraph]),
        (fun i hi => by simp at hi), (fun i hi => by simp at hi)⟩,
      (fun _ h => by cases h), (fun _ h => by cases h),
      (fun e he => by simp [mem, dgEPresBase, dgEmptyGraph]; omega),
      ⟨[], by simp [dgEmptyGraph, MGraph.m], List.nodup_nil, (fun _ => by simp [dgEmptyGraph]),
        (fun i hi => by simp at hi), (fun i hi => by simp at hi)⟩,
      (fun _ h => by cases h),
      ⟨fun _ => [], fun s hs => ⟨IsDoublyLinkedList.nil (by simp [mem, dgIncHeadBase]; omega),
        by simp [mem, dgSlotDegBase]; omega, (fun _ => by simp [dgEmptyGraph])⟩⟩⟩
  exact ⟨[0, 0, 40, 0, 40], mem, 0, 0, 40, 0, 40, rfl, by decide, by decide, hEmpty,
    (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
    rfl, (fun i hi => by simp at hi), (fun v => by simp [dgEmptyGraph]), by decide,
    (fun i hi => by omega), rfl, List.nodup_nil, (fun i hi => by simp at hi),
    (fun _ h => by cases h), (fun _ h => by cases h), by decide, (fun i hi => by omega)⟩

end

end MinCostFlow.DynSpanner.Program
