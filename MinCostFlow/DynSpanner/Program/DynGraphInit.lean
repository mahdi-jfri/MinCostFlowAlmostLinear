module

public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop
import MinCostFlow.DynSpanner.Program.DynGraphInsert

/-!
# Verification of `dgInitFromLists` (`DynGraphInit`)

Proves `dgInitFromLists_meetsContract` for `dgBatchProcs bOps bEdge bSplit bBatch` at index
`dgIdxInitFromLists = 2`, initializing a `DynGraphAt` from a vertex list `[v₀, …]` and an
edge-triple list `[e, u, v, …]` in `O(V_len + E_len + 1)` steps.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private def dgAddVStep (H : MGraph) (v : ℕ) : MGraph :=
  { V := insert v H.V, E := H.E, tail := H.tail, head := H.head }

private def dgAddEStep (H : MGraph) (t : ℕ × ℕ × ℕ) : MGraph :=
  H.applyUpdate (.insert t.1 t.2.1 t.2.2)

private lemma mgraph_foldl_addV_V :
    ∀ (vs : List ℕ) (H : MGraph) (v : ℕ),
      v ∈ (vs.foldl dgAddVStep H).V ↔ v ∈ H.V ∨ v ∈ vs
  | [], _, _ => by simp
  | u :: us, H, v => by
    simp only [List.foldl_cons, mgraph_foldl_addV_V, List.mem_cons]
    have hV : (dgAddVStep H u).V = insert u H.V := rfl
    rw [hV, Finset.mem_insert]
    tauto

private lemma mgraph_foldl_addV_E :
    ∀ (vs : List ℕ) (H : MGraph),
      (vs.foldl dgAddVStep H).E = H.E
  | [], _ => rfl
  | u :: us, H => by
    simpa [List.foldl_cons, dgAddVStep] using mgraph_foldl_addV_E us (dgAddVStep H u)

private lemma mgraph_foldl_addEStep_V :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph),
      (es.foldl dgAddEStep H).V = H.V
  | [], _ => rfl
  | t :: ts, H => by
    simpa [List.foldl_cons, dgAddEStep, MGraph.applyUpdate] using
      mgraph_foldl_addEStep_V ts (dgAddEStep H t)

private lemma mgraph_foldl_addEStep_E :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph) (e : ℕ),
      e ∈ (es.foldl dgAddEStep H).E ↔ e ∈ H.E ∨ ∃ t ∈ es, t.1 = e
  | [], H, e => by simp
  | t :: ts, H, e => by
    simp only [List.foldl_cons, mgraph_foldl_addEStep_E, List.mem_cons]
    have hE : (dgAddEStep H t).E = insert t.1 H.E := rfl
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

private lemma mgraph_foldl_addEStep_preserve :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph) (e : ℕ),
      (∀ y ∈ es, y.1 ≠ e) →
      (es.foldl dgAddEStep H).tail e = H.tail e ∧
      (es.foldl dgAddEStep H).head e = H.head e
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: xs, H, e, hne => by
    have hx_ne : x.1 ≠ e := hne x List.mem_cons_self
    have hxs_ne : ∀ y ∈ xs, y.1 ≠ e := fun y hy => hne y (List.mem_cons_of_mem _ hy)
    have ih := mgraph_foldl_addEStep_preserve xs (dgAddEStep H x) e hxs_ne
    have ht : (dgAddEStep H x).tail e = H.tail e := by
      simp [dgAddEStep, MGraph.applyUpdate, hx_ne.symm]
    have hh : (dgAddEStep H x).head e = H.head e := by
      simp [dgAddEStep, MGraph.applyUpdate, hx_ne.symm]
    exact ⟨ih.1.trans ht, ih.2.trans hh⟩

private lemma mgraph_foldl_addEStep_ends :
    ∀ (es : List (ℕ × ℕ × ℕ)) (H : MGraph) (t : ℕ × ℕ × ℕ),
      t ∈ es →
      (es.map Prod.fst).Nodup →
      (es.foldl dgAddEStep H).tail t.1 = t.2.1 ∧
      (es.foldl dgAddEStep H).head t.1 = t.2.2
  | [], _, _, ht, _ => absurd ht List.not_mem_nil
  | x :: xs, H, t, ht, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases hnd with ⟨hx_not, hxs_nd⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ht with rfl | ht_xs
    · have hne : ∀ y ∈ xs, y.1 ≠ t.1 := fun y hy hc =>
        hx_not (List.mem_map.mpr ⟨y, hy, hc⟩)
      have hp := mgraph_foldl_addEStep_preserve xs (dgAddEStep H t) t.1 hne
      have ht0 : (dgAddEStep H t).tail t.1 = t.2.1 := by
        simp [dgAddEStep, MGraph.applyUpdate]
      have hh0 : (dgAddEStep H t).head t.1 = t.2.2 := by
        simp [dgAddEStep, MGraph.applyUpdate]
      exact ⟨hp.1.trans ht0, hp.2.trans hh0⟩
    · exact mgraph_foldl_addEStep_ends xs (dgAddEStep H x) t ht_xs hxs_nd

private lemma list_take_nodup_map {α β : Type*} (f : α → β) :
    ∀ (k : ℕ) (L : List α), (L.map f).Nodup → ((L.take k).map f).Nodup
  | 0, _, _ => by simp
  | _ + 1, [], _ => by simp
  | k + 1, x :: xs, hnd => by
    simp only [List.take_succ_cons, List.map_cons, List.nodup_cons] at hnd ⊢
    refine ⟨fun hc => hnd.1 ?_, list_take_nodup_map f k xs hnd.2⟩
    rcases List.mem_map.mp hc with ⟨y, hy, hyf⟩
    exact List.mem_map.mpr ⟨y, List.mem_of_mem_take hy, hyf⟩

private lemma nodup_getElem_not_mem_take {α β : Type*} (f : α → β)
    {L : List α} {k : ℕ} (hk : k < L.length) (hnd : (L.map f).Nodup) :
    ∀ t ∈ L.take k, f t ≠ f L[k] := by
  intro t ht hc
  have hnd1 : ((L.take (k + 1)).map f).Nodup := list_take_nodup_map f (k + 1) L hnd
  rw [List.take_succ_eq_append_getElem hk, List.map_append, List.map_cons, List.map_nil] at hnd1
  have hdisj := List.nodup_append'.mp hnd1
  exact hdisj.2.2 (List.mem_map.mpr ⟨t, ht, hc⟩) List.mem_cons_self

private lemma zeroFrom_frame_ge {mem mem' : ℕ → ℕ} {a b : ℕ}
    (ha : a ≤ b) (hz : ZeroFrom mem a)
    (hfr : ∀ addr, addr < a ∨ b ≤ addr → mem' addr = mem addr) :
    ZeroFrom mem' b := fun addr haddr => by
  rw [hfr addr (Or.inr haddr)]
  exact hz addr (le_trans ha haddr)

theorem dgInitFromLists_meetsContract {w : ℕ} {p : Program} {bOps bEdge bSplit bBatch vCap eCap : ℕ}
    {G : MGraph} {vL : List ℕ} {eEdges : List (ℕ × ℕ × ℕ)}
    (hp : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bBatch + dgIdxInitFromLists)
      (dgInitFromListsContract w vCap eCap G vL eEdges) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxInitFromLists) (by simp [dgBatchProcs, dgIdxInitFromLists]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, hw16, hbound, hz,
    hG_val, hvCap, heCap, hvL_len, hvL_at, hvL_mem, hV_disj,
    heL_len, heNd, heL_at, heL_spec, heL_cov, hE_disj⟩
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_vc : vCap < 2 ^ w := hargs vCap (by simp)
  have hlt_ec : eCap < 2 ^ w := hargs eCap (by simp)
  have hlt_Vl : V_len < 2 ^ w := hargs V_len (by simp)
  have hlt_Vp : V_ptr < 2 ^ w := hargs V_ptr (by simp)
  have hlt_El : E_len < 2 ^ w := hargs E_len (by simp)
  have hlt_Ep : E_ptr < 2 ^ w := hargs E_ptr (by simp)
  have hw_ne0 : w ≠ 0 := by rintro rfl; omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h4_le_sz : 4 ≤ dynGraphSize vCap eCap := by dsimp [dynGraphSize]; omega
  refine runs_start_le ?_
  dsimp only [dgBatchProcs, dgIdxInitFromLists, List.getElem_cons_succ, List.getElem_cons_zero,
    dgInitFromListsStmt]
  have hpre_init : (dgInitEmptyContract w).pre [gPtr, vCap, eCap] mem :=
    ⟨gPtr, vCap, eCap, rfl, hw16, hbound, hz⟩
  refine runs_seq_call_le (dgInitEmpty_meetsContract hpOps) (by eval_expr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl) <;> assumption)
    hpre_init ?_
  rintro ret0 mem0 pos0 ⟨_, _, _, hEq0, _, hG0, hfr0_small, _⟩
  simp only [List.cons.injEq, and_true] at hEq0
  rcases hEq0 with ⟨h0a, h0b, h0c⟩
  subst h0a h0b h0c
  have hfr0 : ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem0 addr = mem addr := by
    intro addr hout
    rcases hout with hlt | hge
    · exact hfr0_small addr (Or.inl hlt)
    · exact hfr0_small addr (Or.inr (by omega))
  let emptyG : MGraph := { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  let PV : State → Prop := fun st =>
    st.regs 0 = gPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = V_len ∧
    st.regs 4 = V_ptr ∧ st.regs 5 = E_len ∧ st.regs 6 = E_ptr ∧
    DynGraphAt st.mem gPtr vCap eCap emptyG ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let InvV : ℕ → State → Prop := fun k st =>
    k ≤ V_len ∧
    st.regs 0 = gPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = V_len ∧
    st.regs 4 = V_ptr ∧ st.regs 5 = E_len ∧ st.regs 6 = E_ptr ∧ st.regs 7 = k ∧
    DynGraphAt st.mem gPtr vCap eCap ((vL.take k).foldl dgAddVStep emptyG) ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let bodyV : Stmt :=
    .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
    .call 9 (bOps + dgIdxAddVertex) [.reg 0, .reg 8]
  have hLoopV : Triple w p PV (forRange 7 (.const 0) (.reg 3) bodyV) (normalPost (InvV V_len))
      (fun _ => (V_len - 0) * (119 + Expr.size (.reg 3) + 8) + (Expr.size (.const 0) + Expr.size (.reg 3) + 5)) := by
    refine Triple.forRange_const 119 0 V_len (Nat.zero_le _) h1_lt (fun _ => hlt_Vl)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, hG, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
        · simp [h4]
        · simp [h5]
        · simp [h6]
        · simp
        · simpa [emptyG] using hG)
      (fun k st _ _ hk => hk.2.2.2.2.2.2.2.2.1)
      (fun k st _ _ hk => by
        rcases hk with ⟨_, _, _, _, hr3, _, _, _, _, _, _⟩
        simp [Expr.eval, hr3])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hGk, hfrk⟩
        have hlt_Vp_k : V_ptr + k < 2 ^ w := by
          have := hV_disj k hk_lt
          omega
        have hvk_disj : V_ptr + k < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ V_ptr + k :=
          Or.inl (hV_disj k hk_lt)
        have hk_vL : k < vL.length := hvL_len.symm ▸ hk_lt
        have hvk_mem : st.mem (V_ptr + k) = vL[k] := by
          rw [hfrk _ hvk_disj]
          exact hvL_at k hk_vL
        have hvk_cap : vL[k] < vCap := hvCap vL[k] ((hvL_mem vL[k]).mp (List.getElem_mem hk_vL))
        have hvk_ltw : vL[k] < 2 ^ w := lt_trans hvk_cap hlt_vc
        suffices h : ∃ o st₁ c, Runs w p ω' bodyV st o st₁ c ∧
            (normalPost fun st₁ =>
              InvV (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 7 (k + 1), pos := st₁.pos } ∧
                st₁.regs 7 = k) o st₁ ∧
            0 + c ≤ 119 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyV]
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := vL[k])
            (by simp [Expr.eval, BinOp.eval, hr4, hr7, hlt_Vp_k]) hvk_mem) ?_
        let stA : State := { mem := st.mem, regs := Function.update st.regs 8 vL[k], pos := st.pos }
        have hpre_v : (dgAddVertexContract w vCap eCap _).pre [gPtr, vL[k]] stA.mem :=
          ⟨gPtr, vL[k], rfl, hw16, hbound, hvk_cap, hGk⟩
        have hargs_eval_v : evalArgs w stA [Expr.reg 0, Expr.reg 8] = some [gPtr, vL[k]] := by
          simp [stA, evalArgs, Expr.eval, hr0]
        rcases runs_call_of_meetsContract (r := 9) (dgAddVertex_meetsContract hpOps)
          hargs_eval_v
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl) <;> assumption)
          hpre_v ω'
          with ⟨st₁, c_call, ret, hruns_call, hpost_call, _, hregs_call, hcost_call⟩
        rcases hpost_call with ⟨_, _, hEqv, _, hGk1, hfrv⟩
        simp only [List.cons.injEq, and_true] at hEqv
        rcases hEqv with ⟨hva, hvb⟩
        subst hva hvb
        refine ⟨.normal, st₁, c_call, hruns_call, ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · exact (hregs_call 0 (by decide)).trans (by simp [stA, hr0])
        · exact (hregs_call 1 (by decide)).trans (by simp [stA, hr1])
        · exact (hregs_call 2 (by decide)).trans (by simp [stA, hr2])
        · exact (hregs_call 3 (by decide)).trans (by simp [stA, hr3])
        · exact (hregs_call 4 (by decide)).trans (by simp [stA, hr4])
        · exact (hregs_call 5 (by decide)).trans (by simp [stA, hr5])
        · exact (hregs_call 6 (by decide)).trans (by simp [stA, hr6])
        · simp
        · rw [List.take_succ_eq_append_getElem hk_vL, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact hGk1
        · intro addr hout
          exact (hfrv addr hout).trans (hfrk addr hout)
        · exact (hregs_call 7 (by decide)).trans (by simp [stA, hr7])
        · dsimp only [dgAddVertexContract, argsSize, Expr.size] at hcost_call ⊢
          omega)
  refine runs_seq_triple_le hLoopV ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr0⟩ <;> simp [startState, emptyG, hG0]
  intro stV ⟨_, hr0V, hr1V, hr2V, hr3V, hr4V, hr5V, hr6V, _, hGV, hfrV⟩
  let baseV : MGraph := vL.foldl dgAddVStep emptyG
  have hGV' : DynGraphAt stV.mem gPtr vCap eCap baseV := by
    simpa [baseV, List.take_of_length_le hvL_len.le] using hGV
  have hbaseV_V : ∀ v, v ∈ baseV.V ↔ v ∈ G.V := fun v => by
    simpa [baseV, emptyG, mgraph_foldl_addV_V] using hvL_mem v
  have hbaseV_E : baseV.E = ∅ := mgraph_foldl_addV_E vL emptyG
  let PE : State → Prop := fun st =>
    st.regs 0 = gPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = V_len ∧
    st.regs 4 = V_ptr ∧ st.regs 5 = E_len ∧ st.regs 6 = E_ptr ∧
    DynGraphAt st.mem gPtr vCap eCap baseV ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let InvE : ℕ → State → Prop := fun k st =>
    k ≤ E_len ∧
    st.regs 0 = gPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = V_len ∧
    st.regs 4 = V_ptr ∧ st.regs 5 = E_len ∧ st.regs 6 = E_ptr ∧ st.regs 7 = k ∧
    DynGraphAt st.mem gPtr vCap eCap ((eEdges.take k).foldl dgAddEStep baseV) ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let bodyE : Stmt :=
    .assign 8 (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 7))) ;;
    .assign 9 (.load (.reg 8)) ;;
    .assign 10 (.load (.bin .add (.reg 8) (.const 1))) ;;
    .assign 11 (.load (.bin .add (.reg 8) (.const 2))) ;;
    .call 12 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 9, .reg 10, .reg 11]
  have hLoopE : Triple w p PE (forRange 7 (.const 0) (.reg 5) bodyE) (normalPost (InvE E_len))
      (fun _ => (E_len - 0) * (478 + Expr.size (.reg 5) + 8) + (Expr.size (.const 0) + Expr.size (.reg 5) + 5)) := by
    refine Triple.forRange_const 478 0 E_len (Nat.zero_le _) h1_lt (fun _ => hlt_El)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, hG, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
        · simp [h4]
        · simp [h5]
        · simp [h6]
        · simp
        · simpa using hG)
      (fun k st _ _ hk => hk.2.2.2.2.2.2.2.2.1)
      (fun k st _ _ hk => by
        rcases hk with ⟨_, _, _, _, _, _, hr5, _, _, _, _⟩
        simp [Expr.eval, hr5])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hGk, hfrk⟩
        have hk_eL : k < eEdges.length := heL_len.symm ▸ hk_lt
        let t := eEdges[k]
        have hlt_3k : 3 * k < 2 ^ w := by
          have := hE_disj (3 * k) (by omega)
          omega
        have hlt_Ep_3k0 : E_ptr + 3 * k < 2 ^ w := by
          have := hE_disj (3 * k) (by omega)
          omega
        have hlt_Ep_3k1 : E_ptr + 3 * k + 1 < 2 ^ w := by
          have := hE_disj (3 * k + 1) (by omega)
          omega
        have hlt_Ep_3k2 : E_ptr + 3 * k + 2 < 2 ^ w := by
          have := hE_disj (3 * k + 2) (by omega)
          omega
        rcases heL_at k hk_eL with ⟨hm0, hm1, hm2⟩
        have ht0_mem : st.mem (E_ptr + 3 * k) = t.1 := by
          rw [hfrk _ (Or.inl (hE_disj (3 * k) (by omega)))]
          exact hm0
        have ht1_mem : st.mem (E_ptr + 3 * k + 1) = t.2.1 := by
          rw [Nat.add_assoc E_ptr (3 * k) 1, hfrk _ (Or.inl (hE_disj (3 * k + 1) (by omega))), ← Nat.add_assoc]
          exact hm1
        have ht2_mem : st.mem (E_ptr + 3 * k + 2) = t.2.2 := by
          rw [Nat.add_assoc E_ptr (3 * k) 2, hfrk _ (Or.inl (hE_disj (3 * k + 2) (by omega))), ← Nat.add_assoc]
          exact hm2
        rcases heL_spec t (List.getElem_mem hk_eL) with ⟨he_G, hu_eq, hv_eq⟩
        have he_cap : t.1 < eCap := heCap t.1 he_G
        have hu_V : t.2.1 ∈ G.V := hu_eq ▸ (hG_val t.1 he_G).1
        have hv_V : t.2.2 ∈ G.V := hv_eq ▸ (hG_val t.1 he_G).2
        have hu_cap : t.2.1 < vCap := hvCap t.2.1 hu_V
        have hv_cap : t.2.2 < vCap := hvCap t.2.2 hv_V
        have hlt_e : t.1 < 2 ^ w := lt_trans he_cap hlt_ec
        have hlt_u : t.2.1 < 2 ^ w := lt_trans hu_cap hlt_vc
        have hlt_v : t.2.2 < 2 ^ w := lt_trans hv_cap hlt_vc
        have hu_Gk : t.2.1 ∈ ((eEdges.take k).foldl dgAddEStep baseV).V := by
          rw [mgraph_foldl_addEStep_V]; exact (hbaseV_V _).mpr hu_V
        have hv_Gk : t.2.2 ∈ ((eEdges.take k).foldl dgAddEStep baseV).V := by
          rw [mgraph_foldl_addEStep_V]; exact (hbaseV_V _).mpr hv_V
        have he_not_Gk : t.1 ∉ ((eEdges.take k).foldl dgAddEStep baseV).E := by
          rw [mgraph_foldl_addEStep_E, hbaseV_E]
          rintro (hc | ⟨y, hy, hyf⟩)
          · cases hc
          · exact nodup_getElem_not_mem_take Prod.fst hk_eL heNd y hy hyf
        suffices h : ∃ o st₁ c, Runs w p ω' bodyE st o st₁ c ∧
            (normalPost fun st₁ =>
              InvE (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 7 (k + 1), pos := st₁.pos } ∧
                st₁.regs 7 = k) o st₁ ∧
            0 + c ≤ 478 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyE]
        refine runs_seq_assign_le (v := E_ptr + 3 * k)
          (by simp [Expr.eval, BinOp.eval, h3_lt, hr6, hr7, hlt_3k, hlt_Ep_3k0]) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := t.1) (by eval_expr) ht0_mem) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := t.2.1)
            (by simp [Expr.eval, BinOp.eval, h1_lt, hlt_Ep_3k1]) ht1_mem) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := t.2.2)
            (by simp [Expr.eval, BinOp.eval, h2_lt, hlt_Ep_3k2]) ht2_mem) ?_
        let stE : State := {
          mem := st.mem,
          regs := Function.update (Function.update (Function.update (Function.update st.regs
            8 (E_ptr + 3 * k)) 9 t.1) 10 t.2.1) 11 t.2.2,
          pos := st.pos }
        have hpre_e : (dgInsertEdgeContract w vCap eCap _).pre [gPtr, t.1, t.2.1, t.2.2] stE.mem :=
          ⟨gPtr, t.1, t.2.1, t.2.2, rfl, hw16, hbound, hu_Gk, hv_Gk, hGk⟩
        have hargs_eval_e : evalArgs w stE [Expr.reg 0, Expr.reg 9, Expr.reg 10, Expr.reg 11] =
            some [gPtr, t.1, t.2.1, t.2.2] := by
          simp [stE, evalArgs, Expr.eval, hr0]
        rcases runs_call_of_meetsContract (r := 12) (dgInsertEdge_meetsContract hpEdge hpOps)
          hargs_eval_e
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl|rfl) <;> assumption)
          hpre_e ω'
          with ⟨st₁, c_call, ret, hruns_call, hpost_call, _, hregs_call, hcost_call⟩
        rcases hpost_call with ⟨_, _, _, _, hEqe, _, hGk1, hfre⟩
        simp only [List.cons.injEq, and_true] at hEqe
        rcases hEqe with ⟨hea, heb, hec, hed⟩
        subst hea heb hec hed
        refine ⟨.normal, st₁, c_call, hruns_call, ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · exact (hregs_call 0 (by decide)).trans (by simp [stE, hr0])
        · exact (hregs_call 1 (by decide)).trans (by simp [stE, hr1])
        · exact (hregs_call 2 (by decide)).trans (by simp [stE, hr2])
        · exact (hregs_call 3 (by decide)).trans (by simp [stE, hr3])
        · exact (hregs_call 4 (by decide)).trans (by simp [stE, hr4])
        · exact (hregs_call 5 (by decide)).trans (by simp [stE, hr5])
        · exact (hregs_call 6 (by decide)).trans (by simp [stE, hr6])
        · simp
        · simp only [he_cap, he_not_Gk] at hGk1
          rw [List.take_succ_eq_append_getElem hk_eL, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact hGk1
        · intro addr hout
          exact (hfre addr hout).trans (hfrk addr hout)
        · exact (hregs_call 7 (by decide)).trans (by simp [stE, hr7])
        · dsimp only [dgInsertEdgeContract, argsSize, Expr.size] at hcost_call ⊢
          omega)
  refine runs_seq_triple_le hLoopE ⟨hr0V, hr1V, hr2V, hr3V, hr4V, hr5V, hr6V, hGV', hfrV⟩ ?_
  intro stE ⟨_, hr0E, _, _, _, _, _, _, _, hGE, hfrE⟩
  have hGE_full : DynGraphAt stE.mem gPtr vCap eCap (eEdges.foldl dgAddEStep baseV) := by
    simpa [List.take_of_length_le heL_len.le] using hGE
  have hGE_G : DynGraphAt stE.mem gPtr vCap eCap G := by
    refine DynGraphAt.congr_ends ?_ ?_ ?_ hGE_full
    · rw [mgraph_foldl_addEStep_V]
      exact Finset.ext hbaseV_V
    · ext e
      rw [mgraph_foldl_addEStep_E, hbaseV_E]
      simp only [Finset.notMem_empty, false_or]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact (heL_spec t ht).1
      · intro heG; exact heL_cov e heG
    · intro e he_fold
      rw [mgraph_foldl_addEStep_E, hbaseV_E] at he_fold
      rcases he_fold with hc | ⟨t, ht, rfl⟩
      · cases hc
      · have h1 := mgraph_foldl_addEStep_ends eEdges baseV t ht heNd
        rcases heL_spec t ht with ⟨_, ht_tail, ht_head⟩
        exact ⟨h1.1.trans ht_tail, h1.2.trans ht_head⟩
  have hz_out : ZeroFrom stE.mem (gPtr + dynGraphSize vCap eCap) :=
    zeroFrom_frame_ge (by omega) hz hfrE
  refine runs_ret_le (by simp [Expr.eval, hr0E])
    ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, rfl, hGE_G, hfrE, hz_out⟩ ?_
  dsimp only [dgInitFromListsContract, dgInitEmptyContract, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, argsSize, Expr.size]
  omega

end

end MinCostFlow.DynSpanner.Program
