module

public import MinCostFlow.DynSpanner.Program.DynSpannerPhaseDefs

public import MinCostFlow.DynSpanner.Program.StateLayout
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MinCostFlow.DynSpanner.Program.DynGraphDelete
import MinCostFlow.DynSpanner.Program.DynGraphInsert

/-!
# Part 2 of `DynSpannerPhase`

See `DynSpannerPhase.lean` for the overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

theorem clearAuxGraph_meetsContract {w : ℕ} {p : Program} {bPhase bEdge bOps vCap eCap : ℕ}
    {A : MGraph}
    (hp : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bPhase + phaseIdxClearAux) (clearAuxGraphContract w vCap eCap A) := by
  refine meetsContract_of_runs (hp.get (i := phaseIdxClearAux) (by simp [phaseProcs, phaseIdxClearAux]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨auxPtr, rfl, hw16, hbound, hA⟩
  have hlt_a : auxPtr < 2 ^ w := hargs auxPtr (by simp)
  have h0w : (0 : ℕ) < 2 ^ w := by omega
  have h1w : (1 : ℕ) < 2 ^ w := by omega
  have h4w : (4 : ℕ) < 2 ^ w := by omega
  have h7vw : 7 * vCap < 2 ^ w := by simp [dynGraphSize] at hbound; omega
  have hePres_ltw : dgEPresBase auxPtr vCap < 2 ^ w := by
    simp [dgEPresBase, dynGraphSize] at hbound ⊢; omega
  have heList_ltw : dgEListBase auxPtr vCap eCap < 2 ^ w := by
    simp [dgEListBase, dynGraphSize] at hbound ⊢; omega
  have hvPres_ltw : dgVPresBase auxPtr < 2 ^ w := by
    simp [dgVPresBase, dynGraphSize] at hbound ⊢; omega
  have hvList_ltw : dgVListBase auxPtr vCap < 2 ^ w := by
    simp [dgVListBase, dynGraphSize] at hbound ⊢; omega
  refine runs_start_le ?_
  dsimp only [phaseProcs, phaseIdxClearAux, List.getElem_cons_succ, List.getElem_cons_zero, clearAuxGraphStmt]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (by eval_expr) hA.2.2.2.1) ?_
  refine runs_seq_assign_le (v := eCap) ?_ ?_
  · refine Expr.eval_load_of_eq ?_ hA.2.2.2.2.1
    rw [dgECapOff]
    simp [Expr.eval, BinOp.eval, startState, h1w,
      show auxPtr + 1 < 2 ^ w by simp [dynGraphSize] at hbound; omega]
  refine runs_seq_assign_le (v := dgEPresBase auxPtr vCap) ?_ ?_
  · have hb4 : auxPtr + 4 < 2 ^ w := by simp [dynGraphSize] at hbound; omega
    have hePres' : auxPtr + 4 + 7 * vCap < 2 ^ w := by simpa [dgEPresBase] using hePres_ltw
    simp [Expr.eval, BinOp.eval, startState, h4w, h7vw, hb4, hePres', dgEPresBase,
      show (7 : ℕ) < 2 ^ w by omega]
  refine runs_seq_assign_le (v := dgEListBase auxPtr vCap eCap) ?_ ?_
  · have heList' : auxPtr + 4 + 7 * vCap + eCap < 2 ^ w := by simpa [dgEListBase] using heList_ltw
    simp [Expr.eval, BinOp.eval, startState, dgEListBase, dgEPresBase, heList']
  -- Loop 1: delete all remaining edges in `auxPtr`
  let Inv1 : State → Prop := fun st =>
    ∃ G : MGraph,
      G.V = A.V ∧ G.m ≤ A.m ∧ DynGraphAt st.mem auxPtr vCap eCap G ∧
      st.regs 0 = auxPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧
      st.regs 3 = dgEPresBase auxPtr vCap ∧ st.regs 4 = dgEListBase auxPtr vCap eCap ∧
      ∀ addr, addr < auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr
  have hLoop1 : Triple w p Inv1
      (.loop (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const dgMOff))))
        (.assign 5 (.load (.reg 4)) ;; .call 6 (bEdge + dgIdxDeleteEdge) [.reg 0, .reg 5]))
      (normalPost fun st =>
        ∃ G : MGraph, G.V = A.V ∧ G.E = ∅ ∧ DynGraphAt st.mem auxPtr vCap eCap G ∧
          st.regs 0 = auxPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧
          ∀ addr, addr < auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
      (fun st => ((.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const dgMOff))) : Expr).size + 465 + 1) *
        st.mem (auxPtr + dgMOff) +
        (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const dgMOff))) : Expr).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => st.mem (auxPtr + dgMOff))
      (condVal := fun st => if 0 < st.mem (auxPtr + dgMOff) then 1 else 0)
      (bodyBound := 465)
      (fun st ⟨G, _, _, hG, hr0, _, _, _, _, _⟩ => by
        have hm_eq := hG.2.2.2.2.2.2.1
        have hm_lt : G.m < 2 ^ w := by
          have : G.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (hG.2.2.1 e he)
          have : G.m ≤ eCap := by simpa [MGraph.m] using Finset.card_le_card this
          simp [dynGraphSize] at hbound; omega
        have hdgm_lt : dgMOff < 2 ^ w := by simp [dgMOff]; omega
        have haddr_lt : auxPtr + dgMOff < 2 ^ w := by
          simp [dgMOff, dynGraphSize] at hbound ⊢; omega
        have hload : (.load (.bin .add (.reg 0) (.const dgMOff)) : Expr).eval w st = some G.m := by
          refine Expr.eval_load_of_eq ?_ hm_eq
          simp [Expr.eval, BinOp.eval, hr0, hdgm_lt, haddr_lt]
        have heval_c : (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const dgMOff))) : Expr).eval w st =
            some (if 0 < G.m then 1 else 0) := by
          rw [Expr.eval, Expr.eval, hload]
          by_cases hm0 : 0 < G.m
          · simp [BinOp.eval, h0w, h1w, hm0]
          · simp [BinOp.eval, h0w, hm0]
        simpa [hm_eq] using heval_c)
      (fun st ⟨G, hGV, _, hG, hr0, hr1, hr2, _, _, hfr⟩ hv => by
        have hm_eq := hG.2.2.2.2.2.2.1
        have hm0 : G.m = 0 := by
          by_contra hne
          have hpos : 0 < G.m := Nat.pos_of_ne_zero hne
          simp [hm_eq, hpos] at hv
        exact ⟨G, hGV, Finset.card_eq_zero.mp hm0, hG, hr0, hr1, hr2, hfr⟩)
      (fun st ⟨G, hGV, hGm, hG, hr0, hr1, hr2, hr3, hr4, hfr⟩ hv => by
        intro s ω hs
        rw [hs]
        refine runs_start_le ?_
        have hm_eq := hG.2.2.2.2.2.2.1
        have hm0 : 0 < G.m := by
          simp only [hm_eq] at hv
          split_ifs at hv with hm0
          · exact hm0
          · exact absurd rfl hv
        obtain ⟨eL, heL_len, _, heL_mem, heL_at, _⟩ := hG.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h0_lt : 0 < eL.length := by rw [heL_len]; exact hm0
        let e := eL[0]'h0_lt
        have heE : e ∈ G.E := (heL_mem e).mp (List.getElem_mem h0_lt)
        have he_mem : st.mem (dgEListBase auxPtr vCap eCap) = e := by simpa using heL_at 0 h0_lt
        have he_ltw : e < 2 ^ w := by have := hG.2.2.1 e heE; simp [dynGraphSize] at hbound; omega
        refine runs_seq_assign_le (v := e) ?_ ?_
        · exact Expr.eval_load_of_eq (by simp [Expr.eval, hr4]) he_mem
        · let st1 := { st with regs := Function.update st.regs 5 e }
          have hpre_del : (dgDeleteEdgeContract w vCap eCap G).pre [auxPtr, e] st1.mem :=
            ⟨auxPtr, e, rfl, hw16, hbound, hG⟩
          have heval_del : evalArgs w st1 [.reg 0, .reg 5] = some [auxPtr, e] := by
            simp [st1, Expr.eval, evalArgs, hr0]
          refine runs_call_le (r := 6) (dgDeleteEdge_meetsContract hpEdge hpOps)
            heval_del (fun z hz => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with rfl | rfl <;> assumption)
            hpre_del ?_
          intro ret mem' pos' hpost_del
          rcases hpost_del with ⟨_, _, hEq, _, hG2, hfr2⟩
          simp only [List.cons.injEq, and_true] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          simp only [heE, ↓reduceIte] at hG2
          have hm'_lt : (G.applyUpdate (.delete e)).m < G.m := by
            simpa [MGraph.applyUpdate, MGraph.m] using Finset.card_erase_lt_of_mem heE
          refine ⟨⟨⟨G.applyUpdate (.delete e), hGV, le_trans hm'_lt.le hGm, hG2,
            by simp [hr0], by simp [hr1], by simp [hr2],
            by simp [hr3], by simp [hr4],
            fun addr ha => (hfr2 addr ha).trans (hfr addr ha)⟩, ?_⟩, ?_⟩
          · dsimp only
            rw [hG2.2.2.2.2.2.2.1, hm_eq]
            exact hm'_lt
          · dsimp only [dgDeleteEdgeContract, argsSize, Expr.size]
            omega)
  refine runs_seq_triple_le hLoop1
    ⟨A, rfl, le_rfl, hA, by simp [startState], by simp, by simp, by simp, by simp, fun _ _ => rfl⟩ ?_
  intro stA ⟨G, hGV, hGE, hGA, hr0A, hr1A, hr2A, hfrA⟩
  rcases hGA with ⟨_, hvCA, _, h0A, h1A, h2A, h3A, hvpA, hvLA, _, _, hepA, _, _, hincA⟩
  have hGnA : G.n = A.n := by simp [MGraph.n, hGV]
  have hn_ltw : A.n < 2 ^ w := by
    have hsub : A.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (hA.2.1 v hv)
    have hle : A.n ≤ vCap := by simpa [MGraph.n] using Finset.card_le_card hsub
    simp [dynGraphSize] at hbound; omega
  refine runs_seq_assign_le (v := A.n) ?_ ?_
  · refine Expr.eval_load_of_eq ?_ (by simpa [hGnA] using h2A)
    rw [dgNOff]
    simp [Expr.eval, BinOp.eval, hr0A,
      show (2 : ℕ) < 2 ^ w by omega,
      show auxPtr + 2 < 2 ^ w by simp [dynGraphSize] at hbound; omega]
  refine runs_seq_assign_le (v := dgVPresBase auxPtr) ?_ ?_
  · have hvPres' : auxPtr + 4 < 2 ^ w := by simpa [dgVPresBase] using hvPres_ltw
    simp [Expr.eval, BinOp.eval, hr0A, h4w, hvPres', dgVPresBase]
  refine runs_seq_assign_le (v := dgVListBase auxPtr vCap) ?_ ?_
  · have hvList' : auxPtr + 4 + vCap < 2 ^ w := by simpa [dgVListBase] using hvList_ltw
    simp [Expr.eval, BinOp.eval, hr1A, dgVListBase, dgVPresBase, hvList']
  obtain ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, _⟩ := hvLA
  have hvL_len' : vL.length = A.n := by rw [hvL_len, hGnA]
  -- Loop 2: zero `dgVPresBase auxPtr + v` for all `v ∈ vL`
  let Inv2 : ℕ → State → Prop := fun i st =>
    st.regs 0 = auxPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧
    st.regs 5 = A.n ∧ st.regs 6 = dgVPresBase auxPtr ∧ st.regs 7 = dgVListBase auxPtr vCap ∧
    st.regs 8 = i ∧
    (∀ addr, addr < auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr) ∧
    (∀ addr, st.mem addr = stA.mem addr ∨
      ∃ j < i, ∃ hj : j < vL.length, addr = dgVPresBase auxPtr + vL[j]) ∧
    (∀ j (hj : j < i), ∃ hjt : j < vL.length, st.mem (dgVPresBase auxPtr + vL[j]) = 0)
  have hLoop2 : Triple w p
      (fun st => st.regs 0 = auxPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧
        st.regs 5 = A.n ∧ st.regs 6 = dgVPresBase auxPtr ∧ st.regs 7 = dgVListBase auxPtr vCap ∧
        (∀ addr, addr < auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr) ∧
        st.mem = stA.mem)
      (forRange 8 (.const 0) (.reg 5)
        (.assign 9 (.load (.bin .add (.reg 7) (.reg 8))) ;;
         .store (.bin .add (.reg 6) (.reg 9)) (.const 0)))
      (normalPost (Inv2 A.n))
      (fun _ => A.n * (12 + (.reg 5 : Expr).size + 8) + ((.const 0 : Expr).size + (.reg 5 : Expr).size + 5)) := by
    refine Triple.forRange_const 12 0 A.n (Nat.zero_le _) h1w (fun _ => hn_ltw)
      (fun st ⟨hr0, hr1, hr2, hr5, hr6, hr7, hfr, hmeq⟩ => ⟨by eval_expr,
        by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr5], by simp [hr6], by simp [hr7],
        by simp, by simpa [hmeq] using hfr, fun addr => Or.inl (by simp [hmeq]), fun _ hj => by omega⟩)
      (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
      (fun i st _ _ h => by simp [Expr.eval, h.2.2.2.1])
      (fun i _ hi st ω hInv => by
        refine runs_start_le ?_
        rcases hInv with ⟨hr0, hr1, hr2, hr5, hr6, hr7, hr8, hfr, hchg, hzero⟩
        have hi_vL : i < vL.length := by omega
        have hi_ltw : i < 2 ^ w := lt_of_lt_of_le hi hn_ltw.le
        have hiv_ltw : dgVListBase auxPtr vCap + i < 2 ^ w := by
          have hsub : A.V ⊆ Finset.range vCap := fun z hz => Finset.mem_range.mpr (hA.2.1 z hz)
          have hAn_le : A.n ≤ vCap := by simpa [MGraph.n] using Finset.card_le_card hsub
          have : i < vCap := by omega
          simp [dgVListBase, dynGraphSize] at hbound ⊢; omega
        let v := vL[i]'hi_vL
        have hvG : v ∈ G.V := (hvL_mem v).mp (List.getElem_mem hi_vL)
        have hv_ltv : v < vCap := hvCA v hvG
        have hv_ltw : v < 2 ^ w := by simp [dynGraphSize] at hbound; omega
        have hv_addr_ltw : dgVPresBase auxPtr + v < 2 ^ w := by
          simp [dgVPresBase, dynGraphSize] at hbound ⊢; omega
        have hv_load : st.mem (dgVListBase auxPtr vCap + i) = v := by
          have hmem_vL := hvL_at i hi_vL
          rcases hchg (dgVListBase auxPtr vCap + i) with heq | ⟨j, hj1, hj2, had⟩
          · exact heq.trans hmem_vL
          · exfalso
            have hvj : vL[j] < vCap := hvCA _ ((hvL_mem _).mp (List.getElem_mem hj2))
            simp [dgVListBase, dgVPresBase] at had; omega
        refine runs_seq_assign_le (v := v) ?_ ?_
        · exact Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr7, hr8, hiv_ltw]) hv_load
        refine runs_store_le (x := dgVPresBase auxPtr + v) (v := 0)
          (by simp [Expr.eval, BinOp.eval, hr6, hv_addr_ltw]) (by eval_expr) ?_ ?_
        · refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr5],
            by simp [hr6], by simp [hr7], by simp, ?_, ?_, ?_⟩, by simp [hr8]⟩
          · intro addr ha
            dsimp only
            rw [Function.update_of_ne (by simp [dgVPresBase, dynGraphSize] at ha ⊢; omega)]
            exact hfr addr ha
          · intro addr
            dsimp only
            by_cases hhit : addr = dgVPresBase auxPtr + v
            · exact Or.inr ⟨i, Nat.lt_succ_self i, hi_vL, hhit⟩
            · rw [Function.update_of_ne hhit]
              rcases hchg addr with heq | ⟨j, hj1, hj2, had⟩
              · exact Or.inl heq
              · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj1, hj2, had⟩
          · intro j hj
            have hjt : j < vL.length := by omega
            refine ⟨hjt, ?_⟩
            dsimp only
            by_cases hje : vL[j] = v
            · rw [hje, Function.update_self]
            · rw [Function.update_of_ne (by omega)]
              have hji : j ≠ i := fun heq => hje (by subst heq; rfl)
              exact (hzero j (by omega)).2
        · dsimp only [Expr.size]; omega)
  refine runs_seq_triple_le hLoop2
    ⟨by simp [hr0A], by simp [hr1A], by simp [hr2A], by simp, by simp, by simp, hfrA, rfl⟩ ?_
  intro stB ⟨hr0B, _, _, _, _, _, _, hfrB, hchgB, hzeroB⟩
  have hn_ltw' : auxPtr + dgNOff < 2 ^ w := by
    simp [dgNOff, dynGraphSize] at hbound ⊢; omega
  refine runs_seq_store_le (x := auxPtr + dgNOff) (v := 0)
    (by rw [dgNOff]; simp [Expr.eval, BinOp.eval, hr0B,
      show auxPtr + 2 < 2 ^ w by simpa [dgNOff] using hn_ltw',
      show (2 : ℕ) < 2 ^ w by omega])
    (by eval_expr) ?_
  refine runs_ret_le (by eval_expr) ⟨auxPtr, rfl, rfl, ?_, ?_⟩ ?_
  · refine ⟨emptyMGraph_isValid, (fun _ h => by cases h), (fun _ h => by cases h),
      ?_, ?_, ?_, ?_, ?_, ⟨[], rfl, List.nodup_nil, (fun v => by simp [emptyMGraph]),
        (fun i hi => by simp at hi), (fun i hi => by simp at hi)⟩,
      (fun _ hv => by cases hv), (fun _ hs => by cases hs),
      ?_, ⟨[], rfl, List.nodup_nil, (fun e => by simp [emptyMGraph]),
        (fun i hi => by simp at hi), (fun i hi => by simp at hi)⟩,
      (fun _ he => by cases he), ⟨fun _ => [], fun s hs => ?_⟩⟩
    · dsimp only
      rw [Function.update_of_ne (by simp [dgNOff, dgVCapOff])]
      rcases hchgB (auxPtr + dgVCapOff) with heq | ⟨j, _, hj, had⟩
      · exact heq.trans h0A
      · exfalso; simp [dgVCapOff, dgVPresBase] at had; omega
    · dsimp only
      rw [Function.update_of_ne (by simp [dgNOff, dgECapOff])]
      rcases hchgB (auxPtr + dgECapOff) with heq | ⟨j, _, hj, had⟩
      · exact heq.trans h1A
      · exfalso; simp [dgECapOff, dgVPresBase] at had; omega
    · exact Function.update_self _ _ _
    · dsimp only
      rw [Function.update_of_ne (by simp [dgNOff, dgMOff])]
      rcases hchgB (auxPtr + dgMOff) with heq | ⟨j, _, hj, had⟩
      · exact heq.trans (by simpa [emptyMGraph, MGraph.m, hGE] using h3A)
      · exfalso; simp [dgMOff, dgVPresBase] at had; omega
    · intro v hv
      dsimp only
      rw [Function.update_of_ne (by simp [dgNOff, dgVPresBase]; omega)]
      simp only [emptyMGraph, Finset.notMem_empty, ↓reduceIte]
      by_cases hvG : v ∈ G.V
      · have hmv := (hvL_mem v).mpr hvG
        obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem hmv
        exact (hzeroB j (by omega)).2
      · rcases hchgB (dgVPresBase auxPtr + v) with heq | ⟨j, _, hj, had⟩
        · simpa [hvG] using heq.trans (hvpA v hv)
        · exfalso
          have hmem : vL[j] ∈ G.V := (hvL_mem _).mp (List.getElem_mem hj)
          have hveq : v = vL[j] := by simp [dgVPresBase] at had; omega
          exact hvG (hveq ▸ hmem)
    · intro e he
      dsimp only
      rw [Function.update_of_ne (by simp [dgNOff, dgEPresBase]; omega)]
      simp only [emptyMGraph, Finset.notMem_empty, ↓reduceIte]
      rcases hchgB (dgEPresBase auxPtr vCap + e) with heq | ⟨j, _, hj, had⟩
      · simpa [hGE] using heq.trans (hepA e he)
      · exfalso
        have hvj : vL[j] < vCap := hvCA _ ((hvL_mem _).mp (List.getElem_mem hj))
        simp [dgEPresBase, dgVPresBase] at had; omega
    · rcases hincA with ⟨incL, hincL⟩
      rcases hincL s hs with ⟨hdll, hdeg, hmem_inc⟩
      have hinc_nil : incL s = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro h hh
        have hm := (hmem_inc h).mp hh
        rw [hGE] at hm
        exact Finset.notMem_empty _ hm.2.1
      rw [hinc_nil] at hdll hdeg
      refine ⟨?_, ?_, fun h => by simp [emptyMGraph]⟩
      · exact hdll.of_agree
          (by dsimp only; rw [Function.update_of_ne (by simp [dgNOff, dgIncHeadBase]; omega)]
              rcases hchgB (dgIncHeadBase auxPtr vCap + s) with heq | ⟨j, _, hj, had⟩
              · exact heq
              · exfalso; have hvj := hvCA _ ((hvL_mem _).mp (List.getElem_mem hj))
                simp [dgIncHeadBase, dgVPresBase] at had; omega)
          (fun h hh => by
              dsimp only; rw [Function.update_of_ne (by simp [dgNOff, dgHePrevBase]; omega)]
              rcases hchgB (dgHePrevBase auxPtr vCap eCap + h) with heq | ⟨j, _, hj, had⟩
              · exact heq
              · exfalso; have hvj := hvCA _ ((hvL_mem _).mp (List.getElem_mem hj))
                simp [dgHePrevBase, dgVPresBase] at had; omega)
          (fun h hh => by
              dsimp only; rw [Function.update_of_ne (by simp [dgNOff, dgHeNextBase]; omega)]
              rcases hchgB (dgHeNextBase auxPtr vCap eCap + h) with heq | ⟨j, _, hj, had⟩
              · exact heq
              · exfalso; have hvj := hvCA _ ((hvL_mem _).mp (List.getElem_mem hj))
                simp [dgHeNextBase, dgVPresBase] at had; omega)
      · dsimp only
        rw [Function.update_of_ne (by simp [dgNOff, dgSlotDegBase]; omega)]
        rcases hchgB (dgSlotDegBase auxPtr vCap + s) with heq | ⟨j, _, hj, had⟩
        · exact heq.trans hdeg
        · exfalso; have hvj := hvCA _ ((hvL_mem _).mp (List.getElem_mem hj))
          simp [dgSlotDegBase, dgVPresBase] at had; omega
  · intro addr ha
    dsimp only
    rw [Function.update_of_ne (by simp [dgNOff, dynGraphSize] at ha ⊢; omega)]
    exact hfrB addr ha
  · dsimp only [clearAuxGraphContract, Expr.size, startState]
    rw [hA.2.2.2.2.2.2.1]
    omega

theorem buildActiveOnAux_meetsContract {w : ℕ} {p : Program} {bPhase bOps bEdge vCap eCap : ℕ}
    {G : MGraph}
    (hp : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bPhase + phaseIdxBuildActive)
      (buildActiveOnAuxContract w vCap eCap G) := by
  refine meetsContract_of_runs
    (hp.get (i := phaseIdxBuildActive) (by simp [phaseProcs, phaseIdxBuildActive]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, auxPtr, rfl, hw16, hboundG, hboundA, hdisj, hG, hAux⟩
  have hlt_g : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_a : auxPtr < 2 ^ w := hargs auxPtr (by simp)
  have h0w : (0 : ℕ) < 2 ^ w := by omega
  have h1w : (1 : ℕ) < 2 ^ w := by omega
  have h4w : (4 : ℕ) < 2 ^ w := by omega
  have h7vw : 7 * vCap < 2 ^ w := by simp [dynGraphSize] at hboundG; omega
  have hePres_ltw : dgEPresBase gPtr vCap < 2 ^ w := by
    simp [dgEPresBase, dynGraphSize] at hboundG ⊢; omega
  have heList_ltw : dgEListBase gPtr vCap eCap < 2 ^ w := by
    simp [dgEListBase, dynGraphSize] at hboundG ⊢; omega
  have hm_ltw : G.m < 2 ^ w := by
    have : G.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (hG.2.2.1 e he)
    have : G.m ≤ eCap := by simpa [MGraph.m] using Finset.card_le_card this
    simp [dynGraphSize] at hboundG; omega
  obtain ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩ := hG.2.2.2.2.2.2.2.2.2.2.2.2.1
  let A_of : ℕ → MGraph := fun i =>
    { V := G.V.filter (fun v => ∃ e ∈ (eL.take i).toFinset, G.tail e = v ∨ G.head e = v)
      E := (eL.take i).toFinset
      tail := fun e => if e ∈ (eL.take i).toFinset then G.tail e else 0
      head := fun e => if e ∈ (eL.take i).toFinset then G.head e else 0 }
  have hA0 : DynGraphAt mem auxPtr vCap eCap (A_of 0) := by
    refine dynGraphAt_congr (G₁ := emptyMGraph) (G₂ := A_of 0)
      (by simp [A_of, emptyMGraph]) (by simp [A_of, emptyMGraph])
      (fun _ h => by cases h) hAux
  have hAGm :
      (A_of G.m).V = (activeSubgraph G).V ∧
      (A_of G.m).E = (activeSubgraph G).E ∧
      ∀ e ∈ (A_of G.m).E, (A_of G.m).tail e = (activeSubgraph G).tail e ∧
        (A_of G.m).head e = (activeSubgraph G).head e := by
    have htake : eL.take G.m = eL := by rw [← heL_len]; exact List.take_length
    have hE : (eL.take G.m).toFinset = G.E := by
      ext e; simp [htake, heL_mem]
    refine ⟨?_, ?_, ?_⟩
    · ext v
      simp only [A_of, hE, activeSubgraph, Finset.mem_filter, and_congr_right_iff]
      intro _
      unfold MGraph.deg
      constructor
      · rintro ⟨e, heE, htail | hhead⟩
        · have hpos : 0 < (G.E.filter fun e' => G.tail e' = v).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heE, htail⟩⟩
          omega
        · have hpos : 0 < (G.E.filter fun e' => G.head e' = v).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heE, hhead⟩⟩
          omega
      · intro hdeg
        by_cases htail_pos : 0 < (G.E.filter fun e' => G.tail e' = v).card
        · obtain ⟨e, he⟩ := Finset.card_pos.mp htail_pos
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
        · have hhead_pos : 0 < (G.E.filter fun e' => G.head e' = v).card := by omega
          obtain ⟨e, he⟩ := Finset.card_pos.mp hhead_pos
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
    · exact hE
    · intro e he
      simp [A_of, activeSubgraph, show e ∈ (eL.take G.m).toFinset from he]
  refine runs_start_le ?_
  dsimp only [phaseProcs, phaseIdxBuildActive, List.getElem_cons_succ, List.getElem_cons_zero,
    buildActiveOnAuxStmt]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (by eval_expr) hG.2.2.2.1) ?_
  refine runs_seq_assign_le (v := eCap) ?_ ?_
  · refine Expr.eval_load_of_eq ?_ hG.2.2.2.2.1
    rw [dgECapOff]
    simp [Expr.eval, BinOp.eval, startState, h1w,
      show gPtr + 1 < 2 ^ w by simp [dynGraphSize] at hboundG; omega]
  refine runs_seq_assign_le (v := G.m) ?_ ?_
  · refine Expr.eval_load_of_eq ?_ hG.2.2.2.2.2.2.1
    rw [dgMOff]
    simp [Expr.eval, BinOp.eval, startState, show (3 : ℕ) < 2 ^ w by omega,
      show gPtr + 3 < 2 ^ w by simp [dynGraphSize] at hboundG; omega]
  refine runs_seq_assign_le (v := dgEListBase gPtr vCap eCap) ?_ ?_
  · have hg4 : gPtr + 4 < 2 ^ w := by simp [dynGraphSize] at hboundG; omega
    have hg7 : gPtr + 4 + 7 * vCap < 2 ^ w := by simp [dynGraphSize] at hboundG; omega
    have heList' : gPtr + 4 + 7 * vCap + eCap < 2 ^ w := by simpa [dgEListBase] using heList_ltw
    simp [Expr.eval, BinOp.eval, startState, h4w, h7vw, hg4, hg7, heList', dgEListBase,
      show (7 : ℕ) < 2 ^ w by omega]
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = gPtr ∧ st.regs 1 = auxPtr ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧
    st.regs 4 = G.m ∧ st.regs 5 = dgEListBase gPtr vCap eCap ∧ st.regs 6 = i ∧
    DynGraphAt st.mem auxPtr vCap eCap (A_of i) ∧
    ∀ addr, addr < auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr
  have hLoop : Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = auxPtr ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧
        st.regs 4 = G.m ∧ st.regs 5 = dgEListBase gPtr vCap eCap ∧ st.mem = mem)
      (forRange 6 (.const 0) (.reg 4)
        (.assign 7 (.load (.bin .add (.reg 5) (.reg 6))) ;;
         .call 8 (bOps + dgIdxGetTail) [.reg 0, .reg 7] ;;
         .call 9 (bOps + dgIdxGetHead) [.reg 0, .reg 7] ;;
         .call 10 (bOps + dgIdxAddVertex) [.reg 1, .reg 8] ;;
         .call 10 (bOps + dgIdxAddVertex) [.reg 1, .reg 9] ;;
         .call 10 (bEdge + dgIdxInsertEdge) [.reg 1, .reg 7, .reg 8, .reg 9]))
      (normalPost (Inv G.m))
      (fun _ => G.m * (800 + (.reg 4 : Expr).size + 8) + ((.const 0 : Expr).size + (.reg 4 : Expr).size + 5)) := by
    refine Triple.forRange_const 800 0 G.m (Nat.zero_le _) h1w (fun _ => hm_ltw)
      (fun st ⟨hr0, hr1, hr2, hr3, hr4, hr5, hmeq⟩ => ⟨by eval_expr,
        by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4], by simp [hr5],
        by simp, by simpa [hmeq] using hA0, fun _ _ => by simp [hmeq]⟩)
      (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
      (fun i st _ _ h => by simp [Expr.eval, h.2.2.2.2.1])
      (fun i _ hi st ω hInv => by
        refine runs_start_le ?_
        rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hAi, hfr⟩
        have hi_eL : i < eL.length := by omega
        have hi_ltw : i < 2 ^ w := lt_of_lt_of_le hi hm_ltw.le
        have hi_eCap : i < eCap := by
          have hsub : G.E ⊆ Finset.range eCap := fun z hz => Finset.mem_range.mpr (hG.2.2.1 z hz)
          have hGm_le : G.m ≤ eCap := by simpa [MGraph.m] using Finset.card_le_card hsub
          omega
        have hie_ltw : dgEListBase gPtr vCap eCap + i < 2 ^ w := by
          simp [dgEListBase, dynGraphSize] at hboundG ⊢; omega
        let e := eL[i]'hi_eL
        have heG : e ∈ G.E := (heL_mem e).mp (List.getElem_mem hi_eL)
        have he_mem : st.mem (dgEListBase gPtr vCap eCap + i) = e := by
          have haddr_in : dgEListBase gPtr vCap eCap + i < gPtr + dynGraphSize vCap eCap := by
            simp [dgEListBase, dynGraphSize]; omega
          have haddr_ge : gPtr ≤ dgEListBase gPtr vCap eCap + i := by
            simp [dgEListBase]; omega
          have hfr_g : st.mem (dgEListBase gPtr vCap eCap + i) = mem (dgEListBase gPtr vCap eCap + i) :=
            hfr _ (by
              rcases hdisj with h1 | h2
              · exact Or.inl (lt_of_lt_of_le haddr_in h1)
              · exact Or.inr (le_trans h2 haddr_ge))
          exact hfr_g.trans (heL_at i hi_eL)
        have hG_st : DynGraphAt st.mem gPtr vCap eCap G := by
          refine dynGraphAt_of_agree hG fun addr ha1 ha2 => hfr addr ?_
          rcases hdisj with h1 | h2
          · exact Or.inl (lt_of_lt_of_le ha2 h1)
          · exact Or.inr (le_trans h2 ha1)
        have he_ltw : e < 2 ^ w := by have := hG.2.2.1 e heG; simp [dynGraphSize] at hboundG; omega
        have huG : G.tail e ∈ G.V := (hG.1 e heG).1
        have hvG : G.head e ∈ G.V := (hG.1 e heG).2
        have hu_vCap : G.tail e < vCap := hG.2.1 _ huG
        have hv_vCap : G.head e < vCap := hG.2.1 _ hvG
        have hu_ltw : G.tail e < 2 ^ w := by simp [dynGraphSize] at hboundG; omega
        have hv_ltw : G.head e < 2 ^ w := by simp [dynGraphSize] at hboundG; omega
        refine runs_seq_assign_le (v := e) ?_ ?_
        · exact Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr5, hr6, hie_ltw]) he_mem
        let st1 := { st with regs := Function.update st.regs 7 e }
        refine runs_seq_call_le (r := 8) (dgGetTail_meetsContract hpOps)
          (by simp [Expr.eval, evalArgs, hr0])
          (fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl <;> assumption)
          ⟨gPtr, e, rfl, hw16, hboundG, heG, hG_st⟩ ?_
        intro retT memT posT hpostT
        rcases hpostT with ⟨_, _, hEqT, hmemT, hretT⟩
        simp only [List.cons.injEq, and_true] at hEqT
        rcases hEqT with ⟨rfl, rfl⟩
        subst hmemT; subst hretT
        let st2 : State := { mem := st1.mem, regs := Function.update st1.regs 8 (G.tail e), pos := posT }
        refine runs_seq_call_le (r := 9) (dgGetHead_meetsContract hpOps)
          (by simp [Expr.eval, evalArgs, hr0])
          (fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl <;> assumption)
          ⟨gPtr, e, rfl, hw16, hboundG, heG, hG_st⟩ ?_
        intro retH memH posH hpostH
        rcases hpostH with ⟨_, _, hEqH, hmemH, hretH⟩
        simp only [List.cons.injEq, and_true] at hEqH
        rcases hEqH with ⟨rfl, rfl⟩
        subst hmemH; subst hretH
        let st3 : State := { mem := st2.mem, regs := Function.update st2.regs 9 (G.head e), pos := posH }
        refine runs_seq_call_le (r := 10) (dgAddVertex_meetsContract hpOps)
          (by simp [Expr.eval, evalArgs, hr1])
          (fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl <;> assumption)
          ⟨auxPtr, G.tail e, rfl, hw16, hboundA, hu_vCap, hAi⟩ ?_
        intro retV1 memV1 posV1 hpostV1
        rcases hpostV1 with ⟨_, _, hEqV1, _, hAV1, hfrV1⟩
        simp only [List.cons.injEq, and_true] at hEqV1
        rcases hEqV1 with ⟨rfl, rfl⟩
        let st4 : State := { mem := memV1, regs := Function.update st3.regs 10 retV1, pos := posV1 }
        refine runs_seq_call_le (r := 10) (dgAddVertex_meetsContract hpOps)
          (by simp [Expr.eval, evalArgs, hr1])
          (fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl <;> assumption)
          ⟨auxPtr, G.head e, rfl, hw16, hboundA, hv_vCap, hAV1⟩ ?_
        intro retV2 memV2 posV2 hpostV2
        rcases hpostV2 with ⟨_, _, hEqV2, _, hAV2, hfrV2⟩
        simp only [List.cons.injEq, and_true] at hEqV2
        rcases hEqV2 with ⟨rfl, rfl⟩
        let st5 : State := { mem := memV2, regs := Function.update st4.regs 10 retV2, pos := posV2 }
        refine runs_call_le (r := 10) (dgInsertEdge_meetsContract hpEdge hpOps)
          (by simp [Expr.eval, evalArgs, hr1])
          (fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> assumption)
          ⟨auxPtr, e, G.tail e, G.head e, rfl, hw16, hboundA,
            by simp, by simp [Finset.mem_insert], hAV2⟩ ?_
        intro retE memE posE hpostE
        rcases hpostE with ⟨_, _, _, _, hEqE, _, hAE, hfrE⟩
        simp only [List.cons.injEq, and_true] at hEqE
        rcases hEqE with ⟨rfl, rfl, rfl, rfl⟩
        have he_lt_eCap : e < eCap := hG.2.2.1 e heG
        have he_not_mem_take : e ∉ eL.take i := by
          intro hmem_take
          obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem hmem_take
          have hje : j < i := lt_of_lt_of_le hj (by simp)
          rw [List.getElem_take] at hj_eq
          have hinj := (List.nodup_iff_injective_getElem.mp heL_nd)
            (a₁ := ⟨j, by omega⟩) (a₂ := ⟨i, hi_eL⟩) hj_eq
          exact Nat.ne_of_lt hje (congrArg Fin.val hinj)
        have he_not_A : e ∉ (A_of i).E := by
          simpa [A_of] using he_not_mem_take
        simp only [he_lt_eCap, he_not_A, not_false_eq_true, and_self, ↓reduceIte] at hAE
        have htake_succ : (eL.take (i + 1)).toFinset = insert e (eL.take i).toFinset := by
          rw [List.take_succ_eq_append_getElem hi_eL]
          ext x
          simp only [List.toFinset_append, Finset.mem_union, List.toFinset_cons,
            List.toFinset_nil, insert_empty_eq, Finset.mem_singleton, Finset.mem_insert,
            List.mem_toFinset]
          exact or_comm
        have hAE_next : DynGraphAt memE auxPtr vCap eCap (A_of (i + 1)) := by
          refine dynGraphAt_congr (G₁ := _ ) (G₂ := A_of (i + 1)) ?_ ?_ ?_ hAE
          · ext z
            simp only [MGraph.applyUpdate, A_of, htake_succ, Finset.mem_insert, Finset.mem_filter]
            constructor
            · rintro (rfl | rfl | ⟨hzG, e', he', hend⟩)
              · exact ⟨hvG, e, Or.inl rfl, Or.inr rfl⟩
              · exact ⟨huG, e, Or.inl rfl, Or.inl rfl⟩
              · exact ⟨hzG, e', Or.inr he', hend⟩
            · rintro ⟨hzG, e', rfl | he', htail | hhead⟩
              · exact Or.inr (Or.inl htail.symm)
              · exact Or.inl hhead.symm
              · exact Or.inr (Or.inr ⟨hzG, e', he', Or.inl htail⟩)
              · exact Or.inr (Or.inr ⟨hzG, e', he', Or.inr hhead⟩)
          · simp [MGraph.applyUpdate, A_of, htake_succ]
          · intro e' he'
            simp only [MGraph.applyUpdate, A_of] at he' ⊢
            rcases Finset.mem_insert.mp he' with rfl | he'_in
            · simp [Function.update_self, htake_succ]
            · have hne : e' ≠ e := fun h => he_not_mem_take (h ▸ List.mem_toFinset.mp he'_in)
              have he'_take1 : e' ∈ (eL.take (i + 1)).toFinset :=
                htake_succ ▸ Finset.mem_insert_of_mem he'_in
              simp [Function.update_of_ne hne, List.mem_toFinset.mp he'_in, he'_take1]
        refine ⟨⟨⟨by simp [hr0], by simp [hr1],
          by simp [hr2], by simp [hr3],
          by simp [hr4], by simp [hr5],
          by simp, hAE_next,
          fun addr ha => (hfrE addr ha).trans ((hfrV2 addr ha).trans ((hfrV1 addr ha).trans (hfr addr ha)))⟩,
          by simp [hr6]⟩, ?_⟩
        dsimp only [dgGetTailContract, dgGetHeadContract, dgAddVertexContract, dgInsertEdgeContract,
          argsSize, Expr.size]
        omega)
  refine runs_seq_triple_le hLoop ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  intro stF ⟨_, _, _, _, _, _, _, hAF, hfrF⟩
  refine runs_ret_le (by eval_expr) ⟨gPtr, auxPtr, rfl, rfl, ?_, hfrF⟩ ?_
  · exact dynGraphAt_congr hAGm.1 hAGm.2.1 hAGm.2.2 hAF
  · dsimp only [buildActiveOnAuxContract, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program

