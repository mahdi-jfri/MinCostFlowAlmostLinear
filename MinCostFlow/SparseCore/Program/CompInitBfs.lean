module

public import MinCostFlow.SparseCore.Program.CompInitBfsInner
import WordRAM.Tactic

/-!
# Connected-Component BFS Discovery (`CompInitBfs`)

Proves `compBfsComp_meetsContract`, verifying the outer BFS queue loop and full contract of
`compBfsCompProc` in `O(n_C + m_C + 1)` Word-RAM steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Execution and invariant preservation of the outer BFS queue loop `compBfsOuterLoop`. -/
lemma compBfsOuter_runs {w vCap eCap : ℕ} {G₀ : MGraph} {C visSet : Finset ℕ}
    {mem : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    (ctx : BfsCtx w vCap eCap G₀ C visSet mem)
    (rem qHead : ℕ) (qL : List ℕ) (eL : List (ℕ × ℕ × ℕ)) (st : State) :
    qHead ≤ qL.length → (compGraph G₀ C).n - qHead = rem →
    ctx.v0 ∈ qL →
    BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
      ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st.regs →
    st.regs 18 = qHead → st.regs 19 = qL.length → st.regs 20 = eL.length →
    BfsMemInv mem st.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
      ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL eL →
    (∀ e ∈ G₀.E, (∃ t ∈ eL, t.1 = e) ↔ G₀.tail e ∈ qL.take qHead) →
    (∀ u ∈ qL.take qHead, ∀ e ∈ G₀.E,
      (G₀.tail e = u → G₀.head e ∈ qL) ∧ (G₀.head e = u → G₀.tail e ∈ qL)) →
    ∃ st' qL' eL' c_out,
      Runs w p ω compBfsOuterLoop st .normal st' c_out ∧
      BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
        ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st'.regs ∧
      st'.regs 19 = (compGraph G₀ C).n ∧ st'.regs 20 = (compGraph G₀ C).m ∧
      qL'.length = (compGraph G₀ C).n ∧ (∀ x, x ∈ qL' ↔ x ∈ C) ∧
      eL'.length = (compGraph G₀ C).m ∧ (∀ e ∈ compEdgeSet G₀ C, ∃ t ∈ eL', t.1 = e) ∧
      BfsMemInv mem st'.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
        ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL' eL' ∧
      c_out ≤ 80 * rem + 160 * ((C \ (qL.take qHead).toFinset).sum fun u =>
        (ctx.incL (mem (dgExtToIntBase ctx.g0Ptr vCap + u))).length) + 6 := by
  classical
  have hG₀ := ctx.hdg.1
  have hVlt := ctx.hdg.2.1
  have hE2I := ctx.hdg.2.2.2.2.2.2.2.2.2.1
  have hC_sub := ctx.hC_sub
  have hw1 : 1 < 2 ^ w := by have := ctx.hw16; omega
  have hg0_w := ctx.hg0_w
  have hbq_w := ctx.hbq_w
  set extToInt := dgExtToIntBase ctx.g0Ptr vCap
  set incHead := dgIncHeadBase ctx.g0Ptr vCap
  induction rem generalizing qHead qL eL st with
  | zero =>
    intro hqh hrem hv0_q hR hr18 hr19 hr20 hInv heChar hclosed
    have hq_le : qL.length ≤ (compGraph G₀ C).n := bfs_qL_len_le hInv.1 hInv.2.1
    have hq_eq : qHead = qL.length := by omega
    have hq_n : qL.length = (compGraph G₀ C).n := by omega
    have hall : ∀ x, x ∈ qL ↔ x ∈ C := compBfs_reach_all hG₀ ctx.hC ctx.hv0 hv0_q hInv.2.1
      (by simpa [hq_eq, List.take_length] using hclosed)
    have he_cov : ∀ e ∈ compEdgeSet G₀ C, ∃ t ∈ eL, t.1 = e := fun e heC => by
      have ⟨heG, htC, _⟩ := mem_compEdgeSet_endpoints hG₀ ctx.hC heC
      exact (heChar e heG).mpr (by rw [hq_eq, List.take_length]; exact (hall _).mpr htC)
    have he_m : eL.length = (compGraph G₀ C).m := by
      have hle := bfs_eL_len_le hInv.2.2.2.1 hInv.2.2.2.2.2.1
      have hge : (compGraph G₀ C).m ≤ eL.length := by
        have : compEdgeSet G₀ C ⊆ (eL.map Prod.fst).toFinset := fun e he => by
          obtain ⟨t, ht, rfl⟩ := he_cov e he
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)
        calc (compGraph G₀ C).m ≤ (eL.map Prod.fst).toFinset.card := Finset.card_le_card this
          _ = eL.length := by rw [List.toFinset_card_of_nodup hInv.2.2.2.1, List.length_map]
      omega
    refine ⟨st, qL, eL, 4,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr18, hr19, hq_eq],
        rfl, rfl, by simp [Expr.size]⟩),
      hR, by omega, by omega, hq_n, hall, he_m, he_cov, hInv, by omega⟩
  | succ rem ih =>
    intro hqh hrem hv0_q hR hr18 hr19 hr20 hInv heChar hclosed
    by_cases hdone : qHead = qL.length
    · have hall : ∀ x, x ∈ qL ↔ x ∈ C := compBfs_reach_all hG₀ ctx.hC ctx.hv0 hv0_q hInv.2.1
        (by simpa [hdone, List.take_length] using hclosed)
      have hq_n : qL.length = (compGraph G₀ C).n := by
        rw [← List.toFinset_card_of_nodup hInv.1]
        exact congrArg Finset.card (by ext x; simp [hall, compGraph])
      omega
    · have hqlt : qHead < qL.length := by omega
      set u := qL[qHead]
      have huC : u ∈ C := hInv.2.1 u (List.getElem_mem hqlt)
      have hu_lt : u < vCap := hVlt u (hC_sub huC)
      set su := mem (extToInt + u)
      have hsu_lt : su < vCap := hVlt su (hE2I u (hC_sub huC)).1
      have hDLL_u := (ctx.hincFull su hsu_lt).1
      have hg0_st := ctx.hg0_agree hInv.2.2.2.2.2.2.2.2.2.2.2
      have hu_m : st.mem (ctx.bfsQBase + qHead) = u := hInv.2.2.1 qHead hqlt
      have hsu_m : st.mem (extToInt + u) = su :=
        hg0_st _ (by dsimp [extToInt, dgExtToIntBase]; omega)
          (by dsimp [extToInt, dgExtToIntBase, dynGraphSize]; omega)
      have hhd_val : st.mem (incHead + su) = (if h0 : 0 < (ctx.incL su).length then (ctx.incL su)[0] + 1 else 0) := by
        rw [hg0_st _ (by dsimp [incHead, dgIncHeadBase]; omega)
          (by dsimp [incHead, dgIncHeadBase, dynGraphSize]; omega), hDLL_u.2.2.1]
        cases ctx.incL su <;> simp
      have hhd_lt : st.mem (incHead + su) < 2 ^ w := by
        rw [hhd_val]; split_ifs with h0
        · have := hDLL_u.2.1 _ (List.getElem_mem h0); dsimp [dynGraphSize] at hg0_w; omega
        · omega
      have hq_le := bfs_qL_len_le hInv.1 hInv.2.1
      let st1 : State := { st with regs := Function.update st.regs 21 u }
      let st2 : State := { st1 with regs := Function.update st1.regs 18 (qHead + 1) }
      let st3 : State := { st2 with regs := Function.update st2.regs 22 su }
      let st4 : State := { st3 with regs := Function.update st3.regs 23 (st.mem (incHead + su)) }
      have hp1 : Runs w p ω (.assign 21 (.load (.bin .add (.reg 5) (.reg 18)))) st .normal st1 5 :=
        runs_assign_iff.mpr ⟨u, Expr.eval_load_of_eq (by have := hR.r5; eval_expr) hu_m,
          rfl, rfl, by simp [Expr.size]⟩
      have hp2 : Runs w p ω (.assign 18 (.bin .add (.reg 18) (.const 1))) st1 .normal st2 4 :=
        runs_assign_iff.mpr ⟨qHead + 1, by simp [st1, Expr.eval, BinOp.eval, hr18, hw1, show qHead + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hp3 : Runs w p ω (.assign 22 (.load (.bin .add (.reg 12) (.reg 21)))) st2 .normal st3 5 :=
        runs_assign_iff.mpr ⟨su, Expr.eval_load_of_eq (by
            have := hR.r12
            simp [st2, st1, Expr.eval, BinOp.eval, this, extToInt, show dgExtToIntBase ctx.g0Ptr vCap + u < 2 ^ w by
              dsimp [dgExtToIntBase, dynGraphSize] at hg0_w ⊢; omega]) hsu_m,
          rfl, rfl, by simp [Expr.size]⟩
      have hp4 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 14) (.reg 22)))) st3 .normal st4 5 :=
        runs_assign_iff.mpr ⟨st.mem (incHead + su), Expr.eval_load_of_eq (by
            have := hR.r14
            simp [st3, st2, st1, Expr.eval, BinOp.eval, this, incHead, show dgIncHeadBase ctx.g0Ptr vCap + su < 2 ^ w by
              dsimp [dgIncHeadBase, dynGraphSize] at hg0_w ⊢; omega]) rfl,
          rfl, rfl, by simp [Expr.size]⟩
      have huNot : u ∉ qL.take qHead := fun hm => by
        obtain ⟨j, hj, hju⟩ := List.getElem_of_mem hm
        rw [List.length_take, Nat.min_eq_left (le_of_lt hqlt)] at hj
        rw [List.getElem_take] at hju
        have := hInv.1.getElem_inj_iff.mp hju; omega
      have hR4 : BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
          ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st4.regs :=
        (((hR.update_ge18 (by omega)).update_ge18 (by omega)).update_ge18 (by omega)).update_ge18 (by omega)
      obtain ⟨st_m, qL1, eL1, c_in, hrun_in, hRm, hm18, hm19, hm20, hq1_le, hq1_take, hq1_sub,
        hInv_m, heChar1, hnb1, hcin⟩ := compBfsInner_runs ctx u huC (qHead + 1) (ctx.incL su).length 0 qL eL st4
        (Nat.zero_le _) (Nat.sub_zero _) hqlt (by simpa using huNot) hR4
        (by simp [st4, st3, st2]) (by simp [st4, st3, st2, st1, hr19]) (by simp [st4, st3, st2, st1, hr20])
        (by simpa [st4] using hhd_val) hInv
        (fun e' heG' => by simp [heChar e' heG']) (fun _ hh => by simp at hh)
      have hstep_run : Runs w p ω _ st .normal st_m (23 + c_in) :=
        runs_seq_iff.mpr (Or.inr ⟨st1, 5, 17 + c_in, hp1,
          runs_seq_iff.mpr (Or.inr ⟨st2, 4, 12 + c_in, hp2,
            runs_seq_iff.mpr (Or.inr ⟨st3, 5, 6 + c_in, hp3,
              runs_seq_iff.mpr (Or.inr ⟨st4, 5, c_in, hp4, hrun_in, by omega⟩), by omega⟩), by omega⟩), by omega⟩)
      have htake_succ : qL1.take (qHead + 1) = qL.take qHead ++ [u] := by
        rw [hq1_take, List.take_succ_eq_append_getElem hqlt]
      have hrem_sum : (C \ (qL.take qHead).toFinset).sum (fun w' => (ctx.incL (mem (extToInt + w'))).length) =
          (ctx.incL su).length +
          (C \ (qL1.take (qHead + 1)).toFinset).sum (fun w' => (ctx.incL (mem (extToInt + w'))).length) := by
        have hu_in_diff : u ∈ C \ (qL.take qHead).toFinset :=
          Finset.mem_sdiff.mpr ⟨huC, by simp [huNot]⟩
        have hsdiff_eq : (C \ (qL.take qHead).toFinset).erase u = C \ (qL1.take (qHead + 1)).toFinset := by
          ext w'; simp only [Finset.mem_erase, Finset.mem_sdiff, htake_succ, List.toFinset_append,
            List.toFinset_cons, List.toFinset_nil, Finset.mem_union, Finset.mem_insert,
            Finset.notMem_empty, or_false]
          tauto
        rw [← Finset.add_sum_erase _ _ hu_in_diff, hsdiff_eq]
      obtain ⟨st', qL', eL', c_rec, hrun_r, hR', hr19', hr20', hq_n', hall', he_m', he_cov',
        hInv', hcr⟩ := ih (qHead + 1) qL1 eL1 st_m (by omega) (by omega) (hq1_sub ctx.v0 hv0_q)
        hRm hm18 hm19 hm20 hInv_m
        (fun e' heG' => by
          rw [htake_succ, List.mem_append, List.mem_singleton]
          simpa using heChar1 e' heG')
        (fun w' hw' e' heG' => by
          rw [htake_succ, List.mem_append, List.mem_singleton] at hw'
          rcases hw' with hw1 | rfl
          · exact ⟨fun ht => hq1_sub _ ((hclosed w' hw1 e' heG').1 ht),
              fun hh => hq1_sub _ ((hclosed w' hw1 e' heG').2 hh)⟩
          · exact hnb1 e' heG')
      refine ⟨st', qL', eL', 3 + (23 + c_in) + c_rec + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st_m, 23 + c_in, c_rec,
          by simp [Expr.eval, BinOp.eval, hr18, hr19, hqlt, hw1], by decide,
          hstep_run, hrun_r, by simp [Expr.size]⟩)),
        hR', hr19', hr20', hq_n', hall', he_m', he_cov', hInv', by omega⟩

/-- Verification of `compBfsCompProc`. -/
theorem compBfsComp_meetsContract {w vCap eCap b : ℕ} {G₀ : MGraph} {C visSet : Finset ℕ}
    {p : Program} (hp : p.procs[b]? = some compBfsCompProc) :
    MeetsContract w p b (compBfsCompContract w vCap eCap G₀ C visSet) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase,
    v0, c, outM0Addr, rfl, hw16, hdg, hC, hv0, hvisSub, hvisDisj, hvisAt, hc_lt,
    hg0_w, hvis_w, hvc_w, hec1_w, hec2_w, hbq_w, hce_w, hm0_w,
    hd_gv, hd_gvc, hd_ge1, hd_ge2, hd_gbq, hd_gce, hd_gm0,
    hd_vvc, hd_ve1, hd_ve2, hd_vbq, hd_vce, hd_vm0,
    hd_vce1, hd_vce2, hd_vcbq, hd_vcce, hd_vcm0,
    hd_e1e2, hd_e1bq, hd_e1ce, hd_e1m0,
    hd_e2bq, hd_e2ce, hd_e2m0,
    hd_bqce, hd_bqm0, hd_cem0⟩
  obtain ⟨incL, hincFull⟩ := hdg.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let ctx : BfsCtx w vCap eCap G₀ C visSet mem :=
    { g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase, v0, c, outM0Addr,
      hw16, hdg, incL,
      hincFull := fun s hs => ⟨(hincFull s hs).1, (hincFull s hs).1.2.1, (hincFull s hs).2.2⟩,
      hC, hv0, hvisSub, hvisDisj, hvisAt, hc_lt,
      hg0_w, hvis_w, hvc_w, hec1_w, hec2_w, hbq_w, hce_w, hm0_w,
      hd_gv, hd_gvc, hd_ge1, hd_ge2, hd_gbq, hd_gce, hd_gm0,
      hd_vvc, hd_ve1, hd_ve2, hd_vbq, hd_vce, hd_vm0,
      hd_vce1, hd_vce2, hd_vcbq, hd_vcce, hd_vcm0,
      hd_e1e2, hd_e1bq, hd_e1ce, hd_e1m0,
      hd_e2bq, hd_e2ce, hd_e2m0,
      hd_bqce, hd_bqm0, hd_cem0 }
  have hVlt := hdg.2.1
  have hElt := hdg.2.2.1
  have hC_sub := ctx.hC_sub
  have hw1 : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  set extToInt := dgExtToIntBase g0Ptr vCap
  set intToExt := dgIntToExtBase g0Ptr vCap
  set incHead := dgIncHeadBase g0Ptr vCap
  set eTailSlot := dgETailSlotBase g0Ptr vCap eCap
  set eHeadSlot := dgEHeadSlotBase g0Ptr vCap eCap
  set heNext := dgHeNextBase g0Ptr vCap eCap
  refine runs_start_le ?_
  unfold compBfsCompProc
  have h3v_w : 3 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h4v_w : 4 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h6v_w : 6 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h7v_w : 7 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h3e_w : 3 * eCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h4e_w : 4 * eCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have h7e_w : 7 * eCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have hg4_w : g0Ptr + 4 < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have hg47v_w : g0Ptr + 4 + 7 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
  have hbase_w : g0Ptr + 4 + 3 * vCap < 2 ^ w ∧ g0Ptr + 4 + 4 * vCap < 2 ^ w ∧
      g0Ptr + 4 + 6 * vCap < 2 ^ w ∧ g0Ptr + 4 + 7 * vCap + 3 * eCap < 2 ^ w ∧
      g0Ptr + 4 + 7 * vCap + 4 * eCap < 2 ^ w ∧ g0Ptr + 4 + 7 * vCap + 7 * eCap < 2 ^ w := by
    dsimp [dynGraphSize] at hg0_w; omega
  have hv0_lt : v0 < vCap := hVlt v0 (hC_sub hv0)
  have hnC_pos : 1 ≤ (compGraph G₀ C).n := Finset.card_pos.mpr ⟨v0, hv0⟩
  have hInv0 : BfsMemInv mem (Function.update (Function.update (Function.update mem (visBase + v0) 1)
      (vCompBase + v0) c) bfsQBase v0) vCap eCap visBase vCompBase edgeC1Base edgeC2Base bfsQBase
      compEdgesBase outM0Addr c G₀ C visSet [v0] [] := by
    refine ⟨List.nodup_singleton _, fun u hu => by simp at hu; exact hu ▸ hv0,
      fun i hi => by simp at hi; subst hi; simp, List.nodup_nil, fun _ hi => by simp at hi,
      fun _ h => by simp at h, ?_, ?_, ?_, fun _ h => by simp at h, ?_, ?_⟩
    · intro v hv
      rw [Function.update_of_ne (by rcases hd_vbq with h | h <;> omega),
        Function.update_of_ne (by rcases hd_vvc with h | h <;> omega)]
      by_cases hv0e : v = v0
      · subst hv0e; simp
      · rw [Function.update_of_ne (by omega), hvisAt v hv]; simp [hv0e]
    · intro u hu; simp only [List.mem_singleton] at hu; subst hu
      rw [Function.update_of_ne (by rcases hd_vcbq with h | h <;> omega), Function.update_self]
    · intro u hu hun
      have hne : u ≠ v0 := fun h => hun (by simp [h])
      rw [Function.update_of_ne (by rcases hd_vcbq with h | h <;> omega),
        Function.update_of_ne (by omega),
        Function.update_of_ne (by rcases hd_vvc with h | h <;> omega)]
    · intro e he _
      rw [Function.update_of_ne (by rcases hd_e1bq with h | h <;> omega),
        Function.update_of_ne (by rcases hd_vce1 with h | h <;> omega),
        Function.update_of_ne (by rcases hd_ve1 with h | h <;> omega),
        Function.update_of_ne (by rcases hd_e2bq with h | h <;> omega),
        Function.update_of_ne (by rcases hd_vce2 with h | h <;> omega),
        Function.update_of_ne (by rcases hd_ve2 with h | h <;> omega)]
      exact ⟨rfl, rfl⟩
    · intro a ha1 ha2 ha3 ha4 ha5 ha6 ha7
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  have hsum_deg := compBfs_sum_incLen hdg hC (fun s hs => ⟨(hincFull s hs).1.1, (hincFull s hs).2.2⟩)
  have htail : ∀ (st0 : State) (cp : ℕ),
      BfsRegsOK g0Ptr visBase vCompBase edgeC1Base edgeC2Base bfsQBase compEdgesBase
        c outM0Addr vCap eCap st0.regs →
      st0.regs 18 = 0 → st0.regs 19 = 1 → st0.regs 20 = 0 →
      BfsMemInv mem st0.mem vCap eCap visBase vCompBase edgeC1Base edgeC2Base bfsQBase
        compEdgesBase outM0Addr c G₀ C visSet [v0] [] →
      cp ≤ 165 →
      ∃ o st' c_tail,
        Runs w p ω (compBfsOuterLoop ;; .store (.reg 9) (.reg 20) ;; .ret (.reg 19)) st0 o st' c_tail ∧
        (compBfsCompContract w vCap eCap G₀ C visSet).post
          [g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase, v0, c, outM0Addr]
          mem o.value st'.mem ∧
        cp + c_tail ≤ (compBfsCompContract w vCap eCap G₀ C visSet).cost
          [g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase, v0, c, outM0Addr] mem := by
    intro st0 cp hR0 hr18 hr19 hr20 hInv_st0 hcp
    obtain ⟨stF, qL', eL', c_out, hrun_out, hRF, hr19F, hr20F, hq_n, hall, he_m, he_cov, hInvF, hcout⟩ :=
      compBfsOuter_runs ctx (compGraph G₀ C).n 0 [v0] [] st0
        (by simp) (Nat.sub_zero _) (by simp [ctx]) hR0 hr18 hr19 hr20 hInv_st0
        (fun _ _ => by simp) (fun _ h => by simp at h)
    have hdeg_le : (C \ ([v0].take 0).toFinset).sum (fun u => (ctx.incL (mem (dgExtToIntBase ctx.g0Ptr vCap + u))).length) =
        2 * (compGraph G₀ C).m := by simpa [ctx, extToInt] using hsum_deg
    have hrun_st : Runs w p ω (.store (.reg 9) (.reg 20)) stF .normal
        { stF with mem := Function.update stF.mem outM0Addr (compGraph G₀ C).m } 3 :=
      runs_store_iff.mpr ⟨outM0Addr, (compGraph G₀ C).m,
        by simp [Expr.eval, hRF.r9, ctx],
        by simp [Expr.eval, hr20F],
        rfl, rfl, by simp [Expr.size]⟩
    have hrun_ret : Runs w p ω (.ret (.reg 19))
        { stF with mem := Function.update stF.mem outM0Addr (compGraph G₀ C).m }
        (.returned (compGraph G₀ C).n)
        { stF with mem := Function.update stF.mem outM0Addr (compGraph G₀ C).m } 2 :=
      runs_ret_iff.mpr ⟨(compGraph G₀ C).n,
        by simp [Expr.eval, hr19F],
        rfl, rfl, by simp [Expr.size]⟩
    refine ⟨.returned (compGraph G₀ C).n,
      { stF with mem := Function.update stF.mem outM0Addr (compGraph G₀ C).m },
      c_out + 7,
      runs_seq_iff.mpr (Or.inr ⟨stF, c_out, 6, hrun_out,
        runs_seq_iff.mpr (Or.inr ⟨_, 3, 2, hrun_st, hrun_ret, rfl⟩), by omega⟩),
      ?_, by simp [compBfsCompContract]; omega⟩
    dsimp only [Outcome.value]
    refine ⟨g0Ptr, visBase, vCompBase, edgeC1Base, edgeC2Base, bfsQBase, compEdgesBase, v0, c, outM0Addr,
      rfl, rfl, Function.update_self _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [Function.update_of_ne (by rcases hd_vm0 with h | h <;> omega), hInvF.2.2.2.2.2.2.1 v hv]
      simp [hall]
    · intro u hu
      have hu_lt : u < vCap := hVlt u (hC_sub hu)
      rw [Function.update_of_ne (by rcases hd_vcm0 with h | h <;> omega)]
      exact hInvF.2.2.2.2.2.2.2.1 u ((hall u).mpr hu)
    · intro u hu hun
      rw [Function.update_of_ne (by rcases hd_vcm0 with h | h <;> omega)]
      exact hInvF.2.2.2.2.2.2.2.2.1 u hu (fun h => hun ((hall u).mp h))
    · intro e heC
      have he_lt : e < eCap := hElt e (Finset.filter_subset _ _ heC)
      obtain ⟨t, ht, hte⟩ := he_cov e heC
      rw [Function.update_of_ne (by rcases hd_e1m0 with h | h <;> omega),
        Function.update_of_ne (by rcases hd_e2m0 with h | h <;> omega)]
      simpa [hte] using hInvF.2.2.2.2.2.2.2.2.2.1 t ht
    · intro e he hen
      rw [Function.update_of_ne (by rcases hd_e1m0 with h | h <;> omega),
        Function.update_of_ne (by rcases hd_e2m0 with h | h <;> omega)]
      exact hInvF.2.2.2.2.2.2.2.2.2.2.1 e he fun t ht hte => hen (hte ▸ (hInvF.2.2.2.2.2.1 t ht).1)
    · refine ⟨qL', hq_n, hInvF.1, hall, fun i hi => ?_⟩
      rw [Function.update_of_ne (by rcases hd_bqm0 with h | h <;> omega)]
      exact hInvF.2.2.1 i hi
    · refine ⟨eL', he_m, hInvF.2.2.2.1, fun i hi => ?_, hInvF.2.2.2.2.2.1, he_cov⟩
      have ha := hInvF.2.2.2.2.1 i hi
      exact ⟨by rw [Function.update_of_ne (by rcases hd_cem0 with h | h <;> omega)]; exact ha.1,
        by rw [Function.update_of_ne (by rcases hd_cem0 with h | h <;> omega)]; exact ha.2.1,
        by rw [Function.update_of_ne (by rcases hd_cem0 with h | h <;> omega)]; exact ha.2.2⟩
    · intro a ha1 ha2 ha3 ha4 ha5 ha6 ha7
      rw [Function.update_of_ne ha7]
      exact hInvF.2.2.2.2.2.2.2.2.2.2.2 a ha1 ha2 ha3 ha4 ha5 ha6 ha7
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dgVCapOff, show g0Ptr < 2 ^ w by omega]) hdg.2.2.2.1) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dgECapOff, hw1, show g0Ptr + 1 < 2 ^ w by omega]) hdg.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := extToInt) (by simp [Expr.eval, BinOp.eval, startState, extToInt, dgExtToIntBase, hw3, hw4, hg4_w, h3v_w, hbase_w.1]) ?_
  refine runs_seq_assign_le (v := intToExt) (by simp [Expr.eval, BinOp.eval, startState, intToExt, dgIntToExtBase, hw4, hg4_w, h4v_w, hbase_w.2.1]) ?_
  refine runs_seq_assign_le (v := incHead) (by simp [Expr.eval, BinOp.eval, startState, incHead, dgIncHeadBase, hw4, hw6, hg4_w, h6v_w, hbase_w.2.2.1]) ?_
  refine runs_seq_assign_le (v := eTailSlot) (by simp [Expr.eval, BinOp.eval, startState, eTailSlot, dgETailSlotBase, hw3, hw4, hw7, hg4_w, h7v_w, hg47v_w, h3e_w, hbase_w.2.2.2.1]) ?_
  refine runs_seq_assign_le (v := eHeadSlot) (by simp [Expr.eval, BinOp.eval, startState, eHeadSlot, dgEHeadSlotBase, hw4, hw7, hg4_w, h7v_w, hg47v_w, h4e_w, hbase_w.2.2.2.2.1]) ?_
  refine runs_seq_assign_le (v := heNext) (by simp [Expr.eval, BinOp.eval, startState, heNext, dgHeNextBase, hw4, hw7, hg4_w, h7v_w, hg47v_w, h7e_w, hbase_w.2.2.2.2.2]) ?_
  refine runs_seq_store_le (x := visBase + v0) (v := 1) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := vCompBase + v0) (v := c) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := bfsQBase) (v := v0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  exact htail _ _
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp, by simp, by simp [extToInt], by simp [intToExt],
     by simp [incHead], by simp [eTailSlot], by simp [eHeadSlot], by simp [heNext]⟩
    (by simp) (by simp) (by simp) (by simpa [startState] using hInv0) (by simp [Expr.size])

end

end MinCostFlow.SparseCore.Program
