module

public import MinCostFlow.SparseCore.Program.CompInitBfsBase
import WordRAM.Tactic

/-!
# Connected-Component BFS Discovery: Inner Incidence Loop (`CompInitBfsInner`)

Proves `compBfsInner_runs`, verifying the inner incidence-list traversal loop `compBfsInnerLoop`
of `compBfsCompProc`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Execution and invariant preservation of the inner incidence-list loop `compBfsInnerLoop`. -/
lemma compBfsInner_runs {w vCap eCap : ℕ} {G₀ : MGraph} {C visSet : Finset ℕ}
    {mem : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    (ctx : BfsCtx w vCap eCap G₀ C visSet mem)
    (u : ℕ) (huC : u ∈ C) (qHead rem k : ℕ)
    (qL : List ℕ) (eL : List (ℕ × ℕ × ℕ)) (st : State) :
    let su := mem (dgExtToIntBase ctx.g0Ptr vCap + u)
    k ≤ (ctx.incL su).length → (ctx.incL su).length - k = rem →
    qHead ≤ qL.length → u ∉ qL.take (qHead - 1) →
    BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
      ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st.regs →
    st.regs 18 = qHead → st.regs 19 = qL.length → st.regs 20 = eL.length →
    st.regs 23 = (if hk : k < (ctx.incL su).length then (ctx.incL su)[k] + 1 else 0) →
    BfsMemInv mem st.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
      ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL eL →
    (∀ e ∈ G₀.E, (∃ t ∈ eL, t.1 = e) ↔
      G₀.tail e ∈ qL.take (qHead - 1) ∨ (G₀.tail e = u ∧ 2 * e ∈ (ctx.incL su).take k)) →
    (∀ h ∈ (ctx.incL su).take k,
      (h % 2 = 0 → G₀.head (h / 2) ∈ qL) ∧ (h % 2 ≠ 0 → G₀.tail (h / 2) ∈ qL)) →
    ∃ st' qL' eL' c_in,
      Runs w p ω compBfsInnerLoop st .normal st' c_in ∧
      BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
        ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st'.regs ∧
      st'.regs 18 = qHead ∧ st'.regs 19 = qL'.length ∧ st'.regs 20 = eL'.length ∧
      qL.length ≤ qL'.length ∧ qL'.take qHead = qL.take qHead ∧
      (∀ x ∈ qL, x ∈ qL') ∧
      BfsMemInv mem st'.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
        ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL' eL' ∧
      (∀ e ∈ G₀.E, (∃ t ∈ eL', t.1 = e) ↔ G₀.tail e ∈ qL.take (qHead - 1) ∨ G₀.tail e = u) ∧
      (∀ e ∈ G₀.E, (G₀.tail e = u → G₀.head e ∈ qL') ∧ (G₀.head e = u → G₀.tail e ∈ qL')) ∧
      c_in ≤ 160 * rem + 4 := by
  classical
  have hG₀ := ctx.hdg.1
  have hVlt := ctx.hdg.2.1
  have hElt := ctx.hdg.2.2.1
  have hE2I := ctx.hdg.2.2.2.2.2.2.2.2.2.1
  have hEnds := ctx.hdg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC_sub := ctx.hC_sub
  have hw1 : 1 < 2 ^ w := by have := ctx.hw16; omega
  have hw2 : 2 < 2 ^ w := by have := ctx.hw16; omega
  have hw3 : 3 < 2 ^ w := by have := ctx.hw16; omega
  dsimp only
  set su := mem (dgExtToIntBase ctx.g0Ptr vCap + u)
  set intToExt := dgIntToExtBase ctx.g0Ptr vCap
  set eTailSlot := dgETailSlotBase ctx.g0Ptr vCap eCap
  set eHeadSlot := dgEHeadSlotBase ctx.g0Ptr vCap eCap
  set heNext := dgHeNextBase ctx.g0Ptr vCap eCap
  induction rem generalizing k qL eL st with
  | zero =>
    intro hk hrem hqh huNot hR hr18 hr19 hr20 hr23 hInv heChar hnbCov
    have hkeq : k = (ctx.incL su).length := by omega
    subst hkeq
    have hr23_0 : st.regs 23 = 0 := by simpa using hr23
    have hsu_mem : su ∈ G₀.V := (hE2I u (hC_sub huC)).1
    have hsu_lt : su < vCap := hVlt su hsu_mem
    have hinc_u := (ctx.hincFull su hsu_lt).2.2
    refine ⟨st, qL, eL, 2,
      runs_loop_iff.mpr (Or.inl ⟨by eval_expr, rfl, rfl, by simp [Expr.size]⟩),
      hR, hr18, hr19, hr20, le_rfl, rfl, fun _ h => h, hInv, ?_, ?_, by omega⟩
    · intro e heG
      rw [heChar e heG, List.take_length]
      constructor
      · rintro (h | ⟨ht, _⟩); exact Or.inl h; exact Or.inr ht
      · rintro (h | ht)
        · exact Or.inl h
        · right
          refine ⟨ht, (hinc_u (2 * e)).mpr ⟨by have := hElt e heG; omega, by simpa using heG, ?_⟩⟩
          simp only [Nat.mul_mod_right, ↓reduceIte, show 2 * e / 2 = e by omega]
          rw [(hEnds e heG).1, ht]
    · intro e heG
      refine ⟨fun ht => ?_, fun hh => ?_⟩
      · have h2e : 2 * e ∈ (ctx.incL su).take (ctx.incL su).length := by
          rw [List.take_length]
          refine (hinc_u (2 * e)).mpr ⟨by have := hElt e heG; omega, by simpa using heG, ?_⟩
          simp only [Nat.mul_mod_right, ↓reduceIte, show 2 * e / 2 = e by omega]
          rw [(hEnds e heG).1, ht]
        simpa using (hnbCov (2 * e) h2e).1 (by omega)
      · have h2e1 : 2 * e + 1 ∈ (ctx.incL su).take (ctx.incL su).length := by
          rw [List.take_length]
          refine (hinc_u (2 * e + 1)).mpr
            ⟨by have := hElt e heG; omega, by rw [show (2 * e + 1) / 2 = e by omega]; exact heG, ?_⟩
          simp only [show (2 * e + 1) % 2 = 1 by omega, show (2 * e + 1) / 2 = e by omega,
            one_ne_zero, ↓reduceIte]
          rw [(hEnds e heG).2, hh]
        simpa [show (2 * e + 1) / 2 = e by omega] using (hnbCov (2 * e + 1) h2e1).2 (by omega)
  | succ rem ih =>
    intro hk hrem hqh huNot hR hr18 hr19 hr20 hr23 hInv heChar hnbCov
    have hklt : k < (ctx.incL su).length := by omega
    have hsu_mem : su ∈ G₀.V := (hE2I u (hC_sub huC)).1
    have hsu_lt : su < vCap := hVlt su hsu_mem
    have hDLL := (ctx.hincFull su hsu_lt).1
    have hinc_u := (ctx.hincFull su hsu_lt).2.2
    set h := (ctx.incL su)[k]
    have hh_mem : h ∈ ctx.incL su := List.getElem_mem hklt
    have ⟨hh_lt, heG, hslot⟩ := (hinc_u h).mp hh_mem
    set e := h / 2
    set isHead := h % 2
    change (if isHead = 0 then mem (eTailSlot + e) else mem (eHeadSlot + e)) = su at hslot
    have he_lt : e < eCap := hElt e heG
    have hst_m := hEnds e heG
    have hut_mem : G₀.tail e ∈ G₀.V := (hG₀ e heG).1
    have hvh_mem : G₀.head e ∈ G₀.V := (hG₀ e heG).2
    have hut_lt : G₀.tail e < vCap := hVlt _ hut_mem
    have hvh_lt : G₀.head e < vCap := hVlt _ hvh_mem
    have hst_lt : mem (eTailSlot + e) < vCap := by rw [hst_m.1]; exact hVlt _ (hE2I _ hut_mem).1
    have hsh_lt : mem (eHeadSlot + e) < vCap := by rw [hst_m.2]; exact hVlt _ (hE2I _ hvh_mem).1
    have hut_eq : mem (intToExt + mem (eTailSlot + e)) = G₀.tail e := by
      rw [hst_m.1]; exact (hE2I _ hut_mem).2
    have hvh_eq : mem (intToExt + mem (eHeadSlot + e)) = G₀.head e := by
      rw [hst_m.2]; exact (hE2I _ hvh_mem).2
    have htail_of_0 : isHead = 0 → G₀.tail e = u := fun hp => by
      have hs' : mem (eTailSlot + e) = su := by simpa [hp] using hslot
      have h1 := (hE2I _ hut_mem).2
      rw [← hst_m.1, hs'] at h1
      exact h1.symm.trans (hE2I u (hC_sub huC)).2
    have hhead_of_ne : isHead ≠ 0 → G₀.head e = u := fun hp => by
      have hs' : mem (eHeadSlot + e) = su := by simpa [hp] using hslot
      have h1 := (hE2I _ hvh_mem).2
      rw [← hst_m.2, hs'] at h1
      exact h1.symm.trans (hE2I u (hC_sub huC)).2
    have heC : e ∈ compEdgeSet G₀ C := by
      rw [compEdgeSet, Finset.mem_filter]; refine ⟨heG, ?_⟩
      by_cases hp : isHead = 0
      · exact htail_of_0 hp ▸ huC
      · rcases Finset.mem_image.mp ctx.hC with ⟨w', _, rfl⟩
        exact mem_compOf_iff.mpr ⟨hut_mem,
          connected_trans (mem_compOf_iff.mp (hhead_of_ne hp ▸ huC)).2 (connected_symm (connected_of_edge heG))⟩
    have ⟨_, htC, hhC⟩ := mem_compEdgeSet_endpoints hG₀ ctx.hC heC
    have hg0_st := ctx.hg0_agree hInv.2.2.2.2.2.2.2.2.2.2.2
    have hhr23 : st.regs 23 = h + 1 := by simpa [hklt, h] using hr23
    have hg0_w := ctx.hg0_w
    have hh_w : h + 1 < 2 ^ w := by dsimp [dynGraphSize] at hg0_w; omega
    have hte_st : st.mem (eTailSlot + e) = mem (eTailSlot + e) :=
      hg0_st _ (by dsimp [eTailSlot, dgETailSlotBase]; omega)
        (by dsimp [eTailSlot, dgETailSlotBase, dynGraphSize]; omega)
    have hhe_st : st.mem (eHeadSlot + e) = mem (eHeadSlot + e) :=
      hg0_st _ (by dsimp [eHeadSlot, dgEHeadSlotBase]; omega)
        (by dsimp [eHeadSlot, dgEHeadSlotBase, dynGraphSize]; omega)
    have hi2e_t : st.mem (intToExt + mem (eTailSlot + e)) = G₀.tail e :=
      (hg0_st _ (by dsimp [intToExt, dgIntToExtBase]; omega)
        (by dsimp [intToExt, dgIntToExtBase, dynGraphSize]; omega)).trans hut_eq
    have hi2e_h : st.mem (intToExt + mem (eHeadSlot + e)) = G₀.head e :=
      (hg0_st _ (by dsimp [intToExt, dgIntToExtBase]; omega)
        (by dsimp [intToExt, dgIntToExtBase, dynGraphSize]; omega)).trans hvh_eq
    set nb := if isHead = 0 then G₀.head e else G₀.tail e
    have hnbC : nb ∈ C := by dsimp only [nb]; split_ifs <;> assumption
    have hnb_lt : nb < vCap := hVlt nb (hC_sub hnbC)
    have hnb_nvis : nb ∉ visSet := Finset.disjoint_right.mp ctx.hvisDisj hnbC
    set eL1 := if isHead = 0 then eL ++ [(e, G₀.tail e, G₀.head e)] else eL
    have heNotIn : isHead = 0 → ∀ t ∈ eL, t.1 ≠ e := by
      intro hp t ht hte
      rcases (heChar e heG).mp ⟨t, ht, hte⟩ with hprev | ⟨_, h2e_take⟩
      · exact huNot (htail_of_0 hp ▸ hprev)
      · have h2e_eq : 2 * e = (ctx.incL su)[k] := by dsimp only [h, e, isHead] at hp ⊢; omega
        rw [h2e_eq] at h2e_take
        obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem h2e_take
        rw [List.length_take, Nat.min_eq_left (le_of_lt hklt)] at hj
        rw [List.getElem_take] at hjk
        have := hDLL.1.getElem_inj_iff.mp hjk
        omega
    have heL1_nd : (eL1.map Prod.fst).Nodup := by
      dsimp only [eL1]; split_ifs with hp
      · rw [List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨hInv.2.2.2.1, List.nodup_singleton _, fun x hx y hy => ?_⟩
        simp only [List.mem_singleton] at hy; subst hy
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        exact heNotIn hp t ht
      · exact hInv.2.2.2.1
    have heL1_sub : ∀ t ∈ eL1, t.1 ∈ compEdgeSet G₀ C ∧ t.2.1 = G₀.tail t.1 ∧ t.2.2 = G₀.head t.1 := by
      intro t ht; dsimp only [eL1] at ht; split_ifs at ht with hp
      · rcases List.mem_append.mp ht with h1 | h2
        · exact hInv.2.2.2.2.2.1 t h1
        · simp only [List.mem_singleton] at h2; subst h2; exact ⟨heC, rfl, rfl⟩
      · exact hInv.2.2.2.2.2.1 t ht
    have heL1_len_le : eL1.length ≤ (compGraph G₀ C).m := bfs_eL_len_le heL1_nd heL1_sub
    have heL_lt_m : isHead = 0 → eL.length < (compGraph G₀ C).m := fun hp => by
      have : eL1.length = eL.length + 1 := by simp [eL1, hp]
      omega
    have hbody : ∃ st_mid c_b,
        Runs w p ω compBfsInnerBody st .normal st_mid c_b ∧
        let qL1 := if nb ∈ qL then qL else qL ++ [nb]
        BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
          ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st_mid.regs ∧
        st_mid.regs 18 = qHead ∧ st_mid.regs 19 = qL1.length ∧
        st_mid.regs 20 = eL1.length ∧
        st_mid.regs 23 = (if hk1 : k + 1 < (ctx.incL su).length then (ctx.incL su)[k + 1] + 1 else 0) ∧
        BfsMemInv mem st_mid.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
          ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL1 eL1 ∧
        c_b ≤ 155 := by
      set nxtVal := if hk1 : k + 1 < (ctx.incL su).length then (ctx.incL su)[k + 1] + 1 else 0
      have hnxt_eq : mem (heNext + h) = nxtVal := by
        have h2 := (hDLL.2.2.2 k hklt).2
        dsimp only [heNext, nxtVal, h]
        rw [h2]
        by_cases hk1 : k + 1 < (ctx.incL su).length
        · simp [hk1, show k + 1 ≠ (ctx.incL su).length by omega]
        · simp [show k + 1 = (ctx.incL su).length by omega]
      have hnxt_lt : nxtVal < 2 ^ w := by
        dsimp only [nxtVal]; split_ifs with hk1
        · have := hDLL.2.1 _ (List.getElem_mem hk1); dsimp [dynGraphSize] at hg0_w; omega
        · omega
      have hcont : ∀ (stA : State) (cp : ℕ),
          BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
            ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap stA.regs →
          stA.regs 18 = qHead → stA.regs 19 = qL.length →
          stA.regs 20 = eL1.length → stA.regs 24 = h → stA.regs 29 = nb →
          BfsMemInv mem stA.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
            ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL eL1 →
          cp + 52 ≤ 155 →
          ∃ o st_mid c_tail,
            Runs w p ω
              (.assign 30 (.load (.bin .add (.reg 1) (.reg 29))) ;;
               .cond (.reg 30)
                 .nop
                 (.store (.bin .add (.reg 1) (.reg 29)) (.const 1) ;;
                  .store (.bin .add (.reg 2) (.reg 29)) (.reg 8) ;;
                  .store (.bin .add (.reg 5) (.reg 19)) (.reg 29) ;;
                  .assign 19 (.bin .add (.reg 19) (.const 1))) ;;
               .assign 23 (.load (.bin .add (.reg 17) (.reg 24))))
              stA o st_mid c_tail ∧
            (o = .normal ∧
              let qL1 := if nb ∈ qL then qL else qL ++ [nb]
              BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
                ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st_mid.regs ∧
              st_mid.regs 18 = qHead ∧ st_mid.regs 19 = qL1.length ∧
              st_mid.regs 20 = eL1.length ∧ st_mid.regs 23 = nxtVal ∧
              BfsMemInv mem st_mid.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
                ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL1 eL1) ∧
            cp + c_tail ≤ 155 := by
        intro stA cp hRA hA18 hA19 hA20 hA24 hA29 hInvA hcp
        have hvis_nb : stA.mem (ctx.visBase + nb) = if nb ∈ qL then 1 else 0 := by
          have := hInvA.2.2.2.2.2.2.1 nb hnb_lt
          simpa [hnb_nvis] using this
        have hvnb_lt : (if nb ∈ qL then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        have hheN_w : heNext + h < 2 ^ w := by
          dsimp [heNext, dgHeNextBase, dynGraphSize] at hg0_w ⊢; omega
        have hvis_w := ctx.hvis_w; have hvc_w := ctx.hvc_w; have hbq_w := ctx.hbq_w
        have hc_lt := ctx.hc_lt
        refine runs_seq_assign_le (v := if nb ∈ qL then 1 else 0)
          (Expr.eval_load_of_eq (by have := hRA.r1; eval_expr) hvis_nb) ?_
        refine runs_seq_cond_le (v := if nb ∈ qL then 1 else 0) (by eval_expr) ?_ ?_
        · intro hvis_ne
          have hnb_in : nb ∈ qL := by by_contra hni; exact hvis_ne (by simp [hni])
          refine runs_seq_nop_le ?_
          have hnxtA : stA.mem (heNext + h) = nxtVal :=
            (ctx.hg0_agree hInvA.2.2.2.2.2.2.2.2.2.2.2 (heNext + h)
              (by dsimp [heNext, dgHeNextBase]; omega)
              (by dsimp [heNext, dgHeNextBase, dynGraphSize]; omega)).trans hnxt_eq
          have hrun_last : Runs w p ω (.assign 23 (.load (.bin .add (.reg 17) (.reg 24))))
              { stA with regs := Function.update stA.regs 30 (if nb ∈ qL then 1 else 0) }
              .normal
              { stA with regs := Function.update (Function.update stA.regs 30 (if nb ∈ qL then 1 else 0)) 23 nxtVal }
              5 :=
            runs_assign_iff.mpr ⟨nxtVal,
              Expr.eval_load_of_eq (by have := hRA.r17; eval_expr) hnxtA,
              rfl, rfl, by simp [Expr.size]⟩
          exact ⟨.normal, _, 5, hrun_last, ⟨rfl, (hRA.update_ge18 (by omega)).update_ge18 (by omega),
            by simp [hA18], by simp [hnb_in, hA19], by simp [hA20], by simp,
            by simpa [hnb_in] using hInvA⟩, by simp [Expr.size]; omega⟩
        · intro hvis_0
          have hnb_nin : nb ∉ qL := fun h => absurd (by simp [h] : (if nb ∈ qL then 1 else 0) = 1) (by omega)
          have hqL1_nd : (qL ++ [nb]).Nodup := by
            rw [List.nodup_append]; exact ⟨hInvA.1, List.nodup_singleton _, fun x hx y hy => by
              simp only [List.mem_singleton] at hy; subst hy; exact fun h => hnb_nin (h ▸ hx)⟩
          have hqL1_sub : ∀ x ∈ qL ++ [nb], x ∈ C := fun x hx => by
            rcases List.mem_append.mp hx with h1 | h2
            · exact hInvA.2.1 x h1
            · simp only [List.mem_singleton] at h2; subst h2; exact hnbC
          have hqL1_le : (qL ++ [nb]).length ≤ (compGraph G₀ C).n := bfs_qL_len_le hqL1_nd hqL1_sub
          have hqL_lt : qL.length < (compGraph G₀ C).n := by simp at hqL1_le; omega
          let st0 := { stA with regs := Function.update stA.regs 30 (if nb ∈ qL then 1 else 0) }
          let m1 := Function.update st0.mem (ctx.visBase + nb) 1
          let m2 := Function.update m1 (ctx.vCompBase + nb) ctx.c
          let m3 := Function.update m2 (ctx.bfsQBase + qL.length) nb
          let r3 := Function.update st0.regs 19 (qL.length + 1)
          let r4 := Function.update r3 23 nxtVal
          have hrun1 : Runs w p ω (.store (.bin .add (.reg 1) (.reg 29)) (.const 1)) st0 .normal
              { st0 with mem := m1 } 5 :=
            runs_store_iff.mpr ⟨ctx.visBase + nb, 1, by have := hRA.r1; eval_expr, by eval_expr,
              rfl, rfl, by simp [Expr.size]⟩
          have hrun2 : Runs w p ω (.store (.bin .add (.reg 2) (.reg 29)) (.reg 8))
              { st0 with mem := m1 } .normal { st0 with mem := m2 } 5 :=
            runs_store_iff.mpr ⟨ctx.vCompBase + nb, ctx.c, by have := hRA.r2; eval_expr,
              by have := hRA.r8; eval_expr, rfl, rfl, by simp [Expr.size]⟩
          have hrun3 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 19)) (.reg 29))
              { st0 with mem := m2 } .normal { st0 with mem := m3 } 5 :=
            runs_store_iff.mpr ⟨ctx.bfsQBase + qL.length, nb, by have := hRA.r5; eval_expr,
              by eval_expr, rfl, rfl, by simp [Expr.size]⟩
          have hrun4 : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.const 1)))
              { st0 with mem := m3 } .normal { mem := m3, regs := r3, pos := st0.pos } 4 :=
            runs_assign_iff.mpr ⟨qL.length + 1, by eval_expr, rfl, rfl, by simp [Expr.size]⟩
          have hblock : Runs w p ω _ st0 .normal { mem := m3, regs := r3, pos := st0.pos } 22 :=
            runs_seq_iff.mpr (Or.inr ⟨_, 5, 16, hrun1,
              runs_seq_iff.mpr (Or.inr ⟨_, 5, 10, hrun2,
                runs_seq_iff.mpr (Or.inr ⟨_, 5, 4, hrun3, hrun4, rfl⟩), rfl⟩), rfl⟩)
          have hInv3 : BfsMemInv mem m3 vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base
              ctx.edgeC2Base ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet
              (qL ++ [nb]) eL1 := by
            have hne_vbq : ∀ x < vCap, ctx.visBase + x ≠ ctx.bfsQBase + qL.length := fun x hx => by
              rcases ctx.hd_vbq with h | h <;> omega
            have hne_vvc : ∀ x < vCap, ∀ y < vCap, ctx.visBase + x ≠ ctx.vCompBase + y := fun x hx y hy => by
              rcases ctx.hd_vvc with h | h <;> omega
            have hne_vcbq : ∀ x < vCap, ctx.vCompBase + x ≠ ctx.bfsQBase + qL.length := fun x hx => by
              rcases ctx.hd_vcbq with h | h <;> omega
            refine ⟨hqL1_nd, hqL1_sub, ?_, hInvA.2.2.2.1, ?_, hInvA.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro i hi
              simp only [List.length_append, List.length_singleton] at hi
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
              · rw [List.getElem_append_left hi']
                dsimp only [m3, m2, m1, st0]
                rw [Function.update_of_ne (by omega),
                  Function.update_of_ne (by rcases ctx.hd_vcbq with h | h <;> omega),
                  Function.update_of_ne (by rcases ctx.hd_vbq with h | h <;> omega)]
                exact hInvA.2.2.1 i hi'
              · simp [m3]
            · intro i hi
              have hlen_m := bfs_eL_len_le hInvA.2.2.2.1 hInvA.2.2.2.2.2.1
              have he3 : ∀ d < 3, m3 (ctx.compEdgesBase + (3 * i + d)) =
                  stA.mem (ctx.compEdgesBase + (3 * i + d)) := fun d hd => by
                dsimp only [m3, m2, m1, st0]
                rw [Function.update_of_ne (by rcases ctx.hd_bqce with h | h <;> omega),
                  Function.update_of_ne (by rcases ctx.hd_vcce with h | h <;> omega),
                  Function.update_of_ne (by rcases ctx.hd_vce with h | h <;> omega)]
              have h0 := he3 0 (by omega); have h1 := he3 1 (by omega); have h2 := he3 2 (by omega)
              have ha := hInvA.2.2.2.2.1 i hi
              exact ⟨by simpa using h0.trans ha.1, by simpa [Nat.add_assoc] using h1.trans ha.2.1,
                by simpa [Nat.add_assoc] using h2.trans ha.2.2⟩
            · intro v hv
              dsimp only [m3, m2, m1, st0]
              rw [Function.update_of_ne (hne_vbq v hv), Function.update_of_ne (hne_vvc v hv nb hnb_lt)]
              by_cases hvn : v = nb
              · subst hvn; simp
              · rw [Function.update_of_ne (by omega), hInvA.2.2.2.2.2.2.1 v hv]
                simp [hvn]
            · intro w' hw'
              dsimp only [m3, m2, m1, st0]
              have hw_lt : w' < vCap := hVlt w' (hC_sub (hqL1_sub w' hw'))
              rw [Function.update_of_ne (hne_vcbq w' hw_lt)]
              rcases List.mem_append.mp hw' with hw1 | hw2
              · have hwn : w' ≠ nb := fun h => hnb_nin (h ▸ hw1)
                rw [Function.update_of_ne (by omega), Function.update_of_ne (Ne.symm (hne_vvc nb hnb_lt w' hw_lt))]
                exact hInvA.2.2.2.2.2.2.2.1 w' hw1
              · simp only [List.mem_singleton] at hw2; subst hw2; exact Function.update_self _ _ _
            · intro w' hw' hwn
              dsimp only [m3, m2, m1, st0]
              have hwn1 : w' ∉ qL := fun h => hwn (List.mem_append_left _ h)
              have hwn2 : w' ≠ nb := fun h => hwn (List.mem_append_right _ (by simp [h]))
              rw [Function.update_of_ne (hne_vcbq w' hw'), Function.update_of_ne (by omega),
                Function.update_of_ne (Ne.symm (hne_vvc nb hnb_lt w' hw'))]
              exact hInvA.2.2.2.2.2.2.2.2.1 w' hw' hwn1
            · intro t ht
              have ht_lt : t.1 < eCap := hElt t.1 (Finset.filter_subset _ _ (hInvA.2.2.2.2.2.1 t ht).1)
              dsimp only [m3, m2, m1, st0]
              rw [Function.update_of_ne (by rcases ctx.hd_e1bq with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_vce1 with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_ve1 with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e2bq with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_vce2 with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_ve2 with h | h <;> omega)]
              exact hInvA.2.2.2.2.2.2.2.2.2.1 t ht
            · intro e' he' hne
              dsimp only [m3, m2, m1, st0]
              rw [Function.update_of_ne (by rcases ctx.hd_e1bq with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_vce1 with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_ve1 with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e2bq with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_vce2 with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_ve2 with h | h <;> omega)]
              exact hInvA.2.2.2.2.2.2.2.2.2.2.1 e' he' hne
            · intro a ha1 ha2 ha3 ha4 ha5 ha6 ha7
              dsimp only [m3, m2, m1, st0]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
              exact hInvA.2.2.2.2.2.2.2.2.2.2.2 a ha1 ha2 ha3 ha4 ha5 ha6 ha7
          have hnxt3 : m3 (heNext + h) = nxtVal :=
            (ctx.hg0_agree hInv3.2.2.2.2.2.2.2.2.2.2.2 (heNext + h)
              (by dsimp [heNext, dgHeNextBase]; omega)
              (by dsimp [heNext, dgHeNextBase, dynGraphSize]; omega)).trans hnxt_eq
          have hrun_last : Runs w p ω (.assign 23 (.load (.bin .add (.reg 17) (.reg 24))))
              { mem := m3, regs := r3, pos := st0.pos } .normal
              { mem := m3, regs := r4, pos := st0.pos } 5 :=
            runs_assign_iff.mpr ⟨nxtVal,
              Expr.eval_load_of_eq (by have := hRA.r17; simp [r3, st0, Expr.eval, BinOp.eval, this, hA24, heNext, hheN_w]) hnxt3,
              rfl, rfl, by simp [Expr.size]⟩
          exact ⟨.normal, { mem := m3, regs := r4, pos := st0.pos }, 22 + 5 + 1,
            runs_seq_iff.mpr (Or.inr ⟨_, 22, 5, hblock, hrun_last, rfl⟩),
            ⟨rfl, ((hRA.update_ge18 (by omega)).update_ge18 (by omega)).update_ge18 (by omega),
             by simp [r4, r3, st0, hA18], by simp [hnb_nin, r4, r3],
             by simp [r4, r3, st0, hA20], by simp [r4], by simpa [hnb_nin] using hInv3⟩,
            by simp [Expr.size]; omega⟩
      suffices hfull : ∃ o st_mid c_b,
          Runs w p ω compBfsInnerBody st o st_mid c_b ∧
          (o = .normal ∧
            let qL1 := if nb ∈ qL then qL else qL ++ [nb]
            BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
              ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap st_mid.regs ∧
            st_mid.regs 18 = qHead ∧ st_mid.regs 19 = qL1.length ∧
            st_mid.regs 20 = eL1.length ∧ st_mid.regs 23 = nxtVal ∧
            BfsMemInv mem st_mid.mem vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
              ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL1 eL1) ∧
          0 + c_b ≤ 155 by
        rcases hfull with ⟨_, st_mid, c_b, hrun, ⟨rfl, h1, h2, h3, h4, h5, h6⟩, hcb⟩
        exact ⟨st_mid, c_b, hrun, h1, h2, h3, h4, h5, h6, by omega⟩
      unfold compBfsInnerBody
      have heT_w : eTailSlot + e < 2 ^ w := by dsimp [eTailSlot, dgETailSlotBase, dynGraphSize] at hg0_w ⊢; omega
      have heH_w : eHeadSlot + e < 2 ^ w := by dsimp [eHeadSlot, dgEHeadSlotBase, dynGraphSize] at hg0_w ⊢; omega
      have hiT_w : intToExt + mem (eTailSlot + e) < 2 ^ w := by dsimp [intToExt, dgIntToExtBase, dynGraphSize] at hg0_w ⊢; omega
      have hiH_w : intToExt + mem (eHeadSlot + e) < 2 ^ w := by dsimp [intToExt, dgIntToExtBase, dynGraphSize] at hg0_w ⊢; omega
      refine runs_seq_assign_le (v := h)
        (by simp [Expr.eval, BinOp.eval, hhr23, hw1, show h < 2 ^ w by omega]) ?_
      refine runs_seq_assign_le (v := e)
        (by simp [Expr.eval, BinOp.eval, hw2, show e < 2 ^ w by omega, e]) ?_
      refine runs_seq_assign_le (v := isHead)
        (by simp [Expr.eval, BinOp.eval, hw2, show isHead < 2 ^ w by omega, isHead]) ?_
      refine runs_seq_assign_le (v := mem (eTailSlot + e))
        (Expr.eval_load_of_eq (by have := hR.r15; eval_expr) hte_st) ?_
      refine runs_seq_assign_le (v := mem (eHeadSlot + e))
        (Expr.eval_load_of_eq (by have := hR.r16; eval_expr) hhe_st) ?_
      refine runs_seq_assign_le (v := G₀.tail e)
        (Expr.eval_load_of_eq (by have := hR.r13; eval_expr) hi2e_t) ?_
      refine runs_seq_assign_le (v := G₀.head e)
        (Expr.eval_load_of_eq (by have := hR.r13; eval_expr) hi2e_h) ?_
      refine runs_seq_cond_le (v := isHead) (by eval_expr) ?_ ?_
      · intro hmod_ne
        refine runs_seq_assign_le (v := G₀.tail e) (by eval_expr) ?_
        exact hcont _ _ ((((((((hR.update_ge18 (by decide)).update_ge18 (by decide)).update_ge18
          (by decide)).update_ge18 (by decide)).update_ge18 (by decide)).update_ge18
          (by decide)).update_ge18 (by decide)).update_ge18 (by decide))
          (by simp [hr18]) (by simp [hr19])
          (by simp [hr20, eL1, hmod_ne]) (by simp) (by simp [nb, hmod_ne])
          (by simpa [eL1, hmod_ne] using hInv) (by simp [Expr.size])
      · intro hmod_0
        have heL_lt := heL_lt_m hmod_0
        let stP : State :=
          { st with regs := Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update (Function.update st.regs 24 h) 25 e) 26 isHead)
              27 (mem (eTailSlot + e))) 28 (mem (eHeadSlot + e))) 27 (G₀.tail e)) 28 (G₀.head e) }
        let me1 := Function.update st.mem (ctx.edgeC1Base + e) ctx.c
        let me2 := Function.update me1 (ctx.edgeC2Base + e) ctx.c
        let me3 := Function.update me2 (ctx.compEdgesBase + 3 * eL.length) e
        let me4 := Function.update me3 (ctx.compEdgesBase + (3 * eL.length + 1)) (G₀.tail e)
        let me5 := Function.update me4 (ctx.compEdgesBase + (3 * eL.length + 2)) (G₀.head e)
        let re1 := Function.update stP.regs 30 (3 * eL.length)
        let re2 := Function.update re1 20 (eL.length + 1)
        let re3 := Function.update re2 29 (G₀.head e)
        have hec1_w := ctx.hec1_w; have hec2_w := ctx.hec2_w; have hce_w := ctx.hce_w
        have hvc_w := ctx.hvc_w; have hc_lt := ctx.hc_lt
        have h3m_w : 3 * eL.length + 2 < 2 ^ w := by omega
        have hce0_w : ctx.compEdgesBase + 3 * eL.length < 2 ^ w := by omega
        have hce1_w : ctx.compEdgesBase + (3 * eL.length + 1) < 2 ^ w := by omega
        have hce2_w : ctx.compEdgesBase + (3 * eL.length + 2) < 2 ^ w := by omega
        have hs1 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 25)) (.reg 8)) stP .normal
            { stP with mem := me1 } 5 :=
          runs_store_iff.mpr ⟨ctx.edgeC1Base + e, ctx.c,
            by simp [stP, Expr.eval, BinOp.eval, hR.r3, show ctx.edgeC1Base + e < 2 ^ w by omega],
            by simp [stP, Expr.eval, hR.r8], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 25)) (.reg 8))
            { stP with mem := me1 } .normal { stP with mem := me2 } 5 :=
          runs_store_iff.mpr ⟨ctx.edgeC2Base + e, ctx.c,
            by simp [stP, Expr.eval, BinOp.eval, hR.r4, show ctx.edgeC2Base + e < 2 ^ w by omega],
            by simp [stP, Expr.eval, hR.r8], rfl, rfl, by simp [Expr.size]⟩
        have hs3 : Runs w p ω (.assign 30 (.bin .mul (.const 3) (.reg 20)))
            { stP with mem := me2 } .normal { mem := me2, regs := re1, pos := stP.pos } 4 :=
          runs_assign_iff.mpr ⟨3 * eL.length,
            by simp [stP, Expr.eval, BinOp.eval, hr20, hw3, show 3 * eL.length < 2 ^ w by omega],
            rfl, rfl, by simp [Expr.size]⟩
        have hs4 : Runs w p ω (.store (.bin .add (.reg 6) (.reg 30)) (.reg 25))
            { mem := me2, regs := re1, pos := stP.pos } .normal { mem := me3, regs := re1, pos := stP.pos } 5 :=
          runs_store_iff.mpr ⟨ctx.compEdgesBase + 3 * eL.length, e,
            by simp [re1, stP, Expr.eval, BinOp.eval, hR.r6, hce0_w],
            by simp [re1, stP, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
        have hs5 : Runs w p ω (.store (.bin .add (.reg 6) (.bin .add (.reg 30) (.const 1))) (.reg 27))
            { mem := me3, regs := re1, pos := stP.pos } .normal { mem := me4, regs := re1, pos := stP.pos } 7 :=
          runs_store_iff.mpr ⟨ctx.compEdgesBase + (3 * eL.length + 1), G₀.tail e,
            by simp [re1, stP, Expr.eval, BinOp.eval, hR.r6, hw1, show 3 * eL.length + 1 < 2 ^ w by omega, hce1_w],
            by simp [re1, stP, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
        have hs6 : Runs w p ω (.store (.bin .add (.reg 6) (.bin .add (.reg 30) (.const 2))) (.reg 28))
            { mem := me4, regs := re1, pos := stP.pos } .normal { mem := me5, regs := re1, pos := stP.pos } 7 :=
          runs_store_iff.mpr ⟨ctx.compEdgesBase + (3 * eL.length + 2), G₀.head e,
            by simp [re1, stP, Expr.eval, BinOp.eval, hR.r6, hw2, h3m_w, hce2_w],
            by simp [re1, stP, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
        have hs7 : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1)))
            { mem := me5, regs := re1, pos := stP.pos } .normal { mem := me5, regs := re2, pos := stP.pos } 4 :=
          runs_assign_iff.mpr ⟨eL.length + 1,
            by simp [re1, stP, Expr.eval, BinOp.eval, hr20, hw1, show eL.length + 1 < 2 ^ w by omega],
            rfl, rfl, by simp [Expr.size]⟩
        have hs8 : Runs w p ω (.assign 29 (.reg 28))
            { mem := me5, regs := re2, pos := stP.pos } .normal { mem := me5, regs := re3, pos := stP.pos } 2 :=
          runs_assign_iff.mpr ⟨G₀.head e,
            by simp [re2, re1, stP, Expr.eval],
            rfl, rfl, by simp [Expr.size]⟩
        have hem_run : Runs w p ω _ stP .normal { mem := me5, regs := re3, pos := stP.pos } 46 :=
          runs_seq_iff.mpr (Or.inr ⟨_, 5, 40, hs1,
            runs_seq_iff.mpr (Or.inr ⟨_, 5, 34, hs2,
              runs_seq_iff.mpr (Or.inr ⟨_, 4, 29, hs3,
                runs_seq_iff.mpr (Or.inr ⟨_, 5, 23, hs4,
                  runs_seq_iff.mpr (Or.inr ⟨_, 7, 15, hs5,
                    runs_seq_iff.mpr (Or.inr ⟨_, 7, 7, hs6,
                      runs_seq_iff.mpr (Or.inr ⟨_, 4, 2, hs7, hs8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        have hInv_em : BfsMemInv mem me5 vCap eCap ctx.visBase ctx.vCompBase ctx.edgeC1Base
            ctx.edgeC2Base ctx.bfsQBase ctx.compEdgesBase ctx.outM0Addr ctx.c G₀ C visSet qL eL1 := by
          have heL1_eq : eL1 = eL ++ [(e, G₀.tail e, G₀.head e)] := by simp [eL1, hmod_0]
          rw [heL1_eq]
          refine ⟨hInv.1, hInv.2.1, ?_, heL1_eq ▸ heL1_nd, ?_, heL1_eq ▸ heL1_sub, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro i hi
            have hq_le : qL.length ≤ (compGraph G₀ C).n := bfs_qL_len_le hInv.1 hInv.2.1
            dsimp only [me5, me4, me3, me2, me1]
            rw [Function.update_of_ne (by rcases ctx.hd_bqce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_bqce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_bqce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_e2bq with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_e1bq with h | h <;> omega)]
            exact hInv.2.2.1 i hi
          · intro i hi
            simp only [List.length_append, List.length_singleton] at hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · simp only [List.getElem_append_left hi']
              have ha := hInv.2.2.2.2.1 i hi'
              dsimp only [me5, me4, me3, me2, me1]
              refine ⟨?_, ?_, ?_⟩
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega),
                  Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                  Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega)]
                exact ha.1
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega),
                  Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                  Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega)]
                exact ha.2.1
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega),
                  Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                  Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega)]
                exact ha.2.2
            · simp [me5, me4, me3, Nat.add_assoc]
          · intro v hv
            dsimp only [me5, me4, me3, me2, me1]
            rw [Function.update_of_ne (by rcases ctx.hd_vce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_ve2 with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_ve1 with h | h <;> omega)]
            exact hInv.2.2.2.2.2.2.1 v hv
          · intro w' hw'
            have hw_lt : w' < vCap := hVlt w' (hC_sub (hInv.2.1 w' hw'))
            dsimp only [me5, me4, me3, me2, me1]
            rw [Function.update_of_ne (by rcases ctx.hd_vcce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vcce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vcce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vce2 with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vce1 with h | h <;> omega)]
            exact hInv.2.2.2.2.2.2.2.1 w' hw'
          · intro w' hw' hwn
            dsimp only [me5, me4, me3, me2, me1]
            rw [Function.update_of_ne (by rcases ctx.hd_vcce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vcce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vcce with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vce2 with h | h <;> omega),
              Function.update_of_ne (by rcases ctx.hd_vce1 with h | h <;> omega)]
            exact hInv.2.2.2.2.2.2.2.2.1 w' hw' hwn
          · intro t ht
            have ht_lt : t.1 < eCap := hElt t.1 (Finset.filter_subset _ _ (heL1_sub t (heL1_eq ▸ ht)).1)
            dsimp only [me5, me4, me3, me2, me1]
            constructor
            · rw [Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e1e2 with h | h <;> omega)]
              rcases List.mem_append.mp ht with ht1 | ht2
              · have hne : t.1 ≠ e := heNotIn hmod_0 t ht1
                rw [Function.update_of_ne (by omega)]
                exact (hInv.2.2.2.2.2.2.2.2.2.1 t ht1).1
              · simp only [List.mem_singleton] at ht2; subst ht2; exact Function.update_self _ _ _
            · rw [Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega)]
              rcases List.mem_append.mp ht with ht1 | ht2
              · have hne : t.1 ≠ e := heNotIn hmod_0 t ht1
                rw [Function.update_of_ne (by omega),
                  Function.update_of_ne (by rcases ctx.hd_e1e2 with h | h <;> omega)]
                exact (hInv.2.2.2.2.2.2.2.2.2.1 t ht1).2
              · simp only [List.mem_singleton] at ht2; subst ht2; exact Function.update_self _ _ _
          · intro e' he' hne
            have he'_ne : e' ≠ e := fun h => hne (e, G₀.tail e, G₀.head e) (by simp) h.symm
            dsimp only [me5, me4, me3, me2, me1]
            constructor
            · rw [Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e1ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e1e2 with h | h <;> omega),
                Function.update_of_ne (by omega)]
              exact (hInv.2.2.2.2.2.2.2.2.2.2.1 e' he' fun t ht => hne t (List.mem_append_left _ ht)).1
            · rw [Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                Function.update_of_ne (by rcases ctx.hd_e2ce with h | h <;> omega),
                Function.update_of_ne (by omega),
                Function.update_of_ne (by rcases ctx.hd_e1e2 with h | h <;> omega)]
              exact (hInv.2.2.2.2.2.2.2.2.2.2.1 e' he' fun t ht => hne t (List.mem_append_left _ ht)).2
          · intro a ha1 ha2 ha3 ha4 ha5 ha6 ha7
            dsimp only [me5, me4, me3, me2, me1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hInv.2.2.2.2.2.2.2.2.2.2.2 a ha1 ha2 ha3 ha4 ha5 ha6 ha7
        have hR10 : BfsRegsOK ctx.g0Ptr ctx.visBase ctx.vCompBase ctx.edgeC1Base ctx.edgeC2Base
            ctx.bfsQBase ctx.compEdgesBase ctx.c ctx.outM0Addr vCap eCap re3 :=
          ((((((((((hR.update_ge18 (by decide)).update_ge18 (by decide)).update_ge18 (by decide)).update_ge18
            (by decide)).update_ge18 (by decide)).update_ge18 (by decide)).update_ge18 (by decide)).update_ge18
            (by decide)).update_ge18 (by decide)).update_ge18 (by decide))
        obtain ⟨o, st_mid, c_tail, hrun_t, hpost_t, hct⟩ := hcont { mem := me5, regs := re3, pos := stP.pos }
          (0 + (4 + 1) + (4 + 1) + (4 + 1) + (5 + 1) + (5 + 1) + (5 + 1) + (5 + 1) + (1 + 46 + 2))
          hR10 (by simp [re3, re2, re1, stP, hr18]) (by simp [re3, re2, re1, stP, hr19])
          (by simp [re3, re2, re1, eL1, hmod_0]) (by simp [re3, re2, re1, stP])
          (by simp [re3, nb, hmod_0]) hInv_em (by omega)
        exact ⟨o, st_mid, 46 + c_tail + 1,
          runs_seq_iff.mpr (Or.inr ⟨_, 46, c_tail, hem_run, hrun_t, rfl⟩),
          hpost_t, by simp [Expr.size]; omega⟩
    rcases hbody with ⟨st_mid, c_b, hrun_b, hR_m, hm18, hm19, hm20, hm23, hInv_m, hcb⟩
    set qL1 := if nb ∈ qL then qL else qL ++ [nb]
    have hqL1_take : qL1.take qHead = qL.take qHead := by
      dsimp only [qL1]; split_ifs
      · rfl
      · exact List.take_append_of_le_length hqh
    have hqL1_take1 : qL1.take (qHead - 1) = qL.take (qHead - 1) := by
      dsimp only [qL1]; split_ifs
      · rfl
      · exact List.take_append_of_le_length (by omega)
    have hqL1_sub : ∀ x ∈ qL, x ∈ qL1 := fun x hx => by
      dsimp only [qL1]; split_ifs; exact hx; exact List.mem_append_left _ hx
    have hnb_in_qL1 : nb ∈ qL1 := by dsimp only [qL1]; split_ifs with h'; exact h'; simp
    obtain ⟨st', qL', eL', c_rec, hrun_r, hR', hr18', hr19', hr20', hqle', hqtake', hqsub',
      hInv', heChar', hnbCov', hcr⟩ := ih (k + 1) qL1 eL1 st_mid (by omega) (by omega)
      (by dsimp only [qL1]; split_ifs; exact hqh; simp; omega) (hqL1_take1 ▸ huNot)
      hR_m hm18 hm19 hm20 hm23 hInv_m
      (fun e' heG' => by
        rw [hqL1_take1, List.take_succ_eq_append_getElem hklt]
        dsimp only [eL1]
        split_ifs with hp
        · have htail_u := htail_of_0 hp
          have h2e : 2 * e = (ctx.incL su)[k] := by dsimp only [h, e, isHead] at hp ⊢; omega
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨t, ht | rfl, rfl⟩
            · rcases (heChar t.1 heG').mp ⟨t, ht, rfl⟩ with h1 | ⟨h2, h3⟩
              · exact Or.inl h1
              · exact Or.inr ⟨h2, Or.inl h3⟩
            · exact Or.inr ⟨htail_u, Or.inr h2e⟩
          · rintro (h1 | ⟨h2, h3 | h3⟩)
            · obtain ⟨t, ht, hte⟩ := (heChar e' heG').mpr (Or.inl h1)
              exact ⟨t, Or.inl ht, hte⟩
            · obtain ⟨t, ht, hte⟩ := (heChar e' heG').mpr (Or.inr ⟨h2, h3⟩)
              exact ⟨t, Or.inl ht, hte⟩
            · exact ⟨(e, G₀.tail e, G₀.head e), Or.inr rfl, by omega⟩
        · rw [heChar e' heG']
          have hne : 2 * e' ≠ (ctx.incL su)[k] := fun heq =>
            hp (by dsimp only [isHead, h]; omega)
          simp only [List.mem_append, List.mem_singleton, hne, or_false])
      (fun h' hh' => by
        rw [List.take_succ_eq_append_getElem hklt, List.mem_append, List.mem_singleton] at hh'
        rcases hh' with hh1 | rfl
        · exact ⟨fun h0 => hqL1_sub _ ((hnbCov h' hh1).1 h0),
            fun h1 => hqL1_sub _ ((hnbCov h' hh1).2 h1)⟩
        · exact ⟨fun h0 => by simpa [nb, isHead, h, e, h0] using hnb_in_qL1,
            fun h1 => by simpa [nb, isHead, h, e, h1] using hnb_in_qL1⟩)
    refine ⟨st', qL', eL', 1 + c_b + c_rec + 1,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨h + 1, st_mid, c_b, c_rec, by eval_expr,
        Nat.succ_ne_zero _, hrun_b, hrun_r, by simp [Expr.size]⟩)),
      hR', hr18', hr19', hr20',
      le_trans (by dsimp only [qL1]; split_ifs <;> simp) hqle',
      hqtake'.trans hqL1_take, fun x hx => hqsub' x (hqL1_sub x hx),
      hInv', by simpa [hqL1_take1] using heChar', hnbCov', by omega⟩

end

end MinCostFlow.SparseCore.Program
