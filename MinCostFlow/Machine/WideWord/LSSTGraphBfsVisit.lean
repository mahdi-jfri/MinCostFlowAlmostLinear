module

public import MinCostFlow.Machine.WideWord.LSSTGraphBfsBase
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# WordRAM `O(n + m)` BFS component visit verification (`bfsVisit`)

This file proves the inner adjacency scan triple `bfsVisit_inner_triple` and the exact and
upper-bounded component-visit contracts `bfsVisit_exact_meetsContract` and `bfsVisit_meetsContract`
building on `LSSTGraphBfsBase.lean`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM
open MinCostFlow
open MinCostFlow.LSF

private lemma bfsVisit_inner_triple {G : IndexedGraph} {w offPtr adjPtr s visPtr queuePtr qhead q pSt pEn : ℕ}
    {mem : ℕ → ℕ} {st : State} {p : Program}
    (hG : G.Valid) (hw1 : 1 < 2 ^ w) (hs_lt : s < G.n) (hq_lt_n : q < G.n)
    (hq_conn : ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected s q)
    (hoff_disj : offPtr + (G.n + 1) ≤ visPtr) (hadj_disj : adjPtr + 2 * (nonloopEdges G).length ≤ visPtr)
    (hq_eq : visPtr + G.n = queuePtr) (hq_w : queuePtr + G.n < 2 ^ w)
    (hcsr : CSRAdjacencySpec G mem offPtr adjPtr) (hp_le : pSt ≤ pEn)
    (hpSt_def : mem (offPtr + q) = pSt) (hpEn_def : mem (offPtr + (q + 1)) = pEn)
    (hvis01 : ∀ u < G.n, mem (visPtr + u) = 0 ∨ mem (visPtr + u) = 1)
    (hInv : bfsVisitLoopInv G offPtr adjPtr s visPtr queuePtr mem st)
    (h6 : st.regs 6 = qhead) (h67 : qhead < st.regs 7)
    (hqq : st.mem (queuePtr + qhead) = q) :
    let rem0 := bfsRemTotal G offPtr visPtr queuePtr mem st - 50 - 120 * (pEn - pSt)
    Triple w p
      (fun s₁ => s₁.regs 0 = G.n ∧ s₁.regs 1 = offPtr ∧ s₁.regs 2 = adjPtr ∧
        s₁.regs 4 = visPtr ∧ s₁.regs 5 = queuePtr ∧ s₁.regs 6 = qhead + 1 ∧
        s₁.regs 7 = st.regs 7 ∧ s₁.regs 8 = q ∧ s₁.regs 9 = pSt ∧ s₁.regs 10 = pEn ∧
        s₁.mem = st.mem)
      bfsVisitInner
      (normalPost fun s₁ => bfsVisitInnerInv G offPtr adjPtr s visPtr queuePtr qhead q pSt pEn
        mem st.mem rem0 pEn s₁)
      (fun _ => (pEn - pSt) * 41 + 7) := by
  let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  let rem0 := bfsRemTotal G offPtr visPtr queuePtr mem st - 50 - 120 * (pEn - pSt)
  have hmon := hcsr.2.1
  have hadj_bnd := hcsr.2.2.1
  have hpEn_le_2nl : pEn ≤ 2 * (nonloopEdges G).length := hpEn_def ▸ csr_off_le_2nl hcsr (by omega)
  have hpEn_w : pEn < 2 ^ w := by omega
  rcases hInv with ⟨_, _, _, _, _, hst67, hst7n, hst_s, hst_mon0, hst_01, hst_conn,
    hst_qex, hst_qinfo, hst_qnd, hst_qcl, hst_fa⟩
  have hadj_lt_n : ∀ u p' (s₁_mem : ℕ → ℕ), u < G.n → mem (offPtr + u) ≤ p' → p' < mem (offPtr + (u + 1)) →
      s₁_mem (adjPtr + p') = mem (adjPtr + p') → s₁_mem (adjPtr + p') < G.n := by
    intro u p' s₁_mem hu hp1 hp2 heq
    obtain ⟨e, he_nl, hth⟩ := hcsr.2.2.2.1 u hu p' hp1 hp2
    have hem := (mem_nonloopEdges_iff.mp he_nl).1
    rw [heq]
    rcases hth with ⟨_, hw_eq⟩ | ⟨_, hw_eq⟩ <;> rw [hw_eq]
    · exact (hG.2 e hem).2
    · exact (hG.2 e hem).1
  dsimp only [bfsVisitInner]
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 11) (lo := .reg 9) (hi := .reg 10)
    (body :=
      .assign 12 (.load (.bin .add (.reg 2) (.reg 11))) ;;
      .cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 12))) (.const 0))
        (.store (.bin .add (.reg 4) (.reg 12)) (.const 1) ;;
         .store (.bin .add (.reg 5) (.reg 7)) (.reg 12) ;;
         .assign 7 (.bin .add (.reg 7) (.const 1)))
        .nop)
    (P := fun s₁ => s₁.regs 0 = G.n ∧ s₁.regs 1 = offPtr ∧ s₁.regs 2 = adjPtr ∧
      s₁.regs 4 = visPtr ∧ s₁.regs 5 = queuePtr ∧ s₁.regs 6 = qhead + 1 ∧
      s₁.regs 7 = st.regs 7 ∧ s₁.regs 8 = q ∧ s₁.regs 9 = pSt ∧ s₁.regs 10 = pEn ∧
      s₁.mem = st.mem)
    (Inv := bfsVisitInnerInv G offPtr adjPtr s visPtr queuePtr qhead q pSt pEn mem st.mem rem0)
    32 pSt pEn hp_le hw1 (fun _ => hpEn_w)
    (fun s₁ ⟨r0, r1, r2, r4, r5, r6, r7, r8, r9, r10, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      dsimp only [bfsVisitInnerInv]
      let s₁' : State := { s₁ with regs := Function.update s₁.regs 11 pSt }
      change s₁'.regs 0 = G.n ∧ s₁'.regs 1 = offPtr ∧ s₁'.regs 2 = adjPtr ∧ s₁'.regs 4 = visPtr ∧
        s₁'.regs 5 = queuePtr ∧ s₁'.regs 6 = qhead + 1 ∧ s₁'.regs 8 = q ∧
        s₁'.regs 9 = pSt ∧ s₁'.regs 10 = pEn ∧ s₁'.regs 11 = pSt ∧
        qhead + 1 ≤ s₁'.regs 7 ∧ s₁'.regs 7 ≤ G.n ∧
        s₁'.mem (visPtr + s) = 1 ∧
        (∀ u < G.n, mem (visPtr + u) = 1 → s₁'.mem (visPtr + u) = 1) ∧
        (∀ u < G.n, st.mem (visPtr + u) = 1 → s₁'.mem (visPtr + u) = 1) ∧
        (∀ u < G.n, s₁'.mem (visPtr + u) = 0 ∨ s₁'.mem (visPtr + u) = 1) ∧
        (∀ u < G.n, mem (visPtr + u) = 0 → s₁'.mem (visPtr + u) = 1 → G_nl.Connected s u) ∧
        (∀ u < G.n, mem (visPtr + u) = 0 → s₁'.mem (visPtr + u) = 1 →
          ∃ j < s₁'.regs 7, s₁'.mem (queuePtr + j) = u) ∧
        (∀ j < s₁'.regs 7,
          s₁'.mem (queuePtr + j) < G.n ∧ s₁'.mem (visPtr + s₁'.mem (queuePtr + j)) = 1 ∧
          G_nl.Connected s (s₁'.mem (queuePtr + j))) ∧
        ((List.range (s₁'.regs 7)).map fun j => s₁'.mem (queuePtr + j)).Nodup ∧
        (∀ j < qhead, ∀ p, mem (offPtr + s₁'.mem (queuePtr + j)) ≤ p →
          p < mem (offPtr + (s₁'.mem (queuePtr + j) + 1)) → s₁'.mem (visPtr + s₁'.mem (adjPtr + p)) = 1) ∧
        (∀ p, pSt ≤ p → p < pSt → s₁'.mem (visPtr + s₁'.mem (adjPtr + p)) = 1) ∧
        (∀ j < qhead + 1, j < s₁'.regs 7 → s₁'.mem (queuePtr + j) = st.mem (queuePtr + j)) ∧
        (∀ a, a < visPtr ∨ visPtr + 2 * G.n ≤ a → s₁'.mem a = mem a) ∧
        bfsRemTotal G offPtr visPtr queuePtr mem s₁' ≤ rem0
      have hm' : s₁'.mem = st.mem := hm
      have h6s : s₁'.regs 6 = qhead + 1 := by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r6]
      have h7s : s₁'.regs 7 = st.regs 7 := by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r7]
      refine ⟨by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r0],
        by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r1],
        by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r2],
        by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r4],
        by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r5],
        h6s,
        by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r8],
        by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r9],
        by dsimp only [s₁']; rw [Function.update_of_ne (by omega), r10],
        by dsimp only [s₁']; rw [Function.update_self],
        by rw [h7s]; omega, by rw [h7s]; exact hst7n,
        by rw [hm']; exact hst_s,
        fun u hu h => by rw [hm']; exact hst_mon0 u hu h,
        fun u hu h => by rw [hm']; exact h,
        fun u hu => by rw [hm']; exact hst_01 u hu,
        fun u hu h0 h1 => by rw [hm'] at h1; exact hst_conn u hu h0 h1,
        fun u hu h0 h1 => by rw [hm'] at h1; rw [h7s, hm']; exact hst_qex u hu h0 h1,
        fun j hj => by rw [h7s] at hj; rw [hm']; exact hst_qinfo j hj,
        by rw [h7s, hm']; exact hst_qnd,
        fun j hj p' hp1 hp2 => by rw [hm'] at *; exact hst_qcl j (h6 ▸ hj) p' hp1 hp2,
        fun p' hp1 hp2 => absurd hp2 (Nat.not_lt_of_ge hp1),
        fun _ _ _ => by rw [hm'],
        fun a ha => by rw [hm']; exact hst_fa a ha, ?_⟩
      have hIco : Finset.Ico qhead (st.regs 7) = insert qhead (Finset.Ico (qhead + 1) (st.regs 7)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnin : qhead ∉ Finset.Ico (qhead + 1) (st.regs 7) := by simp
      have hqDeg : qDegSum offPtr queuePtr mem st = (pEn - pSt) + qDegSum offPtr queuePtr mem s₁' := by
        dsimp only [qDegSum]; rw [h6, h6s, h7s, hm', hIco, Finset.sum_insert hnin, hqq, hpSt_def, hpEn_def]
      dsimp only [rem0, bfsRemTotal] at *
      have hcz := visZero_congr (n := G.n) (visPtr := visPtr) (offPtr := offPtr) (m0 := mem)
        (mem₁ := s₁'.mem) (mem₂ := st.mem) (fun u _ => by rw [hm'])
      rw [h6s, h7s, hqDeg, hcz.1, hcz.2]
      omega)
    (fun _ s₁ _ _ hi => hi.2.2.2.2.2.2.2.2.2.1)
    (fun _ s₁ _ _ hi => by have h10 := hi.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun pIdx hpSt_le hp_lt_En => by
      intro s₁ _ ⟨r0, r1, r2, r4, r5, r6, r8, r9, r10, r11, h67', h7n, hms, hmon0, hmonst, hs01,
        hconn, hqex, hqinfo, hqnd, hqcl, hpcl, hqpref, hfa, hrem_sub⟩
      have hadj_mem : s₁.mem (adjPtr + pIdx) = mem (adjPtr + pIdx) :=
        hfa _ (Or.inl (by omega))
      obtain ⟨e, he_nl, htail_or_head⟩ := hcsr.2.2.2.1 q hq_lt_n pIdx (hpSt_def.symm ▸ hpSt_le)
        (hpEn_def.symm ▸ hp_lt_En)
      set wv := mem (adjPtr + pIdx)
      have hwv_lt_n : wv < G.n := by
        have hem : e < G.m := (mem_nonloopEdges_iff.mp he_nl).1
        rcases htail_or_head with ⟨_, hw_eq⟩ | ⟨_, hw_eq⟩
        · rw [hw_eq]; exact (hG.2 e hem).2
        · rw [hw_eq]; exact (hG.2 e hem).1
      have hwv_conn : G_nl.Connected s wv := by
        have heE : e ∈ G_nl.E := List.mem_toFinset.mpr he_nl
        have hqw : G_nl.Connected q wv := by
          rcases htail_or_head with ⟨ht, hh⟩ | ⟨hh, ht⟩
          · have hdst : G_nl.dst (e, true) = wv := by simp only [MGraph.dst, G_nl, ↓reduceIte]; exact hh.symm
            exact ⟨[(e, true)], .cons heE (by simp only [MGraph.src, G_nl, ↓reduceIte]; exact ht)
              (hdst.symm ▸ .nil wv)⟩
          · have hdst : G_nl.dst (e, false) = wv := by simp only [MGraph.dst, G_nl, Bool.false_eq_true, ↓reduceIte]; exact ht.symm
            exact ⟨[(e, false)], .cons heE (by simp only [MGraph.src, G_nl, Bool.false_eq_true, ↓reduceIte]; exact hh)
              (hdst.symm ▸ .nil wv)⟩
        exact connected_trans hq_conn hqw
      have hvw01 := hs01 wv hwv_lt_n
      have hvw_lt_2w : s₁.mem (visPtr + wv) < 2 ^ w := by rcases hvw01 with h0 | h1 <;> omega
      let s₂ : State := { s₁ with regs := Function.update s₁.regs 12 wv }
      have hcond_s2 : (Expr.bin .eq (.load (.bin .add (.reg 4) (.reg 12))) (.const 0)).eval w s₂ =
          some (if s₁.mem (visPtr + wv) = 0 then 1 else 0) :=
        Expr.eval_eq_op
          (Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_reg_of_eq (by dsimp only [s₂]; rw [Function.update_of_ne (by omega), r4] : _ = visPtr))
              (Expr.eval_reg_of_eq (by dsimp only [s₂]; rw [Function.update_self] : _ = wv)) (by omega))
            (rfl : s₁.mem (visPtr + wv) = _))
          (Expr.eval_const (by omega)) hw1
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r11) (by omega)) hadj_mem) ?_
      refine runs_cond_le hcond_s2 ?_ ?_
      · intro hcond
        have hvw_zero : s₁.mem (visPtr + wv) = 0 := by
          by_contra hne; apply hcond; simp [hne]
        have hwv_not_mem : ∀ j < s₁.regs 7, s₁.mem (queuePtr + j) ≠ wv := fun j hj heq => by
          have := (hqinfo j hj).2.1; rw [heq, hvw_zero] at this; exact absurd this (by norm_num)
        have hq7_lt_n : s₁.regs 7 < G.n := by
          let Qset := ((List.range (s₁.regs 7)).map fun j => s₁.mem (queuePtr + j)).toFinset
          have hQcard : Qset.card = s₁.regs 7 := by
            rw [List.toFinset_card_of_nodup hqnd, List.length_map, List.length_range]
          have hsub : insert wv Qset ⊆ Finset.range G.n := by
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hxQ
            · exact Finset.mem_range.mpr hwv_lt_n
            · rw [List.mem_toFinset, List.mem_map] at hxQ
              obtain ⟨j, hj, rfl⟩ := hxQ
              exact Finset.mem_range.mpr (hqinfo j (List.mem_range.mp hj)).1
          have hnin_Q : wv ∉ Qset := fun hm => by
            rw [List.mem_toFinset, List.mem_map] at hm
            obtain ⟨j, hj, heq⟩ := hm
            exact hwv_not_mem j (List.mem_range.mp hj) heq
          have := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hnin_Q, hQcard, Finset.card_range] at this; exact this
        have hwv_old0 : mem (visPtr + wv) = 0 := by
          by_contra hne
          have := hmon0 wv hwv_lt_n ((hvis01 wv hwv_lt_n).resolve_left hne)
          omega
        refine runs_seq_store_le
          (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r4] : _ = visPtr))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self] : _ = wv)) (by omega))
          (Expr.eval_const (by omega)) ?_
        refine runs_seq_store_le
          (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r5] : _ = queuePtr))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega)] : _ = s₁.regs 7))
            (by omega))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self] : _ = wv)) ?_
        refine runs_assign_le
          (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega)] : _ = s₁.regs 7))
            (Expr.eval_const (by omega)) (by omega)) ?_ ?_
        · dsimp only
          set m₁ := Function.update s₁.mem (visPtr + wv) 1
          set m₂ := Function.update m₁ (queuePtr + s₁.regs 7) wv
          have hflip := visZero_flip (offPtr := offPtr) (m0 := mem) hwv_lt_n hvw_zero
          have hm2_vis : ∀ x, x < visPtr + G.n → m₂ x = m₁ x := fun x hx => by
            dsimp only [m₂]; rw [Function.update_of_ne (by omega : x ≠ queuePtr + s₁.regs 7)]
          have hcz2 := visZero_congr (n := G.n) (visPtr := visPtr) (offPtr := offPtr) (m0 := mem)
            (mem₁ := m₂) (mem₂ := m₁) (fun u hu => by rw [hm2_vis _ (by omega)])
          have hvis0_m2 : visZeroCount G.n visPtr m₂ + 1 = visZeroCount G.n visPtr s₁.mem := by
            rw [hcz2.1]; exact hflip.1
          have hvis0d_m2 : visZeroDegSum G.n visPtr offPtr mem m₂ +
              (mem (offPtr + (wv + 1)) - mem (offPtr + wv)) =
              visZeroDegSum G.n visPtr offPtr mem s₁.mem := by
            rw [hcz2.2]; exact hflip.2
          refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r4], by simp [r5],
            by simp [r6], by simp [r8], by simp [r9], by simp [r10], by simp,
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]; omega,
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]; omega,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
            by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r11]⟩
          · dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_apply]
            by_cases hsw : s = wv <;> [simp [hsw]; simp [hsw, hms]]
          · intro u hu hm1; dsimp only [m₂, m₁]
            rw [Function.update_of_ne (by omega), Function.update_apply]
            by_cases huw : u = wv <;> [simp [huw]; simp [huw, hmon0 u hu hm1]]
          · intro u hu hst1; dsimp only [m₂, m₁]
            rw [Function.update_of_ne (by omega), Function.update_apply]
            by_cases huw : u = wv <;> [simp [huw]; simp [huw, hmonst u hu hst1]]
          · intro u hu; dsimp only [m₂, m₁]
            rw [Function.update_of_ne (by omega), Function.update_apply]
            by_cases huw : u = wv <;> [simp [huw]; simp [huw, hs01 u hu]]
          · intro u hu hm0 hm2; dsimp only [m₂, m₁] at hm2
            rw [Function.update_of_ne (by omega), Function.update_apply] at hm2
            by_cases huw : u = wv
            · subst huw; exact hwv_conn
            · rw [ite_eq_right (by omega)] at hm2; exact hconn u hu hm0 hm2
          · intro u hu hm0 hm2; dsimp only [m₂, m₁] at hm2
            rw [Function.update_of_ne (by omega), Function.update_apply] at hm2
            dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]
            by_cases huw : u = wv
            · subst huw; exact ⟨s₁.regs 7, by omega, by dsimp only [m₂]; rw [Function.update_self]⟩
            · rw [ite_eq_right (by omega)] at hm2
              obtain ⟨j, hj, hqj⟩ := hqex u hu hm0 hm2
              exact ⟨j, by omega, by dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]; exact hqj⟩
          · intro j hj
            dsimp only at hj; rw [Function.update_of_ne (by omega), Function.update_self] at hj
            by_cases hj' : j < s₁.regs 7
            · obtain ⟨hj1, hj2, hj3⟩ := hqinfo j hj'
              have hqeq : m₂ (queuePtr + j) = s₁.mem (queuePtr + j) := by
                dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              dsimp only; rw [hqeq]; dsimp only [m₂, m₁]
              rw [Function.update_of_ne (by omega), Function.update_apply]
              by_cases hqw : s₁.mem (queuePtr + j) = wv
              · simp [hqw]; exact ⟨hwv_lt_n, hwv_conn⟩
              · simp [hqw, hj1, hj2, hj3]
            · have hje : j = s₁.regs 7 := by omega
              subst hje
              have hqeq : m₂ (queuePtr + s₁.regs 7) = wv := by dsimp only [m₂]; rw [Function.update_self]
              dsimp only; rw [hqeq]; dsimp only [m₂, m₁]
              rw [Function.update_of_ne (by omega), Function.update_self]
              exact ⟨hwv_lt_n, rfl, hwv_conn⟩
          · dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]
            rw [List.range_succ, List.map_append, List.map_singleton, List.nodup_append]
            refine ⟨?_, List.nodup_singleton _, fun x hx y hy heq => ?_⟩
            · have : (List.range (s₁.regs 7)).map (fun j => m₂ (queuePtr + j)) =
                  (List.range (s₁.regs 7)).map (fun j => s₁.mem (queuePtr + j)) := by
                refine List.map_congr_left fun j hj => ?_
                have hj' := List.mem_range.mp hj
                dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              rw [this]; exact hqnd
            · rw [List.mem_map] at hx; rw [List.mem_singleton] at hy; subst hy
              obtain ⟨j, hj, rfl⟩ := hx
              have hj' := List.mem_range.mp hj
              have hqeq : m₂ (queuePtr + j) = s₁.mem (queuePtr + j) := by
                dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              rw [hqeq] at heq
              have hm_w : m₂ (queuePtr + s₁.regs 7) = wv := by dsimp only [m₂]; rw [Function.update_self]
              rw [hm_w] at heq
              exact hwv_not_mem j hj' heq
          · intro j hj p' hp1 hp2
            have hqeq : m₂ (queuePtr + j) = s₁.mem (queuePtr + j) := by
              dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            dsimp only at hp1 hp2
            rw [hqeq] at hp1 hp2
            have hqj_n := (hqinfo j (by omega)).1
            have hp_2nl : p' < 2 * (nonloopEdges G).length :=
              lt_of_lt_of_le hp2 (csr_off_le_2nl hcsr hqj_n)
            have ha_lt_n : s₁.mem (adjPtr + p') < G.n :=
              hadj_lt_n _ p' s₁.mem hqj_n hp1 hp2 (hfa _ (Or.inl (by omega)))
            have haeq : m₂ (adjPtr + p') = s₁.mem (adjPtr + p') := by
              dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            dsimp only; rw [haeq]
            have hsv := hqcl j hj p' hp1 hp2
            dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_apply]
            by_cases hsw : s₁.mem (adjPtr + p') = wv <;> [simp [hsw]; simp [hsw, hsv]]
          · intro p' hp1 hp2
            have hp_2nl : p' < 2 * (nonloopEdges G).length := lt_of_lt_of_le (by omega) hpEn_le_2nl
            have ha_lt_n : s₁.mem (adjPtr + p') < G.n :=
              hadj_lt_n q p' s₁.mem hq_lt_n (by omega) (by omega) (hfa _ (Or.inl (by omega)))
            have haeq : m₂ (adjPtr + p') = s₁.mem (adjPtr + p') := by
              dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            dsimp only; rw [haeq]
            by_cases hpp : p' = pIdx
            · subst hpp; rw [hadj_mem]
              dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_self]
            · have h1 := hpcl p' hp1 (by omega)
              dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_apply]
              by_cases hsw : s₁.mem (adjPtr + p') = wv <;> [simp [hsw]; simp [hsw, h1]]
          · intro j hj1 hj2
            dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hqpref j hj1 (by omega)
          · intro a ha
            dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfa a ha
          · have hqDeg_step : qDegSum offPtr queuePtr mem
                { mem := m₂,
                  regs := Function.update (Function.update (Function.update s₁.regs 12 wv) 7 (s₁.regs 7 + 1)) 11 (pIdx + 1),
                  pos := s₁.pos } =
                qDegSum offPtr queuePtr mem s₁ + (mem (offPtr + (wv + 1)) - mem (offPtr + wv)) := by
              dsimp only [qDegSum]
              simp only [Function.update_of_ne (by omega : 6 ≠ 11), Function.update_of_ne (by omega : 6 ≠ 7),
                Function.update_of_ne (by omega : 6 ≠ 12), Function.update_of_ne (by omega : 7 ≠ 11),
                Function.update_self, r6]
              have hIco : Finset.Ico (qhead + 1) (s₁.regs 7 + 1) =
                  insert (s₁.regs 7) (Finset.Ico (qhead + 1) (s₁.regs 7)) := by
                ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
              have hnin : s₁.regs 7 ∉ Finset.Ico (qhead + 1) (s₁.regs 7) := by simp
              rw [hIco, Finset.sum_insert hnin]
              have hlast : m₂ (queuePtr + s₁.regs 7) = wv := by dsimp only [m₂]; rw [Function.update_self]
              rw [hlast, Nat.add_comm]
              congr 1
              refine Finset.sum_congr rfl fun j hj => ?_
              have hj' := Finset.mem_Ico.mp hj
              have hm2j : m₂ (queuePtr + j) = s₁.mem (queuePtr + j) := by
                dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              rw [hm2j]
            dsimp only at hrem_sub ⊢
            dsimp only [bfsRemTotal] at hrem_sub ⊢
            rw [hqDeg_step]
            rw [← hvis0_m2, ← hvis0d_m2] at hrem_sub
            dsimp only [m₁, m₂] at *
            simp only [Function.update_of_ne (by omega : 6 ≠ 11), Function.update_of_ne (by omega : 6 ≠ 7),
              Function.update_of_ne (by omega : 6 ≠ 12), Function.update_of_ne (by omega : 7 ≠ 11),
              Function.update_self, r6] at *
            omega
        · wram_cost
      · intro hcond
        have hvw_one : s₁.mem (visPtr + wv) = 1 := by
          have hne : s₁.mem (visPtr + wv) ≠ 0 := by intro h0; simp [wv, h0] at hcond
          exact hvw01.resolve_left hne
        refine runs_nop_le ?_ ?_
        · refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r4], by simp [r5],
            by simp [r6], by simp [r8], by simp [r9], by simp [r10], by simp, h67', h7n,
            hms, hmon0, hmonst, hs01, hconn, hqex, hqinfo, hqnd, hqcl, ?_, hqpref, hfa, ?_⟩,
            by dsimp only; rw [Function.update_of_ne (by omega), r11]⟩
          · intro p' hp1 hp2
            by_cases hpp : p' = pIdx
            · subst hpp; rw [hadj_mem]; exact hvw_one
            · exact hpcl p' hp1 (by omega)
          · dsimp only [bfsRemTotal] at hrem_sub ⊢
            have hqeq : qDegSum offPtr queuePtr mem
                { mem := s₁.mem, regs := Function.update (Function.update s₁.regs 12 wv) 11 (pIdx + 1), pos := s₁.pos } =
                qDegSum offPtr queuePtr mem s₁ := rfl
            rw [hqeq]
            simp only [Function.update_of_ne (by omega : 7 ≠ 11), Function.update_of_ne (by omega : 7 ≠ 12),
              Function.update_of_ne (by omega : 6 ≠ 11), Function.update_of_ne (by omega : 6 ≠ 12)]
            omega
        · wram_cost)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned _ => exact False.elim h
    | normal => exact h
  · intro _ _; simp only [Expr.size_reg]; omega

theorem bfsVisit_exact_meetsContract {G : IndexedGraph} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [bfsVisit]) :
    MeetsContract w p b (bfsVisitExactContract G w) := by
  classical
  have hproc : p.procs[b]? = some bfsVisit := hp 0 (by simp)
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨offPtr, adjPtr, s, visPtr, queuePtr, rfl, hG, hw16, hs_lt, hs0,
    hoff_disj, hadj_disj, hq_eq, hq_w, hcsr, hvis01, hvis_closed⟩
  set G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  have hw1 : 1 < 2 ^ w := by omega
  let U := unreachUnvisSet G visPtr s mem
  let R := reachUnvisSet G visPtr s mem
  let K_unreach := 120 * U.card + 120 * ∑ u ∈ U, (mem (offPtr + (u + 1)) - mem (offPtr + u))
  let condExpr : Expr := .bin .lt (.reg 6) (.reg 7)
  let loopBody : Stmt :=
    .assign 8 (.load (.bin .add (.reg 5) (.reg 6))) ;;
    .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
    .assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
    .assign 10 (.load (.bin .add (.reg 1) (.bin .add (.reg 8) (.const 1)))) ;;
    bfsVisitInner
  have hK_le : ∀ st, bfsVisitLoopInv G offPtr adjPtr s visPtr queuePtr mem st →
      K_unreach ≤ 120 * visZeroCount G.n visPtr st.mem +
        120 * visZeroDegSum G.n visPtr offPtr mem st.mem := fun st hInv => by
    have hsub : U ⊆ (Finset.range G.n).filter (fun u => st.mem (visPtr + u) = 0) := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have hun := Finset.mem_range.mp hu'.1
      rw [Finset.mem_filter]
      refine ⟨hu'.1, ?_⟩
      rcases hInv.2.2.2.2.2.2.2.2.2.1 u hun with h0 | h1
      · exact h0
      · exact absurd (hInv.2.2.2.2.2.2.2.2.2.2.1 u hun hu'.2.1 h1) hu'.2.2
    have hc := Finset.card_le_card hsub
    have hs := Finset.sum_le_sum_of_subset (f := fun u => mem (offPtr + (u + 1)) - mem (offPtr + u)) hsub
    change 120 * U.card + 120 * ∑ u ∈ U, (mem (offPtr + (u + 1)) - mem (offPtr + u)) ≤ _
    change _ ≤ 120 * ((Finset.range G.n).filter (fun u => st.mem (visPtr + u) = 0)).card +
      120 * ∑ u ∈ (Finset.range G.n).filter (fun u => st.mem (visPtr + u) = 0),
        (mem (offPtr + (u + 1)) - mem (offPtr + u))
    omega
  have hloop := Triple.loop_measure (w := w) (p := p) (e := condExpr) (body := loopBody)
    (Inv := bfsVisitLoopInv G offPtr adjPtr s visPtr queuePtr mem)
    (Q := normalPost fun st => bfsVisitLoopInv G offPtr adjPtr s visPtr queuePtr mem st ∧ st.regs 6 = st.regs 7)
    (m := fun st => G.n - st.regs 6)
    (rem := fun st => bfsRemTotal G offPtr visPtr queuePtr mem st - K_unreach)
    (condVal := fun st => if st.regs 6 < st.regs 7 then 1 else 0)
    (fun st hInv => by
      have := hInv.2.2.2.2.2.1; have := hInv.2.2.2.2.2.2.1
      have h6w : st.regs 6 < 2 ^ w := by omega
      have h7w : st.regs 7 < 2 ^ w := by omega
      eval_expr)
    (fun st hInv hcv => by
      have h67 : st.regs 6 = st.regs 7 := by
        have := hInv.2.2.2.2.2.1; by_contra hne; simp [show st.regs 6 < st.regs 7 by omega] at hcv
      have hk := hK_le st hInv
      dsimp only [bfsRemTotal, condExpr, Expr.size_bin, Expr.size_reg]
      exact ⟨⟨hInv, h67⟩, by omega⟩)
    (fun st hInv hcv => by
      have hr0 := hInv.1
      have hr1 := hInv.2.1
      have hr5 := hInv.2.2.2.2.1
      have h67_st := hInv.2.2.2.2.2.1
      have h7n_st := hInv.2.2.2.2.2.2.1
      have h6_lt_7 : st.regs 6 < st.regs 7 := by by_contra hle; simp [hle] at hcv
      set qhead := st.regs 6
      have hq_info := hInv.2.2.2.2.2.2.2.2.2.2.2.2.1 qhead h6_lt_7
      set q := st.mem (queuePtr + qhead)
      set pSt := mem (offPtr + q)
      set pEn := mem (offPtr + (q + 1))
      have hp_le : pSt ≤ pEn := hcsr.2.1 q hq_info.1
      have hpSt_eq : st.mem (offPtr + q) = pSt := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (Or.inl (by omega))
      have hpEn_eq : st.mem (offPtr + (q + 1)) = pEn := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (Or.inl (by omega))
      have hp_le_2nl : pEn ≤ 2 * (nonloopEdges G).length :=
        csr_off_le_2nl hcsr hq_info.1
      have hinner := bfsVisit_inner_triple (p := p) hG hw1 hs_lt hq_info.1 hq_info.2.2 hoff_disj hadj_disj
        hq_eq hq_w hcsr hp_le rfl rfl hvis01 hInv rfl h6_lt_7 rfl
      refine ⟨28 + ((pEn - pSt) * 41 + 7), fun s0 ω' hs0 => ?_⟩
      subst s0
      refine runs_start_le ?_
      dsimp only [loopBody]
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hr5) (Expr.eval_reg_of_eq (rfl : st.regs 6 = _)) (by omega))
        (rfl : st.mem (queuePtr + qhead) = _)) ?_
      refine runs_seq_assign_le (Expr.eval_add
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega)] : _ = qhead))
        (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), hr1] : _ = offPtr))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self] : _ = q))
          (by omega)) hpSt_eq) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), hr1] : _ = offPtr))
          (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self] : _ = q))
            (Expr.eval_const (by omega)) (by omega)) (by omega)) hpEn_eq) ?_
      refine runs_triple_le hinner
        ⟨by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), hr0],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), hr1],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), hInv.2.2.1],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), hInv.2.2.2.1],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), hr5],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self],
         by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
         by dsimp only; rw [Function.update_self], rfl⟩
        ?_ (by simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega)
      · intro o s_end hs_end
        cases o with
        | returned _ => exact False.elim hs_end
        | normal =>
          rcases hs_end with ⟨e0, e1, e2, e4, e5, e6, e8, e9, e10, _, e67, e7n, ems, emon0, _, es01,
            econn, eqex, eqinfo, eqnd, eqcl, epcl, eqpref, efa, erem⟩
          have hInv_end : bfsVisitLoopInv G offPtr adjPtr s visPtr queuePtr mem s_end := by
            refine ⟨e0, e1, e2, e4, e5, by omega, e7n, ems, emon0, es01, econn, eqex, eqinfo, eqnd, ?_, efa⟩
            intro j hj p' hp1 hp2
            by_cases hjq : j = qhead
            · subst hjq
              have := eqpref qhead (by omega) (by omega)
              rw [this] at hp1 hp2
              exact epcl p' hp1 hp2
            · exact eqcl j (by omega) p' hp1 hp2
          have hk_end := hK_le s_end hInv_end
          dsimp only [bfsRemTotal, condExpr, Expr.size_bin, Expr.size_reg] at hk_end erem ⊢
          have hm_lt : G.n - s_end.regs 6 < G.n - st.regs 6 := by
            have := hInv.2.2.2.2.2.2.1; omega
          refine ⟨hInv_end, hm_lt, ?_⟩
          omega)
  refine runs_start_le ?_
  dsimp only [bfsVisit]
  have s0 : (startState [G.n, offPtr, adjPtr, s, visPtr, queuePtr] mem pos).regs 0 = G.n := rfl
  have s1 : (startState [G.n, offPtr, adjPtr, s, visPtr, queuePtr] mem pos).regs 1 = offPtr := rfl
  have s2 : (startState [G.n, offPtr, adjPtr, s, visPtr, queuePtr] mem pos).regs 2 = adjPtr := rfl
  have s3 : (startState [G.n, offPtr, adjPtr, s, visPtr, queuePtr] mem pos).regs 3 = s := rfl
  have s4 : (startState [G.n, offPtr, adjPtr, s, visPtr, queuePtr] mem pos).regs 4 = visPtr := rfl
  have s5 : (startState [G.n, offPtr, adjPtr, s, visPtr, queuePtr] mem pos).regs 5 = queuePtr := rfl
  refine runs_seq_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq s4) (Expr.eval_reg_of_eq s3) (by omega))
    (Expr.eval_const (by omega)) ?_
  refine runs_seq_store_le
    (Expr.eval_reg_of_eq s5) (Expr.eval_reg_of_eq s3) ?_
  refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
  set m₁ := Function.update mem (visPtr + s) 1
  set m₂ := Function.update m₁ queuePtr s
  have hm2_vis : ∀ x, x < visPtr + G.n → m₂ x = m₁ x := fun x hx => by
    dsimp only [m₂]; rw [Function.update_of_ne (by omega : x ≠ queuePtr)]
  have hInv0 : bfsVisitLoopInv G offPtr adjPtr s visPtr queuePtr mem
      { mem := m₂,
        regs := Function.update (Function.update (startState [G.n, offPtr, adjPtr, s, visPtr, queuePtr] mem pos).regs 6 0) 7 1,
        pos := pos } := by
    refine ⟨by simp [s0], by simp [s1], by simp [s2], by simp [s4], by simp [s5],
      by simp, by simp; exact hG.1,
      by dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_self],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu hu1; dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_apply]
      by_cases hus : u = s <;> [simp [hus]; simp [hus, hu1]]
    · intro u hu; dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_apply]
      by_cases hus : u = s <;> [simp [hus]; simp [hus, hvis01 u hu]]
    · intro u hu hu0 hm2; dsimp only [m₂, m₁] at hm2
      rw [Function.update_of_ne (by omega : visPtr + u ≠ queuePtr), Function.update_apply] at hm2
      by_cases hus : u = s
      · subst u; exact ⟨[], .nil s⟩
      · rw [ite_eq_right (by omega), hu0] at hm2; exact absurd hm2 (by norm_num)
    · intro u hu hu0 hm2; dsimp only [m₂, m₁] at hm2
      rw [Function.update_of_ne (by omega : visPtr + u ≠ queuePtr), Function.update_apply] at hm2
      by_cases hus : u = s
      · subst u; refine ⟨0, by simp, ?_⟩; dsimp only [m₂]; rw [Nat.add_zero, Function.update_self]
      · rw [ite_eq_right (by omega), hu0] at hm2; exact absurd hm2 (by norm_num)
    · intro j hj
      have hj0 : j = 0 := by simp at hj; exact hj
      subst hj0
      dsimp only [m₂, m₁]; rw [Nat.add_zero, Function.update_self, Function.update_of_ne (by omega),
        Function.update_self]
      exact ⟨hs_lt, rfl, ⟨[], .nil s⟩⟩
    · simp
    · intro j hj; simp at hj
    · intro a ha; dsimp only [m₂, m₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine runs_seq_triple_le hloop hInv0 ?_
  · intro st₁ ⟨hInv₁, h67_1⟩
    rcases hInv₁ with ⟨_, _, _, _, _, h67_st, h7n_st, hs1_st, hmon0_st, h01_st, hconn_st,
      hqex_st, hqinfo_st, hqnd_st, hqcl_st, hfa_st⟩
    refine runs_ret_le (Expr.eval_const (by omega)) ?_ ?_
    · have hcl₁ : ∀ e ∈ nonloopEdges G, st₁.mem (visPtr + G.tail e) = 1 ↔ st₁.mem (visPtr + G.head e) = 1 := by
        intro e he
        have het := (hG.2 e (mem_nonloopEdges_iff.mp he).1).1
        have heh := (hG.2 e (mem_nonloopEdges_iff.mp he).1).2
        obtain ⟨⟨p1, hp1a, hp1b, hp1c⟩, ⟨p2, hp2a, hp2b, hp2c⟩⟩ := hcsr.2.2.2.2 e he
        constructor
        · intro h1
          rcases hvis01 _ het with ht0 | ht1
          · obtain ⟨j, hj, hqj⟩ := hqex_st _ het ht0 h1
            have hp1_lt : p1 < 2 * (nonloopEdges G).length :=
              lt_of_lt_of_le hp1b (csr_off_le_2nl hcsr (by omega))
            have hmem := hqcl_st j (by omega) p1 (hqj.symm ▸ hp1a) (hqj.symm ▸ hp1b)
            rw [hfa_st (adjPtr + p1) (Or.inl (by omega)), hp1c] at hmem
            exact hmem
          · exact hmon0_st _ heh ((hvis_closed e he).mp ht1)
        · intro h1
          rcases hvis01 _ heh with hh0 | hh1
          · obtain ⟨j, hj, hqj⟩ := hqex_st _ heh hh0 h1
            have hp2_lt : p2 < 2 * (nonloopEdges G).length :=
              lt_of_lt_of_le hp2b (csr_off_le_2nl hcsr (by omega))
            have hmem := hqcl_st j (by omega) p2 (hqj.symm ▸ hp2a) (hqj.symm ▸ hp2b)
            rw [hfa_st (adjPtr + p2) (Or.inl (by omega)), hp2c] at hmem
            exact hmem
          · exact hmon0_st _ het ((hvis_closed e he).mpr hh1)
      have hU_eq : (Finset.range G.n).filter (fun u => st₁.mem (visPtr + u) = 0) = U := by
        ext u
        simp only [U, unreachUnvisSet, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hun, hu0⟩
          refine ⟨hun, ?_, ?_⟩
          · rcases hvis01 u hun with h0 | h1
            · exact h0
            · exact absurd (hmon0_st u hun h1) (by omega)
          · intro hc
            obtain ⟨P, hP⟩ := hc
            have := vis_walk_invariant hcl₁ hP hs1_st
            omega
        · rintro ⟨hun, hu0, hn⟩
          refine ⟨hun, ?_⟩
          rcases h01_st u hun with h0 | h1
          · exact h0
          · exact absurd (hconn_st u hun hu0 h1) hn
      have hvc : visZeroCount G.n visPtr st₁.mem = U.card := congrArg Finset.card hU_eq
      have hvd : visZeroDegSum G.n visPtr offPtr mem st₁.mem =
          ∑ u ∈ U, (mem (offPtr + (u + 1)) - mem (offPtr + u)) := congrArg (Finset.sum · _) hU_eq
      have hpart := visZero_partition G visPtr offPtr s mem mem
      have hs_R : s ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs_lt, hs0, ⟨[], .nil s⟩⟩
      have hR_pos : 1 ≤ R.card := Finset.card_pos.mpr ⟨s, hs_R⟩
      have hc1 : visZeroCount G.n visPtr st₁.mem + R.card = visZeroCount G.n visPtr mem := by
        dsimp only [R, U] at hvc hpart ⊢; omega
      have hd1 : visZeroDegSum G.n visPtr offPtr mem st₁.mem +
          (∑ u ∈ R, (mem (offPtr + (u + 1)) - mem (offPtr + u))) =
          visZeroDegSum G.n visPtr offPtr mem mem := by
        dsimp only [R, U] at hvd hpart ⊢; omega
      refine ⟨⟨offPtr, adjPtr, s, visPtr, queuePtr, rfl,
        hs1_st, hmon0_st, h01_st, hconn_st, hcl₁, hfa_st, by rw [hvc]; dsimp only [R, U] at hR_pos hpart ⊢; omega⟩,
        ⟨offPtr, adjPtr, s, visPtr, queuePtr, rfl, hc1, hd1⟩⟩
    · have hpart := visZero_partition G visPtr offPtr s mem mem
      have hflip := visZero_flip (offPtr := offPtr) (m0 := mem) hs_lt hs0
      have hcz2 := visZero_congr (n := G.n) (visPtr := visPtr) (offPtr := offPtr) (m0 := mem)
        (mem₁ := m₂) (mem₂ := m₁) (fun u hu => by rw [hm2_vis _ (by omega)])
      have hs_R : s ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs_lt, hs0, ⟨[], .nil s⟩⟩
      have hR_pos : 1 ≤ R.card := Finset.card_pos.mpr ⟨s, hs_R⟩
      dsimp only [bfsVisitExactContract, bfsVisitExactCost, bfsRemTotal, qDegSum, R, U, K_unreach, m₂, m₁,
        startState] at hpart hflip hcz2 hR_pos ⊢
      simp only [Function.update_of_ne (by omega : 6 ≠ 7), Function.update_self,
        Expr.size_bin, Expr.size_reg, Expr.size_const, Nat.sub_zero]
      rw [show Finset.Ico 0 1 = {0} by ext x; simp, Finset.sum_singleton,
        show queuePtr + 0 = queuePtr by omega, Function.update_self, hcz2.1, hcz2.2]
      omega

theorem bfsVisit_meetsContract {G : IndexedGraph} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [bfsVisit]) :
    MeetsContract w p b (bfsVisitContract G w) := by
  classical
  intro args mem pos ω hwords hpre
  obtain ⟨body, hproc, o, st', c, hrun, ⟨hpost, _⟩, hc⟩ :=
    (bfsVisit_exact_meetsContract hp) args mem pos ω hwords hpre
  refine ⟨body, hproc, o, st', c, hrun, hpost, hc.trans ?_⟩
  rcases hpre with ⟨offPtr, adjPtr, s, visPtr, queuePtr, rfl, _, _, _, _, _, _, _, _, _, _, _⟩
  have hpart := visZero_partition G visPtr offPtr s mem mem
  dsimp only [bfsVisitExactContract, bfsVisitExactCost, bfsVisitContract]
  omega


end MinCostFlow.WideWord
