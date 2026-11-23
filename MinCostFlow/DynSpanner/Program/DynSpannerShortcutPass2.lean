module

public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutPush

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pass 2 Backward Scan for `dsShortcutEmbStmt` (`DynSpannerShortcutPass2`)

Defines `Pass2Inv` and proves `shortcut_pass2_triple` with linear amortized cost via
`rangeCost_shortcut_step`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

/-- Pass 2 backward loop invariant (`forRange 13 0 P.length`). -/
@[expose] def Pass2Inv (vCap vStampPtr stampVal gen0 nodeBase vEnd : ℕ)
    (G : MGraph) (u : ℕ) (P : List (ℕ × Bool)) (mem0 : ℕ → ℕ) (regs0 : ℕ → ℕ)
    (j : ℕ) (st : State) : Prop :=
  let i := P.length - j
  let cur := vertAt G u P i
  let Q := shortcutWalk G cur (P.drop i)
  ∃ nodePtr : ℕ,
    st.regs 13 = j ∧
    st.regs 17 = nodePtr ∧
    nodeBase ≤ nodePtr ∧
    nodePtr ≤ nodeBase + 4 * j ∧
    (∀ r, (r ≤ 11 ∨ r = 16 ∨ r = 19) → st.regs r = regs0 r) ∧
    cur ∈ G.V ∧ G.IsWalk cur vEnd Q ∧ (G.walkVertices cur Q).Nodup ∧
    StackListIn G nodeBase nodePtr st.mem (st.regs 18) cur Q ∧
    VStampInv st.mem vStampPtr vCap stampVal gen0 (G.walkVertices cur Q) ∧
    ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) → (addr < nodeBase ∨ nodePtr ≤ addr) →
      st.mem addr = mem0 addr

theorem shortcut_pass2_triple {w vCap vStampPtr stampVal gen0 permPtr wPtr nodeBase vEnd : ℕ}
    {G : MGraph} {u : ℕ} {P : List (ℕ × Bool)} {p : Program}
    {mem0 : ℕ → ℕ} {regs0 : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hnb : nodeBase = permPtr + P.length + 1)
    (hnode1 : 1 ≤ nodeBase)
    (hnode_lt : nodeBase + 4 * P.length < 2 ^ w)
    (hvst_disj : ∀ v < vCap, vStampPtr + v < nodeBase)
    (hvst_perm : ∀ v < vCap, vStampPtr + v < permPtr)
    (hvst_w : vStampPtr + vCap < 2 ^ w)
    (hwPtr_lt : wPtr + 1 + 2 * P.length < 2 ^ w)
    (hgen_lt : gen0 < stampVal)
    (he_w : ∀ x ∈ P, x.1 < 2 ^ w)
    (hG_val : G.IsValid) (hvG : ∀ v ∈ G.V, v < vCap)
    (hu : u ∈ G.V) (hWalk : G.IsWalk u vEnd P)
    (hVarr : ∀ i ≤ P.length, mem0 (permPtr + i) = vertAt G u P i)
    (hMWalk : MWalkAt mem0 wPtr P)
    (hW_disj : ∀ a, wPtr ≤ a → a < wPtr + 1 + 2 * P.length →
      (∀ v < vCap, a ≠ vStampPtr + v) ∧ (a < nodeBase ∨ nodeBase + 4 * P.length ≤ a))
    (hr5 : regs0 5 = permPtr) (hr6 : regs0 6 = vStampPtr) (hr7 : regs0 7 = stampVal)
    (hr10 : regs0 10 = wPtr) (hr11 : regs0 11 = P.length)
    (hvEnd_stamp : VStampInv mem0 vStampPtr vCap stampVal gen0 [vEnd]) :
    Triple w p
      (fun st => st.mem = mem0 ∧
        (∀ r, (r ≤ 11 ∨ r = 16 ∨ r = 19) → st.regs r = regs0 r) ∧
        st.regs 17 = nodeBase ∧ st.regs 18 = 0)
      (forRange 13 (.const 0) (.reg 11)
        (.assign 21 (.bin .sub (.bin .sub (.reg 11) (.const 1)) (.reg 13)) ;;
         .assign 12 (.load (.bin .add (.reg 5) (.reg 21))) ;;
         .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.reg 7))
           (.cond (.reg 18)
              (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
                (.assign 20 (.const 0)) (.assign 20 (.const 1)))
              (.assign 20 (.const 0)) ;;
            .loop (.reg 20)
              (.assign 15 (.load (.reg 18)) ;;
               .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
               .assign 18 (.load (.bin .add (.reg 18) (.const 3))) ;;
               .cond (.reg 18)
                 (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
                   (.assign 20 (.const 0)) (.assign 20 (.const 1)))
                 (.assign 20 (.const 0))))
           (.assign 14 (.load (.bin .add (.reg 10)
              (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
            .assign 15 (.load (.bin .add (.reg 10)
              (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
            .store (.reg 17) (.reg 12) ;;
            .store (.bin .add (.reg 17) (.const 1)) (.reg 14) ;;
            .store (.bin .add (.reg 17) (.const 2)) (.reg 15) ;;
            .store (.bin .add (.reg 17) (.const 3)) (.reg 18) ;;
            .assign 18 (.reg 17) ;;
            .assign 17 (.bin .add (.reg 17) (.const 4)) ;;
            .store (.bin .add (.reg 6) (.reg 12)) (.reg 7))))
      (normalPost (Pass2Inv vCap vStampPtr stampVal gen0 nodeBase vEnd G u P mem0 regs0
        P.length))
      (fun _ => 125 * P.length + 15) := by
  have hw1 : 1 < 2 ^ w := by omega
  let qLen (j : ℕ) : ℕ :=
    (shortcutWalk G (vertAt G u P (P.length - j)) (P.drop (P.length - j))).length
  let stepCost (j : ℕ) : ℕ := 75 + 32 * (qLen j + 1 - qLen (j + 1))
  let Inv := Pass2Inv vCap vStampPtr stampVal gen0 nodeBase vEnd G u P mem0 regs0
  let popStmt : Stmt :=
    .cond (.reg 18)
      (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
        (.assign 20 (.const 0)) (.assign 20 (.const 1)))
      (.assign 20 (.const 0)) ;;
    .loop (.reg 20)
      (.assign 15 (.load (.reg 18)) ;;
       .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
       .assign 18 (.load (.bin .add (.reg 18) (.const 3))) ;;
       .cond (.reg 18)
         (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
           (.assign 20 (.const 0)) (.assign 20 (.const 1)))
         (.assign 20 (.const 0)))
  let pushStmt : Stmt :=
    .assign 14 (.load (.bin .add (.reg 10)
      (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
    .assign 15 (.load (.bin .add (.reg 10)
      (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
    .store (.reg 17) (.reg 12) ;;
    .store (.bin .add (.reg 17) (.const 1)) (.reg 14) ;;
    .store (.bin .add (.reg 17) (.const 2)) (.reg 15) ;;
    .store (.bin .add (.reg 17) (.const 3)) (.reg 18) ;;
    .assign 18 (.reg 17) ;;
    .assign 17 (.bin .add (.reg 17) (.const 4)) ;;
    .store (.bin .add (.reg 6) (.reg 12)) (.reg 7)
  let P0 : State → Prop := fun st => st.mem = mem0 ∧
    (∀ r, (r ≤ 11 ∨ r = 16 ∨ r = 19) → st.regs r = regs0 r) ∧
    st.regs 17 = nodeBase ∧ st.regs 18 = 0
  have hvEnd_eq : vertAt G u P P.length = vEnd := vertAt_length_eq_of_isWalk hWalk
  have hvEnd_V : vEnd ∈ G.V := hvEnd_eq ▸ vertAt_mem_V hG_val hu hWalk P.length le_rfl
  have hloop : Triple w p P0
      (forRange 13 (.const 0) (.reg 11)
        (.assign 21 (.bin .sub (.bin .sub (.reg 11) (.const 1)) (.reg 13)) ;;
         .assign 12 (.load (.bin .add (.reg 5) (.reg 21))) ;;
         .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.reg 7))
           (.cond (.reg 18)
              (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
                (.assign 20 (.const 0)) (.assign 20 (.const 1)))
              (.assign 20 (.const 0)) ;;
            .loop (.reg 20)
              (.assign 15 (.load (.reg 18)) ;;
               .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
               .assign 18 (.load (.bin .add (.reg 18) (.const 3))) ;;
               .cond (.reg 18)
                 (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
                   (.assign 20 (.const 0)) (.assign 20 (.const 1)))
                 (.assign 20 (.const 0))))
           (.assign 14 (.load (.bin .add (.reg 10)
              (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
            .assign 15 (.load (.bin .add (.reg 10)
              (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
            .store (.reg 17) (.reg 12) ;;
            .store (.bin .add (.reg 17) (.const 1)) (.reg 14) ;;
            .store (.bin .add (.reg 17) (.const 2)) (.reg 15) ;;
            .store (.bin .add (.reg 17) (.const 3)) (.reg 18) ;;
            .assign 18 (.reg 17) ;;
            .assign 17 (.bin .add (.reg 17) (.const 4)) ;;
            .store (.bin .add (.reg 6) (.reg 12)) (.reg 7))))
      (normalPost (Inv P.length))
      (fun _ => rangeCost stepCost 0 P.length + (P.length - 0) * ((Expr.reg 11).size + 8) +
        ((Expr.const 0).size + (Expr.reg 11).size + 5)) :=
    Triple.forRange_le (P := P0) (Inv := Inv) stepCost 0 P.length (Nat.zero_le _) hw1
      (fun _ => by omega)
      (fun st ⟨hm, hr, hr17, hr18⟩ => by
        refine ⟨Expr.eval_const (by omega), nodeBase, by simp,
          by simp [hr17], le_rfl,
          by simp, fun r hrr => by
            dsimp only; rw [Function.update_of_ne (by omega : r ≠ 13)]; exact hr r hrr,
          ?_, ?_, ?_, ?_, ?_, fun _ _ _ => hm ▸ rfl⟩
        · simpa [hvEnd_eq] using hvEnd_V
        · simp [hvEnd_eq, shortcutWalk]; exact .nil vEnd
        · simp [hvEnd_eq, shortcutWalk, MGraph.walkVertices]
        · simp [hvEnd_eq, shortcutWalk, StackListIn, hr18]
        · simpa [hvEnd_eq, shortcutWalk, MGraph.walkVertices, hm] using hvEnd_stamp)
      (fun _ _ _ _ ⟨_, hr13, _⟩ => hr13)
      (fun _ _ _ _ ⟨_, _, _, _, _, hr, _⟩ => by simp [Expr.eval, hr 11 (Or.inl (by omega)), hr11])
      (fun j _ hj => by
        intro st ω ⟨nodePtr, hr13, hr17, hnp_lo, hnp_hi, hr_eq, hcur_V, hWalk_cur, hNd_cur,
          hSt_cur, hV_cur, hfr⟩
        have hstep_walk := shortcutWalk_drop_step (G := G) (u := u) (P := P) hj
        set i := P.length - 1 - j
        have hi : i < P.length := by omega
        set cur := vertAt G u P (P.length - j)
        set Q := shortcutWalk G cur (P.drop (P.length - j))
        set target := vertAt G u P i
        have htarget_V : target ∈ G.V := vertAt_mem_V hG_val hu hWalk i (Nat.le_of_lt hi)
        have htarget_lt : target < vCap := hvG target htarget_V
        have hperm_lt : permPtr + i < nodeBase := by omega
        have hst_target : st.mem (permPtr + i) = target := by
          rw [hfr (permPtr + i) (fun v hv => by have := hvst_perm v hv; omega) (Or.inl hperm_lt)]
          exact hVarr i (Nat.le_of_lt hi)
        have hr5_st : st.regs 5 = permPtr := (hr_eq 5 (Or.inl (by omega))).trans hr5
        have hr6_st : st.regs 6 = vStampPtr := (hr_eq 6 (Or.inl (by omega))).trans hr6
        have hr7_st : st.regs 7 = stampVal := (hr_eq 7 (Or.inl (by omega))).trans hr7
        have hr10_st : st.regs 10 = wPtr := (hr_eq 10 (Or.inl (by omega))).trans hr10
        have hr11_st : st.regs 11 = P.length := (hr_eq 11 (Or.inl (by omega))).trans hr11
        have hnode_w : nodePtr < 2 ^ w := by omega
        have hk_w : P.length < 2 ^ w := by omega
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := i)
          (by simp [Expr.eval, BinOp.eval, hr11_st, hr13, show 1 < 2 ^ w by omega,
            show P.length - 1 < 2 ^ w by omega, show P.length - 1 - j < 2 ^ w by omega, i]) ?_
        refine runs_seq_assign_le (v := target)
          (Expr.eval_load_of_eq (x := permPtr + i) (by
            simp [Expr.eval, BinOp.eval, hr5_st,
              show permPtr + i < 2 ^ w by omega]) (by simpa using hst_target)) ?_
        let stB : State :=
          { st with regs := Function.update (Function.update st.regs 21 i) 12 target }
        have hr6_B : stB.regs 6 = vStampPtr := by
          simp [stB, hr6_st]
        have hr7_B : stB.regs 7 = stampVal := by
          simp [stB, hr7_st]
        have hr10_B : stB.regs 10 = wPtr := by
          simp [stB, hr10_st]
        have hr12_B : stB.regs 12 = target := by simp [stB]
        have hr17_B : stB.regs 17 = nodePtr := by
          simp [stB, hr17]
        have hr21_B : stB.regs 21 = i := by simp [stB]
        have hvsp_t_lt : vStampPtr + target < 2 ^ w := by omega
        have hstep_sub : P.length - (j + 1) = i := by omega
        have hcur_eq_dst : G.dst (P[i]'hi) = cur := by
          have := vertAt_succ G u hi
          rw [show i + 1 = P.length - j by omega] at this
          exact this.symm
        by_cases hmem : target ∈ G.walkVertices cur Q
        · have hvst_t : stB.mem (vStampPtr + target) = stampVal :=
            (hV_cur target htarget_lt).1 hmem
          have hcond_ev : (Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.reg 7)).eval w stB =
              some 1 :=
            Expr.eval_eq_true
              (Expr.eval_load_of_eq
                (by simp [Expr.eval, BinOp.eval, hr6_B, hr12_B, hvsp_t_lt]) hvst_t)
              (Expr.eval_reg_of_eq hr7_B) rfl hw1
          obtain ⟨oP, stP, cP, hrunP, hqP, hcP⟩ :=
            shortcut_popLoop_triple (p := p) hw16 hnode1 hvst_disj hvst_w hnode_w
              hG_val hvG hcur_V hWalk_cur hNd_cur hmem st.mem stB.regs hr6_B hr12_B
              (by simpa [stB] using hSt_cur) hV_cur stB ω ⟨rfl, rfl⟩
          cases oP with
          | returned u => exact False.elim hqP
          | normal =>
            rcases hqP with ⟨hSt_P, hW_P, hNd_P, hV_P, hr_P, hm_P⟩
            have hQ'_eq : suffixFrom G target cur Q =
                shortcutWalk G (vertAt G u P (P.length - (j + 1))) (P.drop (P.length - (j + 1))) := by
              rw [hstep_walk]
              unfold shortcutStep
              rw [show G.dst (P[P.length - 1 - j]'hi) = cur from hcur_eq_dst]
              change suffixFrom G target cur Q =
                if target ∈ G.walkVertices cur Q then suffixFrom G target cur Q else P[i]'hi :: Q
              exact (ite_eq_left_iff.mpr fun h => absurd hmem h).symm
            have hvert_eq : vertAt G u P (P.length - (j + 1)) = target := by rw [hstep_sub]
            have hlen_sub : (popPrefix G target cur Q).length ≤ qLen j + 1 - qLen (j + 1) := by
              have h1 := popPrefix_length_add_suffixFrom G target cur Q
              have h2 : qLen (j + 1) = (suffixFrom G target cur Q).length := by
                dsimp [qLen]; rw [hQ'_eq]
              have h3 : qLen j = Q.length := rfl
              omega
            have hcond_runs : Runs w p ω
                (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.reg 7))
                  popStmt pushStmt)
                stB .normal stP (6 + cP + 1) :=
              runs_cond_iff.mpr ⟨1, cP, hcond_ev, by simpa [popStmt] using hrunP, by simp [Expr.size]⟩
            refine ⟨.normal, stP, 6 + cP + 1, hcond_runs, ?_, ?_⟩
            · refine ⟨⟨nodePtr,
                by simp,
                by simp [(hr_P 17 (Or.inr (Or.inr (Or.inl rfl)))).trans hr17_B],
                hnp_lo, le_trans hnp_hi (by omega),
                fun r hrr => ?_,
                by simpa [hvert_eq] using htarget_V,
                by rw [← hQ'_eq, hvert_eq]; exact hW_P,
                by rw [← hQ'_eq, hvert_eq]; exact hNd_P,
                by rw [← hQ'_eq, hvert_eq]
                   simpa using hSt_P,
                by rw [← hQ'_eq, hvert_eq]; exact hV_P,
                fun addr hv_ne ha_rng => (hm_P addr hv_ne).trans (hfr addr hv_ne (by omega))⟩,
                (hr_P 13 (Or.inl (by omega))).trans (by simp [stB, hr13])⟩
              rcases hrr with hr11 | rfl | rfl
              · simp [stB, hr_P r (Or.inl (by omega)),
                  Function.update_of_ne (by omega : r ≠ 13),
                  Function.update_of_ne (by omega : r ≠ 12),
                  Function.update_of_ne (by omega : r ≠ 21), hr_eq r (Or.inl hr11)]
              · simp [stB, hr_P 16 (Or.inr (Or.inl rfl)), hr_eq 16 (Or.inr (Or.inl rfl))]
              · simp [stB, hr_P 19 (Or.inr (Or.inr (Or.inr rfl))),
                  hr_eq 19 (Or.inr (Or.inr rfl))]
            · dsimp only [Expr.size, stepCost] at hcP ⊢
              omega
        · have hvst_t : stB.mem (vStampPtr + target) ≤ gen0 := (hV_cur target htarget_lt).2 hmem
          have hvst_ne : stB.mem (vStampPtr + target) ≠ stampVal := by omega
          have hcond_ev : (Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.reg 7)).eval w stB =
              some 0 :=
            Expr.eval_eq_false
              (Expr.eval_load_of_eq
                (by simp [Expr.eval, BinOp.eval, hr6_B, hr12_B, hvsp_t_lt]) rfl)
              (Expr.eval_reg_of_eq hr7_B) hvst_ne hw1
          have ⟨he_mem, hsrc_i⟩ := isWalk_getElem_src hWalk i hi
          have hMW_B : MWalkAt stB.mem wPtr P := hMWalk.of_agree fun a ha1 ha2 => by
            have hd := hW_disj a ha1 ha2
            exact hfr a hd.1 (hd.2.imp id (fun h => le_trans hnp_hi (le_trans (by omega) h)))
          obtain ⟨oU, stU, cU, hrunU, hqU, hcU⟩ :=
            shortcut_pushNode_triple (p := p) hi hw16 hvst_disj hnp_lo (by omega) hwPtr_lt
              hvsp_t_lt htarget_lt hcur_eq_dst stB hr6_B hr7_B hr10_B hr12_B hr17_B hr21_B
              (he_w _ (List.getElem_mem hi)) hMW_B hSt_cur hV_cur stB ω rfl
          cases oU with
          | returned u => exact False.elim hqU
          | normal =>
            rcases hqU with ⟨hr13_U, hr17_U, hr18_U, hr_U, hSt_U, hV_U, hm_U⟩
            have hQ'_eq : (P[i]'hi) :: Q =
                shortcutWalk G (vertAt G u P (P.length - (j + 1))) (P.drop (P.length - (j + 1))) := by
              rw [hstep_walk]
              unfold shortcutStep
              rw [show G.dst (P[P.length - 1 - j]'hi) = cur from hcur_eq_dst]
              change P[i]'hi :: Q =
                if target ∈ G.walkVertices cur Q then suffixFrom G target cur Q else P[i]'hi :: Q
              exact (ite_eq_right_iff.mpr fun h => absurd h hmem).symm
            have hvert_eq : vertAt G u P (P.length - (j + 1)) = target := by rw [hstep_sub]
            have hcond_runs : Runs w p ω
                (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.reg 7))
                  popStmt pushStmt)
                stB .normal stU (6 + cU + 1) :=
              runs_cond_iff.mpr ⟨0, cU, hcond_ev, by simpa [pushStmt] using hrunU, by simp [Expr.size]⟩
            refine ⟨.normal, stU, 6 + cU + 1, hcond_runs, ?_, ?_⟩
            · refine ⟨⟨nodePtr + 4,
                by simp,
                by simp [hr17_U],
                by omega, by omega,
                fun r hrr => ?_,
                by simpa [hvert_eq] using htarget_V,
                by rw [← hQ'_eq, hvert_eq]
                   exact (.cons he_mem (by simpa [target] using hsrc_i)
                     (hcur_eq_dst ▸ hWalk_cur)),
                by rw [← hQ'_eq, hvert_eq]
                   change (target :: G.walkVertices (G.dst (P[i]'hi)) Q).Nodup
                   rw [hcur_eq_dst]
                   exact List.nodup_cons.mpr ⟨hmem, hNd_cur⟩,
                by rw [← hQ'_eq, hvert_eq]
                   simpa [Function.update_of_ne (by omega : (18 : ℕ) ≠ 13), hr18_U] using hSt_U,
                by rw [← hQ'_eq, hvert_eq]; exact hV_U,
                fun addr hv_ne ha_rng =>
                  (hm_U addr hv_ne (by rcases ha_rng with h | h <;> omega)).trans
                    (hfr addr hv_ne (by rcases ha_rng with h | h <;> omega))⟩,
                by rw [hr13_U]; simp [stB, hr13]⟩
              rcases hrr with hr11 | rfl | rfl
              · simp [stB, hr_U r (Or.inl hr11),
                  Function.update_of_ne (by omega : r ≠ 13),
                  Function.update_of_ne (by omega : r ≠ 12),
                  Function.update_of_ne (by omega : r ≠ 21), hr_eq r (Or.inl hr11)]
              · simp [stB, hr_U 16 (Or.inr (Or.inl rfl)), hr_eq 16 (Or.inr (Or.inl rfl))]
              · simp [stB, hr_U 19 (Or.inr (Or.inr rfl)), hr_eq 19 (Or.inr (Or.inr rfl))]
            · dsimp only [Expr.size, stepCost] at hcU ⊢
              omega)
  refine hloop.conseq (fun st ⟨hm, hr, hr17, hr18⟩ => ⟨hm, hr, hr17, hr18⟩)
    (fun o s' hq => hq) (fun _ _ => ?_)
  have hq0 : qLen 0 = 0 := by simp [qLen, shortcutWalk]
  have hq_le : ∀ j < P.length, qLen (j + 1) ≤ qLen j + 1 := fun j hj => by
    dsimp only [qLen]
    rw [shortcutWalk_drop_step hj]
    exact shortcutStep_len_le_succ _ _ _ _
  have hrc := rangeCost_shortcut_step 75 32 P.length hq_le
  rw [hq0, Nat.add_zero] at hrc
  dsimp only [Expr.size, stepCost] at hrc ⊢
  omega

end

end MinCostFlow.DynSpanner.Program
