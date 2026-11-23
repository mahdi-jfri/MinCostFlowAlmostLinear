module

public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalksDefs

import Mathlib.Tactic.Linarith

/-!
# Verification of `dsWriteIdEmbStmt` (`DynSpannerWriteIdEmb`)

Proves `dsWriteIdEmb_meetsContract` (`levelWalkProcs bOps bRev` at index `lwIdxWriteIdEmb = 0`),
materializing `idEmb` at heap `[heapPtr .. heapPtr + 3 * G.m)` in `O(G.m + 1)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

public theorem dsWriteIdEmb_meetsContract {w vCap eCap : ℕ} {G : MGraph}
    {p : Program} {bOps bRev bLW : ℕ}
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev)) :
    MeetsContract w p (bLW + lwIdxWriteIdEmb) (dsWriteIdEmbContract w vCap eCap G) := by
  refine meetsContract_of_runs
    (hpLW.get (i := lwIdxWriteIdEmb) (by simp [levelWalkProcs, lwIdxWriteIdEmb]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, mEmbPtr, heapPtr, rfl, hw16, hg_ltw, hm_ltw, hh_ltw,
    hdisjG, hdisjM, hG, heCap⟩
  obtain ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩ := hG.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hg_lt : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hm_lt : mEmbPtr < 2 ^ w := hargs mEmbPtr (by simp)
  have hh_lt : heapPtr < 2 ^ w := hargs heapPtr (by simp)
  have hvC : mem gPtr = vCap := hG.2.2.2.1
  have heC : mem (gPtr + dgECapOff) = eCap := hG.2.2.2.2.1
  have hmG : mem (gPtr + dgMOff) = G.m := hG.2.2.2.2.2.2.1
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h4_lt : (4 : ℕ) < 2 ^ w := by omega
  have h7_lt : (7 : ℕ) < 2 ^ w := by omega
  have hdg_lt : dynGraphSize vCap eCap < 2 ^ w := by omega
  have hvCap_ltw : vCap < 2 ^ w := by dsimp [dynGraphSize] at hg_ltw; omega
  have heCap_ltw : eCap < 2 ^ w := by dsimp [dynGraphSize] at hg_ltw; omega
  have hm_le_eCap : G.m ≤ eCap := by
    simpa [MGraph.m] using Finset.card_le_card
      (Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr (heCap x hx))
  refine runs_start_le ?_
  dsimp only [levelWalkProcs, lwIdxWriteIdEmb, List.getElem_cons_zero, dsWriteIdEmbStmt]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (x := gPtr) (by simp [Expr.eval, startState]) hvC) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (x := gPtr + dgECapOff)
      (by simp [Expr.eval, BinOp.eval, startState, dgECapOff, h1_lt,
        show gPtr + 1 < 2 ^ w by dsimp [dynGraphSize] at hg_ltw; omega]) heC) ?_
  refine runs_seq_assign_le (v := G.m)
    (Expr.eval_load_of_eq (x := gPtr + dgMOff)
      (by simp [Expr.eval, BinOp.eval, startState, dgMOff, h3_lt,
        show gPtr + 3 < 2 ^ w by dsimp [dynGraphSize] at hg_ltw; omega]) hmG) ?_
  refine runs_seq_assign_le (v := dgEListBase gPtr vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgEListBase,
          h4_lt, h7_lt, show 7 * vCap < 2 ^ w by dsimp [dynGraphSize] at hg_ltw; omega,
          show gPtr + 4 < 2 ^ w by dsimp [dynGraphSize] at hg_ltw; omega,
          show gPtr + 4 + 7 * vCap < 2 ^ w by dsimp [dynGraphSize] at hg_ltw; omega,
          show gPtr + 4 + 7 * vCap + eCap < 2 ^ w by dsimp [dynGraphSize] at hg_ltw; omega]) ?_
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 1 = mEmbPtr ∧ st.regs 2 = heapPtr + 3 * k ∧
    st.regs 5 = G.m ∧ st.regs 6 = dgEListBase gPtr vCap eCap ∧ st.regs 7 = k ∧
    (∀ j < k, ∃ hj : j < eL.length,
      heapPtr + 3 * j = st.mem (mEmbPtr + eL[j]) ∧
      MWalkAt st.mem (heapPtr + 3 * j) [(eL[j], true)]) ∧
    ∀ addr,
      (addr < mEmbPtr ∨ mEmbPtr + eCap ≤ addr) →
      (addr < heapPtr ∨ heapPtr + 3 * k ≤ addr) →
      st.mem addr = mem addr
  let P0 : State → Prop := fun st => Inv 0 { st with regs := Function.update st.regs 7 0 }
  have hLoop : Triple w p P0
      (WordRAM.forRange 7 (.const 0) (.reg 5)
        (.assign 8 (.load (.bin .add (.reg 6) (.reg 7))) ;;
         .store (.reg 2) (.const 1) ;;
         .store (.bin .add (.reg 2) (.const 1)) (.reg 8) ;;
         .store (.bin .add (.reg 2) (.const 2)) (.const 1) ;;
         .store (.bin .add (.reg 1) (.reg 8)) (.reg 2) ;;
         .assign 2 (.bin .add (.reg 2) (.const 3))))
      (normalPost (Inv G.m))
      (fun _ => (G.m - 0) * (45 + (.reg 5 : Expr).size + 8) +
        ((.const 0 : Expr).size + (.reg 5 : Expr).size + 5)) := by
    refine Triple.forRange_const (P := P0) (Inv := Inv) 45 0 G.m (Nat.zero_le _) h1_lt
      (fun _ => show G.m < 2 ^ w by omega)
      (fun st hP0 => ⟨by eval_expr, hP0⟩)
      (fun k st _ _ ⟨_, _, _, _, hr7, _⟩ => hr7)
      (fun k st _ _ ⟨_, _, hr5, _⟩ => by simp [Expr.eval, hr5])
      (fun k _ hk st ω ⟨hr1, hr2, hr5, hr6, hr7, hrec, hfr⟩ => by
        refine runs_start_le ?_
        have hk_eL : k < eL.length := by omega
        have hk_eCap : k < eCap := lt_of_lt_of_le hk hm_le_eCap
        let e := eL[k]'hk_eL
        have heE : e ∈ G.E := (heL_mem e).mp (List.getElem_mem hk_eL)
        have he_cap : e < eCap := heCap e heE
        have he_ltw : e < 2 ^ w := by omega
        have hk_ltw : k < 2 ^ w := by omega
        have hptr_k : dgEListBase gPtr vCap eCap + k < 2 ^ w := by
          simp [dgEListBase, dynGraphSize] at hg_ltw ⊢; omega
        have he_disj : (dgEListBase gPtr vCap eCap + k < mEmbPtr ∨
            mEmbPtr + eCap ≤ dgEListBase gPtr vCap eCap + k) ∧
            (dgEListBase gPtr vCap eCap + k < heapPtr ∨
            heapPtr + 3 * k ≤ dgEListBase gPtr vCap eCap + k) := by
          have hd := hdisjG (4 + 7 * vCap + eCap + k)
            (by dsimp [dynGraphSize]; omega)
          have haddr_eq : gPtr + (4 + 7 * vCap + eCap + k) = dgEListBase gPtr vCap eCap + k := by
            simp [dgEListBase]; omega
          rw [haddr_eq] at hd
          refine ⟨hd.1, ?_⟩
          rcases hd.2 with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]
        have hmem_e : st.mem (dgEListBase gPtr vCap eCap + k) = e :=
          (hfr _ he_disj.1 he_disj.2).trans (heL_at k hk_eL)
        have hh3_ltw : heapPtr + 3 * k + 2 < 2 ^ w := by omega
        have hme_ltw : mEmbPtr + e < 2 ^ w := by omega
        refine runs_seq_assign_le (v := e)
          (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr6, hr7, hptr_k]) hmem_e) ?_
        refine runs_seq_store_le (x := heapPtr + 3 * k) (v := 1)
          (by simp [Expr.eval, hr2]) (by eval_expr) ?_
        refine runs_seq_store_le (x := heapPtr + 3 * k + 1) (v := e)
          (by simp [Expr.eval, BinOp.eval, hr2, h1_lt, show heapPtr + 3 * k + 1 < 2 ^ w by omega])
          (by simp [Expr.eval]) ?_
        refine runs_seq_store_le (x := heapPtr + 3 * k + 2) (v := 1)
          (by simp [Expr.eval, BinOp.eval, hr2, h2_lt, hh3_ltw])
          (by eval_expr) ?_
        refine runs_seq_store_le (x := mEmbPtr + e) (v := heapPtr + 3 * k)
          (by simp [Expr.eval, BinOp.eval, hr1, hme_ltw])
          (by simp [Expr.eval, hr2]) ?_
        refine runs_assign_le (v := heapPtr + 3 * (k + 1))
          (by simp [Expr.eval, BinOp.eval, hr2, h3_lt, show heapPtr + 3 * k + 3 < 2 ^ w by omega]; omega)
          ?_ (by dsimp only [Expr.size]; omega)
        have hne_me : mEmbPtr + e ≠ heapPtr + 3 * k := by omega
        have hne_me1 : mEmbPtr + e ≠ heapPtr + 3 * k + 1 := by omega
        have hne_me2 : mEmbPtr + e ≠ heapPtr + 3 * k + 2 := by omega
        refine ⟨⟨by simp [hr1], by simp, by simp [hr5], by simp [hr6], by simp, ?_, ?_⟩,
          by simp [hr7]⟩
        · intro j hj
          dsimp only
          by_cases hjk : j = k
          · subst hjk
            refine ⟨hk_eL, ?_, ?_⟩
            · dsimp only [e]; rw [Function.update_self]
            · intro q hq
              have hq3 : q < 3 := by simp [mWalkEncode] at hq; omega
              dsimp only [e] at hne_me hne_me1 hne_me2 ⊢
              rcases q with _ | _ | _ | q'
              · simp only [Nat.add_zero]
                rw [Function.update_of_ne hne_me.symm, Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_self]; rfl
              · rw [Function.update_of_ne hne_me1.symm, Function.update_of_ne (by omega),
                  Function.update_self]; rfl
              · rw [Function.update_of_ne hne_me2.symm, Function.update_self]; rfl
              · omega
          · obtain ⟨hj_lt, hptr_j, hwalk_j⟩ := hrec j (by omega)
            have hne_ej : eL[j] ≠ e := fun heq => hjk (Fin.ext_iff.mp
              (List.nodup_iff_injective_getElem.mp heL_nd (a₁ := ⟨j, hj_lt⟩) (a₂ := ⟨k, hk_eL⟩) heq))
            have he_j_cap : eL[j] < eCap := heCap _ ((heL_mem _).mp (List.getElem_mem hj_lt))
            refine ⟨hj_lt, ?_, ?_⟩
            · dsimp only [e] at hne_ej he_cap ⊢
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hptr_j
            · refine hwalk_j.of_agree fun addr ha1 ha2 => ?_
              have ha_lt_3k : addr < heapPtr + 3 * k := by
                dsimp only [List.length] at ha2; omega
              dsimp only [e] at he_cap ⊢
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        · intro addr hm_d hh_d
          dsimp only
          dsimp only [e] at he_cap ⊢
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr addr hm_d (by rcases hh_d with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
  refine runs_seq_triple_le hLoop ⟨by simp [startState], by simp [startState], by simp, by simp,
    by simp, fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl⟩ ?_
  intro stF ⟨_, hr2, _, _, _, hrec, hfr⟩
  refine runs_ret_le (by simp [Expr.eval, hr2])
    ⟨gPtr, mEmbPtr, heapPtr, rfl, rfl, ?_, ?_, hfr⟩ ?_
  · intro e he
    have he_mem : e ∈ eL := (heL_mem e).mpr he
    obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem he_mem
    obtain ⟨hj_lt', hptr, hwalk⟩ := hrec j (by omega)
    refine ⟨heCap _ he, ?_⟩
    rw [← hptr]
    simpa [idEmb] using hwalk
  · intro e he
    have he_mem : e ∈ eL := (heL_mem e).mpr he
    obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem he_mem
    obtain ⟨hj_lt', hptr, _⟩ := hrec j (by omega)
    rw [← hptr]
    omega
  · dsimp only [dsWriteIdEmbContract, Expr.size]; omega

end

end MinCostFlow.DynSpanner.Program
