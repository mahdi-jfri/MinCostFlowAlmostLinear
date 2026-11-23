module

public import MinCostFlow.DynSpanner.Program.GraphTranslate

import Mathlib.Data.List.TakeDrop

/-!
# Walk Flattening Procedures for Graph Translation (`GraphTranslateCollect`)

Verifies `gtCollectRawEs_meetsContract` (`gtIdxCollectRawEs = 3`) and
`gtCollectRawVs_meetsContract` (`gtIdxCollectRawVs = 4`) from `gtProcs bSort bOps`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

theorem gtCollectRawEs_meetsContract {w eCap : ℕ} {p : Program} {b bSort bOps : ℕ}
    {J : MGraph} {jEs : List ℕ} {emb : MinCostFlow.Embedding}
    (hp : p.HasAt b (gtProcs bSort bOps)) :
    MeetsContract w p (b + gtIdxCollectRawEs) (gtCollectRawEsContract w eCap J jEs emb) := by
  refine meetsContract_of_runs (hp.get (i := gtIdxCollectRawEs) (by simp [gtProcs, gtIdxCollectRawEs]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨jEsPtr, mEmbPtr, rawEsPtr, rfl, hw16, hjB, hmB, hrawB, hdisjJ, hdisjM,
    hdisjW, hjE, hmEmb, hjAt, hembw, hwLenB⟩
  have hlt_mJ : jEs.length < 2 ^ w := hargs jEs.length (by simp)
  have hlt_jP : jEsPtr < 2 ^ w := hargs jEsPtr (by simp)
  have hlt_mP : mEmbPtr < 2 ^ w := hargs mEmbPtr (by simp)
  have hlt_rP : rawEsPtr < 2 ^ w := hargs rawEsPtr (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  let prefEs : ℕ → List ℕ := fun j => collectRawEsFun (jEs.take j) emb
  have hpref_len : ∀ j, (prefEs j).length ≤ (collectRawEsFun jEs emb).length := fun j => by
    dsimp only [prefEs, collectRawEsFun]
    conv_rhs => rw [← List.take_append_drop j jEs, List.flatMap_append, List.length_append]
    exact Nat.le_add_right _ _
  have hpref_succ : ∀ j (hj : j < jEs.length),
      prefEs (j + 1) = prefEs j ++ (emb jEs[j]).map Prod.fst := fun j hj => by
    dsimp only [prefEs, collectRawEsFun]
    rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
    simp
  refine runs_start_le ?_
  dsimp only [gtProcs, gtIdxCollectRawEs, List.getElem_cons_succ, List.getElem_cons_zero,
    gtCollectRawEsStmt]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  let outerBody : Stmt :=
    .assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
    .assign 7 (.load (.bin .add (.reg 2) (.reg 6))) ;;
    .assign 8 (.load (.reg 7)) ;;
    forRange 9 (.const 0) (.reg 8)
      (.assign 10 (.load (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 9))))) ;;
       .store (.bin .add (.reg 3) (.reg 4)) (.reg 10) ;;
       .assign 4 (.bin .add (.reg 4) (.const 1)))
  let InvO : ℕ → State → Prop := fun j st =>
    st.regs 0 = jEs.length ∧ st.regs 1 = jEsPtr ∧ st.regs 2 = mEmbPtr ∧ st.regs 3 = rawEsPtr ∧
    st.regs 4 = (prefEs j).length ∧ st.regs 5 = j ∧
    ListAt st.mem rawEsPtr (prefEs j) ∧
    ∀ addr, addr < rawEsPtr ∨ rawEsPtr + (prefEs j).length ≤ addr → st.mem addr = mem addr
  let stepCost : ℕ → ℕ := fun j => 35 * (emb (jEs.getD j 0)).length + 25
  have houter : Triple w p (InvO 0) (forRange 5 (.const 0) (.reg 0) outerBody) (normalPost (InvO jEs.length))
      (fun _ => rangeCost stepCost 0 jEs.length + jEs.length * (Expr.size (.reg 0) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 0) + 5)) := by
    refine Triple.forRange_le stepCost 0 jEs.length (Nat.zero_le _) h1_lt (fun _ => hlt_mJ)
      (fun st hInv => ⟨by simp [Expr.eval, h0_lt], by
        rcases hInv with ⟨h0, h1, h2, h3, h4, _, hat, hfr⟩
        refine ⟨h0, h1, h2, h3, ?_, by simp, ?_, ?_⟩
        · simp [prefEs, collectRawEsFun, h4]
        · simp [prefEs, collectRawEsFun]
        · simpa [prefEs, collectRawEsFun] using hfr⟩)
      (fun j st _ _ hInv => hInv.2.2.2.2.2.1)
      (fun j st _ _ hInv => by simp [Expr.eval, hInv.1]) ?_
    intro j _ hj_lt st ω' ⟨hr0, hr1, hr2, hr3, hr4, hr5, hat, hfr⟩
    have hpref_j_le := hpref_len j
    have he_mem : jEs[j] ∈ J.E := (hjE _).mp (List.getElem_mem hj_lt)
    have hlt_e : jEs[j] < 2 ^ w := by have := (hmEmb _ he_mem).1; omega
    have hj_addr_lt : jEsPtr + j < 2 ^ w := by omega
    have hj_ltw : j < 2 ^ w := by omega
    have hje_val : st.mem (jEsPtr + j) = jEs[j] := by
      rw [hfr _ (by rcases hdisjJ j hj_lt with h | h <;> [left; right] <;> omega)]
      exact hjAt j hj_lt
    have hm_addr_lt : mEmbPtr + jEs[j] < 2 ^ w := by have := (hmEmb _ he_mem).1; omega
    let wPtr := mem (mEmbPtr + jEs[j])
    have hwPtr_mem : st.mem (mEmbPtr + jEs[j]) = wPtr :=
      hfr _ (by rcases hdisjM _ he_mem with h | h <;> [left; right] <;> omega)
    have hwB_e := hwLenB _ he_mem
    have hwPtr_lt : wPtr < 2 ^ w := by omega
    have hwLen_lt : (emb jEs[j]).length < 2 ^ w := hwB_e.1
    have hwAt : MWalkAt st.mem wPtr (emb jEs[j]) := by
      have hw0 := (hmEmb _ he_mem).2
      intro k hk
      rw [hfr (wPtr + k) (by rcases hdisjW _ he_mem k hk with h | h <;> [left; right] <;> omega)]
      exact hw0 k hk
    have hwLen_mem : st.mem wPtr = (emb jEs[j]).length := MWalkAt_head hwAt
    let wSteps := (emb jEs[j]).map Prod.fst
    let innerBody : Stmt :=
      .assign 10 (.load (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 9))))) ;;
      .store (.bin .add (.reg 3) (.reg 4)) (.reg 10) ;;
      .assign 4 (.bin .add (.reg 4) (.const 1))
    let InvI : ℕ → State → Prop := fun t stI =>
      stI.regs 0 = jEs.length ∧ stI.regs 1 = jEsPtr ∧ stI.regs 2 = mEmbPtr ∧
      stI.regs 3 = rawEsPtr ∧
      stI.regs 4 = (prefEs j).length + t ∧ stI.regs 5 = j ∧
      stI.regs 6 = jEs[j] ∧ stI.regs 7 = wPtr ∧ stI.regs 8 = (emb jEs[j]).length ∧
      stI.regs 9 = t ∧
      ListAt stI.mem rawEsPtr (prefEs j ++ wSteps.take t) ∧
      ∀ addr, addr < rawEsPtr ∨ rawEsPtr + ((prefEs j).length + t) ≤ addr → stI.mem addr = mem addr
    have hpref_j_add : (prefEs j).length + (emb jEs[j]).length ≤ (collectRawEsFun jEs emb).length := by
      have hle := hpref_len (j + 1)
      rw [hpref_succ j hj_lt, List.length_append, List.length_map] at hle
      exact hle
    let InvIPre : State → Prop := fun stI =>
      stI.regs 0 = jEs.length ∧ stI.regs 1 = jEsPtr ∧ stI.regs 2 = mEmbPtr ∧
      stI.regs 3 = rawEsPtr ∧
      stI.regs 4 = (prefEs j).length ∧ stI.regs 5 = j ∧
      stI.regs 6 = jEs[j] ∧ stI.regs 7 = wPtr ∧ stI.regs 8 = (emb jEs[j]).length ∧
      ListAt stI.mem rawEsPtr (prefEs j) ∧
      ∀ addr, addr < rawEsPtr ∨ rawEsPtr + (prefEs j).length ≤ addr → stI.mem addr = mem addr
    have hinner : Triple w p InvIPre (forRange 9 (.const 0) (.reg 8) innerBody)
        (normalPost (InvI (emb jEs[j]).length))
        (fun _ => (emb jEs[j]).length * (24 + Expr.size (.reg 8) + 8) +
          (Expr.size (.const 0) + Expr.size (.reg 8) + 5)) := by
      refine Triple.forRange_const 24 0 (emb jEs[j]).length (Nat.zero_le _) h1_lt (fun _ => hwLen_lt)
        (fun _ h => ⟨by simp [Expr.eval, h0_lt],
          ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
           by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2.1],
           by simp [h.2.2.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2.2.2.1], by simp,
           by simpa using h.2.2.2.2.2.2.2.2.2.1, by simpa using h.2.2.2.2.2.2.2.2.2.2⟩⟩)
        (fun t _ _ _ h => h.2.2.2.2.2.2.2.2.2.1)
        (fun t _ _ _ h => by simp [Expr.eval, h.2.2.2.2.2.2.2.2.1]) ?_
      intro t _ ht_lt stI ω'' ⟨hI0, hI1, hI2, hI3, hI4, hI5, hI6, hI7, hI8, hI9, hIat, hIfr⟩
      have hwEnc := mWalkEncode_length (emb jEs[j])
      have ht_ltw : t < 2 ^ w := by omega
      have h2t_lt : 2 * t < 2 ^ w := by omega
      have h12t_lt : 1 + 2 * t < 2 ^ w := by omega
      have hwp_lt : wPtr + (1 + 2 * t) < 2 ^ w := by omega
      have hk_enc : 1 + 2 * t < (mWalkEncode (emb jEs[j])).length := by omega
      have hwI : MWalkAt stI.mem wPtr (emb jEs[j]) := by
        have hw0 := (hmEmb _ he_mem).2
        intro k hk
        rw [hIfr _ (by rcases hdisjW _ he_mem k hk with h | h <;> [left; right] <;> omega)]
        exact hw0 k hk
      have heH_mem : stI.mem (wPtr + (1 + 2 * t)) = (emb jEs[j])[t].1 :=
        by simpa [Nat.add_assoc] using MWalkAt_step_edge hwI ht_lt
      have heH_lt : (emb jEs[j])[t].1 < 2 ^ w := hembw _ he_mem _ (List.getElem_mem ht_lt)
      have hdst_addr : rawEsPtr + ((prefEs j).length + t) < 2 ^ w := by omega
      have hlen_next_lt : (prefEs j).length + (t + 1) < 2 ^ w := by omega
      refine runs_start_le ?_
      dsimp only [innerBody]
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (v := (emb jEs[j])[t].1)
          (by simp [Expr.eval, BinOp.eval, hI7, hI9, h1_lt, h2_lt, h2t_lt, h12t_lt, hwp_lt])
          heH_mem) ?_
      refine runs_seq_store_le (x := rawEsPtr + ((prefEs j).length + t)) (v := (emb jEs[j])[t].1)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hI3, hI4, hdst_addr])
        (by eval_expr) ?_
      refine runs_assign_le (v := (prefEs j).length + (t + 1))
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hI4, h1_lt, hlen_next_lt,
          show (prefEs j).length + t + 1 = (prefEs j).length + (t + 1) by omega]) ?_
        (by dsimp only [Expr.size]; omega)
      refine ⟨⟨by simp [hI0], by simp [hI1], by simp [hI2], by simp [hI3],
        by simp, by simp [hI5], by simp [hI6], by simp [hI7], by simp [hI8], by simp,
        ?_, ?_⟩, by simp [hI9]⟩
      · have htake : wSteps.take (t + 1) = wSteps.take t ++ [(emb jEs[j])[t].1] := by
          have ht_w : t < wSteps.length := by simpa [wSteps] using ht_lt
          rw [List.take_succ_eq_append_getElem ht_w]
          simp [wSteps]
        rw [htake, ← List.append_assoc]
        refine listAt_append.mpr ⟨ListAt.update_ge hIat (by
          rw [List.length_append, List.length_take, Nat.min_eq_left (by simp [wSteps]; omega)]), fun u hu => ?_⟩
        simp only [List.length_cons, List.length_nil] at hu
        have hu0 : u = 0 := by omega
        subst hu0
        have hlen_w : (prefEs j ++ wSteps.take t).length = (prefEs j).length + t := by
          rw [List.length_append, List.length_take, Nat.min_eq_left (by simp [wSteps]; omega)]
        rw [hlen_w, ← Nat.add_assoc]
        simp
      · intro addr had
        have hne : addr ≠ rawEsPtr + ((prefEs j).length + t) := by omega
        dsimp only
        rw [Function.update_of_ne hne]
        exact hIfr addr (by omega)
    refine runs_start_le ?_
    dsimp only [outerBody]
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := jEs[j])
        (by simp [Expr.eval, BinOp.eval, hr1, hr5, hj_addr_lt]) hje_val) ?_
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := wPtr)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hm_addr_lt]) hwPtr_mem) ?_
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := (emb jEs[j]).length)
        (by simp [Expr.eval]) hwLen_mem) ?_
    refine runs_triple_le hinner
      ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
       by simp [hr5], by simp, by simp, by simp, by simpa using hat, by simpa using hfr⟩
      (fun o stI hq => by
        cases o with
        | returned u => exact False.elim hq
        | normal =>
          rcases hq with ⟨hI0, hI1, hI2, hI3, hI4, hI5, _, _, _, _, hIat, hIfr⟩
          have htake_all : wSteps.take (emb jEs[j]).length = wSteps :=
            List.take_of_length_le (by simp [wSteps])
          refine ⟨⟨by simp [hI0], by simp [hI1], by simp [hI2], by simp [hI3], ?_, by simp,
            by simpa [hpref_succ j hj_lt, wSteps, htake_all] using hIat, ?_⟩, hI5⟩
          · rw [hpref_succ j hj_lt, List.length_append, List.length_map]; exact hI4
          · intro addr had
            rw [hpref_succ j hj_lt, List.length_append, List.length_map] at had
            exact hIfr addr had)
      (by dsimp only [stepCost, Expr.size]; rw [List.getD_eq_getElem _ _ hj_lt]; omega)
  refine runs_seq_triple_le houter
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [prefEs, collectRawEsFun, startState], by simp [startState],
     listAt_nil _ _, fun _ _ => rfl⟩ ?_
  intro st' ⟨_, _, _, _, hr4, _, hat', hfr'⟩
  have htake_all : prefEs jEs.length = collectRawEsFun jEs emb := by simp [prefEs]
  rw [htake_all] at hr4 hat' hfr'
  refine runs_ret_le (by eval_expr) ⟨jEsPtr, mEmbPtr, rawEsPtr, rfl, hr4, hat', hfr'⟩ ?_
  dsimp only [gtCollectRawEsContract, Expr.size]
  have hrc : rangeCost stepCost 0 jEs.length =
      35 * (collectRawEsFun jEs emb).length + 25 * jEs.length := by
    have hsum : rangeCost stepCost 0 jEs.length =
        rangeCost (fun j => 35 * (emb (jEs.getD j 0)).length) 0 jEs.length +
        rangeCost (fun _ => 25) 0 jEs.length := rangeCost_add _ _ _ _
    rw [hsum, rangeCost_const, Nat.sub_zero]
    have h1 : rangeCost (fun j => 35 * (emb (jEs.getD j 0)).length) 0 jEs.length =
        35 * (collectRawEsFun jEs emb).length := by
      have haux : ∀ k, k ≤ jEs.length →
          rangeCost (fun j => 35 * (emb (jEs.getD j 0)).length) 0 k =
            35 * (collectRawEsFun (jEs.take k) emb).length := by
        intro k hk
        induction k with
        | zero => simp [collectRawEsFun]
        | succ k ih =>
          have hstep : rangeCost (fun j => 35 * (emb (jEs.getD j 0)).length) 0 (k + 1) =
              rangeCost (fun j => 35 * (emb (jEs.getD j 0)).length) 0 k +
              35 * (emb (jEs.getD k 0)).length := by
            simp only [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.map_cons,
              List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
          rw [hstep, ih (by omega)]
          dsimp only [prefEs] at hpref_succ
          rw [hpref_succ k (by omega), List.length_append, List.length_map,
            List.getD_eq_getElem _ _ (by omega : k < jEs.length)]
          omega
      simpa using haux jEs.length (le_refl _)
    rw [h1]; omega
  rw [hrc]
  omega

theorem gtCollectRawVs_meetsContract {w vCap eCap : ℕ} {p : Program} {b bSort bOps : ℕ}
    {H' J : MGraph} {jEs jTails : List ℕ} {emb : MinCostFlow.Embedding}
    (hp : p.HasAt b (gtProcs bSort bOps)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + gtIdxCollectRawVs)
      (gtCollectRawVsContract w vCap eCap H' J jEs jTails emb) := by
  refine meetsContract_of_runs (hp.get (i := gtIdxCollectRawVs) (by simp [gtProcs, gtIdxCollectRawVs]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨hPtr, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr, rfl, hw16, hhB, hjB, hjtB, hmB,
    hrawB, hdisjH, hdisjJ, hdisjT, hdisjM, hdisjW, hDynH, hLenT, hjE, htailEq, hmEmb, hjAt, htAt,
    hembH, hHVw, hwLenB⟩
  have hlt_hP : hPtr < 2 ^ w := hargs hPtr (by simp)
  have hlt_mJ : jEs.length < 2 ^ w := hargs jEs.length (by simp)
  have hlt_jP : jEsPtr < 2 ^ w := hargs jEsPtr (by simp)
  have hlt_tP : jTailsPtr < 2 ^ w := hargs jTailsPtr (by simp)
  have hlt_mP : mEmbPtr < 2 ^ w := hargs mEmbPtr (by simp)
  have hlt_rP : rawVsPtr < 2 ^ w := hargs rawVsPtr (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  let stepVs : ℕ → List ℕ := fun j => H'.walkVertices (jTails.getD j 0) (emb (jEs.getD j 0))
  let prefVs : ℕ → List ℕ := fun j => (List.range j).flatMap stepVs
  have hpref_all : prefVs jEs.length = collectRawVsFun H' jEs jTails emb := rfl
  have hpref_len : ∀ j ≤ jEs.length, (prefVs j).length ≤ (collectRawVsFun H' jEs jTails emb).length := by
    intro j hj
    dsimp only [prefVs, collectRawVsFun]
    rw [show jEs.length = j + (jEs.length - j) by omega, List.range_add, List.flatMap_append,
      List.length_append]
    exact Nat.le_add_right _ _
  have hpref_succ : ∀ j, prefVs (j + 1) = prefVs j ++ stepVs j := fun j => by
    dsimp only [prefVs]
    rw [List.range_succ, List.flatMap_append]
    simp
  refine runs_start_le ?_
  dsimp only [gtProcs, gtIdxCollectRawVs, List.getElem_cons_succ, List.getElem_cons_zero,
    gtCollectRawVsStmt]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  let outerBody : Stmt :=
    .assign 8 (.load (.bin .add (.reg 3) (.reg 7))) ;;
    .store (.bin .add (.reg 5) (.reg 6)) (.reg 8) ;;
    .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
    .assign 8 (.load (.bin .add (.reg 2) (.reg 7))) ;;
    .assign 9 (.load (.bin .add (.reg 4) (.reg 8))) ;;
    .assign 10 (.load (.reg 9)) ;;
    forRange 11 (.const 0) (.reg 10)
      (.assign 12 (.load (.bin .add (.reg 9) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 11))))) ;;
       .assign 13 (.load (.bin .add (.reg 9) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 11))))) ;;
       .cond (.bin .eq (.reg 13) (.const 1))
         (.call 14 (bOps + dgIdxGetHead) [.reg 0, .reg 12])
         (.call 14 (bOps + dgIdxGetTail) [.reg 0, .reg 12]) ;;
       .store (.bin .add (.reg 5) (.reg 6)) (.reg 14) ;;
       .assign 6 (.bin .add (.reg 6) (.const 1)))
  let InvO : ℕ → State → Prop := fun j st =>
    st.regs 0 = hPtr ∧ st.regs 1 = jEs.length ∧ st.regs 2 = jEsPtr ∧
    st.regs 3 = jTailsPtr ∧ st.regs 4 = mEmbPtr ∧ st.regs 5 = rawVsPtr ∧
    st.regs 6 = (prefVs j).length ∧ st.regs 7 = j ∧
    ListAt st.mem rawVsPtr (prefVs j) ∧
    ∀ addr, addr < rawVsPtr ∨ rawVsPtr + (prefVs j).length ≤ addr → st.mem addr = mem addr
  let stepCost : ℕ → ℕ := fun j => 115 * (emb (jEs.getD j 0)).length + 100
  have houter : Triple w p (InvO 0) (forRange 7 (.const 0) (.reg 1) outerBody) (normalPost (InvO jEs.length))
      (fun _ => rangeCost stepCost 0 jEs.length + jEs.length * (Expr.size (.reg 1) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 1) + 5)) := by
    refine Triple.forRange_le stepCost 0 jEs.length (Nat.zero_le _) h1_lt (fun _ => hlt_mJ)
      (fun st hInv => ⟨by simp [Expr.eval, h0_lt], by
        rcases hInv with ⟨h0, h1, h2, h3, h4, h5, h6, _, hat, hfr⟩
        refine ⟨h0, h1, h2, h3, h4, h5, ?_, by simp, ?_, ?_⟩
        · simp [prefVs, h6]
        · simp [prefVs]
        · simpa [prefVs] using hfr⟩)
      (fun j st _ _ hInv => hInv.2.2.2.2.2.2.2.1)
      (fun j st _ _ hInv => by simp [Expr.eval, hInv.2.1]) ?_
    intro j _ hj_lt st ω' ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hat, hfr⟩
    have hpref_j_le := hpref_len j (le_of_lt hj_lt)
    have hj_tlen : j < jTails.length := by omega
    have hj_ltw : j < 2 ^ w := by omega
    have hjt_addr_lt : jTailsPtr + j < 2 ^ w := by omega
    have hjt_val : st.mem (jTailsPtr + j) = jTails[j] := by
      rw [hfr _ (by rcases hdisjT j hj_lt with h | h <;> [left; right] <;> omega)]
      exact htAt j hj_tlen
    have hjt_gd : jTails[j] = J.tail jEs[j] := by
      have hget := (htailEq j hj_lt).1
      rw [List.getD_eq_getElem _ _ hj_tlen] at hget
      exact hget
    have hjt_ltw : jTails[j] < 2 ^ w := hjt_gd ▸ (htailEq j hj_lt).2
    have hdst_j0 : rawVsPtr + (prefVs j).length < 2 ^ w := by
      have := hpref_len (j + 1) hj_lt
      rw [hpref_succ, List.length_append] at this
      have hspos : 1 ≤ (stepVs j).length := by simp [stepVs, MGraph.walkVertices]
      omega
    have hpref1_ltw : (prefVs j).length + 1 < 2 ^ w := by
      have := hpref_len (j + 1) hj_lt
      rw [hpref_succ, List.length_append] at this
      have hspos : 1 ≤ (stepVs j).length := by simp [stepVs, MGraph.walkVertices]
      omega
    have he_mem : jEs[j] ∈ J.E := (hjE _).mp (List.getElem_mem hj_lt)
    have hlt_e : jEs[j] < 2 ^ w := by have := (hmEmb _ he_mem).1; omega
    have hje_addr_lt : jEsPtr + j < 2 ^ w := by omega
    have hm_addr_lt : mEmbPtr + jEs[j] < 2 ^ w := by have := (hmEmb _ he_mem).1; omega
    let wPtr := mem (mEmbPtr + jEs[j])
    have hwB_e := hwLenB _ he_mem
    have hwPtr_lt : wPtr < 2 ^ w := by omega
    have hwLen_lt : (emb jEs[j]).length < 2 ^ w := hwB_e.1
    have hpref_j_add : (prefVs j).length + 1 + (emb jEs[j]).length ≤
        (collectRawVsFun H' jEs jTails emb).length := by
      have := hpref_len (j + 1) hj_lt
      rw [hpref_succ, List.length_append] at this
      simp only [stepVs, MGraph.walkVertices, List.length_cons, List.length_map,
        List.getD_eq_getElem _ _ hj_lt] at this
      omega
    let memM : ℕ → ℕ := Function.update st.mem (rawVsPtr + (prefVs j).length) jTails[j]
    have hfr_M : ∀ addr, addr < rawVsPtr ∨ rawVsPtr + ((prefVs j).length + 1) ≤ addr →
        memM addr = mem addr := fun addr had => by
      have hne : addr ≠ rawVsPtr + (prefVs j).length := by omega
      dsimp only [memM]
      rw [Function.update_of_ne hne]
      exact hfr addr (by omega)
    have hje_val_M : memM (jEsPtr + j) = jEs[j] := by
      have hne : jEsPtr + j ≠ rawVsPtr + (prefVs j).length := by
        rcases hdisjJ j hj_lt with h | h <;> omega
      dsimp only [memM]
      rw [Function.update_of_ne hne, hfr _ (by rcases hdisjJ j hj_lt with h | h <;> [left; right] <;> omega)]
      exact hjAt j hj_lt
    have hwPtr_val_M : memM (mEmbPtr + jEs[j]) = wPtr := by
      have hne : mEmbPtr + jEs[j] ≠ rawVsPtr + (prefVs j).length := by
        rcases hdisjM _ he_mem with h | h <;> omega
      dsimp only [memM]
      rw [Function.update_of_ne hne, hfr _ (by rcases hdisjM _ he_mem with h | h <;> [left; right] <;> omega)]
    have hwAt_M : MWalkAt memM wPtr (emb jEs[j]) := by
      have hw0 := (hmEmb _ he_mem).2
      intro k hk
      have hne : wPtr + k ≠ rawVsPtr + (prefVs j).length := by
        rcases hdisjW _ he_mem k hk with h | h <;> omega
      dsimp only [memM]
      rw [Function.update_of_ne hne, hfr _ (by rcases hdisjW _ he_mem k hk with h | h <;> [left; right] <;> omega)]
      exact hw0 k hk
    have hwLen_M : memM wPtr = (emb jEs[j]).length := MWalkAt_head hwAt_M
    let dsts := (emb jEs[j]).map H'.dst
    let innerBody : Stmt :=
      .assign 12 (.load (.bin .add (.reg 9) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 11))))) ;;
      .assign 13 (.load (.bin .add (.reg 9) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 11))))) ;;
      .cond (.bin .eq (.reg 13) (.const 1))
        (.call 14 (bOps + dgIdxGetHead) [.reg 0, .reg 12])
        (.call 14 (bOps + dgIdxGetTail) [.reg 0, .reg 12]) ;;
      .store (.bin .add (.reg 5) (.reg 6)) (.reg 14) ;;
      .assign 6 (.bin .add (.reg 6) (.const 1))
    let InvI : ℕ → State → Prop := fun t stI =>
      stI.regs 0 = hPtr ∧ stI.regs 1 = jEs.length ∧ stI.regs 2 = jEsPtr ∧
      stI.regs 3 = jTailsPtr ∧ stI.regs 4 = mEmbPtr ∧ stI.regs 5 = rawVsPtr ∧
      stI.regs 6 = (prefVs j).length + 1 + t ∧ stI.regs 7 = j ∧
      stI.regs 9 = wPtr ∧ stI.regs 10 = (emb jEs[j]).length ∧ stI.regs 11 = t ∧
      ListAt stI.mem rawVsPtr (prefVs j ++ [jTails[j]] ++ dsts.take t) ∧
      ∀ addr, addr < rawVsPtr ∨ rawVsPtr + ((prefVs j).length + 1 + t) ≤ addr → stI.mem addr = mem addr
    let InvIPre : State → Prop := fun stI =>
      stI.regs 0 = hPtr ∧ stI.regs 1 = jEs.length ∧ stI.regs 2 = jEsPtr ∧
      stI.regs 3 = jTailsPtr ∧ stI.regs 4 = mEmbPtr ∧ stI.regs 5 = rawVsPtr ∧
      stI.regs 6 = (prefVs j).length + 1 ∧ stI.regs 7 = j ∧
      stI.regs 9 = wPtr ∧ stI.regs 10 = (emb jEs[j]).length ∧
      ListAt stI.mem rawVsPtr (prefVs j ++ [jTails[j]]) ∧
      ∀ addr, addr < rawVsPtr ∨ rawVsPtr + ((prefVs j).length + 1) ≤ addr → stI.mem addr = mem addr
    have hinner : Triple w p InvIPre (forRange 11 (.const 0) (.reg 10) innerBody)
        (normalPost (InvI (emb jEs[j]).length))
        (fun _ => (emb jEs[j]).length * (95 + Expr.size (.reg 10) + 8) +
          (Expr.size (.const 0) + Expr.size (.reg 10) + 5)) := by
      refine Triple.forRange_const 95 0 (emb jEs[j]).length (Nat.zero_le _) h1_lt (fun _ => hwLen_lt)
        (fun _ h => ⟨by simp [Expr.eval, h0_lt],
          ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
           by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2.1],
           by simp [h.2.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2.2.1],
           by simp [h.2.2.2.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2.2.2.2.1], by simp,
           by simpa using h.2.2.2.2.2.2.2.2.2.2.1,
           by simpa using h.2.2.2.2.2.2.2.2.2.2.2⟩⟩)
        (fun t _ _ _ h => h.2.2.2.2.2.2.2.2.2.2.1)
        (fun t _ _ _ h => by simp [Expr.eval, h.2.2.2.2.2.2.2.2.2.1]) ?_
      intro t _ ht_lt stI ω'' ⟨hI0, hI1, hI2, hI3, hI4, hI5, hI6, hI7, hI9, hI10, hI11, hIat, hIfr⟩
      have hwEnc := mWalkEncode_length (emb jEs[j])
      have ht_ltw : t < 2 ^ w := by omega
      have h2t_lt : 2 * t < 2 ^ w := by omega
      have h12t_lt : 1 + 2 * t < 2 ^ w := by omega
      have h22t_lt : 2 + 2 * t < 2 ^ w := by omega
      have hwp1_lt : wPtr + (1 + 2 * t) < 2 ^ w := by omega
      have hwp2_lt : wPtr + (2 + 2 * t) < 2 ^ w := by omega
      have hwI : MWalkAt stI.mem wPtr (emb jEs[j]) := by
        have hw0 := (hmEmb _ he_mem).2
        intro k hk
        rw [hIfr _ (by rcases hdisjW _ he_mem k hk with h | h <;> [left; right] <;> omega)]
        exact hw0 k hk
      have heH_mem : stI.mem (wPtr + (1 + 2 * t)) = (emb jEs[j])[t].1 := by
        simpa [Nat.add_assoc] using MWalkAt_step_edge hwI ht_lt
      let dBit := if (emb jEs[j])[t].2 then 1 else 0
      have hdB_mem : stI.mem (wPtr + (2 + 2 * t)) = dBit := by
        simpa [dBit, show wPtr + (2 + 2 * t) = wPtr + 1 + 2 * t + 1 by omega] using
          MWalkAt_step_dir hwI ht_lt
      have heH_prop := hembH _ he_mem _ (List.getElem_mem ht_lt)
      have heH_E : (emb jEs[j])[t].1 ∈ H'.E := heH_prop.1
      have heH_lt : (emb jEs[j])[t].1 < 2 ^ w := heH_prop.2
      have hdB_lt : dBit < 2 ^ w := by dsimp only [dBit]; split_ifs <;> omega
      have hDynI : DynGraphAt stI.mem hPtr vCap eCap H' := by
        refine hDynH.of_agree ?_
        intro k hk hk2
        rw [hIfr _ (by rcases hdisjH (k - hPtr) (by omega) with h | h <;> [left; right] <;> omega)]
      have hdst_addr : rawVsPtr + ((prefVs j).length + 1 + t) < 2 ^ w := by omega
      have hlen_next : (prefVs j).length + 1 + (t + 1) < 2 ^ w := by omega
      have hdst_V : H'.dst (emb jEs[j])[t] ∈ H'.V := by
        rcases (hDynH.1 _ heH_E) with ⟨htV, hhV⟩
        dsimp only [MGraph.dst]; split_ifs <;> assumption
      have hdst_lt : H'.dst (emb jEs[j])[t] < 2 ^ w := hHVw _ hdst_V
      have hwords_e : ∀ v ∈ [hPtr, (emb jEs[j])[t].1], v < 2 ^ w := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_hP
        rcases List.mem_cons.mp hv with rfl | hv; · exact heH_lt
        cases hv
      refine runs_start_le ?_
      dsimp only [innerBody]
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (v := (emb jEs[j])[t].1)
          (by simp [Expr.eval, BinOp.eval, hI9, hI11, h1_lt, h2_lt, h2t_lt, h12t_lt, hwp1_lt])
          heH_mem) ?_
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (v := dBit)
          (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hI9, hI11, h2_lt, h2t_lt, h22t_lt, hwp2_lt])
          hdB_mem) ?_
      let stC : State :=
        { mem := stI.mem
          regs := Function.update (Function.update stI.regs 12 (emb jEs[j])[t].1) 13 dBit
          pos := stI.pos }
      have hbranch : ∃ o s' c, Runs w p ω''
          (.cond (.bin .eq (.reg 13) (.const 1))
            (.call 14 (bOps + dgIdxGetHead) [.reg 0, .reg 12])
            (.call 14 (bOps + dgIdxGetTail) [.reg 0, .reg 12]))
          stC o s' c ∧
          (match o with
            | .returned _ => False
            | .normal => s'.mem = stI.mem ∧ s'.regs 0 = hPtr ∧ s'.regs 1 = jEs.length ∧
              s'.regs 2 = jEsPtr ∧ s'.regs 3 = jTailsPtr ∧ s'.regs 4 = mEmbPtr ∧
              s'.regs 5 = rawVsPtr ∧ s'.regs 6 = (prefVs j).length + 1 + t ∧
              s'.regs 7 = j ∧ s'.regs 9 = wPtr ∧ s'.regs 10 = (emb jEs[j]).length ∧
              s'.regs 11 = t ∧ s'.regs 14 = H'.dst (emb jEs[j])[t]) ∧
          c ≤ 60 := by
        refine runs_start_le ?_
        by_cases hdir : (emb jEs[j])[t].2 = true
        · have hdB1 : dBit = 1 := by simp [dBit, hdir]
          refine runs_cond_le_gt (v := 1) ?_ ?_ ?_
          · simp [stC, Expr.eval, BinOp.eval, hdB1, h1_lt]
          · intro _
            have hpre_h : (dgGetHeadContract w vCap eCap H').pre [hPtr, (emb jEs[j])[t].1] stC.mem :=
              ⟨hPtr, (emb jEs[j])[t].1, rfl, hw16, hhB, heH_E, hDynI⟩
            rcases runs_call_of_meetsContract (r := 14) (args := [.reg 0, .reg 12])
              (dgGetHead_meetsContract hpOps)
              (by simp [stC, evalArgs, Expr.eval, Function.update_of_ne, hI0])
              hwords_e hpre_h ω'' with
              ⟨stH, cH, retH, hrH, ⟨_, _, heqH, hmemH, hretH⟩, hr14, hotherH, hcostH⟩
            simp only [List.cons.injEq, and_true] at heqH
            rcases heqH with ⟨_, rfl⟩
            have hdst_eq : H'.dst (emb jEs[j])[t] = H'.head (emb jEs[j])[t].1 := by simp [MGraph.dst, hdir]
            refine ⟨.normal, stH, cH, hrH, ⟨hmemH,
              by rw [hotherH 0 (by decide)]; simp [stC, hI0],
              by rw [hotherH 1 (by decide)]; simp [stC, hI1],
              by rw [hotherH 2 (by decide)]; simp [stC, hI2],
              by rw [hotherH 3 (by decide)]; simp [stC, hI3],
              by rw [hotherH 4 (by decide)]; simp [stC, hI4],
              by rw [hotherH 5 (by decide)]; simp [stC, hI5],
              by rw [hotherH 6 (by decide)]; simp [stC, hI6],
              by rw [hotherH 7 (by decide)]; simp [stC, hI7],
              by rw [hotherH 9 (by decide)]; simp [stC, hI9],
              by rw [hotherH 10 (by decide)]; simp [stC, hI10],
              by rw [hotherH 11 (by decide)]; simp [stC, hI11],
              by rw [hr14, hretH, hdst_eq]⟩,
              by dsimp only [dgGetHeadContract, argsSize, Expr.size] at hcostH ⊢; omega⟩
          · intro hc; cases hc
        · have hdB0 : dBit = 0 := by simp [dBit, hdir]
          refine runs_cond_le_gt (v := 0) ?_ ?_ ?_
          · simp [stC, Expr.eval, BinOp.eval, hdB0, h0_lt, h1_lt]
          · intro hc; exact absurd rfl hc
          · intro _
            have hpre_t : (dgGetTailContract w vCap eCap H').pre [hPtr, (emb jEs[j])[t].1] stC.mem :=
              ⟨hPtr, (emb jEs[j])[t].1, rfl, hw16, hhB, heH_E, hDynI⟩
            rcases runs_call_of_meetsContract (r := 14) (args := [.reg 0, .reg 12])
              (dgGetTail_meetsContract hpOps)
              (by simp [stC, evalArgs, Expr.eval, Function.update_of_ne, hI0])
              hwords_e hpre_t ω'' with
              ⟨stT, cT, retT, hrT, ⟨_, _, heqT, hmemT, hretT⟩, hr14, hotherT, hcostT⟩
            simp only [List.cons.injEq, and_true] at heqT
            rcases heqT with ⟨_, rfl⟩
            have hdst_eq : H'.dst (emb jEs[j])[t] = H'.tail (emb jEs[j])[t].1 := by simp [MGraph.dst, hdir]
            refine ⟨.normal, stT, cT, hrT, ⟨hmemT,
              by rw [hotherT 0 (by decide)]; simp [stC, hI0],
              by rw [hotherT 1 (by decide)]; simp [stC, hI1],
              by rw [hotherT 2 (by decide)]; simp [stC, hI2],
              by rw [hotherT 3 (by decide)]; simp [stC, hI3],
              by rw [hotherT 4 (by decide)]; simp [stC, hI4],
              by rw [hotherT 5 (by decide)]; simp [stC, hI5],
              by rw [hotherT 6 (by decide)]; simp [stC, hI6],
              by rw [hotherT 7 (by decide)]; simp [stC, hI7],
              by rw [hotherT 9 (by decide)]; simp [stC, hI9],
              by rw [hotherT 10 (by decide)]; simp [stC, hI10],
              by rw [hotherT 11 (by decide)]; simp [stC, hI11],
              by rw [hr14, hretT, hdst_eq]⟩,
              by dsimp only [dgGetTailContract, argsSize, Expr.size] at hcostT ⊢; omega⟩
      rcases hbranch with ⟨ob, stB, cb, hrB, hqB, hcB⟩
      cases ob with
      | returned u => exact False.elim hqB
      | normal =>
        rcases hqB with ⟨hBm, hB0, hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB9, hB10, hB11, hB14⟩
        have hTail : ∃ o s' c, Runs w p ω''
            (.store (.bin .add (.reg 5) (.reg 6)) (.reg 14) ;;
             .assign 6 (.bin .add (.reg 6) (.const 1))) stB o s' c ∧
            normalPost (fun s' =>
              InvI (t + 1) { s' with regs := Function.update s'.regs 11 (t + 1) } ∧
                s'.regs 11 = t) o s' ∧
            (20 + cb + 1) + c ≤ 95 := by
          refine runs_seq_store_le (x := rawVsPtr + ((prefVs j).length + 1 + t))
            (v := H'.dst (emb jEs[j])[t])
            (by simp [Expr.eval, BinOp.eval, hB5, hB6, hdst_addr])
            (by simp [Expr.eval, hB14]) ?_
          refine runs_assign_le (v := (prefVs j).length + 1 + (t + 1))
            (by simp [Expr.eval, BinOp.eval, hB6, h1_lt, hlen_next,
              show (prefVs j).length + 1 + t + 1 = (prefVs j).length + 1 + (t + 1) by omega]) ?_
            (by dsimp only [Expr.size]; omega)
          refine ⟨⟨by simp [hB0], by simp [hB1], by simp [hB2], by simp [hB3],
            by simp [hB4], by simp [hB5], by simp, by simp [hB7],
            by simp [hB9], by simp [hB10], by simp, ?_, ?_⟩, by simp [hB11]⟩
          · have htake : dsts.take (t + 1) = dsts.take t ++ [H'.dst (emb jEs[j])[t]] := by
              have ht_d : t < dsts.length := by simpa [dsts] using ht_lt
              rw [List.take_succ_eq_append_getElem ht_d]
              simp [dsts]
            rw [htake, ← List.append_assoc]
            have hatB : ListAt stB.mem rawVsPtr (prefVs j ++ [jTails[j]] ++ dsts.take t) := by
              rw [hBm]; exact hIat
            refine listAt_append.mpr ⟨ListAt.update_ge hatB (by
              rw [List.length_append, List.length_append, List.length_cons, List.length_nil,
                List.length_take, Nat.min_eq_left (by simp [dsts]; omega : t ≤ dsts.length)]), fun u hu => ?_⟩
            simp only [List.length_cons, List.length_nil] at hu
            have hu0 : u = 0 := by omega
            subst hu0
            have hlen_p : (prefVs j ++ [jTails[j]] ++ dsts.take t).length =
                (prefVs j).length + 1 + t := by
              simp only [List.length_append, List.length_cons, List.length_nil,
                List.length_take, Nat.min_eq_left (by simp [dsts]; omega : t ≤ dsts.length)]
            rw [hlen_p]
            simp [Nat.add_assoc]
          · intro addr had
            have hne : addr ≠ rawVsPtr + ((prefVs j).length + 1 + t) := by omega
            dsimp only
            rw [Function.update_of_ne hne, hBm]
            exact hIfr addr (by omega)
        rcases hTail with ⟨ot, stT, ct, hrT, hqT, hcT⟩
        exact ⟨ot, stT, cb + ct + 1, runs_seq_iff.mpr (Or.inr ⟨stB, cb, ct, hrB, hrT, rfl⟩),
          hqT, by dsimp only [Expr.size]; omega⟩
    refine runs_start_le ?_
    dsimp only [outerBody]
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := jTails[j])
        (by simp [Expr.eval, BinOp.eval, hr3, hr7, hjt_addr_lt]) hjt_val) ?_
    refine runs_seq_store_le (x := rawVsPtr + (prefVs j).length) (v := jTails[j])
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr5, hr6, hdst_j0])
      (by eval_expr) ?_
    refine runs_seq_assign_le (v := (prefVs j).length + 1)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr6, h1_lt, hpref1_ltw]) ?_
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := jEs[j])
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hr7, hje_addr_lt])
        hje_val_M) ?_
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := wPtr)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr4, hm_addr_lt])
        hwPtr_val_M) ?_
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := (emb jEs[j]).length)
        (by simp [Expr.eval]) hwLen_M) ?_
    refine runs_triple_le hinner
      ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
       by simp [hr5], by simp, by simp [hr7], by simp, by simp,
       by simpa using listAt_append.mpr ⟨ListAt.update_ge hat (le_refl _),
         fun u hu => by simp at hu; subst u; simp⟩,
       by simpa using hfr_M⟩
      (fun o stI hq => by
        cases o with
        | returned u => exact False.elim hq
        | normal =>
          rcases hq with ⟨hI0, hI1, hI2, hI3, hI4, hI5, hI6, hI7, _, _, _, hIat, hIfr⟩
          have hstep_eq : stepVs j = [jTails[j]] ++ dsts := by
            dsimp only [stepVs, dsts, MGraph.walkVertices]
            rw [List.getD_eq_getElem _ _ hj_tlen, List.getD_eq_getElem _ _ hj_lt]
            simp
          have htake_all : dsts.take (emb jEs[j]).length = dsts :=
            List.take_of_length_le (by simp [dsts])
          refine ⟨⟨by simp [hI0], by simp [hI1], by simp [hI2], by simp [hI3],
            by simp [hI4], by simp [hI5], ?_, by simp, ?_, ?_⟩, hI7⟩
          · rw [hpref_succ, List.length_append, hstep_eq, List.length_append, List.length_cons,
              List.length_nil]
            simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 7), dsts, List.length_map] at hI6 ⊢
            omega
          · rw [hpref_succ, hstep_eq]
            simpa [List.append_assoc, htake_all] using hIat
          · intro addr had
            rw [hpref_succ, hstep_eq] at had
            simp only [List.length_append, List.length_cons, List.length_nil, dsts,
              List.length_map] at had
            exact hIfr addr (by omega))
      (by dsimp only [stepCost, Expr.size]; rw [List.getD_eq_getElem _ _ hj_lt]; omega)
  refine runs_seq_triple_le houter
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [prefVs, startState], by simp [startState],
     listAt_nil _ _, fun _ _ => rfl⟩ ?_
  intro st' ⟨_, _, _, _, _, _, hr6, _, hat', hfr'⟩
  rw [hpref_all] at hr6 hat' hfr'
  refine runs_ret_le (by eval_expr)
    ⟨hPtr, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr, rfl, hr6, hat', hfr'⟩ ?_
  dsimp only [gtCollectRawVsContract, Expr.size]
  have hrc : rangeCost stepCost 0 jEs.length + 15 * jEs.length =
      115 * (collectRawVsFun H' jEs jTails emb).length := by
    have haux : ∀ k, k ≤ jEs.length →
        rangeCost stepCost 0 k + 15 * k = 115 * (prefVs k).length := by
      intro k hk
      induction k with
      | zero => simp [prefVs]
      | succ k ih =>
        have hstep : rangeCost stepCost 0 (k + 1) =
            rangeCost stepCost 0 k + stepCost k := by
          simp only [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.map_cons,
            List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [hstep, hpref_succ, List.length_append]
        have hslen : (stepVs k).length = 1 + (emb (jEs.getD k 0)).length := by
          simp [stepVs, MGraph.walkVertices]; omega
        rw [hslen]
        have hih := ih (by omega)
        dsimp only [stepCost] at hih ⊢
        omega
    simpa [hpref_all] using haux jEs.length (le_refl _)
  omega

end

end MinCostFlow.DynSpanner.Program
