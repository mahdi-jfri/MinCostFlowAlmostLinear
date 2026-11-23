module

public import MinCostFlow.DynSpanner.Program.DynGraphRefillDefs
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop
import WordRAM.Tactic

/-!
# Verification of `dgClearStmt` (`DynGraphRefillClear`)

Proves `dgClear_meetsContract`: clearing a `DynGraphAt mem gPtr vCap eCap G` via its live vertex
and edge lists restores `DynGraphAt mem' gPtr vCap eCap dgEmptyGraph` in `O(G.n + G.m + 1)` steps
with zero scratch memory and preserves all memory outside `[gPtr, gPtr + dynGraphSize vCap eCap)`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

/-- `dgClearStmt` clears a `DynGraphAt` in `O(G.n + G.m + 1)` steps using zero scratch. -/
theorem dgClear_meetsContract {w : ℕ} {p : Program} {bOps bEdge bRefill vCap eCap : ℕ} {G : MGraph}
    (hp : p.HasAt bRefill (dgRefillProcs bOps bEdge bRefill)) :
    MeetsContract w p (bRefill + dgIdxClear) (dgClearContract w vCap eCap G) := by
  refine meetsContract_of_runs
    (hp.get (i := dgIdxClear) (by simp [dgRefillProcs, dgIdxClear]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gPtr, rfl, hw16, hbound, hG⟩
  have hG_copy := hG
  rcases hG with ⟨_, hvCap, heCap, hvc_mem, hec_mem, hn_mem, hm_mem, hvp_mem,
    ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, _⟩, _, _, hep_mem,
    ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩, _, _⟩
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hGn_le : G.n ≤ vCap := by
    rw [← hvL_len]
    exact nodup_length_le_cap hvL_nd (fun v hv => hvCap v ((hvL_mem v).mp hv))
  have hGm_le : G.m ≤ eCap := by
    rw [← heL_len]
    exact nodup_length_le_cap heL_nd (fun e he => heCap e ((heL_mem e).mp he))
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h4_lt : (4 : ℕ) < 2 ^ w := by omega
  have h5_lt : (5 : ℕ) < 2 ^ w := by omega
  have h6_lt : (6 : ℕ) < 2 ^ w := by omega
  have h7_lt : (7 : ℕ) < 2 ^ w := by omega
  have hgp_lt : gPtr < 2 ^ w := by omega
  have hvc_lt : vCap < 2 ^ w := by omega
  have hec_lt : eCap < 2 ^ w := by omega
  have hGn_lt : G.n < 2 ^ w := by omega
  have hGm_lt : G.m < 2 ^ w := by omega
  have h5vc_lt : 5 * vCap < 2 ^ w := by omega
  have h6vc_lt : 6 * vCap < 2 ^ w := by omega
  have h7vc_lt : 7 * vCap < 2 ^ w := by omega
  have hgp1_lt : gPtr + 1 < 2 ^ w := by omega
  have hgp2_lt : gPtr + 2 < 2 ^ w := by omega
  have hgp3_lt : gPtr + 3 < 2 ^ w := by omega
  have hgp4_lt : gPtr + 4 < 2 ^ w := by omega
  have hvlist_lt : gPtr + 4 + vCap < 2 ^ w := by omega
  have hsdeg_lt : gPtr + 4 + 5 * vCap < 2 ^ w := by omega
  have hinc_lt : gPtr + 4 + 6 * vCap < 2 ^ w := by omega
  have hepres_lt : gPtr + 4 + 7 * vCap < 2 ^ w := by omega
  have helist_lt : gPtr + 4 + 7 * vCap + eCap < 2 ^ w := by omega
  have hvc_mem' : mem gPtr = vCap := by simpa [dgVCapOff] using hvc_mem
  have hec_mem' : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hec_mem
  have hn_mem' : mem (gPtr + 2) = G.n := by simpa [dgNOff] using hn_mem
  have hm_mem' : mem (gPtr + 3) = G.m := by simpa [dgMOff] using hm_mem
  refine runs_start_le ?_
  dsimp only [dgRefillProcs, dgIdxClear, List.getElem_cons_zero, dgClearStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := vCap) (by eval_expr)
    (by simpa [startState] using hvc_mem')) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := eCap) (by eval_expr)
    (by simpa [startState] using hec_mem')) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := G.n) (by eval_expr)
    (by simpa [startState] using hn_mem')) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := G.m) (by eval_expr)
    (by simpa [startState] using hm_mem')) ?_
  refine runs_seq_assign_le (v := gPtr + 4) (by eval_expr) ?_
  refine runs_seq_assign_le (v := gPtr + 4 + vCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := gPtr + 4 + 5 * vCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := gPtr + 4 + 6 * vCap) (by eval_expr) ?_
  -- Vertex clearing loop
  let InvV : ℕ → State → Prop := fun k st =>
    k ≤ G.n ∧
    st.regs 0 = gPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = G.n ∧
    st.regs 4 = G.m ∧ st.regs 5 = gPtr + 4 ∧ st.regs 6 = gPtr + 4 + vCap ∧
    st.regs 7 = gPtr + 4 + 5 * vCap ∧ st.regs 8 = gPtr + 4 + 6 * vCap ∧ st.regs 9 = k ∧
    (∀ v < vCap, (v ∉ G.V ∨ v ∈ vL.take k) →
      st.mem (dgVPresBase gPtr + v) = 0 ∧
      st.mem (dgSlotDegBase gPtr vCap + v) = 0 ∧
      st.mem (dgIncHeadBase gPtr vCap + v) = 0) ∧
    (∀ addr,
      (addr < gPtr + 4 ∨
       (gPtr + 4 + vCap ≤ addr ∧ addr < gPtr + 4 + 5 * vCap) ∨
       gPtr + 4 + 7 * vCap ≤ addr) →
      st.mem addr = mem addr)
  let bodyV : Stmt :=
    .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
    .store (.bin .add (.reg 5) (.reg 10)) (.const 0) ;;
    .store (.bin .add (.reg 7) (.reg 10)) (.const 0) ;;
    .store (.bin .add (.reg 8) (.reg 10)) (.const 0)
  let PV : State → Prop := fun st =>
    st.regs 0 = gPtr ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = G.n ∧
    st.regs 4 = G.m ∧ st.regs 5 = gPtr + 4 ∧ st.regs 6 = gPtr + 4 + vCap ∧
    st.regs 7 = gPtr + 4 + 5 * vCap ∧ st.regs 8 = gPtr + 4 + 6 * vCap ∧
    st.mem = mem
  have hLoopV : Triple w p PV (forRange 9 (.const 0) (.reg 3) bodyV) (normalPost (InvV G.n))
      (fun _ => (G.n - 0) * (25 + Expr.size (.reg 3) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 3) + 5)) := by
    refine Triple.forRange_const 25 0 G.n (Nat.zero_le _) h1_lt (fun _ => hGn_lt)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmem⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
            by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp, ?_, fun _ _ => hmem ▸ rfl⟩⟩
        intro v hv hcase
        rcases hcase with hvNot | hvTake
        · rw [hmem]
          have hsd := hG_copy.slotDeg_zero_of_not_mem hv hvNot
          exact ⟨by simpa [hvNot] using hvp_mem v hv, hsd.1, hsd.2⟩
        · simp at hvTake)
      (fun k st _ _ hk => hk.2.2.2.2.2.2.2.2.2.2.1)
      (fun k st _ _ hk => by simp [Expr.eval, hk.2.2.2.2.1])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hcl, hfr⟩
        have hk_vL : k < vL.length := hvL_len.symm ▸ hk_lt
        let v := vL[k]
        have hv_cap : v < vCap := hvCap v ((hvL_mem v).mp (List.getElem_mem hk_vL))
        have hv_ltw : v < 2 ^ w := lt_trans hv_cap hvc_lt
        have hvlist_k_lt : gPtr + 4 + vCap + k < 2 ^ w := by omega
        have hvlist_k_mem : st.mem (gPtr + 4 + vCap + k) = v := by
          rw [hfr _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
          exact hvL_at k hk_vL
        have hvpres_lt : gPtr + 4 + v < 2 ^ w := by omega
        have hvsdeg_lt : gPtr + 4 + 5 * vCap + v < 2 ^ w := by omega
        have hvinc_lt : gPtr + 4 + 6 * vCap + v < 2 ^ w := by omega
        suffices h : ∃ o st₁ c, Runs w p ω' bodyV st o st₁ c ∧
            (normalPost fun st₁ =>
              InvV (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 9 (k + 1), pos := st₁.pos } ∧
                st₁.regs 9 = k) o st₁ ∧
            0 + c ≤ 25 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyV]
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := v)
          (by simp [Expr.eval, BinOp.eval, hr6, hr9, hvlist_k_lt]) hvlist_k_mem) ?_
        refine runs_seq_store_le (x := gPtr + 4 + v) (v := 0)
          (by simp [Expr.eval, BinOp.eval, hr5, hvpres_lt]) (by simp [Expr.eval, h0_lt]) ?_
        refine runs_seq_store_le (x := gPtr + 4 + 5 * vCap + v) (v := 0)
          (by simp [Expr.eval, BinOp.eval, hr7, hvsdeg_lt]) (by simp [Expr.eval, h0_lt]) ?_
        refine runs_store_le (x := gPtr + 4 + 6 * vCap + v) (v := 0)
          (by simp [Expr.eval, BinOp.eval, hr8, hvinc_lt]) (by simp [Expr.eval, h0_lt]) ?_ (by simp)
        refine ⟨⟨by omega, by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
          by simp [hr5], by simp [hr6], by simp [hr7], by simp [hr8], by simp, ?_, ?_⟩, by simp [hr9]⟩
        · intro u hu hcase
          have hcase' : (u ∉ G.V ∨ u ∈ vL.take k) ∨ u = v := by
            rcases hcase with hnot | htake
            · exact Or.inl (Or.inl hnot)
            · rw [List.take_succ_eq_append_getElem hk_vL, List.mem_append, List.mem_singleton] at htake
              rcases htake with h1 | h2
              · exact Or.inl (Or.inr h1)
              · exact Or.inr h2
          rcases hcase' with hold | rfl
          · have ho := hcl u hu hold
            refine ⟨?_, ?_, ?_⟩
            · dsimp only [dgVPresBase]
              by_cases huv : u = v
              · subst huv
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact ho.1
            · dsimp only [dgSlotDegBase]
              by_cases huv : u = v
              · subst huv
                rw [Function.update_of_ne (by omega), Function.update_self]
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact ho.2.1
            · dsimp only [dgIncHeadBase]
              by_cases huv : u = v
              · subst huv; rw [Function.update_self]
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact ho.2.2
          · refine ⟨?_, ?_, ?_⟩
            · dsimp only [dgVPresBase]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
            · dsimp only [dgSlotDegBase]
              rw [Function.update_of_ne (by omega), Function.update_self]
            · dsimp only [dgIncHeadBase]; rw [Function.update_self]
        · intro addr haddr
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hfr addr haddr)
  refine runs_seq_triple_le hLoopV ?_ ?_
  · refine ⟨by simp [startState], by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, rfl⟩
  intro stV ⟨_, hr0V, hr1V, hr2V, hr3V, hr4V, hr5V, hr6V, _, _, _, hclV, hfrV⟩
  have hclV_all : ∀ v < vCap,
      stV.mem (dgVPresBase gPtr + v) = 0 ∧
      stV.mem (dgSlotDegBase gPtr vCap + v) = 0 ∧
      stV.mem (dgIncHeadBase gPtr vCap + v) = 0 := by
    intro v hv
    apply hclV v hv
    by_cases hvG : v ∈ G.V
    · right; rw [List.take_of_length_le hvL_len.le]; exact (hvL_mem v).mpr hvG
    · left; exact hvG
  refine runs_seq_assign_le (v := gPtr + 4 + 7 * vCap)
    (by simp [Expr.eval, BinOp.eval, hr5V, hr1V, h7_lt, h7vc_lt, hepres_lt]) ?_
  refine runs_seq_assign_le (v := gPtr + 4 + 7 * vCap + eCap)
    (by simp [Expr.eval, BinOp.eval, hr2V, helist_lt]) ?_
  -- Edge clearing loop
  let InvE : ℕ → State → Prop := fun k st =>
    k ≤ G.m ∧
    st.regs 0 = gPtr ∧ st.regs 4 = G.m ∧ st.regs 5 = gPtr + 4 + 7 * vCap ∧
    st.regs 6 = gPtr + 4 + 7 * vCap + eCap ∧ st.regs 9 = k ∧
    (∀ v < vCap,
      st.mem (dgVPresBase gPtr + v) = 0 ∧
      st.mem (dgSlotDegBase gPtr vCap + v) = 0 ∧
      st.mem (dgIncHeadBase gPtr vCap + v) = 0) ∧
    (∀ e < eCap, (e ∉ G.E ∨ e ∈ eL.take k) → st.mem (dgEPresBase gPtr vCap + e) = 0) ∧
    (∀ addr, (addr < gPtr + 4 + 7 * vCap ∨ gPtr + 4 + 7 * vCap + eCap ≤ addr) →
      st.mem addr = stV.mem addr)
  let bodyE : Stmt :=
    .assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
    .store (.bin .add (.reg 5) (.reg 10)) (.const 0)
  let PE : State → Prop := fun st =>
    st.regs 0 = gPtr ∧ st.regs 4 = G.m ∧ st.regs 5 = gPtr + 4 + 7 * vCap ∧
    st.regs 6 = gPtr + 4 + 7 * vCap + eCap ∧ st.mem = stV.mem
  have hLoopE : Triple w p PE (forRange 9 (.const 0) (.reg 4) bodyE) (normalPost (InvE G.m))
      (fun _ => (G.m - 0) * (15 + Expr.size (.reg 4) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 4) + 5)) := by
    refine Triple.forRange_const 15 0 G.m (Nat.zero_le _) h1_lt (fun _ => hGm_lt)
      (fun st hst => by
        rcases hst with ⟨h0, h4, h5, h6, hmem⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, by simp [h0], by simp [h4], by simp [h5], by simp [h6], by simp,
            hmem ▸ hclV_all, ?_, fun _ _ => hmem ▸ rfl⟩⟩
        intro e he hcase
        rcases hcase with heNot | heTake
        · rw [hmem, hfrV _ (Or.inr (Or.inr (by dsimp [dgEPresBase]; omega)))]
          simpa [heNot] using hep_mem e he
        · simp at heTake)
      (fun k st _ _ hk => hk.2.2.2.2.2.1)
      (fun k st _ _ hk => by simp [Expr.eval, hk.2.2.1])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr4, hr5, hr6, hr9, hclv, hcle, hfr⟩
        have hk_eL : k < eL.length := heL_len.symm ▸ hk_lt
        let e := eL[k]
        have he_cap : e < eCap := heCap e ((heL_mem e).mp (List.getElem_mem hk_eL))
        have he_ltw : e < 2 ^ w := lt_trans he_cap hec_lt
        have helist_k_lt : gPtr + 4 + 7 * vCap + eCap + k < 2 ^ w := by omega
        have helist_k_mem : st.mem (gPtr + 4 + 7 * vCap + eCap + k) = e := by
          rw [hfr _ (Or.inr (by omega)), hfrV _ (Or.inr (Or.inr (by omega)))]
          exact heL_at k hk_eL
        have hepres_e_lt : gPtr + 4 + 7 * vCap + e < 2 ^ w := by omega
        suffices h : ∃ o st₁ c, Runs w p ω' bodyE st o st₁ c ∧
            (normalPost fun st₁ =>
              InvE (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 9 (k + 1), pos := st₁.pos } ∧
                st₁.regs 9 = k) o st₁ ∧
            0 + c ≤ 15 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyE]
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := e)
          (by simp [Expr.eval, BinOp.eval, hr6, hr9, helist_k_lt]) helist_k_mem) ?_
        refine runs_store_le (x := gPtr + 4 + 7 * vCap + e) (v := 0)
          (by simp [Expr.eval, BinOp.eval, hr5, hepres_e_lt]) (by simp [Expr.eval, h0_lt]) ?_ (by simp)
        refine ⟨⟨by omega, by simp [hr0], by simp [hr4], by simp [hr5], by simp [hr6], by simp,
          ?_, ?_, ?_⟩, by simp [hr9]⟩
        · intro v hv
          have hv0 := hclv v hv
          refine ⟨?_, ?_, ?_⟩
          · dsimp only [dgVPresBase]; rw [Function.update_of_ne (by omega)]; exact hv0.1
          · dsimp only [dgSlotDegBase]; rw [Function.update_of_ne (by omega)]; exact hv0.2.1
          · dsimp only [dgIncHeadBase]; rw [Function.update_of_ne (by omega)]; exact hv0.2.2
        · intro u hu hcase
          have hcase' : (u ∉ G.E ∨ u ∈ eL.take k) ∨ u = e := by
            rcases hcase with hnot | htake
            · exact Or.inl (Or.inl hnot)
            · rw [List.take_succ_eq_append_getElem hk_eL, List.mem_append, List.mem_singleton] at htake
              rcases htake with h1 | h2
              · exact Or.inl (Or.inr h1)
              · exact Or.inr h2
          rcases hcase' with hold | rfl
          · dsimp only [dgEPresBase]
            by_cases hue : u = e
            · subst hue; rw [Function.update_self]
            · rw [Function.update_of_ne (by omega)]; exact hcle u hu hold
          · dsimp only [dgEPresBase]; rw [Function.update_self]
        · intro addr haddr
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr addr haddr)
  refine runs_seq_triple_le hLoopE ⟨by simp [hr0V], by simp [hr4V], by simp, by simp, rfl⟩ ?_
  intro stE ⟨_, hr0E, _, _, _, _, hclV_E, hclE, hfrE⟩
  have hclE_all : ∀ e < eCap, stE.mem (dgEPresBase gPtr vCap + e) = 0 := by
    intro e he
    apply hclE e he
    by_cases heG : e ∈ G.E
    · right; rw [List.take_of_length_le heL_len.le]; exact (heL_mem e).mpr heG
    · left; exact heG
  -- Store n := 0, m := 0, return gPtr
  refine runs_seq_store_le (x := gPtr + 2) (v := 0)
    (by simp [Expr.eval, BinOp.eval, hr0E, h2_lt, hgp2_lt]) (by simp [Expr.eval, h0_lt]) ?_
  refine runs_seq_store_le (x := gPtr + 3) (v := 0)
    (by simp [Expr.eval, BinOp.eval, hr0E, h3_lt, hgp3_lt]) (by simp [Expr.eval, h0_lt]) ?_
  refine runs_ret_le (v := gPtr) (by simp [Expr.eval, hr0E]) ?_ ?_
  · refine ⟨gPtr, rfl, rfl, ?_, ?_⟩
    · refine ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [dgVCapOff]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Nat.add_zero,
          hfrE _ (Or.inl (by omega)), hfrV _ (Or.inl (by omega))]
        exact hvc_mem'
      · dsimp only [dgECapOff]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          hfrE _ (Or.inl (by omega)), hfrV _ (Or.inl (by omega))]
        exact hec_mem'
      · dsimp only [dgNOff]
        rw [Function.update_of_ne (by omega), Function.update_self]; simp [dgEmptyGraph, MGraph.n]
      · dsimp only [dgMOff]
        rw [Function.update_self]; simp [dgEmptyGraph, MGraph.m]
      · intro v hv
        simp only [dgEmptyGraph, Finset.notMem_empty, ↓reduceIte, dgVPresBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact (hclV_E v hv).1
      · exact ⟨[], by simp [dgEmptyGraph, MGraph.n], List.nodup_nil, fun _ => by simp [dgEmptyGraph],
          fun i hi => by simp at hi, fun i hi => by simp at hi⟩
      · intro _ h; cases h
      · intro _ h; cases h
      · intro e he
        simp only [dgEmptyGraph, Finset.notMem_empty, ↓reduceIte, dgEPresBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hclE_all e he
      · exact ⟨[], by simp [dgEmptyGraph, MGraph.m], List.nodup_nil, fun _ => by simp [dgEmptyGraph],
          fun i hi => by simp at hi, fun i hi => by simp at hi⟩
      · intro _ h; cases h
      · refine ⟨fun _ => [], fun s hs => ?_⟩
        have hhd0 : (Function.update (Function.update stE.mem (gPtr + 2) 0) (gPtr + 3) 0)
            (dgIncHeadBase gPtr vCap + s) = 0 := by
          dsimp only [dgIncHeadBase]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (hclV_E s hs).2.2
        have hdeg0 : (Function.update (Function.update stE.mem (gPtr + 2) 0) (gPtr + 3) 0)
            (dgSlotDegBase gPtr vCap + s) = 0 := by
          dsimp only [dgSlotDegBase]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (hclV_E s hs).2.1
        exact ⟨IsDoublyLinkedList.nil hhd0, hdeg0, fun h => by simp [dgEmptyGraph]⟩
    · intro addr hout
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rcases hout with hlt | hge
      · exact (hfrE addr (Or.inl (by omega))).trans (hfrV addr (Or.inl (by omega)))
      · exact (hfrE addr (Or.inr (by omega))).trans (hfrV addr (Or.inr (Or.inr (by omega))))
  · simp only [dgClearContract, dgClearCost, List.getD_cons_zero, hn_mem, hm_mem, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
