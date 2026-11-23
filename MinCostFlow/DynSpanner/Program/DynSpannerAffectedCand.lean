module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedCandB

import Mathlib.Tactic.Linarith

/-!
# Dynamic Spanner Candidate Collection (`DynSpannerAffectedCand`)

Completes the Word-RAM correctness and exact cost bound for `dsCollectCandStmt`:
middle loop (`dsCollectCand_midLoop_triple`), outer loop (`dsCollectCand_outerLoop_triple`),
Phase B (`dsCollectCand_phaseB_triple`), and `dsCollectCand_meetsContract`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

private lemma rangeCost_add_const (f : ℕ → ℕ) (c n : ℕ) :
    rangeCost (fun k => f k + c) 0 n = rangeCost f 0 n + rangeCost (fun _ => c) 0 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [rangeCost, Nat.sub_zero, List.range'_eq_map_range, List.map_map,
      List.range_succ, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton, Function.comp_def, Nat.zero_add] at ih ⊢
    omega

/-! ## Middle loop (`forRange 22 0 r15`) -/

private lemma dsCollectCand_midLoop_triple (c : CandCtx) {p : Program}
    {i : ℕ} (hi : i < c.j) (cand0 : List ℕ)
    (hnd0 : cand0.Nodup) (hsub0 : ∀ x ∈ cand0, x ∈ c.G'.E ∧ x < c.eCap)
    (rInit : ℕ → ℕ) :
    let hiL1 : i < c.L + 1 := by have := c.hjL; omega
    Triple c.w p
      (fun st => CandMemInv c cand0 st ∧
        st.regs 18 = i ∧
        st.regs 19 = c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i) ∧
        0 < st.regs 19 ∧
        st.regs 20 = dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
        st.regs 21 = dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
        ∀ r ≤ 21, r ≠ 14 → st.regs r = rInit r)
      (forRange 22 (.const 0) (.reg 15) dsCandMidBody)
      (normalPost fun st =>
        CandMemInv c (midCandFold c.G' (c.revLists ⟨i, hiL1⟩) cand0 c.sPrevList c.sPrevList.length) st ∧
        st.regs 18 = i ∧
        st.regs 19 = c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i) ∧
        0 < st.regs 19 ∧
        st.regs 20 = dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
        st.regs 21 = dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
        ∀ r ≤ 21, r ≠ 14 → st.regs r = rInit r)
      (fun _ =>
        60 * (c.sPrevList.map fun v => (c.revLists ⟨i, hiL1⟩ v).length).sum +
          44 * c.sPrevList.length + 7) := by
  intro hiL1
  have hlay := c.lay
  have hw16 := c.hw16
  let stepCost : ℕ → ℕ := fun k =>
    60 * (if hk : k < c.sPrevList.length then (c.revLists ⟨i, hiL1⟩ c.sPrevList[k]).length else 0) + 35
  let InvM : ℕ → State → Prop := fun k st =>
    CandMemInv c (midCandFold c.G' (c.revLists ⟨i, hiL1⟩) cand0 c.sPrevList k) st ∧
    st.regs 18 = i ∧
    st.regs 19 = c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i) ∧
    0 < st.regs 19 ∧
    st.regs 20 = dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
    st.regs 21 = dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
    st.regs 22 = k ∧
    ∀ r ≤ 21, r ≠ 14 → st.regs r = rInit r
  have ht := Triple.forRange_le (w := c.w) (p := p)
    (P := fun st => CandMemInv c cand0 st ∧
      st.regs 18 = i ∧
      st.regs 19 = c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i) ∧
      0 < st.regs 19 ∧
      st.regs 20 = dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
      st.regs 21 = dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
      ∀ r ≤ 21, r ≠ 14 → st.regs r = rInit r)
    (r := 22) (lo := .const 0) (hi := .reg 15)
    (body := dsCandMidBody) (Inv := InvM) stepCost 0 c.sPrevList.length
    (Nat.zero_le _) (by have := c.hw16; omega)
    (fun _ => lt_of_le_of_lt c.sPrev_len_le hlay.vCap_w)
    (fun st hP => by
      rcases hP with ⟨hinv, r18, r19, h19, r20, r21, hfr⟩
      refine ⟨Expr.eval_const (by omega), ?_⟩
      dsimp only [InvM]
      exact ⟨{
        regs := hinv.regs.agree (fun r hr _ => by
          dsimp only; rw [Function.update_of_ne (by omega : r ≠ 22)])
        cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
        r14_eq := by
          dsimp only
          rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 22), hinv.r14_eq]; rfl
        cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame
      },
      by rw [Function.update_of_ne (by decide : (18 : ℕ) ≠ 22), r18],
      by rw [Function.update_of_ne (by decide : (19 : ℕ) ≠ 22), r19],
      by rw [Function.update_of_ne (by decide : (19 : ℕ) ≠ 22)]; exact h19,
      by rw [Function.update_of_ne (by decide : (20 : ℕ) ≠ 22), r20],
      by rw [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22), r21],
      Function.update_self _ _ _,
      fun r hr h14 => by rw [Function.update_of_ne (by omega : r ≠ 22), hfr r hr h14]⟩)
    (fun k st _ _ hM => hM.2.2.2.2.2.2.1)
    (fun k st _ _ hM => by simp [Expr.eval, hM.1.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])
    (fun k _ hk => by
      intro st ω ⟨hinv, r18, r19, h19, r20, r21, r22, hfr⟩
      set v := c.sPrevList[k]
      have hv_S : v ∈ c.S_prev := (c.hs_mem v).mp (List.getElem_mem hk)
      have hv_cap : v < c.vCap := c.hS_cap v hv_S
      have hhp2_lt : c.heapPtr + 2 < 2 ^ c.w := by have := c.hh_lt; omega
      have hhp2k_lt : c.heapPtr + 2 + k < 2 ^ c.w := by
        have := c.hh_lt; have := c.sPrev_len_le; omega
      have hev23 : (Expr.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 22))).eval c.w st = some v :=
        Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hinv.regs.2.2.1) (Expr.eval_const (by omega)) hhp2_lt)
            (Expr.eval_reg_of_eq r22) hhp2k_lt)
          (hinv.read_sPrev hk)
      suffices hres : ∃ o st' c_1,
          Runs c.w p ω dsCandMidBody st o st' c_1 ∧
            normalPost (fun st' =>
              InvM (k + 1) { st' with regs := Function.update st'.regs 22 (k + 1) } ∧ st'.regs 22 = k) o st' ∧
            0 + c_1 ≤ stepCost k by
        rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
        dsimp only
        exact ⟨o, st', c_1, hr, hq, by omega⟩
      dsimp only [dsCandMidBody]
      refine runs_seq_assign_le hev23 ?_
      have hrevg_lt_fix : dsRevGenBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) <
          c.b + dsFixedSize c.L c.vCap c.eCap := by
        have hm := c.mul_vCap_add_lt hi hv_cap
        have := hlay.revg_lt_revh; have := hlay.revh_lt_sg; have := hlay.sg_lt_sh
        have := hlay.sh_lt_sb; have := hlay.sb_lt_es; have := hlay.es_lt_fix; omega
      have hrevg_w : dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap + v < 2 ^ c.w := by
        have := hlay.hp_lt_w; have := c.hfix; omega
      have hrevg_mem : st.mem (dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap + v) =
          c.mem0 (dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap + v) := by
        have h1 : dsRevGenBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) ≠ c.b + dsGenOff := by
          have := hlay.b_lt_dom; have := hlay.dom_lt_revg; omega
        have h2 : ∀ z < c.vCap, dsRevGenBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) ≠
            dsSBitBase c.b c.L c.vCap c.eCap + z := fun z hz => by
          have hm := c.mul_vCap_add_lt hi hv_cap
          have := hlay.revg_lt_revh; have := hlay.revh_lt_sg; have := hlay.sg_lt_sh
          have := hlay.sh_lt_sb; omega
        have h3 : ∀ z < c.eCap, dsRevGenBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) ≠
            dsEStampBase c.b c.L c.vCap c.eCap + z := fun z hz => by
          have hm := c.mul_vCap_add_lt hi hv_cap
          have := hlay.revg_lt_revh; have := hlay.revh_lt_sg; have := hlay.sg_lt_sh
          have := hlay.sh_lt_sb; have := hlay.sb_lt_es; omega
        simpa [Nat.add_assoc] using hinv.read_lt_fix hrevg_lt_fix h1 h2 h3
      have hrev_spec := c.hm_rev ⟨i, hiL1⟩ hi v hv_S
      set rg := c.mem0 (dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap + v)
      set dg := c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i)
      refine runs_cond_le (v := if rg = dg then 1 else 0) ?_ ?_ ?_
      · refine Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_add
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide : (20 : ℕ) ≠ 23), r20]))
          (Expr.eval_reg_of_eq (r := 23) (v := v) (by simp)) hrevg_w) hrevg_mem)
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide : (19 : ℕ) ≠ 23), r19]))
          (by have := c.hw16; omega)
      · intro hrg_eq_nz
        have hrg_eq : rg = dg := by by_contra hne; simp [hne] at hrg_eq_nz
        have h19_pos : 0 < dg := by rw [← r19]; exact h19
        have hll_v : LinkedListIn c.footRev c.mem0
            (c.mem0 (dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap + v))
            (c.revLists ⟨i, hiL1⟩ v) := by
          have hcond : 0 < dg ∧ rg = dg := ⟨h19_pos, hrg_eq⟩
          have h2 := hrev_spec.2.1; simp only [hcond] at h2; exact h2
        have hrevh_lt_fix : dsRevHeadBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) <
            c.b + dsFixedSize c.L c.vCap c.eCap := by
          have hm := c.mul_vCap_add_lt hi hv_cap
          have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
          have := hlay.sb_lt_es; have := hlay.es_lt_fix; omega
        have hrevh_w : dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap + v < 2 ^ c.w := by
          have := hlay.hp_lt_w; have := c.hfix; omega
        have hrevh_mem : st.mem (dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap + v) =
            c.mem0 (dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap + v) := by
          have h1 : dsRevHeadBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) ≠ c.b + dsGenOff := by
            have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh; omega
          have h2 : ∀ z < c.vCap, dsRevHeadBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) ≠
              dsSBitBase c.b c.L c.vCap c.eCap + z := fun z hz => by
            have hm := c.mul_vCap_add_lt hi hv_cap
            have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb; omega
          have h3 : ∀ z < c.eCap, dsRevHeadBase c.b c.L c.vCap c.eCap + (i * c.vCap + v) ≠
              dsEStampBase c.b c.L c.vCap c.eCap + z := fun z hz => by
            have hm := c.mul_vCap_add_lt hi hv_cap
            have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
            have := hlay.sb_lt_es; omega
          simpa [Nat.add_assoc] using hinv.read_lt_fix hrevh_lt_fix h1 h2 h3
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide : (21 : ℕ) ≠ 23), r21]))
            (Expr.eval_reg_of_eq (r := 23) (v := v) (by simp)) hrevh_w) hrevh_mem) ?_
        have hmid_props := midCandFold_props (revLists_i := c.revLists ⟨i, hiL1⟩)
          hnd0 hsub0 (fun u hu => (c.hm_rev ⟨i, hiL1⟩ hi u ((c.hs_mem u).mp hu)).2.2) k (Nat.le_of_lt hk)
        let stA : State :=
          { mem := st.mem
            regs := Function.update (Function.update st.regs 23 v) 24
              (c.mem0 (dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap + v))
            pos := st.pos }
        have hinvA : CandMemInv c (midCandFold c.G' (c.revLists ⟨i, hiL1⟩) cand0 c.sPrevList k) stA :=
          { regs := hinv.regs.agree (fun r hr h14 => by
              dsimp only [stA]
              rw [Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 23)])
            cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
            r14_eq := by
              dsimp only [stA]
              rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 24),
                Function.update_of_ne (by decide : (14 : ℕ) ≠ 23), hinv.r14_eq]
            cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame }
        have hr24A : stA.regs 24 = c.mem0 (dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap + v) := by
          dsimp only [stA]; rw [Function.update_self]
        rcases dsCollectCand_innerLoop_triple c (p := p) hmid_props.1 hmid_props.2.1
            (c.mem0 (dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap + v))
            (c.revLists ⟨i, hiL1⟩ v) hll_v hrev_spec.2.2 stA.regs stA ω
            ⟨hinvA, hr24A, fun _ _ _ _ => rfl⟩ with
          ⟨o', st', c', hr', hPost', hc'⟩
        cases o' with
        | returned _ => exact False.elim hPost'
        | normal =>
        rcases hPost' with ⟨hi', hreg'⟩
        refine ⟨.normal, st', c', hr', ?_, ?_⟩
        · have hagree : ∀ r ≤ 22, r ≠ 14 → st'.regs r = st.regs r := fun r hr h14 => by
            have h1 := hreg' r h14 (by omega) (by omega)
            dsimp only [stA] at h1
            rw [Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 23)] at h1
            exact h1
          refine ⟨?_, (hagree 22 (by omega) (by omega)).trans r22⟩
          dsimp only [InvM]
          rw [midCandFold_succ hk]
          exact ⟨{
            regs := hi'.regs.agree (fun r hr h14 => by
              dsimp only; rw [Function.update_of_ne (by omega : r ≠ 22), hagree r (by omega) h14])
            cand_nd := hi'.cand_nd, cand_sub := hi'.cand_sub
            r14_eq := by
              dsimp only; rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 22), hi'.r14_eq]
            cand_at := hi'.cand_at, eStamp_spec := hi'.eStamp_spec, frame := hi'.frame
          },
          by rw [Function.update_of_ne (by decide : (18 : ℕ) ≠ 22), hagree 18 (by omega) (by omega), r18],
          by rw [Function.update_of_ne (by decide : (19 : ℕ) ≠ 22), hagree 19 (by omega) (by omega), r19],
          by rw [Function.update_of_ne (by decide : (19 : ℕ) ≠ 22), hagree 19 (by omega) (by omega)]; exact h19,
          by rw [Function.update_of_ne (by decide : (20 : ℕ) ≠ 22), hagree 20 (by omega) (by omega), r20],
          by rw [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22), hagree 21 (by omega) (by omega), r21],
          by simp,
          fun r hr h14 => by
            rw [Function.update_of_ne (by omega : r ≠ 22), hagree r (by omega) h14, hfr r hr h14]⟩
        · dsimp only at hc'
          dsimp only [stepCost, Expr.size, v] at *
          rw [dite_eq_left_of_eq_true (eq_true hk)]
          omega
      · intro hrg_eq_z
        have hrg_ne : rg ≠ dg := fun h => by simp [h] at hrg_eq_z
        have hne_g : ¬ (0 < dg ∧ rg = dg) := fun h => hrg_ne h.2
        have hrl_empty : c.revLists ⟨i, hiL1⟩ v = [] := by
          have h2 := hrev_spec.2.1; simp only [hne_g] at h2; exact h2
        refine runs_nop_le (k := 8 + 7) ?_ (by dsimp only [stepCost, Expr.size]; omega)
        · simp only [normalPost]
          have hfold_eq : midCandFold c.G' (c.revLists ⟨i, hiL1⟩) cand0 c.sPrevList (k + 1) =
              midCandFold c.G' (c.revLists ⟨i, hiL1⟩) cand0 c.sPrevList k := by
            rw [midCandFold_succ hk, hrl_empty]; rfl
          dsimp only [InvM]
          refine ⟨?_, by simp [r22]⟩
          rw [hfold_eq]
          exact ⟨{
            regs := hinv.regs.agree (fun r hr _ => by
              simp [show r ≠ 22 by omega, show r ≠ 23 by omega])
            cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
            r14_eq := by simp [hinv.r14_eq]
            cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame
          },
          by simp [r18],
          by simp [r19, dg],
          by simp [h19],
          by simp [r20],
          by simp [r21],
          by simp,
          fun r hr h14 => by simp [show r ≠ 22 by omega, show r ≠ 23 by omega, hfr r hr h14]⟩)
  refine ht.conseq (fun st h => h)
    (fun o st' h => by
      cases o with
      | returned _ => exact h
      | normal => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
    fun st _ => ?_
  dsimp only [Expr.size]
  have hsum : rangeCost stepCost 0 c.sPrevList.length =
      60 * (c.sPrevList.map fun v => (c.revLists ⟨i, hiL1⟩ v).length).sum + 35 * c.sPrevList.length := by
    have hsplit : rangeCost stepCost 0 c.sPrevList.length =
        rangeCost (fun k => 60 * (if hk : k < c.sPrevList.length then
          (c.revLists ⟨i, hiL1⟩ c.sPrevList[k]).length else 0)) 0 c.sPrevList.length +
        rangeCost (fun _ => 35) 0 c.sPrevList.length :=
      rangeCost_add_const _ 35 c.sPrevList.length
    rw [hsplit, rangeCost_scale, rangeCost_const]
    have hmap : rangeCost (fun k => if hk : k < c.sPrevList.length then
          (c.revLists ⟨i, hiL1⟩ c.sPrevList[k]).length else 0) 0 c.sPrevList.length =
        (c.sPrevList.map fun v => (c.revLists ⟨i, hiL1⟩ v).length).sum :=
      rangeCost_zero_map_sum c.sPrevList (fun v => (c.revLists ⟨i, hiL1⟩ v).length)
    rw [hmap]; omega
  rw [hsum]; omega

/-! ## Outer loop (`forRange 18 0 r1`) -/

private lemma dsCollectCand_outerLoop_triple (c : CandCtx) {p : Program}
    (rInit : ℕ → ℕ) :
    Triple c.w p
      (fun st => CandMemInv c [] st ∧ ∀ r ≤ 17, r ≠ 14 → st.regs r = rInit r)
      (forRange 18 (.const 0) (.reg 1) dsCandOuterBody)
      (normalPost fun st =>
        CandMemInv c (outerCandFold c.L c.G' c.revLists c.sPrevList c.j) st ∧
        ∀ r ≤ 17, r ≠ 14 → st.regs r = rInit r)
      (fun _ =>
        60 * candRevSum c.L c.j c.revLists c.sPrevList +
          44 * (c.j * c.sPrevList.length) + 39 * c.j + 7) := by
  have hlay := c.lay
  have hw16 := c.hw16
  let stepCost : ℕ → ℕ := fun i =>
    60 * (if hi : i < c.L + 1 then (c.sPrevList.map fun v => (c.revLists ⟨i, hi⟩ v).length).sum else 0) +
      44 * c.sPrevList.length + 30
  let InvO : ℕ → State → Prop := fun i st =>
    CandMemInv c (outerCandFold c.L c.G' c.revLists c.sPrevList i) st ∧
    st.regs 18 = i ∧
    ∀ r ≤ 17, r ≠ 14 → st.regs r = rInit r
  have ht := Triple.forRange_le (w := c.w) (p := p)
    (P := fun st => CandMemInv c [] st ∧ ∀ r ≤ 17, r ≠ 14 → st.regs r = rInit r)
    (r := 18) (lo := .const 0) (hi := .reg 1)
    (body := dsCandOuterBody) (Inv := InvO) stepCost 0 c.j
    (Nat.zero_le _) (by have := c.hw16; omega)
    (fun _ => lt_of_le_of_lt c.hjL (Nat.lt_trans (Nat.lt_succ_self c.L) hlay.L1_w))
    (fun st ⟨hinv, hfr⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      dsimp only [InvO]
      exact ⟨{
        regs := hinv.regs.agree (fun r hr _ => by
          dsimp only; rw [Function.update_of_ne (by omega : r ≠ 18)])
        cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
        r14_eq := by
          dsimp only; rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 18), hinv.r14_eq]; rfl
        cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame
      },
      Function.update_self _ _ _,
      fun r hr h14 => by rw [Function.update_of_ne (by omega : r ≠ 18), hfr r hr h14]⟩)
    (fun i st _ _ hO => hO.2.1)
    (fun i st _ _ hO => by simp [Expr.eval, hO.1.regs.2.1])
    (fun i _ hi => by
      intro st ω ⟨hinv, r18, hfr⟩
      have hiL1 : i < c.L + 1 := by have := c.hjL; omega
      have hdg_lt_fix : dsDomGenBase c.b c.L c.vCap c.eCap + i <
          c.b + dsFixedSize c.L c.vCap c.eCap := by
        have := hlay.dom_lt_revg; have := hlay.revg_lt_revh; have := hlay.revh_lt_sg
        have := hlay.sg_lt_sh; have := hlay.sh_lt_sb; have := hlay.sb_lt_es
        have := hlay.es_lt_fix; omega
      have hdg_w : dsDomGenBase c.b c.L c.vCap c.eCap + i < 2 ^ c.w := by
        have := hlay.hp_lt_w; have := c.hfix; omega
      have hdg_mem : st.mem (dsDomGenBase c.b c.L c.vCap c.eCap + i) =
          c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i) := by
        have h1 : dsDomGenBase c.b c.L c.vCap c.eCap + i ≠ c.b + dsGenOff := by
          have := hlay.b_lt_dom; omega
        have h2 : ∀ z < c.vCap, dsDomGenBase c.b c.L c.vCap c.eCap + i ≠
            dsSBitBase c.b c.L c.vCap c.eCap + z := fun z hz => by
          have := hlay.dom_lt_revg; have := hlay.revg_lt_revh; have := hlay.revh_lt_sg
          have := hlay.sg_lt_sh; have := hlay.sh_lt_sb; omega
        have h3 : ∀ z < c.eCap, dsDomGenBase c.b c.L c.vCap c.eCap + i ≠
            dsEStampBase c.b c.L c.vCap c.eCap + z := fun z hz => by
          have := hlay.dom_lt_revg; have := hlay.revg_lt_revh; have := hlay.revh_lt_sg
          have := hlay.sg_lt_sh; have := hlay.sh_lt_sb; have := hlay.sb_lt_es; omega
        exact hinv.read_lt_fix hdg_lt_fix h1 h2 h3
      set dg := c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i)
      suffices hres : ∃ o st' c_1,
          Runs c.w p ω dsCandOuterBody st o st' c_1 ∧
            normalPost (fun st' =>
              InvO (i + 1) { st' with regs := Function.update st'.regs 18 (i + 1) } ∧ st'.regs 18 = i) o st' ∧
            0 + c_1 ≤ stepCost i by
        rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
        dsimp only
        exact ⟨o, st', c_1, hr, hq, by omega⟩
      dsimp only [dsCandOuterBody]
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hinv.regs.2.2.2.2.2.2.2.1)
          (Expr.eval_reg_of_eq r18) hdg_w) hdg_mem) ?_
      refine runs_cond_le (v := dg)
        (Expr.eval_reg_of_eq (r := 19) (v := dg) (by dsimp only; exact Function.update_self 19 dg st.regs)) ?_ ?_
      · intro hdg_nz
        have hdg_pos : 0 < dg := Nat.pos_of_ne_zero hdg_nz
        have hrevg_hi_w : dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap < 2 ^ c.w := by
          rcases Nat.eq_zero_or_pos c.vCap with hv0 | hv0
          · have hiz : i * c.vCap = 0 := by rw [hv0, Nat.mul_zero]
            rw [hiz, Nat.add_zero]; exact hlay.revg_w
          · have hm := c.mul_vCap_lt hi hv0
            have := hlay.revg_lt_revh; have := hlay.revh_lt_sg; have := hlay.sg_lt_sh
            have := hlay.sh_lt_sb; have := hlay.sb_lt_es; have := hlay.es_lt_fix
            have := hlay.hp_lt_w; have := c.hfix; omega
        have hrevh_hi_w : dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap < 2 ^ c.w := by
          rcases Nat.eq_zero_or_pos c.vCap with hv0 | hv0
          · have hiz : i * c.vCap = 0 := by rw [hv0, Nat.mul_zero]
            rw [hiz, Nat.add_zero]; exact hlay.revh_w
          · have hm := c.mul_vCap_lt hi hv0
            have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
            have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := hlay.hp_lt_w; have := c.hfix; omega
        have hiv_w : i * c.vCap < 2 ^ c.w := by
          rcases Nat.eq_zero_or_pos c.vCap with hv0 | hv0
          · have hiz : i * c.vCap = 0 := by rw [hv0, Nat.mul_zero]
            rw [hiz]; omega
          · have hm := c.mul_vCap_lt hi hv0; have := hlay.revg_lt_revh
            have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
            have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := hlay.hp_lt_w
            have := c.hfix; omega
        refine runs_seq_assign_le
          (Expr.eval_add (Expr.eval_reg_of_eq (by
            dsimp only; rw [Function.update_of_ne (by decide : (8 : ℕ) ≠ 19), hinv.regs.2.2.2.2.2.2.2.2.1]))
            (Expr.eval_mul (Expr.eval_reg_of_eq (by
              dsimp only; rw [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19), r18]))
              (Expr.eval_reg_of_eq (by
                dsimp only; rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 19), hinv.regs.2.2.2.1])) hiv_w)
            hrevg_hi_w) ?_
        refine runs_seq_assign_le
          (Expr.eval_add (Expr.eval_reg_of_eq (by
            dsimp only
            rw [Function.update_of_ne (by decide : (9 : ℕ) ≠ 20),
              Function.update_of_ne (by decide : (9 : ℕ) ≠ 19), hinv.regs.2.2.2.2.2.2.2.2.2.1]))
            (Expr.eval_mul (Expr.eval_reg_of_eq (by
              dsimp only
              rw [Function.update_of_ne (by decide : (18 : ℕ) ≠ 20),
                Function.update_of_ne (by decide : (18 : ℕ) ≠ 19), r18]))
              (Expr.eval_reg_of_eq (by
                dsimp only
                rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 20),
                  Function.update_of_ne (by decide : (3 : ℕ) ≠ 19), hinv.regs.2.2.2.1])) hiv_w)
            hrevh_hi_w) ?_
        let stM : State :=
          { mem := st.mem
            regs := Function.update (Function.update (Function.update st.regs 19 dg) 20
              (dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap)) 21
              (dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap)
            pos := st.pos }
        have hinvM : CandMemInv c (outerCandFold c.L c.G' c.revLists c.sPrevList i) stM :=
          { regs := hinv.regs.agree (fun r hr _ => by
              dsimp only [stM]
              rw [Function.update_of_ne (by omega : r ≠ 21),
                Function.update_of_ne (by omega : r ≠ 20),
                Function.update_of_ne (by omega : r ≠ 19)])
            cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
            r14_eq := by
              dsimp only [stM]
              rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 21),
                Function.update_of_ne (by decide : (14 : ℕ) ≠ 20),
                Function.update_of_ne (by decide : (14 : ℕ) ≠ 19), hinv.r14_eq]
            cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame }
        have hPreM : CandMemInv c (outerCandFold c.L c.G' c.revLists c.sPrevList i) stM ∧
            stM.regs 18 = i ∧ stM.regs 19 = dg ∧ 0 < stM.regs 19 ∧
            stM.regs 20 = dsRevGenBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
            stM.regs 21 = dsRevHeadBase c.b c.L c.vCap c.eCap + i * c.vCap ∧
            ∀ r ≤ 21, r ≠ 14 → stM.regs r = stM.regs r := by
          refine ⟨hinvM, ?_, ?_, ?_, ?_, ?_, fun _ _ _ => rfl⟩ <;> dsimp only [stM]
          · rw [Function.update_of_ne (by decide : (18 : ℕ) ≠ 21),
              Function.update_of_ne (by decide : (18 : ℕ) ≠ 20),
              Function.update_of_ne (by decide : (18 : ℕ) ≠ 19), r18]
          · rw [Function.update_of_ne (by decide : (19 : ℕ) ≠ 21),
              Function.update_of_ne (by decide : (19 : ℕ) ≠ 20), Function.update_self]
          · rw [Function.update_of_ne (by decide : (19 : ℕ) ≠ 21),
              Function.update_of_ne (by decide : (19 : ℕ) ≠ 20), Function.update_self]; exact hdg_pos
          · rw [Function.update_of_ne (by decide : (20 : ℕ) ≠ 21), Function.update_self]
          · rw [Function.update_self]
        rcases dsCollectCand_midLoop_triple c (p := p) hi (outerCandFold c.L c.G' c.revLists c.sPrevList i)
            hinv.cand_nd hinv.cand_sub stM.regs stM ω hPreM with
          ⟨o', st', c', hr', hPost', hc'⟩
        cases o' with
        | returned _ => exact False.elim hPost'
        | normal =>
        rcases hPost' with ⟨hi', r18', _, _, _, _, hfr'⟩
        refine ⟨.normal, st', c', hr', ?_, ?_⟩
        · have hagree : ∀ r ≤ 18, r ≠ 14 → st'.regs r = st.regs r := fun r hr h14 => by
            have h1 := hfr' r (by omega) h14
            dsimp only [stM] at h1
            rw [Function.update_of_ne (by omega : r ≠ 21),
              Function.update_of_ne (by omega : r ≠ 20),
              Function.update_of_ne (by omega : r ≠ 19)] at h1
            exact h1
          refine ⟨?_, r18'⟩
          dsimp only [InvO]
          rw [outerCandFold_succ hiL1]
          exact ⟨{
            regs := hi'.regs.agree (fun r hr h14 => by
              dsimp only; rw [Function.update_of_ne (by omega : r ≠ 18), hagree r (by omega) h14])
            cand_nd := hi'.cand_nd, cand_sub := hi'.cand_sub
            r14_eq := by dsimp only; rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 18), hi'.r14_eq]
            cand_at := hi'.cand_at, eStamp_spec := hi'.eStamp_spec, frame := hi'.frame
          },
          by simp,
          fun r hr h14 => by
            rw [Function.update_of_ne (by omega : r ≠ 18), hagree r (by omega) h14, hfr r hr h14]⟩
        · dsimp only at hc'
          dsimp only [stepCost, Expr.size] at *
          rw [dite_eq_left_of_eq_true (eq_true hiL1)]
          omega
      · intro hdg_z
        have hnot : ∀ v ∈ c.sPrevList, c.revLists ⟨i, hiL1⟩ v = [] := fun v hv => by
          have h2 := (c.hm_rev ⟨i, hiL1⟩ hi v ((c.hs_mem v).mp hv)).2.1
          split_ifs at h2 with hc
          · exfalso; dsimp only [dg] at hdg_z; dsimp only at hc; omega
          · exact h2
        refine runs_nop_le (k := 6 + 2) ?_ (by dsimp only [stepCost, Expr.size]; omega)
        · simp only [normalPost]
          dsimp only [InvO]
          rw [outerCandFold_succ hiL1, midCandFold_of_empty hnot _ (le_refl _)]
          refine ⟨⟨{
            regs := hinv.regs.agree (fun r hr _ => by
              dsimp only
              rw [Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 19)])
            cand_nd := hinv.cand_nd, cand_sub := hinv.cand_sub
            r14_eq := by
              dsimp only
              rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 18),
                Function.update_of_ne (by decide : (14 : ℕ) ≠ 19), hinv.r14_eq]
            cand_at := hinv.cand_at, eStamp_spec := hinv.eStamp_spec, frame := hinv.frame
          },
          by simp,
          fun r hr h14 => by
            rw [Function.update_of_ne (by omega : r ≠ 18),
              Function.update_of_ne (by omega : r ≠ 19), hfr r hr h14]⟩,
          by rw [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19), r18]⟩)
  refine ht.conseq (fun st h => h)
    (fun o st' h => by cases o with | returned _ => exact h | normal => exact ⟨h.1, h.2.2⟩)
    fun st _ => ?_
  dsimp only [Expr.size]
  have hsum : rangeCost stepCost 0 c.j =
      60 * candRevSum c.L c.j c.revLists c.sPrevList + (44 * c.sPrevList.length + 30) * c.j := by
    have hsplit : rangeCost stepCost 0 c.j =
        rangeCost (fun i => 60 * (if hi : i < c.L + 1 then
          (c.sPrevList.map fun v => (c.revLists ⟨i, hi⟩ v).length).sum else 0)) 0 c.j +
        rangeCost (fun _ => 44 * c.sPrevList.length + 30) 0 c.j :=
      rangeCost_add_const _ (44 * c.sPrevList.length + 30) c.j
    rw [hsplit, rangeCost_scale, rangeCost_zero_finset_sum, rangeCost_const]
    have hcand : (Finset.range c.j).sum (fun i => if hi : i < c.L + 1 then
          (c.sPrevList.map fun v => (c.revLists ⟨i, hi⟩ v).length).sum else 0) =
        candRevSum c.L c.j c.revLists c.sPrevList := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · simp
    rw [hcand, Nat.sub_zero, Nat.mul_comm c.j (44 * c.sPrevList.length + 30)]
  rw [hsum, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm c.sPrevList.length c.j]; omega

/-! ## Phase B and `dsCollectCand_meetsContract` -/

private lemma dsCollectCand_phaseB_triple (c : CandCtx) {p : Program}
    (memA : ℕ → ℕ)
    (hmA_len : memA c.heapPtr = c.sPrevList.length)
    (hmA_at : ListAt memA (c.heapPtr + 2) c.sPrevList)
    (hmA_sBit : ∀ v < c.vCap, memA (dsSBitBase c.b c.L c.vCap c.eCap + v) = if v ∈ c.S_prev then 1 else 0)
    (hmA_agree : ∀ addr, (∀ v < c.vCap, addr ≠ dsSBitBase c.b c.L c.vCap c.eCap + v) →
      (addr < c.heapPtr ∨ c.heapPtr + 2 + c.sPrevList.length ≤ addr) → memA addr = c.mem0 addr)
    (hmB0_eq : c.memB0 = Function.update memA (c.b + dsGenOff) c.gen1) :
    Triple c.w p
      (fun st => st.mem = memA ∧
        st.regs 0 = c.b ∧ st.regs 1 = c.j ∧ st.regs 2 = c.heapPtr ∧
        st.regs 3 = c.vCap ∧ st.regs 4 = c.eCap ∧ st.regs 5 = c.L ∧
        st.regs 6 = c.gen0 ∧
        st.regs 7 = dsDomGenBase c.b c.L c.vCap c.eCap ∧
        st.regs 8 = dsRevGenBase c.b c.L c.vCap c.eCap ∧
        st.regs 9 = dsRevHeadBase c.b c.L c.vCap c.eCap ∧
        st.regs 10 = dsSGenBase c.b c.L c.vCap c.eCap ∧
        st.regs 11 = dsSHeadBase c.b c.L c.vCap c.eCap ∧
        st.regs 12 = dsSBitBase c.b c.L c.vCap c.eCap ∧
        st.regs 13 = dsEStampBase c.b c.L c.vCap c.eCap ∧
        st.regs 14 = c.candBase ∧
        st.regs 15 = c.sPrevList.length)
      dsCandPhaseBStmt
      (fun o st' => ∃ cand,
        cand = outerCandFold c.L c.G' c.revLists c.sPrevList c.j ∧
        o = .returned (c.candBase + cand.length) ∧
        st'.mem c.heapPtr = c.sPrevList.length ∧
        st'.mem (c.heapPtr + 1) = cand.length ∧
        ListAt st'.mem (c.heapPtr + 2) c.sPrevList ∧
        ListAt st'.mem c.candBase cand ∧
        (∀ v < c.vCap, st'.mem (dsSBitBase c.b c.L c.vCap c.eCap + v) =
          if v ∈ c.S_prev then 1 else 0) ∧
        st'.mem (c.b + dsGenOff) = c.gen1 ∧
        (∀ e < c.eCap, st'.mem (dsEStampBase c.b c.L c.vCap c.eCap + e) ≤ c.gen1) ∧
        ∀ addr, dsCollectCandFrameCond c.L c.vCap c.eCap c.b c.heapPtr
            (c.candBase + cand.length) addr →
          st'.mem addr = c.mem0 addr)
      (fun _ =>
        60 * candRevSum c.L c.j c.revLists c.sPrevList +
          44 * (c.j * c.sPrevList.length) + 39 * c.j + 60) := by
  intro st ω hPre
  rcases hPre with ⟨hmem, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩
  have hlay := c.lay
  have hw16 := c.hw16
  have hgen1_lt : c.gen1 < 2 ^ c.w := c.hgen1_lt
  have hgen_addr : c.b + dsGenOff < 2 ^ c.w := by have := hlay.b_lt_dom; have := hlay.dom_w; omega
  have hep_w : dgEPresBase (dsGPtr c.b) c.vCap < 2 ^ c.w := by
    have := hlay.ep_lt_fix; have := c.hfix; have := hlay.hp_lt_w; omega
  have h7v_w : 7 * c.vCap < 2 ^ c.w := by have := hlay.ep_w; have := hlay.epres_eq; omega
  have hbh_w : c.b + (dsHdrSize + 4) < 2 ^ c.w := by have := hlay.ep_w; have := hlay.epres_eq; omega
  suffices hres : ∃ o st' c_1,
      Runs c.w p ω dsCandPhaseBStmt st o st' c_1 ∧
        (∃ cand,
          cand = outerCandFold c.L c.G' c.revLists c.sPrevList c.j ∧
          o = .returned (c.candBase + cand.length) ∧
          st'.mem c.heapPtr = c.sPrevList.length ∧
          st'.mem (c.heapPtr + 1) = cand.length ∧
          ListAt st'.mem (c.heapPtr + 2) c.sPrevList ∧
          ListAt st'.mem c.candBase cand ∧
          (∀ v < c.vCap, st'.mem (dsSBitBase c.b c.L c.vCap c.eCap + v) =
            if v ∈ c.S_prev then 1 else 0) ∧
          st'.mem (c.b + dsGenOff) = c.gen1 ∧
          (∀ e < c.eCap, st'.mem (dsEStampBase c.b c.L c.vCap c.eCap + e) ≤ c.gen1) ∧
          ∀ addr, dsCollectCandFrameCond c.L c.vCap c.eCap c.b c.heapPtr
              (c.candBase + cand.length) addr →
            st'.mem addr = c.mem0 addr) ∧
        0 + c_1 ≤ 60 * candRevSum c.L c.j c.revLists c.sPrevList +
            44 * (c.j * c.sPrevList.length) + 39 * c.j + 60 by
    rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
    dsimp only
    exact ⟨o, st', c_1, hr, hq, by omega⟩
  have hdg_lt16 : dsGenOff < 16 := by decide
  have hhd_lt_ep : dsHdrSize + 4 ≤ c.b + (dsHdrSize + 4) + 7 * c.vCap := by omega
  dsimp only [dsCandPhaseBStmt]
  refine runs_seq_assign_le (v := c.gen1)
    (Expr.eval_add (Expr.eval_reg_of_eq r6) (Expr.eval_const (by omega)) hgen1_lt) ?_
  refine runs_seq_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 6), r0]))
      (Expr.eval_const (by omega)) hgen_addr)
    (Expr.eval_reg_of_eq (r := 6) (v := c.gen1) (by dsimp only; exact Function.update_self 6 c.gen1 st.regs)) ?_
  refine runs_seq_assign_le (v := c.candBase)
    (Expr.eval_reg_of_eq (r := 14) (v := c.candBase)
      (by dsimp only; rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 6), r14])) ?_
  refine runs_seq_assign_le (v := dgEPresBase (dsGPtr c.b) c.vCap)
    (by
      rw [← hlay.epres_eq]
      refine Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by
            dsimp only; rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 16),
              Function.update_of_ne (by decide : (0 : ℕ) ≠ 6), r0]))
          (Expr.eval_const (by have := hlay.ep_w; have := hlay.epres_eq; omega))
          hbh_w)
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (by
            dsimp only; rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 16),
              Function.update_of_ne (by decide : (3 : ℕ) ≠ 6), r3])) h7v_w)
        hep_w) ?_
  let stB0 : State :=
    { mem := Function.update st.mem (c.b + dsGenOff) c.gen1
      regs := Function.update (Function.update (Function.update st.regs 6 c.gen1) 16 c.candBase)
        17 (dgEPresBase (dsGPtr c.b) c.vCap)
      pos := st.pos }
  have hst_mem_eq : Function.update st.mem (c.b + dsGenOff) c.gen1 = c.memB0 := by
    rw [hmem, hmB0_eq]
  have hinvB0 : CandMemInv c [] stB0 := {
    regs := ⟨
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 17), Function.update_of_ne (by decide : (0 : ℕ) ≠ 16), Function.update_of_ne (by decide : (0 : ℕ) ≠ 6), r0],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (1 : ℕ) ≠ 17), Function.update_of_ne (by decide : (1 : ℕ) ≠ 16), Function.update_of_ne (by decide : (1 : ℕ) ≠ 6), r1],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (2 : ℕ) ≠ 17), Function.update_of_ne (by decide : (2 : ℕ) ≠ 16), Function.update_of_ne (by decide : (2 : ℕ) ≠ 6), r2],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 17), Function.update_of_ne (by decide : (3 : ℕ) ≠ 16), Function.update_of_ne (by decide : (3 : ℕ) ≠ 6), r3],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (4 : ℕ) ≠ 17), Function.update_of_ne (by decide : (4 : ℕ) ≠ 16), Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), r4],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (5 : ℕ) ≠ 17), Function.update_of_ne (by decide : (5 : ℕ) ≠ 16), Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), r5],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (6 : ℕ) ≠ 17), Function.update_of_ne (by decide : (6 : ℕ) ≠ 16), Function.update_self],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (7 : ℕ) ≠ 17), Function.update_of_ne (by decide : (7 : ℕ) ≠ 16), Function.update_of_ne (by decide : (7 : ℕ) ≠ 6), r7],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (8 : ℕ) ≠ 17), Function.update_of_ne (by decide : (8 : ℕ) ≠ 16), Function.update_of_ne (by decide : (8 : ℕ) ≠ 6), r8],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (9 : ℕ) ≠ 17), Function.update_of_ne (by decide : (9 : ℕ) ≠ 16), Function.update_of_ne (by decide : (9 : ℕ) ≠ 6), r9],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (10 : ℕ) ≠ 17), Function.update_of_ne (by decide : (10 : ℕ) ≠ 16), Function.update_of_ne (by decide : (10 : ℕ) ≠ 6), r10],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (11 : ℕ) ≠ 17), Function.update_of_ne (by decide : (11 : ℕ) ≠ 16), Function.update_of_ne (by decide : (11 : ℕ) ≠ 6), r11],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (12 : ℕ) ≠ 17), Function.update_of_ne (by decide : (12 : ℕ) ≠ 16), Function.update_of_ne (by decide : (12 : ℕ) ≠ 6), r12],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (13 : ℕ) ≠ 17), Function.update_of_ne (by decide : (13 : ℕ) ≠ 16), Function.update_of_ne (by decide : (13 : ℕ) ≠ 6), r13],
      by dsimp only [stB0]; rw [Function.update_of_ne (by decide : (15 : ℕ) ≠ 17), Function.update_of_ne (by decide : (15 : ℕ) ≠ 16), Function.update_of_ne (by decide : (15 : ℕ) ≠ 6), r15],
      by dsimp only [stB0, CandCtx.candBase]; rw [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17), Function.update_self],
      by dsimp only [stB0]; rw [Function.update_self]⟩
    cand_nd := List.nodup_nil
    cand_sub := fun _ hx => by cases hx
    r14_eq := by
      dsimp only [stB0]
      rw [Function.update_of_ne (by decide : (14 : ℕ) ≠ 17),
        Function.update_of_ne (by decide : (14 : ℕ) ≠ 16),
        Function.update_of_ne (by decide : (14 : ℕ) ≠ 6), r14]; rfl
    cand_at := fun _ hk => by cases hk
    eStamp_spec := fun e he =>
      ⟨(fun hn => by cases hn),
       (fun _ => by dsimp only [stB0]; rw [congrFun hst_mem_eq _]; exact c.hm_eStamp0 e he)⟩
    frame := fun addr _ _ => by dsimp only [stB0]; exact congrFun hst_mem_eq addr
  }
  refine runs_seq_triple_le (dsCollectCand_outerLoop_triple c stB0.regs) ⟨(by exact hinvB0), fun _ _ _ => rfl⟩ ?_
  rintro stO ⟨hinvO, hfrO⟩
  set cand := outerCandFold c.L c.G' c.revLists c.sPrevList c.j
  have hcand_len_le : cand.length ≤ c.eCap := by
    have hp := outerCandFold_props (G' := c.G') c.hjL c.hs_mem
      (fun i hi v hv => (c.hm_rev i hi v hv).2.2) c.j (le_refl _)
    exact list_length_le_of_nodup_lt hp.1 fun x hx => (hp.2.1 x hx).2
  have hhp1_lt : c.heapPtr + 1 < 2 ^ c.w := by have := c.hh_lt; omega
  have hclen_lt : cand.length < 2 ^ c.w := by have := hlay.eCap_w; omega
  have hret_lt : c.candBase + cand.length < 2 ^ c.w := by
    have := c.hh_lt; have := c.sPrev_len_le; dsimp only [CandCtx.candBase]; omega
  have hr14_sub : c.candBase + cand.length - c.candBase = cand.length := by omega
  have hr16O : stO.regs 16 = c.candBase := by
    rw [hfrO 16 (by omega) (by omega)]; dsimp only [stB0]
    rw [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17), Function.update_self]
  refine runs_seq_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq hinvO.regs.2.2.1) (Expr.eval_const (by omega)) hhp1_lt)
    (by
      have hev := Expr.eval_sub (Expr.eval_reg_of_eq hinvO.r14_eq) (Expr.eval_reg_of_eq hr16O) hret_lt
      simpa [hr14_sub] using hev) ?_
  refine runs_ret_le (Expr.eval_reg_of_eq hinvO.r14_eq) ?_ ?_
  · refine ⟨cand, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [Function.update_of_ne (by omega)]
      have hes : ∀ e < c.eCap, c.heapPtr ≠ dsEStampBase c.b c.L c.vCap c.eCap + e := fun e he => by
        have := hlay.es_lt_fix; have := c.hfix; omega
      have hcb : c.heapPtr < c.candBase := by dsimp only [CandCtx.candBase]; omega
      rw [hinvO.frame _ hes (Or.inl hcb), hmB0_eq, Function.update_of_ne (by
        have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh
        have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
        have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := c.hfix; omega), hmA_len]
    · dsimp only; exact Function.update_self _ _ _
    · intro k hk
      dsimp only
      rw [Function.update_of_ne (by omega)]
      have hes : ∀ e < c.eCap, c.heapPtr + 2 + k ≠ dsEStampBase c.b c.L c.vCap c.eCap + e :=
        fun e he => by have := hlay.es_lt_fix; have := c.hfix; omega
      have hcb : c.heapPtr + 2 + k < c.candBase := by dsimp only [CandCtx.candBase]; omega
      rw [hinvO.frame _ hes (Or.inl hcb), hmB0_eq, Function.update_of_ne (by
        have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh
        have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
        have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := c.hfix; omega)]
      exact hmA_at k hk
    · intro k hk
      dsimp only
      rw [Function.update_of_ne (by dsimp only [CandCtx.candBase]; omega)]
      exact hinvO.cand_at k hk
    · intro v hv
      dsimp only
      have hne1 : dsSBitBase c.b c.L c.vCap c.eCap + v ≠ c.heapPtr + 1 := by
        have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := c.hfix; omega
      have hne2 : ∀ e < c.eCap, dsSBitBase c.b c.L c.vCap c.eCap + v ≠
          dsEStampBase c.b c.L c.vCap c.eCap + e := fun e he => by
        have := hlay.sb_lt_es; omega
      have hcb : dsSBitBase c.b c.L c.vCap c.eCap + v < c.candBase := by
        have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := c.hfix
        dsimp only [CandCtx.candBase]; omega
      rw [Function.update_of_ne hne1, hinvO.frame _ hne2 (Or.inl hcb), hmB0_eq,
        Function.update_of_ne (by
          have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh
          have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb; omega)]
      exact hmA_sBit v hv
    · dsimp only
      have hne1 : c.b + dsGenOff ≠ c.heapPtr + 1 := by
        have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh
        have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
        have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := c.hfix; omega
      have hne2 : ∀ e < c.eCap, c.b + dsGenOff ≠ dsEStampBase c.b c.L c.vCap c.eCap + e :=
        fun e he => by
          have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh
          have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
          have := hlay.sb_lt_es; omega
      have hcb : c.b + dsGenOff < c.candBase := by
        have := hlay.b_lt_dom; have := hlay.dom_lt_revg; have := hlay.revg_lt_revh
        have := hlay.revh_lt_sg; have := hlay.sg_lt_sh; have := hlay.sh_lt_sb
        have := hlay.sb_lt_es; have := hlay.es_lt_fix; have := c.hfix
        dsimp only [CandCtx.candBase]; omega
      rw [Function.update_of_ne hne1, hinvO.frame _ hne2 (Or.inl hcb), hmB0_eq, Function.update_self]
    · intro e he
      dsimp only
      have hne1 : dsEStampBase c.b c.L c.vCap c.eCap + e ≠ c.heapPtr + 1 := by
        have := hlay.es_lt_fix; have := c.hfix; omega
      rw [Function.update_of_ne hne1]
      by_cases heC : e ∈ cand
      · rw [(hinvO.eStamp_spec e he).1 heC]
      · have hle := (hinvO.eStamp_spec e he).2 heC
        dsimp only [CandCtx.gen0, CandCtx.gen1] at hle ⊢; omega
    · intro addr ⟨hgen, hsb, hes, hrange⟩
      dsimp only
      have hne1 : addr ≠ c.heapPtr + 1 := by dsimp only [CandCtx.candBase] at hrange; omega
      have hmem_o := hinvO.frame addr hes (hrange.elim
        (fun h => Or.inl (by dsimp only [CandCtx.candBase]; omega))
        (fun h => Or.inr (by dsimp only [CandCtx.candBase]; exact h)))
      rw [Function.update_of_ne hne1, hmem_o, hmB0_eq, Function.update_of_ne hgen]
      refine hmA_agree addr hsb ?_
      exact hrange.elim (fun h => Or.inl h) (fun h => Or.inr (by dsimp only [CandCtx.candBase] at h; omega))
  · dsimp only [Expr.size]; omega

theorem dsCollectCand_meetsContract (w L vCap eCap b j : ℕ) (G' : MGraph)
    (S_prev : Finset ℕ) (sPrevList : List ℕ)
    (revLists : Fin (L + 1) → ℕ → List ℕ) (footS footRev : ℕ → Prop)
    {p : Program} {bOps bAff : ℕ}
    (hpAff : p.HasAt bAff (affectedProcs bOps)) :
    MeetsContract w p (bAff + affIdxCollectCand)
      (dsCollectCandContract w L vCap eCap b j G' S_prev sPrevList revLists footS footRev) := by
  refine meetsContract_of_runs
    (hpAff.get (i := affIdxCollectCand) (by simp [affectedProcs, affIdxCollectCand]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨heapPtr, rfl, hw16, h1j, hjL, hfix, hh_lt, hmL, hmV, hmE, hgen_pos, hgen1_lt,
    hDG, hG_val, hG_E, hfootS, hfootRev, hS_cap, hs_nd, hs_mem, hsg_pos, hsg_le, hllS,
    hsBit0, heStamp0, hdomGen0, hm_rev⟩
  simp only [affectedProcs, affIdxCollectCand]
  have hr0 : (startState [b, j, heapPtr] mem pos).regs 0 = b := rfl
  have hr1 : (startState [b, j, heapPtr] mem pos).regs 1 = j := rfl
  have hr2 : (startState [b, j, heapPtr] mem pos).regs 2 = heapPtr := rfl
  have hmem0 : (startState [b, j, heapPtr] mem pos).mem = mem := rfl
  have lay := dsCandLayout_mk hfix hh_lt
  have hsg_lt : mem (dsSGenBase b L vCap eCap + (j - 1)) < 2 ^ w := by
    have := hgen1_lt; omega
  have hgen0_lt : mem (b + dsGenOff) < 2 ^ w := by omega
  have hs_len_le : sPrevList.length ≤ vCap :=
    list_length_le_of_nodup_lt hs_nd fun v hv => hS_cap v ((hs_mem v).mp hv)
  have hBases := dsCollectCand_bases_triple (j := j) (p := p) mem hw16 hfix hh_lt hmL hmV hmE hgen0_lt
  have hPhaseA := dsCollectCand_phaseA_triple (p := p) mem S_prev sPrevList footS hw16 h1j hjL hfix hh_lt
    hfootS hS_cap hs_nd hs_mem hsg_pos hsg_lt hllS hsBit0
  suffices hres : ∃ o st' c',
      Runs w p ω dsCollectCandStmt (startState [b, j, heapPtr] mem pos) o st' c' ∧
        (dsCollectCandContract w L vCap eCap b j G' S_prev sPrevList revLists footS footRev).post
          [b, j, heapPtr] mem o.value st'.mem ∧
        0 + c' ≤
          (dsCollectCandContract w L vCap eCap b j G' S_prev sPrevList revLists footS footRev).cost
            [b, j, heapPtr] mem by
    rcases hres with ⟨o, st', c', hr', hp', hc'⟩
    exact ⟨o, st', c', hr', hp', by omega⟩
  rw [dsCollectCandStmt_eq]
  refine runs_seqAppend_triple_le hBases ⟨hmem0, hr0, hr1, hr2⟩ ?_
  intro st₁ hQ1
  refine runs_seqAppend_triple_le hPhaseA hQ1 ?_
  intro st₂ ⟨r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂, r11₂, r12₂, r13₂, r14₂, r15₂,
      hm2_len, hm2_at, hm2_sBit, hm2_agree⟩
  let memB0 := Function.update st₂.mem (b + dsGenOff) (mem (b + dsGenOff) + 1)
  have hm_eStampB : ∀ e < eCap, memB0 (dsEStampBase b L vCap eCap + e) ≤ mem (b + dsGenOff) := by
    intro e he
    have hne_g : dsEStampBase b L vCap eCap + e ≠ b + dsGenOff := by
      have := lay.b_lt_dom; have := lay.dom_lt_revg; have := lay.revg_lt_revh
      have := lay.revh_lt_sg; have := lay.sg_lt_sh; have := lay.sh_lt_sb
      have := lay.sb_lt_es; omega
    have hne_sb : ∀ v < vCap, dsEStampBase b L vCap eCap + e ≠ dsSBitBase b L vCap eCap + v :=
      fun v hv => by have := lay.sb_lt_es; omega
    have hlt_hp : dsEStampBase b L vCap eCap + e < heapPtr := by
      have := lay.es_lt_fix; omega
    dsimp only [memB0]
    rw [Function.update_of_ne hne_g, hm2_agree _ hne_sb (Or.inl hlt_hp)]
    exact heStamp0 e he
  let c : CandCtx := {
    w := w, L := L, vCap := vCap, eCap := eCap, b := b, j := j, heapPtr := heapPtr
    G' := G', S_prev := S_prev, sPrevList := sPrevList, revLists := revLists
    footRev := footRev, mem0 := mem, memB0 := memB0
    hw16 := hw16, h1j := h1j, hjL := hjL, hfix := hfix, hh_lt := hh_lt
    hG_E := hG_E
    hepres := hDG.2.2.2.2.2.2.2.2.2.2.2.1
    hfootRev := hfootRev, hS_cap := hS_cap, hs_nd := hs_nd, hs_mem := hs_mem
    hgen_pos := hgen_pos, hgen1_lt := hgen1_lt
    hm_sPrev_len := by
      dsimp only [memB0]
      rw [Function.update_of_ne (by
        have := lay.b_lt_dom; have := lay.dom_lt_revg; have := lay.revg_lt_revh
        have := lay.revh_lt_sg; have := lay.sg_lt_sh; have := lay.sh_lt_sb
        have := lay.sb_lt_es; have := lay.es_lt_fix; omega), hm2_len]
    hm_sPrev_at := fun k hk => by
      dsimp only [memB0]
      rw [Function.update_of_ne (by
        have := lay.b_lt_dom; have := lay.dom_lt_revg; have := lay.revg_lt_revh
        have := lay.revh_lt_sg; have := lay.sg_lt_sh; have := lay.sh_lt_sb
        have := lay.sb_lt_es; have := lay.es_lt_fix; omega)]
      exact hm2_at k hk
    hm_sBit := fun v hv => by
      dsimp only [memB0]
      rw [Function.update_of_ne (by
        have := lay.b_lt_dom; have := lay.dom_lt_revg; have := lay.revg_lt_revh
        have := lay.revh_lt_sg; have := lay.sg_lt_sh; have := lay.sh_lt_sb; omega)]
      exact hm2_sBit v hv
    hm_gen := by dsimp only [memB0]; exact Function.update_self _ _ _
    hm_eStamp0 := hm_eStampB
    hm_domGen0 := hdomGen0, hm_rev := hm_rev
    hm_agree := fun addr hgen hsb hrange => by
      dsimp only [memB0]
      rw [Function.update_of_ne hgen, hm2_agree addr hsb hrange]
  }
  have hr14_c : st₂.regs 14 = c.candBase := r14₂
  rcases dsCollectCand_phaseB_triple c (p := p) st₂.mem hm2_len hm2_at hm2_sBit hm2_agree rfl st₂ ω
      ⟨rfl, r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂, r11₂, r12₂, r13₂, hr14_c, r15₂⟩
    with ⟨o', st', c', hr', ⟨cand, hcand_eq, rfl, hm_len, hm_clen, hm_sPrev, hm_cand, hm_sb,
      hm_gen, hm_es, hm_frame⟩, hc'⟩
  have hp := outerCandFold_props (G' := G') hjL hs_mem (fun i hi v hv => (hm_rev i hi v hv).2.2) j (le_refl _)
  rw [← hcand_eq] at hp
  have hc_len : cand.length ≤ eCap :=
    list_length_le_of_nodup_lt hp.1 fun x hx => (hp.2.1 x hx).2
  refine ⟨.returned (c.candBase + cand.length), st', c', hr', ?_, ?_⟩
  · refine ⟨heapPtr, cand, rfl, hp.1, rfl,
      by dsimp only [Outcome.value, CandCtx.candBase, c] at *; omega,
      hm_len, hm_clen, hm_sPrev, hm_cand, hm_sb, hp.2.2, fun e he => (hp.2.1 e he).2,
      hm_gen, hm_es, hm_frame⟩
  · dsimp only [dsCollectCandContract, c] at hc' ⊢
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at hc' ⊢
    omega

end

end MinCostFlow.DynSpanner.Program
