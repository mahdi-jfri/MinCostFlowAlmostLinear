module

public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# `RemoveFake` Midpoint Flags, Parameter Computation, and Output Extraction

Verifies Stages 4, 5, and 8 of the `RemoveFake` Word-RAM procedure:
1. `rfBuildInB_triple`: writes the midpoint indicator `B = Finset.Ico k (k + mF)` at `rfInBAddr`.
2. `rfComputeH_triple`: computes `⌊log₂(2 * mJ + 1)⌋` and `H_param = rfHParam mH mF rhoNum rhoDen`.
3. `rfExtractR_triple`: maps kept local vertices back to original vertex IDs at `outRAddr`,
   returning `|R|`, together with `filterVertsByMem_nodup` and `filterVertsByMem_toFinset`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Stage 4: writes `inB[0..k-1] := 0`, `inB[k..k+mF-1] := 1`. -/
theorem rfBuildInB_triple {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (st₀ : State)
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr)
    (hregs : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st₀)
    (hmem : st₀.mem = mem) :
    let inBAddr := rfInBAddr workAddr mH mF
    Triple w p (fun st => st = st₀) rfBuildInBStmt
      (normalPost fun st' =>
        RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st' ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem inBAddr (inBAddr + (k + mF)) ∧
        (∀ b, b ∈ Finset.Ico k (k + mF) ↔ b < k + mF ∧ st'.mem (inBAddr + b) ≠ 0))
      (fun _ => 25 * (k + mF) + 30) := by
  intro inBAddr
  obtain ⟨hws, hval⟩ := rfWorkSpace_word_lt hw
  have hw2 : 1 < 2 ^ w := by omega
  have hinB_lt : inBAddr + (k + mF) < 2 ^ w := by
    dsimp only [inBAddr, rfInBAddr]; omega
  let Inv1 : ℕ → State → Prop := fun i st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.regs rfI = i ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem inBAddr (inBAddr + (k + mF)) ∧
    (∀ j < i, st.mem (inBAddr + j) = 0)
  let Inv2 : ℕ → State → Prop := fun i st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.regs rfI = i ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem inBAddr (inBAddr + (k + mF)) ∧
    (∀ j < k, st.mem (inBAddr + j) = 0) ∧
    (∀ j < i, st.mem (inBAddr + k + j) = 1)
  have hloop1 := Triple.forRange_const (w := w) (p := p) (r := rfI) (lo := .const 0) (hi := .reg rfK)
    (body := .store (.bin .add (.reg rfInB) (.reg rfI)) (.const 0))
    (P := fun st => st = st₀) (Inv := Inv1) 10 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), rfRegs_update_ge (by decide) hregs, by simp, rfl,
        hmem ▸ memFrame_refl mem _ _, fun j hj => by omega⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hfr, h0⟩
      refine runs_start_le (runs_store_le (x := inBAddr + i) (v := 0)
        (Expr.eval_add (Expr.eval_reg_of_eq hr.r_inB) (Expr.eval_reg_of_eq hi) (by omega))
        (Expr.eval_const (by omega)) ?_ (by simp [Expr.size]))
      refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide) (rfRegs_update_mem hr), by simp, hpos,
        memFrame_trans hfr (memFrame_update (by omega) (by omega)), ?_⟩, hi⟩
      intro j hj
      dsimp only
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne (by omega)]; exact h0 j (by omega))
  have hloop2 := Triple.forRange_const (w := w) (p := p) (r := rfI) (lo := .const 0) (hi := .reg rfMF)
    (body := .store (.bin .add (.bin .add (.reg rfInB) (.reg rfK)) (.reg rfI)) (.const 1))
    (P := fun st => Inv1 k st) (Inv := Inv2) 12 0 mF (Nat.zero_le mF) hw2 (fun _ => by omega)
    (fun st ⟨hr, _, hpos, hfr, h0⟩ =>
      ⟨Expr.eval_const (by omega), rfRegs_update_ge (by decide) hr, by simp, hpos, hfr, h0,
       fun j hj => by omega⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_mF)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hfr, h0, h1⟩
      refine runs_start_le (runs_store_le (x := inBAddr + k + i) (v := 1)
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_inB) (Expr.eval_reg_of_eq hr.r_k) (by omega))
          (Expr.eval_reg_of_eq hi) (by omega))
        (Expr.eval_const hw2) ?_ (by simp [Expr.size]))
      refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide) (rfRegs_update_mem hr), by simp, hpos,
        memFrame_trans hfr (memFrame_update (by omega) (by omega)),
        fun j hj => by dsimp only; rw [Function.update_of_ne (by omega)]; exact h0 j hj, ?_⟩, hi⟩
      intro j hj
      dsimp only
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne (by omega)]; exact h1 j (by omega))
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [rfBuildInBStmt, seqStmts]
  refine runs_seq_triple_le hloop1 rfl ?_
  intro st1 h1
  refine runs_triple_le hloop2 h1 ?_ ?_
  · rintro (_ | _) st2 hq2
    · rcases hq2 with ⟨hr2, _, hpos2, hfr2, h0, h1'⟩
      refine ⟨hr2, hpos2, hfr2, fun b => ?_⟩
      simp only [Finset.mem_Ico]
      constructor
      · rintro ⟨hkb, hblt⟩
        refine ⟨hblt, ?_⟩
        have hb1 := h1' (b - k) (by omega)
        rw [show inBAddr + b = inBAddr + k + (b - k) by omega, hb1]
        exact one_ne_zero
      · rintro ⟨hblt, hne⟩
        refine ⟨?_, hblt⟩
        by_contra hlt
        exact hne (h0 b (by omega))
    · exact False.elim hq2
  · simp [Expr.size]; omega

/-- Stage 5: computes `rfHParamReg = rfHParam mH mF rhoNum rhoDen`. -/
theorem rfComputeH_triple {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (p : Program) (st₀ : State)
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr)
    (hregs : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st₀) :
    Triple w p (fun st => st = st₀) rfComputeHStmt
      (normalPost fun st' =>
        RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st' ∧
        st'.regs rfHParamReg = rfHParam mH mF rhoNum rhoDen ∧
        st'.mem = st₀.mem ∧ st'.pos = st₀.pos)
      (fun _ => 20 * Nat.log 2 (2 * (mH + 2 * mF) + 1) + 45) := by
  obtain ⟨_, hval⟩ := rfWorkSpace_word_lt hw
  set N0 := 2 * (mH + 2 * mF) + 1
  set L0 := Nat.log 2 N0
  have hN0_lt : N0 < 2 ^ w := by omega
  have hL0_le : L0 + 1 ≤ rfHParam mH mF rhoNum rhoDen := by
    unfold rfHParam
    have hq : 0 ≤ (12 * rhoDen + rhoNum - 1) / rhoNum := Nat.zero_le _
    have h4c : 1 ≤ 4 * rfCcap rhoNum rhoDen := by unfold rfCcap; omega
    nlinarith
  let Inv : State → Prop := fun st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.mem = st₀.mem ∧ st.pos = st₀.pos ∧
    1 ≤ st.regs rfTmp1 ∧ st.regs rfTmp1 ≤ N0 ∧
    Nat.log 2 (st.regs rfTmp1) + st.regs rfTmp2 = L0
  have hloop := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .lt (.const 1) (.reg rfTmp1))
    (body := seqStmts
      [ .assign rfTmp1 (.bin .div (.reg rfTmp1) (.const 2))
      , .assign rfTmp2 (.bin .add (.reg rfTmp2) (.const 1)) ])
    (Inv := Inv) (Q := fun st => Inv st ∧ st.regs rfTmp1 = 1)
    (fun st => Nat.log 2 (st.regs rfTmp1))
    (fun st => if 1 < st.regs rfTmp1 then 1 else 0) 15
    (fun st hInv =>
      Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq rfl) (by omega))
    (fun st hInv h0 => by
      have hle1 : st.regs rfTmp1 ≤ 1 := by
        by_contra hgt
        have hlt : 1 < st.regs rfTmp1 := by omega
        simp [hlt] at h0
      exact ⟨hInv, by have := hInv.2.2.2.1; omega⟩)
    (fun st hInv hne => by
      have hgt1 : 1 < st.regs rfTmp1 := by
        by_contra hle
        simp [hle] at hne
      rcases hInv with ⟨hr, hm, hp, h1, hleN, hlog⟩
      have hlog_step : Nat.log 2 (st.regs rfTmp1) = Nat.log 2 (st.regs rfTmp1 / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by decide) (by omega)
      have hdiv_lt : st.regs rfTmp1 / 2 < 2 ^ w :=
        lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      intro s ω hs
      subst hs
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := s.regs rfTmp1 / 2)
        (Expr.eval_div (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_assign_le (v := s.regs rfTmp2 + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega)) ?_
        (by simp [Expr.size])
      refine ⟨⟨rfRegs_update_ge (by decide) (rfRegs_update_ge (by decide) hr), hm, hp,
        by simp; omega, by simp; exact le_trans (Nat.div_le_self _ _) hleN, ?_⟩, ?_⟩
      · simp only [Function.update_self, Function.update_of_ne (by decide : (21 : ℕ) ≠ 22)]
        omega
      · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22), Function.update_self]
        omega)
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [rfComputeHStmt, seqStmts]
  refine runs_seq_assign_le (v := N0)
    (Expr.eval_add
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hregs.r_mJ) (by omega))
      (Expr.eval_const (by omega)) hN0_lt) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop
    ⟨rfRegs_update_ge (by decide) (rfRegs_update_ge (by decide) hregs), rfl, rfl,
     by simp [N0], by simp [N0], by simp [N0, L0]⟩ ?_
  intro st1 ⟨⟨hr1, hm1, hp1, _, _, hlog1⟩, h1eq⟩
  have hacc : st1.regs rfTmp2 = L0 := by
    rw [h1eq] at hlog1
    simp at hlog1
    exact hlog1
  have h4c_lt : 4 * rfCcap rhoNum rhoDen < 2 ^ w := by omega
  have hH_lt : rfHParam mH mF rhoNum rhoDen < 2 ^ w := by omega
  have hprod_lt : 4 * rfCcap rhoNum rhoDen * (L0 + 1) < 2 ^ w := by
    dsimp only [L0, N0]
    unfold rfHParam at hH_lt
    omega
  have hL01_lt : L0 + 1 < 2 ^ w := by omega
  refine runs_assign_le (v := rfHParam mH mF rhoNum rhoDen)
    (Expr.eval_add
      (Expr.eval_mul
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr1.r_ccap) h4c_lt)
        (Expr.eval_add (Expr.eval_reg_of_eq hacc) (Expr.eval_const (by omega)) hL01_lt)
        hprod_lt)
      (Expr.eval_const (by omega)) hH_lt) ?_ ?_
  · exact ⟨rfRegs_update_ge (by decide) hr1, by simp, hm1, hp1⟩
  · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22), Function.update_self, Expr.size]
    dsimp only [L0, N0]
    omega

/-- Stage 8: maps kept local vertices `outRLoc[i] ≠ 0` back to `verts[i]` at `outRAddr`,
returning `|R|`. -/
theorem rfExtractR_triple {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (st₀ : State)
    (hvlen : verts.length = k)
    (hlist : ListAt mem vertsAddr verts)
    (hdisj_ov : DisjointRange outRAddr k vertsAddr k)
    (hdisj_ow : DisjointRange outRAddr k (rfOutRLocAddr workAddr k mH mF) k)
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr)
    (hregs : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st₀)
    (hmem : st₀.mem = mem) :
    let outRLocAddr := rfOutRLocAddr workAddr k mH mF
    let R_list := filterVertsByMem mem outRLocAddr verts
    Triple w p (fun st => st = st₀) rfExtractRStmt
      (fun o st' =>
        o = .returned R_list.length ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem outRAddr (outRAddr + k) ∧
        ListAt st'.mem outRAddr R_list)
      (fun _ => 50 * k + 35) := by
  intro outRLocAddr R_list
  obtain ⟨hws, hval⟩ := rfWorkSpace_word_lt hw
  have hw2 : 1 < 2 ^ w := by omega
  have hvk_w := hw.1
  have houtR_w := hw.2.2.2.2.2.1
  have houtLoc_w : outRLocAddr + k < 2 ^ w := by
    dsimp only [outRLocAddr, rfOutRLocAddr]; omega
  let pref : ℕ → List ℕ := fun i =>
    ((List.range i).filter fun j => decide (mem (outRLocAddr + j) ≠ 0)).map fun j => verts.getD j 0
  have hpref_len : ∀ i, (pref i).length ≤ i := fun i => by
    simp only [pref, List.length_map]
    exact le_trans (List.length_filter_le _ _) (by simp)
  let Inv : ℕ → State → Prop := fun i st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.regs rfI = i ∧ st.regs rfCnt = (pref i).length ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem outRAddr (outRAddr + k) ∧
    ListAt st.mem outRAddr (pref i)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rfI) (lo := .const 0) (hi := .reg rfK)
    (body := seqStmts
      [ .assign rfTmp1 (.load (.bin .add (.reg rfOutRLoc) (.reg rfI)))
      , .cond (.bin .lt (.const 0) (.reg rfTmp1))
          (seqStmts
            [ .assign rfTmp2 (.load (.bin .add (.reg rfVerts) (.reg rfI)))
            , .store (.bin .add (.reg rfOutR) (.reg rfCnt)) (.reg rfTmp2)
            , .assign rfCnt (.bin .add (.reg rfCnt) (.const 1)) ])
          .nop ])
    (P := fun st =>
      RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
      st.regs rfCnt = 0 ∧ st.mem = mem ∧ st.pos = st₀.pos)
    (Inv := Inv) 38 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st ⟨hr, hcnt, hm, hp⟩ =>
      ⟨Expr.eval_const (by omega), rfRegs_update_ge (by decide) hr, by simp, by simp [pref, hcnt], hp,
        hm ▸ memFrame_refl mem _ _, by simp [pref]⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hcnt, hpos, hfr, hlat⟩
      have hi_lt : i < verts.length := hvlen ▸ hilt
      have hflag : st.mem (outRLocAddr + i) = mem (outRLocAddr + i) :=
        hfr (outRLocAddr + i) (disjointRange_outside hdisj_ow (by omega) (by omega))
      have hplen := hpref_len i
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := mem (outRLocAddr + i))
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_outRLoc) (Expr.eval_reg_of_eq hi) (by omega))
          hflag) ?_
      refine runs_cond_le
        (Expr.eval_lt_op (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (v := mem (outRLocAddr + i)) (by simp)) hw2)
        (fun hvne => ?_) (fun hv0 => ?_)
      · have hnz : mem (outRLocAddr + i) ≠ 0 := by
          intro h0; simp [h0] at hvne
        have hmem_v : st.mem (vertsAddr + i) = verts[i]'hi_lt := by
          rw [hfr (vertsAddr + i) (disjointRange_outside hdisj_ov (by omega) (by omega))]
          exact hlist i hi_lt
        have hpref_succ : pref (i + 1) = pref i ++ [verts[i]'hi_lt] := by
          simp [pref, List.range_succ, List.filter_append, hnz, List.getD_eq_getElem?_getD, hi_lt]
        refine runs_seq_assign_le (v := verts[i]'hi_lt)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (v := vertsAddr) (by simp [hr.r_verts]))
              (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega))
            hmem_v) ?_
        refine runs_seq_store_le (x := outRAddr + (pref i).length) (v := verts[i]'hi_lt)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := outRAddr) (by simp [hr.r_outR]))
            (Expr.eval_reg_of_eq (v := (pref i).length) (by simp [hcnt])) (by omega))
          (Expr.eval_reg_of_eq (v := verts[i]'hi_lt) (by simp)) ?_
        refine runs_assign_le (v := (pref i).length + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := (pref i).length) (by simp [hcnt]))
            (Expr.eval_const hw2) (by omega)) ?_ (by simp [Expr.size])
        refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide)
            (rfRegs_update_ge (r := rfCnt) (by decide)
              (rfRegs_update_mem (rfRegs_update_ge (r := rfTmp2) (by decide)
                (rfRegs_update_ge (r := rfTmp1) (by decide) hr)))),
          by simp, by rw [hpref_succ]; simp, hpos,
          memFrame_trans hfr (memFrame_update (by omega) (by omega)), ?_⟩, by simp [hi]⟩
        rw [hpref_succ]
        intro j hj
        dsimp only
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < (pref i).length
        · rw [Function.update_of_ne (by omega), List.getElem_append_left hjl]
          exact hlat j hjl
        · have hjeq : j = (pref i).length := by omega
          subst hjeq
          simp
      · have hnz : mem (outRLocAddr + i) = 0 := by
          by_contra hne
          have hpos' : 0 < mem (outRLocAddr + i) := Nat.pos_of_ne_zero hne
          simp [hpos'] at hv0
        have hpref_succ : pref (i + 1) = pref i := by
          dsimp only [pref]
          rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil, hnz]
          simp
        refine runs_nop_le ?_ (by simp [Expr.size])
        refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide)
            (rfRegs_update_ge (r := rfTmp1) (by decide) hr),
          by simp, by rw [hpref_succ]; simp [hcnt],
          hpos, hfr, by rw [hpref_succ]; exact hlat⟩, by simp [hi]⟩)
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [rfExtractRStmt, seqStmts]
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨rfRegs_update_ge (by decide) hregs, by simp, hmem, rfl⟩ ?_
  intro st1 ⟨_, _, hcnt1, hpos1, hfr1, hlat1⟩
  have hR_eq : pref k = R_list := by simp [pref, R_list, filterVertsByMem, hvlen]
  refine runs_ret_le (Expr.eval_reg_of_eq (hR_eq ▸ hcnt1))
    ⟨rfl, hpos1, hfr1, hR_eq ▸ hlat1⟩ ?_
  simp [Expr.size]; omega

/-! ## Pure properties of `filterVertsByMem` -/

lemma filterVertsByMem_length_le (mem : ℕ → ℕ) (outRLocAddr : ℕ) (verts : List ℕ) :
    (filterVertsByMem mem outRLocAddr verts).length ≤ verts.length := by
  simp only [filterVertsByMem, List.length_map]
  exact le_trans (List.length_filter_le _ _) (by simp)

lemma filterVertsByMem_nodup {mem : ℕ → ℕ} {outRLocAddr : ℕ} {verts : List ℕ}
    (hnd : verts.Nodup) : (filterVertsByMem mem outRLocAddr verts).Nodup := by
  unfold filterVertsByMem
  refine List.Nodup.map_on ?_ (List.Nodup.filter _ List.nodup_range)
  intro i hi j hj hij
  have hilt : i < verts.length := List.mem_range.mp (List.mem_filter.mp hi).1
  have hjlt : j < verts.length := List.mem_range.mp (List.mem_filter.mp hj).1
  exact nodup_getD_inj hnd hilt hjlt hij

lemma filterVertsByMem_toFinset (mem : ℕ → ℕ) (outRLocAddr : ℕ) (verts : List ℕ) :
    (filterVertsByMem mem outRLocAddr verts).toFinset =
      ((Finset.range verts.length).filter fun i => decide (mem (outRLocAddr + i) ≠ 0)).image
        (fun i => verts.getD i 0) := by
  ext u
  simp only [filterVertsByMem, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range,
    Finset.mem_image, Finset.mem_filter, Finset.mem_range]

end MinCostFlow.ExpanderDecomp
