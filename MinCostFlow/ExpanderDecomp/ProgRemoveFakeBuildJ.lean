module

public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase

import Mathlib.Tactic.Linarith

/-!
# `RemoveFake` Subdivided Graph Construction (`rfBuildJ_triple`)

Verifies Stage 2 (`rfBuildJStmt`) of the `RemoveFake` Word-RAM procedure: given the populated
local-ID table `locAddr[u] = verts.idxOf u` for `u ∈ verts`, builds `GraphAt st'.mem workAddr J`
for `J = subdivGraph k (relabelEdges verts H) (relabelEdges verts F)` in `O(mH + mF + 1)` steps.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Stage 2: writes `subdivGraph k H_loc F_loc` into `rfJGraphAddr workAddr`. -/
theorem rfBuildJ_triple {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (H F : List (ℕ × ℕ)) (st₀ : State)
    (hHlen : H.length = mH) (hFlen : F.length = mF)
    (hverts_lt : ∀ u ∈ verts, u < n)
    (hH_in : ∀ e ∈ H, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    (hF_in : ∀ e ∈ F, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    (hH_at : EdgesAt mem hAddr H) (hF_at : EdgesAt mem fAddr F)
    (hloc_map : ∀ u ∈ verts, mem (locAddr + u) = verts.idxOf u)
    (hdisj_wl : DisjointRange workAddr (2 + 2 * (mH + 2 * mF)) locAddr n)
    (hdisj_wh : DisjointRange workAddr (2 + 2 * (mH + 2 * mF)) hAddr (2 * mH))
    (hdisj_wf : DisjointRange workAddr (2 + 2 * (mH + 2 * mF)) fAddr (2 * mF))
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr)
    (hregs : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st₀)
    (hmem : st₀.mem = mem) :
    let J := subdivGraph k (relabelEdges verts H) (relabelEdges verts F)
    Triple w p (fun st => st = st₀) rfBuildJStmt
      (normalPost fun st' =>
        RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st' ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem workAddr (workAddr + 2 + 2 * (mH + 2 * mF)) ∧
        GraphAt st'.mem workAddr J)
      (fun _ => 75 * mH + 95 * mF + 40) := by
  intro J
  obtain ⟨hws, hval⟩ := rfWorkSpace_word_lt hw
  have hw2 : 16 < 2 ^ w := by omega
  have hh_w := hw.2.1
  have hf_w := hw.2.2.1
  have hloc_w := hw.2.2.2.2.1
  have hws_j : workAddr + 2 + 2 * (mH + 2 * mF) < 2 ^ w := by omega
  let InvH : ℕ → State → Prop := fun i st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.regs rfI = i ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem workAddr (workAddr + 2 + 2 * (mH + 2 * mF)) ∧
    st.mem workAddr = k + mF ∧
    st.mem (workAddr + 1) = mH + 2 * mF ∧
    (∀ j (hj : j < i), ∀ (hjH : j < H.length),
      st.mem (workAddr + 2 + 2 * j) = verts.idxOf (H[j]'hjH).1 ∧
      st.mem (workAddr + 3 + 2 * j) = verts.idxOf (H[j]'hjH).2)
  let InvF : ℕ → State → Prop := fun i st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.regs rfI = i ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem workAddr (workAddr + 2 + 2 * (mH + 2 * mF)) ∧
    st.mem workAddr = k + mF ∧
    st.mem (workAddr + 1) = mH + 2 * mF ∧
    (∀ j (hjH : j < H.length),
      st.mem (workAddr + 2 + 2 * j) = verts.idxOf (H[j]'hjH).1 ∧
      st.mem (workAddr + 3 + 2 * j) = verts.idxOf (H[j]'hjH).2) ∧
    (∀ j (hj : j < i), ∀ (hjF : j < F.length),
      st.mem (workAddr + 2 + 2 * mH + 4 * j) = verts.idxOf (F[j]'hjF).1 ∧
      st.mem (workAddr + 2 + 2 * mH + 4 * j + 1) = k + j ∧
      st.mem (workAddr + 2 + 2 * mH + 4 * j + 2) = k + j ∧
      st.mem (workAddr + 2 + 2 * mH + 4 * j + 3) = verts.idxOf (F[j]'hjF).2)
  have hloopH := Triple.forRange_const (w := w) (p := p) (r := rfI) (lo := .const 0) (hi := .reg rfMH)
    (body := seqStmts
      [ .assign rfTmp1 (.load (.bin .add (.reg rfH) (.bin .mul (.const 2) (.reg rfI))))
      , .assign rfTmp2 (.load (.bin .add (.bin .add (.reg rfH) (.bin .mul (.const 2) (.reg rfI))) (.const 1)))
      , .assign rfTmp3 (.load (.bin .add (.reg rfLoc) (.reg rfTmp1)))
      , .assign rfTmp4 (.load (.bin .add (.reg rfLoc) (.reg rfTmp2)))
      , .store (.bin .add (.bin .add (.reg rfJGraph) (.const 2)) (.bin .mul (.const 2) (.reg rfI))) (.reg rfTmp3)
      , .store (.bin .add (.bin .add (.reg rfJGraph) (.const 3)) (.bin .mul (.const 2) (.reg rfI))) (.reg rfTmp4) ])
    (P := fun st =>
      RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
      st.pos = st₀.pos ∧
      MemFrame mem st.mem workAddr (workAddr + 2 + 2 * (mH + 2 * mF)) ∧
      st.mem workAddr = k + mF ∧ st.mem (workAddr + 1) = mH + 2 * mF)
    (Inv := InvH) 62 0 mH (Nat.zero_le mH) (by omega) (fun _ => by omega)
    (fun st ⟨hr, hpos, hfr, hm0, hm1⟩ =>
      ⟨Expr.eval_const (by omega), rfRegs_update_ge (by decide) hr, by simp, hpos, hfr, hm0, hm1,
       fun j hj => by omega⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_mH)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hfr, hm0, hm1, hedges⟩
      have hiH : i < H.length := hHlen ▸ hilt
      have he_in := hH_in _ (List.getElem_mem hiH)
      have hu_mem : (H[i]'hiH).1 ∈ verts := List.mem_toFinset.mp he_in.1
      have hv_mem : (H[i]'hiH).2 ∈ verts := List.mem_toFinset.mp he_in.2
      have hu_lt : (H[i]'hiH).1 < n := hverts_lt _ hu_mem
      have hv_lt : (H[i]'hiH).2 < n := hverts_lt _ hv_mem
      have hmem_u : st.mem (hAddr + 2 * i) = (H[i]'hiH).1 := by
        have hout := disjointRange_outside hdisj_wh (x := hAddr + 2 * i) (by omega) (by omega)
        rw [hfr (hAddr + 2 * i) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact (hH_at i hiH).1
      have hmem_v : st.mem (hAddr + 2 * i + 1) = (H[i]'hiH).2 := by
        have hout := disjointRange_outside hdisj_wh (x := hAddr + 2 * i + 1) (by omega) (by omega)
        rw [hfr (hAddr + 2 * i + 1) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact (hH_at i hiH).2
      have hloc_u : st.mem (locAddr + (H[i]'hiH).1) = verts.idxOf (H[i]'hiH).1 := by
        have hout := disjointRange_outside hdisj_wl (x := locAddr + (H[i]'hiH).1) (by omega) (by omega)
        rw [hfr (locAddr + (H[i]'hiH).1) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact hloc_map _ hu_mem
      have hloc_v : st.mem (locAddr + (H[i]'hiH).2) = verts.idxOf (H[i]'hiH).2 := by
        have hout := disjointRange_outside hdisj_wl (x := locAddr + (H[i]'hiH).2) (by omega) (by omega)
        rw [hfr (locAddr + (H[i]'hiH).2) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact hloc_map _ hv_mem
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := (H[i]'hiH).1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_h)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hi) (by omega))
            (by omega)) hmem_u) ?_
      refine runs_seq_assign_le (v := (H[i]'hiH).2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := hAddr) (by simp [hr.r_h]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega))
              (by omega))
            (Expr.eval_const (by omega)) (by omega)) hmem_v) ?_
      refine runs_seq_assign_le (v := verts.idxOf (H[i]'hiH).1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
            (Expr.eval_reg_of_eq (v := (H[i]'hiH).1) (by simp)) (by omega)) hloc_u) ?_
      refine runs_seq_assign_le (v := verts.idxOf (H[i]'hiH).2)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
            (Expr.eval_reg_of_eq (v := (H[i]'hiH).2) (by simp)) (by omega)) hloc_v) ?_
      refine runs_seq_store_le (x := workAddr + 2 + 2 * i) (v := verts.idxOf (H[i]'hiH).1)
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (v := workAddr) (by simp [hr.r_jGraph, rfJGraphAddr]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega))
          (by omega))
        (Expr.eval_reg_of_eq (v := verts.idxOf (H[i]'hiH).1) (by simp)) ?_
      refine runs_store_le (x := workAddr + 3 + 2 * i) (v := verts.idxOf (H[i]'hiH).2)
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (v := workAddr) (by simp [hr.r_jGraph, rfJGraphAddr]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega))
          (by omega))
        (Expr.eval_reg_of_eq (v := verts.idxOf (H[i]'hiH).2) (by simp)) ?_ ?_
      · refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide)
            (rfRegs_update_mem (rfRegs_update_mem
              (rfRegs_update_ge (r := rfTmp4) (by decide)
                (rfRegs_update_ge (r := rfTmp3) (by decide)
                  (rfRegs_update_ge (r := rfTmp2) (by decide)
                    (rfRegs_update_ge (r := rfTmp1) (by decide) hr)))))),
          by simp, hpos,
          memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
            (memFrame_update (by omega) (by omega))),
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hm0,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hm1, ?_⟩,
          by simp [hi]⟩
        intro j hj hjH
        dsimp only
        by_cases hji : j = i
        · subst hji
          refine ⟨?_, by simp⟩
          rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hedges j (by omega) hjH
      · simp [Expr.size])
  have hloopF := Triple.forRange_const (w := w) (p := p) (r := rfI) (lo := .const 0) (hi := .reg rfMF)
    (body := seqStmts
      [ .assign rfTmp1 (.load (.bin .add (.reg rfF) (.bin .mul (.const 2) (.reg rfI))))
      , .assign rfTmp2 (.load (.bin .add (.bin .add (.reg rfF) (.bin .mul (.const 2) (.reg rfI))) (.const 1)))
      , .assign rfTmp3 (.load (.bin .add (.reg rfLoc) (.reg rfTmp1)))
      , .assign rfTmp4 (.load (.bin .add (.reg rfLoc) (.reg rfTmp2)))
      , .assign rfTmp5 (.bin .add (.reg rfK) (.reg rfI))
      , .assign rfTmp1 (.bin .add (.bin .add (.bin .add (.reg rfJGraph) (.const 2))
          (.bin .mul (.const 2) (.reg rfMH))) (.bin .mul (.const 4) (.reg rfI)))
      , .store (.reg rfTmp1) (.reg rfTmp3)
      , .store (.bin .add (.reg rfTmp1) (.const 1)) (.reg rfTmp5)
      , .store (.bin .add (.reg rfTmp1) (.const 2)) (.reg rfTmp5)
      , .store (.bin .add (.reg rfTmp1) (.const 3)) (.reg rfTmp4) ])
    (P := fun st =>
      RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
      st.pos = st₀.pos ∧
      MemFrame mem st.mem workAddr (workAddr + 2 + 2 * (mH + 2 * mF)) ∧
      st.mem workAddr = k + mF ∧ st.mem (workAddr + 1) = mH + 2 * mF ∧
      (∀ j (hjH : j < H.length),
        st.mem (workAddr + 2 + 2 * j) = verts.idxOf (H[j]'hjH).1 ∧
        st.mem (workAddr + 3 + 2 * j) = verts.idxOf (H[j]'hjH).2))
    (Inv := InvF) 82 0 mF (Nat.zero_le mF) (by omega) (fun _ => by omega)
    (fun st ⟨hr, hpos, hfr, hm0, hm1, hedgesH⟩ =>
      ⟨Expr.eval_const (by omega), rfRegs_update_ge (by decide) hr, by simp, hpos, hfr, hm0, hm1,
       hedgesH, fun j hj => by omega⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_mF)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hfr, hm0, hm1, hedgesH, hedgesF⟩
      have hiF : i < F.length := hFlen ▸ hilt
      have he_in := hF_in _ (List.getElem_mem hiF)
      have hu_mem : (F[i]'hiF).1 ∈ verts := List.mem_toFinset.mp he_in.1
      have hv_mem : (F[i]'hiF).2 ∈ verts := List.mem_toFinset.mp he_in.2
      have hu_lt : (F[i]'hiF).1 < n := hverts_lt _ hu_mem
      have hv_lt : (F[i]'hiF).2 < n := hverts_lt _ hv_mem
      have hmem_u : st.mem (fAddr + 2 * i) = (F[i]'hiF).1 := by
        have hout := disjointRange_outside hdisj_wf (x := fAddr + 2 * i) (by omega) (by omega)
        rw [hfr (fAddr + 2 * i) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact (hF_at i hiF).1
      have hmem_v : st.mem (fAddr + 2 * i + 1) = (F[i]'hiF).2 := by
        have hout := disjointRange_outside hdisj_wf (x := fAddr + 2 * i + 1) (by omega) (by omega)
        rw [hfr (fAddr + 2 * i + 1) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact (hF_at i hiF).2
      have hloc_u : st.mem (locAddr + (F[i]'hiF).1) = verts.idxOf (F[i]'hiF).1 := by
        have hout := disjointRange_outside hdisj_wl (x := locAddr + (F[i]'hiF).1) (by omega) (by omega)
        rw [hfr (locAddr + (F[i]'hiF).1) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact hloc_map _ hu_mem
      have hloc_v : st.mem (locAddr + (F[i]'hiF).2) = verts.idxOf (F[i]'hiF).2 := by
        have hout := disjointRange_outside hdisj_wl (x := locAddr + (F[i]'hiF).2) (by omega) (by omega)
        rw [hfr (locAddr + (F[i]'hiF).2) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact hloc_map _ hv_mem
      set base := workAddr + 2 + 2 * mH + 4 * i
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := (F[i]'hiF).1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_f)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hi) (by omega))
            (by omega)) hmem_u) ?_
      refine runs_seq_assign_le (v := (F[i]'hiF).2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := fAddr) (by simp [hr.r_f]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega))
              (by omega))
            (Expr.eval_const (by omega)) (by omega)) hmem_v) ?_
      refine runs_seq_assign_le (v := verts.idxOf (F[i]'hiF).1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
            (Expr.eval_reg_of_eq (v := (F[i]'hiF).1) (by simp)) (by omega)) hloc_u) ?_
      refine runs_seq_assign_le (v := verts.idxOf (F[i]'hiF).2)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
            (Expr.eval_reg_of_eq (v := (F[i]'hiF).2) (by simp)) (by omega)) hloc_v) ?_
      refine runs_seq_assign_le (v := k + i)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := k) (by simp [hr.r_k]))
          (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega)) ?_
      refine runs_seq_assign_le (v := base)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := workAddr) (by simp [hr.r_jGraph, rfJGraphAddr]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := mH) (by simp [hr.r_mH])) (by omega))
            (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega))
          (by omega)) ?_
      refine runs_seq_store_le (x := base) (v := verts.idxOf (F[i]'hiF).1)
        (Expr.eval_reg_of_eq (v := base) (by simp))
        (Expr.eval_reg_of_eq (v := verts.idxOf (F[i]'hiF).1) (by simp)) ?_
      refine runs_seq_store_le (x := base + 1) (v := k + i)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := base) (by simp)) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := k + i) (by simp)) ?_
      refine runs_seq_store_le (x := base + 2) (v := k + i)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := base) (by simp)) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := k + i) (by simp)) ?_
      refine runs_store_le (x := base + 3) (v := verts.idxOf (F[i]'hiF).2)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := base) (by simp)) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := verts.idxOf (F[i]'hiF).2) (by simp)) ?_ ?_
      · refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide)
            (rfRegs_update_mem (rfRegs_update_mem (rfRegs_update_mem (rfRegs_update_mem
              (rfRegs_update_ge (r := rfTmp1) (by decide) (rfRegs_update_ge (r := rfTmp5) (by decide)
                (rfRegs_update_ge (r := rfTmp4) (by decide) (rfRegs_update_ge (r := rfTmp3) (by decide)
                  (rfRegs_update_ge (r := rfTmp2) (by decide) (rfRegs_update_ge (r := rfTmp1) (by decide) hr)))))))))),
          by simp, hpos,
          memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
            (memFrame_trans (memFrame_update (by omega) (by omega))
              (memFrame_trans (memFrame_update (by omega) (by omega))
                (memFrame_update (by omega) (by omega))))),
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hm0,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hm1,
          fun j hjH => by
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hedgesH j hjH, ?_⟩, by simp [hi]⟩
        intro j hj hjF
        dsimp only
        by_cases hji : j = i
        · subst hji
          refine ⟨?_, ?_, ?_, by simp [base]⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hedgesF j (by omega) hjF
      · simp [Expr.size])
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [rfBuildJStmt, seqStmts]
  refine runs_seq_store_le (x := workAddr) (v := k + mF)
    (Expr.eval_reg_of_eq (by simp [hregs.r_jGraph, rfJGraphAddr]))
    (Expr.eval_reg_of_eq hregs.r_nJ) ?_
  refine runs_seq_store_le (x := workAddr + 1) (v := mH + 2 * mF)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hregs.r_jGraph, rfJGraphAddr]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp [hregs.r_mJ])) ?_
  refine runs_seq_triple_le hloopH
    ⟨rfRegs_update_mem (rfRegs_update_mem hregs), rfl,
     hmem ▸ memFrame_trans (memFrame_update (by omega) (by omega))
       (memFrame_update (by omega) (by omega)),
     by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self], by simp⟩ ?_
  intro st1 ⟨hr1, _, hpos1, hfr1, hm01, hm11, hedgesH1⟩
  refine runs_triple_le hloopF
    ⟨hr1, hpos1, hfr1, hm01, hm11, fun j hjH => hedgesH1 j (hHlen ▸ hjH) hjH⟩ ?_ ?_
  · rintro (_ | _) st2 hq2
    · rcases hq2 with ⟨hr2, _, hpos2, hfr2, hm02, hm12, hedgesH2, hedgesF2⟩
      refine ⟨hr2, hpos2, hfr2, ?_⟩
      have hJn : J.n = k + mF := by simp [J, subdivGraph, relabelEdges, hFlen]
      have hJm : J.m = mH + 2 * mF := by
        simp [J, subdivGraph, Graph.m, relabelEdges, subdiv_length, hHlen, hFlen]
      refine graphAt_of_cells (by rw [hJn]; exact hm02) (by rw [hJm]; exact hm12) ?_
      intro j hj
      have hj' : j < mH + 2 * mF := hJm ▸ hj
      by_cases hjmH : j < mH
      · have hjH : j < H.length := hHlen ▸ hjmH
        have hget : (J.edges[j]'hj) = (verts.idxOf (H[j]'hjH).1, verts.idxOf (H[j]'hjH).2) := by
          simp only [J, subdivGraph]
          rw [List.getElem_append_left (by simp [relabelEdges, hjH])]
          simp [relabelEdges]
        rw [hget]
        exact hedgesH2 j hjH
      · set q := (j - mH) / 2
        have hqF : q < F.length := by omega
        have hFL_len : (relabelEdges verts F).length = F.length := by simp [relabelEdges]
        have hFloc_q : (relabelEdges verts F)[q]'(hFL_len ▸ hqF) =
            (verts.idxOf (F[q]'hqF).1, verts.idxOf (F[q]'hqF).2) := by
          simp [relabelEdges]
        have hF2 := hedgesF2 q (hFlen ▸ hqF) hqF
        rcases Nat.even_or_odd' (j - mH) with ⟨r, hr_eq | hr_eq⟩
        · have hrq : r = q := by omega
          have hj_eq : j = mH + 2 * q := by omega
          have hget : (J.edges[j]'hj) = (verts.idxOf (F[q]'hqF).1, k + q) := by
            simp only [J, subdivGraph]
            rw [List.getElem_append_right (by simp [relabelEdges, hHlen]; omega)]
            have hidx : j - (relabelEdges verts H).length = 2 * q := by
              simp [relabelEdges, hHlen]; omega
            simp only [hidx]
            rw [subdiv_getElem_even k (relabelEdges verts F) q (hFL_len ▸ hqF), hFloc_q]
          rw [hget, hj_eq]
          refine ⟨?_, ?_⟩
          · rw [show workAddr + 2 + 2 * (mH + 2 * q) = workAddr + 2 + 2 * mH + 4 * q by omega]
            exact hF2.1
          · rw [show workAddr + 3 + 2 * (mH + 2 * q) = workAddr + 2 + 2 * mH + 4 * q + 1 by omega]
            exact hF2.2.1
        · have hrq : r = q := by omega
          have hj_eq : j = mH + 2 * q + 1 := by omega
          have hget : (J.edges[j]'hj) = (k + q, verts.idxOf (F[q]'hqF).2) := by
            simp only [J, subdivGraph]
            rw [List.getElem_append_right (by simp [relabelEdges, hHlen]; omega)]
            have hidx : j - (relabelEdges verts H).length = 2 * q + 1 := by
              simp [relabelEdges, hHlen]; omega
            simp only [hidx]
            rw [subdiv_getElem_odd k (relabelEdges verts F) q (hFL_len ▸ hqF), hFloc_q]
          rw [hget, hj_eq]
          refine ⟨?_, ?_⟩
          · rw [show workAddr + 2 + 2 * (mH + 2 * q + 1) = workAddr + 2 + 2 * mH + 4 * q + 2 by omega]
            exact hF2.2.2.1
          · rw [show workAddr + 3 + 2 * (mH + 2 * q + 1) = workAddr + 2 + 2 * mH + 4 * q + 3 by omega]
            exact hF2.2.2.2
    · exact False.elim hq2
  · simp [Expr.size]; omega

end MinCostFlow.ExpanderDecomp
