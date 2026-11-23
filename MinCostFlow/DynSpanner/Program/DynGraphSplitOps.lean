module

public import MinCostFlow.DynSpanner.Program.DynGraphSplitOpsBasic
public import MinCostFlow.DynSpanner.Program.DynGraphEdges
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Dynamic graph vertex split primitives (`DynGraphSplitOps`)

This file defines all dynamic-graph vertex split procedures (`dgSplitProcs`) and verifies the
low-level half-edge and edge-list movement primitives:

* `dgIdxMoveSlotEdge` (`0`): move the tail or head half-edge (`isHead ∈ {0, 1}`) of an edge `e`
  currently attached to slot `sSrc` over to slot `sDst` in `O(1)` time (no-op if `e ∉ E`).
* `dgIdxMoveSlotLoop` (`1`): iterate `j = 0 .. L_len - 1` over an edge-ID array `L_ptr`,
  calling `dgMoveSlotEdge` on each entry in `O(L_len + 1)` time.

The high-level `dgIdxApplySplit` (`2`) procedure and its proof live in
`MinCostFlow.DynSpanner.Program.DynGraphSplit`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma dgMoveHalfEdge_triple {w : ℕ} {p : Program} {bOps : ℕ}
    {gPtr vCap eCap sSrc sDst e : ℕ} {E : Finset ℕ} {slotTail slotHead : ℕ → ℕ}
    {mem₀ : ℕ → ℕ} (isHead : Bool)
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hsSrc_lt : sSrc < vCap) (hsDst_lt : sDst < vCap) (hne : sSrc ≠ sDst)
    (heE : e ∈ E) (hInc : DgIncStateAt mem₀ gPtr vCap eCap E slotTail slotHead) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = sSrc ∧ st.regs 2 = sDst ∧ st.regs 3 = e ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧
        st.regs 7 = dgETailSlotBase gPtr vCap eCap ∧ st.regs 8 = dgEHeadSlotBase gPtr vCap eCap ∧
        st.regs 9 = dgHePrevBase gPtr vCap eCap ∧ st.regs 10 = dgHeNextBase gPtr vCap eCap ∧
        st.regs 11 = dgIncHeadBase gPtr vCap ∧ st.regs 12 = dgSlotDegBase gPtr vCap ∧
        st.mem = mem₀)
      (dgMoveHalfEdgeStmt bOps isHead)
      (normalPost fun st =>
        st.regs 0 = gPtr ∧ st.regs 1 = sSrc ∧ st.regs 2 = sDst ∧ st.regs 3 = e ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧
        st.regs 7 = dgETailSlotBase gPtr vCap eCap ∧ st.regs 8 = dgEHeadSlotBase gPtr vCap eCap ∧
        st.regs 9 = dgHePrevBase gPtr vCap eCap ∧ st.regs 10 = dgHeNextBase gPtr vCap eCap ∧
        st.regs 11 = dgIncHeadBase gPtr vCap ∧ st.regs 12 = dgSlotDegBase gPtr vCap ∧
        DgIncStateAt st.mem gPtr vCap eCap E
          (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x)
          (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) ∧
        DgSlotsOnlyModified mem₀ st.mem gPtr vCap eCap)
      (fun _ => 210) := by
  intro st ω ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr7, hr8, hr9, hr10, hr11, hr12, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hr7 hr8 hr9 hr10 hr11 hr12 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  rcases hInc with ⟨h0, h1, hEcap, hep, hets_ehs, ⟨incL, hincL⟩⟩
  have hInc' : DgIncStateAt mem₀ gPtr vCap eCap E slotTail slotHead :=
    ⟨h0, h1, hEcap, hep, hets_ehs, ⟨incL, hincL⟩⟩
  have he_lt := (hEcap e heE).1
  have he_ltw : e < 2 ^ w := by omega
  have hcur_eq : mem₀ ((if isHead then dgEHeadSlotBase gPtr vCap eCap else dgETailSlotBase gPtr vCap eCap) + e) =
      if isHead then slotHead e else slotTail e := by
    rcases hets_ehs e heE with ⟨hxt, hxh⟩
    cases isHead <;> simp [hxt, hxh]
  have hlt_slot : ((if isHead then dgEHeadSlotBase gPtr vCap eCap else dgETailSlotBase gPtr vCap eCap) + e) < 2 ^ w := by
    cases isHead <;> [dsimp [dgETailSlotBase]; dsimp [dgEHeadSlotBase]] <;> omega
  have hlt_cur : (if isHead then slotHead e else slotTail e) < 2 ^ w := by
    rcases hEcap e heE with ⟨_, hxt, hxh⟩; cases isHead <;> dsimp <;> omega
  have hcond : (Expr.bin .eq (.load (.bin .add (.reg (if isHead then 8 else 7)) (.reg 3))) (.reg 1)).eval w
      { mem := mem₀, regs := str, pos := stp } =
      some (if (if isHead then slotHead e else slotTail e) = sSrc then 1 else 0) := by
    have hload : (Expr.load (.bin .add (.reg (if isHead then 8 else 7)) (.reg 3))).eval w
        { mem := mem₀, regs := str, pos := stp } = some (if isHead then slotHead e else slotTail e) := by
      refine Expr.eval_load_of_eq ?_ hcur_eq
      cases isHead
      · dsimp [dgETailSlotBase] at hlt_slot ⊢; eval_expr
      · dsimp [dgEHeadSlotBase] at hlt_slot ⊢; eval_expr
    refine Expr.eval_bin hload (by eval_expr) (by dsimp [BinOp.eval]; split_ifs <;> omega)
  dsimp only [dgMoveHalfEdgeStmt]
  suffices h : ∃ o st' c,
      Runs w p ω (.cond (.bin .eq (.load (.bin .add (.reg (if isHead then 8 else 7)) (.reg 3))) (.reg 1))
        (.call 13 (bOps + dgIdxDllRemove)
          [.reg 9, .reg 10, .bin .add (.reg 11) (.reg 1), .bin .add (.reg 12) (.reg 1),
            if isHead then .bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)
            else .bin .mul (.const 2) (.reg 3)] ;;
         .call 13 (bOps + dgIdxDllCons)
          [.reg 9, .reg 10, .bin .add (.reg 11) (.reg 2), .bin .add (.reg 12) (.reg 2),
            if isHead then .bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)
            else .bin .mul (.const 2) (.reg 3)] ;;
         .store (.bin .add (.reg (if isHead then 8 else 7)) (.reg 3)) (.reg 2))
        .nop) { mem := mem₀, regs := str, pos := stp } o st' c ∧
      normalPost (fun st =>
        st.regs 0 = gPtr ∧ st.regs 1 = sSrc ∧ st.regs 2 = sDst ∧ st.regs 3 = e ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧
        st.regs 7 = dgETailSlotBase gPtr vCap eCap ∧ st.regs 8 = dgEHeadSlotBase gPtr vCap eCap ∧
        st.regs 9 = dgHePrevBase gPtr vCap eCap ∧ st.regs 10 = dgHeNextBase gPtr vCap eCap ∧
        st.regs 11 = dgIncHeadBase gPtr vCap ∧ st.regs 12 = dgSlotDegBase gPtr vCap ∧
        DgIncStateAt st.mem gPtr vCap eCap E
          (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x)
          (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) ∧
        DgSlotsOnlyModified mem₀ st.mem gPtr vCap eCap) o st' ∧
      0 + c ≤ 210 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  refine runs_cond_le hcond ?_ ?_
  · intro hne_eq
    have hcur : (if isHead then slotHead e else slotTail e) = sSrc := by
      by_contra hc; simp [hc] at hne_eq
    let hh := if isHead then 2 * e + 1 else 2 * e
    have hh_lt : hh < 2 * eCap := by cases isHead <;> simp [hh] <;> omega
    have hh_ltw : hh < 2 ^ w := by omega
    have h_div : hh / 2 = e := by
      cases isHead
      · simp [hh]
      · simp [hh]; omega
    have h_mod : hh % 2 = if isHead then 1 else 0 := by cases isHead <;> simp [hh]
    have hh_in_src : hh ∈ incL sSrc := by
      rw [(hincL sSrc hsSrc_lt).2.2 hh]
      refine ⟨hh_lt, h_div ▸ heE, ?_⟩
      rw [h_div, h_mod]
      cases isHead
      · simp only [Bool.false_eq_true, ↓reduceIte] at hcur ⊢; exact hcur
      · simp only [↓reduceIte] at hcur ⊢; exact hcur
    have hh_not_dst : hh ∉ incL sDst := by
      intro hm
      have hs := ((hincL sDst hsDst_lt).2.2 hh).mp hm |>.2.2
      rw [h_div, h_mod] at hs
      cases isHead
      · simp only [Bool.false_eq_true, ↓reduceIte] at hcur hs; exact hne (hcur.symm.trans hs)
      · simp only [↓reduceIte] at hcur hs; exact hne (hcur.symm.trans hs)
    have hlt_hp : dgHePrevBase gPtr vCap eCap + 2 * eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
    have hlt_hn : dgHeNextBase gPtr vCap eCap + 2 * eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
    have hlt_ih_src : dgIncHeadBase gPtr vCap + sSrc < 2 ^ w := by dsimp [dgIncHeadBase]; omega
    have hlt_sd_src : dgSlotDegBase gPtr vCap + sSrc < 2 ^ w := by dsimp [dgSlotDegBase]; omega
    have hlt_ih_dst : dgIncHeadBase gPtr vCap + sDst < 2 ^ w := by dsimp [dgIncHeadBase]; omega
    have hlt_sd_dst : dgSlotDegBase gPtr vCap + sDst < 2 ^ w := by dsimp [dgSlotDegBase]; omega
    have hsrc_len_w : mem₀ (dgSlotDegBase gPtr vCap + sSrc) < 2 ^ w := by
      rw [(hincL sSrc hsSrc_lt).2.1]
      have := nodup_length_le_cap (hincL sSrc hsSrc_lt).1.1 (hincL sSrc hsSrc_lt).1.2.1
      omega
    have hlt_hp0 : dgHePrevBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
    have hlt_hn0 : dgHeNextBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
    have hlt_ih0 : dgIncHeadBase gPtr vCap < 2 ^ w := by dsimp [dgIncHeadBase]; omega
    have hlt_sd0 : dgSlotDegBase gPtr vCap < 2 ^ w := by dsimp [dgSlotDegBase]; omega
    have h2e_ltw : 2 * e < 2 ^ w := by omega
    have h2e1_ltw : 2 * e + 1 < 2 ^ w := by omega
    have hargs1 : evalArgs w { mem := mem₀, regs := str, pos := stp }
        [.reg 9, .reg 10, .bin .add (.reg 11) (.reg 1), .bin .add (.reg 12) (.reg 1),
          if isHead then .bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)
          else .bin .mul (.const 2) (.reg 3)] =
        some [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
          dgIncHeadBase gPtr vCap + sSrc, dgSlotDegBase gPtr vCap + sSrc, hh] := by
      cases isHead
      · simp only [Bool.false_eq_true, ↓reduceIte, hh]; eval_expr
      · simp only [↓reduceIte, hh]; eval_expr
    have hpre1 : (dgDllRemoveContract w (2 * eCap) (incL sSrc)).pre
        [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
         dgIncHeadBase gPtr vCap + sSrc, dgSlotDegBase gPtr vCap + sSrc, hh] mem₀ := by
      refine ⟨dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
        dgIncHeadBase gPtr vCap + sSrc, dgSlotDegBase gPtr vCap + sSrc, hh, rfl,
        hw16, hlt_hp, hlt_hn, hlt_ih_src, hlt_sd_src, (hincL sSrc hsSrc_lt).1, hh_in_src,
        hsrc_len_w, by dsimp [dgIncHeadBase, dgSlotDegBase]; omega,
        fun x _ => by dsimp [dgHePrevBase, dgIncHeadBase, dgSlotDegBase]; omega,
        fun x _ => by dsimp [dgHeNextBase, dgIncHeadBase, dgSlotDegBase]; omega,
        fun x y hEq _ _ => by dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega⟩
    refine runs_seq_call_le (dgDllRemove_meetsContract hpOps) hargs1
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl) <;> omega)
      hpre1 ?_
    rintro v1 mem1 pos1 ⟨hb1, hb2, hb3, hb4, hb5, hEq1, _, hc1_dll, hc1_deg, hc1_fr⟩
    simp only [List.cons.injEq, and_true] at hEq1
    rcases hEq1 with ⟨h1', h2', h3', h4', h5'⟩
    subst h1' h2' h3' h4' h5'
    let st1 : State := { mem := mem1, regs := Function.update str 13 v1, pos := pos1 }
    have hm1_dst_dll : IsDoublyLinkedList mem1 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + sDst) (2 * eCap) (incL sDst) := by
      have hdisj : ∀ y ∈ incL sDst, y ∉ incL sSrc := by
        intro y hy1 hy2
        have hEq1 := ((hincL sDst hsDst_lt).2.2 y).mp hy1 |>.2.2
        have hEq2 := ((hincL sSrc hsSrc_lt).2.2 y).mp hy2 |>.2.2
        exact hne (hEq2.symm.trans hEq1)
      exact (hincL sDst hsDst_lt).1.of_agree
        (hc1_fr _ (fun x hEq hx => by
          have hlt := (hincL sSrc hsSrc_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := (hincL sSrc hsSrc_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega))
        (fun x hx => hc1_fr _
          (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hdisj x hx hy)
          (fun y hEq hy => by
            have hlt1 := (hincL sDst hsDst_lt).1.2.1 x hx; have hlt2 := (hincL sSrc hsSrc_lt).1.2.1 y hy
            dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgHePrevBase, dgIncHeadBase]; omega)
          (by dsimp [dgHePrevBase, dgSlotDegBase]; omega))
        (fun x hx => hc1_fr _
          (fun y hEq hy => by
            have hlt1 := (hincL sDst hsDst_lt).1.2.1 x hx; have hlt2 := (hincL sSrc hsSrc_lt).1.2.1 y hy
            dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
          (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hdisj x hx hy)
          (by dsimp [dgHeNextBase, dgIncHeadBase]; omega)
          (by dsimp [dgHeNextBase, dgSlotDegBase]; omega))
    have hm1_dst_deg : mem1 (dgSlotDegBase gPtr vCap + sDst) = (incL sDst).length := by
      rw [hc1_fr _ (fun x hEq hx => by dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
        (fun x hEq hx => by dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
        (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega) (by dsimp [dgSlotDegBase]; omega)]
      exact (hincL sDst hsDst_lt).2.1
    have hdst_len : (incL sDst).length + 1 ≤ 2 * eCap :=
      nodup_length_lt_of_notMem hm1_dst_dll.1 hm1_dst_dll.2.1 hh_lt hh_not_dst
    have hargs2 : evalArgs w st1
        [.reg 9, .reg 10, .bin .add (.reg 11) (.reg 2), .bin .add (.reg 12) (.reg 2),
          if isHead then .bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)
          else .bin .mul (.const 2) (.reg 3)] =
        some [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
          dgIncHeadBase gPtr vCap + sDst, dgSlotDegBase gPtr vCap + sDst, hh] := by
      dsimp only [st1]
      cases isHead
      · simp only [Bool.false_eq_true, ↓reduceIte, hh]; eval_expr
      · simp only [↓reduceIte, hh]; eval_expr
    have hpre2 : (dgDllConsContract w (2 * eCap) (incL sDst)).pre
        [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
         dgIncHeadBase gPtr vCap + sDst, dgSlotDegBase gPtr vCap + sDst, hh] mem1 := by
      refine ⟨dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
        dgIncHeadBase gPtr vCap + sDst, dgSlotDegBase gPtr vCap + sDst, hh, rfl,
        hw16, hlt_hp, hlt_hn, hlt_ih_dst, hlt_sd_dst, hm1_dst_dll, hh_lt, hh_not_dst,
        by rw [hm1_dst_deg]; omega, by dsimp [dgIncHeadBase, dgSlotDegBase]; omega,
        fun x _ => by dsimp [dgHePrevBase, dgIncHeadBase, dgSlotDegBase]; omega,
        fun x _ => by dsimp [dgHeNextBase, dgIncHeadBase, dgSlotDegBase]; omega,
        fun x y hEq _ _ => by dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega⟩
    refine runs_seq_call_le (dgDllCons_meetsContract hpOps) hargs2
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl) <;> omega)
      hpre2 ?_
    rintro v2 mem2 pos2 ⟨hb1', hb2', hb3', hb4', hb5', hEq2, _, hc2_dll, hc2_deg, hc2_fr⟩
    simp only [List.cons.injEq, and_true] at hEq2
    rcases hEq2 with ⟨h1'', h2'', h3'', h4'', h5''⟩
    subst h1'' h2'' h3'' h4'' h5''
    let st2 : State := { mem := mem2, regs := Function.update st1.regs 13 v2, pos := pos2 }
    have hlt_ts0 : dgETailSlotBase gPtr vCap eCap < 2 ^ w := by dsimp [dgETailSlotBase]; omega
    have hlt_hs0 : dgEHeadSlotBase gPtr vCap eCap < 2 ^ w := by dsimp [dgEHeadSlotBase]; omega
    have heval_store :
        (Expr.bin .add (.reg (if isHead then 8 else 7)) (.reg 3)).eval w st2 =
          some ((if isHead then dgEHeadSlotBase gPtr vCap eCap else dgETailSlotBase gPtr vCap eCap) + e) ∧
        (Expr.reg 2).eval w st2 = some sDst := by
      constructor
      · dsimp only [st2, st1]
        cases isHead
        · simp only [Bool.false_eq_true, ↓reduceIte] at hlt_slot ⊢; eval_expr
        · simp only [↓reduceIte] at hlt_slot ⊢; eval_expr
      · dsimp only [st2, st1]; eval_expr
    refine runs_store_le heval_store.1 heval_store.2 ?_ ?_
    · dsimp only [normalPost]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hr0]
      · simp [hr1]
      · simp [hr2]
      · simp [hr3]
      · simp [hr4]
      · simp [hr5]
      · simp [hr7]
      · simp [hr8]
      · simp [hr9]
      · simp [hr10]
      · simp [hr11]
      · simp [hr12]
      · exact (dgIncStateAt_move_halfEdge_step isHead hbound hsSrc_lt hsDst_lt hne heE hInc' hcur
          hincL hc1_dll hc1_deg hc1_fr hc2_dll hc2_deg hc2_fr rfl).1
      · exact (dgIncStateAt_move_halfEdge_step isHead hbound hsSrc_lt hsDst_lt hne heE hInc' hcur
          hincL hc1_dll hc1_deg hc1_fr hc2_dll hc2_deg hc2_fr rfl).2
    · dsimp only [dgDllRemoveContract, dgDllConsContract, argsSize, Expr.size]
      cases isHead <;> dsimp <;> omega
  · intro he_zero
    have hcur_ne : (if isHead then slotHead e else slotTail e) ≠ sSrc := by
      intro hc; simp [hc] at he_zero
    refine runs_nop_le ?_ ?_
    · refine ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr7, hr8, hr9, hr10, hr11, hr12, ?_,
        DgSlotsOnlyModified.refl mem₀ gPtr vCap eCap⟩
      have hsub_t : (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x) =
          slotTail := by
        cases isHead
        · funext x
          simp only [Bool.false_eq_true, ↓reduceIte] at hcur_ne ⊢
          split_ifs with hm
          · exact absurd hm.2 hcur_ne
          · rfl
        · rfl
      have hsub_h : (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) =
          slotHead := by
        cases isHead
        · rfl
        · funext x
          simp only [↓reduceIte] at hcur_ne ⊢
          split_ifs with hm
          · exact absurd hm.2 hcur_ne
          · rfl
      rw [hsub_t, hsub_h]; exact hInc'
    · dsimp only [Expr.size]; cases isHead <;> dsimp <;> omega

private lemma dgMoveSlotEdgeBody_triple {w : ℕ} {p : Program} {bOps : ℕ}
    {gPtr vCap eCap sSrc sDst e : ℕ} {E : Finset ℕ} {slotTail slotHead : ℕ → ℕ}
    {mem₀ : ℕ → ℕ} (isHead : Bool)
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hsSrc_lt : sSrc < vCap) (hsDst_lt : sDst < vCap) (hne : sSrc ≠ sDst)
    (heE : e ∈ E) (hInc : DgIncStateAt mem₀ gPtr vCap eCap E slotTail slotHead) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = sSrc ∧ st.regs 2 = sDst ∧ st.regs 3 = e ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.regs 6 = dgEPresBase gPtr vCap ∧
        st.regs 14 = (if isHead then 1 else 0) ∧ st.mem = mem₀)
      (dgMoveSlotEdgeBodyStmt bOps)
      (normalPost fun st =>
        DgIncStateAt st.mem gPtr vCap eCap E
          (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x)
          (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) ∧
        DgSlotsOnlyModified mem₀ st.mem gPtr vCap eCap)
      (fun _ => 510) := by
  intro st ω ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr14, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr14 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_ep : dgEPresBase gPtr vCap < 2 ^ w := by dsimp [dgEPresBase]; omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_ec : eCap < 2 ^ w := by omega
  have hlt_3ec : 3 * eCap < 2 ^ w := by omega
  have hlt_4ec : 4 * eCap < 2 ^ w := by omega
  have hlt_5ec : 5 * eCap < 2 ^ w := by omega
  have hlt_7ec : 7 * eCap < 2 ^ w := by omega
  have hlt_6vc : 6 * vCap < 2 ^ w := by omega
  have hlt_5vc : 5 * vCap < 2 ^ w := by omega
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_gp4 : gPtr + 4 < 2 ^ w := by omega
  have hlt_ts : dgETailSlotBase gPtr vCap eCap < 2 ^ w := by dsimp [dgETailSlotBase]; omega
  have hlt_hs : dgEHeadSlotBase gPtr vCap eCap < 2 ^ w := by dsimp [dgEHeadSlotBase]; omega
  have hlt_hp : dgHePrevBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
  have hlt_hn : dgHeNextBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
  have hlt_ih : dgIncHeadBase gPtr vCap < 2 ^ w := by dsimp [dgIncHeadBase]; omega
  have hlt_sd : dgSlotDegBase gPtr vCap < 2 ^ w := by dsimp [dgSlotDegBase]; omega
  dsimp only [dgMoveSlotEdgeBodyStmt]
  suffices h : ∃ o st' c,
      Runs w p ω
        (.assign 7 (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 5))) ;;
         .assign 8 (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 5))) ;;
         .assign 9 (.bin .add (.reg 6) (.bin .mul (.const 5) (.reg 5))) ;;
         .assign 10 (.bin .add (.reg 6) (.bin .mul (.const 7) (.reg 5))) ;;
         .assign 11 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 4))) ;;
         .assign 12 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 5) (.reg 4))) ;;
         .cond (.reg 14)
           (dgMoveHalfEdgeStmt bOps true)
           (dgMoveHalfEdgeStmt bOps false)) { mem := mem₀, regs := str, pos := stp } o st' c ∧
      normalPost (fun st =>
        DgIncStateAt st.mem gPtr vCap eCap E
          (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x)
          (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) ∧
        DgSlotsOnlyModified mem₀ st.mem gPtr vCap eCap) o st' ∧
      0 + c ≤ 510 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  refine runs_seq_assign_le (v := dgETailSlotBase gPtr vCap eCap)
    (by dsimp [dgETailSlotBase, dgEPresBase] at hlt_ts ⊢; eval_expr) ?_
  refine runs_seq_assign_le (v := dgEHeadSlotBase gPtr vCap eCap)
    (by dsimp [dgEHeadSlotBase, dgEPresBase] at hlt_hs ⊢; eval_expr) ?_
  refine runs_seq_assign_le (v := dgHePrevBase gPtr vCap eCap)
    (by dsimp [dgHePrevBase, dgEPresBase] at hlt_hp ⊢; eval_expr) ?_
  refine runs_seq_assign_le (v := dgHeNextBase gPtr vCap eCap)
    (by dsimp [dgHeNextBase, dgEPresBase] at hlt_hn ⊢; eval_expr) ?_
  refine runs_seq_assign_le (v := dgIncHeadBase gPtr vCap)
    (by dsimp [dgIncHeadBase] at hlt_ih ⊢; eval_expr) ?_
  refine runs_seq_assign_le (v := dgSlotDegBase gPtr vCap)
    (by dsimp [dgSlotDegBase] at hlt_sd ⊢; eval_expr) ?_
  refine runs_cond_le (v := if isHead then 1 else 0) (by eval_expr) ?_ ?_
  · intro hne14
    have hisT : isHead = true := by cases isHead <;> simp at hne14 ⊢
    subst hisT
    refine runs_triple_le
      (dgMoveHalfEdge_triple true hpOps hw16 hbound hsSrc_lt hsDst_lt hne heE hInc)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
            simp [hr0, hr1, hr2, hr3, hr4, hr5])
      (fun o st' hq => by cases o <;> simp_all)
      (by dsimp only [Expr.size]; omega)
  · intro hez14
    have hisF : isHead = false := by cases isHead <;> simp at hez14 ⊢
    subst hisF
    refine runs_triple_le
      (dgMoveHalfEdge_triple false hpOps hw16 hbound hsSrc_lt hsDst_lt hne heE hInc)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
            simp [hr0, hr1, hr2, hr3, hr4, hr5])
      (fun o st' hq => by cases o <;> simp_all)
      (by dsimp only [Expr.size]; omega)

theorem dgMoveSlotEdge_meetsContract {w : ℕ} {p : Program} {b bOps bSplit vCap eCap : ℕ}
    {E : Finset ℕ} {slotTail slotHead : ℕ → ℕ} {isHead : Bool}
    (hp : p.HasAt b (dgSplitProcs bOps bSplit)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + dgIdxMoveSlotEdge)
      (dgMoveSlotEdgeContract w vCap eCap E slotTail slotHead isHead) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxMoveSlotEdge) (by simp [dgSplitProcs, dgIdxMoveSlotEdge]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, sSrc, sDst, e, rfl, hw16, hbound, hsSrc_lt, hsDst_lt, hne, hInc⟩
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_gp4 : gPtr + 4 < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_ec : eCap < 2 ^ w := by omega
  have hlt_7vc : 7 * vCap < 2 ^ w := by omega
  have hlt_ep : dgEPresBase gPtr vCap < 2 ^ w := by dsimp [dgEPresBase]; omega
  have he_ltw : e < 2 ^ w := hargs e (by simp)
  have hlt_is : (if isHead then 1 else 0) < 2 ^ w := by
    cases isHead <;> exact Nat.lt_of_lt_of_le (by decide) hw16
  have hvc_eq : mem gPtr = vCap := by simpa [dgVCapOff] using hInc.1
  have hec_eq : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hInc.2.1
  refine runs_start_le ?_
  dsimp only [dgSplitProcs, dgIdxMoveSlotEdge, List.getElem_cons_zero, dgMoveSlotEdgeStmt]
  refine runs_seq_assign_le (v := if isHead then 1 else 0) (by eval_expr) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := vCap) (by eval_expr)
    (by simpa [startState] using hvc_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := eCap) (by eval_expr)
    (by simpa [startState] using hec_eq)) ?_
  refine runs_seq_assign_le (v := dgEPresBase gPtr vCap) (by dsimp [dgEPresBase]; eval_expr) ?_
  refine runs_seq_cond_le (v := if e < eCap then 1 else 0) (by eval_expr) ?_ ?_
  · intro hne1
    have he_lt : e < eCap := by by_contra hc; simp [hc] at hne1
    have hlt_epe : dgEPresBase gPtr vCap + e < 2 ^ w := by dsimp [dgEPresBase]; omega
    have hep_eq : mem (dgEPresBase gPtr vCap + e) = if e ∈ E then 1 else 0 := hInc.2.2.2.1 e he_lt
    refine runs_seq_cond_le (v := if e ∈ E then 1 else 0)
        (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState] using hep_eq)) ?_ ?_
    · intro hne2
      have heE : e ∈ E := by by_contra hc; simp [hc] at hne2
      refine runs_seq_triple_le
        (dgMoveSlotEdgeBody_triple isHead hpOps hw16 hbound hsSrc_lt hsDst_lt hne heE hInc)
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> simp [startState]) ?_
      rintro stB ⟨hIncB, hfrB⟩
      refine runs_ret_le (by eval_expr) ⟨gPtr, sSrc, sDst, e, rfl, rfl, hIncB, hfrB⟩ ?_
      dsimp only [dgMoveSlotEdgeContract, Expr.size]; omega
    · intro he2
      have he_not : e ∉ E := fun hc => by simp [hc] at he2
      refine runs_seq_nop_le ?_
      refine runs_ret_le (by eval_expr) ⟨gPtr, sSrc, sDst, e, rfl, rfl, ?_,
        DgSlotsOnlyModified.refl mem gPtr vCap eCap⟩ ?_
      · exact dgIncStateAt_of_not_mem isHead he_not hInc
      · dsimp only [dgMoveSlotEdgeContract, Expr.size]; omega
  · intro he1
    have he_ge : ¬ (e < eCap) := fun hc => by simp [hc] at he1
    have he_not : e ∉ E := fun hc => he_ge (hInc.2.2.1 e hc).1
    refine runs_seq_nop_le ?_
    refine runs_ret_le (by eval_expr) ⟨gPtr, sSrc, sDst, e, rfl, rfl, ?_,
      DgSlotsOnlyModified.refl mem gPtr vCap eCap⟩ ?_
    · exact dgIncStateAt_of_not_mem isHead he_not hInc
    · dsimp only [dgMoveSlotEdgeContract, Expr.size]; omega

private lemma slotJ_step (L : List ℕ) (slot : ℕ → ℕ) (sSrc sDst j : ℕ) (hne : sSrc ≠ sDst)
    (hj : j < L.length) :
    (fun x => if x = L[j] ∧
      (if L[j] ∈ (L.take j).toFinset ∧ slot L[j] = sSrc then sDst else slot L[j]) = sSrc
      then sDst
      else (if x ∈ (L.take j).toFinset ∧ slot x = sSrc then sDst else slot x)) =
    (fun x => if x ∈ (L.take (j + 1)).toFinset ∧ slot x = sSrc then sDst else slot x) := by
  funext x
  have htake : (L.take (j + 1)).toFinset = insert L[j] (L.take j).toFinset := by
    ext y
    simp only [Finset.mem_insert, List.mem_toFinset]
    rw [List.take_succ_eq_append_getElem hj]
    simp only [List.mem_append, List.mem_singleton, or_comm]
  simp only [htake, Finset.mem_insert]
  by_cases hmem : L[j] ∈ (L.take j).toFinset <;> by_cases hslot : slot L[j] = sSrc <;>
    by_cases hxj : x = L[j] <;> simp_all [hne.symm]

theorem dgMoveSlotLoop_meetsContract {w : ℕ} {p : Program} {b bOps vCap eCap : ℕ}
    {E : Finset ℕ} {slotTail slotHead : ℕ → ℕ} {L : List ℕ} {isHead : Bool}
    (hp : p.HasAt b (dgSplitProcs bOps b)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + dgIdxMoveSlotLoop)
      (dgMoveSlotLoopContract w vCap eCap E slotTail slotHead L isHead) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxMoveSlotLoop) (by simp [dgSplitProcs, dgIdxMoveSlotLoop]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, sSrc, sDst, L_ptr, L_len, rfl, hw16, hbound, hLbound,
    hsSrc_lt, hsDst_lt, hne, hL_len, hL_at, hL_word, hL_disj, hInc⟩
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_ss : sSrc < 2 ^ w := hargs sSrc (by simp)
  have hlt_sd : sDst < 2 ^ w := hargs sDst (by simp)
  have hlt_Lp : L_ptr < 2 ^ w := hargs L_ptr (by simp)
  have hlt_Ll : L_len < 2 ^ w := hargs L_len (by simp)
  have hlt_is : (if isHead then 1 else 0) < 2 ^ w := by
    cases isHead <;> exact Nat.lt_of_lt_of_le (by decide) hw16
  let slotTailJ : ℕ → ℕ → ℕ := fun j x =>
    if isHead then slotTail x
    else if x ∈ (L.take j).toFinset ∧ slotTail x = sSrc then sDst else slotTail x
  let slotHeadJ : ℕ → ℕ → ℕ := fun j x =>
    if isHead then (if x ∈ (L.take j).toFinset ∧ slotHead x = sSrc then sDst else slotHead x)
    else slotHead x
  let Inv : ℕ → State → Prop := fun j st =>
    j ≤ L_len ∧ st.regs 0 = gPtr ∧ st.regs 1 = sSrc ∧ st.regs 2 = sDst ∧
    st.regs 3 = L_ptr ∧ st.regs 4 = L_len ∧ st.regs 5 = (if isHead then 1 else 0) ∧
    st.regs 6 = j ∧
    DgIncStateAt st.mem gPtr vCap eCap E (slotTailJ j) (slotHeadJ j) ∧
    DgSlotsOnlyModified mem st.mem gPtr vCap eCap
  have hfor := Triple.forRange_const (w := w) (p := p)
    (P := fun st => st = startState [gPtr, sSrc, sDst, L_ptr, L_len, if isHead then 1 else 0] mem pos)
    (r := 6) (lo := .const 0) (hi := .reg 4)
    (body := .assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
             .call 8 (b + dgIdxMoveSlotEdge) [.reg 0, .reg 1, .reg 2, .reg 7, .reg 5])
    (Inv := Inv) (stepBound := 615) (loVal := 0) (hiVal := L_len)
    (Nat.zero_le L_len) (by omega) (fun _ => hlt_Ll)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        DgSlotsOnlyModified.refl mem gPtr vCap eCap⟩
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp
      · simp only [slotTailJ, slotHeadJ, List.take_zero, List.toFinset_nil, Finset.notMem_empty,
          false_and, ↓reduceIte]
        cases isHead <;> exact hInc)
    (fun j st _ _ hInv => hInv.2.2.2.2.2.2.2.1)
    (fun j st _ _ hInv => by
      have : st.regs 4 = L_len := hInv.2.2.2.2.2.1
      eval_expr)
    (fun j _ hj => by
      intro st ω' ⟨hj_le, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hIncJ, hfrJ⟩
      have hj_L : j < L.length := by omega
      have hj_ltw : j < 2 ^ w := by omega
      have he_eq : st.mem (L_ptr + j) = L[j] := by
        rw [hfrJ.outside (hL_disj j hj), hL_at j hj_L]
      have he_ltw : L[j] < 2 ^ w := hL_word _ (List.getElem_mem hj_L)
      have hassign : (Expr.load (.bin .add (.reg 3) (.reg 6))).eval w st = some L[j] :=
        Expr.eval_load_of_eq (by eval_expr) he_eq
      suffices h : ∃ o st' c,
          Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
            .call 8 (b + dgIdxMoveSlotEdge) [.reg 0, .reg 1, .reg 2, .reg 7, .reg 5]) st o st' c ∧
          normalPost (fun st₁ =>
            Inv (j + 1) { st₁ with regs := Function.update st₁.regs 6 (j + 1) } ∧ st₁.regs 6 = j) o st' ∧
          0 + c ≤ 615 by
        rcases h with ⟨o, st', c, hr, hq, hc⟩
        exact ⟨o, st', c, hr, hq, by simpa using hc⟩
      refine runs_seq_assign_le hassign ?_
      let st1 : State := { st with regs := Function.update st.regs 7 L[j] }
      have hargs1 : evalArgs w st1 [.reg 0, .reg 1, .reg 2, .reg 7, .reg 5] =
          some [gPtr, sSrc, sDst, L[j], if isHead then 1 else 0] := by
        dsimp only [st1]; eval_expr
      have hpre1 : (dgMoveSlotEdgeContract w vCap eCap E (slotTailJ j) (slotHeadJ j) isHead).pre
          [gPtr, sSrc, sDst, L[j], if isHead then 1 else 0] st1.mem :=
        ⟨gPtr, sSrc, sDst, L[j], rfl, hw16, hbound, hsSrc_lt, hsDst_lt, hne, hIncJ⟩
      rcases runs_call_of_meetsContract (r := 8) (dgMoveSlotEdge_meetsContract hp hpOps)
          hargs1 (by
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro v (rfl | rfl | rfl | rfl | rfl)
            · exact hlt_gp
            · exact hlt_ss
            · exact hlt_sd
            · exact he_ltw
            · exact hlt_is)
          hpre1 ω' with ⟨st', c, v, hrun, hcpost, h8, hother, hcost⟩
      rcases hcpost with ⟨_, _, _, _, hEq', _, hInc', hfr'⟩
      cases hEq'
      refine ⟨.normal, st', c, hrun, ⟨⟨hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · simpa [st1, hr0] using hother 0 (by decide)
      · simpa [st1, hr1] using hother 1 (by decide)
      · simpa [st1, hr2] using hother 2 (by decide)
      · simpa [st1, hr3] using hother 3 (by decide)
      · simpa [st1, hr4] using hother 4 (by decide)
      · simpa [st1, hr5] using hother 5 (by decide)
      · simp
      · have hst_eq := slotJ_step L slotTail sSrc sDst j hne hj_L
        have hsh_eq := slotJ_step L slotHead sSrc sDst j hne hj_L
        cases isHead <;> dsimp only [slotTailJ, slotHeadJ] at hInc' ⊢
        · simp only [Bool.false_eq_true, ↓reduceIte] at hInc' ⊢
          rwa [hst_eq] at hInc'
        · simp only [↓reduceIte] at hInc' ⊢
          rwa [hsh_eq] at hInc'
      · exact hfrJ.trans hfr'
      · simpa [st1, hr6] using hother 6 (by decide)
      · dsimp only [dgMoveSlotEdgeContract, argsSize, Expr.size] at hcost ⊢
        omega)
  refine runs_start_le ?_
  dsimp only [dgSplitProcs, dgIdxMoveSlotLoop, dgMoveSlotLoopStmt]
  refine runs_seq_triple_le
    (Triple.mono_cost (T' := fun _ => 625 * L_len + 10) hfor
      (fun _ _ => by dsimp [Expr.size]; omega)) rfl ?_
  rintro st' ⟨_, _, _, _, _, _, _, _, hIncF, hfrF⟩
  refine runs_ret_le (by eval_expr) ?_ ?_
  · refine ⟨gPtr, sSrc, sDst, L_ptr, L_len, rfl, rfl, ?_, hfrF⟩
    have htakeF : (L.take L_len).toFinset = L.toFinset := by rw [← hL_len, List.take_length]
    dsimp only [slotTailJ, slotHeadJ] at hIncF
    cases isHead <;> simp only [Bool.false_eq_true, ↓reduceIte] at hIncF ⊢
    · rwa [htakeF] at hIncF
    · rwa [htakeF] at hIncF
  · dsimp only [dgMoveSlotLoopContract, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
