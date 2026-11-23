module

public import MinCostFlow.DynSpanner.Program.DynGraphEdges
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Dynamic graph edge deletion verification (`DynGraphDelete`)

This file proves the Word-RAM contract for `dgDeleteEdgeStmt bOps` (`dgEdgeProcs bOps` at index
`dgIdxDeleteEdge = 1`): swap-with-last removal from `eList`/`ePos` and doubly-linked-list removal of
both half-edges `2 * e` and `2 * e + 1` in `O(1)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

private lemma dgDeleteEdgePart1_triple {w : ℕ} {p : Program}
    {gPtr e vCap eCap : ℕ} {G : MGraph} {mem₀ : ℕ → ℕ}
    {eL : List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (he_lt : e < eCap) (heE : e ∈ G.E)
    (hG : DynGraphAt mem₀ gPtr vCap eCap G)
    (heL_len : eL.length = G.m) (_heL_nd : eL.Nodup) (heL_mem : ∀ x, x ∈ eL ↔ x ∈ G.E)
    (heL_at : ListAt mem₀ (dgEListBase gPtr vCap eCap) eL)
    (heL_pos : ∀ i (hi : i < eL.length), mem₀ (dgEPosBase gPtr vCap eCap + eL[i]) = i) :
    let pos := eL.idxOf e
    let m' := G.m - 1
    let last := eL[m']'(by dsimp only [m']; rw [heL_len]; exact Nat.sub_lt (Finset.card_pos.mpr ⟨e, heE⟩) Nat.one_pos)
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = vCap ∧
        st.regs 3 = eCap ∧ st.mem = mem₀)
      dgDeleteEdgePart1Stmt
      (normalPost fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = vCap ∧
        st.regs 3 = eCap ∧ st.regs 6 = dgEPresBase gPtr vCap ∧ st.regs 7 = m' ∧
        st.regs 8 = pos ∧ st.regs 9 = last ∧
        st.mem = Function.update
          (Function.update
            (Function.update
              (Function.update mem₀ (dgEPresBase gPtr vCap + e) 0)
              (gPtr + 3) m')
            (dgEListBase gPtr vCap eCap + pos) last)
          (dgEPosBase gPtr vCap eCap + last) pos)
      (fun _ => 115) := by
  intro pos m' last st _ ⟨hr0, hr1, hr2, hr3, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hm_pos : 0 < G.m := Finset.card_pos.mpr ⟨e, heE⟩
  have hm_le : G.m ≤ eCap := by
    have hsub : G.E ⊆ Finset.range eCap := fun x hx => Finset.mem_range.mpr (hG.2.2.1 x hx)
    simpa [MGraph.m] using Finset.card_le_card hsub
  have he_mem : e ∈ eL := (heL_mem e).mpr heE
  have hpos_lt : pos < G.m := heL_len ▸ List.idxOf_lt_length_of_mem he_mem
  have he_at_pos : eL[pos]'(by omega) = e := List.getElem_idxOf (List.idxOf_lt_length_of_mem he_mem)
  have hpos_eq : mem₀ (dgEPosBase gPtr vCap eCap + e) = pos := by
    have h := heL_pos pos (by omega)
    simpa [he_at_pos] using h
  have hlast_E : last ∈ G.E := (heL_mem _).mp (List.getElem_mem _)
  have hlast_lt : last < eCap := hG.2.2.1 last hlast_E
  have hlast_eq : mem₀ (dgEListBase gPtr vCap eCap + m') = last := heL_at m' (by omega)
  have hm_eq : mem₀ (gPtr + 3) = G.m := by simpa [dgMOff] using hG.2.2.2.2.2.2.1
  have hlt_ep : dgEPresBase gPtr vCap < 2 ^ w := by dsimp [dgEPresBase]; omega
  have hlt_ep_e : dgEPresBase gPtr vCap + e < 2 ^ w := by dsimp [dgEPresBase]; omega
  have hlt_m3 : gPtr + 3 < 2 ^ w := by omega
  have hlt_m : G.m < 2 ^ w := by omega
  have hlt_epos_e : dgEPosBase gPtr vCap eCap + e < 2 ^ w := by dsimp [dgEPosBase]; omega
  have hlt_el_m' : dgEListBase gPtr vCap eCap + m' < 2 ^ w := by dsimp [dgEListBase]; omega
  have hlt_el_pos : dgEListBase gPtr vCap eCap + pos < 2 ^ w := by dsimp [dgEListBase]; omega
  have hlt_epos_last : dgEPosBase gPtr vCap eCap + last < 2 ^ w := by dsimp [dgEPosBase]; omega
  have hlt_pos_w : pos < 2 ^ w := by omega
  have hlt_last_w : last < 2 ^ w := by omega
  have hlt_m'_w : m' < 2 ^ w := by omega
  have hm1_m : (Function.update mem₀ (gPtr + 4 + 7 * vCap + e) 0) (gPtr + 3) = G.m := by
    rw [Function.update_of_ne (by omega), hm_eq]
  have hm2_pos : (Function.update (Function.update mem₀ (gPtr + 4 + 7 * vCap + e) 0) (gPtr + 3) m')
      (dgEPosBase gPtr vCap eCap + e) = pos := by
    rw [Function.update_of_ne (by dsimp [dgEPosBase]; omega),
        Function.update_of_ne (by dsimp [dgEPosBase]; omega), hpos_eq]
  have hm2_last : (Function.update (Function.update mem₀ (gPtr + 4 + 7 * vCap + e) 0) (gPtr + 3) m')
      (dgEListBase gPtr vCap eCap + m') = last := by
    rw [Function.update_of_ne (by dsimp [dgEListBase]; omega),
        Function.update_of_ne (by dsimp [dgEListBase]; omega), hlast_eq]
  refine runs_start_le ?_
  dsimp only [dgDeleteEdgePart1Stmt]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_store_le (by dsimp only [dgEPresBase]; eval_expr) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_sub
    (Expr.eval_load_of_eq (v := G.m) (by eval_expr) (by simpa using hm1_m))
    (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := pos) (by dsimp only [dgEPresBase]; eval_expr)
    (by simpa [dgEPosBase, dgEPresBase] using hm2_pos)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := last) (by dsimp only [dgEPresBase]; eval_expr)
    (by simpa [dgEListBase, dgEPresBase] using hm2_last)) ?_
  refine runs_seq_store_le (by dsimp only [dgEPresBase]; eval_expr) (by eval_expr) ?_
  refine runs_store_le (by dsimp only [dgEPresBase]; eval_expr) (by eval_expr) ?_ (by simp [Expr.size])
  dsimp only [normalPost, dgEPresBase, dgEListBase, dgEPosBase]
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;> simp [hr0, hr1, hr2, hr3]

private lemma dgDeleteEdgePart2_triple {w : ℕ} {p : Program}
    {gPtr e vCap eCap su sv : ℕ} {mem₁ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (he_lt : e < eCap)
    (hsu_eq : mem₁ (dgETailSlotBase gPtr vCap eCap + e) = su)
    (hsv_eq : mem₁ (dgEHeadSlotBase gPtr vCap eCap + e) = sv)
    (_hsu_lt : su < 2 ^ w) (_hsv_lt : sv < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = vCap ∧
        st.regs 3 = eCap ∧ st.regs 6 = dgEPresBase gPtr vCap ∧ st.mem = mem₁)
      dgDeleteEdgePart2Stmt
      (normalPost fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = vCap ∧
        st.regs 3 = eCap ∧ st.regs 4 = su ∧ st.regs 5 = sv ∧
        st.regs 10 = dgHePrevBase gPtr vCap eCap ∧ st.regs 11 = dgHeNextBase gPtr vCap eCap ∧
        st.regs 12 = dgIncHeadBase gPtr vCap ∧ st.regs 13 = dgSlotDegBase gPtr vCap ∧
        st.mem = mem₁)
      (fun _ => 95) := by
  intro st _ ⟨hr0, hr1, hr2, hr3, hr6, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hr6 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_ec : eCap < 2 ^ w := by omega
  have hlt_ep : gPtr + 4 + 7 * vCap < 2 ^ w := by omega
  have hlt_ts : dgETailSlotBase gPtr vCap eCap + e < 2 ^ w := by dsimp [dgETailSlotBase]; omega
  have hlt_hs : dgEHeadSlotBase gPtr vCap eCap + e < 2 ^ w := by dsimp [dgEHeadSlotBase]; omega
  have hlt_hp : dgHePrevBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
  have hlt_hn : dgHeNextBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
  have hlt_ih : dgIncHeadBase gPtr vCap < 2 ^ w := by dsimp [dgIncHeadBase]; omega
  have hlt_sd : dgSlotDegBase gPtr vCap < 2 ^ w := by dsimp [dgSlotDegBase]; omega
  have hr6' : str 6 = gPtr + 4 + 7 * vCap := hr6
  refine runs_start_le ?_
  dsimp only [dgDeleteEdgePart2Stmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := su) (by eval_expr)
    (by dsimp only [dgETailSlotBase, dgEPresBase] at hsu_eq; exact hsu_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := sv) (by eval_expr)
    (by dsimp only [dgEHeadSlotBase, dgEPresBase] at hsv_eq; exact hsv_eq)) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_assign_le (by eval_expr) ?_ (by simp [Expr.size])
  dsimp only [normalPost, dgHePrevBase, dgHeNextBase, dgIncHeadBase, dgSlotDegBase]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> simp [hr0, hr1, hr2, hr3]

private lemma dgDeleteEdge_post_dynGraphAt {gPtr vCap eCap e su sv : ℕ}
    {G : MGraph} {mem₀ mem1 mem2 mem3 : ℕ → ℕ} {eL : List ℕ} {incL : ℕ → List ℕ}
    (he_lt : e < eCap) (heE : e ∈ G.E)
    (hG : DynGraphAt mem₀ gPtr vCap eCap G)
    (heL_len : eL.length = G.m) (heL_nd : eL.Nodup) (heL_mem : ∀ x, x ∈ eL ↔ x ∈ G.E)
    (heL_at : ListAt mem₀ (dgEListBase gPtr vCap eCap) eL)
    (heL_pos : ∀ i (hi : i < eL.length), mem₀ (dgEPosBase gPtr vCap eCap + eL[i]) = i)
    (hsu_eq : mem₀ (dgETailSlotBase gPtr vCap eCap + e) = su)
    (hsv_eq : mem₀ (dgEHeadSlotBase gPtr vCap eCap + e) = sv)
    (hsu_lt : su < vCap) (hsv_lt : sv < vCap)
    (hinc_orig : ∀ s < vCap,
      IsDoublyLinkedList mem₀ (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem₀ (dgSlotDegBase gPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔
        h < 2 * eCap ∧ h / 2 ∈ G.E ∧
        (if h % 2 = 0 then mem₀ (dgETailSlotBase gPtr vCap eCap + h / 2)
         else mem₀ (dgEHeadSlotBase gPtr vCap eCap + h / 2)) = s)
    (hmem1 : let pos := eL.idxOf e; let m' := G.m - 1
      let last := eL[m']'(by dsimp only [m']; rw [heL_len]; exact Nat.sub_lt (Finset.card_pos.mpr ⟨e, heE⟩) Nat.one_pos)
      mem1 = Function.update
        (Function.update
          (Function.update
            (Function.update mem₀ (dgEPresBase gPtr vCap + e) 0)
            (gPtr + 3) m')
          (dgEListBase gPtr vCap eCap + pos) last)
        (dgEPosBase gPtr vCap eCap + last) pos)
    (hc1_dll : IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + su) (2 * eCap) ((incL su).erase (2 * e)))
    (hc1_deg : mem2 (dgSlotDegBase gPtr vCap + su) = mem1 (dgSlotDegBase gPtr vCap + su) - 1)
    (hc1_fr : ∀ addr, (∀ x, addr = dgHePrevBase gPtr vCap eCap + x → x ∉ incL su) →
      (∀ x, addr = dgHeNextBase gPtr vCap eCap + x → x ∉ incL su) →
      addr ≠ dgIncHeadBase gPtr vCap + su → addr ≠ dgSlotDegBase gPtr vCap + su → mem2 addr = mem1 addr)
    (hc2_dll : IsDoublyLinkedList mem3 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sv) (2 * eCap)
      ((if su = sv then (incL su).erase (2 * e) else incL sv).erase (2 * e + 1)))
    (hc2_deg : mem3 (dgSlotDegBase gPtr vCap + sv) = mem2 (dgSlotDegBase gPtr vCap + sv) - 1)
    (hc2_fr : ∀ addr, (∀ x, addr = dgHePrevBase gPtr vCap eCap + x →
        x ∉ (if su = sv then (incL su).erase (2 * e) else incL sv)) →
      (∀ x, addr = dgHeNextBase gPtr vCap eCap + x →
        x ∉ (if su = sv then (incL su).erase (2 * e) else incL sv)) →
      addr ≠ dgIncHeadBase gPtr vCap + sv → addr ≠ dgSlotDegBase gPtr vCap + sv → mem3 addr = mem2 addr) :
    DynGraphAt mem3 gPtr vCap eCap (G.applyUpdate (.delete e)) ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem3 addr = mem₀ addr := by
  dsimp only at hmem1
  have hm_pos : 0 < G.m := Finset.card_pos.mpr ⟨e, heE⟩
  have hm_le : G.m ≤ eCap := by
    have hsub : G.E ⊆ Finset.range eCap := fun x hx => Finset.mem_range.mpr (hG.2.2.1 x hx)
    simpa [MGraph.m] using Finset.card_le_card hsub
  set pos := eL.idxOf e
  set m' := G.m - 1
  set last := eL[m']'(by omega)
  have he_mem : e ∈ eL := (heL_mem e).mpr heE
  have hpos_lt : pos < G.m := heL_len ▸ List.idxOf_lt_length_of_mem he_mem
  have hlast_lt : last < eCap := hG.2.2.1 last ((heL_mem _).mp (List.getElem_mem _))
  have hm1_mem0 : ∀ addr,
      addr ≠ dgEPresBase gPtr vCap + e →
      addr ≠ dgEListBase gPtr vCap eCap + pos →
      addr ≠ dgEPosBase gPtr vCap eCap + last →
      addr ≠ gPtr + 3 →
      mem1 addr = mem₀ addr := by
    intro addr h1 h2 h3 h4
    rw [hmem1,
        Function.update_of_ne h3,
        Function.update_of_ne h2,
        Function.update_of_ne h4,
        Function.update_of_ne h1]
  have hc2_hlt : ∀ x ∈ (if su = sv then (incL su).erase (2 * e) else incL sv), x < 2 * eCap := by
    intro x hx
    split_ifs at hx
    · exact (hinc_orig su hsu_lt).1.2.1 x (List.mem_of_mem_erase hx)
    · exact (hinc_orig sv hsv_lt).1.2.1 x hx
  have hm3_outside_dll : ∀ addr,
      (∀ x < 2 * eCap, addr ≠ dgHePrevBase gPtr vCap eCap + x ∧ addr ≠ dgHeNextBase gPtr vCap eCap + x) →
      (∀ s < vCap, addr ≠ dgIncHeadBase gPtr vCap + s ∧ addr ≠ dgSlotDegBase gPtr vCap + s) →
      mem3 addr = mem1 addr := by
    intro addr hhe hs
    rw [hc2_fr addr (fun x hEq hx => (hhe x (hc2_hlt x hx)).1 hEq)
        (fun x hEq hx => (hhe x (hc2_hlt x hx)).2 hEq)
        (hs sv hsv_lt).1 (hs sv hsv_lt).2,
        hc1_fr addr (fun x hEq hx => (hhe x ((hinc_orig su hsu_lt).1.2.1 x hx)).1 hEq)
        (fun x hEq hx => (hhe x ((hinc_orig su hsu_lt).1.2.1 x hx)).2 hEq)
        (hs su hsu_lt).1 (hs su hsu_lt).2]
  have hm3_preserves_early : ∀ addr, addr < dgSlotDegBase gPtr vCap → addr ≠ gPtr + 3 →
      mem3 addr = mem₀ addr := by
    intro addr hlt h3
    rw [hm3_outside_dll addr
      (fun x hx => ⟨by dsimp [dgSlotDegBase, dgHePrevBase] at *; omega,
                    by dsimp [dgSlotDegBase, dgHeNextBase] at *; omega⟩)
      (fun s hs => ⟨by dsimp [dgSlotDegBase, dgIncHeadBase] at *; omega,
                    by dsimp [dgSlotDegBase] at *; omega⟩)]
    exact hm1_mem0 addr
      (by dsimp [dgSlotDegBase, dgEPresBase] at *; omega)
      (by dsimp [dgSlotDegBase, dgEListBase] at *; omega)
      (by dsimp [dgSlotDegBase, dgEPosBase] at *; omega)
      h3
  rcases hG with ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_at, hvL_pos⟩, heti0, hite0, hep0, ⟨_, _, _, _, _, _⟩, hets_ehs, _⟩
  have hn_le : G.n ≤ vCap := by
    rw [← hvL_len]
    exact nodup_length_le_cap hvL_nd (fun x hx => hvCap x ((hvL_mem x).mp hx))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e' he'
    exact hval e' (Finset.mem_erase.mp he').2
  · exact hvCap
  · intro e' he'
    exact heCap e' (Finset.mem_erase.mp he').2
  · rw [hm3_preserves_early _ (by dsimp [dgVCapOff, dgSlotDegBase]; omega) (by dsimp [dgVCapOff]; omega)]
    exact h0
  · rw [hm3_preserves_early _ (by dsimp [dgECapOff, dgSlotDegBase]; omega) (by dsimp [dgECapOff]; omega)]
    exact h1
  · rw [hm3_preserves_early _ (by dsimp [dgNOff, dgSlotDegBase]; omega) (by dsimp [dgNOff]; omega)]
    exact h2
  · dsimp only [MGraph.applyUpdate, MGraph.m, dgMOff]
    rw [Finset.card_erase_of_mem heE]
    rw [hm3_outside_dll _
      (fun x _ => ⟨by dsimp [dgHePrevBase]; omega, by dsimp [dgHeNextBase]; omega⟩)
      (fun s _ => ⟨by dsimp [dgIncHeadBase]; omega, by dsimp [dgSlotDegBase]; omega⟩),
      hmem1,
      Function.update_of_ne (by dsimp [dgEPosBase]; omega),
      Function.update_of_ne (by dsimp [dgEListBase]; omega),
      Function.update_self]
    rfl
  · intro x hx
    dsimp only [MGraph.applyUpdate]
    rw [hm3_preserves_early _ (by dsimp [dgVPresBase, dgSlotDegBase]; omega) (by dsimp [dgVPresBase]; omega)]
    exact hvp0 x hx
  · refine ⟨vL, hvL_len, hvL_nd, hvL_mem, ?_, ?_⟩
    · intro i hi
      rw [hm3_preserves_early _ (by dsimp [dgVListBase, dgSlotDegBase]; omega) (by dsimp [dgVListBase]; omega)]
      exact hvL_at i hi
    · intro i hi
      have hv_lt := hvCap _ ((hvL_mem _).mp (List.getElem_mem hi))
      rw [hm3_preserves_early _ (by dsimp [dgVPosBase, dgSlotDegBase]; omega) (by dsimp [dgVPosBase]; omega)]
      exact hvL_pos i hi
  · intro x hx
    dsimp only [MGraph.applyUpdate] at hx ⊢
    rcases heti0 x hx with ⟨hsV, hinv⟩
    have hx_lt := hvCap x hx
    have hs_lt := hvCap _ hsV
    rw [hm3_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
        hm3_preserves_early _ (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega) (by dsimp [dgIntToExtBase]; omega)]
    exact ⟨hsV, hinv⟩
  · intro s hs
    dsimp only [MGraph.applyUpdate] at hs ⊢
    rcases hite0 s hs with ⟨hxV, hinv⟩
    have hs_lt := hvCap s hs
    have hx_lt := hvCap _ hxV
    rw [hm3_preserves_early _ (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega) (by dsimp [dgIntToExtBase]; omega),
        hm3_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega)]
    exact ⟨hxV, hinv⟩
  · intro e' he'
    dsimp only [MGraph.applyUpdate]
    rw [hm3_outside_dll _
      (fun x _ => ⟨by dsimp [dgEPresBase, dgHePrevBase]; omega, by dsimp [dgEPresBase, dgHeNextBase]; omega⟩)
      (fun s hs => ⟨by dsimp [dgEPresBase, dgIncHeadBase]; omega, by dsimp [dgEPresBase, dgSlotDegBase]; omega⟩),
      hmem1,
      Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase]; omega),
      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase]; omega),
      Function.update_of_ne (by dsimp [dgEPresBase]; omega)]
    by_cases hee : e' = e
    · subst hee; simp [Function.update_self]
    · simp only [Finset.mem_erase, hee, ne_eq, not_false_eq_true, true_and]
      rw [Function.update_of_ne (by omega)]
      exact hep0 e' he'
  · rcases eList_swap_delete heL_len heL_nd heL_mem heE with ⟨hpos_lt', heL'_len, heL'_nd, heL'_mem, hget⟩
    let eL' := if pos = m' then eL.take m' else (eL.take m').set pos last
    refine ⟨eL', heL'_len, heL'_nd, fun x => by simp only [MGraph.applyUpdate]; exact heL'_mem x, ?_, ?_⟩
    · intro i hi
      have him : i < m' := by rw [heL'_len, Finset.card_erase_of_mem heE] at hi; exact hi
      rw [hget i him]
      rw [hm3_outside_dll _
        (fun x _ => ⟨by dsimp [dgEListBase, dgHePrevBase]; omega, by dsimp [dgEListBase, dgHeNextBase]; omega⟩)
        (fun s hs => ⟨by dsimp [dgEListBase, dgIncHeadBase]; omega, by dsimp [dgEListBase, dgSlotDegBase]; omega⟩),
        hmem1, Function.update_of_ne (by dsimp [dgEListBase, dgEPosBase]; omega)]
      by_cases hip : i = pos
      · have hip' : i = List.idxOf e eL := hip
        rw [show (if i = List.idxOf e eL then eL[G.m - 1] else eL[i]'(by omega)) = last from by
          split_ifs; rfl]
        dsimp only [pos, last]
        rw [show dgEListBase gPtr vCap eCap + i = dgEListBase gPtr vCap eCap + List.idxOf e eL from
          congrArg (dgEListBase gPtr vCap eCap + ·) hip', Function.update_self]
      · simp only [pos, hip, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [dgEListBase]; omega),
            Function.update_of_ne (by dsimp [dgEListBase, dgEPresBase]; omega)]
        exact heL_at i (by omega)
    · intro i hi
      have him : i < m' := by rw [heL'_len, Finset.card_erase_of_mem heE] at hi; exact hi
      have heLi_lt : eL'[i] < eCap := heCap _ (Finset.mem_erase.mp ((heL'_mem _).mp (List.getElem_mem hi))).2
      rw [hm3_outside_dll _
        (fun x _ => ⟨by dsimp [dgEPosBase, dgHePrevBase]; omega, by dsimp [dgEPosBase, dgHeNextBase]; omega⟩)
        (fun s hs => ⟨by dsimp [dgEPosBase, dgIncHeadBase]; omega, by dsimp [dgEPosBase, dgSlotDegBase]; omega⟩),
        hmem1]
      rw [hget i him]
      by_cases hip : i = pos
      · have hip' : i = List.idxOf e eL := hip
        rw [show (if i = List.idxOf e eL then eL[G.m - 1] else eL[i]'(by omega)) = last from by
          split_ifs; rfl]
        dsimp only [pos, last]
        rw [Function.update_self, ← hip']
      · simp only [pos, hip, ↓reduceIte]
        have hne_last : eL[i] ≠ last := by
          intro hEq
          have hinj := heL_nd.getElem_inj_iff.mp (hEq : eL[i] = eL[m'])
          omega
        rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp [dgEPosBase, dgEListBase]; omega),
            Function.update_of_ne (by dsimp [dgEPosBase]; omega),
            Function.update_of_ne (by dsimp [dgEPosBase, dgEPresBase]; omega)]
        exact heL_pos i (by omega)
  · intro e' he'
    dsimp only [MGraph.applyUpdate] at he' ⊢
    rcases Finset.mem_erase.mp he' with ⟨_, heG⟩
    have he'_lt := heCap e' heG
    have htu_lt := hvCap _ (hval e' heG).1
    have hhv_lt := hvCap _ (hval e' heG).2
    constructor
    · rw [hm3_outside_dll _
        (fun x _ => ⟨by dsimp [dgETailSlotBase, dgHePrevBase]; omega, by dsimp [dgETailSlotBase, dgHeNextBase]; omega⟩)
        (fun s hs => ⟨by dsimp [dgETailSlotBase, dgIncHeadBase]; omega, by dsimp [dgETailSlotBase, dgSlotDegBase]; omega⟩),
        hm3_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
        hm1_mem0 _ (by dsimp [dgETailSlotBase, dgEPresBase]; omega)
          (by dsimp [dgETailSlotBase, dgEListBase]; omega) (by dsimp [dgETailSlotBase, dgEPosBase]; omega)
          (by dsimp [dgETailSlotBase]; omega)]
      exact (hets_ehs e' heG).1
    · rw [hm3_outside_dll _
        (fun x _ => ⟨by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega, by dsimp [dgEHeadSlotBase, dgHeNextBase]; omega⟩)
        (fun s hs => ⟨by dsimp [dgEHeadSlotBase, dgIncHeadBase]; omega, by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega⟩),
        hm3_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
        hm1_mem0 _ (by dsimp [dgEHeadSlotBase, dgEPresBase]; omega)
          (by dsimp [dgEHeadSlotBase, dgEListBase]; omega) (by dsimp [dgEHeadSlotBase, dgEPosBase]; omega)
          (by dsimp [dgEHeadSlotBase]; omega)]
      exact (hets_ehs e' heG).2
  · let incL' : ℕ → List ℕ := fun s =>
      let s1 := if s = su then (incL s).erase (2 * e) else incL s
      if s = sv then s1.erase (2 * e + 1) else s1
    refine ⟨incL', fun s hs => ?_⟩
    have hdisj_s : ∀ s₁ s₂, s₁ < vCap → s₂ < vCap → s₁ ≠ s₂ → ∀ x, x ∈ incL s₁ → x ∉ incL s₂ := by
      intro s₁ s₂ hs1 hs2 hne x hx1 hx2
      have h1 := ((hinc_orig s₁ hs1).2.2 x).mp hx1
      have h2 := ((hinc_orig s₂ hs2).2.2 x).mp hx2
      exact hne (h1.2.2.symm.trans h2.2.2)
    have h2e_su : 2 * e ∈ incL su := ((hinc_orig su hsu_lt).2.2 (2 * e)).mpr
      ⟨by omega, by simpa [Nat.mul_div_right _ (by omega : 0 < 2)] using heE,
       by simp [Nat.mul_div_right _ (by omega : 0 < 2), Nat.mul_mod_right, hsu_eq]⟩
    have h2e1_sv : 2 * e + 1 ∈ incL sv := ((hinc_orig sv hsv_lt).2.2 (2 * e + 1)).mpr
      ⟨by omega, by simpa [show (2 * e + 1) / 2 = e by omega] using heE,
       by simp [show (2 * e + 1) / 2 = e by omega, show (2 * e + 1) % 2 = 1 by omega, hsv_eq]⟩
    have h2e_notin_ne : ∀ s' < vCap, s' ≠ su → 2 * e ∉ incL s' := fun s' hs' hne hc =>
      hdisj_s su s' hsu_lt hs' hne.symm (2 * e) h2e_su hc
    have h2e1_notin_ne : ∀ s' < vCap, s' ≠ sv → 2 * e + 1 ∉ incL s' := fun s' hs' hne hc =>
      hdisj_s sv s' hsv_lt hs' hne.symm (2 * e + 1) h2e1_sv hc
    have hm1_dll : ∀ s' < vCap,
        IsDoublyLinkedList mem1 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
          (dgIncHeadBase gPtr vCap + s') (2 * eCap) (incL s') ∧
        mem1 (dgSlotDegBase gPtr vCap + s') = (incL s').length := by
      intro s' hs'
      have ho := hinc_orig s' hs'
      refine ⟨ho.1.of_agree ?_ ?_ ?_, ?_⟩
      · rw [hm1_mem0 _ (by dsimp [dgIncHeadBase, dgEPresBase]; omega)
          (by dsimp [dgIncHeadBase, dgEListBase]; omega) (by dsimp [dgIncHeadBase, dgEPosBase]; omega)
          (by dsimp [dgIncHeadBase]; omega)]
      · intro x hx; rw [hm1_mem0 _ (by dsimp [dgHePrevBase, dgEPresBase]; omega)
          (by dsimp [dgHePrevBase, dgEListBase]; omega) (by dsimp [dgHePrevBase, dgEPosBase]; omega)
          (by dsimp [dgHePrevBase]; omega)]
      · intro x hx; rw [hm1_mem0 _ (by dsimp [dgHeNextBase, dgEPresBase]; omega)
          (by dsimp [dgHeNextBase, dgEListBase]; omega) (by dsimp [dgHeNextBase, dgEPosBase]; omega)
          (by dsimp [dgHeNextBase]; omega)]
      · rw [hm1_mem0 _ (by dsimp [dgSlotDegBase, dgEPresBase]; omega)
          (by dsimp [dgSlotDegBase, dgEListBase]; omega) (by dsimp [dgSlotDegBase, dgEPosBase]; omega)
          (by dsimp [dgSlotDegBase]; omega), ho.2.1]
    have hm2_dll_ne : ∀ s' < vCap, s' ≠ su →
        IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
          (dgIncHeadBase gPtr vCap + s') (2 * eCap) (incL s') ∧
        mem2 (dgSlotDegBase gPtr vCap + s') = (incL s').length := by
      intro s' hs' hne
      have hm1s := hm1_dll s' hs'
      refine ⟨hm1s.1.of_agree ?_ ?_ ?_, ?_⟩
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := (hinc_orig su hsu_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := (hinc_orig su hsu_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by
            rw [← Nat.add_left_cancel hEq] at hy
            exact hdisj_s su s' hsu_lt hs' hne.symm x hy hx)
          (fun y hEq hy => by
            have hlt_x := hm1s.1.2.1 x hx; have hlt_y := (hinc_orig su hsu_lt).1.2.1 y hy
            dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgHePrevBase, dgIncHeadBase]; omega) (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by
            have hlt_x := hm1s.1.2.1 x hx; have hlt_y := (hinc_orig su hsu_lt).1.2.1 y hy
            dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
          (fun y hEq hy => by
            rw [← Nat.add_left_cancel hEq] at hy
            exact hdisj_s su s' hsu_lt hs' hne.symm x hy hx)
          (by dsimp [dgHeNextBase, dgIncHeadBase]; omega) (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)]
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := (hinc_orig su hsu_lt).1.2.1 x hx; dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := (hinc_orig su hsu_lt).1.2.1 x hx; dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega) (by dsimp [dgSlotDegBase]; omega), hm1s.2]
    refine ⟨?_, ?_, ?_⟩
    · by_cases hssv : s = sv
      · subst hssv
        by_cases hsuv : su = s
        · simp only [incL', ↓reduceIte, hsuv.symm]
          simpa only [hsuv, ↓reduceIte] using hc2_dll
        · simp only [incL', ↓reduceIte, Ne.symm hsuv]
          simpa only [hsuv, ↓reduceIte] using hc2_dll
      · simp only [incL', hssv, ↓reduceIte]
        have hnotin_2 : ∀ y ∈ (if s = su then (incL s).erase (2 * e) else incL s),
            y ∉ (if su = sv then (incL su).erase (2 * e) else incL sv) := by
          intro y hy hc
          have hy_orig : y ∈ incL s := by
            split_ifs at hy
            · exact List.mem_of_mem_erase hy
            · exact hy
          split_ifs at hc with huv
          · by_cases hsu : s = su
            · exact absurd (hsu.trans huv) hssv
            · exact hdisj_s su s hsu_lt hs (Ne.symm hsu) y (List.mem_of_mem_erase hc) hy_orig
          · exact hdisj_s sv s hsv_lt hs (Ne.symm hssv) y hc hy_orig
        have h2s : IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
            (dgIncHeadBase gPtr vCap + s) (2 * eCap)
            (if s = su then (incL s).erase (2 * e) else incL s) := by
          split_ifs with hssu
          · subst hssu; exact hc1_dll
          · exact (hm2_dll_ne s hs hssu).1
        refine h2s.of_agree ?_ ?_ ?_
        · rw [hc2_fr _ (fun x hEq hx => by
              have hlt := hc2_hlt x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
            (fun x hEq hx => by
              have hlt := hc2_hlt x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
            (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)]
        · intro x hx
          rw [hc2_fr _ (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin_2 x hx hy)
            (fun y hEq hy => by
              have hlt_x := h2s.2.1 x hx; have hlt_y := hc2_hlt y hy
              dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
            (by dsimp [dgHePrevBase, dgIncHeadBase]; omega) (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)]
        · intro x hx
          rw [hc2_fr _ (fun y hEq hy => by
              have hlt_x := h2s.2.1 x hx; have hlt_y := hc2_hlt y hy
              dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
            (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin_2 x hx hy)
            (by dsimp [dgHeNextBase, dgIncHeadBase]; omega) (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)]
    · by_cases hssv : s = sv
      · subst hssv
        rw [hc2_deg]
        by_cases hsuv : su = s
        · subst hsuv
          simp only [incL', ↓reduceIte, hc1_deg, (hm1_dll su hsu_lt).2]
          have h2e1_er : 2 * e + 1 ∈ (incL su).erase (2 * e) :=
            List.mem_erase_of_ne (by omega) |>.mpr h2e1_sv
          rw [List.length_erase_of_mem h2e1_er, List.length_erase_of_mem h2e_su]
        · simp only [incL', ↓reduceIte, Ne.symm hsuv, (hm2_dll_ne s hs (Ne.symm hsuv)).2,
            List.length_erase_of_mem h2e1_sv]
      · rw [hc2_fr _ (fun x hEq hx => by
            have hlt := hc2_hlt x hx; dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := hc2_hlt x hx; dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega) (by dsimp [dgSlotDegBase]; omega)]
        by_cases hssu : s = su
        · subst hssu
          simp only [incL', hssv, ↓reduceIte, hc1_deg, (hm1_dll s hs).2, List.length_erase_of_mem h2e_su]
        · simp only [incL', hssv, hssu, ↓reduceIte, (hm2_dll_ne s hs hssu).2]
    · intro h
      by_cases h2e : h = 2 * e
      · subst h2e
        have hdiv : (2 * e) / 2 = e := Nat.mul_div_right _ (by omega)
        simp only [incL', hdiv, MGraph.applyUpdate, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
          and_false, iff_false]
        by_cases hssu : s = su
        · subst hssu
          simp only [↓reduceIte]
          intro hc
          split_ifs at hc
          · exact (hinc_orig s hs).1.1.not_mem_erase (List.mem_of_mem_erase hc)
          · exact (hinc_orig s hs).1.1.not_mem_erase hc
        · simp only [hssu, ↓reduceIte]
          intro hc
          split_ifs at hc
          · exact h2e_notin_ne s hs hssu (List.mem_of_mem_erase hc)
          · exact h2e_notin_ne s hs hssu hc
      · by_cases h2e1 : h = 2 * e + 1
        · subst h2e1
          have hdiv : (2 * e + 1) / 2 = e := by omega
          simp only [incL', hdiv, MGraph.applyUpdate, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
            and_false, iff_false]
          by_cases hssv : s = sv
          · subst hssv
            simp only [↓reduceIte]
            intro hc
            split_ifs at hc
            · exact ((hinc_orig s hs).1.1.erase (2 * e)).not_mem_erase hc
            · exact (hinc_orig s hs).1.1.not_mem_erase hc
          · simp only [hssv, ↓reduceIte]
            intro hc
            split_ifs at hc
            · exact h2e1_notin_ne s hs hssv (List.mem_of_mem_erase hc)
            · exact h2e1_notin_ne s hs hssv hc
        · have hne_e : h / 2 ≠ e := half_ne_of_ne_pair h2e h2e1
          have hmem_iff_orig : h ∈ incL' s ↔ h ∈ incL s := by
            dsimp only [incL']
            split_ifs <;> simp [List.mem_erase_of_ne, h2e, h2e1]
          rw [hmem_iff_orig, (hinc_orig s hs).2.2 h]
          dsimp only [MGraph.applyUpdate]
          simp only [Finset.mem_erase, hne_e, ne_eq, not_false_eq_true, true_and]
          by_cases hlt2 : h < 2 * eCap
          · have hd2 : h / 2 < eCap := by omega
            have hslot_eq :
                (if h % 2 = 0 then mem3 (dgETailSlotBase gPtr vCap eCap + h / 2)
                 else mem3 (dgEHeadSlotBase gPtr vCap eCap + h / 2)) =
                (if h % 2 = 0 then mem₀ (dgETailSlotBase gPtr vCap eCap + h / 2)
                 else mem₀ (dgEHeadSlotBase gPtr vCap eCap + h / 2)) := by
              split_ifs <;>
              · rw [hm3_outside_dll _
                  (fun x hx => ⟨by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase]; omega,
                    by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgHeNextBase]; omega⟩)
                  (fun s' hs' => ⟨by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgIncHeadBase]; omega,
                    by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgSlotDegBase]; omega⟩),
                  hm1_mem0 _
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgEPresBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgEListBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgEPosBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega)]
            rw [hslot_eq]
          · constructor <;> intro hc <;> exact absurd hc.1 hlt2
  · intro addr haddr
    rw [hm3_outside_dll _
      (fun x hx => ⟨by dsimp [dgHePrevBase, dynGraphSize] at *; omega,
        by dsimp [dgHeNextBase, dynGraphSize] at *; omega⟩)
      (fun s hs => ⟨by dsimp [dgIncHeadBase, dynGraphSize] at *; omega,
        by dsimp [dgSlotDegBase, dynGraphSize] at *; omega⟩),
      hm1_mem0 _
        (by dsimp [dgEPresBase, dynGraphSize] at *; omega)
        (by dsimp [dgEListBase, dynGraphSize] at *; omega)
        (by dsimp [dgEPosBase, dynGraphSize] at *; omega)
        (by dsimp [dynGraphSize] at *; omega)]

private lemma dgDeleteEdgeBody_triple {w : ℕ} {p : Program} {bOps : ℕ}
    {gPtr e vCap eCap : ℕ} {G : MGraph} {mem₀ : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (he_lt : e < eCap) (heE : e ∈ G.E)
    (hG : DynGraphAt mem₀ gPtr vCap eCap G) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = vCap ∧
        st.regs 3 = eCap ∧ st.mem = mem₀)
      (dgDeleteEdgePart1Stmt ;;
       dgDeleteEdgePart2Stmt ;;
       .call 14 (bOps + dgIdxDllRemove)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 4), .bin .add (.reg 13) (.reg 4),
          .bin .mul (.const 2) (.reg 1)] ;;
       .call 14 (bOps + dgIdxDllRemove)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 5), .bin .add (.reg 13) (.reg 5),
          .bin .add (.bin .mul (.const 2) (.reg 1)) (.const 1)])
      (normalPost fun st =>
        DynGraphAt st.mem gPtr vCap eCap (G.applyUpdate (.delete e)) ∧
        ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem₀ addr)
      (fun _ => 400) := by
  intro st ω ⟨hr0, hr1, hr2, hr3, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  rcases hG with ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_at, hvL_pos⟩, heti0, hite0, hep0, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩,
    hets_ehs, ⟨incL, hincL⟩⟩
  have hG' : DynGraphAt mem₀ gPtr vCap eCap G :=
    ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, hvL_pos⟩,
     heti0, hite0, hep0, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩, hets_ehs, ⟨incL, hincL⟩⟩
  have hm_pos : 0 < G.m := Finset.card_pos.mpr ⟨e, heE⟩
  have hm_le : G.m ≤ eCap := by
    have hsub : G.E ⊆ Finset.range eCap := fun x hx => Finset.mem_range.mpr (heCap x hx)
    simpa [MGraph.m] using Finset.card_le_card hsub
  set pos := eL.idxOf e
  set m' := G.m - 1
  set last := eL[m']'(by omega)
  have he_mem : e ∈ eL := (heL_mem e).mpr heE
  have hpos_lt : pos < G.m := heL_len ▸ List.idxOf_lt_length_of_mem he_mem
  have hlast_lt : last < eCap := heCap last ((heL_mem _).mp (List.getElem_mem _))
  set su := mem₀ (dgETailSlotBase gPtr vCap eCap + e)
  set sv := mem₀ (dgEHeadSlotBase gPtr vCap eCap + e)
  have hsu_V : su ∈ G.V := by
    rw [show su = mem₀ (dgExtToIntBase gPtr vCap + G.tail e) from (hets_ehs e heE).1]
    exact (heti0 _ (hval e heE).1).1
  have hsv_V : sv ∈ G.V := by
    rw [show sv = mem₀ (dgExtToIntBase gPtr vCap + G.head e) from (hets_ehs e heE).2]
    exact (heti0 _ (hval e heE).2).1
  have hsu_lt : su < vCap := hvCap su hsu_V
  have hsv_lt : sv < vCap := hvCap sv hsv_V
  have hsu_ltw : su < 2 ^ w := by omega
  have hsv_ltw : sv < 2 ^ w := by omega
  set mem1 := Function.update
    (Function.update
      (Function.update
        (Function.update mem₀ (dgEPresBase gPtr vCap + e) 0)
        (gPtr + 3) m')
      (dgEListBase gPtr vCap eCap + pos) last)
    (dgEPosBase gPtr vCap eCap + last) pos
  have hm1_su : mem1 (dgETailSlotBase gPtr vCap eCap + e) = su := by
    simp only [mem1]
    rw [Function.update_of_ne (by dsimp [dgETailSlotBase, dgEPosBase]; omega),
        Function.update_of_ne (by dsimp [dgETailSlotBase, dgEListBase]; omega),
        Function.update_of_ne (by dsimp [dgETailSlotBase]; omega),
        Function.update_of_ne (by dsimp [dgETailSlotBase, dgEPresBase]; omega)]
  have hm1_sv : mem1 (dgEHeadSlotBase gPtr vCap eCap + e) = sv := by
    simp only [mem1]
    rw [Function.update_of_ne (by dsimp [dgEHeadSlotBase, dgEPosBase]; omega),
        Function.update_of_ne (by dsimp [dgEHeadSlotBase, dgEListBase]; omega),
        Function.update_of_ne (by dsimp [dgEHeadSlotBase]; omega),
        Function.update_of_ne (by dsimp [dgEHeadSlotBase, dgEPresBase]; omega)]
  have hm1_eq0 : ∀ addr, dgHePrevBase gPtr vCap eCap ≤ addr → mem1 addr = mem₀ addr := by
    intro addr hge
    simp only [mem1]
    rw [Function.update_of_ne (by dsimp [dgHePrevBase, dgEPosBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase, dgEListBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase, dgEPresBase] at *; omega)]
  have hm1_eq0_low : ∀ addr, dgSlotDegBase gPtr vCap ≤ addr → addr < dgEPresBase gPtr vCap →
      mem1 addr = mem₀ addr := by
    intro addr _ hlt
    simp only [mem1]
    rw [Function.update_of_ne (by dsimp [dgEPosBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by dsimp [dgEListBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by dsimp [dgSlotDegBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by omega)]
  have hm1_dll : ∀ s < vCap,
      IsDoublyLinkedList mem1 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem1 (dgSlotDegBase gPtr vCap + s) = (incL s).length := by
    intro s hs
    have ho := hincL s hs
    refine ⟨ho.1.of_agree ?_ ?_ ?_, ?_⟩
    · exact hm1_eq0_low _ (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)
        (by dsimp [dgIncHeadBase, dgEPresBase]; omega)
    · intro x _; exact hm1_eq0 _ (by dsimp [dgHePrevBase]; omega)
    · intro x _; exact hm1_eq0 _ (by dsimp [dgHeNextBase, dgHePrevBase]; omega)
    · rw [hm1_eq0_low _ (by omega) (by dsimp [dgSlotDegBase, dgEPresBase]; omega), ho.2.1]
  have h2e_su : 2 * e ∈ incL su := ((hincL su hsu_lt).2.2 (2 * e)).mpr
    ⟨by omega, by simpa [Nat.mul_div_right _ (by omega : 0 < 2)] using heE,
     by simp only [Nat.mul_div_right _ (by omega : 0 < 2), Nat.mul_mod_right, ↓reduceIte]; rfl⟩
  have h2e1_sv : 2 * e + 1 ∈ incL sv := ((hincL sv hsv_lt).2.2 (2 * e + 1)).mpr
    ⟨by omega, by simpa [show (2 * e + 1) / 2 = e by omega] using heE,
     by simp only [show (2 * e + 1) / 2 = e by omega, show (2 * e + 1) % 2 = 1 by omega,
       Nat.one_ne_zero, ↓reduceIte]; rfl⟩
  have hlt_hp_cap : dgHePrevBase gPtr vCap eCap + 2 * eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
  have hlt_hn_cap : dgHeNextBase gPtr vCap eCap + 2 * eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
  have hlt_ih_u : dgIncHeadBase gPtr vCap + su < 2 ^ w := by dsimp [dgIncHeadBase]; omega
  have hlt_sd_u : dgSlotDegBase gPtr vCap + su < 2 ^ w := by dsimp [dgSlotDegBase]; omega
  have hlt_ih_v : dgIncHeadBase gPtr vCap + sv < 2 ^ w := by dsimp [dgIncHeadBase]; omega
  have hlt_sd_v : dgSlotDegBase gPtr vCap + sv < 2 ^ w := by dsimp [dgSlotDegBase]; omega
  refine runs_start_le ?_
  refine runs_seq_triple_le
    (dgDeleteEdgePart1_triple hw16 hbound he_lt heE hG' heL_len heL_nd heL_mem heL_at heL_pos)
    ⟨hr0, hr1, hr2, hr3, rfl⟩ ?_
  rintro st₁ ⟨hr10, hr11, hr12, hr13, hr16, _, _, _, hmem1_st⟩
  refine runs_seq_triple_le
    (dgDeleteEdgePart2_triple hw16 hbound he_lt hm1_su hm1_sv hsu_ltw hsv_ltw)
    ⟨hr10, hr11, hr12, hr13, hr16, hmem1_st⟩ ?_
  rintro st₂ ⟨hr20, hr21, hr22, hr23, hr24, hr25, hr2_10, hr2_11, hr2_12, hr2_13, hmem2_st⟩
  have hsu_len : (incL su).length < 2 ^ w := by
    have := nodup_length_le_cap (hincL su hsu_lt).1.1 (hincL su hsu_lt).1.2.1; omega
  have hargs1 : evalArgs w st₂
      [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 4), .bin .add (.reg 13) (.reg 4),
       .bin .mul (.const 2) (.reg 1)] =
      some [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
        dgIncHeadBase gPtr vCap + su, dgSlotDegBase gPtr vCap + su, 2 * e] := by
    have hlt_hp0 : dgHePrevBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
    have hlt_hn0 : dgHeNextBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
    have hlt_ih0 : dgIncHeadBase gPtr vCap < 2 ^ w := by dsimp [dgIncHeadBase]; omega
    have hlt_sd0 : dgSlotDegBase gPtr vCap < 2 ^ w := by dsimp [dgSlotDegBase]; omega
    have he_ltw : e < 2 ^ w := by omega
    eval_expr
  have hpre_c1 : (dgDllRemoveContract w (2 * eCap) (incL su)).pre
      [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
       dgIncHeadBase gPtr vCap + su, dgSlotDegBase gPtr vCap + su, 2 * e] st₂.mem := by
    rw [hmem2_st]
    refine ⟨dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
      dgIncHeadBase gPtr vCap + su, dgSlotDegBase gPtr vCap + su, 2 * e, rfl,
      hw16, hlt_hp_cap, hlt_hn_cap, hlt_ih_u, hlt_sd_u, (hm1_dll su hsu_lt).1, h2e_su,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [(hm1_dll su hsu_lt).2]; exact hsu_len
    · dsimp [dgIncHeadBase, dgSlotDegBase]; omega
    · intro x hx; constructor <;> [dsimp [dgHePrevBase, dgIncHeadBase]; dsimp [dgHePrevBase, dgSlotDegBase]] <;> omega
    · intro x hx; constructor <;> [dsimp [dgHeNextBase, dgIncHeadBase]; dsimp [dgHeNextBase, dgSlotDegBase]] <;> omega
    · intro x y hEq _ _; dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega
  refine runs_seq_call_le (dgDllRemove_meetsContract hpOps) hargs1
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl) <;> omega)
    hpre_c1 ?_
  rintro v1 mem2 pos2 ⟨hb1, hb2, hb3, hb4, hb5, hEq1, _, hc1_dll, hc1_deg, hc1_fr⟩
  simp only [List.cons.injEq, and_true] at hEq1
  rcases hEq1 with ⟨h1, h2, h3, h4, h5⟩
  subst h1 h2 h3 h4 h5
  rw [hmem2_st] at hc1_deg hc1_fr
  let st₃ : State := { mem := mem2, regs := Function.update st₂.regs 14 v1, pos := pos2 }
  let L₂ := if su = sv then (incL su).erase (2 * e) else incL sv
  have hm2_sv : IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sv) (2 * eCap) L₂ ∧
      mem2 (dgSlotDegBase gPtr vCap + sv) = L₂.length := by
    by_cases hsuv : su = sv
    · rw [show L₂ = (incL su).erase (2 * e) by dsimp only [L₂]; split_ifs; rfl]
      rw [← hsuv]
      refine ⟨hc1_dll, ?_⟩
      rw [hc1_deg, (hm1_dll su hsu_lt).2, List.length_erase_of_mem h2e_su]
    · simp only [L₂, hsuv, ↓reduceIte]
      have hm1v := hm1_dll sv hsv_lt
      have hdisj : ∀ y ∈ incL sv, y ∉ incL su := fun y hy hc =>
        hsuv ((((hincL su hsu_lt).2.2 y).mp hc).2.2.symm.trans (((hincL sv hsv_lt).2.2 y).mp hy).2.2)
      refine ⟨hm1v.1.of_agree ?_ ?_ ?_, ?_⟩
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := (hincL su hsu_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := (hincL su hsu_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hdisj x hx hy)
          (fun y hEq hy => by
            have hlt_x := hm1v.1.2.1 x hx; have hlt_y := (hincL su hsu_lt).1.2.1 y hy
            dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgHePrevBase, dgIncHeadBase]; omega) (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by
            have hlt_x := hm1v.1.2.1 x hx; have hlt_y := (hincL su hsu_lt).1.2.1 y hy
            dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
          (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hdisj x hx hy)
          (by dsimp [dgHeNextBase, dgIncHeadBase]; omega) (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)]
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := (hincL su hsu_lt).1.2.1 x hx; dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := (hincL su hsu_lt).1.2.1 x hx; dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega) (by dsimp [dgSlotDegBase]; omega), hm1v.2]
  have h2e1_L2 : 2 * e + 1 ∈ L₂ := by
    dsimp only [L₂]; split_ifs with hsuv
    · exact List.mem_erase_of_ne (by omega) |>.mpr (hsuv ▸ h2e1_sv)
    · exact h2e1_sv
  have hL2_len : L₂.length < 2 ^ w := by
    have := nodup_length_le_cap hm2_sv.1.1 hm2_sv.1.2.1; omega
  have hargs2 : evalArgs w st₃
      [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 5), .bin .add (.reg 13) (.reg 5),
       .bin .add (.bin .mul (.const 2) (.reg 1)) (.const 1)] =
      some [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
        dgIncHeadBase gPtr vCap + sv, dgSlotDegBase gPtr vCap + sv, 2 * e + 1] := by
    have hlt_hp0 : dgHePrevBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
    have hlt_hn0 : dgHeNextBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
    have hlt_ih0 : dgIncHeadBase gPtr vCap < 2 ^ w := by dsimp [dgIncHeadBase]; omega
    have hlt_sd0 : dgSlotDegBase gPtr vCap < 2 ^ w := by dsimp [dgSlotDegBase]; omega
    have he_ltw : e < 2 ^ w := by omega
    have hr3_10 : st₃.regs 10 = dgHePrevBase gPtr vCap eCap := by simp [st₃, hr2_10]
    have hr3_11 : st₃.regs 11 = dgHeNextBase gPtr vCap eCap := by simp [st₃, hr2_11]
    have hr3_12 : st₃.regs 12 = dgIncHeadBase gPtr vCap := by simp [st₃, hr2_12]
    have hr3_13 : st₃.regs 13 = dgSlotDegBase gPtr vCap := by simp [st₃, hr2_13]
    have hr3_5 : st₃.regs 5 = sv := by simp [st₃, hr25]
    have hr3_1 : st₃.regs 1 = e := by simp [st₃, hr21]
    eval_expr
  have hpre_c2 : (dgDllRemoveContract w (2 * eCap) L₂).pre
      [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
       dgIncHeadBase gPtr vCap + sv, dgSlotDegBase gPtr vCap + sv, 2 * e + 1] st₃.mem := by
    refine ⟨dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
      dgIncHeadBase gPtr vCap + sv, dgSlotDegBase gPtr vCap + sv, 2 * e + 1, rfl,
      hw16, hlt_hp_cap, hlt_hn_cap, hlt_ih_v, hlt_sd_v, hm2_sv.1, h2e1_L2,
      ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [st₃]; rw [hm2_sv.2]; exact hL2_len
    · dsimp [dgIncHeadBase, dgSlotDegBase]; omega
    · intro x hx; constructor <;> [dsimp [dgHePrevBase, dgIncHeadBase]; dsimp [dgHePrevBase, dgSlotDegBase]] <;> omega
    · intro x hx; constructor <;> [dsimp [dgHeNextBase, dgIncHeadBase]; dsimp [dgHeNextBase, dgSlotDegBase]] <;> omega
    · intro x y hEq _ _; dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega
  rcases runs_call_of_meetsContract (r := 14) (dgDllRemove_meetsContract hpOps)
      hargs2
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl) <;> omega)
      hpre_c2 ω with
    ⟨st₄, c₂, v2, hr₂, ⟨hc1, hc2, hc3, hc4, hc5, hEq2, _, hc2_dll, hc2_deg, hc2_fr⟩, _, _, hcost₂⟩
  simp only [List.cons.injEq, and_true] at hEq2
  rcases hEq2 with ⟨h1', h2', h3', h4', h5'⟩
  subst h1' h2' h3' h4' h5'
  refine ⟨.normal, st₄, c₂, hr₂, ?_, ?_⟩
  · dsimp only [normalPost]
    exact dgDeleteEdge_post_dynGraphAt he_lt heE hG' heL_len heL_nd heL_mem heL_at heL_pos
      rfl rfl hsu_lt hsv_lt hincL rfl hc1_dll hc1_deg hc1_fr hc2_dll hc2_deg hc2_fr
  · dsimp only [dgDllRemoveContract, argsSize, Expr.size] at hcost₂ ⊢
    omega

theorem dgDeleteEdge_meetsContract {w : ℕ} {p : Program} {b bOps vCap eCap : ℕ} {G : MGraph}
    (hp : p.HasAt b (dgEdgeProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + dgIdxDeleteEdge) (dgDeleteEdgeContract w vCap eCap G) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxDeleteEdge) (by simp [dgEdgeProcs, dgIdxDeleteEdge]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, e, rfl, hw16, hbound, hG⟩
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_ec : eCap < 2 ^ w := by omega
  have he_arg_lt : e < 2 ^ w := hargs e (by simp)
  have hvc_eq : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hec_eq : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  refine runs_start_le ?_
  dsimp only [dgEdgeProcs, dgIdxDeleteEdge, List.getElem_cons_succ, List.getElem_cons_zero, dgDeleteEdgeStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := vCap) (by eval_expr)
    (by simpa [startState] using hvc_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := eCap) (by eval_expr)
    (by simpa [startState] using hec_eq)) ?_
  have hcond1 : (Expr.bin .lt (.reg 1) (.reg 3)).eval w
      { mem := mem,
        regs := Function.update (Function.update (startState [gPtr, e] mem pos).regs 2 vCap) 3 eCap,
        pos := pos } = some (if e < eCap then 1 else 0) := by
    eval_expr
  refine runs_seq_cond_le hcond1 ?_ ?_
  · intro hne
    have he_lt : e < eCap := by by_contra hc; simp [hc] at hne
    have hep_eq : mem (dgEPresBase gPtr vCap + e) = if e ∈ G.E then 1 else 0 :=
      hG.2.2.2.2.2.2.2.2.2.2.2.1 e he_lt
    have hlt_ep : gPtr + 4 + 7 * vCap + e < 2 ^ w := by omega
    have hep_eval : (Expr.bin .eq (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
        (.bin .mul (.const 7) (.reg 2))) (.reg 1))) (.const 1)).eval w
        { mem := mem,
          regs := Function.update (Function.update (startState [gPtr, e] mem pos).regs 2 vCap) 3 eCap,
          pos := pos } = some (if (if e ∈ G.E then 1 else 0) = 1 then 1 else 0) := by
      refine Expr.eval_bin
        (Expr.eval_load_of_eq (by eval_expr) (by simpa [dgEPresBase] using hep_eq))
        (Expr.eval_const (by omega)) (by dsimp [BinOp.eval]; split_ifs <;> omega)
    refine runs_seq_cond_le hep_eval ?_ ?_
    · intro hne2
      have heE : e ∈ G.E := by by_contra hm; simp [hm] at hne2
      refine runs_seq_triple_le
        (dgDeleteEdgeBody_triple hpOps hw16 hbound he_lt heE hG)
        ⟨by simp [startState], by simp [startState], by simp, by simp, rfl⟩ ?_
      rintro st' ⟨hG', hfr'⟩
      refine runs_ret_le (by eval_expr) ?_ (by dsimp [dgDeleteEdgeContract, Expr.size]; omega)
      refine ⟨gPtr, e, rfl, rfl, ?_, hfr'⟩
      simpa [heE] using hG'
    · intro he2
      have he_not : e ∉ G.E := fun hm => by simp [hm] at he2
      refine runs_seq_nop_le ?_
      refine runs_ret_le (by eval_expr) ?_ (by dsimp [dgDeleteEdgeContract, Expr.size]; omega)
      refine ⟨gPtr, e, rfl, rfl, ?_, fun _ _ => rfl⟩
      dsimp only [startState]
      simpa [he_not] using hG
  · intro he1
    have he_ge : ¬ (e < eCap) := fun hc => by simp [hc] at he1
    have he_not : e ∉ G.E := fun hm => he_ge (hG.2.2.1 e hm)
    refine runs_seq_nop_le ?_
    refine runs_ret_le (by eval_expr) ?_ (by dsimp [dgDeleteEdgeContract, Expr.size]; omega)
    refine ⟨gPtr, e, rfl, rfl, ?_, fun _ _ => rfl⟩
    dsimp only [startState]
    simpa [he_not] using hG

end

end MinCostFlow.DynSpanner.Program
