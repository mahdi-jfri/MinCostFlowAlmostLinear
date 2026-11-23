module

public import MinCostFlow.DynSpanner.Program.DynGraphOpsBasic
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Dynamic graph primitive Word-RAM procedures (`DynGraphOps`)

This file implements and verifies the zero-dependency primitive Word-RAM procedures for
`DynGraphAt` and doubly-linked lists:

* `dgIdxInitEmpty` (`0`): initialize an empty `DynGraphAt` at a `ZeroFrom` pointer in `O(1)`.
* `dgIdxAddVertex` (`1`): insert a vertex `v < vCap` in `O(1)` (idempotent).
* `dgIdxDllCons` (`2`): `O(1)` cons onto a doubly-linked list (`IsDoublyLinkedList`).
* `dgIdxDllRemove` (`3`): `O(1)` removal from a doubly-linked list (`IsDoublyLinkedList`).
* `dgIdxGetTail` (`4`), `dgIdxGetHead` (`5`), `dgIdxGetDeg` (`6`): `O(1)` read-only accessors.

Each procedure is proven deterministic (`Stmt.NoRand`) and verified against a `WordRAM.Contract`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma dgAddVertexBody_triple {w : ℕ} {p : Program}
    {gPtr v vCap eCap : ℕ} {G : MGraph} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hv_lt : v < vCap) (hv_not : v ∉ G.V) (hG : DynGraphAt mem₀ gPtr vCap eCap G) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = v ∧ st.regs 2 = vCap ∧
        st.regs 3 = dgVPresBase gPtr + v ∧ st.mem = mem₀)
      dgAddVertexBodyStmt
      (normalPost fun st =>
        DynGraphAt st.mem gPtr vCap eCap { G with V := insert v G.V } ∧
        ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem₀ addr)
      (fun _ => 80) := by
  intro st _ ⟨hr0, hr1, hr2, hr3, hmem⟩
  rcases st with ⟨st_m, st_r, st_p⟩
  dsimp only at hr0 hr1 hr2 hr3 hmem
  rw [hmem] at *
  have hn_lt : G.n < vCap := by
    have hsub : G.V ⊂ Finset.range vCap := by
      rw [Finset.ssubset_iff_of_subset (fun x hx => Finset.mem_range.mpr (hG.2.1 x hx))]
      exact ⟨v, Finset.mem_range.mpr hv_lt, hv_not⟩
    simpa [MGraph.n] using Finset.card_lt_card hsub
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hmem_n : mem₀ (gPtr + 2) = G.n := by simpa [dgNOff] using hG.2.2.2.2.2.1
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_vp : dgVPresBase gPtr + v < 2 ^ w := by dsimp [dgVPresBase]; omega
  have hlt_n2 : gPtr + 2 < 2 ^ w := by omega
  have hlt_vl : gPtr + 4 + vCap + G.n < 2 ^ w := by omega
  have hlt_vpos : gPtr + 4 + 2 * vCap + v < 2 ^ w := by omega
  have hlt_eti : gPtr + 4 + 3 * vCap + v < 2 ^ w := by omega
  have hlt_ite : gPtr + 4 + 4 * vCap + v < 2 ^ w := by omega
  have hlt_n1 : G.n + 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgAddVertexBodyStmt]
  refine runs_seq_store_le (Expr.eval_reg_of_eq hr3) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by omega)) hlt_n2) ?_
  have hmem_n1 : (Function.update mem₀ (dgVPresBase gPtr + v) 1) (gPtr + 2) = G.n := by
    rw [Function.update_of_ne (by dsimp [dgVPresBase]; omega), hmem_n]
  refine runs_seq_assign_le
    (Expr.eval_load_of_eq (v := G.n) (by dsimp only; eval_expr) (by simpa using hmem_n1)) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by simp [Expr.size])
  dsimp only [normalPost]
  rcases hG with ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_at, hvL_pos⟩, heti0, hite0, hep0, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩,
    hets_ehs, ⟨incL, hincL⟩⟩
  set mem' := Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update mem₀ (dgVPresBase gPtr + v) 1)
            (gPtr + 4 + vCap + G.n) v)
          (gPtr + 4 + 2 * vCap + v) G.n)
        (gPtr + 4 + 3 * vCap + v) v)
      (gPtr + 4 + 4 * vCap + v) v)
    (gPtr + 2) (G.n + 1)
  have h_eq_mem : ∀ addr, addr ≠ dgVPresBase gPtr + v →
      addr ≠ gPtr + 4 + vCap + G.n →
      addr ≠ gPtr + 4 + 2 * vCap + v →
      addr ≠ gPtr + 4 + 3 * vCap + v →
      addr ≠ gPtr + 4 + 4 * vCap + v →
      addr ≠ gPtr + 2 →
      mem' addr = mem₀ addr := by
    intro addr ha1 ha2 ha3 ha4 ha5 ha6
    simp only [mem']
    rw [Function.update_of_ne ha6, Function.update_of_ne ha5, Function.update_of_ne ha4,
        Function.update_of_ne ha3, Function.update_of_ne ha2, Function.update_of_ne ha1]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he; exact ⟨Finset.mem_insert_of_mem (hval e he).1, Finset.mem_insert_of_mem (hval e he).2⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxG
    · exact hv_lt
    · exact hvCap x hxG
  · exact heCap
  · rw [h_eq_mem _ (by dsimp [dgVPresBase, dgVCapOff]; omega) (by dsimp [dgVCapOff]; omega)
      (by dsimp [dgVCapOff]; omega) (by dsimp [dgVCapOff]; omega) (by dsimp [dgVCapOff]; omega)
      (by dsimp [dgVCapOff]; omega)]; exact h0
  · rw [h_eq_mem _ (by dsimp [dgVPresBase, dgECapOff]; omega) (by dsimp [dgECapOff]; omega)
      (by dsimp [dgECapOff]; omega) (by dsimp [dgECapOff]; omega) (by dsimp [dgECapOff]; omega)
      (by dsimp [dgECapOff]; omega)]; exact h1
  · simp [dgNOff, MGraph.n, Finset.card_insert_of_notMem hv_not, mem']
  · rw [h_eq_mem _ (by dsimp [dgVPresBase, dgMOff]; omega) (by dsimp [dgMOff]; omega)
      (by dsimp [dgMOff]; omega) (by dsimp [dgMOff]; omega) (by dsimp [dgMOff]; omega)
      (by dsimp [dgMOff]; omega)]; exact h3
  · intro x hx
    by_cases hxv : x = v
    · subst hxv
      simp only [Finset.mem_insert_self, ↓reduceIte, mem']
      rw [Function.update_of_ne (by dsimp [dgVPresBase]; omega),
          Function.update_of_ne (by dsimp [dgVPresBase]; omega),
          Function.update_of_ne (by dsimp [dgVPresBase]; omega),
          Function.update_of_ne (by dsimp [dgVPresBase]; omega),
          Function.update_of_ne (by dsimp [dgVPresBase]; omega), Function.update_self]
    · simp only [Finset.mem_insert, hxv, false_or]
      rw [h_eq_mem _ (by dsimp [dgVPresBase]; omega) (by dsimp [dgVPresBase]; omega)
        (by dsimp [dgVPresBase]; omega) (by dsimp [dgVPresBase]; omega) (by dsimp [dgVPresBase]; omega)
        (by dsimp [dgVPresBase]; omega)]
      exact hvp0 x hx
  · refine ⟨vL ++ [v], by simp [hvL_len, MGraph.n, Finset.card_insert_of_notMem hv_not],
      List.nodup_append.mpr ⟨hvL_nd, List.nodup_singleton v, fun x hx y hy hEq => by
        simp only [List.mem_singleton] at hy; subst hy hEq; exact hv_not ((hvL_mem x).mp hx)⟩,
      fun x => by simp [hvL_mem, or_comm], ?_, ?_⟩
    · intro i hi
      simp only [List.length_append, List.length_singleton, hvL_len] at hi
      by_cases hil : i = G.n
      · subst hil
        simp only [List.getElem_append_right (by rw [hvL_len]), hvL_len, Nat.sub_self, List.getElem_singleton]
        simp only [dgVListBase, mem']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      · have hi_lt : i < vL.length := by omega
        rw [List.getElem_append_left hi_lt]
        rw [h_eq_mem _ (by dsimp [dgVListBase, dgVPresBase]; omega) (by dsimp [dgVListBase]; omega)
          (by dsimp [dgVListBase]; omega) (by dsimp [dgVListBase]; omega) (by dsimp [dgVListBase]; omega)
          (by dsimp [dgVListBase]; omega)]
        exact hvL_at i hi_lt
    · intro i hi
      simp only [List.length_append, List.length_singleton, hvL_len] at hi
      by_cases hil : i = G.n
      · subst hil
        simp only [List.getElem_append_right (by rw [hvL_len]), hvL_len, Nat.sub_self, List.getElem_singleton]
        simp only [dgVPosBase, mem']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
      · have hi_lt : i < vL.length := by omega
        have hne_v : vL[i] ≠ v := fun hEq => hv_not ((hvL_mem _).mp (hEq ▸ List.getElem_mem hi_lt))
        have hv_lt_i : vL[i] < vCap := hvCap _ ((hvL_mem _).mp (List.getElem_mem hi_lt))
        rw [List.getElem_append_left hi_lt]
        rw [h_eq_mem _ (by dsimp [dgVPosBase, dgVPresBase]; omega) (by dsimp [dgVPosBase]; omega)
          (by dsimp [dgVPosBase]; omega) (by dsimp [dgVPosBase]; omega) (by dsimp [dgVPosBase]; omega)
          (by dsimp [dgVPosBase]; omega)]
        exact hvL_pos i hi_lt
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxG
    · have h1 : mem' (dgExtToIntBase gPtr vCap + x) = x := by
        simp only [dgExtToIntBase, mem']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      have h2 : mem' (dgIntToExtBase gPtr vCap + x) = x := by
        simp only [dgIntToExtBase, mem']
        rw [Function.update_of_ne (by omega), Function.update_self]
      rw [h1, h2]
      exact ⟨Finset.mem_insert_self _ _, rfl⟩
    · have hx_lt := hvCap x hxG
      have hxv : x ≠ v := fun hEq => hv_not (hEq ▸ hxG)
      rcases heti0 x hxG with ⟨hsV, hinv⟩
      have hs_lt := hvCap _ hsV
      have hsv : mem₀ (dgExtToIntBase gPtr vCap + x) ≠ v := fun hc => hv_not (hc ▸ hsV)
      have h1 : mem' (dgExtToIntBase gPtr vCap + x) = mem₀ (dgExtToIntBase gPtr vCap + x) :=
        h_eq_mem _ (by dsimp [dgExtToIntBase, dgVPresBase]; omega) (by dsimp [dgExtToIntBase]; omega)
          (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
          (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
      have h2 : mem' (dgIntToExtBase gPtr vCap + mem₀ (dgExtToIntBase gPtr vCap + x)) =
          mem₀ (dgIntToExtBase gPtr vCap + mem₀ (dgExtToIntBase gPtr vCap + x)) :=
        h_eq_mem _ (by dsimp [dgIntToExtBase, dgVPresBase]; omega) (by dsimp [dgIntToExtBase]; omega)
          (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase]; omega)
          (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase]; omega)
      rw [h1, h2]
      exact ⟨Finset.mem_insert_of_mem hsV, hinv⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hsG
    · have h1 : mem' (dgIntToExtBase gPtr vCap + s) = s := by
        simp only [dgIntToExtBase, mem']
        rw [Function.update_of_ne (by omega), Function.update_self]
      have h2 : mem' (dgExtToIntBase gPtr vCap + s) = s := by
        simp only [dgExtToIntBase, mem']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      rw [h1, h2]
      exact ⟨Finset.mem_insert_self _ _, rfl⟩
    · have hs_lt := hvCap s hsG
      have hsv : s ≠ v := fun hEq => hv_not (hEq ▸ hsG)
      rcases hite0 s hsG with ⟨hxV, hinv⟩
      have hx_lt := hvCap _ hxV
      have hxv : mem₀ (dgIntToExtBase gPtr vCap + s) ≠ v := fun hc => hv_not (hc ▸ hxV)
      have h1 : mem' (dgIntToExtBase gPtr vCap + s) = mem₀ (dgIntToExtBase gPtr vCap + s) :=
        h_eq_mem _ (by dsimp [dgIntToExtBase, dgVPresBase]; omega) (by dsimp [dgIntToExtBase]; omega)
          (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase]; omega)
          (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase]; omega)
      have h2 : mem' (dgExtToIntBase gPtr vCap + mem₀ (dgIntToExtBase gPtr vCap + s)) =
          mem₀ (dgExtToIntBase gPtr vCap + mem₀ (dgIntToExtBase gPtr vCap + s)) :=
        h_eq_mem _ (by dsimp [dgExtToIntBase, dgVPresBase]; omega) (by dsimp [dgExtToIntBase]; omega)
          (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
          (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
      rw [h1, h2]
      exact ⟨Finset.mem_insert_of_mem hxV, hinv⟩
  · intro e he
    rw [h_eq_mem _ (by dsimp [dgEPresBase, dgVPresBase]; omega) (by dsimp [dgEPresBase]; omega)
      (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase]; omega)
      (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase]; omega)]
    exact hep0 e he
  · refine ⟨eL, heL_len, heL_nd, heL_mem, ?_, ?_⟩
    · intro i hi
      have hlt_i : i < eCap := by
        have hsub : eL.toFinset ⊆ Finset.range eCap := fun x hx =>
          Finset.mem_range.mpr (heCap x ((heL_mem x).mp (List.mem_toFinset.mp hx)))
        have hcard : eL.length ≤ eCap := by
          rw [← List.toFinset_card_of_nodup heL_nd]; simpa using Finset.card_le_card hsub
        omega
      rw [h_eq_mem _ (by dsimp [dgEListBase, dgVPresBase]; omega) (by dsimp [dgEListBase]; omega)
        (by dsimp [dgEListBase]; omega) (by dsimp [dgEListBase]; omega)
        (by dsimp [dgEListBase]; omega) (by dsimp [dgEListBase]; omega)]
      exact heL_at i hi
    · intro i hi
      have hlt_e := heCap _ ((heL_mem _).mp (List.getElem_mem hi))
      rw [h_eq_mem _ (by dsimp [dgEPosBase, dgVPresBase]; omega) (by dsimp [dgEPosBase]; omega)
        (by dsimp [dgEPosBase]; omega) (by dsimp [dgEPosBase]; omega)
        (by dsimp [dgEPosBase]; omega) (by dsimp [dgEPosBase]; omega)]
      exact heL_pos i hi
  · intro e he
    have he_lt := heCap e he
    have ht_ne : G.tail e ≠ v := fun hc => hv_not (hc ▸ (hval e he).1)
    have hh_ne : G.head e ≠ v := fun hc => hv_not (hc ▸ (hval e he).2)
    have ht_lt := hvCap _ (hval e he).1
    have hh_lt := hvCap _ (hval e he).2
    have h1 := h_eq_mem (dgETailSlotBase gPtr vCap eCap + e) (by dsimp [dgETailSlotBase, dgVPresBase]; omega)
      (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)
      (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)
      (by dsimp [dgETailSlotBase]; omega)
    have h2 := h_eq_mem (dgEHeadSlotBase gPtr vCap eCap + e) (by dsimp [dgEHeadSlotBase, dgVPresBase]; omega)
      (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
      (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
      (by dsimp [dgEHeadSlotBase]; omega)
    have h3 := h_eq_mem (dgExtToIntBase gPtr vCap + G.tail e) (by dsimp [dgExtToIntBase, dgVPresBase]; omega)
      (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
      (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
      (by dsimp [dgExtToIntBase]; omega)
    have h4 := h_eq_mem (dgExtToIntBase gPtr vCap + G.head e) (by dsimp [dgExtToIntBase, dgVPresBase]; omega)
      (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
      (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase]; omega)
      (by dsimp [dgExtToIntBase]; omega)
    rw [h1, h2, h3, h4]
    exact hets_ehs e he
  · refine ⟨incL, fun s hs => ?_⟩
    rcases hincL s hs with ⟨hdll, hsdeg, hmem_iff⟩
    have hagree : IsDoublyLinkedList mem' (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) :=
      hdll.of_agree
        (h_eq_mem _ (by dsimp [dgIncHeadBase, dgVPresBase]; omega) (by dsimp [dgIncHeadBase]; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase]; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase]; omega))
        (fun h hh => h_eq_mem _ (by dsimp [dgHePrevBase, dgVPresBase]; omega) (by dsimp [dgHePrevBase]; omega)
          (by dsimp [dgHePrevBase]; omega) (by dsimp [dgHePrevBase]; omega)
          (by dsimp [dgHePrevBase]; omega) (by dsimp [dgHePrevBase]; omega))
        (fun h hh => h_eq_mem _ (by dsimp [dgHeNextBase, dgVPresBase]; omega) (by dsimp [dgHeNextBase]; omega)
          (by dsimp [dgHeNextBase]; omega) (by dsimp [dgHeNextBase]; omega)
          (by dsimp [dgHeNextBase]; omega) (by dsimp [dgHeNextBase]; omega))
    refine ⟨hagree, ?_, fun h => ?_⟩
    · rw [h_eq_mem _ (by dsimp [dgSlotDegBase, dgVPresBase]; omega) (by dsimp [dgSlotDegBase]; omega)
        (by dsimp [dgSlotDegBase]; omega) (by dsimp [dgSlotDegBase]; omega)
        (by dsimp [dgSlotDegBase]; omega) (by dsimp [dgSlotDegBase]; omega)]
      exact hsdeg
    · rw [hmem_iff h]
      constructor
      · rintro ⟨hh2, heE, hslot⟩
        refine ⟨hh2, heE, ?_⟩
        have he_lt : h / 2 < eCap := by omega
        split_ifs at hslot ⊢
        · rw [h_eq_mem _ (by dsimp [dgETailSlotBase, dgVPresBase]; omega) (by dsimp [dgETailSlotBase]; omega)
            (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)
            (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)]
          exact hslot
        · rw [h_eq_mem _ (by dsimp [dgEHeadSlotBase, dgVPresBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
            (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
            (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)]
          exact hslot
      · rintro ⟨hh2, heE, hslot⟩
        refine ⟨hh2, heE, ?_⟩
        have he_lt : h / 2 < eCap := by omega
        split_ifs at hslot ⊢
        · rw [h_eq_mem _ (by dsimp [dgETailSlotBase, dgVPresBase]; omega) (by dsimp [dgETailSlotBase]; omega)
            (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)
            (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)] at hslot
          exact hslot
        · rw [h_eq_mem _ (by dsimp [dgEHeadSlotBase, dgVPresBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
            (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
            (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)] at hslot
          exact hslot
  · intro addr haddr
    exact h_eq_mem addr (by dsimp [dgVPresBase, dynGraphSize] at haddr ⊢; omega)
      (by dsimp [dynGraphSize] at haddr; omega) (by dsimp [dynGraphSize] at haddr; omega)
      (by dsimp [dynGraphSize] at haddr; omega) (by dsimp [dynGraphSize] at haddr; omega)
      (by dsimp [dynGraphSize] at haddr; omega)

theorem dgAddVertex_meetsContract {w : ℕ} {p : Program} {b vCap eCap : ℕ} {G : MGraph}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxAddVertex) (dgAddVertexContract w vCap eCap G) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxAddVertex) (by simp [dgOpsProcs, dgIdxAddVertex]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gPtr, v, rfl, hw16, hbound, hv_lt, hG⟩
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_vp : dgVPresBase gPtr + v < 2 ^ w := by dsimp [dgVPresBase]; omega
  have hvc_eq : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hvp_eq : mem (dgVPresBase gPtr + v) = if v ∈ G.V then 1 else 0 := hG.2.2.2.2.2.2.2.1 v hv_lt
  refine runs_start_le ?_
  dsimp only [dgOpsProcs, dgIdxAddVertex, List.getElem_cons_succ, List.getElem_cons_zero, dgAddVertexStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState] using hvc_eq)) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  have hvp_mem : (Function.update (Function.update (startState [gPtr, v] mem pos).regs 2 vCap) 3
      (gPtr + 4 + v)) 3 = gPtr + 4 + v := by simp
  refine runs_seq_cond_le
    (Expr.eval_bin (op := .eq)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hvp_mem) (by simpa [startState, dgVPresBase] using hvp_eq))
      (Expr.eval_const (by omega)) (by dsimp [BinOp.eval]; split_ifs <;> omega)) ?_ ?_
  · intro hne
    have hv_not : v ∉ G.V := by
      by_contra hmem
      simp [hmem] at hne
    refine runs_seq_triple_le (dgAddVertexBody_triple hw16 hbound hv_lt hv_not hG)
      ⟨rfl, rfl, by simp, by dsimp [dgVPresBase]; simp, rfl⟩ ?_
    rintro st₁ ⟨hG', hframe⟩
    refine runs_ret_le (by eval_expr) ⟨gPtr, v, rfl, rfl, hG', hframe⟩
      (by dsimp [dgAddVertexContract]; omega)
  · intro heq0
    have hv_mem : v ∈ G.V := by
      by_contra hnot
      simp [hnot] at heq0
    refine runs_seq_nop_le ?_
    dsimp only [startState]
    have hins : ({ G with V := insert v G.V } : MGraph) = G := by
      simp [Finset.insert_eq_of_mem hv_mem]
    refine runs_ret_le (by eval_expr) ?_ (by dsimp [dgAddVertexContract]; omega)
    dsimp only [dgAddVertexContract, startState]
    refine ⟨gPtr, v, rfl, rfl, ?_, fun _ _ => rfl⟩
    rw [hins]
    exact hG

theorem dgGetTail_meetsContract {w : ℕ} {p : Program} {b vCap eCap : ℕ} {G : MGraph}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxGetTail) (dgGetTailContract w vCap eCap G) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxGetTail) (by simp [dgOpsProcs, dgIdxGetTail]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gPtr, e, rfl, hw16, hbound, heE, hG⟩
  have he_lt := hG.2.2.1 e heE
  have htV := (hG.1 e heE).1
  have ht_lt := hG.2.1 _ htV
  have hsV := (hG.2.2.2.2.2.2.2.2.2.1 _ htV).1
  have hs_lt := hG.2.1 _ hsV
  have hvc_eq : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hec_eq : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  have hts_eq : mem (dgETailSlotBase gPtr vCap eCap + e) = mem (dgExtToIntBase gPtr vCap + G.tail e) :=
    (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heE).1
  have hite_eq : mem (dgIntToExtBase gPtr vCap + mem (dgExtToIntBase gPtr vCap + G.tail e)) = G.tail e :=
    (hG.2.2.2.2.2.2.2.2.2.1 _ htV).2
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt1 : gPtr < 2 ^ w := by omega
  have hlt2 : vCap < 2 ^ w := by omega
  have hlt3 : eCap < 2 ^ w := by omega
  have hlt4 : gPtr + 4 + 7 * vCap + 3 * eCap + e < 2 ^ w := by omega
  have hlt5 : gPtr + 4 + 4 * vCap + mem (dgExtToIntBase gPtr vCap + G.tail e) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgOpsProcs, dgIdxGetTail, List.getElem_cons_succ, List.getElem_cons_zero, dgGetTailStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState] using hvc_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState] using hec_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState, dgETailSlotBase] using hts_eq)) ?_
  refine runs_ret_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState, dgIntToExtBase] using hite_eq))
    ⟨gPtr, e, rfl, rfl, rfl⟩ (by dsimp [dgGetTailContract]; omega)

theorem dgGetHead_meetsContract {w : ℕ} {p : Program} {b vCap eCap : ℕ} {G : MGraph}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxGetHead) (dgGetHeadContract w vCap eCap G) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxGetHead) (by simp [dgOpsProcs, dgIdxGetHead]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gPtr, e, rfl, hw16, hbound, heE, hG⟩
  have he_lt := hG.2.2.1 e heE
  have hhV := (hG.1 e heE).2
  have hsV := (hG.2.2.2.2.2.2.2.2.2.1 _ hhV).1
  have hs_lt := hG.2.1 _ hsV
  have hvc_eq : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hec_eq : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  have hhs_eq : mem (dgEHeadSlotBase gPtr vCap eCap + e) = mem (dgExtToIntBase gPtr vCap + G.head e) :=
    (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heE).2
  have hite_eq : mem (dgIntToExtBase gPtr vCap + mem (dgExtToIntBase gPtr vCap + G.head e)) = G.head e :=
    (hG.2.2.2.2.2.2.2.2.2.1 _ hhV).2
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt1 : gPtr < 2 ^ w := by omega
  have hlt2 : vCap < 2 ^ w := by omega
  have hlt3 : eCap < 2 ^ w := by omega
  have hlt4 : gPtr + 4 + 7 * vCap + 4 * eCap + e < 2 ^ w := by omega
  have hlt5 : gPtr + 4 + 4 * vCap + mem (dgExtToIntBase gPtr vCap + G.head e) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgOpsProcs, dgIdxGetHead, List.getElem_cons_succ, List.getElem_cons_zero, dgGetHeadStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState] using hvc_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState] using hec_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState, dgEHeadSlotBase] using hhs_eq)) ?_
  refine runs_ret_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState, dgIntToExtBase] using hite_eq))
    ⟨gPtr, e, rfl, rfl, rfl⟩ (by dsimp [dgGetHeadContract]; omega)

theorem dgGetDeg_meetsContract {w : ℕ} {p : Program} {b vCap eCap : ℕ} {G : MGraph}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxGetDeg) (dgGetDegContract w vCap eCap G) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxGetDeg) (by simp [dgOpsProcs, dgIdxGetDeg]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gPtr, v, rfl, hw16, hbound, hvV, hG⟩
  have hv_lt := hG.2.1 v hvV
  have hsV := (hG.2.2.2.2.2.2.2.2.2.1 v hvV).1
  have hs_lt := hG.2.1 _ hsV
  have hvc_eq : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hdeg_eq : mem (dgSlotDegBase gPtr vCap + mem (dgExtToIntBase gPtr vCap + v)) = G.deg v :=
    hG.slotDeg_eq_deg hvV
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt1 : gPtr < 2 ^ w := by omega
  have hlt2 : vCap < 2 ^ w := by omega
  have hlt3 : gPtr + 4 + 3 * vCap + v < 2 ^ w := by omega
  have hlt4 : gPtr + 4 + 5 * vCap + mem (dgExtToIntBase gPtr vCap + v) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgOpsProcs, dgIdxGetDeg, List.getElem_cons_succ, List.getElem_cons_zero, dgGetDegStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) (by simpa [startState] using hvc_eq)) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_ret_le (Expr.eval_load_of_eq (by eval_expr) (by dsimp only [startState, dgExtToIntBase, dgSlotDegBase]; exact hdeg_eq))
    ⟨gPtr, v, rfl, rfl, rfl⟩ (by dsimp [dgGetDegContract]; omega)

end

end MinCostFlow.DynSpanner.Program
