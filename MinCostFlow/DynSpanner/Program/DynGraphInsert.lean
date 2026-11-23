module

public import MinCostFlow.DynSpanner.Program.DynGraphEdges
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Dynamic graph edge insertion verification (`DynGraphInsert`)

This file proves the Word-RAM contract for `dgInsertEdgeStmt bOps` (`dgEdgeProcs bOps` at index
`dgIdxInsertEdge = 0`): inserting edge `e = (u, v)` (including self-loops `u = v`) into
`DynGraphAt mem a vCap eCap G` in `O(1)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

private lemma dgInsertEdgePart1_triple {w : ℕ} {p : Program}
    {gPtr e u v vCap eCap : ℕ} {G : MGraph} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (he_lt : e < eCap) (he_not : e ∉ G.E) (hG : DynGraphAt mem₀ gPtr vCap eCap G) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = u ∧ st.regs 3 = v ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.mem = mem₀)
      dgInsertEdgePart1Stmt
      (normalPost fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = u ∧ st.regs 3 = v ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.regs 6 = dgEPresBase gPtr vCap ∧ st.regs 7 = G.m ∧
        st.mem = Function.update
          (Function.update
            (Function.update
              (Function.update mem₀ (dgEPresBase gPtr vCap + e) 1)
              (dgEListBase gPtr vCap eCap + G.m) e)
            (dgEPosBase gPtr vCap eCap + e) G.m)
          (gPtr + 3) (G.m + 1))
      (fun _ => 90) := by
  intro st _ ⟨hr0, hr1, hr2, hr3, hr4, hr5, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hmem
  rw [hmem] at *
  have hm_lt : G.m < eCap := by
    have hsub : G.E ⊂ Finset.range eCap := by
      rw [Finset.ssubset_iff_of_subset (fun x hx => Finset.mem_range.mpr (hG.2.2.1 x hx))]
      exact ⟨e, Finset.mem_range.mpr he_lt, he_not⟩
    simpa [MGraph.m] using Finset.card_lt_card hsub
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hmem_m : mem₀ (gPtr + 3) = G.m := by simpa [dgMOff] using hG.2.2.2.2.2.2.1
  have hlt_ep : gPtr + 4 + 7 * vCap < 2 ^ w := by omega
  have hlt_ep_e : gPtr + 4 + 7 * vCap + e < 2 ^ w := by omega
  have hlt_m3 : gPtr + 3 < 2 ^ w := by omega
  have hlt_el : gPtr + 4 + 7 * vCap + eCap + G.m < 2 ^ w := by omega
  have hlt_epos : gPtr + 4 + 7 * vCap + 2 * eCap + e < 2 ^ w := by omega
  have hlt_m1 : G.m + 1 < 2 ^ w := by omega
  have he_ltw : e < 2 ^ w := by omega
  have hvc_ltw : vCap < 2 ^ w := by omega
  have hec_ltw : eCap < 2 ^ w := by omega
  have hmem_m1 : (Function.update mem₀ (gPtr + 4 + 7 * vCap + e) 1) (gPtr + 3) = G.m := by
    rw [Function.update_of_ne (by omega), hmem_m]
  refine runs_start_le ?_
  dsimp only [dgInsertEdgePart1Stmt]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := G.m) (by eval_expr) (by simpa using hmem_m1)) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by simp [Expr.size])
  dsimp only [normalPost, dgEPresBase, dgEListBase, dgEPosBase]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩ <;> simp [hr0, hr1, hr2, hr3, hr4, hr5]

private lemma dgInsertEdgePart2_triple {w : ℕ} {p : Program}
    {gPtr e u v vCap eCap su sv : ℕ} {mem₁ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (he_lt : e < eCap) (hu_lt : u < vCap) (hv_lt : v < vCap)
    (hsu_eq : mem₁ (dgExtToIntBase gPtr vCap + u) = su)
    (hsv_eq : mem₁ (dgExtToIntBase gPtr vCap + v) = sv)
    (_hsu_lt : su < 2 ^ w) (_hsv_lt : sv < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = u ∧ st.regs 3 = v ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.regs 6 = dgEPresBase gPtr vCap ∧ st.mem = mem₁)
      dgInsertEdgePart2Stmt
      (normalPost fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 4 = vCap ∧ st.regs 5 = eCap ∧
        st.regs 8 = su ∧ st.regs 9 = sv ∧
        st.regs 10 = dgHePrevBase gPtr vCap eCap ∧ st.regs 11 = dgHeNextBase gPtr vCap eCap ∧
        st.regs 12 = dgIncHeadBase gPtr vCap ∧ st.regs 13 = dgSlotDegBase gPtr vCap ∧
        st.mem = Function.update
          (Function.update mem₁ (dgETailSlotBase gPtr vCap eCap + e) su)
          (dgEHeadSlotBase gPtr vCap eCap + e) sv)
      (fun _ => 110) := by
  intro st _ ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_ec : eCap < 2 ^ w := by omega
  have hlt_ep : gPtr + 4 + 7 * vCap < 2 ^ w := by omega
  have hlt_eti_u : gPtr + 4 + 3 * vCap + u < 2 ^ w := by omega
  have hlt_eti_v : gPtr + 4 + 3 * vCap + v < 2 ^ w := by omega
  have hlt_ts : gPtr + 4 + 7 * vCap + 3 * eCap + e < 2 ^ w := by omega
  have hlt_hs : gPtr + 4 + 7 * vCap + 4 * eCap + e < 2 ^ w := by omega
  have hlt_hp : gPtr + 4 + 7 * vCap + 5 * eCap < 2 ^ w := by omega
  have hlt_hn : gPtr + 4 + 7 * vCap + 7 * eCap < 2 ^ w := by omega
  have hlt_ih : gPtr + 4 + 6 * vCap < 2 ^ w := by omega
  have hlt_sd : gPtr + 4 + 5 * vCap < 2 ^ w := by omega
  have hr6' : str 6 = gPtr + 4 + 7 * vCap := hr6
  refine runs_start_le ?_
  dsimp only [dgInsertEdgePart2Stmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := su) (by eval_expr)
    (by dsimp only [dgExtToIntBase] at hsu_eq; exact hsu_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := sv) (by eval_expr)
    (by dsimp only [dgExtToIntBase] at hsv_eq; exact hsv_eq)) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_assign_le (by eval_expr) ?_ (by simp [Expr.size])
  dsimp only [normalPost, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase,
    dgIncHeadBase, dgSlotDegBase, dgEPresBase]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> simp [hr0, hr1, hr4, hr5]

private lemma dgInsertEdge_post_dynGraphAt {gPtr vCap eCap e u v su sv : ℕ}
    {G : MGraph} {mem₀ mem1 mem2 mem3 mem4 : ℕ → ℕ} {incL : ℕ → List ℕ}
    (he_lt : e < eCap) (he_not : e ∉ G.E) (huV : u ∈ G.V) (hvV : v ∈ G.V)
    (hG : DynGraphAt mem₀ gPtr vCap eCap G)
    (hsu_eq : mem₀ (dgExtToIntBase gPtr vCap + u) = su)
    (hsv_eq : mem₀ (dgExtToIntBase gPtr vCap + v) = sv)
    (hsu_lt : su < vCap) (hsv_lt : sv < vCap)
    (hinc_orig : ∀ s < vCap,
      IsDoublyLinkedList mem₀ (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem₀ (dgSlotDegBase gPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔
        h < 2 * eCap ∧ h / 2 ∈ G.E ∧
        (if h % 2 = 0 then mem₀ (dgETailSlotBase gPtr vCap eCap + h / 2)
         else mem₀ (dgEHeadSlotBase gPtr vCap eCap + h / 2)) = s)
    (hmem1 : mem1 = Function.update
      (Function.update
        (Function.update
          (Function.update mem₀ (dgEPresBase gPtr vCap + e) 1)
          (dgEListBase gPtr vCap eCap + G.m) e)
        (dgEPosBase gPtr vCap eCap + e) G.m)
      (gPtr + 3) (G.m + 1))
    (hmem2 : mem2 = Function.update
      (Function.update mem1 (dgETailSlotBase gPtr vCap eCap + e) su)
      (dgEHeadSlotBase gPtr vCap eCap + e) sv)
    (hc1_dll : IsDoublyLinkedList mem3 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + su) (2 * eCap) ((2 * e) :: incL su))
    (hc1_deg : mem3 (dgSlotDegBase gPtr vCap + su) = mem2 (dgSlotDegBase gPtr vCap + su) + 1)
    (hc1_fr : ∀ addr, (∀ x, addr = dgHePrevBase gPtr vCap eCap + x → x ∉ (2 * e) :: incL su) →
      (∀ x, addr = dgHeNextBase gPtr vCap eCap + x → x ∉ (2 * e) :: incL su) →
      addr ≠ dgIncHeadBase gPtr vCap + su → addr ≠ dgSlotDegBase gPtr vCap + su → mem3 addr = mem2 addr)
    (hc2_dll : IsDoublyLinkedList mem4 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sv) (2 * eCap)
      ((2 * e + 1) :: (if su = sv then (2 * e) :: incL su else incL sv)))
    (hc2_deg : mem4 (dgSlotDegBase gPtr vCap + sv) = mem3 (dgSlotDegBase gPtr vCap + sv) + 1)
    (hc2_fr : ∀ addr, (∀ x, addr = dgHePrevBase gPtr vCap eCap + x →
        x ∉ (2 * e + 1) :: (if su = sv then (2 * e) :: incL su else incL sv)) →
      (∀ x, addr = dgHeNextBase gPtr vCap eCap + x →
        x ∉ (2 * e + 1) :: (if su = sv then (2 * e) :: incL su else incL sv)) →
      addr ≠ dgIncHeadBase gPtr vCap + sv → addr ≠ dgSlotDegBase gPtr vCap + sv → mem4 addr = mem3 addr) :
    DynGraphAt mem4 gPtr vCap eCap (G.applyUpdate (.insert e u v)) ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem4 addr = mem₀ addr := by
  have hm_lt : G.m < eCap := by
    have hsub : G.E ⊂ Finset.range eCap := by
      rw [Finset.ssubset_iff_of_subset (fun x hx => Finset.mem_range.mpr (hG.2.2.1 x hx))]
      exact ⟨e, Finset.mem_range.mpr he_lt, he_not⟩
    simpa [MGraph.m] using Finset.card_lt_card hsub
  have hm2_mem0 : ∀ addr,
      addr ≠ dgEPresBase gPtr vCap + e →
      addr ≠ dgEListBase gPtr vCap eCap + G.m →
      addr ≠ dgEPosBase gPtr vCap eCap + e →
      addr ≠ gPtr + 3 →
      addr ≠ dgETailSlotBase gPtr vCap eCap + e →
      addr ≠ dgEHeadSlotBase gPtr vCap eCap + e →
      mem2 addr = mem₀ addr := by
    intro addr h1 h2 h3 h4 h5 h6
    have hm1_eq : mem1 addr = mem₀ addr := by
      rw [hmem1,
          Function.update_of_ne h4,
          Function.update_of_ne h3,
          Function.update_of_ne h2,
          Function.update_of_ne h1]
    rw [hmem2, Function.update_of_ne h6, Function.update_of_ne h5, hm1_eq]
  have hc2_hlt : ∀ x ∈ (2 * e + 1) :: (if su = sv then (2 * e) :: incL su else incL sv), x < 2 * eCap :=
    hc2_dll.2.1
  have hm4_outside_dll : ∀ addr,
      (∀ x < 2 * eCap, addr ≠ dgHePrevBase gPtr vCap eCap + x ∧ addr ≠ dgHeNextBase gPtr vCap eCap + x) →
      (∀ s < vCap, addr ≠ dgIncHeadBase gPtr vCap + s ∧ addr ≠ dgSlotDegBase gPtr vCap + s) →
      mem4 addr = mem2 addr := by
    intro addr hhe hs
    rw [hc2_fr addr (fun x hEq hx => (hhe x (hc2_hlt x hx)).1 hEq)
        (fun x hEq hx => (hhe x (hc2_hlt x hx)).2 hEq)
        (hs sv hsv_lt).1 (hs sv hsv_lt).2,
        hc1_fr addr (fun x hEq hx => (hhe x (hc1_dll.2.1 x hx)).1 hEq)
        (fun x hEq hx => (hhe x (hc1_dll.2.1 x hx)).2 hEq)
        (hs su hsu_lt).1 (hs su hsu_lt).2]
  have hm4_preserves_early : ∀ addr,
      addr < dgSlotDegBase gPtr vCap → addr ≠ gPtr + 3 → mem4 addr = mem₀ addr := by
    intro addr hlt h3
    rw [hm4_outside_dll addr
      (fun x hx => ⟨by dsimp [dgSlotDegBase, dgHePrevBase] at *; omega,
                    by dsimp [dgSlotDegBase, dgHeNextBase] at *; omega⟩)
      (fun s hs => ⟨by dsimp [dgSlotDegBase, dgIncHeadBase] at *; omega,
                    by dsimp [dgSlotDegBase] at *; omega⟩)]
    exact hm2_mem0 addr
      (by dsimp [dgSlotDegBase, dgEPresBase] at *; omega)
      (by dsimp [dgSlotDegBase, dgEListBase] at *; omega)
      (by dsimp [dgSlotDegBase, dgEPosBase] at *; omega)
      h3
      (by dsimp [dgSlotDegBase, dgETailSlotBase] at *; omega)
      (by dsimp [dgSlotDegBase, dgEHeadSlotBase] at *; omega)
  rcases hG with ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_at, hvL_pos⟩, heti0, hite0, hep0, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩,
    hets_ehs, _⟩
  have hu_lt : u < vCap := hvCap u huV
  have hv_lt : v < vCap := hvCap v hvV
  have hn_le : G.n ≤ vCap := by
    rw [← hvL_len]
    exact nodup_length_le_cap hvL_nd (fun x hx => hvCap x ((hvL_mem x).mp hx))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e' he'
    rcases Finset.mem_insert.mp he' with rfl | heG
    · simp [MGraph.applyUpdate, huV, hvV]
    · have hne : e' ≠ e := fun hEq => he_not (hEq ▸ heG)
      simp only [MGraph.applyUpdate, Function.update_of_ne hne]
      exact hval e' heG
  · exact hvCap
  · intro e' he'
    rcases Finset.mem_insert.mp he' with rfl | heG
    · exact he_lt
    · exact heCap e' heG
  · rw [hm4_preserves_early _ (by dsimp [dgVCapOff, dgSlotDegBase]; omega) (by dsimp [dgVCapOff]; omega)]
    exact h0
  · rw [hm4_preserves_early _ (by dsimp [dgECapOff, dgSlotDegBase]; omega) (by dsimp [dgECapOff]; omega)]
    exact h1
  · rw [hm4_preserves_early _ (by dsimp [dgNOff, dgSlotDegBase]; omega) (by dsimp [dgNOff]; omega)]
    exact h2
  · dsimp only [MGraph.applyUpdate, MGraph.m, dgMOff]
    rw [Finset.card_insert_of_notMem he_not]
    rw [hm4_outside_dll _
      (fun x _ => ⟨by dsimp [dgHePrevBase]; omega, by dsimp [dgHeNextBase]; omega⟩)
      (fun s _ => ⟨by dsimp [dgIncHeadBase]; omega, by dsimp [dgSlotDegBase]; omega⟩),
      hmem2, Function.update_of_ne (by dsimp [dgEHeadSlotBase]; omega),
      Function.update_of_ne (by dsimp [dgETailSlotBase]; omega), hmem1, Function.update_self]
    rfl
  · intro x hx
    dsimp only [MGraph.applyUpdate]
    rw [hm4_preserves_early _ (by dsimp [dgVPresBase, dgSlotDegBase]; omega) (by dsimp [dgVPresBase]; omega)]
    exact hvp0 x hx
  · refine ⟨vL, hvL_len, hvL_nd, hvL_mem, ?_, ?_⟩
    · intro i hi
      rw [hm4_preserves_early _ (by dsimp [dgVListBase, dgSlotDegBase]; omega) (by dsimp [dgVListBase]; omega)]
      exact hvL_at i hi
    · intro i hi
      have hv_lt := hvCap _ ((hvL_mem _).mp (List.getElem_mem hi))
      rw [hm4_preserves_early _ (by dsimp [dgVPosBase, dgSlotDegBase]; omega) (by dsimp [dgVPosBase]; omega)]
      exact hvL_pos i hi
  · intro x hx
    dsimp only [MGraph.applyUpdate] at hx ⊢
    rcases heti0 x hx with ⟨hsV, hinv⟩
    have hx_lt := hvCap x hx
    have hs_lt := hvCap _ hsV
    rw [hm4_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
        hm4_preserves_early _ (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega) (by dsimp [dgIntToExtBase]; omega)]
    exact ⟨hsV, hinv⟩
  · intro s hs
    dsimp only [MGraph.applyUpdate] at hs ⊢
    rcases hite0 s hs with ⟨hxV, hinv⟩
    have hs_lt := hvCap s hs
    have hx_lt := hvCap _ hxV
    rw [hm4_preserves_early _ (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega) (by dsimp [dgIntToExtBase]; omega),
        hm4_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega)]
    exact ⟨hxV, hinv⟩
  · intro e' he'
    dsimp only [MGraph.applyUpdate]
    rw [hm4_outside_dll _
      (fun x _ => ⟨by dsimp [dgEPresBase, dgHePrevBase]; omega, by dsimp [dgEPresBase, dgHeNextBase]; omega⟩)
      (fun s hs => ⟨by dsimp [dgEPresBase, dgIncHeadBase]; omega, by dsimp [dgEPresBase, dgSlotDegBase]; omega⟩),
      hmem2, Function.update_of_ne (by dsimp [dgEPresBase, dgEHeadSlotBase]; omega),
      Function.update_of_ne (by dsimp [dgEPresBase, dgETailSlotBase]; omega), hmem1,
      Function.update_of_ne (by dsimp [dgEPresBase]; omega),
      Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase]; omega),
      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase]; omega)]
    by_cases hee : e' = e
    · subst hee; simp [Function.update_self]
    · simp only [Finset.mem_insert, hee, false_or]
      rw [Function.update_of_ne (by omega)]
      exact hep0 e' he'
  · refine ⟨eL ++ [e], by simp [MGraph.applyUpdate, MGraph.m, heL_len, Finset.card_insert_of_notMem he_not],
      List.nodup_append.mpr ⟨heL_nd, List.nodup_singleton e, fun x hx y hy hEq => by
        simp only [List.mem_singleton] at hy; subst hy hEq; exact he_not ((heL_mem x).mp hx)⟩,
      fun x => by simp [MGraph.applyUpdate, heL_mem, or_comm], ?_, ?_⟩
    · intro i hi
      simp only [List.length_append, List.length_singleton, heL_len] at hi
      rw [hm4_outside_dll _
        (fun x _ => ⟨by dsimp [dgEListBase, dgHePrevBase]; omega, by dsimp [dgEListBase, dgHeNextBase]; omega⟩)
        (fun s hs => ⟨by dsimp [dgEListBase, dgIncHeadBase]; omega, by dsimp [dgEListBase, dgSlotDegBase]; omega⟩),
        hmem2, Function.update_of_ne (by dsimp [dgEListBase, dgEHeadSlotBase]; omega),
        Function.update_of_ne (by dsimp [dgEListBase, dgETailSlotBase]; omega), hmem1,
        Function.update_of_ne (by dsimp [dgEListBase]; omega),
        Function.update_of_ne (by dsimp [dgEListBase, dgEPosBase]; omega)]
      by_cases him : i = G.m
      · subst him
        simp only [List.getElem_append_right (by rw [heL_len]), heL_len, Nat.sub_self,
          List.getElem_singleton, Function.update_self]
      · have hi_lt : i < eL.length := by omega
        rw [List.getElem_append_left hi_lt, Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp [dgEListBase, dgEPresBase]; omega)]
        exact heL_at i hi_lt
    · intro i hi
      simp only [List.length_append, List.length_singleton, heL_len] at hi
      by_cases him : i = G.m
      · subst him
        simp only [List.getElem_append_right (by rw [heL_len]), heL_len, Nat.sub_self, List.getElem_singleton]
        rw [hm4_outside_dll _
          (fun x _ => ⟨by dsimp [dgEPosBase, dgHePrevBase]; omega, by dsimp [dgEPosBase, dgHeNextBase]; omega⟩)
          (fun s hs => ⟨by dsimp [dgEPosBase, dgIncHeadBase]; omega, by dsimp [dgEPosBase, dgSlotDegBase]; omega⟩),
          hmem2, Function.update_of_ne (by dsimp [dgEPosBase, dgEHeadSlotBase]; omega),
          Function.update_of_ne (by dsimp [dgEPosBase, dgETailSlotBase]; omega), hmem1,
          Function.update_of_ne (by dsimp [dgEPosBase]; omega), Function.update_self]
      · have hi_lt : i < eL.length := by omega
        have he_lt_i : eL[i] < eCap := heCap _ ((heL_mem _).mp (List.getElem_mem hi_lt))
        have hne_e : eL[i] ≠ e := fun hEq => he_not ((heL_mem _).mp (hEq ▸ List.getElem_mem hi_lt))
        rw [List.getElem_append_left hi_lt]
        rw [hm4_outside_dll _
          (fun x _ => ⟨by dsimp [dgEPosBase, dgHePrevBase]; omega, by dsimp [dgEPosBase, dgHeNextBase]; omega⟩)
          (fun s hs => ⟨by dsimp [dgEPosBase, dgIncHeadBase]; omega, by dsimp [dgEPosBase, dgSlotDegBase]; omega⟩),
          hmem2, Function.update_of_ne (by dsimp [dgEPosBase, dgEHeadSlotBase]; omega),
          Function.update_of_ne (by dsimp [dgEPosBase, dgETailSlotBase]; omega), hmem1,
          Function.update_of_ne (by dsimp [dgEPosBase]; omega),
          Function.update_of_ne (by omega),
          Function.update_of_ne (by dsimp [dgEPosBase, dgEListBase]; omega),
          Function.update_of_ne (by dsimp [dgEPosBase, dgEPresBase]; omega)]
        exact heL_pos i hi_lt
  · intro e' he'
    dsimp only [MGraph.applyUpdate] at he' ⊢
    rcases Finset.mem_insert.mp he' with rfl | heG
    · simp only [Function.update_self]
      constructor
      · rw [hm4_outside_dll _
          (fun x _ => ⟨by dsimp [dgETailSlotBase, dgHePrevBase]; omega, by dsimp [dgETailSlotBase, dgHeNextBase]; omega⟩)
          (fun s hs => ⟨by dsimp [dgETailSlotBase, dgIncHeadBase]; omega, by dsimp [dgETailSlotBase, dgSlotDegBase]; omega⟩),
          hm4_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
          hmem2, Function.update_of_ne (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega),
          Function.update_self]
        exact hsu_eq.symm
      · rw [hm4_outside_dll _
          (fun x _ => ⟨by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega, by dsimp [dgEHeadSlotBase, dgHeNextBase]; omega⟩)
          (fun s hs => ⟨by dsimp [dgEHeadSlotBase, dgIncHeadBase]; omega, by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega⟩),
          hm4_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
          hmem2, Function.update_self]
        exact hsv_eq.symm
    · have hne : e' ≠ e := fun hEq => he_not (hEq ▸ heG)
      have he'_lt := heCap e' heG
      have htu_lt := hvCap _ (hval e' heG).1
      have hhv_lt := hvCap _ (hval e' heG).2
      simp only [Function.update_of_ne hne]
      constructor
      · rw [hm4_outside_dll _
          (fun x _ => ⟨by dsimp [dgETailSlotBase, dgHePrevBase]; omega, by dsimp [dgETailSlotBase, dgHeNextBase]; omega⟩)
          (fun s hs => ⟨by dsimp [dgETailSlotBase, dgIncHeadBase]; omega, by dsimp [dgETailSlotBase, dgSlotDegBase]; omega⟩),
          hm4_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
          hm2_mem0 _ (by dsimp [dgETailSlotBase, dgEPresBase]; omega)
            (by dsimp [dgETailSlotBase, dgEListBase]; omega) (by dsimp [dgETailSlotBase, dgEPosBase]; omega)
            (by dsimp [dgETailSlotBase]; omega) (by omega)
            (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega)]
        exact (hets_ehs e' heG).1
      · rw [hm4_outside_dll _
          (fun x _ => ⟨by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega, by dsimp [dgEHeadSlotBase, dgHeNextBase]; omega⟩)
          (fun s hs => ⟨by dsimp [dgEHeadSlotBase, dgIncHeadBase]; omega, by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega⟩),
          hm4_preserves_early _ (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega) (by dsimp [dgExtToIntBase]; omega),
          hm2_mem0 _ (by dsimp [dgEHeadSlotBase, dgEPresBase]; omega)
            (by dsimp [dgEHeadSlotBase, dgEListBase]; omega) (by dsimp [dgEHeadSlotBase, dgEPosBase]; omega)
            (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase, dgETailSlotBase]; omega)
            (by omega)]
        exact (hets_ehs e' heG).2
  · let incL' : ℕ → List ℕ := fun s =>
      if s = sv then (2 * e + 1) :: (if s = su then (2 * e) :: incL s else incL s)
      else if s = su then (2 * e) :: incL s else incL s
    refine ⟨incL', fun s hs => ?_⟩
    have hdisj_s : ∀ s₁ s₂, s₁ < vCap → s₂ < vCap → s₁ ≠ s₂ → ∀ x, x ∈ incL s₁ → x ∉ incL s₂ := by
      intro s₁ s₂ hs1 hs2 hne x hx1 hx2
      have h1 := ((hinc_orig s₁ hs1).2.2 x).mp hx1
      have h2 := ((hinc_orig s₂ hs2).2.2 x).mp hx2
      exact hne (h1.2.2.symm.trans h2.2.2)
    have hnot_2e : ∀ s' < vCap, 2 * e ∉ incL s' := fun s' hs' hc =>
      he_not (by simpa [Nat.mul_div_right _ (by omega : 0 < 2)] using ((hinc_orig s' hs').2.2 (2 * e)).mp hc |>.2.1)
    have hnot_2e1 : ∀ s' < vCap, 2 * e + 1 ∉ incL s' := fun s' hs' hc =>
      he_not (by simpa [show (2 * e + 1) / 2 = e by omega] using ((hinc_orig s' hs').2.2 (2 * e + 1)).mp hc |>.2.1)
    have hm2_dll : ∀ s' < vCap,
        IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
          (dgIncHeadBase gPtr vCap + s') (2 * eCap) (incL s') ∧
        mem2 (dgSlotDegBase gPtr vCap + s') = (incL s').length := by
      intro s' hs'
      have ho := hinc_orig s' hs'
      refine ⟨ho.1.of_agree ?_ ?_ ?_, ?_⟩
      · rw [hm2_mem0 _ (by dsimp [dgIncHeadBase, dgEPresBase]; omega)
          (by dsimp [dgIncHeadBase, dgEListBase]; omega) (by dsimp [dgIncHeadBase, dgEPosBase]; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgETailSlotBase]; omega)
          (by dsimp [dgIncHeadBase, dgEHeadSlotBase]; omega)]
      · intro x hx
        rw [hm2_mem0 _ (by dsimp [dgHePrevBase, dgEPresBase]; omega)
          (by dsimp [dgHePrevBase, dgEListBase]; omega) (by dsimp [dgHePrevBase, dgEPosBase]; omega)
          (by dsimp [dgHePrevBase]; omega) (by dsimp [dgHePrevBase, dgETailSlotBase]; omega)
          (by dsimp [dgHePrevBase, dgEHeadSlotBase]; omega)]
      · intro x hx
        rw [hm2_mem0 _ (by dsimp [dgHeNextBase, dgEPresBase]; omega)
          (by dsimp [dgHeNextBase, dgEListBase]; omega) (by dsimp [dgHeNextBase, dgEPosBase]; omega)
          (by dsimp [dgHeNextBase]; omega) (by dsimp [dgHeNextBase, dgETailSlotBase]; omega)
          (by dsimp [dgHeNextBase, dgEHeadSlotBase]; omega)]
      · rw [hm2_mem0 _ (by dsimp [dgSlotDegBase, dgEPresBase]; omega)
          (by dsimp [dgSlotDegBase, dgEListBase]; omega) (by dsimp [dgSlotDegBase, dgEPosBase]; omega)
          (by dsimp [dgSlotDegBase]; omega) (by dsimp [dgSlotDegBase, dgETailSlotBase]; omega)
          (by dsimp [dgSlotDegBase, dgEHeadSlotBase]; omega), ho.2.1]
    have hm3_dll_ne : ∀ s' < vCap, s' ≠ su →
        IsDoublyLinkedList mem3 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
          (dgIncHeadBase gPtr vCap + s') (2 * eCap) (incL s') ∧
        mem3 (dgSlotDegBase gPtr vCap + s') = (incL s').length := by
      intro s' hs' hne
      have hm2s := hm2_dll s' hs'
      have hnotin : ∀ y ∈ incL s', y ∉ (2 * e) :: incL su := by
        intro y hy hc
        rcases List.mem_cons.mp hc with rfl | hsu_m
        · exact hnot_2e s' hs' hy
        · exact hdisj_s su s' hsu_lt hs' hne.symm y hsu_m hy
      refine ⟨hm2s.1.of_agree ?_ ?_ ?_, ?_⟩
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by
            rw [← Nat.add_left_cancel hEq] at hy
            exact hnotin x hx hy)
          (fun y hEq hy => by
            have hlt_x := hm2s.1.2.1 x hx
            have hlt_y := hc1_dll.2.1 y hy
            dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgHePrevBase, dgIncHeadBase]; omega) (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by
            have hlt_x := hm2s.1.2.1 x hx
            have hlt_y := hc1_dll.2.1 y hy
            dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
          (fun y hEq hy => by
            rw [← Nat.add_left_cancel hEq] at hy
            exact hnotin x hx hy)
          (by dsimp [dgHeNextBase, dgIncHeadBase]; omega) (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)]
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega) (by dsimp [dgSlotDegBase]; omega), hm2s.2]
    refine ⟨?_, ?_, ?_⟩
    · by_cases hssv : s = sv
      · subst hssv
        by_cases hsuv : su = s
        · simp only [incL', ↓reduceIte, hsuv.symm]
          simpa only [hsuv, ↓reduceIte] using hc2_dll
        · simp only [incL', ↓reduceIte, Ne.symm hsuv]
          simpa only [hsuv, ↓reduceIte] using hc2_dll
      · simp only [incL', hssv, ↓reduceIte]
        by_cases hssu : s = su
        · subst hssu
          simp only [↓reduceIte]
          have hnotin : ∀ y ∈ (2 * e) :: incL s,
              y ∉ (2 * e + 1) :: (if s = sv then (2 * e) :: incL s else incL sv) := by
            intro y hy hc
            simp only [hssv, ↓reduceIte] at hc
            rcases List.mem_cons.mp hc with rfl | hsv_m
            · rcases List.mem_cons.mp hy with h1 | h2
              · omega
              · exact hnot_2e1 s hs h2
            · rcases List.mem_cons.mp hy with rfl | h2
              · exact hnot_2e sv hsv_lt hsv_m
              · exact hdisj_s sv s hsv_lt hs (Ne.symm hssv) y hsv_m h2
          refine hc1_dll.of_agree ?_ ?_ ?_
          · rw [hc2_fr _ (fun x hEq hx => by
                have hlt := hc2_hlt x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
              (fun x hEq hx => by
                have hlt := hc2_hlt x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
              (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)]
          · intro x hx
            rw [hc2_fr _ (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin x hx hy)
              (fun y hEq hy => by
                have hlt_x := hc1_dll.2.1 x hx; have hlt_y := hc2_hlt y hy
                dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
              (by dsimp [dgHePrevBase, dgIncHeadBase]; omega) (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)]
          · intro x hx
            rw [hc2_fr _ (fun y hEq hy => by
                have hlt_x := hc1_dll.2.1 x hx; have hlt_y := hc2_hlt y hy
                dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
              (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin x hx hy)
              (by dsimp [dgHeNextBase, dgIncHeadBase]; omega) (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)]
        · simp only [hssu, ↓reduceIte]
          have hnotin : ∀ y ∈ incL s,
              y ∉ (2 * e + 1) :: (if su = sv then (2 * e) :: incL su else incL sv) := by
            intro y hy hc
            rcases List.mem_cons.mp hc with rfl | hm
            · exact hnot_2e1 s hs hy
            · split_ifs at hm with huv
              · rcases List.mem_cons.mp hm with rfl | hm'
                · exact hnot_2e s hs hy
                · exact hdisj_s su s hsu_lt hs (Ne.symm hssu) y hm' hy
              · exact hdisj_s sv s hsv_lt hs (Ne.symm hssv) y hm hy
          have h3 := (hm3_dll_ne s hs hssu).1
          refine h3.of_agree ?_ ?_ ?_
          · rw [hc2_fr _ (fun x hEq hx => by
                have hlt := hc2_hlt x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
              (fun x hEq hx => by
                have hlt := hc2_hlt x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
              (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)]
          · intro x hx
            rw [hc2_fr _ (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin x hx hy)
              (fun y hEq hy => by
                have hlt_x := h3.2.1 x hx; have hlt_y := hc2_hlt y hy
                dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
              (by dsimp [dgHePrevBase, dgIncHeadBase]; omega) (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)]
          · intro x hx
            rw [hc2_fr _ (fun y hEq hy => by
                have hlt_x := h3.2.1 x hx; have hlt_y := hc2_hlt y hy
                dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
              (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin x hx hy)
              (by dsimp [dgHeNextBase, dgIncHeadBase]; omega) (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)]
    · by_cases hssv : s = sv
      · subst hssv
        rw [hc2_deg]
        by_cases hsuv : su = s
        · subst hsuv
          simp only [incL', ↓reduceIte, List.length_cons, hc1_deg, (hm2_dll su hsu_lt).2]
        · have h3d := (hm3_dll_ne s hs (Ne.symm hsuv)).2
          simp only [incL', ↓reduceIte, Ne.symm hsuv, List.length_cons, h3d]
      · rw [hc2_fr _ (fun x hEq hx => by
            have hlt := hc2_hlt x hx; dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := hc2_hlt x hx; dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega) (by dsimp [dgSlotDegBase]; omega)]
        by_cases hssu : s = su
        · subst hssu
          simp only [incL', hssv, ↓reduceIte, hc1_deg, (hm2_dll s hs).2, List.length_cons]
        · simp only [incL', hssv, hssu, ↓reduceIte, (hm3_dll_ne s hs hssu).2]
    · intro h
      have h_ts : mem4 (dgETailSlotBase gPtr vCap eCap + e) = su := by
        rw [hm4_outside_dll _
          (fun x hx => ⟨by dsimp [dgETailSlotBase, dgHePrevBase]; omega, by dsimp [dgETailSlotBase, dgHeNextBase]; omega⟩)
          (fun s' hs' => ⟨by dsimp [dgETailSlotBase, dgIncHeadBase]; omega, by dsimp [dgETailSlotBase, dgSlotDegBase]; omega⟩),
          hmem2, Function.update_of_ne (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega), Function.update_self]
      have h_hs : mem4 (dgEHeadSlotBase gPtr vCap eCap + e) = sv := by
        rw [hm4_outside_dll _
          (fun x hx => ⟨by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega, by dsimp [dgEHeadSlotBase, dgHeNextBase]; omega⟩)
          (fun s' hs' => ⟨by dsimp [dgEHeadSlotBase, dgIncHeadBase]; omega, by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega⟩),
          hmem2, Function.update_self]
      by_cases h2e : h = 2 * e
      · subst h2e
        have hmul : (2 * e) / 2 = e := Nat.mul_div_right _ (by omega)
        have hmod : (2 * e) % 2 = 0 := Nat.mul_mod_right _ _
        simp only [hmul, hmod, ↓reduceIte, h_ts, Finset.mem_insert_self, true_and, MGraph.applyUpdate]
        dsimp only [incL']
        split_ifs with hsv hsu1 hsu2 <;> try simp only [List.mem_cons]
        · exact ⟨fun _ => ⟨by omega, hsu1.symm⟩, fun _ => Or.inr (Or.inl trivial)⟩
        · constructor
          · rintro (hc | hc)
            · omega
            · exact False.elim (hnot_2e s hs hc)
          · rintro ⟨_, hsu'⟩; exact absurd hsu'.symm hsu1
        · exact ⟨fun _ => ⟨by omega, hsu2.symm⟩, fun _ => Or.inl trivial⟩
        · constructor
          · intro hc; exact False.elim (hnot_2e s hs hc)
          · rintro ⟨_, hsu'⟩; exact absurd hsu'.symm hsu2
      · by_cases h2e1 : h = 2 * e + 1
        · subst h2e1
          have hdiv : (2 * e + 1) / 2 = e := by omega
          have hmod0 : (2 * e + 1) % 2 ≠ 0 := by omega
          simp only [hdiv, hmod0, ↓reduceIte, h_hs, Finset.mem_insert_self, true_and,
            MGraph.applyUpdate]
          dsimp only [incL']
          split_ifs with hsv hsu1 hsu2 <;> try simp only [List.mem_cons]
          · exact ⟨fun _ => ⟨by omega, hsv.symm⟩, fun _ => Or.inl trivial⟩
          · exact ⟨fun _ => ⟨by omega, hsv.symm⟩, fun _ => Or.inl trivial⟩
          · constructor
            · rintro (hc | hc)
              · omega
              · exact False.elim (hnot_2e1 s hs hc)
            · rintro ⟨_, hEq⟩; exact absurd hEq.symm hsv
          · constructor
            · intro hc; exact False.elim (hnot_2e1 s hs hc)
            · rintro ⟨_, hEq⟩; exact absurd hEq.symm hsv
        · have hne_e : h / 2 ≠ e := half_ne_of_ne_pair h2e h2e1
          have hmem_iff_orig : h ∈ incL' s ↔ h ∈ incL s := by
            dsimp only [incL']
            split_ifs <;> simp [List.mem_cons, h2e, h2e1]
          rw [hmem_iff_orig, (hinc_orig s hs).2.2 h]
          dsimp only [MGraph.applyUpdate]
          simp only [Finset.mem_insert, hne_e, false_or]
          by_cases hlt2 : h < 2 * eCap
          · have hd2 : h / 2 < eCap := by omega
            have hslot_eq :
                (if h % 2 = 0 then mem4 (dgETailSlotBase gPtr vCap eCap + h / 2)
                 else mem4 (dgEHeadSlotBase gPtr vCap eCap + h / 2)) =
                (if h % 2 = 0 then mem₀ (dgETailSlotBase gPtr vCap eCap + h / 2)
                 else mem₀ (dgEHeadSlotBase gPtr vCap eCap + h / 2)) := by
              split_ifs <;>
              · rw [hm4_outside_dll _
                  (fun x hx => ⟨by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase]; omega,
                    by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgHeNextBase]; omega⟩)
                  (fun s' hs' => ⟨by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgIncHeadBase]; omega,
                    by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgSlotDegBase]; omega⟩),
                  hm2_mem0 _
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgEPresBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgEListBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase, dgEPosBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega)
                    (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega)]
            rw [hslot_eq]
          · constructor <;> intro hc <;> exact absurd hc.1 hlt2
  · intro addr haddr
    rw [hm4_outside_dll _
      (fun x hx => ⟨by dsimp [dgHePrevBase, dynGraphSize] at *; omega,
        by dsimp [dgHeNextBase, dynGraphSize] at *; omega⟩)
      (fun s hs => ⟨by dsimp [dgIncHeadBase, dynGraphSize] at *; omega,
        by dsimp [dgSlotDegBase, dynGraphSize] at *; omega⟩),
      hm2_mem0 _
        (by dsimp [dgEPresBase, dynGraphSize] at *; omega)
        (by dsimp [dgEListBase, dynGraphSize] at *; omega)
        (by dsimp [dgEPosBase, dynGraphSize] at *; omega)
        (by dsimp [dynGraphSize] at *; omega)
        (by dsimp [dgETailSlotBase, dynGraphSize] at *; omega)
        (by dsimp [dgEHeadSlotBase, dynGraphSize] at *; omega)]

private lemma dgInsertEdgeBody_triple {w : ℕ} {p : Program} {bOps : ℕ}
    {gPtr e u v vCap eCap : ℕ} {G : MGraph} {mem₀ : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (he_lt : e < eCap) (he_not : e ∉ G.E) (huV : u ∈ G.V) (hvV : v ∈ G.V)
    (hG : DynGraphAt mem₀ gPtr vCap eCap G) :
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = e ∧ st.regs 2 = u ∧ st.regs 3 = v ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.mem = mem₀)
      (dgInsertEdgePart1Stmt ;;
       dgInsertEdgePart2Stmt ;;
       .call 14 (bOps + dgIdxDllCons)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 8), .bin .add (.reg 13) (.reg 8),
          .bin .mul (.const 2) (.reg 1)] ;;
       .call 14 (bOps + dgIdxDllCons)
         [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 9), .bin .add (.reg 13) (.reg 9),
          .bin .add (.bin .mul (.const 2) (.reg 1)) (.const 1)])
      (normalPost fun st =>
        DynGraphAt st.mem gPtr vCap eCap (G.applyUpdate (.insert e u v)) ∧
        ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem₀ addr)
      (fun _ => 380) := by
  intro st ω ⟨hr0, hr1, hr2, hr3, hr4, hr5, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  rcases hG with ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_at, hvL_pos⟩, heti0, hite0, hep0, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩,
    hets_ehs, ⟨incL, hincL⟩⟩
  have hG' : DynGraphAt mem₀ gPtr vCap eCap G :=
    ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, hvL_pos⟩,
     heti0, hite0, hep0, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩, hets_ehs, ⟨incL, hincL⟩⟩
  have hu_lt := hvCap u huV
  have hv_lt := hvCap v hvV
  set su := mem₀ (dgExtToIntBase gPtr vCap + u)
  set sv := mem₀ (dgExtToIntBase gPtr vCap + v)
  have hsu_V : su ∈ G.V := (heti0 u huV).1
  have hsv_V : sv ∈ G.V := (heti0 v hvV).1
  have hsu_lt : su < vCap := hvCap su hsu_V
  have hsv_lt : sv < vCap := hvCap sv hsv_V
  have hsu_ltw : su < 2 ^ w := by omega
  have hsv_ltw : sv < 2 ^ w := by omega
  have hlt_hp_cap : dgHePrevBase gPtr vCap eCap + 2 * eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
  have hlt_hn_cap : dgHeNextBase gPtr vCap eCap + 2 * eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
  have hlt_ih_u : dgIncHeadBase gPtr vCap + su < 2 ^ w := by dsimp [dgIncHeadBase]; omega
  have hlt_sd_u : dgSlotDegBase gPtr vCap + su < 2 ^ w := by dsimp [dgSlotDegBase]; omega
  have hlt_ih_v : dgIncHeadBase gPtr vCap + sv < 2 ^ w := by dsimp [dgIncHeadBase]; omega
  have hlt_sd_v : dgSlotDegBase gPtr vCap + sv < 2 ^ w := by dsimp [dgSlotDegBase]; omega
  have hlt_2e : 2 * e < 2 * eCap := by omega
  have hlt_2e1 : 2 * e + 1 < 2 * eCap := by omega
  have hlt_2e_w : 2 * e < 2 ^ w := by omega
  have hlt_2e1_w : 2 * e + 1 < 2 ^ w := by omega
  have hnot_2e : ∀ s < vCap, 2 * e ∉ incL s := fun s hs hc =>
    he_not (by simpa [Nat.mul_div_right _ (by omega : 0 < 2)] using ((hincL s hs).2.2 (2 * e)).mp hc |>.2.1)
  have hnot_2e1 : ∀ s < vCap, 2 * e + 1 ∉ incL s := fun s hs hc =>
    he_not (by simpa [show (2 * e + 1) / 2 = e by omega] using ((hincL s hs).2.2 (2 * e + 1)).mp hc |>.2.1)
  set mem1 := Function.update
    (Function.update
      (Function.update
        (Function.update mem₀ (dgEPresBase gPtr vCap + e) 1)
        (dgEListBase gPtr vCap eCap + G.m) e)
      (dgEPosBase gPtr vCap eCap + e) G.m)
    (gPtr + 3) (G.m + 1)
  set mem2 := Function.update
    (Function.update mem1 (dgETailSlotBase gPtr vCap eCap + e) su)
    (dgEHeadSlotBase gPtr vCap eCap + e) sv
  have hm_lt : G.m < eCap := by
    have hsub : G.E ⊂ Finset.range eCap := by
      rw [Finset.ssubset_iff_of_subset (fun x hx => Finset.mem_range.mpr (heCap x hx))]
      exact ⟨e, Finset.mem_range.mpr he_lt, he_not⟩
    simpa [MGraph.m] using Finset.card_lt_card hsub
  have hm1_su : mem1 (dgExtToIntBase gPtr vCap + u) = su := by
    simp only [mem1]
    rw [Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgEPosBase]; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgEListBase]; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgEPresBase]; omega)]
  have hm1_sv : mem1 (dgExtToIntBase gPtr vCap + v) = sv := by
    simp only [mem1]
    rw [Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgEPosBase]; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgEListBase]; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgEPresBase]; omega)]
  have hm2_eq0 : ∀ addr, dgHePrevBase gPtr vCap eCap ≤ addr → mem2 addr = mem₀ addr := by
    intro addr hge
    simp only [mem2, mem1]
    rw [Function.update_of_ne (by dsimp [dgHePrevBase, dgEHeadSlotBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase, dgETailSlotBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase, dgEPosBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase, dgEListBase] at *; omega),
        Function.update_of_ne (by dsimp [dgHePrevBase, dgEPresBase] at *; omega)]
  have hm2_eq0_low : ∀ addr, dgSlotDegBase gPtr vCap ≤ addr → addr < dgEPresBase gPtr vCap →
      mem2 addr = mem₀ addr := by
    intro addr _ hlt
    simp only [mem2, mem1]
    rw [Function.update_of_ne (by dsimp [dgEHeadSlotBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by dsimp [dgETailSlotBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by dsimp [dgSlotDegBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by dsimp [dgEPosBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by dsimp [dgEListBase, dgEPresBase] at *; omega),
        Function.update_of_ne (by omega)]
  have hm2_dll : ∀ s < vCap,
      IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem2 (dgSlotDegBase gPtr vCap + s) = (incL s).length := by
    intro s hs
    have ho := hincL s hs
    refine ⟨ho.1.of_agree ?_ ?_ ?_, ?_⟩
    · exact hm2_eq0_low _ (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)
        (by dsimp [dgIncHeadBase, dgEPresBase]; omega)
    · intro x _; exact hm2_eq0 _ (by dsimp [dgHePrevBase]; omega)
    · intro x _; exact hm2_eq0 _ (by dsimp [dgHeNextBase, dgHePrevBase]; omega)
    · rw [hm2_eq0_low _ (by omega) (by dsimp [dgSlotDegBase, dgEPresBase]; omega), ho.2.1]
  refine runs_start_le ?_
  refine runs_seq_triple_le
    (dgInsertEdgePart1_triple hw16 hbound he_lt he_not hG')
    ⟨hr0, hr1, hr2, hr3, hr4, hr5, rfl⟩ ?_
  rintro st₁ ⟨hr10, hr11, hr12, hr13, hr14, hr15, hr16, _, hmem1_st⟩
  refine runs_seq_triple_le
    (dgInsertEdgePart2_triple hw16 hbound he_lt hu_lt hv_lt hm1_su hm1_sv hsu_ltw hsv_ltw)
    ⟨hr10, hr11, hr12, hr13, hr14, hr15, hr16, hmem1_st⟩ ?_
  rintro st₂ ⟨hr20, hr21, hr24, hr25, hr28, hr29, hr2_10, hr2_11, hr2_12, hr2_13, hmem2_st⟩
  have hsu_len : (incL su).length + 1 ≤ 2 * eCap :=
    nodup_length_lt_of_notMem (hincL su hsu_lt).1.1 (hincL su hsu_lt).1.2.1 hlt_2e (hnot_2e su hsu_lt)
  have hpre_c1 : (dgDllConsContract w (2 * eCap) (incL su)).pre
      [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
       dgIncHeadBase gPtr vCap + su, dgSlotDegBase gPtr vCap + su, 2 * e] st₂.mem := by
    change st₂.mem = mem2 at hmem2_st
    rw [hmem2_st]
    refine ⟨dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
      dgIncHeadBase gPtr vCap + su, dgSlotDegBase gPtr vCap + su, 2 * e, rfl,
      hw16, hlt_hp_cap, hlt_hn_cap, hlt_ih_u, hlt_sd_u, (hm2_dll su hsu_lt).1, hlt_2e,
      hnot_2e su hsu_lt, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(hm2_dll su hsu_lt).2]; omega
    · dsimp [dgIncHeadBase, dgSlotDegBase]; omega
    · intro x hx; constructor <;> [dsimp [dgHePrevBase, dgIncHeadBase]; dsimp [dgHePrevBase, dgSlotDegBase]] <;> omega
    · intro x hx; constructor <;> [dsimp [dgHeNextBase, dgIncHeadBase]; dsimp [dgHeNextBase, dgSlotDegBase]] <;> omega
    · intro x y hEq _ _; dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega
  have hargs1 : evalArgs w st₂
      [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 8), .bin .add (.reg 13) (.reg 8),
       .bin .mul (.const 2) (.reg 1)] =
      some [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
        dgIncHeadBase gPtr vCap + su, dgSlotDegBase gPtr vCap + su, 2 * e] := by
    have hlt_hp0 : dgHePrevBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHePrevBase]; omega
    have hlt_hn0 : dgHeNextBase gPtr vCap eCap < 2 ^ w := by dsimp [dgHeNextBase]; omega
    have hlt_ih0 : dgIncHeadBase gPtr vCap < 2 ^ w := by dsimp [dgIncHeadBase]; omega
    have hlt_sd0 : dgSlotDegBase gPtr vCap < 2 ^ w := by dsimp [dgSlotDegBase]; omega
    have he_ltw : e < 2 ^ w := by omega
    eval_expr
  refine runs_seq_call_le (dgDllCons_meetsContract hpOps) hargs1
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl) <;> omega)
    hpre_c1 ?_
  rintro v1 mem3 pos3 ⟨hb1, hb2, hb3, hb4, hb5, hEq1, _, hc1_dll, hc1_deg, hc1_fr⟩
  simp only [List.cons.injEq, and_true] at hEq1
  rcases hEq1 with ⟨h1, h2, h3, h4, h5⟩
  subst h1 h2 h3 h4 h5
  change st₂.mem = mem2 at hmem2_st
  rw [hmem2_st] at hc1_deg hc1_fr
  let st₃ : State := { mem := mem3, regs := Function.update st₂.regs 14 v1, pos := pos3 }
  let L₂ := if su = sv then (2 * e) :: incL su else incL sv
  have hm3_sv : IsDoublyLinkedList mem3 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sv) (2 * eCap) L₂ ∧
      mem3 (dgSlotDegBase gPtr vCap + sv) = L₂.length := by
    by_cases hsuv : su = sv
    · rw [show L₂ = (2 * e) :: incL su by dsimp only [L₂]; split_ifs; rfl]
      have hlen_eq : (incL sv).length = (incL su).length := by rw [hsuv]
      rw [← hsuv]
      refine ⟨hc1_dll, ?_⟩
      rw [hc1_deg, (hm2_dll su hsu_lt).2, List.length_cons]
    · simp only [L₂, hsuv, ↓reduceIte]
      have hm2v := hm2_dll sv hsv_lt
      have hnotin : ∀ y ∈ incL sv, y ∉ (2 * e) :: incL su := by
        intro y hy hc
        rcases List.mem_cons.mp hc with rfl | hsu_m
        · exact hnot_2e sv hsv_lt hy
        · have h1 := ((hincL sv hsv_lt).2.2 y).mp hy
          have h2 := ((hincL su hsu_lt).2.2 y).mp hsu_m
          exact hsuv (h2.2.2.symm.trans h1.2.2)
      refine ⟨hm2v.1.of_agree ?_ ?_ ?_, ?_⟩
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin x hx hy)
          (fun y hEq hy => by
            have hlt_x := hm2v.1.2.1 x hx; have hlt_y := hc1_dll.2.1 y hy
            dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgHePrevBase, dgIncHeadBase]; omega) (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)]
      · intro x hx
        rw [hc1_fr _ (fun y hEq hy => by
            have hlt_x := hm2v.1.2.1 x hx; have hlt_y := hc1_dll.2.1 y hy
            dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
          (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnotin x hx hy)
          (by dsimp [dgHeNextBase, dgIncHeadBase]; omega) (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)]
      · rw [hc1_fr _ (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq hx => by
            have hlt := hc1_dll.2.1 x hx; dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega) (by dsimp [dgSlotDegBase]; omega), hm2v.2]
  have hnot_2e1_L2 : 2 * e + 1 ∉ L₂ := by
    dsimp only [L₂]; split_ifs
    · simp only [List.mem_cons]
      rintro (hc | hc)
      · omega
      · exact hnot_2e1 su hsu_lt hc
    · exact hnot_2e1 sv hsv_lt
  have hL2_len : L₂.length + 1 ≤ 2 * eCap :=
    nodup_length_lt_of_notMem hm3_sv.1.1 hm3_sv.1.2.1 hlt_2e1 hnot_2e1_L2
  have hargs2 : evalArgs w st₃
      [.reg 10, .reg 11, .bin .add (.reg 12) (.reg 9), .bin .add (.reg 13) (.reg 9),
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
    have hr3_9 : st₃.regs 9 = sv := by simp [st₃, hr29]
    have hr3_1 : st₃.regs 1 = e := by simp [st₃, hr21]
    eval_expr
  have hpre_c2 : (dgDllConsContract w (2 * eCap) L₂).pre
      [dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
       dgIncHeadBase gPtr vCap + sv, dgSlotDegBase gPtr vCap + sv, 2 * e + 1] st₃.mem := by
    refine ⟨dgHePrevBase gPtr vCap eCap, dgHeNextBase gPtr vCap eCap,
      dgIncHeadBase gPtr vCap + sv, dgSlotDegBase gPtr vCap + sv, 2 * e + 1, rfl,
      hw16, hlt_hp_cap, hlt_hn_cap, hlt_ih_v, hlt_sd_v, hm3_sv.1, hlt_2e1,
      hnot_2e1_L2, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [st₃]; rw [hm3_sv.2]; omega
    · dsimp [dgIncHeadBase, dgSlotDegBase]; omega
    · intro x hx; constructor <;> [dsimp [dgHePrevBase, dgIncHeadBase]; dsimp [dgHePrevBase, dgSlotDegBase]] <;> omega
    · intro x hx; constructor <;> [dsimp [dgHeNextBase, dgIncHeadBase]; dsimp [dgHeNextBase, dgSlotDegBase]] <;> omega
    · intro x y hEq _ _; dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega
  rcases runs_call_of_meetsContract (r := 14) (dgDllCons_meetsContract hpOps)
      hargs2
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl) <;> omega)
      hpre_c2 ω with
    ⟨st₄, c₂, v2, hr₂, ⟨hc1, hc2, hc3, hc4, hc5, hEq2, _, hc2_dll, hc2_deg, hc2_fr⟩, _, _, hcost₂⟩
  simp only [List.cons.injEq, and_true] at hEq2
  rcases hEq2 with ⟨h1', h2', h3', h4', h5'⟩
  subst h1' h2' h3' h4' h5'
  refine ⟨.normal, st₄, c₂, hr₂, ?_, ?_⟩
  · dsimp only [normalPost]
    refine dgInsertEdge_post_dynGraphAt he_lt he_not huV hvV hG' rfl rfl hsu_lt hsv_lt
      hincL rfl rfl hc1_dll hc1_deg hc1_fr hc2_dll hc2_deg hc2_fr
  · dsimp only [dgDllConsContract, argsSize, Expr.size] at hcost₂ ⊢
    omega

theorem dgInsertEdge_meetsContract {w : ℕ} {p : Program} {b bOps vCap eCap : ℕ} {G : MGraph}
    (hp : p.HasAt b (dgEdgeProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + dgIdxInsertEdge) (dgInsertEdgeContract w vCap eCap G) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxInsertEdge) (by simp [dgEdgeProcs, dgIdxInsertEdge]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, e, u, v, rfl, hw16, hbound, huV, hvV, hG⟩
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_ec : eCap < 2 ^ w := by omega
  have he_arg_lt : e < 2 ^ w := hargs e (by simp)
  have hvc_eq : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hec_eq : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  refine runs_start_le ?_
  dsimp only [dgEdgeProcs, dgIdxInsertEdge, List.getElem_cons_zero, dgInsertEdgeStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := vCap) (by eval_expr)
    (by simpa [startState] using hvc_eq)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := eCap) (by eval_expr)
    (by simpa [startState] using hec_eq)) ?_
  have hcond1 : (Expr.bin .lt (.reg 1) (.reg 5)).eval w
      { mem := mem,
        regs := Function.update (Function.update (startState [gPtr, e, u, v] mem pos).regs 4 vCap) 5 eCap,
        pos := pos } = some (if e < eCap then 1 else 0) := by
    eval_expr
  refine runs_seq_cond_le hcond1 ?_ ?_
  · intro hne
    have he_lt : e < eCap := by by_contra hc; simp [hc] at hne
    have hep_eq : mem (dgEPresBase gPtr vCap + e) = if e ∈ G.E then 1 else 0 :=
      hG.2.2.2.2.2.2.2.2.2.2.2.1 e he_lt
    have hlt_ep : gPtr + 4 + 7 * vCap + e < 2 ^ w := by omega
    have hep_eval : (Expr.bin .eq (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
        (.bin .mul (.const 7) (.reg 4))) (.reg 1))) (.const 0)).eval w
        { mem := mem,
          regs := Function.update (Function.update (startState [gPtr, e, u, v] mem pos).regs 4 vCap) 5 eCap,
          pos := pos } = some (if (if e ∈ G.E then 1 else 0) = 0 then 1 else 0) := by
      refine Expr.eval_bin
        (Expr.eval_load_of_eq (by eval_expr) (by simpa [dgEPresBase] using hep_eq))
        (Expr.eval_const (by omega)) (by dsimp [BinOp.eval]; split_ifs <;> omega)
    refine runs_seq_cond_le hep_eval ?_ ?_
    · intro hne2
      have he_not : e ∉ G.E := by intro hm; simp [hm] at hne2
      refine runs_seq_triple_le
        (dgInsertEdgeBody_triple hpOps hw16 hbound he_lt he_not huV hvV hG)
        ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
         by simp, by simp, rfl⟩ ?_
      rintro st' ⟨hG', hfr'⟩
      refine runs_ret_le (by eval_expr) ?_ (by dsimp [dgInsertEdgeContract, Expr.size]; omega)
      refine ⟨gPtr, e, u, v, rfl, rfl, ?_, hfr'⟩
      simpa [he_lt, he_not] using hG'
    · intro he2
      have he_in : e ∈ G.E := by by_contra hm; simp [hm] at he2
      refine runs_seq_nop_le ?_
      refine runs_ret_le (by eval_expr) ?_ (by dsimp [dgInsertEdgeContract, Expr.size]; omega)
      refine ⟨gPtr, e, u, v, rfl, rfl, ?_, fun _ _ => rfl⟩
      dsimp only [startState]
      simpa [he_in] using hG
  · intro he1
    have he_ge : ¬ (e < eCap) := fun hc => by simp [hc] at he1
    refine runs_seq_nop_le ?_
    refine runs_ret_le (by eval_expr) ?_ (by dsimp [dgInsertEdgeContract, Expr.size]; omega)
    refine ⟨gPtr, e, u, v, rfl, rfl, ?_, fun _ _ => rfl⟩
    dsimp only [startState]
    simpa [he_ge] using hG

end

end MinCostFlow.DynSpanner.Program
