module

public import MinCostFlow.Machine.WideWord.LSSTGraphBfsVisit
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# WordRAM `O(n + m)` BFS bridges verification (`bfsBridges`)

This file proves the bridge-vertex discovery contract `bfsBridges_meetsContract` using
`bfsVisit_exact_meetsContract` from `LSSTGraphBfsVisit.lean` and re-exports `graphModule`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM
open MinCostFlow
open MinCostFlow.LSF

/-! ### `bfsBridges` contract and verification -/

def bfsBridgesCost (n nlCnt : ℕ) : ℕ := 300 * n + 300 * nlCnt + 200

def bfsBridgesContract (G : IndexedGraph) (V_list : List ℕ) (w : ℕ) : Contract where
  pre args mem := ∃ offPtr adjPtr vListPtr outBPtr heap,
    args = [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] ∧
    G.Valid ∧ 16 ≤ 2 ^ w ∧
    V_list = activeVertsList G ∧ V_list ≠ [] ∧
    offPtr + (G.n + 1) ≤ heap ∧ adjPtr + 2 * (nonloopEdges G).length ≤ heap ∧
    vListPtr + V_list.length ≤ heap ∧ outBPtr + V_list.length ≤ heap ∧
    (∀ a, outBPtr ≤ a → a < outBPtr + V_list.length → vListPtr ≤ a → a < vListPtr + V_list.length → False) ∧
    (∀ a, outBPtr ≤ a → a < outBPtr + V_list.length → offPtr ≤ a → a < offPtr + (G.n + 1) → False) ∧
    (∀ a, outBPtr ≤ a → a < outBPtr + V_list.length → adjPtr ≤ a → a < adjPtr + 2 * (nonloopEdges G).length → False) ∧
    heap + 2 * G.n < 2 ^ w ∧
    ListAt mem vListPtr V_list ∧
    CSRAdjacencySpec G mem offPtr adjPtr ∧
    ZeroFrom mem heap
  post args mem ret mem' := ∃ offPtr adjPtr vListPtr outBPtr heap,
    args = [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] ∧
    ∃ B : List ℕ, ret = B.length ∧ B.length ≤ V_list.length ∧
      ListAt mem' outBPtr B ∧
      ZeroFrom mem' (heap + 2 * G.n) ∧
      (∀ a, (a < outBPtr ∨ (outBPtr + V_list.length ≤ a ∧ a < heap) ∨ heap + 2 * G.n ≤ a) →
        mem' a = mem a) ∧
      (∀ (v : ℕ → ℝ), (∀ e < G.m, 0 < v e) →
        IsBridgeVerts
          (weightedCopyGraph { G.toMGraph with E := (nonloopEdges G).toFinset } v)
          V_list.toFinset (V_list.headD 0) B)
  cost _ _ := bfsBridgesCost G.n (nonloopEdges G).length

private noncomputable def bfsCondCost (G : IndexedGraph) (offPtr heap v : ℕ) (mem m0 : ℕ → ℕ) : ℕ :=
  by classical
     exact if mem (heap + v) = 0
     then 85 + 120 * (reachUnvisSet G heap v mem).card +
       120 * (∑ u ∈ reachUnvisSet G heap v mem, (m0 (offPtr + (u + 1)) - m0 (offPtr + u)))
     else 8

private lemma bfsBridges_cond_triple {G : IndexedGraph} {V_list : List ℕ} {w b offPtr adjPtr outBPtr heap v r₀ : ℕ}
    {mem : ℕ → ℕ} {s₁ : State} {p : Program} {B : List ℕ}
    (hG : G.Valid) (hw16 : 16 ≤ 2 ^ w) (hv_lt : v < G.n) (hr₀_lt : r₀ < G.n)
    (hv_mem : v ∈ V_list) (hV_lt : ∀ x ∈ V_list, x < G.n)
    (hoff_h : offPtr + (G.n + 1) ≤ heap) (hadj_h : adjPtr + 2 * (nonloopEdges G).length ≤ heap)
    (hoB_h : outBPtr + V_list.length ≤ heap) (hheap_w : heap + 2 * G.n < 2 ^ w)
    (hdisj_oo : ∀ a, outBPtr ≤ a → a < outBPtr + V_list.length → offPtr ≤ a → a < offPtr + (G.n + 1) → False)
    (hdisj_oa : ∀ a, outBPtr ≤ a → a < outBPtr + V_list.length → adjPtr ≤ a → a < adjPtr + 2 * (nonloopEdges G).length → False)
    (hvis_mc : MeetsContract w p (b + idxBfsVisit) (bfsVisitExactContract G w))
    (hcsr : CSRAdjacencySpec G s₁.mem offPtr adjPtr)
    (hoff_eq : ∀ u ≤ G.n, s₁.mem (offPtr + u) = mem (offPtr + u))
    (r0 : s₁.regs 0 = G.n) (r1 : s₁.regs 1 = offPtr) (r2 : s₁.regs 2 = adjPtr)
    (r5 : s₁.regs 5 = outBPtr) (r6 : s₁.regs 6 = heap) (r7 : s₁.regs 7 = v)
    (r8 : s₁.regs 8 = heap + G.n) (r9 : s₁.regs 9 = B.length)
    (hBV : B.length < V_list.length)
    (hBnd : B.Nodup) (hBv : ∀ x ∈ B, x ∈ V_list) (hr₀_nB : r₀ ∉ B)
    (hBm : ListAt s₁.mem outBPtr B)
    (hr₀1 : s₁.mem (heap + r₀) = 1) (hB1 : ∀ x ∈ B, s₁.mem (heap + x) = 1)
    (h01 : ∀ u < G.n, s₁.mem (heap + u) = 0 ∨ s₁.mem (heap + u) = 1)
    (hreach : ∀ u < G.n, s₁.mem (heap + u) = 1 →
      ∃ c ∈ r₀ :: B, ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected c u)
    (hclosed : ∀ e ∈ nonloopEdges G,
      s₁.mem (heap + G.tail e) = 1 ↔ s₁.mem (heap + G.head e) = 1)
    (hdisj_B : ∀ a ∈ r₀ :: B, ∀ c ∈ r₀ :: B, a ≠ c →
      ¬ ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected a c)
    (hfr : ∀ a, a < outBPtr ∨ (outBPtr + V_list.length ≤ a ∧ a < heap) ∨ heap + 2 * G.n ≤ a →
      s₁.mem a = mem a) :
    Triple w p (fun s => s = s₁) (bfsBridgesCond b)
      (normalPost fun s₂ =>
        (∀ r, r ≠ 9 → r ≠ 11 → s₂.regs r = s₁.regs r) ∧
        ∃ B' : List ℕ, s₂.regs 9 = B'.length ∧ B'.length ≤ B.length + 1 ∧
          B'.Nodup ∧ (∀ x ∈ B', x ∈ V_list) ∧ r₀ ∉ B' ∧
          ListAt s₂.mem outBPtr B' ∧
          s₂.mem (heap + r₀) = 1 ∧ (∀ x ∈ B', s₂.mem (heap + x) = 1) ∧
          s₂.mem (heap + v) = 1 ∧
          (∀ u < G.n, s₂.mem (heap + u) = 0 ∨ s₂.mem (heap + u) = 1) ∧
          (∀ u < G.n, s₁.mem (heap + u) = 1 → s₂.mem (heap + u) = 1) ∧
          (∀ u < G.n, s₂.mem (heap + u) = 1 → ∃ c ∈ r₀ :: B',
            ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected c u) ∧
          (∀ e ∈ nonloopEdges G, s₂.mem (heap + G.tail e) = 1 ↔ s₂.mem (heap + G.head e) = 1) ∧
          (∀ a ∈ r₀ :: B', ∀ c ∈ r₀ :: B', a ≠ c →
            ¬ ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected a c) ∧
          (∀ a, a < outBPtr ∨ (outBPtr + V_list.length ≤ a ∧ a < heap) ∨ heap + 2 * G.n ≤ a →
            s₂.mem a = mem a) ∧
          120 * visZeroCount G.n heap s₂.mem + 120 * visZeroDegSum G.n heap offPtr mem s₂.mem +
            bfsCondCost G offPtr heap v s₁.mem mem ≤
            120 * visZeroCount G.n heap s₁.mem + 120 * visZeroDegSum G.n heap offPtr mem s₁.mem + 85)
      (fun _ => bfsCondCost G offPtr heap v s₁.mem mem) := by
  classical
  set G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  intro s ω hs
  subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hv01 := h01 v hv_lt
  have hcond_eval : (Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 7))) (.const 0)).eval w s₁ =
      some (if s₁.mem (heap + v) = 0 then 1 else 0) :=
    Expr.eval_eq_op
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq r6) (Expr.eval_reg_of_eq r7) (by omega))
        (rfl : s₁.mem (heap + v) = _))
      (Expr.eval_const (by omega)) hw1
  refine runs_start_le ?_
  refine runs_cond_le hcond_eval ?_ ?_
  · intro hT
    have hv0 : s₁.mem (heap + v) = 0 := by by_contra hne; simp [hne] at hT
    have hT_eq : bfsCondCost G offPtr heap v s₁.mem mem = 85 + 120 * (reachUnvisSet G heap v s₁.mem).card +
        120 * (∑ u ∈ reachUnvisSet G heap v s₁.mem, (mem (offPtr + (u + 1)) - mem (offPtr + u))) := by
      dsimp only [bfsCondCost]; rw [ite_eq_left hv0]
    have hm_out_lt_heap : outBPtr + B.length < heap := by omega
    set m_b := Function.update s₁.mem (outBPtr + B.length) v
    have hmb_heap : ∀ x, heap ≤ x → m_b x = s₁.mem x := fun x hx => by
      dsimp only [m_b]; rw [Function.update_of_ne (by omega : x ≠ outBPtr + B.length)]
    have hmb_off : ∀ u ≤ G.n, m_b (offPtr + u) = s₁.mem (offPtr + u) := fun u hu => by
      dsimp only [m_b]
      rw [Function.update_of_ne (by
        intro h; exact hdisj_oo (offPtr + u) (by omega) (by omega) (by omega) (by omega) :
        offPtr + u ≠ outBPtr + B.length)]
    have hmb_adj : ∀ q < 2 * (nonloopEdges G).length, m_b (adjPtr + q) = s₁.mem (adjPtr + q) := fun q hq => by
      dsimp only [m_b]
      rw [Function.update_of_ne (by
        intro h; exact hdisj_oa (adjPtr + q) (by omega) (by omega) (by omega) (by omega) :
        adjPtr + q ≠ outBPtr + B.length)]
    have hcsr_mb : CSRAdjacencySpec G m_b offPtr adjPtr := csr_adj_frame hG hcsr hmb_off hmb_adj
    have hmb_words : ∀ a ∈ [G.n, offPtr, adjPtr, v, heap, heap + G.n], a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hpre_visit : (bfsVisitExactContract G w).pre [G.n, offPtr, adjPtr, v, heap, heap + G.n] m_b := by
      refine ⟨offPtr, adjPtr, v, heap, heap + G.n, rfl, hG, hw16, hv_lt,
        by rw [hmb_heap _ (by omega), hv0], hoff_h, hadj_h, rfl, by omega, hcsr_mb,
        fun u hu => by rw [hmb_heap _ (by omega)]; exact h01 u hu,
        fun e he => by
          rw [hmb_heap _ (by omega), hmb_heap _ (by omega)]
          exact hclosed e he⟩
    have hR_eq : reachUnvisSet G heap v m_b = reachUnvisSet G heap v s₁.mem := by
      ext u
      simp only [reachUnvisSet, Finset.mem_filter, Finset.mem_range]
      constructor <;> rintro ⟨hun, hm, hc⟩ <;>
        exact ⟨hun, by first | rwa [hmb_heap _ (by omega)] at hm | rwa [hmb_heap _ (by omega)], hc⟩
    have hcost_mb : (bfsVisitExactContract G w).cost [G.n, offPtr, adjPtr, v, heap, heap + G.n] m_b =
        120 * (reachUnvisSet G heap v s₁.mem).card +
        120 * (∑ u ∈ reachUnvisSet G heap v s₁.mem, (mem (offPtr + (u + 1)) - mem (offPtr + u))) + 60 := by
      dsimp only [bfsVisitExactContract, bfsVisitExactCost]
      rw [hR_eq]
      congr 2; congr 1
      refine Finset.sum_congr rfl fun u hu => ?_
      have hun := (Finset.mem_filter.mp hu).1
      have hun' := Finset.mem_range.mp hun
      rw [hmb_off _ (by omega), hmb_off _ (by omega), hoff_eq _ (by omega), hoff_eq _ (by omega)]
    refine runs_seq_store_le
      (Expr.eval_add (Expr.eval_reg_of_eq r5) (Expr.eval_reg_of_eq r9) (by omega))
      (Expr.eval_reg_of_eq r7) ?_
    refine runs_seq_assign_le
      (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [r9] : _ = B.length))
        (Expr.eval_const (by omega)) (by omega)) ?_
    have hargs : evalArgs w
        { mem := m_b, regs := Function.update s₁.regs 9 (B.length + 1), pos := s₁.pos }
        [.reg 0, .reg 1, .reg 2, .reg 7, .reg 6, .reg 8] =
        some [G.n, offPtr, adjPtr, v, heap, heap + G.n] := by
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r0] : _ = G.n)) ?_
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r1] : _ = offPtr)) ?_
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r2] : _ = adjPtr)) ?_
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r7] : _ = v)) ?_
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r6] : _ = heap)) ?_
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), r8] : _ = heap + G.n)) ?_
      rfl
    refine runs_call_le hvis_mc hargs hmb_words hpre_visit ?_
    intro ret mem' pos' hpost
    rcases hpost with ⟨⟨_, _, _, _, _, hpad, hv_one, hmon, h01', hconn_v, hclosed', hfr_v, _⟩,
      _, _, _, _, _, hpad2, hvc_ex, hvd_ex⟩
    simp only [List.cons.injEq, true_and, and_true] at hpad hpad2
    rcases hpad with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rcases hpad2 with ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hvc_ex' : visZeroCount G.n heap mem' + (reachUnvisSet G heap v m_b).card = visZeroCount G.n heap m_b := hvc_ex
    have hvd_ex' : visZeroDegSum G.n heap offPtr m_b mem' +
        (∑ u ∈ reachUnvisSet G heap v m_b, (m_b (offPtr + (u + 1)) - m_b (offPtr + u))) =
        visZeroDegSum G.n heap offPtr m_b m_b := hvd_ex
    have hfr_v' : ∀ a, a < heap ∨ heap + 2 * G.n ≤ a → mem' a = m_b a := hfr_v
    have hmon' : ∀ u < G.n, m_b (heap + u) = 1 → mem' (heap + u) = 1 := hmon
    have hconn_v' : ∀ u < G.n, m_b (heap + u) = 0 → mem' (heap + u) = 1 → G_nl.Connected v u := hconn_v
    have hv_nB : v ∉ B := fun hvb => by have := hB1 v hvb; omega
    have hv_ne_r₀ : v ≠ r₀ := fun hvr => by subst hvr; omega
    have hr₀_one' : mem' (heap + r₀) = 1 := hmon' r₀ hr₀_lt (by rw [hmb_heap (heap + r₀) (by omega)]; exact hr₀1)
    have hBm' : ListAt mem' outBPtr (B ++ [v]) := by
      refine listAt_congr' (fun i hi => ?_) (listAt_snoc' hBm)
      rw [List.length_append, List.length_singleton] at hi
      exact (hfr_v' (outBPtr + i) (Or.inl (by omega))).symm
    have hcz_mb := visZero_congr (n := G.n) (visPtr := heap) (offPtr := offPtr) (m0 := mem)
      (mem₁ := m_b) (mem₂ := s₁.mem) (fun u _ => by rw [hmb_heap (heap + u) (by omega)])
    have hdeg_m0 : ∀ m', visZeroDegSum G.n heap offPtr m_b m' = visZeroDegSum G.n heap offPtr mem m' := fun m' => by
      refine Finset.sum_congr rfl fun u hu => ?_
      have hun := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
      rw [hmb_off (u + 1) (by omega), hmb_off u (by omega), hoff_eq (u + 1) (by omega), hoff_eq u (by omega)]
    have hsumR : (∑ u ∈ reachUnvisSet G heap v m_b, (m_b (offPtr + (u + 1)) - m_b (offPtr + u))) =
        ∑ u ∈ reachUnvisSet G heap v s₁.mem, (mem (offPtr + (u + 1)) - mem (offPtr + u)) := by
      rw [hR_eq]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hun := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
      rw [hmb_off (u + 1) (by omega), hmb_off u (by omega), hoff_eq (u + 1) (by omega), hoff_eq u (by omega)]
    rw [hcz_mb.1, hR_eq] at hvc_ex'
    rw [hdeg_m0 mem', hdeg_m0 m_b, hcz_mb.2, hsumR] at hvd_ex'
    refine ⟨?_, ?_⟩
    · refine ⟨fun r hr9 hr11 => ?_, B ++ [v], by simp, by simp,
        List.nodup_append.mpr ⟨hBnd, List.nodup_singleton _, fun a ha b hb heq => by
          rw [List.mem_singleton] at hb; subst hb; subst heq; exact hv_nB ha⟩,
        fun x hx => by
          rcases List.mem_append.mp hx with hxB | hxv
          · exact hBv x hxB
          · rw [List.mem_singleton.mp hxv]; exact hv_mem,
        fun hr₀mem => by
          rcases List.mem_append.mp hr₀mem with hB | hvs
          · exact hr₀_nB hB
          · rw [List.mem_singleton.mp hvs] at hr₀1; omega,
        hBm', hr₀_one', fun x hx => by
          rcases List.mem_append.mp hx with hxB | hxv
          · exact hmon' x (hV_lt x (hBv x hxB)) (by rw [hmb_heap (heap + x) (by omega)]; exact hB1 x hxB)
          · rw [List.mem_singleton.mp hxv]; exact hv_one,
        hv_one, h01', fun u hu hu1 => hmon' u hu (by rw [hmb_heap (heap + u) (by omega)]; exact hu1),
        fun u hu hu1 => ?_, hclosed', fun a ha c hc hac => ?_, fun a ha => ?_, ?_⟩
      · dsimp only
        rw [Function.update_of_ne hr11, Function.update_of_ne hr9]
      · rcases h01 u hu with hu0 | hu1_old
        · exact ⟨v, by simp, hconn_v' u hu (by rw [hmb_heap (heap + u) (by omega)]; exact hu0) hu1⟩
        · obtain ⟨c, hc, hcu⟩ := hreach u hu hu1_old
          refine ⟨c, ?_, hcu⟩
          rcases List.mem_cons.mp hc with rfl | hcB
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ hcB)
      · have hnot_conn_v : ∀ x ∈ r₀ :: B, ¬ G_nl.Connected x v := fun x hx ⟨P, hP⟩ => by
          have hx1 : s₁.mem (heap + x) = 1 := by
            rcases List.mem_cons.mp hx with rfl | hxB
            · exact hr₀1
            · exact hB1 x hxB
          have hv1_abs := vis_walk_invariant hclosed hP hx1
          omega
        rcases List.mem_cons.mp ha with har | ha'
        · rcases List.mem_cons.mp hc with hcr | hc'
          · exact absurd (har.trans hcr.symm) hac
          · rcases List.mem_append.mp hc' with hcB | hcv
            · rw [har] at hac ⊢
              exact hdisj_B r₀ List.mem_cons_self c (List.mem_cons_of_mem _ hcB) hac
            · rw [har, List.mem_singleton.mp hcv]; exact hnot_conn_v r₀ List.mem_cons_self
        · rcases List.mem_cons.mp hc with hcr | hc'
          · rcases List.mem_append.mp ha' with haB | hav
            · rw [hcr] at hac ⊢
              exact hdisj_B a (List.mem_cons_of_mem _ haB) r₀ List.mem_cons_self hac
            · rw [hcr, List.mem_singleton.mp hav]
              exact fun hcv => hnot_conn_v r₀ List.mem_cons_self (connected_symm hcv)
          · rcases List.mem_append.mp ha' with haB | hav <;>
              rcases List.mem_append.mp hc' with hcB | hcv
            · exact hdisj_B a (List.mem_cons_of_mem _ haB) c (List.mem_cons_of_mem _ hcB) hac
            · rw [List.mem_singleton.mp hcv]; exact hnot_conn_v a (List.mem_cons_of_mem _ haB)
            · rw [List.mem_singleton.mp hav]
              exact fun hcv' => hnot_conn_v c (List.mem_cons_of_mem _ hcB) (connected_symm hcv')
            · rw [List.mem_singleton.mp hav, List.mem_singleton.mp hcv] at hac
              exact absurd rfl hac
      · dsimp only
        rw [hfr_v' a (by omega), show m_b a = Function.update s₁.mem (outBPtr + B.length) v a from rfl,
          Function.update_of_ne (by omega), hfr a ha]
      · dsimp only
        rw [hT_eq]
        omega
    · dsimp only [argsSize, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      rw [hcost_mb, hT_eq]
      omega
  · intro hF
    have hv1 : s₁.mem (heap + v) = 1 := by
      rcases hv01 with h0 | h1
      · simp [h0] at hF
      · exact h1
    have hT_eq : bfsCondCost G offPtr heap v s₁.mem mem = 8 := by
      dsimp only [bfsCondCost]; rw [ite_eq_right (by omega)]
    refine runs_nop_le ?_ (by
      dsimp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
      rw [hT_eq])
    refine ⟨fun _ _ _ => rfl, B, r9, by omega, hBnd, hBv, hr₀_nB, hBm, hr₀1, hB1, hv1, h01,
      fun _ _ h => h, hreach, hclosed, hdisj_B, hfr, ?_⟩
    rw [hT_eq]; omega

theorem bfsBridges_meetsContract {G : IndexedGraph} {V_list : List ℕ} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (graphModule b)) :
    MeetsContract w p (b + idxBfsBridges) (bfsBridgesContract G V_list w) := by
  classical
  have hproc : p.procs[b + idxBfsBridges]? = some (bfsBridges b) :=
    hp 5 (by simp [graphModule, csrAuxModule])
  have hvis_mc := bfsVisit_exact_meetsContract (G := G) (w := w) (hasAt_bfsVisit hp)
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨offPtr, adjPtr, vListPtr, outBPtr, heap, rfl, hG, hw16, hVeq, hVne,
    hoff_h, hadj_h, hvL_h, hoB_h, hdisj_ov, hdisj_oo, hdisj_oa, hheap_w, hvm, hcsr, hz0⟩
  set G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  set r₀ := V_list.headD 0
  have hVnd : V_list.Nodup := hVeq ▸ activeVertsList_nodup G
  have hV_lt : ∀ x ∈ V_list, x < G.n := fun x hx => (mem_activeVertsList_iff.mp (hVeq ▸ hx)).1
  have hV_len_pos : 0 < V_list.length := List.length_pos_of_ne_nil hVne
  have hr₀_eq : V_list[0]'hV_len_pos = r₀ := by
    cases V_list with | nil => contradiction | cons x xs => rfl
  have hr₀_mem : r₀ ∈ V_list := by rw [← hr₀_eq]; exact List.getElem_mem hV_len_pos
  have hr₀_lt : r₀ < G.n := hV_lt r₀ hr₀_mem
  have hw1 : 1 < 2 ^ w := by omega
  let bridgeInv : State → Prop := fun st =>
    st.regs 0 = G.n ∧ st.regs 1 = offPtr ∧ st.regs 2 = adjPtr ∧
    st.regs 3 = V_list.length ∧ st.regs 4 = vListPtr ∧ st.regs 5 = outBPtr ∧
    st.regs 6 = heap ∧ st.regs 8 = heap + G.n ∧
    1 ≤ st.regs 10 ∧ st.regs 10 ≤ V_list.length ∧
    ∃ B : List ℕ, st.regs 9 = B.length ∧ B.length ≤ st.regs 10 ∧
      B.Nodup ∧ (∀ x ∈ B, x ∈ V_list) ∧ r₀ ∉ B ∧
      ListAt st.mem outBPtr B ∧
      st.mem (heap + r₀) = 1 ∧ (∀ x ∈ B, st.mem (heap + x) = 1) ∧
      (∀ u < G.n, st.mem (heap + u) = 0 ∨ st.mem (heap + u) = 1) ∧
      (∀ j < st.regs 10, ∀ hj : j < V_list.length, st.mem (heap + V_list[j]'hj) = 1) ∧
      (∀ u < G.n, st.mem (heap + u) = 1 → ∃ c ∈ r₀ :: B, G_nl.Connected c u) ∧
      (∀ e ∈ nonloopEdges G, st.mem (heap + G.tail e) = 1 ↔ st.mem (heap + G.head e) = 1) ∧
      (∀ a ∈ r₀ :: B, ∀ c ∈ r₀ :: B, a ≠ c → ¬ G_nl.Connected a c) ∧
      (∀ a, a < outBPtr ∨ (outBPtr + V_list.length ≤ a ∧ a < heap) ∨ heap + 2 * G.n ≤ a →
        st.mem a = mem a)
  let remBridge : State → ℕ := fun st =>
    160 * (V_list.length - st.regs 10) +
    120 * visZeroCount G.n heap st.mem +
    120 * visZeroDegSum G.n heap offPtr mem st.mem + 15
  let condExpr : Expr := .bin .lt (.reg 10) (.reg 3)
  let loopBody : Stmt :=
    .assign 7 (.load (.bin .add (.reg 4) (.reg 10))) ;;
    bfsBridgesCond b ;;
    .assign 10 (.bin .add (.reg 10) (.const 1))
  have hloop := Triple.loop_measure (w := w) (p := p) (e := condExpr) (body := loopBody)
    (Inv := bridgeInv) (Q := normalPost fun st => bridgeInv st ∧ st.regs 10 = V_list.length)
    (m := fun st => V_list.length - st.regs 10)
    (rem := remBridge)
    (condVal := fun st => if st.regs 10 < st.regs 3 then 1 else 0)
    (fun st ⟨_, _, _, r3, _, _, _, _, _, r10_le, _⟩ => by
      have hk_w : st.regs 10 < 2 ^ w := by omega
      have hL_w : V_list.length < 2 ^ w := hwords _ (by simp)
      eval_expr)
    (fun st hInv hcv => by
      have hL : st.regs 10 = V_list.length := by
        have := hInv.2.2.2.2.2.2.2.2.2.1; by_contra hne
        simp [show st.regs 10 < V_list.length by omega, hInv.2.2.2.1] at hcv
      refine ⟨⟨hInv, hL⟩, ?_⟩
      dsimp only [remBridge, condExpr, Expr.size_bin, Expr.size_reg]; omega)
    (fun st hInv hcv => by
      rcases hInv with ⟨r0, r1, r2, r3, r4, r5, r6, r8, hk1, hkL, B, r9, hBL, hBnd, hBv, hr₀_nB,
        hBm, hr₀1, hB1, h01, hkvis, hreach, hclosed, hdisj_B, hfr⟩
      set k := st.regs 10
      have hk_lt : k < V_list.length := by by_contra hle; simp [hle, r3] at hcv
      set v := V_list[k]'hk_lt
      have hv_mem : v ∈ V_list := List.getElem_mem hk_lt
      have hv_lt : v < G.n := hV_lt v hv_mem
      have hvk_eq : st.mem (vListPtr + k) = v := by
        rw [hfr (vListPtr + k) (by
          by_cases h1 : vListPtr + k < outBPtr
          · exact Or.inl h1
          · right; left; refine ⟨?_, by omega⟩
            by_contra hlt; exact hdisj_ov (vListPtr + k) (by omega) (by omega) (by omega) (by omega))]
        exact hvm k hk_lt
      have hoff_eq : ∀ u ≤ G.n, st.mem (offPtr + u) = mem (offPtr + u) := fun u hu =>
        hfr (offPtr + u) (by
          by_cases h1 : offPtr + u < outBPtr
          · exact Or.inl h1
          · right; left; refine ⟨?_, by omega⟩
            by_contra hlt; exact hdisj_oo (offPtr + u) (by omega) (by omega) (by omega) (by omega))
      have hadj_eq : ∀ q < 2 * (nonloopEdges G).length, st.mem (adjPtr + q) = mem (adjPtr + q) := fun q hq =>
        hfr (adjPtr + q) (by
          by_cases h1 : adjPtr + q < outBPtr
          · exact Or.inl h1
          · right; left; refine ⟨?_, by omega⟩
            by_contra hlt; exact hdisj_oa (adjPtr + q) (by omega) (by omega) (by omega) (by omega))
      have hcsr_st : CSRAdjacencySpec G st.mem offPtr adjPtr := csr_adj_frame hG hcsr hoff_eq hadj_eq
      let T_cond := bfsCondCost G offPtr heap v st.mem mem
      refine ⟨11 + T_cond, fun s0 ω' hs0 => ?_⟩
      subst s0
      refine runs_start_le ?_
      dsimp only [loopBody]
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq (rfl : st.regs 10 = _)) (by omega))
        hvk_eq) ?_
      let s₁ : State := { st with regs := Function.update st.regs 7 v }
      have hcond_s1 := bfsBridges_cond_triple (p := p) (b := b) (s₁ := s₁) hG hw16 hv_lt hr₀_lt hv_mem hV_lt
        hoff_h hadj_h hoB_h hheap_w hdisj_oo hdisj_oa hvis_mc (by simpa [s₁] using hcsr_st)
        (by simpa [s₁] using hoff_eq)
        (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r0])
        (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r1])
        (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r2])
        (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r5])
        (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r6])
        (by dsimp only [s₁]; rw [Function.update_self])
        (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r8])
        (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r9])
        (by omega) hBnd hBv hr₀_nB hBm hr₀1 hB1 h01 hreach hclosed hdisj_B hfr
      refine runs_seq_triple_le hcond_s1 rfl ?_
      intro s₂ ⟨hregs, B', r9', hBL', hBnd', hBv', hr₀_nB', hBm', hr₀1', hB1', hv1', h01', hmon',
        hreach', hclosed', hdisj_B', hfr', hpot'⟩
      have hs₂_10 : s₂.regs 10 = k := by rw [hregs 10 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega)]
      refine runs_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hs₂_10) (Expr.eval_const (by omega)) (by omega))
        ?_ ?_
      · refine ⟨?_, by dsimp only; rw [Function.update_self]; omega, ?_⟩
        · refine ⟨by dsimp only; rw [Function.update_of_ne (by omega), hregs 0 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r0],
            by dsimp only; rw [Function.update_of_ne (by omega), hregs 1 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r1],
            by dsimp only; rw [Function.update_of_ne (by omega), hregs 2 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r2],
            by dsimp only; rw [Function.update_of_ne (by omega), hregs 3 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r3],
            by dsimp only; rw [Function.update_of_ne (by omega), hregs 4 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r4],
            by dsimp only; rw [Function.update_of_ne (by omega), hregs 5 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r5],
            by dsimp only; rw [Function.update_of_ne (by omega), hregs 6 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r6],
            by dsimp only; rw [Function.update_of_ne (by omega), hregs 8 (by omega) (by omega)]; dsimp only [s₁]; rw [Function.update_of_ne (by omega), r8],
            by dsimp only; rw [Function.update_self]; omega, by dsimp only; rw [Function.update_self]; omega,
            B', by dsimp only; rw [Function.update_of_ne (by omega)]; exact r9', by dsimp only; rw [Function.update_self]; omega,
            hBnd', hBv', hr₀_nB', hBm', hr₀1', hB1', h01', ?_, hreach', hclosed', hdisj_B', hfr'⟩
          intro j hj_lt hj_L
          dsimp only at hj_lt
          rw [Function.update_self] at hj_lt
          by_cases hjk : j = k
          · subst hjk; exact hv1'
          · exact hmon' _ (hV_lt _ (List.getElem_mem hj_L)) (hkvis j (by omega) hj_L)
        · dsimp only [remBridge, condExpr, Expr.size_bin, Expr.size_reg, s₁] at hpot' ⊢
          rw [Function.update_self]
          change 3 + (11 + T_cond) + (160 * (V_list.length - (k + 1)) +
            120 * visZeroCount G.n heap s₂.mem +
            120 * visZeroDegSum G.n heap offPtr mem s₂.mem + 15) + 1 ≤
            160 * (V_list.length - k) +
            120 * visZeroCount G.n heap st.mem +
            120 * visZeroDegSum G.n heap offPtr mem st.mem + 15
          omega
      · dsimp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, s₁, T_cond]
        omega)
  refine runs_start_le ?_
  dsimp only [bfsBridges]
  have s0 : (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 0 = G.n := rfl
  have s1 : (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 1 = offPtr := rfl
  have s2 : (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 2 = adjPtr := rfl
  have s3 : (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 3 = V_list.length := rfl
  have s4 : (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 4 = vListPtr := rfl
  have s5 : (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 5 = outBPtr := rfl
  have s6 : (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 6 = heap := rfl
  have hv0_mem : mem vListPtr = r₀ := by simpa using (hvm 0 hV_len_pos).trans hr₀_eq
  refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_reg_of_eq s4) hv0_mem) ?_
  refine runs_seq_assign_le (Expr.eval_add
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), s6] : _ = heap))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega), s0] : _ = G.n)) (by omega)) ?_
  let st₂ : State :=
    { mem := mem,
      regs := Function.update (Function.update
        (startState [G.n, offPtr, adjPtr, V_list.length, vListPtr, outBPtr, heap] mem pos).regs 7 r₀) 8 (heap + G.n),
      pos := pos }
  have hargs0 : evalArgs w st₂ [.reg 0, .reg 1, .reg 2, .reg 7, .reg 6, .reg 8] =
      some [G.n, offPtr, adjPtr, r₀, heap, heap + G.n] := by
    refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), s0] : _ = G.n)) ?_
    refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), s1] : _ = offPtr)) ?_
    refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), s2] : _ = adjPtr)) ?_
    refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [st₂]; rw [Function.update_of_ne (by omega), Function.update_self] : _ = r₀)) ?_
    refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), s6] : _ = heap)) ?_
    refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [st₂]; rw [Function.update_self] : _ = heap + G.n)) ?_
    rfl
  have hwords0 : ∀ a ∈ [G.n, offPtr, adjPtr, r₀, heap, heap + G.n], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hpre0 : (bfsVisitExactContract G w).pre [G.n, offPtr, adjPtr, r₀, heap, heap + G.n] mem := by
    refine ⟨offPtr, adjPtr, r₀, heap, heap + G.n, rfl, hG, hw16, hr₀_lt, hz0 (heap + r₀) (by omega),
      hoff_h, hadj_h, rfl, by omega, hcsr, fun u _ => Or.inl (hz0 (heap + u) (by omega)), fun e he => by
        have het := (hG.2 e (mem_nonloopEdges_iff.mp he).1).1
        have heh := (hG.2 e (mem_nonloopEdges_iff.mp he).1).2
        simp [hz0 (heap + G.tail e) (by omega), hz0 (heap + G.head e) (by omega)]⟩
  refine runs_seq_call_le hvis_mc hargs0 hwords0 hpre0 ?_
  intro ret₁ mem₁ pos₁ hpost₁
  rcases hpost₁ with ⟨⟨_, _, _, _, _, hpad1, hr₀_1, _, h01_1, hconn_1, hclosed_1, hfr_1, _⟩,
    _, _, _, _, _, hpad2, hvc1, hvd1⟩
  simp only [List.cons.injEq, true_and, and_true] at hpad1 hpad2
  rcases hpad1 with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rcases hpad2 with ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
  let st_loop0 : State :=
    { mem := mem₁, regs := Function.update (Function.update (Function.update st₂.regs 11 ret₁) 9 0) 10 1, pos := pos₁ }
  have hInv0 : bridgeInv st_loop0 := by
    refine ⟨by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), s0],
      by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), s1],
      by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), s2],
      by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), s3],
      by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), s4],
      by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), s5],
      by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), s6],
      by dsimp only [st_loop0, st₂]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
      by dsimp only [st_loop0]; rw [Function.update_self],
      by dsimp only [st_loop0]; rw [Function.update_self]; exact hV_len_pos,
      [], by dsimp only [st_loop0]; rw [Function.update_of_ne (by omega), Function.update_self]; rfl,
      by dsimp only [st_loop0]; rw [Function.update_self]; norm_num,
      List.nodup_nil, fun x hx => by simp at hx, by simp, listAt_nil' _ _,
      hr₀_1, fun x hx => by simp at hx, h01_1, ?_, ?_, hclosed_1, ?_, fun a ha => hfr_1 a (by omega)⟩
    · intro j hj hjL
      have hj0 : j = 0 := by dsimp only [st_loop0] at hj; rw [Function.update_self] at hj; omega
      subst hj0; rw [hr₀_eq]; exact hr₀_1
    · intro u hu hu1
      exact ⟨r₀, List.mem_cons_self, hconn_1 u hu (hz0 (heap + u) (by omega)) hu1⟩
    · intro a ha c hc hac
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hc
      rw [ha, hc] at hac; exact absurd rfl hac
  refine runs_seq_triple_le hloop hInv0 ?_
  intro st_end ⟨hInv_end, h10_end⟩
  rcases hInv_end with ⟨r0, r1, r2, r3, r4, r5, r6, r8, hk1, hkL, B, r9, hBL, hBnd, hBv, hr₀_nB,
    hBm, hr₀1, hB1, h01, hkvis, hreach, hclosed, hdisj_B, hfr⟩
  refine runs_ret_le (Expr.eval_reg_of_eq r9) ?_ ?_
  · refine ⟨offPtr, adjPtr, vListPtr, outBPtr, heap, rfl, B, rfl, by omega, hBm,
      fun a ha => by rw [hfr a (Or.inr (Or.inr ha))]; exact hz0 a (by omega), hfr, ?_⟩
    intro v hv
    have hnl_ne : (nonloopEdges G).toFinset.Nonempty := by
      obtain ⟨e, he, _⟩ := (mem_activeVertsList_iff.mp (hVeq ▸ hr₀_mem)).2
      exact ⟨e, List.mem_toFinset.mpr he⟩
    refine isBridgeVerts_of_bfs_spec rfl rfl hnl_ne hv hBnd (fun b hb => List.mem_toFinset.mpr (hBv b hb))
      hr₀_nB (fun x hx => ?_) hdisj_B
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hx)
    have hxj := hkvis j (by omega) hj
    exact hreach _ (hV_lt _ (List.getElem_mem hj)) hxj
  · have hVL_le_n : V_list.length ≤ G.n := by
      rw [hVeq]; exact (List.length_filter_le _ _).trans (by simp)
    have hvz := visZero_le_total (n := G.n) (visPtr := heap) (offPtr := offPtr) (m0 := mem) (mem := mem)
      (fun u hu => hcsr.2.1 u hu)
    rw [hcsr.2.2.1, hcsr.1] at hvz
    have hvc1' : visZeroCount G.n heap mem₁ + (reachUnvisSet G heap r₀ mem).card = visZeroCount G.n heap mem := hvc1
    have hvd1' : visZeroDegSum G.n heap offPtr mem mem₁ +
        (∑ u ∈ reachUnvisSet G heap r₀ mem, (mem (offPtr + (u + 1)) - mem (offPtr + u))) =
        visZeroDegSum G.n heap offPtr mem mem := hvd1
    have hcost_eq (mem0 : ℕ → ℕ) (h : mem0 = mem) :
        (bfsVisitExactContract G w).cost [G.n, offPtr, adjPtr, r₀, heap, heap + G.n] mem0 =
        bfsVisitExactCost G [G.n, offPtr, adjPtr, r₀, heap, heap + G.n] mem := h ▸ rfl
    rw [hcost_eq]
    · dsimp only [bfsBridgesContract, bfsVisitExactCost, remBridge, bfsBridgesCost, argsSize,
        Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, st_loop0, st₂] at hvz ⊢
      rw [Function.update_self]
      omega
    · rfl

end MinCostFlow.WideWord
