module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedFilter
public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedCand
public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedUpdateS
public import MinCostFlow.DynSpanner.Complexity

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The filter procedure for the affected edges

The procedure `dsFilterAffectedStmt` gets a list of candidate edges at level `j`. For each
candidate `e` it finds the level `m₁ < j` whose embedding holds `e`, follows the walk of `e` in
that embedding, and checks the `sBit` of each vertex of the walk. It writes `e` to the output
exactly when some vertex of the walk lies in `S_prev`, which is the definition of
`affectedEdges G' H_lt piLt_mid S_prev`.

The main result is `dsFilterAffected_meetsContract`. Its proof runs the prefix (the base
addresses), then the candidate loop with the invariant `FilterMemInv`, whose step is proved in
`dsFilterAffected_step_flat` for the loop body written as one right-nested sequence and then
moved to the program's own nesting by `runs_of_runs_seqSnoc`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Reassociating a sequence that ends in a statement -/

/-- `seqSnoc s c` appends `c` at the end of the right spine of `s`: it is `s ;; c` with the
sequence reassociated to the right. -/
private def seqSnoc : Stmt → Stmt → Stmt
  | .seq a b, c => .seq a (seqSnoc b c)
  | s, c => .seq s c

private lemma runs_seq_reassoc_l_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {a b c : Stmt} {st st' : State} {k : ℕ}
    (h : Runs w p ω (a ;; (b ;; c)) st .normal st' k) :
    Runs w p ω ((a ;; b) ;; c) st .normal st' k := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hret, _⟩ | ⟨st₁, k₁, k₂, h₁, hbc, rfl⟩
  · cases hret
  · rcases runs_seq_iff.mp hbc with ⟨_, _, _, hret, _⟩ | ⟨st₂, k₃, k₄, h₂, h₃, rfl⟩
    · cases hret
    · refine runs_seq_iff.mpr (Or.inr ⟨st₂, k₁ + k₃ + 1, k₄,
        runs_seq_iff.mpr (Or.inr ⟨st₁, k₁, k₃, h₁, h₂, rfl⟩), h₃, by omega⟩)

/-- A run of `seqSnoc s c` that ends normally is a run of `s ;; c` with the same cost. -/
private lemma runs_of_runs_seqSnoc {w : ℕ} {p : Program} {ω : ℕ → Bool} (c : Stmt) :
    ∀ (s : Stmt) {st st' : State} {k : ℕ},
      Runs w p ω (seqSnoc s c) st .normal st' k → Runs w p ω (s ;; c) st .normal st' k
  | .seq a b, st, st', k, h => by
    change Runs w p ω (a ;; seqSnoc b c) st .normal st' k at h
    rcases runs_seq_iff.mp h with ⟨_, _, _, hret, _⟩ | ⟨st₁, k₁, k₂, h₁, h₂, rfl⟩
    · cases hret
    · exact runs_seq_reassoc_l_normal
        (runs_seq_iff.mpr (Or.inr ⟨st₁, k₁, k₂, h₁, runs_of_runs_seqSnoc c b h₂, rfl⟩))
  | .nop, _, _, _, h => h
  | .assign _ _, _, _, _, h => h
  | .store _ _, _, _, _, h => h
  | .rand _, _, _, _, h => h
  | .cond _ _ _, _, _, _, h => h
  | .loop _ _, _, _, _, h => h
  | .call _ _ _, _, _, _, h => h
  | .ret _, _, _, _, h => h

private lemma fr4 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) :
    st.regs 4 = c.outArrPtr := h.2.2.2.2.1

private lemma fr10 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) :
    st.regs 10 = dsPiPtrBase c.b c.L c.vCap c.eCap := h.2.2.2.2.2.2.2.2.2.2.1

/-! ## `dsFilterAffected` Contract & Verification -/

def dsFilterAffectedContract (c : FilterCtx) : Contract where
  pre args mem :=
    args = [c.b, c.j, c.candPtr, c.candLen, c.outArrPtr] ∧ mem = c.mem0
  post _ mem v mem' :=
    let eAff := c.cand.filter fun e => decide (e ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev)
    v = eAff.length ∧
    eAff.Nodup ∧
    ListAt mem' c.outArrPtr eAff ∧
    (∀ addr, (addr < c.outArrPtr ∨ c.outArrPtr + c.candLen ≤ addr) → mem' addr = mem addr) ∧
    eAff.length ≤ c.candLen ∧
    ∀ e, e ∈ eAff ↔ e ∈ c.cand ∧ e ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev
  cost _ _ :=
    100 * (c.cand.map fun e => (c.piLt_mid e).length).sum + 40 * (c.cand.length * c.j) +
      160 * c.cand.length + 140

private lemma filterMemInv_zero (c : FilterCtx) {st : State}
    (hf : FilterFixedRegs c st) (hm : st.mem = c.mem0)
    (hr12 : st.regs 12 = 0) (hr14 : st.regs 14 = 0) :
    FilterMemInv c 0 st := by
  refine ⟨hf, hr14, ?_, by simp, ?_, ?_⟩
  · simpa using hr12
  · intro i hi
    simp at hi
  · intro addr _
    exact congrFun hm addr

private lemma dsFilterAffected_step_flat (c : FilterCtx) {p : Program} {bOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) {idx : ℕ} (hidx : idx < c.candLen) :
    Triple c.w p
      (fun st => FilterMemInv c idx st)
      (.assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
       .assign 16 (.const 0) ;;
       forRange 17 (.const 0) (.reg 1)
         (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
          .cond (.reg 18)
            (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
              (.assign 16 (.reg 17))
              .nop)
            .nop) ;;
       .assign 17 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 16) (.reg 6)) (.reg 15)))) ;;
       .call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 15] ;;
       .assign 19 (.load (.bin .add (.reg 11) (.reg 18))) ;;
       .assign 20 (.load (.reg 17)) ;;
       .assign 21 (.const 0) ;;
       .loop (.bin .mul (.bin .lt (.reg 21) (.reg 20)) (.bin .eq (.reg 19) (.const 0)))
         (.assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
          .assign 23 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
          .cond (.reg 23)
            (.call 18 (bOps + dgIdxGetHead) [.reg 13, .reg 22])
            (.call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 22]) ;;
          .cond (.load (.bin .add (.reg 11) (.reg 18))) (.assign 19 (.const 1)) .nop ;;
          .assign 21 (.bin .add (.reg 21) (.const 1))) ;;
       .cond (.reg 19)
         (.store (.bin .add (.reg 4) (.reg 12)) (.reg 15) ;;
          .assign 12 (.bin .add (.reg 12) (.const 1)))
         .nop ;;
       .assign 14 (.bin .add (.reg 14) (.const 1)))
      (normalPost fun st => FilterMemInv c (idx + 1) st)
      (fun _ =>
        let e := c.cand[idx]'(by have := c.hcand_len; omega)
        100 * (c.piLt_mid e).length + 40 * c.j + 150) := by
  have hlay := c.lay
  have hw16 := c.hw16
  set e := c.cand[idx]'(by have := c.hcand_len; omega)
  have he_mem : e ∈ c.cand := List.getElem_mem _
  obtain ⟨he_G, he_cap⟩ := c.hcand_sub e he_mem
  let stepCost := 100 * (c.piLt_mid e).length + 40 * c.j + 150
  intro st ω hfm
  have hr2 : st.regs 2 = c.candPtr := hfm.1.2.2.1
  have hr14 : st.regs 14 = idx := hfm.2.1
  have he_w : e < 2 ^ c.w := lt_trans he_cap hlay.eCap_w
  have hcand_idx_w : c.candPtr + idx < 2 ^ c.w := by have := c.hcand_w; omega
  have he_eq_mem : st.mem (c.candPtr + idx) = e := hfm.read_cand hidx
  let m₁ := findEmbLevel c.inDom_mid c.j e
  have hm1_lt := findEmbLevel_lt c.inDom_mid c.h1j c.hjL e
  have hm1_in : e ∈ c.inDom_mid ⟨m₁, hm1_lt.2⟩ :=
    findEmbLevel_mem c.inDom_mid c.h1j c.hjL (c.hinDom0 e he_G)
  have hpi_spec := c.hpi_at ⟨m₁, hm1_lt.2⟩ hm1_lt.1 e hm1_in
  have hpi_eq : c.piLt_mid e = c.Pi_level ⟨m₁, hm1_lt.2⟩ e := by
    rw [c.hpiLt_eq]
    dsimp only [piLtFrom]
    split_ifs with h
    · rfl
    · exact absurd hm1_lt.2 h
  have hpi_walk : ∀ k (hk : k < (c.Pi_level ⟨m₁, hm1_lt.2⟩ e).length),
      ¬ (c.G'.tail e ∈ c.S_prev ∨
        ∃ i < k, ∃ hi : i < (c.Pi_level ⟨m₁, hm1_lt.2⟩ e).length,
          c.G'.dst ((c.Pi_level ⟨m₁, hm1_lt.2⟩ e)[i]'hi) ∈ c.S_prev) →
      ((c.Pi_level ⟨m₁, hm1_lt.2⟩ e)[k]'hk).1 ∈ c.H_lt.E := by
    have hw := c.hpi_walk e he_mem
    rwa [hpi_eq] at hw
  let ptr := c.mem0 (dsPiPtrBase c.b c.L c.vCap c.eCap + m₁ * c.eCap + e)
  suffices hres : ∃ o st' c_1,
      Runs c.w p ω
        (.assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
         .assign 16 (.const 0) ;;
         forRange 17 (.const 0) (.reg 1)
           (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
            .cond (.reg 18)
              (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
                (.assign 16 (.reg 17))
                .nop)
              .nop) ;;
         .assign 17 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 16) (.reg 6)) (.reg 15)))) ;;
         .call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 15] ;;
         .assign 19 (.load (.bin .add (.reg 11) (.reg 18))) ;;
         .assign 20 (.load (.reg 17)) ;;
         .assign 21 (.const 0) ;;
         .loop (.bin .mul (.bin .lt (.reg 21) (.reg 20)) (.bin .eq (.reg 19) (.const 0)))
           (.assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
            .assign 23 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
            .cond (.reg 23)
              (.call 18 (bOps + dgIdxGetHead) [.reg 13, .reg 22])
              (.call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 22]) ;;
            .cond (.load (.bin .add (.reg 11) (.reg 18))) (.assign 19 (.const 1)) .nop ;;
            .assign 21 (.bin .add (.reg 21) (.const 1))) ;;
         .cond (.reg 19)
           (.store (.bin .add (.reg 4) (.reg 12)) (.reg 15) ;;
            .assign 12 (.bin .add (.reg 12) (.const 1)))
           .nop ;;
         .assign 14 (.bin .add (.reg 14) (.const 1)))
        st o st' c_1 ∧ normalPost (fun st => FilterMemInv c (idx + 1) st) o st' ∧ 0 + c_1 ≤ stepCost by
    rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
    exact ⟨o, st', c_1, hr, hq, by show c_1 ≤ stepCost; omega⟩
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr14) hcand_idx_w) he_eq_mem) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let rInit : ℕ → ℕ := Function.update st.regs 15 e
  refine runs_seq_triple_le
    (dsFilterAffected_findLevel_triple c he_G he_cap rInit)
    ⟨FilterMemInv.of_regs_agree hfm rfl
        (fun r hr _ => by simp [show r ≠ 15 by omega, show r ≠ 16 by omega]) (by simp),
      by simp, by simp,
      fun r hr _ => by
        dsimp only [rInit]
        by_cases h15 : r = 15
        · subst h15; simp
        · simp [show r ≠ 16 by omega, h15]⟩
    ?_
  intro st1 ⟨hfm1, hr15_1, hr16_1, hfr1⟩
  have hm1_e_lt : m₁ * c.eCap + e < (c.L + 1) * c.eCap := by
    have h1 : m₁ * c.eCap + e < m₁ * c.eCap + c.eCap := by omega
    have h2 : (m₁ + 1) * c.eCap ≤ (c.L + 1) * c.eCap := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at h2; omega
  have hm1_e_w : m₁ * c.eCap + e < 2 ^ c.w := lt_trans hm1_e_lt hlay.Le_w
  have hm1_mul_w : m₁ * c.eCap < 2 ^ c.w := by omega
  have hpi_lt_fix : dsPiPtrBase c.b c.L c.vCap c.eCap + (m₁ * c.eCap + e) <
      c.b + dsFixedSize c.L c.vCap c.eCap := by
    have := hlay.sb_eq; have := hlay.sb_le_fix; omega
  have hpi_w : dsPiPtrBase c.b c.L c.vCap c.eCap + (m₁ * c.eCap + e) < 2 ^ c.w := by
    have := hlay.pi_lt_w; omega
  have hptr_mem : st1.mem (dsPiPtrBase c.b c.L c.vCap c.eCap + (m₁ * c.eCap + e)) = ptr := by
    rw [hfm1.read_fix hpi_lt_fix, ← Nat.add_assoc]
  refine runs_seq_assign_le (v := ptr)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (fr10 hfm1.1))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_reg_of_eq hr16_1) (Expr.eval_reg_of_eq hfm1.1.r6) hm1_mul_w)
          (Expr.eval_reg_of_eq hr15_1) hm1_e_w)
        hpi_w)
      hptr_mem) ?_
  have hg_w : dsGPtr c.b < 2 ^ c.w := by
    have := hlay.g_lt_w; dsimp only [dynGraphSize] at this; omega
  refine runs_seq_call_le (dgGetTail_meetsContract (w := c.w) (vCap := c.vCap) (eCap := c.eCap) (G := c.G') hpOps)
    (by simp [evalArgs, Expr.eval, hfm1.1.r13, hr15_1])
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl; exact hg_w; exact he_w)
    ⟨dsGPtr c.b, e, rfl, c.hw16, hlay.g_lt_w, he_G, hfm1.dynGraphAt⟩ ?_
  intro v_tail mem2 pos2 ⟨_, _, rfl, hmem2, htail⟩
  let st2 : State :=
    { mem := mem2
      regs := Function.update { st1 with regs := Function.update st1.regs 17 ptr }.regs 18 v_tail
      pos := pos2 }
  have htail_V : v_tail ∈ c.G'.V := htail ▸ (c.hG_val e he_G).1
  have htail_cap : v_tail < c.vCap := c.hGV_cap v_tail htail_V
  have hsb_tail_w : dsSBitBase c.b c.L c.vCap c.eCap + v_tail < 2 ^ c.w := by
    have := hlay.sb_lt_w; omega
  have hfm2 : FilterMemInv c idx st2 :=
    FilterMemInv.of_regs_agree hfm1 hmem2
      (fun r hr _ => by simp [st2, show r ≠ 17 by omega, show r ≠ 18 by omega])
      (by simp [st2])
  have hr11_2 : st2.regs 11 = dsSBitBase c.b c.L c.vCap c.eCap := hfm2.1.r11
  have hsb_tail_eq : st2.mem (dsSBitBase c.b c.L c.vCap c.eCap + v_tail) =
      if c.G'.tail e ∈ c.S_prev then 1 else 0 := by
    rw [hfm2.read_sBit htail_cap, htail]
  refine runs_seq_assign_le (v := if c.G'.tail e ∈ c.S_prev then 1 else 0)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr11_2)
        (Expr.eval_reg_of_eq (r := 18) (v := v_tail) (by simp))
        hsb_tail_w)
      hsb_tail_eq) ?_
  have hptr_walk_st : MWalkAt st2.mem ptr (c.Pi_level ⟨m₁, hm1_lt.2⟩ e) :=
    hpi_spec.1.of_agree fun addr ha1 ha2 => by
      refine hfm2.2.2.2.2.2 addr (c.hfoot_out addr (hpi_spec.2.1 addr ha1 ?_))
      have := mWalkEncode_length (c.Pi_level ⟨m₁, hm1_lt.2⟩ e); omega
  have hptr_w0 : ptr < 2 ^ c.w := lt_of_le_of_lt (Nat.le_add_right _ _) hpi_spec.2.2
  have hptr_len_eq : st2.mem ptr = (c.Pi_level ⟨m₁, hm1_lt.2⟩ e).length :=
    MWalkAt_head hptr_walk_st
  refine runs_seq_assign_le (v := (c.Pi_level ⟨m₁, hm1_lt.2⟩ e).length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (r := 17) (v := ptr) (by simp))
      (by dsimp only; exact hptr_len_eq)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le
    (dsFilterAffected_walkLoop_triple c hpOps (c.Pi_level ⟨m₁, hm1_lt.2⟩ e)
      hpi_walk hpi_spec.1 hpi_spec.2.1 hpi_spec.2.2 he_G rInit)
    ⟨FilterMemInv.of_regs_agree hfm2 rfl
        (fun r hr _ => by simp [st2, show r ≠ 19 by omega, show r ≠ 20 by omega, show r ≠ 21 by omega])
        (by simp [st2]),
      by simp [hr15_1], by simp [ptr], by simp, by simp, by simp,
      fun r hr h12 => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega,
        show r ≠ 19 by omega, show r ≠ 20 by omega, show r ≠ 21 by omega, hfr1 r (by omega) h12]⟩
    ?_
  intro st3 ⟨hfm3, hr15_3, hr19_3, _hfr3⟩
  have hG_aff_iff : (e ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev) ↔
      (∃ z ∈ c.G'.walkVertices (c.G'.tail e) (c.Pi_level ⟨m₁, hm1_lt.2⟩ e), z ∈ c.S_prev) := by
    have hw_eq : c.H_lt.walkVertices (c.G'.tail e) (c.Pi_level ⟨m₁, hm1_lt.2⟩ e) =
        c.G'.walkVertices (c.G'.tail e) (c.Pi_level ⟨m₁, hm1_lt.2⟩ e) := by
      simp only [MGraph.walkVertices, List.cons.injEq, true_and]
      refine List.map_congr_left fun x _ => ?_
      cases x.2 <;> simp [MGraph.dst, c.hH_ends.1, c.hH_ends.2]
    simp only [affectedEdges, Finset.mem_filter, hpi_eq, hw_eq, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨he_G, h⟩⟩
  have htake_eq : ((c.cand.take (idx + 1)).filter fun x => decide (x ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev)) =
      ((c.cand.take idx).filter fun x => decide (x ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev)) ++
        if decide (e ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev) then [e] else [] := by
    have hk_c : idx < c.cand.length := by have := c.hcand_len; omega
    simpa [e] using take_succ_filter_decide c.cand hk_c (fun x => decide (x ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev))
  refine runs_seq_cond_le (v := if ∃ z ∈ c.G'.walkVertices (c.G'.tail e) (c.Pi_level ⟨m₁, hm1_lt.2⟩ e), z ∈ c.S_prev then 1 else 0)
    (Expr.eval_reg_of_eq hr19_3) ?_ ?_
  · intro hhit_nz
    have hhit : ∃ z ∈ c.G'.walkVertices (c.G'.tail e) (c.Pi_level ⟨m₁, hm1_lt.2⟩ e), z ∈ c.S_prev := by
      by_contra hnh; simp [hnh] at hhit_nz
    have he_aff : e ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev := hG_aff_iff.mpr hhit
    have hcur12 : st3.regs 12 = ((c.cand.take idx).filter fun x => decide (x ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev)).length :=
      hfm3.2.2.1
    have h12_le : st3.regs 12 ≤ idx := by rw [hcur12]; exact hfm3.2.2.2.1
    have hout_addr_w : c.outArrPtr + st3.regs 12 < 2 ^ c.w := by have := c.hout_w; omega
    have h12_next_w : st3.regs 12 + 1 < 2 ^ c.w := by have := c.hout_w; omega
    have h14_next_w : idx + 1 < 2 ^ c.w := by have := c.hcand_w; omega
    suffices hthen : ∃ o st' c_2,
        Runs c.w p ω
          (.store (.bin .add (.reg 4) (.reg 12)) (.reg 15) ;;
           .assign 12 (.bin .add (.reg 12) (.const 1)) ;;
           .assign 14 (.bin .add (.reg 14) (.const 1)))
          st3 o st' c_2 ∧
        normalPost (fun st => FilterMemInv c (idx + 1) st) o st' ∧
        0 + (Expr.bin .add (.reg 2) (.reg 14)).load.size + 2 + (Expr.const 0).size + 2 + (35 * c.j + 7) +
          1 + (Expr.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 16) (.reg 6)) (.reg 15))).load.size + 2 +
          argsSize [.reg 13, .reg 15] +
          (dgGetTailContract c.w c.vCap c.eCap c.G').cost [dsGPtr c.b, e] st1.mem + 2 +
          (Expr.bin .add (.reg 11) (.reg 18)).load.size + 2 + (Expr.reg 17).load.size + 2 +
          (Expr.const 0).size + 2 + (96 * (c.Pi_level ⟨m₁, hm1_lt.2⟩ e).length + 10) + 1 +
          (Expr.reg 19).size + 1 + c_2 ≤ stepCost by
      rcases hthen with ⟨o, st', c_2, hr, hq, hc⟩
      cases o with
      | returned u => exact absurd hq (by simp)
      | normal => exact ⟨.normal, st', c_2, runs_seq_reassoc_l_normal hr, hq, hc⟩
    refine runs_seq_store_le
      (Expr.eval_add (Expr.eval_reg_of_eq (fr4 hfm3.1)) (Expr.eval_reg_of_eq (r := 12) (v := st3.regs 12) rfl) hout_addr_w)
      (Expr.eval_reg_of_eq hr15_3) ?_
    refine runs_seq_assign_le
      (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) (v := st3.regs 12) (by simp)) (Expr.eval_const (by omega)) h12_next_w) ?_
    refine runs_assign_le
      (Expr.eval_add (Expr.eval_reg_of_eq (r := 14) (v := idx) (by simp [hfm3.2.1])) (Expr.eval_const (by omega)) h14_next_w)
      ?_ (by dsimp only [Expr.size, dgGetTailContract, argsSize, stepCost]; rw [← hpi_eq]; omega)
    refine ⟨hfm3.1.agree (fun r hr _ => by simp [show r ≠ 14 by omega, show r ≠ 12 by omega]),
      by simp, ?_, ?_, ?_, ?_⟩
    · rw [htake_eq]; simp [he_aff, hcur12]
    · rw [htake_eq]; simp [he_aff]; exact hfm3.2.2.2.1
    · rw [htake_eq]; simp only [decide_eq_true_eq.mpr he_aff, ↓reduceIte]
      rw [hcur12]
      exact hfm3.2.2.2.2.1.snoc e
    · intro addr haddr
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hfm3.2.2.2.2.2 addr haddr
  · intro hhit_z
    have hnhit : ¬ ∃ z ∈ c.G'.walkVertices (c.G'.tail e) (c.Pi_level ⟨m₁, hm1_lt.2⟩ e), z ∈ c.S_prev := by
      intro h; simp [h] at hhit_z
    have he_naff : e ∉ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev := fun h => hnhit (hG_aff_iff.mp h)
    have h14_next_w : idx + 1 < 2 ^ c.w := by have := c.hcand_w; omega
    refine runs_seq_nop_le ?_
    refine runs_assign_le
      (Expr.eval_add (Expr.eval_reg_of_eq hfm3.2.1) (Expr.eval_const (by omega)) h14_next_w)
      ?_ (by dsimp only [Expr.size, dgGetTailContract, argsSize, stepCost]; rw [← hpi_eq]; omega)
    refine ⟨hfm3.1.agree (fun r hr _ => by simp [show r ≠ 14 by omega]),
      by simp, ?_, ?_, ?_, hfm3.2.2.2.2.2⟩
    · rw [htake_eq]; simp [he_naff, hfm3.2.2.1]
    · rw [htake_eq]; simp [he_naff]; have := hfm3.2.2.2.1; omega
    · rw [htake_eq]; simp [he_naff]; exact hfm3.2.2.2.2.1

/-- One iteration of the candidate loop of `dsFilterAffectedStmt`: from the invariant at index
`idx`, the body and the counter increment reach the invariant at `idx + 1`. -/
private lemma dsFilterAffected_step_triple (c : FilterCtx) {p : Program} {bOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) {idx : ℕ} (hidx : idx < c.candLen) :
    Triple c.w p
      (fun st => FilterMemInv c idx st)
      (dsFilterBodyStmt bOps ;; .assign 14 (.bin .add (.reg 14) (.const 1)))
      (normalPost fun st => FilterMemInv c (idx + 1) st)
      (fun _ =>
        let e := c.cand[idx]'(by have := c.hcand_len; omega)
        100 * (c.piLt_mid e).length + 40 * c.j + 150) := by
  intro st ω hfm
  rcases dsFilterAffected_step_flat c hpOps hidx st ω hfm with ⟨o, st', k, hr, hq, hc⟩
  cases o with
  | returned u => exact absurd hq (by simp [normalPost])
  | normal => exact ⟨.normal, st', k, runs_of_runs_seqSnoc _ (dsFilterBodyStmt bOps) hr, hq, hc⟩

/-- The filter procedure `bAff + affIdxFilterAffected` meets `dsFilterAffectedContract`: it
returns the candidates that are affected edges, in the order of the candidate list, at a cost
linear in the total walk length of the candidates plus `j` per candidate. -/
theorem dsFilterAffected_meetsContract (c : FilterCtx) {p : Program} {bOps bAff : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpAff : p.HasAt bAff (affectedProcs bOps)) :
    MeetsContract c.w p (bAff + affIdxFilterAffected) (dsFilterAffectedContract c) := by
  refine meetsContract_of_runs
    (hpAff.get (i := affIdxFilterAffected) (by simp [affectedProcs, affIdxFilterAffected])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  have hlay := c.lay
  have hw16 := c.hw16
  simp only [affectedProcs, affIdxFilterAffected, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsFilterAffectedStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le (dsFilterAffected_bases_triple c)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  intro st1 ⟨hm1, hf1, hr12_1⟩
  dsimp only [forRange]
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let remLoop : ℕ → ℕ := fun idx =>
    100 * ((c.cand.drop idx).map fun e => (c.piLt_mid e).length).sum +
      40 * ((c.candLen - idx) * c.j) + 160 * (c.candLen - idx) + 4
  have hloop : Triple c.w p (fun st => FilterMemInv c 0 st)
      (forUp 14 (.reg 3) (dsFilterBodyStmt bOps))
      (normalPost fun st => FilterMemInv c c.candLen st)
      (fun _ => remLoop 0) := by
    dsimp only [forUp]
    refine (Triple.loop_inv (w := c.w) (p := p) (α := ℕ)
      (Inv := fun idx st => idx ≤ c.candLen ∧ FilterMemInv c idx st)
      (Q := normalPost fun st => FilterMemInv c c.candLen st)
      (condVal := fun st => if st.regs 14 < c.candLen then 1 else 0)
      (m := fun idx => c.candLen - idx) (rem := remLoop)
      (fun idx st ⟨_, hfi⟩ =>
        Expr.eval_lt_op (Expr.eval_reg_of_eq (v := st.regs 14) rfl)
          (Expr.eval_reg_of_eq hfi.1.2.2.2.1) (by omega))
      (fun idx st ⟨hle, hfi⟩ hz => by
        have hid_ge : c.candLen ≤ idx := by
          by_contra hlt
          have : st.regs 14 < c.candLen := by rw [hfi.2.1]; omega
          simp [this] at hz
        have hEq : idx = c.candLen := le_antisymm hle hid_ge
        subst hEq
        exact ⟨hfi, by dsimp only [remLoop, Expr.size]; omega⟩)
      (fun idx st ⟨_hle, hfi⟩ hnz => by
        have hidx_lt : idx < c.candLen := by
          by_contra hge
          have : ¬ st.regs 14 < c.candLen := by rw [hfi.2.1]; omega
          simp [this] at hnz
        refine ⟨100 * (c.piLt_mid (c.cand[idx]'(by have := c.hcand_len; omega))).length + 40 * c.j + 150,
          fun s ω hs => ?_⟩
        · subst s
          rcases dsFilterAffected_step_triple c hpOps hidx_lt st ω hfi with ⟨o, st', c_step, hr, hq, hc⟩
          cases o with
          | returned u => exact absurd hq (by simp [normalPost])
          | normal =>
            have hk_c : idx < c.cand.length := by have := c.hcand_len; omega
            have hdrop : (c.cand.drop idx).map (fun e => (c.piLt_mid e).length) =
                (c.piLt_mid (c.cand[idx]'hk_c)).length ::
                  ((c.cand.drop (idx + 1)).map fun e => (c.piLt_mid e).length) := by
              rw [List.drop_eq_getElem_cons hk_c, List.map_cons]
            have hsum_drop : ((c.cand.drop idx).map fun e => (c.piLt_mid e).length).sum =
                (c.piLt_mid (c.cand[idx]'hk_c)).length +
                  ((c.cand.drop (idx + 1)).map fun e => (c.piLt_mid e).length).sum := by
              rw [hdrop, List.sum_cons]
            have hmul_sub : (c.candLen - idx) * c.j = (c.candLen - (idx + 1)) * c.j + c.j := by
              rw [show c.candLen - idx = (c.candLen - (idx + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
            refine ⟨.normal, st', c_step, hr, ⟨idx + 1, ⟨hidx_lt, hq⟩, by omega, ?_⟩, hc⟩
            dsimp only [remLoop, Expr.size]
            rw [hsum_drop, hmul_sub]
            omega) 0).conseq
      (fun st h => ⟨Nat.zero_le _, h⟩) (fun _ _ h => h) (fun _ _ => Nat.le_refl _)
  refine runs_seq_triple_le hloop
    (filterMemInv_zero c (hf1.agree (fun r hr h12 => by simp [show r ≠ 14 by omega]))
      (by simp [hm1]) (by simp [hr12_1]) (by simp)) ?_
  intro st2 hfm2
  have htake_all : c.cand.take c.candLen = c.cand := List.take_of_length_le (by rw [c.hcand_len])
  let eAff := c.cand.filter fun e => decide (e ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev)
  have heAff_nd : eAff.Nodup := c.hcand_nd.sublist List.filter_sublist
  refine runs_ret_le (v := eAff.length) (Expr.eval_reg_of_eq (by simp [hfm2.2.2.1, htake_all, eAff])) ?_ ?_
  · refine ⟨rfl, heAff_nd, ?_, ?_, ?_, fun e => by simp⟩
    · simpa [htake_all, eAff] using hfm2.2.2.2.2.1
    · intro addr ha
      simpa using hfm2.2.2.2.2.2 addr ha
    · have := hfm2.2.2.2.1
      simpa [htake_all, eAff] using this
  · dsimp only [remLoop, dsFilterAffectedContract, Expr.size]
    simp only [List.drop_zero, Nat.sub_zero, c.hcand_len]
    omega

end

end MinCostFlow.DynSpanner.Program
