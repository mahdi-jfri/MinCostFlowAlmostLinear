module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import WordRAM.Entry
public import MinCostFlow.ExplicitExpander.Program
public import MinCostFlow.Expander.GraphHelpers
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.ExpanderDecomp.ProgRelabel

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cloud Expander Model and Word-RAM Procedure (`ProgCloud`)

Defines the concrete cloud expander model `cloud : ℕ → Cited.Graph` (with expansion constant
`cloudAlpha = 1 / 12`) and implements a deterministic (`NoRand`) linear-time Word-RAM procedure
module `cloudExpanderProcs` that, given `s ≥ 2` in memory at `sAddr`, invokes
`MinCostFlow.ExplicitExpander.explicitProgram` through `WordRAM.runner`, deletes any self-loops
while copying the edge list to `outAddr`, and writes the graph header `[s, (cloud s).m]` at
`[outAddr, outAddr + 2)`.

The model `cloud` together with `cloud_spec` provides the explicit expander instance required by
the expander decomposition models.

Main exports:
- `deleteLoops`, `cloud`, `cloudAlpha`, `cloudAlpha_pos`, `cloud_eq_explicitGraph`, `cloud_spec`,
  `cloud_m_le`;
- `cloudExpanderEntry`, `cloudExpanderProcs`, `cloudExpanderProcs_noRand`;
- `cloudExpanderSpace`, `cloudExpanderCost`, `cloudExpanderContract`, `cloudExpander_spec`,
  `cloudExpanderContract_pre_example`.
-/

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

@[expose] public section

/-! ## 1. The Cloud Expander Model `cloud` -/

/-- Delete self-loops from an edge list. -/
def deleteLoops (edges : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  edges.filter fun e => decide (e.1 ≠ e.2)

/-- The cloud expander model on `s` vertices: `ExplicitExpander.explicitGraph s` with self-loops
deleted. For `s ≥ 2`, `explicitGraph s` is already loopless, so `cloud s = explicitGraph s`. -/
def cloud (s : ℕ) : Graph :=
  ⟨(explicitGraph s).n, deleteLoops (explicitGraph s).edges⟩

/-- Edge-expansion constant of `cloud s` (`α = 1 / 12`). -/
noncomputable def cloudAlpha : ℝ := alpha0

lemma cloudAlpha_pos : 0 < cloudAlpha := by
  unfold cloudAlpha alpha0
  norm_num

lemma deleteLoops_eq_self_of_loopless {G : Graph} (hL : G.IsLoopless) :
    deleteLoops G.edges = G.edges := by
  unfold deleteLoops
  exact List.filter_eq_self.mpr fun e he => decide_eq_true (hL e he)

lemma cloud_eq_explicitGraph {s : ℕ} (hs : 2 ≤ s) :
    cloud s = explicitGraph s := by
  have hspec := explicitGraph_spec s (by omega)
  cases hG : explicitGraph s with
  | mk n edges =>
    unfold cloud
    simp only [hG]
    congr 1
    have hL : (Graph.mk n edges).IsLoopless := hG ▸ hspec.2.2.1
    exact deleteLoops_eq_self_of_loopless hL

/-- Properties of `cloud s` for `s ≥ 2`: `s` vertices, valid, loopless, maximum degree at most `9`,
and edge expansion at least `cloudAlpha = 1 / 12`. -/
theorem cloud_spec {s : ℕ} (hs : 2 ≤ s) :
    (cloud s).n = s ∧
    (cloud s).IsValid ∧
    (cloud s).IsLoopless ∧
    (∀ v < s, (cloud s).deg v ≤ 9) ∧
    (cloud s).IsExpansionExpanderOn (cloud s).verts cloudAlpha := by
  rw [cloud_eq_explicitGraph hs]
  rcases explicitGraph_spec s (by omega) with ⟨hn, hval, hloop, hexp, hdeg⟩
  exact ⟨hn, hval, hloop, hdeg, hexp⟩

/-- Handshaking degree bound on the number of edges of `cloud s`: `2 * (cloud s).m ≤ 9 * s`. -/
lemma cloud_m_le {s : ℕ} (hs : 2 ≤ s) : 2 * (cloud s).m ≤ 9 * s := by
  rcases cloud_spec hs with ⟨hn, hval, _, hdeg, _⟩
  have hsum := sum_deg_eq_two_mul_m hval
  have h9 : ∑ u ∈ (cloud s).verts, (cloud s).deg u ≤ 9 * s := by
    calc ∑ u ∈ (cloud s).verts, (cloud s).deg u
        ≤ ∑ _u ∈ (cloud s).verts, 9 := Finset.sum_le_sum fun u hu =>
          hdeg u (hn ▸ Finset.mem_range.mp hu)
      _ = 9 * (cloud s).verts.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 9 * s := by simp [Graph.verts, hn]
  omega

/-! ## 2. Word-RAM Procedure Definitions and `NoRand` -/

/-- Loop scanning `mRaw = r5` edges at `h + 4` (`r2 + 4`), copying non-loop edges (`u ≠ v`) to
`outAddr + 2` (`r1 + 2`) and accumulating the count in `r6`. -/
def cloudFilterLoopsStmt : Stmt :=
  forRange 7 (.const 0) (.reg 5) (
    seqStmts [
      .assign 8 (.load (.bin .add (.bin .add (.reg 2) (.const 4)) (.bin .mul (.const 2) (.reg 7)))),
      .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.const 5)) (.bin .mul (.const 2) (.reg 7)))),
      .cond (.bin .eq (.reg 8) (.reg 9))
        .nop
        (seqStmts [
          .store (.bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 2) (.reg 6))) (.reg 8),
          .store (.bin .add (.bin .add (.reg 1) (.const 3)) (.bin .mul (.const 2) (.reg 6))) (.reg 9),
          .assign 6 (.bin .add (.reg 6) (.const 1))])
    ]
  )

/-- Entry procedure for the cloud expander: `args = [sAddr, outAddr, h]`.
Reads `s = mem[sAddr]`, calls `runner explicitProgram 4 (b + 1)` at `b + 1` with input `[s]` stored
at `h` and heap `h + 1`, copies all non-loop edges to `[outAddr + 2, outAddr + 2 + 2 * (cloud s).m)`,
stores `[s, (cloud s).m]` at `[outAddr, outAddr + 2)`, and returns the new zero-heap pointer
`top = h + 2 + 2 ^ wordSize 4 [s]`. -/
def cloudExpanderEntry (b : ℕ) : Stmt :=
  seqStmts [
    .assign 3 (.load (.reg 0)),
    .store (.reg 2) (.reg 3),
    .call 4 (b + 1) [.reg 2, .const 1, .bin .add (.reg 2) (.const 1)],
    .assign 5 (.load (.bin .add (.reg 2) (.const 3))),
    .assign 6 (.const 0),
    cloudFilterLoopsStmt,
    .store (.reg 1) (.reg 3),
    .store (.bin .add (.reg 1) (.const 1)) (.reg 6),
    .ret (.reg 4)
  ]

/-- Self-contained procedure list for the cloud expander at base `b`. -/
def cloudExpanderProcs (b : ℕ) : List Stmt :=
  cloudExpanderEntry b :: runner explicitProgram 4 (b + 1)

lemma cloudExpanderEntry_noRand (b : ℕ) : (cloudExpanderEntry b).NoRand := by
  simp [cloudExpanderEntry, cloudFilterLoopsStmt, seqStmts, forRange, forUp, Stmt.NoRand]

theorem cloudExpanderProcs_noRand (b : ℕ) :
    ∀ s ∈ cloudExpanderProcs b, s.NoRand := by
  intro s hs
  simp only [cloudExpanderProcs, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact cloudExpanderEntry_noRand b
  · exact runner_noRand explicitProgram_isDeterministic 4 (b + 1) s hs

/-! ## 3. Space Bound, Cost Bound, and Contract -/

/-- Explicit polynomial heap space bound for `cloudExpanderEntry`: covers the input cell at `h`,
the runner output header at `h + 1`, and `2 ^ (wordSize 4 [s] + 1) + 2`. -/
def cloudExpanderSpace (s : ℕ) : ℕ :=
  32 * (s + 3) ^ 4 + 4

/-- Explicit linear deterministic time bound `O(s)` for `cloudExpanderEntry`. -/
def cloudExpanderCost (s : ℕ) : ℕ :=
  (runnerScale explicitProgram * 380 + 400) * s

/-- Contract for `cloudExpanderEntry`: `args = [sAddr, outAddr, h]`.
Given `s = mem[sAddr] ≥ 2`, `ZeroFrom mem h`, `outAddr + 2 + 9 * s ≤ h`, and
`h + cloudExpanderSpace s ≤ 2 ^ w`, writes `cloud s` at `outAddr` (so both `GraphAt mem' outAddr (cloud s)`
and `EdgesAt mem' (outAddr + 2) (cloud s).edges` hold), satisfies all cloud-expander guarantees
(valid, loopless, max degree `≤ 9`, edge expansion `≥ cloudAlpha = 1 / 12`), preserves memory below
`h` outside `[outAddr, outAddr + 2 + 9 * s)`, returns `top ∈ [h, h + cloudExpanderSpace s]` with
`ZeroFrom mem' top`, and runs in `O(s)` steps. -/
noncomputable def cloudExpanderContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (sAddr outAddr h s : ℕ),
      args = [sAddr, outAddr, h] ∧
      mem sAddr = s ∧
      2 ≤ s ∧
      ZeroFrom mem h ∧
      outAddr + 2 + 9 * s ≤ h ∧
      h + cloudExpanderSpace s ≤ 2 ^ w
  post args mem v mem' :=
    let sAddr := args.getD 0 0
    let outAddr := args.getD 1 0
    let h := args.getD 2 0
    let s := mem sAddr
    GraphAt mem' outAddr (cloud s) ∧
    EdgesAt mem' (outAddr + 2) (cloud s).edges ∧
    (cloud s).n = s ∧
    (cloud s).IsValid ∧
    (cloud s).IsLoopless ∧
    (∀ u < s, (cloud s).deg u ≤ 9) ∧
    (cloud s).IsExpansionExpanderOn (cloud s).verts cloudAlpha ∧
    h ≤ v ∧
    v ≤ h + cloudExpanderSpace s ∧
    ZeroFrom mem' v ∧
    (∀ a < h, (a < outAddr ∨ outAddr + 2 + 9 * s ≤ a) → mem' a = mem a)
  cost args mem :=
    cloudExpanderCost (mem (args.getD 0 0))

/-! ## 4. Helper Lemmas for Word Size, Space, and Loop Filtering -/

private lemma cloud_word_bound {s : ℕ} (hs : 2 ≤ s) :
    16 * s + 48 < 2 ^ wordSize 4 [s] := by
  have h := pow_lt_two_pow_wordSize (c := 4) (by norm_num) [s]
  simp only [List.length_singleton, List.foldr_cons, List.foldr_nil, Nat.max_zero] at h
  have h3 : 27 ≤ (1 + s + 2) ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (1 + s + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h4 : 16 * s + 48 ≤ (1 + s + 2) ^ 4 := by
    rw [pow_succ]
    nlinarith
  omega

private lemma cloud_wordSize_le {s : ℕ} :
    wordSize 4 [s] ≤ 4 * s + 16 := by
  unfold wordSize
  simp only [List.length_singleton, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  have hlog : Nat.log 2 (1 + s + 2) ≤ 1 + s + 2 := Nat.log_le_self 2 _
  omega

private lemma cloud_two_pow_wordSize_le (s : ℕ) :
    2 ^ wordSize 4 [s] ≤ 16 * (s + 3) ^ 4 := by
  unfold wordSize
  simp only [List.length_singleton, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  have h1 : 2 ^ (Nat.log 2 (1 + s + 2) + 1) ≤ 2 * (s + 3) := by
    rw [Nat.pow_succ, Nat.mul_comm]
    have hlog := Nat.pow_log_le_self 2 (show 1 + s + 2 ≠ 0 by omega)
    omega
  calc 2 ^ (4 * (Nat.log 2 (1 + s + 2) + 1))
      = (2 ^ (Nat.log 2 (1 + s + 2) + 1)) ^ 4 := by rw [Nat.mul_comm, Nat.pow_mul]
    _ ≤ (2 * (s + 3)) ^ 4 := Nat.pow_le_pow_left h1 4
    _ = 16 * (s + 3) ^ 4 := by ring

private lemma cloud_space_covers (s : ℕ) :
    1 + 2 ^ (wordSize 4 [s] + 1) + 2 ≤ cloudExpanderSpace s := by
  unfold cloudExpanderSpace
  have h := cloud_two_pow_wordSize_le s
  rw [Nat.pow_succ]
  omega

private lemma deleteLoops_take_succ {edges : List (ℕ × ℕ)} {j : ℕ} (hj : j < edges.length) :
    deleteLoops (edges.take (j + 1)) =
      deleteLoops (edges.take j) ++
        if edges[j].1 = edges[j].2 then [] else [edges[j]] := by
  unfold deleteLoops
  rw [List.take_succ_eq_append_getElem hj, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases heq : edges[j].1 = edges[j].2
  · simp [heq]
  · simp [heq]

private lemma deleteLoops_length_le (edges : List (ℕ × ℕ)) :
    (deleteLoops edges).length ≤ edges.length :=
  List.length_filter_le _ _

/-- Triple for `cloudFilterLoopsStmt`: copies non-loop edges from `h + 4` to `outAddr + 2`. -/
private lemma cloudFilterLoops_triple {w outAddr h s top mRaw : ℕ}
    (p : Program) (mem2 : ℕ → ℕ) (rawEdges : List (ℕ × ℕ)) (st₀ : State)
    (hlen : rawEdges.length = mRaw)
    (hE_at : EdgesAt mem2 (h + 4) rawEdges)
    (hdisj : outAddr + 2 + 2 * mRaw ≤ h)
    (hsrc_w : h + 4 + 2 * mRaw < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hr1 : st₀.regs 1 = outAddr) (hr2 : st₀.regs 2 = h)
    (hr3 : st₀.regs 3 = s) (hr4 : st₀.regs 4 = top)
    (hr5 : st₀.regs 5 = mRaw) (hr6 : st₀.regs 6 = 0)
    (hmem : st₀.mem = mem2) :
    Triple w p (fun st => st = st₀) cloudFilterLoopsStmt
      (normalPost fun st' =>
        st'.regs 1 = outAddr ∧ st'.regs 2 = h ∧ st'.regs 3 = s ∧ st'.regs 4 = top ∧
        st'.regs 6 = (deleteLoops rawEdges).length ∧
        st'.pos = st₀.pos ∧
        MemFrame mem2 st'.mem (outAddr + 2) (outAddr + 2 + 2 * mRaw) ∧
        EdgesAt st'.mem (outAddr + 2) (deleteLoops rawEdges))
      (fun _ => 65 * mRaw + 20) := by
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 1 = outAddr ∧ st.regs 2 = h ∧ st.regs 3 = s ∧ st.regs 4 = top ∧
    st.regs 5 = mRaw ∧ st.regs 7 = i ∧
    st.regs 6 = (deleteLoops (rawEdges.take i)).length ∧
    st.pos = st₀.pos ∧
    MemFrame mem2 st.mem (outAddr + 2) (outAddr + 2 + 2 * mRaw) ∧
    EdgesAt st.mem (outAddr + 2) (deleteLoops (rawEdges.take i))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 5)
    (body := seqStmts [
      .assign 8 (.load (.bin .add (.bin .add (.reg 2) (.const 4)) (.bin .mul (.const 2) (.reg 7)))),
      .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.const 5)) (.bin .mul (.const 2) (.reg 7)))),
      .cond (.bin .eq (.reg 8) (.reg 9))
        .nop
        (seqStmts [
          .store (.bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 2) (.reg 6))) (.reg 8),
          .store (.bin .add (.bin .add (.reg 1) (.const 3)) (.bin .mul (.const 2) (.reg 6))) (.reg 9),
          .assign 6 (.bin .add (.reg 6) (.const 1))])])
    (P := fun st => st = st₀) (Inv := Inv) 56 0 mRaw (Nat.zero_le mRaw) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      exact ⟨Expr.eval_const (by omega), by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
        by simp [hr5], by simp, by simp [hr6, deleteLoops], rfl, hmem ▸ memFrame_refl _ _ _,
        fun k hk => by simp [deleteLoops] at hk⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.2.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.2.2.1)
    (fun i _ hilt => by
      intro st ω ⟨hr1, hr2, hr3, hr4, hr5, hr7, hr6, hpos, hfr, hEout⟩
      have hi_len : i < rawEdges.length := hlen.symm ▸ hilt
      set e := rawEdges[i]'hi_len
      set outM := (deleteLoops (rawEdges.take i)).length
      have houtM_le : outM ≤ i := by
        have h1 := deleteLoops_length_le (rawEdges.take i)
        have h2 : (rawEdges.take i).length ≤ i := by rw [List.length_take]; exact Nat.min_le_left _ _
        omega
      have hmem_u : st.mem (h + 4 + 2 * i) = e.1 := by
        rw [hfr (h + 4 + 2 * i) (Or.inr (by omega))]
        simpa [Nat.add_assoc] using (hE_at i hi_len).1
      have hmem_v : st.mem (h + 5 + 2 * i) = e.2 := by
        rw [hfr (h + 5 + 2 * i) (Or.inr (by omega))]
        have := (hE_at i hi_len).2
        rwa [show h + 4 + 2 * i + 1 = h + 5 + 2 * i by omega] at this
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := e.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr7) (by omega))
            (by omega))
          hmem_u) ?_
      refine runs_seq_assign_le (v := e.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [hr2]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := i) (by simp [hr7])) (by omega))
            (by omega))
          hmem_v) ?_
      refine runs_cond_le (v := if e.1 = e.2 then 1 else 0)
        (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := e.1) (by simp))
          (Expr.eval_reg_of_eq (v := e.2) (by simp)) (by omega))
        (fun hEq_ne => ?_) (fun hEq_0 => ?_)
      · -- e.1 = e.2 (loop skipped)
        have heq : e.1 = e.2 := by
          by_contra hne
          simp [hne] at hEq_ne
        have hdl : deleteLoops (rawEdges.take (i + 1)) = deleteLoops (rawEdges.take i) := by
          rw [deleteLoops_take_succ hi_len]
          simp [e, heq]
        refine runs_nop_le ?_ (by simp [Expr.size])
        refine ⟨⟨by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4], by simp [hr5],
          by simp, by simp [hr6, hdl, outM], hpos, hfr, hdl.symm ▸ hEout⟩, by simp [hr7]⟩
      · -- e.1 ≠ e.2 (emit edge)
        have hne : e.1 ≠ e.2 := by
          intro heq
          simp [heq] at hEq_0
        have hdl : deleteLoops (rawEdges.take (i + 1)) = deleteLoops (rawEdges.take i) ++ [e] := by
          rw [deleteLoops_take_succ hi_len]
          simp [e, hne]
        refine runs_seq_store_le (x := outAddr + 2 + 2 * outM) (v := e.1)
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr1]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := outM) (by simp [hr6])) (by omega))
            (by omega))
          (Expr.eval_reg_of_eq (v := e.1) (by simp)) ?_
        refine runs_seq_store_le (x := outAddr + 3 + 2 * outM) (v := e.2)
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr1]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := outM) (by simp [hr6])) (by omega))
            (by omega))
          (Expr.eval_reg_of_eq (v := e.2) (by simp)) ?_
        refine runs_assign_le (v := outM + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := outM) (by simp [hr6]))
            (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
        refine ⟨⟨by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4], by simp [hr5],
          by simp, by simp [hdl, outM], hpos,
          memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
            (memFrame_update (by omega) (by omega))), ?_⟩, by simp [hr7]⟩
        intro k hk
        dsimp only
        have hk' : k < outM + 1 := by simpa [hdl, outM] using hk
        by_cases hkeq : k = outM
        · subst hkeq
          have hget : (deleteLoops (rawEdges.take (i + 1)))[outM]'hk = e := by
            simp only [hdl]
            rw [List.getElem_append_right (by omega)]
            simp [outM]
          rw [hget]
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [show outAddr + 2 + 2 * outM + 1 = outAddr + 3 + 2 * outM by omega,
              Function.update_self]
        · have hklt : k < (deleteLoops (rawEdges.take i)).length := by omega
          have hget : (deleteLoops (rawEdges.take (i + 1)))[k]'hk =
              (deleteLoops (rawEdges.take i))[k]'hklt := by
            simp only [hdl]
            exact List.getElem_append_left hklt
          rw [hget]
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hEout k hklt).1
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hEout k hklt).2)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr1', hr2', hr3', hr4', _, _, hr6', hpos', hfr', hEout'⟩
    have htake : rawEdges.take mRaw = rawEdges := by rw [← hlen, List.take_length]
    rw [htake] at hr6' hEout'
    exact ⟨hr1', hr2', hr3', hr4', hr6', hpos', hfr', hEout'⟩
  · exact False.elim hq

/-! ## 5. Main Specification Theorem and Non-Vacuity Example -/

/-- `cloudExpanderProcs b` meets `cloudExpanderContract w` in `O(s)` deterministic steps. -/
theorem cloudExpander_spec {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (cloudExpanderProcs b)) :
    MeetsContract w p b (cloudExpanderContract w) := by
  have hEntry : p.procs[b]? = some (cloudExpanderEntry b) := by
    simpa [cloudExpanderProcs] using hp 0 (by simp [cloudExpanderProcs])
  have hp_run : p.HasAt (b + 1) (runner explicitProgram 4 (b + 1)) := by
    intro i hi
    have h := hp (i + 1) (by simp [cloudExpanderProcs]; omega)
    simpa [cloudExpanderProcs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  intro args mem pos ω _ hpre
  rcases hpre with ⟨sAddr, outAddr, h, s, hargs, hs_mem, hs_ge2, hzero, hout_h, h_space_w⟩
  subst hargs
  have hsAddr_lt_h : sAddr < h := by
    by_contra hge
    have h0 := hzero sAddr (by omega)
    omega
  have hw_space := cloud_space_covers s
  have hw_runner : (h + 1) + 2 ^ (wordSize 4 [s] + 1) + 2 ≤ 2 ^ w := by omega
  have h2pow_lt : 16 * s + 48 < 2 ^ wordSize 4 [s] := cloud_word_bound hs_ge2
  have h2pow_le : 2 ^ wordSize 4 [s] ≤ 2 ^ (wordSize 4 [s] + 1) := by
    rw [Nat.pow_succ]; omega
  have hw16 : 16 < 2 ^ w := by omega
  set H := explicitGraph s
  have hH_eq : cloud s = H := cloud_eq_explicitGraph hs_ge2
  rcases cloud_spec hs_ge2 with ⟨hcn, hcval, hcloop, hcdeg, hcexp⟩
  have hHm_le : 2 * H.m ≤ 9 * s := by rw [← hH_eq]; exact cloud_m_le hs_ge2
  set top := (h + 1) + 1 + 2 ^ wordSize 4 [s]
  have htop_le : top ≤ h + cloudExpanderSpace s := by omega
  have htop_lt_w : top < 2 ^ w := by omega
  have hsrc_w : h + 4 + 2 * H.m < 2 ^ w := by omega
  have hout_w : outAddr + 2 + 2 * H.m < 2 ^ w := by omega
  -- Run the inner `explicitProgram` at word size `wordSize 4 [s]` on `subBits`
  have hrun : ∃ o st' c,
      Runs w p ω (cloudExpanderEntry b) (startState [sAddr, outAddr, h] mem pos) o st' c ∧
      (cloudExpanderContract w).post [sAddr, outAddr, h] mem o.value st'.mem ∧
      c ≤ cloudExpanderCost s := by
    refine runs_start_le ?_
    dsimp only [cloudExpanderEntry, seqStmts]
    -- Step 1: r3 := mem[r0] (= s)
    refine runs_seq_assign_le (v := s)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := sAddr) (by simp [startState]))
        (by simp [startState, hs_mem])) ?_
    -- Step 2: mem[h] := s
    refine runs_seq_store_le (x := h) (v := s)
      (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
      (Expr.eval_reg_of_eq (v := s) (by simp)) ?_
    let st1 : State :=
      { mem := Function.update mem h s,
        regs := Function.update (startState [sAddr, outAddr, h] mem pos).regs 3 s,
        pos := pos }
    have hlist_s : ListAt st1.mem h [s] := by
      intro i hi
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi
      simp [st1]
    have hzero_h1 : ZeroFrom st1.mem (h + 1) := by
      intro a ha
      simp only [st1, Function.update_of_ne (by omega : a ≠ h)]
      exact hzero a (by omega)
    -- Step 3: call `runner explicitProgram 4 (b + 1)` on `[h, 1, h + 1]`
    have hE_run : evalArgs w st1 [.reg 2, .const 1, .bin .add (.reg 2) (.const 1)] =
        some [h, 1, h + 1] := by
      simp [evalArgs, Expr.eval, BinOp.eval, st1, startState,
        show 1 < 2 ^ w by omega, show h + 1 < 2 ^ w by omega]
    obtain ⟨o_in, st_in, c_in, hrun_in, ⟨ho_in, hout_in⟩, hc_in⟩ :=
      mainBody_runs (w := wordSize 4 [s]) (by omega : 1 ≤ s) h2pow_lt
        (subBits w (wordSize 4 [s]) st1.pos ω)
    subst ho_in
    have hrunsTo_in : RunsTo (wordSize 4 [s]) explicitProgram [s]
        (subBits w (wordSize 4 [s]) st1.pos ω) H.encode (c_in + 2) :=
      runsTo_of_entry (body := mainBody) rfl (by simp only [List.length_singleton]; omega)
        hrun_in rfl hout_in
    obtain ⟨body_r, o_r, st_r, c_r, hproc_r, hruns_r, hval_r, _, hout_r, hfr_r, hzero_r, hc_r⟩ :=
      runner_spec hp_run (a := h) (len := 1) (h := h + 1) (x := [s]) (mem := st1.mem)
        (pos := st1.pos) (ω := ω) (by omega) rfl hlist_s hzero_h1 hw_runner hrunsTo_in
    have hstart_r : startState [h, 1, h + 1] st1.mem st1.pos =
        { st1 with regs := fun i => ([h, 1, h + 1] : List ℕ).getD i 0 } := rfl
    rw [hstart_r] at hruns_r
    let st2 : State := { st_r with regs := Function.update st1.regs 4 o_r.value }
    have hcall_r : Runs w p ω (.call 4 (b + 1) [.reg 2, .const 1, .bin .add (.reg 2) (.const 1)])
        st1 .normal st2 (argsSize [.reg 2, .const 1, .bin .add (.reg 2) (.const 1)] + c_r + 1) :=
      runs_call_iff.mpr ⟨[h, 1, h + 1], body_r, o_r, st_r, c_r, hE_run, hproc_r, hruns_r, rfl, rfl, rfl⟩
    have hr_val_eq : o_r.value = top := hval_r
    -- Extract `GraphAt st2.mem (h + 2) H` and `EdgesAt st2.mem (h + 4) H.edges`
    have hGA_H : GraphAt st2.mem (h + 2) H := by
      simpa [GraphAt, st2, Nat.add_assoc] using hout_r
    have hm_at : st2.mem (h + 3) = H.m := by
      have := graphAt_m hGA_H
      rwa [show h + 2 + 1 = h + 3 by omega] at this
    have hEA_H : EdgesAt st2.mem (h + 4) H.edges := by
      have := graphAt_to_edgesAt hGA_H
      rwa [show h + 2 + 2 = h + 4 by omega] at this
    -- Sequence the call with the rest of `cloudExpanderEntry`
    suffices hrest : ∃ o st' c₂,
        Runs w p ω
          (seqStmts [
            .assign 5 (.load (.bin .add (.reg 2) (.const 3))),
            .assign 6 (.const 0),
            cloudFilterLoopsStmt,
            .store (.reg 1) (.reg 3),
            .store (.bin .add (.reg 1) (.const 1)) (.reg 6),
            .ret (.reg 4)])
          st2 o st' c₂ ∧
        (cloudExpanderContract w).post [sAddr, outAddr, h] mem o.value st'.mem ∧
        (0 + Expr.size (.load (.reg 0)) + 2 + Expr.size (.reg 2) + Expr.size (.reg 3) + 2 +
          (argsSize [.reg 2, .const 1, .bin .add (.reg 2) (.const 1)] + c_r + 1) + 1) + c₂ ≤
          cloudExpanderCost s by
      rcases hrest with ⟨o, st', c₂, hr₂, hq₂, hc₂⟩
      exact ⟨o, st', (argsSize [.reg 2, .const 1, .bin .add (.reg 2) (.const 1)] + c_r + 1) + c₂ + 1,
        runs_seq_iff.mpr (Or.inr ⟨st2, _, c₂, hcall_r, hr₂, rfl⟩), hq₂, by omega⟩
    dsimp only [seqStmts]
    -- Step 4: r5 := mem[h + 3] (= H.m)
    refine runs_seq_assign_le (v := H.m)
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [st2, st1, startState]))
          (Expr.eval_const (by omega)) (by omega))
        hm_at) ?_
    -- Step 5: r6 := 0
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
    -- Step 6: `cloudFilterLoopsStmt`
    let st2b : State :=
      { st2 with regs := Function.update (Function.update st2.regs 5 H.m) 6 0 }
    refine runs_seq_triple_le
      (cloudFilterLoops_triple (outAddr := outAddr) (h := h) (s := s) (top := top) (mRaw := H.m)
        p st2.mem H.edges st2b rfl hEA_H (by omega) hsrc_w hw16
        (by simp [st2b, st2, st1, startState]) (by simp [st2b, st2, st1, startState])
        (by simp [st2b, st2, st1]) (by simp [st2b, st2, hr_val_eq])
        (by simp [st2b]) (by simp [st2b]) rfl) rfl ?_
    intro st3 ⟨hr3_1, hr3_2, hr3_3, hr3_4, hr3_6, _, hfr3, hEout3⟩
    -- Step 7: mem[outAddr] := s
    refine runs_seq_store_le (x := outAddr) (v := s)
      (Expr.eval_reg_of_eq hr3_1) (Expr.eval_reg_of_eq hr3_3) ?_
    -- Step 8: mem[outAddr + 1] := (cloud s).m
    refine runs_seq_store_le (x := outAddr + 1) (v := (deleteLoops H.edges).length)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr3_1]))
        (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (v := (deleteLoops H.edges).length) (by simp [hr3_6])) ?_
    -- Step 9: ret top
    refine runs_ret_le (Expr.eval_reg_of_eq (v := top) (by simp [hr3_4])) ?_ ?_
    · dsimp only [cloudExpanderContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hs_mem]
      have hEdges_fin : EdgesAt
          (Function.update (Function.update st3.mem outAddr s) (outAddr + 1)
            (deleteLoops H.edges).length)
          (outAddr + 2) (cloud s).edges := by
        intro j hj
        have hj' : j < (deleteLoops H.edges).length := by simpa [cloud] using hj
        have h1 := (hEout3 j hj').1
        have h2 := (hEout3 j hj').2
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact h1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact h2
      have hGraph_fin : GraphAt
          (Function.update (Function.update st3.mem outAddr s) (outAddr + 1)
            (deleteLoops H.edges).length)
          outAddr (cloud s) := by
        refine graphAt_of_cells ?_ ?_ fun j hj => ?_
        · rw [Function.update_of_ne (by omega), Function.update_self]; exact hcn.symm
        · rw [Function.update_self]; rfl
        · have hj' : j < (cloud s).edges.length := hj
          have h1 := (hEdges_fin j hj').1
          have h2 := (hEdges_fin j hj').2
          refine ⟨?_, ?_⟩
          · exact h1
          · rwa [show outAddr + 2 + 2 * j + 1 = outAddr + 3 + 2 * j by omega] at h2
      refine ⟨hGraph_fin, hEdges_fin, hcn, hcval, hcloop, hcdeg, hcexp,
        by omega, htop_le, ?_, ?_⟩
      · intro a ha
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          hfr3 a (Or.inr (by omega))]
        exact hzero_r a ha
      · intro a ha_lt ha_out
        rw [Function.update_of_ne (by rcases ha_out with h | h <;> omega),
          Function.update_of_ne (by rcases ha_out with h | h <;> omega),
          hfr3 a (by rcases ha_out with h | h <;> [left; right] <;> omega)]
        have h_below : st2.mem a = st1.mem a := hfr_r a (by omega)
        rw [h_below]
        simp only [st1, Function.update_of_ne (by omega : a ≠ h)]
    · -- Cost bound `O(s)`
      have hws_le := cloud_wordSize_le (s := s)
      have hinner : (c_in + 2) + 1 + wordSize 4 [s] + 1 ≤ 380 * s := by omega
      have hcr_le : c_r ≤ runnerScale explicitProgram * (380 * s) :=
        le_trans hc_r (Nat.mul_le_mul_left _ hinner)
      dsimp only [cloudExpanderCost, argsSize, Expr.size]
      have hmul : (runnerScale explicitProgram * 380 + 400) * s =
          runnerScale explicitProgram * (380 * s) + 400 * s := by ring
      rw [hmul]
      omega
  rcases hrun with ⟨o, st', c, hr, hpost, hcost⟩
  exact ⟨cloudExpanderEntry b, hEntry, o, st', c, hr, hpost, by simpa [cloudExpanderContract, hs_mem] using hcost⟩

/-- Non-vacuity witness for `cloudExpanderContract 16` at `s = 2`. -/
theorem cloudExpanderContract_pre_example :
    ∃ args mem, (∀ a ∈ args, a < 2 ^ 16) ∧ (cloudExpanderContract 16).pre args mem := by
  let mem : ℕ → ℕ := fun a => if a = 0 then 2 else 0
  let args : List ℕ := [0, 10, 100]
  refine ⟨args, mem, by decide, ?_⟩
  refine ⟨0, 10, 100, 2, rfl, by simp [mem], by omega, ?_, by omega, ?_⟩
  · intro a ha; simp [mem]; omega
  · unfold cloudExpanderSpace; decide

end

end MinCostFlow.ExpanderDecomp
