module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.BfsCompProg
import all MinCostFlow.Expander.BfsCompProg
public import MinCostFlow.Expander.Components
public import MinCostFlow.ExpanderDecomp.ProgRelabel
public import MinCostFlow.ExpanderDecomp.ProgInduced

import Mathlib.Tactic.Linarith

/-!
# Word-RAM Connected Component Labels Inside `X` (`ProgCompLabels`)

Implements a deterministic (`NoRand`) Word-RAM procedure module `compLabelsInProcs` that, given a
duplicate-free list of vertices `verts` (`|verts| = k`, representing `X ⊆ {0, ..., n - 1}`), a flat
edge list `edges` (`|edges| = mE`), and a zero-initialized reusable local-index buffer `locAddr` of
length `n`, computes connected-component labels of the induced subgraph `G[X]` in `O(|X| + |E| + 1)`
time without scanning `range n`.

The entry procedure `compLabelsInEntry` composes three already-verified procedures:
1. `inducedSubgraphProc` (`ProgInduced.lean`): builds `G_X = relabelGraph verts (G.inside X)` in
   `workAddr` while preserving `locAddr` (zeroed on exit);
2. `buildCsrProc` (`MinCostFlow/Expander/CsrBfsProg.lean`): builds the CSR adjacency representation
   of `G_X` inside `workAddr`;
3. `bfsLabelsProc` (`MinCostFlow/Expander/BfsCompProg.lean`): runs linear-time BFS labeling on the
   CSR of `G_X` and writes `label[i] < k` at `outLabelAddr + i` for `i < k`.

The postcondition guarantees both:
- `Cited.partsOf G_X (readList mem' outLabelAddr k) = Cited.partsOf G_X (compLabels G_X)`, and
- direct reachability equivalence inside `X`: for all `i, j < k`,
  `mem' (outLabelAddr + i) = mem' (outLabelAddr + j) ↔ ∃ P, IsPathAlong (G.inside X) (verts.getD i 0) (verts.getD j 0) P`.
-/

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

public section

/-! ## 1. Pure Graph Reachability and Partition Lemmas -/

/-- If two labelings induce the same `Cited.partsOf G`, they assign equal labels to the same pairs
of vertices in `G`. -/
lemma label_eq_iff_of_partsOf_eq {G : Graph} {lbl₁ lbl₂ : List ℕ}
    (hparts : Cited.partsOf G lbl₁ = Cited.partsOf G lbl₂) {u v : ℕ}
    (hu : u < G.n) (hv : v < G.n) :
    lbl₁.getD u 0 = lbl₁.getD v 0 ↔ lbl₂.getD u 0 = lbl₂.getD v 0 := by
  have huV : u ∈ G.verts := Finset.mem_range.mpr hu
  have hvV : v ∈ G.verts := Finset.mem_range.mpr hv
  let f₁ : ℕ → Finset ℕ := fun w => G.verts.filter fun x => lbl₁.getD x 0 = lbl₁.getD w 0
  let f₂ : ℕ → Finset ℕ := fun w => G.verts.filter fun x => lbl₂.getD x 0 = lbl₂.getD w 0
  have hf1_mem : f₁ u ∈ Cited.partsOf G lbl₂ := by
    rw [← hparts]; exact Finset.mem_image.mpr ⟨u, huV, rfl⟩
  rcases Finset.mem_image.mp hf1_mem with ⟨w, _, hfw⟩
  have hfw' : f₂ w = f₁ u := hfw
  have hu_in_f1 : u ∈ f₁ u := Finset.mem_filter.mpr ⟨huV, rfl⟩
  have hu_in_f2w : u ∈ f₂ w := hfw' ▸ hu_in_f1
  have huw : lbl₂.getD u 0 = lbl₂.getD w 0 := (Finset.mem_filter.mp hu_in_f2w).2
  have hf_eq : f₁ u = f₂ u := by
    rw [← hfw']
    ext x
    simp only [f₂, Finset.mem_filter, huw]
  have hv_iff : v ∈ f₁ u ↔ v ∈ f₂ u := by rw [hf_eq]
  simp only [f₁, f₂, Finset.mem_filter, hvV, true_and] at hv_iff
  exact ⟨fun h => (hv_iff.mp h.symm).symm, fun h => (hv_iff.mpr h.symm).symm⟩

private lemma isPathAlong_map_getD {verts : List ℕ} {edges : List (ℕ × ℕ)} {i j : ℕ}
    {P : List ℕ}
    (hP : IsPathAlong (relabelGraph verts ((Graph.mk 0 edges).inside verts.toFinset)).edges i j P) :
    IsPathAlong ((Graph.mk 0 edges).inside verts.toFinset)
      (verts.getD i 0) (verts.getD j 0) (P.map fun x => verts.getD x 0) := by
  set X := verts.toFinset
  set G_X := relabelGraph verts ((Graph.mk 0 edges).inside X)
  rcases hP with ⟨hhead, hlast, hchain⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [List.head?_map, hhead]; rfl
  · rw [List.getLast?_map, hlast]; rfl
  · have hmem_edge : ∀ {x y : ℕ}, (x, y) ∈ G_X.edges →
        (verts.getD x 0, verts.getD y 0) ∈ (Graph.mk 0 edges).inside X := by
      intro x y hxy
      rcases List.mem_map.mp hxy with ⟨e, he, heq⟩
      have heX := (mem_inside_iff.mp he).2
      have h1m : e.1 ∈ verts := List.mem_toFinset.mp heX.1
      have h2m : e.2 ∈ verts := List.mem_toFinset.mp heX.2
      have hx : x = verts.idxOf e.1 := (Prod.mk.inj heq).1.symm
      have hy : y = verts.idxOf e.2 := (Prod.mk.inj heq).2.symm
      rw [hx, hy, nodup_getD_idxOf h1m, nodup_getD_idxOf h2m]
      exact he
    clear hhead hlast
    induction P with
    | nil => simp
    | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b bs =>
        rw [List.isChain_cons_cons] at hchain
        simp only [List.map_cons, List.isChain_cons_cons]
        refine ⟨?_, ih hchain.2⟩
        rcases hchain.1 with hab | hba
        · left; exact hmem_edge hab
        · right; exact hmem_edge hba

private lemma isPathAlong_map_idxOf {verts : List ℕ} {edges : List (ℕ × ℕ)}
    (hnd : verts.Nodup) {i j : ℕ} (hi : i < verts.length) (hj : j < verts.length)
    {Q : List ℕ}
    (hQ : IsPathAlong ((Graph.mk 0 edges).inside verts.toFinset)
      (verts.getD i 0) (verts.getD j 0) Q) :
    IsPathAlong (relabelGraph verts ((Graph.mk 0 edges).inside verts.toFinset)).edges i j
      (Q.map fun u => verts.idxOf u) := by
  set X := verts.toFinset
  rcases hQ with ⟨hhead, hlast, hchain⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [List.head?_map, hhead]
    simp only [Option.map_some, Option.some.injEq]
    exact nodup_idxOf_getD hnd hi
  · rw [List.getLast?_map, hlast]
    simp only [Option.map_some, Option.some.injEq]
    exact nodup_idxOf_getD hnd hj
  · clear hhead hlast hi hj
    induction Q with
    | nil => simp
    | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b bs =>
        rw [List.isChain_cons_cons] at hchain
        simp only [List.map_cons, List.isChain_cons_cons]
        refine ⟨?_, ih hchain.2⟩
        rcases hchain.1 with hab | hba
        · left
          exact List.mem_map.mpr ⟨(a, b), hab, rfl⟩
        · right
          exact List.mem_map.mpr ⟨(b, a), hba, rfl⟩

/-- Reachability in the relabeled induced subgraph `relabelGraph verts ((Graph.mk 0 edges).inside X)`
coincides with reachability in `(Graph.mk 0 edges).inside X` via `verts.getD · 0`. -/
lemma reachable_relabelGraph_inside_iff {verts : List ℕ} {edges : List (ℕ × ℕ)}
    (hnd : verts.Nodup) {i j : ℕ} (hi : i < verts.length) (hj : j < verts.length) :
    (∃ P, IsPathAlong (relabelGraph verts ((Graph.mk 0 edges).inside verts.toFinset)).edges i j P) ↔
      ∃ Q, IsPathAlong ((Graph.mk 0 edges).inside verts.toFinset)
        (verts.getD i 0) (verts.getD j 0) Q := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.map fun x => verts.getD x 0, isPathAlong_map_getD hP⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨Q.map fun u => verts.idxOf u, isPathAlong_map_idxOf hnd hi hj hQ⟩

/-! ## 2. Workspace, Procedure Definitions, and `NoRand` -/

/-- Contiguous scratch workspace size required by `compLabelsInEntry`:
- `[workAddr, workAddr + 2 + 2 * mE)`: encoded induced subgraph `G_X`;
- `[workAddr + 2 + 2 * mE, workAddr + 2 * k + 6 * mE + 3)`: CSR of `G_X`;
- `[workAddr + 2 * k + 6 * mE + 3, workAddr + 3 * k + 6 * mE + 3)`: BFS queue of size `k`. -/
def compLabelsInWorkSpace (k mE : ℕ) : ℕ :=
  3 * k + 6 * mE + 3

/-- Entry procedure for connected-component labeling inside `X`.
Arguments `r0..r6 = [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr]`.
Calls `b + 1` (`inducedSubgraphProc`), `b + 2` (`buildCsrProc`), and `b + 3` (`bfsLabelsProc`). -/
def compLabelsInEntry (b : ℕ) : Stmt :=
  seqStmts [
    -- r7 := mX = inducedSubgraphProc(k, vertsAddr, mE, edgesAddr, locAddr, workAddr)
    .call 7 (b + 1) [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6],
    -- r8 := csrAddr = workAddr + 2 + 2 * mE
    .assign 8 (.bin .add (.bin .add (.reg 6) (.const 2)) (.bin .mul (.const 2) (.reg 2))),
    -- r9 := buildCsrProc(workAddr, csrAddr)
    .call 9 (b + 2) [.reg 6, .reg 8],
    -- r10 := queueAddr = csrAddr + 2 * k + 1 + 4 * mE
    .assign 10 (.bin .add
      (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 0))) (.const 1))
      (.bin .mul (.const 4) (.reg 2))),
    -- r11 := bfsLabelsProc(k, mX, csrAddr, queueAddr, outLabelAddr)
    .call 11 (b + 3) [.reg 0, .reg 7, .reg 8, .reg 10, .reg 5],
    .ret (.const 0)
  ]

/-- Self-contained 4-procedure module for connected-component labeling inside `X`. -/
def compLabelsInProcs (b : ℕ) : List Stmt :=
  [compLabelsInEntry b, inducedSubgraphProc, buildCsrProc, bfsLabelsProc]

lemma compLabelsInEntry_noRand (b : ℕ) : (compLabelsInEntry b).NoRand := by
  simp [compLabelsInEntry, seqStmts, Stmt.NoRand]

lemma compLabelsInProcs_noRand (b : ℕ) : ∀ s ∈ compLabelsInProcs b, s.NoRand := by
  intro s hs
  simp only [compLabelsInProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact compLabelsInEntry_noRand b
  · exact inducedSubgraphProc_noRand
  · exact buildCsrProc_noRand
  · exact bfsLabelsProc_noRand

/-! ## 3. Word Bounds, Disjointness, Cost, and Contract -/

/-- Word-size bounds ensuring every address and intermediate arithmetic fits in `< 2 ^ w`. -/
def CompLabelsInWordBound (w n k mE vertsAddr edgesAddr locAddr outLabelAddr workAddr : ℕ) : Prop :=
  vertsAddr + k < 2 ^ w ∧
  edgesAddr + 2 * mE < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  outLabelAddr + k < 2 ^ w ∧
  workAddr + compLabelsInWorkSpace k mE < 2 ^ w ∧
  k + 1 < 2 ^ w ∧
  16 < 2 ^ w

/-- Buffer disjointness conditions for `compLabelsInEntry`. -/
def CompLabelsInDisjoint (n k mE vertsAddr edgesAddr locAddr outLabelAddr workAddr : ℕ) : Prop :=
  DisjointRange locAddr n vertsAddr k ∧
  DisjointRange locAddr n edgesAddr (2 * mE) ∧
  DisjointRange locAddr n workAddr (compLabelsInWorkSpace k mE) ∧
  DisjointRange workAddr (compLabelsInWorkSpace k mE) vertsAddr k ∧
  DisjointRange workAddr (compLabelsInWorkSpace k mE) edgesAddr (2 * mE) ∧
  DisjointRange workAddr (compLabelsInWorkSpace k mE) outLabelAddr k

/-- Explicit deterministic time bound `O(|X| + |E| + 1)` (independent of `n`). -/
def compLabelsInCost (k mE : ℕ) : ℕ :=
  650 * k + 500 * mE + 450

/-- Contract for `compLabelsInEntry`:
`args = [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr]`.
Writes connected-component labels `label[i] < k` of `G[X]` at `outLabelAddr + i` (`i < k`),
preserving all memory outside `[outLabelAddr, outLabelAddr + k)` and
`[workAddr, workAddr + compLabelsInWorkSpace k mE)` (so `locAddr` stays zeroed if disjoint from
`outLabelAddr`). -/
noncomputable def compLabelsInContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k vertsAddr mE edgesAddr locAddr outLabelAddr workAddr : ℕ)
      (verts : List ℕ) (edges : List (ℕ × ℕ)),
      args = [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr] ∧
      verts.length = k ∧
      verts.Nodup ∧
      (∀ u ∈ verts, u < n) ∧
      edges.length = mE ∧
      (∀ e ∈ edges, e.1 < n ∧ e.2 < n) ∧
      ListAt mem vertsAddr verts ∧
      EdgesAt mem edgesAddr edges ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      CompLabelsInWordBound w n k mE vertsAddr edgesAddr locAddr outLabelAddr workAddr ∧
      CompLabelsInDisjoint n k mE vertsAddr edgesAddr locAddr outLabelAddr workAddr
  post args mem v mem' :=
    let k := args.getD 0 0
    let vertsAddr := args.getD 1 0
    let mE := args.getD 2 0
    let edgesAddr := args.getD 3 0
    let outLabelAddr := args.getD 5 0
    let workAddr := args.getD 6 0
    let verts := readList mem vertsAddr k
    let edges := readEdges mem edgesAddr mE
    let X := verts.toFinset
    let G_X := relabelGraph verts ((Graph.mk 0 edges).inside X)
    let label := readList mem' outLabelAddr k
    v = 0 ∧
    (∀ i < k, mem' (outLabelAddr + i) < k) ∧
    Cited.partsOf G_X label = Cited.partsOf G_X (compLabels G_X) ∧
    (∀ i < k, ∀ j < k,
      mem' (outLabelAddr + i) = mem' (outLabelAddr + j) ↔
        ∃ P, IsPathAlong ((Graph.mk 0 edges).inside X) (verts.getD i 0) (verts.getD j 0) P) ∧
    PreservedOutside2 mem mem' outLabelAddr (outLabelAddr + k)
      workAddr (workAddr + compLabelsInWorkSpace k mE)
  cost args _mem :=
    compLabelsInCost (args.getD 0 0) (args.getD 2 0)

/-! ## 4. Main Specification Theorem and Non-Vacuity Example -/

/-- `compLabelsInProcs b` meets `compLabelsInContract w` in `O(|X| + |E| + 1)` deterministic steps,
without scanning `range n`. -/
theorem compLabelsIn_spec {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (compLabelsInProcs b)) :
    MeetsContract w p b (compLabelsInContract w) := by
  have hEntry : p.procs[b]? = some (compLabelsInEntry b) := by
    simpa [compLabelsInProcs] using hp 0 (by simp [compLabelsInProcs])
  have hp_ind : p.HasAt (b + 1) [inducedSubgraphProc] := by
    intro i hi
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simpa [compLabelsInProcs] using hp 1 (by simp [compLabelsInProcs])
  have hp_csr : p.HasAt (b + 2) [buildCsrProc] := by
    intro i hi
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simpa [compLabelsInProcs] using hp 2 (by simp [compLabelsInProcs])
  have hp_bfs : p.HasAt (b + 3) [bfsLabelsProc] := by
    intro i hi
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simpa [compLabelsInProcs] using hp 3 (by simp [compLabelsInProcs])
  have hSpec_ind := inducedSubgraph_spec (w := w) hp_ind
  have hSpec_csr := buildCsr_spec (w := w) hp_csr
  have hSpec_bfs := bfsLabels_spec (w := w) p (b + 3) hp_bfs
  intro args mem pos ω _ hpre
  rcases hpre with ⟨n, k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr,
    verts, edges, hargs, hvlen, hnd, hverts_lt, hElen, hE_lt, hverts_at, hE_at, hloc0, hw, hdisj⟩
  subst hargs
  rcases hw with ⟨hv_w, he_w, hloc_w, hout_w, hwork_w, hk1_w, hw16⟩
  rcases hdisj with ⟨hd_lv, hd_le, hd_lw, hd_wv, hd_we, hd_wo⟩
  have hws_def : compLabelsInWorkSpace k mE = 3 * k + 6 * mE + 3 := rfl
  set X := verts.toFinset
  set G_X := relabelGraph verts ((Graph.mk 0 edges).inside X)
  have hGX_n : G_X.n = k := by simp [G_X, relabelGraph, hvlen]
  have hGX_valid : G_X.IsValid := by
    apply relabelGraph_isValid
    intro e he
    exact (mem_inside_iff.mp he).2
  have hGX_m_le : G_X.m ≤ mE := by
    rw [relabelGraph_m, ← hElen]
    exact inside_length_le_m (Graph.mk 0 edges) X
  have hread_verts : readList mem vertsAddr k = verts := hvlen ▸ readList_eq_of_listAt hverts_at
  have hread_edges : readEdges mem edgesAddr mE = edges := hElen ▸ readEdges_eq_of_edgesAt hE_at
  -- Call 1 preconditions for `inducedSubgraphProc`
  have hind_pre : (inducedSubgraphContract w).pre
      [k, vertsAddr, mE, edgesAddr, locAddr, workAddr] mem := by
    refine ⟨n, k, vertsAddr, mE, edgesAddr, locAddr, workAddr, verts, edges,
      rfl, hvlen, hnd, hverts_lt, hElen, hE_lt, hverts_at, hE_at, hloc0, ?_, ?_⟩
    · refine ⟨hv_w, he_w, hloc_w, by omega, hk1_w, hw16⟩
    · refine ⟨hd_lv, hd_le, ?_, ?_, ?_⟩
      · rcases hd_lw with h | h <;> [left; right] <;> omega
      · rcases hd_wv with h | h <;> [left; right] <;> omega
      · rcases hd_we with h | h <;> [left; right] <;> omega
  have hind_words : ∀ a ∈ ([k, vertsAddr, mE, edgesAddr, locAddr, workAddr] : List ℕ), a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  -- Run the full sequence
  have hrun : ∃ o st' c,
      Runs w p ω (compLabelsInEntry b)
        (startState [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr] mem pos) o st' c ∧
      (compLabelsInContract w).post
        [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr] mem o.value st'.mem ∧
      c ≤ compLabelsInCost k mE := by
    refine runs_start_le ?_
    dsimp only [compLabelsInEntry, seqStmts]
    -- Step 1: call `inducedSubgraphProc`
    have hE1 : evalArgs w
        (startState [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr] mem pos)
        [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6] =
        some [k, vertsAddr, mE, edgesAddr, locAddr, workAddr] := by
      simp [evalArgs, Expr.eval, startState]
    refine runs_seq_call_le hSpec_ind hE1 hind_words hind_pre ?_
    intro mX1 mem1 pos1 hpost1
    dsimp only [inducedSubgraphContract, startState] at hpost1
    simp only [List.getD_cons_zero, List.getD_cons_succ, hread_verts, hread_edges] at hpost1
    rcases hpost1 with ⟨hmX1_eq, _, _, _, hGX_at1, hfr1⟩
    -- Step 2: compute `csrAddr := workAddr + 2 + 2 * mE`
    set csrAddr := workAddr + 2 + 2 * mE
    refine runs_seq_assign_le (v := csrAddr)
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (v := workAddr) (by simp [startState]))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (v := mE) (by simp [startState])) (by omega))
        (by omega)) ?_
    -- Step 3: call `buildCsrProc(workAddr, csrAddr)`
    have hcsr_pre : (buildCsrContract w).pre [workAddr, csrAddr] mem1 := by
      refine ⟨workAddr, csrAddr, G_X, rfl, hGX_at1, hGX_valid, ?_, ?_, by omega⟩
      · rw [graph_encode_length]; omega
      · omega
    have hcsr_words : ∀ a ∈ ([workAddr, csrAddr] : List ℕ), a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    have hE2 : evalArgs w
        { regs := Function.update
            (Function.update
              (startState [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr] mem pos).regs
              7 mX1) 8 csrAddr,
          mem := mem1, pos := pos1 }
        [.reg 6, .reg 8] = some [workAddr, csrAddr] := by
      simp [evalArgs, Expr.eval, startState]
    refine runs_seq_call_le hSpec_csr hE2 hcsr_words hcsr_pre ?_
    intro v2 mem2 pos2 hpost2
    have hread_GX : Cited.readGraph mem1 workAddr = G_X := graphAt_iff_readGraph.mp hGX_at1
    dsimp only [buildCsrContract] at hpost2
    simp only [List.getD_cons_zero, List.getD_cons_succ, hread_GX] at hpost2
    rcases hpost2 with ⟨_, hcsr2, hfr2⟩
    -- Step 4: compute `queueAddr := csrAddr + 2 * k + 1 + 4 * mE`
    set queueAddr := csrAddr + 2 * k + 1 + 4 * mE
    refine runs_seq_assign_le (v := queueAddr)
      (Expr.eval_add
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (v := csrAddr) (by simp))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := k) (by simp [startState])) (by omega))
            (by omega))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (v := mE) (by simp [startState])) (by omega))
        (by omega)) ?_
    -- Step 5: call `bfsLabelsProc(k, mX1, csrAddr, queueAddr, outLabelAddr)`
    have hbfs_pre : (bfsLabelsContract w).pre [k, mX1, csrAddr, queueAddr, outLabelAddr] mem2 := by
      dsimp only [bfsLabelsContract]
      refine ⟨k, mX1, csrAddr, queueAddr, outLabelAddr, G_X, rfl, hGX_n, hmX1_eq.symm, hGX_valid,
        hcsr2, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · left; omega
      · rcases hd_wo with h | h <;> [left; right] <;> omega
      · rcases hd_wo with h | h <;> [left; right] <;> omega
      · omega
      · omega
      · omega
    have hbfs_words : ∀ a ∈ ([k, mX1, csrAddr, queueAddr, outLabelAddr] : List ℕ), a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
    have hE3 : evalArgs w
        { regs := Function.update
            (Function.update
              (Function.update
                (Function.update
                  (startState [k, vertsAddr, mE, edgesAddr, locAddr, outLabelAddr, workAddr] mem pos).regs
                  7 mX1) 8 csrAddr) 9 v2) 10 queueAddr,
          mem := mem2, pos := pos2 }
        [.reg 0, .reg 7, .reg 8, .reg 10, .reg 5] =
        some [k, mX1, csrAddr, queueAddr, outLabelAddr] := by
      simp [evalArgs, Expr.eval, startState]
    refine runs_seq_call_le hSpec_bfs hE3 hbfs_words hbfs_pre ?_
    intro v3 mem3 pos3 hpost3
    dsimp only [bfsLabelsContract] at hpost3
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hpost3
    rcases hpost3 with ⟨hfr3, hbfs_all⟩
    rcases hbfs_all G_X hGX_n hmX1_eq.symm hGX_valid hcsr2 with ⟨_, hlbl_lt, hparts_eq⟩
    -- Step 6: `ret 0`
    refine runs_ret_le (Expr.eval_const (by omega)) ?_ ?_
    · dsimp only [compLabelsInContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hread_verts, hread_edges]
      have hread_eq : readList mem3 outLabelAddr k =
          (List.range k).map fun x => mem3 (outLabelAddr + x) := rfl
      refine ⟨trivial, ?_, ?_, ?_, ?_⟩
      · intro i hi
        exact hGX_n ▸ hlbl_lt i (hGX_n.symm ▸ hi)
      · rw [hread_eq]; exact hparts_eq
      · intro i hi j hj
        have hi_len : i < verts.length := hvlen.symm ▸ hi
        have hj_len : j < verts.length := hvlen.symm ▸ hj
        have hget_i : (readList mem3 outLabelAddr k).getD i 0 = mem3 (outLabelAddr + i) := by
          simp [readList, List.getD_eq_getElem?_getD, hi]
        have hget_j : (readList mem3 outLabelAddr k).getD j 0 = mem3 (outLabelAddr + j) := by
          simp [readList, List.getD_eq_getElem?_getD, hj]
        rw [← hget_i, ← hget_j]
        rw [label_eq_iff_of_partsOf_eq (hread_eq ▸ hparts_eq) (hGX_n.symm ▸ hi) (hGX_n.symm ▸ hj)]
        rw [compLabels_eq_iff_reachable hGX_valid (hGX_n.symm ▸ hi) (hGX_n.symm ▸ hj)]
        exact reachable_relabelGraph_inside_iff hnd hi_len hj_len
      · intro a ha_out ha_work
        have ha_q : a < queueAddr ∨ queueAddr + k ≤ a := by
          rcases ha_work with h | h <;> [left; right] <;> omega
        have ha_csr : a < csrAddr ∨ csrAddr + 2 * G_X.n + 1 + 4 * G_X.m ≤ a := by
          rcases ha_work with h | h <;> [left; right] <;> omega
        have ha_gx : a < workAddr ∨ workAddr + 2 + 2 * mE ≤ a := by
          rcases ha_work with h | h <;> [left; right] <;> omega
        rw [hfr3 a ha_q ha_out, hfr2 a ha_csr, hfr1 a ha_gx]
    · dsimp only [inducedSubgraphContract, buildCsrContract, bfsLabelsContract,
        inducedSubgraphCost, compLabelsInCost, Expr.size, argsSize]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hread_GX]
      omega
  rcases hrun with ⟨o, st', c, hr, hpost, hcost⟩
  exact ⟨compLabelsInEntry b, hEntry, o, st', c, hr, hpost, by simpa [compLabelsInContract] using hcost⟩

/-- Non-vacuity witness for `compLabelsInContract 16`. -/
theorem compLabelsInContract_pre_example :
    ∃ args mem, (∀ a ∈ args, a < 2 ^ 16) ∧ (compLabelsInContract 16).pre args mem := by
  let verts : List ℕ := [1, 2, 4]
  let edges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3)]
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 4
    else if a = 10 then 0 else if a = 11 then 1
    else if a = 12 then 1 else if a = 13 then 2
    else if a = 14 then 2 else if a = 15 then 3
    else 0
  let args : List ℕ := [3, 0, 3, 10, 20, 40, 100]
  refine ⟨args, mem, by decide, ?_⟩
  refine ⟨5, 3, 0, 3, 10, 20, 40, 100, verts, edges,
    rfl, rfl, by decide, by decide, rfl, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rcases i with _ | _ | _ | i <;> simp [verts, mem] at hi ⊢; omega
  · intro j hj; rcases j with _ | _ | _ | j <;> simp [edges, mem] at hj ⊢; omega
  · intro u hu; simp only [mem]; split_ifs <;> omega
  · unfold CompLabelsInWordBound compLabelsInWorkSpace; decide
  · unfold CompLabelsInDisjoint compLabelsInWorkSpace DisjointRange; decide

end

end MinCostFlow.ExpanderDecomp
