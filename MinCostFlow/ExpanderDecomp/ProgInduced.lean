module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgRelabel
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase

import Mathlib.Tactic.Linarith

/-!
# Induced Subgraph `G[X]` in Compact Local IDs (`inducedSubgraphProc`)

Implements and verifies `inducedSubgraphProc`: given a duplicate-free vertex list `verts` of
length `k` (`X = verts.toFinset`), an edge list `edges` of length `mE`, and a zero-initialized
local-ID table `locAddr` of size `n`, builds `G_X = relabelGraph verts ((Graph.mk 0 edges).inside X)`
at `outGraphAddr` (in `GraphAt` format) and returns `G_X.m`, restoring `locAddr` to all zeros.

All scans are local to `X` and `edges`, costing `O(|X| + |E| + 1)` steps (never scanning `range n`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Register Map, Procedure, Bounds, and Contract -/

abbrev indK : ℕ := 0
abbrev indVerts : ℕ := 1
abbrev indME : ℕ := 2
abbrev indEdges : ℕ := 3
abbrev indLoc : ℕ := 4
abbrev indOutG : ℕ := 5

abbrev indI : ℕ := 6
abbrev indOutM : ℕ := 7
abbrev indU : ℕ := 8
abbrev indV : ℕ := 9
abbrev indLU : ℕ := 10
abbrev indLV : ℕ := 11

/-- Deterministic Word-RAM procedure building the compact local induced subgraph `G[X]` at
`outGraphAddr` and returning its edge count `m_X`.
Args: `[k, vertsAddr, mE, edgesAddr, locAddr, outGraphAddr]`. -/
def inducedSubgraphProc : Stmt :=
  seqStmts
    [ forRange indI (.const 0) (.reg indK)
        (seqStmts
          [ .assign indU (.load (.bin .add (.reg indVerts) (.reg indI)))
          , .store (.bin .add (.reg indLoc) (.reg indU)) (.bin .add (.reg indI) (.const 1)) ])
    , .assign indOutM (.const 0)
    , forRange indI (.const 0) (.reg indME)
        (seqStmts
          [ .assign indU (.load (.bin .add (.reg indEdges) (.bin .mul (.const 2) (.reg indI))))
          , .assign indV (.load (.bin .add (.bin .add (.reg indEdges) (.bin .mul (.const 2) (.reg indI))) (.const 1)))
          , .assign indLU (.load (.bin .add (.reg indLoc) (.reg indU)))
          , .assign indLV (.load (.bin .add (.reg indLoc) (.reg indV)))
          , .cond (.bin .lt (.const 0) (.reg indLU))
              (.cond (.bin .lt (.const 0) (.reg indLV))
                (seqStmts
                  [ .store (.bin .add (.bin .add (.reg indOutG) (.const 2)) (.bin .mul (.const 2) (.reg indOutM)))
                      (.bin .sub (.reg indLU) (.const 1))
                  , .store (.bin .add (.bin .add (.reg indOutG) (.const 3)) (.bin .mul (.const 2) (.reg indOutM)))
                      (.bin .sub (.reg indLV) (.const 1))
                  , .assign indOutM (.bin .add (.reg indOutM) (.const 1)) ])
                .nop)
              .nop ])
    , .store (.reg indOutG) (.reg indK)
    , .store (.bin .add (.reg indOutG) (.const 1)) (.reg indOutM)
    , forRange indI (.const 0) (.reg indK)
        (seqStmts
          [ .assign indU (.load (.bin .add (.reg indVerts) (.reg indI)))
          , .store (.bin .add (.reg indLoc) (.reg indU)) (.const 0) ])
    , .ret (.reg indOutM) ]

/-- Explicit step bound `O(|X| + |E| + 1)` for `inducedSubgraphProc`. -/
def inducedSubgraphCost (k mE : ℕ) : ℕ :=
  100 * k + 120 * mE + 100

/-- Word-size bound for `inducedSubgraphProc`. -/
def InducedWordBound (w n k mE vertsAddr edgesAddr locAddr outGraphAddr : ℕ) : Prop :=
  vertsAddr + k < 2 ^ w ∧
  edgesAddr + 2 * mE < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  outGraphAddr + 2 + 2 * mE < 2 ^ w ∧
  k + 1 < 2 ^ w ∧
  16 < 2 ^ w

/-- Disjointness of mutable arrays (`locAddr`, `outGraphAddr`) from inputs and each other. -/
def InducedDisjoint (n k mE vertsAddr edgesAddr locAddr outGraphAddr : ℕ) : Prop :=
  DisjointRange locAddr n vertsAddr k ∧
  DisjointRange locAddr n edgesAddr (2 * mE) ∧
  DisjointRange locAddr n outGraphAddr (2 + 2 * mE) ∧
  DisjointRange outGraphAddr (2 + 2 * mE) vertsAddr k ∧
  DisjointRange outGraphAddr (2 + 2 * mE) edgesAddr (2 * mE)

/-- Word-RAM contract for `inducedSubgraphProc`: builds `G_X = relabelGraph verts ((Graph.mk 0 edges).inside X)`
at `outGraphAddr` in `O(|X| + |E| + 1)` time while preserving `locAddr` (restored to all zeros) and
every cell outside `[outGraphAddr, outGraphAddr + 2 + 2 * mE)`. -/
def inducedSubgraphContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k vertsAddr mE edgesAddr locAddr outGraphAddr : ℕ)
      (verts : List ℕ) (edges : List (ℕ × ℕ)),
      args = [k, vertsAddr, mE, edgesAddr, locAddr, outGraphAddr] ∧
      verts.length = k ∧ verts.Nodup ∧ (∀ u ∈ verts, u < n) ∧
      edges.length = mE ∧ (∀ e ∈ edges, e.1 < n ∧ e.2 < n) ∧
      ListAt mem vertsAddr verts ∧
      EdgesAt mem edgesAddr edges ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      InducedWordBound w n k mE vertsAddr edgesAddr locAddr outGraphAddr ∧
      InducedDisjoint n k mE vertsAddr edgesAddr locAddr outGraphAddr
  post args mem v mem' :=
    let k := args.getD 0 0
    let vertsAddr := args.getD 1 0
    let mE := args.getD 2 0
    let edgesAddr := args.getD 3 0
    let outGraphAddr := args.getD 5 0
    let verts := readList mem vertsAddr k
    let X := verts.toFinset
    let edges := readEdges mem edgesAddr mE
    let G_X := relabelGraph verts ((Graph.mk 0 edges).inside X)
    v = G_X.m ∧
    v ≤ mE ∧
    G_X.n = k ∧
    G_X.IsValid ∧
    GraphAt mem' outGraphAddr G_X ∧
    MemFrame mem mem' outGraphAddr (outGraphAddr + 2 + 2 * mE)
  cost args _mem :=
    inducedSubgraphCost (args.getD 0 0) (args.getD 2 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma inducedSubgraphProc_noRand : inducedSubgraphProc.NoRand := by
  simp [inducedSubgraphProc, seqStmts, forRange, forUp, Stmt.NoRand]

private structure IndRegs (k vertsAddr mE edgesAddr locAddr outGraphAddr : ℕ)
    (st : State) : Prop where
  r_k : st.regs indK = k
  r_verts : st.regs indVerts = vertsAddr
  r_mE : st.regs indME = mE
  r_edges : st.regs indEdges = edgesAddr
  r_loc : st.regs indLoc = locAddr
  r_outG : st.regs indOutG = outGraphAddr

private lemma indRegs_of_agree {k vertsAddr mE edgesAddr locAddr outGraphAddr : ℕ}
    {st st' : State}
    (h : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st)
    (hag : ∀ r ≤ 5, st'.regs r = st.regs r) :
    IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st' :=
  ⟨(hag 0 (by omega)).trans h.r_k,
   (hag 1 (by omega)).trans h.r_verts,
   (hag 2 (by omega)).trans h.r_mE,
   (hag 3 (by omega)).trans h.r_edges,
   (hag 4 (by omega)).trans h.r_loc,
   (hag 5 (by omega)).trans h.r_outG⟩

private lemma indRegs_update_ge {k vertsAddr mE edgesAddr locAddr outGraphAddr : ℕ}
    {st : State} {r v : ℕ} (hr6 : 6 ≤ r)
    (h : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st) :
    IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr
      { st with regs := Function.update st.regs r v } :=
  indRegs_of_agree h fun j hj => Function.update_of_ne (by omega) v st.regs

private lemma indRegs_update_mem {k vertsAddr mE edgesAddr locAddr outGraphAddr : ℕ}
    {st : State} {mem' : ℕ → ℕ}
    (h : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st) :
    IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr { st with mem := mem' } :=
  indRegs_of_agree h fun _ _ => rfl

/-- Stage 1 of `inducedSubgraphProc`: sets `locAddr[verts[i]] := i + 1` on a zeroed `locAddr`. -/
private lemma indFillLoc1_triple {w n k mE vertsAddr edgesAddr locAddr outGraphAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (st₀ : State)
    (hvlen : verts.length = k) (hnd : verts.Nodup)
    (hverts_lt : ∀ u ∈ verts, u < n) (hlist : ListAt mem vertsAddr verts)
    (hloc0 : ∀ u < n, mem (locAddr + u) = 0)
    (hdisj : DisjointRange locAddr n vertsAddr k)
    (hw : InducedWordBound w n k mE vertsAddr edgesAddr locAddr outGraphAddr)
    (hregs : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st₀)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀)
      (forRange indI (.const 0) (.reg indK)
        (seqStmts
          [ .assign indU (.load (.bin .add (.reg indVerts) (.reg indI)))
          , .store (.bin .add (.reg indLoc) (.reg indU)) (.bin .add (.reg indI) (.const 1)) ]))
      (normalPost fun st' =>
        IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st' ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem locAddr (locAddr + n) ∧
        (∀ u < n, st'.mem (locAddr + u) = if u ∈ verts then verts.idxOf u + 1 else 0))
      (fun _ => 38 * k + 20) := by
  rcases hw with ⟨hvk_w, _, hloc_w, _, hk1_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st ∧
    st.regs indI = i ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem locAddr (locAddr + n) ∧
    (∀ u < n, st.mem (locAddr + u) =
      if u ∈ verts.take i then verts.idxOf u + 1 else 0)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := indI) (lo := .const 0) (hi := .reg indK)
    (body := seqStmts
      [ .assign indU (.load (.bin .add (.reg indVerts) (.reg indI)))
      , .store (.bin .add (.reg indLoc) (.reg indU)) (.bin .add (.reg indI) (.const 1)) ])
    (P := fun st => st = st₀) (Inv := Inv) 22 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), indRegs_update_ge (r := indI) (by decide) hregs,
        by simp, rfl, hmem ▸ memFrame_refl mem _ _, fun u hu => by simp [hmem, hloc0 u hu]⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hfr, hmap⟩
      have hi_lt : i < verts.length := hvlen ▸ hilt
      have hv_lt : verts[i]'hi_lt < n := hverts_lt _ (List.getElem_mem hi_lt)
      have hmem_v : st.mem (vertsAddr + i) = verts[i]'hi_lt := by
        rw [hfr (vertsAddr + i) (disjointRange_outside hdisj (by omega) (by omega))]
        exact hlist i hi_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := verts[i]'hi_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_verts) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_v) ?_
      refine runs_store_le (x := locAddr + verts[i]'hi_lt) (v := i + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
          (Expr.eval_reg_of_eq (v := verts[i]'hi_lt) (by simp)) (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq (v := i) (by simp [hi]))
          (Expr.eval_const hw2) (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨indRegs_update_ge (r := indI) (by decide)
          (indRegs_update_mem (indRegs_update_ge (r := indU) (by decide) hr)),
        by simp, hpos, memFrame_trans hfr (memFrame_update (by omega) (by omega)), ?_⟩, by simp [hi]⟩
      intro u hu
      dsimp only
      by_cases huv : u = verts[i]'hi_lt
      · subst huv
        have hidx : verts.idxOf (verts[i]'hi_lt) = i := by
          have hlt := List.idxOf_lt_length_of_mem (List.getElem_mem hi_lt)
          exact (List.Nodup.getElem_inj_iff hnd).mp (List.getElem_idxOf hlt)
        rw [List.take_succ_eq_append_getElem hi_lt]
        simp only [Function.update_self, List.mem_append, List.mem_singleton, or_true, ↓reduceIte, hidx]
      · rw [Function.update_of_ne (by omega), List.take_succ_eq_append_getElem hi_lt]
        simp only [List.mem_append, List.mem_singleton, huv, or_false]
        exact hmap u hu)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hpos, hfr, hmap⟩
    refine ⟨hr, hpos, hfr, fun u hu => ?_⟩
    have := hmap u hu
    rwa [← hvlen, List.take_length] at this
  · exact False.elim hq

/-- Stage 2 of `inducedSubgraphProc`: filters and relabels edges with both endpoints in `X`. -/
private lemma indFilterEdges_triple {w n k mE vertsAddr edgesAddr locAddr outGraphAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (edges : List (ℕ × ℕ)) (st₀ : State)
    (hvlen : verts.length = k) (hElen : edges.length = mE)
    (hE_lt : ∀ e ∈ edges, e.1 < n ∧ e.2 < n)
    (hE_at : EdgesAt mem edgesAddr edges)
    (hloc_map : ∀ u < n, mem (locAddr + u) = if u ∈ verts then verts.idxOf u + 1 else 0)
    (hdisj_ol : DisjointRange outGraphAddr (2 + 2 * mE) locAddr n)
    (hdisj_oe : DisjointRange outGraphAddr (2 + 2 * mE) edgesAddr (2 * mE))
    (hw : InducedWordBound w n k mE vertsAddr edgesAddr locAddr outGraphAddr)
    (hregs : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st₀)
    (hmem : st₀.mem = mem) (houtM0 : st₀.regs indOutM = 0) :
    let X := verts.toFinset
    let esX := relabelEdges verts ((Graph.mk 0 edges).inside X)
    Triple w p (fun st => st = st₀)
      (forRange indI (.const 0) (.reg indME)
        (seqStmts
          [ .assign indU (.load (.bin .add (.reg indEdges) (.bin .mul (.const 2) (.reg indI))))
          , .assign indV (.load (.bin .add (.bin .add (.reg indEdges) (.bin .mul (.const 2) (.reg indI))) (.const 1)))
          , .assign indLU (.load (.bin .add (.reg indLoc) (.reg indU)))
          , .assign indLV (.load (.bin .add (.reg indLoc) (.reg indV)))
          , .cond (.bin .lt (.const 0) (.reg indLU))
              (.cond (.bin .lt (.const 0) (.reg indLV))
                (seqStmts
                  [ .store (.bin .add (.bin .add (.reg indOutG) (.const 2)) (.bin .mul (.const 2) (.reg indOutM)))
                      (.bin .sub (.reg indLU) (.const 1))
                  , .store (.bin .add (.bin .add (.reg indOutG) (.const 3)) (.bin .mul (.const 2) (.reg indOutM)))
                      (.bin .sub (.reg indLV) (.const 1))
                  , .assign indOutM (.bin .add (.reg indOutM) (.const 1)) ])
                .nop)
              .nop ]))
      (normalPost fun st' =>
        IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st' ∧
        st'.regs indOutM = esX.length ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem outGraphAddr (outGraphAddr + 2 + 2 * mE) ∧
        EdgesAt st'.mem (outGraphAddr + 2) esX)
      (fun _ => 115 * mE + 25) := by
  intro X esX
  rcases hw with ⟨_, he_w, hloc_w, hout_w, hk1_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  let pref : ℕ → List (ℕ × ℕ) := fun i =>
    relabelEdges verts ((edges.take i).filter fun e => decide (e.1 ∈ X) && decide (e.2 ∈ X))
  have hpref_len : ∀ i, (pref i).length ≤ i := fun i => by
    simp only [pref, relabelEdges, List.length_map]
    exact le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  let Inv : ℕ → State → Prop := fun i st =>
    IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st ∧
    st.regs indI = i ∧ st.regs indOutM = (pref i).length ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem outGraphAddr (outGraphAddr + 2 + 2 * mE) ∧
    EdgesAt st.mem (outGraphAddr + 2) (pref i)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := indI) (lo := .const 0) (hi := .reg indME)
    (body := seqStmts
      [ .assign indU (.load (.bin .add (.reg indEdges) (.bin .mul (.const 2) (.reg indI))))
      , .assign indV (.load (.bin .add (.bin .add (.reg indEdges) (.bin .mul (.const 2) (.reg indI))) (.const 1)))
      , .assign indLU (.load (.bin .add (.reg indLoc) (.reg indU)))
      , .assign indLV (.load (.bin .add (.reg indLoc) (.reg indV)))
      , .cond (.bin .lt (.const 0) (.reg indLU))
          (.cond (.bin .lt (.const 0) (.reg indLV))
            (seqStmts
              [ .store (.bin .add (.bin .add (.reg indOutG) (.const 2)) (.bin .mul (.const 2) (.reg indOutM)))
                  (.bin .sub (.reg indLU) (.const 1))
              , .store (.bin .add (.bin .add (.reg indOutG) (.const 3)) (.bin .mul (.const 2) (.reg indOutM)))
                  (.bin .sub (.reg indLV) (.const 1))
              , .assign indOutM (.bin .add (.reg indOutM) (.const 1)) ])
            .nop)
          .nop ])
    (P := fun st => st = st₀) (Inv := Inv) 100 0 mE (Nat.zero_le mE) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), indRegs_update_ge (r := indI) (by decide) hregs,
        by simp, by simp [pref, relabelEdges, houtM0], rfl, hmem ▸ memFrame_refl mem _ _,
        fun j hj => by simp [pref, relabelEdges] at hj⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_mE)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, houtM, hpos, hfr, hedg⟩
      have hiE : i < edges.length := hElen ▸ hilt
      set e := edges[i]'hiE
      have he_lt := hE_lt e (List.getElem_mem hiE)
      have hmem_u : st.mem (edgesAddr + 2 * i) = e.1 := by
        have hout := disjointRange_outside hdisj_oe (x := edgesAddr + 2 * i) (by omega) (by omega)
        rw [hfr (edgesAddr + 2 * i) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact (hE_at i hiE).1
      have hmem_v : st.mem (edgesAddr + 2 * i + 1) = e.2 := by
        have hout := disjointRange_outside hdisj_oe (x := edgesAddr + 2 * i + 1) (by omega) (by omega)
        rw [hfr (edgesAddr + 2 * i + 1) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact (hE_at i hiE).2
      set lu := if e.1 ∈ verts then verts.idxOf e.1 + 1 else 0
      set lv := if e.2 ∈ verts then verts.idxOf e.2 + 1 else 0
      have hloc_u : st.mem (locAddr + e.1) = lu := by
        have hout := disjointRange_outside hdisj_ol (x := locAddr + e.1) (by omega) (by omega)
        rw [hfr (locAddr + e.1) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact hloc_map e.1 he_lt.1
      have hloc_v : st.mem (locAddr + e.2) = lv := by
        have hout := disjointRange_outside hdisj_ol (x := locAddr + e.2) (by omega) (by omega)
        rw [hfr (locAddr + e.2) (by rcases hout with h | h <;> [left; right] <;> omega)]
        exact hloc_map e.2 he_lt.2
      have hplen := hpref_len i
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := e.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_edges)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hi) (by omega))
            (by omega)) hmem_u) ?_
      refine runs_seq_assign_le (v := e.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := edgesAddr) (by simp [hr.r_edges]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := i) (by simp [hi])) (by omega))
              (by omega))
            (Expr.eval_const hw2) (by omega)) hmem_v) ?_
      refine runs_seq_assign_le (v := lu)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
            (Expr.eval_reg_of_eq (v := e.1) (by simp)) (by omega)) hloc_u) ?_
      refine runs_seq_assign_le (v := lv)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
            (Expr.eval_reg_of_eq (v := e.2) (by simp)) (by omega)) hloc_v) ?_
      refine runs_cond_le
        (Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := lu) (by simp)) hw2)
        (fun hlu_ne => ?_) (fun hlu_0 => ?_)
      · have he1X : e.1 ∈ X := by
          have hpos_lu : 0 < lu := by by_contra h; simp [h] at hlu_ne
          by_contra hnot
          have : e.1 ∉ verts := fun hm => hnot (List.mem_toFinset.mpr hm)
          simp [lu, this] at hpos_lu
        have hlu_eq : lu = verts.idxOf e.1 + 1 := by simp [lu, List.mem_toFinset.mp he1X]
        have hlu_lt : lu < 2 ^ w := by
          have := List.idxOf_lt_length_of_mem (List.mem_toFinset.mp he1X); omega
        refine runs_cond_le
          (Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := lv) (by simp)) hw2)
          (fun hlv_ne => ?_) (fun hlv_0 => ?_)
        · have he2X : e.2 ∈ X := by
            have hpos_lv : 0 < lv := by by_contra h; simp [h] at hlv_ne
            by_contra hnot
            have : e.2 ∉ verts := fun hm => hnot (List.mem_toFinset.mpr hm)
            simp [lv, this] at hpos_lv
          have hlv_eq : lv = verts.idxOf e.2 + 1 := by simp [lv, List.mem_toFinset.mp he2X]
          have hlv_lt : lv < 2 ^ w := by
            have := List.idxOf_lt_length_of_mem (List.mem_toFinset.mp he2X); omega
          have hpref_succ : pref (i + 1) = pref i ++ [(verts.idxOf e.1, verts.idxOf e.2)] := by
            dsimp only [pref, relabelEdges]
            rw [List.take_succ_eq_append_getElem hiE, List.filter_append, List.filter_cons,
              List.filter_nil]
            simp [e, he1X, he2X]
          refine runs_seq_store_le (x := outGraphAddr + 2 + 2 * (pref i).length) (v := verts.idxOf e.1)
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (v := outGraphAddr) (by simp [hr.r_outG]))
                (Expr.eval_const (by omega)) (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := (pref i).length) (by simp [houtM])) (by omega))
              (by omega))
            (Expr.eval_eq_of_eq
              (Expr.eval_sub (Expr.eval_reg_of_eq (v := lu) (by simp))
                (Expr.eval_const hw2) hlu_lt)
              (by omega)) ?_
          refine runs_seq_store_le (x := outGraphAddr + 3 + 2 * (pref i).length) (v := verts.idxOf e.2)
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (v := outGraphAddr) (by simp [hr.r_outG]))
                (Expr.eval_const (by omega)) (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := (pref i).length) (by simp [houtM])) (by omega))
              (by omega))
            (Expr.eval_eq_of_eq
              (Expr.eval_sub (Expr.eval_reg_of_eq (v := lv) (by simp))
                (Expr.eval_const hw2) hlv_lt)
              (by omega)) ?_
          refine runs_assign_le (v := (pref i).length + 1)
            (Expr.eval_add (Expr.eval_reg_of_eq (v := (pref i).length) (by simp [houtM]))
              (Expr.eval_const hw2) (by omega)) ?_ (by simp [Expr.size])
          refine ⟨⟨indRegs_update_ge (r := indI) (by decide)
              (indRegs_update_ge (r := indOutM) (by decide)
                (indRegs_update_mem (indRegs_update_mem
                  (indRegs_update_ge (r := indLV) (by decide)
                    (indRegs_update_ge (r := indLU) (by decide)
                      (indRegs_update_ge (r := indV) (by decide)
                        (indRegs_update_ge (r := indU) (by decide) hr))))))),
            by simp, by rw [hpref_succ]; simp, hpos,
            memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
              (memFrame_update (by omega) (by omega))), ?_⟩, by simp [hi]⟩
          rw [hpref_succ]
          intro j hj
          dsimp only
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hjl : j < (pref i).length
          · rw [List.getElem_append_left hjl,
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hedg j hjl
          · have hjeq : j = (pref i).length := by omega
            subst hjeq
            simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
            refine ⟨?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_self]
            · rw [show outGraphAddr + 2 + 2 * (pref i).length + 1 = outGraphAddr + 3 + 2 * (pref i).length by omega,
                Function.update_self]
        · have he2X : e.2 ∉ X := by
            intro hm
            have hpos_lv : 0 < lv := by simp [lv, List.mem_toFinset.mp hm]
            simp [hpos_lv] at hlv_0
          have hpref_succ : pref (i + 1) = pref i := by
            dsimp only [pref, relabelEdges]
            rw [List.take_succ_eq_append_getElem hiE, List.filter_append, List.filter_cons,
              List.filter_nil]
            simp [e, he2X]
          refine runs_nop_le ?_ (by simp [Expr.size])
          refine ⟨⟨indRegs_update_ge (r := indI) (by decide)
              (indRegs_update_ge (r := indLV) (by decide)
                (indRegs_update_ge (r := indLU) (by decide)
                  (indRegs_update_ge (r := indV) (by decide)
                    (indRegs_update_ge (r := indU) (by decide) hr)))),
            by simp, by rw [hpref_succ]; simp [houtM], hpos, hfr,
            by rw [hpref_succ]; exact hedg⟩, by simp [hi]⟩
      · have he1X : e.1 ∉ X := by
          intro hm
          have hpos_lu : 0 < lu := by simp [lu, List.mem_toFinset.mp hm]
          simp [hpos_lu] at hlu_0
        have hpref_succ : pref (i + 1) = pref i := by
          dsimp only [pref, relabelEdges]
          rw [List.take_succ_eq_append_getElem hiE, List.filter_append, List.filter_cons,
            List.filter_nil]
          simp [e, he1X]
        refine runs_nop_le ?_ (by simp [Expr.size])
        refine ⟨⟨indRegs_update_ge (r := indI) (by decide)
            (indRegs_update_ge (r := indLV) (by decide)
              (indRegs_update_ge (r := indLU) (by decide)
                (indRegs_update_ge (r := indV) (by decide)
                  (indRegs_update_ge (r := indU) (by decide) hr)))),
          by simp, by rw [hpref_succ]; simp [houtM], hpos, hfr,
          by rw [hpref_succ]; exact hedg⟩, by simp [hi]⟩)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, houtM, hpos, hfr, hedg⟩
    have hpeq : pref mE = esX := by
      simp [pref, esX, Graph.inside, ← hElen]
    rw [hpeq] at houtM hedg
    exact ⟨hr, houtM, hpos, hfr, hedg⟩
  · exact False.elim hq

/-- Stage 3 of `inducedSubgraphProc`: resets `locAddr[verts[i]] := 0`, restoring `locAddr` to `0`. -/
private lemma indClearLoc_triple {w n k mE mX vertsAddr edgesAddr locAddr outGraphAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (st₀ : State)
    (hvlen : verts.length = k)
    (hverts_lt : ∀ u ∈ verts, u < n) (hlist : ListAt mem vertsAddr verts)
    (hdisj : DisjointRange locAddr n vertsAddr k)
    (hw : InducedWordBound w n k mE vertsAddr edgesAddr locAddr outGraphAddr)
    (hregs : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st₀)
    (hmem : st₀.mem = mem) (houtM : st₀.regs indOutM = mX) :
    Triple w p (fun st => st = st₀)
      (forRange indI (.const 0) (.reg indK)
        (seqStmts
          [ .assign indU (.load (.bin .add (.reg indVerts) (.reg indI)))
          , .store (.bin .add (.reg indLoc) (.reg indU)) (.const 0) ]))
      (normalPost fun st' =>
        IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st' ∧
        st'.regs indOutM = mX ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem locAddr (locAddr + n) ∧
        (∀ a, (∀ u ∈ verts, a ≠ locAddr + u) → st'.mem a = mem a) ∧
        (∀ u ∈ verts, st'.mem (locAddr + u) = 0))
      (fun _ => 35 * k + 20) := by
  rcases hw with ⟨hvk_w, _, hloc_w, _, hk1_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st ∧
    st.regs indI = i ∧ st.regs indOutM = mX ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem locAddr (locAddr + n) ∧
    (∀ a, (∀ u ∈ verts, a ≠ locAddr + u) → st.mem a = mem a) ∧
    (∀ j (hj : j < i), ∀ (hjk : j < verts.length), st.mem (locAddr + verts[j]'hjk) = 0)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := indI) (lo := .const 0) (hi := .reg indK)
    (body := seqStmts
      [ .assign indU (.load (.bin .add (.reg indVerts) (.reg indI)))
      , .store (.bin .add (.reg indLoc) (.reg indU)) (.const 0) ])
    (P := fun st => st = st₀) (Inv := Inv) 18 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), indRegs_update_ge (r := indI) (by decide) hregs,
        by simp, by simp [houtM], rfl, hmem ▸ memFrame_refl mem _ _,
        fun a _ => by simp [hmem], fun j hj => by omega⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hmX, hpos, hfr, hpt, hclr⟩
      have hi_lt : i < verts.length := hvlen ▸ hilt
      have hv_lt : verts[i]'hi_lt < n := hverts_lt _ (List.getElem_mem hi_lt)
      have hmem_v : st.mem (vertsAddr + i) = verts[i]'hi_lt := by
        rw [hfr (vertsAddr + i) (disjointRange_outside hdisj (by omega) (by omega))]
        exact hlist i hi_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := verts[i]'hi_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_verts) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_v) ?_
      refine runs_store_le (x := locAddr + verts[i]'hi_lt) (v := 0)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
          (Expr.eval_reg_of_eq (v := verts[i]'hi_lt) (by simp)) (by omega))
        (Expr.eval_const (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨indRegs_update_ge (r := indI) (by decide)
          (indRegs_update_mem (indRegs_update_ge (r := indU) (by decide) hr)),
        by simp, by simp [hmX], hpos,
        memFrame_trans hfr (memFrame_update (by omega) (by omega)),
        fun a ha => by
          dsimp only
          rw [Function.update_of_ne (ha _ (List.getElem_mem hi_lt))]
          exact hpt a ha, ?_⟩, by simp [hi]⟩
      intro j hj hjk
      dsimp only
      by_cases hji : verts[j]'hjk = verts[i]'hi_lt
      · rw [hji]; simp
      · have hne_ji : j ≠ i := fun h => hji (by subst h; rfl)
        rw [Function.update_of_ne (by omega)]
        exact hclr j (by omega) hjk)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hmX, hpos, hfr, hpt, hclr⟩
    refine ⟨hr, hmX, hpos, hfr, hpt, fun u hu => ?_⟩
    rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
    exact hclr j (hvlen ▸ hj) hj
  · exact False.elim hq

/-! ## 2. Main Specification and Non-Vacuity Example -/

/-- `inducedSubgraphProc` meets `inducedSubgraphContract w` in `O(|X| + |E| + 1)` deterministic
steps, without scanning `range n`. -/
theorem inducedSubgraph_spec {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [inducedSubgraphProc]) :
    MeetsContract w p b (inducedSubgraphContract w) := by
  have hEntry : p.procs[b]? = some inducedSubgraphProc := by simpa using hp 0 (by simp)
  intro args mem pos ω _ hpre
  rcases hpre with ⟨n, k, vertsAddr, mE, edgesAddr, locAddr, outGraphAddr, verts, edges,
    hargs, hvlen, hnd, hverts_lt, hElen, hE_lt, hverts_at, hE_at, hloc0, hw, hdisj⟩
  subst hargs
  rcases hdisj with ⟨hd_lv, hd_le, hd_lo, hd_ov, hd_oe⟩
  have hw2 : 1 < 2 ^ w := by rcases hw with ⟨_, _, _, _, _, h16⟩; omega
  have hout_w : outGraphAddr + 2 + 2 * mE < 2 ^ w := hw.2.2.2.1
  set X := verts.toFinset
  set G_X := relabelGraph verts ((Graph.mk 0 edges).inside X)
  have hGX_valid : G_X.IsValid := by
    apply relabelGraph_isValid
    intro e he
    exact (mem_inside_iff.mp he).2
  have hGX_m_le : G_X.m ≤ mE := by
    rw [relabelGraph_m, ← hElen]
    exact inside_length_le_m (Graph.mk 0 edges) X
  have hrun : ∃ o st' c,
      Runs w p ω inducedSubgraphProc
        (startState [k, vertsAddr, mE, edgesAddr, locAddr, outGraphAddr] mem pos) o st' c ∧
      (inducedSubgraphContract w).post [k, vertsAddr, mE, edgesAddr, locAddr, outGraphAddr]
        mem o.value st'.mem ∧
      c ≤ inducedSubgraphCost k mE := by
    refine runs_start_le ?_
    dsimp only [inducedSubgraphProc, seqStmts]
    have hr0 : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr
        (startState [k, vertsAddr, mE, edgesAddr, locAddr, outGraphAddr] mem pos) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine runs_seq_triple_le
      (indFillLoc1_triple p mem verts _ hvlen hnd hverts_lt hverts_at hloc0 hd_lv hw hr0 rfl) rfl ?_
    intro st1 ⟨hr1, hpos1, hfr1, hloc1⟩
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
    let st1' := { st1 with regs := Function.update st1.regs indOutM 0 }
    have hr1' : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st1' :=
      indRegs_update_ge (r := indOutM) (by decide) hr1
    have hE_at1 : EdgesAt st1'.mem edgesAddr edges :=
      hE_at.congr fun a ha1 ha2 => hfr1 a (disjointRange_outside hd_le ha1 (by omega))
    refine runs_seq_triple_le
      (indFilterEdges_triple p st1'.mem verts edges st1' hvlen hElen hE_lt hE_at1 hloc1
        hd_lo.symm hd_oe hw hr1' rfl (by simp [st1'])) rfl ?_
    intro st2 ⟨hr2, hmX2, hpos2, hfr2, hedg2⟩
    refine runs_seq_store_le (x := outGraphAddr) (v := k)
      (Expr.eval_reg_of_eq hr2.r_outG) (Expr.eval_reg_of_eq hr2.r_k) ?_
    refine runs_seq_store_le (x := outGraphAddr + 1) (v := G_X.m)
      (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_outG) (Expr.eval_const hw2) (by omega))
      (Expr.eval_reg_of_eq hmX2) ?_
    let st3 := { st2 with mem := Function.update (Function.update st2.mem outGraphAddr k) (outGraphAddr + 1) G_X.m }
    have hr3 : IndRegs k vertsAddr mE edgesAddr locAddr outGraphAddr st3 := indRegs_update_mem hr2
    have hfr23 : MemFrame st1.mem st3.mem outGraphAddr (outGraphAddr + 2 + 2 * mE) :=
      memFrame_trans hfr2 (memFrame_trans (memFrame_update (by omega) (by omega))
        (memFrame_update (by omega) (by omega)))
    have hverts_at3 : ListAt st3.mem vertsAddr verts :=
      hverts_at.congr fun a ha1 ha2 => by
        have hout_o := disjointRange_outside hd_ov (x := a) ha1 (by omega)
        have hout_l := disjointRange_outside hd_lv (x := a) ha1 (by omega)
        rw [hfr23 a (by rcases hout_o with h | h <;> [left; right] <;> omega), hfr1 a hout_l]
    refine runs_seq_triple_le
      (indClearLoc_triple (mX := G_X.m) p st3.mem verts st3 hvlen hverts_lt hverts_at3 hd_lv hw
        hr3 rfl hmX2) rfl ?_
    intro st4 ⟨hr4, hmX4, hpos4, hfr4, hpt4, hclr4⟩
    refine runs_ret_le (Expr.eval_reg_of_eq hmX4) ?_ ?_
    · have hread_verts : readList mem vertsAddr k = verts := hvlen ▸ readList_eq_of_listAt hverts_at
      have hread_edges : readEdges mem edgesAddr mE = edges := hElen ▸ readEdges_eq_of_edgesAt hE_at
      dsimp only [inducedSubgraphContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hread_verts, hread_edges]
      refine ⟨rfl, hGX_m_le, hvlen, hGX_valid, ?_, ?_⟩
      · refine graphAt_of_cells ?_ ?_ ?_
        · have hout := disjointRange_outside hd_lo (x := outGraphAddr) (by omega) (by omega)
          rw [hfr4 outGraphAddr hout]
          simp [st3, G_X, relabelGraph, hvlen]
        · have hout := disjointRange_outside hd_lo (x := outGraphAddr + 1) (by omega) (by omega)
          rw [hfr4 (outGraphAddr + 1) hout]
          simp [st3, G_X, X]
        · intro j hj
          have hj_mE : j < mE := lt_of_lt_of_le hj hGX_m_le
          have hout1 := disjointRange_outside hd_lo (x := outGraphAddr + 2 + 2 * j) (by omega) (by omega)
          have hout2 := disjointRange_outside hd_lo (x := outGraphAddr + 3 + 2 * j) (by omega) (by omega)
          rw [hfr4 (outGraphAddr + 2 + 2 * j) hout1, hfr4 (outGraphAddr + 3 + 2 * j) hout2]
          simp only [st3]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          have hp := hedg2 j hj
          refine ⟨hp.1, ?_⟩
          rw [show outGraphAddr + 3 + 2 * j = outGraphAddr + 2 + 2 * j + 1 by omega]
          exact hp.2
      · intro a ha
        by_cases hal : a < locAddr ∨ locAddr + n ≤ a
        · rw [hfr4 a hal, hfr23 a ha, hfr1 a hal]
        · have hu_lt : a - locAddr < n := by omega
          have ha_eq : locAddr + (a - locAddr) = a := by omega
          by_cases hu_mem : (a - locAddr) ∈ verts
          · rw [← ha_eq, hclr4 (a - locAddr) hu_mem, hloc0 (a - locAddr) hu_lt]
          · have hnot : ∀ u ∈ verts, a ≠ locAddr + u := fun u hu heq =>
              hu_mem ((by omega : a - locAddr = u) ▸ hu)
            rw [hpt4 a hnot, hfr23 a ha, ← ha_eq, hloc1 (a - locAddr) hu_lt,
              ite_eq_right_iff.mpr (fun h => absurd h hu_mem), hloc0 (a - locAddr) hu_lt]
    · dsimp only [inducedSubgraphCost, Expr.size]
      omega
  rcases hrun with ⟨o, st', c, hr, hpost, hcost⟩
  exact ⟨inducedSubgraphProc, hEntry, o, st', c, hr, hpost, by simpa [inducedSubgraphContract] using hcost⟩

/-- Non-vacuity witness for `inducedSubgraphContract 16`. -/
theorem inducedSubgraphContract_pre_example :
    ∃ args mem, (∀ a ∈ args, a < 2 ^ 16) ∧ (inducedSubgraphContract 16).pre args mem := by
  let verts : List ℕ := [1, 2]
  let edges : List (ℕ × ℕ) := [(0, 1), (1, 2)]
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 1 else if a = 1 then 2
    else if a = 10 then 0 else if a = 11 then 1
    else if a = 12 then 1 else if a = 13 then 2
    else 0
  let args : List ℕ := [2, 0, 2, 10, 20, 30]
  refine ⟨args, mem, by decide, ?_⟩
  refine ⟨3, 2, 0, 2, 10, 20, 30, verts, edges, rfl, rfl, by decide, by decide, rfl, by decide,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rcases i with _ | _ | i <;> simp [verts, mem] at hi ⊢
  · intro j hj; rcases j with _ | _ | j <;> simp [edges, mem] at hj ⊢
  · intro u hu; simp only [mem]; split_ifs <;> omega
  · unfold InducedWordBound; decide
  · unfold InducedDisjoint DisjointRange; decide

end MinCostFlow.ExpanderDecomp
