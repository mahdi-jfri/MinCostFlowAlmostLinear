module

public import MinCostFlow.Expander.DecomposePhiProg
public import MinCostFlow.Expander.DecomposeCompress
public import MinCostFlow.Expander.DecomposeGroupEdgesSpec
public import MinCostFlow.Expander.DecomposeMath

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Partition Pruning Base: Memory Layout, Program, and Pure Bridges

Defines the scratch layout (`partWorkSize`), `pruneWrapProc` (wrapping `pruneExpanderStmt`),
`partPruneProc` (per-partition compressed graph construction, bad-twin filtering, CSR + pruning,
and component emission), and the pure combinatorial bridges connecting `groupVertsContract` /
`groupEdgesContract` to `compressPartGraph`, `degX`, `PruneMemDisjoint`, `PruneWordBound`, and
component size bounds.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Layout, Cost, and Program Definitions -/

abbrev partGXAddr (workAddr _n_p _m_p : ℕ) : ℕ := workAddr
abbrev partDegXAddr (workAddr _n_p m_p : ℕ) : ℕ := workAddr + 2 + 2 * m_p
abbrev partInBAddr (workAddr n_p m_p : ℕ) : ℕ := workAddr + 2 + 2 * m_p + n_p
abbrev partOutRAddr (workAddr n_p m_p : ℕ) : ℕ := workAddr + 2 + 2 * m_p + 2 * n_p
abbrev partCsrAddr (workAddr n_p m_p : ℕ) : ℕ := workAddr + 2 + 2 * m_p + 3 * n_p
abbrev partPruneWorkAddr (workAddr n_p m_p : ℕ) : ℕ := workAddr + 5 * n_p + 6 * m_p + 3

def partWorkSize (n_p m_p H : ℕ) : ℕ :=
  5 * n_p + 6 * m_p + 3 + pruneWorkSpace n_p m_p H

def partPruneCost (n_p m_p D_phi : ℕ) : ℕ :=
  let H := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m_p + 1) + 1) + 2
  pruneTimeBound n_p m_p H + 450 * (n_p + m_p + 1) + 13 * (Nat.log 2 (2 * m_p + 1) + 1) + 200

/-- Wrapper procedure exposing `pruneExpanderStmt` behind a standard Word-RAM `.call`. -/
def pruneWrapProc : Stmt := .seq pruneExpanderStmt (.ret (.const 0))

lemma pruneWrapProc_noRand : pruneWrapProc.NoRand :=
  ⟨pruneExpanderStmt_noRand, by simp [Stmt.NoRand]⟩

def partPtrSetupStmt : Stmt :=
  seqStmts
    [ .assign 12 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 5) (.reg 9))) (.reg 2)))
    , .assign 12 (.bin .add (.bin .add (.bin .add (.reg 1)
        (.bin .mul (.const 7) (.reg 9))) (.const 1)) (.reg 12))
    , .assign 13 (.load (.bin .add (.bin .add (.bin .add (.reg 1)
        (.bin .mul (.const 9) (.reg 9))) (.const 1)) (.reg 2)))
    , .assign 14 (.load (.bin .add (.bin .add (.bin .add (.reg 1)
        (.bin .mul (.const 10) (.reg 9))) (.const 1)) (.reg 2)))
    , .assign 14 (.bin .add (.bin .add (.bin .add (.reg 1)
        (.bin .mul (.const 12) (.reg 9))) (.const 2)) (.bin .mul (.const 2) (.reg 14)))
    , .assign 15 (.reg 6)
    , .assign 16 (.bin .add (.reg 15) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 13))))
    , .assign 17 (.bin .add (.reg 16) (.reg 11))
    , .assign 18 (.bin .add (.reg 17) (.reg 11))
    , .assign 19 (.bin .add (.reg 18) (.reg 11))
    , .assign 20 (.bin .add (.reg 19)
        (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 11)) (.const 1))
          (.bin .mul (.const 4) (.reg 13)))) ]

def partBuildGXStmt : Stmt :=
  seqStmts
    [ .store (.reg 15) (.reg 11)
    , .store (.bin .add (.reg 15) (.const 1)) (.reg 13)
    , forRange 24 (.const 0) (.reg 13)
        (seqStmts
          [ .assign 25 (.load (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 24))))
          , .assign 26 (.load (.bin .add (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 24)) (.const 1))))
          , .store (.bin .add (.reg 15) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 24)))) (.reg 25)
          , .store (.bin .add (.reg 15) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 24)))) (.reg 26) ]) ]

def partDegXStmt : Stmt :=
  seqStmts
    [ forRange 24 (.const 0) (.reg 11)
        (.store (.bin .add (.reg 16) (.reg 24)) (.const 0))
    , forRange 24 (.const 0) (.reg 13)
        (seqStmts
          [ .assign 25 (.load (.bin .add (.reg 15) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 24)))))
          , .assign 26 (.load (.bin .add (.reg 15) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 24)))))
          , .assign 27 (.load (.bin .add (.reg 16) (.reg 25)))
          , .store (.bin .add (.reg 16) (.reg 25)) (.bin .add (.reg 27) (.const 1))
          , .assign 27 (.load (.bin .add (.reg 16) (.reg 26)))
          , .store (.bin .add (.reg 16) (.reg 26)) (.bin .add (.reg 27) (.const 1)) ]) ]

def partInBStmt : Stmt :=
  seqStmts
    [ .assign 21 (.const 0)
    , forRange 24 (.const 0) (.reg 11)
        (seqStmts
          [ .assign 25 (.load (.bin .add (.reg 16) (.reg 24)))
          , .cond (.bin .lt (.bin .mul (.reg 25) (.reg 5)) (.reg 4))
              (seqStmts
                [ .assign 26 (.load (.bin .add (.reg 12) (.reg 24)))
                , .assign 27 (.load (.bin .add (.reg 1) (.reg 26)))
                , .cond (.bin .lt (.const 0) (.reg 27))
                    (.assign 21 (.const 1))
                    .nop
                , .store (.bin .add (.reg 17) (.reg 24)) (.const 1) ])
              (.store (.bin .add (.reg 17) (.reg 24)) (.const 0)) ])
    , .cond (.bin .lt (.const 0) (.reg 21)) (.ret (.reg 8)) .nop ]

def partPruneCallStmt (b_csr b_prune : ℕ) : Stmt :=
  seqStmts
    [ .assign 22 (.bin .add (.bin .mul (.const 4) (.reg 5)) (.const 2))
    , .assign 24 (.bin .add (.bin .mul (.const 2) (.reg 13)) (.const 1))
    , .assign 23 (.const 0)
    , .loop (.bin .lt (.const 1) (.reg 24))
        (seqStmts
          [ .assign 24 (.bin .div (.reg 24) (.const 2))
          , .assign 23 (.bin .add (.reg 23) (.const 1)) ])
    , .assign 25 (.bin .add (.bin .mul (.bin .mul (.const 4) (.reg 22)) (.bin .add (.reg 23) (.const 1))) (.const 2))
    , .assign 26 (.bin .div (.bin .sub (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 5))) (.const 1))
        (.bin .mul (.const 3) (.reg 5)))
    , .call 27 b_csr [.reg 15, .reg 19]
    , .call 27 b_prune [.reg 15, .reg 19, .reg 17, .reg 18, .reg 20, .reg 22, .reg 25, .reg 26] ]

def partEmitRStmt : Stmt :=
  seqStmts
    [ .assign 21 (.const 0)
    , forRange 24 (.const 0) (.reg 11)
        (seqStmts
          [ .assign 25 (.load (.bin .add (.reg 18) (.reg 24)))
          , .cond (.bin .lt (.const 0) (.reg 25))
              (.assign 21 (.bin .add (.reg 21) (.const 1)))
              .nop ])
    , .cond (.bin .lt (.reg 21) (.const 2)) (.ret (.reg 8)) .nop
    , .store (.reg 8) (.reg 3)
    , .store (.bin .add (.reg 8) (.const 1)) (.reg 21)
    , .assign 22 (.bin .add (.reg 8) (.const 2))
    , forRange 24 (.const 0) (.reg 11)
        (seqStmts
          [ .assign 25 (.load (.bin .add (.reg 18) (.reg 24)))
          , .cond (.bin .lt (.const 0) (.reg 25))
              (seqStmts
                [ .assign 26 (.load (.bin .add (.reg 12) (.reg 24)))
                , .store (.bin .add (.reg 7) (.reg 26)) (.const 1)
                , .store (.reg 22) (.reg 26)
                , .assign 22 (.bin .add (.reg 22) (.const 1)) ])
              .nop ])
    , .ret (.reg 22) ]

/-- `partPruneProc`: args `[curGAddr, bufAddr, q, lvl, D, D_phi, workAddr, keptVertAddr, arenaPtr]`.
Processes partition `q`, updating `keptVertAddr` and emitting `[lvl, |R|] ++ R` at `arenaPtr`
if `2 ≤ |R|`, returning the updated arena pointer. -/
def partPruneProc (b_csr b_prune : ℕ) : Stmt :=
  seqStmts
    [ .assign 9 (.load (.reg 0))
    , .assign 10 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 11 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 4) (.reg 9))) (.reg 2)))
    , .cond (.bin .lt (.reg 11) (.const 2)) (.ret (.reg 8)) .nop
    , partPtrSetupStmt
    , partBuildGXStmt
    , partDegXStmt
    , partInBStmt
    , partPruneCallStmt b_csr b_prune
    , partEmitRStmt ]

lemma partPruneProc_noRand (b_csr b_prune : ℕ) : (partPruneProc b_csr b_prune).NoRand := by
  simp [partPruneProc, partPtrSetupStmt, partBuildGXStmt, partDegXStmt, partInBStmt,
    partPruneCallStmt, partEmitRStmt, forRange, WordRAM.forUp, seqStmts, Stmt.NoRand]

/-! ## 2. Wrapper Spec for `pruneWrapProc` -/

theorem pruneWrap_runs {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} {φ₀ : ℝ}
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hexp : cfg.G.IsConductanceExpanderOn cfg.X φ₀) (hφ₀ : 0 < φ₀)
    (hC5 : 5 ≤ cfg.C_cap) (hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1))
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hinB_w : inBAddr + cfg.G.n < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hG : GraphAt mem gAddr cfg.G)
    (hCsr : HasCsrAt mem csrAddr cfg.G)
    (hinB : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ mem (inBAddr + b) ≠ 0) :
    let args := [gAddr, csrAddr, inBAddr, outRAddr, workAddr, cfg.C_cap, cfg.H, cfg.θ_out_nat]
    ∃ st' c,
      Runs w p ω pruneWrapProc (startState args mem pos) (.returned 0) st' c ∧
      st'.pos = pos ∧
      PreservedOutside2 mem st'.mem outRAddr (outRAddr + cfg.G.n)
        workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
      c ≤ pruneTimeBound cfg.G.n cfg.G.m cfg.H + 3 ∧
      have R := (Finset.range cfg.G.n).filter fun x => decide (st'.mem (outRAddr + x) ≠ 0)
      R ⊆ cfg.X \ cfg.B ∧
      cfg.G.IsConductanceExpanderOn R (φ₀ / 3) ∧
      (∀ v ∈ R, cfg.θ_out_nat ≤ cfg.G.degIn R v) ∧
      cfg.G.volIn cfg.X (cfg.X \ R) ≤
        cfg.G.volIn cfg.X cfg.B + 2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B := by
  intro args
  let st₀ := startState args mem pos
  have hreg0 : InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hmem0 : st₀.mem = mem := rfl
  obtain ⟨st', c, hr, hpos', hpr, hc, hRsub, hexpR, hdegR, _, hvol⟩ :=
    pruneExpander_wordram_spec (p := p) st₀ ω hreg0 hcfgX hval hexp hφ₀ hC5 hCphi hθ hw hdisj
      hg_w hcsr_w hinB_w houtR_w hG hCsr hinB
  have hret : Runs w p ω (.ret (.const 0)) st' (.returned 0) st' 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have hseq : Runs w p ω pruneWrapProc st₀ (.returned 0) st' (c + 2 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st', c, 2, hr, hret, rfl⟩)
  exact ⟨st', c + 2 + 1, hseq, hpos', hpr, by omega, hRsub, hexpR, hdegR, hvol⟩

/-! ## 3. Pure Combinatorial Bridges -/

lemma compressPartGraph_eq_of_groupEdges {curG : Cited.Graph} (hV : curG.IsValid)
    {mem : ℕ → ℕ} {curGAddr bufAddr q cnt off ecnt eoff : ℕ}
    (hga : GraphAt mem curGAddr curG)
    (hverts_eq : ∀ u, (u ∈ tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)) ↔
      u < curG.n ∧ mem (grpPartId bufAddr curG.n + u) = q)
    (hstrict : (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)).Pairwise (· < ·))
    (hlid_inv : ∀ u < curG.n, mem (grpPartId bufAddr curG.n + u) = q →
      mem (grpLocalId bufAddr curG.n + u) < cnt ∧
      mem (grpPartVerts bufAddr curG.n + off + mem (grpLocalId bufAddr curG.n + u)) = u)
    (hes :
      let partFn := fun u => mem (grpPartId bufAddr curG.n + u)
      let localFn := fun u => mem (grpLocalId bufAddr curG.n + u)
      let es := ((List.range curG.m).filter fun j =>
        let u := mem (curGAddr + 2 + 2 * j)
        let v := mem (curGAddr + 3 + 2 * j)
        decide (partFn u = q ∧ partFn v = q)).map fun j =>
        (localFn (mem (curGAddr + 2 + 2 * j)), localFn (mem (curGAddr + 3 + 2 * j)))
      ecnt = es.length ∧
      ∀ t (ht : t < es.length),
        mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t)) = es[t].1 ∧
        mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t) + 1) = es[t].2) :
    let actVerts := tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)
    let X := actVerts.toFinset
    let G_X := compressPartGraph actVerts (curG.inside X)
    G_X.n = cnt ∧
    G_X.m = ecnt ∧
    ∀ t (ht : t < G_X.edges.length),
      mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t)) = (G_X.edges[t]'ht).1 ∧
      mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t) + 1) = (G_X.edges[t]'ht).2 := by
  intro actVerts X G_X
  have hlen : actVerts.length = cnt := by simp [actVerts, tab]
  have hnodup : actVerts.Nodup := hstrict.imp fun h => ne_of_lt h
  have hact_mem : ∀ u, u ∈ actVerts ↔ u < curG.n ∧ mem (grpPartId bufAddr curG.n + u) = q :=
    fun u => by simpa [actVerts] using hverts_eq u
  have hbound : ∀ u ∈ actVerts, u < curG.n := fun u hu => ((hact_mem u).mp hu).1
  have hact := actVertsSpec_inside hstrict hbound
  have hid_eq : ∀ u < curG.n, mem (grpPartId bufAddr curG.n + u) = q →
      mem (grpLocalId bufAddr curG.n + u) = actVerts.idxOf u := by
    intro u hu hpu
    have hlid := hlid_inv u hu hpu
    have hlt : mem (grpLocalId bufAddr curG.n + u) < actVerts.length := by
      simp [actVerts, tab, hlid.1]
    have hget : actVerts.getD (mem (grpLocalId bufAddr curG.n + u)) 0 = u := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      simpa [actVerts, tab] using hlid.2
    have hres := (hact.idxOf_getD hlt).symm
    rw [hget] at hres
    exact hres
  let es := ((List.range curG.m).filter fun j =>
    let u := mem (curGAddr + 2 + 2 * j)
    let v := mem (curGAddr + 3 + 2 * j)
    decide (mem (grpPartId bufAddr curG.n + u) = q ∧
      mem (grpPartId bufAddr curG.n + v) = q)).map fun j =>
    (mem (grpLocalId bufAddr curG.n + mem (curGAddr + 2 + 2 * j)),
     mem (grpLocalId bufAddr curG.n + mem (curGAddr + 3 + 2 * j)))
  have edges_idx_eq : curG.edges = (List.range curG.m).map fun j => curG.edges.getD j (0, 0) := by
    refine List.ext_getElem (by simp [Cited.Graph.m]) fun j hj1 hj2 => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [Cited.Graph.m] using hj1)]
  have hj_map : (List.range curG.m).filter (fun j =>
      let u := mem (curGAddr + 2 + 2 * j)
      let v := mem (curGAddr + 3 + 2 * j)
      decide (mem (grpPartId bufAddr curG.n + u) = q ∧
        mem (grpPartId bufAddr curG.n + v) = q)) =
      ((List.range curG.m).filter fun j =>
        let e := curG.edges.getD j (0, 0)
        decide (e.1 ∈ X ∧ e.2 ∈ X)) := by
    refine List.filter_congr fun j hj => ?_
    have hjlt : j < curG.m := List.mem_range.mp hj
    have hev := hV _ (List.getElem_mem hjlt)
    have hf := graphAt_edge_fst hga hjlt
    have hs := graphAt_edge_snd hga hjlt
    have hed : curG.edges.getD j (0, 0) = (curG.edges[j]'hjlt) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
    rw [hf, hs, hed]
    have h1 : (curG.edges[j]'hjlt).1 ∈ X ↔ mem (grpPartId bufAddr curG.n + (curG.edges[j]'hjlt).1) = q := by
      rw [List.mem_toFinset, hact_mem]
      exact ⟨fun h => h.2, fun h => ⟨hev.1, h⟩⟩
    have h2 : (curG.edges[j]'hjlt).2 ∈ X ↔ mem (grpPartId bufAddr curG.n + (curG.edges[j]'hjlt).2) = q := by
      rw [List.mem_toFinset, hact_mem]
      exact ⟨fun h => h.2, fun h => ⟨hev.2, h⟩⟩
    simp [h1, h2]
  have hes_eq : es = G_X.edges := by
    change es = (curG.inside X).map fun e => (actVerts.idxOf e.1, actVerts.idxOf e.2)
    have hins : curG.inside X = ((List.range curG.m).filter fun j =>
        let e := curG.edges.getD j (0, 0)
        decide (e.1 ∈ X ∧ e.2 ∈ X)).map fun j => curG.edges.getD j (0, 0) := by
      unfold Cited.Graph.inside
      conv_lhs => rw [edges_idx_eq, List.filter_map]
      rfl
    rw [hins, List.map_map]
    dsimp only [es]
    rw [hj_map]
    refine List.map_congr_left fun j hj => ?_
    have hj_fil := List.mem_filter.mp hj
    have hjlt : j < curG.m := List.mem_range.mp hj_fil.1
    have hf := graphAt_edge_fst hga hjlt
    have hs := graphAt_edge_snd hga hjlt
    have hed : curG.edges.getD j (0, 0) = curG.edges[j]'hjlt := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
    have hdec := decide_eq_true_eq.mp hj_fil.2
    rw [hed] at hdec
    have h1m := (hact_mem _).mp (List.mem_toFinset.mp hdec.1)
    have h2m := (hact_mem _).mp (List.mem_toFinset.mp hdec.2)
    simp only [Function.comp_apply, hed]
    rw [hf, hs, hid_eq _ h1m.1 h1m.2, hid_eq _ h2m.1 h2m.2]
  rcases hes with ⟨hec_eq, hed_mem⟩
  change ecnt = es.length at hec_eq
  change ∀ t (ht : t < es.length),
    mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t)) = es[t].1 ∧
    mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t) + 1) = es[t].2 at hed_mem
  refine ⟨hlen, by rw [hec_eq, hes_eq]; rfl, fun t ht => ?_⟩
  have htec : t < es.length := by rw [hes_eq]; exact ht
  have hmem := hed_mem t htec
  simpa [hes_eq] using hmem

lemma degXPrefix_succ_of_edge {G : Cited.Graph} {j : ℕ} (hj : j < G.edges.length) (w : ℕ) :
    degXPrefix G (j + 1) w =
      degXPrefix G j w + (if G.edges[j].1 = w then 1 else 0) +
        (if G.edges[j].2 = w then 1 else 0) := by
  have htake : G.edges.take (j + 1) = G.edges.take j ++ [G.edges[j]] :=
    List.take_succ_eq_append_getElem hj
  simp only [degXPrefix, htake, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  by_cases h1 : G.edges[j].1 = w <;> by_cases h2 : G.edges[j].2 = w <;> simp [h1, h2] <;> omega

lemma volIn_self_eq_two_mul_inside (G : Cited.Graph) (R : Finset ℕ) :
    G.volIn R R = 2 * (G.inside R).length := by
  have hsum : ∀ (L : List (ℕ × ℕ)) (f : ℕ × ℕ → ℕ),
      (∀ e ∈ L, f e ∈ R) →
      ∑ u ∈ R, (L.filter fun e => decide (f e = u)).length = L.length := by
    intro L f hf
    induction L with
    | nil => simp
    | cons e rest ih =>
      have hrest : ∀ e' ∈ rest, f e' ∈ R := fun e' he' => hf e' (by simp [he'])
      have hfe : f e ∈ R := hf e (by simp)
      have hstep : ∀ u ∈ R,
          ((e :: rest).filter fun x => decide (f x = u)).length =
            (if u = f e then 1 else 0) + (rest.filter fun x => decide (f x = u)).length := by
        intro u _
        simp only [List.filter_cons]
        by_cases h : f e = u
        · simp [h, Nat.add_comm]
        · have hne : u ≠ f e := fun h' => h h'.symm
          simp [h, hne]
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [hfe, ih hrest, Nat.add_comm]
  have hmem1 : ∀ e ∈ G.inside R, e.1 ∈ R := fun e he => by
    simp only [Cited.Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.2.1
  have hmem2 : ∀ e ∈ G.inside R, e.2 ∈ R := fun e he => by
    simp only [Cited.Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.2.2
  unfold Cited.Graph.volIn Cited.Graph.degIn
  rw [Finset.sum_add_distrib, hsum (G.inside R) Prod.fst hmem1, hsum (G.inside R) Prod.snd hmem2]
  omega

lemma card_two_add_le_four_mul_m {G : Cited.Graph} {R : Finset ℕ}
    (hcard : 2 ≤ R.card) (hdeg : ∀ v ∈ R, 1 ≤ G.degIn R v) :
    2 + R.card ≤ 4 * G.m := by
  have hcard_le_vol : R.card ≤ G.volIn R R := by
    calc R.card = ∑ _v ∈ R, 1 := by simp
      _ ≤ ∑ v ∈ R, G.degIn R v := Finset.sum_le_sum hdeg
      _ = G.volIn R R := rfl
  have hvol : G.volIn R R = 2 * (G.inside R).length := volIn_self_eq_two_mul_inside G R
  have hins : (G.inside R).length ≤ G.m := List.length_filter_le _ _
  omega

lemma partPrune_memDisjoint (workAddr n_p m_p H : ℕ) :
    PruneMemDisjoint (partGXAddr workAddr n_p m_p) (partCsrAddr workAddr n_p m_p)
      (partInBAddr workAddr n_p m_p) (partOutRAddr workAddr n_p m_p)
      (partPruneWorkAddr workAddr n_p m_p) n_p m_p H (2 + 2 * m_p) := by
  dsimp only [PruneMemDisjoint, partGXAddr, partInBAddr, partOutRAddr, partCsrAddr,
    partPruneWorkAddr, pruneWorkSpace]
  refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, Or.inr ?_, Or.inr ?_, Or.inr ?_, Or.inl ?_⟩ <;> omega

lemma partPrune_wordBound {w workAddr n_p m_p C_cap H D_phi : ℕ}
    (hH_le : H = 4 * C_cap * (Nat.log 2 (2 * m_p + 1) + 1) + 2)
    (hC_le : C_cap = 4 * D_phi + 2)
    (hw : workAddr + partWorkSize n_p m_p H + 2 < 2 ^ w)
    (harith : 8 * C_cap * m_p + 4 * C_cap + 2 * n_p + 2 * m_p + H + 16 < 2 ^ w) :
    PruneWordBound w n_p m_p C_cap H (partPruneWorkAddr workAddr n_p m_p) := by
  have _ := hH_le
  have _ := hC_le
  unfold PruneWordBound partPruneWorkAddr partWorkSize pruneWorkSpace at *
  omega

private lemma pruneTimeBound_mono {n₁ m₁ H₁ n₂ m₂ H₂ : ℕ}
    (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) (hH : H₁ ≤ H₂) :
    pruneTimeBound n₁ m₁ H₁ ≤ pruneTimeBound n₂ m₂ H₂ := by
  unfold pruneTimeBound
  have hp12 : (4 * H₁ + 14) * (4 * H₁ + 4) ≤ (4 * H₂ + 14) * (4 * H₂ + 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hp3 : (4 * H₁ + 14) * (4 * H₁ + 4) * (2 * m₁ + 1) ≤
      (4 * H₂ + 14) * (4 * H₂ + 4) * (2 * m₂ + 1) :=
    Nat.mul_le_mul hp12 (by omega)
  have hmul : 360 * ((4 * H₁ + 14) * (4 * H₁ + 4) * (2 * m₁ + 1)) ≤
      360 * ((4 * H₂ + 14) * (4 * H₂ + 4) * (2 * m₂ + 1)) :=
    Nat.mul_le_mul_left 360 hp3
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left 170 hn) (Nat.mul_le_mul_left 140 hm))
    (Nat.mul_le_mul_left 30 (Nat.add_le_add_right hH 1))) hmul) (le_refl 221)

lemma partPruneCost_mono {n₁ m₁ n₂ m₂ D_phi : ℕ} (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) :
    partPruneCost n₁ m₁ D_phi ≤ partPruneCost n₂ m₂ D_phi := by
  have hlg : Nat.log 2 (2 * m₁ + 1) ≤ Nat.log 2 (2 * m₂ + 1) :=
    Nat.log_mono_right (by omega)
  have hH_le : 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m₁ + 1) + 1) + 2 ≤
      4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m₂ + 1) + 1) + 2 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlg 1)) 2
  have ht_le := pruneTimeBound_mono hn hm hH_le
  unfold partPruneCost
  dsimp only
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht_le
    (Nat.mul_le_mul_left 450 (by omega))) (Nat.mul_le_mul_left 13 (by omega))) (le_refl 200)

end MinCostFlow.Expander
