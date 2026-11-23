module

public import WordRAM.Contract
public import WordRAM.Logic
public import MinCostFlow.Expander.PruningProg
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBuildJ
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeStages

import MinCostFlow.Spanner.PathDSContract
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `RemoveFake` Word-RAM Program and Contract

Assembles the deterministic Word-RAM implementation of `RemoveFake` (`removeFakeEntry`,
`removeFakeProcs`) using `buildCsrProc` (`CsrBfsProg.lean`) and `pruneExpanderStmt`
(`PruningProg.lean`):
1. Relabels `X` (`verts[0..k-1]`) to `0 .. k - 1` via a local-ID map in `O(k)` time (never
   scanning `range n`).
2. Builds `J_loc = subdivGraph k H_loc F_loc`, its midpoint indicator `B = Ico k (k + mF)`, and
   its CSR in `O(k + mH + mF + 1)` time.
3. Computes `C_cap = rfCcap rhoNum rhoDen` and `H_param = rfHParam mH mF rhoNum rhoDen` from
   `[rhoNum, rhoDen]` stored at `rhoAddr`, and calls `pruneExpanderStmt` with `φ₀ = ρ / 3` and
   `θ = 1`.
4. Maps the kept local vertices back to original vertex names at `outRAddr` and returns `|R|`.

Proves:
- `removeFake_spec_prog`: `MeetsContract w p b (removeFakeContract w)`, delivering the full
  conclusion of `removeFake_of_pruned` read from memory: `R ⊆ X`, `(ρ / 9)`-conductance on `R`,
  minimum degree `≥ 1` in `H[R]`, and removed `K`-volume `≤ 4 * C_cap * |F| ≤ 60 * |F| / ρ`.
- `removeFakeCost_le_asymptotic`: explicit `O(|X| + |F| + (|H| + |F| + 1) · log²(|H| + |F| + 2) / ρ²)`
  bound on `removeFakeCost`.
- `removeFakeContract_pre_example`: non-vacuity witness showing all precondition hypotheses hold
  simultaneously on a concrete graph.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Procedures, `NoRand`, and Cost -/

/-- Wrapper procedure exposing `pruneExpanderStmt` behind a `.call`. -/
def rfPruneWrap : Stmt :=
  .seq pruneExpanderStmt (.ret (.const 0))

/-- Entry procedure `b` of `RemoveFake`, calling `buildCsrProc` at `b + 1` and `rfPruneWrap` at
`b + 2`. Args: `[k, vertsAddr, mH, hAddr, mF, fAddr, rhoAddr, locAddr, outRAddr, workAddr]`. -/
def removeFakeEntry (b : ℕ) : Stmt :=
  seqStmts
    [ rfSetupStmt
    , rfFillLocStmt
    , rfBuildJStmt
    , rfClearLocStmt
    , rfBuildInBStmt
    , rfComputeHStmt
    , .call rfTmp1 (b + 1) [.reg rfJGraph, .reg rfCsr]
    , .call rfTmp1 (b + 2)
        [.reg rfJGraph, .reg rfCsr, .reg rfInB, .reg rfOutRLoc, .reg rfPruneWork,
         .reg rfCcapReg, .reg rfHParamReg, .const 1]
    , rfExtractRStmt ]

/-- Complete deterministic module for `RemoveFake` installed at index `b`. -/
def removeFakeProcs (b : ℕ) : List Stmt :=
  [removeFakeEntry b, buildCsrProc, rfPruneWrap]

/-- Explicit Word-RAM step bound for `removeFakeEntry`, linear in `|X| + |H| + |F|` up to
`pruneTimeBound` on the subdivided graph. -/
def removeFakeCost (k mH mF rhoNum rhoDen : ℕ) : ℕ :=
  let nJ := k + mF
  let mJ := mH + 2 * mF
  let H_param := rfHParam mH mF rhoNum rhoDen
  pruneTimeBound nJ mJ H_param +
    350 * nJ + 300 * mJ + 20 * Nat.log 2 (2 * mJ + 1) + 600

/-- Word-RAM contract for `removeFakeEntry`: given `X` (`verts`), host edges `H` inside `X`, fake
edges `F` inside `X`, and rational `ρ = rhoNum / rhoDen ∈ (0, 1]` at `rhoAddr`, writes a nodup
list `R_list` of kept original vertices at `outRAddr` and returns `|R_list|`, with the full
postcondition of `removeFake_of_pruned` read from memory. -/
def removeFakeContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen : ℕ)
      (verts : List ℕ) (H F : List (ℕ × ℕ)),
      args = [k, vertsAddr, mH, hAddr, mF, fAddr, rhoAddr, locAddr, outRAddr, workAddr] ∧
      verts.length = k ∧ verts.Nodup ∧ (∀ u ∈ verts, u < n) ∧
      H.length = mH ∧ F.length = mF ∧
      (∀ e ∈ H, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset) ∧
      (∀ e ∈ F, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset) ∧
      ListAt mem vertsAddr verts ∧
      EdgesAt mem hAddr H ∧
      EdgesAt mem fAddr F ∧
      mem rhoAddr = rhoNum ∧ mem (rhoAddr + 1) = rhoDen ∧
      1 ≤ rhoNum ∧ rhoNum ≤ rhoDen ∧
      (Graph.mk n (H ++ F)).IsConductanceExpanderOn verts.toFinset ((rhoNum : ℝ) / (rhoDen : ℝ)) ∧
      (∀ v ∈ verts.toFinset, 1 ≤ (Graph.mk n (H ++ F)).degIn verts.toFinset v) ∧
      RemoveFakeWordBound w n k mH mF rhoNum rhoDen
        vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr ∧
      RemoveFakeDisjoint n k mH mF (rfHParam mH mF rhoNum rhoDen)
        vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr
  post args mem v mem' :=
    let k := args.getD 0 0
    let vertsAddr := args.getD 1 0
    let mH := args.getD 2 0
    let hAddr := args.getD 3 0
    let mF := args.getD 4 0
    let fAddr := args.getD 5 0
    let rhoAddr := args.getD 6 0
    let locAddr := args.getD 7 0
    let outRAddr := args.getD 8 0
    let workAddr := args.getD 9 0
    let verts := readList mem vertsAddr k
    let X := verts.toFinset
    let H := readEdges mem hAddr mH
    let F := readEdges mem fAddr mF
    let rhoNum := mem rhoAddr
    let rhoDen := mem (rhoAddr + 1)
    let ρ : ℝ := (rhoNum : ℝ) / (rhoDen : ℝ)
    let R_list := readList mem' outRAddr v
    let R := R_list.toFinset
    let ws := removeFakeWorkSpace k mH mF (rfHParam mH mF rhoNum rhoDen)
    v ≤ k ∧
    R_list.Nodup ∧
    R ⊆ X ∧
    (∀ n, (∀ u ∈ verts, u < n) →
      (Graph.mk n H).IsConductanceExpanderOn R (ρ / 9) ∧
      (∀ u ∈ R, 1 ≤ (Graph.mk n H).degIn R u) ∧
      (Graph.mk n (H ++ F)).volIn X (X \ R) ≤ 4 * rfCcap rhoNum rhoDen * mF ∧
      ((Graph.mk n (H ++ F)).volIn X (X \ R) : ℝ) ≤ 60 / ρ * mF) ∧
    (∀ u ∈ verts, mem' (locAddr + u) = 0) ∧
    (∀ a, (∀ u ∈ verts, a ≠ locAddr + u) →
      (a < outRAddr ∨ outRAddr + k ≤ a) →
      (a < workAddr ∨ workAddr + ws ≤ a) →
      mem' a = mem a)
  cost args mem :=
    removeFakeCost (args.getD 0 0) (args.getD 2 0) (args.getD 4 0)
      (mem (args.getD 6 0)) (mem (args.getD 6 0 + 1))

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma rfPruneWrap_noRand : rfPruneWrap.NoRand :=
  ⟨pruneExpanderStmt_noRand, by simp [Stmt.NoRand]⟩

lemma removeFakeEntry_noRand (b : ℕ) : (removeFakeEntry b).NoRand := by
  simp [removeFakeEntry, seqStmts, Stmt.NoRand, rfSetupStmt_noRand, rfFillLocStmt_noRand,
    rfBuildJStmt_noRand, rfClearLocStmt_noRand, rfBuildInBStmt_noRand, rfComputeHStmt_noRand,
    rfExtractRStmt_noRand]

theorem removeFakeProcs_noRand (b : ℕ) : ∀ s ∈ removeFakeProcs b, s.NoRand := by
  intro s hs
  simp only [removeFakeProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact removeFakeEntry_noRand b
  · exact buildCsrProc_noRand
  · exact rfPruneWrap_noRand

/-! ## 2. `rfPruneWrap` Wrapper Spec -/

/-- Direct specification of `rfPruneWrap` retaining the full volume-plus-cut pruning bound needed
by `removeFake_of_pruned`. -/
theorem rfPruneWrap_runs {w : ℕ} {p : Program}
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
      Runs w p ω rfPruneWrap (startState args mem pos) (.returned 0) st' c ∧
      st'.pos = pos ∧
      PreservedOutside2 mem st'.mem outRAddr (outRAddr + cfg.G.n)
        workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
      c ≤ pruneTimeBound cfg.G.n cfg.G.m cfg.H + 3 ∧
      let R : Finset ℕ := (Finset.range cfg.G.n).filter fun x => decide (st'.mem (outRAddr + x) ≠ 0)
      R ⊆ cfg.X \ cfg.B ∧
      cfg.G.IsConductanceExpanderOn R (φ₀ / 3) ∧
      (∀ v ∈ R, cfg.θ_out_nat ≤ cfg.G.degIn R v) ∧
      cfg.G.volIn cfg.X ((cfg.X \ cfg.B) \ R) + 2 * cfg.C_cap * cfg.G.cutIn cfg.X R ≤
        2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B := by
  intro args
  let st₀ := startState args mem pos
  have hreg0 : InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hw0 : 0 < 2 ^ w := Nat.two_pow_pos w
  obtain ⟨st', c, hr, hpos', hpr, hc, hRsub, hexpR, hdegR, hvc, _⟩ :=
    pruneExpander_wordram_spec (p := p) st₀ ω hreg0 hcfgX hval hexp hφ₀ hC5 hCphi hθ hw hdisj
      hg_w hcsr_w hinB_w houtR_w hG hCsr hinB
  have hret : Runs w p ω (.ret (.const 0)) st' (.returned 0) st' 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, by simp [Expr.size]⟩
  have hseq : Runs w p ω rfPruneWrap st₀ (.returned 0) st' (c + 2 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st', c, 2, hr, hret, rfl⟩)
  exact ⟨st', c + 2 + 1, hseq, hpos', hpr, by omega, hRsub, hexpR, hdegR, hvc⟩

/-! ## 3. Main Theorem: `removeFake_spec_prog` -/

private lemma rf_pruneMemDisjoint (workAddr k mH mF H_param : ℕ) :
    let nJ := k + mF
    let mJ := mH + 2 * mF
    PruneMemDisjoint (rfJGraphAddr workAddr) (rfCsrAddr workAddr k mH mF)
      (rfInBAddr workAddr mH mF) (rfOutRLocAddr workAddr k mH mF)
      (rfPruneWorkAddr workAddr k mH mF) nJ mJ H_param (2 + 2 * mJ) := by
  dsimp only [PruneMemDisjoint, rfJGraphAddr, rfInBAddr, rfOutRLocAddr, rfCsrAddr, rfPruneWorkAddr]
  refine ⟨Or.inr (by omega), Or.inl (by omega), Or.inr (by omega), Or.inr (by omega),
    Or.inr (by omega), Or.inr (by omega), Or.inl (by omega)⟩

/-- Main Word-RAM specification of `RemoveFake`: `removeFakeProcs b` meets `removeFakeContract w`,
delivering the full guarantees of `removeFake_of_pruned` (conductance `ρ / 9` on `R`, minimum
degree `≥ 1` in `H[R]`, and removed `K`-volume `≤ 4 * C_cap * |F| ≤ 60 / ρ * |F|`) in
`removeFakeCost` deterministic steps. -/
theorem removeFake_spec_prog {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (removeFakeProcs b)) :
    MeetsContract w p b (removeFakeContract w) := by
  have hEntry : p.procs[b]? = some (removeFakeEntry b) := by
    simpa [removeFakeProcs] using hp 0 (by simp [removeFakeProcs])
  have hCsrAt : p.HasAt (b + 1) [buildCsrProc] := by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa [removeFakeProcs] using hp 1 (by simp [removeFakeProcs])
  have hPruneAt : p.procs[b + 2]? = some rfPruneWrap := by
    simpa [removeFakeProcs] using hp 2 (by simp [removeFakeProcs])
  have hCsrSpec := buildCsr_spec (w := w) hCsrAt
  intro args mem pos ω _ hpre
  rcases hpre with ⟨n, k, vertsAddr, mH, hAddr, mF, fAddr, rhoAddr, locAddr, outRAddr, workAddr,
    rhoNum, rhoDen, verts, H, F, hargs, hvlen, hnd, hverts_lt, hHlen, hFlen, hH_in, hF_in,
    hverts_at, hH_at, hF_at, hrho1, hrho2, hrho_pos, hrho_le, hK_exp, hK_deg, hw, hdisj⟩
  subst hargs
  set nJ := k + mF
  set mJ := mH + 2 * mF
  set C_cap := rfCcap rhoNum rhoDen
  set H_param := rfHParam mH mF rhoNum rhoDen
  set ws := removeFakeWorkSpace k mH mF H_param
  set H_loc := relabelEdges verts H
  set F_loc := relabelEdges verts F
  set J_loc := subdivGraph k H_loc F_loc
  set ρ : ℝ := (rhoNum : ℝ) / (rhoDen : ℝ)
  have hws_lt := rfWorkSpace_word_lt hw
  have hws_def : ws = 4 * nJ + 6 * mJ + 3 + pruneWorkSpace nJ mJ H_param := rfl
  rcases hdisj with ⟨hd_lv, hd_lh, hd_lf, hd_lr, hd_lo, hd_lw, hd_ov, hd_oh, hd_of, hd_or, hd_ow,
    hd_wv, hd_wh, hd_wf, hd_wr⟩
  have hρ_pos : 0 < ρ := by
    have : (0 : ℝ) < rhoNum := by exact_mod_cast hrho_pos
    have : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans hrho_pos hrho_le)
    positivity
  have hρ_le1 : ρ ≤ 1 := by
    have : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans hrho_pos hrho_le)
    rw [div_le_one this]; exact_mod_cast hrho_le
  -- Mathematical facts on the relabeled graph `J_loc`
  have hJn : J_loc.n = nJ := by simp [J_loc, subdivGraph, F_loc, relabelEdges, hFlen, nJ]
  have hJm : J_loc.m = mJ := by
    simp [J_loc, subdivGraph, Graph.m, H_loc, F_loc, relabelEdges, subdiv_length, hHlen, hFlen, mJ]
  have hH_loc_lt : ∀ e ∈ H_loc, e.1 < k ∧ e.2 < k := by
    intro e he
    simp only [H_loc, relabelEdges, List.mem_map] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    exact ⟨hvlen ▸ List.idxOf_lt_length_of_mem (List.mem_toFinset.mp (hH_in e₀ he₀).1),
      hvlen ▸ List.idxOf_lt_length_of_mem (List.mem_toFinset.mp (hH_in e₀ he₀).2)⟩
  have hF_loc_in : ∀ e ∈ F_loc, e.1 ∈ Finset.range k ∧ e.2 ∈ Finset.range k := by
    intro e he
    simp only [F_loc, relabelEdges, List.mem_map] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    exact ⟨Finset.mem_range.mpr (hvlen ▸ List.idxOf_lt_length_of_mem (List.mem_toFinset.mp (hF_in e₀ he₀).1)),
      Finset.mem_range.mpr (hvlen ▸ List.idxOf_lt_length_of_mem (List.mem_toFinset.mp (hF_in e₀ he₀).2))⟩
  have hHF_in : ∀ e ∈ H ++ F, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset := by
    intro e he
    rcases List.mem_append.mp he with he' | he'
    · exact hH_in e he'
    · exact hF_in e he'
  have hKloc_eq : Graph.mk k (H_loc ++ F_loc) = relabelGraph verts (H ++ F) := by
    simp [relabelGraph, relabelEdges, H_loc, F_loc, hvlen]
  have hKloc_exp : (Graph.mk k (H_loc ++ F_loc)).IsConductanceExpanderOn (Finset.range k) ρ := by
    rw [hKloc_eq, ← hvlen]
    rw [relabelGraph_isConductanceExpanderOn_iff (n := n) hnd hHF_in (Finset.Subset.refl _),
      image_range_getD]
    exact hK_exp
  have hKloc_deg : ∀ v ∈ Finset.range k,
      1 ≤ (Graph.mk k (H_loc ++ F_loc)).degIn (Finset.range k) v := by
    intro v hv
    rw [hKloc_eq, ← hvlen]
    have hv_lt : v < verts.length := hvlen.symm ▸ Finset.mem_range.mp hv
    rw [relabelGraph_degIn (n := n) hnd hHF_in (Finset.Subset.refl _) hv_lt, image_range_getD]
    have hv_mem : verts.getD v 0 ∈ verts.toFinset := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv_lt, Option.getD_some,
        List.mem_toFinset]
      exact List.getElem_mem hv_lt
    exact hK_deg _ hv_mem
  have hJ_exp : J_loc.IsConductanceExpanderOn (Finset.range J_loc.n) (ρ / 3) := by
    have h1 := isConductanceExpanderOn_subdivGraph (Finset.Subset.refl _) hH_loc_lt hF_loc_in
      hρ_pos hρ_le1 hKloc_exp
    rwa [range_union_midpoints] at h1
  let cfg : PruneCfg :=
    { G := J_loc
      X := Finset.range J_loc.n
      B := midpoints k F_loc
      C_cap := C_cap
      H := H_param
      θ_out_nat := 1 }
  have hHloc_len : H_loc.length = mH := by simp [H_loc, relabelEdges, hHlen]
  have hFloc_len : F_loc.length = mF := by simp [F_loc, relabelEdges, hFlen]
  obtain ⟨hcfg_val, hcfg_theta⟩ : cfg.Valid ∧
      (∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x) := by
    have h := rf_pruneCfg_valid hrho_pos hrho_le hH_loc_lt hF_loc_in hKloc_deg
    simpa only [hHloc_len, hFloc_len, cfg, J_loc, C_cap, H_param] using h
  -- Execute Stages 0..8
  have hrun_full : ∃ o st_fin c,
      Runs w p ω (removeFakeEntry b) (startState [k, vertsAddr, mH, hAddr, mF, fAddr, rhoAddr, locAddr, outRAddr, workAddr] mem pos) o st_fin c ∧
      (removeFakeContract w).post [k, vertsAddr, mH, hAddr, mF, fAddr, rhoAddr, locAddr, outRAddr, workAddr] mem o.value st_fin.mem ∧
      c ≤ removeFakeCost k mH mF rhoNum rhoDen := by
    refine runs_start_le ?_
    dsimp only [removeFakeEntry, seqStmts]
    -- Stage 0: rfSetupStmt
    refine runs_seq_triple_le (rfSetup_triple p mem pos hrho1 hrho2 hw) rfl ?_
    intro st0 ⟨hr0, hm0, hpos0⟩
    -- Stage 1: rfFillLocStmt
    refine runs_seq_triple_le
      (rfFillLoc_triple p mem verts st0 hvlen hnd hverts_lt hverts_at hd_lv hw hr0 hm0) rfl ?_
    intro st1 ⟨hr1, hpos1, hfr1, hpt1, hloc1⟩
    have hH_at1 : EdgesAt st1.mem hAddr H :=
      hH_at.congr fun a ha1 ha2 => hfr1 a (disjointRange_outside hd_lh ha1 (by omega))
    have hF_at1 : EdgesAt st1.mem fAddr F :=
      hF_at.congr fun a ha1 ha2 => hfr1 a (disjointRange_outside hd_lf ha1 (by omega))
    -- Stage 2: rfBuildJStmt
    have hd_wl_j : DisjointRange workAddr (2 + 2 * mJ) locAddr n :=
      disjointRange_shrink_left hd_lw.symm (by dsimp only [ws, removeFakeWorkSpace, nJ, mJ]; omega)
    have hd_wh_j : DisjointRange workAddr (2 + 2 * mJ) hAddr (2 * mH) :=
      disjointRange_shrink_left hd_wh (by dsimp only [ws, removeFakeWorkSpace, nJ, mJ]; omega)
    have hd_wf_j : DisjointRange workAddr (2 + 2 * mJ) fAddr (2 * mF) :=
      disjointRange_shrink_left hd_wf (by dsimp only [ws, removeFakeWorkSpace, nJ, mJ]; omega)
    refine runs_seq_triple_le
      (rfBuildJ_triple p st1.mem verts H F st1 hHlen hFlen hverts_lt hH_in hF_in hH_at1 hF_at1
        hloc1 hd_wl_j hd_wh_j hd_wf_j hw hr1 rfl) rfl ?_
    intro st2 ⟨hr2, hpos2, hfr2, hG2⟩
    have hverts_at2 : ListAt st2.mem vertsAddr verts :=
      hverts_at.congr fun a ha1 ha2 => by
        have hd_wv_j : DisjointRange workAddr (2 + 2 * mJ) vertsAddr k :=
          disjointRange_shrink_left hd_wv (by dsimp only [ws, removeFakeWorkSpace, nJ, mJ]; omega)
        have hout2 := disjointRange_outside hd_wv_j (x := a) ha1 (by omega)
        have hout1 := disjointRange_outside hd_lv (x := a) ha1 (by omega)
        rw [hfr2 a (by rcases hout2 with h | h <;> [left; right] <;> dsimp only [mJ] at * <;> omega),
            hfr1 a hout1]
    -- Stage 3: rfClearLocStmt
    refine runs_seq_triple_le
      (rfClearLoc_triple p st2.mem verts st2 hvlen hverts_lt hverts_at2 hd_lv hw hr2 rfl) rfl ?_
    intro st3 ⟨hr3, hpos3, hfr3, hpt3, hclr3⟩
    have hG3 : GraphAt st3.mem workAddr J_loc :=
      hG2.congr fun a ha1 ha2 => by
        have hlenJ : J_loc.encode.length = 2 + 2 * mJ := by
          rw [graph_encode_length, hJm]
        have ha2' : a < workAddr + (2 + 2 * mJ) := by
          change a < workAddr + J_loc.encode.length at ha2; omega
        exact hfr3 a (disjointRange_outside hd_wl_j.symm (x := a) ha1 ha2')
    -- Stage 4: rfBuildInBStmt
    refine runs_seq_triple_le (rfBuildInB_triple p st3.mem st3 hw hr3 rfl) rfl ?_
    intro st4 ⟨hr4, hpos4, hfr4, hinB4⟩
    have hG4 : GraphAt st4.mem workAddr J_loc :=
      hG3.congr fun a ha1 ha2 => by
        have hlenJ : J_loc.encode.length = 2 + 2 * mJ := by rw [graph_encode_length, hJm]
        change a < workAddr + J_loc.encode.length at ha2
        exact hfr4 a (Or.inl (by dsimp only [rfInBAddr, mJ] at *; omega))
    -- Stage 5: rfComputeHStmt
    refine runs_seq_triple_le (rfComputeH_triple p st4 hw hr4) rfl ?_
    intro st5 ⟨hr5, hHreg5, hm5, hpos5⟩
    have hG5 : GraphAt st5.mem workAddr J_loc := hm5 ▸ hG4
    have hinB5 : ∀ x, x ∈ cfg.B ↔ x < J_loc.n ∧ st5.mem (rfInBAddr workAddr mH mF + x) ≠ 0 := by
      intro x
      rw [hm5, hJn]
      have hB_eq : cfg.B = Finset.Ico k (k + mF) := by
        simp [cfg, midpoints, F_loc, relabelEdges, hFlen]
      rw [hB_eq]
      exact hinB4 x
    -- Stage 6: buildCsrProc call
    have hcsr_args : evalArgs w st5 [.reg rfJGraph, .reg rfCsr] =
        some [workAddr, rfCsrAddr workAddr k mH mF] := by
      simp [evalArgs, Expr.eval, hr5.r_jGraph, hr5.r_csr, rfJGraphAddr]
    have hcsr_words : ∀ v ∈ [workAddr, rfCsrAddr workAddr k mH mF], v < 2 ^ w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by omega, by dsimp only [rfCsrAddr]; omega⟩
    have hcsr_pre : (buildCsrContract w).pre [workAddr, rfCsrAddr workAddr k mH mF] st5.mem := by
      refine ⟨workAddr, rfCsrAddr workAddr k mH mF, J_loc, rfl, hG5, hcfg_val.1, ?_, ?_, by omega⟩
      · rw [graph_encode_length, hJm]; dsimp only [rfCsrAddr]; omega
      · rw [hJn, hJm]; dsimp only [rfCsrAddr]; omega
    refine runs_seq_call_le (vs := [workAddr, rfCsrAddr workAddr k mH mF])
      hCsrSpec hcsr_args hcsr_words hcsr_pre ?_
    intro v6 mem6 pos6 hpost6
    have hread5 : Cited.readGraph st5.mem workAddr = J_loc := graphAt_iff_readGraph.mp hG5
    simp only [buildCsrContract, List.getD_cons_zero, List.getD_cons_succ, hread5] at hpost6
    rcases hpost6 with ⟨_, hCsr6, hfr6⟩
    let st6 : State := { mem := mem6, regs := Function.update st5.regs rfTmp1 v6, pos := pos6 }
    have hr6 : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st6 :=
      rfRegs_of_agree hr5 fun r hle => Function.update_of_ne (by dsimp [rfTmp1]; omega) _ _
    have hHreg6 : st6.regs rfHParamReg = H_param := by
      simp [st6, hHreg5, H_param]
    have hG6 : GraphAt mem6 workAddr J_loc :=
      hG5.congr fun a ha1 ha2 => by
        have hlenJ : J_loc.encode.length = 2 + 2 * mJ := by rw [graph_encode_length, hJm]
        exact hfr6 a (Or.inl (by dsimp only [rfCsrAddr]; omega))
    have hinB6 : ∀ x, x ∈ cfg.B ↔ x < J_loc.n ∧ mem6 (rfInBAddr workAddr mH mF + x) ≠ 0 := by
      intro x
      rw [hinB5 x]
      refine and_congr_right fun hx => ?_
      rw [hJn] at hx
      rw [hfr6 (rfInBAddr workAddr mH mF + x) (Or.inl (by dsimp only [rfInBAddr, rfCsrAddr]; omega))]
    -- Stage 7: rfPruneWrap call
    have hp_args_list : evalArgs w st6
        [.reg rfJGraph, .reg rfCsr, .reg rfInB, .reg rfOutRLoc, .reg rfPruneWork,
         .reg rfCcapReg, .reg rfHParamReg, .const 1] =
        some [workAddr, rfCsrAddr workAddr k mH mF, rfInBAddr workAddr mH mF,
              rfOutRLocAddr workAddr k mH mF, rfPruneWorkAddr workAddr k mH mF,
              C_cap, H_param, 1] := by
      simp [evalArgs, Expr.eval, hr6.r_jGraph, hr6.r_csr, hr6.r_inB, hr6.r_outRLoc,
        hr6.r_pruneWork, hr6.r_ccap, hHreg6, rfJGraphAddr, show 1 < 2 ^ w by omega, C_cap]
    have hpw : PruneWordBound w J_loc.n J_loc.m cfg.C_cap cfg.H (rfPruneWorkAddr workAddr k mH mF) := by
      rw [hJn, hJm]; exact hw.2.2.2.2.2.2.2
    have hpd : PruneMemDisjoint workAddr (rfCsrAddr workAddr k mH mF) (rfInBAddr workAddr mH mF)
        (rfOutRLocAddr workAddr k mH mF) (rfPruneWorkAddr workAddr k mH mF)
        J_loc.n J_loc.m cfg.H J_loc.encode.length := by
      rw [hJn, hJm, graph_encode_length, hJm]
      exact rf_pruneMemDisjoint workAddr k mH mF H_param
    obtain ⟨st7_inner, c7, hr7_inner, hpos7_inner, hpr7, hc7, hRloc_sub, hRloc_exp, hRloc_deg, hRloc_vc⟩ :=
      rfPruneWrap_runs (w := w) (p := p) (cfg := cfg) (φ₀ := ρ / 3)
        mem6 pos6 ω rfl hcfg_val hJ_exp (by positivity)
        (by have := rfCcap_ge_fourteen hrho_pos hrho_le; dsimp only [cfg, C_cap]; omega)
        (rfCcap_phi_bound hrho_pos hrho_le) hcfg_theta hpw hpd
        (by rw [graph_encode_length, hJm]; omega)
        (by rw [hJn, hJm]; dsimp only [rfCsrAddr]; omega)
        (by rw [hJn]; dsimp only [rfInBAddr]; omega)
        (by rw [hJn]; dsimp only [rfOutRLocAddr]; omega)
        hG6 hCsr6 hinB6
    let st7 : State := { mem := st7_inner.mem, regs := Function.update st6.regs rfTmp1 0, pos := st7_inner.pos }
    have hcall7 : Runs w p ω
        (.call rfTmp1 (b + 2)
          [.reg rfJGraph, .reg rfCsr, .reg rfInB, .reg rfOutRLoc, .reg rfPruneWork,
           .reg rfCcapReg, .reg rfHParamReg, .const 1])
        st6 .normal st7 (argsSize [.reg rfJGraph, .reg rfCsr, .reg rfInB, .reg rfOutRLoc,
          .reg rfPruneWork, .reg rfCcapReg, .reg rfHParamReg, .const 1] + c7 + 1) :=
      runs_call_iff.mpr ⟨_, rfPruneWrap, .returned 0, st7_inner, c7,
        hp_args_list, hPruneAt, hr7_inner, rfl, rfl, rfl⟩
    have hr7 : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st7 :=
      rfRegs_of_agree hr6 fun r hle => Function.update_of_ne (by dsimp [rfTmp1]; omega) _ _
    -- Memory frame from `st3.mem` to `st7.mem` outside `[workAddr, workAddr + ws)`
    have hwork_to7 : ∀ a, (a < workAddr ∨ workAddr + ws ≤ a) → st7.mem a = st3.mem a := by
      intro a haw
      have h7 : st7.mem a = mem6 a := by
        apply hpr7 a
        · rcases haw with h | h
          · left; dsimp only [rfOutRLocAddr]; linarith only [h]
          · right; dsimp only [cfg]; rw [hJn]
            dsimp only [rfOutRLocAddr, ws, removeFakeWorkSpace, nJ, mJ, H_param] at h ⊢
            linarith only [h]
        · rcases haw with h | h
          · left; dsimp only [rfPruneWorkAddr]; linarith only [h]
          · right; dsimp only [cfg]; rw [hJn, hJm]
            dsimp only [rfPruneWorkAddr, ws, removeFakeWorkSpace, nJ, mJ, H_param] at h ⊢
            linarith only [h]
      have h6 : mem6 a = st5.mem a := by
        apply hfr6 a
        rw [hJn, hJm]
        rcases haw with h | h
        · left; dsimp only [rfCsrAddr, nJ, mJ]; linarith only [h]
        · right; dsimp only [rfCsrAddr, ws, removeFakeWorkSpace, nJ, mJ, H_param] at h ⊢
          linarith only [h]
      have h4 : st4.mem a = st3.mem a := by
        apply hfr4 a
        rcases haw with h | h
        · left; dsimp only [rfInBAddr]; linarith only [h]
        · right; dsimp only [rfInBAddr, ws, removeFakeWorkSpace, nJ, mJ, H_param] at h ⊢
          linarith only [h]
      rw [h7, h6, hm5, h4]
    have hwork_12 : ∀ a, (a < workAddr ∨ workAddr + ws ≤ a) → st2.mem a = st1.mem a := by
      intro a haw
      apply hfr2 a
      rcases haw with h | h
      · left; linarith only [h]
      · right; dsimp only [ws, removeFakeWorkSpace, nJ, mJ, H_param] at h ⊢
        linarith only [h]
    have hverts_at7 : ListAt st7.mem vertsAddr verts :=
      hverts_at.congr fun a ha1 ha2 => by
        have hal := disjointRange_outside hd_lv (x := a) ha1 (by omega)
        have haw := disjointRange_outside hd_wv (x := a) ha1 (by omega)
        rw [hwork_to7 a haw, hfr3 a hal, hwork_12 a haw, hfr1 a hal]
    -- Stage 8: rfExtractRStmt
    have hd_ow_loc : DisjointRange outRAddr k (rfOutRLocAddr workAddr k mH mF) k := by
      rcases hd_ow with h | h
      · left; dsimp only [rfOutRLocAddr]; omega
      · right; dsimp only [rfOutRLocAddr, ws, removeFakeWorkSpace, nJ, mJ] at *; omega
    obtain ⟨o8, st8, c8, hr8, hq8, hc8⟩ :=
      rfExtractR_triple p st7.mem verts st7 hvlen hverts_at7 hd_ov hd_ow_loc hw hr7 rfl st7 ω rfl
    rcases hq8 with ⟨ho8, _, hfr8, hlat8⟩
    refine ⟨o8, st8, _, runs_seq_iff.mpr (Or.inr ⟨st7, _, c8, hcall7, hr8, rfl⟩), ?_, ?_⟩
    · -- Postcondition proof
      have hRloc_eq :
          (Finset.range J_loc.n).filter (fun x => decide (st7_inner.mem (rfOutRLocAddr workAddr k mH mF + x) ≠ 0)) =
          (Finset.range k).filter (fun x => decide (st7.mem (rfOutRLocAddr workAddr k mH mF + x) ≠ 0)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨hxJ, hnz⟩
          have hx_mem : x ∈ (Finset.range J_loc.n).filter
              (fun y => decide (st7_inner.mem (rfOutRLocAddr workAddr k mH mF + y) ≠ 0)) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxJ, decide_eq_true hnz⟩
          have hx_sdiff := hRloc_sub hx_mem
          simp only [cfg, midpoints, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico] at hx_sdiff
          rw [hJn, hFloc_len] at hx_sdiff
          exact ⟨by omega, hnz⟩
        · rintro ⟨hxk, hnz⟩
          exact ⟨by rw [hJn]; omega, hnz⟩
      set R_loc := (Finset.range J_loc.n).filter
        fun x => decide (st7_inner.mem (rfOutRLocAddr workAddr k mH mF + x) ≠ 0)
      set R_list := filterVertsByMem st7.mem (rfOutRLocAddr workAddr k mH mF) verts
      have hread_verts : readList mem vertsAddr k = verts :=
        hvlen ▸ readList_eq_of_listAt hverts_at
      have hread_H : readEdges mem hAddr mH = H := hHlen ▸ readEdges_eq_of_edgesAt hH_at
      have hread_F : readEdges mem fAddr mF = F := hFlen ▸ readEdges_eq_of_edgesAt hF_at
      have hval_eq : o8.value = R_list.length := by rw [ho8]; rfl
      have hread_R : readList st8.mem outRAddr o8.value = R_list := by
        rw [hval_eq]; exact readList_eq_of_listAt hlat8
      have hR_img : R_list.toFinset = R_loc.image (fun i => verts.getD i 0) := by
        rw [filterVertsByMem_toFinset, hvlen, hRloc_eq]
      -- Apply `removeFake_of_pruned` on the local subdivided graph `J_loc`
      have hYB : Finset.range k ∪ midpoints k F_loc = Finset.range J_loc.n := by
        rw [range_union_midpoints, hJn, hFloc_len]
      have hRloc_sub' : R_loc ⊆ (Finset.range k ∪ midpoints k F_loc) \ midpoints k F_loc := by
        rw [hYB]; exact hRloc_sub
      have hRloc_degR : ∀ v ∈ R_loc, (1 : ℝ) ≤ (J_loc.degIn R_loc v : ℝ) := fun v hv => by
        exact_mod_cast hRloc_deg v hv
      have hRloc_vc' :
          J_loc.volIn (Finset.range k ∪ midpoints k F_loc)
              (((Finset.range k ∪ midpoints k F_loc) \ midpoints k F_loc) \ R_loc) +
            2 * C_cap * J_loc.cutIn (Finset.range k ∪ midpoints k F_loc) R_loc ≤
          2 * C_cap * J_loc.cutIn (Finset.range k ∪ midpoints k F_loc) (midpoints k F_loc) := by
        rw [hYB]; exact hRloc_vc
      obtain ⟨hRloc_k, hHloc_exp, hHloc_deg, hKloc_vol⟩ :=
        removeFake_of_pruned (Finset.Subset.refl _) hH_loc_lt hF_loc_in
          hRloc_sub' hRloc_exp hRloc_degR hRloc_vc'
      -- Now discharge all conjuncts of `(removeFakeContract w).post`
      dsimp only [removeFakeContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hread_verts, hread_H, hread_F,
        hrho1, hrho2, hread_R]
      refine ⟨by rw [hval_eq, ← hvlen]; exact filterVertsByMem_length_le _ _ _,
        filterVertsByMem_nodup hnd, ?_, ?_, ?_, ?_⟩
      · rw [hR_img]
        exact image_getD_subset_toFinset (hvlen ▸ hRloc_k)
      · intro n' _
        have hHloc_eq : Graph.mk k H_loc = relabelGraph verts H := by
          simp [relabelGraph, H_loc, hvlen]
        have hρ9 : ρ / 3 / 3 = ρ / 9 := by ring
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hR_img]
          rw [← relabelGraph_isConductanceExpanderOn_iff (n := n') hnd hH_in (hvlen ▸ hRloc_k),
            ← hHloc_eq, ← hρ9]
          exact hHloc_exp
        · intro u hu
          rw [hR_img] at hu ⊢
          rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
          have hi_lt : i < verts.length := hvlen.symm ▸ Finset.mem_range.mp (hRloc_k hi)
          have hdeg_eq := relabelGraph_degIn (n := n') hnd hH_in (hvlen ▸ hRloc_k) hi_lt
          rw [← hHloc_eq] at hdeg_eq
          have h1R := hHloc_deg i hi
          rw [hdeg_eq] at h1R
          exact_mod_cast h1R
        · have hvol_eq := relabelGraph_volIn (n := n') hnd hHF_in
            (Finset.Subset.refl _) (Finset.sdiff_subset : Finset.range verts.length \ R_loc ⊆ Finset.range verts.length)
          rw [image_sdiff_getD hnd (Finset.Subset.refl _) (hvlen ▸ hRloc_k),
            image_range_getD, ← hR_img, ← hKloc_eq, hvlen] at hvol_eq
          rw [← hvol_eq, ← hFloc_len]
          exact hKloc_vol
        · have hvol_eq := relabelGraph_volIn (n := n') hnd hHF_in
            (Finset.Subset.refl _) (Finset.sdiff_subset : Finset.range verts.length \ R_loc ⊆ Finset.range verts.length)
          rw [image_sdiff_getD hnd (Finset.Subset.refl _) (hvlen ▸ hRloc_k),
            image_range_getD, ← hR_img, ← hKloc_eq, hvlen] at hvol_eq
          have hvolR : ((Graph.mk n' (H ++ F)).volIn verts.toFinset (verts.toFinset \ R_list.toFinset) : ℝ) ≤
              4 * (C_cap : ℝ) * (mF : ℝ) := by
            rw [← hvol_eq]
            have : (Graph.mk k (H_loc ++ F_loc)).volIn (Finset.range k) (Finset.range k \ R_loc) ≤
                4 * C_cap * mF := hFloc_len ▸ hKloc_vol
            exact_mod_cast this
          have hcap := rfCcap_le_fifteen_div_rho hrho_pos hrho_le
          have hmF0 : (0 : ℝ) ≤ mF := Nat.cast_nonneg _
          calc ((Graph.mk n' (H ++ F)).volIn verts.toFinset (verts.toFinset \ R_list.toFinset) : ℝ)
              ≤ 4 * (C_cap : ℝ) * mF := hvolR
            _ ≤ 4 * (15 / ρ) * mF := by gcongr
            _ = 60 / ρ * mF := by ring
      · -- `locAddr` cleared on all `u ∈ verts`
        intro u hu
        have hu_lt : u < n := hverts_lt u hu
        have hloc_out_w : locAddr + u < workAddr ∨ workAddr + ws ≤ locAddr + u :=
          disjointRange_outside hd_lw.symm (by omega) (by omega)
        have hloc_out_o : locAddr + u < outRAddr ∨ outRAddr + k ≤ locAddr + u :=
          disjointRange_outside hd_lo.symm (by omega) (by omega)
        rw [hfr8 (locAddr + u) hloc_out_o, hwork_to7 (locAddr + u) hloc_out_w, hclr3 u hu]
      · -- Frame outside `{locAddr + u | u ∈ verts}`, `outRAddr`, `workAddr`
        intro a hnotloc hao haw
        rw [hfr8 a hao, hwork_to7 a haw, hpt3 a hnotloc, hwork_12 a haw, hpt1 a hnotloc]
    · -- Cost bound
      have harg1 : argsSize [.reg rfJGraph, .reg rfCsr] = 2 := by decide
      have harg2 : argsSize [.reg rfJGraph, .reg rfCsr, .reg rfInB, .reg rfOutRLoc,
          .reg rfPruneWork, .reg rfCcapReg, .reg rfHParamReg, .const 1] = 8 := by decide
      have hc7' : c7 ≤ pruneTimeBound (k + mF) (mH + 2 * mF) (rfHParam mH mF rhoNum rhoDen) + 3 := by
        dsimp only [cfg] at hc7; rw [hJn, hJm] at hc7; exact hc7
      have hc8' : c8 ≤ 50 * k + 35 := hc8
      dsimp only [buildCsrContract, removeFakeCost]
      simp only [List.getD_cons_zero]
      rw [harg1, harg2, hread5, hJn, hJm]
      dsimp only [nJ, mJ]
      linarith only [hc7', hc8']
  rcases hrun_full with ⟨o, st_fin, c, hrun, hpost, hcost⟩
  refine ⟨removeFakeEntry b, hEntry, o, st_fin, c, hrun, hpost, ?_⟩
  simpa [removeFakeContract, hrho1, hrho2] using hcost

/-! ## 4. Asymptotic Cost Bound and Non-Vacuity Example -/

/-- Asymptotic shape of `removeFakeCost`: `O(|X| + |F| + (|H| + |F| + 1) · log²(|H| + |F| + 2) / ρ²)`.
-/
theorem removeFakeCost_le_asymptotic (k mH mF rhoNum rhoDen : ℕ)
    (h1 : 1 ≤ rhoNum) (h2 : rhoNum ≤ rhoDen) :
    let ρ : ℝ := (rhoNum : ℝ) / (rhoDen : ℝ)
    let L : ℕ := Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1
    (removeFakeCost k mH mF rhoNum rhoDen : ℝ) ≤
      100000000 * ((k : ℝ) + mF + ((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2) := by
  intro ρ L
  have hρ_pos : 0 < ρ := by
    have : (0 : ℝ) < rhoNum := by exact_mod_cast h1
    have : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans h1 h2)
    positivity
  have hρ_le1 : ρ ≤ 1 := by
    have : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans h1 h2)
    rw [div_le_one this]; exact_mod_cast h2
  have hinv_ge1 : (1 : ℝ) ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ_pos]; linarith
  have hL_ge1 : (1 : ℝ) ≤ L := by dsimp only [L]; norm_cast; omega
  have hL_div_ge1 : (1 : ℝ) ≤ (L : ℝ) / ρ := by
    have : (1 : ℝ) * 1 ≤ (L : ℝ) * (1 / ρ) := mul_le_mul hL_ge1 hinv_ge1 (by positivity) (by positivity)
    simpa [div_eq_mul_inv] using this
  have hC : (rfCcap rhoNum rhoDen : ℝ) ≤ 15 / ρ := rfCcap_le_fifteen_div_rho h1 h2
  have hH_le : (rfHParam mH mF rhoNum rhoDen : ℝ) ≤ 62 * ((L : ℝ) / ρ) := by
    have hdef : (rfHParam mH mF rhoNum rhoDen : ℝ) =
        4 * (rfCcap rhoNum rhoDen : ℝ) * (L : ℝ) + 2 := by
      unfold rfHParam; dsimp only [L]; push_cast; ring
    rw [hdef]
    have h1' : 4 * (rfCcap rhoNum rhoDen : ℝ) * (L : ℝ) ≤ 60 * ((L : ℝ) / ρ) := by
      calc 4 * (rfCcap rhoNum rhoDen : ℝ) * (L : ℝ)
          ≤ 4 * (15 / ρ) * (L : ℝ) := by gcongr
        _ = 60 * ((L : ℝ) / ρ) := by ring
    linarith
  have h4H14 : 4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 14 ≤ 262 * ((L : ℝ) / ρ) := by linarith
  have h4H4 : 4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 4 ≤ 252 * ((L : ℝ) / ρ) := by linarith
  have hprod : (4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 14) *
      (4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 4) ≤ 66024 * ((L : ℝ) ^ 2 / ρ ^ 2) := by
    calc (4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 14) *
          (4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 4)
        ≤ (262 * ((L : ℝ) / ρ)) * (252 * ((L : ℝ) / ρ)) :=
          mul_le_mul h4H14 h4H4 (by positivity) (by positivity)
      _ = 66024 * ((L : ℝ) ^ 2 / ρ ^ 2) := by ring
  have hmJ_le : (2 * (mH + 2 * mF) + 1 : ℝ) ≤ 4 * ((mH : ℝ) + mF + 1) := by linarith
  have hmain : 360 * ((4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 14) *
      (4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 4) * (2 * (mH + 2 * mF) + 1 : ℝ)) ≤
      95074560 * (((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2) := by
    calc 360 * ((4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 14) *
          (4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 4) * (2 * (mH + 2 * mF) + 1 : ℝ))
        ≤ 360 * ((66024 * ((L : ℝ) ^ 2 / ρ ^ 2)) * (4 * ((mH : ℝ) + mF + 1))) := by
          gcongr
      _ = 95074560 * (((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2) := by ring
  have hterm_ge1 : (1 : ℝ) ≤ ((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2 := by
    have hsq : (1 : ℝ) ≤ (L : ℝ) ^ 2 / ρ ^ 2 := by
      have : (1 : ℝ) ≤ ((L : ℝ) / ρ) ^ 2 := by nlinarith
      simpa [div_pow] using this
    have hm1 : (1 : ℝ) ≤ (mH : ℝ) + mF + 1 := by linarith
    have : 1 * 1 ≤ ((mH : ℝ) + mF + 1) * ((L : ℝ) ^ 2 / ρ ^ 2) :=
      mul_le_mul hm1 hsq (by positivity) (by positivity)
    simpa [mul_div_assoc] using this
  have hL_le_sq : (L : ℝ) / ρ ≤ ((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2 := by
    have h1' : (L : ℝ) / ρ ≤ ((L : ℝ) / ρ) ^ 2 := by nlinarith
    have hm1 : (1 : ℝ) ≤ (mH : ℝ) + mF + 1 := by linarith
    calc (L : ℝ) / ρ ≤ 1 * ((L : ℝ) / ρ) ^ 2 := by linarith
      _ ≤ ((mH : ℝ) + mF + 1) * ((L : ℝ) / ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right hm1 (by positivity)
      _ = ((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2 := by ring
  have hm_le_sq : (mH : ℝ) + 2 * mF ≤ 2 * (((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2) := by
    have hsq : (1 : ℝ) ≤ (L : ℝ) ^ 2 / ρ ^ 2 := by
      have : (1 : ℝ) ≤ ((L : ℝ) / ρ) ^ 2 := by nlinarith
      simpa [div_pow] using this
    calc (mH : ℝ) + 2 * mF ≤ 2 * ((mH : ℝ) + mF + 1) * 1 := by linarith
      _ ≤ 2 * ((mH : ℝ) + mF + 1) * ((L : ℝ) ^ 2 / ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * (((mH : ℝ) + mF + 1) * (L : ℝ) ^ 2 / ρ ^ 2) := by ring
  have hlog_le : (Nat.log 2 (2 * (mH + 2 * mF) + 1) : ℝ) ≤ (L : ℝ) / ρ := by
    have : (Nat.log 2 (2 * (mH + 2 * mF) + 1) : ℝ) ≤ (L : ℝ) := by dsimp only [L]; push_cast; linarith
    have : (L : ℝ) ≤ (L : ℝ) / ρ := by
      calc (L : ℝ) = (L : ℝ) * 1 := (mul_one _).symm
        _ ≤ (L : ℝ) * (1 / ρ) := mul_le_mul_of_nonneg_left hinv_ge1 (by positivity)
        _ = (L : ℝ) / ρ := by ring
    linarith
  have hcast : (removeFakeCost k mH mF rhoNum rhoDen : ℝ) =
      170 * ((k : ℝ) + mF) + 140 * ((mH : ℝ) + 2 * mF) +
      30 * ((rfHParam mH mF rhoNum rhoDen : ℝ) + 1) +
      360 * ((4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 14) *
        (4 * (rfHParam mH mF rhoNum rhoDen : ℝ) + 4) * (2 * (mH + 2 * mF) + 1 : ℝ)) + 221 +
      350 * ((k : ℝ) + mF) + 300 * ((mH : ℝ) + 2 * mF) +
      20 * (Nat.log 2 (2 * (mH + 2 * mF) + 1) : ℝ) + 600 := by
    unfold removeFakeCost pruneTimeBound
    push_cast
    ring
  rw [hcast]
  linarith

/-- Non-vacuity witness: all preconditions of `removeFakeContract 24` hold simultaneously on a
2-vertex graph with 1 real edge, 1 fake edge, and `ρ = 1`. -/
theorem removeFakeContract_pre_example :
    ∃ args mem, (∀ a ∈ args, a < 2 ^ 24) ∧ (removeFakeContract 24).pre args mem := by
  let verts : List ℕ := [0, 1]
  let H : List (ℕ × ℕ) := [(0, 1)]
  let F : List (ℕ × ℕ) := [(0, 1)]
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 0 else if a = 1 then 1
    else if a = 10 then 0 else if a = 11 then 1
    else if a = 20 then 0 else if a = 21 then 1
    else if a = 30 then 1 else if a = 31 then 1
    else 0
  let args : List ℕ := [2, 0, 1, 10, 1, 20, 30, 40, 50, 60]
  refine ⟨args, mem, by decide, ?_⟩
  refine ⟨2, 2, 0, 1, 10, 1, 20, 30, 40, 50, 60, 1, 1, verts, H, F, rfl,
    rfl, by decide, by decide, rfl, rfl, by decide, by decide, ?_, ?_, ?_,
    by simp [mem], by simp [mem], le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | i <;> simp [verts, mem] at hi ⊢
  · intro j hj
    rcases j with _ | j <;> simp [H, mem] at hj ⊢
  · intro j hj
    rcases j with _ | j <;> simp [F, mem] at hj ⊢
  · intro S hS hne hneX
    have hXeq : verts.toFinset = ({0, 1} : Finset ℕ) := by decide
    rw [hXeq] at hS hneX ⊢
    have hcases : S = {0} ∨ S = {1} := by
      have hsub : S ⊆ {0, 1} := hS
      by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S
      · exfalso; apply hneX; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx; exact by simpa using hsub hx
        · rintro (rfl | rfl) <;> assumption
      · left; ext x; simp only [Finset.mem_singleton]
        constructor
        · intro hx; have := Finset.mem_insert.mp (hsub hx)
          rcases this with rfl | hx1
          · rfl
          · exact absurd (Finset.mem_singleton.mp hx1 ▸ hx) h1
        · rintro rfl; exact h0
      · right; ext x; simp only [Finset.mem_singleton]
        constructor
        · intro hx; have := Finset.mem_insert.mp (hsub hx)
          rcases this with rfl | hx1
          · exact absurd hx h0
          · exact Finset.mem_singleton.mp hx1
        · rintro rfl; exact h1
      · exfalso; rcases hne with ⟨x, hx⟩
        rcases Finset.mem_insert.mp (hsub hx) with rfl | hx1
        · exact h0 hx
        · exact h1 (Finset.mem_singleton.mp hx1 ▸ hx)
    rcases hcases with rfl | rfl
    · have hcut : (Graph.mk 2 (H ++ F)).cutIn {0, 1} {0} = 2 := by decide
      have hv1 : (Graph.mk 2 (H ++ F)).volIn {0, 1} {0} = 2 := by decide
      have hv2 : (Graph.mk 2 (H ++ F)).volIn {0, 1} ({0, 1} \ {0}) = 2 := by decide
      rw [hcut, hv1, hv2]; norm_num
    · have hcut : (Graph.mk 2 (H ++ F)).cutIn {0, 1} {1} = 2 := by decide
      have hv1 : (Graph.mk 2 (H ++ F)).volIn {0, 1} {1} = 2 := by decide
      have hv2 : (Graph.mk 2 (H ++ F)).volIn {0, 1} ({0, 1} \ {1}) = 2 := by decide
      rw [hcut, hv1, hv2]; norm_num
  · intro v hv
    have hXeq : verts.toFinset = ({0, 1} : Finset ℕ) := by decide
    rw [hXeq] at hv ⊢
    rcases Finset.mem_insert.mp hv with rfl | hv1
    · exact by decide
    · rw [Finset.mem_singleton.mp hv1]; exact by decide
  · refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
    unfold PruneWordBound pruneWorkSpace rfCcap rfHParam rfPruneWorkAddr
    decide
  · unfold RemoveFakeDisjoint DisjointRange removeFakeWorkSpace pruneWorkSpace rfHParam rfCcap
    decide

end MinCostFlow.ExpanderDecomp
