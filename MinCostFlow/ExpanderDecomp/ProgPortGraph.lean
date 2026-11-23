module

public import MinCostFlow.ExpanderDecomp.ProgPortGraphBase
public import MinCostFlow.ExpanderDecomp.ProgPortGraphStages
import MinCostFlow.ExpanderDecomp.ProgPortGraphCloud

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Port Graph Word-RAM Procedure — Cost, Contract, and Specification (`ProgPortGraph`)

Completes the deterministic (`NoRand`) Word-RAM implementation `portGraphProcs` of
`portGraph cloud G X` and `portOwner G X` (`PortGraph.lean`) using `cloud` and
`cloudExpanderProcs` from `ProgCloud.lean`:
- `portGraphCost` (`O(|X| + |G.inside X| + 1)`), `portGraphContract`, `portGraph_spec`, and
  non-vacuity witness `portGraphContract_pre_example`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 2. Cost, Contract, Main Specification, and Non-Vacuity Example -/

/-- Explicit linear deterministic time bound `O(|X| + |G.inside X| + 1)` (independent of `n`). -/
def portGraphCost (k e : ℕ) : ℕ :=
  220 * k + (runnerScale explicitProgram * 760 + 1900) * e + 260

/-- Contract for `portGraphEntry`:
`args = [k, vertsAddr, e, edgesAddr, locAddr, outOwnerAddr, outGraphAddr, workAddr, h]`.
Given a strictly increasing vertex list `verts` (`|verts| = k`, `X = verts.toFinset`), the inside
edge list `inEdges = G.inside X` (`|inEdges| = e`), a pre-zeroed local-ID buffer `locAddr` of size
`n`, and a zero-heap pointer `h`:
- writes `GraphAt mem' outGraphAddr (portGraph cloud G X)` and `portOwner G X p` at `outOwnerAddr + p`
  (`p < 2 * e`);
- restores `locAddr` to all zeros and preserves all memory `< h` outside `outOwnerAddr`,
  `outGraphAddr`, and `workAddr`;
- returns `v ∈ [h, h + portGraphHeapSpace e]` with `ZeroFrom mem' v`;
- runs in `O(|X| + |G.inside X| + 1)` deterministic steps. -/
noncomputable def portGraphContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k va e ea la oa ga wa h : ℕ) (verts : List ℕ) (inEdges : List (ℕ × ℕ)),
      args = [k, va, e, ea, la, oa, ga, wa, h] ∧
      verts.length = k ∧
      verts.Pairwise (· < ·) ∧
      (∀ u ∈ verts, u < n) ∧
      inEdges.length = e ∧
      (∀ ed ∈ inEdges, ed.1 ∈ verts ∧ ed.2 ∈ verts) ∧
      ListAt mem va verts ∧
      EdgesAt mem ea inEdges ∧
      (∀ u < n, mem (la + u) = 0) ∧
      ZeroFrom mem h ∧
      PortGraphBounds w n k e va ea la oa ga wa h ∧
      PortGraphDisjoint n k e va ea la oa ga wa
  post args mem v mem' :=
    let k := args.getD 0 0
    let va := args.getD 1 0
    let e := args.getD 2 0
    let ea := args.getD 3 0
    let oa := args.getD 5 0
    let ga := args.getD 6 0
    let wa := args.getD 7 0
    let h := args.getD 8 0
    let verts := readList mem va k
    let inEdges := readEdges mem ea e
    let X := verts.toFinset
    let G_in := Graph.mk 0 inEdges
    GraphAt mem' ga (portGraph cloud G_in X) ∧
    (∀ p < 2 * e, mem' (oa + p) = portOwner G_in X p) ∧
    (∀ G : Graph, G.inside X = inEdges →
      GraphAt mem' ga (portGraph cloud G X) ∧
      (∀ p < 2 * e, mem' (oa + p) = portOwner G X p)) ∧
    h ≤ v ∧
    v ≤ h + portGraphHeapSpace e ∧
    ZeroFrom mem' v ∧
    (∀ a < h, (a < oa ∨ oa + 2 * e ≤ a) → (a < ga ∨ ga + 2 + 20 * e ≤ a) →
      (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → mem' a = mem a)
  cost args _mem :=
    portGraphCost (args.getD 0 0) (args.getD 2 0)

/-- `portGraphProcs b` meets `portGraphContract w` in `O(|X| + |G.inside X| + 1)` deterministic
steps, without scanning `range n`. -/
theorem portGraph_spec {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (portGraphProcs b)) :
    MeetsContract w p b (portGraphContract w) := by
  have hEntry : p.procs[b]? = some (portGraphEntry b) := by
    simpa [portGraphProcs] using hp 0 (by simp [portGraphProcs])
  have hp_cloud : p.HasAt (b + 1) (cloudExpanderProcs (b + 1)) := by
    intro i hi
    have h1 := hp (i + 1) (by simp [portGraphProcs]; omega)
    simpa [portGraphProcs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
  intro args mem pos ω _ hpre
  rcases hpre with ⟨n, k, va, e, ea, la, oa, ga, wa, h, verts, inEdges,
    hargs, hvlen, hsorted, hverts_lt, helen, hE_inX, hverts_at, hE_at, hloc0, hzero, hb, hd⟩
  subst hargs
  have hnd : verts.Nodup := hsorted.imp fun h1 => Nat.ne_of_lt h1
  set X := verts.toFinset
  set G_in := Graph.mk 0 inEdges
  have hinside_eq : G_in.inside X = inEdges := by
    unfold Graph.inside
    exact List.filter_eq_self.mpr fun ed hed => by
      have h12 := hE_inX ed hed
      simp [X, h12.1, h12.2]
  have he_eq : (G_in.inside X).length = e := hinside_eq ▸ helen
  have hread_verts : readList mem va k = verts := hvlen ▸ readList_eq_of_listAt hverts_at
  have hread_edges : readEdges mem ea e = inEdges := helen ▸ readEdges_eq_of_edgesAt hE_at
  rcases hb with ⟨hva_h, hea_h, hla_h, hoa_h, hga_h, hws_h, hhw, hw16⟩
  rcases hd with ⟨hd_lv, hd_le, hd_lo, hd_lg, hd_lw, hd_ov, hd_oe, hd_og, hd_ow, hd_gv, hd_ge, hd_gw, hd_wv, hd_we⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  have hb' : PortGraphBounds w n k e va ea la oa ga wa h :=
    ⟨hva_h, hea_h, hla_h, hoa_h, hga_h, hws_h, hhw, hw16⟩
  have hd' : PortGraphDisjoint n k e va ea la oa ga wa :=
    ⟨hd_lv, hd_le, hd_lo, hd_lg, hd_lw, hd_ov, hd_oe, hd_og, hd_ow, hd_gv, hd_ge, hd_gw, hd_wv, hd_we⟩
  have hrun : ∃ o st' c,
      Runs w p ω (portGraphEntry b)
        (startState [k, va, e, ea, la, oa, ga, wa, h] mem pos) o st' c ∧
      (portGraphContract w).post [k, va, e, ea, la, oa, ga, wa, h] mem o.value st'.mem ∧
      c ≤ portGraphCost k e := by
    refine runs_start_le ?_
    dsimp only [portGraphEntry, seqStmts]
    -- Setup
    refine runs_seq_triple_le (pgSetup_triple p mem pos hb') rfl ?_
    intro st0 ⟨hr0, hmem0, _⟩
    -- Stage 1: init loc & cur
    refine runs_seq_triple_le
      (pgInitLoc_triple p mem verts st0 hvlen hnd hverts_lt hverts_at hloc0 hb' hd' hr0 hmem0) rfl ?_
    intro st1 ⟨hr1, _, hpr1, hloc1, hcur1⟩
    have hE_at1 : EdgesAt st1.mem ea inEdges :=
      hE_at.congr fun a ha1 ha2 => hpr1 a
        (disjointRange_outside hd_le ha1 (by omega))
        (by rcases hd_we with h1 | h1 <;> [right; left] <;> omega)
    -- Stage 2: orig edges, portOwner, degrees
    refine runs_seq_triple_le
      (pgOrigAndDeg_triple p st1.mem verts inEdges st1 hvlen hnd helen hE_inX hverts_lt
        hE_at1 hloc1 hcur1 hb' hd' hr1 rfl) rfl ?_
    intro st2 ⟨hr2, _, hfr2, hown2, horig2, hdeg2⟩
    -- Stage 3: prefix sum
    refine runs_seq_triple_le
      (pgPrefixSum_triple p st2.mem verts G_in st2 hvlen hnd he_eq hdeg2 hb' hr2 rfl) rfl ?_
    intro st3 ⟨hr3, _, hfr3, hoff3, hcur3⟩
    have hloc3 : ∀ u < n, st3.mem (la + u) = if u ∈ verts then verts.idxOf u + 1 else 0 := fun u hu => by
      rw [hfr3 (la + u) (by rcases hd_lw with h1 | h1 <;> [left; right] <;> omega),
        hfr2 (la + u) (disjointRange_outside hd_lo.symm (by omega) (by omega))
          (by rcases hd_lg with h1 | h1 <;> [left; right] <;> omega)
          (by rcases hd_lw with h1 | h1 <;> [left; right] <;> omega)]
      exact hloc1 u hu
    have hown3 : ∀ q < 2 * e, st3.mem (oa + q) = portOwner G_in X q := fun q hq => by
      rw [hfr3 (oa + q) (by rcases hd_ow with h1 | h1 <;> [left; right] <;> omega)]
      exact hown2 q hq
    -- Stage 4: scatter ports
    refine runs_seq_triple_le
      (pgScatterPorts_triple p st3.mem verts G_in st3 hvlen hnd he_eq hverts_lt hloc3 hown3 hcur3
        hb' hd' hr3 rfl) rfl ?_
    intro st4 ⟨hr4, _, hfr4, hpts4⟩
    have hoff4 : ∀ i ≤ k, st4.mem (wa + 1 + i) = cloudOff verts G_in X i := fun i hi => by
      rw [hfr4 (wa + 1 + i) (Or.inl (by omega))]
      exact hoff3 i hi
    have horig4 : EdgesAt st4.mem (ga + 2) (origPortEdges e) :=
      horig2.congr fun a ha1 ha2 => by
        have horig_len : (origPortEdges e).length = e := by simp [origPortEdges]
        rw [hfr4 a (by rcases hd_gw with h1 | h1 <;> [left; right] <;> omega),
          hfr3 a (by rcases hd_gw with h1 | h1 <;> [left; right] <;> omega)]
    have hzero4 : ZeroFrom st4.mem h := fun a ha => by
      rw [hfr4 a (Or.inr (by omega)), hfr3 a (Or.inr (by omega)),
        hfr2 a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
        hpr1 a (Or.inr (by omega)) (Or.inr (by omega))]
      exact hzero a ha
    -- Stage 5: cloud expander calls & edge mapping
    refine runs_seq_triple_le
      (pgCloudLoop_triple p st4.mem verts G_in st4 hp_cloud hvlen hsorted he_eq hoff4 hpts4
        horig4 hzero4 hb' hd' hr4 rfl) rfl ?_
    intro st5 ⟨hr5, hh_le5, hh_ub5, hz5, hGA5, hfr5⟩
    have hverts_at5 : ListAt st5.mem va verts := fun i hi => by
      have hi_k : i < k := hvlen ▸ hi
      rw [hfr5 (va + i) (by omega)
          (by rcases hd_gv with h1 | h1 <;> [right; left] <;> omega)
          (by rcases hd_wv with h1 | h1 <;> [right; left] <;> omega),
        hfr4 (va + i) (by rcases hd_wv with h1 | h1 <;> [right; left] <;> omega),
        hfr3 (va + i) (by rcases hd_wv with h1 | h1 <;> [right; left] <;> omega),
        hfr2 (va + i) (by rcases hd_ov with h1 | h1 <;> [right; left] <;> omega)
          (by rcases hd_gv with h1 | h1 <;> [right; left] <;> omega)
          (by rcases hd_wv with h1 | h1 <;> [right; left] <;> omega),
        hpr1 (va + i) (disjointRange_outside hd_lv (by omega) (by omega))
          (by rcases hd_wv with h1 | h1 <;> [right; left] <;> omega)]
      exact hverts_at i hi
    -- Stage 6: clear locAddr
    refine runs_seq_triple_le
      (pgClearLoc_triple (hCur := st5.regs pgHCur) p st5.mem verts st5 hvlen hverts_lt hverts_at5
        hb' hd_lv hr5 rfl rfl) rfl ?_
    intro st6 ⟨hr6, hhcur6, _, hfr6, hpt6, hclr6⟩
    -- Return hCur
    refine runs_ret_le (Expr.eval_reg_of_eq hhcur6) ?_ ?_
    · dsimp only [portGraphContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hread_verts, hread_edges]
      have hGA6 : GraphAt st6.mem ga (portGraph cloud G_in X) := by
        have hm_le : (portGraph cloud G_in X).m ≤ 10 * e := he_eq ▸ portGraph_cloud_m_le G_in X
        have hlen_enc : (portGraph cloud G_in X).encode.length = 2 + 2 * (portGraph cloud G_in X).m :=
          graph_encode_length _
        intro i hi
        rw [hfr6 (ga + i) (by rcases hd_lg with h1 | h1 <;> [right; left] <;> omega)]
        exact hGA5 i hi
      have hown6 : ∀ q < 2 * e, st6.mem (oa + q) = portOwner G_in X q := fun q hq => by
        rw [hfr6 (oa + q) (by rcases hd_lo with h1 | h1 <;> [right; left] <;> omega),
          hfr5 (oa + q) (by omega)
            (by rcases hd_og with h1 | h1 <;> [left; right] <;> omega)
            (by rcases hd_ow with h1 | h1 <;> [left; right] <;> omega),
          hfr4 (oa + q) (by rcases hd_ow with h1 | h1 <;> [left; right] <;> omega)]
        exact hown3 q hq
      refine ⟨hGA6, hown6, fun G hG => ?_, hh_le5, hh_ub5, ?_, ?_⟩
      · have hG' : G.inside X = G_in.inside X := hG.trans hinside_eq.symm
        exact ⟨portGraph_congr_inside cloud hG' ▸ hGA6,
          fun q hq => (portOwner_congr_inside hG' q).symm ▸ hown6 q hq⟩
      · intro a ha
        rw [hfr6 a (Or.inr (by omega))]
        exact hz5 a ha
      · intro a ha_h ha_o ha_g ha_w
        by_cases hal : a < la ∨ la + n ≤ a
        · rw [hfr6 a hal, hfr5 a ha_h ha_g ha_w,
            hfr4 a (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
            hfr3 a (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
            hfr2 a ha_o (by rcases ha_g with h1 | h1 <;> [left; right] <;> omega)
              (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
            hpr1 a hal (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega)]
        · have hu_lt : a - la < n := by omega
          have ha_eq : la + (a - la) = a := by omega
          by_cases hu_mem : (a - la) ∈ verts
          · rw [← ha_eq, hclr6 (a - la) hu_mem, hloc0 (a - la) hu_lt]
          · have hnot : ∀ u ∈ verts, a ≠ la + u := fun u hu heq =>
              hu_mem ((by omega : a - la = u) ▸ hu)
            rw [hpt6 a hnot, hfr5 a ha_h ha_g ha_w,
              hfr4 a (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
              hfr3 a (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
              hfr2 a ha_o (by rcases ha_g with h1 | h1 <;> [left; right] <;> omega)
                (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
              ← ha_eq, hloc1 (a - la) hu_lt,
              ite_eq_right_iff.mpr (fun h1 => absurd h1 hu_mem), hloc0 (a - la) hu_lt]
    · dsimp only [portGraphCost, Expr.size]
      have hmul : (runnerScale explicitProgram * 380 + 800) * (2 * e) =
          (runnerScale explicitProgram * 760 + 1600) * e := by ring
      rw [hmul]
      have hmul2 : (runnerScale explicitProgram * 760 + 1900) * e =
          (runnerScale explicitProgram * 760 + 1600) * e + 300 * e := by ring
      rw [hmul2]
      omega
  rcases hrun with ⟨o, st', c, hr, hpost, hcost⟩
  exact ⟨portGraphEntry b, hEntry, o, st', c, hr, hpost, by simpa [portGraphContract] using hcost⟩

/-- Non-vacuity witness for `portGraphContract 20` with a degree-2 vertex exercising the cloud
expander call. -/
theorem portGraphContract_pre_example :
    ∃ args mem, (∀ a ∈ args, a < 2 ^ 20) ∧ (portGraphContract 20).pre args mem := by
  let verts : List ℕ := [1, 3, 5]
  let inEdges : List (ℕ × ℕ) := [(1, 3), (3, 5)]
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 1 else if a = 1 then 3 else if a = 2 then 5
    else if a = 10 then 1 else if a = 11 then 3
    else if a = 12 then 3 else if a = 13 then 5
    else 0
  let args : List ℕ := [3, 0, 2, 10, 20, 40, 60, 120, 300]
  refine ⟨args, mem, by decide, ?_⟩
  refine ⟨6, 3, 0, 2, 10, 20, 40, 60, 120, 300, verts, inEdges,
    rfl, rfl, by decide, by decide, rfl, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rcases i with _ | _ | _ | i <;> simp [verts, mem] at hi ⊢; omega
  · intro j hj; rcases j with _ | _ | j <;> simp [inEdges, mem] at hj ⊢
  · intro u hu; simp only [mem]; split_ifs <;> omega
  · intro a ha; simp only [mem]; split_ifs <;> omega
  · unfold PortGraphBounds portGraphWorkSpace portGraphHeapSpace; decide
  · unfold PortGraphDisjoint portGraphWorkSpace DisjointRange; decide

end MinCostFlow.ExpanderDecomp
