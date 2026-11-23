module

public import MinCostFlow.HierPaths.BuildTopCloud
public import MinCostFlow.ExpanderDecomp.ProgPortGraphBase
public import MinCostFlow.ExpanderDecomp.ProgPortGraphStages

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Zero-heap compact port graph procedure

Reuses stages 1–4 and 6 of `ExpanderDecomp.ProgPortGraph` verbatim, replacing
only the Stage 5 cloud expander call with `buildTopCloud` (`BuildTopCloud.lean`).
Because `buildTopCloud` writes `(cloud s).encode` directly into the existing
workspace buffer and returns the heap pointer unchanged, the compact port graph
procedure uses zero heap (`v = h`) and runs in linear time `O(k + e)`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander
  MinCostFlow.ExpanderDecomp MinCostFlow.ExplicitExpander

/-- Stage 5 with a relocatable cloud expander procedure at index `cloudIdx`. -/
def buildTopCompactCloudLoopStmt (cloudIdx : ℕ) : Stmt :=
  seqStmts [
    .assign pgOutM (.reg pgE),
    .assign pgHCur (.reg pgH),
    .assign pgI (.const 0),
    .loop (.bin .lt (.reg pgI) (.reg pgK)) (
      seqStmts [
        .assign pgTmp1 (.load (.bin .add (.reg pgOff) (.reg pgI))),
        .assign pgTmp2 (.bin .sub
          (.load (.bin .add (.bin .add (.reg pgOff) (.reg pgI)) (.const 1)))
          (.reg pgTmp1)),
        .cond (.bin .lt (.const 1) (.reg pgTmp2))
          (seqStmts [
            .store (.reg pgWork) (.reg pgTmp2),
            .call pgHCur cloudIdx [.reg pgWork, .reg pgCloudBuf, .reg pgHCur],
            .assign pgCM (.load (.bin .add (.reg pgCloudBuf) (.const 1))),
            pgMapCloudEdgesStmt
          ])
          .nop,
        .assign pgI (.bin .add (.reg pgI) (.const 1))
      ]
    ),
    .store (.reg pgOutGraph) (.bin .mul (.const 2) (.reg pgE)),
    .store (.bin .add (.reg pgOutGraph) (.const 1)) (.reg pgOutM)
  ]

/-- Compact port graph entry procedure calling `buildTopCloud` at `cloudIdx`. -/
def buildTopPortCompactEntry (cloudIdx : ℕ) : Stmt :=
  seqStmts [
    pgSetupStmt,
    pgInitLocStmt,
    pgOrigAndDegStmt,
    pgPrefixSumStmt,
    pgScatterPortsStmt,
    buildTopCompactCloudLoopStmt cloudIdx,
    pgClearLocStmt,
    .ret (.reg pgHCur)
  ]

theorem buildTopPortCompactEntry_noRand (cloudIdx : ℕ) :
    (buildTopPortCompactEntry cloudIdx).NoRand := by
  simp [buildTopPortCompactEntry, buildTopCompactCloudLoopStmt,
    pgSetupStmt, pgInitLocStmt, pgOrigAndDegStmt, pgPrefixSumStmt,
    pgScatterPortsStmt, pgMapCloudEdgesStmt, pgClearLocStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

/-- Linear deterministic time bound `O(|X| + |G.inside X| + 1)` without runner overhead. -/
def buildTopPortCompactCost (k e : ℕ) : ℕ :=
  220 * k + 2200 * e + 260

/-- Contract for `buildTopPortCompactEntry`: identical precondition to `portGraphContract`,
but zero heap advance (`v = h`) and `ZeroFrom mem' h`. -/
noncomputable def buildTopPortCompactContract (w : ℕ) : Contract where
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
    v = h ∧
    ZeroFrom mem' h ∧
    (∀ a < h, (a < oa ∨ oa + 2 * e ≤ a) → (a < ga ∨ ga + 2 + 20 * e ≤ a) →
      (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → mem' a = mem a)
  cost args _mem :=
    buildTopPortCompactCost (args.getD 0 0) (args.getD 2 0)

private lemma cloudEdgesFor_eq_map_cloud' {G : Graph} {X : Finset ℕ} {v : ℕ}
    (hs : 2 ≤ (cloudPortsList G X v).length) :
    cloudEdgesFor cloud G X v =
      (cloud (cloudPortsList G X v).length).edges.map fun ed =>
        ((cloudPortsList G X v).getD ed.1 0, (cloudPortsList G X v).getD ed.2 0) := by
  unfold cloudEdgesFor
  dsimp only
  rw [ite_eq_left_iff.mpr (fun h => absurd hs h)]
  congr 1
  exact List.filter_eq_self.mpr fun e he => decide_eq_true ((cloud_spec hs).2.2.1 e he)

private lemma mapCloudEdges_triple {w n k e va ea la oa ga wa h : ℕ}
    {i sStart s hCur : ℕ}
    (p : Program) (mem : ℕ → ℕ) (pts : List ℕ) (prevEdges : List (ℕ × ℕ)) (st₀ : State)
    (hs : 2 ≤ s) (hpts_len : pts.length = s)
    (hpts_at : ListAt mem (wa + 2 * k + 2 + sStart) pts)
    (hcloud_at : EdgesAt mem (wa + 2 * k + 2 + 2 * e + 2) (cloud s).edges)
    (hprev_at : EdgesAt mem (ga + 2) prevEdges)
    (hsStart_le : sStart + s ≤ 2 * e)
    (hprev_le : prevEdges.length + (cloud s).m ≤ 10 * e)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h)
    (hd : PortGraphDisjoint n k e va ea la oa ga wa)
    (hregs : PgRegs k va e ea la oa ga wa h st₀)
    (hri : st₀.regs pgI = i) (hrs : st₀.regs pgTmp1 = sStart)
    (hrcm : st₀.regs pgCM = (cloud s).m) (hroutM : st₀.regs pgOutM = prevEdges.length)
    (hrhcur : st₀.regs pgHCur = hCur) (hmem : st₀.mem = mem) :
    let mapped := (cloud s).edges.map fun ed => (pts.getD ed.1 0, pts.getD ed.2 0)
    Triple w p (fun st => st = st₀) pgMapCloudEdgesStmt
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧
        st'.regs pgI = i ∧ st'.regs pgHCur = hCur ∧
        st'.regs pgOutM = prevEdges.length + (cloud s).m ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem (ga + 2) (ga + 2 + 20 * e) ∧
        EdgesAt st'.mem (ga + 2) (prevEdges ++ mapped))
      (fun _ => 80 * (cloud s).m + 20) := by
  intro mapped
  rcases hb with ⟨_, _, _, _, hga_h, hws_h, hhw, hw16⟩
  rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, hd_gw, _, _⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  have hcm_le : 2 * (cloud s).m ≤ 9 * s := cloud_m_le hs
  have hcloud_val := (cloud_spec hs).2.1
  have hcloud_n := (cloud_spec hs).1
  let portsAddr := wa + 2 * k + 2
  let cloudBufAddr := wa + 2 * k + 2 + 2 * e
  let Inv : ℕ → State → Prop := fun j st =>
    PgRegs k va e ea la oa ga wa h st ∧
    st.regs pgI = i ∧ st.regs pgTmp1 = sStart ∧ st.regs pgCM = (cloud s).m ∧
    st.regs pgHCur = hCur ∧ st.regs pgJ = j ∧ st.regs pgOutM = prevEdges.length + j ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem (ga + 2) (ga + 2 + 20 * e) ∧
    EdgesAt st.mem (ga + 2) (prevEdges ++ mapped.take j)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := pgJ)
    (lo := .const 0) (hi := .reg pgCM)
    (body := seqStmts [
      .assign pgU (.load (.bin .add (.bin .add (.reg pgCloudBuf) (.const 2)) (.bin .mul (.const 2) (.reg pgJ)))),
      .assign pgV (.load (.bin .add (.bin .add (.reg pgCloudBuf) (.const 3)) (.bin .mul (.const 2) (.reg pgJ)))),
      .assign pgPA (.load (.bin .add (.bin .add (.reg pgPorts) (.reg pgTmp1)) (.reg pgU))),
      .assign pgPB (.load (.bin .add (.bin .add (.reg pgPorts) (.reg pgTmp1)) (.reg pgV))),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 2)) (.bin .mul (.const 2) (.reg pgOutM))) (.reg pgPA),
      .store (.bin .add (.bin .add (.reg pgOutGraph) (.const 3)) (.bin .mul (.const 2) (.reg pgOutM))) (.reg pgPB),
      .assign pgOutM (.bin .add (.reg pgOutM) (.const 1))])
    (P := fun st => st = st₀) (Inv := Inv) 68 0 (cloud s).m (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st hs0 => by
      subst hs0
      refine ⟨Expr.eval_const (by omega), pgRegs_update_ge (r := pgJ) (by decide) hregs,
        by dsimp only; rw [Function.update_of_ne (by decide), hri],
        by dsimp only; rw [Function.update_of_ne (by decide), hrs],
        by dsimp only; rw [Function.update_of_ne (by decide), hrcm],
        by dsimp only; rw [Function.update_of_ne (by decide), hrhcur],
        by simp, by dsimp only; rw [Function.update_of_ne (by decide), hroutM, add_zero],
        rfl, hmem ▸ memFrame_refl _ _ _, by simpa [hmem] using hprev_at⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.2.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.2.1)
    (fun j _ hjlt => by
      intro st ω ⟨hr, hri', hrs', hrcm', hrhcur', hrj, hroutM', hpos, hfr, hEprev⟩
      have hj_len : j < (cloud s).edges.length := hjlt
      set ed := (cloud s).edges[j]'hj_len
      have hed_lt := hcloud_val ed (List.getElem_mem hj_len)
      rw [hcloud_n] at hed_lt
      have hu_pts : ed.1 < pts.length := hpts_len.symm ▸ hed_lt.1
      have hv_pts : ed.2 < pts.length := hpts_len.symm ▸ hed_lt.2
      set pa := pts.getD ed.1 0
      set pb := pts.getD ed.2 0
      have hmem_u : st.mem (cloudBufAddr + 2 + 2 * j) = ed.1 := by
        rw [hfr _ (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega)]
        exact (hcloud_at j hj_len).1
      have hmem_v : st.mem (cloudBufAddr + 3 + 2 * j) = ed.2 := by
        rw [hfr _ (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega),
          show cloudBufAddr + 3 + 2 * j = cloudBufAddr + 2 + 2 * j + 1 by omega]
        exact (hcloud_at j hj_len).2
      have hmem_pa : st.mem (portsAddr + sStart + ed.1) = pa := by
        rw [hfr _ (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega),
          show pa = pts[ed.1]'hu_pts from List.getD_eq_getElem pts 0 hu_pts]
        exact hpts_at ed.1 hu_pts
      have hmem_pb : st.mem (portsAddr + sStart + ed.2) = pb := by
        rw [hfr _ (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega),
          show pb = pts[ed.2]'hv_pts from List.getD_eq_getElem pts 0 hv_pts]
        exact hpts_at ed.2 hv_pts
      set curM := prevEdges.length + j
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := ed.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr.r_cloudBuf) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hrj) (by omega)) (by omega))
          hmem_u) ?_
      refine runs_seq_assign_le (v := ed.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_add
            (Expr.eval_reg_of_eq (v := cloudBufAddr) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_cloudBuf]))
            (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hrj])) (by omega))
            (by omega)) hmem_v) ?_
      refine runs_seq_assign_le (v := pa)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := portsAddr)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_ports]))
              (Expr.eval_reg_of_eq (v := sStart)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrs'])) (by omega))
            (Expr.eval_reg_of_eq (v := ed.1)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega))
          hmem_pa) ?_
      refine runs_seq_assign_le (v := pb)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := portsAddr)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                  Function.update_of_ne (by decide), hr.r_ports]))
              (Expr.eval_reg_of_eq (v := sStart)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                  Function.update_of_ne (by decide), hrs'])) (by omega))
            (Expr.eval_reg_of_eq (v := ed.2)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega))
          hmem_pb) ?_
      refine runs_seq_store_le (x := ga + 2 + 2 * curM) (v := pa)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ga)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_outGraph]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := curM)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), Function.update_of_ne (by decide), hroutM'])) (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := pa) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) ?_
      refine runs_seq_store_le (x := ga + 3 + 2 * curM) (v := pb)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ga)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_outGraph]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := curM)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), Function.update_of_ne (by decide), hroutM'])) (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := pb) (by simp)) ?_
      refine runs_assign_le (v := curM + 1)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := curM)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), Function.update_of_ne (by decide), hroutM']))
          (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨pgRegs_update_ge (r := pgJ) (by decide)
          (pgRegs_update_ge (r := pgOutM) (by decide)
            (pgRegs_update_mem (pgRegs_update_mem
              (pgRegs_update_ge (r := pgPB) (by decide)
                (pgRegs_update_ge (r := pgPA) (by decide)
                  (pgRegs_update_ge (r := pgV) (by decide)
                    (pgRegs_update_ge (r := pgU) (by decide) hr))))))),
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hri'],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrs'],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrcm'],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrhcur'],
        by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]; omega,
        hpos,
        memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
          (memFrame_update (by omega) (by omega))), ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrj]⟩
      intro t ht
      dsimp only
      have hmap_len : mapped.length = (cloud s).m := by simp [mapped, Graph.m]
      have htake_succ : mapped.take (j + 1) = mapped.take j ++ [(pa, pb)] := by
        have hj_m : j < mapped.length := hmap_len.symm ▸ hjlt
        rw [List.take_succ_eq_append_getElem hj_m]
        simp [mapped, pa, pb, ed]
      have hlen_pre : (prevEdges ++ mapped.take j).length = curM := by
        rw [List.length_append, List.length_take, hmap_len, Nat.min_eq_left (by omega)]
      have ht' : t < curM + 1 := by
        rw [htake_succ, ← List.append_assoc, List.length_append, hlen_pre, List.length_singleton] at ht
        exact ht
      by_cases hteq : t = curM
      · subst hteq
        have hget : (prevEdges ++ mapped.take (j + 1))[curM]'ht = (pa, pb) := by
          have h1 : prevEdges ++ mapped.take (j + 1) = (prevEdges ++ mapped.take j) ++ [(pa, pb)] := by
            rw [htake_succ, List.append_assoc]
          simp only [h1]
          rw [List.getElem_append_right (by omega)]
          simp [hlen_pre]
        rw [hget]
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [show ga + 2 + 2 * curM + 1 = ga + 3 + 2 * curM by omega, Function.update_self]
      · have htlt : t < (prevEdges ++ mapped.take j).length := by omega
        have hget : (prevEdges ++ mapped.take (j + 1))[t]'ht =
            (prevEdges ++ mapped.take j)[t]'htlt := by
          have h1 : prevEdges ++ mapped.take (j + 1) = (prevEdges ++ mapped.take j) ++ [(pa, pb)] := by
            rw [htake_succ, List.append_assoc]
          simp only [h1]
          exact List.getElem_append_left htlt
        rw [hget]
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (hEprev t htlt).1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (hEprev t htlt).2)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, hri', _, _, hrhcur', _, hroutM', hpos', hfr', hEout'⟩
    have hmap_len : mapped.length = (cloud s).m := by simp [mapped, Graph.m]
    rw [← hmap_len, List.take_length] at hEout'
    exact ⟨hr, hri', hrhcur', hroutM', hpos', hfr', hEout'⟩
  · exact False.elim hq

private lemma compactCloudLoop_triple {w n k e va ea la oa ga wa h cloudIdx : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (G : Graph) (st₀ : State)
    (hp_cloud : p.procs[cloudIdx]? = some buildTopCloud)
    (hvlen : verts.length = k) (hsorted : verts.Pairwise (· < ·))
    (he_eq : (G.inside verts.toFinset).length = e)
    (hoff_at : ∀ i ≤ k, mem (wa + 1 + i) = cloudOff verts G verts.toFinset i)
    (hpts_at : ∀ i < k, ListAt mem (wa + 2 * k + 2 + cloudOff verts G verts.toFinset i)
      (cloudPortsList G verts.toFinset (verts.getD i 0)))
    (horig_at : EdgesAt mem (ga + 2) (origPortEdges e))
    (hzero : ZeroFrom mem h)
    (hb : PortGraphBounds w n k e va ea la oa ga wa h)
    (hd : PortGraphDisjoint n k e va ea la oa ga wa)
    (hregs : PgRegs k va e ea la oa ga wa h st₀) (hmem : st₀.mem = mem) :
    let X := verts.toFinset
    Triple w p (fun st => st = st₀) (buildTopCompactCloudLoopStmt cloudIdx)
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧
        st'.regs pgHCur = h ∧
        ZeroFrom st'.mem h ∧
        GraphAt st'.mem ga (portGraph cloud G X) ∧
        (∀ a < h, (a < ga ∨ ga + 2 + 20 * e ≤ a) →
          (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → st'.mem a = mem a))
      (fun _ => 60 * k + 850 * (2 * e) + 60) := by
  intro X
  have hnd : verts.Nodup := hsorted.imp fun h1 => Nat.ne_of_lt h1
  have hSpec_cloud := buildTopCloud_meetsContract (w := w) hp_cloud
  rcases hb with ⟨hva_h, hea_h, hla_h, hoa_h, hga_h, hws_h, hhw, hw16⟩
  rcases hd with ⟨hd_lv, hd_le, hd_lo, hd_lg, hd_lw, hd_ov, hd_oe, hd_og, hd_ow, hd_gv, hd_ge, hd_gw, hd_wv, hd_we⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  let offAddr := wa + 1
  let portsAddr := wa + 2 * k + 2
  let cloudBufAddr := wa + 2 * k + 2 + 2 * e
  let Inv : ℕ → State → Prop := fun i st =>
    i ≤ k ∧
    PgRegs k va e ea la oa ga wa h st ∧
    st.regs pgI = i ∧
    st.regs pgOutM = e + (allCloudEdgesPrefix verts G X i).length ∧
    st.regs pgHCur = h ∧
    ZeroFrom st.mem h ∧
    (∀ t ≤ k, st.mem (offAddr + t) = cloudOff verts G X t) ∧
    (∀ t < k, ListAt st.mem (portsAddr + cloudOff verts G X t)
      (cloudPortsList G X (verts.getD t 0))) ∧
    EdgesAt st.mem (ga + 2) (origPortEdges e ++ allCloudEdgesPrefix verts G X i) ∧
    (∀ a < h, (a < ga ∨ ga + 2 + 20 * e ≤ a) →
      (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → st.mem a = mem a)
  let T_rem : ℕ → ℕ := fun i => 60 * (k - i) + 850 * (2 * e - cloudOff verts G X i) + 10
  have hloop_ind : ∀ rem i st ω, k - i = rem → Inv i st →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg pgI) (.reg pgK)) (
            seqStmts [
              .assign pgTmp1 (.load (.bin .add (.reg pgOff) (.reg pgI))),
              .assign pgTmp2 (.bin .sub
                (.load (.bin .add (.bin .add (.reg pgOff) (.reg pgI)) (.const 1)))
                (.reg pgTmp1)),
              .cond (.bin .lt (.const 1) (.reg pgTmp2))
                (seqStmts [
                  .store (.reg pgWork) (.reg pgTmp2),
                  .call pgHCur cloudIdx [.reg pgWork, .reg pgCloudBuf, .reg pgHCur],
                  .assign pgCM (.load (.bin .add (.reg pgCloudBuf) (.const 1))),
                  pgMapCloudEdgesStmt
                ])
                .nop,
              .assign pgI (.bin .add (.reg pgI) (.const 1))]))
          st .normal st' c ∧
        Inv k st' ∧ c ≤ T_rem i := by
    intro rem
    induction rem with
    | zero =>
      intro i st ω hrem hInv
      have hik : i = k := by have := hInv.1; omega
      subst hik
      have hcond : (Expr.bin .lt (.reg pgI) (.reg pgK)).eval w st = some 0 := by
        have h1 := hInv.2.1.r_k; have h2 := hInv.2.2.1
        simp [Expr.eval, BinOp.eval, h1, h2]
      exact ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, by simp [Expr.size]⟩), hInv,
        by dsimp only [T_rem]; omega⟩
    | succ rem ih =>
      intro i st ω hrem hInv
      rcases hInv with ⟨hik, hr, hi, houtM, hhcur_eq, hz, hoff, hpts, hE, hfr⟩
      have hilt : i < k := by omega
      have hi_len : i < verts.length := hvlen.symm ▸ hilt
      set sStart := cloudOff verts G X i
      set sEnd := cloudOff verts G X (i + 1)
      set pts := cloudPortsList G X (verts.getD i 0)
      set s := pts.length
      have hsEnd_eq : sEnd = sStart + s := cloudOff_succ verts G X i
      have hsEnd_le : sEnd ≤ 2 * e := by
        rw [← he_eq]; exact cloudOff_le_two_mul_e hnd G (by omega)
      have hcond : (Expr.bin .lt (.reg pgI) (.reg pgK)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, hr.r_k, hi, hilt, show 1 < 2 ^ w by omega]
      have hstep : ∃ o st_next c_body,
          Runs w p ω
            (seqStmts [
              .assign pgTmp1 (.load (.bin .add (.reg pgOff) (.reg pgI))),
              .assign pgTmp2 (.bin .sub
                (.load (.bin .add (.bin .add (.reg pgOff) (.reg pgI)) (.const 1)))
                (.reg pgTmp1)),
              .cond (.bin .lt (.const 1) (.reg pgTmp2))
                (seqStmts [
                  .store (.reg pgWork) (.reg pgTmp2),
                  .call pgHCur cloudIdx [.reg pgWork, .reg pgCloudBuf, .reg pgHCur],
                  .assign pgCM (.load (.bin .add (.reg pgCloudBuf) (.const 1))),
                  pgMapCloudEdgesStmt
                ])
                .nop,
              .assign pgI (.bin .add (.reg pgI) (.const 1))])
            st o st_next c_body ∧
          (o = .normal ∧ Inv (i + 1) st_next) ∧
          c_body ≤ 50 + 850 * s := by
        refine runs_start_le ?_
        dsimp only [seqStmts]
        have hmem_s1 : st.mem (offAddr + i) = sStart := hoff i (by omega)
        have hmem_s2 : st.mem (offAddr + i + 1) = sEnd := by
          rw [show offAddr + i + 1 = offAddr + (i + 1) by omega]; exact hoff (i + 1) (by omega)
        refine runs_seq_assign_le (v := sStart)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hr.r_off) (Expr.eval_reg_of_eq hi) (by omega))
            hmem_s1) ?_
        refine runs_seq_assign_le (v := s)
          (Expr.eval_eq_of_eq
            (Expr.eval_sub
              (Expr.eval_load_of_eq
                (Expr.eval_add
                  (Expr.eval_add
                    (Expr.eval_reg_of_eq (v := offAddr)
                      (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_off]))
                    (Expr.eval_reg_of_eq (v := i)
                      (by dsimp only; rw [Function.update_of_ne (by decide), hi])) (by omega))
                  (Expr.eval_const (by omega)) (by omega))
                hmem_s2)
              (Expr.eval_reg_of_eq (v := sStart) (by simp))
              (by omega)) (by omega)) ?_
        refine runs_seq_cond_le (v := if 1 < s then 1 else 0)
          (Expr.eval_lt_op (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := s) (by simp)) (by omega))
          (fun hs_gt1_ne => ?_) (fun hs_gt1_0 => ?_)
        · have hs2 : 2 ≤ s := by
            by_contra hlt
            have hnot : ¬ (1 < s) := by omega
            simp [hnot] at hs_gt1_ne
          have he1 : 1 ≤ e := by omega
          have he4 : e ≤ e ^ 4 := Nat.le_self_pow (by decide : 4 ≠ 0) e
          have h16s : 16 * s + 48 < 2 ^ w := by
            have h1 : 32 * e + 48 < 41600 * e ^ 4 + 4 := by omega
            omega
          have hr_b : PgRegs k va e ea la oa ga wa h
              { st with regs := Function.update (Function.update st.regs pgTmp1 sStart) pgTmp2 s } :=
            pgRegs_update_ge (r := pgTmp2) (by decide) (pgRegs_update_ge (r := pgTmp1) (by decide) hr)
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_le (x := wa) (v := s)
            (Expr.eval_reg_of_eq hr_b.r_work)
            (Expr.eval_reg_of_eq (v := s) (by simp)) ?_
          let st_c0 : State :=
            { mem := Function.update st.mem wa s,
              regs := Function.update (Function.update st.regs pgTmp1 sStart) pgTmp2 s,
              pos := st.pos }
          have hcloud_pre : (buildTopCloudContract w).pre [wa, cloudBufAddr, h] st_c0.mem :=
            ⟨wa, cloudBufAddr, h, s, rfl, by simp [st_c0], hs2, by omega, h16s⟩
          have hcloud_words : ∀ a ∈ ([wa, cloudBufAddr, h] : List ℕ), a < 2 ^ w := by
            intro a ha
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl <;> omega
          have hE_cloud : evalArgs w st_c0 [.reg pgWork, .reg pgCloudBuf, .reg pgHCur] =
              some [wa, cloudBufAddr, h] := by
            have h1 : st_c0.regs pgWork = wa := hr_b.r_work
            have h2 : st_c0.regs pgCloudBuf = cloudBufAddr := hr_b.r_cloudBuf
            have h3 : st_c0.regs pgHCur = h := by
              dsimp only [st_c0]
              rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hhcur_eq]
            simp [evalArgs, Expr.eval, h1, h2, h3]
          refine runs_seq_assoc_le ?_
          refine runs_seq_call_le hSpec_cloud hE_cloud hcloud_words hcloud_pre ?_
          intro hNext mem1 pos1 hpost1
          dsimp only [buildTopCloudContract] at hpost1
          simp only [List.getD_cons_zero, List.getD_cons_succ, Function.update_self] at hpost1
          rcases hpost1 with ⟨hhNext_eq, hGA1, hfr1⟩
          subst hNext
          have hEA1 : EdgesAt mem1 (cloudBufAddr + 2) (cloud s).edges := graphAt_to_edgesAt hGA1
          have hcm_mem : mem1 (cloudBufAddr + 1) = (cloud s).m := graphAt_m hGA1
          let st_c1 : State :=
            { mem := mem1, regs := Function.update st_c0.regs pgHCur h, pos := pos1 }
          refine runs_seq_assoc_le ?_
          refine runs_seq_assign_le (v := (cloud s).m)
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_reg_of_eq (v := cloudBufAddr)
                  (by dsimp only [st_c1]; rw [Function.update_of_ne (by decide)]; exact hr_b.r_cloudBuf))
                (Expr.eval_const (by omega)) (by omega))
              hcm_mem) ?_
          let st_c2 : State :=
            { mem := mem1, regs := Function.update st_c1.regs pgCM (cloud s).m, pos := pos1 }
          have hpts_i1 : ListAt mem1 (portsAddr + sStart) pts := fun t ht => by
            rw [hfr1 (portsAddr + sStart + t) (Or.inl (by omega)),
              Function.update_of_ne (by omega)]
            exact hpts i hilt t ht
          have hE_prev1 : EdgesAt mem1 (ga + 2) (origPortEdges e ++ allCloudEdgesPrefix verts G X i) := by
            intro t ht
            have hlen_pre : (origPortEdges e ++ allCloudEdgesPrefix verts G X i).length ≤ 10 * e := by
              rw [List.length_append, show (origPortEdges e).length = e by simp [origPortEdges]]
              have h1 : (allCloudEdgesPrefix verts G X i).length ≤ 9 * e :=
                he_eq ▸ allCloudEdgesPrefix_length_le hnd G (by omega : i ≤ verts.length)
              omega
            have hout_cb1 : ga + 2 + 2 * t < cloudBufAddr ∨ cloudBufAddr + 2 + 9 * s ≤ ga + 2 + 2 * t := by
              rcases hd_gw with h1 | h1 <;> [left; right] <;> omega
            have hout_cb2 : ga + 2 + 2 * t + 1 < cloudBufAddr ∨ cloudBufAddr + 2 + 9 * s ≤ ga + 2 + 2 * t + 1 := by
              rcases hd_gw with h1 | h1 <;> [left; right] <;> omega
            refine ⟨?_, ?_⟩
            · rw [hfr1 _ hout_cb1,
                Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega)]
              exact (hE t ht).1
            · rw [hfr1 _ hout_cb2,
                Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega)]
              exact (hE t ht).2
          have hprev_cm_le : (origPortEdges e ++ allCloudEdgesPrefix verts G X i).length + (cloud s).m ≤ 10 * e := by
            have h1 : (allCloudEdgesPrefix verts G X (i + 1)).length ≤ 9 * e :=
              he_eq ▸ allCloudEdgesPrefix_length_le hnd G (by omega : i + 1 ≤ verts.length)
            rw [allCloudEdgesPrefix_succ G X hi_len, List.length_append] at h1
            have hce_len : (cloudEdgesFor cloud G X (verts[i]'hi_len)).length = (cloud s).m := by
              rw [← List.getD_eq_getElem verts 0 hi_len, cloudEdgesFor_eq_map_cloud' hs2, List.length_map]
              rfl
            rw [List.length_append, show (origPortEdges e).length = e by simp [origPortEdges]]
            rw [hce_len] at h1; omega
          have hr_c0m : PgRegs k va e ea la oa ga wa h
              { mem := mem1, regs := st_c0.regs, pos := pos1 } :=
            ⟨hr_b.r_k, hr_b.r_verts, hr_b.r_e, hr_b.r_edges, hr_b.r_loc, hr_b.r_outOwner,
             hr_b.r_outGraph, hr_b.r_work, hr_b.r_h, hr_b.r_off, hr_b.r_cur, hr_b.r_ports,
             hr_b.r_cloudBuf⟩
          have hr_c2 : PgRegs k va e ea la oa ga wa h st_c2 :=
            pgRegs_update_ge (r := pgCM) (by decide) (pgRegs_update_ge (r := pgHCur) (by decide) hr_c0m)
          have hlen_outM : (origPortEdges e ++ allCloudEdgesPrefix verts G X i).length =
              e + (allCloudEdgesPrefix verts G X i).length := by
            rw [List.length_append]; simp [origPortEdges]
          refine runs_seq_triple_le
            (mapCloudEdges_triple (i := i) (sStart := sStart) (s := s) (hCur := h)
              p mem1 pts (origPortEdges e ++ allCloudEdgesPrefix verts G X i) st_c2
              hs2 rfl hpts_i1 hEA1 hE_prev1 (by omega) hprev_cm_le
              ⟨hva_h, hea_h, hla_h, hoa_h, hga_h, hws_h, hhw, hw16⟩
              ⟨hd_lv, hd_le, hd_lo, hd_lg, hd_lw, hd_ov, hd_oe, hd_og, hd_ow, hd_gv, hd_ge, hd_gw, hd_wv, hd_we⟩
              hr_c2
              (by dsimp only [st_c2, st_c1, st_c0]
                  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                    Function.update_of_ne (by decide), Function.update_of_ne (by decide), hi])
              (by dsimp only [st_c2, st_c1, st_c0]
                  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                    Function.update_of_ne (by decide), Function.update_self])
              (by simp [st_c2])
              (by dsimp only [st_c2, st_c1, st_c0]
                  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                    Function.update_of_ne (by decide), Function.update_of_ne (by decide), houtM, hlen_outM])
              (by dsimp only [st_c2, st_c1]; rw [Function.update_of_ne (by decide), Function.update_self])
              rfl) rfl ?_
          intro st3 ⟨hr3, hri3, hrhcur3, hroutM3, _, hfr3, hE3⟩
          refine runs_assign_le (v := i + 1)
            (Expr.eval_add (Expr.eval_reg_of_eq hri3) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
          · have hce_eq : cloudEdgesFor cloud G X (verts[i]'hi_len) =
                (cloud s).edges.map fun ed => (pts.getD ed.1 0, pts.getD ed.2 0) := by
              rw [← List.getD_eq_getElem verts 0 hi_len]
              exact cloudEdgesFor_eq_map_cloud' hs2
            refine ⟨rfl, by omega, pgRegs_update_ge (r := pgI) (by decide) hr3, by simp, ?_, ?_, ?_,
              ?_, ?_, ?_, ?_⟩
            · dsimp only
              rw [Function.update_of_ne (by decide), hroutM3, hlen_outM,
                allCloudEdgesPrefix_succ G X hi_len, List.length_append, hce_eq, List.length_map]
              change e + (allCloudEdgesPrefix verts G X i).length + (cloud s).edges.length =
                e + ((allCloudEdgesPrefix verts G X i).length + (cloud s).edges.length)
              omega
            · dsimp only; rw [Function.update_of_ne (by decide), hrhcur3]
            · intro a ha
              dsimp only at ha ⊢
              rw [hfr3 a (Or.inr (by omega)), hfr1 a (Or.inr (by omega)),
                Function.update_of_ne (by omega)]
              exact hz a ha
            · intro t ht
              dsimp only
              rw [hfr3 (offAddr + t) (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega),
                hfr1 (offAddr + t) (Or.inl (by omega)),
                Function.update_of_ne (by omega)]
              exact hoff t ht
            · intro t ht u hu
              dsimp only
              have hu_le : cloudOff verts G X t + u < 2 * e := by
                have h1 := cloudOff_succ verts G X t
                have h2 : cloudOff verts G X (t + 1) ≤ 2 * e := by
                  rw [← he_eq]; exact cloudOff_le_two_mul_e hnd G (by omega)
                omega
              rw [hfr3 (portsAddr + cloudOff verts G X t + u) (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega),
                hfr1 (portsAddr + cloudOff verts G X t + u) (Or.inl (by omega)),
                Function.update_of_ne (by omega)]
              exact hpts t ht u hu
            · dsimp only
              rw [allCloudEdgesPrefix_succ G X hi_len, ← List.append_assoc, hce_eq]
              exact hE3
            · intro a ha_h ha_g ha_w
              dsimp only
              rw [hfr3 a (by rcases ha_g with h1 | h1 <;> [left; right] <;> omega),
                hfr1 a (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
                Function.update_of_ne (by rcases ha_w with h1 | h1 <;> omega)]
              exact hfr a ha_h ha_g ha_w
          · have hcm_s : 2 * (cloud s).m ≤ 9 * s := cloud_m_le hs2
            dsimp only [buildTopCloudContract, argsSize, Expr.size, st_c0]
            simp only [List.getD_cons_zero, Function.update_self]
            omega
        · have hs_lt2 : s < 2 := by
            by_contra hge
            have hlt : 1 < s := by omega
            simp [hlt] at hs_gt1_0
          refine runs_seq_nop_le ?_
          refine runs_assign_le (v := i + 1)
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := i)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hi]))
              (Expr.eval_const (by omega)) (by omega)) ?_ ?_
          · have hce_nil : cloudEdgesFor cloud G X (verts[i]'hi_len) = [] := by
              rw [← List.getD_eq_getElem verts 0 hi_len]
              unfold cloudEdgesFor
              exact ite_eq_right_iff.mpr (fun h1 => absurd h1 (show ¬ (2 ≤ s) by omega))
            refine ⟨rfl, by omega,
              pgRegs_update_ge (r := pgI) (by decide)
                (pgRegs_update_ge (r := pgTmp2) (by decide)
                  (pgRegs_update_ge (r := pgTmp1) (by decide) hr)),
              by simp,
              by dsimp only
                 rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                   Function.update_of_ne (by decide), houtM, allCloudEdgesPrefix_succ G X hi_len,
                   hce_nil, List.append_nil],
              by dsimp only
                 rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                   Function.update_of_ne (by decide)]; exact hhcur_eq,
              hz, hoff, hpts,
              by rw [allCloudEdgesPrefix_succ G X hi_len, hce_nil, List.append_nil]; exact hE,
              hfr⟩
          · simp only [Expr.size]; omega
      rcases hstep with ⟨o, st_next, c_body, hr_body, ⟨rfl, hInv_next⟩, hc_body⟩
      rcases ih (i + 1) st_next ω (by omega) hInv_next with ⟨st_end, c_rest, hr_rest, hInv_end, hc_rest⟩
      refine ⟨st_end, 3 + c_body + c_rest + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st_next, c_body, c_rest, hcond, by decide,
          hr_body, hr_rest, rfl⟩)),
        hInv_end, ?_⟩
      dsimp only [T_rem] at hc_rest ⊢
      have hsub_off : 2 * e - cloudOff verts G X i = s + (2 * e - cloudOff verts G X (i + 1)) := by
        omega
      rw [hsub_off, Nat.mul_add]
      omega
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [buildTopCompactCloudLoopStmt, seqStmts]
  refine runs_seq_assign_le (v := e) (Expr.eval_reg_of_eq hregs.r_e) ?_
  refine runs_seq_assign_le (v := h)
    (Expr.eval_reg_of_eq (v := h) (by dsimp only; rw [Function.update_of_ne (by decide), hregs.r_h])) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st1 : State :=
    { mem := st₀.mem,
      regs := Function.update (Function.update (Function.update st₀.regs pgOutM e) pgHCur h) pgI 0,
      pos := st₀.pos }
  have hInv0 : Inv 0 st1 := by
    refine ⟨Nat.zero_le k,
      pgRegs_update_ge (r := pgI) (by decide)
        (pgRegs_update_ge (r := pgHCur) (by decide)
          (pgRegs_update_ge (r := pgOutM) (by decide) hregs)),
      by simp [st1],
      by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
           Function.update_self]; simp [allCloudEdgesPrefix],
      by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self],
      by dsimp only [st1]; rw [hmem]; exact hzero,
      fun t ht => hmem ▸ hoff_at t ht,
      fun t ht => hmem ▸ hpts_at t ht,
      by simp [st1, hmem, allCloudEdgesPrefix, horig_at],
      fun a _ _ _ => hmem ▸ rfl⟩
  rcases hloop_ind k 0 st1 ω (by omega) hInv0 with ⟨st2, c_loop, hr_loop, hInv2, hc_loop⟩
  rcases hInv2 with ⟨_, hr2, _, houtM2, hhcur2, hz2, _, _, hE2, hfr2⟩
  have hfull_eq : allCloudEdgesPrefix verts G X k = allCloudEdges cloud G X := by
    rw [← hvlen]; exact allCloudEdgesPrefix_full hsorted G
  have he_X : (G.inside X).length = e := he_eq
  have hpg_m : e + (allCloudEdgesPrefix verts G X k).length = (portGraph cloud G X).m := by
    rw [hfull_eq]
    simp [portGraph, Graph.m, origPortEdges, he_X]
  suffices htail : ∃ o st' c_tail,
      Runs w p ω
        (.seq (.store (.reg pgOutGraph) (.bin .mul (.const 2) (.reg pgE)))
          (.store (.bin .add (.reg pgOutGraph) (.const 1)) (.reg pgOutM)))
        st2 o st' c_tail ∧
      normalPost (fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧
        st'.regs pgHCur = h ∧
        ZeroFrom st'.mem h ∧
        GraphAt st'.mem ga (portGraph cloud G X) ∧
        (∀ a < h, (a < ga ∨ ga + 2 + 20 * e ≤ a) →
          (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → st'.mem a = mem a)) o st' ∧
      (0 + Expr.size (.reg pgE) + 2 + Expr.size (.reg pgH) + 2 + Expr.size (.const 0) + 2 +
        c_loop + 1) + c_tail ≤ 60 * k + 850 * (2 * e) + 60 by
    rcases htail with ⟨o, st', c_tail, hr_tail, hq_tail, hc_tail⟩
    exact ⟨o, st', c_loop + c_tail + 1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c_loop, c_tail, hr_loop, hr_tail, rfl⟩), hq_tail, by omega⟩
  refine runs_seq_store_le (x := ga) (v := 2 * e)
    (Expr.eval_reg_of_eq hr2.r_outGraph)
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr2.r_e) (by omega)) ?_
  refine runs_store_le (x := ga + 1) (v := (portGraph cloud G X).m)
    (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_outGraph) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := (portGraph cloud G X).m) (by dsimp only; rw [houtM2, hpg_m])) ?_ ?_
  · refine ⟨pgRegs_update_mem (pgRegs_update_mem hr2), hhcur2, ?_, ?_, ?_⟩
    · intro a ha
      dsimp only at ha ⊢
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hz2 a ha
    · refine graphAt_of_cells ?_ ?_ fun j hj => ?_
      · dsimp only; rw [Function.update_of_ne (by omega), Function.update_self, portGraph_n, he_eq]
      · dsimp only; rw [Function.update_self]
      · dsimp only
        have hpg_edges : (portGraph cloud G X).edges =
            origPortEdges e ++ allCloudEdgesPrefix verts G X k := by
          simp [portGraph, he_X, hfull_eq]
        have hj' : j < (origPortEdges e ++ allCloudEdgesPrefix verts G X k).length :=
          hpg_edges ▸ hj
        have h1 := (hE2 j hj').1
        have h2 := (hE2 j hj').2
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h1]
          simp [hpg_edges]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            show ga + 3 + 2 * j = ga + 2 + 2 * j + 1 by omega, h2]
          simp [hpg_edges]
    · intro a ha_h ha_g ha_w
      dsimp only
      rw [Function.update_of_ne (by rcases ha_g with h1 | h1 <;> omega),
        Function.update_of_ne (by rcases ha_g with h1 | h1 <;> omega)]
      exact hfr2 a ha_h ha_g ha_w
  · dsimp only [T_rem, Expr.size, cloudOff] at hc_loop ⊢
    simp only [Finset.range_zero, Finset.sum_empty, Nat.sub_zero] at hc_loop
    omega

/-- `buildTopPortCompactEntry` meets `buildTopPortCompactContract w` in linear time with zero heap. -/
theorem buildTopPortCompact_meetsContract {w f cloudIdx : ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildTopPortCompactEntry cloudIdx))
    (hc : p.procs[cloudIdx]? = some buildTopCloud) :
    MeetsContract w p f (buildTopPortCompactContract w) := by
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
      Runs w p ω (buildTopPortCompactEntry cloudIdx)
        (startState [k, va, e, ea, la, oa, ga, wa, h] mem pos) o st' c ∧
      (buildTopPortCompactContract w).post [k, va, e, ea, la, oa, ga, wa, h] mem o.value st'.mem ∧
      c ≤ buildTopPortCompactCost k e := by
    refine runs_start_le ?_
    dsimp only [buildTopPortCompactEntry, seqStmts]
    refine runs_seq_triple_le (pgSetup_triple p mem pos hb') rfl ?_
    intro st0 ⟨hr0, hmem0, _⟩
    refine runs_seq_triple_le
      (pgInitLoc_triple p mem verts st0 hvlen hnd hverts_lt hverts_at hloc0 hb' hd' hr0 hmem0) rfl ?_
    intro st1 ⟨hr1, _, hpr1, hloc1, hcur1⟩
    have hE_at1 : EdgesAt st1.mem ea inEdges :=
      hE_at.congr fun a ha1 ha2 => hpr1 a
        (disjointRange_outside hd_le ha1 (by omega))
        (by rcases hd_we with h1 | h1 <;> [right; left] <;> omega)
    refine runs_seq_triple_le
      (pgOrigAndDeg_triple p st1.mem verts inEdges st1 hvlen hnd helen hE_inX hverts_lt
        hE_at1 hloc1 hcur1 hb' hd' hr1 rfl) rfl ?_
    intro st2 ⟨hr2, _, hfr2, hown2, horig2, hdeg2⟩
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
    refine runs_seq_triple_le
      (compactCloudLoop_triple p st4.mem verts G_in st4 hc hvlen hsorted he_eq hoff4 hpts4
        horig4 hzero4 hb' hd' hr4 rfl) rfl ?_
    intro st5 ⟨hr5, hhcur5, hz5, hGA5, hfr5⟩
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
    refine runs_seq_triple_le
      (pgClearLoc_triple (hCur := h) p st5.mem verts st5 hvlen hverts_lt hverts_at5
        hb' hd_lv hr5 hhcur5 rfl) rfl ?_
    intro st6 ⟨hr6, hhcur6, _, hfr6, hpt6, hclr6⟩
    refine runs_ret_le (Expr.eval_reg_of_eq hhcur6) ?_ ?_
    · dsimp only [buildTopPortCompactContract, Outcome.value]
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
      refine ⟨hGA6, hown6, fun G hG => ?_, trivial, ?_, ?_⟩
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
    · dsimp only [buildTopPortCompactCost, Expr.size]
      omega
  rcases hrun with ⟨o, st', c, hr, hpost, hcost⟩
  exact ⟨buildTopPortCompactEntry cloudIdx, hf, o, st', c, hr, hpost,
    by simpa [buildTopPortCompactContract] using hcost⟩

end MinCostFlow.HierPaths

end
