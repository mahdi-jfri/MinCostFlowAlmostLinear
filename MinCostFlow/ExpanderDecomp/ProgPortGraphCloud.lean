module

public import MinCostFlow.ExpanderDecomp.ProgPortGraphBase
public import MinCostFlow.ExpanderDecomp.ProgPortGraphStages

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Port Graph Word-RAM Procedure — Stage 5 Cloud Loop (`ProgPortGraphCloud`)

Completes the deterministic (`NoRand`) Word-RAM implementation `portGraphProcs` of
`portGraph cloud G X` and `portOwner G X` (`PortGraph.lean`) using `cloud` and
`cloudExpanderProcs` from `ProgCloud.lean`:
- `pgMapCloudEdges_triple`: inner loop appending mapped cloud edges for a single cloud of size `s ≥ 2`.
- `pgCloudLoop_triple`: Stage 5 outer loop calling `cloudExpanderEntry` once per cloud of size
  `s ≥ 2` in exact linear time `O(|X| + |G.inside X| + 1)` and polynomial heap space
  `portGraphHeapSpace e = 41600 * e ^ 4 + 4`.
- `portGraphCost`, `portGraphContract`, `portGraph_spec`, and non-vacuity witness
  `portGraphContract_pre_example`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 1. Inner Mapping Loop and Stage 5 (`pgCloudLoopStmt`) -/

/-- Helper: mapping the edges of `cloud s` (`2 ≤ s`) through `pts` produces `cloudEdgesFor`. -/
private lemma cloudEdgesFor_eq_map_cloud {G : Graph} {X : Finset ℕ} {v : ℕ}
    (hs : 2 ≤ (cloudPortsList G X v).length) :
    cloudEdgesFor cloud G X v =
      (cloud (cloudPortsList G X v).length).edges.map fun ed =>
        ((cloudPortsList G X v).getD ed.1 0, (cloudPortsList G X v).getD ed.2 0) := by
  unfold cloudEdgesFor
  dsimp only
  rw [ite_eq_left_iff.mpr (fun h => absurd hs h)]
  congr 1
  exact List.filter_eq_self.mpr fun e he => decide_eq_true ((cloud_spec hs).2.2.1 e he)

/-- Inner loop triple: maps `(cloud s).edges` from `cloudBufAddr + 2` through `portsAddr + sStart`
and appends them after `prevEdges` at `outGraphAddr + 2`. -/
private lemma pgMapCloudEdges_triple {w n k e va ea la oa ga wa h : ℕ}
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
        rw [hfr (cloudBufAddr + 2 + 2 * j) (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega)]
        exact (hcloud_at j hj_len).1
      have hmem_v : st.mem (cloudBufAddr + 3 + 2 * j) = ed.2 := by
        rw [hfr (cloudBufAddr + 3 + 2 * j) (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega)]
        have h2 := (hcloud_at j hj_len).2
        rwa [show cloudBufAddr + 2 + 2 * j + 1 = cloudBufAddr + 3 + 2 * j by omega] at h2
      have hmem_pa : st.mem (portsAddr + sStart + ed.1) = pa := by
        rw [hfr (portsAddr + sStart + ed.1) (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega)]
        dsimp only [pa]
        rw [List.getD_eq_getElem pts 0 hu_pts]
        exact hpts_at ed.1 hu_pts
      have hmem_pb : st.mem (portsAddr + sStart + ed.2) = pb := by
        rw [hfr (portsAddr + sStart + ed.2) (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega)]
        dsimp only [pb]
        rw [List.getD_eq_getElem pts 0 hv_pts]
        exact hpts_at ed.2 hv_pts
      set curM := prevEdges.length + j
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := ed.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr.r_cloudBuf) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hrj) (by omega)) (by omega))
          hmem_u) ?_
      refine runs_seq_assign_le (v := ed.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := cloudBufAddr)
                (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_cloudBuf]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := j)
                (by dsimp only; rw [Function.update_of_ne (by decide), hrj])) (by omega)) (by omega))
          hmem_v) ?_
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
        (Expr.eval_reg_of_eq (v := pa)
          (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) ?_
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

/-- Stage 5 triple: builds all cloud expander edges and writes the `portGraph` header at
`outGraphAddr`, in linear time `O(k + e)` and heap space `≤ portGraphHeapSpace e`. -/
lemma pgCloudLoop_triple {w n k e va ea la oa ga wa h b : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (G : Graph) (st₀ : State)
    (hp_cloud : p.HasAt (b + 1) (cloudExpanderProcs (b + 1)))
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
    Triple w p (fun st => st = st₀) (pgCloudLoopStmt b)
      (normalPost fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧
        h ≤ st'.regs pgHCur ∧
        st'.regs pgHCur ≤ h + portGraphHeapSpace e ∧
        ZeroFrom st'.mem (st'.regs pgHCur) ∧
        GraphAt st'.mem ga (portGraph cloud G X) ∧
        (∀ a < h, (a < ga ∨ ga + 2 + 20 * e ≤ a) →
          (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → st'.mem a = mem a))
      (fun _ => 60 * k + (runnerScale explicitProgram * 380 + 800) * (2 * e) + 60) := by
  intro X
  have hnd : verts.Nodup := hsorted.imp fun h1 => Nat.ne_of_lt h1
  have hSpec_cloud := cloudExpander_spec (w := w) hp_cloud
  rcases hb with ⟨hva_h, hea_h, hla_h, hoa_h, hga_h, hws_h, hhw, hw16⟩
  rcases hd with ⟨hd_lv, hd_le, hd_lo, hd_lg, hd_lw, hd_ov, hd_oe, hd_og, hd_ow, hd_gv, hd_ge, hd_gw, hd_wv, hd_we⟩
  have hws_def : portGraphWorkSpace k e = 2 * k + 20 * e + 4 := rfl
  have hhs_def : portGraphHeapSpace e = 41600 * e ^ 4 + 4 := rfl
  let offAddr := wa + 1
  let portsAddr := wa + 2 * k + 2
  let cloudBufAddr := wa + 2 * k + 2 + 2 * e
  let Cport := runnerScale explicitProgram * 380 + 800
  let Inv : ℕ → State → Prop := fun i st =>
    i ≤ k ∧
    PgRegs k va e ea la oa ga wa h st ∧
    st.regs pgI = i ∧
    st.regs pgOutM = e + (allCloudEdgesPrefix verts G X i).length ∧
    h ≤ st.regs pgHCur ∧
    st.regs pgHCur ≤ h + cloudHeapUsed verts G X i ∧
    ZeroFrom st.mem (st.regs pgHCur) ∧
    (∀ t ≤ k, st.mem (offAddr + t) = cloudOff verts G X t) ∧
    (∀ t < k, ListAt st.mem (portsAddr + cloudOff verts G X t)
      (cloudPortsList G X (verts.getD t 0))) ∧
    EdgesAt st.mem (ga + 2) (origPortEdges e ++ allCloudEdgesPrefix verts G X i) ∧
    (∀ a < h, (a < ga ∨ ga + 2 + 20 * e ≤ a) →
      (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → st.mem a = mem a)
  let T_rem : ℕ → ℕ := fun i => 60 * (k - i) + Cport * (2 * e - cloudOff verts G X i) + 10
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
                  .call pgHCur (b + 1) [.reg pgWork, .reg pgCloudBuf, .reg pgHCur],
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
      rcases hInv with ⟨hik, hr, hi, houtM, hh_le, hh_ub, hz, hoff, hpts, hE, hfr⟩
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
      -- Run one iteration body
      have hbody : ∃ st_next c_body,
          Runs w p ω
            (seqStmts [
              .assign pgTmp1 (.load (.bin .add (.reg pgOff) (.reg pgI))),
              .assign pgTmp2 (.bin .sub
                (.load (.bin .add (.bin .add (.reg pgOff) (.reg pgI)) (.const 1)))
                (.reg pgTmp1)),
              .cond (.bin .lt (.const 1) (.reg pgTmp2))
                (seqStmts [
                  .store (.reg pgWork) (.reg pgTmp2),
                  .call pgHCur (b + 1) [.reg pgWork, .reg pgCloudBuf, .reg pgHCur],
                  .assign pgCM (.load (.bin .add (.reg pgCloudBuf) (.const 1))),
                  pgMapCloudEdgesStmt
                ])
                .nop,
              .assign pgI (.bin .add (.reg pgI) (.const 1))])
            st .normal st_next c_body ∧
          Inv (i + 1) st_next ∧
          c_body ≤ 50 + Cport * s := by
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
                    .call pgHCur (b + 1) [.reg pgWork, .reg pgCloudBuf, .reg pgHCur],
                    .assign pgCM (.load (.bin .add (.reg pgCloudBuf) (.const 1))),
                    pgMapCloudEdgesStmt
                  ])
                  .nop,
                .assign pgI (.bin .add (.reg pgI) (.const 1))])
              st o st_next c_body ∧
            (o = .normal ∧ Inv (i + 1) st_next) ∧
            c_body ≤ 50 + Cport * s := by
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
          · -- Branch `2 ≤ s`: invoke `cloudExpanderEntry` and map its edges
            have hs2 : 2 ≤ s := by
              by_contra hlt
              have hnot : ¬ (1 < s) := by omega
              simp [hnot] at hs_gt1_ne
            set hCur := st.regs pgHCur
            have hheap_succ : cloudHeapUsed verts G X (i + 1) =
                cloudHeapUsed verts G X i + cloudExpanderSpace s := by
              unfold cloudHeapUsed
              rw [Finset.sum_range_succ]
              simp only [pts, s, hs2, ↓reduceIte]
            have hheap_le : cloudHeapUsed verts G X (i + 1) ≤ portGraphHeapSpace e := by
              rw [← he_eq]; exact cloudHeapUsed_le hnd G (by omega)
            have hhcur_lt_w : hCur + cloudExpanderSpace s ≤ 2 ^ w := by omega
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
            have hz_c0 : ZeroFrom st_c0.mem hCur := fun a ha => by
              dsimp only [st_c0]; rw [Function.update_of_ne (by omega)]; exact hz a ha
            have hcloud_pre : (cloudExpanderContract w).pre [wa, cloudBufAddr, hCur] st_c0.mem :=
              ⟨wa, cloudBufAddr, hCur, s, rfl, by simp [st_c0], hs2, hz_c0, by omega, hhcur_lt_w⟩
            have hcloud_words : ∀ a ∈ ([wa, cloudBufAddr, hCur] : List ℕ), a < 2 ^ w := by
              intro a ha
              simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
              have hcs_pos : 4 ≤ cloudExpanderSpace s := by unfold cloudExpanderSpace; omega
              rcases ha with rfl | rfl | rfl <;> omega
            have hE_cloud : evalArgs w st_c0 [.reg pgWork, .reg pgCloudBuf, .reg pgHCur] =
                some [wa, cloudBufAddr, hCur] := by
              have h1 : st_c0.regs pgWork = wa := hr_b.r_work
              have h2 : st_c0.regs pgCloudBuf = cloudBufAddr := hr_b.r_cloudBuf
              have h3 : st_c0.regs pgHCur = hCur := by
                dsimp only [st_c0]
                rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
              simp [evalArgs, Expr.eval, h1, h2, h3]
            refine runs_seq_assoc_le ?_
            refine runs_seq_call_le hSpec_cloud hE_cloud hcloud_words hcloud_pre ?_
            intro hNext mem1 pos1 hpost1
            dsimp only [cloudExpanderContract] at hpost1
            simp only [List.getD_cons_zero, List.getD_cons_succ, Function.update_self] at hpost1
            rcases hpost1 with ⟨hGA1, hEA1, _, _, _, _, _, hhcur_le_next, hnext_le, hz1, hbelow1⟩
            have hcm_mem : mem1 (cloudBufAddr + 1) = (cloud s).m := graphAt_m hGA1
            let st_c1 : State :=
              { mem := mem1, regs := Function.update st_c0.regs pgHCur hNext, pos := pos1 }
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
              have hlt_h : portsAddr + sStart + t < h := by omega
              rw [hbelow1 (portsAddr + sStart + t) (by omega) (Or.inl (by omega)),
                Function.update_of_ne (by omega)]
              exact hpts i hilt t ht
            have hE_prev1 : EdgesAt mem1 (ga + 2) (origPortEdges e ++ allCloudEdgesPrefix verts G X i) := by
              intro t ht
              have hlen_pre : (origPortEdges e ++ allCloudEdgesPrefix verts G X i).length ≤ 10 * e := by
                rw [List.length_append, show (origPortEdges e).length = e by simp [origPortEdges]]
                have h1 : (allCloudEdgesPrefix verts G X i).length ≤ 9 * e :=
                  he_eq ▸ allCloudEdgesPrefix_length_le hnd G (by omega : i ≤ verts.length)
                omega
              have hlt_ga1 : ga + 2 + 2 * t < h := by omega
              have hlt_ga2 : ga + 2 + 2 * t + 1 < h := by omega
              have hout_cb1 : ga + 2 + 2 * t < cloudBufAddr ∨ cloudBufAddr + 2 + 9 * s ≤ ga + 2 + 2 * t := by
                rcases hd_gw with h1 | h1 <;> [left; right] <;> omega
              have hout_cb2 : ga + 2 + 2 * t + 1 < cloudBufAddr ∨ cloudBufAddr + 2 + 9 * s ≤ ga + 2 + 2 * t + 1 := by
                rcases hd_gw with h1 | h1 <;> [left; right] <;> omega
              refine ⟨?_, ?_⟩
              · rw [hbelow1 _ (by omega) hout_cb1,
                  Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega)]
                exact (hE t ht).1
              · rw [hbelow1 _ (by omega) hout_cb2,
                  Function.update_of_ne (by rcases hd_gw with h1 | h1 <;> omega)]
                exact (hE t ht).2
            have hprev_cm_le : (origPortEdges e ++ allCloudEdgesPrefix verts G X i).length + (cloud s).m ≤ 10 * e := by
              have h1 : (allCloudEdgesPrefix verts G X (i + 1)).length ≤ 9 * e :=
                he_eq ▸ allCloudEdgesPrefix_length_le hnd G (by omega : i + 1 ≤ verts.length)
              rw [allCloudEdgesPrefix_succ G X hi_len, List.length_append] at h1
              have hce_len : (cloudEdgesFor cloud G X (verts[i]'hi_len)).length = (cloud s).m := by
                rw [← List.getD_eq_getElem verts 0 hi_len, cloudEdgesFor_eq_map_cloud hs2, List.length_map]
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
              (pgMapCloudEdges_triple (i := i) (sStart := sStart) (s := s) (hCur := hNext)
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
                exact cloudEdgesFor_eq_map_cloud hs2
              refine ⟨rfl, by omega, pgRegs_update_ge (r := pgI) (by decide) hr3, by simp, ?_, ?_, ?_,
                ?_, ?_, ?_, ?_, ?_⟩
              · dsimp only
                rw [Function.update_of_ne (by decide), hroutM3, hlen_outM,
                  allCloudEdgesPrefix_succ G X hi_len, List.length_append, hce_eq, List.length_map]
                change e + (allCloudEdgesPrefix verts G X i).length + (cloud s).edges.length =
                  e + ((allCloudEdgesPrefix verts G X i).length + (cloud s).edges.length)
                omega
              · dsimp only; rw [Function.update_of_ne (by decide), hrhcur3]; omega
              · dsimp only; rw [Function.update_of_ne (by decide), hrhcur3]; omega
              · intro a ha
                dsimp only at ha ⊢
                rw [Function.update_of_ne (by decide), hrhcur3] at ha
                rw [hfr3 a (Or.inr (by omega))]
                exact hz1 a ha
              · intro t ht
                dsimp only
                rw [hfr3 (offAddr + t) (by rcases hd_gw with h1 | h1 <;> [right; left] <;> omega),
                  hbelow1 (offAddr + t) (by omega) (Or.inl (by omega)),
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
                  hbelow1 (portsAddr + cloudOff verts G X t + u) (by omega) (Or.inl (by omega)),
                  Function.update_of_ne (by omega)]
                exact hpts t ht u hu
              · dsimp only
                rw [allCloudEdgesPrefix_succ G X hi_len, ← List.append_assoc, hce_eq]
                exact hE3
              · intro a ha_h ha_g ha_w
                dsimp only
                rw [hfr3 a (by rcases ha_g with h1 | h1 <;> [left; right] <;> omega),
                  hbelow1 a (by omega) (by rcases ha_w with h1 | h1 <;> [left; right] <;> omega),
                  Function.update_of_ne (by rcases ha_w with h1 | h1 <;> omega)]
                exact hfr a ha_h ha_g ha_w
            · have hcm_s : 2 * (cloud s).m ≤ 9 * s := cloud_m_le hs2
              dsimp only [cloudExpanderContract, cloudExpanderCost, Cport, argsSize, Expr.size, st_c0]
              simp only [List.getD_cons_zero, Function.update_self]
              have hmul : (runnerScale explicitProgram * 380 + 800) * s =
                  (runnerScale explicitProgram * 380 + 400) * s + 400 * s := by ring
              rw [hmul]
              omega
          · -- Branch `s < 2`: `nop`, no cloud edges added
            have hs_lt2 : s < 2 := by
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
              have hheap_eq : cloudHeapUsed verts G X (i + 1) = cloudHeapUsed verts G X i := by
                unfold cloudHeapUsed
                rw [Finset.sum_range_succ]
                simp only [pts, s, show ¬ (2 ≤ s) by omega, ↓reduceIte, add_zero]
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
                     Function.update_of_ne (by decide)]; exact hh_le,
                by dsimp only
                   rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                     Function.update_of_ne (by decide), hheap_eq]; exact hh_ub,
                by dsimp only
                   rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                     Function.update_of_ne (by decide)]; exact hz,
                hoff, hpts,
                by rw [allCloudEdgesPrefix_succ G X hi_len, hce_nil, List.append_nil]; exact hE,
                hfr⟩
            · simp only [Expr.size]; omega
        rcases hstep with ⟨o, st_next, c_body, hr_b, ⟨rfl, hInv_next⟩, hc_b⟩
        exact ⟨st_next, c_body, hr_b, hInv_next, hc_b⟩
      rcases hbody with ⟨st_next, c_body, hr_body, hInv_next, hc_body⟩
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
  -- Assemble `pgCloudLoopStmt`
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [pgCloudLoopStmt, seqStmts]
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
      by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]; simp [cloudHeapUsed],
      by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self, hmem]; exact hzero,
      fun t ht => hmem ▸ hoff_at t ht,
      fun t ht => hmem ▸ hpts_at t ht,
      by simp [st1, hmem, allCloudEdgesPrefix, horig_at],
      fun a _ _ _ => hmem ▸ rfl⟩
  rcases hloop_ind k 0 st1 ω (by omega) hInv0 with ⟨st2, c_loop, hr_loop, hInv2, hc_loop⟩
  rcases hInv2 with ⟨_, hr2, _, houtM2, hh_le2, hh_ub2, hz2, _, _, hE2, hfr2⟩
  have hheap_k : cloudHeapUsed verts G X k ≤ portGraphHeapSpace e := by
    rw [← he_eq]; exact cloudHeapUsed_le hnd G (hvlen ▸ le_refl k)
  have hfull_eq : allCloudEdgesPrefix verts G X k = allCloudEdges cloud G X := by
    rw [← hvlen]; exact allCloudEdgesPrefix_full hsorted G
  have he_X : (G.inside X).length = e := he_eq
  have hpg_m : e + (allCloudEdgesPrefix verts G X k).length = (portGraph cloud G X).m := by
    rw [hfull_eq]
    simp [portGraph, Graph.m, origPortEdges, he_X]
  -- Sequence loop + 2 header stores
  suffices htail : ∃ o st' c_tail,
      Runs w p ω
        (.seq (.store (.reg pgOutGraph) (.bin .mul (.const 2) (.reg pgE)))
          (.store (.bin .add (.reg pgOutGraph) (.const 1)) (.reg pgOutM)))
        st2 o st' c_tail ∧
      normalPost (fun st' =>
        PgRegs k va e ea la oa ga wa h st' ∧
        h ≤ st'.regs pgHCur ∧ st'.regs pgHCur ≤ h + portGraphHeapSpace e ∧
        ZeroFrom st'.mem (st'.regs pgHCur) ∧
        GraphAt st'.mem ga (portGraph cloud G X) ∧
        (∀ a < h, (a < ga ∨ ga + 2 + 20 * e ≤ a) →
          (a < wa ∨ wa + portGraphWorkSpace k e ≤ a) → st'.mem a = mem a)) o st' ∧
      (0 + Expr.size (.reg pgE) + 2 + Expr.size (.reg pgH) + 2 + Expr.size (.const 0) + 2 +
        c_loop + 1) + c_tail ≤ 60 * k + Cport * (2 * e) + 60 by
    rcases htail with ⟨o, st', c_tail, hr_tail, hq_tail, hc_tail⟩
    dsimp only [Cport] at hc_tail
    exact ⟨o, st', c_loop + c_tail + 1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c_loop, c_tail, hr_loop, hr_tail, rfl⟩), hq_tail, by omega⟩
  refine runs_seq_store_le (x := ga) (v := 2 * e)
    (Expr.eval_reg_of_eq hr2.r_outGraph)
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr2.r_e) (by omega)) ?_
  refine runs_store_le (x := ga + 1) (v := (portGraph cloud G X).m)
    (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_outGraph) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := (portGraph cloud G X).m) (by dsimp only; rw [houtM2, hpg_m])) ?_ ?_
  · refine ⟨pgRegs_update_mem (pgRegs_update_mem hr2), hh_le2,
      le_trans hh_ub2 (Nat.add_le_add_left hheap_k h), ?_, ?_, ?_⟩
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


end MinCostFlow.ExpanderDecomp
