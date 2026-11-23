module

public import MinCostFlow.Expander.DecomposePartBuild
public import MinCostFlow.Expander.DecomposePartInB

import Mathlib.Data.Nat.Log

/-!
# Partition Pruning: Call, Output Emission, and Combined `partPruneProc` Spec

Proves `partPruneCall_triple`, `partEmitR_triple`, and the full per-partition execution theorem
`partPrune_runs` for `partPruneProc`, connecting the Word-RAM execution on partition `q` directly
to `badTwin_part_spec`, `prune_compressed_part_pre`, `prune_compressed_part_post`, and
`card_two_add_le_four_mul_m`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Pure Helpers -/

lemma partWorkSize_mono {n₁ m₁ H₁ n₂ m₂ H₂ : ℕ}
    (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) (hH : H₁ ≤ H₂) :
    partWorkSize n₁ m₁ H₁ ≤ partWorkSize n₂ m₂ H₂ := by
  unfold partWorkSize pruneWorkSpace
  omega

private lemma compressPartGraph_inside_verts_length (curG : Cited.Graph)
    (actVerts : List ℕ) (X : Finset ℕ) (hstrict : actVerts.Pairwise (· < ·))
    (hbound : ∀ u ∈ actVerts, u < curG.n) :
    let G_X := compressPartGraph actVerts (curG.inside X)
    G_X.IsValid → (G_X.inside G_X.verts).length = G_X.m := by
  intro G_X hV
  have _ := hstrict
  have _ := hbound
  have heq : G_X.inside G_X.verts = G_X.edges := by
    unfold Cited.Graph.inside
    exact List.filter_eq_self.mpr fun e he => by
      have hv := hV e he
      simp [Cited.Graph.verts, hv.1, hv.2]
  rw [heq]; rfl

/-! ## 2. `partPruneCallStmt` Triple -/

lemma partPruneCall_triple {w curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr
    b_csr b_prune : ℕ}
    (p : Program) (mem : ℕ → ℕ)
    (curG : Cited.Graph) (hV : curG.IsValid) (_hL : curG.IsLoopless)
    (hD : 1 ≤ D) (hDphi : 200 ≤ D_phi)
    {Y : Finset ℕ} {φ_B1 : ℝ} (hφ_unif : 1 / (D_phi : ℝ) ≤ φ_B1)
    (hexpY : (twinGraph D curG).IsConductanceExpanderOn Y φ_B1)
    (cnt off ecnt eoff : ℕ)
    (hstrict : (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)).Pairwise (· < ·))
    (hactX : (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)).toFinset = partX curG.n Y)
    (hGX_n : (compressPartGraph (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t))
      (curG.inside (partX curG.n Y))).n = cnt)
    (hGX_m : (compressPartGraph (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t))
      (curG.inside (partX curG.n Y))).m = ecnt)
    (hgaX : GraphAt mem (partGXAddr workAddr cnt ecnt)
      (compressPartGraph (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t))
        (curG.inside (partX curG.n Y))))
    (hinB : ∀ x < cnt,
      mem (partInBAddr workAddr cnt ecnt + x) ≠ 0 ↔
        (compressPartGraph (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t))
          (curG.inside (partX curG.n Y))).degIn
          (compressPartGraph (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t))
            (curG.inside (partX curG.n Y))).verts x * D_phi < D)
    (hp_csr : MeetsContract w p b_csr (buildCsrContract w))
    (hp_prune : p.procs[b_prune]? = some pruneWrapProc)
    (hwork_w : workAddr + partWorkSize cnt ecnt
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) + 2 < 2 ^ w)
    (harith_w : 8 * (4 * D_phi + 2) * ecnt + 4 * (4 * D_phi + 2) + 2 * cnt + 2 * ecnt +
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) + 16 < 2 ^ w)
    (hD_w : D + 3 * D_phi < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) :
    let H := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2
    let actVerts := tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)
    let G_X := compressPartGraph actVerts (curG.inside (partX curG.n Y))
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      (partPruneCallStmt b_csr b_prune)
      (normalPost fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        MemFrame mem st.mem workAddr (workAddr + partWorkSize cnt ecnt H) ∧
        have R_loc := (Finset.range cnt).filter fun x =>
          decide (st.mem (partOutRAddr workAddr cnt ecnt + x) ≠ 0)
        R_loc ⊆ G_X.verts \ ((Finset.range G_X.n).filter fun k => decide (G_X.degIn G_X.verts k * D_phi < D)) ∧
        G_X.IsConductanceExpanderOn R_loc ((1 / (D_phi : ℝ)) / 3) ∧
        (∀ v ∈ R_loc, (D + 3 * D_phi - 1) / (3 * D_phi) ≤ G_X.degIn R_loc v) ∧
        (let B_loc := (Finset.range G_X.n).filter fun k => decide (G_X.degIn G_X.verts k * D_phi < D)
         G_X.volIn G_X.verts (G_X.verts \ R_loc) ≤
           G_X.volIn G_X.verts B_loc + 2 * (4 * D_phi + 2) * G_X.cutIn G_X.verts B_loc))
      (fun _ => pruneTimeBound cnt ecnt H + 200 * (cnt + ecnt + 1) +
        13 * (Nat.log 2 (2 * ecnt + 1) + 1) + 100) := by
  intro H actVerts G_X st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, hm⟩
  have hpre_p := prune_compressed_part_pre hV hD hDphi hφ_unif hexpY hstrict hactX
  rcases hpre_p with ⟨hbound, hGX_V, hcfgV, hexpGX, hC5, hCphi, hθ⟩
  set X := partX curG.n Y
  set B_loc := (Finset.range G_X.n).filter fun k => decide (G_X.degIn G_X.verts k * D_phi < D)
  set cfg := pruneCfgOf G_X G_X.verts B_loc (1 / (D_phi : ℝ)) ((1 / (D_phi : ℝ)) * (D : ℝ))
  have hunif := pruneCfg_unif_params (G := G_X) (X := G_X.verts) (B := B_loc) (D := D) hDphi
  rcases hunif with ⟨hcfg_C, _, _, hcfg_θ, hcfg_H⟩
  have hins_len : (G_X.inside G_X.verts).length = ecnt := by
    rw [compressPartGraph_inside_verts_length curG actVerts X hstrict hbound hGX_V]
    exact hGX_m
  have hcfg_H_eq : cfg.H = H := by rw [hcfg_H, hins_len]
  have hφ0_pos : (0 : ℝ) < 1 / (D_phi : ℝ) := by positivity
  have hw4 : 4 ≤ 2 ^ w := by omega
  have hC_w : 4 * D_phi + 2 < 2 ^ w := by omega
  have h2ec_w : 2 * ecnt + 1 < 2 ^ w := by omega
  have hlog_w : Nat.log 2 (2 * ecnt + 1) < 2 ^ w :=
    lt_of_le_of_lt (Nat.log_le_self 2 (2 * ecnt + 1)) h2ec_w
  have hH_w : H < 2 ^ w := by
    dsimp only [H]
    unfold partWorkSize pruneWorkSpace at hwork_w
    omega
  have hD3_pos : 0 < 3 * D_phi := by omega
  have hθ_w : (D + 3 * D_phi - 1) / (3 * D_phi) < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  -- Step 1-3: `r22 = C_cap`, `r24 = 2 * ecnt + 1`, `r23 = 0`
  let st0a : State := { st with regs := Function.update st.regs 22 (4 * D_phi + 2) }
  let st0b : State := { st0a with regs := Function.update st0a.regs 24 (2 * ecnt + 1) }
  let st1 : State := { st0b with regs := Function.update st0b.regs 23 0 }
  have ha22 : Runs w p ω (.assign 22 (.bin .add (.bin .mul (.const 4) (.reg 5)) (.const 2)))
      st .normal st0a 6 :=
    runs_assign_iff.mpr ⟨4 * D_phi + 2, by
      simp [Expr.eval, BinOp.eval, h5, show (4 : ℕ) < 2 ^ w by omega, show (2 : ℕ) < 2 ^ w by omega,
        show 4 * D_phi < 2 ^ w by omega, hC_w], rfl, rfl, rfl⟩
  have ha24 : Runs w p ω (.assign 24 (.bin .add (.bin .mul (.const 2) (.reg 13)) (.const 1)))
      st0a .normal st0b 6 :=
    runs_assign_iff.mpr ⟨2 * ecnt + 1, by
      simp [st0a, Expr.eval, BinOp.eval, h13, show (2 : ℕ) < 2 ^ w by omega,
        show (1 : ℕ) < 2 ^ w by omega, show 2 * ecnt < 2 ^ w by omega, h2ec_w], rfl, rfl, rfl⟩
  have ha23 : Runs w p ω (.assign 23 (.const 0)) st0b .normal st1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Step 4: `log2_loop_runs`
  have hloop_res := log2_loop_runs (w := w) (p := p) (ω := ω) 24 23 (by decide)
    (2 * ecnt + 1) h2ec_w hw4 st1 (by simp [st1, st0b]) (by simp [st1]) hlog_w
  rcases hloop_res with ⟨st2, c_log, hr_log, hr23, hm2, hpos2, hregs2, hc_log⟩
  have hr_eq2 : ∀ r, r ≤ 20 → st2.regs r = st.regs r := fun r hr => by
    have hr24 : r ≠ 24 := by omega
    have hr23' : r ≠ 23 := by omega
    rw [hregs2 r hr24 hr23']
    simp only [st1, st0b, st0a, Function.update_of_ne hr23', Function.update_of_ne hr24,
      Function.update_of_ne (by omega : r ≠ 22)]
  have hst2_22 : st2.regs 22 = 4 * D_phi + 2 := by
    rw [hregs2 22 (by decide) (by decide)]
    simp [st1, st0b, st0a]
  have hm2_mem : st2.mem = mem := hm2.trans hm
  -- Step 5-6: `r25 = H`, `r26 = theta_out_nat`
  let st2a : State := { st2 with regs := Function.update st2.regs 25 H }
  let st3 : State := { st2a with regs := Function.update st2a.regs 26 ((D + 3 * D_phi - 1) / (3 * D_phi)) }
  have h4_st2 : st2.regs 4 = D := (hr_eq2 4 (by omega)).trans h4
  have h5_st2 : st2.regs 5 = D_phi := (hr_eq2 5 (by omega)).trans h5
  have hlog_le_ec : Nat.log 2 (2 * ecnt + 1) ≤ 2 * ecnt + 1 := Nat.log_le_self 2 (2 * ecnt + 1)
  have ha25 : Runs w p ω
      (.assign 25 (.bin .add (.bin .mul (.bin .mul (.const 4) (.reg 22))
        (.bin .add (.reg 23) (.const 1))) (.const 2))) st2 .normal st2a 10 := by
    have h4C : 4 * (4 * D_phi + 2) < 2 ^ w := by omega
    have hlg1 : Nat.log 2 (2 * ecnt + 1) + 1 < 2 ^ w := by omega
    have hprod : 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) < 2 ^ w := by
      dsimp only [H] at hH_w; omega
    have h4lt : 4 < 2 ^ w := by omega
    have hH_exp : 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2 < 2 ^ w := hH_w
    refine runs_assign_iff.mpr ⟨H, ?_, rfl, rfl, rfl⟩
    dsimp only [H]
    simp [Expr.eval, BinOp.eval, hst2_22, hr23, h4lt, show (1 : ℕ) < 2 ^ w by omega,
      show (2 : ℕ) < 2 ^ w by omega, h4C, hlg1, hprod, hH_exp]
  have ha26 : Runs w p ω
      (.assign 26 (.bin .div (.bin .sub (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 5))) (.const 1))
        (.bin .mul (.const 3) (.reg 5)))) st2a .normal st3 12 := by
    have h3D : 3 * D_phi < 2 ^ w := by omega
    have hD3D : D + 3 * D_phi < 2 ^ w := hD_w
    have hD3D1 : D + 3 * D_phi - 1 < 2 ^ w := by omega
    exact runs_assign_iff.mpr ⟨(D + 3 * D_phi - 1) / (3 * D_phi), by
      simp [st2a, Expr.eval, BinOp.eval, h4_st2, h5_st2, show (3 : ℕ) < 2 ^ w by omega,
        show (1 : ℕ) < 2 ^ w by omega, h3D, hD3D, hD3D1, hθ_w], rfl, rfl, rfl⟩
  have hr_eq3 : ∀ r, r ≤ 20 → st3.regs r = st.regs r := fun r hr => by
    simp only [st3, st2a, Function.update_of_ne (by omega : r ≠ 26),
      Function.update_of_ne (by omega : r ≠ 25)]
    exact hr_eq2 r hr
  have hst3_22 : st3.regs 22 = 4 * D_phi + 2 := by
    simp [st3, st2a, hst2_22]
  have hst3_25 : st3.regs 25 = H := by simp [st3, st2a]
  have hst3_26 : st3.regs 26 = (D + 3 * D_phi - 1) / (3 * D_phi) := by simp [st3]
  have hm3_mem : st3.mem = mem := hm2_mem
  -- Step 7: `.call 27 b_csr [.reg 15, .reg 19]`
  have hGX_addr_w : partGXAddr workAddr cnt ecnt < 2 ^ w := by
    dsimp only [partGXAddr, partWorkSize] at hwork_w ⊢; omega
  have hCsr_addr_w : partCsrAddr workAddr cnt ecnt < 2 ^ w := by
    dsimp only [partCsrAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega
  have hcsr_pre : (buildCsrContract w).pre [partGXAddr workAddr cnt ecnt, partCsrAddr workAddr cnt ecnt] st3.mem := by
    refine ⟨partGXAddr workAddr cnt ecnt, partCsrAddr workAddr cnt ecnt, G_X, rfl,
      hm3_mem ▸ hgaX, hGX_V, ?_, ?_, hw4⟩
    · dsimp only [partGXAddr, partCsrAddr]
      rw [graph_encode_length, hGX_m]
      omega
    · dsimp only [partCsrAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢
      rw [hGX_n, hGX_m]
      omega
  have hcall_csr := runs_call_of_meetsContract (r := 27) (ω := ω) hp_csr
    (args := [.reg 15, .reg 19])
    (vs := [partGXAddr workAddr cnt ecnt, partCsrAddr workAddr cnt ecnt])
    (st := st3)
    (by simp [evalArgs, Expr.eval, (hr_eq3 15 (by omega)).trans h15,
      (hr_eq3 19 (by omega)).trans h19])
    (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> omega)
    hcsr_pre
  rcases hcall_csr with ⟨st4, c_csr, v_csr, hr_csr, hpost_csr, hr27_csr, hother_csr, hc_csr⟩
  dsimp only [buildCsrContract] at hpost_csr hc_csr
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at hpost_csr hc_csr
  have hread_GX : Cited.readGraph st3.mem (partGXAddr workAddr cnt ecnt) = G_X :=
    graphAt_iff_readGraph.mp (hm3_mem ▸ hgaX)
  rw [hread_GX] at hpost_csr hc_csr
  rcases hpost_csr with ⟨_, hHasCsr4, hfr_csr4⟩
  have hr_eq4 : ∀ r, r ≤ 26 → st4.regs r = st3.regs r := fun r hr =>
    hother_csr r (by omega)
  have hgaX4 : GraphAt st4.mem (partGXAddr workAddr cnt ecnt) G_X := by
    refine graphAt_of_cells
      (by rw [hfr_csr4 _ (Or.inl (by dsimp only [partGXAddr, partCsrAddr]; omega)), hm3_mem]; exact graphAt_n hgaX)
      (by rw [hfr_csr4 _ (Or.inl (by dsimp only [partGXAddr, partCsrAddr]; omega)), hm3_mem]; exact graphAt_m hgaX)
      fun j hj => ?_
    have hj_m : j < ecnt := hGX_m ▸ hj
    refine ⟨?_, ?_⟩
    · rw [hfr_csr4 _ (Or.inl (by dsimp only [partGXAddr, partCsrAddr]; omega)), hm3_mem]
      exact graphAt_edge_fst hgaX hj
    · rw [hfr_csr4 _ (Or.inl (by dsimp only [partGXAddr, partCsrAddr]; omega)), hm3_mem]
      exact graphAt_edge_snd hgaX hj
  have hinB4 : ∀ x, x ∈ B_loc ↔ x < G_X.n ∧ st4.mem (partInBAddr workAddr cnt ecnt + x) ≠ 0 := by
    intro x
    have hmem_inB : x < cnt → st4.mem (partInBAddr workAddr cnt ecnt + x) = mem (partInBAddr workAddr cnt ecnt + x) := by
      intro hx
      rw [hfr_csr4 _ (Or.inl (by dsimp only [partInBAddr, partCsrAddr]; omega)), hm3_mem]
    simp only [B_loc, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hxd⟩
      have hxc : x < cnt := hGX_n ▸ hx
      refine ⟨hx, ?_⟩
      rw [hmem_inB hxc]
      exact (hinB x hxc).mpr (by simpa using hxd)
    · rintro ⟨hx, hxnz⟩
      have hxc : x < cnt := hGX_n ▸ hx
      rw [hmem_inB hxc] at hxnz
      refine ⟨hx, decide_eq_true ((hinB x hxc).mp hxnz)⟩
  -- Step 8: `.call 27 b_prune [...]`
  have hinB_w : partInBAddr workAddr cnt ecnt + G_X.n < 2 ^ w := by
    rw [hGX_n]; dsimp only [partInBAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega
  have houtR_w : partOutRAddr workAddr cnt ecnt + G_X.n < 2 ^ w := by
    rw [hGX_n]; dsimp only [partOutRAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega
  have hPruneWork_addr_w : partPruneWorkAddr workAddr cnt ecnt < 2 ^ w := by
    dsimp only [partPruneWorkAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega
  have hprune_wb : PruneWordBound w G_X.n G_X.m cfg.C_cap cfg.H (partPruneWorkAddr workAddr cnt ecnt) := by
    rw [hGX_n, hGX_m, hcfg_H_eq, hcfg_C]
    exact partPrune_wordBound rfl rfl (by omega) (by omega)
  have hprune_disj : PruneMemDisjoint (partGXAddr workAddr cnt ecnt) (partCsrAddr workAddr cnt ecnt)
      (partInBAddr workAddr cnt ecnt) (partOutRAddr workAddr cnt ecnt)
      (partPruneWorkAddr workAddr cnt ecnt) G_X.n G_X.m cfg.H G_X.encode.length := by
    rw [graph_encode_length, hGX_n, hGX_m, hcfg_H_eq]
    exact partPrune_memDisjoint workAddr cnt ecnt H
  have hg_len_w : partGXAddr workAddr cnt ecnt + G_X.encode.length < 2 ^ w := by
    rw [graph_encode_length, hGX_m]; dsimp only [partGXAddr, partWorkSize] at hwork_w ⊢; omega
  have hcsr_len_w : partCsrAddr workAddr cnt ecnt + 2 * G_X.n + 1 + 4 * G_X.m < 2 ^ w := by
    rw [hGX_n, hGX_m]; dsimp only [partCsrAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega
  have hpw_res := pruneWrap_runs (w := w) (p := p) (cfg := cfg)
    (gAddr := partGXAddr workAddr cnt ecnt) (csrAddr := partCsrAddr workAddr cnt ecnt)
    (inBAddr := partInBAddr workAddr cnt ecnt) (outRAddr := partOutRAddr workAddr cnt ecnt)
    (workAddr := partPruneWorkAddr workAddr cnt ecnt) (φ₀ := 1 / (D_phi : ℝ))
    st4.mem st4.pos ω rfl hcfgV hexpGX hφ0_pos hC5 hCphi hθ hprune_wb hprune_disj
    hg_len_w hcsr_len_w hinB_w houtR_w hgaX4 hHasCsr4 hinB4
  rcases hpw_res with ⟨st_pw, c_pw, hr_pw, _, hpr_pw, hc_pw, hR_sub, hexpR, hdegR, hvolR⟩
  let st5 : State := { st_pw with regs := Function.update st4.regs 27 0 }
  have hcall_args : evalArgs w st4 [.reg 15, .reg 19, .reg 17, .reg 18, .reg 20, .reg 22, .reg 25, .reg 26] =
      some [partGXAddr workAddr cnt ecnt, partCsrAddr workAddr cnt ecnt,
        partInBAddr workAddr cnt ecnt, partOutRAddr workAddr cnt ecnt,
        partPruneWorkAddr workAddr cnt ecnt, cfg.C_cap, cfg.H, cfg.θ_out_nat] := by
    have h17_w : partInBAddr workAddr cnt ecnt < 2 ^ w := by
      rw [hGX_n] at hinB_w; dsimp only [partInBAddr] at hinB_w ⊢; omega
    have h18_w : partOutRAddr workAddr cnt ecnt < 2 ^ w := by
      rw [hGX_n] at houtR_w; dsimp only [partOutRAddr] at houtR_w ⊢; omega
    simp only [evalArgs, Expr.eval, (hr_eq4 15 (by omega)).trans ((hr_eq3 15 (by omega)).trans h15),
      (hr_eq4 19 (by omega)).trans ((hr_eq3 19 (by omega)).trans h19),
      (hr_eq4 17 (by omega)).trans ((hr_eq3 17 (by omega)).trans h17),
      (hr_eq4 18 (by omega)).trans ((hr_eq3 18 (by omega)).trans h18),
      (hr_eq4 20 (by omega)).trans ((hr_eq3 20 (by omega)).trans h20),
      (hr_eq4 22 (by omega)).trans hst3_22, (hr_eq4 25 (by omega)).trans hst3_25,
      (hr_eq4 26 (by omega)).trans hst3_26]
    rw [← hcfg_C, ← hcfg_H_eq, ← hcfg_θ]
  have hr_call_pw : Runs w p ω
      (.call 27 b_prune [.reg 15, .reg 19, .reg 17, .reg 18, .reg 20, .reg 22, .reg 25, .reg 26])
      st4 .normal st5 (8 + c_pw + 1) :=
    runs_call_iff.mpr ⟨_, pruneWrapProc, .returned 0, st_pw, c_pw, hcall_args, hp_prune, hr_pw,
      rfl, rfl, by simp [argsSize, Expr.size]⟩
  -- Combine steps 1-8
  have hseq_all : Runs w p ω (partPruneCallStmt b_csr b_prune) st .normal st5
      (6 + (6 + (2 + (c_log + (10 + (12 + (c_csr + (8 + c_pw + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    dsimp only [partPruneCallStmt, seqStmts]
    exact runs_seq_iff.mpr (Or.inr ⟨st0a, 6, _, ha22,
      runs_seq_iff.mpr (Or.inr ⟨st0b, 6, _, ha24,
        runs_seq_iff.mpr (Or.inr ⟨st1, 2, _, ha23,
          runs_seq_iff.mpr (Or.inr ⟨st2, c_log, _, hr_log,
            runs_seq_iff.mpr (Or.inr ⟨st2a, 10, _, ha25,
              runs_seq_iff.mpr (Or.inr ⟨st3, 12, _, ha26,
                runs_seq_iff.mpr (Or.inr ⟨st4, c_csr, 8 + c_pw + 1, hr_csr, hr_call_pw, rfl⟩),
                rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hr5_eq : ∀ r, r ≤ 20 → st5.regs r = st.regs r := fun r hr => by
    simp only [st5, Function.update_of_ne (by omega : r ≠ 27)]
    exact (hr_eq4 r (by omega)).trans (hr_eq3 r (by omega))
  have hfr_total : MemFrame mem st5.mem workAddr (workAddr + partWorkSize cnt ecnt H) := by
    intro a ha
    have ha_outR : a < partOutRAddr workAddr cnt ecnt ∨ partOutRAddr workAddr cnt ecnt + G_X.n ≤ a := by
      dsimp only [partOutRAddr, partWorkSize, pruneWorkSpace] at ha ⊢
      rw [hGX_n]
      rcases ha with ha_lo | ha_hi
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have ha_pw : a < partPruneWorkAddr workAddr cnt ecnt ∨
        partPruneWorkAddr workAddr cnt ecnt + pruneWorkSpace G_X.n G_X.m cfg.H ≤ a := by
      dsimp only [partPruneWorkAddr, partWorkSize, pruneWorkSpace] at ha ⊢
      rw [hGX_n, hGX_m, hcfg_H_eq]
      rcases ha with ha_lo | ha_hi
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have ha_csr : a < partCsrAddr workAddr cnt ecnt ∨
        partCsrAddr workAddr cnt ecnt + 2 * G_X.n + 1 + 4 * G_X.m ≤ a := by
      dsimp only [partCsrAddr, partWorkSize, pruneWorkSpace] at ha ⊢
      rw [hGX_n, hGX_m]
      rcases ha with ha_lo | ha_hi
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    calc st5.mem a = st_pw.mem a := rfl
      _ = st4.mem a := hpr_pw a ha_outR ha_pw
      _ = st3.mem a := hfr_csr4 a (by rcases ha_csr with h1 | h2 <;> [exact Or.inl h1; exact Or.inr (by omega)])
      _ = mem a := hm3_mem ▸ rfl
  refine ⟨.normal, st5, _, hseq_all, ?_, ?_⟩
  · refine ⟨(hr5_eq 0 (by omega)).trans h0, (hr5_eq 1 (by omega)).trans h1,
      (hr5_eq 2 (by omega)).trans h2, (hr5_eq 3 (by omega)).trans h3,
      (hr5_eq 4 (by omega)).trans h4, (hr5_eq 5 (by omega)).trans h5,
      (hr5_eq 6 (by omega)).trans h6, (hr5_eq 7 (by omega)).trans h7,
      (hr5_eq 8 (by omega)).trans h8, (hr5_eq 9 (by omega)).trans h9,
      (hr5_eq 10 (by omega)).trans h10, (hr5_eq 11 (by omega)).trans h11,
      (hr5_eq 12 (by omega)).trans h12, (hr5_eq 13 (by omega)).trans h13,
      (hr5_eq 14 (by omega)).trans h14, (hr5_eq 15 (by omega)).trans h15,
      (hr5_eq 16 (by omega)).trans h16, (hr5_eq 17 (by omega)).trans h17,
      (hr5_eq 18 (by omega)).trans h18, (hr5_eq 19 (by omega)).trans h19,
      (hr5_eq 20 (by omega)).trans h20, hfr_total, ?_⟩
    have hR_eq : (Finset.range cnt).filter (fun x => decide (st5.mem (partOutRAddr workAddr cnt ecnt + x) ≠ 0)) =
        (Finset.range G_X.n).filter (fun x => decide (st_pw.mem (partOutRAddr workAddr cnt ecnt + x) ≠ 0)) := by
      rw [hGX_n]
    rw [hR_eq]
    rw [hcfg_θ] at hdegR
    rw [hcfg_C] at hvolR
    dsimp only [cfg, pruneCfgOf] at hR_sub hexpR hdegR hvolR
    exact ⟨hR_sub, hexpR, hdegR, hvolR⟩
  · rw [hcfg_H_eq] at hc_pw
    dsimp only [cfg, pruneCfgOf] at hc_pw
    rw [hGX_n, hGX_m] at hc_pw hc_csr
    dsimp only at hc_csr ⊢
    simp only [argsSize, Expr.size] at hc_csr
    omega

/-! ## 3. `partEmitRStmt` Triple -/

lemma partEmitR_triple {w curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr : ℕ}
    (p : Program) (mem : ℕ → ℕ)
    (curG : Cited.Graph) (cnt off ecnt eoff H : ℕ)
    (hcnt_le : cnt ≤ curG.n)
    (hverts_lt : ∀ x < cnt, mem (grpPartVerts bufAddr curG.n + off + x) < curG.n)
    (hoff_le : off + cnt ≤ curG.n)
    (hlow_work : bufAddr + groupBufSize curG.n curG.m ≤ workAddr)
    (hwork_kept : workAddr + partWorkSize cnt ecnt H ≤ keptVertAddr)
    (hkept_arena : keptVertAddr + curG.n ≤ arenaPtr)
    (harena_w : arenaPtr + 2 + cnt < 2 ^ w)
    (_hlvl_w : lvl < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) :
    let selIdx : ℕ → List ℕ := fun j =>
      (List.range j).filter fun x => decide (mem (partOutRAddr workAddr cnt ecnt + x) ≠ 0)
    let R_list := (selIdx cnt).map fun x => mem (grpPartVerts bufAddr curG.n + off + x)
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      partEmitRStmt
      (fun o st =>
        match o with
        | .normal => False
        | .returned ptr =>
          if R_list.length < 2 then
            ptr = arenaPtr ∧ st.mem = mem
          else
            ptr = arenaPtr + 2 + R_list.length ∧
            ListAt st.mem arenaPtr ([lvl, R_list.length] ++ R_list) ∧
            (∀ u < curG.n,
              (u ∈ R_list → st.mem (keptVertAddr + u) = 1) ∧
              (u ∉ R_list → st.mem (keptVertAddr + u) = mem (keptVertAddr + u))) ∧
            (∀ a, ¬ (keptVertAddr ≤ a ∧ a < keptVertAddr + curG.n) →
                  ¬ (arenaPtr ≤ a ∧ a < ptr) → st.mem a = mem a))
      (fun _ => 95 * cnt + 45) := by
  intro selIdx R_list
  dsimp only [groupBufSize] at hlow_work
  have hw2 : 1 < 2 ^ w := by omega
  have hcnt_w : cnt < 2 ^ w := by omega
  have hwork_le_outR : workAddr ≤ partOutRAddr workAddr cnt ecnt := by
    dsimp only [partOutRAddr]; omega
  have houtR_hi : partOutRAddr workAddr cnt ecnt + cnt ≤ keptVertAddr := by
    dsimp only [partOutRAddr, partWorkSize, pruneWorkSpace] at hwork_kept ⊢; omega
  have hsel_len : ∀ j, (selIdx j).length ≤ j := fun j =>
    le_trans (List.length_filter_le _ _) (by simp)
  have hR_len : R_list.length = (selIdx cnt).length := List.length_map _
  -- Init: `r21 := 0`
  let Pre1 : State → Prop := fun st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = partGXAddr workAddr cnt ecnt ∧
    st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
    st.regs 17 = partInBAddr workAddr cnt ecnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 21 = 0 ∧
    st.mem = mem
  have hinit : Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      (.assign 21 (.const 0)) (normalPost Pre1) (fun _ => 2) := by
    intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, hm⟩
    refine runs_start_le ?_
    wram_run
    · exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        h16, h17, h18, h19, h20, by simp, hm⟩
    · wram_cost
  -- Loop 1: count `selIdx cnt`
  let Inv1 : ℕ → State → Prop := fun j st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = partGXAddr workAddr cnt ecnt ∧
    st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
    st.regs 17 = partInBAddr workAddr cnt ecnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 24 = j ∧
    st.regs 21 = (selIdx j).length ∧
    st.mem = mem
  let body1 := seqStmts
    [ .assign 25 (.load (.bin .add (.reg 18) (.reg 24)))
    , .cond (.bin .lt (.const 0) (.reg 25))
        (.assign 21 (.bin .add (.reg 21) (.const 1)))
        .nop ]
  have hloop1 := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 11)
    (body := body1) (P := Pre1) (Inv := Inv1) 20 0 cnt (Nat.zero_le cnt) hw2
    (fun _ => hcnt_w)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
        h19, h20, h21, hm⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17, h18, h19, h20, by simp, by simp [selIdx, h21], hm⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hjlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, h24, h21, hm⟩
      have hsucc : (selIdx (j + 1)).length = (selIdx j).length +
          if mem (partOutRAddr workAddr cnt ecnt + j) ≠ 0 then 1 else 0 := by
        simp only [selIdx, List.range_succ, List.filter_append, List.length_append,
          List.filter_cons, List.filter_nil]
        by_cases hnz : mem (partOutRAddr workAddr cnt ecnt + j) ≠ 0 <;> simp [hnz]
      have hsel_j := hsel_len j
      have hinc_w : (selIdx j).length + 1 < 2 ^ w := by omega
      refine runs_start_le ?_
      dsimp only [body1, seqStmts]
      wram_step; simp only [hm]
      wram_step
      · have hnz : mem (partOutRAddr workAddr cnt ecnt + j) ≠ 0 := by omega
        wram_run
        · exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, by simp, by simp [h21, hsucc, hnz], by simp⟩, by simp [h24]⟩
        · wram_cost
      · have hz : mem (partOutRAddr workAddr cnt ecnt + j) = 0 := by omega
        wram_run
        · exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, by simp, by simp [h21, hsucc, hz], by simp⟩, by simp [h24]⟩
        · wram_cost)
  -- Setup before Loop 2
  let Pre2 : State → Prop := fun st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = partGXAddr workAddr cnt ecnt ∧
    st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
    st.regs 17 = partInBAddr workAddr cnt ecnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 21 = R_list.length ∧
    st.regs 22 = arenaPtr + 2 ∧
    st.mem arenaPtr = lvl ∧
    st.mem (arenaPtr + 1) = R_list.length ∧
    (∀ a, a ≠ arenaPtr → a ≠ arenaPtr + 1 → st.mem a = mem a)
  let Inv2 : ℕ → State → Prop := fun j st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = partGXAddr workAddr cnt ecnt ∧
    st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
    st.regs 17 = partInBAddr workAddr cnt ecnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 21 = R_list.length ∧
    st.regs 24 = j ∧
    st.regs 22 = arenaPtr + 2 + (selIdx j).length ∧
    st.mem arenaPtr = lvl ∧
    st.mem (arenaPtr + 1) = R_list.length ∧
    (∀ t (ht : t < (selIdx j).length),
      st.mem (arenaPtr + 2 + t) = mem (grpPartVerts bufAddr curG.n + off + (selIdx j)[t]'ht)) ∧
    (∀ u < curG.n,
      let pref := (selIdx j).map (fun x => mem (grpPartVerts bufAddr curG.n + off + x))
      (u ∈ pref → st.mem (keptVertAddr + u) = 1) ∧
      (u ∉ pref → st.mem (keptVertAddr + u) = mem (keptVertAddr + u))) ∧
    (∀ a, ¬ (keptVertAddr ≤ a ∧ a < keptVertAddr + curG.n) →
          ¬ (arenaPtr ≤ a ∧ a < arenaPtr + 2 + (selIdx j).length) →
          a ≠ arenaPtr → a ≠ arenaPtr + 1 → st.mem a = mem a)
  let body2 := seqStmts
    [ .assign 25 (.load (.bin .add (.reg 18) (.reg 24)))
    , .cond (.bin .lt (.const 0) (.reg 25))
        (seqStmts
          [ .assign 26 (.load (.bin .add (.reg 12) (.reg 24)))
          , .store (.bin .add (.reg 7) (.reg 26)) (.const 1)
          , .store (.reg 22) (.reg 26)
          , .assign 22 (.bin .add (.reg 22) (.const 1)) ])
        .nop ]
  have hloop2 := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 11)
    (body := body2) (P := Pre2) (Inv := Inv2) 45 0 cnt (Nat.zero_le cnt) hw2
    (fun _ => hcnt_w)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
        h19, h20, h21, h22, hm0, hm1, hm_rest⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17, h18, h19, h20, h21, by simp, by simp [selIdx, h22], hm0, hm1,
        fun t ht => by simp [selIdx] at ht,
        fun u _ => ⟨fun hu => by simp [selIdx] at hu, fun _ => hm_rest _ (by omega) (by omega)⟩,
        fun a _ _ ha0 ha1 => hm_rest a ha0 ha1⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hjlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, h21, h24, h22, hm0, hm1, hpref, hkept, hrest⟩
      have hsel_j := hsel_len j
      have hout_eq : st.mem (partOutRAddr workAddr cnt ecnt + j) =
          mem (partOutRAddr workAddr cnt ecnt + j) :=
        hrest _ (by omega) (by omega) (by omega) (by omega)
      refine runs_start_le ?_
      dsimp only [body2, seqStmts]
      wram_step; simp only [hout_eq]
      wram_step
      · have hnz : mem (partOutRAddr workAddr cnt ecnt + j) ≠ 0 := by omega
        have hvert_eq : st.mem (grpPartVerts bufAddr curG.n + off + j) =
            mem (grpPartVerts bufAddr curG.n + off + j) := by
          dsimp only [grpPartVerts]
          exact hrest _ (by omega) (by omega) (by omega) (by omega)
        set u := mem (grpPartVerts bufAddr curG.n + off + j)
        have hu_lt : u < curG.n := hverts_lt j hjlt
        have hsel_succ : selIdx (j + 1) = selIdx j ++ [j] := by
          simp [selIdx, List.range_succ, List.filter_append, hnz]
        have hpref_succ : ((selIdx (j + 1)).map fun x => mem (grpPartVerts bufAddr curG.n + off + x)) =
            ((selIdx j).map fun x => mem (grpPartVerts bufAddr curG.n + off + x)) ++ [u] := by
          simp [hsel_succ, u]
        have hu_w : u < 2 ^ w := by omega
        have hka_w : keptVertAddr + u < 2 ^ w := by omega
        have har_next_w : arenaPtr + 2 + (selIdx j).length + 1 < 2 ^ w := by omega
        dsimp only [grpPartVerts] at h12
        have hvert_eq' : st.mem (bufAddr + 7 * curG.n + 1 + off + j) = u := by
          simpa [grpPartVerts, u] using hvert_eq
        wram_step; simp only [h12, h24, hvert_eq']
        wram_run
        · refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, h21, by simp, ?_, ?_, ?_, fun t ht => ?_, fun v hv => ?_, ?_⟩,
            by simp [h24]⟩
          · rw [hsel_succ, List.length_append, List.length_singleton]; simp [h22, Nat.add_assoc]
          · simp [h7, h22, Function.update_of_ne (by omega : arenaPtr ≠ arenaPtr + 2 + (selIdx j).length),
              Function.update_of_ne (by omega : arenaPtr ≠ keptVertAddr + u), hm0]
          · simp [h7, h22, Function.update_of_ne (by omega : arenaPtr + 1 ≠ arenaPtr + 2 + (selIdx j).length),
              Function.update_of_ne (by omega : arenaPtr + 1 ≠ keptVertAddr + u), hm1]
          · dsimp only
            have ht_len : t < (selIdx j).length + 1 := by
              have hlen_succ : (selIdx (j + 1)).length = (selIdx j).length + 1 := by
                simp [hsel_succ]
              omega
            rcases Nat.lt_succ_iff_lt_or_eq.mp ht_len with ht' | rfl
            · have hp_t := hpref t ht'
              simp only [h7, h22, Function.update_of_ne (by omega : arenaPtr + 2 + t ≠ arenaPtr + 2 + (selIdx j).length),
                Function.update_of_ne (by omega : arenaPtr + 2 + t ≠ keptVertAddr + u)]
              rw [hp_t]
              have hget_eq : (selIdx (j + 1))[t]'ht = (selIdx j)[t]'ht' := by
                simp [hsel_succ, List.getElem_append_left ht']
              rw [hget_eq]
            · simp only [h7, h22, Function.update_self, u]
              have hget_eq : (selIdx (j + 1))[(selIdx j).length]'ht = j := by
                simp [hsel_succ, List.getElem_append_right le_rfl]
              rw [hget_eq]
          · dsimp only
            rw [hpref_succ, List.mem_append, List.mem_singleton]
            by_cases hvu : v = u
            · refine ⟨fun _ => ?_, fun hneg => absurd (Or.inr hvu) hneg⟩
              simp [h7, h22, hvu, Function.update_of_ne (by omega : keptVertAddr + u ≠ arenaPtr + 2 + (selIdx j).length),
                Function.update_self]
            · have hk_v := hkept v hv
              dsimp only at hk_v
              simp only [h7, h22, Function.update_of_ne (by omega : keptVertAddr + v ≠ arenaPtr + 2 + (selIdx j).length),
                Function.update_of_ne (by omega : keptVertAddr + v ≠ keptVertAddr + u)]
              exact ⟨fun hmem => hk_v.1 (by rcases hmem with h | h; exact h; exact absurd h hvu),
                fun hneg => hk_v.2 (fun h => hneg (Or.inl h))⟩
          · intro a ha1 ha2 ha0 ha1'
            rw [hsel_succ, List.length_append, List.length_singleton] at ha2
            simp only [h7, h22, Function.update_of_ne (by omega : a ≠ arenaPtr + 2 + (selIdx j).length),
              Function.update_of_ne (by omega : a ≠ keptVertAddr + u)]
            exact hrest a ha1 (by omega) ha0 ha1'
        · wram_cost
      · have hz : mem (partOutRAddr workAddr cnt ecnt + j) = 0 := by omega
        have hsel_succ : selIdx (j + 1) = selIdx j := by
          simp [selIdx, List.range_succ, List.filter_append, hz]
        wram_run
        · refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, h21, by simp, ?_, hm0, hm1, fun t ht => ?_, fun v hv => ?_, ?_⟩,
            by simp [h24]⟩
          · rw [hsel_succ]; exact h22
          · have ht' : t < (selIdx j).length := by
              have hlen_succ : (selIdx (j + 1)).length = (selIdx j).length := by rw [hsel_succ]
              omega
            rw [hpref t ht']
            congr 2
            simp [hsel_succ]
          · rw [hsel_succ]; exact hkept v hv
          · rw [hsel_succ]; exact hrest
        · wram_cost)
  -- Execute full `partEmitRStmt`
  intro st ω hpre
  rcases hinit st ω hpre with ⟨o1, st1, c1, hr1, ho1, hc1⟩
  cases o1 with
  | returned _ => exact False.elim ho1
  | normal =>
    rcases hloop1 st1 ω ho1 with ⟨o2, st2, c2, hr2, ho2, hc2⟩
    cases o2 with
    | returned _ => exact False.elim ho2
    | normal =>
      rcases ho2 with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16,
        s17, s18, s19, s20, s24, s21, hm2⟩
      by_cases hlt : R_list.length < 2
      · have h21_lt : st2.regs 21 < 2 := by rw [s21, ← hR_len]; exact hlt
        have hcond_ev : (Expr.bin .lt (.reg 21) (.const 2)).eval w st2 = some 1 := by
          simp [Expr.eval, BinOp.eval, s21, ← hR_len, hlt, show (2 : ℕ) < 2 ^ w by omega, hw2]
        have hret : Runs w p ω (.ret (.reg 8)) st2 (.returned arenaPtr) st2 2 :=
          runs_ret_iff.mpr ⟨arenaPtr, by simp [Expr.eval, s8], rfl, rfl, rfl⟩
        have htail : Runs w p ω
            (seqStmts
              [ .cond (.bin .lt (.reg 21) (.const 2)) (.ret (.reg 8)) .nop
              , .store (.reg 8) (.reg 3)
              , .store (.bin .add (.reg 8) (.const 1)) (.reg 21)
              , .assign 22 (.bin .add (.reg 8) (.const 2))
              , forRange 24 (.const 0) (.reg 11) body2
              , .ret (.reg 22) ])
            st2 (.returned arenaPtr) st2 7 := by
          dsimp only [seqStmts]
          exact runs_seq_iff.mpr (Or.inl ⟨arenaPtr, 6,
            runs_cond_iff.mpr ⟨1, 2, hcond_ev, by simpa using hret, rfl⟩, rfl, rfl⟩)
        have hseq : Runs w p ω partEmitRStmt st (.returned arenaPtr) st2 (c1 + (c2 + 7 + 1) + 1) := by
          dsimp only [partEmitRStmt, seqStmts]
          exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1,
            runs_seq_iff.mpr (Or.inr ⟨st2, c2, 7, hr2, htail, rfl⟩), rfl⟩)
        refine ⟨.returned arenaPtr, st2, _, hseq, by simp [hlt, hm2], ?_⟩
        dsimp only at hc1 hc2 ⊢
        simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at hc2
        omega
      · have h21_ge : 2 ≤ st2.regs 21 := by rw [s21, ← hR_len]; omega
        have hcond_ev : (Expr.bin .lt (.reg 21) (.const 2)).eval w st2 = some 0 := by
          simp [Expr.eval, BinOp.eval, show ¬ st2.regs 21 < 2 by omega, show (2 : ℕ) < 2 ^ w by omega]
        have hnop : Runs w p ω .nop st2 .normal st2 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
        have hcond_r : Runs w p ω (.cond (.bin .lt (.reg 21) (.const 2)) (.ret (.reg 8)) .nop)
            st2 .normal st2 5 :=
          runs_cond_iff.mpr ⟨0, 1, hcond_ev, by simpa using hnop, rfl⟩
        -- Setup stores and r22 step-by-step
        have hsel_c : R_list.length ≤ cnt := hR_len.symm ▸ hsel_len cnt
        let st2a : State := { st2 with mem := Function.update st2.mem arenaPtr lvl }
        let st2b : State := { st2a with mem := Function.update st2a.mem (arenaPtr + 1) R_list.length }
        let st3 : State := { st2b with regs := Function.update st2b.regs 22 (arenaPtr + 2) }
        have hs_lvl : Runs w p ω (.store (.reg 8) (.reg 3)) st2 .normal st2a 3 :=
          runs_store_iff.mpr ⟨arenaPtr, lvl, by simp [Expr.eval, s8],
            by simp [Expr.eval, s3], rfl, rfl, rfl⟩
        have hs_len : Runs w p ω (.store (.bin .add (.reg 8) (.const 1)) (.reg 21)) st2a .normal st2b 5 :=
          runs_store_iff.mpr ⟨arenaPtr + 1, R_list.length,
            by simp [st2a, Expr.eval, BinOp.eval, s8, hw2, show arenaPtr + 1 < 2 ^ w by omega],
            by simp [st2a, Expr.eval, s21, hR_len], rfl, rfl, rfl⟩
        have ha_22 : Runs w p ω (.assign 22 (.bin .add (.reg 8) (.const 2))) st2b .normal st3 4 :=
          runs_assign_iff.mpr ⟨arenaPtr + 2,
            by simp [st2b, st2a, Expr.eval, BinOp.eval, s8, show (2 : ℕ) < 2 ^ w by omega,
              show arenaPtr + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have hpre2 : Pre2 st3 :=
          ⟨by simp [st3, st2b, st2a, s0], by simp [st3, st2b, st2a, s1], by simp [st3, st2b, st2a, s2],
           by simp [st3, st2b, st2a, s3], by simp [st3, st2b, st2a, s4], by simp [st3, st2b, st2a, s5],
           by simp [st3, st2b, st2a, s6], by simp [st3, st2b, st2a, s7], by simp [st3, st2b, st2a, s8],
           by simp [st3, st2b, st2a, s9], by simp [st3, st2b, st2a, s10], by simp [st3, st2b, st2a, s11],
           by simp [st3, st2b, st2a, s12], by simp [st3, st2b, st2a, s13], by simp [st3, st2b, st2a, s14],
           by simp [st3, st2b, st2a, s15], by simp [st3, st2b, st2a, s16], by simp [st3, st2b, st2a, s17],
           by simp [st3, st2b, st2a, s18], by simp [st3, st2b, st2a, s19], by simp [st3, st2b, st2a, s20],
           by simp [st3, st2b, st2a, s21, hR_len], by simp [st3],
           by simp [st3, st2b, st2a],
           by simp [st3, st2b],
           fun a ha0 ha1 => by simp [st3, st2b, st2a, Function.update_of_ne ha1, Function.update_of_ne ha0, hm2]⟩
        rcases hloop2 st3 ω hpre2 with ⟨o4, st4, c4, hr4, ho4, hc4⟩
        cases o4 with
        | returned _ => exact False.elim ho4
        | normal =>
          rcases ho4 with ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
            t16, t17, t18, t19, t20, t21, t24, t22, tm0, tm1, hpref4, hkept4, hrest4⟩
          have hret4 : Runs w p ω (.ret (.reg 22)) st4 (.returned (arenaPtr + 2 + R_list.length)) st4 2 :=
            runs_ret_iff.mpr ⟨arenaPtr + 2 + R_list.length,
              by simp [Expr.eval, t22, hR_len], rfl, rfl, rfl⟩
          have hseq : Runs w p ω partEmitRStmt st (.returned (arenaPtr + 2 + R_list.length)) st4
              (c1 + (c2 + (5 + (3 + (5 + (4 + (c4 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
            dsimp only [partEmitRStmt, seqStmts]
            exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1,
              runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hr2,
                runs_seq_iff.mpr (Or.inr ⟨st2, 5, _, hcond_r,
                  runs_seq_iff.mpr (Or.inr ⟨st2a, 3, _, hs_lvl,
                    runs_seq_iff.mpr (Or.inr ⟨st2b, 5, _, hs_len,
                      runs_seq_iff.mpr (Or.inr ⟨st3, 4, _, ha_22,
                        runs_seq_iff.mpr (Or.inr ⟨st4, c4, 2, hr4, hret4, rfl⟩),
                        rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
          have hlistAt : ListAt st4.mem arenaPtr ([lvl, R_list.length] ++ R_list) := by
            rw [ListAt]
            intro t ht
            simp only [List.length_append, List.length_cons, List.length_nil] at ht
            match t with
            | 0 => simp [tm0]
            | 1 => simp [tm1]
            | t' + 2 =>
              have ht'_lt : t' < (selIdx cnt).length := by omega
              have hpt := hpref4 t' ht'_lt
              rw [show arenaPtr + (t' + 2) = arenaPtr + 2 + t' by omega, hpt]
              have hlen2 : ([lvl, R_list.length] : List ℕ).length = 2 := rfl
              rw [List.getElem_append_right (by omega : ([lvl, R_list.length] : List ℕ).length ≤ t' + 2)]
              simp [R_list]
          refine ⟨.returned (arenaPtr + 2 + R_list.length), st4, _, hseq, ?_, ?_⟩
          · dsimp only
            simp only [hlt, ↓reduceIte]
            exact ⟨trivial, hlistAt, hkept4, fun a ha1 ha2 => by
              by_cases ha0 : a = arenaPtr
              · subst ha0; omega
              · by_cases ha1' : a = arenaPtr + 1
                · subst ha1'; omega
                · exact hrest4 a ha1 (by omega) ha0 ha1'⟩
          · dsimp only at hc1 hc2 hc4 ⊢
            simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at hc2 hc4
            omega

end MinCostFlow.Expander
