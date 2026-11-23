module

public import MinCostFlow.Expander.DecomposePartCallEmit

/-!
# Partition Pruning: Full `partPruneProc` Execution Specification

Proves `partPrune_runs` for `partPruneProc`, tying together setup, compressed graph copy,
degree computation, bad-twin early exit, CSR/pruning call, and component emission.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 4. Full `partPruneProc` Execution Lemma -/

private lemma pairwise_lt_map_tab_filter (f : ℕ → ℕ) (n : ℕ)
    (hstrict : (tab n f).Pairwise (· < ·)) (L : List ℕ) (hL_sub : ∀ x ∈ L, x < n)
    (hL_pw : L.Pairwise (· < ·)) :
    (L.map f).Pairwise (· < ·) := by
  have hlt_map : ∀ {x y : ℕ}, x < n → y < n → x < y → f x < f y := by
    intro x y hx hy hxy
    have htab_pw : ((List.range n).map f).Pairwise (· < ·) := hstrict
    rw [List.pairwise_map] at htab_pw
    have hmem : ∀ a b, a < b → a < n → b < n →
        List.Pairwise (fun a b => f a < f b) (List.range n) → f a < f b := by
      intro a b hab ha hb hpw
      have h := (List.pairwise_iff_getElem.mp hpw) a b (by simp [ha]) (by simp [hb]) (by simp [hab])
      simp only [List.getElem_range] at h
      exact h
    exact hmem x y hxy hx hy htab_pw
  rw [List.pairwise_map]
  induction L with
  | nil => exact .nil
  | cons a rest ih =>
    rw [List.pairwise_cons] at hL_pw ⊢
    refine ⟨fun b hb => hlt_map (hL_sub a List.mem_cons_self)
        (hL_sub b (List.mem_cons_of_mem _ hb)) (hL_pw.1 b hb),
      ih (fun b hb => hL_sub b (List.mem_cons_of_mem _ hb)) hL_pw.2⟩

private lemma partPrune_noBadTwin
    {curG : Cited.Graph} {D D_phi bufAddr off cnt : ℕ} {Y : Finset ℕ} {φ_B1 : ℝ}
    (hV : curG.IsValid) (hD : 1 ≤ D) (hDphi : 200 ≤ D_phi) (hφ_unif : 1 / (D_phi : ℝ) ≤ φ_B1)
    (hexpY : (twinGraph D curG).IsConductanceExpanderOn Y φ_B1)
    {actVerts : List ℕ} (hstrict : actVerts.Pairwise (· < ·)) (hactX : actVerts.toFinset = partX curG.n Y)
    (hlen : actVerts.length = cnt) (hGX_n : (compressPartGraph actVerts (curG.inside (partX curG.n Y))).n = cnt)
    (mem mem4 : ℕ → ℕ)
    (hinB : ∀ x < cnt,
      (compressPartGraph actVerts (curG.inside (partX curG.n Y))).degIn
        (compressPartGraph actVerts (curG.inside (partX curG.n Y))).verts x * D_phi < D →
      mem4 (grpSameTwin bufAddr curG.n + mem4 (grpPartVerts bufAddr curG.n + off + x)) = 0)
    (hpv : ∀ x < cnt, mem4 (grpPartVerts bufAddr curG.n + off + x) = mem (grpPartVerts bufAddr curG.n + off + x))
    (hst : ∀ x < cnt,
      mem4 (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) =
      mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)))
    (htwin_eq_iff : ∀ x < cnt,
      mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) ≠ 0 ↔
      2 * actVerts.getD x 0 + 1 ∈ Y) :
    ∀ x < actVerts.length,
      curG.degIn (partX curG.n Y) (actVerts.getD x 0) * D_phi < D →
      2 * actVerts.getD x 0 + 1 ∉ Y := by
  intro x hx hdeg_cur
  have hx_cnt : x < cnt := hlen ▸ hx
  have hbound := (prune_compressed_part_pre hV hD hDphi hφ_unif hexpY hstrict hactX).1
  have hdeg_eq := compressPartGraph_degIn hstrict hbound
    (S_loc := Finset.range actVerts.length) le_rfl hx
  have himg : (Finset.range actVerts.length).image (fun i => actVerts.getD i 0) = partX curG.n Y := by
    rw [compressPartGraph_image_f_verts, hactX]
  dsimp only at hdeg_eq
  rw [himg, hactX] at hdeg_eq
  set G_X := compressPartGraph actVerts (curG.inside (partX curG.n Y))
  have hGXv : G_X.verts = Finset.range actVerts.length := by
    dsimp only [Cited.Graph.verts]; rw [hGX_n, hlen]
  have hdeg_loc : G_X.degIn G_X.verts x * D_phi < D := by
    rw [hGXv, hdeg_eq]; exact hdeg_cur
  have htw0 := hinB x hx_cnt hdeg_loc
  rw [hpv x hx_cnt, hst x hx_cnt] at htw0
  intro hY
  exact absurd ((htwin_eq_iff x hx_cnt).mpr hY) (by omega)

theorem partPrune_runs {w : ℕ} {p : Program} {b_csr b_prune : ℕ}
    (hp_csr : MeetsContract w p b_csr (buildCsrContract w))
    (hp_prune : p.procs[b_prune]? = some pruneWrapProc)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr : ℕ)
    (curG : Cited.Graph) (hV : curG.IsValid) (hL : curG.IsLoopless)
    (hD : 1 ≤ D) (hDphi : 200 ≤ D_phi)
    (label : List ℕ) (φ_B1 : ℝ) (hφ_unif : 1 / (D_phi : ℝ) ≤ φ_B1)
    (_hdecExp : Cited.IsExpanderDecomposition (twinGraph D curG) (1 / 200 : ℝ) φ_B1 label)
    (hga : GraphAt mem curGAddr curG)
    (hcur_buf : curGAddr + 2 + 2 * curG.m ≤ bufAddr)
    (k cnt off ecnt eoff : ℕ)
    (_hk : 1 ≤ k) (hqk : q < k) (hkn : k ≤ curG.n)
    (hcnt_eq : mem (grpPartCnt bufAddr curG.n + q) = cnt)
    (hoff_eq : mem (grpPartOff bufAddr curG.n + q) = off)
    (hecnt_eq : mem (grpEdgeCnt bufAddr curG.n + q) = ecnt)
    (heoff_eq : mem (grpEdgeOff bufAddr curG.n + q) = eoff)
    (hoff_le : off + cnt ≤ curG.n)
    (heoff_le : eoff + ecnt ≤ curG.m)
    (hlbl_q : let L := mem (grpUniqLbl bufAddr curG.n + q)
      let Y := (Finset.range (2 * curG.n)).filter fun z => label.getD z 0 = L
      (tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)).toFinset = partX curG.n Y ∧
      ((twinGraph D curG).IsConductanceExpanderOn Y φ_B1))
    (htwin_spec : ∀ u < curG.n,
      mem (grpSameTwin bufAddr curG.n + u) < 2 ^ w ∧
      (mem (grpSameTwin bufAddr curG.n + u) ≠ 0 ↔
        2 * u + 1 ∈ (Finset.range (2 * curG.n)).filter fun z => label.getD z 0 = label.getD (2 * u) 0))
    (hpartId_spec : ∀ u < curG.n,
      mem (grpPartId bufAddr curG.n + u) < k ∧
      (mem (grpPartId bufAddr curG.n + u) = q ↔
        label.getD (2 * u) 0 = mem (grpUniqLbl bufAddr curG.n + q)))
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
        mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t) + 1) = es[t].2)
    (hbuf : bufAddr + groupBufSize curG.n curG.m + 2 < 2 ^ w)
    (hlow_work : bufAddr + groupBufSize curG.n curG.m ≤ workAddr)
    (hwork_kept : workAddr + partWorkSize curG.n curG.m
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) ≤ keptVertAddr)
    (hkept_arena : keptVertAddr + curG.n ≤ arenaPtr)
    (harena_w : arenaPtr + 2 + cnt < 2 ^ w)
    (harith_w : 8 * (4 * D_phi + 2) * curG.m + 4 * (4 * D_phi + 2) + 2 * curG.n + 2 * curG.m +
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) + 16 < 2 ^ w)
    (hmul_w : 2 * curG.m * D_phi + D + 4 < 2 ^ w)
    (hD_w : D + 3 * D_phi < 2 ^ w)
    (hlvl_w : lvl < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) :
    let L := mem (grpUniqLbl bufAddr curG.n + q)
    let Y := (Finset.range (2 * curG.n)).filter fun z => label.getD z 0 = L
    let X := partX curG.n Y
    let args := [curGAddr, bufAddr, q, lvl, D, D_phi, workAddr, keptVertAddr, arenaPtr]
    let H_max := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
    ∃ (st' : State) (c arenaPtr' : ℕ) (R : Finset ℕ) (R_list : List ℕ),
      Runs w p ω (partPruneProc b_csr b_prune) (startState args mem pos) (.returned arenaPtr') st' c ∧
      c ≤ partPruneCost cnt ecnt D_phi ∧
      arenaPtr ≤ arenaPtr' ∧
      arenaPtr' ≤ arenaPtr + 2 + 4 * ecnt ∧
      R_list.Pairwise (· < ·) ∧
      R_list.toFinset = R ∧
      (if R = ∅ then
        arenaPtr' = arenaPtr ∧
        ∀ u < curG.n, st'.mem (keptVertAddr + u) = mem (keptVertAddr + u)
      else
        2 ≤ R_list.length ∧
        arenaPtr' = arenaPtr + 2 + R_list.length ∧
        ListAt st'.mem arenaPtr ([lvl, R_list.length] ++ R_list) ∧
        ∀ u < curG.n,
          (u ∈ R → st'.mem (keptVertAddr + u) = 1) ∧
          (u ∉ R → st'.mem (keptVertAddr + u) = mem (keptVertAddr + u))) ∧
      (∀ a, ¬ (workAddr ≤ a ∧ a < workAddr + partWorkSize curG.n curG.m H_max) →
            ¬ (keptVertAddr ≤ a ∧ a < keptVertAddr + curG.n) →
            ¬ (arenaPtr ≤ a ∧ a < arenaPtr') → st'.mem a = mem a) ∧
      R ⊆ X ∧
      (R = ∅ ∨
        (2 ≤ R.card ∧ curG.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
          ∀ v ∈ R, (1 / (3 * (D_phi : ℝ))) * (D : ℝ) ≤ (curG.degIn R v : ℝ))) ∧
      (curG.inside X).length - (curG.inside R).length ≤ 15 * (twinGraph D curG).cut Y := by
  intro L Y X args H_max
  rcases hlbl_q with ⟨hactX, hexpY⟩
  set actVerts := tab cnt fun t => mem (grpPartVerts bufAddr curG.n + off + t)
  set G_X := compressPartGraph actVerts (curG.inside X)
  have hcomp := compressPartGraph_eq_of_groupEdges hV hga hverts_eq hstrict hlid_inv hes
  rcases hcomp with ⟨hGX_n, hGX_m, hedges⟩
  rw [hactX] at hGX_n hGX_m hedges
  have hcnt_le : cnt ≤ curG.n := by omega
  have hecnt_le : ecnt ≤ curG.m := by omega
  have hH_le : 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2 ≤ H_max := by
    have hlog : Nat.log 2 (2 * ecnt + 1) ≤ Nat.log 2 (2 * curG.m + 1) := Nat.log_mono_right (by omega)
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)) 2
  have hwork_sz_le : partWorkSize cnt ecnt
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) ≤
      partWorkSize curG.n curG.m H_max :=
    partWorkSize_mono hcnt_le hecnt_le hH_le
  dsimp only [H_max] at hwork_sz_le
  have harith_sub : 8 * (4 * D_phi + 2) * ecnt + 4 * (4 * D_phi + 2) + 2 * cnt + 2 * ecnt +
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) + 16 < 2 ^ w := by
    have hmul : 8 * (4 * D_phi + 2) * ecnt ≤ 8 * (4 * D_phi + 2) * curG.m :=
      Nat.mul_le_mul_left _ hecnt_le
    omega
  have hwork_w : workAddr + partWorkSize cnt ecnt
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) + 2 < 2 ^ w := by omega
  have hwork_kept_sub : workAddr + partWorkSize cnt ecnt
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) ≤ keptVertAddr :=
    le_trans (Nat.add_le_add_left hwork_sz_le workAddr) hwork_kept
  have hverts_lt : ∀ x < cnt, mem (grpPartVerts bufAddr curG.n + off + x) < curG.n := by
    intro x hx
    have hmem : mem (grpPartVerts bufAddr curG.n + off + x) ∈ actVerts := by
      simp only [actVerts, tab, List.mem_map, List.mem_range]
      exact ⟨x, hx, rfl⟩
    exact ((hverts_eq _).mp hmem).1
  have htwin_eq_iff : ∀ x < cnt,
      mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) ≠ 0 ↔
      2 * actVerts.getD x 0 + 1 ∈ Y := by
    intro x hx
    have hu_lt := hverts_lt x hx
    have hget : actVerts.getD x 0 = mem (grpPartVerts bufAddr curG.n + off + x) := by
      simp [actVerts, tab, List.getD_eq_getElem?_getD, hx]
    rw [hget]
    have hmem_act : mem (grpPartVerts bufAddr curG.n + off + x) ∈ actVerts := by
      simp [actVerts, tab]; exact ⟨x, hx, rfl⟩
    have hpid_q := ((hverts_eq _).mp hmem_act).2
    have hL_eq : label.getD (2 * mem (grpPartVerts bufAddr curG.n + off + x)) 0 = L :=
      ((hpartId_spec _ hu_lt).2).mp hpid_q
    have htw := (htwin_spec _ hu_lt).2
    rw [hL_eq] at htw
    exact htw
  let st₀ := startState [curGAddr, bufAddr, q, lvl, D, D_phi, workAddr, keptVertAddr, arenaPtr] mem pos
  have hw2 : 1 < 2 ^ w := by omega
  have hw2_lt : 2 < 2 ^ w := by omega
  dsimp only [groupBufSize] at hbuf hlow_work
  have hcurG_n_eq : mem curGAddr = curG.n := graphAt_n hga
  have hcurG_m_eq : mem (curGAddr + 1) = curG.m := graphAt_m hga
  have hcnt_mem : mem (bufAddr + 4 * curG.n + q) = cnt := by simpa [grpPartCnt] using hcnt_eq
  have hn_w : curG.n < 2 ^ w := by omega
  have hm_w : curG.m < 2 ^ w := by omega
  have hcnt_w : cnt < 2 ^ w := by omega
  have hcurG_w : curGAddr < 2 ^ w := by omega
  have hbuf_w : bufAddr + 4 * curG.n + q < 2 ^ w := by omega
  have hgrpPV_lt : ∀ x < cnt, grpPartVerts bufAddr curG.n + off + x < workAddr := fun x hx => by
    dsimp only [grpPartVerts]; omega
  have hgrpST_lt : ∀ u < curG.n, grpSameTwin bufAddr curG.n + u < workAddr := fun u hu => by
    dsimp only [grpSameTwin]; omega
  have hpart_gx_inB : ∀ j < 2 + 2 * ecnt,
      partGXAddr workAddr cnt ecnt + j < partInBAddr workAddr cnt ecnt := fun j hj => by
    dsimp only [partGXAddr, partInBAddr]; omega
  have hpart_gx_degX : ∀ j < 2 + 2 * ecnt,
      partGXAddr workAddr cnt ecnt + j < partDegXAddr workAddr cnt ecnt := fun j hj => by
    dsimp only [partGXAddr, partDegXAddr]; omega
  have hkept_sub_u : ∀ u < curG.n,
      workAddr + partWorkSize cnt ecnt (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) ≤ keptVertAddr + u :=
    fun u hu => by omega
  have hwork_ge_sub : ∀ a,
      (a < workAddr ∨ workAddr + partWorkSize curG.n curG.m (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) ≤ a) →
      (a < workAddr ∨ workAddr + partWorkSize cnt ecnt (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) ≤ a) := by
    intro a ha
    rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]
  let st0a : State := { st₀ with regs := Function.update st₀.regs 9 curG.n }
  let st0b : State := { st0a with regs := Function.update st0a.regs 10 curG.m }
  let st₁ : State := { st0b with regs := Function.update st0b.regs 11 cnt }
  have ha9 : Runs w p ω (.assign 9 (.load (.reg 0))) st₀ .normal st0a 3 :=
    runs_assign_iff.mpr ⟨curG.n, by
      simp [st₀, startState, List.getD, Expr.eval, hcurG_n_eq], rfl, rfl, rfl⟩
  have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const 1)))) st0a .normal st0b 5 :=
    runs_assign_iff.mpr ⟨curG.m, by
      simp [st0a, st₀, startState, List.getD, Expr.eval, BinOp.eval, hw2,
        show curGAddr + 1 < 2 ^ w by omega, hcurG_m_eq], rfl, rfl, rfl⟩
  have ha11 : Runs w p ω
      (.assign 11 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 4) (.reg 9))) (.reg 2))))
      st0b .normal st₁ 9 :=
    runs_assign_iff.mpr ⟨cnt, by
      simp [st0b, st0a, st₀, startState, List.getD, Expr.eval, BinOp.eval,
        show (4 : ℕ) < 2 ^ w by omega, show 4 * curG.n < 2 ^ w by omega,
        show bufAddr + 4 * curG.n < 2 ^ w by omega, hbuf_w, hcnt_mem], rfl, rfl, rfl⟩
  by_cases hcnt_lt2 : cnt < 2
  · have hcond_ev : (Expr.bin .lt (.reg 11) (.const 2)).eval w st₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, st₁, hcnt_lt2, hw2, hw2_lt]
    have hret : Runs w p ω (.ret (.reg 8)) st₁ (.returned arenaPtr) st₁ 2 :=
      runs_ret_iff.mpr ⟨arenaPtr, by
        simp [Expr.eval, st₁, st0b, st0a, st₀, startState, List.getD], rfl, rfl, rfl⟩
    have htail : Runs w p ω
        (seqStmts
          [ .cond (.bin .lt (.reg 11) (.const 2)) (.ret (.reg 8)) .nop
          , partPtrSetupStmt, partBuildGXStmt, partDegXStmt, partInBStmt,
            partPruneCallStmt b_csr b_prune, partEmitRStmt ])
        st₁ (.returned arenaPtr) st₁ 7 := by
      dsimp only [seqStmts]
      exact runs_seq_iff.mpr (Or.inl ⟨arenaPtr, 6,
        runs_cond_iff.mpr ⟨1, 2, hcond_ev, by simpa using hret, rfl⟩, rfl, rfl⟩)
    have hseq : Runs w p ω (partPruneProc b_csr b_prune) st₀ (.returned arenaPtr) st₁
        (3 + (5 + (9 + 7 + 1) + 1) + 1) := by
      dsimp only [partPruneProc, seqStmts]
      exact runs_seq_iff.mpr (Or.inr ⟨st0a, 3, _, ha9,
        runs_seq_iff.mpr (Or.inr ⟨st0b, 5, _, ha10,
          runs_seq_iff.mpr (Or.inr ⟨st₁, 9, 7, ha11, htail, rfl⟩), rfl⟩), rfl⟩)
    have hX_card : X.card ≤ 1 := by
      dsimp only [X]
      rw [← hactX, List.toFinset_card_of_nodup (hstrict.imp fun h => ne_of_lt h)]
      simp only [actVerts, tab, List.length_map, List.length_range]
      omega
    have hins_nil : curG.inside X = [] := inside_card_le_one_eq_nil hL hX_card
    have hcost_le : 3 + (5 + (9 + 7 + 1) + 1) + 1 ≤ partPruneCost cnt ecnt D_phi := by
      unfold partPruneCost pruneTimeBound; dsimp only; omega
    refine ⟨st₁, 3 + (5 + (9 + 7 + 1) + 1) + 1, arenaPtr, ∅, [], hseq, hcost_le, le_rfl,
      by omega, .nil, by simp, ?_, fun a _ _ _ => rfl, Finset.empty_subset X, Or.inl rfl, ?_⟩
    · simp only [↓reduceIte]
      exact ⟨trivial, fun _ _ => rfl⟩
    · rw [hins_nil]; simp
  · have hcnt_ge2 : 2 ≤ cnt := by omega
    have hcond_ev : (Expr.bin .lt (.reg 11) (.const 2)).eval w st₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, st₁, show ¬ cnt < 2 by omega, hw2_lt]
    have hnop : Runs w p ω .nop st₁ .normal st₁ 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    have hcond_r : Runs w p ω (.cond (.bin .lt (.reg 11) (.const 2)) (.ret (.reg 8)) .nop)
        st₁ .normal st₁ 5 :=
      runs_cond_iff.mpr ⟨0, 1, hcond_ev, by simpa using hnop, rfl⟩
    -- Chaining `partPtrSetup`, `partBuildGX`, `partDegX`
    have hptr := partPtrSetup_triple (curGAddr := curGAddr) (bufAddr := bufAddr) (q := q)
      (lvl := lvl) (D := D) (D_phi := D_phi) (workAddr := workAddr) (keptVertAddr := keptVertAddr)
      (arenaPtr := arenaPtr) (p := p) (mem := mem) curG k cnt off ecnt eoff _hk hqk hkn
      hcnt_eq hoff_eq hecnt_eq heoff_eq hoff_le heoff_le
      (by dsimp only [groupBufSize]; omega)
      (by dsimp only [partPruneWorkAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega)
      hw16
    have hbuild := partBuildGX_triple (curGAddr := curGAddr) (bufAddr := bufAddr) (q := q)
      (lvl := lvl) (D := D) (D_phi := D_phi) (workAddr := workAddr) (keptVertAddr := keptVertAddr)
      (arenaPtr := arenaPtr) (p := p) (mem := mem) curG cnt off ecnt eoff G_X hGX_n hGX_m
      hedges (prune_compressed_part_pre hV hD hDphi hφ_unif hexpY hstrict hactX).2.1
      heoff_le (by dsimp only [groupBufSize]; omega) hcnt_w
      (by dsimp only [partDegXAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega) hw16
    have hPre_eq : st₁.regs 0 = curGAddr ∧ st₁.regs 1 = bufAddr ∧ st₁.regs 2 = q ∧
        st₁.regs 3 = lvl ∧ st₁.regs 4 = D ∧ st₁.regs 5 = D_phi ∧
        st₁.regs 6 = workAddr ∧ st₁.regs 7 = keptVertAddr ∧ st₁.regs 8 = arenaPtr ∧
        st₁.regs 9 = curG.n ∧ st₁.regs 10 = curG.m ∧ st₁.regs 11 = cnt ∧ st₁.mem = mem := by
      simp [st₁, st0b, st0a, st₀, startState, List.getD]
    rcases hptr st₁ ω hPre_eq with ⟨o2, st₂, c2, hr2, ho2, hc2⟩
    cases o2 with
    | returned _ => exact False.elim ho2
    | normal =>
      rcases hbuild st₂ ω ho2 with ⟨o3, st₃, c3, hr3, ho3, hc3⟩
      cases o3 with
      | returned _ => exact False.elim ho3
      | normal =>
        rcases ho3 with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
          r16, r17, r18, r19, r20, hgaX3, hfr3⟩
        have hGX_V := (prune_compressed_part_pre hV hD hDphi hφ_unif hexpY hstrict hactX).2.1
        have hdeg := partDegX_triple (curGAddr := curGAddr) (bufAddr := bufAddr) (q := q)
          (lvl := lvl) (D := D) (D_phi := D_phi) (workAddr := workAddr)
          (keptVertAddr := keptVertAddr) (arenaPtr := arenaPtr) (p := p) (mem := st₃.mem)
          curG cnt off ecnt eoff G_X hGX_n hGX_m hGX_V hgaX3
          (by dsimp only [partInBAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega)
          (by omega) hw16
        rcases hdeg st₃ ω ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
            r16, r17, r18, r19, r20, rfl⟩ with ⟨o4, st₄, c4, hr4, ho4, hc4⟩
        cases o4 with
        | returned _ => exact False.elim ho4
        | normal =>
          rcases ho4 with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
            s16, s17, s18, s19, s20, hdegX4, hfr4⟩
          have hmem4_below : ∀ a, a < workAddr → st₄.mem a = mem a := fun a ha => by
            rw [hfr4 a (Or.inl (by dsimp only [partDegXAddr]; omega))]
            exact hfr3 a (Or.inl (by dsimp only [partGXAddr]; exact ha))
          have hverts_lt4 : ∀ x < cnt, st₄.mem (grpPartVerts bufAddr curG.n + off + x) < curG.n := by
            intro x hx
            rw [hmem4_below _ (by dsimp only [grpPartVerts]; omega)]
            exact hverts_lt x hx
          have htwin_lt4 : ∀ u < curG.n, st₄.mem (grpSameTwin bufAddr curG.n + u) < 2 ^ w := by
            intro u hu
            rw [hmem4_below _ (by dsimp only [grpSameTwin]; omega)]
            exact (htwin_spec u hu).1
          have hmul_ecnt : 2 * ecnt * D_phi + D + 4 < 2 ^ w := by
            have h := Nat.mul_le_mul_right D_phi (by omega : 2 * ecnt ≤ 2 * curG.m)
            omega
          have hinB := partInB_triple (curGAddr := curGAddr) (bufAddr := bufAddr) (q := q)
            (lvl := lvl) (D := D) (D_phi := D_phi) (workAddr := workAddr)
            (keptVertAddr := keptVertAddr) (arenaPtr := arenaPtr) (p := p) (mem := st₄.mem)
            curG cnt off ecnt eoff G_X hGX_n hGX_m hGX_V hdegX4 hoff_le hverts_lt4 htwin_lt4
            (by dsimp only [groupBufSize]; omega) (by dsimp only [groupBufSize]; omega)
            (by dsimp only [partOutRAddr, partWorkSize, pruneWorkSpace] at hwork_w ⊢; omega)
            hmul_ecnt hw16
          rcases hinB st₄ ω ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
              s16, s17, s18, s19, s20, rfl⟩ with ⟨o5, st₅, c5, hr5, ho5, hc5⟩
          cases o5 with
          | returned v5 =>
            rcases ho5 with ⟨rfl, hfr5, x, hx_lt, hxd, htw_nz⟩
            have hfr_all : ∀ a, a < workAddr ∨
                workAddr + partWorkSize cnt ecnt
                  (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2) ≤ a →
                st₅.mem a = mem a := by
              intro a ha
              have ha_inB : a < partInBAddr workAddr cnt ecnt ∨ partOutRAddr workAddr cnt ecnt ≤ a := by
                dsimp only [partInBAddr, partOutRAddr, partWorkSize, pruneWorkSpace] at ha ⊢
                rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
              have ha_deg : a < partDegXAddr workAddr cnt ecnt ∨ partInBAddr workAddr cnt ecnt ≤ a := by
                dsimp only [partDegXAddr, partInBAddr, partWorkSize, pruneWorkSpace] at ha ⊢
                rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
              have ha_gx : a < partGXAddr workAddr cnt ecnt ∨ partDegXAddr workAddr cnt ecnt ≤ a := by
                dsimp only [partGXAddr, partDegXAddr, partWorkSize, pruneWorkSpace] at ha ⊢
                rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
              calc st₅.mem a = st₄.mem a := hfr5 a ha_inB
                _ = st₃.mem a := hfr4 a ha_deg
                _ = mem a := hfr3 a ha_gx
            have htail5 : Runs w p ω
                (seqStmts [partInBStmt, partPruneCallStmt b_csr b_prune, partEmitRStmt])
                st₄ (.returned v5) st₅ (c5 + 1) := by
              dsimp only [seqStmts]
              exact runs_seq_iff.mpr (Or.inl ⟨v5, c5, hr5, rfl, rfl⟩)
            have hseq : Runs w p ω (partPruneProc b_csr b_prune) st₀ (.returned v5) st₅
                (3 + (5 + (9 + (5 + (c2 + (c3 + (c4 + (c5 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
              dsimp only [partPruneProc, seqStmts]
              exact runs_seq_iff.mpr (Or.inr ⟨st0a, 3, _, ha9,
                runs_seq_iff.mpr (Or.inr ⟨st0b, 5, _, ha10,
                  runs_seq_iff.mpr (Or.inr ⟨st₁, 9, _, ha11,
                    runs_seq_iff.mpr (Or.inr ⟨st₁, 5, _, hcond_r,
                      runs_seq_iff.mpr (Or.inr ⟨st₂, c2, _, hr2,
                        runs_seq_iff.mpr (Or.inr ⟨st₃, c3, _, hr3,
                          runs_seq_iff.mpr (Or.inr ⟨st₄, c4, c5 + 1, hr4, htail5, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
            have hdeg_cur : curG.degIn X (actVerts.getD x 0) * D_phi < D := by
              have hbound := (prune_compressed_part_pre hV hD hDphi hφ_unif hexpY hstrict hactX).1
              have hlen_act : actVerts.length = cnt := by simp [actVerts, tab]
              have hdeg_eq := compressPartGraph_degIn hstrict hbound
                (S_loc := Finset.range actVerts.length) le_rfl (by omega : x < actVerts.length)
              have himg : (Finset.range actVerts.length).image (fun i => actVerts.getD i 0) = X := by
                rw [compressPartGraph_image_f_verts, hactX]
              dsimp only at hdeg_eq
              rw [himg, hactX] at hdeg_eq
              have hGXv : G_X.verts = Finset.range actVerts.length := by
                dsimp only [Cited.Graph.verts]; rw [hGX_n, hlen_act]
              dsimp only [G_X] at hxd
              rw [hGXv, hdeg_eq] at hxd
              exact hxd
            have htw_Y : 2 * actVerts.getD x 0 + 1 ∈ Y := by
              rw [← htwin_eq_iff x hx_lt]
              have hv_eq := hmem4_below (grpPartVerts bufAddr curG.n + off + x) (hgrpPV_lt x hx_lt)
              have hw_eq := hmem4_below (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x))
                (hgrpST_lt _ (hverts_lt x hx_lt))
              rwa [hv_eq, hw_eq] at htw_nz
            have hφ_pos : (0 : ℝ) < φ_B1 := lt_of_lt_of_le (by positivity) hφ_unif
            have hdrop := badTwin_part_spec hV hL hD (by omega : 1 ≤ D_phi) hφ_pos hφ_unif hexpY hstrict
              hactX (by simp [actVerts, tab, hcnt_ge2]) (by simp [actVerts, tab, hx_lt]) hdeg_cur htw_Y
            have hcost_le : 3 + (5 + (9 + (5 + (c2 + (c3 + (c4 + (c5 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
                partPruneCost cnt ecnt D_phi := by
              unfold partPruneCost pruneTimeBound; dsimp only at hc2 hc3 hc4 hc5 ⊢; omega
            refine ⟨st₅, _, v5, ∅, [], hseq, hcost_le, le_rfl, by omega, .nil, by simp, ?_,
              fun a ha1 _ _ => hfr_all a (hwork_ge_sub a (by
                dsimp only [H_max] at ha1
                exact (not_and_or.mp ha1).elim (fun h => Or.inl (lt_of_not_ge h))
                  (fun h => Or.inr (le_of_not_gt h)))),
              Finset.empty_subset X, Or.inl rfl, by
                dsimp only [X, Y] at hdrop ⊢
                exact Nat.le_trans (Nat.sub_le _ _) hdrop⟩
            simp only [↓reduceIte]
            exact ⟨trivial, fun u hu => hfr_all _ (Or.inr (hkept_sub_u u hu))⟩
          | normal =>
            rcases ho5 with ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
              t16, t17, t18, t19, t20, hinB5, hfr5⟩
            have hfr_mem5 : MemFrame mem st₅.mem workAddr
                (workAddr + partWorkSize cnt ecnt
                  (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2)) := by
              intro a ha
              have ha_inB : a < partInBAddr workAddr cnt ecnt ∨ partOutRAddr workAddr cnt ecnt ≤ a := by
                dsimp only [partInBAddr, partOutRAddr, partWorkSize, pruneWorkSpace] at ha ⊢
                rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
              have ha_deg : a < partDegXAddr workAddr cnt ecnt ∨ partInBAddr workAddr cnt ecnt ≤ a := by
                dsimp only [partDegXAddr, partInBAddr, partWorkSize, pruneWorkSpace] at ha ⊢
                rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
              have ha_gx : a < partGXAddr workAddr cnt ecnt ∨ partDegXAddr workAddr cnt ecnt ≤ a := by
                dsimp only [partGXAddr, partDegXAddr, partWorkSize, pruneWorkSpace] at ha ⊢
                rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
              calc st₅.mem a = st₄.mem a := hfr5 a ha_inB
                _ = st₃.mem a := hfr4 a ha_deg
                _ = mem a := hfr3 a ha_gx
            have hmem5_below : ∀ a, a < workAddr → st₅.mem a = mem a := fun a ha =>
              hfr_mem5 a (Or.inl ha)
            have hact_st5' : (tab cnt fun t => st₅.mem (grpPartVerts bufAddr curG.n + off + t)) = actVerts :=
              List.map_congr_left fun t ht =>
                hmem5_below _ (hgrpPV_lt t (List.mem_range.mp ht))
            have hgaX5 : GraphAt st₅.mem (partGXAddr workAddr cnt ecnt) G_X := by
              refine graphAt_of_cells
                (by
                  have h1 := hpart_gx_inB 0 (by omega)
                  have h2 := hpart_gx_degX 0 (by omega)
                  rw [add_zero] at h1 h2
                  rw [hfr5 _ (Or.inl h1), hfr4 _ (Or.inl h2)]; exact graphAt_n hgaX3)
                (by
                  have h1 := hpart_gx_inB 1 (by omega)
                  have h2 := hpart_gx_degX 1 (by omega)
                  rw [hfr5 _ (Or.inl h1), hfr4 _ (Or.inl h2)]; exact graphAt_m hgaX3)
                fun j hj => ?_
              have hj_m : j < ecnt := hGX_m ▸ hj
              have h1a := hpart_gx_inB (2 + 2 * j) (by omega)
              have h1b := hpart_gx_degX (2 + 2 * j) (by omega)
              have h2a := hpart_gx_inB (3 + 2 * j) (by omega)
              have h2b := hpart_gx_degX (3 + 2 * j) (by omega)
              rw [← Nat.add_assoc] at h1a h1b h2a h2b
              refine ⟨?_, ?_⟩
              · rw [hfr5 _ (Or.inl h1a), hfr4 _ (Or.inl h1b)]; exact graphAt_edge_fst hgaX3 hj
              · rw [hfr5 _ (Or.inl h2a), hfr4 _ (Or.inl h2b)]; exact graphAt_edge_snd hgaX3 hj
            have hcall_res := partPruneCall_triple (curGAddr := curGAddr) (bufAddr := bufAddr)
              (q := q) (lvl := lvl) (D := D) (D_phi := D_phi) (workAddr := workAddr)
              (keptVertAddr := keptVertAddr) (arenaPtr := arenaPtr)
              (b_csr := b_csr) (b_prune := b_prune) (p := p) (mem := st₅.mem)
              curG hV hL hD hDphi hφ_unif hexpY cnt off ecnt eoff
              (by rw [hact_st5']; exact hstrict)
              (by rw [hact_st5']; exact hactX)
              (by rw [hact_st5']; exact hGX_n)
              (by rw [hact_st5']; exact hGX_m)
              (by rw [hact_st5']; exact hgaX5)
              (fun x hx => by rw [hact_st5']; exact (hinB5 x hx).1)
              hp_csr hp_prune hwork_w harith_sub hD_w hw16
            rcases hcall_res st₅ ω ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13,
                t14, t15, t16, t17, t18, t19, t20, rfl⟩ with ⟨o6, st₆, c6, hr6, ho6, hc6⟩
            cases o6 with
            | returned _ => exact False.elim ho6
            | normal =>
              rcases ho6 with ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14,
                u15, u16, u17, u18, u19, u20, hfr6, hR_sub6, hexpR6, hdegR6, hvolR6⟩
              rw [hact_st5'] at hR_sub6 hexpR6 hdegR6 hvolR6
              have hmem6_below : ∀ a, a < workAddr → st₆.mem a = mem a := fun a ha => by
                rw [hfr6 a (Or.inl ha)]; exact hmem5_below a ha
              have hverts_lt6 : ∀ x < cnt, st₆.mem (grpPartVerts bufAddr curG.n + off + x) < curG.n := fun x hx => by
                rw [hmem6_below _ (hgrpPV_lt x hx)]; exact hverts_lt x hx
              have hemit := partEmitR_triple (curGAddr := curGAddr) (bufAddr := bufAddr) (q := q)
                (lvl := lvl) (D := D) (D_phi := D_phi) (workAddr := workAddr)
                (keptVertAddr := keptVertAddr) (arenaPtr := arenaPtr) (p := p) (mem := st₆.mem)
                curG cnt off ecnt eoff
                (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2)
                hcnt_le hverts_lt6 hoff_le (by dsimp only [groupBufSize]; omega) hwork_kept_sub
                hkept_arena harena_w hlvl_w hw16
              rcases hemit st₆ ω ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14,
                  u15, u16, u17, u18, u19, u20, rfl⟩ with ⟨o7, st₇, c7, hr7, ho7, hc7⟩
              cases o7 with
              | normal => exact False.elim ho7
              | returned arenaPtr' =>
                have hseq : Runs w p ω (partPruneProc b_csr b_prune) st₀ (.returned arenaPtr') st₇
                    (3 + (5 + (9 + (5 + (c2 + (c3 + (c4 + (c5 + (c6 + c7 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
                  dsimp only [partPruneProc, seqStmts]
                  exact runs_seq_iff.mpr (Or.inr ⟨st0a, 3, _, ha9,
                    runs_seq_iff.mpr (Or.inr ⟨st0b, 5, _, ha10,
                      runs_seq_iff.mpr (Or.inr ⟨st₁, 9, _, ha11,
                        runs_seq_iff.mpr (Or.inr ⟨st₁, 5, _, hcond_r,
                          runs_seq_iff.mpr (Or.inr ⟨st₂, c2, _, hr2,
                            runs_seq_iff.mpr (Or.inr ⟨st₃, c3, _, hr3,
                              runs_seq_iff.mpr (Or.inr ⟨st₄, c4, _, hr4,
                                runs_seq_iff.mpr (Or.inr ⟨st₅, c5, _, hr5,
                                  runs_seq_iff.mpr (Or.inr ⟨st₆, c6, c7, hr6, hr7, rfl⟩),
                                  rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
                have hnoBadTwin : ∀ x < actVerts.length,
                    curG.degIn X (actVerts.getD x 0) * D_phi < D →
                    2 * actVerts.getD x 0 + 1 ∉ Y :=
                  partPrune_noBadTwin hV hD hDphi hφ_unif hexpY hstrict hactX
                    (by simp [actVerts, tab]) hGX_n mem st₄.mem (fun x hx => (hinB5 x hx).2)
                    (fun x hx => hmem4_below _ (hgrpPV_lt x hx))
                    (fun x hx => hmem4_below _ (hgrpST_lt _ (hverts_lt x hx)))
                    htwin_eq_iff
                have hpost_p := prune_compressed_part_post hV hL hDphi hstrict hactX
                  hR_sub6 hexpR6 hdegR6 hvolR6 hnoBadTwin
                rcases hpost_p with ⟨hRX, hR_or, hdrop⟩
                set selIdx := (List.range cnt).filter fun x =>
                  decide (st₆.mem (partOutRAddr workAddr cnt ecnt + x) ≠ 0)
                set R_list_raw := selIdx.map fun x => st₆.mem (grpPartVerts bufAddr curG.n + off + x)
                set R_loc := (Finset.range cnt).filter fun x =>
                  decide (st₆.mem (partOutRAddr workAddr cnt ecnt + x) ≠ 0)
                have hR_raw_eq : R_list_raw =
                    selIdx.map fun x => mem (grpPartVerts bufAddr curG.n + off + x) := by
                  refine List.map_congr_left fun x hx => ?_
                  exact hmem6_below _ (hgrpPV_lt x (List.mem_range.mp (List.mem_filter.mp hx).1))
                have hR_list_toFinset : R_list_raw.toFinset = R_loc.image (fun k => actVerts.getD k 0) := by
                  rw [hR_raw_eq]
                  ext u
                  simp only [R_loc, selIdx, List.mem_toFinset, List.mem_map, List.mem_filter,
                    List.mem_range, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
                  constructor
                  · rintro ⟨x, ⟨hx, hnz⟩, rfl⟩
                    exact ⟨x, ⟨hx, hnz⟩, by simp [actVerts, tab, List.getD_eq_getElem?_getD, hx]⟩
                  · rintro ⟨x, ⟨hx, hnz⟩, rfl⟩
                    exact ⟨x, ⟨hx, hnz⟩, by simp [actVerts, tab, List.getD_eq_getElem?_getD, hx]⟩
                have hsel_nd : selIdx.Nodup := (List.nodup_range).filter _
                have hlen_card : R_list_raw.length = R_loc.card := by
                  simp only [R_list_raw, List.length_map]
                  rw [← List.toFinset_card_of_nodup hsel_nd]
                  congr 1
                  ext x
                  simp [selIdx, R_loc, List.mem_range]
                have hfr6_all : MemFrame mem st₆.mem workAddr
                    (workAddr + partWorkSize curG.n curG.m H_max) := by
                  intro a ha
                  have ha_sub := hwork_ge_sub a (by dsimp only [H_max] at ha; exact ha)
                  calc st₆.mem a = st₅.mem a := hfr6 a ha_sub
                    _ = mem a := hfr_mem5 a ha_sub
                have hcost_total :
                    3 + (5 + (9 + (5 + (c2 + (c3 + (c4 + (c5 + (c6 + c7 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
                    partPruneCost cnt ecnt D_phi := by
                  clear hnoBadTwin hexpR6 hdegR6 hvolR6 hR_sub6 hact_st5' hgaX5 hGX_V
                    hgaX3 hdegX4 hinB5 hedges hexpY hstrict hactX hverts_eq hseq ho7 hr2 hr3 hr4 hr5 hr6 hr7
                    hfr3 hfr4 hfr5 hfr6 hfr_mem5 hfr6_all hmem4_below hmem5_below hmem6_below hverts_lt4 htwin_lt4 hverts_lt6
                    hsel_nd hlen_card hR_raw_eq hR_list_toFinset
                  unfold partPruneCost
                  dsimp only at hc2 hc3 hc4 hc5 hc6 hc7 ⊢
                  omega
                dsimp only at ho7
                by_cases hlt2 : R_list_raw.length < 2
                · have hR_card_le1 : R_loc.card ≤ 1 := by omega
                  split_ifs at ho7
                  · rcases ho7 with ⟨hptr_eq, hmem7⟩
                    have hdrop1 : (curG.inside X).length - (curG.inside ∅).length ≤ 15 * (twinGraph D curG).cut Y := by
                      have hR0 : (if R_loc.card ≤ 1 then ∅ else R_loc.image (fun k => actVerts.getD k 0)) = ∅ := by
                        split_ifs; rfl
                      rw [hR0] at hdrop; exact hdrop
                    rw [hptr_eq] at hseq
                    refine ⟨st₇, _, arenaPtr, ∅, [], hseq, hcost_total, le_rfl, by omega,
                      .nil, by simp, ?_, ?_, Finset.empty_subset X, Or.inl rfl, hdrop1⟩
                    · simp only [↓reduceIte]
                      exact ⟨trivial, fun u hu => by rw [hmem7]; exact hfr6_all _ (Or.inr (by dsimp only [H_max]; omega))⟩
                    · intro a ha1 _ _
                      rw [hmem7]
                      exact hfr6_all a ((not_and_or.mp ha1).elim (fun h => Or.inl (lt_of_not_ge h))
                        (fun h => Or.inr (le_of_not_gt h)))
                · have hR_card_ge2 : 2 ≤ R_loc.card := by omega
                  have hnot_le1 : ¬ R_loc.card ≤ 1 := by omega
                  split_ifs at ho7
                  rcases ho7 with ⟨hptr_eq, hlistAt, hkept7, hrest7⟩
                  have hdegR1 : ∀ v ∈ R_loc, 1 ≤ G_X.degIn R_loc v := fun v hv =>
                    le_trans (by
                      have : 3 * D_phi ≤ D + 3 * D_phi - 1 := by omega
                      exact Nat.div_pos this (by omega)) (hdegR6 v hv)
                  have hcard_le_4m : 2 + R_loc.card ≤ 4 * ecnt := by
                    rw [← hGX_m]
                    exact card_two_add_le_four_mul_m hR_card_ge2 hdegR1
                  have hpw_R : R_list_raw.Pairwise (· < ·) := by
                    rw [hR_raw_eq]
                    exact pairwise_lt_map_tab_filter _ cnt hstrict selIdx
                      (fun x hx => List.mem_range.mp (List.mem_filter.mp hx).1)
                      (List.pairwise_lt_range.filter _)
                  set R_res := R_loc.image (fun k => actVerts.getD k 0)
                  have hR_ne : R_res ≠ ∅ := by
                    intro hemp
                    have hc0 : R_res.card = 0 := by rw [hemp]; simp
                    have hc_eq : R_res.card = R_loc.card := by
                      rw [← hR_list_toFinset, List.toFinset_card_of_nodup (hpw_R.imp fun h => ne_of_lt h)]
                      exact hlen_card
                    omega
                  have hR_if : (if R_loc.card ≤ 1 then ∅ else R_loc.image (fun k => actVerts.getD k 0)) = R_res := by
                    change (if R_loc.card ≤ 1 then ∅ else R_res) = R_res
                    exact ite_eq_right_iff.mpr fun h => absurd h hnot_le1
                  rw [hR_if] at hRX hR_or hdrop
                  rw [hptr_eq] at hseq hrest7
                  refine ⟨st₇, _, arenaPtr + 2 + R_list_raw.length, R_res, R_list_raw, hseq,
                    hcost_total, by omega, by omega, hpw_R, hR_list_toFinset, ?_, ?_, hRX,
                    Or.inr (hR_or.resolve_left hR_ne), hdrop⟩
                  · rw [ite_eq_right_iff.mpr fun h => absurd h hR_ne]
                    refine ⟨by omega, rfl, hlistAt, fun u hu => ?_⟩
                    have hk_u := hkept7 u hu
                    have hmem_u : st₆.mem (keptVertAddr + u) = mem (keptVertAddr + u) :=
                      hfr6_all _ (Or.inr (by dsimp only [H_max]; omega))
                    rw [← hR_list_toFinset, List.mem_toFinset]
                    exact ⟨hk_u.1, fun hneg => by rw [hk_u.2 hneg, hmem_u]⟩
                  · intro a ha1 ha2 ha3
                    rw [hrest7 a ha2 ha3]
                    exact hfr6_all a ((not_and_or.mp ha1).elim (fun h => Or.inl (lt_of_not_ge h))
                      (fun h => Or.inr (le_of_not_gt h)))

end MinCostFlow.Expander
