/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinCostFlow.Expander.DecomposeProgInv

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-Level Loop Step Preservation and Execution (`decomposeLevelLoop_runs`)

Proves `decomposeStep_mk_inv`, `decomposeStep_preserves`, and `decomposeLevelLoop_runs` for
`DecomposeImpl`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section

private lemma decomposeStep_mk_inv
    {G : Cited.Graph} {gAddr h ℓ D_phi c k thr : ℕ} {mem_orig : ℕ → ℕ}
    {recs : List DecompLevelRec} {remG remG' Gi : Cited.Graph}
    {remIdx remIdx' keptIdx : List ℕ} {keptFlag : ℕ → Bool}
    {arena zc arena₁ zeroCursor' : ℕ}
    {rawComps_lvl : List (ℕ × List ℕ)} {validRs : List (Finset ℕ)}
    {st st1 st_lvl st4 : State}
    (hlvl_le_m : ℓ ≤ G.m) (h200_Dphi : 200 ≤ D_phi)
    (hinv : DecompLoopInv G gAddr h ℓ D_phi c (k + 1) mem_orig recs remG remIdx arena zc st)
    (harena_ge1 : arena ≤ arena₁)
    (hmem_sp : st_lvl.mem (mkDecompLayout h G.n G.m D_phi).statePtr = arena₁)
    (hmem_zc : st_lvl.mem ((mkDecompLayout h G.n G.m D_phi).statePtr + 1) = zeroCursor')
    (hmem_tot : st_lvl.mem ((mkDecompLayout h G.n G.m D_phi).statePtr + 2) =
      (recs.map (fun x => x.rawComps)).flatten.length + rawComps_lvl.length)
    (hzero' : ZeroFrom st_lvl.mem zeroCursor')
    (hzc_ge1 : zc ≤ zeroCursor')
    (hzc_le1 : zeroCursor' ≤ if thr ≤ remG.m + 2 ^ (k + 1) * remG.n then
      zc + 1 + 2 ^ wordSize c ((twinGraph (2 ^ (k + 1)) remG).encode ++ [1, 200, rOf (remG.m + 2 ^ (k + 1) * remG.n)])
      else zc)
    (hlist_ar : ListAt st_lvl.mem arena (List.flatMap compRecord rawComps_lvl))
    (harena_eq : arena₁ = arena + (List.flatMap compRecord rawComps_lvl).length)
    (hvalid_eq : List.map (fun comp => comp.2.toFinset) rawComps_lvl = validRs)
    (hraw_props : ∀ comp ∈ rawComps_lvl,
      comp.1 = k + 1 ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length)
    (hGi_n : Gi.n = remG.n) (hrem_n' : remG'.n = remG.n)
    (hrem_valid' : remG'.IsValid) (hrem_loopless' : remG'.IsLoopless)
    (hperm : (Gi.edges ++ remG'.edges).Perm remG.edges)
    (hGi_m : Gi.m ≤ 2 ^ (k + 1) * remG.n) (hrem_m' : remG'.m ≤ 2 ^ (k + 1 - 1) * remG.n)
    (hRs_disj : validRs.Pairwise Disjoint)
    (hRs_prop : ∀ R ∈ validRs, R ⊆ remG.verts ∧ 2 ≤ R.card ∧
      Gi.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
      (∀ x ∈ R, 1 / (3 * (D_phi : ℝ)) * 2 ^ (k + 1) ≤ ↑(Gi.degIn R x)) ∧
      ∀ e ∈ Gi.edges, e.1 ∈ R ↔ e.2 ∈ R)
    (hcov : ∀ e ∈ Gi.edges, ∃ R ∈ validRs, e.1 ∈ R ∧ e.2 ∈ R)
    (hremG'_at : GraphAt st_lvl.mem (curAddrs (mkDecompLayout h G.n G.m D_phi) (ℓ - (k + 1))).2.2.1 remG')
    (hremIdx'_at : ListAt st_lvl.mem (curAddrs (mkDecompLayout h G.n G.m D_phi) (ℓ - (k + 1))).2.2.2 remIdx')
    (hremIdx'_len : remIdx'.length = remG'.m) (hremIdx'_pw : remIdx'.Pairwise (· < ·))
    (hkeptIdx_pw : keptIdx.Pairwise (· < ·))
    (hremG'_edges : remG'.edges = List.map (fun t => remG.edges.getD t (0, 0))
      (List.filter (fun t => !keptFlag t) (List.range remG.m)))
    (hremIdx'_eq : remIdx' = List.map (fun t => remIdx.getD t 0)
      (List.filter (fun t => !keptFlag t) (List.range remG.m)))
    (hGi_edges : Gi.edges = List.map (fun t => remG.edges.getD t (0, 0))
      (List.filter (fun t => keptFlag t) (List.range remG.m)))
    (hkeptIdx_eq : keptIdx = List.map (fun t => remIdx.getD t 0)
      (List.filter (fun t => keptFlag t) (List.range remG.m)))
    (hlvl_arr : ∀ a < G.m, st_lvl.mem ((mkDecompLayout h G.n G.m D_phi).lvlArrAddr + a) =
      if a ∈ keptIdx then k + 1 else st1.mem ((mkDecompLayout h G.n G.m D_phi).lvlArrAddr + a))
    (hframe_lvl : let L := mkDecompLayout h G.n G.m D_phi
      let ca := curAddrs L (ℓ - (k + 1))
      ∀ a < zc,
        ¬(L.statePtr ≤ a ∧ a < L.statePtr + 3) →
        ¬(L.lvlArrAddr ≤ a ∧ a < L.lvlArrAddr + G.m) →
        ¬(ca.2.2.1 ≤ a ∧ a < ca.2.2.1 + 2 + 2 * remG.m) →
        ¬(ca.2.2.2 ≤ a ∧ a < ca.2.2.2 + remG.m) →
        ¬(L.twAddr ≤ a ∧ a < L.keptVertAddr + remG.n) →
        ¬(arena ≤ a ∧ a < arena₁) →
        st_lvl.mem a = st1.mem a)
    (hst4_regs : let L := mkDecompLayout h G.n G.m D_phi
      let ca := curAddrs L (ℓ - (k + 1))
      DecompRegs gAddr h G.n G.m ℓ D_phi k (2 ^ k) ca.2.2.1 ca.2.2.2 ca.1 ca.2.1 L st4)
    (hst4_mem_ne : ∀ a, a ≠ (mkDecompLayout h G.n G.m D_phi).boundsAddr + 2 * (k + 1) + 1 → st4.mem a = st_lvl.mem a)
    (hst4_mem_bnd1 : st4.mem ((mkDecompLayout h G.n G.m D_phi).boundsAddr + 2 * (k + 1) + 1) = arena₁)
    (hst1_mem_ne : ∀ a, a ≠ (mkDecompLayout h G.n G.m D_phi).boundsAddr + 2 * (k + 1) → st1.mem a = st.mem a)
    (hst1_mem_bnd0 : st1.mem ((mkDecompLayout h G.n G.m D_phi).boundsAddr + 2 * (k + 1)) = arena)
    (h2p_ws : 2 ^ (wordSize c ((twinGraph (2 ^ (k + 1)) remG).encode ++ [1, 200, rOf (remG.m + 2 ^ (k + 1) * remG.n)]) + 1) ≤
      2 * (416 * (G.n + G.m + 2)) ^ c) :
    DecompLoopInv G gAddr h ℓ D_phi c k mem_orig
      ({ lvl := k + 1, rawComps := rawComps_lvl, validRs := validRs, Gi := Gi, keptIdx := keptIdx } :: recs)
      remG' remIdx' arena₁ zeroCursor' st4 := by
  set L := mkDecompLayout h G.n G.m D_phi
  have hb := mkDecompLayout_bounds h G.n G.m D_phi
  change DecompLayoutBounds L h G.n G.m D_phi at hb
  have hL_sp := hb.hsp
  have hL_bnd := hb.hbnd
  have hL_lvl := hb.hlvl
  have hL_g0 := hb.hg0
  have hL_i0 := hb.hi0
  have hL_g1 := hb.hg1
  have hL_i1 := hb.hi1
  have hL_tw := hb.htw
  have hL_buf := hb.hbuf
  have hL_bw : L.bufAddr ≤ L.workAddr := by rw [hb.hwork]; omega
  have hL_wk : L.workAddr ≤ L.keptVertAddr := by rw [hb.hkept]; omega
  have hrem_n_eq : remG.n = G.n := hinv.hrem_n
  have hL_ar := hb.har
  have hL_zc := hb.hzc
  have hL_ar_m : arena + 4 * remG.m ≤ L.zeroCursor₀ := hinv.harena_m
  have hL_ar_ge : L.arena₀ ≤ arena := hinv.harena_ge
  have hL_zc_ge : L.zeroCursor₀ ≤ zc := hinv.hzc_ge
  let ca := curAddrs L (ℓ - (k + 1))
  let lvl := k + 1
  have hk_le : k + 1 ≤ ℓ := hinv.hk
  have hbnd_le : L.boundsAddr + 2 * lvl + 1 < L.lvlArrAddr := by omega
  have hca_ge_lvl : L.lvlArrAddr ≤ ca.1 ∧ L.lvlArrAddr ≤ ca.2.1 ∧
      L.lvlArrAddr ≤ ca.2.2.1 ∧ L.lvlArrAddr ≤ ca.2.2.2 := by
    dsimp only [ca, curAddrs]
    by_cases hp : (ℓ - (k + 1)) % 2 = 0 <;> simp [hp] <;> omega
  have hca_le_tw : ca.1 + 2 + 2 * remG.m ≤ L.twAddr ∧ ca.2.1 + remG.m ≤ L.twAddr ∧
      ca.2.2.1 + 2 + 2 * remG.m ≤ L.twAddr ∧ ca.2.2.2 + remG.m ≤ L.twAddr := by
    have hm_le := hinv.hrem_m_le
    dsimp only [ca, curAddrs]
    by_cases hp : (ℓ - (k + 1)) % 2 = 0 <;> simp [hp] <;> omega
  have hperm_len : Gi.m + remG'.m = remG.m := by
    simpa [Cited.Graph.m, List.length_append] using hperm.length_eq
  have hrem_part := mem_kept_rem_partition hinv.hidx_len hinv.hidx_pw.nodup keptFlag
  rw [← hremIdx'_eq, ← hkeptIdx_eq] at hrem_part
  have harena_len := arena_len_le_four_mul_Gi (Gi := Gi) (validRs := validRs)
      (rawComps_lvl := rawComps_lvl) (φ := 1 / (3 * (D_phi : ℝ))) (lvl := lvl)
      (by have : (200 : ℝ) ≤ D_phi := Nat.cast_le.mpr h200_Dphi; positivity) hvalid_eq hraw_props hRs_disj
      (fun R hR => ⟨(hRs_prop R hR).2.1, (hRs_prop R hR).2.2.2.1⟩)
  have hremG'_m_le : remG'.m ≤ G.m := by have := hinv.hrem_m_le; omega
  have harena₁_m : arena₁ + 4 * remG'.m ≤ L.zeroCursor₀ := by
    have h4g := harena_len.1
    omega
  have hfr_bnd : ∀ a, L.boundsAddr ≤ a → a < L.lvlArrAddr → st_lvl.mem a = st1.mem a := by
    intro a ha1 ha2
    have hlt_zc : a < zc := by omega
    apply hframe_lvl a hlt_zc
    · omega
    · omega
    · exact fun ⟨hge, _⟩ => by change ca.2.2.1 ≤ a at hge; omega
    · exact fun ⟨hge, _⟩ => by change ca.2.2.2 ≤ a at hge; omega
    · exact fun ⟨hge, _⟩ => by omega
    · exact fun ⟨hge, _⟩ => by omega
  have hfr_ar : ∀ a, L.arena₀ ≤ a → a < arena → st_lvl.mem a = st1.mem a := by
    intro a ha1 ha2
    have hlt_zc : a < zc := by omega
    apply hframe_lvl a hlt_zc
    · omega
    · omega
    · exact fun ⟨_, hlt⟩ => by change a < ca.2.2.1 + 2 + 2 * remG.m at hlt; omega
    · exact fun ⟨_, hlt⟩ => by change a < ca.2.2.2 + remG.m at hlt; omega
    · exact fun ⟨_, hlt⟩ => by rw [hinv.hrem_n] at hlt; omega
    · exact fun ⟨hge, _⟩ => by omega
  have hflip := curAddrs_flip L hk_le
  dsimp only [ca] at hflip
  refine
    { hk := by omega
      hlen := by simp [hinv.hlen]; omega
      hregs := by dsimp only; rw [hflip]; exact hst4_regs
      hrem_valid := hrem_valid'
      hrem_loopless := hrem_loopless'
      hrem_n := hrem_n'.trans hinv.hrem_n
      hrem_m_le_pow := by rw [hinv.hrem_n] at hrem_m'; exact hrem_m'
      hrem_m_le := hremG'_m_le
      hrem_edges := by
        rw [hremG'_edges, hinv.hrem_edges, hremIdx'_eq]
        exact edges_map_filter (fun j => G.edges.getD j (0, 0)) (0, 0) remIdx remG.m hinv.hidx_len
          (fun t => !keptFlag t)
      hidx_len := hremIdx'_len
      hidx_pw := hremIdx'_pw
      hidx_lt := fun a ha => hinv.hidx_lt a (hrem_part.1 a ha).1
      hcurG_at := by
        rw [hflip]
        intro idx hidx
        have hne : ca.2.2.1 + idx ≠ L.boundsAddr + 2 * lvl + 1 := by omega
        rw [hst4_mem_ne _ hne]
        exact hremG'_at idx hidx
      hcurIdx_at := by
        rw [hflip]
        intro idx hidx
        have hne : ca.2.2.2 + idx ≠ L.boundsAddr + 2 * lvl + 1 := by omega
        rw [hst4_mem_ne _ hne]
        exact hremIdx'_at idx hidx
      hstate_ar := by
        have hne : L.statePtr ≠ L.boundsAddr + 2 * lvl + 1 := by omega
        rw [hst4_mem_ne _ hne]
        exact hmem_sp
      hstate_zc := by
        have hne : L.statePtr + 1 ≠ L.boundsAddr + 2 * lvl + 1 := by omega
        rw [hst4_mem_ne _ hne]
        exact hmem_zc
      hstate_tot := by
        have hne : L.statePtr + 2 ≠ L.boundsAddr + 2 * lvl + 1 := by omega
        rw [hst4_mem_ne _ hne, hmem_tot]
        simp only [List.map_cons, List.flatten_cons, List.length_append]
        omega
      hzero := by
        intro a ha
        have hne : a ≠ L.boundsAddr + 2 * lvl + 1 := by
          have := hL_zc_ge; have := hzc_ge1; omega
        rw [hst4_mem_ne _ hne]
        exact hzero' a ha
      harena_ge := le_trans hinv.harena_ge harena_ge1
      harena_m := harena₁_m
      htotal_m := by
        have hlen_rec : (List.map (fun x => x.rawComps)
            ({ lvl := k + 1, rawComps := rawComps_lvl, validRs := validRs, Gi := Gi, keptIdx := keptIdx } :: recs)).flatten.length =
            rawComps_lvl.length + (List.map (fun x => x.rawComps) recs).flatten.length := by
          change (rawComps_lvl ++ (List.map (fun x => x.rawComps) recs).flatten).length = _
          rw [List.length_append]
        have h1 := harena_len.2
        have h2 := hinv.htotal_m
        omega
      hzc_ge := le_trans hinv.hzc_ge hzc_ge1
      hzc_le := by
        have hstep_zc : zeroCursor' ≤ zc + (1 + (416 * (G.n + G.m + 2)) ^ c) := by
          by_cases hthr_m : thr ≤ remG.m + 2 ^ (k + 1) * remG.n
          · have h2p := h2p_ws
            have h2s : 2 ^ wordSize c ((twinGraph (2 ^ (k + 1)) remG).encode ++ [1, 200, rOf (remG.m + 2 ^ (k + 1) * remG.n)]) ≤
                (416 * (G.n + G.m + 2)) ^ c := by
              rw [pow_succ'] at h2p
              exact Nat.le_of_mul_le_mul_left h2p (by omega)
            simp only [hthr_m, ite_true] at hzc_le1
            rw [← Nat.add_assoc zc 1]
            exact le_trans hzc_le1 (Nat.add_le_add_left h2s (zc + 1))
          · simp only [hthr_m, ite_false] at hzc_le1
            exact le_trans hzc_le1 (Nat.le_add_right _ _)
        have hdone_eq : ℓ - k = (ℓ - (k + 1)) + 1 := by omega
        rw [hdone_eq, Nat.add_one_mul]
        exact le_trans hstep_zc (le_trans (Nat.add_le_add_right hinv.hzc_le _)
          (le_of_eq (Nat.add_assoc _ _ _)))
      hrecs := by
        intro i hi
        rcases i with _ | j
        · simp only [List.getElem_cons_zero]
          refine ⟨by simp, hraw_props, hvalid_eq, hkeptIdx_pw,
            fun a ha => hinv.hidx_lt a (hrem_part.2.1 a ha).1,
            hGi_n.trans hinv.hrem_n, ?_, ?_, hRs_disj, ?_, hcov⟩
          · rw [hGi_edges, hinv.hrem_edges, hkeptIdx_eq]
            exact edges_map_filter (fun j => G.edges.getD j (0, 0)) (0, 0) remIdx remG.m hinv.hidx_len keptFlag
          · rw [hinv.hrem_n] at hGi_m; exact hGi_m
          · intro R hR
            obtain ⟨hRv, hRc, hRe, hRd, hRi⟩ := hRs_prop R hR
            have hverts : remG.verts = G.verts := by simp [Cited.Graph.verts, hinv.hrem_n]
            exact ⟨hverts ▸ hRv, hRc, hRe, hRd, hRi⟩
        · simp only [List.getElem_cons_succ]
          exact hrecs_shift (hinv.hrecs j (Nat.lt_of_succ_lt_succ hi))
      hbounds := decomposeStep_hbounds (L := L) rfl hk_le hinv.hlen hlvl_le_m hL_lvl hbnd_le
        (decompLayout_lvl_le_ar hb) hinv.harena_ge harena_ge1 harena_eq hlist_ar hinv.hbounds
        hst4_mem_ne hst4_mem_bnd1 hfr_bnd hfr_ar hst1_mem_ne hst1_mem_bnd0
      hlvl := decomposeStep_hlvl rfl
        (fun a ha => by
          have hne4 : L.lvlArrAddr + a ≠ L.boundsAddr + 2 * lvl + 1 :=
            Nat.ne_of_gt (lt_of_lt_of_le hbnd_le (Nat.le_add_right _ _))
          have hne1 : L.lvlArrAddr + a ≠ L.boundsAddr + 2 * lvl :=
            Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_of_succ_lt hbnd_le) (Nat.le_add_right _ _))
          rw [hst4_mem_ne _ hne4, hlvl_arr a ha, hst1_mem_ne _ hne1])
        hrem_part hinv.hlvl
      hframe := by
        have hh_le := decompLayout_h_le hb
        have hh_ar : h ≤ arena :=
          le_trans hh_le.2.2.2.2.1 (le_trans (hL_ar ▸ Nat.le_add_right _ _) hL_ar_ge)
        intro a ha_h
        have hne3 : a ≠ L.boundsAddr + 2 * lvl + 1 :=
          Nat.ne_of_lt (lt_of_lt_of_le ha_h
            (le_trans hh_le.2.1 (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
        have hne1 : a ≠ L.boundsAddr + 2 * lvl :=
          Nat.ne_of_lt (lt_of_lt_of_le ha_h (le_trans hh_le.2.1 (Nat.le_add_right _ _)))
        have hlt_zc : a < zc :=
          lt_of_lt_of_le ha_h (le_trans hh_le.2.2.2.2.2 hL_zc_ge)
        have h2 : st_lvl.mem a = st1.mem a :=
          hframe_lvl a hlt_zc
            (not_mem_interval_of_lt ha_h hh_le.1)
            (not_mem_interval_of_lt ha_h hh_le.2.2.1)
            (not_mem_interval_of_lt ha_h (le_trans hh_le.2.2.1 hca_ge_lvl.2.2.1))
            (not_mem_interval_of_lt ha_h (le_trans hh_le.2.2.1 hca_ge_lvl.2.2.2))
            (not_mem_interval_of_lt ha_h hh_le.2.2.2.1)
            (not_mem_interval_of_lt ha_h hh_ar)
        rw [hst4_mem_ne a hne3, h2, hst1_mem_ne a hne1]
        exact hinv.hframe a ha_h }

private lemma decomposeStep_preserves {K cr : ℝ} {P : Program} {c : ℕ} (hK : 0 < K)
    (hDec : ∀ G_tw : Cited.Graph, G_tw.IsValid → G_tw.IsLoopless → thresholdB1 cr ≤ G_tw.m →
      ∀ ω : ℕ → Bool, ∃ out cost,
        RunsTo (wordSize c (G_tw.encode ++ [1, 200, rOf G_tw.m])) P (G_tw.encode ++ [1, 200, rOf G_tw.m]) ω out cost ∧
        IsExpanderDecomposition G_tw (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
          ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) / (K * Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2))) out ∧
        (cost : ℝ) ≤ K * (G_tw.n + ((G_tw.m : ℝ) + 2) ^ (1 + K / rOf G_tw.m) *
          Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2) / (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2))
    {K_nat thr b : ℕ} (hK_nat : K ≤ ↑K_nat) (hthr200 : 200 ≤ thr) (hthr_cr : thresholdB1 cr ≤ thr)
    {w C_phi : ℕ} {p : Program} {ω : ℕ → Bool}
    (hc : DecompProgContracts K_nat thr P c w b p)
    (G : Cited.Graph) (gAddr h ℓ k : ℕ) (C₀_lvl C_lvl : ℝ) (c_cited_ub c_ws_ub : ℕ)
    (h1n : 1 ≤ G.n) (hnm : G.n < G.m) (hℓ_eq : ℓ = Nat.log 2 (G.m / G.n) + 1)
    (hCphi : maxPhiDenOf K_nat thr G.m ≤ C_phi * (G.m + 2) ^ 1)
    (hspace : h + decompSpace C_phi c G.n G.m < 2 ^ w)
    (hB4 : (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 4 < 2 ^ w)
    (hcited_ub_def : ∀ (m_tw : ℕ), 200 ≤ m_tw → m_tw ≤ 4 * G.m →
      K * (2 * ↑G.n + (↑m_tw + 2) ^ (1 + K / ↑(rOf m_tw)) *
        Real.log (↑m_tw + 2) ^ (K * ↑(rOf m_tw) ^ 2) / (1 / 200 : ℝ) ^ 2) ≤ ↑c_cited_ub)
    (hlevel_ub : ∀ (curM D : ℕ), curM ≤ G.m → D * G.n ≤ 2 * G.m →
      ∀ (cw_s : ℕ), cw_s ≤ c_ws_ub →
        ↑(levelCost G.n curM D (phiDenHalf K_nat thr G.m) c_cited_ub (runnerScale P) cw_s) ≤
          C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m)
    (hc_ws_spec : ∀ (D : ℕ) (curG : Cited.Graph), curG.IsValid → curG.m ≤ G.m → D * G.n ≤ 2 * G.m →
      curG.n = G.n →
        2 ^ (wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) + 1) ≤
          2 * (416 * (G.n + G.m + 2)) ^ c ∧
        wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) ≤ c_ws_ub)
    (mem_orig : ℕ → ℕ) (recs : List DecompLevelRec) (remG : Cited.Graph) (remIdx : List ℕ)
    (arena zc : ℕ) (st : State)
    (hinv : DecompLoopInv G gAddr h ℓ (phiDenHalf K_nat thr G.m) c (k + 1) mem_orig recs remG remIdx arena zc st) :
    ∃ recs' remG' remIdx' arena' zc' st' c_step,
      Runs w p ω (decomposeStepBody (b + 11)) st .normal st' c_step ∧
      DecompLoopInv G gAddr h ℓ (phiDenHalf K_nat thr G.m) c k mem_orig recs' remG' remIdx' arena' zc' st' ∧
      ↑c_step ≤ C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m + 100 := by
  classical
  set D_phi := phiDenHalf K_nat thr G.m
  set L := mkDecompLayout h G.n G.m D_phi
  have hb := mkDecompLayout_bounds h G.n G.m D_phi
  change DecompLayoutBounds L h G.n G.m D_phi at hb
  have hL_sp : L.statePtr = h + 4 + 5 * G.m := hb.hsp
  have hL_bnd : L.boundsAddr = L.statePtr + 3 := hb.hbnd
  have hL_lvl : L.lvlArrAddr = L.boundsAddr + 2 * G.m + 6 := hb.hlvl
  have hL_g0 : L.g0Addr = L.lvlArrAddr + G.m := hb.hg0
  have hL_i0 : L.idx0Addr = L.g0Addr + 2 + 2 * G.m := hb.hi0
  have hL_g1 : L.g1Addr = L.idx0Addr + G.m := hb.hg1
  have hL_i1 : L.idx1Addr = L.g1Addr + 2 + 2 * G.m := hb.hi1
  have hL_tw : L.twAddr = L.idx1Addr + G.m := hb.htw
  have hL_buf : L.bufAddr = L.twAddr + 6 + 8 * G.n + 18 * G.m := hb.hbuf
  have hL_bw : L.bufAddr ≤ L.workAddr := by rw [hb.hwork]; omega
  have hL_wk : L.workAddr ≤ L.keptVertAddr := by rw [hb.hkept]; omega
  have hL_ar : L.arena₀ = L.keptVertAddr + G.n := hb.har
  have hL_zc : L.zeroCursor₀ = L.arena₀ + 4 * G.m := hb.hzc
  have hL_ar_m : arena + 4 * remG.m ≤ L.zeroCursor₀ := hinv.harena_m
  have hL_ar_ge : L.arena₀ ≤ arena := hinv.harena_ge
  have hL_zc_ge : L.zeroCursor₀ ≤ zc := hinv.hzc_ge
  have hL_zc_le' : zc ≤ L.zeroCursor₀ + (ℓ - (k + 1)) * (1 + (416 * (G.n + G.m + 2)) ^ c) := hinv.hzc_le
  let ca := curAddrs L (ℓ - (k + 1))
  let lvl := k + 1
  let D := 2 ^ lvl
  have hk_le : k + 1 ≤ ℓ := hinv.hk
  have hB_def : 201 ≤ G.n + G.m + maxPhiDenOf K_nat thr G.m + 2 := by
    have hp := le_phiDenHalf_thr K_nat thr G.m
    have hm : maxPhiDenOf K_nat thr G.m = 3 * D_phi := rfl
    omega
  have hB1 : G.n + G.m + maxPhiDenOf K_nat thr G.m + 2 < 2 ^ w := by
    have hpow : (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 1 ≤
        (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simp only [pow_one] at hpow; omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h201w : 201 ≤ 2 ^ w := by omega
  have hDphi_eq : maxPhiDenOf K_nat thr G.m = 3 * D_phi := rfl
  have h200_Dphi : 200 ≤ D_phi := by have := le_phiDenHalf_thr K_nat thr G.m; omega
  have hthr_Dphi : thr + 1 ≤ D_phi := le_phiDenHalf_thr K_nat thr G.m
  have hthr_w : thr < 2 ^ w := by omega
  have hlvl_le_m : ℓ ≤ G.m := by
    have hlog := natLog2_add_one_le_self' (Nat.div_pos (le_of_lt hnm) h1n)
    have hdiv : G.m / G.n ≤ G.m := Nat.div_le_self G.m G.n
    omega
  have h2pow_ell_n : 2 ^ ℓ * G.n ≤ 2 * G.m := hℓ_eq ▸ two_pow_ell_mul_n_le h1n hnm
  have hDn_le : D * G.n ≤ 2 * G.m := by
    have hle : 2 ^ lvl ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by omega) hk_le
    exact le_trans (Nat.mul_le_mul_right G.n hle) h2pow_ell_n
  have hcurM_le_m : remG.m ≤ G.m := hinv.hrem_m_le
  have hL_zc_le : L.zeroCursor₀ - h ≤ (100 + 64 * C_phi) * (G.n + G.m + 2) ^ 2 := by
    apply layout_zeroCursor_le
    have h3 : D_phi ≤ maxPhiDenOf K_nat thr G.m := by rw [hDphi_eq]; omega
    simp only [pow_one] at hCphi
    exact le_trans h3 hCphi
  have hds_zc : L.zeroCursor₀ + (G.m + 2) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) + 2 * G.n + 5 ≤
      h + decompSpace C_phi c G.n G.m := by
    unfold decompSpace
    have hm1 : (G.m + 2) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) +
        (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) =
        (G.m + 3) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) := by ring
    have hpos : 1 ≤ 1 + 2 * (416 * (G.n + G.m + 2)) ^ c := by omega
    omega
  have hzc_cur_le : zc + (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) + 2 * G.n + 5 ≤ 2 ^ w := by
    have hdone_le : ℓ - (k + 1) ≤ G.m + 1 := by omega
    have hpow1 : 1 + (416 * (G.n + G.m + 2)) ^ c ≤ 1 + 2 * (416 * (G.n + G.m + 2)) ^ c := by omega
    have h1 := Nat.mul_le_mul_right (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) hdone_le
    have h2 : (ℓ - (k + 1)) * (1 + (416 * (G.n + G.m + 2)) ^ c) ≤
        (ℓ - (k + 1)) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) :=
      Nat.mul_le_mul_left _ hpow1
    have hmul_sum : (G.m + 1) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) +
        (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) =
        (G.m + 2) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) := by ring
    linarith [hL_zc_le']
  have hzc_w : zc < 2 ^ w := by omega
  have hL_zc_w : L.zeroCursor₀ < 2 ^ w := by omega
  have hbnd_le : L.boundsAddr + 2 * lvl + 1 < L.lvlArrAddr := by omega
  have hL_lvl_le_zc : L.lvlArrAddr ≤ L.zeroCursor₀ := by omega
  have hbnd_w1 : L.boundsAddr + 2 * lvl < 2 ^ w := by omega
  have hbnd_w2 : L.boundsAddr + (2 * lvl + 1) < 2 ^ w := by omega
  have h2lvl_w : 2 * lvl < 2 ^ w := by omega
  have h2lvl1_w : 2 * lvl + 1 < 2 ^ w := by omega
  have hsp_w : L.statePtr < 2 ^ w := by omega
  have har_w : arena < 2 ^ w := by omega
  let st1 : State := { st with mem := Function.update st.mem (L.boundsAddr + 2 * lvl) arena }
  have hr_regs := hinv.hregs
  have hst1_run : Runs w p ω
      (.store (.bin .add (.reg rBounds) (.bin .mul (.const 2) (.reg rLvl))) (.load (.reg rStatePtr)))
      st .normal st1 8 := by
    apply runs_store_iff.mpr
    refine ⟨L.boundsAddr + 2 * lvl, arena,
      dp_ev_add (dp_ev_reg (dr_bnd hr_regs))
        (dp_ev_mul (dp_ev_const h2w) (dp_ev_reg (dr_lvl hr_regs)) h2lvl_w)
        hbnd_w1,
      dp_ev_load (dp_ev_reg (dr_sp hr_regs)) hinv.hstate_ar,
      rfl, rfl, by simp [Expr.size]⟩
  have hsplit : SplitDisjoint ca.1 ca.2.1 ca.2.2.1 ca.2.2.2 L.lvlArrAddr L.bufAddr L.keptVertAddr
      remG.n remG.m G.m := by
    rw [hinv.hrem_n]
    dsimp only [ca, curAddrs]
    by_cases hp : (ℓ - (k + 1)) % 2 = 0 <;> simp [hp]
    · exact layout_splitDisjoint_g0 hcurM_le_m
    · exact layout_splitDisjoint_g1 hcurM_le_m
  have hca_le_tw : ca.1 + 2 + 2 * remG.m ≤ L.twAddr ∧ ca.2.1 + remG.m ≤ L.twAddr ∧
      ca.2.2.1 + 2 + 2 * remG.m ≤ L.twAddr ∧ ca.2.2.2 + remG.m ≤ L.twAddr := by
    dsimp only [ca, curAddrs]
    by_cases hp : (ℓ - (k + 1)) % 2 = 0 <;> simp [hp] <;> omega
  have hca_ge_lvl : L.lvlArrAddr ≤ ca.1 ∧ L.lvlArrAddr ≤ ca.2.1 ∧
      L.lvlArrAddr ≤ ca.2.2.1 ∧ L.lvlArrAddr ≤ ca.2.2.2 := by
    dsimp only [ca, curAddrs]
    by_cases hp : (ℓ - (k + 1)) % 2 = 0 <;> simp [hp] <;> omega
  have hst1_curG : GraphAt st1.mem ca.1 remG := by
    intro idx hidx
    have hne : ca.1 + idx ≠ L.boundsAddr + 2 * lvl := by omega
    dsimp only [st1]; rw [Function.update_of_ne hne]; exact hinv.hcurG_at idx hidx
  have hst1_curIdx : ListAt st1.mem ca.2.1 remIdx := by
    intro idx hidx
    have hne : ca.2.1 + idx ≠ L.boundsAddr + 2 * lvl := by omega
    dsimp only [st1]; rw [Function.update_of_ne hne]; exact hinv.hcurIdx_at idx hidx
  have hst1_sp0 : st1.mem L.statePtr = arena := by
    dsimp only [st1]
    rw [Function.update_of_ne (by omega : L.statePtr ≠ L.boundsAddr + 2 * lvl)]
    exact hinv.hstate_ar
  have hst1_sp1 : st1.mem (L.statePtr + 1) = zc := by
    dsimp only [st1]
    rw [Function.update_of_ne (by omega : L.statePtr + 1 ≠ L.boundsAddr + 2 * lvl)]
    exact hinv.hstate_zc
  have hst1_sp2 : st1.mem (L.statePtr + 2) = (recs.map (fun x => x.rawComps)).flatten.length := by
    dsimp only [st1]
    rw [Function.update_of_ne (by omega : L.statePtr + 2 ≠ L.boundsAddr + 2 * lvl)]
    exact hinv.hstate_tot
  have hst1_zero : ZeroFrom st1.mem zc := by
    intro a ha
    have hne : a ≠ L.boundsAddr + 2 * lvl := by omega
    dsimp only [st1]; rw [Function.update_of_ne hne]; exact hinv.hzero a ha
  have hB3 : (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 3 ≤ 2 ^ w := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ G.n + G.m + maxPhiDenOf K_nat thr G.m + 2)
      (by omega : 3 ≤ 4)
    omega
  have htw_cited : thr ≤ remG.m + D * remG.n →
      ∃ out cost_c,
        RunsTo (wordSize c ((twinGraph D remG).encode ++ [1, 200, rOf (remG.m + D * remG.n)]))
          P ((twinGraph D remG).encode ++ [1, 200, rOf (remG.m + D * remG.n)]) (fun _ => false) out cost_c ∧
        IsExpanderDecomposition (twinGraph D remG) (1 / 200)
          ((1 / 200 : ℝ) / (K * Real.log ((↑((twinGraph D remG).m) : ℝ) + 2) ^ (K * ↑(rOf (remG.m + D * remG.n)) ^ 2))) out ∧
        (1 : ℝ) / ↑D_phi ≤ (1 / 200 : ℝ) / (K * Real.log ((↑((twinGraph D remG).m) : ℝ) + 2) ^ (K * ↑(rOf (remG.m + D * remG.n)) ^ 2)) ∧
        cost_c ≤ c_cited_ub := by
    intro hthr_mtw
    have hmtw_eq : (twinGraph D remG).m = remG.m + D * remG.n := twinGraph_m D remG
    have hm_le_4m : remG.m + D * remG.n ≤ 4 * G.m := by rw [hinv.hrem_n]; omega
    have hmtw_200 : 200 ≤ remG.m + D * remG.n := le_trans hthr200 hthr_mtw
    obtain ⟨out, cost_c, hrun_c, his_dec, hcost_c⟩ :=
      hDec (twinGraph D remG)
        (twinGraph_isValid hinv.hrem_valid) (twinGraph_isLoopless hinv.hrem_loopless)
        (by rw [hmtw_eq]; exact le_trans hthr_cr hthr_mtw) (fun _ => false)
    refine ⟨out, cost_c, by simpa [hmtw_eq] using hrun_c, by simpa [hmtw_eq] using his_dec, ?_, ?_⟩
    · rw [hmtw_eq]
      exact one_div_phiDenHalf_le_cited hK hK_nat hm_le_4m
    · have htw_n : (twinGraph D remG).n = 2 * G.n := by simp [twinGraph, hinv.hrem_n]
      rw [htw_n, hmtw_eq] at hcost_c
      have hcb := hcited_ub_def (remG.m + D * remG.n) hmtw_200 hm_le_4m
      have hreal : (cost_c : ℝ) ≤ (c_cited_ub : ℝ) := by
        calc (cost_c : ℝ)
            ≤ K * (↑(2 * G.n) + (↑(remG.m + D * remG.n) + 2) ^ (1 + K / ↑(rOf (remG.m + D * remG.n))) *
                Real.log (↑(remG.m + D * remG.n) + 2) ^ (K * ↑(rOf (remG.m + D * remG.n)) ^ 2) /
                ((1 : ℝ) / (200 : ℝ)) ^ 2) := by simpa using hcost_c
          _ = K * (2 * ↑G.n + (↑(remG.m + D * remG.n) + 2) ^ (1 + K / ↑(rOf (remG.m + D * remG.n))) *
                Real.log (↑(remG.m + D * remG.n) + 2) ^ (K * ↑(rOf (remG.m + D * remG.n)) ^ 2) /
                (1 / 200 : ℝ) ^ 2) := by push_cast; ring
          _ ≤ (c_cited_ub : ℝ) := hcb
      exact_mod_cast hreal
  have htw_buf : L.twAddr + 6 + 6 * remG.n + 6 * (remG.m + D * remG.n) + 2 * remG.n ≤ L.bufAddr := by
    rw [hinv.hrem_n]; omega
  have hbuf_work : L.bufAddr + groupBufSize remG.n remG.m ≤ L.workAddr := by
    rw [hinv.hrem_n, hb.hwork]; simp only [groupBufSize]; omega
  have hwork_kept : L.workAddr +
      partWorkSize remG.n remG.m (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * remG.m + 1) + 1) + 2) ≤
      L.keptVertAddr := by
    rw [hinv.hrem_n, hb.hkept]
    have hlog : Nat.log 2 (2 * remG.m + 1) ≤ Nat.log 2 (2 * G.m + 1) := Nat.log_mono_right (by omega)
    apply Nat.add_le_add_left
    simp only [partWorkSize, pruneWorkSpace]
    have hdp_mul : 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * remG.m + 1) + 1) ≤
        4 * (4 * D_phi + 2) * (Nat.log 2 (2 * G.m + 1) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hkept_ar : L.keptVertAddr + remG.n ≤ arena := by rw [hinv.hrem_n]; omega
  have har_zc : arena + 4 * remG.m ≤ zc := le_trans hL_ar_m hL_zc_ge
  have har_w : arena + 4 * remG.m + 2 + remG.n < 2 ^ w := by rw [hinv.hrem_n]; omega
  have hlog_w : Nat.log 2 (remG.m + D * remG.n) + 1 < 2 ^ w := by
    rw [hinv.hrem_n]
    have hle : Nat.log 2 (remG.m + D * G.n) + 1 ≤ Nat.log 2 (4 * G.m) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
    have h2 : Nat.log 2 (4 * G.m) + 1 ≤ 4 * G.m := natLog2_add_one_le_self' (by omega : 1 ≤ 4 * G.m)
    omega
  have hrOf_w : (rOf (remG.m + D * remG.n) + 1) ^ 3 < 2 ^ w := by
    have hr_le : rOf (remG.m + D * remG.n) ≤ Nat.log 2 (remG.m + D * remG.n) := by
      have hp := rOf_pow_le (remG.m + D * remG.n)
      rcases Nat.eq_zero_or_pos (rOf (remG.m + D * remG.n)) with hr0 | hrpos
      · omega
      · have h1 : rOf (remG.m + D * remG.n) ≤ rOf (remG.m + D * remG.n) ^ 3 :=
          calc rOf (remG.m + D * remG.n) = rOf (remG.m + D * remG.n) ^ 1 := (pow_one _).symm
            _ ≤ rOf (remG.m + D * remG.n) ^ 3 := Nat.pow_le_pow_right hrpos (by omega)
        exact le_trans h1 hp
    have hlog_4m : Nat.log 2 (remG.m + D * remG.n) ≤ G.m + 1 := by
      rw [hinv.hrem_n]
      have h1 : remG.m + D * G.n ≤ 4 * G.m := by omega
      have h2 : Nat.log 2 (remG.m + D * G.n) ≤ Nat.log 2 (4 * G.m) := Nat.log_mono_right h1
      have h3 : 4 * G.m < 2 ^ (Nat.log 2 G.m + 3) := by
        have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < 2) G.m
        rw [show Nat.log 2 G.m + 3 = (Nat.log 2 G.m + 1) + 2 by omega, pow_add]
        omega
      have h4 : Nat.log 2 (4 * G.m) < Nat.log 2 G.m + 3 :=
        (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mpr h3
      have h5 : Nat.log 2 G.m + 1 ≤ G.m := natLog2_add_one_le_self' (by omega)
      omega
    have h1 : rOf (remG.m + D * remG.n) + 1 ≤ G.n + G.m + maxPhiDenOf K_nat thr G.m + 2 := by omega
    have h2 := Nat.pow_le_pow_left h1 3
    have h3 : (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 3 ≤
        (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact lt_of_le_of_lt (le_trans h2 h3) hB4
  have hrun_w : thr ≤ remG.m + D * remG.n →
      zc + 2 * remG.n +
        2 ^ (wordSize c ((twinGraph D remG).encode ++ [1, 200, rOf (remG.m + D * remG.n)]) + 1) + 2 ≤ 2 ^ w := by
    intro _
    have hcws : 2 ^ (wordSize c ((twinGraph D remG).encode ++ [1, 200, rOf (remG.m + D * remG.n)]) + 1) ≤
        2 * (416 * (G.n + G.m + 2)) ^ c :=
      (hc_ws_spec D remG hinv.hrem_valid hcurM_le_m hDn_le hinv.hrem_n).1
    calc zc + 2 * remG.n +
          2 ^ (wordSize c ((twinGraph D remG).encode ++ [1, 200, rOf (remG.m + D * remG.n)]) + 1) + 2
        = zc + 2 * G.n +
            2 ^ (wordSize c ((twinGraph D remG).encode ++ [1, 200, rOf (remG.m + D * remG.n)]) + 1) + 2 := by
            rw [hinv.hrem_n]
      _ ≤ zc + 2 * G.n + 2 * (416 * (G.n + G.m + 2)) ^ c + 2 := by
            have := Nat.add_le_add_right (Nat.add_le_add_left hcws (zc + 2 * G.n)) 2
            simpa [Nat.add_assoc] using this
      _ ≤ zc + (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) + 2 * G.n + 5 := by omega
      _ ≤ 2 ^ w := hzc_cur_le
  have hword_part : 8 * (4 * D_phi + 2) * remG.m + 4 * (4 * D_phi + 2) + 2 * remG.n + 2 * remG.m +
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * remG.m + 1) + 1) + 2) + 16 < 2 ^ w := by
    set B := G.n + G.m + maxPhiDenOf K_nat thr G.m + 2
    have h4dp : 4 * D_phi + 2 ≤ 2 * B := by have := hDphi_eq; omega
    have hlog : Nat.log 2 (2 * remG.m + 1) + 1 ≤ 2 * G.m + 1 :=
      le_trans (Nat.log_mono_right (by omega) |> fun h => Nat.add_le_add_right h 1)
        (natLog2_add_one_le_self' (by omega))
    have ht1 : 8 * (4 * D_phi + 2) * remG.m ≤ 16 * B ^ 2 := by
      nlinarith only [h4dp, show remG.m ≤ B by omega]
    have ht2 : 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * remG.m + 1) + 1) ≤ 24 * B ^ 2 := by
      nlinarith only [h4dp, show Nat.log 2 (2 * remG.m + 1) + 1 ≤ 3 * B by omega]
    have hrem : 4 * (4 * D_phi + 2) + 2 * remG.n + 2 * remG.m + 2 + 16 ≤ 20 * B := by
      rw [hinv.hrem_n]; omega
    have hB_sq : 60 * B ^ 2 < B ^ 3 := by nlinarith only [hB_def]
    have hle : 8 * (4 * D_phi + 2) * remG.m + 4 * (4 * D_phi + 2) + 2 * remG.n + 2 * remG.m +
        (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * remG.m + 1) + 1) + 2) + 16 ≤ 60 * B ^ 2 := by
      have : 20 * B ≤ 20 * B ^ 2 := by nlinarith only [hB_def]
      omega
    omega
  have hword_D : 2 * remG.m * D_phi + D + 4 < 2 ^ w := by
    set B := G.n + G.m + maxPhiDenOf K_nat thr G.m + 2
    have hD_le : D ≤ 2 * G.m := le_trans (Nat.le_mul_of_pos_right D h1n) hDn_le
    have hmB : remG.m ≤ B := by omega
    have hdpB : D_phi ≤ B := by have := hDphi_eq; omega
    have hDB2 : D + 4 ≤ 2 * B ^ 2 := by
      nlinarith only [hD_le, show 2 * G.m + 4 ≤ 2 * B by omega, hB_def]
    have hle : 2 * remG.m * D_phi + D + 4 ≤ 4 * B ^ 2 := by nlinarith only [hmB, hdpB, hDB2]
    have hB_sq : 4 * B ^ 2 < B ^ 3 := by nlinarith only [hB_def]
    omega
  have hword_Dphi : D + 3 * D_phi < 2 ^ w := by
    have hD_le : D ≤ 2 * G.m := le_trans (Nat.le_mul_of_pos_right D h1n) hDn_le
    rw [← hDphi_eq]; omega
  have htot_w : (recs.map (fun x => x.rawComps)).flatten.length + remG.n < 2 ^ w := by
    have ht := hinv.htotal_m; rw [hinv.hrem_n]; omega
  have hca_lt_zc : ca.1 < L.zeroCursor₀ ∧ ca.2.1 < L.zeroCursor₀ ∧
      ca.2.2.1 < L.zeroCursor₀ ∧ ca.2.2.2 < L.zeroCursor₀ ∧
      L.lvlArrAddr < L.zeroCursor₀ ∧ L.twAddr < L.zeroCursor₀ ∧
      L.bufAddr < L.zeroCursor₀ ∧ L.workAddr < L.zeroCursor₀ ∧ L.keptVertAddr < L.zeroCursor₀ := by
    dsimp only [ca, curAddrs]
    by_cases hp : (ℓ - (k + 1)) % 2 = 0 <;> simp only [hp, ite_true, ite_false] <;> omega
  have hargs_w : ∀ a ∈ [ca.1, ca.2.1, ca.2.2.1, ca.2.2.2, L.lvlArrAddr, L.twAddr, L.bufAddr,
      L.workAddr, L.keptVertAddr, L.statePtr, lvl, D, D_phi, G.m], a < 2 ^ w := by
    intro a ha
    have hD_le : D ≤ 2 * G.m := le_trans (Nat.le_mul_of_pos_right D h1n) hDn_le
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hs_lvl : L.statePtr + 3 ≤ L.lvlArrAddr := by omega
  obtain ⟨st_lvl, c_lvl, arena₁, zeroCursor', rawComps_lvl, validRs, remG', Gi, remIdx', keptIdx, keptFlag,
      hlvl_run, harena_ge1, _, hmem_sp, hmem_zc, hmem_tot, hzero', hzc_ge1, hzc_le1,
      hlist_ar, harena_eq, hvalid_eq, hraw_props, hGi_n, hrem_n', hGi_valid, hGi_loopless,
      hrem_valid', hrem_loopless', hperm, hGi_m, hrem_m', hRs_disj, hRs_prop, hcov,
      hremG'_at, hremIdx'_at, hremIdx'_len, _, hremIdx'_pw, hremIdx'_lt,
      hkeptIdx_len, _, hkeptIdx_pw, _,
      hremG'_edges, hremIdx'_eq, hGi_edges, hkeptIdx_eq, hlvl_arr, hframe_lvl, hc_lvl⟩ :=
    level_runs (b_run := b + 12) (b_csr := b + 1) (b_bfs := b + 2) (b_gv := b + 7)
      (b_ge := b + 8) (b_part := b + 10) (b_prune := b + 9) (thr := thr)
      (P_cited := P) (c_cited := c)
      st1.mem st1.pos ω remG remIdx ca.1 ca.2.1 ca.2.2.1 ca.2.2.2
      L.lvlArrAddr L.twAddr L.bufAddr L.workAddr L.keptVertAddr L.statePtr lvl D D_phi G.m
      zc arena (recs.map (fun x => x.rawComps)).flatten.length c_cited_ub
      hinv.hrem_valid hinv.hrem_loopless (hinv.hrem_n ▸ h1n) (by omega) rfl
      (by rw [hinv.hrem_n]; exact hinv.hrem_m_le_pow) hcurM_le_m h200_Dphi hst1_curG hinv.hidx_len hinv.hidx_pw
      hinv.hidx_lt hst1_curIdx hst1_sp0 hst1_sp1 hst1_sp2 hst1_zero
      hc.hCsr hc.hBfs hc.hRun hc.hGv hc.hGe hc.hPart hc.hPrune
      htw_cited hthr_Dphi hthr_w hs_lvl hsplit
      hca_le_tw.1 hca_le_tw.2.1 hca_le_tw.2.2.1 hca_le_tw.2.2.2
      htw_buf hbuf_work hwork_kept hkept_ar har_zc har_w hlog_w hrOf_w h201w hzc_w
      hrun_w hword_part hword_D hword_Dphi (by omega) (by omega) htot_w hargs_w
  let st2 : State := { mem := st_lvl.mem, regs := Function.update st1.regs rRet 0, pos := st_lvl.pos }
  have hst2_run : Runs w p ω
      (.call rRet (b + 11)
        [ .reg rCurG, .reg rCurIdx, .reg rNextG, .reg rNextIdx
        , .reg rLvlArr, .reg rTw, .reg rBuf, .reg rWork, .reg rKept
        , .reg rStatePtr, .reg rLvl, .reg rD, .reg rDphi, .reg rM ])
      st1 .normal st2 (14 + c_lvl + 1) := by
    apply runs_call_iff.mpr
    refine ⟨[ca.1, ca.2.1, ca.2.2.1, ca.2.2.2, L.lvlArrAddr, L.twAddr, L.bufAddr, L.workAddr,
        L.keptVertAddr, L.statePtr, lvl, D, D_phi, G.m],
      levelProc (b + 12) (b + 1) (b + 2) (b + 7) (b + 8) (b + 10) thr,
      .returned 0, st_lvl, c_lvl, ?_, hc.hLvl, hlvl_run, rfl, ?_, ?_⟩
    · simp only [evalArgs.eq_2, evalArgs.eq_1, Expr.eval, st1]
      rw [dr_curG hr_regs, dr_curIdx hr_regs, dr_nextG hr_regs, dr_nextIdx hr_regs,
        dr_lvlArr hr_regs, dr_tw hr_regs, dr_buf hr_regs, dr_work hr_regs,
        dr_kept hr_regs, dr_sp hr_regs, dr_lvl hr_regs, dr_d hr_regs,
        dr_dphi hr_regs, dr_m hr_regs]
    · simp only [Outcome.value]; rfl
    · simp [argsSize, Expr.size]
  let st3 : State := { st2 with mem := Function.update st2.mem (L.boundsAddr + 2 * lvl + 1) arena₁ }
  have hst2_regs : ∀ r ≤ 20, st2.regs r = st.regs r := fun r hr => by
    dsimp only [st2, st1]
    have hr26 : rRet = 26 := rfl
    rw [Function.update_of_ne (by omega : r ≠ rRet)]
  have hr_regs2 := decompRegs_of_eq hst2_regs hr_regs
  have hst3_run : Runs w p ω
      (.store (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.reg rLvl)) (.const 1)))
        (.load (.reg rStatePtr)))
      st2 .normal st3 10 := by
    apply runs_store_iff.mpr
    refine ⟨L.boundsAddr + (2 * lvl + 1), arena₁,
      dp_ev_add (dp_ev_reg (dr_bnd hr_regs2))
        (dp_ev_add (dp_ev_mul (dp_ev_const h2w) (dp_ev_reg (dr_lvl hr_regs2)) h2lvl_w)
          (dp_ev_const h1w) h2lvl1_w)
        hbnd_w2,
      dp_ev_load (dp_ev_reg (dr_sp hr_regs2)) hmem_sp,
      rfl, rfl, by simp [Expr.size]⟩
  have hD_le_w : 2 ^ (k + 1) < 2 ^ w := by
    have hD_eq : D = 2 ^ (k + 1) := rfl
    have : D ≤ 2 * G.m := le_trans (Nat.le_mul_of_pos_right D h1n) hDn_le
    omega
  obtain ⟨st4, c4, hst4_run, hst4_regs, hst4_mem, _, hc4⟩ :=
    swap_regs_step gAddr h G.n G.m ℓ D_phi k ca.1 ca.2.1 ca.2.2.1 ca.2.2.2 L st3
      h1w h2w (by omega) hD_le_w hr_regs2
  have hst4_mem_ne : ∀ a, a ≠ L.boundsAddr + 2 * lvl + 1 → st4.mem a = st_lvl.mem a := fun a hne => by
    rw [hst4_mem]; dsimp only [st3, st2]; exact Function.update_of_ne hne arena₁ st_lvl.mem
  have hst4_mem_bnd1 : st4.mem (L.boundsAddr + 2 * lvl + 1) = arena₁ := by
    rw [hst4_mem]; dsimp only [st3, st2]; exact Function.update_self _ _ _
  have hst1_mem_ne : ∀ a, a ≠ L.boundsAddr + 2 * lvl → st1.mem a = st.mem a := fun a hne => by
    dsimp only [st1]; exact Function.update_of_ne hne arena st.mem
  have hst1_mem_bnd0 : st1.mem (L.boundsAddr + 2 * lvl) = arena := by
    dsimp only [st1]; exact Function.update_self _ _ _
  have hfull := runs_seq hst1_run (runs_seq hst2_run (runs_seq hst3_run hst4_run))
  change Runs w p ω (decomposeStepBody (b + 11)) st .normal st4 _ at hfull
  let rec_new : DecompLevelRec := ⟨lvl, rawComps_lvl, validRs, Gi, keptIdx⟩
  have hzc_spec := hc_ws_spec D remG hinv.hrem_valid hcurM_le_m hDn_le hinv.hrem_n
  have hinv' : DecompLoopInv G gAddr h ℓ D_phi c k mem_orig (rec_new :: recs) remG' remIdx'
      arena₁ zeroCursor' st4 :=
    decomposeStep_mk_inv hlvl_le_m h200_Dphi hinv harena_ge1 hmem_sp hmem_zc hmem_tot
      hzero' hzc_ge1 hzc_le1 hlist_ar harena_eq hvalid_eq hraw_props hGi_n hrem_n'
      hrem_valid' hrem_loopless' hperm hGi_m hrem_m' hRs_disj hRs_prop hcov
      hremG'_at hremIdx'_at hremIdx'_len hremIdx'_pw hkeptIdx_pw
      hremG'_edges hremIdx'_eq hGi_edges hkeptIdx_eq hlvl_arr hframe_lvl
      hst4_regs hst4_mem_ne hst4_mem_bnd1 hst1_mem_ne hst1_mem_bnd0 hzc_spec.1
  have hc_lvl_r : (c_lvl : ℝ) ≤ C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m := by
    have h1 := hlevel_ub remG.m D hcurM_le_m hDn_le _ hzc_spec.2
    have h2 : (c_lvl : ℝ) ≤ ↑(levelCost G.n remG.m D D_phi c_cited_ub (runnerScale P)
        (wordSize c ((twinGraph D remG).encode ++ [1, 200, rOf (remG.m + D * remG.n)]))) :=
      Nat.cast_le.mpr (hinv.hrem_n ▸ hc_lvl)
    exact le_trans h2 h1
  have hstep_bd : ((8 + ((14 + c_lvl + 1) + (10 + c4 + 1) + 1) + 1 : ℕ) : ℝ) ≤
      C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m + 100 := by
    have hc_nat_le : 8 + ((14 + c_lvl + 1) + (10 + c4 + 1) + 1) + 1 ≤ c_lvl + 100 := by omega
    have hcast_le : ((8 + ((14 + c_lvl + 1) + (10 + c4 + 1) + 1) + 1 : ℕ) : ℝ) ≤
        ((c_lvl + 100 : ℕ) : ℝ) := Nat.cast_le.mpr hc_nat_le
    have hc_100 : ((100 : ℕ) : ℝ) = 100 := by norm_num
    rw [Nat.cast_add c_lvl 100, hc_100] at hcast_le
    linarith
  exact ⟨rec_new :: recs, remG', remIdx', arena₁, zeroCursor', st4, _, hfull, hinv', hstep_bd⟩

lemma decomposeLevelLoop_runs {K cr : ℝ} {P : Program} {c : ℕ} (hK : 0 < K)
    (hDec : ∀ G_tw : Cited.Graph, G_tw.IsValid → G_tw.IsLoopless → thresholdB1 cr ≤ G_tw.m →
      ∀ ω : ℕ → Bool, ∃ out cost,
        RunsTo (wordSize c (G_tw.encode ++ [1, 200, rOf G_tw.m])) P (G_tw.encode ++ [1, 200, rOf G_tw.m]) ω out cost ∧
        IsExpanderDecomposition G_tw (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
          ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) / (K * Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2))) out ∧
        (cost : ℝ) ≤ K * (G_tw.n + ((G_tw.m : ℝ) + 2) ^ (1 + K / rOf G_tw.m) *
          Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2) / (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2))
    {K_nat thr b : ℕ} (hK_nat : K ≤ ↑K_nat) (hthr200 : 200 ≤ thr) (hthr_cr : thresholdB1 cr ≤ thr)
    {w C_phi : ℕ} {p : Program} {ω : ℕ → Bool}
    (hc : DecompProgContracts K_nat thr P c w b p)
    (G : Cited.Graph) (gAddr h ℓ : ℕ) (C₀_lvl C_lvl : ℝ) (c_cited_ub c_ws_ub : ℕ)
    (h1n : 1 ≤ G.n) (hnm : G.n < G.m) (hℓ_eq : ℓ = Nat.log 2 (G.m / G.n) + 1)
    (hCphi : maxPhiDenOf K_nat thr G.m ≤ C_phi * (G.m + 2) ^ 1)
    (hspace : h + decompSpace C_phi c G.n G.m < 2 ^ w)
    (hB4 : (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 4 < 2 ^ w)
    (hcited_ub_def : ∀ (m_tw : ℕ), 200 ≤ m_tw → m_tw ≤ 4 * G.m →
      K * (2 * ↑G.n + (↑m_tw + 2) ^ (1 + K / ↑(rOf m_tw)) *
        Real.log (↑m_tw + 2) ^ (K * ↑(rOf m_tw) ^ 2) / (1 / 200 : ℝ) ^ 2) ≤ ↑c_cited_ub)
    (hlevel_ub : ∀ (curM D : ℕ), curM ≤ G.m → D * G.n ≤ 2 * G.m →
      ∀ (cw_s : ℕ), cw_s ≤ c_ws_ub →
        ↑(levelCost G.n curM D (phiDenHalf K_nat thr G.m) c_cited_ub (runnerScale P) cw_s) ≤
          C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m)
    (hc_ws_spec : ∀ (D : ℕ) (curG : Cited.Graph), curG.IsValid → curG.m ≤ G.m → D * G.n ≤ 2 * G.m →
      curG.n = G.n →
        2 ^ (wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) + 1) ≤
          2 * (416 * (G.n + G.m + 2)) ^ c ∧
        wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) ≤ c_ws_ub)
    (mem_orig : ℕ → ℕ)
    (k : ℕ) (recs : List DecompLevelRec) (remG : Cited.Graph) (remIdx : List ℕ)
    (arena zc : ℕ) (st : State)
    (hinv : DecompLoopInv G gAddr h ℓ (phiDenHalf K_nat thr G.m) c k mem_orig recs remG remIdx arena zc st) :
    ∃ recs' remG' remIdx' arena' zc' st' c_loop,
      Runs w p ω (decomposeLevelLoop (b + 11)) st .normal st' c_loop ∧
      DecompLoopInv G gAddr h ℓ (phiDenHalf K_nat thr G.m) c 0 mem_orig recs' remG' remIdx' arena' zc' st' ∧
      ↑c_loop ≤ ↑k * (C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m + 100) + 6 * ↑k + 4 := by
  induction k generalizing recs remG remIdx arena zc st with
  | zero =>
    have h0w : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have h1w : 1 < 2 ^ w := by
      have := hB4; have : 201 ≤ G.n + G.m + maxPhiDenOf K_nat thr G.m + 2 := by
        have := le_phiDenHalf_thr K_nat thr G.m; have : maxPhiDenOf K_nat thr G.m = 3 * phiDenHalf K_nat thr G.m := rfl; omega
      have h1 : 201 ^ 4 ≤ (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    have hev : Expr.eval w st (.bin .lt (.const 0) (.reg rLvl)) = some 0 := by
      simpa using dp_ev_lt (dp_ev_const h0w) (dp_ev_reg (dr_lvl hinv.hregs)) h1w
    have hrun : Runs w p ω (decomposeLevelLoop (b + 11)) st .normal st ((Expr.bin .lt (.const 0) (.reg rLvl)).size + 1) :=
      runs_loop_iff.mpr (Or.inl ⟨hev, rfl, rfl, rfl⟩)
    refine ⟨recs, remG, remIdx, arena, zc, st, _, hrun, hinv, ?_⟩
    simp [Expr.size]
  | succ k ih =>
    have h0w : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have h1w : 1 < 2 ^ w := by
      have := hB4; have : 201 ≤ G.n + G.m + maxPhiDenOf K_nat thr G.m + 2 := by
        have := le_phiDenHalf_thr K_nat thr G.m; have : maxPhiDenOf K_nat thr G.m = 3 * phiDenHalf K_nat thr G.m := rfl; omega
      have h1 : 201 ^ 4 ≤ (G.n + G.m + maxPhiDenOf K_nat thr G.m + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    have hev : Expr.eval w st (.bin .lt (.const 0) (.reg rLvl)) = some 1 := by
      simpa using dp_ev_lt (dp_ev_const h0w) (dp_ev_reg (dr_lvl hinv.hregs)) h1w
    obtain ⟨recs1, remG1, remIdx1, arena1, zc1, st1, c1, hstep, hinv1, hc1⟩ :=
      decomposeStep_preserves hK hDec hK_nat hthr200 hthr_cr hc G gAddr h ℓ k C₀_lvl C_lvl
        c_cited_ub c_ws_ub h1n hnm hℓ_eq hCphi hspace hB4 hcited_ub_def hlevel_ub hc_ws_spec
        mem_orig recs remG remIdx arena zc st hinv
    obtain ⟨recs', remG', remIdx', arena', zc', st', c2, htail, hinv', hc2⟩ :=
      ih recs1 remG1 remIdx1 arena1 zc1 st1 hinv1
    have hrun : Runs w p ω (decomposeLevelLoop (b + 11)) st .normal st'
        ((Expr.bin .lt (.const 0) (.reg rLvl)).size + c1 + c2 + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, c1, c2, hev, by omega, hstep, htail, rfl⟩))
    refine ⟨recs', remG', remIdx', arena', zc', st', _, hrun, hinv', ?_⟩
    have hsz : (Expr.bin .lt (.const 0) (.reg rLvl)).size = 3 := rfl
    set S : ℝ := C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m + 100
    have hcast_lhs : ((Expr.bin .lt (.const 0) (.reg rLvl)).size + c1 + c2 + 1 : ℕ) = (4 : ℝ) + ↑c1 + ↑c2 := by
      rw [hsz]; push_cast; ring
    have hcast_rhs : (↑(k + 1) : ℝ) * S + 6 * ↑(k + 1) + 4 = ↑k * S + S + 6 * ↑k + 10 := by
      push_cast; ring
    rw [hcast_lhs, hcast_rhs]
    linarith


end

end MinCostFlow.Expander
