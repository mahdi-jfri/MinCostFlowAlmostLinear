module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBRoundHelpers

import Mathlib.Tactic.Linarith

/-!
# Step B Single-Round Procedure and Proof (`ProgStepBRound`)

Defines and verifies `sbOneRoundStmt bSubCore bRoute`, executing one round of Step B's parallel
block cut-matching game (`OneShotStepB.stepBRound`) by running `sbQueryLoopStmt bSubCore`
followed by `sbOneRoundAfterQueryStmt bRoute`.

Main results:
- `sbOneRoundStmt`, `sbOneRoundStmt_noRand`
- `sbOneRound_step`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Single-Round Statement -/

/-- One round of the Step B block cut-matching game (`r15 = m`, `0 ≤ m ≤ 49 * L`). -/
def sbOneRoundStmt (bSubCore bRoute : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 13) (.const 0))
    (seqStmts [
      .assign 22 (.reg 12),
      .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 5))),
      .assign 24 (.bin .add (.bin .add (.reg 23) (.const 1)) (.bin .mul (.reg 5) (.bin .add (.const 2) (.reg 4)))),
      .assign 25 (.const 0),
      .assign 26 (.bin .add (.reg 23) (.const 1)),
      .assign 12 (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 5) (.reg 4))) (.const 2)),
      sbQueryLoopStmt bSubCore,
      sbOneRoundAfterQueryStmt bRoute
    ])
    .nop

theorem sbOneRoundStmt_noRand (bSubCore bRoute : ℕ) :
    (sbOneRoundStmt bSubCore bRoute).NoRand := by
  simp [sbOneRoundStmt, sbQueryLoopStmt_noRand, sbOneRoundAfterQueryStmt_noRand, seqStmts, Stmt.NoRand]

/-! ## 2. Post-Query Dispatch Proof (`sbOneRound_afterQuery`) -/

private lemma sbOneRound_afterQuery {cfg : ParamConfig} {M r q w bRoute C_rt C_sp Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 hRound cutRecsA pairsA tmpA hSub0 m : ℕ}
    {p : Program} {mem0 memStart : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    {stQ : State} {ω : ℕ → Bool}
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w))
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt mem0 pA (coreParamsOf cfg M r) r)
    (hG_at : GraphAt mem0 gA G) (hG_val : G.IsValid)
    (hX_at : VertsAt mem0 xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2) (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k) (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hm_le : m ≤ 49 * LParam M)
    (hmod : SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z m bst)
    (hpers : SbPersistAt memStart G X b nBlocks (LParam M) h0 bst)
    (hF_at0 : EdgesAt memStart fA (callsFakeEdges bst.calls))
    (hfr0 : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) →
      (a < fA ∨ fA + 2 * k ≤ a) → (a < outA ∨ outA + 2 + k ≤ a) → memStart a = mem0 a)
    (hgeom : gA + 2 + 2 * G.m ≤ h0 ∧ xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧
      locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ outA + 2 + k ≤ h0 ∧
      DisjointRange locA G.n gA (2 + 2 * G.m) ∧ DisjointRange locA G.n xA k ∧
      DisjointRange locA G.n pA (coreParamsSize r) ∧ DisjointRange locA G.n fA (2 * k) ∧
      DisjointRange locA G.n outA (2 + k) ∧ DisjointRange outA (2 + k) gA (2 + 2 * G.m) ∧
      DisjointRange outA (2 + k) xA k ∧ DisjointRange outA (2 + k) pA (coreParamsSize r) ∧
      DisjointRange outA (2 + k) fA (2 * k) ∧ DisjointRange fA (2 * k) gA (2 + 2 * G.m) ∧
      DisjointRange fA (2 * k) xA k ∧ DisjointRange fA (2 * k) pA (coreParamsSize r))
    (hlay : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ hRound ∧
      hRound ≤ (sbPersist h0 k b nBlocks (LParam M)).hPersist +
        m * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks ∧
      cutRecsA = hRound ∧ pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧ hSub0 = tmpA + 4 * b + 2 + b ∧
      hRound + sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks < 2 ^ w ∧
      (coreParamsOf cfg M r).Δ < 2 ^ w ∧ 128 < 2 ^ w)
    (hInvQ : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 memStart G X bst nBlocks res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists stQ)
    (hr14Q : stQ.regs 14 = (callsFakeEdges bst.calls).length)
    (hr15Q : stQ.regs 15 = m) :
    ∃ st' cost,
      Runs w p ω (sbOneRoundAfterQueryStmt bRoute) stQ .normal st' cost ∧
      SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X (m + 1)
        { mem := st'.mem, regs := Function.update st'.regs 15 (m + 1), pos := st'.pos } ∧
      st'.regs 15 = m ∧
      cost ≤ C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt + 350 * k + 360 * nBlocks + 340 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  set t := cutIds.length
  rcases hgeom with ⟨hg_h, hx_h, hp_h, hloc_h, hf_h, hout_h, hd_lg, hd_lx, hd_lp, hd_lf, hd_lo,
    hd_og, hd_ox, hd_op, hd_of, hd_fg, hd_fx, hd_fp⟩
  rcases hlay with ⟨hhP_le, hhR_le, hcut_eq, hpairs_eq, htmp_eq, hhSub_eq, hStep_w, hΔ_w, hw16⟩
  have hcfg : CoreParamsValid cp r := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnb_div : nBlocks = k / b := by rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX_at.1]
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hb_pos : 0 < b := by have := harith.2.2.1; omega
  have hb_even : Even b := harith.2.2.2.1
  have hXL : X.card < 2 ^ cp.L := by rw [← hX_at.1]; exact harith.2.2.2.2.2.2.2.2
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le vs b
    rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  have hb_le_k : b ≤ k := by rw [hb_eq]; exact hklo
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by
    dsimp only [ps, sbPersist]; omega
  have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
  have hsub0_bound : hSub0 ≤ hRound + 6 * k + 5 * nBlocks + 3 := by
    have hmul : nBlocks * (2 + b) = 2 * nBlocks + nBlocks * b := by ring
    omega
  have hstep_def : sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks =
      nBlocks * Sprev + outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
      6 * k + 6 * nBlocks + 2 * G.n + 10 := rfl
  have hQ12_step : stQ.regs 12 + 2 + 2 * G.n +
      outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) ≤
      hRound + sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks := by
    have := hInvQ.h_le; omega
  have ht_le_nb : t ≤ nBlocks := by
    dsimp only [t]; rw [hInvQ.cutIds_eq]
    exact (List.length_filterMap_le _ _).trans (by rw [List.length_range])
  -- Connect `cutIds` / `pairs` to `sbModelInv_round_step`
  have hstep_mod := sbModelInv_round_step hcfg hX_sub hGloop hdegG hXL
    (Finset.sort_nodup X (· ≤ ·)) (by ext u; simp) hb_pos hb_even
    (hnb_eq ▸ hmod) res (fun i hi hact => hInvQ.res_spec i (hnb_eq.symm ▸ hi) hact)
  dsimp only at hstep_mod
  set rpairs : List (ℕ × (Finset ℕ × Finset ℕ)) := (List.range nBlocks).filterMap fun i =>
    if bst.active i then match res i with
      | .expander _ => none
      | .cut U => let B := blockSet vs b i; let C' := padToHalf B (smallerSide B U); some (i, (C', B \ C'))
    else none
  have hrp_eq : rpairs = (List.range (numFullBlocks vs b)).filterMap (fun i =>
      if bst.active i then match res i with
        | .expander _ => none
        | .cut U => let B := blockSet vs b i; let C' := padToHalf B (smallerSide B U); some (i, (C', B \ C'))
      else none) := by rw [← hnb_eq]
  have hfs := sb_rpairs_fst_snd (nBlocks := nBlocks) (b := b) (vs := vs) (bst := bst) (res := res)
  have hcut_rp : cutIds = rpairs.map Prod.fst := hInvQ.cutIds_eq.trans hfs.1.symm
  have hpairs_rp : pairs = rpairs.map Prod.snd := hInvQ.pairs_eq.trans hfs.2.symm
  have hvtp : ValidTerminalPairs X pairs := by
    convert hstep_mod.1 using 1
    rw [hpairs_rp, ← hnb_eq]; rfl
  -- Store `mem[pairsA] := t`
  let memP := Function.update stQ.mem pairsA t
  let stP : State := { mem := memP, regs := stQ.regs, pos := stQ.pos }
  have hstoreP : Runs w p ω (.store (.reg 23) (.reg 25)) stQ .normal stP
      (Expr.size (.reg 23) + Expr.size (.reg 25) + 1) :=
    runs_store_n (Expr.eval_reg_of_eq hInvQ.r23) (Expr.eval_reg_of_eq hInvQ.r25)
  have hfrP_below : ∀ a < ps.wRelA, (a < locA ∨ locA + G.n ≤ a) →
      (a < ps.actA ∨ ps.wBaseA ≤ a) → memP a = memStart a := fun a ha h1 h2 => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.frame_persist a ha h1 h2
  have hfrP_w : ∀ a, ps.wBaseA ≤ a → a < ps.wRelA → memP a = memStart a := fun a h1 h2 => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.frame_w a h1 h2
  have hlocP : ∀ u < G.n, memP (locA + u) = 0 := fun u hu => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.loc0 u hu
  have hzfP : ZeroFrom memP (stQ.regs 12) := fun a ha => by
    have := hInvQ.h_ge; dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.zf a ha
  -- Split on `t = 0` vs `t > 0`
  by_cases ht0 : t = 0
  · exact sbOneRound_afterQuery_zero ha hrl hq2 hqr hX_at hX_sub hGloop hdegG hklo hkhi hb_eq
      hnb_eq hz_eq hm_le hmod hpers hF_at0 hfr0 ⟨hloc_h, hf_h, hd_lf⟩
      ⟨hhP_le, hhR_le, hcut_eq, hpairs_eq, htmp_eq, hhSub_eq, hStep_w, hw16⟩
      hInvQ hr14Q hr15Q ht0
  · -- Non-empty `pairs` (`t > 0`): invoke `bRoute` and handle `.cut` / `.matched`!
    set rtOutA := stQ.regs 12
    set hRt := rtOutA + 2 + 2 * G.n
    set pairLists := cPrimeLists.zip compLists
    have hmp : MultiPairsAt memP pairsA pairLists ∧ (encodePairs pairLists).length = 1 + t * (2 + b) :=
      multiPairsAt_of_fixed_stride hb_even hInvQ.lens_eq.2.2.1 hInvQ.lens_eq.2.2.2.1
        (by dsimp only [memP]; rw [Function.update_self])
        (fun idx hidx => by
          rcases hInvQ.recs_at idx hidx with ⟨hcA, hoA, _, _, _, hp0, hp1, _, _, hcLen, hoLen, hLatC, hLatO⟩
          have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨u, hu⟩; omega
          exact ⟨by dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hp0,
            by dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hp1,
            hcLen, hoLen,
            fun u hu => by dsimp only [memP]; rw [Function.update_of_ne (by omega)]; rw [← hcA]; exact hLatC u hu,
            fun u hu => by dsimp only [memP]; rw [Function.update_of_ne (by omega)]; rw [← hoA]; exact hLatO u hu⟩)
    have hpairLists_nd : ∀ p ∈ pairLists, p.1.Nodup ∧ p.2.Nodup := by
      intro p hp
      rcases List.mem_iff_getElem.mp hp with ⟨idx, hidx, rfl⟩
      have hidx_t : idx < t := by
        simp only [pairLists, List.length_zip, hInvQ.lens_eq.2.2.1, hInvQ.lens_eq.2.2.2.1, min_self] at hidx; exact hidx
      rcases hInvQ.recs_at idx hidx_t with ⟨_, _, _, _, _, _, _, hcL, hoL, _, _, _, _⟩
      simp only [pairLists, List.getElem_zip, hcL, hoL]
      exact ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _⟩
    have hpairLists_map : pairLists.map (fun p => (p.1.toFinset, p.2.toFinset)) = pairs := by
      refine List.ext_getElem (by
        simp only [pairLists, List.length_map, List.length_zip, hInvQ.lens_eq.2.2.1,
          hInvQ.lens_eq.2.2.2.1, hInvQ.lens_eq.2.2.2.2, min_self]) fun idx h1 h2 => ?_
      have hidx_t : idx < t := by dsimp only [t]; rw [← hInvQ.lens_eq.2.2.2.2]; exact h2
      rcases hInvQ.recs_at idx hidx_t with ⟨_, _, _, _, _, _, _, hcL, hoL, _, _, _, _⟩
      simp only [pairLists, List.getElem_map, List.getElem_zip, hcL, hoL]
      ext u <;> simp
    have hG_P : GraphAt memP gA G := by
      have hagree : ∀ a, gA ≤ a → a < gA + 2 + 2 * G.m → memP a = mem0 a := fun a h1 h2 =>
        (hfrP_below a (by omega) (by rcases hd_lg with h | h <;> [right; left] <;> omega) (Or.inl (by omega))).trans
          (hfr0 a (by omega) (by rcases hd_lg with h | h <;> [right; left] <;> omega)
            (by rcases hd_fg with h | h <;> [right; left] <;> omega)
            (by rcases hd_og with h | h <;> [right; left] <;> omega))
      cases G with | mk gn ges =>
        rw [graphAt_mk_iff] at hG_at ⊢
        exact ⟨(hagree gA (by omega) (by simp [Graph.m]; omega)).trans hG_at.1,
          (hagree (gA + 1) (by omega) (by simp [Graph.m]; omega)).trans hG_at.2.1,
          fun idx hidx => ⟨(hagree _ (by omega) (by simp [Graph.m]; omega)).trans (hG_at.2.2 idx hidx).1,
            (hagree _ (by omega) (by simp [Graph.m]; omega)).trans (hG_at.2.2 idx hidx).2⟩⟩
    have hcp_P : CoreParamsAt memP pA cp r := by
      have hagree : ∀ a, pA ≤ a → a < pA + coreParamsSize r → memP a = mem0 a := fun a h1 h2 =>
        (hfrP_below a (by omega) (by rcases hd_lp with h | h <;> [right; left] <;> omega) (Or.inl (by omega))).trans
          (hfr0 a (by omega) (by rcases hd_lp with h | h <;> [right; left] <;> omega)
            (by rcases hd_fp with h | h <;> [right; left] <;> omega)
            (by rcases hd_op with h | h <;> [right; left] <;> omega))
      refine ⟨(hagree pA (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.1,
        (hagree (pA + 1) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.1,
        (hagree (pA + 2) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.1,
        (hagree (pA + 3) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.2.1,
        fun i hi => (hagree (pA + 4 + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.1 i hi),
        fun i hi => (hagree (pA + 5 + r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.1 i hi),
        fun i hi => (hagree (pA + 6 + 2 * r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.2 i hi)⟩
    have hXlen_P : LenListAt memP h0 vs :=
      ⟨(hfrP_below h0 (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans hpers.xLen_at.1,
        fun idx hidx => by
          have hidx' : idx < k := by rw [Finset.length_sort, ← hX_at.1] at hidx; exact hidx
          exact (hfrP_below (h0 + 1 + idx) (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (hpers.xLen_at.2 idx hidx)⟩
    have hrcCost_le : routerCallCost G X pairs cp.Δ cp.L 100 z ≤ stepBRouterR1 (NOf M r) (LParam M) q :=
      stepB_single_routerCallCost_le ha hrl hqr hX_sub hGloop hdegG
        (by rw [← hX_at.1]; have := harith.2.2.1; omega) (by rw [← hX_at.1]; exact hkhi) hvtp
        (by rw [hInvQ.lens_eq.2.2.2.2]; exact le_trans ht_le_nb harith.2.2.2.2.2.2.1)
    have hsp_mono : outerRouterSpace C_sp G.n (routerCallCost G X pairs cp.Δ cp.L 100 z) ≤
        outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) := by
      unfold outerRouterSpace; exact Nat.mul_le_mul_left C_sp (by omega)
    have hvs_fin : vs.toFinset = X := by ext u; simp [vs]
    have hrt_w_bnd : hRt + outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) < 2 ^ w := by
      have : hRt = rtOutA + 2 + 2 * G.n := rfl
      omega
    have hgeQ : ps.hPersist ≤ cutRecsA := by rw [hcut_eq, ← hps_id]; exact hhP_le
    have hrt_ge_sub : hSub0 ≤ rtOutA := hInvQ.h_ge
    have hlen_vs : vs.length = k := by rw [Finset.length_sort, ← hX_at.1]
    have hlen_mp : (encodePairs pairLists).length ≤ 1 + nBlocks * (2 + b) := by
      rw [hmp.2]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ht_le_nb) 1
    have hg_rt : gA + 2 + 2 * G.m ≤ rtOutA := by omega
    have hx_rt : h0 + 1 + vs.length ≤ rtOutA := by omega
    have hp_rt : pairsA + (encodePairs pairLists).length ≤ rtOutA := by omega
    have hrt_le_hRt : rtOutA ≤ hRt := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    have hPreRt : (multiPairRouterContract C_rt C_sp w).pre
        [gA, h0, pairsA, cp.Δ, cp.L, 100, z, rtOutA, hRt] memP :=
      ⟨gA, h0, pairsA, cp.Δ, cp.L, 100, z, rtOutA, hRt, G, vs, pairLists,
        rfl, hG_P, hG_val, hXlen_P, Finset.sort_nodup X (· ≤ ·), hvs_fin.symm ▸ hX_sub,
        hvs_fin.symm ▸ hGloop, by have := hcfg.hΔ; omega, hvs_fin.symm ▸ hdegG,
        by have := hcfg.hL; omega, hvs_fin.symm ▸ hXL, by decide,
        hmp.1, hpairLists_nd, by rw [hvs_fin, hpairLists_map]; exact hvtp,
        fun a ha => hzfP a (le_trans hrt_le_hRt ha),
        le_trans hg_rt hrt_le_hRt, le_trans hx_rt hrt_le_hRt, le_trans hp_rt hrt_le_hRt,
        le_refl _, Or.inr (by omega), Or.inr (by omega), Or.inr hp_rt,
        by rw [hvs_fin, hpairLists_map]; exact lt_of_le_of_lt (Nat.add_le_add_left hsp_mono hRt) hrt_w_bnd,
        by omega,
        by rw [Finset.length_sort, ← hX_at.1]; exact hmG,
        by rw [Finset.length_sort, ← hX_at.1, hz_eq]; exact Nat.div_le_self _ _⟩
    have hreadG : readGraph memP gA = G := readGraph_eq_of_graphAt hG_P
    have hreadX : (readLenPrefixedList memP h0).toFinset = X := by
      rw [readLenPrefixedList_eq_of_lenListAt hXlen_P, hvs_fin]
    have hreadP : readMultiPairs memP pairsA = pairs := by
      rw [readMultiPairs_eq_of_multiPairsAt hmp.1, hpairLists_map]
    have hL_w : cp.L < 2 ^ w := by
      have : cp.L ≤ cp.Δ := by change LParam M ≤ 1024 * LParam M; omega
      omega
    have hhRt_lt_w : hRt < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hrt_w_bnd
    have hrt_lt_w : rtOutA < 2 ^ w := lt_of_le_of_lt hrt_le_hRt hhRt_lt_w
    have hh0_rt : h0 ≤ rtOutA := le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) hx_rt)
    have hpA2_h0 : pA + 2 ≤ h0 := by unfold coreParamsSize at hp_h; omega
    have hz_k : z ≤ k := by rw [hz_eq]; exact Nat.div_le_self _ _
    obtain ⟨hAfterRt, memR, stR, cR, hrunsR, hmemR_eq, hr12R, hr27R, hlt27R, hRoutR,
      hRt_le, hRt_ub, hzfR, hfrR, hcR⟩ :=
      sbOneRound_callRouter (stP := stP) (ω := ω) hRoute hG_P hcp_P.2.2.1 hcp_P.2.1 hreadG hreadX hreadP
        hrcCost_le hsp_mono hPreRt rfl
        ⟨lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) hg_rt)) hrt_lt_w,
         lt_of_le_of_lt hh0_rt hrt_lt_w,
         lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hp_rt) hrt_lt_w,
         lt_of_le_of_lt (le_trans hpA2_h0 hh0_rt) hrt_lt_w, hΔ_w, hL_w,
         lt_of_le_of_lt (le_trans hz_k (by rw [← hlen_vs]; exact le_trans (Nat.le_add_left _ _) hx_rt)) hrt_lt_w,
         hhRt_lt_w, hw16⟩
        ⟨hInvQ.args.r1, hInvQ.args.r6, hInvQ.args.r7, hInvQ.args.r11, rfl, hInvQ.r23⟩ rfl
    -- Helper: combine `hrunsR` with post-router branch `postS`
    have hcomb_all : ∀ (st' : State) (cPost : ℕ),
        Runs w p ω (.cond (.bin .eq (.load (.reg 27)) (.const 1))
            (seqStmts [sbCopyCutZeroStmt 27 10 30 31 32, .assign 13 (.const 1)])
            sbMatchedPostStmt) stR .normal st' cPost →
        ∃ cost, Runs w p ω (sbOneRoundAfterQueryStmt bRoute) stQ .normal st' cost ∧
          cost ≤ cR + cPost + 20 := by
      intro st' cPost hPost
      have hseqR : Runs w p ω (seqStmts [
          .assign 27 (.reg 12),
          .assign 28 (.load (.reg 1)),
          .assign 29 (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 28))),
          .assign 30 (.load (.bin .add (.reg 7) (.const 2))),
          .assign 31 (.load (.bin .add (.reg 7) (.const 1))),
          .call 12 bRoute [.reg 1, .reg 11, .reg 23, .reg 30, .reg 31, .const 100, .reg 6, .reg 27, .reg 29],
          .cond (.bin .eq (.load (.reg 27)) (.const 1))
            (seqStmts [sbCopyCutZeroStmt 27 10 30 31 32, .assign 13 (.const 1)])
            sbMatchedPostStmt]) stP .normal st' (cR + cPost + 1) := by
        dsimp only [seqStmts] at hrunsR ⊢
        rcases runs_seq_n_mp hrunsR with ⟨s1, c1a, c1b, h1a, h1b, rfl⟩
        rcases runs_seq_n_mp h1b with ⟨s2, c2a, c2b, h2a, h2b, rfl⟩
        rcases runs_seq_n_mp h2b with ⟨s3, c3a, c3b, h3a, h3b, rfl⟩
        rcases runs_seq_n_mp h3b with ⟨s4, c4a, c4b, h4a, h4b, rfl⟩
        rcases runs_seq_n_mp h4b with ⟨s5, c5a, c5b, h5a, h5b, rfl⟩
        have hc := runs_seq_n h1a (runs_seq_n h2a (runs_seq_n h3a
          (runs_seq_n h4a (runs_seq_n h5a (runs_seq_n h5b hPost)))))
        have hceq : c1a + (c2a + (c3a + (c4a + (c5a + (c5b + cPost + 1) + 1) + 1) + 1) + 1) + 1 =
            c1a + (c2a + (c3a + (c4a + (c5a + c5b + 1) + 1) + 1) + 1) + 1 + cPost + 1 := by omega
        rwa [hceq] at hc
      have hcond_ne0 : (.bin .eq (.reg 25) (.const 0) : Expr).eval w stP = some 0 :=
        Expr.eval_eq_false (Expr.eval_reg_of_eq hInvQ.r25) (Expr.eval_const (by omega)) ht0 (by omega)
      exact ⟨_, runs_seq_n hstoreP (runs_cond_f hcond_ne0 hseqR), by simp only [Expr.size]; omega⟩
    -- Case split on `routeOrCut G X pairs cp.Δ cp.L 100 z`
    cases hrc_eq : routeOrCut G X pairs cp.Δ cp.L 100 z with
    | cut U =>
      have hcut_spec : RouteCutSpec G X 100 z U := by
        have hstep_rc := hstep_mod.2.2
        split at hstep_rc
        · next U' hrt =>
          have heq : routeOrCut G X pairs cp.Δ cp.L 100 z = .cut U' := by
            rw [← hrt]; congr 1; rw [hpairs_rp, ← hnb_eq]; rfl
          rw [hrc_eq] at heq; cases heq; exact hstep_rc
        · next matchings' emb' hrt =>
          have heq : routeOrCut G X pairs cp.Δ cp.L 100 z = .matched matchings' emb' := by
            rw [← hrt]; congr 1; rw [hpairs_rp, ← hnb_eq]; rfl
          rw [hrc_eq] at heq; cases heq
      rw [hrc_eq] at hRoutR
      rcases hRoutR with ⟨htag1, U_l, hU_nd, hU_fin, hU_len_mem, hU_atR⟩
      have hU_card : U_l.length = U.card := by rw [← hU_fin, List.toFinset_card_of_nodup hU_nd]
      have hU_le_k : U_l.length ≤ k := by
        rw [hU_card, hX_at.1]; exact Finset.card_le_card hcut_spec.1
      have hU_le_n : U_l.length ≤ G.n := by
        rw [hU_card]; exact Finset.card_range G.n ▸ Finset.card_le_card (hcut_spec.1.trans hX_sub)
      have hpostRun : ∃ o st' cPost,
          Runs w p ω (.cond (.bin .eq (.load (.reg 27)) (.const 1))
              (seqStmts [sbCopyCutZeroStmt 27 10 30 31 32, .assign 13 (.const 1)])
              sbMatchedPostStmt) stR o st' cPost ∧
          (normalPost fun st' =>
            (∀ r < 27, r ≠ 13 → st'.regs r = stR.regs r) ∧
            st'.regs 13 = 1 ∧
            MemFrame memR st'.mem outA (outA + (2 + U_l.length)) ∧
            CoreOutAt st'.mem outA (.cut U)) o st' ∧
          cPost ≤ 32 * k + 60 := by
        refine runs_start_le ?_
        refine runs_cond_le (v := 1)
          (Expr.eval_eq_true (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr27R) (hmemR_eq ▸ htag1))
            (Expr.eval_const (by omega)) rfl (by omega))
          (fun _ => ?_) (fun h => absurd h (by decide))
        dsimp only [seqStmts]
        refine runs_seq_triple_le
          (sbCopyCutZero_triple (w := w) (cap := 2 + U_l.length) (srcA := rtOutA) (dstA := outA)
            (rSrc := 27) (rDst := 10) (rLen := 30) (rI := 31) (rU := 32) (by decide)
            p memR U_l stR hU_len_mem hU_atR (le_refl _) (Or.inl (by omega))
            (by omega) (by omega) (by omega) hr27R ((hlt27R 10 (by decide) (by decide)).trans hInvQ.args.r10)
            hmemR_eq) rfl ?_
        intro st1 ⟨hoth1, _, hfr1, htag0, hlen1, hlat1⟩
        refine runs_assign_le (v := 1) (Expr.eval_const (by omega)) ?_ (by simp only [Expr.size]; omega)
        exact ⟨fun r hr h13 => by dsimp only; rw [Function.update_of_ne h13]; exact hoth1 r (by omega) (by omega) (by omega),
          by simp, hfr1, htag0, U_l, hU_nd, hU_fin, hlen1, hlat1⟩
      rcases hpostRun with ⟨o, st', cPost, hPost, hPpost, hcPost⟩
      cases o with
      | returned _ => exact False.elim hPpost
      | normal =>
        rcases hPpost with ⟨hreg', hr13', hfr', hCoreOut⟩
        obtain ⟨cost, hruns_full, hcost⟩ := hcomb_all st' cPost hPost
        refine ⟨st', cost, hruns_full, ?_, (hreg' 15 (by decide) (by decide)).trans ((hlt27R 15 (by decide) (by decide)).trans hr15Q), by omega⟩
        have hloc' : ∀ u < G.n, st'.mem (locA + u) = 0 := fun u hu => by
          rw [hfr' (locA + u) (by rcases hd_lo with h | h <;> [left; right] <;> omega),
            hfrR (locA + u) (by omega) (Or.inl (by omega))]
          exact hlocP u hu
        refine ⟨sbArgs_of_eq hInvQ.args (fun r hr => by
            dsimp only; rw [Function.update_of_ne (by omega)]
            exact (hreg' r (by omega) (by omega)).trans (hlt27R r (by omega) (by omega))),
          by simp, hloc',
          by dsimp only; rw [Function.update_of_ne (by decide), hreg' 12 (by decide) (by decide), hr12R, hps_id]; omega,
          by dsimp only; rw [Function.update_of_ne (by decide), hreg' 12 (by decide) (by decide), hr12R, hps_id]; rw [Nat.succ_mul]; omega,
          fun a ha => by
            dsimp only at ha ⊢; rw [Function.update_of_ne (by decide), hreg' 12 (by decide) (by decide), hr12R] at ha
            rw [hfr' a (Or.inr (by omega))]
            exact hzfR a ha,
          fun a ha h1 h2 h3 => by
            rw [hfr' a (by omega), hfrR a (by omega) (Or.inl (by omega)),
              hfrP_below a (by omega) h1 (Or.inl (by omega))]
            exact hfr0 a ha h1 h2 h3,
          Or.inl ⟨by dsimp only; rw [Function.update_of_ne (by decide), hr13'], U, hCoreOut, hcut_spec⟩⟩
    | matched matchings emb =>
      rw [hrc_eq] at hRoutR
      obtain ⟨st', cPost, hPost, hInv', hr15', hcPost⟩ :=
        sbOneRound_afterQuery_matched ha hrl hq2 hqr hG_val hX_at hX_sub hGloop hdegG
          hklo hkhi hb_eq hnb_eq hz_eq hm_le hmod hpers hF_at0 hfr0 ⟨hloc_h, hf_h, hd_lf⟩
          ⟨hhP_le, hhR_le, hcut_eq, hpairs_eq, htmp_eq, hhSub_eq, hStep_w, hw16⟩
          hInvQ hr14Q hr15Q ht0 hvtp hrc_eq hmemR_eq hr27R hlt27R hRoutR
          (hr12R.symm ▸ hRt_le) (hr12R.symm ▸ hRt_ub) (hr12R.symm ▸ hzfR)
          (fun a ha => hfrR a (by omega) (Or.inl ha))
      obtain ⟨cost, hruns_full, hcost⟩ := hcomb_all st' cPost hPost
      exact ⟨st', cost, hruns_full, hInv', hr15', by omega⟩

/-! ## 4. Full Single-Round Theorem (`sbOneRound_step`) -/

/-- One round of Step B advances `SbLoopInv ... m` to `SbLoopInv ... (m + 1)` (`m ≤ 49 * L`). -/
theorem sbOneRound_step {cfg : ParamConfig} {M r q w bSubCore bRoute C_rt C_sp Tprev Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 m : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {st : State} {ω : ℕ → Bool}
    (hSub : MeetsContract w p bSubCore (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev))
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w))
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt mem0 pA (coreParamsOf cfg M r) r)
    (hG_at : GraphAt mem0 gA G) (hG_val : G.IsValid)
    (hX_at : VertsAt mem0 xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2) (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k) (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hm_le : m ≤ 49 * LParam M)
    (hgeom : gA + 2 + 2 * G.m ≤ h0 ∧ xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧
      locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ outA + 2 + k ≤ h0 ∧
      DisjointRange locA G.n gA (2 + 2 * G.m) ∧ DisjointRange locA G.n xA k ∧
      DisjointRange locA G.n pA (coreParamsSize r) ∧ DisjointRange locA G.n fA (2 * k) ∧
      DisjointRange locA G.n outA (2 + k) ∧ DisjointRange outA (2 + k) gA (2 + 2 * G.m) ∧
      DisjointRange outA (2 + k) xA k ∧ DisjointRange outA (2 + k) pA (coreParamsSize r) ∧
      DisjointRange outA (2 + k) fA (2 * k) ∧ DisjointRange fA (2 * k) gA (2 + 2 * G.m) ∧
      DisjointRange fA (2 * k) xA k ∧ DisjointRange fA (2 * k) pA (coreParamsSize r))
    (hSpace_w : (sbPersist h0 k b nBlocks (LParam M)).hPersist +
      (m + 1) * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks < 2 ^ w)
    (hΔ_w : (coreParamsOf cfg M r).Δ < 2 ^ w)
    (hw128 : 128 < 2 ^ w)
    (hInv : SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X m st) :
    ∃ st' cost,
      Runs w p ω (sbOneRoundStmt bSubCore bRoute) st .normal st' cost ∧
      SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X (m + 1)
        { mem := st'.mem, regs := Function.update st'.regs 15 (m + 1), pos := st'.pos } ∧
      st'.regs 15 = m ∧
      cost ≤ nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
        1720 * k * LParam M + 750 * k + 1050 * nBlocks + 420 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set cp := coreParamsOf cfg M r
  have hcfg : CoreParamsValid cp r := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnb_div : nBlocks = k / b := by rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX_at.1]
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hb_even : Even b := harith.2.2.2.1
  have hb_le_N : b ≤ cp.N ^ (q - 1) := by rw [hb_eq]; exact Nat.div_le_self _ 2
  have hb_le_k : b ≤ k := by rw [hb_eq]; exact hklo
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le (X.sort (· ≤ ·)) b
    rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  rcases hInv.state_match with ⟨hr13, hcut⟩ | ⟨hr13, bst, hmod, hpers, hr14, hF_at⟩
  · -- Already cut in an earlier round (`r13 = 1`): `.nop`
    have hcond : (.bin .eq (.reg 13) (.const 0) : Expr).eval w st = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq hr13) (Expr.eval_const (by omega)) (by decide) (by omega)
    refine ⟨st, _, runs_cond_f hcond runs_nop_n, ?_, hInv.rm, by simp only [Expr.size]; omega⟩
    refine ⟨sbArgs_of_eq hInv.args (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
      by simp, hInv.loc0, by dsimp only; rw [Function.update_of_ne (by decide)]; exact hInv.h_ge,
      by dsimp only; rw [Function.update_of_ne (by decide)]; have := hInv.h_le; rw [Nat.succ_mul]; omega,
      by dsimp only; rw [Function.update_of_ne (by decide)]; exact hInv.zf, hInv.frame,
      Or.inl ⟨by dsimp only; rw [Function.update_of_ne (by decide), hr13], hcut⟩⟩
  · -- Active round (`r13 = 0`): setup scratch, run query loop, run post-query handler
    set hRound := st.regs 12
    set cutRecsA := hRound
    set pairsA := cutRecsA + 3 * nBlocks
    set tmpA := pairsA + 1 + nBlocks * (2 + b)
    set hSub0 := tmpA + 4 * b + 2 + b
    have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
    have hStep_w : hRound + sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks < 2 ^ w := by
      have h1 := hInv.h_le
      rw [Nat.succ_mul] at hSpace_w
      have h2 := Nat.add_le_add_right h1 (sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks)
      exact lt_of_le_of_lt (by dsimp only [hRound]; linarith) hSpace_w
    have hsub0_le : hSub0 ≤ hRound + 6 * k + 5 * nBlocks + 3 := by
      have hmul : nBlocks * (2 + b) = 2 * nBlocks + nBlocks * b := by ring
      omega
    have hstep_def : sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks =
        nBlocks * Sprev + outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
        6 * k + 6 * nBlocks + 2 * G.n + 10 := rfl
    have hsub_w : hSub0 + nBlocks * Sprev < 2 ^ w := by omega
    -- Step 1: evaluate the 6 setup assignments into `stSetup`
    let stSetup : State :=
      { mem := st.mem,
        regs := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update st.regs 22 cutRecsA) 23 pairsA) 24 tmpA) 25 0)
          26 (pairsA + 1)) 12 hSub0,
        pos := st.pos }
    have hSetup : ∃ c0, Runs w p ω (seqStmts [
        .assign 22 (.reg 12),
        .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 5))),
        .assign 24 (.bin .add (.bin .add (.reg 23) (.const 1)) (.bin .mul (.reg 5) (.bin .add (.const 2) (.reg 4)))),
        .assign 25 (.const 0),
        .assign 26 (.bin .add (.reg 23) (.const 1)),
        .assign 12 (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 5) (.reg 4))) (.const 2))])
        st .normal stSetup c0 ∧ c0 ≤ 40 := by
      have hrun0 : ∃ o s c0, Runs w p ω (seqStmts [
          .assign 22 (.reg 12),
          .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 5))),
          .assign 24 (.bin .add (.bin .add (.reg 23) (.const 1)) (.bin .mul (.reg 5) (.bin .add (.const 2) (.reg 4)))),
          .assign 25 (.const 0),
          .assign 26 (.bin .add (.reg 23) (.const 1)),
          .assign 12 (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 5) (.reg 4))) (.const 2))])
          st o s c0 ∧ (normalPost fun s => s = stSetup) o s ∧ c0 ≤ 40 := by
        refine runs_start_le ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := cutRecsA) (Expr.eval_reg_of_eq rfl) ?_
        refine runs_seq_assign_le (v := pairsA)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hInv.args.r5])) (by omega)) (by omega)) ?_
        refine runs_seq_assign_le (v := tmpA)
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r5]))
              (Expr.eval_add (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r4])) (by omega))
              (by omega)) (by omega)) ?_
        refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
        refine runs_seq_assign_le (v := pairsA + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]))
            (Expr.eval_const (by omega)) (by omega)) ?_
        refine runs_assign_le (v := hSub0)
          (by have heq : tmpA + 5 * b + 2 = hSub0 := by omega
              exact heq ▸ Expr.eval_add (Expr.eval_add
                (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]))
                (Expr.eval_mul (Expr.eval_const (by omega))
                  (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.args.r4]))
                  (by omega)) (by omega)) (Expr.eval_const (by omega)) (by omega))
          rfl (by simp only [Expr.size]; omega)
      rcases hrun0 with ⟨o, s, c0, hr0, hp0, hc0⟩
      cases o with
      | returned _ => exact False.elim hp0
      | normal => subst hp0; exact ⟨c0, hr0, hc0⟩
    rcases hSetup with ⟨c0, hrun0, hc0⟩
    have hcp_st : CoreParamsAt st.mem pA cp r := by
      rcases hgeom with ⟨_, _, hp_h, _, _, _, _, _, hd_lp, _, _, _, _, hd_op, _, _, _, hd_fp⟩
      have hagree : ∀ a, pA ≤ a → a < pA + coreParamsSize r → st.mem a = mem0 a := fun a h1 h2 =>
        hInv.frame a (by omega) (by rcases hd_lp with h | h <;> [right; left] <;> omega)
          (by rcases hd_fp with h | h <;> [right; left] <;> omega)
          (by rcases hd_op with h | h <;> [right; left] <;> omega)
      refine ⟨(hagree pA (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.1,
        (hagree (pA + 1) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.1,
        (hagree (pA + 2) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.1,
        (hagree (pA + 3) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.2.1,
        fun i hi => (hagree (pA + 4 + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.1 i hi),
        fun i hi => (hagree (pA + 5 + r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.1 i hi),
        fun i hi => (hagree (pA + 6 + 2 * r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.2 i hi)⟩
    have hX_st : VertsAt st.mem xA k X := by
      rcases hgeom with ⟨_, hx_h, _, _, _, _, _, hd_lx, _, _, _, _, hd_ox, _, _, _, hd_fx, _⟩
      refine ⟨hX_at.1, fun idx hidx => ?_⟩
      have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort, ← hX_at.1]
      rw [hInv.frame _ (by omega) (by rcases hd_lx with h | h <;> [right; left] <;> omega)
        (by rcases hd_fx with h | h <;> [right; left] <;> omega)
        (by rcases hd_ox with h | h <;> [right; left] <;> omega)]
      exact hX_at.2 idx hidx
    have hcur_lay : ps.hPersist ≤ cutRecsA ∧ pairsA = cutRecsA + 3 * nBlocks ∧
        tmpA = pairsA + 1 + nBlocks * (2 + b) ∧ hSub0 = tmpA + 4 * b + 2 + b ∧
        xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧ locA + G.n ≤ h0 ∧
        DisjointRange locA G.n xA k ∧ DisjointRange locA G.n pA (coreParamsSize r) ∧
        hSub0 + nBlocks * Sprev < 2 ^ w ∧ 16 < 2 ^ w :=
      ⟨hInv.h_ge, rfl, rfl, rfl, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1,
        hgeom.2.2.2.2.2.2.2.1, hgeom.2.2.2.2.2.2.2.2.1, hsub_w, by omega⟩
    obtain ⟨res, cutIds, pairs, cPA, oPA, cPL, oPL, stQ, cQ, hrunQ, hInvQ, hr14Q, hr15Q, hcQ⟩ :=
      sbQueryLoop_run (st₀ := stSetup) (ω := ω) hSub ha0 ha hrl hq2 hqr hcp_st hX_st hX_sub hb_even hb_le_N hnb_eq hm_le
        hmod hpers hcur_lay
        (sbArgs_of_eq hInv.args (fun r hr => by
          dsimp only [stSetup]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]))
        (by dsimp only [stSetup]; rw [Function.update_self])
        (by dsimp only [stSetup]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr13])
        (by dsimp only [stSetup]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
        (by dsimp only [stSetup]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
        (by dsimp only [stSetup]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
        (by dsimp only [stSetup]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
        (by dsimp only [stSetup]; rw [Function.update_of_ne (by decide), Function.update_self])
        (fun a ha => hInv.zf a (by omega)) hInv.loc0
    have hr14Q' : stQ.regs 14 = (callsFakeEdges bst.calls).length := by
      rw [hr14Q]; dsimp only [stSetup]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr14]
    have hr15Q' : stQ.regs 15 = m := by
      rw [hr15Q]; dsimp only [stSetup]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hInv.rm]
    obtain ⟨st', cA, hrunA, hInv', hr15', hcA⟩ :=
      sbOneRound_afterQuery (ω := ω) hRoute ha hrl hq2 hqr hcp_at hG_at hG_val hX_at hX_sub hGloop hdegG hmG
        hklo hkhi hb_eq hnb_eq hz_eq hm_le hmod hpers hF_at hInv.frame hgeom
        ⟨hInv.h_ge, hInv.h_le, rfl, rfl, rfl, rfl, hStep_w, hΔ_w, hw128⟩ hInvQ hr14Q' hr15Q'
    -- Combine setup + query loop + post-query into `sbOneRoundStmt`
    have hbody : Runs w p ω (seqStmts [
        .assign 22 (.reg 12),
        .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 5))),
        .assign 24 (.bin .add (.bin .add (.reg 23) (.const 1)) (.bin .mul (.reg 5) (.bin .add (.const 2) (.reg 4)))),
        .assign 25 (.const 0),
        .assign 26 (.bin .add (.reg 23) (.const 1)),
        .assign 12 (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 5) (.reg 4))) (.const 2)),
        sbQueryLoopStmt bSubCore,
        sbOneRoundAfterQueryStmt bRoute]) st .normal st' (c0 + (cQ + cA + 1) + 1) := by
      dsimp only [seqStmts] at hrun0 ⊢
      rcases runs_seq_n_mp hrun0 with ⟨s1, c1a, c1b, h1a, h1b, rfl⟩
      rcases runs_seq_n_mp h1b with ⟨s2, c2a, c2b, h2a, h2b, rfl⟩
      rcases runs_seq_n_mp h2b with ⟨s3, c3a, c3b, h3a, h3b, rfl⟩
      rcases runs_seq_n_mp h3b with ⟨s4, c4a, c4b, h4a, h4b, rfl⟩
      rcases runs_seq_n_mp h4b with ⟨s5, c5a, c5b, h5a, h5b, rfl⟩
      have hQA := runs_seq_n hrunQ hrunA
      have hc := runs_seq_n h1a (runs_seq_n h2a (runs_seq_n h3a
        (runs_seq_n h4a (runs_seq_n h5a (runs_seq_n h5b hQA)))))
      have hceq : c1a + (c2a + (c3a + (c4a + (c5a + (c5b + (cQ + cA + 1) + 1) + 1) + 1) + 1) + 1) + 1 =
          c1a + (c2a + (c3a + (c4a + (c5a + c5b + 1) + 1) + 1) + 1) + 1 + (cQ + cA + 1) + 1 := by omega
      rwa [hceq] at hc
    have hcond : (.bin .eq (.reg 13) (.const 0) : Expr).eval w st = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq hr13) (Expr.eval_const (by omega)) rfl (by omega)
    exact ⟨st', _, runs_cond_t hcond (by decide) hbody, hInv', hr15', by simp only [Expr.size]; omega⟩

end MinCostFlow.ExpanderDecomp
