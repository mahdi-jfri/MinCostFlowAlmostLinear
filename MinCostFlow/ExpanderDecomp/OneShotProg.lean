module

public import MinCostFlow.ExpanderDecomp.OneShotProgTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of the `OneShot` Word-RAM Procedure (`OneShotProg`)

Proves `oneShotProc_meetsContract`, showing that `oneShotProc idx` (`OneShotProgTail.lean`) meets
`oneShotContract`: given `CoreParamsAt`, a valid loopless induced host `(G, X)`, and
verified callees `idx.copyWords`, `idx.cloudExpander`, `idx.edgeColor17`, `idx.stepB`,
`idx.stepCMacro` (`ProgStepCSpec.stepCContract`), `idx.stepCLeftover`
(`ProgStepCSpec.stepCLeftoverContract`), and `idx.stepD`, it writes `CoreOutAt mem' outAddr res`
with `OneShotSpec (coreParamsOf cfg M r) q G X res`, preserves `ZeroFrom` and the zeroed `locAddr`
buffer, and runs within `oneShotProgCost` steps and `oneShotProgSpace` heap headroom.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma oneShotTailCD_conseq {w : ℕ} {p : Program} {idx : CoreIdx}
    {cfg : ParamConfig} {M r q C_stepC C_left C_sp : ℕ}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hcloud : MeetsContract w p idx.cloudExpander (cloudExpanderContract w))
    (hcol : MeetsContract w p idx.edgeColor17 (edgeColor17Contract w))
    (hstepC : MeetsContract w p idx.stepCMacro
      (stepCContract (coreParamsOf cfg M r) cloud C_stepC C_sp w))
    (hleft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) C_left C_sp w))
    (hstepD : MeetsContract w p idx.stepD (stepDContract w))
    {gAddr k xAddr locAddr outAddr h hCur mFB b numBlk z hBound : ℕ}
    {G : Graph} {X : Finset ℕ} {callsB : List RoutedCall} {mem₀ : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool} {Q : Outcome → State → Prop} {Pcost : ℕ → Prop}
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hG : GraphAt st.mem gAddr G) (hGvalid : G.IsValid)
    (hGn : G.n ≤ 2048 * LParam M * (NOf M r) ^ r)
    (hX : VertsAt st.mem xAddr k X) (hXrange : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hk2 : 2 ≤ k) (hkNq : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_pos : 0 < b) (hble : b ≤ k)
    (hnb_eq : numBlk = numFullBlocks (X.sort (· ≤ ·)) b)
    (hnb_ge1 : 1 ≤ numBlk) (hnb_le : numBlk ≤ 2 * (coreParamsOf cfg M r).N)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hloc : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hcallsB_len : callsB.length ≤ 49 * (coreParamsOf cfg M r).L + 2)
    (hcallsB_v : ∀ c ∈ callsB, c.Valid G X (routeCong (coreParamsOf cfg M r).Δ 100
      (coreParamsOf cfg M r).L) z)
    (hcallsB_exp : ∀ i < numBlk,
      (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
        (blockSet (X.sort (· ≤ ·)) b i) (1 / (2 * ((coreParamsOf cfg M r).P (q - 1) : ℝ))))
    (hmFB_eq : mFB = (callsFakeEdges callsB).length)
    (hFB : EdgesAt st.mem h (callsFakeEdges callsB))
    (hg_le : gAddr + 2 + 2 * G.m ≤ h) (hx_le : xAddr + k ≤ h)
    (hloc_le : locAddr + G.n ≤ h) (hout_le : outAddr + 2 + k ≤ h)
    (hhCur_ge : h + 2 * k ≤ hCur)
    (hd_lg : DisjointRange locAddr G.n gAddr (2 + 2 * G.m))
    (hd_lx : DisjointRange locAddr G.n xAddr k)
    (hd_lo : DisjointRange locAddr G.n outAddr (2 + k))
    (hd_og : DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hZero : ZeroFrom st.mem hCur)
    (hframe₀ : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a)
    (hBound_ge : hCur +
      stepCSpaceConst C_sp * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
      65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound)
    (hBound_w : hBound < 2 ^ w)
    (hr1 : st.regs 1 = gAddr) (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = xAddr)
    (hr5 : st.regs 5 = locAddr) (hr6 : st.regs 6 = outAddr)
    (hr8 : st.regs 8 = (coreParamsOf cfg M r).L) (hr9 : st.regs 9 = (coreParamsOf cfg M r).Δ)
    (hr11 : st.regs 11 = (coreParamsOf cfg M r).P q) (hr13 : st.regs 13 = z)
    (hr14 : st.regs 14 = b) (hr15 : st.regs 15 = numBlk)
    (hr16 : st.regs 16 = h) (hr17 : st.regs 17 = hCur) (hr18 : st.regs 18 = mFB)
    (hQ : ∀ v st_fin,
      (∃ res : CoreResult,
        CoreOutAt st_fin.mem outAddr res ∧ OneShotSpec (coreParamsOf cfg M r) q G X res) →
      h ≤ v → v ≤ hBound → ZeroFrom st_fin.mem v →
      (∀ u < G.n, st_fin.mem (locAddr + u) = 0) →
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st_fin.mem a = mem₀ a) →
      Q (.returned v) st_fin)
    (hB : ∀ c, c ≤ stepCTimeConst C_stepC C_left * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
      (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) →
      Pcost c) :
    ∃ o st_fin c, Runs w p ω (oneShotTailCD idx) st o st_fin c ∧ Q o st_fin ∧ Pcost c := by
  obtain ⟨v, st_fin, c, hrun, h1, h2, h3, h4, h5, h6, hc⟩ :=
    oneShotTailCD_runs hcopy hcloud hcol hstepC hleft hstepD st ω ha0 ha hrl hq1 hqr
      hG hGvalid hGn hX hXrange hGloop hdegG hmG hk2 hkNq hb_pos hble hnb_eq hnb_ge1 hnb_le hz_eq
      hloc hcallsB_len hcallsB_v hcallsB_exp hmFB_eq hFB hg_le hx_le hloc_le hout_le hhCur_ge
      hd_lg hd_lx hd_lo hd_og hd_ox hZero hframe₀ hBound_ge hBound_w
      hr1 hr2 hr3 hr5 hr6 hr8 hr9 hr11 hr13 hr14 hr15 hr16 hr17 hr18
  exact ⟨.returned v, st_fin, c, hrun, hQ v st_fin h1 h2 h3 h4 h5 h6, hB c hc⟩

/-- **`OneShot` Word-RAM contract**: `oneShotProc idx` meets `oneShotContract`. -/
theorem oneShotProc_meetsContract {w : ℕ} {p : Program} {idx : CoreIdx}
    {cfg : ParamConfig} {M r q K_B C_stepC C_left S_B C_sp Tprev Sprev : ℕ}
    (hself : p.procs[idx.oneShot]? = some (oneShotProc idx))
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hcloud : MeetsContract w p idx.cloudExpander (cloudExpanderContract w))
    (hcol : MeetsContract w p idx.edgeColor17 (edgeColor17Contract w))
    (hstepB : 2 ≤ q →
      MeetsContract w p idx.stepB (oneShotStepBContract cfg M r q w K_B S_B Tprev Sprev))
    (hstepC : MeetsContract w p idx.stepCMacro
      (stepCContract (coreParamsOf cfg M r) cloud C_stepC C_sp w))
    (hleft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) C_left C_sp w))
    (hstepD : MeetsContract w p idx.stepD (stepDContract w)) :
    MeetsContract w p idx.oneShot
      (oneShotContract cfg M r q w K_B (stepCTimeConst C_stepC C_left)
        S_B (stepCSpaceConst C_sp) Tprev Sprev) := by
  set K_C := stepCTimeConst C_stepC C_left
  set S_C := stepCSpaceConst C_sp
  refine meetsContract_of_runs hself fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gAddr, k, xAddr, pAddr, locAddr, outAddr, h, G, X,
    rfl, ha0, ha, hrl, hq1, hqr, hP, hG, hGvalid, hGn, hX, hXrange, hGloop, hdegG, hmG,
    hsize1, hsize2, hloc0, hg_h, hx_h, hp_h, hloc_h, hout_h,
    hd_lg, hd_lx, hd_lp, hd_lo, hd_og, hd_ox, hd_op, hz, hw⟩
  set cp := coreParamsOf cfg M r
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hN1 : 1 ≤ NOf M r := by omega
  have hF1 : 1 ≤ FParam cfg M := one_le_FParam cfg M
  have hB1 : 1 ≤ coreSpaceBase M r := by
    unfold coreSpaceBase; exact Nat.one_le_pow _ _ (by omega)
  have hvs_len : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort]; exact hX.1.symm
  have hvs_nd : (X.sort (· ≤ ·)).Nodup := X.sort_nodup (· ≤ ·)
  have hk_Nq : k ≤ cp.N ^ q := by
    by_cases hq : q = 1
    · subst hq; simpa using (hsize1 rfl).2
    · exact (hsize2 (by omega)).2
  have hk2 : 2 ≤ k := by
    by_cases hq : q = 1
    · exact (hsize1 hq).1
    · have hq2 : 2 ≤ q := by omega
      have hpow4 : 4 ≤ (NOf M r) ^ (q - 1) := by
        calc 4 ≤ NOf M r := hN4
          _ = (NOf M r) ^ 1 := (pow_one _).symm
          _ ≤ (NOf M r) ^ (q - 1) := Nat.pow_le_pow_right hN1 (by omega)
      have h2 := (hsize2 hq2).1
      change (NOf M r) ^ (q - 1) / 2 ≤ k at h2
      omega
  have hsp_big : 65536 ≤ oneShotProgSpace S_B S_C cfg M r q Sprev := by
    unfold oneShotProgSpace
    dsimp only
    have h1 := Nat.one_le_pow q (NOf M r) hN1
    have h2 := Nat.one_le_pow 3 (LParam M) (by omega : 1 ≤ LParam M)
    have h3 := Nat.one_le_pow (2 * q) (FParam cfg M) hF1
    have hprod : 1 ≤ (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have h65 : 65536 ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
      calc 65536 = 65536 * 1 := (Nat.mul_one _).symm
        _ ≤ 65536 * ((NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q)) :=
            Nat.mul_le_mul_left 65536 hprod
        _ = 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by ring
    omega
  have hcost_big : 1000 ≤ 2 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have h1 : 1 ≤ (NOf M r) ^ (q + 1) := Nat.one_le_pow _ _ hN1
    have h2 : 4 ^ 8 ≤ (LParam M) ^ 8 := Nat.pow_le_pow_left hL4 8
    have hprod : 4 ^ 8 ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
      calc 4 ^ 8 = 1 * 4 ^ 8 := (Nat.one_mul _).symm
        _ ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := Nat.mul_le_mul h1 h2
    have h48 : 1000 ≤ 2 * (4 ^ 8) := by decide
    have hr : 2 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) =
        2 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
    omega
  have h2k_le : 2 * k ≤ 2 * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have h1 : 1 ≤ coreSpaceBase M r * (LParam M) ^ 8 :=
      Nat.mul_le_mul hB1 (Nat.one_le_pow _ _ (by omega : 1 ≤ LParam M))
    have h2 : (NOf M r) ^ q ≤ (NOf M r) ^ (q + 1) := Nat.pow_le_pow_right hN1 (by omega)
    have h3 : (NOf M r) ^ q ≤ coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
      calc (NOf M r) ^ q = (NOf M r) ^ q * 1 := (Nat.mul_one _).symm
        _ ≤ (NOf M r) ^ (q + 1) * (coreSpaceBase M r * (LParam M) ^ 8) := Nat.mul_le_mul h2 h1
        _ = coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
    have hk' : k ≤ (NOf M r) ^ q := hk_Nq
    calc 2 * k ≤ 2 * (NOf M r) ^ q := Nat.mul_le_mul_left 2 hk'
      _ ≤ 2 * (coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8) :=
          Nat.mul_le_mul_left 2 h3
      _ = 2 * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
  have hspace_split :
      2 * k + oneShotStepBSpace S_B M r q Sprev +
        S_C * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
        65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤
      oneShotProgSpace S_B S_C cfg M r q Sprev := by
    unfold oneShotStepBSpace oneShotProgSpace
    dsimp only
    have hdist :
        (S_B + S_C + 2) * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 =
        S_B * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
          S_C * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
          2 * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
    omega
  have hcost_split :
      oneShotStepBCost K_B (NOf M r) (LParam M) q Tprev +
        K_C * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
        (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) +
        500 ≤
      oneShotProgCost K_B K_C cfg M r q Tprev := by
    unfold oneShotStepBCost oneShotProgCost
    dsimp only
    have hdist :
        (K_B + K_C + 2) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 =
        K_B * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
          K_C * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
          2 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
    omega
  have h1_lt_w : 1 < 2 ^ w := by omega
  have h2_lt_w : 2 < 2 ^ w := by omega
  have hcorePS : coreParamsSize r = 7 + 3 * r := rfl
  have hDq_pos : 0 < cp.D q := hcfg.hD_pos hq1 hqr
  set z := k / cp.D q
  -- Execute Step A straight-line prefix
  refine runs_start_le ?_
  dsimp only [oneShotProc, seqStmts]
  refine runs_seq_assign_le (v := cp.L)
    (hP.2.1 ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const h1_lt_w) (by omega))) ?_
  refine runs_seq_assign_le (v := cp.Δ)
    (hP.2.2.1 ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const h2_lt_w) (by omega))) ?_
  refine runs_seq_assign_le (v := r)
    (hP.2.2.2.1 ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))) ?_
  refine runs_seq_assign_le (v := cp.P q)
    (hP.2.2.2.2.1 q hqr ▸ Expr.eval_load (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [startState])) (by omega))) ?_
  refine runs_seq_assign_le (v := cp.D q)
    (hP.2.2.2.2.2.1 q hqr ▸ Expr.eval_load (Expr.eval_add
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by simp [startState])) (by omega))
      (Expr.eval_reg_of_eq (by simp [startState])) (by omega))) ?_
  refine runs_seq_assign_le (v := z)
    (Expr.eval_div (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) ?_
  refine runs_seq_assign_le (v := h)
    (Expr.eval_reg_of_eq (by simp [startState])) ?_
  refine runs_seq_assign_le (v := h + 2 * k)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_mul (Expr.eval_const h2_lt_w) (Expr.eval_reg_of_eq (by simp [startState])) (by omega))
      (by omega)) ?_
  -- Branch on `q = 1`
  refine runs_cond_le (v := if q = 1 then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const h1_lt_w) h1_lt_w) ?_ ?_
  · -- Branch `q = 1`: skip Step B (`b = 1, nBlocks = k, callsB = [], mFB = 0`), run Steps C & D
    intro hcond
    have hq_eq : q = 1 := by by_contra hne; simp [hne] at hcond
    have hkN : k ≤ cp.N := (hsize1 hq_eq).2
    refine runs_seq_assign_le (v := 1) (Expr.eval_const h1_lt_w) ?_
    refine runs_seq_assign_le (v := k) (Expr.eval_reg_of_eq (by simp [startState])) ?_
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
    have hnb_eq : k = numFullBlocks (X.sort (· ≤ ·)) 1 := by
      simp [numFullBlocks, hvs_len]
    have hsingle_exp : ∀ i < k,
        (Graph.mk G.n (callsWitnessEdges [])).IsExpansionExpanderOn
          (blockSet (X.sort (· ≤ ·)) 1 i) (1 / (2 * (cp.P (q - 1) : ℝ))) := by
      intro i hi S hS hSne hSneB
      have hcard1 : (blockSet (X.sort (· ≤ ·)) 1 i).card = 1 :=
        card_blockSet hvs_nd (by rwa [← hnb_eq])
      have hScard : S.card ≤ 1 := hcard1 ▸ Finset.card_le_card hS
      have hSpos : 1 ≤ S.card := Finset.Nonempty.card_pos hSne
      have hSeq : S = blockSet (X.sort (· ≤ ·)) 1 i :=
        Finset.eq_of_subset_of_card_le hS (by omega)
      exact absurd hSeq hSneB
    apply oneShotTailCD_conseq hcopy hcloud hcol hstepC hleft hstepD
      (gAddr := gAddr) (k := k) (xAddr := xAddr) (locAddr := locAddr) (outAddr := outAddr)
      (h := h) (hCur := h + 2 * k) (mFB := 0) (b := 1) (numBlk := k) (z := z)
      (hBound := h + oneShotProgSpace S_B S_C cfg M r q Sprev)
      (G := G) (X := X) (callsB := []) (mem₀ := mem)
    · exact ha0
    · exact ha
    · exact hrl
    · exact hq1
    · exact hqr
    · exact hG
    · exact hGvalid
    · exact hGn
    · exact hX
    · exact hXrange
    · exact hGloop
    · exact hdegG
    · exact hmG
    · exact hk2
    · exact hk_Nq
    · omega
    · omega
    · exact hnb_eq
    · omega
    · change k ≤ 2 * cp.N; omega
    · rfl
    · exact hloc0
    · simp
    · simp
    · exact hsingle_exp
    · simp [callsFakeEdges]
    · intro j hj; simp [callsFakeEdges] at hj
    · exact hg_h
    · exact hx_h
    · exact hloc_h
    · exact hout_h
    · exact le_rfl
    · exact hd_lg
    · exact hd_lx
    · exact hd_lo
    · exact hd_og
    · exact hd_ox
    · exact fun a ha => hz a (by omega)
    · exact fun _ _ _ => rfl
    · change h + 2 * k + S_C * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
        65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤
        h + oneShotProgSpace S_B S_C cfg M r q Sprev
      omega
    · exact hw
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp [startState, cp]
    · simp [startState, cp]
    · simp [startState, cp]
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · intro v st_fin hres_cd hh_lo hh_hi hz_fin hloc_fin hfr_fin
        gAddr' k' xAddr' pAddr' locAddr' outAddr' h' G' X' hargs'
        _ _ _ _ _ _ hG' _ _ hX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      simp only [List.cons.injEq, and_true, true_and] at hargs'
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs'
      have hG_eq : G = G' := by
        rw [← readGraph_eq_of_graphAt hG, readGraph_eq_of_graphAt hG']
      rcases hG_eq with rfl
      have hX_eq : X = X' := by
        have h1' := readList_eq_of_listAt hX.2
        have h2' := readList_eq_of_listAt hX'.2
        rw [Finset.length_sort, ← hX.1] at h1'
        rw [Finset.length_sort, ← hX'.1] at h2'
        simpa [Finset.sort_toFinset] using congrArg List.toFinset (h1'.symm.trans h2')
      rcases hX_eq with rfl
      exact ⟨hres_cd, hh_lo, hh_hi, hz_fin, hloc_fin, hfr_fin⟩
    · intro c hc
      simp only [oneShotContract, Expr.size]
      change c ≤ K_C * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
        (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) at hc
      omega
  · -- Branch `q ≥ 2`: compute `b, nBlocks`, run Step B, then on match run Steps C & D
    intro hcond
    have hq2 : 2 ≤ q := by
      by_contra hlt
      have hq1' : q = 1 := by omega
      simp [hq1'] at hcond
    have h2 := hsize2 hq2
    set b := cp.N ^ (q - 1) / 2
    set nBlocks := numFullBlocks (X.sort (· ≤ ·)) b
    have hsp := stepA_block_params hvs_nd hq2 hcfg.hNpos hcfg.hN4
      (by rw [hvs_len]; exact h2.1) (by rw [hvs_len]; exact h2.2)
    have hb_pos : 0 < b := hsp.1
    have hble : b ≤ k := h2.1
    have hnb1 : 1 ≤ nBlocks := hsp.2.2.1
    have hnb2N : nBlocks ≤ 2 * cp.N := hsp.2.2.2.1
    have hnb_div : k / b = nBlocks := by simp [nBlocks, numFullBlocks, hvs_len]
    -- 1. reg 14 := mem[pAddr + 6 + 2 * r + (q - 1)] / 2 = b
    refine runs_seq_assign_le (v := b)
      (Expr.eval_div
        (hP.2.2.2.2.2.2 (q - 1) (by omega) ▸ Expr.eval_load (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const h2_lt_w) (Expr.eval_reg_of_eq (by simp [startState])) (by omega))
            (by omega))
          (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const h1_lt_w) (by omega))
          (by omega)))
        (Expr.eval_const h2_lt_w) (by omega)) ?_
    -- 2. reg 15 := k / b = nBlocks
    refine runs_seq_assign_le (v := nBlocks)
      (hnb_div ▸ Expr.eval_div (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
    -- 3. call `idx.stepB`
    have hB_pre : (oneShotStepBContract cfg M r q w K_B S_B Tprev Sprev).pre
        [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, h, outAddr, h + 2 * k] mem :=
      ⟨gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, h, outAddr, h + 2 * k, G, X,
        rfl, ha, hrl, hq2, hqr, hP, hG, hGvalid, hGn, hX, hXrange, hGloop, hdegG, hmG,
        h2.1, h2.2, rfl, rfl, rfl, hloc0,
        by omega, by omega, by omega, by omega, le_rfl, by omega,
        hd_lg, hd_lx, hd_lp, Or.inl hloc_h, hd_lo, hd_og, hd_ox, hd_op, Or.inl (by omega),
        Or.inr (by omega), Or.inr hx_h, Or.inr hp_h,
        fun a ha => hz a (by omega), by omega⟩
    have hnb_lt : nBlocks < 2 ^ w := by
      have hN_le : cp.N ≤ (NOf M r) ^ q := by
        change NOf M r ≤ (NOf M r) ^ q
        calc NOf M r = (NOf M r) ^ 1 := (pow_one _).symm
          _ ≤ (NOf M r) ^ q := Nat.pow_le_pow_right hN1 hq1
      have h1 : 1 ≤ (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) :=
        Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega : 1 ≤ LParam M)) (Nat.one_le_pow _ _ hF1)
      have h2' : 2 * (NOf M r) ^ q ≤
          65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
        calc 2 * (NOf M r) ^ q = (2 * (NOf M r) ^ q) * 1 := (Nat.mul_one _).symm
          _ ≤ (65536 * (NOf M r) ^ q) * ((LParam M) ^ 3 * (FParam cfg M) ^ (2 * q)) :=
              Nat.mul_le_mul (by omega) h1
          _ = 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by ring
      unfold oneShotProgSpace at hw; dsimp only at hw; omega
    have hB_words : ∀ v ∈ [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, h, outAddr,
        h + 2 * k], v < 2 ^ w := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact hnb_lt
      · have : z ≤ k := Nat.div_le_self _ _; omega
      · omega
      · omega
      · omega
      · omega
      · omega
    refine runs_seq_call_le
      (vs := [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, h, outAddr, h + 2 * k])
      (hstepB hq2)
      (by simp [evalArgs, Expr.eval, startState])
      hB_words hB_pre ?_
    intro hB memB posB hB_post
    have hB_res := hB_post gAddr k xAddr b nBlocks z pAddr locAddr h outAddr (h + 2 * k) G X
      rfl ha hrl hq2 hqr hP hG hGvalid hGn hX hXrange hGloop hdegG hmG h2.1 h2.2 rfl rfl rfl hloc0
      (by omega) (by omega) (by omega) (by omega) le_rfl (by omega)
      hd_lg hd_lx hd_lp (Or.inl hloc_h) hd_lo hd_og hd_ox hd_op (Or.inl (by omega))
      (Or.inr (by omega)) (Or.inr hx_h) (Or.inr hp_h) (fun a ha => hz a (by omega)) (by omega)
    obtain ⟨hB_out, hhB_lo, hhB_hi, hzB, hlocB, hframeB⟩ := hB_res
    -- 4. reg 19 := load outAddr
    set tagB := memB outAddr
    refine runs_seq_assign_le (v := tagB)
      (Expr.eval_load (Expr.eval_reg_of_eq (by simp [startState]))) ?_
    -- 5. cond (tagB = 0)
    refine runs_cond_le (v := if tagB = 0 then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) h1_lt_w) ?_ ?_
    · -- Step B returned a cut (`tagB = 0`)
      intro hcondB
      have htagB0 : tagB = 0 := by by_contra hne; simp [hne] at hcondB
      have hcutB : ∃ U : Finset ℕ, CoreOutAt memB outAddr (.cut U) ∧ RouteCutSpec G X 100 z U := by
        rcases hB_out with ⟨_, hU⟩ | ⟨h1, _⟩
        · exact hU
        · exact absurd (htagB0.symm.trans h1) (by decide)
      obtain ⟨U, hUout, hUcut⟩ := hcutB
      refine ⟨.returned hB, _, 2,
        runs_ret_iff.mpr ⟨hB, Expr.eval_reg_of_eq (by simp), rfl, rfl, by simp [Expr.size]⟩,
        ?_, ?_⟩
      · simp only [Outcome.value]
        intro gAddr' k' xAddr' pAddr' locAddr' outAddr' h' G' X' hargs'
          _ _ _ _ _ _ hG' _ _ hX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        simp only [List.cons.injEq, and_true, true_and] at hargs'
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs'
        have hG_eq : G = G' := by
          rw [← readGraph_eq_of_graphAt hG, readGraph_eq_of_graphAt hG']
        rcases hG_eq with rfl
        have hX_eq : X = X' := by
          have h1' := readList_eq_of_listAt hX.2
          have h2' := readList_eq_of_listAt hX'.2
          rw [Finset.length_sort, ← hX.1] at h1'
          rw [Finset.length_sort, ← hX'.1] at h2'
          simpa [Finset.sort_toFinset] using congrArg List.toFinset (h1'.symm.trans h2')
        rcases hX_eq with rfl
        refine ⟨⟨.cut U, hUout, by simpa [OneShotSpec, z, hX.1] using hUcut⟩,
          by omega, by omega, hzB, hlocB, ?_⟩
        intro a ha hout_a
        exact hframeB a (by omega) (Or.inl ha) hout_a
      · have hargB : argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 14, .reg 15, .reg 13,
            .reg 4, .reg 5, .reg 16, .reg 6, .reg 17] = 12 := by decide
        simp only [oneShotContract, oneShotStepBContract, Expr.size, hargB]
        change _ ≤ oneShotProgCost K_B K_C cfg M r q Tprev
        omega
    · -- Step B succeeded (`tagB = 1`): load `mFB`, run Steps C & D
      intro hcondB
      have htagB1 : tagB = 1 := by
        rcases hB_out with ⟨h0, _⟩ | ⟨h1, _⟩
        · simp [tagB, h0] at hcondB
        · exact h1
      have hmatchedB : ∃ callsB : List RoutedCall,
          callsB.length ≤ 49 * cp.L + 2 ∧
          (∀ c ∈ callsB, c.Valid G X (routeCong cp.Δ 100 cp.L) z) ∧
          (∀ i < nBlocks, (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
            (blockSet (X.sort (· ≤ ·)) b i) (1 / (2 * (cp.P (q - 1) : ℝ)))) ∧
          memB (outAddr + 1) = (callsFakeEdges callsB).length ∧
          EdgesAt memB h (callsFakeEdges callsB) := by
        rcases hB_out with ⟨h0, _⟩ | ⟨_, hM⟩
        · exact absurd (htagB1.symm.trans h0) (by decide)
        · exact hM
      obtain ⟨callsB, hcallsB_len, hcallsB_val, hcallsB_exp, hmFB_eq, hfB_at⟩ := hmatchedB
      set mFB := (callsFakeEdges callsB).length
      refine runs_seq_assign_le (v := mFB)
        (hmFB_eq ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_const h1_lt_w) (by omega))) ?_
      have hmemB_G : GraphAt memB gAddr G :=
        hG.congr fun a ha1 ha2 => by
          have hlenG : G.encode.length = 2 + 2 * G.m := graph_encode_length G
          have ho := disjointRange_outside hd_og ha1 (by omega)
          exact hframeB a (by omega) (Or.inl (by omega)) (by omega)
      have hmemB_X : VertsAt memB xAddr k X := by
        refine ⟨hX.1, fun i hi => ?_⟩
        have ho := disjointRange_outside hd_ox (x := xAddr + i) (by omega) (by omega)
        rw [hframeB (xAddr + i) (by omega) (Or.inl (by omega)) (by omega)]
        exact hX.2 i hi
      apply oneShotTailCD_conseq hcopy hcloud hcol hstepC hleft hstepD
        (gAddr := gAddr) (k := k) (xAddr := xAddr) (locAddr := locAddr) (outAddr := outAddr)
        (h := h) (hCur := hB) (mFB := mFB) (b := b) (numBlk := nBlocks) (z := z)
        (hBound := h + oneShotProgSpace S_B S_C cfg M r q Sprev)
        (G := G) (X := X) (callsB := callsB) (mem₀ := mem)
      · exact ha0
      · exact ha
      · exact hrl
      · exact hq1
      · exact hqr
      · exact hmemB_G
      · exact hGvalid
      · exact hGn
      · exact hmemB_X
      · exact hXrange
      · exact hGloop
      · exact hdegG
      · exact hmG
      · exact hk2
      · exact hk_Nq
      · exact hb_pos
      · exact hble
      · rfl
      · exact hnb1
      · exact hnb2N
      · rfl
      · exact hlocB
      · exact hcallsB_len
      · exact hcallsB_val
      · exact hcallsB_exp
      · rfl
      · exact hfB_at
      · exact hg_h
      · exact hx_h
      · exact hloc_h
      · exact hout_h
      · exact hhB_lo
      · exact hd_lg
      · exact hd_lx
      · exact hd_lo
      · exact hd_og
      · exact hd_ox
      · exact hzB
      · exact fun a ha hout_a => hframeB a (by omega) (Or.inl ha) hout_a
      · change hB + S_C * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
          65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤
          h + oneShotProgSpace S_B S_C cfg M r q Sprev
        omega
      · exact hw
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState, cp]
      · simp [startState, cp]
      · simp [startState, cp]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · intro v st_fin hres_cd hh_lo hh_hi hz_fin hloc_fin hfr_fin
          gAddr' k' xAddr' pAddr' locAddr' outAddr' h' G' X' hargs'
          _ _ _ _ _ _ hG' _ _ hX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        simp only [List.cons.injEq, and_true, true_and] at hargs'
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs'
        have hG_eq : G = G' := by
          rw [← readGraph_eq_of_graphAt hG, readGraph_eq_of_graphAt hG']
        rcases hG_eq with rfl
        have hX_eq : X = X' := by
          have h1' := readList_eq_of_listAt hX.2
          have h2' := readList_eq_of_listAt hX'.2
          rw [Finset.length_sort, ← hX.1] at h1'
          rw [Finset.length_sort, ← hX'.1] at h2'
          simpa [Finset.sort_toFinset] using congrArg List.toFinset (h1'.symm.trans h2')
        rcases hX_eq with rfl
        exact ⟨hres_cd, hh_lo, hh_hi, hz_fin, hloc_fin, hfr_fin⟩
      · intro c hc
        have hargB : argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 14, .reg 15, .reg 13,
            .reg 4, .reg 5, .reg 16, .reg 6, .reg 17] = 12 := by decide
        simp only [oneShotContract, oneShotStepBContract, Expr.size, hargB]
        change _ ≤ oneShotProgCost K_B K_C cfg M r q Tprev
        change c ≤ K_C * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
          (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) at hc
        omega

end MinCostFlow.ExpanderDecomp
