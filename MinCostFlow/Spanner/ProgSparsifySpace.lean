module

public import MinCostFlow.Spanner.ProgSparsifySpaceBase

@[expose] public section

/-!
# Polynomial Space and Logarithmic Word-Width Theorem for Word-RAM `Sparsify`

Combines `SparsifyPolyPack` with the non-heap intermediate word bounds and the 6 subcall
logarithmic word-width bounds to prove `sparsify_poly_space_and_wordWidth`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- Given `impl : SpannerToolImpl` and `invB : impl.decompose.InvPhiBound`, produces constants
`C_sp, c_sp, cw : ℕ` (`6 ≤ C_sp`, `2 ≤ cw`) such that:
- `heap + C_sp * (s + 2) ^ c_sp < (heap + mVal + 2) ^ cw` for `3 ≤ heap` and `s ≤ 3 * (heap + mVal)`,
- `sparsifyMaxHeapEnd impl inp ≤ inp.h + C_sp * (sparsifyInputSize inp + 2) ^ c_sp`,
- `cw * (Nat.log 2 (inp.h + mVal + 2) + 1) ≤ w` implies `inp.WordWidthOK impl w ∧ SparsifyWordOK impl inp w`
  even under the quadratic bound `s ≤ 2 * (inp.h + mVal + 2) ^ 2` (which holds from `EmbBounded`
  without assuming walk disjointness). -/
theorem sparsify_poly_space_and_wordWidth (impl : SpannerToolImpl)
    (invB : impl.decompose.InvPhiBound) :
    ∃ (C_sp c_sp cw : ℕ),
      6 ≤ C_sp ∧ 2 ≤ cw ∧
      (∀ heap mVal s, 3 ≤ heap → s ≤ 3 * (heap + mVal) →
        heap + C_sp * (s + 2) ^ c_sp < (heap + mVal + 2) ^ cw) ∧
      (∀ (inp : Task1Input) (w : ℕ),
        let s := sparsifyInputSize inp
        inp.H'.IsValid → inp.J.IsValid → IsEmbedding inp.J inp.H' inp.embJH →
        sparsifyMaxHeapEnd impl inp ≤ inp.h + C_sp * (s + 2) ^ c_sp ∧
        (∀ mVal, 3 ≤ inp.h → s ≤ 2 * (inp.h + mVal + 2) ^ 2 →
          (∀ x ∈ inp.J.encode, x ≤ mVal) →
          16 ≤ 2 ^ w →
          cw * (Nat.log 2 (inp.h + mVal + 2) + 1) ≤ w →
          inp.WordWidthOK impl w ∧ SparsifyWordOK impl inp w)) := by
  obtain ⟨P⟩ := SparsifyPolyPack.exists_of_invPhi impl invB
  set dec := impl.decompose
  set ce := impl.constructExpander
  set pds := impl.pathDS.params
  set dW := WitnessCoreInput.dWInt ce
  set C_w1 := 8 * P.C_pd + 4 * ce.c_deg_int * P.C_pd + 2 * ce.phiDen + 4 + 16 * P.C_tau2 + 4
  set k_w1 := max (P.k_pd + 1) (P.k_tau2 + 2)
  set C_w2 := 16 * P.C_η1 * P.C_tau2 * P.C_pd + 4 * P.C_mw * P.C_pd + 4 +
    2 * P.C_mw * P.C_pds + 6 + P.C_η1 + 2 * P.C_mw + 4
  set k_w2 := max (max (P.k_mw + P.k_tau2 + P.k_pd + 2) (P.k_mw + P.k_pd + 1))
    (P.k_mw + P.k_pds + 1)
  set C_w3 := 18 * P.C_tau2 * P.C_pd + 4 + P.C_pd + 4 + 3 * P.C_mw + 8
  set k_w3 := max (P.k_tau2 + P.k_pd + 2) (max (P.k_pd + 1) P.k_mw)
  set C_sp := P.C_sp + 6
  set C_all_s := C_sp + 4 + C_w1 + C_w2 + C_w3
  set k_all := max P.c_sp (max k_w1 (max k_w2 k_w3))
  set C_log := max (P.C_pd + 3) (max (P.C_argJ + 2 * P.C_pds) (max (P.C_argW + 2 * P.C_pds)
    (max P.C_ceArg (max P.C_dsJArg P.C_dsWArg))))
  set k_log := max P.k_pd (max (max P.k_mw P.k_pds)
    (max P.k_ceArg (max P.k_dsJArg P.k_dsWArg)))
  set C_allH := C_all_s * 3 ^ k_all + 2
  set C_logH := C_log * 3 ^ k_log
  set cw_sub := max dec.cw (max pds.cw ce.cw)
  set cw := max 2 (max (Nat.log 2 C_allH + 1 + 2 * k_all)
    (cw_sub * (Nat.log 2 C_logH + 1 + 2 * k_log)))
  have hk_all_pos : 1 ≤ k_all := le_trans P.hc_sp (le_max_left _ _)
  refine ⟨C_sp, P.c_sp, cw, by omega, le_max_left _ _, ?_, ?_⟩
  · intro heap mVal s hheap hs
    set H := heap + mVal + 2
    have hH2 : 2 ≤ H := by omega
    have hx_le : s + 2 ≤ 3 * H := by omega
    have h1 : heap + C_sp * (s + 2) ^ P.c_sp ≤ C_allH * H ^ k_all := by
      have hp1 : (s + 2) ^ P.c_sp ≤ (3 * H) ^ k_all :=
        le_trans (Nat.pow_le_pow_left hx_le P.c_sp)
          (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
      rw [mul_pow] at hp1
      have hp2 : C_sp * (s + 2) ^ P.c_sp ≤ (C_all_s * 3 ^ k_all) * H ^ k_all := by
        calc C_sp * (s + 2) ^ P.c_sp ≤ C_all_s * (3 ^ k_all * H ^ k_all) :=
              Nat.mul_le_mul (by omega) hp1
          _ = (C_all_s * 3 ^ k_all) * H ^ k_all := by ring
      have hp3 : heap ≤ H ^ k_all := le_trans (by omega) (Nat.le_self_pow (by omega) H)
      calc heap + C_sp * (s + 2) ^ P.c_sp
          ≤ H ^ k_all + (C_all_s * 3 ^ k_all) * H ^ k_all := Nat.add_le_add hp3 hp2
        _ ≤ C_allH * H ^ k_all := by
            have : C_allH * H ^ k_all = (C_all_s * 3 ^ k_all) * H ^ k_all + 2 * H ^ k_all := by
              dsimp only [C_allH]; ring
            omega
    have hcw_k : Nat.log 2 C_allH + 1 + k_all ≤ cw :=
      le_trans (by omega) (le_trans (le_max_left _ _) (le_max_right _ _))
    exact lt_of_le_of_lt h1 (spNat_lt_pow_of_poly hH2 hcw_k)
  · intro inp w s _ hJv hEmb
    set x := s + 2
    have hx1 : 1 ≤ x := by omega
    set m0 := (stripLoops inp.J).m
    have hm0_le_m : m0 ≤ inp.J.m := stripLoops_m_le inp.J
    have hJn_x : inp.J.n ≤ x := by dsimp only [x, s, sparsifyInputSize]; omega
    have hJm_x : inp.J.m ≤ x := by dsimp only [x, s, sparsifyInputSize]; omega
    have hm0_x : m0 ≤ x := le_trans hm0_le_m hJm_x
    have hevs_x : (inp.toT2 0).embVertSum ≤ x := by dsimp only [x, s, sparsifyInputSize]; omega
    have hlen_x : length inp.J inp.embJH ≤ x := le_trans (spLength_le_embVertSum hEmb) hevs_x
    have hvc_x : vcongNat inp.J inp.H' inp.embJH ≤ x := le_trans (spVcongNat_le_m _ _ _) hJm_x
    have hdeg_x : maxDeg inp.J ≤ 2 * x := le_trans (spMaxDeg_le_two_m hJv) (by omega)
    have h1_pow : ∀ r, 1 ≤ x ^ r := fun r => Nat.one_le_pow r x hx1
    have hP := P.hbounds inp
    have hpd_le : Task1Input.phiDenCap impl inp.J ≤ P.C_pd * x ^ P.k_pd := hP.1
    have hmw_le : Task1Input.mwCap impl inp.J ≤ P.C_mw * x ^ P.k_mw := hP.2.1
    have hargJ_le : Task1Input.dJCap impl inp.J + m0 + 2 ≤ P.C_argJ * x ^ P.k_mw := hP.2.2.1
    have hargW_le : dW + Task1Input.mwCap impl inp.J + 2 ≤ P.C_argW * x ^ P.k_mw := hP.2.2.2.1
    have hgEJ_le : pds.gExp (Task1Input.dJCap impl inp.J) m0 ≤ P.C_pds * x ^ P.k_pds := hP.2.2.2.2.1
    have hgEW_le : pds.gExp dW (Task1Input.mwCap impl inp.J) ≤ P.C_pds * x ^ P.k_pds := hP.2.2.2.2.2.1
    have hgDJ_le : pds.gDel (Task1Input.dJCap impl inp.J) m0 ≤ P.C_pds * x ^ P.k_pds := hP.2.2.2.2.2.2.1
    have hgDW_le : pds.gDel dW (Task1Input.mwCap impl inp.J) ≤ P.C_pds * x ^ P.k_pds := hP.2.2.2.2.2.2.2.1
    have hγE_le : Task2Input.gammaExpCap impl inp.J ≤ P.C_pds * x ^ P.k_pds := hP.2.2.2.2.2.2.2.2.1
    have htau2_le : Task1Input.tau2Cap impl inp.J ≤ P.C_tau2 * x ^ P.k_tau2 := hP.2.2.2.2.2.2.2.2.2.1
    have hη1_le : Task2Input.eta1Cap impl inp.J ≤ P.C_η1 * x ^ P.k_mw := hP.2.2.2.2.2.2.2.2.2.2.1
    have hceArg_le : inp.J.n + 4 * m0 * Task1Input.phiDenCap impl inp.J + 2 ≤ P.C_ceArg * x ^ P.k_ceArg :=
      hP.2.2.2.2.2.2.2.2.2.2.2.1
    have hdsJArg_le : Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
        pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2 ≤ P.C_dsJArg * x ^ P.k_dsJArg :=
      hP.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hdsWArg_le : ce.phiDen + 4 * Task1Input.mwCap impl inp.J +
        pds.gExp dW (Task1Input.mwCap impl inp.J) + 2 ≤ P.C_dsWArg * x ^ P.k_dsWArg :=
      hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have ht1_sp : inp.maxHeapEnd impl ≤ inp.h + P.C_sp * x ^ P.c_sp :=
      hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hsp_heap : sparsifyMaxHeapEnd impl inp ≤ inp.h + P.C_sp * x ^ P.c_sp :=
      hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    clear hP
    refine ⟨le_trans hsp_heap (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : P.C_sp ≤ C_sp)) _), ?_⟩
    intro mVal hh3 hs_le hJenc hw16 hcw_w
    set H := inp.h + mVal + 2
    have hH2 : 2 ≤ H := by omega
    have hx_3H2 : x ≤ 3 * H ^ 2 := by
      have hHsq : 2 ≤ H ^ 2 := by nlinarith only [hH2]
      dsimp only [x]; omega
    have hcw_all : Nat.log 2 C_allH + 1 + 2 * k_all ≤ cw :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hcw_log : cw_sub * (Nat.log 2 C_logH + 1 + 2 * k_log) ≤ cw :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hlt_w_of_s : ∀ Y, Y ≤ inp.h + C_all_s * x ^ k_all → Y < 2 ^ w := fun Y hY => by
      have hp1 : x ^ k_all ≤ 3 ^ k_all * H ^ (2 * k_all) := by
        calc x ^ k_all ≤ (3 * H ^ 2) ^ k_all := Nat.pow_le_pow_left hx_3H2 k_all
          _ = 3 ^ k_all * (H ^ 2) ^ k_all := mul_pow 3 (H ^ 2) k_all
          _ = 3 ^ k_all * H ^ (2 * k_all) := by rw [← pow_mul]
      have hp2 : inp.h ≤ H ^ (2 * k_all) := le_trans (by omega) (Nat.le_self_pow (by omega) H)
      have hp3 : Y ≤ C_allH * H ^ (2 * k_all) := by
        have h1 : C_all_s * x ^ k_all ≤ (C_all_s * 3 ^ k_all) * H ^ (2 * k_all) := by
          calc _ ≤ C_all_s * (3 ^ k_all * H ^ (2 * k_all)) := Nat.mul_le_mul_left _ hp1
            _ = _ := by ring
        have h2 : C_allH * H ^ (2 * k_all) = (C_all_s * 3 ^ k_all) * H ^ (2 * k_all) + 2 * H ^ (2 * k_all) := by
          dsimp only [C_allH]; ring
        omega
      exact spNat_lt_two_pow_of_poly hH2 hp3 hcw_all hcw_w
    have hlog_w_of_s : ∀ cSub Y, cSub ≤ cw_sub → Y ≤ C_log * x ^ k_log →
        cSub * (Nat.log 2 Y + 1) ≤ w := fun cSub Y hcSub hY => by
      have hp1 : x ^ k_log ≤ 3 ^ k_log * H ^ (2 * k_log) := by
        calc x ^ k_log ≤ (3 * H ^ 2) ^ k_log := Nat.pow_le_pow_left hx_3H2 k_log
          _ = 3 ^ k_log * (H ^ 2) ^ k_log := mul_pow 3 (H ^ 2) k_log
          _ = 3 ^ k_log * H ^ (2 * k_log) := by rw [← pow_mul]
      have hp2 : Y ≤ C_logH * H ^ (2 * k_log) := by
        calc Y ≤ C_log * (3 ^ k_log * H ^ (2 * k_log)) := le_trans hY (Nat.mul_le_mul_left _ hp1)
          _ = C_logH * H ^ (2 * k_log) := by dsimp only [C_logH]; ring
      have h1 := spLog2_poly_le hp2
      have h2 : cSub * (Nat.log 2 Y + 1) ≤ cw_sub * ((Nat.log 2 C_logH + 1 + 2 * k_log) * (Nat.log 2 H + 1)) :=
        Nat.mul_le_mul hcSub h1
      rw [← Nat.mul_assoc] at h2
      exact le_trans h2 (le_trans (Nat.mul_le_mul_right _ hcw_log) hcw_w)
    have hH_lt_2w : H < 2 ^ w := by
      have h1 : H ≤ 2 * H ^ (2 * k_all) := by
        have := Nat.le_self_pow (by omega : 2 * k_all ≠ 0) H; omega
      have h2 : H ≤ C_allH * H ^ (2 * k_all) := le_trans h1 (Nat.mul_le_mul_right _ (by omega : 2 ≤ C_allH))
      exact spNat_lt_two_pow_of_poly hH2 h2 hcw_all hcw_w
    -- Task 1 `maxWordBound`:
    have hw1_le : Task1Input.maxWordBound impl inp ≤ inp.h + C_all_s * x ^ k_all := by
      unfold Task1Input.maxWordBound; dsimp only
      refine max_le (le_trans ht1_sp (Nat.add_le_add_left
        (spPoly_le hx1 le_rfl (by omega) (le_max_left _ _)) _)) (max_le ?_ ?_)
      · have h1 : (m0 + 1) * Task1Input.phiDenCap impl inp.J ≤ 2 * P.C_pd * x ^ (P.k_pd + 1) := by
          simpa [show 1 + P.k_pd = P.k_pd + 1 by omega] using
            spPoly_mul (show m0 + 1 ≤ 2 * x ^ 1 by simp only [pow_one]; omega) hpd_le
        have ha : (m0 + 1) * Task1Input.phiDenCap impl inp.J ≤ (2 * P.C_pd) * x ^ k_w1 :=
          spPoly_le hx1 h1 le_rfl (le_max_left _ _)
        have hb := h1_pow k_w1
        have hc : 4 * (m0 + 1) * Task1Input.phiDenCap impl inp.J =
            4 * ((m0 + 1) * Task1Input.phiDenCap impl inp.J) := by ring
        have hd : 2 * ce.c_deg_int * (m0 + 1) * Task1Input.phiDenCap impl inp.J =
            (2 * ce.c_deg_int) * ((m0 + 1) * Task1Input.phiDenCap impl inp.J) := by ring
        have h2 : 4 * (m0 + 1) * Task1Input.phiDenCap impl inp.J +
            2 * ce.c_deg_int * (m0 + 1) * Task1Input.phiDenCap impl inp.J + 2 * ce.phiDen + 2 ≤
            C_w1 * x ^ k_w1 := by
          have ha2 := Nat.mul_le_mul_left (2 * ce.c_deg_int) ha
          rw [hc, hd]
          calc _ ≤ (8 * P.C_pd + 4 * ce.c_deg_int * P.C_pd + 2 * ce.phiDen + 4) * x ^ k_w1 := by
                nlinarith only [ha, ha2, hb]
            _ ≤ C_w1 * x ^ k_w1 := Nat.mul_le_mul_right _ (by dsimp only [C_w1]; omega)
        exact le_trans (spPoly_le hx1 h2 (by omega) (le_trans (le_max_left _ _) (le_max_right _ _)))
          (Nat.le_add_left _ _)
      · have h1 : (length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1) ≤
            8 * x ^ 2 := by
          have := Nat.mul_le_mul (show length inp.J inp.embJH + 1 ≤ 2 * x by omega)
            (show vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1 ≤ 4 * x by omega)
          linarith only [this]
        have h2 : Task1Input.tau2Cap impl inp.J *
            ((length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) ≤
            (8 * P.C_tau2) * x ^ (P.k_tau2 + 2) := by
          simpa [mul_comm P.C_tau2 8] using spPoly_mul htau2_le h1
        have ha : Task1Input.tau2Cap impl inp.J *
            ((length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) ≤
            (8 * P.C_tau2) * x ^ k_w1 :=
          spPoly_le hx1 h2 le_rfl (le_max_right _ _)
        have hb := h1_pow k_w1
        have hc : 2 * Task1Input.tau2Cap impl inp.J * (length inp.J inp.embJH + 1) *
            (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1) =
            2 * (Task1Input.tau2Cap impl inp.J *
              ((length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1))) := by ring
        have h3 : 2 * Task1Input.tau2Cap impl inp.J * (length inp.J inp.embJH + 1) *
            (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1) + 2 ≤ C_w1 * x ^ k_w1 := by
          rw [hc]
          calc _ ≤ (16 * P.C_tau2 + 4) * x ^ k_w1 := by nlinarith only [ha, hb]
            _ ≤ C_w1 * x ^ k_w1 := Nat.mul_le_mul_right _ (by dsimp only [C_w1]; omega)
        exact le_trans (spPoly_le hx1 h3 (by omega) (le_trans (le_max_left _ _) (le_max_right _ _)))
          (Nat.le_add_left _ _)
    -- Task 2 `maxWordBound + Task1.maxHeapEnd`:
    have hw2_le : Task2Input.maxWordBound impl (inp.toT2 0) + inp.maxHeapEnd impl ≤
        inp.h + C_all_s * x ^ k_all := by
      have hheap_12 : Task2Input.maxHeapEnd impl (inp.toT2 0) + 3 + inp.maxHeapEnd impl ≤
          inp.h + C_all_s * x ^ k_all := by
        have h1 : Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl ≤
            sparsifyMaxHeapEnd impl inp := by unfold sparsifyMaxHeapEnd; omega
        have h2 := le_trans h1 hsp_heap
        have h3 : 3 ≤ 4 * x ^ P.c_sp := by have := h1_pow P.c_sp; omega
        have h4 : (P.C_sp + 4) * x ^ P.c_sp ≤ C_all_s * x ^ k_all :=
          spPoly_le hx1 le_rfl (by omega) (le_max_left _ _)
        nlinarith only [h2, h3, h4]
      unfold Task2Input.maxWordBound; simp only [Task1Input.toT2]
      have hmax_add : ∀ a b c : ℕ, max a b + c = max (a + c) (b + c) := fun a b c => by omega
      rw [hmax_add]
      refine max_le hheap_12 ?_
      have hnonheap : max (Task2Input.eta1Cap impl inp.J *
            (2 * Task2Input.gammaExpCap impl inp.J *
              max (pds.gDel (Task1Input.dJCap impl inp.J) m0) (pds.gDel dW (Task1Input.mwCap impl inp.J)) *
              max (pds.phiOutDen (Task1Input.dJCap impl inp.J) m0) (pds.phiOutDen dW (Task1Input.mwCap impl inp.J)) *
              (length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) *
            Task1Input.phiDenCap impl inp.J +
            2 * Task1Input.mwCap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J + 2)
          (max (Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J *
              (length inp.J inp.embJH + 1) + (inp.toT2 0).embVertSum + 4)
            (Task2Input.eta1Cap impl inp.J * inp.J.m + 2 * Task1Input.mwCap impl inp.J + 2)) ≤
          C_w2 * x ^ k_w2 := by
        refine max_le ?_ (max_le ?_ ?_)
        · have hlv : (length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1) ≤
              8 * x ^ 2 := by
            have := Nat.mul_le_mul (show length inp.J inp.embJH + 1 ≤ 2 * x by omega)
              (show vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1 ≤ 4 * x by omega)
            linarith only [this]
          have ha : Task2Input.eta1Cap impl inp.J *
              (Task2Input.gammaExpCap impl inp.J *
                max (pds.gDel (Task1Input.dJCap impl inp.J) m0) (pds.gDel dW (Task1Input.mwCap impl inp.J)) *
                max (pds.phiOutDen (Task1Input.dJCap impl inp.J) m0) (pds.phiOutDen dW (Task1Input.mwCap impl inp.J))) *
              ((length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) *
              Task1Input.phiDenCap impl inp.J ≤ (8 * P.C_η1 * P.C_tau2 * P.C_pd) * x ^ k_w2 := by
            have hτ : Task2Input.gammaExpCap impl inp.J *
                max (pds.gDel (Task1Input.dJCap impl inp.J) m0) (pds.gDel dW (Task1Input.mwCap impl inp.J)) *
                max (pds.phiOutDen (Task1Input.dJCap impl inp.J) m0) (pds.phiOutDen dW (Task1Input.mwCap impl inp.J)) =
                Task1Input.tau2Cap impl inp.J := by
              unfold Task1Input.tau2Cap Task1Input.gammaExpCap Task1Input.gammaDelCap
                Task1Input.phiDsDenCap Task2Input.gammaExpCap
              rfl
            rw [hτ]
            have p3 := spPoly_mul (spPoly_mul (spPoly_mul hη1_le htau2_le) hlv) hpd_le
            exact spPoly_le hx1 p3 (le_of_eq (by ring)) (by dsimp only [k_w2]; omega)
          have hb : Task1Input.mwCap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J ≤
              (2 * P.C_mw * P.C_pd) * x ^ k_w2 := by
            have p2 := spPoly_mul (spPoly_mul hmw_le (show maxDeg inp.J ≤ 2 * x ^ 1 by simp only [pow_one]; omega)) hpd_le
            exact spPoly_le hx1 p2 (le_of_eq (by ring)) (by dsimp only [k_w2]; omega)
          have hrew : Task2Input.eta1Cap impl inp.J *
              (2 * Task2Input.gammaExpCap impl inp.J *
                max (pds.gDel (Task1Input.dJCap impl inp.J) m0) (pds.gDel dW (Task1Input.mwCap impl inp.J)) *
                max (pds.phiOutDen (Task1Input.dJCap impl inp.J) m0) (pds.phiOutDen dW (Task1Input.mwCap impl inp.J)) *
                (length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) *
              Task1Input.phiDenCap impl inp.J =
              2 * (Task2Input.eta1Cap impl inp.J *
                (Task2Input.gammaExpCap impl inp.J *
                  max (pds.gDel (Task1Input.dJCap impl inp.J) m0) (pds.gDel dW (Task1Input.mwCap impl inp.J)) *
                  max (pds.phiOutDen (Task1Input.dJCap impl inp.J) m0) (pds.phiOutDen dW (Task1Input.mwCap impl inp.J))) *
                ((length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) *
                Task1Input.phiDenCap impl inp.J) := by ring
          have hrew2 : 2 * Task1Input.mwCap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J =
              2 * (Task1Input.mwCap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J) := by ring
          have hc := h1_pow k_w2
          rw [hrew, hrew2]
          calc _ ≤ (16 * P.C_η1 * P.C_tau2 * P.C_pd + 4 * P.C_mw * P.C_pd + 4) * x ^ k_w2 := by
                nlinarith only [ha, hb, hc]
            _ ≤ C_w2 * x ^ k_w2 := Nat.mul_le_mul_right _ (by dsimp only [C_w2]; omega)
        · have ha := spPoly_mul (spPoly_mul hmw_le hγE_le) (show length inp.J inp.embJH + 1 ≤ 2 * x ^ 1 by simp only [pow_one]; omega)
          have hb : Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J * (length inp.J inp.embJH + 1) ≤
              (2 * P.C_mw * P.C_pds) * x ^ k_w2 :=
            spPoly_le hx1 ha (le_of_eq (by ring)) (by dsimp only [k_w2]; omega)
          have hc : (inp.toT2 0).embVertSum + 4 ≤ 6 * x ^ k_w2 := by
            have : x ≤ x ^ k_w2 := Nat.le_self_pow (by omega) x; omega
          calc _ ≤ (2 * P.C_mw * P.C_pds + 6) * x ^ k_w2 := by nlinarith only [hb, hc]
            _ ≤ C_w2 * x ^ k_w2 := Nat.mul_le_mul_right _ (by dsimp only [C_w2]; omega)
        · have ha : Task2Input.eta1Cap impl inp.J * inp.J.m ≤ P.C_η1 * x ^ k_w2 :=
            spPoly_le hx1 (spPoly_mul hη1_le (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega))
              (by omega) (by dsimp only [k_w2]; omega)
          have hb : Task1Input.mwCap impl inp.J ≤ P.C_mw * x ^ k_w2 :=
            spPoly_le hx1 hmw_le le_rfl (by dsimp only [k_w2]; omega)
          have hc := h1_pow k_w2
          calc _ ≤ (P.C_η1 + 2 * P.C_mw + 4) * x ^ k_w2 := by nlinarith only [ha, hb, hc]
            _ ≤ C_w2 * x ^ k_w2 := Nat.mul_le_mul_right _ (by dsimp only [C_w2]; omega)
      have ht1_all : inp.maxHeapEnd impl ≤ inp.h + P.C_sp * x ^ k_all :=
        le_trans ht1_sp (Nat.add_le_add_left (spPoly_le hx1 le_rfl le_rfl (le_max_left _ _)) _)
      have hw2_all : C_w2 * x ^ k_w2 ≤ C_w2 * x ^ k_all :=
        spPoly_le hx1 le_rfl le_rfl (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      have hsum : P.C_sp * x ^ k_all + C_w2 * x ^ k_all ≤ C_all_s * x ^ k_all := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      change max (Task2Input.eta1Cap impl inp.J *
            (2 * Task2Input.gammaExpCap impl inp.J *
              max (pds.gDel (Task1Input.dJCap impl inp.J) m0) (pds.gDel dW (Task1Input.mwCap impl inp.J)) *
              max (pds.phiOutDen (Task1Input.dJCap impl inp.J) m0) (pds.phiOutDen dW (Task1Input.mwCap impl inp.J)) *
              (length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) *
            Task1Input.phiDenCap impl inp.J +
            2 * Task1Input.mwCap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J + 2)
          (max (Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J *
              (length inp.J inp.embJH + 1) + (inp.toT2 0).embVertSum + 4)
            (Task2Input.eta1Cap impl inp.J * inp.J.m + 2 * Task1Input.mwCap impl inp.J + 2)) +
        inp.maxHeapEnd impl ≤ inp.h + C_all_s * x ^ k_all
      linarith only [hnonheap, ht1_all, hw2_all, hsum]
    -- Task 3 `maxWordBound + Task2.maxHeapEnd + Task1.maxHeapEnd`:
    have hw3_le : Task3Input.maxWordBound impl (inp.toT3 0) +
        Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl ≤
        inp.h + C_all_s * x ^ k_all := by
      have hheap_123 : Task3Input.maxHeapEnd impl (inp.toT3 0) + 3 +
          Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl ≤
          inp.h + C_all_s * x ^ k_all := by
        have h1 : Task3Input.maxHeapEnd impl (inp.toT3 0) +
            Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl ≤
            sparsifyMaxHeapEnd impl inp := by unfold sparsifyMaxHeapEnd; omega
        have h2 := le_trans h1 hsp_heap
        have h3 : 3 ≤ 4 * x ^ P.c_sp := by have := h1_pow P.c_sp; omega
        have h4 : (P.C_sp + 4) * x ^ P.c_sp ≤ C_all_s * x ^ k_all :=
          spPoly_le hx1 le_rfl (by omega) (le_max_left _ _)
        nlinarith only [h2, h3, h4]
      unfold Task3Input.maxWordBound; simp only [Task1Input.toT3]
      have hmax_add : ∀ a b c d : ℕ, max a b + c + d = max (a + c + d) (b + c + d) :=
        fun a b c d => by omega
      rw [hmax_add]
      refine max_le hheap_123 ?_
      have hη2_le : eta2Bound inp.J ≤ 3 * x := by
        unfold eta2Bound; have := spNat_log2_le_self (inp.J.m + 1); dsimp only [x, s, sparsifyInputSize]; omega
      have hnonheap : max (eta2Bound inp.J * Task1Input.tau2Cap impl inp.J * maxDeg inp.J *
            Task1Input.phiDenCap impl inp.J + 2)
          (max (inp.J.m * Task1Input.phiDenCap impl inp.J + 2)
            (3 * Task1Input.mwCap impl inp.J + 2 * inp.J.m + 4)) ≤
          C_w3 * x ^ k_w3 := by
        refine max_le ?_ (max_le ?_ ?_)
        · have p3 := spPoly_mul (spPoly_mul (spPoly_mul (show eta2Bound inp.J ≤ 3 * x ^ 1 by simp only [pow_one]; omega) htau2_le)
            (show maxDeg inp.J ≤ 2 * x ^ 1 by simp only [pow_one]; omega)) hpd_le
          have p3' : eta2Bound inp.J * Task1Input.tau2Cap impl inp.J * maxDeg inp.J *
              Task1Input.phiDenCap impl inp.J ≤ (6 * P.C_tau2 * P.C_pd) * x ^ (1 + P.k_tau2 + 1 + P.k_pd) := by
            have hEq : 3 * P.C_tau2 * 2 * P.C_pd = 6 * P.C_tau2 * P.C_pd := by ring
            rwa [hEq] at p3
          have p4 : eta2Bound inp.J * Task1Input.tau2Cap impl inp.J * maxDeg inp.J *
              Task1Input.phiDenCap impl inp.J ≤ (6 * P.C_tau2 * P.C_pd) * x ^ k_w3 :=
            spPoly_le hx1 p3' le_rfl (by omega)
          have hb := h1_pow k_w3
          have hge : (6 * P.C_tau2 * P.C_pd + 4) * x ^ k_w3 ≤ C_w3 * x ^ k_w3 := by
            have h6 : 6 * P.C_tau2 * P.C_pd ≤ 18 * P.C_tau2 * P.C_pd :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
            exact Nat.mul_le_mul_right _ (by dsimp only [C_w3]; omega)
          have hrew : (6 * P.C_tau2 * P.C_pd + 4) * x ^ k_w3 =
              (6 * P.C_tau2 * P.C_pd) * x ^ k_w3 + 4 * x ^ k_w3 := by ring
          linarith only [p4, hb, hge, hrew]
        · have p2 : inp.J.m * Task1Input.phiDenCap impl inp.J ≤ P.C_pd * x ^ k_w3 :=
            spPoly_le hx1 (by simpa [one_mul] using spPoly_mul (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega) hpd_le)
              le_rfl (by omega)
          have hb := h1_pow k_w3
          have hge : (P.C_pd + 4) * x ^ k_w3 ≤ C_w3 * x ^ k_w3 :=
            Nat.mul_le_mul_right _ (by dsimp only [C_w3]; omega)
          have hrew : (P.C_pd + 4) * x ^ k_w3 = P.C_pd * x ^ k_w3 + 4 * x ^ k_w3 := by ring
          linarith only [p2, hb, hge, hrew]
        · have ha := spPoly_le hx1 hmw_le le_rfl (by omega : P.k_mw ≤ k_w3)
          have hb : 2 * inp.J.m + 4 ≤ 8 * x ^ k_w3 := by
            have : x ≤ x ^ k_w3 := Nat.le_self_pow (by omega) x; omega
          have hge : (3 * P.C_mw + 8) * x ^ k_w3 ≤ C_w3 * x ^ k_w3 :=
            Nat.mul_le_mul_right _ (by dsimp only [C_w3]; omega)
          have hrew : (3 * P.C_mw + 8) * x ^ k_w3 = 3 * (P.C_mw * x ^ k_w3) + 8 * x ^ k_w3 := by ring
          linarith only [ha, hb, hge, hrew]
      have ht12_all : Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl ≤
          inp.h + P.C_sp * x ^ k_all := by
        have h1 : Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl ≤
            sparsifyMaxHeapEnd impl inp := by unfold sparsifyMaxHeapEnd; omega
        exact le_trans (le_trans h1 hsp_heap) (Nat.add_le_add_left (spPoly_le hx1 le_rfl le_rfl (le_max_left _ _)) _)
      have hw3_all : C_w3 * x ^ k_w3 ≤ C_w3 * x ^ k_all :=
        spPoly_le hx1 le_rfl le_rfl (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      have hsum : P.C_sp * x ^ k_all + C_w3 * x ^ k_all ≤ C_all_s * x ^ k_all := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      linarith only [hnonheap, ht12_all, hw3_all, hsum]
    -- All 6 `Nat.log 2` bounds:
    have hlog_dec : dec.cw * (Nat.log 2 (inp.J.n + m0 + Task1Input.phiDenCap impl inp.J + 2) + 1) ≤ w := by
      refine hlog_w_of_s dec.cw _ (le_max_left _ _) ?_
      have h1 : inp.J.n + m0 + 2 ≤ 3 * x ^ P.k_pd := by
        have hx2 : 2 ≤ x := by dsimp only [x]; omega
        have hxp : x ≤ x ^ P.k_pd := Nat.le_self_pow (by have := P.hk_pd; omega) x
        linarith only [hJn_x, hm0_x, hx2, hxp]
      have h2 : inp.J.n + m0 + Task1Input.phiDenCap impl inp.J + 2 ≤ (P.C_pd + 3) * x ^ P.k_pd := by
        have hrew : (P.C_pd + 3) * x ^ P.k_pd = P.C_pd * x ^ P.k_pd + 3 * x ^ P.k_pd := by ring
        linarith only [h1, hpd_le, hrew]
      exact spPoly_le hx1 h2 (le_max_left _ _) (le_max_left _ _)
    have hlog_pdsJ : pds.cw * (Nat.log 2 (Task1Input.dJCap impl inp.J + m0 +
        pds.gExp (Task1Input.dJCap impl inp.J) m0 + pds.gDel (Task1Input.dJCap impl inp.J) m0 + 2) + 1) ≤ w := by
      refine hlog_w_of_s pds.cw _ (le_trans (le_max_left _ _) (le_max_right _ _)) ?_
      have h1 := spPoly_le hx1 hargJ_le le_rfl (le_max_left P.k_mw P.k_pds)
      have h2 := spPoly_le hx1 hgEJ_le le_rfl (le_max_right P.k_mw P.k_pds)
      have h3 := spPoly_le hx1 hgDJ_le le_rfl (le_max_right P.k_mw P.k_pds)
      have h4 : Task1Input.dJCap impl inp.J + m0 + pds.gExp (Task1Input.dJCap impl inp.J) m0 +
          pds.gDel (Task1Input.dJCap impl inp.J) m0 + 2 ≤ (P.C_argJ + 2 * P.C_pds) * x ^ max P.k_mw P.k_pds := by
        have hrew : (P.C_argJ + 2 * P.C_pds) * x ^ max P.k_mw P.k_pds =
            P.C_argJ * x ^ max P.k_mw P.k_pds + 2 * (P.C_pds * x ^ max P.k_mw P.k_pds) := by ring
        linarith only [h1, h2, h3, hrew]
      exact spPoly_le hx1 h4 (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    have hlog_pdsW : pds.cw * (Nat.log 2 (dW + Task1Input.mwCap impl inp.J +
        pds.gExp dW (Task1Input.mwCap impl inp.J) + pds.gDel dW (Task1Input.mwCap impl inp.J) + 2) + 1) ≤ w := by
      refine hlog_w_of_s pds.cw _ (le_trans (le_max_left _ _) (le_max_right _ _)) ?_
      have h1 := spPoly_le hx1 hargW_le le_rfl (le_max_left P.k_mw P.k_pds)
      have h2 := spPoly_le hx1 hgEW_le le_rfl (le_max_right P.k_mw P.k_pds)
      have h3 := spPoly_le hx1 hgDW_le le_rfl (le_max_right P.k_mw P.k_pds)
      have h4 : dW + Task1Input.mwCap impl inp.J + pds.gExp dW (Task1Input.mwCap impl inp.J) +
          pds.gDel dW (Task1Input.mwCap impl inp.J) + 2 ≤ (P.C_argW + 2 * P.C_pds) * x ^ max P.k_mw P.k_pds := by
        have hrew : (P.C_argW + 2 * P.C_pds) * x ^ max P.k_mw P.k_pds =
            P.C_argW * x ^ max P.k_mw P.k_pds + 2 * (P.C_pds * x ^ max P.k_mw P.k_pds) := by ring
        linarith only [h1, h2, h3, hrew]
      exact spPoly_le hx1 h4 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    have hlog_ce : ce.cw * (Nat.log 2 (inp.J.n + 4 * m0 * Task1Input.phiDenCap impl inp.J + 2) + 1) ≤ w := by
      refine hlog_w_of_s ce.cw _ (le_trans (le_max_right _ _) (le_max_right _ _)) ?_
      exact spPoly_le hx1 hceArg_le
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hlog_t2 : pds.cw * (Nat.log 2 (inp.J.n + m0 + Task1Input.phiDenCap impl inp.J + m0 +
        pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) + 1) ≤ w := by
      refine hlog_w_of_s pds.cw _ (le_trans (le_max_left _ _) (le_max_right _ _)) ?_
      have hrew : inp.J.n + m0 + Task1Input.phiDenCap impl inp.J + m0 +
          pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2 =
          Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
          pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2 := by ring
      rw [hrew]
      exact spPoly_le hx1 hdsJArg_le
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _)))))
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have hlog_t3 : pds.cw * (Nat.log 2 (ce.phiDen + 4 * Task1Input.mwCap impl inp.J +
        pds.gExp dW (Task1Input.mwCap impl inp.J) + 2) + 1) ≤ w := by
      refine hlog_w_of_s pds.cw _ (le_trans (le_max_left _ _) (le_max_right _ _)) ?_
      exact spPoly_le hx1 hdsWArg_le
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _)))))
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have hw1_gt : 1 < 2 ^ w := lt_of_lt_of_le (by norm_num : 1 < 16) hw16
    have hmVal_lt : mVal < 2 ^ w := lt_of_le_of_lt (by dsimp only [H]; omega) hH_lt_2w
    have hw1_ok : inp.WordWidthOK impl w :=
      ⟨hw1_gt, fun v hv => lt_of_le_of_lt (hJenc v hv) hmVal_lt,
        hlog_dec, hlog_pdsJ, hlog_pdsW, hlog_ce, hlt_w_of_s _ hw1_le⟩
    have hw2_lt := hlt_w_of_s _ hw2_le
    have hw3_lt := hlt_w_of_s _ hw3_le
    have hsp_lt : sparsifyMaxHeapEnd impl inp < 2 ^ w :=
      hlt_w_of_s _ (le_trans hsp_heap (Nat.add_le_add_left (spPoly_le hx1 le_rfl (by omega) (le_max_left _ _)) _))
    have hcore_ok : SparsifyCoreWordOK impl inp w :=
      sparsifyCoreWordOK_of_width
        ⟨⟨hw1_gt, hlog_t2, lt_of_le_of_lt (Nat.le_add_right _ _) hw2_lt⟩, hw2_lt⟩
        ⟨⟨hw1_gt, hlog_t3, lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hw3_lt⟩, hw3_lt⟩
    exact ⟨hw1_ok, hcore_ok, hsp_lt⟩

end MinCostFlow.Spanner
