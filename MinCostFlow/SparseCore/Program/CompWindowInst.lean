module

public import MinCostFlow.SparseCore.Program.CompWindow
public import MinCostFlow.SparseCore.Program.LSFWindowProc
import Mathlib.Tactic.Linarith

/-!
# Canonical P3 Window Instantiation (`CompWindowInst`)

Instantiates `CompWindow.LSFWindowImpl` with P3's canonical dynamic-LSF window initializer
(`LSFWindowProc.lsfWindowProcs`, `lsfWindowInit_runs`, `h = 4`, `canonicalLSFInit`,
`canonicalLSFInit_spec`), yielding `canonicalLSFWindowImpl`.

The space bound `canonWinSpace` replaces the graph-dependent `canonVCap G₀` and `canonECap G₀`
in `lsfWindowSpace` by the host capacities `vCap` and `eCap` (which dominate them by
`canonVCap_le_of_dynGraphAt` and `canonECap_le_of_dynGraphAt`), and the cost bound is verbatim
`lsfWindowCost`, completely independent of `vCap`, `eCap`, and `L_w`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## Monotone host-parameter space upper bound for `lsfWindowSpace` -/

/-- Host-parameter upper bound on `canonWordBound` replacing `canonVCap G₀, canonECap G₀` by
`vCap, eCap`. -/
noncomputable def canonWinWordBound (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (h L_in P_fp k_nat vCap eCap n0 m0 : ℕ) : ℕ :=
  let cHeap := dynGraphSize vCap eCap + eCap * L_in + k_nat
  max (cHeap +
        lemma55Space Q_AN K_AN c_AN h L_in (canonLw K_AN L_in n0 k_nat) P_fp k_nat
          vCap eCap n0 m0)
      (max (2 * P_fp + 9) (3 * (4 * k_nat * (hldDepthBound n0 + 1)))) + 1

/-- Host-parameter upper bound on `canonWordBits`. -/
noncomputable def canonWinWordBits (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (h L_in P_fp k_nat vCap eCap n0 m0 : ℕ) : ℕ :=
  max (3 * h + 2) (Nat.log 2 (canonWinWordBound Q_AN c_AN K_AN h L_in P_fp k_nat vCap eCap n0 m0) + 1)

/-- Host-parameter upper bound on `lsfWindowSpace`, depending only on `(k, L_w, vCap, eCap, n, m)`. -/
noncomputable def canonWinSpace (Q_AN : Program) (K_AN : ℝ) (c_AN h L_in P_fp : ℕ)
    (k_nat L_w vCap eCap n0 m0 : ℕ) : ℕ :=
  let cHnd := dynGraphSize vCap eCap + eCap * L_in
  max (2 ^ canonWinWordBits Q_AN c_AN K_AN h L_in P_fp k_nat vCap eCap n0 m0)
    (cHnd + max n0 m0 + 1) +
    k_nat * lsfStaticSize vCap eCap n0 n0 L_w + 1

private lemma lsfStaticSize_mono {v1 v2 e1 e2 n0 tM L_w : ℕ} (hv : v1 ≤ v2) (he : e1 ≤ e2) :
    lsfStaticSize v1 e1 n0 tM L_w ≤ lsfStaticSize v2 e2 n0 tM L_w := by
  unfold lsfStaticSize tBlockSize fAncSize fECap auxSize
  unfold dynGraphSize
  have h1 : e1 * L_w ≤ e2 * L_w := Nat.mul_le_mul_right L_w he
  omega

private lemma lemma55Space_mono {Q_AN : Program} {K_AN : ℝ}
    {c_AN h L_in L_w P_fp k_nat v1 v2 e1 e2 n0 m0 : ℕ} (hv : v1 ≤ v2) (he : e1 ≤ e2) :
    lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat v1 e1 n0 m0 ≤
      lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat v2 e2 n0 m0 := by
  unfold lemma55Space
  dsimp only
  have h1 : e1 * L_in ≤ e2 * L_in := Nat.mul_le_mul_right L_in he
  have h2 : e1 * L_w ≤ e2 * L_w := Nat.mul_le_mul_right L_w he
  have h3 : lsfStaticSize v1 e1 n0 n0 L_w ≤ lsfStaticSize v2 e2 n0 n0 L_w :=
    lsfStaticSize_mono hv he
  have h4 : k_nat * (lsfStaticSize v1 e1 n0 n0 L_w + 2 * (e1 * L_w) +
      WideWord.lsstSpace Q_AN K_AN n0 (2 * m0) (WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h) h +
      200 * (n0 + m0 + 1) * (L_w + WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h + auxLogCap n0 + 20) + 1000) ≤
    k_nat * (lsfStaticSize v2 e2 n0 n0 L_w + 2 * (e2 * L_w) +
      WideWord.lsstSpace Q_AN K_AN n0 (2 * m0) (WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h) h +
      200 * (n0 + m0 + 1) * (L_w + WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h + auxLogCap n0 + 20) + 1000) :=
    Nat.mul_le_mul_left k_nat (by omega)
  omega

lemma lsfWindowSpace_le_canonWinSpace {Q_AN : Program} {K_AN : ℝ}
    {c_AN h L_in L_w P_fp k_nat vCap eCap : ℕ} {G₀ : MGraph}
    (hv : canonVCap G₀ ≤ vCap) (he : canonECap G₀ ≤ eCap) :
    lsfWindowSpace Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀ ≤
      canonWinSpace Q_AN K_AN c_AN h L_in P_fp k_nat L_w vCap eCap G₀.n G₀.m := by
  have hdg : dynGraphSize (canonVCap G₀) (canonECap G₀) ≤ dynGraphSize vCap eCap := by
    unfold dynGraphSize; omega
  have heL : canonECap G₀ * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in he
  have hHnd : canonHandlesOut G₀ L_in ≤ dynGraphSize vCap eCap + eCap * L_in := by
    unfold canonHandlesOut canonLenArr; omega
  have hHeap : canonHeap G₀ L_in k_nat ≤ dynGraphSize vCap eCap + eCap * L_in + k_nat := by
    unfold canonHeap; omega
  have hSp := lemma55Space_mono (Q_AN := Q_AN) (K_AN := K_AN) (c_AN := c_AN) (h := h)
    (L_in := L_in) (L_w := canonLw K_AN L_in G₀.n k_nat) (P_fp := P_fp) (k_nat := k_nat)
    (n0 := G₀.n) (m0 := G₀.m) hv he
  have hWB : canonWordBound Q_AN c_AN K_AN h L_in P_fp G₀ k_nat ≤
      canonWinWordBound Q_AN c_AN K_AN h L_in P_fp k_nat vCap eCap G₀.n G₀.m := by
    unfold canonWordBound canonWinWordBound
    have h1 := Nat.add_le_add hHeap hSp
    exact Nat.add_le_add_right (max_le (le_trans h1 (le_max_left _ _)) (le_max_right _ _)) 1
  have hBits : canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat ≤
      canonWinWordBits Q_AN c_AN K_AN h L_in P_fp k_nat vCap eCap G₀.n G₀.m := by
    unfold canonWordBits canonWinWordBits
    exact max_le (le_max_left _ _)
      (le_trans (Nat.add_le_add_right (Nat.log_mono_right hWB) 1) (le_max_right _ _))
  have hPow : 2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat ≤
      2 ^ canonWinWordBits Q_AN c_AN K_AN h L_in P_fp k_nat vCap eCap G₀.n G₀.m :=
    Nat.pow_le_pow_right (by decide) hBits
  unfold lsfWindowSpace canonWinSpace
  dsimp only
  have hM : max (2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat)
      (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) ≤
      max (2 ^ canonWinWordBits Q_AN c_AN K_AN h L_in P_fp k_nat vCap eCap G₀.n G₀.m)
        (dynGraphSize vCap eCap + eCap * L_in + max G₀.n G₀.m + 1) :=
    max_le (le_trans hPow (le_max_left _ _)) (le_trans (by omega) (le_max_right _ _))
  exact Nat.add_le_add_right (Nat.add_le_add_right hM _) 1

/-! ## Parameter precondition and P3 `LSFWindowImpl` instance -/

/-- Parameter precondition for `canonicalLSFWindowImpl` (`h = 4`): matches the exact fixed-point
and word-size hypotheses of `lsfWindowInit_runs`. -/
def canonWinPre (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (L_in P_fp : ℕ)
    (w k_nat L_w _vCap _eCap : ℕ) (G_C : MGraph) : Prop :=
  1 ≤ L_in ∧ 4 ∣ P_fp ∧ P_fp + 6 ≤ 4 * L_in ∧
  (∃ q, q + 11 ≤ P_fp ∧ 40 * k_nat ≤ 2 ^ q) ∧
  32 * (G_C.E.card + 1) * 2 ^ P_fp < 2 ^ (4 * L_in - 1) ∧
  canonLw K_AN L_in G_C.n k_nat ≤ L_w ∧
  canonWordBits Q_AN c_AN K_AN 4 L_in P_fp G_C k_nat ≤ w

/-- **Canonical P3 instantiation of `CompWindow.LSFWindowImpl`** (`h = 4`, `canonicalLSFInit`,
`lsfWindowProcs`, `lsfWindowInit_runs`). -/
noncomputable def canonicalLSFWindowImpl (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) (L_in P_fp : ℕ) : LSFWindowImpl where
  Q_AN := Q_AN
  c_AN := c_AN
  K_AN := K_AN
  h := 4
  hh := by decide
  L_in := L_in
  P_fp := P_fp
  lsfInit := canonicalLSFInit Q_AN c_AN K_AN L_in P_fp
  C_lsst := max (4 * max K_AN 1 + 5) (MinCostFlow.LSF.Program.defaultK_sigma K_AN / 6272)
  hInitValid := fun k j _ hj => by
    obtain ⟨K_ρ, _, hMWU⟩ := canonicalLSFInit_spec Q_AN c_AN K_AN (fullAN19_to_stretchOnly hQ)
    exact (hMWU L_in P_fp).toValidLSFInitFor hj
  procs b := lsfWindowProcs Q_AN c_AN K_AN b 4
  procsLen := 21 + (lemma55Module Q_AN c_AN K_AN 4).procs.length
  procs_length b := lsfWindowProcs_length Q_AN c_AN K_AN b 4
  procs_noRand b := lsfWindowProcs_noRand Q_AN c_AN K_AN b 4
  initOff := lsfWindowIdxInit
  winPre := canonWinPre Q_AN c_AN K_AN L_in P_fp
  winSpace := canonWinSpace Q_AN K_AN c_AN 4 L_in P_fp
  winCost k _L_w n m := lsfWindowCost Q_AN c_AN K_AN 4 L_in P_fp k n m
  winInit_runs := by
    intro w b g0Ptr lenArr k L_w vCap eCap handlesOut heap p ω G_C ℓ₀ mem pos
      hp hk hLw heCap1 hpre hG_val hV_ne _ _ hdg hℓ hg0_le hlen_le hhnd_le _ _ _ hz hsp
    obtain ⟨hLin1, hdiv, hPLin, ⟨q, hqP, hkq⟩, hmLin, hLwC, hw_le⟩ := hpre
    have hv_le : canonVCap G_C ≤ vCap := canonVCap_le_of_dynGraphAt hdg hV_ne
    have he_le : canonECap G_C ≤ eCap := canonECap_le_of_dynGraphAt hdg heCap1
    have hsp_le := lsfWindowSpace_le_canonWinSpace (Q_AN := Q_AN) (K_AN := K_AN) (c_AN := c_AN)
      (h := 4) (L_in := L_in) (L_w := L_w) (P_fp := P_fp) (k_nat := k) hv_le he_le
    have hheap1 : 1 ≤ heap := by
      have : 4 ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
      omega
    obtain ⟨body, hbody, endHeap, st', c, x_h, hs, hrun, hlo, hhi, hz', hfr, hjs, hdisj, hcost⟩ :=
      lsfWindowInit_runs (w := w) (h := 4) (q := q) (c_AN := c_AN) (b := b) (g0Ptr := g0Ptr)
        (lenArr := lenArr) (L_in := L_in) (P_fp := P_fp) (k_nat := k) (L_w_host := L_w)
        (vCap_host := vCap) (eCap_host := eCap) (handlesOut := handlesOut) (heap := heap)
        (vCap0 := vCap) (eCap0 := eCap) pos ω hp hQ (by decide) hLin1 hdiv hPLin hk hqP hkq hmLin
        hLwC hG_val hV_ne hdg (le_refl _) (le_refl _) heCap1 hℓ hg0_le hlen_le hhnd_le hheap1 hz
        hw_le (lt_of_le_of_lt (Nat.add_le_add_left hsp_le heap) hsp)
    exact ⟨body, hbody, endHeap, st', c, x_h, hs, hrun, hlo, le_trans hhi (Nat.add_le_add_left hsp_le heap),
      hz', hfr, fun j hj => by
        obtain ⟨h1, h2, h3, h4, h5, _, _, h8⟩ := hjs j hj
        exact ⟨h1, h2, h3, h4, h5, h8⟩,
      hdisj, hcost⟩

end

end MinCostFlow.SparseCore.Program
