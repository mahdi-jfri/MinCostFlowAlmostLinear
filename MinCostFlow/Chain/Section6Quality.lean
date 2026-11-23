module

public import MinCostFlow.Chain.Lemma5_11

/-!
# Section 6.1: Cycle Quality with Representative Timesteps

This file formalizes **Section 6.1** (`jtree.tex` lines 520–706, pages 25–27):

* **Definition 6.1** (`hstrAt`, `hstrCurr`, `IsRepTimestamps`): representative timestamps
  `repT_0, ..., repT_d` and current / branch-wise stretches `hstr_{i, j}` with respect to
  `w^{(repT_i), G_i}`.
* **Lemma 6.2** (`lemma_6_2`): inductive width bound `eq:treeChainIH` (563) and total level
  bound `eq:hintedTreeChainWidthBound` (556) relating `∑_{i=0}^d ‖w^{(t), G_i}‖₁` to
  `‖w^{(t)}‖₁` and `∏ (1 + 2 hstr_b) ‖w^{(repT_a)}‖₁` with explicit constant `(2 γ_ℓ)^d`.
* **Corollary 6.4** (`corollary_6_4`): at every level `i < d`, the average over `j < k` of
  `hstr_{i, j}` is at most `σ_mwu`, so some branch `j < k` achieves `hstr_{i, j} ≤ σ_mwu`.
* **Lemma 6.3** (`lemma_6_3`): contrapositive cycle-quality dichotomy (`eq:dsBadWtSum` 640 or
  `eq:dsBadStr` 645) showing explicitly that Definition 4.4 item 3 (`⟨g, c⟩ / ‖w‖₁ ≤ -α`)
  is used **only** at level `0` at stage `t` (never at lower levels `i ≥ 1` or past
  timestamps `repT_a`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section Def6_1

/-- Branch-`j` stretch at level `i` of a `TreeChain` snapshot `C` relative to a top-level
witness weight vector `w` (**Definition 6.1**, page 25, lines 536–541):
`hstr_{i, j} = (∑_{e ∈ E(G_i)} wstr^{F_j}_e * w^{G_i}_e) / ‖w^{G_i}‖₁` (and `0` when the
denominator vanishes). -/
noncomputable def hstrAt (C : TreeChain) (w : ℕ → ℝ) (i j : ℕ) : ℝ :=
  let wi := C.chainW w i
  let den := (C.G i).norm1 wi
  if den = 0 then 0
  else (∑ e ∈ (C.G i).E, (C.lsfs i j).wstr e * wi e) / den

/-- Current stretch `hstr_i := hstr_{i, bran_i}` (**Definition 6.1**, page 25, line 543). -/
noncomputable def hstrCurr (C : TreeChain) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  hstrAt C w i (C.bran i)

/-- **Definition 6.1** (Representative timestamps, page 25): at stage `t`, each level `i ≤ d`
has `reinit i ≤ repT i ≤ t`, ordered `repT (i - 1) ≤ repT i` for `0 < i`, and
`repT i ≤ reinit (i + 1)` for `i < d` (since any rebuild/shift below `i + 1` re-initializes
level `i + 1`). -/
def IsRepTimestamps (d : ℕ) (reinit : ℕ → ℕ) (t : ℕ) (repT : ℕ → ℕ) : Prop :=
  (∀ i ≤ d, reinit i ≤ repT i ∧ repT i ≤ t) ∧
  (∀ i, 0 < i → i ≤ d → repT (i - 1) ≤ repT i) ∧
  (∀ i < d, repT i ≤ reinit (i + 1))

lemma hstrAt_nonneg {C : TreeChain} {G : MGraph} {ℓ w : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hw : ∀ e ∈ G.E, 0 ≤ w e) {i j : ℕ} (hi : i < C.d)
    (hj : j < C.k) :
    0 ≤ hstrAt C w i j := by
  have hvp0 : IsValidPair G ℓ (fun _ => 0) w :=
    ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using hw e he⟩
  have hci := C.chain_isValidPair hH hSub hℓ hvp0 i (Nat.le_of_lt hi)
  have hwi_nn : ∀ e ∈ (C.G i).E, 0 ≤ C.chainW w i e := fun e he =>
    le_trans (abs_nonneg _) (hci.1.2 e he)
  have hLSFj : (C.lsfs i j).Holds (C.G i) (C.chainLen ℓ i) σ :=
    ((hH.2.2.2.2.1 i hi).2.1 j hj).1
  have hwstr_nn : ∀ e ∈ (C.G i).E, 0 ≤ (C.lsfs i j).wstr e := fun e he => by
    have h1 := one_le_stretch hLSFj.2.1.2.2.2.2 (fun f hf => hci.2 f hf) he
    have h2 := (hLSFj.2.2.2 e he).1
    linarith
  unfold hstrAt
  dsimp only
  split_ifs with hden
  · exact le_rfl
  · refine div_nonneg ?_ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact Finset.sum_nonneg fun e he => mul_nonneg (hwstr_nn e he) (hwi_nn e he)

lemma sum_wstr_mul_chainW_eq_hstrAt {C : TreeChain} {G : MGraph} {ℓ w : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hw : ∀ e ∈ G.E, 0 ≤ w e) (i j : ℕ) (hi : i ≤ C.d) :
    ∑ e ∈ (C.G i).E, (C.lsfs i j).wstr e * C.chainW w i e =
      hstrAt C w i j * (C.G i).norm1 (C.chainW w i) := by
  have hvp0 : IsValidPair G ℓ (fun _ => 0) w :=
    ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using hw e he⟩
  have hwi_nn : ∀ e ∈ (C.G i).E, 0 ≤ C.chainW w i e := fun e he =>
    le_trans (abs_nonneg _) ((C.chain_isValidPair hH hSub hℓ hvp0 i hi).1.2 e he)
  unfold hstrAt
  by_cases hden : (C.G i).norm1 (C.chainW w i) = 0
  · rw [ite_eq_left_iff.mpr fun h => absurd hden h, zero_mul]
    refine Finset.sum_eq_zero fun e he => ?_
    have hnorm0 : ∑ e' ∈ (C.G i).E, |C.chainW w i e'| = 0 := hden
    have hle : |C.chainW w i e| ≤ 0 := hnorm0 ▸
      Finset.single_le_sum (f := fun e' => |C.chainW w i e'|) (fun _ _ => abs_nonneg _) he
    have habs0 : |C.chainW w i e| = 0 := le_antisymm hle (abs_nonneg _)
    have hwe0 : C.chainW w i e = 0 := abs_eq_zero.mp habs0
    rw [hwe0, mul_zero]
  · rw [ite_eq_right_iff.mpr fun h => absurd h hden, div_mul_cancel₀ _ hden]

end Def6_1

section Lemma6_2

/-- Snapshots and stability invariants over `[reinit i, t]` justifying **Lemma 6.2**:
1. Every active level window `[reinit i, t]` satisfies `Chain` holds and nonneg `ℓ0, w`
   (notice item 3 of Definition 4.4 is NOT needed anywhere here).
2. During `[reinit i, t]`, no level `b < i` changes branch.
3. Between `repT i` and any stage `r ∈ [repT i, t]`, every edge `e ∈ E(G_i^{(r)})` either was
   inserted after `repT i` (so `wstr = 1`) or survived without insertion (so `wstr` is unchanged
   and `w^{(r), G_i}_e ≤ 2 w^{(repT_i), G_i}_e` from WeakHiddenStable item 4 via Lemma 5.17
   item 2). -/
structure RepQualityCtx where
  d : ℕ
  k : ℕ
  hd : 0 < d
  hk : 0 < k
  γ_ℓ : ℝ
  γ_c : ℝ
  hγℓ : 1 ≤ γ_ℓ
  hγc : 1 ≤ γ_c
  σ : ℝ
  σ_mwu : ℝ
  C : ℕ → TreeChain
  G0 : ℕ → MGraph
  ℓ0 : ℕ → ℕ → ℝ
  w : ℕ → ℕ → ℝ
  reinit : ℕ → ℕ
  repT : ℕ → ℕ
  t : ℕ
  hRep : IsRepTimestamps d reinit t repT
  hWindow : ∀ i ≤ d, ∀ r, reinit i ≤ r → r ≤ t →
    (C r).d = d ∧
    (C r).k = k ∧
    (C r).Holds (G0 r) (ℓ0 r) σ σ_mwu γ_ℓ γ_c ∧
    (C r).ForestsAreSubgraphs ∧
    (∀ e ∈ (G0 r).E, 0 ≤ ℓ0 r e ∧ 0 ≤ w r e) ∧
    (∀ b < i, (C r).bran b = (C t).bran b) ∧
    (∀ (_hi : i < d), repT i ≤ r → ∀ e ∈ ((C r).G i).E,
      ((C r).lsfs i ((C t).bran i)).wstr e = 1 ∨
      (e ∈ ((C (repT i)).G i).E ∧
        ((C r).lsfs i ((C t).bran i)).wstr e = ((C (repT i)).lsfs i ((C t).bran i)).wstr e ∧
        (C r).chainW (w r) i e ≤ 2 * (C (repT i)).chainW (w (repT i)) i e))

lemma chainW_norm1_succ_le {C : TreeChain} {G : MGraph} {ℓ w : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hγ : 0 ≤ γ_ℓ) (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hw : ∀ e ∈ G.E, 0 ≤ w e)
    {i : ℕ} (hi : i < C.d) :
    (C.G (i + 1)).norm1 (C.chainW w (i + 1)) ≤
      2 * γ_ℓ * ∑ e ∈ (C.G i).E, (C.activeLSF i).wstr e * C.chainW w i e := by
  have hvp0 : IsValidPair G ℓ (fun _ => 0) w :=
    ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using hw e he⟩
  have hci := C.chain_isValidPair hH hSub hℓ hvp0 i (Nat.le_of_lt hi)
  have hCore := lemma_5_13 (C.G_isValid hH i (Nat.le_of_lt hi))
    (C.activeLSF_holds hH (Nat.le_of_lt hi)) (hSub i (Nat.le_of_lt hi)) hci.2 hci.1
  have hSp := C.activeS_isSparsified hH hi
  have hSparse := lemma_5_16_noSize hSp hCore.1
  have hSp' : (C.G (i + 1)).norm1 (C.chainW w (i + 1)) ≤
      2 * γ_ℓ * (coreGraph (C.G i) (C.activeLSF i)).norm1
        (passCoreW (C.activeLSF i) (C.chainW w i)) := by
    simpa only [TreeChain.chainW, TreeChain.activeCore, C.activeS_eq_G_succ hH hi] using hSparse.2
  exact le_trans hSp' (mul_le_mul_of_nonneg_left hCore.2 (by positivity))

private lemma hstrRep_nonneg (ctx : RepQualityCtx) {b : ℕ} (hb : b < ctx.d) :
    0 ≤ hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b) := by
  have hrt := ctx.hRep.1 b (Nat.le_of_lt hb)
  have hW := ctx.hWindow b (Nat.le_of_lt hb) (ctx.repT b) hrt.1 hrt.2
  have hW1 := ctx.hWindow (b + 1) hb ctx.t (ctx.hRep.1 (b + 1) hb |>.1 |>.trans
    (ctx.hRep.1 (b + 1) hb |>.2)) (le_refl ctx.t)
  have hb_lt_d' : b < (ctx.C (ctx.repT b)).d := by rw [hW.1]; exact hb
  have hbran_lt : (ctx.C ctx.t).bran b < (ctx.C (ctx.repT b)).k := by
    rw [hW.2.1, ← hW1.2.1]
    exact (hW1.2.2.1.2.2.2.2.1 b (by rw [hW1.1]; exact hb)).1
  exact hstrAt_nonneg hW.2.2.1 hW.2.2.2.1 (fun e he => (hW.2.2.2.2.1 e he).1)
    (fun e he => (hW.2.2.2.2.1 e he).2) hb_lt_d' hbran_lt

/-- **Lemma 6.2** (inductive level bound `eq:treeChainIH`, page 25, line 563):
for every `i ≤ ctx.d` and every `r ∈ [ctx.reinit i, ctx.t]`,
`‖w^{(r), G_i}‖₁ ≤ (2 γ_ℓ)^i (‖w^{(r)}‖₁ + ∑_{a < i} (∏_{b ∈ [a, i)} (1 + 2 hstr_b)) ‖w^{(repT_a)}‖₁)`. -/
theorem lemma_6_2_inductive (ctx : RepQualityCtx) :
    ∀ i ≤ ctx.d, ∀ r, ctx.reinit i ≤ r → r ≤ ctx.t →
      ((ctx.C r).G i).norm1 ((ctx.C r).chainW (ctx.w r) i) ≤
        (2 * ctx.γ_ℓ) ^ i *
          ((ctx.G0 r).norm1 (ctx.w r) +
            ∑ a ∈ Finset.range i,
              (∏ b ∈ Finset.Ico a i,
                (1 + 2 * hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b
                  ((ctx.C ctx.t).bran b))) *
                (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))) := by
  let H : ℕ → ℝ := fun b =>
    hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b)
  intro i
  induction i with
  | zero =>
    intro _ r hre hrt
    have hW := ctx.hWindow 0 (Nat.zero_le ctx.d) r hre hrt
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, add_zero]
    rw [hW.2.2.1.1]
    simp [TreeChain.chainW]
  | succ i ih =>
    intro hi r hre hrt
    have hi_lt : i < ctx.d := hi
    have hi_le : i ≤ ctx.d := Nat.le_of_lt hi_lt
    have hW1 := ctx.hWindow (i + 1) hi r hre hrt
    have hrep_le_re1 : ctx.repT i ≤ ctx.reinit (i + 1) := ctx.hRep.2.2 i hi_lt
    have hre_i_r : ctx.reinit i ≤ r := le_trans (ctx.hRep.1 i hi_le).1 (le_trans hrep_le_re1 hre)
    have hre_i_rep : ctx.reinit i ≤ ctx.repT i := (ctx.hRep.1 i hi_le).1
    have hrt_rep : ctx.repT i ≤ ctx.t := (ctx.hRep.1 i hi_le).2
    have hrep_le_r : ctx.repT i ≤ r := le_trans hrep_le_re1 hre
    have hIH_r := ih hi_le r hre_i_r hrt
    have hIH_rep := ih hi_le (ctx.repT i) hre_i_rep hrt_rep
    have hWi := ctx.hWindow i hi_le r hre_i_r hrt
    have hWrep := ctx.hWindow i hi_le (ctx.repT i) hre_i_rep hrt_rep
    have hbran_eq : (ctx.C r).bran i = (ctx.C ctx.t).bran i := hW1.2.2.2.2.2.1 i (Nat.lt_succ_self i)
    have hstep : ((ctx.C r).G (i + 1)).norm1 ((ctx.C r).chainW (ctx.w r) (i + 1)) ≤
        2 * ctx.γ_ℓ * ∑ e ∈ ((ctx.C r).G i).E,
          ((ctx.C r).activeLSF i).wstr e * (ctx.C r).chainW (ctx.w r) i e := by
      refine chainW_norm1_succ_le hW1.2.2.1 hW1.2.2.2.1 (le_trans zero_le_one ctx.hγℓ)
        (fun e he => (hW1.2.2.2.2.1 e he).1) (fun e he => (hW1.2.2.2.2.1 e he).2) ?_
      rw [hW1.1]; exact hi_lt
    have hvp0_r : IsValidPair (ctx.G0 r) (ctx.ℓ0 r) (fun _ => 0) (ctx.w r) :=
      ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using (hWi.2.2.2.2.1 e he).2⟩
    have hci_r := (ctx.C r).chain_isValidPair hWi.2.2.1 hWi.2.2.2.1
      (fun e he => (hWi.2.2.2.2.1 e he).1) hvp0_r i (by rw [hWi.1]; exact hi_le)
    have hwr_nn : ∀ e ∈ ((ctx.C r).G i).E, 0 ≤ (ctx.C r).chainW (ctx.w r) i e := fun e he =>
      le_trans (abs_nonneg _) (hci_r.1.2 e he)
    have hvp0_rep : IsValidPair (ctx.G0 (ctx.repT i)) (ctx.ℓ0 (ctx.repT i))
        (fun _ => 0) (ctx.w (ctx.repT i)) :=
      ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using (hWrep.2.2.2.2.1 e he).2⟩
    have hci_rep := (ctx.C (ctx.repT i)).chain_isValidPair hWrep.2.2.1 hWrep.2.2.2.1
      (fun e he => (hWrep.2.2.2.2.1 e he).1) hvp0_rep i (by rw [hWrep.1]; exact hi_le)
    have hwrep_nn : ∀ e ∈ ((ctx.C (ctx.repT i)).G i).E,
        0 ≤ (ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i e := fun e he =>
      le_trans (abs_nonneg _) (hci_rep.1.2 e he)
    have hbran_lt_k : (ctx.C ctx.t).bran i < (ctx.C (ctx.repT i)).k := by
      rw [hWrep.2.1, ← hW1.2.1, ← hbran_eq]
      exact (hW1.2.2.1.2.2.2.2.1 i (by rw [hW1.1]; exact hi_lt)).1
    have hwstr_rep_nn : ∀ e ∈ ((ctx.C (ctx.repT i)).G i).E,
        0 ≤ ((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e := by
      intro e he
      have hL := ((hWrep.2.2.1.2.2.2.2.1 i (by rw [hWrep.1]; exact hi_lt)).2.1
        ((ctx.C ctx.t).bran i) hbran_lt_k).1
      have h1 := one_le_stretch hL.2.1.2.2.2.2 (fun f hf => hci_rep.2 f hf) he
      have h2 := (hL.2.2.2 e he).1
      linarith
    classical
    have hterm_le : ∀ e ∈ ((ctx.C r).G i).E,
        ((ctx.C r).activeLSF i).wstr e * (ctx.C r).chainW (ctx.w r) i e ≤
          |(ctx.C r).chainW (ctx.w r) i e| +
          if e ∈ ((ctx.C (ctx.repT i)).G i).E then
            2 * (((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e *
              (ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i e)
          else 0 := by
      intro e he
      have hact_eq : (ctx.C r).activeLSF i = (ctx.C r).lsfs i ((ctx.C ctx.t).bran i) := by
        simp [TreeChain.activeLSF, hWi.1, hi_lt, hbran_eq]
      have hwe_nn := hwr_nn e he
      have hite_nn : 0 ≤ (if e ∈ ((ctx.C (ctx.repT i)).G i).E then
            2 * (((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e *
              (ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i e) else 0) := by
        split_ifs with he'
        · exact mul_nonneg (by norm_num) (mul_nonneg (hwstr_rep_nn e he') (hwrep_nn e he'))
        · exact le_rfl
      rcases hWi.2.2.2.2.2.2 hi_lt hrep_le_r e he with h1 | ⟨he', hwstr_eq, hw_le⟩
      · rw [hact_eq, h1, one_mul, abs_of_nonneg hwe_nn]
        linarith
      · rw [ite_eq_left_iff.mpr fun h => absurd he' h, hact_eq, hwstr_eq]
        have h1 : ((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e *
            (ctx.C r).chainW (ctx.w r) i e ≤
            2 * (((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e *
              (ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i e) := by
          have hnn := hwstr_rep_nn e he'
          nlinarith
        linarith [abs_nonneg ((ctx.C r).chainW (ctx.w r) i e)]
    have hsum_le : ∑ e ∈ ((ctx.C r).G i).E,
          ((ctx.C r).activeLSF i).wstr e * (ctx.C r).chainW (ctx.w r) i e ≤
        ((ctx.C r).G i).norm1 ((ctx.C r).chainW (ctx.w r) i) +
          2 * (H i * ((ctx.C (ctx.repT i)).G i).norm1 ((ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i)) := by
      have hs1 := Finset.sum_le_sum hterm_le
      rw [Finset.sum_add_distrib] at hs1
      have hite_le : ∑ e ∈ ((ctx.C r).G i).E,
          (if e ∈ ((ctx.C (ctx.repT i)).G i).E then
            2 * (((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e *
              (ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i e)
          else 0) ≤
          2 * (H i * ((ctx.C (ctx.repT i)).G i).norm1
            ((ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i)) := by
        rw [← Finset.sum_filter]
        have hsub : ((ctx.C r).G i).E.filter (fun e => e ∈ ((ctx.C (ctx.repT i)).G i).E) ⊆
            ((ctx.C (ctx.repT i)).G i).E := fun e he => (Finset.mem_filter.mp he).2
        have hs2 : ∑ e ∈ ((ctx.C r).G i).E.filter (fun e => e ∈ ((ctx.C (ctx.repT i)).G i).E),
              2 * (((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e *
                (ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i e) ≤
            ∑ e ∈ ((ctx.C (ctx.repT i)).G i).E,
              2 * (((ctx.C (ctx.repT i)).lsfs i ((ctx.C ctx.t).bran i)).wstr e *
                (ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i e) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun e he _ =>
            mul_nonneg (by norm_num) (mul_nonneg (hwstr_rep_nn e he) (hwrep_nn e he))
        refine le_trans hs2 ?_
        rw [← Finset.mul_sum]
        have hHeq := sum_wstr_mul_chainW_eq_hstrAt hWrep.2.2.1 hWrep.2.2.2.1
          (fun e he => (hWrep.2.2.2.2.1 e he).1) (fun e he => (hWrep.2.2.2.2.1 e he).2)
          i ((ctx.C ctx.t).bran i) (by rw [hWrep.1]; exact hi_le)
        exact le_of_eq (congrArg (2 * ·) hHeq)
      exact le_trans hs1 (add_le_add le_rfl hite_le)
    have hHi_nn : 0 ≤ H i := hstrRep_nonneg ctx hi_lt
    set S_i : ℝ := ∑ a ∈ Finset.range i,
      (∏ b ∈ Finset.Ico a i, (1 + 2 * H b)) * (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))
    have hpow_nn : 0 ≤ (2 * ctx.γ_ℓ) ^ i := by have := ctx.hγℓ; positivity
    have hcomb : ((ctx.C r).G i).norm1 ((ctx.C r).chainW (ctx.w r) i) +
          2 * (H i * ((ctx.C (ctx.repT i)).G i).norm1 ((ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i)) ≤
        (2 * ctx.γ_ℓ) ^ i * ((ctx.G0 r).norm1 (ctx.w r) +
          ∑ a ∈ Finset.range (i + 1),
            (∏ b ∈ Finset.Ico a (i + 1), (1 + 2 * H b)) *
              (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))) := by
      have hwrep_norm_nn : 0 ≤ (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hsum_succ :
          ∑ a ∈ Finset.range (i + 1),
            (∏ b ∈ Finset.Ico a (i + 1), (1 + 2 * H b)) *
              (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) =
          (1 + 2 * H i) * S_i +
            (1 + 2 * H i) * (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) := by
        rw [Finset.sum_range_succ]
        have hi_term : (∏ b ∈ Finset.Ico i (i + 1), (1 + 2 * H b)) *
            (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) =
            (1 + 2 * H i) * (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) := by
          simp [Nat.Ico_succ_singleton]
        have hpre : ∑ a ∈ Finset.range i,
            (∏ b ∈ Finset.Ico a (i + 1), (1 + 2 * H b)) *
              (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) =
            (1 + 2 * H i) * S_i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have hai : a ≤ i := Nat.le_of_lt (Finset.mem_range.mp ha)
          rw [Finset.prod_Ico_succ_top hai]
          ring
        rw [hi_term, hpre]
      rw [hsum_succ]
      have h1 : ((ctx.C r).G i).norm1 ((ctx.C r).chainW (ctx.w r) i) +
            2 * (H i * ((ctx.C (ctx.repT i)).G i).norm1
              ((ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i)) ≤
          (2 * ctx.γ_ℓ) ^ i * ((ctx.G0 r).norm1 (ctx.w r) + S_i) +
            2 * H i * ((2 * ctx.γ_ℓ) ^ i * ((ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) + S_i)) := by
        refine add_le_add hIH_r ?_
        rw [← mul_assoc 2 (H i)]
        exact mul_le_mul_of_nonneg_left hIH_rep (by positivity)
      have h2 : (2 * ctx.γ_ℓ) ^ i * ((ctx.G0 r).norm1 (ctx.w r) + S_i) +
            2 * H i * ((2 * ctx.γ_ℓ) ^ i * ((ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) + S_i)) ≤
          (2 * ctx.γ_ℓ) ^ i * ((ctx.G0 r).norm1 (ctx.w r) +
            ((1 + 2 * H i) * S_i +
              (1 + 2 * H i) * (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)))) := by
        have hdiff : (2 * ctx.γ_ℓ) ^ i * ((ctx.G0 r).norm1 (ctx.w r) +
              ((1 + 2 * H i) * S_i +
                (1 + 2 * H i) * (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)))) -
            ((2 * ctx.γ_ℓ) ^ i * ((ctx.G0 r).norm1 (ctx.w r) + S_i) +
              2 * H i * ((2 * ctx.γ_ℓ) ^ i *
                ((ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) + S_i))) =
            (2 * ctx.γ_ℓ) ^ i * (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) := by ring
        have hnonneg : 0 ≤ (2 * ctx.γ_ℓ) ^ i * (ctx.G0 (ctx.repT i)).norm1 (ctx.w (ctx.repT i)) :=
          mul_nonneg hpow_nn hwrep_norm_nn
        linarith
      exact le_trans h1 h2
    calc
      ((ctx.C r).G (i + 1)).norm1 ((ctx.C r).chainW (ctx.w r) (i + 1))
          ≤ 2 * ctx.γ_ℓ * ∑ e ∈ ((ctx.C r).G i).E,
              ((ctx.C r).activeLSF i).wstr e * (ctx.C r).chainW (ctx.w r) i e := hstep
      _ ≤ 2 * ctx.γ_ℓ * (((ctx.C r).G i).norm1 ((ctx.C r).chainW (ctx.w r) i) +
              2 * (H i * ((ctx.C (ctx.repT i)).G i).norm1
                ((ctx.C (ctx.repT i)).chainW (ctx.w (ctx.repT i)) i))) :=
          mul_le_mul_of_nonneg_left hsum_le (by have := ctx.hγℓ; positivity)
      _ ≤ 2 * ctx.γ_ℓ * ((2 * ctx.γ_ℓ) ^ i * ((ctx.G0 r).norm1 (ctx.w r) +
              ∑ a ∈ Finset.range (i + 1),
                (∏ b ∈ Finset.Ico a (i + 1), (1 + 2 * H b)) *
                  (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)))) :=
          mul_le_mul_of_nonneg_left hcomb (by have := ctx.hγℓ; positivity)
      _ = (2 * ctx.γ_ℓ) ^ (i + 1) * ((ctx.G0 r).norm1 (ctx.w r) +
              ∑ a ∈ Finset.range (i + 1),
                (∏ b ∈ Finset.Ico a (i + 1), (1 + 2 * H b)) *
                  (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))) := by
          rw [pow_succ']; ring

/-- **Lemma 6.2** (total width bound `eq:hintedTreeChainWidthBound`, page 25, line 556):
at stage `ctx.t`,
`∑_{i=0}^d ‖w^{(t), G_i}‖₁ ≤ (d + 1) (2 γ_ℓ)^d (‖w^{(t)}‖₁ + ∑_{a=0}^{d-1} (∏_{b=a}^{d-1} (1 + 2 hstr_b)) ‖w^{(repT_a)}‖₁)`. -/
theorem lemma_6_2 (ctx : RepQualityCtx) :
    ∑ i ∈ Finset.range (ctx.d + 1),
        ((ctx.C ctx.t).G i).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) i) ≤
      ((ctx.d : ℝ) + 1) * (2 * ctx.γ_ℓ) ^ ctx.d *
        ((ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
          ∑ a ∈ Finset.range ctx.d,
            (∏ b ∈ Finset.Ico a ctx.d,
              (1 + 2 * hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b
                ((ctx.C ctx.t).bran b))) *
              (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))) := by
  let H : ℕ → ℝ := fun b =>
    hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b)
  have hbase : (1 : ℝ) ≤ 2 * ctx.γ_ℓ := by linarith [ctx.hγℓ]
  have hterm : ∀ i ∈ Finset.range (ctx.d + 1),
      ((ctx.C ctx.t).G i).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) i) ≤
        (2 * ctx.γ_ℓ) ^ ctx.d *
          ((ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
            ∑ a ∈ Finset.range ctx.d,
              (∏ b ∈ Finset.Ico a ctx.d, (1 + 2 * H b)) *
                (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))) := by
    intro i hi
    have hi_le : i ≤ ctx.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hre_le_t : ctx.reinit i ≤ ctx.t := (ctx.hRep.1 i hi_le).1.trans (ctx.hRep.1 i hi_le).2
    have hIHi := lemma_6_2_inductive ctx i hi_le ctx.t hre_le_t (le_refl ctx.t)
    have hpow : (2 * ctx.γ_ℓ) ^ i ≤ (2 * ctx.γ_ℓ) ^ ctx.d := pow_le_pow_right₀ hbase hi_le
    have hsum_mono :
        ∑ a ∈ Finset.range i, (∏ b ∈ Finset.Ico a i, (1 + 2 * H b)) *
            (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) ≤
          ∑ a ∈ Finset.range ctx.d, (∏ b ∈ Finset.Ico a ctx.d, (1 + 2 * H b)) *
            (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) := by
      have hterm_le : ∑ a ∈ Finset.range i, (∏ b ∈ Finset.Ico a i, (1 + 2 * H b)) *
            (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) ≤
          ∑ a ∈ Finset.range i, (∏ b ∈ Finset.Ico a ctx.d, (1 + 2 * H b)) *
            (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) := by
        refine Finset.sum_le_sum fun a ha => ?_
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        have hai : a ≤ i := Nat.le_of_lt (Finset.mem_range.mp ha)
        have hsplit : Finset.Ico a ctx.d = Finset.Ico a i ∪ Finset.Ico i ctx.d :=
          (Finset.Ico_union_Ico_eq_Ico hai hi_le).symm
        have hdisj : Disjoint (Finset.Ico a i) (Finset.Ico i ctx.d) :=
          Finset.Ico_disjoint_Ico_consecutive a i ctx.d
        have hP1 : 0 ≤ ∏ b ∈ Finset.Ico a i, (1 + 2 * H b) :=
          Finset.prod_nonneg fun b hb => by
            linarith [hstrRep_nonneg ctx (lt_of_lt_of_le (Finset.mem_Ico.mp hb).2 hi_le)]
        have hP2 : 1 ≤ ∏ b ∈ Finset.Ico i ctx.d, (1 + 2 * H b) :=
          Finset.prod_induction (fun b => 1 + 2 * H b) (fun x => 1 ≤ x)
            (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl
            fun b hb => by linarith [hstrRep_nonneg ctx (Finset.mem_Ico.mp hb).2]
        rw [hsplit, Finset.prod_union hdisj]
        exact le_mul_of_one_le_right hP1 hP2
      refine le_trans hterm_le (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hi_le) fun a ha _ => ?_)
      refine mul_nonneg (Finset.prod_nonneg fun b hb => ?_) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      have hbd : b < ctx.d := (Finset.mem_Ico.mp hb).2
      linarith [hstrRep_nonneg ctx hbd]
    have hinner_nn : 0 ≤ (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
        ∑ a ∈ Finset.range ctx.d, (∏ b ∈ Finset.Ico a ctx.d, (1 + 2 * H b)) *
          (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) := by
      refine add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.sum_nonneg fun a _ => mul_nonneg (Finset.prod_nonneg fun b hb => ?_)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      have hbd : b < ctx.d := (Finset.mem_Ico.mp hb).2
      linarith [hstrRep_nonneg ctx hbd]
    have h1 : (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
          ∑ a ∈ Finset.range i, (∏ b ∈ Finset.Ico a i, (1 + 2 * H b)) *
            (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) ≤
        (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
          ∑ a ∈ Finset.range ctx.d, (∏ b ∈ Finset.Ico a ctx.d, (1 + 2 * H b)) *
            (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) := by linarith
    exact le_trans hIHi (mul_le_mul hpow h1 (by
      refine add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.sum_nonneg fun a ha => mul_nonneg (Finset.prod_nonneg fun b hb => ?_)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      have hbd : b < ctx.d := lt_of_lt_of_le (Finset.mem_Ico.mp hb).2 hi_le
      linarith [hstrRep_nonneg ctx hbd]) (by positivity))
  calc
    ∑ i ∈ Finset.range (ctx.d + 1),
        ((ctx.C ctx.t).G i).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) i)
        ≤ ∑ _i ∈ Finset.range (ctx.d + 1),
            (2 * ctx.γ_ℓ) ^ ctx.d *
              ((ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
                ∑ a ∈ Finset.range ctx.d,
                  (∏ b ∈ Finset.Ico a ctx.d, (1 + 2 * H b)) *
                    (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))) :=
          Finset.sum_le_sum hterm
    _ = ((ctx.d : ℝ) + 1) * (2 * ctx.γ_ℓ) ^ ctx.d *
          ((ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
            ∑ a ∈ Finset.range ctx.d,
              (∏ b ∈ Finset.Ico a ctx.d, (1 + 2 * H b)) *
                (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring

end Lemma6_2

section Corollary6_4_And_Lemma6_3

/-- **Corollary 6.4** (page 27, lines 688–705): at any stage where `C.Holds` holds and any
level `i < C.d`, the uniform average of `hstr_{i, j}` over `j < C.k` is at most `σ_mwu`, so
there exists a branch `j < C.k` with `hstr_{i, j} ≤ σ_mwu`. -/
theorem corollary_6_4 {C : TreeChain} {G : MGraph} {ℓ w : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hw : ∀ e ∈ G.E, 0 ≤ w e) (hσ_mwu_nn : 0 ≤ σ_mwu)
    {i : ℕ} (hi : i < C.d) :
    (∑ j ∈ Finset.range C.k, hstrAt C w i j) / (C.k : ℝ) ≤ σ_mwu ∧
    ∃ j < C.k, hstrAt C w i j ≤ σ_mwu := by
  have hk_pos : (0 : ℝ) < C.k := Nat.cast_pos.mpr hH.2.2.1
  have hvp0 : IsValidPair G ℓ (fun _ => 0) w :=
    ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using hw e he⟩
  have hci := C.chain_isValidPair hH hSub hℓ hvp0 i (Nat.le_of_lt hi)
  have hwi_nn : ∀ e ∈ (C.G i).E, 0 ≤ C.chainW w i e := fun e he =>
    le_trans (abs_nonneg _) (hci.1.2 e he)
  have havg : (∑ j ∈ Finset.range C.k, hstrAt C w i j) / (C.k : ℝ) ≤ σ_mwu := by
    unfold hstrAt
    by_cases hden : (C.G i).norm1 (C.chainW w i) = 0
    · simp [hden, hσ_mwu_nn]
    · have hden_pos : 0 < (C.G i).norm1 (C.chainW w i) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Ne.symm hden)
      simp only [hden, ↓reduceIte]
      have hmwu := (hH.2.2.2.2.1 i hi).2.2.1
      have hsum_eq :
          (∑ j ∈ Finset.range C.k,
            (∑ e ∈ (C.G i).E, (C.lsfs i j).wstr e * C.chainW w i e) /
              (C.G i).norm1 (C.chainW w i)) / (C.k : ℝ) =
          (∑ e ∈ (C.G i).E,
            ((∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr e) / (C.k : ℝ)) *
              C.chainW w i e) / (C.G i).norm1 (C.chainW w i) := by
        simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
        rw [Finset.sum_comm]
        have hinner : ∑ e ∈ (C.G i).E, ∑ j ∈ Finset.range C.k,
              (C.lsfs i j).wstr e * C.chainW w i e =
            ∑ e ∈ (C.G i).E, (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr e) *
              C.chainW w i e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.sum_mul]
        rw [hinner, Finset.sum_mul, Finset.sum_mul]
        rw [show (∑ x ∈ (C.G i).E, (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr x) * (↑C.k)⁻¹ *
            C.chainW w i x) * ((C.G i).norm1 (C.chainW w i))⁻¹ =
            ∑ x ∈ (C.G i).E, (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr x) * (↑C.k)⁻¹ *
              C.chainW w i x * ((C.G i).norm1 (C.chainW w i))⁻¹ by rw [Finset.sum_mul]]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
      rw [hsum_eq, div_le_iff₀ hden_pos]
      have hden_abs : (C.G i).norm1 (C.chainW w i) = ∑ e ∈ (C.G i).E, C.chainW w i e := by
        unfold MGraph.norm1
        refine Finset.sum_congr rfl fun e he => abs_of_nonneg (hwi_nn e he)
      rw [hden_abs, Finset.mul_sum]
      refine Finset.sum_le_sum fun e he => ?_
      exact mul_le_mul_of_nonneg_right (hmwu e he) (hwi_nn e he)
  refine ⟨havg, ?_⟩
  by_contra hno
  push Not at hno
  have hgt : (C.k : ℝ) * σ_mwu < ∑ j ∈ Finset.range C.k, hstrAt C w i j := by
    have hlt_sum : ∑ _j ∈ Finset.range C.k, σ_mwu < ∑ j ∈ Finset.range C.k, hstrAt C w i j :=
      Finset.sum_lt_sum (fun j hj => (hno j (Finset.mem_range.mp hj)).le)
        ⟨0, Finset.mem_range.mpr hH.2.2.1, hno 0 hH.2.2.1⟩
    simpa [Finset.sum_const, nsmul_eq_mul] using hlt_sum
  have : σ_mwu < (∑ j ∈ Finset.range C.k, hstrAt C w i j) / (C.k : ℝ) :=
    (lt_div_iff₀ hk_pos).mpr (by linarith)
  linarith

/-- Explicit quality ratio factor `κ` for **Lemma 6.3** (pages 26–27) and **Theorem 5.1**:
`κ = 1 / ((σ_tot + 1) * (d + 1) * (2d + 3) * (2 γ_ℓ (1 + 2 σ_mwu))^d)`. -/
noncomputable def kappaBound (d : ℕ) (γ_ℓ σ_tot σ_mwu_max : ℝ) : ℝ :=
  1 / ((σ_tot + 1) * (((d : ℝ) + 1) * (2 * (d : ℝ) + 3) *
    (2 * γ_ℓ * (1 + 2 * σ_mwu_max)) ^ d))

lemma kappaBound_pos {d : ℕ} {γ_ℓ σ_tot σ_mwu_max : ℝ}
    (hγ : 1 ≤ γ_ℓ) (hσ : 0 ≤ σ_tot) (hσ_mwu : 0 ≤ σ_mwu_max) :
    0 < kappaBound d γ_ℓ σ_tot σ_mwu_max := by
  unfold kappaBound
  have h1 : 0 < 2 * γ_ℓ * (1 + 2 * σ_mwu_max) := by positivity
  have h2 : 0 < σ_tot + 1 := by linarith
  have h3 : 0 < ((d : ℝ) + 1) * (2 * (d : ℝ) + 3) := by positivity
  positivity

/-- Witness-norm drop condition (`eq:dsBadWtSum`, page 26, line 640):
`∑_{i=0}^d ‖w^{(repT_i)}‖₁ > 2 (d + 1) ‖w^{(t)}‖₁`. -/
def BadNormCond (d : ℕ) (W : ℕ → ℝ) (repT : ℕ → ℕ) (t : ℕ) : Prop :=
  2 * ((d : ℝ) + 1) * W t < ∑ i ∈ Finset.range (d + 1), W (repT i)

/-- Bad current-stretch condition (`eq:dsBadStr`, page 26, line 645):
some level `i < d` has `hstr_{i, bran_i} > σ_mwu_max`. -/
def BadHstrCond (ctx : RepQualityCtx) (σ_mwu_max : ℝ) : Prop :=
  ∃ i < ctx.d,
    σ_mwu_max < hstrAt (ctx.C (ctx.repT i)) (ctx.w (ctx.repT i)) i ((ctx.C ctx.t).bran i)

/-- **Lemma 6.3** (pages 26–27, lines 622–673):
At stage `t = ctx.t`, if `algorithm1_findCycle st` (with `st.toTreeChain = ctx.C ctx.t`,
`st.g = g_t`, `st.ℓ = ctx.ℓ0 ctx.t`) fails to achieve ratio `κ α`, then either:
* `BadNormCond`: `∑_{i=0}^d ‖w^{(repT_i)}‖₁ > 2 (d + 1) ‖w^{(t)}‖₁`, or
* `BadHstrCond`: some level `i < d` has `hstr_{i, bran_i} > σ_mwu_max`.

Crucially, Definition 4.4 item 3 (`⟨g^{(t)}, c^{(t)}⟩ / ‖w^{(t)}‖₁ ≤ -α`) is assumed **only**
at level `0` at stage `t` (hypothesis `hItem3`), never at lower levels `i ≥ 1` or past times. -/
theorem lemma_6_3 {T : SparseCoreRestartTool} {P : ChainParams} (ctx : RepQualityCtx)
    (st : ChainState T P) (hChainEq : st.toTreeChain = ctx.C ctx.t)
    {g_t c_t : ℕ → ℝ} (hgEq : st.g = g_t) (hℓEq : st.ℓ = ctx.ℓ0 ctx.t)
    {σ_tot σ_mwu_max α : ℝ}
    (hσ_le : ctx.σ ≤ σ_tot) (hσ_nn : 0 ≤ σ_tot) (hσ_mwu_nn : 0 ≤ σ_mwu_max)
    (hα : 0 < α)
    (hℓPos : ∀ e ∈ (st.G 0).E, 0 < st.ℓ e)
    (hSpan : st.toTreeChain.LastLevelSpans)
    (hEmbSurv : st.toTreeChain.EmbedsSurviving)
    (hvp_t : IsValidPair (ctx.G0 ctx.t) (ctx.ℓ0 ctx.t) c_t (ctx.w ctx.t))
    (hItem3 : (ctx.G0 ctx.t).inner g_t c_t / (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) ≤ -α) :
    let Δ := (algorithm1_findCycle st).1
    let κ := kappaBound ctx.d ctx.γ_ℓ σ_tot σ_mwu_max
    ((ctx.G0 ctx.t).inner g_t Δ / (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) Δ > -(κ * α)) →
    BadNormCond ctx.d (fun r => (ctx.G0 r).norm1 (ctx.w r)) ctx.repT ctx.t ∨
      BadHstrCond ctx σ_mwu_max := by
  dsimp only
  set κ := kappaBound ctx.d ctx.γ_ℓ σ_tot σ_mwu_max
  set Δ := (algorithm1_findCycle st).1
  intro hBadRatio
  by_contra hNeither
  rw [not_or] at hNeither
  rcases hNeither with ⟨hNoNorm, hNoHstr⟩
  unfold BadNormCond at hNoNorm
  unfold BadHstrCond at hNoHstr
  push Not at hNoNorm hNoHstr
  have htWin := ctx.hWindow ctx.d (le_refl ctx.d) ctx.t
    (ctx.hRep.1 ctx.d (le_refl ctx.d) |>.1.trans (ctx.hRep.1 ctx.d (le_refl ctx.d) |>.2))
    (le_refl ctx.t)
  have hG0_eq : st.G 0 = ctx.G0 ctx.t := by
    have h1 : st.G 0 = (ctx.C ctx.t).G 0 := by rw [← hChainEq]; rfl
    rw [h1, htWin.2.2.1.1]
  have hH_st : st.toTreeChain.Holds (st.G 0) st.ℓ σ_tot ctx.σ_mwu ctx.γ_ℓ ctx.γ_c := by
    rw [hChainEq, hG0_eq, hℓEq]
    have hH0 := htWin.2.2.1
    refine ⟨hH0.1, hH0.2.1, hH0.2.2.1, hH0.2.2.2.1, fun i hi => ?_, hH0.2.2.2.2.2.1,
      fun j hj => ?_, hH0.2.2.2.2.2.2.2⟩
    · rcases hH0.2.2.2.2.1 i hi with ⟨hb, hls, hmwu, hs⟩
      exact ⟨hb, fun j hj => ⟨LSF.Holds.mono_σ (hls j hj).1 hσ_le, (hls j hj).2⟩, hmwu, hs⟩
    · exact LSF.Holds.mono_σ (hH0.2.2.2.2.2.2.1 j hj) hσ_le
  have hvp_st : IsValidPair (st.G 0) st.ℓ c_t (ctx.w ctx.t) := by
    rwa [hG0_eq, hℓEq]
  have hFC := findCycle_spec_of_holds st ctx.hγℓ hℓPos hH_st hSpan hEmbSurv hvp_st
  have hW_t_pos : 0 < (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
    by_contra hle
    have h0 : (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) = 0 :=
      le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    rw [h0, div_zero] at hItem3
    linarith
  have hInner_c_le : (ctx.G0 ctx.t).inner g_t c_t ≤
      -(α * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t)) := by
    have := (div_le_iff₀ hW_t_pos).mp hItem3
    linarith
  have hAbs_c : α * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) ≤ |(ctx.G0 ctx.t).inner g_t c_t| := by
    rw [abs_of_nonpos (by nlinarith)]
    linarith
  have hInner_c_ne0 : (ctx.G0 ctx.t).inner g_t c_t ≠ 0 := by
    have : 0 < α * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := mul_pos hα hW_t_pos
    linarith
  have hOptSome : ∃ e, (algorithm1_findCycle st).2.2 = some e := by
    rcases Option.eq_none_or_eq_some (algorithm1_findCycle st).2.2 with hOpt | ⟨e, he⟩
    · have hnc : (st.G 0).inner st.g c_t = 0 := (hFC.2.2.2.1 hOpt).2.2
      rw [hG0_eq, hgEq] at hnc
      exact absurd hnc hInner_c_ne0
    · exact ⟨e, he⟩
  obtain ⟨e, he⟩ := hOptSome
  have hGood := hFC.2.2.2.2 e he
  have hΔnorm_pos : 0 < (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) Δ := by
    rw [← hG0_eq, ← hℓEq]
    exact hGood.2.1
  have hΔinner_le0 : (ctx.G0 ctx.t).inner g_t Δ ≤ 0 := by
    rw [← hG0_eq, ← hgEq]
    exact hFC.2.1
  have hW62 := lemma_6_2 ctx
  have hProd_le : ∀ a ∈ Finset.range ctx.d,
      ∏ b ∈ Finset.Ico a ctx.d,
          (1 + 2 * hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b)) ≤
        (1 + 2 * σ_mwu_max) ^ ctx.d := by
    intro a _
    have hbase1 : 1 ≤ 1 + 2 * σ_mwu_max := by linarith
    calc
      ∏ b ∈ Finset.Ico a ctx.d,
          (1 + 2 * hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b))
          ≤ ∏ _b ∈ Finset.Ico a ctx.d, (1 + 2 * σ_mwu_max) :=
        Finset.prod_le_prod₀
          (fun b hb => by linarith [hstrRep_nonneg ctx (Finset.mem_Ico.mp hb).2])
          (fun b hb => by linarith [hNoHstr b (Finset.mem_Ico.mp hb).2])
      _ = (1 + 2 * σ_mwu_max) ^ (ctx.d - a) := by simp
      _ ≤ (1 + 2 * σ_mwu_max) ^ ctx.d := pow_le_pow_right₀ hbase1 (Nat.sub_le ctx.d a)
  have hSum_rep_le :
      ∑ a ∈ Finset.range ctx.d, (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) ≤
        2 * ((ctx.d : ℝ) + 1) * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
    have hsub : Finset.range ctx.d ⊆ Finset.range (ctx.d + 1) := Finset.range_mono (Nat.le_succ _)
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) hNoNorm
  have hpow_σ_ge1 : (1 : ℝ) ≤ (1 + 2 * σ_mwu_max) ^ ctx.d :=
    one_le_pow₀ (by linarith)
  have hW_bound :
      ∑ i ∈ Finset.range ((ctx.C ctx.t).d + 1),
          ((ctx.C ctx.t).G i).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) i) ≤
        ((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
          (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d *
          (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
    rw [htWin.1]
    have hs1 : ∑ a ∈ Finset.range ctx.d,
        (∏ b ∈ Finset.Ico a ctx.d,
          (1 + 2 * hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b))) *
          (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) ≤
        (1 + 2 * σ_mwu_max) ^ ctx.d *
          (2 * ((ctx.d : ℝ) + 1) * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t)) := by
      calc
        ∑ a ∈ Finset.range ctx.d,
            (∏ b ∈ Finset.Ico a ctx.d,
              (1 + 2 * hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b))) *
              (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a))
            ≤ ∑ a ∈ Finset.range ctx.d,
                (1 + 2 * σ_mwu_max) ^ ctx.d *
                  (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          exact mul_le_mul_of_nonneg_right (hProd_le a ha) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        _ = (1 + 2 * σ_mwu_max) ^ ctx.d *
              ∑ a ∈ Finset.range ctx.d, (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) := by
          rw [← Finset.mul_sum]
        _ ≤ (1 + 2 * σ_mwu_max) ^ ctx.d *
              (2 * ((ctx.d : ℝ) + 1) * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t)) :=
          mul_le_mul_of_nonneg_left hSum_rep_le (by positivity)
    have hinner : (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) +
        ∑ a ∈ Finset.range ctx.d,
          (∏ b ∈ Finset.Ico a ctx.d,
            (1 + 2 * hstrAt (ctx.C (ctx.repT b)) (ctx.w (ctx.repT b)) b ((ctx.C ctx.t).bran b))) *
            (ctx.G0 (ctx.repT a)).norm1 (ctx.w (ctx.repT a)) ≤
        (2 * (ctx.d : ℝ) + 3) * (1 + 2 * σ_mwu_max) ^ ctx.d *
          (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
      have h1 : (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) ≤
          (1 + 2 * σ_mwu_max) ^ ctx.d * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
        nlinarith [hW_t_pos]
      nlinarith
    have h2 : ((ctx.d : ℝ) + 1) * (2 * ctx.γ_ℓ) ^ ctx.d *
          ((2 * (ctx.d : ℝ) + 3) * (1 + 2 * σ_mwu_max) ^ ctx.d *
            (ctx.G0 ctx.t).norm1 (ctx.w ctx.t)) =
        ((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
          (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d *
          (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
      rw [mul_pow (2 * ctx.γ_ℓ) (1 + 2 * σ_mwu_max) ctx.d]
      ring
    calc
      ∑ i ∈ Finset.range (ctx.d + 1),
          ((ctx.C ctx.t).G i).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) i)
          ≤ ((ctx.d : ℝ) + 1) * (2 * ctx.γ_ℓ) ^ ctx.d *
              ((ctx.G0 ctx.t).norm1 (ctx.w ctx.t) + _) := hW62
      _ ≤ ((ctx.d : ℝ) + 1) * (2 * ctx.γ_ℓ) ^ ctx.d *
            ((2 * (ctx.d : ℝ) + 3) * (1 + 2 * σ_mwu_max) ^ ctx.d *
              (ctx.G0 ctx.t).norm1 (ctx.w ctx.t)) :=
          mul_le_mul_of_nonneg_left hinner (by have := ctx.hγℓ; positivity)
      _ = _ := h2
  set Wtot := ∑ i ∈ Finset.range ((ctx.C ctx.t).d + 1),
    ((ctx.C ctx.t).G i).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) i)
  have hWtot_eq : ∑ i ∈ Finset.range (st.toTreeChain.d + 1),
      (st.toTreeChain.G i).norm1 (st.toTreeChain.chainW (ctx.w ctx.t) i) = Wtot := by
    rw [hChainEq]
  have hW_bound_pos : 0 < ((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
      (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d *
      (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
    have := ctx.hγℓ
    positivity
  have hWtot_pos : 0 < Wtot := by
    have he0 : 0 ∈ Finset.range ((ctx.C ctx.t).d + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
    have h0le := Finset.single_le_sum (f := fun i =>
      ((ctx.C ctx.t).G i).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) i))
      (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) he0
    have h0eq : ((ctx.C ctx.t).G 0).norm1 ((ctx.C ctx.t).chainW (ctx.w ctx.t) 0) =
        (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
      rw [htWin.2.2.1.1]; simp [TreeChain.chainW]
    linarith
  have hdiv_ge : κ * α ≤
      |(ctx.G0 ctx.t).inner g_t Δ| / (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) Δ := by
    have hGoodRatio : (1 / (σ_tot + 1)) * (|(ctx.G0 ctx.t).inner g_t c_t| / Wtot) ≤
        |(ctx.G0 ctx.t).inner g_t Δ| / (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) Δ := by
      rw [← hG0_eq, ← hgEq, ← hℓEq, ← hWtot_eq]
      exact hGood.2.2
    have hlower : κ * α ≤ (1 / (σ_tot + 1)) * (|(ctx.G0 ctx.t).inner g_t c_t| / Wtot) := by
      have h1 : α / (((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
            (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d) ≤
          |(ctx.G0 ctx.t).inner g_t c_t| / Wtot := by
        rw [div_le_div_iff₀ (by have := ctx.hγℓ; positivity) hWtot_pos]
        calc
          α * Wtot ≤ α * (((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
                (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d *
                (ctx.G0 ctx.t).norm1 (ctx.w ctx.t)) :=
            mul_le_mul_of_nonneg_left hW_bound hα.le
          _ = (α * (ctx.G0 ctx.t).norm1 (ctx.w ctx.t)) *
                (((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
                  (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d) := by ring
          _ ≤ |(ctx.G0 ctx.t).inner g_t c_t| *
                (((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
                  (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d) :=
            mul_le_mul_of_nonneg_right hAbs_c (by have := ctx.hγℓ; positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 / (σ_tot + 1) by positivity)
      have heqκ : κ * α = (1 / (σ_tot + 1)) * (α / (((ctx.d : ℝ) + 1) * (2 * (ctx.d : ℝ) + 3) *
          (2 * ctx.γ_ℓ * (1 + 2 * σ_mwu_max)) ^ ctx.d)) := by
        unfold κ kappaBound
        have := ctx.hγℓ
        field_simp
      linarith
    exact le_trans hlower hGoodRatio
  rw [abs_of_nonpos hΔinner_le0, neg_div] at hdiv_ge
  linarith

end Corollary6_4_And_Lemma6_3

end MinCostFlow.Chain
