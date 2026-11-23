module

public import MinCostFlow.DynSpanner.Program.DynSpannerDSDefs

import MinCostFlow.DynSpanner.Correctness
import MinCostFlow.DynSpanner.Program.DynSpannerSpaceStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Heap-space bounds for the dynamic spanner update (`DynSpannerSpace`)

Bounds the heap space `dsUpdateLoopSpace` (`DynSpannerUpdateLoopDefs.lean`) and
`dsUpdateOpSpace` (`DynSpannerDSDefs.lean`) of one batch update of the dynamic spanner
(Algorithm 6, Theorem 8.2) in terms of:
* the caps and batch size `B = vCap + eCap + L + W + 2`,
* the static-sparsifier walk-stretch bound `g = ⌈impl.γ_ℓ mMax⌉₊`,
* the dynamic-spanner walk-length bound `W_len = ⌈lenBound (impl.γ_ℓ mMax) L⌉₊`
  (`Claim 5.8`, `DynSpanner/Correctness.lean`), and
* the guest word-size exponent `impl.cw`.

Main results:
* `dsHist_piTotal_length_le`: every edge walk `piTotal (d.state P) e` of a valid history has
  length at most `⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊`.
* `dsStepSpaceAt_le_caps`: every single update step (`j = 0` or `0 < j`) uses at most
  `2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len` heap words.
* `dsUpdateLoopSpace_le_caps` and `dsUpdateOpSpace_le_caps`: the batch update uses at most
  `2 * B * (180 * B * W_len) ^ impl.cw + 450 * B ^ 3 * g * W_len` heap words.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

/-! ## Helpers -/

private lemma list_getD_le_sum : ∀ (l : List ℕ) (r : ℕ), l.getD r 0 ≤ l.sum
  | [], _ => by simp
  | x :: xs, 0 => by simp
  | x :: xs, r + 1 => by
    have ih := list_getD_le_sum xs r
    simp only [List.getD_cons_succ, List.sum_cons]
    omega

private lemma card_le_cap_of_lt {E : Finset ℕ} {c : ℕ} (h : ∀ e ∈ E, e < c) : E.card ≤ c :=
  (Finset.card_le_card fun e he => Finset.mem_range.mpr (h e he)).trans (Finset.card_range c).le

private lemma batch_length_le_m_add_splits :
    ∀ {G : MGraph} {U : List Update}, G.BatchIsValid U → (∀ u ∈ U, isDelOrSplit u) →
      U.length ≤ G.m + batchSplitCount U
  | _, [], _, _ => by simp [batchSplitCount]
  | G, u :: rest, ⟨hu, hrest⟩, hds => by
    have hu1 := hds u List.mem_cons_self
    have ih := batch_length_le_m_add_splits hrest fun x hx => hds x (List.mem_cons_of_mem _ hx)
    cases u with
    | insert _ _ _ => cases hu1
    | delete e =>
      have hm : (G.applyUpdate (.delete e)).m + 1 = G.m := by
        simp only [MGraph.m, MGraph.applyUpdate]
        exact Finset.card_erase_add_one hu
      simp only [List.length_cons, batchSplitCount, List.countP_cons, isSplit] at ih ⊢
      omega
    | split v v' St Sh =>
      have hm : (G.applyUpdate (.split v v' St Sh)).m = G.m := rfl
      simp only [List.length_cons, batchSplitCount, List.countP_cons, isSplit, ↓reduceIte] at ih ⊢
      omega

/-! ## Walk-length bound on `piTotal` for a valid history -/

public section

/-- Every edge walk `piTotal (d.state P) e` of a valid dynamic spanner history has length at most
`⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊` (`Claim 5.8`, `DynSpanner/Correctness.lean`). -/
theorem dsHist_piTotal_length_le (P : DSParams) {d : DSHist}
    (hL : 1 ≤ P.L) (hVG₀ : d.G₀.IsValid) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hBV : d.G₀.BatchIsValid d.flat) (hds : ∀ u ∈ d.flat, isDelOrSplit u)
    {e : ℕ} (he : e ∈ (d.state P).G.E) :
    (piTotal (d.state P) e).length ≤ ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊ := by
  have hq : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hSpec := canonicalSparsify_spec_absorb P.impl P.mMax
  have hInv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds d.flat.length le_rfl).1
  have he' : e ∈ (d.G₀.applyBatch (d.flat.take d.flat.length)).E := by
    rw [← hInv.G_eq]; exact he
  have hlen := claim_5_8 hVG₀ hL hq hGm₀ hSpec hBV hds (k := d.flat.length) le_rfl
    ⟨P.L, Nat.lt_succ_self P.L⟩
  have hle : (piTotal (d.state P) e).length ≤
      Embedding.length (piLe (d.state P) P.L) (d.G₀.applyBatch (d.flat.take d.flat.length)) :=
    Finset.le_sup (f := fun x => (piLe (d.state P) P.L x).length) he'
  have hcast : ((piTotal (d.state P) e).length : ℝ) ≤ lenBound (P.impl.γ_ℓ P.mMax) P.L :=
    le_trans (Nat.cast_le.mpr hle) hlen
  exact nat_le_ceil_of_cast_le hcast

/-! ## Bounds for `dsStepSpaceAt`, `dsUpdateLoopSpace`, and `dsUpdateOpSpace` -/

/-- **Per-step heap space bound of Algorithm 6.** For any valid history `us` of deletions and
splits from `G₀`, every step `k` uses at most
`2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len` heap words, where
`B = vCap + eCap + L + len + 2`, `g = ⌈impl.γ_ℓ mMax⌉₊`, and `W_len = ⌈lenBound (impl.γ_ℓ mMax) L⌉₊`. -/
theorem dsStepSpaceAt_le_caps {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax L q vCap eCap k len : ℕ} {us : List Update}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hGm_e : G₀.m ≤ eCap) (hGn_v : G₀.n + batchSplitCount us ≤ vCap)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') :
    let B := vCap + eCap + L + len + 2
    let g := ⌈impl.γ_ℓ mMax⌉₊
    let W_len := ⌈lenBound (impl.γ_ℓ mMax) L⌉₊
    dsStepSpaceAt G₀ impl mMax L q vCap eCap us k len ≤
      2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len := by
  intro B g W_len
  unfold dsStepSpaceAt
  cases hk : us[k]? with
  | none =>
    simp only
    have hB2 : 2 ≤ B := by omega
    have hg1 : 1 ≤ g := one_le_ceil_gamma impl mMax
    have hW1 : 1 ≤ W_len := one_le_ceil_lenBound impl mMax L
    have h1 : 4 ≤ B ^ 2 * g * W_len := by
      have h4 : 4 ≤ B ^ 2 := by nlinarith
      calc 4 ≤ B ^ 2 := h4
        _ = B ^ 2 * 1 * 1 := by ring
        _ ≤ B ^ 2 * g * W_len := Nat.mul_le_mul (Nat.mul_le_mul_left _ hg1) hW1
    have h400 : 400 * B ^ 2 * g * W_len = 400 * (B ^ 2 * g * W_len) := by ring
    omega
  | some u =>
    dsimp only
    split_ifs with hj0
    · have hklt : k < us.length := (List.getElem?_eq_some_iff.mp hk).1
      have hSpec := canonicalSparsify_spec_absorb impl mMax
      have hInv0 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (le_of_lt hklt)).1
      have hG'sub := runStep_G'_E_sub (impl := impl) (mMax := mMax) (L := L) (q := q)
        hVG₀ hL hq hGm₀ hBV hds hk
      have hG'm : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).m ≤ eCap :=
        (Finset.card_le_card hG'sub).trans hGm_e
      have hG'eq : (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u =
          G₀.applyBatch (us.take (k + 1)) := by
        have htk : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hk
        rw [htk, applyBatch_append, ← hInv0.G_eq]; rfl
      have htk1 := batchIsValid_take us G₀ (k + 1) hBV hds
      have hG'V : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).IsValid := by
        rw [hG'eq]; exact (batch_delOrSplit_invariants _ G₀ hVG₀ htk1.1 htk1.2.1).1
      have hG'n : ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).n ≤ vCap := by
        rw [hG'eq, n_applyBatch_of_delOrSplit _ _ htk1.1 htk1.2.1]
        have hsc : batchSplitCount (us.take (k + 1)) ≤ batchSplitCount us := by
          have h1 : us = us.take (k + 1) ++ us.drop (k + 1) := (List.take_append_drop _ _).symm
          conv_rhs => rw [h1]
          simp only [batchSplitCount, List.countP_append]; omega
        omega
      have hHo : (runState (L := L) G₀ q (canonicalSparsify impl) us k).H.m ≤ eCap := by
        have htk0 := batchIsValid_take us G₀ k hBV hds
        have hsub : (runState (L := L) G₀ q (canonicalSparsify impl) us k).H.E ⊆ G₀.E :=
          hInv0.H_sub.2.1.trans (batch_delOrSplit_invariants _ G₀ hVG₀ htk0.1 htk0.2.1).2.1
        exact (Finset.card_le_card hsub).trans hGm_e
      have hHn : (initCore ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u)
          (canonicalSparsify impl)).1.m ≤ eCap := by
        have hi := initCore_spec hSpec hG'V ((Finset.card_le_card hG'sub).trans hGm₀)
        exact (Finset.card_le_card (hi.2.1.2.1.trans hG'sub)).trans hGm_e
      exact dsStepZeroSpace_le_caps hG'n hG'm hHo hHn
    · exact dsStepPosSpaceAt_le_caps hVG₀ hL hq hGm₀ hGm_e hGn_v hBV hds hk (by omega)

/-- **Heap space bound for `dsUpdateLoopSpace`.** With `B = vCap + eCap + L + W + 2`,
`g = ⌈impl.γ_ℓ mMax⌉₊`, and `W_len = ⌈lenBound (impl.γ_ℓ mMax) L⌉₊`, the loop space for a batch
`U` of length `≤ vCap + eCap` and word sum `lens.sum ≤ W` is at most
`2 * B * (180 * B * W_len) ^ impl.cw + 449 * B ^ 3 * g * W_len`. -/
theorem dsUpdateLoopSpace_le_caps {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax L q vCap eCap W k₀ : ℕ} {us U : List Update} {lens : List ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hGm_e : G₀.m ≤ eCap) (hGn_v : G₀.n + batchSplitCount us ≤ vCap)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hUlen : U.length ≤ vCap + eCap) (hlens : lens.sum ≤ W) :
    let B := vCap + eCap + L + W + 2
    let g := ⌈impl.γ_ℓ mMax⌉₊
    let W_len := ⌈lenBound (impl.γ_ℓ mMax) L⌉₊
    dsUpdateLoopSpace G₀ impl mMax L q vCap eCap us U lens k₀ ≤
      2 * B * (180 * B * W_len) ^ impl.cw + 449 * B ^ 3 * g * W_len := by
  intro B g W_len
  have hB2 : 2 ≤ B := by omega
  have hg1 : 1 ≤ g := one_le_ceil_gamma impl mMax
  have hW1 : 1 ≤ W_len := one_le_ceil_lenBound impl mMax L
  have hB_B3 : B ≤ B ^ 3 := Nat.le_self_pow (by decide) B
  have hB2_B3 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hB3_gW : B ^ 3 ≤ B ^ 3 * g * W_len := by
    calc B ^ 3 = B ^ 3 * 1 * 1 := by ring
      _ ≤ B ^ 3 * g * W_len := Nat.mul_le_mul (Nat.mul_le_mul_left _ hg1) hW1
  have hU_B : U.length ≤ B := by omega
  have hstep : ∑ r ∈ Finset.range U.length,
      (dsStepSpaceAt G₀ impl mMax L q vCap eCap us (k₀ + r) (lens.getD r 0) + 7) ≤
      B * (2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len + 7) := by
    calc _ ≤ ∑ _r ∈ Finset.range U.length,
          (2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len + 7) := by
          refine Finset.sum_le_sum fun r _ => Nat.add_le_add_right ?_ 7
          have hlr : lens.getD r 0 ≤ W := (list_getD_le_sum lens r).trans hlens
          have hBr : vCap + eCap + L + lens.getD r 0 + 2 ≤ B := by omega
          refine (dsStepSpaceAt_le_caps (k := k₀ + r) (len := lens.getD r 0)
            hVG₀ hL hq hGm₀ hGm_e hGn_v hBV hds).trans ?_
          exact Nat.add_le_add
            (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left
              (Nat.mul_le_mul_right W_len (Nat.mul_le_mul_left 180 hBr)) _))
            (Nat.mul_le_mul_right W_len (Nat.mul_le_mul_right g
              (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left hBr 2))))
      _ = U.length * (2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len + 7) := by simp
      _ ≤ B * (2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len + 7) :=
          Nat.mul_le_mul_right _ hU_B
  have hD : ∑ r ∈ Finset.range U.length,
      (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).D.card ≤ B ^ 2 := by
    calc _ ≤ ∑ _r ∈ Finset.range U.length, B :=
          Finset.sum_le_sum fun r _ =>
            (runStep_D_card_le hVG₀ hL hq hGm₀ hBV hds).trans (hGm_e.trans (by omega))
      _ = U.length * B := by simp
      _ ≤ B * B := Nat.mul_le_mul_right B hU_B
      _ = B ^ 2 := (sq B).symm
  have hR : ∑ r ∈ Finset.range U.length,
      (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).card ≤ B ^ 2 := by
    calc _ ≤ ∑ _r ∈ Finset.range U.length, B :=
          Finset.sum_le_sum fun r _ =>
            (runStep_reemb_card_le hVG₀ hL hq hGm₀ hBV hds).trans (hGm_e.trans (by omega))
      _ = U.length * B := by simp
      _ ≤ B * B := Nat.mul_le_mul_right B hU_B
      _ = B ^ 2 := (sq B).symm
  have hUH : ∑ r ∈ Finset.range U.length,
      (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).UH.length ≤ 3 * B ^ 2 := by
    calc _ ≤ ∑ _r ∈ Finset.range U.length, (3 * B) :=
          Finset.sum_le_sum fun r _ =>
            (runStep_UH_length_le hVG₀ hL hq hGm₀ hBV hds).trans (by omega)
      _ = U.length * (3 * B) := by simp
      _ ≤ B * (3 * B) := Nat.mul_le_mul_right _ hU_B
      _ = 3 * B ^ 2 := by ring
  unfold dsUpdateLoopSpace
  have he1 : B * (2 * (180 * B * W_len) ^ impl.cw + 400 * B ^ 2 * g * W_len + 7) =
      2 * B * (180 * B * W_len) ^ impl.cw + 400 * B ^ 3 * g * W_len + 7 * B := by ring
  have htail : 7 + U.length + 7 * B + 2 * B ^ 2 + 2 * B ^ 2 + 1 + 2 * (W + 4 * (3 * B ^ 2)) ≤
      49 * B ^ 3 * g * W_len := by
    have h1 : 7 + U.length + 7 * B + 1 + 2 * W ≤ 14 * B := by omega
    have h2 : 14 * B + 28 * B ^ 2 ≤ 42 * B ^ 3 := by omega
    have h3 : 42 * B ^ 3 ≤ 49 * B ^ 3 * g * W_len := by
      have : 42 * B ^ 3 ≤ 49 * B ^ 3 := Nat.mul_le_mul_right _ (by decide)
      calc 42 * B ^ 3 ≤ 49 * B ^ 3 := this
        _ ≤ 49 * (B ^ 3 * g * W_len) := Nat.mul_le_mul_left 49 hB3_gW
        _ = 49 * B ^ 3 * g * W_len := by ring
    omega
  linarith

/-- **Heap space bound for `dsUpdateOpSpace`.** For a dynamic spanner history `d` and update batch
`U = (opBatch P d [b, batchPtr, W, h] mem).1` with encoded word length sum `lens.sum ≤ W`, if
`d.flat ++ U` is a valid deletion/split sequence within `P.splitBound` and `d.G₀` fits in
`(P.vCap, P.eCap, P.mMax)`, then
`dsUpdateOpSpace P d [b, batchPtr, W, h] mem ≤ 2 * B * (180 * B * W_len) ^ P.impl.cw + 450 * B ^ 3 * g * W_len`,
where `B = P.vCap + P.eCap + P.L + W + 2`, `g = ⌈P.impl.γ_ℓ P.mMax⌉₊`, and
`W_len = ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊`. -/
theorem dsUpdateOpSpace_le_caps (P : DSParams) {d : DSHist} {b batchPtr W h : ℕ} {mem : ℕ → ℕ}
    (hL : 1 ≤ P.L) (hVG₀ : d.G₀.IsValid) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hG₀E : ∀ e ∈ d.G₀.E, e < P.eCap) (hG₀n : d.G₀.n + P.splitBound ≤ P.vCap)
    (hBV : d.G₀.BatchIsValid (d.flat ++ (opBatch P d [b, batchPtr, W, h] mem).1))
    (hds : ∀ u ∈ d.flat ++ (opBatch P d [b, batchPtr, W, h] mem).1, isDelOrSplit u)
    (hsplit : batchSplitCount (d.flat ++ (opBatch P d [b, batchPtr, W, h] mem).1) ≤ P.splitBound)
    (hlens : (opBatch P d [b, batchPtr, W, h] mem).2.sum ≤ W) :
    let B := P.vCap + P.eCap + P.L + W + 2
    let g := ⌈P.impl.γ_ℓ P.mMax⌉₊
    let W_len := ⌈lenBound (P.impl.γ_ℓ P.mMax) P.L⌉₊
    dsUpdateOpSpace P d [b, batchPtr, W, h] mem ≤
      2 * B * (180 * B * W_len) ^ P.impl.cw + 450 * B ^ 3 * g * W_len := by
  intro B g W_len
  have hGm_e : d.G₀.m ≤ P.eCap := card_le_cap_of_lt hG₀E
  have hGn_v : d.G₀.n + batchSplitCount (d.flat ++ (opBatch P d [b, batchPtr, W, h] mem).1) ≤ P.vCap := by
    omega
  have hUlen : (opBatch P d [b, batchPtr, W, h] mem).1.length ≤ P.vCap + P.eCap := by
    have h1 := batch_length_le_m_add_splits hBV hds
    rw [List.length_append] at h1
    omega
  have hq : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hloop := dsUpdateLoopSpace_le_caps (impl := P.impl) (W := W) (k₀ := d.flat.length)
    hVG₀ hL hq hGm₀ hGm_e hGn_v hBV hds hUlen hlens
  have hopW : opWords [b, batchPtr, W, h] = W := rfl
  have hB_le : W ≤ B ^ 3 * g * W_len := by
    have hB2 : 2 ≤ B := by omega
    have hg1 : 1 ≤ g := one_le_ceil_gamma P.impl P.mMax
    have hW1 : 1 ≤ W_len := one_le_ceil_lenBound P.impl P.mMax P.L
    have h1 : W ≤ B := by omega
    have h2 : B ≤ B ^ 3 := Nat.le_self_pow (by decide) B
    have h3 : B ^ 3 ≤ B ^ 3 * g * W_len := by
      calc B ^ 3 = B ^ 3 * 1 * 1 := by ring
        _ ≤ B ^ 3 * g * W_len := Nat.mul_le_mul (Nat.mul_le_mul_left _ hg1) hW1
    omega
  unfold dsUpdateOpSpace
  rw [hopW]
  dsimp only
  change dsUpdateLoopSpace d.G₀ P.impl P.mMax P.L (d.q P) P.vCap P.eCap
      (d.flat ++ (opBatch P d [b, batchPtr, W, h] mem).1)
      (opBatch P d [b, batchPtr, W, h] mem).1 (opBatch P d [b, batchPtr, W, h] mem).2
      d.flat.length ≤
    2 * B * (180 * B * W_len) ^ P.impl.cw + 449 * B ^ 3 * g * W_len at hloop
  have e450 : 450 * B ^ 3 * g * W_len = 449 * B ^ 3 * g * W_len + B ^ 3 * g * W_len := by ring
  omega

end

end MinCostFlow.DynSpanner.Program
