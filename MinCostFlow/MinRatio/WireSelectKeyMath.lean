module

public import MinCostFlow.Chain.FindCycleHeap
public import MinCostFlow.Chain.Ordered.CyclePathRepFind
public import MinCostFlow.MinRatio.UpdateCycleLoopBase
public import MinCostFlow.MinRatio.PathCancellationAccounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Exact key comparison, signed key invariance, and route extraction for `FindCycle`

This file provides the pure mathematical bridge between the heap of own-level candidate keys
(`Chain/FindCycleHeap.lean`, `jtree.tex` pages 21 and 24) and the Word-RAM cycle selector:

1. `keyBetter`: exact cross-multiplication order comparing two candidate keys `(e₁, N₁, D₁)` and
   `(e₂, N₂, D₂)` (`|N₁| · D₂ > |N₂| · D₁`, breaking ties by least internal edge ID `e₁ < e₂`).
   Proved to be a strict total order on distinct edge IDs and to identify the heap root with
   `leastArgmax S (heapCycleRatio C g ℓ) hne` (`heapTop_eq_leastArgmax`).
2. `walkInner_and_wlenAt_congr_prefix` and `walkInner_and_wlenAt_eq_of_unchanged_emb`:
   strengthens `heapCycleRatio_congr_prefix` and `heapCycleRatio_eq_of_unchanged_emb` to preserve
   both the signed numerator `walkInner` (needed for cycle orientation) and the denominator `wlenAt`.
3. `stretch_coreLen_exact`: exact branch-free/division-free update of core edge lengths from
   `StretchValuesAt` `(num, den)` when `den = prev ∨ num = den`.
4. `rawEdgesOfWalk`, `rawPathsOfWalk`, `rawRouteOfWalk_spec`, and `cycleRouteAt_of_raw_cancel`:
   deterministic extraction of off-tree edges and tree-path endpoint pairs from `C.sparsifierCycle i eBest`
   and `flip = ¬ (N_{eBest} ≤ 0)`, establishing `CycleRouteAt` once the tree paths are made
   cancellation-free (`PathCancellationAccounting.lean`).
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-! ## 1. Exact cross-multiplication key order -/

/-- Exact comparison of two candidate keys `(e₁, n₁, d₁)` and `(e₂, n₂, d₂)`:
returns `true` iff `|n₁| / d₁ > |n₂| / d₂` (for positive `d₁, d₂`) or they tie with `e₁ < e₂`.
Uses `natAbs` products so it agrees directly with `|(n₁ * d₂)|` vs `|(n₂ * d₁)|`. -/
@[expose] def keyBetter (e₁ : ℕ) (n₁ d₁ : ℤ) (e₂ : ℕ) (n₂ d₂ : ℤ) : Bool :=
  decide (n₂.natAbs * d₁.natAbs < n₁.natAbs * d₂.natAbs ∨
    (n₂.natAbs * d₁.natAbs = n₁.natAbs * d₂.natAbs ∧ e₁ < e₂))

theorem keyBetter_iff (e₁ : ℕ) (n₁ d₁ : ℤ) (e₂ : ℕ) (n₂ d₂ : ℤ) :
    keyBetter e₁ n₁ d₁ e₂ n₂ d₂ = true ↔
      n₂.natAbs * d₁.natAbs < n₁.natAbs * d₂.natAbs ∨
        (n₂.natAbs * d₁.natAbs = n₁.natAbs * d₂.natAbs ∧ e₁ < e₂) := by
  simp [keyBetter]

theorem keyBetter_iff_mul_natAbs (e₁ : ℕ) (n₁ d₁ : ℤ) (e₂ : ℕ) (n₂ d₂ : ℤ) :
    keyBetter e₁ n₁ d₁ e₂ n₂ d₂ = true ↔
      (n₂ * d₁).natAbs < (n₁ * d₂).natAbs ∨
        ((n₂ * d₁).natAbs = (n₁ * d₂).natAbs ∧ e₁ < e₂) := by
  simp [keyBetter, Int.natAbs_mul]

theorem keyBetter_irrefl (e : ℕ) (n d : ℤ) : keyBetter e n d e n d = false := by
  simp [keyBetter]

theorem keyBetter_asymm {e₁ e₂ : ℕ} {n₁ d₁ n₂ d₂ : ℤ}
    (h : keyBetter e₁ n₁ d₁ e₂ n₂ d₂ = true) :
    keyBetter e₂ n₂ d₂ e₁ n₁ d₁ = false := by
  rw [keyBetter_iff] at h
  rw [Bool.eq_false_iff]
  intro h2
  rw [keyBetter_iff] at h2
  omega

theorem keyBetter_total_of_ne {e₁ e₂ : ℕ} {n₁ d₁ n₂ d₂ : ℤ} (hne : e₁ ≠ e₂) :
    keyBetter e₁ n₁ d₁ e₂ n₂ d₂ = true ∨ keyBetter e₂ n₂ d₂ e₁ n₁ d₁ = true := by
  simp only [keyBetter_iff]
  omega

/-- Clean real-ratio characterization of `keyBetter` when denominators are positive. -/
theorem keyBetter_iff_real {e₁ e₂ P : ℕ} {n₁ d₁ n₂ d₂ : ℤ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    let r₁ : ℝ := |((n₁ : ℝ) / (2 : ℝ) ^ P)| / ((d₁ : ℝ) / (2 : ℝ) ^ P)
    let r₂ : ℝ := |((n₂ : ℝ) / (2 : ℝ) ^ P)| / ((d₂ : ℝ) / (2 : ℝ) ^ P)
    keyBetter e₁ n₁ d₁ e₂ n₂ d₂ = true ↔ r₂ < r₁ ∨ (r₂ = r₁ ∧ e₁ < e₂) := by
  dsimp only
  have hP : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos (by norm_num) P
  have hd₁R : (0 : ℝ) < (d₁ : ℝ) := Int.cast_pos.mpr hd₁
  have hd₂R : (0 : ℝ) < (d₂ : ℝ) := Int.cast_pos.mpr hd₂
  have hnatAbs (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hn₁ : ((n₁.natAbs : ℕ) : ℝ) = |(n₁ : ℝ)| := hnatAbs n₁
  have hn₂ : ((n₂.natAbs : ℕ) : ℝ) = |(n₂ : ℝ)| := hnatAbs n₂
  have hd₁N : ((d₁.natAbs : ℕ) : ℝ) = (d₁ : ℝ) := (hnatAbs d₁).trans (abs_of_pos hd₁R)
  have hd₂N : ((d₂.natAbs : ℕ) : ℝ) = (d₂ : ℝ) := (hnatAbs d₂).trans (abs_of_pos hd₂R)
  have hr₁ : |((n₁ : ℝ) / (2 : ℝ) ^ P)| / ((d₁ : ℝ) / (2 : ℝ) ^ P) = |(n₁ : ℝ)| / (d₁ : ℝ) := by
    rw [abs_div, abs_of_pos hP, div_div_div_cancel_right₀ hP.ne']
  have hr₂ : |((n₂ : ℝ) / (2 : ℝ) ^ P)| / ((d₂ : ℝ) / (2 : ℝ) ^ P) = |(n₂ : ℝ)| / (d₂ : ℝ) := by
    rw [abs_div, abs_of_pos hP, div_div_div_cancel_right₀ hP.ne']
  rw [hr₁, hr₂, keyBetter_iff]
  have hlt_iff : n₂.natAbs * d₁.natAbs < n₁.natAbs * d₂.natAbs ↔
      |(n₂ : ℝ)| / (d₂ : ℝ) < |(n₁ : ℝ)| / (d₁ : ℝ) := by
    rw [div_lt_div_iff₀ hd₂R hd₁R]
    constructor
    · intro h
      have hR : ((n₂.natAbs * d₁.natAbs : ℕ) : ℝ) < ((n₁.natAbs * d₂.natAbs : ℕ) : ℝ) :=
        Nat.cast_lt.mpr h
      simpa only [Nat.cast_mul, hn₁, hn₂, hd₁N, hd₂N] using hR
    · intro h
      have hR : ((n₂.natAbs * d₁.natAbs : ℕ) : ℝ) < ((n₁.natAbs * d₂.natAbs : ℕ) : ℝ) := by
        simpa only [Nat.cast_mul, hn₁, hn₂, hd₁N, hd₂N] using h
      exact Nat.cast_lt.mp hR
  have heq_iff : n₂.natAbs * d₁.natAbs = n₁.natAbs * d₂.natAbs ↔
      |(n₂ : ℝ)| / (d₂ : ℝ) = |(n₁ : ℝ)| / (d₁ : ℝ) := by
    rw [div_eq_div_iff hd₂R.ne' hd₁R.ne']
    constructor
    · intro h
      have hR : ((n₂.natAbs * d₁.natAbs : ℕ) : ℝ) = ((n₁.natAbs * d₂.natAbs : ℕ) : ℝ) :=
        congrArg Nat.cast h
      simpa only [Nat.cast_mul, hn₁, hn₂, hd₁N, hd₂N] using hR
    · intro h
      have hR : ((n₂.natAbs * d₁.natAbs : ℕ) : ℝ) = ((n₁.natAbs * d₂.natAbs : ℕ) : ℝ) := by
        simpa only [Nat.cast_mul, hn₁, hn₂, hd₁N, hd₂N] using h
      exact Nat.cast_injective hR
  rw [hlt_iff, heq_iff]

/-- Clean transitivity of `keyBetter` when all denominators are positive. -/
theorem keyBetter_trans_pos {e₁ e₂ e₃ : ℕ} {n₁ d₁ n₂ d₂ n₃ d₃ : ℤ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (h₁₂ : keyBetter e₁ n₁ d₁ e₂ n₂ d₂ = true)
    (h₂₃ : keyBetter e₂ n₂ d₂ e₃ n₃ d₃ = true) :
    keyBetter e₁ n₁ d₁ e₃ n₃ d₃ = true := by
  have h1 := (keyBetter_iff_real (P := 0) hd₁ hd₂).mp h₁₂
  have h2 := (keyBetter_iff_real (P := 0) hd₂ hd₃).mp h₂₃
  refine (keyBetter_iff_real (P := 0) hd₁ hd₃).mpr ?_
  rcases h1 with h1 | ⟨he1, hl1⟩ <;> rcases h2 with h2 | ⟨he2, hl2⟩
  · exact Or.inl (lt_trans h2 h1)
  · exact Or.inl (he2.symm ▸ h1)
  · exact Or.inl (he1 ▸ h2)
  · exact Or.inr ⟨he2.trans he1, lt_trans hl1 hl2⟩

/-- **Heap-root identification theorem**: if `eBest ∈ S` beats every other `e ∈ S` under
`keyBetter`, where `(n e, d e)` represent the numerator and positive denominator of
`heapCycleRatio C g ℓ e` at a common precision `P`, then `eBest = leastArgmax S (heapCycleRatio C g ℓ) hne`. -/
theorem heapTop_eq_leastArgmax (C : TreeChain) (g ℓ : ℕ → ℝ) (P : ℕ)
    (S : Finset ℕ) (hne : S.Nonempty) (eBest : ℕ) (heBest : eBest ∈ S)
    (n d : ℕ → ℤ)
    (hdPos : ∀ e ∈ S, 0 < d e)
    (hRatio : ∀ e ∈ S,
      heapCycleRatio C g ℓ e = |((n e : ℝ) / (2 : ℝ) ^ P)| / ((d e : ℝ) / (2 : ℝ) ^ P))
    (hTop : ∀ e ∈ S, e ≠ eBest → keyBetter eBest (n eBest) (d eBest) e (n e) (d e) = true) :
    eBest = leastArgmax S (heapCycleRatio C g ℓ) hne := by
  have hBestMax : ∀ e ∈ S, heapCycleRatio C g ℓ e ≤ heapCycleRatio C g ℓ eBest := by
    intro e he
    by_cases hEq : e = eBest
    · subst hEq; exact le_rfl
    · have hb := (keyBetter_iff_real (P := P) (hdPos eBest heBest) (hdPos e he)).mp (hTop e he hEq)
      rw [hRatio e he, hRatio eBest heBest]
      rcases hb with hlt | ⟨heq, _⟩
      · exact le_of_lt hlt
      · exact le_of_eq heq
  have hSpec := leastArgmax_spec S (heapCycleRatio C g ℓ) hne
  have hLe1 : leastArgmax S (heapCycleRatio C g ℓ) hne ≤ eBest :=
    leastArgmax_le S (heapCycleRatio C g ℓ) hne heBest hBestMax
  by_contra hneBest
  have hb := (keyBetter_iff_real (P := P) (hdPos eBest heBest) (hdPos _ hSpec.1)).mp
    (hTop _ hSpec.1 (Ne.symm hneBest))
  rw [← hRatio _ hSpec.1, ← hRatio eBest heBest] at hb
  have hge := hSpec.2 eBest heBest
  rcases hb with hlt | ⟨_, heLt⟩
  · linarith
  · omega

/-- The signed integer pair `(n, d)` represents the exact signed cycle ratio `(num, den)`:
there is a positive real scale `s > 0` with `(n : ℝ) = s * num` and `(d : ℝ) = s * den`.
This accommodates fixed-point precision `P` on interior levels `j < d` and `P + pLast` on the
terminal level `j = d`, while preserving both the ratio `|n| / d = |num| / den` and the sign
`n ≤ 0 ↔ num ≤ 0`. -/
@[expose] def SelectKeyRepresents (n d : ℤ) (num den : ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ (n : ℝ) = s * num ∧ (d : ℝ) = s * den

theorem SelectKeyRepresents.of_fixVal {n d : ℤ} {num den : ℝ} {Q : ℕ}
    (hn : (n : ℝ) / (2 : ℝ) ^ Q = num) (hd : (d : ℝ) / (2 : ℝ) ^ Q = den) :
    SelectKeyRepresents n d num den := by
  have hQ : (0 : ℝ) < (2 : ℝ) ^ Q := pow_pos zero_lt_two Q
  refine ⟨(2 : ℝ) ^ Q, hQ, ?_, ?_⟩
  · rw [← hn, mul_div_cancel₀ _ hQ.ne']
  · rw [← hd, mul_div_cancel₀ _ hQ.ne']

theorem SelectKeyRepresents.ratio_eq {n d : ℤ} {num den : ℝ}
    (h : SelectKeyRepresents n d num den) :
    |(n : ℝ)| / (d : ℝ) = |num| / den := by
  obtain ⟨s, hs, hn, hd⟩ := h
  rw [hn, hd, abs_mul, abs_of_pos hs, mul_div_mul_left _ _ hs.ne']

theorem SelectKeyRepresents.div_eq {n d : ℤ} {num den : ℝ}
    (h : SelectKeyRepresents n d num den) :
    (n : ℝ) / (d : ℝ) = num / den := by
  obtain ⟨s, hs, hn, hd⟩ := h
  rw [hn, hd, mul_div_mul_left _ _ hs.ne']

theorem SelectKeyRepresents.nonpos_iff {n d : ℤ} {num den : ℝ}
    (h : SelectKeyRepresents n d num den) :
    n ≤ 0 ↔ num ≤ 0 := by
  obtain ⟨s, hs, hn, _⟩ := h
  constructor
  · intro hle
    have hR : s * num ≤ 0 := hn ▸ Int.cast_nonpos.mpr hle
    exact nonpos_of_mul_nonpos_right hR hs
  · intro hle
    have hR : (n : ℝ) ≤ 0 := hn.symm ▸ mul_nonpos_of_nonneg_of_nonpos hs.le hle
    exact Int.cast_nonpos.mp hR

/-! ## 2. Signed numerator and denominator invariance -/

/-- Prefix independence of the signed numerator and denominator (`Shift(i₀)` / `Rebuild(i₀)`). -/
theorem walkInner_and_wlenAt_congr_prefix (C C' : TreeChain) {ℓ g : ℕ → ℝ} {i : ℕ}
    (hG : ∀ j ≤ i, C'.G j = C.G j)
    (hL : ∀ j ≤ i, C'.activeLSF j = C.activeLSF j)
    (hS : C'.activeS i = C.activeS i)
    (hEmb : C'.activeEmb i = C.activeEmb i)
    {e : ℕ} (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    e ∈ (C'.activeCore i).E \ (C'.activeS i).E ∧
      walkInner (C'.chainGrad g (i + 1)) (C'.sparsifierCycle i e) =
        walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) ∧
      C'.wlenAt ℓ i e = C.wlenAt ℓ i e := by
  have hCoreEq : C'.activeCore i = C.activeCore i := by
    unfold TreeChain.activeCore; rw [hG i le_rfl, hL i le_rfl]
  have he' : e ∈ (C'.activeCore i).E \ (C'.activeS i).E := by rwa [hCoreEq, hS]
  have hSp : C'.sparsifierCycle i e = C.sparsifierCycle i e := by
    unfold TreeChain.sparsifierCycle; rw [hEmb]
  have hLen : C'.chainLen ℓ (i + 1) = C.chainLen ℓ (i + 1) :=
    chainLen_congr_lt ℓ (i + 1)
      (fun j hj => hG j (Nat.lt_succ_iff.mp hj))
      (fun j hj => hL j (Nat.lt_succ_iff.mp hj))
  have hGrad : C'.chainGrad g (i + 1) = C.chainGrad g (i + 1) :=
    chainGrad_congr_lt g (i + 1)
      (fun j hj => hG j (Nat.lt_succ_iff.mp hj))
      (fun j hj => hL j (Nat.lt_succ_iff.mp hj))
  refine ⟨he', by rw [hSp, hGrad], ?_⟩
  unfold TreeChain.wlenAt
  rw [hSp, hLen]

/-- **Signed numerator and denominator invariance under non-rebuilding updates**:
if `φ` is a frozen potential family matching both `C` and `C'` on levels `0..i` (via
`walkInner_potGrad_eq_chainGrad`), and `e` stays in `(activeCore i).E \ (activeS i).E` with
unchanged embedding, unchanged `G_j`-endpoints on `W`, unchanged `g`, `ℓ`, and `wstr_j` on `W`,
then BOTH the signed numerator `walkInner` and the denominator `wlenAt` are identical. -/
theorem walkInner_and_wlenAt_eq_of_unchanged_emb (C C' : TreeChain)
    {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c) (hSpan' : C'.LastLevelSpans)
    {i e : ℕ} (hi : i ≤ C.d) (hi' : i ≤ C'.d)
    (φ : ℕ → ℕ → ℝ)
    (hPot : ∀ j ≤ i, ∀ a b, (C.activeLSF j).F.F.Connected a b →
      walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath a b) = φ j a - φ j b)
    (hPot' : ∀ j ≤ i, ∀ a b, (C'.activeLSF j).F.F.Connected a b →
      walkInner (potGrad C' g' φ j) ((C'.activeLSF j).F.F.forestPath a b) = φ j a - φ j b)
    (hEnds : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
      (C'.G j).tail f = (C.G j).tail f ∧ (C'.G j).head f = (C.G j).head f)
    (hWstr : ∀ j ≤ i, ∀ f ∈ walkEdges (C.sparsifierCycle i e),
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (he : e ∈ (C.activeCore i).E \ (C.activeS i).E)
    (he' : e ∈ (C'.activeCore i).E \ (C'.activeS i).E)
    (hEmb : C'.activeEmb i e = C.activeEmb i e) :
    walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
      walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) ∧
    C'.wlenAt ℓ' i e = C.wlenAt ℓ i e := by
  have hSpEq : C'.sparsifierCycle i e = C.sparsifierCycle i e := by
    unfold TreeChain.sparsifierCycle; rw [hEmb]
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hClosed' := C'.sparsifierCycle_isClosedWalk hH' hSpan' hi' he'
  have hChainLenEq : ∀ k ≤ i + 1, ∀ f ∈ walkEdges (C.sparsifierCycle i e),
      (k = 0 → f ∈ (C'.G 0).E → f ∈ (C.G 0).E → C'.chainLen ℓ' 0 f = C.chainLen ℓ 0 f) ∧
      (∀ m, k = m + 1 → f ∈ (C'.G m).E → f ∈ (C.G m).E →
        C'.chainLen ℓ' (m + 1) f = C.chainLen ℓ (m + 1) f) := by
    intro k
    induction k with
    | zero =>
      intro _ f _
      exact ⟨fun _ hf' hf => hℓEq f hf' hf, fun _ h => by omega⟩
    | succ m ih =>
      intro hm f hfW
      refine ⟨fun h => by omega, fun m' hm' hf' hf => ?_⟩
      have heqm : m' = m := by omega
      subst m'
      have hm_i : m ≤ i := Nat.le_of_succ_le_succ hm
      have hm_d : m ≤ C.d := le_trans hm_i hi
      have hm_d' : m ≤ C'.d := le_trans hm_i hi'
      have hprev : C'.chainLen ℓ' m f = C.chainLen ℓ m f := by
        cases m with
        | zero => exact (ih (Nat.le_of_lt hm) f hfW).1 rfl hf' hf
        | succ m'' =>
          have hf1' : f ∈ (C'.G m'').E := (Finset.mem_sdiff.mp (C'.G_succ_E_subset hH' hm_d' hf')).1
          have hf1 : f ∈ (C.G m'').E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hm_d hf)).1
          exact (ih (Nat.le_of_lt hm) f hfW).2 m'' rfl hf1' hf1
      change (C'.activeLSF m).wstr f * C'.chainLen ℓ' m f =
        (C.activeLSF m).wstr f * C.chainLen ℓ m f
      rw [hWstr m hm_i f hfW, hprev]
  have hWlenEq : C'.wlenAt ℓ' i e = C.wlenAt ℓ i e := by
    unfold TreeChain.wlenAt
    rw [hSpEq]
    apply congrArg List.sum
    refine List.map_congr_left fun x hx => ?_
    have hf : x.1 ∈ walkEdges (C.sparsifierCycle i e) := by
      unfold walkEdges; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have hfCore : x.1 ∈ (C.activeCore i).E := mem_E_of_mem_walkEdges hClosed hf
    have hfCore' : x.1 ∈ (C'.activeCore i).E := mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hf)
    have hfGi : x.1 ∈ (C.G i).E := (Finset.mem_sdiff.mp hfCore).1
    have hfGi' : x.1 ∈ (C'.G i).E := (Finset.mem_sdiff.mp hfCore').1
    exact (hChainLenEq (i + 1) le_rfl x.1 hf).2 i rfl hfGi' hfGi
  have hPotGradEq : ∀ f ∈ (C'.G i).E, f ∈ (C.G i).E →
      potGrad C' g' φ (i + 1) f = potGrad C g φ (i + 1) f := by
    intro f hfGi' hfGi
    rw [potGrad_eq_sum, potGrad_eq_sum]
    have hf0' : f ∈ (C'.G 0).E := C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' hfGi'
    have hf0 : f ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi hfGi
    rw [hgEq f hf0' hf0]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hfj' : f ∈ (C'.G j).E := C'.G_E_subset_of_le hH' hji hi' hfGi'
    have hfj : f ∈ (C.G j).E := C.G_E_subset_of_le hH hji hi hfGi
    have hej := hEnds j hji f hfj' hfj
    rw [hej.1, hej.2]
  have hGradEq : walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
      walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) := by
    rw [← walkInner_potGrad_eq_chainGrad C' hH' hSpan' φ hi' hPot' he',
        ← walkInner_potGrad_eq_chainGrad C hH hSpan φ hi hPot he, hSpEq]
    unfold walkInner
    refine Finset.sum_congr rfl fun f hf => ?_
    have hfCore : f ∈ (C.activeCore i).E := mem_E_of_mem_walkEdges hClosed hf
    have hfCore' : f ∈ (C'.activeCore i).E := mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hf)
    rw [hPotGradEq f (Finset.mem_sdiff.mp hfCore').1 (Finset.mem_sdiff.mp hfCore).1]
  exact ⟨hGradEq, hWlenEq⟩

/-! ## 3. Exact core length update from `StretchValuesAt` -/

/-- Exact branch-free update of `coreLen = wstr * prev` from a stretch fraction `(num, den)`:
whenever `wstr = num / den` with `0 < den` and either `den = prev` (original edges) or
`num = den` (inserted edges with `wstr = 1`), `if num = den then prev else num` equals `wstr * prev`. -/
theorem stretch_coreLen_exact {wstr num den prev : ℝ}
    (hden : 0 < den) (hquot : num / den = wstr) (hform : den = prev ∨ num = den) :
    (if num = den then prev else num) = wstr * prev := by
  split_ifs with heq
  · rw [← hquot, heq, div_self hden.ne', one_mul]
  · have hdp : den = prev := hform.resolve_right heq
    rw [← hquot, hdp, div_mul_cancel₀ _ (hdp ▸ hden.ne')]

/-! ## 4. Deterministic route extraction for `Select` -/

/-- Every active spanner embedding `Π_i(e)` (`i < d`) for an off-spanner core edge `e`
has distinct edge names (satisfied by `DynSpanner` via `shortcutWalk`). -/
@[expose] def EdgeSimpleEmbeddings (C : TreeChain) : Prop :=
  ∀ i < C.d, ∀ e ∈ (C.activeCore i).E \ (C.activeS i).E, ((C.activeEmb i e).map Prod.fst).Nodup

/-- Oriented step list of a sparsifier cycle: keeps `W` when `flip = false` and reverses
every edge's direction when `flip = true`. -/
@[expose] def orientWalkSteps (W : List (ℕ × Bool)) (flip : Bool) : List (ℕ × Bool) :=
  if flip then W.map (fun x => (x.1, !x.2)) else W

/-- Raw off-tree edge list extracted from `W` by keeping only steps outside `F.E`. -/
@[expose] noncomputable def rawEdgesOfWalk (F : MGraph) (W : List (ℕ × Bool)) (flip : Bool) :
    List (ℕ × Bool) :=
  open Classical in
  (orientWalkSteps W flip).filter (fun x => !(decide (x.1 ∈ F.E)))

/-- Raw tree-path endpoint list extracted from `W`: single-edge paths for steps in `F.E`
followed by the stitching endpoint pairs between consecutive steps of `W`. -/
@[expose] noncomputable def rawPathsOfWalk (G₀ F : MGraph) (W : List (ℕ × Bool)) (flip : Bool) :
    List (ℕ × ℕ) :=
  open Classical in
  let W_or := orientWalkSteps W flip
  let treeSteps := (W_or.filter (fun x => decide (x.1 ∈ F.E))).map (fun x => (G₀.src x, G₀.dst x))
  let stitches :=
    if flip then (cycleSegments G₀ W).2.map Prod.swap else (cycleSegments G₀ W).2
  treeSteps ++ stitches

private lemma walkFlow_orient_flip (W : List (ℕ × Bool)) (e : ℕ) :
    ((W.map (fun x => (x.1, !x.2))).map (fun x => walkFlow [x] e)).sum =
      -(W.map (fun x => walkFlow [x] e)).sum := by
  induction W with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have h1 : walkFlow [(x.1, !x.2)] e = -walkFlow [x] e := by
      cases hx : x.2 <;> simp [walkFlow, hx] <;> split_ifs <;> ring
    linarith

private lemma walkFlow_swap_paths (F : MGraph) (hF : F.IsForest)
    (ps : List (ℕ × ℕ)) (hconn : ∀ p ∈ ps, F.Connected p.1 p.2) (e : ℕ) :
    ((ps.map Prod.swap).map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum =
      -(ps.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := walkFlow_forestPath_walkRev hF (hconn p (by simp)) e
    have h2 := ih (fun q hq => hconn q (by simp [hq]))
    simp only [Prod.swap]
    linarith

private lemma split_filter_sum' {α : Type _} (L : List α) (p : α → Bool) (f : α → ℝ) :
    (L.map f).sum =
      ((L.filter (fun x => !(p x))).map f).sum + ((L.filter p).map f).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    cases hx : p x <;> simp [hx, ih] <;> ring

private lemma cycleSegmentsAux_conn' (G F : MGraph) (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      TreeChain.AdjConn G F target x xs →
      ∀ p ∈ (cycleSegmentsAux G target x xs).2, F.Connected p.1 p.2
  | [], x, hadj, p, hp => by
    simp only [cycleSegmentsAux, List.mem_singleton] at hp; subst hp; exact hadj
  | y :: ys, x, hadj, p, hp => by
    simp only [cycleSegmentsAux, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact hadj.1
    · exact cycleSegmentsAux_conn' G F target ys y hadj.2 p hp'

private lemma cycleSegmentsAux_mem_V (G : MGraph) (hV : G.IsValid) (target : ℕ) (ht : target ∈ G.V) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      x.1 ∈ G.E → (∀ y ∈ xs, y.1 ∈ G.E) →
      ∀ p ∈ (cycleSegmentsAux G target x xs).2, p.1 ∈ G.V ∧ p.2 ∈ G.V
  | [], x, hx, _, p, hp => by
    simp only [cycleSegmentsAux, List.mem_singleton] at hp; subst hp
    have h := hV x.1 hx
    exact ⟨by cases hx2 : x.2 <;> simp [MGraph.dst, hx2, h.1, h.2], ht⟩
  | y :: ys, x, hx, hxs, p, hp => by
    have hy : y.1 ∈ G.E := hxs y List.mem_cons_self
    simp only [cycleSegmentsAux, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · have hxV := hV x.1 hx; have hyV := hV y.1 hy
      exact ⟨by cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hxV.1, hxV.2],
             by cases hy2 : y.2 <;> simp [MGraph.src, hy2, hyV.1, hyV.2]⟩
    · exact cycleSegmentsAux_mem_V G hV target ht ys y hy
        (fun z hz => hxs z (List.mem_cons_of_mem _ hz)) p hp'

/-- **Exact specification of `rawEdgesOfWalk` and `rawPathsOfWalk`** for the best off-tree edge
`eBest = leastArgmax S (heapCycleRatio C st.g st.ℓ) hne` at level `i = C.edgeLevel eBest`
(unconditional, without `EdgeSimpleEmbeddings`). -/
theorem rawRouteOfWalk_spec {cfg : Alg2Config} (model : Alg2State cfg)
    {G : MGraph} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : model.chain.toTreeChain.Holds G model.chain.ℓ σ σ_mwu γ_ℓ γ_c)
    (hSpan : model.chain.toTreeChain.LastLevelSpans)
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hVlt : ∀ v ∈ model.extG.V, v < model.extG.n)
    (hne : ((model.chain.G 0).E \ model.chain.toTreeChain.chainTree.E).Nonempty) :
    let C := model.chain.toTreeChain
    let S := (model.chain.G 0).E \ C.chainTree.E
    let eBest := leastArgmax S (heapCycleRatio C model.chain.g model.chain.ℓ) hne
    let i := C.edgeLevel eBest
    let W := C.sparsifierCycle i eBest
    let flip := !(decide (walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0))
    let edges := rawEdgesOfWalk C.chainTree W flip
    let paths := rawPathsOfWalk (model.chain.G 0) C.chainTree W flip
    edges.length ≤ W.length ∧
    paths.length ≤ 2 * W.length ∧
    (∀ x ∈ edges, x.1 ∈ (model.chain.G 0).E \ C.chainTree.E) ∧
    (∀ p ∈ paths, p.1 < model.extG.n ∧ p.2 < model.extG.n ∧ C.chainTree.Connected p.1 p.2) ∧
    ∀ ei : ℕ, (algorithm1_findCycle model.chain).1 ei =
      (edges.map (fun x => walkFlow [x] ei)).sum +
      (paths.map (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) ei)).sum := by
  classical
  dsimp only
  set C := model.chain.toTreeChain
  set S := (model.chain.G 0).E \ C.chainTree.E
  set eBest := leastArgmax S (heapCycleRatio C model.chain.g model.chain.ℓ) hne
  set i := C.edgeLevel eBest
  set W := C.sparsifierCycle i eBest
  set flip := !(decide (walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0))
  set edges := rawEdgesOfWalk C.chainTree W flip
  set paths := rawPathsOfWalk (model.chain.G 0) C.chainTree W flip
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hFor := C.chainTree_isForest hH hSub
  have heBest : eBest ∈ S := (leastArgmax_spec S (heapCycleRatio C model.chain.g model.chain.ℓ) hne).1
  have hlvl := C.mem_activeCore_diff_edgeLevel hH heBest
  have hi : i ≤ C.d := hlvl.1
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi hlvl.2
  have hG0Val : (C.G 0).IsValid := C.G_isValid hH 0 (Nat.zero_le C.d)
  have hWE : ∀ y ∈ W, y.1 ∈ (C.G 0).E := fun y hy =>
    C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp (MGraph.isWalk_edges_mem hClosed y hy)).1
  have hWOrLen : (orientWalkSteps W flip).length = W.length := by
    unfold orientWalkSteps; split_ifs <;> simp
  have hWOrE : ∀ x ∈ orientWalkSteps W flip, x.1 ∈ (C.G 0).E := by
    intro x hx
    unfold orientWalkSteps at hx
    split_ifs at hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hWE y hy
    · exact hWE x hx
  have hconn : ∀ a b : ℕ × Bool, a.1 ∈ (C.activeCore i).E → b.1 ∈ (C.activeCore i).E →
      (C.activeCore i).dst a = (C.activeCore i).src b →
      C.chainTree.Connected ((C.G 0).dst a) ((C.G 0).src b) := by
    intro a b haE hbE heq
    have haGi : a.1 ∈ (C.G i).E := (Finset.mem_sdiff.mp haE).1
    have hbGi : b.1 ∈ (C.G i).E := (Finset.mem_sdiff.mp hbE).1
    have haG0 : a.1 ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi haGi
    have hbG0 : b.1 ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi hbGi
    have hEndsA := hG0Val a.1 haG0; have hEndsB := hG0Val b.1 hbG0
    have haV0 : (C.G 0).dst a ∈ (C.G 0).V := by cases ha2 : a.2 <;> simp [MGraph.dst, ha2, hEndsA.1, hEndsA.2]
    have hbV0 : (C.G 0).src b ∈ (C.G 0).V := by cases hb2 : b.2 <;> simp [MGraph.src, hb2, hEndsB.1, hEndsB.2]
    have hproj_eq : C.proj (i + 1) ((C.G 0).dst a) = C.proj (i + 1) ((C.G 0).src b) := by
      change (C.activeLSF i).F.root (C.proj i ((C.G 0).dst a)) =
        (C.activeLSF i).F.root (C.proj i ((C.G 0).src b))
      rw [← C.G_dst_eq_proj hH hi haGi, ← C.G_src_eq_proj hH hi hbGi]
      have hdst : (C.activeCore i).dst a = (C.activeLSF i).F.root ((C.G i).dst a) := by
        cases ha2 : a.2 <;> simp [MGraph.dst, TreeChain.activeCore, coreGraph, ha2]
      have hsrc : (C.activeCore i).src b = (C.activeLSF i).F.root ((C.G i).src b) := by
        cases hb2 : b.2 <;> simp [MGraph.src, TreeChain.activeCore, coreGraph, hb2]
      rw [← hdst, ← hsrc]; exact heq
    exact C.connected_chainTree_of_proj_eq hH hSub (i + 1) (Nat.succ_le_succ hi) _ haV0 _ hbV0 hproj_eq
  have hPsConn : ∀ p ∈ (cycleSegments (C.G 0) W).2, C.chainTree.Connected p.1 p.2 := by
    cases hW : W with
    | nil => simp [W, TreeChain.sparsifierCycle] at hW
    | cons x₀ xs =>
      have hC' : (C.activeCore i).IsWalk ((C.activeCore i).tail eBest) ((C.activeCore i).tail eBest) (x₀ :: xs) :=
        hW ▸ hClosed
      have hadj := TreeChain.adjConn_of_closedWalk (G := C.G 0) (F := C.chainTree) hC' hconn
      exact cycleSegmentsAux_conn' (C.G 0) C.chainTree ((C.G 0).src x₀) xs x₀ hadj
  have hPsMemV : ∀ p ∈ (cycleSegments (C.G 0) W).2, p.1 ∈ (C.G 0).V ∧ p.2 ∈ (C.G 0).V := by
    cases hW : W with
    | nil => simp [W, TreeChain.sparsifierCycle] at hW
    | cons x₀ xs =>
      have hx₀ : x₀.1 ∈ (C.G 0).E := hWE x₀ (hW ▸ List.mem_cons_self)
      have hxs : ∀ y ∈ xs, y.1 ∈ (C.G 0).E := fun y hy => hWE y (hW ▸ List.mem_cons_of_mem _ hy)
      have hsrcV : (C.G 0).src x₀ ∈ (C.G 0).V := by
        have h := hG0Val x₀.1 hx₀; cases hx02 : x₀.2 <;> simp [MGraph.src, hx02, h.1, h.2]
      exact cycleSegmentsAux_mem_V (C.G 0) hG0Val ((C.G 0).src x₀) hsrcV xs x₀ hx₀ hxs
  have hSeg := cycleSegments_eq (C.G 0) W
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (List.length_filter_le _ _).trans_eq hWOrLen
  · dsimp only [paths, rawPathsOfWalk]
    rw [List.length_append, List.length_map]
    have h1 : ((orientWalkSteps W flip).filter (fun x => decide (x.1 ∈ C.chainTree.E))).length ≤ W.length :=
      (List.length_filter_le _ _).trans_eq hWOrLen
    have h2 : (if flip then (cycleSegments (model.chain.G 0) W).2.map Prod.swap
        else (cycleSegments (model.chain.G 0) W).2).length = W.length := by
      have hSeg2 : (cycleSegments (model.chain.G 0) W).2.length = W.length := hSeg.2
      split_ifs <;> simp [hSeg2]
    rw [h2]; omega
  · intro x hx
    dsimp only [edges, rawEdgesOfWalk] at hx
    rw [List.mem_filter] at hx
    exact Finset.mem_sdiff.mpr ⟨hWOrE x hx.1, by simpa using hx.2⟩
  · intro p hp
    dsimp only [paths, rawPathsOfWalk] at hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_filter] at hx
      have hxG0 : x.1 ∈ (C.G 0).E := hWOrE x hx.1
      have hxT : x.1 ∈ C.chainTree.E := by simpa using hx.2
      have hEnds : (model.chain.G 0).tail x.1 ∈ (model.chain.G 0).V ∧
          (model.chain.G 0).head x.1 ∈ (model.chain.G 0).V := hG0Val x.1 hxG0
      have hsrcV : (model.chain.G 0).src x ∈ model.extG.V := by
        rw [hFresh.hV]; cases hx2 : x.2 <;> simp [MGraph.src, hx2, hEnds.1, hEnds.2]
      have hdstV : (model.chain.G 0).dst x ∈ model.extG.V := by
        rw [hFresh.hV]; cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hEnds.1, hEnds.2]
      exact ⟨hVlt _ hsrcV, hVlt _ hdstV, ⟨[x], .cons hxT rfl (by simp [TreeChain.chainTree]; exact .nil _)⟩⟩
    · split_ifs at hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have hqV := hPsMemV q hq
        exact ⟨hVlt _ (hFresh.hV ▸ hqV.2), hVlt _ (hFresh.hV ▸ hqV.1), MGraph.connected_symm (hPsConn q hq)⟩
      · have hpV := hPsMemV p hp
        exact ⟨hVlt _ (hFresh.hV ▸ hpV.1), hVlt _ (hFresh.hV ▸ hpV.2), hPsConn p hp⟩
  · intro ei
    have hAlg : (algorithm1_findCycle model.chain).1 ei =
        (if walkInner model.chain.g (C.fundChainCycle eBest) ≤ 0
          then walkFlow (C.fundChainCycle eBest) ei
          else walkFlow (walkRev (C.fundChainCycle eBest)) ei) := by
      unfold algorithm1_findCycle
      rw [dite_eq_left_of_eq_true (eq_true hne)]
      dsimp only
      split_ifs <;> rfl
    rw [hAlg]
    have hSignIff : walkInner model.chain.g (C.fundChainCycle eBest) ≤ 0 ↔
        walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0 :=
      walkInner_fundChainCycle_nonpos_iff C hH hSpan heBest
    have hRaw : walkFlow (C.fundChainCycle eBest) ei =
        (W.map (fun y => walkFlow [y] ei)).sum +
        ((cycleSegments (C.G 0) W).2.map (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) ei)).sum := by
      have h1 := walkFlow_stitchCycle_segments (C.G 0) C.chainTree W ei
      rw [hSeg.1] at h1
      simpa [TreeChain.fundChainCycle, TreeChain.fundChainCycleAt, i, W] using h1
    have hOrSplit : ((orientWalkSteps W flip).map (fun x => walkFlow [x] ei)).sum =
        (edges.map (fun x => walkFlow [x] ei)).sum +
        (((orientWalkSteps W flip).filter (fun x => decide (x.1 ∈ C.chainTree.E))).map
          (fun x => walkFlow (C.chainTree.forestPath ((C.G 0).src x) ((C.G 0).dst x)) ei)).sum := by
      have hsp := split_filter_sum' (orientWalkSteps W flip)
        (fun x => decide (x.1 ∈ C.chainTree.E)) (fun x => walkFlow [x] ei)
      rw [hsp]
      congr 1
      apply congrArg List.sum
      refine List.map_congr_left fun x hx => ?_
      have hxT : x.1 ∈ C.chainTree.E := by simpa using (List.mem_filter.mp hx).2
      have hW1 : C.chainTree.IsWalk ((C.G 0).src x) ((C.G 0).dst x) [x] :=
        .cons hxT rfl (by simp [TreeChain.chainTree]; exact .nil _)
      exact walkFlow_eq_of_isForest hFor hW1 (MGraph.isWalk_forestPath ⟨[x], hW1⟩) ei
    have hPathsSum : (paths.map (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) ei)).sum =
        (((orientWalkSteps W flip).filter (fun x => decide (x.1 ∈ C.chainTree.E))).map
          (fun x => walkFlow (C.chainTree.forestPath ((C.G 0).src x) ((C.G 0).dst x)) ei)).sum +
        ((if flip then (cycleSegments (C.G 0) W).2.map Prod.swap else (cycleSegments (C.G 0) W).2).map
          (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) ei)).sum := by
      dsimp only [paths, rawPathsOfWalk]
      rw [List.map_append, List.sum_append, List.map_map]
      rfl
    rw [hPathsSum]
    by_cases hneg : walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0
    · have hneg0 : walkInner model.chain.g (C.fundChainCycle eBest) ≤ 0 := hSignIff.mpr hneg
      have hfl : flip = false := by simp [flip, hneg]
      simp only [hneg0, ↓reduceIte, hfl, Bool.false_eq_true] at hOrSplit ⊢
      unfold orientWalkSteps at hOrSplit ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hOrSplit ⊢
      linarith
    · have hpos0 : ¬ walkInner model.chain.g (C.fundChainCycle eBest) ≤ 0 := fun h => hneg (hSignIff.mp h)
      have hfl : flip = true := by simp [flip, hneg]
      simp only [hpos0, ↓reduceIte, hfl] at hOrSplit ⊢
      unfold orientWalkSteps at hOrSplit ⊢
      simp only [↓reduceIte] at hOrSplit ⊢
      rw [walkFlow_orient_flip] at hOrSplit
      rw [walkFlow_walkRev, hRaw, walkFlow_swap_paths C.chainTree hFor _ hPsConn]
      linarith

/-- Combining a raw off-tree edge list `edges` and a cancellation-free rerouting `paths` of
`rawPaths` (producing the same signed flow on every edge and no opposite tree-edge traversals)
yields `CycleRouteAt model edges paths`. -/
theorem cycleRouteAt_of_raw_cancel {cfg : Alg2Config} {model : Alg2State cfg}
    {edges : List (ℕ × Bool)} {paths : List (ℕ × ℕ)}
    (hEd : ∀ x ∈ edges, x.1 ∈ (model.chain.G 0).E \ model.chain.toTreeChain.chainTree.E)
    (hPt : ∀ p ∈ paths, p.1 < model.extG.n ∧ p.2 < model.extG.n ∧
      model.chain.toTreeChain.chainTree.Connected p.1 p.2)
    (hFlow : ∀ ei : ℕ, (algorithm1_findCycle model.chain).1 ei =
      (edges.map (fun x => walkFlow [x] ei)).sum +
      (paths.map (fun p => walkFlow (model.chain.toTreeChain.chainTree.forestPath p.1 p.2) ei)).sum)
    (hNoCancel : ∀ (x : ℕ × Bool) p q, p ∈ paths → q ∈ paths →
      x ∈ model.chain.toTreeChain.chainTree.forestPath p.1 p.2 →
      (x.1, !x.2) ∉ model.chain.toTreeChain.chainTree.forestPath q.1 q.2) :
    CycleRouteAt model edges paths := by
  refine ⟨hEd, hPt, fun e _ => ⟨hFlow (model.extToInt e), fun k => ?_⟩⟩
  set F := model.chain.toTreeChain.chainTree
  set ei := model.extToInt e
  rw [hFlow ei]
  have hAcc := pathCancel_account_of_no_reverse F paths hNoCancel ei k
  by_cases hei : ei ∈ F.E
  · have hE0 : (edges.map (fun x => walkFlow [x] ei)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      have hne : x.1 ≠ ei := fun h => (Finset.mem_sdiff.mp (hEd x hx)).2 (h ▸ hei)
      simp [walkFlow, hne]
    rw [hE0, zero_add, mul_zero, abs_zero, zero_add, hAcc]
  · have hP0 : (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) ei)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
      apply walkFlow_eq_zero_of_not_mem
      intro hm
      exact hei (mem_E_of_mem_walkEdges (MGraph.isWalk_forestPath (hPt p hp).2.2) hm)
    have hP0abs : (paths.map (fun p => |k * walkFlow (F.forestPath p.1 p.2) ei|)).sum = 0 := by
      rw [hAcc, hP0, mul_zero, abs_zero]
    rw [hP0, add_zero, hP0abs, add_zero]

end MinCostFlow.MinRatio
