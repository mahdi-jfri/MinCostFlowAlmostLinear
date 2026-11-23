module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMidFacts
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBack
public import MinCostFlow.SparseCore.Program.AssemblyBranchInitBound
import Mathlib.Tactic.Ring

/-!
# Polynomial space bound for the build of a branch at its init (`AssemblyFirstInitBoundSpace`)

The body of the build of a branch at its init (`asmFirstInitBuildBody`) allocates fresh memory in
three phases: the front (`asmFiFrontSpace`), the middle (`asmFiMidSpace`), and the back
(`asmFiBackSpace`). This file defines an explicit polynomial `asmFiBuildSpacePoly` in
`X = M + N + k + vCap + eCap + L + depth`, depending only on the word exponent `cw` of the
sparsifier, its stretch bound `⌈γ_ℓ m⌉ ≤ Cγ · (m + 2) ^ cγ`, and `capExp` (free of `limbMul`),
and proves that:

1. For any bundle table `S5 : Fin eCap → Option BundleState` and slot count `n ≤ eCap` whose
   listed slot graphs meet `SpanGraphOK (asmFiSP impl w M depth k eCap)`, the fresh spanner table
   `spanAfter (fun _ => none) (asmFirstInitSlotGraph S5) (List.range n)` satisfies
   `rebuildSize ≤ n * (2 * eCap)` (`rebuildSize_spanAfter_init_le`) and
   `embRefreshSizeAt ≤ n * (eCap * (2 * ⌈impl.γ_ℓ M⌉₊ + 3) + 1)`
   (`embRefreshSizeAt_spanAfter_init_le`).
2. The total space `asmFiFrontSpace + asmFiMidSpace + asmFiBackSpace` is at most
   `(asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval (M + N + k + vCap + eCap + L + depth)`
   (`asmFiBuildSpace_le_poly`).
3. The word condition `h + (asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval X < 2 ^ w` implies all
   word-size bounds required by the build and by `initTree_spanGraphOK`, including
   `2 * (36 * (spV + 2 * spE + 1)) ^ impl.cw < 2 ^ w` and, when `P ≤ 4 * L`,
   `vCap * asmFirstInitKeyBase P Lw L < 2 ^ w` (`asmFiBuildSpace_word_bounds`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Bounds on `rebuildSize` and `embRefreshSizeAt` after spanner initialization -/

/-- A listed slot in `spanAfter (fun _ => none) g (List.range n)` holds the fresh spanner
`⟨g s, []⟩`. -/
theorem spanAfter_init_listed {cap : ℕ} (g : ℕ → MGraph) {n s : ℕ} (hs : s < cap)
    (hm : s ∈ List.range n) :
    spanAfter (fun _ => none) g (List.range n) ⟨s, hs⟩ = some ⟨g s, []⟩ := by
  simp [spanAfter, hm]

/-- **The graphs read by P10's rebuild at the init.** When `n ≤ cap` and each slot graph
`asmFirstInitSlotGraph S5 s` for `s < n` meets `SpanGraphOK P`, every listed slot adds at most
`2 * P.eCap` to `rebuildSize`. -/
theorem rebuildSize_spanAfter_init_le (P : DSParams) {slotCap cap : ℕ}
    (S5 : Fin slotCap → Option BundleState) {n : ℕ} (hn : n ≤ cap)
    (hok : ∀ s ∈ List.range n, SpanGraphOK P (asmFirstInitSlotGraph S5 s)) :
    rebuildSize P
        (spanAfter (fun _ => none : BucketSpannerState cap) (asmFirstInitSlotGraph S5)
          (List.range n)) (List.range n) ≤
      n * (2 * P.eCap) := by
  unfold rebuildSize
  refine (sum_map_le_length_mul (List.range n) _ (2 * P.eCap) fun s hm => ?_).trans
    (by rw [List.length_range])
  have hlt : s < n := List.mem_range.mp hm
  have hs : s < cap := lt_of_lt_of_le hlt hn
  have hG := hok s hm
  have hval := hG.2.2.2.2.2.2.1
  have hmM := hG.2.2.2.2.2.2.2.1
  have hS := spanAfter_init_listed (cap := cap) (asmFirstInitSlotGraph S5) hs hm
  have hGE : slotGE P (spanAfter (fun _ => none : BucketSpannerState cap)
      (asmFirstInitSlotGraph S5) (List.range n)) s = (asmFirstInitSlotGraph S5 s).E := by
    simp only [slotGE, hs, ↓reduceDIte, hS, dsHist_init_G_eq]
  have hHE : slotHE P (spanAfter (fun _ => none : BucketSpannerState cap)
      (asmFirstInitSlotGraph S5) (List.range n)) s ⊆ (asmFirstInitSlotGraph S5 s).E := by
    simp only [slotHE, hs, ↓reduceDIte, hS]
    exact dsHist_init_H_sub_E P hval hmM
  have h1 := Finset.card_le_card hHE
  have h2 := spanGraphOK_m_le hG
  rw [hGE]
  unfold MGraph.m at h2
  omega

/-- **The walks written by the embedding refresh at the init.** When `n ≤ cap` and each slot graph
`asmFirstInitSlotGraph S5 s` for `s < n` meets `SpanGraphOK P`, every listed slot adds at most
`P.eCap * (2 * ⌈P.impl.γ_ℓ P.mMax⌉₊ + 3) + 1` to `embRefreshSizeAt`. -/
theorem embRefreshSizeAt_spanAfter_init_le (P : DSParams) {slotCap cap : ℕ}
    (S5 : Fin slotCap → Option BundleState) {n : ℕ} (hn : n ≤ cap)
    (hok : ∀ s ∈ List.range n, SpanGraphOK P (asmFirstInitSlotGraph S5 s)) :
    embRefreshSizeAt P
        (spanAfter (fun _ => none : BucketSpannerState cap) (asmFirstInitSlotGraph S5)
          (List.range n)) (List.range n) ≤
      n * (P.eCap * (2 * ⌈P.impl.γ_ℓ P.mMax⌉₊ + 3) + 1) := by
  unfold embRefreshSizeAt
  refine (sum_map_le_length_mul (List.range n) _ _ fun s hm => ?_).trans
    (by rw [List.length_range])
  have hlt : s < n := List.mem_range.mp hm
  have hs : s < cap := lt_of_lt_of_le hlt hn
  have hG := hok s hm
  have hval := hG.2.2.2.2.2.2.1
  have hmM := hG.2.2.2.2.2.2.2.1
  have hS := spanAfter_init_listed (cap := cap) (asmFirstInitSlotGraph S5) hs hm
  set Hb := asmFirstInitSlotGraph S5 s
  set g := ⌈P.impl.γ_ℓ P.mMax⌉₊
  simp only [hs, ↓reduceDIte, hS, dsHist_init_G_eq, ↓reduceIte]
  have hsum : (Hb.E.sum fun e =>
      Read.walkWords (slotWalk P (spanAfter (fun _ => none : BucketSpannerState cap)
        (asmFirstInitSlotGraph S5) (List.range n)) s e) + 0 + 2) ≤
      Hb.E.card * (2 * g + 3) := by
    rw [← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun e he => ?_
    have hl := slotWalk_init_length_le_ceil P hs hS hval hmM he
    unfold Read.walkWords
    omega
  have hm' : Hb.E.card ≤ P.eCap := spanGraphOK_m_le hG
  exact Nat.add_le_add_right (hsum.trans (Nat.mul_le_mul_right (2 * g + 3) hm')) 1

/-! ## The polynomial bound -/

/-- **Polynomial space bound for the build of a branch at its init**, in
`X = M + N + k + vCap + eCap + L + depth`, parameterized by the word exponent `cw` of the
sparsifier, its stretch bound `⌈γ_ℓ m⌉ ≤ Cγ · (m + 2) ^ cγ`, and `capExp` (free of `limbMul`). -/
def asmFiBuildSpacePoly (cw Cγ cγ capExp : ℕ) : PolyBound where
  coeff := 84 * (capExp + sparseCoreReadout2LimbConst + 1) + 25332 +
    2 * 4284 ^ cw + 60 * (Cγ + 1) + embRefreshMul * (2 * Cγ + 6)
  deg := cw + cγ + 3

/-- The split bound `bundleSplitBudget k M` is at most `112 * M + 2` for `1 ≤ k`. -/
theorem bundleSplitBudget_le_linear {k M : ℕ} (hk : 1 ≤ k) :
    bundleSplitBudget k M ≤ 112 * M + 2 := by
  rw [bundleSplitBudget_eq_div k M hk]
  have hdiv : (56 * M + k - 1) / k ≤ 56 * M + 1 := by
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_eq_add_one, show 56 * M + (k' + 1) - 1 = 56 * M + k' by omega]
    nlinarith
  omega

/-- **Pure arithmetic of the space bound.** When every parameter is bounded in terms of `Z ≥ 2`,
the sum of the front, middle, and back space bounds is at most `(asmFiBuildSpacePoly …).coeff`
times `Z ^ (cw + cγ + 3)`. -/
theorem asmFiBuildSpace_arith {Z cw Cγ cγ cL vCap eCap Lw L depth spV g n Sn Sm rb er : ℕ}
    (hZ : 2 ≤ Z) (hv : vCap ≤ Z) (he : eCap ≤ Z) (hL : L ≤ Z) (hLw : Lw ≤ cL * Z)
    (hd : depth ≤ Z) (hspV : spV ≤ 116 * Z) (hg : g ≤ Cγ * Z ^ cγ)
    (hn : n ≤ eCap) (hSn : Sn ≤ Z) (hSm : Sm ≤ Z)
    (hrb : rb ≤ n * (2 * eCap)) (her : er ≤ n * (eCap * (2 * g + 3) + 1)) :
    asmFiFrontSpace vCap eCap Lw L +
      (5 * vCap + bundleTableFixedSize eCap eCap + eCap * (3 + 24 * eCap) + 3 * eCap + spV +
        eCap * (6 + 10 * eCap + (4 + spV + 3 * eCap) +
          (100 * ((depth + 1) * (spV + eCap + 1)) +
            (2 * (36 * (spV + 2 * eCap + 1)) ^ cw + 30 * (eCap + 1) * (g + 1) + 3 * spV +
              dynGraphSize spV eCap + eCap + 10)))) +
      (rootTblSpace vCap eCap + (7 + dynGraphSize vCap eCap + n + 2 * rb) +
        (4 + Sn + 3 * Sm) + (3 + eCap + embRefreshMul * (er + n + 1))) ≤
    (84 * cL + 25332 + 2 * 4284 ^ cw + 60 * (Cγ + 1) + embRefreshMul * (2 * Cγ + 6)) *
      Z ^ (cw + cγ + 3) := by
  have hZpos : 0 < Z := by omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → Z ^ a ≤ Z ^ b := fun h => Nat.pow_le_pow_right hZpos h
  have hZ12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) Z
  have hZ2d : Z ^ 2 ≤ Z ^ (cw + cγ + 3) := hpw (by omega)
  have hZ1d : Z ≤ Z ^ (cw + cγ + 3) := hZ12.trans hZ2d
  -- 1. Front space
  have hFront : asmFiFrontSpace vCap eCap Lw L ≤ (21 * cL + 178) * Z ^ (cw + cγ + 3) := by
    have hbws : bucketWordSpace Lw L ≤ (21 * cL + 26) * Z := by
      unfold bucketWordSpace
      have e : (21 * cL + 26) * Z = 21 * (cL * Z) + 26 * Z := by ring
      omega
    have heb : eCap * bucketWordSpace Lw L ≤ (21 * cL + 26) * Z ^ 2 := by
      calc eCap * bucketWordSpace Lw L ≤ Z * ((21 * cL + 26) * Z) := Nat.mul_le_mul he hbws
        _ = (21 * cL + 26) * Z ^ 2 := by ring
    have hrest : asmFiFrontSpace vCap eCap Lw L ≤ eCap * bucketWordSpace Lw L + 152 * Z := by
      unfold asmFiFrontSpace tourBranchInitSpace tourFixedSize ordArenaSize slotListSpace
      omega
    have hZ152 : 152 * Z ≤ 152 * Z ^ 2 := Nat.mul_le_mul_left 152 hZ12
    have hsum : asmFiFrontSpace vCap eCap Lw L ≤ (21 * cL + 178) * Z ^ 2 := by
      have e : (21 * cL + 178) * Z ^ 2 = (21 * cL + 26) * Z ^ 2 + 152 * Z ^ 2 := by ring
      omega
    exact hsum.trans (Nat.mul_le_mul_left _ hZ2d)
  -- 2. Middle space
  have hPer : 100 * ((depth + 1) * (spV + eCap + 1)) +
      (2 * (36 * (spV + 2 * eCap + 1)) ^ cw + 30 * (eCap + 1) * (g + 1) + 3 * spV +
        dynGraphSize spV eCap + eCap + 10) ≤
      (24777 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 2) := by
    have hZ1m : Z ≤ Z ^ (cw + cγ + 2) := by
      simpa using hpw (a := 1) (b := cw + cγ + 2) (by omega)
    have p1 : 100 * ((depth + 1) * (spV + eCap + 1)) ≤ 23600 * Z ^ (cw + cγ + 2) := by
      have h1 : (depth + 1) * (spV + eCap + 1) ≤ (2 * Z) * (118 * Z) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : 100 * ((2 * Z) * (118 * Z)) = 23600 * Z ^ 2 := by ring
      calc 100 * ((depth + 1) * (spV + eCap + 1)) ≤ 100 * ((2 * Z) * (118 * Z)) :=
            Nat.mul_le_mul_left 100 h1
        _ = 23600 * Z ^ 2 := h2
        _ ≤ 23600 * Z ^ (cw + cγ + 2) := Nat.mul_le_mul_left _ (hpw (by omega))
    have p2 : 2 * (36 * (spV + 2 * eCap + 1)) ^ cw ≤ 2 * 4284 ^ cw * Z ^ (cw + cγ + 2) := by
      have h1 : 36 * (spV + 2 * eCap + 1) ≤ 4284 * Z := by omega
      have h2 : (36 * (spV + 2 * eCap + 1)) ^ cw ≤ 4284 ^ cw * Z ^ cw := by
        rw [← mul_pow]; exact Nat.pow_le_pow_left h1 cw
      calc 2 * (36 * (spV + 2 * eCap + 1)) ^ cw ≤ 2 * (4284 ^ cw * Z ^ cw) :=
            Nat.mul_le_mul_left 2 h2
        _ ≤ 2 * (4284 ^ cw * Z ^ (cw + cγ + 2)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (hpw (by omega)))
        _ = 2 * 4284 ^ cw * Z ^ (cw + cγ + 2) := by ring
    have p3 : 30 * (eCap + 1) * (g + 1) ≤ 60 * (Cγ + 1) * Z ^ (cw + cγ + 2) := by
      have h1c : 1 ≤ Z ^ cγ := Nat.one_le_pow _ _ hZpos
      have hg1 : g + 1 ≤ (Cγ + 1) * Z ^ cγ := by
        have e : (Cγ + 1) * Z ^ cγ = Cγ * Z ^ cγ + Z ^ cγ := by ring
        omega
      calc 30 * (eCap + 1) * (g + 1) ≤ 30 * (2 * Z) * ((Cγ + 1) * Z ^ cγ) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 30 (by omega)) hg1
        _ = 60 * (Cγ + 1) * Z ^ (cγ + 1) := by ring
        _ ≤ 60 * (Cγ + 1) * Z ^ (cw + cγ + 2) := Nat.mul_le_mul_left _ (hpw (by omega))
    have p4 : 3 * spV + dynGraphSize spV eCap + eCap + 10 ≤ 1177 * Z ^ (cw + cγ + 2) := by
      unfold dynGraphSize
      have hlin : 3 * spV + (4 + 7 * spV + 9 * eCap) + eCap + 10 ≤ 1177 * Z := by omega
      exact hlin.trans (Nat.mul_le_mul_left 1177 hZ1m)
    have e : (24777 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 2) =
        23600 * Z ^ (cw + cγ + 2) + 2 * 4284 ^ cw * Z ^ (cw + cγ + 2) +
          60 * (Cγ + 1) * Z ^ (cw + cγ + 2) + 1177 * Z ^ (cw + cγ + 2) := by ring
    omega
  have hMid : 5 * vCap + bundleTableFixedSize eCap eCap + eCap * (3 + 24 * eCap) + 3 * eCap +
      spV + eCap * (6 + 10 * eCap + (4 + spV + 3 * eCap) +
        (100 * ((depth + 1) * (spV + eCap + 1)) +
          (2 * (36 * (spV + 2 * eCap + 1)) ^ cw + 30 * (eCap + 1) * (g + 1) + 3 * spV +
            dynGraphSize spV eCap + eCap + 10))) ≤
      (25084 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 3) := by
    have hq1 : eCap * (3 + 24 * eCap) ≤ 3 * Z + 24 * Z ^ 2 := by
      have h1 : eCap * (3 + 24 * eCap) = 3 * eCap + 24 * (eCap * eCap) := by ring
      have h2 : eCap * eCap ≤ Z ^ 2 := by rw [sq]; exact Nat.mul_le_mul he he
      omega
    have hq2 : eCap * (6 + 10 * eCap + (4 + spV + 3 * eCap)) ≤ 134 * Z ^ 2 := by
      have h1 : 6 + 10 * eCap + (4 + spV + 3 * eCap) ≤ 134 * Z := by omega
      calc eCap * (6 + 10 * eCap + (4 + spV + 3 * eCap)) ≤ Z * (134 * Z) := Nat.mul_le_mul he h1
        _ = 134 * Z ^ 2 := by ring
    have hq3 : eCap * (100 * ((depth + 1) * (spV + eCap + 1)) +
          (2 * (36 * (spV + 2 * eCap + 1)) ^ cw + 30 * (eCap + 1) * (g + 1) + 3 * spV +
            dynGraphSize spV eCap + eCap + 10)) ≤
        (24777 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 3) := by
      calc _ ≤ Z * ((24777 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 2)) :=
            Nat.mul_le_mul he hPer
        _ = (24777 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 3) := by ring
    have hpre : 5 * vCap + bundleTableFixedSize eCap eCap + eCap * (3 + 24 * eCap) + 3 * eCap +
        spV + eCap * (6 + 10 * eCap + (4 + spV + 3 * eCap)) ≤ 307 * Z ^ (cw + cγ + 3) := by
      have hbt : bundleTableFixedSize eCap eCap = 14 + 7 * eCap + 8 * eCap := rfl
      have hlin : 5 * vCap + (14 + 7 * eCap + 8 * eCap) + 3 * Z + 3 * eCap + spV ≤ 149 * Z := by
        omega
      have hZ149 : 149 * Z ≤ 149 * Z ^ 2 := Nat.mul_le_mul_left 149 hZ12
      have h307 : 149 * Z ^ 2 + 24 * Z ^ 2 + 134 * Z ^ 2 ≤ 307 * Z ^ (cw + cγ + 3) := by
        have e : 149 * Z ^ 2 + 24 * Z ^ 2 + 134 * Z ^ 2 = 307 * Z ^ 2 := by ring
        rw [e]; exact Nat.mul_le_mul_left 307 hZ2d
      rw [hbt]; omega
    have hdist : eCap * (6 + 10 * eCap + (4 + spV + 3 * eCap) +
        (100 * ((depth + 1) * (spV + eCap + 1)) +
          (2 * (36 * (spV + 2 * eCap + 1)) ^ cw + 30 * (eCap + 1) * (g + 1) + 3 * spV +
            dynGraphSize spV eCap + eCap + 10))) =
        eCap * (6 + 10 * eCap + (4 + spV + 3 * eCap)) +
        eCap * (100 * ((depth + 1) * (spV + eCap + 1)) +
          (2 * (36 * (spV + 2 * eCap + 1)) ^ cw + 30 * (eCap + 1) * (g + 1) + 3 * spV +
            dynGraphSize spV eCap + eCap + 10)) := Nat.mul_add _ _ _
    have e : (25084 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 3) =
        307 * Z ^ (cw + cγ + 3) +
        (24777 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 3) := by ring
    omega
  -- 3. Back space
  have hBack : rootTblSpace vCap eCap + (7 + dynGraphSize vCap eCap + n + 2 * rb) +
      (4 + Sn + 3 * Sm) + (3 + eCap + embRefreshMul * (er + n + 1)) ≤
      (70 + embRefreshMul * (2 * Cγ + 6)) * Z ^ (cw + cγ + 3) := by
    have hrb2 : 2 * rb ≤ 4 * Z ^ 2 := by
      calc 2 * rb ≤ 2 * (n * (2 * eCap)) := Nat.mul_le_mul_left 2 hrb
        _ ≤ 2 * (Z * (2 * Z)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul (hn.trans he) (by omega))
        _ = 4 * Z ^ 2 := by ring
    have hlin : rootTblSpace vCap eCap + (7 + dynGraphSize vCap eCap + n) + (4 + Sn + 3 * Sm) +
        (3 + eCap) ≤ 66 * Z := by
      unfold rootTblSpace dynGraphSize; omega
    have h66 : 66 * Z + 4 * Z ^ 2 ≤ 70 * Z ^ (cw + cγ + 3) := by
      have h1 : 66 * Z ≤ 66 * Z ^ 2 := Nat.mul_le_mul_left 66 hZ12
      have h2 : 70 * Z ^ 2 ≤ 70 * Z ^ (cw + cγ + 3) := Nat.mul_le_mul_left 70 hZ2d
      omega
    have herB : er + n + 1 ≤ (2 * Cγ + 6) * Z ^ (cw + cγ + 3) := by
      have h1c : 1 ≤ Z ^ cγ := Nat.one_le_pow _ _ hZpos
      have h1c1 : Z ≤ Z ^ (cγ + 1) := by simpa using hpw (a := 1) (b := cγ + 1) (by omega)
      have h1c2 : Z ≤ Z ^ (cγ + 2) := by simpa using hpw (a := 1) (b := cγ + 2) (by omega)
      have he1 : eCap * (2 * g + 3) + 1 ≤ (2 * Cγ + 4) * Z ^ (cγ + 1) := by
        calc eCap * (2 * g + 3) + 1
            ≤ Z * (2 * (Cγ * Z ^ cγ) + 3 * Z ^ cγ) + Z ^ (cγ + 1) := by
              have h3 : 3 ≤ 3 * Z ^ cγ := Nat.le_mul_of_pos_right 3 (by omega)
              have h1' : 1 ≤ Z ^ (cγ + 1) := Nat.one_le_pow _ _ hZpos
              exact Nat.add_le_add (Nat.mul_le_mul he (by omega)) h1'
          _ = (2 * Cγ + 4) * Z ^ (cγ + 1) := by ring
      have her1 : er ≤ (2 * Cγ + 4) * Z ^ (cγ + 2) := by
        calc er ≤ n * (eCap * (2 * g + 3) + 1) := her
          _ ≤ Z * ((2 * Cγ + 4) * Z ^ (cγ + 1)) := Nat.mul_le_mul (hn.trans he) he1
          _ = (2 * Cγ + 4) * Z ^ (cγ + 2) := by ring
      have hn1 : n + 1 ≤ 2 * Z ^ (cγ + 2) := by omega
      have htot : er + n + 1 ≤ (2 * Cγ + 6) * Z ^ (cγ + 2) := by
        have e : (2 * Cγ + 6) * Z ^ (cγ + 2) =
            (2 * Cγ + 4) * Z ^ (cγ + 2) + 2 * Z ^ (cγ + 2) := by ring
        omega
      exact htot.trans (Nat.mul_le_mul_left _ (hpw (by omega)))
    have hemb : embRefreshMul * (er + n + 1) ≤
        embRefreshMul * (2 * Cγ + 6) * Z ^ (cw + cγ + 3) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left embRefreshMul herB
    have e : (70 + embRefreshMul * (2 * Cγ + 6)) * Z ^ (cw + cγ + 3) =
        70 * Z ^ (cw + cγ + 3) + embRefreshMul * (2 * Cγ + 6) * Z ^ (cw + cγ + 3) := by ring
    omega
  -- Combine front, middle, and back
  have hcL : (21 * cL + 178) * Z ^ (cw + cγ + 3) ≤ (84 * cL + 178) * Z ^ (cw + cγ + 3) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (84 * cL + 25332 + 2 * 4284 ^ cw + 60 * (Cγ + 1) + embRefreshMul * (2 * Cγ + 6)) *
      Z ^ (cw + cγ + 3) =
      (84 * cL + 178) * Z ^ (cw + cγ + 3) +
      (25084 + 2 * 4284 ^ cw + 60 * (Cγ + 1)) * Z ^ (cw + cγ + 3) +
      (70 + embRefreshMul * (2 * Cγ + 6)) * Z ^ (cw + cγ + 3) := by ring
  omega

/-- **The total heap space of the build of a branch at its init is polynomial.**
For any `S5 : Fin eCap → Option BundleState` and `n ≤ eCap` whose listed slot graphs meet
`SpanGraphOK (asmFiSP impl w M depth k eCap)`, the sum `asmFiFrontSpace + asmFiMidSpace +
asmFiBackSpace` is at most `(asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval X`, where
`X = M + N + k + vCap + eCap + L + depth`. -/
theorem asmFiBuildSpace_le_poly {impl : SparsifyImpl} {Cγ cγ capExp w M N k vCap eCap L depth Lw
    n : ℕ} {S5 : Fin eCap → Option BundleState} {S : MGraph}
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ) (hk : 1 ≤ k)
    (hLw : Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1))
    (hSn : S.n ≤ N) (hSm : S.m ≤ M) (hn : n ≤ eCap)
    (hok : ∀ s ∈ List.range n,
      SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)) :
    asmFiFrontSpace vCap eCap Lw L +
      asmFiMidSpace (asmFiSP impl w M depth k eCap) vCap eCap +
      asmFiBackSpace (asmFiSP impl w M depth k eCap)
        (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
          (List.range n)) (List.range n) vCap eCap S ≤
    (asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval (M + N + k + vCap + eCap + L + depth) := by
  set SP := asmFiSP impl w M depth k eCap with hSP
  set Z := M + N + k + vCap + eCap + L + depth + 2 with hZdef
  set cL := capExp + sparseCoreReadout2LimbConst + 1 with hcLdef
  have hZ : 2 ≤ Z := by omega
  have hLw1 : Lw + 1 ≤ cL * Z := limbs_succ_le_B (by omega) (by omega) hLw
  have hspB : bundleSplitBudget k M ≤ 112 * M + 2 := bundleSplitBudget_le_linear hk
  have hspV : SP.vCap ≤ 116 * Z := by
    show 2 * eCap + bundleSplitBudget k M + 1 ≤ 116 * Z
    omega
  have hg : ⌈impl.γ_ℓ M⌉₊ ≤ Cγ * Z ^ cγ :=
    (hγ M).trans (Nat.mul_le_mul_left Cγ (Nat.pow_le_pow_left (by omega) cγ))
  have hrb : rebuildSize SP
      (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
        (List.range n)) (List.range n) ≤ n * (2 * eCap) :=
    rebuildSize_spanAfter_init_le SP S5 hn hok
  have her : embRefreshSizeAt SP
      (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
        (List.range n)) (List.range n) ≤ n * (eCap * (2 * ⌈impl.γ_ℓ M⌉₊ + 3) + 1) :=
    embRefreshSizeAt_spanAfter_init_le SP S5 hn hok
  have hmain := asmFiBuildSpace_arith (Z := Z) (cw := impl.cw) (Cγ := Cγ) (cγ := cγ) (cL := cL)
    (vCap := vCap) (eCap := eCap) (Lw := Lw) (L := L) (depth := depth) (spV := SP.vCap)
    (g := ⌈impl.γ_ℓ M⌉₊) (n := n) (Sn := S.n) (Sm := S.m)
    hZ (by omega) (by omega) (by omega) (by omega) (by omega) hspV hg hn
    (by omega) (by omega) hrb her
  have hL_eq : SP.L = depth := rfl
  have he_eq : SP.eCap = eCap := rfl
  have hi_eq : SP.impl = impl := rfl
  have hm_eq : SP.mMax = M := rfl
  change asmFiFrontSpace vCap eCap Lw L +
    (5 * vCap + bundleTableFixedSize eCap eCap + eCap * (3 + 24 * eCap) + 3 * eCap + SP.vCap +
      eCap * (6 + 10 * SP.eCap + (4 + SP.vCap + 3 * SP.eCap) +
        (100 * ((SP.L + 1) * (SP.vCap + SP.eCap + 1)) +
          (2 * (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ SP.impl.cw +
            30 * (SP.eCap + 1) * (⌈SP.impl.γ_ℓ SP.mMax⌉₊ + 1) + 3 * SP.vCap +
            dynGraphSize SP.vCap SP.eCap + SP.eCap + 10)))) +
    (rootTblSpace vCap eCap +
      (7 + dynGraphSize vCap eCap + (List.range n).length +
        2 * rebuildSize SP (spanAfter (fun _ => none : BucketSpannerState eCap)
          (asmFirstInitSlotGraph S5) (List.range n)) (List.range n)) +
      (4 + S.n + 3 * S.m) +
      (3 + eCap + embRefreshMul * (embRefreshSizeAt SP
        (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
          (List.range n)) (List.range n) + (List.range n).length + 1))) ≤
    (84 * cL + 25332 + 2 * 4284 ^ impl.cw + 60 * (Cγ + 1) + embRefreshMul * (2 * Cγ + 6)) *
      Z ^ (impl.cw + cγ + 3)
  rw [hL_eq, he_eq, hi_eq, hm_eq, List.length_range]
  exact hmain

/-! ## Word-size corollaries from the space polynomial -/

/-- **All word-size bounds of the build follow from `h + (asmFiBuildSpacePoly …).eval X < 2 ^ w`.**
In particular, this gives `10 ≤ w`, `(vCap + eCap + 2) ^ 2 < 2 ^ w`, `56 * M + k < 2 ^ w`,
`depth < 2 ^ w`, the spanner cap and sparsifier word bounds for `initTree_spanGraphOK` (even when
`eCap = 0`), and — given `P ≤ 4 * L` — the key-base bounds `asmFirstInitKeyBase P Lw L < 2 ^ w`
and `vCap * asmFirstInitKeyBase P Lw L < 2 ^ w`. -/
theorem asmFiBuildSpace_word_bounds {impl : SparsifyImpl} {Cγ cγ capExp w h M N k vCap eCap L
    depth P Lw : ℕ}
    (hk : 1 ≤ k) (hP : P ≤ 4 * L)
    (hLw : Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1))
    (hsp : h + (asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval
      (M + N + k + vCap + eCap + L + depth) < 2 ^ w) :
    let SP := asmFiSP impl w M depth k eCap
    10 ≤ w ∧
    (vCap + eCap + 2) ^ 2 < 2 ^ w ∧
    56 * M + k < 2 ^ w ∧
    depth < 2 ^ w ∧
    SP.vCap + SP.eCap + 2 < 2 ^ w ∧
    2 * (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ impl.cw < 2 ^ w ∧
    asmFirstInitKeyBase P Lw L < 2 ^ w ∧
    vCap * asmFirstInitKeyBase P Lw L < 2 ^ w := by
  intro SP
  set Z := M + N + k + vCap + eCap + L + depth + 2 with hZdef
  set cL := capExp + sparseCoreReadout2LimbConst + 1 with hcLdef
  set K := (asmFiBuildSpacePoly impl.cw Cγ cγ capExp).coeff with hKdef
  have hZ : 2 ≤ Z := by omega
  have hZpos : 0 < Z := by omega
  have hEv : (asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval
      (M + N + k + vCap + eCap + L + depth) = K * Z ^ (impl.cw + cγ + 3) := rfl
  have hEvLt : K * Z ^ (impl.cw + cγ + 3) < 2 ^ w := by rw [← hEv]; omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → Z ^ a ≤ Z ^ b := fun h => Nat.pow_le_pow_right hZpos h
  have h1d : 1 ≤ Z ^ (impl.cw + cγ + 3) := Nat.one_le_pow _ _ hZpos
  have hZd : Z ≤ Z ^ (impl.cw + cγ + 3) := by
    simpa using hpw (a := 1) (b := impl.cw + cγ + 3) (by omega)
  have hZ2d : Z ^ 2 ≤ Z ^ (impl.cw + cγ + 3) := hpw (by omega)
  have hK25 : 25332 ≤ K := by dsimp only [K, asmFiBuildSpacePoly]; omega
  have hKcw : 2 * 4284 ^ impl.cw ≤ K := by dsimp only [K, asmFiBuildSpacePoly]; omega
  have hKcL : 84 * cL + 122 ≤ K := by dsimp only [K, asmFiBuildSpacePoly]; omega
  have hspB : bundleSplitBudget k M ≤ 112 * M + 2 := bundleSplitBudget_le_linear hk
  have hspV : SP.vCap ≤ 116 * Z := by
    show 2 * eCap + bundleSplitBudget k M + 1 ≤ 116 * Z
    omega
  -- 1. `10 ≤ w`
  have hw10 : 10 ≤ w := by
    have h210 : 2 ^ 10 < 2 ^ w := by
      have h1 : 2 ^ 10 ≤ K := by norm_num; omega
      have h2 : K ≤ K * Z ^ (impl.cw + cγ + 3) := Nat.le_mul_of_pos_right K (by omega)
      omega
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h210)
  -- 2. `(vCap + eCap + 2) ^ 2 < 2 ^ w`
  have hwsq : (vCap + eCap + 2) ^ 2 < 2 ^ w := by
    have h1 : (vCap + eCap + 2) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : Z ^ 2 ≤ K * Z ^ (impl.cw + cγ + 3) :=
      hZ2d.trans (Nat.le_mul_of_pos_left _ (by omega))
    omega
  -- 3. `56 * M + k < 2 ^ w`
  have hMw : 56 * M + k < 2 ^ w := by
    have h1 : 56 * M + k ≤ 56 * Z := by omega
    have h2 : 56 * Z ≤ K * Z ^ (impl.cw + cγ + 3) := Nat.mul_le_mul (by omega) hZd
    omega
  -- 4. `depth < 2 ^ w`
  have hdw : depth < 2 ^ w := by
    have h1 : depth ≤ Z := by omega
    have h2 : Z ≤ K * Z ^ (impl.cw + cγ + 3) := hZd.trans (Nat.le_mul_of_pos_left _ (by omega))
    omega
  -- 5. `SP.vCap + SP.eCap + 2 < 2 ^ w`
  have hSPcap : SP.vCap + SP.eCap + 2 < 2 ^ w := by
    have h1 : SP.vCap + SP.eCap + 2 ≤ 118 * Z := by
      show SP.vCap + eCap + 2 ≤ 118 * Z; omega
    have h2 : 118 * Z ≤ K * Z ^ (impl.cw + cγ + 3) := Nat.mul_le_mul (by omega) hZd
    omega
  -- 6. `2 * (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ impl.cw < 2 ^ w`
  have hSPcw : 2 * (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ impl.cw < 2 ^ w := by
    have h1 : 36 * (SP.vCap + 2 * SP.eCap + 1) ≤ 4284 * Z := by
      show 36 * (SP.vCap + 2 * eCap + 1) ≤ 4284 * Z; omega
    have h2 : (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ impl.cw ≤ 4284 ^ impl.cw * Z ^ impl.cw := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left h1 impl.cw
    have h3 : 2 * (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ impl.cw ≤
        K * Z ^ (impl.cw + cγ + 3) := by
      calc 2 * (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ impl.cw
          ≤ 2 * (4284 ^ impl.cw * Z ^ impl.cw) := Nat.mul_le_mul_left 2 h2
        _ = (2 * 4284 ^ impl.cw) * Z ^ impl.cw := by ring
        _ ≤ K * Z ^ (impl.cw + cγ + 3) := Nat.mul_le_mul hKcw (hpw (by omega))
    omega
  -- 7 & 8. Key base bounds
  have hLw1 : Lw + 1 ≤ cL * Z := limbs_succ_le_B (by omega) (by omega) hLw
  have hB : asmFirstInitKeyBase P Lw L ≤ (42 * cL + 61) * Z := by
    unfold asmFirstInitKeyBase
    have e : (42 * cL + 61) * Z = 42 * (cL * Z) + 61 * Z := by ring
    omega
  have hKvB : (vCap + 1) * asmFirstInitKeyBase P Lw L ≤ K * Z ^ (impl.cw + cγ + 3) := by
    calc (vCap + 1) * asmFirstInitKeyBase P Lw L
        ≤ (2 * Z) * ((42 * cL + 61) * Z) := Nat.mul_le_mul (by omega) hB
      _ = (84 * cL + 122) * Z ^ 2 := by ring
      _ ≤ K * Z ^ (impl.cw + cγ + 3) := Nat.mul_le_mul hKcL hZ2d
  have hBw : asmFirstInitKeyBase P Lw L < 2 ^ w := by
    have h1 : asmFirstInitKeyBase P Lw L ≤ (vCap + 1) * asmFirstInitKeyBase P Lw L :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hkw : vCap * asmFirstInitKeyBase P Lw L < 2 ^ w := by
    have h1 : vCap * asmFirstInitKeyBase P Lw L ≤ (vCap + 1) * asmFirstInitKeyBase P Lw L :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  exact ⟨hw10, hwsq, hMw, hdw, hSPcap, hSPcw, hBw, hkw⟩

end MinCostFlow.SparseCore.Program
