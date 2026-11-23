module

public import MinCostFlow.SparseCore.Program.AssemblyBranchFull
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartSpace
import Mathlib.Tactic.Ring

/-!
# A polynomial bound on the space of the restart of a branch (`AssemblyBranchRestartPoly`)

The clause `restart_runs` of `AsmBranchAt` bounds the heap space of a restart by a polynomial
`S.restartSpace capExp` in `X = M + N + k + vCap + eCap + L + depth`, fixed before the instance.
This file gives such a polynomial, `asmBrRestartPoly`, and proves that the heap space
`asmBrRestartSpace` of the restart is at most its value at `X` (`asmBrRestartSpace_le_poly`).

**The route.** Let `B = (X + 2) ^ (capExp + 1)`. Every size that the space depends on is at most
a polynomial in `B` with a degree free of the instance:
* the caps `vCap`, `eCap`, the depth and the edges of the core graph are at most `X + 2 ≤ B`;
* the caps of the spanners: `spV + spE + 2 ≤ (M + N + 2) ^ capExp ≤ B` (the cap hypothesis of the
  bundle side);
* the caps `tCap` and `slotCap` are at most `2 (vCap + eCap + 2) ^ 2 ≤ 2 B ^ 2` (the full
  representation), and the slot list has at most `slotCap` slots;
* the limb count: `L_w + 1 ≤ (capExp + 129) · B` (the limb bound of the representation);
* the walk length bound: `⌈γ_ℓ mMax⌉ ≤ ⌈γ_ℓ M⌉ ≤ Cγ · B ^ cγ`. The first step holds because the
  spanner parameters of the program are at most those of the model (`SparsifyParamsLe` of the
  bundle side), and those of the model are at most the parameters at `m₀ = M` (the full
  representation). The second step is the hypothesis `SparsifyPolyStretch` on `impl`.
Then each of the five terms of the space is at most a constant times `B ^ (cw + cγ + 4)`
(`asmBrRestart_arith`), where `cw` is the word exponent of the cited sparsifier. This is
`(X + 2) ^ ((capExp + 1) (cw + cγ + 4))`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The polynomial bound on the heap space of the restart of a branch**, for P5's multiplier
`bunMul`, P10's multiplier `readMul`, the refresh multiplier `embMul`, the space `qSpace` of one
query of the tour, the word exponent `cw` of the sparsifier, the stretch bound `Cγ · (m + 2) ^ cγ`
and the cap exponent `capExp`. -/
def asmBrRestartPoly (bunMul readMul embMul qSpace cw Cγ cγ capExp : ℕ) : PolyBound where
  coeff := 12 * bunMul + 2 * (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) +
    10 * readMul * (capExp + sparseCoreReadout2LimbConst + 1) + (4 * qSpace + 1) +
    embMul * (4 * Cγ + 11)
  deg := (capExp + 7) * (cw + cγ + 4)

/-- **The arithmetic of the bound.** When every size is at most a polynomial in `B ≥ 2` as in
the module docstring, the five terms of the space of a restart (P5's restart, the spanner
initializations, P10's rebuild, P7's reset and the refresh) add up to at most a constant times
`B ^ (cw + cγ + 4)`. -/
theorem asmBrRestart_arith {B bunMul readMul embMul qS cw Cγ cγ cL : ℕ} (hB : 2 ≤ B)
    {bunS slotCap m len vC eC tC Lw depth spV spE g rb er sumSpan : ℕ}
    (hbun : bunS ≤ bunMul * (slotCap + 1) * (m + len + 1))
    (hslotCap : slotCap ≤ 2 * B ^ 2) (hm : m ≤ B) (hlen : len ≤ slotCap) (hvC : vC ≤ B)
    (heC : eC ≤ B) (htC : tC ≤ 2 * B ^ 2) (hLw : Lw + 1 ≤ cL * B) (hsp : spV + spE + 2 ≤ B)
    (hdepth : depth + 1 ≤ B) (hg : g ≤ Cγ * B ^ cγ) (hrb : rb ≤ len * (2 * spE))
    (her : er ≤ len * (spE * (2 * g + 3) + 1))
    (hspan : sumSpan ≤ len * (100 * ((depth + 1) * (spV + spE + 1)) +
      (2 * (36 * (spV + 2 * spE + 1)) ^ cw + 30 * (spE + 1) * (g + 1) + 3 * spV +
        dynGraphSize spV spE + spE + 10))) :
    bunS + sumSpan + readMul * (vC + tC + (rb + len) + 1) * (Lw + 1) +
        (2 * (2 * eC) * qS + 1) + embMul * (er + len + 1) ≤
      (12 * bunMul + 2 * (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) + 10 * readMul * cL +
        (4 * qS + 1) + embMul * (4 * Cγ + 11)) * B ^ (cw + cγ + 4) := by
  have hBpos : 0 < B := by omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → B ^ a ≤ B ^ b := fun h => Nat.pow_le_pow_right hBpos h
  have hB2 : B ≤ B ^ 2 := Nat.le_self_pow (by norm_num) B
  have h1B2 : 1 ≤ B ^ 2 := Nat.one_le_pow _ _ hBpos
  have hBD : B ≤ B ^ (cw + cγ + 4) := by simpa using hpw (a := 1) (b := cw + cγ + 4) (by omega)
  -- P5's restart
  have hT1 : bunS ≤ 12 * bunMul * B ^ (cw + cγ + 4) := by
    have e1 : slotCap + 1 ≤ 3 * B ^ 2 := by omega
    have e2 : m + len + 1 ≤ 4 * B ^ 2 := by omega
    calc bunS ≤ bunMul * (slotCap + 1) * (m + len + 1) := hbun
      _ ≤ bunMul * (3 * B ^ 2) * (4 * B ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) e2
      _ = 12 * bunMul * B ^ 4 := by ring
      _ ≤ 12 * bunMul * B ^ (cw + cγ + 4) := Nat.mul_le_mul_left _ (hpw (by omega))
  -- the spanner initializations
  have hPer : 100 * ((depth + 1) * (spV + spE + 1)) +
      (2 * (36 * (spV + 2 * spE + 1)) ^ cw + 30 * (spE + 1) * (g + 1) + 3 * spV +
        dynGraphSize spV spE + spE + 10) ≤
      (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 2) := by
    have hE : B ≤ B ^ (cw + cγ + 2) := by simpa using hpw (a := 1) (b := cw + cγ + 2) (by omega)
    have p1 : 100 * ((depth + 1) * (spV + spE + 1)) ≤ 100 * B ^ (cw + cγ + 2) := by
      have h1 : (depth + 1) * (spV + spE + 1) ≤ B * B := Nat.mul_le_mul hdepth (by omega)
      have h2 : B * B ≤ B ^ (cw + cγ + 2) := by rw [← pow_two]; exact hpw (by omega)
      omega
    have p2 : 2 * (36 * (spV + 2 * spE + 1)) ^ cw ≤ 2 * 72 ^ cw * B ^ (cw + cγ + 2) := by
      have h1 : 36 * (spV + 2 * spE + 1) ≤ 72 * B := by omega
      have h2 : (36 * (spV + 2 * spE + 1)) ^ cw ≤ 72 ^ cw * B ^ cw := by
        rw [← mul_pow]; exact Nat.pow_le_pow_left h1 cw
      calc 2 * (36 * (spV + 2 * spE + 1)) ^ cw ≤ 2 * (72 ^ cw * B ^ cw) :=
            Nat.mul_le_mul_left 2 h2
        _ ≤ 2 * (72 ^ cw * B ^ (cw + cγ + 2)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (hpw (by omega)))
        _ = 2 * 72 ^ cw * B ^ (cw + cγ + 2) := by ring
    have p3 : 30 * (spE + 1) * (g + 1) ≤ 30 * (Cγ + 1) * B ^ (cw + cγ + 2) := by
      have hc : 1 ≤ B ^ cγ := Nat.one_le_pow _ _ hBpos
      have h1 : g + 1 ≤ (Cγ + 1) * B ^ cγ := by
        calc g + 1 ≤ Cγ * B ^ cγ + B ^ cγ := by omega
          _ = (Cγ + 1) * B ^ cγ := by ring
      calc 30 * (spE + 1) * (g + 1) ≤ 30 * B * ((Cγ + 1) * B ^ cγ) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 30 (by omega)) h1
        _ = 30 * (Cγ + 1) * B ^ (cγ + 1) := by ring
        _ ≤ 30 * (Cγ + 1) * B ^ (cw + cγ + 2) := Nat.mul_le_mul_left _ (hpw (by omega))
    have p4 : 3 * spV + dynGraphSize spV spE + spE + 10 ≤ 10 * B ^ (cw + cγ + 2) := by
      unfold dynGraphSize; omega
    have e : (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 2) =
        100 * B ^ (cw + cγ + 2) + 2 * 72 ^ cw * B ^ (cw + cγ + 2) +
          30 * (Cγ + 1) * B ^ (cw + cγ + 2) + 10 * B ^ (cw + cγ + 2) := by ring
    omega
  have hT2 : sumSpan ≤ 2 * (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 4) := by
    calc sumSpan ≤ _ := hspan
      _ ≤ (2 * B ^ 2) * ((110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 2)) :=
          Nat.mul_le_mul (by omega) hPer
      _ = 2 * (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 4) := by ring
  -- P10's rebuild
  have hT3 : readMul * (vC + tC + (rb + len) + 1) * (Lw + 1) ≤
      10 * readMul * cL * B ^ (cw + cγ + 4) := by
    have hB3 : B ^ 2 ≤ B ^ 3 := hpw (by omega)
    have h1B3 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hBpos
    have hrb' : rb ≤ 4 * B ^ 3 := by
      calc rb ≤ len * (2 * spE) := hrb
        _ ≤ (2 * B ^ 2) * (2 * B) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4 * B ^ 3 := by ring
    have e1 : vC + tC + (rb + len) + 1 ≤ 10 * B ^ 3 := by omega
    calc readMul * (vC + tC + (rb + len) + 1) * (Lw + 1) ≤ readMul * (10 * B ^ 3) * (cL * B) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) hLw
      _ = 10 * readMul * cL * B ^ 4 := by ring
      _ ≤ 10 * readMul * cL * B ^ (cw + cγ + 4) := Nat.mul_le_mul_left _ (hpw (by omega))
  -- P7's reset
  have hT4 : 2 * (2 * eC) * qS + 1 ≤ (4 * qS + 1) * B ^ (cw + cγ + 4) := by
    have h1 : eC * qS ≤ B ^ (cw + cγ + 4) * qS := Nat.mul_le_mul_right qS (heC.trans hBD)
    have h2 : 2 * (2 * eC) * qS = 4 * (eC * qS) := by ring
    have h3 : (4 * qS + 1) * B ^ (cw + cγ + 4) =
        4 * (B ^ (cw + cγ + 4) * qS) + B ^ (cw + cγ + 4) := by ring
    omega
  -- the refresh
  have hT5 : embMul * (er + len + 1) ≤ embMul * (4 * Cγ + 11) * B ^ (cw + cγ + 4) := by
    have hb1 : B ≤ B ^ (cγ + 1) := by simpa using hpw (a := 1) (b := cγ + 1) (by omega)
    have hc1 : spE * (2 * g + 3) + 1 ≤ (2 * Cγ + 4) * B ^ (cγ + 1) := by
      calc spE * (2 * g + 3) + 1 ≤ B * (2 * (Cγ * B ^ cγ) + 3) + B :=
            Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
        _ = 2 * Cγ * B ^ (cγ + 1) + 4 * B := by ring
        _ ≤ 2 * Cγ * B ^ (cγ + 1) + 4 * B ^ (cγ + 1) := by omega
        _ = (2 * Cγ + 4) * B ^ (cγ + 1) := by ring
    have her' : er ≤ 2 * (2 * Cγ + 4) * B ^ (cγ + 3) := by
      calc er ≤ len * (spE * (2 * g + 3) + 1) := her
        _ ≤ (2 * B ^ 2) * ((2 * Cγ + 4) * B ^ (cγ + 1)) := Nat.mul_le_mul (by omega) hc1
        _ = 2 * (2 * Cγ + 4) * B ^ (cγ + 3) := by ring
    have hl : len + 1 ≤ 3 * B ^ (cγ + 3) := by
      have : B ^ 2 ≤ B ^ (cγ + 3) := hpw (by omega)
      omega
    have e : er + len + 1 ≤ (4 * Cγ + 11) * B ^ (cγ + 3) := by
      have : (4 * Cγ + 11) * B ^ (cγ + 3) =
          2 * (2 * Cγ + 4) * B ^ (cγ + 3) + 3 * B ^ (cγ + 3) := by ring
      omega
    calc embMul * (er + len + 1) ≤ embMul * ((4 * Cγ + 11) * B ^ (cγ + 3)) :=
          Nat.mul_le_mul_left _ e
      _ ≤ embMul * ((4 * Cγ + 11) * B ^ (cw + cγ + 4)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hpw (by omega)))
      _ = embMul * (4 * Cγ + 11) * B ^ (cw + cγ + 4) := by ring
  have e : (12 * bunMul + 2 * (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) + 10 * readMul * cL +
        (4 * qS + 1) + embMul * (4 * Cγ + 11)) * B ^ (cw + cγ + 4) =
      12 * bunMul * B ^ (cw + cγ + 4) +
        2 * (110 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 4) +
        10 * readMul * cL * B ^ (cw + cγ + 4) + (4 * qS + 1) * B ^ (cw + cγ + 4) +
        embMul * (4 * Cγ + 11) * B ^ (cw + cγ + 4) := by ring
  omega

/-- **The heap space of the restart of a branch is polynomial.** Let the branch hold
`⟨tr, ord, vCap, eCap⟩` in the full representation, with `tr.m₀ = M`, `tr.n₀ = N` and the edges of
the core graph below `eCap`. Let P5's space be at most `bunMul · (slotCap + 1) · (n + 1)` (as
`AsmBrBunAt.space_le` gives), and let the sparsifier meet the stretch bound
`⌈γ_ℓ m⌉ ≤ Cγ · (m + 2) ^ cγ` (`SparsifyPolyStretch`). Then the heap space of the restart is at
most `asmBrRestartPoly` at `M + N + k + vCap + eCap + L + depth`, for every `k`. -/
theorem asmBrRestartSpace_le_poly {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {Cγ cγ : ℕ} (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ)
    {Ψ : BundleTreeState depth → ℕ} {bunSpace : ℕ → ℕ → ℕ} {bunMul : ℕ}
    (hbun : ∀ slotCap n, bunSpace slotCap n ≤ bunMul * (slotCap + 1) * (n + 1))
    (readMul embMul : ℕ) (OS : OutTourSpec)
    {b k M N vCap eCap : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ} {mem : ℕ → ℕ}
    (hrep : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).rep b
      ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hGE : ∀ e ∈ tr.cs.G.E, e < eCap) :
    asmBrRestartSpace (bunSpace x.xRest.slotCap) readMul embMul OS (asmBrSP impl w depth x.xRest)
        x.xRest.bunS x.xRest.spanS tr.cs ord tr.k x.xRest.slots x.vCap x.eCap x.tCap x.L_w ≤
      (asmBrRestartPoly bunMul readMul embMul OS.querySpace impl.cw Cγ cγ capExp).eval
        (M + N + k + vCap + eCap + L + depth) := by
  obtain ⟨hrepA, -, -, hvc, hec, htc, hsc, -, hγs⟩ := hrep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hXr, -, hcap, hLw, -⟩ :=
    hrepA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmod⟩ := hXr
  obtain ⟨hMap, -, -, -, hok, -, -, hPle, -, -, hCapS, -, -⟩ := hmod
  dsimp only at hvc hec hcap hLw hγs hMap hok hPle hCapS
  set y := x.xRest
  set SP := asmBrSP impl w depth y
  set Z := M + N + k + vCap + eCap + L + depth + 2
  set B := Z ^ (capExp + 7)
  have hZ : 2 ≤ Z := by omega
  have hZB : Z ≤ B := Nat.le_self_pow (by omega) Z
  have hB : 2 ≤ B := hZ.trans hZB
  have hMN : (M + N + 2) ^ (capExp + 7) ≤ B :=
    Nat.pow_le_pow_left (show M + N + 2 ≤ Z by omega) (capExp + 7)
  have hcap' : x.vCap + x.eCap + 2 ≤ Z := by rw [hvc, hec]; omega
  have hsq : 2 * (x.vCap + x.eCap + 2) ^ 2 ≤ 2 * B ^ 2 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hcap'.trans hZB) 2)
  have hspE : y.spV + y.spE + 2 ≤ B := by
    have h := hCapS.1
    rw [hM, hN] at h
    exact h.trans hMN
  have hslotCap : y.slotCap ≤ 2 * B ^ 2 := hsc.trans hsq
  have hlen : y.slots.length ≤ y.slotCap := slots_length_le_slotCap hMap
  have hm : tr.cs.G.m ≤ B := by
    have := card_le_of_forall_mem_lt hGE
    unfold MGraph.m; omega
  have hLw' : x.L_w + 1 ≤ (capExp + sparseCoreReadout2LimbConst + 1) * B := by
    have hlog : Nat.log 2 (M + N + 2) + 1 ≤ Z := by
      have := Nat.log_lt_self 2 (show M + N + 2 ≠ 0 by omega); omega
    have hLw2 : x.L_w ≤
        L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) := by
      rw [← hM, ← hN]; exact hLw
    have h1 := Nat.mul_le_mul_left (capExp + sparseCoreReadout2LimbConst) hlog
    have h2 : (capExp + sparseCoreReadout2LimbConst + 1) * Z ≤
        (capExp + sparseCoreReadout2LimbConst + 1) * B := Nat.mul_le_mul_left _ hZB
    have h3 : (capExp + sparseCoreReadout2LimbConst + 1) * Z =
        (capExp + sparseCoreReadout2LimbConst) * Z + Z := by ring
    omega
  have hg : ⌈impl.γ_ℓ y.mMax⌉₊ ≤ Cγ * B ^ cγ := by
    have h1 : impl.γ_ℓ y.mMax ≤ impl.γ_ℓ M := by
      have h := hPle.2.1
      have h' : tr.spanParams.γ_ℓ ≤ impl.γ_ℓ tr.m₀ := hγs
      rw [hM] at h'
      exact h.trans h'
    refine (Nat.ceil_mono h1).trans ((hγ M).trans (Nat.mul_le_mul_left _ ?_))
    exact Nat.pow_le_pow_left ((show M + 2 ≤ Z by omega).trans hZB) cγ
  have hok' : ∀ s ∈ y.slots, s < y.cap ∧
      SpanGraphOK SP (restartSlotGraph y.bunS tr.cs ord tr.k s) :=
    fun s hs => ⟨(hMap.2.2.2.2 s hs).2, hok s hs⟩
  have hrb := rebuildSize_restartSpanState_le SP y.spanS y.bunS tr.cs ord tr.k y.slots hok'
  have her := embRefreshSizeAt_restartSpanState_le SP y.spanS y.bunS tr.cs ord tr.k y.slots hok'
  have hspan := sum_map_le_length_mul y.slots
    (fun s => spanActivateSpace SP (restartSlotGraph y.bunS tr.cs ord tr.k s)) _
    (fun s hs => spanActivateSpace_le_caps SP (hok s hs))
  have hmain := asmBrRestart_arith (qS := OS.querySpace) (cw := impl.cw) (embMul := embMul)
    (readMul := readMul) hB (hbun y.slotCap (tr.cs.G.m + y.slots.length)) hslotCap hm hlen
    (show x.vCap ≤ B by omega) (show x.eCap ≤ B by omega) (htc.trans hsq) hLw' hspE
    (show depth + 1 ≤ B by omega) hg hrb her hspan
  unfold asmBrRestartSpace asmBrP8Space asmBrEmbBound readSpace outResetSpace PolyBound.eval
    asmBrRestartPoly
  rw [pow_mul]
  exact hmain

end MinCostFlow.SparseCore.Program
