module

public import WordRAM.Contract
public import MinCostFlow.ExpanderDecomp.OneShotProgLayout
public import MinCostFlow.ExpanderDecomp.ProgStepCSpec
import Mathlib.Tactic.Linarith

/-!
# Step B Word-RAM Contracts (`ProgStepBSpec`)

States the standalone deterministic Word-RAM contracts for Step B of `OneShot` (the parallel
block cut-matching game and complement injection, `OneShotStepB.lean`) and its recursive
sub-core callee (`coreOn` at level `q - 1`), aligned directly with `OneShot`'s calling
convention (`OneShotProgLayout.lean`):

* `stepBSpace`: heap-space bound `100 * N * L * Sprev + S_B * ((n + 3) ^ 4 * L + N ^ (q + 1) * L ^ 8)`,
  accounting for at most `100 * N * L` sub-core calls of space `Sprev` and at most `49 * L + 2`
  calls to `multiPairRouterContract` (each needing `outerRouterSpace C_sp G.n rcost`).
* `stepBCostBound`: step-count bound `100 * N * L * Tprev + K_B * N ^ (q + 1) * L ^ 8` (identical
  to `OneShot`'s `oneShotStepBCost`).
* `stepBSubCoreContract`: contract for the recursive `coreOn` subprocedure called by Step B on
  each active block's witness graph at level `q - 1` (identical in arguments, layouts, and
  postconditions to `CoreProgPeel.coreOnContract` specialized to level `q - 1`).
* `stepBContract`: contract for Step B (`args = [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr,
  fAddr, outAddr, h]`), matching `OneShot`'s `oneShotStepBContract` in arguments, layouts,
  postcondition, and cost, with the minimal space adjustment `(N + 3) ^ 4 * N ^ (q + 1) * L ^ 8`
  replaced by `(G.n + 3) ^ 4 * L + N ^ (q + 1) * L ^ 8` required by `outerRouterSpace`.
* `stepBContract_router_space_counterexample` and `stepBContract_relabel_space_counterexample`:
  explicit counterexamples showing that `(N + 3) ^ 4 * N ^ (q + 1) * L ^ 8` cannot cover
  `outerRouterSpace C_sp G.n rcost` (neither directly on `G` nor after relabeling `G` to `k = N ^ 2`
  vertices).
* `stepBSubCoreContract_pre_example` and `stepBContract_pre_example`: non-vacuity witnesses.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Space and Cost Envelopes for Step B -/

/-- Heap-space advance and headroom bound for Step B at level `q` on an `n`-vertex host graph,
given per-call space bound `Sprev` for `coreOn` at level `q - 1`. -/
def stepBSpace (S_B n N L q Sprev : ℕ) : ℕ :=
  100 * N * L * Sprev + S_B * ((n + 3) ^ 4 * L + N ^ (q + 1) * L ^ 8)

/-- Step-count bound for Step B at level `q`, given per-call step bound `Tprev` for `coreOn`
at level `q - 1` (identical to `OneShot`'s `oneShotStepBCost`). -/
def stepBCostBound (K_B N L q Tprev : ℕ) : ℕ :=
  100 * N * L * Tprev + K_B * N ^ (q + 1) * L ^ 8

/-! ## 2. Sub-Core Callee Contract (`stepBSubCoreContract`) -/

/-- Contract for the recursive `coreOn` callee invoked by Step B at level `q'` (`q' = q - 1`).
Args: `[q', wAddr, b, blockAddr, pAddr, locAddr, outAddr, h]`.
Matches `CoreProgPeel.coreOnContract` (arguments, `CoreParamsAt`, `GraphAt`, `VertsAt`,
`CoreOutAt`, `CoreSpec`, `ZeroFrom`, `locAddr` restoration, and memory frame). -/
noncomputable def stepBSubCoreContract (cfg : ParamConfig) (M r q' w Tprev Sprev : ℕ) :
    Contract where
  pre args mem :=
    let cp := coreParamsOf cfg M r
    ∃ (wAddr b blockAddr pAddr locAddr outAddr h : ℕ) (W : Graph) (Y : Finset ℕ),
      args = [q', wAddr, b, blockAddr, pAddr, locAddr, outAddr, h] ∧
      12 ≤ cfg.a₀ ∧ 4 ≤ cfg.a ∧ r ≤ ell M ∧ q' ≤ r ∧
      CoreParamsAt mem pAddr cp r ∧
      GraphAt mem wAddr W ∧
      W.IsValid ∧
      W.n ≤ 2048 * LParam M * (NOf M r) ^ r ∧
      VertsAt mem blockAddr b Y ∧
      Y ⊆ Finset.range W.n ∧
      (∀ e ∈ W.inside Y, e.1 ≠ e.2) ∧
      b ≤ cp.N ^ q' ∧
      (∀ v ∈ Y, W.degIn Y v ≤ cp.Δ) ∧
      W.m ≤ cp.Δ * b ∧
      (∀ u < W.n, mem (locAddr + u) = 0) ∧
      wAddr + 2 + 2 * W.m ≤ h ∧
      blockAddr + b ≤ h ∧
      pAddr + coreParamsSize r ≤ h ∧
      locAddr + W.n ≤ h ∧
      outAddr + 2 + b ≤ h ∧
      DisjointRange locAddr W.n wAddr (2 + 2 * W.m) ∧
      DisjointRange locAddr W.n blockAddr b ∧
      DisjointRange locAddr W.n pAddr (coreParamsSize r) ∧
      DisjointRange locAddr W.n outAddr (2 + b) ∧
      DisjointRange outAddr (2 + b) wAddr (2 + 2 * W.m) ∧
      DisjointRange outAddr (2 + b) blockAddr b ∧
      DisjointRange outAddr (2 + b) pAddr (coreParamsSize r) ∧
      ZeroFrom mem h ∧
      h + Sprev < 2 ^ w
  post args mem v mem' :=
    let cp := coreParamsOf cfg M r
    ∀ (wAddr b blockAddr pAddr locAddr outAddr h : ℕ) (W : Graph) (Y : Finset ℕ),
      args = [q', wAddr, b, blockAddr, pAddr, locAddr, outAddr, h] →
      12 ≤ cfg.a₀ → 4 ≤ cfg.a → r ≤ ell M → q' ≤ r →
      CoreParamsAt mem pAddr cp r →
      GraphAt mem wAddr W →
      W.IsValid →
      W.n ≤ 2048 * LParam M * (NOf M r) ^ r →
      VertsAt mem blockAddr b Y →
      Y ⊆ Finset.range W.n →
      (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      b ≤ cp.N ^ q' →
      (∀ v ∈ Y, W.degIn Y v ≤ cp.Δ) →
      W.m ≤ cp.Δ * b →
      (∀ u < W.n, mem (locAddr + u) = 0) →
      wAddr + 2 + 2 * W.m ≤ h →
      blockAddr + b ≤ h →
      pAddr + coreParamsSize r ≤ h →
      locAddr + W.n ≤ h →
      outAddr + 2 + b ≤ h →
      DisjointRange locAddr W.n wAddr (2 + 2 * W.m) →
      DisjointRange locAddr W.n blockAddr b →
      DisjointRange locAddr W.n pAddr (coreParamsSize r) →
      DisjointRange locAddr W.n outAddr (2 + b) →
      DisjointRange outAddr (2 + b) wAddr (2 + 2 * W.m) →
      DisjointRange outAddr (2 + b) blockAddr b →
      DisjointRange outAddr (2 + b) pAddr (coreParamsSize r) →
      ZeroFrom mem h →
      h + Sprev < 2 ^ w →
      (∃ res : CoreResult, CoreOutAt mem' outAddr res ∧ CoreSpec cp q' W Y res) ∧
      h ≤ v ∧ v ≤ h + Sprev ∧
      ZeroFrom mem' v ∧
      (∀ u < W.n, mem' (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + b ≤ a) → mem' a = mem a)
  cost _ _ := Tprev

/-! ## 3. Step B Contract (`stepBContract`) -/

/-- **Step B Word-RAM contract** (`stepB` in `OneShotStepB.lean`, `2 ≤ q ≤ r`).
Args: `[q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h]`.

Matches `OneShot`'s calling convention (`CoreParamsAt`, `GraphAt`, `VertsAt`, `CoreOutAt`,
`EdgesAt`, `stepBCostBound`, `locAddr` restoration, and memory frame):
- On a router cut, writes `CoreOutAt mem' outAddr (.cut U)` (`mem' outAddr = 0`) with
  `RouteCutSpec G X 100 z U`;
- Otherwise sets `mem' outAddr = 1`, `mem' (outAddr + 1) = (callsFakeEdges callsB).length`,
  and writes `EdgesAt mem' fAddr (callsFakeEdges callsB)` for valid calls `callsB`
  (`callsB.length ≤ 49 * cp.L + 2`) making every full block `blockSet (X.sort (· ≤ ·)) b i`
  a `1 / (2 * cp.P (q - 1))`-expander in `callsWitnessEdges callsB`;
- Restores `locAddr` to all zeros without scanning `range G.n`, preserves memory `< h` outside
  `[fAddr, fAddr + 2 * k)` and `[outAddr, outAddr + 2 + k)`, returns `h' ∈ [h, h + stepBSpace]`
  with `ZeroFrom mem' h'`, and runs in at most `stepBCostBound K_B (NOf M r) (LParam M) q Tprev`
  deterministic steps. -/
noncomputable def stepBContract (cfg : ParamConfig) (M r q w K_B S_B Tprev Sprev : ℕ) :
    Contract where
  pre args mem :=
    let cp := coreParamsOf cfg M r
    ∃ (gAddr k xAddr b nBlocks z pAddr locAddr fAddr outAddr h : ℕ)
      (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h] ∧
      4 ≤ cfg.a ∧ r ≤ ell M ∧ 2 ≤ q ∧ q ≤ r ∧
      CoreParamsAt mem pAddr cp r ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      VertsAt mem xAddr k X ∧
      X ⊆ Finset.range G.n ∧
      (∀ e ∈ G.inside X, e.1 ≠ e.2) ∧
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) ∧
      G.m ≤ 2 * cp.Δ * k ∧
      cp.N ^ (q - 1) / 2 ≤ k ∧ k ≤ cp.N ^ q ∧
      b = cp.N ^ (q - 1) / 2 ∧
      nBlocks = numFullBlocks (X.sort (· ≤ ·)) b ∧
      z = k / cp.D q ∧
      (∀ u < G.n, mem (locAddr + u) = 0) ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + k ≤ h ∧
      pAddr + coreParamsSize r ≤ h ∧
      locAddr + G.n ≤ h ∧
      fAddr + 2 * k ≤ h ∧
      outAddr + 2 + k ≤ h ∧
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) ∧
      DisjointRange locAddr G.n xAddr k ∧
      DisjointRange locAddr G.n pAddr (coreParamsSize r) ∧
      DisjointRange locAddr G.n fAddr (2 * k) ∧
      DisjointRange locAddr G.n outAddr (2 + k) ∧
      DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m) ∧
      DisjointRange outAddr (2 + k) xAddr k ∧
      DisjointRange outAddr (2 + k) pAddr (coreParamsSize r) ∧
      DisjointRange outAddr (2 + k) fAddr (2 * k) ∧
      DisjointRange fAddr (2 * k) gAddr (2 + 2 * G.m) ∧
      DisjointRange fAddr (2 * k) xAddr k ∧
      DisjointRange fAddr (2 * k) pAddr (coreParamsSize r) ∧
      ZeroFrom mem h ∧
      h + stepBSpace S_B G.n (NOf M r) (LParam M) q Sprev < 2 ^ w
  post args mem v mem' :=
    let cp := coreParamsOf cfg M r
    ∀ (gAddr k xAddr b nBlocks z pAddr locAddr fAddr outAddr h : ℕ)
      (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h] →
      4 ≤ cfg.a → r ≤ ell M → 2 ≤ q → q ≤ r →
      CoreParamsAt mem pAddr cp r →
      GraphAt mem gAddr G →
      G.IsValid →
      VertsAt mem xAddr k X →
      X ⊆ Finset.range G.n →
      (∀ e ∈ G.inside X, e.1 ≠ e.2) →
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) →
      G.m ≤ 2 * cp.Δ * k →
      cp.N ^ (q - 1) / 2 ≤ k → k ≤ cp.N ^ q →
      b = cp.N ^ (q - 1) / 2 →
      nBlocks = numFullBlocks (X.sort (· ≤ ·)) b →
      z = k / cp.D q →
      (∀ u < G.n, mem (locAddr + u) = 0) →
      gAddr + 2 + 2 * G.m ≤ h →
      xAddr + k ≤ h →
      pAddr + coreParamsSize r ≤ h →
      locAddr + G.n ≤ h →
      fAddr + 2 * k ≤ h →
      outAddr + 2 + k ≤ h →
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) →
      DisjointRange locAddr G.n xAddr k →
      DisjointRange locAddr G.n pAddr (coreParamsSize r) →
      DisjointRange locAddr G.n fAddr (2 * k) →
      DisjointRange locAddr G.n outAddr (2 + k) →
      DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m) →
      DisjointRange outAddr (2 + k) xAddr k →
      DisjointRange outAddr (2 + k) pAddr (coreParamsSize r) →
      DisjointRange outAddr (2 + k) fAddr (2 * k) →
      DisjointRange fAddr (2 * k) gAddr (2 + 2 * G.m) →
      DisjointRange fAddr (2 * k) xAddr k →
      DisjointRange fAddr (2 * k) pAddr (coreParamsSize r) →
      ZeroFrom mem h →
      h + stepBSpace S_B G.n (NOf M r) (LParam M) q Sprev < 2 ^ w →
      ((mem' outAddr = 0 ∧
          ∃ U : Finset ℕ, CoreOutAt mem' outAddr (.cut U) ∧ RouteCutSpec G X 100 z U) ∨
        (mem' outAddr = 1 ∧
          ∃ callsB : List RoutedCall,
            callsB.length ≤ 49 * cp.L + 2 ∧
            (∀ c ∈ callsB, c.Valid G X (routeCong cp.Δ 100 cp.L) z) ∧
            (∀ i < nBlocks, (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
              (blockSet (X.sort (· ≤ ·)) b i) (1 / (2 * (cp.P (q - 1) : ℝ)))) ∧
            mem' (outAddr + 1) = (callsFakeEdges callsB).length ∧
            EdgesAt mem' fAddr (callsFakeEdges callsB))) ∧
      h ≤ v ∧ v ≤ h + stepBSpace S_B G.n (NOf M r) (LParam M) q Sprev ∧
      ZeroFrom mem' v ∧
      (∀ u < G.n, mem' (locAddr + u) = 0) ∧
      (∀ a < h, (a < fAddr ∨ fAddr + 2 * k ≤ a) → (a < outAddr ∨ outAddr + 2 + k ≤ a) →
        mem' a = mem a)
  cost _ _ := stepBCostBound K_B (NOf M r) (LParam M) q Tprev

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 4. Space Comparison and Counterexample for `(N + 3) ^ 4` vs `(G.n + 3) ^ 4` -/

/-- Whenever `n ≤ N`, `stepBSpace S_B n N L q Sprev` is bounded by `OneShot`'s
`100 * N * L * Sprev + (2 * S_B) * (N + 3) ^ 4 * N ^ (q + 1) * L ^ 8`. -/
theorem stepBSpace_le_of_n_le {S_B n N L q Sprev : ℕ} (hn : n ≤ N) (hN : 1 ≤ N) (hL : 1 ≤ L) :
    stepBSpace S_B n N L q Sprev ≤
      100 * N * L * Sprev + (2 * S_B) * (N + 3) ^ 4 * N ^ (q + 1) * L ^ 8 := by
  unfold stepBSpace
  have h1 : (n + 3) ^ 4 ≤ (N + 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 : L ≤ N ^ (q + 1) * L ^ 8 := by
    have hNp : 1 ≤ N ^ (q + 1) := Nat.one_le_pow _ _ hN
    have hL7 : 1 ≤ L ^ 7 := Nat.one_le_pow _ _ hL
    have hL8 : L ^ 8 = L * L ^ 7 := by ring
    rw [hL8]
    calc L = 1 * (L * 1) := by ring
      _ ≤ N ^ (q + 1) * (L * L ^ 7) := Nat.mul_le_mul hNp (Nat.mul_le_mul_left L hL7)
      _ = N ^ (q + 1) * (L * L ^ 7) := rfl
  have h3 : (n + 3) ^ 4 * L ≤ (N + 3) ^ 4 * (N ^ (q + 1) * L ^ 8) := Nat.mul_le_mul h1 h2
  have h4 : N ^ (q + 1) * L ^ 8 ≤ (N + 3) ^ 4 * (N ^ (q + 1) * L ^ 8) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h5 : (n + 3) ^ 4 * L + N ^ (q + 1) * L ^ 8 ≤ 2 * ((N + 3) ^ 4 * (N ^ (q + 1) * L ^ 8)) := by
    omega
  have h6 := Nat.mul_le_mul_left S_B h5
  have h7 : S_B * (2 * ((N + 3) ^ 4 * (N ^ (q + 1) * L ^ 8))) =
      (2 * S_B) * (N + 3) ^ 4 * N ^ (q + 1) * L ^ 8 := by ring
  omega

/-- Small concrete counterexample showing why `stepBSpace` must include `(G.n + 3) ^ 4`:
for any constant `S_B`, at `M = 1, r = 2, q = 2` (`N = 4, L = 8`) and `Sprev = 0`, an ambient
graph with `G.n = (S_B + 1) * (N + 3) * N * L ^ 2` vertices has `outerRouterSpace 1 G.n 0`
strictly exceeding `100 * N * L * 0 + S_B * (N + 3) ^ 4 * N ^ (q + 1) * L ^ 8`. -/
theorem stepBContract_router_space_counterexample (S_B : ℕ) :
    let N := NOf 1 2
    let L := LParam 1
    let n := (S_B + 1) * (N + 3) * N * L ^ 2
    100 * N * L * 0 + S_B * (N + 3) ^ 4 * N ^ (2 + 1) * L ^ 8 < outerRouterSpace 1 n 0 := by
  intro N L n
  unfold outerRouterSpace
  have hN : N = 4 := by
    change NOf 1 2 = 4; unfold NOf ceilDiv ell; decide
  have hL : L = 8 := by
    change LParam 1 = 8; unfold LParam ell; decide
  have hn_eq : n = (S_B + 1) * 7 * 4 * 64 := by
    dsimp only [n]; rw [hN, hL]; ring
  rw [hN, hL, hn_eq]
  have hlt : S_B * (4 + 3) ^ 4 * 4 ^ (2 + 1) * 8 ^ 8 < ((S_B + 1) * 7 * 4 * 64) ^ 4 := by
    have hlhs : S_B * (4 + 3) ^ 4 * 4 ^ (2 + 1) * 8 ^ 8 =
        S_B * (7 ^ 4 * 4 ^ 3 * 8 ^ 8) := by ring
    have hrhs : ((S_B + 1) * 7 * 4 * 64) ^ 4 =
        (S_B + 1) ^ 4 * (7 ^ 4 * 4 ^ 4 * 8 ^ 8) := by ring
    rw [hlhs, hrhs]
    have h1 : S_B < (S_B + 1) ^ 4 := by
      have : S_B + 1 ≤ (S_B + 1) ^ 4 := Nat.le_self_pow (by decide) (S_B + 1)
      omega
    have h2 : 7 ^ 4 * 4 ^ 3 * 8 ^ 8 ≤ 7 ^ 4 * 4 ^ 4 * 8 ^ 8 := by decide
    have h3 : 0 < 7 ^ 4 * 4 ^ 3 * 8 ^ 8 := by decide
    calc S_B * (7 ^ 4 * 4 ^ 3 * 8 ^ 8)
        < (S_B + 1) ^ 4 * (7 ^ 4 * 4 ^ 3 * 8 ^ 8) := Nat.mul_lt_mul_of_pos_right h1 h3
      _ ≤ (S_B + 1) ^ 4 * (7 ^ 4 * 4 ^ 4 * 8 ^ 8) := Nat.mul_le_mul_left _ h2
  have hle : ((S_B + 1) * 7 * 4 * 64) ^ 4 ≤ ((S_B + 1) * 7 * 4 * 64 + 3) ^ 4 :=
    Nat.pow_le_pow_left (by omega) 4
  omega

private lemma relabel_space_aux (P : ℕ) (hP : 16 * 800 ^ 8 < P) :
    100 * P * 800 * 0 + 1 * (P + 3) ^ 4 * P ^ (2 + 1) * 800 ^ 8 < 1 * (0 + (P ^ 2 + 3) ^ 4 + 1) := by
  have h3 : 3 ≤ P := by
    have : 3 ≤ 16 * 800 ^ 8 := by decide
    omega
  have hP3 : P + 3 ≤ 2 * P := by omega
  have h1 : (P + 3) ^ 4 ≤ (2 * P) ^ 4 := Nat.pow_le_pow_left hP3 4
  have h2 : (2 * P) ^ 4 * P ^ 3 * 800 ^ 8 = 16 * 800 ^ 8 * P ^ 7 := by ring
  have h4 : P ^ 8 = P * P ^ 7 := by ring
  have h5 : 0 < P ^ 7 := Nat.pow_pos (by omega)
  have hlhs : (P + 3) ^ 4 * P ^ 3 * 800 ^ 8 < P ^ 8 :=
    calc (P + 3) ^ 4 * P ^ 3 * 800 ^ 8
        ≤ (2 * P) ^ 4 * P ^ 3 * 800 ^ 8 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ = 16 * 800 ^ 8 * P ^ 7 := h2
      _ < P * P ^ 7 := Nat.mul_lt_mul_of_pos_right hP h5
      _ = P ^ 8 := h4.symm
  have hrhs : P ^ 8 ≤ (P ^ 2 + 3) ^ 4 := by
    have hsq : P ^ 8 = (P ^ 2) ^ 4 := by ring
    rw [hsq]; exact Nat.pow_le_pow_left (by omega) 4
  simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul]
  exact lt_of_lt_of_le hlhs (le_trans hrhs (Nat.le_succ _))

/-- Even after relabeling `G` onto `k = N ^ 2` vertices (`q = 2, r = 2`), at `S_B = 1, Sprev = 0`
and `M = 2 ^ 199 - 1` (`ell M = 200`, `L = 800`, `N = 2 ^ 100`), a single router call's
`outerRouterSpace 1 (N ^ 2) 0` strictly exceeds `1 * (N + 3) ^ 4 * N ^ 3 * L ^ 8`. -/
theorem stepBContract_relabel_space_counterexample :
    let M := 2 ^ 199 - 1
    let N := NOf M 2
    let L := LParam M
    100 * N * L * 0 + 1 * (N + 3) ^ 4 * N ^ (2 + 1) * L ^ 8 < outerRouterSpace 1 (N ^ 2) 0 := by
  intro M N L
  unfold outerRouterSpace
  have hell : ell M = 200 := by
    unfold ell
    have hM2 : 2 * M + 2 = 2 ^ 200 := by
      dsimp only [M]
      have h1 : 1 ≤ 2 ^ 199 := Nat.one_le_pow 199 2 (by decide)
      have h2 : 2 * (2 ^ 199 - 1) + 2 = 2 * 2 ^ 199 := by
        rw [Nat.mul_sub, Nat.mul_one]; exact Nat.sub_add_cancel (by omega)
      rw [h2, ← Nat.pow_succ']
    rw [hM2, Nat.clog_pow 2 200 (by decide)]
  have hL : L = 800 := by dsimp only [L]; unfold LParam; rw [hell]
  have hN : N = 2 ^ 100 := by
    dsimp only [N]; unfold NOf ceilDiv; rw [hell]; congr 1
  rw [hL, hN]
  apply relabel_space_aux (2 ^ 100)
  have h800 : 800 ^ 8 < 2 ^ 80 := by
    have h1 : 800 ^ 8 < (2 ^ 10) ^ 8 := Nat.pow_lt_pow_left (by decide) (by decide)
    rwa [← Nat.pow_mul] at h1
  have h16 : 16 * 800 ^ 8 < 2 ^ 84 := by
    have ha : 16 * 800 ^ 8 < 16 * 2 ^ 80 := Nat.mul_lt_mul_of_pos_left h800 (by decide)
    have hb : 16 * 2 ^ 80 = 2 ^ 84 := by rw [show (16 : ℕ) = 2 ^ 4 by decide, ← Nat.pow_add]
    rwa [hb] at ha
  exact lt_of_lt_of_le h16 (Nat.pow_le_pow_right (by decide) (by decide))

/-! ## 5. Non-Vacuity Witnesses -/

/-- Helper memory image for `CoreParamsAt` at `pAddr`. -/
private noncomputable def stepBParamsMem (pAddr : ℕ) (cp : CoreParams) (r : ℕ) (a : ℕ) : ℕ :=
  if a = pAddr then cp.N
  else if a = pAddr + 1 then cp.L
  else if a = pAddr + 2 then cp.Δ
  else if a = pAddr + 3 then r
  else if pAddr + 4 ≤ a ∧ a ≤ pAddr + 4 + r then cp.P (a - (pAddr + 4))
  else if pAddr + 5 + r ≤ a ∧ a ≤ pAddr + 5 + 2 * r then cp.D (a - (pAddr + 5 + r))
  else if pAddr + 6 + 2 * r ≤ a ∧ a ≤ pAddr + 6 + 3 * r then cp.N ^ (a - (pAddr + 6 + 2 * r))
  else 0

private lemma stepBParamsMem_coreParamsAt (pAddr : ℕ) (cp : CoreParams) (r : ℕ) :
    CoreParamsAt (stepBParamsMem pAddr cp r) pAddr cp r := by
  refine ⟨by simp [stepBParamsMem], by simp [stepBParamsMem], by simp [stepBParamsMem],
    by simp [stepBParamsMem], fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [stepBParamsMem]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [stepBParamsMem]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [stepBParamsMem]
    split_ifs <;> first | omega | (congr 1; omega)

/-- Non-vacuity witness for `stepBSubCoreContract`: concrete 2-vertex edgeless graph at
`M = 1, r = 2, q' = 1`, `cfg = ParamConfig.default`. -/
theorem stepBSubCoreContract_pre_example :
    ∃ w args mem, (∀ a ∈ args, a < 2 ^ w) ∧
      (stepBSubCoreContract ParamConfig.default 1 2 1 w 1 1).pre args mem := by
  set cp := coreParamsOf ParamConfig.default 1 2
  have hell : ell 1 = 2 := by unfold ell; decide
  have hN : NOf 1 2 = 4 := by unfold NOf ceilDiv; rw [hell]; decide
  have hL : LParam 1 = 8 := by unfold LParam; rw [hell]
  let G : Graph := ⟨2, []⟩
  let X : Finset ℕ := Finset.range 2
  have hsort : X.sort (· ≤ ·) = List.range 2 := sort_range_eq_list_range 2
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 2
    else if a = 1 then 0
    else if 10 ≤ a ∧ a < 12 then a - 10
    else if 20 ≤ a ∧ a < 33 then stepBParamsMem 20 cp 2 a
    else 0
  let w : ℕ := 64
  let args : List ℕ := [1, 0, 2, 10, 20, 40, 50, 100]
  have hargs_w : ∀ a ∈ args, a < 2 ^ w := by
    intro a ha
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨w, args, mem, hargs_w, 0, 2, 10, 20, 40, 50, 100, G, X,
    rfl, by decide, by decide, by rw [hell], by omega, ?_, ?_, fun e he => by simp [G] at he,
    by show 2 ≤ 2048 * LParam 1 * (NOf 1 2) ^ 2; rw [hL, hN]; decide,
    ?_, Finset.Subset.refl _, fun e he => by simp [G, Graph.inside] at he,
    by change 2 ≤ (NOf 1 2) ^ 1; rw [hN]; decide,
    fun v _ => by simp [G, Graph.degIn, Graph.inside],
    by simp [G, Graph.m],
    fun u hu => by simp [G] at hu; simp only [mem]; split_ifs <;> omega,
    by simp [G, Graph.m], by omega, by unfold coreParamsSize; omega, by simp [G], by omega,
    Or.inr (by simp [G, Graph.m]), Or.inr (by omega), Or.inr (by unfold coreParamsSize; omega),
    Or.inl (by simp [G]),
    Or.inr (by simp [G, Graph.m]), Or.inr (by omega), Or.inr (by unfold coreParamsSize; omega),
    fun a ha => by simp only [mem]; split_ifs <;> omega, by decide⟩
  · have hpm := stepBParamsMem_coreParamsAt 20 cp 2
    have hagree : ∀ a, 20 ≤ a → a < 33 → mem a = stepBParamsMem 20 cp 2 a := fun a h1 h2 => by
      simp only [mem]; split_ifs <;> omega
    exact ⟨by rw [hagree 20 (by omega) (by omega)]; exact hpm.1,
      by rw [hagree 21 (by omega) (by omega)]; exact hpm.2.1,
      by rw [hagree 22 (by omega) (by omega)]; exact hpm.2.2.1,
      by rw [hagree 23 (by omega) (by omega)]; exact hpm.2.2.2.1,
      fun j hj => by rw [hagree (20 + 4 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.1 j hj,
      fun j hj => by rw [hagree (20 + 5 + 2 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.2.1 j hj,
      fun j hj => by rw [hagree (20 + 6 + 2 * 2 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.2.2 j hj⟩
  · intro i hi
    rcases i with _ | _ | i <;> simp [G, Graph.encode, Graph.m, mem] at hi ⊢
  · refine ⟨by simp [X], ?_⟩
    rw [hsort]
    intro i hi
    simp only [List.length_range] at hi
    rw [List.getElem_range]
    simp only [mem]; split_ifs <;> omega

/-- Non-vacuity witness for `stepBContract`: concrete 2-vertex edgeless graph at
`M = 1, r = 2, q = 2`, `cfg = ParamConfig.default`. -/
theorem stepBContract_pre_example :
    ∃ w args mem, (∀ a ∈ args, a < 2 ^ w) ∧
      (stepBContract ParamConfig.default 1 2 2 w 1 1 1 1).pre args mem := by
  set cp := coreParamsOf ParamConfig.default 1 2
  have hell : ell 1 = 2 := by unfold ell; decide
  have hN : NOf 1 2 = 4 := by unfold NOf ceilDiv; rw [hell]; decide
  have hL : LParam 1 = 8 := by unfold LParam; rw [hell]
  have hΔ : deltaParam 1 = 8192 := by unfold deltaParam tParam; rw [hL]
  let G : Graph := ⟨2, []⟩
  let X : Finset ℕ := Finset.range 2
  have hsort : X.sort (· ≤ ·) = List.range 2 := sort_range_eq_list_range 2
  let z : ℕ := 2 / cp.D 2
  have hz0 : z = 0 := by
    have hD : 60 * cp.Δ * cp.P 2 ≤ cp.D 2 :=
      (coreParamsValid_of_paramConfig ParamConfig.default 1 2 (by decide) (by rw [hell])).hD 2
        (by omega) (by omega)
    have hP2 : 1 ≤ cp.P 2 :=
      (coreParamsValid_of_paramConfig ParamConfig.default 1 2 (by decide) (by rw [hell])).hP_pos
        (by omega)
    have hDgt : 2 < cp.D 2 := by
      have hcpΔ : cp.Δ = 8192 := hΔ
      have : 8192 ≤ 60 * cp.Δ * cp.P 2 := by rw [hcpΔ]; nlinarith
      omega
    exact Nat.div_eq_of_lt hDgt
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 2
    else if a = 1 then 0
    else if 10 ≤ a ∧ a < 12 then a - 10
    else if 20 ≤ a ∧ a < 33 then stepBParamsMem 20 cp 2 a
    else 0
  let w : ℕ := 64
  let args : List ℕ := [2, 0, 2, 10, 2, 1, z, 20, 40, 50, 60, 100]
  have hargs_w : ∀ a ∈ args, a < 2 ^ w := by
    intro a ha
    simp only [args, hz0, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  refine ⟨w, args, mem, hargs_w, 0, 2, 10, 2, 1, z, 20, 40, 50, 60, 100, G, X,
    rfl, by decide, by rw [hell], by omega, by omega, ?_, ?_, fun e he => by simp [G] at he,
    ?_, Finset.Subset.refl _, fun e he => by simp [G, Graph.inside] at he,
    fun v _ => by simp [G, Graph.degIn, Graph.inside],
    by simp [G, Graph.m],
    by change (NOf 1 2) ^ 1 / 2 ≤ 2; rw [hN]; decide,
    by change 2 ≤ (NOf 1 2) ^ 2; rw [hN]; decide,
    by change 2 = (NOf 1 2) ^ 1 / 2; rw [hN]; decide,
    by simp [numFullBlocks, hsort], rfl,
    fun u hu => by simp [G] at hu; simp only [mem]; split_ifs <;> omega,
    by simp [G, Graph.m], by omega, by unfold coreParamsSize; omega, by simp [G], by omega, by omega,
    Or.inr (by simp [G, Graph.m]), Or.inr (by omega), Or.inr (by unfold coreParamsSize; omega),
    Or.inl (by simp [G]), Or.inl (by simp [G]),
    Or.inr (by simp [G, Graph.m]), Or.inr (by omega), Or.inr (by unfold coreParamsSize; omega),
    Or.inr (by omega),
    Or.inr (by simp [G, Graph.m]), Or.inr (by omega), Or.inr (by unfold coreParamsSize; omega),
    fun a ha => by simp only [mem]; split_ifs <;> omega, ?_⟩
  · have hpm := stepBParamsMem_coreParamsAt 20 cp 2
    have hagree : ∀ a, 20 ≤ a → a < 33 → mem a = stepBParamsMem 20 cp 2 a := fun a h1 h2 => by
      simp only [mem]; split_ifs <;> omega
    exact ⟨by rw [hagree 20 (by omega) (by omega)]; exact hpm.1,
      by rw [hagree 21 (by omega) (by omega)]; exact hpm.2.1,
      by rw [hagree 22 (by omega) (by omega)]; exact hpm.2.2.1,
      by rw [hagree 23 (by omega) (by omega)]; exact hpm.2.2.2.1,
      fun j hj => by rw [hagree (20 + 4 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.1 j hj,
      fun j hj => by rw [hagree (20 + 5 + 2 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.2.1 j hj,
      fun j hj => by rw [hagree (20 + 6 + 2 * 2 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.2.2 j hj⟩
  · intro i hi
    rcases i with _ | _ | i <;> simp [G, Graph.encode, Graph.m, mem] at hi ⊢
  · refine ⟨by simp [X], ?_⟩
    rw [hsort]
    intro i hi
    simp only [List.length_range] at hi
    rw [List.getElem_range]
    simp only [mem]; split_ifs <;> omega
  · unfold stepBSpace
    rw [hN, hL]
    simp only [G]
    decide

end MinCostFlow.ExpanderDecomp
