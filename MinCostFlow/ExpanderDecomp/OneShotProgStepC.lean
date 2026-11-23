module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProgStepContracts
public import MinCostFlow.ExpanderDecomp.OneShotProgAux
public import MinCostFlow.ExpanderDecomp.ProgStepCSpec
public import MinCostFlow.ExpanderDecomp.ProgEdgeColorBase
public import MinCostFlow.ExpanderDecomp.OneShot
import MinCostFlow.ExpanderDecomp.DecompModel
import MinCostFlow.ExpanderDecomp.RouteMeets
import MinCostFlow.ExpanderDecomp.CoreCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `OneShot` Step C Preparation, Cost/Space Bounds, and Stage C1 Verification (`OneShotProgStepC`)

Connects `OneShot`'s Step C macro-join and leftover-injection calls directly to the shared
contracts `ProgStepCSpec.stepCContract`, `ProgStepCSpec.stepCLeftoverContract`,
`ProgCloud.cloudExpanderContract`, and `ProgEdgeColorBase.edgeColor17Contract`:

* `isCloudExpander_cloud_of_paramConfig`: `ProgCloud.cloud` satisfies `IsCloudExpander` for
  every `ParamConfig`.
* `stepCMacroCost_le_oneShot`, `stepCLeftoverCost_le_oneShot`: explicit `O(N^{q+1} L^8)` upper
  bounds on `stepCMacroCost` and `stepCLeftoverCost` using `routerCallCost_bounded`.
* `stepC_space_le_oneShot`, `stepC_time_le_oneShot`: absorb Step C preparation (`copyWords` of
  `LenListAt`, `cloudExpander`, `edgeColor17`), `stepCContract`, `stepCLeftoverContract`, and
  fake-edge copies into `stepCSpaceConst` and `stepCTimeConst`.
* `oneShotStepC1Stmt` and `oneShotStepC1_runs`: verified statement fragment preparing `LenListAt`
  and (for `2 ≤ numBlk`) building and 17-colouring `cloud numBlk`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Stage C1 Statement (`LenListAt` + `cloud` + `edgeColor17`) -/

/-- Stage C1 fragment inside `oneShotProc`:
writes `LenListAt mem lenXAddr vs` (`r20 = lenXAddr`), allocates `sAddr (r21)`, `cloudAddr (r22)`,
`usedAddr (r23)`, `colAddr (r24)`, advances `r17`, and when `2 ≤ numBlk (r15)` invokes
`idx.cloudExpander` and `idx.edgeColor17` to produce `colM (r25)` and `ColoredEdgesAt` at `r24`. -/
def oneShotStepC1Stmt (idx : CoreIdx) : Stmt :=
  seqStmts
    [ .assign 20 (.reg 17)
    , .store (.reg 20) (.reg 2)
    , .call 29 idx.copyWords [.reg 2, .reg 3, .bin .add (.reg 20) (.const 1)]
    , .assign 21 (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 2))
    , .assign 22 (.bin .add (.reg 21) (.const 1))
    , .assign 23 (.bin .add (.bin .add (.reg 22) (.const 2)) (.bin .mul (.const 9) (.reg 15)))
    , .assign 24 (.bin .add (.reg 23) (.bin .mul (.const 17) (.reg 15)))
    , .assign 17 (.bin .add (.reg 24) (.bin .mul (.const 15) (.reg 15)))
    , .cond (.bin .lt (.reg 15) (.const 2))
        (.assign 25 (.const 0))
        (seqStmts
          [ .store (.reg 21) (.reg 15)
          , .call 17 idx.cloudExpander [.reg 21, .reg 22, .reg 17]
          , .call 25 idx.edgeColor17 [.reg 22, .reg 23, .reg 24] ]) ]

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma oneShotStepC1Stmt_noRand (idx : CoreIdx) : (oneShotStepC1Stmt idx).NoRand := by
  simp [oneShotStepC1Stmt, seqStmts, Stmt.NoRand]

/-! ## 2. Cloud Expander and Step C Cost/Space Lemmas -/

/-- `ProgCloud.cloud` is a `coreParamsOf cfg M r`-cloud expander whenever `12 ≤ cfg.a₀`
(in particular for `ParamConfig.default` where `a₀ = 12`). -/
lemma isCloudExpander_cloud_of_paramConfig (cfg : ParamConfig) (M r : ℕ) (ha0 : 12 ≤ cfg.a₀) :
    IsCloudExpander cloud (coreParamsOf cfg M r).α where
  n_eq := fun s hs => (cloud_spec hs).1
  isValid := fun s hs => (cloud_spec hs).2.1
  deg_le := fun s hs => (cloud_spec hs).2.2.2.1
  expansion := fun s hs => by
    have hα : (coreParamsOf cfg M r).α ≤ cloudAlpha := by
      show 1 / (cfg.a₀ : ℝ) ≤ 1 / 12
      have ha0' : (12 : ℝ) ≤ cfg.a₀ := by exact_mod_cast ha0
      exact one_div_le_one_div_of_le (by norm_num) ha0'
    exact IsExpansionExpanderOn.mono hα (cloud_spec hs).2.2.2.2

/-- Total fake edges across `calls` is at most `k` whenever `calls.length ≤ cp.Δ` and every call
is valid with deficit budget `z = k / cp.D q`. -/
lemma callsFakeEdges_length_le_k {cfg : ParamConfig} {M r q k : ℕ}
    {G : Graph} {X : Finset ℕ} {calls : List RoutedCall}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hlen : calls.length ≤ (coreParamsOf cfg M r).Δ)
    (hvalid : ∀ c ∈ calls,
      c.Valid G X (routeCong (coreParamsOf cfg M r).Δ 100 (coreParamsOf cfg M r).L)
        (k / (coreParamsOf cfg M r).D q)) :
    (callsFakeEdges calls).length ≤ k := by
  set cp := coreParamsOf cfg M r
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hDge : cp.Δ ≤ cp.D q := by
    have hD := hcfg.hD q hq1 hqr
    have hP := hcfg.hP_pos hqr
    have h60 : 1 ≤ 60 * cp.P q := by
      calc 1 ≤ 60 * 1 := by decide
        _ ≤ 60 * cp.P q := Nat.mul_le_mul_left 60 hP
    calc cp.Δ = 1 * cp.Δ := (Nat.one_mul _).symm
      _ ≤ (60 * cp.P q) * cp.Δ := Nat.mul_le_mul_right _ h60
      _ = 60 * cp.Δ * cp.P q := by ring
      _ ≤ cp.D q := hD
  have hsum : (callsFakeEdges calls).length ≤ calls.length * (k / cp.D q) := by
    unfold callsFakeEdges
    induction calls with
    | nil => simp
    | cons c rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      have hc : c.fake.length ≤ k / cp.D q := (hvalid c List.mem_cons_self).2.2.2.2.2
      have hr := ih (by simp at hlen; omega) (fun c' hc' => hvalid c' (List.mem_cons_of_mem _ hc'))
      omega
  calc (callsFakeEdges calls).length
      ≤ calls.length * (k / cp.D q) := hsum
    _ ≤ cp.D q * (k / cp.D q) := Nat.mul_le_mul_right _ (le_trans hlen hDge)
    _ ≤ k := Nat.mul_div_le k (cp.D q)

/-- Every endpoint word in `EdgesAt mem addr es` is `< n` when all edges lie in `X ⊆ range n`. -/
lemma edgesAt_words_lt {mem : ℕ → ℕ} {addr n : ℕ} {X : Finset ℕ} {es : List (ℕ × ℕ)}
    (hed : EdgesAt mem addr es) (hX : X ⊆ Finset.range n)
    (hin : ∀ e ∈ es, e.1 ∈ X ∧ e.2 ∈ X) :
    ∀ i < 2 * es.length, mem (addr + i) < n := by
  intro i hi
  have hj : i / 2 < es.length := by omega
  have hmem := hin (es[i / 2]'hj) (List.getElem_mem hj)
  rcases hed (i / 2) hj with ⟨h1, h2⟩
  by_cases hev : i % 2 = 0
  · have haddr : addr + i = addr + 2 * (i / 2) := by omega
    rw [haddr, h1]
    exact Finset.mem_range.mp (hX hmem.1)
  · have haddr : addr + i = addr + 2 * (i / 2) + 1 := by omega
    rw [haddr, h2]
    exact Finset.mem_range.mp (hX hmem.2)

/-- `EdgesAt` transfer across `copyWordsContract`. -/
lemma edgesAt_of_copyWords {mem mem' : ℕ → ℕ} {src dst : ℕ} {es : List (ℕ × ℕ)}
    (hsrc : EdgesAt mem src es)
    (hcopy : ∀ i < 2 * es.length, mem' (dst + i) = mem (src + i)) :
    EdgesAt mem' dst es := by
  intro j hj
  have h1 := hcopy (2 * j) (by omega)
  have h2 := hcopy (2 * j + 1) (by omega)
  have hsrcj := hsrc j hj
  refine ⟨?_, ?_⟩
  · rw [h1, hsrcj.1]
  · rw [show dst + 2 * j + 1 = dst + (2 * j + 1) by omega, h2,
      show src + (2 * j + 1) = src + 2 * j + 1 by omega, hsrcj.2]

/-- Single `routerCallCost` call bound at `C_route = 80`. -/
lemma stepC_routeCost_le {M r q : ℕ} {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {z : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ deltaParam M) (hXL : X.card < 2 ^ LParam M)
    (hX2 : 2 ≤ X.card) (hXle : X.card ≤ (NOf M r) ^ q)
    (hpairs : ValidTerminalPairs X pairs) (hplen : pairs.length ≤ 2 * NOf M r) :
    routerCallCost G X pairs (deltaParam M) (LParam M) 100 z ≤
      stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 7 := by
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hΔ : 1 ≤ deltaParam M := one_le_tParam M
  have hbase := routerCallCost_bounded G X pairs (deltaParam M) (LParam M) 100 z hX hGloop hΔ hdegG
    (by omega) hXL (by decide) hpairs
  have hpath : routePathLen (deltaParam M) 100 (LParam M) + 1 ≤ ParamConfig.d0 * (LParam M) ^ 2 := by
    rw [routePathLen_core_eq]
    unfold dCore deltaParam tParam ParamConfig.d0
    have hL : 1 ≤ (LParam M) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    have heq : 3200 * (1024 * LParam M) * LParam M = 3276800 * (LParam M) ^ 2 := by ring
    omega
  have hcong : routeCong (deltaParam M) 100 (LParam M) ≤ ParamConfig.R0 * (LParam M) ^ 4 := by
    rw [routeCong_core_eq]
    unfold RCore deltaParam tParam ParamConfig.R0
    have hd : dCore M + 1 ≤ ParamConfig.d0 * (LParam M) ^ 2 := by
      rw [← routePathLen_core_eq]; exact hpath
    calc 1600 * (1024 * LParam M) * (dCore M + 1) * LParam M
        ≤ 1600 * (1024 * LParam M) * (ParamConfig.d0 * (LParam M) ^ 2) * LParam M :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
      _ = 1600 * 1024 * ParamConfig.d0 * (LParam M) ^ 4 := by ring
  have hins : X.card + (G.inside X).length + 1 ≤ 1024 * LParam M * X.card := by
    have hsum : G.volIn X X = 2 * (G.inside X).length := volIn_self G X
    unfold Graph.volIn at hsum
    have hle : ∑ v ∈ X, G.degIn X v ≤ ∑ _v ∈ X, deltaParam M :=
      Finset.sum_le_sum fun v hv => hdegG v hv
    simp only [Finset.sum_const, smul_eq_mul] at hle
    have hδ : deltaParam M = 1024 * LParam M := rfl
    rw [hδ] at hle
    have h2 : (G.inside X).length ≤ 512 * LParam M * X.card := by
      have : X.card * (1024 * LParam M) = 2 * (512 * LParam M * X.card) := by ring
      omega
    have h3 : X.card + 1 ≤ 512 * LParam M * X.card := by
      have h2x : 2 * X.card ≤ 512 * LParam M * X.card :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have h1024 : 512 * LParam M * X.card + 512 * LParam M * X.card =
        1024 * LParam M * X.card := by ring
    omega
  have hinsN : X.card + (G.inside X).length + 1 ≤ 1024 * LParam M * (NOf M r) ^ q :=
    le_trans hins (Nat.mul_le_mul_left _ hXle)
  set B := 1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 7
  have hBpos : 1 ≤ B := by
    have h1 : 1 ≤ 1024 * ParamConfig.d0 * ParamConfig.R0 := by
      unfold ParamConfig.R0 ParamConfig.d0; decide
    have h2 : 1 ≤ (NOf M r) ^ (q + 1) := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ (LParam M) ^ 7 := Nat.one_le_pow _ _ (by omega)
    calc 1 = 1 * 1 * 1 := by decide
      _ ≤ 1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 7 :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hprod : pairs.length * (X.card + (G.inside X).length + 1) *
      (routePathLen (deltaParam M) 100 (LParam M) + 1) *
      routeCong (deltaParam M) 100 (LParam M) ≤ 2 * B := by
    calc pairs.length * (X.card + (G.inside X).length + 1) *
          (routePathLen (deltaParam M) 100 (LParam M) + 1) *
          routeCong (deltaParam M) 100 (LParam M)
        ≤ (2 * NOf M r) * (1024 * LParam M * (NOf M r) ^ q) *
            (ParamConfig.d0 * (LParam M) ^ 2) * (ParamConfig.R0 * (LParam M) ^ 4) :=
          Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul hplen hinsN) hpath) hcong
      _ = 2 * B := by simp only [B, pow_succ]; ring
  calc routerCallCost G X pairs (deltaParam M) (LParam M) 100 z
      ≤ 80 * (pairs.length * (X.card + (G.inside X).length + 1) *
          (routePathLen (deltaParam M) 100 (LParam M) + 1) *
          routeCong (deltaParam M) 100 (LParam M) + 1) := hbase
    _ ≤ 80 * (2 * B + 1) := Nat.mul_le_mul_left 80 (Nat.add_le_add_right hprod 1)
    _ ≤ 80 * (3 * B) := Nat.mul_le_mul_left 80 (by omega)
    _ = stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 7 := by
        unfold stepCRouterConst; simp only [B]; ring

/-- Bound `stepCMacroCost` by `(17 * stepCRouterConst + 250) * N ^ (q + 1) * L ^ 8`. -/
lemma stepCMacroCost_le_oneShot {cfg : ParamConfig} {M r q b numBlk z : ℕ}
    {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ deltaParam M) (hXL : X.card < 2 ^ LParam M)
    (hX2 : 2 ≤ X.card) (hXle : X.card ≤ (NOf M r) ^ q)
    (hb : 0 < b) (hnb : numBlk = numFullBlocks (X.sort (· ≤ ·)) b)
    (hnble : numBlk ≤ 2 * NOf M r) :
    stepCMacroCost (coreParamsOf cfg M r) routeOrCut routerCallCost cloud G X
        (X.sort (· ≤ ·)) b numBlk z ≤
      (17 * stepCRouterConst + 250) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hvs : vs.toFinset = X := by ext v; simp [vs]
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  set R1 := stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 7
  have hNL8 : X.card + 1 ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have hNq : (NOf M r) ^ q ≤ (NOf M r) ^ (q + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hL8 : 2 ≤ (LParam M) ^ 8 := by
      calc 2 ≤ LParam M := by omega
        _ = (LParam M) ^ 1 := (pow_one _).symm
        _ ≤ (LParam M) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    calc X.card + 1 ≤ 2 * X.card := by omega
      _ ≤ 2 * (NOf M r) ^ (q + 1) := by omega
      _ ≤ (LParam M) ^ 8 * (NOf M r) ^ (q + 1) := Nat.mul_le_mul_right _ hL8
      _ = (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
  have hnbNL : numBlk ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have h1 : numBlk ≤ X.card := by
      rw [hnb]; unfold numFullBlocks
      rw [Finset.length_sort]
      exact Nat.div_le_self _ _
    omega
  have hR1 : R1 ≤ stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have hL78 : (LParam M) ^ 7 ≤ (LParam M) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    exact Nat.mul_le_mul_left _ hL78
  have hcost : stepCMacroCost cp routeOrCut routerCallCost cloud G X vs b numBlk z ≤
      17 * R1 + 17 * (X.card + 1) + (200 * numBlk + 1) := by
    unfold stepCMacroCost
    by_cases hk2 : 2 ≤ numBlk
    · simp only [hk2, ↓reduceIte]
      have hcs := cloud_spec hk2
      have hcn : (cloud numBlk).n = numBlk := hcs.1
      have hcvalid : (cloud numBlk).IsValid := hcs.2.1
      have hcdeg : ∀ v < (cloud numBlk).n, (cloud numBlk).deg v ≤ 9 :=
        fun v hv => hcs.2.2.2.1 v (hcn ▸ hv)
      have hcol := edgeColor17_spec hcvalid hcdeg
      have hHvalid := removeLoops_isValid hcvalid
      have hloop : ∀ m, stepCMacroLoopCost cp routeOrCut routerCallCost G X vs b z
          (edgeColor17 (cloud numBlk)) m ≤ m * (R1 + (X.card + 1)) := by
        intro m
        induction m with
        | zero => simp [stepCMacroLoopCost]
        | succ m ih =>
          unfold stepCMacroLoopCost
          cases stepCMacroLoop cp routeOrCut G X vs b z (edgeColor17 (cloud numBlk)) m with
          | inl _ =>
            rw [Nat.add_zero]
            exact le_trans ih (Nat.mul_le_mul_right _ (Nat.le_succ m))
          | inr _ =>
            have hcc : stepCMacroColorCost cp routerCallCost G X vs b z
                (colorClass (edgeColor17 (cloud numBlk)) m) ≤ R1 + (X.card + 1) := by
              unfold stepCMacroColorCost
              split_ifs
              · omega
              · have hEc_v : ∀ e ∈ colorClass (edgeColor17 (cloud numBlk)) m,
                    e.1 < numBlk ∧ e.2 < numBlk := by
                  intro e he
                  unfold colorClass at he
                  obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
                  have hin : ec.1 ∈ (removeLoops (cloud numBlk)).edges := by
                    rw [← hcol.1]
                    exact List.mem_map.mpr ⟨ec, (List.mem_filter.mp hec).1, rfl⟩
                  have hv := hHvalid ec.1 hin
                  rwa [removeLoops_n, hcn] at hv
                have hEc_v' : ∀ e ∈ colorClass (edgeColor17 (cloud numBlk)) m,
                    e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b :=
                  hnb ▸ hEc_v
                have hvp := hvs ▸ validTerminalPairs_of_matching_edges hnd hb hEc_v'
                  (hcol.2.2.1 m)
                have hlen : ((colorClass (edgeColor17 (cloud numBlk)) m).map fun e =>
                    (blockSet vs b e.1, blockSet vs b e.2)).length ≤ 2 * NOf M r := by
                  rw [List.length_map]
                  have hcl : (colorClass (edgeColor17 (cloud numBlk)) m).length ≤ numBlk := by
                    have hsub : (colorClass (edgeColor17 (cloud numBlk)) m).map Prod.fst ⊆
                        List.range numBlk := fun u hu => by
                      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
                      exact List.mem_range.mpr (hEc_v e he).1
                    have hnd1 : ((colorClass (edgeColor17 (cloud numBlk)) m).map Prod.fst).Nodup := by
                      have hfm := hcol.2.2.1 m
                      have hsubl : ((colorClass (edgeColor17 (cloud numBlk)) m).map Prod.fst).Sublist
                          ((colorClass (edgeColor17 (cloud numBlk)) m).flatMap fun e => [e.1, e.2]) := by
                        clear hfm hsub hEc_v hEc_v' hvp
                        induction colorClass (edgeColor17 (cloud numBlk)) m with
                        | nil => simp
                        | cons e rest ih =>
                          simp only [List.map_cons, List.flatMap_cons, List.cons_append,
                            List.nil_append]
                          exact List.Sublist.cons_cons e.1 (List.Sublist.cons e.2 ih)
                      exact hfm.sublist hsubl
                    calc (colorClass (edgeColor17 (cloud numBlk)) m).length
                        = ((colorClass (edgeColor17 (cloud numBlk)) m).map Prod.fst).length :=
                          (List.length_map _).symm
                      _ ≤ (List.range numBlk).length := hnd1.length_le_of_subset hsub
                      _ = numBlk := List.length_range
                  exact le_trans hcl hnble
                exact Nat.add_le_add
                  (stepC_routeCost_le hX hGloop hdegG hXL hX2 hXle hvp hlen) le_rfl
            rw [Nat.succ_mul]
            exact Nat.add_le_add ih hcc
      have h17 := hloop 17
      have hexp : 17 * (R1 + (X.card + 1)) = 17 * R1 + 17 * (X.card + 1) := by ring
      omega
    · simp only [hk2, ↓reduceIte]; omega
  have h1 : (17 * stepCRouterConst + 250) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 =
      17 * (stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 8) +
      250 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) := by ring
  omega

/-- Bound `stepCLeftoverCost` by `(stepCRouterConst + 2) * N ^ (q + 1) * L ^ 8`. -/
lemma stepCLeftoverCost_le_oneShot {cfg : ParamConfig} {M r q b z : ℕ}
    {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ deltaParam M) (hXL : X.card < 2 ^ LParam M)
    (hX2 : 2 ≤ X.card) (hXle : X.card ≤ (NOf M r) ^ q)
    (hb : 0 < b) (hble : b ≤ X.card) :
    stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X (X.sort (· ≤ ·)) b z ≤
      (stepCRouterConst + 2) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
  set vs := X.sort (· ≤ ·)
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hvs : vs.toFinset = X := by ext v; simp [vs]
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hNL8 : X.card + 1 ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have hNq : (NOf M r) ^ q ≤ (NOf M r) ^ (q + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hL8 : 2 ≤ (LParam M) ^ 8 := by
      calc 2 ≤ LParam M := by omega
        _ = (LParam M) ^ 1 := (pow_one _).symm
        _ ≤ (LParam M) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    calc X.card + 1 ≤ 2 * X.card := by omega
      _ ≤ 2 * (NOf M r) ^ (q + 1) := by omega
      _ ≤ (LParam M) ^ 8 * (NOf M r) ^ (q + 1) := Nat.mul_le_mul_right _ hL8
      _ = (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
  have hR1 : stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 7 ≤
      stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide))
  have hcost : stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X vs b z ≤
      stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 7 + (X.card + 1) := by
    unfold stepCLeftoverCost
    split_ifs
    · have hble' : b ≤ vs.length := by rw [Finset.length_sort]; exact hble
      have hpairs : ValidTerminalPairs X [(leftoverVerts vs b, fullVerts vs b)] := by
        have hle := card_leftoverVerts_le_card_sdiff hnd hb hble'
        rw [sdiff_leftoverVerts_eq_fullVerts hnd] at hle
        refine ⟨?_, ?_⟩
        · intro p hp
          rw [List.mem_singleton.mp hp]
          exact ⟨hvs ▸ leftoverVerts_subset_toFinset vs b, hvs ▸ fullVerts_subset_toFinset vs b, hle⟩
        · simp [(disjoint_fullVerts_leftoverVerts hnd b).symm]
      exact Nat.add_le_add
        (stepC_routeCost_le hX hGloop hdegG hXL hX2 hXle hpairs (by simp; omega)) le_rfl
    · omega
  have h1 : (stepCRouterConst + 2) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 =
      stepCRouterConst * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
      2 * ((NOf M r) ^ (q + 1) * (LParam M) ^ 8) := by ring
  omega

/-- Combined heap-space bound for all of Step C (Stage C1 + `stepCSpace` + `stepCLeftoverSpace`). -/
lemma stepC_space_le_oneShot {C_sp M r q n k numBlk costM costL : ℕ}
    (hqr : q ≤ r) (hn : n ≤ 2048 * LParam M * (NOf M r) ^ r)
    (hk : k ≤ (NOf M r) ^ q) (hnb : numBlk ≤ k)
    (hM : costM ≤ (17 * stepCRouterConst + 250) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8)
    (hL : costL ≤ (stepCRouterConst + 2) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8) :
    (1 + k) + (3 + 41 * numBlk) + cloudExpanderSpace numBlk +
      (2 + 34 * k) + stepCSpace C_sp n k numBlk costM +
      (2 + 2 * k) + stepCLeftoverSpace C_sp n k costL ≤
      stepCSpaceConst C_sp * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
  set N := NOf M r
  set L := LParam M
  set B := coreSpaceBase M r
  set NL := N ^ (q + 1) * L ^ 8
  have hN4 : 4 ≤ N := four_le_NOf M r
  have hL4 : 4 ≤ L := four_le_LParam M
  have hNL1 : 1 ≤ NL :=
    Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by omega))
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hpow4_le_B : ∀ t ≤ 2048 * L * N ^ r, (t + 3) ^ 4 ≤ B := fun t ht => by
    have h1 : t + 3 ≤ 2048 * L * N ^ r + 3 := by omega
    calc (t + 3) ^ 4 ≤ (2048 * L * N ^ r + 3) ^ 4 := Nat.pow_le_pow_left h1 4
      _ ≤ (2048 * L * N ^ r + 3) ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hn4 : (n + 3) ^ 4 ≤ B := hpow4_le_B n hn
  have hnb4 : (numBlk + 3) ^ 4 ≤ B := by
    apply hpow4_le_B
    have h1 : N ^ q ≤ N ^ r := Nat.pow_le_pow_right (by omega) hqr
    have h2 : N ^ r ≤ 2048 * L * N ^ r := by
      calc N ^ r = 1 * N ^ r := (Nat.one_mul _).symm
        _ ≤ (2048 * L) * N ^ r := Nat.mul_le_mul_right _ (by omega)
    omega
  have hkNL : k ≤ NL := by
    have h1 : N ^ q ≤ N ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 1 ≤ L ^ 8 := Nat.one_le_pow _ _ (by omega)
    calc k ≤ N ^ (q + 1) := le_trans hk h1
      _ = N ^ (q + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ N ^ (q + 1) * L ^ 8 := Nat.mul_le_mul_left _ h2
  have hB_le_BNL : B ≤ B * NL := by
    calc B = B * 1 := (Nat.mul_one _).symm
      _ ≤ B * NL := Nat.mul_le_mul_left _ hNL1
  have hNL_le_BNL : NL ≤ B * NL := by
    calc NL = 1 * NL := (Nat.one_mul _).symm
      _ ≤ B * NL := Nat.mul_le_mul_right _ hB1
  have hcloud : cloudExpanderSpace numBlk ≤ 36 * (B * NL) := by
    unfold cloudExpanderSpace
    have : 4 ≤ 4 * (B * NL) := by have := le_trans hB1 hB_le_BNL; omega
    omega
  have hsc1 : stepCSpace C_sp n k numBlk costM ≤
      (C_sp + 1) * ((17 * stepCRouterConst + 1470) * (B * NL)) := by
    unfold stepCSpace
    apply Nat.mul_le_mul_left
    have hM' : costM ≤ (17 * stepCRouterConst + 250) * (B * NL) := by
      have hr : (17 * stepCRouterConst + 250) * N ^ (q + 1) * L ^ 8 =
          (17 * stepCRouterConst + 250) * NL := by ring
      rw [hr] at hM
      exact le_trans hM (Nat.mul_le_mul_left _ hNL_le_BNL)
    have h1 : (17 * stepCRouterConst + 1470) * (B * NL) =
        (17 * stepCRouterConst + 250) * (B * NL) + 20 * (B * NL) + 1200 * (B * NL) := by ring
    have h2 : 400 * (k + numBlk + 1) ≤ 1200 * (B * NL) := by
      have : k + numBlk + 1 ≤ 3 * NL := by omega
      have := Nat.mul_le_mul_left 400 (le_trans this (Nat.mul_le_mul_left 3 hNL_le_BNL))
      omega
    have h20 : 20 * (n + 3) ^ 4 ≤ 20 * (B * NL) :=
      Nat.mul_le_mul_left 20 (le_trans hn4 hB_le_BNL)
    linarith only [hM', h1, h2, h20]
  have hsc2 : stepCLeftoverSpace C_sp n k costL ≤
      (C_sp + 1) * ((stepCRouterConst + 44) * (B * NL)) := by
    unfold stepCLeftoverSpace
    apply Nat.mul_le_mul_left
    have hL' : costL ≤ (stepCRouterConst + 2) * (B * NL) := by
      have hr : (stepCRouterConst + 2) * N ^ (q + 1) * L ^ 8 =
          (stepCRouterConst + 2) * NL := by ring
      rw [hr] at hL
      exact le_trans hL (Nat.mul_le_mul_left _ hNL_le_BNL)
    have h1 : (stepCRouterConst + 44) * (B * NL) =
        (stepCRouterConst + 2) * (B * NL) + 2 * (B * NL) + 40 * (B * NL) := by ring
    have h2 : 20 * (k + 1) ≤ 40 * (B * NL) := by
      have : k + 1 ≤ 2 * NL := by omega
      have := Nat.mul_le_mul_left 20 (le_trans this (Nat.mul_le_mul_left 2 hNL_le_BNL))
      omega
    have h2n : 2 * (n + 3) ^ 4 ≤ 2 * (B * NL) :=
      Nat.mul_le_mul_left 2 (le_trans hn4 hB_le_BNL)
    linarith only [hL', h1, h2, h2n]
  have hmisc : (1 + k) + (3 + 41 * numBlk) + (2 + 34 * k) + (2 + 2 * k) ≤ 86 * (B * NL) := by
    have : 1 + k + (3 + 41 * numBlk) + (2 + 34 * k) + (2 + 2 * k) ≤ 86 * NL := by omega
    exact le_trans this (Nat.mul_le_mul_left 86 hNL_le_BNL)
  have htot : stepCSpaceConst C_sp * B * N ^ (q + 1) * L ^ 8 =
      (C_sp + 1) * ((20 * stepCRouterConst + 10000) * (B * NL)) := by
    unfold stepCSpaceConst; simp only [NL]; ring
  rw [htot]
  have h1 : 36 * (B * NL) + 86 * (B * NL) ≤ (C_sp + 1) * (122 * (B * NL)) := by
    have : 1 ≤ C_sp + 1 := by omega
    calc 36 * (B * NL) + 86 * (B * NL) = 1 * (122 * (B * NL)) := by ring
      _ ≤ (C_sp + 1) * (122 * (B * NL)) := Nat.mul_le_mul_right _ this
  have h2 : (C_sp + 1) * ((17 * stepCRouterConst + 1470) * (B * NL)) +
      (C_sp + 1) * ((stepCRouterConst + 44) * (B * NL)) +
      (C_sp + 1) * (122 * (B * NL)) ≤
      (C_sp + 1) * ((20 * stepCRouterConst + 10000) * (B * NL)) := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    apply Nat.mul_le_mul_left
    have ha : (17 * stepCRouterConst + 1470) * (B * NL) + (stepCRouterConst + 44) * (B * NL) +
        122 * (B * NL) = (18 * stepCRouterConst + 1636) * (B * NL) := by ring
    rw [ha]
    apply Nat.mul_le_mul_right
    have hc : 18 * stepCRouterConst ≤ 20 * stepCRouterConst :=
      Nat.mul_le_mul_right _ (by decide)
    linarith only [hc]
  linarith only [hcloud, hsc1, hsc2, hmisc, h1, h2]

/-- Combined step-count bound for all of Step C (Stage C1 + `stepCMacro` + `stepCLeftover` + copies). -/
lemma stepC_time_le_oneShot {C_stepC C_left M r q k numBlk costM costL : ℕ}
    (hk : k ≤ (NOf M r) ^ q) (hnb : numBlk ≤ k)
    (hM : costM ≤ (17 * stepCRouterConst + 250) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8)
    (hL : costL ≤ (stepCRouterConst + 2) * (NOf M r) ^ (q + 1) * (LParam M) ^ 8) :
    copyWordsCost k + cloudExpanderCost numBlk + edgeColor17Cost (5 * numBlk) +
      (C_stepC * costM + C_stepC) + (C_left * costL + C_left) +
      copyWordsCost (2 * k) + copyWordsCost (2 * k) + 600 ≤
      stepCTimeConst C_stepC C_left * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
  set N := NOf M r
  set L := LParam M
  set NL := N ^ (q + 1) * L ^ 8
  have hN4 : 4 ≤ N := four_le_NOf M r
  have hL4 : 4 ≤ L := four_le_LParam M
  have hNL1 : 1 ≤ NL :=
    Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by omega))
  have hkNL : k ≤ NL := by
    have h1 : N ^ q ≤ N ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 1 ≤ L ^ 8 := Nat.one_le_pow _ _ (by omega)
    calc k ≤ N ^ (q + 1) := le_trans hk h1
      _ = N ^ (q + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ N ^ (q + 1) * L ^ 8 := Nat.mul_le_mul_left _ h2
  have hcloud : cloudExpanderCost numBlk ≤ cloudExpanderCost 1 * NL := by
    unfold cloudExpanderCost
    rw [Nat.mul_one]
    exact Nat.mul_le_mul_left _ (le_trans hnb hkNL)
  have hcol : edgeColor17Cost (5 * numBlk) ≤ 5580 * NL := by
    unfold edgeColor17Cost; omega
  have hcp : copyWordsCost k + copyWordsCost (2 * k) + copyWordsCost (2 * k) + 600 ≤ 850 * NL := by
    unfold copyWordsCost; omega
  have hM' : C_stepC * costM + C_stepC ≤ C_stepC * ((17 * stepCRouterConst + 251) * NL) := by
    have hr : (17 * stepCRouterConst + 250) * N ^ (q + 1) * L ^ 8 =
        (17 * stepCRouterConst + 250) * NL := by ring
    rw [hr] at hM
    have h1 : C_stepC * costM ≤ C_stepC * ((17 * stepCRouterConst + 250) * NL) :=
      Nat.mul_le_mul_left _ hM
    have h2 : C_stepC ≤ C_stepC * NL := by
      calc C_stepC = C_stepC * 1 := (Nat.mul_one _).symm
        _ ≤ C_stepC * NL := Nat.mul_le_mul_left _ hNL1
    have h3 : C_stepC * ((17 * stepCRouterConst + 251) * NL) =
        C_stepC * ((17 * stepCRouterConst + 250) * NL) + C_stepC * NL := by ring
    omega
  have hL' : C_left * costL + C_left ≤ C_left * ((stepCRouterConst + 3) * NL) := by
    have hr : (stepCRouterConst + 2) * N ^ (q + 1) * L ^ 8 = (stepCRouterConst + 2) * NL := by ring
    rw [hr] at hL
    have h1 : C_left * costL ≤ C_left * ((stepCRouterConst + 2) * NL) :=
      Nat.mul_le_mul_left _ hL
    have h2 : C_left ≤ C_left * NL := by
      calc C_left = C_left * 1 := (Nat.mul_one _).symm
        _ ≤ C_left * NL := Nat.mul_le_mul_left _ hNL1
    have h3 : C_left * ((stepCRouterConst + 3) * NL) =
        C_left * ((stepCRouterConst + 2) * NL) + C_left * NL := by ring
    omega
  have htot : stepCTimeConst C_stepC C_left * N ^ (q + 1) * L ^ 8 =
      (C_stepC + C_left + 1) * ((20 * stepCRouterConst + 10000) * NL) +
        cloudExpanderCost 1 * NL := by
    unfold stepCTimeConst; simp only [NL]; ring
  rw [htot]
  have hsum : C_stepC * ((17 * stepCRouterConst + 251) * NL) +
      C_left * ((stepCRouterConst + 3) * NL) + (5580 * NL + 850 * NL) ≤
      (C_stepC + C_left + 1) * ((20 * stepCRouterConst + 10000) * NL) := by
    have hA : C_stepC * ((17 * stepCRouterConst + 251) * NL) ≤
        C_stepC * ((20 * stepCRouterConst + 10000) * NL) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by
        have : 17 * stepCRouterConst ≤ 20 * stepCRouterConst :=
          Nat.mul_le_mul_right _ (by decide)
        linarith only [this]))
    have hB : C_left * ((stepCRouterConst + 3) * NL) ≤
        C_left * ((20 * stepCRouterConst + 10000) * NL) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by
        have : 1 * stepCRouterConst ≤ 20 * stepCRouterConst :=
          Nat.mul_le_mul_right _ (by decide)
        linarith only [this]))
    have hC : 5580 * NL + 850 * NL ≤ 1 * ((20 * stepCRouterConst + 10000) * NL) := by
      have : 5580 * NL + 850 * NL = 6430 * NL := by ring
      rw [this, Nat.one_mul]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _ |>.trans' (by decide : 6430 ≤ 10000))
    have hd : (C_stepC + C_left + 1) * ((20 * stepCRouterConst + 10000) * NL) =
        C_stepC * ((20 * stepCRouterConst + 10000) * NL) +
        C_left * ((20 * stepCRouterConst + 10000) * NL) +
        1 * ((20 * stepCRouterConst + 10000) * NL) := by ring
    linarith only [hA, hB, hC, hd]
  linarith only [hcloud, hcol, hcp, hM', hL', hsum]

/-! ## 3. Verified Execution of Stage C1 (`oneShotStepC1_runs`) -/

/-- Verified execution of `oneShotStepC1Stmt`: writes `LenListAt mem' hCur (X.sort (· ≤ ·))`,
and if `2 ≤ numBlk`, builds `cloud numBlk` and 17-edge-colours it at `colAddr`, advancing the
heap cursor by at most `(1 + k) + (3 + 41 * numBlk) + cloudExpanderSpace numBlk` while preserving
all memory `< hCur`. -/
theorem oneShotStepC1_runs {idx : CoreIdx} {w : ℕ} {p : Program}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hcloud : MeetsContract w p idx.cloudExpander (cloudExpanderContract w))
    (hcol : MeetsContract w p idx.edgeColor17 (edgeColor17Contract w))
    (st : State) (ω : ℕ → Bool)
    {k xAddr numBlk hCur n : ℕ} {X : Finset ℕ}
    (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = xAddr)
    (hr15 : st.regs 15 = numBlk) (hr17 : st.regs 17 = hCur)
    (hX : VertsAt st.mem xAddr k X) (hXrange : X ⊆ Finset.range n)
    (hx_le : xAddr + k ≤ hCur) (hn_lt : n < 2 ^ w)
    (hZero : ZeroFrom st.mem hCur)
    (hw : hCur + (1 + k) + (3 + 41 * numBlk) + cloudExpanderSpace numBlk < 2 ^ w)
    (hw32 : 32 < 2 ^ w) :
    ∃ out st' c,
      Runs w p ω (oneShotStepC1Stmt idx) st out st' c ∧
      normalPost (fun st' =>
        st'.regs 20 = hCur ∧
        st'.regs 24 = hCur + 1 + k + 1 + (2 + 9 * numBlk) + 17 * numBlk ∧
        st'.regs 25 ≤ 5 * numBlk ∧
        st'.regs 17 ≤ hCur + (1 + k) + (3 + 41 * numBlk) + cloudExpanderSpace numBlk ∧
        hCur + (1 + k) + (3 + 41 * numBlk) ≤ st'.regs 17 ∧
        (∀ r < 20, r ≠ 17 → st'.regs r = st.regs r) ∧
        LenListAt st'.mem hCur (X.sort (· ≤ ·)) ∧
        (2 ≤ numBlk →
          (cloud numBlk).n = numBlk ∧
          (cloud numBlk).IsValid ∧
          (∀ v < numBlk, (cloud numBlk).deg v ≤ 9) ∧
          st'.regs 25 = (edgeColor17 (cloud numBlk)).length ∧
          st'.regs 25 ≤ 5 * numBlk ∧
          ColoredEdgesAt st'.mem (st'.regs 24) (edgeColor17 (cloud numBlk))) ∧
        ZeroFrom st'.mem (st'.regs 17) ∧
        (∀ a < hCur, st'.mem a = st.mem a)) out st' ∧
      c ≤ copyWordsCost k + cloudExpanderCost numBlk + edgeColor17Cost (5 * numBlk) + 120 := by
  refine runs_start_le ?_
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw32
  have hk_lt : k < 2 ^ w := by omega
  have hnb_lt : numBlk < 2 ^ w := by omega
  have h1_lt : 1 < 2 ^ w := by omega
  have h2_lt : 2 < 2 ^ w := by omega
  have h9_lt : 9 < 2 ^ w := by omega
  have h15_lt : 15 < 2 ^ w := by omega
  have h17_lt : 17 < 2 ^ w := by omega
  set sAddr := hCur + 1 + k
  set cloudAddr := sAddr + 1
  set usedAddr := cloudAddr + 2 + 9 * numBlk
  set colAddr := usedAddr + 17 * numBlk
  set hCloud := colAddr + 15 * numBlk
  have hhCloud_eq : hCloud = hCur + (1 + k) + (3 + 41 * numBlk) := by
    simp only [hCloud, colAddr, usedAddr, cloudAddr, sAddr]; omega
  unfold oneShotStepC1Stmt seqStmts
  -- r20 := r17 (= hCur)
  refine runs_seq_assign_le (v := hCur) (by rw [Expr.eval_reg, hr17]) ?_
  -- store r20 r2 (mem[hCur] := k)
  refine runs_seq_store_le (x := hCur) (v := k)
    (by simp [Expr.eval]) (by simp [Expr.eval, hr2]) ?_
  set mem1 := Function.update st.mem hCur k
  -- call copyWords [k, xAddr, hCur + 1]
  have hcopy_pre : (copyWordsContract w).pre [k, xAddr, hCur + 1] mem1 := by
    refine ⟨k, xAddr, hCur + 1, rfl, by omega, by omega, by omega, by omega,
      Or.inr (by omega), ?_⟩
    intro i hi
    have hne : xAddr + i ≠ hCur := by omega
    simp only [mem1, Function.update_of_ne hne]
    have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort]; exact hX.1.symm
    have hi' : i < (X.sort (· ≤ ·)).length := by omega
    rw [hX.2 i hi']
    have hmem : (X.sort (· ≤ ·))[i]'hi' ∈ X :=
      (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi')
    exact lt_trans (Finset.mem_range.mp (hXrange hmem)) hn_lt
  refine runs_seq_call_le (vs := [k, xAddr, hCur + 1]) hcopy
    (by simp [evalArgs, Expr.eval, hr2, hr3, hw0, show hCur + 1 < 2 ^ w by omega])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    hcopy_pre ?_
  intro v1 mem2 _hv1 hpost1
  simp only [copyWordsContract, List.getD_cons_zero, List.getD_cons_succ] at hpost1
  rcases hpost1 with ⟨_, hcopy_eq, hcopy_frame⟩
  have hLenX_mem2 : LenListAt mem2 hCur (X.sort (· ≤ ·)) := by
    have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort]; exact hX.1.symm
    refine ⟨?_, ?_⟩
    · rw [hlen, hcopy_frame hCur (Or.inl (by omega))]
      simp [mem1]
    · intro i hi
      have hik : i < k := by omega
      rw [hcopy_eq i hik]
      have hne : xAddr + i ≠ hCur := by omega
      simp only [mem1, Function.update_of_ne hne]
      exact hX.2 i hi
  have hmem2_lt : ∀ a < hCur, mem2 a = st.mem a := fun a ha => by
    rw [hcopy_frame a (Or.inl (by omega))]
    exact Function.update_of_ne (by omega) _ _
  have hmem2_zero : ZeroFrom mem2 sAddr := fun a ha => by
    rw [hcopy_frame a (Or.inr (by omega))]
    dsimp only [mem1]
    rw [Function.update_of_ne (by omega)]
    exact hZero a (by omega)
  -- r21 := r20 + 1 + r2 (= sAddr)
  refine runs_seq_assign_le (v := sAddr)
    (by simp [Expr.eval, hr2, sAddr, hw0,
      show hCur + 1 < 2 ^ w by omega, show hCur + 1 + k < 2 ^ w by omega]) ?_
  -- r22 := r21 + 1 (= cloudAddr)
  refine runs_seq_assign_le (v := cloudAddr)
    (by simp [Expr.eval, cloudAddr, hw0, show sAddr + 1 < 2 ^ w by omega]) ?_
  -- r23 := r22 + 2 + 9 * r15 (= usedAddr)
  refine runs_seq_assign_le (v := usedAddr)
    (by simp [Expr.eval, hr15, usedAddr, h2_lt, h9_lt,
      show cloudAddr + 2 < 2 ^ w by omega, show 9 * numBlk < 2 ^ w by omega,
      show cloudAddr + 2 + 9 * numBlk < 2 ^ w by omega]) ?_
  -- r24 := r23 + 17 * r15 (= colAddr)
  refine runs_seq_assign_le (v := colAddr)
    (by simp [Expr.eval, hr15, colAddr, h17_lt,
      show 17 * numBlk < 2 ^ w by omega, show usedAddr + 17 * numBlk < 2 ^ w by omega]) ?_
  -- r17 := r24 + 15 * r15 (= hCloud)
  refine runs_seq_assign_le (v := hCloud)
    (by simp [Expr.eval, hr15, hCloud, h15_lt,
      show 15 * numBlk < 2 ^ w by omega, show colAddr + 15 * numBlk < 2 ^ w by omega]) ?_
  -- cond (r15 < 2)
  refine runs_cond_le (v := if numBlk < 2 then 1 else 0)
    (by by_cases hlt : numBlk < 2 <;> simp [Expr.eval, hr15, hlt, h2_lt, hw0]) ?_ ?_
  · intro hne
    have hlt : numBlk < 2 := by split_ifs at hne with h; exact h; exact absurd rfl hne
    refine runs_assign_le (v := 0) (Expr.eval_const (by omega : 0 < 2 ^ w)) ?_ ?_
    · refine ⟨by simp, by simp [colAddr, usedAddr, cloudAddr, sAddr]; omega,
        by simp,
        by simp [hhCloud_eq], by simp [hhCloud_eq],
        fun r hr h17 => by simp [show r ≠ 25 by omega, show r ≠ 17 by omega, show r ≠ 24 by omega,
          show r ≠ 23 by omega, show r ≠ 22 by omega, show r ≠ 21 by omega, show r ≠ 29 by omega,
          show r ≠ 20 by omega],
        hLenX_mem2, fun h2 => by omega,
        fun a ha => by
          simp [hCloud, colAddr, usedAddr, cloudAddr] at ha
          exact hmem2_zero a (by omega),
        hmem2_lt⟩
    · simp only [Expr.size, argsSize, copyWordsContract, List.getD_cons_zero]
      omega
  · intro hzero
    have hnb2 : 2 ≤ numBlk := by split_ifs at hzero with h; omega
    -- store sAddr numBlk
    refine runs_seq_store_le (x := sAddr) (v := numBlk)
      (by simp [Expr.eval]) (by simp [Expr.eval, hr15]) ?_
    set mem3 := Function.update mem2 sAddr numBlk
    have hcloud_pre : (cloudExpanderContract w).pre [sAddr, cloudAddr, hCloud] mem3 := by
      refine ⟨sAddr, cloudAddr, hCloud, numBlk, rfl, by simp [mem3], hnb2,
        fun a ha => by dsimp only [mem3]; rw [Function.update_of_ne (by omega)]; exact hmem2_zero a (by omega),
        by simp only [hCloud, colAddr, usedAddr]; omega,
        by rw [hhCloud_eq]; omega⟩
    -- call cloudExpander [sAddr, cloudAddr, hCloud]
    refine runs_seq_call_le (vs := [sAddr, cloudAddr, hCloud]) hcloud
      (by simp [evalArgs, Expr.eval])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
      hcloud_pre ?_
    intro hAfterCloud mem4 _hhAC_w hpostC
    simp only [cloudExpanderContract, List.getD_cons_zero, List.getD_cons_succ] at hpostC
    have hs_eq : mem3 sAddr = numBlk := by simp [mem3]
    rw [hs_eq] at hpostC
    rcases hpostC with ⟨hGcloud, _, hCn, hCval, _, hCdeg, _, hhCl_le, hhCl_hi, hZero4, hframe4⟩
    have h2m : 2 * (cloud numBlk).m ≤ 9 * numBlk := cloud_m_le (s := numBlk) hnb2
    have hCm_le : (cloud numBlk).m ≤ 5 * numBlk := by omega
    have hused4 : ∀ i < 17 * numBlk, mem4 (usedAddr + i) = 0 := fun i hi => by
      rw [hframe4 (usedAddr + i) (by simp only [hCloud, colAddr]; omega)
        (Or.inr (by simp only [usedAddr]; omega))]
      dsimp only [mem3]
      rw [Function.update_of_ne (by simp only [usedAddr, cloudAddr]; omega)]
      exact hmem2_zero (usedAddr + i) (by simp only [usedAddr, cloudAddr]; omega)
    have hcol_pre : (edgeColor17Contract w).pre [cloudAddr, usedAddr, colAddr] mem4 := by
      refine ⟨cloudAddr, usedAddr, colAddr, cloud numBlk, rfl, hGcloud, hCval,
        by rw [hCn]; exact hused4, ?_, ?_⟩
      · refine ⟨by simp only [hCloud, colAddr, usedAddr] at *; omega,
          by simp only [hCloud, colAddr] at *; omega,
          by simp only [hCloud] at *; omega, hw32⟩
      · refine ⟨Or.inr (by simp only [usedAddr]; omega),
          Or.inl (by simp only [colAddr, hCn]; omega),
          Or.inr (by simp only [colAddr, usedAddr]; omega)⟩
    -- call edgeColor17 [cloudAddr, usedAddr, colAddr]
    refine runs_call_le (vs := [cloudAddr, usedAddr, colAddr]) hcol
      (by simp [evalArgs, Expr.eval])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
      hcol_pre ?_
    intro colM mem5 _hcolM_w hpostE
    simp only [edgeColor17Contract, List.getD_cons_zero, List.getD_cons_succ] at hpostE
    have hrd : Cited.readGraph mem4 cloudAddr = cloud numBlk :=
      graphAt_iff_readGraph.mp hGcloud
    rw [hrd] at hpostE
    rcases hpostE with ⟨hcolM_eq, hcolM_le, hColAt, _, hframe5⟩
    have hmem5_lt_col : ∀ a < colAddr, mem5 a = mem4 a := fun a ha =>
      hframe5 a (Or.inl ha)
    have hmem5_ge_hCloud : ∀ a, hCloud ≤ a → mem5 a = mem4 a := fun a ha =>
      hframe5 a (Or.inr (by simp only [hCloud] at ha; omega))
    refine ⟨?_, ?_⟩
    · refine ⟨by simp, by simp [colAddr, usedAddr, cloudAddr, sAddr]; omega,
        by simp; omega,
        by simp [hhCloud_eq] at hhCl_hi ⊢; omega,
        by simp [hhCloud_eq] at hhCl_le ⊢; omega,
        fun r hr h17 => by simp [show r ≠ 25 by omega, show r ≠ 17 by omega, show r ≠ 24 by omega,
          show r ≠ 23 by omega, show r ≠ 22 by omega, show r ≠ 21 by omega, show r ≠ 29 by omega,
          show r ≠ 20 by omega],
        ?_, fun _ => ⟨hCn, hCval, hCdeg, by simp [hcolM_eq], by simp; omega, by simpa using hColAt⟩,
        fun a ha => by dsimp only at ha ⊢; rw [hmem5_ge_hCloud a (by simp at ha; omega)]; exact hZero4 a (by simpa using ha),
        fun a ha => by
          dsimp only
          rw [hmem5_lt_col a (by simp only [colAddr, usedAddr, cloudAddr, sAddr]; omega)]
          rw [hframe4 a (by simp only [hCloud, colAddr, usedAddr, cloudAddr, sAddr]; omega)
            (Or.inl (by simp only [cloudAddr, sAddr]; omega))]
          dsimp only [mem3]
          rw [Function.update_of_ne (by simp only [sAddr]; omega)]
          exact hmem2_lt a ha⟩
      -- LenListAt mem5 hCur (X.sort)
      have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort]; exact hX.1.symm
      have hag : ∀ a, hCur ≤ a → a < sAddr → mem5 a = mem2 a := fun a h1 h2 => by
        rw [hmem5_lt_col a (by simp only [colAddr, usedAddr, cloudAddr]; omega)]
        rw [hframe4 a (by simp only [hCloud, colAddr, usedAddr, cloudAddr]; omega)
          (Or.inl (by simp only [cloudAddr]; omega))]
        dsimp only [mem3]
        exact Function.update_of_ne (by omega) _ _
      refine ⟨by dsimp only; rw [hag hCur le_rfl (by simp only [sAddr]; omega)]; exact hLenX_mem2.1,
        fun i hi => by
          dsimp only
          rw [hag (hCur + 1 + i) (by omega) (by simp only [sAddr]; omega)]
          exact hLenX_mem2.2 i hi⟩
    · -- Cost bound
      simp only [Expr.size, argsSize, copyWordsContract, cloudExpanderContract,
        edgeColor17Contract, List.getD_cons_zero, hs_eq, hrd]
      unfold edgeColor17Cost
      omega

end MinCostFlow.ExpanderDecomp
