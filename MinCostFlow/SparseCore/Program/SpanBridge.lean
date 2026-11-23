module

public import MinCostFlow.DynSpanner.Program.DynSpannerDS
public import MinCostFlow.SparseCore.BundleTreeCore
public import MinCostFlow.Chain.BundleRestart

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bucket Spanners: Model Bridge (`SpanBridge`)

Connects the dynamic spanner data structure `dynSpannerDS P` (Theorem 8.2, page 39) to the
per-(component, bucket) spanners of `BundleTreeState` (Lemma 5.17, page 23, with the bundle
repair described in the README).

* `update_foldl_eq_runState`: folding `DynSpanner.update` over a list of batches `Us` starting from
  `DynSpanner.init G₀ L q sparsify` produces `DynSpanner.runState G₀ q sparsify Us.flatten
  Us.flatten.length`.
* `dsHist_state_nil`, `dsHist_state_snoc`, `dsHist_state_eq_foldl`: the `DSHist` abstract state of
  `dynSpannerDS` matches the initial, single-step, and folded `DynSpanner` model states.
* `bucketDSParams`: the `DSParams` of a bucket spanner (`splitBound = bundleSplitBudget k M`),
  with exact identification lemmas for `initBundleTree`, `stepBundleTree`, and `restartBundleTree`
  when `sparsify = fun _ => canonicalSparsify impl`.
* `bundleSplitBudget_eq_div` and `phaseBase_le_iff`: exact natural-number characterizations of
  `bundleSplitBudget k M` and `phaseBase nCap L`, used by the Word-RAM parameter procedures.
* `delete_mem_of_mem_H_sdiff`: any edge present in `H` before a batch and absent after it appears
  as a deletion in the returned `U_H` batch (used to locate edges leaving `H` for `D_left`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.DynSpanner MinCostFlow.SparseCore

public section

/-! ## Bridge between folded `DynSpanner.update` and `DynSpanner.runState` -/

/-- Folding `DynSpanner.update` over a list of batches `Us` starting from
`DynSpanner.init G₀ L q sparsify` yields `DynSpanner.runState G₀ q sparsify Us.flatten
Us.flatten.length`. -/
theorem update_foldl_eq_runState (L : ℕ) (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (Us : List (List Update)) :
    Us.foldl (fun st U => (DynSpanner.update st U sparsify).state)
        (DynSpanner.init G₀ L q sparsify).state =
      DynSpanner.runState (L := L) G₀ q sparsify Us.flatten Us.flatten.length := by
  induction Us using List.reverseRecOn with
  | nil => rfl
  | append_singleton Us U ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    have hflat : (Us ++ [U]).flatten = Us.flatten ++ U := by
      simp [List.flatten_append]
    rw [hflat, List.length_append]
    have hpref :
        DynSpanner.runState (L := L) G₀ q sparsify Us.flatten Us.flatten.length =
          DynSpanner.runState (L := L) G₀ q sparsify (Us.flatten ++ U) Us.flatten.length :=
      (runState_append G₀ q sparsify Us.flatten U Us.flatten.length le_rfl).symm
    rw [hpref]
    have hslice : ∀ i (hi : i < U.length),
        (Us.flatten ++ U)[Us.flatten.length + i]? = some (U[i]'hi) := by
      intro i hi
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact List.getElem?_eq_getElem hi
    exact (update_slice_spec (L := L) G₀ q sparsify (Us.flatten ++ U) U Us.flatten.length hslice).1

/-- The model state of an empty `DSHist` is the `DynSpanner.init` state with `q = phaseBase`. -/
theorem dsHist_state_nil (P : DSParams) (G₀ : MGraph) :
    DSHist.state P ⟨G₀, []⟩ =
      (DynSpanner.init G₀ P.L (phaseBase (G₀.n + P.splitBound) P.L)
        (canonicalSparsify P.impl)).state := by
  simp [DSHist.state, DSHist.flat, DSHist.q, runState]

/-- Appending one batch `U` to a `DSHist` advances its model state by one `DynSpanner.update`. -/
theorem dsHist_state_snoc (P : DSParams) (s : DSHist) (U : List Update) :
    DSHist.state P ⟨s.G₀, s.Us ++ [U]⟩ =
      (DynSpanner.update (s.state P) U (canonicalSparsify P.impl)).state := by
  rw [DSHist.state_append]
  have hpref : s.state P =
      runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) s.flat.length :=
    (runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U s.flat.length le_rfl).symm
  rw [hpref]
  have hslice : ∀ i (hi : i < U.length),
      (s.flat ++ U)[s.flat.length + i]? = some (U[i]'hi) := by
    intro i hi
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hi
  exact (update_slice_spec (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl)
    (s.flat ++ U) U s.flat.length hslice).1.symm

/-- The model state of `s : DSHist` equals folding `DynSpanner.update` over `s.Us`. -/
theorem dsHist_state_eq_foldl (P : DSParams) (s : DSHist) :
    s.state P =
      s.Us.foldl (fun st U => (DynSpanner.update st U (canonicalSparsify P.impl)).state)
        (DynSpanner.init s.G₀ P.L (s.q P) (canonicalSparsify P.impl)).state :=
  (update_foldl_eq_runState P.L s.G₀ (s.q P) (canonicalSparsify P.impl) s.Us).symm

/-! ## Bucket spanner parameters and `BundleTreeState` identification -/

/-- `DSParams` for every `(component, bucket)` spanner of a branch with parameters
`(impl, M, w, L, vCap, eCap, k)`: edge cap `M` and split bound `bundleSplitBudget k M`. -/
@[expose] noncomputable def bucketDSParams (impl : SparsifyImpl) (M w L vCap eCap k : ℕ) :
    DSParams where
  impl := impl
  mMax := M
  w := w
  L := L
  vCap := vCap
  eCap := eCap
  splitBound := bundleSplitBudget k M

theorem bucketDSParams_q (impl : SparsifyImpl) (M w L vCap eCap k : ℕ) (s : DSHist) :
    s.q (bucketDSParams impl M w L vCap eCap k) =
      phaseBase (s.G₀.n + bundleSplitBudget k M) L :=
  rfl

/-- At initialization of `initBundleTreeWithParams` with `sparsify := fun _ => canonicalSparsify impl`,
the empty `DSHist` on the normalized initial bundle graph `normGraph (st₀.bun p).graph` has the
exact model state `st₀.dyn p`. -/
theorem bucketDSParams_initWithParams_eq_bundleTree
    (lsfInit : LSFInit) (impl : SparsifyImpl) (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (w L vCap eCap k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (p : Finset ℕ × ℤ) :
    let st₀ := initBundleTreeWithParams lsfInit L (fun _ => canonicalSparsify impl) params
      spanConst k M N G₀ ℓ₀ ord j
    let P := bucketDSParams impl M w L vCap eCap k
    DSHist.state P ⟨normGraph (st₀.bun p).graph, []⟩ = st₀.dyn p := by
  intro st₀ P
  rw [dsHist_state_nil]
  rfl

/-- At initialization of `initBundleTree` with `sparsify := fun _ => canonicalSparsify impl`,
the empty `DSHist` on the normalized initial bundle graph `normGraph (st₀.bun p).graph` has the
exact model state `st₀.dyn p`. -/
theorem bucketDSParams_init_eq_bundleTree
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (impl : SparsifyImpl)
    (w L vCap eCap k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (p : Finset ℕ × ℤ) :
    let st₀ := initBundleTree oracle C_lsst L (fun _ => canonicalSparsify impl) k M N G₀ ℓ₀ ord j
    let P := bucketDSParams impl M w L vCap eCap k
    DSHist.state P ⟨normGraph (st₀.bun p).graph, []⟩ = st₀.dyn p := by
  intro st₀ P
  rw [dsHist_state_nil]
  rfl

/-- After one step of `stepBundleTree` with `sparsify := fun _ => canonicalSparsify impl`,
appending the bucket's bundle batch `info.U_B p` to a `DSHist` representing `st.dyn p` produces a
`DSHist` representing `info.state.dyn p`. -/
theorem bucketDSParams_step_eq_bundleTree (impl : SparsifyImpl) (M w L vCap eCap k : ℕ)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (p : Finset ℕ × ℤ) (h : DSHist)
    (hEq : h.state (bucketDSParams impl M w L vCap eCap k) = st.dyn p) :
    let info := stepBundleTree (fun _ => canonicalSparsify impl) st U ord ord'
    DSHist.state (bucketDSParams impl M w L vCap eCap k) ⟨h.G₀, h.Us ++ [info.U_B p]⟩ =
      info.state.dyn p := by
  intro info
  rw [dsHist_state_snoc, hEq]
  rfl

/-- After `restartBundleTree` with `sparsify := fun _ => canonicalSparsify impl`, for every active
component `C ∈ tr.activeComps` and bucket `b`, the empty `DSHist` on the normalized rebuilt bundle
graph `normGraph (restartBucketBundle tr ord C b).graph` has the exact model state `tr'.dyn (C, b)`. -/
theorem bucketDSParams_restart_eq_bundleTree (impl : SparsifyImpl) (M w L vCap eCap k : ℕ)
    (tr : BundleTreeState L) (ord : ℕ → List End) (C : Finset ℕ) (b : ℤ)
    (hAct : C ∈ tr.activeComps) (hSB : tr.splitBound = bundleSplitBudget k M) :
    let tr' := restartBundleTree L (fun _ => canonicalSparsify impl) tr ord
    let P := bucketDSParams impl M w L vCap eCap k
    DSHist.state P ⟨normGraph (restartBucketBundle tr ord C b).graph, []⟩ = tr'.dyn (C, b) := by
  intro tr' P
  rw [dsHist_state_nil]
  simp only [tr', restartBundleTree, hAct, ↓reduceIte, P, bucketDSParams, hSB]

/-! ## Links between P6 spanner charges and model `spanInitBound` / `spanBatchChargeWith` -/

/-- When `impl.γ_t mMax = 1`, absorbing `γ_t` into `K_t` leaves `canonicalSparsifyParams impl mMax`
unchanged. -/
theorem canonicalSparsifyParams_absorbTime_eq_of_unit (impl : SparsifyImpl) (mMax : ℕ)
    (hγt : impl.γ_t mMax = 1) :
    (canonicalSparsifyParams impl mMax).absorbTime = canonicalSparsifyParams impl mMax := by
  unfold SparsifyParams.absorbTime canonicalSparsifyParams
  simp [hγt]

/-- Exact identity: P6's `dsBatchCharge` is literally the model's `spanBatchChargeWith` at
`dsAmortConst impl` and `(canonicalSparsifyParams impl mMax).absorbTime`. -/
theorem dsBatchCharge_eq_spanBatchChargeWith (impl : SparsifyImpl) (mMax L nMax : ℕ)
    (G₀ G : MGraph) (U : List Update) :
    dsBatchCharge impl mMax L nMax G₀ G U =
      spanBatchChargeWith (dsAmortConst impl) (canonicalSparsifyParams impl mMax).absorbTime
        L nMax G₀ G U :=
  rfl

/-- Unit-time-factor specialization of `dsBatchCharge_eq_spanBatchChargeWith`: when
`impl.γ_t mMax = 1`, P6's `dsBatchCharge` equals `spanBatchChargeWith` directly at
`canonicalSparsifyParams impl mMax`. -/
theorem dsBatchCharge_eq_spanBatchChargeWith_of_unit (impl : SparsifyImpl) (mMax L nMax : ℕ)
    (G₀ G : MGraph) (U : List Update) (hγt : impl.γ_t mMax = 1) :
    dsBatchCharge impl mMax L nMax G₀ G U =
      spanBatchChargeWith (dsAmortConst impl) (canonicalSparsifyParams impl mMax)
        L nMax G₀ G U := by
  rw [dsBatchCharge_eq_spanBatchChargeWith, canonicalSparsifyParams_absorbTime_eq_of_unit _ _ hγt]

private lemma levelPot_init_eq_H_m (L : ℕ) (G : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut) :
    levelPot (runState (L := L) G q sparsify [] 0) = (init G L q sparsify).state.H.m := by
  change levelPot (init G L q sparsify).state = _
  rw [levelPot_init]
  rfl

private lemma natLog2_add_two_le (n : ℕ) :
    ((Nat.log 2 (n + 2) + 2 : ℕ) : ℝ) ≤ 2 * (1 + Real.log ((n : ℝ) + 2)) := by
  have hpow : (2 : ℝ) ^ Nat.log 2 (n + 2) ≤ (n : ℝ) + 2 := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)
  have hlog_pow : (Nat.log 2 (n + 2) : ℝ) * Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 (n + 2)) hpow
    rwa [Real.log_pow] at h1
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hk_nn : (0 : ℝ) ≤ (Nat.log 2 (n + 2) : ℝ) := Nat.cast_nonneg _
  have hhalf : (Nat.log 2 (n + 2) : ℝ) * (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    le_trans (mul_le_mul_of_nonneg_left hlog2 hk_nn) hlog_pow
  push_cast
  linarith

/-- P6's spanner-activation cost formula (`phaseBaseCost` + `dsInitContract` + `dsInitBank` + `35`)
is bounded with constant `1` by `dsAmortConst P.impl * spanInitBound P_a P.L P.splitBound G`. -/
theorem dsInitActivateCost_le_spanInitBound (P : DSParams) (G : MGraph)
    (hG : G.IsValid) (hGm : G.m ≤ P.mMax) :
    ((45 * P.L + 80) * (Nat.log 2 (G.n + P.splitBound + 2) + 2) + 80) +
      (dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 + dsInitBank P G) + 35 ≤
    dsAmortConst P.impl *
      spanInitBound (canonicalSparsifyParams P.impl P.mMax).absorbTime P.L P.splitBound G := by
  set q := phaseBase (G.n + P.splitBound) P.L
  set P₀ := canonicalSparsifyParams P.impl P.mMax
  set Pa := P₀.absorbTime
  set Gact := activeSubgraph G
  set initOut := init G P.L q (canonicalSparsify P.impl)
  have hcore := dsInit_initCostBound P.impl P.mMax P.w P.L q P.vCap P.eCap G [] [] [] (fun _ => 0)
    hG hGm
  have hcore_eq : (dsInitContract P.impl P.mMax P.w P.L q P.vCap P.eCap G [] []).cost [] (fun _ => 0) =
      dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 := rfl
  rw [hcore_eq] at hcore
  have hbank_eq : dsInitBank P G = 1440 * initOut.state.H.m := by
    unfold dsInitBank
    rw [levelPot_init_eq_H_m]
  have hHm_le : (initOut.state.H.m : ℝ) ≤
      Pa.K_s * (G.n : ℝ) * Pa.γ_ℓ * (1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2)) ^ Pa.p_s := by
    by_cases hE : G.E.Nonempty
    · have hspec := canonicalSparsify_spec_absorb P.impl P.mMax Gact Gact idEmb
        (activeSubgraph_isValid hG) (activeSubgraph_isValid hG)
        hGm (fun h => by rw [idEmb_length_eq_one h]) (idEmb_isEmbedding Gact)
      have hHm_eq : initOut.state.H.m = (canonicalSparsify P.impl Gact Gact idEmb).Jtilde.m := by
        simp [initOut, init, initAt, initCore, hE, Gact, MGraph.m]
      rw [hHm_eq]
      have h1 := hspec.2.2.2.2.1
      have hact_n : (Gact.n : ℝ) ≤ (G.n : ℝ) := by exact_mod_cast activeSubgraph_n_le G
      have hact_m : (Gact.m : ℝ) = (G.m : ℝ) := rfl
      have hlog_le : 1 + Real.log ((Gact.n : ℝ) + (Gact.m : ℝ) + 2) ≤
          1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2) := by
        rw [hact_m]
        have hpos : (0 : ℝ) < (Gact.n : ℝ) + (G.m : ℝ) + 2 := by positivity
        linarith [Real.log_le_log hpos (show (Gact.n : ℝ) + (G.m : ℝ) + 2 ≤ (G.n : ℝ) + (G.m : ℝ) + 2 by linarith)]
      have hlog_nn : 0 ≤ 1 + Real.log ((Gact.n : ℝ) + (Gact.m : ℝ) + 2) := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ (Gact.n : ℝ) + (Gact.m : ℝ) + 2 by linarith)]
      have hpow : (1 + Real.log ((Gact.n : ℝ) + (Gact.m : ℝ) + 2)) ^ Pa.p_s ≤
          (1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2)) ^ Pa.p_s :=
        pow_le_pow_left₀ hlog_nn hlog_le Pa.p_s
      have hKs_nn : 0 ≤ Pa.K_s := Pa.hK_s
      have hγℓ_nn : 0 ≤ Pa.γ_ℓ := by linarith [Pa.hγ_ℓ]
      refine le_trans h1 ?_
      gcongr
    · have hHm0 : initOut.state.H.m = 0 := by
        simp [initOut, init, initAt, initCore, hE, emptyGraphOn, MGraph.m]
      rw [hHm0, Nat.cast_zero]
      have hKs_nn : 0 ≤ Pa.K_s := Pa.hK_s
      have hγℓ_nn : 0 ≤ Pa.γ_ℓ := by linarith [Pa.hγ_ℓ]
      have hlog_nn : 0 ≤ 1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2) := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ (G.n : ℝ) + (G.m : ℝ) + 2 by linarith)]
      positivity
  set nMax := G.n + P.splitBound
  have hlogN_ge1 : 1 ≤ 1 + Real.log ((nMax : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ (nMax : ℝ) + 2 by linarith)]
  have hpb_le : (((45 * P.L + 80) * (Nat.log 2 (nMax + 2) + 2) + 80 + 35 : ℕ) : ℝ) ≤
      275 * (((P.L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2)) + 1) := by
    have hlog2 := natLog2_add_two_le nMax
    have hL_nn : (0 : ℝ) ≤ (P.L : ℝ) := Nat.cast_nonneg _
    have h45 : (45 : ℝ) * (P.L : ℝ) + 80 ≤ 80 * ((P.L : ℝ) + 1) := by linarith
    have hmul : ((45 : ℝ) * (P.L : ℝ) + 80) * ((Nat.log 2 (nMax + 2) + 2 : ℕ) : ℝ) ≤
        80 * ((P.L : ℝ) + 1) * (2 * (1 + Real.log ((nMax : ℝ) + 2))) :=
      mul_le_mul h45 hlog2 (Nat.cast_nonneg _) (by positivity)
    have hmul_eq : 80 * ((P.L : ℝ) + 1) * (2 * (1 + Real.log ((nMax : ℝ) + 2))) =
        160 * (((P.L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2))) := by ring
    have hprod_nn : 0 ≤ ((P.L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2)) :=
      mul_nonneg (by positivity) (by linarith)
    push_cast at hmul ⊢
    linarith
  set B_real : ℝ :=
    Pa.K_t * (((Gact.n : ℝ) + (G.m : ℝ) * Pa.γ_ℓ ^ 2) *
      (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max Pa.p_t 1) +
    Pa.K_s * (G.n : ℝ) * Pa.γ_ℓ *
      (1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2)) ^ Pa.p_s +
    (G.n : ℝ) + (G.m : ℝ) + (G.m : ℝ) * Pa.γ_ℓ +
    ((P.L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2)) + 1
  have hB_le_ceil : B_real ≤ (spanInitBound Pa P.L P.splitBound G : ℝ) := Nat.le_ceil B_real
  have hKt_eq : P₀.K_t * P₀.γ_t = Pa.K_t := rfl
  have hcore_le : ((dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 : ℕ) : ℝ) ≤
      (dsInitCostFactor P.impl : ℝ) * B_real := by
    have hL1 : (P.L : ℝ) + 1 ≤ ((P.L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2)) :=
      le_mul_of_one_le_right (by positivity) hlogN_ge1
    have hinner : P₀.K_t * P₀.γ_t * ((Gact.n : ℝ) + (G.m : ℝ) * P₀.γ_ℓ ^ 2) *
          (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max P₀.p_t 1 +
          (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * P₀.γ_ℓ + (P.L : ℝ) + 1 ≤
        B_real := by
      dsimp only [B_real]
      change P₀.K_t * P₀.γ_t * ((Gact.n : ℝ) + (G.m : ℝ) * Pa.γ_ℓ ^ 2) *
          (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max Pa.p_t 1 +
          (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * Pa.γ_ℓ + (P.L : ℝ) + 1 ≤ _
      rw [hKt_eq, mul_assoc]
      linarith [hHm_le, hL1]
    exact le_trans hcore (mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _))
  have hB_nn : 0 ≤ B_real := by
    have hKt_nn : 0 ≤ Pa.K_t := Pa.hK_t
    have hKs_nn : 0 ≤ Pa.K_s := Pa.hK_s
    have hγℓ_nn : 0 ≤ Pa.γ_ℓ := by linarith [Pa.hγ_ℓ]
    have hlog1 : 0 ≤ 1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (Gact.n : ℝ) + (G.m : ℝ) + 2 by linarith)]
    have hlog2 : 0 ≤ 1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (G.n : ℝ) + (G.m : ℝ) + 2 by linarith)]
    dsimp only [B_real]; positivity
  have hHm_le_B : (initOut.state.H.m : ℝ) ≤ B_real := by
    have hKt_nn : 0 ≤ Pa.K_t := Pa.hK_t
    have hγℓ_nn : 0 ≤ Pa.γ_ℓ := by linarith [Pa.hγ_ℓ]
    have hlog1 : 0 ≤ 1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (Gact.n : ℝ) + (G.m : ℝ) + 2 by linarith)]
    have hterm1 : 0 ≤ Pa.K_t * (((Gact.n : ℝ) + (G.m : ℝ) * Pa.γ_ℓ ^ 2) *
        (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max Pa.p_t 1) := by positivity
    have hterm3 : 0 ≤ (G.n : ℝ) + (G.m : ℝ) + (G.m : ℝ) * Pa.γ_ℓ +
        ((P.L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2)) + 1 := by positivity
    dsimp only [B_real]; linarith
  have hpb_le_B : (((45 * P.L + 80) * (Nat.log 2 (nMax + 2) + 2) + 80 + 35 : ℕ) : ℝ) ≤
      275 * B_real := by
    have hKt_nn : 0 ≤ Pa.K_t := Pa.hK_t
    have hKs_nn : 0 ≤ Pa.K_s := Pa.hK_s
    have hγℓ_nn : 0 ≤ Pa.γ_ℓ := by linarith [Pa.hγ_ℓ]
    have hlog1 : 0 ≤ 1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (Gact.n : ℝ) + (G.m : ℝ) + 2 by linarith)]
    have hlog2 : 0 ≤ 1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (G.n : ℝ) + (G.m : ℝ) + 2 by linarith)]
    have hrest : 0 ≤ Pa.K_t * (((Gact.n : ℝ) + (G.m : ℝ) * Pa.γ_ℓ ^ 2) *
          (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max Pa.p_t 1) +
        Pa.K_s * (G.n : ℝ) * Pa.γ_ℓ *
          (1 + Real.log ((G.n : ℝ) + (G.m : ℝ) + 2)) ^ Pa.p_s +
        (G.n : ℝ) + (G.m : ℝ) + (G.m : ℝ) * Pa.γ_ℓ := by positivity
    have hle : ((P.L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2)) + 1 ≤ B_real := by
      dsimp only [B_real]; linarith
    linarith [hpb_le]
  have hamort_ge : (dsInitCostFactor P.impl : ℝ) + 1440 + 275 ≤ (dsAmortConst P.impl : ℝ) := by
    unfold dsAmortConst; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (dsStepPosFactor P.impl)]
  have htot : ((((45 * P.L + 80) * (Nat.log 2 (nMax + 2) + 2) + 80) +
      (dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 + dsInitBank P G) + 35 : ℕ) : ℝ) ≤
      (dsAmortConst P.impl : ℝ) * (spanInitBound Pa P.L P.splitBound G : ℝ) := by
    rw [hbank_eq]
    have hrearr : ((((45 * P.L + 80) * (Nat.log 2 (nMax + 2) + 2) + 80) +
          (dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 +
            1440 * initOut.state.H.m) + 35 : ℕ) : ℝ) =
        (((45 * P.L + 80) * (Nat.log 2 (nMax + 2) + 2) + 80 + 35 : ℕ) : ℝ) +
          ((dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 : ℕ) : ℝ) +
          1440 * (initOut.state.H.m : ℝ) := by push_cast; ring
    rw [hrearr]
    have h1 : (((45 * P.L + 80) * (Nat.log 2 (nMax + 2) + 2) + 80 + 35 : ℕ) : ℝ) +
        ((dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 : ℕ) : ℝ) +
        1440 * (initOut.state.H.m : ℝ) ≤
        ((dsInitCostFactor P.impl : ℝ) + 1440 + 275) * B_real := by linarith
    have h2 : ((dsInitCostFactor P.impl : ℝ) + 1440 + 275) * B_real ≤
        (dsAmortConst P.impl : ℝ) * B_real :=
      mul_le_mul_of_nonneg_right hamort_ge hB_nn
    have h3 : (dsAmortConst P.impl : ℝ) * B_real ≤
        (dsAmortConst P.impl : ℝ) * (spanInitBound Pa P.L P.splitBound G : ℝ) :=
      mul_le_mul_of_nonneg_left hB_le_ceil (Nat.cast_nonneg _)
    exact le_trans h1 (le_trans h2 h3)
  exact_mod_cast htot

/-! ## Exact natural-number characterizations for Word-RAM parameter procedures -/

/-- Exact natural-number ceiling division formula for `Nat.ceil ((a : ℝ) / (b : ℝ))`. -/
theorem natCeil_div_eq (a b : ℕ) (hb : 1 ≤ b) :
    Nat.ceil ((a : ℝ) / (b : ℝ)) = (a + b - 1) / b := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hb_pos]
    have hmul : a ≤ ((a + b - 1) / b) * b := by
      have h1 : a + b - 1 < ((a + b - 1) / b + 1) * b := by
        have hdm := Nat.div_add_mod (a + b - 1) b
        have hlt := Nat.mod_lt (a + b - 1) (by omega : 0 < b)
        nlinarith
      rw [Nat.add_one_mul] at h1
      omega
    exact_mod_cast hmul
  · have hle : (a : ℝ) / (b : ℝ) ≤ (Nat.ceil ((a : ℝ) / (b : ℝ)) : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hb_pos] at hle
    have hmul : a ≤ Nat.ceil ((a : ℝ) / (b : ℝ)) * b := by exact_mod_cast hle
    have hlt : a + b - 1 < (Nat.ceil ((a : ℝ) / (b : ℝ)) + 1) * b := by
      rw [Nat.add_one_mul]; omega
    have hdiv : (a + b - 1) / b < Nat.ceil ((a : ℝ) / (b : ℝ)) + 1 :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).mpr hlt
    omega

/-- Exact integer arithmetic formula for `bundleSplitBudget k M` when `1 ≤ k`. -/
theorem bundleSplitBudget_eq_div (k M : ℕ) (hk : 1 ≤ k) :
    bundleSplitBudget k M = 2 * ((56 * M + k - 1) / k) := by
  unfold bundleSplitBudget
  have hcast : (56 : ℝ) * (M : ℝ) = ((56 * M : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, natCeil_div_eq (56 * M) k hk]

/-- When `nCap ≤ 1`, `phaseBase nCap L = 2`. -/
theorem phaseBase_of_le_one {nCap L : ℕ} (h : nCap ≤ 1) : phaseBase nCap L = 2 := by
  have hmax : max nCap 1 = 1 := max_eq_right h
  unfold phaseBase
  rw [hmax]
  simp

/-- Exact threshold characterization of `phaseBase nCap L` for `1 ≤ L`, `1 ≤ nCap`, `2 ≤ q`:
`phaseBase nCap L ≤ q ↔ nCap ≤ q ^ L`. -/
theorem phaseBase_le_iff {nCap L q : ℕ} (hL : 1 ≤ L) (hn : 1 ≤ nCap) (hq : 2 ≤ q) :
    phaseBase nCap L ≤ q ↔ nCap ≤ q ^ L := by
  have hmaxN : max nCap 1 = nCap := max_eq_left hn
  have hmaxL : max (L : ℝ) 1 = (L : ℝ) := max_eq_left (by exact_mod_cast hL)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hn_nn : (0 : ℝ) ≤ (nCap : ℝ) := Nat.cast_nonneg _
  have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  unfold phaseBase
  rw [hmaxN, hmaxL, max_le_iff]
  simp only [hq, true_and, Nat.ceil_le]
  constructor
  · intro h
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hn_nn _) h (Nat.cast_nonneg L)
    rw [← Real.rpow_mul hn_nn, one_div_mul_cancel (ne_of_gt hL_pos), Real.rpow_one,
      Real.rpow_natCast] at hpow
    exact_mod_cast hpow
  · intro h
    have hr : (nCap : ℝ) ≤ (q : ℝ) ^ (L : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast h
    have hpow := Real.rpow_le_rpow hn_nn hr (by positivity : (0 : ℝ) ≤ 1 / (L : ℝ))
    rw [← Real.rpow_mul hq_nn, mul_one_div_cancel (ne_of_gt hL_pos), Real.rpow_one] at hpow
    exact hpow

/-- When `1 ≤ L` and `nCap ≤ 2 ^ L`, `phaseBase nCap L = 2`. -/
theorem phaseBase_eq_two_of_le_pow {nCap L : ℕ} (hL : 1 ≤ L) (h : nCap ≤ 2 ^ L) :
    phaseBase nCap L = 2 := by
  by_cases hn : nCap ≤ 1
  · exact phaseBase_of_le_one hn
  · exact le_antisymm ((phaseBase_le_iff hL (by omega) le_rfl).mpr h) (two_le_phaseBase nCap L)

/-- Binary-search termination characterization of `phaseBase nCap L`: if `2 ≤ lo`, `lo ^ L < nCap`,
and `nCap ≤ (lo + 1) ^ L`, then `phaseBase nCap L = lo + 1`. -/
theorem phaseBase_eq_of_bracket {nCap L lo : ℕ} (hL : 1 ≤ L) (hlo : 2 ≤ lo)
    (hlt : lo ^ L < nCap) (hle : nCap ≤ (lo + 1) ^ L) :
    phaseBase nCap L = lo + 1 := by
  have hn : 1 ≤ nCap := by
    have h1 : 1 ≤ lo ^ L := Nat.one_le_pow L lo (by omega)
    omega
  have h1 : phaseBase nCap L ≤ lo + 1 :=
    (phaseBase_le_iff hL hn (by omega)).mpr hle
  have h2 : ¬ phaseBase nCap L ≤ lo := by
    rw [phaseBase_le_iff hL hn hlo]
    omega
  omega

/-- Overflow-free multiplication threshold: for `1 ≤ target`, `1 ≤ base`,
`target ≤ acc * base ↔ (target - 1) / base < acc`. -/
theorem le_mul_iff_div_lt {target acc base : ℕ} (ht : 1 ≤ target) (hb : 1 ≤ base) :
    target ≤ acc * base ↔ (target - 1) / base < acc := by
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < base), mul_comm]
  omega

/-! ## Helper for locating edges leaving `H` (`D_left`) -/

/-- Any edge present in `H` before a batch `uhActual` and absent from `H.applyBatch uhActual`
appears as `.delete e` in `uhActual`. -/
theorem delete_mem_of_mem_H_sdiff {H : MGraph} {uhActual : List Update} {e : ℕ}
    (heBefore : e ∈ H.E) (heAfter : e ∉ (H.applyBatch uhActual).E) :
    Update.delete e ∈ uhActual :=
  exists_delete_of_mem_sdiff_applyBatch H uhActual heBefore heAfter

end

end MinCostFlow.SparseCore.Program
