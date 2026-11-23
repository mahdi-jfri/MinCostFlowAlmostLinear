module

public import MinCostFlow.LSF.Program.Layout
public import MinCostFlow.LSF.Lemma54With
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Model properties of `initLSFWith` on a one-vertex graph

When `G₀` has a single vertex `r₀`, every edge of `G₀` is a self-loop at `r₀`. The trivial tree
`oneVertTree r₀` with vertex set `{r₀}` and no edges satisfies `IsLSST`, the empty decomposition
`∅` satisfies `IsTreeDecompSpec`, every edge has `levelStretchBound = 6 < defaultThreshNat`, and
`initLSFWith` yields a rooted forest with root set `{r₀}`, no edges, empty `W_init`, and `wstr = 6`
on every edge of `G₀`.
-/

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- The one-vertex, zero-edge spanning tree on `{r₀}`. -/
def oneVertTree (r₀ : ℕ) : MGraph where
  V := {r₀}
  E := ∅
  tail := fun _ => 0
  head := fun _ => 0

lemma oneVert_V_eq {G₀ : MGraph} {r₀ : ℕ} (hn1 : G₀.n = 1) (hr₀ : r₀ ∈ G₀.V) :
    G₀.V = {r₀} := by
  have hcard : G₀.V.card = 1 := hn1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  rw [ha] at hr₀ ⊢
  rw [Finset.mem_singleton.mp hr₀]

lemma projectTree_oneVert_V {G₀ : MGraph} {v : ℕ → ℝ} {r₀ : ℕ} :
    (projectTree G₀ v (oneVertTree r₀)).V = {r₀} := by
  classical
  unfold projectTree oneVertTree
  split_ifs <;> rfl

lemma projectTree_oneVert_E {G₀ : MGraph} {v : ℕ → ℝ} {r₀ : ℕ} :
    (projectTree G₀ v (oneVertTree r₀)).E = ∅ := by
  classical
  unfold projectTree oneVertTree
  split_ifs <;> simp

lemma oneVert_isSpanningTreeOn {V : Finset ℕ} {r₀ : ℕ} (hV : V = {r₀}) :
    (oneVertTree r₀).IsSpanningTreeOn V := by
  refine ⟨⟨fun e he => absurd he (Finset.notMem_empty _), fun Q hQ => ?_⟩, hV.symm, ?_⟩
  · rcases hQ with ⟨hQne, -, u, hWQ⟩
    cases Q with
    | nil => exact hQne rfl
    | cons x xs =>
      have hx : x.1 ∈ (oneVertTree r₀).E := IsWalk_edges_mem hWQ List.mem_cons_self
      exact absurd hx (Finset.notMem_empty _)
  · intro u hu w hw
    rw [hV, Finset.mem_singleton] at hu hw
    subst hu; subst hw
    exact ⟨[], MGraph.IsWalk.nil _⟩

lemma oneVert_forestPath_nil {T : MGraph} {r₀ : ℕ} (hF : T.IsForest) :
    T.forestPath r₀ r₀ = [] :=
  forestPath_eq_of_isPath hF ⟨MGraph.IsWalk.nil r₀, List.nodup_singleton r₀⟩

lemma oneVert_isLSST_aux {G : MGraph} {ℓ : ℕ → ℝ} {γ : ℝ} {r₀ : ℕ}
    (hG : G.IsValid) (hV : G.V = {r₀}) (hγ : 1 ≤ γ) :
    IsLSST G ℓ (fun _ => 1) γ (oneVertTree r₀) := by
  have hST := oneVert_isSpanningTreeOn hV
  have hfp : (oneVertTree r₀).forestPath r₀ r₀ = [] :=
    oneVert_forestPath_nil hST.1
  refine ⟨hST, fun _ he => absurd he (Finset.notMem_empty _), ?_, ?_⟩
  · intro e he f hf
    have huv := hG e he
    rw [hV, Finset.mem_singleton, Finset.mem_singleton] at huv
    rw [huv.1, huv.2, hfp] at hf
    simp [walkEdges] at hf
  · have hsum : ∑ e ∈ G.E, (1 : ℝ) * treeStretch G (oneVertTree r₀) ℓ e = (G.E.card : ℝ) := by
      have hterm : ∀ e ∈ G.E, (1 : ℝ) * treeStretch G (oneVertTree r₀) ℓ e = 1 := by
        intro e he
        have huv := hG e he
        rw [hV, Finset.mem_singleton, Finset.mem_singleton] at huv
        simp [treeStretch, huv.1, huv.2, hfp, walkLength]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hnorm : G.norm1 (fun _ => 1) = (G.E.card : ℝ) := by
      simp [MGraph.norm1]
    rw [hsum, hnorm]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hγ

lemma oneVert_gamma_ge_one (K_AN : ℝ) :
    (1 : ℝ) ≤ (4 * max K_AN 1 + 5) * (Real.log ((1 : ℝ) + 2)) ^ 2 := by
  have hC : (9 : ℝ) ≤ 4 * max K_AN 1 + 5 := by
    have := le_max_right K_AN 1
    linarith
  have hlog : (1 : ℝ) / 2 < Real.log ((1 : ℝ) + 2) := by
    have h := (real_log_add_two_bounds 1).1
    have hlg : Nat.log 2 (1 + 2) = 1 := by decide
    rw [hlg] at h
    norm_num at h ⊢
    linarith
  have hsq : (1 : ℝ) / 4 < (Real.log ((1 : ℝ) + 2)) ^ 2 := by nlinarith
  have hmul : (9 : ℝ) * (1 / 4) ≤ (4 * max K_AN 1 + 5) * (Real.log ((1 : ℝ) + 2)) ^ 2 :=
    mul_le_mul hC (le_of_lt hsq) (by norm_num) (by linarith)
  norm_num at hmul ⊢
  linarith

lemma oneVert_isLSST {G₀ : MGraph} {K_AN : ℝ} {ℓ v : ℕ → ℝ} {r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hn1 : G₀.n = 1) (hr₀ : r₀ ∈ G₀.V) :
    IsLSST
      (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
      (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ else fun _ => 1)
      (fun _ => 1)
      ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2)
      (oneVertTree r₀) := by
  classical
  have hV := oneVert_V_eq hn1 hr₀
  have hγ : (1 : ℝ) ≤ (4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    rw [hn1, Nat.cast_one]
    exact oneVert_gamma_ge_one K_AN
  split_ifs with hE
  · exact oneVert_isLSST_aux (weightedCopyGraph_isValid hG₀ v)
      ((weightedCopyGraph_V G₀ v).trans hV) hγ
  · exact oneVert_isLSST_aux hG₀ hV hγ

lemma oneVert_isCompReps {G₀ : MGraph} {r₀ : ℕ} (hn1 : G₀.n = 1) (hr₀ : r₀ ∈ G₀.V) :
    IsCompReps G₀ r₀ {r₀} := by
  have hV := oneVert_V_eq hn1 hr₀
  refine ⟨Finset.mem_singleton_self r₀, Finset.singleton_subset_iff.mpr hr₀, ?_, ?_⟩
  · have hne : (components G₀).Nonempty := ⟨compOf G₀ r₀, Finset.mem_image.mpr ⟨r₀, hr₀, rfl⟩⟩
    simpa using Finset.card_pos.mpr hne
  · intro w hw
    rw [hV, Finset.mem_singleton] at hw
    subst hw
    exact ⟨w, Finset.mem_singleton_self w, ⟨[], MGraph.IsWalk.nil w⟩⟩

lemma oneVert_isTreeDecompSpec {G₀ : MGraph} {v : ℕ → ℝ} {r₀ : ℕ} {k : ℝ} (hk : 1 ≤ k) :
    IsTreeDecompSpec G₀ (projectTree G₀ v (oneVertTree r₀)) k ∅ := by
  have hE : (projectTree G₀ v (oneVertTree r₀)).E = ∅ := projectTree_oneVert_E
  have hb : boundary (∅ : Finset (Finset ℕ)) = ∅ := by
    ext x
    simp [boundary]
  refine ⟨fun _ h => absurd h (Finset.notMem_empty _),
    fun _ h => absurd h (Finset.notMem_empty _),
    by rw [Finset.biUnion_empty, hE], ?_, ?_,
    fun _ h => absurd h (Finset.notMem_empty _)⟩
  · rw [hb, Finset.card_empty, Nat.cast_zero]
    positivity
  · rw [Finset.card_empty, Nat.cast_zero]
    positivity

lemma oneVert_validLSFParams {G₀ : MGraph} {K_AN : ℝ} {ℓ v : ℕ → ℝ} {kk r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hn1 : G₀.n = 1) (hr₀ : r₀ ∈ G₀.V) (hk : 1 ≤ kk) :
    ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
      (defaultThreshNat K_AN G₀.n kk : ℝ) (defaultK_sigma K_AN : ℝ)
      G₀ ℓ v (kk : ℝ) (oneVertTree r₀) r₀ {r₀} (fun _ => 0) ∅ where
  hT_raw := oneVert_isLSST hG₀ hn1 hr₀
  hr₀ := hr₀
  hC_reps := oneVert_isCompReps hn1 hr₀
  hπ := by
    have hE : (projectTree G₀ v (oneVertTree r₀)).E = ∅ := projectTree_oneVert_E
    refine ⟨fun _ hf => absurd (hE ▸ hf) (Finset.notMem_empty _),
      by norm_num, fun _ hf => absurd (hE ▸ hf) (Finset.notMem_empty _)⟩
  hW_T := oneVert_isTreeDecompSpec (by exact_mod_cast hk)
  hthresh := defaultThreshNat_isWstrThresh (by exact_mod_cast hk) le_rfl (by
    have : (0 : ℝ) ≤ (kk : ℝ) := Nat.cast_nonneg kk
    linarith)

lemma oneVert_levelStretchBound {G₀ : MGraph} {v ℓ : ℕ → ℝ} {r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hn1 : G₀.n = 1) (hr₀ : r₀ ∈ G₀.V) {e : ℕ} (he : e ∈ G₀.E) :
    levelStretchBound (projectTree G₀ v (oneVertTree r₀)) r₀ (fun _ => 0) G₀ (safeLen G₀ ℓ) e =
      6 := by
  have hV := oneVert_V_eq hn1 hr₀
  have hTV : (projectTree G₀ v (oneVertTree r₀)).V = {r₀} := projectTree_oneVert_V
  have hTE : (projectTree G₀ v (oneVertTree r₀)).E = ∅ := projectTree_oneVert_E
  have hcard : (projectTree G₀ v (oneVertTree r₀)).V.card = 1 := by rw [hTV]; simp
  have huv := hG₀ e he
  rw [hV, Finset.mem_singleton, Finset.mem_singleton] at huv
  unfold levelStretchBound
  dsimp only
  rw [hcard]
  have hD : (Nat.log 2 1 + 1) * (Nat.log 2 1 + 2) + 1 = 3 := by decide
  rw [hD]
  have hterm : ∀ i ∈ Finset.range 3,
      (rootedForestGivenRoots (projectTree G₀ v (oneVertTree r₀)) r₀
        (levelRoots (projectTree G₀ v (oneVertTree r₀)) r₀ i) (fun _ => 0)).stretch
        G₀ (safeLen G₀ ℓ) e = 1 := by
    intro i _
    set RF := rootedForestGivenRoots (projectTree G₀ v (oneVertTree r₀)) r₀
      (levelRoots (projectTree G₀ v (oneVertTree r₀)) r₀ i) (fun _ => 0)
    have hFV : RF.F.V = {r₀} := by
      show (forestGivenRoots _ _ _ _).V = {r₀}
      simp [forestGivenRoots, hTV]
    have hFE : RF.F.E = ∅ := by
      show (forestGivenRoots _ _ _ _).E = ∅
      simp [forestGivenRoots, hTE]
    have hFF : RF.F.IsForest := by
      refine ⟨fun f hf => absurd (hFE ▸ hf) (Finset.notMem_empty _), fun Q hQ => ?_⟩
      rcases hQ with ⟨hQne, -, u, hWQ⟩
      cases Q with
      | nil => exact hQne rfl
      | cons x xs =>
        have hx : x.1 ∈ RF.F.E := IsWalk_edges_mem hWQ List.mem_cons_self
        exact absurd (hFE ▸ hx) (Finset.notMem_empty _)
    have hfp : RF.F.forestPath r₀ r₀ = [] := oneVert_forestPath_nil hFF
    simp [RootedForest.stretch, huv.1, huv.2, hfp, walkLength]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
  norm_num

lemma six_lt_defaultThreshNat_one (K_AN : ℝ) {kk : ℕ} (hk : 1 ≤ kk) :
    6 < defaultThreshNat K_AN 1 kk := by
  have hC : 9 ≤ defaultC_ceil K_AN := by
    have h1 : 1 ≤ Nat.ceil (max K_AN 1) := Nat.one_le_ceil_iff.mpr (by positivity)
    unfold defaultC_ceil
    omega
  have hD : hldDepthBound 1 = 2 := by decide
  have hlg : Nat.log 2 (1 + 2) = 1 := by decide
  have hval : 2916 ≤ 9 * (hldDepthBound 1 + 1) ^ 2 * defaultC_ceil K_AN *
      (Nat.log 2 (1 + 2) + 1) ^ 2 * kk := by
    rw [hD, hlg]
    nlinarith
  have hle : 9 * (hldDepthBound 1 + 1) ^ 2 * defaultC_ceil K_AN *
      (Nat.log 2 (1 + 2) + 1) ^ 2 * kk ≤ defaultThreshNat K_AN 1 kk := Nat.le_max_right _ _
  omega

/-- Concrete field identities for `initLSFWith` on a one-vertex graph. -/
lemma oneVert_initLSFWith_fields {G₀ : MGraph} {K_AN : ℝ} {ℓ v : ℕ → ℝ} {kk r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hn1 : G₀.n = 1) (hr₀ : r₀ ∈ G₀.V) (hk : 1 ≤ kk) :
    let S := initLSFWith G₀ ℓ v (kk : ℝ) (oneVertTree r₀) r₀ {r₀} (fun _ => 0) ∅
      (defaultThreshNat K_AN G₀.n kk : ℝ)
    S.G₀ = G₀ ∧ S.G = G₀ ∧ S.r₀ = r₀ ∧ S.π = (fun _ => 0) ∧
    S.numUpdates = 0 ∧ S.origVert = id ∧
    S.T₀.V = {r₀} ∧ S.T₀.E = ∅ ∧ S.T_cur = S.T₀ ∧
    S.R₀_init = {r₀} ∧ S.R_orig = {r₀} ∧ S.R = {r₀} ∧
    S.RF.R = {r₀} ∧ S.RF.F.V = {r₀} ∧ S.RF.F.E = ∅ ∧
    S.W_init = ∅ ∧
    ∀ e ∈ G₀.E, S.wstr e = 6 := by
  classical
  intro S
  have hT₀V : S.T₀.V = {r₀} := projectTree_oneVert_V
  have hT₀E : S.T₀.E = ∅ := projectTree_oneVert_E
  have hth : (6 : ℝ) < (defaultThreshNat K_AN G₀.n kk : ℝ) := by
    rw [hn1]
    exact_mod_cast six_lt_defaultThreshNat_one K_AN hk
  have hraw : ∀ e ∈ G₀.E,
      levelStretchBound S.T₀ r₀ (fun _ => 0) G₀ (safeLen G₀ ℓ) e = 6 :=
    fun e he => oneVert_levelStretchBound hG₀ hn1 hr₀ he
  have hEhigh : G₀.E.filter (fun e =>
      (defaultThreshNat K_AN G₀.n kk : ℝ) ≤
        levelStretchBound S.T₀ r₀ (fun _ => 0) G₀ (safeLen G₀ ℓ) e) = ∅ := by
    ext e
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro he hle
    rw [hraw e he] at hle
    linarith
  have hR0 : S.R₀_init = {r₀} := by
    have hb : boundary (∅ : Finset (Finset ℕ)) = ∅ := by ext x; simp [boundary]
    show {r₀} ∪ boundary ∅ ∪ _ = {r₀}
    dsimp only
    rw [hb, show {e ∈ G₀.E | (defaultThreshNat K_AN G₀.n kk : ℝ) ≤
        levelStretchBound (projectTree G₀ v (oneVertTree r₀)) r₀ (fun _ => 0) G₀ (safeLen G₀ ℓ) e} =
        ∅ from hEhigh]
    simp
  have hT₀_rt : IsRootedTree S.T₀ r₀ := by
    have hST : S.T₀.IsSpanningTreeOn {r₀} := by
      refine ⟨⟨fun f hf => absurd (hT₀E ▸ hf) (Finset.notMem_empty _), fun Q hQ => ?_⟩, hT₀V, ?_⟩
      · rcases hQ with ⟨hQne, -, u, hWQ⟩
        cases Q with
        | nil => exact hQne rfl
        | cons x xs =>
          have hx : x.1 ∈ S.T₀.E := IsWalk_edges_mem hWQ List.mem_cons_self
          exact absurd (hT₀E ▸ hx) (Finset.notMem_empty _)
      · intro u hu w hw
        rw [Finset.mem_singleton] at hu hw
        subst hu; subst hw
        exact ⟨[], MGraph.IsWalk.nil _⟩
    exact isRootedTree_of_spanningTreeOn hST (Finset.mem_singleton_self r₀)
  have hRorig : S.R_orig = {r₀} := by
    have hsub : S.R_orig ⊆ {r₀} := by
      have h1 : S.R_orig ⊆ S.T₀.V := upClosure_subset (hldAuxTree_isRootedTree hT₀_rt) (by
        show S.R₀_init ⊆ S.T₀.V; rw [hR0, hT₀V])
      rwa [hT₀V] at h1
    have hmem : r₀ ∈ S.R_orig := subset_upClosure (by show r₀ ∈ S.R₀_init; rw [hR0]; simp)
    exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)
  have hR : S.R = {r₀} := by
    show S.R_orig ∪ ∅ = {r₀}
    rw [hRorig, Finset.union_empty]
  have hRFV : S.RF.F.V = {r₀} := hT₀V
  have hRFE : S.RF.F.E = ∅ := by
    show (forestGivenRoots S.T₀ r₀ S.R_orig (fun _ => 0)).E = ∅
    simp [forestGivenRoots, hT₀E]
  have hW : S.W_init = ∅ := by
    show refineDecomp ∅ _ = ∅
    simp [refineDecomp]
  have hwstr : ∀ e ∈ G₀.E, S.wstr e = 6 := by
    intro e he
    show (if e ∈ G₀.E then
        if (defaultThreshNat K_AN G₀.n kk : ℝ) ≤
          levelStretchBound S.T₀ r₀ (fun _ => 0) G₀ (safeLen G₀ ℓ) e
        then (1 : ℝ) else levelStretchBound S.T₀ r₀ (fun _ => 0) G₀ (safeLen G₀ ℓ) e
      else 1) = 6
    rw [ite_eq_left_iff.mpr (fun h => absurd he h), hraw e he,
      ite_eq_right_iff.mpr (fun h => by linarith)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hT₀V, hT₀E, rfl, hR0, hRorig, hR, hR, hRFV, hRFE, hW, hwstr⟩

end

end MinCostFlow.LSF.Program
