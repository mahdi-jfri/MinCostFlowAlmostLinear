module

public import MinCostFlow.LSF.Components
public import MinCostFlow.LSF.Model
public import MinCostFlow.LSF.SafePaths
public import MinCostFlow.LSF.Lemma54Init
public import MinCostFlow.LSF.Tools
public import MinCostFlow.Chain.CoreGraph
public import MinCostFlow.Chain.WalkFlow
public import MinCostFlow.Chain.SparseCoreTool
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete `LastLevelTool` for Level `d` (Definition 5.8 / Lemma 5.5)

This file builds `lastLevelTool : LastLevelTool` from `LSF`'s static LSST oracle (`HasLSSTSpec`)
together with deterministic multiplicative weights on a simple minimum-length representative
subgraph `simpleMinLenSubgraph G_d ℓ_d` (so that parallel multigraph edges never blow up `σ_last`
or `σ_mwu` beyond functions of `G_d.n`, and `cost G_d = Õ((G_d.m + 1)^2)`).

Specifically, for every valid graph `G_d` and positive edge lengths `ℓ_d`, `lastLevelTool_isSpec`
establishes `LastLevelTool.IsSpec (lastLevelParams C_lsst)` with:
* `σ_last n = max 1 (2 * max 1 C_lsst * n^2 * log²(n + 2))`,
* `σ_mwu n = max 1 (24 * max 1 C_lsst * log³(n + 2))`,
* `LastLevelSpans`: every returned `F_j` spans each connected component of `G_d`,
* `cost G_d ≤ 8 * (G_d.m + 1)^2 * (Real.log (G_d.m + G_d.n + 2)) ^ 0`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

/-! ## Simple minimum-length representative subgraph for multigraphs -/

/-- Canonical unordered endpoint key `{min (tail e) (head e), max (tail e) (head e)}`. -/
def edgePairKey (G : MGraph) (e : ℕ) : ℕ × ℕ :=
  (min (G.tail e) (G.head e), max (G.tail e) (G.head e))

/-- All non-loop edges of `G`. -/
def nonLoopEdges (G : MGraph) : Finset ℕ :=
  G.E.filter (fun e => G.tail e ≠ G.head e)

/-- Pick one edge in `G` with endpoint key `p` and minimum length `ℓ` (or `0` if none exists). -/
noncomputable def minLenRepEdge (G : MGraph) (ℓ : ℕ → ℝ) (p : ℕ × ℕ) : ℕ :=
  open Classical in
  let S := (nonLoopEdges G).filter (fun e => edgePairKey G e = p)
  if h : S.Nonempty then Classical.choose (Finset.exists_min_image S ℓ h) else 0

lemma minLenRepEdge_spec {G : MGraph} {ℓ : ℕ → ℝ} {e : ℕ} (he : e ∈ nonLoopEdges G) :
    let e' := minLenRepEdge G ℓ (edgePairKey G e)
    e' ∈ nonLoopEdges G ∧ edgePairKey G e' = edgePairKey G e ∧ ℓ e' ≤ ℓ e := by
  classical
  let p := edgePairKey G e
  let S := (nonLoopEdges G).filter (fun f => edgePairKey G f = p)
  have heS : e ∈ S := Finset.mem_filter.mpr ⟨he, rfl⟩
  have hS : S.Nonempty := ⟨e, heS⟩
  have hdef : minLenRepEdge G ℓ p = Classical.choose (Finset.exists_min_image S ℓ hS) := by
    dsimp only [minLenRepEdge]
    split_ifs with h'
    · rfl
    · exact absurd hS h'
  have hsp := Classical.choose_spec (Finset.exists_min_image S ℓ hS)
  rw [← hdef] at hsp
  have hmem := Finset.mem_filter.mp hsp.1
  exact ⟨hmem.1, hmem.2, hsp.2 e heS⟩

/-- Simple loopless subgraph `G_simp` containing one minimum-length edge per non-loop unordered
pair and only non-isolated vertices. -/
noncomputable def simpleMinLenSubgraph (G : MGraph) (ℓ : ℕ → ℝ) : MGraph :=
  open Classical in
  let keys := (nonLoopEdges G).image (edgePairKey G)
  let E_s := keys.image (minLenRepEdge G ℓ)
  { V := E_s.biUnion (fun e => {G.tail e, G.head e})
    E := E_s
    tail := G.tail
    head := G.head }

lemma simpleMinLenSubgraph_props {G : MGraph} (hG : G.IsValid) (ℓ : ℕ → ℝ) :
    let Gs := simpleMinLenSubgraph G ℓ
    Gs.IsValid ∧
    G.IsSubgraph Gs ∧
    Gs.n ≤ G.n ∧
    Gs.m ≤ G.m ∧
    Gs.m ≤ Gs.n ^ 2 ∧
    (∀ e ∈ Gs.E, Gs.tail e ≠ Gs.head e) ∧
    (∀ e ∈ nonLoopEdges G, ∃ e' ∈ Gs.E, edgePairKey G e' = edgePairKey G e ∧ ℓ e' ≤ ℓ e) ∧
    ((nonLoopEdges G).Nonempty → Gs.V.Nonempty ∧ 1 ≤ Gs.m ∧ 2 ≤ Gs.n) := by
  classical
  intro Gs
  have hE_sub_nl : Gs.E ⊆ nonLoopEdges G := by
    intro e' he'
    unfold Gs simpleMinLenSubgraph at he'
    rcases Finset.mem_image.mp he' with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hp with ⟨e, he, rfl⟩
    exact (minLenRepEdge_spec he).1
  have hE_sub_G : Gs.E ⊆ G.E := fun e he => (Finset.mem_filter.mp (hE_sub_nl he)).1
  have hV_sub_G : Gs.V ⊆ G.V := by
    intro v hv
    unfold Gs simpleMinLenSubgraph at hv
    rcases Finset.mem_biUnion.mp hv with ⟨e, he, hmem⟩
    have heG := hE_sub_G he
    rcases Finset.mem_insert.mp hmem with rfl | hmem'
    · exact (hG e heG).1
    · rw [Finset.mem_singleton] at hmem'
      rw [hmem']
      exact (hG e heG).2
  have hGs_val : Gs.IsValid := by
    intro e he
    unfold Gs simpleMinLenSubgraph
    exact ⟨Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_insert_self _ _⟩,
      Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩⟩
  have hSub : G.IsSubgraph Gs := ⟨hV_sub_G, hE_sub_G, fun _ _ => ⟨rfl, rfl⟩⟩
  have hn_le : Gs.n ≤ G.n := Finset.card_le_card hV_sub_G
  have hm_le : Gs.m ≤ G.m := Finset.card_le_card hE_sub_G
  have hm_sq : Gs.m ≤ Gs.n ^ 2 := by
    have hinj : ∀ e₁ ∈ Gs.E, ∀ e₂ ∈ Gs.E, edgePairKey G e₁ = edgePairKey G e₂ → e₁ = e₂ := by
      intro e₁ he₁ e₂ he₂ hEq
      unfold Gs simpleMinLenSubgraph at he₁ he₂
      rcases Finset.mem_image.mp he₁ with ⟨p₁, hp₁, rfl⟩
      rcases Finset.mem_image.mp he₂ with ⟨p₂, hp₂, rfl⟩
      rcases Finset.mem_image.mp hp₁ with ⟨a₁, ha₁, rfl⟩
      rcases Finset.mem_image.mp hp₂ with ⟨a₂, ha₂, rfl⟩
      have hs₁ := (@minLenRepEdge_spec G ℓ a₁ ha₁).2.1
      have hs₂ := (@minLenRepEdge_spec G ℓ a₂ ha₂).2.1
      have hpeq : edgePairKey G a₁ = edgePairKey G a₂ := by rw [← hs₁, ← hs₂, hEq]
      rw [hpeq]
    have himg_card : Gs.E.card = (Gs.E.image (edgePairKey G)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    have hkey_sub : Gs.E.image (edgePairKey G) ⊆ Gs.V ×ˢ Gs.V := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨e, he, rfl⟩
      have heV := hGs_val e he
      unfold edgePairKey
      rw [Finset.mem_product]
      change G.tail e ∈ Gs.V ∧ G.head e ∈ Gs.V at heV
      rcases le_total (G.tail e) (G.head e) with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]; exact ⟨heV.1, heV.2⟩
      · rw [min_eq_right hle, max_eq_left hle]; exact ⟨heV.2, heV.1⟩
    have hprod_card : (Gs.V ×ˢ Gs.V).card = Gs.n ^ 2 := by
      rw [Finset.card_product, sq]
      rfl
    unfold MGraph.m
    rw [himg_card, ← hprod_card]
    exact Finset.card_le_card hkey_sub
  have hnl_Gs : ∀ e ∈ Gs.E, Gs.tail e ≠ Gs.head e := fun e he =>
    (Finset.mem_filter.mp (hE_sub_nl he)).2
  have hrep : ∀ e ∈ nonLoopEdges G, ∃ e' ∈ Gs.E, edgePairKey G e' = edgePairKey G e ∧ ℓ e' ≤ ℓ e := by
    intro e he
    have hs := @minLenRepEdge_spec G ℓ e he
    refine ⟨minLenRepEdge G ℓ (edgePairKey G e), ?_, hs.2.1, hs.2.2⟩
    unfold Gs simpleMinLenSubgraph
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ he)
  refine ⟨hGs_val, hSub, hn_le, hm_le, hm_sq, hnl_Gs, hrep, fun ⟨e₀, he₀⟩ => ?_⟩
  obtain ⟨e', he', _, _⟩ := hrep e₀ he₀
  have h2V : {Gs.tail e', Gs.head e'} ⊆ Gs.V := fun x hx => by
    have heV := hGs_val e' he'
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact heV.1
    · rw [Finset.mem_singleton.mp hx']; exact heV.2
  have hne : Gs.tail e' ≠ Gs.head e' := hnl_Gs e' he'
  have h2 : 2 ≤ Gs.V.card := by
    calc 2 = ({Gs.tail e', Gs.head e'} : Finset ℕ).card := (Finset.card_pair hne).symm
      _ ≤ Gs.V.card := Finset.card_le_card h2V
  exact ⟨⟨Gs.tail e', (hGs_val e' he').1⟩, Finset.card_pos.mpr ⟨e', he'⟩, h2⟩

/-! ## Static multiplicative-weights loop on `G_simp` -/

private lemma one_add_ge_exp_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (x / 2) ≤ 1 + x := by
  have hpos : 0 < 1 - x / 2 := by linarith
  have hexp_neg : 1 - x / 2 ≤ Real.exp (-(x / 2)) := by
    linarith [Real.add_one_le_exp (-(x / 2))]
  have hexp_inv : Real.exp (x / 2) ≤ (1 - x / 2)⁻¹ := by
    rw [← inv_inv (Real.exp (x / 2)), ← Real.exp_neg]
    exact inv_anti₀ hpos hexp_neg
  have hprod : 1 ≤ (1 - x / 2) * (1 + x) := by nlinarith
  have hinv_le : (1 - x / 2)⁻¹ ≤ 1 + x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    simpa [mul_comm] using hprod
  exact hexp_inv.trans hinv_le

/-- Positive total-edge length wrapper using `safeLen`. -/
noncomputable def lastW (C_lsst : ℝ) (Gs : MGraph) : ℝ :=
  max 1 C_lsst * (Real.log ((Gs.n : ℝ) + 2)) ^ 2

lemma lastW_pos (C_lsst : ℝ) (Gs : MGraph) : 0 < lastW C_lsst Gs := by
  unfold lastW
  have hL : (1 / 2 : ℝ) < Real.log ((Gs.n : ℝ) + 2) := half_lt_log_add_two Gs.n
  have hC : (0 : ℝ) < max 1 C_lsst := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos hC (sq_pos_of_pos (by linarith))

/-- MWU step scale `ρ = 2 * lastW * G_simp.m`. -/
noncomputable def lastRho (C_lsst : ℝ) (Gs : MGraph) : ℝ :=
  2 * lastW C_lsst Gs * (Gs.m : ℝ)

lemma lastRho_pos {C_lsst : ℝ} {Gs : MGraph} (hm : 1 ≤ Gs.m) : 0 < lastRho C_lsst Gs := by
  unfold lastRho
  have hm_pos : (0 : ℝ) < Gs.m := by exact_mod_cast hm
  exact mul_pos (mul_pos zero_lt_two (lastW_pos C_lsst Gs)) hm_pos

/-- Number of MWU rounds on `G_simp`: `lastK = ⌊2 * Gs.m * log 2⌋ ≥ 1`. -/
noncomputable def lastMWUK (Gs : MGraph) : ℕ :=
  Nat.floor (2 * (Gs.m : ℝ) * Real.log 2)

lemma lastMWUK_bounds {Gs : MGraph} (hm : 1 ≤ Gs.m) :
    1 ≤ lastMWUK Gs ∧
    (Gs.m : ℝ) / 2 ≤ (lastMWUK Gs : ℝ) ∧
    (lastMWUK Gs : ℝ) ≤ 2 * (Gs.m : ℝ) * Real.log 2 ∧
    lastMWUK Gs ≤ 2 * Gs.m := by
  have hlog2_half : (1 / 2 : ℝ) < Real.log 2 := by
    have := half_lt_log_add_two 0
    simpa using this
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hm_r : (1 : ℝ) ≤ (Gs.m : ℝ) := by exact_mod_cast hm
  have hval_ge1 : (1 : ℝ) ≤ 2 * (Gs.m : ℝ) * Real.log 2 := by nlinarith
  have hfl_le : ((Nat.floor (2 * (Gs.m : ℝ) * Real.log 2) : ℕ) : ℝ) ≤
      2 * (Gs.m : ℝ) * Real.log 2 :=
    Nat.floor_le (by positivity)
  have hk1 : 1 ≤ lastMWUK Gs := Nat.le_floor (by simpa using hval_ge1)
  have hkm : (Gs.m : ℝ) / 2 ≤ (lastMWUK Gs : ℝ) := by
    have hm_lt : (Gs.m : ℝ) < (lastMWUK Gs : ℝ) + 1 := by
      have h1 : (Gs.m : ℝ) < 2 * (Gs.m : ℝ) * Real.log 2 := by nlinarith
      have h2 : 2 * (Gs.m : ℝ) * Real.log 2 < (lastMWUK Gs : ℝ) + 1 := Nat.lt_floor_add_one _
      exact h1.trans h2
    have hm_lt_nat : Gs.m < lastMWUK Gs + 1 := by exact_mod_cast hm_lt
    have hm_le_K : (Gs.m : ℝ) ≤ (lastMWUK Gs : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp hm_lt_nat
    linarith
  have hk_nat : lastMWUK Gs ≤ 2 * Gs.m := by
    have hmul : 2 * (Gs.m : ℝ) * Real.log 2 ≤ 2 * (Gs.m : ℝ) :=
      (mul_le_mul_of_nonneg_left hlog2_le_one (by positivity : 0 ≤ 2 * (Gs.m : ℝ))).trans_eq (mul_one _)
    have hle_real : (lastMWUK Gs : ℝ) ≤ ((2 * Gs.m : ℕ) : ℝ) := by
      push_cast
      exact hfl_le.trans hmul
    exact_mod_cast hle_real
  exact ⟨hk1, hkm, hfl_le, hk_nat⟩

/-- Sequentially updated weights `v_j` on `Gs` using `(1 + treeStretch / ρ)` updates on
`safeLen Gs ℓ`. -/
noncomputable def lastMWUWeights
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (Gs : MGraph) (ℓ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, e =>
    let vj := lastMWUWeights oracle C_lsst Gs ℓ j
    let ℓs := safeLen Gs ℓ
    let Tj := oracle Gs ℓs vj
    vj e * (1 + treeStretch Gs Tj ℓs e / lastRho C_lsst Gs)

lemma lastMWU_invariants (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {Gs : MGraph} {ℓ : ℕ → ℝ} (hGs : Gs.IsValid) (hV : Gs.V.Nonempty) (hm : 1 ≤ Gs.m)
    (hℓ : ∀ e ∈ Gs.E, 0 < ℓ e) :
    let W := lastW C_lsst Gs
    let ρ := lastRho C_lsst Gs
    let K := lastMWUK Gs
    ∀ j ≤ K,
      (∀ e ∈ Gs.E, 1 ≤ lastMWUWeights oracle C_lsst Gs ℓ j e) ∧
      (∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e ≤
        (Gs.m : ℝ) * Real.exp ((j : ℝ) * W / ρ)) ∧
      (∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e ≤ 2 * (Gs.m : ℝ)) ∧
      (j < K →
        let Tj := oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j)
        IsLSST Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j)
          (C_lsst * (Real.log ((Gs.n : ℝ) + 2)) ^ 2) Tj ∧
        ∀ e ∈ Gs.E, 1 ≤ treeStretch Gs Tj (safeLen Gs ℓ) e ∧
          treeStretch Gs Tj (safeLen Gs ℓ) e ≤ ρ) := by
  intro W ρ K
  have hW_pos : 0 < W := lastW_pos C_lsst Gs
  have hρ_pos : 0 < ρ := lastRho_pos hm
  have hsafe_pos : ∀ e ∈ Gs.E, 0 < safeLen Gs ℓ e := fun e he => by
    rw [safeLen_eq_of_mem ℓ he]; exact hℓ e he
  have hK := lastMWUK_bounds hm
  have hexp_le_two : ∀ j ≤ K, Real.exp ((j : ℝ) * W / ρ) ≤ 2 := by
    intro j hj
    have hjr : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
    have hlog2_pos : 0 < Real.log 2 := by
      have := half_lt_log_add_two 0
      linarith
    have hm_pos : (0 : ℝ) < Gs.m := by exact_mod_cast hm
    have hbound : (j : ℝ) * W / ρ ≤ Real.log 2 := by
      calc (j : ℝ) * W / ρ
          ≤ (K : ℝ) * W / ρ := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hjr hW_pos.le) hρ_pos.le
        _ ≤ (2 * (Gs.m : ℝ) * Real.log 2) * W / ρ := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hK.2.2.1 hW_pos.le) hρ_pos.le
        _ = Real.log 2 := by
            dsimp only [ρ, lastRho, W]
            field_simp [ne_of_gt (lastW_pos C_lsst Gs), ne_of_gt hm_pos]
    calc Real.exp ((j : ℝ) * W / ρ)
        ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hbound
      _ = 2 := Real.exp_log (by norm_num)
  have hMain : ∀ j ≤ K,
      (∀ e ∈ Gs.E, 1 ≤ lastMWUWeights oracle C_lsst Gs ℓ j e) ∧
      (∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e ≤
        (Gs.m : ℝ) * Real.exp ((j : ℝ) * W / ρ)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun _ _ => le_rfl, ?_⟩
      simp [lastMWUWeights, MGraph.m]
    | succ j ih =>
      intro hjK
      have hj_le : j ≤ K := Nat.le_of_succ_le hjK
      obtain ⟨ih_one, ih_sum⟩ := ih hj_le
      have hvj_pos : ∀ e ∈ Gs.E, 0 < lastMWUWeights oracle C_lsst Gs ℓ j e := fun e he =>
        lt_of_lt_of_le zero_lt_one (ih_one e he)
      have hlsst := hLSST Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j) hGs hV
        hsafe_pos hvj_pos
      have hnorm : Gs.norm1 (lastMWUWeights oracle C_lsst Gs ℓ j) =
          ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e :=
        Finset.sum_congr rfl fun e he => abs_of_pos (hvj_pos e he)
      have hW_ge : C_lsst * (Real.log ((Gs.n : ℝ) + 2)) ^ 2 ≤ W := by
        unfold W lastW
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      have hnorm_nn : 0 ≤ Gs.norm1 (lastMWUWeights oracle C_lsst Gs ℓ j) := by
        rw [hnorm]
        exact Finset.sum_nonneg fun e he => (hvj_pos e he).le
      have hsum_st : ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e *
            treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
              (safeLen Gs ℓ) e ≤
          W * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e := by
        rw [← hnorm]
        exact hlsst.2.2.2.trans (mul_le_mul_of_nonneg_right hW_ge hnorm_nn)
      have hst_nn : ∀ e ∈ Gs.E,
          0 ≤ treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
            (safeLen Gs ℓ) e := fun e he => by
        unfold treeStretch
        have he_pos : 0 < safeLen Gs ℓ e := hsafe_pos e he
        have hw_nn : 0 ≤ walkLength (safeLen Gs ℓ)
            ((oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j)).forestPath
              (Gs.tail e) (Gs.head e)) := by
          unfold walkLength
          exact Finset.sum_nonneg fun f _ => mul_nonneg (safeLen_nonneg hℓ f) (abs_nonneg _)
        exact add_nonneg zero_le_one (div_nonneg hw_nn he_pos.le)
      refine ⟨fun e he => ?_, ?_⟩
      · unfold lastMWUWeights
        dsimp only
        have h1 : 1 ≤ 1 + treeStretch Gs
            (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
              (safeLen Gs ℓ) e / ρ :=
          le_add_of_nonneg_right (div_nonneg (hst_nn e he) hρ_pos.le)
        exact one_le_mul_of_one_le_of_one_le (ih_one e he) h1
      · have hPhi_succ : ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ (j + 1) e =
            (∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e) +
              (1 / ρ) * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e *
                treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
                  (safeLen Gs ℓ) e := by
          calc ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ (j + 1) e
              = ∑ e ∈ Gs.E, (lastMWUWeights oracle C_lsst Gs ℓ j e +
                  (1 / ρ) * (lastMWUWeights oracle C_lsst Gs ℓ j e *
                    treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
                      (safeLen Gs ℓ) e)) := by
                  refine Finset.sum_congr rfl fun e _ => ?_
                  change lastMWUWeights oracle C_lsst Gs ℓ j e *
                      (1 + treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
                        (safeLen Gs ℓ) e / ρ) = _
                  ring
            _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
        have hstep1 : ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ (j + 1) e ≤
            (1 + W / ρ) * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e := by
          rw [hPhi_succ]
          have hmul := mul_le_mul_of_nonneg_left hsum_st (div_nonneg zero_le_one hρ_pos.le)
          linarith [show (1 + W / ρ) * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e =
            (∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e) +
              (1 / ρ) * (W * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e) by ring]
        have hexp1 : 1 + W / ρ ≤ Real.exp (W / ρ) := by
          linarith [Real.add_one_le_exp (W / ρ)]
        have hsum_nn : 0 ≤ ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e :=
          Finset.sum_nonneg fun e he => (hvj_pos e he).le
        calc ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ (j + 1) e
            ≤ (1 + W / ρ) * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e := hstep1
          _ ≤ Real.exp (W / ρ) * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e :=
              mul_le_mul_of_nonneg_right hexp1 hsum_nn
          _ ≤ Real.exp (W / ρ) * ((Gs.m : ℝ) * Real.exp ((j : ℝ) * W / ρ)) :=
              mul_le_mul_of_nonneg_left ih_sum (Real.exp_pos _).le
          _ = (Gs.m : ℝ) * Real.exp (((j + 1 : ℕ) : ℝ) * W / ρ) := by
              push_cast
              rw [mul_left_comm, ← Real.exp_add]
              congr 2
              ring
  intro j hjK
  obtain ⟨hone, hsum⟩ := hMain j hjK
  have hPhi_2m : ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e ≤ 2 * (Gs.m : ℝ) :=
    hsum.trans ((mul_le_mul_of_nonneg_left (hexp_le_two j hjK) (Nat.cast_nonneg _)).trans_eq
      (by ring))
  refine ⟨hone, hsum, hPhi_2m, fun _ => ?_⟩
  have hv_pos : ∀ e ∈ Gs.E, 0 < lastMWUWeights oracle C_lsst Gs ℓ j e := fun e he =>
    lt_of_lt_of_le zero_lt_one (hone e he)
  have hlsst := hLSST Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j) hGs hV
    hsafe_pos hv_pos
  have hnorm : Gs.norm1 (lastMWUWeights oracle C_lsst Gs ℓ j) =
      ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e :=
    Finset.sum_congr rfl fun e he => abs_of_pos (hv_pos e he)
  have hW_ge : C_lsst * (Real.log ((Gs.n : ℝ) + 2)) ^ 2 ≤ W := by
    unfold W lastW
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have hnorm_nn : 0 ≤ Gs.norm1 (lastMWUWeights oracle C_lsst Gs ℓ j) := by
    rw [hnorm]; exact Finset.sum_nonneg fun e he => (hv_pos e he).le
  have hsum_st : ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e *
        treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
          (safeLen Gs ℓ) e ≤
      2 * W * (Gs.m : ℝ) := by
    calc ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e *
          treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
            (safeLen Gs ℓ) e
        ≤ W * Gs.norm1 (lastMWUWeights oracle C_lsst Gs ℓ j) :=
          hlsst.2.2.2.trans (mul_le_mul_of_nonneg_right hW_ge hnorm_nn)
      _ = W * ∑ e ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ j e := by rw [hnorm]
      _ ≤ W * (2 * (Gs.m : ℝ)) := mul_le_mul_of_nonneg_left hPhi_2m hW_pos.le
      _ = 2 * W * (Gs.m : ℝ) := by ring
  refine ⟨hlsst, fun e he => ?_⟩
  have hst_ge1 : 1 ≤ treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
      (safeLen Gs ℓ) e := by
    unfold treeStretch
    have he_pos : 0 < safeLen Gs ℓ e := hsafe_pos e he
    have hw_nn : 0 ≤ walkLength (safeLen Gs ℓ)
        ((oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j)).forestPath
          (Gs.tail e) (Gs.head e)) := by
      unfold walkLength
      exact Finset.sum_nonneg fun f _ => mul_nonneg (safeLen_nonneg hℓ f) (abs_nonneg _)
    exact le_add_of_nonneg_right (div_nonneg hw_nn he_pos.le)
  have hst_nonneg : ∀ f ∈ Gs.E, 0 ≤ lastMWUWeights oracle C_lsst Gs ℓ j f *
      treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
        (safeLen Gs ℓ) f := by
    intro f hf
    unfold treeStretch
    have hf_pos : 0 < safeLen Gs ℓ f := hsafe_pos f hf
    have hw_nn : 0 ≤ walkLength (safeLen Gs ℓ)
        ((oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j)).forestPath
          (Gs.tail f) (Gs.head f)) := by
      unfold walkLength
      exact Finset.sum_nonneg fun g _ => mul_nonneg (safeLen_nonneg hℓ g) (abs_nonneg _)
    exact mul_nonneg (hv_pos f hf).le (add_nonneg zero_le_one (div_nonneg hw_nn hf_pos.le))
  have hsingle := Finset.single_le_sum hst_nonneg he
  have hmul1 : treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
      (safeLen Gs ℓ) e ≤
      lastMWUWeights oracle C_lsst Gs ℓ j e *
        treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
          (safeLen Gs ℓ) e :=
    le_mul_of_one_le_left (by linarith) (hone e he)
  exact ⟨hst_ge1, hmul1.trans (hsingle.trans hsum_st)⟩

lemma lastMWU_avg_bound (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {Gs : MGraph} {ℓ : ℕ → ℝ} (hGs : Gs.IsValid) (hV : Gs.V.Nonempty) (hm : 1 ≤ Gs.m)
    (hℓ : ∀ e ∈ Gs.E, 0 < ℓ e) :
    let K := lastMWUK Gs
    ∀ e ∈ Gs.E,
      (∑ j ∈ Finset.range K,
        treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
          (safeLen Gs ℓ) e) / (K : ℝ) ≤
        8 * lastW C_lsst Gs * Real.log (2 * (Gs.m : ℝ)) := by
  intro K e he
  have hInv := lastMWU_invariants oracle C_lsst hLSST hGs hV hm hℓ
  have hK := lastMWUK_bounds hm
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK.1
  have hρ_pos : 0 < lastRho C_lsst Gs := lastRho_pos hm
  have hW_pos : 0 < lastW C_lsst Gs := lastW_pos C_lsst Gs
  have hm_pos : (0 : ℝ) < (Gs.m : ℝ) := by exact_mod_cast hm
  have hExp_prod : ∀ m ≤ K,
      Real.exp ((∑ j ∈ Finset.range m,
        treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
          (safeLen Gs ℓ) e) / (2 * lastRho C_lsst Gs)) ≤
        lastMWUWeights oracle C_lsst Gs ℓ m e := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [lastMWUWeights]
    | succ m ih =>
      intro hmK
      have hm_lt : m < K := hmK
      have ih' := ih (Nat.le_of_lt hm_lt)
      have hbd := (hInv m (Nat.le_of_lt hm_lt)).2.2.2 hm_lt |>.2 e he
      have hx0 : 0 ≤ treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ m))
          (safeLen Gs ℓ) e / lastRho C_lsst Gs := by
        have hst1 := (hInv m (Nat.le_of_lt hm_lt)).2.2.2 hm_lt |>.2 e he |>.1
        exact div_nonneg (by linarith) hρ_pos.le
      have hx1 : treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ m))
          (safeLen Gs ℓ) e / lastRho C_lsst Gs ≤ 1 :=
        (div_le_one hρ_pos).mpr hbd.2
      have hexp := one_add_ge_exp_half hx0 hx1
      have hv_nn : 0 ≤ lastMWUWeights oracle C_lsst Gs ℓ m e :=
        le_trans zero_le_one ((hInv m (Nat.le_of_lt hm_lt)).1 e he)
      rw [Finset.sum_range_succ, add_div, Real.exp_add]
      have hdiv2 : (treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ m))
          (safeLen Gs ℓ) e / lastRho C_lsst Gs) / 2 =
          treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ m))
            (safeLen Gs ℓ) e / (2 * lastRho C_lsst Gs) := by ring
      rw [← hdiv2]
      calc Real.exp ((∑ j ∈ Finset.range m, _) / (2 * lastRho C_lsst Gs)) * Real.exp (_ / 2)
          ≤ lastMWUWeights oracle C_lsst Gs ℓ m e * (1 + _ / lastRho C_lsst Gs) :=
            mul_le_mul ih' hexp (Real.exp_pos _).le hv_nn
        _ = lastMWUWeights oracle C_lsst Gs ℓ (m + 1) e := rfl
  have hsingle_K : lastMWUWeights oracle C_lsst Gs ℓ K e ≤
      ∑ f ∈ Gs.E, lastMWUWeights oracle C_lsst Gs ℓ K f :=
    Finset.single_le_sum (fun f hf => le_trans zero_le_one ((hInv K (le_refl K)).1 f hf)) he
  have hPhi_K := (hInv K (le_refl K)).2.2.1
  have hlog : (∑ j ∈ Finset.range K,
      treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
        (safeLen Gs ℓ) e) / (2 * lastRho C_lsst Gs) ≤ Real.log (2 * (Gs.m : ℝ)) := by
    rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
    exact (hExp_prod K (le_refl K)).trans (hsingle_K.trans hPhi_K)
  have hsum_le : ∑ j ∈ Finset.range K,
      treeStretch Gs (oracle Gs (safeLen Gs ℓ) (lastMWUWeights oracle C_lsst Gs ℓ j))
        (safeLen Gs ℓ) e ≤
      2 * lastRho C_lsst Gs * Real.log (2 * (Gs.m : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 2 * lastRho C_lsst Gs)
    rwa [mul_div_cancel₀ _ (by positivity)] at hmul
  calc (∑ j ∈ Finset.range K, _) / (K : ℝ)
      ≤ (2 * lastRho C_lsst Gs * Real.log (2 * (Gs.m : ℝ))) / (K : ℝ) :=
        div_le_div_of_nonneg_right hsum_le hK_pos.le
    _ ≤ (2 * lastRho C_lsst Gs * Real.log (2 * (Gs.m : ℝ))) / ((Gs.m : ℝ) / 2) := by
        refine div_le_div_of_nonneg_left ?_ (by positivity) hK.2.1
        have hm_r : (1 : ℝ) ≤ (Gs.m : ℝ) := by exact_mod_cast hm
        have h1_le_2m : (1 : ℝ) ≤ 2 * (Gs.m : ℝ) := by linarith
        exact mul_nonneg (by positivity) (Real.log_nonneg h1_le_2m)
    _ = 8 * lastW C_lsst Gs * Real.log (2 * (Gs.m : ℝ)) := by
        dsimp only [lastRho]
        field_simp [ne_of_gt hm_pos]
        ring

/-! ## Concrete `LastLevelParams`, `lastLevelTool`, and `lastLevelTool_isSpec` -/

/-- Explicit `LastLevelParams` for `lastLevelTool` (Lemma 5.5 / Definition 5.8).
On general multigraphs (`LastLevelSpans`), `σ_last n = O(C_lsst * n² log² n)` and
`σ_mwu n = O(C_lsst * log³ n)` depend only on `n = G_d.n` (via `simpleMinLenSubgraph`). -/
noncomputable def lastLevelParams (C_lsst : ℝ) : LastLevelParams where
  σ_last := fun n => max 1 (2 * max 1 C_lsst * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2)
  σ_mwu := fun n => max 1 (24 * max 1 C_lsst * (Real.log ((n : ℝ) + 2)) ^ 3)
  c_last := 8
  p_last := 0

lemma lastLevelParams_valid (C_lsst : ℝ) : (lastLevelParams C_lsst).Valid := by
  have hC : 0 ≤ max 1 C_lsst := le_trans zero_le_one (le_max_left _ _)
  unfold lastLevelParams
  refine ⟨fun _ => le_max_left _ _, fun n₁ n₂ hn => ?_, fun _ => le_max_left _ _,
    fun n₁ n₂ hn => ?_, by norm_num⟩
  · have hlog1 : (0 : ℝ) ≤ Real.log ((n₁ : ℝ) + 2) :=
      (half_lt_log_add_two n₁).le.trans' (by norm_num)
    have hlog_le : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith [show (n₁ : ℝ) ≤ n₂ from by exact_mod_cast hn])
    have hn_le : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
    refine max_le_max_left 1 (mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le 2) (mul_nonneg zero_le_two hC))
      (pow_le_pow_left₀ hlog1 hlog_le 2) (sq_nonneg _) (by positivity))
  · have hlog1 : (0 : ℝ) ≤ Real.log ((n₁ : ℝ) + 2) :=
      (half_lt_log_add_two n₁).le.trans' (by norm_num)
    have hlog_le : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith [show (n₁ : ℝ) ≤ n₂ from by exact_mod_cast hn])
    exact max_le_max_left 1 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog1 hlog_le 3)
      (mul_nonneg (by norm_num) hC))

/-- Concrete `LastLevelTool` built from `oracle` (`HasLSSTSpec`) and deterministic MWU over
`simpleMinLenSubgraph G_d ℓ_d`. -/
noncomputable def lastLevelTool (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) :
    LastLevelTool where
  build := fun G_d ℓ_d =>
    open Classical in
    if _hnl : (nonLoopEdges G_d).Nonempty then
      let Gs := simpleMinLenSubgraph G_d ℓ_d
      let K := lastMWUK Gs
      let r₀ := pickRoot G_d
      let R := compReps G_d r₀
      let lsfs := fun j =>
        let Tj := oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j)
        let F : MGraph :=
          { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
        { T := F
          F := { F := F, R := R }
          wstr := fun e =>
            if e ∈ G_d.E then
              if G_d.tail e = G_d.head e then 1
              else treeStretch Gs Tj (safeLen Gs ℓ_d) (minLenRepEdge G_d ℓ_d (edgePairKey G_d e))
            else 1 }
      (K, lsfs)
    else
      let F0 : MGraph := { V := G_d.V, E := ∅, tail := G_d.tail, head := G_d.head }
      (1, fun _ => { T := F0, F := { F := F0, R := G_d.V }, wstr := fun _ => 1 })
  cost := fun G_d =>
    open Classical in
    if (nonLoopEdges G_d).Nonempty then
      lastMWUK (simpleMinLenSubgraph G_d (fun _ => 1)) * (G_d.m + 1) + 1
    else
      1

lemma simpleMinLenSubgraph_m_indep (G_d : MGraph) (ℓ₁ ℓ₂ : ℕ → ℝ) :
    (simpleMinLenSubgraph G_d ℓ₁).E.card = (simpleMinLenSubgraph G_d ℓ₂).E.card := by
  classical
  have hinj : ∀ ℓ,
      (((nonLoopEdges G_d).image (edgePairKey G_d)).image (minLenRepEdge G_d ℓ)).card =
        ((nonLoopEdges G_d).image (edgePairKey G_d)).card := by
    intro ℓ
    refine Finset.card_image_of_injOn fun p₁ hp₁ p₂ hp₂ hEq => ?_
    rcases Finset.mem_image.mp hp₁ with ⟨e₁, he₁, rfl⟩
    rcases Finset.mem_image.mp hp₂ with ⟨e₂, he₂, rfl⟩
    have hs₁ := (@minLenRepEdge_spec G_d ℓ e₁ he₁).2.1
    have hs₂ := (@minLenRepEdge_spec G_d ℓ e₂ he₂).2.1
    rw [← hs₁, ← hs₂, hEq]
  exact (hinj ℓ₁).trans (hinj ℓ₂).symm

lemma pair_eq_of_edgePairKey {G₁ G₂ : MGraph} {e₁ e₂ : ℕ}
    (h : edgePairKey G₁ e₁ = edgePairKey G₂ e₂) :
    (G₁.tail e₁ = G₂.tail e₂ ∧ G₁.head e₁ = G₂.head e₂) ∨
    (G₁.tail e₁ = G₂.head e₂ ∧ G₁.head e₁ = G₂.tail e₂) := by
  unfold edgePairKey at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  omega

private lemma isWalk_of_walkEdges_eq {H K : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : H.IsWalk u v P)
    (hE : ∀ f ∈ walkEdges P, f ∈ K.E ∧ K.tail f = H.tail f ∧ K.head f = H.head f) :
    K.IsWalk u v P ∧ K.walkVertices u P = H.walkVertices u P := by
  induction hW with
  | nil s => exact ⟨.nil s, rfl⟩
  | @cons u₀ v₀ x₀ P₀ hxE hsrc _ ih =>
    have hwe : x₀.1 ∈ walkEdges (x₀ :: P₀) := by
      rw [walkEdges_cons, Finset.mem_insert]; exact Or.inl rfl
    have hxK := hE x₀.1 hwe
    have hsub : ∀ f ∈ walkEdges P₀, f ∈ K.E ∧ K.tail f = H.tail f ∧ K.head f = H.head f :=
      fun f hf => hE f (by rw [walkEdges_cons, Finset.mem_insert]; exact Or.inr hf)
    obtain ⟨ihW, ihV⟩ := ih hsub
    have hsrc' : K.src x₀ = u₀ := by
      rw [← hsrc]
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.src, hxK.2.1, hxK.2.2]
    have hdst' : K.dst x₀ = H.dst x₀ := by
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hxK.2.1, hxK.2.2]
    refine ⟨.cons hxK.1 hsrc' (hdst'.symm ▸ ihW), ?_⟩
    rw [walkVertices_cons, walkVertices_cons, hdst']
    exact congrArg (u₀ :: ·) (by simpa [hdst'] using ihV)

private lemma compReps_unique {G : MGraph} {r₀ r₁ r₂ : ℕ}
    (hr₁ : r₁ ∈ compReps G r₀) (hr₂ : r₂ ∈ compReps G r₀) (hc : G.Connected r₁ r₂) :
    r₁ = r₂ := by
  classical
  let pick : Finset ℕ → ℕ := fun C =>
    if r₀ ∈ C then r₀ else if h : C.Nonempty then Classical.choose h else r₀
  have hmemC : ∀ C ∈ components G, pick C ∈ C := by
    intro C hC
    rw [components, Finset.mem_image] at hC
    obtain ⟨w, hw, rfl⟩ := hC
    dsimp only [pick]
    split_ifs with h1 h2
    · exact h1
    · exact Classical.choose_spec h2
    · exact absurd ⟨w, self_mem_compOf hw⟩ h2
  have hC_eq : ∀ C ∈ components G, compOf G (pick C) = C := by
    intro C hC
    have hp := hmemC C hC
    rw [components, Finset.mem_image] at hC
    obtain ⟨w, _, rfl⟩ := hC
    exact (compOf_eq_of_connected (mem_compOf_iff.mp hp).2).symm
  unfold compReps at hr₁ hr₂
  rcases Finset.mem_image.mp hr₁ with ⟨C₁, hC₁, rfl⟩
  rcases Finset.mem_image.mp hr₂ with ⟨C₂, hC₂, rfl⟩
  change pick C₁ = pick C₂
  have hcomp_eq : C₁ = C₂ := by
    rw [← hC_eq C₁ hC₁, ← hC_eq C₂ hC₂]
    exact compOf_eq_of_connected hc
  rw [hcomp_eq]

private lemma mem_edges_of_mem_walkEdges {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) {f : ℕ} (hf : f ∈ walkEdges P) : f ∈ G.E := by
  rw [walkEdges, List.mem_toFinset, List.mem_map] at hf
  obtain ⟨a, haP, rfl⟩ := hf
  exact IsWalk_edges_mem hW haP

/-- **Main specification theorem for `lastLevelTool`**: satisfies `LastLevelTool.IsSpec`
unconditionally for all valid graphs `G_d` and positive edge lengths `ℓ_d`. -/
theorem lastLevelTool_isSpec (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst) :
    (lastLevelTool oracle C_lsst).IsSpec (lastLevelParams C_lsst) := by
  classical
  intro G_d ℓ_d hG hℓ
  dsimp only [lastLevelTool]
  by_cases hnl : (nonLoopEdges G_d).Nonempty
  · simp only [hnl, ↓reduceDIte]
    have hGs_props := simpleMinLenSubgraph_props hG ℓ_d
    rcases hGs_props with ⟨hGs_val, hGs_sub, hGs_n, hGs_m, hGs_sq, hGs_nl, hGs_rep, hGs_ne⟩
    obtain ⟨hGs_Vne, hGs_m1, _⟩ := hGs_ne hnl
    have hℓs : ∀ e ∈ (simpleMinLenSubgraph G_d ℓ_d).E, 0 < ℓ_d e := fun e he =>
      hℓ e (hGs_sub.2.1 he)
    have hInv := lastMWU_invariants oracle C_lsst hLSST hGs_val hGs_Vne hGs_m1 hℓs
    have hK := lastMWUK_bounds hGs_m1
    have hAvg := lastMWU_avg_bound oracle C_lsst hLSST hGs_val hGs_Vne hGs_m1 hℓs
    let Gs := simpleMinLenSubgraph G_d ℓ_d
    let K := lastMWUK Gs
    let r₀ := pickRoot G_d
    let R := compReps G_d r₀
    have hR_sub : R ⊆ G_d.V := fun r hr => by
      have hGne : G_d.V.Nonempty := ⟨hGs_Vne.choose, hGs_sub.1 hGs_Vne.choose_spec⟩
      exact compReps_subset hG (pickRoot_mem hGne) hr
    have hbranch : ∀ j < K,
        let Tj := oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j)
        let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
        let RF : RootedForest := { F := F, R := R }
        F.IsForest ∧
        RF.IsRootedSpanningForestOf G_d ∧
        (∀ u v, G_d.Connected u v → F.Connected u v) ∧
        ∀ e ∈ Gs.E, F.forestPath (Gs.tail e) (Gs.head e) = Tj.forestPath (Gs.tail e) (Gs.head e) := by
      intro j hj
      obtain ⟨hIsLSST, _⟩ := (hInv j (Nat.le_of_lt hj)).2.2.2 hj
      set Tj := oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j)
      let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
      have hF_val : F.IsValid := fun e he => hG e (hGs_sub.2.1 (Finset.mem_inter.mp he).2)
      have hF_for : F.IsForest := by
        refine ⟨hF_val, fun P ⟨hne, hnd, u, hW⟩ => hIsLSST.1.1.2 P ⟨hne, hnd, u, ?_⟩⟩
        have hEdges : ∀ f ∈ walkEdges P, f ∈ Tj.E ∧ Tj.tail f = F.tail f ∧ Tj.head f = F.head f := by
          intro f hf
          have hfF := mem_edges_of_mem_walkEdges hW hf
          have hfTj : f ∈ Tj.E := (Finset.mem_inter.mp hfF).1
          have hEnds := hIsLSST.2.1 f hfTj (Finset.mem_inter.mp hfF).2
          exact ⟨hfTj, hEnds.1, hEnds.2⟩
        exact (isWalk_of_walkEdges_eq hW hEdges).1
      have hSub_GF : G_d.IsSubgraph F :=
        ⟨Finset.Subset.refl _, fun e he => hGs_sub.2.1 (Finset.mem_inter.mp he).2, fun _ _ => ⟨rfl, rfl⟩⟩
      have hpath_eq : ∀ e ∈ Gs.E,
          F.forestPath (Gs.tail e) (Gs.head e) = Tj.forestPath (Gs.tail e) (Gs.head e) := by
        intro e he
        have heV := hGs_val e he
        have hP := forestPath_isPath hIsLSST.1.1
          (hIsLSST.1.2.2 (Gs.tail e) (hIsLSST.1.2.1 ▸ heV.1) (Gs.head e) (hIsLSST.1.2.1 ▸ heV.2))
        have hEdges_mem : ∀ f ∈ walkEdges (Tj.forestPath (Gs.tail e) (Gs.head e)),
            f ∈ F.E ∧ F.tail f = Tj.tail f ∧ F.head f = Tj.head f := fun f hf => by
          have hfTj : f ∈ Tj.E := mem_edges_of_mem_walkEdges hP.1 hf
          have hfGs : f ∈ Gs.E := hIsLSST.2.2.1 e he f hf
          have hfF : f ∈ F.E := Finset.mem_inter.mpr ⟨hfTj, hfGs⟩
          have hEnds := hIsLSST.2.1 f hfTj hfGs
          exact ⟨hfF, hEnds.1.symm, hEnds.2.symm⟩
        obtain ⟨hW_F, hverts_F⟩ := isWalk_of_walkEdges_eq hP.1 hEdges_mem
        exact forestPath_eq_of_isPath hF_for ⟨hW_F, hverts_F ▸ hP.2⟩
      have hedge_conn : ∀ e ∈ G_d.E, F.Connected (G_d.tail e) (G_d.head e) := by
        intro e he
        by_cases hloop : G_d.tail e = G_d.head e
        · rw [hloop]; exact MGraph.connected_refl F _
        · obtain ⟨e', he', hkey, _⟩ := hGs_rep e (Finset.mem_filter.mpr ⟨he, hloop⟩)
          have hW : F.IsWalk (Gs.tail e') (Gs.head e') (Tj.forestPath (Gs.tail e') (Gs.head e')) := by
            have he'V := hGs_val e' he'
            have hP := forestPath_isPath hIsLSST.1.1
              (hIsLSST.1.2.2 (Gs.tail e') (hIsLSST.1.2.1 ▸ he'V.1)
                (Gs.head e') (hIsLSST.1.2.1 ▸ he'V.2))
            have hEdges_mem : ∀ f ∈ walkEdges (Tj.forestPath (Gs.tail e') (Gs.head e')),
                f ∈ F.E ∧ F.tail f = Tj.tail f ∧ F.head f = Tj.head f := fun f hf => by
              have hfTj := mem_edges_of_mem_walkEdges hP.1 hf
              have hfGs := hIsLSST.2.2.1 e' he' f hf
              have hfF := Finset.mem_inter.mpr ⟨hfTj, hfGs⟩
              have hEnds := hIsLSST.2.1 f hfTj hfGs
              exact ⟨hfF, hEnds.1.symm, hEnds.2.symm⟩
            exact (isWalk_of_walkEdges_eq hP.1 hEdges_mem).1
          have hc_e' : F.Connected (G_d.tail e') (G_d.head e') := hW |> fun hw => ⟨_, hw⟩
          have hpair := pair_eq_of_edgePairKey hkey
          rcases hpair with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · rw [← ht, ← hh]; exact hc_e'
          · rw [← ht, ← hh]; exact MGraph.connected_symm hc_e'
      have hSpan : ∀ u v, G_d.Connected u v → F.Connected u v := by
        intro u v ⟨P, hW⟩
        induction hW with
        | nil s => exact MGraph.connected_refl F s
        | @cons a b x xs hxE hsrc _ ih =>
          have hstep : F.Connected a (G_d.dst x) := by
            rcases x with ⟨e, _ | _⟩ <;> dsimp only [MGraph.src, MGraph.dst] at hsrc ⊢ <;>
              rw [← hsrc]
            · exact MGraph.connected_symm (hedge_conn e hxE)
            · exact hedge_conn e hxE
          exact MGraph.connected_trans hstep ih
      have hRF : ({ F := F, R := R } : RootedForest).IsRootedSpanningForestOf G_d := by
        refine ⟨hF_for, rfl, hR_sub, ?_, hSub_GF⟩
        intro v hv
        obtain ⟨r, hrR, hcG⟩ := compReps_connected hv
        refine ⟨r, ⟨hrR, hSpan v r hcG⟩, fun r' ⟨hr'R, hcF'⟩ => ?_⟩
        have hcG' : G_d.Connected r' r :=
          MGraph.connected_trans (MGraph.connected_symm (connected_of_subgraph hSub_GF hcF')) hcG
        exact compReps_unique hr'R hrR hcG'
      exact ⟨hF_for, hRF, hSpan, hpath_eq⟩
    have hGs_m_pos : (0 : ℝ) < (Gs.m : ℝ) := by exact_mod_cast hGs_m1
    have hL2_pos : 0 < Real.log ((G_d.n : ℝ) + 2) := by
      have := half_lt_log_add_two G_d.n; linarith
    have hGs_log_le : Real.log ((Gs.n : ℝ) + 2) ≤ Real.log ((G_d.n : ℝ) + 2) :=
      Real.log_le_log (by positivity)
        (by linarith [show (Gs.n : ℝ) ≤ G_d.n from by exact_mod_cast hGs_n])
    have hm_le_Gd_sq : (Gs.m : ℝ) ≤ (G_d.n : ℝ) ^ 2 := by
      exact_mod_cast hGs_sq.trans (Nat.pow_le_pow_left hGs_n 2)
    have hm_log_le : Real.log (2 * (Gs.m : ℝ)) ≤ 3 * Real.log ((G_d.n : ℝ) + 2) := by
      have hm_le_cube : (2 * (Gs.m : ℝ)) ≤ ((G_d.n : ℝ) + 2) ^ 3 := by
        have hn_nn : (0 : ℝ) ≤ G_d.n := Nat.cast_nonneg _
        nlinarith [sq_nonneg ((G_d.n : ℝ))]
      calc Real.log (2 * (Gs.m : ℝ))
          ≤ Real.log (((G_d.n : ℝ) + 2) ^ 3) := Real.log_le_log (by positivity) hm_le_cube
        _ = 3 * Real.log ((G_d.n : ℝ) + 2) := by rw [Real.log_pow]; ring
    have hW_le : lastW C_lsst Gs ≤ max 1 C_lsst * (Real.log ((G_d.n : ℝ) + 2)) ^ 2 := by
      unfold lastW
      have hlog1 : 0 ≤ Real.log ((Gs.n : ℝ) + 2) :=
        (half_lt_log_add_two Gs.n).le.trans' (by norm_num)
      have hsq : Real.log ((Gs.n : ℝ) + 2) ^ 2 ≤ Real.log ((G_d.n : ℝ) + 2) ^ 2 :=
        pow_le_pow_left₀ hlog1 hGs_log_le 2
      have hC0 : 0 ≤ max 1 C_lsst := le_trans zero_le_one (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left hsq hC0
    have hRho_le : lastRho C_lsst Gs ≤ (lastLevelParams C_lsst).σ_last G_d.n := by
      unfold lastRho lastLevelParams
      refine le_max_of_le_right ?_
      have h1 : 2 * lastW C_lsst Gs * (Gs.m : ℝ) ≤
          2 * (max 1 C_lsst * Real.log ((G_d.n : ℝ) + 2) ^ 2) * (G_d.n : ℝ) ^ 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hW_le zero_le_two) hm_le_Gd_sq
          (Nat.cast_nonneg _) (by positivity)
      linarith
    have hstretch_bound : ∀ j < K, ∀ e ∈ G_d.E,
        let Tj := oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j)
        let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
        let RF : RootedForest := { F := F, R := R }
        let wstr_e := if G_d.tail e = G_d.head e then (1 : ℝ)
          else treeStretch Gs Tj (safeLen Gs ℓ_d) (minLenRepEdge G_d ℓ_d (edgePairKey G_d e))
        1 ≤ wstr_e ∧
        RF.stretch G_d ℓ_d e ≤ wstr_e ∧
        wstr_e ≤ (lastLevelParams C_lsst).σ_last G_d.n := by
      intro j hj e he
      dsimp only
      obtain ⟨hF_for, hRF, hSpan, hpath_eq⟩ := hbranch j hj
      set Tj := oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j)
      let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
      let RF : RootedForest := { F := F, R := R }
      by_cases hloop : G_d.tail e = G_d.head e
      · simp only [hloop, ↓reduceIte]
        have hstr1 : RF.stretch G_d ℓ_d e = 1 := by
          unfold RootedForest.stretch
          dsimp only
          rw [hloop]
          simp only [↓reduceIte]
          change 1 + walkLength ℓ_d (F.forestPath (G_d.head e) (G_d.head e)) / ℓ_d e = 1
          rw [forestPath_self hF_for, walkLength_nil, zero_div, add_zero]
        rw [hstr1]
        exact ⟨le_rfl, le_rfl, le_max_left _ _⟩
      · simp only [hloop, ↓reduceIte]
        have he_nl : e ∈ nonLoopEdges G_d := Finset.mem_filter.mpr ⟨he, hloop⟩
        set e' := minLenRepEdge G_d ℓ_d (edgePairKey G_d e)
        have hspec := @minLenRepEdge_spec G_d ℓ_d e he_nl
        have he' : e' ∈ Gs.E := Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ he_nl)
        have hkey : edgePairKey G_d e' = edgePairKey G_d e := hspec.2.1
        have hlen_le : ℓ_d e' ≤ ℓ_d e := hspec.2.2
        have hcF : F.Connected (Gs.tail e') (Gs.head e') :=
          hSpan _ _ (connected_of_edge (hGs_sub.2.1 he'))
        have hIsLSST_j := (hInv j (Nat.le_of_lt hj)).2.2.2 hj
        set P := Tj.forestPath (Gs.tail e') (Gs.head e')
        have hlen_safe : walkLength ℓ_d P = walkLength (safeLen Gs ℓ_d) P := by
          unfold walkLength
          refine Finset.sum_congr rfl fun f hf => ?_
          rw [safeLen_eq_of_mem ℓ_d (hIsLSST_j.1.2.2.1 e' he' f hf)]
        have hpath_F_Tj : F.forestPath (Gs.tail e') (Gs.head e') = P := hpath_eq e' he'
        have hwalkLen_eq :
            walkLength ℓ_d (F.forestPath (G_d.tail e) (G_d.head e)) =
              walkLength (safeLen Gs ℓ_d) P := by
          have hpair := pair_eq_of_edgePairKey hkey
          rcases hpair with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · change Gs.tail e' = G_d.tail e at ht
            change Gs.head e' = G_d.head e at hh
            rw [← ht, ← hh, hpath_F_Tj, hlen_safe]
          · change Gs.tail e' = G_d.head e at ht
            change Gs.head e' = G_d.tail e at hh
            rw [← ht, ← hh, forestPath_rev hF_for hcF, walkLength_walkRev, hpath_F_Tj, hlen_safe]
        have hroot_eq : RF.root (G_d.tail e) = RF.root (G_d.head e) :=
          root_eq_of_connected hRF (hG e he).1 (hG e he).2 (hSpan _ _ (connected_of_edge he))
        have hstretch_le : RF.stretch G_d ℓ_d e ≤ treeStretch Gs Tj (safeLen Gs ℓ_d) e' := by
          unfold RootedForest.stretch treeStretch
          dsimp only
          simp only [hroot_eq, ↓reduceIte]
          rw [hwalkLen_eq, safeLen_eq_of_mem ℓ_d he']
          have hw_nn : 0 ≤ walkLength (safeLen Gs ℓ_d) P := by
            unfold walkLength
            exact Finset.sum_nonneg fun f _ => mul_nonneg (safeLen_nonneg hℓs f) (abs_nonneg _)
          have hℓe'_pos : 0 < ℓ_d e' := hℓs e' he'
          exact add_le_add_right (div_le_div_of_nonneg_left hw_nn hℓe'_pos hlen_le) 1
        have hbd := hIsLSST_j.2 e' he'
        exact ⟨hbd.1, hstretch_le, hbd.2.trans hRho_le⟩
    refine ⟨hK.1, ?_, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨hF_for, hRF, _, _⟩ := hbranch j hj
      refine ⟨hF_for, hRF, ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩, ?_⟩
      intro e he
      have hb := hstretch_bound j hj e he
      exact ⟨by simpa [he] using hb.2.1, by simpa [he] using hb.2.2⟩
    · intro e he
      by_cases hloop : G_d.tail e = G_d.head e
      · have hsum_one : (∑ j ∈ Finset.range K,
            (if e ∈ G_d.E then if G_d.tail e = G_d.head e then (1 : ℝ) else
              treeStretch Gs (oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j))
                (safeLen Gs ℓ_d) (minLenRepEdge G_d ℓ_d (edgePairKey G_d e))
            else 1)) = (K : ℝ) := by
          simp [he, hloop]
        have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK.1
        change (∑ j ∈ Finset.range K, _) / (K : ℝ) ≤ (lastLevelParams C_lsst).σ_mwu G_d.n
        rw [hsum_one, div_self hK_ne]
        exact le_max_left _ _
      · have he_nl : e ∈ nonLoopEdges G_d := Finset.mem_filter.mpr ⟨he, hloop⟩
        set e' := minLenRepEdge G_d ℓ_d (edgePairKey G_d e)
        have he' : e' ∈ Gs.E := Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ he_nl)
        have havg_e' := hAvg e' he'
        have hsum_eq : (∑ j ∈ Finset.range K,
            (if e ∈ G_d.E then if G_d.tail e = G_d.head e then (1 : ℝ) else
              treeStretch Gs (oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j))
                (safeLen Gs ℓ_d) (minLenRepEdge G_d ℓ_d (edgePairKey G_d e))
            else 1)) =
            ∑ j ∈ Finset.range K,
              treeStretch Gs (oracle Gs (safeLen Gs ℓ_d) (lastMWUWeights oracle C_lsst Gs ℓ_d j))
                (safeLen Gs ℓ_d) e' := by
          refine Finset.sum_congr rfl fun j _ => by simp [he, hloop, e']
        change (∑ j ∈ Finset.range K, _) / (K : ℝ) ≤ (lastLevelParams C_lsst).σ_mwu G_d.n
        rw [hsum_eq]
        refine le_trans havg_e' ?_
        unfold lastLevelParams
        refine le_max_of_le_right ?_
        have hmul1 : 8 * lastW C_lsst Gs * Real.log (2 * (Gs.m : ℝ)) ≤
            8 * (max 1 C_lsst * Real.log ((G_d.n : ℝ) + 2) ^ 2) * (3 * Real.log ((G_d.n : ℝ) + 2)) := by
          have hlog2m_nn : 0 ≤ Real.log (2 * (Gs.m : ℝ)) :=
            Real.log_nonneg (by linarith [show (1 : ℝ) ≤ (Gs.m : ℝ) from by exact_mod_cast hGs_m1])
          exact mul_le_mul (mul_le_mul_of_nonneg_left hW_le (by norm_num)) hm_log_le hlog2m_nn
            (by positivity)
        linarith
    · intro j hj u _ v _ hc
      exact (hbranch j hj).2.2.1 u v hc
    · have hGs1_props := simpleMinLenSubgraph_props hG (fun _ => 1)
      have hGs1_m1 : 1 ≤ (simpleMinLenSubgraph G_d (fun _ => 1)).m := (hGs1_props.2.2.2.2.2.2.2 hnl).2.1
      have hK1_le : lastMWUK (simpleMinLenSubgraph G_d (fun _ => 1)) ≤ 2 * G_d.m :=
        (lastMWUK_bounds hGs1_m1).2.2.2.trans (Nat.mul_le_mul_left 2 hGs1_props.2.2.2.1)
      have hcost_nat : lastMWUK (simpleMinLenSubgraph G_d (fun _ => 1)) * (G_d.m + 1) + 1 ≤
          8 * (G_d.m + 1) ^ 2 := by
        have hm1 : 2 * G_d.m * (G_d.m + 1) ≤ 4 * (G_d.m + 1) ^ 2 := by nlinarith
        nlinarith [Nat.mul_le_mul_right (G_d.m + 1) hK1_le]
      have hcost_real : ((lastMWUK (simpleMinLenSubgraph G_d (fun _ => 1)) * (G_d.m + 1) + 1 : ℕ) : ℝ) ≤
          8 * ((G_d.m : ℝ) + 1) ^ 2 := by exact_mod_cast hcost_nat
      unfold lastLevelParams
      simpa [pow_zero] using hcost_real
  · simp only [hnl, ↓reduceDIte]
    let F0 : MGraph := { V := G_d.V, E := ∅, tail := G_d.tail, head := G_d.head }
    have hloop_all : ∀ e ∈ G_d.E, G_d.tail e = G_d.head e := by
      intro e he
      by_contra hne
      exact hnl ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩⟩
    have hF0_for : F0.IsForest := by
      refine ⟨fun _ he => False.elim (Finset.notMem_empty _ he), fun P ⟨hne, _, _, hW⟩ => ?_⟩
      cases hW with
      | nil _ => exact hne rfl
      | cons hxE _ _ => exact Finset.notMem_empty _ hxE
    have hF0_conn_eq : ∀ {u v : ℕ}, F0.Connected u v → u = v := by
      intro u v ⟨P, hW⟩
      cases hW with
      | nil _ => rfl
      | cons hxE _ _ => exact False.elim (Finset.notMem_empty _ hxE)
    have hG_conn_eq : ∀ {u v : ℕ}, G_d.Connected u v → u = v := by
      intro u v ⟨P, hW⟩
      induction hW with
      | nil _ => rfl
      | @cons a b x xs hxE hsrc _ ih =>
        have hloop := hloop_all x.1 hxE
        have heq_sd : G_d.src x = G_d.dst x := by
          rcases x with ⟨e, _ | _⟩ <;> simp [MGraph.src, MGraph.dst, hloop]
        exact hsrc.symm.trans (heq_sd.trans ih)
    have hRF0 : ({ F := F0, R := G_d.V } : RootedForest).IsRootedSpanningForestOf G_d := by
      refine ⟨hF0_for, rfl, Finset.Subset.refl _, ?_,
        ⟨Finset.Subset.refl _, Finset.empty_subset _, fun _ _ => ⟨rfl, rfl⟩⟩⟩
      intro v hv
      exact ⟨v, ⟨hv, MGraph.connected_refl F0 v⟩, fun r' ⟨_, hc⟩ => (hF0_conn_eq hc).symm⟩
    refine ⟨Nat.zero_lt_one, ?_, ?_, ?_, ?_⟩
    · intro j _
      refine ⟨hF0_for, hRF0, ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩, ?_⟩
      intro e he
      have hloop := hloop_all e he
      have hstr : ({ F := F0, R := G_d.V } : RootedForest).stretch G_d ℓ_d e = 1 := by
        unfold RootedForest.stretch
        dsimp only
        rw [hloop]
        simp only [↓reduceIte]
        rw [forestPath_self hF0_for, walkLength_nil, zero_div, add_zero]
      rw [hstr]
      exact ⟨le_rfl, le_max_left _ _⟩
    · intro e _
      simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_one, div_one]
      exact le_max_left _ _
    · intro _ _ u _ v _ hc
      rw [hG_conn_eq hc]
      exact MGraph.connected_refl F0 v
    · have hcost1 : (1 : ℝ) ≤ 8 * ((G_d.m : ℝ) + 1) ^ 2 := by
        have hm0 : (0 : ℝ) ≤ (G_d.m : ℝ) := Nat.cast_nonneg _
        nlinarith
      unfold lastLevelParams
      simpa [pow_zero] using hcost1

end MinCostFlow.SparseCore
