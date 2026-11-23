module

public import WordRAM.Contract
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Expander.DecomposePhi
public import MinCostFlow.Expander.GraphCompression
public import MinCostFlow.Expander.TwinDecompose
public import MinCostFlow.Expander.PruningProg

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mathematical Bridges for Word-RAM `Decompose` (Theorem 8.5 / Theorem B.1 / Algorithm 5)

Provides the pure graph-theoretic and arithmetic bridges used by the Word-RAM `DecomposeImpl`:
1. Exact integer/ceil characterizations for uniform denominator `D_phi = phiDenHalf` and `PruneCfg`;
2. Exact subgraph isomorphism between `(curG, X)` and `compressPartGraph actVerts (curG.inside X)`;
3. Reduction from pruning on `compressPartGraph` (or bad-twin drop) to `partX` guarantees;
4. Level correctness and `remG.m ≤ 2^(i - 1) * curG.n` from Word-RAM `uniqLabels` and `R_of`;
5. `Decompose.encode` length bound `≤ 4 + 5 * G.m` and level count `ℓ` bounds.
-/

@[expose] public section

namespace MinCostFlow.Expander

open Classical
open MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Integer / Ceil Arithmetic for `D_phi` and `PruneCfg` -/

lemma ceil_div_eq_nat_div (a b : ℕ) (hb : 1 ≤ b) :
    Nat.ceil ((a : ℝ) / (b : ℝ)) = (a + b - 1) / b := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hk_lt : (a + b - 1) / b * b ≤ a + b - 1 := Nat.div_mul_le_self _ _
  by_cases ha0 : a = 0
  · subst ha0
    have hdiv0 : (b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
    simp [hdiv0]
  · have hpos : 0 < (a + b - 1) / b := Nat.div_pos (by omega) (by omega)
    rw [Nat.ceil_eq_iff (by omega : (a + b - 1) / b ≠ 0)]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hbR]
      have hnat : ((a + b - 1) / b - 1) * b < a := by
        have hsub : ((a + b - 1) / b - 1) * b + b = (a + b - 1) / b * b := by
          calc ((a + b - 1) / b - 1) * b + b
              = ((a + b - 1) / b - 1 + 1) * b := by ring
            _ = (a + b - 1) / b * b := by rw [Nat.sub_add_cancel hpos]
        omega
      exact_mod_cast hnat
    · rw [div_le_iff₀ hbR]
      have h1 : a ≤ ((a + b - 1) / b) * b := by
        have hmod : (a + b - 1) / b * b + (a + b - 1) % b = a + b - 1 := by
          rw [mul_comm]; exact Nat.div_add_mod (a + b - 1) b
        have hltb : (a + b - 1) % b ≤ b - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ (by omega))
        omega
      exact_mod_cast h1

lemma lt_one_div_mul_iff {d D D_phi : ℕ} (hDphi : 1 ≤ D_phi) :
    (d : ℝ) < (1 / (D_phi : ℝ)) * (D : ℝ) ↔ d * D_phi < D := by
  have hpos : (0 : ℝ) < (D_phi : ℝ) := by exact_mod_cast hDphi
  rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
  exact_mod_cast Iff.rfl

lemma one_div_three_mul_le_iff {d D D_phi : ℕ} (hDphi : 1 ≤ D_phi) :
    (1 / (3 * (D_phi : ℝ))) * (D : ℝ) ≤ (d : ℝ) ↔ (D + 3 * D_phi - 1) / (3 * D_phi) ≤ d := by
  have h3pos : 1 ≤ 3 * D_phi := by omega
  have hle : (1 / (3 * (D_phi : ℝ))) * (D : ℝ) ≤ (d : ℝ) ↔
      (D : ℝ) / ((3 * D_phi : ℕ) : ℝ) ≤ (d : ℝ) := by
    push_cast; rw [one_div_mul_eq_div]
  rw [hle, ← Nat.ceil_le, ceil_div_eq_nat_div D (3 * D_phi) h3pos]

lemma pruneCfg_unif_params {G : Cited.Graph} {X B : Finset ℕ} {D D_phi : ℕ}
    (hDphi : 200 ≤ D_phi) :
    let φ₀ : ℝ := 1 / (D_phi : ℝ)
    let θ_in : ℝ := φ₀ * (D : ℝ)
    let cfg := pruneCfgOf G X B φ₀ θ_in
    cfg.C_cap = 4 * D_phi + 2 ∧
    5 ≤ cfg.C_cap ∧
    4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1) ∧
    cfg.θ_out_nat = (D + 3 * D_phi - 1) / (3 * D_phi) ∧
    cfg.H = 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * (G.inside X).length + 1) + 1) + 2 := by
  intro φ₀ θ_in cfg
  have hpos : (0 : ℝ) < (D_phi : ℝ) := by exact_mod_cast (by omega : 1 ≤ D_phi)
  have h4div : 4 / φ₀ = ((4 * D_phi : ℕ) : ℝ) := by
    dsimp only [φ₀]
    rw [div_eq_mul_inv, one_div, inv_inv]
    push_cast
    ring
  have hCcap : cfg.C_cap = 4 * D_phi + 2 := by
    dsimp only [cfg, pruneCfgOf]
    rw [h4div, Nat.ceil_natCast]
    exact max_eq_right (by omega)
  have hC5 : 5 ≤ cfg.C_cap := by omega
  have hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1) := by
    rw [hCcap]
    have hc : ((4 * D_phi + 2 : ℕ) : ℝ) - 1 = 4 * (D_phi : ℝ) + 1 := by
      push_cast; ring
    rw [hc]
    dsimp only [φ₀]
    rw [one_div_mul_eq_div, le_div_iff₀ hpos]
    nlinarith
  have htheta : cfg.θ_out_nat = (D + 3 * D_phi - 1) / (3 * D_phi) := by
    dsimp only [cfg, pruneCfgOf, θ_in, φ₀]
    have heq : (1 / (D_phi : ℝ) * (D : ℝ)) / 3 = (D : ℝ) / ((3 * D_phi : ℕ) : ℝ) := by
      push_cast; ring
    rw [heq]
    exact ceil_div_eq_nat_div D (3 * D_phi) (by omega)
  have hH : cfg.H = 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * (G.inside X).length + 1) + 1) + 2 := by
    change 4 * cfg.C_cap * (Nat.log 2 (2 * (G.inside X).length + 1) + 1) + 2 = _
    rw [hCcap]
  exact ⟨hCcap, hC5, hCphi, htheta, hH⟩

/-! ## 2. Compressed Induced Subgraph Isomorphism -/

/-- Compressed multigraph built from `actVerts` and an edge list `es`. -/
def compressPartGraph (actVerts : List ℕ) (es : List (ℕ × ℕ)) : Cited.Graph where
  n := actVerts.length
  edges := compressEdges actVerts es

lemma actVertsSpec_inside {curG : Cited.Graph} {actVerts : List ℕ}
    (hstrict : actVerts.Pairwise (· < ·)) (hbound : ∀ u ∈ actVerts, u < curG.n) :
    ActVertsSpec { n := curG.n, edges := curG.inside actVerts.toFinset } actVerts := by
  refine ⟨hstrict, hbound, fun e he => ?_⟩
  simp only [Cited.Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_toFinset] at he
  exact he.2

lemma compressPartGraph_eq_compressGraph (curG : Cited.Graph) (actVerts : List ℕ) (X : Finset ℕ) :
    compressPartGraph actVerts (curG.inside X) =
      compressGraph actVerts { n := curG.n, edges := curG.inside X } := rfl

lemma compressPartGraph_isValid {curG : Cited.Graph} {actVerts : List ℕ}
    (hstrict : actVerts.Pairwise (· < ·)) (hbound : ∀ u ∈ actVerts, u < curG.n) :
    (compressPartGraph actVerts (curG.inside actVerts.toFinset)).IsValid := by
  rw [compressPartGraph_eq_compressGraph]
  exact compressGraph_isValid (actVertsSpec_inside hstrict hbound)

lemma compressPartGraph_isLoopless {curG : Cited.Graph} {actVerts : List ℕ}
    (hL : curG.IsLoopless) (hstrict : actVerts.Pairwise (· < ·))
    (hbound : ∀ u ∈ actVerts, u < curG.n) :
    (compressPartGraph actVerts (curG.inside actVerts.toFinset)).IsLoopless := by
  rw [compressPartGraph_eq_compressGraph]
  exact compressGraph_isLoopless (actVertsSpec_inside hstrict hbound)
    fun e he => hL e (List.mem_filter.mp he).1

lemma compressPartGraph_m (actVerts : List ℕ) (es : List (ℕ × ℕ)) :
    (compressPartGraph actVerts es).m = es.length := by
  simp [compressPartGraph, compressEdges, Cited.Graph.m]

lemma compressPartGraph_inside {curG : Cited.Graph} {actVerts : List ℕ}
    (hstrict : actVerts.Pairwise (· < ·)) (hbound : ∀ u ∈ actVerts, u < curG.n)
    {S_loc : Finset ℕ} (hS : S_loc ⊆ Finset.range actVerts.length) :
    let X := actVerts.toFinset
    let f : ℕ → ℕ := fun k => actVerts.getD k 0
    let g : ℕ → ℕ := fun u => actVerts.idxOf u
    (compressPartGraph actVerts (curG.inside X)).inside S_loc =
      (curG.inside (S_loc.image f)).map fun e => (g e.1, g e.2) := by
  intro X f g
  have hact := actVertsSpec_inside hstrict hbound
  have hinj : ∀ i j, i < actVerts.length → j < actVerts.length → f i = f j → i = j :=
    fun _ _ hi hj h => pairwise_lt_getD_inj hstrict hi hj h
  have himg_sub : S_loc.image f ⊆ X := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hk_lt : k < actVerts.length := Finset.mem_range.mp (hS hk)
    simp only [X, f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt,
      Option.getD_some, List.mem_toFinset]
    exact List.getElem_mem hk_lt
  have hcomp_inside : (compressPartGraph actVerts (curG.inside X)).inside S_loc =
      ((curG.inside X).filter fun e => decide (g e.1 ∈ S_loc) && decide (g e.2 ∈ S_loc)).map
        fun e => (g e.1, g e.2) := by
    simp [compressPartGraph, compressEdges, Cited.Graph.inside, List.filter_map, Function.comp_def, g]
  have hfilter_eq :
      (curG.inside X).filter (fun e => decide (g e.1 ∈ S_loc) && decide (g e.2 ∈ S_loc)) =
        curG.inside (S_loc.image f) := by
    simp only [Cited.Graph.inside, List.filter_filter]
    refine List.filter_congr fun e _ => ?_
    by_cases he1X : e.1 ∈ X <;> by_cases he2X : e.2 ∈ X
    · have h1m : e.1 ∈ actVerts := List.mem_toFinset.mp he1X
      have h2m : e.2 ∈ actVerts := List.mem_toFinset.mp he2X
      have hg1_lt : g e.1 < actVerts.length := hact.idxOf_lt h1m
      have hg2_lt : g e.2 < actVerts.length := hact.idxOf_lt h2m
      have h1_iff : g e.1 ∈ S_loc ↔ e.1 ∈ S_loc.image f := by
        constructor
        · intro hg
          exact Finset.mem_image.mpr ⟨g e.1, hg, hact.getD_idxOf h1m⟩
        · intro hm
          rcases Finset.mem_image.mp hm with ⟨k, hk, hfk⟩
          have hk_lt : k < actVerts.length := Finset.mem_range.mp (hS hk)
          have hkeq : k = g e.1 := hinj k (g e.1) hk_lt hg1_lt (hfk.trans (hact.getD_idxOf h1m).symm)
          rwa [← hkeq]
      have h2_iff : g e.2 ∈ S_loc ↔ e.2 ∈ S_loc.image f := by
        constructor
        · intro hg
          exact Finset.mem_image.mpr ⟨g e.2, hg, hact.getD_idxOf h2m⟩
        · intro hm
          rcases Finset.mem_image.mp hm with ⟨k, hk, hfk⟩
          have hk_lt : k < actVerts.length := Finset.mem_range.mp (hS hk)
          have hkeq : k = g e.2 := hinj k (g e.2) hk_lt hg2_lt (hfk.trans (hact.getD_idxOf h2m).symm)
          rwa [← hkeq]
      simp [he1X, he2X, h1_iff, h2_iff]
    · have hnot2 : e.2 ∉ S_loc.image f := fun h => he2X (himg_sub h)
      simp [he1X, he2X, hnot2]
    · have hnot1 : e.1 ∉ S_loc.image f := fun h => he1X (himg_sub h)
      simp [he1X, he2X, hnot1]
    · have hnot1 : e.1 ∉ S_loc.image f := fun h => he1X (himg_sub h)
      simp [he1X, he2X, hnot1]
  rw [hcomp_inside, hfilter_eq]

lemma compressPartGraph_degIn {curG : Cited.Graph} {actVerts : List ℕ}
    (hstrict : actVerts.Pairwise (· < ·)) (hbound : ∀ u ∈ actVerts, u < curG.n)
    {S_loc : Finset ℕ} (hS : S_loc ⊆ Finset.range actVerts.length)
    {k : ℕ} (hk : k < actVerts.length) :
    let X := actVerts.toFinset
    let f : ℕ → ℕ := fun i => actVerts.getD i 0
    (compressPartGraph actVerts (curG.inside X)).degIn S_loc k =
      curG.degIn (S_loc.image f) (f k) := by
  intro X f
  have hact := actVertsSpec_inside hstrict hbound
  set g : ℕ → ℕ := fun u => actVerts.idxOf u
  have hins := compressPartGraph_inside hstrict hbound hS
  have himg_sub : S_loc.image f ⊆ X := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
    exact List.mem_toFinset.mpr <| by
      have hi_lt := Finset.mem_range.mp (hS hi)
      simp [f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt]
  have hmem_X : ∀ e ∈ curG.inside (S_loc.image f), e.1 ∈ actVerts ∧ e.2 ∈ actVerts := by
    intro e he
    simp only [Cited.Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
    exact ⟨List.mem_toFinset.mp (himg_sub he.2.1), List.mem_toFinset.mp (himg_sub he.2.2)⟩
  unfold Cited.Graph.degIn
  rw [hins, List.filter_map, List.length_map, List.filter_map, List.length_map]
  have hf1 : ((curG.inside (S_loc.image f)).filter (fun e => decide (g e.1 = k))).length =
      ((curG.inside (S_loc.image f)).filter (fun e => decide (e.1 = f k))).length := by
    congr 1
    refine List.filter_congr fun e he => ?_
    have h1m := (hmem_X e he).1
    have heq : g e.1 = k ↔ e.1 = f k := by
      change actVerts.idxOf e.1 = k ↔ e.1 = actVerts.getD k 0
      constructor
      · intro h; rw [← h]; exact (hact.getD_idxOf h1m).symm
      · intro h; rw [h]; exact hact.idxOf_getD hk
    simp [heq]
  have hf2 : ((curG.inside (S_loc.image f)).filter (fun e => decide (g e.2 = k))).length =
      ((curG.inside (S_loc.image f)).filter (fun e => decide (e.2 = f k))).length := by
    congr 1
    refine List.filter_congr fun e he => ?_
    have h2m := (hmem_X e he).2
    have heq : g e.2 = k ↔ e.2 = f k := by
      change actVerts.idxOf e.2 = k ↔ e.2 = actVerts.getD k 0
      constructor
      · intro h; rw [← h]; exact (hact.getD_idxOf h2m).symm
      · intro h; rw [h]; exact hact.idxOf_getD hk
    simp [heq]
  exact congrArg₂ (· + ·) hf1 hf2

lemma compressPartGraph_volIn {curG : Cited.Graph} {actVerts : List ℕ}
    (hstrict : actVerts.Pairwise (· < ·)) (hbound : ∀ u ∈ actVerts, u < curG.n)
    {A_loc S_loc : Finset ℕ} (hA : A_loc ⊆ Finset.range actVerts.length) (hSA : S_loc ⊆ A_loc) :
    let X := actVerts.toFinset
    let f : ℕ → ℕ := fun i => actVerts.getD i 0
    (compressPartGraph actVerts (curG.inside X)).volIn A_loc S_loc =
      curG.volIn (A_loc.image f) (S_loc.image f) := by
  intro X f
  have hS : S_loc ⊆ Finset.range actVerts.length := hSA.trans hA
  have hinj : Set.InjOn f (S_loc : Set ℕ) := fun i hi j hj hij =>
    pairwise_lt_getD_inj hstrict (Finset.mem_range.mp (hS hi)) (Finset.mem_range.mp (hS hj)) hij
  unfold Cited.Graph.volIn
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact compressPartGraph_degIn hstrict hbound hA (Finset.mem_range.mp (hS hk))

lemma compressPartGraph_cutIn {curG : Cited.Graph} {actVerts : List ℕ}
    (hstrict : actVerts.Pairwise (· < ·)) (hbound : ∀ u ∈ actVerts, u < curG.n)
    {A_loc S_loc : Finset ℕ} (hA : A_loc ⊆ Finset.range actVerts.length) (hSA : S_loc ⊆ A_loc) :
    let X := actVerts.toFinset
    let f : ℕ → ℕ := fun i => actVerts.getD i 0
    (compressPartGraph actVerts (curG.inside X)).cutIn A_loc S_loc =
      curG.cutIn (A_loc.image f) (S_loc.image f) := by
  intro X f
  have hact := actVertsSpec_inside hstrict hbound
  set g : ℕ → ℕ := fun u => actVerts.idxOf u
  have hins := compressPartGraph_inside hstrict hbound hA
  have hA_sub : A_loc.image f ⊆ X := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hk_lt := Finset.mem_range.mp (hA hk)
    simp [X, f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
  have hinj : ∀ i j, i < actVerts.length → j < actVerts.length → f i = f j → i = j :=
    fun _ _ hi hj h => pairwise_lt_getD_inj hstrict hi hj h
  unfold Cited.Graph.cutIn
  rw [hins, List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun e he => ?_
  simp only [Cited.Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
  have h1m : e.1 ∈ actVerts := List.mem_toFinset.mp (hA_sub he.2.1)
  have h2m : e.2 ∈ actVerts := List.mem_toFinset.mp (hA_sub he.2.2)
  have hg1_lt : g e.1 < actVerts.length := hact.idxOf_lt h1m
  have hg2_lt : g e.2 < actVerts.length := hact.idxOf_lt h2m
  have h1_iff : g e.1 ∈ S_loc ↔ e.1 ∈ S_loc.image f := by
    constructor
    · intro hg; exact Finset.mem_image.mpr ⟨g e.1, hg, hact.getD_idxOf h1m⟩
    · intro hm
      rcases Finset.mem_image.mp hm with ⟨k, hk, hfk⟩
      have hk_lt := Finset.mem_range.mp (hA (hSA hk))
      have hkeq : k = g e.1 := hinj k (g e.1) hk_lt hg1_lt (hfk.trans (hact.getD_idxOf h1m).symm)
      rwa [← hkeq]
  have h2_iff : g e.2 ∈ S_loc ↔ e.2 ∈ S_loc.image f := by
    constructor
    · intro hg; exact Finset.mem_image.mpr ⟨g e.2, hg, hact.getD_idxOf h2m⟩
    · intro hm
      rcases Finset.mem_image.mp hm with ⟨k, hk, hfk⟩
      have hk_lt := Finset.mem_range.mp (hA (hSA hk))
      have hkeq : k = g e.2 := hinj k (g e.2) hk_lt hg2_lt (hfk.trans (hact.getD_idxOf h2m).symm)
      rwa [← hkeq]
  dsimp only [g, Function.comp_def] at h1_iff h2_iff ⊢
  simp only [h1_iff, h2_iff]

lemma compressPartGraph_image_f_verts (actVerts : List ℕ) :
    (Finset.range actVerts.length).image (fun i => actVerts.getD i 0) = actVerts.toFinset := by
  ext u
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  · intro hu
    rcases List.getElem_of_mem hu with ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]⟩

lemma compressPartGraph_sdiff_image {actVerts : List ℕ} (hstrict : actVerts.Pairwise (· < ·))
    {A_loc S_loc : Finset ℕ} (hA : A_loc ⊆ Finset.range actVerts.length) (hSA : S_loc ⊆ A_loc) :
    let f : ℕ → ℕ := fun i => actVerts.getD i 0
    (A_loc \ S_loc).image f = A_loc.image f \ S_loc.image f := by
  intro f
  ext u
  simp only [Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨k, ⟨hkA, hkS⟩, rfl⟩
    refine ⟨⟨k, hkA, rfl⟩, ?_⟩
    rintro ⟨j, hjS, hjf⟩
    have hj_lt := Finset.mem_range.mp (hA (hSA hjS))
    have hk_lt := Finset.mem_range.mp (hA hkA)
    have heq := pairwise_lt_getD_inj hstrict hj_lt hk_lt hjf
    exact hkS (heq ▸ hjS)
  · rintro ⟨⟨k, hkA, rfl⟩, hnS⟩
    exact ⟨k, ⟨hkA, fun hkS => hnS ⟨k, hkS, rfl⟩⟩, rfl⟩

lemma compressPartGraph_expander_iff {curG : Cited.Graph} {actVerts : List ℕ}
    (hstrict : actVerts.Pairwise (· < ·)) (hbound : ∀ u ∈ actVerts, u < curG.n)
    {R_loc : Finset ℕ} (hR : R_loc ⊆ Finset.range actVerts.length) {φ : ℝ} :
    let X := actVerts.toFinset
    let f : ℕ → ℕ := fun i => actVerts.getD i 0
    (compressPartGraph actVerts (curG.inside X)).IsConductanceExpanderOn R_loc φ ↔
      curG.IsConductanceExpanderOn (R_loc.image f) φ := by
  intro X f
  have hact := actVertsSpec_inside hstrict hbound
  set g : ℕ → ℕ := fun u => actVerts.idxOf u
  set G_X := compressPartGraph actVerts (curG.inside X)
  have hR_sub_X : R_loc.image f ⊆ X := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hk_lt := Finset.mem_range.mp (hR hk)
    simp [X, f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
  have hf_injOn : Set.InjOn f (R_loc : Set ℕ) := fun i hi j hj hij =>
    pairwise_lt_getD_inj hstrict (Finset.mem_range.mp (hR hi)) (Finset.mem_range.mp (hR hj)) hij
  constructor
  · intro hexp S hS hSne hSneR
    let S_loc := S.image g
    have hS_loc_sub : S_loc ⊆ R_loc := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨u, huS, rfl⟩
      rcases Finset.mem_image.mp (hS huS) with ⟨k', hk'R, rfl⟩
      have hk'_lt := Finset.mem_range.mp (hR hk'R)
      have hidx : g (f k') = k' := hact.idxOf_getD hk'_lt
      rw [hidx]; exact hk'R
    have hS_loc_img : S_loc.image f = S := by
      ext u
      simp only [S_loc, Finset.mem_image]
      constructor
      · rintro ⟨k, ⟨v, hvS, rfl⟩, rfl⟩
        rcases Finset.mem_image.mp (hS hvS) with ⟨k', hk'R, rfl⟩
        have hk'_lt := Finset.mem_range.mp (hR hk'R)
        have hvm : f k' ∈ actVerts := by
          simp [f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'_lt]
        have hfgk : f (g (f k')) = f k' := hact.getD_idxOf hvm
        rwa [hfgk]
      · intro huS
        rcases Finset.mem_image.mp (hS huS) with ⟨k', hk'R, rfl⟩
        have hk'_lt := Finset.mem_range.mp (hR hk'R)
        exact ⟨k', ⟨f k', huS, hact.idxOf_getD hk'_lt⟩, rfl⟩
    have hloc_ne : S_loc.Nonempty := by
      rcases hSne with ⟨u, huS⟩
      exact ⟨g u, Finset.mem_image.mpr ⟨u, huS, rfl⟩⟩
    have hloc_neR : S_loc ≠ R_loc := fun h => hSneR (by rw [← hS_loc_img, h])
    have hexp_loc := hexp S_loc hS_loc_sub hloc_ne hloc_neR
    have hsdiff := compressPartGraph_sdiff_image hstrict hR hS_loc_sub
    dsimp only at hsdiff
    rw [hS_loc_img] at hsdiff
    have hv1 := compressPartGraph_volIn hstrict hbound hR hS_loc_sub
    have hv2 := compressPartGraph_volIn hstrict hbound hR (Finset.sdiff_subset (s := R_loc) (t := S_loc))
    have hc1 := compressPartGraph_cutIn hstrict hbound hR hS_loc_sub
    dsimp only at hv1 hv2 hc1
    rwa [hv1, hv2, hc1, hS_loc_img, hsdiff] at hexp_loc
  · intro hexp S_loc hSR hSne hSneR
    have hS_img_sub : S_loc.image f ⊆ R_loc.image f := Finset.image_subset_image hSR
    have hS_img_ne : (S_loc.image f).Nonempty := hSne.image f
    have hS_img_neR : S_loc.image f ≠ R_loc.image f := by
      intro h
      apply hSneR
      ext k
      constructor
      · intro hk; exact hSR hk
      · intro hk
        have hmem : f k ∈ S_loc.image f := h ▸ Finset.mem_image.mpr ⟨k, hk, rfl⟩
        rcases Finset.mem_image.mp hmem with ⟨j, hjS, hfj⟩
        rwa [← hf_injOn (hSR hjS) hk hfj]
    have hexp_img := hexp (S_loc.image f) hS_img_sub hS_img_ne hS_img_neR
    have hsdiff := compressPartGraph_sdiff_image hstrict hR hSR
    have hv1 := compressPartGraph_volIn hstrict hbound hR hSR
    have hv2 := compressPartGraph_volIn hstrict hbound hR (Finset.sdiff_subset (s := R_loc) (t := S_loc))
    have hc1 := compressPartGraph_cutIn hstrict hbound hR hSR
    dsimp only at hsdiff hv1 hv2 hc1
    rw [← hsdiff] at hexp_img
    rwa [hv1, hv2, hc1]

/-! ## 3. Reduction from Compressed Pruning / Bad-Twin Drop to `partX` Guarantees -/

lemma badTwin_part_spec {D D_phi : ℕ} {curG : Cited.Graph}
    (hV : curG.IsValid) (hL : curG.IsLoopless) (hD : 1 ≤ D) (hDphi : 1 ≤ D_phi)
    {Y : Finset ℕ} {φ_B1 : ℝ} (hφ₀ : 0 < φ_B1) (hφ_unif : 1 / (D_phi : ℝ) ≤ φ_B1)
    (hexpY : (twinGraph D curG).IsConductanceExpanderOn Y φ_B1)
    {actVerts : List ℕ} (hstrict : actVerts.Pairwise (· < ·))
    (hactX : actVerts.toFinset = partX curG.n Y)
    (hcard : 2 ≤ actVerts.length)
    {k : ℕ} (hk : k < actVerts.length)
    (hdeg : curG.degIn (partX curG.n Y) (actVerts.getD k 0) * D_phi < D)
    (htwin : 2 * actVerts.getD k 0 + 1 ∈ Y) :
    (curG.inside (partX curG.n Y)).length ≤ 15 * (twinGraph D curG).cut Y := by
  set X := partX curG.n Y
  have hXcard : 2 ≤ X.card := by
    rw [← hactX, List.toFinset_card_of_nodup (hstrict.imp fun h => ne_of_lt h)]
    exact hcard
  have hvk : actVerts.getD k 0 ∈ X := by
    rw [← hactX, List.mem_toFinset]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have hdegR : (curG.degIn X (actVerts.getD k 0) : ℝ) < φ_B1 * (D : ℝ) := by
    have hlt1 : (curG.degIn X (actVerts.getD k 0) : ℝ) < (1 / (D_phi : ℝ)) * (D : ℝ) :=
      (lt_one_div_mul_iff hDphi).mpr hdeg
    exact lt_of_lt_of_le hlt1 (mul_le_mul_of_nonneg_right hφ_unif (Nat.cast_nonneg _))
  have hdrop := subcase1_drop hV hL hD hφ₀ hexpY hXcard hvk hdegR htwin
  omega

theorem prune_compressed_part_pre {D D_phi : ℕ} {curG : Cited.Graph}
    (hV : curG.IsValid) (hD : 1 ≤ D) (hDphi : 200 ≤ D_phi)
    {Y : Finset ℕ} {φ_B1 : ℝ} (hφ_unif : 1 / (D_phi : ℝ) ≤ φ_B1)
    (hexpY : (twinGraph D curG).IsConductanceExpanderOn Y φ_B1)
    {actVerts : List ℕ} (hstrict : actVerts.Pairwise (· < ·))
    (hactX : actVerts.toFinset = partX curG.n Y) :
    let X := partX curG.n Y
    let G_X := compressPartGraph actVerts (curG.inside X)
    let B_loc := (Finset.range G_X.n).filter fun k => decide (G_X.degIn G_X.verts k * D_phi < D)
    let cfg := pruneCfgOf G_X G_X.verts B_loc (1 / (D_phi : ℝ)) ((1 / (D_phi : ℝ)) * (D : ℝ))
    (∀ u ∈ actVerts, u < curG.n) ∧
    G_X.IsValid ∧
    cfg.Valid ∧
    G_X.IsConductanceExpanderOn G_X.verts (1 / (D_phi : ℝ)) ∧
    5 ≤ cfg.C_cap ∧
    4 ≤ (1 / (D_phi : ℝ)) * ((cfg.C_cap : ℝ) - 1) ∧
    (∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x) := by
  intro X G_X B_loc cfg
  have hbound : ∀ u ∈ actVerts, u < curG.n := fun u hu => by
    have huX : u ∈ partX curG.n Y := by rw [← hactX, List.mem_toFinset]; exact hu
    exact Finset.mem_range.mp (Finset.mem_filter.mp huX).1
  have hGX_V : G_X.IsValid := by
    simpa [G_X, hactX] using compressPartGraph_isValid hstrict hbound
  have hexpX : curG.IsConductanceExpanderOn X (1 / (D_phi : ℝ)) := by
    have h1 := conductance_of_twin hV (le_trans (by positivity) hφ_unif) hexpY
    intro S hS hSne hSneX
    have hmul : (1 / (D_phi : ℝ)) * min (curG.volIn X S : ℝ) (curG.volIn X (X \ S)) ≤
        φ_B1 * min (curG.volIn X S : ℝ) (curG.volIn X (X \ S)) :=
      mul_le_mul_of_nonneg_right hφ_unif (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact le_trans hmul (h1 S hS hSne hSneX)
  have hexpGX : G_X.IsConductanceExpanderOn G_X.verts (1 / (D_phi : ℝ)) := by
    have hiff := compressPartGraph_expander_iff (curG := curG) hstrict hbound
      (R_loc := Finset.range actVerts.length) le_rfl (φ := 1 / (D_phi : ℝ))
    dsimp only at hiff
    dsimp only [X] at hexpX
    rw [← hactX] at hexpX
    have himg : (Finset.range actVerts.length).image (fun i => actVerts.getD i 0) = actVerts.toFinset :=
      compressPartGraph_image_f_verts actVerts
    rw [himg] at hiff
    have hverts_eq : G_X.verts = Finset.range actVerts.length := rfl
    have hGX_eq : compressPartGraph actVerts (curG.inside actVerts.toFinset) = G_X := by
      simp [G_X, X, hactX]
    rw [hGX_eq] at hiff
    rw [hverts_eq]
    exact hiff.mpr hexpX
  obtain ⟨hCcap, hC5, hCphi, htheta, _⟩ := pruneCfg_unif_params (G := G_X) (X := G_X.verts) (B := B_loc)
    (D := D) hDphi
  have hθ_nat : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x := by
    intro x hxX hxB d hd
    have hge : D ≤ G_X.degIn G_X.verts x * D_phi := by
      by_contra hlt
      push Not at hlt
      exact hxB (Finset.mem_filter.mpr ⟨hxX, decide_eq_true hlt⟩)
    rw [htheta] at hd
    have h3d : (3 * d : ℕ) * D_phi < D := by
      have hdiv_lt : d < (D + 3 * D_phi - 1) / (3 * D_phi) := hd
      have hmul_lt : d * (3 * D_phi) + (3 * D_phi) ≤ (D + 3 * D_phi - 1) / (3 * D_phi) * (3 * D_phi) := by
        calc d * (3 * D_phi) + (3 * D_phi) = (d + 1) * (3 * D_phi) := by ring
          _ ≤ (D + 3 * D_phi - 1) / (3 * D_phi) * (3 * D_phi) :=
            Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdiv_lt)
      have hle_top : (D + 3 * D_phi - 1) / (3 * D_phi) * (3 * D_phi) ≤ D + 3 * D_phi - 1 :=
        Nat.div_mul_le_self _ _
      have hring : 3 * d * D_phi = d * (3 * D_phi) := by ring
      omega
    change 3 * d ≤ G_X.degIn G_X.verts x
    nlinarith
  have hcfgV : cfg.Valid := by
    refine ⟨hGX_V, Finset.filter_subset _ _, le_trans (by decide) hC5, le_rfl, ?_⟩
    intro v hvX hvB
    have hge : D ≤ G_X.degIn G_X.verts v * D_phi := by
      by_contra hlt
      push Not at hlt
      exact hvB (Finset.mem_filter.mpr ⟨hvX, decide_eq_true hlt⟩)
    change cfg.θ_out_nat ≤ G_X.degIn G_X.verts v
    rw [htheta]
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 3 * D_phi)]
    have hk_le : G_X.degIn G_X.verts v * D_phi ≤ G_X.degIn G_X.verts v * (3 * D_phi) :=
      Nat.mul_le_mul_left _ (by omega)
    calc D + 3 * D_phi - 1 < D + 3 * D_phi := by omega
      _ ≤ G_X.degIn G_X.verts v * (3 * D_phi) + 3 * D_phi := by omega
      _ = (G_X.degIn G_X.verts v + 1) * (3 * D_phi) := by ring
  exact ⟨hbound, hGX_V, hcfgV, hexpGX, hC5, hCphi, hθ_nat⟩

theorem prune_compressed_part_post {D D_phi : ℕ} {curG : Cited.Graph}
    (hV : curG.IsValid) (hL : curG.IsLoopless) (hDphi : 200 ≤ D_phi)
    {Y : Finset ℕ} {actVerts : List ℕ} (hstrict : actVerts.Pairwise (· < ·))
    (hactX : actVerts.toFinset = partX curG.n Y)
    {R_loc : Finset ℕ}
    (hR_sub : R_loc ⊆
      (compressPartGraph actVerts (curG.inside (partX curG.n Y))).verts \
        ((Finset.range (compressPartGraph actVerts (curG.inside (partX curG.n Y))).n).filter
          fun k => decide ((compressPartGraph actVerts (curG.inside (partX curG.n Y))).degIn
            (compressPartGraph actVerts (curG.inside (partX curG.n Y))).verts k * D_phi < D)))
    (hexpR_loc : (compressPartGraph actVerts (curG.inside (partX curG.n Y))).IsConductanceExpanderOn
      R_loc ((1 / (D_phi : ℝ)) / 3))
    (hdegR_loc : ∀ v ∈ R_loc, (D + 3 * D_phi - 1) / (3 * D_phi) ≤
      (compressPartGraph actVerts (curG.inside (partX curG.n Y))).degIn R_loc v)
    (hvol_loc :
      let G_X := compressPartGraph actVerts (curG.inside (partX curG.n Y))
      let B_loc := (Finset.range G_X.n).filter fun k => decide (G_X.degIn G_X.verts k * D_phi < D)
      G_X.volIn G_X.verts (G_X.verts \ R_loc) ≤
        G_X.volIn G_X.verts B_loc + 2 * (4 * D_phi + 2) * G_X.cutIn G_X.verts B_loc)
    (hnoBadTwin : ∀ k < actVerts.length,
      curG.degIn (partX curG.n Y) (actVerts.getD k 0) * D_phi < D →
      2 * actVerts.getD k 0 + 1 ∉ Y) :
    let X := partX curG.n Y
    let R := if R_loc.card ≤ 1 then ∅ else R_loc.image (fun k => actVerts.getD k 0)
    R ⊆ X ∧
    (R = ∅ ∨
      (2 ≤ R.card ∧
       curG.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
       ∀ v ∈ R, (1 / (3 * (D_phi : ℝ))) * (D : ℝ) ≤ (curG.degIn R v : ℝ))) ∧
    (curG.inside X).length - (curG.inside R).length ≤ 15 * (twinGraph D curG).cut Y := by
  intro X R_raw
  set G_X := compressPartGraph actVerts (curG.inside X)
  set B_loc := (Finset.range G_X.n).filter fun k => decide (G_X.degIn G_X.verts k * D_phi < D)
  let f : ℕ → ℕ := fun k => actVerts.getD k 0
  have hbound : ∀ u ∈ actVerts, u < curG.n := fun u hu => by
    have huX : u ∈ partX curG.n Y := by rw [← hactX, List.mem_toFinset]; exact hu
    exact Finset.mem_range.mp (Finset.mem_filter.mp huX).1
  have hR_verts : R_loc ⊆ Finset.range actVerts.length := by
    intro k hk
    have h1 := (Finset.mem_sdiff.mp (hR_sub hk)).1
    simpa [G_X, compressPartGraph, Cited.Graph.verts] using h1
  have hinj : Set.InjOn f (R_loc : Set ℕ) := fun i hi j hj hij =>
    pairwise_lt_getD_inj hstrict (Finset.mem_range.mp (hR_verts hi))
      (Finset.mem_range.mp (hR_verts hj)) hij
  have himg_X : R_loc.image f ⊆ X := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hk_lt := Finset.mem_range.mp (hR_verts hk)
    dsimp only [X]
    rw [← hactX, List.mem_toFinset]
    simp [f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
  let B := B_loc.image f
  have hB_verts : B_loc ⊆ Finset.range actVerts.length := fun k hk => by
    simpa [B_loc, G_X, compressPartGraph] using (Finset.mem_filter.mp hk).1
  have hBX : B ⊆ X := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hk_lt := Finset.mem_range.mp (hB_verts hk)
    dsimp only [X]
    rw [← hactX, List.mem_toFinset]
    simp [f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
  have hGX_eq : compressPartGraph actVerts (curG.inside actVerts.toFinset) = G_X := by
    simp [G_X, X, hactX]
  have hvol_lift : curG.volIn X (X \ R_loc.image f) ≤
      curG.volIn X B + 2 * (4 * D_phi + 2) * curG.cutIn X B := by
    have hGX_v := compressPartGraph_volIn hstrict hbound
      (A_loc := Finset.range actVerts.length) (S_loc := Finset.range actVerts.length \ R_loc)
      le_rfl Finset.sdiff_subset
    have hGX_B := compressPartGraph_volIn hstrict hbound
      (A_loc := Finset.range actVerts.length) (S_loc := B_loc) le_rfl hB_verts
    have hGX_cutB := compressPartGraph_cutIn hstrict hbound
      (A_loc := Finset.range actVerts.length) (S_loc := B_loc) le_rfl hB_verts
    have hsdiff := compressPartGraph_sdiff_image hstrict (A_loc := Finset.range actVerts.length)
      (S_loc := R_loc) le_rfl hR_verts
    have hverts_img : (Finset.range actVerts.length).image f = X := by
      dsimp only [X]
      simpa [f, hactX] using compressPartGraph_image_f_verts actVerts
    dsimp only at hGX_v hGX_B hGX_cutB hsdiff
    dsimp only [f] at hverts_img himg_X ⊢
    rw [hGX_eq] at hGX_v hGX_B hGX_cutB
    rw [hverts_img] at hsdiff
    rw [hsdiff, hverts_img] at hGX_v
    rw [hverts_img] at hGX_B hGX_cutB
    change G_X.volIn G_X.verts (G_X.verts \ R_loc) ≤ _ at hvol_loc
    rw [show G_X.verts = Finset.range actVerts.length by rfl] at hvol_loc
    change G_X.volIn (Finset.range actVerts.length) (Finset.range actVerts.length \ R_loc) ≤
      G_X.volIn (Finset.range actVerts.length) B_loc +
        2 * (4 * D_phi + 2) * G_X.cutIn (Finset.range actVerts.length) B_loc at hvol_loc
    rwa [hGX_v, hGX_B, hGX_cutB] at hvol_loc
  have hB_twin : ∀ b ∈ B, curG.degIn X b * D_phi < D ∧ 2 * b ∈ Y ∧ 2 * b + 1 ∉ Y := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨k, hk, rfl⟩
    have hk_lt := Finset.mem_range.mp (hB_verts hk)
    have hdeg_loc : G_X.degIn G_X.verts k * D_phi < D :=
      decide_eq_true_eq.mp (Finset.mem_filter.mp hk).2
    have hdeg_eq := compressPartGraph_degIn hstrict hbound
      (S_loc := Finset.range actVerts.length) le_rfl hk_lt
    have hverts_img : (Finset.range actVerts.length).image f = X := by
      dsimp only [X]
      simpa [f, hactX] using compressPartGraph_image_f_verts actVerts
    dsimp only at hdeg_eq
    rw [hGX_eq, hverts_img] at hdeg_eq
    change G_X.degIn (Finset.range actVerts.length) k = _ at hdeg_eq
    have hdegX : curG.degIn X (f k) * D_phi < D := by rwa [← hdeg_eq]
    have hfk_X : f k ∈ X := hBX (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    exact ⟨hdegX, (Finset.mem_filter.mp hfk_X).2, hnoBadTwin k hk_lt hdegX⟩
  have hcut_ge_B : D * B.card ≤ (twinGraph D curG).cut Y :=
    twin_cut_ge_of_mem_not_twin hV
      (fun b hb => Finset.mem_range.mp (Finset.mem_filter.mp (hBX hb)).1)
      (fun b hb => (hB_twin b hb).2.1) (fun b hb => (hB_twin b hb).2.2)
  have hvolB_Dphi : curG.volIn X B * D_phi ≤ (twinGraph D curG).cut Y := by
    calc curG.volIn X B * D_phi
        = (∑ b ∈ B, curG.degIn X b) * D_phi := rfl
      _ = ∑ b ∈ B, curG.degIn X b * D_phi := Finset.sum_mul _ _ _
      _ ≤ ∑ _b ∈ B, D := Finset.sum_le_sum fun b hb => Nat.le_of_lt (hB_twin b hb).1
      _ = B.card * D := by simp
      _ = D * B.card := Nat.mul_comm _ _
      _ ≤ (twinGraph D curG).cut Y := hcut_ge_B
  have hcutB : curG.cutIn X B ≤ curG.volIn X B := cutIn_le_volIn curG X B
  have hvolXR_le : curG.volIn X (X \ R_loc.image f) ≤ 15 * (twinGraph D curG).cut Y := by
    have h1 : curG.volIn X (X \ R_loc.image f) ≤ (2 * (4 * D_phi + 2) + 1) * curG.volIn X B := by
      nlinarith
    have h2 : (2 * (4 * D_phi + 2) + 1) ≤ 15 * D_phi := by omega
    calc curG.volIn X (X \ R_loc.image f)
        ≤ (2 * (4 * D_phi + 2) + 1) * curG.volIn X B := h1
      _ ≤ (15 * D_phi) * curG.volIn X B := Nat.mul_le_mul_right _ h2
      _ = 15 * (curG.volIn X B * D_phi) := by ring
      _ ≤ 15 * (twinGraph D curG).cut Y := Nat.mul_le_mul_left 15 hvolB_Dphi
  have hinside_img : (curG.inside X).length - (curG.inside (R_loc.image f)).length ≤
      15 * (twinGraph D curG).cut Y :=
    le_trans (inside_sub_length_le_vol hL himg_X) hvolXR_le
  by_cases hcard1 : R_loc.card ≤ 1
  · simp only [R_raw, hcard1, ↓reduceIte]
    have hcard_img : (R_loc.image f).card ≤ 1 := le_trans Finset.card_image_le hcard1
    have hnil1 : curG.inside (R_loc.image f) = [] := inside_card_le_one_eq_nil hL hcard_img
    have hnil0 : curG.inside ∅ = [] := inside_card_le_one_eq_nil hL (by simp)
    refine ⟨Finset.empty_subset X, Or.inl trivial, ?_⟩
    rw [hnil1] at hinside_img
    simpa [hnil0] using hinside_img
  · simp only [R_raw, hcard1, ↓reduceIte]
    have hcard_img : 2 ≤ (R_loc.image f).card := by
      rw [Finset.card_image_of_injOn hinj]; omega
    have hexp_img : curG.IsConductanceExpanderOn (R_loc.image f) (1 / (3 * (D_phi : ℝ))) := by
      have hiff := compressPartGraph_expander_iff (curG := curG) hstrict hbound hR_verts
        (φ := 1 / (3 * (D_phi : ℝ)))
      dsimp only at hiff
      rw [hGX_eq] at hiff
      have heq_div : (1 / (D_phi : ℝ)) / 3 = 1 / (3 * (D_phi : ℝ)) := by ring
      change G_X.IsConductanceExpanderOn R_loc ((1 / (D_phi : ℝ)) / 3) at hexpR_loc
      rw [heq_div] at hexpR_loc
      exact hiff.mp hexpR_loc
    have hdeg_img : ∀ v ∈ R_loc.image f,
        (1 / (3 * (D_phi : ℝ))) * (D : ℝ) ≤ (curG.degIn (R_loc.image f) v : ℝ) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨k, hk, rfl⟩
      have hk_lt := Finset.mem_range.mp (hR_verts hk)
      have hdeg_loc := hdegR_loc k hk
      have hdeg_eq := compressPartGraph_degIn hstrict hbound hR_verts hk_lt
      dsimp only at hdeg_eq
      rw [hGX_eq] at hdeg_eq
      change G_X.degIn R_loc k = curG.degIn (Finset.image f R_loc) (f k) at hdeg_eq
      have hdeg_R : (D + 3 * D_phi - 1) / (3 * D_phi) ≤ curG.degIn (R_loc.image f) (f k) := by
        rwa [← hdeg_eq]
      exact (one_div_three_mul_le_iff (by omega : 1 ≤ D_phi)).mpr hdeg_R
    exact ⟨himg_X, Or.inr ⟨hcard_img, hexp_img, hdeg_img⟩, hinside_img⟩


end MinCostFlow.Expander
