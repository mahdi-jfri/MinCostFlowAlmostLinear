module

public import MinCostFlow.Chain.SparseCoreTool
public import MinCostFlow.Chain.TreeChain
public import MinCostFlow.Chain.Cycles
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.Chain.EncodingSize
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algorithm 1: Dynamic Tree Chain Maintenance (`jtree.tex`, pages 20–21)

This file formalizes the data structures and procedures of **Algorithm 1** (`Initialize`,
`Rebuild(i_0)`, `Shift(i_0)`, `Update`, `FindCycle`) from `jtree.tex` (pages 20–21) over the
per-level tool `SparseCoreTool` (Lemma 5.17) and the level-`d` LSF/MWU builder `LastLevelTool`.

Faithfulness notes and departures from the paper's pseudocode:
* `Shift(i_0)` (Algorithm 1, lines 312–313) writes `bran_i` and `G_{i+1} ← 𝒮(G_i, F^{G_i}_{bran_i})`
  with `i` unbound before the loop; we read `i` as `i_0`, matching Definition 5.10 (page 20).
  Moreover, to avoid deferred amortized spanner recourse bursts across branch switches (the gap
  witnessed by `exSwitchedRecourse_counterexample` in `RebuildBounds.lean`), `Shift(i_0)` calls
  `T.restart` on the newly selected branch before re-initializing levels `> i_0`. For `i_0 = d`,
  `Shift(d)` circularly advances `lastBran`.
* Algorithm 1 omits updating level `d` (`lastLSFs`, `lastBran`) inside `Rebuild`, `Shift`, and
  `Update`, whereas Definition 5.8 / Definition 6.1 (page 26) rebuilds level `d` whenever `G_d`
  changes; our `rebuildFrom` and `Update` update level `d` via `LastLevelTool` (skipping rebuild
  in `Update` when `U^{(t)}_{G_d} = []`).
* Algorithm 1 line 324 writes the rebuild threshold as `m (γ_ℓ / k)^{i+1} / log² n` and checks it
  before `A_{G_i}.Update` without counting `|U^{(t)}_{G_i}|`. Using `γ := TP.γ_ℓ (P.M₀ ^ 2)` (so
  when `TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀` and `TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k`, every level bound satisfies
  `1 ≤ levelM TP P i ≤ P.M₀ ^ 2` and `TP.γ_ℓ/c/r (levelM TP P i) ≤ TP.γ_ℓ/c/r (P.M₀ ^ 2)`), we
  define `levelM TP P i := ⌈P.M₀ * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k)^i⌉`, matching
  line 324's threshold `M_i / (k log² N₀)` up to ceiling (with `P.M₀ ≤ levelM TP P 0` and
  `Real.log (levelM TP P i + N₀ + 2) ≤ 2 * logFactor P N₀`), and check
  `updCount idx + curU.length > SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀` before
  calling `T.update`, applying `SparseCoreTool.IsSpecRestartNoHidden` with upper bounds
  `(levelM TP P i, N₀)`. When triggered, `algorithm1_update` calls `Rebuild(idx)` on the
  already-updated `G_{idx}^{(t)}` and exits the loop (since `Rebuild(idx)` re-initializes all
  levels `≥ idx`).
* `algorithm1_findCycle` picks the off-tree edge `e ∈ E(G_0) \ E(T^𝒢)` maximizing its
  own-level core-graph key `heapCycleRatio C g ℓ e = |⟨g^{𝒞(G_i, F_i)}, a(e)⟩| / wlen_{e^G}`
  (where `i = edgeLevel e`, matching `jtree.tex` lines 331 and 494–518: "the algorithm simply
  tracks the quality of all fundamental spanner cycles using a heap and returns the best among
  them"), breaking ties by the least internal edge name (`leastArgmax`), and returning the zero
  circulation when `G_0.E ⊆ T^𝒢.E`. By repaired `lemma_7_12`, `lemma_7_13`, and `lemma_A_2_wlen`,
  the exact ratio in `G_0` of the returned cycle is at least its key, which meets the ratio bound
  of Lemma 5.11.
-/

@[expose] public section

namespace MinCostFlow.Chain

section BasicHelpers

lemma applyUpdate_isValid {G : MGraph} (hG : G.IsValid) {u : Update} (hu : G.UpdateIsValid u) :
    (G.applyUpdate u).IsValid := by
  cases u with
  | insert e a b =>
    intro f hf
    simp only [MGraph.applyUpdate, Finset.mem_insert] at hf
    rcases hf with rfl | hfG
    · simp [MGraph.applyUpdate, hu.2.1, hu.2.2]
    · have hne : f ≠ e := fun h => hu.1 (h ▸ hfG)
      simpa [MGraph.applyUpdate, Function.update_of_ne hne] using hG f hfG
  | delete e =>
    intro f hf
    simp only [MGraph.applyUpdate, Finset.mem_erase] at hf
    exact hG f hf.2
  | split v v' _ _ =>
    intro f hf
    simp only [MGraph.applyUpdate] at hf ⊢
    have hEnds := hG f hf
    refine ⟨?_, ?_⟩
    · split_ifs <;> simp [hEnds.1]
    · split_ifs <;> simp [hEnds.2]

lemma applyBatch_isValid {G : MGraph} (hG : G.IsValid) {U : List Update} (hU : G.BatchIsValid U) :
    (G.applyBatch U).IsValid := by
  induction U generalizing G with
  | nil => exact hG
  | cons u us ih => exact ih (applyUpdate_isValid hG hU.1) hU.2

lemma applyUpdate_V_subset (G : MGraph) (u : Update) : G.V ⊆ (G.applyUpdate u).V := by
  cases u with
  | insert _ _ _ => exact Finset.Subset.refl _
  | delete _ => exact Finset.Subset.refl _
  | split _ v' _ _ => exact Finset.subset_insert v' G.V

lemma applyBatch_V_subset (G : MGraph) (U : List Update) : G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.refl _
  | cons u us ih => exact Finset.Subset.trans (applyUpdate_V_subset G u) (ih (G.applyUpdate u))

lemma applyBatch_n_le (G : MGraph) (U : List Update) : G.n ≤ (G.applyBatch U).n :=
  Finset.card_le_card (applyBatch_V_subset G U)

lemma chainLen_congr_lt {C₁ C₂ : TreeChain} (ℓ : ℕ → ℝ) (idx : ℕ)
    (hG : ∀ j < idx, C₁.G j = C₂.G j)
    (hL : ∀ j < idx, C₁.activeLSF j = C₂.activeLSF j) :
    C₁.chainLen ℓ idx = C₂.chainLen ℓ idx := by
  induction idx with
  | zero => rfl
  | succ m ih =>
    have hm1 : ∀ j < m, C₁.G j = C₂.G j := fun j hj => hG j (Nat.lt_succ_of_lt hj)
    have hm2 : ∀ j < m, C₁.activeLSF j = C₂.activeLSF j := fun j hj => hL j (Nat.lt_succ_of_lt hj)
    simp only [TreeChain.chainLen, ih hm1 hm2, hL m (Nat.lt_succ_self m)]

lemma chainGrad_congr_lt {C₁ C₂ : TreeChain} (g : ℕ → ℝ) (idx : ℕ)
    (hG : ∀ j < idx, C₁.G j = C₂.G j)
    (hL : ∀ j < idx, C₁.activeLSF j = C₂.activeLSF j) :
    C₁.chainGrad g idx = C₂.chainGrad g idx := by
  induction idx with
  | zero => rfl
  | succ m ih =>
    have hm1 : ∀ j < m, C₁.G j = C₂.G j := fun j hj => hG j (Nat.lt_succ_of_lt hj)
    have hm2 : ∀ j < m, C₁.activeLSF j = C₂.activeLSF j := fun j hj => hL j (Nat.lt_succ_of_lt hj)
    simp only [TreeChain.chainGrad, ih hm1 hm2, hG m (Nat.lt_succ_self m), hL m (Nat.lt_succ_self m)]

lemma mem_E_of_mem_applyBatch {G : MGraph} {U : List Update} {e : ℕ}
    (he : e ∈ (G.applyBatch U).E) (hnot : ∀ u ∈ U, ¬ u.Inserts e) : e ∈ G.E := by
  induction U generalizing G with
  | nil => exact he
  | cons u us ih =>
    have he1 : e ∈ (G.applyUpdate u).E := ih he (fun w hw => hnot w (List.mem_cons_of_mem _ hw))
    have hnu : ¬ u.Inserts e := hnot u List.mem_cons_self
    cases u with
    | insert e' a b =>
      simp only [MGraph.applyUpdate, Finset.mem_insert] at he1
      rcases he1 with rfl | heG
      · exact absurd rfl hnu
      · exact heG
    | delete e' =>
      simp only [MGraph.applyUpdate, Finset.mem_erase] at he1
      exact he1.2
    | split _ _ _ _ =>
      simpa [MGraph.applyUpdate] using he1

lemma LSF.Holds.congr_len {L : LSF} {G : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ} {σ : ℝ}
    (hL : L.Holds G ℓ₁ σ) (heq : ∀ e ∈ G.E, ℓ₁ e = ℓ₂ e) : L.Holds G ℓ₂ σ := by
  refine ⟨hL.1, hL.2.1, hL.2.2.1, fun e he => ?_⟩
  have hSub := hL.2.1.2.2.2.2
  have hwalkEq : ∀ u v : ℕ,
      walkLength ℓ₁ (MGraph.forestPath L.F.F u v) =
        walkLength ℓ₂ (MGraph.forestPath L.F.F u v) := by
    intro u v
    by_cases hc : L.F.F.Connected u v
    · have hW := MGraph.isWalk_forestPath hc
      unfold walkLength
      refine Finset.sum_congr rfl fun f hf => ?_
      have hfG : f ∈ G.E := by
        rw [walkEdges, List.mem_toFinset, List.mem_map] at hf
        obtain ⟨x, hx, rfl⟩ := hf
        exact hSub.2.1 (MGraph.isWalk_edges_mem hW x hx)
      rw [heq f hfG]
    · have hemp : MGraph.forestPath L.F.F u v = [] := by
        classical
        unfold MGraph.forestPath
        rw [dite_eq_right_iff]
        intro ⟨P, hP⟩; exact absurd ⟨P, hP.1⟩ hc
      simp [hemp, walkLength_nil]
  have hstr : L.F.stretch G ℓ₂ e = L.F.stretch G ℓ₁ e := by
    unfold RootedForest.stretch
    dsimp only
    rw [heq e he, hwalkEq (G.tail e) (G.head e),
      hwalkEq (G.tail e) (L.F.root (G.tail e)), hwalkEq (G.head e) (L.F.root (G.head e))]
  rw [hstr]
  exact hL.2.2.2 e he

lemma LSF.Holds.mono_σ {L : LSF} {G : MGraph} {ℓ : ℕ → ℝ} {σ₁ σ₂ : ℝ}
    (hL : L.Holds G ℓ σ₁) (hσ : σ₁ ≤ σ₂) : L.Holds G ℓ σ₂ :=
  ⟨hL.1, hL.2.1, hL.2.2.1, fun e he => ⟨(hL.2.2.2 e he).1, le_trans (hL.2.2.2 e he).2 hσ⟩⟩

lemma isSparsifiedCoreGraphAt_mono {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ}
    {k γ_ℓ₁ γ_ℓ₂ γ_c₁ γ_c₂ : ℝ} {m₁ m₂ : ℕ} {S : MGraph} {emb : Embedding}
    (hS : IsSparsifiedCoreGraphAt G L ℓ k γ_ℓ₁ γ_c₁ m₁ S emb)
    (hk : 0 < k) (hγ₁ : 0 ≤ γ_ℓ₁) (hℓ : γ_ℓ₁ ≤ γ_ℓ₂) (hc : γ_c₁ ≤ γ_c₂) (hm : m₁ ≤ m₂) :
    IsSparsifiedCoreGraphAt G L ℓ k γ_ℓ₂ γ_c₂ m₂ S emb := by
  rcases hS with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, h2, h3, le_trans h4 hℓ, ?_, ?_⟩
  · exact le_trans h5 (mul_le_mul_of_nonneg_left hc hk.le)
  · refine le_trans h6 ?_
    have hmR : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm
    exact div_le_div_of_nonneg_right
      (mul_le_mul hmR hℓ hγ₁ (Nat.cast_nonneg _)) hk.le

lemma isSparsifiedCoreGraph_mono {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ}
    {k γ_ℓ₁ γ_ℓ₂ γ_c₁ γ_c₂ : ℝ} {S : MGraph} {emb : Embedding}
    (hS : IsSparsifiedCoreGraph G L ℓ k γ_ℓ₁ γ_c₁ S emb)
    (hk : 0 < k) (hℓ : γ_ℓ₁ ≤ γ_ℓ₂) (hc : γ_c₁ ≤ γ_c₂) :
    IsSparsifiedCoreGraph G L ℓ k γ_ℓ₂ γ_c₂ S emb := by
  rcases hS with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, h2, h3, le_trans h4 hℓ, ?_, ?_⟩
  · exact le_trans h5 (mul_le_mul_of_nonneg_left hc hk.le)
  · refine le_trans h6 ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hℓ (Nat.cast_nonneg _)) hk.le

lemma SparseCoreTool.run_congr (T : SparseCoreTool) (k : ℕ) {D₁ D₂ : DynamicInstance}
    (t : ℕ) (hG0 : D₁.G 0 = D₂.G 0) (hℓ0 : D₁.ℓ 0 = D₂.ℓ 0) (hg0 : D₁.g 0 = D₂.g 0)
    (hstep : ∀ s, 1 ≤ s → s ≤ t → D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s) :
    T.run k D₁ t = T.run k D₂ t := by
  induction t with
  | zero => simp [SparseCoreTool.run, SparseCoreTool.runAt, hG0, hℓ0, hg0]
  | succ m ih =>
    have ih' := ih fun s hs1 hsm => hstep s hs1 (Nat.le_succ_of_le hsm)
    have hm := hstep (m + 1) (Nat.succ_pos m) (le_refl _)
    simp only [SparseCoreTool.run, SparseCoreTool.runAt, ih', hm.1, hm.2.1, hm.2.2]

end BasicHelpers

section TreeChanges

/-- Explicit edge insertion or deletion on `T^𝒢` (Lemma 5.11, page 20). -/
inductive TreeChange
  | insert (e : ℕ)
  | delete (e : ℕ)
  deriving DecidableEq, Repr

/-- Apply a list of edge changes to an edge finset. -/
def applyTreeChanges (E : Finset ℕ) (cs : List TreeChange) : Finset ℕ :=
  cs.foldl (fun S c => match c with | .insert e => insert e S | .delete e => S.erase e) E

/-- Explicit symmetric-difference list transforming `oldE` into `newE`. -/
noncomputable def diffTreeChanges (oldE newE : Finset ℕ) : List TreeChange :=
  (oldE \ newE).toList.map TreeChange.delete ++ (newE \ oldE).toList.map TreeChange.insert

private lemma applyTreeChanges_deletes (S : Finset ℕ) (ds : List ℕ) :
    applyTreeChanges S (ds.map TreeChange.delete) = S \ ds.toFinset := by
  induction ds generalizing S with
  | nil => simp [applyTreeChanges]
  | cons x xs ih =>
    simp only [List.map_cons, applyTreeChanges, List.foldl_cons] at ih ⊢
    rw [ih (S.erase x)]
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons, Finset.mem_insert, not_or]
    tauto

private lemma applyTreeChanges_inserts (S : Finset ℕ) (is : List ℕ) :
    applyTreeChanges S (is.map TreeChange.insert) = S ∪ is.toFinset := by
  induction is generalizing S with
  | nil => simp [applyTreeChanges]
  | cons x xs ih =>
    simp only [List.map_cons, applyTreeChanges, List.foldl_cons] at ih ⊢
    rw [ih (insert x S)]
    ext y
    simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
    tauto

lemma applyTreeChanges_diffTreeChanges (oldE newE : Finset ℕ) :
    applyTreeChanges oldE (diffTreeChanges oldE newE) = newE := by
  unfold diffTreeChanges
  have h1 : applyTreeChanges oldE
      ((oldE \ newE).toList.map TreeChange.delete ++
        (newE \ oldE).toList.map TreeChange.insert) =
      applyTreeChanges (applyTreeChanges oldE ((oldE \ newE).toList.map TreeChange.delete))
        ((newE \ oldE).toList.map TreeChange.insert) :=
    List.foldl_append
  rw [h1, applyTreeChanges_deletes, applyTreeChanges_inserts]
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, Finset.mem_toList]
  tauto

lemma diffTreeChanges_length (oldE newE : Finset ℕ) :
    (diffTreeChanges oldE newE).length = (oldE \ newE).card + (newE \ oldE).card := by
  unfold diffTreeChanges
  simp only [List.length_append, List.length_map, Finset.length_toList]

lemma diffTreeChanges_length_le_add (oldE newE : Finset ℕ) :
    (diffTreeChanges oldE newE).length ≤ oldE.card + newE.card := by
  rw [diffTreeChanges_length]
  exact add_le_add (Finset.card_le_card Finset.sdiff_subset) (Finset.card_le_card Finset.sdiff_subset)

lemma diffTreeChanges_length_of_subset {oldE newE : Finset ℕ} (hsub : newE ⊆ oldE) :
    (diffTreeChanges oldE newE).length = oldE.card - newE.card := by
  rw [diffTreeChanges_length, Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty,
    add_zero, Finset.card_sdiff_of_subset hsub]

end TreeChanges

section Algorithm1Defs

/-- Static configuration parameters for Algorithm 1 (`jtree.tex`, pages 20–21). -/
structure ChainParams where
  /-- Number of levels `d ≥ 1`. -/
  d : ℕ
  /-- Branching/reduction factor `k ≥ 1` (`k ≈ M₀^{1/d}`). -/
  k : ℕ
  /-- Upper bound `M₀ ≥ 1` on `|(G_0^{(t)}).E|` across the run. -/
  M₀ : ℕ
  hd : 0 < d
  hk : 0 < k
  hM₀ : 1 ≤ M₀
  hk_pow : M₀ ≤ k ^ d
  hk_upper : (k : ℝ) ≤ 2 * (M₀ : ℝ) ^ (1 / (d : ℝ))

/-- Canonical `ChainParams` taking `k := ⌈M₀^{1/d}⌉`. -/
noncomputable def mkChainParams (d M₀ : ℕ) (hd : 0 < d) (hM₀ : 1 ≤ M₀) : ChainParams where
  d := d
  k := Nat.ceil ((M₀ : ℝ) ^ (1 / (d : ℝ)))
  M₀ := M₀
  hd := hd
  hk := by
    have h1 : (1 : ℝ) ≤ (M₀ : ℝ) ^ (1 / (d : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast hM₀) (by positivity)
    exact Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one h1)
  hM₀ := hM₀
  hk_pow := by
    have hM0_nonneg : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hx : (M₀ : ℝ) ^ (1 / (d : ℝ)) ≤ Nat.ceil ((M₀ : ℝ) ^ (1 / (d : ℝ))) := Nat.le_ceil _
    have hrpow : ((M₀ : ℝ) ^ (1 / (d : ℝ))) ^ d = (M₀ : ℝ) := by
      rw [← Real.rpow_natCast ((M₀ : ℝ) ^ (1 / (d : ℝ))) d,
        ← Real.rpow_mul hM0_nonneg, one_div_mul_cancel hd_pos.ne', Real.rpow_one]
    have hpow : (M₀ : ℝ) ≤ (Nat.ceil ((M₀ : ℝ) ^ (1 / (d : ℝ))) : ℝ) ^ d := by
      calc
        (M₀ : ℝ) = ((M₀ : ℝ) ^ (1 / (d : ℝ))) ^ d := hrpow.symm
        _ ≤ (Nat.ceil ((M₀ : ℝ) ^ (1 / (d : ℝ))) : ℝ) ^ d :=
          pow_le_pow_left₀ (Real.rpow_nonneg hM0_nonneg _) hx d
    exact_mod_cast hpow
  hk_upper := by
    have h1 : (1 : ℝ) ≤ (M₀ : ℝ) ^ (1 / (d : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast hM₀) (by positivity)
    have hlt : (Nat.ceil ((M₀ : ℝ) ^ (1 / (d : ℝ))) : ℝ) < (M₀ : ℝ) ^ (1 / (d : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (le_trans zero_le_one h1)
    linarith

/-- Level-`i` edge upper bound `M_i = ⌈M₀ (γ_ℓ(M₀) / k)^i⌉` (`jtree.tex` page 24, line 469).
With `γ = TP.γ_ℓ (P.M₀ ^ 2)` satisfying `γ ≤ P.M₀` and `γ ≤ P.k`, we have
`1 ≤ levelM TP P i ≤ P.M₀ ^ 2`, `P.M₀ ≤ levelM TP P 0`, and
`(P.M₀ : ℝ) / (P.k : ℝ) ^ i ≤ (P.M₀ : ℝ) * (γ / (P.k : ℝ)) ^ i ≤ (levelM TP P i : ℝ)`. -/
noncomputable def levelM (TP : SparseCoreParams) (P : ChainParams) (i : ℕ) : ℕ :=
  Nat.ceil ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i)

lemma one_le_levelM {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams) (i : ℕ) :
    1 ≤ levelM TP P i := by
  have hM0 : (0 : ℝ) < P.M₀ := by exact_mod_cast P.hM₀
  have hγ : 0 < TP.γ_ℓ (P.M₀ ^ 2) := lt_of_lt_of_le zero_lt_one (hTP.2.2.1 (P.M₀ ^ 2))
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hpos : 0 < (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i := by
    positivity
  exact Nat.ceil_pos.mpr hpos

lemma rpow_le_levelM (TP : SparseCoreParams) (P : ChainParams) (i : ℕ) :
    (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i ≤
      (levelM TP P i : ℝ) :=
  Nat.le_ceil _

lemma M₀_le_levelM_zero {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams) :
    P.M₀ ≤ levelM TP P 0 := by
  have hγ1 : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.1 (P.M₀ ^ 2)
  have hMnn : (0 : ℝ) ≤ P.M₀ := Nat.cast_nonneg _
  have hle : (P.M₀ : ℝ) ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) :=
    le_mul_of_one_le_right hMnn hγ1
  have hle' : (P.M₀ : ℝ) ≤ (levelM TP P 0 : ℝ) :=
    le_trans hle (by simpa using rpow_le_levelM TP P 0)
  exact_mod_cast hle'

lemma levelM_le_sq {TP : SparseCoreParams} (hTP : TP.Valid) {P : ChainParams}
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (i : ℕ) :
    levelM TP P i ≤ P.M₀ ^ 2 := by
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγnn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) :=
    div_nonneg (le_trans zero_le_one (hTP.2.2.1 (P.M₀ ^ 2))) hk.le
  have hγle : TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) ≤ 1 := (div_le_one hk).mpr hγk
  have hpow : (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i ≤ 1 := pow_le_one₀ hγnn hγle
  have hle : (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i ≤
      ((P.M₀ ^ 2 : ℕ) : ℝ) := by
    push_cast
    calc
      (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i
          ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (hTP.2.2.1 (P.M₀ ^ 2))))
      _ = (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := mul_one _
      _ ≤ (P.M₀ : ℝ) * (P.M₀ : ℝ) := mul_le_mul_of_nonneg_left hγM₀ (Nat.cast_nonneg _)
      _ = (P.M₀ : ℝ) ^ 2 := (sq _).symm
  exact Nat.ceil_le.mpr hle

lemma gamma_div_pow_le_levelM {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams)
    (i : ℕ) :
    (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i ≤ (levelM TP P i : ℝ) := by
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγ1 : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.1 (P.M₀ ^ 2)
  have hnn : 0 ≤ (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i := by
    have hγnn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one hγ1
    positivity
  have hle : (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i ≤
      (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i := by
    calc
      (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i
          = 1 * ((P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i) := (one_mul _).symm
      _ ≤ TP.γ_ℓ (P.M₀ ^ 2) * ((P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i) :=
        mul_le_mul_of_nonneg_right hγ1 hnn
      _ = (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i := by ring
  exact le_trans hle (rpow_le_levelM TP P i)

lemma levelM_lt_add_one {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams) (i : ℕ) :
    (levelM TP P i : ℝ) <
      (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i + 1 := by
  have hγnn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.1 (P.M₀ ^ 2))
  have hnn : 0 ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i := by
    positivity
  exact Nat.ceil_lt_add_one hnn

/-- One-step ceiling contraction for `levelM`: any graph with `m_next ≤ levelM i * γ_ℓ / k`
satisfies `m_next ≤ levelM (i + 1)` as natural numbers (with zero `+ 1` drift across levels). -/
lemma levelM_step_nat {TP : SparseCoreParams} (hTP : TP.Valid) {P : ChainParams}
    (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) {i m_next : ℕ}
    (hm : (m_next : ℝ) ≤ (levelM TP P i : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) :
    m_next ≤ levelM TP P (i + 1) := by
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγ_pos : 0 < TP.γ_ℓ (P.M₀ ^ 2) := lt_of_lt_of_le zero_lt_one (hTP.2.2.1 (P.M₀ ^ 2))
  have hrat_pos : 0 < TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) := div_pos hγ_pos hk_pos
  have hrat_le : TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) ≤ 1 := (div_le_one hk_pos).mpr hγk
  have hlt := levelM_lt_add_one hTP P i
  have hmul : (levelM TP P i : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) <
      ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i + 1) *
        (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) :=
    mul_lt_mul_of_pos_right hlt hrat_pos
  have hrhs_eq :
      ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i + 1) *
          (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) =
        (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ (i + 1) +
          TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) := by
    rw [pow_succ]; ring
  have hnext := rpow_le_levelM TP P (i + 1)
  have hstrict : (m_next : ℝ) < ((levelM TP P (i + 1) + 1 : ℕ) : ℝ) := by
    push_cast
    have hm' : (m_next : ℝ) ≤ (levelM TP P i : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) := by
      linarith [show (levelM TP P i : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) =
        (levelM TP P i : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) by ring]
    linarith
  exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp hstrict)

lemma div_pow_le_levelM {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams) (i : ℕ) :
    (P.M₀ : ℝ) / (P.k : ℝ) ^ i ≤ (levelM TP P i : ℝ) := by
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγ1 : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.1 (P.M₀ ^ 2)
  have h1 : (1 / (P.k : ℝ)) ^ i ≤ (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i := by
    gcongr
  have hle : (P.M₀ : ℝ) / (P.k : ℝ) ^ i ≤
      (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i := by
    calc
      (P.M₀ : ℝ) / (P.k : ℝ) ^ i = (P.M₀ : ℝ) * (1 / (P.k : ℝ)) ^ i := by
        rw [div_pow, one_pow]; ring
      _ ≤ (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  exact le_trans hle (gamma_div_pow_le_levelM hTP P i)

/-- State of Algorithm 1 (`jtree.tex`, pages 20–21) together with exact runtime, tree-update,
and received/forwarded update bookkeeping counters for Lemma 5.11 and Theorem 5.1. -/
structure ChainState (T : SparseCoreRestartTool) (P : ChainParams) where
  /-- Current graphs `G_0, …, G_d`. -/
  G : ℕ → MGraph
  /-- Active `SparseCoreRestartTool` state at each level `i < P.d`. -/
  scState : ℕ → T.State
  /-- Number of `T.restart` calls on `scState i` during its current initialized lifetime (`i < P.d`). -/
  curRestarts : ℕ → ℕ
  /-- Active branch index `bran_i < P.k` at each level `i < P.d`. -/
  bran : ℕ → ℕ
  /-- Total update count fed to `scState i` since its last initialization (`i < P.d`). -/
  updCount : ℕ → ℕ
  /-- Cumulative update batch length received at level `i` across the whole run (`i < P.d`). -/
  recUpdates : ℕ → ℕ
  /-- Cumulative update batch length forwarded out of `scState i` during its current lifetime (`i < P.d`). -/
  curFwd : ℕ → ℕ
  /-- Number of LSFs at level `d`. -/
  lastK : ℕ
  /-- LSFs at level `d`. -/
  lastLSFs : ℕ → LSF
  /-- Active branch index at level `d`. -/
  lastBran : ℕ
  /-- Current edge lengths on `G_0`. -/
  ℓ : ℕ → ℝ
  /-- Current edge gradients on `G_0`. -/
  g : ℕ → ℝ
  /-- Pass counters `passes_i` (initialized to `0` by `Initialize`). -/
  passes : ℕ → ℕ
  /-- Cumulative invocations of `Shift(i)` (`s_i`). -/
  shiftCount : ℕ → ℕ
  /-- Cumulative invocations of `Rebuild(i)` (`r_i`). -/
  rebuildCount : ℕ → ℕ
  /-- Cost of all retired `SparseCoreTool` lifetimes, retired `LastLevelTool` builds, and
  retired `batchEnc` operations. -/
  closedRuntime : ℕ
  /-- Cumulative `LastLevelTool` rebuilds triggered by nonempty updates at level `d` within the
  current lifetime of `scState (P.d - 1)`. -/
  curLastRebuilds : ℕ
  /-- Cumulative cost of `LastLevelTool` rebuilds triggered by nonempty updates at level `d` within
  the current lifetime of `scState (P.d - 1)`. -/
  curLastCost : ℕ
  /-- Cumulative `batchEnc` within the current active branch phase at level `i < P.d` (`curEnc 0`
  tracks `G_0.batchEnc`, and `curEnc (i + 1)` tracks `G_{i+1}.batchEnc`). -/
  curEnc : ℕ → ℕ
  /-- Cumulative `TreeChange`s emitted by closed lifetimes/rebuilds/shifts. -/
  closedTreeUpdates : ℕ
  /-- Decremental edge deletions from `F_i` during the current active branch phase (`i < P.d`). -/
  curDecUpdates : ℕ → ℕ
  /-- Edge changes to `F_d` from nonempty level-`d` updates within the current lifetime of
  `scState (P.d - 1)`. -/
  curLastTreeUpdates : ℕ
  /-- Per-level edge-count upper bound passed to `T.init` at level `i`. -/
  lvlM : ℕ → ℕ
  /-- Vertex-count upper bound passed to `T.init` at every level. -/
  N₀ : ℕ

/-- Extract the underlying static `TreeChain` from a `ChainState`. -/
def ChainState.toTreeChain {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) : TreeChain where
  d := P.d
  k := P.k
  G := st.G
  lsfs := fun i => T.lsfs (st.scState i)
  bran := st.bran
  S := fun i => T.S (st.scState i)
  emb := fun i => T.emb (st.scState i)
  lastK := st.lastK
  lastLSFs := st.lastLSFs
  lastBran := st.lastBran

/-- Total runtime accumulated up to state `st`: retired runtime plus active-lifetime costs. -/
def ChainState.totalRuntime {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) : ℕ :=
  st.closedRuntime +
    (Finset.range P.d).sum (fun i => T.cost (st.scState i) + st.curEnc i) +
    st.curLastCost

/-- Total edge updates to `T^𝒢` accumulated up to state `st`. -/
def ChainState.totalTreeUpdates {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) : ℕ :=
  st.closedTreeUpdates +
    (Finset.range P.d).sum (fun i => st.curDecUpdates i) +
    st.curLastTreeUpdates

/-- Recursive suffix builder: given `G, scState, bran, …` already fixed up to `idx`, initializes
levels `idx, idx + 1, …, P.d - 1` and returns the updated state arrays plus level-`d` LSF/MWU. -/
noncomputable def rebuildSuffix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    (rem idx : ℕ) →
      (ℕ → MGraph) → (ℕ → T.State) → (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) →
      (ℕ → MGraph) × (ℕ → T.State) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) ×
        (ℕ × (ℕ → LSF)) × ℕ
  | 0, idx, G, sc, bran, upd, cEnc, cDec, cFwd =>
    let Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let ℓd := Cpartial.chainLen ℓ₀ idx
    (G, sc, bran, upd, cEnc, cDec, cFwd, L.build (G idx) ℓd, L.cost (G idx))
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd =>
    let Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let ℓi := Cpartial.chainLen ℓ₀ idx
    let gi := Cpartial.chainGrad g₀ idx
    let Gi := G idx
    let sc_i := T.init P.k (lvlM idx) N₀ Gi ℓi gi
    let Gi1 := T.S sc_i 0
    let G' := fun j => if j = idx + 1 then Gi1 else G j
    let sc' := fun j => if j = idx then sc_i else sc j
    let bran' := fun j => if j = idx then 0 else bran j
    let upd' := fun j => if j = idx then 0 else upd j
    let cEnc' := fun j => if j = idx then 0 else cEnc j
    let cDec' := fun j => if j = idx then 0 else cDec j
    let cFwd' := fun j => if j = idx then 0 else cFwd j
    rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) G' sc' bran' upd' cEnc' cDec' cFwd'

/-- **Algorithm 1 `Initialize(G^{(0)}, ℓ, g)`** (`jtree.tex`, page 20): initializes `G_0 ← G^{(0)}`,
`passes_i ← 0`, builds all levels `0, …, d` via `rebuildSuffix`, and emits initial `T^𝒢` edge
insertions. -/
noncomputable def algorithm1_initialize (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    ChainState T P × List TreeChange :=
  let dummySc := T.init P.k (lvlM 0) N₀ G₀ ℓ₀ g₀
  let (G', sc', bran', upd', cEnc', cDec', cFwd', lastRes, lastCost) :=
    rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ P.d 0
      (fun _ => G₀) (fun _ => dummySc) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) (fun _ => 0)
  let st : ChainState T P :=
    { G := G'
      scState := sc'
      curRestarts := fun _ => 0
      bran := bran'
      updCount := upd'
      recUpdates := fun _ => 0
      curFwd := cFwd'
      lastK := lastRes.1
      lastLSFs := lastRes.2
      lastBran := 0
      ℓ := ℓ₀
      g := g₀
      passes := fun _ => 0
      shiftCount := fun _ => 0
      rebuildCount := fun _ => 0
      closedRuntime := 0
      curLastRebuilds := 0
      curLastCost := lastCost
      curEnc := cEnc'
      closedTreeUpdates := 0
      curDecUpdates := cDec'
      curLastTreeUpdates := 0
      lvlM := lvlM
      N₀ := N₀ }
  let changes := diffTreeChanges ∅ st.toTreeChain.chainTree.E
  let st' := { st with closedTreeUpdates := changes.length }
  (st', changes)

/-- **Algorithm 1 `Rebuild(i_0)`** (`jtree.tex`, page 20): re-initializes levels `i_0, …, d - 1`
(and level `d`) starting from `Gnew` at level `i_0`, retiring active costs of levels `≥ i_0` and
emitting the `TreeChange`s on `T^𝒢`. Note: when called directly with `i_0 < P.d`, uses `Gnew` as
`G_{i_0}`; when `i_0 = P.d`, rebuilds level `d`. -/
noncomputable def algorithm1_rebuild (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) (Gnew : MGraph)
    (extraEnc : ℕ := 0) : ChainState T P × List TreeChange :=
  if _hi : i₀ < P.d then
    let G0 := fun j => if j = i₀ then Gnew else st.G j
    let (G', sc', bran', upd', cEnc', cDec', cFwd', lastRes, lastCost) :=
      rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
        G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
    let retiredTool := (Finset.Ico i₀ P.d).sum fun j => T.cost (st.scState j) + st.curEnc j
    let retiredDec := (Finset.Ico i₀ P.d).sum fun j => st.curDecUpdates j
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        G := G'
        scState := sc'
        curRestarts := fun j => if i₀ ≤ j ∧ j < P.d then 0 else st.curRestarts j
        bran := bran'
        updCount := upd'
        curFwd := cFwd'
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        rebuildCount := fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j
        closedRuntime := st.closedRuntime + retiredTool + st.curLastCost + extraEnc
        curLastRebuilds := 0
        curLastCost := lastCost
        curEnc := cEnc'
        closedTreeUpdates := st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates
        curDecUpdates := cDec'
        curLastTreeUpdates := 0 }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)
  else
    -- `i₀ = P.d`: rebuild level `d` only
    let ℓd := st.toTreeChain.chainLen st.ℓ P.d
    let lastRes := L.build Gnew ℓd
    let lastCost := L.cost Gnew
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        G := fun j => if j = P.d then Gnew else st.G j
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        rebuildCount := fun j => if j = P.d then st.rebuildCount P.d + 1 else st.rebuildCount j
        closedRuntime := st.closedRuntime + st.curLastCost + extraEnc
        curLastRebuilds := 0
        curLastCost := lastCost
        closedTreeUpdates := st.closedTreeUpdates + st.curLastTreeUpdates
        curLastTreeUpdates := 0 }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)

/-- **Algorithm 1 `Shift(i_0)`** (`jtree.tex`, page 20): increments `bran_{i_0} ← (bran_{i_0} + 1) % k`,
restarts level `i_0`'s core tool on `newBran` via `T.restart`,
sets `G_{i_0+1} ← 𝒮(G_{i_0}, F^{G_{i_0}}_{bran_{i_0}})`, and re-initializes levels `i_0 + 1, …, d`.
For `i_0 = P.d`, advances `lastBran`. -/
noncomputable def algorithm1_shift (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) : ChainState T P × List TreeChange :=
  if _hi : i₀ < P.d then
    let newBran := (st.bran i₀ + 1) % P.k
    let sc_i0 := T.restart (st.scState i₀) newBran
    let Gnext := T.S sc_i0 newBran
    let G0 := fun j => if j = i₀ + 1 then Gnext else st.G j
    let sc0 := fun j => if j = i₀ then sc_i0 else st.scState j
    let bran0 := fun j => if j = i₀ then newBran else st.bran j
    let cDec0 := fun j => if j = i₀ then 0 else st.curDecUpdates j
    let cEnc0 := fun j => if j = i₀ + 1 then 0 else st.curEnc j
    let (G', sc', bran', upd', cEnc', cDec', cFwd', lastRes, lastCost) :=
      rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
        G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd
    let retiredTool := (Finset.Ico (i₀ + 1) P.d).sum fun j => T.cost (st.scState j) + st.curEnc j
    let retiredDec := (Finset.Ico i₀ P.d).sum fun j => st.curDecUpdates j
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        G := G'
        scState := sc'
        curRestarts := fun j =>
          if j = i₀ then st.curRestarts i₀ + 1
          else if i₀ + 1 ≤ j ∧ j < P.d then 0
          else st.curRestarts j
        bran := bran'
        updCount := upd'
        curFwd := cFwd'
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        shiftCount := fun j => if j = i₀ then st.shiftCount i₀ + 1 else st.shiftCount j
        closedRuntime := st.closedRuntime + retiredTool + st.curLastCost
        curLastRebuilds := 0
        curLastCost := lastCost
        curEnc := cEnc'
        closedTreeUpdates := st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates
        curDecUpdates := cDec'
        curLastTreeUpdates := 0 }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)
  else
    let newLastBran := (st.lastBran + 1) % st.lastK
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        lastBran := newLastBran
        shiftCount := fun j => if j = P.d then st.shiftCount P.d + 1 else st.shiftCount j }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)

/-- Integer rebuild threshold at level `i` of Algorithm 1 (page 21):
`⌊M₀ / (k^{i+1} · ⌈log₂(N₀ + 2)⌉²)⌋`.
It stays within the paper's real update budget `M_i / (k log² N₀)` for every valid
sparse-core parameter `TP` (since `M₀ / k^i ≤ M_i` and `log(N₀ + 2) ≤ ⌈log₂(N₀ + 2)⌉`),
and its trigger count `intRebuildThreshold P N₀ i + 1` is at least one sixteenth of
`M₀ / (k^{i+1} · (logFactor P N₀)²)`. On the Word RAM it is computed by iterative
integer division (`t₀ = (M₀ / b²) / k`, `t_{i+1} = t_i / k`) with all values `≤ M₀`. -/
def intRebuildThreshold (P : ChainParams) (N₀ i : ℕ) : ℕ :=
  P.M₀ / (P.k ^ (i + 1) * Nat.clog 2 (N₀ + 2) ^ 2)

lemma intRebuildThreshold_zero_eq (P : ChainParams) (N₀ : ℕ) :
    intRebuildThreshold P N₀ 0 = (P.M₀ / Nat.clog 2 (N₀ + 2) ^ 2) / P.k := by
  unfold intRebuildThreshold
  rw [Nat.div_div_eq_div_mul, pow_one, Nat.mul_comm]

lemma intRebuildThreshold_succ_eq (P : ChainParams) (N₀ i : ℕ) :
    intRebuildThreshold P N₀ (i + 1) = intRebuildThreshold P N₀ i / P.k := by
  unfold intRebuildThreshold
  rw [Nat.div_div_eq_div_mul]
  congr 1
  ring

/-- Recursive level-by-level update loop for **Algorithm 1 `Update(U^{(t)}, g^{(t)}, ℓ^{(t)})`**.
At level `idx`: if `intRebuildThreshold P N₀ idx < updCount idx + curU.length`,
calls `algorithm1_rebuild` from `idx` and stops; otherwise invokes `T.update`, forwards the
active branch batch `U_{S, bran idx}`, and proceeds to `idx + 1`. -/
noncomputable def updateLoop (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    (rem idx : ℕ) → (st : ChainState T P) → (curG : MGraph) → (curU : List Update) → (curEncAcc : ℕ) →
      ChainState T P × List TreeChange
  | 0, _, st, curG, curU, _ =>
    if curU = [] then
      let st' := { st with G := fun j => if j = P.d then curG else st.G j, ℓ := ℓ', g := g' }
      (st', [])
    else
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }
      let ℓd := Cpartial.chainLen ℓ' P.d
      let lastRes := L.build curG ℓd
      let lastCost := L.cost curG
      let oldFdE := (st.lastLSFs st.lastBran).F.F.E
      let newFdE := (lastRes.2 0).F.F.E
      let fdChanges := diffTreeChanges oldFdE newFdE
      let st' : ChainState T P :=
        { st with
          G := fun j => if j = P.d then curG else st.G j
          lastK := lastRes.1
          lastLSFs := lastRes.2
          lastBran := 0
          ℓ := ℓ'
          g := g'
          curLastRebuilds := st.curLastRebuilds + 1
          curLastCost := st.curLastCost + lastCost
          curLastTreeUpdates := st.curLastTreeUpdates + fdChanges.length }
      (st', fdChanges)
  | rem + 1, idx, st, curG, curU, curEncStep =>
    if intRebuildThreshold P N₀ idx < st.updCount idx + curU.length then
      let stWithLG := { st with ℓ := ℓ', g := g' }
      algorithm1_rebuild T L P stWithLG idx curG curEncStep
    else
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let (sc', U_S) := T.update (st.scState idx) curU ℓi gi
      let oldFiE := (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
      let newFiE := (T.lsfs sc' (st.bran idx)).F.F.E
      let fiChanges := diffTreeChanges oldFiE newFiE
      let nextG := T.S sc' (st.bran idx)
      let nextU := U_S (st.bran idx)
      let nextEnc := (st.G (idx + 1)).batchEnc nextU
      let stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEncStep
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      let (stEnd, restChanges) := updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) stNext nextG nextU 0
      (stEnd, fiChanges ++ restChanges)

/-- **Algorithm 1 `Update(U^{(t)}, g^{(t)}, ℓ^{(t)})`** (`jtree.tex`, page 21): applies `U^{(t)}`
to `G_0`, propagates updates through levels `0, …, d - 1` (rebuilding whenever a level would exceed
`M_i / (k log² N₀)`), updates level `d` if `U^{(t)}_{G_d}` is nonempty, and returns the updated state
and exact `TreeChange` list for `T^𝒢`. -/
noncomputable def algorithm1_update (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) :
    ChainState T P × List TreeChange :=
  let oldE := st.toTreeChain.chainTree.E
  let G₀' := (st.G 0).applyBatch U
  let enc₀ := (st.G 0).batchEnc U
  let st0 : ChainState T P :=
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
  let (st', _) := updateLoop T L TP P N₀ ℓ' g' P.d 0 st0 G₀' U enc₀
  (st', diffTreeChanges oldE st'.toTreeChain.chainTree.E)

/-- The least element of `S` among those at which `f` takes its largest value on `S`. It breaks
ties between maximizers by the least name, so that a program can compute it. -/
noncomputable def leastArgmax (S : Finset ℕ) (f : ℕ → ℝ) (hne : S.Nonempty) : ℕ :=
  open Classical in
  (S.filter fun e => ∀ e' ∈ S, f e' ≤ f e).min' (by
    obtain ⟨x, hx, hmax⟩ := S.exists_max_image f hne
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hmax⟩⟩)

/-- `leastArgmax S f hne` lies in `S`, and `f` takes its largest value on `S` there. -/
theorem leastArgmax_spec (S : Finset ℕ) (f : ℕ → ℝ) (hne : S.Nonempty) :
    leastArgmax S f hne ∈ S ∧ ∀ x ∈ S, f x ≤ f (leastArgmax S f hne) := by
  classical
  have h := Finset.min'_mem (S.filter fun e => ∀ e' ∈ S, f e' ≤ f e) (by
    obtain ⟨x, hx, hmax⟩ := S.exists_max_image f hne
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hmax⟩⟩)
  unfold leastArgmax
  convert (Finset.mem_filter.mp h) using 2

/-- `leastArgmax S f hne` is at most every maximizer of `f` on `S`. -/
theorem leastArgmax_le (S : Finset ℕ) (f : ℕ → ℝ) (hne : S.Nonempty) {x : ℕ} (hx : x ∈ S)
    (hmax : ∀ y ∈ S, f y ≤ f x) : leastArgmax S f hne ≤ x := by
  classical
  unfold leastArgmax
  convert Finset.min'_le (S.filter fun e => ∀ e' ∈ S, f e' ≤ f e) x
    (Finset.mem_filter.mpr ⟨hx, hmax⟩)

/-- Exact ratio of the fundamental chain cycle associated to off-tree edge `e`. -/
noncomputable def exactCycleRatio (C : TreeChain) (g ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  |walkInner g (C.fundChainCycle e)| / walkLength ℓ (C.fundChainCycle e)

/-- Heap key maintained by a fast Word-RAM implementation of `FindCycle`:
`|⟨g^{𝒞(G_i, F_i)}, a(e)⟩| / wlen_{e^G}` where `i = edgeLevel e`. By repaired `lemma_7_12`,
the numerator equals `|⟨g, a^G(e^G)⟩|`; by `lemma_7_13`, `wlen_{e^G} ≥ ⟨ℓ, |a^G(e^G)|⟩`; and by
`lemma_A_2` (proof), maximizing `heapKey` also meets the ratio bound of Lemma 5.11. -/
noncomputable def heapCycleRatio (C : TreeChain) (g ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  let i := C.edgeLevel e
  |walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e)| / C.wlen ℓ e

/-- **Algorithm 1 `FindCycle()`** (`jtree.tex`, page 21, line 331, and proof of Lemma 5.11, page 24,
lines 494–518): selects the off-tree edge `e^* ∈ E(G_0) \ E(T^𝒢)` (equivalently, over all levels
`0 ≤ i ≤ d`, each candidate `e ∈ E(𝒞(G_i, F_{bran_i})) \ E(𝒮(G_i, F_{bran_i}))`: fundamental
spanner cycles for `i < d` and level-`d` fundamental tree cycles for `i = d`) maximizing its
own-level core-graph quality key `heapCycleRatio C g ℓ e = |⟨g^{𝒞(G_i, F_i)}, a(e)⟩| / wlen_{e^G}`
(or returns the empty walk / zero circulation when `G_0.E ⊆ E(T^𝒢)`), mapped back to `G_0` as
`C.fundChainCycle e^*` and oriented so that `⟨g, Δ⟩ ≤ 0`. Returns `(Δ, cycleWalk, optEdge)`. Among
several candidates achieving the largest key, this model breaks ties by the least internal edge
name (`leastArgmax`). -/
noncomputable def algorithm1_findCycle {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) : (ℕ → ℝ) × List (ℕ × Bool) × Option ℕ :=
  open Classical in
  let C := st.toTreeChain
  let S := (st.G 0).E \ C.chainTree.E
  if hne : S.Nonempty then
    let eBest := leastArgmax S (heapCycleRatio C st.g st.ℓ) hne
    let rawWalk := C.fundChainCycle eBest
    let orientedWalk := if walkInner st.g rawWalk ≤ 0 then rawWalk else walkRev rawWalk
    (walkFlow orientedWalk, orientedWalk, some eBest)
  else
    (0, [], none)

end Algorithm1Defs

section Invariants

/-- Per-level history witness linking `st.scState i` to a valid `SparseCoreRestartTool`
run-with-restarts over a dynamic graph history of length `len_i` bounded by `(levelM TP P i, N₀)`. -/
structure LevelHistory (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams)
    (N₀ : ℕ) (st : ChainState T P) (i : ℕ) where
  D : DynamicInstance
  len : ℕ
  s₀ : ℕ
  hs₀ : s₀ ≤ len
  restarts : ℕ → List ℕ
  hRestartsLt : ∀ r ≤ len, ∀ j ∈ restarts r, j < P.k
  hRestartsCount : (Finset.range (len + 1)).sum (fun r => (restarts r).length) = st.curRestarts i
  hS0Fresh : s₀ = 0 ∨ st.bran i ∈ restarts s₀
  hNoRestartAfterS0 : ∀ r, s₀ < r → r ≤ len → st.bran i ∉ restarts r
  hG0 : (D.G 0).IsValid
  hD : D.IsValid len
  hLen : LengthsStable D len
  hℓPos : ∀ s ≤ len, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e
  hEndG : D.G len = st.G i
  hEndℓ : ∀ e ∈ (st.G i).E, D.ℓ len e = st.toTreeChain.chainLen st.ℓ i e
  hEndg : D.g len = st.toTreeChain.chainGrad st.g i
  hUpd : (Finset.Icc 1 len).sum (fun s => (D.U s).length) = st.updCount i
  hThresh : ((st.updCount i : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold P.k (levelM TP P i) N₀
  hInitMBound : (D.G 0).m ≤ levelM TP P i
  hInitNBound : (D.G 0).n ≤ N₀
  hRun : st.scState i = T.runAfterRestarts P.k (levelM TP P i) N₀ D restarts len
  branchSeq : ℕ → ℕ
  hBranch : ∀ s, branchSeq s < P.k
  hBranchTail : ∀ s, s₀ < s → s ≤ len → branchSeq s = st.bran i
  hWinFwdBound :
    (((Finset.Icc 1 s₀).sum fun s =>
      ((T.runAfterUpdate P.k (levelM TP P i) N₀ D restarts s).2 (branchSeq s)).length : ℕ) : ℝ) ≤
      TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc 1 s₀).sum fun s => (D.U s).length : ℕ) : ℝ)
  hCurFwdEq : st.curFwd i =
    (Finset.Icc 1 len).sum fun s =>
      ((T.runAfterUpdate P.k (levelM TP P i) N₀ D restarts s).2 (branchSeq s)).length
  hDecEq : st.curDecUpdates i + (T.lsfs (st.scState i) (st.bran i)).F.F.E.card =
    (T.lsfs (T.runAfterRestarts P.k (levelM TP P i) N₀ D restarts s₀) (st.bran i)).F.F.E.card
  hEnc0Le : i = 0 →
    st.curEnc 0 ≤ (Finset.Icc 1 len).sum fun s => (D.G (s - 1)).batchEnc (D.U s)
  hEncLe : i + 1 < P.d →
    st.curEnc (i + 1) ≤
      (Finset.Icc (s₀ + 1) len).sum fun s =>
        (T.S (T.runAfterRestarts P.k (levelM TP P i) N₀ D restarts (s - 1)) (st.bran i)).batchEnc
          ((T.runAfterUpdate P.k (levelM TP P i) N₀ D restarts s).2 (st.bran i))

/-- Telescoping received/forwarded update bound across levels with multiplicative recourse `factor`
(`factor = γ_r(M₀²)` unconditionally via `T.restart` in `Shift`). -/
def ChainRecBound {T : SparseCoreRestartTool} (P : ChainParams) (factor : ℝ)
    (st : ChainState T P) : Prop :=
  ∀ i < P.d,
    (st.curFwd i : ℝ) ≤ factor * (st.updCount i : ℝ) ∧
    ((st.recUpdates (i + 1) : ℝ) - (st.curFwd i : ℝ)) ≤
      factor * ((st.recUpdates i : ℝ) - (st.updCount i : ℝ))

lemma ChainRecBound.recUpdates_succ_le {T : SparseCoreRestartTool} {P : ChainParams} {factor : ℝ}
    {st : ChainState T P} (h : ChainRecBound P factor st) {i : ℕ} (hi : i < P.d) :
    (st.recUpdates (i + 1) : ℝ) ≤ factor * (st.recUpdates i : ℝ) := by
  have hi' := h i hi
  linarith

lemma ChainRecBound.recUpdates_le_pow {T : SparseCoreRestartTool} {P : ChainParams} {factor : ℝ}
    (hf : 0 ≤ factor) {st : ChainState T P} (h : ChainRecBound P factor st) :
    ∀ i ≤ P.d, (st.recUpdates i : ℝ) ≤ factor ^ i * (st.recUpdates 0 : ℝ) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hi_lt : i < P.d := hi
    calc
      (st.recUpdates (i + 1) : ℝ) ≤ factor * (st.recUpdates i : ℝ) := h.recUpdates_succ_le hi_lt
      _ ≤ factor * (factor ^ i * (st.recUpdates 0 : ℝ)) :=
        mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hi_lt)) hf
      _ = factor ^ (i + 1) * (st.recUpdates 0 : ℝ) := by rw [pow_succ]; ring

/-- Master invariant maintained by Algorithm 1 across `Initialize`, `Rebuild`, `Shift`, and
`Update`. -/
structure ChainInv (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P) : Prop where
  hG0Valid : (st.G 0).IsValid
  hG0m : (st.G 0).m ≤ P.M₀
  hG0n : (st.G 0).n ≤ N₀
  hℓPos : ∀ e ∈ (st.G 0).E, 0 < st.ℓ e
  hLastK : 0 < st.lastK
  hLastBran : st.lastBran < st.lastK
  hLastHolds : ∀ j < st.lastK, (st.lastLSFs j).Holds (st.G P.d) (st.toTreeChain.chainLen st.ℓ P.d)
    (LP.σ_last (st.G P.d).n)
  hLastMWU : ∀ e ∈ (st.G P.d).E,
    (∑ j ∈ Finset.range st.lastK, (st.lastLSFs j).wstr e) / (st.lastK : ℝ) ≤
      LP.σ_mwu (st.G P.d).n
  hLastSpans : ∀ j < st.lastK, ∀ u ∈ (st.G P.d).V, ∀ v ∈ (st.G P.d).V,
    (st.G P.d).Connected u v → (st.lastLSFs j).F.F.Connected u v
  hBran : ∀ i < P.d, st.bran i < P.k
  hGSucc : ∀ i < P.d, st.G (i + 1) = T.S (st.scState i) (st.bran i)
  hHist : ∀ i < P.d, Nonempty (LevelHistory T TP P N₀ st i)
  hRecRebuild : ∀ i < P.d,
    (st.rebuildCount i : ℝ) * ((intRebuildThreshold P N₀ i : ℝ) + 1) +
      (st.updCount i : ℝ) ≤ (st.recUpdates i : ℝ)
  hRecFwd : ChainRecBound P (TP.γ_r (P.M₀ ^ 2)) st
  hEnc0 : (st.curEnc 0 : ℝ) ≤
    20 * ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ)) *
      Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2)
  hLastCap : 0 < P.d →
    (∃ H : LevelHistory T TP P N₀ st (P.d - 1),
      st.curLastRebuilds ≤
        (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
          ((T.runAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.restarts s).2
            (st.bran (P.d - 1))).length) ∧
    (st.curLastCost : ℝ) ≤
      ((st.curLastRebuilds + 1 : ℕ) : ℝ) *
        (LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2)) ^
            LP.p_last) ∧
    (st.curLastTreeUpdates : ℝ) ≤
      2 * (st.curLastRebuilds : ℝ) * (levelM TP P P.d : ℝ)
  hLvlM : st.lvlM = levelM TP P
  hN0 : st.N₀ = N₀

end Invariants

end MinCostFlow.Chain
