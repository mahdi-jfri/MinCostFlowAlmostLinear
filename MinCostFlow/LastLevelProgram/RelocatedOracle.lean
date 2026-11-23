module

public import MinCostFlow.LastLevelProgram.CanonicalOracle
public import MinCostFlow.LastLevelProgram.RelocatedTreeCall

/-!
# The canonical oracle as a last-level procedure

On fitting fixed-point inputs, the relocated Theorem 2.2 procedure
(page 7) produces the same compact tree as the canonical oracle used
in the multiplicative-weights model of Definition 5.8 (pages 19–20).
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord Num

/-- A single choice of oracle works for each linked host and every query
on the selected grid. The compact tree meets the cited stretch bound, and
restoring its names gives the tree used by the fixed-point model. -/
theorem exists_relocatedTreeOracle :
    ∃ (Q : Program) (c₀ : ℕ) (K : ℝ), 1 ≤ c₀ ∧
      ∀ L P : ℕ, ∃ oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph,
      ∀ (G : MGraph) (ℓ v : ℕ → ℝ),
        G.IsValid → G.V.Nonempty → 1 ≤ L →
        (∀ e ∈ G.E, 0 < queryNumerator P (ℓ e) ∧ Fits 1 L (queryNumerator P (ℓ e))) →
        (∀ e ∈ G.E, 0 < queryNumerator P (v e) ∧ Fits 1 L (queryNumerator P (v e))) →
        (∀ e, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P) →
        (∀ e, ∃ a : ℤ, v e = (a : ℝ) / (2 : ℝ)^P) →
        ∃ (tree : MGraph) (guestCost : ℕ),
          oracle G ℓ v = restoreTreeNames G tree ∧
          LSF.IsLSST (indexedGraph G).toMGraph (ℓ ∘ edgeName G) (v ∘ edgeName G)
            ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2) tree ∧
          LSF.IsLSST G ℓ v ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2) (oracle G ℓ v) ∧
          (guestCost : ℝ) ≤ 16000 * ((G.m + G.n + 1 : ℕ) : ℝ) *
            lsstOverheadFactor Q c₀ K G.n G.m L ∧
          ∀ (host : Program) (b hostWidth heap src D : ℕ),
            let sim := lsstLSimMin c₀ G.n G.m L 1
            let w := paddedGuestWidth Q D G.n G.m sim (queryHeap G L)
            host.HasAt b (relocatedTreeProcedures Q b) → max K 0 ≤ (D : ℝ) →
            w ≤ hostWidth → heap + 1 + 2 ^ w ≤ 2 ^ hostWidth → 4 ≤ 2 ^ hostWidth →
            MeetsContract hostWidth host b
              (relocatedTreeAtWidthContract Q c₀ w G L (queryNumerator P ∘ ℓ)
                (queryNumerator P ∘ v) heap src guestCost tree) := by
  obtain ⟨Q, c₀, K, hc, hOracle⟩ := exists_canonicalTreeOracle
  refine ⟨Q, c₀, K, hc, ?_⟩
  intro L P
  obtain ⟨oracle, hquery⟩ := hOracle L P
  refine ⟨oracle, ?_⟩
  intro G ℓ v hG hV hL hlen hwt hlenGrid hwtGrid
  obtain ⟨st, cost, hrun, hname, hcompact, hnamed, hcost, hcount, hbridges, hdecode⟩ :=
    hquery G ℓ v hG hV hL hlen hwt hlenGrid hwtGrid
  refine ⟨_, cost, hname, hcompact, hnamed, hcost, ?_⟩
  intro host b hostWidth heap src D sim w hp hK hw hspace hfour
  exact relocatedTree_padded_meetsContract c₀ D K hK G L (queryNumerator P ∘ ℓ)
    (queryNumerator P ∘ v) heap src cost st hc hL (indexedGraph_valid hG hV)
    hp hw hspace hfour hrun hdecode hcount hbridges

/-- Select a single oracle using the query graph and lengths to set the
guest format. Every host receives the same compact tree for that query. -/
theorem exists_graphRelocatedTreeOracle
    (limbs precision : ℝ → MGraph → (ℕ → ℝ) → ℕ) :
    ∃ (Q : Program) (c₀ : ℕ) (K : ℝ), 1 ≤ c₀ ∧
      ∃ oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph,
      ∀ (G : MGraph) (ℓ v : ℕ → ℝ),
        let L := limbs K G ℓ
        let P := precision K G ℓ
        G.IsValid → G.V.Nonempty → 1 ≤ L →
        (∀ e ∈ G.E, 0 < queryNumerator P (ℓ e) ∧ Fits 1 L (queryNumerator P (ℓ e))) →
        (∀ e ∈ G.E, 0 < queryNumerator P (v e) ∧ Fits 1 L (queryNumerator P (v e))) →
        (∀ e, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P) →
        (∀ e, ∃ a : ℤ, v e = (a : ℝ) / (2 : ℝ)^P) →
        ∃ (tree : MGraph) (guestCost : ℕ),
          oracle G ℓ v = restoreTreeNames G tree ∧
          LSF.IsLSST (indexedGraph G).toMGraph (ℓ ∘ edgeName G) (v ∘ edgeName G)
            ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2) tree ∧
          LSF.IsLSST G ℓ v ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2) (oracle G ℓ v) ∧
          (guestCost : ℝ) ≤ 16000 * ((G.m + G.n + 1 : ℕ) : ℝ) *
            lsstOverheadFactor Q c₀ K G.n G.m L ∧
          ∀ (host : Program) (b hostWidth heap src D : ℕ),
            let sim := lsstLSimMin c₀ G.n G.m L 1
            let w := paddedGuestWidth Q D G.n G.m sim (queryHeap G L)
            host.HasAt b (relocatedTreeProcedures Q b) → max K 0 ≤ (D : ℝ) →
            w ≤ hostWidth → heap + 1 + 2 ^ w ≤ 2 ^ hostWidth → 4 ≤ 2 ^ hostWidth →
            MeetsContract hostWidth host b
              (relocatedTreeAtWidthContract Q c₀ w G L (queryNumerator P ∘ ℓ)
                (queryNumerator P ∘ v) heap src guestCost tree) := by
  classical
  obtain ⟨Q,c₀,K,hc,hOracle⟩ := exists_relocatedTreeOracle
  let oracleAt := fun L P => Classical.choose (hOracle L P)
  let oracle := fun G ℓ v => oracleAt (limbs K G ℓ) (precision K G ℓ) G ℓ v
  refine ⟨Q,c₀,K,hc,oracle,?_⟩
  intro G ℓ v L P
  exact Classical.choose_spec (hOracle L P) G ℓ v

end MinCostFlow.LastLevelProgram
