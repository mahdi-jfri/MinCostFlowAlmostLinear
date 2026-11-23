module

public import MinCostFlow.LastLevelProgram.CanonicalTreeCall
import Mathlib.Tactic

/-!
# The fixed-point oracle from the canonical LSST run

For the oracle in Definition 5.8 (pages 19–20), recover the integer
numerators from the queried lengths and weights and read the tree
from the canonical machine execution of Theorem 2.2 (page 7).
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num WideWord

/-- Recover the integer numerator at a given fractional precision. -/
noncomputable def queryNumerator (P : ℕ) (x : ℝ) : ℤ :=
  ⌊x * (2 : ℝ)^P⌋

/-- The query numerator is obtained by scaling and rounding down. -/
theorem queryNumerator_def (P : ℕ) (x : ℝ) :
    queryNumerator P x = ⌊x * (2 : ℝ)^P⌋ := by unfold queryNumerator; rfl

/-- Recovering a numerator from a value on the grid gives the same integer. -/
theorem queryNumerator_grid (P : ℕ) (a : ℤ) :
    queryNumerator P ((a : ℝ) / (2 : ℝ)^P) = a := by
  rw [queryNumerator, div_mul_cancel₀ _ (by positivity), Int.floor_intCast]

/-- A total graph function reads the canonical machine tree on every
valid fixed-point query at the selected limb count and precision. -/
theorem exists_canonicalTreeOracle :
    ∃ (Q : Program) (c₀ : ℕ) (K : ℝ), 1 ≤ c₀ ∧
      ∀ L P : ℕ, ∃ oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph,
      ∀ (G : MGraph) (ℓ v : ℕ → ℝ),
        G.IsValid → G.V.Nonempty → 1 ≤ L →
        (∀ e ∈ G.E, 0 < queryNumerator P (ℓ e) ∧ Fits 1 L (queryNumerator P (ℓ e))) →
        (∀ e ∈ G.E, 0 < queryNumerator P (v e) ∧ Fits 1 L (queryNumerator P (v e))) →
        (∀ e, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P) →
        (∀ e, ∃ a : ℤ, v e = (a : ℝ) / (2 : ℝ)^P) →
        let H := indexedGraph G
        let p : Program := ⟨lsstModule Q 0 1⟩
        let heap := queryHeap G L
        let sim := lsstLSimMin c₀ H.n H.m L 1
        let w := max 5 (Nat.log 2 (heap + lsstSpace Q K H.n H.m sim 1) + 1)
        let orig := queryOriginals G L
        let bridge := queryBridges G L
        let header := queryHeader G L
        let args := [H.n, H.m, 0, H.m, queryLengths G, queryWeights G L, L, sim,
          orig, bridge, header, heap]
        ∃ st cost,
          Runs w p (fun _ => false) (lsstEntryProc 0 1)
            (startState args (queryMemory G L (queryNumerator P ∘ ℓ) (queryNumerator P ∘ v)) 0)
            (.returned 0) st cost ∧
          oracle G ℓ v = restoreTreeNames G (treeFromOutput G st.mem orig bridge header) ∧
          LSF.IsLSST H.toMGraph (ℓ ∘ edgeName G) (v ∘ edgeName G)
            ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2)
            (treeFromOutput G st.mem orig bridge header) ∧
          LSF.IsLSST G ℓ v ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2) (oracle G ℓ v) ∧
          (cost : ℝ) ≤ 16000 * ((G.m + G.n + 1 : ℕ) : ℝ) *
            lsstOverheadFactor Q c₀ K G.n G.m L ∧
          st.mem header ≤ G.n ∧ st.mem (header + 1) ≤ G.n ∧
          (∀ (base : ℕ) (moved : ℕ → ℕ),
            (∀ a < 2 ^ w, moved (base + a) = st.mem a) →
            treeFromOutput G moved (base + orig) (base + bridge) (base + header) =
              treeFromOutput G st.mem orig bridge header) := by
  classical
  obtain ⟨Q, c₀, K, hc, hcall⟩ := canonicalTreeCall_runs
  refine ⟨Q, c₀, K, hc, ?_⟩
  intro L P
  let ready : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → Prop := fun G ℓ v =>
    G.IsValid ∧ G.V.Nonempty ∧ 1 ≤ L ∧
      (∀ e ∈ G.E, 0 < queryNumerator P (ℓ e) ∧ Fits 1 L (queryNumerator P (ℓ e))) ∧
      (∀ e ∈ G.E, 0 < queryNumerator P (v e) ∧ Fits 1 L (queryNumerator P (v e)))
  let run := fun G ℓ v (h : ready G ℓ v) =>
    hcall G L P (queryNumerator P ∘ ℓ) (queryNumerator P ∘ v)
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  let oracle := fun G ℓ v =>
    if h : ready G ℓ v then
      restoreTreeNames G (treeFromOutput G (Classical.choose (run G ℓ v h)).mem
        (queryOriginals G L) (queryBridges G L) (queryHeader G L))
    else G
  refine ⟨oracle, ?_⟩
  intro G ℓ v hG hV hL hℓ hv hℓGrid hvGrid
  dsimp only
  have h : ready G ℓ v := ⟨hG, hV, hL, hℓ, hv⟩
  let st := Classical.choose (run G ℓ v h)
  obtain ⟨cost, hrun, hcompact, htree, hcost, heCount, hbCount, htranslate⟩ := Classical.choose_spec (run G ℓ v h)
  change Runs _ _ _ _ _ _ st cost at hrun
  have horacle : oracle G ℓ v = restoreTreeNames G (treeFromOutput G st.mem
      (queryOriginals G L) (queryBridges G L) (queryHeader G L)) := by
    simp only [oracle, dite_eq_left h, st]
  have hlen : (fun e => (queryNumerator P (ℓ e) : ℝ) / (2 : ℝ)^P) = ℓ := by
    funext e
    obtain ⟨a, ha⟩ := hℓGrid e
    rw [ha, queryNumerator_grid]
  have hweight : (fun e => (queryNumerator P (v e) : ℝ) / (2 : ℝ)^P) = v := by
    funext e
    obtain ⟨a, ha⟩ := hvGrid e
    rw [ha, queryNumerator_grid]
  refine ⟨st, cost, hrun, horacle, ?_, ?_, hcost, heCount, hbCount, htranslate⟩
  · change LSF.IsLSST (indexedGraph G).toMGraph
      ((fun e => (queryNumerator P (ℓ e) : ℝ) / (2 : ℝ)^P) ∘ edgeName G)
      ((fun e => (queryNumerator P (v e) : ℝ) / (2 : ℝ)^P) ∘ edgeName G) _
      (treeFromOutput G st.mem (queryOriginals G L) (queryBridges G L) (queryHeader G L)) at hcompact
    rwa [hlen,hweight] at hcompact
  · rw [horacle]
    change LSF.IsLSST G
      (fun e => (queryNumerator P (ℓ e) : ℝ) / (2 : ℝ)^P)
      (fun e => (queryNumerator P (v e) : ℝ) / (2 : ℝ)^P) _
      (restoreTreeNames G (treeFromOutput G st.mem (queryOriginals G L)
        (queryBridges G L) (queryHeader G L))) at htree
    rwa [hlen, hweight] at htree

end MinCostFlow.LastLevelProgram
