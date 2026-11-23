module

public import MinCostFlow.Chain.ExamplesTools
public import MinCostFlow.Chain.Lemma5_11
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concrete examples and non-vacuity for Algorithm 1 and Lemma 5.11

This file constructs concrete witnesses showing that the hypotheses and conclusions of
`LastLevelTool.IsSpec`, `SparseCoreRestartTool.IsSpecRestart` (on no-update dynamic graphs),
`ChainInv`, `ChainBudgetInv`, `TreeChain.Holds`, `findCycle_spec_of_holds`, and Lemma 5.11 hold
simultaneously:

1. **Kruskal minimum-weight spanning forest (`kruskalLSF`)** on any valid `G : MGraph` with
   positive edge lengths `ℓ`: proves `LSF.Holds` with stretch `≤ max 1 (G.n : ℝ)`, component-spanning
   `F`, and at most `1` root when `G` is connected.
2. **Concrete `LastLevelTool` (`exLastTool`)**: meets **universal** `LastLevelTool.IsSpec exLastParams`
   for every valid graph `G_d` and positive edge lengths `ℓ_d`.
3. **Concrete `SparseCoreRestartTool` (`exCoreTool`)**: maintains the Kruskal LSF `(F, R)` with
   contracted core sparsifier `S = (R, ∅)` and empty embeddings `emb _ = []`; meets all clauses of
   `SparseCoreRestartTool.IsSpecRestart exSparseParams`, `ToolMWURestart`,
   `ToolEmbedsSurvivingRestart`, and `ToolNoReinsertRestart` on arbitrary valid no-update dynamic
   instances (`∀ t ≥ 1, D.U t = []`) under arbitrary branch restart schedules. (Maintaining the
   full dynamic `IsSpecRestart` under arbitrary edge deletions and insertions requires the dynamic
   LSF and dynamic spanner constructions of `MinCostFlow/LSF/` and `MinCostFlow/DynSpanner/`.)
4. **Concrete Algorithm 1 run on `K_3` (`exK3_algorithm1_run_spec`)**: runs `algorithm1_initialize`,
   `algorithm1_shift 0`, `algorithm1_update []`, and `algorithm1_findCycle` on the 3-vertex cycle
   `exK3`, proving `ChainInv`, `ChainBudgetInv`, `TreeChain.Holds`, `LastLevelSpans`,
   `EmbedsSurviving`, exact `T^𝒢` change tracking, a nonzero negative `FindCycle` circulation with
   `≤ 2` off-tree edges and positive ratio bound, level graph sizes, and collapsing runtime /
   tree-update bounds.
-/

@[expose] public section

namespace MinCostFlow.Chain

section ConcreteRunOnK3

/-- The 3-vertex directed triangle `K_3` on `{0, 1, 2}` (`0: 0→1`, `1: 1→2`, `2: 2→0`). -/
def exK3 : MGraph where
  V := {0, 1, 2}
  E := {0, 1, 2}
  tail := fun e => if e = 0 then 0 else if e = 1 then 1 else 2
  head := fun e => if e = 0 then 1 else if e = 1 then 2 else 0

lemma exK3_isValid : exK3.IsValid := by
  intro e he
  simp only [exK3, Finset.mem_insert, Finset.mem_singleton] at he ⊢
  rcases he with rfl | rfl | rfl <;> simp

lemma exK3_m : exK3.m = 3 := by decide
lemma exK3_n : exK3.n = 3 := by decide

lemma exK3_connected : ∀ u ∈ exK3.V, ∀ v ∈ exK3.V, exK3.Connected u v := by
  have h01 : exK3.Connected 0 1 :=
    ⟨[(0, true)], .cons (by decide) (by simp [MGraph.src, exK3])
      (by simp [MGraph.dst, exK3]; exact .nil _)⟩
  have h12 : exK3.Connected 1 2 :=
    ⟨[(1, true)], .cons (by decide) (by simp [MGraph.src, exK3])
      (by simp [MGraph.dst, exK3]; exact .nil _)⟩
  have h20 : exK3.Connected 2 0 :=
    ⟨[(2, true)], .cons (by decide) (by simp [MGraph.src, exK3])
      (by simp [MGraph.dst, exK3]; exact .nil _)⟩
  have h10 := MGraph.connected_symm h01
  have h21 := MGraph.connected_symm h12
  have h02 := MGraph.connected_trans h01 h12
  intro u hu v hv
  simp only [exK3, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact MGraph.connected_refl _ _
  · exact h01
  · exact h02
  · exact h10
  · exact MGraph.connected_refl _ _
  · exact h12
  · exact h20
  · exact h21
  · exact MGraph.connected_refl _ _

/-- Concrete `ChainParams` on `exK3`: `d = 1`, `k = 3`, `M₀ = 3`. -/
def exP : ChainParams where
  d := 1
  k := 3
  M₀ := 3
  hd := zero_lt_one
  hk := by decide
  hM₀ := by decide
  hk_pow := by decide
  hk_upper := by norm_num

lemma exγk : exSparseParams.γ_ℓ (exP.M₀ ^ 2) ≤ exP.k := by
  simp [exSparseParams, exP]

/-- Unit circulation `(1, 1, 1)` around `exK3`. -/
def exCirc : ℕ → ℝ := fun e => if e ∈ exK3.E then 1 else 0

lemma exK3_isValidPair : IsValidPair exK3 (fun _ => 1) exCirc exCirc := by
  refine ⟨fun v _ => ?_, fun e he => ?_⟩
  · unfold MGraph.demand
    have hE : exK3.E = ({0, 1, 2} : Finset ℕ) := rfl
    rw [hE]
    simp [Finset.sum_insert, Finset.sum_singleton, MGraph.b, exK3, exCirc]
  · simp [exCirc, he]

/-- Helper constant no-update `DynamicInstance` at graph `G` with length `ℓ` and gradient `g`. -/
private def constDyn (G : MGraph) (ℓ g : ℕ → ℝ) : DynamicInstance where
  G := fun _ => G
  U := fun _ => []
  g := fun _ => g
  ℓ := fun _ => ℓ

private lemma constDyn_valid (G : MGraph) (ℓ g : ℕ → ℝ) (τ : ℕ) :
    (constDyn G ℓ g).IsValid τ := by
  intro _ _ _
  exact ⟨by simp [constDyn, MGraph.BatchIsValid], rfl⟩

private lemma constDyn_lenStable (G : MGraph) (ℓ g : ℕ → ℝ) (τ : ℕ) :
    LengthsStable (constDyn G ℓ g) τ := fun _ _ _ _ _ _ _ => rfl

private lemma constDyn_noReins (G : MGraph) (ℓ g : ℕ → ℝ) (τ : ℕ) :
    ∀ s, 1 ≤ s → s ≤ τ → NoBatchReinsert ((constDyn G ℓ g).G (s - 1)) ((constDyn G ℓ g).U s) :=
  fun _ _ _ _ _ _ hu => by cases hu

private lemma ex_opRuntimeBudget_nonneg (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (hTP : TP.Valid) (hLP : LP.Valid) (n i₀ : ℕ) :
    0 ≤ opRuntimeBudget TP LP P n i₀ := by
  have hγℓ : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.1 (P.M₀ ^ 2))
  have hlog10 : 0 ≤ Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) := by
    refine Real.log_nonneg ?_
    have hnn : 0 ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := mul_nonneg (Nat.cast_nonneg _) hγℓ
    linarith
  have hlog2 : 0 ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _])
  have hlogF : 0 ≤ logFactor P n := le_trans zero_le_one (one_le_logFactor P n)
  have hγr : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2))
  have hcT : 0 ≤ TP.c_T := hTP.2.2.2.2.2.2.2.2.2
  have hcL : 0 ≤ LP.c_last := hLP.2.2.2.2
  have hdiv : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) := div_nonneg hγℓ (Nat.cast_nonneg _)
  have hTool : ∀ j, 0 ≤ levelToolCap TP P n j := fun j => by
    unfold levelToolCap
    refine add_nonneg (by positivity) ?_
    split_ifs
    · positivity
    · exact mul_nonneg (by positivity)
        (add_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) zero_le_one)
  have hLast : 0 ≤ lastCostCap TP LP P n := by
    unfold lastCostCap
    refine mul_nonneg
      (add_nonneg (add_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) (by positivity))
        zero_le_one) ?_
    positivity
  unfold opRuntimeBudget
  refine add_nonneg (add_nonneg ?_ hLast) ?_
  · split_ifs
    · exact Finset.sum_nonneg fun j _ => hTool j
    · exact le_refl 0
  · split_ifs
    · unfold extraEncCap; positivity
    · exact le_refl 0

private lemma lsfHolds_mono {L : LSF} {G : MGraph} {ℓ : ℕ → ℝ} {σ₁ σ₂ : ℝ}
    (hL : L.Holds G ℓ σ₁) (hσ : σ₁ ≤ σ₂) : L.Holds G ℓ σ₂ :=
  ⟨hL.1, hL.2.1, hL.2.2.1, fun e he => ⟨(hL.2.2.2 e he).1, le_trans (hL.2.2.2 e he).2 hσ⟩⟩

private noncomputable def exG1 : MGraph :=
  MGraph.mk (kruskalLSF exK3 (fun _ => 1)).F.R ∅ exK3.tail exK3.head

private lemma exG1_valid : exG1.IsValid := fun _ he => by cases he

private lemma kruskalLSF_empty_indep (ℓ₁ ℓ₂ : ℕ → ℝ) :
    kruskalLSF exG1 ℓ₁ = kruskalLSF exG1 ℓ₂ := by
  have hsort : ∀ ℓ, kruskalSortedEdges exG1 ℓ = [] := fun ℓ => by
    simp [kruskalSortedEdges, exG1, sortByLen]
  simp only [kruskalLSF, kruskalForest, hsort]

private noncomputable def exInitPair :=
  algorithm1_initialize exCoreTool exLastTool exP (levelM exSparseParams exP) 3 exK3 (fun _ => 1) (fun _ => 1)

private noncomputable def exSt0 := exInitPair.1
private noncomputable def exInitCh := exInitPair.2

private noncomputable def exShiftPair :=
  algorithm1_shift exCoreTool exLastTool exP exSt0 0

private noncomputable def exSt1 := exShiftPair.1
private noncomputable def exCh1 := exShiftPair.2

private noncomputable def exUpdPair :=
  algorithm1_update exCoreTool exLastTool exSparseParams exP 3 exSt1 [] (fun _ => 1) (fun _ => 1)

private noncomputable def exStEnd := exUpdPair.1
private noncomputable def exCh2 := exUpdPair.2

private lemma exK3_not_over :
    ¬ (intRebuildThreshold exP 3 0 < 0) :=
  Nat.not_lt_zero _

private lemma exSt0_G0 : exSt0.G 0 = exK3 := rfl
private lemma exSt0_G1 : exSt0.G 1 = exG1 := rfl
private lemma exSt0_sc0 : exSt0.scState 0 =
    exCoreTool.init 3 (levelM exSparseParams exP 0) 3 exK3 (fun _ => 1) (fun _ => 1) := rfl
private lemma exSt0_bran0 : exSt0.bran 0 = 0 := rfl
private lemma exSt0_upd0 : exSt0.updCount 0 = 0 := rfl
private lemma exSt0_rec : ∀ j, exSt0.recUpdates j = 0 := fun _ => rfl
private lemma exSt0_curFwd0 : exSt0.curFwd 0 = 0 := rfl
private lemma exSt0_curEnc0 : exSt0.curEnc 0 = 0 := rfl
private lemma exSt0_curDec0 : exSt0.curDecUpdates 0 = 0 := rfl
private lemma exSt0_curLastReb : exSt0.curLastRebuilds = 0 := rfl
private lemma exSt0_curLastCost : exSt0.curLastCost = 1 := rfl
private lemma exSt0_curLastTU : exSt0.curLastTreeUpdates = 0 := rfl
private lemma exSt0_shift0 : exSt0.shiftCount 0 = 0 := rfl
private lemma exSt0_shift1 : exSt0.shiftCount 1 = 0 := rfl
private lemma exSt0_reb0 : exSt0.rebuildCount 0 = 0 := rfl
private lemma exSt0_reb1 : exSt0.rebuildCount 1 = 0 := rfl
private lemma exSt0_closedRt : exSt0.closedRuntime = 0 := rfl
private lemma exSt0_closedTU : exSt0.closedTreeUpdates = exInitCh.length := rfl
private lemma exSt0_lastBran : exSt0.lastBran = 0 := rfl
private lemma exSt0_ℓ : exSt0.ℓ = (fun _ => 1) := rfl
private lemma exSt0_g : exSt0.g = (fun _ => 1) := rfl
private lemma exSt0_lastLSF0 : exSt0.lastLSFs 0 = kruskalLSF exG1 (fun _ => 1) :=
  kruskalLSF_empty_indep _ _

private lemma ex_chainTree_eq_kruskal (st : ChainState exCoreTool exP)
    (hSc : st.scState 0 = exCoreTool.init 3 (levelM exSparseParams exP 0) 3 exK3 (fun _ => 1) (fun _ => 1))
    (hLLSF : st.lastLSFs st.lastBran = kruskalLSF exG1 (fun _ => 1)) :
    st.toTreeChain.chainTree.E = (kruskalLSF exK3 (fun _ => 1)).F.F.E := by
  ext e
  have hPd : st.toTreeChain.d = 1 := rfl
  unfold TreeChain.chainTree TreeChain.chainTreeEdges
  rw [hPd]
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hei⟩
    have hi1 : i = 0 ∨ i = 1 := by omega
    rcases hi1 with rfl | rfl
    · have hact : st.toTreeChain.activeLSF 0 = exCoreTool.lsfs (st.scState 0) (st.bran 0) := rfl
      rw [hact, hSc] at hei
      exact hei
    · have hact : st.toTreeChain.activeLSF 1 = st.lastLSFs st.lastBran := rfl
      rw [hact, hLLSF] at hei
      have h1 := (kruskalLSF_holds exG1_valid (fun _ h => by cases h)).2.1.2.1 hei
      cases h1
  · intro he
    refine ⟨0, by decide, ?_⟩
    have hact : st.toTreeChain.activeLSF 0 = exCoreTool.lsfs (st.scState 0) (st.bran 0) := rfl
    rw [hact, hSc]
    exact he

private lemma exSt1_fields :
    exSt1.G 0 = exK3 ∧ exSt1.G 1 = exG1 ∧
    exSt1.scState 0 = exSt0.scState 0 ∧ exSt1.bran 0 = 1 ∧
    exSt1.lastK = 1 ∧ exSt1.lastBran = 0 ∧
    exSt1.ℓ = (fun _ => 1) ∧ exSt1.g = (fun _ => 1) ∧
    exSt1.updCount 0 = 0 ∧ (∀ j, exSt1.recUpdates j = 0) ∧ exSt1.curFwd 0 = 0 ∧
    exSt1.curEnc 0 = 0 ∧ exSt1.curDecUpdates 0 = 0 ∧
    exSt1.curLastRebuilds = 0 ∧ exSt1.curLastCost = 1 ∧ exSt1.curLastTreeUpdates = 0 ∧
    exSt1.shiftCount 0 = 1 ∧ exSt1.shiftCount 1 = 0 ∧
    exSt1.rebuildCount 0 = 0 ∧ exSt1.rebuildCount 1 = 0 ∧
    exSt1.closedRuntime = 1 ∧
    exCh1 = [] ∧
    exSt1.closedTreeUpdates = exInitCh.length ∧
    exSt1.lastLSFs 0 = kruskalLSF exG1 (fun _ => 1) := by
  have hS : exCoreTool.S (exSt0.scState 0) ((exSt0.bran 0 + 1) % exP.k) = exG1 := by
    rw [exSt0_sc0]; rfl
  have hIco1 : (Finset.Ico (0 + 1) exP.d).sum (fun j =>
      exCoreTool.cost (exSt0.scState j) + exSt0.curEnc j) = 0 := by
    change (Finset.Ico 1 1).sum _ = 0
    simp
  have hIco0 : (Finset.Ico 0 exP.d).sum (fun j => exSt0.curDecUpdates j) = 0 := by
    change (Finset.Ico 0 1).sum (fun j => exSt0.curDecUpdates j) = 0
    rw [Finset.sum_Ico_succ_top (by decide), Finset.Ico_self, Finset.sum_empty, zero_add]
    exact exSt0_curDec0
  have hStMid_sc0 : (rebuildSuffix exCoreTool exLastTool exP exSt0.lvlM exSt0.N₀ exSt0.ℓ exSt0.g (exP.d - (0 + 1)) (0 + 1)
      (fun j => if j = 0 + 1 then exCoreTool.S (exSt0.scState 0) ((exSt0.bran 0 + 1) % exP.k) else exSt0.G j)
      exSt0.scState (fun j => if j = 0 then (exSt0.bran 0 + 1) % exP.k else exSt0.bran j)
      exSt0.updCount
      (fun j => if j = 0 + 1 then 0 else exSt0.curEnc j)
      (fun j => if j = 0 then 0 else exSt0.curDecUpdates j)
      exSt0.curFwd).2.1 0 = exSt0.scState 0 := by
    change exSt0.scState 0 = exSt0.scState 0; rfl
  have hLast : (rebuildSuffix exCoreTool exLastTool exP exSt0.lvlM exSt0.N₀ exSt0.ℓ exSt0.g (exP.d - (0 + 1)) (0 + 1)
      (fun j => if j = 0 + 1 then exCoreTool.S (exSt0.scState 0) ((exSt0.bran 0 + 1) % exP.k) else exSt0.G j)
      exSt0.scState (fun j => if j = 0 then (exSt0.bran 0 + 1) % exP.k else exSt0.bran j)
      exSt0.updCount
      (fun j => if j = 0 + 1 then 0 else exSt0.curEnc j)
      (fun j => if j = 0 then 0 else exSt0.curDecUpdates j)
      exSt0.curFwd).2.2.2.2.2.2.2.1.2 0 =
      kruskalLSF exG1 (fun _ => 1) := by
    have hPd0 : exP.d - (0 + 1) = 0 := rfl
    simp only [hPd0, rebuildSuffix, exLastTool, hS]
    exact kruskalLSF_empty_indep _ _
  have hSt1_sc0 : exSt1.scState 0 = exSt0.scState 0 := by
    dsimp only [exSt1, exShiftPair, algorithm1_shift]
    rw [dite_eq_left_iff.mpr (fun h => absurd (by decide : 0 < exP.d) h)]
    exact hStMid_sc0
  have hSt1_lastLSF0 : exSt1.lastLSFs 0 = kruskalLSF exG1 (fun _ => 1) := by
    dsimp only [exSt1, exShiftPair, algorithm1_shift]
    rw [dite_eq_left_iff.mpr (fun h => absurd (by decide : 0 < exP.d) h)]
    exact hLast
  have hCh1_def : exCh1 = diffTreeChanges exSt0.toTreeChain.chainTree.E exSt1.toTreeChain.chainTree.E := by
    dsimp only [exCh1, exSt1, exShiftPair, algorithm1_shift]
    rw [dite_eq_left_iff.mpr (fun h => absurd (by decide : 0 < exP.d) h)]
    rfl
  have hCh1 : exCh1 = [] := by
    rw [hCh1_def, ex_chainTree_eq_kruskal exSt0 exSt0_sc0 exSt0_lastLSF0,
      ex_chainTree_eq_kruskal exSt1 (hSt1_sc0.trans exSt0_sc0) hSt1_lastLSF0]
    simp [diffTreeChanges]
  dsimp only [exSt1, exShiftPair, algorithm1_shift]
  rw [dite_eq_left_iff.mpr (fun h => absurd (by decide : 0 < exP.d) h)]
  dsimp only
  refine ⟨?_, ?_, hStMid_sc0, ?_, ?_, rfl, exSt0_ℓ, exSt0_g, exSt0_upd0, exSt0_rec,
    exSt0_curFwd0, ?_, ?_, rfl, ?_, rfl, ?_, ?_, exSt0_reb0, exSt0_reb1, ?_, hCh1, ?_, hLast⟩
  · change exSt0.G 0 = exK3; exact exSt0_G0
  · change exCoreTool.S (exSt0.scState 0) ((exSt0.bran 0 + 1) % exP.k) = exG1; exact hS
  · change (exSt0.bran 0 + 1) % exP.k = 1; rw [exSt0_bran0]; rfl
  · have hPd0 : exP.d - (0 + 1) = 0 := rfl; simp [hPd0, rebuildSuffix, exLastTool]
  · change exSt0.curEnc 0 = 0; exact exSt0_curEnc0
  · rfl
  · have hPd0 : exP.d - (0 + 1) = 0 := rfl; simp [hPd0, rebuildSuffix, exLastTool, exCoreTool]
  · simp [exSt0_shift0]
  · simp [exSt0_shift1]
  · rw [exSt0_closedRt, hIco1, exSt0_curLastCost]
  · change exSt0.closedTreeUpdates + (Finset.Ico 0 exP.d).sum (fun j => exSt0.curDecUpdates j) +
      exSt0.curLastTreeUpdates + exCh1.length = exInitCh.length
    rw [hIco0, hCh1, exSt0_closedTU, exSt0_curLastTU]
    simp

private lemma exStEnd_eq_upd :
    exStEnd = (updateLoop exCoreTool exLastTool exSparseParams exP 3 (fun _ => 1) (fun _ => 1)
      1 0 exSt1 exK3 [] 0).1 := by
  dsimp only [exStEnd, exUpdPair, algorithm1_update]
  rw [exSt1_fields.1]
  have hRec1 : (fun j => if j = 0 then exSt1.recUpdates 0 + ([] : List Update).length
      else exSt1.recUpdates j) = exSt1.recUpdates := by
    funext j
    split_ifs with hj
    · subst hj; simp [exSt1_fields.2.2.2.2.2.2.2.2.2.1 0]
    · rfl
  have hPd : exP.d = 1 := rfl
  have hB : exK3.applyBatch [] = exK3 := rfl
  have hE : exK3.batchEnc [] = 0 := by simp [MGraph.batchEnc]
  rw [hPd, hB, hE, hRec1]

private lemma exCh2_eq_diff :
    exCh2 = diffTreeChanges exSt1.toTreeChain.chainTree.E exStEnd.toTreeChain.chainTree.E := by
  dsimp only [exCh2, exStEnd, exUpdPair, algorithm1_update]

private lemma exStEnd_fields :
    exStEnd.G 0 = exK3 ∧ exStEnd.G 1 = exG1 ∧
    exStEnd.scState 0 = exSt0.scState 0 ∧ exStEnd.bran 0 = 1 ∧
    exStEnd.lastK = 1 ∧ exStEnd.lastBran = 0 ∧
    exStEnd.ℓ = (fun _ => 1) ∧ exStEnd.g = (fun _ => 1) ∧
    exStEnd.updCount 0 = 0 ∧ (∀ j, exStEnd.recUpdates j = 0) ∧ exStEnd.curFwd 0 = 0 ∧
    exStEnd.curEnc 0 = 0 ∧ exStEnd.curDecUpdates 0 = 0 ∧
    exStEnd.curLastRebuilds = 0 ∧ exStEnd.curLastCost = 1 ∧ exStEnd.curLastTreeUpdates = 0 ∧
    exStEnd.shiftCount 0 = 1 ∧ exStEnd.shiftCount 1 = 0 ∧
    exStEnd.rebuildCount 0 = 0 ∧ exStEnd.rebuildCount 1 = 0 ∧
    exStEnd.closedRuntime = 1 ∧
    exStEnd.curRestarts 0 = 1 ∧ (∀ j ≠ 0, exStEnd.curRestarts j = 0) ∧
    exCh2 = [] ∧
    exStEnd.closedTreeUpdates = exInitCh.length ∧
    exStEnd.lastLSFs 0 = kruskalLSF exG1 (fun _ => 1) := by
  rcases exSt1_fields with ⟨hG0, hG1, hSc0, hBr, hLK, hLB, hℓ, hg, hUpd, hRec, hFwd, hEnc, hDec,
    hLR, hLC, hLTU, hS0, hS1, hR0, hR1, hCR, _, hCTU, hLLSF⟩
  have hNotOver : ¬ (intRebuildThreshold exP 3 0 < exSt1.updCount 0 + ([] : List Update).length) := by
    rw [hUpd]; simp
  have hPd : exP.d = 1 := rfl
  have hLoop : (updateLoop exCoreTool exLastTool exSparseParams exP 3 (fun _ => 1) (fun _ => 1)
      1 0 exSt1 exK3 [] 0).1 =
      { exSt1 with
          G := fun j => if j = 1 then exG1 else (if j = 0 then exK3 else exSt1.G j)
          recUpdates := fun j =>
            if j = 1 then exSt1.recUpdates 1 + ([] : List Update).length else exSt1.recUpdates j
          curFwd := fun j =>
            if j = 0 then exSt1.curFwd 0 + ([] : List Update).length else exSt1.curFwd j
          curEnc := fun j =>
            if j = 0 then exSt1.curEnc 0 + 0
            else if j = 1 then exSt1.curEnc 1 + (exSt1.G 1).batchEnc []
            else exSt1.curEnc j
          curDecUpdates := fun j =>
            if j = 0 then exSt1.curDecUpdates 0 +
              (diffTreeChanges (exCoreTool.lsfs (exSt1.scState 0) (exSt1.bran 0)).F.F.E
                (exCoreTool.lsfs (exSt1.scState 0) (exSt1.bran 0)).F.F.E).length
            else exSt1.curDecUpdates j
          ℓ := fun _ => 1
          g := fun _ => 1 } := by
    dsimp only [updateLoop]
    rw [ite_eq_right_iff.mpr (fun h => absurd h hNotOver)]
    dsimp only [updateLoop]
    split_ifs with hNil
    · have hS1G1 : (exSt1.scState 0).2 = exG1 := by
        change exCoreTool.S (exSt1.scState 0) 0 = exG1
        rw [hSc0, exSt0_sc0]; rfl
      simp [hPd, hS1G1, exCoreTool]
      repeat' constructor
      all_goals (funext j; split_ifs with h <;> [exact h.symm ▸ rfl; rfl])
    · exfalso
      apply hNil
      rfl
  have hEnd : exStEnd = _ := exStEnd_eq_upd.trans hLoop
  have hCh2 : exCh2 = [] := by
    have hScEnd : exStEnd.scState 0 = exSt0.scState 0 := by rw [hEnd]; exact hSc0
    have hLastEnd : exStEnd.lastLSFs exStEnd.lastBran = kruskalLSF exG1 (fun _ => 1) := by
      rw [hEnd]; exact hLLSF
    rw [exCh2_eq_diff, ex_chainTree_eq_kruskal exSt1 (hSc0.trans exSt0_sc0) hLLSF,
      ex_chainTree_eq_kruskal exStEnd (hScEnd.trans exSt0_sc0) hLastEnd]
    simp [diffTreeChanges]
  have h01 : (0 : ℕ) ≠ 1 := by decide
  have hEndCRest : exStEnd.curRestarts 0 = 1 ∧ ∀ j ≠ 0, exStEnd.curRestarts j = 0 := by
    have h1CR : exSt1.curRestarts 0 = 1 ∧ ∀ j ≠ 0, exSt1.curRestarts j = 0 := by
      dsimp only [exSt1, exShiftPair, algorithm1_shift]
      rw [dite_eq_left_iff.mpr (fun h => absurd (by decide : 0 < exP.d) h)]
      refine ⟨by simp [exSt0, exInitPair, algorithm1_initialize], fun j hj => ?_⟩
      simp [exSt0, exInitPair, algorithm1_initialize, hj, show exP.d = 1 from rfl]
    rw [hEnd]
    exact h1CR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hEndCRest.1, hEndCRest.2, hCh2, ?_, ?_⟩
  · rw [hEnd]; simp [h01]
  · rw [hEnd]; simp
  · rw [hEnd]; exact hSc0
  · rw [hEnd]; exact hBr
  · rw [hEnd]; exact hLK
  · rw [hEnd]; exact hLB
  · rw [hEnd]
  · rw [hEnd]
  · rw [hEnd]; simp [hUpd]
  · intro j; rw [hEnd]; dsimp only; split_ifs <;> simp [hRec]
  · rw [hEnd]; simp [hFwd]
  · rw [hEnd]; simp [hEnc]
  · rw [hEnd]; simp [hDec, diffTreeChanges]
  · rw [hEnd]; exact hLR
  · rw [hEnd]; exact hLC
  · rw [hEnd]; exact hLTU
  · rw [hEnd]; exact hS0
  · rw [hEnd]; exact hS1
  · rw [hEnd]; exact hR0
  · rw [hEnd]; exact hR1
  · rw [hEnd]; exact hCR
  · rw [hEnd]; exact hCTU
  · rw [hEnd]; exact hLLSF

/-- **Concrete run of Algorithm 1 and Lemma 5.11 on `K_3` (`exK3`)**:
Starting from `algorithm1_initialize exCoreTool exLastTool exP exK3 1 1` and executing
`[ChainAction.shift 0, ChainAction.update [] 1 1]`:
* `ChainInv`, `ChainBudgetInv`, `TreeChain.Holds`, `LastLevelSpans`, and `EmbedsSurviving` all hold
  simultaneously in a verified run;
* the emitted `TreeChange` sequence tracks `T^𝒢` with change count `≤ totalTreeUpdates`;
* `algorithm1_findCycle` outputs a nonzero circulation `Δ` with `⟨g, Δ⟩ < 0`, `≤ 2` off-tree
  edges, and positive ratio satisfying the Lemma A.2 bound;
* level graph size bounds and collapsing runtime/tree-update bounds hold simultaneously. -/
theorem exK3_algorithm1_run_spec :
    let acts : List ChainAction :=
      [ChainAction.shift 0, ChainAction.update [] (fun _ => 1) (fun _ => 1)]
    let st₀ := (algorithm1_initialize exCoreTool exLastTool exP (levelM exSparseParams exP) 3 exK3 (fun _ => 1) (fun _ => 1)).1
    let initCh := (algorithm1_initialize exCoreTool exLastTool exP (levelM exSparseParams exP) 3 exK3 (fun _ => 1) (fun _ => 1)).2
    let stEnd := (execChainActions exCoreTool exLastTool exSparseParams exP 3 st₀ acts).1
    let chs := (execChainActions exCoreTool exLastTool exSparseParams exP 3 st₀ acts).2
    exLastParams.Valid ∧
    exSparseParams.Valid ∧
    exSparseParams.γ_ℓ (exP.M₀ ^ 2) ≤ exP.k ∧
    exLastTool.IsSpec exLastParams ∧
    ChainInv exCoreTool exLastTool exSparseParams exLastParams exP 3 stEnd ∧
    ChainBudgetInv exSparseParams exLastParams 3 stEnd ∧
    stEnd.toTreeChain.Holds (stEnd.G 0) stEnd.ℓ 3 3 1 1 ∧
    stEnd.toTreeChain.LastLevelSpans ∧
    stEnd.toTreeChain.EmbedsSurviving ∧
    ((initCh :: chs).foldl applyTreeChanges ∅ = stEnd.toTreeChain.chainTree.E ∧
      initCh.length + (chs.map List.length).sum ≤ stEnd.totalTreeUpdates) ∧
    (∀ i ≤ exP.d, ((stEnd.G i).m : ℝ) ≤ (exP.M₀ : ℝ) * (1 / 3 : ℝ) ^ i) ∧
    (let C := stEnd.toTreeChain
     let (Δ, walk, optEdge) := algorithm1_findCycle stEnd
     (stEnd.G 0).IsCirculation Δ ∧
     (stEnd.G 0).inner stEnd.g Δ < 0 ∧
     ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + 1 ∧
     (∃ e, optEdge = some e) ∧
     (∀ e, optEdge = some e →
       e ∈ (stEnd.G 0).E \ C.chainTree.E ∧
       0 < (stEnd.G 0).lnorm stEnd.ℓ Δ ∧
       (1 / (3 + 1 : ℝ)) *
           (|(stEnd.G 0).inner stEnd.g exCirc| /
             ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW exCirc i)) ≤
         |(stEnd.G 0).inner stEnd.g Δ| / (stEnd.G 0).lnorm stEnd.ℓ Δ)) ∧
    ((stEnd.totalRuntime : ℝ) ≤
      ((exP.d : ℝ) + 1) * (8 * exSparseParams.c_T + 36 * exLastParams.c_last + 430) *
        (exP.M₀ : ℝ) ^ (1 / (exP.d : ℝ)) *
        (exSparseParams.γ_ℓ (exP.M₀ ^ 2) * exSparseParams.γ_r (exP.M₀ ^ 2)) ^ (3 * exP.d + 1) *
        (2 * logFactor exP 3) ^ (max exSparseParams.p_T exLastParams.p_last + 1) *
        ((exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i)) ∧
    ((stEnd.totalTreeUpdates : ℝ) ≤
      (12 * (exP.d : ℝ) + 18) *
        (exSparseParams.γ_ℓ (exP.M₀ ^ 2) * exSparseParams.γ_r (exP.M₀ ^ 2)) ^ (2 * exP.d + 1) *
        ((exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i)) := by
  change exLastParams.Valid ∧ _
  have hℓ1 : ∀ e ∈ exK3.E, (0 : ℝ) < 1 := fun _ _ => zero_lt_one
  have hDValid := constDyn_valid exK3 (fun _ => 1) (fun _ => 1) 0
  have hDLen := constDyn_lenStable exK3 (fun _ => 1) (fun _ => 1) 0
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero (D := constDyn exK3 (fun _ => 1) (fun _ => 1))
    (fun _ _ _ _ => zero_lt_one)
  have hCoreSpec := exCoreTool_spec_on_noUpdate exP.k 0 (constDyn exK3 (fun _ => 1) (fun _ => 1))
    (fun r => if r = 0 then [1] else []) Ψ (fun _ _ => 0) (fun _ _ => 1) exP.hk exK3_isValid
    hDValid hDLen hWeak (fun s hs1 hs0 => by omega)
  rcases exStEnd_fields with ⟨hEndG0, hEndG1, hEndSc0, hEndBran0, hEndLastK, hEndLastBran,
    hEndℓ, hEndg, hEndUpd0, hEndRec, hEndCurFwd0, hEndEnc0, hEndDec0, hEndLastReb, hEndLastCost, hEndLastTU,
    hEndSh0, hEndSh1, hEndReb0, hEndReb1, hEndCR, hEndCRest0, hEndCRestNe, hCh2Nil, hEndCTU, hLastLSF0⟩
  have hCh1Nil : exCh1 = [] := exSt1_fields.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hLastHolds, _, hLastConn, _⟩ :=
    kruskalLSF_holds exG1_valid (ℓ := fun _ => 1) (fun e he => by cases he)
  have hLastHolds_len : (kruskalLSF exG1 (exStEnd.toTreeChain.chainLen exStEnd.ℓ 1)).Holds exG1
      (exStEnd.toTreeChain.chainLen exStEnd.ℓ 1) (max 1 (exG1.n : ℝ)) :=
    (kruskalLSF_holds exG1_valid (ℓ := exStEnd.toTreeChain.chainLen exStEnd.ℓ 1)
      (fun e he => by cases he)).1
  have hHist0 : LevelHistory exCoreTool exSparseParams exP 3 exStEnd 0 :=
    { D := constDyn exK3 (fun _ => 1) (fun _ => 1)
      len := 0
      s₀ := 0
      hs₀ := le_refl 0
      restarts := fun r => if r = 0 then [1] else []
      hRestartsLt := fun r _ j hj => by
        split_ifs at hj
        · simp only [List.mem_singleton] at hj; subst hj; decide
        · cases hj
      hRestartsCount := by simp [hEndCRest0]
      hS0Fresh := Or.inl rfl
      hNoRestartAfterS0 := fun r hr1 hr2 => by omega
      hG0 := exK3_isValid
      hD := hDValid
      hLen := hDLen
      hℓPos := fun _ _ _ _ => zero_lt_one
      hEndG := hEndG0.symm
      hEndℓ := fun _ _ => by simp [TreeChain.chainLen, hEndℓ]; rfl
      hEndg := by simp [TreeChain.chainGrad, hEndg]; rfl
      hUpd := by simp [hEndUpd0]
      hThresh := by
        rw [hEndUpd0, Nat.cast_zero]
        unfold SparseCoreTool.updateThreshold
        positivity
      hInitMBound := by simp [constDyn, exK3_m, exP, levelM, exSparseParams]
      hInitNBound := by simp [constDyn, exK3_n]
      branchSeq := fun _ => 0
      hBranch := fun _ => exP.hk
      hBranchTail := fun _ hs1 hs2 => by omega
      hWinFwdBound := by simp
      hRun := by
        rw [hEndSc0, exSt0_sc0]
        simp [SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate,
          exCoreTool, constDyn]
      hCurFwdEq := by simp [hEndCurFwd0]
      hDecEq := by
        simp [hEndDec0, hEndSc0, exSt0_sc0, SparseCoreRestartTool.runAfterRestarts,
          SparseCoreRestartTool.runAfterUpdate, exCoreTool, constDyn]
      hEnc0Le := fun _ => by simp [hEndEnc0]
      hEncLe := fun h => by simp [exP] at h }
  have hInv : ChainInv exCoreTool exLastTool exSparseParams exLastParams exP 3 exStEnd := by
    have hEndLvlM : exStEnd.lvlM = levelM exSparseParams exP := by
      rw [exStEnd_eq_upd]
      dsimp only [updateLoop]
      have hNotOver : ¬ (intRebuildThreshold exP 3 0 < exSt1.updCount 0 + ([] : List Update).length) := by
        rw [exSt1_fields.2.2.2.2.2.2.2.2.1]; simp
      rw [ite_eq_right_iff.mpr (fun h => absurd h hNotOver)]
      dsimp only [updateLoop, exCoreTool]
      have hSt1LvlM : exSt1.lvlM = levelM exSparseParams exP := by
        dsimp only [exSt1, exShiftPair, algorithm1_shift]
        rw [dite_eq_left_iff.mpr (fun h => absurd (by decide : 0 < exP.d) h)]
        rfl
      split_ifs <;> exact hSt1LvlM
    have hEndN0 : exStEnd.N₀ = 3 := by
      rw [exStEnd_eq_upd]
      dsimp only [updateLoop]
      have hNotOver : ¬ (intRebuildThreshold exP 3 0 < exSt1.updCount 0 + ([] : List Update).length) := by
        rw [exSt1_fields.2.2.2.2.2.2.2.2.1]; simp
      rw [ite_eq_right_iff.mpr (fun h => absurd h hNotOver)]
      dsimp only [updateLoop, exCoreTool]
      have hSt1N0 : exSt1.N₀ = 3 := by
        dsimp only [exSt1, exShiftPair, algorithm1_shift]
        rw [dite_eq_left_iff.mpr (fun h => absurd (by decide : 0 < exP.d) h)]
        rfl
      split_ifs <;> exact hSt1N0
    refine ⟨hEndG0 ▸ exK3_isValid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hEndLvlM, hEndN0⟩
    · simp [hEndG0, exK3_m, exP]
    · simp [hEndG0, exK3_n]
    · simp [hEndG0, hEndℓ]
    · simp [hEndLastK]
    · simp [hEndLastK, hEndLastBran]
    · intro j hj
      rw [hEndLastK] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [show exP.d = 1 from rfl, hLastLSF0,
        kruskalLSF_empty_indep (fun _ => 1) (exStEnd.toTreeChain.chainLen exStEnd.ℓ 1), hEndG1]
      exact lsfHolds_mono hLastHolds_len (by
        simp only [exLastParams]
        exact max_le (le_max_left _ _) (le_max_right _ _))
    · intro e he
      rw [show exP.d = 1 from rfl, hEndG1] at he
      cases he
    · intro j hj u hu v hv hC
      rw [hEndLastK] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hLastLSF0]
      rw [show exP.d = 1 from rfl, hEndG1] at hu hv hC
      exact hLastConn u hu v hv hC
    · intro i hi
      have hi0 : i = 0 := by simp [exP] at hi; omega
      subst hi0; simp [hEndBran0, exP]
    · intro i hi
      have hi0 : i = 0 := by simp [exP] at hi; omega
      subst hi0
      rw [hEndG1, hEndSc0, exSt0_sc0]
      rfl
    · intro i hi
      have hi0 : i = 0 := by simp [exP] at hi; omega
      subst hi0; exact ⟨hHist0⟩
    · intro i hi
      have hi0 : i = 0 := by simp [exP] at hi; omega
      subst hi0
      simp [hEndReb0, hEndUpd0, hEndRec]
    · intro i hi
      have hi0 : i = 0 := by simp [exP] at hi; omega
      subst hi0
      rw [hEndCurFwd0, hEndUpd0, hEndRec, hEndRec]
      simp
    · rw [hEndEnc0]
      have hlog : 0 ≤ Real.log ((levelM exSparseParams exP 0 : ℝ) + (exStEnd.updCount 0 : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ levelM exSparseParams exP 0 from Nat.cast_nonneg _,
          show (0 : ℝ) ≤ exStEnd.updCount 0 from Nat.cast_nonneg _])
      rw [Nat.cast_zero]
      positivity
    · intro _
      refine ⟨⟨hHist0, ?_⟩, ?_, ?_⟩
      · simp [hEndLastReb]
      · unfold levelM
        simp only [hEndLastReb, hEndLastCost, hEndG0, exK3_n, exLastParams, exSparseParams]
        rw [show exP.M₀ = 3 from rfl, show exP.k = 3 from rfl, show exP.d = 1 from rfl]
        norm_num
      · simp [hEndLastReb, hEndLastTU]
  have hBud : ChainBudgetInv exSparseParams exLastParams 3 exStEnd := by
    refine ⟨?_, ?_⟩
    · rw [hEndCR]
      have hRest8 : activeRestartCap exSparseParams exP 3 exStEnd.curRestarts = 8 := by
        unfold activeRestartCap restartCostCap
        rw [show exP.d = 1 from rfl, Finset.range_one, Finset.sum_singleton, hEndCRest0]
        simp [exSparseParams, exP]
        norm_num
      have h0_le : 9 ≤ opRuntimeBudget exSparseParams exLastParams exP 3 0 := by
        unfold opRuntimeBudget lastCostCap levelToolCap extraEncCap levelM
        have h1 : 0 ≤ Real.log (10 * 3 * 1 + 2 : ℝ) := Real.log_nonneg (by norm_num)
        have h2 : 0 ≤ Real.log (2 * 3 + 2 : ℝ) := Real.log_nonneg (by norm_num)
        have h3 : 0 ≤ logFactor exP 3 := le_trans zero_le_one (one_le_logFactor exP 3)
        have hPd : exP.d = 1 := rfl
        have hPM : exP.M₀ = 3 := rfl
        have hPk : exP.k = 3 := rfl
        rw [hPd, hPM, hPk]
        simp only [exSparseParams, exLastParams, Nat.lt_one_iff, ↓reduceIte, pow_zero, mul_one,
          Nat.cast_ofNat]
        rw [Finset.sum_Ico_succ_top (by decide : 0 ≤ 0), Finset.Ico_self, Finset.sum_empty, zero_add]
        simp only [↓reduceIte]
        norm_num at h1 h2
        norm_num
        linarith [h1, h2]
      have hTerm0 : (9 : ℝ) ≤ ((exStEnd.shiftCount 0 + exStEnd.rebuildCount 0 : ℕ) : ℝ) *
          opRuntimeBudget exSparseParams exLastParams exP 3 0 := by
        rw [hEndSh0, hEndReb0]; simpa using h0_le
      have hSingle := Finset.single_le_sum (f := fun i =>
          ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) *
            opRuntimeBudget exSparseParams exLastParams exP 3 i)
        (fun i _ => mul_nonneg (Nat.cast_nonneg _)
          (ex_opRuntimeBudget_nonneg exSparseParams exLastParams exP exSparseParams_valid
            exLastParams_valid 3 i))
        (by simp [exP] : 0 ∈ Finset.range (exP.d + 1))
      rw [Nat.cast_one, hRest8]
      linarith [hTerm0, hSingle]
    · have hE0 : exSt0.toTreeChain.chainTree.E = (kruskalLSF exK3 (fun _ => 1)).F.F.E :=
        ex_chainTree_eq_kruskal exSt0 exSt0_sc0 exSt0_lastLSF0
      have hsubK : (kruskalLSF exK3 (fun _ => 1)).F.F.E ⊆ exK3.E :=
        (kruskalLSF_holds exK3_isValid hℓ1).2.1.2.1
      have hcardK : (kruskalLSF exK3 (fun _ => 1)).F.F.E.card ≤ 3 :=
        (Finset.card_le_card hsubK).trans_eq exK3_m
      have hInit_le : exInitCh.length ≤ 3 := by
        have h1 := diffTreeChanges_length_le_add ∅ exSt0.toTreeChain.chainTree.E
        change exInitCh.length ≤ 0 + exSt0.toTreeChain.chainTree.E.card at h1
        rw [hE0] at h1
        omega
      have hclos_le : (exStEnd.closedTreeUpdates : ℝ) ≤ 3 := by
        exact_mod_cast (by omega : exStEnd.closedTreeUpdates ≤ 3)
      have hdiff8 : diffTreeCap exSparseParams exP 0 = 8 := by
        unfold diffTreeCap levelM
        have hPd : exP.d = 1 := rfl
        have hPM : exP.M₀ = 3 := rfl
        have hPk : exP.k = 3 := rfl
        rw [hPd, hPM, hPk]
        simp only [exSparseParams]
        rw [Finset.sum_Ico_succ_top (by decide), Finset.sum_Ico_succ_top (by decide),
          Finset.Ico_self, Finset.sum_empty]
        norm_num
      have hTerm_nn : 0 ≤ ∑ i ∈ Finset.range (exP.d + 1),
          ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * opTreeBudget exSparseParams exP i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
          (opTreeBudget_nonneg exSparseParams_valid exP i)
      linarith
  have hHold : exStEnd.toTreeChain.Holds (exStEnd.G 0) exStEnd.ℓ 3 3 1 1 := by
    refine ⟨rfl, hEndG0 ▸ exK3_isValid, exP.hk, hInv.hLastK, fun i hi => ?_,
      hInv.hLastBran, fun j hj => ?_, fun e he => ?_⟩
    · have hi0 : i = 0 := by change i < 1 at hi; omega
      subst hi0
      refine ⟨hInv.hBran 0 exP.hd, fun j hj => ?_, fun e he => ?_, hInv.hGSucc 0 exP.hd⟩
      · have h0 := hCoreSpec.1 0 (le_refl 0) j hj
        simp only [exSparseParams, constDyn, exK3_n, exK3_m, SparseCoreRestartTool.runAfterRestarts,
          SparseCoreRestartTool.runAfterUpdate, exCoreTool] at h0
        change (exCoreTool.lsfs (exStEnd.scState 0) j).Holds (exStEnd.G 0)
              (exStEnd.toTreeChain.chainLen exStEnd.ℓ 0) (3 : ℝ) ∧
            IsSparsifiedCoreGraphNoSize (exStEnd.G 0) (exCoreTool.lsfs (exStEnd.scState 0) j)
              (exStEnd.toTreeChain.chainLen exStEnd.ℓ 0) 3 1 1
              (exCoreTool.S (exStEnd.scState 0) j) (exCoreTool.emb (exStEnd.scState 0) j)
        rw [hEndG0, hEndSc0, exSt0_sc0]
        simpa [TreeChain.chainLen, hEndℓ, exP, constDyn, exCoreTool] using And.intro h0.1 h0.2.1.toNoSize
      · have hmwu := hCoreSpec.2.2.2.2.2.2.1 0 (le_refl 0) e (hEndG0 ▸ he)
        change (∑ j ∈ Finset.range exP.k, (exCoreTool.lsfs (exStEnd.scState 0) j).wstr e) /
          (exP.k : ℝ) ≤ (3 : ℝ)
        rw [hEndSc0, exSt0_sc0]
        simpa [constDyn, SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate,
          exK3_n, exP, exCoreTool] using hmwu
    · have h0 := hInv.hLastHolds j hj
      exact lsfHolds_mono h0 (by
        have hRc : ((exStEnd.G exP.d).n : ℝ) ≤ 1 := by
          rw [show exP.d = 1 from rfl, hEndG1]
          exact_mod_cast (kruskalLSF_holds exK3_isValid hℓ1).2.2.2 exK3_connected
        simp only [exLastParams]
        exact max_le (by norm_num) (le_trans hRc (by norm_num)))
    · change e ∈ (exStEnd.G 1).E at he
      rw [hEndG1] at he; cases he
  have hSpan : exStEnd.toTreeChain.LastLevelSpans := by
    intro u hu v hv hC
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl, ↓reduceIte]
    exact hInv.hLastSpans exStEnd.lastBran hInv.hLastBran u hu v hv hC
  have hEmbSurv : exStEnd.toTreeChain.EmbedsSurviving := by
    intro i hi e he
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst hi0
    have he' : e ∈ (exStEnd.G 1).E := he
    rw [hEndG1] at he'
    cases he'
  have hTrack : (exInitCh :: [exCh1, exCh2]).foldl applyTreeChanges ∅ =
        exStEnd.toTreeChain.chainTree.E ∧
      exInitCh.length + ([exCh1, exCh2].map List.length).sum ≤ exStEnd.totalTreeUpdates := by
    have hApp0 : applyTreeChanges ∅ exInitCh = exSt0.toTreeChain.chainTree.E :=
      applyTreeChanges_diffTreeChanges _ _
    have hEeq01 : exSt0.toTreeChain.chainTree.E = exStEnd.toTreeChain.chainTree.E := by
      rw [ex_chainTree_eq_kruskal exSt0 exSt0_sc0 exSt0_lastLSF0,
        ex_chainTree_eq_kruskal exStEnd (hEndSc0.trans exSt0_sc0) (by rw [hEndLastBran, hLastLSF0])]
    refine ⟨?_, ?_⟩
    · rw [List.foldl_cons, hApp0, List.foldl_cons, hCh1Nil, List.foldl_cons, hCh2Nil,
        List.foldl_nil]
      simpa [applyTreeChanges] using hEeq01
    · unfold ChainState.totalTreeUpdates
      rw [hEndCTU, hCh1Nil, hCh2Nil, show exP.d = 1 from rfl, Finset.range_one, Finset.sum_singleton,
        hEndDec0, hEndLastTU]
      simp
  have hFC := findCycle_spec_of_holds exStEnd (le_refl (1 : ℝ)) (by simp [hEndG0, hEndℓ])
    hHold hSpan hEmbSurv (by simpa [hEndG0, hEndℓ] using exK3_isValidPair)
  have hSizes : ∀ i ≤ exP.d, ((exStEnd.G i).m : ℝ) ≤ (exP.M₀ : ℝ) * (1 / 3 : ℝ) ^ i := by
    intro i hi
    have hi01 : i = 0 ∨ i = 1 := by simp [exP] at hi; omega
    rcases hi01 with rfl | rfl
    · simp [hEndG0, exK3_m, exP]
    · simp [hEndG1, exG1, MGraph.m]
  refine ⟨exLastParams_valid, exSparseParams_valid, exγk, exLastTool_isSpec, hInv, hBud, hHold,
    hSpan, hEmbSurv, hTrack, hSizes, ?_, ?_, ?_⟩
  · dsimp only
    rcases hFC with ⟨hCirc, hInnerLe, hCard, hNone, hSome⟩
    have hOpt : ∃ e, (algorithm1_findCycle exStEnd).2.2 = some e := by
      cases hopt : (algorithm1_findCycle exStEnd).2.2 with
      | none =>
        have hc0 := (hNone hopt).2.2
        have hsum : (exStEnd.G 0).inner exStEnd.g exCirc = 3 := by
          rw [hEndG0, hEndg]
          unfold MGraph.inner
          rw [show exK3.E = {0, 1, 2} from rfl, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
          simp only [exCirc, exK3, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
            ↓reduceIte]
          norm_num
        linarith
      | some e => exact ⟨e, rfl⟩
    obtain ⟨e, heOpt⟩ := hOpt
    obtain ⟨_, hLnormPos, hRat⟩ := hSome e heOpt
    have hInnerNeg : (exStEnd.G 0).inner exStEnd.g (algorithm1_findCycle exStEnd).1 < 0 := by
      have hcval : |(exStEnd.G 0).inner exStEnd.g exCirc| = 3 := by
        rw [hEndG0, hEndg]
        unfold MGraph.inner
        rw [show exK3.E = {0, 1, 2} from rfl, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
        simp only [exCirc, exK3, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
          ↓reduceIte]
        norm_num
      have hWsum_pos : 0 < ∑ i ∈ Finset.range (exStEnd.toTreeChain.d + 1),
          (exStEnd.toTreeChain.G i).norm1 (exStEnd.toTreeChain.chainW exCirc i) := by
        have h0le := Finset.single_le_sum (f := fun i =>
            (exStEnd.toTreeChain.G i).norm1 (exStEnd.toTreeChain.chainW exCirc i))
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (by simp [exP] : 0 ∈ Finset.range (exStEnd.toTreeChain.d + 1))
        have h0pos : 0 < (exStEnd.toTreeChain.G 0).norm1 (exStEnd.toTreeChain.chainW exCirc 0) := by
          simp [ChainState.toTreeChain, TreeChain.chainW, MGraph.norm1, hEndG0, exK3, exCirc,
            Finset.sum_insert, Finset.sum_singleton]
          norm_num
        linarith
      have hLHS_pos : 0 < (1 / (3 + 1 : ℝ)) *
          (|(exStEnd.G 0).inner exStEnd.g exCirc| /
            ∑ i ∈ Finset.range (exStEnd.toTreeChain.d + 1),
              (exStEnd.toTreeChain.G i).norm1 (exStEnd.toTreeChain.chainW exCirc i)) := by
        rw [hcval]; positivity
      have hAbsPos : 0 < |(exStEnd.G 0).inner exStEnd.g (algorithm1_findCycle exStEnd).1| := by
        have h1 := lt_of_lt_of_le hLHS_pos hRat
        exact div_pos_iff.mp h1 |>.elim And.left fun ⟨_, h⟩ => absurd hLnormPos (not_lt.mpr h.le)
      rcases lt_abs.mp hAbsPos with hpos | hneg
      · exact absurd hpos (not_lt.mpr hInnerLe)
      · exact neg_pos.mp hneg
    exact ⟨hCirc, hInnerNeg, hCard, ⟨e, heOpt⟩, fun _ h => hSome _ h⟩
  · change (exStEnd.totalRuntime : ℝ) ≤
      ((exP.d : ℝ) + 1) * (8 * exSparseParams.c_T + 36 * exLastParams.c_last + 430) *
        (exP.M₀ : ℝ) ^ (1 / (exP.d : ℝ)) *
        (exSparseParams.γ_ℓ (exP.M₀ ^ 2) * exSparseParams.γ_r (exP.M₀ ^ 2)) ^ (3 * exP.d + 1) *
        (2 * logFactor exP 3) ^ (max exSparseParams.p_T exLastParams.p_last + 1) *
        ((exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
          ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i)
    have hrt : exStEnd.totalRuntime = 3 := by
      unfold ChainState.totalRuntime
      rw [show exP.d = 1 from rfl, Finset.range_one, Finset.sum_singleton,
        hEndCR, hEndEnc0, hEndSc0, exSt0_sc0, hEndLastCost]
      simp [exCoreTool]
    have hlog1 : 1 ≤ logFactor exP 3 := one_le_logFactor exP 3
    have hnn : 0 ≤ ∑ i ∈ Finset.range (exP.d + 1),
        ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i :=
      Finset.sum_nonneg fun i hi => mul_nonneg (Nat.cast_nonneg _)
        (le_trans zero_le_one (one_le_powTerm exP (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
    have hSum3 : (3 : ℝ) ≤ (exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
        ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i := by
      rw [show exP.M₀ = 3 from rfl, Nat.cast_ofNat]
      exact le_add_of_nonneg_right hnn
    have hPre : (exStEnd.totalRuntime : ℝ) ≤ (exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
        ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i := by
      rw [hrt]; exact_mod_cast hSum3
    have hC1 : 1 ≤ ((exP.d : ℝ) + 1) * (8 * exSparseParams.c_T + 36 * exLastParams.c_last + 430) *
        (exP.M₀ : ℝ) ^ (1 / (exP.d : ℝ)) *
        (exSparseParams.γ_ℓ (exP.M₀ ^ 2) * exSparseParams.γ_r (exP.M₀ ^ 2)) ^ (3 * exP.d + 1) *
        (2 * logFactor exP 3) ^ (max exSparseParams.p_T exLastParams.p_last + 1) := by
      have hPreCoeff : (1 : ℝ) ≤ ((exP.d : ℝ) + 1) *
          (8 * exSparseParams.c_T + 36 * exLastParams.c_last + 430) *
          (exP.M₀ : ℝ) ^ (1 / (exP.d : ℝ)) *
          (exSparseParams.γ_ℓ (exP.M₀ ^ 2) * exSparseParams.γ_r (exP.M₀ ^ 2)) ^ (3 * exP.d + 1) := by
        simp only [exP, exSparseParams, exLastParams]
        norm_num [Real.rpow_one]
      have hPow1 : 1 ≤ (2 * logFactor exP 3) ^
          (max exSparseParams.p_T exLastParams.p_last + 1) := one_le_pow₀ (by linarith)
      exact one_le_mul_of_one_le_of_one_le hPreCoeff hPow1
    have hPos : 0 ≤ (exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
        ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i := by linarith [hSum3]
    exact le_trans hPre (le_mul_of_one_le_left hPos hC1)
  · change (exStEnd.totalTreeUpdates : ℝ) ≤
      (12 * (exP.d : ℝ) + 18) *
        (exSparseParams.γ_ℓ (exP.M₀ ^ 2) * exSparseParams.γ_r (exP.M₀ ^ 2)) ^ (2 * exP.d + 1) *
        ((exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
          ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i)
    have hE0 : exSt0.toTreeChain.chainTree.E = (kruskalLSF exK3 (fun _ => 1)).F.F.E :=
      ex_chainTree_eq_kruskal exSt0 exSt0_sc0 exSt0_lastLSF0
    have hsubK : (kruskalLSF exK3 (fun _ => 1)).F.F.E ⊆ exK3.E :=
      (kruskalLSF_holds exK3_isValid hℓ1).2.1.2.1
    have hcardK : (kruskalLSF exK3 (fun _ => 1)).F.F.E.card ≤ 3 :=
      (Finset.card_le_card hsubK).trans_eq exK3_m
    have hInit_le : exInitCh.length ≤ 3 := by
      have h1 := diffTreeChanges_length_le_add ∅ exSt0.toTreeChain.chainTree.E
      change exInitCh.length ≤ 0 + exSt0.toTreeChain.chainTree.E.card at h1
      rw [hE0] at h1
      omega
    have hTU : exStEnd.totalTreeUpdates ≤ 3 := by
      unfold ChainState.totalTreeUpdates
      rw [hEndCTU, show exP.d = 1 from rfl, Finset.range_one, Finset.sum_singleton,
        hEndDec0, hEndLastTU]
      omega
    have hTU_real : (exStEnd.totalTreeUpdates : ℝ) ≤ 3 := by exact_mod_cast hTU
    have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (exP.d + 1),
        ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i :=
      Finset.sum_nonneg fun i hi => mul_nonneg (Nat.cast_nonneg _)
        (le_trans zero_le_one (one_le_powTerm exP (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
    have hSum3 : (3 : ℝ) ≤ (exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
        ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i := by
      rw [show exP.M₀ = 3 from rfl, Nat.cast_ofNat]
      exact le_add_of_nonneg_right hnn
    have hCoeff_ge1 : (1 : ℝ) ≤ (12 * (exP.d : ℝ) + 18) *
        (exSparseParams.γ_ℓ (exP.M₀ ^ 2) * exSparseParams.γ_r (exP.M₀ ^ 2)) ^ (2 * exP.d + 1) := by
      simp only [exP, exSparseParams]
      norm_num
    have hPos : 0 ≤ (exP.M₀ : ℝ) + ∑ i ∈ Finset.range (exP.d + 1),
        ((exStEnd.shiftCount i + exStEnd.rebuildCount i : ℕ) : ℝ) * powTerm exP i := by linarith [hSum3]
    exact le_trans hTU_real (le_trans hSum3 (le_mul_of_one_le_left hPos hCoeff_ge1))

end ConcreteRunOnK3

end MinCostFlow.Chain
