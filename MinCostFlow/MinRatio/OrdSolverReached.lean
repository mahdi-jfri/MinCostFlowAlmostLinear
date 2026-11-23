module

public import MinCostFlow.MinRatio.OrdSolverShiftPotential
public import MinCostFlow.MinRatio.OrdSolverHistory
public import MinCostFlow.Chain.Ordered.NextFreshBound
public import MinCostFlow.Chain.Ordered.PreLoopChainInv
import Mathlib.Tactic

/-!
# Reached states of the solver

Some bounds of the solver hold only on the states that Algorithm 2 reaches from `Init`: the
bound on the next fresh name (`alg2_nextFresh_le_with`) and the recourse bound
`FwdBoundNat` before and after the shift loop (`ChainInv.hRecFwd`). The theorems of
`Chain/Ordered/` prove them along a valid history. This file records, as a property of one state,
that a valid history reaches it (`OrdSolverReached`), and shows that `Init`, `Update` and
`Detect` keep this property.

* `histSnoc D T G U g l` appends one stage to a history; `seqSnoc f T a` does the same for the
  operation kinds and the normalizations. The states up to stage `T` do not change
  (`minRatioFailState_snoc_of_le`), and stage `T + 1` is one more operation
  (`minRatioFailState_snoc_succ`). The longer history is valid when the new stage is
  (`histSnoc_valid`).
* `OrdSolverReached cfg κ G model`: a valid, edge-only history with lengths in the range of
  `cfg.Ψ`, whose graphs are all `G`, reaches `model`.
* `ordSolverReached_init`, `ordSolverReached_update`, `ordSolverReached_detect`.
* What it gives: `OrdSolverReached.nextFresh_le`, `OrdSolverReached.fwd` and
  `OrdSolverReached.preLoop_fwd`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain IPM IPM.Machine

/-! ## Appending one stage to a history -/

/-- The sequence `f` up to stage `T`, and `a` after it. -/
@[expose] def seqSnoc {α : Type} (f : ℕ → α) (T : ℕ) (a : α) : ℕ → α :=
  fun t => if t ≤ T then f t else a

/-- The history `D` up to stage `T`, and then the graph `G`, the batch `U`, the gradients `g`
and the lengths `l` at every later stage. Only stage `T + 1` is used. -/
@[expose] def histSnoc (D : DynamicInstance) (T : ℕ) (G : MGraph) (U : List Update)
    (g l : ℕ → ℝ) : DynamicInstance where
  G := seqSnoc D.G T G
  U := seqSnoc D.U T U
  g := seqSnoc D.g T g
  ℓ := seqSnoc D.ℓ T l

theorem seqSnoc_of_le {α : Type} (f : ℕ → α) {T t : ℕ} (a : α) (ht : t ≤ T) :
    seqSnoc f T a t = f t := if_pos ht

theorem seqSnoc_succ {α : Type} (f : ℕ → α) (T : ℕ) (a : α) : seqSnoc f T a (T + 1) = a :=
  if_neg (by omega)

/-- Appending a stage does not change the states up to stage `T`: the state at stage `t` reads
the history only at stages `≤ t`. -/
theorem minRatioFailState_snoc_of_le (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (G : MGraph) (U : List Update) (g l : ℕ → ℝ)
    (a : ℝ) (b : Bool) :
    ∀ t ≤ T, minRatioFailState A (histSnoc D T G U g l) (seqSnoc η T a) (seqSnoc op T b) t =
      minRatioFailState A D η op t := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [minRatioFailState, histSnoc, seqSnoc_of_le _ _ (Nat.zero_le T)]
  | succ t ih =>
    intro ht
    rw [minRatioFailState.eq_2, minRatioFailState.eq_2, ih (by omega)]
    simp only [histSnoc, seqSnoc_of_le _ _ ht]

/-- Stage `T + 1` of the longer history is the operation `b` on the state at stage `T`. -/
theorem minRatioFailState_snoc_succ (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (G : MGraph) (U : List Update) (g l : ℕ → ℝ)
    (a : ℝ) (b : Bool) :
    minRatioFailState A (histSnoc D T G U g l) (seqSnoc η T a) (seqSnoc op T b) (T + 1) =
      if b then (A.update (minRatioFailState A D η op T) U g l a).1
      else (A.detect (minRatioFailState A D η op T)).2 := by
  rw [minRatioFailState.eq_2, minRatioFailState_snoc_of_le A D η op T G U g l a b T le_rfl]
  simp only [histSnoc, seqSnoc_succ]

/-- **The longer history is valid** when the new stage is: the batch is valid on `G` and keeps
`G`, the new lengths are positive, a `Detect` stage changes nothing, and the new vectors agree
with those of stage `T` on the edges that the batch does not insert. -/
theorem histSnoc_valid {D : DynamicInstance} {op : ℕ → Bool} {T : ℕ} {G : MGraph}
    {U : List Update} {g l : ℕ → ℝ} {b : Bool} (hV : MinRatioHistoryValid D op T)
    (hG : D.G T = G) (hU : G.BatchIsValid U) (hGU : G.applyBatch U = G)
    (hl : ∀ e ∈ G.E, 0 < l e) (hdet : b = false → U = [] ∧ g = D.g T ∧ l = D.ℓ T)
    (hagree : ∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → g e = D.g T e ∧ l e = D.ℓ T e) :
    MinRatioHistoryValid (histSnoc D T G U g l) (seqSnoc op T b) (T + 1) := by
  have hGV : G.IsValid := hG ▸ (hV.2.1 T le_rfl).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht1 ht2
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [histSnoc, seqSnoc_succ, Nat.add_sub_cancel, seqSnoc_of_le _ _ le_rfl, hG]
      exact ⟨hU, hGU.symm⟩
    · simp only [histSnoc, seqSnoc_of_le _ _ hle, seqSnoc_of_le _ _ (by omega : t - 1 ≤ T)]
      exact hV.1 t ht1 hle
  · intro t ht
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [histSnoc, seqSnoc_succ]
      exact ⟨hGV, hl⟩
    · simp only [histSnoc, seqSnoc_of_le _ _ hle]
      exact hV.2.1 t hle
  · intro t ht1 ht2 hop
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [seqSnoc_succ] at hop
      obtain ⟨h1, h2, h3⟩ := hdet hop
      simp only [histSnoc, seqSnoc_succ, Nat.add_sub_cancel, seqSnoc_of_le _ _ le_rfl]
      exact ⟨h1, h2, h3⟩
    · simp only [seqSnoc_of_le _ _ hle] at hop
      simp only [histSnoc, seqSnoc_of_le _ _ hle, seqSnoc_of_le _ _ (by omega : t - 1 ≤ T)]
      exact hV.2.2.1 t ht1 hle hop
  · intro t ht1 ht2 e he hnot
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [histSnoc, seqSnoc_succ, Nat.add_sub_cancel, seqSnoc_of_le _ _ le_rfl] at he ⊢
      refine hagree e he fun u hu hins => hnot (T + 1) (by omega) le_rfl u ?_ hins
      simp only [histSnoc, seqSnoc_succ]
      exact hu
    · have hnot' : D.NotInsertedBetween e (t - 1) t := by
        intro s hs1 hs2 u hu hins
        refine hnot s hs1 hs2 u ?_ hins
        simp only [histSnoc, seqSnoc_of_le _ _ (hs2.trans hle)]
        exact hu
      simp only [histSnoc, seqSnoc_of_le _ _ hle, seqSnoc_of_le _ _ (by omega : t - 1 ≤ T)] at he ⊢
      exact hV.2.2.2 t ht1 hle e he hnot'

/-- The longer history is edge-only when the new batch is. -/
theorem histSnoc_edgeOnly {D : DynamicInstance} {T : ℕ} {G : MGraph} {U : List Update}
    {g l : ℕ → ℝ} (h : Ordered.HistoryEdgeOnly D T) (hU : ∀ u ∈ U, Bundle.IsEdgeUpdate u) :
    Ordered.HistoryEdgeOnly (histSnoc D T G U g l) (T + 1) := by
  intro t ht1 ht2 u hu
  rcases Nat.lt_or_ge T t with hlt | hle
  · have htT : t = T + 1 := by omega
    subst htT
    simp only [histSnoc, seqSnoc_succ] at hu
    exact hU u hu
  · simp only [histSnoc, seqSnoc_of_le _ _ hle] at hu
    exact h t ht1 hle u hu

/-- The longer history has its lengths in range when the new lengths are. -/
theorem histSnoc_lengths {D : DynamicInstance} {T : ℕ} {G : MGraph} {U : List Update}
    {g l : ℕ → ℝ} {Ψ : ℝ} (h : Ordered.HistoryLengthsInRange D T Ψ)
    (hl : ∀ e ∈ G.E, |Real.log (l e)| ≤ Ψ) :
    Ordered.HistoryLengthsInRange (histSnoc D T G U g l) (T + 1) Ψ := by
  intro t ht e he
  rcases Nat.lt_or_ge T t with hlt | hle
  · have htT : t = T + 1 := by omega
    subst htT
    simp only [histSnoc, seqSnoc_succ] at he ⊢
    exact hl e he
  · simp only [histSnoc, seqSnoc_of_le _ _ hle] at he ⊢
    exact h t hle e he

/-! ## Reached states -/

/-- The state `model` of ordered Algorithm 2 is reached on the fixed graph `G`: a valid history
(`MinRatioHistoryValid`) of edge-only batches (`HistoryEdgeOnly`), with lengths in the range of
`cfg.Ψ` (`HistoryLengthsInRange`) and the graph `G` at every stage, reaches it. These are the
hypotheses of the history theorems of `Chain/Ordered/` (`algorithm2_uncond_preserves_with`),
except for the size bounds on `G`, which do not depend on the history. -/
@[expose] def OrdSolverReached (cfg : Alg2Config) (κ : ℝ) (G : MGraph) (model : Alg2State cfg) :
    Prop :=
  ∃ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ),
    MinRatioHistoryValid D op T ∧ Ordered.HistoryEdgeOnly D T ∧
    Ordered.HistoryLengthsInRange D T cfg.Ψ ∧ (∀ t ≤ T, D.G t = G) ∧
    model = minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T

/-- The state of the history theorems is the state of the failure-erased structure that
`ordAlg2_minRatioState_ext` speaks about: both run the same operations. -/
theorem minRatioFailState_eq_minRatioState (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) :
    ∀ T, minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T =
      minRatioState (Ordered.algorithm2_dsWithFailureWith cfg κ).eraseFailure D η op T
  | 0 => rfl
  | T + 1 => by
    simp only [minRatioFailState, minRatioState, minRatioFailState_eq_minRatioState cfg κ D η op T]
    rfl

/-- On a reached state, the stored gradients and lengths are those of the history's last stage
(`ordAlg2_minRatioState_ext`). -/
theorem OrdSolverReached.ext {cfg : Alg2Config} {κ : ℝ} {model : Alg2State cfg}
    {D : DynamicInstance} {η : ℕ → ℝ} {op : ℕ → Bool} {T : ℕ} (hV : MinRatioHistoryValid D op T)
    (hm : model = minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T) :
    model.extg = D.g T ∧ model.extℓ = D.ℓ T := by
  rw [hm, minRatioFailState_eq_minRatioState]
  exact ordAlg2_minRatioState_ext cfg κ D η op T hV

/-- **Init reaches its state**, by the history with no operation, when the graph is valid and
the lengths are positive and in the range of `cfg.Ψ`. -/
theorem ordSolverReached_init (cfg : Alg2Config) (κ : ℝ) (G : MGraph) (g l : ℕ → ℝ)
    (hG : G.IsValid) (hl : ∀ e ∈ G.E, 0 < l e) (hlR : ∀ e ∈ G.E, |Real.log (l e)| ≤ cfg.Ψ) :
    OrdSolverReached cfg κ G (Ordered.algorithm2_init cfg G g l) := by
  refine ⟨⟨fun _ => G, fun _ => [], fun _ => g, fun _ => l⟩, fun _ => 0, fun _ => false, 0,
    ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, fun _ _ => rfl, rfl⟩
  · intro t ht ht'; omega
  · intro t _; exact ⟨hG, hl⟩
  · intro t ht ht' _; omega
  · intro t ht ht' _ _ _; omega
  · intro t ht ht'; omega
  · intro t _ e he; exact hlR e he

/-- **Update keeps the state reached.** The batch is a refresh batch of `G`, the new lengths are
positive and in the range of `cfg.Ψ`, and the new vectors agree with the stored ones on the edges
of `G` that the batch does not insert. Then the state after the `Update` is reached, by the
history with one more stage. -/
theorem ordSolverReached_update {cfg : Alg2Config} {κ : ℝ} {G : MGraph} {model : Alg2State cfg}
    (h : OrdSolverReached cfg κ G model) {U : List Update} {g l : ℕ → ℝ} (a : ℝ)
    (hU : RefreshBatch G U) (hl : ∀ e ∈ G.E, 0 < l e)
    (hlR : ∀ e ∈ G.E, |Real.log (l e)| ≤ cfg.Ψ)
    (hagree : ∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → g e = model.extg e ∧ l e = model.extℓ e) :
    OrdSolverReached cfg κ G ((Ordered.algorithm2_dsWith cfg κ).update model U g l a).1 := by
  obtain ⟨D, η, op, T, hV, hE, hL, hG, hm⟩ := h
  obtain ⟨hgx, hlx⟩ := OrdSolverReached.ext hV hm
  have hEdgeU : ∀ u ∈ U, Bundle.IsEdgeUpdate u := by
    intro u hu
    have := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd this id
  refine ⟨histSnoc D T G U g l, seqSnoc η T a, seqSnoc op T true, T + 1,
    histSnoc_valid hV (hG T le_rfl) hU.1 hU.2.1 hl (fun h => absurd h (by decide)) ?_,
    histSnoc_edgeOnly hE hEdgeU, histSnoc_lengths hL hlR, ?_, ?_⟩
  · intro e he hnot
    rw [← hgx, ← hlx]
    exact hagree e he hnot
  · intro t ht
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [histSnoc, seqSnoc_succ]
    · simp only [histSnoc, seqSnoc_of_le _ _ hle]
      exact hG t hle
  · rw [minRatioFailState_snoc_succ, ← hm]
    rfl

/-- **Detect keeps the state reached**, by the history with one more stage that changes
nothing. -/
theorem ordSolverReached_detect {cfg : Alg2Config} {κ : ℝ} {G : MGraph} {model : Alg2State cfg}
    (h : OrdSolverReached cfg κ G model) :
    OrdSolverReached cfg κ G (algorithm2_detect cfg model).2 := by
  obtain ⟨D, η, op, T, hV, hE, hL, hG, hm⟩ := h
  have hGT := hG T le_rfl
  refine ⟨histSnoc D T G [] (D.g T) (D.ℓ T), seqSnoc η T 0, seqSnoc op T false, T + 1,
    histSnoc_valid hV hGT trivial rfl (fun e he => (hV.2.1 T le_rfl).2 e (hGT ▸ he))
      (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩),
    histSnoc_edgeOnly hE (fun u hu => absurd hu List.not_mem_nil),
    histSnoc_lengths hL (fun e he => hL T le_rfl e (hGT ▸ he)), ?_, ?_⟩
  · intro t ht
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [histSnoc, seqSnoc_succ]
    · simp only [histSnoc, seqSnoc_of_le _ _ hle]
      exact hG t hle
  · rw [minRatioFailState_snoc_succ, ← hm]
    rfl

/-! ## What a reached state gives -/

/-- **The bound on the next fresh name** (`alg2_nextFresh_le_with`) on a reached
state, when `G` has at most `M₀` edges and at most `N₀` vertices. -/
theorem OrdSolverReached.nextFresh_le {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀) :
    model.nextFresh ≤ Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  have h1 := Ordered.alg2_nextFresh_le_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG) T le_rfl
  rw [hG 0 (Nat.zero_le T)] at h1
  rw [hm]
  exact h1

/-- **The recourse bound on a reached state**: `curFwd j ≤ Γ · updCount j` for
`Γ = fwdGamma cfg`, from `ChainInv.hRecFwd` (`algorithm2_uncond_preserves_with`). -/
theorem OrdSolverReached.fwd {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀) :
    FwdBoundNat cfg.P (fwdGamma cfg) model.chain := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  have hInv := ((Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl).1
  rw [hm]
  exact fwdBoundNat_of_chainRecBound hInv.hRecFwd

/-- **The recourse bound before the shift loop.** On a reached state, for an `Update` that keeps
the state reached (the hypotheses of `ordSolverReached_update`), the chain that the shift loop
starts from meets `FwdBoundNat`. It is the chain at the last stage of the longer history before
its shift loop, so `alg2_preLoop_chainInv_with` applies. -/
theorem OrdSolverReached.preLoop_fwd {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀) {U : List Update} {g l : ℕ → ℝ}
    (hU : RefreshBatch G U) (hl : ∀ e ∈ G.E, 0 < l e)
    (hlR : ∀ e ∈ G.E, |Real.log (l e)| ≤ cfg.Ψ)
    (hagree : ∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → g e = model.extg e ∧ l e = model.extℓ e) :
    FwdBoundNat cfg.P (fwdGamma cfg) (alg2PreLoopState cfg model U g l).chain := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  obtain ⟨hgx, hlx⟩ := OrdSolverReached.ext hHist hm
  have hEdgeU : ∀ u ∈ U, Bundle.IsEdgeUpdate u := by
    intro u hu
    have := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd this id
  have hV' := histSnoc_valid (b := true) hHist (hG T le_rfl) hU.1 hU.2.1 hl
    (fun h => absurd h (by decide)) (fun e he hnot => by rw [← hgx, ← hlx]; exact hagree e he hnot)
  have hG' : ∀ t ≤ T + 1, (histSnoc D T G U g l).G t = G := by
    intro t ht
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [histSnoc, seqSnoc_succ]
    · simp only [histSnoc, seqSnoc_of_le _ _ hle]
      exact hG t hle
  have hInv := Ordered.alg2_preLoop_chainInv_with (η := seqSnoc η T 0) κ hV hV'
    (histSnoc_edgeOnly hE hEdgeU) (histSnoc_lengths hL hlR)
    (fun t ht => by rw [hG' t ht]; exact hmG) (fun t ht => by rw [hG' t ht]; exact hnG) T le_rfl
  dsimp only at hInv
  rw [minRatioFailState_snoc_of_le _ D η op T G U g l 0 true T le_rfl, ← hm] at hInv
  simp only [histSnoc, seqSnoc_succ] at hInv
  exact fwdBoundNat_of_chainRecBound hInv.hRecFwd

end MinCostFlow.MinRatio

end
