module

public import MinCostFlow.MinRatio.LastLevelContract
public import MinCostFlow.Chain.SparseCoreRestart
public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.MinRatio.SparseCoreContractState
public import MinCostFlow.SparseCore.LastLevel
import MinCostFlow.MinRatio.RebuildModelSuffix
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Input agreement at the terminal rebuild

Algorithm 1 (page 20) passes the chain lengths to the terminal builder.
The machine decoder extends its live-edge table by zero. The terminal
specification observes live branches, while equality of the entire
builder result also observes the unused entries of its branch function.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

private def recordLengthInUnusedBranch (tool : LastLevelTool) (e : ℕ) : LastLevelTool where
  build G length :=
    let result := tool.build G length
    (result.1, fun j => if j = result.1 then
      { result.2 j with wstr := fun _ => length e } else result.2 j)
  cost := tool.cost

private theorem recordLengthInUnusedBranch_isSpec {tool : LastLevelTool}
    {P : LastLevelParams} (h : tool.IsSpec P) (e : ℕ) :
    (recordLengthInUnusedBranch tool e).IsSpec P := by
  intro G length hG hlength
  obtain ⟨hk, holds, avg, spans, cost⟩ := h G length hG hlength
  dsimp only [recordLengthInUnusedBranch]
  refine ⟨hk, ?_, ?_, ?_, cost⟩
  · intro j hj
    simpa only [ite_eq_right (Nat.ne_of_lt hj)] using holds j hj
  · intro f hf
    have he :
        (∑ j ∈ Finset.range (tool.build G length).1,
          (if j = (tool.build G length).1 then
            { (tool.build G length).2 j with wstr := fun _ => length e }
          else (tool.build G length).2 j).wstr f) =
        ∑ j ∈ Finset.range (tool.build G length).1, ((tool.build G length).2 j).wstr f := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [ite_eq_right (Nat.ne_of_lt (Finset.mem_range.mp hj))]
    rw [he]
    exact avg f hf
  · intro j hj u hu v hv hconn
    simpa only [ite_eq_right (Nat.ne_of_lt hj)] using spans j hj u hu v hv hconn

/-- The terminal spec does not imply equality of complete builder results
from equality of lengths on live graph edges. -/
theorem lastLevelSpec_not_exact_of_live_agreement {tool : LastLevelTool}
    {P : LastLevelParams} (h : tool.IsSpec P) {G : MGraph} {e : ℕ} (he : e ∉ G.E) :
    ∃ tool' : LastLevelTool, tool'.IsSpec P ∧
      ∃ l₀ l₁ : ℕ → ℝ, (∀ a ∈ G.E, l₀ a = l₁ a) ∧
        (∀ a ∈ G.E, 0 < l₀ a) ∧ tool'.build G l₀ ≠ tool'.build G l₁ := by
  let tool' := recordLengthInUnusedBranch tool e
  let l₀ : ℕ → ℝ := fun _ => 1
  let l₁ : ℕ → ℝ := fun a => if a = e then 0 else 1
  refine ⟨tool', recordLengthInUnusedBranch_isSpec h e, l₀, l₁, ?_, ?_, ?_⟩
  · intro a ha
    have hne : a ≠ e := fun eq => he (eq ▸ ha)
    simp [l₀, l₁, hne]
  · intro a ha
    simp [l₀]
  · intro eq
    have hk := congrArg Prod.fst eq
    change (tool.build G l₀).1 = (tool.build G l₁).1 at hk
    have hw := congrArg (fun p : ℕ × (ℕ → LSF) =>
      (p.2 (tool.build G l₀).1).wstr e) eq
    simp [tool', recordLengthInUnusedBranch, hk, l₀, l₁] at hw

private def recordSparseCoreLength (tool : SparseCoreRestartTool) (e : ℕ) :
    SparseCoreRestartTool where
  State := tool.State × ℝ
  init k M N G length grad := (tool.init k M N G length grad, length e)
  update state batch length grad :=
    let result := tool.update state.1 batch length grad
    ((result.1, state.2), result.2)
  lsfs state := tool.lsfs state.1
  S state := tool.S state.1
  emb state := tool.emb state.1
  cost state := tool.cost state.1
  restart state branch := (tool.restart state.1 branch, state.2)

private theorem recordSparseCoreLength_fold (tool : SparseCoreRestartTool) (e : ℕ)
    (branches : List ℕ) (state : (recordSparseCoreLength tool e).State) :
    (branches.foldl (recordSparseCoreLength tool e).restart state).1 =
      branches.foldl tool.restart state.1 := by
  induction branches generalizing state with
  | nil => rfl
  | cons branch rest ih => exact ih ((recordSparseCoreLength tool e).restart state branch)

private theorem recordSparseCoreLength_pre (tool : SparseCoreRestartTool) (e k M N : ℕ)
    (D : DynamicInstance) (restarts : ℕ → List ℕ) (t : ℕ) :
    let result := (recordSparseCoreLength tool e).runAfterUpdate k M N D restarts t
    (result.1.1, result.2) = tool.runAfterUpdate k M N D restarts t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := congrArg Prod.fst ih
    dsimp only at hi
    simp only [SparseCoreRestartTool.runAfterUpdate, recordSparseCoreLength_fold,
      show ∀ s batch length grad, ((recordSparseCoreLength tool e).update s batch length grad).1.1 =
        (tool.update s.1 batch length grad).1 from fun _ _ _ _ => rfl,
      show ∀ s batch length grad, ((recordSparseCoreLength tool e).update s batch length grad).2 =
        (tool.update s.1 batch length grad).2 from fun _ _ _ _ => rfl, hi]

private theorem recordSparseCoreLength_post (tool : SparseCoreRestartTool) (e k M N : ℕ)
    (D : DynamicInstance) (restarts : ℕ → List ℕ) (t : ℕ) :
    ((recordSparseCoreLength tool e).runAfterRestarts k M N D restarts t).1 =
      tool.runAfterRestarts k M N D restarts t := by
  unfold SparseCoreRestartTool.runAfterRestarts
  rw [recordSparseCoreLength_fold]
  exact congrArg (List.foldl tool.restart · (restarts t))
    (congrArg Prod.fst (recordSparseCoreLength_pre tool e k M N D restarts t))

private theorem recordSparseCoreLength_isSpec {tool : SparseCoreRestartTool} {P : SparseCoreParams}
    (h : tool.IsSpecRestart P) (e : ℕ) : (recordSparseCoreLength tool e).IsSpecRestart P := by
  intro k τ M N D restarts Ψ c w hk hG hD hstable hhidden hm hn hrest hth
  have hp t := congrArg Prod.fst (recordSparseCoreLength_pre tool e k M N D restarts t)
  have hu t := congrArg Prod.snd (recordSparseCoreLength_pre tool e k M N D restarts t)
  dsimp only at hp hu
  have hlsfs : ∀ s j, (recordSparseCoreLength tool e).lsfs s j = tool.lsfs s.1 j :=
    fun _ _ => rfl
  have hS : ∀ s j, (recordSparseCoreLength tool e).S s j = tool.S s.1 j := fun _ _ => rfl
  have hemb : ∀ s j, (recordSparseCoreLength tool e).emb s j = tool.emb s.1 j := fun _ _ => rfl
  have hcost : ∀ s, (recordSparseCoreLength tool e).cost s = tool.cost s.1 := fun _ => rfl
  have hr : ∀ s j, ((recordSparseCoreLength tool e).restart s j).1 = tool.restart s.1 j :=
    fun _ _ => rfl
  have hC s₀ j : (recordSparseCoreLength tool e).coreCFrom k M N D restarts c s₀ j =
      tool.coreCFrom k M N D restarts c s₀ j := by
    funext δ
    simp only [SparseCoreRestartTool.coreCFrom, hlsfs, hemb, recordSparseCoreLength_post]
  have hW s₀ j : (recordSparseCoreLength tool e).coreWFrom k M N D restarts w s₀ j =
      tool.coreWFrom k M N D restarts w s₀ j := by
    funext δ
    simp only [SparseCoreRestartTool.coreWFrom, hlsfs, hemb, recordSparseCoreLength_post]
  dsimp only
  simp only [hlsfs, hS, hemb, hcost, hr, recordSparseCoreLength_fold,
    recordSparseCoreLength_post, hp, hu, SparseCoreRestartTool.coreInstanceFrom, hC, hW]
  have hs := h k τ M N D restarts Ψ c w hk hG hD hstable hhidden hm hn hrest hth
  simpa only [SparseCoreRestartTool.coreInstanceFrom] using hs

/-- Lemma 5.17's run-with-restarts specification cannot force an opaque
state to ignore lengths outside the active edge set. -/
theorem sparseCoreSpec_not_exact_of_live_agreement {tool : SparseCoreRestartTool}
    {P : SparseCoreParams} (h : tool.IsSpecRestart P) {G : MGraph} {e : ℕ} (he : e ∉ G.E)
    (k M N : ℕ) :
    ∃ tool' : SparseCoreRestartTool, tool'.IsSpecRestart P ∧
      ∃ l₀ l₁ : ℕ → ℝ, (∀ a ∈ G.E, l₀ a = l₁ a) ∧
        (∀ a ∈ G.E, 0 < l₀ a) ∧ tool'.init k M N G l₀ (fun _ => 0) ≠ tool'.init k M N G l₁ (fun _ => 0) := by
  let tool' := recordSparseCoreLength tool e
  let l₀ : ℕ → ℝ := fun _ => 1
  let l₁ : ℕ → ℝ := fun a => if a = e then 0 else 1
  refine ⟨tool', recordSparseCoreLength_isSpec h e, l₀, l₁, ?_, ?_, ?_⟩
  · intro a ha
    have hne : a ≠ e := fun eq => he (eq ▸ ha)
    simp [l₀, l₁, hne]
  · intro a ha
    simp [l₀]
  · intro eq
    have hh := congrArg (fun s : tool'.State => (show tool.State × ℝ from s).2) eq
    change l₀ e = l₁ e at hh
    simp [l₀, l₁] at hh

private theorem minLenRepEdge_eq_on_live (G : MGraph) {len len' : ℕ → ℝ}
    (h : ∀ e ∈ G.E, len e = len' e) (p : ℕ × ℕ) :
    SparseCore.minLenRepEdge G len p = SparseCore.minLenRepEdge G len' p := by
  classical
  unfold SparseCore.minLenRepEdge
  dsimp only
  split_ifs with hn
  · let S := (SparseCore.nonLoopEdges G).filter (fun e => SparseCore.edgePairKey G e = p)
    have hS (e : ℕ) (he : e ∈ S) : e ∈ G.E :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    have hp : (fun e => e ∈ S ∧ ∀ f ∈ S, len e ≤ len f) =
        (fun e => e ∈ S ∧ ∀ f ∈ S, len' e ≤ len' f) := by
      funext e
      by_cases he : e ∈ S
      · apply propext
        simp only [he, true_and]
        constructor <;> intro hh f hf
        · rw [← h e (hS e he), ← h f (hS f hf)]
          exact hh f hf
        · rw [h e (hS e he), h f (hS f hf)]
          exact hh f hf
      · simp [he]
    change @Classical.choose ℕ _ (Finset.exists_min_image S len hn) =
      @Classical.choose ℕ _ (Finset.exists_min_image S len' hn)
    let left : { p : ℕ → Prop // ∃ a, p a } :=
      ⟨_, Finset.exists_min_image S len hn⟩
    let right : { p : ℕ → Prop // ∃ a, p a } :=
      ⟨_, Finset.exists_min_image S len' hn⟩
    have heq : left = right := Subtype.ext hp
    exact congrArg (fun q : { p : ℕ → Prop // ∃ a, p a } => Classical.choose q.2) heq
  · rfl

/-- The concrete terminal builder depends only on lengths of live edges.
The representative choices have identical predicates, and the oracle
receives the same zero-extended lengths at every MWU iteration. -/
theorem concreteLastLevel_build_eq_on_live
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) {len len' : ℕ → ℝ} (h : ∀ e ∈ G.E, len e = len' e) :
    (SparseCore.lastLevelTool oracle C).build G len =
      (SparseCore.lastLevelTool oracle C).build G len' := by
  have hrep : SparseCore.minLenRepEdge G len = SparseCore.minLenRepEdge G len' :=
    funext (minLenRepEdge_eq_on_live G h)
  have hgraph : SparseCore.simpleMinLenSubgraph G len = SparseCore.simpleMinLenSubgraph G len' := by
    simp only [SparseCore.simpleMinLenSubgraph, hrep]
  let H := SparseCore.simpleMinLenSubgraph G len'
  have hsafe : LSF.safeLen H len = LSF.safeLen H len' := by
    funext e
    by_cases he : e ∈ H.E
    · have he' : e ∈ G.E := by
        change e ∈ ((SparseCore.nonLoopEdges G).image (SparseCore.edgePairKey G)).image
          (SparseCore.minLenRepEdge G len') at he
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
        exact (Finset.mem_filter.mp (SparseCore.minLenRepEdge_spec (ℓ := len') hf).1).1
      simp [LSF.safeLen, he, h e he']
    · simp [LSF.safeLen, he]
  have hweights (j : ℕ) :
      SparseCore.lastMWUWeights oracle C H len j = SparseCore.lastMWUWeights oracle C H len' j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      funext e
      simp only [SparseCore.lastMWUWeights, ih, hsafe]
  unfold SparseCore.lastLevelTool
  change (if _ : (SparseCore.nonLoopEdges G).Nonempty then _ else _) =
    (if _ : (SparseCore.nonLoopEdges G).Nonempty then _ else _)
  split_ifs
  · simp only [hgraph]
    simp only [show LSF.safeLen (SparseCore.simpleMinLenSubgraph G len') len =
      LSF.safeLen (SparseCore.simpleMinLenSubgraph G len') len' from hsafe,
      show ∀ j, SparseCore.lastMWUWeights oracle C (SparseCore.simpleMinLenSubgraph G len') len j =
        SparseCore.lastMWUWeights oracle C (SparseCore.simpleMinLenSubgraph G len') len' j from hweights, hrep]
  · rfl

end MinCostFlow.MinRatio
