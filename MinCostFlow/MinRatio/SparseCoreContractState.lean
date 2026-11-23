module

public import MinCostFlow.MinRatio.SparseCoreContract

/-!
# Model state at sparse-core machine boundaries

The initialization, update, and restart postconditions imply the matching
model transitions of Lemma 5.17 (page 23) and the corrected Shift. The
proofs extend the input-graph history one operation at a time. Readouts
leave the model state unchanged. These lemmas use the contract only and
make no claim that a machine program already implements it.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program Chain

variable {w : ℕ} {fmt : Num.Format w} {L : ℕ} {tool : SparseCoreRestartTool}
  {initialGraph : MGraph} {k M N vCap eCap : ℕ}
  {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}

/-- Initialization supplies a valid history for the exact initial model graph. -/
theorem sparseCoreMachineContract_init_input {args : List ℕ} {mem mem' : ℕ → ℕ}
    {s : tool.State}
    (hpre : (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).initPre
      args mem)
    (hpost : (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).initPost
      args mem s mem') :
    SparseCoreInput tool.toSparseCoreTool tool.restart k s initialGraph := by
  rcases hpre with ⟨graph, lengths, gradient, heap, rfl, _, hG, _⟩
  rw [hpost]
  exact .init M N _ _ _ hG.1

/-- Prepared named graphs and fixed-point tables supply the sparse-core
initialization precondition (Lemma 5.17, page 23). Only live lengths are tested. -/
theorem sparseCoreMachineContract_initPre_of_tables {graph lengths gradient heap : ℕ}
    {mem : ℕ → ℕ} {ℓ g : ℕ → ℝ}
    (hk : 0 < k) (hG : DynGraphAt mem graph vCap eCap initialGraph)
    (hm : initialGraph.m ≤ M) (hn : initialGraph.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt mem lengths fmt.limbBits L fmt.precision initialGraph.E ℓ)
    (hg : EdgeValuesAt mem gradient fmt.limbBits L fmt.precision initialGraph.E g)
    (hpos : ∀ e ∈ initialGraph.E, 0 < ℓ e) :
    (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).initPre
      [graph, lengths, gradient, heap] mem := by
  refine ⟨graph, lengths, gradient, heap, rfl, hk, hG, hm, hn, hgraph, hLenRoom, hGradRoom,
    fun e he => ⟨(hℓ e he).1, (hg e he).1⟩, fun e he => ?_⟩
  rw [readEdgeValues_eq hℓ he]
  exact hpos e he

/-- The initializer matches the model call when both source tables
represent the live values and the model uses their zero extension. -/
theorem sparseCoreMachineContract_init_model {graph lengths gradient heap : ℕ}
    {mem mem' : ℕ → ℕ} {s : tool.State} {ℓ g : ℕ → ℝ}
    (hℓ : EdgeValuesAt mem lengths fmt.limbBits L fmt.precision initialGraph.E ℓ)
    (hg : EdgeValuesAt mem gradient fmt.limbBits L fmt.precision initialGraph.E g)
    (hℓzero : ∀ e ∉ initialGraph.E, ℓ e = 0)
    (hgzero : ∀ e ∉ initialGraph.E, g e = 0)
    (hpost : (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).initPost
      [graph, lengths, gradient, heap] mem s mem') :
    s = tool.init k M N initialGraph ℓ g := by
  change s = tool.init k M N initialGraph
    (readEdgeValues mem lengths fmt.limbBits L fmt.precision initialGraph.E)
    (readEdgeValues mem gradient fmt.limbBits L fmt.precision initialGraph.E) at hpost
  simpa only [readEdgeValues_eq_of_support hℓ hℓzero, readEdgeValues_eq_of_support hg hgzero]
    using hpost

/-- Definition 5.6 (page 18) multiplies stretch by the input length.
When the stretch denominator stores that length, its numerator table
already represents the next graph's lengths on every surviving edge. -/
theorem coreLengthAt_of_stretch_numerator {mem : ℕ → ℕ} {a h L P : ℕ}
    {E F : Finset ℕ} {forest : LSF} {ℓ : ℕ → ℝ}
    (hsubset : F ⊆ E)
    (hst : StretchValuesAt mem a h L P E forest.wstr)
    (hlen : EdgeValuesAt mem (mem (a + 1)) h L P E ℓ) :
    EdgeValuesAt mem (mem a) h L P F (coreLen forest ℓ) := by
  intro e he
  obtain ⟨hv, _, hpos, hquot⟩ := hst e (hsubset he)
  have hden := (hlen e (hsubset he)).2
  refine ⟨hv, ?_⟩
  change Num.fixVal mem (mem a + e * L) h L P = forest.wstr e * ℓ e
  rw [← hden]
  exact (div_eq_iff (ne_of_gt hpos)).mp hquot

/-- The Rebuild length handoff can use the original lengths as
denominators and their stretched lengths as numerators. With positive
original lengths, the two tables satisfy the exact stretch layout. -/
theorem stretchValuesAt_of_coreLength {mem : ℕ → ℕ} {a h L P : ℕ}
    {E : Finset ℕ} {forest : LSF} {ℓ : ℕ → ℝ}
    (hnum : EdgeValuesAt mem (mem a) h L P E (coreLen forest ℓ))
    (hden : EdgeValuesAt mem (mem (a + 1)) h L P E ℓ)
    (hpos : ∀ e ∈ E, 0 < ℓ e) :
    StretchValuesAt mem a h L P E forest.wstr := by
  intro e he
  obtain ⟨hn, hnv⟩ := hnum e he
  obtain ⟨hd, hdv⟩ := hden e he
  refine ⟨hn, hd, hdv.symm ▸ hpos e he, ?_⟩
  rw [hnv, hdv, coreLen, mul_div_cancel_right₀ _ (ne_of_gt (hpos e he))]

/-- The sparsifier in Definition 5.7 keeps names from the core graph.
The length handoff therefore uses the same table indices at the next level. -/
theorem sparsifierLengthAt_of_stretch_numerator {mem : ℕ → ℕ} {a h L P : ℕ}
    {G S : MGraph} {forest : LSF} {ℓ : ℕ → ℝ} {k γlen γcong : ℝ} {emb : Embedding}
    (hs : IsSparsifiedCoreGraph G forest ℓ k γlen γcong S emb)
    (hst : StretchValuesAt mem a h L P G.E forest.wstr)
    (hlen : EdgeValuesAt mem (mem (a + 1)) h L P G.E ℓ) :
    EdgeValuesAt mem (mem a) h L P S.E (coreLen forest ℓ) :=
  coreLengthAt_of_stretch_numerator
    (fun _ he => (Finset.mem_sdiff.mp (hs.1.2.1 he)).1) hst hlen

/-- Update extends the graph history by exactly its model batch. -/
theorem sparseCoreMachineContract_update_input {args : List ℕ} {mem mem' : ℕ → ℕ}
    {s s' : tool.State} {G : MGraph} {U : List Update}
    (hinput : SparseCoreUpdateAt fmt L tool.toSparseCoreTool tool.restart k vCap eCap s args mem G U)
    (hpost : (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).post
      0 s args mem s' mem') :
    SparseCoreInput tool.toSparseCoreTool tool.restart k s' (G.applyBatch U) := by
  have heq := (hpost G U hinput).1
  rcases hinput with ⟨handle, graph, batch, words, lengths, gradient, heap, _, hG, _, hU, _⟩
  rw [heq]
  exact .update hG.1 U _ _ hU

/-- A machine restart changes the tool state and keeps the input graph. -/
theorem sparseCoreMachineContract_restart_input {args : List ℕ} {mem mem' : ℕ → ℕ}
    {s s' : tool.State}
    (hpre : (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).pre
      1 s args mem)
    (hpost : (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).post
      1 s args mem s' mem') :
    ∃ G, SparseCoreInput tool.toSparseCoreTool tool.restart k s G ∧ SparseCoreInput tool.toSparseCoreTool tool.restart k s' G := by
  rcases hpre with ⟨handle, branch, heap, G, rfl, hj, hG⟩
  refine ⟨G, hG, ?_⟩
  rw [hpost]
  exact .restart hG branch hj

/-- The three readout operations preserve the model state. -/
theorem sparseCoreMachineContract_readout_state {args : List ℕ} {mem mem' : ℕ → ℕ}
    {s s' : tool.State} {i : ℕ} (hi : i = 2 ∨ i = 3 ∨ i = 4)
    (hpost : (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation).post
      i s args mem s' mem') : s' = s := by
  rcases hi with rfl | rfl | rfl
  · exact hpost.1
  · exact hpost.1
  · exact hpost.1

end MinCostFlow.MinRatio
