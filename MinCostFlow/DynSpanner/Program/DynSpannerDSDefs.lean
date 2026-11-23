module

public import MinCostFlow.DynSpanner.Complexity
public import MinCostFlow.DynSpanner.Program.DynSpannerDSPrefix
public import MinCostFlow.DynSpanner.Program.DynSpannerInitDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerDSOp
public import MinCostFlow.DynSpanner.Program.DynSpannerDSBank

/-!
# The data structure of Theorem 8.2: definitions

Theorem 8.2 (page 39) describes a data structure: it is built on a graph `G₀` and then takes
batches of edge deletions and vertex splits. For each batch it returns the change `U_H` of the
spanner `H` and the set `D` of re-embedded edges. This file states it as a
`WordRAM.DataStructure`.

**Abstract state.** The model of the dynamic spanner (`DynSpanner.runState`) is a function of the
initial graph and of the updates applied so far. So an abstract state `DSHist` is the initial graph
`G₀` with the list of batches `Us` applied so far, and its model state is
`runState G₀ q sparsify Us.flatten Us.flatten.length`. The branching factor is the one of
Theorem 8.2, `q = phaseBase (G₀.n + splitBound) L`.

**Input in memory.** The initialization reads the graph as the procedure `dsInitStmt` does: a list
of vertices and a list of triples `(e, tail e, head e)`. The function `decodeGraph` reads these
lists from memory (the endpoints of a name that is not an edge are set to `0`). An update reads a
batch in the layout `BatchAt` of `DynGraphLayout.lean`; `decodeBatch` reads it. In a vertex split
the sets `St`, `Sh` are read as the sets of the encoded edges (tag `2`) or as the edges at `v` that
are not encoded (tag `3`).

**Postconditions.** The initialization and the update leave the new abstract state, the outputs
`U_H` and `D` of the batch in memory, and the clauses of Theorem 8.2 for the new history
(`Theorem82Clauses`, the statement of `theorem_8_2`).

**Costs.** The initialization costs the bound of `dsInitContract` (`dsInit_initCostBound` puts it
in the form of Theorem 8.2) plus `1440 Φ₀`, where `Φ₀ = Σ_i |E(H_i)|` is the potential `levelPot`
of the first state. An update of a batch `U` costs `⌈C · rate · Enc(U)⌉ + 1440 W + 505`
(`dsUpdateAmortCost`): the time bound of Theorem 8.2 for `U` times the constant
`C = dsAmortConst impl`, plus `1440` per word `W` of the encoded batch (the batch is read word by
word, and a split may be encoded by its larger side, so `W` can exceed `Enc(U)`). The potential is
the bank `dsBank` of `DynSpannerDSBank.lean`: what the batches put in minus what the steps took
out. The worst-case bound of an update is `dsUpdateOpCost`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## The clauses of Theorem 8.2 -/

/-- The conclusion of `theorem_8_2` (Theorem 8.2, page 39) for the initial graph `G₀` and the
batches `Us`. -/
def Theorem82Clauses (G₀ : MGraph) (L splitBound : ℕ) (P : SparsifyParams)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (Us : List (List Update)) : Prop :=
    let nMax := G₀.n + splitBound
    let q := phaseBase nMax L
    let initOut := init G₀ L q sparsify
    let st := fun t => runBatchState (L := L) G₀ q sparsify Us t
    let res := fun t => runBatchStepOut (L := L) G₀ q sparsify Us t
    let Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let M_H := (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s
    let degΛ := 4 * Real.log (6 * M_H + 10) + 4
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let nRoot : ℝ := ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
    let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
    let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
      | some U => ((st t').G.batchEnc U : ℝ)
      | none => 0
    ((initOut.state.H.m : ℝ) ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) ∧
    ((initOut.cost : ℝ) ≤ P.K_t * (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
        (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) ∧
    (∀ t ≤ Us.length,
      (st t).G = G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t)) ∧
      (st t).G.IsSubgraph (st t).H ∧
      ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s ∧
      Embedding.IsEmbedding (piTotal (st t)) (st t).G (st t).H ∧
      (Embedding.length (piTotal (st t)) (st t).G : ℝ) ≤ 3 ^ L * P.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P.γ_ℓ ^ (L * (L + 1) / 2) * P.γ_c ^ (L + 1) *
          (G₀.maxDeg : ℝ)) ∧
    (∀ t < Us.length, ∀ U, Us[t]? = some U →
      res t = update (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t)) U sparsify ∧
      (res t).state = st (t + 1) ∧
      (st t).H.BatchIsValid (res t).UH ∧
      (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
      (res t).D ⊆ (st (t + 1)).H.E ∧
      (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
        eH ∈ walkEdges (piTotal (st (t + 1)) eG) → eH ∉ (res t).D →
        eH ∈ walkEdges (piTotal (st t) eG))) ∧
    (∀ t ≤ Us.length,
      (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤
        (2 + 12 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
        4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
        (2 + 2 * (6 + 3 * degΛ) * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
        6 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s *
          batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
        90 * (L : ℝ) * nRoot * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
          encTotal t))

/-! ## The parameters, the abstract state and its model -/

/-- The parameters of the data structure: the sparsifier `impl` of Theorem 8.1, the edge bound
`mMax` of its contract, the word size `w`, the number of levels `L`, the bounds `vCap`, `eCap` on
the names of vertices and edges, and the bound `splitBound` on the number of vertex splits of
Theorem 8.2. -/
structure DSParams where
  impl : SparsifyImpl
  mMax : ℕ
  w : ℕ
  L : ℕ
  vCap : ℕ
  eCap : ℕ
  splitBound : ℕ

/-- An abstract state: the initial graph and the batches applied so far. -/
structure DSHist where
  G₀ : MGraph
  Us : List (List Update)

namespace DSHist

/-- The updates applied so far, in order. -/
def flat (s : DSHist) : List Update := s.Us.flatten

/-- The branching factor of Theorem 8.2. -/
noncomputable def q (P : DSParams) (s : DSHist) : ℕ := phaseBase (s.G₀.n + P.splitBound) P.L

/-- The model state of an abstract state. -/
noncomputable def state (P : DSParams) (s : DSHist) : DynSpannerState P.L :=
  runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat s.flat.length

/-- The bound on the generation word: `1 + |E(G₀)|` after the initialization, then at most
`dsStepGenAt` per update and `2` per batch (one for `D`-collection and one for `R`-collection). -/
noncomputable def genBound (P : DSParams) (s : DSHist) : ℕ :=
  1 + s.G₀.m + 2 * s.Us.length +
    ∑ r ∈ Finset.range s.flat.length, dsStepGenAt s.G₀ P.impl P.L (s.q P) s.flat r

end DSHist

/-- The parameters of Theorem 8.1 that the data structure uses. -/
noncomputable def dsSparsifyParams (P : DSParams) : SparsifyParams :=
  (canonicalSparsifyParams P.impl P.mMax).absorbTime

/-! ## Reading the input from memory -/

/-- The list of `n` words from address `a`. -/
def readList (mem : ℕ → ℕ) (a n : ℕ) : List ℕ := (List.range n).map fun i => mem (a + i)

/-- The list of `n` triples of words from address `a`. -/
def readTriples (mem : ℕ → ℕ) (a n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).map fun i => (mem (a + 3 * i), mem (a + 3 * i + 1), mem (a + 3 * i + 2))

/-- The graph with vertex list `vL` and edge triples `eE`; the endpoints of a name that is not an
edge are `0`. -/
def graphOfLists (vL : List ℕ) (eE : List (ℕ × ℕ × ℕ)) : MGraph where
  V := vL.toFinset
  E := (eE.map Prod.fst).toFinset
  tail e := ((eE.find? fun t => t.1 = e).map fun t => t.2.1).getD 0
  head e := ((eE.find? fun t => t.1 = e).map fun t => t.2.2).getD 0

/-- The arguments of the initialization: `[L, q, vCap, eCap, |V|, V_ptr, |E|, E_ptr, h]`. -/
def initArgsGraph (args : List ℕ) (mem : ℕ → ℕ) : MGraph :=
  graphOfLists (readList mem (args.getD 5 0) (args.getD 4 0))
    (readTriples mem (args.getD 7 0) (args.getD 6 0))

/-- Read one encoded update at `a`, with the graph `G` before it: the update and its number of
words. -/
noncomputable def decodeUpdate (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) : Update × ℕ :=
  if mem a = 0 then (.insert (mem (a + 1)) (mem (a + 2)) (mem (a + 3)), 4)
  else if mem a = 1 then (.delete (mem (a + 1)), 2)
  else
    let v := mem (a + 1)
    let kt := mem (a + 3)
    let kh := mem (a + 4)
    let Lt := (readList mem (a + 5) kt).toFinset
    let Lh := (readList mem (a + 5 + kt) kh).toFinset
    if mem a = 2 then (.split v (mem (a + 2)) Lt Lh, 5 + kt + kh)
    else (.split v (mem (a + 2)) (G.E.filter (fun e => G.tail e = v) \ Lt)
      (G.E.filter (fun e => G.head e = v) \ Lh), 5 + kt + kh)

/-- Read `n` encoded updates from `a`, starting on the graph `G`: the updates and their numbers
of words. -/
noncomputable def decodeBatchBody (mem : ℕ → ℕ) : ℕ → ℕ → MGraph → List Update × List ℕ
  | 0, _, _ => ([], [])
  | n + 1, a, G =>
    let d := decodeUpdate mem a G
    let rest := decodeBatchBody mem n (a + d.2) (G.applyUpdate d.1)
    (d.1 :: rest.1, d.2 :: rest.2)

/-- The batch at `a` (length word, then the updates), read on the graph `G`. -/
noncomputable def decodeBatch (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) : List Update × List ℕ :=
  decodeBatchBody mem (mem a) (a + 1) G

/-! ## The specification -/

/-- The batch of an update call `[b, batchPtr, W, h]`, read on the current graph. -/
noncomputable def opBatch (P : DSParams) (s : DSHist) (args : List ℕ) (mem : ℕ → ℕ) :
    List Update × List ℕ :=
  decodeBatch mem (args.getD 1 0) (s.state P).G

/-- The words that an update call copies: the batch, at the start of its heap. -/
def opWords (args : List ℕ) : ℕ := args.getD 2 0

/-- The precondition of the initialization `[L, q, vCap, eCap, |V|, V_ptr, |E|, E_ptr, h]`: the
graph read from memory meets the precondition of `dsInitContract`, `q` is the branching factor
of Theorem 8.2, and the sparsifier has `1 ≤ max p_s p_t` (so that its log factor `Λ` pays for the
logs of the program). -/
def DSInitPre (P : DSParams) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  let G := initArgsGraph args mem
  ∃ q nV V_ptr nE E_ptr h,
    args = [P.L, q, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] ∧
    q = phaseBase (G.n + P.splitBound) P.L ∧ 1 ≤ P.L ∧ 1 ≤ max P.impl.p_s P.impl.p_t ∧
    (dsInitContract P.impl P.mMax P.w P.L q P.vCap P.eCap G (readList mem V_ptr nV)
      (readTriples mem E_ptr nE)).pre args mem

/-- The precondition of an update `[b, batchPtr, W, h]` on the abstract state `s`: the batch read
at `batchPtr` is encoded there in `W` words below `h`, it is a valid batch of deletions and
vertex splits within the name bounds, the vertex splits stay within `splitBound`, and the words
of the machine are large enough for the counters of the run. -/
def DSUpdatePre (P : DSParams) (s : DSHist) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  let G := (s.state P).G
  let U := (opBatch P s args mem).1
  let lens := (opBatch P s args mem).2
  let us := s.flat ++ U
  ∃ b batchPtr W h, args = [b, batchPtr, W, h] ∧
    16 ≤ 2 ^ P.w ∧
    BatchBodyLensAt mem (batchPtr + 1) G U lens ∧ W = 1 + lens.sum ∧ batchPtr + W ≤ h ∧
    (∀ i < W, mem (batchPtr + i) < 2 ^ P.w) ∧
    G.BatchIsValid U ∧ (∀ u ∈ U, isDelOrSplit u) ∧ BatchWithinCaps P.vCap P.eCap U ∧
    batchSplitCount us ≤ P.splitBound ∧
    s.genBound P + dsUpdateLoopGen s.G₀ P.impl P.L (s.q P) us U.length s.flat.length < 2 ^ P.w ∧
    s.flat.length + U.length < 2 ^ P.w ∧ s.q P < 2 ^ P.w ∧
    ∀ r < U.length, dsStepWordOKAt s.G₀ P.impl P.w P.L (s.q P) us (s.flat.length + r)

/-- The postcondition of an update `[b, batchPtr, W, h]`: the new abstract state appends the batch
`U` read from memory; at `h + W` the memory holds the 7-word header
`[uhPtr, |U_H|, words, dPtr, |D|, rPtr, |R|]` of the outputs, the batch `U_H` (in some order), the
duplicate-free list `D` of the model's `update (state s) U`, and the duplicate-free list `rOut` of
re-embedded edges (`rOut.toFinset = updateReembSet (s.state P) U (canonicalSparsify P.impl)`);
the lists `D`, `R` and `U_H` lie in this order right after the header, and the last word of `U_H`
is addressable; and the clauses of Theorem 8.2 hold for the new history. -/
def DSUpdatePost (P : DSParams) (s : DSHist) (args : List ℕ) (mem : ℕ → ℕ) (s' : DSHist)
    (mem' : ℕ → ℕ) : Prop :=
  let U := (opBatch P s args mem).1
  let out := update (s.state P) U (canonicalSparsify P.impl)
  let hOut := args.getD 3 0 + opWords args
  s' = ⟨s.G₀, s.Us ++ [U]⟩ ∧
  (∃ (uhOutPtr uhOutWords dOutPtr rOutPtr : ℕ) (uhActual : List Update) (dOut rOut : List ℕ),
    mem' hOut = uhOutPtr ∧ mem' (hOut + 1) = uhActual.length ∧
    mem' (hOut + 2) = 1 + uhOutWords ∧ mem' (hOut + 3) = dOutPtr ∧
    mem' (hOut + 4) = dOut.length ∧ mem' (hOut + 5) = rOutPtr ∧
    mem' (hOut + 6) = rOut.length ∧
    BatchAt mem' uhOutPtr (s.state P).H uhActual (1 + uhOutWords) ∧
    uhActual.Perm out.UH ∧ (s.state P).H.applyBatch uhActual = out.state.H ∧
    dOut.Nodup ∧ dOut.toFinset = out.D ∧ ListAt mem' dOutPtr dOut ∧
    rOut.Nodup ∧ rOut.toFinset = updateReembSet (s.state P) U (canonicalSparsify P.impl) ∧
    ListAt mem' rOutPtr rOut ∧
    hOut + 7 ≤ dOutPtr ∧ dOutPtr + dOut.length = rOutPtr ∧ rOutPtr + rOut.length = uhOutPtr ∧
    uhOutPtr + 1 + uhOutWords < 2 ^ P.w) ∧
  Theorem82Clauses s'.G₀ P.L P.splitBound (dsSparsifyParams P) (canonicalSparsify P.impl) s'.Us

/-- The cost bound of an update: the copy of the batch and the bound of `dsUpdateLoopContract`. -/
noncomputable def dsUpdateOpCost (P : DSParams) (s : DSHist) (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let U := (opBatch P s args mem).1
  let lens := (opBatch P s args mem).2
  30 * opWords args + 25 + dsUpdateOpOverhead +
    dsUpdateLoopCost s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U) U lens
      s.flat.length

/-- The potential of an abstract state: the bank `dsBank` of its history. -/
noncomputable def DSHist.bank (P : DSParams) (s : DSHist) : ℕ :=
  dsBank P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.G₀.n + P.splitBound) s.G₀ s.Us

/-- The potential `1440 Φ₀` of the first state on the graph `G`. -/
noncomputable def dsInitBank (P : DSParams) (G : MGraph) : ℕ :=
  1440 * levelPot (runState (L := P.L) G (phaseBase (G.n + P.splitBound) P.L)
    (canonicalSparsify P.impl) [] 0)

/-- **The amortized cost of an update** `[b, batchPtr, W, h]` with batch `U`: the time bound of
Theorem 8.2 for `U` times `C = dsAmortConst impl` (`dsBatchCharge`, on the current graph), plus
`1440 W` for the words of the batch and `505`. -/
noncomputable def dsUpdateAmortCost (P : DSParams) (s : DSHist) (args : List ℕ)
    (mem : ℕ → ℕ) : ℕ :=
  dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀ (s.G₀.applyBatch s.flat)
      (opBatch P s args mem).1 +
    1440 * opWords args + 485 + dsUpdateOpOverhead

/-- The space bound of an update: the copy of the batch and the bound of `dsUpdateLoopContract`. -/
noncomputable def dsUpdateOpSpace (P : DSParams) (s : DSHist) (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let U := (opBatch P s args mem).1
  let lens := (opBatch P s args mem).2
  opWords args +
    dsUpdateLoopSpace s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U) U lens
      s.flat.length

/-- **The data structure of Theorem 8.2 (page 39).** Initialization: `[L, q, vCap, eCap, |V|,
V_ptr, |E|, E_ptr, h]` builds the state on the graph read from memory. Operation `0`: `[b,
batchPtr, W, h]` applies the batch read at `batchPtr`. -/
noncomputable def dynSpannerDS (P : DSParams) : DataStructure DSHist where
  initPre := DSInitPre P
  initPost args mem s _ :=
    s = ⟨initArgsGraph args mem, []⟩ ∧
    Theorem82Clauses s.G₀ P.L P.splitBound (dsSparsifyParams P) (canonicalSparsify P.impl) s.Us
  initCost args mem :=
    (dsInitContract P.impl P.mMax P.w P.L (args.getD 1 0) P.vCap P.eCap (initArgsGraph args mem)
      [] []).cost args mem + dsInitBank P (initArgsGraph args mem)
  initSpace args mem :=
    dsFixedSize P.L P.vCap P.eCap +
      dsInitCoreSpaceBound P.impl P.mMax P.vCap P.eCap (initArgsGraph args mem)
  pre i s args mem := i = 0 ∧ DSUpdatePre P s args mem
  post _ s args mem s' mem' := DSUpdatePost P s args mem s' mem'
  cost _ s args mem := dsUpdateAmortCost P s args mem
  space _ s args mem := dsUpdateOpSpace P s args mem

/-! ## The representation -/

/-- How memory holds an abstract state `s` with handle `b`: the facts that the batch loop needs
about the history (a valid graph and valid updates), the state block `DynSpannerStateAt` of the
model state with the metadata `x`, the reverse walk lists `RevHistoryInv`, and the bound
`genBound` on the generation word. -/
def DSRepAt (P : DSParams) (b : ℕ) (s : DSHist) (x : DynSpannerMeta P.L) (mem : ℕ → ℕ) : Prop :=
  1 ≤ P.L ∧ s.G₀.IsValid ∧ s.G₀.m ≤ P.mMax ∧ (∀ e ∈ s.G₀.E, e < P.eCap) ∧
  s.G₀.BatchIsValid s.flat ∧ (∀ u ∈ s.flat, isDelOrSplit u) ∧
  batchSplitCount s.flat ≤ P.splitBound ∧
  DynSpannerStateAt P.L P.vCap P.eCap b mem x (s.state P) ∧
  RevHistoryInv s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat s.flat.length x ∧
  mem (b + dsGenOff) ≤ s.genBound P

/-- The representation of the data structure: the concrete state is the history with the metadata
`DynSpannerMeta`, the footprint is `metaFoot` (the state block and the heap intervals), and the
potential is the bank of the history (`DSHist.bank`). The representation also records that the
sparsifier has `1 ≤ max p_s p_t`, which keeps the bank nonnegative. -/
noncomputable def dynSpannerRep (P : DSParams) : DSRep DSHist where
  τ := DSHist × DynSpannerMeta P.L
  rep b s x mem := x.1 = s ∧ DSRepAt P b s x.2 mem ∧ 1 ≤ max P.impl.p_s P.impl.p_t
  phi _ x _ := x.1.bank P
  foot b x := metaFoot b x.2

end

end MinCostFlow.DynSpanner.Program
