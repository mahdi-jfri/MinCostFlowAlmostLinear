module

public import MinCostFlow.HierPaths.BuildProgFinishFits

/-!
# One common round of the child game

Query the core for every active child, route the bisections together, and
append the matches and walks. Replies from the core are retained so a
certified child can leave the active list.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The graphs, player calls, and size bounds used for one round. -/
structure BuildRoundData where
  jobs : BuildGameJobs
  host : Graph
  verts : Finset ℕ
  childSize : ℕ
  pathBound : ℕ
  q : ℕ
  M : ℕ
  r : ℕ
  Δ : ℕ
  L : ℕ
  K : ℕ
  core : ℕ → Graph → CoreResult
  coreCost : ℕ → Graph → ℕ
  coreSpace : ℕ → ℕ
  route : RouterFn
  routeCost : RouterCostFn
  routeSpace : ℕ → ℕ → ℕ → ℕ → ℕ
  routeBump : ℕ := 0

/-- The input addresses of one round. -/
structure BuildRoundAddrs where
  graphs : ℕ
  offsets : ℕ
  heap : ℕ
  replies : ℕ
  host : ℕ
  verts : ℕ

namespace BuildRoundData

/-- The entry words of the common round. -/
def args (B : BuildRoundData) (A : BuildRoundAddrs) : List ℕ :=
  [B.q, B.M, B.r, B.jobs.count, A.graphs, A.offsets, A.heap, A.replies, B.childSize, A.host, A.verts,
    B.Δ, B.L, B.pathBound, B.verts.card]

/-- The earlier scan reads only the active children and their core parameters. -/
def scanArgs (B : BuildRoundData) (A : BuildRoundAddrs) : List ℕ :=
  [B.q, B.M, B.r, B.jobs.count, A.graphs, A.offsets, A.heap, A.replies]

/-- The earlier scan contract for this round. -/
def scanContract (B : BuildRoundData) (w : ℕ) : Contract :=
  buildGameScanContract w B.K B.M B.r B.q B.core B.coreCost B.coreSpace B.jobs

/-- The heap cursor after preparing the core replies. -/
def prepared (B : BuildRoundData) (A : BuildRoundAddrs) : ℕ :=
  B.jobs.prepPrefix B.core B.q A.heap B.jobs.count

/-- The active indices that need a matching. -/
def indices (B : BuildRoundData) : List ℕ := batchJobIndices B.jobs B.core B.q

/-- Their prepared requests. -/
def pairs (B : BuildRoundData) : List (Finset ℕ × Finset ℕ) :=
  batchJobPairs B.jobs B.core B.q B.childSize

/-- The full-router model result, with its last denominator. -/
def result (B : BuildRoundData) : RouteResult × ℕ :=
  lemma1Route B.route B.host B.verts B.pairs B.Δ B.L

/-- The common routing call receives the reply table, parent host, and vertex-set size. -/
def routeArgs (B : BuildRoundData) (A : BuildRoundAddrs) : List ℕ :=
  [A.replies, B.jobs.count, B.childSize, A.host, A.verts, B.Δ, B.L, B.prepared A, B.verts.card]

/-- The common full-routing contract. -/
def routeContract (B : BuildRoundData) (w : ℕ) : Contract :=
  buildRoundRouteContract w B.K B.q B.childSize B.Δ B.L B.jobs B.core B.route B.routeCost
    B.routeSpace B.host B.verts

/-- The location of the matched reply after the prepared block and router input. -/
def routeReply (B : BuildRoundData) (A : BuildRoundAddrs) : ℕ :=
  buildBatchEnd (B.prepared A + 1 + B.jobs.count) B.indices.length B.childSize

/-- The end of the routed block when the round has a cut, including the router bump gap. -/
def routedEnd (B : BuildRoundData) (A : BuildRoundAddrs) : ℕ :=
  B.routeReply A + (routeResultWords B.result.1).length + B.routeBump

/-- Record the router bump gap produced by the common routing call. -/
def withRouteBump (B : BuildRoundData) (rBump : ℕ) : BuildRoundData :=
  { B with routeBump := rBump }

/-- Upper bound on the bump gap left by the full router call. -/
def ValidRouteBump (B : BuildRoundData) (rBump : ℕ) : Prop :=
  rBump ≤ (B.verts.card + 1) * routerSpaceUpTo B.routeSpace B.host.n B.host.encode.length
    (pairsWords B.pairs).length (B.Δ + B.L + max 2 B.verts.card)

/-- The child graphs and routed walks used by the application scan. -/
def applyData (B : BuildRoundData) (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) : ApplyBatchData :=
  ⟨B.jobs, B.indices, Ms, emb, B.host⟩

/-- Runtime arguments of the application entry. -/
def finishArgs (B : BuildRoundData) (A : BuildRoundAddrs) : List ℕ :=
  [B.routeReply A, B.prepared A + 1, A.graphs, A.offsets, A.host + 2, B.host.n, B.pathBound,
    B.routedEnd A, B.indices.length]

end BuildRoundData

/-- Before the round, the parent and active child tables fit. A matched result must
fit in the child graph reservations, and the shared walk arena must fit in a word. -/
structure BuildRoundFit (w : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs) (mem : ℕ → ℕ) : Prop where
  scan : (B.scanContract w).pre (B.scanArgs A) mem
  host : GraphAt mem A.host B.host
  hostValid : B.host.IsValid
  verts : ListAt mem A.verts (finsetWords B.verts)
  hostBelow : A.host + B.host.encode.length ≤ A.replies
  vertsBelow : A.verts + (finsetWords B.verts).length ≤ A.replies
  router : RouterPre B.host B.verts B.pairs B.Δ B.L
  bits : 3 < 2 ^ w
  routeWord : B.routeReply A +
    (B.verts.card + 1) * routerSpaceUpTo B.routeSpace B.host.n B.host.encode.length
      (pairsWords B.pairs).length (B.Δ + B.L + max 2 B.verts.card) < 2 ^ w
  even : 2 * (B.childSize / 2) = B.childSize
  childSize : ∀ i < B.jobs.count, (B.jobs.graph i).n = B.childSize
  sets : ∀ i < B.jobs.count, ∀ U, B.jobs.answer B.core B.q i = .cut U →
    U ⊆ Finset.range B.childSize
  beforeGraph : ∀ i < B.jobs.count,
    A.graphs + B.jobs.count ≤ B.jobs.addr i ∧ A.offsets + B.jobs.count ≤ B.jobs.addr i
  lastBound : B.indices.isEmpty = false → routePathLen B.Δ B.result.2 B.L ≤ B.pathBound
  reserved : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb →
    let D := B.applyData Ms emb
    FinishChildRegions w D (A.host + 2) A.replies ∧
      (∀ i < Ms.length, ∀ e ∈ Ms.getD i [],
        D.offset i ≤ e.1 ∧ D.offset i ≤ e.2 ∧ e.1 < 2 ^ w ∧ e.2 < 2 ^ w) ∧
      D.cursor (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n)
        Ms.length < 2 ^ w

/-- Route the prepared requests (register 15 holds their arena end, register 14 holds `|X|`)
and append the matched rows to the child graphs. -/
def buildOneRoundTail (fRoute fFinish : ℕ) : Stmt :=
  .seq (.call 16 fRoute [.reg 7,.reg 3,.reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 15,.reg 14])
      (.seq (.assign 17 (.load (.reg 15)))
        (.seq (.cond (.reg 17)
          (.seq (.assign 18 (.bin .add (.reg 15) (.const 1)))
            (.seq (.assign 19 (.bin .add (.reg 18) (.reg 3)))
              (.seq (.assign 20 (.bin .add
                (.bin .add (.bin .add (.reg 19) (.bin .add (.reg 17) (.reg 17))) (.const 1))
                (.bin .mul (.reg 17) (.reg 8))))
                (.call 16 fFinish [.reg 20,.reg 18,.reg 4,.reg 5,.bin .add (.reg 9) (.const 2),
                  .load (.reg 9),.reg 13,.reg 16,.reg 17]))))
          .nop)
          (.ret (.reg 16))))

/-- The complete round prepares the active children and then routes the common batch. -/
def buildOneRoundProc (fScan fRoute fFinish : ℕ) : Stmt :=
  .seq (.call 15 fScan [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7])
    (buildOneRoundTail fRoute fFinish)

theorem buildOneRoundProc_noRand (fScan fRoute fFinish : ℕ) :
    (buildOneRoundProc fScan fRoute fFinish).NoRand := by
  simp [buildOneRoundProc, buildOneRoundTail, Stmt.NoRand]

/-- The last phase of the round either keeps an all-expander result or applies a
matched batch to the requesting children. -/
def roundFinishPost (w : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs) (mid : ℕ)
    (mem mem' : ℕ → ℕ) (v : ℕ) : Prop :=
  if B.indices.isEmpty then v = mid ∧ mem' = mem else
    mid = B.routedEnd A ∧
    ∃ Ms emb, B.result.1 = .matched Ms emb ∧
      (buildFinishBatchContract w (B.applyData Ms emb)).post (B.finishArgs A) mem v mem'

/-- All three memory transitions of one common round, with the same data and addresses. -/
def buildOneRoundContract (w : ℕ) (B : BuildRoundData) : Contract where
  pre args mem := ∃ A, args = B.args A ∧ BuildRoundFit w B A mem
  post args mem v mem' := ∃ A mem₁ mem₂ mid, args = B.args A ∧
    (B.scanContract w).post (B.scanArgs A) mem (B.prepared A) mem₁ ∧
    (B.routeContract w).post (B.routeArgs A) mem₁ mid mem₂ ∧
    roundFinishPost w B A mid mem₂ mem' v
  cost args mem := (B.scanContract w).cost args mem + (B.routeContract w).cost args mem +
      (match B.result.1 with
        | .matched Ms emb => (buildFinishBatchContract w (B.applyData Ms emb)).cost args mem
        | .cut _ => 0) + 128

end MinCostFlow.HierPaths
