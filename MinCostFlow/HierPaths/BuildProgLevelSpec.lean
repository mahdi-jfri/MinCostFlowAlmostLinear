module

public import MinCostFlow.HierPaths.BuildProgContracts

/-!
# The static builder's procedure for one parent group

This procedure builds all children of a parent group (as in `lemma_3`)
and all its sibling connectors. The top-level builder calls this
procedure for each non-singleton parent at each depth. It can copy the
three output sections directly into the hierarchy's CSR tables.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Child hosts, their walks in the parent host, and the sibling connectors.
The children and pairs are indexed within the parent, starting at zero. -/
structure BuildLevelData where
  host : ℕ → Graph
  emb : ℕ → ℕ → List ℕ
  conn : ℕ → ℕ → List (ℕ × ℕ × List ℕ)

/-- Terminals of child c in the parent's numbering. -/
def buildLevelChild (start s c : ℕ) : Finset ℕ :=
  shiftSet (start+c*s) (Finset.range s)

/-- The parent has k consecutive children of size s. -/
def buildLevelVerts (start s k : ℕ) : Finset ℕ :=
  Finset.Ico start (start+k*s)

/-- The degree cap after the batched game and its final injection. -/
def buildLevelDegree (L' : ℕ) : ℕ := 49*L'+2

/-- A level call writes the child graphs, child embeddings and pair
connectors as three sections. The first two are indexed by c. The third
has k*k rows, with the row for (c,c') at c*k+c'. Rows with c ≥ c' are empty.
For a singleton child the graph has no edges and its embedding is empty. -/
def BuildLevelData.encode (D : BuildLevelData) (k : ℕ) : List ℕ :=
  layoutList [
    csrList k (fun c => (D.host c).encode),
    csrList k (fun c => csrList (D.host c).m (D.emb c)),
    csrList (k*k) (fun i =>
      let pair := D.conn (i/k) (i%k)
      csrList pair.length (fun j => connWords (pair.getD j (0,0,[]))))]

/-- The mathematical guarantees of the child-game and connector calls.
Walk counts are occurrence counts. -/
structure BuildLevelData.Good (D : BuildLevelData) (G : Graph)
    (start s k M r Δ L L' bh : ℕ) : Prop where
  graph : ∀ c < k, (D.host c).n = G.n ∧ (D.host c).IsValid ∧ (D.host c).IsLoopless ∧
    (∀ e ∈ (D.host c).edges, e.1 ∈ buildLevelChild start s c ∧ e.2 ∈ buildLevelChild start s c) ∧
    (∀ v ∈ buildLevelChild start s c, (D.host c).deg v ≤ buildLevelDegree L') ∧
    (s=1 → (D.host c).edges = []) ∧
    (1<s → (D.host c).IsExpansionExpanderOn (buildLevelChild start s c)
      (1 / (2 * (PParam ParamConfig.default M r : ℝ))))
  embeds : ∀ c < k, IsEmbeddingOn (D.host c) G (buildLevelVerts start s k) (D.emb c)
  embedLength : ∀ c < k, ∀ e < (D.host c).m, (D.emb c e).length ≤ routePathLen Δ bh L
  embedLoad : ∀ e < G.m,
    ∑ c ∈ Finset.range k, ∑ j ∈ Finset.range (D.host c).m, (D.emb c j).count e ≤
      buildLevelDegree L' * routeCong Δ bh L
  connEmpty : ∀ c < k, ∀ c' < k, c' ≤ c → D.conn c c' = []
  connMatch : ∀ c < k, ∀ c' < k, c < c' →
    ((D.conn c c').map Prod.fst).Nodup ∧
    ((D.conn c c').map Prod.fst).toFinset = buildLevelChild start s c ∧
    ((D.conn c c').map fun en => en.2.1).Nodup ∧
    ((D.conn c c').map fun en => en.2.1).toFinset = buildLevelChild start s c'
  connWalk : ∀ c < k, ∀ c' < k, c < c' → ∀ en ∈ D.conn c c',
    IsEdgeWalk G.edges en.1 en.2.1 en.2.2 ∧ en.2.2.length ≤ routePathLen Δ bh L
  connLoad : ∀ c < k, ∀ c' < k, c < c' → ∀ e < G.m,
    ((D.conn c c').map fun en => en.2.2.count e).sum ≤ routeCong Δ bh L

/-- The level cost pays for at most 49 L' + 1 batched rounds and the injection,
one two-child call per sibling pair, and the work of writing their data. -/
def buildLevelCost (K : ℕ) (G : Graph) (s k M r Δ L L' bh : ℕ) : ℕ :=
  let X := s*k
  let T := buildLevelDegree L'
  let d := routePathLen Δ bh L
  let R := routeCong Δ bh L
  K * (T * X * ((NOf M r)^2 * (WParam ParamConfig.default M)^(10*r^2+10) + T + 1) +
    (T*k + k*k + 1) * (X+G.m+1) * (d+1) * (R+1) + k*k + 1)

/-- Inputs of the level call. Only the geometry of the parent and the
numeric player parameters are passed as words. -/
def buildLevelArgs (gAddr xAddr start s k M r Δ L L' bh h : ℕ) : List ℕ :=
  [gAddr,xAddr,start,s,k,M,r,Δ,L,L',bh,h]

/-- The one-parent procedure. It consumes the parent graph and the sorted
parent terminals below h, then writes its result at h, preserving the
prefix. The space function includes room for the router and core scratch. -/
def buildLevelContract (w K : ℕ)
    (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (G : Graph) (start s k M r Δ L L' bh : ℕ) : Contract :=
  let X := buildLevelVerts start s k
  let C := heapContract w
    (fun args mem => ∃ gAddr xAddr h, args = buildLevelArgs gAddr xAddr start s k M r Δ L L' bh h ∧
      GraphAt mem gAddr G ∧ ListAt mem xAddr (finsetWords X) ∧
      gAddr + G.encode.length ≤ h ∧ xAddr + (finsetWords X).length ≤ h ∧
      G.IsValid ∧ HostPre G X Δ L ∧ 2 ≤ k ∧ 1 ≤ s ∧
      (s=1 ∨ s%2=0) ∧ s ≤ (NOf M r)^r ∧ r ≤ ell M ∧ 49*L' ≤ deltaParam M ∧ s < 2^L' ∧
      ∃ β : ℝ, 0 < β ∧ G.IsExpansionExpanderOn X β ∧ max 2 (2/β) ≤ (bh:ℝ))
    (fun _ _ _ => True)
    (fun _ _ => buildLevelCost K G s k M r Δ L L' bh)
    (fun _ _ => space G s k M r Δ L L' bh)
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
        ∃ (gAddr xAddr h : ℕ) (D : BuildLevelData), args = buildLevelArgs gAddr xAddr start s k M r Δ L L' bh h ∧
          ListAt mem' h (D.encode k) ∧ h + (D.encode k).length ≤ v ∧
          D.Good G start s k M r Δ L L' bh }

/-- A level entry can be called with every parent and the supplied numeric
parameters. -/
def ProvidesBuildLevel (w K : ℕ)
    (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ G start s k M r Δ L L' bh,
    MeetsContract w p f (buildLevelContract w K space G start s k M r Δ L L' bh)

end MinCostFlow.HierPaths
