module

public import MinCostFlow.HierPaths.Impl
public import MinCostFlow.HierPaths.InitModelCost
public import MinCostFlow.HierPaths.Model
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.HierPaths.PortsHost

/-!
# The part of `Init` after the static construction: the interface

`Init` has two parts. The static construction builds the hierarchy: a
`HierData` with the owners and labels of the root host. The rest flattens the connectors, builds
the arrays and writes the block of `hierRep a`. This file fixes what passes between the two parts
and what the rest must do.

* `StaticData` is the output of the static construction, and `StaticOut mem addr S` says that
  memory holds it at `addr` in the simple layout `StaticData.encode`: a `layoutList` of six
  sections (header `[x, b, numConn]`, owners, labels, hosts, embeddings, connectors).
* `StaticData.model a d m` is the static part of the model that `Init` builds from it:
  `staticArrays`, the pair numbers `pairIdxOf`, and the bounds `xiOf`, `leafDepth · (2^b − 1)`,
  `lamOf`. `initConcrete` is the concrete state with the dynamic state `DelState.init`.
* `initConcrete_rep`: if memory holds the block of `initConcrete` at the handle, and the model
  meets `Spec` and `Fits`, then memory holds the initial abstract state (`hierRep a`).
* `initPost_of_initPre`: the abstract state `⟨phiNum, phiDen, M, G, ∅, ∅⟩` meets `initPost`, as
  long as the input graph is still in memory.
* `StaticContract`: the contract of the static construction, which ends in `StaticOut`.
* `InitRestContract`: the contract of the rest of `Init`: it overwrites the static output with
  the block of `initConcrete`, with cost a constant times the step count `initRestSteps` plus the
  length of the block. `initRestSteps_le_gamma` bounds the first part by
  `63 · m · Γ` (`initRest_cost_le`).
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-! ### The output of the static construction -/

/-- The output of the static construction: the numbers `x` (`2^x` terminals) and `b` (`2^b`
children per group), the owners and labels of the root host, and the hierarchy. -/
structure StaticData where
  x : ℕ
  b : ℕ
  owner : ℕ → ℕ
  label : ℕ → Option ℕ
  H : HierData

/-- A label as a word: `0` for none, `e + 1` for edge `e`. -/
def labelWord : Option ℕ → ℕ
  | none => 0
  | some e => e + 1

/-- A connector `(y, z, walk)` as words. -/
def connWords (q : ℕ × ℕ × List ℕ) : List ℕ := q.1 :: q.2.1 :: q.2.2

/-- The pair `(j, c, c')` of the pair index `k = (j · 2^x + c) · 2^b + r`: `c'` is the child of
the parent of `c` (at depth `j`) with residue `r` mod `2^b`. The children of one group are at
most `2^b` consecutive numbers starting at `L`, so `c' = L + ((r + 2^b − L mod 2^b) mod 2^b)`.
Section 5 of the static output is indexed this way, so it has `leafDepth · 2^x · 2^b` entries,
as the pair arrays of the model. -/
def pairOfIdx (x b k : ℕ) : ℕ × ℕ × ℕ :=
  let j := k / 2 ^ b / 2 ^ x
  let c := k / 2 ^ b % 2 ^ x
  let L := c / branching x b j * branching x b j
  (j, c, L + (k % 2 ^ b + 2 ^ b - L % 2 ^ b) % 2 ^ b)

namespace StaticData

variable (S : StaticData)

/-- The number of terminals. -/
def numTerm : ℕ := 2 ^ S.x

/-- The number of connectors in the hierarchy. -/
def numConn : ℕ := (connRecs S.H S.x S.b).length

/-- The sections of the layout. Group `g` at depth `t` has index `t · 2^x + g`, and the pair of
groups `c < c'` at depth `j + 1` has the index `pairIdxOf x b j c c' =
(j · 2^x + c) · 2^b + (c' mod 2^b)` (`pairOfIdx` reads the pair back).
0. `[x, b, numConn]`;
1. `owner p` for each terminal `p`;
2. `labelWord (label i)` for each edge `i` of the root host;
3. the host of each group at depths `0, …, leafDepth`, as `Graph.encode`;
4. for each group `c` at depth `j + 1`, the walks `emb j c e` of the edges `e` of its host, in
   `csrList` form;
5. for each pair index `k < leafDepth · 2^x · 2^b`, the connectors `conn j c c'` of the pair
   `(j, c, c') = pairOfIdx x b k`, each as `connWords`, in `csrList` form. -/
def sections : List (List ℕ) :=
  let P := S.numTerm
  let D := leafDepth S.x S.b
  [ [S.x, S.b, S.numConn],
    tabList P S.owner,
    tabList (S.H.host 0 0).m fun i => labelWord (S.label i),
    csrList ((D + 1) * P) fun k => (S.H.host (k / P) (k % P)).encode,
    csrList (D * P) fun k =>
      csrList (S.H.host (k / P + 1) (k % P)).m (S.H.emb (k / P) (k % P)),
    csrList (D * P * 2 ^ S.b) fun k =>
      let l := S.H.conn (pairOfIdx S.x S.b k).1 (pairOfIdx S.x S.b k).2.1
        (pairOfIdx S.x S.b k).2.2
      csrList l.length fun i => connWords (l.getD i (0, 0, [])) ]

/-- The words of the layout. -/
def encode : List ℕ := layoutList S.sections

end StaticData

/-- Memory holds the output `S` of the static construction at `addr`. -/
def StaticOut (mem : ℕ → ℕ) (addr : ℕ) (S : StaticData) : Prop :=
  ListAt mem addr S.encode

/-- Reading section `i` of the static output. -/
theorem StaticOut.section {mem : ℕ → ℕ} {addr : ℕ} {S : StaticData} (h : StaticOut mem addr S)
    {i : ℕ} (hi : i < 6) :
    ListAt mem (addr + 7 + mem (addr + i)) (S.sections.getD i []) := by
  have := listAt_section (bs := S.sections) h (i := i) (by simpa [StaticData.sections] using hi)
  simpa [StaticData.sections] using this

/-! ### The model built from it -/

/-- The pair number of two sibling groups `Y, Z` at depth `j + 1`, as in `pairNum`: the
connectors are stored once, for the smaller group first, so the number is symmetric in `Y, Z`. -/
def pairIdxOf (x b : ℕ) (j Y Z : ℕ) : ℕ :=
  (j * 2 ^ x + min Y Z) * 2 ^ b + max Y Z % 2 ^ b

theorem pairIdxOf_comm (x b j Y Z : ℕ) : pairIdxOf x b j Y Z = pairIdxOf x b j Z Y := by
  simp [pairIdxOf, min_comm, max_comm]

/-- The static part of the model that `Init` builds from `S`, for the constant `a`, the
conductance denominator `d` and the edge count `m`. -/
def StaticData.model (S : StaticData) (a d m : ℕ) : HierModel where
  A := staticArrays S.H S.x S.b S.owner S.label
  pairIdx := pairIdxOf S.x S.b
  ξ := xiOf a d m
  κ := leafDepth S.x S.b * (2 ^ S.b - 1)
  lam := lamOf a d m

/-- The concrete state right after `Init`: the model of `S` and the dynamic state
`DelState.init`, with the abstract state `s`. -/
def initConcrete (S : StaticData) (a : ℕ) (s : PathDSAbsState) : HierConcrete :=
  ⟨S.model a (Nat.ceil (1 / s.φ_in)) s.G.m, ⟨DelState.init, s⟩⟩

/-- **The block of `initConcrete` represents the initial state.** If memory holds the block at
`h`, the model meets `Spec` and `Fits`, and `s` is valid with nothing pruned or deleted, then
memory holds `s` as `initConcrete S a s`. The relation comes from `HierModel.rel_init`. -/
theorem initConcrete_rep (S : StaticData) (a : ℕ) {p : PathDSParams} {s : PathDSAbsState}
    {mem : ℕ → ℕ} {h : ℕ}
    (hspec : (S.model a (Nat.ceil (1 / s.φ_in)) s.G.m).Spec s.G)
    (hfits : (S.model a (Nat.ceil (1 / s.φ_in)) s.G.m).Fits a (Nat.ceil (1 / s.φ_in)) s.G.m)
    (hvalid : s.Valid p) (hV : s.Vhat = ∅) (hD : s.deleted = ∅)
    (hmem : ListAt mem h (initConcrete S a s).encode) :
    (hierRep a).rep h s (initConcrete S a s) mem :=
  ⟨rfl, HierModel.rel_init _ hspec hfits hvalid hV hD, hmem⟩

/-- The abstract state that `Init` creates. -/
def initAbs (phiNum phiDen M : ℕ) (G : Graph) : PathDSAbsState := ⟨phiNum, phiDen, M, G, ∅, ∅⟩

/-- **The postcondition of `Init`.** Under the precondition, with `G` the input graph, the state
`initAbs` meets `initPost`. Validity is `initModel_valid`. -/
theorem initPost_of_initPre (P : PathDSParams) (w : ℕ) {gAddr phiNum phiDen M h : ℕ}
    {G : Graph} {mem mem' : ℕ → ℕ}
    (hpre : (pathDSDataStructure P w).initPre [gAddr, phiNum, phiDen, M, h] mem)
    (hG : GraphAt mem gAddr G) :
    (pathDSDataStructure P w).initPost [gAddr, phiNum, phiDen, M, h] mem
      (initAbs phiNum phiDen M G) mem' := by
  obtain ⟨gAddr', phiNum', phiDen', M', h', G', hargs, _, hGat, h1, h2, hval, hm, hmM, hdeg,
    hcond, _⟩ := hpre
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hGG : G = G' :=
    (graphAt_iff_readGraph.mp hG).symm.trans (graphAt_iff_readGraph.mp hGat)
  subst hGG
  exact ⟨_, _, _, _, _, G, rfl, hG, rfl, rfl, rfl, rfl, rfl, rfl,
    initModel_valid P h1 h2 hval hm hmM hdeg hcond⟩

/-! ### The contract of the rest of `Init` -/

/-- What the rest of `Init` assumes of the static output, beyond its layout: the hypotheses of
`staticArrays_spec_xiOf` and `initRestSteps_le_gamma`, for the constant `a`, the conductance
denominator `d`, the input graph `G` and the bound `M`. -/
structure StaticData.Good (S : StaticData) (a d M : ℕ) (G : Graph) : Prop where
  b_pos : 0 < S.b
  valid : S.H.IsValid S.x S.b
  bounds : S.H.Bounds S.x S.b (lvlBound (hOf d) (uOf a G.m)) (lvlBound (hOf d) (uOf a G.m))
    (lvlBound (hOf d) (uOf a G.m))
  depth : leafDepth S.x S.b ≤ depthOf G.m
  branch : 2 ^ S.b ≤ branchOf G.m
  terms : 2 ^ S.x ≤ 4 * G.m
  verts : G.n ≤ 2 * G.m
  mM : G.m ≤ M
  proj : IsProjection G (S.H.host 0 0).edges S.owner S.label
  label_inj : ∀ j j' e, S.label j = some e → S.label j' = some e → j = j'
  owner_lt : ∀ p < 2 ^ S.x, S.owner p < G.n

/-- The model of a `Good` static output fits the numbers of `HierPaths/Params.lean`. -/
theorem StaticData.fits_of_good {S : StaticData} {a d M : ℕ} {G : Graph} (hS : S.Good a d M G) :
    (S.model a d G.m).Fits a d G.m where
  depth := hS.depth
  conns := Nat.mul_le_mul hS.depth ((Nat.sub_le _ _).trans hS.branch)
  xi := le_rfl
  lam := le_rfl

/-- The arrays of a `Good` static output meet their specification (`staticArrays_spec_xiOf`). -/
theorem StaticData.arrays_of_good {S : StaticData} {a d M : ℕ} {G : Graph} (hS : S.Good a d M G) :
    (S.model a d G.m).A.Spec G (S.model a d G.m).ξ (S.model a d G.m).κ :=
  staticArrays_spec_xiOf hS.b_pos hS.valid hS.bounds hS.depth hS.branch hS.proj hS.label_inj
    hS.owner_lt

/-- The parts of `HierModel.Spec` that do not follow from `Good` alone: the pair arrays and
the degree bound (for the host of `lemma_2` it is `deg_le_card_owned`). -/
structure StaticData.SpecRest (S : StaticData) (a d : ℕ) (G : Graph) : Prop where
  pairs : (S.model a d G.m).A.PairSpec (S.model a d G.m).pairIdx
  deg : ∀ w < G.n, G.deg w ≤ ((S.model a d G.m).A.C.ownedBy w).card

/-- The degree bound of `SpecRest` for the host of `lemma_2`: when the terminals are those of
`hostSize G` with the owners `hostOwner G`, it is `deg_le_card_owned`. -/
theorem StaticData.deg_of_host {S : StaticData} {a d : ℕ} {G : Graph}
    (hx : 2 ^ S.x = hostSize G) (hown : S.owner = hostOwner G) :
    ∀ w < G.n, G.deg w ≤ ((S.model a d G.m).A.C.ownedBy w).card := by
  intro w _
  have : (S.model a d G.m).A.C.ownedBy w =
      (Finset.range (hostSize G)).filter fun p => hostOwner G p = w := by
    show (Finset.range (2 ^ S.x)).filter (fun t => S.owner t = w) = _
    rw [hx, hown]
  rw [this]
  exact deg_le_card_owned G w

/-- `HierModel.Spec` from `Good` and `SpecRest`. The walk lengths are
`connSystem_walk_length_le`. -/
theorem StaticData.spec_of_good {S : StaticData} {a d M : ℕ} {G : Graph} (hS : S.Good a d M G)
    (hR : S.SpecRest a d G) : (S.model a d G.m).Spec G :=
  ⟨S.arrays_of_good hS, hR.pairs, hR.deg, fun _ hc =>
    connSystem_walk_length_le hS.b_pos hS.valid hS.bounds hS.depth hc⟩

/-- The conductance denominator `⌈1/φ⌉` of `φ = phiNum / phiDen`. -/
def dOf (phiNum phiDen : ℕ) : ℕ := Nat.ceil (1 / ((phiNum : ℝ) / (phiDen : ℝ)))

/-- The block that the rest of `Init` writes. -/
def initBlock (S : StaticData) (a : ℕ) (G : Graph) (phiNum phiDen M : ℕ) : List ℕ :=
  (initConcrete S a (initAbs phiNum phiDen M G)).encode

/-- The contract of the static construction, called with the arguments of
`Init`, `[gAddr, phiNum, phiDen, M, h]`, under the precondition of `Init` for the parameters
`P`. It leaves the static output `S` at the heap pointer `h`, ending before the returned heap
pointer, with `Good` and `SpecRest` (`Spec` and `Fits` follow, `StaticData.spec_of_good` and
`StaticData.fits_of_good`); the returned pointer is at most `h + Ks · m · Γ`. It
costs at most `Ks · m · Γ` and uses at most `sS phiNum phiDen n m M` new cells. -/
def StaticContract (w a Ks : ℕ) (P : PathDSParams) (sS : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    Contract :=
  let C := heapContract w
    (fun args mem => (pathDSDataStructure P w).initPre args mem)
    (fun _ _ _ => True)
    (fun args mem => Ks * (readGraph mem (args.getD 0 0)).m *
      gammaHP a (dOf (args.getD 1 0) (args.getD 2 0)) (args.getD 3 0))
    (fun args mem => sS (args.getD 1 0) (args.getD 2 0) (readGraph mem (args.getD 0 0)).n
      (readGraph mem (args.getD 0 0)).m (args.getD 3 0))
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
        ∃ (gAddr phiNum phiDen M h : ℕ) (G : Graph) (S : StaticData),
          args = [gAddr, phiNum, phiDen, M, h] ∧ GraphAt mem gAddr G ∧ StaticOut mem' h S ∧
          h + S.encode.length ≤ v ∧
          S.Good a (dOf phiNum phiDen) M G ∧
          S.SpecRest a (dOf phiNum phiDen) G }

/-- The contract of the rest of `Init`, for the static output `S` and the input graph `G`. The
arguments are those of `Init`, then the heap pointer after the static output:
`[gAddr, phiNum, phiDen, M, h, h₁]`. The procedure overwrites the static output with the block
`initBlock` at `h`, returns a bump heap pointer `v` in `[h + |initBlock|, h₁ + |initBlock|]`,
leaves memory below `h` unchanged and memory from `v` on zero. The cost is `K` per step of the
model (`initRestSteps`) and per word of the block, and the procedure uses at most
`sR phiNum phiDen n m M` cells from `h₁` on. -/
def InitRestContract (w a K : ℕ) (sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (S : StaticData) (G : Graph) :
    Contract where
  pre args mem := ∃ (gAddr phiNum phiDen M h h₁ : ℕ),
    args = [gAddr, phiNum, phiDen, M, h, h₁] ∧ StaticOut mem h S ∧
      h + S.encode.length ≤ h₁ ∧ ZeroFrom mem h₁ ∧ GraphAt mem gAddr G ∧
      gAddr + G.encode.length ≤ h ∧ 1 ≤ phiNum ∧ phiNum ≤ phiDen ∧
      S.Good a (dOf phiNum phiDen) M G ∧ h₁ + sR phiNum phiDen G.n G.m M < 2 ^ w ∧
      xiOf a (dOf phiNum phiDen) G.m < 2 ^ w ∧ lamOf a (dOf phiNum phiDen) G.m < 2 ^ w
  post args mem v mem' := ∃ (gAddr phiNum phiDen M h h₁ : ℕ),
    args = [gAddr, phiNum, phiDen, M, h, h₁] ∧
      h + (initBlock S a G phiNum phiDen M).length ≤ v ∧
      v ≤ h₁ + (initBlock S a G phiNum phiDen M).length ∧
      ListAt mem' h (initBlock S a G phiNum phiDen M) ∧ ZeroFrom mem' v ∧
      ∀ y < h, mem' y = mem y
  cost args _ := K * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m +
    (initBlock S a G (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)).length)

/-- **The cost of the rest of `Init`** is at most `K · (63 · m · Γ + ℓ)`, with `ℓ` the length of
the block, by `initRestSteps_le_gamma`. -/
theorem initRest_cost_le (w a K : ℕ) (ha : 1 ≤ a) (sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (S : StaticData) (G : Graph) {d M : ℕ} (hS : S.Good a d M G) (args : List ℕ)
    (mem : ℕ → ℕ) :
    (InitRestContract w a K sR S G).cost args mem ≤
      K * (63 * G.m * gammaHP a d M +
        (initBlock S a G (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)).length) := by
  show K * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m + _) ≤ _
  have := initRestSteps_le_gamma hS.b_pos hS.valid ha hS.bounds hS.depth hS.branch hS.terms
    hS.verts hS.mM hS.proj hS.owner_lt
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right this _)

end MinCostFlow.HierPaths

end
