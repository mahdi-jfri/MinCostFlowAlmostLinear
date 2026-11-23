module

public import MinCostFlow.SparseCore.Program.RestartIface
public import MinCostFlow.MinRatio.Layouts
public import MinCostFlow.DynSpanner.Program.DynGraphBatch

/-!
# The readout data of a branch: what piece P10 proves

Readouts `2` and `3` of the ordered sparse-core contract (`sparseCoreOrdMachineContractKF`, which
has the readouts of `sparseCoreOrdMachineContractK`; Lemma 5.17, page 23) cost a constant. Each writes pointers to data that must already be in
memory: the LSF view of the branch (`LSFAt`, with the stretches in `L_w` limbs) and the graph
`S_cur` (`DynGraphAt`). This file states what the piece that keeps these data does.

* **The data** (`ReadView`). For one branch: the input graph `G` (the domain of the stretch
  table, and the graph whose ends give the core ends), the LSF view `lsf = (st.trees j).cs.lsf`
  (`tool.lsfs`), the graph `S = (st.trees j).S_cur` (`tool.S`), and the integer pairs `num`, `den`
  that the stretch tables hold (the stretch is `num / den`).
* **An update** (`ReadView.step`). The input batch `U` changes `G`. It changes the tree `T` of the
  LSF view by its deletions and vertex splits (`tViewUpdate`, matching `CompLSFState.T`), the forest
  `F` as a subgraph of `G` (`dgBatchTarget 0`), and the stretch of an
  inserted edge to `1`, with the pair `(1, 1)` (as piece P3 stores it). The other changes of the LSF view are new roots and removed forest edges,
  which only the LSF programs of the components know. Piece P4 hands them over as a change
  record (`LSFChange`, `LSFChangeAt`). The output batch `U_S` (written by piece P7) changes `S`.
* **A restart** (`ReadView.rebuildS`). The edges of `S` in the graphs of the restarted bucket
  spanners are replaced by the edges of their new spanners, with the core ends
  `root (tail e)`, `root (head e)` (`coreGraph`). The roots come from the root query of piece P4
  (`RootQueryAt`), since a forest in memory does not give the root of a vertex in constant time.
* **The statement** (`ReadBranchAt`, `sig_readBranch`). One representation of `ReadView` and five
  procedures: the two readouts, the update, the restart and the initialization, each with its
  post and its cost.

Only definitions are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart MinCostFlow.Chain

/-! ## The data of a branch and how an update changes it -/

/-- The readout data of one branch: the input graph `G`, the LSF view `lsf`, the sparsified core
`S`, and the integer pairs `num e`, `den e` whose quotient is the stretch of the edge `e`. For the
bundle tool on a nonempty state the first three are `a.G`, `tool.lsfs a.st j` and `tool.S a.st j`
(Lemma 5.17, page 23). The pairs are those of the LSF data of piece P4 at the initialization, and
`(1, 1)` for each edge inserted since. -/
structure ReadView where
  G : MGraph
  lsf : LSF
  S : MGraph
  num : ℕ → ℤ
  den : ℕ → ℤ

/-- One update on the tree `T` of the LSF view: vertex splits split `T`, deletions remove the
deleted edge from `T` (matching `CompLSFState.T`), and insertions leave `T` as it is. -/
def tViewUpdate (T : MGraph) : Update → MGraph
  | .split v v' St Sh => T.applyUpdate (.split v v' St Sh)
  | .insert _ _ _ => T
  | .delete e => T.applyUpdate (.delete e)

/-- One update on the stretch table: an inserted edge gets stretch `1` (`compLSFStepSingle`). -/
noncomputable def wstrViewUpdate (wstr : ℕ → ℝ) : Update → ℕ → ℝ
  | .insert e _ _ => Function.update wstr e 1
  | .split _ _ _ _ => wstr
  | .delete _ => wstr

/-- One update on a table of pairs: an inserted edge gets the value `1`. -/
def pairViewUpdate (f : ℕ → ℤ) : Update → ℕ → ℤ
  | .insert e _ _ => Function.update f e 1
  | .split _ _ _ _ => f
  | .delete _ => f

/-- The change of the LSF view that the input batch does not show: the new roots and the forest
edges that leave the forest. Piece P4 computes it (`LSFChange.Exact`). -/
structure LSFChange where
  roots : List ℕ
  fDel : List ℕ

/-- The number of entries of a change record. -/
def LSFChange.size (c : LSFChange) : ℕ := c.roots.length + c.fDel.length

/-- The change record at `a`: the number of new roots, the roots, the number of removed forest
edges, and these edges. -/
def LSFChangeAt (mem : ℕ → ℕ) (a : ℕ) (c : LSFChange) : Prop :=
  mem a = c.roots.length ∧ ListAt mem (a + 1) c.roots ∧
    mem (a + 1 + c.roots.length) = c.fDel.length ∧ ListAt mem (a + 2 + c.roots.length) c.fDel

/-- The words of a change record. -/
def LSFChange.words (c : LSFChange) : ℕ := 2 + c.size

/-- The record is the change of the LSF view from `lsf` to `lsf'`: its roots are the new roots and
its edges the forest edges that leave, each listed once. -/
def LSFChange.Exact (c : LSFChange) (lsf lsf' : LSF) : Prop :=
  c.roots.Nodup ∧ c.roots.toFinset = lsf'.F.R \ lsf.F.R ∧
    c.fDel.Nodup ∧ c.fDel.toFinset = lsf.F.F.E \ lsf'.F.F.E

/-- The LSF view after the input batch `U` and the change record `c`. -/
noncomputable def lsfViewStep (lsf : LSF) (U : List Update) (c : LSFChange) : LSF :=
  open Classical in
  let F' := U.foldl (dgBatchTarget 0) lsf.F.F
  { T := U.foldl tViewUpdate lsf.T
    F := { F := { F' with E := F'.E \ c.fDel.toFinset }, R := lsf.F.R ∪ c.roots.toFinset }
    wstr := U.foldl wstrViewUpdate lsf.wstr }

/-- The data after an update with input batch `U`, LSF change `c` and output batch `U_S`. -/
noncomputable def ReadView.step (v : ReadView) (U : List Update) (c : LSFChange)
    (U_S : List Update) : ReadView :=
  { G := v.G.applyBatch U, lsf := lsfViewStep v.lsf U c, S := v.S.applyBatch U_S,
    num := U.foldl pairViewUpdate v.num, den := U.foldl pairViewUpdate v.den }

/-- The data after a restart in which the graph `S` loses the edges of `old` (the edges of the old
bundle graphs) and of `new` (the edges of the new spanners) and gains the edges of `new` that are
edges of `G` with both core ends in `S`, at their core ends (`coreGraph`, Definition 5.6,
page 18). -/
noncomputable def ReadView.rebuildS (v : ReadView) (old new : Finset ℕ) : ReadView :=
  open Classical in
  let add := (new ∩ v.G.E).filter fun e =>
    (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V
  { v with
    S := { V := v.S.V
           E := (v.S.E \ (old ∪ new)) ∪ add
           tail := fun e => if e ∈ add then (coreGraph v.G v.lsf).tail e else v.S.tail e
           head := fun e => if e ∈ add then (coreGraph v.G v.lsf).head e else v.S.head e } }

/-- The edges of the graph of the spanner of slot `s` (empty if the slot is empty). -/
noncomputable def slotGE (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap) (s : ℕ) :
    Finset ℕ :=
  if hs : s < cap then
    match S ⟨s, hs⟩ with
    | some d => (d.state P).G.E
    | none => ∅
  else ∅

/-- The union of the edges of the graphs of the listed slots. -/
noncomputable def slotsGE (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap)
    (slots : List ℕ) : Finset ℕ :=
  slots.toFinset.biUnion (slotGE P S)

/-- The data after a restart of the listed slots, with the new bucket spanners `S6`. -/
noncomputable def ReadView.rebuild (P : DSParams) {cap : ℕ} (v : ReadView)
    (S6 : BucketSpannerState cap) (slots : List ℕ) : ReadView :=
  v.rebuildS (slotsGE P S6 slots) (slotsHE P S6 slots)

/-- The words a restart reads: the edges of the graphs and of the spanners of the listed slots. -/
noncomputable def rebuildSize (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) : ℕ :=
  (slots.map fun s => (slotGE P S6 s).card + (slotHE P S6 s).card).sum

/-- The data of an empty state: empty graphs, the empty LSF (`emptyLSF`, all stretches `1`) and the
pairs `(1, 1)`. -/
def emptyView : ReadView :=
  ⟨SparseCore.emptyGraph, SparseCore.emptyLSF, SparseCore.emptyGraph, fun _ => 1, fun _ => 1⟩

/-! ## What the representation keeps true -/

/-- The conditions under which the data can be kept: valid graphs within the name bounds, the tree
and the forest on the vertices of `G` (the tree edges within `tCap`), the forest a subgraph of `G`
with the ends of `G`, the tree with the ends of `G` on its edges that are edges of `G`, each vertex
connected in the forest to exactly one root, `S` a valid graph within the bounds, and for each edge
of `G` a positive `den e` with `num e / den e` the stretch. These hold for the model (`CompLSFInv`,
`LSF.Holds`); an update asks them of the data it leaves. -/
def ReadView.Inv (vCap eCap tCap : ℕ) (v : ReadView) : Prop :=
  v.G.IsValid ∧ (∀ x ∈ v.G.V, x < vCap) ∧ (∀ e ∈ v.G.E, e < eCap) ∧ eCap ≤ tCap ∧
  v.lsf.T.IsValid ∧ v.lsf.T.V = v.G.V ∧ (∀ e ∈ v.lsf.T.E, e < tCap) ∧
  (∀ e ∈ v.lsf.T.E, e ∈ v.G.E → v.lsf.T.tail e = v.G.tail e ∧ v.lsf.T.head e = v.G.head e) ∧
  v.lsf.F.F.V = v.G.V ∧ v.G.IsSubgraph v.lsf.F.F ∧ v.lsf.F.R ⊆ v.G.V ∧
  (∀ x ∈ v.G.V, ∃! r, r ∈ v.lsf.F.R ∧ v.lsf.F.F.Connected x r) ∧
  v.S.IsValid ∧ (∀ x ∈ v.S.V, x < vCap) ∧ (∀ e ∈ v.S.E, e < eCap) ∧
  (∀ e ∈ v.G.E, 0 < v.den e ∧ (v.num e : ℝ) / v.den e = v.lsf.wstr e)

/-! ## The readouts -/

/-- The stretch tables of the descriptor at `a` (numerator table at `mem a`, denominator table at
`mem (a + 1)`, `L_w` limbs of `4` bits per edge) hold exactly the integers `num e` and `den e`, for
each edge `e` of `E`. -/
def StretchPairsAt (mem : ℕ → ℕ) (a L_w : ℕ) (E : Finset ℕ) (num den : ℕ → ℤ) : Prop :=
  ∀ e ∈ E, Num.intVal mem (mem a + e * L_w) 4 L_w = num e ∧
    Num.intVal mem (mem (a + 1) + e * L_w) 4 L_w = den e

/-- What the LSF readout writes at `h`: the four pointers of `LSFAt` (limbs of `4` bits, `L_w`
limbs, precision `P`, stretch domain `G.E`) and the limb count `L_w` at `h + 4`. This is the post
of readout `2` of `sparseCoreOrdMachineContractKF` for the data of the branch. The stretch tables
also hold the pairs `num`, `den` exactly (`StretchPairsAt`), so a caller can read more than the
quotient: the pair `(1, 1)` for an edge inserted since the initialization, and the pair of P4
otherwise. -/
def ReadLSFOut (mem : ℕ → ℕ) (h L_w P : ℕ) (v : ReadView) : Prop :=
  mem (h + 4) = L_w ∧ (∃ forestVCap forestECap,
    LSFAt mem h forestVCap forestECap 4 L_w P v.G.E v.lsf) ∧
  StretchPairsAt mem (mem (h + 3)) L_w v.G.E v.num v.den

/-- What the sparsifier readout writes at `h`: a pointer to `S` in `DynGraphAt` form. This is the
post of readout `3` of the contract for the data of the branch. -/
def ReadSOut (mem : ℕ → ℕ) (h : ℕ) (v : ReadView) : Prop :=
  ∃ graphVCap graphECap, DynGraphAt mem (mem h) graphVCap graphECap v.S

/-! ## The root query of piece P4 -/

/-- **Interface of the root query (piece P4, operation `3` of `compLSFDS`).**
A representation `R` of some state, a root function `root s j u` (in P4, `(S j).RF.root u`),
a condition `ok s j u` under which the query may be asked (in P4, `j < k` and `u` a vertex), and a
procedure `f`, called as `[b, j, u, h]`, that writes `root s j u` at `h`, keeps the state, allocates
at most one word, and costs at most `cost` against the potential. -/
structure RootQueryAt (w : ℕ) (p : Program) (f : ℕ) where
  σ : Type
  R : DSRep σ
  root : σ → ℕ → ℕ → ℕ
  ok : σ → ℕ → ℕ → Prop
  cost : ℕ
  R_local : R.Local
  runs : ∀ (b j u h : ℕ) (s : σ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      b < 2 ^ w → j < 2 ^ w → u < 2 ^ w → h < 2 ^ w → ok s j u →
      R.rep b s x mem → (∀ a, R.foot b x a → a < h) → ZeroFrom mem h → h + 1 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [b, j, u, h] mem pos) o st' c ∧
        st'.mem h = root s j u ∧ R.rep b s x' st'.mem ∧
        h ≤ o.value ∧ o.value ≤ h + 1 ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ R.foot b x a → st'.mem a = mem a) ∧
        (∀ a, R.foot b x' a → R.foot b x a ∨ (h ≤ a ∧ a < o.value)) ∧
        c + R.phi b x' st'.mem ≤ cost + R.phi b x mem

/-! ## The statement -/

/-- A call of procedure `f` with arguments `args` on memory `mem`, where `R` holds data with
handle `r` as the concrete state `y`, ends with `R` holding `v'`, the answer `out` in the final
memory, memory below `h` changed only in the old footprint, the new footprint in the old one and
the new cells `[h, o)`, at most `space` new cells, and cost plus new potential at most `cost` plus
the old potential `phi`. -/
def ReadCallEnds (R : DSRep ReadView) (w : ℕ) (p : Program) (f : ℕ) (args : List ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (r : ℕ) (y : R.τ) (h : ℕ) (v' : ReadView)
    (out : (ℕ → ℕ) → Prop) (space cost phi : ℕ) : Prop :=
  ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y',
    Runs w p ω body (startState args mem pos) o st' c ∧
    R.rep r v' y' st'.mem ∧ out st'.mem ∧
    h ≤ o.value ∧ o.value ≤ h + space ∧ ZeroFrom st'.mem o.value ∧
    (∀ a < h, ¬ R.foot r y a → st'.mem a = mem a) ∧
    (∀ a, R.foot r y' a → R.foot r y a ∨ (h ≤ a ∧ a < o.value)) ∧
    c + R.phi r y' st'.mem ≤ cost + phi

/-- The `n` words from `a` are words, lie below `h`, and are outside the footprint `foot`. -/
def InputAt (w : ℕ) (mem : ℕ → ℕ) (foot : ℕ → Prop) (a n h : ℕ) : Prop :=
  a + n ≤ h ∧ ∀ i < n, mem (a + i) < 2 ^ w ∧ ¬ foot (a + i)

/-- The data that the initialization reads: `G`, `T`, `F` and `S` as exported graphs
(`ExportAt`, at `gD`, `tD`, `fD`, `sD`), the `nR` roots listed at `rootsPtr`, and the pairs
`num`, `den` of the edges of `G` as numerator and denominator tables of stride `L_w` at `numPtr`,
`denPtr` (limbs of `4` bits). -/
def ReadInitAt (mem : ℕ → ℕ) (hEnd L_w gD tD fD rootsPtr nR numPtr denPtr sD : ℕ)
    (v : ReadView) : Prop :=
  ExportAt mem gD hEnd v.G ∧ ExportAt mem tD hEnd v.lsf.T ∧ ExportAt mem fD hEnd v.lsf.F.F ∧
  ExportAt mem sD hEnd v.S ∧
  (∃ roots : List ℕ, roots.length = nR ∧ roots.Nodup ∧ roots.toFinset = v.lsf.F.R ∧
    ListAt mem rootsPtr roots ∧ rootsPtr + nR ≤ hEnd) ∧
  (∀ e ∈ v.G.E, numPtr + (e + 1) * L_w ≤ hEnd ∧ denPtr + (e + 1) * L_w ≤ hEnd) ∧
  (∀ e ∈ v.G.E,
    Num.Valid mem (numPtr + e * L_w) 4 L_w ∧ Num.Valid mem (denPtr + e * L_w) 4 L_w ∧
    Num.intVal mem (numPtr + e * L_w) 4 L_w = v.num e ∧
    Num.intVal mem (denPtr + e * L_w) 4 L_w = v.den e)

/-- The size of the data of an initialization: the vertices and edges of the four graphs and the
roots. -/
def readInitSize (v : ReadView) : ℕ :=
  v.G.n + v.G.m + v.lsf.T.n + v.lsf.T.m + v.lsf.F.F.m + v.lsf.F.R.card + v.S.n + v.S.m

/-- The space that an update, a restart or an initialization may allocate, for `x` input words:
`mul · (vCap + tCap + x + 1) · (L_w + 1)`. It is a polynomial in the fixed sizes and `x`, and it
does not depend on the heap pointer. -/
def readSpace (mul vCap tCap L_w x : ℕ) : ℕ := mul * (vCap + tCap + x + 1) * (L_w + 1)

/-- **What piece P10 proves, for one branch.** A local representation `R` of the data
(`ReadView`) with the bounds `vCap`, `eCap` on the names of `G` and `S`, `tCap` on the names of
the tree edges, `L_w` limbs and precision `P` for the stretches, and five procedures of `p` at
`b + readIdx i`, each with its run:
* `i = 0`, LSF readout `[r, h]`: writes `ReadLSFOut` at `h` (five words), at cost `mul`;
* `i = 1`, sparsifier readout `[r, h]`: writes `ReadSOut` at `h` (one word), at cost `mul`;
* `i = 2`, update `[r, batch, words, chg, us, usWords, h]`: reads the input batch `U` on `G`, the
  change record `c` and the output batch `U_S` on `S`, and leaves `v.step U c U_S`, at cost
  `mul · ((words + usWords + 1) · (L_w + 1) + c.size)`;
* `i = 3`, restart `[r, spanTbl, n, slotsPtr, b4, j, h]`: reads the spanners of the `n` listed
  slots of the bucket spanner table (P6) and the roots of branch `j` through the root query `Q` of
  P4 at handle `b4`, and leaves `v.rebuild SP S6 slots`, at cost
  `(mul + 2 · Q.cost) · (rebuildSize + n + 1)`;
* `i = 4`, initialization `[vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h]`:
  builds the data read by `ReadInitAt` with handle `h`, at cost `mul · (readInitSize + 1) · (L_w + 1)`.
The update asks `ReadView.Inv` of the data it leaves, and the initialization of the data it
builds. The update, the restart and the initialization allocate at most `readSpace` cells, a
polynomial in `vCap`, `tCap`, `L_w` and the input words. On an empty state (no vertices), the data
is `emptyView`, which the initialization builds from four exports of the empty graph and no roots;
its readouts then write an empty `LSFAt` and `DynGraphAt`. -/
structure ReadBranchAt (R : DSRep ReadView) (w vCap eCap tCap L_w P : ℕ) (SP : DSParams)
    (cap : ℕ) (p : Program) (b : ℕ) (readIdx : ℕ → ℕ) (fRoot : ℕ) (Q : RootQueryAt w p fRoot)
    (mul : ℕ) : Prop where
  readLSF : ∀ (r h : ℕ) (v : ReadView) (y : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
    r < 2 ^ w → h < 2 ^ w → R.rep r v y mem → (∀ a, R.foot r y a → a < h) → ZeroFrom mem h →
    h + 5 < 2 ^ w →
    ReadCallEnds R w p (b + readIdx 0) [r, h] mem pos ω r y h v
      (fun mem' => ReadLSFOut mem' h L_w P v) 5 mul (R.phi r y mem)
  readS : ∀ (r h : ℕ) (v : ReadView) (y : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
    r < 2 ^ w → h < 2 ^ w → R.rep r v y mem → (∀ a, R.foot r y a → a < h) → ZeroFrom mem h →
    h + 1 < 2 ^ w →
    ReadCallEnds R w p (b + readIdx 1) [r, h] mem pos ω r y h v
      (fun mem' => ReadSOut mem' h v) 1 mul (R.phi r y mem)
  step : ∀ (r batch words chg us usWords h : ℕ) (v : ReadView) (y : R.τ) (U U_S : List Update)
      (c : LSFChange) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
    (∀ a ∈ [r, batch, words, chg, us, usWords, h], a < 2 ^ w) →
    R.rep r v y mem → (∀ a, R.foot r y a → a < h) → ZeroFrom mem h →
    BatchAt mem batch v.G U words → v.G.BatchIsValid U → BatchWithinCaps vCap eCap U →
    InputAt w mem (R.foot r y) batch words h →
    LSFChangeAt mem chg c → InputAt w mem (R.foot r y) chg c.words h →
    BatchAt mem us v.S U_S usWords → v.S.BatchIsValid U_S → BatchWithinCaps vCap eCap U_S →
    InputAt w mem (R.foot r y) us usWords h →
    (∀ k (hk : k < U.length), ∀ e x z, U[k] = Update.insert e x z →
      e ∉ ((U.take k).foldl tViewUpdate v.lsf.T).E) →
    (v.step U c U_S).Inv vCap eCap tCap →
    h + readSpace mul vCap tCap L_w (words + c.words + usWords) < 2 ^ w →
    ReadCallEnds R w p (b + readIdx 2) [r, batch, words, chg, us, usWords, h] mem pos ω r y h
      (v.step U c U_S) (fun _ => True) (readSpace mul vCap tCap L_w (words + c.words + usWords))
      (mul * ((words + usWords + 1) * (L_w + 1) + c.size)) (R.phi r y mem)
  restart : ∀ (r spanTbl slotsPtr h b4 j : ℕ) (slots : List ℕ) (v : ReadView) (y : R.τ)
      (S6 : BucketSpannerState cap) (x6 : (bucketSpannerRep SP cap).τ) (s4 : Q.σ) (x4 : Q.R.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
    r < 2 ^ w → spanTbl < 2 ^ w → slots.length < 2 ^ w → slotsPtr < 2 ^ w → b4 < 2 ^ w →
    j < 2 ^ w → h < 2 ^ w → ListAt mem slotsPtr slots → slotsPtr + slots.length ≤ h →
    (∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome) →
    R.rep r v y mem → (bucketSpannerRep SP cap).rep spanTbl S6 x6 mem →
    Q.R.rep b4 s4 x4 mem → (∀ u ∈ v.G.V, Q.ok s4 j u ∧ Q.root s4 j u = v.lsf.F.root u) →
    (∀ a, R.foot r y a → a < h) → (∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → a < h) →
    (∀ a, Q.R.foot b4 x4 a → a < h) →
    (∀ a, R.foot r y a → ¬ (bucketSpannerRep SP cap).foot spanTbl x6 a) →
    (∀ a, R.foot r y a → ¬ Q.R.foot b4 x4 a) →
    (∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → ¬ Q.R.foot b4 x4 a) →
    (∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length → ¬ R.foot r y a) →
    ZeroFrom mem h → h + readSpace mul vCap tCap L_w (rebuildSize SP S6 slots + slots.length) < 2 ^ w →
    ∃ body, p.procs[b + readIdx 3]? = some body ∧ ∃ o st' c y' x4',
      Runs w p ω body (startState [r, spanTbl, slots.length, slotsPtr, b4, j, h] mem pos)
        o st' c ∧
      R.rep r (v.rebuild SP S6 slots) y' st'.mem ∧ Q.R.rep b4 s4 x4' st'.mem ∧
      h ≤ o.value ∧ o.value ≤ h + readSpace mul vCap tCap L_w (rebuildSize SP S6 slots + slots.length) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ R.foot r y a → ¬ Q.R.foot b4 x4 a → st'.mem a = mem a) ∧
      (∀ a, R.foot r y' a → R.foot r y a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, Q.R.foot b4 x4' a → Q.R.foot b4 x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, R.foot r y' a → ¬ Q.R.foot b4 x4' a) ∧
      c + R.phi r y' st'.mem + Q.R.phi b4 x4' st'.mem ≤
        (mul + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) +
          R.phi r y mem + Q.R.phi b4 x4 mem
  init : ∀ (gD tD fD rootsPtr nR numPtr denPtr sD h : ℕ) (v : ReadView) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
    (∀ a ∈ [gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h], a < 2 ^ w) →
    ReadInitAt mem h L_w gD tD fD rootsPtr nR numPtr denPtr sD v →
    v.Inv vCap eCap tCap → ZeroFrom mem h →
    h + readSpace mul vCap tCap L_w (readInitSize v) < 2 ^ w →
    ∃ body, p.procs[b + readIdx 4]? = some body ∧ ∃ o st' c y,
      Runs w p ω body
        (startState [vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h]
          mem pos) o st' c ∧
      R.rep h v y st'.mem ∧
      h ≤ o.value ∧ o.value ≤ h + readSpace mul vCap tCap L_w (readInitSize v) ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem a) ∧ (∀ a, R.foot h y a → h ≤ a ∧ a < o.value) ∧
      c + R.phi h y st'.mem ≤ mul * (readInitSize v + 1) * (L_w + 1)

/-- **The main statement of piece P10.** There is a constant `mul`, free of the input, such that
for every word size, name bounds, limb count, precision, spanner parameters, program holding the
procedures of the piece at `b` (`HasReadProcs p b fRoot`), and root query `Q` of P4 at `fRoot`,
some local representation meets `ReadBranchAt` with costs and space (`readSpace`) given by `mul`.
The word condition lets every name, every address of the data and every limb offset `e · L_w` fit
in a word, and `1 ≤ L_w` lets the pair `(1, 1)` of an inserted edge fit in the tables. -/
def sig_readBranch (HasReadProcs : Program → ℕ → ℕ → Prop) (readIdx : ℕ → ℕ) : Prop :=
  ∃ mul : ℕ, ∀ (w vCap eCap tCap L_w P : ℕ) (SP : DSParams)
    (cap : ℕ) (p : Program) (b fRoot : ℕ) (Q : RootQueryAt w p fRoot),
    HasReadProcs p b fRoot → SP.w = w → SP.eCap ≤ eCap → eCap ≤ tCap →
    1 ≤ L_w → (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w →
    ∃ R : DSRep ReadView, R.Local ∧
      ReadBranchAt R w vCap eCap tCap L_w P SP cap p b readIdx fRoot Q mul

end MinCostFlow.SparseCore.Program.Read
