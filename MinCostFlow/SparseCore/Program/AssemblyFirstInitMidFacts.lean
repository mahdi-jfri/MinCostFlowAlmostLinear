module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitFront
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBun
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSpanModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitRoots
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartSpace
import Mathlib.Tactic

/-!
# The middle of the build: the facts it needs (`AssemblyFirstInitMidFacts`)

The middle of the build (`asmFirstInitMidStmt`, `AssemblyFirstInitBody.lean`) sorts the roots,
fills P5's table with the slots of the active pairs and starts P6's spanners of those slots. Its
run (`asmFirstInitMid_runs`, `AssemblyFirstInitMid.lean`) chains three run lemmas. This file
proves the small facts that the chain needs between them.
* *The model.* The forest edges of P4's export are the edges of the forest (`asmFi_fe_iff`). The
  sorted copy of the roots has as many members as the roots (`length_eq_of_mem_iff`). Each slot
  of the specs holds a bundle after P5's `initSlots` (`tableAfterInitSlots_some_range`). The graph
  of each listed slot meets `SpanGraphOK` when the start graphs of the active pairs do
  (`asmFi_slotGraphOK`).
* *The space.* P5's blocks and the walks of the tour lists (`slotBlocksSpace_slotSpecsL_le`,
  `asmFi_listSpace_le`), and the three sums of P6's spanner inits (`asmFi_edgeTot_le`,
  `asmFi_exportSpace_le`, `asmFi_activateSpace_le`). Each is a number of slots times a bound in
  the caps.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## The spanner parameters of the build -/

/-- **The spanner parameters of the build**: the sparsifier `impl`, the edge bound `M`, the word
size `w`, the level count `depth`, the vertex cap `2 eCap + splitB + 1`, the edge cap `eCap` and
the split bound `splitB = bundleSplitBudget k M` of the model. -/
noncomputable def asmFiSP (impl : SparsifyImpl) (w M depth k eCap : ℕ) : DSParams :=
  ⟨impl, M, w, depth, 2 * eCap + bundleSplitBudget k M + 1, eCap, bundleSplitBudget k M⟩

/-- The space of one spanner init in the caps of the spanners (`spanActivateSpace_le_caps`). -/
noncomputable def asmFiSpanCapSpace (P : DSParams) : ℕ :=
  100 * ((P.L + 1) * (P.vCap + P.eCap + 1)) +
    (2 * (36 * (P.vCap + 2 * P.eCap + 1)) ^ P.impl.cw +
      30 * (P.eCap + 1) * (⌈P.impl.γ_ℓ P.mMax⌉₊ + 1) + 3 * P.vCap +
      dynGraphSize P.vCap P.eCap + P.eCap + 10)

/-- **The words of the middle**, from the end of the slot lists: the sorted roots (`2 vCap`), P5's
table with its slot blocks and the new cells of the tour, the spanner table (`eCap` words), and
the exports and spanner inits of at most `eCap` slots. -/
noncomputable def asmFiMidSpace (P : DSParams) (vCap eCap : ℕ) : ℕ :=
  5 * vCap + bundleTableFixedSize eCap eCap + eCap * (3 + 24 * eCap) + 3 * eCap + P.vCap +
    eCap * (6 + 10 * P.eCap + (4 + P.vCap + 3 * P.eCap) + asmFiSpanCapSpace P)

/-! ## The model -/

/-- **The forest edges of P4's export** are the edges of the forest of the LSF: the export of the
forest lists each of its edges once, as the first word of a triple. -/
theorem asmFi_fe_iff {w : ℕ} {mem : ℕ → ℕ} {expPtr expEnd L capExp M N vCap eCap : ℕ}
    {cs : CompLSFState} (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap cs)
    (e : ℕ) :
    e ∈ slotForestEdges mem (mem (mem (expPtr + 1) + 3)) (mem (mem (expPtr + 1) + 2)) ↔
      e ∈ cs.lsf.F.F.E := by
  obtain ⟨-, -, -, -, -, hfEx, -⟩ := hExp
  obtain ⟨-, -, -, -, -, hT, hcov, -⟩ := hfEx
  have heq : slotForestEdges mem (mem (mem (expPtr + 1) + 3)) (mem (mem (expPtr + 1) + 2)) =
      (readTriples mem (mem (mem (expPtr + 1) + 3)) (mem (mem (expPtr + 1) + 2))).map
        Prod.fst := by
    simp [slotForestEdges, readTriples, Function.comp_def]
  rw [heq]
  constructor
  · intro he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    exact (hT t ht).1
  · intro he
    obtain ⟨t, ht, rfl⟩ := hcov e he
    exact List.mem_map.mpr ⟨t, ht, rfl⟩

/-- Two lists without repeats and with the same members have the same length. -/
theorem length_eq_of_mem_iff {l l' : List ℕ} (hl : l.Nodup) (hl' : l'.Nodup)
    (h : ∀ x, x ∈ l ↔ x ∈ l') : l.length = l'.length :=
  ((List.perm_ext_iff_of_nodup hl hl').mpr h).length_eq

/-- **Each slot of the specs holds a bundle** after P5's `initSlots` on the empty table. -/
theorem tableAfterInitSlots_some_range {slotCap : ℕ} {mem : ℕ → ℕ} {cmpH bktH B : ℕ}
    {G : MGraph} {S D : List ℕ} (assigns : List (ℕ × ℕ)) (cord : ℕ → List End)
    (rList : List ℕ) (k : ℕ) (hcap : D.length ≤ slotCap) :
    ∀ s ∈ List.range D.length, ∃ hs : s < slotCap, ∃ Bn,
      tableAfterInitSlots (fun _ => none : Fin slotCap → Option BundleState)
        (slotSpecsL mem cmpH bktH B G S D) assigns cord rList k ⟨s, hs⟩ = some Bn := by
  intro s hs
  have hlt := List.mem_range.mp hs
  have hm : s ∈ (slotSpecsL mem cmpH bktH B G S D).map Prod.fst := by
    rw [slotSpecsL_fst]; exact hs
  refine ⟨by omega, ?_⟩
  simp only [tableAfterInitSlots, hm, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- **`SpanGraphOK` of the listed slots.** The graph of the slot of an active pair is the start
graph of the pair (`asmFirstInitSlotGraph_slotOf`), and every listed slot is the slot of an
active pair. -/
theorem asmFi_slotGraphOK (P : DSParams) {L slotCap cap : ℕ} {tr : BundleTreeState L}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S : Fin slotCap → Option BundleState}
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hG : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph)
    (hok : ∀ q ∈ activePairs tr, SpanGraphOK P (tr.initBunG q)) :
    ∀ s ∈ slots, SpanGraphOK P (asmFirstInitSlotGraph S s) := by
  intro s hs
  obtain ⟨q, hq, rfl⟩ := hMap.2.2.1 s hs
  rw [asmFirstInitSlotGraph_slotOf hMatch hG hq]
  exact hok q hq

/-! ## The space -/

/-- **P5's slot blocks**: each of the `|D|` slots has a block of `3 + 6 cap` words, and its cap is
four times its number of edges, which is at most `|S|`. -/
theorem slotBlocksSpace_slotSpecsL_le {mem : ℕ → ℕ} {cmpH bktH B : ℕ} {G : MGraph}
    {S D : List ℕ} :
    slotBlocksSpace (slotSpecsL mem cmpH bktH B G S D) ≤ D.length * (3 + 24 * S.length) := by
  unfold slotBlocksSpace slotSpecsL
  rw [List.map_map]
  refine (sum_map_le_length_mul _ _ _ fun s _ => ?_).trans (by rw [List.length_range])
  simp only [Function.comp_apply, bundleSlotBlockSize]
  have := List.length_filter_le (fun e => D.idxOf (slotKeyOf mem cmpH bktH B G e) = s) S
  omega

/-- A sum of `3 + f a` over a list is three times its length plus the sum of `f`. -/
theorem sum_map_three_add {α : Type} (l : List α) (f : α → ℕ) :
    (l.map fun a => 3 + f a).sum = 3 * l.length + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- **The lists of the tour that P5 walks**: `3 + |cord v|` words for each vertex of `rList`, and
the lists of distinct vertices hold at most `2 m` ends (`coreCord_facts`). -/
theorem asmFi_listSpace_le {cs : CompLSFState} {ord cord : ℕ → List End}
    (hC : CoreCordOf cs ord cord) {rList : List ℕ} (hnd : rList.Nodup) :
    (rList.map fun v => tourBundleSpec.listSpace (cord v).length).sum ≤
      3 * rList.length + 2 * cs.G.m := by
  have hQ := (coreCord_facts hC).2.2.2 rList hnd
  have h := sum_map_three_add rList fun v => (cord v).length
  simp only [tourBundleSpec]
  omega

/-- **P5's space at the init**: the slot blocks and the walks of the tour lists. -/
theorem asmFi_initSlotsSpace_le {cs : CompLSFState} {ord cord : ℕ → List End}
    (hC : CoreCordOf cs ord cord) {rList : List ℕ} (hnd : rList.Nodup) {mem : ℕ → ℕ}
    {cmpH bktH B : ℕ} {G : MGraph} {S D : List ℕ} :
    bundleInitSlotsSpace tourBundleSpec (slotSpecsL mem cmpH bktH B G S D) cord rList ≤
      D.length * (3 + 24 * S.length) + 3 * rList.length + 2 * cs.G.m := by
  unfold bundleInitSlotsSpace
  have h1 := slotBlocksSpace_slotSpecsL_le (mem := mem) (cmpH := cmpH) (bktH := bktH) (B := B)
    (G := G) (S := S) (D := D)
  have h2 := asmFi_listSpace_le hC hnd
  omega

section Span

variable (P : DSParams) {slotCap : ℕ} {S : Fin slotCap → Option BundleState} {slots : List ℕ}

/-- **The edges of the listed slots**: each slot graph has at most `P.eCap` edges. -/
theorem asmFi_edgeTot_le (hok : ∀ s ∈ slots, SpanGraphOK P (asmFirstInitSlotGraph S s)) :
    edgeTot S slots ≤ slots.length * P.eCap := by
  unfold edgeTot
  refine sum_map_le_length_mul _ _ _ fun s hs => ?_
  exact spanGraphOK_m_le (hok s hs)

/-- **The exports of the listed slots**: each has at most `4 + P.vCap + 3 P.eCap` words. -/
theorem asmFi_exportSpace_le (hok : ∀ s ∈ slots, SpanGraphOK P (asmFirstInitSlotGraph S s)) :
    (slots.map fun s => bundleExportSpace (slotB S s)).sum ≤
      slots.length * (4 + P.vCap + 3 * P.eCap) := by
  refine sum_map_le_length_mul _ _ _ fun s hs => ?_
  have hn := spanGraphOK_n_le (hok s hs)
  have hm := spanGraphOK_m_le (hok s hs)
  have e1 : (asmFirstInitSlotGraph S s).n = (slotB S s).vertices.card := rfl
  have e2 : (asmFirstInitSlotGraph S s).m = (slotB S s).edges.card := rfl
  unfold bundleExportSpace
  omega

/-- **The spanner inits of the listed slots**: each takes at most `asmFiSpanCapSpace P` words. -/
theorem asmFi_activateSpace_le
    (hok : ∀ s ∈ slots, SpanGraphOK P (asmFirstInitSlotGraph S s)) :
    (slots.map fun s => spanActivateSpace P (asmFirstInitSlotGraph S s)).sum ≤
      slots.length * asmFiSpanCapSpace P :=
  sum_map_le_length_mul _ _ _ fun s hs => spanActivateSpace_le_caps P (hok s hs)

end Span

/-! ## A call at the end of a statement -/

/-- A call whose body has a run with a postcondition on the returned value and the memory, at the
end of a statement, in the forward form. -/
theorem runs_call_post_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {body : Stmt} {st : State} {vs : List ℕ} {B k T : ℕ}
    {Q_call : ℕ → (ℕ → ℕ) → Prop} {Q : Outcome → State → Prop}
    (hproc : p.procs[f]? = some body) (hargs : evalArgs w st args = some vs)
    (hbody : ∃ o st₁ c₁, Runs w p ω body (startState vs st.mem st.pos) o st₁ c₁ ∧
      Q_call o.value st₁.mem ∧ c₁ ≤ B)
    (hpost : ∀ v mem' pos', Q_call v mem' →
      Q .normal { mem := mem', regs := Function.update st.regs r v, pos := pos' })
    (hc : k + argsSize args + B + 1 ≤ T) :
    ∃ o st' c, Runs w p ω (.call r f args) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩ := hbody
  exact ⟨.normal, { mem := st₁.mem, regs := Function.update st.regs r o₁.value, pos := st₁.pos },
    argsSize args + c₁ + 1, runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hr₁, rfl, rfl,
      rfl⟩, hpost _ _ _ hq₁, by omega⟩

end MinCostFlow.SparseCore.Program
