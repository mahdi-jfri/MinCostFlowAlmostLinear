module

public import MinCostFlow.SparseCore.CompLSFBounds
public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Expander.Components
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic

/-!
# The components of the graph at the init: the arithmetic (`AssemblyFirstInitCompMath`)

The bundle side of a branch keeps, for each vertex of `G₀`, the index of its component in a list
`comps` of the components of `G₀` (`AsmSdMapsAt`). At the init the program finds the components
with a breadth-first search (`bfsLabelsProc`, `Expander/BfsCompProg.lean`). That search works on a
graph on the vertices `0, …, n - 1` (`Cited.Graph`), so the program renames the vertex `vL[x]` of
`G` to its position `x` in the vertex list `vL` of the memory form of `G` (`dynCited`). The search
gives a label to each position, with equal labels exactly on connected vertices
(`dynCited_lab_iff`).

Then the program turns the labels into the indices `0, 1, …` of the components, in the order of
their first position. A position `x` is a *representative* (`isRep`) when no earlier position has
its label. The list of the representatives is `repList`, and `repRank x` counts the
representatives before `x`. The component with index `c` is the component of the vertex at the
`c`-th representative (`compList`). The main results are `compList_nodup`, `mem_compList_iff`
and `compList_map`: if the array holds `repRank r` at each vertex whose representative is `r`,
then it holds `c` at each vertex of the component with index `c`.

At the init the graph of the LSF state of each component `C` has the vertices `C`
(`compSt_V_subset_init`), so the array also holds `c` on those vertices.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LSF MinCostFlow.Expander MinCostFlow.SparseCore

/-! ## The graph on the positions -/

/-- The graph `G` on the positions of its vertices in the list `vL`: the vertex `x < n` is
`vL[x]`, and edge `i` joins the positions of the ends of `eL[i]`. -/
def dynCited (n : ℕ) (vL eL : List ℕ) (G : MGraph) : Cited.Graph :=
  ⟨n, eL.map fun e => (vL.idxOf (G.tail e), vL.idxOf (G.head e))⟩

theorem dynCited_isValid {n : ℕ} {vL eL : List ℕ} {G : MGraph} (hG : G.IsValid)
    (hn : vL.length = n) (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V) (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E) :
    (dynCited n vL eL G).IsValid := by
  intro p hp
  simp only [dynCited, List.mem_map] at hp
  obtain ⟨e, he, rfl⟩ := hp
  have heG := (heMem e).mp he
  refine ⟨?_, ?_⟩
  · rw [← hn]; exact List.idxOf_lt_length_of_mem ((hvMem _).mpr (hG e heG).1)
  · rw [← hn]; exact List.idxOf_lt_length_of_mem ((hvMem _).mpr (hG e heG).2)

/-- A walk of `G` gives a path along the edges of the graph on the positions. -/
theorem dynCited_path_of_walk {n : ℕ} {vL eL : List ℕ} {G : MGraph}
    (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E) {u v : ℕ} {W : List (ℕ × Bool)} (hW : G.IsWalk u v W) :
    ∃ P, Cited.IsPathAlong (dynCited n vL eL G).edges (vL.idxOf u) (vL.idxOf v) P := by
  induction hW with
  | nil u => exact ⟨[vL.idxOf u], isPathAlong_singleton _ _⟩
  | @cons u v x P hx hsrc _ ih =>
    obtain ⟨Q, hQ⟩ := ih
    have hmem : (vL.idxOf (G.tail x.1), vL.idxOf (G.head x.1)) ∈ (dynCited n vL eL G).edges :=
      List.mem_map.mpr ⟨x.1, (heMem _).mpr hx, rfl⟩
    refine ⟨vL.idxOf u :: Q, isPathAlong_cons ?_ hQ⟩
    subst hsrc
    unfold MGraph.src MGraph.dst
    cases x.2
    · exact Or.inr (by simpa using hmem)
    · exact Or.inl (by simpa using hmem)

/-- A path along the edges of the graph on the positions gives a walk of `G`. -/
theorem dynCited_connected_of_path {n : ℕ} {vL eL : List ℕ} {G : MGraph} (hG : G.IsValid)
    (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V) (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E) :
    ∀ (P : List ℕ) (x y : ℕ), Cited.IsPathAlong (dynCited n vL eL G).edges x y P →
      G.Connected (vL.getD x 0) (vL.getD y 0) := by
  have hend : ∀ v ∈ G.V, vL.getD (vL.idxOf v) 0 = v := by
    intro v hv
    have hlt := List.idxOf_lt_length_of_mem ((hvMem v).mpr hv)
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]
  have hedge : ∀ a b, (a, b) ∈ (dynCited n vL eL G).edges →
      G.Connected (vL.getD a 0) (vL.getD b 0) := by
    intro a b hab
    simp only [dynCited, List.mem_map, Prod.mk.injEq] at hab
    obtain ⟨e, he, rfl, rfl⟩ := hab
    have heG := (heMem e).mp he
    rw [hend _ (hG e heG).1, hend _ (hG e heG).2]
    exact connected_of_edge heG
  intro P
  induction P with
  | nil => intro x y hP; simp [Cited.IsPathAlong] at hP
  | cons a rest ih =>
    intro x y hP
    obtain ⟨hh, hl, hc⟩ := hP
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact connected_refl G _
    | cons b bs =>
      rw [List.isChain_cons_cons] at hc
      have hrest := ih b y ⟨rfl, by simpa [List.getLast?_cons] using hl, hc.2⟩
      rcases hc.1 with h | h
      · exact connected_trans (hedge _ _ h) hrest
      · exact connected_trans (connected_symm (hedge _ _ h)) hrest

/-- **Paths on the positions are walks of `G`.** For positions `x, y < n`, there is a path from `x`
to `y` along the edges of `dynCited n vL eL G` exactly when `vL[x]` and `vL[y]` are connected in
`G`. -/
theorem dynCited_path_iff {n : ℕ} {vL eL : List ℕ} {G : MGraph} (hG : G.IsValid)
    (hvNd : vL.Nodup) (hn : vL.length = n) (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E) {x y : ℕ} (hx : x < n) (hy : y < n) :
    (∃ P, Cited.IsPathAlong (dynCited n vL eL G).edges x y P) ↔
      G.Connected (vL.getD x 0) (vL.getD y 0) := by
  refine ⟨fun ⟨P, hP⟩ => dynCited_connected_of_path hG hvMem heMem P x y hP, fun ⟨W, hW⟩ => ?_⟩
  obtain ⟨P, hP⟩ := dynCited_path_of_walk (n := n) heMem hW
  have hix : vL.idxOf (vL.getD x 0) = x := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hvNd.idxOf_getElem x (by omega)
  have hiy : vL.idxOf (vL.getD y 0) = y := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hvNd.idxOf_getElem y (by omega)
  rw [hix, hiy] at hP
  exact ⟨P, hP⟩

/-- Two labelings with the same parts have the same fibers. -/
theorem partsOf_fiber_iff {G : Cited.Graph} {L₁ L₂ : List ℕ}
    (hparts : Cited.partsOf G L₁ = Cited.partsOf G L₂) {x y : ℕ} (hx : x < G.n) (hy : y < G.n) :
    L₁.getD x 0 = L₁.getD y 0 ↔ L₂.getD x 0 = L₂.getD y 0 := by
  have hfib : G.verts.filter (fun z => L₁.getD z 0 = L₁.getD x 0) ∈ Cited.partsOf G L₂ := by
    rw [← hparts]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_range.mpr hx, rfl⟩
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hfib
  have hmem : ∀ t, t < G.n → (L₁.getD t 0 = L₁.getD x 0 ↔ L₂.getD t 0 = L₂.getD z 0) := by
    intro t ht
    have := congrArg (t ∈ ·) hz
    simp only [Cited.Graph.verts, Finset.mem_filter, Finset.mem_range, eq_iff_iff] at this
    simpa [ht] using this.symm
  have hxz := (hmem x hx).mp rfl
  rw [eq_comm, hmem y hy, hxz, eq_comm]

/-- **The labels of the search are the components.** If the labels `lab x` of the positions
`x < n` have the parts of `compLabels` of the graph on the positions (the post of
`bfsLabelsProc`), then two positions have the same label exactly when their vertices are
connected in `G`. -/
theorem dynCited_lab_iff {n : ℕ} {vL eL : List ℕ} {G : MGraph} (hG : G.IsValid)
    (hvNd : vL.Nodup) (hn : vL.length = n) (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E) {lab : ℕ → ℕ}
    (hparts : Cited.partsOf (dynCited n vL eL G) ((List.range n).map lab) =
      Cited.partsOf (dynCited n vL eL G) (compLabels (dynCited n vL eL G)))
    {x y : ℕ} (hx : x < n) (hy : y < n) :
    lab x = lab y ↔ G.Connected (vL.getD x 0) (vL.getD y 0) := by
  have hval := dynCited_isValid hG hn hvMem heMem
  have hfib := partsOf_fiber_iff hparts (x := x) (y := y) hx hy
  have hgx : ((List.range n).map lab).getD x 0 = lab x := by
    rw [List.getD_eq_getElem _ _ (by simpa using hx)]; simp
  have hgy : ((List.range n).map lab).getD y 0 = lab y := by
    rw [List.getD_eq_getElem _ _ (by simpa using hy)]; simp
  rw [hgx, hgy] at hfib
  rw [hfib, compLabels_eq_iff_reachable hval hx hy]
  exact dynCited_path_iff hG hvNd hn hvMem heMem hx hy

/-! ## From labels to indices -/

/-- Position `x` is a representative of its label: no earlier position has its label. -/
def isRep (lab : ℕ → ℕ) (x : ℕ) : Bool :=
  (List.range x).all fun z => lab z != lab x

/-- The representatives below `n`, in order. -/
def repList (lab : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).filter (isRep lab)

/-- The number of representatives before `x`. -/
def repRank (lab : ℕ → ℕ) (x : ℕ) : ℕ :=
  (repList lab x).length

theorem isRep_iff {lab : ℕ → ℕ} {x : ℕ} : isRep lab x = true ↔ ∀ z < x, lab z ≠ lab x := by
  simp [isRep]

theorem repRank_succ (lab : ℕ → ℕ) (x : ℕ) :
    repRank lab (x + 1) = repRank lab x + if isRep lab x then 1 else 0 := by
  unfold repRank repList
  rw [List.range_succ, List.filter_append]
  cases h : isRep lab x <;> simp [h]

/-- Every position has a representative before it, with its label. -/
theorem exists_rep (lab : ℕ → ℕ) (x : ℕ) : ∃ r ≤ x, isRep lab r = true ∧ lab r = lab x := by
  classical
  have hex : ∃ r, lab r = lab x := ⟨x, rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex rfl, isRep_iff.mpr fun z hz hzr => ?_, Nat.find_spec hex⟩
  exact Nat.find_min hex hz (hzr.trans (Nat.find_spec hex))

/-- A representative comes no later than any position with its label. -/
theorem rep_le {lab : ℕ → ℕ} {r y : ℕ} (hr : isRep lab r = true) (hl : lab r = lab y) : r ≤ y := by
  by_contra h
  exact isRep_iff.mp hr y (by omega) hl.symm

/-- Two representatives with the same label are equal. -/
theorem rep_unique {lab : ℕ → ℕ} {r r' : ℕ} (hr : isRep lab r = true) (hr' : isRep lab r' = true)
    (hl : lab r = lab r') : r = r' :=
  le_antisymm (rep_le hr hl) (rep_le hr' hl.symm)

theorem mem_repList {lab : ℕ → ℕ} {n r : ℕ} : r ∈ repList lab n ↔ r < n ∧ isRep lab r = true := by
  simp [repList]

theorem repList_nodup (lab : ℕ → ℕ) (n : ℕ) : (repList lab n).Nodup :=
  (List.nodup_range).filter _

/-- The representative at index `c` has `c` representatives before it. -/
theorem repRank_getElem (lab : ℕ → ℕ) (n : ℕ) (c : ℕ) (hc : c < (repList lab n).length) :
    repRank lab ((repList lab n)[c]) = c := by
  induction n with
  | zero => simp [repList] at hc
  | succ n ih =>
    have hsplit : repList lab (n + 1) = repList lab n ++ (if isRep lab n then [n] else []) := by
      unfold repList
      rw [List.range_succ, List.filter_append]
      cases h : isRep lab n <;> simp [h]
    by_cases hlt : c < (repList lab n).length
    · have heq : (repList lab (n + 1))[c] = (repList lab n)[c] := by
        simp only [hsplit, List.getElem_append_left hlt]
      rw [heq]
      exact ih hlt
    · have hcn : c = (repList lab n).length := by
        rw [hsplit] at hc
        split_ifs at hc <;> simp at hc <;> omega
      have hrep : isRep lab n = true := by
        by_contra hne
        rw [hsplit] at hc
        simp [hne] at hc
        omega
      have heq : (repList lab (n + 1))[c] = n := by
        simp only [hsplit, hrep, ↓reduceIte, List.getElem_append_right (Nat.le_of_eq hcn.symm)]
        simp [hcn]
      rw [heq, hcn]
      rfl

/-! ## The list of the components -/

/-- The components of `G`, one for each representative, in the order of the representatives. -/
noncomputable def compList (G : MGraph) (vL : List ℕ) (lab : ℕ → ℕ) (n : ℕ) : List (Finset ℕ) :=
  (repList lab n).map fun r => compOf G (vL.getD r 0)

/-- The facts on the labels that the search gives: `n` vertices in the list `vL`, and equal labels
on the positions of connected vertices. -/
structure LabelFacts (G : MGraph) (vL : List ℕ) (lab : ℕ → ℕ) (n : ℕ) : Prop where
  hnd : vL.Nodup
  hlen : vL.length = n
  hmem : ∀ v, v ∈ vL ↔ v ∈ G.V
  hlab : ∀ x < n, ∀ y < n, lab x = lab y ↔ G.Connected (vL.getD x 0) (vL.getD y 0)

theorem LabelFacts.getD_mem {G : MGraph} {vL : List ℕ} {lab : ℕ → ℕ} {n : ℕ}
    (h : LabelFacts G vL lab n) {x : ℕ} (hx : x < n) : vL.getD x 0 ∈ G.V := by
  rw [List.getD_eq_getElem _ _ (by rw [h.hlen]; exact hx)]
  exact (h.hmem _).mp (List.getElem_mem _)

theorem LabelFacts.idxOf {G : MGraph} {vL : List ℕ} {lab : ℕ → ℕ} {n : ℕ}
    (h : LabelFacts G vL lab n) {v : ℕ} (hv : v ∈ G.V) :
    vL.idxOf v < n ∧ vL.getD (vL.idxOf v) 0 = v := by
  have hlt := List.idxOf_lt_length_of_mem ((h.hmem v).mpr hv)
  refine ⟨h.hlen ▸ hlt, ?_⟩
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]

theorem compList_length {G : MGraph} {vL : List ℕ} {lab : ℕ → ℕ} {n : ℕ} :
    (compList G vL lab n).length = repRank lab n := by
  simp [compList, repRank]

/-- **The list names each component once.** -/
theorem compList_nodup {G : MGraph} {vL : List ℕ} {lab : ℕ → ℕ} {n : ℕ}
    (h : LabelFacts G vL lab n) : (compList G vL lab n).Nodup := by
  refine (repList_nodup lab n).map_on fun r hr r' hr' heq => ?_
  obtain ⟨hrn, hrr⟩ := mem_repList.mp hr
  obtain ⟨hrn', hrr'⟩ := mem_repList.mp hr'
  have hcon : G.Connected (vL.getD r 0) (vL.getD r' 0) :=
    (compOf_eq_iff (h.getD_mem hrn')).mp heq
  exact rep_unique hrr hrr' ((h.hlab r hrn r' hrn').mpr hcon)

/-- **The list names the components of `G`.** -/
theorem mem_compList_iff {G : MGraph} {vL : List ℕ} {lab : ℕ → ℕ} {n : ℕ}
    (h : LabelFacts G vL lab n) (C : Finset ℕ) : C ∈ compList G vL lab n ↔ C ∈ components G := by
  constructor
  · intro hC
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hC
    exact compOf_mem_components (h.getD_mem (mem_repList.mp hr).1)
  · intro hC
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hx, hux⟩ := h.idxOf hu
    obtain ⟨r, hrx, hrr, hlr⟩ := exists_rep lab (vL.idxOf u)
    have hrn : r < n := by omega
    have hcon := (h.hlab r hrn _ hx).mp hlr
    rw [hux] at hcon
    refine List.mem_map.mpr ⟨r, mem_repList.mpr ⟨hrn, hrr⟩, ?_⟩
    exact compOf_eq_of_connected hcon

/-- **The vertex array.** If the array `cmp` holds `repRank r` at the vertex of each position `y`
whose representative is `r`, then it holds `c` at each vertex of the component with index `c`. -/
theorem compList_map {G : MGraph} {vL : List ℕ} {lab : ℕ → ℕ} {n : ℕ}
    (h : LabelFacts G vL lab n) {cmp : ℕ → ℕ}
    (hcmp : ∀ y < n, ∀ r ≤ y, isRep lab r = true → lab r = lab y → cmp (vL.getD y 0) = repRank lab r)
    (c : ℕ) (hc : c < (compList G vL lab n).length) (v : ℕ)
    (hv : v ∈ (compList G vL lab n)[c]) : cmp v = c := by
  have hc' : c < (repList lab n).length := by simpa [compList] using hc
  have hget : (compList G vL lab n)[c] = compOf G (vL.getD ((repList lab n)[c]) 0) := by
    simp [compList]
  rw [hget] at hv
  set r := (repList lab n)[c] with hr
  obtain ⟨hrn, hrr⟩ := mem_repList.mp (List.getElem_mem hc' : r ∈ repList lab n)
  obtain ⟨hvG, hcon⟩ := mem_compOf_iff.mp hv
  obtain ⟨hy, hvy⟩ := h.idxOf hvG
  have hlr : lab r = lab (vL.idxOf v) := (h.hlab r hrn _ hy).mpr (by rw [hvy]; exact hcon)
  have := hcmp _ hy r (rep_le hrr hlr) hrr hlr
  rw [hvy] at this
  rw [this, hr, repRank_getElem lab n c hc']

/-! ## The vertices of a component at the init -/

/-- **At the init, the graph of the LSF state of a component has only its vertices.** When the
current graph is the start graph (as at the init), the graphs of the LSF states of the components
of `G₀` cover the vertices of `G₀` without overlap (`CompLSFInv`), and the graph of each holds its
component. So it holds no other vertex. -/
theorem compSt_V_subset_init {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hGG : cs.G = cs.G₀) {C : Finset ℕ}
    (hC : C ∈ components cs.G₀) : (cs.compSt C).G.V ⊆ C := by
  have hsub : ∀ C' ∈ components cs.G₀, C' ⊆ (cs.compSt C').G.V := by
    intro C' hC'
    obtain ⟨hlsf, hG₀, -⟩ := hI.hCompLSF C' hC'
    have hV : (cs.compSt C').G₀.V = C' := by rw [hG₀]; rfl
    intro v hv
    rw [← hV] at hv
    rw [hlsf.hGV_eq, hlsf.hTV]
    exact Finset.mem_union_left _ hv
  intro v hv
  have hvG : v ∈ cs.G₀.V := by
    rw [← hGG, ← hI.hV_eq]
    exact Finset.mem_biUnion.mpr ⟨C, hC, hv⟩
  have hC' := compOf_mem_components hvG
  have hvC' : v ∈ compOf cs.G₀ v := self_mem_compOf hvG
  by_cases hEq : C = compOf cs.G₀ v
  · rw [hEq]; exact hvC'
  · exact absurd (hsub _ hC' hvC') (Finset.disjoint_left.mp (hI.hV_disj C hC _ hC' hEq) hv)

end MinCostFlow.SparseCore.Program
