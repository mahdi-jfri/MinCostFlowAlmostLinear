module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Structural properties of Task 1 (`buildWitness`)

This file proves the structural and indexing invariants of `wd := buildWitness tools H' J embJH`
from Task 1 of Algorithm 4 (`spanner.tex`, lines 74–81):
- `CompsAligned` invariants on `buildComps` (`wStart`, adjacency, `flatMap compWEdges`, `wSources`).
- `findJCompEdge` characterization.
- Disjointness of `wd.j0Edges` and `c.jSubOrigEdges` across components.
- `WitnessOK`, proving all `PathDSTool` and `ConstructExpanderTool` preconditions hold on every
  component subgraph `c.J_sub` and witness expander `c.W_sub`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Component list alignment & offset lemmas -/

/-- The `wStart` offsets of `cs : List CompInfo` are contiguous starting at `offset`. -/
def CompsAligned : ℕ → List CompInfo → Prop
  | _, [] => True
  | offset, c :: rest => c.wStart = offset ∧ CompsAligned (offset + c.W_sub.m) rest

theorem buildComps_length {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (J0_strip : Graph) (nlIdx : List ℕ)
    (decomp : DecomposeOutput) (φ_dec : ℝ) :
    ∀ offset raw, (buildComps tools J0_strip nlIdx decomp φ_dec offset raw).length = raw.length := by
  intro offset raw
  induction raw generalizing offset with
  | nil => simp [buildComps]
  | cons p rest ih => simp [buildComps, ih]

theorem buildComps_aligned {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (J0_strip : Graph) (nlIdx : List ℕ)
    (decomp : DecomposeOutput) (φ_dec : ℝ) :
    ∀ offset raw, CompsAligned offset (buildComps tools J0_strip nlIdx decomp φ_dec offset raw) := by
  intro offset raw
  induction raw generalizing offset with
  | nil => trivial
  | cons p rest ih => exact ⟨rfl, ih _⟩

theorem buildComps_getElem {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (J0_strip : Graph) (nlIdx : List ℕ)
    (decomp : DecomposeOutput) (φ_dec : ℝ) :
    ∀ offset raw (ci : ℕ) (hci : ci < raw.length),
      let cs := buildComps tools J0_strip nlIdx decomp φ_dec offset raw
      let c := cs[ci]'(by rw [buildComps_length]; exact hci)
      (c.level, c.X) = raw[ci]'hci := by
  intro offset raw
  induction raw generalizing offset with
  | nil => intro ci hci; simp at hci
  | cons p rest ih =>
    intro ci hci
    cases ci with
    | zero => simp [buildComps]
    | succ k => exact ih _ k (by simpa using hci)

theorem compsAligned_wStart_ge :
    ∀ {offset : ℕ} {cs : List CompInfo}, CompsAligned offset cs →
      ∀ c ∈ cs, offset ≤ c.wStart := by
  intro offset cs
  induction cs generalizing offset with
  | nil => simp
  | cons c0 rest ih =>
    rintro ⟨rfl, hrest⟩ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact le_rfl
    · exact le_trans (Nat.le_add_right _ _) (ih hrest c hc)

theorem compsAligned_sum_m (cs : List CompInfo) :
    (cs.map fun c => c.W_sub.m).sum = (cs.flatMap compWEdges).length := by
  induction cs with
  | nil => simp
  | cons c0 rest ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      compWEdges, List.length_map, ← ih]
    rfl

theorem compsAligned_adjacent :
    ∀ {offset : ℕ} {cs : List CompInfo}, CompsAligned offset cs →
      ∀ (ci₁ ci₂ : ℕ) (h1 : ci₁ < cs.length) (h2 : ci₂ < cs.length), ci₁ < ci₂ →
        (cs[ci₁]'h1).wStart + (cs[ci₁]'h1).W_sub.m ≤ (cs[ci₂]'h2).wStart := by
  intro offset cs
  induction cs generalizing offset with
  | nil => intro _ ci₁ _ h1; simp at h1
  | cons c0 rest ih =>
    rintro ⟨rfl, hrest⟩ ci₁ ci₂ h1 h2 hlt
    cases ci₂ with
    | zero => omega
    | succ k₂ =>
      cases ci₁ with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        exact compsAligned_wStart_ge hrest _ (List.getElem_mem _)
      | succ k₁ =>
        simp only [List.getElem_cons_succ]
        exact ih hrest k₁ k₂ (Nat.succ_lt_succ_iff.mp h1) (Nat.succ_lt_succ_iff.mp h2)
          (Nat.succ_lt_succ_iff.mp hlt)

theorem compsAligned_wEnd_le :
    ∀ {offset : ℕ} {cs : List CompInfo}, CompsAligned offset cs →
      ∀ (ci : ℕ) (hci : ci < cs.length),
        (cs[ci]'hci).wStart + (cs[ci]'hci).W_sub.m ≤ offset + (cs.map fun c => c.W_sub.m).sum := by
  intro offset cs
  induction cs generalizing offset with
  | nil => intro _ ci hci; simp at hci
  | cons c0 rest ih =>
    rintro ⟨rfl, hrest⟩ ci hci
    cases ci with
    | zero =>
      simp only [List.getElem_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ k =>
      simp only [List.getElem_cons_succ, List.map_cons, List.sum_cons]
      have := ih hrest k (Nat.succ_lt_succ_iff.mp hci)
      omega

theorem compsAligned_flatMap_getElem :
    ∀ {offset : ℕ} {cs : List CompInfo}, CompsAligned offset cs →
      ∀ (ci : ℕ) (hci : ci < cs.length) (eL : ℕ) (heL : eL < (cs[ci]'hci).W_sub.m),
        let c := cs[ci]'hci
        ∃ hidx : (c.wStart - offset) + eL < (cs.flatMap compWEdges).length,
          (cs.flatMap compWEdges)[(c.wStart - offset) + eL]'hidx =
            (c.verts.getD (c.W_sub.edges[eL]'heL).1 0,
             c.verts.getD (c.W_sub.edges[eL]'heL).2 0) := by
  intro offset cs
  induction cs generalizing offset with
  | nil => intro _ ci hci; simp at hci
  | cons c0 rest ih =>
    rintro ⟨rfl, hrest⟩ ci hci eL heL
    cases ci with
    | zero =>
      simp only [List.getElem_cons_zero, List.flatMap_cons, Nat.sub_self, zero_add]
      have heL0 : eL < (compWEdges c0).length := by
        simpa [compWEdges, Graph.m] using heL
      refine ⟨Nat.lt_of_lt_of_le heL0 (by rw [List.length_append]; exact Nat.le_add_right _ _), ?_⟩
      rw [List.getElem_append_left heL0]
      simp [compWEdges]
    | succ k =>
      have hk : k < rest.length := Nat.succ_lt_succ_iff.mp hci
      obtain ⟨hidx, heq⟩ := ih hrest k hk eL heL
      simp only [List.flatMap_cons, List.getElem_cons_succ] at hidx heq ⊢
      have hge : c0.wStart + c0.W_sub.m ≤ (rest[k]'hk).wStart :=
        compsAligned_wStart_ge hrest _ (List.getElem_mem hk)
      have hlen0 : (compWEdges c0).length = c0.W_sub.m := by simp [compWEdges, Graph.m]
      have hsub_eq : (rest[k]'hk).wStart - c0.wStart + eL =
          (compWEdges c0).length + (((rest[k]'hk).wStart - (c0.wStart + c0.W_sub.m)) + eL) := by
        rw [hlen0]; omega
      refine ⟨by rw [List.length_append, hsub_eq]; exact Nat.add_lt_add_left hidx _, ?_⟩
      rw [List.getElem_append_right (by rw [hsub_eq]; exact Nat.le_add_right _ _)]
      calc (rest.flatMap compWEdges)[(rest[k]'hk).wStart - c0.wStart + eL - (compWEdges c0).length]'_
          = (rest.flatMap compWEdges)[(rest[k]'hk).wStart - (c0.wStart + c0.W_sub.m) + eL]'hidx := by
              congr 1; omega
        _ = _ := heq

theorem compsAligned_flatMap_wSources :
    ∀ {offset base : ℕ} {cs : List CompInfo}, CompsAligned offset cs →
      ∀ (ci : ℕ) (hci : ci < cs.length) (eL : ℕ) (_heL : eL < (cs[ci]'hci).W_sub.m),
        let c := cs[ci]'hci
        let src := (cs.zipIdx base).flatMap fun (c', ci') =>
          (List.range c'.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci' eLocal
        ∃ hidx : (c.wStart - offset) + eL < src.length,
          src[(c.wStart - offset) + eL]'hidx = WEdgeSource.fromComp (base + ci) eL := by
  intro offset base cs
  induction cs generalizing offset base with
  | nil => intro _ ci hci; simp at hci
  | cons c0 rest ih =>
    rintro ⟨rfl, hrest⟩ ci hci eL heL
    cases ci with
    | zero =>
      simp only [List.zipIdx_cons, List.flatMap_cons, List.getElem_cons_zero, Nat.sub_self,
        zero_add, Nat.add_zero]
      have heL' : eL < ((List.range c0.W_sub.m).map fun eLocal => WEdgeSource.fromComp base eLocal).length := by
        simpa using heL
      refine ⟨Nat.lt_of_lt_of_le heL' (by rw [List.length_append]; exact Nat.le_add_right _ _), ?_⟩
      rw [List.getElem_append_left heL']
      simp
    | succ k =>
      have hk : k < rest.length := Nat.succ_lt_succ_iff.mp hci
      obtain ⟨hidx, heq⟩ := ih hrest k hk eL heL (base := base + 1)
      simp only [List.zipIdx_cons, List.flatMap_cons, List.getElem_cons_succ] at hidx heq ⊢
      have hge : c0.wStart + c0.W_sub.m ≤ (rest[k]'hk).wStart :=
        compsAligned_wStart_ge hrest _ (List.getElem_mem hk)
      have hlen0 : ((List.range c0.W_sub.m).map fun eLocal => WEdgeSource.fromComp base eLocal).length =
          c0.W_sub.m := by simp
      have hsub_eq : (rest[k]'hk).wStart - c0.wStart + eL =
          ((List.range c0.W_sub.m).map fun eLocal => WEdgeSource.fromComp base eLocal).length +
            (((rest[k]'hk).wStart - (c0.wStart + c0.W_sub.m)) + eL) := by
        rw [hlen0]; omega
      refine ⟨by rw [List.length_append, hsub_eq]; exact Nat.add_lt_add_left hidx _, ?_⟩
      simp_rw [hsub_eq]
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simpa [Nat.add_sub_cancel_left, Nat.add_assoc, Nat.add_comm 1 k] using heq

theorem compsAligned_find_wStart :
    ∀ {offset : ℕ} {cs : List CompInfo}, CompsAligned offset cs →
      ∀ eW, offset ≤ eW → eW < offset + (cs.map fun c => c.W_sub.m).sum →
        ∃ (ci : ℕ) (hci : ci < cs.length),
          (cs[ci]'hci).wStart ≤ eW ∧ eW < (cs[ci]'hci).wStart + (cs[ci]'hci).W_sub.m := by
  intro offset cs
  induction cs generalizing offset with
  | nil => intro _ eW hge hlt; simp at hlt; omega
  | cons c0 rest ih =>
    rintro ⟨rfl, hrest⟩ eW hge hlt
    simp only [List.map_cons, List.sum_cons] at hlt
    by_cases hlt0 : eW < c0.wStart + c0.W_sub.m
    · exact ⟨0, by simp, hge, hlt0⟩
    · obtain ⟨ci, hci, h1, h2⟩ := ih hrest eW (Nat.le_of_not_lt hlt0) (by omega)
      exact ⟨ci + 1, Nat.succ_lt_succ hci, h1, h2⟩

theorem find?_comp_unique {offset : ℕ} {cs : List CompInfo} (ha : CompsAligned offset cs)
    {ci : ℕ} (hci : ci < cs.length) {eW : ℕ}
    (h1 : (cs[ci]'hci).wStart ≤ eW) (h2 : eW < (cs[ci]'hci).wStart + (cs[ci]'hci).W_sub.m) :
    cs.find? (fun c => decide (c.wStart ≤ eW ∧ eW < c.wStart + c.W_sub.m)) = some (cs[ci]'hci) := by
  induction cs generalizing offset ci with
  | nil => simp at hci
  | cons c0 rest ih =>
    rcases ha with ⟨rfl, hrest⟩
    cases ci with
    | zero =>
      dsimp only [List.getElem_cons_zero] at h1 h2
      simp [h1, h2]
    | succ k =>
      have hk : k < rest.length := Nat.succ_lt_succ_iff.mp hci
      have hge : c0.wStart + c0.W_sub.m ≤ (rest[k]'hk).wStart :=
        compsAligned_wStart_ge hrest _ (List.getElem_mem hk)
      dsimp only [List.getElem_cons_succ] at h1
      have hnot : ¬ (c0.wStart ≤ eW ∧ eW < c0.wStart + c0.W_sub.m) := by omega
      simp only [List.find?_cons, List.getElem_cons_succ, hnot, decide_false]
      exact ih hrest hk h1 h2

/-! ## `findJCompEdge` characterization -/

theorem findJCompEdge_spec (jOrig : ℕ) :
    ∀ (cs : List CompInfo) (base : ℕ),
      match findJCompEdge jOrig cs base with
      | some (ci, b) =>
        ∃ (hci : ci - base < cs.length) (hb : b < (cs[ci - base]'hci).jSubOrigEdges.length),
          base ≤ ci ∧ (cs[ci - base]'hci).jSubOrigEdges[b]'hb = jOrig
      | none => ∀ c ∈ cs, jOrig ∉ c.jSubOrigEdges := by
  intro cs
  induction cs with
  | nil => intro base; simp [findJCompEdge]
  | cons c0 rest ih =>
    intro base
    unfold findJCompEdge
    split_ifs with hmem
    · refine ⟨by simp, ?_, le_rfl, ?_⟩
      · simpa using List.idxOf_lt_length_iff.mpr hmem
      · simp [List.getElem_idxOf]
    · have ih' := ih (base + 1)
      cases hres : findJCompEdge jOrig rest (base + 1) with
      | none =>
        rw [hres] at ih'
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hmem
        · exact ih' c hc
      | some p =>
        rw [hres] at ih'
        rcases ih' with ⟨hci, hb, hge, heq⟩
        have hsub : p.1 - base = (p.1 - (base + 1)) + 1 := by omega
        refine ⟨by simp; omega, ?_, by omega, ?_⟩
        · simpa [hsub] using hb
        · simp_rw [hsub, List.getElem_cons_succ]
          exact heq

theorem findJCompEdge_eq_some_of_mem {jOrig : ℕ} :
    ∀ (cs : List CompInfo) (base : ℕ),
      (∀ ci₁ ci₂ (h1 : ci₁ < cs.length) (h2 : ci₂ < cs.length),
        ci₁ ≠ ci₂ → Disjoint (cs[ci₁]'h1).jSubOrigEdges.toFinset (cs[ci₂]'h2).jSubOrigEdges.toFinset) →
      ∀ (ci : ℕ) (hci : ci < cs.length),
        jOrig ∈ (cs[ci]'hci).jSubOrigEdges →
        findJCompEdge jOrig cs base = some (base + ci, (cs[ci]'hci).jSubOrigEdges.idxOf jOrig) := by
  intro cs
  induction cs with
  | nil => intro _ _ ci hci; simp at hci
  | cons c0 rest ih =>
    intro base hdisj ci hci hmem
    cases ci with
    | zero =>
      simp only [List.getElem_cons_zero] at hmem
      simp [findJCompEdge, hmem]
    | succ k =>
      have hk : k < rest.length := Nat.succ_lt_succ_iff.mp hci
      have hdisj0 : Disjoint c0.jSubOrigEdges.toFinset (rest[k]'hk).jSubOrigEdges.toFinset :=
        hdisj 0 (k + 1) (by simp) hci (Nat.zero_ne_add_one k)
      have hnot : jOrig ∉ c0.jSubOrigEdges := by
        intro hc0
        exact Finset.disjoint_left.mp hdisj0 (List.mem_toFinset.mpr hc0)
          (List.mem_toFinset.mpr (by simpa using hmem))
      have hdisj' : ∀ i₁ i₂ (h1 : i₁ < rest.length) (h2 : i₂ < rest.length), i₁ ≠ i₂ →
          Disjoint (rest[i₁]'h1).jSubOrigEdges.toFinset (rest[i₂]'h2).jSubOrigEdges.toFinset :=
        fun i₁ i₂ h1 h2 hne =>
          hdisj (i₁ + 1) (i₂ + 1) (Nat.succ_lt_succ h1) (Nat.succ_lt_succ h2)
            (fun h => hne (Nat.succ.inj h))
      have ih' := ih (base + 1) hdisj' k hk (by simpa using hmem)
      simp only [findJCompEdge, hnot, ↓reduceIte]
      rw [ih']
      simp [Nat.add_assoc, Nat.add_comm 1 k]

end MinCostFlow.Spanner
