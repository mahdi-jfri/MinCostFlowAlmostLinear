module

public import MinCostFlow.HierPaths.Ports
public import MinCostFlow.HierPaths.Project
import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.ExpanderDecomp.Injection
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The root host of the hierarchy

Port graph and padding (`lemma_2`): from an input graph `G` with `m ≥ 1` edges and conductance at
least `φ > 0`, build a connected loopless host graph on `P` terminals, where `P` is a power of two
with `2m ≤ P < 4m`, every degree is at most `11`, and the edge expansion by cardinality is at least
`min(φ, 1)/50`. Every terminal has an owner in `G`, every vertex of `G` owns at least its degree in
distinct terminals, and host walks project to walks of `G`.

The construction (`hostGraph`):
- Edge `j` of `G` gets the ports `2j` and `2j + 1`, joined by a host edge that carries the label
  `j`. A loop of `G` gets two distinct ports with the same owner, joined by an edge with the loop's
  number. Inside each cloud of ports with the same owner sits a copy of the cloud expander, with
  its loops deleted. This is `ExpanderDecomp.portGraph`; it has `2m` vertices and degree at most
  `10`.
- Let `P` be the least power of two with `2m ≤ P`. Each extra terminal `2m + i`, `i < P − 2m`, is
  joined by one edge to port `i`, and its owner is the owner of port `i`. Since `P − 2m ≤ 2m`,
  these ports are distinct, so degrees grow by at most one.

Cloud and padding edges join terminals of the same owner and carry no label, so a projection drops
them (`hostGraph_isProjection`). Expansion: `isExpansionExpanderOn_portGraph` gives
`min(φ, 1)/25` before padding and `isExpansionExpanderOn_pad` halves it.

Main results: `hostSize_isPow`, `le_hostSize`, `hostSize_lt`, `hostGraph_isValid`,
`hostGraph_isLoopless`, `hostGraph_deg_le`, `hostGraph_m_le`, `hostGraph_expansion`,
`hostGraph_cut_pos`, `hostOwner_lt`, `deg_le_card_owned`, `hostGraph_isProjection`,
`hostLabel_inj`, and `lemma_2`, which collects them for the explicit cloud expander.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The number `2m` of ports of `G`: two per edge of `G[V(G)]`. -/
def portCount (G : Graph) : ℕ :=
  2 * (G.inside G.verts).length

/-- The number `P` of terminals: the least power of two at least `2m`. -/
def hostSize (G : Graph) : ℕ :=
  2 ^ Nat.clog 2 (portCount G)

/-- The root host: the port graph of `G`, with each extra terminal `2m + i` joined to port `i`. -/
def hostGraph (cloud : ℕ → Graph) (G : Graph) : Graph :=
  ⟨hostSize G, (portGraph cloud G G.verts).edges ++
    attEdges (portCount G) (hostSize G - portCount G) id⟩

/-- The owner of terminal `p`: the owner of the port `p` when `p < 2m`, and the owner of the port
`p − 2m` that the extra terminal `p` is attached to otherwise. -/
def hostOwner (G : Graph) (p : ℕ) : ℕ :=
  if p < portCount G then portOwner G G.verts p else portOwner G G.verts (p - portCount G)

/-- The label of host edge `j`: the first `m` host edges stand for the edges of `G`, in order; the
cloud and padding edges carry no label. -/
def hostLabel (G : Graph) (j : ℕ) : Option ℕ :=
  if j < (G.inside G.verts).length then some j else none

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Expander

/-! ### The number of terminals -/

/-- `P` is a power of two. -/
theorem hostSize_isPow (G : Graph) : ∃ x, hostSize G = 2 ^ x :=
  ⟨_, rfl⟩

/-- `2m ≤ P`. -/
theorem le_hostSize (G : Graph) : portCount G ≤ hostSize G :=
  Nat.le_pow_clog (by norm_num) _

/-- `P < 4m` when `G` has an edge. -/
theorem hostSize_lt {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) :
    hostSize G < 2 * portCount G := by
  have hx : 1 < portCount G := by unfold portCount; omega
  have hpos := Nat.clog_pos (b := 2) (by norm_num) hx
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hx
  unfold hostSize
  have : 2 ^ Nat.clog 2 (portCount G) = 2 * 2 ^ (Nat.clog 2 (portCount G)).pred := by
    rw [← pow_succ']
    congr 1
    exact (Nat.succ_pred_eq_of_pos hpos).symm
  omega

/-- For a valid graph, `G[V(G)]` has all `m` edges. -/
theorem inside_verts_length {G : Graph} (hG : G.IsValid) : (G.inside G.verts).length = G.m := by
  rw [inside_verts_of_isValid hG]; rfl

/-! ### Validity, loops and degrees -/

private theorem mem_attEdges {n₀ q : ℕ} {e : ℕ × ℕ} (he : e ∈ attEdges n₀ q id) :
    ∃ i < q, e = (n₀ + i, i) := by
  simp only [attEdges, List.mem_map, List.mem_range, id] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i, hi, rfl⟩

private theorem pad_le {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) :
    hostSize G - portCount G ≤ portCount G := by
  have := hostSize_lt hm
  omega

/-- Every host edge joins two terminals. -/
theorem hostGraph_isValid {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) : (hostGraph cloud G).IsValid := by
  intro e he
  have hle := le_hostSize G
  have hpad := pad_le hm
  simp only [hostGraph, List.mem_append] at he ⊢
  rcases he with he | he
  · have h := portGraph_isValid hcloud G G.verts e he
    simp only [portGraph_n] at h
    exact ⟨by unfold portCount at hle; omega, by unfold portCount at hle; omega⟩
  · obtain ⟨i, hi, rfl⟩ := mem_attEdges he
    exact ⟨by omega, by omega⟩

/-- The host has no loops. -/
theorem hostGraph_isLoopless {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) : (hostGraph cloud G).IsLoopless := by
  intro e he
  have hpad := pad_le hm
  simp only [hostGraph, List.mem_append] at he
  rcases he with he | he
  · exact portGraph_isLoopless hcloud G G.verts e he
  · obtain ⟨i, hi, rfl⟩ := mem_attEdges he
    simp only
    omega

/-- The number of ends at `v` of the edges of a list. -/
private def endCount (E : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (E.filter fun e => e.1 = v).length + (E.filter fun e => e.2 = v).length

private theorem deg_eq_endCount {H : Graph} (hH : H.IsValid) (v : ℕ) :
    H.deg v = endCount H.edges v := by
  unfold Graph.deg Graph.degIn endCount
  rw [inside_verts_of_isValid hH]

private theorem endCount_append (E E' : List (ℕ × ℕ)) (v : ℕ) :
    endCount (E ++ E') v = endCount E v + endCount E' v := by
  unfold endCount
  simp only [List.filter_append, List.length_append]
  omega

/-- A list without repetitions has at most one entry with a property that at most one number
has. -/
private theorem length_filter_le_one {l : List ℕ} (hl : l.Nodup) {P : ℕ → Bool}
    (hP : ∀ i i', P i = true → P i' = true → i = i') : (l.filter P).length ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    rw [List.filter_cons]
    split_ifs with ha
    · have hnil : l.filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx hPx
        exact hnd.1 (hP x a hPx ha ▸ hx)
      simp [hnil]
    · exact ih hnd.2

/-- A vertex is an end of at most one padding edge. -/
private theorem endCount_attEdges_le {n₀ q : ℕ} (hq : q ≤ n₀) (v : ℕ) :
    endCount (attEdges n₀ q id) v ≤ 1 := by
  unfold endCount attEdges
  simp only [List.filter_map, List.length_map, id]
  by_cases hv : v < n₀
  · have h1 : (List.range q).filter ((fun e : ℕ × ℕ => decide (e.1 = v)) ∘ fun i => (n₀ + i, i))
        = [] := by
      rw [List.filter_eq_nil_iff]
      intro i _
      simp only [Function.comp_apply, decide_eq_true_eq]
      omega
    have h2 := length_filter_le_one (List.nodup_range (n := q))
      (P := (fun e : ℕ × ℕ => decide (e.2 = v)) ∘ fun i => (n₀ + i, i))
      (by intro i i' hi hi'; simp only [Function.comp_apply, decide_eq_true_eq] at hi hi'; omega)
    rw [h1]
    simpa using h2
  · have h2 : (List.range q).filter ((fun e : ℕ × ℕ => decide (e.2 = v)) ∘ fun i => (n₀ + i, i))
        = [] := by
      rw [List.filter_eq_nil_iff]
      intro i hi
      simp only [Function.comp_apply, decide_eq_true_eq]
      have := List.mem_range.mp hi
      omega
    have h1 := length_filter_le_one (List.nodup_range (n := q))
      (P := (fun e : ℕ × ℕ => decide (e.1 = v)) ∘ fun i => (n₀ + i, i))
      (by intro i i' hi hi'; simp only [Function.comp_apply, decide_eq_true_eq] at hi hi'; omega)
    rw [h2]
    simpa using h1

/-- **Degrees.** Every terminal has degree at most `11` in the host. -/
theorem hostGraph_deg_le {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) (v : ℕ) :
    (hostGraph cloud G).deg v ≤ 11 := by
  rw [deg_eq_endCount (hostGraph_isValid hcloud hm)]
  simp only [hostGraph]
  rw [endCount_append]
  have h1 := portGraph_deg_le hcloud G G.verts v
  rw [deg_eq_endCount (portGraph_isValid hcloud G G.verts)] at h1
  have h2 := endCount_attEdges_le (pad_le hm) v
  omega

/-- **Edges.** The host has at most `12 m` edges. -/
theorem hostGraph_m_le {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) :
    (hostGraph cloud G).m ≤ 12 * (G.inside G.verts).length := by
  have h1 := portGraph_m_le hcloud G G.verts
  have h2 := pad_le hm
  unfold Graph.m at h1 ⊢
  simp only [hostGraph, List.length_append, attEdges, List.length_map, List.length_range]
  unfold portCount at h2 ⊢
  omega

/-! ### Expansion and connectivity -/

/-- **Expansion.** If every cloud expander has expansion at least `1 / a₀` and `G` has conductance
at least `φ > 0`, the host has edge expansion at least `min(φ, 1) / (2 a₀ + 1) / 2`. -/
theorem hostGraph_expansion {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {a₀ : ℕ} (ha₀ : 1 ≤ a₀) (hα : (1 : ℝ) / a₀ ≤ α) {G : Graph}
    (hm : 1 ≤ (G.inside G.verts).length) {φ : ℝ} (hφ : 0 < φ)
    (hG : G.IsConductanceExpanderOn G.verts φ) :
    (hostGraph cloud G).IsExpansionExpanderOn (hostGraph cloud G).verts
      (min φ 1 / (2 * a₀ + 1) / 2) := by
  have hport := isExpansionExpanderOn_portGraph hcloud ha₀ hα hφ hG
  have hβ0 : 0 ≤ min φ 1 / (2 * a₀ + 1) := by
    apply div_nonneg (le_min hφ.le zero_le_one); positivity
  have hβ1 : min φ 1 / (2 * a₀ + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : min φ 1 ≤ 1 := min_le_right _ _
    have : (0 : ℝ) ≤ a₀ := Nat.cast_nonneg _
    linarith
  have hpad := isExpansionExpanderOn_pad (n₀ := portCount G) (q := hostSize G - portCount G)
    (att := id) hβ0 hβ1 hport (fun i hi => by have := pad_le hm; simp only [id]; omega)
    (fun i _ i' _ h => h)
  have hsum : portCount G + (hostSize G - portCount G) = hostSize G := by
    have := le_hostSize G; omega
  rw [hsum] at hpad
  exact hpad

/-- **Connectivity.** With `φ > 0`, every nontrivial cut of the host has an edge. -/
theorem hostGraph_cut_pos {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {a₀ : ℕ} (ha₀ : 1 ≤ a₀) (hα : (1 : ℝ) / a₀ ≤ α) {G : Graph}
    (hm : 1 ≤ (G.inside G.verts).length) {φ : ℝ} (hφ : 0 < φ)
    (hG : G.IsConductanceExpanderOn G.verts φ) {S : Finset ℕ}
    (hS : S ⊆ (hostGraph cloud G).verts) (hne : S.Nonempty) (hneX : S ≠ (hostGraph cloud G).verts) :
    1 ≤ (hostGraph cloud G).cutIn (hostGraph cloud G).verts S := by
  have h := hostGraph_expansion hcloud ha₀ hα hm hφ hG S hS hne hneX
  have hψ : 0 < min φ 1 / (2 * a₀ + 1) / 2 := by
    apply div_pos (div_pos (lt_min hφ zero_lt_one) (by positivity)) (by norm_num)
  have h1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hne.card_pos
  have h2 : (1 : ℝ) ≤ ((hostGraph cloud G).verts \ S).card := by
    have : ((hostGraph cloud G).verts \ S).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact hneX (Finset.Subset.antisymm hS hsub)
    exact_mod_cast this.card_pos
  have h3 : (1 : ℝ) ≤ min (S.card : ℝ) ((hostGraph cloud G).verts \ S).card := le_min h1 h2
  have h4 : (0 : ℝ) < (hostGraph cloud G).cutIn (hostGraph cloud G).verts S := by
    nlinarith
  have h5 : 0 < (hostGraph cloud G).cutIn (hostGraph cloud G).verts S := by exact_mod_cast h4
  omega

/-! ### Owners -/

/-- Every terminal has an owner in `G`. -/
theorem hostOwner_mem {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) {p : ℕ}
    (hp : p < hostSize G) : hostOwner G p ∈ G.verts := by
  have hpad := pad_le hm
  unfold hostOwner
  split_ifs with h
  · exact portOwner_mem h
  · exact portOwner_mem (by unfold portCount at h hpad ⊢; omega)

/-- Every terminal has an owner below `n`. -/
theorem hostOwner_lt {G : Graph} (hm : 1 ≤ (G.inside G.verts).length) {p : ℕ}
    (hp : p < hostSize G) : hostOwner G p < G.n :=
  Finset.mem_range.mp (hostOwner_mem hm hp)

/-- **Owned terminals.** Every vertex `v` of `G` owns at least `deg_G(v)` distinct terminals:
the ports of its cloud. -/
theorem deg_le_card_owned (G : Graph) (v : ℕ) :
    G.deg v ≤ ((Finset.range (hostSize G)).filter fun p => hostOwner G p = v).card := by
  have hsub : cloudOf G G.verts v ⊆ (Finset.range (hostSize G)).filter fun p => hostOwner G p = v := by
    intro p hp
    rw [mem_cloudOf_iff] at hp
    have hle := le_hostSize G
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by unfold portCount at hle; omega, ?_⟩
    unfold hostOwner
    rw [ite_eq_left (by unfold portCount; exact hp.1)]
    exact hp.2
  calc G.deg v = (cloudOf G G.verts v).card := (card_cloudOf G G.verts v).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### Projection -/

/-- Distinct host edges carry distinct labels. -/
theorem hostLabel_inj (G : Graph) (j j' e : ℕ) (h : hostLabel G j = some e)
    (h' : hostLabel G j' = some e) : j = j' := by
  unfold hostLabel at h h'
  split_ifs at h h'
  simp only [Option.some.injEq] at h h'
  omega

private theorem edgeAt_append_left {E E' : List (ℕ × ℕ)} {j : ℕ} (hj : j < E.length) :
    edgeAt (E ++ E') j = edgeAt E j := by
  unfold edgeAt
  exact List.getD_append _ _ _ _ hj

private theorem edgeAt_append_right {E E' : List (ℕ × ℕ)} {j : ℕ} (hj : E.length ≤ j) :
    edgeAt (E ++ E') j = edgeAt E' (j - E.length) := by
  unfold edgeAt
  exact List.getD_append_right _ _ _ _ hj

private theorem edgeAt_mem {E : List (ℕ × ℕ)} {j : ℕ} (hj : j < E.length) : edgeAt E j ∈ E := by
  unfold edgeAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

/-- **Projection.** For a valid `G` with an edge, the owners and labels project the host onto
`G`: the host edge with label `j` joins the two ports of edge `j`, whose owners are the ends of
edge `j`, and every other host edge joins two terminals with the same owner. -/
theorem hostGraph_isProjection {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} (hG : G.IsValid) (hm : 1 ≤ (G.inside G.verts).length) :
    IsProjection G (hostGraph cloud G).edges (hostOwner G) (hostLabel G) := by
  intro j hj
  have hvalid := hostGraph_isValid hcloud hm
  have hmem : edgeAt (hostGraph cloud G).edges j ∈ (hostGraph cloud G).edges := edgeAt_mem hj
  have hends := hvalid _ hmem
  have hsize : (hostGraph cloud G).n = hostSize G := rfl
  rw [hsize] at hends
  refine ⟨hostOwner_lt hm hends.1, hostOwner_lt hm hends.2, ?_, ?_⟩
  · -- an edge without label is a cloud or padding edge
    intro hl
    have hje : (G.inside G.verts).length ≤ j := by
      unfold hostLabel at hl; split_ifs at hl with h; omega
    have hpc := le_hostSize G
    have hpad := pad_le hm
    have hE : (hostGraph cloud G).edges = origPortEdges (G.inside G.verts).length ++
        (allCloudEdges cloud G G.verts ++
          attEdges (portCount G) (hostSize G - portCount G) id) := by
      simp [hostGraph, portGraph, List.append_assoc]
    have hlo : (origPortEdges (G.inside G.verts).length).length = (G.inside G.verts).length := by
      simp [origPortEdges]
    rw [hE] at hj ⊢
    rw [edgeAt_append_right (by rw [hlo]; exact hje)]
    rw [List.length_append, hlo] at hj
    have hmem' := edgeAt_mem (E := allCloudEdges cloud G G.verts ++
      attEdges (portCount G) (hostSize G - portCount G) id)
      (j := j - (origPortEdges (G.inside G.verts).length).length) (by rw [hlo]; omega)
    generalize edgeAt (allCloudEdges cloud G G.verts ++
      attEdges (portCount G) (hostSize G - portCount G) id)
      (j - (origPortEdges (G.inside G.verts).length).length) = ed at hmem' ⊢
    rcases List.mem_append.mp hmem' with hc | ha
    · obtain ⟨v, _, h1, h2, _⟩ := mem_allCloudEdges hcloud hc
      rw [mem_cloudOf_iff] at h1 h2
      have e1 : hostOwner G ed.1 = v := by
        unfold hostOwner; rw [ite_eq_left (by unfold portCount; exact h1.1)]; exact h1.2
      have e2 : hostOwner G ed.2 = v := by
        unfold hostOwner; rw [ite_eq_left (by unfold portCount; exact h2.1)]; exact h2.2
      rw [e1, e2]
    · obtain ⟨i, hi, rfl⟩ := mem_attEdges ha
      have e1 : hostOwner G (portCount G + i) = portOwner G G.verts i := by
        unfold hostOwner; rw [ite_eq_right (by omega)]; congr 1; omega
      have e2 : hostOwner G i = portOwner G G.verts i := by
        unfold hostOwner; rw [ite_eq_left (by omega)]
      simp only
      rw [e1, e2]
  · -- a labelled edge is the port edge of an edge of `G`
    intro e hl
    have hje : j < (G.inside G.verts).length := by
      unfold hostLabel at hl; split_ifs at hl with h; exact h
    have hej : e = j := by
      unfold hostLabel at hl; rw [ite_eq_left hje] at hl; exact (Option.some.inj hl).symm
    subst hej
    have hE : (hostGraph cloud G).edges = origPortEdges (G.inside G.verts).length ++
        (allCloudEdges cloud G G.verts ++
          attEdges (portCount G) (hostSize G - portCount G) id) := by
      simp [hostGraph, portGraph, List.append_assoc]
    have hlo : (origPortEdges (G.inside G.verts).length).length = (G.inside G.verts).length := by
      simp [origPortEdges]
    have hat : edgeAt (hostGraph cloud G).edges e = (2 * e, 2 * e + 1) := by
      rw [hE, edgeAt_append_left (by rw [hlo]; exact hje)]
      unfold edgeAt origPortEdges
      rw [List.getD_eq_getElem _ _ (by simp [hje])]
      simp
    refine ⟨by rw [← inside_verts_length hG]; exact hje, ?_⟩
    rw [hat]
    have h1 : hostOwner G (2 * e) = ((G.inside G.verts).getD e (0, 0)).1 := by
      unfold hostOwner portCount
      rw [ite_eq_left (by omega), portOwner_two_mul]
    have h2 : hostOwner G (2 * e + 1) = ((G.inside G.verts).getD e (0, 0)).2 := by
      unfold hostOwner portCount
      rw [ite_eq_left (by omega), portOwner_two_mul_succ]
    simp only
    rw [h1, h2, inside_verts_of_isValid hG]
    exact Or.inl ⟨rfl, rfl⟩

/-! ### The root host: port graph and padding (`lemma_2`) -/

/-- **`lemma_2` (port graph and padding).** Let `G` be a valid graph with `m ≥ 1`
edges and conductance at least `φ > 0`. With the explicit cloud expander, the host
`hostGraph explicitGraph G` has `P` vertices, where `P` is a power of two with `2m ≤ P < 4m`. It is
valid and loopless, every degree is at most `11`, its edge expansion is at least `min(φ, 1)/50`,
and every nontrivial cut has an edge. Every terminal has an owner in `G`, every vertex of `G` owns
at least its degree in distinct terminals, and the owners and labels project host walks to walks of
`G` (`projectWalk_isWalk`), with distinct labels on distinct host edges. -/
theorem lemma_2 {G : Graph} (hG : G.IsValid) (hm : 1 ≤ G.m) {φ : ℝ} (hφ : 0 < φ)
    (hcond : G.IsConductanceExpanderOn G.verts φ) :
    let H := hostGraph ExplicitExpander.explicitGraph G
    (H.n = hostSize G ∧ (∃ x, hostSize G = 2 ^ x) ∧ 2 * G.m ≤ hostSize G ∧
      hostSize G < 4 * G.m) ∧
    H.IsValid ∧ H.IsLoopless ∧ (∀ v, H.deg v ≤ 11) ∧ H.m ≤ 12 * G.m ∧
    H.IsExpansionExpanderOn H.verts (min φ 1 / 50) ∧
    (∀ S ⊆ H.verts, S.Nonempty → S ≠ H.verts → 1 ≤ H.cutIn H.verts S) ∧
    (∀ p < hostSize G, hostOwner G p < G.n) ∧
    (∀ v, G.deg v ≤ ((Finset.range (hostSize G)).filter fun p => hostOwner G p = v).card) ∧
    IsProjection G H.edges (hostOwner G) (hostLabel G) ∧
    (∀ j j' e, hostLabel G j = some e → hostLabel G j' = some e → j = j') := by
  have hcl := isCloudExpander_explicitGraph
  have hlen := inside_verts_length hG
  have hm' : 1 ≤ (G.inside G.verts).length := by rw [hlen]; exact hm
  have ha : (1 : ℝ) / (12 : ℕ) ≤ ExplicitExpander.alpha0 := by
    unfold ExplicitExpander.alpha0; norm_num
  have hexp := hostGraph_expansion hcl (a₀ := 12) (by norm_num) ha hm' hφ hcond
  have h50 : min φ 1 / (2 * ((12 : ℕ) : ℝ) + 1) / 2 = min φ 1 / 50 := by
    push_cast; ring
  rw [h50] at hexp
  refine ⟨⟨rfl, hostSize_isPow G, ?_, ?_⟩, hostGraph_isValid hcl hm', hostGraph_isLoopless hcl hm',
    hostGraph_deg_le hcl hm', ?_, hexp,
    fun S hS hne hneX => hostGraph_cut_pos hcl (a₀ := 12) (by norm_num) ha hm' hφ hcond hS hne hneX,
    fun p hp => hostOwner_lt hm' hp, deg_le_card_owned G, hostGraph_isProjection hcl hG hm',
    hostLabel_inj G⟩
  · have := le_hostSize G; unfold portCount at this; omega
  · have := hostSize_lt hm'; unfold portCount at this; omega
  · have := hostGraph_m_le hcl hm'; omega

end MinCostFlow.HierPaths
