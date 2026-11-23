module

public import MinCostFlow.ExpanderDecomp.PortGraph
public import MinCostFlow.ExpanderDecomp.Embedding
import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.ExpanderDecomp.Injection
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Port-cut rounding and cloud contraction

This file proves the two main lemmas connecting a port graph `portGraph cloud G X` back to the
original induced graph `G[X]`.

* **Port-cut rounding** (`lemma_8`, `lemma_8_real`): given a sparse port cut `U` of `portGraph cloud G X`
  with `|∂ U| ≤ (1 / b) · min(|U|, |Ū|)` and `b ≥ 2 a₀` (where each cloud expander has expansion
  at least `1 / a₀`), rounding each cloud to its majority side (`roundPortCut G X U`) moves at most
  `u_move ≤ a₀ · |∂ U| ≤ (1 / 2) · min(|U|, |Ū|)` ports, keeps at least half of each side's
  cardinality as original volume, and produces an original cut `S ⊆ X` satisfying
  `|∂_{G[X]} S| ≤ (2(a₀ + 1) / b) · min(vol_{G[X]}(S), vol_{G[X]}(X \ S))`.
* **Contraction and its volume bound** (`cutIn_contractedGraph_eq`, `volIn_contractedGraph_le`,
  `isConductanceExpanderOn_contractedGraph_of_embedding`): adding fake port edges `F` of maximum
  degree at most `t` to `portGraph cloud G X`, contracting each cloud to its original vertex, and
  deleting all loops yields `contractedGraph G X F = G + F'` such that:
  - for every `S ⊆ X`, the canonical port cut `liftSet G X S` in `portGraph + F` has the same
    boundary as `S` in `G + F'`;
  - `vol_{G+F'}(S) ≤ (t + 1) · vol_G(S)` inside `X`;
  - any spanning port witness of expansion `β` embedded into `portGraph + F` with congestion `η`
    certifies conductance at least `β / (η · (t + 1))` for `(G + F')[X]`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Round a port cut `U` to an original vertex set `S ⊆ X` by assigning each vertex `v ∈ X` to `S`
when at least half of its cloud lies in `U`. -/
def roundPortCut (G : Graph) (X U : Finset ℕ) : Finset ℕ :=
  X.filter fun v => (cloudOf G X v \ U).card ≤ (U ∩ cloudOf G X v).card

/-- The set of ports that switch side when rounding `U` to `liftSet G X (roundPortCut G X U)`. -/
def movedPorts (G : Graph) (X U : Finset ℕ) : Finset ℕ :=
  (U \ liftSet G X (roundPortCut G X U)) ∪ (liftSet G X (roundPortCut G X U) \ U)

/-- Contract a list of port edges along `portOwner G X` and delete all resulting loops. -/
def contractEdges (G : Graph) (X : Finset ℕ) (F : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (F.map fun e => (portOwner G X e.1, portOwner G X e.2)).filter fun e => decide (e.1 ≠ e.2)

/-- The graph `G` augmented with the contracted, loop-deleted fake edges `contractEdges G X F`. -/
def contractedGraph (G : Graph) (X : Finset ℕ) (F : List (ℕ × ℕ)) : Graph :=
  ⟨G.n, G.edges ++ contractEdges G X F⟩

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Helper arithmetic and list lemmas -/

private theorem sum_range_two_mul' (e : ℕ) (f : ℕ → ℕ) :
    ∑ p ∈ Finset.range (2 * e), f p =
      ∑ i ∈ Finset.range e, (f (2 * i) + f (2 * i + 1)) := by
  induction e with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

private theorem sum_range_getD_eq_sum_map' {α : Type*} (l : List α) (d : α) (f : α → ℕ) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [ih]
    omega

private theorem cutIn_flatMap {n : ℕ} {α : Type*} (l : List α) (f : α → List (ℕ × ℕ))
    (X S : Finset ℕ) :
    (Graph.mk n (l.flatMap f)).cutIn X S =
      (l.map fun x => (Graph.mk n (f x)).cutIn X S).sum := by
  induction l with
  | nil => simp [Graph.cutIn, Graph.inside]
  | cons a t ih =>
    rw [List.flatMap_cons, cutIn_append, List.map_cons, List.sum_cons, ih]

private theorem sum_sort_eq_finset_sum (X : Finset ℕ) (f : ℕ → ℕ) :
    ((X.sort (· ≤ ·)).map f).sum = ∑ v ∈ X, f v := by
  rw [← List.sum_toFinset _ (Finset.sort_nodup X (· ≤ ·))]
  have htoF : (X.sort (· ≤ ·)).toFinset = X := by
    ext v
    simp
  rw [htoF]

/-! ### Rounding a sparse port cut -/

/-- The rounded vertex set lies inside `X`. -/
theorem roundPortCut_subset (G : Graph) (X U : Finset ℕ) :
    roundPortCut G X U ⊆ X :=
  Finset.filter_subset _ _

/-- Inside each cloud `C_v`, the ports moved by rounding number `min |U ∩ C_v| |C_v \ U|`. -/
private theorem card_movedPorts_inter_cloudOf (G : Graph) (X U : Finset ℕ) {v : ℕ} (hv : v ∈ X) :
    (movedPorts G X U ∩ cloudOf G X v).card =
      min (U ∩ cloudOf G X v).card (cloudOf G X v \ U).card := by
  set S := roundPortCut G X U
  set C := cloudOf G X v
  by_cases hvS : v ∈ S
  · have hsub : C ⊆ liftSet G X S := by
      intro p hp
      rw [mem_cloudOf_iff] at hp
      simp [liftSet, hp.1, hp.2, hvS]
    have heq : movedPorts G X U ∩ C = C \ U := by
      ext p
      simp only [movedPorts, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨_, hnot⟩ | ⟨_, hnotU⟩, hpC⟩
        · exact absurd (hsub hpC) hnot
        · exact ⟨hpC, hnotU⟩
      · rintro ⟨hpC, hnotU⟩
        exact ⟨Or.inr ⟨hsub hpC, hnotU⟩, hpC⟩
    rw [heq]
    have hmaj : (C \ U).card ≤ (U ∩ C).card := by
      simpa [S, C, roundPortCut] using (Finset.mem_filter.mp hvS).2
    exact (min_eq_right hmaj).symm
  · have hdisj : Disjoint C (liftSet G X S) := by
      rw [Finset.disjoint_left]
      intro p hpC hpL
      rw [mem_cloudOf_iff] at hpC
      simp only [liftSet, Finset.mem_filter] at hpL
      exact hvS (hpC.2 ▸ hpL.2)
    have heq : movedPorts G X U ∩ C = U ∩ C := by
      ext p
      simp only [movedPorts, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hpU, _⟩ | ⟨hpL, _⟩, hpC⟩
        · exact ⟨hpU, hpC⟩
        · exact absurd hpL (Finset.disjoint_left.mp hdisj hpC)
      · rintro ⟨hpU, hpC⟩
        exact ⟨Or.inl ⟨hpU, Finset.disjoint_left.mp hdisj hpC⟩, hpC⟩
    rw [heq]
    have hmin : (U ∩ C).card ≤ (C \ U).card := by
      have hnot : ¬ (C \ U).card ≤ (U ∩ C).card := fun h =>
        hvS (Finset.mem_filter.mpr ⟨hv, h⟩)
      omega
    exact (min_eq_left hmin).symm

/-- For `U ⊆ Finset.range (2e)`, the total number of moved ports is the sum over all clouds of
`min |U ∩ C_v| |C_v \ U|`. -/
theorem card_movedPorts_eq_sum_min {G : Graph} {X U : Finset ℕ}
    (hU : U ⊆ Finset.range (2 * (G.inside X).length)) :
    (movedPorts G X U).card =
      ∑ v ∈ X, min (U ∩ cloudOf G X v).card (cloudOf G X v \ U).card := by
  have hsub : movedPorts G X U ⊆ Finset.range (2 * (G.inside X).length) := by
    intro p hp
    simp only [movedPorts, Finset.mem_union, Finset.mem_sdiff] at hp
    rcases hp with ⟨hpU, _⟩ | ⟨hpL, _⟩
    · exact hU hpU
    · exact (Finset.mem_filter.mp hpL).1
  have hpart : movedPorts G X U = X.biUnion fun v => movedPorts G X U ∩ cloudOf G X v := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hp
      have hp_lt : p < 2 * (G.inside X).length := Finset.mem_range.mp (hsub hp)
      exact ⟨portOwner G X p, portOwner_mem hp_lt, hp, mem_cloudOf_iff.mpr ⟨hp_lt, rfl⟩⟩
    · rintro ⟨_, _, hp, _⟩
      exact hp
  rw [hpart, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun v hv => card_movedPorts_inter_cloudOf G X U hv
  · intro u _ v _ huv
    exact (cloudOf_disjoint G X huv).mono Finset.inter_subset_right Finset.inter_subset_right

/-- Inside cloud `v`, the cloud expander cut of `U` is at least `α · min(|U ∩ C_v|, |C_v \ U|)`. -/
private theorem alpha_mul_min_le_cutIn_cloudEdgesFor {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) (G : Graph) (X U : Finset ℕ) (v : ℕ) :
    α * (min (U ∩ cloudOf G X v).card (cloudOf G X v \ U).card : ℝ) ≤
      ((Graph.mk (2 * (G.inside X).length) (cloudEdgesFor cloud G X v)).cutIn
        (Finset.range (2 * (G.inside X).length)) U : ℝ) := by
  set pts := cloudPortsList G X v
  set C := cloudOf G X v
  have hlen : pts.length = C.card := cloudPortsList_length G X v
  by_cases hs : 2 ≤ pts.length
  · set s := pts.length
    set A := (Finset.range s).filter fun i => pts.getD i 0 ∈ U
    have hnd : pts.Nodup := cloudPortsList_nodup G X v
    have hA_card : A.card = (U ∩ C).card := by
      apply Finset.card_bij (fun i _ => pts.getD i 0)
      · intro i hi
        simp only [A, Finset.mem_filter, Finset.mem_range] at hi
        refine Finset.mem_inter.mpr ⟨hi.2, ?_⟩
        change pts.getD i 0 ∈ cloudOf G X v
        rw [← cloudPortsList_toFinset, List.mem_toFinset, List.getD_eq_getElem _ _ hi.1]
        exact List.getElem_mem hi.1
      · intro i hi j hj hij
        simp only [A, Finset.mem_filter, Finset.mem_range] at hi hj
        rw [List.getD_eq_getElem _ _ hi.1, List.getD_eq_getElem _ _ hj.1] at hij
        exact (List.Nodup.getElem_inj_iff hnd).mp hij
      · intro p hp
        rw [Finset.mem_inter] at hp
        have hp_pts : p ∈ pts := by
          rw [← List.mem_toFinset, cloudPortsList_toFinset]
          exact hp.2
        obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp_pts
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hpi]; exact hp.1
        · rw [List.getD_eq_getElem _ _ hi, hpi]
    have hAsdiff_card : (Finset.range s \ A).card = (C \ U).card := by
      have h1 : (Finset.range s \ A).card + A.card = s := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _), Finset.card_range]
      have h2 : (U ∩ C).card + (C \ U).card = C.card := by
        rw [Finset.inter_comm, Finset.card_inter_add_card_sdiff]
      omega
    by_cases hAne : A.Nonempty
    · by_cases hAall : A = Finset.range s
      · have hzero : (C \ U).card = 0 := by
          rw [← hAsdiff_card, hAall, Finset.sdiff_self, Finset.card_empty]
        simp [hzero]
      · have hverts : (cloud s).verts = Finset.range s := by
          unfold Graph.verts
          rw [hcloud.n_eq s hs]
        have hexp := hcloud.expansion s hs A (by rw [hverts]; exact Finset.filter_subset _ _)
          hAne (by rw [hverts]; exact hAall)
        rw [hverts, hA_card, hAsdiff_card] at hexp
        have hcut_eq : (cloud s).cutIn (Finset.range s) A =
            (Graph.mk (2 * (G.inside X).length) (cloudEdgesFor cloud G X v)).cutIn
              (Finset.range (2 * (G.inside X).length)) U := by
          have hv_c := hcloud.isValid s hs
          have hins_c : (cloud s).inside (Finset.range s) = (cloud s).edges := by
            rw [← hverts, inside_verts_of_isValid hv_c]
          have hv_e : (Graph.mk (2 * (G.inside X).length) (cloudEdgesFor cloud G X v)).IsValid := by
            intro ed hed
            have hm := mem_cloudEdgesFor hcloud hed
            exact ⟨(mem_cloudOf_iff.mp hm.1).1, (mem_cloudOf_iff.mp hm.2.1).1⟩
          have hins_e : (Graph.mk (2 * (G.inside X).length) (cloudEdgesFor cloud G X v)).inside
              (Finset.range (2 * (G.inside X).length)) = cloudEdgesFor cloud G X v :=
            inside_verts_of_isValid hv_e
          rw [cutIn_eq_sum_map, cutIn_eq_sum_map, hins_c, hins_e]
          unfold cloudEdgesFor
          dsimp only
          rw [ite_eq_left_iff.mpr (fun h => absurd hs h)]
          rw [List.map_map]
          have hgen : ∀ l : List (ℕ × ℕ),
              (∀ e ∈ l, e.1 < s ∧ e.2 < s) →
              (l.map fun e => if (decide (e.1 ∈ A) != decide (e.2 ∈ A)) then 1 else 0).sum =
              ((l.filter fun e => decide (e.1 ≠ e.2)).map
                ((fun e : ℕ × ℕ => if (decide (e.1 ∈ U) != decide (e.2 ∈ U)) then 1 else 0) ∘
                  fun e => (pts.getD e.1 0, pts.getD e.2 0))).sum := by
            intro l hl
            induction l with
            | nil => simp
            | cons a t ih =>
              have ha := hl a List.mem_cons_self
              have ht := ih fun e he => hl e (List.mem_cons_of_mem _ he)
              rw [List.filter_cons]
              by_cases hne : a.1 ≠ a.2
              · simp only [decide_eq_true hne, ↓reduceIte, List.map_cons, List.sum_cons,
                  Function.comp_apply, ht]
                have h1 : a.1 ∈ A ↔ pts.getD a.1 0 ∈ U := by
                  simp [A, ha.1]
                have h2 : a.2 ∈ A ↔ pts.getD a.2 0 ∈ U := by
                  simp [A, ha.2]
                simp [h1, h2]
              · have heq : a.1 = a.2 := Classical.not_not.mp hne
                rw [decide_eq_false hne]
                simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, heq,
                  bne_self_eq_false, zero_add, ht]
          exact hgen (cloud s).edges fun e he => by
            have h := hv_c e he
            rw [hcloud.n_eq s hs] at h
            exact h
        rw [← hcut_eq]
        exact hexp
    · have hzero : (U ∩ C).card = 0 := by
        rw [← hA_card, Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.card_empty]
      rw [← Nat.cast_min, hzero, Nat.zero_min, Nat.cast_zero, mul_zero]
      exact Nat.cast_nonneg _
  · have hcard : C.card ≤ 1 := by omega
    have hsum : (U ∩ C).card + (C \ U).card = C.card := by
      rw [Finset.inter_comm, Finset.card_inter_add_card_sdiff]
    have hzero : min (U ∩ C).card (C \ U).card = 0 := by omega
    rw [← Nat.cast_min, hzero, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _

/-- Cloud expansion bounds the number of moved ports by the cloud-edge cut:
`α · |movedPorts| ≤ cut_{cloud}(U) ≤ cut_{portGraph}(U)`. -/
theorem alpha_mul_movedPorts_le_cut {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) {G : Graph} {X U : Finset ℕ}
    (hU : U ⊆ (portGraph cloud G X).verts) :
    α * ((movedPorts G X U).card : ℝ) ≤
      ((portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℝ) := by
  have hU' : U ⊆ Finset.range (2 * (G.inside X).length) := hU
  rw [card_movedPorts_eq_sum_min hU']
  push_cast
  rw [Finset.mul_sum]
  have hsum_le : ∑ v ∈ X, α * (min (U ∩ cloudOf G X v).card (cloudOf G X v \ U).card : ℝ) ≤
      ∑ v ∈ X, ((Graph.mk (2 * (G.inside X).length) (cloudEdgesFor cloud G X v)).cutIn
        (Finset.range (2 * (G.inside X).length)) U : ℝ) :=
    Finset.sum_le_sum fun v _ => alpha_mul_min_le_cutIn_cloudEdgesFor hcloud G X U v
  have hcloud_cut : ∑ v ∈ X, (Graph.mk (2 * (G.inside X).length) (cloudEdgesFor cloud G X v)).cutIn
        (Finset.range (2 * (G.inside X).length)) U =
      (Graph.mk (2 * (G.inside X).length) (allCloudEdges cloud G X)).cutIn
        (Finset.range (2 * (G.inside X).length)) U := by
    unfold allCloudEdges
    rw [cutIn_flatMap, sum_sort_eq_finset_sum]
  have hle_port : (Graph.mk (2 * (G.inside X).length) (allCloudEdges cloud G X)).cutIn
        (Finset.range (2 * (G.inside X).length)) U ≤
      (portGraph cloud G X).cutIn (portGraph cloud G X).verts U := by
    unfold portGraph Graph.verts
    dsimp only
    exact cutIn_le_cutIn_append_left _ _ _ _ _
  have hcloud_cut_r : (∑ v ∈ X, ((Graph.mk (2 * (G.inside X).length)
        (cloudEdgesFor cloud G X v)).cutIn (Finset.range (2 * (G.inside X).length)) U : ℝ)) ≤
      ((portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℝ) := by
    norm_cast
    rw [hcloud_cut]
    exact hle_port
  exact le_trans hsum_le hcloud_cut_r

/-- When the cloud expansion is at least `1 / a₀`, the number of moved ports is at most `a₀ · c`. -/
theorem movedPorts_le_mul_cut {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) {a₀ : ℕ} (ha₀ : 1 ≤ a₀) (hα : (1 : ℝ) / a₀ ≤ α)
    {G : Graph} {X U : Finset ℕ} (hU : U ⊆ (portGraph cloud G X).verts) :
    (movedPorts G X U).card ≤
      a₀ * (portGraph cloud G X).cutIn (portGraph cloud G X).verts U := by
  have h1 := alpha_mul_movedPorts_le_cut hcloud hU
  have ha₀_pos : (0 : ℝ) < a₀ := by exact_mod_cast (by omega : 0 < a₀)
  have h2 : ((1 : ℝ) / a₀) * ((movedPorts G X U).card : ℝ) ≤
      ((portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)) h1
  have h3 : ((movedPorts G X U).card : ℝ) ≤
      (a₀ : ℝ) * ((portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℝ) := by
    rw [one_div_mul_eq_div, div_le_iff₀ ha₀_pos] at h2
    linarith
  exact_mod_cast h3

/-- Rounding increases the original-edge boundary by at most `|movedPorts|`: each moved port is
incident to a unique original edge occurrence. -/
theorem cutIn_roundPortCut_le_orig_add_moved {G : Graph} {X U : Finset ℕ}
    (hU : U ⊆ Finset.range (2 * (G.inside X).length)) :
    G.cutIn X (roundPortCut G X U) ≤
      (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).cutIn
        (Finset.range (2 * (G.inside X).length)) U + (movedPorts G X U).card := by
  set e := (G.inside X).length
  set S := roundPortCut G X U
  set U' := liftSet G X S
  rw [← cutIn_origPortEdges_liftSet G X S]
  have hv : (Graph.mk (2 * e) (origPortEdges e)).IsValid := by
    intro ed hed
    have h := mem_origPortEdges hed
    exact ⟨h.1, h.2.1⟩
  have hcut_sum : ∀ T : Finset ℕ,
      (Graph.mk (2 * e) (origPortEdges e)).cutIn (Finset.range (2 * e)) T =
        ∑ i ∈ Finset.range e,
          if (decide (2 * i ∈ T) != decide (2 * i + 1 ∈ T)) then 1 else 0 := by
    intro T
    rw [cutIn_eq_sum_map]
    change (((Graph.mk (2 * e) (origPortEdges e)).inside
        (Graph.mk (2 * e) (origPortEdges e)).verts).map _).sum = _
    rw [inside_verts_of_isValid hv]
    dsimp only [origPortEdges]
    rw [List.map_map, ← sum_range_getD_eq_sum_map' (List.range e) 0]
    simp only [List.length_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < e := Finset.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simp [hi']), List.getElem_range]
    rfl
  rw [hcut_sum U', hcut_sum U]
  have hmoved_sum : (movedPorts G X U).card =
      ∑ p ∈ Finset.range (2 * e), if p ∈ movedPorts G X U then 1 else 0 := by
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hp
      refine ⟨?_, hp⟩
      simp only [movedPorts, Finset.mem_union, Finset.mem_sdiff] at hp
      rcases hp with ⟨hpU, _⟩ | ⟨hpL, _⟩
      · exact Finset.mem_range.mp (hU hpU)
      · exact Finset.mem_range.mp (Finset.mem_filter.mp hpL).1
    · exact And.right
  rw [hmoved_sum, sum_range_two_mul', ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases h1U : 2 * i ∈ U <;> by_cases h1U' : 2 * i ∈ U' <;>
    by_cases h2U : 2 * i + 1 ∈ U <;> by_cases h2U' : 2 * i + 1 ∈ U' <;>
    simp [movedPorts, S, U', h1U, h1U', h2U, h2U']

/-- **Port-cut rounding** (integer form).
Let `U` be a port cut of `portGraph cloud G X` satisfying `b · c ≤ min(|U|, |Ū|)` where
`c = |∂ U|` and `b ≥ 2 a₀` (for cloud expansion at least `1 / a₀`). Let `S = roundPortCut G X U`.
Then:
1. `S ⊆ X`;
2. `|movedPorts| ≤ a₀ · c` and `2 · |movedPorts| ≤ min(|U|, |Ū|)`;
3. each rounded original side retains at least half its port cardinality as volume:
   `|U| ≤ 2 · vol_G(S)` and `|Ū| ≤ 2 · vol_G(X \ S)`;
4. `|∂_G S| ≤ (a₀ + 1) · c`;
5. `b · |∂_G S| ≤ 2(a₀ + 1) · min(vol_G(S), vol_G(X \ S))`. -/
theorem lemma_8 {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {a₀ b : ℕ} (ha₀ : 1 ≤ a₀) (hα : (1 : ℝ) / a₀ ≤ α) (hb : 2 * a₀ ≤ b)
    {G : Graph} {X U : Finset ℕ} (hU : U ⊆ (portGraph cloud G X).verts)
    (hsparse : b * (portGraph cloud G X).cutIn (portGraph cloud G X).verts U ≤
      min U.card ((portGraph cloud G X).verts \ U).card) :
    let S := roundPortCut G X U
    let c := (portGraph cloud G X).cutIn (portGraph cloud G X).verts U
    let uMove := (movedPorts G X U).card
    S ⊆ X ∧
      uMove ≤ a₀ * c ∧
      2 * uMove ≤ min U.card ((portGraph cloud G X).verts \ U).card ∧
      U.card ≤ 2 * G.volIn X S ∧
      ((portGraph cloud G X).verts \ U).card ≤ 2 * G.volIn X (X \ S) ∧
      G.cutIn X S ≤ (a₀ + 1) * c ∧
      b * G.cutIn X S ≤ 2 * (a₀ + 1) * min (G.volIn X S) (G.volIn X (X \ S)) := by
  dsimp only
  set S := roundPortCut G X U
  set c := (portGraph cloud G X).cutIn (portGraph cloud G X).verts U
  set uMove := (movedPorts G X U).card
  set Vhat := (portGraph cloud G X).verts
  set U' := liftSet G X S
  have hSX : S ⊆ X := roundPortCut_subset G X U
  have hmove : uMove ≤ a₀ * c := movedPorts_le_mul_cut hcloud ha₀ hα hU
  have hmove_half : 2 * uMove ≤ min U.card (Vhat \ U).card := by
    calc 2 * uMove ≤ 2 * (a₀ * c) := Nat.mul_le_mul_left 2 hmove
      _ = (2 * a₀) * c := by ring
      _ ≤ b * c := Nat.mul_le_mul_right c hb
      _ ≤ min U.card (Vhat \ U).card := hsparse
  have hU_le : U.card ≤ U'.card + uMove := by
    have hsub : U ⊆ U' ∪ movedPorts G X U := by
      intro p hp
      by_cases hp' : p ∈ U'
      · exact Finset.mem_union_left _ hp'
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp, hp'⟩))
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hUbar_le : (Vhat \ U).card ≤ (Vhat \ U').card + uMove := by
    have hsub : Vhat \ U ⊆ (Vhat \ U') ∪ movedPorts G X U := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      by_cases hp' : p ∈ U'
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp', hp.2⟩))
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp.1, hp'⟩)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hU'_card : U'.card = G.volIn X S := card_liftSet G X S
  have hU'bar_card : (Vhat \ U').card = G.volIn X (X \ S) := card_sdiff_liftSet hSX
  have hmin_le1 : 2 * uMove ≤ U.card := le_trans hmove_half (Nat.min_le_left _ _)
  have hmin_le2 : 2 * uMove ≤ (Vhat \ U).card := le_trans hmove_half (Nat.min_le_right _ _)
  have hret1 : U.card ≤ 2 * G.volIn X S := by omega
  have hret2 : (Vhat \ U).card ≤ 2 * G.volIn X (X \ S) := by omega
  have hcut_orig : (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).cutIn
      (Finset.range (2 * (G.inside X).length)) U ≤ c := by
    unfold c portGraph Graph.verts
    dsimp only
    exact cutIn_le_cutIn_append_right _ _ _ _ _
  have hcut_S : G.cutIn X S ≤ (a₀ + 1) * c := by
    have h1 : G.cutIn X S ≤
        (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).cutIn
          (Finset.range (2 * (G.inside X).length)) U + uMove :=
      cutIn_roundPortCut_le_orig_add_moved hU
    have h2 : (a₀ + 1) * c = c + a₀ * c := by ring
    omega
  have hmin_vol : min U.card (Vhat \ U).card ≤ 2 * min (G.volIn X S) (G.volIn X (X \ S)) := by
    rcases le_total (G.volIn X S) (G.volIn X (X \ S)) with h | h
    · rw [min_eq_left h]
      exact le_trans (Nat.min_le_left _ _) hret1
    · rw [min_eq_right h]
      exact le_trans (Nat.min_le_right _ _) hret2
  have h32 : b * G.cutIn X S ≤ 2 * (a₀ + 1) * min (G.volIn X S) (G.volIn X (X \ S)) := by
    calc b * G.cutIn X S ≤ b * ((a₀ + 1) * c) := Nat.mul_le_mul_left b hcut_S
      _ = (a₀ + 1) * (b * c) := by ring
      _ ≤ (a₀ + 1) * min U.card (Vhat \ U).card := Nat.mul_le_mul_left (a₀ + 1) hsparse
      _ ≤ (a₀ + 1) * (2 * min (G.volIn X S) (G.volIn X (X \ S))) :=
            Nat.mul_le_mul_left (a₀ + 1) hmin_vol
      _ = 2 * (a₀ + 1) * min (G.volIn X S) (G.volIn X (X \ S)) := by ring
  exact ⟨hSX, hmove, hmove_half, hret1, hret2, hcut_S, h32⟩

/-- **Port-cut rounding** (real form of `lemma_8`). -/
theorem lemma_8_real {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {a₀ b : ℕ} (ha₀ : 1 ≤ a₀) (hα : (1 : ℝ) / a₀ ≤ α) (hb : 2 * a₀ ≤ b)
    {G : Graph} {X U : Finset ℕ} (hU : U ⊆ (portGraph cloud G X).verts)
    (hsparse : ((portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℝ) ≤
      (1 : ℝ) / b * min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ)) :
    let S := roundPortCut G X U
    let c : ℝ := (portGraph cloud G X).cutIn (portGraph cloud G X).verts U
    let uMove : ℝ := (movedPorts G X U).card
    let κ : ℕ := 2 * (a₀ + 1)
    S ⊆ X ∧
      uMove ≤ a₀ * c ∧
      uMove ≤ (a₀ : ℝ) / b * min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ) ∧
      uMove ≤ (1 / 2 : ℝ) * min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ) ∧
      (G.cutIn X S : ℝ) ≤ (κ : ℝ) / b * min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) := by
  dsimp only
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hsparse_nat : b * (portGraph cloud G X).cutIn (portGraph cloud G X).verts U ≤
      min U.card ((portGraph cloud G X).verts \ U).card := by
    rw [one_div_mul_eq_div, le_div_iff₀ hb_pos] at hsparse
    have hmin_cast : (min U.card ((portGraph cloud G X).verts \ U).card : ℝ) =
        min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ) := by
      exact_mod_cast Nat.cast_min (α := ℝ) U.card ((portGraph cloud G X).verts \ U).card
    rw [← hmin_cast] at hsparse
    have hmul : ((b * (portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℕ) : ℝ) ≤
        (min U.card ((portGraph cloud G X).verts \ U).card : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hmul
  obtain ⟨hSX, hmove, hmove_half, _, _, _, h32⟩ := lemma_8 hcloud ha₀ hα hb hU hsparse_nat
  refine ⟨hSX, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hmove
  · have h1 : ((movedPorts G X U).card : ℝ) ≤
        (a₀ : ℝ) * ((portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℝ) := by
      exact_mod_cast hmove
    calc ((movedPorts G X U).card : ℝ)
        ≤ (a₀ : ℝ) * ((portGraph cloud G X).cutIn (portGraph cloud G X).verts U : ℝ) := h1
      _ ≤ (a₀ : ℝ) * ((1 : ℝ) / b * min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ)) :=
            mul_le_mul_of_nonneg_left hsparse (Nat.cast_nonneg _)
      _ = (a₀ : ℝ) / b * min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ) := by ring
  · have h2 : (2 : ℝ) * ((movedPorts G X U).card : ℝ) ≤
        min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ) := by
      have hmin_cast : (min U.card ((portGraph cloud G X).verts \ U).card : ℝ) =
          min (U.card : ℝ) (((portGraph cloud G X).verts \ U).card : ℝ) := by
        exact_mod_cast Nat.cast_min (α := ℝ) U.card ((portGraph cloud G X).verts \ U).card
      rw [← hmin_cast]
      exact_mod_cast hmove_half
    linarith
  · have h32_r : ((b * G.cutIn X (roundPortCut G X U) : ℕ) : ℝ) ≤
        ((2 * (a₀ + 1) * min (G.volIn X (roundPortCut G X U))
          (G.volIn X (X \ roundPortCut G X U)) : ℕ) : ℝ) := by
      exact_mod_cast h32
    have hmin_cast : (min (G.volIn X (roundPortCut G X U))
          (G.volIn X (X \ roundPortCut G X U)) : ℝ) =
        min (G.volIn X (roundPortCut G X U) : ℝ) (G.volIn X (X \ roundPortCut G X U) : ℝ) := by
      exact_mod_cast Nat.cast_min (α := ℝ) _ _
    rw [div_mul_eq_mul_div, le_div_iff₀ hb_pos, ← hmin_cast]
    push_cast at h32_r ⊢
    linarith

/-! ### Cloud contraction and its volume bound -/

/-- Contracting and deleting loops does not increase the number of fake edges. -/
theorem contractEdges_length_le (G : Graph) (X : Finset ℕ) (F : List (ℕ × ℕ)) :
    (contractEdges G X F).length ≤ F.length := by
  unfold contractEdges
  exact le_trans (List.length_filter_le _ _) (by simp)

/-- Every contracted fake edge has both endpoints in `X` and is not a loop. -/
theorem mem_contractEdges {G : Graph} {X : Finset ℕ} {F : List (ℕ × ℕ)}
    (hF : ∀ e ∈ F, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length)
    {ed : ℕ × ℕ} (hed : ed ∈ contractEdges G X F) :
    ed.1 ∈ X ∧ ed.2 ∈ X ∧ ed.1 ≠ ed.2 := by
  unfold contractEdges at hed
  simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at hed
  obtain ⟨⟨f, hf, rfl⟩, hne⟩ := hed
  have hfv := hF f hf
  exact ⟨portOwner_mem hfv.1, portOwner_mem hfv.2, hne⟩

/-- The contracted fake edge list is loopless. -/
theorem contractEdges_isLoopless (G : Graph) (X : Finset ℕ) (F : List (ℕ × ℕ)) :
    ∀ ed ∈ contractEdges G X F, ed.1 ≠ ed.2 := by
  intro ed hed
  unfold contractEdges at hed
  simp only [List.mem_filter, decide_eq_true_eq] at hed
  exact hed.2

/-- Contracting fake port edges and deleting loops preserves the cut of every canonical port cut
`liftSet G X S`. -/
theorem cutIn_contractEdges_eq {G : Graph} {X : Finset ℕ} {F : List (ℕ × ℕ)}
    (hF : ∀ e ∈ F, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length)
    (S : Finset ℕ) :
    (Graph.mk G.n (contractEdges G X F)).cutIn X S =
      (Graph.mk (2 * (G.inside X).length) F).cutIn
        (Finset.range (2 * (G.inside X).length)) (liftSet G X S) := by
  have hins_L : (Graph.mk G.n (contractEdges G X F)).inside X = contractEdges G X F := by
    unfold Graph.inside
    apply List.filter_eq_self.mpr
    intro ed hed
    have hm := mem_contractEdges hF hed
    simp [hm.1, hm.2.1]
  have hins_R : (Graph.mk (2 * (G.inside X).length) F).inside
      (Finset.range (2 * (G.inside X).length)) = F := by
    change (F.filter fun e => decide (e.1 ∈ Finset.range (2 * (G.inside X).length)) &&
      decide (e.2 ∈ Finset.range (2 * (G.inside X).length))) = F
    apply List.filter_eq_self.mpr
    intro ed hed
    have hm := hF ed hed
    simp [hm.1, hm.2]
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map, hins_L, hins_R]
  unfold contractEdges
  have hgen : ∀ l : List (ℕ × ℕ),
      (∀ e ∈ l, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length) →
      (((l.map fun e => (portOwner G X e.1, portOwner G X e.2)).filter
        fun e => decide (e.1 ≠ e.2)).map
        fun e => if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum =
      (l.map fun e => if (decide (e.1 ∈ liftSet G X S) != decide (e.2 ∈ liftSet G X S))
        then 1 else 0).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      have ha := hl a List.mem_cons_self
      have ht := ih fun e he => hl e (List.mem_cons_of_mem _ he)
      have h1 : a.1 ∈ liftSet G X S ↔ portOwner G X a.1 ∈ S := by simp [liftSet, ha.1]
      have h2 : a.2 ∈ liftSet G X S ↔ portOwner G X a.2 ∈ S := by simp [liftSet, ha.2]
      rw [List.map_cons, List.filter_cons]
      by_cases hne : portOwner G X a.1 ≠ portOwner G X a.2
      · simp only [decide_eq_true hne, ↓reduceIte, List.map_cons, List.sum_cons, h1, h2, ht]
      · have heq : portOwner G X a.1 = portOwner G X a.2 := Classical.not_not.mp hne
        rw [decide_eq_false hne]
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, h1, h2, heq,
          bne_self_eq_false, zero_add, ht]
  exact hgen F hF

/-- **Boundary preservation under contraction**: for any original vertex set `S`, the
canonical port cut `liftSet G X S` in the augmented port graph `portGraph cloud G X + F` has the
same boundary as `S` in the contracted graph `contractedGraph G X F = G + F'`. -/
theorem cutIn_contractedGraph_eq {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} {X : Finset ℕ} {F : List (ℕ × ℕ)}
    (hF : ∀ e ∈ F, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length)
    (S : Finset ℕ) :
    (contractedGraph G X F).cutIn X S =
      (Graph.mk (2 * (G.inside X).length) ((portGraph cloud G X).edges ++ F)).cutIn
        (Finset.range (2 * (G.inside X).length)) (liftSet G X S) := by
  unfold contractedGraph
  rw [cutIn_append, cutIn_append, cutIn_contractEdges_eq hF]
  have h1 : (Graph.mk (2 * (G.inside X).length) (portGraph cloud G X).edges).cutIn
      (Finset.range (2 * (G.inside X).length)) (liftSet G X S) = G.cutIn X S :=
    cutIn_portGraph_liftSet hcloud G X S
  rw [h1]

/-- Contracting fake edges of port maximum degree at most `t` gives each vertex `v` fake degree at
most `t · deg_{G[X]}(v)`. -/
theorem degIn_contractEdges_le {G : Graph} {X : Finset ℕ} {F : List (ℕ × ℕ)} {t : ℕ}
    (hF : ∀ e ∈ F, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length)
    (hdeg : ∀ p < 2 * (G.inside X).length, (Graph.mk (2 * (G.inside X).length) F).deg p ≤ t)
    (v : ℕ) :
    (Graph.mk G.n (contractEdges G X F)).degIn X v ≤ t * G.degIn X v := by
  have hins_F' : (Graph.mk G.n (contractEdges G X F)).inside X = contractEdges G X F := by
    unfold Graph.inside
    apply List.filter_eq_self.mpr
    intro ed hed
    have hm := mem_contractEdges hF hed
    simp [hm.1, hm.2.1]
  have hins_F : (Graph.mk (2 * (G.inside X).length) F).inside
      (Finset.range (2 * (G.inside X).length)) = F := by
    change (F.filter fun e => decide (e.1 ∈ Finset.range (2 * (G.inside X).length)) &&
      decide (e.2 ∈ Finset.range (2 * (G.inside X).length))) = F
    apply List.filter_eq_self.mpr
    intro ed hed
    have hm := hF ed hed
    simp [hm.1, hm.2]
  have hle_vol : (Graph.mk G.n (contractEdges G X F)).degIn X v ≤
      (Graph.mk (2 * (G.inside X).length) F).volIn
        (Finset.range (2 * (G.inside X).length)) (cloudOf G X v) := by
    rw [degIn_eq_sum_map, hins_F', volIn_eq_sum_map, hins_F]
    unfold contractEdges
    have hgen : ∀ l : List (ℕ × ℕ),
        (∀ e ∈ l, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length) →
        (((l.map fun e => (portOwner G X e.1, portOwner G X e.2)).filter
          fun e => decide (e.1 ≠ e.2)).map
          fun e => (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)).sum ≤
        (l.map fun e => (if e.1 ∈ cloudOf G X v then 1 else 0) +
          (if e.2 ∈ cloudOf G X v then 1 else 0)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons a t ih =>
        have ha := hl a List.mem_cons_self
        have ht := ih fun e he => hl e (List.mem_cons_of_mem _ he)
        have h1 : a.1 ∈ cloudOf G X v ↔ portOwner G X a.1 = v := by
          simp [mem_cloudOf_iff, ha.1]
        have h2 : a.2 ∈ cloudOf G X v ↔ portOwner G X a.2 = v := by
          simp [mem_cloudOf_iff, ha.2]
        rw [List.map_cons, List.filter_cons]
        split_ifs
        · simp only [List.map_cons, List.sum_cons, h1, h2]
          omega
        · simp only [List.map_cons, List.sum_cons]
          omega
    exact hgen F hF
  have hvol_le : (Graph.mk (2 * (G.inside X).length) F).volIn
        (Finset.range (2 * (G.inside X).length)) (cloudOf G X v) ≤
      t * (cloudOf G X v).card := by
    apply volIn_le_mul_card (Finset.filter_subset _ _)
    intro p hp
    exact hdeg p (Finset.mem_range.mp hp)
  rw [card_cloudOf] at hvol_le
  exact le_trans hle_vol hvol_le

/-- **Volume after contraction**: after contracting clouds and deleting loops, the volume of any original
vertex set `S` grows by at most a factor `t + 1`. -/
theorem volIn_contractedGraph_le {G : Graph} {X : Finset ℕ} {F : List (ℕ × ℕ)} {t : ℕ}
    (hF : ∀ e ∈ F, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length)
    (hdeg : ∀ p < 2 * (G.inside X).length, (Graph.mk (2 * (G.inside X).length) F).deg p ≤ t)
    (S : Finset ℕ) :
    (contractedGraph G X F).volIn X S ≤ (t + 1) * G.volIn X S := by
  have hvol_add : (contractedGraph G X F).volIn X S =
      G.volIn X S + (Graph.mk G.n (contractEdges G X F)).volIn X S := by
    unfold contractedGraph
    rw [volIn_eq_sum_map, volIn_eq_sum_map, volIn_eq_sum_map]
    unfold Graph.inside
    dsimp only
    rw [List.filter_append, List.map_append, List.sum_append]
  rw [hvol_add]
  have hfake_vol : (Graph.mk G.n (contractEdges G X F)).volIn X S ≤ t * G.volIn X S := by
    unfold Graph.volIn
    calc ∑ v ∈ S, (Graph.mk G.n (contractEdges G X F)).degIn X v
        ≤ ∑ v ∈ S, t * G.degIn X v := Finset.sum_le_sum fun v _ => degIn_contractEdges_le hF hdeg v
      _ = t * ∑ v ∈ S, G.degIn X v := (Finset.mul_sum _ _ _).symm
  have hring : (t + 1) * G.volIn X S = G.volIn X S + t * G.volIn X S := by ring
  omega

/-- **Conductance of the contracted graph (embedding lemma and volume bound)**: if a port witness `W` of
edge expansion `β ≥ 0` embeds into `portGraph cloud G X + F` on the `2e` port vertices with
congestion at most `η > 0`, and `F` has maximum port degree at most `t`, then
`(contractedGraph G X F)[X]` has conductance at least `β / (η · (t + 1))`. -/
theorem isConductanceExpanderOn_contractedGraph_of_embedding {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) {G : Graph} {X : Finset ℕ} {F : List (ℕ × ℕ)} {t : ℕ}
    (hF : ∀ e ∈ F, e.1 < 2 * (G.inside X).length ∧ e.2 < 2 * (G.inside X).length)
    (hdeg : ∀ p < 2 * (G.inside X).length, (Graph.mk (2 * (G.inside X).length) F).deg p ≤ t)
    {W : Graph} {emb : ℕ → List ℕ} {η : ℕ} (hη : 0 < η)
    (hemb : IsEmbeddingOn W
      (Graph.mk (2 * (G.inside X).length) ((portGraph cloud G X).edges ++ F))
      (Finset.range (2 * (G.inside X).length)) emb)
    (hcong : ∀ i < (Graph.mk (2 * (G.inside X).length) ((portGraph cloud G X).edges ++ F)).m,
      congestion W emb i ≤ η)
    {β : ℝ} (hβ : 0 ≤ β)
    (hW : W.IsExpansionExpanderOn (Finset.range (2 * (G.inside X).length)) β) :
    (contractedGraph G X F).IsConductanceExpanderOn X (β / ((η : ℝ) * ((t + 1 : ℕ) : ℝ))) := by
  set Vhat := Finset.range (2 * (G.inside X).length)
  set Kport := Graph.mk (2 * (G.inside X).length) ((portGraph cloud G X).edges ++ F)
  have hKexp : Kport.IsExpansionExpanderOn Vhat (β / η) :=
    isExpansionExpanderOn_of_embedding hemb hcong hη hW
  intro S hSX _ _
  have hv1 : ((contractedGraph G X F).volIn X S : ℝ) ≤ ((t + 1 : ℕ) : ℝ) * (G.volIn X S : ℝ) := by
    exact_mod_cast volIn_contractedGraph_le hF hdeg S
  have hv2 : ((contractedGraph G X F).volIn X (X \ S) : ℝ) ≤
      ((t + 1 : ℕ) : ℝ) * (G.volIn X (X \ S) : ℝ) := by
    exact_mod_cast volIn_contractedGraph_le hF hdeg (X \ S)
  have htpos : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by positivity
  have hηpos : (0 : ℝ) < η := by exact_mod_cast hη
  have hcoef : 0 ≤ β / ((η : ℝ) * ((t + 1 : ℕ) : ℝ)) := by positivity
  by_cases hvol0 : G.volIn X S = 0 ∨ G.volIn X (X \ S) = 0
  · rcases hvol0 with h0 | h0
    · have h0' : (contractedGraph G X F).volIn X S = 0 := by
        have h := volIn_contractedGraph_le hF hdeg S
        rw [h0, Nat.mul_zero] at h
        exact Nat.eq_zero_of_le_zero h
      have hmin : min ((contractedGraph G X F).volIn X S : ℝ)
          ((contractedGraph G X F).volIn X (X \ S) : ℝ) = 0 := by
        rw [h0', Nat.cast_zero]
        exact min_eq_left (Nat.cast_nonneg _)
      rw [hmin, mul_zero]
      exact Nat.cast_nonneg _
    · have h0' : (contractedGraph G X F).volIn X (X \ S) = 0 := by
        have h := volIn_contractedGraph_le hF hdeg (X \ S)
        rw [h0, Nat.mul_zero] at h
        exact Nat.eq_zero_of_le_zero h
      have hmin : min ((contractedGraph G X F).volIn X S : ℝ)
          ((contractedGraph G X F).volIn X (X \ S) : ℝ) = 0 := by
        rw [h0', Nat.cast_zero]
        exact min_eq_right (Nat.cast_nonneg _)
      rw [hmin, mul_zero]
      exact Nat.cast_nonneg _
  · push Not at hvol0
    set U := liftSet G X S
    have hUsub : U ⊆ Vhat := Finset.filter_subset _ _
    have hUne : U.Nonempty := by
      apply Finset.card_pos.mp
      rw [card_liftSet]
      omega
    have hUneV : U ≠ Vhat := by
      intro heq
      have hcard : (Vhat \ U).card = 0 := by rw [heq, Finset.sdiff_self, Finset.card_empty]
      rw [card_sdiff_liftSet hSX] at hcard
      omega
    have hexp := hKexp U hUsub hUne hUneV
    rw [card_liftSet, card_sdiff_liftSet hSX] at hexp
    have hcut_eq : (Kport.cutIn Vhat U : ℝ) = ((contractedGraph G X F).cutIn X S : ℝ) := by
      exact_mod_cast (cutIn_contractedGraph_eq hcloud hF S).symm
    rw [hcut_eq] at hexp
    have hmin : min ((contractedGraph G X F).volIn X S : ℝ)
          ((contractedGraph G X F).volIn X (X \ S) : ℝ) ≤
        ((t + 1 : ℕ) : ℝ) * min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) := by
      rw [mul_min_of_nonneg _ _ htpos.le]
      exact min_le_min hv1 hv2
    calc β / ((η : ℝ) * ((t + 1 : ℕ) : ℝ)) *
          min ((contractedGraph G X F).volIn X S : ℝ)
            ((contractedGraph G X F).volIn X (X \ S) : ℝ)
        ≤ β / ((η : ℝ) * ((t + 1 : ℕ) : ℝ)) *
            (((t + 1 : ℕ) : ℝ) * min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ)) :=
          mul_le_mul_of_nonneg_left hmin hcoef
      _ = β / (η : ℝ) * min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) := by
          field_simp
      _ ≤ ((contractedGraph G X F).cutIn X S : ℝ) := hexp

end MinCostFlow.ExpanderDecomp
